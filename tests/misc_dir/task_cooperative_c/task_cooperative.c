/*
Tests of the task manager's cooperative mode through the C API.

Cooperative mode is the task manager with no worker threads (`lean_init_task_manager_using(0)`,
`LEAN_NUM_THREADS=0`, and the only mode of a runtime built without threads): spawning a task, readying
it by a resolve, or dropping it never runs a task but only queues it, and queued tasks run on the
calling thread when it waits for a task (the awaited task first, then highest priority first, FIFO
within a priority), sleeps, finalizes the manager, or calls `lean_run_pending_tasks`. The one exception
is a `sync := true` continuation, which runs inline inside the call that readies it, as with threads.

Every case runs tasks whose closures append a label to a global log, and compares the log with the one
sequence cooperative mode must produce. Nothing here panics; the deadlock panics are covered by
`tests/compile/task_cooperative_trap_*.lean`.
*/
#include <lean/lean.h>

// `leanc` ships no C library headers, but links the C library.
int printf(char const * fmt, ...);
int strcmp(char const * a, char const * b);

void lean_initialize_runtime_module(void);
// The `IO.Promise` primitives are not declared in `lean.h`. The promise argument is borrowed; the
// value is owned; the result task is returned owned and holds an `Option`: `lean_box(0)` is `none`,
// a constructor of tag 1 with one field is `some`.
lean_object * lean_io_promise_new(void);
lean_object * lean_io_promise_resolve(lean_object * value, lean_object * promise);
lean_object * lean_io_promise_result_opt(lean_object * promise);
// Declared here as well, so that the test compiles against a header that predates them.
void lean_run_pending_tasks(void);
lean_object * lean_io_promise_discard(lean_object * promise);

// The values of `Task.Priority.default`, `Task.Priority.max` and `Task.Priority.dedicated`.
#define PRIO_DEFAULT 0
#define PRIO_MAX 8
#define PRIO_DEDICATED 9

// The values of `IO.TaskState`, as `lean_io_get_task_state_core` returns them.
enum { WAITING = 0, RUNNING = 1, FINISHED = 2 };

static int g_failures = 0;

#define CHECK(c) do { \
    if (!(c)) { printf("%s:%d: check failed: %s\n", __FILE__, __LINE__, #c); g_failures++; } \
} while (0)

#define CHECK_EQ(actual, expected) do { \
    long actual_ = (long)(actual), expected_ = (long)(expected); \
    if (actual_ != expected_) { \
        printf("%s:%d: %s is %ld, expected %ld\n", __FILE__, __LINE__, #actual, actual_, expected_); \
        g_failures++; \
    } \
} while (0)

/* The log: the labels of the tasks that ran, in order, and markers a case pushes around a call. */
#define LOG_CAPACITY 64
static char const * g_log[LOG_CAPACITY];
static unsigned g_log_size = 0;

static void log_push(char const * label) {
    if (g_log_size < LOG_CAPACITY)
        g_log[g_log_size] = label;
    g_log_size++;
}

static void print_labels(char const * const * labels, unsigned n) {
    for (unsigned i = 0; i < n; i++)
        printf(" %s", labels[i]);
    printf("%s\n", n == 0 ? " (empty)" : "");
}

/* Compares the log with the NULL-terminated `expected`, and empties it. */
static void check_log(char const * file, int line, char const * const * expected) {
    unsigned n = 0;
    while (expected[n])
        n++;
    bool ok = n == g_log_size;
    for (unsigned i = 0; ok && i < n; i++)
        ok = strcmp(expected[i], g_log[i]) == 0;
    if (!ok) {
        printf("%s:%d: log mismatch\n  expected:", file, line);
        print_labels(expected, n);
        printf("  actual:  ");
        print_labels(g_log, g_log_size < LOG_CAPACITY ? g_log_size : LOG_CAPACITY);
        g_failures++;
    }
    g_log_size = 0;
}

#define CHECK_LOG(...) check_log(__FILE__, __LINE__, (char const * const[]){__VA_ARGS__, NULL})
#define CHECK_LOG_EMPTY() check_log(__FILE__, __LINE__, (char const * const[]){NULL})

/* What a test task does when it runs: append `label` to the log, then "canceled" if `IO.checkCanceled`
   holds, and return `lean_box(value)`. A closure captures its spec as a boxed pointer, so specs have
   static storage. */
typedef struct {
    char const * label;
    unsigned     value;
    char const * end_label; // `nested_fn` only: logged after its nested wait
} task_spec;

static lean_object * box_spec(task_spec const * spec) {
    return lean_box_usize((size_t)(uintptr_t)spec);
}

/* Consumes `boxed`. */
static task_spec const * unbox_spec(lean_object * boxed) {
    task_spec const * spec = (task_spec const *)(uintptr_t)lean_unbox_usize(boxed);
    lean_dec(boxed);
    return spec;
}

static void log_run(task_spec const * spec) {
    log_push(spec->label);
    if (lean_io_check_canceled_core())
        log_push("canceled");
}

/* A closure of `fn` whose fixed arguments are the spec and, if not NULL, `captured` (owned); `fn`
   receives them owned, followed by the closure's last argument. */
static lean_object * mk_closure(void * fn, task_spec const * spec, lean_object * captured) {
    unsigned num_fixed = captured ? 2 : 1;
    lean_object * c = lean_alloc_closure(fn, num_fixed + 1, num_fixed);
    lean_closure_set(c, 0, box_spec(spec));
    if (captured)
        lean_closure_set(c, 1, captured);
    return c;
}

/* `Unit → Nat`, the closure of a spawned task. */
static lean_object * task_fn(lean_object * spec, lean_object * unit) {
    (void)unit;
    task_spec const * s = unbox_spec(spec);
    log_run(s);
    return lean_box(s->value);
}

static lean_object * spawn(task_spec const * spec, unsigned prio, bool keep_alive) {
    return lean_task_spawn_core(mk_closure((void *)task_fn, spec, NULL), prio, keep_alive);
}

/* `α → α`, the function of a map: logs, and passes the value through. */
static lean_object * map_fn(lean_object * spec, lean_object * value) {
    log_run(unbox_spec(spec));
    return value;
}

/* Consumes `t`. */
static lean_object * map(task_spec const * spec, lean_object * t, unsigned prio, bool sync, bool keep_alive) {
    return lean_task_map_core(mk_closure((void *)map_fn, spec, NULL), t, prio, sync, keep_alive);
}

/* `Unit → Unit`: logs, and resolves the captured promise with the spec's value. */
static lean_object * resolver_fn(lean_object * spec, lean_object * promise, lean_object * unit) {
    (void)unit;
    task_spec const * s = unbox_spec(spec);
    log_run(s);
    lean_io_promise_resolve(lean_box(s->value), promise);
    lean_dec(promise);
    return lean_box(0);
}

/* `Unit → Nat`: logs, waits for the captured task inside the running task, logs `end_label`, and
   returns that task's value plus one. */
static lean_object * nested_fn(lean_object * spec, lean_object * other, lean_object * unit) {
    (void)unit;
    task_spec const * s = unbox_spec(spec);
    log_run(s);
    unsigned v = lean_unbox(lean_task_get(other));
    lean_dec(other);
    log_push(s->end_label);
    if (lean_io_check_canceled_core())
        log_push("canceled");
    return lean_box(v + 1);
}

static task_spec const g_inner_map = {"inner-map", 0, NULL};

/* `Option Nat → Task (Option Nat)`, the function of a bind: logs, and returns a map on the captured
   promise, which is still pending when it runs. */
static lean_object * bind_fn(lean_object * spec, lean_object * inner_promise, lean_object * value) {
    log_run(unbox_spec(spec));
    lean_dec(value);
    lean_object * inner = map(&g_inner_map, lean_io_promise_result_opt(inner_promise), PRIO_DEFAULT, false, false);
    lean_dec(inner_promise);
    return inner;
}

/* `Option Nat → Unit`, one link of the chain of `test_deep_chain`: resolves the captured promise with
   the value plus one. */
static lean_object * chain_fn(lean_object * next_promise, lean_object * value) {
    unsigned v = lean_unbox(lean_ctor_get(value, 0));
    lean_dec(value);
    lean_io_promise_resolve(lean_box(v + 1), next_promise);
    lean_dec(next_promise);
    return lean_box(0);
}

static lean_object * result_task(lean_object * promise) { return lean_io_promise_result_opt(promise); }
static void resolve(lean_object * promise, unsigned value) { lean_io_promise_resolve(lean_box(value), promise); }
static uint8_t state(lean_object * t) { return lean_io_get_task_state_core(t); }

static bool is_none(lean_object * v) { return lean_is_scalar(v) && lean_unbox(v) == 0; }
static bool is_some(lean_object * v, unsigned n) {
    return !lean_is_scalar(v) && lean_ptr_tag(v) == 1 && lean_unbox(lean_ctor_get(v, 0)) == n;
}

/* A `List` cell; takes ownership of both fields. */
static lean_object * cons(lean_object * head, lean_object * tail) {
    lean_object * c = lean_alloc_ctor(1, 2, 0);
    lean_ctor_set(c, 0, head);
    lean_ctor_set(c, 1, tail);
    return c;
}

/* Before `lean_init_task_manager_using`: a spawned task and a map run at once, and the primitives
   that take a task accept the finished one instead of dereferencing the missing manager. */
static void test_before_manager(void) {
    static task_spec const eager = {"eager", 1, NULL}, eager_map = {"eager-map", 0, NULL};
    lean_object * t = spawn(&eager, PRIO_DEFAULT, false);
    CHECK_LOG("eager");
    CHECK_EQ(state(t), FINISHED);
    CHECK_EQ(lean_unbox(lean_task_get(t)), 1);
    lean_io_cancel_core(t);
    CHECK(!lean_io_check_canceled_core());
    lean_inc(t);
    lean_object * list = cons(t, lean_box(0));
    CHECK(lean_io_wait_any_core(list) == t);
    lean_dec(list);
    lean_object * m = map(&eager_map, t, PRIO_DEFAULT, false, false);
    CHECK_LOG("eager-map");
    CHECK_EQ(state(m), FINISHED);
    CHECK_EQ(lean_unbox(lean_task_get(m)), 1);
    lean_dec(m);
}

/* Spawned tasks are queued, and run highest priority first, FIFO within a priority: the dedicated
   priority is clamped to `max`, so a dedicated task runs after the `max` task spawned before it. A
   wait runs the awaited task first, whatever its priority, and nothing else once it is finished. */
static void test_priorities(void) {
    static task_spec const p0 = {"p0", 0, NULL}, p8 = {"p8", 0, NULL}, p9 = {"p9", 0, NULL};
    lean_object * t0 = spawn(&p0, PRIO_DEFAULT, false);
    lean_object * t8 = spawn(&p8, PRIO_MAX, false);
    lean_object * t9 = spawn(&p9, PRIO_DEDICATED, false);
    CHECK_LOG_EMPTY();
    CHECK_EQ(state(t0), WAITING);
    CHECK_EQ(state(t8), WAITING);
    CHECK_EQ(state(t9), WAITING);
    lean_task_get(t0);
    CHECK_LOG("p0");
    CHECK_EQ(state(t0), FINISHED);
    CHECK_EQ(state(t8), WAITING);
    CHECK_EQ(state(t9), WAITING);
    lean_run_pending_tasks();
    CHECK_LOG("p8", "p9");
    CHECK_EQ(state(t9), FINISHED);
    lean_dec(t0);
    lean_dec(t8);
    lean_dec(t9);
}

/* A wait for a task that is not queued, because it waits for a promise that only a queued task
   resolves, runs the queue strictly by priority: the `max` task, the dedicated one (clamped, spawned
   later), the default ones in spawn order including the resolver, and then the continuation the
   resolver readied. */
static void test_promise_rooted_wait(void) {
    static task_spec const p0 = {"p0", 0, NULL}, p8 = {"p8", 0, NULL}, p9 = {"p9", 0, NULL},
        m = {"m", 0, NULL}, r = {"resolve", 5, NULL};
    lean_object * t0 = spawn(&p0, PRIO_DEFAULT, false);
    lean_object * t8 = spawn(&p8, PRIO_MAX, false);
    lean_object * t9 = spawn(&p9, PRIO_DEDICATED, false);
    lean_object * p = lean_io_promise_new();
    lean_object * tm = map(&m, result_task(p), PRIO_DEFAULT, false, false);
    lean_inc(p);
    lean_object * tr = lean_task_spawn_core(mk_closure((void *)resolver_fn, &r, p), PRIO_DEFAULT, false);
    CHECK_LOG_EMPTY();
    CHECK(is_some(lean_task_get(tm), 5));
    CHECK_LOG("p8", "p9", "p0", "resolve", "m");
    lean_dec(t0);
    lean_dec(t8);
    lean_dec(t9);
    lean_dec(tm);
    lean_dec(tr);
    lean_dec(p);
}

/* The awaited task runs first also when it is a continuation that a resolve queued, ahead of a
   higher-priority task queued before it. */
static void test_directed_help_on_continuation(void) {
    static task_spec const p8 = {"p8", 0, NULL}, m = {"m", 0, NULL};
    lean_object * t8 = spawn(&p8, PRIO_MAX, false);
    lean_object * p = lean_io_promise_new();
    lean_object * tm = map(&m, result_task(p), PRIO_DEFAULT, false, false);
    resolve(p, 7);
    CHECK_LOG_EMPTY();
    CHECK(is_some(lean_task_get(tm), 7));
    CHECK_LOG("m");
    CHECK_EQ(state(t8), WAITING);
    lean_run_pending_tasks();
    CHECK_LOG("p8");
    lean_dec(t8);
    lean_dec(tm);
    lean_dec(p);
}

/* A continuation is queued, not run, by what readies it: a map on a finished task at once, a map on a
   promise's task by the resolve. One resolve queues its dependents in reverse registration order. */
static void test_map_queued(void) {
    static task_spec const on_finished = {"map-finished", 0, NULL}, on_pending = {"map-pending", 0, NULL},
        a = {"A", 0, NULL}, b = {"B", 0, NULL};
    lean_object * m1 = map(&on_finished, lean_task_pure(lean_box(5)), PRIO_DEFAULT, false, false);
    CHECK_LOG_EMPTY();
    CHECK_EQ(state(m1), WAITING);
    CHECK_EQ(lean_unbox(lean_task_get(m1)), 5);
    CHECK_LOG("map-finished");
    lean_dec(m1);

    lean_object * p = lean_io_promise_new();
    lean_object * pt = result_task(p);
    CHECK_EQ(state(pt), RUNNING);
    lean_object * m2 = map(&on_pending, pt, PRIO_DEFAULT, false, false);
    CHECK_EQ(state(m2), WAITING);
    resolve(p, 6);
    CHECK_LOG_EMPTY();
    CHECK_EQ(state(m2), WAITING);
    CHECK(is_some(lean_task_get(m2), 6));
    CHECK_LOG("map-pending");
    lean_dec(m2);
    lean_dec(p);

    lean_object * q = lean_io_promise_new();
    lean_object * ma = map(&a, result_task(q), PRIO_DEFAULT, false, false);
    lean_object * mb = map(&b, result_task(q), PRIO_DEFAULT, false, false);
    resolve(q, 0);
    CHECK_LOG_EMPTY();
    lean_run_pending_tasks();
    CHECK_LOG("B", "A");
    lean_dec(ma);
    lean_dec(mb);
    lean_dec(q);
}

/* `sync := true` continuations are the exception to queueing: one on a pending promise runs inside the
   resolve, one on a finished task inside `lean_task_map_core`. */
static void test_sync_inline(void) {
    static task_spec const on_promise = {"sync-on-promise", 0, NULL}, on_finished = {"sync-on-finished", 0, NULL};
    lean_object * p = lean_io_promise_new();
    lean_object * m = map(&on_promise, result_task(p), PRIO_DEFAULT, true, false);
    CHECK_EQ(state(m), WAITING);
    log_push("before-resolve");
    resolve(p, 3);
    log_push("after-resolve");
    CHECK_LOG("before-resolve", "sync-on-promise", "after-resolve");
    CHECK_EQ(state(m), FINISHED);
    CHECK(is_some(lean_task_get(m), 3));
    lean_dec(m);
    lean_dec(p);

    log_push("before-map");
    lean_object * m2 = map(&on_finished, lean_task_pure(lean_box(4)), PRIO_DEFAULT, true, false);
    log_push("after-map");
    CHECK_LOG("before-map", "sync-on-finished", "after-map");
    CHECK_EQ(state(m2), FINISHED);
    CHECK_EQ(lean_unbox(lean_task_get(m2)), 4);
    lean_dec(m2);
}

/* A bind whose function returns an unfinished task (a map on a pending promise) makes the outer task
   wait for that inner task; it finishes with the inner value once the inner promise is resolved and
   the thread waits. */
static void test_bind_pending_inner(void) {
    static task_spec const outer_spec = {"bind", 0, NULL};
    lean_object * p_outer = lean_io_promise_new();
    lean_object * p_inner = lean_io_promise_new();
    lean_inc(p_inner);
    lean_object * outer = lean_task_bind_core(result_task(p_outer), mk_closure((void *)bind_fn, &outer_spec, p_inner),
        PRIO_DEFAULT, false, false);
    CHECK_EQ(state(outer), WAITING);
    resolve(p_outer, 1);
    lean_run_pending_tasks(); // runs the bind function; its task is pending, so `outer` now waits for it
    CHECK_LOG("bind");
    CHECK_EQ(state(outer), WAITING);
    resolve(p_inner, 2); // queues the inner map only
    CHECK_LOG_EMPTY();
    CHECK_EQ(state(outer), WAITING);
    CHECK(is_some(lean_task_get(outer), 2));
    CHECK_LOG("inner-map");
    lean_dec(outer);
    lean_dec(p_outer);
    lean_dec(p_inner);
}

/* Dropping a promise resolves its task with `none`; the continuation is queued by the drop, not run. */
static void test_promise_drop(void) {
    static task_spec const m = {"on-dropped", 0, NULL};
    lean_object * p = lean_io_promise_new();
    lean_object * tm = map(&m, result_task(p), PRIO_DEFAULT, false, false);
    lean_dec(p);
    CHECK_LOG_EMPTY();
    CHECK_EQ(state(tm), WAITING);
    CHECK(is_none(lean_task_get(tm)));
    CHECK_LOG("on-dropped");
    lean_dec(tm);
}

/* `IO.cancel` only sets a flag: a queued task still runs, seeing `IO.checkCanceled`; canceling a
   promise's task is passed on to the dependents the resolve readies. */
static void test_cancel(void) {
    static task_spec const q = {"q", 0, NULL}, m = {"m", 0, NULL};
    lean_object * tq = spawn(&q, PRIO_DEFAULT, false);
    lean_io_cancel_core(tq);
    CHECK_EQ(state(tq), WAITING);
    lean_run_pending_tasks();
    CHECK_LOG("q", "canceled");
    lean_dec(tq);

    lean_object * p = lean_io_promise_new();
    lean_object * pt = result_task(p);
    lean_object * tm = map(&m, result_task(p), PRIO_DEFAULT, false, false);
    lean_io_cancel_core(pt);
    lean_dec(pt);
    resolve(p, 1);
    CHECK_LOG_EMPTY();
    lean_run_pending_tasks();
    CHECK_LOG("m", "canceled");
    CHECK(!lean_io_check_canceled_core());
    lean_dec(tm);
    lean_dec(p);
}

/* A `keep_alive` task runs although its handle was dropped; without `keep_alive`, dropping the handle
   of a queued task frees its closure and the task never runs. */
static void test_keep_alive(void) {
    static task_spec const kept = {"kept", 0, NULL}, dropped = {"dropped", 0, NULL};
    lean_dec(spawn(&kept, PRIO_DEFAULT, true));
    lean_dec(spawn(&dropped, PRIO_DEFAULT, false));
    CHECK_LOG_EMPTY();
    lean_run_pending_tasks();
    CHECK_LOG("kept");
}

/* A task that waits for a queued task runs it on its own stack, and is the current task again
   afterwards: the inner task's canceled flag is not seen by the outer one, and there is no current
   task once the wait at the top level returns. */
static void test_nested_wait(void) {
    static task_spec const b = {"B", 41, NULL}, a = {"A-start", 0, "A-end"};
    lean_object * tb = spawn(&b, PRIO_DEFAULT, false);
    lean_io_cancel_core(tb);
    lean_inc(tb);
    lean_object * ta = lean_task_spawn_core(mk_closure((void *)nested_fn, &a, tb), PRIO_DEFAULT, false);
    CHECK_LOG_EMPTY();
    CHECK_EQ(lean_unbox(lean_task_get(ta)), 42);
    CHECK_LOG("A-start", "B", "canceled", "A-end");
    CHECK_EQ(state(tb), FINISHED);
    CHECK(!lean_io_check_canceled_core());
    lean_dec(ta);
    lean_dec(tb);
}

/* A chain of promises, each resolved by the continuation of the previous one, runs on a flat stack:
   resolving only queues the next continuation, which the wait's loop then runs. */
static void test_deep_chain(void) {
    enum { N = 100000 };
    lean_object * first = lean_io_promise_new();
    lean_inc(first);
    lean_object * cur = first;
    for (unsigned i = 1; i < N; i++) {
        lean_object * next = lean_io_promise_new();
        lean_inc(next);
        lean_object * c = lean_alloc_closure((void *)chain_fn, 2, 1);
        lean_closure_set(c, 0, next);
        lean_dec(lean_task_map_core(c, result_task(cur), PRIO_DEFAULT, false, true));
        lean_dec(cur);
        cur = next;
    }
    resolve(first, 1);
    CHECK_LOG_EMPTY();
    lean_object * last = result_task(cur);
    CHECK(is_some(lean_task_get(last), N));
    lean_dec(last);
    lean_dec(cur);
    lean_dec(first);
}

/* `IO.waitAny` runs a queued member directly when none is finished, leaving one that waits for a
   promise alone. */
static void test_wait_any(void) {
    static task_spec const m = {"m", 0, NULL}, q = {"q", 0, NULL};
    lean_object * p = lean_io_promise_new();
    lean_object * tm = map(&m, result_task(p), PRIO_DEFAULT, false, false);
    lean_object * tq = spawn(&q, PRIO_DEFAULT, false);
    lean_inc(tm);
    lean_inc(tq);
    lean_object * list = cons(tm, cons(tq, lean_box(0)));
    CHECK(lean_io_wait_any_core(list) == tq);
    CHECK_LOG("q");
    CHECK_EQ(state(tm), WAITING);
    resolve(p, 9);
    CHECK(is_some(lean_task_get(tm), 9));
    CHECK_LOG("m");
    lean_dec(list);
    lean_dec(tm);
    lean_dec(tq);
    lean_dec(p);
}

/* `lean_finalize_task_manager` runs what is still queued, with `IO.checkCanceled` true, before the
   manager goes away. A task waiting for a promise that is never resolved stays unfinished, and it and
   its promise can be dropped afterwards in either order. Last, since the manager is gone afterwards. */
static void test_finalize(void) {
    static task_spec const at_exit = {"at-exit", 0, NULL}, held = {"held", 0, NULL},
        never1 = {"never1", 0, NULL}, never2 = {"never2", 0, NULL};
    lean_dec(spawn(&at_exit, PRIO_DEFAULT, true));
    lean_object * t_held = spawn(&held, PRIO_DEFAULT, false);
    lean_object * p1 = lean_io_promise_new();
    lean_object * m1 = map(&never1, result_task(p1), PRIO_DEFAULT, false, false);
    lean_object * p2 = lean_io_promise_new();
    lean_object * m2 = map(&never2, result_task(p2), PRIO_DEFAULT, false, false);
    CHECK_LOG_EMPTY();
    lean_finalize_task_manager();
    CHECK_LOG("at-exit", "canceled", "held", "canceled");
    CHECK_EQ(state(t_held), FINISHED);
    CHECK_EQ(state(m1), WAITING);
    CHECK(!lean_io_check_canceled_core());
    lean_dec(t_held);
    lean_dec(m1);
    lean_dec(p1);
    lean_dec(p2);
    lean_dec(m2);
    CHECK_LOG_EMPTY();
}

/* `lean_io_promise_discard` resolves a promise's task with `none` without running the tasks that wait
   for it: a map with a dropped handle is freed, one with a kept handle is orphaned (state `running`, and
   freed with the handle), a sync map is freed rather than run, a promise that a freed closure captured
   is discarded too, with its own dependents, and resolving the promise afterwards does nothing. */
static void test_discard(void) {
    static task_spec const kept = {"kept", 0, NULL}, dropped = {"dropped", 0, NULL},
        sync = {"sync", 0, NULL}, inner = {"inner", 0, NULL}, capturing = {"capturing", 3, NULL};
    lean_object * p = lean_io_promise_new();
    lean_object * rp = result_task(p);
    lean_object * t_kept = map(&kept, result_task(p), PRIO_DEFAULT, false, true);
    lean_dec(map(&dropped, result_task(p), PRIO_DEFAULT, false, true));
    lean_object * t_sync = map(&sync, result_task(p), PRIO_DEFAULT, true, false);
    lean_object * q = lean_io_promise_new();
    lean_object * tq = result_task(q);
    lean_object * t_inner = map(&inner, result_task(q), PRIO_DEFAULT, false, false);
    // A map whose closure captures `q` (it would resolve `q` if it ran).
    lean_object * t_capturing = lean_task_map_core(mk_closure((void *)resolver_fn, &capturing, q),
                                                   result_task(p), PRIO_DEFAULT, false, false);
    CHECK_EQ(state(t_kept), WAITING);
    lean_dec(lean_io_promise_discard(p));
    CHECK_LOG_EMPTY();
    CHECK(is_none(lean_task_get(rp)));
    CHECK_EQ(state(t_kept), RUNNING);
    CHECK_EQ(state(t_sync), RUNNING);
    CHECK_EQ(state(t_capturing), RUNNING);
    CHECK(is_none(lean_task_get(tq)));
    CHECK_EQ(state(t_inner), RUNNING);
    resolve(p, 5);
    lean_run_pending_tasks();
    CHECK(is_none(lean_task_get(rp)));
    CHECK_LOG_EMPTY();
    lean_dec(t_kept);
    lean_dec(t_sync);
    lean_dec(t_capturing);
    lean_dec(t_inner);
    lean_dec(tq);
    lean_dec(rp);
    lean_dec(p);
    // A discarded chain of promises, each captured by the continuation of the one before, is freed on a
    // flat stack: the last promise's task resolves to `none`.
    lean_object * first = lean_io_promise_new();
    lean_object * prev = first;
    for (unsigned i = 0; i < 100000; i++) {
        lean_object * next = lean_io_promise_new();
        lean_inc(next);
        lean_object * c = lean_alloc_closure((void *)chain_fn, 2, 1);
        lean_closure_set(c, 0, next);
        lean_dec(lean_task_map_core(c, result_task(prev), PRIO_DEFAULT, false, true));
        if (prev != first)
            lean_dec(prev);
        prev = next;
    }
    lean_object * last = result_task(prev);
    lean_dec(prev);
    lean_dec(lean_io_promise_discard(first));
    lean_dec(first);
    CHECK(is_none(lean_task_get(last)));
    lean_dec(last);
    CHECK_LOG_EMPTY();
}

int main(void) {
    lean_initialize_runtime_module();
    test_before_manager();
    lean_init_task_manager_using(0);
    test_priorities();
    test_promise_rooted_wait();
    test_directed_help_on_continuation();
    test_map_queued();
    test_sync_inline();
    test_bind_pending_inner();
    test_promise_drop();
    test_cancel();
    test_keep_alive();
    test_nested_wait();
    test_deep_chain();
    test_wait_any();
    test_discard();
    test_finalize();
    if (g_failures != 0) {
        printf("%d check(s) failed\n", g_failures);
        return 1;
    }
    return 0;
}

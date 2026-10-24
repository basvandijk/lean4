import Std.Async.Basic

/-!
Trace tests of the task manager's cooperative mode: no worker threads, selected here by
`LEAN_NUM_THREADS=0` (see `task_cooperative.lean.init.sh`), and the only mode of a runtime built without
threads. Queued tasks run on the calling thread when it waits (`IO.wait`, `Task.get`, `IO.waitAny`),
sleeps (`IO.sleep`) or exits: a wait runs the awaited task first if it is queued, then queued tasks
highest priority first. Creating, readying or dropping a task never runs one, except `(sync := true)`
continuations, which run inline as they do with threads.

`all` runs every case that returns, in order; `shared` those whose trace is the same with one worker
thread (`task_cooperative_mt1.lean`); a case name runs that case, and the `trap-` cases end with an
internal panic (`task_cooperative_trap_*.lean`).
-/

open Std.Async

def showResult [ToString α] : Except IO.Error α → String
  | .ok a => s!"ok {a}"
  | .error e => s!"error {e}"

/-- Waits for the task, and prints its result. -/
def waitResult [ToString α] (t : Task (Except IO.Error α)) : IO Unit := do
  IO.println s!"result: {showResult (← IO.wait t)}"

/-- Before a trap, so that the lines printed so far precede the panic in the captured output. -/
def flush : IO Unit := do (← IO.getStdout).flush

def dropped : IO.Error := IO.userError "the promise was dropped"

/-- A spawned task is queued, not run, until the thread waits for it. -/
def spawnLazy : IO Unit := do
  let t ← IO.asTask (do IO.println "spawned"; return 1)
  IO.println "after spawn"
  IO.println s!"state {← IO.getTaskState t}"
  waitResult t

/-- A task spawned inside a task is queued too; the wait for the outer task does not run it, the next
yield (`IO.sleep`) does. -/
def spawnNested : IO Unit := do
  let outer ← IO.asTask do
    IO.println "outer start"
    let inner ← IO.asTask (IO.println "inner")
    IO.println s!"inner state: {← IO.getTaskState inner}"
    IO.println "outer end"
  IO.println "after outer"
  discard <| IO.wait outer
  IO.println "done"
  IO.sleep 0

/-- A continuation on a pending promise is queued by `resolve`, and runs at the wait. -/
def mapPending : IO Unit := do
  let p ← IO.Promise.new (α := Nat)
  let t ← IO.mapTask (fun v => do IO.println s!"continuation {v}"; return v.getD 0 + 1) p.result?
  IO.println "setup done"
  p.resolve 5
  IO.println "resolved"
  IO.println s!"state {← IO.getTaskState t}"
  waitResult t

/-- A continuation on a finished task is queued, not run. -/
def mapFinished : IO Unit := do
  let t ← IO.mapTask (fun v => do IO.println s!"continuation on finished {v}"; return v + 1) (Task.pure 1)
  IO.println s!"state {← IO.getTaskState t}"
  waitResult t

/-- `(sync := true)` continuations run inline: inside the `resolve` that readies them, at top level or
inside a task, and in the caller on a finished task. -/
def syncInline : IO Unit := do
  let p ← IO.Promise.new (α := Nat)
  let t ← IO.mapTask (sync := true) (fun v => do IO.println s!"sync continuation {v}"; return v.getD 0) p.result?
  IO.println "before resolve"
  p.resolve 1
  IO.println "after resolve"
  waitResult t
  let q ← IO.Promise.new (α := Nat)
  let u ← IO.mapTask (sync := true) (fun v => do IO.println s!"sync continuation {v}"; return v.getD 0) q.result?
  let r ← IO.asTask do
    IO.println "task: before resolve"
    q.resolve 2
    IO.println "task: after resolve"
  discard <| IO.wait r
  waitResult u
  let s ← IO.mapTask (sync := true) (fun v => do IO.println s!"sync on finished {v}"; return v) (Task.pure 3)
  waitResult s
  IO.println "end"

/-- A continuation that itself waits on a second promise: the task of the first continuation becomes a
dependent of the second promise. Either promise may be resolved first. -/
def nested (pFirst : Bool) : IO Unit := do
  let p ← IO.Promise.new (α := Nat)
  let q ← IO.Promise.new (α := Nat)
  let t ← IO.bindTask p.result? fun v => do
    IO.println s!"p continuation {v}"
    IO.mapTask (fun w => do IO.println s!"q continuation {w}"; return v.getD 0 + w.getD 0) q.result?
  IO.println "setup done"
  if pFirst then
    p.resolve 1
    q.resolve 2
  else
    q.resolve 2
    p.resolve 1
  waitResult t

/-- A `do` block in `Async` with three awaits: each segment runs when the wait reaches it. -/
def asyncDo : IO Unit := do
  let p0 ← IO.Promise.new (α := Nat)
  let p1 ← IO.Promise.new (α := Nat)
  let p2 ← IO.Promise.new (α := Nat)
  let act : Async Nat := do
    IO.println "segment 0"
    let some a ← await p0.result? | throw dropped
    IO.println s!"segment 1: {a}"
    let some b ← await p1.result? | throw dropped
    IO.println s!"segment 2: {b}"
    let some c ← await p2.result? | throw dropped
    IO.println s!"segment 3: {c}"
    return a + b + c
  let t ← EAsync.toBaseIO act
  IO.println "setup done"
  for (p, i) in [p0, p1, p2].zip [0, 1, 2] do
    p.resolve (i + 1)
  waitResult t

/-- `for` over a list, whose iterations await, and `repeat`, which `Std.Async` runs through a promise
of its own. -/
def loops : IO Unit := do
  let p0 ← IO.Promise.new (α := Nat)
  let p1 ← IO.Promise.new (α := Nat)
  let p2 ← IO.Promise.new (α := Nat)
  let act : Async Nat := do
    let mut sum := 0
    for p in [p0, p1, p2] do
      let some v ← await p.result? | throw dropped
      IO.println s!"for: {v}"
      sum := sum + v
    let mut i := 0
    repeat
      if i == 2 then break
      IO.println s!"repeat: {i}"
      i := i + 1
    return sum
  let t ← EAsync.toBaseIO act
  IO.println "setup done"
  p0.resolve 1
  p1.resolve 2
  p2.resolve 3
  waitResult t

/-- An error thrown after an await is caught by a `try` around the await. -/
def tryCatch : IO Unit := do
  let p ← IO.Promise.new (α := Nat)
  let act : Async Nat := do
    try
      let some v ← await p.result? | throw dropped
      throw (IO.userError s!"failed after {v}")
    catch e =>
      IO.println s!"caught: {e}"
      return 0
  let t ← EAsync.toBaseIO act
  IO.println "setup done"
  p.resolve 1
  waitResult t

/-- `Async.race`: both computations are queued when started and run at the wait, after both promises
were resolved, so the first in queue order wins (with threads, the one whose promise is resolved first). -/
def race : IO Unit := do
  let p ← IO.Promise.new (α := Nat)
  let q ← IO.Promise.new (α := Nat)
  let x : Async Nat := do
    let some a ← await p.result? | throw dropped
    return a
  let y : Async Nat := do
    let some b ← await q.result? | throw dropped
    return b
  let t ← EAsync.toBaseIO (Async.race x y)
  q.resolve 2
  p.resolve 1
  waitResult t

/-- `Async.concurrently`: both computations are queued when started, and run at the wait. -/
def concurrently : IO Unit := do
  let p ← IO.Promise.new (α := Nat)
  let q ← IO.Promise.new (α := Nat)
  let x : Async Nat := do
    IO.println "x before await"
    let some a ← await p.result? | throw dropped
    IO.println s!"x after await {a}"
    return a
  let y : Async Nat := do
    IO.println "y before await"
    let some b ← await q.result? | throw dropped
    IO.println s!"y after await {b}"
    return b
  let t ← EAsync.toBaseIO (Async.concurrently x y)
  IO.println "setup done"
  q.resolve 2
  p.resolve 1
  waitResult t

/-- A promise that is dropped without being resolved resolves its task with `none`; the continuation
is queued, not run, by the drop. -/
def dropPromise : IO Unit := do
  IO.println "setup done"
  let t ← do
    let p ← IO.Promise.new (α := Nat)
    IO.mapTask (fun v => do IO.println s!"continuation {v}"; return v.getD 0) p.result?
  IO.println s!"state {← IO.getTaskState t}"
  waitResult t

/-- A promise dropped inside a running task: the same, and the continuation runs after that task. -/
def dropPromiseInTask : IO Unit := do
  let r ← IO.asTask do
    let p ← IO.Promise.new (α := Nat)
    let t ← IO.mapTask (fun v => do IO.println s!"continuation {v}"; return v.getD 0) p.result?
    IO.println "task: dropped"
    IO.println s!"task: state {← IO.getTaskState t}"
    return t
  let t ← IO.ofExcept (← IO.wait r)
  IO.println "task done"
  waitResult t

/-- A continuation that resolves another promise: that promise's continuation runs after the resolving
one has returned, not inside `resolve`. -/
def reentrant : IO Unit := do
  let p ← IO.Promise.new (α := Nat)
  let q ← IO.Promise.new (α := Nat)
  let tq ← IO.mapTask (fun v => IO.println s!"q continuation {v}") q.result?
  let tp ← IO.mapTask (fun v => do
      IO.println s!"p continuation {v}"
      q.resolve 7
      IO.println "after resolve q") p.result?
  IO.println "setup done"
  p.resolve 3
  discard <| IO.wait tp
  discard <| IO.wait tq
  IO.println "done"

/-- A task that waits on a promise that is resolved afterwards: it runs at the wait on it, after the
resolve, so the wait inside it finds the promise resolved. -/
def consumerFirst : IO Unit := do
  let p ← IO.Promise.new (α := Nat)
  let t ← IO.asTask (IO.wait p.result?)
  p.resolve 1
  IO.println s!"result: {showResult (← IO.wait t)}"

/-- `IO.cancel` on a continuation's task, before it runs. -/
def cancel : IO Unit := do
  let p ← IO.Promise.new (α := Nat)
  let t ← IO.mapTask (fun _ => do IO.println s!"canceled: {← IO.checkCanceled}") p.result?
  IO.cancel t
  p.resolve 1
  discard <| IO.wait t

/-- Canceling a promise's task cancels its dependents when it is resolved. -/
def cancelPropagates : IO Unit := do
  let p ← IO.Promise.new (α := Nat)
  let t ← IO.mapTask (fun _ => do IO.println s!"canceled: {← IO.checkCanceled}") p.result?
  IO.cancel p.result?
  p.resolve 1
  discard <| IO.wait t

/-- `IO.checkCanceled` refers to the innermost task: inside a task run at a wait inside a canceled task,
and again to the canceled one afterwards. -/
def cancelNested : IO Unit := do
  let inner ← IO.asTask (do IO.println s!"inner canceled: {← IO.checkCanceled}")
  let outer ← IO.asTask do
    IO.println s!"outer canceled before: {← IO.checkCanceled}"
    discard <| IO.wait inner
    IO.println s!"outer canceled after: {← IO.checkCanceled}"
  IO.cancel outer
  discard <| IO.wait outer

/-- A chain of `n` promises, each resolved by the continuation of the one before: resolving the first
queues them one after the other, on a stack that does not grow with `n`. -/
def deep (n : Nat) : IO Unit := do
  let first ← IO.Promise.new (α := Nat)
  let mut p := first
  for _ in [0:n] do
    let q ← IO.Promise.new (α := Nat)
    discard <| IO.mapTask (fun v => q.resolve (v.getD 0 + 1)) p.result?
    p := q
  first.resolve 0
  IO.println s!"deep {n}: {← IO.wait p.result?}"

/-- Continuations of three priorities on one promise, observed from a wait on a fourth promise, which
the last of them resolves: the highest priority first, with the dedicated priority as the maximum
(there are no dedicated threads). -/
def priorities : IO Unit := do
  let p ← IO.Promise.new (α := Nat)
  let done ← IO.Promise.new (α := Unit)
  discard <| IO.mapTask (prio := Task.Priority.default) (fun _ => do IO.println "default priority"; done.resolve ()) p.result?
  discard <| IO.mapTask (prio := Task.Priority.max) (fun _ => IO.println "max priority") p.result?
  discard <| IO.mapTask (prio := Task.Priority.dedicated) (fun _ => IO.println "dedicated priority") p.result?
  IO.println "setup done"
  p.resolve 0
  discard <| IO.wait done.result?
  IO.println "done"

/-- A wait runs the awaited task first, before queued tasks of higher priority. -/
def directed : IO Unit := do
  let p ← IO.Promise.new (α := Nat)
  let t0 ← IO.mapTask (prio := Task.Priority.default) (fun _ => IO.println "default priority") p.result?
  let t8 ← IO.mapTask (prio := Task.Priority.max) (fun _ => IO.println "max priority") p.result?
  p.resolve 0
  discard <| IO.wait t0
  IO.println "after wait"
  discard <| IO.wait t8

@[noinline] def mkPureTask (k : Nat) : Task Nat :=
  Task.spawn fun _ => dbgTrace s!"pure task ran {k}" fun _ => k

/-- A queued `Task.spawn` whose last reference is dropped never runs; a queued `IO.asTask` runs anyway. -/
def dropQueued : IO Unit := do
  let k := (← IO.getRandomBytes 0).size + 1
  let t := mkPureTask k
  IO.println s!"pure task state {← IO.getTaskState t}"
  discard <| IO.asTask (IO.println "io task ran")
  IO.sleep 0
  IO.println "after yield"

@[noinline] def work (k : Nat) : IO Nat :=
  pure (List.range k).length

/-- A task run at a wait is not charged to the waiting thread's heartbeats, which keep counting the
waiter's own work before and after the wait; the task's work counts toward the task's own. -/
def heartbeatsNested : IO Unit := do
  let k := (← IO.getRandomBytes 0).size + 100000
  let t ← IO.asTask do
    let h₀ ← IO.getNumHeartbeats
    let n ← work k
    let h₁ ← IO.getNumHeartbeats
    return (n, decide (h₁ - h₀ > 1000))
  let h₀ ← IO.getNumHeartbeats
  let m ← work k
  let h₁ ← IO.getNumHeartbeats
  let (n, taskCounted) ← IO.ofExcept (← IO.wait t)
  let h₂ ← IO.getNumHeartbeats
  let m' ← work k
  let h₃ ← IO.getNumHeartbeats
  IO.println s!"{n} {m} {m'} before {decide (h₁ - h₀ > 1000)} across {decide (h₁ ≤ h₂ ∧ h₂ - h₁ < 1000)} after {decide (h₃ - h₂ > 1000)} task {taskCounted}"

/-- A task run at a wait prints to the process's stdout, not to the waiting thread's redirected one. -/
def streamsNested : IO Unit := do
  let t ← IO.asTask (IO.println "from task")
  let (captured, ()) ← IO.FS.withIsolatedStreams do
    discard <| IO.wait t
    IO.println "captured"
  IO.print s!"buffer: {captured}"

/-- The task states: a promise's task is `running`, a queued task `waiting`, a task that runs `running`. -/
def states : IO Unit := do
  let p ← IO.Promise.new (α := Nat)
  IO.println s!"promised: {← IO.getTaskState p.result?}"
  p.resolve 0 -- keeps `p` alive until here: a dropped promise's task is finished
  let t ← IO.asTask (pure ())
  IO.println s!"queued: {← IO.getTaskState t}"
  let ref ← IO.mkRef (none : Option (Task (Except IO.Error Unit)))
  let u ← IO.asTask do
    match ← ref.get with
    | some u => IO.println s!"running: {← IO.getTaskState u}"
    | none => IO.println "running: ?"
  ref.set (some u)
  discard <| IO.wait u
  IO.println s!"finished: {← IO.getTaskState u}"
  discard <| IO.wait t

/-- `IO.waitAny` runs a queued member first; a member waiting on a promise does not block it. -/
def waitAny : IO Unit := do
  let p ← IO.Promise.new (α := Nat)
  let a ← IO.mapTask (fun v => pure (v.getD 0)) p.result?
  let b ← IO.asTask (pure (7 : Nat))
  let first ← IO.waitAny [a, b]
  IO.println s!"first: {showResult first}"
  p.resolve 9
  waitResult a

/-- `IO.sleep` runs the queued tasks before sleeping. -/
def sleepYield : IO Unit := do
  discard <| IO.asTask (IO.println "ran during sleep")
  IO.sleep 0
  IO.println "after sleep"

/-- A task still queued when `main` returns runs before the process exits. Last in `all`. -/
def exitDrains : IO Unit := do
  discard <| IO.asTask (IO.println "ran at exit")
  IO.println "main done"

/-- `IO.wait` on a promise that nothing queued resolves: an internal panic, as nothing can resolve it.
The promise is used after the wait, so that it is alive during it. -/
def trapWaitPending : IO Unit := do
  let p ← IO.Promise.new (α := Nat)
  IO.println "waiting"
  flush
  let v ← IO.wait p.result?
  IO.println s!"unreachable {v}"
  p.resolve 0

/-- A task that waits on a promise that the code waiting for the task would resolve afterwards. -/
def trapWaitAncestor : IO Unit := do
  let p ← IO.Promise.new (α := Nat)
  let t ← IO.asTask do
    IO.println "task: waiting for p"
    flush
    IO.wait p.result?
  discard <| IO.wait t
  p.resolve 1

/-- A wait on a promise runs the queued tasks in order: the first blocks on a promise that `main` would
resolve after its wait, although the second would have resolved the awaited one. -/
def trapBlockedSibling : IO Unit := do
  let p ← IO.Promise.new (α := Nat)
  let q ← IO.Promise.new (α := Nat)
  discard <| IO.asTask do
    IO.println "t2: waiting for p"
    flush
    discard <| IO.wait p.result?
  discard <| IO.asTask do
    IO.println "t1: resolving q"
    flush
    q.resolve 1
  discard <| IO.wait q.result?
  p.resolve 1

/-- `Promise.result!` of a promise that is dropped: an internal panic, at the drop, where threads would
block forever. -/
def trapResultBang : IO Unit := do
  IO.println "dropping"
  flush
  let t ← do
    let p ← IO.Promise.new (α := Nat)
    pure p.result!
  IO.println s!"unreachable {← IO.wait t}"

/-- The cases: name, kind (`shared`: the trace is the same with one worker thread; `all`: cooperative
mode only; `trap`: ends with an internal panic), and the case. `exit-drains` must come last. -/
def cases : List (String × String × IO Unit) := [
  ("spawn-lazy", "all", spawnLazy),
  ("spawn-nested", "all", spawnNested),
  ("map-pending", "all", mapPending),
  ("map-finished", "all", mapFinished),
  ("sync-inline", "shared", syncInline),
  ("bind-pending-pq", "shared", nested true),
  ("bind-pending-qp", "shared", nested false),
  ("async-do", "shared", asyncDo),
  ("loops", "shared", loops),
  ("try-catch", "shared", tryCatch),
  ("race", "all", race),
  ("concurrently", "all", concurrently),
  ("drop-promise", "all", dropPromise),
  ("drop-promise-in-task", "all", dropPromiseInTask),
  ("reentrant", "shared", reentrant),
  ("consumer-first", "shared", consumerFirst),
  ("cancel", "shared", cancel),
  ("cancel-propagates", "shared", cancelPropagates),
  ("cancel-nested", "all", cancelNested),
  ("deep-10000", "shared", deep 10000),
  ("deep-100000", "all", deep 100000),
  ("priorities", "all", priorities),
  ("directed", "all", directed),
  ("drop-queued", "all", dropQueued),
  ("heartbeats-nested", "shared", heartbeatsNested),
  ("streams-nested", "shared", streamsNested),
  ("states", "all", states),
  ("wait-any", "shared", waitAny),
  ("sleep-yield", "all", sleepYield),
  ("exit-drains", "all", exitDrains),
  ("trap-wait-pending", "trap", trapWaitPending),
  ("trap-wait-ancestor", "trap", trapWaitAncestor),
  ("trap-blocked-sibling", "trap", trapBlockedSibling),
  ("trap-result-bang", "trap", trapResultBang)
]

def runCases (select : String → Bool) : IO Unit := do
  for (name, kind, run) in cases do
    if select kind then
      IO.println s!"== {name}"
      run

def main : List String → IO UInt32
  | ["all"] => do runCases (· != "trap"); return 0
  | ["shared"] => do runCases (· == "shared"); return 0
  | [name] => do
    match cases.find? (·.1 == name) with
    | some (_, _, run) => run; return 0
    | none => IO.eprintln s!"there is no case {name}"; return 2
  | _ => do IO.eprintln "usage: all | shared | <case>"; return 2

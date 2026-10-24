/*
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Gabriel Ebner, Henrik Böving
*/
#include <lean/lean.h>
#include "runtime/mutex.h"
#include "runtime/io.h"
#include "runtime/object.h"
#include "runtime/thread.h"

namespace lean {

#if defined(LEAN_MULTI_THREAD)
typedef mutex              basemutex;
typedef condition_variable condvar;
typedef recursive_mutex    baserecmutex;
typedef shared_mutex       basesharedmutex;
#else
// Without threads, `thread.h`'s mutexes and condition variables are no-ops: a lock would always succeed, so
// `Mutex.tryAtomically` would report a held mutex as free, and a wait would return at once, so
// `Condvar.waitUntil` would spin forever. These keep the one thread honest: locking what it holds is a
// deadlock, and a wait runs the queued tasks of the cooperative task manager, the only code that could ever
// notify.
struct basemutex {
    bool m_locked = false;
    void lock() {
        if (m_locked)
            lean_internal_panic("deadlock: the mutex is held by this thread, and the runtime has no other");
        m_locked = true;
    }
    bool try_lock() {
        if (m_locked)
            return false;
        m_locked = true;
        return true;
    }
    void unlock() { m_locked = false; }
};
struct condvar {
    void wait(basemutex & m) {
        m.unlock();
        if (!task_manager_run_pending())
            lean_internal_panic("`Condvar.wait`: nothing can notify the condition variable, the runtime has no "
                                "other thread and no task is queued");
        m.lock();
    }
    void notify_one() {}
    void notify_all() {}
};
struct baserecmutex {
    unsigned m_count = 0;
    void lock() { m_count++; }
    bool try_lock() { m_count++; return true; }
    void unlock() { m_count--; }
};
struct basesharedmutex {
    unsigned m_readers = 0;
    bool     m_writer = false;
    void lock() {
        if (m_writer || m_readers > 0)
            lean_internal_panic("deadlock: the shared mutex is held by this thread, and the runtime has no other");
        m_writer = true;
    }
    bool try_lock() {
        if (m_writer || m_readers > 0)
            return false;
        m_writer = true;
        return true;
    }
    void unlock() { m_writer = false; }
    void lock_shared() {
        if (m_writer)
            lean_internal_panic("deadlock: the shared mutex is held for writing by this thread, and the runtime "
                                "has no other");
        m_readers++;
    }
    bool try_lock_shared() {
        if (m_writer)
            return false;
        m_readers++;
        return true;
    }
    void unlock_shared() { m_readers--; }
};
#endif

static lean_external_class * g_basemutex_external_class = nullptr;
static void basemutex_finalizer(void * h) {
    delete static_cast<basemutex *>(h);
}
static void basemutex_foreach(void *, b_obj_arg) {}

static basemutex * basemutex_get(lean_object * mtx) {
    return static_cast<basemutex *>(lean_get_external_data(mtx));
}

extern "C" LEAN_EXPORT obj_res lean_io_basemutex_new() {
    return lean_alloc_external(g_basemutex_external_class, new basemutex);
}

extern "C" LEAN_EXPORT obj_res lean_io_basemutex_lock(b_obj_arg mtx) {
    basemutex_get(mtx)->lock();
    return box(0);
}

extern "C" LEAN_EXPORT uint8_t lean_io_basemutex_try_lock(b_obj_arg mtx) {
    bool success = basemutex_get(mtx)->try_lock();
    return success;
}

extern "C" LEAN_EXPORT obj_res lean_io_basemutex_unlock(b_obj_arg mtx) {
    basemutex_get(mtx)->unlock();
    return box(0);
}

static lean_external_class * g_condvar_external_class = nullptr;
static void condvar_finalizer(void * h) {
    delete static_cast<condvar *>(h);
}
static void condvar_foreach(void *, b_obj_arg) {}

static condvar * condvar_get(lean_object * mtx) {
    return static_cast<condvar *>(lean_get_external_data(mtx));
}

extern "C" LEAN_EXPORT obj_res lean_io_condvar_new() {
    return lean_alloc_external(g_condvar_external_class, new condvar);
}

extern "C" LEAN_EXPORT obj_res lean_io_condvar_wait(b_obj_arg cv, b_obj_arg mtx) {
#if defined(LEAN_MULTI_THREAD)
    unique_lock<basemutex> lock(*basemutex_get(mtx), std::adopt_lock_t());
    condvar_get(cv)->wait(lock);
    lock.release();
#else
    condvar_get(cv)->wait(*basemutex_get(mtx));
#endif
    return box(0);
}

extern "C" LEAN_EXPORT obj_res lean_io_condvar_notify_one(b_obj_arg cv) {
    condvar_get(cv)->notify_one();
    return box(0);
}

extern "C" LEAN_EXPORT obj_res lean_io_condvar_notify_all(b_obj_arg cv) {
    condvar_get(cv)->notify_all();
    return box(0);
}

static lean_external_class * g_baserecmutex_external_class = nullptr;
static void baserecmutex_finalizer(void * h) {
    delete static_cast<baserecmutex *>(h);
}
static void baserecmutex_foreach(void *, b_obj_arg) {}

static baserecmutex * baserecmutex_get(lean_object * mtx) {
    return static_cast<baserecmutex *>(lean_get_external_data(mtx));
}

extern "C" LEAN_EXPORT obj_res lean_io_baserecmutex_new() {
    return lean_alloc_external(g_baserecmutex_external_class, new baserecmutex);
}

extern "C" LEAN_EXPORT obj_res lean_io_baserecmutex_lock(b_obj_arg mtx) {
    baserecmutex_get(mtx)->lock();
    return box(0);
}

extern "C" LEAN_EXPORT uint8_t lean_io_baserecmutex_try_lock(b_obj_arg mtx) {
    bool success = baserecmutex_get(mtx)->try_lock();
    return success;
}

extern "C" LEAN_EXPORT obj_res lean_io_baserecmutex_unlock(b_obj_arg mtx) {
    baserecmutex_get(mtx)->unlock();
    return box(0);
}

static lean_external_class * g_basesharedmutex_external_class = nullptr;
static void basesharedmutex_finalizer(void * h) {
    delete static_cast<basesharedmutex *>(h);
}
static void basesharedmutex_foreach(void *, b_obj_arg) {}

static basesharedmutex * basesharedmutex_get(lean_object * mtx) {
    return static_cast<basesharedmutex *>(lean_get_external_data(mtx));
}

extern "C" LEAN_EXPORT obj_res lean_io_basesharedmutex_new() {
    return lean_alloc_external(g_basesharedmutex_external_class, new basesharedmutex);
}

extern "C" LEAN_EXPORT obj_res lean_io_basesharedmutex_write(b_obj_arg mtx) {
    basesharedmutex_get(mtx)->lock();
    return box(0);
}

extern "C" LEAN_EXPORT uint8_t lean_io_basesharedmutex_try_write(b_obj_arg mtx) {
    bool success = basesharedmutex_get(mtx)->try_lock();
    return success;
}

extern "C" LEAN_EXPORT obj_res lean_io_basesharedmutex_unlock_write(b_obj_arg mtx) {
    basesharedmutex_get(mtx)->unlock();
    return box(0);
}

extern "C" LEAN_EXPORT obj_res lean_io_basesharedmutex_read(b_obj_arg mtx) {
    basesharedmutex_get(mtx)->lock_shared();
    return box(0);
}

extern "C" LEAN_EXPORT uint8_t lean_io_basesharedmutex_try_read(b_obj_arg mtx) {
    bool success = basesharedmutex_get(mtx)->try_lock_shared();
    return success;
}

extern "C" LEAN_EXPORT obj_res lean_io_basesharedmutex_unlock_read(b_obj_arg mtx) {
    basesharedmutex_get(mtx)->unlock_shared();
    return box(0);
}

void initialize_mutex() {
    g_basemutex_external_class = lean_register_external_class(basemutex_finalizer, basemutex_foreach);
    g_condvar_external_class = lean_register_external_class(condvar_finalizer, condvar_foreach);
    g_baserecmutex_external_class = lean_register_external_class(baserecmutex_finalizer, baserecmutex_foreach);
    g_basesharedmutex_external_class = lean_register_external_class(basesharedmutex_finalizer, basesharedmutex_foreach);
}

void finalize_mutex() {
}

}

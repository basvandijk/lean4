/*
Copyright (c) 2026 Bas van Dijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Bas van Dijk

The runtime for wasm32-wasip1: what replaces the parts that are not built for it.

CMake does not build this configuration; a consumer compiles the runtime sources directly, with the
flags of the release build (`-std=c++20 -O3 -DNDEBUG -DLEAN_BUILD_TYPE=Release -DLEAN_EXPORTING
-D__CLANG__ -ffp-contract=off -fvisibility=hidden -fvisibility-inlines-hidden -fexceptions`), without
`LEAN_MULTI_THREAD`, with a `config.h` without `LEAN_MIMALLOC`, and with `-Isrc/runtime/wasi` so that
io.cpp's `<uv.h>` is uv.h in this directory. The sources are those of src/runtime/CMakeLists.txt
except process.cpp, stack_overflow.cpp, libuv.cpp, the files of uv/ and openssl.cpp (processes,
signals, libuv and OpenSSL do not exist on WASI, nor on the Internet Computer), mimalloc.cpp (no
mimalloc) and compact.cpp (.olean files and compacted regions need mmap and dl_iterate_phdr, and Init
does not use it); cadical.cpp is compiled without `LEAN_CADICAL` and provides only stubs. Without
threads the task manager runs in its cooperative mode (see `lean_run_pending_tasks` in lean.h), and
`lean_mark_mt` marks nothing. Numbers are Lean's own bignums (no GMP). The link needs `-lc++ -lc++abi`
(the runtime is C++) and a stack in linear memory for the runtime functions that have frames there,
among them `lean_apply_*` through which Lean calls closures: `-Wl,-z,stack-size=8388608` (what Lean
gives threads on 32-bit targets) and `-Wl,--stack-first`, so that an overflow traps instead of
overwriting static data; wasm-ld's default of 64 KiB runs out long before an engine's stack does.

This file defines those of the left-out files' symbols that the rest of the runtime and Lean's `Init`
library refer to. Operations that cannot work return an IO error rather than abort. It also stands
in for the C++ exception runtime, see `__cxa_throw` below.
*/
#ifndef __wasi__
#error "src/runtime/wasi/stubs.cpp belongs to the wasm32-wasip1 build only"
#endif
#include <cerrno>
#include <climits>
#include <cstdio>
#include <cstdlib>
#include <cxxabi.h> // declares the __cxa_* functions defined below
#include <typeinfo>
#include <unistd.h>
#include <lean/lean.h>
#include "runtime/exception.h"

static lean_obj_res unsupported(char const * what) {
    return lean_io_result_mk_error(lean_mk_io_error_unsupported_operation(ENOSYS, lean_mk_string(what)));
}

/* process.cpp. WASI keeps a current directory, so that part works. */

extern "C" LEAN_EXPORT lean_obj_res lean_io_process_get_current_dir() {
    char path[PATH_MAX];
    if (getcwd(path, PATH_MAX)) {
        return lean_io_result_mk_ok(lean_mk_string(path));
    } else {
        return lean_io_result_mk_error(lean_decode_io_error(errno, nullptr));
    }
}

extern "C" LEAN_EXPORT lean_obj_res lean_io_process_set_current_dir(b_lean_obj_arg path) {
    if (!chdir(lean_string_cstr(path))) {
        return lean_io_result_mk_ok(lean_box(0));
    } else {
        return lean_io_result_mk_error(lean_decode_io_error(errno, path));
    }
}

// WASI has neither process nor thread identifiers.
extern "C" LEAN_EXPORT uint32_t lean_io_process_get_pid() { return 0; }
extern "C" LEAN_EXPORT uint64_t lean_io_get_tid() { return 0; }

extern "C" LEAN_EXPORT lean_obj_res lean_io_process_spawn(lean_obj_arg args) {
    lean_dec(args);
    return unsupported("spawning processes is not supported on WASI");
}

// As spawning always fails, the remaining functions never receive a child.
extern "C" LEAN_EXPORT lean_obj_res lean_io_process_child_wait(b_lean_obj_arg, b_lean_obj_arg) {
    return unsupported("there are no child processes on WASI");
}

extern "C" LEAN_EXPORT lean_obj_res lean_io_process_child_try_wait(b_lean_obj_arg, b_lean_obj_arg) {
    return unsupported("there are no child processes on WASI");
}

extern "C" LEAN_EXPORT lean_obj_res lean_io_process_child_kill(b_lean_obj_arg, b_lean_obj_arg) {
    return unsupported("there are no child processes on WASI");
}

extern "C" LEAN_EXPORT lean_obj_res lean_io_process_child_take_stdin(b_lean_obj_arg, lean_obj_arg child) {
    lean_dec(child);
    return unsupported("there are no child processes on WASI");
}

extern "C" LEAN_EXPORT uint32_t lean_io_process_child_pid(b_lean_obj_arg, b_lean_obj_arg) {
    lean_internal_panic("there are no child processes on WASI");
}

/* libuv.cpp. The generated `main` calls this; libuv only copies `argv` so that it can change
   the process title. */
extern "C" LEAN_EXPORT char ** lean_setup_args(int, char ** argv) { return argv; }

namespace lean {
void initialize_process() {}
void finalize_process() {}
// A stack overflow traps instead: the stack sits below the static data (`--stack-first`).
void initialize_stack_overflow() {}
void finalize_stack_overflow() {}
}

/* io.cpp locks files with `flock`, which wasi-libc declares but does not define. Weak, in case
   a later wasi-libc does. */
extern "C" __attribute__((weak)) int flock(int, int) {
    errno = ENOSYS;
    return -1;
}

/* The C++ exception runtime.

   The runtime is compiled with -fexceptions so that its `throw`s compile. Without WebAssembly
   exception handling (which the Internet Computer does not support), LLVM drops all `catch`
   blocks, so a `throw` can only end the program, as an uncaught exception would. libc++abi for
   WASI is built without exception support, so we define the entry points that the compiled
   `throw`s and (unreachable) handlers call: they report what was thrown and abort, which traps.
   On the Internet Computer a trap rolls back the current message. */

extern "C" void * __cxa_allocate_exception(size_t size) noexcept {
    // Never freed: the program is about to end.
    void * p = malloc(size);
    if (!p) abort();
    return p;
}

// The message of the Lean runtime's own exceptions; `type` is the exact type of `obj`.
static char const * lean_exception_message(void * obj, std::type_info const & type) {
    if (type == typeid(lean::exception)) return static_cast<lean::exception *>(obj)->what();
    if (type == typeid(lean::stack_space_exception)) return static_cast<lean::stack_space_exception *>(obj)->what();
    if (type == typeid(lean::memory_exception)) return static_cast<lean::memory_exception *>(obj)->what();
    if (type == typeid(lean::heartbeat_exception)) return static_cast<lean::heartbeat_exception *>(obj)->what();
    return nullptr;
}

// (In the WebAssembly C++ ABI, destructors return `this`.)
extern "C" void __cxa_throw(void * obj, std::type_info * type, void * (*)(void *)) {
    char const * msg = lean_exception_message(obj, *type);
    // The type name stays mangled: the demangler would add over 100 KB of code.
    fprintf(stderr, "uncaught C++ exception of type %s%s%s\n", type->name(), msg ? ": " : "", msg ? msg : "");
    abort();
}

extern "C" void * __cxa_begin_catch(void *) noexcept {
    abort();
}

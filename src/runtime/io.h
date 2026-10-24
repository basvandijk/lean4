/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <errno.h>
#include <stdio.h>
#include <string>
#include <lean/lean.h>

namespace lean {
inline lean_obj_res io_result_mk_ok(lean_obj_arg a) { return lean_io_result_mk_ok(a); }
inline lean_obj_res io_result_mk_error(lean_obj_arg e) { return lean_io_result_mk_error(e); }
LEAN_EXPORT lean_obj_res io_result_mk_error(char const * msg);
LEAN_EXPORT lean_obj_res io_result_mk_error(std::string const & msg);
inline lean_obj_res decode_io_error(int errnum, b_lean_obj_arg fname) { return lean_decode_io_error(errnum, fname); }
inline lean_obj_res decode_uv_error(int errnum, b_lean_obj_arg fname) { return lean_decode_uv_error(errnum, fname); }
inline lean_obj_res io_result_mk_uv_error(int errnum) { return io_result_mk_error(decode_uv_error(errnum, nullptr)); }
inline lean_obj_res io_result_mk_enomem() { return io_result_mk_error(decode_io_error(ENOMEM, nullptr)); }
LEAN_EXPORT lean_obj_res mk_embedded_nul_error(b_lean_obj_arg str);
LEAN_EXPORT lean_obj_res io_wrap_handle(FILE * hfile);
/* Makes the current thread's standard streams the process's for its scope, and restores the thread's
   afterwards: for a task the cooperative task manager runs on a waiting thread's stack, which must not
   inherit that thread's redirections (`IO.setStdout`, `IO.FS.withIsolatedStreams`), as a task on a worker
   thread would not. */
class LEAN_EXPORT scoped_default_streams {
    lean_object * m_stdin;
    lean_object * m_stdout;
    lean_object * m_stderr;
public:
    scoped_default_streams();
    ~scoped_default_streams();
};
void initialize_io();
void finalize_io();
}

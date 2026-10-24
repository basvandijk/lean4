/*
Copyright (c) 2020 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sebastian Ullrich
*/
#pragma once
// WASI has no signals; stack_overflow.cpp is not built there.
#if !defined(LEAN_WINDOWS) && !defined(__wasi__)
#include <csignal>
#endif

namespace lean {
class stack_guard {
#if !defined(LEAN_WINDOWS) && !defined(__wasi__)
    // We need a separate signal stack since we can't use the overflowed stack
    stack_t m_signal_stack;
#endif
public:
    stack_guard();
    ~stack_guard();
};

void initialize_stack_overflow();
void finalize_stack_overflow();
}

# Cooperative mode of the task manager, no worker threads, for the compiled binary and the interpreter.
export LEAN_NUM_THREADS=0
TEST_LEANI_ARGS+=( -j0 )
TEST_ARGS=( all )

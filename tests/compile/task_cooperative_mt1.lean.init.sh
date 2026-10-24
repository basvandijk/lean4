# The cases whose trace is the same with one worker thread as in cooperative mode: the traces of
# `task_cooperative.lean` are schedules the threaded task manager can produce.
export LEAN_NUM_THREADS=1
TEST_LEANI_ARGS+=( -j1 )
TEST_ARGS=( shared )

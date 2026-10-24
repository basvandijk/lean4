# The same with the cooperative task manager (no worker threads): the dedicated task, queued at the highest
# regular priority, runs when the task manager is finalized.
export LEAN_NUM_THREADS=0
TEST_LEANI_ARGS+=( -j0 )

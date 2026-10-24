# Cooperative mode of the task manager (no worker threads); the libuv loop thread resolves the promise.
export LEAN_NUM_THREADS=0
TEST_LEANI_ARGS+=( -j0 )

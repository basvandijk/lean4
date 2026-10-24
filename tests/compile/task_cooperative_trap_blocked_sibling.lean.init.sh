# A wait in cooperative mode that nothing can finish ends with an internal panic (see `task_cooperative.lean`).
export LEAN_NUM_THREADS=0
TEST_LEANI_ARGS+=( -j0 )
TEST_ARGS=( trap-blocked-sibling )
TEST_EXIT=1

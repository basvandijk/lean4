import Std.Internal.UV

/-!
A wait in cooperative mode (no worker threads, `LEAN_NUM_THREADS=0`) on a promise that the libuv loop
thread resolves: the waiting thread has nothing queued to run, and waits for the loop.
-/

open Std.Internal.UV in
def main : IO Unit := do
  IO.println "before"
  let timer ← Timer.mk 10 false
  let p ← timer.next
  discard <| IO.wait p.result?
  IO.println "after"

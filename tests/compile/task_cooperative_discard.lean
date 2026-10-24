/-!
`lean_io_promise_discard` in the task manager's cooperative mode (no worker threads, `LEAN_NUM_THREADS=0`):
resolving a promise without running the tasks that wait for it, for a host whose callback must not run
Lean code, such as a cleanup after a trapped callback. Compiled only: the interpreter cannot call an
`@[extern]` declaration of the file it runs.
-/

@[extern "lean_io_promise_discard"]
opaque discardPromise (promise : @& IO.Promise Nat) : BaseIO Unit

/-- Discarding a promise (`lean_io_promise_discard`, for a host whose callback must not run Lean code):
the continuation does not run, nor does the one on the inner promise that it captured, which is dropped
with it, so that its task resolves to `none`; the outer continuation's task, whose handle is kept, never
finishes. Resolving the promise afterwards does nothing. -/
def discard : IO Unit := do
  let p ← IO.Promise.new (α := Nat)
  let (t, tq) ← do
    let q ← IO.Promise.new (α := Nat)
    let t ← IO.bindTask p.result? fun v => do
      IO.println s!"continuation {v}"
      IO.mapTask (fun w => do IO.println s!"q continuation {w}"; return w.getD 0) q.result?
    pure (t, q.result?)
  IO.println "setup done"
  discardPromise p
  IO.println "discarded"
  IO.println s!"outer task: {← IO.getTaskState t}"
  IO.println s!"inner promise's task: {← IO.wait tq}"
  p.resolve 1
  IO.println "after resolve p"

def main : IO Unit := discard

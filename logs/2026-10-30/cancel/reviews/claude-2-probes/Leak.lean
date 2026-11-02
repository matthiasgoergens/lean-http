def arm (capture : Bool) (done : IO.Promise Bool) : BaseIO Unit := do
  let r : IO.Ref (IO.Promise Unit) ← IO.mkRef (← IO.Promise.new)
  let p ← r.get
  if capture then
    BaseIO.chainTask (sync := true) p.result? fun v => do
      let _ ← r.get
      done.resolve v.isSome
  else
    BaseIO.chainTask (sync := true) p.result? fun v => done.resolve v.isSome

def main : IO Unit := do
  for capture in [false, true] do
    let done ← IO.Promise.new
    arm capture done
    IO.sleep 300
    let fin ← IO.hasFinished done.result?
    IO.println s!"closure captures the ref holding its promise: {capture}; continuation ran: {fin}"

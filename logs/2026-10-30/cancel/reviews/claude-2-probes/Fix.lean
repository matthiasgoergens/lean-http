def arm (done : IO.Promise Bool) : BaseIO (IO.Ref (IO.Promise Unit)) := do
  let r : IO.Ref (IO.Promise Unit) ← IO.mkRef (← IO.Promise.new)
  let p ← r.get
  BaseIO.chainTask (sync := true) p.result? fun v => do
    let _ ← r.get
    done.resolve v.isSome
  return r

def main : IO Unit := do
  for dropAtEnd in [false, true] do
    let done ← IO.Promise.new
    let r ← arm done
    if dropAtEnd then r.set (← IO.Promise.new)
    IO.sleep 300
    IO.println s!"bell replaced at the end: {dropAtEnd}; continuation ran: {← IO.hasFinished done.result?}"

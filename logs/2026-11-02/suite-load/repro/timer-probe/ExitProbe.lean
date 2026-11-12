import Std.Async
/-! What delays a process's exit after `main` returns: `exitprobe dedicated|pool|timer MS`. -/
def main (args : List String) : IO Unit := do
  let ms := (args[1]? >>= String.toNat?).getD 3000
  match args[0]? with
  | some "dedicated" => discard <| IO.asTask (prio := .dedicated) (IO.sleep ms.toUInt32)
  | some "pool" => discard <| IO.asTask (IO.sleep ms.toUInt32)
  | some "timer" => discard <| (Std.Async.EAsync.toBaseIO (Std.Async.sleep (.ofNat ms)) : BaseIO _)
  | _ => pure ()
  IO.println "main returning"

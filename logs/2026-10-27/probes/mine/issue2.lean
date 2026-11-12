def main (args : List String) : IO UInt32 := do
  let variant := args[0]!
  let p : IO.Promise Nat ← IO.Promise.new
  let _ ← IO.asTask (prio := .dedicated) do
    IO.sleep 200
    p.resolve 1
  let _ ← IO.asTask do
    let v : Nat ← match variant with
      | "direct" => pure ((p.result?.get).getD 0)
      | "mappedsync" => pure ((p.result?.map (sync := true) (fun o => o.getD 0)).get)
      | _ => pure ((p.result?.map (fun o => o.getD 0)).get)
    IO.eprintln s!"pool task got {v}"
  IO.sleep 50
  return 0

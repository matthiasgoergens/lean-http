/-- Minimal exit-hang repro with no sockets and no Std.Async.
Usage: prom <variant> <main_ms> <resolve_ms>
A pool task blocks in `Task.get` on something that depends on a promise; another thread resolves the
promise after <resolve_ms>; `main` returns after <main_ms>.
  mapped      the pool task blocks on a `Task.map` of the promise's result (a dependent task that needs a pool worker to run)
  direct      the pool task blocks on the promise's result task itself (no dependent task)
  mappedsync  like mapped, but the map is `sync := true` (runs on the resolving thread)
  mappedjoin  like mapped, but main first waits for the pool task before returning -/
def main (args : List String) : IO UInt32 := do
  let variant := args[0]!
  let mainMs := args[1]!.toNat!
  let resolveMs := args[2]!.toNat!
  let p : IO.Promise Nat ← IO.Promise.new
  -- the resolver: a dedicated thread, so it is not a pool worker
  let _r ← IO.asTask (prio := .dedicated) do
    IO.sleep resolveMs.toUInt32
    p.resolve 1
    IO.eprintln "promise resolved"
  let t ← IO.asTask do
    let v : Nat ← match variant with
      | "direct" => pure ((p.result?.get).getD 0)
      | "mappedsync" => pure ((p.result?.map (sync := true) (fun o => o.getD 0)).get)
      | _ => pure ((p.result?.map (fun o => o.getD 0)).get)
    IO.eprintln s!"pool task got {v}"
    return v
  IO.sleep mainMs.toUInt32
  if variant == "mappedjoin" then discard <| IO.wait t
  IO.eprintln "main returning"
  return 0

structure C where
  tokens : Array Nat
  signal : IO.Promise (Option Nat)
  bell : IO.Ref (IO.Promise Unit)

set_option trace.compiler.ir.result true in
def race (c : C) (winner : IO.Promise Nat) : BaseIO Unit := do
  let bell ← IO.Promise.new
  c.bell.set bell
  let tokens := c.tokens
  BaseIO.chainTask (sync := true) bell.result? fun
    | some () => do
      let r ← tokens.findSomeM? fun t => pure (if t > 3 then some t else none)
      winner.resolve (r.getD 0)
    | none => pure ()

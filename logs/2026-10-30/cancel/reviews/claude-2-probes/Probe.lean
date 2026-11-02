structure C where
  tokens : Array Nat
  signal : IO.Promise (Option Nat)
  bell : IO.Ref (IO.Promise Unit)

def reason? (c : C) : BaseIO (Option Nat) := do
  let t := c.signal.result?
  if ← IO.hasFinished t then return t.get.join
  for x in c.tokens do
    if x > 3 then return some x
  return none

set_option trace.compiler.ir.result true in
def race (c : C) (winner : IO.Promise Nat) : BaseIO Unit := do
  let bell ← IO.Promise.new
  c.bell.set bell
  BaseIO.chainTask (sync := true) bell.result? fun
    | some () => do winner.resolve ((← reason? c).getD 0)
    | none => pure ()

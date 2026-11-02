module

public import Std.Async.Select
import all Std.Async.Select
public import Std.Sync.CancellationToken

open Std.Async

def consumers (t : Std.CancellationToken) : BaseIO Nat :=
  t.state.atomically (m := BaseIO) do return (← get).consumers.toArray.size

public def main (args : List String) : IO Unit := do
  let mode := args.headD "inline"
  let token ← Std.CancellationToken.new
  let promise : IO.Promise (Except IO.Error Unit) ← IO.Promise.new
  let waiter : Waiter Unit := Waiter.mk (← IO.mkRef false) promise
  let ran ← IO.mkRef false
  let tid0 ← IO.getTID
  let tidIn ← IO.mkRef (0 : UInt64)
  BaseIO.chainTask (sync := true) promise.result? fun
    | some (.ok ()) => do
      tidIn.set (← IO.getTID)
      if mode == "ask" then
        let r ← token.getCancellationReason
        IO.eprintln s!"asked inside: {repr r}" |>.catchExceptions fun _ => pure ()
      ran.set true
    | _ => pure ()
  discard <| (token.selector.registerFn waiter).toBaseIO
  IO.println s!"consumers after register: {← consumers token}"
  if mode == "finish" then
    waiter.race (pure ()) fun p => p.resolve (.error (IO.userError "ended"))
    discard <| (token.selector.unregisterFn).toBaseIO
    IO.println s!"consumers after finish: {← consumers token}"
    IO.println s!"chain ran (should be false): {← ran.get}"
    return
  -- cancel from a dedicated thread so that a deadlock does not hang main
  let t ← IO.asTask (prio := .dedicated) (token.cancel .deadline)
  IO.sleep 500
  IO.println s!"cancel finished within 500ms: {← IO.hasFinished t}"
  IO.println s!"chain ran: {← ran.get}; same thread as canceller? tidIn={← tidIn.get} main={tid0}"
  if mode == "ask" then
    IO.println "exiting (a deadlocked thread may keep the process alive)"
    IO.Process.exit 0

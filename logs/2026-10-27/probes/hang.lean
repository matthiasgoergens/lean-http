import Std.Async
open Std Async TCP Socket Net

def run (x : Async α) : IO (Except IO.Error α) := x.block.toBaseIO

def showR : Except IO.Error String → String
  | .error e => s!"error({e})"
  | .ok s => s

def recvStr (r : Option ByteArray) : String :=
  match r with | none => "EOF" | some b => s!"{b.size} bytes"

/- Usage: hang <port> <variant> <arg_ms> <hold_ms> [<nconns> [<exit-style>]]
  variants:
   bg        background task `Selectable.one #[recv selector]` registered, abandoned; main sleeps hold_ms, returns
   bg2       two connections, each with its own abandoned background selector
   timeout   `Selectable.one #[recv selector, sleep arg_ms]` awaited in main (timeout path cancels the selector); then hold, return
   timeoutN  like timeout but repeated nconns times on the same connection (cancel/re-register), then return
   plain     background plain `recv?` (no selector) abandoned
   bgcancel  like bg, but main calls `cancelRecv` on the socket before returning
   bgshut    like bg, but main shuts the write side down and calls cancelRecv before returning
   bgdrop    like bg, but the main's reference to the socket is dropped before the hold (only the selector holds it)
   mybg      like bg, but with `ownRecvSelector` (non-blocking registration callback)
   mycancel  like mybg, but main calls `cancelRecv` before returning
   closeable like bg, but the Selectable.one also has a `closed` alternative; main resolves it at hold_ms and waits for the task to end before returning
   none      connect and exchange only (control)
-/
/-- A recv selector whose registration callback never blocks a pool thread: it takes the `recv?` promise
itself and races on its result.  It reads when registered (so bytes read by a lost race are dropped). -/
def ownRecvSelector (s : Client) (size : UInt64) : Selector (Option ByteArray) where
  tryFn := pure none
  registerFn waiter := do
    let p ← s.native.recv? size
    discard <| IO.mapTask (t := p.result?) fun res => do
      match res with
      | none => return ()
      | some res => waiter.race (pure ()) (fun promise => promise.resolve res)
  unregisterFn := s.native.cancelRecv

/-- A selector that becomes ready when `p` is resolved (used to wake a waiting loop so it can end normally). -/
def promiseSelector (p : IO.Promise Unit) : Selector Unit where
  tryFn := do if (← p.isResolved) then return some () else return none
  registerFn waiter := do
    discard <| IO.mapTask (t := p.result?) fun res => do
      match res with
      | none => return ()
      | some _ => waiter.race (pure ()) (fun promise => promise.resolve (.ok ()))
  unregisterFn := pure ()

def main (args : List String) : IO UInt32 := do
  let port := args[0]!.toNat!
  let variant := args[1]!
  let argMs := args[2]!.toNat!
  let hold := args[3]!.toNat!
  let n := (args[4]?.map String.toNat!).getD 1
  let addr := SocketAddress.v4 ⟨IPv4Addr.ofParts 127 0 0 1, port.toUInt16⟩
  let connect : IO Client := do
    let s ← Client.mk
    (do s.connect addr; s.send "ping".toUTF8 : Async Unit).block
    return s
  -- registered without blocking a thread on the result (Async.toIO), as an HTTP connection loop would
  let bgSel (s : Client) : IO (AsyncTask String) :=
    (do
      let r ← Selectable.one #[.case (Client.recvSelector s 65536) fun r => pure (recvStr r)]
      IO.eprintln s!"bg selector finished: {r}"
      pure r : Async String).toIO
  match variant with
  | "none" =>
    let _s ← connect
    IO.sleep hold.toUInt32
  | "bg" | "bgcancel" | "bgshut" =>
    let s ← connect
    let _t ← bgSel s
    IO.sleep hold.toUInt32
    if variant == "bgcancel" || variant == "bgshut" then
      if variant == "bgshut" then discard <| run (s.shutdown)
      s.native.cancelRecv
      IO.eprintln "cancelRecv done"
  | "mybg" | "mycancel" =>
    let s ← connect
    let _t ← (do
      let r ← Selectable.one #[.case (ownRecvSelector s 65536) fun r => pure (recvStr r)]
      IO.eprintln s!"bg selector finished: {r}"
      pure r : Async String).toIO
    IO.sleep hold.toUInt32
    if variant == "mycancel" then
      s.native.cancelRecv
      IO.eprintln "cancelRecv done"
  | "closeable" =>
    let s ← connect
    let closed ← IO.Promise.new
    let t ← (do
      let r ← Selectable.one #[
        .case (Client.recvSelector s 65536) fun r => pure s!"recv: {recvStr r}",
        .case (promiseSelector closed) fun _ => pure "closed"]
      IO.eprintln s!"bg selector finished: {r}"
      pure r : Async String).toIO
    IO.sleep hold.toUInt32
    closed.resolve ()
    let r ← IO.wait t
    IO.eprintln s!"loop ended: {repr (r.toOption)}"
  | "bgloop" | "mybgloop" | "closeloop" =>
    -- a body-reader style loop: keep selecting on recv while a large response streams in; main abandons it
    let s ← connect
    let closed ← IO.Promise.new
    let total ← IO.mkRef 0
    let sel := if variant == "mybgloop" then ownRecvSelector s 65536 else Client.recvSelector s 65536
    let t ← (do
      let mut stop := false
      while !stop do
        let r ← Selectable.one (if variant == "closeloop" then
          #[.case sel fun r => pure (some r), .case (promiseSelector closed) fun _ => pure none]
          else #[.case sel fun r => pure (some r)])
        match r with
        | some (some b) => total.modify (· + b.size)
        | _ => stop := true
      pure () : Async Unit).toIO
    IO.sleep hold.toUInt32
    if variant == "closeloop" then
      closed.resolve ()
      IO.wait t >>= fun r => IO.eprintln s!"loop ended: {repr (r.toOption)}"
    IO.eprintln s!"read {← total.get} bytes before main returned"
  | "bgdrop" =>
    let _t ← (do let s ← connect; bgSel s)
    IO.sleep hold.toUInt32
  | "bg2" =>
    let s1 ← connect
    let s2 ← connect
    let _t1 ← bgSel s1
    let _t2 ← bgSel s2
    IO.sleep hold.toUInt32
  | "plain" =>
    let s ← connect
    let _t ← (do let r ← s.recv? 65536; IO.eprintln s!"plain recv finished: {recvStr r}" : Async Unit).toIO
    IO.sleep hold.toUInt32
  | "timeout" | "timeoutN" =>
    let s ← connect
    let reps := if variant == "timeout" then 1 else n
    for i in [0:reps] do
      let r ← run (do
        let sl ← Selector.sleep ⟨argMs⟩
        Selectable.one #[
          .case (Client.recvSelector s 65536) fun r => pure s!"recv: {recvStr r}",
          .case sl fun _ => pure "timeout"])
      IO.eprintln s!"round {i}: {showR r}"
    IO.sleep hold.toUInt32
  | _ => IO.eprintln "bad variant"
  IO.eprintln "main returning"
  return 0

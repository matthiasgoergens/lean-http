module

public import Std.Async.TCP
public import LeanHttp.Tls
public import LeanHttp.Cancel
public import LeanHttp.Wait

public section

/-!
# Transports: plain TCP, or TLS over TCP

A connection's bytes travel over a `Transport`: a TCP socket, or a TCP socket with a TLS session.
The exchange core sees plaintext either way.  TLS has no task of its own: the task driving the
connection (`Live`, in `LeanHttp.Body`) does the TLS work in its own steps, so a session is driven
by one task at a time, in sequence.  (Another task may mark it failed, `cancelRecv`, when the callback
of `withResponse` ends during a read; the C side's lock makes that safe.)

- A write is encrypted at once and its ciphertext handed to the TCP socket (`startSend`); it
  completes when that TCP write does.
- A read is answered at once from what the session already holds, or else becomes a TCP receive of
  ciphertext (`startRead`).  When that completes, `absorb` feeds the bytes to the session and
  decrypts: plaintext, a clean end (`close_notify`), a failure (an end without `close_notify` is a
  truncation), or nothing yet, in which case the driver tells the exchange core the time and
  registers the next receive with `startRead`, as a step of its own, so that its checks before every
  wait apply to it as to any receive.
- Cancelling the pending receive is the TCP socket's `cancelRecv` for both.

The handshake (`handshake`) and the idle check (`idleClean`) are short loops in the calling task.
-/

namespace LeanHttp

set_option linter.all true

open Std.Net Std.Async

/--
How a connection's bytes travel.
-/
inductive Transport where
  /--
  Plain TCP.
  -/
  | tcp (socket : TCP.Socket.Client)

  /--
  TLS over TCP, after a complete handshake.
  -/
  | tls (socket : TCP.Socket.Client) (session : Tls.Session)

namespace Transport

/--
The TCP socket underneath.
-/
def socket : Transport → TCP.Socket.Client
  | .tcp s => s
  | .tls s _ => s

/--
Whether the transport is TLS.
-/
def isTls : Transport → Bool
  | .tcp _ => false
  | .tls .. => true

/--
The bytes asked for in one TCP receive of ciphertext: at least a whole TLS record (16 KiB of
plaintext and its overhead), and no less than the plaintext asked for.
-/
def cipherReadBytes (max : Nat) : Nat :=
  Nat.max max (16 * 1024 + 512)

/--
Hands the ciphertext a session produced to the TCP socket, if there is any, and returns the task of
that write.  Writes are queued by libuv in the order they are issued.
-/
def flush (socket : TCP.Socket.Client) (session : Tls.Session) :
    IO (Option (AsyncTask Unit)) := do
  let out ← session.takeOutput
  if out.isEmpty then return none
  return some (← start (socket.send out))

/--
Starts a write of `bytes` (plaintext): for TLS, encrypts them and hands the ciphertext to the TCP
socket.  The task completes when the TCP write does, or at once with the error if encryption failed.
-/
def startSend (t : Transport) (bytes : ByteArray) : BaseIO (AsyncTask Unit) :=
  match t with
  | .tcp s => start (s.send bytes)
  | .tls s session => do
    let started ← (do session.write bytes; flush s session).toBaseIO
    match started with
    | .ok (some task) => return task
    | .ok none => return Task.pure (.ok ())
    | .error e => return Task.pure (.error e)

/--
A read the transport started: its result is plaintext already (`plain`), or ciphertext from the TCP
socket that `absorb` must feed to the session first (`cipher`).
-/
inductive Arrival where
  /--
  Plaintext, the clean end of input (`none`), or a failure.
  -/
  | plain (result : Except IO.Error (Option ByteArray))

  /--
  What a TCP receive under TLS gave: ciphertext, the end of TCP input, or a failure.
  -/
  | cipher (result : Except IO.Error (Option ByteArray))

/--
What a session's read step means for the reader: plaintext, the clean end, a failure, or `none`
when it needs more input.
-/
def ofStep : Tls.ReadStep → Option (Except IO.Error (Option ByteArray))
  | .data bytes => some (.ok (some bytes))
  | .closed => some (.ok none)
  | .truncated detail => some (.error (IO.userError detail))
  | .failed detail => some (.error (IO.userError detail))
  | .wantRead => none

/--
Starts a read of at most `max` bytes of plaintext.  For TLS: what the session already holds answers
it at once; otherwise a TCP receive of ciphertext starts.  Output the session produced while reading
(a key update's reply) is sent; nothing waits for it.
-/
def startRead (t : Transport) (max : Nat) : BaseIO (Task Arrival) :=
  match t with
  | .tcp s => do
    let task ← start (s.recv? max.toUInt64)
    return Task.map (sync := true) Arrival.plain task
  | .tls s session => do
    let held ← (do
        let step ← session.read max
        discard <| flush s session
        return ofStep step).toBaseIO
    match held with
    | .ok (some result) => return Task.pure (.plain result)
    | .error e => return Task.pure (.plain (.error e))
    | .ok none =>
      let task ← start (s.recv? (cipherReadBytes max).toUInt64)
      return Task.map (sync := true) Arrival.cipher task

/--
Feeds what a TCP receive under TLS gave to the session and reads up to `max` bytes of plaintext:
the result for the reader, or `none` if the session needs more input (the driver then starts the
next read).  A TCP failure is the reader's failure; the end of TCP input is told to the session,
which reports a clean end after `close_notify` and a truncation otherwise.  Output the session
produced is sent; nothing waits for it.
-/
def absorb (t : Transport) (max : Nat) (result : Except IO.Error (Option ByteArray)) :
    BaseIO (Option (Except IO.Error (Option ByteArray))) :=
  match t with
  | .tcp _ => return some result
  | .tls s session => do
    let r ← (do
        match result with
        | .error e =>
          session.poison
          return some (Except.error (IO.userError s!"TLS: the connection failed: {e}"))
        | .ok (some bytes) => session.feed bytes
        | .ok none => session.feedEof
        let step ← session.read max
        discard <| flush s session
        -- After the end of input OpenSSL reports an end or a failure; should it ask for more
        -- anyway, the reader fails rather than waiting on a socket that has ended.
        if result matches .ok none then
          if step matches .wantRead then
            session.poison
            return some (Except.error (IO.userError "TLS: the connection ended within a record"))
        return ofStep step : IO (Option (Except IO.Error (Option ByteArray)))).toBaseIO
    match r with
    | .ok r => return r
    | .error e => return some (.error e)

/--
Cancels the pending receive, if any, so that no receive registration outlives the exchange.  A
TLS read given up while it was pending may have taken ciphertext from the socket that the session
never saw, so the session is marked failed and the connection is never reused.
-/
def cancelRecv (t : Transport) (pending : Bool) : BaseIO Unit := do
  t.socket.native.cancelRecv.catchExceptions fun _ => pure ()
  if pending then
    if let .tls _ session := t then
      session.poison.catchExceptions fun _ => pure ()

/--
Whether the transport holds nothing that could belong to a later exchange: always for TCP (the
kernel's buffer is the idle check's business); for TLS, a session that holds no plaintext or
ciphertext, has seen no `close_notify`, no end of input and no failure.  A connection goes back to
the pool only if this holds.
-/
def clean (t : Transport) : BaseIO Bool :=
  match t with
  | .tcp _ => return true
  | .tls _ session => session.clean.catchExceptions fun _ => pure false

/--
Lets an idle connection go: for TLS, sends `close_notify`, best effort, and waits for nothing; the
write completes or is abandoned like any other once the socket is no longer referenced.  Never
called with an exchange in progress.
-/
def release (t : Transport) : BaseIO Unit :=
  match t with
  | .tcp _ => pure ()
  | .tls s session =>
    (do session.closeNotify; discard <| flush s session).catchExceptions fun _ => pure ()

/--
The TLS version negotiated, or `none` for TCP.
-/
def tlsVersion (t : Transport) : BaseIO (Option String) :=
  match t with
  | .tcp _ => return none
  | .tls _ session => do
    match ← session.version.toBaseIO with
    | .ok v => return some v
    | .error _ => return some ""

/--
Whether an idle connection is still clean: nothing arrived on it within `ms` milliseconds of
starting to wait for input (no bytes, no end of input, no error), and, for TLS, the session holds
nothing (`clean`).  The wait is cancelled before this returns, so no receive stays pending.  It does
not read: a connection that is not clean is closed.
-/
def idleClean (t : Transport) (ms : Nat) : Async Bool := do
  unless ← t.clean do return false
  let socket := t.socket
  let waiter ← try socket.native.waitReadable catch _ => return false
  let result ← try awaitFirst #[waiter.result?] ms catch _ => pure (some none)
  socket.native.cancelRecv
  return result.isNone

end Transport

/--
How a TLS handshake failed.
-/
inductive HandshakeFailure where
  /-- The certificate or the name was refused. -/
  | verify (detail : String)
  /-- An alert or a protocol failure. -/
  | failed (detail : String)
  /-- The connection closed or failed during the handshake. -/
  | closed (detail : String)
  /-- `Config.tlsHandshakeTimeoutMs` ran out. -/
  | timedOut
  /-- The call's deadline passed. -/
  | deadline
  /-- The call was cancelled. -/
  | cancelled (reason : Std.CancellationReason)
deriving Repr

/--
Runs the handshake of `session` over `socket` until it completes and its last flight has been
written, or it fails, or `timeoutAt` or `deadline` (values of `IO.monoMsNow`) passes, or the call is
cancelled.  On a time-out or a cancellation the pending receive is cancelled; no receive is pending
when this returns.  A write of the handshake still in flight is abandoned.
-/
partial def handshake (socket : TCP.Socket.Client) (session : Tls.Session) (timeoutAt deadline : Nat)
    (cancel : Cancel) (lastWrite : Option (AsyncTask Unit) := none) (ended : Bool := false) :
    Async (Except HandshakeFailure Unit) := do
  -- A wait that timed out ended no earlier than the earlier of the two times: when the deadline came
  -- first, the wait was for the deadline, and a wait that woke late may find it passed as well.
  let late : BaseIO HandshakeFailure := do
    return if deadline ≤ timeoutAt || deadline ≤ (← IO.monoMsNow) then .deadline else .timedOut
  let step ← try session.handshake catch e => pure (.failed (toString e))
  let written ← try Transport.flush socket session catch e => return .error (.closed (toString e))
  let lastWrite := written <|> lastWrite
  match step with
  | .verify detail => return .error (.verify detail)
  | .failed detail => return .error (.failed detail)
  | .closed detail => return .error (.closed detail)
  | .done =>
    let some task := lastWrite | return .ok ()
    match ← cancel.race #[task] (Nat.min timeoutAt deadline - (← IO.monoMsNow)) with
    | .timedOut => return .error (← late)
    | .cancelled reason => return .error (.cancelled reason)
    | .done (.error e) => return .error (.closed s!"writing the handshake: {e}")
    | .done (.ok ()) => return .ok ()
  | .wantRead =>
    -- After the end of input OpenSSL reports a failure; should it ask for more anyway, the
    -- connection has closed.
    if ended then return .error (.closed "the server closed the connection")
    let left := Nat.min timeoutAt deadline - (← IO.monoMsNow)
    if left == 0 then return .error (← late)
    let recv ← start (socket.recv? (Transport.cipherReadBytes 0).toUInt64)
    match ← cancel.race #[recv] left with
    | .timedOut =>
      socket.native.cancelRecv.catchExceptions fun _ => pure ()
      return .error (← late)
    | .cancelled reason =>
      socket.native.cancelRecv.catchExceptions fun _ => pure ()
      return .error (.cancelled reason)
    | .done (.error e) => return .error (.closed (toString e))
    | .done (.ok input) =>
      let fed ← (match input with
        | some bytes => session.feed bytes
        | none => session.feedEof).toBaseIO
      if let .error e := fed then return .error (.failed (toString e))
      handshake socket session timeoutAt deadline cancel lastWrite input.isNone

end LeanHttp

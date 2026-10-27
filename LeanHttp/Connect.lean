module

public import Std.Async.TCP
public import Std.Async.DNS
public import LeanHttp.Address
public import LeanHttp.Backoff
public import LeanHttp.Config
public import LeanHttp.Error
public import LeanHttp.Wait

public section

/-!
# Connecting

Name resolution, bounded only by the call's deadline and the resolver's own timeouts, then rounds of
connect attempts, with backoff between rounds.

Within a round the addresses are tried in order, each with its own time limit
(`Config.connectTimeoutMs`).  The next attempt starts when the current one fails, or when it has not
succeeded after `Config.connectStaggerMs`, a simple form of Happy Eyeballs (RFC 8305).  The first
attempt to connect wins.  The others are abandoned: a loser that connects later has its socket
dropped, which closes it.  v4.34.1 cannot cancel a pending connect, so a loser still waiting for an
answer keeps its socket until the kernel gives up on it; it holds no worker and does not keep the
process from exiting.

A round fails when every attempt in it has failed.  The client then waits a jittered backoff
(`LeanHttp.Backoff`) and starts the next round, up to `Config.maxConnectRetries` more, all within
the call's deadline.
-/

namespace LeanHttp

set_option linter.all true

open Std.Net Std.Async

/--
A connected socket.
-/
structure Connected where
  /--
  The socket, with `TCP_NODELAY` set if the configuration asks for it.
  -/
  socket : TCP.Socket.Client

  /--
  The address it is connected to.
  -/
  address : SocketAddress

  /--
  Every attempt that did not win, in every round.
  -/
  attempts : Array ConnectAttempt

  /--
  How many rounds of attempts were made, counting the successful one.
  -/
  rounds : Nat

/--
Why connecting failed.
-/
inductive ConnectError where
  /--
  Name resolution failed, or found no address.
  -/
  | resolve (host : String) (detail : String)

  /--
  Every attempt of every round failed.
  -/
  | exhausted (attempts : Array ConnectAttempt) (rounds : Nat)

  /--
  The call's deadline passed while connecting.
  -/
  | deadline (attempts : Array ConnectAttempt) (rounds : Nat)

namespace Connect

/--
One connect attempt: a fresh socket, connected to `addr` within `timeoutMs`, with `TCP_NODELAY` set
on success if `noDelay`.
-/
def attempt (addr : SocketAddress) (timeoutMs : Nat) (noDelay : Bool) :
    Async (Except AttemptOutcome TCP.Socket.Client) := do
  let socket ← TCP.Socket.Client.mk
  let connecting ← start (socket.connect addr)
  match ← awaitWithin connecting timeoutMs with
  | none => return .error .timedOut
  | some (.error err) => return .error (.failed (toString err))
  | some (.ok ()) =>
    if noDelay then
      try
        socket.noDelay
      catch err =>
        return .error (.failed s!"setting TCP_NODELAY: {err}")
    return .ok socket

/--
What a round of attempts came to.
-/
inductive RoundResult where
  /--
  An attempt connected.
  -/
  | connected (socket : TCP.Socket.Client) (address : SocketAddress)

  /--
  Every attempt failed.
  -/
  | failed

  /--
  The deadline passed first.
  -/
  | deadline

/--
What one wait inside a round ended with.
-/
private inductive Woken where
  | won
  | attemptEnded
  | allEnded

/--
Who holds the winning socket of a round.  The socket lives here, and only here, from the moment an
attempt connects until the round hands it over, so that attempts still pending after the round
reference no socket but their own.
-/
private inductive Slot where
  | open
  | won (index : Nat) (socket : TCP.Socket.Client)
  | closed

/--
One round of attempts over `addrs`, in order, staggered.  Returns the round's result and the record
of every attempt started, except the one that won.
-/
def round (config : Config) (roundIndex : Nat) (addrs : Array SocketAddress) (deadline : Nat) :
    Async (RoundResult × Array ConnectAttempt) := do
  let slot : IO.Ref Slot ← IO.mkRef .open
  -- Resolved when an attempt has put its socket in `slot`.
  let signal : IO.Promise Unit ← IO.Promise.new
  let signalled : Task (Option Woken) := signal.result?.map (sync := true) (·.map fun _ => .won)
  -- An attempt that connects after another has won, or after the round, finds the slot taken or
  -- closed; its socket is then referenced by nothing and is closed when dropped.
  let run (i : Nat) (addr : SocketAddress) (timeoutMs : Nat) : Async (Except AttemptOutcome Unit) := do
    match ← attempt addr timeoutMs config.noDelay with
    | .error outcome => return .error outcome
    | .ok socket =>
      let won ← slot.modifyGet fun
        | .open => (true, .won i socket)
        | taken => (false, taken)
      if won then signal.resolve ()
      return .ok ()
  let mut started : Array (AsyncTask (Except AttemptOutcome Unit)) := #[]
  let mut result : RoundResult := .deadline
  for h : i in [0:addrs.size] do
    if ← signal.isResolved then
      break
    let left ← remainingMs deadline
    if left == 0 then
      result := .deadline
      break
    let task ← start (run i addrs[i] (min config.connectTimeoutMs left))
    started := started.push task
    let isLast := i + 1 == addrs.size
    let ended : Task (Option Woken) ←
      if isLast then
        BaseIO.mapTasks (sync := true) (fun _ => pure (some Woken.allEnded))
          (started.toList.map ExceptT.run)
      else
        pure (Task.map (sync := true) (fun _ => some Woken.attemptEnded) task.run)
    let waitMs := if isLast then left else min config.connectStaggerMs left
    match ← awaitFirst #[signalled, ended] waitMs with
    | some (some .won) => break
    | some (some .allEnded) =>
      result := .failed
      break
    | some (some .attemptEnded) | some none => pure ()
    | none =>
      if (← remainingMs deadline) == 0 then
        result := .deadline
        break
      -- Otherwise the stagger passed with the attempt still pending: start the next one.
  -- Close the round.  Whatever the loop concluded, an attempt that connected wins.
  let won ← slot.modifyGet fun st => (st, .closed)
  let (final, winner) := match won with
    | .won i socket => (RoundResult.connected socket addrs[i]!, some i)
    | _ => (result, none)
  let mut attempts := #[]
  for h : i in [0:started.size] do
    if winner == some i then
      continue
    let outcome ←
      if ← IO.hasFinished started[i] then
        match started[i].get with
        | .ok (.error outcome) => pure outcome
        | .ok (.ok ()) => pure .abandoned
        | .error err => pure (.failed (toString err))
      else
        pure .abandoned
    attempts := attempts.push { round := roundIndex, address := addrs[i]!, outcome }
  return (final, attempts)

/--
Resolves `target` to the socket addresses to try, in order.
-/
def resolve (target : Target) (port : UInt16) (deadline : Nat) :
    Async (Except ConnectError (Array SocketAddress)) := do
  match target with
  | .literal addr => return .ok #[Address.withPort addr port]
  | .name host =>
    -- Only the deadline bounds the lookup: v4.34.1 cannot cancel one, and an abandoned lookup
    -- occupies a thread of libuv's pool, and delays the process's exit, until the resolver gives
    -- up by its own timeouts.  So the client leaves those timeouts to decide.
    let lookup ← start (DNS.getAddrInfo host (toString port))
    match ← awaitWithin lookup (← remainingMs deadline) with
    | none => return .error (.deadline #[] 0)
    | some (.error err) => return .error (.resolve host (toString err))
    | some (.ok answers) =>
      let addrs := Address.connectOrder answers
      if addrs.isEmpty then
        return .error (.resolve host "no addresses")
      return .ok (addrs.map (Address.withPort · port))

/--
Connects to `target`: resolves it, then runs rounds of attempts with jittered backoff between them,
within `deadline` (a value of `IO.monoMsNow`).  `seed` drives the backoff jitter.
-/
def run (config : Config) (target : Target) (port : UInt16) (seed : UInt64) (deadline : Nat) :
    Async (Except ConnectError Connected) := do
  let addrs ← match ← resolve target port deadline with
    | .error err => return .error err
    | .ok addrs => pure addrs
  let mut attempts : Array ConnectAttempt := #[]
  for roundIndex in [0:config.maxConnectRetries + 1] do
    if roundIndex > 0 then
      let delay := Backoff.delayMs config.backoffBaseMs config.backoffCapMs seed (roundIndex - 1)
      if delay ≥ (← remainingMs deadline) then
        -- No time for another round: report the failures rather than wait for the deadline.
        return .error (.exhausted attempts roundIndex)
      if delay > 0 then
        Std.Async.sleep (.ofNat delay)
    let (result, roundAttempts) ← round config roundIndex addrs deadline
    attempts := attempts ++ roundAttempts
    match result with
    | .connected socket address =>
      return .ok { socket, address, attempts, rounds := roundIndex + 1 }
    | .deadline => return .error (.deadline attempts (roundIndex + 1))
    | .failed => pure ()
  return .error (.exhausted attempts (config.maxConnectRetries + 1))

end Connect

end LeanHttp

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

Name resolution, then rounds of connect attempts, with backoff between rounds.

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
  let connecting : AsyncTask Unit ← async (socket.connect addr)
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
One round of attempts over `addrs`, in order, staggered.  Returns the round's result and the record
of every attempt started, except the one that won.
-/
def round (config : Config) (roundIndex : Nat) (addrs : Array SocketAddress) (deadline : Nat) :
    Async (RoundResult × Array ConnectAttempt) := do
  -- Resolved by the first attempt to connect.  `resolve` ignores later winners, and their sockets,
  -- referenced by nothing else, are closed when dropped.
  let first : IO.Promise (Option (Nat × TCP.Socket.Client)) ← IO.Promise.new
  let firstTask : Task (Option Woken) := first.result?.map (sync := true) (·.map fun _ => .won)
  let mut started : Array (AsyncTask (Except AttemptOutcome TCP.Socket.Client)) := #[]
  let mut result : RoundResult := .deadline
  for h : i in [0:addrs.size] do
    if ← first.isResolved then
      break
    let left ← remainingMs deadline
    if left == 0 then
      result := .deadline
      break
    let task : AsyncTask (Except AttemptOutcome TCP.Socket.Client) ←
      async (attempt addrs[i] (min config.connectTimeoutMs left) config.noDelay)
    BaseIO.chainTask (sync := true) task fun (r : Except IO.Error (Except AttemptOutcome _)) =>
      match r with
      | .ok (.ok socket) => first.resolve (some (i, socket))
      | _ => pure ()
    started := started.push task
    let isLast := i + 1 == addrs.size
    let ended : Task (Option Woken) ←
      if isLast then
        BaseIO.mapTasks (sync := true) (fun _ => pure (some Woken.allEnded))
          (started.toList.map ExceptT.run)
      else
        pure (Task.map (sync := true) (fun _ => some Woken.attemptEnded) task.run)
    let waitMs := if isLast then left else min config.connectStaggerMs left
    match ← awaitFirst #[firstTask, ended] waitMs with
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
  -- Whatever the loop concluded, an attempt that connected wins.
  let won ← do
    if ← first.isResolved then pure first.result?.get.join else pure none
  let final := match won with
    | some (i, socket) => RoundResult.connected socket addrs[i]!
    | none => result
  let mut attempts := #[]
  for h : i in [0:started.size] do
    if won.map (·.1) == some i then
      continue
    let outcome ←
      if ← IO.hasFinished started[i] then
        match started[i].get with
        | .ok (.error outcome) => pure outcome
        | .ok (.ok _) => pure .abandoned
        | .error err => pure (.failed (toString err))
      else
        pure .abandoned
    attempts := attempts.push { round := roundIndex, address := addrs[i]!, outcome }
  return (final, attempts)

/--
Resolves `target` to the socket addresses to try, in order.
-/
def resolve (config : Config) (target : Target) (port : UInt16) (deadline : Nat) :
    Async (Except ConnectError (Array SocketAddress)) := do
  match target with
  | .literal addr => return .ok #[Address.withPort addr port]
  | .name host =>
    let left ← remainingMs deadline
    let lookup : AsyncTask (Array IPAddr) ← async (DNS.getAddrInfo host (toString port))
    match ← awaitWithin lookup (min config.connectTimeoutMs left) with
    | none =>
      if (← remainingMs deadline) == 0 then
        return .error (.deadline #[] 0)
      return .error (.resolve host "timed out")
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
  let addrs ← match ← resolve config target port deadline with
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

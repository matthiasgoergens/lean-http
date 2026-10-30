module

public section

/-!
# The pool core

Which connections exist per origin, which are idle and which are checked out, as pure data: no
timers, no I/O, no sockets.  Connections are opaque numbers (`ConnId`) that the pool allocates; the
shell keeps the socket of each idle connection next to the pool and the socket of each checked-out
connection in the call using it, and does what the pool's results say: open a connection, reuse
one, close the ones the pool let go.  Every operation is a quick pure step, so one mutex can guard
the pool without holding up any call for longer than that step.

A connection is in exactly one of three states (`ConnState`): idle in the pool, checked out by a
call, or gone (closed, never to be handed out again).  Ids the pool has not allocated yet are
unused.

- `take` hands out an idle connection of the origin, the most recently returned one first, or
  allocates a new id for the shell to connect.  With `PoolConfig.maxActive` set it refuses while the
  origin has that many connections checked out, and the shell waits for one to come back.
- `giveBack` takes a checked-out connection back with the exchange core's reuse verdict: a reusable
  one goes idle, unless the origin's idle connections are at `PoolConfig.maxIdle` or the pool is
  closed; anything else is gone.  Giving back a connection that is not checked out changes nothing
  (but for letting the expired idle connections go) and says so.
- `drop` lets a checked-out connection go: its exchange failed, or it failed the idle check.
- `sweep` lets go of the idle connections that expired (`PoolConfig.idleTimeoutMs`).
- `closeAll` lets go of every idle connection and closes the pool: from then on nothing is handed
  out and everything given back is gone.

Time is an argument: an idle connection expires once `idleTimeoutMs` have passed since it was given
back, as judged by the `now` passed to `take`, `giveBack` or `sweep`, each of which first lets go of
the expired ones.  Nothing happens between operations.

`LeanHttp.Pool.Proofs` proves the invariant over every sequence of operations and the properties
the shell relies on.
-/

namespace LeanHttp

set_option linter.all true

/--
A connection, as the pool knows it: a number the pool allocated, never reused for another
connection.
-/
abbrev ConnId := Nat

/--
The limits of a pool.
-/
structure PoolConfig where
  /--
  Most idle connections kept per origin (default: 4).  A reusable connection given back while the
  origin has this many idle is closed instead.
  -/
  maxIdle : Nat := 4

  /--
  How long an idle connection is kept, in milliseconds (default: 4 s, below the keep-alive timeouts
  common servers use, 5 s and up).  It expires when this much time has passed since it was given
  back.
  -/
  idleTimeoutMs : Nat := 4 * 1000

  /--
  Most connections checked out at once per origin, or `none` (the default) for no limit.
  -/
  maxActive : Option Nat := none
deriving Repr, Inhabited

/--
An idle connection.
-/
structure IdleConn (κ : Type) where
  /--
  The connection.
  -/
  id : ConnId

  /--
  Its origin.
  -/
  origin : κ

  /--
  When it was given back.
  -/
  since : Nat
deriving Repr, Inhabited

/--
The pool: idle and checked-out connections per origin.  Origins are of any type with decidable
equality; the shell uses `scheme://host:port`.
-/
structure Pool (κ : Type) where
  /--
  The limits.
  -/
  config : PoolConfig := {}

  /--
  The idle connections, most recently given back first.
  -/
  idle : List (IdleConn κ) := []

  /--
  The checked-out connections, with their origins.
  -/
  out : List (ConnId × κ) := []

  /--
  The next id to allocate.  Every id below it has been allocated.
  -/
  next : ConnId := 0

  /--
  Whether `closeAll` has closed the pool.
  -/
  closed : Bool := false
deriving Repr, Inhabited

/--
Where a connection stands.
-/
inductive ConnState where
  /--
  Idle in the pool.
  -/
  | idle

  /--
  Checked out by a call.
  -/
  | out

  /--
  Let go: closed, never to be handed out again.
  -/
  | gone

  /--
  Not allocated yet.
  -/
  | unused
deriving Repr, DecidableEq, Inhabited

/--
What `take` decided.
-/
inductive Taken where
  /--
  Use this idle connection, now checked out.  The shell checks it before use and drops it if it
  fails the check.
  -/
  | reuse (id : ConnId)

  /--
  Open a new connection under this id, now checked out.  The shell drops it if the connect fails.
  -/
  | fresh (id : ConnId)

  /--
  The origin has `PoolConfig.maxActive` connections checked out: wait for one to come back.
  -/
  | atCap

  /--
  The pool is closed.
  -/
  | closed
deriving Repr, DecidableEq, Inhabited

/--
What `giveBack` did with the connection.
-/
inductive Returned where
  /--
  It is idle in the pool: the shell keeps its socket for the next call.
  -/
  | idle

  /--
  It is gone: the shell closes it.
  -/
  | dropped

  /--
  It was not checked out, so nothing changed but for letting the expired idle connections go.
  -/
  | notOut
deriving Repr, DecidableEq, Inhabited

/--
An operation on the pool, for stating properties of sequences of them.
-/
inductive PoolOp (κ : Type) where
  /--
  `Pool.take`.
  -/
  | take (origin : κ) (now : Nat) (reuse : Bool)

  /--
  `Pool.giveBack`.
  -/
  | giveBack (id : ConnId) (reusable : Bool) (now : Nat)

  /--
  `Pool.drop`.
  -/
  | drop (id : ConnId)

  /--
  `Pool.sweep`.
  -/
  | sweep (now : Nat)

  /--
  `Pool.closeAll`.
  -/
  | closeAll
deriving Repr, Inhabited

namespace Pool

variable {κ : Type} [DecidableEq κ]

/--
An empty pool with the given limits.
-/
def empty (config : PoolConfig := {}) : Pool κ :=
  { config }

/--
The ids of the idle connections.
-/
def idleIds (p : Pool κ) : List ConnId :=
  p.idle.map (·.id)

/--
The ids of the checked-out connections.
-/
def outIds (p : Pool κ) : List ConnId :=
  p.out.map (·.1)

/--
Where connection `id` stands.
-/
def state (p : Pool κ) (id : ConnId) : ConnState :=
  if id ∈ p.idleIds then .idle
  else if id ∈ p.outIds then .out
  else if id < p.next then .gone
  else .unused

/--
How many connections of `origin` are idle.
-/
def idleCount (p : Pool κ) (origin : κ) : Nat :=
  (p.idle.filter (·.origin = origin)).length

/--
How many connections of `origin` are checked out.
-/
def activeCount (p : Pool κ) (origin : κ) : Nat :=
  (p.out.filter (·.2 = origin)).length

/--
Whether idle connection `c` has expired at `now`.
-/
def expired (p : Pool κ) (now : Nat) (c : IdleConn κ) : Bool :=
  c.since + p.config.idleTimeoutMs ≤ now

/--
Whether `origin` has as many connections checked out as `PoolConfig.maxActive` allows.
-/
def atCap (p : Pool κ) (origin : κ) : Bool :=
  match p.config.maxActive with
  | some m => m ≤ p.activeCount origin
  | none => false

/--
Lets go of the idle connections that expired at `now`.  Returns the pool and the connections let
go, for the shell to close.
-/
def sweep (p : Pool κ) (now : Nat) : Pool κ × List ConnId :=
  ({ p with idle := p.idle.filter (!p.expired now ·) },
    (p.idle.filter (p.expired now ·)).map (·.id))

/--
`take` once the expired idle connections are gone: the most recently given back idle connection of
`origin` if `reuse` holds and there is one, or else a new id to connect under, unless the pool is
closed or the origin has `maxActive` connections checked out.
-/
def checkout (p : Pool κ) (origin : κ) (reuse : Bool) : Pool κ × Taken :=
  if p.closed then (p, .closed)
  else if p.atCap origin then (p, .atCap)
  else
    match (if reuse then p.idle.find? (·.origin = origin) else none) with
    | some c =>
      ({ p with idle := p.idle.filter (·.id ≠ c.id), out := (c.id, origin) :: p.out }, .reuse c.id)
    | none => ({ p with out := (p.next, origin) :: p.out, next := p.next + 1 }, .fresh p.next)

/--
A connection of `origin` for a call at `now`: after letting go of the expired idle connections, the
most recently given back idle connection of the origin if `reuse` holds and there is one, or else a
new id to connect under.  Refuses while the pool is closed, or the origin has `maxActive`
connections checked out.  Returns the pool, the decision and the connections let go, for the shell
to close.
-/
def take (p : Pool κ) (origin : κ) (now : Nat) (reuse : Bool := true) :
    Pool κ × Taken × List ConnId :=
  let r := (p.sweep now).1.checkout origin reuse
  (r.1, r.2, (p.sweep now).2)

/--
`giveBack` once the expired idle connections are gone.
-/
def checkin (p : Pool κ) (id : ConnId) (reusable : Bool) (now : Nat) : Pool κ × Returned :=
  match p.out.find? (·.1 = id) with
  | none => (p, .notOut)
  | some (_, origin) =>
    if reusable && !p.closed && p.idleCount origin < p.config.maxIdle then
      ({ p with out := p.out.filter (·.1 ≠ id), idle := { id, origin, since := now } :: p.idle },
        .idle)
    else
      ({ p with out := p.out.filter (·.1 ≠ id) }, .dropped)

/--
Takes back checked-out connection `id` at `now`, with its exchange's reuse verdict, after letting go
of the expired idle connections.  A reusable connection goes idle unless the pool is closed or its
origin has `maxIdle` idle connections; anything else is gone.  A connection that is not checked out
leaves the pool unchanged but for the expired idle connections.  Returns the pool, what happened to
the connection and the connections let go, for the shell to close (not including `id`).
-/
def giveBack (p : Pool κ) (id : ConnId) (reusable : Bool) (now : Nat) :
    Pool κ × Returned × List ConnId :=
  let r := (p.sweep now).1.checkin id reusable now
  (r.1, r.2, (p.sweep now).2)

/--
Lets go of checked-out connection `id`.  Returns whether it was checked out; if it was not, nothing
changed.
-/
def drop (p : Pool κ) (id : ConnId) : Pool κ × Bool :=
  if id ∈ p.outIds then ({ p with out := p.out.filter (·.1 ≠ id) }, true) else (p, false)

/--
Lets go of every idle connection and closes the pool.  Returns the pool and the connections let
go, for the shell to close.  Connections checked out stay so, and are gone when given back.
-/
def closeAll (p : Pool κ) : Pool κ × List ConnId :=
  ({ p with idle := [], closed := true }, p.idleIds)

/--
The connection a decision of `take` hands out, if any.
-/
def handed : Taken → Option ConnId
  | .reuse id | .fresh id => some id
  | .atCap | .closed => none

/--
The pool after `op`.
-/
def apply (p : Pool κ) : PoolOp κ → Pool κ
  | .take origin now reuse => (p.take origin now reuse).1
  | .giveBack id reusable now => (p.giveBack id reusable now).1
  | .drop id => (p.drop id).1
  | .sweep now => (p.sweep now).1
  | .closeAll => p.closeAll.1

/--
The pool after `ops`, in order.
-/
def run (p : Pool κ) (ops : List (PoolOp κ)) : Pool κ :=
  ops.foldl apply p

end Pool

end LeanHttp

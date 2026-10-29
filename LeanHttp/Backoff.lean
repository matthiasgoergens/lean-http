module

public section

/-!
# Backoff

The delay before each retry of a failed connect: exponential backoff with full jitter, a uniform draw
from `[0, min cap (base * 2 ^ attempt)]` milliseconds.  The draw is a pure function of a seed and the
attempt number, so a call's schedule can be replayed from the seed recorded in its result or error.
-/

namespace LeanHttp.Backoff

set_option linter.all true

/--
The SplitMix64 output function: a bijection on 64-bit words that spreads every input bit over the
whole output.
-/
def mix64 (z : UInt64) : UInt64 :=
  let z := (z ^^^ (z >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb
  z ^^^ (z >>> 31)

/--
The pseudo-random word for retry number `attempt` (counting from 0) under `seed`: the `attempt`-th
output of a SplitMix64 generator started at `seed`.
-/
def draw (seed : UInt64) (attempt : Nat) : UInt64 :=
  mix64 (seed + (attempt.toUInt64 + 1) * 0x9e3779b97f4a7c15)

/--
The largest delay allowed before retry number `attempt`: `min capMs (baseMs * 2 ^ attempt)`.
-/
def ceiling (baseMs capMs attempt : Nat) : Nat :=
  -- Past 64 doublings any positive base exceeds every cap a `UInt64` clock could express.
  if attempt ≥ 64 then (if baseMs = 0 then 0 else capMs) else min capMs (baseMs * 2 ^ attempt)

/--
The delay in milliseconds before retry number `attempt` (counting from 0): a draw from
`[0, ceiling baseMs capMs attempt]`, determined by `seed` and `attempt` alone.
-/
def delayMs (baseMs capMs : Nat) (seed : UInt64) (attempt : Nat) : Nat :=
  (draw seed attempt).toNat % (ceiling baseMs capMs attempt + 1)

/--
The ceiling never exceeds the cap.
-/
theorem ceiling_le_cap (baseMs capMs attempt : Nat) : ceiling baseMs capMs attempt ≤ capMs := by
  unfold ceiling
  split
  · split <;> omega
  · exact Nat.min_le_left _ _

/--
A delay never exceeds the ceiling.
-/
theorem delayMs_le_ceiling (baseMs capMs : Nat) (seed : UInt64) (attempt : Nat) :
    delayMs baseMs capMs seed attempt ≤ ceiling baseMs capMs attempt := by
  unfold delayMs
  generalize (draw seed attempt).toNat = x
  generalize ceiling baseMs capMs attempt = c
  have := Nat.mod_lt x (show 0 < c + 1 by omega)
  omega

/--
A delay never exceeds the cap.
-/
theorem delayMs_le_cap (baseMs capMs : Nat) (seed : UInt64) (attempt : Nat) :
    delayMs baseMs capMs seed attempt ≤ capMs :=
  Nat.le_trans (delayMs_le_ceiling baseMs capMs seed attempt) (ceiling_le_cap baseMs capMs attempt)

/--
The delays before the first `n` retries.
-/
def schedule (baseMs capMs : Nat) (seed : UInt64) (n : Nat) : List Nat :=
  (List.range n).map (delayMs baseMs capMs seed)

end LeanHttp.Backoff

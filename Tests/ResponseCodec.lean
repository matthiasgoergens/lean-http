import Tests.Support.CodecDrive

/-!
# Response codec tests

Runs the response codec (`LeanHttp.Codec`) over the response shapes of `Tests/Codec.lean`, each fed
whole, one byte at a time, and split in two at every position, and checks that the outcome is the
one expected of the exchange core with the vendored machine.  The informational cases, whose outcome
the exchange core's test only records, must come out as the vendored machine has them (rejected as
bad messages).

Also checks that the codec's byte classes agree with `Std.Http`'s character classes on every byte.

Prints one line per case, then a summary; exits with status 1 if anything failed.
-/

open Std.Http LeanHttp

/-- What the informational cases come to with the vendored machine (`logs/2026-10-27/codec-vendored`). -/
def informational : List (String × String) := [
  ("status line without reason phrase or space", "failed LeanHttp.Cause.protocol \"Bad message\""),
  ("bare LF line endings", "failed LeanHttp.Cause.protocol \"Bad message\""),
  ("obsolete line folding", "failed LeanHttp.Cause.protocol \"Bad message\"")
]

/-- Runs one case in every split mode; returns the number of failing modes. -/
def runCase (c : Shape) : IO Nat := do
  let bytes := c.response.toUTF8
  let modes := splits bytes (bytes.size ≤ 2000)
  let cfg := codecConfig c.limits
  let results := modes.map fun (label, pieces) =>
    (label, renderCodec (codecRun cfg c.method pieces c.eof))
  let expected := c.expect.orElse fun _ => (informational.lookup c.name)
  match expected with
  | some expected =>
    let bad := results.filter (·.2 != expected)
    if bad.isEmpty then
      IO.println s!"PASS {c.name}: {expected} ({modes.length} modes)"
    else
      IO.println s!"FAIL {c.name}: expected {expected}"
      let outcomes := bad.map (·.2) |>.eraseDups
      for o in outcomes do
        let labels := bad.filter (·.2 == o) |>.map (·.1)
        let shown := String.intercalate " " (labels.take 12)
        let more := if labels.length > 12 then s!" (+{labels.length - 12} more)" else ""
        IO.println s!"     got {o} in {labels.length}/{modes.length} modes: {shown}{more}"
    return bad.length
  | none =>
    IO.println s!"FAIL {c.name}: no expected outcome"
    return 1

/-- The byte classes against `Std.Http.Internal.Char`, on all 256 bytes; returns the mismatches. -/
def checkClasses : List String := Id.run do
  let mut bad := []
  for i in [0:256] do
    let b := i.toUInt8
    let c := Char.ofUInt8 b
    if Codec.isTChar b != Std.Http.Internal.Char.tchar c then bad := s!"tchar {i}" :: bad
    if Codec.isFieldContent b != Std.Http.Internal.Char.fieldContent c then
      bad := s!"field-content {i}" :: bad
    if Codec.isFieldContent b != Std.Http.Internal.Char.reasonPhraseChar c then
      bad := s!"reason-phrase {i}" :: bad
    if Codec.isQdText b != Std.Http.Internal.Char.qdtext c then bad := s!"qdtext {i}" :: bad
    if Codec.isQuotedPairChar b != Std.Http.Internal.Char.quotedPairChar c then
      bad := s!"quoted-pair {i}" :: bad
    if Codec.isWs b != Std.Http.Internal.Char.ows c then bad := s!"ows {i}" :: bad
    if (Codec.hexVal? b).isSome != Std.Http.Internal.Char.isHexDigitByte b then
      bad := s!"hexdig {i}" :: bad
  return bad.reverse

def main : IO UInt32 := do
  let classes := checkClasses
  if classes.isEmpty then IO.println "PASS byte classes agree with Std.Http on all 256 bytes"
  else IO.println s!"FAIL byte classes: {classes}"
  let mut failing := if classes.isEmpty then 0 else 1
  for c in cases do
    if (← runCase c) > 0 then
      failing := failing + 1
  IO.println s!"{cases.length} cases, {failing} failing"
  return if failing == 0 then 0 else 1

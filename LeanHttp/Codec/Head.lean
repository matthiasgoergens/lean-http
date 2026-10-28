module

public import LeanHttp.Codec.Lines
public import LeanHttp.Codec.Fields

@[expose] public section

/-!
# Reading response heads

Reads the status line and header section of each response, one byte at a time, skips interim
(1xx) responses up to `Config.maxInterim`, refuses `101 Switching Protocols`, and reports the final
head with its framing.
-/

namespace LeanHttp.Codec

set_option linter.all true

/--
Which part of a head is being read.
-/
inductive HeadPart where
  /-- The status line. -/
  | status (sl : StatusLine)
  /--
  The header section, after the status line `sl`: the current line, the fields so far (in reverse),
  how many, and how many bytes they took.
  -/
  | fields (sl : StatusLine) (fl : FieldLine) (fields : List Field) (count bytes : Nat)
deriving Repr, Inhabited, DecidableEq

/--
The state of the head reader: the current head, and what the interim responses so far left behind.
-/
structure HeadState where
  /-- Which part of the current head is being read. -/
  part : HeadPart := .status {}
  /-- Interim responses so far. -/
  interim : Nat := 0
  /-- Whether every head so far allowed the connection to stay open. -/
  keepAlive : Bool := true
deriving Repr, Inhabited, DecidableEq

/--
What one byte of a head leads to.
-/
inductive HeadResult where
  /-- The head reader goes on (also after an interim response). -/
  | more (hs : HeadState)
  /-- The final head ended with this byte. -/
  | final (h : Head)
  /-- The response is rejected. -/
  | fail (e : Error)
deriving Inhabited

/--
Ends a head, at its empty line: rejects invalid framing fields, skips an interim response, refuses
`101`, or reports the final head.
-/
def endOfHead (cfg : Config) (isHead : Bool) (hs : HeadState) (sl : StatusLine)
    (fields : List Field) : HeadResult :=
  let http10 := sl.minor == 0
  let keepAlive := hs.keepAlive && keepAliveOf http10 fields
  match framingOf isHead sl.code http10 fields with
  | none => .fail .badMessage
  | some framing =>
    if 100 ≤ sl.code && sl.code < 200 then
      if sl.code == 101 then .fail .switchingProtocols
      else if cfg.maxInterim ≤ hs.interim then .fail .tooManyInterim
      else .more { part := .status {}, interim := hs.interim + 1, keepAlive }
    else
      let reason := sl.reason.reverse
      match toResponseHead? sl.code http10 reason fields with
      | none => .fail .badMessage
      | some response =>
        .final { code := sl.code, http10, reason, fields, framing, keepAlive, interim := hs.interim,
                 response }

/--
Reads one byte of a response head.  `isHead` says whether the request was HEAD.
-/
def stepHead (cfg : Config) (isHead : Bool) (hs : HeadState) (b : UInt8) : HeadResult :=
  match hs.part with
  | .status sl =>
    match stepStatusLine cfg sl b with
    | .more sl => .more { hs with part := .status sl }
    | .bad => .fail .badMessage
    | .done sl =>
      -- The status code is checked before the version, as the vendored machine does.
      if sl.code < 100 then .fail .badMessage
      else if sl.major == 1 && (sl.minor == 0 || sl.minor == 1) then
        .more { hs with part := .fields sl {} [] 0 0 }
      else .fail .unsupportedVersion
  | .fields sl fl fields count bytes =>
    match stepFieldLine cfg fl b with
    | .more fl => .more { hs with part := .fields sl fl fields count bytes }
    | .bad => .fail .badMessage
    | .field name value n =>
      if cfg.maxHeaders ≤ count then .fail .tooManyHeaders
      else if cfg.maxHeaderBytes < bytes + n then .fail .headersTooLarge
      else .more { hs with part := .fields sl {} ({ name, value } :: fields) (count + 1) (bytes + n) }
    | .blank => endOfHead cfg isHead hs sl fields.reverse

end LeanHttp.Codec

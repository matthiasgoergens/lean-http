import LeanHttp.Codec
import LeanHttp.Error
import Tests.Support.CodecCases

/-!
# Driving the response codec in tests

Runs `LeanHttp.Codec.Parser` over pieces of a response and renders the outcome in the same words as
`Tests/Codec.lean` renders the exchange core's, so that the two can be compared.
-/

open Std.Http LeanHttp

/-- The codec's limits for a test case's limits. -/
def codecConfig (l : Limits) : Codec.Config :=
  { maxHeaders := l.h1.maxHeaders, maxHeaderBytes := l.h1.maxHeaderBytes,
    maxHeaderNameLength := l.h1.maxHeaderNameLength,
    maxHeaderValueLength := l.h1.maxHeaderValueLength, maxSpaceSequence := l.h1.maxSpaceSequence,
    maxReasonPhraseLength := l.h1.maxReasonPhraseLength,
    maxChunkExtensions := l.h1.maxChunkExtensions,
    maxChunkExtNameLength := l.h1.maxChunkExtNameLength,
    maxChunkExtValueLength := l.h1.maxChunkExtValueLength,
    maxChunkLineLength := l.h1.maxChunkLineLength, maxTrailerHeaders := l.h1.maxTrailerHeaders,
    maxInterim := l.maxInterim, maxBody := l.maxBody }

/-- The exchange core's cause for a codec error, as the core would report it. -/
def codecCause : Codec.Error → Cause
  | .badMessage => .protocol "Bad message"
  | .unsupportedVersion => .protocol "Unsupported version"
  | .tooManyHeaders | .headersTooLarge => .limit .headers
  | .bodyTooLarge => .limit .body
  | .tooManyInterim => .limit .interim
  | .switchingProtocols => .protocol "101 Switching Protocols, but no upgrade was requested"
  | .unsupportedCoding => .protocol "a transfer coding other than chunked, which the client cannot decode"
  | .closed => .peerClosed

/-- A codec run: the parser and every event so far. -/
structure CodecRun where
  /-- The parser. -/
  p : Codec.Parser
  /-- Every event, in order. -/
  events : Array Codec.Event := #[]

/-- Feeds `pieces` in order to a parser for `method`, then end of input if `eof`. -/
def codecRun (cfg : Codec.Config) (method : Method) (pieces : List ByteArray) (eof : Bool) :
    CodecRun :=
  let r := pieces.foldl (init := { p := Codec.Parser.start cfg method : CodecRun }) fun r piece =>
    let (p, es) := r.p.feed piece
    { p, events := r.events ++ es }
  if eof then
    let (p, es) := r.p.finish
    { p, events := r.events ++ es }
  else r

/-- The body bytes of a run, joined once. -/
def CodecRun.body (r : CodecRun) : ByteArray :=
  let parts := r.events.filterMap fun | .body b => some b | _ => none
  let total := parts.foldl (· + ·.size) 0
  parts.foldl (· ++ ·) (ByteArray.emptyWithCapacity total)

/-- The final head of a run, if one arrived. -/
def CodecRun.head? (r : CodecRun) : Option Codec.Head :=
  r.events.findSome? fun | .head h => some h | _ => none

/-- The outcome of a run, in the words of `Tests/Codec.lean`. -/
def renderCodec (r : CodecRun) : String :=
  let err := r.events.findSome? fun | .error e => some e | _ => none
  let done := r.events.any fun | .done => true | _ => false
  match err, done, r.head? with
  | some e, _, _ => s!"failed {repr (codecCause e)}"
  | none, true, some h =>
    let body := r.body
    let text := String.fromUTF8? body |>.getD s!"<{body.size} bytes>"
    s!"done {h.code} interim={h.interim} body={repr text}"
  | _, _, _ => "pending"

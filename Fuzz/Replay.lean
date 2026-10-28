import Fuzz.Harness

/-!
# Replaying fuzz inputs

Runs the fuzzing harness's check over the files named on the command line and prints, for each,
the decoded input, what both drivers did and the verdict.  Exits with status 1 if any input breaks
an invariant.  Used to triage AFL++ findings and to check the seeds without AFL++.

With `--brief`, prints one line per file.  With `--class`, prints for each file only the class of
the broken invariant (the first 120 characters of the failure's first line, digits replaced by
`N`), or `ok`; `fuzz/triage.sh` groups crashes by it.  With `--framing`, prints one JSON line
per file with the framing decisions, for `fuzz/h11-diff.py`.
-/

open LeanHttpFuzz

/-- A printable rendering of response bytes. -/
def showBytes (b : ByteArray) : String :=
  match String.fromUTF8? b with
  | some s => repr s |>.pretty
  | none => s!"<{b.size} bytes, not UTF-8> {repr b.data}"

/-- Prints what one input did. -/
def describe (rep : Report) : IO Unit := do
  let i := rep.input
  IO.println s!"  method={repr i.method} eof={i.eof} bytewise={i.bytewise} reads={rep.reads.map (·.size)}"
  IO.println s!"  response={showBytes i.response}"
  IO.println s!"  exchange/whole: {renderExchange rep.exWhole}"
  IO.println s!"  exchange/split: {renderExchange rep.exSplit}"
  IO.println s!"  machine/whole:  {renderRun rep.runWhole}"
  IO.println s!"  machine/split:  {renderRun rep.runSplit}"
  IO.println s!"  machine/flipped end of input: {renderRun rep.runFlipped}"

/-- The class of a failure message: the start of its first line, with digits replaced by `N`. -/
def failureClass (msg : String) : String :=
  let first := (msg.splitOn "\n").headD ""
  String.ofList ((first.toList.map fun c => if c.isDigit then 'N' else c).take 120)

/-- Lowercase hexadecimal of a byte string. -/
def hex (b : ByteArray) : String :=
  let digit (n : Nat) : Char := "0123456789abcdef".toList[n]!
  String.ofList (b.data.toList.flatMap fun x => [digit (x.toNat / 16), digit (x.toNat % 16)])

/--
One JSON line with the framing decisions of the direct driver (keep-alive on) over the whole
response, for the differential check against h11 (`fuzz/h11-diff.py`).
-/
def framingJson (file : String) (rep : Report) : String :=
  let r := rep.runWhole
  let failed := r.trace.any (· matches .failed _)
  -- Input that ends before the response completes is a failure, as the exchange core reports it,
  -- even where the machine only closes (end of input before any byte).
  let outcome :=
    if r.trace.contains .endBody then "done" else if failed || r.eof then "failed" else "pending"
  let status := match r.finalHead with
    | some h => toString h.status.toCode
    | none => "null"
  let leftover := if reusable r then toString r.machine.reader.input.remainingBytes else "null"
  s!"\{\"file\": {repr file}, \"outcome\": \"{outcome}\", \"status\": {status}, " ++
    s!"\"interim\": {r.interim}, \"body\": \"{hex r.body}\", \"reuse\": {reusable r}, " ++
    s!"\"leftover\": {leftover}}"

/-- What the tool prints. -/
inductive Mode where
  /-- Everything about each input. -/
  | full
  /-- One line per input. -/
  | brief
  /-- The class of the broken invariant, per input. -/
  | classOnly
  /-- JSON framing decisions, per input. -/
  | framing

def main (args : List String) : IO UInt32 := do
  let (modes, files) := args.partition (·.startsWith "--")
  let mode ← match modes with
    | [] => pure Mode.full
    | ["--brief"] => pure .brief
    | ["--class"] => pure .classOnly
    | ["--framing"] => pure .framing
    | _ => throw (IO.userError s!"usage: fuzz-replay [--brief | --class | --framing] <file>...")
  let mut bad := 0
  for f in files do
    let data ← IO.FS.readBinFile f
    let result := check data
    if result matches .error _ then bad := bad + 1
    match mode, result with
    | .classOnly, .ok _ => IO.println "ok"
    | .classOnly, .error msg => IO.println (failureClass msg)
    | .framing, _ => IO.println (framingJson f (run data))
    | .brief, .ok rep => IO.println s!"OK   {f}: {renderRun rep.runWhole}"
    | .full, .ok rep =>
      IO.println s!"OK   {f}"
      describe rep
    | .brief, .error msg => IO.println s!"FAIL {f}: {msg}"
    | .full, .error msg =>
      IO.println s!"FAIL {f}: {msg}"
      describe (run data)
  if mode matches .full | .brief then IO.println s!"{files.length} inputs, {bad} failing"
  return if bad == 0 then 0 else 1

#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.12"
# dependencies = ["h11==0.16.0"]
# ///
"""Compares the machine's framing decisions with h11's over fuzz inputs.

Reads the JSON lines that `fuzz-replay --framing` prints (the direct driver of the machine, keep-alive
on, response fed whole), feeds the same request and response bytes to an h11 client connection, and
classifies each input:

- agree: both complete with the same final status, body and reuse decision (and the same bytes
  left over when both would reuse), or neither completes;
- we-accept-it-rejects: the machine completes the response, h11 raises a protocol error (a finding);
- framed-differently: both complete, but status, body, reuse decision or leftover differ (a finding);
- it-accepts-we-reject: h11 completes, the machine fails (an expected strictness difference, listed
  for review rather than reported);
- we-reject-it-waits: the machine fails, h11 still waits for input (h11 parses a head only once it
  has all of it, so it has not decided yet);
- other: any other combination (one pending, the other failed or complete), listed for review.

Differences explained by a rule in ALLOWED are marked with the rule's name and not counted as
findings.  Prints the counts and writes every input that is not `agree` to the output file, one JSON
line each.
The input files are read relative to the current directory, as `fuzz-replay` named them.

Usage: fuzz/h11-diff.py <framing.jsonl> <output.jsonl>
"""

import argparse
import json
import re
from collections import Counter
from collections.abc import Callable
from dataclasses import asdict, dataclass
from enum import Enum, StrEnum
from pathlib import Path

import h11

MAX_RESPONSE = 2432  # Fuzz/Harness.lean, maxResponse


class Method(Enum):
    GET = 0
    HEAD = 1
    POST = 2
    OPTIONS = 3


@dataclass
class Input:
    method: Method
    eof: bool
    response: bytes


def decode(data: bytes) -> Input:
    """The harness's input format (Fuzz/Harness.lean, decode)."""
    if not data:
        return Input(Method.GET, True, b"")
    ctrl = data[0]
    k = min(ctrl // 16, len(data) - 1)
    return Input(Method(ctrl % 4), (ctrl // 4) % 2 == 1, data[k + 1 : k + 1 + MAX_RESPONSE])


class Outcome(StrEnum):
    DONE = "done"
    FAILED = "failed"
    PENDING = "pending"


@dataclass
class Result:
    outcome: Outcome
    status: int | None
    interim: int
    body: str
    reuse: bool
    leftover: int | None
    error: str | None = None


def run_h11(inp: Input) -> Result:
    conn = h11.Connection(our_role=h11.CLIENT, max_incomplete_event_size=1 << 20)
    headers = [("Host", "example.test")]
    if inp.method is Method.POST:
        headers.append(("Content-Length", "0"))
    conn.send(h11.Request(method=inp.method.name, target="/", headers=headers))
    conn.send(h11.EndOfMessage())
    status: int | None = None
    interim = 0
    body = bytearray()
    done = False
    try:
        if inp.response:  # receive_data(b"") means end of input to h11
            conn.receive_data(inp.response)
        if inp.eof:
            conn.receive_data(b"")
        while True:
            event = conn.next_event()
            if event is h11.NEED_DATA or event is h11.PAUSED:
                break
            match event:
                case h11.InformationalResponse():
                    interim += 1
                case h11.Response(status_code=code):
                    status = code
                case h11.Data(data=data):
                    body += data
                case h11.EndOfMessage():
                    done = True
                case h11.ConnectionClosed():
                    break
                case _:
                    raise AssertionError(f"unexpected h11 event {event!r}")
    except h11.RemoteProtocolError as e:
        return Result(Outcome.FAILED, status, interim, body.hex(), False, None, str(e))
    if not done:
        return Result(Outcome.PENDING, status, interim, body.hex(), False, None)
    # h11 keeps an end of input that arrives after the response in trailing_data, without changing
    # state; a connection whose peer closed is not reusable.
    trailing, closed = conn.trailing_data
    reuse = conn.our_state is h11.DONE and conn.their_state is h11.DONE and not closed
    leftover = len(trailing) if reuse else None
    return Result(Outcome.DONE, status, interim, body.hex(), reuse, leftover)


class Verdict(StrEnum):
    AGREE = "agree"
    WE_ACCEPT_IT_REJECTS = "we-accept-it-rejects"
    FRAMED_DIFFERENTLY = "framed-differently"
    IT_ACCEPTS_WE_REJECT = "it-accepts-we-reject"
    WE_REJECT_IT_WAITS = "we-reject-it-waits"
    OTHER = "other"


FINDINGS = {Verdict.WE_ACCEPT_IT_REJECTS, Verdict.FRAMED_DIFFERENTLY, Verdict.OTHER}


@dataclass
class Rule:
    name: str
    verdict: Verdict
    reason: str
    applies: Callable[[Input, Result, Result], bool]


def same_response(ours: Result, theirs: Result) -> bool:
    return (ours.status, ours.body) == (theirs.status, theirs.body)


TOKEN_LIST = re.compile(rb"[!#$%&'*+.^_`|~0-9A-Za-z-]+([ \t]*,[ \t]*[!#$%&'*+.^_`|~0-9A-Za-z-]+)*")
CONNECTION_LINE = re.compile(rb"\r\nconnection:[ \t]*([^\r\n]*?)[ \t]*(?=\r\n)", re.IGNORECASE)
BWS_BEFORE_EXTENSION = re.compile(rb"\r\n[0-9A-Fa-f]+[ \t]+;")


def keep_alive_breaking_interim(inp: Input) -> bool:
    """Whether some interim (1xx) head is HTTP/1.0 or has a Connection field mentioning close."""
    heads = [h for h in inp.response.split(b"\r\n\r\n") if re.match(rb"HTTP/1\.[01] 1\d\d", h)]
    return any(h.startswith(b"HTTP/1.0") or any(b"close" in v.lower() for v in
               CONNECTION_LINE.findall(h + b"\r\n")) for h in heads)


def bad_connection_value(inp: Input) -> bool:
    """Whether some Connection field value is not a list of tokens."""
    return any(not TOKEN_LIST.fullmatch(v) for v in CONNECTION_LINE.findall(inp.response))


ALLOWED = [
    Rule("unsolicited-101", Verdict.WE_ACCEPT_IT_REJECTS,
         "the machine treats a 101 nobody asked for as final; the exchange core refuses it",
         lambda inp, ours, theirs: ours.status == 101 and "_SWITCH_UPGRADE" in (theirs.error or "")),
    Rule("data-after-close", Verdict.WE_ACCEPT_IT_REJECTS,
         "h11 rejects bytes after a response it will not reuse the connection for; the machine "
         "leaves them unread, and a pool must not reuse a connection with bytes left over",
         lambda inp, ours, theirs: theirs.error == "Got data when expecting EOF"
         and not (ours.reuse and ours.leftover == 0)),
    Rule("http10-keep-alive", Verdict.FRAMED_DIFFERENTLY,
         "h11 never reuses an HTTP/1.0 connection; RFC 9112 section 9.3 allows it with keep-alive",
         lambda inp, ours, theirs: ours.reuse and not theirs.reuse and same_response(ours, theirs)
         and inp.response.startswith(b"HTTP/1.0 ")),
    Rule("malformed-connection", Verdict.FRAMED_DIFFERENTLY,
         "a Connection value that is not a list of tokens turns the machine's reuse off; h11 "
         "ignores it (the machine is the safer one)",
         lambda inp, ours, theirs: not ours.reuse and theirs.reuse and same_response(ours, theirs)
         and bad_connection_value(inp)),
    Rule("bws-before-chunk-extension", Verdict.OTHER,
         "h11 rejects whitespace between a chunk size and ';', which RFC 9112 section 7.1.1 allows "
         "(BWS); the machine accepts it",
         lambda inp, ours, theirs: ours.outcome is not Outcome.FAILED
         and theirs.outcome is Outcome.FAILED and "illegal chunk header" in (theirs.error or "")
         and BWS_BEFORE_EXTENSION.search(inp.response) is not None),
    Rule("interim-disables-reuse", Verdict.FRAMED_DIFFERENTLY,
         "the machine's keep-alive only ever turns off, so an interim response that is HTTP/1.0 "
         "or carries Connection: close stops reuse even if the final response allows it (safe, "
         "not optimal)",
         lambda inp, ours, theirs: not ours.reuse and theirs.reuse and same_response(ours, theirs)
         and ours.interim > 0 and keep_alive_breaking_interim(inp)),
]


def classify(ours: Result, theirs: Result) -> Verdict:
    match ours.outcome, theirs.outcome:
        case Outcome.DONE, Outcome.DONE:
            same = (ours.status, ours.body, ours.reuse, ours.leftover) == (
                theirs.status, theirs.body, theirs.reuse, theirs.leftover)
            return Verdict.AGREE if same else Verdict.FRAMED_DIFFERENTLY
        case Outcome.DONE, Outcome.FAILED:
            return Verdict.WE_ACCEPT_IT_REJECTS
        case Outcome.FAILED, Outcome.DONE:
            return Verdict.IT_ACCEPTS_WE_REJECT
        case Outcome.FAILED, Outcome.PENDING:
            return Verdict.WE_REJECT_IT_WAITS
        case (Outcome.FAILED, Outcome.FAILED) | (Outcome.PENDING, Outcome.PENDING):
            return Verdict.AGREE
        case Outcome.PENDING, Outcome.FAILED:
            return Verdict.OTHER
        case (Outcome.DONE, Outcome.PENDING) | (Outcome.PENDING, Outcome.DONE):
            return Verdict.OTHER
        case _:
            raise AssertionError(f"unhandled outcomes {ours.outcome}, {theirs.outcome}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("framing", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    counts: Counter[tuple[Verdict, str | None]] = Counter()
    with args.framing.open() as lines, args.output.open("w") as out:
        for line in lines:
            row = json.loads(line)
            data = Path(row["file"]).read_bytes()
            inp = decode(data)
            ours = Result(Outcome(row["outcome"]), row["status"], row["interim"], row["body"],
                          row["reuse"], row["leftover"])
            theirs = run_h11(inp)
            verdict = classify(ours, theirs)
            rule = next((r.name for r in ALLOWED
                         if r.verdict is verdict and r.applies(inp, ours, theirs)), None)
            counts[verdict, rule] += 1
            if verdict is not Verdict.AGREE:
                out.write(json.dumps({
                    "verdict": verdict, "allowed": rule, "finding": verdict in FINDINGS and not rule,
                    "file": row["file"], "method": inp.method.name,
                    "eof": inp.eof, "response": inp.response.decode("latin-1"),
                    "ours": asdict(ours), "h11": asdict(theirs)}) + "\n")
    for (verdict, rule), n in sorted(counts.items(), key=lambda kv: (kv[0][0], kv[0][1] or "")):
        tag = f" (allowed: {rule})" if rule else (" FINDING" if verdict in FINDINGS else "")
        print(f"{verdict}{tag}: {n}")
    for rule in ALLOWED:
        print(f"rule {rule.name}: {rule.reason}")


if __name__ == "__main__":
    main()

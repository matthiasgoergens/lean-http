#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.10"
# dependencies = []
# ///
"""Plants one defect in LeanHttp/Exchange.lean of the tree in the current directory.

Usage: mutate.py <name>; the names and what they break are in MUTATIONS."""
import sys
from pathlib import Path

MUTATIONS = {
    # A pull while bytes already known are still to be written: without the condition that they were
    # written.  The write scheduled first in the same step makes this one equivalent (a write is in
    # flight whenever bytes are unwritten), so the checker cannot see it; "pull-with-write" drops
    # the condition on the write in flight too.
    "pull-early": ("decide (ex.headBytes ≤ ex.written) && decide (ex.known ≤ ex.written)",
                   "decide (ex.headBytes ≤ ex.written)"),
    # A pull while a write is in flight and bytes are unwritten.
    "pull-with-write": ("!ex.uploadStopped && ex.writeInFlight.isNone && ex.sentAny &&\n    decide (ex.headBytes ≤ ex.written) && decide (ex.known ≤ ex.written)",
                        "!ex.uploadStopped && ex.sentAny &&\n    decide (ex.headBytes ≤ ex.written)"),
    # A pull before the request head is out: without the conditions on the head, on the bytes
    # written and on the write in flight (with only the first two gone, the write of the head,
    # scheduled first, is in flight whenever the head is unwritten, and nothing changes).
    "pull-before-head": ("!ex.uploadStopped && ex.writeInFlight.isNone && ex.sentAny &&\n    decide (ex.headBytes ≤ ex.written) && decide (ex.known ≤ ex.written)",
                         "!ex.uploadStopped && ex.sentAny"),
    # A declared size exceeded by one byte is accepted.
    "size-plus-one": ("if ex.taken + chunk.size ≤ size then", "if ex.taken + chunk.size ≤ size + 1 then"),
    # The end of a body short of its declared size is accepted.
    "short-end": ("if ex.taken = size then .ok { ex with complete := true }",
                  "if ex.taken ≤ size then .ok { ex with complete := true }"),
    # Chunked framing without the CRLF after the data.
    "no-crlf": ("{ ex.enqueue (Codec.chunkFrame chunk) with",
                "{ ex.enqueue (ByteArray.mk (Codec.hexDigits chunk.size ++ [Codec.cr, Codec.lf]).toArray ++ chunk) with"),
    # The request counted as complete on the wire from the start.
    "wire-done": ("def wireDone (ex : Exchange) : Bool :=\n  ex.complete ||", "def wireDone (ex : Exchange) : Bool :=\n  true ||"),
    # A refused chunk only ends the pull, and the exchange goes on.
    "ignore-broken": ("        setEx { ex with pulling := false }\n        failOrDrop cause",
                      "        setEx { ex with pulling := false }"),
    # A producer's failure only ends the pull.
    "ignore-failure": ("      setEx { ex with pulling := false }\n      failOrDrop (.requestBody s!\"the producer failed: {detail}\")",
                       "      setEx { ex with pulling := false }"),
}

name = sys.argv[1]
old, new = MUTATIONS[name]
p = Path("LeanHttp/Exchange.lean")
s = p.read_text()
if s.count(old) != 1:
    sys.exit(f"{name}: the text to change occurs {s.count(old)} times")
p.write_text(s.replace(old, new))
print(f"planted {name}")

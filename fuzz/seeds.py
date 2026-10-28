#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Writes the fuzzing seeds into a directory, in the harness's input format (Fuzz/Harness.lean).

The hand-written seeds below cover the response shapes a client meets; the samples in
fuzz/httparse/ (response heads from the httparse OSS-Fuzz corpus, minimised against this harness)
are added with a control byte for GET with end of input.

Usage: fuzz/seeds.py <output directory>
"""

import argparse
from dataclasses import dataclass, field
from enum import IntEnum
from pathlib import Path

HERE = Path(__file__).resolve().parent


class Method(IntEnum):
    GET = 0
    HEAD = 1
    POST = 2
    OPTIONS = 3


@dataclass
class Seed:
    name: str
    response: bytes
    method: Method = Method.GET
    eof: bool = False
    bytewise: bool = False
    splits: list[int] = field(default_factory=list)

    def encode(self) -> bytes:
        assert len(self.splits) < 16 and all(0 <= s < 256 for s in self.splits)
        ctrl = self.method | (self.eof << 2) | (self.bytewise << 3) | (len(self.splits) << 4)
        return bytes([ctrl, *self.splits]) + self.response


def crlf(*lines: str) -> bytes:
    return "".join(line + "\r\n" for line in lines).encode()


SEEDS = [
    Seed("content-length", crlf("HTTP/1.1 200 OK", "Content-Length: 5", "") + b"hello",
         splits=[10, 7, 0, 20]),
    Seed("content-length-26",
         crlf("HTTP/1.1 200 OK", "Content-Length: 26", "") + b"abcdefghijklmnopqrstuvwxyz",
         splits=[45, 9]),
    Seed("chunked-ext-trailers",
         crlf("HTTP/1.1 200 OK", "Transfer-Encoding: chunked", "", '5;a=1;b="x y"', "hello",
              "6", " world", "0;end", "X-Checksum: abc", "X-Other: d", ""),
         splits=[50, 4, 3, 30]),
    Seed("chunked-bytewise",
         crlf("HTTP/1.1 200 OK", "Transfer-Encoding: chunked", "", "a", "0123456789", "0", ""),
         bytewise=True),
    Seed("close-delimited", crlf("HTTP/1.1 200 OK", "Content-Type: text/plain", "") + b"abc",
         eof=True, splits=[20]),
    Seed("http10-close-delimited", crlf("HTTP/1.0 200 OK", "") + b"old", eof=True),
    Seed("http10-keep-alive",
         crlf("HTTP/1.0 200 OK", "Connection: keep-alive", "Content-Length: 2", "") + b"ok"),
    Seed("interim-then-final",
         crlf("HTTP/1.1 100 Continue", "", "HTTP/1.1 103 Early Hints", "Link: </a>", "",
              "HTTP/1.1 200 OK", "Content-Length: 2", "") + b"ok",
         splits=[25, 1, 40]),
    Seed("head-content-length", crlf("HTTP/1.1 200 OK", "Content-Length: 100", ""),
         method=Method.HEAD),
    Seed("head-chunked", crlf("HTTP/1.1 200 OK", "Transfer-Encoding: chunked", ""),
         method=Method.HEAD),
    Seed("204-content-length", crlf("HTTP/1.1 204 No Content", "Content-Length: 5", "")),
    Seed("304-content-length", crlf("HTTP/1.1 304 Not Modified", "Content-Length: 100", "")),
    Seed("101", crlf("HTTP/1.1 101 Switching Protocols", "Upgrade: x", "Connection: upgrade", "")),
    Seed("connection-close",
         crlf("HTTP/1.1 200 OK", "Connection: close", "Content-Length: 3", "") + b"bye", eof=True),
    Seed("stray-bytes-after",
         crlf("HTTP/1.1 200 OK", "Content-Length: 2", "") + b"ok" + crlf("HTTP/1.1 408 Timeout", "")),
    Seed("post-417", crlf("HTTP/1.1 417 Expectation Failed", "Content-Length: 0", ""),
         method=Method.POST),
    Seed("options-ows", crlf("HTTP/1.1 200 OK", "content-length:   3  ", "X-Empty:", "") + b"abc",
         method=Method.OPTIONS),
    Seed("announced-too-large", crlf("HTTP/1.1 200 OK", "Content-Length: 2000", "")),
    Seed("announced-above-2-62",
         crlf("HTTP/1.1 200 OK", "Content-Length: 99999999999999999999999999", "")),
    Seed("gzip-chunked",
         crlf("HTTP/1.1 200 OK", "Transfer-Encoding: gzip, chunked", "", "5", "hello", "0", ""),
         splits=[30, 20]),
    Seed("post-chunked",
         crlf("HTTP/1.1 200 OK", "Transfer-Encoding: chunked", "", "2", "ok", "0", ""),
         method=Method.POST, splits=[10, 30, 5]),
    Seed("empty-eof", b"", eof=True),
    Seed("eof-in-chunk",
         crlf("HTTP/1.1 200 OK", "Transfer-Encoding: chunked", "", "5") + b"hel", eof=True),
]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("out", type=Path)
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    for seed in SEEDS:
        (args.out / f"hand-{seed.name}").write_bytes(seed.encode())
    samples = sorted((HERE / "httparse").iterdir())
    for sample in samples:
        get_eof = Seed(sample.name, sample.read_bytes(), eof=True)
        (args.out / f"httparse-{sample.name}").write_bytes(get_eof.encode())
    print(f"wrote {len(SEEDS)} hand-written seeds and {len(samples)} httparse samples to {args.out}")


if __name__ == "__main__":
    main()

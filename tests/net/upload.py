#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.12"
# ///
"""Receives uploads.  Reads each request's body, framed by Content-Length or chunked (decoding the
chunked framing itself and refusing any deviation from RFC 9112 section 7.1 with a 400), checks that
byte k of the body is k % 251 (the pattern net-client's producer writes), discards it, and answers
with what it received, keeping the connection alive:

    pattern=<ok|bad at k> received=<bytes> framing=<length|chunked> chunks=<n>

Paths:
  /sink            read the body, answer 200
  /close?after=N   read N bytes of the body, then close the connection without answering
  /307             read the body, answer 307 with Location: /sink

Logs one line per connection accepted and closed, and per request: method, path, framing, bytes,
chunks and pattern.  Usage: upload.py PORT"""
import socket, sys, threading, time
from urllib.parse import parse_qs, urlsplit

PATTERN = bytes(range(251)) * (65536 // 251 + 2)
t0 = time.monotonic()
lock = threading.Lock()


def log(msg):
    with lock:
        print(f"{1000 * (time.monotonic() - t0):10.1f} {msg}", flush=True)


class Closed(Exception):
    pass


class Reader:
    def __init__(self, conn):
        self.conn = conn
        self.buf = b""

    def fill(self):
        d = self.conn.recv(65536)
        if not d:
            raise Closed()
        self.buf += d

    def line(self):
        while b"\r\n" not in self.buf:
            if len(self.buf) > 65536:
                raise ValueError("line too long")
            self.fill()
        line, _, self.buf = self.buf.partition(b"\r\n")
        return line

    def take(self, n):
        """Up to n bytes, at least one."""
        if not self.buf:
            self.fill()
        out, self.buf = self.buf[:n], self.buf[n:]
        return out


class Body:
    def __init__(self):
        self.n = 0
        self.bad = None

    def feed(self, data):
        for i in range(0, len(data), 60000):
            piece = data[i:i + 60000]
            start = self.n % 251
            if self.bad is None and piece != PATTERN[start:start + len(piece)]:
                k = next(j for j in range(len(piece)) if piece[j] != PATTERN[start + j])
                self.bad = self.n + k
            self.n += len(piece)


def read_fixed(r, body, n, limit=None):
    """Reads n body bytes (or stops after `limit`); returns whether all were read."""
    left = n if limit is None else min(n, limit)
    while left > 0:
        d = r.take(left)
        body.feed(d)
        left -= len(d)
    return limit is None or limit >= n


def read_chunked(r, body):
    chunks = 0
    while True:
        line = r.line()
        size_text = line.split(b";", 1)[0]
        if not size_text or any(c not in b"0123456789abcdefABCDEF" for c in size_text):
            raise ValueError(f"bad chunk-size line {line!r}")
        size = int(size_text, 16)
        if size == 0:
            break
        chunks += 1
        read_fixed(r, body, size)
        if r.line() != b"":
            raise ValueError("chunk data not followed by CRLF")
    while r.line() != b"":
        pass
    return chunks


def serve(conn, cid):
    r = Reader(conn)
    try:
        while True:
            head = []
            while True:
                line = r.line()
                if line == b"":
                    break
                head.append(line.decode("latin-1"))
            method, target, _ = head[0].split(" ", 2)
            fields = {}
            for h in head[1:]:
                k, _, v = h.partition(":")
                fields.setdefault(k.strip().lower(), []).append(v.strip())
            url = urlsplit(target)
            q = parse_qs(url.query)
            body = Body()
            te = fields.get("transfer-encoding", [])
            limit = int(q["after"][0]) if url.path == "/close" else None
            if te:
                if te != ["chunked"] or "content-length" in fields:
                    raise ValueError(f"framing {fields}")
                framing = "chunked"
                chunks = read_chunked(r, body) if limit is None else None
                if limit is not None:
                    # Read raw bytes of the chunked body up to the limit, then close.
                    got = 0
                    while got < limit:
                        got += len(r.take(limit - got))
            else:
                framing = "length"
                n = int(fields.get("content-length", ["0"])[0])
                chunks = 0
                read_fixed(r, body, n, limit)
            pattern = "ok" if body.bad is None else f"bad at {body.bad}"
            log(f"conn{cid} {method} {url.path} framing={framing} received={body.n} chunks={chunks} "
                f"pattern={pattern} fields={sorted(fields)}")
            if limit is not None:
                log(f"conn{cid} closing after {limit} body bytes, without an answer")
                conn.shutdown(socket.SHUT_RDWR)
                return
            text = f"pattern={pattern} received={body.n} framing={framing} chunks={chunks}".encode()
            if url.path == "/307":
                resp = b"HTTP/1.1 307 Temporary Redirect\r\nLocation: /sink\r\nContent-Length: 0\r\n\r\n"
            else:
                resp = (b"HTTP/1.1 200 OK\r\nContent-Length: " + str(len(text)).encode() + b"\r\n\r\n"
                        + text)
            conn.sendall(resp)
    except Closed:
        log(f"conn{cid} EOF from client")
    except ValueError as e:
        log(f"conn{cid} BAD REQUEST: {e}")
        conn.sendall(b"HTTP/1.1 400 Bad Request\r\nContent-Length: 0\r\nConnection: close\r\n\r\n")
    except OSError as e:
        log(f"conn{cid} {e}")
    finally:
        conn.close()


def main():
    port = int(sys.argv[1])
    s = socket.socket()
    s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    s.bind(("127.0.0.1", port))
    s.listen(64)
    print(f"listening on 127.0.0.1:{port}", flush=True)
    cid = 0
    while True:
        c, peer = s.accept()
        log(f"conn{cid} accepted {peer}")
        threading.Thread(target=serve, args=(c, cid), daemon=True).start()
        cid += 1


main()

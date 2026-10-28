#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.12"
# ///
"""Answers every request early: reads only the request head, sends a complete 413 response at once,
and then never reads again but keeps the connection open, with a small receive buffer, so that a
client still uploading stalls.  Usage: early.py PORT"""
import socket, sys, threading, time

port = int(sys.argv[1])
s = socket.socket()
s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
s.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, 4096)
s.bind(("127.0.0.1", port))
s.listen(16)
print(f"listening on 127.0.0.1:{port}", flush=True)
t0 = time.monotonic()
conns = []


def serve(c):
    buf = b""
    while b"\r\n\r\n" not in buf:
        d = c.recv(4096)
        if not d:
            return
        buf += d
    head = buf.partition(b"\r\n\r\n")[0].decode("latin-1").split("\r\n")[0]
    print(f"{1000 * (time.monotonic() - t0):10.1f} read the head {head!r}; answering 413, reading no more", flush=True)
    c.sendall(b"HTTP/1.1 413 Payload Too Large\r\nContent-Length: 3\r\n\r\nbig")


while True:
    c, peer = s.accept()
    conns.append(c)
    print(f"{1000 * (time.monotonic() - t0):10.1f} accepted {peer}", flush=True)
    threading.Thread(target=serve, args=(c,), daemon=True).start()

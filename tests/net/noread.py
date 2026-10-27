#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.12"
# ///
"""Accepts connections and never reads from them, with a small receive buffer, so that a client's
large write fills the socket buffers and stalls.  Usage: noread.py PORT"""
import socket, sys, time

port = int(sys.argv[1])
s = socket.socket()
s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
s.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, 4096)
s.bind(("127.0.0.1", port))
s.listen(16)
print(f"listening on 127.0.0.1:{port}", flush=True)
conns = []
t0 = time.monotonic()
while True:
    c, peer = s.accept()
    conns.append(c)
    print(f"{1000 * (time.monotonic() - t0):10.1f} accepted {peer}; not reading", flush=True)

#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.12"
# ///
"""Accepts connections and never reads from them, with a small receive buffer, so that a client's
large write fills the socket buffers and stalls; logs when a connection's first bytes arrive, which
it sees without reading them.  Usage: noread.py PORT"""
import select, socket, sys, threading, time

port = int(sys.argv[1])
s = socket.socket()
s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
s.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, 4096)
s.bind(("127.0.0.1", port))
s.listen(16)
print(f"listening on 127.0.0.1:{port}", flush=True)
conns = []
t0 = time.monotonic()


def watch(c, n):
    select.select([c], [], [])
    print(f"{1000 * (time.monotonic() - t0):10.1f} conn{n} bytes arrived; not reading", flush=True)


while True:
    c, peer = s.accept()
    conns.append(c)
    print(f"{1000 * (time.monotonic() - t0):10.1f} conn{len(conns)} accepted {peer}; not reading", flush=True)
    threading.Thread(target=watch, args=(c, len(conns)), daemon=True).start()

#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.12"
# ///
"""A minimal HTTP/1.1 server that answers every request (Content-Length body, any method and path)
with the same small JSON response, written in ONE sendall, with TCP_NODELAY set on the accepted
socket, and keeps the connection alive.  So any delay a client sees comes from how the client writes
its request, not from the server.

Logs one line per request: the number of recv() calls the request took and the gap in ms between
its first byte and the last byte of its body.  Two recv() calls and a gap of about 40 ms mean the
client's body was held back until the server's delayed ACK of the head (Nagle's algorithm).

Usage: onewrite.py --port N [--log FILE] [--nodelay 0|1]"""
import argparse, socket, threading, time

REPLY = b'{"ok": true}'
RESP = (b"HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nContent-Length: "
        + str(len(REPLY)).encode() + b"\r\n\r\n" + REPLY)


def serve(conn, log, lock):
    buf = b""
    with conn:
        while True:
            t_first = None
            nrecv = 0
            while b"\r\n\r\n" not in buf:
                d = conn.recv(65536)
                if not d:
                    return
                if t_first is None:
                    t_first = time.monotonic()
                nrecv += 1
                buf += d
            head, _, rest = buf.partition(b"\r\n\r\n")
            n = 0
            for line in head.split(b"\r\n")[1:]:
                k, _, v = line.partition(b":")
                if k.strip().lower() == b"content-length":
                    n = int(v.strip())
            while len(rest) < n:
                d = conn.recv(65536)
                if not d:
                    return
                nrecv += 1
                rest += d
            t_last = time.monotonic()
            buf = rest[n:]
            if t_first is None:
                t_first = t_last
            with lock:
                log.write(f"{nrecv} {1000*(t_last-t_first):.3f}\n")
                log.flush()
            conn.sendall(RESP)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--port", type=int, required=True)
    ap.add_argument("--log", default="/dev/null")
    ap.add_argument("--nodelay", type=int, default=1)
    a = ap.parse_args()
    log = open(a.log, "w")
    lock = threading.Lock()
    s = socket.socket()
    s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    s.bind(("127.0.0.1", a.port))
    s.listen(64)
    print(f"listening on 127.0.0.1:{a.port}", flush=True)
    while True:
        c, _ = s.accept()
        if a.nodelay:
            c.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        threading.Thread(target=serve, args=(c, log, lock), daemon=True).start()


main()

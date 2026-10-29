#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.12"
# ///
"""A server for measuring the client's idle check (net-client idlecheck).

Each connection sends one line naming a scenario; the server answers "pong", and 50 ms later sends
bytes ("data"), closes ("fin"), resets ("rst") or does nothing ("none"), then keeps the connection
until the client closes it.

Usage: idle.py <port>
"""
import socket, sys, threading, time

SO_LINGER_RST = b"\x01\x00\x00\x00\x00\x00\x00\x00"


def handle(conn):
    try:
        line = b""
        while not line.endswith(b"\n"):
            d = conn.recv(64)
            if not d:
                return
            line += d
        scenario = line.strip().decode()
        conn.sendall(b"pong")
        time.sleep(0.05)
        if scenario == "data":
            conn.sendall(b"HTTP/1.1 408 Request Timeout\r\nContent-Length: 0\r\n\r\n")
        elif scenario == "fin":
            conn.shutdown(socket.SHUT_WR)
        elif scenario == "rst":
            conn.setsockopt(socket.SOL_SOCKET, socket.SO_LINGER, SO_LINGER_RST)
            conn.close()
            return
        while conn.recv(65536):
            pass
    except OSError:
        pass
    finally:
        conn.close()


def main():
    port = int(sys.argv[1])
    s = socket.socket()
    s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    s.bind(("127.0.0.1", port))
    s.listen(256)
    print("listening", flush=True)
    while True:
        c, _ = s.accept()
        threading.Thread(target=handle, args=(c,), daemon=True).start()


main()

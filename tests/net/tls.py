#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.12"
# ///
"""An HTTPS server for probing the client's TLS over real TCP, with a plain HTTP listener beside it.

The certificate and key come from tests/net/tls-certs.sh, which makes a test CA and its
certificates at test time.  Behaviour is chosen by the request path; every connection, request and
TLS event is logged with a connection number and a monotonic timestamp.

  GET  /hello              200, a short body framed by Content-Length; the connection is kept
  POST /echo               200, the request body back
  PUT  /count              200, what the request body was: its size, its framing (Content-Length or
                           chunked), and whether byte k of it is k % 251, the pattern net-client's
                           upload producer writes
  GET  /close-delimited    200 without Content-Length, a 100 KB body ended by close_notify
  GET  /truncate           200 without Content-Length, 50 KB of body, then the TCP connection
                           closed without close_notify
  GET  /truncate-framed    200 with Content-Length, the whole body, then closed without close_notify
  GET  /truncate-midbody   200 with Content-Length: 100000, 50 KB of it, closed without close_notify
  GET  /stray              200 with Content-Length, then 5 stray bytes in a TLS record of their own
  GET  /big?n=N            200 with a body of N bytes
  GET  /trickle?ms=M       200 with Content-Length: 20, one byte of it every M milliseconds
  GET  /close-after        200 with Content-Length, and close_notify in the same TCP segment
  GET  /redirect-http      302 to http://127.0.0.1:<plain port>/plain
  GET  /plain (plain port) 200 over plain HTTP

Modes (--mode) for the TLS port: normal; hang (accept TCP and never answer the handshake);
close-handshake (read the ClientHello, then close); tls11 (offer TLS 1.1 at most); tls12 (offer
TLS 1.2 at most).  The server name each client sent (SNI) is logged as sni=<name>, or sni=None.

--idle-close MS closes a kept connection that has been idle for MS milliseconds, with close_notify
(--idle-notify 1) or without it (0).

Usage: tls.py --cert FILE --key FILE [--port N] [--plain-port N] [--mode M] [--idle-close MS]
              [--idle-notify 0|1]
"""
import argparse, socket, ssl, sys, threading, time, warnings

LOCK = threading.Lock()
T0 = time.monotonic()
SEQ = [0]
ARGS = None


def log(msg):
    with LOCK:
        sys.stdout.write(f"{1000*(time.monotonic()-T0):10.1f} {msg}\n")
        sys.stdout.flush()


def read_request(conn, buf):
    """Returns (method, target, headers, body, rest), or (None, ...) at the end of input."""
    while b"\r\n\r\n" not in buf:
        d = conn.recv(65536)
        if not d:
            return None, None, None, None, buf
        buf += d
    head, _, rest = buf.partition(b"\r\n\r\n")
    lines = head.decode("latin-1").split("\r\n")
    method, target, _ = lines[0].split(" ", 2)
    headers = {}
    for line in lines[1:]:
        k, _, v = line.partition(":")
        headers[k.strip().lower()] = v.strip()
    if headers.get("transfer-encoding", "").lower() == "chunked":
        body = b""
        while True:
            while b"\r\n" not in rest:
                d = conn.recv(65536)
                if not d:
                    return None, None, None, None, b""
                rest += d
            line, _, rest = rest.partition(b"\r\n")
            size = int(line.split(b";")[0], 16)
            while len(rest) < size + 2:
                d = conn.recv(65536)
                if not d:
                    return None, None, None, None, b""
                rest += d
            if size == 0:
                # The last chunk; an empty trailer section follows (the client sends none).
                return method, target, headers, body, rest[2:]
            body += rest[:size]
            rest = rest[size + 2:]
    n = int(headers.get("content-length", "0"))
    while len(rest) < n:
        d = conn.recv(65536)
        if not d:
            return None, None, None, None, b""
        rest += d
    return method, target, headers, rest[:n], rest[n:]


def response(status, body, extra=""):
    return (f"HTTP/1.1 {status}\r\nContent-Length: {len(body)}\r\n{extra}\r\n").encode() + body


def abrupt(conn, n):
    """Closes the TCP connection without close_notify."""
    log(f"conn{n} closing without close_notify")
    try:
        conn.shutdown(socket.SHUT_RDWR)  # drops the TLS state and shuts the socket down: no alert
    except OSError:
        pass
    conn.close()


def notify(conn, n):
    """Sends close_notify, then closes."""
    log(f"conn{n} sending close_notify")
    try:
        conn.unwrap().close()
    except (OSError, ssl.SSLError) as e:
        log(f"conn{n} unwrap: {e!r}")
        conn.close()


def serve_tls(conn, n):
    buf = b""
    while True:
        if ARGS.idle_close:
            conn.settimeout(ARGS.idle_close / 1000)
        try:
            method, target, headers, body, buf = read_request(conn, buf)
        except socket.timeout:
            log(f"conn{n} idle for {ARGS.idle_close} ms")
            (notify if ARGS.idle_notify else abrupt)(conn, n)
            return
        except (OSError, ssl.SSLError) as e:
            log(f"conn{n} read failed: {e!r}")
            conn.close()
            return
        conn.settimeout(None)
        if method is None:
            log(f"conn{n} EOF from client")
            conn.close()
            return
        log(f"conn{n} {method} {target} {headers} body={len(body)}B version={conn.version()}")
        if target == "/hello":
            conn.sendall(response("200 OK", b"hello over tls\n"))
        elif target == "/echo":
            conn.sendall(response("200 OK", body))
        elif target == "/count":
            pattern = bytes(k % 251 for k in range(len(body)))
            framing = "chunked" if "transfer-encoding" in headers else "length"
            text = f"pattern={'ok' if body == pattern else 'bad'} received={len(body)} framing={framing}"
            conn.sendall(response("200 OK", text.encode()))
        elif target == "/close-delimited":
            conn.sendall(b"HTTP/1.1 200 OK\r\nConnection: close\r\n\r\n" + b"c" * 100_000)
            notify(conn, n)
            return
        elif target == "/truncate":
            conn.sendall(b"HTTP/1.1 200 OK\r\nConnection: close\r\n\r\n" + b"t" * 50_000)
            time.sleep(0.05)
            abrupt(conn, n)
            return
        elif target == "/truncate-framed":
            conn.sendall(response("200 OK", b"f" * 10_000, "Connection: close\r\n"))
            time.sleep(0.05)
            abrupt(conn, n)
            return
        elif target == "/truncate-midbody":
            conn.sendall(b"HTTP/1.1 200 OK\r\nContent-Length: 100000\r\n\r\n" + b"m" * 50_000)
            time.sleep(0.05)
            abrupt(conn, n)
            return
        elif target == "/stray":
            conn.sendall(response("200 OK", b"stray\n"))
            conn.sendall(b"XXXXX")  # a record of its own
        elif target.startswith("/big?n="):
            n = int(target.split("=", 1)[1])
            conn.sendall(f"HTTP/1.1 200 OK\r\nContent-Length: {n}\r\n\r\n".encode())
            chunk = b"b" * 65536
            while n > 0:
                conn.sendall(chunk[:n])
                n -= min(n, len(chunk))
        elif target.startswith("/trickle?ms="):
            ms = int(target.split("=", 1)[1])
            conn.sendall(b"HTTP/1.1 200 OK\r\nContent-Length: 20\r\n\r\n")
            try:
                for _ in range(20):
                    time.sleep(ms / 1000)
                    conn.sendall(b"t")
            except (OSError, ssl.SSLError) as e:
                log(f"conn{n} trickle stopped: {e!r}")
                conn.close()
                return
        elif target == "/close-after":
            # Cork the socket, so that the response and the close_notify after it leave in one
            # segment and reach the client in one read; uncork only once both are queued.  unwrap()
            # queues close_notify and then waits for the client's, which cannot come before the
            # uncork: its time-out ends that wait.
            conn.setsockopt(socket.IPPROTO_TCP, socket.TCP_CORK, 1)
            conn.sendall(response("200 OK", b"bye\n"))
            conn.settimeout(0.2)
            log(f"conn{n} sending close_notify, corked with the response")
            try:
                conn.unwrap()
            except (OSError, ssl.SSLError) as e:
                log(f"conn{n} unwrap: {e!r}")
            try:
                conn.setsockopt(socket.IPPROTO_TCP, socket.TCP_CORK, 0)
                time.sleep(0.2)
            except OSError:
                pass
            conn.close()
            return
        elif target == "/redirect-http":
            conn.sendall(response("302 Found", b"", f"Location: http://127.0.0.1:{ARGS.plain_bound}/plain\r\n"))
        else:
            conn.sendall(response("404 Not Found", b"no such path\n"))


def handle(raw, n, ctx):
    # Without it, a small response after the session tickets waits for the client's delayed ACK
    # (about 70 ms on Linux; logs/2026-10-30/tls/net/nagle.txt).
    raw.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
    if ARGS.mode == "hang":
        log(f"conn{n} accepted; never answering the handshake")
        time.sleep(3600)
        return
    if ARGS.mode == "close-handshake":
        raw.recv(65536)
        log(f"conn{n} read the ClientHello; closing")
        raw.close()
        return
    try:
        # Ragged EOFs raise, so that the log tells a close with close_notify from one without.
        conn = ctx.wrap_socket(raw, server_side=True, suppress_ragged_eofs=False)
    except (OSError, ssl.SSLError) as e:
        log(f"conn{n} handshake failed: {e!r}")
        raw.close()
        return
    log(f"conn{n} handshake done version={conn.version()} cipher={conn.cipher()[0]} alpn={conn.selected_alpn_protocol()}")
    serve_tls(conn, n)


def serve_plain(raw, n):
    buf = b""
    while True:
        method, target, headers, body, buf = read_request(raw, buf)
        if method is None:
            raw.close()
            return
        log(f"plain{n} {method} {target} {headers}")
        raw.sendall(response("200 OK", b"plain hello\n"))


def accept_loop(listener, tls_ctx):
    while True:
        raw, peer = listener.accept()
        with LOCK:
            SEQ[0] += 1
            n = SEQ[0]
        log(f"{'conn' if tls_ctx else 'plain'}{n} accepted from {peer}")
        target = (lambda: handle(raw, n, tls_ctx)) if tls_ctx else (lambda: serve_plain(raw, n))
        threading.Thread(target=target, daemon=True).start()


def main():
    global ARGS
    p = argparse.ArgumentParser()
    p.add_argument("--cert", required=True)
    p.add_argument("--key", required=True)
    p.add_argument("--port", type=int, default=0)
    p.add_argument("--plain-port", type=int, default=0)
    p.add_argument("--mode", default="normal", choices=["normal", "hang", "close-handshake", "tls11", "tls12"])
    p.add_argument("--idle-close", type=int, default=0)
    p.add_argument("--idle-notify", type=int, default=1)
    ARGS = p.parse_args()
    ctx = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
    ctx.load_cert_chain(ARGS.cert, ARGS.key)
    ctx.set_alpn_protocols(["http/1.1"])
    ctx.sni_callback = lambda sslobj, name, c: log(f"sni={name}")
    if ARGS.mode == "tls12":
        ctx.maximum_version = ssl.TLSVersion.TLSv1_2
    if ARGS.mode == "tls11":
        ctx.minimum_version = ssl.TLSVersion.MINIMUM_SUPPORTED
        with warnings.catch_warnings():
            warnings.simplefilter("ignore", DeprecationWarning)
            ctx.maximum_version = ssl.TLSVersion.TLSv1_1
        ctx.set_ciphers("DEFAULT:@SECLEVEL=0")
    tls_listener = socket.create_server(("127.0.0.1", ARGS.port))
    plain_listener = socket.create_server(("127.0.0.1", ARGS.plain_port))
    ARGS.plain_bound = plain_listener.getsockname()[1]
    threading.Thread(target=accept_loop, args=(plain_listener, None), daemon=True).start()
    log(f"listening tls={tls_listener.getsockname()[1]} plain={ARGS.plain_bound} mode={ARGS.mode} "
        f"openssl={ssl.OPENSSL_VERSION}")
    accept_loop(tls_listener, ctx)


if __name__ == "__main__":
    main()

#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.12"
# ///
"""A deliberately misbehaving HTTP/1.1 server for probing a client over real TCP.

Behaviour is chosen by the request path (query parameters tune it).  Every connection and every
request it reads is logged with a connection number and a monotonic timestamp, so the log shows how
many connections the client opened and what it sent on each.

Usage: evil.py --port N [--host 0.0.0.0] [--log FILE] [--v6]
"""
import argparse, email.utils, socket, threading, time, urllib.parse, sys

LOG = sys.stdout
LOCK = threading.Lock()
T0 = time.monotonic()
CONN_SEQ = [0]
FLAKY = {}
LISTENER = [None]


def log(msg):
    with LOCK:
        LOG.write(f"{1000*(time.monotonic()-T0):10.1f} {msg}\n")
        LOG.flush()


def read_request(conn, buf):
    """Returns (method, target, headers dict lowercased, body bytes, rest) or None on EOF."""
    while b"\r\n\r\n" not in buf:
        d = conn.recv(65536)
        if not d:
            return None, buf
        buf += d
    head, _, rest = buf.partition(b"\r\n\r\n")
    lines = head.decode("latin-1").split("\r\n")
    method, target, _ = lines[0].split(" ", 2)
    headers = {}
    for line in lines[1:]:
        k, _, v = line.partition(":")
        headers.setdefault(k.strip().lower(), []).append(v.strip())
    body = b""
    if "content-length" in headers:
        n = int(headers["content-length"][0])
        while len(rest) < n:
            d = conn.recv(65536)
            if not d:
                return None, b""
            rest += d
        body, rest = rest[:n], rest[n:]
    elif headers.get("transfer-encoding", [""])[0].lower() == "chunked":
        while True:
            while b"\r\n" not in rest:
                d = conn.recv(65536)
                if not d:
                    return None, b""
                rest += d
            line, _, rest = rest.partition(b"\r\n")
            size = int(line.split(b";")[0], 16)
            while len(rest) < size + 2:
                d = conn.recv(65536)
                if not d:
                    return None, b""
                rest += d
            body += rest[:size]
            rest = rest[size + 2:]
            if size == 0:
                break
    return (method, target, headers, body), rest


def resp(status, headers=(), body=b"", version="HTTP/1.1"):
    h = "".join(f"{k}: {v}\r\n" for k, v in headers)
    return f"{version} {status}\r\n{h}\r\n".encode() + body


def cl(body, extra=()):
    return [("Content-Length", str(len(body)))] + list(extra)


def handle(conn, cid, args):
    try:
        handle1(conn, cid, args)
    finally:
        conn.close()
        log(f"conn{cid} closed by server")


def handle1(conn, cid, args):
    buf = b""
    nreq = 0
    while True:
        try:
            req, buf = read_request(conn, buf)
        except (ConnectionResetError, OSError) as e:
            log(f"conn{cid} read error {e!r}")
            return
        if req is None:
            log(f"conn{cid} EOF from client after {nreq} requests")
            return
        nreq += 1
        method, target, headers, body = req
        u = urllib.parse.urlsplit(target)
        q = dict(urllib.parse.parse_qsl(u.query))
        path = u.path
        hdrs = {k: v for k, v in headers.items() if k in ("authorization", "cookie", "host", "content-length", "transfer-encoding", "expect", "connection", "x-test")}
        log(f"conn{cid} req{nreq} {method} {target} {hdrs} body={len(body)}B")
        mode = path.strip("/").split("/")[0]
        if mode == "close-after-idle":
            # answer normally (keep-alive), then close if no new request arrives within ms
            b = b"ok"
            conn.sendall(resp("200 OK", cl(b), b if method != "HEAD" else b""))
            conn.settimeout(int(q.get("ms", "1000")) / 1000)
            try:
                d = conn.recv(65536)
            except socket.timeout:
                log(f"conn{cid} idle timeout, closing")
                return
            finally:
                conn.settimeout(None)
            if not d:
                log(f"conn{cid} EOF from client after {nreq} requests")
                return
            buf += d
            continue
        if mode == "die-on-next":
            # answer this request with keep-alive, then close as soon as the next request's first
            # bytes arrive, without answering it: the stale keep-alive race made deterministic
            # (ms=M: answer M ms after reading the request)
            time.sleep(int(q.get("ms", "0")) / 1000)
            b = b"ok"
            conn.sendall(resp("200 OK", cl(b), b))
            d = conn.recv(65536)
            log(f"conn{cid} got {len(d)} bytes of the next request; closing without answering")
            if q.get("rst") == "1":
                conn.setsockopt(socket.SOL_SOCKET, socket.SO_LINGER, b"\x01\x00\x00\x00\x00\x00\x00\x00")
            return
        out = route(mode, method, path, q, headers, body, args, conn, cid)
        if out == "close":
            return
        if out is not None:
            conn.sendall(out)


def route(mode, method, path, q, headers, body, args, conn, cid):
    ms = int(q.get("ms", "0"))
    if mode in ("ok", ""):
        b = b"hello"
        return resp("200 OK", cl(b, [("Set-Cookie", "sid=1; Path=/")] if q.get("cookie") else []), b if method != "HEAD" else b"")
    if mode == "echo":
        b = (f"{method} {path} auth={headers.get('authorization')} cookie={headers.get('cookie')} "
             f"host={headers.get('host')} body={body.decode('latin-1')!r}").encode()
        return resp("200 OK", cl(b), b)
    if mode == "sleep":
        time.sleep(ms / 1000)
        log(f"conn{cid} answering after {ms} ms")
        b = f"slept {ms}".encode()
        return resp("200 OK", cl(b), b)
    if mode == "close-delimited":
        conn.sendall(resp("200 OK", [("Content-Type", "text/plain")], version=q.get("v", "HTTP/1.0")))
        for i in range(int(q.get("n", "3"))):
            conn.sendall(f"part{i};".encode())
            time.sleep(ms / 1000)
        return "close"
    if mode == "chunked-ext":
        out = resp("200 OK", [("Transfer-Encoding", "chunked"), ("Trailer", "X-Sum")])
        out += b"5;name=value;flag\r\nhello\r\n"
        out += b"6;quoted=\"a b\"\r\n world\r\n"
        out += b"0;last=1\r\nX-Sum: 42\r\nX-Other: y\r\n\r\n"
        return out
    if mode == "drip":
        # chunked, n chunks, each after ms; total exceeds readTimeout though each gap is below it
        conn.sendall(resp("200 OK", [("Transfer-Encoding", "chunked")]))
        for i in range(int(q.get("n", "5"))):
            time.sleep(ms / 1000)
            conn.sendall(b"2\r\nab\r\n")
        conn.sendall(b"0\r\n\r\n")
        return None
    if mode == "stall-body":
        conn.sendall(resp("200 OK", [("Content-Length", "10")], b"abc"))
        time.sleep(ms / 1000)
        conn.sendall(b"defghij")
        return None
    if mode == "stall-head":
        time.sleep(ms / 1000)
        b = b"late"
        return resp("200 OK", cl(b), b)
    if mode == "unsolicited-100":
        b = b"after100"
        return resp("100 Continue") + resp("200 OK", cl(b), b)
    if mode == "early-hints":
        b = b"after103"
        return (resp("103 Early Hints", [("Link", "</style.css>; rel=preload")])
                + resp("103 Early Hints", [("Link", "</app.js>; rel=preload")])
                + resp("200 OK", cl(b), b))
    if mode == "102":
        b = b"after102"
        conn.sendall(resp("102 Processing"))
        time.sleep(ms / 1000)
        return resp("200 OK", cl(b), b)
    if mode == "204":
        return resp("204 No Content", [("Content-Length", "5")])
    if mode == "304":
        return resp("304 Not Modified", [("Content-Length", "5"), ("ETag", "\"x\"")])
    if mode == "head-cl":
        # HEAD with Content-Length of the GET body, no body bytes
        return resp("200 OK", [("Content-Length", "12345")], b"" if method == "HEAD" else b"x" * 12345)
    if mode == "bigheader":
        n = int(q.get("n", "20000"))
        b = b"ok"
        return resp("200 OK", cl(b, [("X-Big", "a" * n)]), b)
    if mode == "manyheaders":
        n = int(q.get("n", "300"))
        b = b"ok"
        return resp("200 OK", cl(b, [(f"X-H{i}", "v") for i in range(n)]), b)
    if mode == "bigbody":
        n = int(q.get("n", str(100 * 1024 * 1024)))
        conn.sendall(resp("200 OK", [("Content-Length", str(n))]))
        chunk = b"z" * 65536
        sent = 0
        try:
            while sent < n:
                k = min(len(chunk), n - sent)
                conn.sendall(chunk[:k])
                sent += k
        except OSError as e:
            log(f"conn{cid} bigbody send failed after {sent}B: {e!r}")
            return "close"
        return None
    if mode == "badstatus":
        return b"HTTP/1.1 2OO OK\r\nContent-Length: 2\r\n\r\nok"
    if mode == "noreason":
        return b"HTTP/1.1 200\r\nContent-Length: 2\r\n\r\nok"
    if mode == "lf-only":
        return b"HTTP/1.1 200 OK\nContent-Length: 2\n\nok"
    if mode == "http09":
        conn.sendall(b"hello there\n")
        return "close"
    if mode == "garbage-after":
        # a response followed by bytes nobody asked for (an unsolicited second response)
        b = b"ok"
        return resp("200 OK", cl(b), b) + resp("200 OK", cl(b"evil"), b"evil")
    if mode == "redir":
        # /redir/<code>?to=<location>
        code = int(path.strip("/").split("/")[1])
        reason = {301: "Moved", 302: "Found", 303: "See Other", 307: "Temporary", 308: "Permanent"}[code]
        b = b"redirect body" + b"p" * int(q.get("pad", "0"))
        extra = [("Location", q["to"])]
        if q.get("cookie"):
            extra.append(("Set-Cookie", "sid=abc; Path=/"))
        return resp(f"{code} {reason}", cl(b, extra), b)
    if mode == "chain":
        # /chain/<n>?code=C: a redirect (302 by default) to /chain/<n-1> with the same query, and at 0
        # what /echo answers
        n = int(path.strip("/").split("/")[1])
        if n == 0:
            return route("echo", method, path, q, headers, body, args, conn, cid)
        code = int(q.get("code", "302"))
        u = urllib.parse.urlencode(q)
        b = b"chain"
        return resp(f"{code} Redirect", cl(b, [("Location", f"/chain/{n - 1}" + (f"?{u}" if u else ""))]), b)
    if mode == "bounce":
        # /bounce/<port>/<rest>?code=C: a redirect (302 by default) to http://127.0.0.1:<port>/<rest>
        # with the same query
        parts = path.strip("/").split("/")
        u = urllib.parse.urlencode(q)
        loc = f"http://127.0.0.1:{parts[1]}/" + "/".join(parts[2:]) + (f"?{u}" if u else "")
        b = b"bounce"
        return resp(f"{int(q.get('code', '302'))} Redirect", cl(b, [("Location", loc)]), b)
    if mode == "flaky":
        # /flaky?key=K&code=C&n=N&after=A: the first N requests with key K (over all connections)
        # are answered with status C (503 by default), with Retry-After: A when given (A=dateS sends
        # an HTTP-date S seconds after the response's Date); later ones with 200
        key = q.get("key", "")
        with LOCK:
            FLAKY[key] = FLAKY.get(key, 0) + 1
            k = FLAKY[key]
        if k <= int(q.get("n", "1")):
            extra = []
            after = q.get("after")
            if after is not None and after.startswith("date"):
                now = int(time.time())
                extra = [("Date", email.utils.formatdate(now, usegmt=True)),
                         ("Retry-After", email.utils.formatdate(now + int(after[4:]), usegmt=True))]
            elif after is not None:
                extra = [("Retry-After", after)]
            b = b"busy" + b"p" * int(q.get("pad", "0"))
            log(f"conn{cid} flaky {key} request {k}: {q.get('code', '503')}")
            return resp(f"{q.get('code', '503')} Busy", cl(b, extra), b)
        b = f"recovered after {k - 1}".encode()
        return resp("200 OK", cl(b), b)
    if mode == "loop":
        nxt = "/loop/b" if path.endswith("/a") else "/loop/a"
        return resp("302 Found", cl(b"", [("Location", nxt)]))
    if mode == "infinite-redirect":
        n = int(path.strip("/").split("/")[1]) if path.count("/") > 1 else 0
        return resp("302 Found", cl(b"", [("Location", f"/infinite-redirect/{n+1}")]))
    if mode == "unread-body":
        # a large body the caller is not expected to read
        n = int(q.get("n", str(4 * 1024 * 1024)))
        return resp("200 OK", [("Content-Length", str(n))], b"u" * n)
    if mode == "late-unsolicited":
        # answer, then after ms (client idle) send a second, unrequested response
        b = b"ok"
        conn.sendall(resp("200 OK", cl(b), b))
        time.sleep(ms / 1000)
        conn.sendall(resp("200 OK", cl(b"evil"), b"evil"))
        log(f"conn{cid} sent unsolicited response")
        return None
    if mode == "idle-408":
        # answer, then after ms of idleness send 408 Request Timeout with Connection: close and
        # close (what some servers do on keep-alive timeout); linger=ms2 delays the close itself
        b = b"ok"
        conn.sendall(resp("200 OK", cl(b), b))
        conn.settimeout(ms / 1000)
        try:
            d = conn.recv(65536)
            conn.settimeout(None)
            if d:
                log(f"conn{cid} got next request before idle timeout")
            return "close"
        except socket.timeout:
            conn.settimeout(None)
        conn.sendall(resp("408 Request Timeout", [("Connection", "close"), ("Content-Length", "0")]))
        log(f"conn{cid} sent 408")
        if q.get("unlisten") == "1":
            # stop accepting connections, keeping this one: a fresh connect is then refused
            LISTENER[0].shutdown(socket.SHUT_RDWR)
            LISTENER[0].close()
            log("stopped listening")
        time.sleep(int(q.get("linger", "0")) / 1000)
        return "close"
    if mode == "trickle":
        # a head promising a large body, then one byte every ms until the client goes away
        conn.sendall(resp("200 OK", [("Content-Length", q.get("n", "1000000"))]))
        try:
            while True:
                time.sleep(ms / 1000)
                conn.sendall(b"t")
        except OSError as e:
            log(f"conn{cid} trickle stopped: {e!r}")
        return "close"
    if mode == "interim-forever":
        # interim responses, one every ms, and never a final one
        try:
            while True:
                conn.sendall(resp("102 Processing"))
                time.sleep(ms / 1000)
        except OSError as e:
            log(f"conn{cid} interim stream stopped: {e!r}")
        return "close"
    if mode == "cl-mismatch":
        # Content-Length larger than the body, then close
        conn.sendall(b"HTTP/1.1 200 OK\r\nContent-Length: 100\r\n\r\nshort")
        return "close"
    if mode == "badchunk":
        # a chunk, then a chunk-size line that is not one, all in one write, then close
        conn.sendall(b"HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\nZZ\r\n")
        return "close"
    if mode == "dup-cl":
        return b"HTTP/1.1 200 OK\r\nContent-Length: 2\r\nContent-Length: 3\r\n\r\nok!"
    if mode == "te-cl":
        return b"HTTP/1.1 200 OK\r\nContent-Length: 2\r\nTransfer-Encoding: chunked\r\n\r\n3\r\nabc\r\n0\r\n\r\n"
    if mode == "head-stray":
        # a response to HEAD followed by the body it must not have: stray bytes on the connection
        return resp("200 OK", [("Content-Length", "5")], b"hello")
    if mode == "close-hdr":
        b = b"bye"
        return resp("200 OK", cl(b, [("Connection", "close")]), b)
    if mode == "rst":
        conn.setsockopt(socket.SOL_SOCKET, socket.SO_LINGER, b"\x01\x00\x00\x00\x00\x00\x00\x00")
        return "close"
    b = b"not found"
    return resp("404 Not Found", cl(b), b)


def main():
    global LOG
    ap = argparse.ArgumentParser()
    ap.add_argument("--port", type=int, required=True)
    ap.add_argument("--host", default="127.0.0.1")
    ap.add_argument("--log", default=None)
    ap.add_argument("--v6", action="store_true")
    a = ap.parse_args()
    if a.log:
        LOG = open(a.log, "a")
    fam = socket.AF_INET6 if a.v6 else socket.AF_INET
    s = socket.socket(fam)
    s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    if a.v6:
        s.setsockopt(socket.IPPROTO_IPV6, socket.IPV6_V6ONLY, 1)
    s.bind((a.host, a.port))
    s.listen(64)
    LISTENER[0] = s
    log(f"listening on {a.host}:{a.port}")
    while True:
        try:
            c, peer = s.accept()
        except OSError:
            # the listening socket was closed (idle-408 with unlisten=1): serve what is open
            while True:
                time.sleep(3600)
        c.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        CONN_SEQ[0] += 1
        cid = CONN_SEQ[0]
        log(f"conn{cid} accepted from {peer}")
        threading.Thread(target=handle, args=(c, cid, a), daemon=True).start()


main()

#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.10"
# dependencies = []
# ///
"""A small HTTP/1.1 server for the examples, on 127.0.0.1.

    GET  /hello            200, a JSON object, Content-Type: application/json
    POST /echo             200, the request body back, with the request's Content-Type
    GET  /numbers?count=N  200, the numbers 0 to N-1, one per line, in a chunked body

Prints "listening on PORT" once it accepts connections.  Usage: server.py [PORT] (default 8080)
"""

import argparse
import json
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, urlsplit


class Handler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"

    def send_body(self, body: bytes, content_type: str) -> None:
        self.send_response(200)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self) -> None:
        url = urlsplit(self.path)
        if url.path == "/hello":
            self.send_body(json.dumps({"greeting": "hello"}).encode(), "application/json")
        elif url.path == "/numbers":
            count = int(parse_qs(url.query).get("count", ["10"])[0])
            self.send_response(200)
            self.send_header("Content-Type", "text/plain")
            self.send_header("Transfer-Encoding", "chunked")
            self.end_headers()
            batch = 1000
            for start in range(0, count, batch):
                chunk = "".join(f"{n}\n" for n in range(start, min(start + batch, count))).encode()
                self.wfile.write(f"{len(chunk):x}\r\n".encode() + chunk + b"\r\n")
            self.wfile.write(b"0\r\n\r\n")
        else:
            self.send_error(404)

    def do_POST(self) -> None:
        if urlsplit(self.path).path != "/echo":
            self.send_error(404)
            return
        body = self.rfile.read(int(self.headers.get("Content-Length", "0")))
        self.send_body(body, self.headers.get("Content-Type", "application/octet-stream"))

    def log_message(self, format: str, *args: object) -> None:
        print(f"{self.address_string()} {format % args}", flush=True)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("port", type=int, nargs="?", default=8080)
    args = parser.parse_args()
    server = ThreadingHTTPServer(("127.0.0.1", args.port), Handler)
    print(f"listening on {args.port}", flush=True)
    server.serve_forever()


if __name__ == "__main__":
    main()

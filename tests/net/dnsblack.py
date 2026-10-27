#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.12"
# ///
"""A name server that receives queries on 127.0.0.1:53 over UDP and never answers, so that a
resolver pointed at it waits for its own timeouts.  Usage: dnsblack.py"""
import socket, time

s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
s.bind(("127.0.0.1", 53))
print("listening on 127.0.0.1:53 (udp)", flush=True)
t0 = time.monotonic()
while True:
    data, peer = s.recvfrom(4096)
    print(f"{1000 * (time.monotonic() - t0):10.1f} query of {len(data)} bytes from {peer}; ignored", flush=True)

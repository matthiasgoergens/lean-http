#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.12"
# ///
"""A local SYN blackhole: listens on ADDR:PORT with backlog 0, never accepts, and fills the accept
queue itself, so the kernel drops further SYNs and a client's connect hangs in SYN_SENT (as against
a firewalled address).  Verifies itself with a 1 s connect attempt.  Usage: blackhole.py ADDR PORT"""
import socket, sys, time
addr, port = sys.argv[1], int(sys.argv[2])
fam = socket.AF_INET6 if ":" in addr else socket.AF_INET
s = socket.socket(fam)
s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
if fam == socket.AF_INET6:
    s.setsockopt(socket.IPPROTO_IPV6, socket.IPV6_V6ONLY, 1)
s.bind((addr, port))
s.listen(0)
fillers = []
for i in range(4):
    c = socket.socket(fam)
    c.setblocking(False)
    try:
        c.connect((addr, port))
    except BlockingIOError:
        pass
    fillers.append(c)
time.sleep(0.5)
probe = socket.socket(fam)
probe.settimeout(1)
try:
    probe.connect((addr, port))
    print(f"blackhole {addr}:{port}: NOT working (connect succeeded)", flush=True)
except socket.timeout:
    print(f"blackhole {addr}:{port}: ok (connect timed out)", flush=True)
except Exception as e:
    print(f"blackhole {addr}:{port}: unexpected {e!r}", flush=True)
probe.close()
while True:
    time.sleep(3600)

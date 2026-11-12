# Q1 server.  Usage: srv1.py <port> <scenario: data|fin|rst|none> <act_delay_ms> [conns]
# Per connection: read b"ping", reply b"pong", wait act_delay, then act; log to stdout.
import socket, struct, sys, time, threading
port, scen, delay = int(sys.argv[1]), sys.argv[2], int(sys.argv[3])
conns = int(sys.argv[4]) if len(sys.argv) > 4 else 1
ls = socket.socket(); ls.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
ls.bind(("127.0.0.1", port)); ls.listen(16)
print("listening", port, flush=True)
def serve(c):
    c.settimeout(20)
    assert c.recv(4) == b"ping"
    c.sendall(b"pong")
    time.sleep(delay / 1000)
    if scen == "data":
        c.sendall(b"late-data"); print("server: sent data", flush=True)
        try: c.recv(1)
        except Exception as e: print("server: recv", e)
    elif scen == "fin":
        c.shutdown(socket.SHUT_WR); print("server: FIN", flush=True)
        try: c.recv(1)
        except Exception as e: print("server: recv", e)
    elif scen == "rst":
        c.setsockopt(socket.SOL_SOCKET, socket.SO_LINGER, struct.pack("ii", 1, 0))
        c.close(); print("server: RST", flush=True); return
    else:
        print("server: idle", flush=True)
        try: c.recv(1)
        except Exception as e: print("server: recv", e)
    c.close()
for _ in range(conns):
    c, _a = ls.accept()
    threading.Thread(target=serve, args=(c,), daemon=True).start()
time.sleep(float(sys.argv[5]) if len(sys.argv) > 5 else 30)

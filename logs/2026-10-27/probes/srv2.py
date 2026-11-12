# Q2 server.  Usage: srv2.py <port> <mode: none|data|fin|rst|flood> <delay_ms> <size> <nconns> <lifetime_s>
# Per connection: read b"ping", then after delay: data = send `size` bytes then keep open;
# fin = close after delay; rst = RST after delay; flood = keep sending `size` bytes (blocking) until peer goes;
# none = just hold the connection open.  Connections are held until the client closes or lifetime ends.
import socket, struct, sys, time, threading
port, mode, delay, size, nconns, life = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), float(sys.argv[6])
ls = socket.socket(); ls.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
ls.bind(("127.0.0.1", int(port))); ls.listen(16)
print("listening", port, flush=True)
def serve(c, i):
    c.settimeout(life)
    try:
        assert c.recv(4) == b"ping"
        time.sleep(delay / 1000)
        if mode == "data":
            c.sendall(b"x" * size); print(f"server[{i}]: sent {size}", flush=True)
        elif mode == "flood":
            n = 0
            try:
                while True: c.sendall(b"x" * size); n += size
            except Exception as e: print(f"server[{i}]: flood stopped after {n}: {e}", flush=True)
        elif mode == "fin":
            c.shutdown(socket.SHUT_WR); print(f"server[{i}]: FIN", flush=True)
        elif mode == "rst":
            c.setsockopt(socket.SOL_SOCKET, socket.SO_LINGER, struct.pack("ii", 1, 0)); c.close()
            print(f"server[{i}]: RST", flush=True); return
        else:
            print(f"server[{i}]: idle", flush=True)
        try:
            while c.recv(65536): pass
            print(f"server[{i}]: client closed", flush=True)
        except Exception as e: print(f"server[{i}]: recv {e}", flush=True)
    finally:
        c.close()
ls.settimeout(life)
for i in range(nconns):
    try: c, _a = ls.accept()
    except Exception: break
    threading.Thread(target=serve, args=(c, i), daemon=True).start()
time.sleep(life)

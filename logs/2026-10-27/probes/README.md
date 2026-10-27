# Std.Async.TCP probes (Lean v4.34.1), 2026-10-27

Run on the build host in `~/lean-http-probes/`, inside throwaway podman containers (image `localhost/b8perf-lean`, Lean v4.34.1 from the `b8perf-elan` volume, no network, loopback only; versions in `versions.txt`).  `./ctr.sh <cmd>` runs a command in the container, `./ctr.sh ./build.sh <name>` builds `<name>.lean` (`lean -c`, `leanc -O3`).  Servers are stdlib-only Python (`srv1.py`, `srv2.py`, uv CPython 3.14.8, `-I`).  Raw output is under `out/`; each `run-*.sh` header says which file it writes.  `trace-hang.sh`, `capture-hang.sh`, `poke-hang.sh` and `crash-hunt.sh` run the binary on the host (it is statically linked against Lean) so that host gdb can attach.

Source checked: the toolchain's `Std/Async/TCP.lean` and, for the runtime, `src/runtime/uv/tcp.cpp` and `event_loop.cpp` of `~/prog/lean-speed-client-review/wt-design` (3e6f42a58a).  `tcp.cpp` and `Std/Async/TCP.lean` there are identical to the `v4.34.1` tag; the runtime files that differ from the tag are `io.cpp`, `object.cpp` and `sharecommon.cpp` (reference-count details), none of them in the paths used here.

## Question 1: idle-socket check (`idle.lean`, `srv1.py`)

- `run-q1-all.sh` -> `out/q1-all.txt`: each scenario (server sends bytes, FIN, RST, nothing 50 ms after an exchange; client checks 400 ms later) with modes `once`, `loop`, `spaced`, `wait`, `ready`.
- `run-q1-first-all.sh` -> `out/q1-first.txt`: the first `tryFn` call on 100 fresh connections per scenario, 100 ms and 1000 ms after the server's action.
- `run-q1-latency.sh` -> `out/q1-latency.txt`: time from `waitReadable` to its promise resolving, 200 fresh connections per scenario.

## Question 2: exit hang

- `hang.lean` (variants documented in its header), `srv2.py`, `run-q2.sh` (one run, exit status 137 = still running at the limit).
- `run-q2-matrix.sh` -> `out/q2-matrix*`: server mode x server delay x variant, `run-q2-matrix2.sh` -> `out/q2-matrix2*` finer sweep around the race with the candidate fixes, `run-q2-loop.sh` -> `out/q2-loop*` body-reader loops over a flood, `run-q2-drop.sh` -> `out/q2-drop2*`.
- `capture-hang.sh` -> `out/hang1.txt`, `out/hang2.txt`: thread stacks, epoll registrations and socket queues of a hung process.  `poke-hang.sh` -> `out/poke1.txt`: waking the event loop does not release it.  `trace-hang.sh` with `trace.gdb` / `trace2.gdb` -> `out/trace*.txt`: breakpoint traces of the socket calls in good and hung runs.
- `prom.lean`, `run-prom.sh`, `run-prom-all.sh` -> `out/prom.txt`: the same hang with no sockets and no `Std.Async`.
- `crash-hunt.sh`, `segv.c`, `run-q2-drop-segv.sh`: attempts to catch the rare segfault described in the report (not caught).

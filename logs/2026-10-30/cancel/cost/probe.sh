#!/usr/bin/env bash
# Runs on the build host itself (perf needs the host's kernel), under batchrun, from ~/lean-http-cost:
# counts, per reused GET, how often each binary enters some functions of Lean's runtime (uprobes)
# and how often the kernel switches and wakes its threads and how many futex calls they make
# (tracepoints), for the whole client process.  Each binary makes <n1> and then <n2> calls through
# one client to evil.py's /ok, in <rounds> rounds that run the cells in random order; the count per
# call is (count at n2 - count at n1) / (n2 - n1), which takes out the process's start and end.
# Server on CPU <server cpu>, client on <client cpu>.  Adds the probes it needs (perf probe), and
# removes them at the end (event names must differ between binaries, hence the suffix).  Counts include a uprobe's own trap only in the kernel's instructions.
# Usage: probe.sh <rounds> <n1> <n2> <server cpu> <client cpu> <cell>...
set -u
rounds=$1 n1=$2 n2=$3 scpu=$4 ccpu=$5; shift 5
PY=$HOME/.local/share/uv/python/cpython-3.14.8-linux-x86_64-gnu/bin/python3
port=${PORT:-18341}
log=out/bench/probe-server-$port.log
funcs="lean_mark_mt lean_task_spawn_core lean_task_bind_core lean_task_map_core lean_io_promise_new
  lean_io_promise_resolve lean_io_basemutex_lock lean_st_ref_get lean_st_ref_set lean_st_ref_take"
cleanup() {
  kill $server 2>/dev/null; wait $server 2>/dev/null
  for c in "$@"; do sudo --non-interactive perf probe --quiet --del "cost_$c:*" 2>/dev/null; done
}
taskset --cpu-list "$scpu" "$PY" -I tests/net/evil.py --port "$port" > "$log" 2>&1 &
server=$!
trap 'cleanup "$@"' EXIT
for _ in $(seq 100); do grep --quiet listening "$log" && break; sleep 0.05; done
for c in "$@"; do
  sha256sum "out/bench/net-client-$c"
  # On a copy without debug information (objcopy --strip-debug: the same code), which perf probe
  # reads by symbol; with the debug information it finds none for these runtime functions.
  objcopy --strip-debug "out/bench/net-client-$c" "out/bench/probe-net-client-$c" || exit 1
  for f in $funcs; do
    sudo --non-interactive perf probe --quiet -x "out/bench/probe-net-client-$c" --add "cost_$c:${f}_$c=$f" || exit 1
  done
  sudo --non-interactive perf probe --list "cost_$c:*" 2>/dev/null
done
for r in $(seq 1 "$rounds"); do
  for c in $(printf '%s\n' "$@" | shuf); do
    events=sched:sched_switch,sched:sched_wakeup,syscalls:sys_enter_futex,instructions:u
    for f in $funcs; do events="$events,cost_$c:${f}_$c"; done
    for n in "$n1" "$n2"; do
      load=$(cut --delimiter=' ' --fields=1 /proc/loadavg)
      stat=$(sudo --non-interactive perf stat --field-separator=, --event="$events" -- \
          sudo --non-interactive --user="$(id -un)" taskset --cpu-list "$ccpu" "out/bench/probe-net-client-$c" call GET \
          "http://127.0.0.1:$port/ok" repeat="$n" trace=0 2>&1 >/dev/null \
        | awk -F, -v c="$c" '$3 != "" {sub(/^cost_[^:]*:/, "", $3); sub("_" c "$", "", $3); printf "%s=%s ", $3, $1}')
      echo "round=$r variant=$c calls=$n load=$load $stat"
    done
  done
done

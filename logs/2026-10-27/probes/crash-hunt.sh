#!/usr/bin/env bash
# On the box, host-side (see trace-hang.sh).  ./crash-hunt.sh <variant> <server-mode> <delay-ms> <size> <tries> <outfile>
# Runs bin/hang under gdb repeatedly; on SIGSEGV/SIGABRT prints all thread backtraces and stops.
cd "$HOME/lean-http-probes" || exit 1
variant=$1; smode=$2; sdelay=$3; size=$4; tries=$5; out=$6
py=$HOME/.local/share/uv/python/cpython-3.14.8-linux-x86_64-gnu/bin/python3
for i in $(seq "$tries"); do
  port=$((20000 + RANDOM % 20000))
  $py -I srv2.py "$port" "$smode" "$sdelay" "$size" 1 8 > /tmp/ch.$$ 2>&1 &
  sp=$!; sleep 0.3
  timeout --signal=KILL 15 gdb -batch -ex "set pagination off" -ex run -ex "thread apply all bt 25" -ex "info registers rip" --args ./bin/hang "$port" "$variant" 0 300 1 > /tmp/chg.$$ 2>&1
  if grep -q "received signal SIG" /tmp/chg.$$; then
    { echo "### try $i: crashed ($variant server=$smode delay=$sdelay)"; grep -v "^\[New\|^\[Thread\|^warning\|libthread_db\|^Using host" /tmp/chg.$$; } >> "$out"
    kill $sp 2>/dev/null; exit 0
  fi
  kill $sp 2>/dev/null; wait $sp 2>/dev/null
done
echo "no crash in $tries tries under gdb" >> "$out"

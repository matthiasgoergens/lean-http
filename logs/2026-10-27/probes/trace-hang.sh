#!/usr/bin/env bash
# On the box, directly on the host (the binary is statically linked against Lean; only libc is shared),
# so that host gdb can set breakpoints.  ./trace-hang.sh <server-mode> <delay-ms> <size> <variant> <hold-ms> <outfile>
cd "$HOME/lean-http-probes" || exit 1
smode=$1; sdelay=$2; size=$3; variant=$4; hold=$5; out=$6
py=$HOME/.local/share/uv/python/cpython-3.14.8-linux-x86_64-gnu/bin/python3
port=$((20000 + RANDOM % 20000))
$py -I srv2.py "$port" "$smode" "$sdelay" "$size" 1 15 > /tmp/trsrv.$$ 2>&1 &
sp=$!
sleep 0.3
{
echo "### trace server=$smode delay=$sdelay size=$size variant=$variant hold=$hold"
t0=$(date +%s%N)
timeout --signal=KILL 12 gdb -batch -x ${GDBSCRIPT:-trace.gdb} --args ./bin/hang "$port" "$variant" 0 "$hold" 1 2>&1 | grep -v "^\[New\|^\[Thread\|^warning\|^\[Inferior\|libthread_db\|^Using host"
echo "gdb exit=${PIPESTATUS[0]} wall=$(( ($(date +%s%N) - t0) / 1000000 ))ms"
cat /tmp/trsrv.$$ | sed 's/^/  [server] /'
} >> "$out" 2>&1
kill $sp 2>/dev/null

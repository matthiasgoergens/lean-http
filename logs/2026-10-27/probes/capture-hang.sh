#!/usr/bin/env bash
# On the box.  ./capture-hang.sh <server-mode> <delay-ms> <size> <variant> <hold-ms> <tries> <outfile>
# Repeats a run until the client is still alive 4 s after start, then dumps all thread stacks with gdb
# (host gdb, sudo) and /proc state, then kills it.  Output appended to <outfile>.
cd "$HOME/lean-http-probes" || exit 1
smode=$1; sdelay=$2; size=$3; variant=$4; hold=$5; tries=$6; out=$7
for i in $(seq "$tries"); do
  ./ctr.sh ./run-q2.sh "$smode" "$sdelay" "$size" "$variant" 0 "$hold" 1 15 > /tmp/cap.$$ 2>&1 &
  cp=$!
  sleep 4
  pid=$(pgrep --newest --full "bin/hang .* $variant ")
  if [ -n "$pid" ] && [ -d /proc/$pid ]; then
    {
    echo "### try $i: hang caught, pid $pid ($smode delay=$sdelay size=$size variant=$variant hold=$hold)"
    cat /tmp/cap.$$
    for t in /proc/$pid/task/*; do echo "task $(basename $t) $(cat $t/comm) wchan=$(sudo --non-interactive cat $t/wchan 2>/dev/null) state=$(grep State $t/status)"; done
    sudo --non-interactive gdb -batch -p "$pid" -ex "set pagination off" -ex "thread apply all bt" 2>&1 | grep -v "^\[New\|^warning\|Reading symbols"
    sudo --non-interactive ls -l /proc/$pid/fd 2>&1 | tail -n +2
    echo "--- epoll registrations (fdinfo of the eventpoll fd 3)"
    sudo --non-interactive grep -E "^tfd" /proc/$pid/fdinfo/3
    echo "--- sockets in the container's network namespace (ss -tn: Recv-Q/Send-Q)"
    sudo --non-interactive nsenter --target "$pid" --net ss -tn
    } >> "$out"
    sudo --non-interactive kill -9 "$pid"
    wait $cp; exit 0
  fi
  wait $cp
done
echo "no hang in $tries tries" >> "$out"

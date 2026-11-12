#!/usr/bin/env bash
# On the box.  ./poke-hang.sh <server-mode> <delay-ms> <size> <variant> <hold-ms> <tries> <outfile>
# Like capture-hang.sh, but once a hang is caught it writes 1 to the process's event-loop eventfd (fd 8,
# the uv_async_t wake-up) with gdb (call eventfd_write(8, 1)), which makes the loop thread run one more iteration
# without touching anything else, and records whether the process then exits by itself.
cd "$HOME/lean-http-probes" || exit 1
smode=$1; sdelay=$2; size=$3; variant=$4; hold=$5; tries=$6; out=$7
for i in $(seq "$tries"); do
  ./ctr.sh ./run-q2.sh "$smode" "$sdelay" "$size" "$variant" 0 "$hold" 1 15 > /tmp/poke.$$ 2>&1 &
  cp=$!
  sleep 3
  pid=$(pgrep --newest --full "bin/hang .* $variant ")
  if [ -n "$pid" ] && [ -d /proc/$pid ]; then
    {
    echo "### try $i: hang caught at +3 s, pid $pid ($smode delay=$sdelay size=$size variant=$variant hold=$hold)"
    echo "epoll tfds before: $(sudo --non-interactive grep -c '^tfd' /proc/$pid/fdinfo/3)"
    sudo --non-interactive grep -E "^tfd" /proc/$pid/fdinfo/3
    sudo --non-interactive ls -l /proc/$pid/fd/8
    sudo --non-interactive gdb -batch -p "$pid" -ex "call (int)eventfd_write(8, 1)" 2>&1 | grep -E '^\$'
    echo "wrote 1 to eventfd (fd 8) with gdb: call eventfd_write(8, 1)"
    sleep 1.5
    if [ -d /proc/$pid ]; then echo "process still alive 1.5 s after the poke"; sudo --non-interactive grep -E "^tfd" /proc/$pid/fdinfo/3; else echo "PROCESS EXITED after the poke"; fi
    } >> "$out"
    [ -d /proc/$pid ] && sudo --non-interactive kill -9 "$pid"
    wait $cp; cat /tmp/poke.$$ >> "$out"; exit 0
  fi
  wait $cp
done
echo "no hang in $tries tries" >> "$out"

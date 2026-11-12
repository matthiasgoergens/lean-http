# try-timers.sh HOGS N: one timers run with HOGS busy loops on the last CPU, timing it.
hogs=$1 n=$2 cpu=$(( $(nproc) - 1 ))
pids=()
for _ in $(seq "$hogs"); do taskset --cpu-list "$cpu" bash -c 'while :; do :; done' & pids+=($!); done
t0=${EPOCHREALTIME/[.,]/}
.lake/build/bin/net-client timers n="$n" hammer=4 pinloop="$cpu" | grep '^timers'
t1=${EPOCHREALTIME/[.,]/}
kill "${pids[@]}"; wait "${pids[@]}" 2>/dev/null
echo "hogs=$hogs n=$n took $(( (t1 - t0) / 1000 )) ms, loadavg $(cut -d' ' -f1 /proc/loadavg)"

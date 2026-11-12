#!/usr/bin/env bash
# starve.sh <cpus> <hogs> <command...>: runs <command> pinned to <cpus> alongside <hogs> busy loops
# pinned there too, so that every thread of the command waits behind them to be scheduled.
cpus=$1 hogs=$2; shift 2
pids=()
for _ in $(seq "$hogs"); do taskset --cpu-list "$cpus" bash -c 'while :; do :; done' & pids+=($!); done
taskset --cpu-list "$cpus" "$@"
rc=$?
kill "${pids[@]}" 2>/dev/null
wait 2>/dev/null
exit $rc

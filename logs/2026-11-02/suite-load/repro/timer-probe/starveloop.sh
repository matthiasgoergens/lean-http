#!/usr/bin/env bash
# starveloop.sh <cpu> <hogs> <command...>: runs <command> with <hogs> busy loops pinned to <cpu>; the
# command (timerprobe pinloop=<cpu>) pins its event loop's thread there, and its other threads run
# anywhere.
cpu=$1 hogs=$2; shift 2
pids=()
for _ in $(seq "$hogs"); do taskset --cpu-list "$cpu" bash -c 'while :; do :; done' & pids+=($!); done
"$@"
rc=$?
kill "${pids[@]}" 2>/dev/null
wait 2>/dev/null
exit $rc

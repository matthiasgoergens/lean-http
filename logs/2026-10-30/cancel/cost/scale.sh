#!/usr/bin/env bash
# Runs inside the build container (scripts/remote.sh), copied to out/bench/ first: <reps> blocks,
# each running cost-scale of every binary once (one repetition of every k, in random order) in
# random order, on CPU <cpu>.  Usage: scale.sh <reps> <cpu> <k list, comma-separated> <binary>...
set -u
reps=$1 cpu=$2 ks=$3; shift 3
for b in "$@"; do sha256sum "out/bench/cost-scale-$b"; done
for r in $(seq 1 "$reps"); do
  for b in $(printf '%s\n' "$@" | shuf); do
    taskset --cpu-list "$cpu" "out/bench/cost-scale-$b" 1 $(tr , ' ' <<< "$ks") \
      | sed "s/^rep=0 /block=$r variant=$b load=$(cut --delimiter=' ' --fields=1 /proc/loadavg) /"
  done
done

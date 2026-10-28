#!/usr/bin/env bash
# Cross-binary randomised blocks: in each block, main's codec-bench and the branch's run once each
# (one block of their own cells), in an order drawn from the block number, pinned to CPU 101.
# Prints obs lines prefixed with the binary.  Run inside the container from the branch tree.
blocks=${1:-30}
for b in $(seq 1 "$blocks"); do
  if [ $(( (b * 2654435761) % 7 )) -lt 4 ]; then order="main branch"; else order="branch main"; fi
  for w in $order; do
    if [ "$w" = main ]; then bin=out/main/.lake/build/bin/codec-bench; else bin=.lake/build/bin/codec-bench; fi
    taskset --cpu-list 101 "$bin" 1 "$b" | grep '^obs' | sed "s/^obs \([^ ]*\) 0 /obs $w-\1 $b /"
  done
done

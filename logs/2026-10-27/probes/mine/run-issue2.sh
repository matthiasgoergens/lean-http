#!/usr/bin/env bash
# Compiles issue2.lean (the program in the draft report, verbatim) and runs each variant 5 times, killing after 5 s.
cd /w || exit 1
lean --version
lean -c issue2.c issue2.lean || exit 1
leanc -O2 -o issue2 issue2.c || exit 1
for v in mapped direct mappedsync; do
  hangs=0
  for i in 1 2 3 4 5; do timeout 5 ./issue2 $v 2>/dev/null; [ $? -eq 124 ] && hangs=$((hangs+1)); done
  echo "$v: $hangs of 5 hung"
done

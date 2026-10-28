#!/usr/bin/env bash
# Compiles prom.lean with the lean on PATH, then runs mapped and direct 5 times each (main 50 ms,
# resolve 200 ms), killing a run after 5 s.
cd /w || exit 1
lean --version
lean -c prom.c prom.lean || exit 1
leanc -O2 -o prom prom.c || exit 1
for v in mapped direct; do
  hangs=0
  for i in 1 2 3 4 5; do
    timeout 5 ./prom $v 50 200 2>/dev/null; rc=$?
    [ $rc -eq 124 ] && hangs=$((hangs+1))
  done
  echo "$v: $hangs of 5 runs hung (killed after 5 s)"
done

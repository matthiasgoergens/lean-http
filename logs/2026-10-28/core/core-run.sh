#!/usr/bin/env bash
# Builds and runs the pure suites inside the container; writes out/<name>.txt for each.
mkdir --parents out || exit 1
lake build 2>&1 | tail -n 1
lake build unit-tests codec-tests core-tests 2>&1 | tail -n 1
run() { # run <name> <command...>
  local name=$1; shift
  local t0 t1 rc
  t0=$(date +%s%N)
  { echo "\$ $*"; "$@"; } > "out/$name.txt" 2>&1
  rc=$?
  t1=$(date +%s%N)
  echo "exit status $rc, wall $(( (t1 - t0) / 1000000 )) ms" >> "out/$name.txt"
  echo "$name: exit status $rc"
}
run unit .lake/build/bin/unit-tests
run codec .lake/build/bin/codec-tests
run traces .lake/build/bin/core-tests traces
for s in 1 2 3; do run props-seed$s .lake/build/bin/core-tests props 1000000 $s; done
for d in 10 12; do run explore-$d .lake/build/bin/core-tests explore $d; done

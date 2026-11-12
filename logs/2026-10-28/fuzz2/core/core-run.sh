#!/usr/bin/env bash
# Builds and runs the pure suites inside the container; writes out/<tag>/<name>.txt for each.
# Usage (inside the container, at the tree's root): bash out/core-run.sh <tag>
tag=${1:?tag}
mkdir --parents "out/$tag" || exit 1
lake build 2>&1 | tail -n 1
lake build unit-tests codec-tests core-tests 2>&1 | tail -n 1
run() { # run <name> <command...>
  local name=$1; shift
  local rc
  { echo "\$ $*"; "$@"; } > "out/$tag/$name.txt" 2>&1
  rc=$?
  echo "exit status $rc" >> "out/$tag/$name.txt"
  echo "$name: exit status $rc"
}
run unit .lake/build/bin/unit-tests
run codec .lake/build/bin/codec-tests
run traces .lake/build/bin/core-tests traces
for s in 1 2; do run props-seed$s .lake/build/bin/core-tests props 200000 $s; done
run explore-10 .lake/build/bin/core-tests explore 10

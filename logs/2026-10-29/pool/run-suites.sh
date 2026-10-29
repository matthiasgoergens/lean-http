#!/usr/bin/env bash
# Builds and runs the pure suites of the tree it is run from, inside the container; writes
# <outdir>/<name>.txt for each, with the command first and the exit status and wall time last.
#
# Usage (through scripts/remote.sh, from the tree to test): bash run-suites.sh <outdir>
out=${1:?usage: run-suites.sh <outdir>}
mkdir --parents "$out" || exit 1
run() { # run <name> <command...>
  local name=$1; shift
  local t0 t1 rc
  t0=$(date +%s%N)
  { echo "\$ $*"; "$@"; } > "$out/$name.txt" 2>&1
  rc=$?
  t1=$(date +%s%N)
  echo "exit status $rc, wall $(( (t1 - t0) / 1000000 )) ms" >> "$out/$name.txt"
  echo "$name: exit status $rc"
}
run build lake build
run build-tests lake build unit-tests codec-tests response-codec-tests core-tests codec-diff codec-bench net-client fuzz-replay pool-tests call-tests call-diff
run proof-axioms lake env lean scripts/proof-axioms.lean
run codec-axioms lake env lean scripts/codec-axioms.lean
run pool-axioms lake env lean scripts/pool-axioms.lean
run call-axioms lake env lean scripts/call-axioms.lean
run unit .lake/build/bin/unit-tests
run codec .lake/build/bin/codec-tests
run response-codec .lake/build/bin/response-codec-tests
run traces .lake/build/bin/core-tests traces
for s in 1 2; do run props-seed$s .lake/build/bin/core-tests props 200000 $s; done
run explore-10 .lake/build/bin/core-tests explore 10
for s in 1 2 3 4; do run diff-seed$s .lake/build/bin/codec-diff $s 60000 60000; done
run diff-control .lake/build/bin/codec-diff 1 20000 20000 control
# The comparison of random runs with the former core exists on the branch only.
if .lake/build/bin/core-tests compare 1 1 > /dev/null 2>&1; then
  for s in 1 2; do run compare-seed$s .lake/build/bin/core-tests compare 200000 $s; done
fi
run pool-traces .lake/build/bin/pool-tests traces
for s in 1 2; do run pool-props-seed$s .lake/build/bin/pool-tests props 200000 $s; done
run pool-explore-8 .lake/build/bin/pool-tests explore 8
run pool-control .lake/build/bin/pool-tests control 20000 1 7
# The per-call planner's suites, as its own runs had them (logs/2026-10-29/planner/run.sh).
run call-tests-seed1 .lake/build/bin/call-tests 20000 1
run call-tests-seed2 .lake/build/bin/call-tests 200000 2
run call-diff-seed1 .lake/build/bin/call-diff 3 1 20000
run call-diff-seed2 .lake/build/bin/call-diff 6 2 100000

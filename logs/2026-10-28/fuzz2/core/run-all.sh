#!/usr/bin/env bash
# Runs inside the container at the tree's root, with this file and core-run.sh in out/: a full
# build, the axioms of both proof sets, the exchange core's suites (core-run.sh), the codec's shapes
# and its differential test against the core.
# Usage: bash out/run-all.sh <tag>
tag=${1:?tag}
mkdir --parents "out/$tag" || exit 1
run() { # run <name> <command...>
  local name=$1; shift
  local rc
  { echo "\$ $*"; "$@"; } > "out/$tag/$name.txt" 2>&1
  rc=$?
  echo "exit status $rc" >> "out/$tag/$name.txt"
  echo "$name: exit status $rc"
}
run build lake build
run axioms lake env lean scripts/proof-axioms.lean
run codec-axioms lake env lean scripts/codec-axioms.lean
bash out/core-run.sh "$tag"
lake build response-codec-tests codec-diff 2>&1 | tail -n 1
run shapes-codec .lake/build/bin/response-codec-tests
for s in 1 2 3 4; do run diff-seed$s .lake/build/bin/codec-diff $s 60000 60000; done
run diff-control .lake/build/bin/codec-diff 1 20000 20000 control

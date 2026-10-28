#!/usr/bin/env bash
# Builds and runs the response codec's checks inside the container; writes out/<tag>/<name>.txt for each.
# Usage (inside the container, at the tree's root): bash out/codec-run.sh <tag>
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
run axioms lake env lean scripts/codec-axioms.lean
lake build codec-tests response-codec-tests codec-diff codec-bench 2>&1 | tail -n 1
run shapes-core .lake/build/bin/codec-tests
run shapes-codec .lake/build/bin/response-codec-tests
for s in 1 2 3 4; do run diff-seed$s .lake/build/bin/codec-diff $s 60000 60000; done
run diff-control .lake/build/bin/codec-diff 1 20000 20000 control
run bench taskset --cpu-list 101 .lake/build/bin/codec-bench 100 1

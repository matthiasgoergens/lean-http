#!/usr/bin/env bash
# The runs behind the per-call planner, from scratch (no .lake).  scripts/remote.sh does not copy
# logs/, so the script goes on stdin:
#   LEAN_HTTP_REMOTE_DIR=lean-http-planner CTR_EXTRA=-i scripts/remote.sh bash -s < logs/2026-10-29/planner/run.sh
#   rsync --archive buildhost:lean-http-planner/out/planner/ logs/2026-10-29/planner/
# Each output goes to out/planner/<name>.txt, starting with the command that made it.
mkdir -p out/planner || exit 1
run() {
  local name=$1; shift
  { echo "\$ $*"; "$@" 2>&1; echo "exit status $?"; } > "out/planner/$name.txt"
}
rm -rf .lake || exit 1
run build lake build
run build-tests lake build call-tests call-diff unit-tests
run axioms lake env lean scripts/call-axioms.lean
run unit .lake/build/bin/unit-tests
run call-tests-seed1 .lake/build/bin/call-tests 20000 1
run call-tests-seed2 .lake/build/bin/call-tests 200000 2
run call-diff-seed1 .lake/build/bin/call-diff 3 1 20000
run call-diff-seed2 .lake/build/bin/call-diff 6 2 100000

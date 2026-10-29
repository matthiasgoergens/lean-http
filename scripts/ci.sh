#!/usr/bin/env bash
# The checks CI runs, in order; .github/workflows/ci.yml calls this, and it runs the same anywhere
# with elan (or a toolchain's lake) on the PATH and python3, for example on the build host:
#
#   CTR_EXTRA='--sysctl net.ipv4.tcp_syn_retries=2' scripts/remote.sh bash scripts/ci.sh
#
# Usage: scripts/ci.sh [stage...]   (default: every stage, in this order)
#   vendor     generate vendor/, the upstream protocol layer the oracle tests compare with, unless it
#              is there at the commit scripts/vendor.sh names: from $LEAN4_CLONE if that has the
#              commit, else from a shallow, partial fetch of github.com/leanprover/lean4 (network)
#   build      lake build (every proof), failing on any warning or `sorry`; then the test executables
#   axioms     scripts/check-axioms.py on the four axiom scripts, after a control that must fail
#   pure       the suites that need no sockets, in modest sizes: unit, codec, response-codec, the
#              exchange core's traces, props, explore and compare, the pool's and the planner's
#              suites, codec-diff with its control, and the fuzzing seeds through fuzz-replay
#   examples   build examples/ (a package that requires this one) and run it against examples/server.py,
#              and check that every Lean block of README.md is in an example
#   net        the real-socket suite, tests/net/run.sh, which skips what the environment cannot run
#
# Each step writes <out>/<step>.txt (the command first, the exit status and wall time last); the
# real-socket suite writes out/net/ as well.  <out> is $CI_OUT, default out/ci.  A failed build ends
# the run; any other failed step fails it at the end.  Never changes system state: the CI workflow
# sets the sysctl and the names the real-socket suite wants before calling this.

root=$(cd "$(dirname "$0")/.." && pwd) || exit 1
cd "$root" || exit 1
out=${CI_OUT:-$root/out/ci}
mkdir --parents "$out" || exit 1
if [ -z "${PY:-}" ]; then
  if [ -x /py/bin/python3 ]; then PY=/py/bin/python3; else PY=python3; fi
fi
export PY
bin=$root/.lake/build/bin
failed=()

# step <name> <command...>: run a command, its output to <out>/<name>.txt.
step() {
  local name=$1; shift
  local t0 t1 rc
  t0=$(date +%s%N)
  { echo "\$ $*"; "$@"; } > "$out/$name.txt" 2>&1
  rc=$?
  t1=$(date +%s%N)
  echo "exit status $rc, wall $(( (t1 - t0) / 1000000 )) ms" >> "$out/$name.txt"
  if [ $rc -eq 0 ]; then
    echo "ok   $name ($(( (t1 - t0) / 1000000 )) ms)"
  else
    echo "FAIL $name (exit status $rc); the end of $out/$name.txt:"
    tail --lines=30 "$out/$name.txt" | sed 's/^/     /'
    failed+=("$name")
  fi
  return $rc
}

# no_match <file> <extended regex> <what>: fails, showing the lines, if the regex matches.
no_match() {
  if grep --extended-regexp "$2" "$1"; then
    echo "found $3 in $1"
    return 1
  fi
}

stage_vendor() {
  local commit clone
  commit=$(sed --quiet 's/^commit=//p' scripts/vendor.sh)
  if grep --quiet --fixed-strings "$commit" vendor/SOURCE 2>/dev/null; then
    echo "ok   vendor (vendor/ is at $commit)"
    return 0
  fi
  clone=${LEAN4_CLONE:-}
  if [ -n "$clone" ] && git -C "$clone" cat-file -e "$commit^{commit}" 2>/dev/null; then
    step vendor scripts/vendor.sh "$clone"
    return
  fi
  clone=$(mktemp --directory) || return 1
  step vendor-fetch fetch_lean4 "$clone" "$commit" \
    && step vendor scripts/vendor.sh "$clone"
  local rc=$?
  rm --recursive --force "$clone"
  return $rc
}

# fetch_lean4 <dir> <commit>: the commit's trees only, at depth 1; vendor.sh reads the few files it
# needs, which git then fetches on demand.  The commit is the head of leanprover/lean4 PR 14548;
# should GitHub not serve it by name, it is fetched through the PR's ref.
fetch_lean4() {
  local url=https://github.com/leanprover/lean4
  git -C "$1" init --quiet || return 1
  git -C "$1" remote add origin "$url" || return 1
  git -C "$1" fetch --depth 1 --filter=blob:none origin "$2" \
    || git -C "$1" fetch --depth 1 --filter=blob:none origin "refs/pull/14548/head" || return 1
  git -C "$1" cat-file -e "$2^{commit}"
}

lake_build_clean() { # lake build <targets>, failing on a warning or `sorry` in its output
  local log=$out/.lake-build-$$.txt
  lake build "$@" 2>&1 | tee "$log"
  local rc=${PIPESTATUS[0]}
  if [ "$rc" -eq 0 ]; then
    no_match "$log" "sorry|warning" "a warning or a sorry" || rc=1
  fi
  rm --force "$log"
  return "$rc"
}

stage_build() {
  step toolchain bash -c 'command -v lake && lake --version && lean --version && cat lean-toolchain' || return 1
  step build lake_build_clean || return 1
  step build-tests lake_build_clean unit-tests codec-tests response-codec-tests core-tests codec-diff \
    pool-tests call-tests call-diff fuzz-replay net-client
}

stage_axioms() {
  local control
  control=$(mktemp --directory) || return 1
  cat > "$control/Control.lean" <<'EOF'
axiom extra : False
theorem viaSorry : 1 = 2 := sorry
theorem viaAxiom : 1 = 2 := extra.elim
theorem clean : 1 + 1 = 2 := rfl
#print axioms viaSorry
#print axioms viaAxiom
#print axioms clean
EOF
  # The checker must see a sorry and a foreign axiom, or its silence on the real scripts means nothing.
  step axioms-control axioms_control "$control/Control.lean"
  rm --recursive --force "$control"
  step axioms "$PY" -I scripts/check-axioms.py scripts/proof-axioms.lean scripts/codec-axioms.lean \
    scripts/pool-axioms.lean scripts/call-axioms.lean
}

axioms_control() {
  local result
  result=$("$PY" -I scripts/check-axioms.py "$1")
  local rc=$?
  echo "$result"
  [ $rc -ne 0 ] \
    && grep --quiet --fixed-strings "viaSorry depends on ['sorryAx']" <<< "$result" \
    && grep --quiet --fixed-strings "viaAxiom depends on ['extra']" <<< "$result" \
    && ! grep --quiet --fixed-strings "clean depends" <<< "$result"
}

# codec_diff <args...>: codec-diff classifies disagreements without failing; here a disagreement of
# the codec with itself when cut, of the exchange core with the codec, of a request encoding, or one
# no known difference explains, fails.
codec_diff() {
  local log=$out/.codec-diff-$$.txt rc
  "$bin/codec-diff" "$@" | tee "$log"
  rc=${PIPESTATUS[0]}
  [ "$rc" -eq 0 ] && no_match "$log" '^== (CODEC|CORE|REQUEST)|UNEXPLAINED' "a disagreement that must not occur" \
    || rc=1
  rm --force "$log"
  return "$rc"
}

# The control plants an off-by-one in the codec's limits: codec-diff must find disagreements that
# nothing explains.
codec_diff_control() {
  local log=$out/.codec-diff-control-$$.txt rc
  "$bin/codec-diff" "$@" control | tee "$log"
  rc=${PIPESTATUS[0]}
  [ "$rc" -eq 0 ] && grep --quiet 'UNEXPLAINED' "$log" || { echo "the planted bug went unseen"; rc=1; }
  rm --force "$log"
  return "$rc"
}

fuzz_seeds() {
  local dir rc
  dir=$(mktemp --directory) || return 1
  "$PY" -I fuzz/seeds.py "$dir" && "$bin/fuzz-replay" --brief "$dir"/*
  rc=$?
  echo "$(find "$dir" -type f | wc --lines) seeds"
  rm --recursive --force "$dir"
  return $rc
}

stage_pure() {
  step unit "$bin/unit-tests"
  step codec "$bin/codec-tests"
  step response-codec "$bin/response-codec-tests"
  step core-traces "$bin/core-tests" traces
  step core-props "$bin/core-tests" props 50000 1
  step core-explore "$bin/core-tests" explore 10
  step core-compare "$bin/core-tests" compare 20000 1
  step pool-traces "$bin/pool-tests" traces
  step pool-props "$bin/pool-tests" props 20000 1
  step pool-explore "$bin/pool-tests" explore 8
  step pool-control "$bin/pool-tests" control 20000 1 7
  step call-tests "$bin/call-tests" 20000 1
  step call-diff "$bin/call-diff" 3 1 20000
  step codec-diff codec_diff 1 10000 10000
  step codec-diff-control codec_diff_control 1 5000 5000
  step fuzz-seeds fuzz_seeds
}

stage_examples() {
  step readme-blocks "$PY" -I scripts/check-readme.py README.md examples
  step examples bash examples/run.sh
}

stage_net() {
  step net bash tests/net/run.sh
}

stages=("$@")
[ ${#stages[@]} -gt 0 ] || stages=(vendor build axioms pure examples net)
for s in "${stages[@]}"; do
  case $s in
    vendor) stage_vendor || { echo "the vendored layer is missing; stopping"; exit 1; } ;;
    build) stage_build || { echo "the build failed; stopping"; exit 1; } ;;
    axioms) stage_axioms ;;
    pure) stage_pure ;;
    examples) stage_examples ;;
    net) stage_net ;;
    *) echo "unknown stage $s; the stages are vendor build axioms pure examples net" >&2; exit 2 ;;
  esac
done
if [ ${#failed[@]} -gt 0 ]; then
  echo "failed: ${failed[*]}"
  exit 1
fi
echo "every step passed"

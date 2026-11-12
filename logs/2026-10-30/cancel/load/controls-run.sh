#!/usr/bin/env bash
# Positive controls for the checks added with cancellation and with the lookups of a call: each
# planted defect (mutate.py) on the committed tree (HEAD), built and run on the build host in a
# directory of its own (directly, not through scripts/remote.sh, which would copy the working tree
# over it), against the checks that should see it.  Prints each check's verdict lines.
# A copy of ../controls/run.sh with a directory of its own on the build host, for the scenarios placed
# at a stage of the call (branch cancel-flake).
# Usage: controls-run.sh [mutation...]   (default: none, then every mutation)
set -u
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../../.." && pwd)
host=$(head -n 1 "$root/.build-host")
dir=lean-http-flake-ctl
ctr() { # ctr <command>
  ssh "$host" "cd ~/$dir && batchrun podman --cgroup-manager=cgroupfs run --cgroups=disabled --rm --network none --sysctl net.ipv4.tcp_syn_retries=2 -v b8perf-elan:/root/.elan:ro -v \"\$PWD\":/w -w /w -v /home/matthias/.local/share/uv/python/cpython-3.14.8-linux-x86_64-gnu:/py:ro localhost/b8perf-lean env PATH=/root/.elan/toolchains/leanprover--lean4---v4.34.1/bin:/usr/local/bin:/usr/bin:/bin bash -c '$1'"
}
# What each mutation is checked against.
declare -A checks=(
  [core-cancel-ignored]=core [core-cancel-finishes]=core [core-cancel-cause]=core
  [planner-retries-cancelled]=planner [trace-any-failure]=unit
  [shell-no-watch]="net cancel-before cancel-head"
  [shell-no-mailbox]="net cancel-head cancel-body cancel-upload"
  [shell-abandon-drains]="net cancel-body cancel-steps"
  [shell-sleep-uncancellable]="net cancel-backoff"
  [shell-handshake-uncancellable]="net cancel-tls"
  [shell-connect-uncancellable]="net cancel-connect"
  [shell-cap-uncancellable]="net cancel-cap"
  [shell-checks-signal-only]="unit+net shutdown cancel-cap"
  [stream-hands-out-held]="net cancel-body"
  [cancel-keeps-last-bell]=unit
  [shutdown-no-table]="net shutdown"
  [lookup-every-round]="net dns-once"
)
echo "HEAD $(git -C "$root" rev-parse --short HEAD)"
names=("$@")
[ ${#names[@]} -gt 0 ] || names=(none core-cancel-ignored core-cancel-finishes core-cancel-cause planner-retries-cancelled trace-any-failure shell-no-watch shell-no-mailbox shell-abandon-drains shell-sleep-uncancellable shell-handshake-uncancellable shell-connect-uncancellable shell-cap-uncancellable shell-checks-signal-only stream-hands-out-held cancel-keeps-last-bell shutdown-no-table lookup-every-round)
for m in "${names[@]}"; do
  tree=$(mktemp --directory)
  git -C "$root" archive HEAD | tar --extract --directory "$tree"
  cp -r "$root/vendor" "$tree/vendor"
  [ "$m" = none ] || (cd "$tree" && "$here/../controls/mutate.py" "$m") || exit 1
  rsync --archive --delete --exclude .lake --exclude out "$tree/" "$host:$dir/" || exit 1
  rm --recursive --force "$tree"
  echo "### $m"
  what=${checks[$m]:-all}
  case $what in
    core|all) ctr 'lake build core-tests 2>&1 | grep -E "error|^Build" | head -3
      for s in "traces" "props 50000 1" "explore 10"; do
        echo "core-tests $s: $(.lake/build/bin/core-tests $s 2>&1 | grep -E "^(FAIL|PASS [0-9]|[0-9]+ (traces|searches))" | head -2 | tr "\n" " " | cut -c1-300)"
      done' ;;
  esac
  case $what in
    planner|all) ctr 'lake build call-tests 2>&1 | grep -E "error|^Build" | head -3
      .lake/build/bin/call-tests 20000 1 2>&1 | grep -E "^FAIL|violation|checks," | head -6' ;;
  esac
  case $what in
    unit|unit+net*|all) ctr 'lake build unit-tests 2>&1 | grep -E "error|^Build" | head -3
      .lake/build/bin/unit-tests 2>&1 | grep -E "^FAIL|checks," | head -6' ;;
  esac
  case $what in
    net*|unit+net*) what=${what#unit+}; ctr "lake build net-client 2>&1 | grep -E \"error|^Build\" | head -3
      bash tests/net/run.sh ${what#net } 2>&1 | grep -E \"^(FAIL|###)\" | cut -c1-300" ;;
    all) ctr "lake build net-client 2>&1 | grep -E \"error|^Build\" | head -3
      bash tests/net/run.sh cancel-before cancel-head cancel-body cancel-upload cancel-tls cancel-backoff cancel-connect cancel-cap shutdown dns-once 2>&1 | grep -E \"^(FAIL|###)\" | cut -c1-300" ;;
  esac
done
echo done

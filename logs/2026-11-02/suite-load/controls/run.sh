#!/usr/bin/env bash
# Positive controls for the checks changed to hold under load: each planted defect (mutate.py) on the
# committed tree (HEAD), built and run on the build host in a directory of its own (directly, not
# through scripts/remote.sh, which would copy the working tree over it), against the checks that
# should see it.  Prints each run's verdicts: every FAIL, KNOWN and SKIP line, and the summary.
# Usage: run.sh [mutation...]   (default: none, then every mutation)
set -u
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../../.." && pwd)
host=$(head -n 1 "$root/.build-host")
dir=lean-http-load-ctl
ctr() { # ctr <command>
  ssh "$host" "cd ~/$dir && echo \"loadavg \$(cat /proc/loadavg)\" && batchrun podman --cgroup-manager=cgroupfs run --cgroups=disabled --rm --network none --sysctl net.ipv4.tcp_syn_retries=2 -v b8perf-elan:/root/.elan:ro -v \"\$PWD\":/w -w /w -v /home/matthias/.local/share/uv/python/cpython-3.14.8-linux-x86_64-gnu:/py:ro localhost/b8perf-lean env PATH=/root/.elan/toolchains/leanprover--lean4---v4.34.1/bin:/usr/local/bin:/usr/bin:/bin bash -c '$1'"
}
# What each mutation is checked against: unit, and the real-socket scenarios after net.
declare -A checks=(
  [none]="unit net refused-backoff blackhole-timeout deadline-trickle deadline-interim read-gap connect-deadline early-response concurrency retry-after stream-abandon upload-early upload-exit tls-handshake tls-stream timers get"
  [exit-delay]="net get post"
  [timer-early-unfixed]="unit net timers"
  [deadline-late]="net deadline-trickle deadline-interim connect-deadline stream-abandon upload-exit tls-handshake tls-stream"
  [gap-late]="net read-gap"
  [handshake-late]="net tls-handshake"
  [handshake-early]="net tls-handshake"
  [connect-late]="net blackhole-timeout"
  [retry-wait-double]="net refused-backoff retry-after"
  [retry-wait-none]="net refused-backoff retry-after"
  [notime-ignored]="net refused-backoff"
  [cap-one-less]="net concurrency"
  [drain-longer]="net stream-abandon"
  [drain-zero]="net stream-abandon"
  [race-waits-read]="net stream-abandon tls-stream"
  [helper-missing]="net stream-abandon"
)
echo "HEAD $(git -C "$root" rev-parse --short HEAD)"
names=("$@")
[ ${#names[@]} -gt 0 ] || names=(none exit-delay timer-early-unfixed deadline-late gap-late handshake-late handshake-early connect-late retry-wait-double retry-wait-none notime-ignored cap-one-less drain-longer drain-zero race-waits-read helper-missing)
for m in "${names[@]}"; do
  tree=$(mktemp --directory)
  git -C "$root" archive HEAD | tar --extract --directory "$tree"
  cp -r "$root/vendor" "$tree/vendor"
  [ "$m" = none ] || (cd "$tree" && "$here/mutate.py" "$m") || exit 1
  rsync --archive --delete --exclude .lake --exclude out "$tree/" "$host:$dir/" || exit 1
  rm --recursive --force "$tree"
  echo "### $m"
  what=${checks[$m]}
  case $what in
    unit*) ctr 'lake build unit-tests 2>&1 | grep -E "error|^Build" | head -3
      .lake/build/bin/unit-tests 2>&1 | grep -E "^FAIL|checks," | head -8' ;;
  esac
  case $what in
    *net*) scenarios=${what#*net }; ctr "lake build net-client 2>&1 | grep -E \"error|^Build\" | head -3
      bash tests/net/run.sh $scenarios 2>&1 | grep -E \"^(FAIL|KNOWN|SKIP|###)\" | cut -c1-300" ;;
  esac
done
echo done

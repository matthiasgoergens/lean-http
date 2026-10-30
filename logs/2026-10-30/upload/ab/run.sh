#!/usr/bin/env bash
# The real-socket scenarios that failed in a CI run of this branch under load (keepalive-close,
# concurrency-cap, redispatch-refused, retry-503, retry-429-date, redispatch-408,
# tls-hang-deadline, tls12-close-delimited; and stream-drain, of the scenario stream-abandon, in the
# next run), run on main and on this branch in alternation, rounds
# times, each tree in its own directory on the build host (built and run directly, not through
# scripts/remote.sh, which copies the working tree).  Prints each run's summary line and failures,
# with the load average before it.
set -u
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../../.." && pwd)
host=$(head -n 1 "$root/.build-host")
rounds=${1:-3}
scen="stream-abandon keepalive-close concurrency redispatch-refused retry-after redispatch-408 tls-handshake tls-12"
ctr() { # ctr <dir> <command>
  ssh "$host" "cd ~/$1 && batchrun podman --cgroup-manager=cgroupfs run --cgroups=disabled --rm --network none --sysctl net.ipv4.tcp_syn_retries=2 -v b8perf-elan:/root/.elan:ro -v \"\$PWD\":/w -w /w -v /home/matthias/.local/share/uv/python/cpython-3.14.8-linux-x86_64-gnu:/py:ro localhost/b8perf-lean env PATH=/root/.elan/toolchains/leanprover--lean4---v4.34.1/bin:/usr/local/bin:/usr/bin:/bin bash -c '$2'"
}
for t in main HEAD; do
  tree=$(mktemp --directory)
  git -C "$root" archive "$t" | tar --extract --directory "$tree"
  cp -r "$root/vendor" "$tree/vendor"
  echo "### $t = $(git -C "$root" rev-parse --short "$t")"
  rsync --archive --delete --exclude .lake "$tree/" "$host:lean-http-upload-ab-$t/" || exit 1
  rm --recursive --force "$tree"
  ctr lean-http-upload-ab-$t 'lake build net-client 2>&1 | tail -1' || exit 1
done
for k in $(seq "$rounds"); do
  for t in main HEAD; do
    echo "--- round $k $t, load $(ssh "$host" cat /proc/loadavg)"
    ctr lean-http-upload-ab-$t "bash tests/net/run.sh $scen 2>&1 | grep -E \"^(FAIL|###)\""
  done
done

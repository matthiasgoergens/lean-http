#!/usr/bin/env bash
# Follow-up to run.sh: the same upload with the call's record on (net-client's default, trace=1, as
# in tests/net/run.sh) and off (trace=0), in the variants run.sh built, three runs each, alternating.
set -u
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../../.." && pwd)
host=$(head -n 1 "$root/.build-host")
for k in 1 2 3; do
  for v in result index mailbox; do
    for t in 1 0; do
      ssh "$host" "cd ~/lean-http-upload-rss-$v && batchrun podman --cgroup-manager=cgroupfs run --cgroups=disabled --rm --network none -v b8perf-elan:/root/.elan:ro -v \"\$PWD\":/w -w /w -v /home/matthias/.local/share/uv/python/cpython-3.14.8-linux-x86_64-gnu:/py:ro localhost/b8perf-lean bash -c '/py/bin/python3 -I tests/net/upload.py 18131 > /tmp/u.log 2>&1 & sleep 1; .lake/build/bin/net-client upload PUT http://127.0.0.1:18131/sink size=268435456 chunk=16384 deadline=600000 trace=$t | grep -E \"rss_peak\"'" | sed "s/^/$v trace=$t run $k: /"
    done
  done
done

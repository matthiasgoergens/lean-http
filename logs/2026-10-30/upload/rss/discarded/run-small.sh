#!/usr/bin/env bash
# Follow-up to run.sh: the variants it built, with 1 KiB chunks (262144 pulls for 256 MiB), where
# anything kept per chunk shows; two runs each, alternating, the call's record off.
set -u
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../../.." && pwd)
host=$(head -n 1 "$root/.build-host")
for k in 1 2; do
  for v in result index mailbox; do
    ssh "$host" "cd ~/lean-http-upload-rss-$v && batchrun podman --cgroup-manager=cgroupfs run --cgroups=disabled --rm --network none -v b8perf-elan:/root/.elan:ro -v \"\$PWD\":/w -w /w -v /home/matthias/.local/share/uv/python/cpython-3.14.8-linux-x86_64-gnu:/py:ro localhost/b8perf-lean bash -c '/py/bin/python3 -I tests/net/upload.py 18131 > /tmp/u.log 2>&1 & sleep 1; .lake/build/bin/net-client upload PUT http://127.0.0.1:18131/sink size=268435456 chunk=1024 deadline=600000 trace=0 | grep -E \"^upload call|rss_peak\" | cut -c1-60,200-'" | sed "s/^/$v run $k: /"
  done
done

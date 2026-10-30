#!/usr/bin/env bash
# Follow-up to run.sh: the variants' own tests/net/run.sh upload-big scenario (each run writes its
# output to a file, as the suite does), two runs each, alternating; then the same for the tree as it
# is now on the build host (~/lean-http-upload, write-first race order and main's awaitFirst).
set -u
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../../.." && pwd)
host=$(head -n 1 "$root/.build-host")
for k in 1 2; do
  for v in rss-result rss-index rss-mailbox rss-first-result; do
    ssh "$host" "cd ~/lean-http-upload-$v && batchrun podman --cgroup-manager=cgroupfs run --cgroups=disabled --rm --network none -v b8perf-elan:/root/.elan:ro -v \"\$PWD\":/w -w /w -v /home/matthias/.local/share/uv/python/cpython-3.14.8-linux-x86_64-gnu:/py:ro localhost/b8perf-lean bash -c 'bash tests/net/run.sh upload-big > /dev/null 2>&1; grep -h rss_peak out/net/upload-big.txt out/net/upload-big-chunked.txt'" | sed "s/^/$v run $k: /"
  done
done

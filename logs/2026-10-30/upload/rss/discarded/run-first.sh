#!/usr/bin/env bash
# Follow-up to run.sh: the tree of the first measurement (commit be4dd1f, which added the upload
# scenarios together with the change of awaitFirst) with and without that change of
# LeanHttp/Wait.lean, three runs each, alternating, with the call's record on as in run.sh.
set -u
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../../.." && pwd)
host=$(head -n 1 "$root/.build-host")
for v in first-result first-index; do
  tree=$(mktemp --directory)
  git -C "$root" archive be4dd1f | tar --extract --directory "$tree"
  cp -r "$root/vendor" "$tree/vendor"
  [ $v = first-result ] && git -C "$root" show db37391:LeanHttp/Wait.lean > "$tree/LeanHttp/Wait.lean"
  cp "$root/.build-host" "$tree/"
  echo "### variant $v: $(cd "$tree" && sha256sum LeanHttp/Body.lean LeanHttp/Wait.lean | tr '\n' ' ')"
  rsync --archive --delete --exclude .lake "$tree/" "$host:lean-http-upload-rss-$v/" || exit 1
  rm --recursive --force "$tree"
  LEAN_HTTP_REMOTE_DIR=lean-http-upload-rss-$v "$root/scripts/remote.sh" bash -c 'lake build net-client 2>&1 | tail -1' || exit 1
done
for k in 1 2 3; do
  for v in first-result first-index; do
    ssh "$host" "cd ~/lean-http-upload-rss-$v && batchrun podman --cgroup-manager=cgroupfs run --cgroups=disabled --rm --network none -v b8perf-elan:/root/.elan:ro -v \"\$PWD\":/w -w /w -v /home/matthias/.local/share/uv/python/cpython-3.14.8-linux-x86_64-gnu:/py:ro localhost/b8perf-lean bash -c '/py/bin/python3 -I tests/net/upload.py 18131 > /tmp/u.log 2>&1 & sleep 1; .lake/build/bin/net-client upload PUT http://127.0.0.1:18131/sink size=268435456 chunk=16384 deadline=600000 | grep -E \"^upload call|rss_peak\" | cut -c1-60,200-'" | sed "s/^/$v run $k: /"
  done
done

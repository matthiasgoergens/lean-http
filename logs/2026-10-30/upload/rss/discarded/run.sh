#!/usr/bin/env bash
# Peak resident memory of a 256 MiB streamed upload in 16 KiB chunks, for three versions of the
# shell's wait (run from the repository root on the laptop; builds and runs on the build host):
#   result   awaitFirst resolves its promise with the winner's result (as on main), Live.next races
#            the read, the write and the pull with awaitFirst
#   index    awaitFirst resolves with the winner's index; Live.next as in `result`
#   mailbox  the change as committed: each operation reports to the exchange's mailbox once
# Each variant is the committed tree with LeanHttp/Body.lean and LeanHttp/Wait.lean taken from the
# commits named below, built in its own directory on the build host.  Three runs each, alternating.
set -u
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../../.." && pwd)
host=$(head -n 1 "$root/.build-host")
pre_mailbox=929928b   # Body.lean before the mailbox (Live.next races with awaitFirst)
main=db37391          # Wait.lean as on main
for v in result index mailbox; do
  tree=$(mktemp --directory)
  git -C "$root" archive HEAD | tar --extract --directory "$tree"
  cp -r "$root/vendor" "$tree/vendor"
  case $v in
    result) git -C "$root" show $pre_mailbox:LeanHttp/Body.lean > "$tree/LeanHttp/Body.lean"
            git -C "$root" show $main:LeanHttp/Wait.lean > "$tree/LeanHttp/Wait.lean" ;;
    index) git -C "$root" show $pre_mailbox:LeanHttp/Body.lean > "$tree/LeanHttp/Body.lean" ;;
    mailbox) ;;
  esac
  cp "$root/.build-host" "$tree/"
  echo "### variant $v: $(cd "$tree" && sha256sum LeanHttp/Body.lean LeanHttp/Wait.lean | tr '\n' ' ')"
  rsync --archive --delete --exclude .lake "$tree/" "$host:lean-http-upload-rss-$v/" || exit 1
  rm --recursive --force "$tree"
  LEAN_HTTP_REMOTE_DIR=lean-http-upload-rss-$v "$root/scripts/remote.sh" bash -c 'lake build net-client 2>&1 | tail -1' || exit 1
done
for k in 1 2 3; do
  for v in result index mailbox; do
    ssh "$host" "cd ~/lean-http-upload-rss-$v && batchrun podman --cgroup-manager=cgroupfs run --cgroups=disabled --rm --network none -v b8perf-elan:/root/.elan:ro -v \"\$PWD\":/w -w /w -v /home/matthias/.local/share/uv/python/cpython-3.14.8-linux-x86_64-gnu:/py:ro localhost/b8perf-lean bash -c '/py/bin/python3 -I tests/net/upload.py 18131 > /tmp/u.log 2>&1 & sleep 1; .lake/build/bin/net-client upload PUT http://127.0.0.1:18131/sink size=268435456 chunk=16384 deadline=600000 trace=0 | grep -E \"^upload call|rss_peak\"'" | sed "s/^/$v run $k: /"
  done
done

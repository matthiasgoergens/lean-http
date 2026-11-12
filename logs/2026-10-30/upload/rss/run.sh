#!/usr/bin/env bash
# Peak resident memory of a 256 MiB streamed upload, for three versions of the shell's wait, from
# the laptop (each variant is copied to its own directory on the build host and built and run there
# directly, not through scripts/remote.sh, which would copy the working tree over it):
#   result    LeanHttp/Wait.lean as on main: awaitFirst resolves its promise with the winner's result
#   index     awaitFirst resolves its promise with the winner's index (Wait.lean of be4dd1f, on branch
#             upload-wip)
#   mailbox   Body.lean of the commit "WIP: mailbox, broken-body theorem, review fixes" (each operation reports once to a mailbox), index Wait.lean
# all on the committed tree (HEAD) otherwise.  Chunks of 16 KiB and of 1 KiB; two runs per cell,
# cells alternating.
set -u
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../../.." && pwd)
host=$(head -n 1 "$root/.build-host")
mailbox_commit=8be4e63   # "WIP: mailbox, broken-body theorem, review fixes", on branch upload-wip
ctr() { # ctr <dir> <command>: run a command in the Lean container in ~/<dir> on the build host
  ssh "$host" "cd ~/$1 && batchrun podman --cgroup-manager=cgroupfs run --cgroups=disabled --rm --network none -v b8perf-elan:/root/.elan:ro -v \"\$PWD\":/w -w /w -v /home/matthias/.local/share/uv/python/cpython-3.14.8-linux-x86_64-gnu:/py:ro localhost/b8perf-lean env PATH=/root/.elan/toolchains/leanprover--lean4---v4.34.1/bin:/usr/local/bin:/usr/bin:/bin bash -c '$2'"
}
echo "HEAD $(git -C "$root" rev-parse --short HEAD); mailbox commit $mailbox_commit"
for v in result index mailbox; do
  tree=$(mktemp --directory)
  git -C "$root" archive HEAD | tar --extract --directory "$tree"
  cp -r "$root/vendor" "$tree/vendor"
  case $v in
    result) git -C "$root" show db37391:LeanHttp/Wait.lean > "$tree/LeanHttp/Wait.lean" ;;
    index) git -C "$root" show be4dd1f:LeanHttp/Wait.lean > "$tree/LeanHttp/Wait.lean" ;;
    mailbox) git -C "$root" show be4dd1f:LeanHttp/Wait.lean > "$tree/LeanHttp/Wait.lean"
             git -C "$root" show "$mailbox_commit":LeanHttp/Body.lean > "$tree/LeanHttp/Body.lean" ;;
  esac
  echo "### variant $v: $(cd "$tree" && sha256sum LeanHttp/Body.lean LeanHttp/Wait.lean | tr '\n' ' ')"
  rsync --archive --delete --exclude .lake "$tree/" "$host:lean-http-upload-rss2-$v/" || exit 1
  rm --recursive --force "$tree"
  ctr lean-http-upload-rss2-$v 'lake build net-client 2>&1 | tail -1; sha256sum LeanHttp/Body.lean LeanHttp/Wait.lean' || exit 1
done
for chunk in 16384 1024; do
  for k in 1 2; do
    for v in result index mailbox; do
      ctr lean-http-upload-rss2-$v "/py/bin/python3 -I tests/net/upload.py 18131 > /tmp/u.log 2>&1 & sleep 1; .lake/build/bin/net-client upload PUT http://127.0.0.1:18131/sink size=268435456 chunk=$chunk deadline=600000 trace=0 | grep -E \"rss_peak|^upload call\" | cut -c1-40,330-" | sed "s/^/$v chunk=$chunk run $k: /"
    done
  done
done

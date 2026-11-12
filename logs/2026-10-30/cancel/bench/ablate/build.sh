here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../../../.." && pwd)
host=$(head -n 1 "$root/.build-host")
for m in "$@"; do
  tree=$(mktemp --directory); git -C "$root" archive 3dfd87d | tar --extract --directory "$tree"; cp -r "$root/vendor" "$tree/"
  (cd "$tree" && python3 "$here/mutate.py" "$m") || exit 1
  rsync --archive --delete --exclude .lake "$tree/" "$host:lean-http-cancel-ablate-$m/" || exit 1; rm -rf "$tree"
  ssh "$host" "cd ~/lean-http-cancel-ablate-$m && batchrun podman --cgroup-manager=cgroupfs run --cgroups=disabled --rm --network none -v b8perf-elan:/root/.elan:ro -v \"\$PWD\":/w -w /w localhost/b8perf-lean env PATH=/root/.elan/toolchains/leanprover--lean4---v4.34.1/bin:/usr/local/bin:/usr/bin:/bin bash -c 'lake build net-client 2>&1 | tail -1' && cp .lake/build/bin/net-client ~/lean-http-cancel/out/bench/net-client-$m"
done

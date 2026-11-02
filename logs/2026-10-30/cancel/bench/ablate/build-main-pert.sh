here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../../../.." && pwd)
host=$(head -n 1 "$root/.build-host")
tree=$(mktemp --directory); git -C "$root" archive 27a0d86 | tar --extract --directory "$tree"; cp -r "$root/vendor" "$tree/"
# A function nothing calls, before the client's code: the same program, its code placed differently.
python3 - "$tree/LeanHttp/Client.lean" <<'PY'
import sys
from pathlib import Path
p = Path(sys.argv[1]); s = p.read_text()
s = s.replace("namespace Client\n", "namespace Client\n\n/-- Unused: moves the code that follows. -/\ndef layoutPad (n : Nat) : Nat := (List.range n).foldl (fun a b => a * 31 + b * b + 7) 3\n", 1)
p.write_text(s)
PY
rsync --archive --delete --exclude .lake "$tree/" "$host:lean-http-cancel-ablate-mainpert/" || exit 1; rm -rf "$tree"
ssh "$host" "cd ~/lean-http-cancel-ablate-mainpert && batchrun podman --cgroup-manager=cgroupfs run --cgroups=disabled --rm --network none -v b8perf-elan:/root/.elan:ro -v \"\$PWD\":/w -w /w localhost/b8perf-lean env PATH=/root/.elan/toolchains/leanprover--lean4---v4.34.1/bin:/usr/local/bin:/usr/bin:/bin bash -c 'lake build net-client 2>&1 | tail -1' && cp .lake/build/bin/net-client ~/lean-http-cancel/out/bench/net-client-mainpert"

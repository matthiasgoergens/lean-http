#!/usr/bin/env bash
# Every run behind logs/2026-10-29/pool/, from the laptop, on the committed tree: the pure suites
# from a clean build, the real-socket suite, the strace check, the idle-check measurements and the
# randomised-block timing of the idle check.  Raw output lands in ~/lean-http-pool/out/final/ on the
# box; rsync it back afterwards.
here=$(cd "$(dirname "$0")/../../.." && pwd) || exit 1
logs=$here/logs/2026-10-29/pool
export LEAN_HTTP_REMOTE_DIR=lean-http-pool
remote=$here/scripts/remote.sh
ssh buildhost 'rm -rf ~/lean-http-pool/out/final ~/lean-http-pool/.lake/build && mkdir -p ~/lean-http-pool/out/final' || exit 1
scp -q "$logs"/run-suites.sh "$logs"/idlecheck.sh "$logs"/idlecheck0.sh "$logs"/bench-idlecheck.sh \
  buildhost:lean-http-pool/out/ || exit 1
"$remote" bash out/run-suites.sh out/final/suites || exit 1
CTR_EXTRA='--sysctl net.ipv4.tcp_syn_retries=2' "$remote" bash -c \
  'bash tests/net/run.sh > out/net-run.log 2>&1; cp -r out/net out/final/net; cp out/net-run.log out/final/net/run.log'
ssh buildhost 'cd ~/lean-http-pool && bash tests/net/strace-nodelay.sh > out/final/strace-nodelay.txt 2>&1'
"$remote" bash -c 'mkdir -p out/final/idlecheck out/final/bench && bash out/idlecheck.sh out/final/idlecheck/windows-200.txt 200 && bash out/idlecheck0.sh out/final/idlecheck/zero-1000.txt && bash out/bench-idlecheck.sh out/final/bench/bench-idlecheck-20.txt 20 1'
echo "done"

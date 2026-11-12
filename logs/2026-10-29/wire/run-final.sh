#!/usr/bin/env bash
# Every run behind logs/2026-10-29/wire/, from the laptop, on the committed tree: the pure suites
# from a clean build (lean-http-wire), then, from a second copy of the tree (lean-http-wire-net, so
# that no build replaces a binary mid-run), the real-socket suite, the strace check and the
# randomised-block timing of a 60 MB body against main's client.  Raw output lands in out/final/ of
# each copy on the box; rsync it back afterwards (see COMMAND).
here=$(cd "$(dirname "$0")/../../.." && pwd) || exit 1
logs=$here/logs/2026-10-29/wire
remote=$here/scripts/remote.sh
ssh buildhost 'rm -rf ~/lean-http-wire/out/final ~/lean-http-wire/.lake/build && mkdir -p ~/lean-http-wire/out/final' || exit 1
scp -q "$logs"/run-suites.sh buildhost:lean-http-wire/out/ || exit 1
LEAN_HTTP_REMOTE_DIR=lean-http-wire "$remote" bash out/run-suites.sh out/final/suites || exit 1
LEAN_HTTP_REMOTE_DIR=lean-http-wire-net "$remote" lake build net-client || exit 1
ssh buildhost 'rm -rf ~/lean-http-wire-net/out/final && mkdir -p ~/lean-http-wire-net/out/final' || exit 1
scp -q "$logs"/bench/bench-bigbody.sh buildhost:lean-http-wire-net/out/ || exit 1
CTR_EXTRA='--sysctl net.ipv4.tcp_syn_retries=2' LEAN_HTTP_REMOTE_DIR=lean-http-wire-net "$remote" bash -c \
  'bash tests/net/run.sh > out/net-run.log 2>&1; cp -r out/net out/final/net; cp out/net-run.log out/final/net/run.log'
ssh buildhost 'cd ~/lean-http-wire-net && bash tests/net/strace-nodelay.sh > out/final/strace-nodelay.txt 2>&1'
CTR_EXTRA='-v /home/matthias/lean-http-wire-main/.lake/build/bin:/main:ro' LEAN_HTTP_REMOTE_DIR=lean-http-wire-net \
  "$remote" bash out/bench-bigbody.sh out/final/bench-bigbody-20.txt 20 1
echo "done"

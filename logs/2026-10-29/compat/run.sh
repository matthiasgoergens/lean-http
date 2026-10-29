#!/usr/bin/env bash
# Every run behind logs/2026-10-29/compat/, from the laptop, on the committed tree, once per
# toolchain: v4.35.0 (from the elan volume LEAN_HTTP_ELAN names, which must hold it, in
# ~/lean-http-compat on the build host) and v4.34.1 (from b8perf-elan, in ~/lean-http-compat-434).  For each: the pure suites from a clean
# build (run-suites.sh, here), then the real-socket suite.  Raw output lands in out/compat/ of each
# copy on the box; rsync it back afterwards (see COMMAND).
#
# Usage: [LEAN_HTTP_ELAN=<volume>] bash logs/2026-10-29/compat/run.sh <v4.35.0|v4.34.1>
here=$(cd "$(dirname "$0")/../../.." && pwd) || exit 1
logs=$here/logs/2026-10-29/compat
remote=$here/scripts/remote.sh
host=$(head -n 1 "$here/.build-host") || exit 1
case $1 in
  v4.35.0) dir=lean-http-compat elan=${LEAN_HTTP_ELAN:?name an elan volume that holds v4.35.0} ;;
  v4.34.1) dir=lean-http-compat-434 elan=b8perf-elan ;;
  *) echo "usage: run.sh <v4.35.0|v4.34.1>" >&2; exit 1 ;;
esac
export LEAN_HTTP_REMOTE_DIR=$dir LEAN_HTTP_TOOLCHAIN=$1 LEAN_HTTP_ELAN=$elan
ssh "$host" "mkdir -p ~/$dir && cd ~/$dir && rm -rf out/compat .lake/build && mkdir -p out/compat" || exit 1
scp -q "$logs"/run-suites.sh "$host:$dir/out/" || exit 1
"$remote" bash -c 'lean --version > out/compat/toolchain.txt; bash out/run-suites.sh out/compat/suites' || exit 1
CTR_EXTRA='--sysctl net.ipv4.tcp_syn_retries=2' "$remote" bash -c \
  'bash tests/net/run.sh > out/net-run.log 2>&1; cp -r out/net out/compat/net; cp out/net-run.log out/compat/net/run.log'
echo "done $1"

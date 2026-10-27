#!/usr/bin/env bash
# Shows the system calls the client makes for one POST: that it sets TCP_NODELAY on its socket and
# writes the request in one call.  Runs on the host of the build host (strace is not in the Lean
# image), with the net-client binary that scripts/remote.sh built, against evil.py on a loopback
# port of the host.  From the repository root, after `scripts/remote.sh lake build net-client`:
#
#   ssh buildhost 'cd ~/lean-http && bash tests/net/strace-nodelay.sh'
py=${PY:-$HOME/.local/share/uv/python/cpython-3.14.8-linux-x86_64-gnu/bin/python3}
here=$(cd "$(dirname "$0")" && pwd) || exit 1
bin=$here/../../.lake/build/bin/net-client
port=$((30000 + RANDOM % 20000))
log=$(mktemp) || exit 1
"$py" -I "$here/evil.py" --port $port > "$log" 2>&1 &
server=$!
trap 'kill $server 2>/dev/null; wait $server 2>/dev/null; rm --force "$log"' EXIT
for _ in $(seq 100); do grep --quiet listening "$log" && break; sleep 0.05; done
trace=$(mktemp) || exit 1
echo "\$ strace -f -o TRACE -e trace=socket,connect,setsockopt,writev,sendmsg,sendto,write net-client call POST http://127.0.0.1:$port/echo body=100"
strace -f -o "$trace" -e trace=socket,connect,setsockopt,writev,sendmsg,sendto,write \
  "$bin" call POST "http://127.0.0.1:$port/echo" body=100
echo "### TRACE, without the writes to stdout and the runtime's own wake-ups"
grep --invert-match -e '] write(1, ' -e '^[0-9]* write(1, ' -e 'write([0-9]*, "\*", 1)' \
  -e 'write([0-9]*, "\\1\\0\\0\\0\\0\\0\\0\\0", 8)' "$trace"
rm --force "$trace"

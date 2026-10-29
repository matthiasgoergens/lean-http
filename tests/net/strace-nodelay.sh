#!/usr/bin/env bash
# Checks with strace that the client sets TCP_NODELAY on its socket and writes a small request in one
# call, and, as a control, that with `nodelay=0` it does not set the option.  Runs on the host of
# the build host (strace is not in the Lean image), with the net-client binary that
# scripts/remote.sh built, against evil.py on a loopback port of the host.  From the repository
# root, after `scripts/remote.sh lake build net-client`:
#
#   ssh buildhost 'cd ~/lean-http && bash tests/net/strace-nodelay.sh'
py=${PY:-$HOME/.local/share/uv/python/cpython-3.14.8-linux-x86_64-gnu/bin/python3}
here=$(cd "$(dirname "$0")" && pwd) || exit 1
bin=$here/../../.lake/build/bin/net-client
port=$((30000 + RANDOM % 20000))
log=$(mktemp) || exit 1
trace=$(mktemp) || exit 1
"$py" -I "$here/evil.py" --port $port > "$log" 2>&1 &
server=$!
trap 'kill $server 2>/dev/null; wait $server 2>/dev/null; rm --force "$log" "$trace"' EXIT
for _ in $(seq 100); do grep --quiet listening "$log" && break; sleep 0.05; done

fails=0
check() { # check <status of the condition> <description>
  if [ "$1" -eq 0 ]; then echo "PASS $2"; else echo "FAIL $2"; fails=$((fails + 1)); fi
}

for nodelay in 1 0; do
  echo "\$ strace -f -o TRACE -e trace=socket,connect,setsockopt,writev,sendmsg,sendto,write net-client call POST http://127.0.0.1:$port/echo body=100 nodelay=$nodelay"
  strace -f -o "$trace" -e trace=socket,connect,setsockopt,writev,sendmsg,sendto,write \
    "$bin" call POST "http://127.0.0.1:$port/echo" body=100 nodelay=$nodelay
  echo "### TRACE, without the writes to stdout and the runtime's own wake-ups"
  grep --invert-match -e '] write(1, ' -e '^[0-9]* write(1, ' -e 'write([0-9]*, "\*", 1)' \
    -e 'write([0-9]*, "\\1\\0\\0\\0\\0\\0\\0\\0", 8)' -e '+++ exited' "$trace"
  # The socket the client connected with, and what it did with it.
  fd=$(sed --quiet 's/.*connect(\([0-9]*\), {sa_family=AF_INET, sin_port=htons('"$port"').*/\1/p' "$trace" | head --lines=1)
  nodelays=$(grep --count "setsockopt($fd, SOL_TCP, TCP_NODELAY, \[1\], 4) = 0" "$trace")
  writes=$(grep --count -e "write($fd, " -e "writev($fd, " -e "sendmsg($fd, " -e "sendto($fd, " "$trace")
  whole=$(grep --count "write($fd, \"POST /echo HTTP/1.1.*, 191) = 191" "$trace")
  if [ "$nodelay" = 1 ]; then
    [ "$nodelays" = 1 ]; check $? "nodelay=1: TCP_NODELAY set once on the connected socket (fd ${fd:-?})"
  else
    [ "$nodelays" = 0 ]; check $? "nodelay=0 (control): TCP_NODELAY not set (fd ${fd:-?})"
  fi
  [ "$writes" = 1 ] && [ "$whole" = 1 ]
  check $? "nodelay=$nodelay: the 191-byte request went out in one write ($writes writes on the socket)"
done
echo "### $fails failed"
[ "$fails" -eq 0 ]

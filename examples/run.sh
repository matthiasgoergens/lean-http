#!/usr/bin/env bash
# Builds the examples (a package that requires lean-http by path) and runs them against
# examples/server.py on 127.0.0.1, checking what they print.  Needs lake on the PATH and python3
# ($PY if set).  Writes the outputs to out/examples/ at the repository root.
#
# Usage: examples/run.sh   (the server's port is $EXAMPLES_PORT, default 18300)
here=$(cd "$(dirname "$0")" && pwd) || exit 1
out=$here/../out/examples
port=${EXAMPLES_PORT:-18300}
if [ -z "${PY:-}" ]; then
  if [ -x /py/bin/python3 ]; then PY=/py/bin/python3; else PY=python3; fi
fi
mkdir --parents "$out" || exit 1

(cd "$here" && lake build) || exit 1

"$PY" -I "$here/server.py" "$port" > "$out/server.log" 2>&1 &
server=$!
trap 'kill $server 2>/dev/null; wait $server 2>/dev/null' EXIT
for _ in $(seq 100); do
  grep --quiet "listening on $port" "$out/server.log" && break
  sleep 0.05
done
grep --quiet "listening on $port" "$out/server.log" || { cat "$out/server.log"; exit 1; }

fails=0
# expect <file> <fixed string>: the example printed that line.
expect() {
  if grep --quiet --line-regexp --fixed-strings "$2" "$1"; then
    echo "PASS $(basename "$1"): $2"
  else
    echo "FAIL $(basename "$1"): no line $2"
    fails=$((fails + 1))
  fi
}

base=http://127.0.0.1:$port
"$here/.lake/build/bin/request-example" "$base" > "$out/request-example.txt" 2>&1 \
  || { echo "FAIL request-example exited with status $?"; fails=$((fails + 1)); }
cat "$out/request-example.txt"
expect "$out/request-example.txt" 'GET 200 application/json {"greeting": "hello"}'
expect "$out/request-example.txt" 'POST 200 33 bytes: {"name": "lean-http", "stars": 5}'
if grep --quiet --extended-regexp '^refused: could not connect: 127\.0\.0\.1:1 \(round 0\): .*; the server cannot have seen the request: sending it again is safe$' \
    "$out/request-example.txt"; then
  echo "PASS request-example.txt: the refused connect is reported as not sent"
else
  echo "FAIL request-example.txt: no line for the refused connect"
  fails=$((fails + 1))
fi

"$here/.lake/build/bin/stream-example" "$base" > "$out/stream-example.txt" 2>&1 \
  || { echo "FAIL stream-example exited with status $?"; fails=$((fails + 1)); }
cat "$out/stream-example.txt"
# The numbers 0 to 99999, one per line: 10 * 2 + 90 * 3 + 900 * 4 + 9000 * 5 + 90000 * 6 bytes.
case $(cat "$out/stream-example.txt") in
  "streamed 200: 588890 bytes in "*" pieces") echo "PASS stream-example.txt: the whole body, in pieces" ;;
  *) echo "FAIL stream-example.txt: expected 588890 bytes"; fails=$((fails + 1)) ;;
esac

"$here/.lake/build/bin/upload-example" "$base" > "$out/upload-example.txt" 2>&1 \
  || { echo "FAIL upload-example exited with status $?"; fails=$((fails + 1)); }
cat "$out/upload-example.txt"
# "line 0\n" to "line 9999\n": 10 * 7 + 90 * 8 + 900 * 9 + 9000 * 10 bytes.
expect "$out/upload-example.txt" 'streamed 200 {"bytes": 98890, "lines": 10000, "framing": "chunked"}'
expect "$out/upload-example.txt" 'known size 200 {"bytes": 24, "lines": 1, "framing": "length"}'

echo "$fails failing"
[ $fails -eq 0 ]

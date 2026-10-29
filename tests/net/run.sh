#!/usr/bin/env bash
# Real-socket tests of the client over loopback, against the local servers in this directory.
#
# Runs inside the container that scripts/remote.sh starts (no network but its own loopback, uv's
# CPython at /py), after `lake build net-client`.  From the repository root:
#
#   CTR_EXTRA='--sysctl net.ipv4.tcp_syn_retries=2' scripts/remote.sh bash tests/net/run.sh [name...]
#
# The sysctl makes the kernel give up on an unanswered SYN after about 7 s instead of about 127 s,
# so that the descriptor check of the blackhole scenario finishes quickly.
#
# Writes one file per scenario to out/net/<name>.txt, each starting with the client's command and
# ending with its exit status, wall time and how long the process took to exit after `main`
# returned, plus the logs of the servers it used; prints PASS or FAIL per check and a summary.

PY=${PY:-/py/bin/python3}
BIN=/w/.lake/build/bin/net-client
here=/w/tests/net
out=/w/out/net
mkdir --parents "$out" || exit 1

pids=()
cleanup() {
  for p in "${pids[@]}"; do kill "$p" 2>/dev/null; done
  for p in "${pids[@]}"; do wait "$p" 2>/dev/null; done
  pids=()
}
trap cleanup EXIT

passes=0
fails=0
knowns=0
result() { # result <PASS|FAIL|KNOWN> <scenario> <description>
  echo "$1 $2: $3" | tee --append "$out/summary.txt"
  case $1 in
    PASS) passes=$((passes + 1)) ;;
    KNOWN) knowns=$((knowns + 1)) ;;
    *) fails=$((fails + 1)) ;;
  esac
}

# start <scenario> <server name> <ready text> <command...>: start a server, wait for <ready text>.
start() {
  local scenario=$1 name=$2 ready=$3; shift 3
  local log="$out/$scenario.$name.log"
  "$@" > "$log" 2>&1 &
  pids+=($!)
  for _ in $(seq 100); do
    grep --quiet --fixed-strings "$ready" "$log" 2>/dev/null && return 0
    sleep 0.05
  done
  echo "server $name for $scenario did not become ready" >&2
  cat "$log" >&2
  return 1
}

# client <scenario> <net-client args...>: run the client once, record its output and timings.
# A non-zero exit status or a slow exit is a FAIL, or KNOWN with the reason in $known_exit.
client() {
  local scenario=$1; shift
  local file="$out/$scenario.txt"
  echo "\$ net-client $*" > "$file"
  local t0 t1 rc
  t0=$(date +%s%N)
  timeout 60 "$BIN" "$@" >> "$file" 2>&1
  rc=$?
  t1=$(date +%s%N)
  local wall=$(( (t1 - t0) / 1000000 ))
  local main
  main=$(sed --quiet 's/^main returning at ms=\([0-9]*\)\..*/\1/p' "$file")
  local after=$(( wall - ${main:-$wall} ))
  echo "exit status=$rc wall_ms=$wall exit_after_main_ms=$after" >> "$file"
  if [ -z "$main" ]; then
    result FAIL "$scenario" "main never returned (status $rc)"
  elif { [ "$after" -gt 1000 ] || [ "$rc" -ne 0 ]; } && [ -n "${known_exit:-}" ]; then
    result KNOWN "$scenario" "exit status $rc, ${after} ms after main returned: $known_exit"
  elif [ "$rc" -ne 0 ]; then
    result FAIL "$scenario" "exit status $rc, ${after} ms after main returned"
  elif [ "$after" -gt 1000 ]; then
    result FAIL "$scenario" "process took ${after} ms to exit after main returned"
  else
    result PASS "$scenario" "process exited ${after} ms after main returned"
  fi
}

# expect <scenario> <extended regex> <description>: check the client's output.
expect() {
  if grep --quiet --extended-regexp "$2" "$out/$1.txt"; then
    result PASS "$1" "$3"
  else
    result FAIL "$1" "$3 (no match for: $2)"
  fi
}

# call_ms <scenario>: the time of the first call, in whole milliseconds.
call_ms() {
  sed --quiet 's/^call 0 .* ms=\([0-9]*\)\..*/\1/p' "$out/$1.txt" | head --lines=1
}

# within <scenario> <lo> <hi> <description>: the first call took between lo and hi ms.
within() {
  local ms
  ms=$(call_ms "$1")
  if [ -n "$ms" ] && [ "$ms" -ge "$2" ] && [ "$ms" -le "$3" ]; then
    result PASS "$1" "$4: ${ms} ms"
  else
    result FAIL "$1" "$4: ${ms:-no} ms, expected ${2}-${3}"
  fi
}

# median_within <scenario> <lo> <hi> <description>: the median of repeated calls is in [lo, hi] ms.
median_within() {
  local ms
  # The summary of all calls (net-client also summarises the later calls and the idle checks).
  ms=$(sed --quiet '/^summary \(later calls\|idle checks\) /d; s/^summary .* p50=\([0-9]*\)\..*/\1/p' "$out/$1.txt")
  if [ -n "$ms" ] && [ "$ms" -ge "$2" ] && [ "$ms" -le "$3" ]; then
    result PASS "$1" "$4: ${ms} ms"
  else
    result FAIL "$1" "$4: ${ms:-no} ms, expected ${2}-${3}"
  fi
}

EVIL=18080      # evil.py on 127.0.0.1
EVIL6=18081     # evil.py on ::1
ONEWRITE=18082  # onewrite.py on 127.0.0.1
DUAL=18083      # blackhole on ::1, evil.py on 127.0.0.1
HOLE=18084      # blackhole on ::1 only
CLOSED=18085    # nothing listens
HOLE2=18086     # blackhole on ::1 only, for the connect deadline
NOREAD=18087    # accepts and never reads
LARGE=18088     # onewrite.py, for a large POST
EARLY=18089     # early.py: answers 413 after the head, then reads no more
# 18090-18101 and 18104: the pooling scenarios, each with an evil.py of its own; 18102: idle.py

# Names for the resolver tests.  getaddrinfo without a socket type returns each of these addresses
# once per socket type, three times in all.
grep --quiet 'dual\.test' /etc/hosts || {
  printf '127.0.0.1 dup.test\n::1 dual.test\n127.0.0.1 dual.test\n' >> /etc/hosts || exit 1
}

servers() {
  start shared evil "listening" "$PY" -I "$here/evil.py" --port $EVIL || return 1
}

scenario() { # scenario <name>: true if the scenario was asked for (or none were)
  [ ${#selected[@]} -eq 0 ] && return 0
  local s; for s in "${selected[@]}"; do [ "$s" = "$1" ] && { matched+=("$1"); return 0; }; done
  return 1
}
matched=()
selected=("$@")
rm --force "$out"/*.txt "$out"/*.log
echo "### $(date --utc +%FT%TZ) $(uname -r); syn_retries=$(cat /proc/sys/net/ipv4/tcp_syn_retries)" \
  | tee "$out/summary.txt"

servers || exit 1

if scenario get; then
  client get call GET "http://127.0.0.1:$EVIL/ok"
  expect get 'call 0 ok status=200 bytes=5 .*address=127\.0\.0\.1:18080' "GET returns the body"
fi

if scenario post; then
  client post call POST "http://127.0.0.1:$EVIL/echo" body=11
  expect post 'call 0 ok status=200 .*body_start="POST /echo ' "POST is answered"
  if grep --quiet --extended-regexp "POST /echo \{'host': \['127\.0\.0\.1:18080'\], 'connection': \['keep-alive'\], 'content-length': \['11'\]\} body=11B" "$out/shared.evil.log"; then
    result PASS post "the server read Host, Content-Length: 11, Connection: keep-alive and an 11-byte body"
  else
    result FAIL post "the server did not log an 11-byte body"
  fi
fi

if scenario head; then
  client head call HEAD "http://127.0.0.1:$EVIL/head-cl"
  expect head 'call 0 ok status=200 bytes=0 ' "HEAD with Content-Length: 12345 has an empty body"
fi

if scenario chunked; then
  client chunked call GET "http://127.0.0.1:$EVIL/chunked-ext"
  expect chunked 'call 0 ok status=200 bytes=11 .*body_start="hello world"' \
    "chunked body with extensions and trailers"
fi

if scenario interim; then
  client interim call GET "http://127.0.0.1:$EVIL/early-hints"
  expect interim 'call 0 ok status=200 bytes=8 .*body_start="after103"' "two 103 responses, then 200"
fi

if scenario ipv6-literal; then
  start ipv6-literal evil6 "listening" "$PY" -I "$here/evil.py" --port $EVIL6 --v6 --host ::1 || exit 1
  client ipv6-literal call GET "http://[::1]:$EVIL6/ok"
  expect ipv6-literal 'call 0 ok status=200 bytes=5 .*address=\[::1\]:18081' "an IPv6 literal URL connects"
fi

if scenario dns-dup; then
  getent ahosts dup.test > "$out/dns-dup.getent.log" 2>&1
  getent ahosts dual.test > "$out/dns-dual.getent.log" 2>&1
  client dns-dup call GET "http://dup.test:$CLOSED/" retries=0
  expect dns-dup 'attempts=\[127\.0\.0\.1:18085#0:failed\([^]]*\)\]$' \
    "a name with one address (returned three times) gets one attempt"
fi

if scenario dns-dual; then
  client dns-dual call GET "http://dual.test:$CLOSED/" retries=0
  refused='failed\(no such thing \(error code: 111, connection refused\)\)'
  expect dns-dual "attempts=\\[\\[::1\\]:18085#0:$refused, 127\\.0\\.0\\.1:18085#0:$refused\\]\$" \
    "a name with two addresses (each returned three times) gets two attempts, ::1 first"
fi

if scenario blackhole-first; then
  start blackhole-first hole "blackhole" "$PY" -I "$here/blackhole.py" ::1 $DUAL || exit 1
  start blackhole-first evil "listening" "$PY" -I "$here/evil.py" --port $DUAL || exit 1
  # Without pooling, so that every call connects (and the ::1 attempt is abandoned every time).
  client blackhole-first call GET "http://dual.test:$DUAL/ok" repeat=10 pool=0
  expect blackhole-first 'call 0 ok status=200 bytes=5 .*address=127\.0\.0\.1:18083' \
    "connects to 127.0.0.1 when ::1 drops SYNs"
  expect blackhole-first 'summary calls n=10 .* ok=10$' "ten calls out of ten"
  expect blackhole-first 'failed_attempts=\[\[::1\]:18083#0:abandoned\]' "the ::1 attempt was abandoned"
  # Each call's connection must close before the next call connects.  A connection kept open by the
  # abandoned ::1 attempt would close only when the kernel gives up on that attempt, or at exit.
  ordered=1
  for k in $(seq 1 9); do
    eof=$(grep --line-number "conn$k EOF from client" "$out/blackhole-first.evil.log" | cut --delimiter=: --fields=1 | head --lines=1)
    next=$(grep --line-number "conn$((k + 1)) accepted" "$out/blackhole-first.evil.log" | cut --delimiter=: --fields=1 | head --lines=1)
    { [ -n "$eof" ] && [ -n "$next" ] && [ "$eof" -lt "$next" ]; } || ordered=0
  done
  if [ $ordered -eq 1 ]; then
    result PASS blackhole-first "each call's connection closed before the next call connected"
  else
    result FAIL blackhole-first "a call's connection was still open when the next call connected"
  fi
  median_within blackhole-first 240 400 "median call within about the 250 ms stagger"
  client blackhole-stagger50 call GET "http://dual.test:$DUAL/ok" repeat=10 stagger=50 pool=0
  median_within blackhole-stagger50 40 200 "with a 50 ms stagger, the median call is about 50 ms"
fi

if scenario blackhole-timeout; then
  start blackhole-timeout hole "blackhole" "$PY" -I "$here/blackhole.py" ::1 $HOLE || exit 1
  client blackhole-timeout call GET "http://[::1]:$HOLE/" connect=1000 retries=1 seed=1 linger=9000
  expect blackhole-timeout 'call 0 error delivery=not sent .*attempts=\[\[::1\]:18084#0:timedOut, \[::1\]:18084#1:timedOut\]' \
    "two connect attempts time out; nothing sent"
  within blackhole-timeout 2000 2400 "two 1 s attempts and one backoff"
  calls=$(sed --quiet 's/^fds_after_calls=//p' "$out/blackhole-timeout.txt")
  later=$(sed --quiet 's/^fds_after_linger_9000ms=//p' "$out/blackhole-timeout.txt")
  if [ -n "$calls" ] && [ -n "$later" ] && [ "$later" -le $((calls - 2)) ]; then
    result PASS blackhole-timeout "the abandoned attempts' sockets are released later ($calls, then $later descriptors)"
  else
    result FAIL blackhole-timeout "descriptors after the call: ${calls:-?}, 9 s later: ${later:-?}"
  fi
fi

if scenario refused-backoff; then
  "$BIN" backoff 42 > "$out/refused-backoff.schedule.txt" 2>&1
  client refused-backoff call GET "http://127.0.0.1:$CLOSED/" seed=42
  expect refused-backoff 'call 0 error delivery=not sent .*rounds=3 seed=42 .*could not connect' \
    "refused three times (two retries); nothing sent"
  expect refused-backoff 'attempts=\[127\.0\.0\.1:18085#0:failed\([^]]*\), 127\.0\.0\.1:18085#1:failed\([^]]*\), 127\.0\.0\.1:18085#2:failed\([^]]*\)\]' \
    "one attempt per round"
  # backoff 42 gives [23, 49]: the call takes at least their sum.
  within refused-backoff 72 400 "at least the 23 + 49 ms of backoff for seed 42"
fi

if scenario deadline-trickle; then
  client deadline-trickle call GET "http://127.0.0.1:$EVIL/trickle?ms=100" deadline=2000 gap=1000
  expect deadline-trickle 'call 0 error delivery=response received .*status=\(some 200\) cause="deadline timeout"' \
    "a body trickling one byte per 100 ms ends at the deadline"
  within deadline-trickle 1990 2400 "at the 2 s deadline"
fi

if scenario deadline-interim; then
  client deadline-interim call GET "http://127.0.0.1:$EVIL/interim-forever?ms=300" deadline=2000
  expect deadline-interim 'call 0 error delivery=maybe delivered .*cause="deadline timeout"' \
    "interim responses every 300 ms, never a final one, end at the deadline"
  within deadline-interim 1990 2400 "at the 2 s deadline"
fi

if scenario interim-limit; then
  client interim-limit call GET "http://127.0.0.1:$EVIL/interim-forever?ms=5"
  expect interim-limit 'call 0 error delivery=maybe delivered .*cause="interim responses limit exceeded"' \
    "the eleventh interim response fails the call"
fi

if scenario read-gap; then
  client read-gap call GET "http://127.0.0.1:$EVIL/stall-head?ms=3000" gap=1000
  expect read-gap 'call 0 error delivery=maybe delivered .*cause="read timeout"' "a silent server hits the read gap"
  within read-gap 990 1400 "after the 1 s gap"
fi

if scenario body-limit; then
  client body-limit call GET "http://127.0.0.1:$EVIL/bigbody?n=10000000" maxbody=1000000
  expect body-limit 'call 0 error delivery=response received .*cause="body size limit exceeded"' \
    "a 10 MB body against a 1 MB limit"
fi

if scenario malformed; then
  client malformed call GET "http://127.0.0.1:$EVIL/badstatus"
  expect malformed 'call 0 error delivery=maybe delivered .*cause="invalid response: Bad message"' \
    "a malformed status line"
fi

if scenario cut-body; then
  client cut-body call GET "http://127.0.0.1:$EVIL/cl-mismatch"
  expect cut-body 'call 0 error delivery=response received .*cause="the connection closed before a complete response"' \
    "the server closes 95 bytes short of its Content-Length"
fi

if scenario reset; then
  client reset call GET "http://127.0.0.1:$EVIL/rst"
  expect reset 'call 0 error delivery=maybe delivered .*cause="the connection closed before a complete response"' \
    "the server resets the connection instead of answering"
fi

if scenario resolve; then
  client resolve call GET "http://nonexistent.invalid/"
  expect resolve 'call 0 error delivery=not sent .*could not resolve nonexistent\.invalid' \
    "a name that does not resolve; not retried"
fi

if scenario nodelay; then
  start nodelay onewrite "listening" "$PY" -I "$here/onewrite.py" --port $ONEWRITE --log "$out/nodelay.recv.log" || exit 1
  client nodelay call POST "http://127.0.0.1:$ONEWRITE/" body=100 repeat=300
  client nodelay-off call POST "http://127.0.0.1:$ONEWRITE/" body=100 repeat=300 nodelay=0
  client nodelay-raw-split-keepalive rawpost $ONEWRITE n=50 size=100 keepalive=1 nodelay=0
  client nodelay-raw-split-keepalive-nodelay rawpost $ONEWRITE n=300 size=100 keepalive=1 nodelay=1
  client nodelay-raw-split-fresh rawpost $ONEWRITE n=300 size=100 keepalive=0 nodelay=0
  p50() { sed --quiet '/^summary \(later calls\|idle checks\) /d; s/^summary .* p50=\([0-9]*\)\..*/\1/p' "$out/$1.txt"; }
  for s in nodelay nodelay-off nodelay-raw-split-fresh nodelay-raw-split-keepalive-nodelay; do
    v=$(p50 $s)
    if [ -n "$v" ] && [ "$v" -lt 20 ]; then
      result PASS $s "median call ${v} ms, no 40 ms stall"
    else
      result FAIL $s "median call ${v:-?} ms"
    fi
  done
  v=$(p50 nodelay-raw-split-keepalive)
  if [ -n "$v" ] && [ "$v" -ge 20 ]; then
    result PASS nodelay-raw-split-keepalive "control: split writes with Nagle on a kept-alive connection stall (median ${v} ms)"
  else
    result FAIL nodelay-raw-split-keepalive "control did not stall (median ${v:-?} ms): the harness cannot see the effect"
  fi
fi

if scenario post-large; then
  start post-large onewrite "listening" "$PY" -I "$here/onewrite.py" --port $LARGE || exit 1
  client post-large call POST "http://127.0.0.1:$LARGE/" body=3000000
  expect post-large 'call 0 ok status=200 bytes=12 ' "a 3 MB body goes out in slices and is answered"
fi

if scenario connect-deadline; then
  start connect-deadline hole "blackhole" "$PY" -I "$here/blackhole.py" ::1 $HOLE2 || exit 1
  client connect-deadline call GET "http://[::1]:$HOLE2/" deadline=1500
  expect connect-deadline 'call 0 error delivery=not sent .*cause="deadline timeout"' \
    "the deadline passes while connecting; nothing sent"
  within connect-deadline 1490 1900 "at the 1.5 s deadline"
fi

if scenario write-timeout; then
  start write-timeout noread "listening" "$PY" -I "$here/noread.py" $NOREAD || exit 1
  client write-timeout call POST "http://127.0.0.1:$NOREAD/" body=32000000 gap=1000
  expect write-timeout 'call 0 error delivery=maybe delivered .*cause="write timeout" detail="[0-9]+ of 32000[0-9]+ request bytes accepted"' \
    "a peer that stops reading stalls the upload; the write gap ends it"
fi

if scenario early-response; then
  start early-response early "listening" "$PY" -I "$here/early.py" $EARLY || exit 1
  client early-response call POST "http://127.0.0.1:$EARLY/" body=32000000 gap=1000
  expect early-response 'call 0 ok status=413 bytes=3 .*body_start="big"' \
    "a server that answers 413 after the head and stops reading: the response is delivered"
  within early-response 0 900 "before the 1 s write gap"
fi

# --- Pooling.  Each scenario has an evil.py of its own, so that its log counts the connections.

# conns <scenario> <n> <description>: the scenario's server accepted exactly n connections.
conns() {
  local got
  got=$(grep --count ' accepted from ' "$out/$1.evil.log")
  if [ "$got" -eq "$2" ]; then
    result PASS "$1" "$3: $got"
  else
    result FAIL "$1" "$3: $got, expected $2"
  fi
}

# logged <scenario> <extended regex> <description>: the scenario's server logged a match.
logged() {
  if grep --quiet --extended-regexp "$2" "$out/$1.evil.log"; then
    result PASS "$1" "$3"
  else
    result FAIL "$1" "$3 (no match in the server log for: $2)"
  fi
}

evil() { # evil <scenario> <port>: an evil.py for one scenario
  start "$1" evil "listening" "$PY" -I "$here/evil.py" --port "$2"
}

if scenario pool-reuse; then
  evil pool-reuse 18090 || exit 1
  client pool-reuse call GET "http://127.0.0.1:18090/ok" repeat=3
  expect pool-reuse 'call 0 ok status=200 .* conn=\(some 0\) reused=false' "the first call opens connection 0"
  expect pool-reuse 'call 1 ok status=200 .* conn=\(some 0\) reused=true discarded=0 .*redispatched=false' \
    "the second call reuses it after a clean idle check"
  expect pool-reuse 'call 2 ok status=200 .* conn=\(some 0\) reused=true discarded=0 ' "so does the third"
  expect pool-reuse '^pool idle=1 checked_out=0 allocated=1$' "one idle connection at the end"
  conns pool-reuse 1 "the server saw one connection for three calls"
  logged pool-reuse "req3 GET /ok \{'host': \['127\.0\.0\.1:18090'\], 'connection': \['keep-alive'\]\}" \
    "the requests say Connection: keep-alive"
fi

if scenario pool-off; then
  evil pool-off 18091 || exit 1
  client pool-off call GET "http://127.0.0.1:18091/ok" repeat=3 pool=0
  expect pool-off 'call 2 ok status=200 .* conn=none reused=false' "with pooling off, no call reuses"
  conns pool-off 3 "the server saw a connection per call"
  logged pool-off "req1 GET /ok \{'host': \['127\.0\.0\.1:18091'\], 'connection': \['close'\]\}" \
    "the requests say Connection: close"
fi

if scenario keepalive-close; then
  # The server closes a connection 200 ms after its last response; the next call comes 500 ms later.
  evil keepalive-close 18092 || exit 1
  client keepalive-close call GET "http://127.0.0.1:18092/close-after-idle?ms=200" repeat=3 pause=500
  expect keepalive-close 'call 1 ok status=200 .*reused=false discarded=1 .*redispatched=false' \
    "the idle check finds the closed connection; the call opens a new one"
  expect keepalive-close 'call 2 ok status=200 .*reused=false discarded=1 .*redispatched=false' "and again"
  expect keepalive-close 'summary calls n=3 .* ok=3$' "no call fails"
  conns keepalive-close 3 "three connections"
  # Without the idle check, the closed connection is used: the request goes out, the end of input
  # comes back, and a GET is sent again on a fresh connection.
  client keepalive-close-nocheck call GET "http://127.0.0.1:18092/close-after-idle?ms=200" repeat=2 pause=500 idlecheck=off
  expect keepalive-close-nocheck 'call 1 ok status=200 .*reused=false discarded=0 .*redispatched=true' \
    "without the idle check, the GET is sent again on a fresh connection"
  # A POST is not: the server may have acted on it.
  client keepalive-close-post call POST "http://127.0.0.1:18092/close-after-idle?ms=200" body=5 repeat=2 pause=500 idlecheck=off
  expect keepalive-close-post 'call 1 error delivery=maybe delivered .*reused=true redispatched=false .*cause="the connection closed before a complete response"' \
    "without the idle check, a POST on the closed connection fails, maybe delivered"
fi

if scenario keepalive-race; then
  # The server closes the connection when the next request arrives, without answering: the request
  # crosses the server's close, which no idle check can see.
  evil keepalive-race 18093 || exit 1
  client keepalive-race call GET "http://127.0.0.1:18093/die-on-next" repeat=2
  expect keepalive-race 'call 1 ok status=200 .*reused=false .*redispatched=true' \
    "a GET whose connection closes as it is sent goes again on a fresh connection"
  logged keepalive-race 'conn1 got [0-9]+ bytes of the next request; closing without answering' \
    "the server closed the first connection on the second request"
  conns keepalive-race 2 "two connections"
  client keepalive-race-rst call GET "http://127.0.0.1:18093/die-on-next?rst=1" repeat=2
  expect keepalive-race-rst 'call 1 ok status=200 .*redispatched=true' "the same with a reset"
  client keepalive-race-post call POST "http://127.0.0.1:18093/die-on-next" body=5 repeat=2
  expect keepalive-race-post 'call 1 error delivery=maybe delivered .*reused=true redispatched=false' \
    "a POST in the same race fails, maybe delivered"
fi

if scenario idle-408; then
  # The server sends 408 and closes 100 ms after its response; the next call comes 400 ms later.
  evil idle-408 18094 || exit 1
  client idle-408 call POST "http://127.0.0.1:18094/idle-408?ms=100" body=5 repeat=2 pause=400
  expect idle-408 'call 1 ok status=200 .*reused=false discarded=1 .*redispatched=false' \
    "the idle check catches the 408 and the close; the POST goes on a new connection"
  logged idle-408 'conn1 sent 408' "the server sent the 408"
  # Without the idle check, and with the server keeping the connection open after the 408, the
  # request is written and the 408 read as its response: the POST is sent again, any method being
  # safe after a 408.
  client idle-408-nocheck call POST "http://127.0.0.1:18094/idle-408?ms=100&linger=2000" body=5 repeat=2 pause=400 idlecheck=off
  expect idle-408-nocheck 'call 1 ok status=200 .*reused=false .*redispatched=true' \
    "without the idle check, the 408 read as the response sends the POST again"
fi

if scenario close-response; then
  evil close-response 18095 || exit 1
  client close-response call GET "http://127.0.0.1:18095/close-hdr" repeat=2
  expect close-response 'call 1 ok status=200 bytes=3 .*reused=false' "a Connection: close response is not reused"
  expect close-response '^pool idle=0 checked_out=0 allocated=2$' "nothing idle"
  conns close-response 2 "two connections"
fi

if scenario head-stray; then
  evil head-stray 18096 || exit 1
  client head-stray call HEAD "http://127.0.0.1:18096/head-stray" repeat=2
  expect head-stray 'call 0 ok status=200 bytes=0 ' "the HEAD response has no body"
  expect head-stray 'call 1 ok status=200 bytes=0 .*reused=false' "stray bytes after it: not reused"
  conns head-stray 2 "two connections"
fi

if scenario concurrency; then
  evil concurrency 18097 || exit 1
  client concurrency call GET "http://127.0.0.1:18097/sleep?ms=300" concurrent=8 repeat=2
  r0=$(sed --quiet 's/^round 0 of 8 calls took ms=\([0-9]*\)\..*/\1/p' "$out/concurrency.txt")
  r1=$(sed --quiet 's/^round 1 of 8 calls took ms=\([0-9]*\)\..*/\1/p' "$out/concurrency.txt")
  if [ -n "$r0" ] && [ -n "$r1" ] && [ "$r0" -lt 900 ] && [ "$r1" -lt 900 ]; then
    result PASS concurrency "eight 300 ms calls at once take ${r0} and ${r1} ms: none waits for another"
  else
    result FAIL concurrency "rounds took ${r0:-?} and ${r1:-?} ms, expected under 900"
  fi
  expect concurrency 'summary calls n=16 .* ok=16$' "all sixteen calls succeed"
  expect concurrency '^pool idle=4 checked_out=0 allocated=12$' \
    "the first round opens eight connections and keeps four; the second reuses those and opens four"
  conns concurrency 12 "twelve connections"
  [ "$(grep --count 'reused=true' "$out/concurrency.txt")" -eq 4 ]
  if [ $? -eq 0 ]; then result PASS concurrency "four calls reused"; else result FAIL concurrency "not four calls reused"; fi
  evil concurrency-cap 18098 || exit 1
  client concurrency-cap call GET "http://127.0.0.1:18098/sleep?ms=200" concurrent=6 maxactive=2
  r0=$(sed --quiet 's/^round 0 of 6 calls took ms=\([0-9]*\)\..*/\1/p' "$out/concurrency-cap.txt")
  if [ -n "$r0" ] && [ "$r0" -ge 590 ] && [ "$r0" -lt 1200 ]; then
    result PASS concurrency-cap "six 200 ms calls with at most two at once take ${r0} ms"
  else
    result FAIL concurrency-cap "the round took ${r0:-?} ms, expected 600 to 1200"
  fi
  expect concurrency-cap 'summary calls n=6 .* ok=6$' "all six succeed"
  conns concurrency-cap 2 "two connections"
fi

if scenario pool-close; then
  evil pool-close 18099 || exit 1
  client pool-close call GET "http://127.0.0.1:18099/ok" repeat=2 close=1
  expect pool-close '^after close: pool idle=0 checked_out=0$' "closing the client closes the idle connection"
  expect pool-close 'after close: call 2 error delivery=not sent .*cause="the client closed the connection"' \
    "a call after closing fails, not sent"
  logged pool-close 'conn1 EOF from client after 2 requests' "the server sees the connection closed"
  client pool-close-off call GET "http://127.0.0.1:18099/ok" close=1 pool=0
  expect pool-close-off 'after close: call 1 error delivery=not sent .*cause="the client closed the connection"' \
    "with pooling off, too"
fi

if scenario redispatch-refused; then
  # The server goes away between two calls.  Without the idle check, the second call's GET goes out
  # on the closed connection and is sent again on a fresh connection, which is refused: the error
  # describes the second attempt, but the first was written, so it says maybe delivered.
  evil redispatch-refused 18104 || exit 1
  ( sleep 0.5; kill "${pids[-1]}" ) &
  client redispatch-refused call GET "http://127.0.0.1:18104/ok" repeat=2 pause=1000 idlecheck=off retries=0
  expect redispatch-refused 'call 1 error delivery=maybe delivered .*reused=false redispatched=true .*could not connect' \
    "a re-dispatched GET whose fresh connection is refused: maybe delivered"
fi

if scenario idle-timeout; then
  evil idle-timeout 18100 || exit 1
  client idle-timeout call GET "http://127.0.0.1:18100/ok" repeat=2 pause=600 idletimeout=300
  expect idle-timeout 'call 1 ok status=200 .*reused=false discarded=0 ' "an expired idle connection is not used"
  logged idle-timeout 'conn1 EOF from client after 1 requests' "and is closed"
  conns idle-timeout 2 "two connections"
fi

# Last, because it points the resolver at a name server that never answers.
if scenario dns-timeout; then
  cp /etc/resolv.conf /tmp/resolv.conf.saved 2>/dev/null || : > /tmp/resolv.conf.saved
  printf 'nameserver 127.0.0.1\n' > /etc/resolv.conf || exit 1
  start dns-timeout dns "listening" "$PY" -I "$here/dnsblack.py" || exit 1
  known_exit="the abandoned lookup delays exit until the resolver gives up, and the process often crashes then (NOTES.md)" \
    client dns-timeout call GET "http://slow.test/" deadline=2000
  cp /tmp/resolv.conf.saved /etc/resolv.conf
  expect dns-timeout 'call 0 error delivery=not sent .*cause="deadline timeout"' \
    "a name server that never answers: the call ends at the deadline; nothing sent"
  within dns-timeout 1990 2400 "at the 2 s deadline"
fi

cleanup
# A name that matches no scenario, or a run with no checks at all, must not pass silently.
for s in "${selected[@]}"; do
  case " ${matched[*]} " in *" $s "*) ;; *) echo "FAIL $s: no such scenario" | tee --append "$out/summary.txt"; fails=$((fails + 1)) ;; esac
done
if [ $((passes + fails + knowns)) -eq 0 ]; then
  echo "FAIL run: no checks ran" | tee --append "$out/summary.txt"; fails=1
fi
echo "### $passes passed, $fails failed, $knowns known limitations" | tee --append "$out/summary.txt"
[ "$fails" -eq 0 ]

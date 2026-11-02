# The tls-partial-wild call N times with segv.so preloaded, keeping each crash's output and its
# backtrace resolved by addr2line.  In the build container, from the tree's root, after lake build
# net-client and with crash-loop.sh's server set up (run crash-loop.sh 1 first):
#   bash segv-run.sh N
n=${1:-1000}
gcc -shared -fPIC -O1 -o out/crash/segv.so segv.c -ldl || exit 1
certs=out/crash/certs
PY=/py/bin/python3
grep --quiet 'wild\.lh\.test' /etc/hosts || cat tests/net/hosts >> /etc/hosts
"$PY" -I tests/net/tls.py --cert "$certs/partial-wild.pem" --key "$certs/partial-wild.key" --port 18266 --plain-port 18267 > out/crash/tls.log 2>&1 &
server=$!
sleep 1
echo "loadavg $(cat /proc/loadavg) n=$n"
crashes=0
for i in $(seq "$n"); do
  LD_PRELOAD=$PWD/out/crash/segv.so timeout 60 .lake/build/bin/net-client call GET https://wild.lh.test:18266/hello ca="$certs/ca.pem" > out/crash/call.txt 2>&1
  rc=$?
  if [ "$rc" -ne 0 ]; then
    crashes=$((crashes + 1))
    echo "=== run $i: exit status $rc"
    cat out/crash/call.txt
    grep --only-matching 'net-client+0x[0-9a-f]*' out/crash/call.txt | sed 's/.*+//' \
      | xargs --no-run-if-empty addr2line --functions --demangle --inlines --exe .lake/build/bin/net-client
  fi
done
echo "crashes: $crashes of $n; loadavg $(cat /proc/loadavg)"
kill $server

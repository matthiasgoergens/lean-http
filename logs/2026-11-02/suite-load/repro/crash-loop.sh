# The call of tls-partial-wild (a certificate refused for its name, after a lookup in /etc/hosts) N
# times, counting the runs that end with a signal (139: a segmentation fault) after main returned.
# In the build container, from the tree's root, after lake build net-client:
#   bash crash-loop.sh N [URL-PATH]
n=${1:-100}
PY=/py/bin/python3
grep --quiet 'wild\.lh\.test' /etc/hosts || cat tests/net/hosts >> /etc/hosts
certs=out/crash/certs
mkdir --parents "$certs"
[ -f "$certs/ca.pem" ] || bash tests/net/tls-certs.sh "$certs" > /dev/null 2>&1 || exit 1
"$PY" -I tests/net/tls.py --cert "$certs/partial-wild.pem" --key "$certs/partial-wild.key" --port 18266 --plain-port 18267 > out/crash/tls.log 2>&1 &
server=$!
sleep 1
echo "loadavg $(cat /proc/loadavg) n=$n $(git rev-parse --short HEAD 2>/dev/null)"
declare -A codes=()
for i in $(seq "$n"); do
  timeout 60 .lake/build/bin/net-client call GET https://wild.lh.test:18266/hello ca="$certs/ca.pem" > out/crash/call.txt 2>&1
  rc=$?
  codes[$rc]=$(( ${codes[$rc]:-0} + 1 ))
  if [ "$rc" -ne 0 ]; then cp out/crash/call.txt "out/crash/fail-$i.txt"; fi
done
for k in "${!codes[@]}"; do echo "exit status $k: ${codes[$k]} runs"; done
echo "loadavg $(cat /proc/loadavg)"
kill $server

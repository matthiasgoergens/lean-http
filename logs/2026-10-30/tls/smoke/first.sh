# First end-to-end check over loopback, inside the build container (scripts/remote.sh).
set -u
d=out/tls-smoke; mkdir -p $d
bash tests/net/tls-certs.sh $d/certs > $d/certs.txt 2>&1 || { cat $d/certs.txt; exit 1; }
cat $d/certs.txt
/py/bin/python3 -I tests/net/tls.py --cert $d/certs/good.pem --key $d/certs/good.key --port 18130 --plain-port 18131 > $d/server.log 2>&1 &
sleep 1
B=.lake/build/bin/net-client
$B call GET https://127.0.0.1:18130/hello ca=$d/certs/ca.pem repeat=3
$B call GET https://localhost:18130/hello ca=$d/certs/ca.pem
$B call POST https://127.0.0.1:18130/echo body=100000 ca=$d/certs/ca.pem
$B call GET https://127.0.0.1:18130/hello
echo "--- server log"; cat $d/server.log
kill %1

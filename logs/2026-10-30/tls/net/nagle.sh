# Is the 80 ms of a first GET over TLS the test server's Nagle algorithm?  Same client, server
# with and without TCP_NODELAY on its accepted sockets.
set -u
d=out/nagle; mkdir -p $d
bash tests/net/tls-certs.sh $d/certs > /dev/null 2>&1 || exit 1
sed 's/^def handle(raw, n, ctx):/def handle(raw, n, ctx):\n    raw.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)/' tests/net/tls.py > $d/tls-nodelay.py
/py/bin/python3 -I tests/net/tls.py --cert $d/certs/good.pem --key $d/certs/good.key --port 18170 --plain-port 18171 > $d/a.log 2>&1 &
/py/bin/python3 -I $d/tls-nodelay.py --cert $d/certs/good.pem --key $d/certs/good.key --port 18172 --plain-port 18173 > $d/b.log 2>&1 &
sleep 1
B=.lake/build/bin/net-client
for i in 1 2 3 4 5; do
  echo "nagle-on  $($B call GET https://127.0.0.1:18170/hello ca=$d/certs/ca.pem | grep '^call 0' | sed 's/ rounds.*//')"
  echo "nodelay   $($B call GET https://127.0.0.1:18172/hello ca=$d/certs/ca.pem | grep '^call 0' | sed 's/ rounds.*//')"
done
kill %1 %2

# Public HTTPS smoke test, in the build container with network (LEAN_HTTP_NETWORK=pasta), using the
# system trust store the client discovers (/etc/ssl/certs/ca-certificates.crt in the image).
B=.lake/build/bin/net-client
getent hosts example.com
for u in https://example.com/ https://www.google.com/ https://github.com/; do
  $B call GET $u repeat=2 | grep "^call\|^trace"
done
# badssl.com's deliberately broken servers: each must be refused, not retried, nothing sent.
for u in https://self-signed.badssl.com/ https://expired.badssl.com/ https://wrong.host.badssl.com/ \
    https://untrusted-root.badssl.com/ https://tls-v1-1.badssl.com:1011/ https://tls-v1-2.badssl.com:1012/; do
  echo "# $u"; $B call GET $u | grep ^call
done

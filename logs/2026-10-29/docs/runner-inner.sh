#!/usr/bin/env bash
# Inside the ubuntu:24.04 container of runner-emulation.sh, as root: the runner's packages and the
# workflow's /etc/hosts step, then, as an unprivileged user, the workflow's elan step and
# scripts/ci.sh.  Copies out/ and the console to /out.
apt-get update -qq && apt-get install -y -qq curl git python3 ca-certificates > /dev/null || exit 1
cat /src/tests/net/hosts >> /etc/hosts || exit 1
useradd --create-home runner || exit 1
cp -r /src /home/runner/w && chown -R runner /home/runner/w || exit 1
cat > /home/runner/run.sh <<'EOF'
cd ~/w || exit 1
d=$(mktemp -d)
curl -sSfL "https://github.com/leanprover/elan/releases/download/$ELAN_VERSION/elan-x86_64-unknown-linux-gnu.tar.gz" \
  | tar -xz -C "$d" || exit 1
"$d/elan-init" -y --no-modify-path --default-toolchain none || exit 1
export PATH=$HOME/.elan/bin:$PATH
python3 --version; id
scripts/ci.sh
EOF
su runner --preserve-environment --command 'HOME=/home/runner bash /home/runner/run.sh' > /out/console.txt 2>&1
rc=$?
cp -r /home/runner/w/out/. /out/
echo "exit status $rc" >> /out/console.txt
exit $rc

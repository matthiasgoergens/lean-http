#!/usr/bin/env bash
# Runs the CI workflow's steps as a GitHub runner would, as far as that can be had here: in a fresh
# ubuntu:24.04 container on the build host, with network, as an unprivileged user, without vendor/
# (so scripts/ci.sh fetches lean4) and without a toolchain (so elan, pinned as in the workflow,
# installs it).  The workflow's preparation (the sysctl, the names in /etc/hosts) is done as on the
# runner: the sysctl through podman, the names as root before switching user (runner-inner.sh).
#
# Usage, from the laptop at the root of the tree: bash logs/2026-10-29/docs/runner-emulation.sh
# Output: ~/lean-http-docs-runner-out/ on the build host (copy it back with rsync).
here=$(cd "$(dirname "$0")/../../.." && pwd) || exit 1
host=${LEAN_HTTP_HOST:-$(head -n 1 "$here/.build-host")}
elan=$(sed --quiet 's/^ *ELAN_VERSION: //p' "$here/.github/workflows/ci.yml")
[ -n "$elan" ] || { echo "no ELAN_VERSION in the workflow" >&2; exit 1; }
rsync --archive --delete --exclude .lake --exclude .git --exclude logs --exclude out --exclude vendor \
  --exclude .build-host "$here/" "$host:lean-http-docs-runner/" || exit 1
ssh "$host" 'rm -rf ~/lean-http-docs-runner-out && mkdir ~/lean-http-docs-runner-out' || exit 1
scp -q "$here/logs/2026-10-29/docs/runner-inner.sh" "$host:lean-http-docs-runner-out/" || exit 1
ssh "$host" "batchrun podman --cgroup-manager=cgroupfs run --cgroups=disabled --rm \
  --sysctl net.ipv4.tcp_syn_retries=2 -e ELAN_VERSION=$elan \
  -v \$HOME/lean-http-docs-runner:/src:ro -v \$HOME/lean-http-docs-runner-out:/out \
  docker.io/library/ubuntu:24.04 bash /out/runner-inner.sh"

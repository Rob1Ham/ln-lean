#!/usr/bin/env bash
# Build one module or the whole library under the shared build lock.
set -euo pipefail
export PATH=/dev/shm/btc/elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
cd /home/ubuntu/ln-lean
target="${1:-}"
if [ -n "$target" ]; then
  exec flock -w 900 /tmp/ln-build.lock lake build "$target"
else
  exec flock -w 900 /tmp/ln-build.lock lake build
fi

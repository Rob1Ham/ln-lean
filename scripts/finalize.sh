#!/usr/bin/env bash
# Final integration gate for ln-lean.  Runs after waves A and B.
set -euo pipefail
cd /home/ubuntu/ln-lean
export PATH=/dev/shm/btc/elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH

echo "== vendor integrity =="
./scripts/verify-vendor.sh

echo "== anchor integrity =="
python3 scripts/verify-anchors.py

echo "== policy checks =="
./scripts/check.sh

echo "== regenerate root =="
./scripts/regen-root.sh >/tmp/ln-root.txt
head -40 /tmp/ln-root.txt

echo "== full build =="
flock -w 1800 /tmp/ln-build.lock lake build

echo "== obligation index =="
python3 scripts/collect-obligations.py

echo "== git status =="
git status --short

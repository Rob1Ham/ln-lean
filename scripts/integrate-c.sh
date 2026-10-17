#!/usr/bin/env bash
# Wave-C integration gate.  Run only after scripts/watch-c.sh reports C_DONE.
set -uo pipefail
cd /home/ubuntu/ln-lean
export PATH=/dev/shm/btc/elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH

echo "== wave-C per-module closure =="
python3 scripts/check-wave-c.py --build || exit 1

echo "== regenerate root =="
./scripts/regen-root.sh >/tmp/ln-c-root.txt
head -20 /tmp/ln-c-root.txt

echo "== full build =="
flock -w 1800 /tmp/ln-build.lock lake build >/tmp/ln-c-full-build.log 2>&1
rc=$?
tail -20 /tmp/ln-c-full-build.log
[ "$rc" -eq 0 ] || exit "$rc"

echo "== policy and anchor gates =="
./scripts/verify-vendor.sh || exit 1
./scripts/check.sh || exit 1
python3 scripts/verify-anchors.py || exit 1

echo "== indexes =="
python3 scripts/collect-obligations.py
python3 scripts/collect-anchors.py

echo "== git status =="
git status --short
exit 0

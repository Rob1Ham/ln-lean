#!/usr/bin/env bash
# Final integration gate for ln-lean.  Runs after waves A and B.
# It never hides a failed build: the report is generated, then the script
# exits with the build's return code.
set -uo pipefail
cd /home/ubuntu/ln-lean
export PATH=/dev/shm/btc/elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH

echo "== vendor integrity =="
./scripts/verify-vendor.sh || exit 1

echo "== anchor integrity =="
python3 scripts/verify-anchors.py || exit 1

echo "== policy checks =="
./scripts/check.sh || exit 1

echo "== wave presence =="
python3 scripts/check-wave-a.py
python3 scripts/check-wave-b.py

echo "== regenerate root =="
./scripts/regen-root.sh >/tmp/ln-root.txt
head -40 /tmp/ln-root.txt

echo "== full build =="
set +e
flock -w 1800 /tmp/ln-build.lock lake build >/tmp/ln-final-build.log 2>&1
rc=$?
set -e
tail -30 /tmp/ln-final-build.log

echo "== obligation index =="
python3 scripts/collect-obligations.py
python3 scripts/collect-anchors.py

echo "== integrator report =="
BUILD_RC="$rc" python3 scripts/make-report.py

echo "== git status =="
git status --short

exit "$rc"

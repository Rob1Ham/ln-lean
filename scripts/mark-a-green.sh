#!/usr/bin/env bash
# Mark wave A green.  This is the gate the 32 wave-B wrappers wait on.
# It refuses to write the sentinel unless the vendor snapshot is intact, all
# wave-A modules build, and the static policy checks pass.
set -euo pipefail
cd /home/ubuntu/ln-lean
export PATH=/dev/shm/btc/elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH

echo "== vendor =="
./scripts/verify-vendor.sh

echo "== wave A presence and build =="
python3 scripts/check-wave-a.py --build

echo "== policy =="
./scripts/check.sh

stamp="$(date -u +%FT%TZ)"
{
  echo "A-GREEN ${stamp}"
  echo "modules=35"
  echo "vendor=ok"
  echo "check=ok"
} > agents/status/A-GREEN

git add agents/status/A-GREEN
git -c user.name='LN Integrator' -c user.email='integrator@ln-lean.local' \
  commit -m "[LN-A] wave A green: 35 modules build, checks pass ${stamp}" >/dev/null

echo "wave A green at ${stamp}; wave-B gate opened"

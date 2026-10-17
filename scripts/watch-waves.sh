#!/usr/bin/env bash
set -uo pipefail
cd /home/ubuntu/ln-lean
while ! grep -q 'DONE wave=A' agents/status/A.status 2>/dev/null; do sleep 20; done
echo "A_DONE $(date -u +%FT%TZ)"
while [ "$(grep -c 'exit=' agents/status/B.status 2>/dev/null || echo 0)" -lt 32 ]; do sleep 30; done
echo "B_DONE $(date -u +%FT%TZ)"
grep -c 'exit=0' agents/status/B.status || true

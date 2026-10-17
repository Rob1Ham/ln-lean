#!/usr/bin/env bash
# Wait for all 16 wave-C agents to write an exit line.
set -uo pipefail
cd /home/ubuntu/ln-lean
want="${LN_C_AGENTS:-16}"
while true; do
  got=$(grep -c 'exit=' agents/status/C.status 2>/dev/null || true)
  if [ "${got:-0}" -ge "$want" ]; then
    ok=$(grep -c 'exit=0' agents/status/C.status 2>/dev/null || true)
    echo "C_DONE $(date -u +%FT%TZ)"
    echo "exits=$got ok=$ok"
    break
  fi
  sleep 30
done

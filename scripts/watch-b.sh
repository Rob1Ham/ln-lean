#!/usr/bin/env bash
set -uo pipefail
cd /home/ubuntu/ln-lean
while :; do
  n=$(awk '/exit=/{c++} END{print c+0}' agents/status/B.status 2>/dev/null)
  if [ "${n:-0}" -ge 32 ]; then break; fi
  sleep 60
done
echo "B_DONE $(date -u +%FT%TZ)"
awk '/exit=/{c++} /exit=0/{ok++} END{print "exits=" c+0, "ok=" ok+0}' agents/status/B.status

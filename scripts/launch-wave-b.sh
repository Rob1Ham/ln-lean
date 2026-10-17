#!/usr/bin/env bash
# Fan out the 32 wave-B proof-scaffold agents.
# Each wrapper waits for the wave-A gate, then starts one OpenCode session.
set -uo pipefail
cd /home/ubuntu/ln-lean

if pgrep -f '[r]un-b-agent.sh B[0-9][0-9]' >/dev/null 2>&1; then
  echo "wave B already running; refusing to duplicate" >&2
  exit 1
fi

mkdir -p agents/logs agents/status
status="agents/status/B.status"
: > "$status"
echo "START wave=B agents=32 $(date -u +%FT%TZ)" >> "$status"

for brief in agents/briefs/B*.md; do
  name="$(basename "$brief" .md)"
  setsid -f ./scripts/run-b-agent.sh "$name" "$brief" >/dev/null 2>&1
  sleep 1
done

echo "launched 32 wave-B wrappers; they wait for agents/status/A-GREEN" 

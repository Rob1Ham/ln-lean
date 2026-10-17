#!/usr/bin/env bash
# Launch a wave of OpenCode agents on the peer.
# Usage: ./scripts/run-wave.sh A agents/briefs/A*.md
set -uo pipefail
wave="${1:?wave name}"
shift
if [ "$#" -eq 0 ]; then
  echo "no briefs" >&2
  exit 2
fi
cd /home/ubuntu/ln-lean
export PATH="$HOME/.opencode/bin:/dev/shm/btc/elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH"
export OPENCODE_DISABLE_AUTOUPDATE=1
mkdir -p agents/logs agents/status
status="agents/status/${wave}.status"
: > "$status"
echo "START wave=$wave agents=$# $(date -u +%FT%TZ)" >> "$status"

for brief in "$@"; do
  name="$(basename "$brief" .md)"
  (
    timeout "${LN_AGENT_TIMEOUT:-2700}" \
      opencode run --auto -m tff/deepseek-v4.1-flash-1017 \
      --title "LN-${name}" "$(cat "$brief")" \
      > "agents/logs/${name}.log" 2>&1
    rc=$?
    echo "${name} exit=${rc} $(date -u +%FT%TZ)" >> "$status"
  ) &
  sleep 2
done

wait
echo "DONE wave=$wave $(date -u +%FT%TZ)" >> "$status"

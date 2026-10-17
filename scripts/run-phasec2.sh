#!/usr/bin/env bash
# Launch the phase-C wave in the dedicated worktree.
# Usage: ./scripts/run-phasec.sh agents/briefs/PC*.md
set -uo pipefail
cd /home/ubuntu/ln-lean-phasec2
export PATH="$HOME/.opencode/bin:/dev/shm/btc/elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH"
export OPENCODE_DISABLE_AUTOUPDATE=1
mkdir -p agents/logs agents/status agents/reports
status="agents/status/PC2.status"
: > "$status"
echo "START wave=PC2 agents=$# $(date -u +%FT%TZ)" >> "$status"
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
echo "DONE wave=PC2 $(date -u +%FT%TZ)" >> "$status"

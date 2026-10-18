#!/usr/bin/env bash
# Run one repair agent in the shared repair worktree.
# Usage: ./scripts/run-repair-agent.sh R01 agents/briefs/R01.md
set -uo pipefail
name="${1:?agent name}"
brief="${2:?brief path}"
cd /home/ubuntu/ln-lean-repair

export PATH="$HOME/.opencode/bin:/dev/shm/btc/elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH"
export OPENCODE_DISABLE_AUTOUPDATE=1
mkdir -p agents/logs agents/status
status="agents/status/REPAIR.status"

timeout "${LN_AGENT_TIMEOUT:-7200}" \
  opencode run --auto -m tff/deepseek-v4.1-flash-1017 \
  --title "LN-REPAIR-${name}" "$(cat "$brief")" \
  > "agents/logs/${name}.log" 2>&1
rc=$?
echo "${name} exit=${rc} $(date -u +%FT%TZ)" >> "$status"

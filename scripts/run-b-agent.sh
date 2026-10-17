#!/usr/bin/env bash
# Run one wave-B agent, waiting for the wave-A scaffolding gate first.
# Usage: ./scripts/run-b-agent.sh B01 agents/briefs/B01.md
set -uo pipefail
name="${1:?agent name}"
brief="${2:?brief path}"
cd /home/ubuntu/ln-lean

export PATH="$HOME/.opencode/bin:/dev/shm/btc/elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH"
export OPENCODE_DISABLE_AUTOUPDATE=1
mkdir -p agents/logs agents/status
status="agents/status/B.status"

if [ "${LN_SKIP_GATE:-0}" != "1" ]; then
  deadline=$((SECONDS + ${LN_GATE_TIMEOUT:-3600}))
  while :; do
    if grep -q 'DONE wave=A' agents/status/A.status 2>/dev/null; then
      break
    fi
    exits=$(grep -c 'exit=' agents/status/A.status 2>/dev/null || true)
    if [ "${exits:-0}" -ge 8 ]; then
      break
    fi
    if [ "$SECONDS" -ge "$deadline" ]; then
      echo "${name} gate_timeout $(date -u +%FT%TZ)" >> "$status"
      exit 3
    fi
    sleep 20
  done
fi

timeout "${LN_AGENT_TIMEOUT:-3600}" \
  opencode run --auto -m tff/deepseek-v4.1-flash-1017 \
  --title "LN-${name}" "$(cat "$brief")" \
  > "agents/logs/${name}.log" 2>&1
rc=$?
echo "${name} exit=${rc} $(date -u +%FT%TZ)" >> "$status"

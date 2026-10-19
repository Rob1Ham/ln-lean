#!/usr/bin/env bash
# Launch the read-only 32-lane wave-13 review.
#
# R01-R31 run with bounded concurrency (default 8).  R32 is a separate
# synthesis lane and starts only after all 31 evidence lanes have finished.
# Every lane may write exactly one report under agents/reports/wave13-review/.
set -uo pipefail
cd /home/ubuntu/ln-lean-repair

export PATH="$HOME/.opencode/bin:$HOME/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH"
export OPENCODE_DISABLE_AUTOUPDATE=1

mkdir -p agents/logs/wave13-review agents/reports/wave13-review agents/status
status="agents/status/wave13-review.status"
export status

if pgrep -f '[o]pencode run.*wave13-review' >/dev/null 2>&1; then
  echo "wave13-review already running; refusing to duplicate" >&2
  exit 1
fi

if [ ! -f agents/briefs/wave13-review/R01.md ]; then
  echo "missing review briefs; run scripts/gen-review-wave-13.py first" >&2
  exit 2
fi

: > "$status"
echo "START wave=13-review lanes=32 concurrency=${REVIEW_CONCURRENCY:-8} $(date -u +%FT%TZ)" >> "$status"

run_lane() {
  local brief="$1"
  local name
  name="$(basename "$brief" .md)"
  local log="agents/logs/wave13-review/${name}.log"
  timeout "${REVIEW_LANE_TIMEOUT:-1800}" \
    opencode run --auto -m tff/deepseek-v4.1-flash-1017 \
    --title "LN-REVIEW-${name}" "$(cat "$brief")" > "$log" 2>&1
  local rc=$?
  echo "${name} exit=${rc} $(date -u +%FT%TZ)" >> "$status"
  return 0
}

export -f run_lane

# R01-R31: evidence and gap reports.
printf '%s\0' agents/briefs/wave13-review/R{01..31}.md |
  xargs -0 -n1 -P "${REVIEW_CONCURRENCY:-8}" bash -c 'run_lane "$1"' _

# R32: synthesis over the completed reports.
if [ -f agents/briefs/wave13-review/R32.md ]; then
  run_lane agents/briefs/wave13-review/R32.md
else
  echo "R32 exit=missing-brief $(date -u +%FT%TZ)" >> "$status"
fi

# Report completeness check, without treating a failed lane as a script crash.
python3 - <<'PY' >> "$status" 2>&1
import json
from pathlib import Path
manifest = json.loads(Path("agents/swarm/WAVE-13-REVIEW.json").read_text())
missing = []
for lane in manifest["lanes"]:
    p = Path(lane["report"])
    if not p.exists() or p.stat().st_size < 200:
        missing.append(f"{lane['id']}:{p}")
print(f"REPORTS total={len(manifest['lanes'])} missing_or_small={len(missing)}")
for m in missing:
    print("MISSING", m)
PY

echo "DONE wave=13-review $(date -u +%FT%TZ)" >> "$status"

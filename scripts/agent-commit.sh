#!/usr/bin/env bash
# Commit only the named paths, under the shared git lock.
# Usage: MSG="[LN-A1] ..." ./scripts/agent-commit.sh LN-A1 path1 [path2 ...]
set -euo pipefail
name="${1:-LN-AGENT}"
shift || true
cd /home/ubuntu/ln-lean
if [ "$#" -eq 0 ]; then
  echo "agent-commit: no paths given" >&2
  exit 2
fi
msg="${MSG:-[$name] agent work $(date -u +%FT%TZ)}"
exec 9>/tmp/ln-git.lock
flock -w 300 9
git add -- "$@"
git commit -m "$msg"

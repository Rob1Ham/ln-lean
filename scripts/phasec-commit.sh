#!/usr/bin/env bash
# Commit only the named paths on the phase-c worktree, under the shared git lock.
# Usage: MSG="[PC01] ..." ./scripts/phasec-commit.sh PC01 path1 [path2 ...]
set -euo pipefail
name="${1:-PC}"
shift || true
cd /home/ubuntu/ln-lean-phasec
if [ "$#" -eq 0 ]; then
  echo "phasec-commit: no paths given" >&2
  exit 2
fi
msg="${MSG:-[$name] phase-C proof work $(date -u +%FT%TZ)}"
exec 9>/tmp/ln-git.lock
flock -w 300 9
git add -- "$@"
git commit -m "$msg"

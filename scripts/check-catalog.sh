#!/usr/bin/env bash
# Thin wrapper around the exact source-level catalog checker.
set -euo pipefail
cd "$(dirname "$0")/.."
exec python3 scripts/check-catalog.py "$@"

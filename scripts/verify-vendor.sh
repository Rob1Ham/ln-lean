#!/usr/bin/env bash
# Verify that the read-only L1 reference snapshot has not been modified.
#
# Usage: ./scripts/verify-vendor.sh [SNAPSHOT_DIR]
#   SNAPSHOT_DIR defaults to vendor/btc-lean-core. The tracked checksum list is
#   always vendor/VENDOR-SHA256; the optional argument only selects which tree
#   is compared against it, so fetch-vendor.sh can verify a staged candidate
#   with exactly the same check before installing it.
set -euo pipefail
cd "$(dirname "$(readlink -f "$0")")/.."

root="${1:-vendor/btc-lean-core}"
manifest="vendor/VENDOR-SHA256"
if [ ! -f "$manifest" ]; then
  echo "verify-vendor: missing $manifest" >&2
  exit 2
fi
if [ ! -d "$root" ]; then
  echo "verify-vendor: missing snapshot directory $root" >&2
  exit 2
fi

now_file="$(mktemp "${TMPDIR:-/tmp}/ln-vendor-now.XXXXXX")"
diff_file="$(mktemp "${TMPDIR:-/tmp}/ln-vendor-diff.XXXXXX")"
trap 'rm -f "$now_file" "$diff_file"' EXIT

# Source files only; .lake is a build cache and is intentionally excluded.
(cd "$root" && find . -path ./.lake -prune -o -type f -print0 \
  | sort -z | xargs -0 sha256sum) > "$now_file"

if diff -u "$manifest" "$now_file" >"$diff_file"; then
  echo "verify-vendor: OK ($(wc -l < "$manifest") files)"
else
  echo "verify-vendor: MODIFIED" >&2
  cat "$diff_file" >&2
  exit 1
fi

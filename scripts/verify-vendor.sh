#!/usr/bin/env bash
# Verify that the read-only L1 reference snapshot has not been modified.
set -euo pipefail
cd /home/ubuntu/ln-lean

manifest="vendor/VENDOR-SHA256"
if [ ! -f "$manifest" ]; then
  echo "verify-vendor: missing $manifest" >&2
  exit 2
fi

# Source files only; .lake is a build cache and is intentionally excluded.
(cd vendor/btc-lean-core && find . -path ./.lake -prune -o -type f -print0 \
  | sort -z | xargs -0 sha256sum) > /tmp/ln-vendor-now.sha256

if diff -u "$manifest" /tmp/ln-vendor-now.sha256 >/tmp/ln-vendor.diff; then
  echo "verify-vendor: OK ($(wc -l < "$manifest") files)"
else
  echo "verify-vendor: MODIFIED" >&2
  cat /tmp/ln-vendor.diff >&2
  exit 1
fi

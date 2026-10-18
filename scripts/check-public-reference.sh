#!/usr/bin/env bash
# Check the local public btc-lean reference and the vendor snapshot.
#
# This is a read-only check:
#   * it never writes to vendor/ or to the public clone;
#   * it is offline by default (the clone is already present);
#   * it verifies that the LN build does not depend on the public clone.
#
# Usage: ./scripts/check-public-reference.sh [--fetch]
#   --fetch   optionally refresh origin/main over the network, then re-check.
#
# The expected values are the L01 pin (see refs/PINNED.md, docs/L1-PIN.md).
set -euo pipefail
cd "$(dirname "$(readlink -f "$0")")/.."

EXPECTED_URL="https://github.com/Rob1Ham/btc-lean"
EXPECTED_COMMIT="4f5c4f858fb9ca0743042644453cfa92d30dd271"
EXPECTED_TAG="data-2026.10.17"
CLONE="${BTC_LEAN_PUBLIC:-/home/ubuntu/btc-lean-public}"
FETCH=0

usage() {
  echo "usage: $0 [--fetch]" >&2
}

for arg in "$@"; do
  case "$arg" in
    --fetch) FETCH=1 ;;
    -h|--help) usage; exit 0 ;;
    *) usage; exit 2 ;;
  esac
done

fail() {
  echo "check-public-reference: FAIL: $*" >&2
  exit 1
}

norm_url() {
  # Accept https://host/owner/repo and .../repo.git and a trailing slash.
  printf '%s' "$1" | sed -e 's#/*$##' -e 's#\.git$##'
}

echo "public clone: $CLONE"

[ -e "$CLONE" ] || fail "clone not found at $CLONE"
[ -e "$CLONE/.git" ] || fail "$CLONE is not a git worktree"

git -C "$CLONE" rev-parse --git-dir >/dev/null 2>&1 \
  || fail "$CLONE is not a readable git worktree"

if [ "$FETCH" -eq 1 ]; then
  echo "fetching origin main (network opt-in) ..."
  git -C "$CLONE" fetch --quiet origin main \
    || fail "network fetch failed; rerun without --fetch for an offline check"
fi

remote_url="$(git -C "$CLONE" remote get-url origin 2>/dev/null || true)"
[ -n "$remote_url" ] || fail "origin remote is missing"
[ "$(norm_url "$remote_url")" = "$(norm_url "$EXPECTED_URL")" ] \
  || fail "origin is '$remote_url', expected '$EXPECTED_URL'"
echo "origin:        OK ($remote_url)"

head_commit="$(git -C "$CLONE" rev-parse HEAD)" \
  || fail "cannot resolve HEAD"
[ "$head_commit" = "$EXPECTED_COMMIT" ] \
  || fail "HEAD is $head_commit, expected $EXPECTED_COMMIT"
git -C "$CLONE" cat-file -e "$EXPECTED_COMMIT^{commit}" 2>/dev/null \
  || fail "expected commit object is not present locally"
echo "HEAD:          OK ($head_commit)"

branch="$(git -C "$CLONE" rev-parse --abbrev-ref HEAD)"
echo "branch:        $branch"

if git -C "$CLONE" rev-parse -q --verify "refs/tags/$EXPECTED_TAG" >/dev/null; then
  tag_commit="$(git -C "$CLONE" rev-parse "refs/tags/$EXPECTED_TAG^{commit}")"
  [ "$tag_commit" = "$EXPECTED_COMMIT" ] \
    || fail "tag $EXPECTED_TAG is $tag_commit, expected $EXPECTED_COMMIT"
  echo "tag:           OK ($EXPECTED_TAG)"
else
  echo "tag:           WARN ($EXPECTED_TAG not present locally)"
fi

[ -d "$CLONE/spec/core" ] || fail "missing $CLONE/spec/core"
core_files="$(find "$CLONE/spec/core" -name '*.lean' | wc -l)"
echo "spec/core:     OK ($core_files .lean files)"

# The public clone must never become a build dependency.
for f in lakefile.lean lean-toolchain; do
  [ -f "$f" ] || continue
  if grep -q -e 'btc-lean-public' -e 'refs/btc-lean' "$f"; then
    fail "$f references the public clone; the build must use vendor/ only"
  fi
done
echo "build dep:     OK (lakefile does not reference the public clone)"

# Read-only local reference (untracked symlink); reported, not required.
if [ -L refs/btc-lean ]; then
  echo "symlink:       refs/btc-lean -> $(readlink refs/btc-lean)"
else
  echo "symlink:       WARN (refs/btc-lean is absent; run: ln -s $CLONE refs/btc-lean)"
fi

# Vendor integrity is the gate that protects the build input.
[ -x scripts/verify-vendor.sh ] || fail "scripts/verify-vendor.sh is missing"
if ./scripts/verify-vendor.sh; then
  echo "vendor:        OK"
else
  fail "vendor integrity check failed (see above)"
fi

if [ "$FETCH" -eq 1 ]; then
  echo "check-public-reference: OK (fetched)"
else
  echo "check-public-reference: OK (offline)"
fi

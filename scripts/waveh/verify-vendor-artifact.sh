#!/usr/bin/env bash
# Check a candidate btc-lean-core snapshot directory before it is published or
# installed as the read-only Lake path dependency «core».
#
# This is the publication-side companion to the existing gates:
#
#   scripts/verify-vendor.sh          compares the working snapshot to the
#                                     tracked manifest (digests only)
#   scripts/fetch-vendor.sh           provisions/verifies a snapshot and
#                                     rejects unsafe archive members
#   scripts/waveh/verify-vendor-artifact.sh  (this file) checks a candidate
#                                     artifact directory for the three
#                                     publication facts: exact manifest,
#                                     exact 119-file digest, and no symlinks
#                                     (absolute symlinks are the OPS-04 defect).
#
# The script is read-only: it never writes inside the repository, never edits
# the artifact, never touches Git, and never uses the network. Scratch files
# live in mktemp(1) directories and are removed on exit.
#
# Exit codes:
#   0  artifact verified: manifest canonical, 119/119 digests match, no symlinks
#   1  verification failure: digest mismatch, extra/missing file, malformed
#      manifest, non-directory artifact, or prohibited symlink
#   2  usage/configuration error (bad option, missing manifest)
#   3  artifact directory is missing (the "no artifact" case)
set -euo pipefail

SCRIPT_DIR="$(dirname "$(readlink -f "$0")")"
REPO_ROOT="$(readlink -f "$SCRIPT_DIR/../..")"
cd "$REPO_ROOT"

EXPECTED_FILES=119
DEFAULT_ARTIFACT="vendor/btc-lean-core"
DEFAULT_MANIFEST="vendor/VENDOR-SHA256"

ARTIFACT="$DEFAULT_ARTIFACT"
MANIFEST="$DEFAULT_MANIFEST"
STRICT_ROOT=0

EXIT_OK=0
EXIT_FAIL=1
EXIT_USAGE=2
EXIT_MISSING=3

TMP_DIR=""
cleanup() {
  if [ -n "$TMP_DIR" ] && [ -d "$TMP_DIR" ]; then
    rm -rf -- "$TMP_DIR"
  fi
}
trap cleanup EXIT

usage() {
  cat <<'EOF'
Usage: scripts/waveh/verify-vendor-artifact.sh [options]

Verify a candidate btc-lean-core snapshot directory against the tracked
119-file manifest without modifying it, committing it, or using the network.

Options:
  --artifact DIR    Candidate snapshot directory (default: vendor/btc-lean-core).
                    Relative paths are resolved from the repository root.
  --manifest FILE   Per-file checksum manifest (default: vendor/VENDOR-SHA256).
  --strict-root     Fail if the artifact path itself is a symlink. By default a
                    symlinked root is reported as a note (local checkouts link
                    vendor/btc-lean-core); symlinks inside the tree always fail.
  -h, --help        Show this help.

Checks (all required):
  1. The artifact exists, is a directory, and contains lakefile.lean and
     Bitcoin.lean (so it is a btc-lean core snapshot).
  2. The manifest has exactly 119 entries, each "SHA256  ./relative/path",
     with lowercase hex, no absolute/traversal/.lake/.git entries, no
     duplicates, and LC_ALL=C path order.
  3. Each regular source file under the artifact (top-level .lake and .git
     pruned, matching scripts/verify-vendor.sh) hashes to the manifest entry;
     there are no extra or missing files.
  4. No symlinks exist inside the scanned tree. Absolute targets are reported
     as "absolute symlink" (OPEN-ISSUES OPS-04); relative symlinks are also
     rejected because scripts/fetch-vendor.sh rejects every non-regular
     archive member.

Exit codes:
  0  verified
  1  integrity/format failure, or a prohibited symlink
  2  usage/configuration error
  3  artifact directory missing

The script is reproducible: it prints only repository-relative paths, sorts
with LC_ALL=C, and its output depends only on the manifest and tree contents.
EOF
}

die_usage() {
  printf 'verify-vendor-artifact: %s\n\n' "$*" >&2
  usage >&2
  exit "$EXIT_USAGE"
}

fail() {
  printf 'verify-vendor-artifact: FAIL: %s\n' "$*" >&2
  exit "$EXIT_FAIL"
}

need_value() {
  [ "$#" -ge 2 ] || die_usage "$1 needs a value"
}

while [ "$#" -gt 0 ]; do
  case "$1" in
    --artifact)
      need_value "$@"
      ARTIFACT="$2"
      shift
      ;;
    --artifact=*)
      ARTIFACT="${1#*=}"
      ;;
    --manifest)
      need_value "$@"
      MANIFEST="$2"
      shift
      ;;
    --manifest=*)
      MANIFEST="${1#*=}"
      ;;
    --strict-root)
      STRICT_ROOT=1
      ;;
    -h|--help)
      usage
      exit "$EXIT_OK"
      ;;
    --)
      shift
      [ "$#" -eq 0 ] || die_usage "unexpected positional argument: $1"
      ;;
    -*)
      die_usage "unknown option: $1"
      ;;
    *)
      die_usage "unexpected positional argument: $1"
      ;;
  esac
  shift
done

case "$ARTIFACT" in
  ""|"/"|".")
    die_usage "unsafe --artifact: '$ARTIFACT'"
    ;;
esac
case "$MANIFEST" in
  "") die_usage "--manifest must not be empty" ;;
esac

# ---------------------------------------------------------------------------
# 0. inputs
# ---------------------------------------------------------------------------

[ -f "$MANIFEST" ] || die_usage "missing manifest: $MANIFEST (run from a complete checkout)"

if [ ! -e "$ARTIFACT" ]; then
  cat >&2 <<EOF
verify-vendor-artifact: artifact not found: $ARTIFACT
verify-vendor-artifact: this is the OPS-01 "no snapshot" case. Provision a
verify-vendor-artifact: candidate first, for example:
verify-vendor-artifact:   scripts/fetch-vendor.sh --from-tarball /path/to/btc-lean-core.tar.gz
verify-vendor-artifact: then re-run this script with --artifact <installed-dir>.
EOF
  exit "$EXIT_MISSING"
fi

[ -d "$ARTIFACT" ] || fail "artifact is not a directory: $ARTIFACT"
[ -f "$ARTIFACT/lakefile.lean" ] \
  || fail "not a btc-lean core snapshot (missing lakefile.lean): $ARTIFACT"
[ -f "$ARTIFACT/Bitcoin.lean" ] \
  || fail "not a btc-lean core snapshot (missing Bitcoin.lean): $ARTIFACT"

if [ -L "$ARTIFACT" ]; then
  root_target="$(readlink -- "$ARTIFACT")"
  case "$root_target" in
    /*)
      root_kind="absolute symlink"
      ;;
    *)
      root_kind="relative symlink"
      ;;
  esac
  if [ "$root_kind" = "absolute symlink" ]; then root_article="an"; else root_article="a"; fi
  if [ "$STRICT_ROOT" -eq 1 ]; then
    fail "artifact root is $root_article $root_kind (prohibited for a published artifact): $ARTIFACT -> $root_target"
  fi
  printf 'verify-vendor-artifact: note: artifact root is %s %s (%s -> %s); scanning the resolved tree\n' \
    "$root_article" "$root_kind" "$ARTIFACT" "$root_target" >&2
fi

TMP_DIR="$(mktemp -d "${TMPDIR:-/tmp}/ln-vendor-artifact.XXXXXX")"

# ---------------------------------------------------------------------------
# 1. manifest shape
# ---------------------------------------------------------------------------

line_count="$(wc -l < "$MANIFEST" | tr -d ' ')"
[ "$line_count" -eq "$EXPECTED_FILES" ] \
  || fail "manifest $MANIFEST has $line_count entries; expected exactly $EXPECTED_FILES"

format_errors="$TMP_DIR/manifest-format"
awk '
  NF != 2 {
    printf "line %d: expected two space-separated fields\n", NR
    next
  }
  length($1) != 64 || $1 !~ /^[0-9a-f]+$/ {
    printf "line %d: digest is not 64 lowercase hex characters\n", NR
    next
  }
  $2 !~ /^\.\/[^\/]/ {
    printf "line %d: path does not start with ./<name>: %s\n", NR, $2
    next
  }
  $2 ~ /\/\// {
    printf "line %d: path contains //: %s\n", NR, $2
    next
  }
  $2 ~ /\\/ {
    printf "line %d: path contains a backslash: %s\n", NR, $2
    next
  }
  $2 ~ /(^|\/)\.\.(\/|$)/ {
    printf "line %d: path escapes the artifact: %s\n", NR, $2
    next
  }
  $2 ~ /^\.\/(\.lake|\.git)(\/|$)/ {
    printf "line %d: path is build/VCS state, not source: %s\n", NR, $2
    next
  }
' "$MANIFEST" > "$format_errors"
if [ -s "$format_errors" ]; then
  {
    printf 'verify-vendor-artifact: FAIL: malformed manifest %s\n' "$MANIFEST"
    sed -n '1,10p' "$format_errors"
  } >&2
  exit "$EXIT_FAIL"
fi

awk '{print $2}' "$MANIFEST" > "$TMP_DIR/manifest-paths"
if [ -n "$(LC_ALL=C sort "$TMP_DIR/manifest-paths" | uniq -d | sed -n '1,1p')" ]; then
  {
    printf 'verify-vendor-artifact: FAIL: duplicate paths in manifest %s\n' "$MANIFEST"
    LC_ALL=C sort "$TMP_DIR/manifest-paths" | uniq -d | sed -n '1,10p'
  } >&2
  exit "$EXIT_FAIL"
fi
LC_ALL=C sort "$TMP_DIR/manifest-paths" > "$TMP_DIR/manifest-paths-sorted"
if ! cmp -s "$TMP_DIR/manifest-paths" "$TMP_DIR/manifest-paths-sorted"; then
  fail "manifest entries are not in LC_ALL=C path order: $MANIFEST"
fi

# Manifest hash for the report/evidence line. It is stable for a given pin.
manifest_sha="$(sha256sum "$MANIFEST" | awk '{print $1}')"

# ---------------------------------------------------------------------------
# 2. digest of the candidate tree
# ---------------------------------------------------------------------------

# Tab-separated "path<TAB>digest" so paths containing spaces (if any) survive.
awk '{print substr($0, 67) "\t" substr($0, 1, 64)}' "$MANIFEST" \
  | LC_ALL=C sort -t "$(printf '\t')" -k1,1 > "$TMP_DIR/expected"

(
  cd "$ARTIFACT"
  find . \( -path ./.lake -o -path ./.git \) -prune -o -type f -print0 \
    | LC_ALL=C sort -z \
    | xargs -0 -r sha256sum \
    | awk '{print substr($0, 67) "\t" substr($0, 1, 64)}'
) | LC_ALL=C sort -t "$(printf '\t')" -k1,1 > "$TMP_DIR/actual"

awk -F'\t' '
  NR == FNR { expected[$1] = $2; next }
  {
    if ($1 in expected) {
      if (expected[$1] != $2) print "changed\t" $1
      delete expected[$1]
    } else {
      print "extra\t" $1
    }
  }
  END {
    for (path in expected) print "missing\t" path
  }
' "$TMP_DIR/expected" "$TMP_DIR/actual" \
  | LC_ALL=C sort > "$TMP_DIR/digest-problems"

digest_counts="$(awk -F'\t' '
  { count[$1]++ }
  END {
    printf "%d %d %d", count["missing"], count["extra"], count["changed"]
  }
' "$TMP_DIR/digest-problems")"
read -r n_missing n_extra n_changed <<< "$digest_counts"

# ---------------------------------------------------------------------------
# 3. symlinks inside the scanned tree
# ---------------------------------------------------------------------------

symlink_report="$TMP_DIR/symlinks"
(
  cd "$ARTIFACT"
  find . \( -path ./.lake -o -path ./.git \) -prune -o -type l -print0 2>/dev/null \
    | LC_ALL=C sort -z \
    | while IFS= read -r -d '' link; do
        target="$(readlink -- "$link")"
        case "$target" in
          /*) kind="absolute symlink" ;;
          *)  kind="relative symlink" ;;
        esac
        printf '%s\t%s\t%s\n' "$kind" "$link" "$target"
      done
) > "$symlink_report"
n_symlinks="$(wc -l < "$symlink_report" | tr -d ' ')"
n_absolute="$(awk -F'\t' '$1 == "absolute symlink"' "$symlink_report" | wc -l | tr -d ' ')"

# ---------------------------------------------------------------------------
# 4. report
# ---------------------------------------------------------------------------

printf 'verify-vendor-artifact: artifact: %s\n' "$ARTIFACT"
printf 'verify-vendor-artifact: manifest: %s (%s entries, sha256 %s)\n' \
  "$MANIFEST" "$line_count" "$manifest_sha"
printf 'verify-vendor-artifact: digest: %s/%s files match (%s missing, %s extra, %s changed)\n' \
  "$((EXPECTED_FILES - n_missing - n_changed))" "$EXPECTED_FILES" \
  "$n_missing" "$n_extra" "$n_changed"
printf 'verify-vendor-artifact: symlinks: %s (%s absolute)\n' "$n_symlinks" "$n_absolute"

status=0
if [ "$n_missing" -ne 0 ] || [ "$n_extra" -ne 0 ] || [ "$n_changed" -ne 0 ]; then
  status=1
  show_category() {
    local kind="$1" lines
    lines="$(awk -F'\t' -v k="$kind" '$1 == k {print "  " $2}' "$TMP_DIR/digest-problems")"
    [ -n "$lines" ] || return 0
    printf 'verify-vendor-artifact: %s (up to 5 shown):\n' "$kind"
    printf '%s\n' "$lines" | sed -n '1,5p'
  }
  {
    printf 'verify-vendor-artifact: FAIL: digest does not match %s\n' "$MANIFEST"
    show_category missing
    show_category extra
    show_category changed
  } >&2
fi
if [ "$n_symlinks" -ne 0 ]; then
  status=1
  {
    printf 'verify-vendor-artifact: FAIL: prohibited symlink(s) inside %s\n' "$ARTIFACT"
    printf 'verify-vendor-artifact: %s absolute, %s relative (all symlinks are prohibited)\n' \
      "$n_absolute" "$((n_symlinks - n_absolute))"
    while IFS=$'\t' read -r kind link target; do
      printf 'verify-vendor-artifact:   %s: %s -> %s\n' "$kind" "$link" "$target"
    done < <(sed -n '1,10p' "$symlink_report")
  } >&2
fi

if [ "$status" -ne 0 ]; then
  printf 'verify-vendor-artifact: FAIL\n' >&2
  exit "$EXIT_FAIL"
fi

printf 'verify-vendor-artifact: OK\n'
exit "$EXIT_OK"

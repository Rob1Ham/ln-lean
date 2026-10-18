#!/usr/bin/env bash
# Provision or verify the pinned read-only btc-lean L1 snapshot.
#
# OPS-01 background: vendor/btc-lean-core is excluded by .gitignore (only
# vendor/VENDOR-SHA256 is tracked), and the pinned commit f950806... is not in
# public btc-lean history. A clean public checkout therefore has no build input.
#
# This script never fetches a branch or tag tip. It accepts only an explicit
# local archive, an explicit URL plus its archive SHA-256, or the exact pinned
# commit. Every provisioning path is verified against the tracked per-file
# manifest vendor/VENDOR-SHA256 (119 files) before anything is installed, and
# the installed tree is verified a second time.
#
# Exit codes:
#   0  snapshot present and verified (or provisioned and verified)
#   1  checksum/integrity failure, unsafe archive, or refused installation
#   2  usage/configuration error
#   3  no snapshot and no provisioning input (the CI skip gate)
set -euo pipefail
cd "$(dirname "$(readlink -f "$0")")/.."

PINNED_COMMIT="f95080638ae571a3664f4f41b9b6f6b4cfa7c5eb"
PINNED_REPO="https://github.com/Rob1Ham/btc-lean.git"
DEFAULT_DEST="vendor/btc-lean-core"
MANIFEST="vendor/VENDOR-SHA256"
VERIFY="scripts/verify-vendor.sh"

EXIT_OK=0
EXIT_FAIL=1
EXIT_USAGE=2
EXIT_UNAVAILABLE=3

MODE="verify"
SOURCE=""
DEST="$DEFAULT_DEST"
TARBALL=""
URL=""
ARCHIVE_SHA256=""
REPO="$PINNED_REPO"
COMMIT="$PINNED_COMMIT"
DRY_RUN=0
FORCE=0
ALLOW_HTTP=0
CI=0

STAGE_DIR=""
STAGE_ROOT=""

cleanup() {
  if [ -n "$STAGE_DIR" ] && [ -d "$STAGE_DIR" ]; then
    rm -rf -- "$STAGE_DIR"
  fi
}
trap cleanup EXIT

usage() {
  cat <<'EOF'
Usage: scripts/fetch-vendor.sh [options]

Verify, or provision and verify, the pinned read-only btc-lean L1 snapshot
used as the Lake path dependency «core».

Modes (choose at most one; the default is --check):
  --check                    Verify DEST against vendor/VENDOR-SHA256. No network.
  --from-tarball PATH        Extract a local archive, verify it, then install it.
  --from-git                 Fetch exactly --commit from --repo, never a branch tip.
  --url URL                  Download a published archive; --sha256 is required.

Options:
  --sha256 HEX               Expected SHA-256 of the downloaded/copied archive.
  --repo URL                 Git remote for --from-git (default: pinned btc-lean).
  --commit SHA               Commit for --from-git (default: pinned f950806...).
  --dest DIR                 Verify/install location (default: vendor/btc-lean-core).
  --dry-run                  Extract and verify, but never write DEST.
  --force                    Replace an existing DEST (moved to DEST.bak-*).
  --allow-http               Permit http:// URLs (tests/local mirrors only).
  --ci                       Read VENDOR_ARTIFACT_URL, VENDOR_ARTIFACT_PATH, and
                             VENDOR_ARTIFACT_SHA256 from the environment when no
                             mode is given on the command line.
  -h, --help                 Show this help.

Exit codes:
  0  snapshot present and verified (or provisioned and verified)
  1  checksum/integrity failure, unsafe archive, or refused installation
  2  usage/configuration error
  3  no snapshot and no provisioning input (the CI skip gate)

The per-file manifest is always authoritative. An archive SHA-256, when supplied,
is an additional transport check; it never replaces vendor/VENDOR-SHA256.
EOF
}

die_usage() {
  printf 'fetch-vendor: %s\n\n' "$*" >&2
  usage >&2
  exit "$EXIT_USAGE"
}

die() {
  printf 'fetch-vendor: %s\n' "$*" >&2
  exit "$EXIT_FAIL"
}

note() {
  printf 'fetch-vendor: %s\n' "$*" >&2
}

set_source() {
  if [ -n "$SOURCE" ]; then
    die_usage "choose exactly one source: --check, --from-tarball, --from-git, or --url"
  fi
  SOURCE="$1"
  MODE="$1"
}

need_value() {
  [ "$#" -ge 2 ] || die_usage "$1 needs a value"
}

while [ "$#" -gt 0 ]; do
  case "$1" in
    --check|--verify)
      set_source "verify"
      ;;
    --from-tarball)
      need_value "$@"
      TARBALL="$2"
      set_source "tarball"
      shift
      ;;
    --from-tarball=*)
      TARBALL="${1#*=}"
      set_source "tarball"
      ;;
    --from-git)
      set_source "git"
      ;;
    --url)
      need_value "$@"
      URL="$2"
      set_source "url"
      shift
      ;;
    --url=*)
      URL="${1#*=}"
      set_source "url"
      ;;
    --sha256)
      need_value "$@"
      ARCHIVE_SHA256="$2"
      shift
      ;;
    --sha256=*)
      ARCHIVE_SHA256="${1#*=}"
      ;;
    --repo)
      need_value "$@"
      REPO="$2"
      shift
      ;;
    --repo=*)
      REPO="${1#*=}"
      ;;
    --commit)
      need_value "$@"
      COMMIT="$2"
      shift
      ;;
    --commit=*)
      COMMIT="${1#*=}"
      ;;
    --dest)
      need_value "$@"
      DEST="$2"
      shift
      ;;
    --dest=*)
      DEST="${1#*=}"
      ;;
    --dry-run)
      DRY_RUN=1
      ;;
    --force)
      FORCE=1
      ;;
    --allow-http)
      ALLOW_HTTP=1
      ;;
    --ci)
      CI=1
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

# CI mode: only fill in a source when the command line did not choose one.
if [ "$CI" -eq 1 ] && [ -z "$SOURCE" ]; then
  if [ -n "${VENDOR_ARTIFACT_URL:-}" ] && [ -n "${VENDOR_ARTIFACT_PATH:-}" ]; then
    die_usage "set only one of VENDOR_ARTIFACT_URL and VENDOR_ARTIFACT_PATH"
  elif [ -n "${VENDOR_ARTIFACT_URL:-}" ]; then
    URL="$VENDOR_ARTIFACT_URL"
    ARCHIVE_SHA256="${VENDOR_ARTIFACT_SHA256:-}"
    MODE="url"
    SOURCE="url"
  elif [ -n "${VENDOR_ARTIFACT_PATH:-}" ]; then
    TARBALL="$VENDOR_ARTIFACT_PATH"
    ARCHIVE_SHA256="${VENDOR_ARTIFACT_SHA256:-}"
    MODE="tarball"
    SOURCE="tarball"
  fi
fi

if [ -n "$ARCHIVE_SHA256" ] && { [ "$MODE" = "verify" ] || [ "$MODE" = "git" ]; }; then
  die_usage "--sha256 only applies to --from-tarball or --url"
fi

# Normalise and validate the archive hash.
if [ -n "$ARCHIVE_SHA256" ]; then
  ARCHIVE_SHA256="$(printf '%s' "$ARCHIVE_SHA256" | tr '[:upper:]' '[:lower:]')"
  case "$ARCHIVE_SHA256" in
    *[!0-9a-f]*|"")
      die_usage "--sha256 must be 64 hexadecimal characters"
      ;;
  esac
  [ "${#ARCHIVE_SHA256}" -eq 64 ] \
    || die_usage "--sha256 must be 64 hexadecimal characters"
fi

# Refuse destinations that could damage the repository or this script's own
# staging area.
case "$DEST" in
  ""|"/"|"."|"./")
    die_usage "unsafe --dest: '$DEST'"
    ;;
esac
dest_abs="$(readlink -f "$DEST" 2>/dev/null || printf '%s' "$DEST")"
[ "$dest_abs" != "$PWD" ] || die_usage "refusing to use the repository root as --dest"

[ -f "$MANIFEST" ] || die "missing $MANIFEST; run this script from a complete checkout"
[ -x "$VERIFY" ] || die "missing executable $VERIFY"

# ---------------------------------------------------------------------------
# helpers
# ---------------------------------------------------------------------------

check_archive_hash() {
  local file="$1" actual
  if [ -z "$ARCHIVE_SHA256" ]; then
    note "no archive SHA-256 supplied; the 119-file manifest is the integrity gate"
    return 0
  fi
  actual="$(sha256sum "$file" | awk '{print $1}')"
  if [ "$actual" != "$ARCHIVE_SHA256" ]; then
    die "archive SHA-256 mismatch: got $actual, expected $ARCHIVE_SHA256"
  fi
  note "archive SHA-256 OK ($actual)"
}

verify_root() {
  local root="$1"
  [ -d "$root" ] || die "snapshot directory not found: $root"
  [ -f "$root/lakefile.lean" ] \
    || die "not a btc-lean core snapshot (missing lakefile.lean): $root"
  if ! "$VERIFY" "$root"; then
    die "checksum verification failed for $root (diff against $MANIFEST is above)"
  fi
}

# A published snapshot is source-only; never install someone's build cache.
strip_build_cache() {
  rm -rf -- "$1/.lake" "$1/.git"
}

# Print the directory that contains lakefile.lean inside a staging tree.
snapshot_root() {
  local base="$1" found=() f
  if [ -f "$base/lakefile.lean" ]; then
    printf '%s\n' "$base"
    return 0
  fi
  if [ -f "$base/spec/core/lakefile.lean" ] && [ -f "$base/spec/core/Bitcoin.lean" ]; then
    printf '%s\n' "$base/spec/core"
    return 0
  fi
  while IFS= read -r -d '' f; do
    found+=("$(dirname "$f")")
  done < <(find "$base" -name lakefile.lean -type f -print0 2>/dev/null || true)
  if [ "${#found[@]}" -eq 1 ]; then
    printf '%s\n' "${found[0]}"
    return 0
  fi
  note "cannot identify the btc-lean core root under $base"
  find "$base" -mindepth 1 -maxdepth 2 -printf '  %y %p\n' >&2 2>/dev/null || true
  return 1
}

# Validate and extract an archive into an existing empty directory.
unpack_archive() {
  local archive="$1" stage="$2"
  [ -f "$archive" ] || die_usage "archive not found: $archive"
  check_archive_hash "$archive"
  python3 - "$archive" "$stage" <<'PY'
import sys
import tarfile

if sys.version_info < (3, 12):
    sys.exit("fetch-vendor: Python 3.12+ is required for safe archive extraction")

archive, dest = sys.argv[1], sys.argv[2]
try:
    tf = tarfile.open(archive, "r:*")
except tarfile.TarError as exc:
    sys.exit(f"fetch-vendor: not a readable tar archive: {exc}")

with tf:
    members = tf.getmembers()
    if not members:
        sys.exit("fetch-vendor: archive is empty")
    for member in members:
        name = member.name
        parts = name.replace("\\", "/").split("/")
        if name.startswith("/") or ".." in parts:
            sys.exit(f"fetch-vendor: unsafe archive member: {name!r}")
        if not (member.isfile() or member.isdir()):
            sys.exit(
                "fetch-vendor: unsupported archive member "
                f"(regular files and directories only): {name!r}; "
                "exclude local convenience symlinks when creating the archive"
            )
    # filter="data" rejects absolute paths, escaping links, and device nodes.
    tf.extractall(path=dest, filter="data")
PY
}

stage_from_tarball() {
  [ -n "$TARBALL" ] || die_usage "--from-tarball needs PATH"
  STAGE_DIR="$(mktemp -d "${TMPDIR:-/tmp}/ln-vendor-stage.XXXXXX")"
  note "extracting $TARBALL into a temporary staging directory"
  unpack_archive "$TARBALL" "$STAGE_DIR"
  STAGE_ROOT="$(snapshot_root "$STAGE_DIR")" \
    || die "cannot locate the btc-lean core snapshot root in $TARBALL"
  strip_build_cache "$STAGE_ROOT"
  verify_root "$STAGE_ROOT"
}

stage_from_url() {
  [ -n "$URL" ] || die_usage "--url needs a URL"
  [ -n "$ARCHIVE_SHA256" ] \
    || die_usage "refusing an unpinned URL: --sha256 (or VENDOR_ARTIFACT_SHA256) is required"
  case "$URL" in
    https://*|file://*)
      ;;
    http://*)
      [ "$ALLOW_HTTP" -eq 1 ] \
        || die_usage "http:// is disabled; use https:// or pass --allow-http for a local mirror"
      ;;
    *)
      die_usage "unsupported URL scheme: $URL"
      ;;
  esac

  STAGE_DIR="$(mktemp -d "${TMPDIR:-/tmp}/ln-vendor-dl.XXXXXX")"
  local archive="$STAGE_DIR/archive"
  note "downloading $URL"
  if ! curl -fsSL --retry 3 --retry-delay 2 --connect-timeout 20 --max-time 900 \
      --proto '=https,file' --proto-redir '=https,file' \
      -o "$archive" "$URL"; then
    die "download failed: $URL"
  fi
  mkdir -p "$STAGE_DIR/unpacked"
  unpack_archive "$archive" "$STAGE_DIR/unpacked"
  STAGE_ROOT="$(snapshot_root "$STAGE_DIR/unpacked")" \
    || die "cannot locate the btc-lean core snapshot root in $URL"
  strip_build_cache "$STAGE_ROOT"
  verify_root "$STAGE_ROOT"
}

stage_from_git() {
  STAGE_DIR="$(mktemp -d "${TMPDIR:-/tmp}/ln-vendor-git.XXXXXX")"
  local repo="$STAGE_DIR/repo" actual src
  note "fetching exactly $COMMIT from $REPO (no branch or tag tip)"
  git init -q "$repo"
  git -C "$repo" remote add origin "$REPO"
  if ! git -C "$repo" fetch -q --depth 1 origin "$COMMIT"; then
    die "commit $COMMIT is not fetchable from $REPO; if it is not public, use --from-tarball or --url"
  fi
  git -C "$repo" checkout -q --detach FETCH_HEAD
  actual="$(git -C "$repo" rev-parse HEAD)"
  [ "$actual" = "$COMMIT" ] || die "fetched $actual, expected $COMMIT"
  [ "$COMMIT" = "$PINNED_COMMIT" ] \
    || die "refusing non-pinned commit $COMMIT (expected $PINNED_COMMIT)"

  src="$(snapshot_root "$repo")" || die "no btc-lean core snapshot in $COMMIT"
  mkdir -p "$STAGE_DIR/root"
  tar -C "$src" --exclude=.git --exclude=.lake -cf - . \
    | tar -C "$STAGE_DIR/root" -xf -
  STAGE_ROOT="$STAGE_DIR/root"
  verify_root "$STAGE_ROOT"
}

install_snapshot() {
  local root="$1" backup="" failed=""
  root="$(readlink -f "$root")"

  if [ -n "$STAGE_DIR" ]; then
    case "$(readlink -f "$DEST" 2>/dev/null || printf '%s' "$DEST")" in
      "$STAGE_DIR"|"$STAGE_DIR"/*) die "refusing --dest inside the staging directory" ;;
    esac
  fi

  if [ "$DRY_RUN" -eq 1 ]; then
    note "DRY RUN: verified candidate at $root; $DEST was not modified"
    exit "$EXIT_OK"
  fi

  if [ -e "$DEST" ]; then
    [ "$FORCE" -eq 1 ] \
      || die "destination exists: $DEST; refusing to replace it (use --force)"
    backup="${DEST}.bak-$(date -u +%Y%m%dT%H%M%SZ)-$$"
    note "moving existing $DEST aside to $backup"
    mv -- "$DEST" "$backup"
  fi

  mkdir -p -- "$(dirname "$DEST")"
  mv -- "$root" "$DEST"

  if ! "$VERIFY" "$DEST"; then
    failed="${DEST}.failed-$(date -u +%Y%m%dT%H%M%SZ)-$$"
    note "verification of the installed tree failed; moving it aside to $failed"
    mv -- "$DEST" "$failed"
    if [ -n "$backup" ]; then
      mv -- "$backup" "$DEST"
      note "restored the previous snapshot at $DEST"
    fi
    die "installation aborted; $DEST is unchanged"
  fi

  note "provisioned $DEST (pinned commit $PINNED_COMMIT)"
  note "read-only by policy: do not edit; re-verify with scripts/verify-vendor.sh"
}

unavailable() {
  cat >&2 <<EOF
fetch-vendor: no pinned btc-lean snapshot at $DEST.
fetch-vendor: pinned commit: $PINNED_COMMIT
fetch-vendor: that commit is NOT in public btc-lean history, so a clean public
fetch-vendor: checkout cannot download it from the public repository.

This is the OPS-01 build-input gap. Supply one explicit, checksummed input:
  scripts/fetch-vendor.sh --from-tarball /path/to/btc-lean-core-$PINNED_COMMIT.tar.gz
  scripts/fetch-vendor.sh --url https://.../btc-lean-core.tar.gz --sha256 <64-hex>
  VENDOR_ARTIFACT_URL=... VENDOR_ARTIFACT_SHA256=... scripts/fetch-vendor.sh --ci
  scripts/fetch-vendor.sh --from-git   # only if the pinned commit is reachable

Every path is verified against $MANIFEST (119 files) before installation.
Use --dry-run to test an input without touching $DEST.
EOF
  exit "$EXIT_UNAVAILABLE"
}

verify_existing() {
  if [ ! -e "$DEST" ]; then
    unavailable
  fi
  [ -d "$DEST" ] || die "$DEST exists but is not a directory"
  [ -f "$DEST/lakefile.lean" ] \
    || die "$DEST exists but is not a btc-lean core snapshot (missing lakefile.lean); remove it or re-provision with --force"
  if ! "$VERIFY" "$DEST"; then
    die "existing snapshot does not match $MANIFEST; do not build this tree until it is re-provisioned"
  fi
  note "OK: $DEST matches $MANIFEST ($(wc -l < "$MANIFEST") files)"
}

# ---------------------------------------------------------------------------
# dispatch
# ---------------------------------------------------------------------------

case "$MODE" in
  verify)
    verify_existing
    ;;
  tarball)
    stage_from_tarball
    install_snapshot "$STAGE_ROOT"
    ;;
  url)
    stage_from_url
    install_snapshot "$STAGE_ROOT"
    ;;
  git)
    stage_from_git
    install_snapshot "$STAGE_ROOT"
    ;;
  *)
    die_usage "unknown mode: $MODE"
    ;;
esac

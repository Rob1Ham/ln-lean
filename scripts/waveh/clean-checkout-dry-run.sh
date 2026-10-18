#!/usr/bin/env bash
# H47 (OPS-01, OPS-03): reproducible clean-checkout / source-gate dry run.
#
# Purpose
# -------
# A clean public checkout of this tree has no `vendor/btc-lean-core` (it is
# gitignored), so `lake build` cannot run there.  This script prints the exact
# gate sequence for that checkout and labels every step as one of:
#
#   SOURCE        must pass on a clean checkout, no vendor input required
#   SOURCE-DEFER  source check that needs the pinned refs/rust-lightning clone
#   VENDOR        vendor provisioning/verification; an absent snapshot is an
#                 explicit skip (fetch-vendor.sh RC 3), not a source failure
#   BUILD         full build / axiom audit; this script NEVER runs it
#
# Default behaviour is print-only: it inspects the tree, prints the plan, and
# exits.  `--run` executes the SOURCE steps in the printed order and never the
# VENDOR or BUILD steps.  No network access, no Git writes (no commit/checkout/
# branch/tag/reset/push/worktree), no build, and no file creation.
#
# Required-input contract
# -----------------------
# If any required source file is missing (or, when the root is a Git worktree,
# untracked, or a required executable bit is absent), the plan is still printed
# and the script exits 1.  A missing vendor snapshot is NOT a missing source
# file: it exits 3 only with --require-vendor (mirrors REQUIRE_VENDOR_BUILD).
#
# Exit codes
#   0  plan printed (print-only), or all runnable source gates passed (--run)
#   1  required source input is missing / untracked / not executable
#   2  usage or configuration error
#   3  vendor snapshot unavailable while --require-vendor was requested
#   4  a source gate failed under --run
#
# Usage
#   scripts/waveh/clean-checkout-dry-run.sh
#   scripts/waveh/clean-checkout-dry-run.sh --run
#   scripts/waveh/clean-checkout-dry-run.sh --root /tmp/ln-lean-clean-check --run
#   REQUIRE_VENDOR_BUILD=true scripts/waveh/clean-checkout-dry-run.sh --root .
#
# This script does not resolve OPS-01 or OPS-03.  It records the distance
# between "source gates pass" and "the tree builds", and leaves tagging, PRs,
# and vendor publication to the maintainer.
set -euo pipefail

export LC_ALL=C
export PYTHONHASHSEED=0
export PYTHONDONTWRITEBYTECODE=1
export TZ=UTC

SCRIPT="$(readlink -f -- "${BASH_SOURCE[0]}")"
DEFAULT_ROOT="$(cd -- "$(dirname -- "$SCRIPT")/../.." && pwd)"

ROOT="$DEFAULT_ROOT"
MODE="print"
KEEP_GOING=0
REQUIRE_TRACKED=1
REQUIRE_VENDOR=0
case "${REQUIRE_VENDOR_BUILD:-false}" in
  true|TRUE|True|1|yes|YES|Yes) REQUIRE_VENDOR=1 ;;
esac

# Required tracked inputs for the source gates.  This list is deliberately
# explicit: a missing path is a clean-checkout failure, not a warning.
REQUIRED_FILES=(
  "lakefile.lean"
  "lean-toolchain"
  "lake-manifest.json"
  "LnLean.lean"
  ".github/workflows/ci.yml"
  "docs/OPEN-ISSUES.md"
  "docs/RELEASE-CHECKLIST.md"
  "refs/PINNED.md"
  "scripts/check-catalog.py"
  "scripts/check.py"
  "scripts/check.sh"
  "scripts/check-final.py"
  "scripts/check-conformance.py"
  "scripts/verify-anchors.py"
  "scripts/verify-vendor.sh"
  "scripts/fetch-vendor.sh"
  "tests/conformance/vectors.json"
  "vendor/VENDOR-SHA256"
)

# Invoked as ./scripts/<name> by the gate sequence, so the executable bit is
# part of the source contract (CI checks the two vendor scripts explicitly).
REQUIRED_EXEC=(
  "scripts/check.sh"
  "scripts/fetch-vendor.sh"
  "scripts/verify-vendor.sh"
)

usage() {
  cat <<'EOF'
Usage: scripts/waveh/clean-checkout-dry-run.sh [options]

Print (default) or execute (--run) the reproducible source-gate sequence for a
clean checkout, and classify the missing vendor snapshot as an explicit skip.

Options:
  --root DIR              Inspect/run against DIR (default: this repository).
  --run                   Execute the runnable SOURCE gates in printed order.
                          Vendor and BUILD steps are still never executed.
  --print                 Print only; do not execute anything (default).
  --keep-going            With --run, continue after a failing source gate.
  --require-vendor        Fail with RC 3 when the vendor snapshot is absent
                          (mirrors CI REQUIRE_VENDOR_BUILD=true).
  --no-require-vendor     Treat an absent vendor snapshot as an explicit skip
                          (default unless REQUIRE_VENDOR_BUILD is true).
  --no-tracked            Do not require required files to be Git-tracked.
  -h, --help              Show this help.

Exit codes:
  0 plan printed / all runnable source gates passed
  1 required source input missing, untracked, or not executable
  2 usage or configuration error
  3 vendor snapshot unavailable while --require-vendor was requested
  4 a source gate failed under --run

Guarantees:
  * no network access (the anchor reference is reported as deferred);
  * no Git writes (read-only `git ls-files`/`rev-parse` only);
  * no `lake build`, no `fetch-vendor.sh` provisioning, no tag, no push;
  * no files are created or modified.
EOF
}

die_usage() {
  printf 'clean-checkout-dry-run: %s\n' "$*" >&2
  printf 'clean-checkout-dry-run: try --help\n' >&2
  exit 2
}

section() {
  printf '\n== %s ==\n' "$*"
}

kv() {
  printf '  %-34s %s\n' "$1" "$2"
}

digest() {
  local rel="$1"
  if [ -f "$ROOT/$rel" ]; then
    ( cd -- "$ROOT" && sha256sum -- "$rel" )
  else
    printf 'MISSING  %s\n' "$rel"
  fi
}

while [ "$#" -gt 0 ]; do
  case "$1" in
    --root)
      [ "$#" -ge 2 ] || die_usage "--root needs a directory"
      ROOT="$2"
      shift
      ;;
    --root=*) ROOT="${1#*=}" ;;
    --run) MODE="run" ;;
    --print|--dry-run) MODE="print" ;;
    --keep-going) KEEP_GOING=1 ;;
    --require-vendor) REQUIRE_VENDOR=1 ;;
    --no-require-vendor) REQUIRE_VENDOR=0 ;;
    --no-tracked) REQUIRE_TRACKED=0 ;;
    -h|--help) usage; exit 0 ;;
    --)
      shift
      [ "$#" -eq 0 ] || die_usage "unexpected argument: $1"
      ;;
    -*) die_usage "unknown option: $1" ;;
    *) die_usage "unexpected argument: $1" ;;
  esac
  shift
done

[ -d "$ROOT" ] || die_usage "--root is not a directory: $ROOT"
ROOT="$(cd -- "$ROOT" && pwd)"

# ---------------------------------------------------------------------------
# read-only inspection
# ---------------------------------------------------------------------------

GIT_ROOT=0
if [ -e "$ROOT/.git" ]; then
  GIT_ROOT=1
fi

vendor_state="absent"
if [ -f "$ROOT/vendor/btc-lean-core/lakefile.lean" ]; then
  vendor_state="present"
fi

refs_state="absent"
refs_head=""
if [ -d "$ROOT/refs/rust-lightning/.git" ]; then
  refs_state="present"
  refs_head="$(git -C "$ROOT/refs/rust-lightning" rev-parse HEAD 2>/dev/null || printf 'unknown')"
fi

lake_state="absent"
lake_detail=""
if [ -L "$ROOT/.lake" ]; then
  lake_state="symlink"
  lake_detail="$(readlink -- "$ROOT/.lake")"
elif [ -d "$ROOT/.lake" ]; then
  lake_state="directory"
fi

missing=()
untracked=()
not_exec=()

for rel in "${REQUIRED_FILES[@]}"; do
  if [ ! -e "$ROOT/$rel" ]; then
    missing+=("$rel")
  fi
done

if [ "$GIT_ROOT" -eq 1 ] && [ "$REQUIRE_TRACKED" -eq 1 ] && command -v git >/dev/null 2>&1; then
  for rel in "${REQUIRED_FILES[@]}"; do
    if [ -e "$ROOT/$rel" ] \
      && ! git -C "$ROOT" ls-files --error-unmatch -- "$rel" >/dev/null 2>&1; then
      untracked+=("$rel")
    fi
  done
fi

for rel in "${REQUIRED_EXEC[@]}"; do
  if [ -e "$ROOT/$rel" ] && [ ! -x "$ROOT/$rel" ]; then
    not_exec+=("$rel")
  fi
done

# ---------------------------------------------------------------------------
# header and preflight
# ---------------------------------------------------------------------------

printf 'clean-checkout-dry-run: H47 (OPS-01, OPS-03)\n'
kv "root" "$ROOT"
if [ "$MODE" = "run" ]; then
  kv "mode" "RUN source gates (vendor/build never executed)"
else
  kv "mode" "PRINT ONLY (nothing executed)"
fi
kv "root is git worktree" "$([ "$GIT_ROOT" -eq 1 ] && printf yes || printf no)"
kv "vendor/btc-lean-core" "$vendor_state"
kv "refs/rust-lightning" "$refs_state${refs_head:+ (HEAD $refs_head)}"
kv ".lake" "$lake_state${lake_detail:+ -> $lake_detail} (ignored by the clean-checkout model)"
kv "python3" "$(python3 --version 2>&1 || printf 'not found')"
kv "bash" "$(bash --version 2>/dev/null | head -n 1 || printf 'unknown')"
kv "toolchain file" "$(cat -- "$ROOT/lean-toolchain" 2>/dev/null || printf 'missing')"

section "input digests (reproducibility record)"
for rel in \
  "lakefile.lean" \
  "lean-toolchain" \
  "lake-manifest.json" \
  "vendor/VENDOR-SHA256" \
  "tests/conformance/vectors.json" \
  "scripts/check-catalog.py" \
  "scripts/check.py" \
  "scripts/check-final.py" \
  "scripts/check-conformance.py" \
  "scripts/verify-anchors.py" \
  "scripts/fetch-vendor.sh" \
  "scripts/verify-vendor.sh"; do
  digest "$rel"
done
digest "scripts/waveh/clean-checkout-dry-run.sh"

section "required source files (${#REQUIRED_FILES[@]})"
for rel in "${REQUIRED_FILES[@]}"; do
  if [ -e "$ROOT/$rel" ]; then
    printf '  OK       %s\n' "$rel"
  else
    printf '  MISSING  %s\n' "$rel"
  fi
done

if [ "${#untracked[@]}" -gt 0 ]; then
  printf '\n  UNTRACKED required files (a clean checkout would not contain them):\n'
  for rel in "${untracked[@]}"; do
    printf '  UNTRACKED %s\n' "$rel"
  done
fi
if [ "${#not_exec[@]}" -gt 0 ]; then
  printf '\n  NOT EXECUTABLE required scripts:\n'
  for rel in "${not_exec[@]}"; do
    printf '  NOEXEC    %s\n' "$rel"
  done
fi

# ---------------------------------------------------------------------------
# the gate sequence
# ---------------------------------------------------------------------------

SOURCE_STEPS=7
VENDOR_STEPS=2
BUILD_STEPS=2

section "gate sequence (${SOURCE_STEPS} source, ${VENDOR_STEPS} vendor, ${BUILD_STEPS} build)"
printf '  CI mapping: .github/workflows/ci.yml -> jobs.source-gates (1-7) and jobs.build (8-11)\n'
printf '  "SOURCE" checks are the required clean-checkout signal; "VENDOR"/"BUILD" are not run.\n'

cat <<'EOF'

  [1/11] SOURCE      catalog strict audit
          cmd: python3 scripts/check-catalog.py --audit
          expect: RC 0; 48 rows / 48 proved / 79 targets / 0 unresolved
          why: exact declaration, duplicate-id, and proved-row sorry check

  [2/11] SOURCE      source policy and forbidden constructs
          cmd: ./scripts/check.sh
          expect: RC 0; files=204 obligations=82 sorry_in_proofs=0
          why: shared source-level gate (runs scripts/check.py)

  [3/11] SOURCE      file selection and root imports
          cmd: python3 scripts/check-final.py
          expect: RC 0; lean files=204, root imports=202
          why: sparse-selection, module-count, and root-import consistency

  [4/11] SOURCE      wire conformance vectors
          cmd: python3 scripts/check-conformance.py
          expect: RC 0; vectors + mutation controls + committed fixtures only
          why: no network, no Rust toolchain; provenance is skipped without refs

  [5/11] SOURCE      shell syntax and executable bits
          cmd: bash -n scripts/fetch-vendor.sh scripts/verify-vendor.sh \
                 && test -x scripts/fetch-vendor.sh && test -x scripts/verify-vendor.sh
          expect: RC 0
          why: mirrors the CI "Check shell script syntax" step

  [6/11] SOURCE      exact sorry scan (must print nothing)
          cmd: grep -RInE '^[[:space:]]*sorry[[:space:]]*$' LnLean --include='*.lean'
          expect: no output; grep RC 1 (no match) is the pass condition
          why: SWARM-LOOP gate; `check.sh` also reports sorry_in_proofs=0

  [7/11] SOURCE-DEFER pinned rust-lightning anchor check
          cmd: python3 scripts/verify-anchors.py
          expect: RC 0, bad=0 (historical: anchors=306 unanchored_rows=2)
          why: needs refs/rust-lightning at the pinned commit; a clean checkout
               must fetch it first, so this script never runs it by default.
          note: status below depends on whether refs/rust-lightning/.git exists.

  [8/11] VENDOR      provision or verify the pinned snapshot
          cmd: ./scripts/fetch-vendor.sh --ci
          expect: RC 0 snapshot present+verified; RC 3 = explicit skip (OPS-01);
                  any other RC is a real CI failure
          why: this is the ONLY explicit vendor-build skip in the plan

  [9/11] VENDOR      verify vendored snapshot checksums (vendor-gated)
          cmd: ./scripts/verify-vendor.sh
          expect: RC 0; OK (119 files) against vendor/VENDOR-SHA256
          when: only if step 8 returned RC 0 (snapshot available)

  [10/11] BUILD     full Lean build (never run by this script)
          cmd: export PATH=/dev/shm/btc/elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
               LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock lake build
          expect: RC 0 (historical wave-7 claim: 233 jobs)
          when: only after step 9 verifies the 119-file snapshot

  [11/11] BUILD     axiom audit (never run by this script)
          cmd: lake build LnLean.Proofs.PhaseC3.AxiomAudit
          expect: RC 0; only propext, Quot.sound, Classical.choice
          when: only after a successful step 10
EOF

section "classification of this run"
if [ "$vendor_state" = "present" ]; then
  printf '  VENDOR: present; step 8 would verify it locally (no network), steps 9-11 stay manual.\n'
else
  printf '  VENDOR: ABSENT -> step 8 is the explicit skip (fetch-vendor.sh RC 3).\n'
  printf '          This is OPS-01, not a missing source file: source gates 1-6 still run.\n'
fi
if [ "$refs_state" = "present" ]; then
  printf '  ANCHOR: refs/rust-lightning present; step 7 is runnable with --run.\n'
else
  printf '  ANCHOR: refs/rust-lightning absent; step 7 is DEFERRED (needs the pinned fetch).\n'
fi
printf '  BUILD:  0 build steps executed. This run is not evidence that the tree builds.\n'

section "verbatim source-gate sequence"
cat <<EOF
  cd $ROOT
  export LC_ALL=C PYTHONHASHSEED=0 PYTHONDONTWRITEBYTECODE=1
  python3 scripts/check-catalog.py --audit
  ./scripts/check.sh
  python3 scripts/check-final.py
  python3 scripts/check-conformance.py
  bash -n scripts/fetch-vendor.sh scripts/verify-vendor.sh
  test -x scripts/fetch-vendor.sh && test -x scripts/verify-vendor.sh
  grep -RInE '^[[:space:]]*sorry[[:space:]]*\$' LnLean --include='*.lean'
  python3 scripts/verify-anchors.py        # needs refs/rust-lightning
EOF

# ---------------------------------------------------------------------------
# optional execution of SOURCE steps only
# ---------------------------------------------------------------------------

failures=0
ran=0
skipped=0
stop=0

run_cmd() {
  local label="$1"
  shift
  printf '\n--- RUN %s ---\n' "$label"
  ran=$((ran + 1))
  local rc=0
  ( cd -- "$ROOT" && "$@" ) || rc=$?
  if [ "$rc" -eq 0 ]; then
    printf 'PASS %s\n' "$label"
    return 0
  fi
  printf 'FAIL %s (rc=%s)\n' "$label" "$rc" >&2
  failures=$((failures + 1))
  return 1
}

if [ "$MODE" = "run" ]; then
  section "executing SOURCE gates (VENDOR and BUILD are never executed)"

  if run_cmd "step 1 catalog audit" python3 scripts/check-catalog.py --audit; then :; else
    [ "$KEEP_GOING" -eq 1 ] || stop=1
  fi

  if [ "$stop" -eq 0 ]; then
    if run_cmd "step 2 source policy" ./scripts/check.sh; then :; else
      [ "$KEEP_GOING" -eq 1 ] || stop=1
    fi
  else
    skipped=$((skipped + 1))
  fi

  if [ "$stop" -eq 0 ]; then
    if run_cmd "step 3 file selection / root imports" python3 scripts/check-final.py; then :; else
      [ "$KEEP_GOING" -eq 1 ] || stop=1
    fi
  else
    skipped=$((skipped + 1))
  fi

  if [ "$stop" -eq 0 ]; then
    if run_cmd "step 4 conformance vectors" python3 scripts/check-conformance.py; then :; else
      [ "$KEEP_GOING" -eq 1 ] || stop=1
    fi
  else
    skipped=$((skipped + 1))
  fi

  if [ "$stop" -eq 0 ]; then
    if run_cmd "step 5 shell syntax / exec bits" \
      bash -c 'bash -n scripts/fetch-vendor.sh scripts/verify-vendor.sh && test -x scripts/fetch-vendor.sh && test -x scripts/verify-vendor.sh'; then
      :
    else
      [ "$KEEP_GOING" -eq 1 ] || stop=1
    fi
  else
    skipped=$((skipped + 1))
  fi

  if [ "$stop" -eq 0 ]; then
    printf '\n--- RUN step 6 exact sorry scan ---\n'
    ran=$((ran + 1))
    set +e
    scan_out="$(cd -- "$ROOT" && grep -RInE '^[[:space:]]*sorry[[:space:]]*$' LnLean --include='*.lean')"
    scan_rc=$?
    set -e
    if [ "$scan_rc" -eq 1 ]; then
      printf 'PASS step 6 exact sorry scan (no matches)\n'
    else
      printf 'FAIL step 6 exact sorry scan (rc=%s)\n' "$scan_rc" >&2
      [ -z "$scan_out" ] || printf '%s\n' "$scan_out" >&2
      failures=$((failures + 1))
      [ "$KEEP_GOING" -eq 1 ] || stop=1
    fi
  else
    skipped=$((skipped + 1))
  fi

  if [ "$stop" -eq 0 ] && [ "$refs_state" = "present" ]; then
    if run_cmd "step 7 anchors" python3 scripts/verify-anchors.py; then :; else
      [ "$KEEP_GOING" -eq 1 ] || stop=1
    fi
  else
    printf '\nSKIP step 7 anchors (refs/rust-lightning absent or earlier failure)\n'
    skipped=$((skipped + 1))
  fi
fi

# ---------------------------------------------------------------------------
# summary and contract
# ---------------------------------------------------------------------------

section "summary"
printf '  required source files:      %d present, %d missing\n' \
  "$(( ${#REQUIRED_FILES[@]} - ${#missing[@]} ))" "${#missing[@]}"
printf '  untracked required files:   %d\n' "${#untracked[@]}"
printf '  non-executable scripts:     %d\n' "${#not_exec[@]}"
printf '  source gates run:           %d\n' "$ran"
printf '  source gates skipped:       %d\n' "$skipped"
printf '  source gate failures:       %d\n' "$failures"
printf '  vendor step:                %s\n' \
  "$([ "$vendor_state" = present ] && printf 'present -> verify locally (not run)' || printf 'absent -> explicit skip, RC 3 (OPS-01)')"
printf '  build steps executed:       0 (full build is out of scope for H47)\n'

if [ "${#missing[@]}" -gt 0 ] || [ "${#untracked[@]}" -gt 0 ] || [ "${#not_exec[@]}" -gt 0 ]; then
  printf '\nRESULT: PREFLIGHT FAILED — required source input is incomplete (RC 1).\n'
  printf '        Fix the MISSING/UNTRACKED/NOEXEC rows above before any release gate.\n'
  exit 1
fi

if [ "$REQUIRE_VENDOR" -eq 1 ] && [ "$vendor_state" != "present" ]; then
  printf '\nRESULT: VENDOR BUILD REQUIRED BUT UNAVAILABLE (RC 3).\n'
  printf '        REQUIRE_VENDOR_BUILD/--require-vendor is set and vendor/btc-lean-core is absent.\n'
  printf '        Publish/point at a checksummed snapshot (OPS-01) or unset the requirement.\n'
  exit 3
fi

if [ "$MODE" = "run" ] && [ "$failures" -ne 0 ]; then
  printf '\nRESULT: SOURCE GATE FAILURE (RC 4) — %d failing step(s); build was not run.\n' "$failures"
  exit 4
fi

if [ "$MODE" = "run" ]; then
  printf '\nRESULT: OK — runnable source gates passed; vendor/build were not run (RC 0).\n'
  printf '        This is NOT evidence that the tree builds. See OPS-01.\n'
else
  printf '\nRESULT: OK — plan printed; nothing was executed (RC 0).\n'
  printf '        Re-run with --run to execute SOURCE steps only.\n'
fi
exit 0

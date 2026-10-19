#!/usr/bin/env python3
"""Final combined-tree checker for the D/E/F selection.

This is intentionally stricter than the per-lane checkers: it verifies the
sparse selection, one module per catalog slot, the exclusion list, and the
generated root import set.
"""
import argparse
import os
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
LEAN = "/dev/shm/btc/elan/toolchains/leanprover--lean4---v4.35.0/bin"

# The repair/integrated branch adds the Phase-C2/C3 modules, LnLean/Proofs/Common,
# the proof-wave 3 target modules, the proof-wave 4 bridge/vector modules, the
# wave-H modules, the five wave-9 proof modules, the five wave-10 proof
# modules, and the seven wave-11 proof modules to the original 132-file final
# tree.
EXPECTED_LEAN_FILES = 273

# These are convenience aggregators, not root dependencies.  The root module
# imports the concrete modules directly; importing an aggregator as well would
# only duplicate the import graph.
ROOT_AGGREGATORS = {
    "LnLean/Proofs/All.lean",
    "LnLean/Proofs/PhaseC2.lean",
}

D = set("01 02 03 04 05 07 08 10 11 12 13 14 15 16 17 18 21 23 25 27 28 29 30 32 34 36 38 41 42 43 44 46 47".split())
E = set("06 09 19 20 22 24 26 31 33 35 37 39 40 45 48".split())
F = set("01 02 03 04 05 06 07 08 09 11 12 13 14 15 16".split())
EXCLUDED = {
    "LnLean/Proofs/WaveD/D06.lean", "LnLean/Proofs/WaveD/D09.lean",
    "LnLean/Proofs/WaveD/D19.lean", "LnLean/Proofs/WaveD/D20.lean",
    "LnLean/Proofs/WaveD/D22.lean", "LnLean/Proofs/WaveD/D24.lean",
    "LnLean/Proofs/WaveD/D26.lean", "LnLean/Proofs/WaveD/D31.lean",
    "LnLean/Proofs/WaveD/D33.lean", "LnLean/Proofs/WaveD/D35.lean",
    "LnLean/Proofs/WaveD/D37.lean", "LnLean/Proofs/WaveD/D39.lean",
    "LnLean/Proofs/WaveD/D40.lean", "LnLean/Proofs/WaveD/D45.lean",
    "LnLean/Proofs/WaveD/D48.lean",
    "LnLean/Proofs/WaveE/E14.lean",
    "LnLean/Proofs/ModelHardening/F10.lean",
}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--build", action="store_true")
    args = ap.parse_args()
    errors = []

    d = sorted(p.name[1:3] for p in (ROOT / "LnLean/Proofs/WaveD").glob("D*.lean"))
    e = sorted(p.name[1:3] for p in (ROOT / "LnLean/Proofs/WaveE").glob("E*.lean"))
    f = sorted(p.name[1:3] for p in (ROOT / "LnLean/Proofs/ModelHardening").glob("F*.lean"))
    print(f"selected: D={len(d)} E={len(e)} F={len(f)} total={len(d)+len(e)+len(f)}")
    if set(d) != D:
        errors.append(f"WaveD selection mismatch: {sorted(set(d) ^ D)}")
    if set(e) != E:
        errors.append(f"WaveE selection mismatch: {sorted(set(e) ^ E)}")
    if set(f) != F:
        errors.append(f"ModelHardening selection mismatch: {sorted(set(f) ^ F)}")
    if "14" in d and "14" in e:
        errors.append("slot 14 exists in both D and E (Reserve.bounds collision)")
    for n in range(1, 49):
        k = f"{n:02d}"
        c = (1 if k in d else 0) + (1 if k in e else 0)
        if c != 1:
            errors.append(f"slot {k} has {c} D/E modules")

    for p in sorted((ROOT / "LnLean").rglob("*Alt.lean")):
        errors.append(f"leftover alt module: {p.relative_to(ROOT)}")
    for rel in EXCLUDED:
        if (ROOT / rel).exists():
            errors.append(f"excluded module present: {rel}")

    files = sorted((ROOT / "LnLean").rglob("*.lean"))
    print(f"lean files={len(files)}")
    if len(files) != EXPECTED_LEAN_FILES:
        errors.append(
            f"expected {EXPECTED_LEAN_FILES} Lean files, found {len(files)}"
        )

    for rel in sorted(ROOT_AGGREGATORS):
        if not (ROOT / rel).exists():
            errors.append(f"missing expected aggregator: {rel}")

    root = (ROOT / "LnLean.lean").read_text(encoding="utf-8")
    imports = [ln for ln in root.splitlines() if ln.startswith("import ")]
    expected = {
        "import " + str(p.relative_to(ROOT).with_suffix("")).replace("/", ".")
        for p in files
        if str(p.relative_to(ROOT)) not in ROOT_AGGREGATORS
    }
    print(f"root imports={len(imports)}")
    if set(imports) != expected:
        missing = sorted(expected - set(imports))
        extra = sorted(set(imports) - expected)
        if missing:
            errors.append(f"root imports missing: {', '.join(missing)}")
        if extra:
            errors.append(f"root imports extra: {', '.join(extra)}")
        if not missing and not extra:
            errors.append("root imports do not match the Lean file set")

    if args.build:
        env = dict(os.environ)
        env["PATH"] = LEAN + ":" + env.get("PATH", "")
        proc = subprocess.run(
            ["flock", "-w", "1800", "/tmp/ln-build.lock", "lake", "build"],
            cwd=ROOT, env=env,
        )
        if proc.returncode != 0:
            errors.append(f"full build failed RC={proc.returncode}")

    if errors:
        for e in errors:
            print("FAIL:", e)
        return 1
    print("check-final: OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())

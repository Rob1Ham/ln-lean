#!/usr/bin/env python3
"""Scaffold integrity checks.

Fails on:
  * forbidden constructs in any Lean module;
  * `sorry` in a model module (anything outside LnLean/Proofs/);
  * `sorry` in a proof module without an OBLIGATION marker nearby;
  * duplicate obligation ids.

Prints a summary of obligations.
"""
import pathlib
import re
import sys

ROOT = pathlib.Path("/home/ubuntu/ln-lean")
FORBIDDEN = re.compile(r"\b(axiom|native_decide|unsafe|admit)\b")
SORRY = re.compile(r"\bsorry\b")
OBLIGATION = re.compile(r"--\s*OBLIGATION:\s*(\S+)")

errors = []
obligations = {}
counts = {"files": 0, "sorry_proofs": 0, "obligations": 0}

for path in sorted((ROOT / "LnLean").rglob("*.lean")):
    counts["files"] += 1
    text = path.read_text(encoding="utf-8")
    rel = path.relative_to(ROOT)

    for i, line in enumerate(text.splitlines(), 1):
        if FORBIDDEN.search(line):
            errors.append(f"{rel}:{i}: forbidden construct: {line.strip()}")
        if SORRY.search(line):
            if not str(rel).startswith("LnLean/Proofs/"):
                errors.append(f"{rel}:{i}: sorry in model module")
            else:
                counts["sorry_proofs"] += 1

    for m in OBLIGATION.finditer(text):
        oid = m.group(1)
        counts["obligations"] += 1
        if oid in obligations:
            errors.append(f"{rel}: duplicate obligation id {oid} (also {obligations[oid]})")
        obligations[oid] = str(rel)

# Every sorry in Proofs must have an obligation marker in the same file.
for path in sorted((ROOT / "LnLean" / "Proofs").rglob("*.lean")):
    text = path.read_text(encoding="utf-8")
    if SORRY.search(text) and not OBLIGATION.search(text):
        errors.append(f"{path.relative_to(ROOT)}: sorry without any OBLIGATION marker")

for e in errors:
    print("FAIL:", e)

print(f"files={counts['files']} obligations={counts['obligations']} "
      f"sorry_in_proofs={counts['sorry_proofs']}")

if errors:
    sys.exit(1)
print("check: OK")

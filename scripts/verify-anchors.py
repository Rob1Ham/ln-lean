#!/usr/bin/env python3
"""Verify that cited rust-lightning anchors exist at the pinned commit.

Scans Lean sources and `docs/TRACEABILITY.md` for
`lightning*/src/...rs:<line>` references, then checks the path and line
against `refs/rust-lightning`.  Anchors without a line are checked for the
file only.  `UNANCHORED` is allowed in the traceability table but reported.
"""
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
REFS = ROOT / "refs" / "rust-lightning"
ANCHOR = re.compile(
    r"((?:rust-lightning/)?(?:lightning|lightning-invoice|lightning-types)/"
    r"[A-Za-z0-9_./-]+\.rs)(?::(\d+))?"
)

seen = {}
for path in sorted((ROOT / "LnLean").rglob("*.lean")):
    text = path.read_text(encoding="utf-8")
    for m in ANCHOR.finditer(text):
        rel = m.group(1)
        if rel.startswith("rust-lightning/"):
            rel = rel[len("rust-lightning/"):]
        line = int(m.group(2)) if m.group(2) else None
        seen.setdefault((rel, line), []).append(str(path.relative_to(ROOT)))

trace = ROOT / "docs" / "TRACEABILITY.md"
un = 0
if trace.exists():
    for line in trace.read_text(encoding="utf-8").splitlines():
        if "UNANCHORED" in line:
            un += 1
        for m in ANCHOR.finditer(line):
            rel = m.group(1)
            if rel.startswith("rust-lightning/"):
                rel = rel[len("rust-lightning/"):]
            n = int(m.group(2)) if m.group(2) else None
            seen.setdefault((rel, n), []).append("docs/TRACEABILITY.md")

bad = []
for (rel, line), sources in sorted(seen.items(), key=lambda kv: (kv[0][0], kv[0][1] or 0)):
    p = REFS / rel
    if not p.exists():
        bad.append((rel, line, "missing file", sources[:2]))
        continue
    if line is not None:
        total = sum(1 for _ in p.open(encoding="utf-8", errors="replace"))
        if line > total:
            bad.append((rel, line, f"line > {total}", sources[:2]))

print(f"anchors={len(seen)} bad={len(bad)} unanchored_rows={un}")
for rel, line, why, sources in bad:
    print(f"FAIL {rel}:{line} {why} <- {', '.join(sources)}")
if bad:
    sys.exit(1)
print("verify-anchors: OK")

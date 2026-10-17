#!/usr/bin/env python3
"""Extract BOLT and rust-lightning anchors from the Lean sources.

This is a traceability report, not a proof.  It scans module docstrings and
comments for `BOLT <n>` and `lightning/src/...rs:<line>` references and emits
one row per (file, anchor).
"""
import pathlib
import re
from collections import defaultdict

ROOT = pathlib.Path("/home/ubuntu/ln-lean")
OUT = ROOT / "docs" / "ANCHORS-GENERATED.md"

BOLT = re.compile(r"\bBOLT\s*#?\s*(\d+)\b", re.IGNORECASE)
LDK = re.compile(r"((?:rust-lightning/)?lightning/src/[A-Za-z0-9_./-]+\.rs)(?::(\d+))?")
# Also accept the shorter `ln/...` form used by some LDK paths.
LDK_SHORT = re.compile(r"\b(ln/[A-Za-z0-9_./-]+\.rs)(?::(\d+))?")

def normalize(anchor: str) -> str:
    """Use one canonical LDK path spelling."""
    if anchor.startswith("rust-lightning/"):
        anchor = anchor[len("rust-lightning/"):]
    if anchor.startswith("ln/"):
        anchor = "lightning/src/" + anchor
    return anchor

rows = defaultdict(set)
files = sorted((ROOT / "LnLean").rglob("*.lean"))
for path in files:
    rel = str(path.relative_to(ROOT))
    text = path.read_text(encoding="utf-8")
    for line in text.splitlines():
        for m in BOLT.finditer(line):
            rows[rel].add(("BOLT", f"BOLT {m.group(1)}"))
        for m in LDK.finditer(line):
            anchor = m.group(1)
            if m.group(2):
                anchor += ":" + m.group(2)
            rows[rel].add(("LDK", normalize(anchor)))
        for m in LDK_SHORT.finditer(line):
            anchor = "lightning/src/" + m.group(1)
            if m.group(2):
                anchor += ":" + m.group(2)
            rows[rel].add(("LDK", normalize(anchor)))

lines = [
    "# Generated anchor index",
    "",
    "Extracted from `LnLean/**.lean` by `scripts/collect-anchors.py`.",
    "The pinned commits are in `refs/PINNED.md`.",
    "",
    f"- Lean files scanned: **{len(files)}**",
    f"- files with anchors: **{len(rows)}**",
    "",
    "| Lean file | Kind | Anchor |",
    "|---|---|---|",
]
for rel in sorted(rows):
    for kind, anchor in sorted(rows[rel]):
        lines.append(f"| `{rel}` | {kind} | `{anchor}` |")
OUT.write_text("\n".join(lines) + "\n", encoding="utf-8")
print(f"scanned={len(files)} with_anchors={len(rows)} rows={sum(len(v) for v in rows.values())}")

#!/usr/bin/env python3
"""Collect the obligation markers and declarations from the proof scaffold.

Run after both waves.  This is a reporting tool; it does not edit Lean.
"""
import json
import pathlib
import re
from collections import Counter, defaultdict

ROOT = pathlib.Path(__file__).resolve().parents[1]
PROOFS = ROOT / "LnLean" / "Proofs"
OUT_MD = ROOT / "docs" / "OBLIGATIONS-GENERATED.md"
OUT_JSON = ROOT / "agents" / "status" / "obligations.json"


def strip_comments(text: str) -> str:
    """Remove Lean comments/strings, preserving newlines for line numbers."""
    out = []
    i = 0
    depth = 0
    in_str = False
    n = len(text)
    while i < n:
        if depth > 0:
            if text.startswith("/-", i):
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                if text[i] == "\n":
                    out.append("\n")
                i += 1
            continue
        if in_str:
            if text[i] == "\\":
                i += 2 if i + 1 < n else 1
            elif text[i] == '"':
                in_str = False
                out.append('"')
                i += 1
            else:
                if text[i] == "\n":
                    out.append("\n")
                i += 1
            continue
        if text.startswith("/-", i):
            depth = 1
            i += 2
            continue
        if text.startswith("--", i):
            j = text.find("\n", i)
            if j == -1:
                break
            out.append("\n")
            i = j + 1
            continue
        if text[i] == '"':
            in_str = True
            out.append('"')
            i += 1
            continue
        out.append(text[i])
        i += 1
    return "".join(out)

OBLIGATION = re.compile(r"--\s*OBLIGATION:\s*(LN-[A-Za-z0-9_-]+)(.*)$")
DECL = re.compile(
    r"^\s*(theorem|lemma|def|structure|inductive|abbrev)\s+"
    r"([A-Za-z0-9_'.]+)"
)

rows = []
decls = []
sorries = []
catalog_rows = []
files = sorted(PROOFS.rglob("*.lean")) if PROOFS.exists() else []

# The wave-A catalog is a Lean list of records, not `-- OBLIGATION:` comments.
CATALOG = ROOT / "LnLean" / "Proofs" / "Obligations.lean"
if CATALOG.exists():
    text = CATALOG.read_text(encoding="utf-8")
    for m in re.finditer(r'\{\s*id := "(LN-[^"]+)"(.*?)\}(?:,|\s*\])', text, re.S):
        oid, body = m.group(1), m.group(2)
        def field(name, default=""):
            fm = re.search(rf'\b{name} := "([^"]*)"', body)
            return fm.group(1) if fm else default
        sm = re.search(r'\bstatus := \.(\w+)', body)
        dm = re.search(r'\bdomain := \.(\w+)', body)
        catalog_rows.append({
            "id": oid,
            "claim": field("claim"),
            "lean_target": field("leanTarget"),
            "boltdoc": field("boltdoc"),
            "anchor": field("rlAnchor"),
            "status": sm.group(1) if sm else "unknown",
            "domain": dm.group(1) if dm else "unknown",
        })

for path in files:
    text = path.read_text(encoding="utf-8")
    rel = path.relative_to(ROOT)
    domain = rel.parts[2] if len(rel.parts) > 2 else "Root"
    code_lines = strip_comments(text).splitlines()
    code_line_set = set()
    for i, line in enumerate(code_lines, 1):
        if re.search(r"\bsorry\b", line):
            code_line_set.add(i)
    for i, line in enumerate(text.splitlines(), 1):
        m = OBLIGATION.search(line)
        if m:
            rows.append({
                "id": m.group(1),
                "claim": (m.group(2) or "").strip().strip("`").lstrip(":").strip(),
                "domain": domain,
                "file": str(rel),
                "line": i,
            })
        # Match declarations on the comment-stripped line.  The obligation
        # marker itself lives in a line comment, so that scan below still uses
        # the original text.
        d = DECL.match(code_lines[i - 1])
        if d:
            decls.append({
                "kind": d.group(1),
                "name": d.group(2),
                "domain": domain,
                "file": str(rel),
                "line": i,
            })
        if i in code_line_set:
            sorries.append({"file": str(rel), "line": i, "text": line.strip()})

by_domain = Counter(r["domain"] for r in rows)
by_kind = Counter(d["kind"] for d in decls)
ids = [r["id"] for r in rows]
duplicates = sorted({i for i in ids if ids.count(i) > 1})

OUT_JSON.parent.mkdir(parents=True, exist_ok=True)
catalog_ids = [r["id"] for r in catalog_rows]
catalog_dups = sorted({i for i in catalog_ids if catalog_ids.count(i) > 1})
OUT_JSON.write_text(json.dumps({
    "files": len(files),
    "obligations": len(rows),
    "catalog_obligations": len(catalog_rows),
    "declarations": len(decls),
    "sorries": len(sorries),
    "by_domain": dict(sorted(by_domain.items())),
    "by_kind": dict(sorted(by_kind.items())),
    "duplicate_ids": duplicates,
    "catalog_duplicate_ids": catalog_dups,
    "rows": rows,
    "catalog_rows": catalog_rows,
}, indent=2), encoding="utf-8")

lines = [
    "# Generated obligation index",
    "",
    "This file is generated by `scripts/collect-obligations.py` from the",
    "`-- OBLIGATION:` markers in `LnLean/Proofs/`. It is a status view, not",
    "a proof: a listed obligation may still be `sorry`.",
    "",
    f"- proof files: **{len(files)}**",
    f"- wave-B obligation markers: **{len(rows)}**",
    f"- wave-A catalog obligations: **{len(catalog_rows)}** "
    f"({sum(1 for r in catalog_rows if r['status'] == 'proved')} proved, "
    f"{sum(1 for r in catalog_rows if r['status'] == 'statementOnly')} statement-only)",
    f"- declarations: **{len(decls)}**",
    f"- `sorry` sites: **{len(sorries)}**",
    f"- duplicate marker ids: **{len(duplicates)}**",
    "",
    "## By domain",
    "",
    "| Domain | Obligations |",
    "|---|---:|",
]
for k, v in sorted(by_domain.items()):
    lines.append(f"| {k} | {v} |")
lines += ["", "## Obligations", "", "| Id | Domain | File:line | Claim |", "|---|---|---|---|"]
for r in rows:
    claim = r["claim"].replace("|", "\\|")
    lines.append(f"| `{r['id']}` | {r['domain']} | `{r['file']}:{r['line']}` | {claim} |")
lines += ["", "## Wave-A catalog", "", "| Id | Domain | Status | Lean target | Claim |", "|---|---|---|---|---|"]
for r in catalog_rows:
    claim = r["claim"].replace("|", "\\|")
    lines.append(f"| `{r['id']}` | {r['domain']} | {r['status']} | `{r['lean_target']}` | {claim} |")
lines += ["", "## Declarations", "", "| Kind | Name | File:line |", "|---|---|---|"]
for d in decls:
    lines.append(f"| {d['kind']} | `{d['name']}` | `{d['file']}:{d['line']}` |")
if duplicates:
    lines += ["", "## Duplicate obligation ids", ""]
    lines += [f"- `{x}`" for x in duplicates]
OUT_MD.write_text("\n".join(lines) + "\n", encoding="utf-8")

print(f"files={len(files)} markers={len(rows)} catalog={len(catalog_rows)} "
      f"declarations={len(decls)} sorries={len(sorries)} "
      f"duplicate_marker_ids={len(duplicates)}")
print("by_domain:", dict(sorted(by_domain.items())))

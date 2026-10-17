#!/usr/bin/env python3
"""Write the integrator report after waves A and B.

The report is generated from the tree and the status files.  It does not
claim a build passed unless BUILD_RC=0 is present in the environment (the
finalize script sets it after `lake build`).
"""
import json
import os
import pathlib
import re
import subprocess
from collections import Counter

ROOT = pathlib.Path("/home/ubuntu/ln-lean")
OUT = ROOT / "agents" / "reports" / "INTEGRATOR.md"

DECL = re.compile(r"^\s*(theorem|lemma|def|structure|inductive|abbrev)\s+([A-Za-z0-9_'.]+)", re.M)
SORRY = re.compile(r"\bsorry\b")


def strip_comments(text: str) -> str:
    """Crude comment stripper for reporting counts, not for policy checks."""
    text = re.sub(r"/-.*?-/", "", text, flags=re.S)
    text = re.sub(r"--[^\n]*", "", text)
    return text


def count_decls(paths):
    n = 0
    for p in paths:
        n += len(DECL.findall(strip_comments(p.read_text(encoding="utf-8"))))
    return n


def status_lines(name):
    p = ROOT / "agents" / "status" / f"{name}.status"
    if not p.exists():
        return []
    return [l for l in p.read_text(encoding="utf-8").splitlines() if l.strip()]


def main():
    head = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True, text=True).stdout.strip()
    subj = subprocess.run(["git", "log", "-1", "--format=%s"], cwd=ROOT, capture_output=True, text=True).stdout.strip()
    a_status = status_lines("A")
    b_status = status_lines("B")
    a_done = sum(1 for l in a_status if re.search(r"exit=", l))
    b_done = sum(1 for l in b_status if re.search(r"exit=", l))
    b_ok = sum(1 for l in b_status if "exit=0" in l)
    green = (ROOT / "agents" / "status" / "A-GREEN").read_text(encoding="utf-8").strip() if (ROOT / "agents" / "status" / "A-GREEN").exists() else "absent"

    all_lean = sorted((ROOT / "LnLean").rglob("*.lean"))
    proofs = sorted((ROOT / "LnLean" / "Proofs").rglob("*.lean"))
    model = [p for p in all_lean if p not in proofs]
    b_files = [p for p in proofs if p.name != "Obligations.lean"]
    sorries = []
    for p in all_lean:
        code = strip_comments(p.read_text(encoding="utf-8"))
        for i, line in enumerate(code.splitlines(), 1):
            if SORRY.search(line):
                sorries.append((p.relative_to(ROOT), i))
    markers = 0
    for p in proofs:
        markers += len(re.findall(r"--\s*OBLIGATION:\s*LN-", p.read_text(encoding="utf-8")))

    ob_path = ROOT / "agents" / "status" / "obligations.json"
    ob = json.loads(ob_path.read_text(encoding="utf-8")) if ob_path.exists() else {}
    catalog = ob.get("catalog_obligations", 0)
    catalog_proved = sum(1 for r in ob.get("catalog_rows", []) if r.get("status") == "proved")

    build_rc = os.environ.get("BUILD_RC", "not run by this report")
    vendor = "OK" if subprocess.run(["./scripts/verify-vendor.sh"], cwd=ROOT, capture_output=True).returncode == 0 else "FAIL"

    lines = [
        "# Integrator report",
        "",
        f"- repository: `{ROOT}`",
        f"- HEAD: `{head}` ({subj})",
        f"- wave A: **{a_done}/8** agents exited, gate: `{green}`",
        f"- wave B: **{b_done}/32** agents exited, **{b_ok}** with RC 0",
        f"- vendor integrity: **{vendor}**",
        f"- full build: **{build_rc}**",
        "",
        "## Tree counts",
        "",
        f"- Lean files: **{len(all_lean)}** ({len(model)} model, {len(proofs)} proof)",
        f"- model declarations: **{count_decls(model)}**",
        f"- proof declarations: **{count_decls(proofs)}**",
        f"- wave-A catalog rows: **{catalog}** ({catalog_proved} proved, {catalog - catalog_proved} statement-only)",
        f"- wave-B `-- OBLIGATION:` markers: **{markers}**",
        f"- `sorry` sites under `Proofs/`: **{len(sorries)}**",
        "",
        "## Wave-B files",
        "",
        "| File | Declarations | Obligation markers |",
        "|---|---:|---:|",
    ]
    for p in b_files:
        raw = p.read_text(encoding="utf-8")
        code = strip_comments(raw)
        lines.append(
            f"| `{p.relative_to(ROOT)}` | {len(DECL.findall(code))} | "
            f"{len(re.findall(r'--\\s*OBLIGATION:\\s*LN-', raw))} |"
        )
    lines += [
        "",
        "## Status records",
        "",
        "```",
        *a_status,
        *b_status,
        "```",
        "",
        "## Honest limits",
        "",
        "This is a scaffold.  The wave-A catalog is metadata; most rows are",
        "`statementOnly`.  Wave-B files add theorem statements and obligation",
        "markers, and many contain `sorry`.  Cryptographic facts are `Prop`",
        "hypotheses, not axioms.  The report does not upgrade an obligation to a",
        "proof: only a build with no `sorry` at that site would.",
        "",
        "## Reproduce",
        "",
        "```sh",
        "export PATH=/dev/shm/btc/elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH",
        "cd /home/ubuntu/ln-lean",
        "./scripts/verify-vendor.sh",
        "./scripts/check.sh",
        "python3 scripts/collect-obligations.py",
        "python3 scripts/collect-anchors.py",
        "flock -w 1800 /tmp/ln-build.lock lake build",
        "```",
        "",
    ]
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text("\n".join(lines), encoding="utf-8")
    print(f"wrote {OUT} (A {a_done}/8, B {b_done}/32, files {len(all_lean)}, markers {markers})")


if __name__ == "__main__":
    main()

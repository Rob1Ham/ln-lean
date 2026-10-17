#!/usr/bin/env python3
"""Compare wave-c/235 with the phase-c branch per proof file.

Prints remaining `sorry` counts, diff size, and whether an existing
theorem/lemma line was removed.  It does not modify the worktree.
"""
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path("/home/ubuntu/ln-lean")
BASE = "b891a59"
OTHER = "phasec/phase-c"
SORRY = re.compile(r"\bsorry\b")
FILES = [
    "LnLean/Proofs/Bitcoin/AnchorProps.lean",
    "LnLean/Proofs/Bitcoin/FundingProps.lean",
    "LnLean/Proofs/Bitcoin/ScriptProps.lean",
    "LnLean/Proofs/Channel/HTLCProps.lean",
    "LnLean/Proofs/Channel/ReserveProps.lean",
    "LnLean/Proofs/Channel/StateMachineProps.lean",
    "LnLean/Proofs/Conservation.lean",
    "LnLean/Proofs/Crypto/EcdsaProps.lean",
    "LnLean/Proofs/Crypto/Sha256Props.lean",
    "LnLean/Proofs/Payment/KeysendProps.lean",
    "LnLean/Proofs/Payment/MPPProps.lean",
    "LnLean/Proofs/Protocol/ChannelReestablishProps.lean",
    "LnLean/Proofs/Protocol/FeaturesProps.lean",
    "LnLean/Proofs/Routing/GossipProps.lean",
    "LnLean/Proofs/Routing/GraphProps.lean",
    "LnLean/Proofs/Wire/TLVProps.lean",
]


def strip_comments(text: str) -> str:
    text = re.sub(r"/-.*?-/", "", text, flags=re.S)
    text = re.sub(r"--[^\n]*", "", text)
    return text


def show(ref: str, path: str) -> str:
    p = subprocess.run(["git", "show", f"{ref}:{path}"], cwd=ROOT, capture_output=True, text=True)
    return p.stdout if p.returncode == 0 else ""


def count(ref: str, path: str) -> int:
    return len(SORRY.findall(strip_comments(show(ref, path))))


def diff_lines(ref: str, path: str) -> int:
    p = subprocess.run(["git", "diff", "--numstat", BASE, ref, "--", path], cwd=ROOT, capture_output=True, text=True)
    parts = p.stdout.split()
    return int(parts[0]) + int(parts[1]) if len(parts) >= 2 and parts[0].isdigit() and parts[1].isdigit() else 0


def removed_statement(ref: str, path: str) -> bool:
    p = subprocess.run(["git", "diff", "-U0", BASE, ref, "--", path], cwd=ROOT, capture_output=True, text=True)
    return any(l.startswith(("-theorem ", "-lemma ")) for l in p.stdout.splitlines())


def main() -> int:
    try:
        subprocess.run(["git", "rev-parse", "--verify", OTHER], cwd=ROOT, check=True, capture_output=True)
    except subprocess.CalledProcessError:
        print(f"{OTHER} is not fetched; fetch the phase-c branch first")
        return 2
    print(f"{'file':58} {'base':>4} {'ours':>4} {'PC':>3} {'ours±':>6} {'PC±':>5} flags")
    for path in FILES:
        b, o, p = count(BASE, path), count("wave-c/235", path), count(OTHER, path)
        flags = []
        if removed_statement("wave-c/235", path):
            flags.append("ours-stmt")
        if removed_statement(OTHER, path):
            flags.append("pc-stmt")
        print(f"{path:58} {b:4} {o:4} {p:3} {diff_lines('wave-c/235', path):6} {diff_lines(OTHER, path):5} {','.join(flags)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())

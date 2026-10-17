#!/usr/bin/env python3
"""Wave-C closure checker.

Checks the 16 owned proof files, counts the remaining `sorry` sites against
the wave-B baseline (25), optionally builds every module, and flags any
change to a model module or to an existing theorem/lemma statement.

This is a reporting/integration aid; `scripts/check.sh` remains the policy
gate and the root `lake build` remains the build gate.
"""
import argparse
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path("/home/ubuntu/ln-lean")
BASE = "b891a59"
LEAN = "/dev/shm/btc/elan/toolchains/leanprover--lean4---v4.35.0/bin"
SORRY = re.compile(r"\bsorry\b")
OBLIGATION = re.compile(r"--\s*OBLIGATION:\s*(LN-\S+)")
STATEMENT = re.compile(r"^\s*(theorem|lemma)\s+([A-Za-z0-9_'.]+)")

UNITS = {
    "C01": ("LnLean/Proofs/Bitcoin/AnchorProps.lean", "LnLean.Proofs.Bitcoin.AnchorProps", 2),
    "C02": ("LnLean/Proofs/Bitcoin/FundingProps.lean", "LnLean.Proofs.Bitcoin.FundingProps", 2),
    "C03": ("LnLean/Proofs/Bitcoin/ScriptProps.lean", "LnLean.Proofs.Bitcoin.ScriptProps", 3),
    "C04": ("LnLean/Proofs/Channel/HTLCProps.lean", "LnLean.Proofs.Channel.HTLCProps", 2),
    "C05": ("LnLean/Proofs/Channel/ReserveProps.lean", "LnLean.Proofs.Channel.ReserveProps", 1),
    "C06": ("LnLean/Proofs/Channel/StateMachineProps.lean", "LnLean.Proofs.Channel.StateMachineProps", 1),
    "C07": ("LnLean/Proofs/Conservation.lean", "LnLean.Proofs.Conservation", 1),
    "C08": ("LnLean/Proofs/Crypto/EcdsaProps.lean", "LnLean.Proofs.Crypto.EcdsaProps", 2),
    "C09": ("LnLean/Proofs/Crypto/Sha256Props.lean", "LnLean.Proofs.Crypto.Sha256Props", 1),
    "C10": ("LnLean/Proofs/Payment/KeysendProps.lean", "LnLean.Proofs.Payment.KeysendProps", 1),
    "C11": ("LnLean/Proofs/Payment/MPPProps.lean", "LnLean.Proofs.Payment.MPPProps", 1),
    "C12": ("LnLean/Proofs/Protocol/ChannelReestablishProps.lean", "LnLean.Proofs.Protocol.ChannelReestablishProps", 2),
    "C13": ("LnLean/Proofs/Protocol/FeaturesProps.lean", "LnLean.Proofs.Protocol.FeaturesProps", 1),
    "C14": ("LnLean/Proofs/Routing/GossipProps.lean", "LnLean.Proofs.Routing.GossipProps", 3),
    "C15": ("LnLean/Proofs/Routing/GraphProps.lean", "LnLean.Proofs.Routing.GraphProps", 1),
    "C16": ("LnLean/Proofs/Wire/TLVProps.lean", "LnLean.Proofs.Wire.TLVProps", 1),
}


def strip_comments(text: str) -> str:
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


def git(*args: str) -> str:
    return subprocess.run(["git", *args], cwd=ROOT, capture_output=True, text=True).stdout


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--build", action="store_true")
    args = ap.parse_args()

    errors = []
    before = sum(v[2] for v in UNITS.values())
    after = 0
    print(f"wave-c baseline sorry sites: {before}")
    for name, (rel, module, expected) in sorted(UNITS.items()):
        path = ROOT / rel
        if not path.exists():
            errors.append(f"{name}: missing {rel}")
            continue
        raw = path.read_text(encoding="utf-8")
        code = strip_comments(raw)
        n = len(SORRY.findall(code))
        markers = len(OBLIGATION.findall(raw))
        after += n
        state = "CLOSED" if n == 0 else f"{n} open"
        print(f"  {name:3} {state:8} markers={markers:2}  {rel}")
        if n > expected:
            errors.append(f"{name}: sorry count increased {expected} -> {n}")

        # A removed theorem/lemma line means an existing statement changed.
        diff = git("diff", "-U0", BASE, "--", rel)
        for line in diff.splitlines():
            if line.startswith(("-theorem ", "-lemma ")):
                errors.append(f"{name}: existing statement removed/changed: {line}")

        if args.build:
            env = dict(__import__("os").environ)
            env["PATH"] = LEAN + ":" + env.get("PATH", "")
            proc = subprocess.run(
                ["flock", "-w", "900", "/tmp/ln-build.lock", "lake", "build", module],
                cwd=ROOT, capture_output=True, text=True, env=env,
            )
            if proc.returncode != 0:
                tail = "\n".join(proc.stdout.splitlines()[-8:])
                errors.append(f"{name}: build failed RC={proc.returncode}\n{tail}")

    # No model file may change in a proof-closure wave.
    changed = [p for p in git("diff", "--name-only", BASE, "--").splitlines() if p]
    model_changes = [p for p in changed if p.startswith("LnLean/") and not p.startswith("LnLean/Proofs/")]
    for p in model_changes:
        errors.append(f"model file changed: {p}")

    print(f"wave-c final sorry sites: {after} (closed {before - after})")
    if errors:
        for e in errors:
            print("FAIL:", e)
        return 1
    print("check-wave-c: OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""Check the 32 wave-B proof-scaffold modules.

Presence, imports, obligation markers, nearby-marker warnings, and optional
build.  Builds use the shared `/tmp/ln-build.lock`.
"""
import argparse
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path("/home/ubuntu/ln-lean")
LEAN = "/dev/shm/btc/elan/toolchains/leanprover--lean4---v4.35.0/bin"
LOCK = "/tmp/ln-build.lock"

MODULES = [
    "LnLean.Proofs.Bitcoin.FundingProps",
    "LnLean.Proofs.Bitcoin.ScriptProps",
    "LnLean.Proofs.Bitcoin.AnchorProps",
    "LnLean.Proofs.Bitcoin.WeightProps",
    "LnLean.Proofs.Crypto.Sha256Props",
    "LnLean.Proofs.Crypto.EcdsaProps",
    "LnLean.Proofs.Crypto.SchnorrProps",
    "LnLean.Proofs.Wire.TLVProps",
    "LnLean.Proofs.Channel.CommitmentTxProps",
    "LnLean.Proofs.Channel.StateMachineProps",
    "LnLean.Proofs.Channel.FeeProps",
    "LnLean.Proofs.Channel.ReserveProps",
    "LnLean.Proofs.Channel.HTLCProps",
    "LnLean.Proofs.Channel.RevocationProps",
    "LnLean.Proofs.Channel.PenaltyProps",
    "LnLean.Proofs.Channel.BreachProps",
    "LnLean.Proofs.Protocol.HandshakeProps",
    "LnLean.Proofs.Protocol.ChannelReestablishProps",
    "LnLean.Proofs.Protocol.FeaturesProps",
    "LnLean.Proofs.Protocol.ErrorProps",
    "LnLean.Proofs.Routing.GraphProps",
    "LnLean.Proofs.Routing.GossipProps",
    "LnLean.Proofs.Routing.OnionProps",
    "LnLean.Proofs.Routing.RouteBlindingProps",
    "LnLean.Proofs.Payment.InvoiceProps",
    "LnLean.Proofs.Payment.MPPProps",
    "LnLean.Proofs.Payment.KeysendProps",
    "LnLean.Proofs.Payment.LiquidityProps",
    "LnLean.Proofs.Security.ThreatModelProps",
    "LnLean.Proofs.Conservation",
    "LnLean.Proofs.Liveness",
    "LnLean.Proofs.Traceability",
]

DECL = re.compile(r"^\s*(theorem|lemma|def|structure|inductive|abbrev)\s+([A-Za-z0-9_'.]+)", re.M)
MARK = re.compile(r"--\s*OBLIGATION:\s*(LN-\S+)")
SORRY = re.compile(r"\bsorry\b")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--build", action="store_true")
    args = ap.parse_args()

    missing = []
    bad_imports = []
    no_marker = []
    nearby = []
    stats = {}
    for m in MODULES:
        p = ROOT / (m.replace(".", "/") + ".lean")
        if not p.exists():
            missing.append(m)
            continue
        t = p.read_text(encoding="utf-8")
        stats[m] = (len(DECL.findall(t)), len(MARK.findall(t)), len(SORRY.findall(t)))
        for line in t.splitlines():
            if line.startswith("import LnLean.Proofs.") and "Obligations" not in line:
                bad_imports.append((m, line.strip()))
        if stats[m][0] > 0 and stats[m][1] == 0:
            no_marker.append(m)
        lines = t.splitlines()
        for i, line in enumerate(lines):
            code = re.sub(r"--.*$", "", line)
            if SORRY.search(code) and "-- OBLIGATION" not in line:
                prev = lines[i - 1] if i else ""
                if "-- OBLIGATION" not in prev:
                    nearby.append((m, i + 1))

    print(f"modules={len(MODULES)} missing={len(missing)}")
    for m in missing:
        print("MISSING", m)
    for m, imp in bad_imports:
        print("CROSS-B IMPORT", m, imp)
    for m in no_marker:
        print("NO MARKERS", m)
    for m, line in nearby[:20]:
        print("SORRY WITHOUT ADJACENT MARKER", f"{m}:{line}")

    failed = []
    if args.build:
        env = {"PATH": f"{LEAN}:/usr/bin:/bin", "HOME": str(pathlib.Path.home())}
        for m in MODULES:
            if m in missing:
                continue
            r = subprocess.run(
                ["flock", "-w", "120", LOCK, "lake", "build", m],
                cwd=ROOT, env=env, capture_output=True, text=True,
            )
            if r.returncode != 0:
                failed.append(m)
                print(f"FAIL {m} rc={r.returncode}")
                errs = [l for l in (r.stdout + r.stderr).splitlines() if "error" in l.lower()]
                for line in errs[:5]:
                    print("   ", line)
            else:
                print(f"OK   {m}")
        print(f"build_failed={len(failed)}")

    print("per-file (decls, markers, sorry):")
    for m in MODULES:
        if m in stats:
            print(f"  {m}: {stats[m]}")
    return 1 if (missing or bad_imports or no_marker or failed) else 0


if __name__ == "__main__":
    sys.exit(main())

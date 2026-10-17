#!/usr/bin/env python3
"""Check the wave-A scaffolding: expected files, docs, and optional builds.

Usage:
  python3 scripts/check-wave-a.py          # presence only
  python3 scripts/check-wave-a.py --build  # build each module (shared lock)
"""
import argparse
import pathlib
import subprocess
import sys

ROOT = pathlib.Path("/home/ubuntu/ln-lean")
LEAN = "/dev/shm/btc/elan/toolchains/leanprover--lean4---v4.35.0/bin"
LOCK = "/tmp/ln-build.lock"

MODULES = [
    # A1
    "LnLean.Bitcoin.Funding", "LnLean.Bitcoin.ScriptTemplates", "LnLean.Bitcoin.Laws",
    # A2
    "LnLean.Crypto.Model", "LnLean.Crypto.Hash", "LnLean.Crypto.Sig", "LnLean.Crypto.Noise",
    "LnLean.Wire.BigSize", "LnLean.Wire.TLV", "LnLean.Wire.Message",
    # A3
    "LnLean.Channel.Types", "LnLean.Channel.State", "LnLean.Channel.Commitment",
    "LnLean.Channel.Fee", "LnLean.Channel.Laws",
    # A4
    "LnLean.Channel.HTLC", "LnLean.Channel.Revocation", "LnLean.Channel.Penalty",
    "LnLean.Channel.HTLCLaws",
    # A5
    "LnLean.Protocol.Handshake", "LnLean.Protocol.Peer", "LnLean.Protocol.Messages",
    "LnLean.Protocol.Laws",
    # A6
    "LnLean.Routing.Graph", "LnLean.Routing.Gossip", "LnLean.Routing.Onion",
    "LnLean.Routing.Route", "LnLean.Routing.Laws",
    # A7
    "LnLean.Payment.Invoice", "LnLean.Payment.HTLC", "LnLean.Payment.MPP",
    "LnLean.Payment.Laws",
    # A8
    "LnLean.Security.Model", "LnLean.Security.Invariants", "LnLean.Proofs.Obligations",
]

DOCS = [
    "docs/SCOPE.md", "docs/THEOREM-INDEX.md", "docs/TRACEABILITY.md", "docs/ROADMAP.md",
]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--build", action="store_true")
    args = ap.parse_args()

    missing = []
    for m in MODULES:
        p = ROOT / (m.replace(".", "/") + ".lean")
        if not p.exists():
            missing.append(m)
    missing_docs = [d for d in DOCS if not (ROOT / d).exists()]

    print(f"modules={len(MODULES)} missing={len(missing)} missing_docs={len(missing_docs)}")
    for m in missing:
        print("MISSING module:", m)
    for d in missing_docs:
        print("MISSING doc:", d)

    failed = []
    if args.build:
        env = {"PATH": f"{LEAN}:/usr/bin:/bin", "HOME": str(pathlib.Path.home())}
        for m in MODULES:
            if m in missing:
                continue
            cmd = ["flock", "-w", "120", LOCK, "lake", "build", m]
            r = subprocess.run(cmd, cwd=ROOT, env=env, capture_output=True, text=True)
            if r.returncode != 0:
                failed.append(m)
                print(f"FAIL {m} rc={r.returncode}")
                errs = [l for l in (r.stdout + r.stderr).splitlines() if "error" in l.lower()]
                for line in errs[:6]:
                    print("   ", line)
            else:
                print(f"OK   {m}")
        print(f"build_failed={len(failed)}")

    return 1 if (missing or missing_docs or failed) else 0


if __name__ == "__main__":
    sys.exit(main())

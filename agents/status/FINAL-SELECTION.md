# Final D/E/F selection

Base: `a9f8d87` (Wave-C).  Branch: `final/integrated`.

Selection rule: one whole-file D/E version per catalog slot 01–48, plus the
model-hardening F modules.  D41–D48 and E45/E48 are annex/refinement modules
with their own namespaces; they do not close a second catalog row.

## Counts

| Lane | Files |
|---|---:|
| Base (Wave C) | 69 |
| Wave D | 33 |
| Wave E | 15 |
| Model hardening (F) | 15 |
| **Total Lean files** | **132** |

## Wave D primary/annex (33)

`D01 D02 D03 D04 D05 D07 D08 D10 D11 D12 D13 D14 D15 D16 D17 D18 D21 D23
D25 D27 D28 D29 D30 D32 D34 D36 D38 D41 D42 D43 D44 D46 D47`

## Wave E primary/annex (15)

`E06 E09 E19 E20 E22 E24 E26 E31 E33 E35 E37 E39 E40 E45 E48`

## Model hardening (15)

`F01 F02 F03 F04 F05 F06 F07 F08 F09 F11 F12 F13 F14 F15 F16`

## Exclusions

- All unselected D/E files, including `E14` (hard collision:
  `LnLean.Channel.Reserve.bounds` with D14) and `D37`/`D39`/`D40`.
- `F10`: malformed marker in the lane snapshot and a Msat/Nat premise
  mismatch; excluded from the final tree.  It remains on `wave-f/16`.
- `D37Alt`, `E03Alt`, and other `*Alt` files: discarded backups.
- Host-local `.lake`, `vendor/btc-lean-core`, `refs/rust-lightning`, and
  `refs/bolts` symlinks: never committed.

## Verified

- 48/48 slots have exactly one D or E module.
- 132 Lean files and 132 root imports.
- `scripts/check-final.py` OK.
- Full `lake build`: 140 jobs, RC 0.
- `verify-vendor.sh`: OK (119 files).
- `verify-anchors.py`: 288 anchors, 0 bad.
- `check.sh`: OK; 95 obligation markers, 15 real `sorry` sites.
- No duplicate marker ids.

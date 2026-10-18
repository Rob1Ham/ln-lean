# License decision matrix — ln-lean

**Status: DECISION PENDING. No license is selected, applied, or recommended by
this document.** It is decision support for the maintainer, not legal advice.
Adding a license, changing copyright notices, or relicensing third-party code
requires the maintainer's authority and, where appropriate, legal review.

**Snapshot:** branch `repair/integrated`, lane base `47189fe`, checks at
`f2123ef`.
**Related blocker:** `OPS-02` in `docs/OPEN-ISSUES.md`.
**Related release gate:** section 4 of `docs/RELEASE-CHECKLIST.md`.

## 1. Current facts

| Fact | Evidence |
|---|---|
| No root `LICENSE`, `COPYING`, `NOTICE`, or `AUTHORS` file | filesystem check |
| No SPDX identifier or license field in `lakefile.lean` | `lakefile.lean` |
| No project version or license metadata in package configuration | `lakefile.lean`; `lake-manifest.json` `"version": "1.3.0"` is the Lake manifest schema, not a project version |
| GitHub reports the repository license as `None` | GitHub repository API |
| `README.md` says choosing a license is a maintainer decision | `README.md` §Release status |
| No `CONTRIBUTING`, CLA, or DCO file | repository root/tree check |
| Commit authors are automation identities (`LN Fleet`, `LN Integrator`, `LN PhaseC`, `LN PhaseC3`, `Ubuntu`) | `git log --format='%an'` |
| No release tag or GitHub release exists | `git tag -l`; GitHub tags/releases APIs |

The absence of a license is not a neutral default for a public release: in many
jurisdictions it leaves users without a clear permission to copy, modify, or
redistribute the work. The repository should not be tagged as a public release
until the maintainer records a decision and adds the corresponding files.

## 2. Inputs and their obligations

These are the third-party materials a release actually touches. They are not
all code dependencies, and their obligations differ.

| Input | How it is used | License / status | What a release must preserve |
|---|---|---|---|
| `btc-lean` public repository, pin `4f5c4f8` | Authoritative L1 reference for review; not imported | **MIT** (`LICENSE`: "Copyright (c) 2026 btc-lean contributors"; portions derived from Bitcoin Core, MIT; vectors from BIPs/Bitcoin Core test data under their respective terms) | MIT copyright/permission notice and Bitcoin Core notice if its code is copied or redistributed |
| `vendor/btc-lean-core`, pin `f950806` | **Build dependency**; imported as Lake path dependency `«core»` | Snapshot contains **no `LICENSE` file**; commit `f950806` is **not in public `btc-lean` history**; the public repository's MIT license is evidence of project policy but does not by itself prove the grant for this separate lineage | Maintainer must confirm the grant for `f950806`; if the snapshot or a build artifact is distributed, include the upstream MIT text, Bitcoin Core notice, and provenance record |
| `rust-lightning`, pin `fe49009` | Reference-only for `path:line` anchors; not imported | **Dual MIT OR Apache-2.0** (`LICENSE.md`, `LICENSE-MIT`, `LICENSE-APACHE`) | If any code/text is copied, retain the applicable notice; reference-only use does not relicense this tree |
| BOLTs, pin `1aadb71` | Specification text quoted/paraphrased and cited by anchor | **CC-BY-4.0** per-file notices; no root software license detected | Attribution for quoted/adapted BOLT text; CC-BY is not a software license and does not replace the code license |
| Lean 4 toolchain `v4.35.0` | Build toolchain, not vendored | **Apache-2.0** upstream | Not redistributed with source; preserve notices if a binary/toolchain bundle is shipped |

Consequences:

- A permissive code license for this repository does **not** automatically cover
  the vendored snapshot or BOLT text. Those need their own notices.
- The unresolved vendor provenance is a separate blocker from the choice among
  MIT, Apache-2.0, and dual licensing. No license choice can cure an absent
  grant for `f950806`.
- If the release is source-only and the vendor snapshot is not redistributed,
  the vendor remains a documented build prerequisite; this reduces, but does
  not eliminate, the need to explain the provenance and rights.

## 3. Decision matrix

The options are presented neutrally. No ranking is intended and none is
selected here.

| Consideration | MIT | Apache-2.0 | Dual: MIT OR Apache-2.0 |
|---|---|---|---|
| **SPDX identifier** | `MIT` | `Apache-2.0` | `MIT OR Apache-2.0` (downstream chooses) |
| **Core permission** | Broad permission to use, copy, modify, merge, publish, distribute, sublicense, and sell | Broad permission under the Apache License, including sublicensing | Either of the above, at the downstream user's option |
| **Conditions** | Include copyright and permission notice in copies/substantial portions | Include a copy of the license; retain NOTICE files if present; mark modified files; preserve attribution | Ship both license texts and state the dual choice clearly; satisfy the conditions of the option the user selects |
| **Express patent grant** | **No** express patent license | **Yes**, Apache-2.0 §3, with termination if the recipient initiates patent litigation alleging the work infringes | Patent grant is available through the Apache-2.0 option; a user relying on MIT alone does not get it |
| **Trademark** | No trademark license (name/logo rights are separate) | No trademark license (Apache-2.0 §6) | No trademark license; same caveat |
| **Warranty** | “AS IS”, no warranty; broad liability disclaimer | “AS IS”, no warranty; broad liability disclaimer | Same disclaimers under the chosen option |
| **Compatibility with permissive code** | Compatible with MIT/BSD/Apache-2.0 projects | Compatible with MIT/BSD and other permissive projects; Apache-2.0 code can be combined with GPLv3 | Maximum downstream flexibility; standard in the Rust ecosystem |
| **GPL compatibility** | GPL-compatible; can be incorporated into GPLv2/GPLv3 projects | Compatible with GPLv3; **not** GPLv2-only-compatible without a separate arrangement | A downstream GPLv2 project can rely on the MIT option; GPLv3 can rely on either |
| **Compliance burden** | Lowest: one short notice | Higher: license copy, NOTICE handling, modification marking, patent-termination awareness | Highest: two texts, a clear dual-license statement, and consistent contribution terms |
| **Practical considerations for this tree** | Short notice, compatible with the MIT `btc-lean` input; no express patent grant | Same license family as the Apache-2.0 Lean toolchain; adds NOTICE and modification-marking obligations | Same convention as the dual-licensed Rust/LDK ecosystem; gives users a patent-grant option; adds a second license text and messaging overhead |
| **Main risks if chosen** | Patent risk is not addressed by the license; downstream may expect a patent grant that is absent | Some downstream users treat Apache-2.0 as more burdensome; GPLv2-only compatibility needs attention | Users and contributors may be confused about which terms apply; contribution licensing must be stated clearly |
| **Files typically added** | `LICENSE` (MIT text) | `LICENSE` (Apache-2.0 text) and `NOTICE` if notices exist | `LICENSE-MIT`, `LICENSE-APACHE`, and a short `README`/`NOTICE` explaining the choice |
| **Maintainer work if chosen** | Confirm copyright holder; add MIT text; add third-party notices | Confirm copyright holder; add Apache text; establish NOTICE contents; review modification-marking practice | Confirm copyright holder; add both texts; state the dual offer and inbound contribution terms; maintain both notices |

### Note on “dual licensing” beyond MIT/Apache

A separate business model — for example, offering the code under a copyleft or
commercial license alongside a permissive one — is **not** evaluated here. It
normally requires consolidating copyright, a contributor license agreement or
equivalent permission, and legal review. It is a maintainer/business decision,
not an automation decision, and it should not be inferred from the dual
MIT/Apache row above.

## 4. Compatibility analysis for this repository

The choice depends on what is actually distributed:

1. **Source-only release, vendor not redistributed.** The original Lean modules
   can carry MIT, Apache-2.0, or dual MIT/Apache-2.0. The vendor snapshot is a
   build prerequisite. The release notes must still explain how to obtain it
   and must not imply that the repository license covers it.
2. **Source release that redistributes `vendor/btc-lean-core`.** The upstream
   `btc-lean` code is MIT, so any of the three options can coexist with it, but
   the MIT notice and Bitcoin Core notice must be retained. The `f950806`
   lineage grant must be confirmed first; the public `4f5c4f8` LICENSE is not a
   substitute for that confirmation.
3. **Built `.olean` or binary artifact.** Compiled vendor-derived code is still
   third-party code for licensing purposes. The same notice and grant questions
   apply, plus toolchain and build-provenance questions.
4. **Documentation containing BOLT excerpts.** CC-BY-4.0 attribution is
   required independently of the code license. Do not describe the code license
   as covering the BOLT text.
5. **Reference-only `rust-lightning` anchors.** Dual MIT/Apache-2.0 is
   compatible with all three options. If any implementation text or code is
   copied into this tree, preserve its notice.

Patent and warranty notes that apply regardless of option:

- Formal proofs do not reduce patent exposure, and no option here provides an
  indemnity.
- All three options disclaim warranties. A green build, a proved catalog row,
  or a formal theorem is not a warranty of fitness, security, or conformance.
- None of the options grants trademark rights. A project name/logo policy is a
  separate decision.

## 5. Human decisions required

These cannot be made by this lane or by an automated agent. Record each answer
in the decision record below.

1. **Copyright holder / authorized licensor.** Who owns the work, and who is
   authorized to grant the license? The commit history uses automation
   identities; there is no CLA, DCO, or contributor policy. Confirm whether
   contributors' employers or institutions have any claim.
2. **License option.** MIT, Apache-2.0, dual `MIT OR Apache-2.0`, or another
   option after legal review. This document does not choose one.
3. **Contribution policy.** Will future contributions be accepted under the
   chosen outbound license (inbound = outbound), or is a DCO/CLA required?
4. **Vendor redistribution.** Will `vendor/btc-lean-core` be committed,
   published as a separate checksummed artifact, or kept as an external build
   prerequisite? If distributed, confirm the `f950806` grant and include the
   upstream MIT and Bitcoin Core notices.
5. **Commercial/proprietary relicensing.** Is any dual commercial model
   contemplated? If so, obtain the necessary contributor permissions and legal
   review before promising it.
6. **Third-party notice contents.** Approve the exact `NOTICE`/attribution text
   for `btc-lean`, Bitcoin Core, `rust-lightning` (if applicable), and the
   BOLTs CC-BY-4.0 material.
7. **Trademark/name policy.** Decide whether the project name and marks may be
   used by downstream redistributors.
8. **Legal review.** Decide whether counsel should review the choice, the
   notices, and the vendor provenance before publication.

Until these are answered, `OPS-02` stays open and the release remains blocked.

## 6. What changes after the decision

Only the maintainer (or an explicitly authorized integrator) should make these
changes. This lane did not create `LICENSE` or edit `README.md`.

- [ ] Add the chosen root license file(s):
      `LICENSE` for MIT or Apache-2.0; `LICENSE-MIT` + `LICENSE-APACHE` for the
      dual option.
- [ ] Add or update `NOTICE`/`THIRD-PARTY-NOTICES` with the approved
      attribution for `btc-lean`, Bitcoin Core, `rust-lightning` if applicable,
      and the BOLTs CC-BY-4.0 text.
- [ ] Update `README.md` §Release status to name the chosen license and link the
      license/notice files.
- [ ] Update release notes and `docs/RELEASE-CHECKLIST.md` sign-off with the
      decision, approver, and date.
- [ ] If package metadata is added later, set its license field to the chosen
      SPDX expression. Do not treat the Lake manifest schema version as a
      project version or license.
- [ ] Do not edit, relicense, or add headers to `vendor/btc-lean-core`; it is
      read-only. Include its upstream notices in the distribution instead.
- [ ] Do not claim the chosen code license covers BOLT specification text.

## 7. Decision record

This record is intentionally blank. Filling it is the maintainer's decision.

| Field | Value |
|---|---|
| Chosen option (SPDX) | _pending_ |
| Copyright holder | _pending_ |
| Authority/approval basis | _pending_ |
| Contribution policy (DCO/CLA/inbound=outbound) | _pending_ |
| Vendor redistribution decision | _pending_ |
| Vendor grant confirmed for `f950806` | _pending_ |
| Third-party notices approved | _pending_ |
| Trademark/name policy | _pending_ |
| Legal review completed | _pending_ |
| Approver and date | _pending_ |

**No option is selected by this document. Do not add a `LICENSE` file, tag a
release, or state a license in release notes until this record is completed by
the maintainer.**

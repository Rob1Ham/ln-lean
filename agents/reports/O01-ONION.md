# O01-ONION — proof lane report

Scope: `LnLean/Routing/Onion.lean` only (plus this report), branch
`repair/integrated`.  No catalog, traceability, script, vendor, or other lane
files were modified.

## Catalog rows

| Row | Claim | Exact target | Before | After |
|---|---|---|---|---|
| `LN-RT-003` | Peeling one onion layer exposes the next hop or a terminal payload, never both. | `LnLean.Routing.Onion.peel_deterministic` | `statementOnly`, name undeclared | theorem declared and proved; promotion-ready |
| `LN-RT-004` | An onion layer with an invalid HMAC is rejected rather than forwarded. | `LnLean.Routing.Onion.hmac_sound` | `statementOnly`, name undeclared | theorem declared and proved for the checked path; promotion-ready |

The catalog names contain an `Onion` namespace component (the module name),
while the model's `peel` / `openLayer` live directly in `LnLean.Routing`.  The
new declarations therefore sit in an explicit `namespace Onion` block at the
end of `LnLean/Routing/Onion.lean`, before `end LnLean.Routing`.  No existing
declaration, docstring, or wording was changed; the D25 counterexample and its
documentation were not touched (`LnLean/Proofs/WaveD/D25.lean` unchanged).

## LN-RT-003 — exact statement

```lean
theorem LnLean.Routing.Onion.peel_deterministic (p : OnionPacket) :
    (p.layers = [] ∧
        peel p = some (.final p.routingInfo) ∧
          ∀ (hop : OnionHop) (next : OnionPacket),
            peel p = some (.forward hop next) → False) ∨
      (p.layers ≠ [] ∧
        (∃ (hop : OnionHop) (next : OnionPacket),
          peel p = some (.forward hop next) ∧ next.layers = p.layers.tail) ∧
          ∀ (payload : ByteArray), peel p = some (.final payload) → False)
```

Proof: case split on `p.layers`; the `[]` branch is `Or.inl`, the `l :: ls`
branch is `Or.inr`.  The cross-branch negations close by constructor
disjointness of `OnionPayload.final` / `OnionPayload.forward` (`simp [peel]`
exhausts the impossible `some final = some forward` equality).

Why this is not vacuous:

* It is a genuine disjunction over every packet, not a redefinition.
* The final branch fixes the payload to be exactly `p.routingInfo`.
* The forward branch fixes the inner packet to the packet with the head layer
  removed (`next.layers = p.layers.tail`) and requires `p.layers ≠ []`.
* Exclusivity is explicit and proved: the final branch asserts no forwarding
  payload exists, and the forward branch asserts no terminal payload exists.
  Because `.final` and `.forward` are distinct constructors of
  `OnionPayload`, the two outcomes cannot coexist.

Supporting existing declarations used: `peel` (lines 248–251),
`OnionPayload` constructors (225–228), `peel_final_iff`,
`peel_forward_layers`.

## LN-RT-004 — exact statement

```lean
theorem LnLean.Routing.Onion.hmac_sound {I : OnionInterface} {tag : ByteArray}
    {p : OnionPacket} {l : OnionLayer} {ls : List OnionLayer}
    (hp : p.layers = l :: ls) (hver : I.verifyHmac tag l.hmac = false) :
    openLayer I tag p = none

theorem LnLean.Routing.Onion.hmac_sound_not_forwarded
    {I : OnionInterface} {tag : ByteArray}
    {p : OnionPacket} {l : OnionLayer} {ls : List OnionLayer}
    (hp : p.layers = l :: ls) (hver : I.verifyHmac tag l.hmac = false) :
    ¬ ∃ (hop : OnionHop) (next : OnionPacket),
      openLayer I tag p = some (hop, next)
```

Both are direct corollaries of the existing `openLayer_reject`
(`Onion.lean:353–360`); `hmac_sound_not_forwarded` rewrites the rejection to
`none` and derives the absence of the `some (hop, next)` result.

### Why `hmac_sound` is faithful to the catalog claim

The claim has two halves: "rejected" and "rather than forwarded".

* **Rejected.** `hver : I.verifyHmac tag l.hmac = false` is the model's only
  notion of an invalid HMAC (the verifier is opaque; there is no separate
  `valid` predicate).  The theorem concludes `openLayer I tag p = none`, i.e.
  the checked step produces no hop and no inner packet.
* **Rather than forwarded.** `openLayer` is the model's checked forwarding
  step: it is the only operation that returns `(hop, next)` and it performs
  the verifier test before doing so.  `hmac_sound_not_forwarded` states
  explicitly that no forwarding result exists under the rejected HMAC.
* **Raw `peel` is not the forwarding step.** `peel` is the documented
  structural peel: it is total (`peel_isSome`), never consults `I`, and
  returns `some (.forward ...)` even for a layer whose HMAC is rejected.  D25
  mechanises this as `waveD_d25_peel_bypasses_hmac`, using an always-rejecting
  interface: `openLayer ... = none` while `peel` still returns a forward
  payload.  Hence the catalog claim cannot be read as a theorem about `peel`;
  reading it as a theorem about the checked acceptance/forwarding step is the
  only faithful reading of this model.  The docstring of `hmac_sound` states
  this limitation explicitly and cites the D25 counterexample.

Conclusion: the exact name **can** faithfully stand for the catalog claim
under the model's documented separation of structural peeling (`peel`) from
checked forwarding (`openLayer`).  No `statementOnly` fallback is required for
LN-RT-004.  The residual cryptographic content ("a forged HMAC is invalid")
remains the named assumption C8 (`OnionInterface.hmacBinding`), exactly as
before; no security claim beyond the mechanical implication is made.

## Verification

Scratch check file: `/tmp/opencode/btc-lean/check_o01_onion.lean`.

```
#check LnLean.Routing.Onion.peel_deterministic
#check LnLean.Routing.Onion.hmac_sound
#check LnLean.Routing.Onion.hmac_sound_not_forwarded
#print axioms ...
```

Results (RC = 0):

* All three exact names resolve; `#check` prints the statements above.
* `#print axioms`:
  * `peel_deterministic` depends on `[propext]`
  * `hmac_sound` depends on `[propext]`
  * `hmac_sound_not_forwarded` depends on `[propext]`
* No `sorryAx`; no `sorry`, `axiom`, `admit`, `native_decide`, `unsafe`, or
  `@[implemented_by]` introduced.

Build evidence (one Lean process at a time, under
`/tmp/opencode/btc-lean/build.lock`):

| Command | RC |
|---|---|
| `LEAN_NUM_THREADS=1 lake env lean LnLean/Routing/Onion.lean` | 0 |
| `LEAN_NUM_THREADS=1 lake build LnLean.Routing.Onion` | 0 (`✔ [8/8] Built LnLean.Routing.Onion`) |
| `lake env lean /tmp/opencode/btc-lean/check_o01_onion.lean` | 0 |

Note: the requested `lake build -j1 ...` form is not accepted by the pinned
toolchain (Lake `5.0.0-src+eb6cafb`, Lean 4.35.0): `lake build` reports
`unknown short option '-j'` (RC 1).  The build was run without `-j` and with
`LEAN_NUM_THREADS=1`, which serialises Lean elaboration.

Pre-existing working-tree modifications in other lanes
(`Payment/Invoice.lean`, `Payment/MPP.lean`, `Proofs/PhaseC2/...`,
`Proofs/PhaseC3/...`, `Wire/Message.lean`, `agents/status/REPAIR.status`) were
present before this lane and were not touched.

## Promotion verdicts

| Row | Verdict | Action for catalog owner |
|---|---|---|
| `LN-RT-003` | **promotion-ready: yes** | Change `.statementOnly` → `.proved`; exact target now exists in `LnLean.Routing.Onion`. |
| `LN-RT-004` | **promotion-ready: yes** | Change `.statementOnly` → `.proved`; exact target now exists and is faithful for the checked `openLayer` path.  Optionally annotate the row/report that raw `peel` is structural (D25 counterexample) and authenticity remains C8. |

No changes were made to `Obligations.lean`, `Traceability.lean`, or generated
docs; status flips remain with the integrator/owner.

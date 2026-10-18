# M01-PAYMENTS — close LN-PM-002 and LN-PM-005

Lane: `M01-PAYMENTS` (branch `repair/integrated`).
Files changed: `LnLean/Payment/Invoice.lean`, `LnLean/Payment/MPP.lean`,
`agents/reports/M01-PAYMENTS.md`.
No other Lean file, catalog file, script, or vendor file was modified.

## Catalog rows

| Row | Exact target | Old status | Verdict |
| --- | --- | --- | --- |
| `LN-PM-002` | `LnLean.Payment.Invoice.signature_valid` | `statementOnly` | promotion-ready (model-level), ECDSA soundness remains C3 |
| `LN-PM-005` | `LnLean.Payment.MPP.running_total_bound` | `statementOnly` | promotion-ready |

`LnLean/Proofs/Obligations.lean` is outside this lane, so its `status` fields
were **not** edited.  The rows remain `statementOnly` in the catalog until the
catalog owner flips them.  `LnLean/Proofs/Traceability.lean` already lists both
exact names.

## LN-PM-002 — invoice signature valid for the payee node key

Location: `LnLean/Payment/Invoice.lean:267`, inside `namespace
LnLean.Payment.Invoice`.

```lean
theorem signature_valid {digest : Invoice → ByteArray}
    {sigCheck : PubKey → ByteArray → InvoiceSignature → Bool}
    {i : Invoice} (h : verify digest sigCheck i) :
    sigCheck i.payee (digest i) i.signature = true :=
  h.2
```

`#check`:

```text
LnLean.Payment.Invoice.signature_valid {digest : Invoice → ByteArray}
  {sigCheck : PubKey → ByteArray → InvoiceSignature → Bool} {i : Invoice}
  (h : Invoice.verify digest sigCheck i) :
  sigCheck i.payee (digest i) i.signature = true
```

### Proof approach

`Invoice.verify` is defined as

```lean
i.Valid ∧ sigCheck i.payee (digest i) i.signature = true
```

so the theorem is the second projection `h.2`.  There is no induction or
arithmetic.

### What this does and does not establish

* It establishes the **model-level** statement: if the model's verifier
  accepts, then the supplied signature checker returns `true` for the
  invoice's own payee key `i.payee`, the invoice's signable digest `digest i`,
  and the invoice's compact signature `i.signature`.
* It is a **definitional projection from the verification predicate**, not a
  cryptographic proof.  `sigCheck` is an unconstrained parameter; the theorem
  does not show that a real ECDSA verifier rejects forgeries, nor that the key
  is uniquely determined by the signature.
* **`Invoice.Valid` alone does not imply this statement.**  `Valid` contains
  only structural checks (field lengths, amount bound, timestamp bound,
  description-hash length) and says nothing about `sigCheck`; the hypothesis
  must be `Invoice.verify`.
* ECDSA unforgeability/key binding remains assumption **C3**
  (`LnLean.Crypto.Model`), and the BOLT 11 signable-digest construction remains
  `LN-PAY-INVOICE-ENCODING`.  The docstring records both gaps explicitly.

## LN-PM-005 — running MPP total stays at or below `total_msat`

Location: `LnLean/Payment/MPP.lean:176`, inside `namespace LnLean.Payment.MPP`.

```lean
theorem running_total_bound {plan : MPPPlan} (hplan : mppComplete plan) (n : Nat) :
    sumParts (plan.parts.take n) ≤ plan.target.val
```

`#check`:

```text
LnLean.Payment.MPP.running_total_bound {plan : MPPPlan}
  (hplan : mppComplete plan) (n : Nat) :
  sumParts (List.take n plan.parts) ≤ plan.target.val
```

Supporting declarations added in the same namespace/file:

```lean
-- LnLean.Payment (outside namespace MPP)
theorem sumParts_sublist {collected all : List MPPPart}
    (h : List.Sublist collected all) : sumParts collected ≤ sumParts all

-- LnLean.Payment.MPP
def runningTotal (plan : MPPPlan) (n : Nat) : Nat :=
  sumParts (plan.parts.take n)

theorem runningTotal_bound {plan : MPPPlan} (hplan : mppComplete plan)
    (n : Nat) : runningTotal plan n ≤ plan.target.val

theorem running_total_add_part {plan : MPPPlan} (hplan : mppComplete plan)
    {collected : List MPPPart} {next : MPPPart}
    (hsub : List.Sublist (collected ++ [next]) plan.parts) :
    sumParts (collected ++ [next]) ≤ plan.target.val

theorem runningTotal_mono (plan : MPPPlan) {m n : Nat} (hmn : m ≤ n) :
    runningTotal plan m ≤ runningTotal plan n

theorem runningTotal_succ (plan : MPPPlan) {n : Nat}
    (hn : n < plan.parts.length) :
    runningTotal plan (n + 1) =
      runningTotal plan n + (plan.parts[n]'hn).amount.val
```

### Proof approach

1. `sumParts_sublist`: induction on the `List.Sublist` derivation.  Each
   constructor either leaves the sum unchanged (`slnil`) or adds the same
   non-negative `Nat` amount to both sides (`cons`, `cons_cons`), discharged
   by `omega`.
2. `running_total_bound`: `List.take_sublist n plan.parts` gives
   `plan.parts.take n <+ plan.parts`; `sumParts_sublist` yields
   `sumParts (plan.parts.take n) ≤ sumParts plan.parts`; rewriting with
   `hplan.2` (`sumParts plan.parts = plan.target.val`) closes the goal.
3. `running_total_add_part` is the literal "each additional part" form for an
   arbitrary arrival order: the extended collection `collected ++ [next]` is
   still a sub-multiset of the plan, so the same sublist bound applies.
4. `runningTotal_mono` composes `take` with the sublist bound and
   `List.take_take`; `runningTotal_succ` uses `List.take_add_one`,
   `sumParts_append`, and `sumParts_cons` to show the increment is exactly the
   arriving part's amount.

The statement covers every prefix length `n`, i.e. every intermediate
collection state, not only the completed plan.  It genuinely uses the
`mppComplete` invariant `sumParts plan.parts = plan.target.val`; without that
invariant the claim is false when a part amount exceeds the target (the
pre-existing `Laws.mppComplete_no_part_exceeds_target` and D30 counterexample
record why the hypothesis cannot be dropped).  The model's `mppComplete` is
the exact-sum form; BOLT 4's `sum ≥ total_msat` overpay variant remains
`LN-PAY-MPP-OVERPAY`.

## Build evidence

All commands run from `/home/ubuntu/ln-lean-repair` with one Lean process at a
time under `/tmp/opencode/btc-lean/build.lock`.

```text
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake env lean LnLean/Payment/Invoice.lean
RC=0

LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake env lean LnLean/Payment/MPP.lean
RC=0

LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Payment.MPP LnLean.Payment.Invoice
✔ [8/8] Built LnLean.Payment.MPP
Build completed successfully (8 jobs).
RC=0
```

Note: this repository uses Lake 5.0.0, which rejects the requested `-j1`
(`error: unknown short option '-j'`).  Serialization was enforced with
`LEAN_NUM_THREADS=1` plus the build lock, and `lake build` completed RC 0.

Exact-name check performed in `/tmp/opencode/btc-lean/check_m01_payments.lean`
with `#check`/`#print`; RC 0 for both catalog targets and all supporting
declarations.

Forbidden-token scan on the two changed Lean files found no `sorry`, `axiom`,
`admit`, `native_decide`, `unsafe`, or `@[implemented_by]` (the only textual
match for "axiom" is the pre-existing prose "conditional, never an axiom").

## Promotion verdicts

* **LN-PM-002: yes, promotion-ready as a model-level theorem.**  Promote with
  the wording that the guarantee is relative to the supplied `sigCheck`; it is
  a projection from `Invoice.verify`, and cryptographic ECDSA soundness/key
  binding is still assumption C3.  Do not promote it as an unconditional
  cryptographic signature-soundness result.
* **LN-PM-005: yes, promotion-ready.**  The exact prefix/running-total bound is
  proved under `mppComplete`, with supporting add-part, monotonicity, and
  increment lemmas.

Remaining catalog action (outside this lane): change both rows in
`LnLean/Proofs/Obligations.lean` from `.statementOnly` to `.proved`.

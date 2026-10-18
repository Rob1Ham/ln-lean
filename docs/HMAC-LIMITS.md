# HMAC limits after the M02 repair

## What was wrong

`PrimitiveModel` used to contain

```lean
hmac_prf : HmacPrf hmacSha256
HmacPrf h := ∀ k m₁ m₂, h k m₁ = h k m₂ → m₁ = m₂
```

together with

```lean
hmac_size : ∀ k m, (hmacSha256 k m).size = 32.
```

For a fixed key `k`, the function `m ↦ hmacSha256 k m` would be an injection
from all of `ByteArray` into the finite set of 32-byte strings.  This is the
same pigeonhole contradiction as the removed global SHA-256 preimage field:
the structure was uninhabited, so the D07 "C8" theorems were vacuous.

## The repair

1. `hmac_prf` is no longer a field of `PrimitiveModel`.  The abbreviation
   `HmacPrf` is kept only for traceability.
2. `LnLean.Proofs.WaveD.D07.hmacPrf_vacuous` proves the negative result

   ```lean
   hmacPrf_vacuous (M : PrimitiveModel) (k : ByteArray) :
       ¬ HmacPrf M.hmacSha256
   ```

   by applying `no_injective_hash_into_32_bytes` to the fixed-key slice
   `m ↦ M.hmacSha256 k m` and `M.hmac_size k`.  This is a theorem, not an
   axiom.
3. C8 is now the finite-execution admission

   ```lean
   HmacBindsOn hmac mu msgs :=
     ∀ m₁ ∈ msgs, ∀ m₂ ∈ msgs,
       hmac mu m₁ = hmac mu m₂ → m₁ = m₂
   ```

   where `msgs` is the finite list of `hop_payloads || associated_data`
   values in one onion execution.  D07's uniqueness, no-reuse and
   `openWithHmac_layer_authentic` theorems take this contract plus explicit
   membership hypotheses for the concatenations involved.
4. `hmacOnionInterface M mu msgs` stores `HmacBindsOn M.hmacSha256 mu msgs`
   in its `hmacBinding` field.  No interface or positive theorem assumes
   global `HmacPrf`.

## Why the new contract is satisfiable

The contract only quantifies over a finite list.  If the tags of the
messages in `msgs` are pairwise distinct, it holds; this is
`hmacBindsOn_of_pairwise_tags`.  In particular `hmacBindsOn_singleton`
proves `HmacBindsOn hmac mu [m]` for every HMAC, key and message, with no
cryptographic assumption.  Unlike global injectivity, this does not conflict
with the 32-byte output width.

## Remaining C8 trust boundary

The model does **not** prove computational HMAC security.  C8 remains an
explicit admission supplied by the caller at the onion boundary:

* the caller must exhibit the finite message list and the
  `HmacBindsOn` evidence (normally discharged outside the model from the
  assumption that the concrete HMAC tags are distinct on that execution);
* tag collision resistance, PRF distinguishing advantage, forgery
  probability and computational reductions are not modelled;
* the mechanical facts — 32-byte tag width, verifier equality, and the
  extraction of the stored tag from a successful open — are proved
  unconditionally.

No theorem in `LnLean` claims computational HMAC security or global HMAC
injectivity.

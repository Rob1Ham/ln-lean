import LnLean.Routing.Gossip
import LnLean.Routing.Graph
import LnLean.Routing.Laws
import LnLean.Routing.Onion
import LnLean.Routing.Route

/-!
# E24 — Peeling one onion layer exposes the next hop or a terminal payload, never both

BOLT 4 "Onion Decryption" says that a node unwraps exactly one layer and then
either forwards the remaining packet to the next hop or, when no layer
remains, delivers the terminal payload.  The Lean model represents this split
with `OnionPayload.forward hop next` and `OnionPayload.final payload`, and
`peel` chooses the branch by pattern-matching on `p.layers`.

The claim proved here is the structural one, with no cryptographic
hypothesis:

* `peel` is a function, so its result is unique
  (`waveE_e24_peel_deterministic`, `waveE_e24_peel_existsUnique`).
* The two constructors are disjoint, so a single peel cannot expose both a
  next hop and a terminal payload (`waveE_e24_peel_never_both`).
* The result is exhaustive: an empty layer list gives exactly the terminal
  `routingInfo`, and a non-empty list gives exactly the head layer's hop
  (`waveE_e24_peel_branch_exhaustive`,
  `waveE_e24_peel_forward_iff`, `waveE_e24_peel_final_iff`).
* A forward peel removes exactly one layer
  (`waveE_e24_peel_forward_layerCount`), matching "one onion layer".
* The branches are inhabited (`waveE_e24_sealLayers_zero_peels_final`,
  `waveE_e24_sealLayers_one_peels_forward`), so the exclusivity statement is
  not vacuous.

What is *not* claimed: `peel` in this model does not verify the HMAC (that is
`openLayer`) and does not decrypt anything.  Ciphertexts and HMACs are opaque.
The mapping "accepted HMAC implies authentic layer" is the named assumption
C8 in `OnionInterface.hmacBinding`; it is irrelevant to the structural branch
disjointness proved here.
-/

namespace LnLean.Proofs.WaveE.E24

open LnLean.Routing

set_option autoImplicit false

-- OBLIGATION: LN-WE-E24

/-! ## Uniqueness and disjointness of the peel result -/

/-- **Peel determinism.**  A packet has at most one peel result: two
executions of `peel` on the same packet agree.  This is the direct formal
content of "either the next hop or the terminal payload", with no choice
left between them. -/
theorem waveE_e24_peel_deterministic (p : OnionPacket)
    (a b : OnionPayload) (ha : peel p = some a) (hb : peel p = some b) :
    a = b := by
  rw [ha] at hb
  exact Option.some.inj hb

/-- **Peeling returns exactly one payload.**  The existential-uniqueness form
of `waveE_e24_peel_deterministic`. -/
theorem waveE_e24_peel_existsUnique (p : OnionPacket) :
    ∃ o : OnionPayload,
      peel p = some o ∧ ∀ b : OnionPayload, peel p = some b → b = o := by
  rcases p with ⟨v, k, r, layers, hm⟩
  cases layers with
  | nil =>
    refine ⟨.final r, rfl, ?_⟩
    intro b hb
    cases hb
    rfl
  | cons l ls =>
    refine ⟨.forward l.hop ⟨v, k, r, ls, hm⟩, rfl, ?_⟩
    intro b hb
    cases hb
    rfl

/-- **Never both.**  No packet peels to a forwarding instruction and to a
terminal payload at the same time.  This is the headline claim: the
constructors `OnionPayload.forward` and `OnionPayload.final` are disjoint. -/
theorem waveE_e24_peel_never_both (p : OnionPacket) :
    ¬ ∃ (hop : OnionHop) (next : OnionPacket) (payload : ByteArray),
        peel p = some (.forward hop next) ∧
          peel p = some (.final payload) := by
  rintro ⟨hop, next, payload, hf, hfin⟩
  have h : OnionPayload.forward hop next = OnionPayload.final payload :=
    waveE_e24_peel_deterministic p _ _ hf hfin
  cases h

/-- If two peels both expose a next hop, they expose the same hop and the
same inner packet. -/
theorem waveE_e24_peel_forward_unique (p : OnionPacket)
    (hop₁ : OnionHop) (next₁ : OnionPacket)
    (hop₂ : OnionHop) (next₂ : OnionPacket)
    (h₁ : peel p = some (.forward hop₁ next₁))
    (h₂ : peel p = some (.forward hop₂ next₂)) :
    hop₁ = hop₂ ∧ next₁ = next₂ := by
  have h := waveE_e24_peel_deterministic p _ _ h₁ h₂
  cases h
  exact ⟨rfl, rfl⟩

/-- If two peels both expose a terminal payload, the payloads are equal. -/
theorem waveE_e24_peel_final_unique (p : OnionPacket)
    (payload₁ payload₂ : ByteArray)
    (h₁ : peel p = some (.final payload₁))
    (h₂ : peel p = some (.final payload₂)) :
    payload₁ = payload₂ := by
  have h := waveE_e24_peel_deterministic p _ _ h₁ h₂
  cases h
  rfl

/-! ## Exact characterisation of each branch -/

/-- **Forward branch, exactly.**  A peel exposes `hop` and `next` iff the
packet has a head layer `l` whose hop is `hop`, and `next` is the packet
with that one head layer removed.  In particular the exposed next hop is the
head layer's hop, not some other layer's. -/
theorem waveE_e24_peel_forward_iff (p : OnionPacket) (hop : OnionHop)
    (next : OnionPacket) :
    peel p = some (.forward hop next) ↔
      ∃ (l : OnionLayer) (ls : List OnionLayer),
        p.layers = l :: ls ∧ l.hop = hop ∧
          next = { p with layers := ls } := by
  constructor
  · intro h
    rcases p with ⟨v, k, r, layers, hm⟩
    cases layers with
    | nil => simp [peel] at h
    | cons l ls =>
      change some (OnionPayload.forward l.hop ⟨v, k, r, ls, hm⟩) =
        some (OnionPayload.forward hop next) at h
      cases h
      exact ⟨l, ls, rfl, rfl, rfl⟩
  · rintro ⟨l, ls, hp, hhop, hnext⟩
    rcases p with ⟨v, k, r, layers, hm⟩
    simp only at hp
    subst hp
    subst hhop
    subst hnext
    rfl

/-- **Final branch, exactly.**  A peel exposes a terminal payload iff no
layer remains and the payload is the packet's `routingInfo`.  Restated from
the model's `peel_final_iff` for the local theorem family. -/
theorem waveE_e24_peel_final_iff (p : OnionPacket) (payload : ByteArray) :
    peel p = some (.final payload) ↔
      p.layers = [] ∧ payload = p.routingInfo :=
  peel_final_iff p payload

/-- **Exhaustiveness.**  Every packet falls in exactly one of the two
branches: either its layer list is empty and it yields the terminal payload,
or its layer list is non-empty and it yields a next hop. -/
theorem waveE_e24_peel_branch_exhaustive (p : OnionPacket) :
    (p.layers = [] ∧ peel p = some (.final p.routingInfo)) ∨
      (p.layers ≠ [] ∧
        ∃ (hop : OnionHop) (next : OnionPacket),
          peel p = some (.forward hop next)) := by
  rcases p with ⟨v, k, r, layers, hm⟩
  cases layers with
  | nil => exact Or.inl ⟨rfl, rfl⟩
  | cons l ls =>
    exact Or.inr ⟨by simp, l.hop, ⟨v, k, r, ls, hm⟩, rfl⟩

/-- A forward peel removes exactly one layer, so the inner packet has one
fewer layer than the outer packet.  This is the "one onion layer" part of
the claim, stated without truncated subtraction. -/
theorem waveE_e24_peel_forward_layerCount (p : OnionPacket) (hop : OnionHop)
    (next : OnionPacket) (h : peel p = some (.forward hop next)) :
    next.layers.length + 1 = p.layers.length := by
  rcases p with ⟨v, k, r, layers, hm⟩
  cases layers with
  | nil => simp [peel] at h
  | cons l ls =>
    change some (OnionPayload.forward l.hop ⟨v, k, r, ls, hm⟩) =
      some (OnionPayload.forward hop next) at h
    cases h
    simp

/-! ## Non-vacuity witnesses -/

/-- A concrete hop used only to exhibit both peel branches. -/
def waveE_e24_testHop : OnionHop :=
  { node := ⟨0⟩
    shortChannelId := ⟨0, 0, 0⟩
    amountMsat := ⟨0⟩
    cltvDelta := 0 }

/-- A concrete (empty) public key for the witness packets. -/
def waveE_e24_testKey : PubKey := ⟨ByteArray.empty⟩

/-- A zero-hop sealed packet peels to a terminal payload. -/
theorem waveE_e24_sealLayers_zero_peels_final (payload : ByteArray) :
    peel (sealLayers ONION_VERSION waveE_e24_testKey [] payload) =
      some (.final payload) := rfl

/-- A one-hop sealed packet peels to a forwarding instruction whose next
packet has no layers left. -/
theorem waveE_e24_sealLayers_one_peels_forward (payload : ByteArray) :
    ∃ next : OnionPacket,
      peel (sealLayers ONION_VERSION waveE_e24_testKey
        [waveE_e24_testHop] payload) =
        some (.forward waveE_e24_testHop next) ∧ next.layers = [] := by
  exact ⟨_, rfl, rfl⟩

/-- The one-hop witness cannot simultaneously yield a terminal payload. -/
theorem waveE_e24_sealLayers_one_not_final (payload : ByteArray) :
    ¬ ∃ terminal : ByteArray,
        peel (sealLayers ONION_VERSION waveE_e24_testKey
          [waveE_e24_testHop] payload) = some (.final terminal) := by
  rintro ⟨terminal, h⟩
  simp [sealLayers, peel] at h

end LnLean.Proofs.WaveE.E24

import LnLean.Protocol.Handshake
import LnLean.Protocol.Laws
import LnLean.Protocol.Messages
import LnLean.Protocol.Peer
import LnLean.Channel.Commitment

/-!
# LnLean.Proofs.WaveE.E20

## English claim

BOLT 2 §"Committing Updates So Far": a `commitment_signed` carries one
signature over the counterparty's commitment transaction — which fixes the
`to_local` / `to_remote` outputs, every untrimmed HTLC output, and the fee
(the residual of the funding value after those outputs) — plus exactly one
signature per HTLC output in that transaction, in commitment order.

## Result

The wave-A model does **not** connect `LnLean.Protocol.CommitmentSigned` to
`LnLean.Channel.Commitment`.  The wire record has a `channelId`, one ECDSA
signature, and an unconstrained list of HTLC signatures; no field names the
commitment transaction, the HTLC set, the fee, or a commitment number, and
`Msg.wellFormed` only bounds signature *lengths* (ECDSA verification is
assumption C3 in `docs/ASSUMPTIONS.md`).  The unconditional reading is
therefore not derivable, and it is in fact false for the model as written.

What is proved here:

1. **Wire accounting.**  `msgLength` of a `commitment_signed` is exactly
   `34 + sigLen signature + sigListLen htlcSignatures`: the 32-byte channel
   id, the 2-byte HTLC count, one DER signature for the commitment
   transaction, and one DER signature per HTLC signature entry.  The
   `signatures` list of the message is `signature :: htlcSignatures`.
2. **The BOLT 2 intent as a predicate.**
   `waveE_e20_commitment_signed_covers m r c` says that `m` carries exactly
   one HTLC signature per untrimmed HTLC output of `c` (equal length, the
   model's positional form of "one per output") and that `c` pays exactly the
   BOLT 3 formula fee at feerate `r`.
3. **The strongest true "covers" statement.**  Under that predicate, the
   number of wire signatures is exactly `#htlcs + 1`, the payload size obeys
   `msgLength ≤ 34 + 73 + 73 * #htlcs`, and two commitments covered by the
   same message have the same HTLC-output count and — when both satisfy the
   BOLT 3 fee formula at the same feerate and agree on `option_anchors` — the
   same fee.
4. **Negative results.**  For every message and every natural number `fee`
   there is a commitment with `htlcs.length = htlcSignatures.length` and
   `feeSat = fee`; an empty `htlcSignatures` list covers no non-empty
   commitment; a single message can "cover" two commitments with different
   HTLC sets of the same cardinality.  Hence the unconditional claim is
   false, and the missing link is a signed-commitment relation
   `CommitmentSigned → Commitment → Prop` together with cryptographic
   signature verification (C3).

## Anchors

* BOLT 2 §"Committing Updates So Far" (`refs/bolts/02-peer-protocol.md`,
  pinned `1aadb719b4007c4cea0ba6e36b08c4fb53788dee`): `commitment_signed`
  layout (type 132), one signature for the remote commitment transaction and
  one per HTLC output.
* LDK (pinned `fe4900930c6bd5786ec4203274d7cf312776a5a6`)
  `lightning/src/ln/channel.rs:2386` (signing the remote commitment) and
  `lightning/src/ln/channel.rs:6270` (building `commitment_signed`).
* Model: `LnLean/Protocol/Messages.lean` (`CommitmentSigned`, `msgLength`,
  `signatures`, `wellFormed`) and `LnLean/Channel/Commitment.lean`
  (`Commitment`, `commitmentWeight`, `commitmentFee`).

## What is NOT modelled

* ECDSA signing and verification (C3/C4); the `signature` field is opaque.
* The commitment number is absent from `CommitmentSigned` (compare the
  duplicate-detection gap documented in `ChannelReestablishProps`).
* The message carries no HTLC identifier, amount, or direction, so positional
  coverage can pin only the *number* of HTLC outputs, not their contents.
-/

namespace LnLean.Proofs.WaveE.E20

set_option autoImplicit false

open LnLean
open LnLean.Protocol
open LnLean.Channel

-- OBLIGATION: LN-WE-E20

/-! ## 1. Structural accounting of a `commitment_signed` -/

/-- BOLT 2 `commitment_signed` payload: `32 + 2 + sigLen + sigListLen`. -/
@[simp] theorem waveE_e20_msgLength_commitment_signed (m : CommitmentSigned) :
    msgLength (.commitmentSigned m) =
      34 + sigLen m.signature + sigListLen m.htlcSignatures := rfl

/-- The signature list of a `commitment_signed` is the commitment signature
followed by the HTLC signatures, and nothing else. -/
@[simp] theorem waveE_e20_signatures_commitment_signed (m : CommitmentSigned) :
    signatures (.commitmentSigned m) = m.signature :: m.htlcSignatures := rfl

/-- The message carries one signature beyond the per-HTLC signatures: the
single signature over the commitment transaction. -/
theorem waveE_e20_signature_count (m : CommitmentSigned) :
    (signatures (.commitmentSigned m)).length = m.htlcSignatures.length + 1 := by
  simp [signatures]

/-- Membership in the wire signature list splits into the commitment
signature and the HTLC signatures. -/
theorem waveE_e20_mem_signatures_iff (m : CommitmentSigned) (s : EcdsaSig) :
    s ∈ signatures (.commitmentSigned m) ↔
      s = m.signature ∨ s ∈ m.htlcSignatures := by
  simp [signatures]

/-- Accumulating signature lengths from an arbitrary initial value. -/
private theorem waveE_e20_foldl_size_add (ss : List EcdsaSig) (a : Nat) :
    ss.foldl (fun acc s => acc + s.bytes.size) a = a + sigListLen ss := by
  induction ss generalizing a with
  | nil => simp [sigListLen]
  | cons s t ih =>
      have h : (s :: t).foldl (fun acc s => acc + s.bytes.size) a =
          (a + s.bytes.size) + sigListLen t := by
        rw [List.foldl_cons, ih]
      have hs : sigListLen (s :: t) = s.bytes.size + sigListLen t := by
        change t.foldl (fun acc s => acc + s.bytes.size) (0 + s.bytes.size)
            = s.bytes.size + sigListLen t
        rw [ih]
        omega
      rw [h, hs]
      omega

/-- One signature contributes its size to `sigListLen` and nothing else. -/
theorem waveE_e20_sigListLen_cons (s : EcdsaSig) (ss : List EcdsaSig) :
    sigListLen (s :: ss) = s.bytes.size + sigListLen ss := by
  change ss.foldl (fun acc s => acc + s.bytes.size) (0 + s.bytes.size)
      = s.bytes.size + sigListLen ss
  rw [waveE_e20_foldl_size_add]
  omega

/-- `sigListLen` is the sum of the supplied signature sizes. -/
theorem waveE_e20_sigListLen_eq_sum (ss : List EcdsaSig) :
    sigListLen ss = (ss.map (fun s => s.bytes.size)).sum := by
  induction ss with
  | nil => rfl
  | cons s t ih =>
      rw [waveE_e20_sigListLen_cons, ih]
      simp

/-- A list of DER signatures of at most 73 bytes each contributes at most
73 bytes per element to the payload. -/
theorem waveE_e20_sigListLen_le_length_mul (ss : List EcdsaSig)
    (h : ∀ s ∈ ss, s.bytes.size ≤ 73) :
    sigListLen ss ≤ 73 * ss.length := by
  induction ss with
  | nil => simp [sigListLen]
  | cons s t ih =>
      have hs : s.bytes.size ≤ 73 := h s (by simp)
      have ht : ∀ x ∈ t, x.bytes.size ≤ 73 := fun x hx => h x (by simp [hx])
      have hrec := ih ht
      rw [waveE_e20_sigListLen_eq_sum]
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [waveE_e20_sigListLen_eq_sum] at hrec
      omega

/-! ## 2. The BOLT 2 coverage predicate -/

/-- BOLT 2 coverage of the HTLC set: one HTLC signature per untrimmed HTLC
output of the commitment.  Signatures are positional on the wire, so list
length is the exact model form of "one signature per output". -/
def waveE_e20_covers_htlcs (m : CommitmentSigned) (c : Commitment) : Prop :=
  m.htlcSignatures.length = c.htlcs.length

/-- BOLT 3 fee exactness: the commitment pays exactly the floored product of
the negotiated feerate and its expected weight. -/
def waveE_e20_covers_fee (r : FeeRate) (c : Commitment) : Prop :=
  c.feeSat = (commitmentFee r c).val

/-- BOLT 2 §"Committing Updates So Far", as a predicate on a wire message and
a commitment transaction: exactly one HTLC signature per untrimmed HTLC
output, and the commitment's fee is the BOLT 3 formula fee.  The single
`signature` field is the signature over this whole transaction; the model
does not verify it (C3). -/
def waveE_e20_commitment_signed_covers (m : CommitmentSigned) (r : FeeRate)
    (c : Commitment) : Prop :=
  waveE_e20_covers_htlcs m c ∧ waveE_e20_covers_fee r c

/-! ## 3. Positive consequences of coverage -/

/-- Under coverage, the wire message carries exactly `#htlcs + 1`
signatures: one for the commitment transaction and one per HTLC output. -/
theorem waveE_e20_signature_count_of_covers
    (m : CommitmentSigned) (r : FeeRate) (c : Commitment)
    (hc : waveE_e20_commitment_signed_covers m r c) :
    (signatures (.commitmentSigned m)).length = c.htlcs.length + 1 := by
  have hh : m.htlcSignatures.length = c.htlcs.length := hc.1
  rw [waveE_e20_signature_count, hh]

/-- Under coverage and BOLT 1 well-formedness, the payload is exactly
accounted for: fixed 34 bytes, at most 73 bytes for the commitment
signature, and at most 73 bytes for each HTLC signature. -/
theorem waveE_e20_msgLength_le_of_covers
    (m : CommitmentSigned) (r : FeeRate) (c : Commitment)
    (hc : waveE_e20_commitment_signed_covers m r c)
    (hwf : wellFormed (.commitmentSigned m)) :
    msgLength (.commitmentSigned m) ≤ 34 + 73 + 73 * c.htlcs.length := by
  obtain ⟨hlen, _⟩ := hc
  have hlen' : m.htlcSignatures.length = c.htlcs.length := hlen
  have hsig : m.signature.bytes.size ≤ 73 :=
    wellFormed_signature hwf (by simp [signatures])
  have hsigs : ∀ s ∈ m.htlcSignatures, s.bytes.size ≤ 73 := by
    intro s hs
    exact wellFormed_signature hwf (by simp [signatures, hs])
  have hlist := waveE_e20_sigListLen_le_length_mul m.htlcSignatures hsigs
  rw [waveE_e20_msgLength_commitment_signed, ← hlen']
  unfold sigLen
  omega

/-- The covered HTLC count is determined by the message: two commitments
covered by the same `commitment_signed` have the same number of untrimmed
HTLC outputs. -/
theorem waveE_e20_htlc_count_determined
    (m : CommitmentSigned) (r : FeeRate) (c c' : Commitment)
    (hc : waveE_e20_commitment_signed_covers m r c)
    (hc' : waveE_e20_commitment_signed_covers m r c') :
    c.htlcs.length = c'.htlcs.length := by
  have h1 : m.htlcSignatures.length = c.htlcs.length := hc.1
  have h2 : m.htlcSignatures.length = c'.htlcs.length := hc'.1
  rw [← h1, h2]

/-- The fee is determined as soon as the covered HTLC count, the feerate, and
`option_anchors` are fixed: both commitments use the same BOLT 3 weight and
therefore the same floored fee. -/
theorem waveE_e20_fee_determined
    (m : CommitmentSigned) (r : FeeRate) (c c' : Commitment)
    (hc : waveE_e20_commitment_signed_covers m r c)
    (hc' : waveE_e20_commitment_signed_covers m r c')
    (hanch : c.anchorOutputs = c'.anchorOutputs) :
    c.feeSat = c'.feeSat := by
  obtain ⟨hlen, hfee⟩ := hc
  obtain ⟨hlen', hfee'⟩ := hc'
  have h1 : m.htlcSignatures.length = c.htlcs.length := hlen
  have h2 : m.htlcSignatures.length = c'.htlcs.length := hlen'
  rw [hfee, hfee']
  unfold commitmentFee Commitment.weight
  rw [← h1, ← h2, hanch]

/-- The bundled statement of the BOLT 2 obligation under the coverage
predicate: exact HTLC count, exact signature count, size accounting, and the
BOLT 3 fee equation. -/
theorem waveE_e20_commitment_signed_covers_exact
    (m : CommitmentSigned) (r : FeeRate) (c : Commitment)
    (hc : waveE_e20_commitment_signed_covers m r c)
    (hwf : wellFormed (.commitmentSigned m)) :
    m.htlcSignatures.length = c.htlcs.length ∧
      (signatures (.commitmentSigned m)).length = c.htlcs.length + 1 ∧
      msgLength (.commitmentSigned m) ≤ 34 + 73 + 73 * c.htlcs.length ∧
      c.feeSat = (commitmentFee r c).val := by
  obtain ⟨hh, hf⟩ := hc
  have hh' : m.htlcSignatures.length = c.htlcs.length := hh
  refine ⟨hh', ?_, ?_, hf⟩
  · rw [waveE_e20_signature_count, hh']
  · exact waveE_e20_msgLength_le_of_covers m r c ⟨hh, hf⟩ hwf

/-! ## 4. The predicate is inhabited (coverage is not vacuous) -/

/-- A concrete non-dust HTLC output used by the counterexamples. -/
def waveE_e20_sampleHtlc : CommitmentHTLCOutput where
  direction := .local
  amountSat := 1000
  cltvExpiry := 100
  state := .offered

/-- A second HTLC output with the same length but different contents. -/
def waveE_e20_sampleHtlcRemote : CommitmentHTLCOutput where
  direction := .remote
  amountSat := 2000
  cltvExpiry := 100
  state := .offered

/-- A commitment carrying `n` copies of the sample HTLC and an arbitrary fee. -/
def waveE_e20_commitmentWith (n fee : Nat) : Commitment where
  holder := .local
  commitmentNumber := 0
  fundingValueSat := 100000
  toLocalSat := 10000
  toRemoteSat := 10000
  htlcs := List.replicate n waveE_e20_sampleHtlc
  feeSat := fee
  contestDelay := 144
  anchorOutputs := false

@[simp] theorem waveE_e20_commitmentWith_htlcs (n fee : Nat) :
    (waveE_e20_commitmentWith n fee).htlcs.length = n := by
  simp [waveE_e20_commitmentWith]

/-- For every message and feerate there is a commitment that it covers. -/
theorem waveE_e20_exists_covered_commitment
    (m : CommitmentSigned) (r : FeeRate) :
    ∃ c : Commitment, waveE_e20_commitment_signed_covers m r c := by
  let c := waveE_e20_commitmentWith m.htlcSignatures.length 0
  refine ⟨{ c with feeSat := (commitmentFee r c).val }, ?_, rfl⟩
  simp [waveE_e20_covers_htlcs, c, waveE_e20_commitmentWith]

/-! ## 5. Negative results: the model does not enforce coverage -/

/-- The empty `commitment_signed`: a valid `channelId`, a signature, and no
HTLC signatures at all. -/
def waveE_e20_emptyCommitmentSigned : CommitmentSigned where
  channelId := ChannelId.zero
  signature := ⟨ByteArray.empty⟩
  htlcSignatures := []

/-- **The unconditional claim is false.**  There is a `commitment_signed`
with no HTLC signatures and a commitment with one HTLC output; the message
therefore does not cover the current HTLC set.  Nothing in the model ties
`htlcSignatures` to the channel's HTLC list. -/
theorem waveE_e20_commitment_signed_covers_unconditional_false :
    ¬ (∀ (m : CommitmentSigned) (r : FeeRate) (c : Commitment),
        waveE_e20_commitment_signed_covers m r c) := by
  intro h
  have hh := (h waveE_e20_emptyCommitmentSigned ⟨0⟩
    (waveE_e20_commitmentWith 1 0)).1
  simp [waveE_e20_covers_htlcs, waveE_e20_emptyCommitmentSigned,
    waveE_e20_commitmentWith] at hh

/-- A message with no HTLC signatures never covers a commitment with an
untrimmed HTLC. -/
theorem waveE_e20_empty_signatures_do_not_cover
    (r : FeeRate) (c : Commitment) (hne : c.htlcs ≠ []) :
    ¬ waveE_e20_commitment_signed_covers waveE_e20_emptyCommitmentSigned r c := by
  intro hc
  have hh := hc.1
  simp [waveE_e20_covers_htlcs, waveE_e20_emptyCommitmentSigned] at hh
  exact hne (List.eq_nil_of_length_eq_zero hh.symm)

/-- **The fee is not pinned by the message.**  For any message and any fee
value there is a commitment with the message's HTLC-signature count and that
exact fee.  Since `covers_htlcs` only sees the list length, a single message
is compatible with commitments paying any fee. -/
theorem waveE_e20_fee_not_determined_by_message
    (m : CommitmentSigned) (fee : Nat) :
    ∃ c : Commitment,
      waveE_e20_covers_htlcs m c ∧ c.feeSat = fee := by
  refine ⟨waveE_e20_commitmentWith m.htlcSignatures.length fee, ?_, rfl⟩
  simp [waveE_e20_covers_htlcs, waveE_e20_commitmentWith]

/-- **The HTLC set is not pinned by the message**, only its cardinality: one
message covers two commitments with different HTLC output lists of the same
length.  The wire message carries no HTLC identifier, amount, or direction. -/
theorem waveE_e20_same_message_different_htlc_sets :
    ∃ (m : CommitmentSigned) (c₁ c₂ : Commitment),
      c₁.htlcs ≠ c₂.htlcs ∧
        waveE_e20_covers_htlcs m c₁ ∧ waveE_e20_covers_htlcs m c₂ := by
  let m : CommitmentSigned :=
    { channelId := ChannelId.zero
      signature := ⟨ByteArray.empty⟩
      htlcSignatures := [⟨ByteArray.empty⟩] }
  let c₁ := waveE_e20_commitmentWith 1 0
  let c₂ : Commitment :=
    { (waveE_e20_commitmentWith 1 0) with
      htlcs := [waveE_e20_sampleHtlcRemote] }
  refine ⟨m, c₁, c₂, ?_, ?_, ?_⟩
  · intro h
    have hmap := congrArg
      (fun l : List CommitmentHTLCOutput =>
        l.map (fun x => (x.direction, x.amountSat))) h
    simp [c₁, c₂, waveE_e20_commitmentWith, waveE_e20_sampleHtlc,
      waveE_e20_sampleHtlcRemote] at hmap
  · simp [waveE_e20_covers_htlcs, m, c₁, waveE_e20_commitmentWith]
  · simp [waveE_e20_covers_htlcs, m, c₂]

/-- The decoder accepts the empty-signature message, so `wellFormed` cannot
enforce coverage: `sigsValid` only checks DER lengths. -/
theorem waveE_e20_wellFormed_empty_signatures :
    wellFormed (.commitmentSigned waveE_e20_emptyCommitmentSigned) := by
  refine ⟨?_, ?_, ?_, trivial⟩
  · simp [msgLength, sigLen, sigListLen, waveE_e20_emptyCommitmentSigned]
  · unfold idsValid
    simp [channelId?, pubKeys, waveE_e20_emptyCommitmentSigned]
    exact ChannelId.zero_valid
  · unfold sigsValid
    simp [signatures, waveE_e20_emptyCommitmentSigned]

end LnLean.Proofs.WaveE.E20

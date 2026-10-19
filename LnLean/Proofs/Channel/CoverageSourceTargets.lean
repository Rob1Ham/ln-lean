/-
# Coverage sources for the missing `commitment_signed` data (`PR-02`)

BOLT 2's `commitment_signed` (type 132) carries a channel id, one commitment
signature, and one `HTLC_signature` per untrimmed HTLC output.  It carries no
commitment number, no digest, no fee, and no per-HTLC identification data, so
the legacy record cannot determine what it covers
(`LnLean.Proofs.ProtocolCoverageTargets.no_wire_determined_coverage`,
`no_coverage_htlc_selector`, and
`LnLean.Proofs.Channel.PreimageCoverageTargets.legacy_projection_not_determine_htlc_coverage`).

Wave 10 (`LnLean.Proofs.Channel.CoverageWitnessTargets`) characterized the
missing data as a per-HTLC `CoverageWitness`, supplied a constructive
`decodeCoverage : CommitmentSigned → CoverageWitness → Option …`, proved the
canonical witness exact, and proved that no legacy-only decoder or
wire-compatible witness selector is correct for every full record.  That
result still treated the witness as an untyped argument.

This module makes the **source/interface** explicit.  It defines three
coverage sources:

* `CoverageSource.fullRecord` — the signer's complete `CommitmentSignedFull`;
* `CoverageSource.outOfBand` — a witness supplied out of band, tagged with an
  explicit `WitnessOrigin` (local signer, persisted transcript, or untrusted
  peer);
* `CoverageSource.protocolExtension` — a `ProtocolExtension` carrying the
  minimum per-HTLC coverage fields.

`decodeSource` is the canonical decoder from a legacy wire record plus a source
to the covered `CommitmentHTLCOutput` list.  The three source-specific
correctness results are:

* `decodeSource_fullRecord_exact` — the full-record source is exact;
* `decodeSource_outOfBand_canonical` — the out-of-band source decodes the
  canonical witness exactly when `wireCompatible` holds;
* `decodeSource_extensionOfFull_canonical` — the canonical extension of a full
  record decodes exactly.

The negative source results are retained:

* `no_wire_determined_source` — no function from `CommitmentSigned` alone
  produces a source that decodes every full record correctly;
* `no_wire_source_selector` — no function from the wire recovers the source
  (even opaquely) for every full record;
* `wire_admits_distinct_out_of_band_witnesses` — the same wire is compatible
  with two out-of-band witnesses that decode differently;
* `wireCompatible_not_out_of_band_binding` — wire compatibility does not
  authenticate an out-of-band witness: the same entries with an untrusted
  origin are still wire-compatible but satisfy no binding law;
* `no_wire_witness_authenticator` — no wire-only Boolean authenticator is both
  complete for the canonical witness and sound for every full record.

`ProtocolExtension` is a *specification* of the smallest fields that would make
wire-plus-extension coverage determinate.  It is not a wire encoding, and this
module does **not** claim that BOLT 2 was changed.  `ExtensionBinds` is an
explicit field-by-field agreement law between an extension and a full record;
`extension_plus_wire_determines_coverage` is conditional on that law and on the
wire row-count check.  The extension model does not authenticate itself, does
not construct production scripts (it carries only a script-family tag), and no
production decoder is claimed.

Anchors: BOLT 2 §"Committing Updates So Far" (`commitment_signed`, type 132),
BOLT 2 §"Updating the Commitment" (`commitment_number` and revocation
ordering), BOLT 3 §"Commitment Transaction" / §"HTLC Outputs";
`LnLean/Protocol/Messages.lean` (`CommitmentSigned`, `SignedHtlcEntry`,
`CommitmentSignedFull`), `LnLean/Channel/Types.lean` (`CommitmentHTLCOutput`,
`Direction`, `HTLCState`), `LnLean/Proofs/ProtocolWireTargets.lean`,
`LnLean/Proofs/ProtocolCoverageTargets.lean`,
`LnLean/Proofs/Channel/PreimageCoverageTargets.lean`, and
`LnLean/Proofs/Channel/CoverageWitnessTargets.lean`.
-/

import LnLean.Proofs.Channel.CoverageWitnessTargets

namespace LnLean.Proofs.Channel.CoverageSourceTargets

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open LnLean
open LnLean.Channel
open LnLean.Protocol
open LnLean.Proofs
open LnLean.Proofs.Channel.CoverageWitnessTargets
open LnLean.Proofs.ProtocolCoverageTargets

/-! ## 1. The protocol-extension model

The extension is the smallest per-HTLC record that, together with the legacy
wire, determines the covered output list.  It carries the millisatoshi amount
(whose satoshi floor is the output value), the `cltv_expiry`, the payment hash
(the 32-byte hash image used to identify the HTLC and to select the offered or
received second-stage script), the direction relative to the commitment
holder, the lifecycle state, and a script-family tag.

The script tag is a *family* tag, not script bytes: this model has no BOLT 3
script encoder.  `offered`/`received` are the only two live commitment-output
families; terminal states no longer have a live commitment output. -/

/-- The BOLT 3 second-stage script family of a live HTLC output.  `offered` is
the `HTLC-success`-style family selected for an HTLC offered by the commitment
holder; `received` is the corresponding family for an HTLC received by the
holder.  The tag abstracts over the 143/136-byte script bytes. -/
inductive HtlcScriptTag where
  | offered
  | received
deriving Repr, DecidableEq, BEq

/-- The lifecycle state a live script family denotes. -/
def HtlcScriptTag.toState : HtlcScriptTag → HTLCState
  | .offered => .offered
  | .received => .received

/-- The script-family convention of a lifecycle state.  For the two live
states this is exact; terminal states (`fulfilled`, `failed`, `removed`) no
longer have a live commitment output, and the convention only keeps the
function total. -/
def HtlcScriptTag.ofState : HTLCState → HtlcScriptTag
  | .offered => .offered
  | .received => .received
  | .fulfilled => .received
  | .failed => .offered
  | .removed => .offered

@[simp] theorem HtlcScriptTag.ofState_offered :
    HtlcScriptTag.ofState .offered = .offered := rfl

@[simp] theorem HtlcScriptTag.ofState_received :
    HtlcScriptTag.ofState .received = .received := rfl

/-- Live states round-trip through the script-family convention. -/
theorem HtlcScriptTag.ofState_toState (t : HtlcScriptTag) :
    HtlcScriptTag.ofState t.toState = t := by
  cases t <;> rfl

/-- The per-HTLC coverage fields of a protocol extension.  These are exactly
the data the legacy `commitment_signed` omits: the millisatoshi amount, the
`cltv_expiry`, the payment hash image, the direction, the lifecycle state, and
the script-family tag.  There is deliberately no signature field: the legacy
wire already carries one signature per row, and `ExtensionBinds` never derives
a signature from the extension. -/
structure HtlcCoverageFields where
  /-- `amount_msat` of the HTLC; the commitment output carries its satoshi
  floor. -/
  amount : Msat
  /-- `cltv_expiry` of the HTLC output. -/
  cltvExpiry : Height
  /-- `payment_hash`, the hash image that identifies the HTLC.  It is not part
  of the covered output projection, but it is part of the HTLC identity and of
  the second-stage script selection. -/
  paymentHash : PaymentHash
  /-- Direction relative to the commitment holder. -/
  direction : Direction
  /-- Lifecycle state of the HTLC. -/
  htlcState : HTLCState
  /-- Script-family tag (`offered`/`received`). -/
  scriptTag : HtlcScriptTag
deriving Repr, BEq

namespace HtlcCoverageFields

/-- The commitment output these fields describe.  This is the same projection
as `SignedHtlcEntry.toCommitmentHtlcOutput`: BOLT 3 floors millisatoshis to
satoshis, and the output carries direction, floored amount, expiry, and
lifecycle state.  The payment hash and the script tag do not enter the
projection; the tag is bound separately by `RowBinds`. -/
def toCommitmentHtlcOutput (r : HtlcCoverageFields) : CommitmentHTLCOutput where
  direction := r.direction
  amountSat := r.amount.toSatFloor
  cltvExpiry := r.cltvExpiry
  state := r.htlcState

@[simp] theorem toCommitmentHtlcOutput_direction (r : HtlcCoverageFields) :
    r.toCommitmentHtlcOutput.direction = r.direction := rfl

@[simp] theorem toCommitmentHtlcOutput_amountSat (r : HtlcCoverageFields) :
    r.toCommitmentHtlcOutput.amountSat = r.amount.toSatFloor := rfl

@[simp] theorem toCommitmentHtlcOutput_cltvExpiry (r : HtlcCoverageFields) :
    r.toCommitmentHtlcOutput.cltvExpiry = r.cltvExpiry := rfl

@[simp] theorem toCommitmentHtlcOutput_state (r : HtlcCoverageFields) :
    r.toCommitmentHtlcOutput.state = r.htlcState := rfl

/-- The payment hash is not part of the covered output projection.  It remains
part of the HTLC identity and of the second-stage script inputs, so the
extension keeps it even though this theorem shows it is not load-bearing for
the output list alone. -/
theorem toCommitmentHtlcOutput_update_paymentHash
    (r : HtlcCoverageFields) (h : PaymentHash) :
    ({ r with paymentHash := h } : HtlcCoverageFields).toCommitmentHtlcOutput =
      r.toCommitmentHtlcOutput := rfl

/-- The script-family tag is not part of the covered output projection either.
It is bound to the full record by `RowBinds.tag_eq`; this separation is what
lets a tag mismatch be rejected without changing the decoded output list. -/
theorem toCommitmentHtlcOutput_update_scriptTag
    (r : HtlcCoverageFields) (t : HtlcScriptTag) :
    ({ r with scriptTag := t } : HtlcCoverageFields).toCommitmentHtlcOutput =
      r.toCommitmentHtlcOutput := rfl

/-- **Exact determining tuple of an extension row.**  Two extension rows
project to the same commitment output exactly when they agree on direction,
the floored satoshi amount, `cltv_expiry`, and lifecycle state.  The payment
hash and the script tag do not enter the output projection. -/
theorem toCommitmentHtlcOutput_eq_iff (r₁ r₂ : HtlcCoverageFields) :
    r₁.toCommitmentHtlcOutput = r₂.toCommitmentHtlcOutput ↔
      r₁.direction = r₂.direction ∧
        r₁.amount.toSatFloor = r₂.amount.toSatFloor ∧
          r₁.cltvExpiry = r₂.cltvExpiry ∧
            r₁.htlcState = r₂.htlcState := by
  constructor
  · intro h
    have h' : r₁.direction = r₂.direction ∧
        r₁.amount.toSatFloor = r₂.amount.toSatFloor ∧
          r₁.cltvExpiry = r₂.cltvExpiry ∧
            r₁.htlcState = r₂.htlcState ∧
              r₁.amount.toSatFloor = r₂.amount.toSatFloor := by
      simpa [HtlcCoverageFields.toCommitmentHtlcOutput,
        CommitmentHTLCOutput.mk.injEq] using h
    exact ⟨h'.1, h'.2.1, h'.2.2.1, h'.2.2.2.1⟩
  · rintro ⟨hd, ha, hc, hs⟩
    simp [HtlcCoverageFields.toCommitmentHtlcOutput, hd, ha, hc, hs]

end HtlcCoverageFields

/-- A protocol extension for one direction of one channel: the channel id and
the per-HTLC coverage rows in commitment order.  The legacy wire supplies the
signatures; the extension supplies the identification/amount rows. -/
structure ProtocolExtension where
  /-- Channel id the extension belongs to. -/
  channelId : ChannelId
  /-- Per-HTLC coverage rows, in commitment order. -/
  rows : List HtlcCoverageFields
deriving Repr, BEq

namespace ProtocolExtension

/-- The covered commitment-output list described by the extension. -/
def toCoverage (ext : ProtocolExtension) : List CommitmentHTLCOutput :=
  ext.rows.map HtlcCoverageFields.toCommitmentHtlcOutput

@[simp] theorem toCoverage_length (ext : ProtocolExtension) :
    ext.toCoverage.length = ext.rows.length := by
  simp [ProtocolExtension.toCoverage]

end ProtocolExtension

/-! ## 2. Field binding: extension plus full record

`RowBinds` is the explicit per-row agreement law.  It states that the
extension row has the same amount, expiry, payment hash, direction, and
lifecycle state as the signed entry, and that its script tag is the family
convention of that state.  `ExtensionBinds` lifts it to the whole list and also
binds the channel id.  Coverage equality is derived from these hypotheses, not
assumed. -/

/-- Field-by-field binding of one extension row to one signed entry. -/
structure RowBinds (r : HtlcCoverageFields) (e : SignedHtlcEntry) : Prop where
  /-- Same millisatoshi amount. -/
  amount_eq : r.amount = e.amount
  /-- Same `cltv_expiry`. -/
  cltv_eq : r.cltvExpiry = e.cltvExpiry
  /-- Same payment hash image. -/
  hash_eq : r.paymentHash = e.paymentHash
  /-- Same direction. -/
  direction_eq : r.direction = e.direction
  /-- Same lifecycle state. -/
  state_eq : r.htlcState = e.htlcState
  /-- The script tag is the family convention of the signed entry's state. -/
  tag_eq : r.scriptTag = HtlcScriptTag.ofState e.htlcState

/-- Two rows that satisfy `RowBinds` project to the same commitment output. -/
theorem RowBinds.output_eq {r : HtlcCoverageFields} {e : SignedHtlcEntry}
    (h : RowBinds r e) :
    r.toCommitmentHtlcOutput = e.toCommitmentHtlcOutput := by
  simp [HtlcCoverageFields.toCommitmentHtlcOutput,
    SignedHtlcEntry.toCommitmentHtlcOutput,
    h.amount_eq, h.cltv_eq, h.direction_eq, h.state_eq]

/-- Row-level binding, lifted to two lists in commitment order.  This is a
local inductive rather than `List.Forall₂` so that the generated inversion
lemmas are available in the pinned core. -/
inductive RowsBind : List HtlcCoverageFields → List SignedHtlcEntry → Prop where
  | nil : RowsBind [] []
  | cons {r : HtlcCoverageFields} {rs : List HtlcCoverageFields}
      {e : SignedHtlcEntry} {es : List SignedHtlcEntry} :
      RowBinds r e → RowsBind rs es → RowsBind (r :: rs) (e :: es)

namespace RowsBind

/-- Invert one cons cell. -/
theorem cons_inv {r : HtlcCoverageFields} {rs : List HtlcCoverageFields}
    {e : SignedHtlcEntry} {es : List SignedHtlcEntry}
    (h : RowsBind (r :: rs) (e :: es)) :
    RowBinds r e ∧ RowsBind rs es := by
  cases h with
  | cons hr ht => exact ⟨hr, ht⟩

/-- Bound lists have the same length. -/
theorem length_eq {rs : List HtlcCoverageFields}
    {es : List SignedHtlcEntry} (h : RowsBind rs es) :
    rs.length = es.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-- Bound rows have the same covered output list.  This is the field-binding
theorem: the conclusion is derived row by row from `RowBinds.output_eq`. -/
theorem coverage_eq {rs : List HtlcCoverageFields}
    {es : List SignedHtlcEntry} (h : RowsBind rs es) :
    rs.map HtlcCoverageFields.toCommitmentHtlcOutput =
      es.map SignedHtlcEntry.toCommitmentHtlcOutput := by
  induction h with
  | nil => rfl
  | cons hr _ ih => simp [RowBinds.output_eq hr, ih]

end RowsBind

/-- Whole-record binding of an extension to a full `commitment_signed` record:
same channel id and a row-by-row field agreement.  The legacy wire is not
mentioned: it is cross-checked separately by the row count. -/
structure ExtensionBinds (ext : ProtocolExtension)
    (f : CommitmentSignedFull) : Prop where
  /-- Same channel id. -/
  channelId_eq : ext.channelId = f.channelId
  /-- Row-by-row field binding. -/
  rows_bind : RowsBind ext.rows f.htlcEntries

namespace ExtensionBinds

/-- The bound channel id. -/
theorem channelId_agrees {ext : ProtocolExtension} {f : CommitmentSignedFull}
    (h : ExtensionBinds ext f) : ext.channelId = f.channelId :=
  h.channelId_eq

/-- The row count is the record's signed-entry count. -/
theorem rowCount {ext : ProtocolExtension} {f : CommitmentSignedFull}
    (h : ExtensionBinds ext f) :
    ext.rows.length = f.htlcEntries.length :=
  h.rows_bind.length_eq

/-- **Field binding determines coverage.**  Under `ExtensionBinds`, the
extension's covered output list is exactly the full record's coverage.  The
wire is not used; this is the extension-only half of the main conditional
theorem. -/
theorem coverage_eq {ext : ProtocolExtension} {f : CommitmentSignedFull}
    (h : ExtensionBinds ext f) :
    ext.toCoverage = coverageOfFull f := by
  unfold ProtocolExtension.toCoverage coverageOfFull
  exact RowsBind.coverage_eq h.rows_bind

end ExtensionBinds

/-! ## 3. Sources

A source is the extra object a decoder needs beyond the legacy record.  The
three constructors are deliberately distinct: a full signer record, an
out-of-band witness with an explicit provenance tag, and a protocol
extension.  The provenance tag is data, not a cryptographic authenticator; it
lets the model state that the wire does not bind the witness without also
claiming that a tag is a signature. -/

/-- Where an out-of-band witness came from.  `localSigner` and
`persistedTranscript` are the model's trusted origins; `untrustedPeer` is an
explicitly untrusted source.  This is an origin tag, not an authentication
proof. -/
inductive WitnessOrigin where
  | localSigner
  | persistedTranscript
  | untrustedPeer
deriving Repr, DecidableEq, BEq

/-- An out-of-band coverage witness: the per-HTLC rows plus their origin tag.
The entries are exactly a `CoverageWitness`; the tag is the explicit
provenance assertion the wire cannot carry. -/
structure OutOfBandWitness where
  /-- Per-HTLC signed rows, in commitment order. -/
  entries : List SignedHtlcEntry
  /-- Provenance tag of this witness. -/
  origin : WitnessOrigin
deriving Repr, BEq

namespace OutOfBandWitness

/-- Forget the provenance tag: the wave-10 `CoverageWitness`. -/
def toWitness (o : OutOfBandWitness) : CoverageWitness :=
  { entries := o.entries }

@[simp] theorem toWitness_entries (o : OutOfBandWitness) :
    o.toWitness.entries = o.entries := rfl

end OutOfBandWitness

/-- The trusted-origin predicate.  It is a model policy, not a proof of
authenticity; a caller that supplies `OutOfBandBinding` is supplying the
binding law explicitly. -/
def TrustedOrigin : WitnessOrigin → Prop
  | .localSigner => True
  | .persistedTranscript => True
  | .untrustedPeer => False

@[simp] theorem trustedOrigin_localSigner : TrustedOrigin .localSigner := trivial

@[simp] theorem trustedOrigin_persistedTranscript :
    TrustedOrigin .persistedTranscript := trivial

theorem not_trustedOrigin_untrustedPeer : ¬ TrustedOrigin .untrustedPeer :=
  fun h => h

/-- The explicit out-of-band binding law: the witness is wire-compatible with
the legacy message **and** carries a trusted origin.  This is the law whose
supply is required; wire compatibility alone does not imply it. -/
def OutOfBandBinding (m : CommitmentSigned) (o : OutOfBandWitness) : Prop :=
  wireCompatible m o.toWitness ∧ TrustedOrigin o.origin

/-- The binding law implies wire compatibility. -/
theorem outOfBandBinding_wireCompatible {m : CommitmentSigned}
    {o : OutOfBandWitness} (h : OutOfBandBinding m o) :
    wireCompatible m o.toWitness :=
  h.1

/-- The binding law implies a trusted origin. -/
theorem outOfBandBinding_trustedOrigin {m : CommitmentSigned}
    {o : OutOfBandWitness} (h : OutOfBandBinding m o) :
    TrustedOrigin o.origin :=
  h.2

/-- Supplying the two binding facts yields the binding law.  This is the
positive direction: authentication is an explicit input, not a wire
consequence. -/
theorem trusted_origin_binding {m : CommitmentSigned} {o : OutOfBandWitness}
    (hw : wireCompatible m o.toWitness) (ho : TrustedOrigin o.origin) :
    OutOfBandBinding m o :=
  ⟨hw, ho⟩

/-- Definitional characterization of the binding law. -/
theorem out_of_band_binding_iff {m : CommitmentSigned}
    {o : OutOfBandWitness} :
    OutOfBandBinding m o ↔
      wireCompatible m o.toWitness ∧ TrustedOrigin o.origin :=
  Iff.rfl

/-- The three coverage sources.  `fullRecord` is the signer's complete record;
`outOfBand` is a tagged witness; `protocolExtension` is the per-HTLC extension
specification.  The constructors are distinct, so source identity is not the
same thing as the wire record. -/
inductive CoverageSource where
  | fullRecord (record : CommitmentSignedFull)
  | outOfBand (witness : OutOfBandWitness)
  | protocolExtension (extension : ProtocolExtension)
deriving Repr, BEq

/-- The full-record source. -/
def fullSource (f : CommitmentSignedFull) : CoverageSource :=
  .fullRecord f

/-- The out-of-band source. -/
def outOfBandSource (o : OutOfBandWitness) : CoverageSource :=
  .outOfBand o

/-- The protocol-extension source. -/
def extensionSource (ext : ProtocolExtension) : CoverageSource :=
  .protocolExtension ext

@[simp] theorem fullSource_eq (f : CommitmentSignedFull) :
    fullSource f = .fullRecord f := rfl

@[simp] theorem outOfBandSource_eq (o : OutOfBandWitness) :
    outOfBandSource o = .outOfBand o := rfl

@[simp] theorem extensionSource_eq (ext : ProtocolExtension) :
    extensionSource ext = .protocolExtension ext := rfl

/-! ## 4. The canonical source decoder

`decodeSource` takes the legacy wire and a source.  The full-record and
out-of-band cases reuse the wave-10 `decodeCoverage` (which checks the
wire-signature count against the witness row count).  The extension case checks
the same count against the extension row count and then returns the extension's
coverage.  The wire never supplies identification data in any case. -/

/-- Decode the covered commitment outputs from a legacy `commitment_signed`
and a coverage source.  Returns `none` when the wire signature count does not
match the source row count. -/
def decodeSource (m : CommitmentSigned) :
    CoverageSource → Option (List CommitmentHTLCOutput)
  | .fullRecord f => decodeCoverage m (witnessOfFull f)
  | .outOfBand o => decodeCoverage m o.toWitness
  | .protocolExtension ext =>
      if m.htlcSignatures.length = ext.rows.length then
        some ext.toCoverage
      else
        none

/-- **The full-record source is exact.**  For every full record, decoding its
own source against its own legacy projection returns its exact coverage. -/
theorem decodeSource_fullRecord_exact (f : CommitmentSignedFull) :
    decodeSource f.toCommitmentSigned (.fullRecord f) = some (coverageOfFull f) :=
  decodeCoverage_canonical f

/-- The full-record case is exactly the wave-10 witness decoder. -/
theorem decodeSource_fullRecord_eq_decodeCoverage
    (m : CommitmentSigned) (f : CommitmentSignedFull) :
    decodeSource m (.fullRecord f) = decodeCoverage m (witnessOfFull f) := rfl

/-- **The out-of-band source decodes its canonical witness.**  For any origin
tag, the witness with the full record's entries decodes exactly.  The tag does
not affect the decode; it only affects `OutOfBandBinding`. -/
theorem decodeSource_outOfBand_canonical (f : CommitmentSignedFull)
    (origin : WitnessOrigin) :
    decodeSource f.toCommitmentSigned
        (.outOfBand { entries := f.htlcEntries, origin := origin }) =
      some (coverageOfFull f) :=
  decodeCoverage_canonical f

/-- A wire-compatible out-of-band witness always decodes to its own rows. -/
theorem decodeSource_outOfBand_of_wireCompatible
    {m : CommitmentSigned} {o : OutOfBandWitness}
    (h : wireCompatible m o.toWitness) :
    decodeSource m (.outOfBand o) =
      some (o.entries.map SignedHtlcEntry.toCommitmentHtlcOutput) :=
  decodeCoverage_of_wireCompatible h

/-- The out-of-band case is exactly the wave-10 witness decoder. -/
theorem decodeSource_outOfBand_eq_decodeCoverage
    (m : CommitmentSigned) (o : OutOfBandWitness) :
    decodeSource m (.outOfBand o) = decodeCoverage m o.toWitness := rfl

/-- The extension source decodes when the wire row count matches. -/
theorem decodeSource_protocolExtension
    {m : CommitmentSigned} {ext : ProtocolExtension}
    (h : m.htlcSignatures.length = ext.rows.length) :
    decodeSource m (.protocolExtension ext) = some ext.toCoverage := by
  unfold decodeSource
  simp [h]

/-- The extension source returns `none` when the wire row count differs. -/
theorem decodeSource_protocolExtension_none
    {m : CommitmentSigned} {ext : ProtocolExtension}
    (h : m.htlcSignatures.length ≠ ext.rows.length) :
    decodeSource m (.protocolExtension ext) = none := by
  unfold decodeSource
  simp [h]

/-- Exact characterization of the extension decoder: success is exactly the
wire row-count match, and the result is the extension's coverage. -/
theorem decodeSource_protocolExtension_eq_some_iff
    (m : CommitmentSigned) (ext : ProtocolExtension)
    (outs : List CommitmentHTLCOutput) :
    decodeSource m (.protocolExtension ext) = some outs ↔
      m.htlcSignatures.length = ext.rows.length ∧ outs = ext.toCoverage := by
  unfold decodeSource
  by_cases h : m.htlcSignatures.length = ext.rows.length
  · simp [h, eq_comm]
  · simp [h]

/-- **Source-decode soundness.**  Any successful source decode gives a wire
signature count equal to the decoded output count, hence covers a commitment
whose HTLC list is that output list. -/
theorem decodeSource_covers {m : CommitmentSigned} {src : CoverageSource}
    {outs : List CommitmentHTLCOutput} {c : Commitment}
    (h : decodeSource m src = some outs) (hc : c.htlcs = outs) :
    CoversHtlcOutputs m c := by
  unfold CoversHtlcOutputs
  rw [Commitment.htlcOutputCount_commitmentOutputs, hc]
  cases src with
  | fullRecord f => exact decodeCoverage_sound h
  | outOfBand o => exact decodeCoverage_sound h
  | protocolExtension ext =>
      obtain ⟨hlen, houts⟩ :=
        (decodeSource_protocolExtension_eq_some_iff m ext outs).1 h
      rw [houts, ProtocolExtension.toCoverage_length, hlen]

/-- **Extension plus legacy wire determines coverage.**  If the legacy wire
record is the projection of the full record, its HTLC-signature count matches
the extension row count, and the extension is field-bound to that full record,
then decoding the extension source returns the full record's exact coverage.

All three hypotheses are explicit.  The row-count check is the only condition
the legacy wire can contribute; the field binding is not derivable from the
wire (see `wireCompatible_not_out_of_band_binding` for the analogous
out-of-band separation). -/
theorem extension_plus_wire_determines_coverage
    {ext : ProtocolExtension} {m : CommitmentSigned}
    {f : CommitmentSignedFull}
    (hwire : m = f.toCommitmentSigned)
    (hlen : m.htlcSignatures.length = ext.rows.length)
    (hbind : ExtensionBinds ext f) :
    decodeSource m (.protocolExtension ext) = some (coverageOfFull f) := by
  subst m
  rw [decodeSource_protocolExtension hlen, hbind.coverage_eq]

/-- The coverage predicate implied by a successful extension decode. -/
theorem extension_plus_wire_covers
    {ext : ProtocolExtension} {m : CommitmentSigned}
    {f : CommitmentSignedFull} {c : Commitment}
    (hwire : m = f.toCommitmentSigned)
    (hlen : m.htlcSignatures.length = ext.rows.length)
    (hbind : ExtensionBinds ext f)
    (hc : c.htlcs = coverageOfFull f) :
    CoversHtlcOutputs m c := by
  have hdec := extension_plus_wire_determines_coverage hwire hlen hbind
  exact decodeSource_covers hdec hc

/-! ## 5. Canonical extension of a full record

The extension source is not vacuous: every full record has a canonical
extension whose rows are its signed entries' coverage fields.  This is the
generic realizable witness for the extension source, and it proves that the
extension model can express every full record without changing the wire. -/

/-- The extension row of a signed entry: keep the coverage fields and replace
the signature by the script-family tag. -/
def extensionRowOfEntry (e : SignedHtlcEntry) : HtlcCoverageFields where
  amount := e.amount
  cltvExpiry := e.cltvExpiry
  paymentHash := e.paymentHash
  direction := e.direction
  htlcState := e.htlcState
  scriptTag := HtlcScriptTag.ofState e.htlcState

/-- The canonical extension of a full record. -/
def extensionOfFull (f : CommitmentSignedFull) : ProtocolExtension where
  channelId := f.channelId
  rows := f.htlcEntries.map extensionRowOfEntry

/-- The canonical extension's rows are field-bound to the entry list. -/
theorem extensionOfFull_rows_bind (l : List SignedHtlcEntry) :
    RowsBind (l.map extensionRowOfEntry) l := by
  induction l with
  | nil => exact RowsBind.nil
  | cons e t ih =>
      exact RowsBind.cons (r := extensionRowOfEntry e) (e := e)
        ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ ih

/-- The canonical extension is field-bound to its full record. -/
theorem extensionOfFull_binds (f : CommitmentSignedFull) :
    ExtensionBinds (extensionOfFull f) f :=
  { channelId_eq := rfl
    rows_bind := extensionOfFull_rows_bind f.htlcEntries }

/-- The canonical extension's coverage is the full record's coverage. -/
theorem extensionOfFull_coverage (f : CommitmentSignedFull) :
    (extensionOfFull f).toCoverage = coverageOfFull f :=
  (extensionOfFull_binds f).coverage_eq

/-- **The extension source is exact on the canonical extension.**  For every
full record, the wire plus the canonical extension decodes to the exact
coverage.  This is the constructive non-vacuity theorem for the extension
source; it does not claim that the extension was received or negotiated. -/
theorem decodeSource_extensionOfFull_canonical (f : CommitmentSignedFull) :
    decodeSource f.toCommitmentSigned
        (.protocolExtension (extensionOfFull f)) =
      some (coverageOfFull f) := by
  apply extension_plus_wire_determines_coverage
    (m := f.toCommitmentSigned) (f := f) (ext := extensionOfFull f)
  · rfl
  · simp [extensionOfFull, CommitmentSignedFull.toCommitmentSigned]
  · exact extensionOfFull_binds f

/-! ## 6. Source separation

The wire is the same object for all sources, so source selection cannot be
recovered from it.  The first two theorems are the source-level restatements of
the wave-10 legacy-only negatives; the remaining theorems separate the
out-of-band binding law from the wire. -/

/-- **No wire-determined source.**  There is no function from the legacy
record alone that produces a source decoding every full record correctly.  The
two wave-10 counterexample records have the same wire projection and different
coverage, so any wire-selected source must decode the same wire to two
different output lists. -/
theorem no_wire_determined_source :
    ¬ ∃ src : CommitmentSigned → CoverageSource,
        ∀ f : CommitmentSignedFull,
          decodeSource f.toCommitmentSigned (src f.toCommitmentSigned) =
            some (coverageOfFull f) := by
  rintro ⟨src, hsrc⟩
  have hA := hsrc witnessFullA
  have hB := hsrc witnessFullB
  have hsame : src witnessFullA.toCommitmentSigned =
      src witnessFullB.toCommitmentSigned := by
    rw [witness_full_same_projection]
  rw [hsame] at hA
  have hcov : coverageOfFull witnessFullA = coverageOfFull witnessFullB :=
    Option.some.inj (hA.symm.trans hB)
  exact witness_full_coverage_ne hcov

/-- **No wire source selector.**  Even an opaque source choice cannot be
recovered from the wire: a selector that always returns the canonical
full-record source would have to return the same source for the two
counterexample records, which are distinct. -/
theorem no_wire_source_selector :
    ¬ ∃ src : CommitmentSigned → CoverageSource,
        ∀ f : CommitmentSignedFull,
          src f.toCommitmentSigned = .fullRecord f := by
  rintro ⟨src, hsrc⟩
  have hA := hsrc witnessFullA
  have hB := hsrc witnessFullB
  have hsame : src witnessFullA.toCommitmentSigned =
      src witnessFullB.toCommitmentSigned := by
    rw [witness_full_same_projection]
  rw [hA] at hsame
  rw [hB] at hsame
  injection hsame with hAB
  exact witness_full_coverage_ne (congrArg coverageOfFull hAB)

/-- The legacy wire admits two out-of-band witnesses with different coverage.
Both are wire-compatible with the same `commitment_signed` and have trusted
origins, yet they decode differently.  The wire cannot select between them; a
source must be supplied. -/
theorem wire_admits_distinct_out_of_band_witnesses :
    ∃ (m : CommitmentSigned) (o₁ o₂ : OutOfBandWitness),
      wireCompatible m o₁.toWitness ∧
        wireCompatible m o₂.toWitness ∧
        o₁.toWitness ≠ o₂.toWitness ∧
        decodeSource m (.outOfBand o₁) ≠ decodeSource m (.outOfBand o₂) := by
  let o₁ : OutOfBandWitness :=
    { entries := (witnessOfFull witnessFullA).entries, origin := .localSigner }
  let o₂ : OutOfBandWitness :=
    { entries := (witnessOfFull witnessFullB).entries, origin := .localSigner }
  refine ⟨witnessFullA.toCommitmentSigned, o₁, o₂, ?_, ?_, ?_, ?_⟩
  · exact wireCompatible_toCommitmentSigned witnessFullA
  · rw [witness_full_same_projection]
    exact wireCompatible_toCommitmentSigned witnessFullB
  · intro h
    have hentries : (witnessOfFull witnessFullA).entries =
        (witnessOfFull witnessFullB).entries := by
      have := congrArg CoverageWitness.entries h
      simpa [o₁, o₂, OutOfBandWitness.toWitness] using this
    have hentries' : witnessFullA.htlcEntries = witnessFullB.htlcEntries := by
      simpa [witnessOfFull] using hentries
    have hcov : coverageOfFull witnessFullA = coverageOfFull witnessFullB := by
      simp [coverageOfFull, hentries']
    exact witness_full_coverage_ne hcov
  · have hA : decodeSource witnessFullA.toCommitmentSigned (.outOfBand o₁) =
        some (coverageOfFull witnessFullA) := by
      simpa [o₁, OutOfBandWitness.toWitness, coverageOfFull] using
        (decodeSource_outOfBand_of_wireCompatible
          (m := witnessFullA.toCommitmentSigned)
          (o := o₁) (wireCompatible_toCommitmentSigned witnessFullA))
    have hB : decodeSource witnessFullA.toCommitmentSigned (.outOfBand o₂) =
        some (coverageOfFull witnessFullB) := by
      have hw : wireCompatible witnessFullA.toCommitmentSigned o₂.toWitness := by
        rw [witness_full_same_projection]
        exact wireCompatible_toCommitmentSigned witnessFullB
      simpa [o₂, OutOfBandWitness.toWitness, coverageOfFull] using
        (decodeSource_outOfBand_of_wireCompatible
          (m := witnessFullA.toCommitmentSigned) (o := o₂) hw)
    rw [hA, hB]
    intro h
    exact witness_full_coverage_ne (Option.some.inj h)

/-- The origin tag does not change the decode: the wire and the entry list are
the only inputs to the out-of-band decoder.  Authentication is orthogonal to
coverage, which is exactly why the binding law must be supplied separately. -/
theorem out_of_band_origin_irrelevant_to_decode
    (m : CommitmentSigned) (entries : List SignedHtlcEntry)
    (o₁ o₂ : WitnessOrigin) :
    decodeSource m (.outOfBand ⟨entries, o₁⟩) =
      decodeSource m (.outOfBand ⟨entries, o₂⟩) := rfl

/-- **Wire compatibility does not authenticate an out-of-band witness.**  The
same wire-compatible entries with an `untrustedPeer` origin satisfy no binding
law.  This is the precise separation: the wire checks the signature count, but
the provenance assertion is an explicit extra hypothesis. -/
theorem wireCompatible_not_out_of_band_binding :
    ∃ (m : CommitmentSigned) (o : OutOfBandWitness),
      wireCompatible m o.toWitness ∧ ¬ OutOfBandBinding m o := by
  refine ⟨witnessFullA.toCommitmentSigned,
    { entries := (witnessOfFull witnessFullA).entries,
      origin := .untrustedPeer }, ?_, ?_⟩
  · exact wireCompatible_toCommitmentSigned witnessFullA
  · intro h
    exact h.2

/-- **No wire-only witness authenticator.**  There is no Boolean function from
the legacy wire and a candidate witness that is both complete for the canonical
witness of every full record and sound for every candidate it accepts.  The
counterexample records project to the same wire, so an authenticator must
accept the same candidate in both worlds, forcing two different coverages. -/
theorem no_wire_witness_authenticator :
    ¬ ∃ auth : CommitmentSigned → CoverageWitness → Bool,
        ∀ f : CommitmentSignedFull,
          auth f.toCommitmentSigned (witnessOfFull f) = true ∧
            ∀ w : CoverageWitness,
              auth f.toCommitmentSigned w = true →
                decodeCoverage f.toCommitmentSigned w =
                  some (coverageOfFull f) := by
  rintro ⟨auth, hauth⟩
  have hA := hauth witnessFullA
  have hB := hauth witnessFullB
  have hsame : auth witnessFullA.toCommitmentSigned =
      auth witnessFullB.toCommitmentSigned := by
    rw [witness_full_same_projection]
  have htrueA :
      auth witnessFullA.toCommitmentSigned
        (witnessOfFull witnessFullA) = true := hA.1
  have htrueB :
      auth witnessFullB.toCommitmentSigned
        (witnessOfFull witnessFullA) = true := by
    rw [← hsame]
    exact htrueA
  have hdecA := hA.2 (witnessOfFull witnessFullA) htrueA
  have hdecB := hB.2 (witnessOfFull witnessFullA) htrueB
  rw [← witness_full_same_projection] at hdecB
  have hcov : coverageOfFull witnessFullA = coverageOfFull witnessFullB :=
    Option.some.inj (hdecA.symm.trans hdecB)
  exact witness_full_coverage_ne hcov

/-! ## 7. Non-vacuity: realizable extension and accepted decode -/

/-- The extension row of the concrete first counterexample entry. -/
def exampleRow : HtlcCoverageFields :=
  extensionRowOfEntry witnessEntryA

/-- The canonical extension of `witnessFullA`. -/
def exampleExtension : ProtocolExtension :=
  extensionOfFull witnessFullA

/-- The concrete extension is field-bound to the concrete full record. -/
theorem exampleExtension_binds_fullA : ExtensionBinds exampleExtension witnessFullA :=
  extensionOfFull_binds witnessFullA

/-- Its coverage is exactly the full record's coverage. -/
theorem exampleExtension_coverage :
    exampleExtension.toCoverage = coverageOfFull witnessFullA :=
  extensionOfFull_coverage witnessFullA

/-- The concrete extension decodes successfully against the concrete wire. -/
theorem exampleExtension_decodes :
    decodeSource witnessFullA.toCommitmentSigned
        (.protocolExtension exampleExtension) =
      some (coverageOfFull witnessFullA) :=
  decodeSource_extensionOfFull_canonical witnessFullA

/-- **Realizable non-vacuity.**  The concrete extension binds the concrete full
record, has nonempty coverage, and decodes successfully.  No hypothesis is
assumed: this is a closed instance. -/
theorem exampleExtension_nonvacuous :
    ExtensionBinds exampleExtension witnessFullA ∧
      exampleExtension.toCoverage ≠ [] ∧
        decodeSource witnessFullA.toCommitmentSigned
            (.protocolExtension exampleExtension) =
          some (coverageOfFull witnessFullA) := by
  refine ⟨exampleExtension_binds_fullA, ?_, exampleExtension_decodes⟩
  simp [exampleExtension, extensionOfFull, ProtocolExtension.toCoverage,
    witnessFullA]

/-- The concrete extension has exactly one row, matching the one wire
`HTLC_signature`. -/
theorem exampleExtension_rowCount :
    exampleExtension.rows.length =
      witnessFullA.toCommitmentSigned.htlcSignatures.length := by
  simp [exampleExtension, extensionOfFull, witnessFullA,
    CommitmentSignedFull.toCommitmentSigned]

/-! ## 8. Rejected cases and field necessity

The extension binding is not automatic.  A row with the right shape but the
wrong amount or script tag is rejected; a wire with the wrong signature count
is rejected by the decoder.  The necessity theorems show which fields are
load-bearing for the output list and which are bound separately. -/

/-- The example row with the amount changed from 1000 msat to 2000 msat. -/
def mismatchedAmountRow : HtlcCoverageFields :=
  { exampleRow with amount := ⟨2000⟩ }

/-- The corresponding full extension. -/
def mismatchedAmountExtension : ProtocolExtension :=
  { exampleExtension with rows := [mismatchedAmountRow] }

/-- A wrong amount is rejected by the binding law. -/
theorem mismatchedAmountExtension_not_binds :
    ¬ ExtensionBinds mismatchedAmountExtension witnessFullA := by
  intro h
  have hb : RowsBind [mismatchedAmountRow] [witnessEntryA] := by
    simpa [mismatchedAmountExtension, exampleExtension, extensionOfFull,
      witnessFullA] using h.rows_bind
  have hrow : RowBinds mismatchedAmountRow witnessEntryA :=
    (RowsBind.cons_inv hb).1
  have hval : (2000 : Nat) = 1000 := by
    simpa [mismatchedAmountRow, exampleRow, extensionRowOfEntry, witnessEntryA]
      using congrArg Msat.val hrow.amount_eq
  omega

/-- The rejected extension's coverage still differs from the record's, so the
rejection is substantive, not merely a bookkeeping failure. -/
theorem mismatchedAmountExtension_coverage_ne :
    mismatchedAmountExtension.toCoverage ≠ coverageOfFull witnessFullA := by
  intro h
  have hamount := congrArg
    (fun l : List CommitmentHTLCOutput => l.map (fun o => o.amountSat)) h
  simp [mismatchedAmountExtension, exampleExtension, extensionOfFull,
    mismatchedAmountRow, exampleRow, extensionRowOfEntry, witnessFullA,
    witnessEntryA, ProtocolExtension.toCoverage,
    HtlcCoverageFields.toCommitmentHtlcOutput, coverageOfFull,
    SignedHtlcEntry.toCommitmentHtlcOutput, Msat.toSatFloor,
    Msat.MSAT_PER_SAT] at hamount

/-- The example row with the script-family tag changed. -/
def mismatchedTagRow : HtlcCoverageFields :=
  { exampleRow with scriptTag := .received }

/-- The corresponding full extension. -/
def mismatchedTagExtension : ProtocolExtension :=
  { exampleExtension with rows := [mismatchedTagRow] }

/-- A wrong script-family tag is rejected by the binding law even though the
covered output projection is unchanged. -/
theorem mismatchedTagExtension_not_binds :
    ¬ ExtensionBinds mismatchedTagExtension witnessFullA := by
  intro h
  have hb : RowsBind [mismatchedTagRow] [witnessEntryA] := by
    simpa [mismatchedTagExtension, exampleExtension, extensionOfFull,
      witnessFullA] using h.rows_bind
  have hrow : RowBinds mismatchedTagRow witnessEntryA :=
    (RowsBind.cons_inv hb).1
  have htag := hrow.tag_eq
  simp [mismatchedTagRow, exampleRow, extensionRowOfEntry, witnessEntryA,
    HtlcScriptTag.ofState] at htag

/-- The tag-mismatched extension still has the same coverage as the correct
extension: the tag is not part of the output projection.  This is why the
binding law must mention it explicitly. -/
theorem mismatchedTagExtension_coverage_eq :
    mismatchedTagExtension.toCoverage = coverageOfFull witnessFullA := by
  rw [show mismatchedTagExtension.toCoverage = exampleExtension.toCoverage from rfl,
    exampleExtension_coverage]

/-- A concrete legacy wire with no HTLC signatures. -/
def emptyWire : CommitmentSigned where
  channelId := ChannelId.zero
  signature := ⟨ByteArray.empty⟩
  htlcSignatures := []

/-- A one-row extension cannot decode against a zero-signature wire. -/
theorem emptyWire_rejects_extension :
    decodeSource emptyWire (.protocolExtension exampleExtension) = none := by
  unfold decodeSource
  simp [emptyWire, exampleExtension, extensionOfFull, witnessFullA]

/-- **The amount field is necessary for extension coverage.**  Two rows can
agree on expiry, payment hash, direction, state, and script tag while projecting
to different outputs.  The amount is therefore load-bearing, and dropping its
binding equation would make `ExtensionBinds` insufficient. -/
theorem extension_amount_binding_necessary :
    ∃ r₁ r₂ : HtlcCoverageFields,
      r₁.cltvExpiry = r₂.cltvExpiry ∧
        r₁.paymentHash = r₂.paymentHash ∧
          r₁.direction = r₂.direction ∧
            r₁.htlcState = r₂.htlcState ∧
              r₁.scriptTag = r₂.scriptTag ∧
                r₁.toCommitmentHtlcOutput ≠ r₂.toCommitmentHtlcOutput := by
  refine ⟨exampleRow, mismatchedAmountRow, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro h
  have hamount := congrArg
    (fun o : CommitmentHTLCOutput => o.amountSat) h
  simp [exampleRow, mismatchedAmountRow, extensionRowOfEntry, witnessEntryA,
    HtlcCoverageFields.toCommitmentHtlcOutput, Msat.toSatFloor,
    Msat.MSAT_PER_SAT] at hamount

/-- The example row with `cltv_expiry` changed from 100 to 101. -/
def mismatchedCltvRow : HtlcCoverageFields :=
  { exampleRow with cltvExpiry := 101 }

/-- **The `cltv_expiry` field is necessary for extension coverage.** -/
theorem extension_cltv_binding_necessary :
    ∃ r₁ r₂ : HtlcCoverageFields,
      r₁.amount = r₂.amount ∧
        r₁.paymentHash = r₂.paymentHash ∧
          r₁.direction = r₂.direction ∧
            r₁.htlcState = r₂.htlcState ∧
              r₁.scriptTag = r₂.scriptTag ∧
                r₁.toCommitmentHtlcOutput ≠ r₂.toCommitmentHtlcOutput := by
  refine ⟨exampleRow, mismatchedCltvRow, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro h
  have hcltv := congrArg
    (fun o : CommitmentHTLCOutput => o.cltvExpiry) h
  simp [exampleRow, mismatchedCltvRow, extensionRowOfEntry, witnessEntryA,
    HtlcCoverageFields.toCommitmentHtlcOutput] at hcltv

/-- The example row with the direction changed. -/
def mismatchedDirectionRow : HtlcCoverageFields :=
  { exampleRow with direction := .remote }

/-- **The direction field is necessary for extension coverage.** -/
theorem extension_direction_binding_necessary :
    ∃ r₁ r₂ : HtlcCoverageFields,
      r₁.amount = r₂.amount ∧
        r₁.cltvExpiry = r₂.cltvExpiry ∧
          r₁.paymentHash = r₂.paymentHash ∧
            r₁.htlcState = r₂.htlcState ∧
              r₁.scriptTag = r₂.scriptTag ∧
                r₁.toCommitmentHtlcOutput ≠ r₂.toCommitmentHtlcOutput := by
  refine ⟨exampleRow, mismatchedDirectionRow, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro h
  have hdir := congrArg
    (fun o : CommitmentHTLCOutput => o.direction) h
  simp [exampleRow, mismatchedDirectionRow, extensionRowOfEntry, witnessEntryA,
    HtlcCoverageFields.toCommitmentHtlcOutput] at hdir

/-- **The payment hash is bound but not part of the output projection.**  A row
with a different payment hash has the same covered output; the hash remains
part of `RowBinds` because it identifies the HTLC and selects the second-stage
script, not because the output list contains it. -/
theorem paymentHash_binding_separate_from_coverage
    (r : HtlcCoverageFields) (h : PaymentHash) :
    ({ r with paymentHash := h } : HtlcCoverageFields).toCommitmentHtlcOutput =
      r.toCommitmentHtlcOutput :=
  HtlcCoverageFields.toCommitmentHtlcOutput_update_paymentHash r h

/-- **The script tag is bound but not part of the output projection.** -/
theorem scriptTag_binding_separate_from_coverage
    (r : HtlcCoverageFields) (t : HtlcScriptTag) :
    ({ r with scriptTag := t } : HtlcCoverageFields).toCommitmentHtlcOutput =
      r.toCommitmentHtlcOutput :=
  HtlcCoverageFields.toCommitmentHtlcOutput_update_scriptTag r t

/-! ## 9. Summary -/

/-- Bundled faithful reading of the source/interface lane.

1. The full-record source is exact for every full record.
2. The extension plus the legacy wire determines coverage under the explicit
   `ExtensionBinds` field law and the wire row-count check.
3. The extension source is realizable: every full record has a canonical
   extension, and the concrete one-row example decodes successfully.
4. No function from the legacy wire alone produces a correct source, and no
   wire function recovers the source opaquely.
5. The same wire admits distinct out-of-band witnesses with different
   coverage.
6. Wire compatibility alone does not authenticate an out-of-band witness; a
   trusted origin (or another explicit binding law) is required.

The conditions in (2) are hypotheses, not theorems about a received message.
No production decoder, wire encoding change, or protocol modification is
claimed. -/
theorem coverage_source_summary :
    (∀ f : CommitmentSignedFull,
        decodeSource f.toCommitmentSigned (.fullRecord f) =
          some (coverageOfFull f)) ∧
      (∀ (ext : ProtocolExtension) (m : CommitmentSigned)
          (f : CommitmentSignedFull),
          m = f.toCommitmentSigned →
            m.htlcSignatures.length = ext.rows.length →
              ExtensionBinds ext f →
                decodeSource m (.protocolExtension ext) =
                  some (coverageOfFull f)) ∧
      (ExtensionBinds exampleExtension witnessFullA ∧
        exampleExtension.toCoverage ≠ []) ∧
      (¬ ∃ src : CommitmentSigned → CoverageSource,
        ∀ f : CommitmentSignedFull,
          decodeSource f.toCommitmentSigned (src f.toCommitmentSigned) =
            some (coverageOfFull f)) ∧
      (¬ ∃ src : CommitmentSigned → CoverageSource,
        ∀ f : CommitmentSignedFull,
          src f.toCommitmentSigned = .fullRecord f) ∧
      (∃ (m : CommitmentSigned) (o₁ o₂ : OutOfBandWitness),
        wireCompatible m o₁.toWitness ∧
          wireCompatible m o₂.toWitness ∧
          o₁.toWitness ≠ o₂.toWitness ∧
          decodeSource m (.outOfBand o₁) ≠ decodeSource m (.outOfBand o₂)) ∧
      (∃ (m : CommitmentSigned) (o : OutOfBandWitness),
        wireCompatible m o.toWitness ∧ ¬ OutOfBandBinding m o) :=
  ⟨decodeSource_fullRecord_exact,
    fun _ext _m _f hwire hlen hbind =>
      extension_plus_wire_determines_coverage hwire hlen hbind,
    ⟨exampleExtension_binds_fullA, exampleExtension_nonvacuous.2.1⟩,
    no_wire_determined_source,
    no_wire_source_selector,
    wire_admits_distinct_out_of_band_witnesses,
    wireCompatible_not_out_of_band_binding⟩

end LnLean.Proofs.Channel.CoverageSourceTargets

import Bitcoin.Data.Basic
import Bitcoin.Data.Script
import Bitcoin.Data.Tx
import LnLean.Basic.Core
import LnLean.Bitcoin.Seam
import LnLean.Bitcoin.Funding
import LnLean.Bitcoin.Laws

/-!
# LnLean.Proofs.Bitcoin.AnchorProps

English claim.  For the anchor variant of a BOLT 3 commitment transaction:
each anchor output carries exactly 330 satoshis, and a zero-HTLC commitment
with both commitment outputs present carries exactly two anchors (at most two
in every template in this model); the two anchors occur exactly when the
anchor feature is negotiated; the anchor output script is the model's
version-0 P2WSH template over
`<funding_pubkey> OP_CHECKSIG OP_IFDUP OP_NOTIF OP_16 OP_CSV OP_ENDIF`; an
anchor script is spendable only with the funding key committed to by that
script, and the local/remote anchors are committed to the local/remote
funding keys respectively; the anchor value is not an input to the fee
calculation, though anchor presence adds a fixed 400 weight units; and the
anchor value enters value conservation as a separate deduction of 660 sat,
not as part of the fee.

The last point corrects the brief's literal phrasing.  In this model (and in
BOLT 3) anchors change the `to_local`/`to_remote` conservation equation in
*two* ways: (i) the anchor outputs are themselves outputs, so the funder pays
`2 * 330` sat in addition to the fee, and (ii) the extra 400 weight units
raise the fee computed from the negotiated feerate.  The theorem
`conservation_effective_deduction` states the corrected equation
`to_local + to_remote = funding - (fee + 2 * 330)`.

BOLT sections (pinned BOLT commit `1aadb719b4007c4cea0ba6e36b08c4fb53788dee`).
* BOLT 3, "`to_local_anchor` and `to_remote_anchor` Output" at
  `refs/bolts/03-transactions.md:148-177`: the witness script template
  (`:155-159`), the fixed 330-sat amount (`:168`), the funding-key lock, and
  the 16-block anyone-sweep rule (`:174-177`).
* BOLT 3, requirements `refs/bolts/03-transactions.md:320-326`: both anchor
  values MUST be subtracted from the funder's output.
* BOLT 3, expected weights `refs/bolts/03-transactions.md:489-497`:
  724 (no anchors) and 1124 (anchors) plus 172 per untrimmed HTLC.
* BOLT 3, construction algorithm `refs/bolts/03-transactions.md:708-736`,
  anchors at `:730-731`.
* BOLT 9, feature bit `22/23 option_anchors`, `refs/bolts/09-features.md:45`.

rust-lightning anchors at commit
`fe4900930c6bd5786ec4203274d7cf312776a5a6`.
* `refs/rust-lightning/lightning/src/ln/chan_utils.rs:1009-1017`
  (`get_to_countersigner_keyed_anchor_redeemscript`: the one-block-CSV
  `to_remote` witness script when anchors are negotiated).
* `refs/rust-lightning/lightning/src/ln/chan_utils.rs:1032-1042`
  (`get_keyed_anchor_redeemscript`: the exact anchor witness-script template).
* `refs/rust-lightning/lightning/src/ln/chan_utils.rs:1044-1054`
  (`build_keyed_anchor_input_witness`: the funding-key signature witness).
* `refs/rust-lightning/lightning/src/ln/chan_utils.rs:1926-1942`
  (`insert_non_htlc_outputs`: both 330-sat anchors, keyed by the respective
  funding keys, present when the output exists or an HTLC output exists).
* `refs/rust-lightning/lightning/src/ln/channel.rs:989`
  (`ANCHOR_OUTPUT_VALUE_SATOSHI: u64 = 330`).

What is explicitly NOT modelled.
* L1 script execution / BIP 143 signature checking.  Spendability is stated
  over an abstract `AnchorSpendModel`; its `sound` field is the missing
  interpreter bridge.  The 16-block CSV anyone-sweep path is not proved.
* SHA256 and collision resistance.  `CommitmentParams.HashesMatch` is taken
  as a hypothesis, so the link from a witness script to its P2WSH program is
  assumed, not computed.  The byte-level key-injectivity lemma is left as
  `LN-ANCHOR-007`.
* The BOLT 3 no-HTLC dust exception in which only one anchor is emitted when
  one commitment output is below the dust limit.  `commitmentOutputs` is the
  both-outputs-present template, so this module proves two anchors for that
  template, not for every possible commitment.
* `shared_anchor` / zero-fee commitments (`option_zero_fee_commitments`,
  P2A), BIP 69+CLTV output ordering, and CPFP fee-bump economics (BOLT 5).
* The wire encoding of feature bits 22/23; the gate is a `Bool` parameter
  matching `ChannelParams.anchorOutputs` in `LnLean.Channel.Types`.
-/

namespace LnLean.Bitcoin

set_option autoImplicit false

open Bitcoin.Data

/-! ## The anchor feature gate -/

/-- The `option_anchors` gate (BOLT 9 bits 22/23) as a Boolean parameter.
The wave-A Bitcoin layer carries no feature vector; a `true` value is the
`ChannelParams.anchorOutputs` flag that selects the anchor commitment
variant. -/
def anchorsNegotiated (anchors : Bool) : Prop := anchors = true

/-- The output kinds of a zero-HTLC commitment, as a function of the anchor
feature.  Without anchors only `to_local` and `to_remote` are present; with
anchors the two keyed anchor kinds are appended.  Ordering is template order,
not BIP 69+CLTV order. -/
def commitmentOutputKinds (anchors : Bool) : List OutputKind :=
  [.toLocal, .toRemote] ++
    (if anchors then [.localAnchor, .remoteAnchor] else [])

/-- Both anchor kinds occur in a kind list. -/
def hasBothAnchors (l : List OutputKind) : Prop :=
  OutputKind.localAnchor ∈ l ∧ OutputKind.remoteAnchor ∈ l

/-- **Anchors are present exactly when the feature is negotiated.**  This is
the feature-gate law for the zero-HTLC commitment template. -/
theorem anchors_present_iff_negotiated (anchors : Bool) :
    hasBothAnchors (commitmentOutputKinds anchors) ↔ anchors = true := by
  cases anchors
  · simp [hasBothAnchors, commitmentOutputKinds]
  · simp [hasBothAnchors, commitmentOutputKinds]

/-- The same gate, phrased with the named `anchorsNegotiated` predicate. -/
theorem anchors_present_iff_feature (anchors : Bool) :
    hasBothAnchors (commitmentOutputKinds anchors) ↔ anchorsNegotiated anchors :=
  anchors_present_iff_negotiated anchors

/-- The concrete zero-HTLC output list is the anchor-enabled template. -/
theorem commitmentOutputs_kinds_template (p : CommitmentParams) :
    (commitmentOutputs p).map CommitmentOutput.kind = commitmentOutputKinds true := by
  simpa [commitmentOutputKinds] using commitmentOutputs_kinds_law p

/-- The concrete zero-HTLC commitment therefore contains both anchors. -/
theorem commitmentOutputs_has_both_anchors (p : CommitmentParams) :
    hasBothAnchors ((commitmentOutputs p).map CommitmentOutput.kind) := by
  rw [commitmentOutputs_kinds_template]
  exact (anchors_present_iff_negotiated true).2 rfl

/-! ## Counting anchors -/

/-- Recognise the two anchor kinds without relying on `BEq`. -/
def isAnchorKind : OutputKind → Bool
  | .localAnchor => true
  | .remoteAnchor => true
  | _ => false

/-- Number of anchor outputs in a commitment output list. -/
def anchorCount (l : List CommitmentOutput) : Nat :=
  (l.filter (fun o => isAnchorKind o.kind)).length

/-- Number of anchor kinds in a kind list. -/
def anchorKindCount (l : List OutputKind) : Nat :=
  (l.filter isAnchorKind).length

/-- The feature-dependent template has zero anchors without the feature and
exactly two with it. -/
theorem commitmentOutputKinds_anchorCount (anchors : Bool) :
    anchorKindCount (commitmentOutputKinds anchors) =
      (if anchors then 2 else 0) := by
  cases anchors
  · rfl
  · rfl

/-- **The zero-HTLC anchor commitment has exactly two anchor outputs.** -/
theorem commitmentOutputs_anchorCount (p : CommitmentParams) :
    anchorCount (commitmentOutputs p) = 2 := by
  simp [anchorCount, commitmentOutputs, isAnchorKind]

/-- **At most two anchor outputs.**  Immediate from the exact count; this is
the form used by conservation and by weight accounting. -/
theorem commitmentOutputs_anchorCount_le_two (p : CommitmentParams) :
    anchorCount (commitmentOutputs p) ≤ 2 := by
  rw [commitmentOutputs_anchorCount p]
  omega

/-- Every anchor output in the concrete zero-HTLC list carries exactly
`anchorValue` (330 sat).  A record merely *tagged* as an anchor may carry any
value; membership in the generated list is what fixes it. -/
theorem commitmentOutputs_anchor_value (p : CommitmentParams)
    (o : CommitmentOutput) (hmem : o ∈ commitmentOutputs p)
    (hk : o.kind = .localAnchor ∨ o.kind = .remoteAnchor) :
    o.value = anchorValue := by
  simp only [commitmentOutputs, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl
  · rcases hk with h | h <;> cases h
  · rcases hk with h | h <;> cases h
  · rfl
  · rfl

/-- The total value of the anchor outputs in the zero-HTLC commitment is
`2 * 330 = 660` satoshis. -/
theorem commitmentOutputs_anchor_value_total (p : CommitmentParams) :
    (((commitmentOutputs p).filter (fun o => isAnchorKind o.kind)).map
      CommitmentOutput.value).sum = 2 * anchorValue := by
  simp [commitmentOutputs, isAnchorKind, anchorValue]

/-- The model's anchor value is 330 satoshis. -/
theorem anchor_value_is_330 : anchorValue = 330 := rfl

/-! ## The anchor script template -/

/-- The anchor `scriptPubKey` is exactly the version-0 P2WSH template over the
supplied 32-byte witness-program. -/
theorem anchor_script_is_v0_p2wsh (program : ByteArray) :
    anchorScriptPubKey program = p2wsh program := rfl

/-- The anchor `scriptPubKey` is 34 bytes for a 32-byte program (BIP 141). -/
theorem anchor_script_size (program : ByteArray) (h : program.size = 32) :
    (anchorScriptPubKey program).bytes.size = 34 :=
  anchorScriptPubKey_size program h

/-- The anchor witness script is 40 bytes for a valid compressed funding key:
34 bytes of push data plus six one-byte opcodes. -/
theorem anchor_witness_script_size_40 (fundingKey : PubKey)
    (h : fundingKey.bytes.size = 33) :
    (anchorWitnessScript fundingKey).bytes.size = 40 :=
  anchorWitnessScript_size fundingKey h

/-- The local anchor output commits, through its P2WSH program, to the anchor
witness script built from the *local* funding key.  This uses the
`HashesMatch` hypothesis because SHA256 is outside this module. -/
theorem localAnchor_script_commits_local_funding_key
    (p : CommitmentParams) (sha256 : Script → ByteArray)
    (h : p.HashesMatch sha256) :
    ∃ o : CommitmentOutput,
      o ∈ commitmentOutputs p ∧
      o.kind = .localAnchor ∧
      o.scriptPubKey = p2wsh (sha256 (anchorWitnessScript p.localFundingKey)) := by
  refine ⟨⟨.localAnchor, anchorValue,
      anchorScriptPubKey p.localAnchorWitnessScriptHash⟩, ?_, rfl, ?_⟩
  · simp [commitmentOutputs]
  · simp [anchorScriptPubKey, h.2.2.1]

/-- The analogous statement for the remote anchor and remote funding key. -/
theorem remoteAnchor_script_commits_remote_funding_key
    (p : CommitmentParams) (sha256 : Script → ByteArray)
    (h : p.HashesMatch sha256) :
    ∃ o : CommitmentOutput,
      o ∈ commitmentOutputs p ∧
      o.kind = .remoteAnchor ∧
      o.scriptPubKey = p2wsh (sha256 (anchorWitnessScript p.remoteFundingKey)) := by
  refine ⟨⟨.remoteAnchor, anchorValue,
      anchorScriptPubKey p.remoteAnchorWitnessScriptHash⟩, ?_, rfl, ?_⟩
  · simp [commitmentOutputs]
  · simp [anchorScriptPubKey, h.2.2.2]

/-! ## Ownership and spendability -/

/-- Which party owns each anchor kind.  `localAnchor` belongs to the local
commitment (the one the local node broadcasts), `remoteAnchor` to the remote
commitment.  Non-anchor kinds have no anchor owner. -/
def anchorOwner : OutputKind → Option Direction
  | .localAnchor => some .local
  | .remoteAnchor => some .remote
  | _ => none

theorem anchorOwner_local : anchorOwner .localAnchor = some .local := rfl

theorem anchorOwner_remote : anchorOwner .remoteAnchor = some .remote := rfl

/-- An abstract model of the L1 anchor spend semantics.  `spend hash key
witness tx` means that `witness` satisfies the anchor `scriptPubKey` for the
witness-program `hash`, with the spend authorised by `key`.  `sound` is the
BIP 143 bridge: a valid spend can only use the key committed to by the
script.  The interpreter itself is not imported in wave A. -/
structure AnchorSpendModel where
  spend : ByteArray → PubKey → WitnessStack → Tx → Prop
  committedKey : ByteArray → PubKey
  sound : ∀ (hash : ByteArray) (key : PubKey) (witness : WitnessStack) (tx : Tx),
    spend hash key witness tx → key = committedKey hash

/-- **Any anchor spend is authorised by the key committed to in the script.** -/
theorem anchor_spend_requires_committed_key
    (M : AnchorSpendModel) {hash : ByteArray} {key : PubKey}
    {witness : WitnessStack} {tx : Tx}
    (h : M.spend hash key witness tx) :
    key = M.committedKey hash :=
  M.sound hash key witness tx h

/-- **The local anchor is spendable only by the local funding key.**  This is
the ownership law for the anchor attached to the local commitment; it is
conditional on the committed-key identification
`committedKey localAnchorHash = localFundingKey`, which is the missing
script-interpreter/hash bridge. -/
theorem local_anchor_spendable_only_by_local_key
    (M : AnchorSpendModel) (p : CommitmentParams)
    (hcommit : M.committedKey p.localAnchorWitnessScriptHash = p.localFundingKey)
    {witness : WitnessStack} {tx : Tx} {key : PubKey}
    (hspend : M.spend p.localAnchorWitnessScriptHash key witness tx) :
    key = p.localFundingKey := by
  rw [M.sound _ _ _ _ hspend, hcommit]

/-- **The remote funding key cannot spend the local anchor** when the two
funding keys differ. -/
theorem local_anchor_not_spendable_by_remote_key
    (M : AnchorSpendModel) (p : CommitmentParams)
    (hcommit : M.committedKey p.localAnchorWitnessScriptHash = p.localFundingKey)
    (hneq : p.remoteFundingKey ≠ p.localFundingKey)
    (witness : WitnessStack) (tx : Tx) :
    ¬ M.spend p.localAnchorWitnessScriptHash p.remoteFundingKey witness tx := by
  intro hspend
  have hkey : p.remoteFundingKey = p.localFundingKey := by
    rw [M.sound _ _ _ _ hspend, hcommit]
  exact hneq hkey

/-- The symmetric ownership law for the remote anchor. -/
theorem remote_anchor_spendable_only_by_remote_key
    (M : AnchorSpendModel) (p : CommitmentParams)
    (hcommit : M.committedKey p.remoteAnchorWitnessScriptHash = p.remoteFundingKey)
    {witness : WitnessStack} {tx : Tx} {key : PubKey}
    (hspend : M.spend p.remoteAnchorWitnessScriptHash key witness tx) :
    key = p.remoteFundingKey := by
  rw [M.sound _ _ _ _ hspend, hcommit]

/-- The local funding key cannot spend the remote anchor when the keys
differ. -/
theorem remote_anchor_not_spendable_by_local_key
    (M : AnchorSpendModel) (p : CommitmentParams)
    (hcommit : M.committedKey p.remoteAnchorWitnessScriptHash = p.remoteFundingKey)
    (hneq : p.localFundingKey ≠ p.remoteFundingKey)
    (witness : WitnessStack) (tx : Tx) :
    ¬ M.spend p.remoteAnchorWitnessScriptHash p.localFundingKey witness tx := by
  intro hspend
  have hkey : p.localFundingKey = p.remoteFundingKey := by
    rw [M.sound _ _ _ _ hspend, hcommit]
  exact hneq hkey

/-! ## Fee treatment of anchors -/

/-- BOLT 3 fee from a feerate and a weight, floored, converted to satoshis:
`feerate_per_kw * weight / 1000 / 1000`.  Since `feerate_per_kw` is msat per
1000 weight units, this is the satoshi fee for the modelled weight. -/
def feerateFeeSat (r : FeeRate) (w : Weight) : BtcAmount :=
  ((r.msatPerKw * w.val / 1000 / 1000 : Nat) : Int)

/-- The inputs the fee rule actually reads.  `anchorValueSat` is carried only
to prove that it is ignored. -/
structure CommitmentFeeContext where
  feerate : FeeRate
  weight : Weight
  anchorValueSat : BtcAmount := anchorValue

/-- The fee is a function of the feerate and the weight alone. -/
def CommitmentFeeContext.feeSat (c : CommitmentFeeContext) : BtcAmount :=
  feerateFeeSat c.feerate c.weight

/-- **The anchor's satoshi value is excluded from the fee calculation.**  The
fee reads only `feerate` and `weight`; changing `anchorValueSat` leaves it
unchanged.  Anchor *presence* still affects the fee through the weight (the
next theorem), which is the exact inclusion rule in this model. -/
theorem fee_ignores_anchor_value (c : CommitmentFeeContext) (v : BtcAmount) :
    ({ c with anchorValueSat := v }).feeSat = c.feeSat := rfl

/-- BOLT 3 expected commitment weight: 724 without anchors, 1124 with
anchors, plus 172 per untrimmed HTLC output.  This restates the constants of
`LnLean.Channel.Commitment.commitmentWeight`; the channel module is outside
this module's wave-A import set. -/
def boltCommitmentWeight (anchors : Bool) (numHtlcs : Nat) : Weight :=
  ⟨(if anchors then 1124 else 724) + 172 * numHtlcs⟩

theorem boltCommitmentWeight_true (numHtlcs : Nat) :
    (boltCommitmentWeight true numHtlcs).val = 1124 + 172 * numHtlcs := rfl

theorem boltCommitmentWeight_false (numHtlcs : Nat) :
    (boltCommitmentWeight false numHtlcs).val = 724 + 172 * numHtlcs := rfl

/-- **Anchors add 400 weight units**, hence affect the fee only through the
weight term. -/
theorem anchor_weight_adds_400 (numHtlcs : Nat) :
    (boltCommitmentWeight true numHtlcs).val =
      (boltCommitmentWeight false numHtlcs).val + 400 := by
  simp [boltCommitmentWeight]
  omega

/-! ## Conservation with anchor outputs -/

/-- The value accounting of a commitment transaction, in satoshis.  `Int` is
used so that the conservation equation can be rearranged without truncating
subtraction.  `anchorCount` is the number of anchor outputs (0 or 2 in the
templates considered here). -/
structure AnchorAccounting where
  funding : Int
  toLocal : Int
  toRemote : Int
  fee : Int
  anchorCount : Nat

/-- The satoshi value paid to anchor outputs.  The per-anchor value is the
protocol constant `anchorValue`, so no per-record override is possible. -/
def AnchorAccounting.anchorDeduction (a : AnchorAccounting) : Int :=
  (a.anchorCount : Int) * anchorValue

/-- BOLT 3 value conservation: outputs plus fee plus anchors equal the funding
value. -/
def AnchorAccounting.Conserves (a : AnchorAccounting) : Prop :=
  a.toLocal + a.toRemote + a.fee + a.anchorDeduction = a.funding

/-- With two anchors the anchor deduction is exactly `2 * 330`. -/
theorem anchor_deduction_two (a : AnchorAccounting)
    (h : a.anchorCount = 2) :
    a.anchorDeduction = 2 * anchorValue := by
  unfold AnchorAccounting.anchorDeduction
  rw [h]
  rfl

/-- **Without anchors, conservation is the plain fee equation.** -/
theorem conservation_no_anchors (a : AnchorAccounting)
    (hcount : a.anchorCount = 0) (h : a.Conserves) :
    a.toLocal + a.toRemote = a.funding - a.fee := by
  have hd : a.anchorDeduction = 0 := by
    unfold AnchorAccounting.anchorDeduction
    rw [hcount]
    rfl
  unfold AnchorAccounting.Conserves at h
  rw [hd] at h
  omega

/-- **With two anchors, the funder's two commitment outputs are reduced by the
fee and by 660 satoshis.**  This is the exact corrected conservation
equation; the anchor value is a separate deduction, not part of the fee. -/
theorem conservation_two_anchors (a : AnchorAccounting)
    (hcount : a.anchorCount = 2) (h : a.Conserves) :
    a.toLocal + a.toRemote = a.funding - a.fee - 2 * anchorValue := by
  have hd : a.anchorDeduction = 2 * anchorValue := anchor_deduction_two a hcount
  unfold AnchorAccounting.Conserves at h
  rw [hd] at h
  omega

/-- The effective deduction from the commitment outputs is `fee + anchors`,
not the fee alone.  This is the form that shows why the brief's "except
through the fee term" is too strong for the anchor variant. -/
theorem conservation_effective_deduction (a : AnchorAccounting)
    (hcount : a.anchorCount = 2) (h : a.Conserves) :
    a.toLocal + a.toRemote = a.funding - (a.fee + 2 * anchorValue) := by
  have hd : a.anchorDeduction = 2 * anchorValue := anchor_deduction_two a hcount
  unfold AnchorAccounting.Conserves at h
  rw [hd] at h
  omega

/-- Equivalently, moving the anchor deduction to the left gives the same
conservation equation as `Conserves`. -/
theorem conservation_separates_fee (a : AnchorAccounting) :
    a.toLocal + a.toRemote + (a.fee + a.anchorDeduction) = a.funding ↔
      a.Conserves := by
  unfold AnchorAccounting.Conserves
  constructor <;> intro h <;> omega

/-! ## Open byte-level obligations -/

/-- `pushData` is injective: both sides have a one-byte length prefix, so
left-cancelling the payload is enough.  The payload length need not be known
in advance; the prefix has the same size (`1`) on both sides. -/
private theorem pushData_injective {a b : ByteArray} (h : pushData a = pushData b) :
    a = b := by
  unfold pushData at h
  have hs : (ByteArray.empty.push a.size.toUInt8).size =
      (ByteArray.empty.push b.size.toUInt8).size := by simp
  exact (ByteArray.append_eq_append_iff_of_size_eq_left hs).mp h |>.2

/-- Two equal anchor witness scripts commit to equal funding keys.  The anchor
template is the key push followed by a fixed opcode suffix, so equality
cancels the suffix (`ByteArray.append_left_inj`) and then the push prefix
(`pushData_injective`). -/
theorem anchorWitnessScript_key_injective
    (k₁ k₂ : PubKey) (h₁ : k₁.Valid) (h₂ : k₂.Valid)
    (h : anchorWitnessScript k₁ = anchorWitnessScript k₂) : k₁ = k₂ := by
  have hb : (anchorWitnessScript k₁).bytes = (anchorWitnessScript k₂).bytes :=
    congrArg Script.bytes h
  have hp : pushData k₁.bytes = pushData k₂.bytes := by
    apply (ByteArray.append_left_inj
      ((ByteArray.empty.push OP_CHECKSIG) ++
       (ByteArray.empty.push OP_IFDUP) ++
       (ByteArray.empty.push OP_NOTIF) ++
       (ByteArray.empty.push OP_16) ++
       (ByteArray.empty.push OP_CSV) ++
       (ByteArray.empty.push OP_ENDIF))).mp
    simpa [anchorWitnessScript, ByteArray.append_assoc] using hb
  have hbytes : k₁.bytes = k₂.bytes := pushData_injective hp
  cases k₁
  cases k₂
  simpa using hbytes

/-- Under SHA256 collision resistance, distinct funding keys give distinct
anchor P2WSH programs.  This composes `LN-ANCHOR-007` with the assumed hash
bridge `HashesMatch`; it is recorded separately because the crypto assumption
must remain visible. -/
theorem localAnchor_hash_ne_remoteAnchor_hash
    (p : CommitmentParams) (sha256 : Script → ByteArray)
    (h : p.HashesMatch sha256)
    (hcr : ∀ a b : Script, sha256 a = sha256 b → a = b)
    (hk₁ : p.localFundingKey.Valid) (hk₂ : p.remoteFundingKey.Valid)
    (hkeys : p.localFundingKey ≠ p.remoteFundingKey) :
    p.localAnchorWitnessScriptHash ≠ p.remoteAnchorWitnessScriptHash := by
  intro heq
  have hlocal : p.localAnchorWitnessScriptHash =
      sha256 (anchorWitnessScript p.localFundingKey) := h.2.2.1
  have hremote : p.remoteAnchorWitnessScriptHash =
      sha256 (anchorWitnessScript p.remoteFundingKey) := h.2.2.2
  have hsh : sha256 (anchorWitnessScript p.localFundingKey) =
      sha256 (anchorWitnessScript p.remoteFundingKey) := by
    rw [← hlocal, ← hremote]
    exact heq
  have hscripts : anchorWitnessScript p.localFundingKey =
      anchorWitnessScript p.remoteFundingKey := hcr _ _ hsh
  exact hkeys (anchorWitnessScript_key_injective
    p.localFundingKey p.remoteFundingKey hk₁ hk₂ hscripts)

end LnLean.Bitcoin

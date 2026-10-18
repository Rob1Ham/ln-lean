import LnLean.Channel.Commitment
import LnLean.Proofs.WaveD.D12

/-!
# Commitment output ordering and dust trimming (LN-CH-003)

Catalog row `LN-CH-003` claims:

> Commitment outputs are ordered by value then script, and dust HTLCs are
> trimmed.

The unconditional claim is **false** of the legacy value-only output function
`LnLean.Channel.Commitment.commitmentOutputs`: that function emits the fixed
group order `to_local, to_remote, HTLCs, anchors`, never sorts, and applies no
dust filter.  The mechanized counterexample is retained in
`LnLean.Proofs.WaveD.D12` (`waveD_d12_output_ordering_fails`,
`waveD_d12_cltv_tiebreak_not_recoverable`,
`waveD_d12_dust_trimming_requires_filter`).  This module restates the
refutation as `unconditional_ordering_refuted`; nothing in that file is
weakened or deleted.

The faithful repair is the `CommitmentTx` extension in
`LnLean.Channel.Commitment`:

* `ScriptPubKey` supplies the missing raw script bytes;
* `CommitmentTxOutput` carries the BOLT 3 key
  `(valueSat, scriptPubKey, cltvExpiry)`;
* `CommitmentTx.dustLimitSat` supplies the transaction owner's
  `dust_limit_satoshis`;
* `CommitmentTx.outputs` is the deterministic construction: trim
  `to_local`/`to_remote`/HTLC outputs below the owner's dust limit (HTLC
  values are already net of the second-stage fee), keep anchors, then sort by
  value, then script (memcmp, shorter prefix first), then CLTV.

`output_ordering` is the catalog target.  It is a theorem about this explicit
model, not about `commitmentOutputs`, and it bundles:

1. the sorted list is a permutation of the constructed pre-sort list;
2. it is pairwise sorted by the BOLT 3 three-key order;
3. its value projection is nondecreasing;
4. on equal values, script order is nondecreasing;
5. on equal values and scripts, CLTV expiry is nondecreasing;
6. `to_local`/`to_remote` are omitted exactly when below the dust limit;
7. every below-dust HTLC produces no output;
8. every at-or-above-dust HTLC in the commitment produces its output;
9. every emitted non-anchor output is at or above the dust limit.

Premises that remain explicit: the owner's dust limit is a parameter of
`CommitmentTx`; script bytes are supplied by the caller (the model does not
derive them from funding keys); `CommitmentHTLCOutput.amountSat` is assumed to
be the BOLT 3 post-second-stage-fee value; anchors are modelled as always
present when `option_anchors` is on (the single-anchor exception is out of
scope, as in the legacy model); equal-key outputs are interchangeable and
their relative order is chosen deterministically by `List.mergeSort`.
-/

namespace LnLean.Channel.Commitment

open LnLean
open LnLean.Channel
open LnLean.Proofs.WaveD.D12

/-- **The unconditional claim remains refuted.**  There is a commitment whose
emitted value sequence is not sorted.  This is D12's counterexample, retained
verbatim as a consequence of the legacy `commitmentOutputs`. -/
theorem unconditional_ordering_refuted :
    ¬ (∀ c : Commitment,
        (c.commitmentOutputs.map CommitmentOutput.value).Pairwise (· ≤ ·)) :=
  waveD_d12_output_ordering_fails

/-- D12's information-loss result: the old output type cannot recover the
CLTV tiebreak, so no ordering theorem over `CommitmentOutput` alone can exist.
Restated here to keep the counterexample visible from the catalog target. -/
theorem cltv_tiebreak_not_recoverable :
    cltvOrderLeft.htlcs ≠ cltvOrderRight.htlcs ∧
      cltvOrderLeft.commitmentOutputs = cltvOrderRight.commitmentOutputs :=
  waveD_d12_cltv_tiebreak_not_recoverable

/-- **Catalog target `LN-CH-003` / `output_ordering`.**  For every faithful
commitment-transaction record, the deterministic BOLT 3 construction produces
a permutation of the trimmed output set that is sorted by value, then script,
then CLTV expiry, and every output it emits is either an anchor or at or above
the owner's dust limit.  Dust HTLCs are absent; non-dust HTLCs are present.

The dust/script/CLTV data and the dust limit are fields of `CommitmentTx`;
they are not invented inside the proof.  The legacy `commitmentOutputs`
function is not the subject of this theorem (see
`unconditional_ordering_refuted`). -/
theorem output_ordering (tx : CommitmentTx) :
    tx.outputs.Perm tx.outputsUnsorted ∧
      tx.outputs.Pairwise CommitmentTxOutput.le ∧
      (tx.outputs.map (fun o => o.valueSat)).Pairwise (· ≤ ·) ∧
      tx.outputs.Pairwise (fun a b =>
        a.valueSat = b.valueSat → a.scriptPubKey.le b.scriptPubKey) ∧
      tx.outputs.Pairwise (fun a b =>
        a.valueSat = b.valueSat → a.scriptPubKey = b.scriptPubKey →
          a.cltvExpiry ≤ b.cltvExpiry) ∧
      (tx.toLocalOutput = none ↔ tx.commitment.toLocalSat < tx.dustLimitSat) ∧
      (tx.toRemoteOutput = none ↔ tx.commitment.toRemoteSat < tx.dustLimitSat) ∧
      (∀ h ∈ tx.commitment.htlcs,
        h.amountSat < tx.dustLimitSat → tx.htlcOutput h = none) ∧
      (∀ h ∈ tx.commitment.htlcs, tx.dustLimitSat ≤ h.amountSat →
        CommitmentTxOutput.htlc h (tx.htlcScript h) ∈ tx.outputs) ∧
      (∀ o ∈ tx.outputs, o.kind ≠ .localAnchor → o.kind ≠ .remoteAnchor →
        tx.dustLimitSat ≤ o.valueSat) :=
  CommitmentTx.outputs_spec tx

/-- Ordering component: the output values are nondecreasing. -/
theorem outputs_values_nondecreasing (tx : CommitmentTx) :
    (tx.outputs.map (fun o => o.valueSat)).Pairwise (· ≤ ·) :=
  CommitmentTx.outputs_values_sorted tx

/-- Ordering component: on equal value, scripts are nondecreasing in BOLT 3
memcmp order. -/
theorem outputs_scripts_nondecreasing (tx : CommitmentTx) :
    tx.outputs.Pairwise (fun a b =>
      a.valueSat = b.valueSat → a.scriptPubKey.le b.scriptPubKey) :=
  CommitmentTx.outputs_scripts_sorted tx

/-- Ordering component: on equal value and script, HTLC CLTV expiries are
nondecreasing. -/
theorem outputs_cltvs_nondecreasing (tx : CommitmentTx) :
    tx.outputs.Pairwise (fun a b =>
      a.valueSat = b.valueSat → a.scriptPubKey = b.scriptPubKey →
        a.cltvExpiry ≤ b.cltvExpiry) :=
  CommitmentTx.outputs_cltvs_sorted tx

/-- Trimming component: a below-dust HTLC produces no output at all. -/
theorem dust_htlc_trimmed (tx : CommitmentTx) (h : CommitmentHTLCOutput)
    (hd : h.amountSat < tx.dustLimitSat) :
    tx.htlcOutput h = none :=
  CommitmentTx.htlcOutput_eq_none_of_dust tx h hd

/-- Trimming component: an at-or-above-dust HTLC in the commitment produces
its output. -/
theorem nonDust_htlc_kept (tx : CommitmentTx) (h : CommitmentHTLCOutput)
    (hmem : h ∈ tx.commitment.htlcs) (hd : tx.dustLimitSat ≤ h.amountSat) :
    CommitmentTxOutput.htlc h (tx.htlcScript h) ∈ tx.outputs :=
  CommitmentTx.htlcOutput_mem_outputs tx h hmem hd

/-- Trimming component: no emitted HTLC output is below the dust limit. -/
theorem no_dust_htlc_output (tx : CommitmentTx) {o : CommitmentTxOutput}
    (ho : o ∈ tx.outputs) (hk : ∃ dir, o.kind = .htlc dir) :
    tx.dustLimitSat ≤ o.valueSat :=
  CommitmentTx.no_dust_htlc_output tx ho hk

/-- Consistency with the legacy model: at dust limit zero, with non-zero
`to_local` and `to_remote`, the kind/value projection of the rich output list
is exactly `Commitment.commitmentOutputs`.  The extension adds scripts, the
dust limit, and sorting; it does not change which non-dust outputs exist. -/
theorem toCommitmentOutput_eq_legacy (tx : CommitmentTx)
    (hdust : tx.dustLimitSat = 0)
    (hl : tx.commitment.toLocalSat ≠ 0) (hr : tx.commitment.toRemoteSat ≠ 0) :
    (tx.outputsUnsorted.map CommitmentTxOutput.toCommitmentOutput) =
      tx.commitment.commitmentOutputs :=
  CommitmentTx.map_toCommitmentOutput_outputsUnsorted tx hdust hl hr

end LnLean.Channel.Commitment

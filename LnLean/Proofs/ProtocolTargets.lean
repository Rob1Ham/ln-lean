/-
# Protocol catalog targets — faithful wrappers

This module supplies the catalog names for the protocol rows whose wave-A
targets were absent:

* `LnLean.Protocol.Handshake.open_bounds` (LN-PR-001);
* `LnLean.Protocol.Handshake.funding_signed_valid` (LN-PR-003);
* `LnLean.Protocol.Messages.commitment_signed_covers` (LN-PR-004);
* `LnLean.Protocol.Handshake.feature_intersection` (LN-PR-006).

Each wrapper is a restatement of an existing faithful theorem, at the
catalog namespace, and adds no hypotheses beyond the source theorem.  The
underlying models live in:

* `LnLean.Proofs.WaveD.D17` — the acceptor-side `open_channel` record and
  `acceptOpenChannel`;
* `LnLean.Proofs.WaveE.E19` — the checked funding-signature predicate;
* `LnLean.Proofs.WaveE.E20` — the `commitment_signed` coverage predicate and
  its bundled consequences;
* `LnLean.Proofs.WaveE.E22` — the support-set intersection form of feature
  negotiation.

The D/E modules import the wave-A protocol modules, never this file, so the
imports below introduce no cycle.

`LnLean.Protocol.Handshake.feature_intersection` (LN-PR-006) restates E22's
conditional main theorem.  The catalog sentence must be read as the
intersection of the two *support sets*, not as a bitwise AND of the raw
feature vectors: the latter is false
(`bitwiseIntersection_not_negotiation` in
`LnLean.Proofs.Protocol.FeaturesProps`).  The BOLT 1 survival hypothesis is
the one condition under which the full negotiated rule equals that
intersection; see `agents/reports/PR-WRAPPERS.md`.
-/

import LnLean.Proofs.WaveD.D17
import LnLean.Proofs.WaveE.E19
import LnLean.Proofs.WaveE.E20
import LnLean.Proofs.WaveE.E22

set_option autoImplicit false

namespace LnLean.Protocol.Handshake

open LnLean
open LnLean.Protocol
open LnLean.Crypto
open LnLean.Proofs.WaveD.D17
open LnLean.Proofs.WaveE.E19
open LnLean.Proofs.WaveE.E22
open LnLean.Proofs.Protocol

/-- **LN-PR-001 / `open_bounds`.**  Any `open_channel` accepted by the D17
acceptor satisfies the three funding bounds: the channel value is strictly
above the negotiated dust limit, at least the hard 1000-satoshi minimum, and
at least the acceptor's configured `min_funding_satoshis`.

This is exactly `D17.waveD_d17_open_bounds`; the acceptance hypothesis is the
acceptor transition, not the conclusion. -/
theorem open_bounds {p : AcceptPolicy} {m : OpenChannelMsg}
    {a : OpenChannelAcceptance}
    (h : acceptOpenChannel p m = some a) :
    m.dustLimitSatoshis < m.fundingSatoshis ∧
      minChannelValueSatoshis ≤ m.fundingSatoshis ∧
      p.minFundingSatoshis ≤ m.fundingSatoshis :=
  waveD_d17_open_bounds h

/-- **LN-PR-003 / `funding_signed_valid`.**  A `funding_signed` signature is
valid exactly when it has a BOLT wire shape and verifies in the funding domain
under the supplied verifier model, funding key, and funding-transaction bytes.

The funding key and transaction are explicit parameters because the wave-A
`FundingSigned` record has no fields for them; this is E19's
`waveE_e19_funding_signed_valid_iff`, not a length check and not an
unconditional claim about every decoded message. -/
theorem funding_signed_valid (M : PrimitiveModel) (fundingKey : PubKey)
    (fundingTx : ByteArray) (m : FundingSigned) :
    fundingSignedValid M fundingKey fundingTx m ↔
      wireSigOK m.signature.bytes = true ∧
        fundingSignedVerifies M fundingKey fundingTx m :=
  waveE_e19_funding_signed_valid_iff M fundingKey fundingTx m

/-- **LN-PR-006 / `feature_intersection`.**  Under the BOLT 1 survival
hypothesis — the peer supports every feature the local node requires — the
negotiated feature predicate is exactly the intersection of the two peers'
supported-feature sets (`featureIntersection`, which is
`FeaturesProps.mutualSupport`).

This is E22's `waveE_e22_negotiated_eq_featureIntersection`.  The intersection
is at the level of supported features, not the raw bitwise AND of the feature
vectors; the latter is false (`bitwiseIntersection_not_negotiation`), and
without the survival hypothesis the unconditional claim also fails
(`waveE_e22_unconditional_claim_false`). -/
theorem feature_intersection (lcl rmt : FeatureVector)
    (hAccept : ∀ n, lcl.requires n = true → rmt.supports n = true)
    (n : Nat) :
    negotiated lcl rmt n = featureIntersection lcl rmt n :=
  waveE_e22_negotiated_eq_featureIntersection lcl rmt hAccept n

end LnLean.Protocol.Handshake

namespace LnLean.Protocol.Messages

open LnLean
open LnLean.Protocol
open LnLean.Channel
open LnLean.Proofs.WaveE.E20

/-- **LN-PR-004 / `commitment_signed_covers`.**  Under E20's coverage
predicate — one HTLC signature per untrimmed HTLC output of the supplied
commitment, and the BOLT 3 fee equation — a well-formed `commitment_signed`
carries exactly `#htlcs + 1` signatures, its payload is bounded by
`34 + 73 + 73 * #htlcs`, and the covered commitment pays the formula fee.

The commitment transaction, its HTLC set, and the feerate are explicit
parameters: the wire record alone does not determine them.  This is exactly
`E20.waveE_e20_commitment_signed_covers_exact`; it is not the false
unconditional reading. -/
theorem commitment_signed_covers (m : CommitmentSigned) (r : FeeRate)
    (c : Commitment)
    (hc : waveE_e20_commitment_signed_covers m r c)
    (hwf : wellFormed (.commitmentSigned m)) :
    m.htlcSignatures.length = c.htlcs.length ∧
      (signatures (.commitmentSigned m)).length = c.htlcs.length + 1 ∧
      msgLength (.commitmentSigned m) ≤ 34 + 73 + 73 * c.htlcs.length ∧
      c.feeSat = (commitmentFee r c).val :=
  waveE_e20_commitment_signed_covers_exact m r c hc hwf

end LnLean.Protocol.Messages

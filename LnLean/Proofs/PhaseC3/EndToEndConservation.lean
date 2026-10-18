import LnLean.Proofs.Common

/-!
# LnLean.Proofs.PhaseC3.EndToEndConservation

English claim.  A Lightning channel is funded by one L1 funding output.  For
every state of the end-to-end model, the value held in that output is exactly
the sum of three explicit buckets:

* the channel outputs not yet attributed to a settled payment,
* the amounts of the payments that have been settled (each settlement is a
  receipt attributed to some channel output, so it is counted exactly once),
* the fee bucket, i.e. the commitment fee announced by the live commitment.

The state additionally carries the channel ledger of
`LnLean.Proofs.Conservation`: a funding value and the list of every commitment
built for the channel.  `Funded` requires the L1 funding value, the ledger's
funding value, and the live commitment's funding value to agree, and requires
every ledger commitment to satisfy the BOLT 3 conservation equation.

Consequently:

* replacing the live commitment by any conserving commitment preserves
  `TotalValue` (a "conserved channel step");
* settling an HTLC output (via `settleHTLCOutputAt_conserved`) and recording
  the payment preserves `TotalValue`;
* every finite run of such steps preserves `TotalValue`, so no run creates
  value: the total stays equal to the L1 funding value.

BOLT sections.
* BOLT 2 `open_channel` / `funding_signed` and the BOLT 3 funding output
  (`refs/bolts/02-peer-protocol.md:600-760`,
  `refs/bolts/03-transactions.md:83-120`): one 2-of-2 funding output carries
  the channel value.
* BOLT 3 §2 `Commitment Transaction Outputs`
  (`refs/bolts/03-transactions.md:102-307`): `to_local`, `to_remote`, HTLC
  outputs and anchor outputs.
* BOLT 3 §4 `Fee Calculation` (`refs/bolts/03-transactions.md:466-576`): the
  commitment fee is part of the funding-value equation.
* BOLT 2 `update_fulfill_htlc` / `update_fail_htlc`
  (`refs/bolts/02-peer-protocol.md:2921-2955`): an HTLC is removed and its
  value is credited to one side, never duplicated.

rust-lightning anchors at `fe4900930c6bd5786ec4203274d7cf312776a5a6`.
* `lightning/src/ln/channel.rs:2683` (`funding` value and outpoint).
* `lightning/src/ln/chan_utils.rs:716-744` (`HTLCOutputInCommitment`,
  `to_bitcoin_amount`).
* `lightning/src/ln/chan_utils.rs:1887-1966` (`insert_non_htlc_outputs` and
  the commitment output sum).
* `lightning/src/chain/channelmonitor.rs:5079` (on-chain resolution of a
  commitment).
* `lightning/src/ln/outbound_payment.rs:164` (`Fulfilled`) and
  `:320` (`mark_fulfilled`): the terminal payment state recorded here.

What is NOT modelled.
* Wire encoding, transaction ordering, signatures, witnesses and script
  execution; the equation is over output *values* only.
* The SHA-256 preimage relation and the BOLT 2 guard conditions of
  `update_add_htlc` / `update_fulfill_htlc`; the payment record only stores
  the coarse terminal session state, supplied by the caller.
* Second-stage HTLC transactions and their fees, anchor CPFP, RBF, and the
  economics of penalty fees.  Those are separate fee buckets outside this
  model.
* Watchtower liveness and whether the counterparty broadcasts the latest
  commitment; this module proves what the accounting does when a step occurs.
-/

namespace LnLean.Proofs.PhaseC3

open LnLean
open LnLean.Channel
open LnLean.Payment
open LnLean.Proofs

set_option autoImplicit false

/-! ## A settled payment as an end-to-end receipt -/

/-- One payment that the end-to-end model has settled.  `session` is the
`LnLean.Payment.PaymentSession` (BOLT 11 payment hash, target and parts);
`amountSat` is the satoshi value attributed to it by the channel settlement;
`fulfilled` records whether the settlement was a fulfilment (as opposed to a
failure refund).  `settled` is the bridge proof that the recorded session is
in the successful terminal state, so a settled receipt cannot be forged from
a pending or failed session. -/
structure SettledPayment where
  session : PaymentSession
  amountSat : Nat
  fulfilled : Bool
  settled : session.state = .succeeded

/-- Total value attributed to settled payments.  Kept as a structural
recursion so that the proofs below do not need list-sum typeclass lemmas. -/
def settledTotal : List SettledPayment → Nat
  | [] => 0
  | p :: ps => p.amountSat + settledTotal ps

@[simp] theorem settledTotal_nil : settledTotal [] = 0 := rfl

@[simp] theorem settledTotal_cons (p : SettledPayment) (ps : List SettledPayment) :
    settledTotal (p :: ps) = p.amountSat + settledTotal ps := rfl

/-! ## The end-to-end state -/

/-- The composition state.  It holds the L1 funding output, the channel
ledger and the live commitment, the settled payments, and the fee bucket.

The L1 bridge is a structure field, not an axiom: `fundingLink` states that
the btc-lean `FundingOutput`'s value (an `Int` amount) is the natural number
`fundingValue` used by the value accounting.  `feeLink` states that the fee
bucket is exactly the live commitment's fee, so the fee term is explicit and
cannot silently drift from the commitment. -/
structure EndToEndState where
  /-- The L1 funding output from `LnLean.Bitcoin.Seam`. -/
  funding : LnLean.Bitcoin.FundingOutput
  /-- The funding value in satoshis, as a `Nat` for the value arithmetic. -/
  fundingValue : Nat
  /-- **L1 bridge (field, not axiom).**  The btc-lean output carries exactly
  `fundingValue`. -/
  fundingLink : funding.value = (fundingValue : Int)
  /-- The channel ledger: one funding value plus every commitment built on
  it (`LnLean.Proofs.ChannelLedger`). -/
  ledger : ChannelLedger
  /-- The live commitment, i.e. the state the channel is currently in. -/
  live : Commitment
  /-- Payments settled so far. -/
  payments : List SettledPayment
  /-- The explicit fee bucket: the commitment fee of the live commitment. -/
  feeBucket : Nat
  /-- **Fee bridge (field, not axiom).**  The bucket equals the live
  commitment's `feeSat`. -/
  feeLink : feeBucket = live.feeSat

/-- `TotalValue` splits the live commitment's output value into the part not
yet attributed to a settled payment and the settled payments themselves, and
adds the explicit fee bucket.  A settled payment is therefore counted exactly
once (never both in the residual channel bucket and the payment bucket). -/
def TotalValue (s : EndToEndState) : Nat :=
  (s.live.totalOutputValue - settledTotal s.payments) + settledTotal s.payments
    + s.feeBucket

/-- The state is funded when the live commitment belongs to the ledger, every
ledger commitment conserves value, the ledger's funding value equals the L1
value, and the settled payments fit inside the live commitment's outputs.
Every clause is an explicit hypothesis about the model bridges. -/
def Funded (s : EndToEndState) : Prop :=
  s.live ∈ s.ledger.commitments ∧
  s.ledger.AllConserved ∧
  s.ledger.fundingValueSat = s.fundingValue ∧
  settledTotal s.payments ≤ s.live.totalOutputValue

/-! ## Small arithmetic facts about `TotalValue` -/

/-- Under the payment-coverage invariant, the split form of `TotalValue` is
exactly "channel outputs + fee bucket". -/
theorem totalValue_eq_outputs_fee (s : EndToEndState)
    (h : settledTotal s.payments ≤ s.live.totalOutputValue) :
    TotalValue s = s.live.totalOutputValue + s.live.feeSat := by
  unfold TotalValue
  rw [s.feeLink]
  omega

/-- **A funded state's total value is the L1 funding value.**  The live
commitment's conservation equation, the ledger funding link, and the L1
funding link are composed here. -/
theorem totalValue_eq_funding (s : EndToEndState) (hf : Funded s) :
    TotalValue s = s.fundingValue := by
  rcases hf with ⟨hmem, hall, hledger, hcov⟩
  rcases hall s.live hmem with ⟨hfund, hcons⟩
  rw [totalValue_eq_outputs_fee s hcov]
  unfold CommitmentConserved at hcons
  omega

/-- No funded channel state emits more than its L1 funding value.  This is the
imported `ledger_no_value_creation` applied to the live commitment. -/
theorem live_outputs_le_funding (s : EndToEndState) (hf : Funded s) :
    s.live.totalOutputValue ≤ s.fundingValue := by
  rcases hf with ⟨hmem, hall, hledger, _⟩
  have h := ledger_no_value_creation s.ledger hall s.live hmem
  rw [hledger] at h
  exact h

/-! ## HTLC settlement at the commitment level -/

/-- `settleHTLCOutputAt` preserves the commitment's funding value: the value
moves between output slots, it is never re-denominated. -/
theorem settleHTLCOutputAt_fundingValueSat (c : Commitment)
    (before after : List CommitmentHTLCOutput) (h : CommitmentHTLCOutput)
    (fulfilled hadOutput : Bool) :
    (settleHTLCOutputAt c before after h fulfilled hadOutput).fundingValueSat =
      c.fundingValueSat := by
  unfold settleHTLCOutputAt
  cases hadOutput with
  | false => rfl
  | true =>
      dsimp only
      simp only [ite_true]
      simp

/-- `settleHTLCOutputAt` preserves the total output value: a succeeded or
failed HTLC removes one output and credits exactly the same amount to a
balance (`credit_replace_htlcs_total`), while a dust HTLC moves nothing. -/
theorem settleHTLCOutputAt_totalOutputValue (c : Commitment)
    (before after : List CommitmentHTLCOutput) (h : CommitmentHTLCOutput)
    (fulfilled hadOutput : Bool)
    (hmem : c.htlcs = before ++ h :: after) :
    (settleHTLCOutputAt c before after h fulfilled hadOutput).totalOutputValue =
      c.totalOutputValue := by
  unfold settleHTLCOutputAt
  cases hadOutput with
  | false => rfl
  | true =>
      dsimp only
      simp only [ite_true]
      exact credit_replace_htlcs_total c before after h
        (fundingSide c (if fulfilled then h.direction.flip else h.direction)) hmem

/-! ## Ledger and live-commitment update helpers -/

/-- Prepending a conserving commitment to a conserving ledger keeps the
ledger conserving, provided the new commitment carries the same funding
value. -/
theorem ChannelLedger.allConserved_cons (l : ChannelLedger) (c : Commitment)
    (hc : CommitmentConserved c)
    (hfund : c.fundingValueSat = l.fundingValueSat)
    (hl : l.AllConserved) :
    ({ l with commitments := c :: l.commitments }).AllConserved := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact ⟨hfund, hc⟩
  · exact hl x hx

namespace EndToEndState

/-- Replace the live commitment with a conserving successor and append it to
the ledger.  The fee bucket follows the new commitment, so the fee bridge is
maintained. -/
def replaceLive (s : EndToEndState) (c : Commitment) : EndToEndState :=
  { funding := s.funding
    fundingValue := s.fundingValue
    fundingLink := s.fundingLink
    ledger := { s.ledger with commitments := c :: s.ledger.commitments }
    live := c
    payments := s.payments
    feeBucket := c.feeSat
    feeLink := rfl }

/-- Settle one HTLC output and record the settled payment.  The commitment
step is the imported `settleHTLCOutputAt`; the new commitment is appended to
the ledger and becomes the live commitment. -/
def settleHTLC (s : EndToEndState)
    (before after : List CommitmentHTLCOutput) (h : CommitmentHTLCOutput)
    (fulfilled hadOutput : Bool) (p : SettledPayment) : EndToEndState :=
  let c' := settleHTLCOutputAt s.live before after h fulfilled hadOutput
  { funding := s.funding
    fundingValue := s.fundingValue
    fundingLink := s.fundingLink
    ledger := { s.ledger with commitments := c' :: s.ledger.commitments }
    live := c'
    payments := p :: s.payments
    feeBucket := c'.feeSat
    feeLink := rfl }

@[simp] theorem replaceLive_fundingValue (s : EndToEndState) (c : Commitment) :
    (s.replaceLive c).fundingValue = s.fundingValue := rfl

@[simp] theorem replaceLive_live (s : EndToEndState) (c : Commitment) :
    (s.replaceLive c).live = c := rfl

@[simp] theorem settleHTLC_fundingValue (s : EndToEndState)
    (before after : List CommitmentHTLCOutput) (h : CommitmentHTLCOutput)
    (fulfilled hadOutput : Bool) (p : SettledPayment) :
    (s.settleHTLC before after h fulfilled hadOutput p).fundingValue =
      s.fundingValue := rfl

@[simp] theorem settleHTLC_live (s : EndToEndState)
    (before after : List CommitmentHTLCOutput) (h : CommitmentHTLCOutput)
    (fulfilled hadOutput : Bool) (p : SettledPayment) :
    (s.settleHTLC before after h fulfilled hadOutput p).live =
      settleHTLCOutputAt s.live before after h fulfilled hadOutput := rfl

/-- A conserving live-commitment replacement keeps the state funded. -/
theorem replaceLive_funded (s : EndToEndState) (hf : Funded s)
    (c : Commitment) (hc : CommitmentConserved c)
    (hfund : c.fundingValueSat = s.ledger.fundingValueSat)
    (hcov : settledTotal s.payments ≤ c.totalOutputValue) :
    Funded (s.replaceLive c) := by
  rcases hf with ⟨hmem, hall, hledger, _⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact List.mem_cons_self
  · exact ChannelLedger.allConserved_cons s.ledger c hc hfund hall
  · exact hledger
  · exact hcov

/-- **A conserved channel step preserves `TotalValue`.**  The new live
commitment is conserving and carries the same funding value, so both the old
and the new state total to the L1 funding value. -/
theorem replaceLive_preserves_totalValue (s : EndToEndState) (hf : Funded s)
    (c : Commitment) (hc : CommitmentConserved c)
    (hfund : c.fundingValueSat = s.ledger.fundingValueSat)
    (hcov : settledTotal s.payments ≤ c.totalOutputValue) :
    TotalValue (s.replaceLive c) = TotalValue s := by
  have hf' : Funded (s.replaceLive c) :=
    replaceLive_funded s hf c hc hfund hcov
  rw [totalValue_eq_funding _ hf', totalValue_eq_funding _ hf]
  rfl

/-- After settling one HTLC output and recording its payment, the settled
amounts still fit inside the new commitment's outputs.  The proof composes
`settleHTLCOutputAt_totalOutputValue` with the per-step coverage hypothesis. -/
theorem settleHTLC_covers (s : EndToEndState)
    (before after : List CommitmentHTLCOutput) (h : CommitmentHTLCOutput)
    (fulfilled hadOutput : Bool) (p : SettledPayment)
    (hmem : s.live.htlcs = before ++ h :: after)
    (hpamt : p.amountSat = h.amountSat)
    (hcover : settledTotal s.payments + h.amountSat ≤ s.live.totalOutputValue) :
    settledTotal (p :: s.payments) ≤
      (settleHTLCOutputAt s.live before after h fulfilled hadOutput).totalOutputValue := by
  rw [settleHTLCOutputAt_totalOutputValue s.live before after h fulfilled hadOutput hmem]
  rw [settledTotal_cons, hpamt]
  omega

/-- Settling an HTLC keeps the state funded.  Conservation of the new live
commitment comes from the imported `settleHTLCOutputAt_conserved`. -/
theorem settleHTLC_funded (s : EndToEndState) (hf : Funded s)
    (before after : List CommitmentHTLCOutput) (h : CommitmentHTLCOutput)
    (fulfilled hadOutput : Bool) (p : SettledPayment)
    (hmem : s.live.htlcs = before ++ h :: after)
    (hpamt : p.amountSat = h.amountSat)
    (hcover : settledTotal s.payments + h.amountSat ≤ s.live.totalOutputValue) :
    Funded (s.settleHTLC before after h fulfilled hadOutput p) := by
  rcases hf with ⟨hmemLive, hall, hledger, _⟩
  have hconsLive : CommitmentConserved s.live := (hall s.live hmemLive).2
  have hfundLive : s.live.fundingValueSat = s.ledger.fundingValueSat :=
    (hall s.live hmemLive).1
  have hcons' : CommitmentConserved
      (settleHTLCOutputAt s.live before after h fulfilled hadOutput) :=
    settleHTLCOutputAt_conserved s.live before after h fulfilled hadOutput
      hconsLive hmem
  have hfund' :
      (settleHTLCOutputAt s.live before after h fulfilled hadOutput).fundingValueSat =
        s.ledger.fundingValueSat := by
    rw [settleHTLCOutputAt_fundingValueSat]
    exact hfundLive
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact List.mem_cons_self
  · exact ChannelLedger.allConserved_cons s.ledger _ hcons' hfund' hall
  · exact hledger
  · exact settleHTLC_covers s before after h fulfilled hadOutput p hmem hpamt hcover

/-- **An HTLC settlement preserves `TotalValue`.**  The commitment step keeps
its output total (the value moves from an HTLC output to a balance), the
payment is recorded as an attributed receipt, and the fee bucket follows the
unchanged commitment fee.  The settled payment is counted exactly once. -/
theorem settleHTLC_preserves_totalValue (s : EndToEndState) (hf : Funded s)
    (before after : List CommitmentHTLCOutput) (h : CommitmentHTLCOutput)
    (fulfilled hadOutput : Bool) (p : SettledPayment)
    (hmem : s.live.htlcs = before ++ h :: after)
    (hpamt : p.amountSat = h.amountSat)
    (hcover : settledTotal s.payments + h.amountSat ≤ s.live.totalOutputValue) :
    TotalValue (s.settleHTLC before after h fulfilled hadOutput p) =
      TotalValue s := by
  have hf' : Funded (s.settleHTLC before after h fulfilled hadOutput p) :=
    settleHTLC_funded s hf before after h fulfilled hadOutput p hmem hpamt hcover
  rw [totalValue_eq_funding _ hf', totalValue_eq_funding _ hf]
  rfl

end EndToEndState

/-! ## A transition system for end-to-end runs -/

/-- One end-to-end step.  Both constructors are value-conserving channel
steps: `commitment` replaces the live commitment by any conserving commitment
with the same funding value, and `settle` performs an HTLC settlement and
records its payment.  All bridge conditions are constructor hypotheses. -/
inductive Step : EndToEndState → EndToEndState → Prop where
  | commitment (s : EndToEndState) (c : Commitment)
      (hc : CommitmentConserved c)
      (hfund : c.fundingValueSat = s.ledger.fundingValueSat)
      (hcov : settledTotal s.payments ≤ c.totalOutputValue) :
      Step s (s.replaceLive c)
  | settle (s : EndToEndState)
      (before after : List CommitmentHTLCOutput) (h : CommitmentHTLCOutput)
      (fulfilled hadOutput : Bool) (p : SettledPayment)
      (hmem : s.live.htlcs = before ++ h :: after)
      (hpamt : p.amountSat = h.amountSat)
      (hcover : settledTotal s.payments + h.amountSat ≤ s.live.totalOutputValue) :
      Step s (s.settleHTLC before after h fulfilled hadOutput p)

/-- A finite run of end-to-end steps. -/
inductive Run : EndToEndState → EndToEndState → Prop where
  | refl (s : EndToEndState) : Run s s
  | step {s t u : EndToEndState} (hst : Step s t) (htu : Run t u) : Run s u

/-- A single step keeps the state funded. -/
theorem step_funded {s t : EndToEndState} (hf : Funded s) (h : Step s t) :
    Funded t := by
  cases h with
  | commitment c hc hfund hcov =>
      exact EndToEndState.replaceLive_funded s hf c hc hfund hcov
  | settle before after hh fulfilled hadOutput p hmem hpamt hcover =>
      exact EndToEndState.settleHTLC_funded s hf before after hh fulfilled
        hadOutput p hmem hpamt hcover

/-- No step rewrites the L1 funding value. -/
theorem step_fundingValue {s t : EndToEndState} (h : Step s t) :
    t.fundingValue = s.fundingValue := by
  cases h <;> rfl

/-- **A single end-to-end step preserves `TotalValue`.**  This is the named
composition of the L1 funding link, the channel conservation equation and the
HTLC settlement lemma. -/
theorem step_preserves_totalValue {s t : EndToEndState} (hf : Funded s)
    (h : Step s t) :
    TotalValue t = TotalValue s := by
  cases h with
  | commitment c hc hfund hcov =>
      exact EndToEndState.replaceLive_preserves_totalValue s hf c hc hfund hcov
  | settle before after hh fulfilled hadOutput p hmem hpamt hcover =>
      exact EndToEndState.settleHTLC_preserves_totalValue s hf before after hh
        fulfilled hadOutput p hmem hpamt hcover

/-- Every finite run keeps the state funded. -/
theorem run_funded {s t : EndToEndState} (h : Run s t) :
    Funded s → Funded t := by
  induction h with
  | refl => exact fun hf => hf
  | step hst htu ih => exact fun hf => ih (step_funded hf hst)

/-- **Every finite run of end-to-end steps preserves `TotalValue`.** -/
theorem run_preserves_totalValue {s t : EndToEndState} (h : Run s t) :
    Funded s → TotalValue t = TotalValue s := by
  induction h with
  | refl => exact fun _ => rfl
  | step hst htu ih =>
      exact fun hf =>
        Eq.trans (ih (step_funded hf hst)) (step_preserves_totalValue hf hst)

/-- **No sequence of steps creates value.**  Starting from a funded state,
every reachable state's total value is exactly the original L1 funding value. -/
theorem run_totalValue_eq_funding {s t : EndToEndState} (h : Run s t)
    (hf : Funded s) :
    TotalValue t = s.fundingValue := by
  rw [run_preserves_totalValue h hf, totalValue_eq_funding s hf]

/-- The inequality form of `run_totalValue_eq_funding`. -/
theorem run_no_value_creation {s t : EndToEndState} (h : Run s t)
    (hf : Funded s) :
    TotalValue t ≤ s.fundingValue :=
  Nat.le_of_eq (run_totalValue_eq_funding h hf)

/-! ## A checked concrete instance (non-vacuity) -/

/-- A settled payment with a successful session. -/
def demoSettledPayment : SettledPayment :=
  { session :=
      { paymentHash := ⟨ByteArray.empty⟩
        target := ⟨1000⟩
        parts := []
        state := .succeeded }
    amountSat := 1000
    fulfilled := true
    settled := rfl }

/-- A 100000-satoshi zero-HTLC commitment with a 1000-satoshi fee. -/
def demoCommitment : Commitment :=
  { holder := .local
    commitmentNumber := 0
    fundingValueSat := 100000
    toLocalSat := 60000
    toRemoteSat := 39000
    htlcs := []
    feeSat := 1000
    contestDelay := 144
    anchorOutputs := false }

/-- Demo L1 funding output carrying 100000 satoshis. -/
def demoFunding : LnLean.Bitcoin.FundingOutput :=
  { outpoint := LnLean.Bitcoin.fundingOutpoint ByteArray.empty 0
    value := 100000
    witnessScriptHash := ByteArray.empty }

/-- A concrete funded end-to-end state.  The live commitment's outputs plus
fee equal the L1 funding value; the settled payment fits in its outputs. -/
def demoState : EndToEndState :=
  { funding := demoFunding
    fundingValue := 100000
    fundingLink := rfl
    ledger := { fundingValueSat := 100000, commitments := [demoCommitment] }
    live := demoCommitment
    payments := [demoSettledPayment]
    feeBucket := 1000
    feeLink := rfl }

theorem demoState_funded : Funded demoState := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [demoState]
  · intro c hc
    simp [demoState] at hc
    subst hc
    exact ⟨rfl, by unfold CommitmentConserved; decide⟩
  · rfl
  · decide

/-- The concrete state's total value is its L1 funding value. -/
theorem demoState_totalValue : TotalValue demoState = 100000 := by
  rw [totalValue_eq_funding demoState demoState_funded]
  rfl

end LnLean.Proofs.PhaseC3

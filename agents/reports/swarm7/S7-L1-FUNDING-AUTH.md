# S7-L1-FUNDING-AUTH — `open_channel` coverage and funding-key authentication (`L1-03`)

- Lane: `S7-L1-FUNDING-AUTH` (issue `L1-03`)
- Worktree: `/home/ubuntu/ln-lean-repair` (branch `repair/integrated`)
- Owned files:
  - `LnLean/Bitcoin/Funding.lean` (consulted; **no edit needed**)
  - `LnLean/Protocol/Handshake.lean` (additive `OpenChannel`, `FundingPhase`,
    `fundingStep`, and key-provenance theorems)
  - new `LnLean/Proofs/Bitcoin/FundingAuthTargets.lean`
  - `agents/reports/swarm7/S7-L1-FUNDING-AUTH.md` (this report)

Read-only files consulted: `docs/OPEN-ISSUES.md`, `agents/swarm/WAVE-7.md`,
`docs/ASSUMPTIONS.md`, `agents/reports/swarm5/S5-L1-FUNDING.md`,
`LnLean/Protocol/Messages.lean`, `LnLean/Bitcoin/Funding.lean`,
`LnLean/Proofs/Bitcoin/FundingLinkTargets.lean`,
`LnLean/Proofs/Bitcoin/FundingScriptTargets.lean`,
`LnLean/Proofs/Bitcoin/FundingProps.lean`, `LnLean/Crypto/Model.lean`,
`LnLean/Basic/Core.lean`.

## 1. Result

`L1-03` is **mitigated at the funding-construction layer, not fully closed at
the wire layer**.  The lane delivers the strongest faithful statement that does
not assume a signature/secret-key model it does not have:

1. **`open_channel` coverage is added additively.**  `Handshake.lean` now has
   an `OpenChannel` record carrying the funding-relevant BOLT 2 fields
   (`temporary_channel_id`, `funding_satoshis`, `push_msat`,
   `funding_pubkey`), the joint constructor
   `OpenChannel.toFundingNegotiation`, and a separate
   `FundingPhase`/`fundingStep` machine for the four funding-negotiation
   messages with BOLT 2 ordering guards.  `HandshakeState`, `HandshakeEvent`,
   and `handshakeStep` are untouched, so downstream exhaustive matches and the
   ten-milestone v1 laws still build.
2. **The existing hash link is not weakened.**  The joint construction is
   definitionally the old accept-only construction:
   `o.toFundingNegotiation a =
   a.toFundingNegotiation o.fundingPubKey o.fundingSatoshis o.pushMsat
   ⟨o.temporaryChannelId⟩`.
   Every `FundingLinkTargets` theorem applies unchanged; the output remains
   the ordered BOLT 3 P2WSH construction.
3. **Funding-key authentication is proved as output binding.**  If two complete
   `open_channel`/`accept_channel` exchanges produce the same funding output,
   and `H` is collision-free on the two 71-byte witness scripts, then the two
   exchanges agreed on the **unordered funding-key set**.  A substitution of
   either key is therefore detectable by checking the output against the
   derived one.  This is the operational meaning of authentication available
   without a signature model.
4. **Peer identity remains an explicit transport hypothesis.**  `OpenChannel`
   carries no sender field, and `same_message_distinct_senders` mechanizes
   that.  `attributed_key_in_script` proves the conditional result: *if* the
   transport attributes the message to a peer key, that key is the local
   funding key of the script and occurs in its bytes.
5. **Limits are mechanized, not hidden.**  The funding output ignores
   `funding_satoshis`, `push_msat`, and the temporary channel id
   (`funding_output_ignores_*`), and neither `accept_channel` alone
   (`acceptChannel_alone_does_not_determine_witnessScript`, retained from
   `FundingLinkTargets`) nor `open_channel` alone
   (`openChannel_alone_does_not_determine_witnessScript`) determines the
   witness script.
6. **The finite C1 admission is retained.**  Reverse binding uses exactly
   `CollisionFreeOn H x y := H x = H y → x = y` at the two constructed
   scripts.  No global SHA-256 injectivity and no derivation from the 32-byte
   C1 domain is assumed; `c1_32_does_not_bind_funding_witnessScripts`
   remains the binding counterexample.

The one thing this lane deliberately did **not** do is add `open_channel` to
`Msg`/`MsgKind` in `LnLean/Protocol/Messages.lean`, because that file is
outside the lane's write set.  The exact integration patch is in §7.  Until
the parent applies it (and the corresponding `Handshake.lean` structure move),
`L1-03` should remain `open (mitigated)`, not `closed`.

## 2. Required build

Command run exactly as specified, under the shared lock:

```sh
cd /home/ubuntu/ln-lean-repair
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Bitcoin.Funding \
    LnLean.Protocol.Handshake \
    LnLean.Proofs.Bitcoin.FundingAuthTargets \
    LnLean.Proofs.Bitcoin.FundingLinkTargets
```

Observed final output:

```text
✔ [17/17] Built LnLean.Proofs.Bitcoin.FundingAuthTargets (851ms)
Build completed successfully (17 jobs).
```

**Build RC: 0.**  No warnings from the owned files.  No full `lake build`,
`collect-obligations.py`, `collect-anchors.py`, or Git write was run.  No
`LnLean/Bitcoin/Funding.lean` change was required; it still builds as the
first target.

An earlier intermediate build of `LnLean.Protocol.Handshake` alone also
succeeded (`✔ [12/12] ... Build completed successfully (12 jobs).`).

## 3. Exact signatures

### 3.1 `LnLean/Protocol/Handshake.lean` (owned additions)

All additions are after the existing declarations and before
`end LnLean.Protocol`; no existing declaration was edited.

```lean
/-- Funding-relevant projection of BOLT 2 `open_channel` (type 32). -/
structure OpenChannel where
  temporaryChannelId : ChannelId
  fundingSatoshis : BtcAmount
  pushMsat : Msat
  fundingPubKey : PubKey
deriving Repr, BEq

namespace OpenChannel

def toFundingNegotiation (o : OpenChannel) (a : AcceptChannel) :
    LnLean.Bitcoin.FundingNegotiation

def toFundingParams (H : ByteArray → ByteArray) (o : OpenChannel)
    (a : AcceptChannel) : LnLean.Bitcoin.FundingParams

@[simp] theorem toFundingNegotiation_localFundingKey (o : OpenChannel)
    (a : AcceptChannel) :
    (o.toFundingNegotiation a).localFundingKey = o.fundingPubKey

@[simp] theorem toFundingNegotiation_remoteFundingKey (o : OpenChannel)
    (a : AcceptChannel) :
    (o.toFundingNegotiation a).remoteFundingKey = a.fundingPubKey

@[simp] theorem toFundingNegotiation_fundingSatoshis (o : OpenChannel)
    (a : AcceptChannel) :
    (o.toFundingNegotiation a).fundingSatoshis = o.fundingSatoshis

@[simp] theorem toFundingNegotiation_pushMsat (o : OpenChannel)
    (a : AcceptChannel) :
    (o.toFundingNegotiation a).pushMsat = o.pushMsat

@[simp] theorem toFundingNegotiation_temporaryChannelId (o : OpenChannel)
    (a : AcceptChannel) :
    (o.toFundingNegotiation a).temporaryChannelId = ⟨o.temporaryChannelId⟩

theorem toFundingNegotiation_eq_acceptChannel (o : OpenChannel)
    (a : AcceptChannel) :
    o.toFundingNegotiation a =
      a.toFundingNegotiation o.fundingPubKey o.fundingSatoshis o.pushMsat
        ⟨o.temporaryChannelId⟩

theorem toFundingParams_witnessScriptHash (H : ByteArray → ByteArray)
    (o : OpenChannel) (a : AcceptChannel) :
    (o.toFundingParams H a).witnessScriptHash =
      H (o.toFundingParams H a).witnessScript.bytes

theorem toFundingParams_fundingScriptPubKey (H : ByteArray → ByteArray)
    (o : OpenChannel) (a : AcceptChannel) :
    (o.toFundingParams H a).fundingScriptPubKey =
      p2wsh (H (o.toFundingParams H a).witnessScript.bytes)

end OpenChannel

structure FundingPhase where
  openSent : Option OpenChannel := none
  openReceived : Option OpenChannel := none
  acceptSent : Option AcceptChannel := none
  acceptReceived : Option AcceptChannel := none
deriving Repr, BEq

namespace FundingPhase

def initial : FundingPhase
def canSendOpen (s : FundingPhase) : Bool
def canRecvOpen (s : FundingPhase) : Bool
def canSendAccept (s : FundingPhase) : Bool
def canRecvAccept (s : FundingPhase) : Bool
def openerNegotiation? (s : FundingPhase) :
    Option LnLean.Bitcoin.FundingNegotiation
def acceptorNegotiation? (s : FundingPhase) :
    Option LnLean.Bitcoin.FundingNegotiation

@[simp] theorem openerNegotiation?_initial :
    initial.openerNegotiation? = none

@[simp] theorem acceptorNegotiation?_initial :
    initial.acceptorNegotiation? = none

end FundingPhase

inductive FundingPhaseEvent where
  | sendOpen (o : OpenChannel)
  | recvOpen (o : OpenChannel)
  | sendAccept (a : AcceptChannel)
  | recvAccept (a : AcceptChannel)
deriving Repr

def fundingStep (s : FundingPhase) : FundingPhaseEvent → Option FundingPhase

inductive FundingReachable : FundingPhase → Prop where
  | initial : FundingReachable FundingPhase.initial
  | step {s s' : FundingPhase} (e : FundingPhaseEvent) :
      FundingReachable s → fundingStep s e = some s' → FundingReachable s'

theorem sendAccept_requires_openReceived {s s' : FundingPhase}
    {a : AcceptChannel} (h : fundingStep s (.sendAccept a) = some s') :
    ∃ o : OpenChannel, s.openReceived = some o

theorem recvAccept_requires_openSent {s s' : FundingPhase}
    {a : AcceptChannel} (h : fundingStep s (.recvAccept a) = some s') :
    ∃ o : OpenChannel, s.openSent = some o

theorem fundingPhase_opener_keys {s : FundingPhase}
    {n : LnLean.Bitcoin.FundingNegotiation}
    (h : s.openerNegotiation? = some n) :
    ∃ (o : OpenChannel) (a : AcceptChannel),
      s.openSent = some o ∧ s.acceptReceived = some a ∧
      n = o.toFundingNegotiation a ∧
      n.localFundingKey = o.fundingPubKey ∧
      n.remoteFundingKey = a.fundingPubKey

theorem fundingPhase_acceptor_keys {s : FundingPhase}
    {n : LnLean.Bitcoin.FundingNegotiation}
    (h : s.acceptorNegotiation? = some n) :
    ∃ (o : OpenChannel) (a : AcceptChannel),
      s.openReceived = some o ∧ s.acceptSent = some a ∧
      n = o.toFundingNegotiation a ∧
      n.localFundingKey = o.fundingPubKey ∧
      n.remoteFundingKey = a.fundingPubKey

theorem acceptKey_bound_before_fundingCreated {s s' : HandshakeState}
    (h : handshakeStep s .sendFundingCreated = some s')
    (o : OpenChannel) (a : AcceptChannel) (H : ByteArray → ByteArray) :
    s.acceptReceived = true ∧
      ((o.toFundingNegotiation a).toFundingParams H).remoteFundingKey =
        a.fundingPubKey

theorem fundingReachable_negotiation_witness :
    ∃ s : FundingPhase,
      FundingReachable s ∧
      s.openerNegotiation?.isSome = true ∧
      s.acceptorNegotiation?.isSome = true
```

### 3.2 `LnLean/Proofs/Bitcoin/FundingAuthTargets.lean`

Namespace: `LnLean.Proofs.Bitcoin.FundingAuthTargets`.  Opens
`FundingScriptTargets` and `FundingLinkTargets`.

```lean
theorem twoOfTwoScriptBytes_injective {a b c d : PubKey}
    (ha : a.bytes.size = 33) (hb : b.bytes.size = 33)
    (hc : c.bytes.size = 33) (hd : d.bytes.size = 33)
    (h : TwoOfTwoScriptBytes a b = TwoOfTwoScriptBytes c d) :
    a = c ∧ b = d

theorem key_mem_ordered (k l : PubKey) :
    k = (orderedFundingKeys k l).1 ∨ k = (orderedFundingKeys k l).2

theorem key_set_eq_of_ordered_eq {o₁ a₁ o₂ a₂ : PubKey}
    (h : orderedFundingKeys o₁ a₁ = orderedFundingKeys o₂ a₂) :
    (o₁ = o₂ ∧ a₁ = a₂) ∨ (o₁ = a₂ ∧ a₁ = o₂)

def KeyInScript (s : ByteArray) (k : PubKey) : Prop :=
  ∃ pre post : ByteArray, s = pre ++ k.bytes ++ post

theorem twoOfTwoScriptBytes_keyInScript_first (a b : PubKey) :
    KeyInScript (TwoOfTwoScriptBytes a b) a

theorem twoOfTwoScriptBytes_keyInScript_second (a b : PubKey) :
    KeyInScript (TwoOfTwoScriptBytes a b) b

theorem openAccept_both_keys_in_script (H : ByteArray → ByteArray)
    (o : OpenChannel) (a : AcceptChannel) :
    KeyInScript (o.toFundingParams H a).witnessScript.bytes o.fundingPubKey ∧
      KeyInScript (o.toFundingParams H a).witnessScript.bytes a.fundingPubKey

theorem openAccept_toFundingParams_eq_acceptChannel
    (H : ByteArray → ByteArray) (o : OpenChannel) (a : AcceptChannel) :
    o.toFundingParams H a =
      a.toFundingParams H o.fundingPubKey o.fundingSatoshis o.pushMsat
        ⟨o.temporaryChannelId⟩

theorem openAccept_hash_linked (H : ByteArray → ByteArray)
    (o : OpenChannel) (a : AcceptChannel) :
    FundingScriptHashLinked H (o.toFundingParams H a)

theorem openAccept_fundingScriptPubKey_eq_p2wsh_ordered
    (H : ByteArray → ByteArray) (o : OpenChannel) (a : AcceptChannel) :
    (o.toFundingParams H a).fundingScriptPubKey =
      p2wsh (H (TwoOfTwoScriptBytes (o.toFundingNegotiation a).firstFundingKey
        (o.toFundingNegotiation a).secondFundingKey))

theorem openAccept_witnessScriptHash_eq_hash_TwoOfTwo
    (H : ByteArray → ByteArray) (o : OpenChannel) (a : AcceptChannel) :
    (o.toFundingParams H a).witnessScriptHash =
      H (TwoOfTwoScriptBytes (o.toFundingNegotiation a).firstFundingKey
        (o.toFundingNegotiation a).secondFundingKey)

theorem openAccept_hash_linked_sha256 (M : PrimitiveModel)
    (o : OpenChannel) (a : AcceptChannel) :
    FundingScriptHashLinked M.sha256 (o.toFundingParams M.sha256 a) ∧
      (o.toFundingParams M.sha256 a).witnessScriptHash.size = 32

theorem openAccept_wellFormed (H : ByteArray → ByteArray)
    (hH : ∀ b : ByteArray, (H b).size = 32) (o : OpenChannel)
    (a : AcceptChannel)
    (hsat0 : 0 ≤ o.fundingSatoshis)
    (hsatMax : o.fundingSatoshis ≤ Bitcoin.Data.MAX_MONEY)
    (hlocal : o.fundingPubKey.Valid)
    (hremote : a.fundingPubKey.Valid)
    (hpush : (o.pushMsat.val : Int) ≤
      o.fundingSatoshis * (Msat.MSAT_PER_SAT : Int)) :
    (o.toFundingParams H a).WellFormed

theorem openAccept_output_determines_ordered_keys
    (H : ByteArray → ByteArray)
    (o₁ : OpenChannel) (a₁ : AcceptChannel)
    (o₂ : OpenChannel) (a₂ : AcceptChannel)
    (hwf₁ : (o₁.toFundingParams H a₁).WellFormed)
    (hwf₂ : (o₂.toFundingParams H a₂).WellFormed)
    (heq : (o₁.toFundingParams H a₁).fundingScriptPubKey =
      (o₂.toFundingParams H a₂).fundingScriptPubKey)
    (hc1 : CollisionFreeOn H
      (o₁.toFundingParams H a₁).witnessScript.bytes
      (o₂.toFundingParams H a₂).witnessScript.bytes) :
    orderedFundingKeys o₁.fundingPubKey a₁.fundingPubKey =
      orderedFundingKeys o₂.fundingPubKey a₂.fundingPubKey

theorem openAccept_output_determines_key_set
    (H : ByteArray → ByteArray)
    (o₁ : OpenChannel) (a₁ : AcceptChannel)
    (o₂ : OpenChannel) (a₂ : AcceptChannel)
    (hwf₁ : (o₁.toFundingParams H a₁).WellFormed)
    (hwf₂ : (o₂.toFundingParams H a₂).WellFormed)
    (heq : (o₁.toFundingParams H a₁).fundingScriptPubKey =
      (o₂.toFundingParams H a₂).fundingScriptPubKey)
    (hc1 : CollisionFreeOn H
      (o₁.toFundingParams H a₁).witnessScript.bytes
      (o₂.toFundingParams H a₂).witnessScript.bytes) :
    (o₁.fundingPubKey = o₂.fundingPubKey ∧
        a₁.fundingPubKey = a₂.fundingPubKey) ∨
      (o₁.fundingPubKey = a₂.fundingPubKey ∧
        a₁.fundingPubKey = o₂.fundingPubKey)

theorem openAccept_output_determines_key_set_sha256 (M : PrimitiveModel)
    (o₁ : OpenChannel) (a₁ : AcceptChannel)
    (o₂ : OpenChannel) (a₂ : AcceptChannel)
    (hwf₁ : (o₁.toFundingParams M.sha256 a₁).WellFormed)
    (hwf₂ : (o₂.toFundingParams M.sha256 a₂).WellFormed)
    (heq : (o₁.toFundingParams M.sha256 a₁).fundingScriptPubKey =
      (o₂.toFundingParams M.sha256 a₂).fundingScriptPubKey)
    (hc1 : CollisionFreeOn M.sha256
      (o₁.toFundingParams M.sha256 a₁).witnessScript.bytes
      (o₂.toFundingParams M.sha256 a₂).witnessScript.bytes) :
    (o₁.fundingPubKey = o₂.fundingPubKey ∧
        a₁.fundingPubKey = a₂.fundingPubKey) ∨
      (o₁.fundingPubKey = a₂.fundingPubKey ∧
        a₁.fundingPubKey = o₂.fundingPubKey)

structure PeerIdentity where
  key : PubKey

structure ReceivedOpen where
  sender : PeerIdentity
  message : OpenChannel

def OpenChannelAttributed (sender : PeerIdentity) (o : OpenChannel) : Prop :=
  sender.key = o.fundingPubKey

theorem attributed_key_in_script (H : ByteArray → ByteArray)
    (sender : PeerIdentity) (o : OpenChannel) (a : AcceptChannel)
    (hattr : OpenChannelAttributed sender o) :
    sender.key = (o.toFundingNegotiation a).localFundingKey ∧
      KeyInScript (o.toFundingParams H a).witnessScript.bytes sender.key

theorem attributed_key_committed (H : ByteArray → ByteArray)
    (sender : PeerIdentity) (o : OpenChannel) (a : AcceptChannel)
    (hattr : OpenChannelAttributed sender o) :
    (o.toFundingParams H a).fundingScriptPubKey =
        p2wsh (H (o.toFundingParams H a).witnessScript.bytes) ∧
      KeyInScript (o.toFundingParams H a).witnessScript.bytes sender.key

theorem same_message_distinct_senders :
    ∃ r₁ r₂ : ReceivedOpen,
      r₁.message = r₂.message ∧ r₁.sender ≠ r₂.sender

theorem firstFundingKey_size {n : LnLean.Bitcoin.FundingNegotiation}
    (hl : n.localFundingKey.bytes.size = 33)
    (hr : n.remoteFundingKey.bytes.size = 33) :
    n.firstFundingKey.bytes.size = 33

theorem secondFundingKey_size {n : LnLean.Bitcoin.FundingNegotiation}
    (hl : n.localFundingKey.bytes.size = 33)
    (hr : n.remoteFundingKey.bytes.size = 33) :
    n.secondFundingKey.bytes.size = 33

theorem funding_output_ignores_fundingSatoshis
    (H : ByteArray → ByteArray) (o : OpenChannel) (a : AcceptChannel)
    (v : BtcAmount) :
    (({ o with fundingSatoshis := v }).toFundingParams H a).fundingScriptPubKey =
      (o.toFundingParams H a).fundingScriptPubKey

theorem funding_output_ignores_pushMsat
    (H : ByteArray → ByteArray) (o : OpenChannel) (a : AcceptChannel)
    (p : Msat) :
    (({ o with pushMsat := p }).toFundingParams H a).fundingScriptPubKey =
      (o.toFundingParams H a).fundingScriptPubKey

theorem funding_output_ignores_temporaryChannelId
    (H : ByteArray → ByteArray) (o : OpenChannel) (a : AcceptChannel)
    (c : ChannelId) :
    (({ o with temporaryChannelId := c }).toFundingParams H a).fundingScriptPubKey =
      (o.toFundingParams H a).fundingScriptPubKey

theorem openAccept_forward_satisfiable :
    ∃ (H : ByteArray → ByteArray) (o : OpenChannel) (a : AcceptChannel),
      (∀ b : ByteArray, (H b).size = 32) ∧
      (o.toFundingParams H a).WellFormed ∧
      FundingScriptHashLinked H (o.toFundingParams H a)

theorem openChannel_alone_does_not_determine_witnessScript :
    ∃ (o : OpenChannel) (a₁ a₂ : AcceptChannel),
      (o.toFundingParams (fun b => b) a₁).witnessScript.bytes ≠
        (o.toFundingParams (fun b => b) a₂).witnessScript.bytes

theorem fundingPhase_opener_negotiation_bound
    (H : ByteArray → ByteArray) {s : FundingPhase}
    {n : LnLean.Bitcoin.FundingNegotiation}
    (h : s.openerNegotiation? = some n) :
    ∃ (o : OpenChannel) (a : AcceptChannel),
      s.openSent = some o ∧ s.acceptReceived = some a ∧
      n = o.toFundingNegotiation a ∧
      n.localFundingKey = o.fundingPubKey ∧
      n.remoteFundingKey = a.fundingPubKey ∧
      KeyInScript (n.toFundingParams H).witnessScript.bytes o.fundingPubKey ∧
      KeyInScript (n.toFundingParams H).witnessScript.bytes a.fundingPubKey

theorem fundingPhase_acceptor_negotiation_bound
    (H : ByteArray → ByteArray) {s : FundingPhase}
    {n : LnLean.Bitcoin.FundingNegotiation}
    (h : s.acceptorNegotiation? = some n) :
    ∃ (o : OpenChannel) (a : AcceptChannel),
      s.openReceived = some o ∧ s.acceptSent = some a ∧
      n = o.toFundingNegotiation a ∧
      n.localFundingKey = o.fundingPubKey ∧
      n.remoteFundingKey = a.fundingPubKey ∧
      KeyInScript (n.toFundingParams H).witnessScript.bytes o.fundingPubKey ∧
      KeyInScript (n.toFundingParams H).witnessScript.bytes a.fundingPubKey

theorem opener_acceptor_negotiation_agree
    (sOpener sAcceptor : FundingPhase) (o : OpenChannel) (a : AcceptChannel)
    (hso : sOpener.openSent = some o) (har : sOpener.acceptReceived = some a)
    (hro : sAcceptor.openReceived = some o) (has : sAcceptor.acceptSent = some a) :
    sOpener.openerNegotiation? = sAcceptor.acceptorNegotiation?
```

Retained results cited unchanged:

```lean
-- LnLean/Proofs/Bitcoin/FundingLinkTargets.lean
theorem acceptChannel_alone_does_not_determine_witnessScript : ...

-- LnLean/Proofs/Bitcoin/FundingScriptTargets.lean
theorem c1_32_does_not_bind_funding_witnessScripts : ...
def CollisionFreeOn (H : ByteArray → ByteArray) (x y : ByteArray) : Prop :=
  H x = H y → x = y
```

## 4. Axiom audit

Scratch file `/tmp/opencode/Axioms.lean` (not committed) ran `#print axioms`
on every new headline result.  Selected output:

```text
twoOfTwoScriptBytes_injective:                  [propext, Quot.sound]
openAccept_both_keys_in_script:                 [propext, Quot.sound]
openAccept_toFundingParams_eq_acceptChannel:    [propext]
openAccept_hash_linked:                         [propext]
openAccept_fundingScriptPubKey_eq_p2wsh_ordered:[propext]
openAccept_wellFormed:                          [propext]
openAccept_output_determines_ordered_keys:      [propext, Quot.sound]
openAccept_output_determines_key_set:           [propext, Quot.sound]
openAccept_output_determines_key_set_sha256:    [propext, Quot.sound]
attributed_key_in_script:                       [propext, Quot.sound]
attributed_key_committed:                       [propext, Quot.sound]
same_message_distinct_senders:                  [propext]
funding_output_ignores_fundingSatoshis:         [propext]
funding_output_ignores_pushMsat:                [propext]
funding_output_ignores_temporaryChannelId:      [propext]
openAccept_forward_satisfiable:                 [propext, Classical.choice, Quot.sound]
openChannel_alone_does_not_determine_witnessScript:
                                                [propext, Quot.sound]
fundingPhase_opener_negotiation_bound:          [propext, Quot.sound]
fundingPhase_acceptor_negotiation_bound:        [propext, Quot.sound]
opener_acceptor_negotiation_agree:              [propext]
sendAccept_requires_openReceived:               [propext, Quot.sound]
recvAccept_requires_openSent:                   [propext, Quot.sound]
fundingPhase_opener_keys:                       [propext]
fundingPhase_acceptor_keys:                     [propext]
acceptKey_bound_before_fundingCreated:          [propext]
fundingReachable_negotiation_witness:           [propext]
OpenChannel.toFundingNegotiation_eq_acceptChannel: no axioms
OpenChannel.toFundingNegotiation:               no axioms
fundingStep:                                    no axioms
```

Every set is a subset of the allowed
`{propext, Quot.sound, Classical.choice}`.  No `sorryAx`, user axiom,
`native_decide`, `unsafe`, or `@[implemented_by]` occurs.

## 5. Forbidden-construct scan

```sh
cd /home/ubuntu/ln-lean-repair
grep -nE '\b(sorry|axiom|admit|native_decide|unsafe|implemented_by)\b' \
  LnLean/Bitcoin/Funding.lean \
  LnLean/Protocol/Handshake.lean \
  LnLean/Proofs/Bitcoin/FundingAuthTargets.lean
```

Observed output:

```text
NO_FORBIDDEN_TOKENS
```

## 6. Scope caveats

- **No signature or secret-key check.**  The construction does not contain an
  ECDSA verification or a secret-key model.  `attributed_key_in_script` takes
  peer attribution as an explicit hypothesis, and `same_message_distinct_senders`
  shows one `OpenChannel` record can be paired with two distinct sender
  identities.  Binding a key to a signer is `PR-01`/C3, not `L1-03`.
- **Authentication is key-set binding, not role binding.**  The strongest
  conclusion from output equality is the *unordered* set
  `{o.fundingPubKey, a.fundingPubKey}`.  Whether opener and acceptor kept
  their roles is not determined by the output; `key_set_eq_of_ordered_eq`
  states the two possibilities explicitly.  Role/ordering is separately
  available from the messages (`n.localFundingKey`, `n.remoteFundingKey`) and
  from `fundingPhase_opener_keys`/`fundingPhase_acceptor_keys`.
- **The finite C1 admission is still a hypothesis.**  Equal outputs determine
  equal witness scripts only under `CollisionFreeOn H` at the two constructed
  scripts.  No global or 71-byte injectivity is claimed; C1 on the 32-byte
  payment-preimage domain is not sufficient
  (`c1_32_does_not_bind_funding_witnessScripts`).
- **The output commits only to the keys.**  `funding_output_ignores_*` shows
  capacity, push amount, and temporary channel id are not bound by the P2WSH
  script.  They must be authenticated by the messages/transport or by the
  funding transaction.  This is a limit, not a defect of the construction.
- **`OpenChannel` here is a funding-relevant projection, not the wire record.**
  It omits `chain_hash`, dust/feerate/basepoint fields, `channel_flags`, and
  `shutdown_scriptpubkey`.  Full `Msg` coverage is the §7 patch, which this
  lane did not apply because `Messages.lean` is outside its write set.
- **`handshakeStep` does not gain an `open_channel` event.**  The separate
  `FundingPhase` machine models the four funding messages without changing the
  existing ten-milestone state.  `Msg.openChannel` (once added) would map to
  `none` in `Peer.sendEvent?`/`receiveEvent?` unless a new handshake event is
  added; that is a deliberate, separate API change.
- **No consensus/script-execution claim.**  The module proves construction,
  serialization, and key occurrence; it does not execute the witness script,
  verify signatures, or claim on-chain validity.
- **No full-tree build.**  Only the four required modules were built, as
  instructed.

## 7. Exact integration patch (`Messages.lean` + root import)

Not applied.  The patch is additive except for the `OpenChannel` structure
move; it is written against the current `Messages.lean` shape.  `msgLength`
uses **313** because the wire record omits `chain_hash` (32 bytes; a
connection/network parameter) and assumes the standard 34-byte
`shutdown_scriptpubkey`.  A BOLT 2 wire `open_channel` including `chain_hash`
is 345 bytes; adjust `msgLength` and add the field if the model wants the full
serialization.

### 7.1 `LnLean/Protocol/Messages.lean`

```lean
-- 1. No new import is required: `LnLean.Channel.Types` already imports
--    `LnLean.Bitcoin.Seam`, which defines `BtcAmount`.  Use the qualified
--    name, or add `open LnLean.Bitcoin` next to the existing `open LnLean`.

-- 2. Add the wire record before `AcceptChannel`.
/-- BOLT 2 `open_channel` (type 32).  `chain_hash` is omitted: it is a
network-wide value fixed by the transport, and this model has no chain-hash
field on any other message.  `shutdown_scriptpubkey` is the standard 34-byte
witness program assumed by `msgLength`. -/
structure OpenChannel where
  temporaryChannelId : ChannelId
  fundingSatoshis : LnLean.Bitcoin.BtcAmount
  pushMsat : Msat
  dustLimitSatoshis : Nat
  maxHtlcValueInFlightMsat : Nat
  htlcMinimumMsat : Nat
  feeratePerKw : Nat
  toSelfDelay : Nat
  maxAcceptedHtlcs : Nat
  fundingPubKey : PubKey
  revocationBasepoint : PubKey
  paymentBasepoint : PubKey
  delayedPaymentBasepoint : PubKey
  htlcBasepoint : PubKey
  firstPerCommitmentPoint : PubKey
  channelFlags : UInt8
  shutdownScriptpubkey : ByteArray
deriving Repr, BEq

-- 3. Add the constructor to `Msg` and `MsgKind`, immediately after `init`.
inductive Msg where
  | init (m : InitMsg)
  | openChannel (m : OpenChannel)      -- new, type 32
  | acceptChannel (m : AcceptChannel)
  ...

inductive MsgKind where
  | init
  | openChannel                        -- new
  | acceptChannel
  ...

-- 4. `Msg.kind`.
def kind : Msg → MsgKind
  | .init _ => .init
  | .openChannel _ => .openChannel     -- new
  | .acceptChannel _ => .acceptChannel
  ...

-- 5. `wireType`.
def wireType : MsgKind → Nat
  | .init => 16
  | .openChannel => 32                 -- new
  | .acceptChannel => 33
  ...

-- 6. `kindOfType?`.
def kindOfType? : Nat → Option MsgKind
  | 1 => some .warning
  | 16 => some .init
  | 17 => some .error
  | 18 => some .ping
  | 19 => some .pong
  | 32 => some .openChannel            -- new
  | 33 => some .acceptChannel
  ...

-- 7. `msgLength`: 32+8+8+8+8+8+4+2+2+6*33+1+34 = 313.
def msgLength : Msg → Nat
  | .init m => 4 + m.globalfeatures.size + m.features.size
  | .openChannel _ => 313              -- new
  | .acceptChannel _ => 270
  ...

-- 8. `channelId?`.
def channelId? : Msg → Option ChannelId
  | .init _ => none
  | .openChannel m => some m.temporaryChannelId   -- new
  | .acceptChannel m => some m.temporaryChannelId
  ...

-- 9. `pubKeys`.
def pubKeys : Msg → List PubKey
  | .openChannel m =>                  -- new
      [m.fundingPubKey, m.revocationBasepoint, m.paymentBasepoint,
       m.delayedPaymentBasepoint, m.htlcBasepoint, m.firstPerCommitmentPoint]
  | .acceptChannel m => ...
  ...

-- `signatures`, `semanticOk`, and `sigsValid` already have `| _ => ...`
-- defaults and need no case.
```

### 7.2 `LnLean/Protocol/Handshake.lean`

After §7.1, delete the local `structure OpenChannel ... deriving Repr, BEq`
(lines 517–526) and keep the `namespace OpenChannel` block.  The field names
(`temporaryChannelId`, `fundingSatoshis`, `pushMsat`, `fundingPubKey`) are
identical in the wire record, so all existing definitions and proofs remain
valid unchanged.  Do not duplicate the structure in both modules.

### 7.3 Root import

`LnLean.lean`, after line 29 (`FundingLinkTargets`):

```lean
import LnLean.Proofs.Bitcoin.FundingAuthTargets
```

### 7.4 Downstream files that must be rebuilt/reviewed

- `LnLean/Protocol/Laws.lean`: `wireType_injective`, `msgType_lt_65536`,
  `msgType_ne_zero`, `kindOfType?_msgType`, `msgLength_pos` all use
  `cases m <;> ...`; they should remain provable once `wireType` and
  `kindOfType?` have the type-32 case.  `msgLength_pos` needs the `313`
  branch, which `omega` discharges.
- `LnLean/Protocol/Peer.lean`: `sendEvent?`/`receiveEvent?` already end in
  `| _ => none`, so `open_channel` compiles but is not routed to the
  handshake.  Wiring it requires a new `HandshakeEvent`/guard, which would
  change `HandshakeState`/`handshakeStep`; that is deliberately out of this
  lane.
- Any aggregate obligation/traceability/axiom lists are parent-owned and were
  not edited.

## 8. Integration steps (parent only)

1. Apply §7.1 and §7.2 together; then add the §7.3 root import.
2. Rebuild `LnLean.Protocol.Messages`, `LnLean.Protocol.Handshake`,
   `LnLean.Protocol.Laws`, `LnLean.Protocol.Peer`,
   `LnLean.Proofs.Bitcoin.FundingAuthTargets`, and the root aggregate under
   the shared lock.
3. Register the `L1-03` targets in the parent-owned
   `LnLean/Proofs/Obligations.lean`, `Traceability.lean`, and
   `PhaseC3/AxiomAudit.lean`.  Suggested strings:
   `LnLean.Proofs.Bitcoin.FundingAuthTargets.openAccept_output_determines_key_set;
    LnLean.Proofs.Bitcoin.FundingAuthTargets.attributed_key_in_script;
    LnLean.Proofs.Bitcoin.FundingAuthTargets.openAccept_both_keys_in_script;
    LnLean.Protocol.fundingPhase_opener_keys`.
4. Update `docs/OPEN-ISSUES.md` `L1-03`: keep `open (mitigated)` until §7.1–
   §7.3 are applied, then state that `open_channel` is a `Msg` constructor and
   that output binding is the authentication result.  Do **not** describe the
   result as peer authentication: it is key-set binding plus optional
   transport attribution.
5. Keep `L1-05` unchanged: the finite `CollisionFreeOn` admission and
   `c1_32_does_not_bind_funding_witnessScripts` remain the honest boundary.
6. Do not add an `open_channel` case to `handshakeStep` without a coordinated
   downstream pass over `Peer.lean` and its proofs.

## 9. Blockers

- **Full wire integration is blocked by ownership, not by a proof gap.**
  `LnLean/Protocol/Messages.lean` is outside this lane's write set, so the
  `Msg`/`MsgKind` constructor patch in §7.1 was not applied or compiled here.
- **No signature/key-ownership model.**  Concluding "peer P owns key K"
  requires `PR-01`/C3 and a secret-key model.  This lane proves the
  construction-level statement and states the attribution hypothesis
  explicitly.
- **No full-tree build.**  The required four-module build is green (17 jobs).
- **No structural blocker in the owned proof module.**

## 10. Final summary for the parent

`S7-L1-FUNDING-AUTH` adds the `open_channel` side of the funding construction
without touching `HandshakeState`/`handshakeStep`, proves that the joint
`open_channel`/`accept_channel` construction is definitionally the old
accept-only construction, and proves the strongest faithful key-authentication
statement: equal funding outputs plus the finite pair-level
`CollisionFreeOn` admission force the two exchanges to agree on the unordered
funding-key set.  Both advertised keys are proved to occur literally in the
71-byte BOLT 3 witness script; transport attribution is an explicit hypothesis
and is mechanized as a scope boundary.  The output is proved not to bind
capacity, push amount, or the temporary channel id, and both one-message
non-determination counterexamples are retained.  The four required modules
build green (17 jobs); all `#print axioms` results are subsets of
`{propext, Quot.sound, Classical.choice}`; the forbidden-construct scan is
clean.  `L1-03` should remain `open (mitigated)` until the exact `Messages.lean`
patch in §7 is applied, since this lane could not edit that file.

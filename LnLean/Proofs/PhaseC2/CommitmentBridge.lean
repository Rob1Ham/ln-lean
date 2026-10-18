import LnLean.Channel.Commitment
import LnLean.Bitcoin.Seam

/-!
# Commitment-output spendability bridge (PC34)

**English claim.**  A BOLT 3 commitment transaction has two main outputs:

* a `to_local` output whose witness script is
  `OP_CSV <csv> OP_DROP <revocation_pubkey> OP_CHECKSIG`, wrapped in a
  P2WSH program; and
* a `to_remote` output, modelled by the seam as the P2WPKH form
  `OP_0 <20-byte-hash>`.

This module proves the byte-level *shape* of those templates (sizes,
non-emptiness, the presence of the CSV field and of its `OP_DROP`), and then
composes an abstract L1 spendability bridge with the ownership facts of the
Lightning model:

* an accepted spend of the `to_local` outpoint either takes the CSV branch
  (allowed only when the relative delay is satisfied and controlled by the
  commitment's holder) or the revocation branch (controlled by the
  revocation key);
* an accepted spend of the `to_remote` outpoint is controlled by the remote
  holder.

The L1 script interpreter, ECDSA revocation signatures, and SHA-256 are
**not** formalised here.  They are explicit fields of
`CommitmentL1Bridge`, never global postulates:

* `spends` is the L1 spend relation and `accepted` is L1 transaction
  acceptance;
* `controls` is the abstract ownership predicate for an output script;
* `toLocal_contestDelay` / `toLocal_revocation` / `toRemote_controlled` are
  the three script-semantics consequences the composition uses.

The hash function is a parameter (`sha256`), so the P2WSH size theorem is
conditional on its 32-byte output, exactly as in `LnLean.Bitcoin.Seam`.  Every
declaration below is fully proved; no proof hole or new postulate occurs.

**BOLT sections** (pinned BOLT commit
`1aadb719b4007c4cea0ba6e36b08c4fb53788dee`).
* BOLT 3 §`to_local` (`refs/bolts/03-transactions.md:113-135`): the CSV
  delay and the revocation-key branch.
* BOLT 3 §`to_remote` (`refs/bolts/03-transactions.md:136-147`): the remote
  party's P2WPKH (or P2WSH) payment output.
* BOLT 3 §`revocationpubkey` (`refs/bolts/03-transactions.md:799`): the key
  that opens the revoked `to_local` branch.
* BOLT 2 §`to_self_delay` (`refs/bolts/02-peer-protocol.md:750-752`): the
  delay on the broadcaster's own output is the *counterparty's* negotiated
  `to_self_delay`.

**rust-lightning anchors** (commit
`fe4900930c6bd5786ec4203274d7cf312776a5a6`).
* `lightning/src/ln/chan_utils.rs:687`
  (`get_revokeable_redeemscript`, the `to_local` CSV/revocation script).
* `lightning/src/ln/chan_utils.rs:2183` (`revokeable_output_index`),
  `:2208` (`build_to_local_justice_tx`).
* `lightning/src/ln/chan_utils.rs:537`
  (`derive_private_revocation_key`).
* `lightning/src/chain/channelmonitor.rs:5104-5110` (look up the revealed
  per-commitment secret, derive the revocation key, build the justice
  package).

**What is explicitly NOT modelled.**  Concrete script execution, witness
serialisation, BIP 143 sighashes, ECDSA/revocation signature checking,
SHA-256, transaction ordering, fee bumping, and the exact single-anchor
exception.  The bridge's fields name these obligations; the theorems below
are unconditional in Lean relative to that interface.
-/

namespace LnLean.Proofs.PhaseC2.CommitmentBridge

open LnLean
open LnLean.Channel
open LnLean.Bitcoin

set_option autoImplicit false

/-! ## Script shapes: `to_local` -/

/-- A one-byte `ByteArray` literal has size one.  The seam's `pushData`
computes the push length from this size, so this is the only reduction fact
needed by the `to_local` size proofs. -/
theorem oneByte_size (x : UInt8) : (ByteArray.mk #[x]).size = 1 := rfl

/-- The exact `to_local` template size:
`<push len> <csv byte> OP_CSV OP_DROP <push len> <pubkey> OP_CHECKSIG`.
The CSV operand is always one byte in the wave-A seam, so the template has
six opcode/length bytes plus the key bytes. -/
theorem toLocalScript_size_exact (pk : PubKey) (csv : Blocks) :
    (toLocalScript pk csv).bytes.size = 6 + pk.bytes.size := by
  simp [toLocalScript, pushData, oneByte_size]
  omega

/-- For a compressed (33-byte) pubkey the `to_local` witness script is
39 bytes. -/
theorem toLocalScript_size (pk : PubKey) (csv : Blocks)
    (h : pk.bytes.size = 33) :
    (toLocalScript pk csv).bytes.size = 39 := by
  rw [toLocalScript_size_exact, h]

/-- The `to_local` template is never empty. -/
theorem toLocalScript_nonempty (pk : PubKey) (csv : Blocks) :
    0 < (toLocalScript pk csv).bytes.size := by
  rw [toLocalScript_size_exact]
  omega

/-- The first byte of the template is the one-byte push length. -/
theorem toLocalScript_push_len (pk : PubKey) (csv : Blocks) :
    (toLocalScript pk csv).bytes[0]? = some 1 := rfl

/-- The second byte is the CSV operand itself. -/
theorem toLocalScript_csv_byte (pk : PubKey) (csv : Blocks) :
    (toLocalScript pk csv).bytes[1]? = some csv.toUInt8 := rfl

/-- The CSV opcode is present at byte 2. -/
theorem toLocalScript_csv_opcode (pk : PubKey) (csv : Blocks) :
    (toLocalScript pk csv).bytes[2]? = some OP_CSV := rfl

/-- The `OP_DROP` that consumes the CSV operand is present at byte 3. -/
theorem toLocalScript_drop_opcode (pk : PubKey) (csv : Blocks) :
    (toLocalScript pk csv).bytes[3]? = some OP_DROP := rfl

/-- The pubkey push length byte is derived from the key size. -/
theorem toLocalScript_key_push_len (pk : PubKey) (csv : Blocks) :
    (toLocalScript pk csv).bytes[4]? = some pk.bytes.size.toUInt8 := rfl

/-- Existential form of the CSV field-presence claim. -/
theorem toLocalScript_has_csv_field (pk : PubKey) (csv : Blocks) :
    ∃ i : Nat, (toLocalScript pk csv).bytes[i]? = some OP_CSV :=
  ⟨2, toLocalScript_csv_opcode pk csv⟩

/-- The commitment-scoped `to_local` witness script, using the commitment's
own contest delay (the counterparty's `to_self_delay`). -/
def commitmentToLocalScript (c : Commitment) (revocationPubKey : PubKey) :
    Script :=
  toLocalScript revocationPubKey c.contestDelay

/-- The commitment-scoped `to_local` witness script has the same 39-byte
shape. -/
theorem commitmentToLocalScript_size (c : Commitment) (pk : PubKey)
    (h : pk.bytes.size = 33) :
    (commitmentToLocalScript c pk).bytes.size = 39 :=
  toLocalScript_size pk c.contestDelay h

/-- The commitment-scoped template is non-empty. -/
theorem commitmentToLocalScript_nonempty (c : Commitment) (pk : PubKey) :
    0 < (commitmentToLocalScript c pk).bytes.size :=
  toLocalScript_nonempty pk c.contestDelay

/-- The commitment-scoped template still exposes the CSV opcode. -/
theorem commitmentToLocalScript_csv_opcode (c : Commitment) (pk : PubKey) :
    (commitmentToLocalScript c pk).bytes[2]? = some OP_CSV :=
  toLocalScript_csv_opcode pk c.contestDelay

/-! ## Script shapes: the revocation branch -/

/-- The revoked `to_local` branch: `<revocation_pubkey> OP_CHECKSIG`.
This is BOLT 3's revocation path without the CSV delay. -/
def revocationScript (revocationPubKey : PubKey) : Script :=
  ⟨pushData revocationPubKey.bytes ++ ByteArray.empty.push OP_CHECKSIG⟩

/-- The revocation branch has one push-length byte, the key, and
`OP_CHECKSIG`. -/
theorem revocationScript_size_exact (pk : PubKey) :
    (revocationScript pk).bytes.size = 2 + pk.bytes.size := by
  simp [revocationScript, pushData]
  omega

/-- For a 33-byte key the revocation branch is 35 bytes. -/
theorem revocationScript_size (pk : PubKey) (h : pk.bytes.size = 33) :
    (revocationScript pk).bytes.size = 35 := by
  rw [revocationScript_size_exact, h]

/-- The revocation branch is never empty. -/
theorem revocationScript_nonempty (pk : PubKey) :
    0 < (revocationScript pk).bytes.size := by
  rw [revocationScript_size_exact]
  omega

/-! ## Script shapes: `to_remote` -/

/-- The seam's `to_remote` output is exactly the P2WPKH witness program. -/
theorem toRemoteScript_eq_p2wpkh (h160 : ByteArray) :
    toRemoteScript h160 = p2wpkh h160 := rfl

/-- Exact `to_remote` size: `OP_0`, the 20-byte push length, and the hash. -/
theorem toRemoteScript_size_exact (h160 : ByteArray) :
    (toRemoteScript h160).bytes.size = 2 + h160.size := by
  simp [toRemoteScript, p2wpkh]

/-- A 20-byte payment-key hash gives the standard 22-byte P2WPKH program. -/
theorem toRemoteScript_size (h160 : ByteArray) (h : h160.size = 20) :
    (toRemoteScript h160).bytes.size = 22 := by
  rw [toRemoteScript_size_exact, h]

/-- The `to_remote` program is never empty. -/
theorem toRemoteScript_nonempty (h160 : ByteArray) :
    0 < (toRemoteScript h160).bytes.size := by
  rw [toRemoteScript_size_exact]
  omega

/-- The `OP_0` version byte and the 20-byte push length are present, so the
template really is a witness program rather than an arbitrary script. -/
theorem toRemoteScript_witness_program_prefix (h160 : ByteArray) :
    (toRemoteScript h160).bytes[0]? = some OP_0 ∧
      (toRemoteScript h160).bytes[1]? = some 0x14 := by
  constructor <;> rfl

/-! ## The two `to_local` spend paths -/

/-- The two script branches of a `to_local` output.  The model does not
attempt to recover which branch a concrete L1 interpreter took; the bridge
records it explicitly. -/
inductive SpendPath where
  | contestDelay
  | revocation
deriving Repr, DecidableEq, BEq

/-- Every `SpendPath` is one of the two branches.  This is a theorem, not a
bridge field. -/
theorem SpendPath.eq_contestDelay_or_revocation (p : SpendPath) :
    p = SpendPath.contestDelay ∨ p = SpendPath.revocation := by
  cases p <;> simp

/-! ## The L1 bridge -/

/-- The L1 facts needed by the two main commitment outputs, as an explicit
interface.

`spends` is the L1 spend relation and `accepted` is L1 acceptance.  The
three law fields are the script-semantics consequences used by the
composition below; they are fields rather than global postulates, so every
theorem in this module is unconditional in Lean relative to the bridge.

`toLocalScriptPubKey`, `revocationScriptPubKey`, and
`toRemoteScriptPubKey` are defined from the bridge parameters (the hash
function and the two keys), so their P2WSH/P2WPKH shapes are *definitional*
and the size theorems below apply directly to the scripts named by the law
fields. -/
structure CommitmentL1Bridge (c : Commitment) where
  /-- L1 spend relation: transaction `tx` spends outpoint `o`. -/
  spends : Tx → OutPoint → Prop
  /-- L1 acceptance (script/witness acceptance plus on-chain inclusion). -/
  accepted : Tx → Prop
  /-- Abstract ownership predicate for an output script.  For the delay
  branch this is the commitment holder; for the `to_remote` output it is the
  remote holder; for the revocation branch it is the holder of the
  revocation key. -/
  controls : Script → Prop
  /-- The hash function used for P2WSH commitments; a parameter, not a
  concrete SHA-256 implementation. -/
  sha256 : ByteArray → ByteArray
  /-- The revocation public key committed to by the `to_local` output. -/
  revocationPubKey : PubKey
  /-- The 20-byte payment-key hash committed to by the `to_remote` output. -/
  remotePaymentHash : ByteArray
  /-- Outpoint of the `to_local` output. -/
  toLocalOutpoint : OutPoint
  /-- Outpoint of the `to_remote` output. -/
  toRemoteOutpoint : OutPoint
  /-- Which `to_local` branch the spend takes. -/
  path : Tx → OutPoint → SpendPath
  /-- The relative timelock of the CSV branch has elapsed. -/
  delaySatisfied : Tx → Prop
  /-- **CSV-branch law.**  An accepted `to_local` spend that takes the
  contest-delay branch satisfies the relative delay and is controlled by the
  commitment holder's script. -/
  toLocal_contestDelay : ∀ (tx : Tx), accepted tx →
    spends tx toLocalOutpoint →
    path tx toLocalOutpoint = SpendPath.contestDelay →
      delaySatisfied tx ∧
        controls (p2wsh (sha256 (toLocalScript revocationPubKey c.contestDelay).bytes))
  /-- **Revocation-branch law.**  An accepted `to_local` spend that takes the
  revocation branch is controlled by the revocation key's script. -/
  toLocal_revocation : ∀ (tx : Tx), accepted tx →
    spends tx toLocalOutpoint →
    path tx toLocalOutpoint = SpendPath.revocation →
      controls (p2wsh (sha256 (revocationScript revocationPubKey).bytes))
  /-- **`to_remote` law.**  An accepted spend of the `to_remote` outpoint is
  controlled by the remote holder's script. -/
  toRemote_controlled : ∀ (tx : Tx), accepted tx →
    spends tx toRemoteOutpoint →
      controls (toRemoteScript remotePaymentHash)

namespace CommitmentL1Bridge

variable {c : Commitment}

/-- The P2WSH script paid by the `to_local` output. -/
def toLocalScriptPubKey (b : CommitmentL1Bridge c) : Script :=
  p2wsh (b.sha256 (toLocalScript b.revocationPubKey c.contestDelay).bytes)

/-- The P2WSH script paid by the revocation branch. -/
def revocationScriptPubKey (b : CommitmentL1Bridge c) : Script :=
  p2wsh (b.sha256 (revocationScript b.revocationPubKey).bytes)

/-- The P2WPKH script paid by the `to_remote` output. -/
def toRemoteScriptPubKey (b : CommitmentL1Bridge c) : Script :=
  toRemoteScript b.remotePaymentHash

/-- The `to_local` script named by the bridge is definitionally the P2WSH
commitment to the commitment-scoped CSV template. -/
theorem toLocalScriptPubKey_eq_p2wsh (b : CommitmentL1Bridge c) :
    b.toLocalScriptPubKey =
      p2wsh (b.sha256
        (toLocalScript b.revocationPubKey c.contestDelay).bytes) := rfl

/-- The `to_remote` script named by the bridge is definitionally the
P2WPKH template. -/
theorem toRemoteScriptPubKey_eq_p2wpkh (b : CommitmentL1Bridge c) :
    b.toRemoteScriptPubKey = p2wpkh b.remotePaymentHash := rfl

/-- **Conditional to-local composition.**  An accepted spend of the
`to_local` outpoint is either a contest-delay spend — the relative delay is
satisfied and the script is controlled by the commitment holder — or a
revocation spend controlled by the revocation key. -/
theorem toLocalSpend_controlled_after_delay_or_revocation
    (b : CommitmentL1Bridge c) {tx : Tx}
    (hacc : b.accepted tx) (hsp : b.spends tx b.toLocalOutpoint) :
    (b.path tx b.toLocalOutpoint = SpendPath.contestDelay ∧
        b.delaySatisfied tx ∧ b.controls b.toLocalScriptPubKey) ∨
      (b.path tx b.toLocalOutpoint = SpendPath.revocation ∧
        b.controls b.revocationScriptPubKey) := by
  rcases SpendPath.eq_contestDelay_or_revocation
    (b.path tx b.toLocalOutpoint) with hd | hr
  · rcases b.toLocal_contestDelay tx hacc hsp hd with ⟨hdel, hctl⟩
    exact Or.inl ⟨hd, hdel, hctl⟩
  · exact Or.inr ⟨hr, b.toLocal_revocation tx hacc hsp hr⟩

/-- The CSV branch of an accepted `to_local` spend: the delay is satisfied
and the script is holder-controlled. -/
theorem toLocalSpend_delay_controlled (b : CommitmentL1Bridge c) {tx : Tx}
    (hacc : b.accepted tx) (hsp : b.spends tx b.toLocalOutpoint)
    (hd : b.path tx b.toLocalOutpoint = SpendPath.contestDelay) :
    b.delaySatisfied tx ∧ b.controls b.toLocalScriptPubKey :=
  b.toLocal_contestDelay tx hacc hsp hd

/-- The revocation branch of an accepted `to_local` spend is controlled by
the revocation key's script. -/
theorem toLocalSpend_revocation_controlled (b : CommitmentL1Bridge c)
    {tx : Tx} (hacc : b.accepted tx) (hsp : b.spends tx b.toLocalOutpoint)
    (hr : b.path tx b.toLocalOutpoint = SpendPath.revocation) :
    b.controls b.revocationScriptPubKey :=
  b.toLocal_revocation tx hacc hsp hr

/-- **Conditional to-remote composition.**  An accepted spend of the
`to_remote` outpoint is controlled by the remote holder's script. -/
theorem toRemoteSpend_controlledByRemoteHolder (b : CommitmentL1Bridge c)
    {tx : Tx} (hacc : b.accepted tx) (hsp : b.spends tx b.toRemoteOutpoint) :
    b.controls b.toRemoteScriptPubKey :=
  b.toRemote_controlled tx hacc hsp

/-- A `to_local` P2WSH output over a 32-byte hash is 34 bytes. -/
theorem toLocalOutput_script_size (b : CommitmentL1Bridge c)
    (h : (b.sha256
      (toLocalScript b.revocationPubKey c.contestDelay).bytes).size = 32) :
    b.toLocalScriptPubKey.bytes.size = 34 := by
  unfold toLocalScriptPubKey
  exact p2wsh_size _ h

/-- The `to_local` P2WSH output is non-empty. -/
theorem toLocalOutput_nonempty (b : CommitmentL1Bridge c)
    (h : (b.sha256
      (toLocalScript b.revocationPubKey c.contestDelay).bytes).size = 32) :
    0 < b.toLocalScriptPubKey.bytes.size := by
  rw [toLocalOutput_script_size b h]
  omega

/-- The revocation-branch P2WSH output over a 32-byte hash is 34 bytes. -/
theorem revocationOutput_script_size (b : CommitmentL1Bridge c)
    (h : (b.sha256 (revocationScript b.revocationPubKey).bytes).size = 32) :
    b.revocationScriptPubKey.bytes.size = 34 := by
  unfold revocationScriptPubKey
  exact p2wsh_size _ h

/-- The `to_remote` P2WPKH output over a 20-byte hash is 22 bytes. -/
theorem toRemoteOutput_script_size (b : CommitmentL1Bridge c)
    (h : b.remotePaymentHash.size = 20) :
    b.toRemoteScriptPubKey.bytes.size = 22 := by
  unfold toRemoteScriptPubKey
  exact toRemoteScript_size b.remotePaymentHash h

/-- **End-to-end shape composition for `to_local`.**  The script named by an
accepted CSV-branch spend is a 34-byte P2WSH program, while the witness
script it commits to is the 39-byte CSV template. -/
theorem toLocalSpend_script_shape (b : CommitmentL1Bridge c) {tx : Tx}
    (hacc : b.accepted tx) (hsp : b.spends tx b.toLocalOutpoint)
    (hd : b.path tx b.toLocalOutpoint = SpendPath.contestDelay)
    (hkey : b.revocationPubKey.bytes.size = 33)
    (hhash : (b.sha256
      (toLocalScript b.revocationPubKey c.contestDelay).bytes).size = 32) :
    b.controls b.toLocalScriptPubKey ∧
      b.toLocalScriptPubKey.bytes.size = 34 ∧
      (toLocalScript b.revocationPubKey c.contestDelay).bytes.size = 39 := by
  rcases b.toLocalSpend_delay_controlled hacc hsp hd with ⟨-, hctl⟩
  exact ⟨hctl, b.toLocalOutput_script_size hhash,
    toLocalScript_size b.revocationPubKey c.contestDelay hkey⟩

end CommitmentL1Bridge

end LnLean.Proofs.PhaseC2.CommitmentBridge

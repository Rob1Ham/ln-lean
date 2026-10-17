import LnLean.Basic.Core
import LnLean.Protocol.Messages

/-!
# Error and warning handling laws (BOLT 1)

## English claim

This module states the error-handling contract of BOLT 1 for the scaffold's
wire model:

1. An `error` message carries a channel identifier, and a well-formed
   `error` has a 32-byte identifier and a data field bounded by the wire
   maximum.
2. A `warning` is observationally neutral at the channel layer: receiving one
   leaves every modelled channel phase unchanged.  A fatal `error` moves the
   addressed channel to the `closed` phase; `closed` is the model's
   representation of a failed channel.
3. An `error` whose `channel_id` does not match a channel is ignored, not
   applied to some other channel.  The all-zero `channel_id` is the BOLT 1
   broadcast form: it fails every channel in the supplied (single-peer) list.
4. Every value of the model's internal `ProtocolError.code` is one of the
   fourteen enumerated `ErrorCode` constructors.
5. A message cannot be both a warning and a fatal error: the two severities
   are disjoint, and their wire types (1 and 17) differ.

## BOLT sections

* BOLT 1 §"Lightning Message Format"
  (`refs/bolts/01-messaging.md:43-92`): two-byte type, two-byte payload
  length, 65535-byte payload bound.
* BOLT 1 §"The `error` and `warning` Messages"
  (`refs/bolts/01-messaging.md:345-420`):
  * both messages are `channel_id || u16 len || len*byte data` (`:349-359`);
  * an all-zero `channel_id` refers to all channels (`:363`);
  * sending an `error` MUST fail the referred channels (`:384-386`);
  * receiving an `error` MUST fail the referred channel, or all channels for
    the all-zero id (`:393-398`);
  * receiving a `warning` only SHOULD log / MAY shutdown (`:399-401`);
  * a message for no existing channel MUST be ignored (`:402-403`);
  * `data` should be printable ASCII before display (`:404-405`).

## rust-lightning anchors (commit fe49009)

* `lightning/src/ln/msgs.rs:131` `ErrorMessage { channel_id, data }` and
  `:149` `WarningMessage { channel_id, data }`.
* `lightning/src/ln/msgs.rs:4276-4300` encodes/decodes `ErrorMessage` as
  `channel_id` plus a `u16` length and data; `:4303-4327` does the same for
  `WarningMessage`.
* `lightning/src/ln/msgs.rs:1636-1671` `ErrorAction`: warnings have their own
  action (`SendWarningMessage`, `DisconnectPeerWithWarning`) and are distinct
  from `SendErrorMessage`.
* `lightning/src/ln/peer_handler.rs:2414-2428`: an inbound `Error` is passed
  to `chan_handler.handle_error`, while an inbound `Warning` is only logged.
* `lightning/src/ln/channelmanager.rs:17840-17950`: a non-zero error id is
  looked up; a missing channel is ignored (`None => {}` at `:17943`), while
  an all-zero id collects and force-closes every channel with that peer
  (`:17898-17913`).
* `lightning/src/ln/channelmanager.rs:4893-4943` `handle_error` performs the
  close/persist/notification work for an internal error action.

## What is NOT modelled

* The wave-A channel state machine (`LnLean.Channel.State`) is not importable
  in this wave-A-only module.  `ChannelView` is the two-field projection on
  which error handling acts: identifier and phase.  Connecting the `closed`
  phase below to the full state machine's transitions is an open refinement.
* The BOLT 1 `error` payload carries no numeric error code.  `ErrorCode` and
  `ProtocolError` are the scaffold's *internal* classification; this module
  does not claim that the wire `data` bytes decode to one of them.
* `data` is modelled as `ByteArray`, not as a UTF-8 `String`.  The
  printable-ASCII logging recommendation is not enforced.
* `channel_id = 0` is interpreted relative to the list supplied to
  `handleInbound`; there is no peer identity in `ChannelView`, so "all
  channels with the sending node" is represented by "all channels in this
  list".  Callers must pass a single peer's channel list.
* No logging, shutdown attempt, retry, timeout, or connection teardown is
  modelled.  The BOLT MAY/SHOULD clauses above are not state transitions.
-/

namespace LnLean.Protocol

set_option autoImplicit false

open LnLean

/-! ## Severity: warnings and fatal errors are disjoint -/

/-- The two BOLT 1 diagnostic severities. -/
inductive Severity where
  | warning
  | error
deriving Repr, DecidableEq, BEq

/-- Severity of a wire message: only the `warning` and `error` constructors
have one. -/
def severityOf : Msg → Option Severity
  | .warning _ => some .warning
  | .error _ => some .error
  | _ => none

/-- `true` exactly for the `warning` constructor. -/
def isWarning : Msg → Bool
  | .warning _ => true
  | _ => false

/-- `true` exactly for the `error` constructor. -/
def isFatal : Msg → Bool
  | .error _ => true
  | _ => false

@[simp] theorem severityOf_warning (w : WarningMsg) :
    severityOf (.warning w) = some .warning := rfl

@[simp] theorem severityOf_error (e : ErrorMsg) :
    severityOf (.error e) = some .error := rfl

/-- The severities of a `warning` and an `error` are unequal. -/
theorem warning_error_severity_ne (w : WarningMsg) (e : ErrorMsg) :
    severityOf (.warning w) ≠ severityOf (.error e) := by
  simp

/-- The two diagnostics have distinct BOLT wire types. -/
theorem warning_error_wireType_ne (w : WarningMsg) (e : ErrorMsg) :
    msgType (.warning w) ≠ msgType (.error e) := by
  rw [show msgType (.warning w) = 1 from rfl,
      show msgType (.error e) = 17 from rfl]
  decide

/-- **No message is both a warning and a fatal error.** -/
theorem not_warning_and_fatal (m : Msg) :
    ¬ (isWarning m = true ∧ isFatal m = true) := by
  cases m <;> simp [isWarning, isFatal]

/-- A fatal message is exactly an `error` message, never a `warning`. -/
theorem fatal_not_warning (m : Msg) (h : isFatal m = true) :
    isWarning m = false := by
  cases m <;> simp [isWarning, isFatal] at h ⊢

/-! ## The enumerated error codes -/

/-- All constructors of the model's `ErrorCode` enumeration, in declaration
order.  `ErrorCode` is an inductive with no other values. -/
def allErrorCodes : List ErrorCode :=
  [.protocol, .funding, .update, .permanentChannelFailure,
   .temporaryChannelFailure, .expiryTooSoon, .amountBelowMinimum,
   .feeInsufficient, .incorrectCltvExpiry, .unknownNextPeer, .invalidOnion,
   .invalidOnionHmac, .invalidOnionKey, .internal]

/-- The enumeration has fourteen codes. -/
theorem allErrorCodes_length : allErrorCodes.length = 14 := rfl

/-- **Every protocol error code is enumerated.**  The proof is by cases over
the `ErrorCode` inductive, so adding a constructor without updating
`allErrorCodes` breaks this theorem. -/
theorem code_mem_allErrorCodes (p : ProtocolError) :
    p.code ∈ allErrorCodes := by
  cases p.code <;> simp [allErrorCodes]

/-- Existential form of `code_mem_allErrorCodes`. -/
theorem code_is_enumerated (p : ProtocolError) :
    ∃ c : ErrorCode, c ∈ allErrorCodes ∧ p.code = c :=
  ⟨p.code, code_mem_allErrorCodes p, rfl⟩

/-! ## Channel projection and error application -/

/-- The part of a channel that BOLT 1 error handling observes.  `phase` is
the wave-A core's coarse lifecycle; `closed` is the failed state. -/
structure ChannelView where
  channelId : ChannelId
  phase : ChannelPhase
deriving Repr

namespace ChannelView

/-- A channel that has been failed.  The model has no separate `failed`
phase, so failure is represented by `closed`. -/
def failed (c : ChannelView) : Prop := c.phase = .closed

theorem failed_iff_phase (c : ChannelView) :
    c.failed ↔ c.phase = .closed := Iff.rfl

end ChannelView

/-- The BOLT 1 all-zero identifier test, reusing the message module's byte
predicate. -/
def allZeroId (c : ChannelId) : Bool := allZero c.bytes

/-- State effect of a diagnostic on one channel.  Warnings are neutral; every
other message, including `error`, leaves the projection unchanged except that
`error` sets the phase to `closed`. -/
def applyMsg (m : Msg) (c : ChannelView) : ChannelView :=
  match m with
  | .error _ => { c with phase := .closed }
  | _ => c

@[simp] theorem applyMsg_warning (c : ChannelView) (w : WarningMsg) :
    applyMsg (.warning w) c = c := rfl

@[simp] theorem applyMsg_error (c : ChannelView) (e : ErrorMsg) :
    applyMsg (.error e) c = { c with phase := .closed } := rfl

theorem applyMsg_error_failed (c : ChannelView) (e : ErrorMsg) :
    (applyMsg (.error e) c).failed := rfl

theorem applyMsg_warning_phase (c : ChannelView) (w : WarningMsg) :
    (applyMsg (.warning w) c).phase = c.phase := rfl

/-- Apply an inbound message to one channel, respecting BOLT 1 scoping.  An
all-zero identifier applies to every channel; otherwise only the channel
whose 32-byte identifier matches is touched.  Non-channel messages and
unknown identifiers leave the channel unchanged. -/
def applyToChannel (m : Msg) (c : ChannelView) : ChannelView :=
  match channelId? m with
  | none => c
  | some cid =>
      if allZeroId cid then applyMsg m c
      else if c.channelId.bytes = cid.bytes then applyMsg m c
      else c

/-- A warning is neutral for every single channel. -/
@[simp] theorem applyToChannel_warning (c : ChannelView) (w : WarningMsg) :
    applyToChannel (.warning w) c = c := by
  simp [applyToChannel, channelId?, applyMsg]

/-- Apply an inbound message to a peer's channel list. -/
def handleInbound (chans : List ChannelView) (m : Msg) : List ChannelView :=
  chans.map (applyToChannel m)

/-- **A warning changes no channel state.** -/
theorem warning_identity (chans : List ChannelView) (w : WarningMsg) :
    handleInbound chans (.warning w) = chans := by
  unfold handleInbound
  rw [List.map_congr_left (fun c _ => applyToChannel_warning c w)]
  exact List.map_id chans

/-- **Only fatal errors change state.**  A message with no severity is
neutral for every channel projection. -/
theorem nonfatal_identity (m : Msg) (h : severityOf m = none)
    (c : ChannelView) : applyToChannel m c = c := by
  cases m <;> simp [severityOf, applyToChannel, channelId?, applyMsg] at h ⊢

/-- An `error` addressed to a matching identifier closes that channel. -/
theorem applyToChannel_error_closed (c : ChannelView) (e : ErrorMsg)
    (h : c.channelId.bytes = e.channelId.bytes) :
    (applyToChannel (.error e) c).phase = .closed := by
  simp [applyToChannel, channelId?, applyMsg, h]

/-- Matching error application produces exactly the closed update. -/
theorem applyToChannel_error_matching (c : ChannelView) (e : ErrorMsg)
    (h : c.channelId.bytes = e.channelId.bytes) :
    applyToChannel (.error e) c = { c with phase := .closed } := by
  simp [applyToChannel, channelId?, applyMsg, h]

/-- **Channel-id scoping.**  An error whose identifier is neither zero nor
equal to the channel's identifier leaves that channel untouched. -/
theorem applyToChannel_error_preserves_other (c : ChannelView) (e : ErrorMsg)
    (hne : c.channelId.bytes ≠ e.channelId.bytes)
    (hnz : allZeroId e.channelId = false) :
    applyToChannel (.error e) c = c := by
  simp [applyToChannel, channelId?, hnz, hne]

/-- **Unknown-channel scoping at the list level.**  If no channel in the list
matches the error's identifier and the identifier is not the all-zero
broadcast value, applying the error returns the list unchanged. -/
theorem handleInbound_error_unknown_ignored (chans : List ChannelView)
    (e : ErrorMsg)
    (hne : ∀ c ∈ chans, c.channelId.bytes ≠ e.channelId.bytes)
    (hnz : allZeroId e.channelId = false) :
    handleInbound chans (.error e) = chans := by
  unfold handleInbound
  rw [List.map_congr_left
    (fun c hc => applyToChannel_error_preserves_other c e (hne c hc) hnz)]
  exact List.map_id chans

/-- An all-zero error identifier closes one channel. -/
theorem applyToChannel_error_allZero (c : ChannelView) (e : ErrorMsg)
    (hz : allZeroId e.channelId = true) :
    applyToChannel (.error e) c = { c with phase := .closed } := by
  simp [applyToChannel, channelId?, applyMsg, hz]

/-- **An all-zero error identifier fails every channel** in the supplied
single-peer list.  This is BOLT 1's `channel_id = 0` broadcast form. -/
theorem handleInbound_error_allZero (chans : List ChannelView) (e : ErrorMsg)
    (hz : allZeroId e.channelId = true) :
    handleInbound chans (.error e) =
      chans.map (fun c => { c with phase := .closed }) := by
  unfold handleInbound
  exact List.map_congr_left (fun c _ => applyToChannel_error_allZero c e hz)

/-- A concrete singleton law: an error for the channel's own identifier
produces a one-element list holding the closed channel. -/
theorem handleInbound_error_singleton (c : ChannelView) (e : ErrorMsg)
    (h : c.channelId.bytes = e.channelId.bytes) :
    handleInbound [c] (.error e) = [{ c with phase := .closed }] := by
  simp [handleInbound, applyToChannel, channelId?, applyMsg, h]

/-- A matching channel appears closed in the output of the list-level
handler. -/
theorem handleInbound_error_mem_closed (chans : List ChannelView)
    (e : ErrorMsg) (c : ChannelView) (hmem : c ∈ chans)
    (h : c.channelId.bytes = e.channelId.bytes) :
    { c with phase := .closed } ∈ handleInbound chans (.error e) := by
  unfold handleInbound
  exact List.mem_map.mpr ⟨c, hmem, applyToChannel_error_matching c e h⟩

/-- **Warnings cannot undo a failure.**  A warning received after an error
leaves the post-error list exactly as it was. -/
theorem warning_after_error (chans : List ChannelView) (e : ErrorMsg)
    (w : WarningMsg) :
    handleInbound (handleInbound chans (.error e)) (.warning w) =
      handleInbound chans (.error e) :=
  warning_identity _ w

/-! ## Wire-level bounds and channel-id validity -/

/-- BOLT 1 `error` carries the channel identifier in the
`channel_id?` projection. -/
theorem error_channelId (e : ErrorMsg) :
    channelId? (.error e) = some e.channelId := rfl

/-- BOLT 1 `warning` carries the channel identifier in the
`channelId?` projection. -/
theorem warning_channelId (w : WarningMsg) :
    channelId? (.warning w) = some w.channelId := rfl

/-- A well-formed `error` has a 32-byte channel identifier. -/
theorem error_channelId_valid {e : ErrorMsg}
    (h : wellFormed (.error e)) : e.channelId.Valid :=
  wellFormed_channelId h rfl

/-- **Error data is bounded by the wire maximum.**  The `error` payload is
`32 (channel_id) + 2 (u16 len) + data`, and the whole payload must fit the
65535-byte BOLT 1 bound, so `data.size ≤ 65501`. -/
theorem error_data_bounded {e : ErrorMsg}
    (h : wellFormed (.error e)) : e.data.size ≤ 65501 := by
  have hlen : 34 + e.data.size ≤ 65535 := by
    simpa [wellFormed, msgLength] using h.1
  omega

/-- The same bound for `warning`, whose payload layout is identical. -/
theorem warning_data_bounded {w : WarningMsg}
    (h : wellFormed (.warning w)) : w.data.size ≤ 65501 := by
  have hlen : 34 + w.data.size ≤ 65535 := by
    simpa [wellFormed, msgLength] using h.1
  omega

/-- An `error` message has BOLT 1 wire type 17. -/
theorem error_msgType_eq_17 (e : ErrorMsg) :
    msgType (.error e) = 17 := rfl

/-- A `warning` message has BOLT 1 wire type 1. -/
theorem warning_msgType_eq_1 (w : WarningMsg) :
    msgType (.warning w) = 1 := rfl

end LnLean.Protocol

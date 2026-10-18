#!/usr/bin/env python3
"""Validate the S5-CONF-DIFF wire, framing, and differential fixtures.

This checker is deliberately small and dependency-free.  It does seven things:

1. Recomputes every BigSize encoding and decoding decision with an independent
   reference implementation and compares it to ``tests/conformance/vectors.json``.
2. Recomputes every TLV structural parse and ordering-admission decision.  The
   parser and admission phases are kept separate because the Lean model's
   ``decodeTLV`` is structural only; BOLT 1 ordering is enforced by
   ``decodeAdmissible``.
3. Recomputes the BOLT 8 transport frame ``type || length || payload`` where
   ``length = 2 + payload.size``, including malformed/truncated frames and the
   maximum transport length.  This is deliberately separate from the model's
   payload-only ``LnLean.Wire.frame``.
4. Replays pinned rust-lightning differential fixtures from
   ``tests/conformance/rust-lightning/fixtures.json`` (committed JSON only; no
   network or Rust toolchain).
5. Verifies the fixture provenance against the pinned checkout when
   ``refs/rust-lightning`` is present: the recorded SHA-256 for each source
   file and, when the checkout has a ``.git`` directory, its exact HEAD.  Use
   ``--no-provenance`` to skip this optional check.
6. Requires the promoted BOLT 8 model to exist in
   ``LnLean/Wire/Message.lean`` (``transportFrame``, ``unframeTransport``, the
   round trip, the declared-length law, and the payload-decoder boundary).
7. Cross-checks that every vector names a theorem that exists in
   ``LnLean/Proofs/ConformanceTargets.lean`` or
   ``LnLean/Proofs/ConformanceDiffTargets.lean`` and that the theorem statement
   mentions the vector's input bytes (and, where applicable, its value).

It does **not** run Lean.  The Lean modules prove the same expectations by
``decide``/the model's lemmas and are checked by ``lake build``.  This is
vector/differential conformance, not a full implementation test.

Usage:
    python3 scripts/check-conformance.py
    python3 scripts/check-conformance.py --no-lean
    python3 scripts/check-conformance.py --verbose
    python3 scripts/check-conformance.py --no-self-test
    python3 scripts/check-conformance.py --no-provenance
    python3 scripts/check-conformance.py --source-dir /path/to/rust-lightning

Exit status: 0 on success, 1 on a vector/Lean-sync mismatch, 2 on usage/IO.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
DEFAULT_VECTORS = ROOT / "tests" / "conformance" / "vectors.json"
DEFAULT_LEAN = ROOT / "LnLean" / "Proofs" / "ConformanceTargets.lean"
DEFAULT_LEAN_DIFF = ROOT / "LnLean" / "Proofs" / "ConformanceDiffTargets.lean"
DEFAULT_MESSAGE = ROOT / "LnLean" / "Wire" / "Message.lean"
DEFAULT_DIFF = ROOT / "tests" / "conformance" / "rust-lightning" / "fixtures.json"
DEFAULT_SOURCE = ROOT / "refs" / "rust-lightning"

UINT64_MAX = 2**64 - 1

# The BOLT 8 transport model promoted from the wave-5 conformance module into
# the production `LnLean.Wire.Message` module.  The checker loads this module
# separately from the vector-theorem modules because `Wire` and
# `Wire.Transport` intentionally share the short name `fits_iff_payload`.
PROMOTED_TRANSPORT_THEOREMS = [
    "transportLength_eq_messageSize",
    "transportFrame_header_eq",
    "transportFrame_size",
    "transportFrame_size_eq",
    "fits_iff_transportLength",
    "fits_iff_payload",
    "unframeTransportList_eq_some_iff",
    "unframeTransport_transportFrame",
    "unframeTransport_transportFrame_of_fits",
    "decode_transport_length",
    "bytesToList_u16BE_mod",
    "u16Nat_u16BE_mod",
    "unframe_transportFrame_eq_none",
]
PROMOTED_TRANSPORT_DEFS = [
    "transportLength",
    "lengthHeader",
    "transportFrame",
    "unframeTransportList",
    "unframeTransport",
    "declaredTransportLength?",
]

# BOLT 1 Appendix A, copied independently from refs/bolts/01-messaging.md.
# (value, hex bytes) for the published encoding vectors.
BOLT_ENCODE = [
    (0, "00"),
    (252, "fc"),
    (253, "fd00fd"),
    (65535, "fdffff"),
    (65536, "fe00010000"),
    (4294967295, "feffffffff"),
    (4294967296, "ff0000000100000000"),
    (18446744073709551615, "ffffffffffffffffff"),
]

# (hex bytes, status, value or None, consumed or None) for the published
# decoding vectors: 8 canonical, 3 non-canonical, 3 short reads, 4 no reads.
BOLT_DECODE = [
    ("00", "ok", 0, 1),
    ("fc", "ok", 252, 1),
    ("fd00fd", "ok", 253, 3),
    ("fdffff", "ok", 65535, 3),
    ("fe00010000", "ok", 65536, 5),
    ("feffffffff", "ok", 4294967295, 5),
    ("ff0000000100000000", "ok", 4294967296, 9),
    ("ffffffffffffffffff", "ok", 18446744073709551615, 9),
    ("fd00fc", "reject", None, None),
    ("fe0000ffff", "reject", None, None),
    ("ff00000000ffffffff", "reject", None, None),
    ("fd00", "reject", None, None),
    ("feffff", "reject", None, None),
    ("ffffffffff", "reject", None, None),
    ("", "reject", None, None),
    ("fd", "reject", None, None),
    ("fe", "reject", None, None),
    ("ff", "reject", None, None),
]


class CheckError(Exception):
    """A single conformance failure."""


def parse_hex(text: str, where: str) -> bytes:
    if not isinstance(text, str):
        raise CheckError(f"{where}: expected a hex string, got {type(text).__name__}")
    if len(text) % 2:
        raise CheckError(f"{where}: odd-length hex string {text!r}")
    if text and not re.fullmatch(r"[0-9a-f]+", text):
        raise CheckError(f"{where}: expected lowercase hex, got {text!r}")
    return bytes.fromhex(text)


def ref_bigsize_encode(value: int) -> bytes:
    if not 0 <= value <= UINT64_MAX:
        raise CheckError(f"encode value {value} is outside uint64")
    if value < 0xFD:
        return bytes([value])
    if value <= 0xFFFF:
        return b"\xfd" + value.to_bytes(2, "big")
    if value <= 0xFFFFFFFF:
        return b"\xfe" + value.to_bytes(4, "big")
    return b"\xff" + value.to_bytes(8, "big")


def ref_bigsize_decode(data: bytes) -> tuple[int, int]:
    """Return (value, consumed) or raise CheckError with the reason."""
    if not data:
        raise CheckError("empty-input")
    tag = data[0]
    if tag < 0xFD:
        return tag, 1
    width = {0xFD: 2, 0xFE: 4, 0xFF: 8}[tag]
    if len(data) < 1 + width:
        raise CheckError("bigsize-short-read")
    value = int.from_bytes(data[1 : 1 + width], "big")
    if tag == 0xFD and not (0xFD <= value <= 0xFFFF):
        raise CheckError("non-canonical-bigsize")
    if tag == 0xFE and not (0x10000 <= value <= 0xFFFFFFFF):
        raise CheckError("non-canonical-bigsize")
    if tag == 0xFF and value < 0x100000000:
        raise CheckError("non-canonical-bigsize")
    return value, 1 + width


def ref_tlv_parse(data: bytes) -> list[dict[str, Any]]:
    """Structural TLV parse mirroring Wire.TLV.parseRecord/decodeTLV.

    Returns a record list or raises CheckError with a reason.  No namespace,
    known-type, or ordering policy is applied here; ordering is a separate
    admission check, exactly as in the Lean model.
    """
    records: list[dict[str, Any]] = []
    rest = data
    while rest:
        try:
            ty, n1 = ref_bigsize_decode(rest)
        except CheckError as exc:
            raise CheckError(str(exc)) from None
        rest = rest[n1:]
        if not rest:
            raise CheckError("missing-length")
        try:
            length, n2 = ref_bigsize_decode(rest)
        except CheckError as exc:
            raise CheckError(str(exc)) from None
        rest = rest[n2:]
        if len(rest) < length:
            raise CheckError("value-truncated")
        records.append({"type": ty, "value": rest[:length].hex()})
        rest = rest[length:]
    return records


def admission(records: list[dict[str, Any]]) -> str:
    types = [int(r["type"]) for r in records]
    return "accept" if all(a < b for a, b in zip(types, types[1:])) else "reject"


def ref_transport_parse(data: bytes) -> tuple[int, int, bytes]:
    """Parse one BOLT 8 transport frame ``type || length || payload``.

    ``length`` is the whole Lightning message size, i.e. ``2 + len(payload)``.
    Rejects a header shorter than four bytes, a declared length below two (it
    could not even contain the type), a truncated payload, and trailing bytes.
    """
    if len(data) < 4:
        raise CheckError("missing-header")
    message_type = int.from_bytes(data[0:2], "big")
    declared = int.from_bytes(data[2:4], "big")
    payload = data[4:]
    if declared < 2:
        raise CheckError("length-too-small")
    if declared > len(payload) + 2:
        raise CheckError("truncated")
    if declared < len(payload) + 2:
        raise CheckError("trailing-bytes")
    return message_type, declared, payload


def require(condition: bool, message: str) -> None:
    if not condition:
        raise CheckError(message)


def check_bigsize_encode(entry: dict[str, Any], seen_ids: set[str]) -> None:
    where = f"bigsize.encode[{entry.get('id', '?')}]"
    for key in ("id", "category", "value", "bytes", "length", "source", "lean"):
        require(key in entry, f"{where}: missing key {key!r}")
    require(entry["id"] not in seen_ids, f"{where}: duplicate id {entry['id']!r}")
    seen_ids.add(entry["id"])

    raw = parse_hex(entry["bytes"], where)
    value = entry["value"]
    require(isinstance(value, int) and 0 <= value <= UINT64_MAX,
            f"{where}: value must be an integer in [0, 2^64-1]")
    expected = ref_bigsize_encode(value)
    require(raw == expected,
            f"{where}: bytes {raw.hex()} != reference {expected.hex()}")
    require(entry["length"] == len(raw),
            f"{where}: length {entry['length']} != {len(raw)} bytes")
    require(len(raw) in (1, 3, 5, 9),
            f"{where}: canonical BigSize length {len(raw)} is not 1/3/5/9")
    # Canonicality is self-consistent: decoding the bytes returns this value.
    decoded, consumed = ref_bigsize_decode(raw)
    require((decoded, consumed) == (value, len(raw)),
            f"{where}: self-decode {(decoded, consumed)} != {(value, len(raw))}")


def check_bigsize_decode(entry: dict[str, Any], seen_ids: set[str]) -> None:
    where = f"bigsize.decode[{entry.get('id', '?')}]"
    for key in ("id", "category", "bytes", "expect", "source", "lean"):
        require(key in entry, f"{where}: missing key {key!r}")
    require(entry["id"] not in seen_ids, f"{where}: duplicate id {entry['id']!r}")
    seen_ids.add(entry["id"])

    raw = parse_hex(entry["bytes"], where)
    expect = entry["expect"]
    require(isinstance(expect, dict) and "status" in expect,
            f"{where}: expect must be an object with a status")
    try:
        value, consumed = ref_bigsize_decode(raw)
    except CheckError as exc:
        reason = str(exc)
        require(expect["status"] == "reject",
                f"{where}: reference rejects ({reason}) but expect is {expect['status']}")
        require(expect.get("reason") == reason,
                f"{where}: reject reason {expect.get('reason')!r} != {reason!r}")
        return

    require(expect["status"] == "ok",
            f"{where}: reference accepts {(value, consumed)} but expect is reject")
    require(expect.get("value") == value,
            f"{where}: value {expect.get('value')} != {value}")
    require(expect.get("consumed") == consumed,
            f"{where}: consumed {expect.get('consumed')} != {consumed}")
    require(consumed <= len(raw),
            f"{where}: consumed {consumed} exceeds {len(raw)} input bytes")


def check_tlv_case(entry: dict[str, Any], seen_ids: set[str]) -> str:
    where = f"tlv.cases[{entry.get('id', '?')}]"
    for key in ("id", "category", "bytes", "parser", "admission", "spec",
                "model_scope", "source", "lean"):
        require(key in entry, f"{where}: missing key {key!r}")
    require(entry["id"] not in seen_ids, f"{where}: duplicate id {entry['id']!r}")
    seen_ids.add(entry["id"])

    raw = parse_hex(entry["bytes"], where)
    parser = entry["parser"]
    require(isinstance(parser, dict) and parser.get("decision") in ("accept", "reject"),
            f"{where}: parser.decision must be accept/reject")
    require(entry["admission"] in ("accept", "reject"),
            f"{where}: admission must be accept/reject")

    try:
        records = ref_tlv_parse(raw)
    except CheckError as exc:
        reason = str(exc)
        require(parser["decision"] == "reject",
                f"{where}: reference parser rejects ({reason}) but JSON says accept")
        require(parser.get("reason") == reason,
                f"{where}: parser reason {parser.get('reason')!r} != {reason!r}")
        require(entry["admission"] == "reject",
                f"{where}: a rejected parse cannot be admitted")
    else:
        require(parser["decision"] == "accept",
                f"{where}: reference parser accepts but JSON says reject")
        require(parser.get("records") == records,
                f"{where}: parser records {parser.get('records')} != {records}")
        require(entry["admission"] == admission(records),
                f"{where}: admission {entry['admission']} != {admission(records)}")

    spec = entry["spec"]
    require(isinstance(spec, dict) and spec.get("decision") in ("accept", "reject"),
            f"{where}: spec.decision must be accept/reject")
    scope = entry["model_scope"]
    if scope in ("enforced", "enforced-by-admission"):
        require(entry["admission"] == spec["decision"],
                f"{where}: BOLT decision {spec['decision']} is not enforced "
                f"(admission {entry['admission']})")
    elif scope.startswith("not-modelled:"):
        require(parser["decision"] == "accept",
                f"{where}: a not-modelled gap must be one the model accepts")
        require(entry["admission"] != spec["decision"],
                f"{where}: declared gap does not change the decision "
                f"(model {entry['admission']}, spec {spec['decision']})")
    else:
        raise CheckError(f"{where}: unknown model_scope {scope!r}")

    lean = entry["lean"]
    require(isinstance(lean, dict) and lean.get("decode") and lean.get("admission"),
            f"{where}: lean must name decode and admission theorems")
    return scope


def check_framing_case(entry: dict[str, Any], seen_ids: set[str]) -> str:
    where = f"framing.cases[{entry.get('id', '?')}]"
    for key in ("id", "category", "decision", "source", "lean"):
        require(key in entry, f"{where}: missing key {key!r}")
    require(entry["id"] not in seen_ids, f"{where}: duplicate id {entry['id']!r}")
    seen_ids.add(entry["id"])
    decision = entry["decision"]
    require(decision in ("accept", "reject"),
            f"{where}: decision must be accept/reject")

    if decision == "accept":
        for key in ("type", "payload", "declared_length", "frame"):
            require(key in entry, f"{where}: missing key {key!r}")
        payload = parse_hex(entry["payload"], where)
        raw = parse_hex(entry["frame"], where)
        message_type = entry["type"]
        require(isinstance(message_type, int) and 0 <= message_type <= 0xFFFF,
                f"{where}: type must be in [0, 65535]")
        declared = entry["declared_length"]
        require(isinstance(declared, int) and 2 <= declared <= 0xFFFF,
                f"{where}: declared_length must be in [2, 65535]")
        require(declared == 2 + len(payload),
                f"{where}: declared_length {declared} != 2 + {len(payload)}")
        expected = (message_type.to_bytes(2, "big") +
                    declared.to_bytes(2, "big") + payload)
        require(raw == expected,
                f"{where}: frame {raw.hex()} != reference {expected.hex()}")
        got_type, got_declared, got_payload = ref_transport_parse(raw)
        require((got_type, got_declared, got_payload) ==
                (message_type, declared, payload),
                f"{where}: parser result disagrees with the vector")
        return "accept"

    for key in ("bytes", "reason"):
        require(key in entry, f"{where}: missing key {key!r}")
    raw = parse_hex(entry["bytes"], where)
    try:
        ref_transport_parse(raw)
    except CheckError as exc:
        require(str(exc) == entry["reason"],
                f"{where}: reference rejects ({exc}) but reason is "
                f"{entry['reason']!r}")
        return "reject"
    raise CheckError(f"{where}: reference accepts but vector says reject")


def check_framing_boundary(entry: dict[str, Any], seen_ids: set[str]) -> None:
    where = f"framing.boundaries[{entry.get('id', '?')}]"
    for key in ("id", "payload_length", "declared_length", "length_hex",
                "frame_size", "fits", "header_truncated", "source", "lean"):
        require(key in entry, f"{where}: missing key {key!r}")
    require(entry["id"] not in seen_ids, f"{where}: duplicate id {entry['id']!r}")
    seen_ids.add(entry["id"])
    payload_length = entry["payload_length"]
    declared = entry["declared_length"]
    require(isinstance(payload_length, int) and payload_length >= 0,
            f"{where}: payload_length must be a non-negative integer")
    require(declared == 2 + payload_length,
            f"{where}: declared_length {declared} != 2 + {payload_length}")
    encoded = declared % 65536
    require(entry["length_hex"] == f"{encoded:04x}",
            f"{where}: length_hex {entry['length_hex']} != {encoded:04x} "
            f"(fixed two-byte truncation)")
    require(entry["frame_size"] == 4 + payload_length,
            f"{where}: frame_size {entry['frame_size']} != 4 + {payload_length}")
    fits = declared <= 0xFFFF
    require(entry["fits"] is fits,
            f"{where}: fits {entry['fits']} != {fits} for declared {declared}")
    require(entry["header_truncated"] is (declared > 0xFFFF),
            f"{where}: header_truncated is inconsistent with declared {declared}")


def check_framing(doc: dict[str, Any], seen_ids: set[str]) -> tuple[int, int, int]:
    framing = doc["framing"]
    require(isinstance(framing, dict), "framing must be an object")
    for key in ("layout", "length_semantics", "cases", "boundaries"):
        require(key in framing, f"framing missing {key!r}")
    require("2 + payload.size" in framing["length_semantics"],
            "framing.length_semantics must say transport_length = 2 + payload.size")
    cases = framing["cases"]
    boundaries = framing["boundaries"]
    accepted = rejected = 0
    for entry in cases:
        decision = check_framing_case(entry, seen_ids)
        if decision == "accept":
            accepted += 1
        else:
            rejected += 1
    for entry in boundaries:
        check_framing_boundary(entry, seen_ids)
    return len(cases), accepted, len(boundaries)


# ---------------------------------------------------------------------------
# Pinned rust-lightning differential fixtures
# ---------------------------------------------------------------------------

def rust_bigsize_class(data: bytes) -> tuple[str, tuple[int, int] | None]:
    """Map the model's Option decoder to rust-lightning's error classes.

    rust-lightning returns ``InvalidValue`` for a non-minimal encoding and
    ``ShortRead`` for every truncated/empty input.  The Lean model collapses
    both to ``none``; the differential fixture keeps the Rust class explicit.
    """
    try:
        return "ok", ref_bigsize_decode(data)
    except CheckError as exc:
        reason = str(exc)
        if reason in ("empty-input", "bigsize-short-read"):
            return "short-read", None
        if reason == "non-canonical-bigsize":
            return "invalid-value", None
        raise


def check_diff_bigsize(entry: dict[str, Any], seen_ids: set[str]) -> None:
    where = f"differential.bigsize[{entry.get('id', '?')}]"
    for key in ("id", "kind", "rust_result", "model_result", "lean", "source"):
        require(key in entry, f"{where}: missing key {key!r}")
    require(entry["id"] not in seen_ids, f"{where}: duplicate id {entry['id']!r}")
    seen_ids.add(entry["id"])
    if entry["kind"] == "encode":
        for key in ("value", "bytes"):
            require(key in entry, f"{where}: missing key {key!r}")
        value = entry["value"]
        require(isinstance(value, int) and 0 <= value <= UINT64_MAX,
                f"{where}: value must be a uint64")
        expected = ref_bigsize_encode(value)
        raw = parse_hex(entry["bytes"], where)
        require(raw == expected,
                f"{where}: bytes {raw.hex()} != reference {expected.hex()}")
        require(entry["rust_result"] == "ok" and entry["model_result"] == "ok",
                f"{where}: an encoding cannot have a reject result")
        return
    require(entry["kind"] == "decode", f"{where}: unknown kind {entry['kind']!r}")
    raw = parse_hex(entry["bytes"], where)
    rust_class, result = rust_bigsize_class(raw)
    require(entry["rust_result"] == rust_class,
            f"{where}: rust_result {entry['rust_result']!r} != {rust_class!r}")
    expected_model = "ok" if rust_class == "ok" else "reject"
    require(entry["model_result"] == expected_model,
            f"{where}: model_result {entry['model_result']!r} != {expected_model!r}")
    if result is not None:
        value, consumed = result
        require(entry.get("value") == value,
                f"{where}: value {entry.get('value')} != {value}")
        require(entry.get("consumed") == consumed,
                f"{where}: consumed {entry.get('consumed')} != {consumed}")


def check_diff_tlv(entry: dict[str, Any], seen_ids: set[str]) -> str:
    where = f"differential.tlv[{entry.get('id', '?')}]"
    for key in ("id", "kind", "bytes", "rust_result", "model_parser",
                "model_admission", "model_scope", "lean_decode",
                "lean_admission", "source"):
        require(key in entry, f"{where}: missing key {key!r}")
    require(entry["id"] not in seen_ids, f"{where}: duplicate id {entry['id']!r}")
    seen_ids.add(entry["id"])
    raw = parse_hex(entry["bytes"], where)
    try:
        records = ref_tlv_parse(raw)
        parsed = True
    except CheckError:
        records = []
        parsed = False
    require(entry["model_parser"] == ("accept" if parsed else "reject"),
            f"{where}: model_parser disagrees with the reference parser")
    if parsed:
        require(entry.get("expected_records") == records,
                f"{where}: expected_records {entry.get('expected_records')} != {records}")
        require(entry["model_admission"] == admission(records),
                f"{where}: model_admission disagrees with strict ordering")
    else:
        require(entry["model_admission"] == "reject",
                f"{where}: a rejected parse cannot be admitted")

    rust = entry["rust_result"]
    scope = entry["model_scope"]
    if rust == "accept":
        require(parsed, f"{where}: rust accepts but the reference parser rejects")
        require(scope == "enforced",
                f"{where}: an agreeing accept must be scoped enforced")
        require(entry["model_admission"] == "accept",
                f"{where}: rust accepts but the model admission rejects")
    elif rust == "unknown-required-feature":
        require(parsed, f"{where}: the structural stream must still parse")
        require(scope.startswith("not-modelled:"),
                f"{where}: an unknown-even rejection is a declared model gap")
        require(entry["model_admission"] == "accept",
                f"{where}: the declared gap must be a model accept")
    elif rust == "short-read":
        require(not parsed, f"{where}: rust reports ShortRead but the parser accepts")
        require(scope == "enforced",
                f"{where}: a short read must be enforced")
        require(entry["model_admission"] == "reject",
                f"{where}: a short read must be rejected")
    else:
        raise CheckError(f"{where}: unknown rust_result {rust!r}")
    return scope


def check_diff_wire(entry: dict[str, Any], seen_ids: set[str]) -> None:
    where = f"differential.wire[{entry.get('id', '?')}]"
    for key in ("id", "kind", "type", "transport_length", "header", "fits",
                "rust_result", "model_fits", "lean", "source"):
        require(key in entry, f"{where}: missing key {key!r}")
    require(entry["id"] not in seen_ids, f"{where}: duplicate id {entry['id']!r}")
    seen_ids.add(entry["id"])
    message_type = entry["type"]
    require(isinstance(message_type, int) and 0 <= message_type <= 0xFFFF,
            f"{where}: type must be in [0, 65535]")
    if "payload" in entry:
        payload_len = len(parse_hex(entry["payload"], where))
        if "payload_length" in entry:
            require(entry["payload_length"] == payload_len,
                    f"{where}: payload_length disagrees with payload bytes")
    else:
        require("payload_length" in entry,
                f"{where}: needs payload or payload_length")
        payload_len = entry["payload_length"]
    require(isinstance(payload_len, int) and payload_len >= 0,
            f"{where}: payload length must be non-negative")
    transport_length = 2 + payload_len
    require(entry["transport_length"] == transport_length,
            f"{where}: transport_length {entry['transport_length']} != "
            f"2 + {payload_len}")
    require(entry["header"] == f"{transport_length & 0xFFFF:04x}",
            f"{where}: header {entry['header']} != "
            f"{transport_length & 0xFFFF:04x}")
    fits = transport_length <= 0xFFFF
    require(entry["fits"] is fits,
            f"{where}: fits {entry['fits']} != {fits}")
    require(entry["model_fits"] is fits,
            f"{where}: model_fits {entry['model_fits']} != {fits}")
    require(entry["rust_result"] == ("accept" if fits else "reject"),
            f"{where}: rust_result must be accept iff the message fits")


def check_differential(doc: dict[str, Any], seen_ids: set[str]) -> tuple[int, int, int]:
    require(doc.get("schema") == "lnlean.rust-lightning.differential.v1",
            f"unexpected differential schema {doc.get('schema')!r}")
    require(doc.get("pinned_commit") ==
            "fe4900930c6bd5786ec4203274d7cf312776a5a6",
            "differential fixtures are not pinned to fe49009")
    require(doc.get("offline") is True,
            "differential fixtures must be marked offline")
    require(isinstance(doc.get("provenance"), list) and doc["provenance"],
            "differential provenance is missing")
    fixtures = doc.get("fixtures")
    require(isinstance(fixtures, dict), "differential fixtures must be an object")
    for key in ("bigsize", "tlv", "wire"):
        require(isinstance(fixtures.get(key), list) and fixtures[key],
                f"differential fixtures missing {key}")
    for entry in fixtures["bigsize"]:
        check_diff_bigsize(entry, seen_ids)
    scopes = [check_diff_tlv(entry, seen_ids) for entry in fixtures["tlv"]]
    for entry in fixtures["wire"]:
        check_diff_wire(entry, seen_ids)
    gaps = sum(1 for scope in scopes if scope.startswith("not-modelled:"))
    return len(fixtures["bigsize"]), len(fixtures["tlv"]), len(fixtures["wire"])


def check_bolt_anchors(doc: dict[str, Any]) -> int:
    """Assert the authoritative BOLT Appendix A subset is present exactly."""
    encode_by_value = {e["value"]: e for e in doc["bigsize"]["encode"]}
    decode_by_bytes = {e["bytes"]: e for e in doc["bigsize"]["decode"]}
    matched = 0
    for value, hx in BOLT_ENCODE:
        require(value in encode_by_value,
                f"BOLT anchor: missing encode vector for value {value}")
        require(encode_by_value[value]["bytes"] == hx,
                f"BOLT anchor: value {value} bytes "
                f"{encode_by_value[value]['bytes']} != {hx}")
        matched += 1
    for hx, status, value, consumed in BOLT_DECODE:
        require(hx in decode_by_bytes, f"BOLT anchor: missing decode vector {hx!r}")
        expect = decode_by_bytes[hx]["expect"]
        require(expect["status"] == status,
                f"BOLT anchor: {hx!r} status {expect['status']} != {status}")
        if status == "ok":
            require((expect.get("value"), expect.get("consumed")) == (value, consumed),
                    f"BOLT anchor: {hx!r} result "
                    f"{(expect.get('value'), expect.get('consumed'))} != {(value, consumed)}")
        matched += 1
    return matched


def check_required_categories(doc: dict[str, Any]) -> None:
    categories = {case["category"] for case in doc["tlv"]["cases"]}
    required = {"empty", "sorted", "duplicate", "out-of-domain"}
    missing = required - categories
    require(not missing, f"tlv: missing required categories {sorted(missing)}")
    bigsize_categories = {e["category"] for e in doc["bigsize"]["decode"]}
    require("canonical" in bigsize_categories and
            "non-canonical" in bigsize_categories and
            "short-read" in bigsize_categories,
            "bigsize.decode: missing canonical/non-canonical/short-read coverage")


# ---------------------------------------------------------------------------
# Lean cross-check
# ---------------------------------------------------------------------------

THEOREM_RE = re.compile(r"(?m)^theorem\s+([A-Za-z0-9_']+)")
DECL_RE = re.compile(r"(?m)^(?:theorem|def|abbrev)\s+([A-Za-z0-9_?']+)")
BYTES_RE = re.compile(r"bytes\s*\[([^\]]*)\]")
HEX_TOKEN_RE = re.compile(r"0x([0-9a-fA-F]+)")


def lean_declarations(text: str) -> dict[str, str]:
    """Map every top-level theorem/def/abbrev name to its source block.

    Namespace-qualified names are not needed here: the promoted transport
    module has the only declaration with each of the checked short names.
    """
    matches = list(DECL_RE.finditer(text))
    blocks: dict[str, str] = {}
    for index, match in enumerate(matches):
        end = matches[index + 1].start() if index + 1 < len(matches) else len(text)
        blocks[match.group(1)] = text[match.start():end]
    return blocks


def namespace_body(text: str, name: str) -> str:
    """Return the body between ``namespace <name>`` and its matching ``end``.

    The promoted transport names include ``fits_iff_payload``, which also exists
    in the enclosing ``LnLean.Wire`` namespace.  Restricting the declaration map
    to the transport namespace keeps that short-name collision from satisfying
    the promoted-model check.
    """
    match = re.search(
        rf"(?ms)^namespace\s+{re.escape(name)}\s*$(.*?)^end\s+{re.escape(name)}\s*$",
        text)
    require(match is not None,
            f"namespace {name} not found in LnLean/Wire/Message.lean")
    return match.group(1)


def check_decoder_boundary(text: str) -> None:
    """Keep the payload-only decoder payload-only and the transport decoder two bytes larger."""
    require("if rest.length = u16Nat c d then" in text,
            "payload decoder changed: unframeList no longer compares the "
            "declared field with the payload length")
    require("if u16Nat c d = rest.length + 2 then" in text,
            "transport decoder changed: unframeTransportList no longer "
            "compares the declared field with 2 + payload length")


def check_promoted_transport(decls: dict[str, str]) -> tuple[int, int]:
    """Require the BOLT 8 transport model in the production Wire module."""
    missing_theorems = [n for n in PROMOTED_TRANSPORT_THEOREMS if n not in decls]
    require(not missing_theorems,
            "promoted transport: missing theorems in LnLean/Wire/Message.lean: "
            + ", ".join(missing_theorems))
    missing_defs = [n for n in PROMOTED_TRANSPORT_DEFS if n not in decls]
    require(not missing_defs,
            "promoted transport: missing definitions in LnLean/Wire/Message.lean: "
            + ", ".join(missing_defs))
    # The boundary theorem must mention the payload-only decoder and the
    # promoted transport frame; this keeps the name from being satisfied by an
    # unrelated statement.
    boundary = decls["unframe_transportFrame_eq_none"]
    require("unframe" in boundary and "transportFrame" in boundary,
            "promoted transport: unframe_transportFrame_eq_none does not state "
            "the payload-decoder/transport-frame boundary")
    return len(PROMOTED_TRANSPORT_THEOREMS), len(PROMOTED_TRANSPORT_DEFS)


def check_generation(doc: dict[str, Any]) -> bool:
    """Validate the deterministic fixture-generation metadata."""
    generation = doc.get("generation")
    require(isinstance(generation, dict), "generation metadata is missing")
    script = generation.get("script")
    require(script == "tests/conformance/rust-lightning/generate.py",
            f"unexpected generation script {script!r}")
    require((ROOT / script).is_file(), f"generation script not found: {script}")
    mode = generation.get("mode")
    require(mode in ("transcribed-from-pinned-source", "live-cargo-test"),
            f"unexpected generation mode {mode!r}")
    live = generation.get("live_cargo_test")
    require(isinstance(live, bool), "generation.live_cargo_test must be a boolean")
    if live:
        require(bool(generation.get("live_transcript_sha256")),
                "a live cargo run must record live_transcript_sha256")
    return live


def check_provenance(doc: dict[str, Any], source_dir: Path) -> tuple[int, bool]:
    """Verify the committed fixture provenance against the pinned checkout."""
    provenance = doc.get("provenance")
    require(isinstance(provenance, list) and provenance,
            "differential provenance is missing")
    verified = 0
    for entry in provenance:
        rel = entry.get("path")
        require(isinstance(rel, str) and rel,
                "provenance entry is missing a path")
        path = source_dir / rel
        require(path.is_file(), f"provenance file not found: {path}")
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        require(digest == entry.get("sha256"),
                f"provenance sha256 mismatch for {rel}: {digest} != "
                f"{entry.get('sha256')}")
        verified += 1
    commit_verified = False
    if (source_dir / ".git").exists():
        try:
            result = subprocess.run(
                ["git", "-C", str(source_dir), "rev-parse", "HEAD"],
                capture_output=True, text=True, check=False)
        except OSError:
            result = None
        if result is not None and result.returncode == 0:
            head = result.stdout.strip()
            require(head == doc["pinned_commit"],
                    f"pinned checkout HEAD {head} != {doc['pinned_commit']}")
            commit_verified = True
    return verified, commit_verified


def lean_theorems(text: str) -> dict[str, str]:
    matches = list(THEOREM_RE.finditer(text))
    blocks: dict[str, str] = {}
    for index, match in enumerate(matches):
        end = matches[index + 1].start() if index + 1 < len(matches) else len(text)
        blocks[match.group(1)] = text[match.start():end]
    return blocks


def byte_literals(block: str) -> list[bytes]:
    out: list[bytes] = []
    for match in BYTES_RE.finditer(block):
        tokens = HEX_TOKEN_RE.findall(match.group(1))
        out.append(bytes(int(token, 16) for token in tokens))
    return out


def load_lean_theorems(lean_paths: list[Path]) -> dict[str, str]:
    merged: dict[str, str] = {}
    for lean_path in lean_paths:
        require(lean_path.is_file(), f"Lean module not found: {lean_path}")
        for name, block in lean_theorems(lean_path.read_text(encoding="utf-8")).items():
            require(name not in merged,
                    f"duplicate theorem {name!r} in {lean_path}")
            merged[name] = block
    return merged


def check_lean_sync(doc: dict[str, Any], theorems: dict[str, str]) -> int:
    checked = 0

    for entry in doc["bigsize"]["encode"]:
        name = entry["lean"]
        where = f"lean[{name}]"
        require(name in theorems, f"{where}: theorem not declared")
        literals = byte_literals(theorems[name])
        expected = parse_hex(entry["bytes"], where)
        require(expected in literals,
                f"{where}: statement does not mention bytes {entry['bytes']}")
        checked += 1

    for entry in doc["bigsize"]["decode"]:
        name = entry["lean"]
        where = f"lean[{name}]"
        require(name in theorems, f"{where}: theorem not declared")
        block = theorems[name]
        literals = byte_literals(block)
        raw = parse_hex(entry["bytes"], where)
        require(bool(literals) and literals[0] == raw,
                f"{where}: first byte literal is not input {entry['bytes']}")
        if entry["expect"]["status"] == "ok":
            value = entry["expect"]["value"]
            consumed = entry["expect"]["consumed"]
            require(re.search(rf"some\s*\(\s*{value}\s*,\s*{consumed}\s*\)", block),
                    f"{where}: statement does not contain some ({value}, {consumed})")
        else:
            require("= none" in block or "=none" in block,
                    f"{where}: reject statement does not conclude none")
        checked += 1

    for entry in doc["tlv"]["cases"]:
        name = entry["lean"]["decode"]
        where = f"lean[{name}]"
        require(name in theorems, f"{where}: theorem not declared")
        block = theorems[name]
        literals = byte_literals(block)
        raw = parse_hex(entry["bytes"], where)
        require(bool(literals) and literals[0] == raw,
                f"{where}: first byte literal is not input {entry['bytes']}")
        if entry["parser"]["decision"] == "accept":
            for record in entry["parser"]["records"]:
                value = parse_hex(record["value"], where)
                require(value in literals,
                        f"{where}: record value {record['value']} absent from statement")
        else:
            require("= none" in block or "=none" in block,
                    f"{where}: reject statement does not conclude none")
        checked += 1

        adm_name = entry["lean"]["admission"]
        adm_where = f"lean[{adm_name}]"
        require(adm_name in theorems, f"{adm_where}: theorem not declared")
        expected = "= true" if entry["admission"] == "accept" else "= false"
        require(expected in theorems[adm_name],
                f"{adm_where}: admission theorem does not conclude {expected.strip()}")
        checked += 1

    return checked


def check_framing_lean_sync(doc: dict[str, Any], theorems: dict[str, str]) -> int:
    checked = 0
    for entry in doc["framing"]["cases"]:
        name = entry["lean"]
        where = f"lean[{name}]"
        require(name in theorems, f"{where}: theorem not declared")
        block = theorems[name]
        literals = byte_literals(block)
        if entry["decision"] == "accept":
            require(parse_hex(entry["frame"], where) in literals,
                    f"{where}: statement does not mention frame {entry['frame']}")
            require(parse_hex(entry["payload"], where) in literals,
                    f"{where}: statement does not mention payload {entry['payload']}")
        else:
            raw = parse_hex(entry["bytes"], where)
            require(bool(literals) and literals[0] == raw,
                    f"{where}: first byte literal is not input {entry['bytes']}")
            require("= none" in block or "=none" in block,
                    f"{where}: reject statement does not conclude none")
        checked += 1

    for entry in doc["framing"]["boundaries"]:
        name = entry["lean"]
        where = f"lean[{name}]"
        require(name in theorems, f"{where}: theorem not declared")
        block = theorems[name]
        require(str(entry["payload_length"]) in block,
                f"{where}: statement does not mention payload length "
                f"{entry['payload_length']}")
        require(str(entry["declared_length"]) in block,
                f"{where}: statement does not mention transport length "
                f"{entry['declared_length']}")
        checked += 1
    return checked


def check_differential_lean_sync(doc: dict[str, Any],
                                 theorems: dict[str, str]) -> int:
    checked = 0
    fixtures = doc["fixtures"]
    for entry in fixtures["bigsize"]:
        name = entry["lean"]
        where = f"lean[{name}]"
        require(name in theorems, f"{where}: theorem not declared")
        block = theorems[name]
        literals = byte_literals(block)
        raw = parse_hex(entry["bytes"], where)
        require(bool(literals) and raw in literals,
                f"{where}: statement does not mention bytes {entry['bytes']}")
        if entry["kind"] == "encode":
            require(str(entry["value"]) in block,
                    f"{where}: statement does not mention value {entry['value']}")
        elif entry["rust_result"] == "ok":
            value = entry["value"]
            consumed = entry["consumed"]
            require(re.search(rf"some\s*\(\s*{value}\s*,\s*{consumed}\s*\)", block),
                    f"{where}: statement does not contain some ({value}, {consumed})")
        else:
            require("= none" in block or "=none" in block,
                    f"{where}: reject statement does not conclude none")
        checked += 1

    for entry in fixtures["tlv"]:
        name = entry["lean_decode"]
        where = f"lean[{name}]"
        require(name in theorems, f"{where}: theorem not declared")
        block = theorems[name]
        literals = byte_literals(block)
        raw = parse_hex(entry["bytes"], where)
        require(bool(literals) and literals[0] == raw,
                f"{where}: first byte literal is not input {entry['bytes']}")
        if entry["model_parser"] == "accept":
            for record in entry["expected_records"]:
                value = parse_hex(record["value"], where)
                require(value in literals,
                        f"{where}: record value {record['value']} absent")
        else:
            require("= none" in block or "=none" in block,
                    f"{where}: reject statement does not conclude none")
        checked += 1

        adm_name = entry["lean_admission"]
        adm_where = f"lean[{adm_name}]"
        require(adm_name in theorems, f"{adm_where}: theorem not declared")
        expected = "= true" if entry["model_admission"] == "accept" else "= false"
        require(expected in theorems[adm_name],
                f"{adm_where}: admission theorem does not conclude {expected.strip()}")
        checked += 1

    for entry in fixtures["wire"]:
        name = entry["lean"]
        where = f"lean[{name}]"
        require(name in theorems, f"{where}: theorem not declared")
        require(str(entry["transport_length"]) in theorems[name],
                f"{where}: statement does not mention transport length "
                f"{entry['transport_length']}")
        checked += 1
    return checked


# ---------------------------------------------------------------------------
# Mutation controls (the checker itself must not be vacuous)
# ---------------------------------------------------------------------------

def mutation_detected(validate: Any) -> bool:
    try:
        validate()
    except CheckError:
        return True
    return False


def check_mutations(doc: dict[str, Any], diff_doc: dict[str, Any] | None,
                    theorems: dict[str, str] | None,
                    message_decls: dict[str, str] | None) -> tuple[int, int]:
    caught = 0
    total = 0

    def control(label: str, validate: Any) -> None:
        nonlocal caught, total
        total += 1
        if not mutation_detected(validate):
            raise CheckError(f"mutation control not detected: {label}")
        caught += 1

    mutated = copy.deepcopy(doc)
    valid = next(e for e in mutated["framing"]["cases"]
                 if e["decision"] == "accept")
    valid["declared_length"] += 1
    control("framing declared length +1",
            lambda: check_framing_case(valid, set()))

    mutated = copy.deepcopy(doc)
    bad = next(e for e in mutated["framing"]["cases"]
               if e["decision"] == "reject")
    bad["reason"] = "wrong-reason"
    control("framing reject reason changed",
            lambda: check_framing_case(bad, set()))

    mutated = copy.deepcopy(doc)
    boundary = mutated["framing"]["boundaries"][-1]
    boundary["fits"] = not boundary["fits"]
    control("framing boundary fits flipped",
            lambda: check_framing_boundary(boundary, set()))

    if diff_doc is not None:
        mutated = copy.deepcopy(diff_doc)
        decode = next(e for e in mutated["fixtures"]["bigsize"]
                      if e["kind"] == "decode" and e["rust_result"] == "ok")
        decode["bytes"] = "01" if decode["bytes"] == "00" else "00"
        control("differential BigSize bytes changed",
                lambda: check_diff_bigsize(decode, set()))

        mutated = copy.deepcopy(diff_doc)
        wire = mutated["fixtures"]["wire"][0]
        wire["transport_length"] += 1
        control("differential wire transport length +1",
                lambda: check_diff_wire(wire, set()))

        mutated = copy.deepcopy(diff_doc)
        tlv = next(e for e in mutated["fixtures"]["tlv"]
                   if e["model_parser"] == "accept")
        tlv["expected_records"][0]["value"] = "00000000"
        control("differential TLV record value changed",
                lambda: check_diff_tlv(tlv, set()))

        mutated = copy.deepcopy(diff_doc)
        mutated["generation"]["live_cargo_test"] = True
        control("fixture generation claims a live run without a transcript",
                lambda: check_generation(mutated))

    if theorems is not None:
        mutated_theorems = dict(theorems)
        name = doc["framing"]["cases"][0]["lean"]
        mutated_theorems.pop(name, None)
        control("framing Lean theorem reference removed",
                lambda: check_framing_lean_sync(doc, mutated_theorems))

    if message_decls is not None:
        mutated_decls = dict(message_decls)
        mutated_decls.pop("unframeTransport_transportFrame", None)
        control("promoted transport theorem removed",
                lambda: check_promoted_transport(mutated_decls))

    return caught, total


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def run(vectors: Path, lean_paths: list[Path] | None, diff_path: Path | None,
        verbose: bool, self_test: bool, source_dir: Path | None,
        check_sources: bool) -> int:
    try:
        doc = json.loads(vectors.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        print(f"FAIL: cannot read {vectors}: {exc}", file=sys.stderr)
        return 2
    diff_doc: dict[str, Any] | None = None
    if diff_path is not None:
        try:
            diff_doc = json.loads(diff_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            print(f"FAIL: cannot read {diff_path}: {exc}", file=sys.stderr)
            return 2

    try:
        require(isinstance(doc, dict), "top level must be an object")
        require(doc.get("schema") == "lnlean.conformance.v1",
                f"unexpected schema {doc.get('schema')!r}")
        for key in ("scope", "sources", "bigsize", "tlv", "framing"):
            require(key in doc, f"top level missing {key!r}")
        require("NOT a full implementation test" in doc["scope"],
                "scope must state that this is not a full implementation test")

        seen_ids: set[str] = set()
        for entry in doc["bigsize"]["encode"]:
            check_bigsize_encode(entry, seen_ids)
        for entry in doc["bigsize"]["decode"]:
            check_bigsize_decode(entry, seen_ids)
        scopes = [check_tlv_case(entry, seen_ids) for entry in doc["tlv"]["cases"]]
        check_required_categories(doc)
        anchors = check_bolt_anchors(doc)
        framing_cases, framing_accept, framing_boundaries = check_framing(
            doc, seen_ids)

        diff_bigsize = diff_tlv = diff_wire = 0
        diff_scopes: list[str] = []
        live_fixtures = False
        if diff_doc is not None:
            live_fixtures = check_generation(diff_doc)
            diff_bigsize, diff_tlv, diff_wire = check_differential(diff_doc, seen_ids)
            diff_scopes = [entry["model_scope"]
                           for entry in diff_doc["fixtures"]["tlv"]]

        provenance_count: int | None = None
        commit_verified = False
        if diff_doc is not None and check_sources:
            if source_dir is not None and source_dir.is_dir():
                provenance_count, commit_verified = check_provenance(
                    diff_doc, source_dir)

        theorems: dict[str, str] | None = None
        message_decls: dict[str, str] | None = None
        lean_checks = 0
        promoted_theorems = promoted_defs = 0
        if lean_paths is not None:
            theorems = load_lean_theorems(lean_paths)
            lean_checks += check_lean_sync(doc, theorems)
            lean_checks += check_framing_lean_sync(doc, theorems)
            if diff_doc is not None:
                lean_checks += check_differential_lean_sync(diff_doc, theorems)
            require(DEFAULT_MESSAGE.is_file(),
                    f"promoted transport module not found: {DEFAULT_MESSAGE}")
            message_text = DEFAULT_MESSAGE.read_text(encoding="utf-8")
            check_decoder_boundary(message_text)
            message_decls = lean_declarations(
                namespace_body(message_text, "Transport"))
            promoted_theorems, promoted_defs = check_promoted_transport(
                message_decls)

        mutations_caught = mutations_total = 0
        if self_test:
            mutations_caught, mutations_total = check_mutations(
                doc, diff_doc, theorems, message_decls)
    except CheckError as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        return 1

    encode_n = len(doc["bigsize"]["encode"])
    decode_n = len(doc["bigsize"]["decode"])
    tlv_n = len(doc["tlv"]["cases"])
    gaps = sum(1 for scope in scopes if scope.startswith("not-modelled:"))
    enforced = tlv_n - gaps
    diff_gaps = sum(1 for scope in diff_scopes if scope.startswith("not-modelled:"))

    if verbose:
        for entry in doc["bigsize"]["encode"]:
            print(f"  bigsize.encode {entry['id']:<40} {entry['bytes']}")
        for entry in doc["bigsize"]["decode"]:
            result = entry["expect"]
            suffix = (f"({result['value']}, {result['consumed']})"
                      if result["status"] == "ok" else f"reject:{result['reason']}")
            print(f"  bigsize.decode {entry['id']:<40} {entry['bytes']:<20} {suffix}")
        for entry in doc["tlv"]["cases"]:
            print(f"  tlv            {entry['id']:<40} {entry['bytes']:<26} "
                  f"parser={entry['parser']['decision']:<6} "
                  f"admission={entry['admission']:<6} scope={entry['model_scope']}")
        for entry in doc["framing"]["cases"]:
            print(f"  framing        {entry['id']:<40} "
                  f"{entry.get('frame', entry.get('bytes')):<26} "
                  f"{entry['decision']}")
        for entry in doc["framing"]["boundaries"]:
            print(f"  boundary       {entry['id']:<40} "
                  f"payload={entry['payload_length']:<7} "
                  f"length={entry['declared_length']:<7} "
                  f"fits={entry['fits']}")
        if diff_doc is not None:
            for group in ("bigsize", "tlv", "wire"):
                for entry in diff_doc["fixtures"][group]:
                    print(f"  rust.{group:<9} {entry['id']:<40} "
                          f"rust={entry['rust_result']}")

    print(f"vectors: {encode_n} BigSize encode, {decode_n} BigSize decode, {tlv_n} TLV")
    print(f"checks:  {encode_n + decode_n + tlv_n} vector expectations validated")
    print(f"BOLT 1 Appendix A anchors: {anchors} published entries matched")
    print(f"TLV: {enforced} enforced cases, {gaps} declared not-modelled gaps")
    print(f"framing: {framing_cases} cases ({framing_accept} accept, "
          f"{framing_cases - framing_accept} reject), "
          f"{framing_boundaries} length boundaries")
    if diff_doc is not None:
        print(f"differential: {diff_bigsize} rust-lightning BigSize, "
              f"{diff_tlv} TLV, {diff_wire} wire fixtures "
              f"(pinned {diff_doc['pinned_commit'][:7]}, offline)")
        print(f"differential TLV: {diff_tlv - diff_gaps} enforced, "
              f"{diff_gaps} declared not-modelled gaps")
        print(f"fixture generation: "
              f"{'live-cargo-test' if live_fixtures else 'transcribed-from-pinned-source'} "
              f"(live cargo test: {'yes' if live_fixtures else 'no'})")
        if provenance_count is not None:
            commit_note = " (HEAD verified)" if commit_verified else ""
            print(f"provenance: {provenance_count} pinned rust-lightning source "
                  f"files verified{commit_note}")
        elif check_sources:
            print("provenance: skipped (pinned source checkout not present)")
        else:
            print("provenance: skipped (--no-provenance)")
    if lean_paths is not None:
        display = ", ".join(str(path.relative_to(ROOT))
                            if path.is_relative_to(ROOT) else str(path)
                            for path in lean_paths)
        print(f"Lean sync: {lean_checks} theorem references checked in {display}")
        print(f"promoted transport: {promoted_theorems}/"
              f"{len(PROMOTED_TRANSPORT_THEOREMS)} theorems, "
              f"{promoted_defs}/{len(PROMOTED_TRANSPORT_DEFS)} definitions "
              f"checked in LnLean/Wire/Message.lean")
    else:
        print("Lean sync: skipped (--no-lean)")
    if self_test:
        print(f"mutation controls: {mutations_caught}/{mutations_total} detected")
    else:
        print("mutation controls: skipped (--no-self-test)")
    print("RESULT: PASS (vector/differential conformance, "
          "not a full implementation test)")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=("Validate ln-lean BOLT 1 BigSize/TLV, BOLT 8 transport "
                     "framing, and pinned rust-lightning differential fixtures."))
    parser.add_argument("--vectors", type=Path, default=DEFAULT_VECTORS,
                        help=f"vector JSON (default: {DEFAULT_VECTORS})")
    parser.add_argument("--diff-fixtures", type=Path, default=DEFAULT_DIFF,
                        help=f"rust-lightning fixture JSON (default: {DEFAULT_DIFF})")
    parser.add_argument("--lean-file", type=Path, action="append", default=None,
                        help="Lean theorem module (repeatable; defaults to both "
                             "ConformanceTargets and ConformanceDiffTargets)")
    parser.add_argument("--no-diff", action="store_true",
                        help="skip the pinned rust-lightning differential fixtures")
    parser.add_argument("--no-lean", action="store_true",
                        help="skip the Lean theorem-name/byte-literal cross-check")
    parser.add_argument("--no-self-test", action="store_true",
                        help="skip the in-memory mutation controls")
    parser.add_argument("--source-dir", type=Path, default=DEFAULT_SOURCE,
                        help="pinned rust-lightning checkout for provenance "
                             f"verification (default: {DEFAULT_SOURCE})")
    parser.add_argument("--no-provenance", action="store_true",
                        help="skip the pinned-source SHA-256/HEAD verification")
    parser.add_argument("--verbose", action="store_true",
                        help="print every vector")
    args = parser.parse_args(argv)
    if args.no_lean:
        lean_paths = None
    elif args.lean_file:
        lean_paths = args.lean_file
    else:
        lean_paths = [DEFAULT_LEAN, DEFAULT_LEAN_DIFF]
    diff_path = None if args.no_diff else args.diff_fixtures
    return run(args.vectors, lean_paths, diff_path, args.verbose,
               not args.no_self_test, args.source_dir, not args.no_provenance)


if __name__ == "__main__":
    raise SystemExit(main())

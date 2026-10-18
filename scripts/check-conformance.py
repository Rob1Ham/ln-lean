#!/usr/bin/env python3
"""Validate the S4-CONFORMANCE wire vectors.

This checker is deliberately small and dependency-free.  It does three things:

1. Recomputes every BigSize encoding and decoding decision with an independent
   reference implementation and compares it to ``tests/conformance/vectors.json``.
2. Recomputes every TLV structural parse and ordering-admission decision.  The
   parser and admission phases are kept separate because the Lean model's
   ``decodeTLV`` is structural only; BOLT 1 ordering is enforced by
   ``decodeAdmissible``.
3. Cross-checks that every vector names a theorem that exists in
   ``LnLean/Proofs/ConformanceTargets.lean`` and that the theorem statement
   mentions the vector's input bytes (and, where applicable, its value).

It does **not** run Lean.  The Lean module proves the same expectations by
``decide`` and is checked by ``lake build LnLean.Proofs.ConformanceTargets``.
This is vector conformance, not a full implementation test.

Usage:
    python3 scripts/check-conformance.py
    python3 scripts/check-conformance.py --no-lean
    python3 scripts/check-conformance.py --verbose

Exit status: 0 on success, 1 on a vector/Lean-sync mismatch, 2 on usage/IO.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
DEFAULT_VECTORS = ROOT / "tests" / "conformance" / "vectors.json"
DEFAULT_LEAN = ROOT / "LnLean" / "Proofs" / "ConformanceTargets.lean"

UINT64_MAX = 2**64 - 1

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
BYTES_RE = re.compile(r"bytes\s*\[([^\]]*)\]")
HEX_TOKEN_RE = re.compile(r"0x([0-9a-fA-F]+)")


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


def check_lean_sync(doc: dict[str, Any], lean_path: Path) -> int:
    require(lean_path.is_file(), f"Lean module not found: {lean_path}")
    text = lean_path.read_text(encoding="utf-8")
    theorems = lean_theorems(text)
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


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def run(vectors: Path, lean_path: Path | None, verbose: bool) -> int:
    try:
        doc = json.loads(vectors.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        print(f"FAIL: cannot read {vectors}: {exc}", file=sys.stderr)
        return 2

    try:
        require(isinstance(doc, dict), "top level must be an object")
        require(doc.get("schema") == "lnlean.conformance.v1",
                f"unexpected schema {doc.get('schema')!r}")
        for key in ("scope", "sources", "bigsize", "tlv"):
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
        lean_checks = 0
        if lean_path is not None:
            lean_checks = check_lean_sync(doc, lean_path)
    except CheckError as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        return 1

    encode_n = len(doc["bigsize"]["encode"])
    decode_n = len(doc["bigsize"]["decode"])
    tlv_n = len(doc["tlv"]["cases"])
    gaps = sum(1 for scope in scopes if scope.startswith("not-modelled:"))
    enforced = tlv_n - gaps

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

    print(f"vectors: {encode_n} BigSize encode, {decode_n} BigSize decode, {tlv_n} TLV")
    print(f"checks:  {encode_n + decode_n + tlv_n} vector expectations validated")
    print(f"BOLT 1 Appendix A anchors: {anchors} published entries matched")
    print(f"TLV: {enforced} enforced cases, {gaps} declared not-modelled gaps")
    if lean_path is not None:
        try:
            display_path = lean_path.relative_to(ROOT)
        except ValueError:
            display_path = lean_path
        print(f"Lean sync: {lean_checks} theorem references checked in {display_path}")
    else:
        print("Lean sync: skipped (--no-lean)")
    print("RESULT: PASS (vector conformance, not a full implementation test)")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Validate ln-lean BOLT 1 BigSize/TLV conformance vectors.")
    parser.add_argument("--vectors", type=Path, default=DEFAULT_VECTORS,
                        help=f"vector JSON (default: {DEFAULT_VECTORS})")
    parser.add_argument("--lean-file", type=Path, default=DEFAULT_LEAN,
                        help=f"Lean vector module (default: {DEFAULT_LEAN})")
    parser.add_argument("--no-lean", action="store_true",
                        help="skip the Lean theorem-name/byte-literal cross-check")
    parser.add_argument("--verbose", action="store_true",
                        help="print every vector")
    args = parser.parse_args(argv)
    lean_path = None if args.no_lean else args.lean_file
    return run(args.vectors, lean_path, args.verbose)


if __name__ == "__main__":
    raise SystemExit(main())

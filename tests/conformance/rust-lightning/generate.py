#!/usr/bin/env python3
"""Deterministically re-derive and verify the pinned rust-lightning fixtures.

The committed ``fixtures.json`` is a *transcription* of the pinned
rust-lightning source at commit ``fe49009``.  This script closes the
reproducibility gap without requiring a Rust toolchain:

1. It verifies the SHA-256 of each source file recorded in ``provenance``.
2. It re-extracts the literal vectors from the pinned unit tests
   (``bigsize_encoding_decoding`` and ``retired_tlvs_skipped_on_read``) and
   the length-header constants from ``peer_channel_encryptor.rs``.
3. It compares every derived value with ``fixtures.json`` (``--check``,
   the default) or rewrites the derived fields deterministically
   (``--write``).

``--live`` is the only mode that invokes ``cargo``.  It copies the pinned
checkout to a disposable directory, installs the committed ``pinned/Cargo.lock``
and the public-API probe ``live_probe.rs``, runs the pinned unit tests with
``--offline --locked``, then runs the probe and compares every BigSize/TLV
fixture field and the BOLT 2 ``channel_ready`` payload against the live
rust-lightning result.  The wire fixtures are compared against the live
``LN_MAX_MSG_LEN`` constant; their header arithmetic is still the pinned source
check performed by ``extract_wire``.  On success it writes a deterministic
transcript; it never claims a live result on failure.

The cargo cache is a machine-level artifact, not part of this tree.  ``--fetch``
performs one online ``cargo fetch --locked`` to complete the cache, after which
``--offline --locked`` is the only mode used for the actual run.  ``--record``
(with ``--live``) records the transcript hash in ``fixtures.json`` after a
successful run; ``--check`` then verifies that hash and the transcript's
fixture/probe/lock provenance.

Usage::

    python3 tests/conformance/rust-lightning/generate.py --check
    python3 tests/conformance/rust-lightning/generate.py --write
    python3 tests/conformance/rust-lightning/generate.py --live
    python3 tests/conformance/rust-lightning/generate.py --live --fetch --record

Exit status: 0 success, 1 fixture/provenance mismatch, 2 usage/IO,
4 a requested live cargo run failed (offline cache incomplete or tests failed).
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent.parent
DEFAULT_SOURCE = ROOT / "refs" / "rust-lightning"
DEFAULT_FIXTURES = HERE / "fixtures.json"
PINNED_LOCK = HERE / "pinned" / "Cargo.lock"
LIVE_PROBE = HERE / "live_probe.rs"
DEFAULT_TRANSCRIPT = HERE / "live-transcript.json"
LIVE_TRANSCRIPT_SCHEMA = "lnlean.rust-lightning.live-transcript.v1"

PINNED_COMMIT = "fe4900930c6bd5786ec4203274d7cf312776a5a6"
LIVE_TESTS = [
    "util::ser::tests::bigsize_encoding_decoding",
    "util::ser_macros::tests::retired_tlvs_skipped_on_read",
    "ln::msgs::tests::encoding_channel_ready",
]
LIVE_NOTE = (
    "The committed rows were extracted from the pinned source/unit-test "
    "literals; `generate.py --check` re-extracts and compares them. "
    "`generate.py --live --fetch` ran the pinned unit tests and the public-API "
    "probe under `cargo --offline --locked` with the committed "
    "`pinned/Cargo.lock`; `live-transcript.json` records the comparison. "
    "The BOLT 2 channel_ready payload is encoded live through the pinned "
    "`Writeable` impl; the wire header arithmetic remains a pinned-source "
    "check and only `LN_MAX_MSG_LEN` is probed live."
)
OFFLINE_NOTE = (
    "The committed rows were extracted from the pinned source/unit-test "
    "literals; `generate.py --check` re-extracts and compares them, and "
    "`generate.py --live` runs the pinned cargo tests only when the "
    "offline cache is complete. No live cargo result is claimed here."
)

PROVENANCE = [
    {
        "path": "lightning/src/util/ser.rs",
        "sha256": "dbb5d75974be6de06d6e4da83157c93c87476fed1ef79fa60b228facb2a3101b",
        "lines": "1857-1901",
        "use": "BigSize encode/decode values and InvalidValue/ShortRead error "
               "classes (bigsize_encoding_decoding unit test)",
    },
    {
        "path": "lightning/src/util/ser_macros.rs",
        "sha256": "57bb7c0229f6f8142e7e10542a82fd0f6980f22d1263c1926cf741a24dc8fa12",
        "lines": "2047-2071",
        "use": "TLV reader accepted stream, unknown-even rejection, truncated "
               "ShortRead (retired_tlvs_skipped_on_read unit test)",
    },
    {
        "path": "lightning/src/ln/peer_channel_encryptor.rs",
        "sha256": "8e3eac2332669763104bf2da6c43aa44a429a4cb46b3fec41de56cdd2e9f28d9",
        "lines": "36, 518-540, 564-580",
        "use": "LN_MAX_MSG_LEN = 65535; length header is msgbuf.len() - 16 - 2 "
               "(type plus payload)",
    },
    {
        "path": "lightning/src/ln/wire.rs",
        "sha256": "01aa058e40a0186b6bc4862642c63b8f17f534572e96196f862959b75410531a",
        "lines": "251-265",
        "use": "a message is a 2-byte big-endian type plus a variable payload",
    },
    {
        "path": "lightning/src/ln/msgs.rs",
        "sha256": "75bc3698ab6e5595dcb02de23dceb52e37a25cd31621947387054fab2461a4f8",
        "lines": "431-443, 3239-3243, 5672-5682",
        "use": "BOLT 2 channel_ready (type 36) field order/Writeable encoding and "
               "the encoding_channel_ready unit-test target value",
    },
]

HEX_RE = re.compile(r'"([0-9a-f]*)"')
INT_RE = re.compile(r"\b(\d+)\b")
FUNCTION_RE = r"fn\s+%s\s*\(\)\s*\{"
LET_ARRAY_RE = r"let\s+%s\s*=\s*\[(.*?)\];"


class FixtureError(Exception):
    """A fixture/provenance mismatch."""


class LiveError(Exception):
    """A requested live cargo/probe run failed."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise FixtureError(message)


def function_body(text: str, name: str) -> str:
    match = re.search(FUNCTION_RE % re.escape(name), text)
    require(match is not None, f"pinned test function not found: {name}")
    start = match.end()
    depth = 1
    index = start
    while index < len(text) and depth:
        if text[index] == "{":
            depth += 1
        elif text[index] == "}":
            depth -= 1
        index += 1
    require(depth == 0, f"unbalanced braces after {name}")
    return text[start:index - 1]


def let_array(body: str, name: str) -> str:
    match = re.search(LET_ARRAY_RE % re.escape(name), body, re.DOTALL)
    require(match is not None, f"array literal not found: let {name}")
    return match.group(1)


def hex_strings(fragment: str) -> list[str]:
    return HEX_RE.findall(fragment)


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verify_provenance(source: Path) -> None:
    require(source.is_dir(), f"pinned source checkout not found: {source}")
    for entry in PROVENANCE:
        path = source / entry["path"]
        require(path.is_file(), f"provenance file not found: {path}")
        digest = sha256_file(path)
        require(digest == entry["sha256"],
                f"provenance sha256 mismatch for {entry['path']}: "
                f"{digest} != {entry['sha256']}")
    if (source / ".git").exists():
        try:
            result = subprocess.run(
                ["git", "-C", str(source), "rev-parse", "HEAD"],
                capture_output=True, text=True, check=False)
        except OSError:
            result = None
        if result is not None and result.returncode == 0:
            head = result.stdout.strip()
            require(head == PINNED_COMMIT,
                    f"pinned checkout HEAD {head} != {PINNED_COMMIT}")


def extract_bigsize(source: Path) -> tuple[list[int], list[str], list[str]]:
    text = (source / "lightning/src/util/ser.rs").read_text(encoding="utf-8")
    body = function_body(text, "bigsize_encoding_decoding")
    values = [int(token) for token in INT_RE.findall(let_array(body, "values"))]
    byte_rows = hex_strings(let_array(body, "bytes"))
    errors = hex_strings(let_array(body, "err_bytes"))
    require(len(values) == 8, f"expected 8 BigSize values, got {len(values)}")
    require(len(byte_rows) == 8, f"expected 8 BigSize encodings, got {len(byte_rows)}")
    require(len(errors) == 10, f"expected 10 BigSize error inputs, got {len(errors)}")
    return values, byte_rows, errors


def first_tlv_record(data: bytes) -> bytes:
    """Return the first complete TLV record (BigSize type || BigSize length || value)."""
    def bigsize_at(offset: int) -> tuple[int, int]:
        require(offset < len(data), "truncated BigSize in TLV stream")
        tag = data[offset]
        if tag < 0xFD:
            return tag, offset + 1
        width = {0xFD: 2, 0xFE: 4, 0xFF: 8}[tag]
        require(offset + 1 + width <= len(data), "short BigSize in TLV stream")
        return int.from_bytes(data[offset + 1:offset + 1 + width], "big"), \
            offset + 1 + width

    _, after_type = bigsize_at(0)
    length, after_length = bigsize_at(after_type)
    require(after_length + length <= len(data), "short TLV value")
    return data[:after_length + length]


def extract_tlv(source: Path) -> tuple[str, str, str]:
    text = (source / "lightning/src/util/ser_macros.rs").read_text(encoding="utf-8")
    body = function_body(text, "retired_tlvs_skipped_on_read")
    concat = re.search(r"from_hex\(concat!\((.*?)\)\)", body, re.DOTALL)
    require(concat is not None, "retired TLV concat! block not found")
    accepted = "".join(hex_strings(concat.group(1)))
    require(accepted, "retired TLV accepted stream is empty")
    unknown_even = first_tlv_record(bytes.fromhex(accepted)).hex()
    truncated_match = re.search(
        r'from_hex\(\s*"([0-9a-f]+)"\s*\)', body[concat.end():])
    require(truncated_match is not None,
            "truncated retired TLV literal not found")
    return accepted, unknown_even, truncated_match.group(1)


def extract_wire(source: Path) -> int:
    text = (source / "lightning/src/ln/peer_channel_encryptor.rs").read_text(
        encoding="utf-8")
    require("LN_MAX_MSG_LEN: usize = u16::MAX as usize" in text,
            "LN_MAX_MSG_LEN = u16::MAX not found")
    require("let msg_len = msgbuf.len() - 16 - 2;" in text,
            "msgbuf.len() - 16 - 2 length computation not found")
    return 0xFFFF


def extract_messages(source: Path) -> dict[str, str]:
    """Re-extract the pinned BOLT 2 channel_ready encoding target.

    The pinned `ln::msgs::tests::encoding_channel_ready` test constructs a
    `ChannelReady` with an all-`0x02` channel id, the public key derived from
    the all-`0x01` secret key, and no `short_channel_id_alias`, then compares
    `encode()` with a literal.  The literal is the full 65-byte payload:
    32-byte channel id followed by a 33-byte compressed point.
    """
    text = (source / "lightning/src/ln/msgs.rs").read_text(encoding="utf-8")
    body = function_body(text, "encoding_channel_ready")
    require("ChannelId::from_bytes([2; 32])" in body,
            "channel_ready test no longer uses an all-0x02 channel id")
    require("short_channel_id_alias: None" in body,
            "channel_ready test no longer omits the alias TLV")
    target = re.search(r'<Vec<u8>>::from_hex\(\s*"([0-9a-f]+)"\s*\)', body)
    require(target is not None,
            "channel_ready encoded payload literal not found")
    payload = target.group(1)
    require(len(payload) == 130,
            f"channel_ready payload is {len(payload)//2} bytes, expected 65")
    point = payload[64:]
    require(point[:2] in ("02", "03"),
            "channel_ready commitment point is not a compressed point")
    return {
        "channel_id": payload[:64],
        "next_per_commitment_point": point,
        "payload": payload,
    }


def offline_generation() -> dict[str, Any]:
    return {
        "script": "tests/conformance/rust-lightning/generate.py",
        "mode": "transcribed-from-pinned-source",
        "live_cargo_test": False,
        "note": OFFLINE_NOTE,
    }


def live_generation(transcript_digest: str,
                    transcript_rel: str) -> dict[str, Any]:
    return {
        "script": "tests/conformance/rust-lightning/generate.py",
        "mode": "live-cargo-test",
        "live_cargo_test": True,
        "live_transcript": transcript_rel,
        "live_transcript_sha256": transcript_digest,
        "note": LIVE_NOTE,
    }


def transcript_location(doc: dict[str, Any],
                        transcript_path: Path | None) -> Path | None:
    if transcript_path is not None:
        return transcript_path
    rel = doc.get("generation", {}).get("live_transcript")
    if isinstance(rel, str) and rel:
        return ROOT / rel
    return None


def generation_block(doc: dict[str, Any],
                     transcript_path: Path | None) -> dict[str, Any]:
    """Return the canonical generation metadata.

    A committed live claim is only accepted when the transcript it names exists,
    hashes to the recorded ``live_transcript_sha256``, and is itself consistent;
    that deeper check lives in ``scripts/check-conformance.py``.
    """
    committed = doc.get("generation")
    require(isinstance(committed, dict), "generation metadata is missing")
    if not committed.get("live_cargo_test"):
        return offline_generation()
    path = transcript_location(doc, transcript_path)
    require(path is not None and path.is_file(),
            "a live cargo claim must name a readable live transcript")
    digest = sha256_file(path)
    stored = committed.get("live_transcript_sha256")
    require(digest == stored,
            f"live transcript sha256 {digest} != recorded {stored}")
    rel = committed.get("live_transcript")
    require(isinstance(rel, str) and rel,
            "a live cargo claim must record live_transcript")
    return live_generation(digest, rel)


def derived(doc: dict[str, Any], source: Path,
            transcript_path: Path | None = None) -> dict[str, Any]:
    values, byte_rows, errors = extract_bigsize(source)
    accepted, unknown_even, truncated = extract_tlv(source)
    max_len = extract_wire(source)
    message_source = extract_messages(source)

    fixtures = doc["fixtures"]
    bigsize = fixtures["bigsize"]
    encode_rows = [row for row in bigsize if row["kind"] == "encode"]
    ok_rows = [row for row in bigsize
               if row["kind"] == "decode" and row["rust_result"] == "ok"]
    invalid_rows = [row for row in bigsize
                    if row["kind"] == "decode"
                    and row["rust_result"] == "invalid-value"]
    short_rows = [row for row in bigsize
                  if row["kind"] == "decode" and row["rust_result"] == "short-read"]
    require(len(encode_rows) == 8, f"expected 8 encode fixtures, got {len(encode_rows)}")
    require(len(ok_rows) == 8, f"expected 8 ok decode fixtures, got {len(ok_rows)}")
    require(len(invalid_rows) == 3,
            f"expected 3 InvalidValue fixtures, got {len(invalid_rows)}")
    require(len(short_rows) == 7,
            f"expected 7 ShortRead fixtures, got {len(short_rows)}")

    for index, row in enumerate(encode_rows):
        row["value"] = values[index]
        row["bytes"] = byte_rows[index]
        row["rust_result"] = "ok"
        row["model_result"] = "ok"
    for index, row in enumerate(ok_rows):
        row["bytes"] = byte_rows[index]
        row["value"] = values[index]
        row["consumed"] = len(bytes.fromhex(byte_rows[index]))
        row["rust_result"] = "ok"
        row["model_result"] = "ok"
    for index, row in enumerate(invalid_rows):
        row["bytes"] = errors[index]
        row["rust_result"] = "invalid-value"
        row["model_result"] = "reject"
        row.pop("value", None)
        row.pop("consumed", None)
    for index, row in enumerate(short_rows):
        row["bytes"] = errors[3 + index]
        row["rust_result"] = "short-read"
        row["model_result"] = "reject"
        row.pop("value", None)
        row.pop("consumed", None)

    tlv = {row["id"]: row for row in fixtures["tlv"]}
    require("rust_tlv_retired_skipped" in tlv, "missing retired TLV fixture")
    require("rust_tlv_unknown_even_2" in tlv, "missing unknown-even TLV fixture")
    require("rust_tlv_truncated_2" in tlv, "missing truncated TLV fixture")
    tlv["rust_tlv_retired_skipped"]["bytes"] = accepted
    tlv["rust_tlv_unknown_even_2"]["bytes"] = unknown_even
    tlv["rust_tlv_truncated_2"]["bytes"] = truncated

    for row in fixtures["wire"]:
        require(row["type"] == 16, f"wire fixture {row['id']} is not type 16")
        if "payload" in row:
            payload_len = len(bytes.fromhex(row["payload"]))
        else:
            payload_len = row["payload_length"]
        transport_length = 2 + payload_len
        require(transport_length <= max_len or row["fits"] is False,
                f"wire fixture {row['id']} exceeds the pinned maximum")
        row["transport_length"] = transport_length
        row["header"] = f"{transport_length & 0xFFFF:04x}"
        row["fits"] = transport_length <= max_len
        row["model_fits"] = row["fits"]
        row["rust_result"] = "accept" if row["fits"] else "reject"

    messages = fixtures.get("messages")
    require(isinstance(messages, list) and messages,
            "differential fixtures missing the BOLT 2 message rows")
    for row in messages:
        require(row.get("kind") == "message",
                f"message fixture {row.get('id')} is not kind=message")
        require(row.get("name") == "channel_ready",
                f"message fixture {row.get('id')} is not channel_ready")
        require(row.get("type") == 36,
                f"message fixture {row.get('id')} is not type 36")
        payload = bytes.fromhex(message_source["payload"])
        transport_length = 2 + len(payload)
        require(transport_length <= max_len,
                f"message fixture {row['id']} exceeds the pinned maximum")
        row["construction"] = {
            "channel_id": message_source["channel_id"],
            "next_per_commitment_point":
                message_source["next_per_commitment_point"],
            "short_channel_id_alias": None,
        }
        row["fields"] = [
            {
                "name": "channel_id",
                "kind": "bytes",
                "offset": 0,
                "length": 32,
                "hex": message_source["channel_id"],
            },
            {
                "name": "next_per_commitment_point",
                "kind": "point",
                "offset": 32,
                "length": 33,
                "hex": message_source["next_per_commitment_point"],
            },
        ]
        row["payload"] = message_source["payload"]
        row["payload_length"] = len(payload)
        row["transport_length"] = transport_length
        row["header"] = f"{transport_length:04x}"
        row["frame_prefix"] = f"{row['type']:04x}{transport_length:04x}"
        row["rust_result"] = "accept"
        row["model_result"] = "accept"

    doc["provenance"] = [dict(entry) for entry in PROVENANCE]
    doc["pinned_commit"] = PINNED_COMMIT
    doc["generation"] = generation_block(doc, transcript_path)
    return doc


def diff_docs(expected: dict[str, Any], actual: dict[str, Any]) -> list[str]:
    problems: list[str] = []

    def walk(path: str, left: Any, right: Any) -> None:
        if type(left) is not type(right):
            problems.append(f"{path}: type {type(left).__name__} != "
                            f"{type(right).__name__}")
            return
        if isinstance(left, dict):
            for key in sorted(set(left) | set(right)):
                if key not in left:
                    problems.append(f"{path}.{key}: missing from derived")
                elif key not in right:
                    problems.append(f"{path}.{key}: missing from committed")
                else:
                    walk(f"{path}.{key}", left[key], right[key])
        elif isinstance(left, list):
            if len(left) != len(right):
                problems.append(f"{path}: length {len(left)} != {len(right)}")
                return
            for index, (litem, ritem) in enumerate(zip(left, right)):
                walk(f"{path}[{index}]", litem, ritem)
        elif left != right:
            problems.append(f"{path}: {left!r} != {right!r}")

    walk("fixtures", expected["fixtures"], actual["fixtures"])
    walk("provenance", expected["provenance"], actual["provenance"])
    walk("generation", expected["generation"], actual["generation"])
    return problems


def write_doc(doc: dict[str, Any], path: Path) -> None:
    text = json.dumps(doc, indent=2, ensure_ascii=True) + "\n"
    path.write_text(text, encoding="utf-8")


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def run_command(command: list[str], cwd: Path, timeout: int,
                stdin_text: str | None = None) -> subprocess.CompletedProcess[str]:
    print("+ " + " ".join(command))
    try:
        result = subprocess.run(
            command, cwd=cwd, input=stdin_text, capture_output=True,
            text=True, timeout=timeout, check=False)
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise LiveError(str(exc)) from None
    if result.returncode != 0:
        detail = (result.stdout + result.stderr).strip().splitlines()[-20:]
        raise LiveError(
            f"cargo returned {result.returncode}; the offline cache is incomplete "
            "or a pinned build/test failed. No live result is claimed.\n  "
            + "\n  ".join(detail))
    return result


def tool_version(command: str) -> str:
    try:
        result = subprocess.run([command, "--version"], capture_output=True,
                                text=True, timeout=60, check=False)
    except (OSError, subprocess.TimeoutExpired):
        return "unknown"
    return result.stdout.strip() if result.returncode == 0 else "unknown"


def probe_commands(doc: dict[str, Any]) -> list[str]:
    """Build the deterministic probe stdin from the committed fixture rows."""
    fixtures = doc["fixtures"]
    commands: list[str] = []
    for row in fixtures["bigsize"]:
        if row["kind"] == "encode":
            commands.append(f"E\t{row['id']}\t{row['value']}")
        else:
            commands.append(f"D\t{row['id']}\t{row['bytes']}")
    for row in fixtures["tlv"]:
        # The pinned tests use the retired reader for both the accepted stream
        # and the truncated record, and the unlisted reader for the unknown
        # even type.
        mode = ("unlisted" if row["rust_result"] == "unknown-required-feature"
                else "retired")
        commands.append(f"T\t{row['id']}\t{mode}\t{row['bytes']}")
    for row in fixtures["messages"]:
        construction = row["construction"]
        alias = construction["short_channel_id_alias"]
        alias_arg = "-" if alias is None else str(alias)
        commands.append(
            f"B\t{row['id']}\t{alias_arg}\t{construction['channel_id']}\t"
            f"{construction['next_per_commitment_point']}")
    commands.append("M")
    return commands


def parse_probe_output(output: str) -> tuple[dict[str, list[str]], list[str]]:
    results: dict[str, list[str]] = {}
    lines: list[str] = []
    for line in output.splitlines():
        if not line.startswith("LNLEAN\t"):
            continue
        lines.append(line)
        fields = line[len("LNLEAN\t"):].split("\t")
        require(len(fields) >= 2, f"malformed probe line: {line!r}")
        results[fields[0]] = fields[1:]
    return results, lines


def compare_live(doc: dict[str, Any], results: dict[str, list[str]]
                 ) -> tuple[list[str], dict[str, int]]:
    """Compare the live rust-lightning results with the committed fixtures."""
    fixtures = doc["fixtures"]
    problems: list[str] = []
    live_max_fields = results.get("LN_MAX_MSG_LEN")
    require(live_max_fields is not None and len(live_max_fields) == 1,
            "live probe did not report LN_MAX_MSG_LEN")
    live_max = int(live_max_fields[0])

    for row in fixtures["bigsize"]:
        got = results.get(row["id"])
        if row["kind"] == "encode":
            expected = ["ok", row["bytes"]]
        elif row["rust_result"] == "ok":
            expected = ["ok", str(row["value"]), str(row["consumed"])]
        else:
            expected = [row["rust_result"]]
        if got != expected:
            problems.append(f"bigsize[{row['id']}]: live {got} != fixture {expected}")

    for row in fixtures["tlv"]:
        got = results.get(row["id"])
        if row["rust_result"] == "accept":
            records = {record["type"]: record["value"]
                       for record in row["expected_records"]}
            required = records[3]
            optional = records.get(7, "-")
            expected = ["accept", required, optional]
        else:
            expected = [row["rust_result"]]
        if got != expected:
            problems.append(f"tlv[{row['id']}]: live {got} != fixture {expected}")

    for row in fixtures["messages"]:
        got = results.get(row["id"])
        expected = ["ok", row["payload"]]
        if got != expected:
            problems.append(
                f"message[{row['id']}]: live {got} != fixture {expected}")

    if live_max != 0xFFFF:
        problems.append(f"live LN_MAX_MSG_LEN {live_max} != 65535")
    for row in fixtures["wire"]:
        if "payload" in row:
            payload_len = len(bytes.fromhex(row["payload"]))
        else:
            payload_len = row["payload_length"]
        transport_length = 2 + payload_len
        if row["transport_length"] != transport_length:
            problems.append(f"wire[{row['id']}]: live transport length "
                            f"{transport_length} != fixture {row['transport_length']}")
        if row["header"] != f"{transport_length & 0xFFFF:04x}":
            problems.append(f"wire[{row['id']}]: header for live transport length "
                            f"{transport_length} != fixture {row['header']}")
        if row["fits"] != (transport_length <= live_max):
            problems.append(f"wire[{row['id']}]: live fits "
                            f"{transport_length <= live_max} != fixture {row['fits']}")

    counts = {
        "bigsize": len(fixtures["bigsize"]),
        "tlv": len(fixtures["tlv"]),
        "wire": len(fixtures["wire"]),
        "messages": len(fixtures["messages"]),
    }
    return problems, counts


def live_run(source: Path, fixture_doc: dict[str, Any], timeout: int,
             fetch: bool, transcript_path: Path) -> dict[str, Any]:
    """Run the pinned tests and the public-API probe in a disposable copy.

    The pinned checkout is often a shared ``refs/`` symlink; copying it avoids
    writing a ``Cargo.lock``/``target`` directory into the vendor source.  The
    committed ``pinned/Cargo.lock`` and ``live_probe.rs`` are installed in the
    copy, so ``--offline --locked`` selects exactly the recorded dependency
    graph without touching the vendor checkout.
    """
    require(source.is_dir(), f"pinned source checkout not found: {source}")
    require(PINNED_LOCK.is_file(), f"pinned Cargo.lock not found: {PINNED_LOCK}")
    require(LIVE_PROBE.is_file(), f"live probe not found: {LIVE_PROBE}")
    commands = probe_commands(fixture_doc)

    with tempfile.TemporaryDirectory(prefix="lnlean-rust-lightning-") as tmp:
        work = Path(tmp) / "rust-lightning"
        shutil.copytree(source, work, symlinks=True,
                        ignore=shutil.ignore_patterns(".git", "target"))
        shutil.copyfile(PINNED_LOCK, work / "Cargo.lock")
        probe_target = work / "lightning" / "examples" / "lnlean_conformance_probe.rs"
        probe_target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(LIVE_PROBE, probe_target)

        if fetch:
            print("completing the cargo cache (one online fetch; "
                  "the run below is --offline):")
            run_command(["cargo", "fetch", "--locked"], work, timeout)

        tests: list[dict[str, Any]] = []
        for name in LIVE_TESTS:
            result = run_command(
                ["cargo", "test", "--offline", "--locked", "-p", "lightning",
                 "--lib", name], work, timeout)
            expected_line = f"test {name} ... ok"
            require(expected_line in result.stdout,
                    f"pinned test did not report '{expected_line}'")
            require("test result: ok. 1 passed; 0 failed" in result.stdout,
                    f"pinned test {name} did not report exactly one pass")
            tests.append({"name": name, "result": "ok", "passed": 1, "failed": 0})

        probe = run_command(
            ["cargo", "run", "--offline", "--locked", "-p", "lightning",
             "--example", "lnlean_conformance_probe"],
            work, timeout, stdin_text="\n".join(commands) + "\n")
        results, result_lines = parse_probe_output(probe.stdout)
        problems, counts = compare_live(fixture_doc, results)
        require(not problems,
                "live rust-lightning output disagrees with the fixtures:\n  "
                + "\n  ".join(problems[:20]))

        transcript = {
            "schema": LIVE_TRANSCRIPT_SCHEMA,
            "pinned_commit": PINNED_COMMIT,
            "fixture_rows_sha256": hashlib.sha256(
                json.dumps(fixture_doc["fixtures"], sort_keys=True,
                           separators=(",", ":")).encode("utf-8")).hexdigest(),
            "probe_sha256": sha256_file(LIVE_PROBE),
            "cargo_lock_sha256": sha256_file(PINNED_LOCK),
            "toolchain": {
                "cargo": tool_version("cargo"),
                "rustc": tool_version("rustc"),
            },
            "tests": tests,
            "comparisons": counts,
            "wire_basis": "live LN_MAX_MSG_LEN; the length-header arithmetic "
                          "remains the pinned-source check in extract_wire",
            "commands_sha256": sha256_text("\n".join(commands)),
            "results_sha256": sha256_text("\n".join(result_lines)),
        }
        transcript_path.parent.mkdir(parents=True, exist_ok=True)
        write_doc(transcript, transcript_path)
        digest = sha256_file(transcript_path)
        print(f"live: {counts['bigsize']} BigSize and {counts['tlv']} TLV fixtures "
              f"agree with rust-lightning; {counts['messages']} BOLT 2 "
              f"channel_ready payload(s) encoded live; wire: {counts['wire']} "
              f"checked against live LN_MAX_MSG_LEN={results['LN_MAX_MSG_LEN'][0]}")
        print(f"live transcript: {transcript_path} ({digest})")
        transcript["_path"] = str(transcript_path)
        transcript["_sha256"] = digest
        return transcript


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Re-derive or verify the pinned rust-lightning fixtures.")
    parser.add_argument("--source-dir", type=Path, default=DEFAULT_SOURCE,
                        help=f"pinned rust-lightning checkout (default: {DEFAULT_SOURCE})")
    parser.add_argument("--fixtures", type=Path, default=DEFAULT_FIXTURES,
                        help=f"fixture JSON (default: {DEFAULT_FIXTURES})")
    parser.add_argument("--check", action="store_true",
                        help="verify the committed fixtures (the default)")
    parser.add_argument("--write", action="store_true",
                        help="rewrite the derived fixture fields deterministically")
    parser.add_argument("--live", action="store_true",
                        help="run the pinned tests and the public-API probe offline")
    parser.add_argument("--fetch", action="store_true",
                        help="with --live: run one online `cargo fetch --locked` "
                             "to complete the cache before the offline run")
    parser.add_argument("--record", action="store_true",
                        help="with --live: record the successful transcript hash in "
                             "fixtures.json (fixture rows are unchanged)")
    parser.add_argument("--transcript", type=Path, default=DEFAULT_TRANSCRIPT,
                        help=f"live transcript path (default: {DEFAULT_TRANSCRIPT})")
    parser.add_argument("--timeout", type=int, default=1800,
                        help="per-command timeout for --live (seconds)")
    args = parser.parse_args(argv)
    if args.record and not args.live:
        parser.error("--record requires --live")
    if args.fetch and not args.live:
        parser.error("--fetch requires --live")

    try:
        verify_provenance(args.source_dir)
        doc = json.loads(args.fixtures.read_text(encoding="utf-8"))
        expected = derived(json.loads(args.fixtures.read_text(encoding="utf-8")),
                           args.source_dir)
        if args.write:
            write_doc(expected, args.fixtures)
            try:
                display = args.fixtures.relative_to(ROOT)
            except ValueError:
                display = args.fixtures
            print(f"wrote {display} "
                  f"({len(expected['fixtures']['bigsize'])} BigSize, "
                  f"{len(expected['fixtures']['tlv'])} TLV, "
                  f"{len(expected['fixtures']['wire'])} wire, "
                  f"{len(expected['fixtures']['messages'])} message fixtures)")
        else:
            problems = diff_docs(expected, doc)
            require(not problems, "fixture mismatch:\n  " + "\n  ".join(problems[:20]))
            print(f"fixtures: {len(doc['fixtures']['bigsize'])} BigSize, "
                  f"{len(doc['fixtures']['tlv'])} TLV, "
                  f"{len(doc['fixtures']['wire'])} wire, "
                  f"{len(doc['fixtures']['messages'])} message match the pinned source")
        print(f"provenance: {len(PROVENANCE)} source files verified at "
              f"{PINNED_COMMIT[:7]}")
        if args.live:
            transcript = live_run(args.source_dir, doc, args.timeout,
                                  args.fetch, args.transcript)
            if args.record:
                path = Path(transcript["_path"]).resolve()
                try:
                    rel = str(path.relative_to(ROOT))
                except ValueError:
                    rel = str(path)
                doc["generation"] = live_generation(transcript["_sha256"], rel)
                write_doc(doc, args.fixtures)
                print(f"recorded live transcript {rel} in {args.fixtures}")
            return 0
        if expected["generation"]["live_cargo_test"]:
            digest = expected["generation"]["live_transcript_sha256"]
            print(f"live cargo test: recorded in "
                  f"{expected['generation']['live_transcript']} ({digest[:12]})")
        else:
            print("live cargo test: not run (use --live; no live result is claimed)")
        return 0
    except LiveError as exc:
        print(f"LIVE RUN FAILED: {exc}", file=sys.stderr)
        return 4
    except FixtureError as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        return 1
    except (OSError, json.JSONDecodeError) as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())

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

``--live`` is the only mode that invokes ``cargo test``.  It runs the two
pinned unit tests with ``--offline`` and exits 4 if the cache is incomplete;
it never claims a live result on failure and never modifies ``fixtures.json``.

Usage::

    python3 tests/conformance/rust-lightning/generate.py --check
    python3 tests/conformance/rust-lightning/generate.py --write
    python3 tests/conformance/rust-lightning/generate.py --live

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

PINNED_COMMIT = "fe4900930c6bd5786ec4203274d7cf312776a5a6"
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
]

HEX_RE = re.compile(r'"([0-9a-f]*)"')
INT_RE = re.compile(r"\b(\d+)\b")
FUNCTION_RE = r"fn\s+%s\s*\(\)\s*\{"
LET_ARRAY_RE = r"let\s+%s\s*=\s*\[(.*?)\];"


class FixtureError(Exception):
    """A fixture/provenance mismatch."""


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


def derived(doc: dict[str, Any], source: Path) -> dict[str, Any]:
    values, byte_rows, errors = extract_bigsize(source)
    accepted, unknown_even, truncated = extract_tlv(source)
    max_len = extract_wire(source)

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

    doc["provenance"] = [dict(entry) for entry in PROVENANCE]
    doc["pinned_commit"] = PINNED_COMMIT
    doc["generation"] = {
        "script": "tests/conformance/rust-lightning/generate.py",
        "mode": "transcribed-from-pinned-source",
        "live_cargo_test": False,
        "note": "The committed rows were extracted from the pinned source/unit-test "
                "literals; `generate.py --check` re-extracts and compares them, and "
                "`generate.py --live` runs the pinned cargo tests only when the "
                "offline cache is complete. No live cargo result is claimed here.",
    }
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


def live_run(source: Path, timeout: int) -> int:
    """Run the pinned unit tests offline in a disposable copy.

    The pinned checkout is often a shared ``refs/`` symlink; copying it avoids
    writing a ``Cargo.lock``/``target`` directory into the vendor source.
    """
    require(source.is_dir(), f"pinned source checkout not found: {source}")
    commands = [
        ["cargo", "test", "--offline", "-p", "lightning", "--lib",
         "util::ser::tests::bigsize_encoding_decoding"],
        ["cargo", "test", "--offline", "-p", "lightning", "--lib",
         "util::ser_macros::tests::retired_tlvs_skipped_on_read"],
    ]
    with tempfile.TemporaryDirectory(prefix="lnlean-rust-lightning-") as tmp:
        work = Path(tmp) / "rust-lightning"
        shutil.copytree(source, work, symlinks=True,
                        ignore=shutil.ignore_patterns(".git", "target"))
        for command in commands:
            print("+ " + " ".join(command))
            try:
                result = subprocess.run(
                    command, cwd=work, capture_output=True, text=True,
                    timeout=timeout, check=False)
            except (OSError, subprocess.TimeoutExpired) as exc:
                print(f"LIVE RUN FAILED: {exc}", file=sys.stderr)
                return 4
            if result.returncode != 0:
                print(result.stdout, file=sys.stderr)
                print(result.stderr, file=sys.stderr)
                print("LIVE RUN FAILED: cargo returned "
                      f"{result.returncode}; the offline cache is incomplete or a "
                      "pinned test failed. No live result is claimed.", file=sys.stderr)
                return 4
            print(result.stdout, end="")
    print("LIVE RUN OK: both pinned unit tests passed under --offline")
    return 0


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
                        help="run the pinned cargo tests offline (does not rewrite)")
    parser.add_argument("--timeout", type=int, default=1800,
                        help="per-command timeout for --live (seconds)")
    args = parser.parse_args(argv)

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
                  f"{len(expected['fixtures']['wire'])} wire fixtures)")
        else:
            problems = diff_docs(expected, doc)
            require(not problems, "fixture mismatch:\n  " + "\n  ".join(problems[:20]))
            print(f"fixtures: {len(doc['fixtures']['bigsize'])} BigSize, "
                  f"{len(doc['fixtures']['tlv'])} TLV, "
                  f"{len(doc['fixtures']['wire'])} wire match the pinned source")
        print(f"provenance: {len(PROVENANCE)} source files verified at "
              f"{PINNED_COMMIT[:7]}")
        if args.live:
            return live_run(args.source_dir, args.timeout)
        print("live cargo test: not run (use --live; no live result is claimed)")
        return 0
    except FixtureError as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        return 1
    except (OSError, json.JSONDecodeError) as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())

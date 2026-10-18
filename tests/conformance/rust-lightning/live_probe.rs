//! Live conformance probe copied into the disposable pinned rust-lightning
//! checkout by `tests/conformance/rust-lightning/generate.py --live`.
//!
//! It reads a tab-separated command stream on stdin and prints one
//! tab-separated result line per command, prefixed with `LNLEAN`.  The probe
//! uses only the public rust-lightning API (BigSize's `Readable`/`Writeable`
//! impls, the exported `decode_tlv_stream!` macro, and `LN_MAX_MSG_LEN`), so
//! it exercises the pinned library code rather than a copy of it.
//!
//! Commands:
//!   `E <id> <value>`                 encode a BigSize
//!   `D <id> <hex>`                   decode a BigSize
//!   `T <id> retired|unlisted <hex>`  run the pinned TLV readers
//!   `M`                              emit `LN_MAX_MSG_LEN`
//!
//! This file is not part of the rust-lightning source tree; it is copied into
//! `lightning/examples/` of a temporary checkout only.

use std::io::{self, BufRead};

use lightning::decode_tlv_stream;
use lightning::io::Cursor;
use lightning::ln::msgs::DecodeError;
use lightning::ln::LN_MAX_MSG_LEN;
use lightning::util::ser::{BigSize, Readable, Writeable};

fn from_hex(text: &str) -> Vec<u8> {
    assert!(text.len() % 2 == 0, "odd-length hex input: {text}");
    (0..text.len())
        .step_by(2)
        .map(|index| u8::from_str_radix(&text[index..index + 2], 16).expect("hex"))
        .collect()
}

fn to_hex(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(2 * bytes.len());
    for byte in bytes {
        out.push_str(&format!("{:02x}", byte));
    }
    out
}

fn class(error: DecodeError) -> &'static str {
    match error {
        DecodeError::InvalidValue => "invalid-value",
        DecodeError::ShortRead => "short-read",
        DecodeError::UnknownRequiredFeature => "unknown-required-feature",
        _ => "other-error",
    }
}

fn encode_bigsize(value: u64) -> String {
    to_hex(&BigSize(value).encode())
}

fn decode_bigsize(hex: &str) -> String {
    let bytes = from_hex(hex);
    let mut cursor = Cursor::new(&bytes[..]);
    match BigSize::read(&mut cursor) {
        Ok(value) => format!("ok\t{}\t{}", value.0, cursor.position()),
        Err(error) => class(error).to_string(),
    }
}

/// The pinned `retired_tlv_reader` from `util::ser_macros::tests`: type 2 is
/// retired (skipped), type 3 is required, type 5 is retired, type 7 optional.
fn retired_tlv_reader(data: &[u8]) -> Result<(u64, Option<u32>), DecodeError> {
    let mut stream = Cursor::new(data);
    let mut a: u64 = 0;
    let mut b: Option<u32> = None;
    decode_tlv_stream!(&mut stream, {
        (2, _old_even, retired),
        (3, a, required),
        (5, _old_odd, retired),
        (7, b, option)
    });
    Ok((a, b))
}

/// The pinned `unlisted_even_tlv_reader`: the same even type is now unknown.
fn unlisted_even_tlv_reader(data: &[u8]) -> Result<(u64, Option<u32>), DecodeError> {
    let mut stream = Cursor::new(data);
    let mut a: u64 = 0;
    let mut b: Option<u32> = None;
    decode_tlv_stream!(&mut stream, {(3, a, required), (7, b, option)});
    Ok((a, b))
}

fn report_tlv(result: Result<(u64, Option<u32>), DecodeError>) -> String {
    match result {
        Ok((a, b)) => match b {
            Some(b) => format!("accept\t{:x}\t{:x}", a, b),
            None => format!("accept\t{:x}\t-", a),
        },
        Err(error) => class(error).to_string(),
    }
}

fn main() {
    for line in io::stdin().lock().lines() {
        let line = line.expect("stdin");
        if line.trim().is_empty() || line.starts_with('#') {
            continue;
        }
        let fields: Vec<&str> = line.split('\t').collect();
        let output = match fields.as_slice() {
            ["E", id, value] => {
                let value: u64 = value.parse().expect("encode value");
                format!("{id}\tok\t{}", encode_bigsize(value))
            }
            ["D", id, hex] => format!("{id}\t{}", decode_bigsize(hex)),
            ["T", id, "retired", hex] => {
                format!("{id}\t{}", report_tlv(retired_tlv_reader(&from_hex(hex))))
            }
            ["T", id, "unlisted", hex] => {
                format!("{id}\t{}", report_tlv(unlisted_even_tlv_reader(&from_hex(hex))))
            }
            ["M"] => format!("LN_MAX_MSG_LEN\t{LN_MAX_MSG_LEN}"),
            other => panic!("bad probe command: {other:?}"),
        };
        println!("LNLEAN\t{output}");
    }
}

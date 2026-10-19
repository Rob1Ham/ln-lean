//! Live conformance probe copied into the disposable pinned rust-lightning
//! checkout by `tests/conformance/rust-lightning/generate.py --live`.
//!
//! It reads a tab-separated command stream on stdin and prints one
//! tab-separated result line per command, prefixed with `LNLEAN`.  The probe
//! uses only the public rust-lightning API (BigSize's `Readable`/`Writeable`
//! impls, the exported `decode_tlv_stream!` macro, `LN_MAX_MSG_LEN`, and the
//! public `ChannelReady` message fields/`Writeable` impl), so it exercises the
//! pinned library code rather than a copy of it.
//!
//! Commands:
//!   `E <id> <value>`                 encode a BigSize
//!   `D <id> <hex>`                   decode a BigSize
//!   `T <id> retired|unlisted <hex>`  run the pinned TLV readers
//!   `F <id> ...`                     encode a BOLT 2 funding_created
//!   `S <id> ...`                     encode a BOLT 2 funding_signed
//!   `B <id> <alias|-> <channel_id> <point>` encode a BOLT 2 channel_ready
//!   `O <id> ...`                     encode a BOLT 2 open_channel
//!   `A <id> ...`                     encode a BOLT 2 accept_channel
//!   `M`                              emit `LN_MAX_MSG_LEN`
//!
//! This file is not part of the rust-lightning source tree; it is copied into
//! `lightning/examples/` of a temporary checkout only.

use std::io::{self, BufRead};

use lightning::bitcoin::constants::ChainHash;
use lightning::bitcoin::hash_types::Txid;
use lightning::bitcoin::hashes::Hash;
use lightning::bitcoin::secp256k1::ecdsa::Signature;
use lightning::bitcoin::secp256k1::PublicKey;
use lightning::bitcoin::Network;
use lightning::decode_tlv_stream;
use lightning::io::Cursor;
use lightning::ln::msgs::{
    AcceptChannel, ChannelReady, CommonAcceptChannelFields, CommonOpenChannelFields,
    DecodeError, FundingCreated, FundingSigned, OpenChannel,
};
use lightning::ln::types::ChannelId;
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

fn channel_id_bytes(hex: &str) -> [u8; 32] {
    let bytes = from_hex(hex);
    assert_eq!(bytes.len(), 32, "channel id must be 32 bytes");
    let mut channel_id = [0u8; 32];
    channel_id.copy_from_slice(&bytes);
    channel_id
}

fn compact_signature(hex: &str) -> Signature {
    Signature::from_compact(&from_hex(hex)).expect("valid compact signature")
}

/// Encode the public BOLT 2 `funding_created` fields through the pinned
/// `Writeable` implementation.  Argument order is
/// `temporary_channel_id`, `funding_txid`, `funding_output_index`, `signature`.
/// The Txid payload bytes are the wire-order bytes; `Txid::from_byte_array`
/// stores them in that order, matching the pinned unit test's encoded target.
fn encode_funding_created(args: &[&str]) -> String {
    let funding_txid_bytes = from_hex(args[1]);
    assert_eq!(funding_txid_bytes.len(), 32, "funding txid must be 32 bytes");
    let mut funding_txid = [0u8; 32];
    funding_txid.copy_from_slice(&funding_txid_bytes);
    let message = FundingCreated {
        temporary_channel_id: ChannelId::from_bytes(channel_id_bytes(args[0])),
        funding_txid: Txid::from_byte_array(funding_txid),
        funding_output_index: args[2].parse::<u16>().expect("u16 output index"),
        signature: compact_signature(args[3]),
    };
    to_hex(&message.encode())
}

/// Encode the public BOLT 2 `funding_signed` fields through the pinned
/// `Writeable` implementation.  Argument order is `channel_id`, `signature`.
fn encode_funding_signed(args: &[&str]) -> String {
    let message = FundingSigned {
        channel_id: ChannelId::from_bytes(channel_id_bytes(args[0])),
        signature: compact_signature(args[1]),
    };
    to_hex(&message.encode())
}

/// Encode the public BOLT 2 `channel_ready` fields through the pinned
/// `Writeable` implementation.  `alias` exercises the optional type-1
/// `short_channel_id_alias` TLV when present.
fn encode_channel_ready(channel_id_hex: &str, point_hex: &str,
                        alias: Option<u64>) -> String {
    let channel_id_bytes = from_hex(channel_id_hex);
    assert_eq!(channel_id_bytes.len(), 32, "channel_id must be 32 bytes");
    let mut channel_id = [0u8; 32];
    channel_id.copy_from_slice(&channel_id_bytes);
    let point = PublicKey::from_slice(&from_hex(point_hex))
        .expect("valid compressed commitment point");
    let message = ChannelReady {
        channel_id: ChannelId::from_bytes(channel_id),
        next_per_commitment_point: point,
        short_channel_id_alias: alias,
    };
    to_hex(&message.encode())
}

/// Encode the public BOLT 2 `open_channel` fields through the pinned
/// `Writeable` implementation.  The construction mirrors the pinned
/// `ln::msgs::tests::do_encoding_open_channel(false, false, false)` case:
/// mainnet chain hash, no `upfront_shutdown_script` TLV, no `channel_type`
/// TLV.  Argument order is documented in the `O` command below.
fn encode_open_channel(args: &[&str]) -> String {
    let parse_u64 = |text: &str| text.parse::<u64>().expect("u64 field");
    let parse_u32 = |text: &str| text.parse::<u32>().expect("u32 field");
    let parse_u16 = |text: &str| text.parse::<u16>().expect("u16 field");
    let parse_u8 = |text: &str| text.parse::<u8>().expect("u8 field");
    let point = |text: &str| {
        PublicKey::from_slice(&from_hex(text)).expect("valid compressed point")
    };
    let channel_id_bytes = from_hex(args[0]);
    assert_eq!(channel_id_bytes.len(), 32, "temporary_channel_id must be 32 bytes");
    let mut channel_id = [0u8; 32];
    channel_id.copy_from_slice(&channel_id_bytes);
    let message = OpenChannel {
        common_fields: CommonOpenChannelFields {
            chain_hash: ChainHash::using_genesis_block(Network::Bitcoin),
            temporary_channel_id: ChannelId::from_bytes(channel_id),
            funding_satoshis: parse_u64(args[1]),
            dust_limit_satoshis: parse_u64(args[3]),
            max_htlc_value_in_flight_msat: parse_u64(args[4]),
            htlc_minimum_msat: parse_u64(args[6]),
            commitment_feerate_sat_per_1000_weight: parse_u32(args[7]),
            to_self_delay: parse_u16(args[8]),
            max_accepted_htlcs: parse_u16(args[9]),
            funding_pubkey: point(args[11]),
            revocation_basepoint: point(args[12]),
            payment_basepoint: point(args[13]),
            delayed_payment_basepoint: point(args[14]),
            htlc_basepoint: point(args[15]),
            first_per_commitment_point: point(args[16]),
            channel_flags: parse_u8(args[10]),
            shutdown_scriptpubkey: None,
            channel_type: None,
        },
        push_msat: parse_u64(args[2]),
        channel_reserve_satoshis: parse_u64(args[5]),
    };
    to_hex(&message.encode())
}

/// Encode the public BOLT 2 `accept_channel` fields through the pinned
/// `Writeable` implementation.  The construction mirrors the pinned
/// `ln::msgs::tests::do_encoding_accept_channel(false)` case: all-`0x02`
/// `temporary_channel_id`, the pinned numeric fields, six compressed points, no
/// `shutdown_scriptpubkey` TLV, and no `channel_type` TLV.  Argument order is
/// documented in the `A` command below.
fn encode_accept_channel(args: &[&str]) -> String {
    let parse_u64 = |text: &str| text.parse::<u64>().expect("u64 field");
    let parse_u32 = |text: &str| text.parse::<u32>().expect("u32 field");
    let parse_u16 = |text: &str| text.parse::<u16>().expect("u16 field");
    let point = |text: &str| {
        PublicKey::from_slice(&from_hex(text)).expect("valid compressed point")
    };
    let channel_id_bytes = from_hex(args[0]);
    assert_eq!(channel_id_bytes.len(), 32, "temporary_channel_id must be 32 bytes");
    let mut channel_id = [0u8; 32];
    channel_id.copy_from_slice(&channel_id_bytes);
    let message = AcceptChannel {
        common_fields: CommonAcceptChannelFields {
            temporary_channel_id: ChannelId::from_bytes(channel_id),
            dust_limit_satoshis: parse_u64(args[1]),
            max_htlc_value_in_flight_msat: parse_u64(args[2]),
            htlc_minimum_msat: parse_u64(args[4]),
            minimum_depth: parse_u32(args[5]),
            to_self_delay: parse_u16(args[6]),
            max_accepted_htlcs: parse_u16(args[7]),
            funding_pubkey: point(args[8]),
            revocation_basepoint: point(args[9]),
            payment_basepoint: point(args[10]),
            delayed_payment_basepoint: point(args[11]),
            htlc_basepoint: point(args[12]),
            first_per_commitment_point: point(args[13]),
            shutdown_scriptpubkey: None,
            channel_type: None,
        },
        channel_reserve_satoshis: parse_u64(args[3]),
    };
    to_hex(&message.encode())
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
            ["F", id, ..] => {
                // F <id> <temporary_channel_id> <funding_txid>
                //   <funding_output_index> <signature>
                format!("{id}\tok\t{}", encode_funding_created(&fields[2..]))
            }
            ["S", id, ..] => {
                // S <id> <channel_id> <signature>
                format!("{id}\tok\t{}", encode_funding_signed(&fields[2..]))
            }
            ["B", id, alias, channel_id, point] => {
                let alias = if *alias == "-" {
                    None
                } else {
                    Some(alias.parse::<u64>().expect("alias"))
                };
                format!("{id}\tok\t{}", encode_channel_ready(channel_id, point, alias))
            }
            ["O", id, ..] => {
                // O <id> <temp_id> <funding> <push> <dust> <max_htlc> <reserve>
                //   <htlc_min> <feerate> <to_self> <max_accepted> <flags>
                //   <funding_pk> <revocation> <payment> <delayed_payment>
                //   <htlc_basepoint> <first_per_commitment_point>
                format!("{id}\tok\t{}", encode_open_channel(&fields[2..]))
            }
            ["A", id, ..] => {
                // A <id> <temp_id> <dust> <max_htlc> <reserve> <htlc_min>
                //   <min_depth> <to_self> <max_accepted> <funding_pk>
                //   <revocation> <payment> <delayed_payment> <htlc_basepoint>
                //   <first_per_commitment_point>
                format!("{id}\tok\t{}", encode_accept_channel(&fields[2..]))
            }
            ["M"] => format!("LN_MAX_MSG_LEN\t{LN_MAX_MSG_LEN}"),
            other => panic!("bad probe command: {other:?}"),
        };
        println!("LNLEAN\t{output}");
    }
}

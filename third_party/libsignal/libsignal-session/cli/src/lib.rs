// Copyright 2026 Google LLC; SPDX-License-Identifier: Apache-2.0.
// This file is ORIGINAL code written for this repository; it copies no upstream source. The
// machine code produced by compiling it together with libsignal is a derived work of libsignal
// (`Copyright 2020-2026 Signal Messenger, LLC.`, `SPDX-License-Identifier: AGPL-3.0-only`); see
// `third_party/libsignal/README.md`.

//! `libsignal-cli`: one operation of a libsignal v0.105.4 1:1 session per process, for the party
//! whose directory is the current directory: key generation, the PQXDH handshake and the Triple
//! Ratchet (Double Ratchet + SPQR).
//!
//! The party's libsignal stores are the files of its directory (`stores.rs`), and what it publishes
//! is under `public/` (`public.rs`). Each run reads the files libsignal asks for, performs ONE
//! operation and, only if libsignal accepts it, writes the files it changed. (A rejected operation
//! may have changed a store before failing, so then nothing is written.) Nothing outlives the
//! process, so a party that leaks its directory has leaked everything it holds.
//!
//! ```text
//! libsignal-cli keygen <address> <n>       a new party, in an empty directory (ids below)
//! libsignal-cli init <peer> <bundle>       a session with <peer>, from <bundle>: a directory of
//!                                           copies of its public files, made by the caller
//!                                           (`public.rs`)
//! libsignal-cli send <peer>                stdin: plaintext (≤ 10^6 B)     stdout: wire
//! libsignal-cli recv <peer>                stdin: wire (≤ 2^20 B)          stdout: plaintext
//! exit 1: libsignal rejected the operation, or send plaintext > 10^6 B; no file is written
//! exit 2: bad command line, stdin > 2^20 B, coins > 2^21 B, or a file could not be read or written
//! abort:  libsignal panicked (all file reads are capped at 2^21 B; store/bundle > 2^21 B → exit 1)
//!
//! address, peer  service id . device id, e.g. 5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6.1
//! keygen     identity key pair and registration id; signed pre-key 1; last-resort Kyber pre-key 1;
//!            one-time pre-keys 1..=n and one-time Kyber pre-keys 2..=n+1 (n ≤ 100); each stored
//!            and its public half published
//! coins      this call's randomness, a file in the party's directory: read in order, zeros past
//!            the end
//! wire       type:u8 (2 = SignalMessage, 3 = PreKeySignalMessage) ‖ message
//! ```
//!
//! - The clock is the Unix epoch.
//!
//! The code is shaped for its proofs (the interface does not depend on it):
//! - All I/O is in the four functions of the untranslated crate `libsignal-cli-io` (`io/`).
//! - No `core::fmt` on the paths of `init`, `send` and `recv`: file names are built by
//!   concatenation, and ids in decimal by `stores::name`.
//! - libsignal's four calls that draw coins are the four functions of two small crates,
//!   `libsignal-cli-ratchet` (`ratchet/`) and `libsignal-cli-handshake` (`handshake/`), so that
//!   their compiled code is the image's (`ratchet/src/lib.rs` says why). The coins are in
//!   `coins.rs`.

pub mod coins;
pub use libsignal_cli_io as io;
mod public;
mod stores;

use std::ffi::{CStr, c_char, c_int};
use std::time::SystemTime;

use libsignal_protocol::{
    CiphertextMessageType, DeviceId, GenericSignedPreKey, IdentityKeyPair, KeyPair, KyberPreKeyId,
    KyberPreKeyRecord, PreKeyId, PreKeyRecord, PreKeySignalMessage, ProtocolAddress, ServiceId,
    SignalMessage, SignalProtocolError, SignedPreKeyId, SignedPreKeyRecord, Timestamp, kem,
};
use public::read_bundle;
use rand_core::RngCore;
use libsignal_cli_handshake::{decrypt_prekey, initiate};
use libsignal_cli_ratchet::{Coins, decrypt_signal, encrypt};
use stores::Stores;

// ── The process ─────────────────────────────────────────────────────────────────────────────────

/// The process: musl's `__libc_start_main` calls it (the binary is `#![no_main]`).
#[unsafe(no_mangle)]
extern "C" fn main(argc: c_int, argv: *const *const c_char) -> c_int {
    // SAFETY: the C runtime passes `argc` NUL-terminated strings in `argv`.
    let args: Vec<&[u8]> = (1..argc as usize)
        .map(|i| unsafe { CStr::from_ptr(*argv.add(i)) }.to_bytes())
        .collect();
    let Some(call) = parse(&args) else {
        return 2;
    };
    // Only `send` and `recv` read stdin, so `keygen` and `init` don't wait on a terminal.
    let input = match call {
        Call::Send(_) | Call::Recv(_) => io::read_stdin(),
        Call::Keygen { .. } | Call::Init { .. } => Ok(Vec::new()),
    };
    let (Ok(coins), Ok(input)) = (io::read_file("coins"), input) else {
        return 2;
    };
    coins::install(coins.leak());
    // The stores write nothing until `commit`, so a rejected call (exit 1) leaves every file as it
    // was. Signal's own apps hold back store writes the same way (see `Stores::commit`).
    if matches!(call, Call::Send(_)) && input.len() > 1_000_000 {
        return 1;
    }
    let Ok((stores, output)) = run(call, Stores::open(), &input) else {
        return 1;
    };
    match stores.commit().and_then(|()| io::write_stdout(&output)) {
        Ok(()) => 0,
        Err(_) => 2,
    }
}

enum Call {
    Keygen {
        me: ProtocolAddress,
        n: u32,
    },
    Init {
        peer: ProtocolAddress,
        bundle: String,
    },
    Send(ProtocolAddress),
    Recv(ProtocolAddress),
}

fn parse(args: &[&[u8]]) -> Option<Call> {
    let args: Vec<&str> = args
        .iter()
        .map(|arg| std::str::from_utf8(arg).ok())
        .collect::<Option<_>>()?;
    Some(match args[..] {
        ["keygen", me, n] => Call::Keygen {
            me: address(me)?,
            n: n.parse().ok().filter(|n| *n <= 100)?,
        },
        ["init", peer, bundle] => Call::Init {
            peer: address(peer)?,
            bundle: bundle.to_owned(),
        },
        ["send", peer] => Call::Send(address(peer)?),
        ["recv", peer] => Call::Recv(address(peer)?),
        _ => return None,
    })
}

/// `<service id>.<device id>` as a protocol address. Only service ids: libsignal binds the two
/// addresses into a message's MAC only if they are, and they are safe file names.
fn address(text: &str) -> Option<ProtocolAddress> {
    let (name, device) = text.rsplit_once('.')?;
    ServiceId::parse_from_service_id_string(name)?;
    let device = DeviceId::new(device.parse().ok()?).ok()?;
    Some(ProtocolAddress::new(name.to_owned(), device))
}

// ── The operation ───────────────────────────────────────────────────────────────────────────────

/// libsignal rejected the call: any error from libsignal or from decoding the party's files, the
/// bundle or the input message.
struct Rejected;

impl<E: std::error::Error> From<E> for Rejected {
    fn from(_: E) -> Self {
        Rejected
    }
}

/// Runs `call` on the party's stores `s`, with the installed coins. Returns the stores, changed,
/// and the output message.
fn run(call: Call, mut s: Stores, input: &[u8]) -> Result<(Stores, Vec<u8>), Rejected> {
    let now = SystemTime::UNIX_EPOCH;
    // The party's own address (none yet before `keygen`).
    let me = address(&s.identity.address()?).ok_or(Rejected);

    let output = match call {
        Call::Keygen { me, n } => {
            keygen(&mut s, &me, n)?;
            Vec::new()
        }
        Call::Init { peer, bundle } => {
            let (me, bundle) = (me?, read_bundle(&bundle, peer.device_id())?);
            let (sessions, identity) = (&mut s.sessions, &mut s.identity);
            accepted(initiate(&peer, &me, sessions, identity, &bundle, now))?;
            Vec::new()
        }
        Call::Send(peer) => {
            let me = me?;
            let (sessions, identity) = (&mut s.sessions, &mut s.identity);
            let message = accepted(encrypt(input, &peer, &me, sessions, identity, now))?;
            [&[message.message_type() as u8], message.serialize()].concat()
        }
        // libsignal's `message_decrypt`, by message type.
        Call::Recv(peer) => {
            let me = me?;
            let (sessions, identity) = (&mut s.sessions, &mut s.identity);
            accepted(match decode_wire(input)? {
                Wire::Signal(message) => decrypt_signal(&message, &peer, &me, sessions, identity),
                Wire::PreKeySignal(message) => decrypt_prekey(
                    &message,
                    &peer,
                    &me,
                    sessions,
                    identity,
                    &mut s.one_time,
                    &s.signed,
                    &mut s.kyber,
                ),
            })?
        }
    };
    Ok((s, output))
}

/// A new party `me`: identity key pair and registration id, a signed pre-key and a last-resort
/// Kyber pre-key, and `n` one-time pre-keys of each kind, each signed pre-key signed by the
/// identity key, all from the coins. Each key is stored, and its public half published. The ids
/// are in the layout above.
fn keygen(s: &mut Stores, me: &ProtocolAddress, n: u32) -> Result<(), Rejected> {
    let coins = &mut Coins;
    let identity = IdentityKeyPair::generate(coins);
    let registration_id = coins.next_u32();
    s.identity.create(me, &identity, registration_id);
    s.public.identity(identity.identity_key(), registration_id);
    let never = Timestamp::from_epoch_millis(0);
    let sign =
        |key: &[u8], coins: &mut Coins| identity.private_key().calculate_signature(key, coins);

    let spk_id = SignedPreKeyId::from(1);
    let spk = KeyPair::generate(coins);
    let spk_signature = sign(&spk.public_key.serialize(), coins)?;
    let spk_record = SignedPreKeyRecord::new(spk_id, never, &spk, &spk_signature);
    s.signed.save(spk_id, &spk_record)?;
    s.public.signed_pre_key(&spk_record)?;

    let kyber_id = KyberPreKeyId::from(1);
    let kyber = kem::KeyPair::generate(kem::KeyType::Kyber1024, coins);
    let kyber_signature = sign(&kyber.public_key.serialize(), coins)?;
    let kyber_record = KyberPreKeyRecord::new(kyber_id, never, &kyber, &kyber_signature);
    s.kyber.save_last_resort(kyber_id, &kyber_record)?;
    s.public.last_resort_kyber_pre_key(&kyber_record)?;

    for i in 1..=n {
        let opk_id = PreKeyId::from(i);
        let opk_record = PreKeyRecord::new(opk_id, &KeyPair::generate(coins));
        s.one_time.save(opk_id, &opk_record)?;
        s.public.one_time_pre_key(&opk_record)?;

        let kyber_id = KyberPreKeyId::from(i + 1);
        let kyber = kem::KeyPair::generate(kem::KeyType::Kyber1024, coins);
        let kyber_signature = sign(&kyber.public_key.serialize(), coins)?;
        let kyber_record = KyberPreKeyRecord::new(kyber_id, never, &kyber, &kyber_signature);
        s.kyber.save_one_time(kyber_id, &kyber_record)?;
        s.public.one_time_kyber_pre_key(&kyber_record)?;
    }
    Ok(())
}

/// The result of one of libsignal's calls: `None` if it did not finish in one poll, which the
/// stores never cause (they answer at once).
fn accepted<T>(result: Option<Result<T, SignalProtocolError>>) -> Result<T, Rejected> {
    Ok(result.ok_or(Rejected)??)
}

// ── The messages ────────────────────────────────────────────────────────────────────────────────

/// The input of `recv`: a message of either type that `message_decrypt` takes.
enum Wire {
    Signal(SignalMessage),
    PreKeySignal(PreKeySignalMessage),
}

/// `wire`: a message tagged with its libsignal `CiphertextMessageType`.
fn decode_wire(wire: &[u8]) -> Result<Wire, Rejected> {
    const SIGNAL: u8 = CiphertextMessageType::Whisper as u8;
    const PRE_KEY_SIGNAL: u8 = CiphertextMessageType::PreKey as u8;
    Ok(match wire {
        [SIGNAL, message @ ..] => Wire::Signal(message.try_into()?),
        [PRE_KEY_SIGNAL, message @ ..] => Wire::PreKeySignal(message.try_into()?),
        _ => return Err(Rejected),
    })
}

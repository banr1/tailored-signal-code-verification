// Copyright 2026 Google LLC; SPDX-License-Identifier: Apache-2.0.
// See `third_party/libsignal/README.md` and `Symbolic/BugInjection/README.md`.
//
// Generic witness replayer of the bug-injection framework. It reads a witness-input file (the
// environment's calls and their free arguments, as byte expressions), drives the `libsignal-cli`
// CLI binary (`CompRefinesCliElf`) on provisioned party directories in that order, and RECORDS the
// structured CLI events (`CliEvent.run` carrying `RunEvent { party, cmd, input, coins, exit }`;
// `clear` emits no event per D7). It prints one JSON object: the setup bytes, the Kyber
// ciphertexts Bob received, the events (`evs`), per-call results, and any calls the statement's
// environment (`CliNextCall`) does not allow. Nothing here is specific to a bug.
//
// This file is ORIGINAL code written for this repository; it copies no upstream source.
//
// Usage: `libsignal-bug-harness <witness-inputs.json> [<statement>]`.

use std::cell::{Cell, RefCell};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use libsignal_protocol::{
    GenericSignedPreKey, IdentityKeyPair, KeyPair, KyberPreKeyId, KyberPreKeyRecord, PreKeyId,
    PreKeyRecord, PreKeySignalMessage, SessionRecord, SignalMessage, SignedPreKeyId,
    SignedPreKeyRecord, Timestamp, kem,
};
use serde_json::{Value, json};

// ---------------------------------------------------------------------------
// Deterministic coin stream and recorded `CliEvent` log
// ---------------------------------------------------------------------------

thread_local! {
    static HOOK_STATE: Cell<u64> = const { Cell::new(0) };
    static EVENTS: RefCell<Vec<Value>> = const { RefCell::new(Vec::new()) };
}

fn splitmix(s: &Cell<u64>) -> u64 {
    let mut z = s.get().wrapping_add(0x9e37_79b9_7f4a_7c15);
    s.set(z);
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    z ^ (z >> 31)
}

fn record_run(
    who: u32,
    cmd: Value,
    input: &[u8],
    coins: &[u8],
    code: Option<i32>,
    stdout: &[u8],
) {
    let party = if who == 0 { "alice" } else { "bob" };
    let exit = code.map(|c| json!({"code": c as u32, "stdout": hex(stdout)}));
    EVENTS.with(|e| {
        e.borrow_mut().push(json!({
            "kind": "run",
            "party": party,
            "cmd": cmd,
            "input": hex(input),
            "coins": hex(coins),
            "exit": exit,
        }));
    });
}

fn record_leak(who: u32, secret: &[u8]) {
    let party = if who == 0 { "alice" } else { "bob" };
    EVENTS.with(|e| {
        e.borrow_mut().push(json!({
            "kind": "leak",
            "party": party,
            "secret": hex(secret),
        }));
    });
}

struct TestRng(Cell<u64>);

impl rand_core::RngCore for TestRng {
    fn next_u32(&mut self) -> u32 {
        splitmix(&self.0) as u32
    }
    fn next_u64(&mut self) -> u64 {
        splitmix(&self.0)
    }
    fn fill_bytes(&mut self, dst: &mut [u8]) {
        for chunk in dst.chunks_mut(8) {
            let w = splitmix(&self.0).to_le_bytes();
            chunk.copy_from_slice(&w[..chunk.len()]);
        }
    }
}
impl rand_core::CryptoRng for TestRng {}

// ---------------------------------------------------------------------------
// The setup (the statement's `Records`): generated from a seed, optional one-time prekey
// ---------------------------------------------------------------------------

struct Setup {
    alice: IdentityKeyPair,
    bob: IdentityKeyPair,
    spk: KeyPair,
    kpk: kem::KeyPair,
    spk_sig: Vec<u8>,
    kpk_sig: Vec<u8>,
    opk: Option<(u32, KeyPair)>,
    reg_a: u32,
    reg_b: u32,
    spk_id: u32,
    kpk_id: u32,
}

fn make_setup(seed: u64, with_opk: bool) -> Setup {
    let mut rng = TestRng(Cell::new(seed));
    let alice = IdentityKeyPair::generate(&mut rng);
    let bob = IdentityKeyPair::generate(&mut rng);
    let spk = KeyPair::generate(&mut rng);
    let kpk = kem::KeyPair::generate(kem::KeyType::Kyber1024, &mut rng);
    let spk_sig =
        bob.private_key().calculate_signature(&spk.public_key.serialize(), &mut rng).unwrap().to_vec();
    let kpk_sig =
        bob.private_key().calculate_signature(&kpk.public_key.serialize(), &mut rng).unwrap().to_vec();
    let opk = if with_opk {
        Some((3, KeyPair::generate(&mut rng)))
    } else {
        None
    };
    Setup {
        alice,
        bob,
        spk,
        kpk,
        spk_sig,
        kpk_sig,
        opk,
        reg_a: 1111,
        reg_b: 2222,
        spk_id: 7,
        kpk_id: 9,
    }
}

impl Setup {
    /// Bob's honest bundle (1813 bytes, `parse_bundle`; `HonestBundle`).
    fn honest_bundle(&self) -> Vec<u8> {
        let mut v = self.reg_b.to_le_bytes().to_vec();
        if let Some((opk_id, ref opk)) = self.opk {
            v.push(1u8);
            v.extend_from_slice(&opk_id.to_le_bytes());
            v.extend_from_slice(&opk.public_key.serialize());
        } else {
            v.extend_from_slice(&[0u8; 38]);
        }
        v.extend_from_slice(&self.spk_id.to_le_bytes());
        v.extend_from_slice(&self.spk.public_key.serialize());
        v.extend_from_slice(&self.spk_sig);
        v.extend_from_slice(&self.kpk_id.to_le_bytes());
        v.extend_from_slice(&self.kpk.public_key.serialize());
        v.extend_from_slice(&self.kpk_sig);
        v.extend_from_slice(&self.bob.identity_key().serialize());
        v
    }
}

// ---------------------------------------------------------------------------
// Byte expressions of the witness inputs
// ---------------------------------------------------------------------------

/// One completed call: what stdout message it returned (`None` = null).
struct CallResult {
    message: Option<Vec<u8>>,
}

fn unhex(s: &str) -> Vec<u8> {
    (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).expect("hex")).collect()
}

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

fn find(hay: &[u8], needle: &[u8]) -> usize {
    hay.windows(needle.len()).position(|w| w == needle).expect("needle not found")
}

/// Evaluate a byte expression:
///   {"hex": "…"} | {"utf8": "…"} | {"honest_bundle": true}
///   {"message_of": i}             the message call `i` returned
///   {"slice": e, "after": e', "offset": k, "len": n}

///       `n` bytes of `e`, `k` bytes after the first occurrence of `e'`
///   {"replace": e, "find": e', "with": e''}   first occurrence of `e'` in `e` replaced
///   {"or_at": e, "after": e', "offset": k, "mask": "80"}   byte `k` after `e'` OR-ed with `mask`
fn eval(x: &Value, s: &Setup, done: &[CallResult]) -> Vec<u8> {
    let sub = |k: &str| eval(&x[k], s, done);
    if let Some(h) = x.get("hex") {
        unhex(h.as_str().unwrap())
    } else if let Some(t) = x.get("utf8") {
        t.as_str().unwrap().as_bytes().to_vec()
    } else if x.get("honest_bundle").is_some() {
        s.honest_bundle()
    } else if let Some(i) = x.get("message_of") {
        done[i.as_u64().unwrap() as usize].message.clone().expect("that call returned null")
    } else if x.get("slice").is_some() {
        let b = sub("slice");
        let at = find(&b, &sub("after")) + x["offset"].as_u64().unwrap() as usize;
        b[at..at + x["len"].as_u64().unwrap() as usize].to_vec()
    } else if x.get("replace").is_some() {
        let mut b = sub("replace");
        let (needle, with) = (sub("find"), sub("with"));
        let at = find(&b, &needle);
        b.splice(at..at + needle.len(), with);
        b
    } else if x.get("or_at").is_some() {
        let mut b = sub("or_at");
        let at = find(&b, &sub("after")) + x["offset"].as_u64().unwrap() as usize;
        b[at] |= unhex(x["mask"].as_str().unwrap())[0];
        b
    } else {
        panic!("unknown byte expression {x}")
    }
}

// ---------------------------------------------------------------------------
// Calls and statement-environment (`AttackerTurn` / `NextCall`) checks
// ---------------------------------------------------------------------------

const STMT_COMP_CLI: &str = "DY.Libsignal.Composed.Refinement.Cli.CompRefinesCliElf";

const ALICE_UUID: &str = "8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b";
const BOB_UUID: &str = "5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6";
const ALICE_ADDR: &str = "8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b.1";
const BOB_ADDR: &str = "5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6.1";
const PARTY_DIRS: [&str; 11] = [
    "identities",
    "sessions",
    "signed-pre-keys",
    "one-time-pre-keys",
    "one-time-kyber-pre-keys",
    "last-resort-kyber-pre-keys",
    "public",
    "public/signed-pre-keys",
    "public/one-time-pre-keys",
    "public/one-time-kyber-pre-keys",
    "public/last-resort-kyber-pre-keys",
];

/// Parse a wire `PreKeySignalMessage` (`0x03 ‖ body`).
fn parse_prekey_wire(b: &[u8]) -> Option<PreKeySignalMessage> {
    let [3, body @ ..] = b else { return None };
    PreKeySignalMessage::try_from(body).ok()
}

/// `PqFromHonest` (`DEV-TR-SPQR-MSG`, `Refinement/Composed/Statement.lean`): if
/// `body` decodes as a `SignalMessage`, its `pq_ratchet` equals that of one of `sent`.
fn pq_from_honest(sent: &[Vec<u8>], body: &[u8]) -> bool {
    let Ok(m) = SignalMessage::try_from(body) else { return true };
    sent.iter().any(|s| {
        SignalMessage::try_from(s.as_slice())
            .map(|m2| m2.pq_ratchet() == m.pq_ratchet())
            .unwrap_or(false)
    })
}

/// `sentBody` (`Refinement/Composed/Statement.lean`): the `SignalMessage` body of a
/// sent wire message (`0x02 ‖ body` or the inner message of `0x03 ‖ PreKeySignalMessage`).
fn sent_body(msg: &[u8]) -> Option<Vec<u8>> {
    match msg.first() {
        Some(&2) => Some(msg[1..].to_vec()),
        Some(&3) => parse_prekey_wire(msg).map(|pk| pk.message().serialized().to_vec()),
        _ => None,
    }
}

/// Read a protobuf varint at the start of `s`, returning `(value, rest)`.
fn read_varint(mut s: &[u8]) -> Option<(usize, &[u8])> {
    let mut val = 0usize;
    let mut shift = 0;
    while let Some((&b, rest)) = s.split_first() {
        s = rest;
        val |= ((b & 0x7f) as usize) << shift;
        if b & 0x80 == 0 {
            return Some((val, s));
        }
        shift += 7;
        if shift >= 64 {
            return None;
        }
    }
    None
}

/// Collect length-delimited (wire type 2) fields `(field_number, bytes)` of a protobuf message.
fn pb_len_fields(mut s: &[u8]) -> Option<Vec<(usize, &[u8])>> {
    let mut out = Vec::new();
    while !s.is_empty() {
        let (key, rest) = read_varint(s)?;
        let (tag, wt) = (key >> 3, key & 7);
        match wt {
            0 => {
                let (_, rest) = read_varint(rest)?;
                s = rest;
            }
            1 => {
                if rest.len() < 8 {
                    return None;
                }
                s = &rest[8..];
            }
            2 => {
                let (len, rest) = read_varint(rest)?;
                if rest.len() < len {
                    return None;
                }
                out.push((tag, &rest[..len]));
                s = &rest[len..];
            }
            5 => {
                if rest.len() < 4 {
                    return None;
                }
                s = &rest[4..];
            }
            _ => return None,
        }
    }
    Some(out)
}

/// Read `current.receiver_chains[idx].sender_ratchet_key_private` from a serialized `SessionRecord`
/// (`KeyInRecord`, `Symbolic/Specifications/Concrete/SessionRecord.lean`), if non-empty.
fn read_recv_chain_priv(rec: &[u8], idx: usize) -> Option<Vec<u8>> {
    let top = pb_len_fields(rec)?;
    let (_, cur) = top.into_iter().find(|&(t, _)| t == 1)?;
    let s_fields = pb_len_fields(cur)?;
    let (_, chain) = s_fields.into_iter().filter(|&(t, _)| t == 7).nth(idx)?;
    let c_fields = pb_len_fields(chain)?;
    let (_, priv_bytes) = c_fields.into_iter().find(|&(t, _)| t == 2)?;
    if priv_bytes.is_empty() {
        None
    } else {
        Some(priv_bytes.to_vec())
    }
}

/// Read Bob's unconsumed one-time pre-key secret from `one-time-pre-keys/<opk_id>` (`KeyInDir`), if
/// the file is still non-empty on disk.
fn read_opk_priv(bob_dir: &Path, opk_id: u32) -> Option<Vec<u8>> {
    let bytes = non_empty_file(&bob_dir.join(format!("one-time-pre-keys/{opk_id}")))?;
    let rec = PreKeyRecord::deserialize(&bytes).ok()?;
    let priv_bytes = rec.private_key().ok()?.serialize().to_vec();
    if priv_bytes.is_empty() {
        None
    } else {
        Some(priv_bytes)
    }
}

/// `SingleSession rec` (`DEV-C-PREV`, `Refinement/Composed/Statement.lean:530`):
/// serialized `SessionRecord` `rec` has only field 1 (`current_session`, tag `0x0a`) and no field 2
/// (`previous_sessions`, tag `0x12`), i.e., `rr.previous = []`.
fn single_session(rec: &[u8]) -> bool {
    let Some((0x0a, after_tag)) = read_varint(rec) else { return false };
    let Some((len, after_len)) = read_varint(after_tag) else { return false };
    after_len.len() == len && SessionRecord::deserialize(rec).is_ok()
}

/// `PromoteMatch rec b` (`DEV-C-PREV`, `Refinement/Composed/Statement.lean:524`):
/// `rec` has no previous session (`single_session`) and its current session's `alice_base_key`
/// equals `b`'s base key.
fn promote_match(rec: &[u8], b: &[u8]) -> bool {
    let Some(pk) = parse_prekey_wire(b) else { return false };
    single_session(rec)
        && SessionRecord::deserialize(rec)
            .ok()
            .and_then(|r| {
                r.alice_base_key().ok().map(|k| k == pk.base_key().serialize().as_ref())
            })
            .unwrap_or(false)
}

fn draw_coins(len: usize) -> Vec<u8> {
    let mut out = vec![0u8; len];
    HOOK_STATE.with(|s| {
        for chunk in out.chunks_mut(8) {
            let w = splitmix(s).to_le_bytes();
            chunk.copy_from_slice(&w[..chunk.len()]);
        }
    });
    out
}

/// `parseBundleFiles` + `bundleBlob` (`Symbolic/Specifications/Refinement/Statement.lean:140-198`):
/// reconstructs the 1813-byte bundle blob as `runInput` records it from `bundle/`, or `[]` if
/// `read_bundle` fails.
fn read_bundle_blob(bundle_dir: &Path) -> Vec<u8> {
    let read = |name: &str| std::fs::read(bundle_dir.join(name)).unwrap_or_default();
    let parse_ec = |bs: &[u8]| -> Option<Vec<u8>> {
        if bs.first() == Some(&0x05) && bs.len() >= 33 {
            Some(bs[..33].to_vec())
        } else {
            None
        }
    };
    let parse_kyber = |bs: &[u8]| -> Option<Vec<u8>> {
        if bs.first() == Some(&0x08) && bs.len() == 1569 {
            Some(bs.to_vec())
        } else {
            None
        }
    };
    fn split_signed(bs: &[u8]) -> Option<(&[u8], &[u8], &[u8])> {
        if bs.len() < 4 + 64 {
            return None;
        }
        let rest = &bs[4..];
        let cut = rest.len() - 64;
        Some((&bs[..4], &rest[..cut], &rest[cut..]))
    }

    let id_file = read("identity-key");
    let reg_file = read("registration-id");
    let spk_file = read("signed-pre-key");
    let kpk_file = read("kyber-pre-key");
    let opk_file = read("one-time-pre-key");

    let Some(id_key) = parse_ec(&id_file) else { return Vec::new() };
    if reg_file.len() != 4 {
        return Vec::new();
    }
    let Some((spk_id, spk_raw, spk_sig)) = split_signed(&spk_file) else { return Vec::new() };
    let Some((kpk_id, kpk_raw, kpk_sig)) = split_signed(&kpk_file) else { return Vec::new() };
    let opk_blob = if opk_file.is_empty() {
        vec![0u8; 38]
    } else if opk_file.len() >= 4 {
        let Some(opk_key) = parse_ec(&opk_file[4..]) else { return Vec::new() };
        let mut v = vec![1u8];
        v.extend_from_slice(&opk_file[..4]);
        v.extend_from_slice(&opk_key);
        v
    } else {
        return Vec::new();
    };
    let Some(spk_key) = parse_ec(spk_raw) else { return Vec::new() };
    let Some(kpk_key) = parse_kyber(kpk_raw) else { return Vec::new() };

    let mut out = Vec::with_capacity(1813);
    out.extend_from_slice(&reg_file);
    out.extend_from_slice(&opk_blob);
    out.extend_from_slice(spk_id);
    out.extend_from_slice(&spk_key);
    out.extend_from_slice(spk_sig);
    out.extend_from_slice(kpk_id);
    out.extend_from_slice(&kpk_key);
    out.extend_from_slice(kpk_sig);
    out.extend_from_slice(&id_key);
    out
}

fn non_empty_file(path: &Path) -> Option<Vec<u8>> {
    std::fs::read(path).ok().filter(|v| !v.is_empty())
}

fn dir_files_bounded(dir: &Path) -> bool {
    let Ok(rd) = std::fs::read_dir(dir) else { return true };
    for ent in rd {
        let Ok(ent) = ent else { return false };
        let Ok(ft) = ent.file_type() else { return false };
        if ft.is_dir() {
            if !dir_files_bounded(&ent.path()) {
                return false;
            }
        } else if ft.is_file() {
            let Ok(meta) = ent.metadata() else { return false };
            if meta.len() >= (1u64 << 31) {
                return false;
            }
        }
    }
    true
}

fn provision_cli_dirs(workdir: &Path, s: &Setup) -> (PathBuf, PathBuf) {
    let alice_dir = workdir.join("alice");
    let bob_dir = workdir.join("bob");
    for party in [&alice_dir, &bob_dir] {
        for sub in PARTY_DIRS {
            std::fs::create_dir_all(party.join(sub)).unwrap();
        }
    }
    std::fs::write(alice_dir.join("address"), ALICE_ADDR.as_bytes()).unwrap();
    std::fs::write(alice_dir.join("identity-key-pair"), &*s.alice.serialize()).unwrap();
    std::fs::write(alice_dir.join("registration-id"), s.reg_a.to_le_bytes()).unwrap();
    std::fs::write(
        alice_dir.join("identities").join(BOB_UUID),
        &*s.bob.identity_key().serialize(),
    )
    .unwrap();

    std::fs::write(bob_dir.join("address"), BOB_ADDR.as_bytes()).unwrap();
    std::fs::write(bob_dir.join("identity-key-pair"), &*s.bob.serialize()).unwrap();
    std::fs::write(bob_dir.join("registration-id"), s.reg_b.to_le_bytes()).unwrap();
    std::fs::write(
        bob_dir.join("identities").join(ALICE_UUID),
        &*s.alice.identity_key().serialize(),
    )
    .unwrap();
    let spk_rec = SignedPreKeyRecord::new(
        SignedPreKeyId::from(s.spk_id),
        Timestamp::from_epoch_millis(0),
        &s.spk,
        &s.spk_sig,
    )
    .serialize()
    .unwrap();
    std::fs::write(bob_dir.join(format!("signed-pre-keys/{}", s.spk_id)), &spk_rec).unwrap();
    let kpk_rec = KyberPreKeyRecord::new(
        KyberPreKeyId::from(s.kpk_id),
        Timestamp::from_epoch_millis(0),
        &s.kpk,
        &s.kpk_sig,
    )
    .serialize()
    .unwrap();
    std::fs::write(bob_dir.join(format!("last-resort-kyber-pre-keys/{}", s.kpk_id)), &kpk_rec)
        .unwrap();
    std::fs::write(bob_dir.join(format!("last-resort-kyber-pre-keys/{}.base-keys", s.kpk_id)), [])
        .unwrap();
    if let Some((opk_id, ref opk)) = s.opk {
        let opk_rec = PreKeyRecord::new(PreKeyId::from(opk_id), opk).serialize().unwrap();
        std::fs::write(bob_dir.join(format!("one-time-pre-keys/{opk_id}")), &opk_rec).unwrap();
    }
    (alice_dir, bob_dir)
}

fn run_cli_cmd(
    cli_bin: &str,
    party_dir: &Path,
    args: &[&str],
    stdin_bytes: &[u8],
) -> (Option<i32>, Vec<u8>) {
    let mut child = Command::new(cli_bin)
        .current_dir(party_dir)
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to spawn libsignal-cli");
    if let Some(mut stdin) = child.stdin.take() {
        let _ = stdin.write_all(stdin_bytes);
    }
    let out = child.wait_with_output().expect("failed to wait on libsignal-cli");
    let code = out.status.code();
    assert!(
        code != Some(2),
        "libsignal-cli exited 2 (args={args:?}): {}",
        String::from_utf8_lossy(&out.stderr)
    );
    (code, out.stdout)
}

fn run_cli_trace(
    w: &Value,
    s: &Setup,
    done: &mut Vec<CallResult>,
    calls: &mut Vec<Value>,
    outside: &mut Vec<String>,
) {
    let cli_bin = std::env::var("LIBSIGNAL_CLI_BIN").expect("LIBSIGNAL_CLI_BIN");
    let workdir = PathBuf::from(
        std::env::var("LIBSIGNAL_CLI_WORKDIR").expect("LIBSIGNAL_CLI_WORKDIR"),
    );
    assert!(
        workdir.components().any(|c| c.as_os_str() == ".lake"),
        "LIBSIGNAL_CLI_WORKDIR must be inside the worktree .lake directory"
    );
    if workdir.exists() {
        std::fs::remove_dir_all(&workdir).unwrap();
    }
    std::fs::create_dir_all(&workdir).unwrap();
    let (alice_dir, bob_dir) = provision_cli_dirs(&workdir, s);
    let mut sent: Vec<Vec<u8>> = Vec::new();
    let mut bob_off = false;
    let mut aborted = false;
    let mut pending_leaks = false;

    for (n, c) in w["calls"].as_array().unwrap().iter().enumerate() {
        let entry = c["entry"].as_str().unwrap().to_owned();
        if aborted {
            outside.push(format!("call {n}: trace continues after an aborted CLI run"));
            break;
        }
        if entry == "clear" {
            if pending_leaks {
                outside.push(format!(
                    "call {n}: clear after leak without an intervening CLI run (CliTraces.step)"
                ));
            }
            let who = c.get("who").and_then(Value::as_u64).expect("clear needs who") as u32;
            if who > 1 {
                outside.push(format!("call {n}: invalid caller {who}"));
            } else {
                let (party_dir, peer_addr) = if who == 0 {
                    (&alice_dir, BOB_ADDR)
                } else {
                    (&bob_dir, ALICE_ADDR)
                };
                let _ = std::fs::remove_file(party_dir.join("sessions").join(peer_addr));
                if who == 1 {
                    bob_off = false;
                }
            }
            done.push(CallResult { message: None });
            continue;
        }
        if entry == "leak" {
            let who = c.get("who").and_then(Value::as_u64).expect("leak needs who") as u32;
            let leaked = if who > 1 {
                outside.push(format!("call {n}: invalid caller {who}"));
                None
            } else {
                let (party_dir, peer_addr) = if who == 0 {
                    (&alice_dir, BOB_ADDR)
                } else {
                    (&bob_dir, ALICE_ADDR)
                };
                let secret_spec = &c["secret"];
                if secret_spec.as_str() == Some("opk") {
                    if who != 1 {
                        outside.push(format!("call {n}: opk leak caller is not Bob (KeyInDir)"));
                        None
                    } else if let Some((opk_id, _)) = s.opk {
                        read_opk_priv(&bob_dir, opk_id)
                    } else {
                        outside.push(format!("call {n}: opk leak when with_opk is false (KeyInDir)"));
                        None
                    }
                } else if let Some(idx) = secret_spec.get("recv_chain_priv").and_then(Value::as_u64) {
                    non_empty_file(&party_dir.join("sessions").join(peer_addr))
                        .and_then(|rec| read_recv_chain_priv(&rec, idx as usize))
                } else {
                    panic!("unknown leak secret {secret_spec}");
                }
            };
            let returned = if let Some(priv_bytes) = leaked {
                record_leak(who, &priv_bytes);
                pending_leaks = true;
                true
            } else {
                false
            };
            calls.push(json!({"entry": "leak", "who": who, "returned": returned}));
            done.push(CallResult { message: None });
            continue;
        }
        pending_leaks = false;

        let b = c.get("b").map(|x| eval(x, s, done)).unwrap_or_default();
        let who = c
            .get("who")
            .and_then(Value::as_u64)
            .map(|w| w as u32)
            .unwrap_or(match entry.as_str() {
                "recv" => 1,
                _ => 0,
            });
        let (party_dir, peer_addr, peer_name) = if who == 0 {
            (&alice_dir, BOB_ADDR, BOB_UUID)
        } else {
            (&bob_dir, ALICE_ADDR, ALICE_UUID)
        };
        if who > 1 {
            outside.push(format!("call {n}: invalid caller {who}"));
        }
        if bob_off && who == 1 {
            outside.push(format!("call {n}: Bob called while switched off (BobCallAllowed)"));
        }
        if !dir_files_bounded(party_dir) {
            outside.push(format!("call {n}: caller directory violates FilesBounded"));
        }

        match entry.as_str() {
            "init" => {
                if who != 0 {
                    outside.push(format!("call {n}: init caller is not Alice (DEV-C-ROLES)"));
                }
                if non_empty_file(&party_dir.join("sessions").join(peer_addr)).is_some() {
                    outside.push(format!("call {n}: init while Alice already holds a session"));
                }
                if b != s.honest_bundle() {
                    outside.push(format!(
                        "call {n}: init bundle is not HonestBundleFiles (DEV-PQS-BUNDLE)"
                    ));
                }
                let bundle_dir = party_dir.join("bundle");
                std::fs::create_dir_all(&bundle_dir).unwrap();
                if b.len() == 1813 {
                    std::fs::write(bundle_dir.join("identity-key"), &b[1780..1813]).unwrap();
                    std::fs::write(bundle_dir.join("registration-id"), &b[0..4]).unwrap();
                    std::fs::write(
                        bundle_dir.join("signed-pre-key"),
                        [&b[42..46], &b[46..79], &b[79..143]].concat(),
                    )
                    .unwrap();
                    std::fs::write(
                        bundle_dir.join("kyber-pre-key"),
                        [&b[143..147], &b[147..1716], &b[1716..1780]].concat(),
                    )
                    .unwrap();
                    if b[4] == 1 {
                        std::fs::write(bundle_dir.join("one-time-pre-key"), &b[5..42]).unwrap();
                    }
                }
                let run_input = read_bundle_blob(&bundle_dir);
                let coins = draw_coins(192);
                std::fs::write(party_dir.join("coins"), &coins).unwrap();
                let (code, stdout) = run_cli_cmd(&cli_bin, party_dir, &["init", peer_addr, "bundle"], &[]);
                let _ = std::fs::remove_file(party_dir.join("coins"));
                let _ = std::fs::remove_dir_all(&bundle_dir);
                let ok = code == Some(0);
                if code.is_none() {
                    aborted = true;
                }
                record_run(
                    who,
                    json!({"op": "init", "peer_name": peer_name, "peer_device": 1, "bundle": "bundle"}),
                    &run_input,
                    &coins,
                    code,
                    &stdout,
                );
                calls.push(json!({"entry": "init", "who": who, "returned": ok}));
                done.push(CallResult {
                    message: if ok { Some(stdout) } else { None },
                });
            }
            "send" => {
                if non_empty_file(&party_dir.join("sessions").join(peer_addr)).is_none() {
                    outside.push(format!("call {n}: send without an active session"));
                }
                if sent.len() as u64 >= (1u64 << 32) - 1 {
                    outside.push(format!("call {n}: sent count exceeds DEV-TR-NS bound"));
                }
                if b.len() as u64 >= (1u64 << 32) {
                    outside.push(format!("call {n}: send plaintext violates StdinBounded"));
                }
                let coins = draw_coins(64);
                std::fs::write(party_dir.join("coins"), &coins).unwrap();
                let (code, stdout) = run_cli_cmd(&cli_bin, party_dir, &["send", peer_addr], &b);
                let _ = std::fs::remove_file(party_dir.join("coins"));
                let ok = code == Some(0);
                if code.is_none() {
                    aborted = true;
                }
                if ok {
                    if let Some(body) = sent_body(&stdout) {
                        sent.push(body);
                    }
                }
                record_run(
                    who,
                    json!({"op": "send", "peer_name": peer_name, "peer_device": 1}),
                    &b,
                    &coins,
                    code,
                    &stdout,
                );
                calls.push(json!({"entry": "send", "who": who, "returned": ok}));
                done.push(CallResult {
                    message: if ok { Some(stdout) } else { None },
                });
            }
            "recv" => {
                let sess = non_empty_file(&party_dir.join("sessions").join(peer_addr));
                if b.first() == Some(&2) && (b.len() - 1) as u64 >= (1u64 << 32) {
                    outside.push(format!("call {n}: recv whisper body violates StdinBounded"));
                }
                if b.first() != Some(&2) && (b.len() as u64) >= (1u64 << 32) {
                    outside.push(format!("call {n}: recv non-whisper stdin violates StdinBounded"));
                }
                if let Some(pk) = parse_prekey_wire(&b) {
                    if (pk.message().serialized().len() as u64) + 2048 >= (1u64 << 32) {
                        outside.push(format!("call {n}: recv pre-key inner message violates StdinBounded"));
                    }
                }
                let whisper_ok =
                    sess.is_some() && b.first() == Some(&2) && pq_from_honest(&sent, &b[1..]);
                let bob_recv_ok = who == 1
                    && (b.first() != Some(&2) || sess.is_none())
                    && parse_prekey_wire(&b)
                        .map(|pk| pq_from_honest(&sent, pk.message().serialized()))
                        .unwrap_or(true);
                if !whisper_ok && !bob_recv_ok {
                    outside.push(format!(
                        "call {n}: recv violates CliNextCall (neither honest whisper on session nor Bob recv with honest pq_ratchet)"
                    ));
                }
                let pre_key_no_match = who == 1
                    && b.first() != Some(&2)
                    && sess.as_deref().is_some_and(|rec| !promote_match(rec, &b));
                let coins = draw_coins(32);
                std::fs::write(party_dir.join("coins"), &coins).unwrap();
                let (code, stdout) = run_cli_cmd(&cli_bin, party_dir, &["recv", peer_addr], &b);
                let _ = std::fs::remove_file(party_dir.join("coins"));
                let ok = code == Some(0);
                if code.is_none() {
                    aborted = true;
                }
                if ok && pre_key_no_match {
                    bob_off = true;
                }
                record_run(
                    who,
                    json!({"op": "recv", "peer_name": peer_name, "peer_device": 1}),
                    &b,
                    &coins,
                    code,
                    &stdout,
                );
                calls.push(json!({"entry": "recv", "who": who, "returned": ok}));
                done.push(CallResult {
                    message: if ok { Some(stdout) } else { None },
                });
            }
            other => panic!("unknown CLI entry {other}"),
        }
    }

    if !aborted && pending_leaks {
        outside.push("trailing leak without a following CLI run (CliTraces.step)".to_owned());
    }
    let _ = std::fs::remove_dir_all(&workdir);
}

fn main() {
    let path = std::env::args()
        .nth(1)
        .expect("usage: libsignal-bug-harness <witness-inputs.json> [<statement>]");
    let statement = std::env::args().nth(2).unwrap_or_else(|| STMT_COMP_CLI.to_owned());
    assert!(statement == STMT_COMP_CLI, "unknown statement {statement}");
    let w: Value = serde_json::from_str(&std::fs::read_to_string(&path).unwrap()).unwrap();
    let with_opk = w.get("with_opk").and_then(Value::as_bool).unwrap_or(false);
    let s = make_setup(w["setup_seed"].as_u64().unwrap(), with_opk);
    HOOK_STATE.with(|h| h.set(w["rng_seed"].as_u64().unwrap()));

    let mut done: Vec<CallResult> = Vec::new();
    let mut calls = Vec::new();
    let mut outside = Vec::new();
    run_cli_trace(&w, &s, &mut done, &mut calls, &mut outside);

    let events: Vec<Value> = EVENTS.with(|e| e.borrow().clone());
    // The Kyber ciphertexts (without type byte) of the pre-key messages Bob received: protobuf
    // field 8 of `PreKeySignalMessage`, `0x42 0xa1 0x0c` (length 1569), then type byte `0x08`.
    let mut kyber_cts = Vec::new();
    for ev in &events {
        if ev["kind"] == "run" && ev["cmd"]["op"] == "recv" {
            let b = unhex(ev["input"].as_str().unwrap());
            if b.first() == Some(&3) {
                if let Some(at) = b.windows(4).position(|w| w == [0x42, 0xa1, 0x0c, 0x08]) {
                    kyber_cts.push(b[at + 4..at + 4 + 1568].to_vec());
                }
            }
        }
    }
    let kyber_pk = s.kpk.public_key.serialize();
    let out = json!({
        "setup": {
            "alice_id": hex(&s.alice.private_key().serialize()),
            "bob_id": hex(&s.bob.private_key().serialize()),
            "spk": hex(&s.spk.private_key.serialize()),
            "spk_sig": hex(&s.spk_sig),
            "kyber_pk": hex(&kyber_pk[1..]),
            "kyber_pk_sig": hex(&s.kpk_sig),
            "kyber_sec": hex(&s.kpk.secret_key.serialize()),
            "reg_id_a": s.reg_a, "reg_id_b": s.reg_b, "spk_id": s.spk_id, "kpk_id": s.kpk_id,
        },
        "kyber_cts": kyber_cts.iter().map(|c| hex(c)).collect::<Vec<_>>(),
        "events": events,
        "calls": calls,
        "outside_statement": outside,
    });
    println!("{out}");
}

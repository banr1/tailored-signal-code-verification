// Copyright 2026 Google LLC; SPDX-License-Identifier: Apache-2.0.
// See `third_party/libsignal/README.md`.
//
// Host end-to-end integration tests for the `libsignal-cli` CLI (`cli/src/`):
// `cargo test --locked --test cli_pqxdh_roundtrip`.
//
// This file is ORIGINAL code written for this repository.
//
// Every party state and session record is produced exclusively by invoking the real
// `libsignal-cli` CLI (`keygen`, `init`, `send`, `recv`) in per-party directories with
// deterministic `coins` files (no hardcoded session records).

use std::cell::Cell;
use std::collections::BTreeMap;
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::OnceLock;
use std::sync::atomic::{AtomicU64, Ordering};

use libsignal_protocol::{SessionRecord, SignalMessage};

// ---------------------------------------------------------------------------
// Deterministic SplitMix64 coin generator
// ---------------------------------------------------------------------------

struct CoinStream(Cell<u64>);

impl CoinStream {
    fn new(seed: u64) -> Self {
        Self(Cell::new(seed))
    }

    fn next_u64(&self) -> u64 {
        let mut z = self.0.get().wrapping_add(0x9e37_79b9_7f4a_7c15);
        self.0.set(z);
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    fn bytes(&self, len: usize) -> Vec<u8> {
        let mut out = vec![0u8; len];
        for chunk in out.chunks_mut(8) {
            let w = self.next_u64().to_le_bytes();
            chunk.copy_from_slice(&w[..chunk.len()]);
        }
        out
    }

    /// Generates `len` deterministic non-zero bytes so truncation at any consumed index replaces a
    /// non-zero byte with `0` (used for exact coin-consumption detection).
    fn nonzero_bytes(&self, len: usize) -> Vec<u8> {
        let mut out = self.bytes(len);
        for b in &mut out {
            if *b == 0 {
                *b = 1;
            }
        }
        out
    }
}

// ---------------------------------------------------------------------------
// CLI binary builder & isolated workspace (under gitignored `target/`, never `/tmp`)
// ---------------------------------------------------------------------------

static CLI_BIN: OnceLock<PathBuf> = OnceLock::new();
static NEXT_WS_ID: AtomicU64 = AtomicU64::new(1);

fn cli_bin() -> &'static Path {
    CLI_BIN
        .get_or_init(|| {
            let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
            let cargo = std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into());
            let status = Command::new(cargo)
                .current_dir(&manifest_dir)
                .args(["build", "--locked", "--quiet", "-p", "libsignal-cli", "--bin", "libsignal-cli"])
                .status()
                .expect("spawn cargo build --bin libsignal-cli");
            assert!(status.success(), "building libsignal-cli binary failed: {status}");

            let exe = std::env::current_exe().expect("current_exe");
            let profile_dir = exe
                .parent()
                .and_then(Path::parent)
                .expect("expected test binary under <target>/<profile>/deps/");
            let bin = profile_dir.join("libsignal-cli");
            assert!(bin.is_file(), "expected compiled CLI binary at {}", bin.display());
            bin
        })
        .as_path()
}

struct Workspace {
    root: PathBuf,
}

impl Workspace {
    fn new(label: &str) -> Self {
        let id = NEXT_WS_ID.fetch_add(1, Ordering::Relaxed);
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("target")
            .join("cli-pqxdh-roundtrip-tmp")
            .join(format!("{label}-{}-{id}", std::process::id()));
        if root.exists() {
            fs::remove_dir_all(&root).expect("clean stale workspace");
        }
        fs::create_dir_all(&root).expect("create workspace root");
        Self { root }
    }

    fn party_dir(&self, name: &str) -> PathBuf {
        let dir = self.root.join(name);
        create_party_skeleton(&dir);
        dir
    }

    fn bundle_dir(&self, name: &str) -> PathBuf {
        let dir = self.root.join(name);
        fs::create_dir_all(&dir).expect("create bundle dir");
        dir
    }
}

impl Drop for Workspace {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
}

const PARTY_SUBDIRS: &[&str] = &[
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

fn create_party_skeleton(dir: &Path) {
    fs::create_dir_all(dir).expect("create party dir");
    for sub in PARTY_SUBDIRS {
        fs::create_dir_all(dir.join(sub)).expect("create party subdir");
    }
}

fn clone_dir_recursive(src: &Path, dst: &Path) {
    if dst.exists() {
        fs::remove_dir_all(dst).expect("clean dst before clone");
    }
    fs::create_dir_all(dst).expect("mkdir dst");
    for entry in fs::read_dir(src).expect("read_dir") {
        let entry = entry.expect("dir entry");
        let ty = entry.file_type().expect("file_type");
        let dst_path = dst.join(entry.file_name());
        if ty.is_dir() {
            clone_dir_recursive(&entry.path(), &dst_path);
        } else {
            fs::copy(entry.path(), dst_path).expect("copy file");
        }
    }
}

/// Snapshot of all regular files under `dir` (excluding `coins`) for atomicity/determinism checks.
fn snapshot_store_files(dir: &Path) -> BTreeMap<String, Vec<u8>> {
    fn walk(base: &Path, cur: &Path, out: &mut BTreeMap<String, Vec<u8>>) {
        for entry in fs::read_dir(cur).expect("read_dir") {
            let entry = entry.expect("entry");
            let path = entry.path();
            let rel = path
                .strip_prefix(base)
                .unwrap()
                .to_string_lossy()
                .replace('\\', "/");
            if entry.file_type().unwrap().is_dir() {
                walk(base, &path, out);
            } else if rel != "coins" {
                out.insert(rel, fs::read(&path).expect("read file"));
            }
        }
    }
    let mut map = BTreeMap::new();
    walk(dir, dir, &mut map);
    map
}

// ---------------------------------------------------------------------------
// CLI invocation helpers
// ---------------------------------------------------------------------------

const ALICE_UUID: &str = "8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b";
const BOB_UUID: &str = "5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6";

const ALICE_ADDR: &str = "8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b.1";
const BOB_ADDR: &str = "5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6.1";
const EVE_ADDR: &str = "c0a7e5d1-2b3c-4d5e-8f60-718293a4b5c6.1";

struct CliResult {
    code: i32,
    stdout: Vec<u8>,
}

fn run_cli(party_dir: &Path, coins: &[u8], args: &[&str], stdin_bytes: &[u8]) -> CliResult {
    fs::write(party_dir.join("coins"), coins).expect("write coins");
    run_cli_keep_coins(party_dir, args, stdin_bytes)
}

fn run_cli_keep_coins(party_dir: &Path, args: &[&str], stdin_bytes: &[u8]) -> CliResult {
    let mut child = Command::new(cli_bin())
        .current_dir(party_dir)
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn libsignal-cli");
    if let Some(mut sin) = child.stdin.take() {
        sin.write_all(stdin_bytes).expect("write stdin");
    }
    let out = child.wait_with_output().expect("wait libsignal-cli");
    CliResult {
        code: out.status.code().unwrap_or(-1),
        stdout: out.stdout,
    }
}

fn cli_keygen(party_dir: &Path, addr: &str, n_opk: u32, coins: &CoinStream) {
    let n_str = n_opk.to_string();
    // Each keygen draws coins for identity, reg_id, spk + sig, lr_kyber + sig, and `n_opk` pairs.
    let tape = coins.bytes(512 + (n_opk as usize) * 256);
    let r = run_cli(party_dir, &tape, &["keygen", addr, &n_str], &[]);
    assert_eq!(r.code, 0, "keygen {addr} n={n_opk} failed with exit {}", r.code);
    assert!(r.stdout.is_empty());
}

/// Assembles a bundle directory from `peer_dir/public/` as Signal's server would serve to a client.
fn assemble_bundle(peer_dir: &Path, bundle_dir: &Path, with_opk: bool) {
    if bundle_dir.exists() {
        fs::remove_dir_all(bundle_dir).unwrap();
    }
    fs::create_dir_all(bundle_dir).unwrap();
    let pub_dir = peer_dir.join("public");
    fs::copy(pub_dir.join("identity-key"), bundle_dir.join("identity-key")).unwrap();
    fs::copy(pub_dir.join("registration-id"), bundle_dir.join("registration-id")).unwrap();
    fs::copy(
        pub_dir.join("signed-pre-keys").join("1"),
        bundle_dir.join("signed-pre-key"),
    )
    .unwrap();
    if with_opk {
        fs::copy(
            pub_dir.join("one-time-kyber-pre-keys").join("2"),
            bundle_dir.join("kyber-pre-key"),
        )
        .unwrap();
        fs::copy(
            pub_dir.join("one-time-pre-keys").join("1"),
            bundle_dir.join("one-time-pre-key"),
        )
        .unwrap();
    } else {
        fs::copy(
            pub_dir.join("last-resort-kyber-pre-keys").join("1"),
            bundle_dir.join("kyber-pre-key"),
        )
        .unwrap();
    }
}

fn cli_init(party_dir: &Path, peer_addr: &str, bundle_dir: &Path, coins: &[u8]) -> CliResult {
    let b = bundle_dir.to_str().expect("utf8 bundle path");
    run_cli(party_dir, coins, &["init", peer_addr, b], &[])
}

fn cli_send(party_dir: &Path, peer_addr: &str, ptext: &[u8], coins: &[u8]) -> CliResult {
    run_cli(party_dir, coins, &["send", peer_addr], ptext)
}

fn cli_recv(party_dir: &Path, peer_addr: &str, wire: &[u8], coins: &[u8]) -> CliResult {
    run_cli(party_dir, coins, &["recv", peer_addr], wire)
}

struct HandshakeFixture {
    ws: Workspace,
    alice_pre_init: PathBuf,
    alice_post_init: PathBuf,
    alice: PathBuf,
    bob_pre_recv: PathBuf,
    bob: PathBuf,
    bundle: PathBuf,
    wire1: Vec<u8>,
    coins: CoinStream,
}

fn setup_handshake(label: &str, seed: u64, with_opk: bool) -> HandshakeFixture {
    let ws = Workspace::new(label);
    let coins = CoinStream::new(seed);
    let alice = ws.party_dir("alice");
    let bob = ws.party_dir("bob");

    cli_keygen(&alice, ALICE_ADDR, 0, &coins);
    let n_bob = if with_opk { 2 } else { 0 };
    cli_keygen(&bob, BOB_ADDR, n_bob, &coins);

    let alice_pre_init = ws.root.join("alice_pre_init");
    clone_dir_recursive(&alice, &alice_pre_init);
    let bob_pre_recv = ws.root.join("bob_pre_recv");
    clone_dir_recursive(&bob, &bob_pre_recv);

    let bundle = ws.bundle_dir("bob_bundle");
    assemble_bundle(&bob, &bundle, with_opk);

    let r_init = cli_init(&alice, BOB_ADDR, &bundle, &coins.bytes(256));
    assert_eq!(r_init.code, 0, "Alice init failed");
    assert!(r_init.stdout.is_empty());

    // Verify Alice stored a valid SessionRecord and pinned Bob's identity key.
    let a0_bytes = fs::read(alice.join("sessions").join(BOB_ADDR)).expect("Alice session file");
    assert!(!a0_bytes.is_empty());
    SessionRecord::deserialize(&a0_bytes).expect("valid Alice SessionRecord after init");
    assert_eq!(
        fs::read(alice.join("identities").join(BOB_UUID)).unwrap(),
        fs::read(bob.join("public").join("identity-key")).unwrap()
    );

    let alice_post_init = ws.root.join("alice_post_init");
    clone_dir_recursive(&alice, &alice_post_init);

    let r_send = cli_send(&alice, BOB_ADDR, b"hello bob", &coins.bytes(256));
    assert_eq!(r_send.code, 0, "Alice first send failed");
    let wire1 = r_send.stdout;
    assert_eq!(wire1[0], 3, "first message must be PreKeySignalMessage (tag 3)");

    let r_recv = cli_recv(&bob, ALICE_ADDR, &wire1, &coins.bytes(256));
    assert_eq!(r_recv.code, 0, "Bob prekey recv failed");
    assert_eq!(r_recv.stdout, b"hello bob");

    let b1_bytes = fs::read(bob.join("sessions").join(ALICE_ADDR)).expect("Bob session file");
    SessionRecord::deserialize(&b1_bytes).expect("valid Bob SessionRecord after prekey recv");
    assert_eq!(
        fs::read(bob.join("identities").join(ALICE_UUID)).unwrap(),
        fs::read(alice.join("public").join("identity-key")).unwrap()
    );

    if with_opk {
        // Used one-time EC pre-key 1 and one-time Kyber pre-key 2 must be emptied; unused keys stay.
        assert!(
            fs::read(bob.join("one-time-pre-keys").join("1")).unwrap().is_empty(),
            "used one-time pre-key 1 must be emptied"
        );
        assert!(
            fs::read(bob.join("one-time-kyber-pre-keys").join("2")).unwrap().is_empty(),
            "used one-time Kyber pre-key 2 must be emptied"
        );
        assert!(!fs::read(bob.join("one-time-pre-keys").join("2")).unwrap().is_empty());
        assert!(!fs::read(bob.join("one-time-kyber-pre-keys").join("3")).unwrap().is_empty());
    } else {
        // Last-resort Kyber pre-key 1 stays intact and records `(spk_id:u32 || base_key[33])`.
        assert!(!fs::read(bob.join("last-resort-kyber-pre-keys").join("1")).unwrap().is_empty());
        let seen = fs::read(bob.join("last-resort-kyber-pre-keys").join("1.base-keys"))
            .expect("last-resort base-keys log");
        assert_eq!(seen.len(), 37, "spk_id (4B) + serialized Curve25519 base_key (33B)");
        assert_eq!(&seen[..4], &1u32.to_le_bytes());
        assert_eq!(seen[4], 0x05, "Curve25519 serialized key type byte");
    }

    HandshakeFixture {
        ws,
        alice_pre_init,
        alice_post_init,
        alice,
        bob_pre_recv,
        bob,
        bundle,
        wire1,
        coins,
    }
}

// ---------------------------------------------------------------------------
// Positive scenarios: PQXDH handshake, Double Ratchet, SPQR transitions, coins
// ---------------------------------------------------------------------------

fn run_conversation(label: &str, with_opk: bool) {
    let f = setup_handshake(label, if with_opk { 101 } else { 102 }, with_opk);

    // Bob replies with a Whisper SignalMessage (tag 2); Alice receives.
    let r = cli_send(&f.bob, ALICE_ADDR, b"hi alice", &f.coins.bytes(256));
    assert_eq!(r.code, 0);
    assert_eq!(r.stdout[0], 2, "Bob's reply must be SignalMessage (tag 2)");
    let r = cli_recv(&f.alice, BOB_ADDR, &r.stdout, &f.coins.bytes(256));
    assert_eq!(r.code, 0);
    assert_eq!(r.stdout, b"hi alice");

    // Alternating turns (DH ratchet steps + SPQR V1 incremental braid steps).
    for i in 0..6u8 {
        let msg_a = [b'A', i];
        let w_a = cli_send(&f.alice, BOB_ADDR, &msg_a, &f.coins.bytes(256));
        assert_eq!(w_a.code, 0);
        assert_eq!(w_a.stdout[0], 2, "after Bob's reply Alice sends SignalMessage (tag 2)");
        SignalMessage::try_from(&w_a.stdout[1..]).expect("valid SignalMessage wire bytes");

        let p_b = cli_recv(&f.bob, ALICE_ADDR, &w_a.stdout, &f.coins.bytes(256));
        assert_eq!(p_b.code, 0);
        assert_eq!(p_b.stdout, msg_a);

        let msg_b = [b'B', i];
        let w_b = cli_send(&f.bob, ALICE_ADDR, &msg_b, &f.coins.bytes(256));
        assert_eq!(w_b.code, 0);
        assert_eq!(w_b.stdout[0], 2);

        let p_a = cli_recv(&f.alice, BOB_ADDR, &w_b.stdout, &f.coins.bytes(256));
        assert_eq!(p_a.code, 0);
        assert_eq!(p_a.stdout, msg_b);
    }

    // Burst of 3 consecutive messages on one chain delivered out of order ([2, 0, 1]).
    let mut burst = Vec::new();
    for i in 0..3u8 {
        let w = cli_send(&f.alice, BOB_ADDR, &[b'x', i], &f.coins.bytes(256));
        assert_eq!(w.code, 0);
        assert_eq!(w.stdout[0], 2);
        burst.push(w.stdout);
    }
    for &idx in &[2usize, 0, 1] {
        let p = cli_recv(&f.bob, ALICE_ADDR, &burst[idx], &f.coins.bytes(256));
        assert_eq!(p.code, 0, "out-of-order whisper delivery {idx}");
        assert_eq!(p.stdout, [b'x', idx as u8]);
    }
}

#[test]
fn round_trip_with_one_time_prekey() {
    run_conversation("rt-opk", true);
}

#[test]
fn round_trip_without_one_time_prekey() {
    run_conversation("rt-no-opk", false);
}

/// Extracts protobuf field 5 (`pq_ratchet`, wire tag `0x2a`) from a `SignalMessage` body (excluding
/// the leading 1-byte version byte and trailing 8-byte MAC).
fn extract_signal_message_pq_ratchet(wire: &[u8]) -> Option<Vec<u8>> {
    assert_eq!(wire[0], 2, "expected SignalMessage wire tag 2");
    let sm = &wire[1..];
    assert!(sm.len() > 1 + 8, "SignalMessage must have version byte + protobuf + 8B MAC");
    let mut pb = &sm[1..sm.len() - 8];
    while !pb.is_empty() {
        let (tag, rest) = read_varint(pb)?;
        pb = rest;
        let field_num = tag >> 3;
        let wire_type = tag & 7;
        match wire_type {
            0 => {
                let (_, rest) = read_varint(pb)?;
                pb = rest;
            }
            2 => {
                let (len, rest) = read_varint(pb)?;
                let len = len as usize;
                assert!(rest.len() >= len);
                let val = &rest[..len];
                pb = &rest[len..];
                if field_num == 5 {
                    return Some(val.to_vec());
                }
            }
            _ => return None,
        }
    }
    None
}

fn read_varint(mut b: &[u8]) -> Option<(u64, &[u8])> {
    let mut acc = 0u64;
    let mut shift = 0u32;
    while let Some((&byte, rest)) = b.split_first() {
        b = rest;
        acc |= u64::from(byte & 0x7f) << shift;
        if byte & 0x80 == 0 {
            return Some((acc, b));
        }
        shift += 7;
        if shift >= 64 {
            return None;
        }
    }
    None
}

#[test]
fn spqr_multi_epoch_ratchet_transitions() {
    let f = setup_handshake("spqr-epochs", 202, true);
    let mut pq_lengths_b = Vec::new();
    let mut pq_lengths_a = Vec::new();

    // SPQR V1 slices ML-KEM-768 public keys (1184B) and ciphertexts (1088B) into small
    // erasure-coded chunks across consecutive messages:
    //   1. Bob's first reply sends a header-only SPQR frame while Alice starts streaming `ek`
    //      chunks;
    //   2. Sending 45 messages from Alice -> Bob delivers all `ek` chunks so Bob reconstructs `ek`
    //      and transitions to streaming `ct` chunks back to Alice;
    //   3. Sending 45 messages from Bob -> Alice delivers all `ct` chunks so Alice decapsulates and
    //      transitions into the next SPQR epoch.
    let wb0 = cli_send(&f.bob, ALICE_ADDR, b"b0", &f.coins.bytes(256));
    assert_eq!(wb0.code, 0);
    let pq_b0 = extract_signal_message_pq_ratchet(&wb0.stdout).expect("SPQR field 6 on wb0");
    assert!(!pq_b0.is_empty(), "SPQR V1 pq_ratchet payload must be non-empty");
    pq_lengths_b.push(pq_b0.len());
    let ra0 = cli_recv(&f.alice, BOB_ADDR, &wb0.stdout, &f.coins.bytes(256));
    assert_eq!(ra0.code, 0);
    assert_eq!(ra0.stdout, b"b0");

    // Phase 1: Alice streams 45 messages so Bob receives the full ML-KEM-768 `ek`.
    for i in 0..45u8 {
        let pt = [b'a', i];
        let wa = cli_send(&f.alice, BOB_ADDR, &pt, &f.coins.bytes(256));
        assert_eq!(wa.code, 0);
        let pq_a = extract_signal_message_pq_ratchet(&wa.stdout).expect("SPQR field 6 on wa");
        assert!(!pq_a.is_empty());
        pq_lengths_a.push(pq_a.len());

        let rb = cli_recv(&f.bob, ALICE_ADDR, &wa.stdout, &f.coins.bytes(256));
        assert_eq!(rb.code, 0);
        assert_eq!(rb.stdout, pt);
    }

    // Phase 2: Bob now streams 45 messages carrying the encapsulated ML-KEM-768 `ct` chunks back,
    // and Alice receives them to ratify the new post-quantum chain key and advance epochs.
    for i in 0..45u8 {
        let pt = [b'b', i];
        let wb = cli_send(&f.bob, ALICE_ADDR, &pt, &f.coins.bytes(256));
        assert_eq!(wb.code, 0);
        let pq_b = extract_signal_message_pq_ratchet(&wb.stdout).expect("SPQR field 6 on wb");
        assert!(!pq_b.is_empty());
        pq_lengths_b.push(pq_b.len());

        let ra = cli_recv(&f.alice, BOB_ADDR, &wb.stdout, &f.coins.bytes(256));
        assert_eq!(ra.code, 0);
        assert_eq!(ra.stdout, pt);
    }

    // Phase 3: Alice sends one more message in the new SPQR epoch and Bob decrypts it.
    let wa_next = cli_send(&f.alice, BOB_ADDR, b"next-epoch", &f.coins.bytes(256));
    assert_eq!(wa_next.code, 0);
    let pq_next = extract_signal_message_pq_ratchet(&wa_next.stdout).expect("SPQR field 6 next");
    assert!(!pq_next.is_empty());
    let rb_next = cli_recv(&f.bob, ALICE_ADDR, &wa_next.stdout, &f.coins.bytes(256));
    assert_eq!(rb_next.code, 0);
    assert_eq!(rb_next.stdout, b"next-epoch");

    // Bob's initial message before reconstructing Alice's `ek` has a short header-only SPQR frame,
    // whereas once Bob reconstructs `ek` in Phase 2 his messages carry larger `ct` chunks.
    let min_b = *pq_lengths_b.iter().min().unwrap();
    let max_b = *pq_lengths_b.iter().max().unwrap();
    let max_a = *pq_lengths_a.iter().max().unwrap();
    assert!(
        max_b > min_b && max_a > min_b,
        "expected SPQR V1 chunked transition from header-only ({min_b}B) to ML-KEM chunk frames (bob max {max_b}B, alice max {max_a}B)"
    );

    let a_rec = fs::read(f.alice.join("sessions").join(BOB_ADDR)).unwrap();
    let b_rec = fs::read(f.bob.join("sessions").join(ALICE_ADDR)).unwrap();
    SessionRecord::deserialize(&a_rec).expect("valid Alice SessionRecord after SPQR epochs");
    SessionRecord::deserialize(&b_rec).expect("valid Bob SessionRecord after SPQR epochs");
}

#[test]
fn alice_keeps_sending_prekey_messages_until_reply() {
    let f = setup_handshake("prekey-until-reply", 303, true);
    let r2 = cli_send(&f.alice, BOB_ADDR, b"again", &f.coins.bytes(256));
    assert_eq!(r2.code, 0);
    assert_eq!(r2.stdout[0], 3, "still PreKeySignalMessage before Bob replies");

    // Bob already consumed his one-time pre-keys on `wire1`, yet accepts `r2` in the existing session.
    let p2 = cli_recv(&f.bob, ALICE_ADDR, &r2.stdout, &f.coins.bytes(256));
    assert_eq!(p2.code, 0);
    assert_eq!(p2.stdout, b"again");
}

#[test]
fn deterministic_given_the_tape() {
    let f1 = setup_handshake("det-1", 404, true);
    let f2 = setup_handshake("det-2", 404, true);

    assert_eq!(f1.wire1, f2.wire1);
    assert_eq!(snapshot_store_files(&f1.alice), snapshot_store_files(&f2.alice));
    assert_eq!(snapshot_store_files(&f1.bob), snapshot_store_files(&f2.bob));
}

/// Finds the exact number of coin bytes consumed by an operation by testing prefixes of `full_tape`
/// (whose bytes are all non-zero, so replacing any consumed byte with `0` past EOF alters the draw).
fn exact_coins_consumed<F>(base_dir: &Path, scratch_root: &Path, tag: &str, full_tape: &[u8], op: F) -> usize
where
    F: Fn(&Path, &[u8]) -> Vec<u8>,
{
    let run_with_len = |len: usize, idx: usize| -> (BTreeMap<String, Vec<u8>>, Vec<u8>) {
        let dir = scratch_root.join(format!("{tag}-{len}-{idx}"));
        clone_dir_recursive(base_dir, &dir);
        let out = op(&dir, &full_tape[..len]);
        let snap = snapshot_store_files(&dir);
        let _ = fs::remove_dir_all(&dir);
        (snap, out)
    };

    let (ref_snap, ref_out) = run_with_len(full_tape.len(), 0);
    // Trailing bytes beyond `full_tape` must not affect output either.
    let mut extended = full_tape.to_vec();
    extended.extend_from_slice(&[0xaa; 64]);
    let dir_ext = scratch_root.join(format!("{tag}-ext"));
    clone_dir_recursive(base_dir, &dir_ext);
    let ext_out = op(&dir_ext, &extended);
    assert_eq!(
        (snapshot_store_files(&dir_ext), ext_out),
        (ref_snap.clone(), ref_out.clone()),
        "{tag}: trailing unused coin bytes must not affect result"
    );
    let _ = fs::remove_dir_all(&dir_ext);

    // Binary search for minimal prefix `lo` in `0..=full_tape.len()` matching `(ref_snap, ref_out)`.
    let mut lo = 0usize;
    let mut hi = full_tape.len();
    let mut probe_id = 1usize;
    while lo < hi {
        let mid = (lo + hi) / 2;
        let cand = run_with_len(mid, probe_id);
        probe_id += 1;
        if cand == (ref_snap.clone(), ref_out.clone()) {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }
    if lo > 0 {
        assert_ne!(
            run_with_len(lo - 1, probe_id),
            (ref_snap, ref_out),
            "{tag}: truncating coin byte {} should change output",
            lo - 1
        );
    }
    lo
}

#[test]
fn coin_draw_bounds_and_zero_padding() {
    let f = setup_handshake("coin-draws", 505, true);
    let tape = f.coins.nonzero_bytes(512);

    // 1. Alice `init`: draws ephemeral X25519 + Kyber1024 encaps + initial DH ratchet + SPQR seed.
    let init_used = exact_coins_consumed(&f.alice_pre_init, &f.ws.root, "init", &tape, |dir, c| {
        let r = cli_init(dir, BOB_ADDR, &f.bundle, c);
        assert_eq!(r.code, 0);
        r.stdout
    });
    assert!(init_used >= 96 && init_used < 512, "unexpected init coin usage: {init_used}");

    // 2. Bob `recv` of `wire1` (`decrypt_prekey`): generates Bob's initial sending ratchet key + SPQR seed.
    let pk_recv_used = exact_coins_consumed(&f.bob_pre_recv, &f.ws.root, "pk-recv", &tape, |dir, c| {
        let r = cli_recv(dir, ALICE_ADDR, &f.wire1, c);
        assert_eq!(r.code, 0);
        r.stdout
    });
    assert!(
        pk_recv_used >= 32 && pk_recv_used < 512,
        "Bob's prekey recv generates his initial ratchet key and must draw >= 32 coin bytes, got {pk_recv_used}"
    );

    // 3. Bob's first `send`: uses the sending chain already initialized during `pk-recv` (`0` DH coins).
    let bob_send1_used = exact_coins_consumed(&f.bob, &f.ws.root, "bob-send1", &tape, |dir, c| {
        let r = cli_send(dir, ALICE_ADDR, b"reply", c);
        assert_eq!(r.code, 0);
        r.stdout
    });
    assert_eq!(bob_send1_used, 0, "Bob's first send reuses his prekey-recv sending chain (0 coins)");

    // 4. Alice `recv` of Bob's reply: performs a DH ratchet step and generates a fresh sending key (>= 32B).
    let bob_reply = cli_send(&f.bob, ALICE_ADDR, b"reply", &f.coins.bytes(256));
    assert_eq!(bob_reply.code, 0);
    let alice_dh_recv_used =
        exact_coins_consumed(&f.alice, &f.ws.root, "alice-dh-recv", &tape, |dir, c| {
            let r = cli_recv(dir, BOB_ADDR, &bob_reply.stdout, c);
            assert_eq!(r.code, 0);
            r.stdout
        });
    assert!(
        alice_dh_recv_used >= 32 && alice_dh_recv_used < 512,
        "Alice's recv of Bob's reply performs a DH ratchet step and must draw >= 32 coin bytes, got {alice_dh_recv_used}"
    );

    // 5. Empty `coins` file zero-pads deterministically without error (`cli/src/coins.rs`).
    let zero_dir = f.ws.root.join("alice-zero-coins");
    clone_dir_recursive(&f.alice_pre_init, &zero_dir);
    let r_zero = cli_init(&zero_dir, BOB_ADDR, &f.bundle, &[]);
    assert_eq!(r_zero.code, 0, "empty coins must zero-extend cleanly");
}

// ---------------------------------------------------------------------------
// Negative scenarios & store-commit atomicity on rejection
// ---------------------------------------------------------------------------

#[test]
fn bad_signed_prekey_signature() {
    let f = setup_handshake("bad-spk-sig", 601, true);
    let bad_bundle = f.ws.bundle_dir("bad_spk_bundle");
    clone_dir_recursive(&f.bundle, &bad_bundle);
    let spk_path = bad_bundle.join("signed-pre-key");
    let mut spk = fs::read(&spk_path).unwrap();
    let sig_start = spk.len() - 64;
    spk[sig_start] ^= 1;
    fs::write(&spk_path, &spk).unwrap();

    let before = snapshot_store_files(&f.alice_pre_init);
    let r = cli_init(&f.alice_pre_init, BOB_ADDR, &bad_bundle, &f.coins.bytes(256));
    assert_eq!(r.code, 1);
    assert!(r.stdout.is_empty());
    assert_eq!(snapshot_store_files(&f.alice_pre_init), before, "rejected init must write no files");
}

#[test]
fn bad_kyber_prekey_signature() {
    let f = setup_handshake("bad-kpk-sig", 602, true);
    let bad_bundle = f.ws.bundle_dir("bad_kpk_bundle");
    clone_dir_recursive(&f.bundle, &bad_bundle);
    let kpk_path = bad_bundle.join("kyber-pre-key");
    let mut kpk = fs::read(&kpk_path).unwrap();
    let sig_start = kpk.len() - 64;
    kpk[sig_start] ^= 1;
    fs::write(&kpk_path, &kpk).unwrap();

    let before = snapshot_store_files(&f.alice_pre_init);
    let r = cli_init(&f.alice_pre_init, BOB_ADDR, &bad_bundle, &f.coins.bytes(256));
    assert_eq!(r.code, 1);
    assert!(r.stdout.is_empty());
    assert_eq!(snapshot_store_files(&f.alice_pre_init), before, "rejected init must write no files");
}

#[test]
fn malformed_inputs() {
    let f = setup_handshake("malformed", 603, true);

    // 1. CLI argument errors -> exit 2, stores untouched.
    let before_a = snapshot_store_files(&f.alice_pre_init);
    for bad_args in [
        &[][..],
        &["unknown", BOB_ADDR][..],
        &["send", "not-a-service-id-no-dot"][..],
        &["send", "not-a-uuid.1"][..],
        &["send", "5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6.0"][..],
        &["keygen", ALICE_ADDR, "101"][..],
    ] {
        let r = run_cli(&f.alice_pre_init, &[], bad_args, &[]);
        assert_eq!(r.code, 2, "expected exit 2 for args {bad_args:?}, got {}", r.code);
    }
    assert_eq!(snapshot_store_files(&f.alice_pre_init), before_a);

    // 2. Malformed bundle files -> exit 1, stores untouched.
    for (file, bad_bytes) in [
        ("registration-id", vec![1u8, 2, 3]),
        ("signed-pre-key", vec![0u8; 20]),
        ("kyber-pre-key", vec![0u8; 40]),
        ("one-time-pre-key", vec![1u8, 0, 0, 0, 0xff]),
        ("identity-key", vec![0x99u8; 33]),
    ] {
        let bdir = f.ws.bundle_dir(&format!("malformed-{file}"));
        clone_dir_recursive(&f.bundle, &bdir);
        fs::write(bdir.join(file), bad_bytes).unwrap();
        let r = cli_init(&f.alice_pre_init, BOB_ADDR, &bdir, &f.coins.bytes(256));
        assert_eq!(r.code, 1, "expected exit 1 on malformed bundle {file}");
        assert_eq!(snapshot_store_files(&f.alice_pre_init), before_a);
    }

    // 3. `send` without an established session -> exit 1.
    let r = cli_send(&f.alice_pre_init, BOB_ADDR, b"no session", &f.coins.bytes(256));
    assert_eq!(r.code, 1);
    assert_eq!(snapshot_store_files(&f.alice_pre_init), before_a);

    // 4. `recv` with empty wire, bad wire tag, or PreKeySignalMessage retagged as SignalMessage (2).
    let before_b = snapshot_store_files(&f.bob_pre_recv);
    assert_eq!(cli_recv(&f.bob_pre_recv, ALICE_ADDR, &[], &[]).code, 1);
    assert_eq!(cli_recv(&f.bob_pre_recv, ALICE_ADDR, &[99, 1, 2, 3], &[]).code, 1);
    let mut retagged = f.wire1.clone();
    retagged[0] = 2;
    assert_eq!(cli_recv(&f.bob_pre_recv, ALICE_ADDR, &retagged, &f.coins.bytes(256)).code, 1);
    assert_eq!(snapshot_store_files(&f.bob_pre_recv), before_b);
}

#[test]
fn wrong_prekey_ids() {
    let f = setup_handshake("wrong-ids", 604, true);

    // Remove each of the 3 pre-keys (`signed-pre-keys/1`, `one-time-kyber-pre-keys/2`,
    // `one-time-pre-keys/1`) one at a time on a fresh copy of Bob before receiving `wire1`.
    for missing_rel in [
        "signed-pre-keys/1",
        "one-time-kyber-pre-keys/2",
        "one-time-pre-keys/1",
    ] {
        let bob_copy = f.ws.root.join(format!("bob-missing-{}", missing_rel.replace('/', "_")));
        clone_dir_recursive(&f.bob_pre_recv, &bob_copy);
        fs::write(bob_copy.join(missing_rel), &[]).unwrap();
        let before = snapshot_store_files(&bob_copy);

        let r = cli_recv(&bob_copy, ALICE_ADDR, &f.wire1, &f.coins.bytes(256));
        assert_eq!(r.code, 1, "missing {missing_rel} must be rejected with exit 1");
        assert!(r.stdout.is_empty());
        assert_eq!(
            snapshot_store_files(&bob_copy),
            before,
            "failed recv on missing {missing_rel} must commit no store changes"
        );
    }
}

#[test]
fn wrong_responder_identity() {
    let f = setup_handshake("wrong-responder", 605, true);
    let eve = f.ws.party_dir("eve");
    cli_keygen(&eve, EVE_ADDR, 2, &f.coins);

    // Even if Eve holds Bob's pre-key records, `wire1` is bound to Bob's identity key and fails.
    for rel in [
        "signed-pre-keys/1",
        "one-time-kyber-pre-keys/2",
        "one-time-pre-keys/1",
    ] {
        fs::copy(f.bob_pre_recv.join(rel), eve.join(rel)).unwrap();
    }
    let before = snapshot_store_files(&eve);
    let r = cli_recv(&eve, ALICE_ADDR, &f.wire1, &f.coins.bytes(256));
    assert_eq!(r.code, 1);
    assert!(r.stdout.is_empty());
    assert_eq!(snapshot_store_files(&eve), before);
}

#[test]
fn tampered_ciphertext() {
    let f = setup_handshake("tampered", 606, true);
    let mut bad_pk = f.wire1.clone();
    let n = bad_pk.len();
    bad_pk[n - 1] ^= 1; // flip MAC byte

    let before_b = snapshot_store_files(&f.bob_pre_recv);
    let r = cli_recv(&f.bob_pre_recv, ALICE_ADDR, &bad_pk, &f.coins.bytes(256));
    assert_eq!(r.code, 1);
    assert_eq!(snapshot_store_files(&f.bob_pre_recv), before_b);

    // Also tamper with a post-handshake SignalMessage (tag 2).
    let w2 = cli_send(&f.bob, ALICE_ADDR, b"whisper", &f.coins.bytes(256));
    assert_eq!(w2.code, 0);
    let mut bad_w2 = w2.stdout;
    let m = bad_w2.len();
    bad_w2[m - 1] ^= 1;
    let before_a = snapshot_store_files(&f.alice);
    let r2 = cli_recv(&f.alice, BOB_ADDR, &bad_w2, &f.coins.bytes(256));
    assert_eq!(r2.code, 1);
    assert_eq!(snapshot_store_files(&f.alice), before_a);
}

#[test]
fn replayed_prekey_message_on_updated_record_is_rejected() {
    // Case A: one-time pre-keys consumed and session already established.
    let f_opk = setup_handshake("replay-pk-opk", 607, true);
    let before_opk = snapshot_store_files(&f_opk.bob);
    let r = cli_recv(&f_opk.bob, ALICE_ADDR, &f_opk.wire1, &f_opk.coins.bytes(256));
    assert_eq!(r.code, 1);
    assert_eq!(snapshot_store_files(&f_opk.bob), before_opk);

    // Case B: last-resort Kyber pre-key (`with_opk = false`): rejected both on duplicate session
    // AND via `1.base-keys` even if the session file is absent (checking buffered commit atomicity
    // so `identities/<alice>` is NOT written when `mark_kyber_pre_key_used` rejects!).
    let f_lr = setup_handshake("replay-pk-lr", 608, false);
    let before_lr = snapshot_store_files(&f_lr.bob);
    let r_dup = cli_recv(&f_lr.bob, ALICE_ADDR, &f_lr.wire1, &f_lr.coins.bytes(256));
    assert_eq!(r_dup.code, 1);
    assert_eq!(snapshot_store_files(&f_lr.bob), before_lr);

    let bob_no_sess = f_lr.ws.root.join("bob_lr_no_sess");
    clone_dir_recursive(&f_lr.bob, &bob_no_sess);
    fs::write(bob_no_sess.join("sessions").join(ALICE_ADDR), &[]).unwrap();
    fs::write(bob_no_sess.join("identities").join(ALICE_UUID), &[]).unwrap();
    let before_no_sess = snapshot_store_files(&bob_no_sess);
    let r_base_replay = cli_recv(&bob_no_sess, ALICE_ADDR, &f_lr.wire1, &f_lr.coins.bytes(256));
    assert_eq!(r_base_replay.code, 1, "reused base key on last-resort Kyber key must be rejected");
    assert_eq!(
        snapshot_store_files(&bob_no_sess),
        before_no_sess,
        "rejected base-key replay must not commit peer identity or session"
    );
}

#[test]
fn replayed_prekey_message_on_fresh_record_is_the_environments_job() {
    // Restoring Bob's pre-handshake directory snapshot removes pre-key consumption state, so a
    // fresh pre-handshake store accepts `wire1` again and empties the same one-time keys.
    let f = setup_handshake("replay-fresh-bob", 609, true);
    let r = cli_recv(&f.bob_pre_recv, ALICE_ADDR, &f.wire1, &f.coins.bytes(256));
    assert_eq!(r.code, 0);
    assert_eq!(r.stdout, b"hello bob");
    assert!(fs::read(f.bob_pre_recv.join("one-time-pre-keys").join("1")).unwrap().is_empty());
    assert!(fs::read(f.bob_pre_recv.join("one-time-kyber-pre-keys").join("2")).unwrap().is_empty());
}

#[test]
fn replayed_whisper_message_is_rejected() {
    let f = setup_handshake("replay-whisper", 610, true);
    let w = cli_send(&f.bob, ALICE_ADDR, b"once", &f.coins.bytes(256));
    assert_eq!(w.code, 0);

    let r1 = cli_recv(&f.alice, BOB_ADDR, &w.stdout, &f.coins.bytes(256));
    assert_eq!(r1.code, 0);
    assert_eq!(r1.stdout, b"once");

    let before = snapshot_store_files(&f.alice);
    let r2 = cli_recv(&f.alice, BOB_ADDR, &w.stdout, &f.coins.bytes(256));
    assert_eq!(r2.code, 1);
    assert_eq!(snapshot_store_files(&f.alice), before);
}

#[test]
fn stale_alice_record_has_no_session_for_bob() {
    let f = setup_handshake("stale-alice", 611, true);
    let w = cli_send(&f.bob, ALICE_ADDR, b"r", &f.coins.bytes(256));
    assert_eq!(w.code, 0);

    // Pre-init Alice has no session for Bob -> rejected with exit 1, nothing written.
    let before_pre = snapshot_store_files(&f.alice_pre_init);
    let r_pre = cli_recv(&f.alice_pre_init, BOB_ADDR, &w.stdout, &f.coins.bytes(256));
    assert_eq!(r_pre.code, 1);
    assert_eq!(snapshot_store_files(&f.alice_pre_init), before_pre);

    // Post-init Alice (`alice_post_init`, before `send 1`) holds the pending pre-key session ->
    // verify whether Bob's reply `w` (whose SPQR braid responds to `wire1`'s `spqr::send`) is
    // rejected or accepted cleanly without panic, whereas `f.alice` (after `send 1`) accepts `w`.
    let r_cur = cli_recv(&f.alice, BOB_ADDR, &w.stdout, &f.coins.bytes(256));
    assert_eq!(r_cur.code, 0);
    assert_eq!(r_cur.stdout, b"r");

    let r_post_init = cli_recv(&f.alice_post_init, BOB_ADDR, &w.stdout, &f.coins.bytes(256));
    assert!(
        r_post_init.code == 0 || r_post_init.code == 1,
        "post-init snapshot must either decrypt cleanly (0) or reject stale SPQR epoch cleanly (1), got {}",
        r_post_init.code
    );
    if r_post_init.code == 0 {
        assert_eq!(r_post_init.stdout, b"r");
    }
}

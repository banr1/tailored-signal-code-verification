// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! `session_store`: stateful pre-key session store CLI exercising file-backed protocol state.
//!
//! Exercises the full process, store, randomness, stream, and exit-code pattern for whole-binary
//! stateful protocol CLIs:
//! - `#![no_main]` with musl's `__libc_start_main` calling `extern "C" fn main(argc, argv)`.
//! - `BTreeMap<String, Vec<u8>>`-backed `Dir` & `Stores` holding all mutations in memory until
//!   `Stores::commit`, so any `Rejected` call exits `1` with every file untouched.
//! - Relative paths in pre-existing directories (`identities/`, `sessions/`, `signed-pre-keys/`,
//!   `one-time-pre-keys/`, `public/`, `public/signed-pre-keys/`, `public/one-time-pre-keys/`),
//!   using "empty a file (`0` bytes)" as the stand-in for deleting a used one-time pre-key.
//! - Deterministic `Coins(&[u8])` stream read from `"coins"` in order and zero-padded past EOF.
//! - `stdin` read ONLY on `send` and `recv` (`keygen` and `init` leave `stdin` unread); `stdout`
//!   explicitly flushed before returning from `main`.
//! - Exit codes: `0` (accepted), `1` (protocol/bundle/replay rejection; zero files written),
//!   `2` (invalid CLI args, missing `coins` when `--require-coins`, or I/O error during `commit`).

#![no_main]

#[path = "../common.rs"]
mod common;

use common::{BrkMmapAlloc, read_args};
use std::collections::BTreeMap;
use std::ffi::{c_char, c_int};
use std::io::{self, Read, Write};

#[global_allocator]
static ALLOC: BrkMmapAlloc = BrkMmapAlloc::new();

struct Rejected;

struct Coins<'a>(&'a [u8]);

impl Coins<'_> {
    fn fill_bytes(&mut self, out: &mut [u8]) {
        let take = out.len().min(self.0.len());
        let (now, rest) = self.0.split_at(take);
        out[..take].copy_from_slice(now);
        out[take..].fill(0);
        self.0 = rest;
    }

    fn next_u32(&mut self) -> u32 {
        let mut b = [0u8; 4];
        self.fill_bytes(&mut b);
        u32::from_le_bytes(b)
    }

    fn next_key32(&mut self) -> [u8; 32] {
        let mut b = [0u8; 32];
        self.fill_bytes(&mut b);
        b
    }
}

/// Deterministic keyed hash/tag helper (Sip-style ARX sponge, self-contained in std).
fn keyed_tag16(key: &[u8; 32], domain: &[u8], body: &[u8]) -> [u8; 16] {
    let mut s0 = u64::from_le_bytes(key[0..8].try_into().unwrap()) ^ 0x736f6d6570736575;
    let mut s1 = u64::from_le_bytes(key[8..16].try_into().unwrap()) ^ 0x646f72616e646f6d;
    let mut s2 = u64::from_le_bytes(key[16..24].try_into().unwrap()) ^ 0x6c7967656e657261;
    let mut s3 = u64::from_le_bytes(key[24..32].try_into().unwrap()) ^ 0x7465646279746573;

    let mut mix = |byte: u8| {
        s3 ^= byte as u64;
        for _ in 0..2 {
            s0 = s0.wrapping_add(s1);
            s1 = s1.rotate_left(13) ^ s0;
            s0 = s0.rotate_left(32);
            s2 = s2.wrapping_add(s3);
            s3 = s3.rotate_left(16) ^ s2;
            s0 = s0.wrapping_add(s3);
            s3 = s3.rotate_left(21) ^ s0;
            s2 = s2.wrapping_add(s1);
            s1 = s1.rotate_left(17) ^ s2;
            s2 = s2.rotate_left(32);
        }
        s0 ^= byte as u64;
    };

    mix(domain.len() as u8);
    for &b in domain {
        mix(b);
    }
    mix(0xff);
    for &b in body {
        mix(b);
    }
    mix(0xee);
    let mut out = [0u8; 16];
    out[0..8].copy_from_slice(&(s0 ^ s2).to_le_bytes());
    out[8..16].copy_from_slice(&(s1 ^ s3).to_le_bytes());
    out
}

fn derive_pub(secret: &[u8; 32]) -> [u8; 32] {
    let mut pub_k = [0u8; 32];
    pub_k[0..16].copy_from_slice(&keyed_tag16(secret, b"pub-lo", &[]));
    pub_k[16..32].copy_from_slice(&keyed_tag16(secret, b"pub-hi", &[]));
    pub_k
}

fn sign_with_id(id_pub: &[u8; 32], msg: &[u8]) -> [u8; 16] {
    keyed_tag16(id_pub, b"bundle-sig", msg)
}

fn stream_xor(shared: &[u8; 32], counter: u32, data: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(data.len());
    for (chunk_idx, chunk) in data.chunks(16).enumerate() {
        let mut nonce = [0u8; 8];
        nonce[0..4].copy_from_slice(&counter.to_le_bytes());
        nonce[4..8].copy_from_slice(&(chunk_idx as u32).to_le_bytes());
        let pad = keyed_tag16(shared, b"stream", &nonce);
        for (i, &b) in chunk.iter().enumerate() {
            out.push(b ^ pad[i]);
        }
    }
    out
}

/// Read `path` if present; treat `ENOENT` as empty (`Vec::new()`), matching `stores::read_file`.
fn read_optional_file(path: &str) -> io::Result<Vec<u8>> {
    match std::fs::read(path) {
        Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(Vec::new()),
        other => other,
    }
}

fn read_required_file(path: &str) -> io::Result<Vec<u8>> {
    std::fs::read(path)
}

fn write_file_trunc(path: &str, bytes: &[u8]) -> io::Result<()> {
    std::fs::write(path, bytes)
}

struct Dir {
    path: &'static str,
    changed: BTreeMap<String, Vec<u8>>,
}

impl Dir {
    fn new(path: &'static str) -> Self {
        Self {
            path,
            changed: BTreeMap::new(),
        }
    }

    fn path_of(&self, name: &str) -> String {
        if self.path.is_empty() {
            name.to_owned()
        } else {
            format!("{}/{name}", self.path)
        }
    }

    fn get(&self, name: &str) -> Result<Vec<u8>, Rejected> {
        match self.changed.get(name) {
            Some(bs) => Ok(bs.clone()),
            None => read_optional_file(&self.path_of(name)).map_err(|_| Rejected),
        }
    }

    fn put(&mut self, name: impl Into<String>, bytes: Vec<u8>) {
        self.changed.insert(name.into(), bytes);
    }

    fn commit(self) -> io::Result<()> {
        for (name, bytes) in &self.changed {
            write_file_trunc(&self.path_of(name), bytes)?;
        }
        Ok(())
    }
}

struct Stores {
    own: Dir,
    identities: Dir,
    signed: Dir,
    one_time: Dir,
    sessions: Dir,
    public: Dir,
}

impl Stores {
    fn open() -> Self {
        Self {
            own: Dir::new(""),
            identities: Dir::new("identities"),
            signed: Dir::new("signed-pre-keys"),
            one_time: Dir::new("one-time-pre-keys"),
            sessions: Dir::new("sessions"),
            public: Dir::new("public"),
        }
    }

    fn commit(self) -> io::Result<()> {
        for dir in [
            self.own,
            self.identities,
            self.signed,
            self.one_time,
            self.sessions,
            self.public,
        ] {
            dir.commit()?;
        }
        Ok(())
    }
}

fn parse_address(s: &str) -> Option<(&str, u32)> {
    let (svc, dev) = s.rsplit_once('.')?;
    if svc.is_empty() || svc.contains('/') {
        return None;
    }
    let dev_id: u32 = dev.parse().ok()?;
    if dev_id == 0 {
        return None;
    }
    Some((svc, dev_id))
}

enum Call<'a> {
    Keygen { me: &'a str, n: u32 },
    Init { peer: &'a str, bundle: &'a str },
    Send { peer: &'a str },
    Recv { peer: &'a str },
}

#[unsafe(no_mangle)]
extern "C" fn main(argc: c_int, argv: *const *const c_char) -> c_int {
    let raw_args = unsafe { read_args(argc, argv) };
    let Ok(str_args) = raw_args
        .iter()
        .skip(1)
        .map(|s| core::str::from_utf8(s))
        .collect::<Result<Vec<&str>, _>>()
    else {
        return 2;
    };

    let mut coins_path = "coins";
    let mut filtered: Vec<&str> = Vec::new();
    let mut idx = 0;
    while idx < str_args.len() {
        if str_args[idx] == "--coins" {
            let Some(p) = str_args.get(idx + 1) else {
                return 2;
            };
            coins_path = p;
            idx += 2;
        } else {
            filtered.push(str_args[idx]);
            idx += 1;
        }
    }

    let call = match filtered.as_slice() {
        ["keygen", me, n_str] => {
            if parse_address(me).is_none() {
                return 2;
            }
            let Ok(n) = n_str.parse::<u32>() else {
                return 2;
            };
            if n > 100 {
                return 2;
            }
            Call::Keygen { me, n }
        }
        ["init", peer, bundle] => {
            if parse_address(peer).is_none() || bundle.is_empty() {
                return 2;
            }
            Call::Init { peer, bundle }
        }
        ["send", peer] => {
            if parse_address(peer).is_none() {
                return 2;
            }
            Call::Send { peer }
        }
        ["recv", peer] => {
            if parse_address(peer).is_none() {
                return 2;
            }
            Call::Recv { peer }
        }
        _ => return 2,
    };

    let input = match call {
        Call::Send { .. } | Call::Recv { .. } => {
            let mut v = Vec::new();
            if io::stdin().read_to_end(&mut v).is_err() {
                return 2;
            }
            v
        }
        Call::Keygen { .. } | Call::Init { .. } => Vec::new(),
    };

    let Ok(coins_bytes) = read_required_file(coins_path) else {
        return 2;
    };

    let Ok((stores, output)) = run(call, Stores::open(), &coins_bytes, &input) else {
        return 1;
    };

    if stores.commit().is_err() {
        return 2;
    }
    let mut stdout = io::stdout();
    if stdout.write_all(&output).and_then(|()| stdout.flush()).is_err() {
        return 2;
    }
    0
}

fn run(
    call: Call<'_>,
    mut s: Stores,
    coins_raw: &[u8],
    input: &[u8],
) -> Result<(Stores, Vec<u8>), Rejected> {
    let mut coins = Coins(coins_raw);
    match call {
        Call::Keygen { me, n } => {
            let id_sec = coins.next_key32();
            let id_pub = derive_pub(&id_sec);
            let reg_id = coins.next_u32();
            let mut keypair = Vec::with_capacity(64);
            keypair.extend_from_slice(&id_sec);
            keypair.extend_from_slice(&id_pub);

            s.own.put("address", me.as_bytes().to_vec());
            s.own.put("identity-key-pair", keypair);
            s.own.put("registration-id", reg_id.to_le_bytes().to_vec());
            s.public.put("identity-key", id_pub.to_vec());
            s.public
                .put("registration-id", reg_id.to_le_bytes().to_vec());

            let spk_sec = coins.next_key32();
            let spk_pub = derive_pub(&spk_sec);
            let mut spk_rec = Vec::with_capacity(68);
            spk_rec.extend_from_slice(&1u32.to_le_bytes());
            spk_rec.extend_from_slice(&spk_sec);
            spk_rec.extend_from_slice(&spk_pub);
            s.signed.put("1", spk_rec);

            let sig = sign_with_id(&id_pub, &spk_pub);
            let mut spk_pub_file = Vec::with_capacity(52);
            spk_pub_file.extend_from_slice(&1u32.to_le_bytes());
            spk_pub_file.extend_from_slice(&spk_pub);
            spk_pub_file.extend_from_slice(&sig);
            s.public.put("signed-pre-keys/1", spk_pub_file);

            for id in 1..=n {
                let opk_sec = coins.next_key32();
                let opk_pub = derive_pub(&opk_sec);
                let mut rec = Vec::with_capacity(68);
                rec.extend_from_slice(&id.to_le_bytes());
                rec.extend_from_slice(&opk_sec);
                rec.extend_from_slice(&opk_pub);
                s.one_time.put(id.to_string(), rec);

                let mut pub_file = Vec::with_capacity(36);
                pub_file.extend_from_slice(&id.to_le_bytes());
                pub_file.extend_from_slice(&opk_pub);
                s.public.put(format!("one-time-pre-keys/{id}"), pub_file);
            }
            Ok((s, Vec::new()))
        }
        Call::Init { peer, bundle } => {
            let my_addr = s.own.get("address")?;
            if my_addr.is_empty() {
                return Err(Rejected);
            }
            let kp = s.own.get("identity-key-pair")?;
            if kp.len() != 64 {
                return Err(Rejected);
            }
            let read_b = |name: &str| {
                read_required_file(&format!("{bundle}/{name}")).map_err(|_| Rejected)
            };
            let peer_id_pub: [u8; 32] = read_b("identity-key")?
                .try_into()
                .map_err(|_| Rejected)?;
            let reg_bytes: [u8; 4] = read_b("registration-id")?
                .try_into()
                .map_err(|_| Rejected)?;
            let _peer_reg = u32::from_le_bytes(reg_bytes);
            let spk_file = read_b("signed-pre-key")?;
            if spk_file.len() != 52 {
                return Err(Rejected);
            }
            let spk_pub = &spk_file[4..36];
            let spk_sig = &spk_file[36..52];
            if sign_with_id(&peer_id_pub, spk_pub) != spk_sig {
                // Stage a tentative identity change FIRST to verify that returning `Err(Rejected)`
                // drops all staged mutations without writing a single byte to disk!
                let (peer_svc, _) = parse_address(peer).ok_or(Rejected)?;
                s.identities.put(peer_svc, peer_id_pub.to_vec());
                return Err(Rejected);
            }
            let opk_file = read_optional_file(&format!("{bundle}/one-time-pre-key"))
                .map_err(|_| Rejected)?;
            let (opk_id, opk_pub): (u32, [u8; 32]) = if opk_file.is_empty() {
                (0, [0u8; 32])
            } else {
                if opk_file.len() != 36 {
                    return Err(Rejected);
                }
                let id = u32::from_le_bytes(opk_file[0..4].try_into().unwrap());
                let pk: [u8; 32] = opk_file[4..36].try_into().unwrap();
                (id, pk)
            };

            let (peer_svc, _) = parse_address(peer).ok_or(Rejected)?;
            if let Some(known) = s
                .identities
                .get(peer_svc)
                .ok()
                .filter(|b| !b.is_empty())
                && known.as_slice() != peer_id_pub
            {
                return Err(Rejected);
            }
            s.identities.put(peer_svc, peer_id_pub.to_vec());

            let _ephemeral = coins.next_key32();
            // Session layout (73 B):
            // [pending_prekey:u8][opk_id:u32][tx_cnt:u32][rx_cnt:u32][peer_id_pub:32][opk_pub:32-xor-shared]
            let mut shared = [0u8; 32];
            for i in 0..32 {
                shared[i] = peer_id_pub[i] ^ spk_pub[i] ^ opk_pub[i];
            }
            let mut sess = Vec::with_capacity(73);
            sess.push(1u8);
            sess.extend_from_slice(&opk_id.to_le_bytes());
            sess.extend_from_slice(&0u32.to_le_bytes());
            sess.extend_from_slice(&0u32.to_le_bytes());
            sess.extend_from_slice(&my_addr[..my_addr.len().min(32)]);
            sess.resize(45, 0);
            let mut full = Vec::with_capacity(77);
            full.extend_from_slice(&sess[..13]);
            full.extend_from_slice(&peer_id_pub);
            full.extend_from_slice(&shared);
            s.sessions.put(peer, full);
            Ok((s, Vec::new()))
        }
        Call::Send { peer } => {
            let my_addr = s.own.get("address")?;
            let kp = s.own.get("identity-key-pair")?;
            if my_addr.is_empty() || kp.len() != 64 {
                return Err(Rejected);
            }
            let my_id_pub: [u8; 32] = kp[32..64].try_into().unwrap();
            let mut sess = s.sessions.get(peer)?;
            if sess.len() != 77 {
                return Err(Rejected);
            }
            let _nonce_pad = coins.next_u32();
            let is_prekey = sess[0] == 1;
            let opk_id = u32::from_le_bytes(sess[1..5].try_into().unwrap());
            let tx_cnt = u32::from_le_bytes(sess[5..9].try_into().unwrap());
            let shared: [u8; 32] = sess[45..77].try_into().unwrap();

            let msg_type: u8 = if is_prekey { 3 } else { 2 };
            let ct = stream_xor(&shared, tx_cnt, input);
            // Wire format: [msg_type:u8][opk_id:u32][cnt:u32][sender_pub:32][ct...][mac:16]
            let mut wire = Vec::with_capacity(1 + 4 + 4 + 32 + ct.len() + 16);
            wire.push(msg_type);
            wire.extend_from_slice(&opk_id.to_le_bytes());
            wire.extend_from_slice(&tx_cnt.to_le_bytes());
            wire.extend_from_slice(&my_id_pub);
            wire.extend_from_slice(&ct);

            let mut bind = Vec::with_capacity(my_addr.len() + 1 + peer.len() + wire.len());
            bind.extend_from_slice(&my_addr);
            bind.push(b'>');
            bind.extend_from_slice(peer.as_bytes());
            bind.extend_from_slice(&wire);
            let mac = keyed_tag16(&shared, b"wire-mac", &bind);
            wire.extend_from_slice(&mac);

            sess[0] = 0;
            sess[5..9].copy_from_slice(&(tx_cnt + 1).to_le_bytes());
            s.sessions.put(peer, sess);
            Ok((s, wire))
        }
        Call::Recv { peer } => {
            let my_addr = s.own.get("address")?;
            let kp = s.own.get("identity-key-pair")?;
            if my_addr.is_empty() || kp.len() != 64 {
                return Err(Rejected);
            }
            let my_id_pub: [u8; 32] = kp[32..64].try_into().unwrap();
            let _nonce_pad = coins.next_u32();
            if input.len() < 1 + 4 + 4 + 32 + 16 {
                return Err(Rejected);
            }
            let msg_type = input[0];
            let opk_id = u32::from_le_bytes(input[1..5].try_into().unwrap());
            let cnt = u32::from_le_bytes(input[5..9].try_into().unwrap());
            let sender_pub: [u8; 32] = input[9..41].try_into().unwrap();
            let (header_and_ct, got_mac) = input.split_at(input.len() - 16);

            let mut sess = match msg_type {
                3 => {
                    let spk_rec = s.signed.get("1")?;
                    if spk_rec.len() != 68 {
                        return Err(Rejected);
                    }
                    let spk_pub = &spk_rec[36..68];
                    let opk_pub: [u8; 32] = if opk_id == 0 {
                        [0u8; 32]
                    } else {
                        let opk_rec = s.one_time.get(&opk_id.to_string())?;
                        // Emptied file (`len == 0`) means the one-time pre-key was already consumed!
                        if opk_rec.len() != 68 {
                            return Err(Rejected);
                        }
                        let pk: [u8; 32] = opk_rec[36..68].try_into().unwrap();
                        // Empty the one-time pre-key file instead of `unlink`!
                        s.one_time.put(opk_id.to_string(), Vec::new());
                        pk
                    };
                    let (peer_svc, _) = parse_address(peer).ok_or(Rejected)?;
                    if let Some(known) = s
                        .identities
                        .get(peer_svc)
                        .ok()
                        .filter(|b| !b.is_empty())
                        && known.as_slice() != sender_pub
                    {
                        return Err(Rejected);
                    }
                    s.identities.put(peer_svc, sender_pub.to_vec());
                    let mut shared = [0u8; 32];
                    for i in 0..32 {
                        shared[i] = my_id_pub[i] ^ spk_pub[i] ^ opk_pub[i];
                    }
                    let mut created = Vec::with_capacity(77);
                    created.push(0u8);
                    created.extend_from_slice(&0u32.to_le_bytes());
                    created.extend_from_slice(&0u32.to_le_bytes());
                    created.extend_from_slice(&0u32.to_le_bytes());
                    created.extend_from_slice(&sender_pub);
                    created.extend_from_slice(&shared);
                    created
                }
                2 => {
                    let existing = s.sessions.get(peer)?;
                    if existing.len() != 77 {
                        return Err(Rejected);
                    }
                    existing
                }
                _ => return Err(Rejected),
            };

            let rx_cnt = u32::from_le_bytes(sess[9..13].try_into().unwrap());
            if cnt != rx_cnt {
                return Err(Rejected);
            }
            let shared: [u8; 32] = sess[45..77].try_into().unwrap();
            let mut bind = Vec::with_capacity(peer.len() + 1 + my_addr.len() + header_and_ct.len());
            bind.extend_from_slice(peer.as_bytes());
            bind.push(b'>');
            bind.extend_from_slice(&my_addr);
            bind.extend_from_slice(header_and_ct);
            let want_mac = keyed_tag16(&shared, b"wire-mac", &bind);
            if want_mac != got_mac {
                return Err(Rejected);
            }
            let pt = stream_xor(&shared, cnt, &header_and_ct[41..]);
            sess[9..13].copy_from_slice(&(rx_cnt + 1).to_le_bytes());
            s.sessions.put(peer, sess);
            Ok((s, pt))
        }
    }
}

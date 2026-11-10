// Copyright 2026 Google LLC; SPDX-License-Identifier: Apache-2.0, except `SignalMessage`, which is
// prost-build's output for libsignal v0.105.4's `rust/protocol/src/proto/wire.proto` and remains
// Copyright 2020 Signal Messenger, LLC.; SPDX-License-Identifier: AGPL-3.0-only.
// See `third_party/libsignal/README.md`.

//! Differential-fuzz vectors for the trusted Lean codec `protoSignalCodec`
//! (`LibsignalBinary/Specifications/LibsignalSignalMessage.lean`). Untrusted tooling.
//!
//! Runs the REAL prost 0.14.4 `Message::decode` / `Message::encode` on a `SignalMessage` declared
//! exactly as prost-build generated it for libsignal v0.105.4
//! (`target/.../build/libsignal-protocol-*/out/signal.proto.wire.rs:2-16`), and writes one vector
//! per line (deterministic: fixed seed, no hash maps, no time):
//!
//! ```text
//! # comment
//! D <input hex or '-' for empty> <result>       decode vector
//! E <field1> ... <field6> <encoding hex or '-'> encode vector
//! ```
//!
//! A decode `<result>` is `ERR` or `OK <f1> <f2> <f3> <f4> <f5> <f6>`; a field is `-` for `None`,
//! `x<hex>` (`x` alone = empty) for a bytes field, or a decimal for a `uint32` field. For every
//! `E` vector prost's own `decode` of the encoding gives back the message (asserted here), so the
//! Lean test checks both `encode m = bytes` and `decode bytes = some m` on it.
//!
//! `decode` is wrapped in `catch_unwind`: a panic would be reported as `PANIC` and abort the run
//! (prost must never panic on any input).

use prost::Message;

#[derive(Clone, PartialEq, Eq, Hash, prost::Message)]
pub struct SignalMessage {
    #[prost(bytes = "vec", optional, tag = "1")]
    pub ratchet_key: ::core::option::Option<::prost::alloc::vec::Vec<u8>>,
    #[prost(uint32, optional, tag = "2")]
    pub counter: ::core::option::Option<u32>,
    #[prost(uint32, optional, tag = "3")]
    pub previous_counter: ::core::option::Option<u32>,
    #[prost(bytes = "vec", optional, tag = "4")]
    pub ciphertext: ::core::option::Option<::prost::alloc::vec::Vec<u8>>,
    #[prost(bytes = "vec", optional, tag = "5")]
    pub pq_ratchet: ::core::option::Option<::prost::alloc::vec::Vec<u8>>,
    #[prost(bytes = "vec", optional, tag = "6")]
    pub addresses: ::core::option::Option<::prost::alloc::vec::Vec<u8>>,
}

/// splitmix64 (deterministic, dependency-free).
struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E3779B97F4A7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
        z ^ (z >> 31)
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
    fn chance(&mut self, num: u64, den: u64) -> bool {
        self.below(den) < num
    }
    fn byte(&mut self) -> u8 {
        self.next() as u8
    }
    fn bytes(&mut self, n: usize) -> Vec<u8> {
        (0..n).map(|_| self.byte()).collect()
    }
    fn pick<T: Copy>(&mut self, xs: &[T]) -> T {
        xs[self.below(xs.len() as u64) as usize]
    }
}

fn hex(b: &[u8]) -> String {
    if b.is_empty() {
        return "-".into();
    }
    b.iter().map(|x| format!("{x:02x}")).collect()
}

fn fbytes(f: &Option<Vec<u8>>) -> String {
    match f {
        None => "-".into(),
        Some(v) => format!("x{}", v.iter().map(|x| format!("{x:02x}")).collect::<String>()),
    }
}

fn fu32(f: &Option<u32>) -> String {
    match f {
        None => "-".into(),
        Some(v) => v.to_string(),
    }
}

fn fields(m: &SignalMessage) -> String {
    format!(
        "{} {} {} {} {} {}",
        fbytes(&m.ratchet_key),
        fu32(&m.counter),
        fu32(&m.previous_counter),
        fbytes(&m.ciphertext),
        fbytes(&m.pq_ratchet),
        fbytes(&m.addresses)
    )
}

struct Out {
    lines: Vec<String>,
    n_dec: usize,
    n_ok: usize,
    n_enc: usize,
}

impl Out {
    fn comment(&mut self, c: &str) {
        self.lines.push(format!("# {c}"));
    }
    fn dec(&mut self, input: &[u8]) {
        let inp = input.to_vec();
        let r = std::panic::catch_unwind(move || SignalMessage::decode(&inp[..]));
        let res = match r {
            Err(_) => panic!("prost PANICKED on input {}", hex(input)),
            Ok(Err(_)) => "ERR".to_string(),
            Ok(Ok(m)) => {
                self.n_ok += 1;
                format!("OK {}", fields(&m))
            }
        };
        self.n_dec += 1;
        self.lines.push(format!("D {} {}", hex(input), res));
    }
    fn enc(&mut self, m: &SignalMessage) {
        let mut buf = Vec::new();
        m.encode(&mut buf).expect("can always append to a Vec");
        assert_eq!(buf, m.encode_to_vec());
        assert_eq!(buf.len(), m.encoded_len());
        self.n_enc += 1;
        let back = SignalMessage::decode(&buf[..]).expect("prost decodes its own encoding");
        assert!(back == *m, "prost round trip");
        self.lines.push(format!("E {} {}", fields(m), hex(&buf)));
    }
}

// ---------- wire building blocks ----------

fn varint(mut v: u64) -> Vec<u8> {
    let mut out = Vec::new();
    loop {
        if v < 0x80 {
            out.push(v as u8);
            return out;
        }
        out.push(((v & 0x7f) | 0x80) as u8);
        v >>= 7;
    }
}

/// A non-minimal varint of exactly `len` bytes (1..=10) for `v` (which must fit).
fn varint_padded(v: u64, len: usize) -> Vec<u8> {
    let mut out = Vec::new();
    let mut x = v;
    for i in 0..len {
        let b = (x & 0x7f) as u8;
        x >>= 7;
        if i + 1 == len {
            out.push(b);
        } else {
            out.push(b | 0x80);
        }
    }
    out
}

fn key(tag: u64, wt: u64) -> Vec<u8> {
    varint((tag << 3) | wt)
}

fn cat(parts: &[&[u8]]) -> Vec<u8> {
    parts.concat()
}

const BOUNDARY_U64: &[u64] = &[
    0,
    1,
    0x7f,
    0x80,
    0x3fff,
    0x4000,
    0xffff_ffff,
    0x1_0000_0000,
    0x1_0000_0001,
    0x7fff_ffff_ffff_ffff,
    0x8000_0000_0000_0000,
    u64::MAX,
];

fn rand_varint_value(r: &mut Rng) -> u64 {
    match r.below(4) {
        0 => r.pick(BOUNDARY_U64),
        1 => r.below(300),
        2 => r.next() >> r.below(64),
        _ => r.next() & 0xffff_ffff,
    }
}

fn varint_len(v: u64) -> usize {
    varint(v).len()
}

/// A (possibly non-minimal) encoding of `v`.
fn rand_varint(r: &mut Rng, v: u64) -> Vec<u8> {
    let min = varint_len(v);
    if min < 10 && r.chance(1, 5) {
        let len = min + 1 + r.below((10 - min) as u64) as usize;
        varint_padded(v, len)
    } else {
        varint(v)
    }
}

/// A random field / garbage token. `depth` = current group nesting (for group tokens).
fn rand_token(r: &mut Rng, depth: u32) -> Vec<u8> {
    let known = r.chance(2, 3);
    let tag: u64 = if known {
        1 + r.below(6)
    } else {
        r.pick(&[7, 8, 15, 16, 100, 2047, 2048, (1 << 29) - 1, 0x1fff_ffff])
    };
    let natural_wt = match tag {
        2 | 3 => 0,
        1 | 4 | 5 | 6 => 2,
        _ => r.pick(&[0, 1, 2, 3, 5]),
    };
    let wt = if r.chance(1, 8) { r.below(8) } else { natural_wt };
    let mut out = if r.chance(1, 10) {
        // non-minimal key
        let k = (tag << 3) | wt;
        let min = varint_len(k);
        varint_padded(k, (min + 1 + r.below((10 - min) as u64) as usize).min(10))
    } else {
        key(tag, wt)
    };
    match wt {
        0 => {
            let v = rand_varint_value(r);
            out.extend(rand_varint(r, v));
        }
        1 => out.extend(r.bytes(8)),
        5 => out.extend(r.bytes(4)),
        2 => {
            let n = r.pick(&[0usize, 1, 2, 3, 5, 8, 16, 32, 33, 34]);
            let declared = if r.chance(1, 12) { n as u64 + 1 + r.below(3) } else { n as u64 };
            out.extend(rand_varint(r, declared));
            out.extend(r.bytes(n));
        }
        3 => {
            if depth < 4 {
                let k = r.below(3);
                for _ in 0..k {
                    out.extend(rand_token(r, depth + 1));
                }
            }
            let end_tag = if r.chance(1, 8) { tag + 1 } else { tag };
            if !r.chance(1, 10) {
                out.extend(key(end_tag, 4));
            }
        }
        _ => {} // 4 (EndGroup), 6, 7: no payload
    }
    out
}

fn mutate(r: &mut Rng, mut v: Vec<u8>) -> Vec<u8> {
    let k = 1 + r.below(3);
    for _ in 0..k {
        match r.below(5) {
            0 if !v.is_empty() => {
                let n = r.below(v.len() as u64) as usize;
                v.truncate(n);
            }
            1 if !v.is_empty() => {
                let i = r.below(v.len() as u64) as usize;
                v[i] ^= 1 << r.below(8);
            }
            2 => {
                let i = r.below(v.len() as u64 + 1) as usize;
                let b = r.byte();
                v.insert(i, b);
            }
            3 if !v.is_empty() => {
                let i = r.below(v.len() as u64) as usize;
                v.remove(i);
            }
            _ if !v.is_empty() => {
                let i = r.below(v.len() as u64) as usize;
                v[i] = r.pick(&[0x00, 0x7f, 0x80, 0xff, 0x01, 0x02]);
            }
            _ => {}
        }
    }
    v
}

fn rand_msg(r: &mut Rng) -> SignalMessage {
    // Mostly short fields (file size); the length-varint boundary 127 / 128 in 1 of 10.
    let lens: &[usize] = &[0, 1, 2, 5, 16, 31, 32, 33];
    let bf = |r: &mut Rng, p: u64| -> Option<Vec<u8>> {
        if r.chance(p, 4) {
            let n = if r.chance(1, 10) { r.pick(&[127, 128, 129]) } else { r.pick(lens) };
            Some(r.bytes(n))
        } else {
            None
        }
    };
    let ratchet_key = bf(r, 3);
    let ciphertext = bf(r, 3);
    let pq_ratchet = bf(r, 2);
    let addresses = bf(r, 2);
    let uf = |r: &mut Rng| -> Option<u32> {
        if r.chance(3, 4) {
            Some(match r.below(3) {
                0 => r.pick(&[0u32, 1, 127, 128, 16383, 16384, 0x7fff_ffff, 0x8000_0000, u32::MAX]),
                1 => r.below(1000) as u32,
                _ => r.next() as u32,
            })
        } else {
            None
        }
    };
    let counter = uf(r);
    let previous_counter = uf(r);
    SignalMessage { ratchet_key, counter, previous_counter, ciphertext, pq_ratchet, addresses }
}

fn structured(o: &mut Out) {
    o.comment("structured edge cases");
    o.dec(&[]);
    // canonical
    o.dec(&cat(&[&[0x0a, 0x02, 5, 6], &[0x10, 0xac, 0x02]]));
    // every field, canonical
    o.dec(&cat(&[
        &[0x0a, 0x01, 0xaa],
        &[0x10, 0x05],
        &[0x18, 0x06],
        &[0x22, 0x02, 1, 2],
        &[0x2a, 0x01, 3],
        &[0x32, 0x00],
    ]));
    // fields out of order
    o.dec(&cat(&[&[0x32, 0x01, 9], &[0x18, 0x07], &[0x0a, 0x00], &[0x10, 0x01]]));
    // duplicates: last one wins (bytes and uint32)
    o.dec(&cat(&[&[0x0a, 0x01, 1], &[0x0a, 0x02, 2, 3], &[0x10, 0x01], &[0x10, 0x02]]));
    o.dec(&cat(&[&[0x0a, 0x02, 2, 3], &[0x0a, 0x00]]));
    // unknown fields of every wire type
    o.dec(&cat(&[&key(7, 0), &[0x96, 0x01], &[0x10, 0x01]]));
    o.dec(&cat(&[&key(7, 1), &[1, 2, 3, 4, 5, 6, 7, 8], &[0x10, 0x01]]));
    o.dec(&cat(&[&key(7, 1), &[1, 2, 3, 4, 5, 6, 7]])); // 64-bit truncated
    o.dec(&cat(&[&key(7, 5), &[1, 2, 3, 4], &[0x10, 0x01]]));
    o.dec(&cat(&[&key(7, 5), &[1, 2, 3]])); // 32-bit truncated
    o.dec(&cat(&[&key(7, 2), &[0x03, 1, 2, 3], &[0x10, 0x01]]));
    o.dec(&cat(&[&key(7, 2), &[0x04, 1, 2, 3]])); // length > remaining
    o.dec(&cat(&[&key(7, 2), &varint(u64::MAX)])); // huge length
    o.dec(&cat(&[&key(7, 3), &key(7, 4), &[0x10, 0x01]])); // empty group
    o.dec(&cat(&[&key(7, 3), &[0x10, 0x05], &key(1, 2), &[0x00], &key(7, 4)])); // known tags inside group are skipped
    o.dec(&cat(&[&key(7, 3), &key(8, 4)])); // mismatched end tag
    o.dec(&cat(&[&key(7, 3), &[0x10, 0x05]])); // unterminated group
    o.dec(&cat(&[&key(7, 3)])); // unterminated empty group
    o.dec(&cat(&[&key(7, 3), &key(8, 3), &key(8, 4), &key(7, 4)])); // nested
    o.dec(&cat(&[&key(7, 3), &key(8, 3), &key(7, 4), &key(8, 4)])); // crossed
    o.dec(&key(7, 4)); // top-level end group, unknown tag
    o.dec(&key(1, 4)); // top-level end group, known tag
    o.dec(&key(1, 3)); // start group on a known bytes field
    o.dec(&cat(&[&key(2, 3), &key(2, 4)])); // start group on a known uint32 field
    // wire types 6, 7
    o.dec(&key(7, 6));
    o.dec(&key(7, 7));
    o.dec(&key(1, 6));
    o.dec(&cat(&[&key(7, 3), &key(8, 7), &key(7, 4)]));
    // tag 0
    o.dec(&[0x00, 0x00]);
    o.dec(&[0x02, 0x00]);
    o.dec(&[0x80, 0x00]); // non-minimal key 0
    o.dec(&cat(&[&key(7, 3), &[0x00], &key(7, 4)])); // tag 0 inside a group
    // key > u32::MAX, max tag
    o.dec(&cat(&[&varint(0x1_0000_0000), &[0x00]]));
    o.dec(&cat(&[&varint(0xffff_ffff)])); // tag 2^29-1, wt 7
    o.dec(&cat(&[&varint(0xffff_fff8), &[0x00]])); // tag 2^29-1, varint
    o.dec(&cat(&[&varint(0xffff_fffd), &[1, 2, 3, 4]])); // tag 2^29-1, 32-bit
    o.dec(&cat(&[&varint_padded(0x10, 10), &[0x05]])); // 10-byte key for counter
    o.dec(&cat(&[&varint_padded(0x10, 11).as_slice()[..10].to_vec().as_slice(), &[0x05]]));
    // varints: 10-byte, overflow, truncated
    for last in [0x00u8, 0x01, 0x02, 0x7f] {
        let mut v = vec![0x10];
        v.extend([0xff; 9]);
        v.push(last);
        o.dec(&v);
    }
    let mut v = vec![0x10];
    v.extend([0x80; 10]);
    v.push(0x00);
    o.dec(&v); // 11-byte varint
    o.dec(&[0x10, 0x80]); // truncated
    o.dec(&[0x10]); // missing value
    o.dec(&[0x0a]); // missing length
    o.dec(&[0x0a, 0x80]); // truncated length
    o.dec(&cat(&[&[0x10], &varint_padded(5, 10)])); // non-minimal 10-byte value
    o.dec(&cat(&[&[0x10], &varint_padded(5, 2)]));
    o.dec(&cat(&[&[0x0a], &varint_padded(2, 5), &[7, 8]])); // non-minimal length
    // uint32 truncation
    for v in BOUNDARY_U64 {
        o.dec(&cat(&[&[0x10], &varint(*v)]));
        o.dec(&cat(&[&[0x18], &varint(*v)]));
    }
    // wire-type mismatch on known fields
    for (tag, wt) in [(1u64, 0u64), (1, 1), (1, 5), (2, 2), (2, 1), (2, 5), (3, 2), (4, 0), (5, 5), (6, 1)] {
        o.dec(&cat(&[&key(tag, wt), &[0x00, 0, 0, 0, 0, 0, 0, 0]]));
    }
    // length = remaining exactly / one more
    o.dec(&[0x22, 0x03, 1, 2, 3]);
    o.dec(&[0x22, 0x04, 1, 2, 3]);
    // group nesting depth: prost's RECURSION_LIMIT = 100
    for depth in [1usize, 2, 50, 98, 99, 100, 101, 102, 150] {
        for inner in [0u8, 1, 2] {
            let mut v = Vec::new();
            for _ in 0..depth {
                v.extend(key(7, 3));
            }
            match inner {
                1 => v.extend([0x10, 0x01]), // a varint field inside the innermost group
                2 => v.extend(cat(&[&key(9, 3), &key(9, 4)])), // one more (empty) group
                _ => {}
            }
            for _ in 0..depth {
                v.extend(key(7, 4));
            }
            v.extend([0x10, 0x2a]);
            o.dec(&v);
        }
    }
}

fn main() {
    let path = std::env::args().nth(1).expect("usage: prost-diff <out-file>");
    std::panic::set_hook(Box::new(|_| {}));
    let mut o = Out { lines: Vec::new(), n_dec: 0, n_ok: 0, n_enc: 0 };
    o.comment("prost 0.14.4 differential vectors for signal.proto.wire.SignalMessage");
    o.comment("generated by third_party/libsignal/libsignal-session/tools/prost-diff (seed 0x5167_7b02)");
    o.comment("D <input hex|-> ERR | OK <ratchet_key> <counter> <previous_counter> <ciphertext> <pq_ratchet> <addresses>");
    o.comment("E <6 fields> <encoding hex|->   (field: '-' = None, x<hex> = bytes, decimal = uint32)");
    structured(&mut o);
    let mut r = Rng(0x5167_7b02);

    o.comment("random token sequences");
    let mut seqs = Vec::new();
    for _ in 0..2500 {
        let k = r.below(7);
        let mut v = Vec::new();
        for _ in 0..k {
            v.extend(rand_token(&mut r, 0));
        }
        o.dec(&v);
        seqs.push(v);
    }

    o.comment("mutated token sequences and encodings");
    for i in 0..1500 {
        let base = if i % 2 == 0 {
            seqs[r.below(seqs.len() as u64) as usize].clone()
        } else {
            rand_msg(&mut r).encode_to_vec()
        };
        let m = mutate(&mut r, base);
        o.dec(&m);
    }

    o.comment("random byte strings");
    for _ in 0..1500 {
        let n = r.pick(&[0usize, 1, 2, 3, 4, 5, 8, 12, 16, 24, 40, 64]);
        let v = r.bytes(n);
        o.dec(&v);
    }

    o.comment("random messages: encode (and prost's decode of the encoding is the message)");
    o.enc(&SignalMessage::default());
    o.enc(&SignalMessage {
        ratchet_key: Some(vec![0x05; 33]),
        counter: Some(u32::MAX),
        previous_counter: Some(0),
        ciphertext: Some(vec![]),
        pq_ratchet: None,
        addresses: None,
    });
    o.enc(&SignalMessage {
        ratchet_key: None,
        counter: None,
        previous_counter: None,
        ciphertext: Some(vec![0xab; 16384]),
        pq_ratchet: Some(vec![0xcd; 300]),
        addresses: Some(vec![]),
    });
    for _ in 0..1000 {
        let m = rand_msg(&mut r);
        o.enc(&m);
    }

    let total = o.lines.len();
    o.lines.push(format!(
        "# total: {} decode vectors ({} OK), {} encode vectors",
        o.n_dec, o.n_ok, o.n_enc
    ));
    std::fs::write(&path, o.lines.join("\n") + "\n").expect("write");
    eprintln!(
        "wrote {path}: {} lines, {} decode vectors ({} OK), {} encode vectors",
        total + 1,
        o.n_dec,
        o.n_ok,
        o.n_enc
    );
}

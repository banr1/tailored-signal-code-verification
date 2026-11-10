// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Unit tests for `proc-snapshot` (`[testing]`): RSP framing, checksums, escapes, run-length
//! decoding, stop replies, target-description parsing, and PT_LOAD page rounding.

use crate::elf::{ElfInfo, Segment};
use crate::rsp::*;
use crate::snapshot::load_regions;

#[test]
fn frame_checksum_and_escapes() {
    assert_eq!(frame(b"g"), b"$g#67");
    assert_eq!(frame(b"qSupported"), b"$qSupported#37");
    assert_eq!(frame(b""), b"$#00");
    // '#' '$' '}' '*' are escaped as '}' (c ^ 0x20); checksum covers the escaped body.
    let f = frame(b"a#b$c}d*");
    assert_eq!(&f[..f.len() - 3], b"$a}\x03b}\x04c}\x5dd}\x0a");
    let body = &f[1..f.len() - 3];
    let cs = body.iter().fold(0u8, |a, &b| a.wrapping_add(b));
    assert_eq!(&f[f.len() - 2..], format!("{cs:02x}").as_bytes());
    assert_eq!(decode_body(body).unwrap(), b"a#b$c}d*");
}

#[test]
fn run_length_decoding() {
    // "0* " = '0' followed by 3 more ('' ' = 32, 32 - 29 = 3).
    assert_eq!(decode_body(b"0* ").unwrap(), b"0000");
    assert_eq!(decode_body(b"ab*\"c").unwrap(), b"abbbbbbc"); // '"' = 34 -> 5 repeats
    assert!(decode_body(b"*!").is_err()); // no previous byte
    assert!(decode_body(b"a}").is_err());
    assert!(decode_body(b"a*\x10").is_err());
}

#[test]
fn hex_and_stop_replies() {
    assert_eq!(hex_decode(b"00ff10Ab").unwrap(), vec![0, 0xff, 0x10, 0xab]);
    assert!(hex_decode(b"0").is_err());
    assert!(hex_decode(b"zz").is_err());
    assert_eq!(parse_stop(b"S05").unwrap(), 5);
    assert_eq!(parse_stop(b"T05thread:p01.01;").unwrap(), 5);
    assert_eq!(parse_stop(b"T0b").unwrap(), 11);
    assert!(parse_stop(b"OK").is_err());
    assert!(parse_stop(b"W00").is_err());
}

#[test]
fn target_xml_parsing() {
    let top = r#"<?xml version="1.0"?><!DOCTYPE target SYSTEM "gdb-target.dtd">
<target><architecture>aarch64</architecture>
<xi:include href="aarch64-core.xml"/><xi:include href="system-registers.xml"/></target>"#;
    assert_eq!(
        parse_includes(top),
        vec!["aarch64-core.xml", "system-registers.xml"]
    );
    let mut next = 0;
    assert!(parse_target_regs(top, &mut next).unwrap().is_empty());
    let core = r#"<feature name="org.gnu.gdb.aarch64.core">
<reg name="x0" bitsize="64"/><reg name="x1" bitsize="64"/>
<reg name="sp" bitsize="64" type="data_ptr"/>
<reg name="cpsr" bitsize="32" regnum="33"/><reg name="fpsr" bitsize="32"/></feature>"#;
    let regs = parse_target_regs(core, &mut next).unwrap();
    let names: Vec<_> = regs
        .iter()
        .map(|r| (r.name.as_str(), r.regnum, r.bitsize))
        .collect();
    assert_eq!(
        names,
        vec![
            ("x0", 0, 64),
            ("x1", 1, 64),
            ("sp", 2, 64),
            ("cpsr", 33, 32),
            ("fpsr", 34, 32)
        ]
    );
    let tls = r#"<feature name="org.gnu.gdb.aarch64.tls"><reg name="tpidr" bitsize="64" type="data_ptr"/></feature>"#;
    assert_eq!(parse_target_regs(tls, &mut next).unwrap()[0].regnum, 35);
    assert!(parse_target_regs(r#"<reg bitsize="64"/>"#, &mut next).is_err());
}

fn seg(vaddr: u64, memsz: u64, flags: u32) -> Segment {
    Segment {
        vaddr,
        memsz,
        flags,
    }
}

#[test]
fn load_regions_round_and_reject_overlap() {
    let ok = ElfInfo {
        entry: 0,
        segments: vec![seg(0x410f00, 0x200, 6), seg(0x400000, 0x1234, 5)],
        symbols: vec![],
    };
    let rs = load_regions(&ok).unwrap();
    assert_eq!(
        (rs[0].start, rs[0].size, rs[0].perm.as_str()),
        (0x400000, 0x2000, "r-x")
    );
    assert_eq!(
        (rs[1].start, rs[1].size, rs[1].perm.as_str()),
        (0x410000, 0x2000, "rw-")
    );
    let bad = ElfInfo {
        entry: 0,
        segments: vec![seg(0x400000, 0x1234, 5), seg(0x401f00, 0x10, 6)],
        symbols: vec![],
    };
    assert!(load_regions(&bad).is_err());
}

#[test]
fn parse_hex_range_accepts_hex_and_dec() {
    use crate::untrusted_dump::parse_hex_range;
    assert_eq!(parse_hex_range("0x402490:32").unwrap(), (0x402490, 32));
    assert_eq!(parse_hex_range("0x210170:0x20").unwrap(), (0x210170, 32));
    assert!(parse_hex_range("0x400000").is_err());
}

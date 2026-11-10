// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Unit tests: `SHF_MERGE` piece splitting, name normalisation, the patch mirror, and witness
//! extraction (relaxation and branch-to-branch detection) against a synthetic ELF image.

use std::collections::{BTreeMap, BTreeSet};

use super::model::*;
use super::patch::*;
use super::witness::{Elf, ElfSym, Perm, Region, extract_from};
use crate::trusted_common::{ObjSection, RelocKind};

fn merge_sec(bytes: &[u8], entsize: u64, strings: bool) -> ObjSection {
    let flags = object::elf::SHF_ALLOC as u64
        | object::elf::SHF_MERGE as u64
        | if strings {
            object::elf::SHF_STRINGS as u64
        } else {
            0
        };
    ObjSection {
        name: ".rodata.str1.1".into(),
        sh_type: object::elf::SHT_PROGBITS,
        sh_flags: flags,
        addr: 0,
        align: 1,
        entsize,
        size: bytes.len() as u64,
        file_offset: 0,
        bytes: bytes.to_vec(),
        relocs: vec![],
        is_rel: false,
        elf_index: 1,
    }
}

#[test]
fn merge_pieces_strings_split_at_nul() {
    let s = merge_sec(b"ab\0\0c\0", 1, true);
    assert_eq!(merge_pieces(&s).unwrap(), vec![(0, 3), (3, 1), (4, 2)]);
}

#[test]
fn merge_pieces_wide_strings_split_at_zero_entry() {
    // entsize 2: a zero byte inside a character does not end the string.
    let s = merge_sec(&[b'a', 0, 0, 0, b'b', 0, 0, 0], 2, true);
    assert_eq!(merge_pieces(&s).unwrap(), vec![(0, 4), (4, 4)]);
}

#[test]
fn merge_pieces_unterminated_string_rejected() {
    assert!(merge_pieces(&merge_sec(b"ab\0c", 1, true)).is_err());
}

#[test]
fn merge_pieces_constants_split_at_entsize() {
    let s = merge_sec(&[1, 2, 3, 4, 5, 6, 7, 8], 4, false);
    assert_eq!(merge_pieces(&s).unwrap(), vec![(0, 4), (4, 4)]);
    assert!(merge_pieces(&merge_sec(&[1, 2, 3, 4, 5, 6], 4, false)).is_err());
}

#[test]
fn strip_anon_hash_removes_only_long_hashes() {
    assert_eq!(
        strip_anon_hash(".rodata..Lanon.0123456789abcdef0123.5"),
        ".rodata..Lanon.5"
    );
    assert_eq!(
        strip_anon_hash(".rodata..Lanon.12.5"),
        ".rodata..Lanon.12.5"
    );
    assert_eq!(strip_anon_hash(".rodata.cst16"), ".rodata.cst16");
}

// ---------------------------------------------------------------------------------------------
// Synthetic library:
//   f:  adrp x0, near ; add x0, x0, :lo12:near   (relaxable, target within ADR range)
//       adrp x1, far  ; add x1, x1, :lo12:far    (relaxable shape, target out of ADR range)
//       bl g                                     (g is `b ext`: branch-to-branch candidate)
//       ret
//   g:  b ext
// ---------------------------------------------------------------------------------------------

const BASE: u64 = 0x21_0000;
const NEAR: u64 = 0x20_0100;
const FAR: u64 = 0x4000_0000;
const EXT: u64 = 0x21_0100;

fn reloc(off: u64, kind: RelocKind, sym: &str) -> PReloc {
    PReloc {
        off,
        kind,
        sym: sym.into(),
        addend: 0,
    }
}

fn data(sym: &str, read_only: bool, bytes: &[u8], zero_tail: u64) -> PData {
    PData {
        sym: sym.into(),
        align: 8,
        read_only,
        is_tls: false,
        bytes: bytes.to_vec(),
        zero_tail,
        relocs: vec![],
        origin: (0, 0, 0),
        raw_names: vec![],
        demangled_names: vec![],
    }
}

fn synth_lib() -> PLib {
    let words: [u32; 7] = [
        0x9000_0000, // adrp x0, 0
        0x9100_0000, // add x0, x0, #0
        0x9000_0001, // adrp x1, 0
        0x9100_0021, // add x1, x1, #0
        0x9400_0000, // bl 0
        0xd65f_03c0, // ret
        0x1400_0000, // b 0
    ];
    let code = words.iter().flat_map(|w| w.to_le_bytes()).collect();
    PLib {
        name: "synth".into(),
        text: PBlock {
            weak_refs: Default::default(),
            code,
            align: 4,
            symbols: vec![("f".into(), 0), ("g".into(), 0x18)],
            relocs: vec![
                reloc(0x00, RelocKind::AdrpHi21, "near"),
                reloc(0x04, RelocKind::AddLo12, "near"),
                reloc(0x08, RelocKind::AdrpHi21, "far"),
                reloc(0x0c, RelocKind::AddLo12, "far"),
                reloc(0x10, RelocKind::Call26, "g"),
                reloc(0x18, RelocKind::Jump26, "ext"),
            ],
            externs: vec!["ext".into()],
        },
        data: vec![
            data("near", true, &[1, 2, 3, 4, 5, 6, 7, 8], 0),
            data("far", false, &[9, 10, 11, 12], 4),
        ],
        tls: vec![],
        exports: vec!["f".into()],
        text_secs: vec![],
        unreferenced_data: vec![],
        block_raw: BTreeMap::new(),
    }
}

fn expected_placement(b2b: bool) -> PPlacement {
    PPlacement {
        undef_weak: Default::default(),
        base: BASE,
        rho: [("near", NEAR), ("far", FAR), ("ext", EXT)]
            .into_iter()
            .map(|(s, a)| (s.to_string(), a))
            .collect(),
        relax: BTreeSet::from([0]),
        b2b: if b2b {
            BTreeSet::from([0x10])
        } else {
            BTreeSet::new()
        },
    }
}

const RX: Perm = Perm {
    r: true,
    w: false,
    x: true,
};
const RO: Perm = Perm {
    r: true,
    w: false,
    x: false,
};
const RW: Perm = Perm {
    r: true,
    w: true,
    x: false,
};

/// The ELF image a linker following `pl` would produce for `lib` (one page per object).
fn synth_elf(lib: &PLib, pl: &PPlacement) -> Elf {
    let page = |start: u64, perm: Perm, at: u64, bytes: &[u8]| {
        let mut v = vec![0u8; 0x1000];
        let o = (at - start) as usize;
        v[o..o + bytes.len()].copy_from_slice(bytes);
        Region {
            start,
            perm,
            bytes: v,
        }
    };
    let mut text = page(BASE, RX, pl.base, &lib.text.patched(pl));
    let o = (EXT - BASE) as usize;
    text.bytes[o..o + 4].copy_from_slice(&0xd65f_03c0u32.to_le_bytes());
    Elf {
        regions: vec![
            page(0x20_0000, RO, NEAR, &lib.patched_data(pl, 0)),
            text,
            page(FAR, RW, FAR, &lib.patched_data(pl, 1)),
        ],
        syms: vec![ElfSym {
            name: "f".into(),
            value: BASE,
            size: 0x18,
            kind: 2,
            shndx: 1,
            global_part: true,
        }],
    }
}

#[test]
fn relaxable_requires_matching_pair() {
    let lib = synth_lib();
    assert!(lib.text.relaxable_at(0));
    assert!(lib.text.relaxable_at(8));
    assert!(!lib.text.relaxable_at(4));
    assert!(!lib.text.relaxable_at(0x10));
    // `add x0, x1, ...` (source register differs from the ADRP destination): not relaxable.
    let mut other = lib.clone();
    other.text.code[4..8].copy_from_slice(&0x9100_0020u32.to_le_bytes());
    assert!(!other.text.relaxable_at(0));
    // Different addends: not relaxable.
    let mut other = lib;
    other.text.relocs[1].addend = 8;
    assert!(!other.text.relaxable_at(0));
}

#[test]
fn patched_words_relaxed_and_b2b() {
    let lib = synth_lib();
    let pl = expected_placement(true);
    lib.check_placeable(&pl).unwrap();
    let blk = &lib.text;
    assert_eq!(blk.patched_word(&pl, 0x0), NOP);
    assert_eq!(
        blk.patched_word(&pl, 0x4),
        adr_word(adr_template(0x9100_0000), BASE + 4, NEAR)
    );
    assert_eq!(
        blk.patched_word(&pl, 0x8),
        adrp_word(0x9000_0001, BASE + 8, FAR)
    );
    // The call to `g` goes straight to `g`'s branch target.
    assert_eq!(
        blk.patched_word(&pl, 0x10),
        branch_word(0x9400_0000, BASE + 0x10, EXT)
    );
    let pl0 = expected_placement(false);
    assert_eq!(
        blk.patched_word(&pl0, 0x10),
        branch_word(0x9400_0000, BASE + 0x10, BASE + 0x18)
    );
    // Relaxing the far pair is not `Placeable` (ADR out of range).
    let mut bad = pl;
    bad.relax.insert(8);
    assert!(lib.check_placeable(&bad).is_err());
}

#[test]
fn extract_recovers_placement() {
    let lib = synth_lib();
    for b2b in [true, false] {
        let pl = expected_placement(b2b);
        let elf = synth_elf(&lib, &pl);
        assert_eq!(extract_from(&lib, &elf).unwrap(), pl, "b2b = {b2b}");
    }
}

#[test]
fn extract_rejects_corrupted_text() {
    let lib = synth_lib();
    let pl = expected_placement(true);
    let mut elf = synth_elf(&lib, &pl);
    // The `ret` at block offset 0x14 has no relocation: any change must be caught.
    elf.regions[1].bytes[0x14] ^= 1;
    assert!(extract_from(&lib, &elf).is_err());
}

#[test]
fn extract_rejects_wrong_data_permission() {
    let lib = synth_lib();
    let pl = expected_placement(true);
    let mut elf = synth_elf(&lib, &pl);
    elf.regions[2].perm = RO;
    assert!(extract_from(&lib, &elf).is_err());
}

#[test]
fn extract_rejects_duplicate_export() {
    let lib = synth_lib();
    let pl = expected_placement(true);
    let mut elf = synth_elf(&lib, &pl);
    let dup = elf.syms[0].clone();
    elf.syms.push(dup);
    assert!(extract_from(&lib, &elf).is_err());
}

#[test]
fn interned_names_are_sorted_by_code_point_and_cover_every_use() {
    use super::emit::interned_names;
    let r = |off, sym: &str| PReloc {
        off,
        kind: RelocKind::Call26,
        sym: sym.into(),
        addend: 0,
    };
    let lib = PLib {
        name: "my_lib".into(),
        text: PBlock {
            weak_refs: Default::default(),
            code: vec![0; 8],
            align: 4,
            symbols: vec![("b".into(), 0), ("Z".into(), 4)],
            relocs: vec![r(0, "ext"), r(4, "é")],
            externs: vec!["ext".into()],
        },
        data: vec![PData {
            sym: "_d".into(),
            align: 1,
            read_only: true,
            bytes: vec![1],
            zero_tail: 0,
            relocs: vec![r(0, "b")],
            ..Default::default()
        }],
        exports: vec!["b".into()],
        ..Default::default()
    };
    assert_eq!(interned_names(&lib), vec!["Z", "_d", "b", "ext", "é"]);
}

#[test]
fn elf_sha_pin_accepts_match_and_normalises_case() {
    let elf = b"\x7fELF fake";
    let sha = crate::trusted_common::sha256_hex(elf);
    let p = std::path::Path::new("x.elf");
    assert_eq!(super::check_elf_sha(p, elf, Some(&sha)).unwrap(), sha);
    assert_eq!(
        super::check_elf_sha(p, elf, Some(&sha.to_ascii_uppercase())).unwrap(),
        sha
    );
}

#[test]
fn elf_sha_pin_rejects_mismatch() {
    let elf = b"\x7fELF fake";
    let other = crate::trusted_common::sha256_hex(b"\x7fELF other");
    let err = super::check_elf_sha(std::path::Path::new("x.elf"), elf, Some(&other))
        .unwrap_err()
        .to_string();
    assert!(err.contains("elf_sha256 pins"), "{err}");
}

#[test]
fn elf_sha_pin_rejects_missing_pin() {
    let err = super::check_elf_sha(std::path::Path::new("x.elf"), b"\x7fELF", None)
        .unwrap_err()
        .to_string();
    assert!(err.contains("needs `elf_sha256`"), "{err}");
}

#[test]
fn witness_names_primary_and_extra() {
    use super::emit::WitNames;
    let p = WitNames::primary("myLib");
    assert_eq!(p.placement, "myLibPlacement");
    assert_eq!(p.elf, "myLibElf");
    assert_eq!(p.elf_parse, "myLibElf_parse");
    assert_eq!(p.lib_eq, "myLibLib_eq");
    assert_eq!(p.linked_in, "myLibLib_linkedIn");
    let x = WitNames::extra("myLib", "myLibAlt", "altBytes");
    assert_eq!(x.lib.lib, "myLibLib");
    assert_eq!(x.elf_bytes, "altBytes");
    assert_eq!(x.placement, "myLibAltPlacement");
    assert_eq!(x.elf, "myLibAltElf");
    assert_eq!(x.elf_parse, "myLibAlt_parse");
    assert_eq!(x.lib_l, "myLibAltL");
    assert_eq!(x.lib_eq, "myLibAltL_eq");
    assert_eq!(x.linked_in, "myLibAlt_linkedIn");
    // The extra witness shares no declaration name with the primary one.
    for (a, b) in [
        (&p.placement, &x.placement),
        (&p.ly, &x.ly),
        (&p.elf_syms, &x.elf_syms),
    ] {
        assert_ne!(a, b);
    }
}

#[test]
fn build_multi_placed_lib_emits_per_function_blocks_and_per_symbol_data() {
    use super::emit::{render_multi_lib, sidecar_multi_bytes};
    use crate::trusted_common::{ObjReloc, ObjSymbol, RelocType, SymBind, SymKind, SymSection};

    let text_flags = object::elf::SHF_ALLOC as u64 | object::elf::SHF_EXECINSTR as u64;
    let ro_flags = object::elf::SHF_ALLOC as u64;
    let rw_flags = object::elf::SHF_ALLOC as u64 | object::elf::SHF_WRITE as u64;

    // Two `.text.<fn>` sections (`caller` calling `callee` and reading `tab_a`; `callee` reading `tab_b`)
    // plus a `.data` section containing two `STT_OBJECT` symbols (`state_lo` and `state_hi`).
    let caller_words = [
        0x9000_0000u32, // adrp x0, tab_a
        0x9100_0000u32, // add x0, x0, :lo12:tab_a
        0x9400_0000u32, // bl callee
        0xd65f_03c0u32, // ret
    ];
    let callee_words = [
        0x9000_0001u32, // adrp x1, state_hi
        0xf940_0020u32, // ldr x0, [x1, :lo12:state_hi]
        0x9400_0000u32, // bl ext_fn
        0xd65f_03c0u32, // ret
    ];
    let dead_words = [
        0xd65f_03c0u32, // ret
    ];
    let caller_bytes: Vec<u8> = caller_words.iter().flat_map(|w| w.to_le_bytes()).collect();
    let callee_bytes: Vec<u8> = callee_words.iter().flat_map(|w| w.to_le_bytes()).collect();
    let dead_bytes: Vec<u8> = dead_words.iter().flat_map(|w| w.to_le_bytes()).collect();

    let obj = crate::trusted_common::ObjObject {
        name: "widget.o".into(),
        sections: vec![
            ObjSection {
                name: ".text.caller".into(),
                sh_type: object::elf::SHT_PROGBITS,
                sh_flags: text_flags,
                addr: 0,
                align: 4,
                entsize: 0,
                size: caller_bytes.len() as u64,
                file_offset: 0,
                bytes: caller_bytes.clone(),
                relocs: vec![
                    ObjReloc {
                        offset: 0,
                        rtype: RelocType::AdrPrelPgHi21,
                        sym: 2,
                        addend: 0,
                    },
                    ObjReloc {
                        offset: 4,
                        rtype: RelocType::AddAbsLo12Nc,
                        sym: 2,
                        addend: 0,
                    },
                    ObjReloc {
                        offset: 8,
                        rtype: RelocType::Call26,
                        sym: 1,
                        addend: 0,
                    },
                ],
                is_rel: false,
                elf_index: 1,
            },
            ObjSection {
                name: ".text.callee".into(),
                sh_type: object::elf::SHT_PROGBITS,
                sh_flags: text_flags,
                addr: 0,
                align: 4,
                entsize: 0,
                size: callee_bytes.len() as u64,
                file_offset: 0,
                bytes: callee_bytes.clone(),
                relocs: vec![
                    ObjReloc {
                        offset: 0,
                        rtype: RelocType::AdrPrelPgHi21,
                        sym: 4,
                        addend: 0,
                    },
                    ObjReloc {
                        offset: 4,
                        rtype: RelocType::Ldst64AbsLo12Nc,
                        sym: 4,
                        addend: 0,
                    },
                    ObjReloc {
                        offset: 8,
                        rtype: RelocType::Call26,
                        sym: 5,
                        addend: 0,
                    },
                ],
                is_rel: false,
                elf_index: 2,
            },
            ObjSection {
                name: ".text.dead_fn".into(),
                sh_type: object::elf::SHT_PROGBITS,
                sh_flags: text_flags,
                addr: 0,
                align: 4,
                entsize: 0,
                size: dead_bytes.len() as u64,
                file_offset: 0,
                bytes: dead_bytes.clone(),
                relocs: vec![],
                is_rel: false,
                elf_index: 5,
            },
            ObjSection {
                name: ".rodata.tab_a".into(),
                sh_type: object::elf::SHT_PROGBITS,
                sh_flags: ro_flags,
                addr: 0,
                align: 8,
                entsize: 0,
                size: 8,
                file_offset: 0,
                bytes: vec![1, 2, 3, 4, 5, 6, 7, 8],
                relocs: vec![],
                is_rel: false,
                elf_index: 3,
            },
            ObjSection {
                name: ".data.state".into(),
                sh_type: object::elf::SHT_PROGBITS,
                sh_flags: rw_flags,
                addr: 0,
                align: 8,
                entsize: 0,
                size: 16,
                file_offset: 0,
                bytes: vec![
                    10, 11, 12, 13, 14, 15, 16, 17, 20, 21, 22, 23, 24, 25, 26, 27,
                ],
                relocs: vec![],
                is_rel: false,
                elf_index: 4,
            },
        ],
        symbols: vec![
            ObjSymbol {
                name: "caller".into(),
                raw_name: "caller".into(),
                kind: SymKind::Func,
                bind: SymBind::Global,
                vis: 0,
                sec: SymSection::Sec(0),
                value: 0,
                size: caller_bytes.len() as u64,
            },
            ObjSymbol {
                name: "callee".into(),
                raw_name: "callee".into(),
                kind: SymKind::Func,
                bind: SymBind::Global,
                vis: 0,
                sec: SymSection::Sec(1),
                value: 0,
                size: callee_bytes.len() as u64,
            },
            ObjSymbol {
                name: "tab_a".into(),
                raw_name: "tab_a".into(),
                kind: SymKind::Object,
                bind: SymBind::Local,
                vis: 0,
                sec: SymSection::Sec(3),
                value: 0,
                size: 8,
            },
            ObjSymbol {
                name: "state_lo".into(),
                raw_name: "state_lo".into(),
                kind: SymKind::Object,
                bind: SymBind::Local,
                vis: 0,
                sec: SymSection::Sec(4),
                value: 0,
                size: 8,
            },
            ObjSymbol {
                name: "state_hi".into(),
                raw_name: "state_hi".into(),
                kind: SymKind::Object,
                bind: SymBind::Local,
                vis: 0,
                sec: SymSection::Sec(4),
                value: 8,
                size: 8,
            },
            ObjSymbol {
                name: "ext_fn".into(),
                raw_name: "ext_fn".into(),
                kind: SymKind::Func,
                bind: SymBind::Global,
                vis: 0,
                sec: SymSection::Undef,
                value: 0,
                size: 0,
            },
            ObjSymbol {
                name: "dead_fn".into(),
                raw_name: "dead_fn".into(),
                kind: SymKind::Func,
                bind: SymBind::Global,
                vis: 0,
                sec: SymSection::Sec(2),
                value: 0,
                size: dead_bytes.len() as u64,
            },
        ],
        groups: vec![],
        elf_bytes: vec![],
    };

    // `extern_boundary`: the cone stops at `callee`, whose block (and `state_hi`, reachable only
    // through it) is left out; the call to it becomes an extern under its raw name.
    let bounded = |boundary: &[&str], o: &crate::trusted_common::ObjObject| {
        let boundary: Vec<String> = boundary.iter().map(|s| s.to_string()).collect();
        build_multi_placed_lib_bounded("widget", std::slice::from_ref(o), &["caller".into()], &boundary)
    };
    let (blib, braw) = bounded(&["callee"], &obj).unwrap();
    assert_eq!(braw, vec!["callee".to_string()]);
    assert_eq!(blib.blocks.len(), 1);
    assert_eq!(blib.blocks[0].symbols, vec![("caller".into(), 0)]);
    assert_eq!(blib.blocks[0].externs, vec!["callee".to_string()]);
    assert_eq!(blib.lookup_block_sym("callee"), None);
    let bdata: Vec<&str> = blib.data.iter().map(|d| d.sym.as_str()).collect();
    assert_eq!(bdata, vec!["tab_a"]);
    assert!(blib.unreferenced_data.contains(&"state_hi".to_string()));
    // An empty boundary is `build_multi_placed_lib`.
    assert_eq!(bounded(&[], &obj).unwrap().1, Vec::<String>::new());
    assert_eq!(bounded(&[], &obj).unwrap().0.blocks.len(), 2);
    // Fail closed: an export, a non-function, an unknown name, a duplicate.
    let err = |boundary: &[&str], o: &crate::trusted_common::ObjObject| {
        match bounded(boundary, o) {
            Ok(_) => panic!("extern_boundary {boundary:?} accepted"),
            Err(e) => format!("{e:#}"),
        }
    };
    assert!(err(&["caller"], &obj).contains("is an export"));
    assert!(err(&["tab_a"], &obj).contains("not a function defined"));
    assert!(err(&["nope"], &obj).contains("not a function defined"));
    assert!(err(&["callee", "callee"], &obj).contains("listed twice"));
    // Fail closed: the address of a boundary function is taken (`adrp`/`add` of `callee`).
    let mut addr_taken = obj.clone();
    addr_taken.sections[0].relocs[0].sym = 1;
    addr_taken.sections[0].relocs[1].sym = 1;
    assert!(err(&["callee"], &addr_taken).contains("non-branch relocation"));
    // Fail closed: a reachable (here exported) alias shares the boundary function's block.
    let mut alias = obj.clone();
    let mut a = alias.symbols[1].clone();
    a.name = "callee_alias".into();
    a.raw_name = "callee_alias".into();
    alias.symbols.push(a);
    let e = build_multi_placed_lib_bounded(
        "widget",
        std::slice::from_ref(&alias),
        &["caller".into(), "callee_alias".into()],
        &["callee".into()],
    )
    .unwrap_err();
    assert!(format!("{e:#}").contains("shares its block"), "{e:#}");

    let mlib = build_multi_placed_lib("widget", &[obj], &["caller".into()]).unwrap();
    assert_eq!(mlib.blocks.len(), 2);
    assert_eq!(mlib.blocks[0].symbols, vec![("caller".into(), 0)]);
    assert_eq!(mlib.blocks[0].externs, vec!["ext_fn".to_string()]);
    assert_eq!(mlib.blocks[1].symbols, vec![("callee".into(), 0)]);
    assert_eq!(mlib.blocks[1].externs, vec!["ext_fn".to_string()]);
    assert_eq!(mlib.lookup_block_sym("caller"), Some((0, 0)));
    assert_eq!(mlib.lookup_block_sym("callee"), Some((1, 0)));
    assert_eq!(mlib.lookup_block_sym("dead_fn"), None);

    // Per-symbol data entries: `tab_a` and `state_hi` are reachable (`state_lo` is unreferenced).
    let data_syms: Vec<&str> = mlib.data.iter().map(|d| d.sym.as_str()).collect();
    assert_eq!(data_syms, vec!["tab_a", "state_hi"]);
    assert_eq!(mlib.unreferenced_data, vec!["state_lo".to_string()]);
    assert_eq!(
        mlib.data[1].bytes,
        vec![20, 21, 22, 23, 24, 25, 26, 27]
    );

    let sidecar = sidecar_multi_bytes(&mlib);
    assert_eq!(
        sidecar.len(),
        caller_bytes.len() + callee_bytes.len() + 8 + 8
    );

    let lean = render_multi_lib(
        &mlib,
        "widget",
        "Examples.Widget",
        "WidgetPlacedObj.bin",
        &[],
    );
    assert!(lean.contains("def widgetBlocks : List Obj.CodeBlock :="));
    assert!(lean.contains("def widgetMultiLib : Obj.MultiPlacedLib where"));
    assert!(lean.contains("abbrev widgetLib : Obj.MultiPlacedLib := widgetMultiLib"));
    // No weak references or mangled exports: the new optional fields are not emitted.
    assert!(mlib.export_syms.is_empty());
    assert!(mlib.blocks.iter().all(|b| b.weak_refs.is_empty()));
    assert!(!lean.contains("weakRefs") && !lean.contains("exportSyms"));

    // Sharding: at most one shard module is exactly the unsharded module.
    use super::emit::{render_multi_lib_sharded, shard_ranges};
    for mods in [vec![], vec!["Examples.Generated.WidgetPlacedObjShard0".to_string()]] {
        let (top, shards) = render_multi_lib_sharded(
            &mlib,
            "widget",
            "Examples.Widget",
            "WidgetPlacedObj.bin",
            &[],
            &mods,
        );
        assert_eq!(top, lean);
        assert!(shards.is_empty());
    }
    // Two and three shards (more shards than blocks leaves one empty): every block's code
    // constant is defined once, at the unsharded sidecar offset, and the top module imports the
    // shards, joins their lists, and keeps the data and library definitions unchanged.
    for n in [2usize, 3] {
        let mods: Vec<String> = (0..n)
            .map(|k| format!("Examples.Generated.WidgetPlacedObjShard{k}"))
            .collect();
        let (top, shards) = render_multi_lib_sharded(
            &mlib,
            "widget",
            "Examples.Widget",
            "WidgetPlacedObj.bin",
            &[],
            &mods,
        );
        assert_eq!(shards.len(), n);
        let code_def = |i: usize| {
            lean.lines()
                .find(|l| l.starts_with(&format!("def widgetPlacedCode{i} :")))
                .unwrap()
                .to_string()
        };
        for i in 0..mlib.blocks.len() {
            let owners: Vec<usize> = (0..n)
                .filter(|&k| shards[k].lines().any(|l| l == code_def(i)))
                .collect();
            assert_eq!(owners.len(), 1, "block {i} defined in shards {owners:?}");
            assert!(!top.contains(&format!("def widgetPlacedCode{i} ")));
        }
        for (k, (m, s)) in mods.iter().zip(&shards).enumerate() {
            assert!(top.contains(&format!("public import {m}\n")));
            assert!(s.contains(&format!("def widgetBlocksShard{k} : List Obj.CodeBlock := [")));
            assert!(s.contains("namespace Examples.Widget") && s.contains("end Examples.Widget"));
        }
        let joined = if n == 2 {
            "  widgetBlocksShard0 ++ widgetBlocksShard1\n"
        } else {
            "  widgetBlocksShard0 ++ (widgetBlocksShard1 ++ widgetBlocksShard2)\n"
        };
        assert!(top.contains(&format!("def widgetBlocks : List Obj.CodeBlock :=\n{joined}")));
        let tail = |s: &str| s[s.find("/-- The data objects of").unwrap()..].to_string();
        assert_eq!(tail(&top), tail(&lean));
        for i in 0..mlib.data.len() {
            let data_def = format!("def widgetPlacedData{i} :");
            let line = |s: &str| s.lines().find(|l| l.starts_with(&data_def)).unwrap().to_string();
            assert_eq!(line(&top), line(&lean));
        }
    }
    // Shard ranges are contiguous, cover every block in order, and number exactly `n`.
    for n in 1..=4 {
        let rs = shard_ranges(&mlib, n);
        assert_eq!(rs.len(), n);
        assert_eq!(rs.first().unwrap().start, 0);
        assert_eq!(rs.last().unwrap().end, mlib.blocks.len());
        assert!(rs.windows(2).all(|w| w[0].end == w[1].start));
    }

    // Exercise multi-block witness extraction, verification, and Lean rendering with reversed
    // block/data addresses (`callee` placed before `caller`, `state_hi` before `tab_a`).
    use super::emit::{WitNames, render_multi_witness};
    use super::witness::{check_multi, extract_multi_from};

    let mut rho = BTreeMap::new();
    rho.insert("ext_fn".into(), 0x21_0200);
    rho.insert("tab_a".into(), 0x20_0100);
    rho.insert("state_hi".into(), 0x4000_0000);
    let mpl = PMultiPlacement {
        undef_weak: Default::default(),
        bases: vec![0x21_0100, 0x21_0000],
        rho,
        relax: vec![BTreeSet::new(), BTreeSet::new()],
        b2b: vec![BTreeSet::new(), BTreeSet::new()],
    };
    mlib.check_placeable(&mpl).unwrap();

    let mut text = vec![0u8; 0x1000];
    let c0 = mlib.blocks[0].patched(&mlib.block_placement(&mpl, 0));
    let c1 = mlib.blocks[1].patched(&mlib.block_placement(&mpl, 1));
    text[0x000..0x000 + c1.len()].copy_from_slice(&c1);
    text[0x100..0x100 + c0.len()].copy_from_slice(&c0);
    text[0x200..0x204].copy_from_slice(&0xd65f_03c0u32.to_le_bytes());

    let elf = Elf {
        regions: vec![
            Region {
                start: 0x20_0100,
                perm: RO,
                bytes: mlib.patched_data(&mpl, 0),
            },
            Region {
                start: 0x21_0000,
                perm: RX,
                bytes: text,
            },
            Region {
                start: 0x4000_0000,
                perm: RW,
                bytes: mlib.patched_data(&mpl, 1),
            },
        ],
        syms: vec![
            ElfSym {
                name: "caller".into(),
                value: 0x21_0100,
                size: 16,
                kind: 2,
                shndx: 1,
                global_part: true,
            },
            ElfSym {
                name: "callee".into(),
                value: 0x21_0000,
                size: 16,
                kind: 2,
                shndx: 1,
                global_part: true,
            },
            ElfSym {
                name: "ext_fn".into(),
                value: 0x21_0200,
                size: 4,
                kind: 2,
                shndx: 1,
                global_part: true,
            },
        ],
    };
    let extracted = extract_multi_from(&mlib, &elf).unwrap();
    check_multi(&mlib, &extracted, &elf).unwrap();
    assert_eq!(extracted.bases, mpl.bases);
    assert_eq!(extracted.rho, mpl.rho);
    let mut wn = WitNames::primary("widget");
    wn.facts = Some(super::facts::ElfFacts::new(
        "Examples.Generated.WidgetElfFacts",
        "Examples.Widget",
        &wn.elf_bytes,
    ));
    let wit_lean = render_multi_witness(
        &mlib,
        &extracted,
        &wn,
        "Examples.Widget",
        "Examples.Generated.WidgetPlacedObj",
        "Examples.Generated.WidgetElfObj",
        "Widget.elf",
        true,
        &[],
    );
    assert!(wit_lean.contains("def widgetPlacement : Obj.MultiPlacement where"));
    assert!(wit_lean.contains("Obj.Interned.checkMultiDisjoint_spec"));
    // The blocks' shared extern list is emitted once and referenced from every block.
    let ext_def = wit_lean
        .lines()
        .filter(|l| l.starts_with("def widgetLExterns : List Nat := ["))
        .count();
    assert_eq!(ext_def, 1, "{wit_lean}");
    assert_eq!(
        wit_lean.matches("externs := widgetLExterns").count(),
        mlib.blocks.len(),
        "{wit_lean}"
    );
    assert!(!wit_lean.contains("externs := ["), "{wit_lean}");
    // The parsed ELF comes from the facts module; the witness only re-exports it.
    assert!(wit_lean.contains("public import Examples.Generated.WidgetElfFacts"));
    assert!(
        wit_lean.contains(
            "noncomputable abbrev widgetElf : ElfImage := Examples.Widget.widgetElfImage"
        )
    );
    assert!(!wit_lean.contains("elf_image%"));
    // Without an extern split, no extern-symtab theorem is emitted.
    assert!(!wit_lean.contains("_externSymtab"));
    assert!(!wit_lean.contains("ProofLib.Placed.ExternSymtab"));
    // Without `split_check_module`, the one-shot check and no split facts.
    assert!(!wit_lean.contains("checkMultiDisjoint_spec_split"));
    assert!(!wit_lean.contains("seg_lens%"));

    // `split_check_module`: separate top-level kernel facts composed by the split lemma, each
    // heavy one in its own shard module.
    let mut wn_split = wn.clone();
    wn_split.split_check = Some("Examples.Proofs.Split".into());
    let wit_mod = "Examples.Generated.WidgetPlacedWitness";
    let split_files = |wn: &WitNames| {
        super::emit::render_multi_witness_files(
            &mlib,
            &extracted,
            wn,
            "Examples.Widget",
            wit_mod,
            "Examples.Generated.WidgetPlacedObj",
            "Examples.Generated.WidgetElfObj",
            "Widget.elf",
            true,
            &[],
        )
    };
    let files = split_files(&wn_split);
    let shard_names: Vec<&str> = files.shards.iter().map(|(n, _)| n.as_str()).collect();
    assert_eq!(
        shard_names,
        [
            "Defs", "LibEq", "SegLens", "Text", "Data", "ChkNodup", "ChkIds", "ChkSyms",
            "ChkPtext", "ChkPdisj", "ChkPsyms", "ChkPdata", "ChkPnone", "ChkExports", "ChkDdisj"
        ]
    );
    let shard = |n: &str| -> &str {
        &files.shards.iter().find(|(s, _)| s == n).unwrap().1
    };
    let main = &files.main;
    let defs = shard("Defs");
    // Every module imports the split module; each shard and the main module import `Defs`, and
    // the main module imports every shard (so `rustExports` sees them all).
    for (n, text) in files.shards.iter().map(|(n, t)| (n.as_str(), t.as_str())).chain([("main", main.as_str())]) {
        assert!(text.contains("public import Examples.Proofs.Split\n"), "{n}: {text}");
        assert!(text.contains("public meta import Examples.Proofs.Split\n"), "{n}");
        assert!(text.contains("namespace Examples.Widget\n"), "{n}");
        assert!(text.contains("open Arm64.Process ProofLib.ProgramReflection\n"), "{n}");
        assert_eq!(text.matches("set_option maxRecDepth 2000000").count(), 1, "{n}");
        assert!(text.ends_with("end Examples.Widget\n"), "{n}");
        if n != "Defs" {
            assert!(
                text.contains(&format!("public import {wit_mod}ShardDefs\n")),
                "{n}: {text}"
            );
        }
    }
    for n in &shard_names {
        assert!(main.contains(&format!("public import {wit_mod}Shard{n}\n")), "{main}");
    }
    // The definitions and cheap facts are in `Defs` only.
    assert!(defs.contains("def widgetL : Obj.Interned.MultiLib where"));
    assert!(defs.contains("def widgetLy : Obj.Interned.MultiLayout where"));
    assert!(defs.contains("theorem widgetL_names : "));
    assert!(defs.contains("noncomputable def widgetL_segLens : List Nat := seg_lens% widgetElf"));
    assert!(defs.contains("def widgetPlacement : Obj.MultiPlacement where"));
    assert!(!main.contains("def widgetL :") && !main.contains("def widgetPlacement"));
    assert!(!defs.contains("by decide +kernel"), "{defs}");
    // Against the `rGetD`-based `toMultiPlacedLibR` (kernel-cheap names lookups).
    assert!(shard("LibEq").contains(&format!("theorem {} : widgetLib = widgetL.toMultiPlacedLib := Examples.Proofs.Split.toMultiPlacedLib_of_r (by rfl_kernel)", wn.lib_eq)));
    assert!(!defs.contains(&format!("theorem {} ", wn.lib_eq)));
    assert!(shard("SegLens").contains(
        "theorem widgetL_segLens_eq : widgetElf.segments.map (fun r => Examples.Proofs.Split.rLen r.bytes) = widgetL_segLens := by rfl_kernel"
    ));
    // A small library: one text chunk and one data chunk (the tail from 0).
    assert!(shard("Text").contains(
        "theorem widgetL_text : Examples.Proofs.Split.lTextTail widgetL widgetLy (widgetElf.segments.zip widgetL_segLens) 0 = true := by rfl_kernel"
    ));
    assert!(shard("Data").contains(
        "theorem widgetL_data : Examples.Proofs.Split.lDataTail widgetL widgetLy (widgetElf.segments.zip widgetL_segLens) 0 = true := by rfl_kernel"
    ));
    assert!(main.contains(
        "  exact Examples.Proofs.Split.checkMultiDisjoint_spec_chunks widgetL_names widgetElfSyms_eq widgetL_segLens_eq\n    (Examples.Proofs.Split.lTextChunks_nil widgetL_text)\n    (Examples.Proofs.Split.lDataChunks_nil widgetL_data)\n    widgetL_chk_nodup widgetL_chk_ids widgetL_chk_syms widgetL_chk_ptext widgetL_chk_pdisj widgetL_chk_psyms widgetL_chk_pdata widgetL_chk_pnone widgetL_chk_exports widgetL_chk_ddisj\n"
    ), "{main}");
    assert!(main.contains("theorem widgetLib_linkedIn : widgetLib.LinkedIn "), "{main}");
    // One `decide +kernel` declaration per segment-free check, each in its own shard.
    assert!(shard("ChkNodup").contains(
        "theorem widgetL_chk_nodup : Obj.Interned.namesNodup widgetNameChars = true := by decide +kernel"
    ));
    assert!(shard("ChkPtext").contains(
        "theorem widgetL_chk_ptext : Examples.Proofs.Split.textPlaceableAllB widgetL widgetLy = true := by decide +kernel"
    ));
    assert!(shard("ChkExports").contains(
        "theorem widgetL_chk_exports : Obj.Interned.multiExportsOk widgetL widgetLy widgetNameChars (ProofLib.ObjectLoad.prepareCharAssocVal widgetElfSymChars) = true := by decide +kernel"
    ));
    // Data disjointness by the linear scan (pairwise fallback inside `dataDisjointFastB`).
    assert!(shard("ChkDdisj").contains(
        "theorem widgetL_chk_ddisj : Examples.Proofs.Split.dataDisjointFastB widgetL widgetLy = true := by decide +kernel"
    ));
    for (n, text) in &files.shards {
        let k = text.matches(" = true := by decide +kernel").count();
        assert_eq!(k, usize::from(n.starts_with("Chk")), "{n}: {text}");
        assert!(!text.contains("multiDataDisjointB"));
    }
    assert!(!main.contains("by decide +kernel") && !main.contains("by rfl_kernel"), "{main}");
    assert!(!main.contains("checkMultiDisjoint_spec_split"));
    assert!(!main.contains("exact Obj.Interned.checkMultiDisjoint_spec "));
    // With extern `.symtab` facts, they get their own shard too.
    let mut wn_split_ext = wn_split.clone();
    wn_split_ext.extern_symtab = Some((vec!["ext_fn".to_string()], Vec::new()));
    let files_ext = split_files(&wn_split_ext);
    let (last, ext_shard) = files_ext.shards.last().unwrap();
    assert_eq!(last, "ExternSymtab");
    assert!(ext_shard.contains("theorem widget_externSymtab : "), "{ext_shard}");
    assert!(ext_shard.contains("public import ProofLib.Placed.ExternSymtab\n"));
    assert!(files_ext.main.contains(&format!("public import {wit_mod}ShardExternSymtab\n")));
    assert!(!files_ext.main.contains("_externSymtab :"));
    // A text walk over the chunk budget: one shard per chunk, composed by `lTextChunks_cons`.
    let mut big = mlib.clone();
    big.blocks[0].code.resize(40 * 1024, 0);
    let files_big = super::emit::render_multi_witness_files(
        &big,
        &extracted,
        &wn_split,
        "Examples.Widget",
        wit_mod,
        "Examples.Generated.WidgetPlacedObj",
        "Examples.Generated.WidgetElfObj",
        "Widget.elf",
        true,
        &[],
    );
    let big_shard = |n: &str| -> &str {
        &files_big.shards.iter().find(|(s, _)| s == n).unwrap_or_else(|| panic!("no shard {n}")).1
    };
    assert!(files_big.shards.iter().all(|(n, _)| n != "Text"));
    assert!(big_shard("Text0").contains(
        "theorem widgetL_text0 : Examples.Proofs.Split.lTextChunk widgetL widgetLy (widgetElf.segments.zip widgetL_segLens) 0 1 = true := by rfl_kernel"
    ));
    assert!(big_shard("Text1").contains(
        "theorem widgetL_text1 : Examples.Proofs.Split.lTextTail widgetL widgetLy (widgetElf.segments.zip widgetL_segLens) 1 = true := by rfl_kernel"
    ));
    assert!(big_shard("Data").contains("theorem widgetL_data : "));
    for n in ["Text0", "Text1"] {
        assert!(files_big.main.contains(&format!("public import {wit_mod}Shard{n}\n")));
    }
    assert!(files_big.main.contains(
        "\n    (Examples.Proofs.Split.lTextChunks_cons widgetL_text0 (Examples.Proofs.Split.lTextChunks_nil widgetL_text1))\n    (Examples.Proofs.Split.lDataChunks_nil widgetL_data)\n"
    ), "{}", files_big.main);
    // Per-item checks over their budgets: one `allIdxChunk` shard per chunk and the `allIdxTail`,
    // composed by `allIdxChunks_cons` and `<check>_of_chunks`.
    let mut many = mlib.clone();
    let sym0 = many.blocks[0].symbols[0].clone();
    let rel0 = many.blocks[0].relocs[0].clone();
    many.blocks[0].symbols.extend(std::iter::repeat_n(sym0, 70_000));
    many.blocks[0].relocs.extend(std::iter::repeat_n(rel0, 1100));
    let files_many = super::emit::render_multi_witness_files(
        &many,
        &extracted,
        &wn_split,
        "Examples.Widget",
        wit_mod,
        "Examples.Generated.WidgetPlacedObj",
        "Examples.Generated.WidgetElfObj",
        "Widget.elf",
        true,
        &[],
    );
    let many_shard = |n: &str| -> &str {
        &files_many.shards.iter().find(|(s, _)| s == n).unwrap_or_else(|| panic!("no shard {n}")).1
    };
    for c in ["ChkSyms", "ChkPtext", "ChkPnone"] {
        assert!(files_many.shards.iter().all(|(n, _)| n != c), "{c} not chunked");
    }
    let m = "Examples.Proofs.Split";
    assert!(many_shard("ChkSyms0").contains(&format!(
        "theorem widgetL_chk_syms0 : {m}.allIdxChunk ({m}.blockSymsMatchAt widgetLy) widgetL.blocks 0 1 = true := by decide +kernel"
    )));
    assert!(many_shard("ChkSyms1").contains(&format!(
        "theorem widgetL_chk_syms1 : {m}.allIdxTail ({m}.blockSymsMatchAt widgetLy) widgetL.blocks 1 = true := by decide +kernel"
    )));
    assert!(many_shard("ChkPtext0").contains(&format!(
        "theorem widgetL_chk_ptext0 : {m}.allIdxChunk ({m}.textPlaceableAt widgetL widgetLy) widgetL.blocks 0 1 = true := by decide +kernel"
    )));
    assert!(many_shard("ChkPnone0").contains(&format!(
        "theorem widgetL_chk_pnone0 : {m}.allIdxChunk ({m}.dataNotBlockAt widgetL) widgetL.data 0 1 = true := by decide +kernel"
    )));
    assert!(many_shard("ChkPnone1").contains(&format!(
        "theorem widgetL_chk_pnone1 : {m}.allIdxTail ({m}.dataNotBlockAt widgetL) widgetL.data 1 = true := by decide +kernel"
    )));
    for n in ["ChkSyms0", "ChkSyms1", "ChkPtext0", "ChkPtext1", "ChkPnone0", "ChkPnone1"] {
        assert!(files_many.main.contains(&format!("public import {wit_mod}Shard{n}\n")), "{n}");
        assert_eq!(many_shard(n).matches(" = true := by decide +kernel").count(), 1, "{n}");
    }
    assert!(files_many.main.contains(&format!(
        " ({m}.blockSymsMatchB_of_chunks ({m}.allIdxChunks_cons widgetL_chk_syms0 ({m}.allIdxChunks_nil widgetL_chk_syms1))) "
    )), "{}", files_many.main);
    assert!(files_many.main.contains(&format!(
        " ({m}.textPlaceableAllB_of_chunks ({m}.allIdxChunks_cons widgetL_chk_ptext0 ({m}.allIdxChunks_nil widgetL_chk_ptext1))) "
    )), "{}", files_many.main);
    assert!(files_many.main.contains(&format!(
        " ({m}.dataNotBlockB_of_chunks ({m}.allIdxChunks_cons widgetL_chk_pnone0 ({m}.allIdxChunks_nil widgetL_chk_pnone1))) "
    )), "{}", files_many.main);

    // Extern `.symtab` facts: `ext_fn` has one global `STT_FUNC` entry at its placed address.
    use super::witness::extern_symtab_split;
    let (ok, skipped) = extern_symtab_split(&mlib, &extracted, &elf);
    assert_eq!(ok, vec!["ext_fn".to_string()]);
    assert!(skipped.is_empty());
    let mut wn_ext = wn.clone();
    wn_ext.extern_symtab = Some((ok, skipped));
    let ext_lean = render_multi_witness(
        &mlib,
        &extracted,
        &wn_ext,
        "Examples.Widget",
        "Examples.Generated.WidgetPlacedObj",
        "Examples.Generated.WidgetElfObj",
        "Widget.elf",
        true,
        &[],
    );
    assert!(ext_lean.contains("public import ProofLib.Placed.ExternSymtab"));
    assert!(ext_lean.contains("theorem widgetExternIds_names : widgetExternIds.map"));
    assert!(ext_lean.contains(
        "theorem widget_externSymtab : ∀ s ∈ [\"ext_fn\"], Obj.lookupUnique s widgetElf.symbols = some ((widgetLy.toMultiPlacement widgetL.names).ρ s) := by"
    ));
    assert!(ext_lean.contains("Obj.Interned.externSymtab_of (addrs := widgetLy.addrs)"));
    // A duplicate `.symtab` name, a wrong value, and a missing entry are each left out, with
    // the reason in the docstring, and an empty `ok` list emits no theorem.
    for (syms, why) in [
        (vec![("ext_fn", 0x21_0200), ("ext_fn", 0x21_0200)], "2 global defined STT_FUNC entries"),
        (vec![("ext_fn", 0x21_0204)], "differs from the placed address 0x210200"),
        (vec![], "no global defined STT_FUNC entry"),
    ] {
        let mut e2 = elf.clone();
        e2.syms.retain(|s| s.name != "ext_fn");
        e2.syms.extend(syms.iter().map(|&(n, v)| ElfSym {
            name: n.into(),
            value: v,
            size: 4,
            kind: 2,
            shndx: 1,
            global_part: true,
        }));
        let (ok, skipped) = extern_symtab_split(&mlib, &extracted, &e2);
        assert!(ok.is_empty());
        assert_eq!(skipped.len(), 1);
        assert_eq!(skipped[0].0, "ext_fn");
        assert!(skipped[0].1.contains(why), "{:?}", skipped[0].1);
        let mut wn2 = wn.clone();
        wn2.extern_symtab = Some((ok, skipped));
        let lean2 = render_multi_witness(
            &mlib,
            &extracted,
            &wn2,
            "Examples.Widget",
            "Examples.Generated.WidgetPlacedObj",
            "Examples.Generated.WidgetElfObj",
            "Widget.elf",
            true,
            &[],
        );
        assert!(!lean2.contains("_externSymtab"));
    }
    // The options precede every placement definition (large `<obj>Bases`/`Rho`/`Relaxed` lists
    // exceed the default `maxRecDepth`), and are emitted once.
    let pos = |s: &str| {
        wit_lean
            .find(s)
            .unwrap_or_else(|| panic!("missing {s:?} in witness"))
    };
    let rec_depth = pos("set_option maxRecDepth 2000000");
    assert!(pos("set_option maxHeartbeats 0") < rec_depth);
    for def in [
        "def widgetBases",
        "def widgetRho",
        "def widgetRelaxed",
        "def widgetB2b",
        "def widgetPlacement",
    ] {
        assert!(rec_depth < pos(def), "`maxRecDepth` must precede `{def}`");
    }
    assert_eq!(wit_lean.matches("set_option maxRecDepth").count(), 1);
    assert_eq!(wit_lean.matches("set_option maxHeartbeats").count(), 1);

    // Sorting blocks by base: `callee` (0x21_0000) moves before `caller` (0x21_0100), every
    // per-block vector follows, and re-extracting under the new order gives the permuted
    // placement, which still checks.
    use super::witness::sort_multi_blocks_by_base;
    let (mut slib, mut smpl) = (mlib.clone(), extracted.clone());
    assert!(sort_multi_blocks_by_base(&mut slib, &mut smpl));
    assert_eq!(smpl.bases, vec![0x21_0000, 0x21_0100]);
    assert_eq!(slib.blocks[0].symbols, mlib.blocks[1].symbols);
    assert_eq!(slib.blocks[1].symbols, mlib.blocks[0].symbols);
    assert_eq!(slib.blocks[0].code, mlib.blocks[1].code);
    assert_eq!(smpl.relax, vec![extracted.relax[1].clone(), extracted.relax[0].clone()]);
    assert_eq!(smpl.b2b, vec![extracted.b2b[1].clone(), extracted.b2b[0].clone()]);
    assert_eq!(smpl.rho, extracted.rho);
    let resorted = extract_multi_from(&slib, &elf).unwrap();
    assert_eq!(resorted, smpl);
    check_multi(&slib, &resorted, &elf).unwrap();
    // Already sorted: a no-op, and the rendered library and witness are byte-identical.
    let (mut slib2, mut smpl2) = (slib.clone(), smpl.clone());
    assert!(!sort_multi_blocks_by_base(&mut slib2, &mut smpl2));
    assert_eq!(smpl2, smpl);
    let render_lib = |l: &PMultiLib| {
        render_multi_lib(l, "widget", "Examples.Widget", "WidgetPlacedObj.bin", &[])
    };
    let render_wit = |l: &PMultiLib, m: &PMultiPlacement| {
        render_multi_witness(
            l,
            m,
            &wn,
            "Examples.Widget",
            "Examples.Generated.WidgetPlacedObj",
            "Examples.Generated.WidgetElfObj",
            "Widget.elf",
            true,
            &[],
        )
    };
    assert_eq!(render_lib(&slib2), render_lib(&slib));
    assert_eq!(render_wit(&slib2, &smpl2), render_wit(&slib, &smpl));
}

#[test]
fn check_extern_boundary_requires_one_symtab_entry_matching_rho() {
    use super::witness::check_extern_boundary;
    let sym = |name: &str, value: u64, global_part: bool| ElfSym {
        name: name.into(),
        value,
        size: 4,
        kind: 2,
        shndx: 1,
        global_part,
    };
    let elf = |syms: Vec<ElfSym>| Elf {
        regions: vec![],
        syms,
    };
    let mut mpl = PMultiPlacement::default();
    mpl.rho.insert("g".into(), 0x1000);
    let b = vec!["g".to_string()];
    check_extern_boundary(&b, &mpl, &elf(vec![sym("g", 0x1000, true)])).unwrap();
    // Unplaced (not an extern of the library): only the `.symtab` entry is required.
    check_extern_boundary(&b, &PMultiPlacement::default(), &elf(vec![sym("g", 0x2000, true)]))
        .unwrap();
    let err = |e: Elf| format!("{:#}", check_extern_boundary(&b, &mpl, &e).unwrap_err());
    assert!(err(elf(vec![])).contains("has 0 global STT_FUNC"));
    assert!(err(elf(vec![sym("g", 0x1000, false)])).contains("has 0 global STT_FUNC"));
    assert!(err(elf(vec![sym("g", 0x1000, true), sym("g", 0x1000, true)])).contains("has 2 global"));
    assert!(err(elf(vec![sym("g", 0x2000, true)])).contains("placed at 0x1000"));
}

#[test]
fn reg31_excluded_in_adrp_add_and_got_relaxation_allowed_in_tlsie() {
    let words = [
        0x9000_001fu32, // adrp xzr, 0
        0x9100_03ffu32, // add sp, sp, #0
        0x9000_001fu32, // adrp xzr, 0
        0xf940_03ffu32, // ldr xzr, [sp, #0]
        0x9000_001fu32, // adrp xzr, 0
        0xf940_03ffu32, // ldr xzr, [sp, #0]
        0xf940_0020u32, // ldr x0, [x1, #0]
    ];
    let blk = PBlock {
        weak_refs: Default::default(),
        code: words.iter().flat_map(|w| w.to_le_bytes()).collect(),
        align: 4,
        symbols: vec![("f".into(), 0)],
        relocs: vec![
            reloc(0x00, RelocKind::AdrpHi21, "d"),
            reloc(0x04, RelocKind::AddLo12, "d"),
            reloc(0x08, RelocKind::AdrGotPage, "g"),
            reloc(0x0c, RelocKind::Ld64GotLo12Nc, "g"),
            reloc(0x10, RelocKind::TlsieAdrGottprelPage21, "t"),
            reloc(0x14, RelocKind::TlsieLd64GottprelLo12Nc, "t"),
            reloc(0x18, RelocKind::TlsieLd64GottprelLo12Nc, "t"),
        ],
        externs: vec![],
    };
    assert!(!blk.relaxable_at(0x00));
    assert!(!blk.got_pair_at(0x08));
    assert!(blk.tlsie_relaxable_at(0x10));
    assert!(blk.tlsie_relaxable_at(0x14));
    assert!(!blk.tlsie_relaxable_at(0x18));
}

#[test]
fn got_and_tlsie_patch_placeable_and_extract_relaxed_and_unrelaxed() {
    let words = [
        0x9000_0000u32, // adrp x0, :got:ext_a
        0xf940_0000u32, // ldr x0, [x0, :got_lo12:ext_a]
        0x9000_0001u32, // adrp x1, :got:ext_b
        0xf940_0021u32, // ldr x1, [x1, :got_lo12:ext_b]
        0x9000_0002u32, // adrp x2, :gottprel:tls_v
        0xf940_0042u32, // ldr x2, [x2, :gottprel_lo12:tls_v]
        0xd65f_03c0u32, // ret
    ];
    let lib = PLib {
        name: "got_tls".into(),
        text: PBlock {
            weak_refs: Default::default(),
            code: words.iter().flat_map(|w| w.to_le_bytes()).collect(),
            align: 4,
            symbols: vec![("f".into(), 0)],
            relocs: vec![
                reloc(0x00, RelocKind::AdrGotPage, "ext_a"),
                reloc(0x04, RelocKind::Ld64GotLo12Nc, "ext_a"),
                reloc(0x08, RelocKind::AdrGotPage, "ext_b"),
                reloc(0x0c, RelocKind::Ld64GotLo12Nc, "ext_b"),
                reloc(0x10, RelocKind::TlsieAdrGottprelPage21, "tls_v"),
                reloc(0x14, RelocKind::TlsieLd64GottprelLo12Nc, "tls_v"),
            ],
            externs: vec![],
        },
        data: vec![],
        tls: vec![],
        exports: vec!["f".into()],
        text_secs: vec![],
        unreferenced_data: vec![],
        block_raw: BTreeMap::new(),
    };

    // 1. Relaxed: ext_a -> NOP + ADR (`0x00` in relax), ext_b -> ADRP + ADD (`0x0c` in relax),
    //    tls_v -> MOVZ + MOVK (`0x10`, `0x14` in relax).
    let pl_relaxed = PPlacement {
        undef_weak: Default::default(),
        base: BASE,
        rho: [
            ("ext_a", NEAR),
            ("ext_b", FAR + 0x20),
            ("tls_v", 0x0001_0010),
        ]
        .into_iter()
        .map(|(s, a)| (s.to_string(), a))
        .collect(),
        relax: BTreeSet::from([0x00, 0x0c, 0x10, 0x14]),
        b2b: BTreeSet::new(),
    };
    lib.check_placeable(&pl_relaxed).unwrap();
    assert_eq!(lib.text.patched_word(&pl_relaxed, 0x00), NOP);
    assert_eq!(
        lib.text.patched_word(&pl_relaxed, 0x04),
        adr_word(adr_template(0), BASE + 0x04, NEAR)
    );
    assert_eq!(
        lib.text.patched_word(&pl_relaxed, 0x08),
        adrp_word(0x9000_0001, BASE + 0x08, FAR + 0x20)
    );
    assert_eq!(
        lib.text.patched_word(&pl_relaxed, 0x0c),
        ldr_to_add_word(0xf940_0021, FAR + 0x20)
    );
    assert_eq!(
        lib.text.patched_word(&pl_relaxed, 0x10),
        tlsie_movz_word(2, 0x0001_0010)
    );
    assert_eq!(
        lib.text.patched_word(&pl_relaxed, 0x14),
        tlsie_movk_word(2, 0x0001_0010)
    );
    let make_elf = |pl: &PPlacement| {
        let mut bytes = vec![0u8; 0x1000];
        let patched = lib.text.patched(pl);
        bytes[..patched.len()].copy_from_slice(&patched);
        Elf {
            regions: vec![Region {
                start: BASE,
                perm: RX,
                bytes,
            }],
            syms: vec![ElfSym {
                name: "f".into(),
                value: BASE,
                size: 0x1c,
                kind: 2,
                shndx: 1,
                global_part: true,
            }],
        }
    };
    let elf_relaxed = make_elf(&pl_relaxed);
    assert_eq!(extract_from(&lib, &elf_relaxed).unwrap(), pl_relaxed);

    // 2. Unrelaxed (`--no-relax`): GOT slots at 8-byte aligned addresses.
    let pl_unrelaxed = PPlacement {
        undef_weak: Default::default(),
        base: BASE,
        rho: [
            ("ext_a", 0x22_0000),
            ("ext_b", 0x22_0008),
            ("tls_v", 0x22_0010),
        ]
        .into_iter()
        .map(|(s, a)| (s.to_string(), a))
        .collect(),
        relax: BTreeSet::new(),
        b2b: BTreeSet::new(),
    };
    lib.check_placeable(&pl_unrelaxed).unwrap();
    let elf_unrelaxed = make_elf(&pl_unrelaxed);
    assert_eq!(extract_from(&lib, &elf_unrelaxed).unwrap(), pl_unrelaxed);

    // 3. Out-of-range TP offset (>= 2^32) in relaxed TLSIE is rejected.
    let mut bad_tls = pl_relaxed.clone();
    bad_tls.rho.insert("tls_v".into(), 1u64 << 32);
    assert!(lib.check_placeable(&bad_tls).is_err());

    // 4. Misaligned GOT slot in unrelaxed mode is rejected.
    let mut bad_got = pl_unrelaxed;
    bad_got.rho.insert("ext_a".into(), 0x22_0004);
    assert!(lib.check_placeable(&bad_got).is_err());
}

#[test]
fn build_placed_lib_and_placed_only_config_with_tls_and_got_relocs() {
    use super::emit::render_lib;
    use crate::trusted_common::{ObjReloc, ObjSymbol, RelocType, SymBind, SymKind, SymSection};
    use crate::untrusted_driver::config::TranslationConfig;

    let text_flags = object::elf::SHF_ALLOC as u64 | object::elf::SHF_EXECINSTR as u64;
    let tls_flags = object::elf::SHF_ALLOC as u64
        | object::elf::SHF_WRITE as u64
        | object::elf::SHF_TLS as u64;
    let words = [
        0x9000_0000u32, // adrp x0, :got:ext_fn
        0xf940_0000u32, // ldr x0, [x0, :got_lo12:ext_fn]
        0x9000_0001u32, // adrp x1, :gottprel:local_tls
        0xf940_0021u32, // ldr x1, [x1, :gottprel_lo12:local_tls]
        0xd65f_03c0u32, // ret
    ];
    let code: Vec<u8> = words.iter().flat_map(|w| w.to_le_bytes()).collect();
    let obj = crate::trusted_common::ObjObject {
        name: "alpha.o".into(),
        sections: vec![
            ObjSection {
                name: ".text.entry".into(),
                sh_type: object::elf::SHT_PROGBITS,
                sh_flags: text_flags,
                addr: 0,
                align: 4,
                entsize: 0,
                size: code.len() as u64,
                file_offset: 0,
                bytes: code,
                relocs: vec![
                    ObjReloc {
                        offset: 0,
                        rtype: RelocType::AdrGotPage,
                        sym: 1,
                        addend: 0,
                    },
                    ObjReloc {
                        offset: 4,
                        rtype: RelocType::Ld64GotLo12Nc,
                        sym: 1,
                        addend: 0,
                    },
                    ObjReloc {
                        offset: 8,
                        rtype: RelocType::TlsieAdrGottprelPage21,
                        sym: 2,
                        addend: 0,
                    },
                    ObjReloc {
                        offset: 12,
                        rtype: RelocType::TlsieLd64GottprelLo12Nc,
                        sym: 2,
                        addend: 0,
                    },
                ],
                is_rel: false,
                elf_index: 1,
            },
            ObjSection {
                name: ".tdata".into(),
                sh_type: object::elf::SHT_PROGBITS,
                sh_flags: tls_flags,
                addr: 0,
                align: 8,
                entsize: 0,
                size: 8,
                file_offset: 0,
                bytes: vec![0; 8],
                relocs: vec![],
                is_rel: false,
                elf_index: 2,
            },
        ],
        symbols: vec![
            ObjSymbol {
                name: "entry".into(),
                raw_name: "entry".into(),
                kind: SymKind::Func,
                bind: SymBind::Global,
                vis: 0,
                sec: SymSection::Sec(0),
                value: 0,
                size: 20,
            },
            ObjSymbol {
                name: "ext_fn".into(),
                raw_name: "ext_fn".into(),
                kind: SymKind::Notype,
                bind: SymBind::Global,
                vis: 0,
                sec: SymSection::Undef,
                value: 0,
                size: 0,
            },
            ObjSymbol {
                name: "local_tls".into(),
                raw_name: "local_tls".into(),
                kind: SymKind::Tls,
                bind: SymBind::Local,
                vis: 0,
                sec: SymSection::Sec(1),
                value: 0,
                size: 8,
            },
        ],
        groups: vec![],
        elf_bytes: vec![],
    };

    let lib = build_placed_lib("alpha", &[obj], &["entry".into()]).unwrap();
    assert!(lib.data.is_empty());
    assert_eq!(lib.text.relocs.len(), 4);
    assert_eq!(lib.text.relocs[0].kind, RelocKind::AdrGotPage);
    assert_eq!(lib.text.relocs[1].kind, RelocKind::Ld64GotLo12Nc);
    assert_eq!(lib.text.relocs[2].kind, RelocKind::TlsieAdrGottprelPage21);
    assert_eq!(lib.text.relocs[3].kind, RelocKind::TlsieLd64GottprelLo12Nc);
    assert_eq!(lib.text.relocs[2].sym, "local_tls");

    let lean = render_lib(&lib, "alpha", "Examples.Alpha", "AlphaPlacedObj.bin", &[], false);
    assert!(lean.contains("kind := .adrGotPage"));
    assert!(lean.contains("kind := .ld64GotLo12Nc"));
    assert!(lean.contains("kind := .tlsieAdrGottprelPage21"));
    assert!(lean.contains("kind := .tlsieLd64GottprelLo12Nc"));
    // By default nothing is `noncomputable`; `noncomputable_code` marks exactly the code bytes,
    // the text block and the library, and leaves the rest of the module unchanged.
    assert!(!lean.contains("noncomputable"));
    let nc = render_lib(&lib, "alpha", "Examples.Alpha", "AlphaPlacedObj.bin", &[], true);
    for decl in [
        "def alphaPlacedCode : List (BitVec 8) := include_bytes%",
        "def alphaText : Obj.CodeBlock where",
        "def alphaLib : Obj.PlacedLib where",
    ] {
        assert!(lean.contains(&format!("\n{decl}")), "missing {decl:?}");
        assert!(nc.contains(&format!("\nnoncomputable {decl}")), "missing noncomputable {decl:?}");
    }
    assert_eq!(nc.matches("noncomputable ").count(), 3);
    assert_eq!(nc.replace("noncomputable ", ""), lean);

    let toml_src = r#"
obj_name = "alpha"
obj_file = "Examples/Generated/AlphaObj.lean"

[placed]
exports = ["entry"]
placed_only = true
"#;
    let parsed: TranslationConfig = toml::from_str(toml_src).unwrap();
    assert!(parsed.placed.as_ref().unwrap().placed_only);
}

/// A library object with `.init_array` / `.fini_array` sections (each an `abs64` pointer to a
/// local function), whose text references only `.fini_array` (as `fini_tab`), and an optional
/// extra allocated section `extra` (name, `sh_type`).
fn ctor_array_obj(extra: Option<(&str, u32)>) -> crate::trusted_common::ObjObject {
    use crate::trusted_common::{ObjReloc, ObjSymbol, RelocType, SymBind, SymKind, SymSection};

    let text_flags = object::elf::SHF_ALLOC as u64 | object::elf::SHF_EXECINSTR as u64;
    let rw_flags = object::elf::SHF_ALLOC as u64 | object::elf::SHF_WRITE as u64;
    let words = [
        0x9000_0000u32, // adrp x0, fini_tab
        0x9100_0000u32, // add x0, x0, :lo12:fini_tab
        0xd65f_03c0u32, // ret
    ];
    let code: Vec<u8> = words.iter().flat_map(|w| w.to_le_bytes()).collect();
    let ptr_sec = |name: &str, sh_type: u32, elf_index: usize| ObjSection {
        name: name.into(),
        sh_type,
        sh_flags: rw_flags,
        addr: 0,
        align: 8,
        entsize: 0,
        size: 8,
        file_offset: 0,
        bytes: vec![0; 8],
        relocs: vec![ObjReloc {
            offset: 0,
            rtype: RelocType::Abs64,
            sym: 1,
            addend: 0,
        }],
        is_rel: false,
        elf_index,
    };
    let mut sections = vec![
        ObjSection {
            name: ".text.entry".into(),
            sh_type: object::elf::SHT_PROGBITS,
            sh_flags: text_flags,
            addr: 0,
            align: 4,
            entsize: 0,
            size: 8,
            file_offset: 0,
            bytes: code[..8].to_vec(),
            relocs: vec![
                ObjReloc {
                    offset: 0,
                    rtype: RelocType::AdrPrelPgHi21,
                    sym: 2,
                    addend: 0,
                },
                ObjReloc {
                    offset: 4,
                    rtype: RelocType::AddAbsLo12Nc,
                    sym: 2,
                    addend: 0,
                },
            ],
            is_rel: false,
            elf_index: 1,
        },
        ObjSection {
            name: ".text.ctor".into(),
            sh_type: object::elf::SHT_PROGBITS,
            sh_flags: text_flags,
            addr: 0,
            align: 4,
            entsize: 0,
            size: 4,
            file_offset: 0,
            bytes: code[8..].to_vec(),
            relocs: vec![],
            is_rel: false,
            elf_index: 2,
        },
        ptr_sec(".init_array", object::elf::SHT_INIT_ARRAY, 3),
        ptr_sec(".fini_array", object::elf::SHT_FINI_ARRAY, 4),
    ];
    if let Some((name, sh_type)) = extra {
        sections.push(ptr_sec(name, sh_type, 5));
    }
    let sym = |name: &str, kind: SymKind, bind: SymBind, sec: usize, size: u64| ObjSymbol {
        name: name.into(),
        raw_name: name.into(),
        kind,
        bind,
        vis: 0,
        sec: SymSection::Sec(sec),
        value: 0,
        size,
    };
    crate::trusted_common::ObjObject {
        name: "alpha.o".into(),
        sections,
        symbols: vec![
            sym("entry", SymKind::Func, SymBind::Global, 0, 8),
            sym("ctor", SymKind::Func, SymBind::Local, 1, 4),
            sym("fini_tab", SymKind::Object, SymBind::Local, 3, 8),
        ],
        groups: vec![],
        elf_bytes: vec![],
    }
}

#[test]
fn init_and_fini_array_sections_are_data() {
    // Single-block library: `.fini_array` (referenced by the text) is emitted as a writable data
    // object carrying its `abs64` constructor pointer; `.init_array` (unreferenced) is accepted
    // but not emitted.
    let lib = build_placed_lib("alpha", &[ctor_array_obj(None)], &["entry".into()]).unwrap();
    assert_eq!(lib.text.relocs.len(), 2);
    assert_eq!(lib.text.relocs[0].kind, RelocKind::AdrpHi21);
    assert_eq!(lib.text.relocs[0].sym, "fini_tab");
    assert_eq!(lib.text.relocs[1].kind, RelocKind::AddLo12);
    assert_eq!(lib.data.len(), 1);
    let d = &lib.data[0];
    assert_eq!(d.sym, "fini_tab");
    assert!(!d.read_only);
    assert_eq!(d.align, 8);
    assert_eq!(d.bytes, vec![0; 8]);
    assert_eq!(d.zero_tail, 0);
    assert_eq!(d.relocs.len(), 1);
    assert_eq!(d.relocs[0].kind, RelocKind::Abs64);
    assert_eq!(d.relocs[0].sym, "ctor");
    assert_eq!(d.relocs[0].off, 0);
    assert!(
        lib.unreferenced_data
            .iter()
            .any(|n| n.contains(".init_array")),
        "unreferenced data: {:?}",
        lib.unreferenced_data
    );

    // Multi-block library: the same data object, one block per `.text.<fn>` section.
    let mlib = build_multi_placed_lib("alpha", &[ctor_array_obj(None)], &["entry".into()]).unwrap();
    assert_eq!(mlib.blocks.len(), 2);
    assert_eq!(mlib.data.len(), 1);
    assert_eq!(mlib.data[0].sym, "fini_tab");
    assert_eq!(mlib.data[0].relocs[0].kind, RelocKind::Abs64);
    assert_eq!(mlib.data[0].relocs[0].sym, "ctor");
}

#[test]
fn preinit_array_section_is_rejected() {
    // `.preinit_array` is only meaningful in executables; libraries keep rejecting it.
    let err = build_placed_lib(
        "alpha",
        &[ctor_array_obj(Some((
            ".preinit_array",
            object::elf::SHT_PREINIT_ARRAY,
        )))],
        &["entry".into()],
    )
    .unwrap_err();
    assert!(
        err.to_string()
            .contains("unsupported data section type of .preinit_array"),
        "{err:#}"
    );
}

#[test]
fn real_lld_got_and_tlsie_relaxed_and_no_relax() {
    use std::process::Command;

    use super::witness::extract;
    use crate::trusted_extractor::parse_c_object;

    let zig_ok = Command::new("zig")
        .arg("version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false);
    if !zig_ok {
        return;
    }

    let tmp = std::env::temp_dir().join(format!("placed_got_tlsie_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&tmp);
    std::fs::create_dir_all(&tmp).unwrap();

    let asm_src = r#"
.section .text.widget_entry,"ax",@progbits
.globl widget_entry
.type widget_entry, @function
.p2align 2
widget_entry:
    adrp x0, :got:ext_near
    ldr  x0, [x0, :got_lo12:ext_near]
    adrp x1, :got:ext_far
    ldr  x1, [x1, :got_lo12:ext_far]
    adrp x2, :gottprel:tls_slot
    ldr  x2, [x2, :gottprel_lo12:tls_slot]
    ret
.size widget_entry, .-widget_entry

.section .tbss.tls_slot,"awT",@nobits
.globl tls_slot
.type tls_slot, @tls_object
.p2align 3
tls_slot:
    .space 8
.size tls_slot, 8
"#;
    let ext_src = r#"
.section .text.ext_near,"ax",@progbits
.globl ext_near
.type ext_near, @function
.p2align 2
ext_near:
    ret
.size ext_near, .-ext_near

.section .text.ext_far,"ax",@progbits
.p2align 2
    .space 0x200000
.globl ext_far
.type ext_far, @function
ext_far:
    ret
.size ext_far, .-ext_far
"#;
    let asm_path = tmp.join("widget.s");
    let ext_asm_path = tmp.join("ext.s");
    let obj_path = tmp.join("widget.o");
    let ext_obj_path = tmp.join("ext.o");
    let elf_relaxed = tmp.join("widget_relaxed.elf");
    let elf_norelax = tmp.join("widget_norelax.elf");
    std::fs::write(&asm_path, asm_src).unwrap();
    std::fs::write(&ext_asm_path, ext_src).unwrap();

    for (src, dst) in [(&asm_path, &obj_path), (&ext_asm_path, &ext_obj_path)] {
        let st_obj = Command::new("zig")
            .args(["cc", "-target", "aarch64-linux-musl", "-c"])
            .arg(src)
            .arg("-o")
            .arg(dst)
            .status()
            .unwrap();
        assert!(st_obj.success());
    }

    let st_rel = Command::new("zig")
        .args([
            "cc",
            "-target",
            "aarch64-linux-musl",
            "-nostdlib",
            "-static",
            "-Wl,-e,widget_entry",
        ])
        .arg(&obj_path)
        .arg(&ext_obj_path)
        .arg("-o")
        .arg(&elf_relaxed)
        .status()
        .unwrap();
    assert!(st_rel.success());

    let obj_bytes = std::fs::read(&obj_path).unwrap();
    let parsed_obj = parse_c_object("widget.o", obj_bytes).unwrap();
    let lib = build_placed_lib("widget", &[parsed_obj], &["widget_entry".into()]).unwrap();

    let rel_bytes = std::fs::read(&elf_relaxed).unwrap();
    let pl_rel = extract(&lib, &rel_bytes).unwrap();
    assert!(pl_rel.relax.contains(&0x00), "near GOT pair should relax to NOP+ADR in ld.lld");
    assert!(pl_rel.relax.contains(&0x0c), "far GOT pair should relax to ADRP+ADD in ld.lld");
    assert!(pl_rel.relax.contains(&0x10), "TLSIE ADRP should relax to MOVZ in ld.lld");
    assert!(pl_rel.relax.contains(&0x14), "TLSIE LDR should relax to MOVK in ld.lld");

    // Also test stock `ld.lld --no-relax` if `ld.lld` or `rust-lld` is available.
    let lld_bin = Command::new("rustc")
        .args(["--print", "sysroot"])
        .output()
        .ok()
        .and_then(|o| String::from_utf8(o.stdout).ok())
        .map(|s| {
            std::path::PathBuf::from(s.trim())
                .join("lib/rustlib/x86_64-unknown-linux-gnu/bin/gcc-ld/ld.lld")
        })
        .filter(|p| p.exists())
        .unwrap_or_else(|| std::path::PathBuf::from("ld.lld"));
    if Command::new(&lld_bin)
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
    {
        let st_norel = Command::new(&lld_bin)
            .args([
                "-m",
                "aarch64linux",
                "-static",
                "-e",
                "widget_entry",
                "--no-relax",
            ])
            .arg(&obj_path)
            .arg(&ext_obj_path)
            .arg("-o")
            .arg(&elf_norelax)
            .status()
            .unwrap();
        assert!(st_norel.success());
        let norel_bytes = std::fs::read(&elf_norelax).unwrap();
        let pl_norel = extract(&lib, &norel_bytes).unwrap();
        assert!(!pl_norel.relax.contains(&0x00), "near GOT pair must not relax under --no-relax");
        assert!(!pl_norel.relax.contains(&0x0c), "far GOT pair must not relax under --no-relax");
        // In static `ET_EXEC`, `ld.lld` relaxes IE -> LE (`MOVZ` + `MOVK`) even under `--no-relax`
        // (unrelaxed TLSIE `ADRP` + `LDR` is covered by `got_and_tlsie_patch_placeable_and_extract_relaxed_and_unrelaxed`).
        assert!(pl_norel.relax.contains(&0x10), "ld.lld relaxes static ET_EXEC TLSIE to LE");
        assert!(pl_norel.relax.contains(&0x14), "ld.lld relaxes static ET_EXEC TLSIE to LE");
    }

    let _ = std::fs::remove_dir_all(&tmp);
}

#[test]
fn relaxable_at_rejects_rd_31_sp_vs_xzr() {
    // `adrp x0, 0; add x0, x0, #0` at 0x00 is relaxable (`rd = 0`).
    // `adrp xzr, 0; add sp, sp, #0` at 0x08 has `rd = rn = 31` (`0x1f`), which must NOT relax
    // because `ADD` interprets 31 as `SP` while `ADR` interprets 31 as `XZR`.
    let words: [u32; 5] = [
        0x9000_0000, // adrp x0, 0
        0x9100_0000, // add x0, x0, #0
        0x9000_001f, // adrp xzr, 0
        0x9100_03ff, // add sp, sp, #0
        0xd65f_03c0, // ret
    ];
    let code = words.iter().flat_map(|w| w.to_le_bytes()).collect();
    let blk = PBlock {
        weak_refs: Default::default(),
        code,
        align: 4,
        symbols: vec![("f".into(), 0)],
        relocs: vec![
            reloc(0x00, RelocKind::AdrpHi21, "dat"),
            reloc(0x04, RelocKind::AddLo12, "dat"),
            reloc(0x08, RelocKind::AdrpHi21, "dat"),
            reloc(0x0c, RelocKind::AddLo12, "dat"),
        ],
        externs: vec![],
    };
    assert!(blk.relaxable_at(0x00));
    assert!(!blk.relaxable_at(0x08));

    let pl = PPlacement {
        undef_weak: Default::default(),
        base: 0x40_0000,
        rho: [("dat".into(), 0x40_1234)].into(),
        relax: [0x00, 0x08].into(),
        b2b: Default::default(),
    };
    assert!(blk.relaxed_at(&pl, 0x00));
    assert!(!blk.relaxed_at(&pl, 0x08));
    assert_eq!(blk.patched_word(&pl, 0x00), NOP);
    assert_eq!(blk.patched_word(&pl, 0x04), adr_word(adr_template(0x9100_0000), 0x40_0004, 0x40_1234));
    // `rd = 31` pair remains unrelaxed ADRP + ADD even when `0x08` is in `pl.relax`.
    assert_eq!(blk.patched_word(&pl, 0x08), adrp_word(0x9000_001f, 0x40_0008, 0x40_1234));
    assert_eq!(blk.patched_word(&pl, 0x0c), lo12_word(0, 0x9100_03ff, 0x40_1234));
}

#[test]
fn tlsdesc_and_tlsle_reloc_patching_and_ranges() {
    assert_eq!(tls_base_offset(1), 16);
    assert_eq!(tls_base_offset(8), 16);
    assert_eq!(tls_base_offset(16), 16);
    assert_eq!(tls_base_offset(32), 32);
    assert_eq!(tls_base_offset(64), 64);

    let tprel = 0x0012_3458u64;
    assert_eq!(
        patch_reloc_word(RelocKind::TlsdescAdrPage21, 0x9000_0000, 0x40_0000, tprel),
        0xd2a0_0000 | (0x0012 << 5)
    );
    assert_eq!(
        patch_reloc_word(RelocKind::TlsdescLd64Lo12, 0xf940_0001, 0x40_0004, tprel),
        0xf280_0000 | (0x3458 << 5)
    );
    assert_eq!(
        patch_reloc_word(RelocKind::TlsdescAddLo12, 0x9100_0000, 0x40_0008, tprel),
        NOP
    );
    assert_eq!(
        patch_reloc_word(RelocKind::TlsdescCall, 0xd63f_0020, 0x40_000c, tprel),
        NOP
    );
    assert_eq!(
        patch_reloc_word(RelocKind::TlsleAddTprelHi12, 0x9140_0043, 0x40_0010, tprel),
        0x9140_0043 | (0x123 << 10)
    );
    assert_eq!(
        patch_reloc_word(RelocKind::TlsleAddTprelLo12Nc, 0x9100_0063, 0x40_0014, tprel),
        0x9100_0063 | (0x458 << 10)
    );
    assert!(code_reloc_in_range(RelocKind::TlsdescAdrPage21, 0x40_0000, (1u64 << 32) - 1));
    assert!(!code_reloc_in_range(RelocKind::TlsdescAdrPage21, 0x40_0000, 1u64 << 32));
    assert!(code_reloc_in_range(RelocKind::TlsleAddTprelHi12, 0x40_0000, (1u64 << 24) - 1));
    assert!(!code_reloc_in_range(RelocKind::TlsleAddTprelHi12, 0x40_0000, 1u64 << 24));
    assert!(code_reloc_in_range(RelocKind::TlsleAddTprelLo12, 0x40_0000, 0xfff));
    assert!(!code_reloc_in_range(RelocKind::TlsleAddTprelLo12, 0x40_0000, 0x1000));
    assert!(code_reloc_in_range(RelocKind::TlsleLdst64TprelLo12Nc, 0x40_0000, 0x18));
    assert!(!code_reloc_in_range(RelocKind::TlsleLdst64TprelLo12Nc, 0x40_0000, 0x14));
}

#[test]
fn synthesize_placement_and_render_placeable_witness_without_elf() {
    use super::emit::{WitNames, render_placeable_witness};
    use super::model::PData;
    use super::witness::synthesize_placement;
    use crate::untrusted_driver::config::TranslationConfig;

    let mut relocs = vec![
        reloc(0x00, RelocKind::Call26, "ext_alpha"),
        reloc(0x04, RelocKind::Call26, "ext_beta"),
        reloc(0x08, RelocKind::TlsleAddTprelHi12, "tls_counter"),
        reloc(0x0c, RelocKind::TlsleAddTprelLo12, "tls_counter"),
    ];
    let mut data = Vec::new();
    for i in 0..300usize {
        let sym = format!("data_obj_{i:03}");
        let off = 0x10 + (i as u64) * 8;
        relocs.push(reloc(off, RelocKind::AdrpHi21, &sym));
        relocs.push(PReloc {
            off: off + 4,
            kind: RelocKind::Ldst64Lo12,
            sym: sym.clone(),
            addend: 8,
        });
        data.push(PData {
            sym,
            align: 16,
            read_only: i % 2 == 0,
            bytes: vec![0u8; 16],
            zero_tail: 16,
            relocs: vec![PReloc {
                off: 0,
                kind: RelocKind::Abs64,
                sym: "entry".into(),
                addend: 0,
            }],
            ..Default::default()
        });
    }
    let code_words = 4 + 300 * 2 + 1;
    let lib = PLib {
        name: "widget".into(),
        text: PBlock {
            weak_refs: Default::default(),
            code: vec![0u8; code_words * 4],
            align: 16,
            symbols: vec![("entry".into(), 0)],
            relocs,
            externs: vec!["ext_alpha".into(), "ext_beta".into()],
        },
        data,
        tls: vec![PData {
            sym: "tls_counter".into(),
            align: 8,
            is_tls: true,
            bytes: vec![0; 8],
            zero_tail: 0,
            ..Default::default()
        }],
        exports: vec!["entry".into()],
        text_secs: vec![],
        unreferenced_data: vec![],
        block_raw: BTreeMap::new(),
    };

    let pl = synthesize_placement(&lib).unwrap();
    lib.check_placeable(&pl).unwrap();
    assert_ne!(pl.rho("ext_alpha"), pl.rho("ext_beta"));
    assert!(pl.rho("tls_counter") < 0x1000);
    assert_eq!(pl.rho("tls_counter") % 16, 0);

    let wn = WitNames::primary("widget");
    let lean = render_placeable_witness(
        &lib,
        &pl,
        &wn,
        "Examples.Widget",
        "Examples.Generated.WidgetPlacedObj",
        &[],
    );
    assert!(lean.contains("public import Examples.Generated.WidgetPlacedObj"));
    assert!(lean.contains("public import ProofLib.Placed.Check"));
    assert!(lean.contains("theorem widgetPlacement_placeable_and_externs :"));
    assert!(lean.contains("theorem widgetPlacement_relocsOk :"));
    assert!(lean.contains("externsDisjoint_of_externsDisjointB rfl rfl hnd hok h4"));
    assert!(lean.contains(
        "theorem widgetLib_placeable : ∃ pl, widgetLib.Placeable pl ∧ (widgetLib.text.externs.map pl.ρ).Nodup :="
    ));
    assert!(lean.contains("theorem widgetLib_exists_placeable : ∃ pl, widgetLib.Placeable pl :="));

    let toml_src = r#"
obj_name = "widget"
obj_file = "Examples/Generated/WidgetObj.lean"

[placed]
exports = ["entry"]
placed_only = true
witness = true
placed_witness_out = "Examples/Generated/WidgetPlacedWitness.lean"
"#;
    let parsed: TranslationConfig = toml::from_str(toml_src).unwrap();
    let p = parsed.placed.unwrap();
    assert!(p.witness);
    assert_eq!(
        p.placed_witness_out.unwrap(),
        std::path::PathBuf::from("Examples/Generated/WidgetPlacedWitness.lean")
    );
}

#[test]
fn undef_weak_branch_patches_to_next_instruction_only_for_weak_refs() {
    let mut lib = synth_lib();
    let mut pl = expected_placement(false);
    pl.undef_weak.insert("ext".into());
    // `ext` is not a weak reference of the block: `undefWeak` is ignored.
    assert_eq!(
        lib.text.patched_word(&pl, 0x18),
        branch_word(0x1400_0000, BASE + 0x18, EXT)
    );
    lib.text.weak_refs = vec!["ext".into()];
    lib.check_placeable(&pl).unwrap();
    // `b ext` with `ext` left undefined becomes `b .+4`.
    assert_eq!(lib.text.patched_word(&pl, 0x18), 0x1400_0001);
    // The call to the defined `g` is unaffected.
    assert_eq!(
        lib.text.patched_word(&pl, 0x10),
        branch_word(0x9400_0000, BASE + 0x10, BASE + 0x18)
    );
    // Without `undefWeak`, the weak reference resolves through `ρ` as before.
    let pl0 = expected_placement(false);
    assert_eq!(
        lib.text.patched_word(&pl0, 0x18),
        branch_word(0x1400_0000, BASE + 0x18, EXT)
    );
    // A weak reference reached only by branches has no recoverable address: extraction fails
    // closed.
    let elf = synth_elf(&lib, &pl);
    assert!(extract_from(&lib, &elf).is_err());
}

#[test]
fn weak_undef_refs_requires_every_reference_weak() {
    use crate::trusted_common::{ObjObject, ObjSymbol, SymBind, SymKind, SymSection};
    let undef = |n: &str, bind| ObjSymbol {
        name: n.into(),
        raw_name: n.into(),
        kind: SymKind::Notype,
        bind,
        vis: 0,
        sec: SymSection::Undef,
        value: 0,
        size: 0,
    };
    let obj = |syms| ObjObject {
        name: "o".into(),
        sections: vec![],
        symbols: syms,
        groups: vec![],
        elf_bytes: vec![],
    };
    let objs = [
        obj(vec![
            undef("wk", SymBind::Weak),
            undef("mixed", SymBind::Weak),
            undef("strong", SymBind::Global),
        ]),
        obj(vec![
            undef("mixed", SymBind::Global),
            undef("wk", SymBind::Weak),
        ]),
    ];
    let externs: Vec<String> = ["mixed", "strong", "wk", "absent"].map(String::from).into();
    assert_eq!(weak_undef_refs(&objs, &externs), vec!["wk".to_string()]);
}

#[test]
fn export_syms_records_mangled_names_checked_by_demangling() {
    let raw = "_ZN4core3fmt5write17h0123456789abcdefE";
    let exports: Vec<String> = vec!["core::fmt::write".into(), "c_fn".into()];
    let block_raw: BTreeMap<String, String> = [
        ("core::fmt::write".to_string(), raw.to_string()),
        ("c_fn".to_string(), "c_fn".to_string()),
    ]
    .into();
    // Unmangled exports are omitted (the `elfSym` default is the export's own name).
    assert_eq!(
        export_syms("alpha", &exports, &block_raw).unwrap(),
        vec![("core::fmt::write".to_string(), raw.to_string())]
    );
    // A recorded raw name that does not demangle to the export is rejected.
    let bad: BTreeMap<String, String> = [
        (
            "core::fmt::write".to_string(),
            "_ZN4core3fmt6format17h0123456789abcdefE".to_string(),
        ),
        ("c_fn".to_string(), "c_fn".to_string()),
    ]
    .into();
    assert!(export_syms("alpha", &exports, &bad).is_err());
    // An export without a raw name is rejected.
    assert!(export_syms("alpha", &exports, &BTreeMap::new()).is_err());
}

#[test]
fn multi_lib_elf_sym_defaults_to_export_name() {
    let mut lib = PMultiLib::default();
    lib.export_syms = vec![("a::b".into(), "_ZN1a1b17h0123456789abcdefE".into())];
    assert_eq!(lib.elf_sym("a::b"), "_ZN1a1b17h0123456789abcdefE");
    assert_eq!(lib.elf_sym("c_fn"), "c_fn");
}

// Per-ELF facts modules (`facts`).

/// A linked `PlacedConfig` whose generated modules live in `dir` (module prefix `Gen`).
fn facts_cfg(dir: &std::path::Path) -> crate::untrusted_driver::config::PlacedConfig {
    crate::untrusted_driver::config::PlacedConfig {
        exports: vec![],
        elf: Some(dir.join("widget.elf")),
        elf_sha256: Some("aa".into()),
        lib_file: dir.join("WidgetPlacedObj.lean"),
        lib_module: "Gen.WidgetPlacedObj".into(),
        elf_file: dir.join("WidgetElfObj.lean"),
        elf_module: "Gen.WidgetElfObj".into(),
        elf_bytes_override: None,
        elf_facts_module: None,
        witness_file: dir.join("WidgetPlacedWitness.lean"),
        witness_module: "Gen.WidgetPlacedWitness".into(),
        linked: true,
        emit_placeable_witness: false,
        multi: false,
        noncomputable_code: false,
        placed_shards: 1,
        extern_boundary: vec![],
        placed_only: false,
        emit_extracted_obj: false,
        extra_witnesses: vec![],
        split_check_module: None,
        chunked_check: false,
        split_parse_module: None,
    }
}

fn elf_use(bytes: &str, sha: &str, ns: &str, facts_module: Option<&str>) -> super::facts::ElfUse {
    super::facts::ElfUse {
        elf: std::path::PathBuf::from("/x/widget.elf"),
        elf_sha256: sha.into(),
        elf_bytes: bytes.into(),
        elf_bytes_module: format!("Spec.{bytes}"),
        namespace: ns.into(),
        facts_module: facts_module.map(str::to_string),
    }
}

/// A fresh empty scratch directory for one test.
fn facts_tmp(name: &str) -> std::path::PathBuf {
    let d = std::env::temp_dir().join(format!("rust-obj2lean-facts-{}-{name}", std::process::id()));
    let _ = std::fs::remove_dir_all(&d);
    std::fs::create_dir_all(&d).unwrap();
    d
}

#[test]
fn facts_stem_and_names() {
    use super::facts::{ElfFacts, bytes_base, facts_stem};
    assert_eq!(bytes_base("widgetElfBytes"), "widgetElf");
    assert_eq!(bytes_base("A.B.altBytes"), "alt");
    assert_eq!(bytes_base("Bytes"), "Bytes");
    assert_eq!(facts_stem("widgetElfBytes"), "WidgetElfFacts");
    assert_eq!(facts_stem("altBytes"), "AltElfFacts");
    assert_eq!(facts_stem("gadgetDriverBytes"), "GadgetDriverElfFacts");
    let f = ElfFacts::new("Gen.WidgetElfFacts", "Ns.Sub", "widgetElfBytes");
    assert_eq!(f.image, "Ns.Sub.widgetElfImage");
    assert_eq!(f.parse, "Ns.Sub.widgetElfImage_parse");
    assert_eq!(f.syms, "Ns.Sub.widgetElfImageSyms");
    assert_eq!(f.sym_chars, "Ns.Sub.widgetElfImageSymChars");
    assert_eq!(f.syms_eq, "Ns.Sub.widgetElfImageSyms_eq");
}

#[test]
fn facts_plan_groups_witnesses_by_bytes_constant() {
    let d = facts_tmp("group");
    let p = facts_cfg(&d);
    let uses = [
        elf_use("widgetElfBytes", "AA", "Ns", None),
        elf_use("altBytes", "bb", "Ns.Alt", None),
        // Same bytes as the primary (SHA compared case-insensitively): shares its module.
        elf_use("widgetElfBytes", "aa", "Ns.Other", None),
    ];
    let plan = super::facts::plan(&p, &uses).unwrap();
    assert_eq!(plan.emit.len(), 2);
    assert_eq!(plan.emit[0].file, d.join("WidgetElfFacts.lean"));
    assert_eq!(plan.emit[0].facts.module, "Gen.WidgetElfFacts");
    assert_eq!(plan.emit[1].facts.module, "Gen.AltElfFacts");
    assert_eq!(plan.per_use[0], plan.per_use[2]);
    // The group takes the namespace of its first witness.
    assert_eq!(plan.per_use[2].image, "Ns.widgetElfImage");
    assert_eq!(plan.per_use[1].image, "Ns.Alt.altImage");
    // A facts module defines no bytes and records what it is about.
    let (_, text) = super::facts::facts_output(&plan.emit[0], &[]);
    assert!(text.contains("public import Spec.widgetElfBytes"));
    assert!(text.contains(
        "-- rust-obj2lean elf-facts: bytes=widgetElfBytes module=Spec.widgetElfBytes sha256=aa namespace=Ns"
    ));
    // The ELF path is relative to the facts module.
    let rel = super::emit::relative_path(&d, std::path::Path::new("/x/widget.elf"));
    assert!(text.contains(&format!(
        "noncomputable def widgetElfImage : ElfImage := elf_image% \"{rel}\""
    )));
    assert!(text.contains(
        "theorem widgetElfImage_parse : ElfImage.parse widgetElfBytes = .ok widgetElfImage := by"
    ));
    assert!(!text.contains("file_bytes%"));
    assert!(!text.contains("def widgetElfBytes"));
}

#[test]
fn facts_plan_rejects_conflicting_pins() {
    let d = facts_tmp("conflict");
    let p = facts_cfg(&d);
    let sha = [
        elf_use("widgetElfBytes", "aa", "Ns", None),
        elf_use("widgetElfBytes", "bb", "Ns", None),
    ];
    assert!(super::facts::plan(&p, &sha).is_err());
    let mut other_module = elf_use("widgetElfBytes", "aa", "Ns", None);
    other_module.elf_bytes_module = "Spec.Other".into();
    let uses = [elf_use("widgetElfBytes", "aa", "Ns", None), other_module];
    assert!(super::facts::plan(&p, &uses).is_err());
    // Two constants with the same stem.
    let uses = [
        elf_use("A.widgetElfBytes", "aa", "Ns", None),
        elf_use("B.widgetElfBytes", "bb", "Ns", None),
    ];
    let err = super::facts::plan(&p, &uses).unwrap_err().to_string();
    assert!(err.contains("both map to facts module"), "{err}");
}

/// A synthetic ELF64 file: header, 3-entry `.symtab` at 64 (`sh_info = 1`), 8-byte `.strtab` at
/// 136, and 3 section headers (null, `.symtab` linking to `.strtab`, `.strtab`) at 144.
fn split_parse_elf() -> Vec<u8> {
    let mut b = vec![0u8; 336];
    b[..6].copy_from_slice(b"\x7fELF\x02\x01");
    let put = |b: &mut Vec<u8>, off: usize, v: u64, n: usize| {
        b[off..off + n].copy_from_slice(&v.to_le_bytes()[..n]);
    };
    put(&mut b, 40, 144, 8); // e_shoff
    put(&mut b, 58, 64, 2); // e_shentsize
    put(&mut b, 60, 3, 2); // e_shnum
    let (sym, str_) = (144 + 64, 144 + 128);
    put(&mut b, sym + 4, 2, 4); // SHT_SYMTAB
    put(&mut b, sym + 24, 64, 8);
    put(&mut b, sym + 32, 72, 8);
    put(&mut b, sym + 40, 2, 4); // sh_link
    put(&mut b, sym + 44, 1, 4); // sh_info
    put(&mut b, str_ + 4, 3, 4); // SHT_STRTAB
    put(&mut b, str_ + 24, 136, 8);
    put(&mut b, str_ + 32, 8, 8);
    b
}

#[test]
fn split_parse_layout_follows_symtab_offsets() {
    use super::facts::{ParseLayout, parse_layout};
    let b = split_parse_elf();
    assert_eq!(
        parse_layout(&b).unwrap(),
        ParseLayout {
            len: 336,
            tails: vec![88, 136, 144]
        }
    );
    // Without a symbol table only the section headers are a far offset.
    let mut nosym = b.clone();
    nosym[144 + 64 + 4] = 1;
    assert_eq!(parse_layout(&nosym).unwrap().tails, vec![144]);
    // No section headers, a section header table past the end, or not an ELF64 file: rejected.
    let mut noshdr = b.clone();
    noshdr[60] = 0;
    assert!(parse_layout(&noshdr).is_err());
    let mut past = b.clone();
    past[40] = 0xf0;
    past[41] = 0x01;
    assert!(parse_layout(&past).is_err());
    assert!(parse_layout(&b[..32]).is_err());
    let mut elf32 = b;
    elf32[4] = 1;
    assert!(parse_layout(&elf32).is_err());
}

#[test]
fn split_parse_facts_compose_kernel_facts() {
    let d = facts_tmp("split");
    let elf = d.join("widget.elf");
    std::fs::write(&elf, split_parse_elf()).unwrap();
    let mut p = facts_cfg(&d);
    p.split_parse_module = Some("Gen.Proofs.ParseSplit".into());
    let mut u = elf_use("widgetElfBytes", "aa", "Ns", None);
    u.elf = elf.clone();
    let plan = super::facts::plan(&p, &[u.clone()]).unwrap();
    let (_, text) = super::facts::facts_output(&plan.emit[0], &[]);
    let m = "Gen.Proofs.ParseSplit";
    for line in [
        format!("public import {m}"),
        format!("public meta import {m}"),
        "noncomputable def widgetElfImage_tail0 : List (BitVec 8) := suffix_of% widgetElfBytes 88"
            .into(),
        format!(
            "theorem widgetElfImage_tail0_eq : widgetElfBytes.drop 88 = widgetElfImage_tail0 := \
             {m}.drop_of_rDrop (by rfl_kernel)"
        ),
        format!("  {m}.drop_chain widgetElfImage_tail1_eq (b := 8) (by rfl_kernel) rfl"),
        "  [(88, widgetElfImage_tail0), (136, widgetElfImage_tail1), (144, widgetElfImage_tail2)]"
            .into(),
        "  .cons widgetElfImage_tail0_eq (.cons widgetElfImage_tail1_eq (.cons \
         widgetElfImage_tail2_eq (.nil)))"
            .into(),
        format!("  {m}.length_of_drop 192 widgetElfImage_tail2_eq (by rfl_kernel) (by decide) rfl"),
        format!(
            "theorem widgetElfImage_hdr : {m}.hdrOk widgetElfBytes 336 widgetElfImage = true := by rfl_kernel"
        ),
        format!(
            "theorem widgetElfImage_symtab : {m}.symtabOf widgetElfBytes widgetElfImage_tails 336 = .ok widgetElfImage.symbols := by"
        ),
        "theorem widgetElfImage_parse : ElfImage.parse widgetElfBytes = .ok widgetElfImage :="
            .into(),
    ] {
        assert!(text.contains(&line), "missing {line:?} in\n{text}");
    }
    assert!(!text.contains("parse_of_fastParse"));
    // Without the key: the one-shot parse proof, and the ELF is not read.
    p.split_parse_module = None;
    u.elf = d.join("missing.elf");
    let plan = super::facts::plan(&p, &[u.clone()]).unwrap();
    let (_, text) = super::facts::facts_output(&plan.emit[0], &[]);
    assert!(text.contains("  apply ElfImage.parse_of_fastParse"));
    assert!(!text.contains("ParseSplit") && !text.contains("suffix_of%"));
    // With the key, an unreadable ELF fails generation.
    p.split_parse_module = Some(m.into());
    assert!(super::facts::plan(&p, &[u]).is_err());
}

#[test]
fn elf_facts_module_fails_closed() {
    use super::facts::{FactsModule, plan};
    let d = facts_tmp("existing");
    let p = facts_cfg(&d);
    let reference = |stem: &str| [elf_use("altBytes", "bb", "Ns.Alt", Some(stem))];
    // Missing module.
    let err = plan(&p, &reference("AltElfFacts")).unwrap_err().to_string();
    assert!(err.contains("does not exist"), "{err}");
    // A file that is not a facts module.
    std::fs::write(d.join("NotFacts.lean"), "module\n").unwrap();
    let err = plan(&p, &reference("NotFacts")).unwrap_err().to_string();
    assert!(err.contains("is not a facts module"), "{err}");
    // A facts module emitted for another config.
    let write_facts = |stem: &str, bytes: &str, sha: &str| {
        let module = FactsModule {
            file: d.join(format!("{stem}.lean")),
            facts: super::facts::ElfFacts::new(&format!("Gen.{stem}"), "Ns.Emit", bytes),
            namespace: "Ns.Emit".into(),
            elf: d.join("alt.elf"),
            elf_sha256: sha.into(),
            elf_bytes: bytes.into(),
            elf_bytes_module: format!("Spec.{bytes}"),
            split_parse: None,
        };
        let (path, text) = super::facts::facts_output(&module, &[]);
        std::fs::write(path, text).unwrap();
    };
    // Wrong module name: it is about another bytes constant.
    write_facts("WidgetElfFacts", "widgetElfBytes", "bb");
    let err = plan(&p, &reference("WidgetElfFacts"))
        .unwrap_err()
        .to_string();
    assert!(err.contains("is about `widgetElfBytes`"), "{err}");
    // Constant mismatch: same name, but the bytes constant is defined in another module.
    let mut moved = reference("WidgetElfFacts");
    moved[0].elf_bytes = "widgetElfBytes".into();
    moved[0].elf_bytes_module = "Spec.Elsewhere".into();
    let err = plan(&p, &moved).unwrap_err().to_string();
    assert!(err.contains("is about `widgetElfBytes`"), "{err}");
    // SHA-256 mismatch.
    write_facts("AltElfFacts", "altBytes", "cc");
    let err = plan(&p, &reference("AltElfFacts")).unwrap_err().to_string();
    assert!(err.contains("records SHA-256 cc"), "{err}");
    // A matching module: its names (in its own namespace) are used, nothing is emitted.
    write_facts("AltElfFacts", "altBytes", "bb");
    let ok = plan(&p, &reference("AltElfFacts")).unwrap();
    assert!(ok.emit.is_empty());
    assert_eq!(ok.per_use[0].module, "Gen.AltElfFacts");
    assert_eq!(ok.per_use[0].image, "Ns.Emit.altImage");
    // Redundant: this config already emits the facts of these bytes.
    let uses = [
        elf_use("altBytes", "bb", "Ns", None),
        elf_use("altBytes", "bb", "Ns", Some("AltElfFacts")),
    ];
    let err = plan(&p, &uses).unwrap_err().to_string();
    assert!(err.contains("redundant"), "{err}");
}

#[test]
fn linked_witness_reexports_facts_under_its_own_names() {
    use super::emit::{WitNames, render_witness};
    let lib = synth_lib();
    let pl = expected_placement(true);
    let mut wn = WitNames::extra("widget", "widgetAlt", "altBytes");
    wn.facts = Some(super::facts::ElfFacts::new(
        "Gen.AltElfFacts",
        "Ns.Emit",
        "altBytes",
    ));
    let lean = render_witness(
        &lib,
        &pl,
        &wn,
        "Ns",
        "Gen.WidgetPlacedObj",
        "Spec.Alt",
        "alt.elf",
        true,
        &[],
    );
    assert!(lean.contains("public import Gen.AltElfFacts"));
    assert!(!lean.contains("elf_image%"));
    assert!(!lean.contains("rfl_kernel\n\nnoncomputable"));
    for line in [
        "noncomputable abbrev widgetAltElf : ElfImage := Ns.Emit.altImage",
        "theorem widgetAlt_parse : ElfImage.parse altBytes = .ok widgetAltElf := by",
        "  with_reducible exact Ns.Emit.altImage_parse",
        "noncomputable abbrev widgetAltElfSyms : List (String × BitVec 64) := Ns.Emit.altImageSyms",
        "noncomputable abbrev widgetAltElfSymChars : List (List Char × BitVec 64) := Ns.Emit.altImageSymChars",
        "theorem widgetAltElfSyms_eq : widgetAltElf.symbols = toStringAssoc widgetAltElfSymChars := by",
        "  with_reducible exact Ns.Emit.altImageSyms_eq",
        "theorem widgetAlt_ok : ",
        "theorem widgetAlt_linkedIn : widgetLib.LinkedIn altBytes :=",
    ] {
        assert!(lean.contains(line), "missing {line:?}");
    }
}

#[test]
fn placed_elf_keys_are_validated() {
    use crate::untrusted_driver::config::{PlacedTomlConfig, validate_placed_elf_keys};
    let check = |extra: &str| {
        let src = format!("exports = []\n{extra}");
        let p: PlacedTomlConfig = toml::from_str(&src).unwrap();
        validate_placed_elf_keys(&p)
    };
    assert!(check("elf = \"a.elf\"\nlinked = true\nelf_facts_module = \"AElfFacts\"\n").is_ok());
    assert!(
        check("elf = \"a.elf\"\nelf_bytes = \"aBytes\"\nelf_bytes_module = \"Spec.A\"\n").is_ok()
    );
    assert!(check("elf = \"a.elf\"\nelf_bytes = \"aBytes\"\n").is_err());
    assert!(check("elf_bytes = \"aBytes\"\nelf_bytes_module = \"Spec.A\"\n").is_err());
    assert!(check("elf = \"a.elf\"\nelf_facts_module = \"AElfFacts\"\n").is_err());
    assert!(
        check("elf = \"a.elf\"\nlinked = true\nelf_facts_module = \"Gen.AElfFacts\"\n").is_err()
    );
    let extra = "[[extra_witnesses]]\nmodule = \"W\"\nprefix = \"w\"\nelf = \"b.elf\"\n\
                 elf_sha256 = \"bb\"\nelf_bytes = \"bBytes\"\nelf_bytes_module = \"Spec.B\"\n";
    assert!(check(&format!("{extra}elf_facts_module = \"BElfFacts\"\n")).is_ok());
    assert!(check(&format!("{extra}elf_facts_module = \"../BElfFacts\"\n")).is_err());
    // `split_check_module`: a dotted module name, only for a linked multi-block witness.
    let split = |m: &str, keys: &str| check(&format!("{keys}split_check_module = \"{m}\"\n"));
    let ml = "elf = \"a.elf\"\nlinked = true\nmulti = true\n";
    assert!(split("Gen.Proofs.Split", ml).is_ok());
    assert!(split("Split", ml).is_ok());
    assert!(split("Gen.Proofs.Split", "elf = \"a.elf\"\nlinked = true\n").is_err());
    assert!(split("Gen.Proofs.Split", "elf = \"a.elf\"\nmulti = true\n").is_err());
    assert!(split("Gen..Split", ml).is_err());
    assert!(split("Gen/Split", ml).is_err());
    assert!(split("", ml).is_err());
    // `split_parse_module`: a dotted module name, only for a linked witness.
    let sp = |m: &str, keys: &str| check(&format!("{keys}split_parse_module = \"{m}\"\n"));
    let linked = "elf = \"a.elf\"\nlinked = true\n";
    assert!(sp("Gen.Proofs.ParseSplit", linked).is_ok());
    assert!(sp("Gen.Proofs.ParseSplit", "elf = \"a.elf\"\n").is_err());
    assert!(sp("Gen.Proofs.ParseSplit", "linked = true\n").is_err());
    assert!(sp("Gen..ParseSplit", linked).is_err());
    assert!(sp("Gen/ParseSplit", linked).is_err());
    // `chunked_check`: only for a linked single-block witness (primary or extra).
    let ch = |keys: &str| check(&format!("{keys}chunked_check = true\n"));
    assert!(ch(linked).is_ok());
    assert!(check(&format!("chunked_check = true\n{extra}")).is_ok());
    assert!(ch("elf = \"a.elf\"\n").is_err());
    assert!(ch("").is_err());
    assert!(ch(ml).is_err());
    // `noncomputable_code`: only for a single-block library without a placement witness.
    let ncc = |keys: &str| check(&format!("noncomputable_code = true\n{keys}"));
    assert!(ncc("placed_only = true\n").is_ok());
    assert!(ncc("multi = true\n").is_err());
    assert!(ncc("elf = \"a.elf\"\n").is_err());
    assert!(ncc("linked = true\n").is_err());
    assert!(ncc("witness = true\n").is_err());
    assert!(ncc("placed_witness_out = \"W.lean\"\n").is_err());
    assert!(ncc("chunked_check = true\n").is_err());
    assert!(ncc(extra).is_err());
}

#[test]
fn split_walk_chunks() {
    use super::emit::{chunk_bounds, chunk_ranges};
    let b = |c: &[u64], budget| chunk_bounds(c.iter().copied(), budget);
    // Everything fits: one chunk, no interior boundary.
    assert_eq!(b(&[], 10), Vec::<usize>::new());
    assert_eq!(b(&[3, 3, 4], 10), Vec::<usize>::new());
    // Greedy split at the first item that would exceed the budget.
    assert_eq!(b(&[3, 3, 5, 6], 10), vec![2, 3]);
    // An item over the budget is a chunk of its own, never an empty chunk before it.
    assert_eq!(b(&[20, 1, 20], 10), vec![1, 2]);
    assert_eq!(b(&[0, 0, 20], 10), Vec::<usize>::new());
    assert_eq!(chunk_ranges(&[]), vec![(0, None)]);
    assert_eq!(chunk_ranges(&[2, 3]), vec![(0, Some(2)), (2, Some(3)), (3, None)]);
}

#[test]
fn chunked_witness_splits_kernel_facts_into_shards() {
    use super::emit::{WitNames, render_witness_files};
    let lib = synth_lib();
    let pl = expected_placement(true);
    let mut wn = WitNames::extra("widget", "widgetAlt", "altBytes");
    wn.facts = Some(super::facts::ElfFacts::new(
        "Gen.AltElfFacts",
        "Ns.Emit",
        "altBytes",
    ));
    wn.chunked = true;
    wn.lib_ns = Some("Lib".into());
    let files = render_witness_files(
        &lib,
        &pl,
        &wn,
        "Ns",
        "Gen.WidgetAltWitness",
        "Gen.WidgetPlacedObj",
        "Spec.Alt",
        "alt.elf",
        true,
        &[],
    );
    let names: Vec<&str> = files.shards.iter().map(|(s, _)| s.as_str()).collect();
    assert_eq!(
        names,
        [
            "Defs",
            "LibEq",
            "Names",
            "SegLens",
            "Sym",
            "Text",
            "Data",
            "ChkNodup",
            "ChkIds",
            "ChkPtext",
            "ChkPdata",
            "ChkExports",
            "ChkDdisj"
        ]
    );
    let shard = |s: &str| &files.shards.iter().find(|(n, _)| n == s).unwrap().1;
    // The tree slot of the block symbol `g` (index 3 of `[ext, f, far, g, near]`) is resolved.
    let defs = shard("Defs");
    assert!(defs.contains("noncomputable def widgetAltLTree : Obj.Interned.VecTree"));
    assert!(defs.contains(&format!("⟨false, 0x0#64, {:#x}#64⟩", BASE + 0x18)));
    assert!(defs.contains(&format!("⟨true, {EXT:#x}#64, {EXT:#x}#64⟩")));
    assert!(
        defs.contains("noncomputable def widgetAltL_segLens : List Nat := seg_lens% widgetAltElf")
    );
    assert!(!defs.contains("theorem widgetAltL_eq"));
    assert!(!defs.contains("decide"));
    // The names tree holds `ext` (index 0 of `[ext, f, far, g, near]`) as a string literal.
    assert!(defs.contains("noncomputable def widgetAltLNamesTree : Obj.Interned.VecTree String"));
    assert!(defs.contains("\"ext\""));
    assert!(shard("LibEq").contains(
        "theorem widgetAltL_eq : widgetLib = widgetAltL.toLibT 5 widgetAltLNamesTree := by rfl_kernel"
    ));
    assert!(shard("LibEq").contains(
        "theorem widgetAltL_namesLen : ProofLib.Placed.Split.rLen widgetAltL.names = 5 := by rfl_kernel"
    ));
    assert!(shard("Names").contains(
        "Obj.Interned.namesFrom widgetAltLNamesTree (5 - 0) 0 = ProofLib.Placed.Split.rDrop 0 widgetAltL.names := by rfl_kernel"
    ));
    assert!(shard("Text").contains(
        "theorem widgetAltL_text : Obj.Interned.textOkTailT widgetAltL widgetAltLy widgetAltLTree (widgetAltElf.segments.zip widgetAltL_segLens) 0x0 false 0 = true := by decide +kernel"
    ));
    assert!(
        shard("Sym")
            .contains("Obj.Interned.symTreeOkTail widgetAltL widgetAltLy widgetAltLTree 0 = true")
    );
    assert!(
        shard("ChkDdisj").contains("Obj.Interned.dataDisjointROB widgetAltL widgetAltLy = true")
    );
    for (s, text) in &files.shards {
        // Every module opens the library module's namespace, which differs from `Ns`.
        assert!(text.contains("\nopen Lib\n"), "{s}");
        if s != "Defs" {
            assert!(
                text.contains("public import Gen.WidgetAltWitnessShardDefs"),
                "{s}"
            );
        }
    }
    // The main module composes the facts without evaluating anything in the kernel.
    let main = &files.main;
    assert!(!main.contains("decide"), "{main}");
    assert!(main.contains("public import Gen.WidgetAltWitnessShardChkDdisj"));
    assert!(main.contains("Obj.Interned.checkDisjoint_spec_chunksT widgetAltL_names"));
    assert!(main.contains(
        "  rw [widgetAltL_eq, Obj.Interned.Lib.toLibT_eq widgetAltL_namesLen (Obj.Interned.namesTreeOkChunks_nil widgetAltL_namesTree)]"
    ));
    assert!(main.contains("(Obj.Interned.textOkChunksT_nil widgetAltL_text)"));
    assert!(main.contains("theorem widgetAlt_ok : widgetLib.Placeable"));
    assert!(main.contains("  ⟨_, widgetAltElf, widgetAlt_parse, widgetAlt_ok.1, widgetAlt_ok.2⟩"));
    // Without `chunked`, one module.
    wn.chunked = false;
    let one = render_witness_files(
        &lib,
        &pl,
        &wn,
        "Ns",
        "Gen.W",
        "Gen.WidgetPlacedObj",
        "Spec.Alt",
        "alt.elf",
        true,
        &[],
    );
    assert!(one.shards.is_empty());
    assert!(one.main.contains("Obj.Interned.check_spec"));
}

#[test]
fn chunked_bounds_cut_text_where_no_relocation_straddles() {
    use super::chunked::{TEXT_CHUNK_WORDS, TREE_CHUNK_NAMES, text_bounds, tree_bounds};
    use super::chunked::{NAMES_CHUNK_NAMES, names_bounds};
    assert_eq!(names_bounds(1718), Vec::<usize>::new());
    // 8193 names: three chunks of about equal size.
    assert_eq!(names_bounds(2 * NAMES_CHUNK_NAMES + 1), vec![2731, 5462]);
    assert_eq!(tree_bounds(10), Vec::<usize>::new());
    assert_eq!(
        tree_bounds(TREE_CHUNK_NAMES + 1),
        vec![TREE_CHUNK_NAMES / 2]
    );
    assert_eq!(tree_bounds(1718), vec![859]);
    let mut lib = synth_lib();
    assert!(text_bounds(&lib).is_empty());
    // Two chunks' worth of code; relocated words at and before the midpoint move the cut on.
    let len = 2 * TEXT_CHUNK_WORDS * 4;
    lib.text.code = vec![0; len as usize];
    let mid = len / 2;
    lib.text.relocs = vec![
        reloc(0x10, RelocKind::Call26, "g"),
        reloc(mid - 4, RelocKind::AdrpHi21, "near"),
        reloc(mid, RelocKind::AddLo12, "near"),
        reloc(mid + 8, RelocKind::Call26, "g"),
    ];
    assert_eq!(text_bounds(&lib), vec![(mid + 8, false, 3)]);
    // Unsorted relocations: one chunk.
    lib.text.relocs.swap(0, 1);
    assert!(text_bounds(&lib).is_empty());
}

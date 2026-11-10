// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Unit tests for [`super`] (`trusted_extractor`) (`Role::Test`, `[TEST ONLY]`; not part of the TCB).
//!
//! Covers ELF section classification, relocation-type mapping, alignment and doc comments,
//! extern resolution and collision checks, rendering of `<ObjName>Obj.lean` literals, and
//! `SHT_GROUP` / COMDAT parsing, trimming, rejection, and `ExtractedObj.groups` emission.

use std::path::PathBuf;

use itertools::Itertools;

use super::*;
use crate::trusted_common::{
    ConfiguredExtern, ExternDecl, ExternKind, Extraction, ObjModuleMeta, SecKind,
};
use crate::untrusted_driver::{
    NeededExtern, RlibDef, check_extern_collisions, needed_externs, resolve_externs,
    resolve_externs_with_config,
};

#[test]
fn classifies_sections_by_type_and_flags() {
    let a = elf::SHF_ALLOC as u64;
    let w = elf::SHF_WRITE as u64;
    let x = elf::SHF_EXECINSTR as u64;
    let t = elf::SHF_TLS as u64;
    let ms = (elf::SHF_MERGE | elf::SHF_STRINGS) as u64;
    assert_eq!(
        SecKind::classify(".s", elf::SHT_PROGBITS, a | x),
        Some(SecKind::Text)
    );
    assert_eq!(
        SecKind::classify(".s", elf::SHT_PROGBITS, a),
        Some(SecKind::Rodata)
    );
    assert_eq!(
        SecKind::classify(".s", elf::SHT_PROGBITS, a | ms),
        Some(SecKind::Rodata)
    );
    assert_eq!(
        SecKind::classify(".s", elf::SHT_PROGBITS, a | w),
        Some(SecKind::Data)
    );
    assert_eq!(
        SecKind::classify(".s", elf::SHT_NOBITS, a | w),
        Some(SecKind::Bss)
    );
    let relro = |n| SecKind::classify(n, elf::SHT_PROGBITS, a | w);
    assert_eq!(relro(".data.rel.ro"), Some(SecKind::Rodata));
    assert_eq!(relro(".data.rel.ro.local"), Some(SecKind::Rodata));
    assert_eq!(relro(".data.rel.ro._ZN3foo3barE"), Some(SecKind::Rodata));
    assert_eq!(relro(".data.rel"), Some(SecKind::Data));
    assert_eq!(relro(".data.rel.rodata"), Some(SecKind::Data));
    let retain = elf::SHF_GNU_RETAIN as u64;
    assert_eq!(
        SecKind::classify(".init_array", elf::SHT_INIT_ARRAY, a | w),
        Some(SecKind::Rodata)
    );
    assert_eq!(
        SecKind::classify(".init_array", elf::SHT_INIT_ARRAY, a | w | retain),
        Some(SecKind::Rodata)
    );
    assert_eq!(
        SecKind::classify(".fini_array", elf::SHT_FINI_ARRAY, a | w),
        Some(SecKind::Rodata)
    );
    assert_eq!(
        SecKind::classify(".s", elf::SHT_PROGBITS, a | w | t),
        Some(SecKind::Tdata)
    );
    assert_eq!(
        SecKind::classify(".s", elf::SHT_NOBITS, a | w | t),
        Some(SecKind::Tbss)
    );
    // Not allocated, COMDAT group flag, writable code, unsupported types.
    assert_eq!(SecKind::classify(".s", elf::SHT_PROGBITS, x), None);
    assert_eq!(
        SecKind::classify(".s", elf::SHT_PROGBITS, a | elf::SHF_GROUP as u64),
        None
    );
    assert_eq!(SecKind::classify(".s", elf::SHT_PROGBITS, a | w | x), None);
    assert_eq!(SecKind::classify(".s", elf::SHT_INIT_ARRAY, a), None);
    assert_eq!(
        SecKind::classify(".s", elf::SHT_INIT_ARRAY, a | w | x),
        None
    );
    assert_eq!(
        SecKind::classify(".s", elf::SHT_INIT_ARRAY, a | w | t),
        None
    );
    assert_eq!(SecKind::classify(".s", elf::SHT_NOBITS, a), None);
}

#[test]
fn reloc_types_map_to_lean_constructors() {
    assert_eq!(RelocType::from_r_type(283), RelocType::Call26);
    assert_eq!(
        RelocType::from_r_type(541).lean_ctor(),
        ".tlsieAdrGottprelPage21"
    );
    assert_eq!(
        RelocType::from_r_type(549).lean_ctor(),
        ".tlsleAddTprelHi12"
    );
    assert_eq!(
        RelocType::from_r_type(551).lean_ctor(),
        ".tlsleAddTprelLo12Nc"
    );
    assert_eq!(RelocType::from_r_type(999).lean_ctor(), "(.other 999)");
    assert!(RelocType::Jump26.is_branch() && !RelocType::AdrGotPage.is_branch());
    assert!(RelocType::TlsleAddTprelHi12.is_tlsle() && RelocType::TlsleAddTprelLo12Nc.is_tlsle());
}

#[test]
fn alignment_and_doc_comments() {
    assert!(check_align(1, "x").is_ok() && check_align(4096, "x").is_ok());
    assert!(check_align(3, "x").is_err() && check_align(8192, "x").is_err());
    assert_eq!(doc_safe("a -/ b /- c"), "a - / b / - c");
    assert_eq!(
        crate::trusted_common::lean_string_lit("a\"b\\c\n"),
        "\"a\\\"b\\\\c\\n\""
    );
}

fn needed(name: &str, types: &[RelocType]) -> NeededExtern {
    NeededExtern {
        raw_name: name.into(),
        name: name.into(),
        ref_types: types.iter().map(|t| t.lean_ctor()).collect(),
        all_branch: types.iter().all(|t| t.is_branch()),
        any_ldst: types.iter().any(|t| t.is_ldst()),
        any_tls: types.iter().any(|t| t.is_tlsie() || t.is_tlsle()),
        all_tls: types.iter().all(|t| t.is_tlsie() || t.is_tlsle()),
        any_branch: types.iter().any(|t| t.is_branch()),
        obj_kinds: [".notype".to_string()].into_iter().collect(),
        max_access_end: types.iter().map(|t| t.access_size()).max().unwrap_or(0),
    }
}

fn def(kind: ExternKind, size: u64) -> RlibDef {
    RlibDef {
        kind,
        size,
        align: 8,
        origin: "libx.rlib(x.o)".into(),
    }
}

#[test]
fn extern_resolution_follows_the_q1_rule() {
    let mut defs = BTreeMap::new();
    defs.insert("data".to_string(), vec![def(ExternKind::Object, 256)]);
    defs.insert("tls".to_string(), vec![def(ExternKind::Tls, 24)]);
    defs.insert(
        "f".to_string(),
        vec![def(ExternKind::Func, 12), def(ExternKind::Func, 12)],
    );
    defs.insert(
        "bad".to_string(),
        vec![def(ExternKind::Func, 12), def(ExternKind::Func, 16)],
    );
    let ok = resolve_externs(
        &[
            needed("memcpy", &[RelocType::Call26, RelocType::Jump26]),
            needed(
                "qsort_cmp",
                &[RelocType::AdrPrelPgHi21, RelocType::AddAbsLo12Nc],
            ),
            needed(
                "ext_data",
                &[RelocType::AdrPrelPgHi21, RelocType::Ldst64AbsLo12Nc],
            ),
            needed("ext_tls", &[RelocType::TlsieAdrGottprelPage21]),
            needed(
                "data",
                &[RelocType::AdrPrelPgHi21, RelocType::Ldst64AbsLo12Nc],
            ),
            needed("tls", &[RelocType::TlsieAdrGottprelPage21]),
            needed("f", &[RelocType::AdrPrelPgHi21, RelocType::AddAbsLo12Nc]),
        ],
        &defs,
    )
    .unwrap();
    let kinds = ok
        .iter()
        .map(|x| (x.name.as_str(), x.kind, x.size))
        .collect_vec();
    assert_eq!(
        kinds,
        [
            ("memcpy", ExternKind::Func, 0),
            ("qsort_cmp", ExternKind::Func, 0),
            ("ext_data", ExternKind::Object, 8),
            ("ext_tls", ExternKind::Tls, 8),
            ("data", ExternKind::Object, 256),
            ("tls", ExternKind::Tls, 24),
            ("f", ExternKind::Func, 12),
        ]
    );
    // Explicit `[[externs]]` override in `translation.toml`.
    let configured = [ConfiguredExtern {
        name: "custom_buf".into(),
        kind: ExternKind::Object,
        size: Some(64),
        align: 16,
    }];
    let custom = resolve_externs_with_config(
        &[needed(
            "custom_buf",
            &[RelocType::AdrPrelPgHi21, RelocType::AddAbsLo12Nc],
        )],
        &BTreeMap::new(),
        &configured,
    )
    .unwrap();
    assert_eq!(
        (custom[0].kind, custom[0].size, custom[0].align),
        (ExternKind::Object, 64, 16)
    );
    // Undersized `[[externs]]` entry (`size < max_access_end`) is rejected.
    let too_small = [ConfiguredExtern {
        name: "small_buf".into(),
        kind: ExternKind::Object,
        size: Some(4),
        align: 8,
    }];
    assert!(
        resolve_externs_with_config(
            &[needed(
                "small_buf",
                &[RelocType::AdrPrelPgHi21, RelocType::Ldst64AbsLo12Nc]
            )],
            &BTreeMap::new(),
            &too_small,
        )
        .is_err()
    );
    // Mixed branch + ldst or mixed tls + non-tls without definition; conflicting definitions; kind mismatch.
    assert!(
        resolve_externs(
            &[needed(
                "nodef",
                &[RelocType::Call26, RelocType::Ldst64AbsLo12Nc]
            )],
            &defs
        )
        .is_err()
    );
    assert!(resolve_externs(&[needed("bad", &[RelocType::Call26])], &defs).is_err());
    assert!(resolve_externs(&[needed("data", &[RelocType::Call26])], &defs).is_err());
    assert!(resolve_externs(&[needed("tls", &[RelocType::AdrGotPage])], &defs).is_err());
    assert!(resolve_externs(&[needed("f", &[RelocType::Ldst8AbsLo12Nc])], &defs).is_err());
}

fn sym(name: &str, kind: SymKind, bind: SymBind, sec: SymSection) -> ObjSymbol {
    ObjSymbol {
        name: name.into(),
        raw_name: format!("raw_{name}"),
        kind,
        bind,
        vis: 0,
        sec,
        value: 0,
        size: 4,
    }
}

fn tiny_object() -> ObjObject {
    let text = ObjSection {
        name: ".text.f".into(),
        sh_type: elf::SHT_PROGBITS,
        sh_flags: (elf::SHF_ALLOC | elf::SHF_EXECINSTR) as u64,
        addr: 0,
        align: 4,
        entsize: 0,
        size: 8,
        file_offset: 0x40,
        bytes: vec![0; 8],
        relocs: vec![ObjReloc {
            offset: 4,
            rtype: RelocType::Call26,
            sym: 2,
            addend: -4,
        }],
        is_rel: false,
        elf_index: 3,
    };
    let bss = ObjSection {
        name: ".bss.x".into(),
        sh_type: elf::SHT_NOBITS,
        sh_flags: (elf::SHF_ALLOC | elf::SHF_WRITE) as u64,
        addr: 0,
        align: 8,
        entsize: 0,
        size: 16,
        file_offset: 0,
        bytes: vec![],
        relocs: vec![],
        is_rel: false,
        elf_index: 4,
    };
    ObjObject {
        name: "demo".into(),
        sections: vec![text, bss],
        symbols: vec![
            sym("", SymKind::Notype, SymBind::Local, SymSection::Undef),
            sym("f", SymKind::Func, SymBind::Global, SymSection::Sec(0)),
            sym("g", SymKind::Notype, SymBind::Global, SymSection::Undef),
        ],
        groups: vec![],
        elf_bytes: vec![1, 2, 3],
    }
}

#[test]
fn needed_externs_and_collisions() {
    let o = tiny_object();
    let n = needed_externs(std::slice::from_ref(&o)).unwrap();
    assert_eq!(n.len(), 1);
    assert_eq!(n[0].raw_name, "raw_g");
    assert!(n[0].all_branch);
    assert!(check_name_collisions(&[o.clone(), o.clone()]).is_err());
    assert!(check_name_collisions(std::slice::from_ref(&o)).is_ok());
    let clash = ExternDecl {
        name: "f".into(),
        raw_name: "raw_f2".into(),
        kind: ExternKind::Func,
        size: 0,
        align: 1,
        origin: String::new(),
    };
    assert!(check_extern_collisions(std::slice::from_ref(&o), &[clash]).is_err());
}

#[test]
fn renders_object_literal() {
    let meta = ObjModuleMeta {
        obj_name: "demo".into(),
        obj_file: PathBuf::from("/out/G/DemoObj.lean"),
        namespace_prefix: "Ns".into(),
        title: "demo".into(),
        license_header: vec![],
    };
    let ex = Extraction {
        objects: vec![tiny_object()],
        externs: vec![ExternDecl {
            name: "g".into(),
            raw_name: "raw_g".into(),
            kind: ExternKind::Func,
            size: 0,
            align: 1,
            origin: "none".into(),
        }],
        provenance: vec![("K".into(), "v -/".into())],
    };
    let li = crate::untrusted_legacy_linker::link(&ex.objects, &ex.externs).unwrap();
    let ((obj_path, out), (code_bin_path, code_bytes), (data_bin_path, data_bytes)) =
        crate::untrusted_legacy_linker::emit_obj_lean_module(&meta, &ex, &li);
    assert_eq!(obj_path, PathBuf::from("/out/G/DemoObj.lean"));
    assert_eq!(code_bin_path, PathBuf::from("/out/G/DemoObj.code.bin"));
    assert_eq!(data_bin_path, PathBuf::from("/out/G/DemoObj.data.bin"));
    assert_eq!(code_bytes.len(), 12);
    assert_eq!(data_bytes.len(), 0);
    assert!(out.contains("* **K**: v - /"));
    assert!(out.contains("* `g` (func, 0 bytes): none"));
    assert!(out.contains("set_option maxHeartbeats 10000000"));
    assert!(out.contains("set_option maxRecDepth 2000000"));
    assert!(out.contains(
        "noncomputable def demoObj : Obj.ObjectInfo where\n  name := \"demo\"\n  fns := []"
    ));
    assert!(out.contains("noncomputable def demoImage : Obj.LinkedImage where"));
    assert!(out.contains("  code := include_bytes% \"DemoObj.code.bin\" 0 12\n"));
    assert!(out.contains("  dataOff := 0x1000\n"));
    assert!(out.contains("  data := include_bytes% \"DemoObj.data.bin\" 0 0\n  bss := 16\n"));
    assert!(out.contains("  gotOff := 0x1010\n"));
    assert!(out.contains("  symbols := [\n    (\"f\", 0)]"));
    assert!(out.contains("  objSymbols := [\n    (\"demo\", [(\"f\", 0)])]"));
    assert!(out.contains("  stubs := [\n    (\"g\", 8)]"));
    assert!(out.contains("  objects := [\n    demoObj]"));
    assert!(out.trim_end().ends_with("end Ns"));
}

#[test]
fn disambiguates_local_v0_global_and_multiversion_extern_collisions() {
    let mk_sym =
        |name: &str, raw_name: &str, kind: SymKind, bind: SymBind, sec: SymSection| -> ObjSymbol {
            ObjSymbol {
                name: name.into(),
                raw_name: raw_name.into(),
                kind,
                bind,
                vis: 0,
                sec,
                value: 0,
                size: 4,
            }
        };

    let fmt_demangled = "<codec::Message as core::fmt::Debug>::fmt";
    let v0_raw_0 = "_RNvXNvXs5_NtCs123_5codec7MessageNtNtCs456_4core3fmt5Debug3fmt";
    let v0_raw_1 = "_RNvXs_NvXs5_NtCs123_5codec7MessageNtNtCs456_4core3fmt5Debug3fmt";
    let v0_raw_2 = "_RNvXs0_NvXs5_NtCs123_5codec7MessageNtNtCs456_4core3fmt5Debug3fmt";

    let hb_demangled = "<hashbrown::raw::Fallibility>::capacity_overflow";
    let hb_raw_015 = "_RNvMNtCsf73KMPtv2x3_9hashbrown3rawNtB2_11Fallibility17capacity_overflow";
    let hb_raw_017 = "_RNvMNtCsjpftf2Xl72v_9hashbrown3rawNtB2_11Fallibility17capacity_overflow";

    let local_dup = "<alloc::raw_vec::RawVecInner>::finish_grow";

    let obj_a = ObjObject {
        name: "crate_a".into(),
        sections: vec![ObjSection {
            elf_index: 1,
            name: ".text".into(),
            sh_type: elf::SHT_PROGBITS,
            sh_flags: (elf::SHF_ALLOC | elf::SHF_EXECINSTR) as u64,
            addr: 0,
            align: 4,
            entsize: 0,
            size: 16,
            file_offset: 64,
            bytes: vec![0; 16],
            relocs: vec![
                ObjReloc {
                    offset: 0,
                    rtype: RelocType::Call26,
                    sym: 6,
                    addend: 0,
                },
                ObjReloc {
                    offset: 4,
                    rtype: RelocType::Call26,
                    sym: 7,
                    addend: 0,
                },
            ],
            is_rel: false,
        }],
        symbols: vec![
            mk_sym("", "", SymKind::Notype, SymBind::Local, SymSection::Undef),
            // Unique local symbol: must keep its original name unchanged.
            mk_sym(
                "unique_local_helper",
                "_RNvCs111_7crate_a19unique_local_helper",
                SymKind::Func,
                SymBind::Local,
                SymSection::Sec(0),
            ),
            // Intra- and cross-object colliding local symbols.
            mk_sym(
                local_dup,
                "_RNvMNtCs222_5alloc7raw_vecNtB2_11RawVecInner11finish_grow",
                SymKind::Func,
                SymBind::Local,
                SymSection::Sec(0),
            ),
            // Intra-crate v0 disambiguated globals.
            mk_sym(
                fmt_demangled,
                v0_raw_0,
                SymKind::Func,
                SymBind::Global,
                SymSection::Sec(0),
            ),
            mk_sym(
                fmt_demangled,
                v0_raw_1,
                SymKind::Func,
                SymBind::Global,
                SymSection::Sec(0),
            ),
            mk_sym(
                fmt_demangled,
                v0_raw_2,
                SymKind::Func,
                SymBind::Global,
                SymSection::Sec(0),
            ),
            // Multi-version crate externs referenced by relocations.
            mk_sym(
                hb_demangled,
                hb_raw_015,
                SymKind::Func,
                SymBind::Global,
                SymSection::Undef,
            ),
            mk_sym(
                hb_demangled,
                hb_raw_017,
                SymKind::Func,
                SymBind::Global,
                SymSection::Undef,
            ),
        ],
        groups: vec![],
        elf_bytes: vec![],
    };

    let obj_b = ObjObject {
        name: "crate_b".into(),
        sections: vec![ObjSection {
            elf_index: 1,
            name: ".text".into(),
            sh_type: elf::SHT_PROGBITS,
            sh_flags: (elf::SHF_ALLOC | elf::SHF_EXECINSTR) as u64,
            addr: 0,
            align: 4,
            entsize: 0,
            size: 8,
            file_offset: 64,
            bytes: vec![0; 8],
            relocs: vec![
                ObjReloc {
                    offset: 0,
                    rtype: RelocType::Call26,
                    sym: 2,
                    addend: 0,
                },
                ObjReloc {
                    offset: 4,
                    rtype: RelocType::Call26,
                    sym: 3,
                    addend: 0,
                },
            ],
            is_rel: false,
        }],
        symbols: vec![
            mk_sym("", "", SymKind::Notype, SymBind::Local, SymSection::Undef),
            // Cross-object local collision with `obj_a`.
            mk_sym(
                local_dup,
                "_RNvMNtCs222_5alloc7raw_vecNtB2_11RawVecInner11finish_grow",
                SymKind::Func,
                SymBind::Local,
                SymSection::Sec(0),
            ),
            // Undefined reference to the second v0 global defined in `obj_a`.
            mk_sym(
                fmt_demangled,
                v0_raw_1,
                SymKind::Func,
                SymBind::Global,
                SymSection::Undef,
            ),
            // Undefined reference to `hb_raw_017` (same raw_name as sym 7 in `obj_a`).
            mk_sym(
                hb_demangled,
                hb_raw_017,
                SymKind::Func,
                SymBind::Global,
                SymSection::Undef,
            ),
        ],
        groups: vec![],
        elf_bytes: vec![],
    };

    let mut objects = vec![obj_a, obj_b];
    disambiguate_symbol_names(&mut objects);
    check_name_collisions(&objects).unwrap();

    // Unique local symbol is untouched.
    assert_eq!(objects[0].symbols[1].name, "unique_local_helper");
    // Colliding local symbols are deterministically disambiguated.
    assert_eq!(objects[0].symbols[2].name, format!("{local_dup} [local#1]"));
    assert_eq!(objects[1].symbols[1].name, format!("{local_dup} [local#2]"));

    // v0 globals get distinct names, and `obj_b`'s undef ref to `v0_raw_1` matches `obj_a`'s def.
    assert_eq!(objects[0].symbols[3].name, fmt_demangled);
    assert_eq!(objects[0].symbols[4].name, format!("{fmt_demangled}#1"));
    assert_eq!(objects[0].symbols[5].name, format!("{fmt_demangled}#2"));
    assert_eq!(objects[1].symbols[2].name, format!("{fmt_demangled}#1"));

    // Multi-version externs get distinct names consistently across objects, and `v0_raw_1`
    // is recognized as defined in `obj_a` (so only the two hashbrown symbols are needed externs).
    let needed = needed_externs(&objects).unwrap();
    assert_eq!(needed.len(), 2);
    assert_eq!(needed[0].raw_name, hb_raw_015);
    assert_eq!(needed[0].name, hb_demangled);
    assert_eq!(needed[1].raw_name, hb_raw_017);
    assert_eq!(needed[1].name, format!("{hb_demangled}#1"));
    assert_eq!(objects[1].symbols[3].name, format!("{hb_demangled}#1"));

    let externs = resolve_externs(&needed, &BTreeMap::new()).unwrap();
    check_extern_collisions(&objects, &externs).unwrap();
}

#[test]
fn extracted_obj_emits_raw_names_sections_relocs_and_nobits() {
    use crate::trusted_common::{Extraction, ObjModuleMeta};

    let mut obj = ObjObject {
        name: "sample_crate".into(),
        sections: vec![
            ObjSection {
                name: ".text._ZN6sample3run17h111E".into(),
                sh_type: elf::SHT_PROGBITS,
                sh_flags: (elf::SHF_ALLOC | elf::SHF_EXECINSTR) as u64,
                addr: 0,
                align: 4,
                entsize: 0,
                size: 8,
                file_offset: 0,
                bytes: vec![0x00, 0x00, 0x00, 0x94, 0xc0, 0x03, 0x5f, 0xd6],
                relocs: vec![
                    ObjReloc {
                        offset: 0,
                        rtype: RelocType::Call26,
                        sym: 3,
                        addend: 0,
                    },
                    ObjReloc {
                        offset: 4,
                        rtype: RelocType::None,
                        sym: 0,
                        addend: 0,
                    },
                    ObjReloc {
                        offset: 4,
                        rtype: RelocType::Other(999),
                        sym: 3,
                        addend: -4,
                    },
                ],
                is_rel: false,
                elf_index: 1,
            },
            ObjSection {
                name: ".data.rel.ro..Lanon.1".into(),
                sh_type: elf::SHT_PROGBITS,
                sh_flags: (elf::SHF_ALLOC | elf::SHF_WRITE) as u64,
                addr: 0,
                align: 8,
                entsize: 0,
                size: 8,
                file_offset: 0,
                bytes: vec![1, 2, 3, 4, 5, 6, 7, 8],
                relocs: vec![],
                is_rel: false,
                elf_index: 2,
            },
            ObjSection {
                name: ".bss..LSTORAGE".into(),
                sh_type: elf::SHT_NOBITS,
                sh_flags: (elf::SHF_ALLOC | elf::SHF_WRITE) as u64,
                addr: 0,
                align: 16,
                entsize: 0,
                size: 32,
                file_offset: 0,
                bytes: vec![],
                relocs: vec![],
                is_rel: false,
                elf_index: 3,
            },
        ],
        symbols: vec![
            ObjSymbol {
                name: String::new(),
                raw_name: String::new(),
                kind: SymKind::Notype,
                bind: SymBind::Local,
                vis: 0,
                sec: SymSection::Undef,
                value: 0,
                size: 0,
            },
            ObjSymbol {
                name: "sample::run".into(),
                raw_name: "_ZN6sample3run17h111E".into(),
                kind: SymKind::Func,
                bind: SymBind::Global,
                vis: 0,
                sec: SymSection::Sec(0),
                value: 0,
                size: 8,
            },
            ObjSymbol {
                name: "sample::STORAGE.0".into(),
                raw_name: "_ZN6sample7STORAGE17h222E.0".into(),
                kind: SymKind::Object,
                bind: SymBind::Local,
                vis: 0,
                sec: SymSection::Sec(2),
                value: 0,
                size: 32,
            },
            ObjSymbol {
                name: "memcpy".into(),
                raw_name: "memcpy".into(),
                kind: SymKind::Notype,
                bind: SymBind::Weak,
                vis: 0,
                sec: SymSection::Undef,
                value: 0,
                size: 0,
            },
            ObjSymbol {
                name: "sample.rs".into(),
                raw_name: "sample.rs".into(),
                kind: SymKind::File,
                bind: SymBind::Local,
                vis: 0,
                sec: SymSection::Abs,
                value: 0,
                size: 0,
            },
        ],
        groups: vec![],
        elf_bytes: vec![],
    };
    let mut objs = vec![obj.clone()];
    disambiguate_symbol_names(&mut objs);
    obj = objs.pop().unwrap();
    let ex = Extraction {
        objects: vec![obj],
        externs: vec![],
        provenance: vec![],
    };
    let meta = ObjModuleMeta {
        obj_name: "sample".into(),
        obj_file: std::path::PathBuf::from("CaseStudies/Sample/Generated/SampleObj.lean"),
        namespace_prefix: "CaseStudies.Sample".into(),
        title: "`sample`".into(),
        license_header: vec![],
    };
    let ((lean_path, lean_src), (bin_path, bin_bytes)) = emit_extracted_obj_lean_module(&meta, &ex);
    assert_eq!(
        lean_path,
        std::path::PathBuf::from("CaseStudies/Sample/Generated/SampleExtractedObj.lean")
    );
    assert_eq!(
        bin_path,
        std::path::PathBuf::from("CaseStudies/Sample/Generated/SampleExtractedObj.bin")
    );
    assert_eq!(bin_bytes.len(), 16);
    assert_eq!(
        &bin_bytes[..8],
        &[0x00, 0x00, 0x00, 0x94, 0xc0, 0x03, 0x5f, 0xd6]
    );
    assert_eq!(&bin_bytes[8..16], &[1, 2, 3, 4, 5, 6, 7, 8]);
    assert!(lean_src.contains("public import Arm64.Trusted.Object.Labels"));
    assert!(lean_src.contains("public import Arm64.Trusted.Surface.IncludeBytes"));
    assert!(lean_src.contains("include_bytes% \"SampleExtractedObj.bin\" 0 8"));
    assert!(lean_src.contains("include_bytes% \"SampleExtractedObj.bin\" 8 8"));
    assert!(lean_src.contains("readOnly := false"));
    assert!(lean_src.contains(
        "bytes := [], size := 32, align := 16, isExec := false, readOnly := false, isNobits := true"
    ));
    assert!(lean_src.contains("{ off := 0x0, kind := some .call26, symIdx := 3 }"));
    assert!(lean_src.contains("{ off := 0x4, kind := none, symIdx := 3, addend := -4 }"));
    assert!(lean_src.contains(
        "rawName := \"_ZN6sample7STORAGE17h222E.0\", name := \"sample::STORAGE.0\", sec := .sec 2, value := 0x0, size := 32, kind := .object, bind := .local"
    ));
    assert!(lean_src.contains(
        "rawName := \"memcpy\", name := \"memcpy\", sec := .undef, value := 0x0, size := 0, kind := .other, bind := .weak"
    ));
    assert!(lean_src.contains("rawName := \"sample.rs\", name := \"sample.rs\", sec := .other"));
    assert!(lean_src.contains("  groups := []\n"));
    assert!(
        lean_src
            .contains("def sampleExtractedObjs : List Obj.ExtractedObj := [sampleExtractedObj0]")
    );
}

#[test]
fn extracted_obj_emitter_has_zero_legacy_linker_edges() {
    let manifest_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let emitter_src =
        std::fs::read_to_string(manifest_dir.join("src/trusted_extractor/extracted_obj.rs"))
            .unwrap();
    for forbidden in [
        "untrusted_legacy_linker",
        "trusted_linker",
        "legacy_linked_image",
        "link_with_layout",
    ] {
        assert!(
            !emitter_src.contains(forbidden),
            "extracted_obj.rs must not reference `{forbidden}` anywhere"
        );
    }
    let common_src =
        std::fs::read_to_string(manifest_dir.join("src/trusted_common/mod.rs")).unwrap();
    for (idx, line) in common_src.lines().enumerate() {
        let code = line.split("//").next().unwrap_or("");
        for forbidden in [
            "untrusted_legacy_linker",
            "trusted_linker",
            "legacy_linked_image",
            "link_with_layout",
        ] {
            assert!(
                !code.contains(forbidden),
                "trusted_common/mod.rs:{} references `{forbidden}`: {line}",
                idx + 1
            );
        }
    }
}

// ---------------------------------------------------------------------------
// COMDAT section groups (`SHT_GROUP`)
// ---------------------------------------------------------------------------

/// Relocatable AArch64 ELF with a plain `.text` and one `.text.<sig>` section per entry of
/// `comdats`, each in its own `GRP_COMDAT` group whose signature is a weak function `<sig>`
/// (or the section symbol, with an empty `.strtab` name, when `<sig>` is empty).
fn comdat_elf(comdats: &[&str]) -> Vec<u8> {
    use object::write::{Comdat, Object, Symbol, SymbolSection};
    use object::{
        Architecture, BinaryFormat, ComdatKind, Endianness, SectionKind, SymbolFlags, SymbolKind,
        SymbolScope,
    };
    let mut obj = Object::new(BinaryFormat::Elf, Architecture::Aarch64, Endianness::Little);
    let text = obj.add_section(Vec::new(), b".text".to_vec(), SectionKind::Text);
    obj.append_section_data(text, &[0xc0, 0x03, 0x5f, 0xd6], 4);
    for sig in comdats {
        let name = format!(".text.{sig}");
        let sec = obj.add_section(Vec::new(), name.into_bytes(), SectionKind::Text);
        obj.append_section_data(sec, &[0xc0, 0x03, 0x5f, 0xd6], 4);
        let symbol = if sig.is_empty() {
            obj.section_symbol(sec)
        } else {
            obj.add_symbol(Symbol {
                name: sig.as_bytes().to_vec(),
                value: 0,
                size: 4,
                kind: SymbolKind::Text,
                scope: SymbolScope::Linkage,
                weak: true,
                section: SymbolSection::Section(sec),
                flags: SymbolFlags::None,
            })
        };
        obj.add_comdat(Comdat { kind: ComdatKind::Any, symbol, sections: vec![sec] });
    }
    obj.write().unwrap()
}

/// File offsets of the `SHT_GROUP` sections' data in `elf`, in section header order.
fn group_data_offsets(elf: &[u8]) -> Vec<usize> {
    let e = parse_elf_rel(elf).unwrap();
    e.sections
        .iter()
        .filter(|sh| sh.sh_type(e.endian) == elf::SHT_GROUP)
        .map(|sh| sh.sh_offset(e.endian) as usize)
        .collect()
}

fn sec_index(o: &ObjObject, name: &str) -> usize {
    o.sections.iter().position(|s| s.name == name).unwrap()
}

#[test]
fn comdat_groups_are_parsed_and_emitted() {
    let o = parse_object("c", comdat_elf(&["foo", "bar"])).unwrap();
    let foo = sec_index(&o, ".text.foo");
    let bar = sec_index(&o, ".text.bar");
    assert_eq!(
        o.groups,
        vec![
            ComdatGroup { signature: "foo".into(), is_comdat: true, sections: vec![foo] },
            ComdatGroup { signature: "bar".into(), is_comdat: true, sections: vec![bar] },
        ]
    );
    let ex = Extraction { objects: vec![o], externs: vec![], provenance: vec![] };
    let meta = ObjModuleMeta {
        obj_name: "c".into(),
        obj_file: PathBuf::from("CaseStudies/C/Generated/CObj.lean"),
        namespace_prefix: "CaseStudies.C".into(),
        title: "`c`".into(),
        license_header: vec![],
    };
    let (src, _) = render_extracted_obj_module(&meta, "CExtractedObj.bin", &ex);
    assert!(src.contains(&format!(
        "  groups := [\n    {{ signature := \"foo\", members := [{foo}] }},\n    \
         {{ signature := \"bar\", members := [{bar}] }}]\n"
    )));
}

#[test]
fn objects_without_groups_emit_empty_groups() {
    let o = parse_object("c", comdat_elf(&[])).unwrap();
    assert!(o.groups.is_empty());
    let ex = Extraction { objects: vec![o], externs: vec![], provenance: vec![] };
    let meta = ObjModuleMeta {
        obj_name: "c".into(),
        obj_file: PathBuf::from("CObj.lean"),
        namespace_prefix: "C".into(),
        title: "`c`".into(),
        license_header: vec![],
    };
    let (src, _) = render_extracted_obj_module(&meta, "CExtractedObj.bin", &ex);
    assert!(src.contains("  groups := []\n"));
}

#[test]
fn trim_keeps_comdat_signature_of_dropped_group() {
    let elf = comdat_elf(&["foo"]);
    let text = {
        let e = parse_elf_rel(&elf).unwrap();
        e.sections
            .enumerate()
            .find(|(_, sh)| section_name(&e, sh).unwrap() == ".text")
            .unwrap()
            .0
            .0
    };
    let trim = Trim { keep: BTreeSet::from([text]), local_suffix: String::new() };
    let o = parse_object_with("c", elf, Some(&trim)).unwrap();
    assert_eq!(o.sections.len(), 1);
    assert_eq!(
        o.groups,
        vec![ComdatGroup { signature: "foo".into(), is_comdat: true, sections: vec![] }]
    );
}

#[test]
fn rejects_unsupported_group_flags() {
    let mut elf = comdat_elf(&["foo"]);
    let off = group_data_offsets(&elf)[0];
    elf[off..off + 4].copy_from_slice(&2u32.to_le_bytes());
    let err = parse_object("c", elf).unwrap_err().to_string();
    assert!(err.contains("unsupported flags"), "{err}");
}

#[test]
fn accepts_non_comdat_group_without_emitting_it() {
    let mut elf = comdat_elf(&["foo"]);
    let off = group_data_offsets(&elf)[0];
    elf[off..off + 4].copy_from_slice(&0u32.to_le_bytes());
    let o = parse_object("c", elf).unwrap();
    assert_eq!(o.groups.len(), 1);
    assert!(!o.groups[0].is_comdat);
    let ex = Extraction { objects: vec![o], externs: vec![], provenance: vec![] };
    let meta = ObjModuleMeta {
        obj_name: "c".into(),
        obj_file: PathBuf::from("CObj.lean"),
        namespace_prefix: "C".into(),
        title: "`c`".into(),
        license_header: vec![],
    };
    let (src, _) = render_extracted_obj_module(&meta, "CExtractedObj.bin", &ex);
    assert!(src.contains("  groups := []\n"));
}

#[test]
fn comdat_group_with_empty_signature_is_kept_as_is() {
    // `lld` keys COMDAT dedup on the raw signature name, including `""`.
    let o = parse_object("c", comdat_elf(&[""])).unwrap();
    assert_eq!(o.groups.len(), 1);
    assert_eq!(o.groups[0].signature, "");
    assert!(o.groups[0].is_comdat);
}

#[test]
fn rejects_section_in_two_groups() {
    let mut elf = comdat_elf(&["foo", "bar"]);
    let offs = group_data_offsets(&elf);
    let first_member: [u8; 4] = elf[offs[0] + 4..offs[0] + 8].try_into().unwrap();
    elf[offs[1] + 4..offs[1] + 8].copy_from_slice(&first_member);
    let err = parse_object("c", elf).unwrap_err().to_string();
    assert!(err.contains("more than one SHT_GROUP"), "{err}");
}

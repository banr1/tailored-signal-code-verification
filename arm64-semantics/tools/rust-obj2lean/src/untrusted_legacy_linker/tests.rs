// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Unit tests for [`super`] (`untrusted_legacy_linker`) (`Role::Test`, `[TEST ONLY]`; not part of the TCB).
//!
//! Covers agreement with `ld.lld` on hand-written assembly, relocation-free function recording,
//! rejection of overlapping relocations / undefined symbols / TLS definitions, GOT entry
//! deduplication, and TLS initial-exec GOT slots.

use super::*;
use crate::trusted_common::{ObjReloc, ObjSection, ObjSymbol};
use object::elf;

fn words(ws: &[u32]) -> Vec<u8> {
    ws.iter().flat_map(|w| w.to_le_bytes()).collect()
}

fn sec(name: &str, kind: SecKind, align: u64, bytes: Vec<u8>, relocs: Vec<ObjReloc>) -> ObjSection {
    let (sh_type, sh_flags) = match kind {
        SecKind::Text => (
            elf::SHT_PROGBITS,
            (elf::SHF_ALLOC | elf::SHF_EXECINSTR) as u64,
        ),
        SecKind::Rodata => (elf::SHT_PROGBITS, elf::SHF_ALLOC as u64),
        SecKind::Data => (elf::SHT_PROGBITS, (elf::SHF_ALLOC | elf::SHF_WRITE) as u64),
        SecKind::Bss => (elf::SHT_NOBITS, (elf::SHF_ALLOC | elf::SHF_WRITE) as u64),
        SecKind::Tdata | SecKind::Tbss => unreachable!(),
    };
    let size = if kind == SecKind::Bss {
        16
    } else {
        bytes.len() as u64
    };
    ObjSection {
        name: name.into(),
        sh_type,
        sh_flags,
        addr: 0,
        align,
        entsize: 0,
        size,
        file_offset: 0,
        bytes,
        relocs,
        is_rel: false,
        elf_index: 0,
    }
}

fn sym(name: &str, kind: SymKind, bind: SymBind, sec: SymSection) -> ObjSymbol {
    ObjSymbol {
        name: name.into(),
        raw_name: name.into(),
        kind,
        bind,
        vis: 0,
        sec,
        value: 0,
        size: 0,
    }
}

fn rel(offset: u64, rtype: RelocType, sym: usize, addend: i64) -> ObjReloc {
    ObjReloc {
        offset,
        rtype,
        sym,
        addend,
    }
}

fn ext(name: &str, kind: ExternKind, size: u64, align: u64) -> ExternDecl {
    ExternDecl {
        name: name.into(),
        raw_name: name.into(),
        kind,
        size,
        align,
        origin: String::new(),
    }
}

/// The `handAsm` object of `Arm64/Testing/ObjectLoad.lean`, whose expected output comes from
/// `ld.lld --no-relax`.
fn hand_asm() -> (ObjObject, Vec<ExternDecl>) {
    use RelocType::*;
    use SymBind::*;
    use SymKind::*;
    let o = ObjObject {
        name: "t.o".into(),
        sections: vec![
            sec(
                ".text",
                SecKind::Text,
                4,
                words(&[0x94000000, 0x94000000, 0x90000000, 0x91000000, 0xd65f03c0]),
                vec![
                    rel(0, Call26, 4, 0),
                    rel(4, Call26, 11, 0),
                    rel(8, AdrPrelPgHi21, 6, 0),
                    rel(12, AddAbsLo12Nc, 6, 0),
                ],
            ),
            sec(".text.g", SecKind::Text, 4, words(&[0xd65f03c0]), vec![]),
            sec(
                ".rodata",
                SecKind::Rodata,
                1,
                vec![0x68, 0x69, 0, 0, 0, 0, 0, 0],
                vec![],
            ),
            sec(
                ".data",
                SecKind::Data,
                8,
                vec![0; 8],
                vec![rel(0, Abs64, 6, 1)],
            ),
        ],
        symbols: vec![
            sym("", Notype, Local, SymSection::Undef),
            sym("$x", Notype, Local, SymSection::Sec(0)),
            sym("g", Notype, Local, SymSection::Sec(1)),
            sym("msg", Notype, Local, SymSection::Sec(2)),
            sym(".text.g", Section, Local, SymSection::Sec(1)),
            sym("$x", Notype, Local, SymSection::Sec(1)),
            sym(".rodata", Section, Local, SymSection::Sec(2)),
            sym("$d", Notype, Local, SymSection::Sec(2)),
            sym("ptr", Notype, Local, SymSection::Sec(3)),
            sym("$d", Notype, Local, SymSection::Sec(3)),
            ObjSymbol {
                size: 20,
                ..sym("f", Func, Global, SymSection::Sec(0))
            },
            sym("ext", Notype, Global, SymSection::Undef),
        ],
        groups: vec![],
        elf_bytes: vec![],
    };
    (o, vec![ext("ext", ExternKind::Func, 0, 4)])
}

#[test]
fn hand_asm_matches_ld_lld() {
    let (o, externs) = hand_asm();
    let li = link(std::slice::from_ref(&o), &externs).unwrap();
    assert_eq!(
        li.code,
        words(&[
            0x94000005, 0x94000005, 0xb0000000, 0x91000000, 0xd65f03c0, 0xd65f03c0, 0
        ])
    );
    assert_eq!(li.symbols, vec![("f".to_string(), 0)]);
    assert_eq!(li.stubs, vec![("ext".to_string(), 0x18)]);
    assert_eq!(li.data_off, 0x1000);
    assert_eq!(li.ro_data, vec![(0x1000, 8)]);
    // `ptr = msg + 1`, written by the loader.
    assert_eq!(
        li.relocs,
        vec![DataReloc {
            off: 8,
            width: 8,
            target: 0x1001
        }]
    );
    assert_eq!(li.got_off, 0x1010);
    // `f` has relocations, so it is not recorded.
    assert_eq!(li.objects[0].fns, vec![]);
}

#[test]
fn reloc_free_functions_are_recorded() {
    use SymBind::*;
    use SymKind::*;
    let o = ObjObject {
        name: "a".into(),
        sections: vec![
            sec(
                ".text.f",
                SecKind::Text,
                4,
                words(&[0xd503201f, 0xd65f03c0]),
                vec![],
            ),
            sec(".bss", SecKind::Bss, 8, vec![], vec![]),
        ],
        symbols: vec![
            sym("", Notype, Local, SymSection::Undef),
            ObjSymbol {
                size: 8,
                ..sym("f", Func, Global, SymSection::Sec(0))
            },
            ObjSymbol {
                size: 16,
                ..sym("buf", Object, Global, SymSection::Sec(1))
            },
        ],
        groups: vec![],
        elf_bytes: vec![],
    };
    let li = link(&[o], &[]).unwrap();
    assert_eq!(
        li.objects[0].fns,
        vec![FnInfo {
            name: "f".into(),
            off: 0,
            size: 8
        }]
    );
    assert_eq!(li.data, Vec::<u8>::new());
    assert_eq!(li.bss, 16);
    assert_eq!(
        li.symbols,
        vec![("buf".to_string(), 0x1000), ("f".to_string(), 0)]
    );
    assert_eq!(li.got_off, 0x1010);
}

#[test]
fn overlapping_relocations_are_rejected() {
    use SymBind::*;
    use SymKind::*;
    let o = ObjObject {
        name: "a".into(),
        sections: vec![sec(
            ".data",
            SecKind::Data,
            8,
            vec![0; 16],
            vec![
                rel(0, RelocType::Abs64, 1, 0),
                rel(4, RelocType::Abs64, 1, 0),
            ],
        )],
        symbols: vec![
            sym("", Notype, Local, SymSection::Undef),
            sym("x", Object, Local, SymSection::Sec(0)),
        ],
        groups: vec![],
        elf_bytes: vec![],
    };
    assert!(link(&[o], &[]).is_err());
}

#[test]
fn undefined_symbol_is_rejected() {
    let (o, _) = hand_asm();
    assert!(link(&[o], &[]).is_err());
}

#[test]
fn got_entries_are_deduplicated_in_order() {
    use RelocType::*;
    let o = ObjObject {
        name: "g.o".into(),
        sections: vec![sec(
            ".text",
            SecKind::Text,
            4,
            words(&[0x90000000, 0xf9400000, 0x90000000, 0xf9400000]),
            vec![
                rel(0, AdrGotPage, 1, 0),
                rel(4, Ld64GotLo12Nc, 1, 0),
                rel(8, AdrGotPage, 1, 0),
                rel(12, Ld64GotLo12Nc, 1, 0),
            ],
        )],
        symbols: vec![
            sym("", SymKind::Notype, SymBind::Local, SymSection::Undef),
            sym("x", SymKind::Notype, SymBind::Global, SymSection::Undef),
        ],
        groups: vec![],
        elf_bytes: vec![],
    };
    let li = link(&[o], &[ext("x", ExternKind::Object, 8, 8)]).unwrap();
    assert_eq!(li.got, vec![GotEntry::Addr(0x1000)]);
    assert_eq!(li.got_off, 0x1008);
    // `adrp x0, 0x1000` from 0 (immlo = 1 << 29 is page 1) and `ldr x0, [x0, #8]`.
    assert_eq!(li.code[0..8], words(&[0xb0000000, 0xf9400400])[..]);
    assert_eq!(li.code[8..16], li.code[0..8]);
}

/// An object loading the TP offset of extern TLS variable `t` (initial-exec) and the
/// address of `x` from the GOT.
fn tls_ie_obj(t_kind: SymKind) -> ObjObject {
    use RelocType::*;
    ObjObject {
        name: "t.o".into(),
        sections: vec![sec(
            ".text",
            SecKind::Text,
            4,
            words(&[0x90000000, 0xf9400000, 0x90000000, 0xf9400000]),
            vec![
                rel(0, TlsieAdrGottprelPage21, 1, 0),
                rel(4, TlsieLd64GottprelLo12Nc, 1, 0),
                rel(8, AdrGotPage, 2, 0),
                rel(12, Ld64GotLo12Nc, 2, 0),
            ],
        )],
        symbols: vec![
            sym("", SymKind::Notype, SymBind::Local, SymSection::Undef),
            sym("t", t_kind, SymBind::Global, SymSection::Undef),
            sym("x", SymKind::Notype, SymBind::Global, SymSection::Undef),
        ],
        groups: vec![],
        elf_bytes: vec![],
    }
}

#[test]
fn tls_ie_got_slots_hold_tp_offsets() {
    let externs = [
        ext("u", ExternKind::Tls, 4, 4),
        ext("t", ExternKind::Tls, 8, 32),
        ext("x", ExternKind::Object, 8, 8),
    ];
    let li = link(&[tls_ie_obj(SymKind::Tls)], &externs).unwrap();
    // TLS block alignment 32: the block starts at TP offset 32; `u` at 32, `t` at 64.
    assert_eq!(
        li.extern_tls,
        vec![("u".to_string(), 32), ("t".to_string(), 64)]
    );
    assert_eq!(li.got, vec![GotEntry::TpOff(64), GotEntry::Addr(0x1000)]);
    assert_eq!(li.got_off, 0x1008);
    // `adrp x0, 0x1000; ldr x0, [x0, #8]` then `adrp x0, 0x1000; ldr x0, [x0, #16]`.
    assert_eq!(
        li.code[0..16],
        words(&[0xb0000000, 0xf9400400, 0xb0000000, 0xf9400800])[..]
    );
    assert_eq!(GotEntry::TpOff(64).value(0x40_0000), 64);
    assert_eq!(GotEntry::Addr(0x1000).value(0x40_0000), 0x40_1000);
}

#[test]
fn tls_ie_against_non_tls_symbol_is_rejected() {
    let externs = [
        ext("t", ExternKind::Object, 8, 8),
        ext("x", ExternKind::Object, 8, 8),
    ];
    let err = link(&[tls_ie_obj(SymKind::Notype)], &externs).unwrap_err();
    assert!(err.to_string().contains("unsupported (tls)"), "{err}");
}

#[test]
fn tls_definitions_are_rejected() {
    let mut o = tls_ie_obj(SymKind::Tls);
    o.symbols[1].sec = SymSection::Sec(0);
    let err = link(&[o], &[ext("x", ExternKind::Object, 8, 8)]).unwrap_err();
    assert!(err.to_string().contains("unsupported (tls)"), "{err}");
}

#[test]
fn reloc_fns_and_data_syms_are_recorded_and_rendered() {
    use RelocType::*;
    use SymBind::*;
    use SymKind::*;
    let o = ObjObject {
        name: "m".into(),
        sections: vec![
            sec(
                ".text",
                SecKind::Text,
                4,
                words(&[0x90000000, 0x91000000, 0x94000000, 0xd65f03c0]),
                vec![
                    rel(0, AdrPrelPgHi21, 2, 8),
                    rel(4, AddAbsLo12Nc, 2, 8),
                    rel(8, Call26, 4, 0),
                ],
            ),
            sec(".rodata", SecKind::Rodata, 8, vec![0; 16], vec![rel(0, Abs64, 4, 0)]),
            sec(".bss", SecKind::Bss, 8, vec![], vec![]),
        ],
        symbols: vec![
            sym("", Notype, Local, SymSection::Undef),
            ObjSymbol {
                size: 16,
                ..sym("f", Func, Global, SymSection::Sec(0))
            },
            ObjSymbol {
                size: 16,
                ..sym("tbl [m]", Object, Local, SymSection::Sec(1))
            },
            ObjSymbol {
                size: 16,
                ..sym("err_buf [m]", Object, Local, SymSection::Sec(2))
            },
            sym("ext_fn", Notype, Global, SymSection::Undef),
        ],
        groups: vec![],
        elf_bytes: vec![],
    };
    let li = link(&[o], &[ext("ext_fn", ExternKind::Func, 0, 4)]).unwrap();
    assert_eq!(
        li.objects[0].reloc_fns,
        vec![SymCodeInfo {
            sym: "f".into(),
            off: 0,
            size: 16,
            code: li.code[0..16].to_vec(),
            words: vec![
                u32::from_le_bytes(li.code[0..4].try_into().unwrap()),
                u32::from_le_bytes(li.code[4..8].try_into().unwrap()),
                u32::from_le_bytes(li.code[8..12].try_into().unwrap()),
                u32::from_le_bytes(li.code[12..16].try_into().unwrap()),
            ],
            relocs: vec![
                RelocEntry {
                    off: 0,
                    kind: RelocKind::AdrpHi21,
                    sym: "tbl [m]".into(),
                    addend: 8,
                    local_sym: true,
                },
                RelocEntry {
                    off: 4,
                    kind: RelocKind::AddLo12,
                    sym: "tbl [m]".into(),
                    addend: 8,
                    local_sym: true,
                },
                RelocEntry {
                    off: 8,
                    kind: RelocKind::Call26,
                    sym: "ext_fn".into(),
                    addend: 0,
                    local_sym: false,
                },
            ],
        }]
    );
    assert_eq!(
        li.objects[0].data_syms,
        vec![
            SymDataInfo {
                sym: "tbl [m]".into(),
                align: 8,
                read_only: true,
                off: 0x1000,
                bytes_len: 16,
                zero_tail: 0,
                relocs: vec![RelocEntry {
                    off: 0,
                    kind: RelocKind::Abs64,
                    sym: "ext_fn".into(),
                    addend: 0,
                    local_sym: false,
                }],
            },
            SymDataInfo {
                sym: "err_buf [m]".into(),
                align: 8,
                read_only: false,
                off: 0x1010,
                bytes_len: 0,
                zero_tail: 16,
                relocs: vec![],
            },
        ]
    );
    let meta = ObjModuleMeta {
        obj_name: "demo".into(),
        obj_file: "Examples/Generated/DemoObj.lean".into(),
        namespace_prefix: "Examples".into(),
        title: "demo".into(),
        license_header: vec![],
    };
    let rendered = render_image(&meta, &li).join("\n");
    assert!(rendered.contains("relocFns := ["), "{rendered}");
    assert!(rendered.contains("dataSyms := ["), "{rendered}");
    assert!(
        rendered.contains("{ off := 0, kind := .adrpHi21, sym := \"tbl [m]\", addend := 8, localSym := true }"),
        "{rendered}"
    );
}

#[test]
fn link_with_perturb_shifts_layout_while_preserving_reloc_fn_words_and_relocs() {
    use RelocType::*;
    use SymBind::*;
    use SymKind::*;
    let o = ObjObject {
        name: "m".into(),
        sections: vec![
            sec(
                ".text.f",
                SecKind::Text,
                4,
                words(&[0x90000000, 0x91000000, 0x94000000, 0xd65f03c0]),
                vec![
                    rel(0, AdrPrelPgHi21, 3, 8),
                    rel(4, AddAbsLo12Nc, 3, 8),
                    rel(8, Call26, 5, 0),
                ],
            ),
            sec(".text.g", SecKind::Text, 4, words(&[0x0b010000, 0xd65f03c0]), vec![]),
            sec(".rodata", SecKind::Rodata, 8, vec![0xaa; 16], vec![rel(0, Abs64, 1, 0)]),
            sec(".bss", SecKind::Bss, 8, vec![], vec![]),
        ],
        symbols: vec![
            sym("", Notype, Local, SymSection::Undef),
            ObjSymbol {
                size: 16,
                ..sym("f", Func, Global, SymSection::Sec(0))
            },
            ObjSymbol {
                size: 8,
                ..sym("g", Func, Global, SymSection::Sec(1))
            },
            ObjSymbol {
                size: 16,
                ..sym("tbl [m]", Object, Local, SymSection::Sec(2))
            },
            ObjSymbol {
                size: 16,
                ..sym("err_buf [m]", Object, Local, SymSection::Sec(3))
            },
            sym("ext_fn", Notype, Global, SymSection::Undef),
        ],
        groups: vec![],
        elf_bytes: vec![],
    };
    let externs = [ext("ext_fn", ExternKind::Func, 0, 4)];

    let err = link_with_perturb(std::slice::from_ref(&o), &externs, 6)
        .expect_err("non-multiple-of-4 perturb_bytes must be rejected");
    assert!(err.to_string().contains("multiple of 4"), "{err}");

    let unperturbed = link(std::slice::from_ref(&o), &externs).unwrap();
    let base = link_with_perturb(std::slice::from_ref(&o), &externs, 0).unwrap();

    // 0. Output is byte-identical when perturbation is off (`perturb_bytes == 0` vs `link`).
    assert_eq!(base.code, unperturbed.code);
    assert_eq!(base.data_off, unperturbed.data_off);
    assert_eq!(base.data, unperturbed.data);
    assert_eq!(base.bss, unperturbed.bss);
    assert_eq!(base.ro_data, unperturbed.ro_data);
    assert_eq!(base.extern_data, unperturbed.extern_data);
    assert_eq!(base.got_off, unperturbed.got_off);
    assert_eq!(base.got, unperturbed.got);
    assert_eq!(base.relocs, unperturbed.relocs);
    assert_eq!(base.symbols, unperturbed.symbols);
    assert_eq!(base.obj_symbols, unperturbed.obj_symbols);
    assert_eq!(base.stubs, unperturbed.stubs);
    assert_eq!(base.objects, unperturbed.objects);
    let meta = ObjModuleMeta {
        obj_name: "demo".into(),
        obj_file: "Examples/Generated/DemoObj.lean".into(),
        namespace_prefix: "Examples".into(),
        title: "demo".into(),
        license_header: vec![],
    };
    assert_eq!(
        render_image(&meta, &base),
        render_image(&meta, &unperturbed)
    );

    for perturb in [64u64, 4096u64] {
        let pert = link_with_perturb(std::slice::from_ref(&o), &externs, perturb).unwrap();

        // 1. Leading padding in `.text` is filled with ARM64 NOP words (`0xd503201f`).
        for chunk in pert.code[..perturb as usize].chunks_exact(4) {
            assert_eq!(u32::from_le_bytes(chunk.try_into().unwrap()), ARM64_NOP_WORD);
        }

        // 2. Function and data symbol offsets shift by `perturb`.
        assert_eq!(pert.objects[0].fns[0].off, base.objects[0].fns[0].off + perturb);
        assert_eq!(
            pert.objects[0].reloc_fns[0].off,
            base.objects[0].reloc_fns[0].off + perturb
        );
        assert_eq!(
            pert.objects[0].data_syms[0].off,
            base.objects[0].data_syms[0].off + perturb
        );
        assert_eq!(
            pert.objects[0].data_syms[1].off,
            base.objects[0].data_syms[1].off + perturb
        );
        assert_eq!(pert.ro_data[0].0, base.ro_data[0].0 + perturb);
        assert_eq!(pert.data_off % PAGE_SIZE, 0, "data_off must stay page-aligned");

        // 3. `reloc_fns` relative `code`, `words`, `size`, and function-relative `relocs`
        //    are completely invariant under layout perturbation.
        assert_eq!(pert.objects[0].reloc_fns[0].sym, base.objects[0].reloc_fns[0].sym);
        assert_eq!(pert.objects[0].reloc_fns[0].size, base.objects[0].reloc_fns[0].size);
        assert_eq!(pert.objects[0].reloc_fns[0].code, base.objects[0].reloc_fns[0].code);
        assert_eq!(pert.objects[0].reloc_fns[0].words, base.objects[0].reloc_fns[0].words);
        assert_eq!(pert.objects[0].reloc_fns[0].relocs, base.objects[0].reloc_fns[0].relocs);

        // 4. Abs64 pointer in `.rodata` resolves to the shifted function address `f`.
        let tbl_rel = pert.objects[0].data_syms[0].off - pert.data_off;
        assert_eq!(pert.relocs[0].off, tbl_rel);
        assert_eq!(pert.relocs[0].target, pert.objects[0].reloc_fns[0].off);
    }
}

fn assert_linked_image_eq(a: &LinkedImage, b: &LinkedImage) {
    assert_eq!(a.code, b.code);
    assert_eq!(a.data_off, b.data_off);
    assert_eq!(a.data, b.data);
    assert_eq!(a.bss, b.bss);
    assert_eq!(a.ro_data, b.ro_data);
    assert_eq!(a.extern_data, b.extern_data);
    assert_eq!(a.got_off, b.got_off);
    assert_eq!(a.got, b.got);
    assert_eq!(a.relocs, b.relocs);
    assert_eq!(a.symbols, b.symbols);
    assert_eq!(a.obj_symbols, b.obj_symbols);
    assert_eq!(a.stubs, b.stubs);
    assert_eq!(a.objects, b.objects);
    assert_eq!(a.sec_off, b.sec_off);
    assert_eq!(a.extern_tls, b.extern_tls);
    let meta = ObjModuleMeta {
        obj_name: "demo".into(),
        obj_file: "Examples/Generated/DemoObj.lean".into(),
        namespace_prefix: "Examples".into(),
        title: "demo".into(),
        license_header: vec![],
    };
    assert_eq!(render_image(&meta, a), render_image(&meta, b));
}

/// Full image with `rodata + data + bss + extdata + GOT` at `perturb = 0`, `4100`, and `8188`:
/// `PageSeparated` enforces 4 KiB page separation and exact `li.ro_data` coverage of
/// `[data_off, rw_off)`, while `Interleaved` equals `link_with_perturb` field by field.
#[test]
fn page_separated_layout_with_rodata_data_bss_extdata_and_got_at_0_and_4100() {
    use RelocType::*;
    use SymBind::*;
    use SymKind::*;
    let o = ObjObject {
        name: "full.o".into(),
        sections: vec![
            sec(
                ".text",
                SecKind::Text,
                4,
                words(&[0x90000000, 0xf9400000, 0xd65f03c0]),
                vec![rel(0, AdrGotPage, 5, 0), rel(4, Ld64GotLo12Nc, 5, 0)],
            ),
            sec(".rodata", SecKind::Rodata, 8, vec![0x11; 16], vec![]),
            sec(".data", SecKind::Data, 8, vec![0x22; 8], vec![]),
            sec(".bss", SecKind::Bss, 8, vec![], vec![]),
        ],
        symbols: vec![
            sym("", Notype, Local, SymSection::Undef),
            ObjSymbol {
                size: 12,
                ..sym("entry", Func, Global, SymSection::Sec(0))
            },
            ObjSymbol {
                size: 16,
                ..sym("ro_tbl", Object, Global, SymSection::Sec(1))
            },
            ObjSymbol {
                size: 8,
                ..sym("rw_val", Object, Global, SymSection::Sec(2))
            },
            ObjSymbol {
                size: 16,
                ..sym("bss_buf", Object, Global, SymSection::Sec(3))
            },
            sym("ext_obj", Notype, Global, SymSection::Undef),
        ],
        groups: vec![],
        elf_bytes: vec![],
    };
    let externs = [ext("ext_obj", ExternKind::Object, 24, 8)];
    let is_ro = |li: &LinkedImage, off: u64| -> bool {
        li.ro_data.iter().any(|&(o, n)| o <= off && off < o + n)
    };

    for p in [0u64, 4096 + 4, 4096 + 4092] {
        let inter =
            link_with_layout(std::slice::from_ref(&o), &externs, p, DataLayout::Interleaved)
                .unwrap();
        let def = link_with_perturb(std::slice::from_ref(&o), &externs, p).unwrap();
        assert_linked_image_eq(&inter, &def);
    }

    let li0 =
        link_with_layout(std::slice::from_ref(&o), &externs, 0, DataLayout::PageSeparated).unwrap();
    assert_eq!(li0.data_off, 0x1000);
    assert_eq!(li0.data.len(), 0x1008);
    assert_eq!(li0.bss, 16);
    assert_eq!(li0.extern_data, vec![("ext_obj".to_string(), 0x2018, 24)]);
    assert_eq!(li0.got_off, 0x3000);
    assert_eq!(li0.got, vec![GotEntry::Addr(0x2018)]);
    for off in 0x1000..0x2000 {
        assert!(is_ro(&li0, off), "perturb=0 byte {off:#x} must be ro_data");
    }
    for off in 0x2000..li0.data_end() {
        assert!(!is_ro(&li0, off), "perturb=0 rw byte {off:#x} must NOT be ro_data");
    }

    let li_p = link_with_layout(
        std::slice::from_ref(&o),
        &externs,
        4096 + 4,
        DataLayout::PageSeparated,
    )
    .unwrap();
    assert_eq!(li_p.data_off, 0x2000);
    assert_eq!(li_p.data.len(), 0x1010);
    assert_eq!(li_p.bss, 16);
    assert_eq!(li_p.extern_data, vec![("ext_obj".to_string(), 0x3020, 24)]);
    assert_eq!(li_p.got_off, 0x4008);
    assert_eq!(li_p.got, vec![GotEntry::Addr(0x3020)]);
    for off in 0x2000..0x3000 {
        assert!(is_ro(&li_p, off), "perturb=4100 byte {off:#x} must be ro_data");
    }
    for off in 0x3000..li_p.data_end() {
        assert!(
            !is_ro(&li_p, off),
            "perturb=4100 byte {off:#x} on rw page must NOT be ro_data"
        );
    }
    assert_ne!(li_p.got_off & !(PAGE_SIZE - 1), 0x3000);

    let li_wrap = link_with_layout(
        std::slice::from_ref(&o),
        &externs,
        4096 + 4092,
        DataLayout::PageSeparated,
    )
    .unwrap();
    assert_eq!(li_wrap.got_off % 8, 0);
}

/// An image with only `.rodata` (no non-empty writable `Data`, `Bss`, or `extern_data`, even if
/// 0-byte `.data`/`.bss` section headers exist as emitted by `llvm-mc`) is identical across
/// `PageSeparated`, `Interleaved`, and `link()`.
#[test]
fn page_separated_pure_rodata_image_matches_interleaved() {
    use RelocType::*;
    use SymBind::*;
    use SymKind::*;
    let mut empty_data = sec(".data", SecKind::Data, 8, vec![], vec![]);
    empty_data.size = 0;
    let mut empty_bss = sec(".bss", SecKind::Bss, 8, vec![], vec![]);
    empty_bss.size = 0;
    let o = ObjObject {
        name: "ro_only.o".into(),
        sections: vec![
            sec(
                ".text",
                SecKind::Text,
                4,
                words(&[0x90000000, 0x91000000, 0xd65f03c0]),
                vec![rel(0, AdrPrelPgHi21, 2, 0), rel(4, AddAbsLo12Nc, 2, 0)],
            ),
            sec(".rodata", SecKind::Rodata, 8, vec![0x42; 24], vec![]),
            empty_data,
            empty_bss,
        ],
        symbols: vec![
            sym("", Notype, Local, SymSection::Undef),
            ObjSymbol {
                size: 12,
                ..sym("get_const", Func, Global, SymSection::Sec(0))
            },
            ObjSymbol {
                size: 24,
                ..sym("KONST", Object, Global, SymSection::Sec(1))
            },
        ],
        groups: vec![],
        elf_bytes: vec![],
    };
    let li_def = link(std::slice::from_ref(&o), &[]).unwrap();
    let li_inter =
        link_with_layout(std::slice::from_ref(&o), &[], 0, DataLayout::Interleaved).unwrap();
    let li_sep =
        link_with_layout(std::slice::from_ref(&o), &[], 0, DataLayout::PageSeparated).unwrap();
    assert_linked_image_eq(&li_inter, &li_def);
    assert_linked_image_eq(&li_sep, &li_def);
    assert_eq!(li_sep.data_off, 0x1000);
    assert_eq!(li_sep.data, vec![0x42; 24]);
    assert_eq!(li_sep.bss, 0);
    assert_eq!(li_sep.ro_data, vec![(0x1000, 24)]);
    assert_eq!(li_sep.extern_data, vec![]);
    assert_eq!(li_sep.got_off, 0x1018);
    assert_eq!(li_sep.got, vec![]);
}

/// Across every multi-region fixture (`hand_asm`, `bss`-only, extern GOT, TLS-IE GOT, and
/// `reloc_fns` + `data_syms`), `DataLayout::Interleaved` equals `link()` field by field while
/// `DataLayout::PageSeparated` produces the exact 4 KiB page-separated layout.
#[test]
fn page_separated_and_interleaved_match_reference_layouts_across_fixtures() {
    use RelocType::*;
    use SymBind::*;
    use SymKind::*;

    // 1. `hand_asm` (`rodata` + `data` + extern func stub).
    let (o_hand, ext_hand) = hand_asm();
    let def = link(std::slice::from_ref(&o_hand), &ext_hand).unwrap();
    let inter = link_with_layout(
        std::slice::from_ref(&o_hand),
        &ext_hand,
        0,
        DataLayout::Interleaved,
    )
    .unwrap();
    assert_linked_image_eq(&inter, &def);
    let sep = link_with_layout(
        std::slice::from_ref(&o_hand),
        &ext_hand,
        0,
        DataLayout::PageSeparated,
    )
    .unwrap();
    assert_eq!(sep.ro_data, vec![(0x1000, 8), (0x1008, 0xff8)]);
    assert_eq!(
        sep.relocs,
        vec![DataReloc {
            off: 0x1000,
            width: 8,
            target: 0x1001
        }]
    );
    assert_eq!(sep.got_off, 0x3000);

    // 2. `.bss`-only writable image (`got_off` moves to fresh page `0x2000`).
    let o_bss = ObjObject {
        name: "a".into(),
        sections: vec![
            sec(
                ".text.f",
                SecKind::Text,
                4,
                words(&[0xd503201f, 0xd65f03c0]),
                vec![],
            ),
            sec(".bss", SecKind::Bss, 8, vec![], vec![]),
        ],
        symbols: vec![
            sym("", Notype, Local, SymSection::Undef),
            ObjSymbol {
                size: 8,
                ..sym("f", Func, Global, SymSection::Sec(0))
            },
            ObjSymbol {
                size: 16,
                ..sym("buf", Object, Global, SymSection::Sec(1))
            },
        ],
        groups: vec![],
        elf_bytes: vec![],
    };
    assert_linked_image_eq(
        &link_with_layout(std::slice::from_ref(&o_bss), &[], 0, DataLayout::Interleaved).unwrap(),
        &link(std::slice::from_ref(&o_bss), &[]).unwrap(),
    );
    let sep_bss =
        link_with_layout(std::slice::from_ref(&o_bss), &[], 0, DataLayout::PageSeparated).unwrap();
    assert_eq!(sep_bss.got_off, 0x2000);

    // 3. Extern data object + GOT + TLS-IE slots.
    let tls_exts = [
        ext("u", ExternKind::Tls, 4, 4),
        ext("t", ExternKind::Tls, 8, 32),
        ext("x", ExternKind::Object, 8, 8),
    ];
    let o_tls = tls_ie_obj(Tls);
    assert_linked_image_eq(
        &link_with_layout(
            std::slice::from_ref(&o_tls),
            &tls_exts,
            0,
            DataLayout::Interleaved,
        )
        .unwrap(),
        &link(std::slice::from_ref(&o_tls), &tls_exts).unwrap(),
    );
    let sep_tls = link_with_layout(
        std::slice::from_ref(&o_tls),
        &tls_exts,
        0,
        DataLayout::PageSeparated,
    )
    .unwrap();
    assert_eq!(sep_tls.got_off, 0x2000);
    assert_eq!(
        sep_tls.code[0..16],
        words(&[0xd0000000, 0xf9400000, 0xd0000000, 0xf9400400])[..]
    );

    // 4. `reloc_fns` + `data_syms` + empty 0-byte `.rodata` section (`ro_data` omission under
    //    `PageSeparated` vs inclusion under `Interleaved`).
    let mut empty_ro = sec(".rodata.empty", SecKind::Rodata, 1, vec![], vec![]);
    empty_ro.size = 0;
    let o_reloc = ObjObject {
        name: "m".into(),
        sections: vec![
            sec(
                ".text",
                SecKind::Text,
                4,
                words(&[0x90000000, 0x91000000, 0x94000000, 0xd65f03c0]),
                vec![
                    rel(0, AdrPrelPgHi21, 2, 8),
                    rel(4, AddAbsLo12Nc, 2, 8),
                    rel(8, Call26, 4, 0),
                ],
            ),
            sec(".rodata", SecKind::Rodata, 8, vec![0; 16], vec![rel(0, Abs64, 4, 0)]),
            empty_ro,
            sec(".bss", SecKind::Bss, 8, vec![], vec![]),
        ],
        symbols: vec![
            sym("", Notype, Local, SymSection::Undef),
            ObjSymbol {
                size: 16,
                ..sym("f", Func, Global, SymSection::Sec(0))
            },
            ObjSymbol {
                size: 16,
                ..sym("tbl [m]", Object, Local, SymSection::Sec(1))
            },
            ObjSymbol {
                size: 16,
                ..sym("err_buf [m]", Object, Local, SymSection::Sec(3))
            },
            sym("ext_fn", Notype, Global, SymSection::Undef),
        ],
        groups: vec![],
        elf_bytes: vec![],
    };
    let fn_exts = [ext("ext_fn", ExternKind::Func, 0, 4)];
    let def_reloc = link(std::slice::from_ref(&o_reloc), &fn_exts).unwrap();
    let inter_reloc = link_with_layout(
        std::slice::from_ref(&o_reloc),
        &fn_exts,
        0,
        DataLayout::Interleaved,
    )
    .unwrap();
    assert_linked_image_eq(&inter_reloc, &def_reloc);
    assert!(inter_reloc.ro_data.iter().any(|&(_, n)| n == 0));

    let sep_reloc = link_with_layout(
        std::slice::from_ref(&o_reloc),
        &fn_exts,
        0,
        DataLayout::PageSeparated,
    )
    .unwrap();
    assert!(!sep_reloc.ro_data.iter().any(|&(_, n)| n == 0));
    assert_eq!(sep_reloc.objects[0].data_syms[0].off, 0x1000);
    assert_eq!(sep_reloc.objects[0].data_syms[1].off, 0x2000);
}

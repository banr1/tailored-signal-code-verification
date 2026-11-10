// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Unit tests for `snapshot-link`'s trimmed sysroot objects ([`crate::trimmed`]) and the
//! `--stock-lld-arg` file provenance (`[TEST ONLY]`).

use crate::stock::lld_arg_files;
use crate::trimmed::{check_none_collected, check_round_trip, emit, keep_set_digest, roots};
use object::write::{Comdat, Object, Relocation, StandardSegment, Symbol, SymbolSection};
use object::{
    Architecture, BinaryFormat, ComdatKind, Endianness, Object as _, ObjectSymbol, RelocationFlags,
    SectionKind, SymbolFlags, SymbolKind, SymbolScope, elf,
};
use rust_obj2lean::trusted_common::{ComdatGroup, ObjObject, SymSection};
use rust_obj2lean::trusted_extractor::{Trim, parse_object_with};
use rust_obj2lean::untrusted_driver::root_section_closure;
use std::path::Path;
use std::process::Command;

/// A codegen-unit-like member: `root` (in `.text.root`) calls the global `helper` and takes the
/// address of a local literal; `helper` is *defined in the member* (`.text.helper`), as is the
/// unrelated `other`. The extractor's keep set for `root` is `.text.root` + `.rodata.lit`
/// (relocations against globals are not followed), so the trim leaves `helper` undefined.
fn member() -> Vec<u8> {
    member_with(&[])
}

/// [`member`], with the extra global `aliases` at offset 0 of `.text.root` (folded functions).
fn member_with(aliases: &[&str]) -> Vec<u8> {
    let mut obj = Object::new(BinaryFormat::Elf, Architecture::Aarch64, Endianness::Little);
    let seg = obj.segment_name(StandardSegment::Text).to_vec();
    let text = |obj: &mut Object, name: &str, code: &[u8]| {
        let s = obj.add_section(seg.clone(), name.as_bytes().to_vec(), SectionKind::Text);
        obj.append_section_data(s, code, 4);
        s
    };
    // root: adrp x0, lit; add x0, x0, :lo12:lit; b helper; ret
    let root = text(
        &mut obj,
        ".text.root",
        &[
            0x00, 0x00, 0x00, 0x90, 0x00, 0x00, 0x00, 0x91, 0x00, 0x00, 0x00, 0x14, 0xc0, 0x03,
            0x5f, 0xd6,
        ],
    );
    let helper = text(
        &mut obj,
        ".text.helper",
        &[0x20, 0x00, 0x80, 0x52, 0xc0, 0x03, 0x5f, 0xd6],
    );
    let other = text(&mut obj, ".text.other", &[0xc0, 0x03, 0x5f, 0xd6]);
    let ro = obj.add_section(
        Vec::new(),
        b".rodata.lit".to_vec(),
        SectionKind::ReadOnlyData,
    );
    obj.append_section_data(ro, b"lit\0", 1);
    let sym = |obj: &mut Object, name: &str, section, scope, kind, size| {
        obj.add_symbol(Symbol {
            name: name.as_bytes().to_vec(),
            value: 0,
            size,
            kind,
            scope,
            weak: false,
            section: SymbolSection::Section(section),
            flags: SymbolFlags::None,
        })
    };
    for name in std::iter::once("root").chain(aliases.iter().copied()) {
        sym(
            &mut obj,
            name,
            root,
            SymbolScope::Linkage,
            SymbolKind::Text,
            16,
        );
    }
    let h = sym(
        &mut obj,
        "helper",
        helper,
        SymbolScope::Linkage,
        SymbolKind::Text,
        8,
    );
    sym(
        &mut obj,
        "other",
        other,
        SymbolScope::Linkage,
        SymbolKind::Text,
        4,
    );
    let lit = sym(
        &mut obj,
        "lit",
        ro,
        SymbolScope::Compilation,
        SymbolKind::Data,
        4,
    );
    for (offset, r_type, symbol) in [
        (0, elf::R_AARCH64_ADR_PREL_PG_HI21, lit),
        (4, elf::R_AARCH64_ADD_ABS_LO12_NC, lit),
        (8, elf::R_AARCH64_JUMP26, h),
    ] {
        obj.add_relocation(
            root,
            Relocation {
                offset,
                symbol,
                addend: 0,
                flags: RelocationFlags::Elf { r_type },
            },
        )
        .unwrap();
    }
    obj.write().unwrap()
}

/// The extractor's trim of [`member`] for root `root` (as `extract_sysroot_object` does).
fn trim() -> ObjObject {
    trim_of(member(), &["root"])
}

/// The extractor's trim of the member `bytes` for `roots`.
fn trim_of(bytes: Vec<u8>, roots: &[&str]) -> ObjObject {
    let roots: Vec<String> = roots.iter().map(|r| r.to_string()).collect();
    let keep = root_section_closure(&bytes, &roots).unwrap();
    let t = Trim {
        keep,
        local_suffix: " [libfixture]".into(),
    };
    parse_object_with("fixture", bytes, Some(&t)).unwrap()
}

fn sec_names(o: &ObjObject) -> Vec<&str> {
    o.sections.iter().map(|s| s.name.as_str()).collect()
}

/// A stub `helper` (the hook the proofs assume): `ret`.
fn stub_helper() -> Vec<u8> {
    let mut stub = Object::new(BinaryFormat::Elf, Architecture::Aarch64, Endianness::Little);
    let s = stub.section_id(object::write::StandardSection::Text);
    stub.append_section_data(s, &[0xc0, 0x03, 0x5f, 0xd6], 4);
    stub.add_symbol(Symbol {
        name: b"helper".to_vec(),
        value: 0,
        size: 4,
        kind: SymbolKind::Text,
        scope: SymbolScope::Linkage,
        weak: false,
        section: SymbolSection::Section(s),
        flags: SymbolFlags::None,
    });
    stub.write().unwrap()
}

#[test]
fn trimmed_member_emits_a_real_object_equal_to_the_trim() {
    let t = trim();
    assert_eq!(sec_names(&t), [".text.root", ".rodata.lit"]);
    let helper = t.symbols.iter().find(|s| s.raw_name == "helper").unwrap();
    assert_eq!(
        helper.sec,
        SymSection::Undef,
        "the trim leaves `helper` undefined"
    );
    assert!(!t.symbols.iter().any(|s| s.raw_name == "other"));

    let bytes = emit(&t).unwrap();
    check_round_trip(&t, &bytes).unwrap();
    assert_eq!(emit(&t).unwrap(), bytes, "emission is deterministic");
    // The emitted object defines only what the trim defines: `helper` is undefined in it, so it
    // can only resolve outside the unit.
    let f = object::File::parse(&*bytes).unwrap();
    let h = f.symbols().find(|s| s.name() == Ok("helper")).unwrap();
    assert!(h.is_undefined());
    assert!(f.symbols().all(|s| s.name() != Ok("other")));
    // Local symbols are kept, not pruned (the round trip above compares them too).
    let locals = |o: &ObjObject| {
        o.symbols
            .iter()
            .filter(|s| s.bind == rust_obj2lean::trusted_common::SymBind::Local)
            .count()
    };
    assert!(locals(&t) > 0);
    let back = rust_obj2lean::trusted_extractor::parse_object("fixture", bytes.clone()).unwrap();
    assert_eq!(locals(&back), locals(&t));
    assert_eq!(keep_set_digest(&t).len(), 64);
}

#[test]
fn trimmed_member_links_helper_outside_the_unit() {
    let Some(lld) = super::tests::find_test_lld() else {
        eprintln!("skipping: ld.lld unavailable");
        return;
    };
    let dir = tempfile::tempdir().unwrap();
    let t = trim();
    std::fs::write(dir.path().join("trim.o"), emit(&t).unwrap()).unwrap();
    std::fs::write(dir.path().join("member.o"), member()).unwrap();
    std::fs::write(dir.path().join("stub.o"), stub_helper()).unwrap();
    // The emitted trim links, and its only `helper` is the stub's.
    let st = Command::new(&lld)
        .current_dir(dir.path())
        .args([
            "-static",
            "--gc-sections",
            "-e",
            "root",
            "-o",
            "t.elf",
            "trim.o",
            "stub.o",
        ])
        .status()
        .unwrap();
    assert!(st.success());
    let b = std::fs::read(dir.path().join("t.elf")).unwrap();
    let f = object::File::parse(&*b).unwrap();
    assert_eq!(f.symbols().filter(|s| s.name() == Ok("helper")).count(), 1);
    // The whole member links its own `helper` instead (the stub's duplicate is an error), which
    // is exactly what linking the trim avoids.
    let out = Command::new(&lld)
        .current_dir(dir.path())
        .args([
            "-static",
            "--gc-sections",
            "-e",
            "root",
            "-o",
            "m.elf",
            "member.o",
            "stub.o",
        ])
        .output()
        .unwrap();
    assert!(!out.status.success());
    assert!(String::from_utf8_lossy(&out.stderr).contains("duplicate symbol: helper"));
}

#[test]
fn round_trip_rejects_an_object_that_differs_from_the_trim() {
    let t = trim();
    // The whole member is not the trim: it keeps `.text.helper` / `.text.other` and defines
    // `helper`.
    let e = check_round_trip(&t, &member()).unwrap_err();
    assert!(format!("{e:#}").contains("sections"), "{e:#}");
    // Patched code bytes.
    let mut bytes = emit(&t).unwrap();
    let pos = bytes
        .windows(4)
        .position(|w| w == [0x00, 0x00, 0x00, 0x14])
        .unwrap();
    bytes[pos + 3] = 0x94; // b -> bl
    let e = check_round_trip(&t, &bytes).unwrap_err();
    assert!(
        format!("{e:#}").contains("section `.text.root` differs"),
        "{e:#}"
    );
    // A trim whose symbol table differs (here: `helper` defined, as the member's copy would be).
    let mut t2 = t.clone();
    let h = t2
        .symbols
        .iter()
        .position(|s| s.raw_name == "helper")
        .unwrap();
    t2.symbols[h].sec = SymSection::Sec(0);
    let e = check_round_trip(&t2, &emit(&t).unwrap()).unwrap_err();
    assert!(
        format!("{e:#}").contains("symbol `helper` differs"),
        "{e:#}"
    );
    // An object missing a kept section (strict equality, not a subset): the trim keeps one more
    // section than the emitted object has.
    let mut t3 = t.clone();
    let mut extra = t3.sections[1].clone();
    extra.name = ".rodata.extra".into();
    t3.sections.push(extra);
    let e = check_round_trip(&t3, &emit(&t).unwrap()).unwrap_err();
    assert!(
        format!("{e:#}").contains("has 2 sections, the trim 3"),
        "{e:#}"
    );
}

#[test]
fn link_must_keep_every_kept_section() {
    let Some(lld) = super::tests::find_test_lld() else {
        eprintln!("skipping: ld.lld unavailable");
        return;
    };
    let dir = tempfile::tempdir().unwrap();
    let t = trim();
    let trim_o = dir.path().join("trim.o");
    crate::trimmed::write(&t, &["root".into()], &trim_o).unwrap();
    std::fs::write(dir.path().join("stub.o"), stub_helper()).unwrap();
    let link = |extra: &[String]| {
        let out = Command::new(&lld)
            .current_dir(dir.path())
            .args([
                "-static",
                "--gc-sections",
                "--print-gc-sections",
                "-e",
                "helper",
            ])
            .args(extra)
            .arg("-o")
            .arg("t.elf")
            .arg(&trim_o)
            .arg("stub.o")
            .output()
            .unwrap();
        assert!(out.status.success());
        String::from_utf8_lossy(&out.stdout).into_owned() + &String::from_utf8_lossy(&out.stderr)
    };
    // Nothing references the trim: lld drops both kept sections, and the check fails.
    let e = check_none_collected(&link(&[]), &[&trim_o]).unwrap_err();
    let msg = format!("{e:#}");
    assert!(
        msg.contains(".text.root") && msg.contains(".rodata.lit"),
        "{msg}"
    );
    // Rooted at the trim's defined globals, the whole keep set survives.
    let roots: Vec<String> = roots(&t).map(|s| format!("--undefined={s}")).collect();
    assert_eq!(roots, ["--undefined=root"]);
    check_none_collected(&link(&roots), &[&trim_o]).unwrap();
}

#[test]
fn emit_rejects_what_the_trim_cannot_represent() {
    let mut t = trim();
    t.groups.push(ComdatGroup {
        signature: "g".into(),
        is_comdat: true,
        sections: vec![0],
    });
    assert!(format!("{:#}", emit(&t).unwrap_err()).contains("section group"));
    let mut t = trim();
    t.sections[0].sh_flags |= u64::from(elf::SHF_GROUP);
    assert!(format!("{:#}", emit(&t).unwrap_err()).contains("SHF_GROUP"));
    let mut t = trim();
    let h = t
        .symbols
        .iter()
        .position(|s| s.raw_name == "helper")
        .unwrap();
    t.symbols[h].sec = SymSection::Other;
    assert!(format!("{:#}", emit(&t).unwrap_err()).contains("not extracted"));
}

/// A member with `root` (in `.text.root`) and `grouped` (in `.text.grouped`, the only member of
/// the COMDAT group with signature `grouped`).
fn comdat_member() -> Vec<u8> {
    let mut obj = Object::new(BinaryFormat::Elf, Architecture::Aarch64, Endianness::Little);
    let seg = obj.segment_name(StandardSegment::Text).to_vec();
    let mut func = |obj: &mut Object, sec: &str, name: &str| {
        let s = obj.add_section(seg.clone(), sec.as_bytes().to_vec(), SectionKind::Text);
        obj.append_section_data(s, &[0xc0, 0x03, 0x5f, 0xd6], 4);
        let sym = obj.add_symbol(Symbol {
            name: name.as_bytes().to_vec(),
            value: 0,
            size: 4,
            kind: SymbolKind::Text,
            scope: SymbolScope::Linkage,
            weak: false,
            section: SymbolSection::Section(s),
            flags: SymbolFlags::None,
        });
        (s, sym)
    };
    func(&mut obj, ".text.root", "root");
    let (grouped, sym) = func(&mut obj, ".text.grouped", "grouped");
    obj.add_comdat(Comdat {
        kind: ComdatKind::Any,
        symbol: sym,
        sections: vec![grouped],
    });
    obj.write().unwrap()
}

#[test]
fn emit_ignores_groups_whose_members_were_all_trimmed() {
    let bytes = comdat_member();
    let t = trim_of(bytes.clone(), &["root"]);
    assert_eq!(sec_names(&t), [".text.root"]);
    assert_eq!(
        t.groups,
        [ComdatGroup {
            signature: "grouped".into(),
            is_comdat: true,
            sections: vec![],
        }]
    );
    let dir = tempfile::tempdir().unwrap();
    crate::trimmed::write(&t, &["root".into()], &dir.path().join("t.o")).unwrap();

    // A group with a kept member section is still rejected.
    let kept = trim_of(bytes, &["root", "grouped"]);
    assert_eq!(kept.groups.len(), 1);
    assert!(!kept.groups[0].sections.is_empty());
    assert!(format!("{:#}", emit(&kept).unwrap_err()).contains("keeps a section group"));
}

#[test]
fn lld_arg_files_hashes_named_files_and_rejects_response_files() {
    let dir = tempfile::tempdir().unwrap();
    std::fs::write(dir.path().join("stock.ld"), "SECTIONS {}\n").unwrap();
    let args = |v: &[&str]| v.iter().map(|s| s.to_string()).collect::<Vec<_>>();
    let got = lld_arg_files(
        &args(&[
            "-O2",
            "-Tstock.ld",
            "--script=stock.ld",
            "stock.ld",
            "--icf=all",
        ]),
        dir.path(),
    )
    .unwrap();
    let names: Vec<&str> = got.iter().map(|(a, _)| a.as_str()).collect();
    assert_eq!(names, ["-Tstock.ld", "--script=stock.ld", "stock.ld"]);
    assert!(got.iter().all(|(_, p)| p == &dir.path().join("stock.ld")));
    assert!(lld_arg_files(&args(&["@resp"]), Path::new(".")).is_err());
    // Two-token forms hash the next argument.
    let got = lld_arg_files(
        &args(&["-T", "stock.ld", "--script", "stock.ld"]),
        dir.path(),
    )
    .unwrap();
    let names: Vec<&str> = got.iter().map(|(a, _)| a.as_str()).collect();
    assert_eq!(names, ["-T stock.ld", "--script stock.ld"]);
    assert!(lld_arg_files(&args(&["-T", "missing.ld"]), dir.path()).is_err());
    assert!(lld_arg_files(&args(&["--script"]), dir.path()).is_err());
    // Library search is rejected.
    for a in ["-L.", "-lfoo", "--library=foo", "--library-path=."] {
        assert!(lld_arg_files(&args(&[a]), dir.path()).is_err(), "{a}");
    }
}

/// On demand: emit, round-trip and report the trims of real sysroot members.
/// `SNAPSHOT_LINK_TRIM_PROBE='<member.o>|<root>;...' cargo test -p snapshot-link -- --ignored`
#[test]
#[ignore]
fn probe_real_sysroot_members() {
    let spec = std::env::var("SNAPSHOT_LINK_TRIM_PROBE").unwrap_or_default();
    for (i, item) in spec.split(';').filter(|s| !s.is_empty()).enumerate() {
        let (path, root) = item.split_once('|').unwrap();
        let bytes = std::fs::read(path).unwrap();
        let keep = root_section_closure(&bytes, &[root.to_string()]).unwrap();
        let t = Trim {
            keep,
            local_suffix: format!(" [lib{i}]"),
        };
        let o = parse_object_with(&format!("m{i}"), bytes.clone(), Some(&t)).unwrap();
        let out = emit(&o).unwrap();
        check_round_trip(&o, &out).unwrap();
        let undef: Vec<&str> = o
            .symbols
            .iter()
            .filter(|s| s.sec == SymSection::Undef && !s.raw_name.is_empty())
            .map(|s| s.raw_name.as_str())
            .collect();
        let dir = std::env::var("SNAPSHOT_LINK_TRIM_PROBE_OUT").unwrap_or_else(|_| ".".into());
        std::fs::write(Path::new(&dir).join(format!("trim{i}.o")), &out).unwrap();
        eprintln!(
            "PROBE {root}: member {} B, trim {} B, sections {:?}, undefined {undef:?}, keepSetSha256 {}",
            bytes.len(),
            out.len(),
            sec_names(&o),
            keep_set_digest(&o)
        );
    }
}

/// A text section with `grow_one` (8 bytes at 0) plus the flagged symbols `extra`
/// (`(name, offset, size)`).
fn flagged_fixture(extra: &[(&str, u64, u64)]) -> Vec<u8> {
    let mut o = Object::new(BinaryFormat::Elf, Architecture::Aarch64, Endianness::Little);
    let s = o.section_id(object::write::StandardSection::Text);
    o.append_section_data(s, &[0xc0, 0x03, 0x5f, 0xd6].repeat(4), 4);
    let mut sym = |name: &str, value, size| {
        o.add_symbol(Symbol {
            name: name.as_bytes().to_vec(),
            value,
            size,
            kind: SymbolKind::Text,
            scope: SymbolScope::Linkage,
            weak: false,
            section: SymbolSection::Section(s),
            flags: SymbolFlags::None,
        });
    };
    sym("grow_one", 0, 8);
    for &(n, v, z) in extra {
        sym(n, v, z);
    }
    o.write().unwrap()
}

#[test]
fn symbol_audit_exempts_only_listed_pure_aliases() {
    let audit = |extra: &[(&str, u64, u64)], exempt: &[&str]| {
        let b = flagged_fixture(extra);
        let exempt: Vec<String> = exempt.iter().map(|e| e.to_string()).collect();
        crate::verify::forbidden_symbols(&object::File::parse(&*b).unwrap(), &exempt)
    };
    let alias = "RawVec<gimli::AttributeValue>::grow_one";
    // A listed folded alias at the same section and address, no larger than `grow_one`: exempt.
    assert!(audit(&[(alias, 0, 8)], &[alias]).is_empty());
    // Not listed (the generic audit): reported.
    assert_eq!(audit(&[(alias, 0, 8)], &[]), [alias]);
    // Listed, but with bytes of its own (elsewhere, or past the end of `grow_one`): reported.
    assert_eq!(
        audit(&[("gimli::read", 8, 4)], &["gimli::read"]),
        ["gimli::read"]
    );
    assert_eq!(
        audit(&[("gimli::wide", 0, 12)], &["gimli::wide"]),
        ["gimli::wide"]
    );
    // Two flagged symbols do not exempt each other.
    assert_eq!(
        audit(
            &[("gimli::a", 8, 4), ("gimli::b", 8, 4)],
            &["gimli::a", "gimli::b"]
        ),
        ["gimli::a", "gimli::b"]
    );
}

/// Link `inputs` (in `dir`) with `ld.lld`, entry `root`, plus `extra` flags; the output
/// (stdout + stderr) and the executable.
fn lld_link(lld: &Path, dir: &Path, inputs: &[&str], extra: &[&str]) -> (String, Vec<u8>) {
    let out = Command::new(lld)
        .current_dir(dir)
        .args(["-static", "--gc-sections", "-e", "root", "-o", "a.elf"])
        .args(extra)
        .args(inputs)
        .output()
        .unwrap();
    let log =
        String::from_utf8_lossy(&out.stdout).into_owned() + &String::from_utf8_lossy(&out.stderr);
    assert!(out.status.success(), "{log}");
    (log, std::fs::read(dir.join("a.elf")).unwrap())
}

#[test]
fn exempt_aliases_requires_a_root_section_with_unchanged_bytes() {
    let Some(lld) = super::tests::find_test_lld() else {
        eprintln!("skipping: ld.lld unavailable");
        return;
    };
    let alias = "RawVec<gimli::AttributeValue>::grow_one";
    let dir = tempfile::tempdir().unwrap();
    let t = trim_of(member_with(&[alias]), &["root"]);
    let roots = vec!["root".to_string()];
    crate::trimmed::write(&t, &roots, &dir.path().join("trim.o")).unwrap();
    std::fs::write(dir.path().join("stub.o"), stub_helper()).unwrap();
    let (_, exe) = lld_link(&lld, dir.path(), &["trim.o", "stub.o"], &[]);
    let exempt = crate::trimmed::exempt_aliases(&exe, &[(&t, &roots)]).unwrap();
    assert_eq!(exempt, [alias]);
    crate::verify::forbidden_symbols(&object::File::parse(&*exe).unwrap(), &exempt)
        .is_empty()
        .then_some(())
        .unwrap();
    // Not in a root section: with `helper` as the only root, `.text.root` is not a root section.
    let none = crate::trimmed::exempt_aliases(&exe, &[(&t, &["helper".to_string()])]).unwrap();
    assert!(none.is_empty());
    // Linked bytes that differ from the trim outside relocation fields (the trailing `ret`).
    let mut t2 = t.clone();
    let n = t2.sections[0].bytes.len();
    t2.sections[0].bytes[n - 1] ^= 1;
    assert!(
        crate::trimmed::exempt_aliases(&exe, &[(&t2, &roots)])
            .unwrap()
            .is_empty()
    );
}

#[test]
fn round_trip_compares_relocations_and_local_symbols() {
    let t = trim();
    let bytes = emit(&t).unwrap();
    // A relocation addend.
    let mut t2 = t.clone();
    t2.sections[0].relocs[0].addend += 4;
    let e = check_round_trip(&t2, &bytes).unwrap_err();
    assert!(
        format!("{e:#}").contains("section `.text.root` differs"),
        "{e:#}"
    );
    // A local symbol's value.
    let mut t3 = t.clone();
    let l = t3.symbols.iter().position(|s| s.raw_name == "lit").unwrap();
    t3.symbols[l].value += 1;
    let e = check_round_trip(&t3, &bytes).unwrap_err();
    assert!(format!("{e:#}").contains("symbol `lit` differs"), "{e:#}");
}

#[test]
fn re_extracting_the_emitted_object_gives_back_the_trim() {
    let t = trim();
    let bytes = emit(&t).unwrap();
    crate::trimmed::check_idempotent(&t, &bytes, &["root".into()]).unwrap();
    // A trim that keeps more than its roots reach (here: also `.text.other`) is not reproduced.
    let wide = trim_of(member(), &["root", "other"]);
    let e = crate::trimmed::check_idempotent(&wide, &emit(&wide).unwrap(), &["root".into()])
        .unwrap_err();
    assert!(
        format!("{e:#}").contains("re-extracted `fixture.o` has 2 sections, the trim 3"),
        "{e:#}"
    );
}

/// A one-member `ar` archive.
fn archive(member: &str, data: &[u8]) -> Vec<u8> {
    let mut a = b"!<arch>\n".to_vec();
    let hdr = format!(
        "{:<16}{:<12}{:<6}{:<6}{:<8}{:<10}`\n",
        format!("{member}/"),
        0,
        0,
        0,
        644,
        data.len()
    );
    a.extend_from_slice(hdr.as_bytes());
    a.extend_from_slice(data);
    if data.len() % 2 == 1 {
        a.push(b'\n');
    }
    a
}

#[test]
fn hooked_externs_resolve_only_to_stubs_or_the_runtime() {
    let Some(lld) = super::tests::find_test_lld() else {
        eprintln!("skipping: ld.lld unavailable");
        return;
    };
    let dir = tempfile::tempdir().unwrap();
    let d = dir.path();
    let t = trim();
    crate::trimmed::write(&t, &["root".into()], &d.join("trim.o")).unwrap();
    std::fs::write(d.join("stub.o"), stub_helper()).unwrap();
    // An archive (e.g. a Rust sysroot rlib) defining the hooked `helper`.
    std::fs::write(d.join("libstd.a"), archive("std.o", &stub_helper())).unwrap();
    let hooked: std::collections::BTreeSet<String> = ["helper".to_string()].into();
    let lib = d.join("libstd.a");
    let stub = d.join("stub.o");
    // Pre-link: the archive is found to define it.
    let defs = crate::stock_hooks::archive_definitions(&[&lib], &hooked).unwrap();
    assert_eq!(
        defs,
        [(
            "helper".to_string(),
            format!("{}(std.o)", lib.display()),
            false
        )]
    );
    assert!(
        crate::stock_hooks::archive_definitions(&[&lib], &["x".into()].into())
            .unwrap()
            .is_empty()
    );
    // Post-link: without the stub, lld fetches `helper` from the archive, which is rejected.
    let trace = ["--trace-symbol=helper"];
    let lib_s = lib.display().to_string();
    let stub_s = stub.display().to_string();
    let (log, _) = lld_link(&lld, d, &["trim.o", &lib_s], &trace);
    let bad = crate::trimmed::disallowed_definers(&log, &[&stub], &[]);
    assert_eq!(bad, [format!("{lib_s}(std.o): helper")], "{log}");
    // ... unless that archive is the C runtime.
    assert!(crate::trimmed::disallowed_definers(&log, &[&stub], &[&lib]).is_empty());
    // With the stub first, the stub defines it.
    let (log, _) = lld_link(&lld, d, &["trim.o", &stub_s, &lib_s], &trace);
    assert!(
        crate::trimmed::disallowed_definers(&log, &[&stub], &[]).is_empty(),
        "{log}"
    );
}

#[test]
fn stock_link_json_records_the_trim() {
    let t = trim();
    let tr = crate::trimmed::Trimmed {
        provenance: "sysroot `liballoc-x.rlib` member `alloc-x.cgu.0.rcgu.o`, 9 bytes".into(),
        roots: vec!["root".into()],
    };
    let j = crate::stock::object_json(&t, "work/lib0_0.o", Some(&tr)).unwrap();
    let f = &j["trimmedFrom"];
    assert_eq!(f["rlib"], "liballoc-x.rlib");
    assert_eq!(f["member"], "alloc-x.cgu.0.rcgu.o");
    assert_eq!(f["roots"], serde_json::json!(["root"]));
    assert_eq!(f["memberSha256"], crate::link::sha256(&t.elf_bytes));
    assert_eq!(f["keepSetSha256"], keep_set_digest(&t));
    assert_eq!(j["sha256"], crate::link::sha256(&emit(&t).unwrap()));
    assert_ne!(j["sha256"], f["memberSha256"]);
}

#[test]
fn std_main_is_weakened_only_for_names_the_emitted_trim_defines() {
    let Ok(objcopy) = crate::link::tool("LLVM_OBJCOPY", "llvm-objcopy") else {
        eprintln!("skipping: llvm-objcopy unavailable");
        return;
    };
    let d = tempfile::tempdir().unwrap();
    // A `std` main defining `root` (also in the trim) and `other` (only in the untrimmed member).
    let main_o = d.path().join("main_rust.o");
    let mut o = Object::new(BinaryFormat::Elf, Architecture::Aarch64, Endianness::Little);
    let text = o.section_id(object::write::StandardSection::Text);
    o.append_section_data(text, &[0xc0, 0x03, 0x5f, 0xd6, 0xc0, 0x03, 0x5f, 0xd6], 4);
    for (i, n) in ["root", "other"].iter().enumerate() {
        o.add_symbol(Symbol {
            name: n.as_bytes().to_vec(),
            value: 4 * i as u64,
            size: 4,
            kind: SymbolKind::Text,
            scope: SymbolScope::Linkage,
            weak: false,
            section: SymbolSection::Section(text),
            flags: SymbolFlags::None,
        });
    }
    std::fs::write(&main_o, o.write().unwrap()).unwrap();
    let emitted = emit(&trim()).unwrap();
    let w = crate::stock_std::weaken_image_symbols(&objcopy, &main_o, std::iter::once(&*emitted))
        .unwrap();
    assert_eq!(
        w,
        ["root"],
        "`other` is defined only by the untrimmed member"
    );
    let bytes = std::fs::read(&main_o).unwrap();
    let f = object::File::parse(&*bytes).unwrap();
    let weak = |n: &str| f.symbols().find(|s| s.name() == Ok(n)).unwrap().is_weak();
    assert!(weak("root") && !weak("other"));
}

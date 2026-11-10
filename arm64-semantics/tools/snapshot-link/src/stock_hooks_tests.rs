// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Unit tests for the hooked-extern resolution of a `--stock` link ([`crate::stock_hooks`])
//! (`[TEST ONLY]`): weak archive definitions shadowed by a global stub, the single-definer
//! positive control, `--stock-lld-arg` multiple-definition rejection, and hooked externs defined
//! by a declared export of a sibling `--config` image.

use crate::stock::StockImage;
use crate::stock_hooks::{
    HookPlan, archive_definitions, check, check_lld_args, classify_archive_definitions,
    elf_address, plan, sibling_definitions, strong_definitions,
};
use object::write::{Object, Symbol, SymbolSection};
use object::{
    Architecture, BinaryFormat, Endianness, SectionKind, SymbolFlags, SymbolKind, SymbolScope,
};
use rust_obj2lean::trusted_common::{ExternDecl, ExternKind};
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::Command;

/// An AArch64 object defining each `(name, weak)` of `defs` as a 4-byte `ret` function in its own
/// `.text.<name>` section.
fn obj(defs: &[(&str, bool)]) -> Vec<u8> {
    let mut o = Object::new(BinaryFormat::Elf, Architecture::Aarch64, Endianness::Little);
    for (n, weak) in defs {
        let s = o.add_section(
            b"".to_vec(),
            format!(".text.{n}").into_bytes(),
            SectionKind::Text,
        );
        o.append_section_data(s, &[0xc0, 0x03, 0x5f, 0xd6], 4);
        o.add_symbol(Symbol {
            name: n.as_bytes().to_vec(),
            value: 0,
            size: 4,
            kind: SymbolKind::Text,
            scope: SymbolScope::Linkage,
            weak: *weak,
            section: SymbolSection::Section(s),
            flags: SymbolFlags::None,
        });
    }
    o.write().unwrap()
}

/// A one-member archive.
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

/// `ld.lld` in `dir` with `args`; returns `(stdout + stderr, success)`.
fn lld(dir: &Path, args: &[&str]) -> (String, bool) {
    let lld = super::tests::find_test_lld().unwrap();
    let out = Command::new(lld)
        .current_dir(dir)
        .args(["-static", "--gc-sections", "-o", "a.elf"])
        .args(args)
        .output()
        .unwrap();
    (
        String::from_utf8_lossy(&out.stdout).into_owned() + &String::from_utf8_lossy(&out.stderr),
        out.status.success(),
    )
}

fn names(v: &[&str]) -> BTreeSet<String> {
    v.iter().map(|s| s.to_string()).collect()
}

fn hook_plan(hooked: &[&str]) -> HookPlan {
    HookPlan {
        hooked: names(hooked),
        ..HookPlan::default()
    }
}

#[test]
fn weak_archive_definition_is_shadowed_only_by_a_global_stub() {
    if super::tests::find_test_lld().is_none() {
        eprintln!("skipping: ld.lld unavailable");
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let d = dir.path();
    let p = |f: &str| d.join(f);
    std::fs::write(p("root.o"), obj(&[("root", false)])).unwrap();
    std::fs::write(p("stub.o"), obj(&[("helper", false)])).unwrap();
    std::fs::write(p("wstub.o"), obj(&[("helper", true)])).unwrap();
    // A single-member archive (like `compiler_builtins.a`) with a weak `helper`, fetched for
    // `other`.
    std::fs::write(
        p("libcb.a"),
        archive("cb.o", &obj(&[("helper", true), ("other", false)])),
    )
    .unwrap();
    std::fs::write(
        p("libstrong.a"),
        archive("s.o", &obj(&[("helper", false), ("other", false)])),
    )
    .unwrap();
    let hooked = names(&["helper"]);
    let (lib, strong_lib) = (p("libcb.a"), p("libstrong.a"));
    let (stub, wstub) = (p("stub.o"), p("wstub.o"));

    // Pre-link: a global stub shadows the weak archive definition ...
    let defs = archive_definitions(&[&lib], &hooked).unwrap();
    assert_eq!(
        defs,
        [("helper".into(), format!("{}(cb.o)", lib.display()), true)]
    );
    let strong = strong_definitions(&[&stub], &hooked).unwrap();
    assert_eq!(strong, hooked);
    let (shadowed, rejected) = classify_archive_definitions(&defs, &strong);
    assert_eq!(shadowed.len(), 1);
    assert!(rejected.is_empty());
    // ... a weak stub does not ...
    let weak = strong_definitions(&[&wstub], &hooked).unwrap();
    assert!(weak.is_empty());
    let (shadowed, rejected) = classify_archive_definitions(&defs, &weak);
    assert!(shadowed.is_empty());
    assert_eq!(
        rejected,
        [format!("{}(cb.o): helper (weak)", lib.display())]
    );
    // ... and a global archive definition is always rejected.
    let defs = archive_definitions(&[&strong_lib], &hooked).unwrap();
    let (_, rejected) = classify_archive_definitions(&defs, &strong);
    assert_eq!(
        rejected,
        [format!("{}(s.o): helper (global)", strong_lib.display())]
    );

    // Post-link, stub before the archive (the stock link order): lld fetches the member for
    // `other` but traces only the winning definition, and `helper` is the stub's.
    let (root_s, stub_s, lib_s) = (
        p("root.o").display().to_string(),
        stub.display().to_string(),
        lib.display().to_string(),
    );
    let link = [
        "-e",
        "root",
        "--undefined=helper",
        "--undefined=other",
        "--trace-symbol=helper",
        "-Map=link.map",
    ];
    let mut args = link.to_vec();
    args.extend([root_s.as_str(), stub_s.as_str(), lib_s.as_str()]);
    let (log, ok) = lld(d, &args);
    assert!(ok, "{log}");
    let def_lines: Vec<&str> = log
        .lines()
        .filter(|l| l.contains(": definition of helper"))
        .collect();
    assert_eq!(
        def_lines,
        [format!("{stub_s}: definition of helper")],
        "{log}"
    );
    let exe = std::fs::read(p("a.elf")).unwrap();
    let map = std::fs::read_to_string(p("link.map")).unwrap();
    assert_eq!(
        elf_address(&exe, "helper").unwrap(),
        crate::stock_hooks::placed_address(&map, &stub, "helper").unwrap(),
        "the executable's `helper` must be the stub's"
    );
    assert_ne!(
        elf_address(&exe, "helper").unwrap(),
        elf_address(&exe, "other").unwrap()
    );
    let mut plan = hook_plan(&["helper"]);
    plan.weak_shadowed =
        classify_archive_definitions(&archive_definitions(&[&lib], &hooked).unwrap(), &strong).0;
    let rec = check(&plan, &log, &[&stub], &[], &exe, None).unwrap();
    assert_eq!(
        rec["weakArchiveShadowed"],
        serde_json::json!([{"symbol": "helper", "archiveMember": "libcb.a(cb.o)"}])
    );
    assert_eq!(rec["siblingDefinedExterns"], serde_json::json!([]));

    // Archive before the stub: lld traces both definitions, and the positive control fails.
    let mut args = link.to_vec();
    args.extend([root_s.as_str(), lib_s.as_str(), stub_s.as_str()]);
    let (log2, ok) = lld(d, &args);
    assert!(ok, "{log2}");
    let e = check(&plan, &log2, &[&stub], &[], &exe, None).unwrap_err();
    assert!(format!("{e:#}").contains("helper: 2 definitions"), "{e:#}");
    // No trace line at all (e.g. a changed trace format) fails too.
    let e = check(&plan, "", &[&stub], &[], &exe, None).unwrap_err();
    assert!(format!("{e:#}").contains("helper: 0 definitions"), "{e:#}");
    // A lone weak stub against the archive: `plan` rejects it before the link.
    let im = trimmed_image("a.toml", &["helper"], vec![]);
    let e = plan_err(&[im], &[&wstub], &[&lib]);
    assert!(e.contains("helper (weak)"), "{e}");
}

fn plan_err(images: &[StockImage], stubs: &[&Path], archives: &[&Path]) -> String {
    format!("{:#}", plan(images, stubs, archives).unwrap_err())
}

#[test]
fn lld_args_allowing_multiple_definitions_are_rejected() {
    for bad in [
        &["--allow-multiple-definition"][..],
        &["-allow-multiple-definition"],
        &["-z", "muldefs"],
        &["-zmuldefs"],
        &["--stock", "-z", "muldefs"],
    ] {
        let v: Vec<String> = bad.iter().map(|s| s.to_string()).collect();
        let e = check_lld_args(&v).unwrap_err();
        assert!(
            format!("{e:#}").contains("multiple definitions"),
            "{bad:?}: {e:#}"
        );
    }
    let ok: Vec<String> = ["-z", "now", "-O2", "muldefs"]
        .iter()
        .map(|s| s.to_string())
        .collect();
    check_lld_args(&ok).unwrap();
}

/// A legacy-mangled Rust name, demangling (`{:#}`) to `signal_session_io::read_file`.
const MANGLED: &str = "_ZN17signal_session_io9read_file17h0123456789abcdefE";
const DEMANGLED: &str = "signal_session_io::read_file";

fn extern_decl(raw: &str) -> ExternDecl {
    ExternDecl {
        name: raw.into(),
        raw_name: raw.into(),
        kind: ExternKind::Func,
        size: 0,
        align: 4,
        origin: String::new(),
    }
}

/// An image with a trimmed sysroot object and the hooked externs `externs` (its objects are
/// not needed here).
fn trimmed_image(config: &str, externs: &[&str], paths: Vec<PathBuf>) -> StockImage {
    StockImage {
        config: config.into(),
        objects: vec![],
        externs: externs.iter().map(|e| extern_decl(e)).collect(),
        page_separate_data: false,
        paths,
        trimmed: vec![Some(crate::trimmed::Trimmed {
            provenance: String::new(),
            roots: vec![],
        })],
        exports: vec![],
    }
}

/// A sibling image whose object `path` defines `defs`, with declared `exports`.
fn sibling_image(config: &str, path: &Path, defs: &[&str], exports: &[&str]) -> StockImage {
    let bytes = obj(&defs.iter().map(|d| (*d, false)).collect::<Vec<_>>());
    std::fs::write(path, &bytes).unwrap();
    StockImage {
        config: config.into(),
        objects: vec![rust_obj2lean::trusted_extractor::parse_object("io", bytes).unwrap()],
        externs: vec![],
        page_separate_data: false,
        paths: vec![path.to_path_buf()],
        trimmed: vec![None],
        exports: exports.iter().map(|e| e.to_string()).collect(),
    }
}

#[test]
fn sibling_image_may_define_a_hooked_extern_only_as_a_declared_export() {
    let dir = tempfile::tempdir().unwrap();
    let b_o = dir.path().join("lib1_0.o");
    let a = || trimmed_image("session.toml", &[MANGLED], vec![]);

    // Declared by its demangled path (as `[placed] exports` lists it): allowed.
    let images = [
        a(),
        sibling_image("io.toml", &b_o, &[MANGLED, "other"], &[DEMANGLED]),
    ];
    let s = sibling_definitions(&images).unwrap();
    assert_eq!(s.len(), 1);
    assert_eq!(s[0].symbol, MANGLED);
    assert_eq!(s[0].export, DEMANGLED);
    assert_eq!(s[0].image, Path::new("io.toml"));
    assert_eq!(s[0].hooked_by, Path::new("session.toml"));
    assert_eq!(s[0].object, b_o);
    // ... or by its raw name.
    let images = [a(), sibling_image("io.toml", &b_o, &[MANGLED], &[MANGLED])];
    assert_eq!(sibling_definitions(&images).unwrap().len(), 1);

    // Defined but not declared as an export: rejected.
    let images = [
        a(),
        sibling_image("io.toml", &b_o, &[MANGLED, "other"], &["other"]),
    ];
    let e = format!("{:#}", sibling_definitions(&images).unwrap_err());
    assert!(e.contains("does not declare it as an export"), "{e}");
    // An export that resolves to no defined symbol, or to two: rejected.
    let images = [
        a(),
        sibling_image("io.toml", &b_o, &[MANGLED], &[DEMANGLED, "missing"]),
    ];
    let e = format!("{:#}", sibling_definitions(&images).unwrap_err());
    assert!(
        e.contains("`missing` does not resolve to exactly one"),
        "{e}"
    );
    let other = "_ZN17signal_session_io9read_file17hfedcba9876543210E";
    let images = [
        a(),
        sibling_image("io.toml", &b_o, &[MANGLED, other], &[DEMANGLED]),
    ];
    let e = format!("{:#}", sibling_definitions(&images).unwrap_err());
    assert!(e.contains("does not resolve to exactly one"), "{e}");
    // The image listing the name as an extern cannot be the sibling defining it.
    let mut b = sibling_image("io.toml", &b_o, &[MANGLED], &[DEMANGLED]);
    b.externs.push(extern_decl(MANGLED));
    let e = format!("{:#}", sibling_definitions(&[a(), b]).unwrap_err());
    assert!(
        e.contains("both defines it and lists it as an extern"),
        "{e}"
    );
    // No sibling defines it: nothing to record (a stub must define it).
    let images = [a(), sibling_image("io.toml", &b_o, &["other"], &["other"])];
    assert!(sibling_definitions(&images).unwrap().is_empty());
}

#[test]
fn two_config_link_with_a_sibling_defined_hooked_extern() {
    if super::tests::find_test_lld().is_none() {
        eprintln!("skipping: ld.lld unavailable");
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let d = dir.path();
    let a_o = d.join("lib0_0.o");
    let b_o = d.join("lib1_0.o");
    std::fs::write(&a_o, obj(&[("root", false)])).unwrap();
    let images = [
        trimmed_image("session.toml", &[MANGLED], vec![a_o.clone()]),
        sibling_image("io.toml", &b_o, &["pad", MANGLED], &[DEMANGLED]),
    ];
    let hp = plan(&images, &[], &[]).unwrap();
    assert_eq!(hp.siblings.len(), 1);
    let undef = format!("--undefined={MANGLED}");
    let trace = format!("--trace-symbol={MANGLED}");
    let (a_s, b_s) = (a_o.display().to_string(), b_o.display().to_string());
    let (log, ok) = lld(
        d,
        &[
            "-e",
            "root",
            "--undefined=pad",
            &undef,
            &trace,
            "-Map=link.map",
            &a_s,
            &b_s,
        ],
    );
    assert!(ok, "{log}");
    let exe = std::fs::read(d.join("a.elf")).unwrap();
    let map = std::fs::read_to_string(d.join("link.map")).unwrap();
    let rec = check(&hp, &log, &[], &[], &exe, Some(&map)).unwrap();
    let addr = elf_address(&exe, MANGLED).unwrap();
    assert_eq!(
        rec["siblingDefinedExterns"],
        serde_json::json!([{
            "symbol": MANGLED, "export": DEMANGLED, "hookedBy": "session.toml",
            "image": "io.toml", "object": "lib1_0.o", "address": format!("{addr:#x}"),
        }])
    );

    // Without the sibling allowance, its definition is rejected.
    let e = check(&hook_plan(&[MANGLED]), &log, &[], &[], &exe, Some(&map)).unwrap_err();
    assert!(format!("{e:#}").contains("resolve to neither"), "{e:#}");
    // The executable's address must be the sibling's placed export address.
    let want = format!("{b_s}:(.text.{MANGLED})");
    let tampered: String = map
        .lines()
        .map(|l| {
            if l.ends_with(&want) {
                let (cols, rest) = l.split_at(crate::stock_std_audit::MAP_COLS);
                let vma = cols.split_whitespace().next().unwrap();
                let moved = format!("{:x}", u64::from_str_radix(vma, 16).unwrap() + 4);
                format!(
                    "{}{rest}\n",
                    cols.replacen(&format!("{vma:>16}"), &format!("{moved:>16}"), 1)
                )
            } else {
                format!("{l}\n")
            }
        })
        .collect();
    assert_ne!(tampered, map);
    let e = check(&hp, &log, &[], &[], &exe, Some(&tampered)).unwrap_err();
    assert!(
        format!("{e:#}").contains("is not the placed address"),
        "{e:#}"
    );
    // A map without the sibling's input section fails closed.
    let header = crate::stock_std_audit::MAP_HEADER;
    let e = check(&hp, &log, &[], &[], &exe, Some(header)).unwrap_err();
    assert!(format!("{e:#}").contains("0 input-section lines"), "{e:#}");
    // So does a stub that defines the name instead of the sibling.
    let stub = d.join("stub.o");
    std::fs::write(&stub, obj(&[(MANGLED, false)])).unwrap();
    let st_s = stub.display().to_string();
    let (log, ok) = lld(
        d,
        &["-e", "root", &undef, &trace, "-Map=link.map", &a_s, &st_s],
    );
    assert!(ok, "{log}");
    let exe = std::fs::read(d.join("a.elf")).unwrap();
    let map = std::fs::read_to_string(d.join("link.map")).unwrap();
    let e = check(&hp, &log, &[&stub], &[], &exe, Some(&map)).unwrap_err();
    assert!(
        format!("{e:#}").contains("not defined by its sibling export object"),
        "{e:#}"
    );
}

#[test]
fn trace_lines_of_extra_names_are_dropped_and_definitions_recorded() {
    let log = "/o/work/lib0_0.o: reference to hooked\n\
               /o/work/main.o: definition of hooked\n\
               /o/work/lib1_0.o: reference to extra\n\
               /o/work/runtime/libc.a(write.lo): definition of extra\n\
               removing unused section /o/work/lib0_0.o:(.text.x)\n";
    let extra: BTreeSet<String> = ["extra".to_string()].into();
    let kept = crate::stock::without_trace_of(log, &extra);
    assert!(kept.contains("definition of hooked"), "{kept}");
    assert!(kept.contains("removing unused section"), "{kept}");
    assert!(!kept.contains("extra"), "{kept}");
    let rel = |p: &Path| {
        p.strip_prefix("/o")
            .map_or(p.display().to_string(), |r| r.display().to_string())
    };
    assert_eq!(
        crate::stock::trace_definitions(log, rel),
        serde_json::json!([
            {"symbol": "hooked", "kind": "definition of", "file": "work/main.o"},
            {"symbol": "extra", "kind": "definition of", "file": "work/runtime/libc.a(write.lo)"},
        ])
    );
}

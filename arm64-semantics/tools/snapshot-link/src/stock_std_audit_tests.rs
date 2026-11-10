// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Unit tests for the `--stock` `std` binary archive-member provenance and unwind audit
//! ([`crate::stock_std_audit`]) (`[TEST ONLY]`).

use crate::stock_std_audit::{Member, members_json, parse_members, unwind_audit};
use object::write::{Object as WObject, Symbol, SymbolSection};
use object::{Architecture, BinaryFormat, Endianness, SymbolFlags, SymbolKind, SymbolScope};
use std::collections::BTreeMap;
use std::path::Path;

const OUT: &str = "/build/out";

const WHY: &str = "reference\textracted\tsymbol\n\
/build/out/work/main_rust.o\t/build/out/work/self-contained/libc.a(write.lo)\twrite\n\
/build/out/work/self-contained/libc.a(write.lo)\t/build/out/work/self-contained/libc.a(syscall_cp.lo)\t__syscall_cp\n\
/build/out/work/main_rust.o\t/build/out/work/self-contained/libc.a(write.lo)\t__write\n";

/// One `-Map` line in `ld.lld`'s layout: `VMA LMA Size Align`, then `item` indented by `indent`
/// (0: output section, 8: input section, 16: symbol).
fn map_line(vma: u64, size: u64, align: u64, indent: usize, item: &str) -> String {
    format!(
        "{vma:>16x} {vma:>16x} {size:>8x} {align:>5} {:indent$}{item}\n",
        ""
    )
}

const MAP_HEADER: &str =
    "             VMA              LMA     Size Align Out     In      Symbol\n";

/// A `-Map` with the `--why-extract` members of [`WHY`] retaining sections.
fn map() -> String {
    let w = "/build/out/work/self-contained/libc.a";
    [
        MAP_HEADER.to_string(),
        map_line(0x2001c0, 0x10, 4, 0, ".text"),
        map_line(
            0x2001c0,
            0xc,
            4,
            8,
            "/build/out/work/main_rust.o:(.text.main)",
        ),
        map_line(
            0x2001d0,
            0x14,
            4,
            8,
            &format!("{w}(write.lo):(.text.write)"),
        ),
        map_line(0x2001d0, 0, 1, 16, "write"),
        map_line(
            0x2001e4,
            0x8,
            4,
            8,
            &format!("{w}(write.lo):(.text.write+0x14)"),
        ),
        map_line(0x2001ec, 0x20, 4, 8, &format!("{w}(syscall_cp.lo):(.text)")),
        map_line(0x200210, 0x4, 1, 8, "<internal>:(.comment)"),
    ]
    .concat()
}

/// `--print-gc-sections` output: an unwinder member extracted only for its `_Unwind_*` names,
/// all of whose sections are removed, plus non-archive noise.
const GC: &str = "removing unused section /build/out/work/self-contained/libunwind.a(UnwindLevel1.o):(.text._Unwind_RaiseException)
removing unused section /build/out/work/main_rust.o:(.text.unused)
removing unused section /build/out/work/self-contained/libc.a(write.lo):(.text.unused_write)
";

fn why_with_unwind() -> String {
    format!(
        "{WHY}/build/out/work/main_rust.o\t/build/out/work/self-contained/libunwind.a(UnwindLevel1.o)\t_Unwind_RaiseException\n"
    )
}

#[test]
fn parse_members_records_extraction_and_retained_sections() {
    let m = parse_members(&why_with_unwind(), &map(), GC, Path::new(OUT)).unwrap();
    assert_eq!(
        m.keys().collect::<Vec<_>>(),
        [
            "work/self-contained/libc.a(syscall_cp.lo)",
            "work/self-contained/libc.a(write.lo)",
            "work/self-contained/libunwind.a(UnwindLevel1.o)",
        ]
    );
    let w = &m["work/self-contained/libc.a(write.lo)"];
    // The first extraction is recorded, with paths relative to the output directory.
    assert_eq!(
        w.extracted_by,
        Some(("work/main_rust.o".to_string(), "write".to_string()))
    );
    // `+0x..` pieces of one input section are summed.
    assert_eq!(w.retained.get(".text.write"), Some(&0x1c));
    assert!(w.removed.contains(".text.unused_write"));
    // A member all of whose sections are removed is accounted for by the gc report.
    let u = &m["work/self-contained/libunwind.a(UnwindLevel1.o)"];
    assert!(u.retained.is_empty());
    assert!(u.removed.contains(".text._Unwind_RaiseException"));
    let j = members_json(&m);
    assert_eq!(j[0]["member"], "work/self-contained/libc.a(syscall_cp.lo)");
    assert_eq!(j[0]["retained"][0]["size"], 0x20);
    assert_eq!(j[1]["extractedBy"]["symbol"], "write");
    assert_eq!(
        j[2]["removed"],
        serde_json::json!([".text._Unwind_RaiseException"])
    );
}

fn parse_err(why: &str, map: &str, gc: &str) -> String {
    format!(
        "{:#}",
        parse_members(why, map, gc, Path::new(OUT)).unwrap_err()
    )
}

#[test]
fn parse_members_rejects_inconsistent_outputs() {
    let why = why_with_unwind();
    // A retained archive section of a member that `--why-extract` does not list.
    let extra = map()
        + &map_line(
            0x200220,
            4,
            4,
            8,
            "/build/out/work/self-contained/libc.a(exit.lo):(.text)",
        );
    assert!(parse_err(&why, &extra, GC).contains("libc.a(exit.lo)"));
    // A removed archive section of a member that `--why-extract` does not list.
    let gc = format!(
        "{GC}removing unused section /build/out/work/self-contained/libc.a(exit.lo):(.text)\n"
    );
    assert!(parse_err(&why, &map(), &gc).contains("libc.a(exit.lo)"));
    // A malformed `--why-extract` line.
    let e = parse_err(&format!("{why}only\ttwo\n"), &map(), GC);
    assert!(e.contains("expected `reference"), "{e}");
    // A non-hex size.
    let e = parse_err(
        &why,
        &map().replace("       14     4 ", "       zz     4 "),
        GC,
    );
    assert!(e.contains("unrecognized line"), "{e}");
    // An extracted member with neither a retained nor a removed section.
    let e = parse_err(&why, &map(), "");
    assert!(
        e.contains("neither a retained") && e.contains("libunwind.a(UnwindLevel1.o)"),
        "{e}"
    );
    // Nothing extracted at all.
    let e = parse_err("reference\textracted\tsymbol\n", &map(), GC);
    assert!(e.contains("no archive member extracted"), "{e}");
}

#[test]
fn parse_members_fails_closed_on_an_unrecognized_map_format() {
    let why = why_with_unwind();
    // A GNU ld style map: the header differs.
    let gnu = "Archive member included to satisfy reference by file (symbol)\n\n\
/build/out/work/self-contained/libc.a(write.lo)\n                              main_rust.o (write)\n";
    let e = parse_err(&why, gnu, GC);
    assert!(e.contains("unrecognized header"), "{e}");
    // The lld header, but lines in another layout (wider columns): no line parses.
    let wide = map()
        .lines()
        .enumerate()
        .map(|(i, l)| {
            if i == 0 {
                l.to_string()
            } else {
                format!("    {l}")
            }
        })
        .collect::<Vec<_>>()
        .join("\n");
    let e = parse_err(&why, &wide, GC);
    assert!(e.contains("unrecognized line"), "{e}");
    // Recognized lines, but no archive input section at all: the retained sets would be
    // vacuously empty.
    let no_inputs: String = map()
        .lines()
        .filter(|l| !l.contains(".a("))
        .map(|l| format!("{l}\n"))
        .collect();
    let e = parse_err(&why, &no_inputs, GC);
    assert!(e.contains("no retained archive input section"), "{e}");
    // An unexpected indentation.
    let odd = map() + &map_line(0x200220, 4, 4, 4, "odd");
    assert!(parse_err(&why, &odd, GC).contains("unrecognized line"));
    // A `--why-extract` header in another format.
    let e = parse_err(&why.replacen("reference", "ref", 1), &map(), GC);
    assert!(e.contains("unrecognized header"), "{e}");
}

/// A relocatable object with the symbols `(name, defined, weak)`.
fn elf_with(symbols: &[(&str, bool, bool)]) -> Vec<u8> {
    let mut o = WObject::new(BinaryFormat::Elf, Architecture::Aarch64, Endianness::Little);
    let text = o.section_id(object::write::StandardSection::Text);
    o.append_section_data(text, &[0xc0, 0x03, 0x5f, 0xd6], 4);
    for &(name, defined, weak) in symbols {
        o.add_symbol(Symbol {
            name: name.as_bytes().to_vec(),
            value: 0,
            size: if defined { 4 } else { 0 },
            kind: SymbolKind::Text,
            scope: SymbolScope::Linkage,
            weak,
            section: if defined {
                SymbolSection::Section(text)
            } else {
                SymbolSection::Undefined
            },
            flags: SymbolFlags::None,
        });
    }
    o.write().unwrap()
}

#[test]
fn unwind_audit_accepts_only_weak_undefined_frame_registration() {
    let none = BTreeMap::new();
    let ok = elf_with(&[
        ("main", true, false),
        ("__register_frame_info", false, true),
        ("__deregister_frame_info", false, true),
    ]);
    let j = unwind_audit(&ok, &none).unwrap();
    let allowed: Vec<&str> = j["allowed"]
        .as_array()
        .unwrap()
        .iter()
        .map(|a| a["symbol"].as_str().unwrap())
        .collect();
    assert_eq!(
        allowed,
        ["__deregister_frame_info", "__register_frame_info"]
    );
    assert!(j["allowed"][0]["reason"].as_str().unwrap().contains("weak"));
    // `STT_FILE` source names of collected members are not symbols of the unwinder.
    let mut o = WObject::new(BinaryFormat::Elf, Architecture::Aarch64, Endianness::Little);
    o.add_file_symbol(b"libunwind.cpp".to_vec());
    o.add_file_symbol(b"UnwindLevel1.c".to_vec());
    unwind_audit(&o.write().unwrap(), &none).unwrap();
    // No unwinder names at all: nothing allowed, nothing rejected.
    let plain = unwind_audit(&elf_with(&[("main", true, false)]), &none).unwrap();
    assert_eq!(plain["allowed"], serde_json::json!([]));

    for (bad, what) in [
        (
            ("_Unwind_Resume", false, false),
            "_Unwind_Resume (undefined)",
        ),
        (("_Unwind_Resume", true, false), "_Unwind_Resume (defined)"),
        (
            ("_Unwind_Backtrace", false, true),
            "_Unwind_Backtrace (undefined)",
        ),
        (("unw_getcontext", true, false), "unw_getcontext (defined)"),
        (
            ("__register_frame", true, false),
            "__register_frame (defined)",
        ),
        (
            ("__register_frame_info", false, false),
            "__register_frame_info (undefined)",
        ),
        (
            ("__register_frame_info", true, true),
            "__register_frame_info (defined)",
        ),
        (
            ("__deregister_frame_info_bases", false, true),
            "__deregister_frame_info_bases (undefined)",
        ),
    ] {
        let e = unwind_audit(&elf_with(&[("main", true, false), bad]), &none).unwrap_err();
        assert!(format!("{e:#}").contains(what), "{what}: {e:#}");
    }
}

#[test]
fn unwind_audit_rejects_retained_libunwind_sections() {
    let ok = elf_with(&[("main", true, false)]);
    let mut members = BTreeMap::new();
    // Extracted but entirely collected by `--gc-sections`: allowed.
    members.insert(
        "work/self-contained/libunwind.a(UnwindLevel1.o)".to_string(),
        Member::default(),
    );
    unwind_audit(&ok, &members).unwrap();
    let mut retained = Member::default();
    retained
        .retained
        .insert(".text._Unwind_Resume".into(), 0x40);
    members.insert(
        "work/self-contained/libunwind.a(UnwindLevel1-gcc-ext.o)".to_string(),
        retained,
    );
    let e = unwind_audit(&ok, &members).unwrap_err();
    assert!(
        format!("{e:#}").contains("libunwind.a(UnwindLevel1-gcc-ext.o)"),
        "{e:#}"
    );
}

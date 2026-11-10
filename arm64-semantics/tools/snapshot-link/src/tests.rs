// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Unit tests for `snapshot-link` (`[TEST ONLY]`).

use crate::link::{
    ExternData, Image, ImageDataLayout, ImageLayout, ImageLayoutKind, MUSL_STRING_MEMBERS, PAGE,
    Pinned, Stub, check_disjoint, check_no_duplicate_strong_defs, effective_native_only,
    effective_stub_mode, extract_musl_string_objects, got_sym, image_extent, image_extent_with,
    image_support_asm, image_support_asm_in, image_support_asm_in_pagesep,
    image_support_asm_pagesep, img_prefix, link_images, linker_script, linker_script_full,
    linker_script_full_pagesep, linker_script_images, linker_script_pagesep, musl_inputs, obj_file,
    pinned_sections, place_bases, prepare_object_bytes, resolve_externs, run,
    rust_encoded_rustflags, sha256, stage_runtime_inputs, stub_asm, stub_asm_with, tool,
    tool_from_env, validate_branch_stubs,
};
use crate::verify::{self, b_target, encode_b};
use crate::{Cli, StubMode};
use clap::Parser;
use object::{Architecture, BinaryFormat, Endianness, Object, SectionKind};
use rust_obj2lean::trusted_common::{ExternDecl, ExternKind};
use rust_obj2lean::untrusted_driver;
use rust_obj2lean::untrusted_legacy_linker;
use std::collections::HashMap;
use std::ffi::OsStr;
use std::path::{Path, PathBuf};
use std::process::Command;

fn find_test_objcopy() -> Option<PathBuf> {
    if let Some(p) = std::env::var_os("LLVM_OBJCOPY").filter(|v| !v.is_empty()) {
        let pb = PathBuf::from(p);
        if pb.is_file() || which::which(&pb).is_ok() {
            return Some(pb);
        }
    }
    if let Ok(pb) = which::which("llvm-objcopy") {
        return Some(pb);
    }
    if let Ok(out) = std::process::Command::new("rustc")
        .args(["--print", "target-libdir"])
        .output()
        && out.status.success()
    {
        let libdir = PathBuf::from(String::from_utf8_lossy(&out.stdout).trim());
        if let Some(parent) = libdir.parent() {
            let candidate = parent.join("bin").join("llvm-objcopy");
            if candidate.is_file() {
                return Some(candidate);
            }
        }
    }
    for name in [
        "llvm-objcopy-22",
        "llvm-objcopy-21",
        "llvm-objcopy-20",
        "llvm-objcopy-19",
        "llvm-objcopy-18",
    ] {
        if let Ok(pb) = which::which(name) {
            return Some(pb);
        }
    }
    None
}

pub(crate) fn find_test_lld() -> Option<PathBuf> {
    if let Ok(pb) = tool("LLD", "ld.lld") {
        return Some(pb);
    }
    if let Ok(out) = std::process::Command::new("rustc")
        .args(["--print", "target-libdir"])
        .output()
        && out.status.success()
    {
        let libdir = PathBuf::from(String::from_utf8_lossy(&out.stdout).trim());
        if let Some(parent) = libdir.parent() {
            for rel in ["bin/gcc-ld/ld.lld", "bin/ld.lld"] {
                let candidate = parent.join(rel);
                if candidate.is_file() {
                    return Some(candidate);
                }
            }
        }
    }
    None
}

fn synthetic_aarch64_obj_with_debug_str() -> Vec<u8> {
    let mut obj =
        object::write::Object::new(BinaryFormat::Elf, Architecture::Aarch64, Endianness::Little);
    let text = obj.section_id(object::write::StandardSection::Text);
    obj.append_section_data(text, &[0xc0, 0x03, 0x5f, 0xd6], 4); // ret
    obj.add_symbol(object::write::Symbol {
        name: b"__synthetic_runtime_sym".to_vec(),
        value: 0,
        size: 4,
        kind: object::SymbolKind::Text,
        scope: object::SymbolScope::Linkage,
        weak: false,
        section: object::write::SymbolSection::Section(text),
        flags: object::SymbolFlags::None,
    });
    let dbg_str = obj.add_section(Vec::new(), b".debug_str".to_vec(), SectionKind::Debug);
    obj.append_section_data(dbg_str, b"/host/specific/comp/dir\0crt1.c\0", 1);
    obj.write().expect("must emit valid AArch64 ELF object")
}

#[test]
fn stage_runtime_inputs_rejects_duplicate_file_names() {
    let Some(objcopy) = find_test_objcopy() else {
        eprintln!("skipping duplicate-name test: LLVM_OBJCOPY / llvm-objcopy unavailable");
        return;
    };
    let dir = tempfile::tempdir().unwrap();
    let a = dir.path().join("a").join("crt1.o");
    let b = dir.path().join("b").join("crt1.o");
    let stage = dir.path().join("stage");
    std::fs::create_dir_all(a.parent().unwrap()).unwrap();
    std::fs::create_dir_all(b.parent().unwrap()).unwrap();
    let bytes = synthetic_aarch64_obj_with_debug_str();
    std::fs::write(&a, &bytes).unwrap();
    std::fs::write(&b, &bytes).unwrap();

    let err = stage_runtime_inputs(&objcopy, &[a, b], &stage).unwrap_err();
    assert!(
        err.to_string()
            .contains("duplicate runtime input file name"),
        "{err}"
    );
}

#[test]
fn stage_runtime_inputs_strips_debug_str_and_keeps_file_names() {
    let Some(objcopy) = find_test_objcopy() else {
        eprintln!("skipping stage_runtime_inputs test: LLVM_OBJCOPY / llvm-objcopy unavailable");
        return;
    };
    let dir = tempfile::tempdir().unwrap();
    let src_dir = dir.path().join("src");
    let stage_dir = dir.path().join("stage");
    std::fs::create_dir_all(&src_dir).unwrap();

    let crt1_src = src_dir.join("crt1.o");
    let crtn_src = src_dir.join("crtn.o");
    let obj_bytes = synthetic_aarch64_obj_with_debug_str();
    std::fs::write(&crt1_src, &obj_bytes).unwrap();
    std::fs::write(&crtn_src, &obj_bytes).unwrap();

    let parsed_before = object::File::parse(obj_bytes.as_slice()).unwrap();
    assert!(parsed_before.section_by_name(".debug_str").is_some());
    assert!(parsed_before.section_by_name(".text").is_some());

    let staged = stage_runtime_inputs(&objcopy, &[crt1_src, crtn_src], &stage_dir)
        .expect("staging succeeds");
    assert_eq!(
        staged,
        vec![stage_dir.join("crt1.o"), stage_dir.join("crtn.o")]
    );

    let stripped_bytes = std::fs::read(&staged[0]).unwrap();
    let parsed_after = object::File::parse(stripped_bytes.as_slice()).unwrap();
    assert!(
        parsed_after.section_by_name(".debug_str").is_none(),
        "expected .debug_str to be stripped"
    );
    assert!(
        parsed_after.section_by_name(".text").is_some(),
        "expected .text to remain intact"
    );

    let dup_err = stage_runtime_inputs(
        &objcopy,
        &[dir.path().join("other").join("crt1.o")],
        &stage_dir,
    )
    .unwrap_err();
    assert!(
        dup_err
            .to_string()
            .contains("duplicate runtime input file name"),
        "{dup_err}"
    );

    // Build two GNU archives whose member paths have distinct directory prefixes (covering both
    // `<= 15`-byte and `> 15`-byte basenames plus `/` symbol-index offset rebasing) and verify
    // `stage_runtime_inputs` produces valid, byte-identical `.a` files.
    let make_gnu_archive = |members: &[(&str, &[u8])]| -> Vec<u8> {
        let mut strtab = Vec::new();
        let mut hdr_names = Vec::new();
        for (name, _) in members {
            if name.len() <= 15 && !name.contains('/') {
                let mut f = [b' '; 16];
                f[..name.len()].copy_from_slice(name.as_bytes());
                f[name.len()] = b'/';
                hdr_names.push(f);
            } else {
                let off = strtab.len();
                strtab.extend_from_slice(name.as_bytes());
                strtab.extend_from_slice(b"/\n");
                let mut f = [b' '; 16];
                f.copy_from_slice(format!("/{off:<15}").as_bytes());
                hdr_names.push(f);
            }
        }
        let mut sym_names = Vec::new();
        for _ in members {
            sym_names.extend_from_slice(b"__synthetic_runtime_sym\0");
        }
        let sym_size = 4 + 4 * members.len() + sym_names.len();
        let sym_sec_len = 60 + sym_size + (sym_size % 2);
        let str_sec_len = if strtab.is_empty() {
            0
        } else {
            60 + strtab.len() + (strtab.len() % 2)
        };
        let mut member_pos = 8 + sym_sec_len + str_sec_len;
        let mut sym_data = Vec::with_capacity(sym_size);
        sym_data.extend_from_slice(&(members.len() as u32).to_be_bytes());
        for (_, payload) in members {
            sym_data.extend_from_slice(&(member_pos as u32).to_be_bytes());
            member_pos += 60 + payload.len() + (payload.len() % 2);
        }
        sym_data.extend_from_slice(&sym_names);

        let mut ar = Vec::from(&b"!<arch>\n"[..]);
        let mut sym_hdr = [b' '; 60];
        sym_hdr[0] = b'/';
        sym_hdr[48..58].copy_from_slice(format!("{:<10}", sym_data.len()).as_bytes());
        sym_hdr[58..60].copy_from_slice(b"`\n");
        ar.extend_from_slice(&sym_hdr);
        ar.extend_from_slice(&sym_data);
        if ar.len() % 2 == 1 {
            ar.push(b'\n');
        }
        if !strtab.is_empty() {
            let mut st_hdr = [b' '; 60];
            st_hdr[..2].copy_from_slice(b"//");
            st_hdr[48..58].copy_from_slice(format!("{:<10}", strtab.len()).as_bytes());
            st_hdr[58..60].copy_from_slice(b"`\n");
            ar.extend_from_slice(&st_hdr);
            ar.extend_from_slice(&strtab);
            if ar.len() % 2 == 1 {
                ar.push(b'\n');
            }
        }
        for ((_, payload), f) in members.iter().zip(hdr_names) {
            let mut m_hdr = [b' '; 60];
            m_hdr[..16].copy_from_slice(&f);
            m_hdr[16..28].copy_from_slice(b"0           ");
            m_hdr[28..34].copy_from_slice(b"0     ");
            m_hdr[34..40].copy_from_slice(b"0     ");
            m_hdr[40..48].copy_from_slice(b"644     ");
            m_hdr[48..58].copy_from_slice(format!("{:<10}", payload.len()).as_bytes());
            m_hdr[58..60].copy_from_slice(b"`\n");
            ar.extend_from_slice(&m_hdr);
            ar.extend_from_slice(payload);
            if ar.len() % 2 == 1 {
                ar.push(b'\n');
            }
        }
        ar
    };

    let ar_a = dir.path().join("cache_a").join("libzigc.a");
    let ar_b = dir.path().join("cache_b").join("libzigc.a");
    std::fs::create_dir_all(ar_a.parent().unwrap()).unwrap();
    std::fs::create_dir_all(ar_b.parent().unwrap()).unwrap();
    std::fs::write(
        &ar_a,
        make_gnu_archive(&[
            ("d/libzigc_zcu.o", &obj_bytes),
            (
                "/home/alice/.cache/zig/o/cafe/compiler_rt_long_member.o",
                &obj_bytes,
            ),
        ]),
    )
    .unwrap();
    std::fs::write(
        &ar_b,
        make_gnu_archive(&[
            (
                "/tmp/very/different/global/zig/cache/o/deadbeef/libzigc_zcu.o",
                &obj_bytes,
            ),
            (
                "/tmp/very/different/global/zig/cache/o/cafe/compiler_rt_long_member.o",
                &obj_bytes,
            ),
        ]),
    )
    .unwrap();

    let stage_a = dir.path().join("stage_ar_a");
    let stage_b = dir.path().join("stage_ar_b");
    let out_a = stage_runtime_inputs(&objcopy, &[ar_a], &stage_a).unwrap();
    let out_b = stage_runtime_inputs(&objcopy, &[ar_b], &stage_b).unwrap();
    assert_eq!(out_a, vec![stage_a.join("libzigc.a")]);
    assert_eq!(out_b, vec![stage_b.join("libzigc.a")]);
    let bytes_a = std::fs::read(&out_a[0]).unwrap();
    let bytes_b = std::fs::read(&out_b[0]).unwrap();
    assert_eq!(
        bytes_a, bytes_b,
        "staged archives from distinct cache dirs must match byte-for-byte"
    );
    assert!(!String::from_utf8_lossy(&bytes_a).contains("alice"));
    let parsed_ar = object::read::archive::ArchiveFile::parse(bytes_a.as_slice()).unwrap();
    let member_names: Vec<String> = parsed_ar
        .members()
        .map(|m| String::from_utf8(m.unwrap().name().to_vec()).unwrap())
        .collect();
    assert_eq!(
        member_names,
        vec!["libzigc_zcu.o", "compiler_rt_long_member.o"]
    );
    let sym_targets: Vec<Vec<u8>> = parsed_ar
        .symbols()
        .unwrap()
        .unwrap()
        .map(|s| {
            let s = s.unwrap();
            let member = parsed_ar.member(s.offset()).unwrap();
            member.data(bytes_a.as_slice()).unwrap().to_vec()
        })
        .collect();
    assert_eq!(sym_targets.len(), 2);
    for mbytes in &sym_targets {
        let mf = object::File::parse(mbytes.as_slice()).unwrap();
        assert!(mf.section_by_name(".debug_str").is_none());
    }
}

#[test]
fn b_target_decodes_forward_and_backward() {
    assert_eq!(b_target(0x1400_0001, 0x1000), Some(0x1004));
    assert_eq!(b_target(0x17ff_ffff, 0x1000), Some(0xffc));
    assert_eq!(b_target(0x9400_0001, 0x1000), None); // bl
    assert_eq!(b_target(0, 0x1000), None);
}

#[test]
fn encode_b_roundtrips_and_enforces_range() {
    for &(pc, target) in &[
        (0x40_0000, 0x40_0000),
        (0x49_722c, 0x4b_c000),
        (0x4b_c324, 0x4b_c040), // backward branch like memmove -> memcpy
        (0x1000_0000, 0x1000_0000 + 0x07ff_fffc),
        (0x1000_0000, 0x1000_0000 - 0x0800_0000),
    ] {
        let w = encode_b(pc, target).expect("in-range aligned displacement");
        assert_eq!(b_target(w, pc), Some(target));
    }
    assert_eq!(encode_b(0x1000_0000, 0x1000_0002), None); // unaligned
    assert_eq!(encode_b(0x1000_0000, 0x1000_0000 + 0x0800_0000), None); // +128 MiB out of range
    assert_eq!(encode_b(0x1000_0000, 0x1000_0000 - 0x0800_0004), None); // -128 MiB - 4 out of range
}

#[test]
fn stub_asm_modes() {
    let stubs = [Stub {
        raw: "memset".into(),
        off: 0x10,
    }];
    let b = stub_asm(&stubs, StubMode::Branch);
    assert!(b.contains("__snapstub_0:\nb \"memset\"\n"), "{b}");
    assert!(b.contains(".section .text.__snapstub_0,\"ax\""));
    let z = stub_asm(&stubs, StubMode::Zero);
    assert!(z.contains("__snapstub_0:\n.word 0\n"), "{z}");
}

#[test]
fn stub_asm_mixed_emits_branch_only_for_selected_externs() {
    let stubs = [
        Stub {
            raw: "memcpy".into(),
            off: 0x10,
        },
        Stub {
            raw: "_RNv_from_utf8".into(),
            off: 0x14,
        },
        Stub {
            raw: "memrchr".into(),
            off: 0x18,
        },
        Stub {
            raw: "bcmp".into(),
            off: 0x1c,
        },
    ];
    let branch_stubs: Vec<String> = ["memcpy", "bcmp"].into_iter().map(String::from).collect();
    validate_branch_stubs(&stubs, &branch_stubs).unwrap();
    let mixed_from_zero = stub_asm_with(&stubs, StubMode::Zero, &branch_stubs);
    let mixed_explicit = stub_asm_with(&stubs, StubMode::Mixed, &branch_stubs);
    assert_eq!(mixed_from_zero, mixed_explicit);
    assert!(mixed_from_zero.contains("__snapstub_0:\nb \"memcpy\"\n"));
    assert!(mixed_from_zero.contains("__snapstub_1:\n.word 0\n"));
    assert!(mixed_from_zero.contains("__snapstub_2:\n.word 0\n"));
    assert!(mixed_from_zero.contains("__snapstub_3:\nb \"bcmp\"\n"));
}

#[test]
fn validate_branch_stubs_rejects_unknown_names() {
    let stubs = [
        Stub {
            raw: "memcpy".into(),
            off: 0x10,
        },
        Stub {
            raw: "bcmp".into(),
            off: 0x14,
        },
    ];
    validate_branch_stubs(&stubs, &[]).unwrap();
    validate_branch_stubs(&stubs, &["memcpy".into(), "bcmp".into()]).unwrap();

    let err = validate_branch_stubs(
        &stubs,
        &[
            "memcpy".into(),
            "missing_stub_one".into(),
            "missing_stub_two".into(),
            "missing_stub_one".into(),
        ],
    )
    .expect_err("unknown --branch-stubs names must be rejected");
    let msg = format!("{err:#}");
    assert!(
        msg.contains("missing_stub_one, missing_stub_two"),
        "expected unknown names in error, got: {msg}"
    );
}

#[test]
fn validate_and_match_branch_stubs_accepts_demangled_rust_symbols() {
    let raw_once = "_RNvMs0_NtNtNtNtCs1234_3std3sys4sync4once5futexNtB5_4Once4call";
    let raw_probe = "_ZN6widget5probe17h0000000000000001E";
    let stubs = [
        Stub {
            raw: raw_once.into(),
            off: 0x10,
        },
        Stub {
            raw: raw_probe.into(),
            off: 0x14,
        },
        Stub {
            raw: "abort".into(),
            off: 0x18,
        },
    ];
    let branch = vec![
        "<std::sys::sync::once::futex::Once>::call".to_string(),
        "widget::probe".to_string(),
    ];
    validate_branch_stubs(&stubs, &branch).unwrap();
    assert_eq!(
        effective_stub_mode(raw_once, StubMode::Zero, &branch),
        StubMode::Branch
    );
    assert_eq!(
        effective_stub_mode(raw_probe, StubMode::Zero, &branch),
        StubMode::Branch
    );
    assert_eq!(
        effective_stub_mode("abort", StubMode::Zero, &branch),
        StubMode::Zero
    );
}

#[test]
fn link_images_extracts_rlib_branch_stubs_and_traps_unbranched_panics() {
    if !have_link_tools() {
        return;
    }
    let zig = rust_obj2lean::untrusted_driver::find_zig_binary("snapshot-link-test").unwrap();
    let dir = tempfile::tempdir().unwrap();
    let raw_probe = "_ZN6widget5probe17h0000000000000001E";
    let raw_panic = "_ZN4core9panicking9panic_fmt17h0000000000000002E";

    // Build an image object exporting `entry_check` that calls `widget::probe` and has an
    // unreachable reference to `core::panicking::panic_fmt`.
    let img_asm = format!(
        r#"
        .section .text.entry_check,"ax",@progbits
        .p2align 2
        .globl entry_check
        .type entry_check,@function
    entry_check:
        stp x29, x30, [sp, #-16]!
        bl {raw_probe}
        cmp w0, #42
        b.ne .Ltrap
        mov w0, #0
        ldp x29, x30, [sp], #16
        ret
    .Ltrap:
        bl {raw_panic}
        .size entry_check, .-entry_check
        "#
    );
    std::fs::write(dir.path().join("img.s"), img_asm).unwrap();
    assert!(
        Command::new(&zig)
            .current_dir(dir.path())
            .args([
                "cc",
                "-target",
                "aarch64-linux-musl",
                "-g0",
                "-c",
                "img.s",
                "-o",
                "img.o"
            ])
            .status()
            .unwrap()
            .success()
    );

    // Build a synthetic `.rlib` archive with `widget::probe` (which has unreachable calls to the
    // unbranched panic stub and `_Unwind_Resume`) plus an unreachable `.text.dead` section calling
    // a missing symbol that must be stripped by reachability trimming.
    let rlib_asm = format!(
        r#"
        .section .text.{raw_probe},"ax",@progbits
        .p2align 2
        .globl {raw_probe}
        .type {raw_probe},@function
    {raw_probe}:
        cbz x30, .Lunreach
        mov w0, #42
        ret
    .Lunreach:
        stp x29, x30, [sp, #-16]!
        bl {raw_panic}
        bl _Unwind_Resume
        .size {raw_probe}, .-{raw_probe}

        .section .text.dead_unkept,"ax",@progbits
        .p2align 2
        .globl dead_unkept
        .type dead_unkept,@function
    dead_unkept:
        bl nonexistent_external_symbol
        ret
        .size dead_unkept, .-dead_unkept
        "#
    );
    std::fs::write(dir.path().join("widget.s"), rlib_asm).unwrap();
    assert!(
        Command::new(&zig)
            .current_dir(dir.path())
            .args([
                "cc",
                "-target",
                "aarch64-linux-musl",
                "-g0",
                "-c",
                "widget.s",
                "-o",
                "widget.rcgu.o",
            ])
            .status()
            .unwrap()
            .success()
    );
    let rlib_path = dir.path().join("libwidget-0123456789abcdef.rlib");
    assert!(
        Command::new(&zig)
            .current_dir(dir.path())
            .args(["ar", "rcs", rlib_path.to_str().unwrap(), "widget.rcgu.o"])
            .status()
            .unwrap()
            .success()
    );

    let o = rust_obj2lean::trusted_extractor::parse_object(
        "alpha",
        std::fs::read(dir.path().join("img.o")).unwrap(),
    )
    .unwrap();
    let externs = vec![
        ExternDecl {
            name: "widget::probe".to_string(),
            raw_name: raw_probe.to_string(),
            kind: ExternKind::Func,
            size: 0,
            align: 4,
            origin: String::new(),
        },
        ExternDecl {
            name: "core::panicking::panic_fmt".to_string(),
            raw_name: raw_panic.to_string(),
            kind: ExternKind::Func,
            size: 0,
            align: 4,
            origin: String::new(),
        },
    ];
    let li = untrusted_legacy_linker::link_with_layout(
        std::slice::from_ref(&o),
        &externs,
        0,
        untrusted_legacy_linker::DataLayout::PageSeparated,
    )
    .unwrap();
    let im = Image {
        objects: vec![o],
        externs,
        li,
        page_separate_data: true,
        rlibs: vec![rlib_path],
    };

    let main_c = dir.path().join("main.c");
    std::fs::write(
        &main_c,
        "extern __attribute__((weak)) int entry_check(void);\nint main(void) { return entry_check(); }\n",
    )
    .unwrap();
    let out_dir = dir.path().join("out");
    let cli = Cli::parse_from([
        "snapshot-link",
        "--config",
        "alpha.toml",
        "--out-dir",
        out_dir.to_str().unwrap(),
        "--stubs",
        "zero",
        "--branch-stubs",
        "widget::probe",
        "--page-separate-data",
        "--main-c",
        main_c.to_str().unwrap(),
    ]);
    link_images(&cli, dir.path(), "rustc 1.98.1", &[im])
        .expect("linking with rlib branch stub must succeed");

    assert!(out_dir.join("work/rlib/widget.o").is_file());
    assert!(out_dir.join("work/rlib/unwind_trap.o").is_file());
    if let Some(q) = qemu() {
        let status = Command::new(q).arg(out_dir.join("prog")).status().unwrap();
        assert!(status.success(), "expected exit 0 under qemu, got {status}");
    }
}

#[test]
fn tool_missing_fails_loudly_without_rustup_fallback() {
    // Explicit env override wins even when `PATH` is empty.
    let explicit = tool_from_env(
        "LLVM_OBJCOPY",
        Some(OsStr::new("/custom/bin/llvm-objcopy")),
        "llvm-objcopy",
        Some(OsStr::new("/nonexistent")),
    )
    .unwrap();
    assert_eq!(explicit, PathBuf::from("/custom/bin/llvm-objcopy"));

    // Without `$LLVM_OBJCOPY` and with `/nonexistent` `PATH`, `tool_from_env` must fail loudly
    // even when `rustup` toolchains have `llvm-tools` installed on disk.
    let err = tool_from_env(
        "LLVM_OBJCOPY",
        None,
        "llvm-objcopy",
        Some(OsStr::new("/nonexistent")),
    )
    .expect_err("missing tool must fail rather than falling back to rustup toolchains");
    let msg = format!("{err:#}");
    assert!(msg.contains("llvm-objcopy"), "missing tool name: {msg}");
    assert!(msg.contains("$LLVM_OBJCOPY"), "missing env var hint: {msg}");
    assert!(
        msg.contains("rustup component add llvm-tools"),
        "missing llvm-tools installation hint: {msg}"
    );
    assert!(
        msg.contains("rustc --print target-libdir"),
        "missing target-libdir bin path hint: {msg}"
    );
}

#[test]
fn linker_script_pins_sections() {
    let p = |sec: &str, off, size| Pinned {
        file: "img0.o".into(),
        sec: sec.into(),
        off,
        size,
    };
    let s = linker_script(
        0x40_0000,
        &[p(".text", 0, 0x40), p(".text.f", 0x40, 0x20)],
        &[Stub {
            raw: "free".into(),
            off: 0x80,
        }],
        &[p(".rodata", 0x1000, 16)],
        &[],
    );
    assert!(s.contains(". = 0x3ff000 + SIZEOF_HEADERS;"));
    assert!(
        s.contains("    . = 0x400040;\n    *img0.o(\".text.f\")\n"),
        "{s}"
    );
    assert!(s.contains("    . = 0x400080;\n    *(.text.__snapstub_0)\n"));
    assert!(s.contains("  . = 0x401000;\n  .img.data : {\n    . = 0x401000;\n"));
    assert!(s.contains("} :imgtext =0"));
}

#[test]
fn linker_script_pagesep_pins_sections() {
    let p = |sec: &str, off, size| Pinned {
        file: "img0.o".into(),
        sec: sec.into(),
        off,
        size,
    };
    let s = linker_script_pagesep(
        0x40_0000,
        &[p(".text", 0, 0x40), p(".text.f", 0x40, 0x20)],
        &[Stub {
            raw: "free".into(),
            off: 0x80,
        }],
        &[p(".rodata", 0x1000, 16)],
        &[],
    );
    assert!(s.contains(". = 0x3ff000 + SIZEOF_HEADERS;"));
    assert!(
        s.contains("    . = 0x400040;\n    *img0.o(\".text.f\")\n"),
        "{s}"
    );
    assert!(s.contains("    . = 0x400080;\n    *(.text.__snapstub_0)\n"));
    assert!(
        s.contains("  . = 0x401000;\n  .img.rodata : {\n    . = 0x401000;\n"),
        "{s}"
    );
    assert!(s.contains("} :imgtext =0"));
    assert!(s.contains("imgtext PT_LOAD FLAGS(5);"), "{s}");
    assert!(s.contains("imgro PT_LOAD FLAGS(4);"), "{s}");
}

#[test]
fn musl_inputs_splits_link_line() {
    let v = "info\n/z/ld.lld -o libc.so /c/x.o /c/y.a\n/z/ld.lld -o probe /c/crt1.o /c/crti.o /w/main.o --start-group /c/libc.a \
             /c/libcompiler_rt.a --end-group /c/crtn.o\n";
    let (pre, libs, post) = musl_inputs(v, Path::new("/w/main.o")).unwrap();
    assert_eq!(
        pre,
        [PathBuf::from("/c/crt1.o"), PathBuf::from("/c/crti.o")]
    );
    assert_eq!(libs.len(), 2);
    assert_eq!(post, [PathBuf::from("/c/crtn.o")]);
    assert!(musl_inputs(v, Path::new("/x/main.o")).is_err());
}

#[test]
fn support_asm_and_script_include_extern_data_and_got() {
    let ext = [ExternData {
        raw: "_RNv_ext_table".into(),
        off: 0x1100,
        size: 16,
    }];
    let asm = image_support_asm(&[], &ext, &[0x10, 0x40_0040], StubMode::Zero);
    assert!(
        asm.contains(".section .rodata.__snapextdata_0,\"a\",@progbits")
            && asm.contains(".zero 16\n.size __snapextdata_0,16\n"),
        "{asm}"
    );
    assert!(
        asm.contains(".section .rodata.__snapgot,\"a\",@progbits")
            && asm.contains(".quad 0x10\n.quad 0x400040\n.size __snapgot,16\n"),
        "{asm}"
    );
    let p = |sec: &str, off, size| Pinned {
        file: "img0.o".into(),
        sec: sec.into(),
        off,
        size,
    };
    let s = linker_script_full(
        0x40_0000,
        &[p(".text", 0, 16)],
        &[],
        &[p(".rodata", 0x1000, 16)],
        &[],
        &ext,
        Some(0x1110),
        false,
    );
    assert!(
        s.contains(
            "  .img.extdata : {\n    . = 0x401100;\n    *(.rodata.__snapextdata_0)\n  } :imgdata\n"
        ),
        "{s}"
    );
    assert!(
        s.contains("  . = 0x401110;\n  .img.got : {\n    . = 0x401110;\n    *(.rodata.__snapgot)\n  } :imgdata\n"),
        "{s}"
    );
    let kept = linker_script_full(
        0x40_0000,
        &[p(".text", 0, 16)],
        &[],
        &[p(".rodata", 0x1000, 16)],
        &[],
        &ext,
        Some(0x1110),
        true,
    );
    assert!(kept.contains("KEEP(*img0.o(\".text\"))"), "{kept}");
    assert!(kept.contains("KEEP(*(.rodata.__snapextdata_0))"), "{kept}");
    assert!(kept.contains("KEEP(*(.rodata.__snapgot))"), "{kept}");
}

#[test]
fn support_asm_and_script_pagesep_include_extern_data_and_got() {
    let ext = [ExternData {
        raw: "_RNv_ext_table".into(),
        off: 0x2020,
        size: 16,
    }];
    let asm = image_support_asm_pagesep(&[], &ext, &[0x10, 0x40_0040], StubMode::Zero);
    assert!(
        asm.contains(".section .data.__snapextdata_0,\"aw\",@progbits")
            && asm.contains(".zero 16\n.size __snapextdata_0,16\n"),
        "{asm}"
    );
    assert!(
        asm.contains(".section .rodata.__snapgot,\"a\",@progbits")
            && asm.contains(".quad 0x10\n.quad 0x400040\n.size __snapgot,16\n"),
        "{asm}"
    );
    let p = |sec: &str, off, size| Pinned {
        file: "img0.o".into(),
        sec: sec.into(),
        off,
        size,
    };
    let layout = ImageDataLayout {
        data_off: 0x1000,
        ro_end: 0x2000,
        data_bytes_end: 0x2010,
        data_end: 0x2020,
        got: Some((0x3000, 16)),
    };
    let s = linker_script_full_pagesep(
        0x40_0000,
        &[p(".text", 0, 16)],
        &[],
        &[p(".rodata", 0x1000, 16)],
        &[p(".data", 0x2000, 16)],
        &[p(".bss", 0x2010, 16)],
        &ext,
        layout,
        false,
    );
    assert!(s.contains("imgtext PT_LOAD FLAGS(5);"), "{s}");
    assert!(s.contains("imgro PT_LOAD FLAGS(4);"), "{s}");
    assert!(s.contains("imgdata PT_LOAD FLAGS(6);"), "{s}");
    assert!(s.contains("imggot PT_LOAD FLAGS(4);"), "{s}");
    assert!(
        s.contains(
            "  .img.extdata : {\n    . = 0x402020;\n    *(.data.__snapextdata_0)\n  } :imgdata =0\n"
        ),
        "{s}"
    );
    assert!(
        s.contains("  . = 0x403000;\n  .img.got : {\n    . = 0x403000;\n    *(.rodata.__snapgot)\n  } :imggot =0\n"),
        "{s}"
    );
    assert!(s.contains(".img.got.pad : {"), "{s}");
    let kept = linker_script_full_pagesep(
        0x40_0000,
        &[p(".text", 0, 16)],
        &[],
        &[p(".rodata", 0x1000, 16)],
        &[p(".data", 0x2000, 16)],
        &[p(".bss", 0x2010, 16)],
        &ext,
        layout,
        true,
    );
    assert!(kept.contains("KEEP(*img0.o(\".text\"))"), "{kept}");
    assert!(kept.contains("KEEP(*(.data.__snapextdata_0))"), "{kept}");
    assert!(kept.contains("KEEP(*(.rodata.__snapgot))"), "{kept}");
}

#[test]
fn rust_encoded_rustflags_pins_static_model_and_path_remaps() {
    let flags = rust_encoded_rustflags(
        Path::new("/host/repo"),
        Path::new("/tmp/work"),
        Some(Path::new("/home/u/.cargo")),
        Some(Path::new("/home/u/.rustup")),
        Some((
            Path::new("/home/u/.rustup/toolchains/stable-x86_64-unknown-linux-gnu"),
            "0123456789abcdef",
        )),
    );
    let parts: Vec<&str> = flags.split('\x1f').collect();
    assert!(
        parts
            .windows(2)
            .any(|w| w == ["-C", "relocation-model=static"])
    );
    assert!(parts.windows(2).any(|w| w == ["-C", "strip=debuginfo"]));
    assert!(parts.windows(2).any(|w| w == ["-C", "no-vectorize-loops"]));
    assert!(parts.windows(2).any(|w| w == ["-C", "no-vectorize-slp"]));
    assert!(parts.windows(2).any(|w| w == ["-C", "target-cpu=generic"]));
    assert!(parts.contains(&"--remap-path-prefix=/tmp/work=/work"));
    assert!(parts.contains(&"--remap-path-prefix=/host/repo=/src"));
    assert!(parts.contains(&"--remap-path-prefix=/home/u/.cargo=/cargo"));
    let rustup_pos = parts
        .iter()
        .position(|&p| p == "--remap-path-prefix=/home/u/.rustup=/rustup")
        .unwrap();
    let sysroot_pos = parts
        .iter()
        .position(|&p| {
            p == "--remap-path-prefix=/home/u/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust=/rustc/0123456789abcdef"
        })
        .unwrap();
    assert!(
        rustup_pos < sysroot_pos,
        "nested sysroot rust-src remap must follow rustup_home remap so last match wins"
    );
}

// ---- Single-image goldens: both the default interleaved (`src/testdata/single_image*`) and
// opt-in page-separated (`src/testdata/single_image_pagesep*`) linker scripts and support
// assembly are pinned byte for byte so committed ELF fixtures and opt-in links stay reproducible.

fn golden_fixture() -> (
    Vec<Pinned>,
    Vec<Stub>,
    Vec<Pinned>,
    Vec<Pinned>,
    Vec<ExternData>,
) {
    let p = |sec: &str, off, size| Pinned {
        file: "img0.o".into(),
        sec: sec.into(),
        off,
        size,
    };
    (
        vec![p(".text", 0, 0x40), p(".text.f", 0x40, 0x40)],
        vec![Stub {
            raw: "free".into(),
            off: 0x80,
        }],
        vec![p(".rodata", 0x1000, 0x80)],
        vec![p(".bss", 0x1080, 0x80)],
        vec![ExternData {
            raw: "tbl".into(),
            off: 0x1100,
            size: 16,
        }],
    )
}

#[test]
fn single_image_linker_script_is_unchanged() {
    let (text, stubs, data, bss, ext) = golden_fixture();
    for (gc, want) in [
        (false, include_str!("testdata/single_image.ld")),
        (true, include_str!("testdata/single_image_gc.ld")),
    ] {
        let s = linker_script_full(
            0x40_0000,
            &text,
            &stubs,
            &data,
            &bss,
            &ext,
            Some(0x1110),
            gc,
        );
        assert_eq!(s, want, "gc_sections = {gc}");
    }
    let p = |sec: &str, off, size| Pinned {
        file: "img0.o".into(),
        sec: sec.into(),
        off,
        size,
    };
    let s = linker_script(
        0x40_0000,
        &[p(".text", 0, 0x40)],
        &[],
        &[p(".rodata", 0x1000, 0x10)],
        &[p(".bss", 0x1010, 0x10)],
    );
    assert_eq!(s, include_str!("testdata/single_image_plain.ld"));
}

/// A golden `testdata/*.s` file without its leading `/* ... */` license header.
fn without_license_header(golden: &str) -> &str {
    golden.split_once("*/\n\n").map_or(golden, |(_, rest)| rest)
}

#[test]
fn single_image_support_asm_is_unchanged() {
    let (_, stubs, _, _, ext) = golden_fixture();
    let asm = image_support_asm(&stubs, &ext, &[0x10, 0x40_0040], StubMode::Branch);
    assert_eq!(asm, without_license_header(include_str!("testdata/single_image_support.s")));
    assert_eq!(
        image_support_asm_in(0, &stubs, &ext, &[0x10], StubMode::Zero),
        image_support_asm(&stubs, &ext, &[0x10], StubMode::Zero)
    );
}

#[allow(clippy::type_complexity)]
fn golden_pagesep_fixture() -> (
    Vec<Pinned>,
    Vec<Stub>,
    Vec<Pinned>,
    Vec<Pinned>,
    Vec<Pinned>,
    Vec<ExternData>,
    ImageDataLayout,
) {
    let p = |sec: &str, off, size| Pinned {
        file: "img0.o".into(),
        sec: sec.into(),
        off,
        size,
    };
    (
        vec![p(".text", 0, 0x40), p(".text.f", 0x40, 0x40)],
        vec![Stub {
            raw: "free".into(),
            off: 0x80,
        }],
        vec![p(".rodata", 0x1000, 0x80)],
        vec![p(".data", 0x2000, 0x10)],
        vec![p(".bss", 0x2010, 0x10)],
        vec![ExternData {
            raw: "tbl".into(),
            off: 0x2020,
            size: 16,
        }],
        ImageDataLayout {
            data_off: 0x1000,
            ro_end: 0x2000,
            data_bytes_end: 0x2010,
            data_end: 0x2020,
            got: Some((0x3000, 16)),
        },
    )
}

#[test]
fn single_image_pagesep_linker_script_is_unchanged() {
    let (text, stubs, rodata, rw_data, bss, ext, layout) = golden_pagesep_fixture();
    for (gc, want) in [
        (false, include_str!("testdata/single_image_pagesep.ld")),
        (true, include_str!("testdata/single_image_pagesep_gc.ld")),
    ] {
        let s = linker_script_full_pagesep(
            0x40_0000, &text, &stubs, &rodata, &rw_data, &bss, &ext, layout, gc,
        );
        assert_eq!(s, want, "gc_sections = {gc}");
    }
    let p = |sec: &str, off, size| Pinned {
        file: "img0.o".into(),
        sec: sec.into(),
        off,
        size,
    };
    let s = linker_script_pagesep(
        0x40_0000,
        &[p(".text", 0, 0x40)],
        &[],
        &[p(".rodata", 0x1000, 0x10)],
        &[p(".bss", 0x2000, 0x10)],
    );
    assert_eq!(s, include_str!("testdata/single_image_pagesep_plain.ld"));
}

#[test]
fn single_image_pagesep_support_asm_is_unchanged() {
    let (_, stubs, _, _, _, ext, _) = golden_pagesep_fixture();
    let asm = image_support_asm_pagesep(&stubs, &ext, &[0x10, 0x40_0040], StubMode::Branch);
    assert_eq!(asm, without_license_header(include_str!("testdata/single_image_pagesep_support.s")));
    assert_eq!(
        image_support_asm_in_pagesep(0, &stubs, &ext, &[0x10], StubMode::Zero),
        image_support_asm_pagesep(&stubs, &ext, &[0x10], StubMode::Zero)
    );
}

// ---- Multi-image naming, layout and placement.

#[test]
fn per_image_names_are_distinct_and_unambiguous() {
    assert_eq!(obj_file(0, 3), "img3.o");
    assert_eq!(obj_file(2, 3), "img3i2.o");
    assert_eq!(img_prefix(0), ".img.");
    assert_eq!(img_prefix(1), ".img1.");
    assert_eq!(Stub::sym_in(0, 4), "__snapstub_4");
    assert_eq!(Stub::sym_in(1, 4), "__snapstub1_4");
    assert_eq!(ExternData::sym_in(2, 0), "__snapextdata2_0");
    assert_eq!(got_sym(0), "__snapgot");
    assert_eq!(got_sym(3), "__snapgot3");
    // The linker script selects inputs with `*<file>`: no file name may end with another.
    let names: Vec<String> = (0..12)
        .flat_map(|tag| (0..12).map(move |i| obj_file(tag, i)))
        .collect();
    for a in &names {
        for b in &names {
            assert!(a == b || !a.ends_with(b.as_str()), "{a} ends with {b}");
        }
    }
    // A section belongs to exactly one image by prefix.
    for (tag, sec) in [(0, ".img.text"), (1, ".img1.text"), (10, ".img10.got")] {
        for other in [0, 1, 10] {
            assert_eq!(
                sec.starts_with(&img_prefix(other)),
                other == tag,
                "{sec} vs {other}"
            );
        }
    }
}

#[test]
fn linker_script_images_orders_by_base_and_separates_segments() {
    let p = |file: &str, sec: &str, off, size| Pinned {
        file: file.into(),
        sec: sec.into(),
        off,
        size,
    };
    let (ta, da) = (
        [p("img0.o", ".text", 0, 16)],
        [p("img0.o", ".data", 0x1000, 16)],
    );
    let tb = [p("img0i1.o", ".text", 0, 16)];
    let sb = [Stub {
        raw: "memset".into(),
        off: 0x10,
    }];
    let a = ImageLayout {
        tag: 0,
        base: 0x48_0000,
        text: &ta,
        stubs: &[],
        bss: &[],
        ext_data: &[],
        kind: ImageLayoutKind::Interleaved {
            data: &da,
            got_off: None,
        },
    };
    let b = ImageLayout {
        tag: 1,
        base: 0x40_0000,
        text: &tb,
        stubs: &sb,
        bss: &[],
        ext_data: &[],
        kind: ImageLayoutKind::Interleaved {
            data: &[],
            got_off: Some(0x1000),
        },
    };
    let s = linker_script_images(&[a, b], false);
    // Headers below the lowest image; image 1 (lower base) first, in PHDRS and SECTIONS.
    assert!(s.contains(". = 0x3ff000 + SIZEOF_HEADERS;"), "{s}");
    let phdrs = "  hdr PT_LOAD FILEHDR PHDRS;\n  imgtext1 PT_LOAD;\n  imgdata1 PT_LOAD;\n  \
                 imgtext PT_LOAD;\n  imgdata PT_LOAD;\n  text PT_LOAD;\n";
    assert!(s.contains(phdrs), "{s}");
    let b_at = s
        .find("  . = 0x400000;\n  .img1.text : {")
        .expect("image 1 block");
    let a_at = s
        .find("  . = 0x480000;\n  .img.text : {")
        .expect("image 0 block");
    assert!(b_at < a_at, "{s}");
    assert!(
        s.contains("    *img0i1.o(\".text\")\n    . = 0x400010;\n    *(.text.__snapstub1_0)\n  } :imgtext1 =0\n"),
        "{s}"
    );
    assert!(
        s.contains(
            "  .img1.got : {\n    . = 0x401000;\n    *(.rodata.__snapgot1)\n  } :imgdata1\n"
        ),
        "{s}"
    );
    assert!(
        s.contains("  . = 0x481000;\n  .img.data : {\n    . = 0x481000;\n    *img0.o(\".data\")\n  } :imgdata\n"),
        "{s}"
    );
    // The C runtime follows the highest image.
    assert!(a_at < s.find("  .text : {").unwrap());
}

#[test]
fn linker_script_images_pagesep_orders_by_base_and_separates_segments() {
    let p = |file: &str, sec: &str, off, size| Pinned {
        file: file.into(),
        sec: sec.into(),
        off,
        size,
    };
    let (ta, da) = (
        [p("img0.o", ".text", 0, 16)],
        [p("img0.o", ".data", 0x1000, 16)],
    );
    let tb = [p("img0i1.o", ".text", 0, 16)];
    let sb = [Stub {
        raw: "memset".into(),
        off: 0x10,
    }];
    let a = ImageLayout {
        tag: 0,
        base: 0x48_0000,
        text: &ta,
        stubs: &[],
        bss: &[],
        ext_data: &[],
        kind: ImageLayoutKind::PageSeparated {
            rodata: &[],
            rw_data: &da,
            layout: ImageDataLayout {
                data_off: 0x1000,
                ro_end: 0x1000,
                data_bytes_end: 0x1010,
                data_end: 0x1010,
                got: None,
            },
        },
    };
    let b = ImageLayout {
        tag: 1,
        base: 0x40_0000,
        text: &tb,
        stubs: &sb,
        bss: &[],
        ext_data: &[],
        kind: ImageLayoutKind::PageSeparated {
            rodata: &[],
            rw_data: &[],
            layout: ImageDataLayout {
                data_off: 0x1000,
                ro_end: 0x1000,
                data_bytes_end: 0x1000,
                data_end: 0x1000,
                got: Some((0x1000, 8)),
            },
        },
    };
    let s = linker_script_images(&[a, b], false);
    assert!(s.contains(". = 0x3ff000 + SIZEOF_HEADERS;"), "{s}");
    let phdrs = "  hdr PT_LOAD FILEHDR PHDRS FLAGS(4);\n  imgtext1 PT_LOAD FLAGS(5);\n  \
                 imggot1 PT_LOAD FLAGS(4);\n  imgtext PT_LOAD FLAGS(5);\n  \
                 imgdata PT_LOAD FLAGS(6);\n  text PT_LOAD FLAGS(5);\n";
    assert!(s.contains(phdrs), "{s}");
    let b_at = s
        .find("  . = 0x400000;\n  .img1.text : {")
        .expect("image 1 block");
    let a_at = s
        .find("  . = 0x480000;\n  .img.text : {")
        .expect("image 0 block");
    assert!(b_at < a_at, "{s}");
    assert!(
        s.contains("    *img0i1.o(\".text\")\n    . = 0x400010;\n    *(.text.__snapstub1_0)\n  } :imgtext1 =0\n"),
        "{s}"
    );
    assert!(
        s.contains(
            "  .img1.got : {\n    . = 0x401000;\n    *(.rodata.__snapgot1)\n  } :imggot1 =0\n"
        ),
        "{s}"
    );
    assert!(s.contains(".img1.got.pad : {"), "{s}");
    assert!(
        s.contains("  . = 0x481000;\n  .img.data : {\n    . = 0x481000;\n    *img0.o(\".data\")\n  } :imgdata =0\n"),
        "{s}"
    );
    assert!(a_at < s.find("  .text : {").unwrap());
}

#[test]
fn place_bases_auto_places_after_earlier_images() {
    // Defaults: the first image at 0x400000, the next on the following page boundary.
    assert_eq!(
        place_bases(&[], &[0x1234, 0x10, 0x1000]).unwrap(),
        vec![0x40_0000, 0x40_2000, 0x40_3000]
    );
    // An explicit base below an earlier image: later automatic images go after all of them.
    assert_eq!(
        place_bases(&[0x50_0000, 0x40_0000], &[0x2000, 0x1000, 0x10]).unwrap(),
        vec![0x50_0000, 0x40_0000, 0x50_2000]
    );
    assert!(place_bases(&[0x40_0800], &[0x10]).is_err());
    assert!(place_bases(&[0], &[0x10]).is_err());
    assert!(place_bases(&[0x40_0000, 0x50_0000], &[0x10]).is_err());
}

#[test]
fn overlapping_bases_are_rejected() {
    let labels = vec!["a.toml".to_string(), "b.toml".to_string()];
    check_disjoint(&labels, &[0x40_0000, 0x40_2000], &[0x2000, 0x10]).unwrap();
    let err = check_disjoint(&labels, &[0x40_0000, 0x40_1000], &[0x2000, 0x10]).unwrap_err();
    let msg = err.to_string();
    assert!(msg.contains("overlaps") && msg.contains("b.toml"), "{msg}");
    // Through the whole recipe (fails before any external tool runs).
    let (a, b) = (image_a(), image_b());
    let dir = tempfile::tempdir().unwrap();
    let cli = multi_cli(dir.path(), &["0x400000", "0x401000"], None);
    let err = link_images(&cli, dir.path(), "", &[a, b]).unwrap_err();
    assert!(err.to_string().contains("overlaps image 1"), "{err}");
}

// ---- Cross-image resolution, on images built from real relocatable objects.

fn words(ws: &[u32]) -> Vec<u8> {
    ws.iter().flat_map(|w| w.to_le_bytes()).collect()
}

/// A relocatable AArch64 object with one `.text` section holding `code`, global functions
/// `defs` (`name`, offset, size), `calls` (`offset`, undefined target, `R_AARCH64_*`), and,
/// with `ptr`, a `.data` pointer `<ptr.0>` holding the address of the function `ptr.1`.
fn fixture_obj(
    code: &[u32],
    defs: &[(&str, u64, u64)],
    calls: &[(u64, &str, u32)],
    ptr: Option<(&str, &str)>,
) -> Vec<u8> {
    use object::write::{Relocation, StandardSection, Symbol, SymbolSection};
    use object::{RelocationFlags, SymbolFlags, SymbolKind, SymbolScope};
    let mut obj =
        object::write::Object::new(BinaryFormat::Elf, Architecture::Aarch64, Endianness::Little);
    let text = obj.section_id(StandardSection::Text);
    obj.append_section_data(text, &words(code), 4);
    let mut ids = std::collections::HashMap::new();
    for &(name, value, size) in defs {
        let id = obj.add_symbol(Symbol {
            name: name.as_bytes().to_vec(),
            value,
            size,
            kind: SymbolKind::Text,
            scope: SymbolScope::Linkage,
            weak: false,
            section: SymbolSection::Section(text),
            flags: SymbolFlags::None,
        });
        ids.insert(name, id);
    }
    for &(offset, target, r_type) in calls {
        let symbol = obj.add_symbol(Symbol {
            name: target.as_bytes().to_vec(),
            value: 0,
            size: 0,
            kind: SymbolKind::Unknown,
            scope: SymbolScope::Linkage,
            weak: false,
            section: SymbolSection::Undefined,
            flags: SymbolFlags::None,
        });
        obj.add_relocation(
            text,
            Relocation {
                offset,
                symbol,
                addend: 0,
                flags: RelocationFlags::Elf { r_type },
            },
        )
        .unwrap();
    }
    if let Some((name, target)) = ptr {
        let data = obj.section_id(StandardSection::Data);
        obj.append_section_data(data, &[0; 8], 8);
        obj.add_symbol(Symbol {
            name: name.as_bytes().to_vec(),
            value: 0,
            size: 8,
            kind: SymbolKind::Data,
            scope: SymbolScope::Linkage,
            weak: false,
            section: SymbolSection::Section(data),
            flags: SymbolFlags::None,
        });
        obj.add_relocation(
            data,
            Relocation {
                offset: 0,
                symbol: ids[target],
                addend: 0,
                flags: RelocationFlags::Elf {
                    r_type: object::elf::R_AARCH64_ABS64,
                },
            },
        )
        .unwrap();
    }
    obj.write().unwrap()
}

/// The image `rust-obj2lean` would export for the single object `bytes` with extern functions
/// `externs`.
fn fixture_image_with(
    name: &str,
    bytes: Vec<u8>,
    externs: &[&str],
    page_separate_data: bool,
) -> Image {
    let o = rust_obj2lean::trusted_extractor::parse_object(name, bytes).unwrap();
    let externs: Vec<ExternDecl> = externs
        .iter()
        .map(|n| ExternDecl {
            name: n.to_string(),
            raw_name: n.to_string(),
            kind: ExternKind::Func,
            size: 0,
            align: 4,
            origin: String::new(),
        })
        .collect();
    let layout = if page_separate_data {
        untrusted_legacy_linker::DataLayout::PageSeparated
    } else {
        untrusted_legacy_linker::DataLayout::Interleaved
    };
    let li =
        untrusted_legacy_linker::link_with_layout(std::slice::from_ref(&o), &externs, 0, layout)
            .unwrap();
    Image {
        objects: vec![o],
        externs,
        li,
        page_separate_data,
        rlibs: Vec::new(),
    }
}

fn fixture_image(name: &str, bytes: Vec<u8>, externs: &[&str]) -> Image {
    fixture_image_with(name, bytes, externs, false)
}

/// Image A: `alpha_entry` returns `widget_value() + 1` (`widget_value` is an extern), and
/// `alpha_abs` tail-calls the C runtime's `abs`; `alpha_ptr` points at `alpha_entry`.
fn image_a() -> Image {
    use object::elf::{R_AARCH64_CALL26, R_AARCH64_JUMP26};
    let code = [
        0xa9bf7bfd, // stp x29, x30, [sp, #-16]!
        0x910003fd, // mov x29, sp
        0x94000000, // bl widget_value
        0x11000400, // add w0, w0, #1
        0xa8c17bfd, // ldp x29, x30, [sp], #16
        0xd65f03c0, // ret
        0x14000000, // b abs
    ];
    let obj = fixture_obj(
        &code,
        &[("alpha_entry", 0, 24), ("alpha_abs", 24, 4)],
        &[
            (8, "widget_value", R_AARCH64_CALL26),
            (24, "abs", R_AARCH64_JUMP26),
        ],
        Some(("alpha_ptr", "alpha_entry")),
    );
    fixture_image("alpha", obj, &["widget_value", "abs"])
}

/// Image B: `widget_value` returns 41.
fn image_b() -> Image {
    let code = [0x52800520 /* mov w0, #41 */, 0xd65f03c0 /* ret */];
    fixture_image(
        "widget",
        fixture_obj(&code, &[("widget_value", 0, 8)], &[], None),
        &[],
    )
}

fn multi_cli(out: &Path, bases: &[&str], main_c: Option<&Path>) -> Cli {
    let mut args = vec!["snapshot-link", "--config", "a.toml", "--config", "b.toml"];
    for b in bases {
        args.extend(["--base", b]);
    }
    let out = out.to_str().unwrap();
    args.extend(["--out-dir", out]);
    let main_c = main_c.map(|p| p.to_str().unwrap().to_string());
    if let Some(m) = &main_c {
        args.extend(["--main-c", m]);
    }
    Cli::parse_from(args)
}

#[test]
fn cross_image_extern_resolves_to_the_defining_image() {
    let (a, b) = (image_a(), image_b());
    let labels = vec!["a.toml".to_string(), "b.toml".to_string()];
    let bases = [0x40_0000, 0x48_0000];
    let r = resolve_externs(&[a, b], &bases, &labels).unwrap();
    let widget = r[0]
        .stubs
        .iter()
        .position(|s| s.raw == "widget_value")
        .unwrap();
    let abs = r[0].stubs.iter().position(|s| s.raw == "abs").unwrap();
    assert_eq!(r[0].targets[widget], Some((1, 0x48_0000)));
    assert_eq!(
        r[0].targets[abs], None,
        "no image defines abs: left to the C runtime"
    );
    assert!(r[1].stubs.is_empty());
}

#[test]
fn duplicate_global_across_images_is_rejected() {
    let labels = vec!["a.toml".to_string(), "b.toml".to_string()];
    let err = resolve_externs(&[image_b(), image_b()], &[0x40_0000, 0x48_0000], &labels)
        .unwrap_err()
        .to_string();
    assert!(
        err.contains("widget_value") && err.contains("a.toml") && err.contains("b.toml"),
        "{err}"
    );
    let dir = tempfile::tempdir().unwrap();
    let cli = multi_cli(dir.path(), &[], None);
    let err = link_images(&cli, dir.path(), "", &[image_b(), image_b()]).unwrap_err();
    assert!(err.to_string().contains("defined by both"), "{err}");
}

#[test]
fn extern_function_defined_as_data_by_another_image_is_rejected() {
    // Image C exports `widget_value` as a data object.
    let mut obj =
        object::write::Object::new(BinaryFormat::Elf, Architecture::Aarch64, Endianness::Little);
    let data = obj.section_id(object::write::StandardSection::Data);
    obj.append_section_data(data, &[0; 8], 8);
    obj.add_symbol(object::write::Symbol {
        name: b"widget_value".to_vec(),
        value: 0,
        size: 8,
        kind: object::SymbolKind::Data,
        scope: object::SymbolScope::Linkage,
        weak: false,
        section: object::write::SymbolSection::Section(data),
        flags: object::SymbolFlags::None,
    });
    let c = fixture_image("gadget", obj.write().unwrap(), &[]);
    let labels = vec!["a.toml".to_string(), "c.toml".to_string()];
    let err = resolve_externs(&[image_a(), c], &[0x40_0000, 0x48_0000], &labels).unwrap_err();
    assert!(err.to_string().contains("is a data symbol"), "{err}");
}

// ---- End to end: link with the pinned zig, ld.lld and llvm-objcopy, and run under qemu when
// available. Skipped when a tool is missing, unless `REQUIRE_PROC_SNAPSHOT=1` (as in CI).

fn have_link_tools() -> bool {
    let ok = tool("LLD", "ld.lld").is_ok()
        && tool("LLVM_OBJCOPY", "llvm-objcopy").is_ok()
        && rust_obj2lean::untrusted_driver::find_zig_binary("snapshot-link tests").is_ok();
    if !ok {
        let required = std::env::var("REQUIRE_PROC_SNAPSHOT").as_deref() == Ok("1")
            || std::env::var("REQUIRE_SNAPSHOT_LINK_TOOLS").as_deref() == Ok("1");
        assert!(
            !required,
            "REQUIRE_PROC_SNAPSHOT=1 / REQUIRE_SNAPSHOT_LINK_TOOLS=1 but zig / ld.lld / llvm-objcopy is missing"
        );
        eprintln!("skipping: zig / ld.lld / llvm-objcopy not on PATH (or $LLD / $LLVM_OBJCOPY)");
    }
    ok
}

fn qemu() -> Option<PathBuf> {
    std::env::var_os("QEMU_AARCH64")
        .filter(|v| !v.is_empty())
        .map(PathBuf::from)
        .or_else(|| which::which("qemu-aarch64").ok())
}

/// Link images A and B with `main` returning `alpha_entry()` at `bases`, check `link.json`,
/// and return `(link.json, base of A, base of B)`.
fn link_two(bases: &[&str]) -> (serde_json::Value, u64, u64) {
    let dir = tempfile::tempdir().unwrap();
    let main_c = dir.path().join("my_main.c");
    std::fs::write(
        &main_c,
        // Weak, like the image entry points a real `--main-c` driver calls, so the runtime
        // probe links `main.o` on its own.
        "__attribute__((weak)) int alpha_entry(void);\nint main(void) {\n  return alpha_entry();\n}\n",
    )
    .unwrap();
    let out = dir.path().join("out");
    let cli = multi_cli(&out, bases, Some(&main_c));
    link_images(&cli, dir.path(), "", &[image_a(), image_b()]).unwrap();
    let json: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(out.join("link.json")).unwrap()).unwrap();
    let images = json["images"].as_array().expect("images array");
    assert_eq!(images.len(), 2);
    assert_eq!(json["check"]["errors"], serde_json::json!([]));
    let (base_a, base_b) = (
        images[0]["base"].as_u64().unwrap(),
        images[1]["base"].as_u64().unwrap(),
    );
    // Backward-compatible top level: the first image.
    assert_eq!(json["base"].as_u64(), Some(base_a));
    assert_eq!(json["config"], "a.toml");
    assert_eq!(images[1]["config"], "b.toml");
    let stub = |name: &str| {
        images[0]["stubs"]
            .as_array()
            .unwrap()
            .iter()
            .find(|s| s["extern"] == name)
            .unwrap()
            .clone()
    };
    assert_eq!(stub("widget_value")["definedBy"], 1);
    assert_eq!(stub("widget_value")["target"].as_u64(), Some(base_b));
    assert_eq!(stub("abs")["definedBy"], "runtime");
    assert!(stub("abs")["target"].as_u64().is_some());
    // Interleaved manifest keeps the original `sections` keys (no `rodata` key).
    assert!(images[0]["sections"].get("rodata").is_none());
    // Each image's sections are where the manifest says.
    let elf_bytes = std::fs::read(out.join("prog")).unwrap();
    let elf = object::File::parse(elf_bytes.as_slice()).unwrap();
    use object::ObjectSection;
    assert_eq!(elf.section_by_name(".img.text").unwrap().address(), base_a);
    assert_eq!(elf.section_by_name(".img1.text").unwrap().address(), base_b);
    // The relocated pointer in image A's data uses image A's base.
    let data = elf.section_by_name(".img.data").unwrap();
    assert_eq!(
        data.address(),
        images[0]["sections"]["data"].as_u64().unwrap()
    );
    assert_eq!(data.data().unwrap()[..8], base_a.to_le_bytes());
    if let Some(q) = qemu() {
        let st = std::process::Command::new(q)
            .arg(out.join("prog"))
            .status()
            .unwrap();
        assert_eq!(st.code(), Some(42), "widget_value() + 1");
    } else {
        eprintln!("not running the executable: qemu-aarch64 not found (set QEMU_AARCH64)");
    }
    (json, base_a, base_b)
}

#[test]
fn two_images_link_with_automatic_bases() {
    if !have_link_tools() {
        return;
    }
    let (_, a, b) = link_two(&[]);
    let ext_a = image_extent(&image_a().li);
    assert_eq!(a, 0x40_0000);
    assert_eq!(b, (a + ext_a).next_multiple_of(PAGE));
}

#[test]
fn two_images_link_with_explicit_bases_in_any_order() {
    if !have_link_tools() {
        return;
    }
    // Image B below image A.
    let (_, a, b) = link_two(&["0x500000", "0x400000"]);
    assert_eq!((a, b), (0x50_0000, 0x40_0000));
}

#[test]
fn single_image_link_json_has_no_images_array() {
    if !have_link_tools() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let out = dir.path().join("out");
    let cli = Cli::parse_from([
        "snapshot-link",
        "--config",
        "b.toml",
        "--out-dir",
        out.to_str().unwrap(),
    ]);
    link_images(&cli, dir.path(), "", &[image_b()]).unwrap();
    let json: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(out.join("link.json")).unwrap()).unwrap();
    assert!(json.get("images").is_none(), "{json}");
    assert_eq!(json["base"].as_u64(), Some(0x40_0000));
    assert_eq!(json["config"], "b.toml");
    assert_eq!(json["check"]["errors"], serde_json::json!([]));
    let keys: Vec<&String> = json.as_object().unwrap().keys().collect();
    assert_eq!(
        keys,
        [
            "base", "check", "config", "elf", "image", "inputs", "schema", "stubMode", "stubs",
            "tools"
        ]
    );
}

// ---- A stub branches to a global (or weak) definition, never to a same-named local symbol.

/// A relocatable object whose `.text` holds `code`, with function symbols `(name, offset,
/// size, scope)`.
fn obj_with_scoped_funcs(code: &[u32], funcs: &[(&str, u64, u64, object::SymbolScope)]) -> Vec<u8> {
    use object::write::{StandardSection, Symbol, SymbolSection};
    let mut obj =
        object::write::Object::new(BinaryFormat::Elf, Architecture::Aarch64, Endianness::Little);
    let text = obj.section_id(StandardSection::Text);
    obj.append_section_data(text, &words(code), 4);
    for &(name, value, size, scope) in funcs {
        obj.add_symbol(Symbol {
            name: name.as_bytes().to_vec(),
            value,
            size,
            kind: object::SymbolKind::Text,
            scope,
            weak: false,
            section: SymbolSection::Section(text),
            flags: object::SymbolFlags::None,
        });
    }
    obj.write().unwrap()
}

#[test]
fn extern_symbols_skip_image_ranges_and_prefer_globals() {
    use object::SymbolScope::{Compilation, Linkage};
    let ret = 0xd65f03c0;
    let bytes = obj_with_scoped_funcs(
        &[ret; 6],
        &[
            ("abs", 0, 4, Compilation),
            ("abs", 4, 4, Linkage),
            ("only_local", 8, 4, Compilation),
            ("twice", 12, 4, Compilation),
            ("twice", 16, 4, Compilation),
            ("in_image", 20, 4, Linkage),
        ],
    );
    // `.text` is at address 0 in a relocatable object; treat `[20, 24)` as an image.
    let syms = crate::verify::extern_symbols(&bytes, &[(20, 24)]).unwrap();
    assert_eq!(
        syms.get("abs"),
        Some(&4),
        "the global `abs`, not the local one at 0"
    );
    assert_eq!(
        syms.get("only_local"),
        Some(&8),
        "a unique local definition (hidden global)"
    );
    assert!(
        !syms.contains_key("twice"),
        "two local definitions are ambiguous"
    );
    assert!(
        !syms.contains_key("in_image"),
        "definitions inside an image are not candidates"
    );
    // A same-named local inside an image never shadows the definition outside it.
    let syms = crate::verify::extern_symbols(&bytes, &[(4, 8)]).unwrap();
    assert_eq!(syms.get("abs"), Some(&0));
}

/// Image B, plus a local function `abs` (`mov w0, #7; ret`) that must not capture image A's
/// `abs` extern.
fn image_b_with_local_abs() -> Image {
    use object::SymbolScope::{Compilation, Linkage};
    let code = [0x52800520, 0xd65f03c0, 0x528000e0, 0xd65f03c0];
    let obj = obj_with_scoped_funcs(
        &code,
        &[("widget_value", 0, 8, Linkage), ("abs", 8, 8, Compilation)],
    );
    fixture_image("widget", obj, &[])
}

#[test]
fn stub_ignores_same_named_local_symbol_of_another_image() {
    if !have_link_tools() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let out = dir.path().join("out");
    let cli = multi_cli(&out, &[], None);
    link_images(&cli, dir.path(), "", &[image_a(), image_b_with_local_abs()]).unwrap();
    let json: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(out.join("link.json")).unwrap()).unwrap();
    assert_eq!(json["check"]["errors"], serde_json::json!([]));
    let images = json["images"].as_array().unwrap();
    let base_b = images[1]["base"].as_u64().unwrap();
    let abs = images[0]["stubs"]
        .as_array()
        .unwrap()
        .iter()
        .find(|s| s["extern"] == "abs")
        .unwrap();
    assert_eq!(abs["definedBy"], "runtime");
    let target = abs["target"].as_u64().unwrap();
    assert_ne!(
        target,
        base_b + 8,
        "the stub target is image B's local `abs`"
    );
    let end_b = base_b + image_extent(&image_b_with_local_abs().li);
    assert!(
        !(0x40_0000..end_b).contains(&target),
        "{target:#x} is in the C runtime, outside both images"
    );
    // The stub word itself branches to the C runtime's `abs`.
    let elf_bytes = std::fs::read(out.join("prog")).unwrap();
    let elf = object::File::parse(elf_bytes.as_slice()).unwrap();
    use object::{ObjectSection, ObjectSymbol};
    assert!(
        elf.symbols()
            .any(|s| s.name() == Ok("abs") && s.is_local() && s.address() == base_b + 8),
        "the local `abs` is in .symtab, so the old first-match lookup could pick it"
    );
    let text = elf.section_by_name(".img.text").unwrap();
    let off = abs["off"].as_u64().unwrap() as usize;
    let w = u32::from_le_bytes(text.data().unwrap()[off..off + 4].try_into().unwrap());
    assert_eq!(b_target(w, text.address() + off as u64), Some(target));
}

// ---- Native objects (`--native-objects` / `--musl-string`), per-extern `--branch-stubs`, and
// opt-in page-separated `PT_LOAD` segment verification.

fn engine_repo_root() -> PathBuf {
    std::fs::canonicalize(Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")).unwrap()
}

fn check_host_link_tools(test_name: &str) -> bool {
    let required = std::env::var("REQUIRE_SNAPSHOT_LINK_TOOLS").as_deref() == Ok("1")
        || std::env::var("REQUIRE_PROC_SNAPSHOT").as_deref() == Ok("1");
    for (var, bin) in [("LLVM_OBJCOPY", "llvm-objcopy"), ("LLD", "ld.lld")] {
        if let Err(e) = tool(var, bin) {
            assert!(!required, "{test_name}: {e:#}");
            eprintln!("skipping {test_name}: {e:#}");
            return false;
        }
    }
    if let Err(e) = untrusted_driver::resolve_zig("0.16.0") {
        assert!(!required, "{test_name}: {e:#}");
        eprintln!("skipping {test_name}: {e:#}");
        return false;
    }
    true
}

fn read_pinned_libc_lo_members() -> HashMap<String, Vec<u8>> {
    let tc = crate::std_profile::StdToolchain::resolve()
        .expect("pinned Rust 1.98.1 std toolchain must resolve");
    let libc_bytes = std::fs::read(tc.self_contained_libc()).unwrap();
    let ar = object::read::archive::ArchiveFile::parse(libc_bytes.as_slice()).unwrap();
    let mut map = HashMap::new();
    for entry in ar.members() {
        let entry = entry.unwrap();
        let mname = std::str::from_utf8(entry.name()).unwrap_or("");
        if let Some(stem) = mname.strip_suffix(".lo") {
            map.insert(
                stem.to_string(),
                entry.data(libc_bytes.as_slice()).unwrap().to_vec(),
            );
        }
    }
    map
}

#[test]
fn extract_musl_string_objects_matches_pinned_libca_and_rejects_unknown() {
    let ref_map = read_pinned_libc_lo_members();
    let all = extract_musl_string_objects(None).unwrap();
    assert_eq!(all.len(), MUSL_STRING_MEMBERS.len());
    for ((name, bytes), &expected_name) in all.iter().zip(MUSL_STRING_MEMBERS.iter()) {
        assert_eq!(name, expected_name);
        assert_eq!(bytes.as_slice(), ref_map[name.as_str()].as_slice());
    }

    let alias_req = vec!["memcpy".to_string(), "__memrchr".to_string()];
    let sub = extract_musl_string_objects(Some(&alias_req)).unwrap();
    assert_eq!(sub.len(), 2);
    assert_eq!(sub[0].0, "memcpy");
    assert_eq!(sub[1].0, "memrchr");
    assert_eq!(sub[1].1.as_slice(), ref_map["memrchr"].as_slice());

    let bad_req = vec!["memcpy".to_string(), "not_a_musl_member".to_string()];
    let err = extract_musl_string_objects(Some(&bad_req)).unwrap_err();
    assert!(format!("{err:#}").contains("not_a_musl_member"));
}

fn write_tiny_image_fixture(dir: &Path, page_separate_data: bool) -> PathBuf {
    std::fs::write(
        dir.join("lib.c"),
        r#"
typedef unsigned long size_t;
extern void *memcpy(void *dst, const void *src, size_t n);
extern void *memset(void *s, int c, size_t n);
extern void *memmove(void *dst, const void *src, size_t n);
extern int memcmp(const void *a, const void *b, size_t n);
extern int bcmp(const void *a, const void *b, size_t n);
extern int unlinked_hooked_ext(int x);

__attribute__((noinline))
int exercise_musl_prims(unsigned char *a, unsigned char *b, int call_hook) {
    memset(a, 0x5a, 32);
    for (size_t i = 0; i < 16; i++) {
        b[i] = (unsigned char)(i + 1);
    }
    memcpy(a, b, 16);
    memmove(a + 4, a, 12);
    if (memcmp(a + 4, b, 12) != 0) return 1;
    if (bcmp(a + 4, b, 12) != 0) return 2;
    if (call_hook) return unlinked_hooked_ext(7);
    return 0;
}

int main(void) {
    unsigned char a[32];
    unsigned char b[32];
    return exercise_musl_prims(a, b, 0);
}
"#,
    )
    .unwrap();
    let cfg = dir.join("translation.toml");
    let flag_line = if page_separate_data {
        "page_separate_data = true\n"
    } else {
        ""
    };
    std::fs::write(
        &cfg,
        format!(
            r#"
obj_name = "tinyImage"
title = "Tiny image exercising musl native objects"
{flag_line}
[native_compiler]
zig_version = "0.16.0"

[[native_objects]]
name = "lib"
source = "lib.c"
c_flags = ["-fno-builtin"]

[[externs]]
name = "memcpy"
kind = "func"

[[externs]]
name = "memset"
kind = "func"

[[externs]]
name = "memmove"
kind = "func"

[[externs]]
name = "memcmp"
kind = "func"

[[externs]]
name = "bcmp"
kind = "func"

[[externs]]
name = "unlinked_hooked_ext"
kind = "func"

[[targets]]
name = "tiny_image"
lean_file = "Out.lean"
sub_namespace = "TinyImage"
prog_name = "tinyImageBin"
title = "Tiny image"
lemma_allowlist = ["exercise_musl_prims", "main"]
"#
        ),
    )
    .unwrap();
    cfg
}

#[test]
fn unknown_branch_stubs_rejected_in_run_before_linking() {
    if let Err(e) = untrusted_driver::resolve_zig("0.16.0") {
        let required = std::env::var("REQUIRE_SNAPSHOT_LINK_TOOLS").as_deref() == Ok("1")
            || std::env::var("REQUIRE_PROC_SNAPSHOT").as_deref() == Ok("1");
        assert!(
            !required,
            "unknown_branch_stubs_rejected_in_run_before_linking: {e:#}"
        );
        eprintln!("skipping unknown_branch_stubs_rejected_in_run_before_linking: {e:#}");
        return;
    }
    let tmp = tempfile::tempdir().unwrap();
    let cfg = write_tiny_image_fixture(tmp.path(), false);
    let out_dir = tmp.path().join("out");
    let err = run(Cli {
        config: vec![cfg],
        repo_root: engine_repo_root(),
        base: vec![0x40_0000],
        stubs: StubMode::Zero,
        branch_stubs: ["memcpy", "unknown_ext_alpha", "unknown_ext_beta"]
            .into_iter()
            .map(String::from)
            .collect(),
        native_objects: None,
        musl_string: false,
        native_only: Vec::new(),
        page_separate_data: false,
        out_dir: out_dir.clone(),
        name: "prog".into(),
        main_c: None,
        main_rust: None,
        check_std_toolchain: false,
        strip_runtime_debug: false,
        stock: false,
        stock_lld_arg: vec![],
        stock_keep_library: false,
        stock_native_object: vec![],
        stock_self_contained_dir: None,
        expect_code: Vec::new(),
        expect_data: Vec::new(),
    })
    .expect_err("expected unknown --branch-stubs error before linking");
    let msg = format!("{err:#}");
    assert!(
        msg.contains("unknown_ext_alpha, unknown_ext_beta"),
        "unexpected error message: {msg}"
    );
    assert!(
        !out_dir.join("prog").exists(),
        "executable must not be linked when --branch-stubs validation fails"
    );
}

#[test]
fn duplicate_strong_memcpy_in_main_c_fails_cleanly() {
    if !check_host_link_tools("duplicate_strong_memcpy_in_main_c_fails_cleanly") {
        return;
    }
    let repo_root = engine_repo_root();
    let tmp = tempfile::tempdir().unwrap();
    let cfg = write_tiny_image_fixture(tmp.path(), true);
    let main_c = tmp.path().join("main_dup.c");
    std::fs::write(
        &main_c,
        r#"
typedef unsigned long size_t;
void *memcpy(void *dst, const void *src, size_t n) {
    unsigned char *d = dst;
    const unsigned char *s = src;
    for (size_t i = 0; i < n; i++) d[i] = s[i];
    return dst;
}
__attribute__((weak)) int main(void) { return 0; }
"#,
    )
    .unwrap();
    let out_dir = tmp.path().join("out");
    let err = run(Cli {
        config: vec![cfg],
        repo_root,
        base: vec![0x40_0000],
        stubs: StubMode::Zero,
        branch_stubs: ["memcpy", "memset", "memmove", "memcmp", "bcmp"]
            .into_iter()
            .map(String::from)
            .collect(),
        native_objects: None,
        musl_string: true,
        native_only: ["memcpy", "memset", "memmove", "memcmp", "bcmp"]
            .into_iter()
            .map(String::from)
            .collect(),
        page_separate_data: false,
        out_dir: out_dir.clone(),
        name: "prog".into(),
        main_c: Some(main_c),
        main_rust: None,
        check_std_toolchain: false,
        strip_runtime_debug: false,
        stock: false,
        stock_lld_arg: vec![],
        stock_keep_library: false,
        stock_native_object: vec![],
        stock_self_contained_dir: None,
        expect_code: Vec::new(),
        expect_data: Vec::new(),
    })
    .expect_err("expected duplicate strong memcpy definition error");
    let msg = format!("{err:#}");
    assert!(
        msg.contains("duplicate strong symbol definition `memcpy`"),
        "unexpected error message: {msg}"
    );
    // Direct helper check on weak vs strong symbols: main.o has weak `main` and strong `memcpy`.
    let main_bytes = std::fs::read(out_dir.join("work/main.o")).unwrap();
    assert!(check_no_duplicate_strong_defs(&main_bytes, &[]).is_ok());
}

#[test]
fn link_with_musl_string_native_objects_and_branch_stubs() {
    if !check_host_link_tools("link_with_musl_string_native_objects_and_branch_stubs") {
        return;
    }
    let repo_root = engine_repo_root();
    use object::{ObjectSection, ObjectSymbol};
    let tmp = tempfile::tempdir().unwrap();
    let cfg = write_tiny_image_fixture(tmp.path(), true);
    let main_c = tmp.path().join("main_clean.c");
    std::fs::write(
        &main_c,
        "__attribute__((weak)) int main(void) { return 0; }\n",
    )
    .unwrap();
    let out_dir = tmp.path().join("out");
    let prims: Vec<String> = ["memcpy", "memset", "memmove", "memcmp", "bcmp"]
        .into_iter()
        .map(String::from)
        .collect();
    run(Cli {
        config: vec![cfg],
        repo_root: repo_root.clone(),
        base: vec![0x40_0000],
        stubs: StubMode::Zero,
        branch_stubs: prims.clone(),
        native_objects: None,
        musl_string: true,
        native_only: Vec::new(),
        page_separate_data: false,
        out_dir: out_dir.clone(),
        name: "prog".into(),
        main_c: Some(main_c),
        main_rust: None,
        check_std_toolchain: false,
        strip_runtime_debug: false,
        stock: false,
        stock_lld_arg: vec![],
        stock_keep_library: false,
        stock_native_object: vec![],
        stock_self_contained_dir: None,
        expect_code: Vec::new(),
        expect_data: Vec::new(),
    })
    .expect("snapshot-link with musl native objects must succeed");

    // 1. Verify extracted `.o` bytes match `<prim>.lo` in pinned `self-contained/libc.a`
    //    byte-for-byte, and `memrchr.o` was not extracted or linked.
    let musl_map = read_pinned_libc_lo_members();
    assert!(!out_dir.join("work/native/memrchr.o").exists());
    let link_json: serde_json::Value =
        serde_json::from_slice(&std::fs::read(out_dir.join("link.json")).unwrap()).unwrap();
    assert_eq!(link_json["stubMode"], "mixed");
    let inputs = link_json["inputs"].as_array().unwrap();
    for prim in &prims {
        let p = out_dir.join(format!("work/native/{prim}.o"));
        let disk_bytes = std::fs::read(&p).unwrap();
        assert_eq!(
            disk_bytes.as_slice(),
            musl_map[prim.as_str()].as_slice(),
            "{prim}.o bytes differed from libc.a {prim}.lo"
        );
        let rel = format!("work/native/{prim}.o");
        let rec = inputs
            .iter()
            .find(|v| v["path"].as_str() == Some(rel.as_str()))
            .unwrap_or_else(|| panic!("missing {rel} in link.json inputs"));
        assert_eq!(rec["sha256"].as_str(), Some(sha256(&disk_bytes).as_str()));
    }

    // 2. Verify ELF symbol table, branch-stub words vs zero-stub word, and `memrchr` absence.
    let exe_path = out_dir.join("prog");
    let elf_bytes = std::fs::read(&exe_path).unwrap();
    let elf = object::File::parse(&*elf_bytes).unwrap();
    let mut sym_addrs = HashMap::new();
    for s in elf.symbols() {
        if !s.is_undefined()
            && let Ok(n) = s.name()
        {
            sym_addrs.entry(n.to_string()).or_insert(s.address());
        }
    }
    assert!(
        !sym_addrs.contains_key("memrchr"),
        "memrchr must not be linked"
    );
    let img_text = elf
        .section_by_name(".img.text")
        .unwrap()
        .uncompressed_data()
        .unwrap();
    let stubs_arr = link_json["stubs"].as_array().unwrap();
    assert_eq!(
        stubs_arr.len(),
        6,
        "expected 5 musl branch stubs + 1 zero stub"
    );
    for st in stubs_arr {
        let ext = st["extern"].as_str().unwrap();
        let off = st["off"].as_u64().unwrap() as usize;
        let w = u32::from_le_bytes(img_text[off..off + 4].try_into().unwrap());
        if prims.iter().any(|p| p == ext) {
            let target = st["target"].as_u64().unwrap();
            assert_eq!(st["mode"], "branch");
            assert_eq!(sym_addrs.get(ext).copied(), Some(target));
            assert_eq!(encode_b(0x40_0000 + off as u64, target), Some(w));
            assert_eq!(b_target(w, 0x40_0000 + off as u64), Some(target));
        } else {
            assert_eq!(ext, "unlinked_hooked_ext");
            assert_eq!(st["mode"], "zero");
            assert!(st["target"].is_null());
            assert_eq!(w, 0);
        }
    }

    // 3. Execute under cached `qemu-aarch64` if present to verify runtime branch-stub dispatch.
    if let Ok(fetch_out) =
        std::process::Command::new(repo_root.join("scripts/fetch-qemu-aarch64")).output()
        && fetch_out.status.success()
    {
        let qemu_bin = String::from_utf8_lossy(&fetch_out.stdout)
            .trim()
            .to_string();
        let status = std::process::Command::new(qemu_bin)
            .arg(&exe_path)
            .status()
            .expect("failed to execute linked binary under qemu-aarch64");
        assert!(status.success(), "linked binary exited with {status}");
    }
}

/// Assemble `asm_src`, link with `rust-obj2lean::untrusted_legacy_linker::link_with_layout(..., DataLayout::PageSeparated)`
/// and `ld.lld` using `linker_script_full_pagesep`, and run `verify::check` on the resulting ELF.
fn link_and_verify_asm_pagesep(
    asm_src: &str,
    externs: &[ExternDecl],
    perturb: u64,
) -> (untrusted_legacy_linker::LinkedImage, Vec<u8>) {
    use rust_obj2lean::trusted_common::{SecKind, SymBind, SymSection};
    use rust_obj2lean::trusted_extractor::parse_object_with;
    use rust_obj2lean::untrusted_driver::find_zig_binary;
    use rust_obj2lean::untrusted_legacy_linker::{ARM64_NOP_WORD, DataLayout, link_with_layout};

    let tmp = tempfile::tempdir().unwrap();
    let work = tmp.path();
    let zig = find_zig_binary("snapshot-link-test").unwrap();
    let objcopy = tool("LLVM_OBJCOPY", "llvm-objcopy").unwrap();
    let lld = tool("LLD", "ld.lld").unwrap();

    let obj_s = work.join("test.s");
    let obj_raw = work.join("test.o");
    std::fs::write(&obj_s, asm_src).unwrap();
    assert!(
        Command::new(&zig)
            .current_dir(work)
            .args([
                "cc",
                "-target",
                "aarch64-linux-musl",
                "-g0",
                "-c",
                "test.s",
                "-o",
                "test.o"
            ])
            .status()
            .unwrap()
            .success()
    );
    let raw_bytes = std::fs::read(&obj_raw).unwrap();
    let obj = parse_object_with("test.o", raw_bytes, None).unwrap();
    let objs = [obj];
    let li = link_with_layout(&objs, externs, perturb, DataLayout::PageSeparated).unwrap();

    let base = 0x40_0000u64;
    let mut globals: HashMap<&str, u64> = HashMap::new();
    for want in [SymBind::Global, SymBind::Weak] {
        for (o, offs) in objs.iter().zip(&li.sec_off) {
            for s in o.symbols.iter().filter(|s| s.bind == want) {
                if let SymSection::Sec(i) = s.sec
                    && let Some(off) = offs.get(i).copied().flatten()
                {
                    globals.entry(s.name.as_str()).or_insert(off + s.value);
                }
            }
        }
    }
    for (n, o) in &li.stubs {
        globals.entry(n.as_str()).or_insert(*o);
    }
    for (n, o, _) in &li.extern_data {
        globals.entry(n.as_str()).or_insert(*o);
    }

    let prepared = prepare_object_bytes(
        &objs[0],
        &li.sec_off[0],
        &globals,
        &li,
        StubMode::Zero,
        true,
    )
    .unwrap();
    let orig_o = work.join("img0.orig.o");
    let img0_o = work.join("img0.o");
    std::fs::write(&orig_o, &prepared).unwrap();

    let stubs: Vec<Stub> = li
        .stubs
        .iter()
        .map(|(n, o)| Stub {
            raw: n.clone(),
            off: *o,
        })
        .collect();
    let ext_data: Vec<ExternData> = li
        .extern_data
        .iter()
        .map(|(n, o, sz)| ExternData {
            raw: n.clone(),
            off: *o,
            size: *sz,
        })
        .collect();
    let mut c = Command::new(&objcopy);
    for (k, s) in stubs.iter().enumerate() {
        c.arg(format!("--redefine-sym={}={}", s.raw, Stub::sym(k)));
    }
    for (k, d) in ext_data.iter().enumerate() {
        c.arg(format!("--redefine-sym={}={}", d.raw, ExternData::sym(k)));
    }
    assert!(c.arg(&orig_o).arg(&img0_o).status().unwrap().success());

    let got_vals: Vec<u64> = li.got.iter().map(|g| g.value(base)).collect();
    let mut support = image_support_asm_pagesep(&stubs, &ext_data, &got_vals, StubMode::Zero);
    // Emit leading NOP pad in `.text.__snapnop` when `perturb > 0` so `.img.text` starts at `base`
    // with ARM64 NOP words matching `link_with_layout`.
    if perturb > 0 {
        support += ".section .text.__snapnop,\"ax\",@progbits\n.p2align 2\n";
        for _ in 0..(perturb / 4) {
            support += &format!(".word {ARM64_NOP_WORD:#010x}\n");
        }
    }
    support += ".section .text._start,\"ax\",@progbits\n.globl _start\n_start:\nret\n";
    std::fs::write(work.join("stubs.s"), support).unwrap();
    assert!(
        Command::new(&zig)
            .current_dir(work)
            .args([
                "cc",
                "-target",
                "aarch64-linux-musl",
                "-g0",
                "-c",
                "stubs.s",
                "-o",
                "stubs.o"
            ])
            .status()
            .unwrap()
            .success()
    );

    let file = |i: usize| format!("img{i}.o");
    let mut text = if perturb > 0 {
        vec![Pinned {
            file: "stubs.o".into(),
            sec: ".text.__snapnop".into(),
            off: 0,
            size: perturb,
        }]
    } else {
        vec![]
    };
    text.extend(pinned_sections(&objs, &li, &[SecKind::Text], file).unwrap());
    let rodata = pinned_sections(&objs, &li, &[SecKind::Rodata], file).unwrap();
    let rw_data = pinned_sections(&objs, &li, &[SecKind::Data], file).unwrap();
    let bss = pinned_sections(&objs, &li, &[SecKind::Bss], file).unwrap();
    assert!(
        externs
            .iter()
            .all(|x| matches!(x.kind, ExternKind::Func | ExternKind::Object))
    );
    let script = linker_script_full_pagesep(
        base,
        &text,
        &stubs,
        &rodata,
        &rw_data,
        &bss,
        &ext_data,
        ImageDataLayout::from_image(&li),
        false,
    );
    let script_path = work.join("link.ld");
    let exe_path = work.join("out.elf");
    std::fs::write(&script_path, script).unwrap();
    assert!(
        Command::new(&lld)
            .args([
                "-static",
                "-no-pie",
                "--no-gc-sections",
                "--icf=none",
                "--no-relax",
                "-z",
                "norelro",
                "-z",
                "max-page-size=4096",
                "-z",
                "common-page-size=4096",
                "-O0",
                "--build-id=none",
                "--strip-debug",
                "-e",
                "_start",
                "-T",
            ])
            .arg(&script_path)
            .arg("-o")
            .arg(&exe_path)
            .arg(&img0_o)
            .arg(work.join("stubs.o"))
            .status()
            .unwrap()
            .success()
    );
    let elf_bytes = std::fs::read(&exe_path).unwrap();
    let report = verify::check(
        &elf_bytes,
        &objs,
        &li,
        base,
        &stubs,
        StubMode::Zero,
        &[],
        true,
    )
    .unwrap();
    assert!(
        report.ok(),
        "verify::check failed at perturb={perturb}:\n{}",
        report.errors.join("\n")
    );
    (li, elf_bytes)
}

/// Assemble, link, and `verify::check` an image containing `rodata + data + bss + extdata + GOT`
/// in page-separated mode at both `perturb = 0` and `perturb = 4096 + 4` (`4100`).
#[test]
fn elf_embedding_rodata_data_bss_extdata_got_at_0_and_4100() {
    if !check_host_link_tools("elf_embedding_rodata_data_bss_extdata_got_at_0_and_4100") {
        return;
    }
    let asm = r#"
        .section .text,"ax",@progbits
        .p2align 2
        .globl f
        .type f,@function
    f:
        adrp x0, :got:ext_buf
        ldr  x0, [x0, :got_lo12:ext_buf]
        adrp x1, ro_konst
        add  x1, x1, :lo12:ro_konst
        adrp x2, rw_state
        add  x2, x2, :lo12:rw_state
        ret
        .size f, .-f

        .section .rodata,"a",@progbits
        .p2align 3
        .globl ro_konst
        .type ro_konst,@object
    ro_konst:
        .quad f
        .quad 0xdeadbeefcafebabe
        .size ro_konst, 16

        .section .data,"aw",@progbits
        .p2align 3
        .globl rw_state
        .type rw_state,@object
    rw_state:
        .quad ro_konst
        .size rw_state, 8

        .section .bss,"aw",@nobits
        .p2align 3
        .globl bss_slot
        .type bss_slot,@object
    bss_slot:
        .zero 16
        .size bss_slot, 16
    "#;
    let externs = [ExternDecl {
        name: "ext_buf".into(),
        raw_name: "ext_buf".into(),
        kind: ExternKind::Object,
        size: 32,
        align: 8,
        origin: String::new(),
    }];

    let (li0, _) = link_and_verify_asm_pagesep(asm, &externs, 0);
    assert_eq!(li0.data_off, PAGE);
    assert_eq!(li0.got_off, 3 * PAGE);
    assert_eq!(image_extent(&li0), 3 * PAGE + 8);
    assert_eq!(image_extent_with(&li0, true), 4 * PAGE);

    let (li_p, _) = link_and_verify_asm_pagesep(asm, &externs, 4096 + 4);
    assert_eq!(li_p.data_off, 2 * PAGE);
    assert_eq!(li_p.got_off, 4 * PAGE + 8);
}

/// Pure-rodata image (no writable data, bss, or extdata) in page-separated mode embeds its
/// read-only data and GOT on a single `PF_R` segment without extra padding pages.
#[test]
fn elf_embedding_pure_rodata_single_pf_r_segment() {
    if !check_host_link_tools("elf_embedding_pure_rodata_single_pf_r_segment") {
        return;
    }
    let asm = r#"
        .section .text,"ax",@progbits
        .p2align 2
        .globl f_ro
        .type f_ro,@function
    f_ro:
        adrp x0, only_ro
        ldr  x0, [x0, :lo12:only_ro]
        ret
        .size f_ro, .-f_ro

        .section .rodata,"a",@progbits
        .p2align 3
        .globl only_ro
        .type only_ro,@object
    only_ro:
        .quad 0x0102030405060708
        .quad 0x1112131415161718
        .size only_ro, 16
    "#;
    let (li, _) = link_and_verify_asm_pagesep(asm, &[], 0);
    assert_eq!(li.data_off, PAGE);
    assert_eq!(li.data.len(), 16);
    assert_eq!(li.bss, 0);
    assert_eq!(li.ro_data, vec![(PAGE, 16)]);
    assert_eq!(li.got_off, PAGE + 16);
}

/// Multi-image link where both images opt into `page_separate_data` and contain `.rodata`,
/// `.data`, `.bss`, and GOT entries embeds each image on page-disjoint `PF_R | PF_X`, `PF_R`,
/// `PF_R | PF_W`, and `PF_R` segments.
#[test]
fn two_images_with_rodata_rwdata_bss_and_got_have_disjoint_segments() {
    if !have_link_tools() {
        return;
    }
    let build_rich_image = |tag_name: &str, sym_prefix: &str| -> Image {
        let zig = rust_obj2lean::untrusted_driver::find_zig_binary("snapshot-link-test").unwrap();
        let tmp = tempfile::tempdir().unwrap();
        let asm = format!(
            r#"
            .section .text,"ax",@progbits
            .p2align 2
            .globl {sym_prefix}_fn
            .type {sym_prefix}_fn,@function
        {sym_prefix}_fn:
            adrp x0, :got:{sym_prefix}_ro
            ldr  x0, [x0, :got_lo12:{sym_prefix}_ro]
            adrp x1, {sym_prefix}_rw
            ldr  x1, [x1, :lo12:{sym_prefix}_rw]
            ret
            .size {sym_prefix}_fn, .-{sym_prefix}_fn

            .section .rodata,"a",@progbits
            .p2align 3
            .globl {sym_prefix}_ro
            .type {sym_prefix}_ro,@object
        {sym_prefix}_ro:
            .quad 0x1122334455667788
            .size {sym_prefix}_ro, 8

            .section .data,"aw",@progbits
            .p2align 3
            .globl {sym_prefix}_rw
            .type {sym_prefix}_rw,@object
        {sym_prefix}_rw:
            .quad {sym_prefix}_ro
            .size {sym_prefix}_rw, 8

            .section .bss,"aw",@nobits
            .p2align 3
            .globl {sym_prefix}_bss
            .type {sym_prefix}_bss,@object
        {sym_prefix}_bss:
            .zero 8
            .size {sym_prefix}_bss, 8
            "#
        );
        std::fs::write(tmp.path().join("rich.s"), asm).unwrap();
        assert!(
            Command::new(&zig)
                .current_dir(tmp.path())
                .args([
                    "cc",
                    "-target",
                    "aarch64-linux-musl",
                    "-g0",
                    "-c",
                    "rich.s",
                    "-o",
                    "rich.o",
                ])
                .status()
                .unwrap()
                .success()
        );
        fixture_image_with(
            tag_name,
            std::fs::read(tmp.path().join("rich.o")).unwrap(),
            &[],
            true,
        )
    };

    let im0 = build_rich_image("rich0", "r0");
    let im1 = build_rich_image("rich1", "r1");
    let dir = tempfile::tempdir().unwrap();
    let out = dir.path().join("out");
    let cli = multi_cli(&out, &[], None);
    link_images(&cli, dir.path(), "", &[im0, im1]).unwrap();
    let json: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(out.join("link.json")).unwrap()).unwrap();
    assert_eq!(json["check"]["errors"], serde_json::json!([]));
    let imgs = json["images"].as_array().unwrap();
    assert_eq!(imgs.len(), 2);
    for (idx, item) in imgs.iter().enumerate() {
        let base = item["base"].as_u64().unwrap();
        assert_eq!(item["sections"]["text"].as_u64(), Some(base));
        assert_eq!(item["sections"]["rodata"].as_u64(), Some(base + PAGE));
        assert_eq!(item["sections"]["data"].as_u64(), Some(base + 2 * PAGE));
        assert_eq!(item["sections"]["got"].as_u64(), Some(base + 3 * PAGE));
        assert_eq!(
            item["sections"]["end"].as_u64(),
            Some(base + 4 * PAGE),
            "image {idx} extent should include the full GOT page"
        );
    }
}

#[test]
fn effective_native_only_defaults_musl_string_and_keeps_custom_config_unfiltered() {
    let musl_cli = Cli::try_parse_from([
        "snapshot-link",
        "--config",
        "a.toml",
        "--musl-string",
        "--out-dir",
        "out",
    ])
    .unwrap();
    assert_eq!(
        effective_native_only(&musl_cli),
        Some(vec![
            "memcpy".into(),
            "memset".into(),
            "memmove".into(),
            "memcmp".into(),
            "bcmp".into(),
        ])
    );

    let custom_cli = Cli::try_parse_from([
        "snapshot-link",
        "--config",
        "a.toml",
        "--native-objects",
        "custom.toml",
        "--out-dir",
        "out",
    ])
    .unwrap();
    assert_eq!(effective_native_only(&custom_cli), None);

    let custom_subset_cli = Cli::try_parse_from([
        "snapshot-link",
        "--config",
        "a.toml",
        "--native-objects",
        "custom.toml",
        "--native-only",
        "alpha,beta",
        "--out-dir",
        "out",
    ])
    .unwrap();
    assert_eq!(
        effective_native_only(&custom_subset_cli),
        Some(vec!["alpha".into(), "beta".into()])
    );
}

#[test]
fn verify_pagesep_truncated_p_filesz_reports_single_error_per_region() {
    if !check_host_link_tools("verify_pagesep_truncated_p_filesz_reports_single_error_per_region") {
        return;
    }
    let asm = r#"
        .section .text,"ax",@progbits
        .p2align 2
        .globl f_trunc
        .type f_trunc,@function
    f_trunc:
        adrp x0, :got:rw_val
        ldr  x0, [x0, :got_lo12:rw_val]
        adrp x1, ro_table
        ldr  x1, [x1, :lo12:ro_table]
        ret
        .size f_trunc, .-f_trunc

        .section .rodata,"a",@progbits
        .p2align 3
        .globl ro_table
        .type ro_table,@object
    ro_table:
        .quad 0x1111111111111111
        .quad 0x2222222222222222
        .size ro_table, 16

        .section .data,"aw",@progbits
        .p2align 3
        .globl rw_val
        .type rw_val,@object
    rw_val:
        .quad 0x3333333333333333
        .size rw_val, 8
    "#;
    let zig = untrusted_driver::find_zig_binary("snapshot-link").unwrap();
    let tmp = tempfile::tempdir().unwrap();
    let obj_path = tmp.path().join("trunc.o");
    std::fs::write(tmp.path().join("trunc.s"), asm).unwrap();
    assert!(
        Command::new(&zig)
            .current_dir(tmp.path())
            .args([
                "cc",
                "-target",
                "aarch64-linux-musl",
                "-g0",
                "-c",
                "trunc.s",
                "-o",
            ])
            .arg(&obj_path)
            .status()
            .unwrap()
            .success()
    );
    let objs = vec![
        rust_obj2lean::trusted_extractor::parse_object_with(
            "test.o",
            std::fs::read(&obj_path).unwrap(),
            None,
        )
        .unwrap(),
    ];
    let (li, mut elf_bytes) = link_and_verify_asm_pagesep(asm, &[], 0);
    let base = 0x40_0000u64;
    // Truncate p_filesz to 0 on every PF_R-only image PT_LOAD (rodata at base + PAGE and GOT at
    // base + 3*PAGE) in the ELF64 little-endian program header table.
    let e_phoff = u64::from_le_bytes(elf_bytes[32..40].try_into().unwrap()) as usize;
    let e_phentsize = u16::from_le_bytes(elf_bytes[54..56].try_into().unwrap()) as usize;
    let e_phnum = u16::from_le_bytes(elf_bytes[56..58].try_into().unwrap()) as usize;
    let mut patched = 0usize;
    for idx in 0..e_phnum {
        let ph = e_phoff + idx * e_phentsize;
        let p_type = u32::from_le_bytes(elf_bytes[ph..ph + 4].try_into().unwrap());
        let p_vaddr = u64::from_le_bytes(elf_bytes[ph + 16..ph + 24].try_into().unwrap());
        if p_type == object::elf::PT_LOAD && (p_vaddr == base + PAGE || p_vaddr == base + 3 * PAGE)
        {
            elf_bytes[ph + 32..ph + 40].copy_from_slice(&0u64.to_le_bytes());
            patched += 1;
        }
    }
    assert_eq!(patched, 2);
    let report =
        verify::check(&elf_bytes, &objs, &li, base, &[], StubMode::Zero, &[], true).unwrap();
    let ro_filesz_errs: Vec<&String> = report
        .errors
        .iter()
        .filter(|m| m.contains("ro_data byte") && m.contains("beyond p_filesz"))
        .collect();
    let got_filesz_errs: Vec<&String> = report
        .errors
        .iter()
        .filter(|m| m.contains("GOT page byte") && m.contains("beyond p_filesz"))
        .collect();
    assert_eq!(ro_filesz_errs.len(), 1, "errors: {:?}", report.errors);
    assert_eq!(got_filesz_errs.len(), 1, "errors: {:?}", report.errors);
}

fn std_test_tempdir(prefix: &str) -> tempfile::TempDir {
    if let Some(ctd) = std::env::var_os("CARGO_TARGET_DIR").filter(|v| !v.is_empty()) {
        let base = PathBuf::from(ctd).join("test-scratch");
        std::fs::create_dir_all(&base).unwrap();
        return tempfile::Builder::new()
            .prefix(prefix)
            .tempdir_in(base)
            .unwrap();
    }
    tempfile::Builder::new().prefix(prefix).tempdir().unwrap()
}

fn write_std_bin_fixture(root: &Path, cargo_toml: &str, main_rs: &str) -> PathBuf {
    let crate_dir = root.join("my_app");
    std::fs::create_dir_all(crate_dir.join("src")).unwrap();
    let manifest = crate_dir.join("Cargo.toml");
    std::fs::write(&manifest, cargo_toml).unwrap();
    std::fs::write(crate_dir.join("src").join("main.rs"), main_rs).unwrap();
    manifest
}

const VALID_STD_CARGO_TOML: &str = r#"[package]
name = "my-app"
version = "0.1.0"
edition = "2024"

[profile.release]
opt-level = 2
codegen-units = 1
lto = "fat"
"#;

const VALID_STD_MAIN_RS: &str = "#![forbid(unsafe_code)]\nfn main() {\n    println!(\"ok\");\n}\n";

#[test]
fn check_std_toolchain_flag_succeeds_without_config_or_out_dir() {
    <Cli as clap::CommandFactory>::command().debug_assert();
    let cli = Cli::parse_from(["snapshot-link", "--check-std-toolchain"]);
    assert!(cli.check_std_toolchain);
    assert!(cli.config.is_empty());
    let msg = crate::std_profile::check_std_toolchain()
        .expect("pinned Rust 1.98.1 std toolchain check must succeed");
    assert_eq!(
        msg,
        "OK: rustc 1.98.1 (48a229cea, LLVM 22.1.8), bundled musl crt1.o + libc.a checksums verified"
    );
    run(cli).expect("`snapshot-link --check-std-toolchain` must succeed");

    let missing_out = Cli::parse_from(["snapshot-link", "--config", "a.toml"]);
    let err = run(missing_out).unwrap_err().to_string();
    assert!(err.contains("--out-dir"), "unexpected error: {err}");
}

#[test]
fn std_manifest_and_source_guards_reject_invalid_crates() {
    use crate::std_profile::{RustMainKind, classify_rust_manifest};

    // 1. Staticlib crate is classified as `Staticlib` without std binary guards.
    let d_stat = std_test_tempdir("snap_stat_");
    std::fs::create_dir_all(d_stat.path().join("src")).unwrap();
    let stat_toml = d_stat.path().join("Cargo.toml");
    std::fs::write(
        &stat_toml,
        "[package]\nname = \"my-driver\"\nversion = \"0.1.0\"\nedition = \"2024\"\n[lib]\ncrate-type = [\"staticlib\"]\n",
    )
    .unwrap();
    std::fs::write(d_stat.path().join("src/lib.rs"), "#![no_std]\n").unwrap();
    assert!(matches!(
        classify_rust_manifest(&stat_toml, d_stat.path()).unwrap(),
        RustMainKind::Staticlib
    ));

    // 2. Valid `std` crate (with `lto = true`, comments mentioning `#![no_std]`, and a `vendor/`
    //    directory containing `.c` files) succeeds.
    let d_ok = std_test_tempdir("snap_ok_");
    let ok_manifest = write_std_bin_fixture(
        d_ok.path(),
        "[package]\nname = \"my-app\"\nversion = \"0.1.0\"\nedition = \"2024\"\n[profile.release]\nopt-level = 2\ncodegen-units = 1\nlto = true\n",
        "// #![no_std] in comment is fine\n#![forbid(unsafe_code)]\nfn main() { let _ = \"#![no_std]\"; }\n",
    );
    let vendor_sub = d_ok.path().join("my_app/vendor/widget");
    std::fs::create_dir_all(&vendor_sub).unwrap();
    std::fs::write(vendor_sub.join("helper.c"), "int x;\n").unwrap();
    match classify_rust_manifest(&ok_manifest, d_ok.path()).unwrap() {
        RustMainKind::StdBin(info) => assert_eq!(info.bin_stem, "my_app"),
        RustMainKind::Staticlib => panic!("expected StdBin"),
    }

    // 3. Reject `[patch]` table.
    let d_patch = std_test_tempdir("snap_patch_");
    let m_patch = write_std_bin_fixture(
        d_patch.path(),
        &format!(
            "{VALID_STD_CARGO_TOML}\n[patch.crates-io]\nwidget = {{ path = \"../widget\" }}\n"
        ),
        VALID_STD_MAIN_RS,
    );
    let err = classify_rust_manifest(&m_patch, d_patch.path()).unwrap_err();
    assert!(err.to_string().contains("[patch]"), "{err}");

    // 4. Reject `.cargo/config.toml` in ancestor up to `repo_root`.
    let d_cfg = std_test_tempdir("snap_cargocfg_");
    let m_cfg = write_std_bin_fixture(d_cfg.path(), VALID_STD_CARGO_TOML, VALID_STD_MAIN_RS);
    std::fs::create_dir_all(d_cfg.path().join(".cargo")).unwrap();
    std::fs::write(d_cfg.path().join(".cargo/config.toml"), "[build]\n").unwrap();
    let err = classify_rust_manifest(&m_cfg, d_cfg.path()).unwrap_err();
    assert!(err.to_string().contains(".cargo/config.toml"), "{err}");
}

#[test]
fn std_source_and_profile_guards_reject_invalid_cases() {
    use crate::std_profile::classify_rust_manifest;

    // 1. Reject `build.rs` and `.c` / `.s` files outside `vendor/`.
    let d_build = std_test_tempdir("snap_buildrs_");
    let m_build = write_std_bin_fixture(d_build.path(), VALID_STD_CARGO_TOML, VALID_STD_MAIN_RS);
    std::fs::write(d_build.path().join("my_app/build.rs"), "fn main() {}\n").unwrap();
    let err = classify_rust_manifest(&m_build, d_build.path()).unwrap_err();
    assert!(err.to_string().contains("build.rs"), "{err}");

    let d_c = std_test_tempdir("snap_cfile_");
    let m_c = write_std_bin_fixture(d_c.path(), VALID_STD_CARGO_TOML, VALID_STD_MAIN_RS);
    std::fs::write(
        d_c.path().join("my_app/src/shim.c"),
        "int f(void) { return 0; }\n",
    )
    .unwrap();
    let err = classify_rust_manifest(&m_c, d_c.path()).unwrap_err();
    assert!(err.to_string().contains("shim.c"), "{err}");

    // 2. Reject `#![no_std]` and missing / commented-out `#![forbid(unsafe_code)]`.
    for (main_src, expected) in [
        (
            "#![no_std]\n#![forbid(unsafe_code)]\nfn main() {}\n",
            "#![no_std]",
        ),
        ("fn main() {}\n", "#![forbid(unsafe_code)]"),
        (
            "// #![forbid(unsafe_code)]\nfn main() {}\n",
            "#![forbid(unsafe_code)]",
        ),
        (
            "fn main() { let _ = \"#![forbid(unsafe_code)]\"; }\n",
            "#![forbid(unsafe_code)]",
        ),
    ] {
        let d = std_test_tempdir("snap_attr_");
        let m = write_std_bin_fixture(d.path(), VALID_STD_CARGO_TOML, main_src);
        let err = classify_rust_manifest(&m, d.path()).unwrap_err();
        assert!(err.to_string().contains(expected), "{err}");
    }

    // 3. Reject wrong `[profile.release]` settings (`opt-level`, `codegen-units`, `lto`).
    for (bad_profile, expected) in [
        ("", "[profile.release]"),
        (
            "[profile.release]\nopt-level = 3\ncodegen-units = 1\nlto = \"fat\"\n",
            "opt-level = 2",
        ),
        (
            "[profile.release]\nopt-level = 2\ncodegen-units = 4\nlto = \"fat\"\n",
            "codegen-units = 1",
        ),
        (
            "[profile.release]\nopt-level = 2\ncodegen-units = 1\nlto = \"thin\"\n",
            "lto = \"fat\"",
        ),
        (
            "[profile.release]\nopt-level = 2\ncodegen-units = 1\nlto = false\n",
            "lto = \"fat\"",
        ),
    ] {
        let d = std_test_tempdir("snap_prof_");
        let toml = format!(
            "[package]\nname = \"my-app\"\nversion = \"0.1.0\"\nedition = \"2024\"\n{bad_profile}"
        );
        let m = write_std_bin_fixture(d.path(), &toml, VALID_STD_MAIN_RS);
        let err = classify_rust_manifest(&m, d.path()).unwrap_err();
        assert!(err.to_string().contains(expected), "{err}");
    }

    // 4. Non-std invocation with 0 `--config` still requires at least one `--config`.
    let d_out = std_test_tempdir("snap_noconfig_");
    let cli = Cli::parse_from(["snapshot-link", "--out-dir", d_out.path().to_str().unwrap()]);
    let err = run(cli).unwrap_err();
    assert!(
        err.to_string()
            .contains("at least one --config is required"),
        "{err}"
    );
}

#[test]
fn rust_alloc_bridge_asm_assembles_and_exports_expected_symbols() {
    let Ok(zig) = untrusted_driver::find_zig_binary("snapshot-link") else {
        eprintln!("skipping alloc bridge assembly test: zig unavailable");
        return;
    };
    let syms = vec![
        "_RNvCs123_7___rustc35___rust_no_alloc_shim_is_unstable_v2".to_string(),
        "_RNvCs123_7___rustc12___rust_alloc".to_string(),
        "_RNvCs123_7___rustc14___rust_dealloc".to_string(),
        "_RNvCs123_7___rustc14___rust_realloc".to_string(),
        "_RNvCs123_7___rustc19___rust_alloc_zeroed".to_string(),
        "_RNvCs123_7___rustc26___rust_alloc_error_handler".to_string(),
        "unrelated_extern_fn".to_string(),
    ];
    let asm = crate::std_profile::rust_alloc_bridge_asm(&syms);
    assert!(!asm.contains("unrelated_extern_fn"));
    let d = std_test_tempdir("snap_bridge_");
    let s_path = d.path().join("bridge.s");
    let o_path = d.path().join("bridge.o");
    std::fs::write(&s_path, &asm).unwrap();
    let status = Command::new(&zig)
        .args([
            "cc",
            "-target",
            "aarch64-linux-musl",
            "-g0",
            "-c",
            s_path.to_str().unwrap(),
            "-o",
            o_path.to_str().unwrap(),
        ])
        .status()
        .unwrap();
    assert!(
        status.success(),
        "zig cc failed to assemble allocator bridge"
    );
    let defined =
        crate::std_profile::defined_nonlocal_symbols(&std::fs::read(&o_path).unwrap()).unwrap();
    for expected in &syms[..6] {
        assert!(
            defined.contains(expected),
            "missing {expected} in {defined:?}"
        );
    }
    assert!(!defined.contains("unrelated_extern_fn"));
}

#[test]
fn std_binary_reproducible_across_tempdirs_passes_checks_and_runs_in_qemu() {
    let std_lockfile = "# This file is automatically @generated by Cargo.\nversion = 4\n\n[[package]]\nname = \"my-app\"\nversion = \"0.1.0\"\n";

    let dir_a = std_test_tempdir("snap_std_a_");
    let dir_b = std_test_tempdir("snap_std_bravo_longer_path_");

    let build_one = |root: &Path| -> (PathBuf, Vec<u8>, String) {
        let manifest = write_std_bin_fixture(root, VALID_STD_CARGO_TOML, VALID_STD_MAIN_RS);
        std::fs::write(manifest.parent().unwrap().join("Cargo.lock"), std_lockfile).unwrap();
        let out_dir = root.join("out");
        let cli = Cli::parse_from([
            "snapshot-link",
            "--repo-root",
            root.to_str().unwrap(),
            "--main-rust",
            "my_app/Cargo.toml",
            "--out-dir",
            out_dir.to_str().unwrap(),
            "--name",
            "my_app.elf",
        ]);
        run(cli).expect("snapshot-link on std binary crate must succeed");
        let elf_path = out_dir.join("my_app.elf");
        let elf_bytes = std::fs::read(&elf_path).unwrap();
        let link_json = std::fs::read_to_string(out_dir.join("link.json")).unwrap();
        (elf_path, elf_bytes, link_json)
    };

    let (elf_path_a, elf_a, json_a) = build_one(dir_a.path());
    let (_elf_path_b, elf_b, json_b) = build_one(dir_b.path());

    assert_eq!(
        sha256(&elf_a),
        sha256(&elf_b),
        "std ELF binaries built in distinct directories must be byte-for-byte identical"
    );
    assert_eq!(elf_a, elf_b);
    assert_eq!(
        json_a, json_b,
        "link.json manifests built in distinct directories must be byte-for-byte identical"
    );

    verify::check_std_elf(&elf_a).expect("check_std_elf must accept linked std binary");

    let parsed_json: serde_json::Value = serde_json::from_str(&json_a).unwrap();
    assert_eq!(parsed_json["config"], serde_json::Value::Null);
    assert_eq!(parsed_json["base"], serde_json::json!(0x40_0000));
    assert_eq!(parsed_json["image"], serde_json::Value::Null);
    assert_eq!(parsed_json["stubs"], serde_json::json!([]));
    assert_eq!(parsed_json["stdProfile"]["rustc"], "1.98.1");
    assert_eq!(
        parsed_json["stdProfile"]["commit"],
        "48a229ceaefd4985c50990b14116b6d856af0985"
    );
    assert_eq!(parsed_json["stdProfile"]["llvm"], "22.1.8");
    assert!(parsed_json["tools"]["rust-lld"].as_str().is_some());

    // Negative checks on mutated copies of the linked ELF (`ET_DYN`, `PT_DYNAMIC`, W+X, symbol audit).
    let mut bad_dyn = elf_a.clone();
    bad_dyn[16..18].copy_from_slice(&3u16.to_le_bytes()); // ET_DYN
    assert!(
        verify::check_std_elf(&bad_dyn)
            .unwrap_err()
            .to_string()
            .contains("ET_EXEC")
    );

    let e_phoff = u64::from_le_bytes(elf_a[32..40].try_into().unwrap()) as usize;
    let mut bad_wx = elf_a.clone();
    let ph1 = e_phoff + 2 * 56; // `.text` PT_LOAD
    bad_wx[ph1 + 4..ph1 + 8].copy_from_slice(&7u32.to_le_bytes()); // PF_R | PF_W | PF_X
    assert!(
        verify::check_std_elf(&bad_wx)
            .unwrap_err()
            .to_string()
            .contains("W^X")
    );

    let mut bad_pt_dyn = elf_a.clone();
    bad_pt_dyn[e_phoff..e_phoff + 4].copy_from_slice(&object::elf::PT_DYNAMIC.to_le_bytes());
    assert!(
        verify::check_std_elf(&bad_pt_dyn)
            .unwrap_err()
            .to_string()
            .contains("PT_DYNAMIC")
    );

    let mut bad_sym = elf_a.clone();
    let needle = b"__do_init\0";
    let pos = bad_sym
        .windows(needle.len())
        .position(|w| w == needle)
        .expect("symbol in strtab");
    bad_sym[pos..pos + needle.len()].copy_from_slice(b"gimli_bad\0");
    assert!(
        verify::check_std_elf(&bad_sym)
            .unwrap_err()
            .to_string()
            .contains("gimli_bad")
    );

    // Execute under `qemu-aarch64` and verify exact stdout + exit status.
    let fetch_qemu = engine_repo_root().join("scripts/fetch-qemu-aarch64");
    let qemu_out = Command::new(&fetch_qemu)
        .current_dir(engine_repo_root())
        .output()
        .expect("scripts/fetch-qemu-aarch64 must run");
    assert!(
        qemu_out.status.success(),
        "fetch-qemu-aarch64 failed: {}",
        String::from_utf8_lossy(&qemu_out.stderr)
    );
    let qemu_bin = PathBuf::from(String::from_utf8_lossy(&qemu_out.stdout).trim());
    let run_out = Command::new(&qemu_bin)
        .arg(&elf_path_a)
        .output()
        .expect("qemu-aarch64 execution must succeed");
    assert_eq!(run_out.status.code(), Some(0));
    assert_eq!(String::from_utf8_lossy(&run_out.stdout), "ok\n");

    // Also link the same `std` binary crate alongside a pre-verified `--config` image, exercising
    // fixed-VA image placement, `stubs.o` allocator bridge emission, and `check_images` + `check_std_elf`.
    if untrusted_driver::resolve_zig("0.16.0").is_ok() {
        let dir_img = std_test_tempdir("snap_std_with_img_");
        std::fs::write(
            dir_img.path().join("lib.c"),
            "typedef unsigned long size_t;\nextern void *memcpy(void *d, const void *s, size_t n);\nint helper_copy(void *d, const void *s, size_t n) { memcpy(d, s, n); return (int)n; }\n",
        )
        .unwrap();
        let img_cfg = dir_img.path().join("translation.toml");
        std::fs::write(
            &img_cfg,
            "obj_name = \"helperLib\"\ntitle = \"Helper lib\"\npage_separate_data = true\n[native_compiler]\nzig_version = \"0.16.0\"\n[[native_objects]]\nname = \"lib\"\nsource = \"lib.c\"\nc_flags = [\"-fno-builtin\"]\n[[externs]]\nname = \"memcpy\"\nkind = \"func\"\n[[targets]]\nname = \"helper_lib\"\nlean_file = \"Out.lean\"\nsub_namespace = \"HelperLib\"\nprog_name = \"helperLibBin\"\ntitle = \"Helper lib\"\nlemma_allowlist = [\"helper_copy\"]\n",
        )
        .unwrap();
        let manifest =
            write_std_bin_fixture(dir_img.path(), VALID_STD_CARGO_TOML, VALID_STD_MAIN_RS);
        std::fs::write(manifest.parent().unwrap().join("Cargo.lock"), std_lockfile).unwrap();
        let out_img = dir_img.path().join("out_img");
        let cli_img = Cli::parse_from([
            "snapshot-link",
            "--repo-root",
            dir_img.path().to_str().unwrap(),
            "--config",
            "translation.toml",
            "--base",
            "0x400000",
            "--main-rust",
            "my_app/Cargo.toml",
            "--out-dir",
            out_img.to_str().unwrap(),
            "--name",
            "with_img.elf",
        ]);
        run(cli_img).expect("std binary + pre-verified --config image link must succeed");
        let elf_img = std::fs::read(out_img.join("with_img.elf")).unwrap();
        verify::check_std_elf(&elf_img).expect("check_std_elf must accept image+std ELF");
        let json_img: serde_json::Value =
            serde_json::from_str(&std::fs::read_to_string(out_img.join("link.json")).unwrap())
                .unwrap();
        assert!(json_img["image"].is_object());
        assert_eq!(json_img["stdProfile"]["rustc"], "1.98.1");
        let run_img = Command::new(&qemu_bin)
            .arg(out_img.join("with_img.elf"))
            .output()
            .expect("qemu-aarch64 execution of image+std ELF must succeed");
        assert_eq!(run_img.status.code(), Some(0));
        assert_eq!(String::from_utf8_lossy(&run_img.stdout), "ok\n");
    }
}

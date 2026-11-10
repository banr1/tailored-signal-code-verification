// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Tests for `--stock` Rust `std` binary and native-object links (`[TEST ONLY]`).

use crate::link::{sha256, tool};
use crate::std_profile::{SELF_CONTAINED_CHECKSUMS, verify_self_contained_dir};
use crate::stock_std::{check_native_object, stage_native_objects, weaken_image_symbols};
use crate::{Cli, stock, verify};
use clap::Parser;
use object::write::{Object as WObject, Symbol, SymbolSection};
use object::{
    Architecture, BinaryFormat, Endianness, Object, ObjectSymbol, SymbolFlags, SymbolKind,
    SymbolScope,
};
use rust_obj2lean::untrusted_driver;
use std::path::{Path, PathBuf};
use std::process::Command;

fn tempdir(prefix: &str) -> tempfile::TempDir {
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

/// A relocatable object for `arch` defining the global functions `globals` in `.text`.
fn obj_with_globals(arch: Architecture, globals: &[&str]) -> Vec<u8> {
    let mut o = WObject::new(BinaryFormat::Elf, arch, Endianness::Little);
    let text = o.section_id(object::write::StandardSection::Text);
    o.append_section_data(
        text,
        &[0xc0, 0x03, 0x5f, 0xd6].repeat(globals.len().max(1)),
        4,
    );
    for (i, g) in globals.iter().enumerate() {
        o.add_symbol(Symbol {
            name: g.as_bytes().to_vec(),
            value: 4 * i as u64,
            size: 4,
            kind: SymbolKind::Text,
            scope: SymbolScope::Linkage,
            weak: false,
            section: SymbolSection::Section(text),
            flags: SymbolFlags::None,
        });
    }
    o.write().unwrap()
}

#[test]
fn native_object_must_be_relocatable_aarch64_elf() {
    check_native_object(&obj_with_globals(Architecture::Aarch64, &["shim"])).unwrap();
    let x86 = check_native_object(&obj_with_globals(Architecture::X86_64, &["shim"]));
    assert!(format!("{:#}", x86.unwrap_err()).contains("AArch64"));
    assert!(check_native_object(b"not an object").is_err());
    // A linked executable is not a native object.
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let elf = std::fs::read_dir(root.join("VerifiedLibraries/RustStd/Testing/empty"))
        .unwrap()
        .map(|e| e.unwrap().path())
        .find(|p| p.extension().is_some_and(|x| x == "elf"))
        .expect("committed empty std ELF fixture");
    let e = check_native_object(&std::fs::read(elf).unwrap()).unwrap_err();
    assert!(format!("{e:#}").contains("ET_REL"), "{e:#}");
}

#[test]
fn stage_native_objects_copies_and_rejects_bad_inputs() {
    let d = tempdir("snap_native_");
    let (root, work) = (d.path().join("repo"), d.path().join("work"));
    std::fs::create_dir_all(root.join("a")).unwrap();
    std::fs::create_dir_all(root.join("b")).unwrap();
    let shim = obj_with_globals(Architecture::Aarch64, &["shim"]);
    std::fs::write(root.join("a/shim.o"), &shim).unwrap();
    std::fs::write(root.join("b/shim.o"), &shim).unwrap();
    std::fs::write(root.join("bogus.o"), b"bogus").unwrap();

    let (staged, notes) = stage_native_objects(&[PathBuf::from("a/shim.o")], &root, &work).unwrap();
    assert_eq!(staged, vec![work.join("native/shim.o")]);
    assert_eq!(std::fs::read(&staged[0]).unwrap(), shim);
    assert_eq!(notes[&staged[0]]["kind"], "nativeObject");
    // No native objects: nothing staged, no `work/native`.
    let w2 = d.path().join("w2");
    assert!(stage_native_objects(&[], &root, &w2).unwrap().0.is_empty());
    assert!(!w2.join("native").exists());

    let dup = stage_native_objects(
        &[PathBuf::from("a/shim.o"), PathBuf::from("b/shim.o")],
        &root,
        &d.path().join("w3"),
    );
    assert!(format!("{:#}", dup.unwrap_err()).contains("two --stock-native-object"));
    let missing = stage_native_objects(&[PathBuf::from("nope.o")], &root, &d.path().join("w4"));
    assert!(format!("{:#}", missing.unwrap_err()).contains("cannot read"));
    let bogus = stage_native_objects(&[PathBuf::from("bogus.o")], &root, &d.path().join("w5"));
    assert!(format!("{:#}", bogus.unwrap_err()).contains("not an object"));
}

#[test]
fn self_contained_dir_fails_closed_on_missing_or_mismatched_files() {
    let d = tempdir("snap_sc_");
    let e = verify_self_contained_dir(d.path()).unwrap_err();
    assert!(format!("{e:#}").contains("missing bundled musl runtime input crt1.o"));
    for &(f, _) in SELF_CONTAINED_CHECKSUMS {
        std::fs::write(d.path().join(f), b"not the pinned bytes").unwrap();
    }
    let e = verify_self_contained_dir(d.path()).unwrap_err();
    assert!(format!("{e:#}").contains("SHA-256 mismatch"), "{e:#}");
}

#[test]
fn weaken_image_symbols_weakens_exactly_the_shared_globals() {
    let Ok(objcopy) = tool("LLVM_OBJCOPY", "llvm-objcopy") else {
        eprintln!("skipping: llvm-objcopy unavailable");
        return;
    };
    let d = tempdir("snap_weaken_");
    let main_o = d.path().join("main_rust.o");
    std::fs::write(
        &main_o,
        obj_with_globals(Architecture::Aarch64, &["shared_fn", "only_main"]),
    )
    .unwrap();
    let lib = obj_with_globals(Architecture::Aarch64, &["shared_fn", "only_lib"]);
    let w = weaken_image_symbols(&objcopy, &main_o, std::iter::once(lib.as_slice())).unwrap();
    assert_eq!(w, vec!["shared_fn".to_string()]);
    let bytes = std::fs::read(&main_o).unwrap();
    let f = object::File::parse(bytes.as_slice()).unwrap();
    let weak = |n: &str| f.symbols().find(|s| s.name() == Ok(n)).unwrap().is_weak();
    assert!(weak("shared_fn"));
    assert!(!weak("only_main"));
    // Nothing shared: the object is left untouched.
    let before = std::fs::read(&main_o).unwrap();
    let other = obj_with_globals(Architecture::Aarch64, &["unrelated"]);
    assert!(
        weaken_image_symbols(&objcopy, &main_o, std::iter::once(other.as_slice()))
            .unwrap()
            .is_empty()
    );
    assert_eq!(std::fs::read(&main_o).unwrap(), before);
}

const STD_CARGO_TOML: &str = "[package]\nname = \"my-app\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[profile.release]\nopt-level = 2\ncodegen-units = 1\nlto = \"fat\"\n";
const STD_MAIN_RS: &str = "#![forbid(unsafe_code)]\nfn main() {\n    println!(\"ok\");\n}\n";
const STD_LOCK: &str = "# This file is automatically @generated by Cargo.\nversion = 4\n\n[[package]]\nname = \"my-app\"\nversion = \"0.1.0\"\n";
const LIB_TOML: &str = "obj_name = \"widgetLib\"\ntitle = \"Widget lib\"\n[native_compiler]\nzig_version = \"0.16.0\"\n[[native_objects]]\nname = \"lib\"\nsource = \"lib.c\"\nc_flags = [\"-O2\", \"-fno-builtin\"]\n[[targets]]\nname = \"widget\"\nlean_file = \"Out.lean\"\nsub_namespace = \"Widget\"\nprog_name = \"widgetBin\"\ntitle = \"Widget\"\nlemma_allowlist = [\"add_bias\"]\n";

/// A repo with a safe `std` binary crate, a C `--config` library and an assembled native object.
fn write_std_repo(root: &Path, zig: &Path) {
    let c = root.join("my_app");
    std::fs::create_dir_all(c.join("src")).unwrap();
    std::fs::write(c.join("Cargo.toml"), STD_CARGO_TOML).unwrap();
    std::fs::write(c.join("Cargo.lock"), STD_LOCK).unwrap();
    std::fs::write(c.join("src/main.rs"), STD_MAIN_RS).unwrap();
    std::fs::write(
        root.join("lib.c"),
        "int add_bias(int x) { return x + 7; }\n",
    )
    .unwrap();
    std::fs::write(root.join("translation.toml"), LIB_TOML).unwrap();
    std::fs::write(
        root.join("shim.S"),
        ".text\n.globl native_marker\n.type native_marker, %function\nnative_marker:\n  ret\n",
    )
    .unwrap();
    let out = Command::new(zig)
        .current_dir(root)
        .args([
            "cc",
            "-target",
            "aarch64-linux-musl",
            "-g0",
            "-c",
            "shim.S",
            "-o",
            "shim.o",
        ])
        .output()
        .unwrap();
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
}

fn std_cli(root: &Path, out: &Path, extra: &[&str]) -> Cli {
    let mut args = vec![
        "snapshot-link",
        "--stock",
        "--stock-keep-library",
        "--repo-root",
        root.to_str().unwrap(),
        "--config",
        "translation.toml",
        "--main-rust",
        "my_app/Cargo.toml",
        "--stock-native-object",
        "shim.o",
        "--stock-lld-arg=--undefined=native_marker",
        "--out-dir",
        out.to_str().unwrap(),
        "--name",
        "app.elf",
    ];
    args.extend_from_slice(extra);
    Cli::parse_from(args)
}

fn stock_tools_available() -> bool {
    untrusted_driver::resolve_zig("0.16.0").is_ok()
        && tool("LLVM_OBJCOPY", "llvm-objcopy").is_ok()
        && tool("LLD", "ld.lld").is_ok()
}

#[test]
fn stock_std_bin_rejects_bad_self_contained_dir_and_non_std_use() {
    if !stock_tools_available() {
        eprintln!("skipping: zig/llvm-objcopy/ld.lld unavailable");
        return;
    }
    let zig = untrusted_driver::find_zig_binary("snapshot-link").unwrap();
    let d = tempdir("snap_stock_std_neg_");
    let root = d.path();
    write_std_repo(root, &zig);
    std::fs::create_dir_all(root.join("empty-sc")).unwrap();

    // Missing self-contained objects: fails before building the crate.
    let cli = std_cli(
        root,
        &root.join("out1"),
        &["--stock-self-contained-dir", "empty-sc"],
    );
    let e = stock::run(&cli).unwrap_err();
    assert!(
        format!("{e:#}").contains("missing bundled musl runtime input crt1.o"),
        "{e:#}"
    );
    assert!(!root.join("out1/work/rust-target").exists());

    // Mismatched self-contained objects.
    let bad = root.join("bad-sc");
    std::fs::create_dir_all(&bad).unwrap();
    for &(f, _) in SELF_CONTAINED_CHECKSUMS {
        std::fs::write(bad.join(f), b"tampered").unwrap();
    }
    let cli = std_cli(
        root,
        &root.join("out2"),
        &["--stock-self-contained-dir", "bad-sc"],
    );
    let e = stock::run(&cli).unwrap_err();
    assert!(format!("{e:#}").contains("SHA-256 mismatch"), "{e:#}");

    // `--stock-self-contained-dir` is only for a `std` binary.
    std::fs::write(root.join("main.c"), "int main(void) { return 0; }\n").unwrap();
    let cli = Cli::parse_from([
        "snapshot-link",
        "--stock",
        "--repo-root",
        root.to_str().unwrap(),
        "--config",
        "translation.toml",
        "--main-c",
        "main.c",
        "--stock-self-contained-dir",
        "empty-sc",
        "--out-dir",
        root.join("out3").to_str().unwrap(),
    ]);
    let e = stock::run(&cli).unwrap_err();
    assert!(
        format!("{e:#}").contains("needs a Rust std binary"),
        "{e:#}"
    );
}

#[test]
fn stock_std_bin_with_native_object_is_reproducible_pinned_and_runs_in_qemu() {
    if !stock_tools_available() {
        eprintln!("skipping: zig/llvm-objcopy/ld.lld unavailable");
        return;
    }
    let zig = untrusted_driver::find_zig_binary("snapshot-link").unwrap();
    let build = |prefix: &str| {
        let d = tempdir(prefix);
        write_std_repo(d.path(), &zig);
        let out = d.path().join("out");
        stock::run(&std_cli(d.path(), &out, &[])).expect("--stock std binary link");
        let elf = std::fs::read(out.join("app.elf")).unwrap();
        let json = std::fs::read_to_string(out.join("stock-link.json")).unwrap();
        (d, out, elf, json)
    };
    let (_da, out_a, elf_a, json_a) = build("snap_stock_std_a_");
    let (_db, _out_b, elf_b, json_b) = build("snap_stock_std_bravo_longer_path_");
    assert_eq!(elf_a, elf_b, "stock std ELF must be reproducible");
    assert_eq!(json_a, json_b, "stock-link.json must be reproducible");
    verify::check_std_elf(&elf_a).unwrap();

    let v: serde_json::Value = serde_json::from_str(&json_a).unwrap();
    assert_eq!(v["parserCheck"], "ok");
    assert_eq!(v["stdBin"]["rustc"], "1.98.1");
    let inputs = v["inputs"].as_array().unwrap();
    let paths: Vec<&str> = inputs.iter().map(|i| i["path"].as_str().unwrap()).collect();
    // rustc's self-contained runtime, never zig's musl.
    assert!(
        !paths.iter().any(|p| p.starts_with("work/runtime/")),
        "{paths:?}"
    );
    for &(f, pinned) in SELF_CONTAINED_CHECKSUMS {
        let p = format!("work/self-contained/{f}");
        let i = inputs.iter().find(|i| i["path"] == p.as_str()).expect(&p);
        assert_eq!(i["kind"], "selfContained");
        assert_eq!(i["pinnedSha256"], pinned);
        assert_eq!(i["sha256"], pinned, "{p} must be linked unmodified");
    }
    let native = inputs
        .iter()
        .find(|i| i["path"] == "work/native/shim.o")
        .unwrap();
    assert_eq!(native["kind"], "nativeObject");
    let shim = std::fs::read(_da.path().join("shim.o")).unwrap();
    assert_eq!(native["sha256"], sha256(&shim));
    // Every recorded hash is the hash of the file that was linked.
    for i in inputs {
        let bytes = std::fs::read(out_a.join(i["path"].as_str().unwrap())).unwrap();
        assert_eq!(i["sha256"], sha256(&bytes));
    }
    for p in [
        "work/main_rust.o",
        "work/compiler_builtins.a",
        "work/lib0_0.o",
    ] {
        assert!(paths.contains(&p), "{p} not in {paths:?}");
    }

    assert_std_provenance(&v);

    // The native object and the library survive `--gc-sections`.
    let f = object::File::parse(elf_a.as_slice()).unwrap();
    for s in ["native_marker", "add_bias"] {
        assert!(f.symbols().any(|x| x.name() == Ok(s)), "{s} missing");
    }

    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let q = Command::new(root.join("scripts/fetch-qemu-aarch64"))
        .current_dir(&root)
        .output()
        .unwrap();
    assert!(q.status.success());
    let qemu = PathBuf::from(String::from_utf8_lossy(&q.stdout).trim());
    let run = Command::new(qemu)
        .arg(out_a.join("app.elf"))
        .output()
        .unwrap();
    assert_eq!(run.status.code(), Some(0));
    assert_eq!(String::from_utf8_lossy(&run.stdout), "ok\n");
}

/// `v["stdBin"]`'s archive members and unwind audit: members are recorded, extracted
/// `libunwind.a` members retain no section, and only crtbegin's weak frame-registration references are allowed.
fn assert_std_provenance(v: &serde_json::Value) {
    // The rebuild key: exact cargo args, rustflags, and hashed manifest, lockfile and sources.
    let k = &v["stdBin"]["rebuildKey"];
    assert_eq!(k["cargoArgs"][2], "/src/my_app/Cargo.toml", "{k}");
    assert!(
        k["cargoArgs"]
            .as_array()
            .unwrap()
            .contains(&"-Zbuild-std=std,panic_abort".into()),
        "{k}"
    );
    assert!(
        k["rustflags"]
            .as_array()
            .unwrap()
            .contains(&"-Cpanic=immediate-abort".into()),
        "{k}"
    );
    assert!(!k.to_string().contains("--remap-path-prefix"), "{k}");
    assert_eq!(k["manifest"]["path"], "/src/my_app/Cargo.toml", "{k}");
    assert!(k["lockfile"]["sha256"].is_string(), "{k}");
    let main_files = k["mainSources"]["files"].as_array().unwrap();
    assert!(
        main_files
            .iter()
            .any(|f| f["path"] == "/src/my_app/src/main.rs"),
        "{k}"
    );
    assert!(
        k["compilerBuiltinsSources"]["count"].as_u64().unwrap() > 0,
        "{k}"
    );
    let members = v["stdBin"]["archiveMembers"].as_array().unwrap();
    assert!(!members.is_empty());
    for m in members {
        let name = m["member"].as_str().unwrap();
        assert!(name.contains(".a("), "{name}");
        if name.contains("libunwind.a(") {
            assert_eq!(m["retained"], serde_json::json!([]), "{name}");
        }
        // Every member is accounted for: it retains a section or `--gc-sections` removed one.
        assert!(
            !m["retained"].as_array().unwrap().is_empty()
                || !m["removed"].as_array().unwrap().is_empty(),
            "{m}"
        );
        assert!(m["extractedBy"]["symbol"].is_string(), "{m}");
    }
    assert!(
        members.iter().any(|m| m["member"]
            .as_str()
            .unwrap()
            .starts_with("work/self-contained/libc.a(")
            && !m["retained"].as_array().unwrap().is_empty()),
        "{members:?}"
    );
    let allowed: Vec<&str> = v["stdBin"]["unwindAudit"]["allowed"]
        .as_array()
        .unwrap()
        .iter()
        .map(|a| a["symbol"].as_str().unwrap())
        .collect();
    assert!(
        allowed
            .iter()
            .all(|a| ["__register_frame_info", "__deregister_frame_info"].contains(a)),
        "{allowed:?}"
    );
}

const TRIM_TOML: &str = "crates = [\"trimlib\"]\nobj_name = \"trimLib\"\n[[sysroot_objects]]\ncrate = \"compiler_builtins\"\nname = \"cb\"\nroots = [\"__ashlti3\"]\n[[targets]]\nname = \"trim\"\nlean_file = \"Out.lean\"\nprog_name = \"trimBin\"\ntitle = \"Trim\"\nlemma_allowlist = [\".*\"]\n";
const TRIM_CARGO_TOML: &str = "[package]\nname = \"trimlib\"\nversion = \"0.1.0\"\nedition = \"2021\"\npublish = false\n\n[lib]\ncrate-type = [\"rlib\"]\n\n[profile.release]\nopt-level = 2\npanic = \"abort\"\ncodegen-units = 1\n";
const TRIM_LOCK: &str = "# This file is automatically @generated by Cargo.\nversion = 4\n\n[[package]]\nname = \"trimlib\"\nversion = \"0.1.0\"\n";
/// `trim_twice` calls `native_marker`, which only the native object defines: with a trim in the
/// image it is a hooked extern, which must resolve to a stub object (here the native object).
const TRIM_LIB_RS: &str = "#![no_std]\nunsafe extern \"C\" {\n    fn native_marker();\n}\n#[no_mangle]\npub extern \"C\" fn trim_twice(x: u32) -> u32 {\n    unsafe { native_marker() };\n    x.wrapping_mul(2)\n}\n";

#[test]
fn stock_std_bin_links_with_a_trimmed_sysroot_member() {
    if !stock_tools_available() {
        eprintln!("skipping: zig/llvm-objcopy/ld.lld unavailable");
        return;
    }
    let zig = untrusted_driver::find_zig_binary("snapshot-link").unwrap();
    let d = tempdir("snap_stock_std_trim_");
    let root = d.path();
    write_std_repo(root, &zig);
    let t = root.join("trim");
    std::fs::create_dir_all(t.join("src")).unwrap();
    std::fs::write(t.join("translation.toml"), TRIM_TOML).unwrap();
    std::fs::write(t.join("Cargo.toml"), TRIM_CARGO_TOML).unwrap();
    std::fs::write(t.join("Cargo.lock"), TRIM_LOCK).unwrap();
    std::fs::write(t.join("src/lib.rs"), TRIM_LIB_RS).unwrap();
    let out = root.join("out");
    stock::run(&std_cli(root, &out, &["--config", "trim/translation.toml"]))
        .expect("--stock std binary link with a trimmed sysroot member");
    let json = std::fs::read_to_string(out.join("stock-link.json")).unwrap();
    let v: serde_json::Value = serde_json::from_str(&json).unwrap();
    assert_eq!(v["parserCheck"], "ok");
    assert!(v["trimmedSysrootObjects"].is_object());
    let trimmed: Vec<&serde_json::Value> = v["configs"]
        .as_array()
        .unwrap()
        .iter()
        .flat_map(|c| c["objects"].as_array().unwrap())
        .filter(|o| o.get("trimmedFrom").is_some())
        .collect();
    assert_eq!(trimmed.len(), 1, "{trimmed:?}");
    assert_eq!(
        trimmed[0]["trimmedFrom"]["roots"],
        serde_json::json!(["__ashlti3"])
    );
    assert_std_provenance(&v);
    assert_eq!(
        v["trimmedSysrootObjects"]["hookedExterns"],
        serde_json::json!(["native_marker"])
    );

    // Every name weakened in `main_rust.o` is defined by an emitted image object, as linked
    // (a trimmed member as its trim).
    let mut emitted = std::collections::BTreeSet::new();
    for e in std::fs::read_dir(out.join("work")).unwrap() {
        let p = e.unwrap().path();
        let n = p.file_name().unwrap().to_str().unwrap();
        if n.starts_with("lib") && n.ends_with(".o") {
            let bytes = std::fs::read(&p).unwrap();
            let f = object::File::parse(bytes.as_slice()).unwrap();
            for s in f.symbols() {
                if s.is_definition() && s.is_global() {
                    emitted.insert(s.name().unwrap().to_string());
                }
            }
        }
    }
    assert!(emitted.contains("__ashlti3") && emitted.contains("trim_twice"));
    for w in v["stdBin"]["weakenedInMain"].as_array().unwrap() {
        assert!(emitted.contains(w.as_str().unwrap()), "{w}");
    }

    let elf = std::fs::read(out.join("app.elf")).unwrap();
    let f = object::File::parse(elf.as_slice()).unwrap();
    for s in ["__ashlti3", "trim_twice", "add_bias", "native_marker"] {
        assert!(f.symbols().any(|x| x.name() == Ok(s)), "{s} missing");
    }
}

/// A sibling C `--config` image whose declared export `native_marker` defines the trim's hooked
/// extern (no stub object defines it).
const SIBLING_TOML: &str = "obj_name = \"ioLib\"\ntitle = \"IO lib\"\n[native_compiler]\nzig_version = \"0.16.0\"\n[[native_objects]]\nname = \"io\"\nsource = \"io.c\"\nc_flags = [\"-O2\", \"-fno-builtin\"]\n[placed]\nexports = [\"native_marker\"]\n[[targets]]\nname = \"io\"\nlean_file = \"Out.lean\"\nsub_namespace = \"Io\"\nprog_name = \"ioBin\"\ntitle = \"IO\"\nlemma_allowlist = [\"native_marker\"]\n";

#[test]
fn stock_std_bin_two_configs_with_a_sibling_defined_hooked_extern() {
    if !stock_tools_available() {
        eprintln!("skipping: zig/llvm-objcopy/ld.lld unavailable");
        return;
    }
    let zig = untrusted_driver::find_zig_binary("snapshot-link").unwrap();
    let d = tempdir("snap_stock_std_sib_");
    let root = d.path();
    write_std_repo(root, &zig);
    let t = root.join("trim");
    std::fs::create_dir_all(t.join("src")).unwrap();
    std::fs::write(t.join("translation.toml"), TRIM_TOML).unwrap();
    std::fs::write(t.join("Cargo.toml"), TRIM_CARGO_TOML).unwrap();
    std::fs::write(t.join("Cargo.lock"), TRIM_LOCK).unwrap();
    std::fs::write(t.join("src/lib.rs"), TRIM_LIB_RS).unwrap();
    let io = root.join("io");
    std::fs::create_dir_all(&io).unwrap();
    std::fs::write(io.join("io.c"), "void native_marker(void) {}\n").unwrap();
    let cli = |toml: &str, out: &Path| {
        std::fs::write(io.join("translation.toml"), toml).unwrap();
        Cli::parse_from([
            "snapshot-link",
            "--stock",
            "--stock-keep-library",
            "--repo-root",
            root.to_str().unwrap(),
            "--config",
            "trim/translation.toml",
            "--config",
            "io/translation.toml",
            "--main-rust",
            "my_app/Cargo.toml",
            "--out-dir",
            out.to_str().unwrap(),
            "--name",
            "app.elf",
        ])
    };
    let out = root.join("out");
    stock::run(&cli(SIBLING_TOML, &out)).expect("two-config --stock std binary link");
    let v: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(out.join("stock-link.json")).unwrap())
            .unwrap();
    assert_eq!(v["parserCheck"], "ok");
    let t = &v["trimmedSysrootObjects"];
    assert_eq!(t["hookedExterns"], serde_json::json!(["native_marker"]));
    let elf = std::fs::read(out.join("app.elf")).unwrap();
    let addr = crate::stock_hooks::elf_address(&elf, "native_marker").unwrap();
    assert_eq!(
        t["siblingDefinedExterns"],
        serde_json::json!([{
            "symbol": "native_marker", "export": "native_marker",
            "hookedBy": "trim/translation.toml", "image": "io/translation.toml",
            "object": "lib1_0.o", "address": format!("{addr:#x}"),
        }])
    );
    assert!(t["weakArchiveShadowed"].is_array(), "{t}");
    assert_std_provenance(&v);
    // The full lld output and the link map are kept, and the trace is recorded.
    assert_eq!(v["lld"]["log"], "work/lld.log");
    assert_eq!(v["lld"]["map"], "work/link.map");
    let log = std::fs::read_to_string(out.join("work/lld.log")).unwrap();
    assert!(log.contains(": definition of native_marker"), "{log}");
    assert!(out.join("work/link.map").is_file());
    assert_eq!(
        v["traceSymbolDefinitions"],
        serde_json::json!([{
            "symbol": "native_marker", "kind": "definition of", "file": "work/lib1_0.o",
        }])
    );

    // The same sibling without the export declared: rejected before the link.
    let no_export = SIBLING_TOML.replace("exports = [\"native_marker\"]", "exports = []");
    let e = stock::run(&cli(&no_export, &root.join("out2"))).unwrap_err();
    assert!(
        format!("{e:#}").contains("does not declare it as an export"),
        "{e:#}"
    );
}

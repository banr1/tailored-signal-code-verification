// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! `snapshot-fixture-diff` (`[OUTSIDE TCB]`): compare a regenerated process-snapshot fixture
//! with a committed one.
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[OUTSIDE TCB]` — a CI regression check. Lean proofs check the frozen
//!   bytes of a committed snapshot against the exported image; this tool checks that the rest
//!   of the fixture (link manifest, region layout, permissions, registers, symbols) still matches
//!   what the pinned link recipe and runner produce today.
//! - **Purpose:** `snapshot-fixture-diff <expected-dir> <actual-dir>` reads `link.json`,
//!   `main.snapshot.json` and `main.snapshot.bin` from both directories and fails on any
//!   difference except the ones that legitimately vary between runs:
//!   - the stack: its placement may move, so the stack region is compared by permission and by
//!     `top - sp`, registers that point into the stack are compared relative to the stack top,
//!     and the stack bytes (auxv random bytes, pointers) are not compared;
//!   - the bytes of writable load regions (the runtime stores a host thread id there): the
//!     number of differing bytes is reported, not rejected;
//!   - `bin.sha256`, which covers those bytes;
//!   - the scratch registers `x9`..`x17`, which hold no defined value at the stop (the C runtime
//!     leaves host-dependent values there; a theorem must not assume them);
//!   - in `link.json`, the ELF sha256 and the hashes of toolchain-cache inputs (musl objects and
//!     archives, recorded by file name): they embed toolchain install paths outside the loaded
//!     segments. The objects built from the image (`work/*.o`) are compared exactly;
//!   - for static-ELF fixture directories (containing `link.json` and the linked `.elf` binary
//!     without `main.snapshot.json`), every `PT_LOAD` segment and every byte outside `.symtab`
//!     must match byte-for-byte, and `.symtab` entries must match except for local `SHN_ABS`
//!     `$d` mapping symbols whose `st_value` records the toolchain install path length from
//!     `crt1.o`'s stripped `.debug_str`.
//!
//!   Each fixture must also be self-consistent: the `.bin` size and sha256 match its JSON, and
//!   the snapshot's ELF sha256 matches `link.json`.
//!
//! # When to Read This File
//! - Read this file to see which fixture fields CI checks exactly and which it relaxes.

use anyhow::{Context, Result, bail, ensure};
use object::Endianness;
use object::elf::{self, PT_LOAD, SHN_ABS, SHT_SYMTAB, STB_LOCAL, STT_NOTYPE};
use object::read::elf::{FileHeader, ProgramHeader, SectionHeader, Sym};
use serde_json::Value;
use sha2::{Digest, Sha256};
use std::path::Path;

/// One process-snapshot fixture directory (`link.json` + `main.snapshot.json` + `.bin`).
struct Fixture {
    link: Value,
    snap: Value,
    bin: Vec<u8>,
}

/// One static ELF fixture directory (`link.json` + `<elf.file>`).
struct ElfFixture {
    link: Value,
    elf: Vec<u8>,
}

fn read_json(p: &Path) -> Result<Value> {
    let s = std::fs::read_to_string(p).with_context(|| format!("cannot read {}", p.display()))?;
    serde_json::from_str(&s).with_context(|| format!("cannot parse {}", p.display()))
}

fn load(dir: &Path) -> Result<Fixture> {
    let link = read_json(&dir.join("link.json"))?;
    let snap = read_json(&dir.join("main.snapshot.json"))?;
    let file = snap["bin"]["file"].as_str().context("bin.file missing")?;
    let bin = std::fs::read(dir.join(file))
        .with_context(|| format!("cannot read {}", dir.join(file).display()))?;
    Ok(Fixture { link, snap, bin })
}

fn u(v: &Value, what: &str) -> Result<u64> {
    v.as_u64()
        .with_context(|| format!("{what} is not an unsigned integer"))
}

/// A region of a snapshot.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Region {
    start: u64,
    size: u64,
    perm: String,
    kind: String,
    bin_off: u64,
}

fn regions(snap: &Value) -> Result<Vec<Region>> {
    let rs = snap["regions"].as_array().context("regions missing")?;
    rs.iter()
        .map(|r| {
            Ok(Region {
                start: u(&r["start"], "region start")?,
                size: u(&r["size"], "region size")?,
                perm: r["perm"].as_str().context("region perm")?.to_string(),
                kind: r["kind"].as_str().context("region kind")?.to_string(),
                bin_off: u(&r["binOff"], "region binOff")?,
            })
        })
        .collect()
}

fn bytes<'a>(f: &'a Fixture, r: &Region) -> Result<&'a [u8]> {
    let lo = usize::try_from(r.bin_off)?;
    let hi = lo + usize::try_from(r.size)?;
    f.bin
        .get(lo..hi)
        .with_context(|| format!("region at {:#x} lies outside the .bin", r.start))
}

/// Check that a fixture is internally consistent.
fn self_check(f: &Fixture, name: &str) -> Result<()> {
    let bin = &f.snap["bin"];
    ensure!(
        u(&bin["size"], "bin.size")? == f.bin.len() as u64,
        "{name}: .bin size differs from bin.size"
    );
    ensure!(
        bin["sha256"].as_str() == Some(format!("{:x}", Sha256::digest(&f.bin)).as_str()),
        "{name}: .bin sha256 differs from bin.sha256"
    );
    ensure!(
        f.snap["elf"]["sha256"] == f.link["elf"]["sha256"],
        "{name}: snapshot elf.sha256 differs from link.json elf.sha256"
    );
    for r in regions(&f.snap)? {
        bytes(f, &r)?;
    }
    Ok(())
}

/// The stack top (exclusive end of the `stack` region) of a snapshot.
fn stack_top(rs: &[Region]) -> Result<(u64, u64)> {
    let mut it = rs.iter().filter(|r| r.kind == "stack");
    let s = it.next().context("no stack region")?;
    ensure!(it.next().is_none(), "several stack regions");
    Ok((s.start, s.start + s.size))
}

/// True if `path` names one of the musl C-runtime startup objects or compiler archives built in
/// the zig cache (`zig cc -target aarch64-linux-musl`).
fn is_toolchain_runtime_input(path: &str) -> bool {
    matches!(
        path,
        "crt1.o"
            | "crti.o"
            | "crtn.o"
            | "rcrt1.o"
            | "Scrt1.o"
            | "libc.a"
            | "libzigc.a"
            | "libcompiler_rt.a"
            | "libunwind.a"
    )
}

/// `link` without the hashes that depend on where the toolchain is installed: the musl C-runtime
/// objects and archives built in the zig cache embed build paths, and so does the executable
/// outside its loaded segments. The loaded bytes are compared separately (frozen regions
/// exactly).
fn toolchain_neutral(link: &Value) -> Value {
    let mut l = link.clone();
    if let Some(e) = l.get_mut("elf").and_then(Value::as_object_mut) {
        e.remove("sha256");
    }
    if let Some(ins) = l.get_mut("inputs").and_then(Value::as_array_mut) {
        for i in ins {
            let cached = i["path"].as_str().is_some_and(is_toolchain_runtime_input);
            if let (true, Some(o)) = (cached, i.as_object_mut()) {
                o.remove("sha256");
            }
        }
    }
    l
}

/// The JSON paths at which `e` and `a` differ, with both values.
fn json_diff(path: &str, e: &Value, a: &Value, out: &mut Vec<String>) {
    match (e, a) {
        (Value::Object(eo), Value::Object(ao)) => {
            let mut keys: Vec<&String> = eo.keys().chain(ao.keys()).collect();
            keys.sort();
            keys.dedup();
            for k in keys {
                let (ev, av) = (
                    eo.get(k).unwrap_or(&Value::Null),
                    ao.get(k).unwrap_or(&Value::Null),
                );
                json_diff(&format!("{path}.{k}"), ev, av, out);
            }
        }
        (Value::Array(ea), Value::Array(aa)) if ea.len() == aa.len() => {
            for (i, (ev, av)) in ea.iter().zip(aa).enumerate() {
                json_diff(&format!("{path}[{i}]"), ev, av, out);
            }
        }
        _ if e != a => out.push(format!("{path}: expected {e}, actual {a}")),
        _ => {}
    }
}

/// Compare `exp` and `act`; returns human-readable notes about tolerated differences.
fn compare(exp: &Fixture, act: &Fixture) -> Result<Vec<String>> {
    let mut notes = Vec::new();
    self_check(exp, "expected")?;
    self_check(act, "actual")?;
    let (el, al) = (toolchain_neutral(&exp.link), toolchain_neutral(&act.link));
    if el != exp.link || al != act.link {
        let mut d = Vec::new();
        json_diff("", &exp.link, &act.link, &mut d);
        for x in d {
            notes.push(format!("link.json {x} (toolchain-dependent; tolerated)"));
        }
    }
    let mut d = Vec::new();
    json_diff("", &el, &al, &mut d);
    if !d.is_empty() {
        bail!("link.json differs:\n  {}", d.join("\n  "));
    }
    // Top-level snapshot fields other than the relaxed ones must be identical.
    let (eo, ao) = (
        exp.snap.as_object().context("snapshot is not an object")?,
        act.snap.as_object().context("snapshot is not an object")?,
    );
    let mut keys: Vec<&String> = eo.keys().chain(ao.keys()).collect();
    keys.sort();
    keys.dedup();
    for k in keys {
        if matches!(k.as_str(), "regions" | "regs" | "bin") {
            continue;
        }
        let strip = |v: Option<&Value>| {
            let mut v = v.cloned();
            // The ELF sha256 is toolchain-dependent (see `toolchain_neutral`); each fixture's
            // own snapshot and `link.json` agree on it (`self_check`).
            if let (true, Some(o)) = (k == "elf", v.as_mut().and_then(Value::as_object_mut)) {
                o.remove("sha256");
            }
            v
        };
        ensure!(
            strip(eo.get(k)) == strip(ao.get(k)),
            "snapshot field `{k}` differs"
        );
    }
    ensure!(
        exp.snap["bin"]["file"] == act.snap["bin"]["file"],
        "bin.file differs"
    );

    let (er, ar) = (regions(&exp.snap)?, regions(&act.snap)?);
    ensure!(er.len() == ar.len(), "number of regions differs");
    let (es, et) = stack_top(&er)?;
    let (as_, at) = stack_top(&ar)?;
    for (e, a) in er.iter().zip(&ar) {
        ensure!(
            e.kind == a.kind && e.perm == a.perm,
            "region at {:#x}: kind/perm differ",
            e.start
        );
        if e.kind == "stack" {
            continue;
        }
        ensure!(
            e == a,
            "region layout differs: expected {e:?}, actual {a:?}"
        );
        let (eb, ab) = (bytes(exp, e)?, bytes(act, a)?);
        if e.perm.contains('w') {
            let n = eb.iter().zip(ab).filter(|(x, y)| x != y).count();
            if n > 0 {
                notes.push(format!(
                    "writable region {:#x}+{:#x}: {n} bytes differ (tolerated)",
                    e.start, e.size
                ));
            }
        } else {
            ensure!(eb == ab, "frozen region {:#x} bytes differ", e.start);
        }
    }
    if es != as_ {
        notes.push(format!(
            "stack moved: expected [{es:#x}, {et:#x}), actual [{as_:#x}, {at:#x}) (tolerated)"
        ));
    }

    // Registers: stack pointers relative to the stack top, everything else exactly.
    let (eg, ag) = (&exp.snap["regs"], &act.snap["regs"]);
    for k in ["pc", "cpsr", "tpidr_el0"] {
        ensure!(eg[k] == ag[k], "register {k} differs");
    }
    let reg = |name: String, e: &Value, a: &Value| -> Result<()> {
        let (e, a) = (u(e, &name)?, u(a, &name)?);
        if (es..=et).contains(&e) {
            ensure!(
                (as_..=at).contains(&a) && et - e == at - a,
                "register {name} differs relative to the stack top"
            );
        } else {
            ensure!(e == a, "register {name} differs");
        }
        Ok(())
    };
    reg("sp".into(), &eg["sp"], &ag["sp"])?;
    let (ex, ax) = (
        eg["x"].as_array().context("regs.x missing")?,
        ag["x"].as_array().context("regs.x missing")?,
    );
    ensure!(ex.len() == ax.len(), "number of x registers differs");
    for (i, (e, a)) in ex.iter().zip(ax).enumerate() {
        // x9..x17 are caller-saved scratch registers (AAPCS64) with no defined value at the
        // stop; the C runtime leaves host-dependent values there (e.g. a thread id).
        if (9..=17).contains(&i) {
            if e != a {
                notes.push(format!(
                    "scratch register x{i} differs: {e} vs {a} (tolerated)"
                ));
            }
            continue;
        }
        reg(format!("x{i}"), e, a)?;
    }
    Ok(notes)
}

fn load_elf(dir: &Path) -> Result<ElfFixture> {
    let link = read_json(&dir.join("link.json"))?;
    let file = link["elf"]["file"].as_str().context("elf.file missing")?;
    let elf = std::fs::read(dir.join(file))
        .with_context(|| format!("cannot read {}", dir.join(file).display()))?;
    Ok(ElfFixture { link, elf })
}

/// Compare two static ELF fixture directories (`link.json` + `<elf.file>`).
fn compare_elf(exp: &ElfFixture, act: &ElfFixture) -> Result<Vec<String>> {
    let mut notes = Vec::new();
    for (f, name) in [(exp, "expected"), (act, "actual")] {
        let sha = format!("{:x}", Sha256::digest(&f.elf));
        ensure!(
            f.link["elf"]["sha256"].as_str() == Some(sha.as_str()),
            "{name}: ELF sha256 differs from link.json elf.sha256"
        );
    }
    let (el, al) = (toolchain_neutral(&exp.link), toolchain_neutral(&act.link));
    if el != exp.link || al != act.link {
        let mut d = Vec::new();
        json_diff("", &exp.link, &act.link, &mut d);
        for x in d {
            notes.push(format!("link.json {x} (toolchain-dependent; tolerated)"));
        }
    }
    let mut d = Vec::new();
    json_diff("", &el, &al, &mut d);
    if !d.is_empty() {
        bail!("link.json differs:\n  {}", d.join("\n  "));
    }
    ensure!(
        exp.elf.len() == act.elf.len(),
        "ELF size differs: expected {}, actual {}",
        exp.elf.len(),
        act.elf.len()
    );
    let endian = Endianness::Little;
    let ehdr_e =
        elf::FileHeader64::<Endianness>::parse(&*exp.elf).context("expected ELF header")?;
    let ehdr_a = elf::FileHeader64::<Endianness>::parse(&*act.elf).context("actual ELF header")?;
    let ph_e = ehdr_e.program_headers(endian, &*exp.elf)?;
    let ph_a = ehdr_a.program_headers(endian, &*act.elf)?;
    ensure!(ph_e.len() == ph_a.len(), "ELF program header count differs");
    for (i, (pe, pa)) in ph_e.iter().zip(ph_a).enumerate() {
        ensure!(
            pe.p_type(endian) == pa.p_type(endian)
                && pe.p_flags(endian) == pa.p_flags(endian)
                && pe.p_offset(endian) == pa.p_offset(endian)
                && pe.p_vaddr(endian) == pa.p_vaddr(endian)
                && pe.p_paddr(endian) == pa.p_paddr(endian)
                && pe.p_filesz(endian) == pa.p_filesz(endian)
                && pe.p_memsz(endian) == pa.p_memsz(endian)
                && pe.p_align(endian) == pa.p_align(endian),
            "PT header[{i}] differs"
        );
        if pe.p_type(endian) == PT_LOAD {
            let lo = usize::try_from(pe.p_offset(endian))?;
            let hi = lo + usize::try_from(pe.p_filesz(endian))?;
            ensure!(
                exp.elf.get(lo..hi) == act.elf.get(lo..hi),
                "PT_LOAD[{i}] bytes at {:#x} differ",
                pe.p_vaddr(endian)
            );
        }
    }
    let sec_e = ehdr_e.sections(endian, &*exp.elf)?;
    let sec_a = ehdr_a.sections(endian, &*act.elf)?;
    let syms_e = sec_e.symbols(endian, &*exp.elf, SHT_SYMTAB)?;
    let syms_a = sec_a.symbols(endian, &*act.elf, SHT_SYMTAB)?;
    let sym_sh = sec_e.section(syms_e.section())?;
    let sym_lo = usize::try_from(sym_sh.sh_offset(endian))?;
    let sym_hi = sym_lo + usize::try_from(sym_sh.sh_size(endian))?;
    ensure!(
        exp.elf[..sym_lo] == act.elf[..sym_lo] && exp.elf[sym_hi..] == act.elf[sym_hi..],
        "ELF bytes outside .symtab differ"
    );
    ensure!(
        syms_e.len() == syms_a.len(),
        ".symtab entry count differs: {} vs {}",
        syms_e.len(),
        syms_a.len()
    );
    for (i, (se, sa)) in syms_e.symbols().iter().zip(syms_a.symbols()).enumerate() {
        let off = sym_lo + i * 24;
        if exp.elf[off..off + 24] == act.elf[off..off + 24] {
            continue;
        }
        let ne = syms_e.symbol_name(endian, se)?;
        let na = syms_a.symbol_name(endian, sa)?;
        let is_abs_map = |s: &elf::Sym64<Endianness>, n: &[u8]| {
            s.st_bind() == STB_LOCAL
                && s.st_type() == STT_NOTYPE
                && s.st_shndx(endian) == SHN_ABS
                && s.st_size(endian) == 0
                && n == b"$d"
        };
        ensure!(
            is_abs_map(se, ne) && is_abs_map(sa, na),
            ".symtab[{i}] (`{}`) differs",
            String::from_utf8_lossy(ne)
        );
        notes.push(format!(
            ".symtab[{i}] ($d SHN_ABS): st_value {:#x} vs {:#x} (toolchain-dependent; tolerated)",
            se.st_value(endian),
            sa.st_value(endian)
        ));
    }
    Ok(notes)
}

fn main() -> Result<()> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.len() != 2 || args.iter().any(|a| a == "-h" || a == "--help") {
        eprintln!(
            "Usage: snapshot-fixture-diff <expected-dir> <actual-dir>\n\n\
             Compare a regenerated process-snapshot or static-ELF fixture with a committed one.\n\n\
             Example:\n  snapshot-fixture-diff Examples/UnitTests/MySnapshot /tmp/regen"
        );
        std::process::exit(if args.len() == 2 { 0 } else { 2 });
    }
    let (exp_dir, act_dir) = (Path::new(&args[0]), Path::new(&args[1]));
    let notes = if exp_dir.join("main.snapshot.json").exists() {
        compare(&load(exp_dir)?, &load(act_dir)?)?
    } else {
        compare_elf(&load_elf(exp_dir)?, &load_elf(act_dir)?)?
    };
    for n in notes {
        println!("note: {n}");
    }
    println!("snapshot-fixture-diff: OK ({} vs {})", args[0], args[1]);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    fn fixture(stack_start: u64, data: u8, code: u8, x0: u64) -> Fixture {
        let bin: Vec<u8> = [vec![code; 16], vec![data; 16], vec![7; 32]].concat();
        let sha = format!("{:x}", Sha256::digest(&bin));
        let snap = json!({
            "schema": "arm64-proc-snapshot/1",
            "elf": { "sha256": "e" },
            "regions": [
                { "start": 0x1000, "size": 16, "perm": "r-x", "kind": "load", "binOff": 0 },
                { "start": 0x2000, "size": 16, "perm": "rw-", "kind": "load", "binOff": 16 },
                { "start": stack_start, "size": 32, "perm": "rw-", "kind": "stack", "binOff": 32 },
            ],
            "regs": { "x": [x0, 5], "sp": stack_start + 16, "pc": 0x1000, "cpsr": 0,
                      "tpidr_el0": null },
            "bin": { "file": "main.snapshot.bin", "size": bin.len(), "sha256": sha },
        });
        Fixture {
            link: json!({ "elf": { "sha256": "e" } }),
            snap,
            bin,
        }
    }

    #[test]
    fn identical_ok() {
        assert!(
            compare(&fixture(0x9000, 1, 2, 3), &fixture(0x9000, 1, 2, 3))
                .unwrap()
                .is_empty()
        );
    }

    #[test]
    fn tolerates_stack_move_and_writable_bytes() {
        let notes = compare(
            &fixture(0x9000, 1, 2, 0x9008),
            &fixture(0xa000, 9, 2, 0xa008),
        )
        .unwrap();
        assert_eq!(notes.len(), 2, "{notes:?}");
    }

    #[test]
    fn rejects_frozen_byte_change() {
        assert!(compare(&fixture(0x9000, 1, 2, 3), &fixture(0x9000, 1, 4, 3)).is_err());
    }

    #[test]
    fn rejects_register_change() {
        assert!(compare(&fixture(0x9000, 1, 2, 3), &fixture(0x9000, 1, 2, 4)).is_err());
        // x1 (argv) is compared; x9..x17 are tolerated scratch registers.
        let mut e = fixture(0x9000, 1, 2, 3);
        let mut a = fixture(0x9000, 1, 2, 3);
        e.snap["regs"]["x"] = json!([3, 5, 0, 0, 0, 0, 0, 0, 0, 1]);
        a.snap["regs"]["x"] = json!([3, 5, 0, 0, 0, 0, 0, 0, 0, 2]);
        assert_eq!(compare(&e, &a).unwrap().len(), 1);
        a.snap["regs"]["x"] = json!([3, 6, 0, 0, 0, 0, 0, 0, 0, 1]);
        assert!(compare(&e, &a).is_err());
        // A stack pointer that moved relative to the stack top.
        assert!(
            compare(
                &fixture(0x9000, 1, 2, 0x9008),
                &fixture(0xa000, 1, 2, 0xa010)
            )
            .is_err()
        );
    }

    #[test]
    fn tolerates_toolchain_cache_hashes_only() {
        let link = |elf: &str, crt: &str, main: &str, extra: &str| {
            json!({ "elf": { "sha256": elf }, "inputs": [
                { "path": "crt1.o", "sha256": crt },
                { "path": "work/main.o", "sha256": main },
                { "path": "extra.o", "sha256": extra },
            ]})
        };
        let mut e = fixture(0x9000, 1, 2, 3);
        e.link = link("e", "c1", "m1", "x1");
        let mut a = fixture(0x9000, 1, 2, 3);
        a.link = link("e", "c2", "m1", "x1");
        assert_eq!(compare(&e, &a).unwrap().len(), 1);
        a.link = link("e", "c1", "m2", "x1");
        assert!(compare(&e, &a).is_err());
        a.link = link("e", "c1", "m1", "x2");
        assert!(compare(&e, &a).is_err());
    }

    #[test]
    fn rejects_link_and_inconsistency() {
        let mut a = fixture(0x9000, 1, 2, 3);
        a.link["extra"] = json!(1);
        assert!(compare(&fixture(0x9000, 1, 2, 3), &a).is_err());
        let mut b = fixture(0x9000, 1, 2, 3);
        b.bin[0] ^= 1;
        assert!(compare(&fixture(0x9000, 1, 2, 3), &b).is_err());
    }

    #[test]
    fn elf_fixture_tolerates_abs_mapping_sym_and_rejects_load_diff() {
        // `VerifiedLibraries/` is part of every distribution of this repository (partial exports
        // drop some `CaseStudies/<Campaign>` directories), so use a fixture from there.
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let mut exp = load_elf(&root.join("VerifiedLibraries/RustStd/Testing/empty")).unwrap();
        // That fixture records `crt1.o` under `work/runtime/`; name it like a toolchain-cache
        // input (bare file name) so its sha256 is tolerated.
        let crt1 = exp.link["inputs"]
            .as_array()
            .unwrap()
            .iter()
            .position(|i| i["path"].as_str().is_some_and(|p| p.ends_with("crt1.o")))
            .expect("fixture links crt1.o");
        exp.link["inputs"][crt1]["path"] = json!("crt1.o");
        assert!(compare_elf(&exp, &exp).unwrap().is_empty());

        // Mutating `st_value` of a local `$d` SHN_ABS mapping symbol + `crt1.o` / `elf` sha256 is
        // tolerated.
        let mut act = ElfFixture {
            link: exp.link.clone(),
            elf: exp.elf.clone(),
        };
        let ehdr = elf::FileHeader64::<Endianness>::parse(&*exp.elf).unwrap();
        let sec = ehdr.sections(Endianness::Little, &*exp.elf).unwrap();
        let syms = sec
            .symbols(Endianness::Little, &*exp.elf, SHT_SYMTAB)
            .unwrap();
        let abs_map = syms
            .symbols()
            .iter()
            .position(|s| {
                s.st_bind() == STB_LOCAL
                    && s.st_type() == STT_NOTYPE
                    && s.st_shndx(Endianness::Little) == SHN_ABS
                    && syms.symbol_name(Endianness::Little, s).unwrap() == b"$d"
            })
            .expect("fixture has a local SHN_ABS `$d` mapping symbol");
        let sym_sh = sec.section(syms.section()).unwrap();
        let sym_lo = sym_sh.sh_offset(Endianness::Little) as usize;
        act.elf[sym_lo + abs_map * 24 + 8] ^= 0x7f;
        let new_sha = format!("{:x}", Sha256::digest(&act.elf));
        act.link["elf"]["sha256"] = json!(new_sha);
        act.link["inputs"][crt1]["sha256"] = json!("different_crt1_sha");
        let notes = compare_elf(&exp, &act).unwrap();
        assert_eq!(notes.len(), 3, "{notes:?}");

        // Mutating a PT_LOAD byte is rejected even when elf.sha256 is updated.
        let load_off = ehdr
            .program_headers(Endianness::Little, &*exp.elf)
            .unwrap()
            .iter()
            .find(|p| p.p_type(Endianness::Little) == PT_LOAD && p.p_filesz(Endianness::Little) > 0)
            .map(|p| p.p_offset(Endianness::Little) as usize)
            .expect("fixture has a non-empty PT_LOAD");
        let mut bad = ElfFixture {
            link: exp.link.clone(),
            elf: exp.elf.clone(),
        };
        bad.elf[load_off] ^= 1;
        bad.link["elf"]["sha256"] = json!(format!("{:x}", Sha256::digest(&bad.elf)));
        assert!(compare_elf(&exp, &bad).is_err());
    }
}

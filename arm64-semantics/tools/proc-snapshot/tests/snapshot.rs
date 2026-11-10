// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Integration test (`[testing]`): build a tiny static non-PIE AArch64 ELF with `zig cc`, snapshot
//! it under qemu-aarch64, and check the snapshot against the ELF file.
//!
//! Skipped (with a message) when `zig` or qemu is missing, unless `REQUIRE_PROC_SNAPSHOT=1`.
//! qemu is taken from `$QEMU_AARCH64`, else the `scripts/fetch-qemu-aarch64` cache, else `PATH`.

use object::read::elf::{ElfFile64, ProgramHeader};
use object::{Endianness, Object, ObjectSymbol};
use serde_json::Value;
use std::path::{Path, PathBuf};
use std::process::Command;

const PROG: &str = r#"
#include <stdio.h>
#include <unistd.h>
volatile unsigned char marker[16] = {0xde,0xad,0xbe,0xef,1,2,3,4,5,6,7,8,9,10,11,12};
unsigned char zeros[3000];
int main(int argc, char **argv) {
    if (argc > 1) { printf("%p\n", sbrk(0)); return 0; }
    return marker[0] + zeros[5];
}
"#;

fn skip(msg: &str) -> bool {
    if std::env::var("REQUIRE_PROC_SNAPSHOT").as_deref() == Ok("1") {
        panic!("REQUIRE_PROC_SNAPSHOT=1 but {msg}");
    }
    eprintln!("skipping proc-snapshot integration test: {msg}");
    true
}

fn find_qemu() -> Option<PathBuf> {
    if let Some(p) = std::env::var_os("QEMU_AARCH64") {
        return Some(p.into());
    }
    let cache = std::env::var_os("ARM64_UPSTREAM_CACHE")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            let base = std::env::var_os("XDG_CACHE_HOME")
                .map(PathBuf::from)
                .unwrap_or_else(|| {
                    PathBuf::from(std::env::var_os("HOME").unwrap_or_default()).join(".cache")
                });
            base.join("arm64-verification-engine")
        });
    let mut cached: Vec<PathBuf> = std::fs::read_dir(cache.join("qemu"))
        .into_iter()
        .flatten()
        .flatten()
        .map(|e| e.path().join("qemu-aarch64"))
        .filter(|p| p.is_file())
        .collect();
    cached.sort();
    if let Some(p) = cached.pop() {
        return Some(p);
    }
    let ok = Command::new("qemu-aarch64")
        .arg("--version")
        .output()
        .is_ok_and(|o| o.status.success());
    ok.then(|| "qemu-aarch64".into())
}

fn build_prog(dir: &Path) -> Option<PathBuf> {
    let src = dir.join("prog.c");
    let out = dir.join("prog");
    std::fs::write(&src, PROG).unwrap();
    let st = Command::new("zig")
        .args([
            "cc",
            "-target",
            "aarch64-linux-musl",
            "-static",
            "-fno-pie",
            "-no-pie",
            "-O1",
            "-o",
        ])
        .arg(&out)
        .arg(&src)
        .env("ZIG_GLOBAL_CACHE_DIR", dir.join("zig-cache"))
        .status()
        .ok()?;
    assert!(st.success(), "zig cc failed");
    Some(out)
}

fn n(v: &Value) -> u64 {
    v.as_u64().unwrap_or_else(|| panic!("not an integer: {v}"))
}

/// Bytes of `[addr, addr+len)` from the snapshot.
fn snap_bytes<'a>(j: &Value, bin: &'a [u8], addr: u64, len: u64) -> &'a [u8] {
    for r in j["regions"].as_array().unwrap() {
        let (s, z, o) = (n(&r["start"]), n(&r["size"]), n(&r["binOff"]));
        if s <= addr && addr + len <= s + z {
            let off = (o + addr - s) as usize;
            return &bin[off..off + len as usize];
        }
    }
    panic!("{addr:#x} not in snapshot");
}

#[test]
fn snapshot_tiny_static_elf() {
    let Some(qemu) = find_qemu() else {
        skip("qemu-aarch64 not found (run scripts/fetch-qemu-aarch64 or set QEMU_AARCH64)");
        return;
    };
    if Command::new("zig").arg("version").output().is_err() {
        skip("zig not on PATH");
        return;
    }
    let tmp = tempfile::tempdir().unwrap();
    let prog = build_prog(tmp.path()).unwrap();
    let run = |out: &Path| {
        let st = Command::new(env!("CARGO_BIN_EXE_proc-snapshot"))
            .args(["snapshot", "--argv0", "prog", "--elf"])
            .arg(&prog)
            .arg("--qemu")
            .arg(&qemu)
            .arg("--out-dir")
            .arg(out)
            .arg("--input")
            .arg(tmp.path().join("prog.c"))
            .status()
            .unwrap();
        assert!(st.success(), "proc-snapshot failed");
    };
    let out = tmp.path().join("out");
    run(&out);
    // Reproducible: ASLR off + `-seed 0` make the exec-entry snapshot byte-identical across runs.
    let out2 = tmp.path().join("out2");
    run(&out2);
    for f in ["entry.snapshot.bin", "entry.snapshot.json"] {
        assert_eq!(
            std::fs::read(out.join(f)).unwrap(),
            std::fs::read(out2.join(f)).unwrap(),
            "{f} differs between runs"
        );
    }

    let elf_data = std::fs::read(&prog).unwrap();
    let elf = ElfFile64::<Endianness>::parse(&*elf_data).unwrap();
    let e = elf.endian();
    let sym = |name: &str| elf.symbols().find(|s| s.name() == Ok(name)).unwrap();
    let main_addr = sym("main").address();

    for stop in ["entry", "main"] {
        let text = std::fs::read_to_string(out.join(format!("{stop}.snapshot.json"))).unwrap();
        assert!(text.ends_with("}\n"));
        let j: Value = serde_json::from_str(&text).unwrap();
        let bin = std::fs::read(out.join(format!("{stop}.snapshot.bin"))).unwrap();
        assert_eq!(j["schema"], "arm64-proc-snapshot/1");
        assert_eq!(n(&j["bin"]["size"]), bin.len() as u64);
        assert_eq!(j["argv"], serde_json::json!(["prog"]));
        assert_eq!(j["envp"], serde_json::json!([]));
        assert_eq!(j["regs"]["x"].as_array().unwrap().len(), 31);
        let (pc, sp) = (n(&j["regs"]["pc"]), n(&j["regs"]["sp"]));
        assert_eq!(sp % 16, 0, "sp {sp:#x} not 16-byte aligned");
        if stop == "main" {
            assert_eq!(j["stop"], "main");
            assert_eq!(pc, main_addr);
        } else {
            assert_eq!(j["stop"], "exec-entry");
            assert_eq!(pc, elf.entry());
            assert_eq!(n(&j["elf"]["entry"]), elf.entry());
        }
        // Region file bytes equal the ELF PT_LOAD file bytes + zero bss (writable segments may be
        // modified by libc start-up before `main`, so only check them at exec entry).
        for ph in elf.elf_program_headers() {
            if ph.p_type(e) != object::elf::PT_LOAD
                || (stop == "main" && ph.p_flags(e) & object::elf::PF_W != 0)
            {
                continue;
            }
            let (va, off, fsz, msz) =
                (ph.p_vaddr(e), ph.p_offset(e), ph.p_filesz(e), ph.p_memsz(e));
            let file_part = &elf_data[off as usize..(off + fsz) as usize];
            assert_eq!(
                snap_bytes(&j, &bin, va, fsz),
                file_part,
                "{stop}: PT_LOAD at {va:#x}"
            );
            assert!(
                snap_bytes(&j, &bin, va + fsz, msz - fsz)
                    .iter()
                    .all(|&b| b == 0),
                "{stop}: bss"
            );
        }
        let m = sym("marker");
        assert_eq!(m.size(), 16);
        assert_eq!(
            snap_bytes(&j, &bin, m.address(), 4),
            &[0xde, 0xad, 0xbe, 0xef]
        );
        let syms = j["symbols"].as_array().unwrap();
        assert!(
            syms.iter()
                .any(|s| s["name"] == "marker" && n(&s["addr"]) == m.address())
        );
        let kinds: Vec<_> = j["regions"]
            .as_array()
            .unwrap()
            .iter()
            .map(|r| r["kind"].as_str().unwrap())
            .collect();
        assert!(kinds.contains(&"stack"));
    }

    // Record what qemu-user's brk really is, so `brkStart` is checked against the runner.
    let o = Command::new(&qemu)
        .env_clear()
        .arg(&prog)
        .arg("x")
        .output()
        .unwrap();
    let brk = u64::from_str_radix(
        String::from_utf8(o.stdout)
            .unwrap()
            .trim()
            .trim_start_matches("0x"),
        16,
    )
    .unwrap();
    let j: Value =
        serde_json::from_str(&std::fs::read_to_string(out.join("main.snapshot.json")).unwrap())
            .unwrap();
    assert_eq!(brk, n(&j["brkStart"]), "qemu brk differs from brkStart");

    // Verify `--entry-only` with `--arg` and `--env` flags.
    let out_entry = tmp.path().join("out_entry");
    let st = Command::new(env!("CARGO_BIN_EXE_proc-snapshot"))
        .args([
            "snapshot",
            "--entry-only",
            "--argv0",
            "prog",
            "--arg",
            "--flag",
            "--arg",
            "hello world",
            "--env",
            "FOO=bar",
            "--env",
            "EMPTY=",
            "--elf",
        ])
        .arg(&prog)
        .arg("--qemu")
        .arg(&qemu)
        .arg("--out-dir")
        .arg(&out_entry)
        .status()
        .unwrap();
    assert!(st.success(), "proc-snapshot --entry-only failed");
    assert!(!out_entry.join("main.snapshot.json").exists());
    let je: Value = serde_json::from_str(
        &std::fs::read_to_string(out_entry.join("entry.snapshot.json")).unwrap(),
    )
    .unwrap();
    assert_eq!(
        je["argv"],
        serde_json::json!(["prog", "--flag", "hello world"])
    );
    assert_eq!(je["envp"], serde_json::json!(["FOO=bar", "EMPTY="]));
}

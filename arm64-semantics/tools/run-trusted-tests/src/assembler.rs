// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Batch AArch64 assembly to 32-bit machine words via LLVM (`rustc` `global_asm!` + `ld.lld`)
//! (`[TEST ONLY]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[TEST ONLY]` (provides ground-truth AArch64 instruction encodings for
//!   `run-trusted-tests` so Lean's decoder in `Arm64/Trusted/ISA/Decode.lean` is tested against LLVM).
//! - **Purpose:** Compiles batches of `(base_addr, asm)` snippets in a single `rustc`
//!   `global_asm!` invocation, links each snippet at its exact target VMA with a generated linker
//!   script and `ld.lld`, and extracts the 32-bit little-endian instruction words.
//!
//! # Key Types & Functions
//! - [`LlvmAssembler`]: Discovers `ld.lld` and provides [`LlvmAssembler::assemble_words`] and
//!   [`LlvmAssembler::assemble_batch`].
//! - `find_required_tool`: Searches `PATH` and rustup's LLVM tools directory for `ld.lld`.
//!
//! # When to Read This File
//! - The header suffices unless you are debugging assembly label scoping, linker VMA placement,
//!   or `ld.lld` discovery across toolchains.

use std::collections::BTreeSet;
use std::fs;
use std::path::Path;
use std::process::Command;

use anyhow::{Context, Result, anyhow, bail};
use object::{Object, ObjectSection};
use walkdir::WalkDir;

pub struct LlvmAssembler {
    lld: String,
}

impl LlvmAssembler {
    pub fn discover() -> Result<Self> {
        let lld = find_required_tool("ld.lld")?;
        Ok(Self { lld })
    }

    /// Assemble a single AArch64 assembly snippet at `base_addr` into 32-bit little-endian instruction words.
    pub fn assemble_words(&self, asm: &str, base_addr: u64) -> Result<Vec<u32>> {
        let mut batch = self.assemble_batch(&[(base_addr, asm)])?;
        batch
            .pop()
            .ok_or_else(|| anyhow!("empty batch assembly result"))
    }

    /// Assemble a batch of `(base_addr, asm)` snippets in a single `rustc` (`global_asm!`) + `ld.lld` invocation.
    pub fn assemble_batch(&self, items: &[(u64, &str)]) -> Result<Vec<Vec<u32>>> {
        if items.is_empty() {
            return Ok(Vec::new());
        }

        let tmp =
            tempfile::tempdir().context("failed to create temp directory for LLVM assembly")?;
        let obj_path = tmp.path().join("batch.o");
        let ld_path = tmp.path().join("batch.ld");
        let elf_path = tmp.path().join("batch.elf");

        let mut asm_sections = String::new();
        let mut ld_script = String::from("SECTIONS {\n");

        for (i, (base_addr, raw_asm)) in items.iter().enumerate() {
            let scoped = scope_local_labels(raw_asm, i);
            asm_sections.push_str(&format!(
                ".section .text.tc_{i}, \"ax\", @progbits\n.p2align 2\n{scoped}\n\n"
            ));
            let lma = 0x1000_0000u64 + (i as u64) * 0x10000;
            ld_script.push_str(&format!(
                "  .text.tc_{i} {base_addr:#x} : AT({lma:#x}) {{ *(.text.tc_{i}) }}\n"
            ));
        }
        ld_script.push_str("  /DISCARD/ : { *(.note.*) *(.comment) *(.eh_frame*) }\n}\n");
        fs::write(&ld_path, &ld_script)?;

        Self::compile_asm_with_rustc(&asm_sections, &obj_path, tmp.path())?;

        let link_out = Command::new(&self.lld)
            .args(["--no-check-sections", "-T"])
            .arg(&ld_path)
            .arg("-o")
            .arg(&elf_path)
            .arg(&obj_path)
            .output()
            .with_context(|| format!("failed to invoke `{}`", self.lld))?;

        if !link_out.status.success() {
            bail!(
                "`ld.lld` failed ({}):\n{}",
                link_out.status,
                String::from_utf8_lossy(&link_out.stderr)
            );
        }

        let elf_bytes = fs::read(&elf_path)?;
        let elf = object::File::parse(&*elf_bytes).context("failed to parse linked ELF image")?;

        let mut results = Vec::with_capacity(items.len());
        for i in 0..items.len() {
            let sec_name = format!(".text.tc_{i}");
            let section = elf
                .section_by_name(&sec_name)
                .ok_or_else(|| anyhow!("missing section `{sec_name}` in linked ELF"))?;
            let data = section.data()?;
            if data.len() % 4 != 0 {
                bail!(
                    "section `{sec_name}` byte length {} is not a multiple of 4",
                    data.len()
                );
            }
            let words: Vec<u32> = data
                .chunks_exact(4)
                .map(|c| u32::from_le_bytes([c[0], c[1], c[2], c[3]]))
                .collect();
            if words.is_empty() {
                bail!("section `{sec_name}` produced 0 instruction words");
            }
            results.push(words);
        }

        Ok(results)
    }

    fn compile_asm_with_rustc(asm_source: &str, obj_path: &Path, tmp_dir: &Path) -> Result<()> {
        let rs_path = tmp_dir.join("batch.rs");
        let escaped_asm = asm_source.replace('{', "{{").replace('}', "}}");
        let rust_src = format!(
            "#![no_std]\ncore::arch::global_asm!(r#\"\n{}\n\"#);\n",
            escaped_asm
        );
        fs::write(&rs_path, rust_src)?;
        let out = Command::new("rustc")
            .args([
                "--edition=2024",
                "--target=aarch64-unknown-linux-gnu",
                "-C",
                "target-feature=+v8.2a,+aes,+sha2,+sha3,+neon,+lse,+rcpc,+rcpc2,+crc",
                "--crate-type=lib",
                "--emit=obj",
            ])
            .arg(&rs_path)
            .arg("-o")
            .arg(obj_path)
            .output()
            .context("failed to invoke `rustc` for AArch64 assembly")?;
        if !out.status.success() {
            bail!(
                "`rustc --emit=obj` assembly failed ({}):\n{}",
                out.status,
                String::from_utf8_lossy(&out.stderr)
            );
        }
        Ok(())
    }
}

fn is_ident_char(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_' || b == b'.'
}

/// Prefix any label defined in `asm` with `.Ltc_{idx}_` so multiple snippets can share one `.s` file.
fn scope_local_labels(asm: &str, idx: usize) -> String {
    let mut labels = BTreeSet::new();
    for line in asm.lines() {
        let trimmed = line.trim();
        if let Some((before_colon, _)) = trimmed.split_once(':') {
            let cand = before_colon.trim();
            if !cand.is_empty()
                && cand.bytes().all(is_ident_char)
                && !cand.bytes().next().unwrap().is_ascii_digit()
            {
                labels.insert(cand.to_string());
            }
        }
    }
    if labels.is_empty() {
        return asm.to_string();
    }

    let mut result = String::with_capacity(asm.len() + 32);
    let bytes = asm.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        if is_ident_char(bytes[i]) && !bytes[i].is_ascii_digit() {
            let start = i;
            while i < bytes.len() && is_ident_char(bytes[i]) {
                i += 1;
            }
            let token = &asm[start..i];
            if labels.contains(token) {
                result.push_str(&format!(".Ltc_{idx}_{token}"));
            } else {
                result.push_str(token);
            }
        } else {
            let ch = asm[i..].chars().next().unwrap();
            result.push(ch);
            i += ch.len_utf8();
        }
    }
    result
}

fn find_optional_tool(name: &str) -> Option<String> {
    if let Ok(p) = which::which(name) {
        return Some(p.to_string_lossy().into_owned());
    }
    if let Ok(out) = Command::new("rustc").args(["--print", "sysroot"]).output() {
        let sysroot = String::from_utf8_lossy(&out.stdout).trim().to_string();
        for entry in WalkDir::new(&sysroot).into_iter().flatten() {
            if entry.file_type().is_file() && entry.file_name() == name {
                return Some(entry.path().to_string_lossy().into_owned());
            }
        }
    }
    None
}

fn find_required_tool(name: &str) -> Result<String> {
    find_optional_tool(name)
        .ok_or_else(|| anyhow!("could not find `{name}` in PATH or `rustc --print sysroot`"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_assemble_basic_and_branches() {
        let asm = LlvmAssembler::discover().expect("discover LLVM assembler");
        let words = asm
            .assemble_words(
                "loop:\ncbz x1, done\nadd x0, x0, x1\nsub x1, x1, #1\nb loop\ndone:\nret",
                0x10000,
            )
            .expect("assemble loop");
        assert_eq!(words.len(), 5);
        assert_eq!(*words.last().unwrap(), 0xd65f03c0); // ret
    }

    #[test]
    fn test_assemble_aes_and_pc_rel() {
        let asm = LlvmAssembler::discover().expect("discover LLVM assembler");
        let words = asm
            .assemble_words(
                "adr x2, target\nadrp x3, target\naese v0.16b, v1.16b\naesmc v0.16b, v0.16b\nst1 { v0.b }[15], [x12], #1\ntarget:\nnop\nret",
                0x10000,
            )
            .expect("assemble aes + neon braces + pc_rel via rustc");
        assert_eq!(words.len(), 7);
        assert_eq!(words[2], 0x4e284820); // aese v0.16b, v1.16b
        assert_eq!(words[3], 0x4e286800); // aesmc v0.16b, v0.16b
    }
}

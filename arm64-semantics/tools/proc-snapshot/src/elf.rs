// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! ELF facts `proc-snapshot` needs (`[CASE-STUDIES TCB]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[CASE-STUDIES TCB]` — PT_LOAD segments decide which memory is dumped;
//!   symbols decide where the `main` stop happens (trusted only by snapshot-based proofs, outside
//!   the core engine `[tcb]`).
//! - **Purpose:** Reads a static AArch64 `ET_EXEC` ELF with the `object` crate: entry point,
//!   PT_LOAD segments (vaddr, memsz, file range, flags), and defined `.symtab` symbols.
//!
//! # Key Types & Functions
//! - [`ElfInfo::parse`], [`Segment`], [`Symbol`].
//!
//! # When to Read This File
//! - Read this file when auditing which segments become snapshot regions.

use anyhow::{Result, ensure};
use object::elf::{EM_AARCH64, ET_EXEC, PF_R, PF_W, PF_X, PT_LOAD};
use object::read::elf::{ElfFile64, FileHeader, ProgramHeader};
use object::{Endianness, Object, ObjectSymbol, SymbolKind};

/// One PT_LOAD program header.
#[derive(Debug, Clone)]
pub struct Segment {
    pub vaddr: u64,
    pub memsz: u64,
    pub flags: u32,
}

impl Segment {
    /// `"rwx"`-style permission string from `p_flags`.
    pub fn perm(&self) -> String {
        let f = |bit, c| if self.flags & bit != 0 { c } else { '-' };
        [f(PF_R, 'r'), f(PF_W, 'w'), f(PF_X, 'x')].iter().collect()
    }
}

/// One defined, named `.symtab` symbol.
#[derive(Debug, Clone, serde::Serialize)]
pub struct Symbol {
    pub name: String,
    pub addr: u64,
    pub size: u64,
}

pub struct ElfInfo {
    pub entry: u64,
    pub segments: Vec<Segment>,
    /// Sorted by name, then address.
    pub symbols: Vec<Symbol>,
}

impl ElfInfo {
    pub fn parse(data: &[u8]) -> Result<Self> {
        let file = ElfFile64::<Endianness>::parse(data)?;
        let (hdr, e) = (file.elf_header(), file.endian());
        ensure!(hdr.e_machine(e) == EM_AARCH64, "elf: not an AArch64 ELF");
        ensure!(
            hdr.e_type(e) == ET_EXEC,
            "elf: not a static non-PIE ET_EXEC executable"
        );
        let segments = file
            .elf_program_headers()
            .iter()
            .filter(|p| p.p_type(e) == PT_LOAD && p.p_memsz(e) > 0)
            .map(|p| Segment {
                vaddr: p.p_vaddr(e),
                memsz: p.p_memsz(e),
                flags: p.p_flags(e),
            })
            .collect();
        let mut symbols: Vec<Symbol> = file
            .symbols()
            .filter(|s| {
                s.is_definition() && !matches!(s.kind(), SymbolKind::Section | SymbolKind::File)
            })
            .filter_map(|s| {
                let name = s.name().ok().filter(|n| !n.is_empty())?;
                Some(Symbol {
                    name: name.to_string(),
                    addr: s.address(),
                    size: s.size(),
                })
            })
            .collect();
        symbols.sort_by(|a, b| (&a.name, a.addr, a.size).cmp(&(&b.name, b.addr, b.size)));
        Ok(Self {
            entry: hdr.e_entry(e),
            segments,
            symbols,
        })
    }

    /// Unique address of a defined symbol.
    pub fn symbol(&self, name: &str) -> Result<u64> {
        let hits: Vec<_> = self.symbols.iter().filter(|s| s.name == name).collect();
        ensure!(
            hits.len() == 1,
            "elf: expected exactly one symbol `{name}`, found {}",
            hits.len()
        );
        Ok(hits[0].addr)
    }
}

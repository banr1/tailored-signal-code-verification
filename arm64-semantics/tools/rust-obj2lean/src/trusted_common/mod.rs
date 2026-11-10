// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Trusted Common Library (`trusted_common`) — `[TCB]`.
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[TCB]` (defines the pure in-memory relocatable-object IR produced by
//!   `trusted_extractor`; contains **zero** CLI/config parsing, compiler orchestration,
//!   instruction decoding, or Lean theorem generation).
//! - **Purpose:** Provides the Rust-side relocatable ELF IR that `trusted_extractor` produces,
//!   external symbol declaration types ([`ExternKind`], [`ExternDecl`], [`ConfiguredExtern`]),
//!   `Obj` module emission metadata ([`ObjModuleMeta`]), Lean string escaping
//!   ([`lean_string_lit`]), and SHA-256 provenance hashing ([`sha256_hex`]).
//!
//! # Key Types & Functions
//! - [`SecKind`], [`ALLOWED_SHF`], [`is_relro_data`]: Allocated ELF section classification.
//! - [`RelocType`], [`ObjReloc`], [`ComdatGroup`], [`ObjSection`], [`SymSection`], [`SymKind`],
//!   [`SymBind`], [`ObjSymbol`], [`ObjObject`]: Relocatable ELF64 object IR.
//! - [`ExternKind`], [`ExternDecl`], [`ConfiguredExtern`], [`Extraction`]: External symbol
//!   declarations and extracted object bundle.
//! - [`ObjModuleMeta`], [`lean_string_lit`], [`upper_camel`], [`sha256_hex`]: Lean `Obj` module
//!   naming, string literal escaping, and SHA-256 digest helpers.
//!
//! # When to Read This File
//! - Read this file when extending supported ELF relocation kinds ([`RelocType`]) or inspecting
//!   [`ObjObject`] / [`ObjSection`] / [`ExternDecl`] definitions.

use std::path::PathBuf;

use sha2::{Digest, Sha256};

// ---------------------------------------------------------------------------
// SHA-256 provenance helper
// ---------------------------------------------------------------------------

/// Compute lowercase hex-encoded SHA-256 digest of `data`.
pub fn sha256_hex(data: impl AsRef<[u8]>) -> String {
    hex::encode(Sha256::digest(data))
}

// ---------------------------------------------------------------------------
// Relocatable object model (Rust-side ELF IR produced by `trusted_extractor`)
// ---------------------------------------------------------------------------

/// Whether `name` is a RELRO data section (`.data.rel.ro`, `.data.rel.ro.*`).
pub fn is_relro_data(name: &str) -> bool {
    name == ".data.rel.ro" || name.starts_with(".data.rel.ro.")
}

/// Kind of an allocated section, derived from its ELF type, flags, and name.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SecKind {
    Text,
    Rodata,
    Data,
    Bss,
    Tdata,
    Tbss,
}

/// Bitmask of ELF section flags accepted on allocated execution sections.
pub const ALLOWED_SHF: u64 = (object::elf::SHF_ALLOC
    | object::elf::SHF_WRITE
    | object::elf::SHF_EXECINSTR
    | object::elf::SHF_TLS
    | object::elf::SHF_MERGE
    | object::elf::SHF_STRINGS
    | object::elf::SHF_GNU_RETAIN) as u64;

impl SecKind {
    /// Short display name (`.text`, `.rodata`, ...), used in diagnostics.
    pub fn lean_ctor(self) -> &'static str {
        match self {
            SecKind::Text => ".text",
            SecKind::Rodata => ".rodata",
            SecKind::Data => ".data",
            SecKind::Bss => ".bss",
            SecKind::Tdata => ".tdata",
            SecKind::Tbss => ".tbss",
        }
    }

    /// `SHT_NOBITS` kinds: no bytes in the file, `size` gives the length.
    pub fn is_nobits(self) -> bool {
        matches!(self, SecKind::Bss | SecKind::Tbss)
    }

    /// Classify an allocated section named `name` from its ELF `sh_type` and `sh_flags`;
    /// `None` if the section is not allocated or unsupported.
    pub fn classify(name: &str, sh_type: u32, sh_flags: u64) -> Option<SecKind> {
        use object::elf::*;
        if sh_flags & (SHF_ALLOC as u64) == 0 || name == ".eh_frame" {
            return None;
        }
        if sh_flags & !ALLOWED_SHF != 0 {
            return None;
        }
        let write = sh_flags & (SHF_WRITE as u64) != 0;
        let exec = sh_flags & (SHF_EXECINSTR as u64) != 0;
        let tls = sh_flags & (SHF_TLS as u64) != 0;
        match sh_type {
            SHT_PROGBITS if exec && !write && !tls => Some(SecKind::Text),
            SHT_PROGBITS if tls && !exec => Some(SecKind::Tdata),
            SHT_NOBITS if tls && !exec => Some(SecKind::Tbss),
            SHT_PROGBITS if write && !exec && is_relro_data(name) => Some(SecKind::Rodata),
            SHT_INIT_ARRAY | SHT_FINI_ARRAY | SHT_PREINIT_ARRAY if write && !exec && !tls => {
                Some(SecKind::Rodata)
            }
            SHT_PROGBITS if write && !exec => Some(SecKind::Data),
            SHT_NOBITS if write && !exec => Some(SecKind::Bss),
            SHT_PROGBITS if !write && !exec => Some(SecKind::Rodata),
            _ => None,
        }
    }
}

/// An AArch64 ELF relocation type (`R_AARCH64_*`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RelocType {
    None,
    Abs64,
    Abs32,
    Abs16,
    Prel64,
    Prel32,
    Prel16,
    MovwUabsG0,
    MovwUabsG0Nc,
    MovwUabsG1,
    MovwUabsG1Nc,
    MovwUabsG2,
    MovwUabsG2Nc,
    MovwUabsG3,
    MovwSabsG0,
    MovwSabsG1,
    MovwSabsG2,
    Plt32,
    LdPrelLo19,
    AdrPrelLo21,
    AdrPrelPgHi21,
    AdrPrelPgHi21Nc,
    AddAbsLo12Nc,
    Ldst8AbsLo12Nc,
    Tstbr14,
    Condbr19,
    Jump26,
    Call26,
    Ldst16AbsLo12Nc,
    Ldst32AbsLo12Nc,
    Ldst64AbsLo12Nc,
    MovwPrelG0,
    MovwPrelG0Nc,
    MovwPrelG1,
    MovwPrelG1Nc,
    MovwPrelG2,
    MovwPrelG2Nc,
    MovwPrelG3,
    Ldst128AbsLo12Nc,
    AdrGotPage,
    Ld64GotLo12Nc,
    Ld64GotpageLo15,
    TlsgdAdrPrel21,
    TlsgdAdrPage21,
    TlsgdAddLo12Nc,
    TlsldAdrPrel21,
    TlsldAdrPage21,
    TlsldAddLo12Nc,
    TlsldAddDtprelHi12,
    TlsldAddDtprelLo12,
    TlsldAddDtprelLo12Nc,
    TlsieMovwGottprelG1,
    TlsieMovwGottprelG0Nc,
    TlsieAdrGottprelPage21,
    TlsieLd64GottprelLo12Nc,
    TlsieLdGottprelPrel19,
    TlsleMovwTprelG2,
    TlsleMovwTprelG1,
    TlsleMovwTprelG1Nc,
    TlsleMovwTprelG0,
    TlsleMovwTprelG0Nc,
    TlsleAddTprelHi12,
    TlsleAddTprelLo12,
    TlsleAddTprelLo12Nc,
    TlsleLdst8TprelLo12Nc,
    TlsleLdst16TprelLo12Nc,
    TlsleLdst32TprelLo12Nc,
    TlsleLdst64TprelLo12Nc,
    TlsleLdst128TprelLo12Nc,
    TlsdescLdPrel19,
    TlsdescAdrPrel21,
    TlsdescAdrPage21,
    TlsdescLd64Lo12,
    TlsdescAddLo12,
    TlsdescCall,
    Copy,
    GlobDat,
    JumpSlot,
    Relative,
    TlsDtpmod,
    TlsDtprel,
    TlsTprel,
    Tlsdesc,
    Irelative,
    /// Any other `r_type`; `load` rejects it.
    Other(u32),
}

impl RelocType {
    /// Map an ELF `r_type` to the Lean constructor (numbers from the AArch64 ELF ABI).
    pub fn from_r_type(r_type: u32) -> Self {
        match r_type {
            0 | 256 => RelocType::None,
            257 => RelocType::Abs64,
            258 => RelocType::Abs32,
            259 => RelocType::Abs16,
            260 => RelocType::Prel64,
            261 => RelocType::Prel32,
            262 => RelocType::Prel16,
            263 => RelocType::MovwUabsG0,
            264 => RelocType::MovwUabsG0Nc,
            265 => RelocType::MovwUabsG1,
            266 => RelocType::MovwUabsG1Nc,
            267 => RelocType::MovwUabsG2,
            268 => RelocType::MovwUabsG2Nc,
            269 => RelocType::MovwUabsG3,
            270 => RelocType::MovwSabsG0,
            271 => RelocType::MovwSabsG1,
            272 => RelocType::MovwSabsG2,
            273 => RelocType::LdPrelLo19,
            274 => RelocType::AdrPrelLo21,
            275 => RelocType::AdrPrelPgHi21,
            276 => RelocType::AdrPrelPgHi21Nc,
            277 => RelocType::AddAbsLo12Nc,
            278 => RelocType::Ldst8AbsLo12Nc,
            279 => RelocType::Tstbr14,
            280 => RelocType::Condbr19,
            282 => RelocType::Jump26,
            283 => RelocType::Call26,
            284 => RelocType::Ldst16AbsLo12Nc,
            285 => RelocType::Ldst32AbsLo12Nc,
            286 => RelocType::Ldst64AbsLo12Nc,
            287 => RelocType::MovwPrelG0,
            288 => RelocType::MovwPrelG0Nc,
            289 => RelocType::MovwPrelG1,
            290 => RelocType::MovwPrelG1Nc,
            291 => RelocType::MovwPrelG2,
            292 => RelocType::MovwPrelG2Nc,
            293 => RelocType::MovwPrelG3,
            299 => RelocType::Ldst128AbsLo12Nc,
            311 => RelocType::AdrGotPage,
            312 => RelocType::Ld64GotLo12Nc,
            313 => RelocType::Ld64GotpageLo15,
            314 => RelocType::Plt32,
            512 => RelocType::TlsgdAdrPrel21,
            513 => RelocType::TlsgdAdrPage21,
            514 => RelocType::TlsgdAddLo12Nc,
            517 => RelocType::TlsldAdrPrel21,
            518 => RelocType::TlsldAdrPage21,
            519 => RelocType::TlsldAddLo12Nc,
            523 => RelocType::TlsldAddDtprelHi12,
            524 => RelocType::TlsldAddDtprelLo12,
            525 => RelocType::TlsldAddDtprelLo12Nc,
            539 => RelocType::TlsieMovwGottprelG1,
            540 => RelocType::TlsieMovwGottprelG0Nc,
            541 => RelocType::TlsieAdrGottprelPage21,
            542 => RelocType::TlsieLd64GottprelLo12Nc,
            543 => RelocType::TlsieLdGottprelPrel19,
            544 => RelocType::TlsleMovwTprelG2,
            545 => RelocType::TlsleMovwTprelG1,
            546 => RelocType::TlsleMovwTprelG1Nc,
            547 => RelocType::TlsleMovwTprelG0,
            548 => RelocType::TlsleMovwTprelG0Nc,
            549 => RelocType::TlsleAddTprelHi12,
            550 => RelocType::TlsleAddTprelLo12,
            551 => RelocType::TlsleAddTprelLo12Nc,
            553 => RelocType::TlsleLdst8TprelLo12Nc,
            555 => RelocType::TlsleLdst16TprelLo12Nc,
            557 => RelocType::TlsleLdst32TprelLo12Nc,
            559 => RelocType::TlsleLdst64TprelLo12Nc,
            560 => RelocType::TlsdescLdPrel19,
            561 => RelocType::TlsdescAdrPrel21,
            562 => RelocType::TlsdescAdrPage21,
            563 => RelocType::TlsdescLd64Lo12,
            564 => RelocType::TlsdescAddLo12,
            569 => RelocType::TlsdescCall,
            571 => RelocType::TlsleLdst128TprelLo12Nc,
            1024 => RelocType::Copy,
            1025 => RelocType::GlobDat,
            1026 => RelocType::JumpSlot,
            1027 => RelocType::Relative,
            1028 => RelocType::TlsDtpmod,
            1029 => RelocType::TlsDtprel,
            1030 => RelocType::TlsTprel,
            1031 => RelocType::Tlsdesc,
            1032 => RelocType::Irelative,
            n => RelocType::Other(n),
        }
    }

    /// Lean-style constructor name (`.call26`, `(.other n)`), used in diagnostics and extern
    /// use classification.
    pub fn lean_ctor(self) -> String {
        match self {
            RelocType::None => ".none".into(),
            RelocType::Abs64 => ".abs64".into(),
            RelocType::Abs32 => ".abs32".into(),
            RelocType::Abs16 => ".abs16".into(),
            RelocType::Prel64 => ".prel64".into(),
            RelocType::Prel32 => ".prel32".into(),
            RelocType::Prel16 => ".prel16".into(),
            RelocType::MovwUabsG0 => ".movwUabsG0".into(),
            RelocType::MovwUabsG0Nc => ".movwUabsG0Nc".into(),
            RelocType::MovwUabsG1 => ".movwUabsG1".into(),
            RelocType::MovwUabsG1Nc => ".movwUabsG1Nc".into(),
            RelocType::MovwUabsG2 => ".movwUabsG2".into(),
            RelocType::MovwUabsG2Nc => ".movwUabsG2Nc".into(),
            RelocType::MovwUabsG3 => ".movwUabsG3".into(),
            RelocType::MovwSabsG0 => ".movwSabsG0".into(),
            RelocType::MovwSabsG1 => ".movwSabsG1".into(),
            RelocType::MovwSabsG2 => ".movwSabsG2".into(),
            RelocType::Plt32 => ".plt32".into(),
            RelocType::LdPrelLo19 => ".ldPrelLo19".into(),
            RelocType::AdrPrelLo21 => ".adrPrelLo21".into(),
            RelocType::AdrPrelPgHi21 => ".adrPrelPgHi21".into(),
            RelocType::AdrPrelPgHi21Nc => ".adrPrelPgHi21Nc".into(),
            RelocType::AddAbsLo12Nc => ".addAbsLo12Nc".into(),
            RelocType::Ldst8AbsLo12Nc => ".ldst8AbsLo12Nc".into(),
            RelocType::Tstbr14 => ".tstbr14".into(),
            RelocType::Condbr19 => ".condbr19".into(),
            RelocType::Jump26 => ".jump26".into(),
            RelocType::Call26 => ".call26".into(),
            RelocType::Ldst16AbsLo12Nc => ".ldst16AbsLo12Nc".into(),
            RelocType::Ldst32AbsLo12Nc => ".ldst32AbsLo12Nc".into(),
            RelocType::Ldst64AbsLo12Nc => ".ldst64AbsLo12Nc".into(),
            RelocType::MovwPrelG0 => ".movwPrelG0".into(),
            RelocType::MovwPrelG0Nc => ".movwPrelG0Nc".into(),
            RelocType::MovwPrelG1 => ".movwPrelG1".into(),
            RelocType::MovwPrelG1Nc => ".movwPrelG1Nc".into(),
            RelocType::MovwPrelG2 => ".movwPrelG2".into(),
            RelocType::MovwPrelG2Nc => ".movwPrelG2Nc".into(),
            RelocType::MovwPrelG3 => ".movwPrelG3".into(),
            RelocType::Ldst128AbsLo12Nc => ".ldst128AbsLo12Nc".into(),
            RelocType::AdrGotPage => ".adrGotPage".into(),
            RelocType::Ld64GotLo12Nc => ".ld64GotLo12Nc".into(),
            RelocType::Ld64GotpageLo15 => ".ld64GotpageLo15".into(),
            RelocType::TlsgdAdrPrel21 => ".tlsgdAdrPrel21".into(),
            RelocType::TlsgdAdrPage21 => ".tlsgdAdrPage21".into(),
            RelocType::TlsgdAddLo12Nc => ".tlsgdAddLo12Nc".into(),
            RelocType::TlsldAdrPrel21 => ".tlsldAdrPrel21".into(),
            RelocType::TlsldAdrPage21 => ".tlsldAdrPage21".into(),
            RelocType::TlsldAddLo12Nc => ".tlsldAddLo12Nc".into(),
            RelocType::TlsldAddDtprelHi12 => ".tlsldAddDtprelHi12".into(),
            RelocType::TlsldAddDtprelLo12 => ".tlsldAddDtprelLo12".into(),
            RelocType::TlsldAddDtprelLo12Nc => ".tlsldAddDtprelLo12Nc".into(),
            RelocType::TlsieMovwGottprelG1 => ".tlsieMovwGottprelG1".into(),
            RelocType::TlsieMovwGottprelG0Nc => ".tlsieMovwGottprelG0Nc".into(),
            RelocType::TlsieAdrGottprelPage21 => ".tlsieAdrGottprelPage21".into(),
            RelocType::TlsieLd64GottprelLo12Nc => ".tlsieLd64GottprelLo12Nc".into(),
            RelocType::TlsieLdGottprelPrel19 => ".tlsieLdGottprelPrel19".into(),
            RelocType::TlsleMovwTprelG2 => ".tlsleMovwTprelG2".into(),
            RelocType::TlsleMovwTprelG1 => ".tlsleMovwTprelG1".into(),
            RelocType::TlsleMovwTprelG1Nc => ".tlsleMovwTprelG1Nc".into(),
            RelocType::TlsleMovwTprelG0 => ".tlsleMovwTprelG0".into(),
            RelocType::TlsleMovwTprelG0Nc => ".tlsleMovwTprelG0Nc".into(),
            RelocType::TlsleAddTprelHi12 => ".tlsleAddTprelHi12".into(),
            RelocType::TlsleAddTprelLo12 => ".tlsleAddTprelLo12".into(),
            RelocType::TlsleAddTprelLo12Nc => ".tlsleAddTprelLo12Nc".into(),
            RelocType::TlsleLdst8TprelLo12Nc => ".tlsleLdst8TprelLo12Nc".into(),
            RelocType::TlsleLdst16TprelLo12Nc => ".tlsleLdst16TprelLo12Nc".into(),
            RelocType::TlsleLdst32TprelLo12Nc => ".tlsleLdst32TprelLo12Nc".into(),
            RelocType::TlsleLdst64TprelLo12Nc => ".tlsleLdst64TprelLo12Nc".into(),
            RelocType::TlsleLdst128TprelLo12Nc => ".tlsleLdst128TprelLo12Nc".into(),
            RelocType::TlsdescLdPrel19 => ".tlsdescLdPrel19".into(),
            RelocType::TlsdescAdrPrel21 => ".tlsdescAdrPrel21".into(),
            RelocType::TlsdescAdrPage21 => ".tlsdescAdrPage21".into(),
            RelocType::TlsdescLd64Lo12 => ".tlsdescLd64Lo12".into(),
            RelocType::TlsdescAddLo12 => ".tlsdescAddLo12".into(),
            RelocType::TlsdescCall => ".tlsdescCall".into(),
            RelocType::Copy => ".copy".into(),
            RelocType::GlobDat => ".globDat".into(),
            RelocType::JumpSlot => ".jumpSlot".into(),
            RelocType::Relative => ".relative".into(),
            RelocType::TlsDtpmod => ".tlsDtpmod".into(),
            RelocType::TlsDtprel => ".tlsDtprel".into(),
            RelocType::TlsTprel => ".tlsTprel".into(),
            RelocType::Tlsdesc => ".tlsdesc".into(),
            RelocType::Irelative => ".irelative".into(),
            RelocType::Other(n) => format!("(.other {n})"),
        }
    }

    pub fn is_branch(self) -> bool {
        matches!(self, RelocType::Call26 | RelocType::Jump26)
    }

    pub fn is_tlsie(self) -> bool {
        matches!(
            self,
            RelocType::TlsieMovwGottprelG1
                | RelocType::TlsieMovwGottprelG0Nc
                | RelocType::TlsieAdrGottprelPage21
                | RelocType::TlsieLd64GottprelLo12Nc
                | RelocType::TlsieLdGottprelPrel19
        )
    }

    pub fn is_tlsle(self) -> bool {
        matches!(
            self,
            RelocType::TlsleMovwTprelG2
                | RelocType::TlsleMovwTprelG1
                | RelocType::TlsleMovwTprelG1Nc
                | RelocType::TlsleMovwTprelG0
                | RelocType::TlsleMovwTprelG0Nc
                | RelocType::TlsleAddTprelHi12
                | RelocType::TlsleAddTprelLo12
                | RelocType::TlsleAddTprelLo12Nc
                | RelocType::TlsleLdst8TprelLo12Nc
                | RelocType::TlsleLdst16TprelLo12Nc
                | RelocType::TlsleLdst32TprelLo12Nc
                | RelocType::TlsleLdst64TprelLo12Nc
                | RelocType::TlsleLdst128TprelLo12Nc
        )
    }

    pub fn is_tls(self) -> bool {
        self.is_tlsie()
            || self.is_tlsle()
            || matches!(
                self,
                RelocType::TlsgdAdrPrel21
                    | RelocType::TlsgdAdrPage21
                    | RelocType::TlsgdAddLo12Nc
                    | RelocType::TlsldAdrPrel21
                    | RelocType::TlsldAdrPage21
                    | RelocType::TlsldAddLo12Nc
                    | RelocType::TlsldAddDtprelHi12
                    | RelocType::TlsldAddDtprelLo12
                    | RelocType::TlsldAddDtprelLo12Nc
                    | RelocType::TlsdescLdPrel19
                    | RelocType::TlsdescAdrPrel21
                    | RelocType::TlsdescAdrPage21
                    | RelocType::TlsdescLd64Lo12
                    | RelocType::TlsdescAddLo12
                    | RelocType::TlsdescCall
                    | RelocType::TlsDtpmod
                    | RelocType::TlsDtprel
                    | RelocType::TlsTprel
                    | RelocType::Tlsdesc
            )
    }

    /// Loads/stores through `:lo12:` of the symbol (data accesses).
    pub fn is_ldst(self) -> bool {
        matches!(
            self,
            RelocType::Ldst8AbsLo12Nc
                | RelocType::Ldst16AbsLo12Nc
                | RelocType::Ldst32AbsLo12Nc
                | RelocType::Ldst64AbsLo12Nc
                | RelocType::Ldst128AbsLo12Nc
        )
    }

    /// Byte width accessed by a load/store or data relocation against a symbol (`0` for
    /// branch/page/add relocations).
    pub fn access_size(self) -> u64 {
        match self {
            RelocType::Ldst8AbsLo12Nc => 1,
            RelocType::Ldst16AbsLo12Nc => 2,
            RelocType::Ldst32AbsLo12Nc | RelocType::Prel32 => 4,
            RelocType::Ldst64AbsLo12Nc
            | RelocType::Abs64
            | RelocType::Ld64GotLo12Nc
            | RelocType::TlsieLd64GottprelLo12Nc => 8,
            RelocType::Ldst128AbsLo12Nc => 16,
            _ => 0,
        }
    }
}

/// `Arm64.Obj.RelocKind`: AArch64 ELF static relocation classes supported by layout-generic objects.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RelocKind {
    Call26,
    Jump26,
    AdrpHi21,
    AdrpHi21Nc,
    AddLo12,
    Ldst8Lo12,
    Ldst16Lo12,
    Ldst32Lo12,
    Ldst64Lo12,
    Ldst128Lo12,
    Condbr19,
    Tstbr14,
    LdPrelLo19,
    AdrPrelLo21,
    Prel32,
    Abs64,
    Abs32,
    AdrGotPage,
    Ld64GotLo12Nc,
    TlsieAdrGottprelPage21,
    TlsieLd64GottprelLo12Nc,
    TlsdescAdrPage21,
    TlsdescLd64Lo12,
    TlsdescAddLo12,
    TlsdescCall,
    TlsleAddTprelHi12,
    TlsleAddTprelLo12,
    TlsleAddTprelLo12Nc,
    TlsleLdst8TprelLo12Nc,
    TlsleLdst16TprelLo12Nc,
    TlsleLdst32TprelLo12Nc,
    TlsleLdst64TprelLo12Nc,
    TlsleLdst128TprelLo12Nc,
    TlsleMovwTprelG1,
    TlsleMovwTprelG1Nc,
    TlsleMovwTprelG0,
    TlsleMovwTprelG0Nc,
}

impl RelocKind {
    pub fn from_reloc_type(t: RelocType) -> Option<Self> {
        match t {
            RelocType::Call26 => Some(Self::Call26),
            RelocType::Jump26 => Some(Self::Jump26),
            RelocType::AdrPrelPgHi21 => Some(Self::AdrpHi21),
            RelocType::AdrPrelPgHi21Nc => Some(Self::AdrpHi21Nc),
            RelocType::AddAbsLo12Nc => Some(Self::AddLo12),
            RelocType::Ldst8AbsLo12Nc => Some(Self::Ldst8Lo12),
            RelocType::Ldst16AbsLo12Nc => Some(Self::Ldst16Lo12),
            RelocType::Ldst32AbsLo12Nc => Some(Self::Ldst32Lo12),
            RelocType::Ldst64AbsLo12Nc => Some(Self::Ldst64Lo12),
            RelocType::Ldst128AbsLo12Nc => Some(Self::Ldst128Lo12),
            RelocType::Condbr19 => Some(Self::Condbr19),
            RelocType::Tstbr14 => Some(Self::Tstbr14),
            RelocType::LdPrelLo19 => Some(Self::LdPrelLo19),
            RelocType::AdrPrelLo21 => Some(Self::AdrPrelLo21),
            RelocType::Prel32 | RelocType::Plt32 => Some(Self::Prel32),
            RelocType::Abs64 => Some(Self::Abs64),
            RelocType::Abs32 => Some(Self::Abs32),
            RelocType::AdrGotPage => Some(Self::AdrGotPage),
            RelocType::Ld64GotLo12Nc => Some(Self::Ld64GotLo12Nc),
            RelocType::TlsieAdrGottprelPage21 => Some(Self::TlsieAdrGottprelPage21),
            RelocType::TlsieLd64GottprelLo12Nc => Some(Self::TlsieLd64GottprelLo12Nc),
            RelocType::TlsdescAdrPage21 => Some(Self::TlsdescAdrPage21),
            RelocType::TlsdescLd64Lo12 => Some(Self::TlsdescLd64Lo12),
            RelocType::TlsdescAddLo12 => Some(Self::TlsdescAddLo12),
            RelocType::TlsdescCall => Some(Self::TlsdescCall),
            RelocType::TlsleAddTprelHi12 => Some(Self::TlsleAddTprelHi12),
            RelocType::TlsleAddTprelLo12 => Some(Self::TlsleAddTprelLo12),
            RelocType::TlsleAddTprelLo12Nc => Some(Self::TlsleAddTprelLo12Nc),
            RelocType::TlsleLdst8TprelLo12Nc => Some(Self::TlsleLdst8TprelLo12Nc),
            RelocType::TlsleLdst16TprelLo12Nc => Some(Self::TlsleLdst16TprelLo12Nc),
            RelocType::TlsleLdst32TprelLo12Nc => Some(Self::TlsleLdst32TprelLo12Nc),
            RelocType::TlsleLdst64TprelLo12Nc => Some(Self::TlsleLdst64TprelLo12Nc),
            RelocType::TlsleLdst128TprelLo12Nc => Some(Self::TlsleLdst128TprelLo12Nc),
            RelocType::TlsleMovwTprelG1 => Some(Self::TlsleMovwTprelG1),
            RelocType::TlsleMovwTprelG1Nc => Some(Self::TlsleMovwTprelG1Nc),
            RelocType::TlsleMovwTprelG0 => Some(Self::TlsleMovwTprelG0),
            RelocType::TlsleMovwTprelG0Nc => Some(Self::TlsleMovwTprelG0Nc),
            _ => None,
        }
    }

    pub fn lean_name(self) -> &'static str {
        match self {
            Self::Call26 => ".call26",
            Self::Jump26 => ".jump26",
            Self::AdrpHi21 => ".adrpHi21",
            Self::AdrpHi21Nc => ".adrpHi21Nc",
            Self::AddLo12 => ".addLo12",
            Self::Ldst8Lo12 => ".ldst8Lo12",
            Self::Ldst16Lo12 => ".ldst16Lo12",
            Self::Ldst32Lo12 => ".ldst32Lo12",
            Self::Ldst64Lo12 => ".ldst64Lo12",
            Self::Ldst128Lo12 => ".ldst128Lo12",
            Self::Condbr19 => ".condbr19",
            Self::Tstbr14 => ".tstbr14",
            Self::LdPrelLo19 => ".ldPrelLo19",
            Self::AdrPrelLo21 => ".adrPrelLo21",
            Self::Prel32 => ".prel32",
            Self::Abs64 => ".abs64",
            Self::Abs32 => ".abs32",
            Self::AdrGotPage => ".adrGotPage",
            Self::Ld64GotLo12Nc => ".ld64GotLo12Nc",
            Self::TlsieAdrGottprelPage21 => ".tlsieAdrGottprelPage21",
            Self::TlsieLd64GottprelLo12Nc => ".tlsieLd64GottprelLo12Nc",
            Self::TlsdescAdrPage21 => ".tlsdescAdrPage21",
            Self::TlsdescLd64Lo12 => ".tlsdescLd64Lo12",
            Self::TlsdescAddLo12 => ".tlsdescAddLo12",
            Self::TlsdescCall => ".tlsdescCall",
            Self::TlsleAddTprelHi12 => ".tlsleAddTprelHi12",
            Self::TlsleAddTprelLo12 => ".tlsleAddTprelLo12",
            Self::TlsleAddTprelLo12Nc => ".tlsleAddTprelLo12Nc",
            Self::TlsleLdst8TprelLo12Nc => ".tlsleLdst8TprelLo12Nc",
            Self::TlsleLdst16TprelLo12Nc => ".tlsleLdst16TprelLo12Nc",
            Self::TlsleLdst32TprelLo12Nc => ".tlsleLdst32TprelLo12Nc",
            Self::TlsleLdst64TprelLo12Nc => ".tlsleLdst64TprelLo12Nc",
            Self::TlsleLdst128TprelLo12Nc => ".tlsleLdst128TprelLo12Nc",
            Self::TlsleMovwTprelG1 => ".tlsleMovwTprelG1",
            Self::TlsleMovwTprelG1Nc => ".tlsleMovwTprelG1Nc",
            Self::TlsleMovwTprelG0 => ".tlsleMovwTprelG0",
            Self::TlsleMovwTprelG0Nc => ".tlsleMovwTprelG0Nc",
        }
    }

    /// Whether `self` is a GOT or initial-exec TLS (`TLSIE`) relocation kind.
    pub fn is_got_or_tls_ie(self) -> bool {
        matches!(
            self,
            Self::AdrGotPage
                | Self::Ld64GotLo12Nc
                | Self::TlsieAdrGottprelPage21
                | Self::TlsieLd64GottprelLo12Nc
        )
    }
}

/// One relocation entry of a section.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ObjReloc {
    pub offset: u64,
    pub rtype: RelocType,
    pub sym: usize,
    pub addend: i64,
}

/// An `SHT_GROUP` section entry (e.g. `GRP_COMDAT`): the signature is the `.strtab` name of the
/// group's `sh_info` symbol, and `sections` are the indices (into `ObjObject::sections`) of its
/// extracted members.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ComdatGroup {
    pub signature: String,
    pub is_comdat: bool,
    pub sections: Vec<usize>,
}

/// An extracted ELF section with its 1-to-1 header attributes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ObjSection {
    pub name: String,
    pub sh_type: u32,
    pub sh_flags: u64,
    pub addr: u64,
    pub align: u64,
    pub entsize: u64,
    pub size: u64,
    /// Byte range `[file_offset, file_offset + size)` of the section's contents in the `.o`
    /// (unused for `SHT_NOBITS` sections).
    pub file_offset: u64,
    /// Section contents (empty for `SHT_NOBITS` sections).
    pub bytes: Vec<u8>,
    pub relocs: Vec<ObjReloc>,
    /// True if `relocs` came from an `SHT_REL` table (implicit addends) instead of `SHT_RELA`.
    pub is_rel: bool,
    /// ELF section header index (provenance only).
    pub elf_index: usize,
}

impl ObjSection {
    /// Whether this section has `SHT_NOBITS`.
    pub fn is_nobits(&self) -> bool {
        self.sh_type == object::elf::SHT_NOBITS
    }

    /// This section's [`SecKind`] (see [`SecKind::classify`]).
    pub fn kind(&self) -> Option<SecKind> {
        SecKind::classify(&self.name, self.sh_type, self.sh_flags)
    }
}

/// The section a symbol is defined in (`st_shndx`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SymSection {
    Undef,
    Sec(usize),
    Abs,
    Common,
    Other,
}

/// ELF symbol type (`STT_*`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SymKind {
    Notype,
    Func,
    Object,
    Tls,
    Section,
    File,
    Common,
    GnuIfunc,
    Other(u8),
}

impl SymKind {
    /// Lean-style constructor name (`.func`, `(.other n)`), used in diagnostics and extern
    /// use classification.
    pub fn lean_ctor(self) -> String {
        match self {
            SymKind::Notype => ".notype".into(),
            SymKind::Func => ".func".into(),
            SymKind::Object => ".object".into(),
            SymKind::Tls => ".tls".into(),
            SymKind::Section => ".section".into(),
            SymKind::File => ".file".into(),
            SymKind::Common => ".common".into(),
            SymKind::GnuIfunc => ".gnuIfunc".into(),
            SymKind::Other(n) => format!("(.other {n})"),
        }
    }
}

/// ELF symbol binding (`STB_*`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SymBind {
    Local,
    Global,
    Weak,
    GnuUnique,
    Other(u8),
}

/// One symbol table entry, in ELF order (index 0 is the null symbol).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ObjSymbol {
    /// Demangled name (`{:#}`); for `STT_SECTION` symbols, the section's name.
    pub name: String,
    /// Raw (mangled) name from `.strtab`.
    pub raw_name: String,
    pub kind: SymKind,
    pub bind: SymBind,
    pub vis: u8,
    pub sec: SymSection,
    pub value: u64,
    pub size: u64,
}

/// One crate's relocatable object (output of `crate::trusted_extractor`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ObjObject {
    /// Crate name (`Object.name`).
    pub name: String,
    pub sections: Vec<ObjSection>,
    pub symbols: Vec<ObjSymbol>,
    pub groups: Vec<ComdatGroup>,
    /// Raw bytes of the `.o` file (provenance).
    pub elf_bytes: Vec<u8>,
}

/// Kind of an external (undefined) symbol, resolved against the dependency rlibs or config.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExternKind {
    Func,
    Object,
    Tls,
}

impl ExternKind {
    pub fn lean_ctor(self) -> &'static str {
        match self {
            ExternKind::Func => ".func",
            ExternKind::Object => ".object",
            ExternKind::Tls => ".tls",
        }
    }

    pub fn as_str(self) -> &'static str {
        match self {
            ExternKind::Func => "func",
            ExternKind::Object => "object",
            ExternKind::Tls => "tls",
        }
    }
}

/// An external symbol the linker must provide (stub, data object, or TLS slot), plus where
/// its kind/size came from.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExternDecl {
    pub name: String,
    pub raw_name: String,
    pub kind: ExternKind,
    pub size: u64,
    pub align: u64,
    /// Defining rlib member, or why none was needed (provenance only).
    pub origin: String,
}

/// Resolved explicit external symbol declaration from `[[externs]]`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConfiguredExtern {
    pub name: String,
    pub kind: ExternKind,
    pub size: Option<u64>,
    pub align: u64,
}

/// Everything the trusted extractor produces for one configuration.
#[derive(Clone, Debug)]
pub struct Extraction {
    pub objects: Vec<ObjObject>,
    pub externs: Vec<ExternDecl>,
    pub provenance: Vec<(String, String)>,
}

/// Naming and path metadata for generated Lean object modules (`<ObjName>PlacedObj.lean` and the
/// `[OUTSIDE TCB]` legacy `<ObjName>Obj.lean` proof-cache module with its `.code.bin`/`.data.bin`
/// sidecars).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ObjModuleMeta {
    pub obj_name: String,
    pub obj_file: PathBuf,
    pub namespace_prefix: String,
    pub title: String,
    pub license_header: Vec<String>,
}

impl ObjModuleMeta {
    /// `<obj_name>Obj` when `num_objects == 1`, or `<obj_name><Crate>Obj` when `num_objects > 1`.
    pub fn obj_def_name_for(&self, crate_name: &str, num_objects: usize) -> String {
        if num_objects == 1 {
            format!("{}Obj", self.obj_name)
        } else {
            format!("{}{}Obj", self.obj_name, upper_camel(crate_name))
        }
    }

    /// `<obj_name>Image : Obj.LinkedImage`, the linked image of all objects.
    pub fn image_def_name(&self) -> String {
        format!("{}Image", self.obj_name)
    }

    /// File next to `obj_file` holding the linked code bytes: `<ObjStem>.code.bin`.
    pub fn code_bin_file(&self) -> PathBuf {
        self.obj_sibling("code.bin")
    }

    /// File next to `obj_file` holding the linked data bytes: `<ObjStem>.data.bin`.
    pub fn data_bin_file(&self) -> PathBuf {
        self.obj_sibling("data.bin")
    }

    fn obj_sibling(&self, ext: &str) -> PathBuf {
        let stem = self
            .obj_file
            .file_stem()
            .unwrap_or_default()
            .to_string_lossy();
        self.obj_file.with_file_name(format!("{stem}.{ext}"))
    }
}

/// `foo_bar-baz` → `FooBarBaz`.
pub fn upper_camel(s: &str) -> String {
    s.split(['_', '-'])
        .map(|part| {
            let mut cs = part.chars();
            match cs.next() {
                Some(c) => c.to_uppercase().chain(cs).collect::<String>(),
                None => String::new(),
            }
        })
        .collect()
}

/// Escape `s` as the contents of a Lean string literal.
pub fn lean_string_lit(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            '\r' => out.push_str("\\r"),
            c if (c as u32) < 0x20 || c as u32 == 0x7f => {
                out.push_str(&format!("\\x{:02x}", c as u32))
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

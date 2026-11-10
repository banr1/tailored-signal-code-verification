// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Shared JSON schema between `run-trusted-tests` and `Arm64/Testing/Harness/TestCase.lean`
//! (`[TEST ONLY]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[TEST ONLY]` (serialization model for differential ISA testing between
//!   Lean's `diff_eval` executable, Unicorn, and the official Sail Armv9.4-A model).
//! - **Purpose:** Defines the JSON test-case inputs (initial registers, memory bytes, watched
//!   memory ranges, step limit, machine words or assembly text) and architectural post-states
//!   ([`OracleState`]) exchanged with `diff_eval`.
//!
//! # Key Types & Functions
//! - [`IsaTestCase`] (alias [`DiffTestCase`]): Single differential test case (`name`, `words`, `asm`, `skip_sail`)
//!   with [`DiffTestCase::to_test_input`] converting to [`isa_oracle::TestInput`].
//! - [`OracleState`] and [`WatchedMemVal`]: Display summary of an [`isa_oracle::Outcome`] for `--print-vectors`.
//! - [`OracleSelection`]: Selects which external oracle(s) (`all`, `unicorn`, `sail`) to run.
//! - [`parse_u64_str`], [`parse_u64_value`]: Hex (`0x...`) and decimal `u64` parsers.
//!
//! # When to Read This File
//! - Read this file when extending the JSON protocol between `Arm64/Testing/Harness/TestCase.lean` and
//!   `run-trusted-tests`; otherwise the header suffices.

use std::collections::BTreeSet;

use anyhow::{Context, Result, anyhow};
use clap::ValueEnum;
use isa_oracle::{CpuState, Outcome, TestInput};
use serde::{Deserialize, Serialize};

pub const DEFAULT_CODE_BASE: u64 = 0x10000;
pub const DEFAULT_DATA_BASE: u64 = 0x80000;
pub const DEFAULT_EXIT_PC: u64 = 0xdead0000;

/// Which reference ISA oracle(s) to run and compare against Lean's `diff_eval`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum)]
pub enum OracleSelection {
    /// Run both Unicorn (`UC_ARCH_ARM64`) and Sail Armv9.4-A (`rems-project/sail-arm`).
    All,
    /// Run only Unicorn (`UC_ARCH_ARM64`).
    Unicorn,
    /// Run only Sail Armv9.4-A (`rems-project/sail-arm`).
    Sail,
}

impl OracleSelection {
    pub fn includes_unicorn(self) -> bool {
        matches!(self, Self::All | Self::Unicorn)
    }

    pub fn includes_sail(self) -> bool {
        matches!(self, Self::All | Self::Sail)
    }

    pub fn as_cli_str(self) -> &'static str {
        match self {
            Self::All => "all",
            Self::Unicorn => "unicorn",
            Self::Sail => "sail",
        }
    }
}

/// Parse a `serde_json::Value` (or string/integer) as a `u64`, accepting `"0x..."` hex or decimal.
pub fn parse_u64_str(s: &str) -> Result<u64> {
    let s = s.trim();
    if let Some(hex) = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")) {
        u64::from_str_radix(hex, 16).with_context(|| format!("invalid hex integer `{s}`"))
    } else {
        s.parse::<u64>()
            .with_context(|| format!("invalid decimal integer `{s}`"))
    }
}

pub fn parse_u64_value(v: &serde_json::Value) -> Result<u64> {
    if let Some(n) = v.as_u64() {
        Ok(n)
    } else if let Some(s) = v.as_str() {
        parse_u64_str(s)
    } else {
        Err(anyhow!("expected integer or hex string, got {v}"))
    }
}

/// Parse a `serde_json::Value` (or string/integer) as a `u128`, accepting `"0x..."` hex or decimal.
pub fn parse_u128_str(s: &str) -> Result<u128> {
    let s = s.trim();
    if let Some(hex) = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")) {
        u128::from_str_radix(hex, 16).with_context(|| format!("invalid 128-bit hex integer `{s}`"))
    } else {
        s.parse::<u128>()
            .with_context(|| format!("invalid 128-bit decimal integer `{s}`"))
    }
}

pub fn parse_u128_value(v: &serde_json::Value) -> Result<u128> {
    if let Some(n) = v.as_u64() {
        Ok(n as u128)
    } else if let Some(s) = v.as_str() {
        parse_u128_str(s)
    } else {
        Err(anyhow!("expected 128-bit integer or hex string, got {v}"))
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct WatchedMemVal {
    pub addr: String,
    pub size: usize,
    pub val: String,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct OracleState {
    pub regs: Vec<String>,
    #[serde(default)]
    pub vregs: Vec<String>,
    pub sp: String,
    pub pc: String,
    pub nzcv: u8,
    pub mem_out: Vec<WatchedMemVal>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
}

impl OracleState {
    /// Convert a typed [`Outcome`] into a displayable [`OracleState`] for `--print-vectors`.
    pub fn from_outcome(outcome: &Outcome) -> Self {
        match outcome {
            Outcome::Ok { state, mem, .. } => {
                let mem_out = mem
                    .iter()
                    .map(|(addr, bytes)| {
                        let mut buf = [0u8; 8];
                        let len = bytes.len().min(8);
                        buf[..len].copy_from_slice(&bytes[..len]);
                        let val = u64::from_le_bytes(buf);
                        WatchedMemVal {
                            addr: format!("0x{addr:016x}"),
                            size: bytes.len(),
                            val: format!("0x{val:016x}"),
                        }
                    })
                    .collect();
                Self {
                    regs: state.gprs.iter().map(|v| format!("0x{v:016x}")).collect(),
                    vregs: state.vregs.iter().map(|v| format!("0x{v:032x}")).collect(),
                    sp: format!("0x{:016x}", state.sp),
                    pc: format!("0x{:016x}", state.pc),
                    nzcv: state.nzcv & 0xF,
                    mem_out,
                    error: None,
                }
            }
            other => Self {
                regs: Vec::new(),
                vregs: Vec::new(),
                sp: String::new(),
                pc: String::new(),
                nzcv: 0,
                mem_out: Vec::new(),
                error: Some(other.summary()),
            },
        }
    }
}

/// Canonical ISA differential test case (mirrors `Testing.Harness.IsaTestCase` in `Arm64/Testing/Harness/TestCase.lean`).
pub type IsaTestCase = DiffTestCase;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DiffTestCase {
    pub name: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub asm: Option<String>,
    #[serde(default = "default_base_pc")]
    pub base_pc: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub start_pc: Option<String>,
    #[serde(default = "default_exit_pc")]
    pub exit_pc: String,
    #[serde(default = "default_max_steps")]
    pub max_steps: usize,
    #[serde(default)]
    pub words: Vec<String>,
    #[serde(default)]
    pub regs: Vec<serde_json::Value>,
    #[serde(default)]
    pub vregs: Vec<serde_json::Value>,
    #[serde(default = "default_sp")]
    pub sp: String,
    #[serde(default)]
    pub nzcv: u8,
    #[serde(default)]
    pub mem_init: Vec<serde_json::Value>,
    #[serde(default)]
    pub mem_watch: Vec<serde_json::Value>,
    /// If set, Sail is not run for this case; the string documents why (Unicorn is still required).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub skip_sail: Option<String>,
}

fn default_base_pc() -> String {
    format!("0x{DEFAULT_CODE_BASE:016x}")
}

fn default_exit_pc() -> String {
    format!("0x{DEFAULT_EXIT_PC:016x}")
}

fn default_sp() -> String {
    format!("0x{:016x}", DEFAULT_DATA_BASE + 0x8000)
}

fn default_max_steps() -> usize {
    500
}

impl DiffTestCase {
    pub fn base_pc_u64(&self) -> Result<u64> {
        parse_u64_str(&self.base_pc)
    }

    pub fn start_pc_u64(&self) -> Result<u64> {
        match &self.start_pc {
            Some(s) => parse_u64_str(s),
            None => self.base_pc_u64(),
        }
    }

    pub fn exit_pc_u64(&self) -> Result<u64> {
        parse_u64_str(&self.exit_pc)
    }

    pub fn sp_u64(&self) -> Result<u64> {
        parse_u64_str(&self.sp)
    }

    pub fn words_u32(&self) -> Result<Vec<u32>> {
        self.words
            .iter()
            .map(|w| Ok(parse_u64_str(w)? as u32))
            .collect()
    }

    pub fn initial_regs_u64(&self) -> Result<[u64; 31]> {
        let mut out = [0u64; 31];
        for (i, entry) in self.regs.iter().enumerate() {
            if let Some(arr) = entry.as_array() {
                if arr.len() >= 2 {
                    let idx = parse_u64_value(&arr[0])? as usize;
                    let val = parse_u64_value(&arr[1])?;
                    if idx < 31 {
                        out[idx] = val;
                    }
                }
            } else if i < 31 {
                out[i] = parse_u64_value(entry)?;
            }
        }
        Ok(out)
    }

    pub fn initial_vregs_u128(&self) -> Result<[u128; 32]> {
        let mut out = [0u128; 32];
        for (i, entry) in self.vregs.iter().enumerate() {
            if let Some(arr) = entry.as_array() {
                if arr.len() >= 2 {
                    let idx = parse_u64_value(&arr[0])? as usize;
                    let val = parse_u128_value(&arr[1])?;
                    if idx < 32 {
                        out[idx] = val;
                    }
                }
            } else if i < 32 {
                out[i] = parse_u128_value(entry)?;
            }
        }
        Ok(out)
    }

    pub fn initial_mem_writes(&self) -> Result<Vec<(u64, u64, usize)>> {
        let mut out = Vec::with_capacity(self.mem_init.len());
        for item in &self.mem_init {
            if let Some(arr) = item.as_array() {
                if arr.len() >= 3 {
                    let addr = parse_u64_value(&arr[0])?;
                    let val = parse_u64_value(&arr[1])?;
                    let sz = parse_u64_value(&arr[2])? as usize;
                    out.push((addr, val, sz));
                }
            } else if let Some(obj) = item.as_object() {
                let addr =
                    parse_u64_value(obj.get("addr").ok_or_else(|| anyhow!("missing addr"))?)?;
                let val = parse_u64_value(obj.get("val").ok_or_else(|| anyhow!("missing val"))?)?;
                let sz = obj
                    .get("size")
                    .map(parse_u64_value)
                    .transpose()?
                    .unwrap_or(8) as usize;
                out.push((addr, val, sz));
            }
        }
        Ok(out)
    }

    pub fn watched_mem_ranges(&self) -> Result<Vec<(u64, usize)>> {
        let mut out = Vec::with_capacity(self.mem_watch.len());
        for item in &self.mem_watch {
            if let Some(arr) = item.as_array() {
                if arr.len() >= 2 {
                    let addr = parse_u64_value(&arr[0])?;
                    let sz = parse_u64_value(&arr[1])? as usize;
                    out.push((addr, sz));
                }
            } else {
                let addr = parse_u64_value(item)?;
                out.push((addr, 8));
            }
        }
        Ok(out)
    }

    /// Convert this [`DiffTestCase`] into a canonical [`TestInput`] consumed by all [`isa_oracle::Arm64Oracle`] backends.
    pub fn to_test_input(&self) -> Result<TestInput> {
        let base_pc = self.base_pc_u64()?;
        let start_pc = self.start_pc_u64()?;
        let exit_pc = self.exit_pc_u64()?;
        let init_sp = self.sp_u64()?;
        let words = self.words_u32()?;
        let gprs = self.initial_regs_u64()?;
        let vregs = self.initial_vregs_u128()?;
        let mem_writes = self.initial_mem_writes()?;
        let mem_watches = self.watched_mem_ranges()?;

        let mut chunks_to_map = BTreeSet::new();
        for chunk_idx in 0..16u64 {
            chunks_to_map.insert(chunk_idx * 0x10000);
        }
        chunks_to_map.insert(base_pc & !0xFFFF);
        chunks_to_map.insert((base_pc + (words.len() as u64) * 4) & !0xFFFF);
        chunks_to_map.insert(start_pc & !0xFFFF);
        chunks_to_map.insert(exit_pc & !0xFFFF);
        chunks_to_map.insert(init_sp & !0xFFFF);
        if init_sp >= 0x10000 {
            chunks_to_map.insert((init_sp - 0x10000) & !0xFFFF);
        }
        for &(addr, _, _) in &mem_writes {
            chunks_to_map.insert(addr & !0xFFFF);
        }
        for &(addr, _) in &mem_watches {
            chunks_to_map.insert(addr & !0xFFFF);
        }

        let mapped = chunks_to_map
            .into_iter()
            .map(|c| c..(c + 0x10000))
            .collect();
        let mem = mem_writes
            .into_iter()
            .map(|(addr, val, sz)| {
                let le = val.to_le_bytes();
                (addr, le[..sz.min(8)].to_vec())
            })
            .collect();
        let watch = mem_watches
            .into_iter()
            .map(|(addr, sz)| addr..(addr + (sz.min(8) as u64)))
            .collect();

        Ok(TestInput {
            state: CpuState {
                gprs,
                vregs,
                sp: init_sp,
                pc: start_pc,
                nzcv: self.nzcv & 0xF,
                fpcr: 0,
                fpsr: 0,
                tpidr_el0: 0,
            },
            code: vec![(base_pc, words)],
            mem,
            mapped,
            watch,
            exit_pc,
            max_steps: self.max_steps,
        })
    }
}

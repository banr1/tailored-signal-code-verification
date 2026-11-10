// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Thin typed AArch64 ISA oracle wrapper around `unicorn-engine` (`[TEST ONLY]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[TEST ONLY]` (wraps the Unicorn Engine `UC_ARCH_ARM64` / `UC_CPU_ARM64_MAX`
//!   QEMU-derived AArch64 CPU emulator behind [`isa_oracle::Arm64Oracle`]).
//! - **Purpose:** Provides [`UnicornOracle`], a stateful [`Arm64Oracle`] implementation that:
//!   - Initializes `UC_CPU_ARM64_MAX` with `CPACR_EL1.FPEN = 0b11` (FP/SIMD enabled at `EL0`).
//!   - Maps 4 KiB-aligned virtual memory intervals from [`TestInput::mapped`], reusing or zeroing
//!     already-mapped pages across consecutive runs.
//!   - Reads and writes typed [`CpuState`] (`X0..X30`, `V0..V31`, `SP`, `PC`, `NZCV`, `FPCR`,
//!     `FPSR`, `TPIDR_EL0`) and watched memory slices without hex-string serialization.
//!
//! # Key Types & Functions
//! - [`UC_X_REGS`], [`UC_V_REGS`]: Ordered tables of Unicorn `X0..X30` and `V0..V31` register IDs.
//! - [`UnicornOracle`]: Persistent Unicorn AArch64 instance implementing [`Arm64Oracle`].
//! - [`coalesce_pages`]: Rounds [`TestInput::mapped`] byte ranges out to sorted, non-overlapping
//!   4 KiB page intervals `(base, size)`.
//!
//! # When to Read This File
//! - Read this file when auditing or modifying how Unicorn maps pages, loads registers/memory,
//!   or classifies emulation faults into [`Outcome`].

use std::ops::Range;

pub use isa_oracle::{Arm64Oracle, CpuState, FaultKind, Outcome, TestInput, NO_EXIT_PC};
use unicorn_engine::unicorn_const::{Arch, Mode, Permission, uc_error};
use unicorn_engine::{RegisterARM64, Unicorn};

/// Unicorn page granularity (4 KiB).
pub const PAGE_SIZE: u64 = 0x1000;

/// C `uc_arm64_reg` ID for `FPCR` (`UC_ARM64_REG_CP_REG + 1` in `include/unicorn/arm64.h`).
const UC_ARM64_REG_FPCR: i32 = RegisterARM64::CP_REG as i32 + 1;

/// C `uc_arm64_reg` ID for `FPSR` (`UC_ARM64_REG_CP_REG + 2` in `include/unicorn/arm64.h`).
const UC_ARM64_REG_FPSR: i32 = RegisterARM64::CP_REG as i32 + 2;

/// Ordered table of Unicorn `X0..X30` general-purpose register identifiers.
pub const UC_X_REGS: [RegisterARM64; 31] = [
    RegisterARM64::X0,
    RegisterARM64::X1,
    RegisterARM64::X2,
    RegisterARM64::X3,
    RegisterARM64::X4,
    RegisterARM64::X5,
    RegisterARM64::X6,
    RegisterARM64::X7,
    RegisterARM64::X8,
    RegisterARM64::X9,
    RegisterARM64::X10,
    RegisterARM64::X11,
    RegisterARM64::X12,
    RegisterARM64::X13,
    RegisterARM64::X14,
    RegisterARM64::X15,
    RegisterARM64::X16,
    RegisterARM64::X17,
    RegisterARM64::X18,
    RegisterARM64::X19,
    RegisterARM64::X20,
    RegisterARM64::X21,
    RegisterARM64::X22,
    RegisterARM64::X23,
    RegisterARM64::X24,
    RegisterARM64::X25,
    RegisterARM64::X26,
    RegisterARM64::X27,
    RegisterARM64::X28,
    RegisterARM64::X29,
    RegisterARM64::X30,
];

/// Ordered table of Unicorn `V0..V31` 128-bit SIMD/FP register identifiers.
pub const UC_V_REGS: [RegisterARM64; 32] = [
    RegisterARM64::V0,
    RegisterARM64::V1,
    RegisterARM64::V2,
    RegisterARM64::V3,
    RegisterARM64::V4,
    RegisterARM64::V5,
    RegisterARM64::V6,
    RegisterARM64::V7,
    RegisterARM64::V8,
    RegisterARM64::V9,
    RegisterARM64::V10,
    RegisterARM64::V11,
    RegisterARM64::V12,
    RegisterARM64::V13,
    RegisterARM64::V14,
    RegisterARM64::V15,
    RegisterARM64::V16,
    RegisterARM64::V17,
    RegisterARM64::V18,
    RegisterARM64::V19,
    RegisterARM64::V20,
    RegisterARM64::V21,
    RegisterARM64::V22,
    RegisterARM64::V23,
    RegisterARM64::V24,
    RegisterARM64::V25,
    RegisterARM64::V26,
    RegisterARM64::V27,
    RegisterARM64::V28,
    RegisterARM64::V29,
    RegisterARM64::V30,
    RegisterARM64::V31,
];

/// Round arbitrary byte ranges out to 4 KiB page boundaries and coalesce overlapping or adjacent
/// intervals into sorted `(base, size)` pairs.
pub fn coalesce_pages(ranges: &[Range<u64>]) -> Vec<(u64, usize)> {
    let mut aligned: Vec<(u64, u64)> = ranges
        .iter()
        .filter(|r| r.start < r.end)
        .map(|r| {
            let start = r.start & !(PAGE_SIZE - 1);
            let end = r.end.saturating_add(PAGE_SIZE - 1) & !(PAGE_SIZE - 1);
            (start, end)
        })
        .collect();
    aligned.sort_unstable_by_key(|&(s, _)| s);

    let mut merged: Vec<(u64, u64)> = Vec::with_capacity(aligned.len());
    for (s, e) in aligned {
        if let Some(last) = merged.last_mut()
            && s <= last.1
        {
            last.1 = last.1.max(e);
            continue;
        }
        merged.push((s, e));
    }
    merged
        .into_iter()
        .filter_map(|(s, e)| {
            let sz = (e - s) as usize;
            (sz > 0).then_some((s, sz))
        })
        .collect()
}

/// Stateful [`Arm64Oracle`] backed by a reusable Unicorn `UC_ARCH_ARM64` (`UC_CPU_ARM64_MAX`) instance.
pub struct UnicornOracle {
    uc: Unicorn<'static, ()>,
    mapped_pages: Vec<(u64, usize)>,
    watch: Vec<Range<u64>>,
    zero_buf: Vec<u8>,
}

impl UnicornOracle {
    /// Create a new [`UnicornOracle`] configured with `UC_CPU_ARM64_MAX` and `EL0` FP/SIMD enabled.
    pub fn new() -> Result<Self, String> {
        let mut uc = Unicorn::new(Arch::ARM64, Mode::LITTLE_ENDIAN)
            .map_err(|e| format!("failed to initialize Unicorn ARM64: {e:?}"))?;
        // Select `max` CPU model so Armv8.1+ LSE atomics and RCpc (`LDAPR`) are enabled.
        uc.ctl_set_cpu_model(unicorn_engine::Arm64CpuModel::UC_CPU_ARM64_MAX as i32)
            .map_err(|e| format!("failed to select UC_CPU_ARM64_MAX: {e:?}"))?;
        // Enable FP/SIMD in CPACR_EL1 (FPEN = 0b11 at bits [21:20]).
        uc.reg_write(RegisterARM64::CPACR_EL1, 3u64 << 20)
            .map_err(|e| format!("failed to write CPACR_EL1: {e:?}"))?;
        Ok(Self {
            uc,
            mapped_pages: Vec::new(),
            watch: Vec::new(),
            zero_buf: vec![0u8; PAGE_SIZE as usize],
        })
    }

    /// Read the current [`CpuState`] from Unicorn registers.
    pub fn read_state(&self) -> Result<CpuState, String> {
        let mut gprs = [0u64; 31];
        for (i, &reg) in UC_X_REGS.iter().enumerate() {
            gprs[i] = self
                .uc
                .reg_read(reg)
                .map_err(|e| format!("reg_read(X{i}) failed: {e:?}"))?;
        }
        let mut vregs = [0u128; 32];
        for (i, &reg) in UC_V_REGS.iter().enumerate() {
            let raw = self
                .uc
                .reg_read_long(reg)
                .map_err(|e| format!("reg_read_long(V{i}) failed: {e:?}"))?;
            let mut buf = [0u8; 16];
            let copy_len = raw.len().min(16);
            buf[..copy_len].copy_from_slice(&raw[..copy_len]);
            vregs[i] = u128::from_le_bytes(buf);
        }
        let sp = self
            .uc
            .reg_read(RegisterARM64::SP)
            .map_err(|e| format!("reg_read(SP) failed: {e:?}"))?;
        let pc = self
            .uc
            .reg_read(RegisterARM64::PC)
            .map_err(|e| format!("reg_read(PC) failed: {e:?}"))?;
        let nzcv_raw = self
            .uc
            .reg_read(RegisterARM64::NZCV)
            .map_err(|e| format!("reg_read(NZCV) failed: {e:?}"))?;
        let fpcr = self
            .uc
            .reg_read(UC_ARM64_REG_FPCR)
            .map_err(|e| format!("reg_read(FPCR) failed: {e:?}"))?;
        let fpsr = self
            .uc
            .reg_read(UC_ARM64_REG_FPSR)
            .map_err(|e| format!("reg_read(FPSR) failed: {e:?}"))?;
        let tpidr_el0 = self
            .uc
            .reg_read(RegisterARM64::TPIDR_EL0)
            .map_err(|e| format!("reg_read(TPIDR_EL0) failed: {e:?}"))?;
        Ok(CpuState {
            gprs,
            vregs,
            sp,
            pc,
            nzcv: ((nzcv_raw >> 28) & 0xF) as u8,
            fpcr,
            fpsr,
            tpidr_el0,
        })
    }

    fn write_state(&mut self, state: &CpuState) -> Result<(), String> {
        self.uc
            .reg_write(RegisterARM64::CPACR_EL1, 3u64 << 20)
            .map_err(|e| format!("reg_write(CPACR_EL1) failed: {e:?}"))?;
        for (i, &val) in state.gprs.iter().enumerate() {
            self.uc
                .reg_write(UC_X_REGS[i], val)
                .map_err(|e| format!("reg_write(X{i}) failed: {e:?}"))?;
        }
        for (i, &val) in state.vregs.iter().enumerate() {
            self.uc
                .reg_write_long(UC_V_REGS[i], &val.to_le_bytes())
                .map_err(|e| format!("reg_write_long(V{i}) failed: {e:?}"))?;
        }
        self.uc
            .reg_write(RegisterARM64::SP, state.sp)
            .map_err(|e| format!("reg_write(SP) failed: {e:?}"))?;
        self.uc
            .reg_write(RegisterARM64::PC, state.pc)
            .map_err(|e| format!("reg_write(PC) failed: {e:?}"))?;
        self.uc
            .reg_write(RegisterARM64::NZCV, ((state.nzcv as u64) & 0xF) << 28)
            .map_err(|e| format!("reg_write(NZCV) failed: {e:?}"))?;
        self.uc
            .reg_write(UC_ARM64_REG_FPCR, state.fpcr)
            .map_err(|e| format!("reg_write(FPCR) failed: {e:?}"))?;
        self.uc
            .reg_write(UC_ARM64_REG_FPSR, state.fpsr)
            .map_err(|e| format!("reg_write(FPSR) failed: {e:?}"))?;
        self.uc
            .reg_write(RegisterARM64::TPIDR_EL0, state.tpidr_el0)
            .map_err(|e| format!("reg_write(TPIDR_EL0) failed: {e:?}"))?;
        Ok(())
    }

    fn sync_mapped_pages(&mut self, desired: &[(u64, usize)]) -> Result<(), String> {
        if self.mapped_pages == desired {
            for &(base, size) in &self.mapped_pages {
                if self.zero_buf.len() < size {
                    self.zero_buf.resize(size, 0);
                }
                self.uc
                    .mem_write(base, &self.zero_buf[..size])
                    .map_err(|e| format!("mem_write(zero {base:#x}..+{size:#x}) failed: {e:?}"))?;
            }
            return Ok(());
        }
        for &(base, size) in &self.mapped_pages {
            self.uc
                .mem_unmap(base, size)
                .map_err(|e| format!("mem_unmap({base:#x}, {size:#x}) failed: {e:?}"))?;
        }
        self.mapped_pages.clear();
        for &(base, size) in desired {
            self.uc
                .mem_map(base, size, Permission::ALL)
                .map_err(|e| format!("mem_map({base:#x}, {size:#x}) failed: {e:?}"))?;
            self.mapped_pages.push((base, size));
        }
        Ok(())
    }

    fn read_watched(&self) -> Result<Vec<(u64, Vec<u8>)>, String> {
        let mut out = Vec::with_capacity(self.watch.len());
        for r in &self.watch {
            let len = r.end.saturating_sub(r.start) as usize;
            let bytes = if len == 0 {
                Vec::new()
            } else {
                self.uc
                    .mem_read_as_vec(r.start, len)
                    .map_err(|e| format!("mem_read({:#x}, {len}) failed: {e:?}", r.start))?
            };
            out.push((r.start, bytes));
        }
        Ok(out)
    }

    fn classify_uc_error(&self, err: uc_error, fallback_pc: u64) -> Outcome {
        let pc = self.uc.reg_read(RegisterARM64::PC).unwrap_or(fallback_pc);
        let kind = match err {
            uc_error::READ_UNMAPPED
            | uc_error::WRITE_UNMAPPED
            | uc_error::FETCH_UNMAPPED
            | uc_error::READ_PROT
            | uc_error::WRITE_PROT
            | uc_error::FETCH_PROT => FaultKind::Unmapped,
            uc_error::READ_UNALIGNED | uc_error::WRITE_UNALIGNED | uc_error::FETCH_UNALIGNED => {
                FaultKind::Misaligned
            }
            uc_error::INSN_INVALID => FaultKind::Undefined,
            uc_error::EXCEPTION => {
                let word = self
                    .uc
                    .mem_read_as_vec(pc, 4)
                    .ok()
                    .and_then(|b| <[u8; 4]>::try_from(b.as_slice()).ok())
                    .map(u32::from_le_bytes)
                    .unwrap_or(0);
                if isa_oracle::is_svc_encoding(word) {
                    FaultKind::Svc
                } else {
                    FaultKind::Other
                }
            }
            _ => FaultKind::Other,
        };
        Outcome::Fault { pc, kind }
    }
}

impl Arm64Oracle for UnicornOracle {
    fn name(&self) -> &'static str {
        "Unicorn"
    }

    fn load(&mut self, input: &TestInput) -> Result<(), String> {
        let desired_pages = coalesce_pages(&input.mapped);
        self.sync_mapped_pages(&desired_pages)?;

        for (base_pc, words) in &input.code {
            if words.is_empty() {
                continue;
            }
            let mut code_bytes = Vec::with_capacity(words.len() * 4);
            for &w in words {
                code_bytes.extend_from_slice(&w.to_le_bytes());
            }
            let end_pc = base_pc.saturating_add(code_bytes.len() as u64);
            let _ = self.uc.ctl_remove_cache(*base_pc, end_pc);
            self.uc
                .mem_write(*base_pc, &code_bytes)
                .map_err(|e| format!("mem_write(code at {base_pc:#x}) failed: {e:?}"))?;
        }

        for (addr, bytes) in &input.mem {
            if bytes.is_empty() {
                continue;
            }
            self.uc
                .mem_write(*addr, bytes)
                .map_err(|e| format!("mem_write(data at {addr:#x}) failed: {e:?}"))?;
        }

        self.write_state(&input.state)?;
        self.watch = input.watch.clone();
        Ok(())
    }

    fn step(&mut self) -> Outcome {
        let pc = match self.uc.reg_read(RegisterARM64::PC) {
            Ok(v) => v,
            Err(e) => return Outcome::OracleError(format!("reg_read(PC) failed: {e:?}")),
        };
        // Check misaligned PC before stepping so it is reported consistently as `Fault`.
        if pc & 0x3 != 0 {
            return Outcome::Fault {
                pc,
                kind: FaultKind::Misaligned,
            };
        }
        let dummy_until = pc.wrapping_add(1);
        if let Err(err) = self.uc.emu_start(pc, dummy_until, 0, 1) {
            return self.classify_uc_error(err, pc);
        }
        let state = match self.read_state() {
            Ok(s) => s,
            Err(e) => return Outcome::OracleError(e),
        };
        let mem = match self.read_watched() {
            Ok(m) => m,
            Err(e) => return Outcome::OracleError(e),
        };
        Outcome::Ok {
            state,
            mem,
            steps: 1,
        }
    }

    fn run(&mut self, input: &TestInput) -> Outcome {
        if let Err(err) = self.load(input) {
            return Outcome::OracleError(err);
        }
        let start_pc = input.state.pc;
        if start_pc & 0x3 != 0 {
            return Outcome::Fault {
                pc: start_pc,
                kind: FaultKind::Misaligned,
            };
        }
        if input.max_steps == 0 {
            let state = match self.read_state() {
                Ok(s) => s,
                Err(e) => return Outcome::OracleError(e),
            };
            if state.pc == input.exit_pc {
                let mem = match self.read_watched() {
                    Ok(m) => m,
                    Err(e) => return Outcome::OracleError(e),
                };
                return Outcome::Ok {
                    state,
                    mem,
                    steps: 0,
                };
            }
            return Outcome::StepLimit { pc: state.pc };
        }
        let until_pc = if input.exit_pc == NO_EXIT_PC {
            start_pc.wrapping_add(1)
        } else {
            input.exit_pc
        };
        if let Err(err) = self.uc.emu_start(start_pc, until_pc, 0, input.max_steps) {
            return self.classify_uc_error(err, start_pc);
        }
        let state = match self.read_state() {
            Ok(s) => s,
            Err(e) => return Outcome::OracleError(e),
        };
        let mem = match self.read_watched() {
            Ok(m) => m,
            Err(e) => return Outcome::OracleError(e),
        };
        if input.exit_pc == NO_EXIT_PC || state.pc == input.exit_pc {
            Outcome::Ok {
                state,
                mem,
                steps: input.max_steps,
            }
        } else {
            Outcome::StepLimit { pc: state.pc }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const CODE_BASE: u64 = 0x0001_0000;
    const STACK_BASE: u64 = 0x0002_8000;

    #[test]
    fn test_coalesce_pages_merges_overlapping_and_adjacent() {
        let pages = coalesce_pages(&[
            0x0001_0000..0x0001_0004,
            0x0001_0500..0x0001_1200,
            0x0002_0000..0x0002_0040,
        ]);
        assert_eq!(pages, vec![(0x0001_0000, 0x2000), (0x0002_0000, 0x1000)]);
    }

    #[test]
    fn test_unicorn_oracle_nop_identity_roundtrip() {
        let mut init = CpuState::new(CODE_BASE, STACK_BASE);
        for i in 0..31 {
            init.set_x(i, 0x0101_0101_0101_0101u64.wrapping_mul((i as u64) + 1));
        }
        for i in 0..32 {
            let lo = 0xaaaa_0000_0000_0000u64 | (i as u64);
            let hi = 0xbbbb_0000_0000_0000u64 | ((i as u64) << 8);
            init.set_v(i, ((hi as u128) << 64) | (lo as u128));
        }
        init.nzcv = 0b1010;
        init.fpcr = 1 << 22; // RTN rounding mode
        init.fpsr = 0x10; // IXC flag
        init.tpidr_el0 = 0x0000_7fff_dead_beef;

        let mut input = TestInput::single_insn(init.clone(), isa_oracle::AARCH64_NOP_WORD);
        input.mem = vec![(
            0x0002_0000,
            vec![0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88],
        )];
        input.mapped.push(0x0002_0000..0x0002_1000);
        input.watch = vec![0x0002_0000..0x0002_0008];

        let mut oracle = UnicornOracle::new().expect("UnicornOracle::new succeeds");
        let out = oracle.run(&input);
        let mut expected = init;
        expected.pc = CODE_BASE + 4;
        assert_eq!(
            out,
            Outcome::Ok {
                state: expected,
                mem: vec![(
                    0x0002_0000,
                    vec![0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88]
                )],
                steps: 1,
            }
        );
    }

    #[test]
    fn test_unicorn_oracle_svc_and_unmapped_fault() {
        let mut oracle = UnicornOracle::new().expect("UnicornOracle::new succeeds");

        // SVC #0 should produce a Fault outcome.
        let init = CpuState::new(CODE_BASE, STACK_BASE);
        let svc_input = TestInput::single_insn(init.clone(), 0xd400_0001);
        let svc_out = oracle.run(&svc_input);
        assert!(
            matches!(svc_out, Outcome::Fault { .. }),
            "expected Fault on SVC #0, got {svc_out:?}"
        );

        // Unmapped load from 0x0009_0000 should produce Fault(Unmapped).
        let mut ldr_init = init;
        ldr_init.set_x(1, 0x0009_0000);
        let ldr_input = TestInput::single_insn(ldr_init, 0xf940_0020); // ldr x0, [x1]
        let ldr_out = oracle.run(&ldr_input);
        assert_eq!(
            ldr_out,
            Outcome::Fault {
                pc: CODE_BASE,
                kind: FaultKind::Unmapped,
            }
        );
    }
}

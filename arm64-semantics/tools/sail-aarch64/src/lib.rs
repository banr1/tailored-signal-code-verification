// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Safe Rust interface to the official Sail Armv9.4-A (`rems-project/sail-arm`) AArch64 ISA
//! simulator (`[TEST ONLY]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[TEST ONLY]` (wraps the authoritative ASL-derived Sail Armv9.4-A C model
//!   `armv9.c` for differential testing against Lean 4 `Arm64.Step` semantics).
//! - **Purpose:** Owns all C FFI (`csrc/sail_ffi.c`) and process-global state synchronization
//!   internally behind a safe, pointer-free Rust API:
//!   - [`CpuState`]: User-space (`EL0`) AArch64 architectural state (`X0..X30`, `V0..V31`, `SP`,
//!     `PC`, `NZCV`).
//!   - [`Simulator`]: RAII guard over the process-global Sail C model that initializes/resets
//!     `EL0` state, reads/writes physical memory, steps instructions (`step`, `step_until`,
//!     `run_to_exit`), and frees sparse physical memory pages on `Drop`.
//!   - [`run_batch`]: Parallel fork-based single-instruction batch evaluator.
//!   - [`StopReason`] and [`SailError`]: Structured execution outcomes and error reporting.
//!
//! # Key Types & Functions
//! - [`CpuState`]: Complete user-space AArch64 register and condition-flag state.
//! - [`Simulator`]: Exclusive handle to the initialized Sail Armv9.4-A simulator.
//! - [`StopReason`]: Indicates whether [`Simulator::step_until`] stopped at `exit_pc` or
//!   after `max_steps` instructions.
//! - [`SailError`]: Errors returned when the Sail model faults, traps out of `EL0`, exceeds a
//!   step budget, or receives malformed batch inputs.
//! - [`run_batch`]: Executes a packed slice of 16-word single-instruction records in Sail.
//!
//! # When to Read This File
//! - Read this file when auditing or calling the Rust API over the Sail Armv9.4-A simulator.
//! - For the underlying C global state wiring and `--wrap` hooks, see `csrc/sail_ffi.c` and
//!   `csrc/Makefile`.

use std::error::Error;
use std::fmt;
use std::ops::Range;
use std::sync::{Mutex, MutexGuard};

pub use isa_oracle::{Arm64Oracle, CpuState, FaultKind, Outcome, TestInput, NO_EXIT_PC};

static SAIL_LOCK: Mutex<()> = Mutex::new(());

unsafe extern "C" {
    fn sail_harness_reset(
        regs: *const u64,
        vregs_lo: *const u64,
        vregs_hi: *const u64,
        sp: u64,
        pc: u64,
        nzcv: u8,
    );
    fn sail_harness_clear_mem();
    fn sail_harness_write_bytes(addr: u64, buf: *const u8, len: usize);
    fn sail_harness_read_bytes(addr: u64, buf: *mut u8, len: usize);
    fn sail_harness_step_until(
        exit_pc: u64,
        max_steps: usize,
        out_steps: *mut usize,
        out_pc: *mut u64,
    ) -> i32;
    fn sail_harness_read_state(
        out_regs: *mut u64,
        out_vregs_lo: *mut u64,
        out_vregs_hi: *mut u64,
        out_sp: *mut u64,
        out_pc: *mut u64,
        out_nzcv: *mut u8,
    );
    fn sail_harness_read_fpsr() -> u64;
    fn sail_harness_set_fpsr(fpsr: u64);
    fn sail_harness_read_fpcr() -> u64;
    fn sail_harness_set_fpcr(fpcr: u64);
    fn sail_harness_read_tpidr_el0() -> u64;
    fn sail_harness_set_tpidr_el0(tpidr: u64);
}

/// Why a bounded execution run ([`Simulator::step_until`]) stopped.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StopReason {
    /// Execution reached `exit_pc` after `steps` instructions.
    ReachedExitPc { steps: usize },
    /// Execution completed all `max_steps` instructions without faulting (`pc != exit_pc`).
    StepLimitReached { steps: usize, pc: u64 },
}

/// Errors returned by the Sail Armv9.4-A simulator.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SailError {
    /// A Sail model assertion or pattern-match failure occurred after `steps` instructions.
    ModelFault { steps: usize, pc: u64 },
    /// An instruction trapped out of `EL0` (e.g. `SVC`, `BRK`, alignment fault, or undefined encoding).
    ExceptionTrap { steps: usize, pc: u64 },
    /// [`Simulator::run_to_exit`] did not reach `exit_pc` within `max_steps` instructions.
    StepLimitExceeded { max_steps: usize, last_pc: u64 },
    /// The process-global Sail simulator mutex was poisoned by a panic in another thread.
    LockPoisoned,
}

impl fmt::Display for SailError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ModelFault { steps, pc } => write!(
                f,
                "Sail model assertion or pattern-match failure at step {steps} (pc=0x{pc:016x})"
            ),
            Self::ExceptionTrap { steps, pc } => write!(
                f,
                "AArch64 exception trap out of EL0 at step {steps} (pc=0x{pc:016x})"
            ),
            Self::StepLimitExceeded { max_steps, last_pc } => write!(
                f,
                "execution did not reach exit_pc within {max_steps} steps (last pc=0x{last_pc:016x})"
            ),
            Self::LockPoisoned => write!(f, "process-global Sail simulator mutex poisoned"),
        }
    }
}

impl Error for SailError {}

/// Exclusive RAII handle to the in-process Sail Armv9.4-A simulator.
///
/// Because the Sail C code generator (`sail -c`) emits process-global state variables for
/// registers and physical memory, `Simulator` holds a process-wide [`MutexGuard`] for its
/// lifetime and releases all sparse physical memory pages (`kill_mem()`) when dropped.
pub struct Simulator {
    _guard: MutexGuard<'static, ()>,
}

impl Simulator {
    /// Acquire the process-global Sail simulator lock and initialize the model to `initial`.
    pub fn new(initial: &CpuState) -> Result<Self, SailError> {
        let guard = SAIL_LOCK.lock().map_err(|_| SailError::LockPoisoned)?;
        let mut sim = Self { _guard: guard };
        sim.reset(initial);
        Ok(sim)
    }

    /// Clear all physical memory pages and reset architectural registers and flags to `state`.
    pub fn reset(&mut self, state: &CpuState) {
        let mut vregs_lo = [0u64; 32];
        let mut vregs_hi = [0u64; 32];
        for (i, &v) in state.vregs.iter().enumerate() {
            vregs_lo[i] = v as u64;
            vregs_hi[i] = (v >> 64) as u64;
        }
        // SAFETY: `self._guard` holds exclusive access to the Sail C model; arrays have fixed
        // lengths matching `sail_harness_reset`.
        unsafe {
            sail_harness_reset(
                state.gprs.as_ptr(),
                vregs_lo.as_ptr(),
                vregs_hi.as_ptr(),
                state.sp,
                state.pc,
                state.nzcv & 0xF,
            );
            sail_harness_set_fpcr(state.fpcr);
            sail_harness_set_fpsr(state.fpsr);
            sail_harness_set_tpidr_el0(state.tpidr_el0);
        }
    }

    /// Write raw `bytes` into Sail physical memory starting at `addr`.
    pub fn write_memory(&mut self, addr: u64, bytes: &[u8]) {
        if bytes.is_empty() {
            return;
        }
        // SAFETY: `self._guard` holds exclusive access; `bytes` is valid for `bytes.len()`.
        unsafe {
            sail_harness_write_bytes(addr, bytes.as_ptr(), bytes.len());
        }
    }

    /// Write little-endian 32-bit A64 instruction words into Sail physical memory at `base_pc`.
    pub fn write_code(&mut self, base_pc: u64, words: &[u32]) {
        let mut code_bytes = Vec::with_capacity(words.len() * 4);
        for &w in words {
            code_bytes.extend_from_slice(&w.to_le_bytes());
        }
        self.write_memory(base_pc, &code_bytes);
    }

    /// Write the low `size.min(8)` bytes of `val` in little-endian order at `addr`.
    pub fn write_u64_le(&mut self, addr: u64, val: u64, size: usize) {
        let le_bytes = val.to_le_bytes();
        let len = size.min(8);
        self.write_memory(addr, &le_bytes[..len]);
    }

    /// Read `len` bytes from Sail physical memory starting at `addr`.
    pub fn read_memory(&self, addr: u64, len: usize) -> Vec<u8> {
        let mut buf = vec![0u8; len];
        if len > 0 {
            // SAFETY: `self._guard` holds exclusive access; `buf` is valid for `len` bytes.
            unsafe {
                sail_harness_read_bytes(addr, buf.as_mut_ptr(), len);
            }
        }
        buf
    }

    /// Read `size.min(8)` bytes from `addr` in little-endian order and zero-extend to `u64`.
    pub fn read_u64_le(&self, addr: u64, size: usize) -> u64 {
        let len = size.min(8);
        let mut buf = [0u8; 8];
        if len > 0 {
            // SAFETY: `self._guard` holds exclusive access; `buf` has 8 bytes >= `len`.
            unsafe {
                sail_harness_read_bytes(addr, buf.as_mut_ptr(), len);
            }
        }
        u64::from_le_bytes(buf)
    }

    /// Read the current user-space architectural state (`X0..X30`, `V0..V31`, `SP`, `PC`, `NZCV`).
    pub fn read_state(&self) -> CpuState {
        let mut gprs = [0u64; 31];
        let mut vregs_lo = [0u64; 32];
        let mut vregs_hi = [0u64; 32];
        let mut sp = 0u64;
        let mut pc = 0u64;
        let mut nzcv = 0u8;
        // SAFETY: `self._guard` holds exclusive access; all output pointers are valid.
        unsafe {
            sail_harness_read_state(
                gprs.as_mut_ptr(),
                vregs_lo.as_mut_ptr(),
                vregs_hi.as_mut_ptr(),
                &mut sp,
                &mut pc,
                &mut nzcv,
            );
        }
        let mut vregs = [0u128; 32];
        for i in 0..32 {
            vregs[i] = ((vregs_hi[i] as u128) << 64) | (vregs_lo[i] as u128);
        }
        let (fpcr, fpsr, tpidr_el0) = unsafe {
            (
                sail_harness_read_fpcr(),
                sail_harness_read_fpsr(),
                sail_harness_read_tpidr_el0(),
            )
        };
        CpuState {
            gprs,
            vregs,
            sp,
            pc,
            nzcv: nzcv & 0xF,
            fpcr,
            fpsr,
            tpidr_el0,
        }
    }

    /// Read the floating-point status register (`FPSR`).
    pub fn read_fpsr(&self) -> u64 {
        // SAFETY: `self._guard` holds exclusive access.
        unsafe { sail_harness_read_fpsr() }
    }

    /// Set the floating-point status register (`FPSR`).
    pub fn set_fpsr(&mut self, fpsr: u64) {
        // SAFETY: `self._guard` holds exclusive access.
        unsafe { sail_harness_set_fpsr(fpsr) }
    }

    /// Read the floating-point control register (`FPCR`).
    pub fn read_fpcr(&self) -> u64 {
        // SAFETY: `self._guard` holds exclusive access.
        unsafe { sail_harness_read_fpcr() }
    }

    /// Set the floating-point control register (`FPCR`).
    pub fn set_fpcr(&mut self, fpcr: u64) {
        // SAFETY: `self._guard` holds exclusive access.
        unsafe { sail_harness_set_fpcr(fpcr) }
    }

    /// Read the user thread pointer register (`TPIDR_EL0`).
    pub fn read_tpidr_el0(&self) -> u64 {
        // SAFETY: `self._guard` holds exclusive access.
        unsafe { sail_harness_read_tpidr_el0() }
    }

    /// Set the user thread pointer register (`TPIDR_EL0`).
    pub fn set_tpidr_el0(&mut self, tpidr_el0: u64) {
        // SAFETY: `self._guard` holds exclusive access.
        unsafe { sail_harness_set_tpidr_el0(tpidr_el0) }
    }

    /// Step a single instruction in the Sail Armv9.4-A model (`zstep_model`).
    pub fn step(&mut self) -> Result<(), SailError> {
        // Choose an `exit_pc` that cannot equal the current `PC` before stepping.
        let cur_pc = self.read_state().pc;
        let dummy_exit = cur_pc.wrapping_add(1);
        let _ = self.step_until(dummy_exit, 1)?;
        Ok(())
    }

    /// Step up to `max_steps` instructions, stopping early when `PC == exit_pc`.
    ///
    /// Matches the bounded stepping semantics of Lean's `execUntilPC` and Unicorn's `emu_start`:
    /// reaching `max_steps` without faulting returns `Ok(StopReason::StepLimitReached { .. })`.
    /// Use [`Simulator::run_to_exit`] if failing to reach `exit_pc` should be an error.
    pub fn step_until(&mut self, exit_pc: u64, max_steps: usize) -> Result<StopReason, SailError> {
        let mut steps = 0usize;
        let mut pc = 0u64;
        // SAFETY: `self._guard` holds exclusive access.
        let rc = unsafe { sail_harness_step_until(exit_pc, max_steps, &mut steps, &mut pc) };
        match rc {
            0 => Ok(StopReason::ReachedExitPc { steps }),
            1 => Ok(StopReason::StepLimitReached { steps, pc }),
            -1 => Err(SailError::ModelFault { steps, pc }),
            -2 => Err(SailError::ExceptionTrap { steps, pc }),
            _ => Err(SailError::ModelFault { steps, pc }),
        }
    }

    /// Step up to `max_steps` instructions and require that execution reaches `exit_pc`.
    ///
    /// Returns [`SailError::StepLimitExceeded`] if `max_steps` instructions execute without
    /// reaching `exit_pc`.
    pub fn run_to_exit(&mut self, exit_pc: u64, max_steps: usize) -> Result<CpuState, SailError> {
        match self.step_until(exit_pc, max_steps)? {
            StopReason::ReachedExitPc { .. } => Ok(self.read_state()),
            StopReason::StepLimitReached { pc, .. } => Err(SailError::StepLimitExceeded {
                max_steps,
                last_pc: pc,
            }),
        }
    }
}

impl Drop for Simulator {
    fn drop(&mut self) {
        // SAFETY: `self._guard` is still held while `drop` runs.
        unsafe {
            sail_harness_clear_mem();
        }
    }
}

/// [`Arm64Oracle`] implementation backed by [`Simulator`].
pub struct SailOracle {
    sim: Simulator,
    watch: Vec<Range<u64>>,
}

impl SailOracle {
    /// Acquire the process-global Sail simulator lock and create a new [`SailOracle`].
    pub fn new() -> Result<Self, SailError> {
        let sim = Simulator::new(&CpuState::default())?;
        Ok(Self {
            sim,
            watch: Vec::new(),
        })
    }

    /// Borrow the underlying [`Simulator`].
    pub fn simulator(&self) -> &Simulator {
        &self.sim
    }

    /// Mutably borrow the underlying [`Simulator`].
    pub fn simulator_mut(&mut self) -> &mut Simulator {
        &mut self.sim
    }

    fn read_watched(&self) -> Vec<(u64, Vec<u8>)> {
        self.watch
            .iter()
            .map(|r| {
                let len = r.end.saturating_sub(r.start) as usize;
                (r.start, self.sim.read_memory(r.start, len))
            })
            .collect()
    }

    fn classify_fault(&self, pc: u64) -> Outcome {
        let bytes = self.sim.read_memory(pc, 4);
        let word = u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
        let kind = if isa_oracle::is_svc_encoding(word) {
            FaultKind::Svc
        } else {
            FaultKind::Other
        };
        Outcome::Fault { pc, kind }
    }
}

impl Arm64Oracle for SailOracle {
    fn name(&self) -> &'static str {
        "Sail"
    }

    fn load(&mut self, input: &TestInput) -> Result<(), String> {
        self.sim.reset(&input.state);
        for (base_pc, words) in &input.code {
            self.sim.write_code(*base_pc, words);
        }
        for (addr, bytes) in &input.mem {
            self.sim.write_memory(*addr, bytes);
        }
        self.watch = input.watch.clone();
        Ok(())
    }

    fn step(&mut self) -> Outcome {
        let cur_pc = self.sim.read_state().pc;
        let dummy_exit = cur_pc.wrapping_add(1);
        match self.sim.step_until(dummy_exit, 1) {
            Ok(_) => Outcome::Ok {
                state: self.sim.read_state(),
                mem: self.read_watched(),
                steps: 1,
            },
            Err(SailError::ExceptionTrap { pc, .. } | SailError::ModelFault { pc, .. }) => {
                self.classify_fault(pc)
            }
            Err(err) => Outcome::OracleError(err.to_string()),
        }
    }

    fn run(&mut self, input: &TestInput) -> Outcome {
        if let Err(err) = self.load(input) {
            return Outcome::OracleError(err);
        }
        if input.max_steps == 0 {
            let state = self.sim.read_state();
            if state.pc == input.exit_pc {
                return Outcome::Ok {
                    state,
                    mem: self.read_watched(),
                    steps: 0,
                };
            }
            return Outcome::StepLimit { pc: state.pc };
        }
        match self.sim.step_until(input.exit_pc, input.max_steps) {
            Ok(StopReason::ReachedExitPc { steps }) => Outcome::Ok {
                state: self.sim.read_state(),
                mem: self.read_watched(),
                steps,
            },
            Ok(StopReason::StepLimitReached { steps, pc }) => {
                if input.exit_pc == NO_EXIT_PC {
                    Outcome::Ok {
                        state: self.sim.read_state(),
                        mem: self.read_watched(),
                        steps,
                    }
                } else {
                    Outcome::StepLimit { pc }
                }
            }
            Err(SailError::ExceptionTrap { pc, .. } | SailError::ModelFault { pc, .. }) => {
                self.classify_fault(pc)
            }
            Err(err) => Outcome::OracleError(err.to_string()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const CODE_BASE: u64 = 0x0001_0000;
    const STACK_BASE: u64 = 0x0002_8000;
    const EXIT_PC: u64 = 0x0004_0000;

    #[test]
    fn test_adds_sets_carry_and_overflow_flags() {
        let mut init = CpuState::new(CODE_BASE, STACK_BASE);
        init.set_x(1, 0x7fff_ffff_ffff_ffff);
        init.set_x(2, 0x8000_0000_0000_0001);
        init.set_x(30, EXIT_PC);

        let mut sim = Simulator::new(&init).expect("Simulator::new succeeds");
        sim.write_code(
            CODE_BASE,
            &[
                0xab02_0020, // adds x0, x1, x2  -> 0x0000_0000_0000_0000, C=1, Z=1
                0xd65f_03c0, // ret
            ],
        );

        let out = sim
            .run_to_exit(EXIT_PC, 10)
            .expect("execution reaches EXIT_PC");
        assert_eq!(out.x(0), 0);
        assert_eq!(out.pc, EXIT_PC);
        assert!(!out.flag_n());
        assert!(out.flag_z());
        assert!(out.flag_c());
        assert!(!out.flag_v());
    }

    #[test]
    fn test_memory_str_ldr_roundtrip() {
        let mut init = CpuState::new(CODE_BASE, STACK_BASE);
        init.set_x(0, 0xdead_beef_cafe_babe);
        init.set_x(30, EXIT_PC);

        let mut sim = Simulator::new(&init).expect("Simulator::new succeeds");
        sim.write_code(
            CODE_BASE,
            &[
                0xf900_0be0, // str x0, [sp, #16]
                0xf940_0be3, // ldr x3, [sp, #16]
                0xd65f_03c0, // ret
            ],
        );

        let out = sim
            .run_to_exit(EXIT_PC, 10)
            .expect("execution reaches EXIT_PC");
        assert_eq!(out.x(3), 0xdead_beef_cafe_babe);
        assert_eq!(sim.read_u64_le(STACK_BASE + 16, 8), 0xdead_beef_cafe_babe);
    }

    #[test]
    fn test_scalar_fp_fadd_d0() {
        let mut init = CpuState::new(CODE_BASE, STACK_BASE);
        init.set_v(1, 1.5f64.to_bits() as u128);
        init.set_v(2, 2.25f64.to_bits() as u128);
        init.set_x(30, EXIT_PC);

        let mut sim = Simulator::new(&init).expect("Simulator::new succeeds");
        sim.write_code(
            CODE_BASE,
            &[
                0x1e62_2820, // fadd d0, d1, d2
                0xd65f_03c0, // ret
            ],
        );

        let out = sim
            .run_to_exit(EXIT_PC, 10)
            .expect("execution reaches EXIT_PC");
        assert_eq!(out.v(0) as u64, 3.75f64.to_bits());
    }

    #[test]
    fn test_reset_isolates_consecutive_runs() {
        let mut init1 = CpuState::new(CODE_BASE, STACK_BASE);
        init1.set_x(0, 0x1111_2222_3333_4444);
        init1.set_x(30, EXIT_PC);

        let mut sim = Simulator::new(&init1).expect("Simulator::new succeeds");
        sim.write_u64_le(0x0002_0000, 0xaaaa_bbbb_cccc_dddd, 8);
        sim.write_code(CODE_BASE, &[0xd65f_03c0]); // ret
        let out1 = sim.run_to_exit(EXIT_PC, 4).expect("first run succeeds");
        assert_eq!(out1.x(0), 0x1111_2222_3333_4444);
        assert_eq!(sim.read_u64_le(0x0002_0000, 8), 0xaaaa_bbbb_cccc_dddd);

        // Reset to a fresh state and verify that both registers and sparse physical memory were cleared.
        let mut init2 = CpuState::new(CODE_BASE, STACK_BASE);
        init2.set_x(30, EXIT_PC);
        sim.reset(&init2);
        assert_eq!(sim.read_u64_le(0x0002_0000, 8), 0);
        sim.write_code(
            CODE_BASE,
            &[
                0xd280_0540, // mov x0, #42
                0xd65f_03c0, // ret
            ],
        );
        let out2 = sim.run_to_exit(EXIT_PC, 4).expect("second run succeeds");
        assert_eq!(out2.x(0), 42);
    }

    #[test]
    fn test_step_limit_reached_and_run_to_exit_error() {
        let mut init = CpuState::new(CODE_BASE, STACK_BASE);
        init.set_x(30, EXIT_PC);

        let mut sim = Simulator::new(&init).expect("Simulator::new succeeds");
        sim.write_code(
            CODE_BASE,
            &[
                0xd280_0020, // mov x0, #1
                0xd280_0041, // mov x1, #2
                0xd65f_03c0, // ret
            ],
        );

        let stop = sim
            .step_until(EXIT_PC, 1)
            .expect("step_until returns Ok on step limit");
        assert_eq!(
            stop,
            StopReason::StepLimitReached {
                steps: 1,
                pc: CODE_BASE + 4
            }
        );

        sim.reset(&init);
        sim.write_code(
            CODE_BASE,
            &[
                0xd280_0020, // mov x0, #1
                0xd280_0041, // mov x1, #2
                0xd65f_03c0, // ret
            ],
        );
        let err = sim
            .run_to_exit(EXIT_PC, 1)
            .expect_err("run_to_exit fails when exit_pc is not reached");
        assert_eq!(
            err,
            SailError::StepLimitExceeded {
                max_steps: 1,
                last_pc: CODE_BASE + 4
            }
        );
    }

    #[test]
    fn test_exception_trap_on_svc() {
        let init = CpuState::new(CODE_BASE, STACK_BASE);
        let mut sim = Simulator::new(&init).expect("Simulator::new succeeds");
        sim.write_code(
            CODE_BASE,
            &[
                0xd400_0001, // svc #0 -> traps from EL0 to EL1
            ],
        );

        let err = sim
            .step_until(EXIT_PC, 4)
            .expect_err("svc #0 traps out of EL0");
        assert!(matches!(err, SailError::ExceptionTrap { steps: 1, .. }));
    }

    #[test]
    fn test_sail_oracle_nop_identity_roundtrip() {
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
        input.mem = vec![(0x0002_0000, vec![0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88])];
        input.mapped.push(0x0002_0000..0x0002_1000);
        input.watch = vec![0x0002_0000..0x0002_0008];

        let mut oracle = SailOracle::new().expect("SailOracle::new succeeds");
        let out = oracle.run(&input);
        let mut expected = init;
        expected.pc = CODE_BASE + 4;
        assert_eq!(
            out,
            Outcome::Ok {
                state: expected,
                mem: vec![(0x0002_0000, vec![0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88])],
                steps: 1,
            }
        );
    }
}

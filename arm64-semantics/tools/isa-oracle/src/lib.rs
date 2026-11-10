// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Common AArch64 ISA oracle trait, typed architectural state, and differential comparison policy
//! (`[TEST ONLY]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[TEST ONLY]` (shared interface and comparison engine for differential ISA
//!   testing across Lean 4 `Arm64.Step`, official ARM Sail Armv9.4-A, and Unicorn Engine).
//! - **Purpose:** Provides a single zero-dependency Rust crate defining:
//!   - [`CpuState`]: User-space (`EL0`) AArch64 architectural state (`X0..X30`, `V0..V31`, `SP`,
//!     `PC`, `NZCV`, `FPCR`, `FPSR`, `TPIDR_EL0`).
//!   - [`TestInput`]: Complete test input (`state`, `code`, `mem`, `mapped`, `watch`, `exit_pc`,
//!     `max_steps`).
//!   - [`Outcome`] and [`FaultKind`]: Structured execution outcomes (`Ok`, `Unmodeled`, `Fault`,
//!     `StepLimit`, `OracleError`).
//!   - [`Arm64Oracle`]: Trait implemented by `SailOracle`, `UnicornOracle`, and `LeanOracle`.
//!   - [`Policy`], [`FieldMismatch`], [`ThreeWayVerdict`], and [`diff`]: Single typed comparison
//!     and adjudication implementation.
//!
//! # Key Types & Functions
//! - [`CpuState`]: Complete user-space AArch64 register and control/status state.
//! - [`TestInput`]: Input state, code words, initial memory, mapped ranges, and watched ranges.
//! - [`Outcome`], [`FaultKind`]: Post-execution state or fault/unmodeled classification.
//! - [`Arm64Oracle`]: Common trait (`name`, `load`, `step`, `run`, `run_batch`).
//! - [`Policy`], [`diff`]: Typed state comparison and oracle quirk adjudication.
//!
//! # When to Read This File
//! - Read this file when auditing or modifying what state fields are compared across Lean, Sail,
//!   and Unicorn, or how `Arm64Oracle` steps and compares test inputs.

use std::fmt;
use std::ops::Range;

/// AArch64 architectural `NOP` instruction encoding (`0xd503_201f`).
pub const AARCH64_NOP_WORD: u32 = 0xd503_201f;

/// Sentinel `exit_pc` indicating that execution should run for `max_steps` instructions without
/// stopping early on a target program counter.
pub const NO_EXIT_PC: u64 = u64::MAX;

/// Mask of modeled `FPSR` cumulative status bits in `Arm64.State`:
/// `IOC` (bit 0), `DZC` (bit 1), `OFC` (bit 2), `UFC` (bit 3), `IXC` (bit 4), `IDC` (bit 7),
/// and `QC` (bit 27). All other bits (`RES0` and AArch32 `NZCV[31:28]`) are `0`.
pub const FPSR_MASK: u64 = 0x0800_009f;

/// Returns `true` if `insn` is in the AArch64 `HINT` encoding space (`0xd503_201f` mask `0xffff_f01f`)
/// with `CRm:op2` outside the side-effect-free hint subset `{0, 1, 4, 5, 16, 20, 22}`.
#[inline]
pub fn is_non_nop_hint_encoding(insn: u32) -> bool {
    (insn & 0xffff_f01f) == AARCH64_NOP_WORD
        && !matches!((insn >> 5) & 0x7f, 0 | 1 | 4 | 5 | 16 | 20 | 22)
}

/// Returns `true` if `insn` is an `SVC #imm16` supervisor call instruction (`0xd400_0001` mask `0xffe0_001f`).
#[inline]
pub fn is_svc_encoding(insn: u32) -> bool {
    (insn & 0xffe0_001f) == 0xd400_0001
}

/// Complete user-space AArch64 architectural state (`EL0`, `SP_EL0`, little-endian).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CpuState {
    /// General-purpose registers `X0`..`X30`.
    pub gprs: [u64; 31],
    /// 128-bit SIMD/FP vector registers `V0`..`V31` (`Q0`..`Q31`).
    pub vregs: [u128; 32],
    /// User stack pointer (`SP_EL0`).
    pub sp: u64,
    /// Program counter (`PC`).
    pub pc: u64,
    /// Condition flags `NZCV` in the low 4 bits (`bit 3 = N, bit 2 = Z, bit 1 = C, bit 0 = V`).
    pub nzcv: u8,
    /// Floating-point control register (`FPCR`).
    pub fpcr: u64,
    /// Floating-point status register (`FPSR`).
    pub fpsr: u64,
    /// User-space thread ID register (`TPIDR_EL0`).
    pub tpidr_el0: u64,
}

impl Default for CpuState {
    fn default() -> Self {
        Self {
            gprs: [0; 31],
            vregs: [0; 32],
            sp: 0,
            pc: 0,
            nzcv: 0,
            fpcr: 0,
            fpsr: 0,
            tpidr_el0: 0,
        }
    }
}

impl CpuState {
    /// Create a zeroed `CpuState` with the given initial `pc` and `sp`.
    pub fn new(pc: u64, sp: u64) -> Self {
        Self {
            pc,
            sp,
            ..Self::default()
        }
    }

    /// Read general-purpose register `X<idx>` (`0 <= idx < 31`).
    pub fn x(&self, idx: usize) -> u64 {
        self.gprs[idx]
    }

    /// Set general-purpose register `X<idx>` (`0 <= idx < 31`).
    pub fn set_x(&mut self, idx: usize, val: u64) {
        self.gprs[idx] = val;
    }

    /// Read 128-bit SIMD/FP register `V<idx>` (`0 <= idx < 32`).
    pub fn v(&self, idx: usize) -> u128 {
        self.vregs[idx]
    }

    /// Set 128-bit SIMD/FP register `V<idx>` (`0 <= idx < 32`).
    pub fn set_v(&mut self, idx: usize, val: u128) {
        self.vregs[idx] = val;
    }

    /// Return the `N` (Negative) condition flag (`bit 3` of `nzcv`).
    pub fn flag_n(&self) -> bool {
        (self.nzcv >> 3) & 1 != 0
    }

    /// Return the `Z` (Zero) condition flag (`bit 2` of `nzcv`).
    pub fn flag_z(&self) -> bool {
        (self.nzcv >> 2) & 1 != 0
    }

    /// Return the `C` (Carry) condition flag (`bit 1` of `nzcv`).
    pub fn flag_c(&self) -> bool {
        (self.nzcv >> 1) & 1 != 0
    }

    /// Return the `V` (Overflow) condition flag (`bit 0` of `nzcv`).
    pub fn flag_v(&self) -> bool {
        self.nzcv & 1 != 0
    }
}

/// Canonical input for a single-instruction or multi-instruction differential test run.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TestInput {
    /// Initial architectural state.
    pub state: CpuState,
    /// Little-endian 32-bit instruction word blocks `(base_pc, words)`.
    pub code: Vec<(u64, Vec<u32>)>,
    /// Initial data memory writes `(addr, bytes)`.
    pub mem: Vec<(u64, Vec<u8>)>,
    /// Mapped virtual address ranges `[start, end)`.
    pub mapped: Vec<Range<u64>>,
    /// Memory ranges `[start, end)` to read back into [`Outcome::Ok::mem`] after execution.
    pub watch: Vec<Range<u64>>,
    /// Stop address (`PC == exit_pc`), or [`NO_EXIT_PC`] (`u64::MAX`) for fixed-step runs.
    pub exit_pc: u64,
    /// Maximum number of instructions to step.
    pub max_steps: usize,
}

impl TestInput {
    /// Construct a single-instruction test input at `state.pc` with no extra data memory.
    pub fn single_insn(state: CpuState, word: u32) -> Self {
        let pc = state.pc;
        Self {
            state,
            code: vec![(pc, vec![word])],
            mem: Vec::new(),
            mapped: vec![pc..pc.wrapping_add(4)],
            watch: Vec::new(),
            exit_pc: NO_EXIT_PC,
            max_steps: 1,
        }
    }

    /// Look up the 32-bit instruction word at `addr` in `self.code`.
    pub fn word_at(&self, addr: u64) -> Option<u32> {
        for (base, words) in &self.code {
            if addr >= *base {
                let off = addr - *base;
                if off % 4 == 0 {
                    let idx = (off / 4) as usize;
                    if idx < words.len() {
                        return Some(words[idx]);
                    }
                }
            }
        }
        None
    }

    /// Return the initial instruction word at `self.state.pc`, if present in `self.code`.
    pub fn entry_word(&self) -> Option<u32> {
        self.word_at(self.state.pc)
    }

    /// Return a copy of `self` where the instruction word at `self.state.pc` is replaced with `NOP`.
    pub fn neutralized_to_nop(&self) -> Self {
        let mut out = self.clone();
        let pc = out.state.pc;
        for (base, words) in &mut out.code {
            if pc >= *base {
                let off = pc - *base;
                if off % 4 == 0 {
                    let idx = (off / 4) as usize;
                    if idx < words.len() {
                        words[idx] = AARCH64_NOP_WORD;
                    }
                }
            }
        }
        out
    }
}

/// Coarse architectural fault classification across Lean, Sail, and Unicorn.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FaultKind {
    /// Unmapped or permission-faulting memory fetch/load/store.
    Unmapped,
    /// Misaligned `PC`, `SP`, or atomic/exclusive memory address.
    Misaligned,
    /// Undefined instruction trap (`UDF`, `BRK`, reserved encoding trap).
    Undefined,
    /// Supervisor call (`SVC #imm`).
    Svc,
    /// Other synchronous trap or model assertion failure.
    Other,
}

/// Result of stepping or running a [`TestInput`] on an [`Arm64Oracle`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Outcome {
    /// Execution completed normally (`steps` instructions executed).
    Ok {
        /// Post-execution architectural state.
        state: CpuState,
        /// Watched memory slices `(start_addr, bytes)` corresponding to `TestInput::watch`.
        mem: Vec<(u64, Vec<u8>)>,
        /// Number of instructions executed.
        steps: usize,
    },
    /// Instruction word at `pc` is not modeled by the decoder (`Arm64.decode w = none`).
    Unmodeled { pc: u64, word: u32 },
    /// Execution raised an architectural fault or trap out of `EL0` at `pc`.
    Fault { pc: u64, kind: FaultKind },
    /// Execution reached `max_steps` without reaching `exit_pc`.
    StepLimit { pc: u64 },
    /// Internal emulator or IPC failure.
    OracleError(String),
}

impl Outcome {
    /// Short human-readable summary of the outcome variant.
    pub fn summary(&self) -> String {
        match self {
            Self::Ok { state, steps, .. } => {
                format!("Ok(pc=0x{:016x}, steps={steps})", state.pc)
            }
            Self::Unmodeled { pc, word } => {
                format!("Unmodeled(pc=0x{pc:016x}, word=0x{word:08x})")
            }
            Self::Fault { pc, kind } => {
                format!("Fault(pc=0x{pc:016x}, kind={kind:?})")
            }
            Self::StepLimit { pc } => {
                format!("StepLimit(pc=0x{pc:016x})")
            }
            Self::OracleError(msg) => format!("OracleError({msg})"),
        }
    }
}

/// Common interface implemented by all AArch64 ISA evaluators (Sail, Unicorn, and Lean).
pub trait Arm64Oracle {
    /// Human-readable oracle identifier (e.g. `"Lean"`, `"Sail"`, `"Unicorn"`).
    fn name(&self) -> &'static str;

    /// Reset the oracle and load `input` (registers, mapped pages, memory bytes, and code words).
    fn load(&mut self, input: &TestInput) -> Result<(), String>;

    /// Execute one instruction from the currently loaded state and return the post-step [`Outcome`].
    fn step(&mut self) -> Outcome;

    /// Load `input` and execute up to `input.max_steps` instructions until `PC == input.exit_pc`.
    fn run(&mut self, input: &TestInput) -> Outcome {
        if let Err(err) = self.load(input) {
            return Outcome::OracleError(err);
        }
        let mut total_steps = 0usize;
        loop {
            if total_steps >= input.max_steps {
                return Outcome::StepLimit {
                    pc: input.state.pc,
                };
            }
            match self.step() {
                Outcome::Ok {
                    state,
                    mem,
                    steps,
                } => {
                    total_steps += steps.max(1);
                    if state.pc == input.exit_pc
                        || (input.exit_pc == NO_EXIT_PC && total_steps >= input.max_steps)
                    {
                        return Outcome::Ok {
                            state,
                            mem,
                            steps: total_steps,
                        };
                    }
                    if total_steps >= input.max_steps {
                        return Outcome::StepLimit { pc: state.pc };
                    }
                }
                other => return other,
            }
        }
    }

    /// Execute a batch of independent [`TestInput`] records and return one [`Outcome`] per record.
    fn run_batch(&mut self, inputs: &[TestInput]) -> Vec<Outcome> {
        inputs.iter().map(|inp| self.run(inp)).collect()
    }
}

/// Policy governing differential comparison, hint neutralization, and oracle quirk adjudication.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Policy {
    /// Rewrite unmodeled (`Outcome::Unmodeled`) and faulting single-instruction probe inputs to `NOP`
    /// when preparing reference-oracle batches.
    pub neutralize_unmodeled_to_nop: bool,
    /// Rewrite non-NOP `HINT` encodings (`CRm:op2` outside `{0, 1, 4, 5, 16, 20, 22}`) to `NOP`.
    pub neutralize_non_nop_hints: bool,
    /// When Lean and authoritative Sail Armv9.4-A agree (`Outcome::Ok`) and Unicorn diverges,
    /// adjudicate the divergence as a known QEMU 5.0 TCG FP/SIMD quirk.
    pub sail_adjudicates_unicorn_fp_quirks: bool,
    /// Whether `CpuState::fpsr` (masked to [`FPSR_MASK`]) is compared (`true` by default).
    pub compare_fpsr: bool,
    /// Whether `CpuState::fpcr` is compared (`false` by default; `Arm64.State` pins `FPCR = 0`).
    pub compare_fpcr: bool,
    /// Whether `CpuState::tpidr_el0` is compared (`false` by default unless testing `TPIDR_EL0`).
    pub compare_tpidr_el0: bool,
}

impl Default for Policy {
    fn default() -> Self {
        Self {
            neutralize_unmodeled_to_nop: true,
            neutralize_non_nop_hints: true,
            sail_adjudicates_unicorn_fp_quirks: true,
            compare_fpsr: true,
            compare_fpcr: false,
            compare_tpidr_el0: false,
        }
    }
}

/// A single field or outcome mismatch between two [`Outcome`] values.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FieldMismatch {
    /// Architectural field or outcome name (`"outcome"`, `"X0"`, `"V3"`, `"SP"`, `"PC"`, `"NZCV"`, `"Mem[0x...]"`).
    pub field: String,
    /// Value produced by the left-hand oracle.
    pub lhs: String,
    /// Value produced by the right-hand oracle.
    pub rhs: String,
}

impl FieldMismatch {
    /// Format this mismatch with explicit oracle names `lhs_name` and `rhs_name`.
    pub fn format_with_names(&self, lhs_name: &str, rhs_name: &str) -> String {
        format!(
            "{}: {lhs_name}={} vs {rhs_name}={}",
            self.field, self.lhs, self.rhs
        )
    }
}

impl fmt::Display for FieldMismatch {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {} vs {}", self.field, self.lhs, self.rhs)
    }
}

fn format_mem_bytes_le(bytes: &[u8]) -> String {
    if bytes.len() <= 8 {
        let mut buf = [0u8; 8];
        buf[..bytes.len()].copy_from_slice(bytes);
        format!("0x{:016x}", u64::from_le_bytes(buf))
    } else {
        let mut s = String::with_capacity(2 + bytes.len() * 2);
        s.push_str("0x");
        for &b in bytes.iter().rev() {
            use std::fmt::Write as _;
            let _ = write!(s, "{b:02x}");
        }
        s
    }
}

/// Compare two [`Outcome`] values under `policy` and return all field mismatches (empty on match).
pub fn diff(a: &Outcome, b: &Outcome, policy: &Policy) -> Vec<FieldMismatch> {
    match (a, b) {
        (
            Outcome::Ok {
                state: sa,
                mem: ma,
                ..
            },
            Outcome::Ok {
                state: sb,
                mem: mb,
                ..
            },
        ) => {
            let mut errs = Vec::new();
            for r in 0..31 {
                if sa.gprs[r] != sb.gprs[r] {
                    errs.push(FieldMismatch {
                        field: format!("X{r}"),
                        lhs: format!("0x{:016x}", sa.gprs[r]),
                        rhs: format!("0x{:016x}", sb.gprs[r]),
                    });
                }
            }
            for r in 0..32 {
                if sa.vregs[r] != sb.vregs[r] {
                    errs.push(FieldMismatch {
                        field: format!("V{r}"),
                        lhs: format!("0x{:032x}", sa.vregs[r]),
                        rhs: format!("0x{:032x}", sb.vregs[r]),
                    });
                }
            }
            if sa.sp != sb.sp {
                errs.push(FieldMismatch {
                    field: "SP".to_string(),
                    lhs: format!("0x{:016x}", sa.sp),
                    rhs: format!("0x{:016x}", sb.sp),
                });
            }
            if sa.pc != sb.pc {
                errs.push(FieldMismatch {
                    field: "PC".to_string(),
                    lhs: format!("0x{:016x}", sa.pc),
                    rhs: format!("0x{:016x}", sb.pc),
                });
            }
            let nzcv_a = sa.nzcv & 0xF;
            let nzcv_b = sb.nzcv & 0xF;
            if nzcv_a != nzcv_b {
                errs.push(FieldMismatch {
                    field: "NZCV".to_string(),
                    lhs: format!("{nzcv_a}"),
                    rhs: format!("{nzcv_b}"),
                });
            }
            if policy.compare_fpcr && sa.fpcr != sb.fpcr {
                errs.push(FieldMismatch {
                    field: "FPCR".to_string(),
                    lhs: format!("0x{:016x}", sa.fpcr),
                    rhs: format!("0x{:016x}", sb.fpcr),
                });
            }
            if policy.compare_fpsr && (sa.fpsr & FPSR_MASK) != (sb.fpsr & FPSR_MASK) {
                errs.push(FieldMismatch {
                    field: "FPSR".to_string(),
                    lhs: format!("0x{:08x}", sa.fpsr & FPSR_MASK),
                    rhs: format!("0x{:08x}", sb.fpsr & FPSR_MASK),
                });
            }
            if policy.compare_tpidr_el0 && sa.tpidr_el0 != sb.tpidr_el0 {
                errs.push(FieldMismatch {
                    field: "TPIDR_EL0".to_string(),
                    lhs: format!("0x{:016x}", sa.tpidr_el0),
                    rhs: format!("0x{:016x}", sb.tpidr_el0),
                });
            }
            if ma.len() != mb.len() {
                errs.push(FieldMismatch {
                    field: "mem_watch.len".to_string(),
                    lhs: format!("{}", ma.len()),
                    rhs: format!("{}", mb.len()),
                });
            }
            for ((addr_a, bytes_a), (addr_b, bytes_b)) in ma.iter().zip(mb.iter()) {
                if addr_a != addr_b || bytes_a != bytes_b {
                    if bytes_a.len() == 64 && bytes_b.len() == 64 && addr_a == addr_b {
                        for w_idx in 0..8 {
                            let wa = &bytes_a[w_idx * 8..(w_idx + 1) * 8];
                            let wb = &bytes_b[w_idx * 8..(w_idx + 1) * 8];
                            if wa != wb {
                                errs.push(FieldMismatch {
                                    field: format!("Mem[0x{:016x}]", addr_a + (w_idx as u64) * 8),
                                    lhs: format_mem_bytes_le(wa),
                                    rhs: format_mem_bytes_le(wb),
                                });
                            }
                        }
                    } else {
                        errs.push(FieldMismatch {
                            field: format!("Mem[0x{addr_a:016x}]"),
                            lhs: format_mem_bytes_le(bytes_a),
                            rhs: format_mem_bytes_le(bytes_b),
                        });
                    }
                }
            }
            errs
        }
        (Outcome::Unmodeled { .. }, Outcome::Unmodeled { .. }) => Vec::new(),
        (Outcome::Fault { kind: ka, .. }, Outcome::Fault { kind: kb, .. }) => {
            if ka == kb {
                Vec::new()
            } else {
                vec![FieldMismatch {
                    field: "fault_kind".to_string(),
                    lhs: format!("{ka:?}"),
                    rhs: format!("{kb:?}"),
                }]
            }
        }
        (Outcome::StepLimit { pc: pa }, Outcome::StepLimit { pc: pb }) => {
            if pa == pb {
                Vec::new()
            } else {
                vec![FieldMismatch {
                    field: "step_limit.pc".to_string(),
                    lhs: format!("0x{pa:016x}"),
                    rhs: format!("0x{pb:016x}"),
                }]
            }
        }
        _ => vec![FieldMismatch {
            field: "outcome".to_string(),
            lhs: a.summary(),
            rhs: b.summary(),
        }],
    }
}

/// Verdict of a 3-way comparison between Lean, authoritative Sail Armv9.4-A, and optional Unicorn.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ThreeWayVerdict {
    /// Lean agreed with Sail (and Unicorn, if present).
    Match,
    /// Lean and Sail agreed bit-for-bit, while Unicorn diverged due to a known QEMU 5.0 TCG quirk.
    UnicornQuirkAdjudicatedBySail {
        unicorn_mismatches: Vec<FieldMismatch>,
    },
    /// Lean diverged from an active oracle.
    Mismatch {
        oracle_name: &'static str,
        mismatches: Vec<FieldMismatch>,
    },
}

impl Policy {
    /// Compare `lean` against authoritative `sail` and optional `unicorn` according to `self`.
    pub fn adjudicate_three_way(
        &self,
        lean: &Outcome,
        sail: &Outcome,
        unicorn: Option<&Outcome>,
    ) -> ThreeWayVerdict {
        let sail_mismatches = diff(lean, sail, self);
        if !sail_mismatches.is_empty() {
            return ThreeWayVerdict::Mismatch {
                oracle_name: "Sail",
                mismatches: sail_mismatches,
            };
        }
        if let Some(uc) = unicorn {
            let uc_mismatches = diff(lean, uc, self);
            if !uc_mismatches.is_empty() {
                if self.sail_adjudicates_unicorn_fp_quirks
                    && matches!(lean, Outcome::Ok { .. })
                    && matches!(sail, Outcome::Ok { .. })
                {
                    return ThreeWayVerdict::UnicornQuirkAdjudicatedBySail {
                        unicorn_mismatches: uc_mismatches,
                    };
                }
                return ThreeWayVerdict::Mismatch {
                    oracle_name: "Unicorn",
                    mismatches: uc_mismatches,
                };
            }
        }
        ThreeWayVerdict::Match
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cpu_state_accessors_and_flags() {
        let mut st = CpuState::new(0x10000, 0x80000);
        st.set_x(5, 0x1234_5678_9abc_def0);
        st.set_v(12, 0x1122_3344_5566_7788_99aa_bbcc_ddee_ff00);
        st.nzcv = 0b1010;
        assert_eq!(st.x(5), 0x1234_5678_9abc_def0);
        assert_eq!(st.v(12), 0x1122_3344_5566_7788_99aa_bbcc_ddee_ff00);
        assert!(st.flag_n());
        assert!(!st.flag_z());
        assert!(st.flag_c());
        assert!(!st.flag_v());
    }

    #[test]
    fn test_diff_detects_register_and_memory_mismatches() {
        let policy = Policy::default();
        let mut s1 = CpuState::new(0x10004, 0x80000);
        s1.set_x(0, 42);
        let mut s2 = s1.clone();
        s2.set_x(0, 43);

        let o1 = Outcome::Ok {
            state: s1,
            mem: vec![(0x20000, vec![1, 2, 3, 4, 5, 6, 7, 8])],
            steps: 1,
        };
        let o2 = Outcome::Ok {
            state: s2,
            mem: vec![(0x20000, vec![1, 2, 3, 4, 5, 6, 7, 9])],
            steps: 1,
        };
        let m = diff(&o1, &o2, &policy);
        assert_eq!(m.len(), 2);
        assert_eq!(m[0].field, "X0");
        assert_eq!(m[1].field, "Mem[0x0000000000020000]");
    }

    #[test]
    fn test_policy_optional_fpsr_and_three_way_adjudication() {
        let mut policy = Policy::default();
        let mut s_lean = CpuState::new(0x10004, 0x80000);
        s_lean.set_v(0, 0x7ff8_0000_0000_0000);
        let mut s_sail = s_lean.clone();
        s_sail.fpsr = 0x10;
        let mut s_uc = s_lean.clone();
        s_uc.set_v(0, 0xfff8_0000_0000_0000);

        let o_lean = Outcome::Ok {
            state: s_lean,
            mem: vec![],
            steps: 1,
        };
        let o_sail = Outcome::Ok {
            state: s_sail,
            mem: vec![],
            steps: 1,
        };
        let o_uc = Outcome::Ok {
            state: s_uc,
            mem: vec![],
            steps: 1,
        };

        // Default policy compares FPSR masked to FPSR_MASK (0x0800_009f).
        assert_eq!(diff(&o_lean, &o_sail, &policy).len(), 1);

        policy.compare_fpsr = false;
        assert!(diff(&o_lean, &o_sail, &policy).is_empty());
        assert!(matches!(
            policy.adjudicate_three_way(&o_lean, &o_sail, Some(&o_uc)),
            ThreeWayVerdict::UnicornQuirkAdjudicatedBySail { .. }
        ));
    }

    #[test]
    fn test_non_nop_hint_and_neutralize() {
        assert!(!is_non_nop_hint_encoding(AARCH64_NOP_WORD));
        // PACIA1716 = 0xd503_211f (CRm:op2 = 8)
        assert!(is_non_nop_hint_encoding(0xd503_211f));
        let inp = TestInput::single_insn(CpuState::new(0x10000, 0x80000), 0xd503_211f);
        assert_eq!(inp.entry_word(), Some(0xd503_211f));
        let neut = inp.neutralized_to_nop();
        assert_eq!(neut.entry_word(), Some(AARCH64_NOP_WORD));
    }
}

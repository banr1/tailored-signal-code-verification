/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Lean.Data.Json
public import Arm64
public import Arm64.Testing.Harness.TestCase
public import Arm64.Testing.Harness.FpEval

/-!
# Outcome Classification and Standalone JSON Evaluation

Outcome classification (`TestOutcomeClass`, `BatchOutcomeCounts`) and standalone `IsaTestCase` JSON
evaluation (`EvalOutcome`, `evalTestCase`), plus re-export of IEEE-754 batch evaluation from
`Arm64.Testing.Harness.FpEval`. Cross-oracle state comparison (`isa_oracle::diff` and `Policy`)
across Lean (`diff_eval --serve`), ARM Sail (`armv9.4-a`), and Unicorn (`UC_ARCH_ARM64`) is
implemented in `tools/isa-oracle` and `tools/run-trusted-tests/src/compare.rs`.

## Oracle Comparison Matrix

| Oracle | Execution Mode | `X0..X30` (31 x 64b) | `V0..V31` (32 x 128b) | `SP` (64b) | `PC` (64b) | `NZCV` (4b) | `FPSR` (32b) | Memory | Unmodeled / Exception / Quirk Handling |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| Unicorn (`UC_ARCH_ARM64`, QEMU 5.0 TCG) | Multi-step (`IsaTestCase`) & single-insn (`TestInput`) | Exact 64-bit | Exact 128-bit | Exact 64-bit | Exact 64-bit | Exact 4-bit (`[31:28]`) | Masked `0x0800009f` (`IOC`, `DZC`, `OFC`, `UFC`, `IXC`, `IDC`, `QC`) | `memWatch` (multi-step) or full 64B scratch `[0x20000, 0x20040)` (`watch`) | Multi-step: any decode failure or `status != .Running` is a test failure. Single-insn batch: `Outcome::Ok` is executed and compared; `Outcome::Unmodeled` and `Outcome::Fault` are counted and neutralized to `NOP` before batch execution; known QEMU 5.0 TCG FP/SIMD quirks where Lean and Sail agree are counted in `unicorn_fp_quirks_adjudicated_by_sail`. |
| Sail Armv9.4-A (`aarch64_small` ASL-derived C model) | Multi-step (`IsaTestCase`) & single-insn (`TestInput`) | Exact 64-bit | Exact 128-bit | Exact 64-bit | Exact 64-bit | Exact 4-bit (`PSTATE.{N,Z,C,V}`) | Masked `0x0800009f` (`IOC`, `DZC`, `OFC`, `UFC`, `IXC`, `IDC`, `QC`) | `memWatch` (multi-step) or full 64B scratch `[0x20000, 0x20040)` (`watch`) | Primary architectural authority for `Outcome::Ok` cases. Only skipped (`skip_sail`) on 2 multi-step cases: `System/Dczid_DcZva_LinuxUserspace` (Sail sets `DCZID_EL0.DZP=1` and traps `DC ZVA` at EL0, unlike Linux userspace `DCZID_EL0 = 4`) and `SimdExtra/Addv_ByteLanes` (the Sail C model hits an internal assertion on byte-lane `ADDV`). |
| Berkeley SoftFloat 3e (`ARM-VFPv2`) & IBM FPgen (`softfloat-sys`) | Pure IEEE-754 batch (`FpBatchRecord`, 480,435 vectors) | N/A | Exact 32-bit / 64-bit IEEE-754 bit pattern (or 4-bit `NZCV` for `FCMP`/`FCMPE`) | N/A | N/A | Exact 4-bit for `FCMP`/`FCMPE` (`op in {20, 22, 52, 54}`) | Exact 5-bit IEEE-754 flags (`IOC`, `DZC`, `OFC`, `UFC`, `IXC`, mask `0x1f`) | N/A | `TestFloat` and `stratified_fp` compare Lean's `FPCR.DN=0` standard ARM NaN propagation and cumulative `FPSR` exception flags bit-for-bit against SoftFloat `ARM-VFPv2` with no NaN canonicalization. In IBM FPgen, symbolic `Q` (`0x7fc00000`) quiet-NaN expected tokens are accepted when Lean and SoftFloat both return a `binary32` NaN and counted in `fpgen_nan_canonicalized`; IEEE 754-1985 trapped underflow/overflow (`u`/`o` enabled on LHS and raised on RHS, `E ± 192` exponent wrapping) lines are counted in `fpgen_trapped_exception_skipped`. |
| Linux Kernel (`qemu-aarch64` / `aarch64-linux-gnu-gcc`) | Syscall trace (`diff_eval --fs-diff-trace`) & ELF (`elf_eval`) | Exact `X0` return value / step return codes | N/A | Checked via ABI | Checked via `exitPC` | N/A | N/A | File contents & cursor offsets after 17-step VFS trace + ELF relocation outputs | Compares Lean's `FsState` (`openat`/`read`/`write`/`lseek`/`close`) and ELF loader against real Linux execution. |

## Masking, Canonicalization, and Adjudication Rules

1. Unmodeled decode (`Outcome::Unmodeled`, `Arm64.decode w = none`):
   In multi-step `IsaTestCase` suites, any decode failure fails the test (`passed = false`). In
   single-instruction `run_batch` fuzzing (`diff_eval --serve`), `Serve.lean` returns
   `STATUS_UNMODELED (1)`, which `classify_lean_insn_batch` in `compare.rs` counts in
   `OutcomeCounts::unmodeled_decode` and skips before invoking Sail/Unicorn.
2. Execution exception (`Outcome::Fault`, `sf.status != .Running`):
   In multi-step `IsaTestCase` suites, any `.Exception` fails the test (`passed = false`). In
   single-instruction `run_batch` fuzzing (`diff_eval --serve`), `Serve.lean` returns
   `STATUS_FAULT_OTHER (13)` (e.g., misaligned `SP` or unmapped memory outside
   `[0x20000, 0x20040)`), which `compare.rs` counts in `OutcomeCounts::exec_exception` and skips
   before invoking Sail/Unicorn.
3. Non-NOP `HINT` encodings (`(w &&& 0xfffff01f) == 0xd503201f`, `CRm:op2 not in {0, 1, 4, 5, 16, 20, 22}`):
   Armv8.3+ PAC (`PACIA1716`, `AUTIA1716`, `XPACLRI`) and Armv8.5+ BTI hints in the `HINT` encoding
   space mutate `X16`/`X17`/`X30` or `PSTATE.BTYPE` in Sail Armv9.4-A, whereas Lean models those
   `HINT` encodings as architectural `NOP`. Counted in `OutcomeCounts::non_nop_hint_neutralized` and
   rewritten to `NOP` (`0xd503_201f`) before invoking the oracles.
4. Unicorn QEMU 5.0 TCG FP/SIMD quirks (`unicorn_fp_quirks_adjudicated_by_sail`):
   When Lean and ARM Sail (`armv9.4-a`) agree bit-for-bit (`ThreeWayVerdict::UnicornQuirkAdjudicatedBySail`)
   but Unicorn disagrees, Sail is authoritative and the divergence is counted in
   `OutcomeCounts::unicorn_fp_quirks_adjudicated_by_sail`.
5. IBM FPgen IEEE 754-1985 trapped underflow/overflow (`fpgen_trapped_exception_skipped`):
   FPgen lines where `u` (underflow) or `o` (overflow) is both trap-enabled on the LHS and raised on
   the RHS specify the IEEE 754-1985 sections 7.3/7.4 trap-handler exponent-wrapped (`E ± 192`)
   result instead of the untrapped IEEE-754 value produced by ARM64 instructions
   (`FPCR.UFE=0, OFE=0`). Counted in `OutcomeCounts::fpgen_trapped_exception_skipped`.
6. IBM FPgen symbolic `Q` quiet-NaN results (`fpgen_nan_canonicalized`):
   FPgen writes symbolic `Q` (`0x7fc0_0000`) for any quiet NaN without fixing an architecture
   payload; when `exp_val`, `lean_val`, and `softfloat_val` are all `binary32` NaNs, the case is
   counted in `OutcomeCounts::fpgen_nan_canonicalized` (`TestFloat` and `stratified_fp` still check
   Lean's exact NaN bit pattern bit-for-bit against SoftFloat `ARM-VFPv2`).
7. Floating-point & SIMD status register (`FPSR`, mask `0x0800009f`):
   `Policy.compare_fpsr` compares `(fpsr & 0x0800009f)` (`IOC` bit 0, `DZC` bit 1, `OFC` bit 2,
   `UFC` bit 3, `IXC` bit 4, `IDC` bit 7, and `QC` bit 27; AArch32-only `NZCV[31:28]` is `RES0` /
   RAZ-WI) across Lean, Sail Armv9.4-A, and Unicorn. In `--batch-fp`, all 480,435 IEEE-754 vectors
   compare the 5 IEEE-754 exception flags (`0x1f`) between Lean's `*Flags` functions and SoftFloat
   (`softfloat_exceptionFlags`).
-/

@[expose] public section

namespace Testing.Harness

open Lean
open Arm64

/-- Classification of a single-instruction or multi-instruction test evaluation, mirrored by
    `tools/run-trusted-tests/src/compare.rs`. -/
inductive TestOutcomeClass where
  /-- Instruction(s) decoded and executed to completion (`status = .Running`), and all active
      oracles were compared bit-for-bit. -/
  | executed
  /-- `Arm64.decode` returned `none` (instruction encoding is outside the modeled A64 subset or
      is a fail-closed reserved encoding). Counted in `OutcomeCounts::unmodeled_decode`. -/
  | unmodeledDecode
  /-- Instruction decoded, but `execInst` / `execUntilPC` terminated with `status != .Running`
      (e.g., `BRK`, unaligned `PC`/`SP`, permission fault, or `SVC` without a handler).
      Counted in `OutcomeCounts::exec_exception`. -/
  | execException
  /-- Non-NOP `HINT` encoding (`(w &&& 0xfffff01f) == 0xd503201f`, `CRm:op2 not in {0, 1, 4, 5, 16, 20, 22}`)
      in external binary corpora such as Linaro RISU. -/
  | nonNopHint
  /-- Executed and compared against Unicorn, with standalone Sail skipped via `skip_sail`. -/
  | skippedOracle (reason : String)
  deriving Repr, DecidableEq, Inhabited

/-- Summary counters for a batch of single-instruction evaluations. -/
structure BatchOutcomeCounts where
  total           : Nat := 0
  executed        : Nat := 0
  unmodeledDecode : Nat := 0
  execException   : Nat := 0
  deriving Repr, DecidableEq, Inhabited

/-- Result of evaluating a single multi-instruction `IsaTestCase` JSON object on Lean's operational
    semantics. -/
structure EvalOutcome where
  name         : String
  json         : Json
  passed       : Bool
  mismatches   : Array String
  totalWords   : Nat
  outcomeClass : TestOutcomeClass := .executed

/-- Evaluate a single multi-instruction test case JSON object on Lean's operational semantics
    (`IsaTestCase.fromJson`, `IsaTestCase.toInitialState`, `execUntilPC`). -/
def evalTestCase (tcJson : Json) : EvalOutcome := Id.run do
  let tc := IsaTestCase.fromJson tcJson
  let (prog, st) := tc.toInitialState

  let mut decodeErrors : Array String := #[]
  let mut inputHexArr : Array Json := #[]
  let mut mismatches : Array String := #[]

  for i in [0:tc.words.size] do
    let w := tc.words[i]!
    let inHex := hex32 w
    inputHexArr := inputHexArr.push (Json.str inHex)
    if (decode w).isNone then
      let addr := tc.basePC + BitVec.ofNat 64 (i * 4)
      let msg := s!"word[{i}] = {inHex} failed to decode ({Arm64.describeUnsupportedAt addr w})"
      decodeErrors := decodeErrors.push msg
      mismatches := mismatches.push s!"decode_error: {msg}"

  let sf := execUntilPC tc.maxSteps prog tc.exitPC st
  if sf.status != .Running then
    mismatches := mismatches.push s!"exec_exception at pc={hex64 sf.pc}"

  let mut outRegs : Array Json := #[]
  for i in [0:31] do
    let v := hex64 (sf.readReg64 (.gpr (BitVec.ofNat 5 i)))
    outRegs := outRegs.push (Json.str v)

  let mut outVRegs : Array Json := #[]
  for i in [0:32] do
    let v := hex128 (sf.readVReg128 (BitVec.ofNat 5 i))
    outVRegs := outVRegs.push (Json.str v)

  let outSP := hex64 sf.sp
  let outPC := hex64 sf.pc
  let outNZCV := (pstateToBits4 sf.pstate).toNat

  let mut outMem : Array Json := #[]
  for m in tc.memWatch do
    let memSz : MemWidth :=
      match m.size with
      | 1 => .B8
      | 2 => .H16
      | 4 => .W32
      | _ => .X64
    let v := sf.mem.readSized memSz false m.addr
    let addrStr := hex64 m.addr
    let valStr := hex64 v
    outMem := outMem.push (Json.mkObj [
      ("addr", Json.str addrStr),
      ("size", toJson m.size),
      ("val", Json.str valStr)
    ])

  let outcomeClass : TestOutcomeClass :=
    if !decodeErrors.isEmpty then .unmodeledDecode
    else if sf.status != .Running then .execException
    else match tc.skipSail with
      | some reason => .skippedOracle reason
      | none => .executed

  let passed := mismatches.isEmpty
  let resJson := Json.mkObj [
    ("name", Json.str tc.name),
    ("passed", toJson passed),
    ("mismatches", toJson mismatches),
    ("total_words", toJson tc.words.size),
    ("decode_ok", toJson decodeErrors.isEmpty),
    ("decode_errors", toJson decodeErrors),
    ("input_hex", Json.arr inputHexArr),
    ("pc", Json.str outPC),
    ("sp", Json.str outSP),
    ("nzcv", toJson outNZCV),
    ("n", toJson sf.pstate.n),
    ("z", toJson sf.pstate.z),
    ("c", toJson sf.pstate.c),
    ("v", toJson sf.pstate.v),
    ("regs", Json.arr outRegs),
    ("vregs", Json.arr outVRegs),
    ("mem", Json.arr outMem)
  ]
  return {
    name := tc.name
    json := resJson
    passed := passed
    mismatches := mismatches
    totalWords := tc.words.size
    outcomeClass := outcomeClass
  }

end Testing.Harness

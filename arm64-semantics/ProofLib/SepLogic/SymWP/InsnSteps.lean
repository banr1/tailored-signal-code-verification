/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public meta import Arm64.Trusted.ISA.Syntax
public meta import ProofLib.Meta.ToExpr
public import ProofLib.SepLogic.WP
public import ProofLib.BV.PolyMul
import Arm64.Trusted.Spec.SepLogic

/-!
# Per-Instruction Symbolic Execution and Step Dispatch

Defines per-instruction unfolding predicates (`isReducibleArm64Helper`, `isUnfoldableArm64Eval`),
the pre-compiled `Sym.Simp` rewrite table (`symWPRewriteDecls`), the instruction-to-`SepWP` step
classification (`SymInsnStepRule`, `classifyInsnStepRule`), and direct symbolic step constructors
for pure instructions and 64-bit loads/stores (`symStepPureInsn?`, `symStepLdr64Insn?`,
`symStepStr64Insn?`).
-/

namespace ProofLib

open Lean Elab Tactic Meta
open Arm64

public meta section

/-! ## Per-Instruction Symbolic Evaluation Unfolding Table -/

/-- Set of `@[reducible]` ARM64 syntax and per-instruction-class evaluation helpers that may be
    exposed when a theorem RHS instantiates pattern variables with concrete constructors during
    `Sym.Simp`. Grouped by `Arm64/Trusted/ISA/Eval.lean` instruction category. -/
def isReducibleArm64Helper (declName : Name) : Bool :=
  -- Width projections
  declName == ``MemWidth.bytes ||
  declName == ``RegWidth.bits ||
  -- Per-instruction-class evaluators in `Arm64/Trusted/ISA/Eval.lean`
  declName == ``execAddSubImm ||
  declName == ``execAddSubExt ||
  declName == ``execAddSubShift ||
  declName == ``execAddSubCarry ||
  declName == ``execLogicalImm ||
  declName == ``execLogicalShift ||
  declName == ``execMoveWide ||
  declName == ``execBitfield ||
  declName == ``execCondSelect ||
  declName == ``execCondCompare ||
  declName == ``execDataProc1 ||
  declName == ``execDataProc2 ||
  declName == ``execDataProc3 ||
  declName == ``execLdr ||
  declName == ``execLdrLit ||
  declName == ``execStr ||
  declName == ``execLdp ||
  declName == ``execStp ||
  -- SIMD lane helpers
  declName == ``getSimdLane ||
  declName == ``mapLanes ||
  declName == ``zipLanes ||
  declName == ``laneMask

/-- Non-recursive ARM64 evaluator definitions (excluding `State.advancePC` and `evalAddSub`, which
    rewrite via explicit `State.advancePC_setPC` and `evalAddSub_*` lemmas) that can be unfolded
    definitionally once their constructor arguments are exposed. -/
def isUnfoldableArm64Eval (declName : Name) : Bool :=
  isReducibleArm64Helper declName ||
  -- Top-level instruction and addressing-mode dispatch
  declName == ``execInst ||
  declName == ``execInstWithSvc ||
  declName == ``Program.evalInst ||
  declName == ``evalAddrMode ||
  declName == ``applyWriteback ||
  -- Register and SIMD state accessors
  declName == ``State.writeReg ||
  declName == ``State.writeReg32 ||
  declName == ``State.readReg ||
  declName == ``State.readReg32 ||
  declName == ``State.writeVReg64 ||
  declName == ``State.writeVReg32 ||
  declName == ``State.readVReg64 ||
  declName == ``State.readVReg32 ||
  -- Shift, extension, logical, and bitfield ALU primitives
  declName == ``shift32 ||
  declName == ``shift64 ||
  declName == ``shiftVal ||
  declName == ``extendVal ||
  declName == ``evalLogical ||
  declName == ``evalBitfield ||
  -- Processor state (NZCV) and alignment helpers
  declName == ``PState.ofBits4 ||
  declName == ``PState.toBits4 ||
  declName == ``AddrMode.baseReg ||
  declName == ``checkRegSPAligned ||
  declName == ``checkAddrSPAligned ||
  declName == ``MemWidth.isAligned ||
  declName == ``CondCode.ofBits ||
  declName == ``ShiftType.ofBits ||
  declName == ``ExtendType.ofBits ||
  -- Floating-point immediate expansion (`FMOV Sd/Dd, #imm8`) and AdvSIMD helpers
  declName == ``vfpExpandImm32 ||
  declName == ``vfpExpandImm64 ||
  declName == ``applySimdResult ||
  declName == ``applySimdSatResult ||
  declName == ``evalSimdModImmExt ||
  declName == ``evalSimdImmShiftNonZeroExt ||
  declName == ``evalSimdImmShiftNonZeroExtSatFlags ||
  declName == ``evalSimdThreeSameExt ||
  declName == ``evalSimdThreeSameExtSatFlags ||
  declName == ``evalSimdTwoRegMiscExt ||
  declName == ``evalSimdTwoRegMiscExtSatFlags ||
  declName == ``advSimdExpandImm ||
  declName == ``narrowSimdLanes ||
  declName == ``anySimdLane ||
  declName == ``anyZipSimdLane ||
  declName == ``anyNarrowSimdLane ||
  declName == ``simdLaneUInt ||
  declName == ``simdLaneSInt ||
  declName == ``intToSimdLane ||
  declName == ``aslRShr ||
  declName == ``aslSignedSat ||
  declName == ``aslSignedSatFlag ||
  declName == ``aslUnsignedSat ||
  declName == ``aslUnsignedSatFlag ||
  declName == ``aslSat ||
  declName == ``aslSatFlag ||
  declName == ``simdClz ||
  declName == ``simdCls ||
  declName == ``shaChoose32 ||
  declName == ``shaParity32 ||
  declName == ``shaMajority32 ||
  declName == ``shaMajority64 ||
  declName == ``sha256Sigma0 ||
  declName == ``sha256Sigma1 ||
  declName == ``sha256Hash ||
  declName == ``evalCryptoSha2Reg ||
  declName == ``evalCryptoSha3Reg ||
  declName == ``evalCryptoSha512Reg2 ||
  declName == ``evalCryptoSha512Reg3 ||
  declName == ``evalCryptoSha3FourReg ||
  declName == ``evalCryptoXar

/-! ## Per-Instruction `Sym.Simp` Rewrite Rule Table -/

end

@[expose] public section

@[wp_norm]
theorem _root_.Arm64.State.advancePC_setMem_setPC (s : Arm64.State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).advancePC = (s.setPC (pc + 4#64)).setMem m := by
  cases s; rfl

end

public meta section

/-- Explicit rewrite lemmas compiled into `Sym.Simp.Theorems`, grouped by semantic category. -/
def symWPRewriteDecls : Array Name := #[
  -- State-update spine canonicalization (`State.writeReg64`, `setPC`, `setPState`, `setMem`)
  ``State.writeReg64_xzr,
  ``State.advancePC_setPC,
  ``State.advancePC_setMem_setPC,
  ``State.setPC_setPC,
  ``State.setPC_setMem_setPC,
  ``State.writeReg64_setPC,
  ``State.writeVReg128_setPC,
  ``State.setPState_setPC,
  ``State.setPState_setPState,
  ``State.writeReg64_setPState,
  ``State.writeVReg128_setPState,
  ``State.setMem_setPC,
  ``State.setMem_setMem,
  ``State.writeReg64_setMem,
  ``State.writeVReg128_setMem,
  ``State.setPState_setMem,
  ``State.orFpsr_zero,
  ``State.orFpsr_orFpsr,
  ``State.setFpsr_orFpsr,
  ``State.setFpsr_setFpsr,
  ``State.orFpsr_setFpsr,
  ``State.writeReg64_orFpsr,
  ``State.writeReg64_setFpsr,
  ``State.writeVReg128_orFpsr,
  ``State.writeVReg128_setFpsr,
  ``State.orFpsr_setPC,
  ``State.orFpsr_setMem,
  ``State.orFpsr_setPState,
  ``State.setFpsr_setPC,
  ``State.setFpsr_setMem,
  ``State.setFpsr_setPState,
  ``State.stepExclOracle_setPC,
  ``State.stepExclOracle_setMem,
  ``State.stepExclOracle_setPState,
  ``State.stepExclOracle_orFpsr,
  ``State.stepExclOracle_setFpsr,
  ``State.stepExclOracle_writeReg64,
  ``State.stepExclOracle_writeVReg128,
  ``State.stepExclLoop_setPC,
  ``State.stepExclLoop_setMem,
  ``State.stepExclLoop_setPState,
  ``State.stepExclLoop_orFpsr,
  ``State.stepExclLoop_setFpsr,
  ``State.stepExclLoop_writeReg64,
  ``State.stepExclLoop_writeVReg128,
  ``State.writeReg64_writeReg64_same,
  ``State.writeVReg128_writeVReg128_same,
  ``State.ite_setPC,
  ``State.ite_setMem,
  -- Addressing-mode evaluation (`evalAddrMode`)
  ``evalAddrMode_offset,
  ``evalAddrMode_unscaled,
  -- 64-bit and 32-bit ADD/ADDS/SUB/SUBS/ADC/ADCS/SBC/SBCS evaluation (`evalAddSub`)
  ``evalAddSub_w64_add,
  ``evalAddSub_w64_adds,
  ``evalAddSub_w64_sub,
  ``evalAddSub_w64_subs,
  ``evalAddSub_w64_adc,
  ``evalAddSub_w64_adcs,
  ``evalAddSub_w64_sbc,
  ``evalAddSub_w64_sbcs,
  ``evalAddSub_w32_add,
  ``evalAddSub_w32_sub,
  ``evalAddSub_w32_subs,
  ``evalAddSub_w32_adds,
  -- Condition-code and NZCV flag evaluation (`conditionHolds`, `subsPState*`, `addsPState*`)
  ``conditionHolds_eq_subs64,
  ``conditionHolds_ne_subs64,
  ``conditionHolds_cs_subs64,
  ``conditionHolds_cc_subs64,
  ``conditionHolds_hi_subs64,
  ``conditionHolds_ls_subs64,
  ``conditionHolds_ge_subs64,
  ``conditionHolds_lt_subs64,
  ``conditionHolds_gt_subs64,
  ``conditionHolds_le_subs64,
  ``conditionHolds_eq_subsPState64,
  ``conditionHolds_ne_subsPState64,
  ``conditionHolds_cs_subsPState64,
  ``conditionHolds_cc_subsPState64,
  ``conditionHolds_hi_subsPState64,
  ``conditionHolds_ls_subsPState64,
  ``conditionHolds_ge_subsPState64,
  ``conditionHolds_lt_subsPState64,
  ``conditionHolds_gt_subsPState64,
  ``conditionHolds_le_subsPState64,
  ``conditionHolds_eq_adds64,
  ``conditionHolds_ne_adds64,
  ``conditionHolds_cs_adds64,
  ``conditionHolds_cc_adds64,
  ``conditionHolds_eq_addsPState64,
  ``conditionHolds_ne_addsPState64,
  ``conditionHolds_cs_addsPState64,
  ``conditionHolds_cc_addsPState64,
  ``conditionHolds_eq_subs32,
  ``conditionHolds_ne_subs32,
  ``conditionHolds_cs_subs32,
  ``conditionHolds_cc_subs32,
  ``conditionHolds_hi_subs32,
  ``conditionHolds_ls_subs32,
  ``conditionHolds_ge_subs32,
  ``conditionHolds_lt_subs32,
  ``conditionHolds_gt_subs32,
  ``conditionHolds_le_subs32,
  ``conditionHolds_eq_subsPState32,
  ``conditionHolds_ne_subsPState32,
  ``conditionHolds_cs_subsPState32,
  ``conditionHolds_cc_subsPState32,
  ``conditionHolds_hi_subsPState32,
  ``conditionHolds_ls_subsPState32,
  ``conditionHolds_ge_subsPState32,
  ``conditionHolds_lt_subsPState32,
  ``conditionHolds_gt_subsPState32,
  ``conditionHolds_le_subsPState32,
  ``conditionHolds_eq_adds32,
  ``conditionHolds_ne_adds32,
  ``conditionHolds_cs_adds32,
  ``conditionHolds_cc_adds32,
  ``conditionHolds_eq_addsPState32,
  ``conditionHolds_ne_addsPState32,
  ``conditionHolds_cs_addsPState32,
  ``conditionHolds_cc_addsPState32,
  ``conditionHolds_mi_subs32,
  ``conditionHolds_pl_subs32,
  ``conditionHolds_mi_subsPState32,
  ``conditionHolds_pl_subsPState32,
  ``conditionHolds_mi_adds32,
  ``conditionHolds_pl_adds32,
  ``conditionHolds_mi_addsPState32,
  ``conditionHolds_pl_addsPState32,
  ``conditionHolds_mi_subs64,
  ``conditionHolds_pl_subs64,
  ``conditionHolds_mi_subsPState64,
  ``conditionHolds_pl_subsPState64,
  ``conditionHolds_mi_adds64,
  ``conditionHolds_pl_adds64,
  ``conditionHolds_mi_addsPState64,
  ``conditionHolds_pl_addsPState64,
  ``conditionHolds_eq_mk,
  ``conditionHolds_ne_mk,
  ``conditionHolds_mi_mk,
  ``conditionHolds_pl_mk,
  ``conditionHolds_ite,
  ``subsPState64_c,
  ``addsPState64_c,
  ``subsPState32_c,
  ``addsPState32_c,
  -- Bitvector arithmetic, logical, and width-extension normalization
  ``BitVec.truncate_64_zeroExtend_128,
  ``extractLsb_low64_append,
  ``extractLsb_high64_append,
  ``evalPmull_false_true,
  ``evalPmull_true_true,
  ``laneMask_8,
  ``laneMask_16,
  ``laneMask_32,
  ``laneMask_64,
  ``mapSimdLanes_true_8,
  ``mapSimdLanes_true_16,
  ``mapSimdLanes_true_32,
  ``mapSimdLanes_true_64,
  ``mapSimdLanes_false_8,
  ``mapSimdLanes_false_16,
  ``mapSimdLanes_false_32,
  ``mapSimdLanes_false_64,
  ``zipSimdLanes_true_8,
  ``zipSimdLanes_true_16,
  ``zipSimdLanes_true_32,
  ``zipSimdLanes_true_64,
  ``zipSimdLanes_false_8,
  ``zipSimdLanes_false_16,
  ``zipSimdLanes_false_32,
  ``zipSimdLanes_false_64,
  ``Int64.toBitVec_ofBitVec,
  ``Obj.adrp_pageOf_cancel,
  ``Obj.pageOf_add_sub_cancel,
  ``Obj.pageOf_add_lo12Of,
  ``Obj.pageOf_add_idx_add_lo12Of,
  ``Obj.pageOf_add_lo12Of_add_idx,
  ``Obj.addSignedAddr_zero,
  ``Arm64.bitvec_add_zero,
  ``BitVec.add_zero,
  ``BitVec.zero_add,
  ``bitvec_add_neg_eq_sub,
  ``bitvec_zero_sub_64,
  ``bitvec_zero_add_64,
  ``bitvec_zero_or_64,
  ``bitvec_zero_or_32,
  ``bitvec_sub_zero_64,
  ``bitvec_shiftLeft_zero,
  ``bitvec32_shiftLeft_zero,
  ``nat_zero_mod_64,
  ``nat_one_mod_64,
  ``truncate_32_zeroExtend_64,
  ``truncate_16_zeroExtend_64,
  ``truncate_8_zeroExtend_64,
  ``truncate_8_zeroExtend_32,
  ``zeroExtend_self,
  ``zeroExtend_64_zeroExtend_32_8,
  ``zeroExtend_64_zeroExtend_32_16,
  ``BitVec.truncate_ite,
  ``ofNat_countLeadingZeros64,
  ``ofNat_countLeadingZeros32,
  ``truncate32_ofNat_countLeadingZeros32,
  ``bitvec32_and_zeroExtend64,
  ``bitvec32_or_zeroExtend64,
  ``bitvec32_xor_zeroExtend64,
  ``bitvec32_bic_zeroExtend64,
  ``bitvec32_orn_zeroExtend64,
  ``bitvec32_eon_zeroExtend64,
  ``BitVec_allOnes_64,
  ``BitVec_allOnes_32,
  ``bitvec_ule_self,
  ``bitvec_ult_self,
  ``bitvec_sle_self,
  ``bitvec_slt_self,
  -- Boolean and `decide` normalizations
  ``Bool.not_true,
  ``Bool.not_false,
  ``Bool.not_not,
  ``Bool.true_and,
  ``Bool.false_and,
  ``Bool.and_true,
  ``Bool.and_false,
  ``Bool.true_or,
  ``Bool.false_or,
  ``Bool.or_true,
  ``Bool.or_false,
  ``Bool.bne_false,
  ``Bool.bne_true,
  ``beq_self_eq_true,
  ``bne_self_eq_false,
  ``decide_true,
  ``decide_false,
  -- Scalar IEEE-754 floating-point opcode dispatch, sign, and comparison normalizations
  ``evalFp1Op64_fmov,
  ``evalFp1Op64_fabs,
  ``evalFp1Op64_fneg,
  ``evalFp1Op64_fsqrt,
  ``evalFp1Op64_frintn,
  ``evalFp1Op64_frintp,
  ``evalFp1Op64_frintm,
  ``evalFp1Op64_frintz,
  ``evalFp1Op64_frinta,
  ``evalFp1Op64_frintx,
  ``evalFp1Op64_frinti,
  ``evalFp1Op32_fmov,
  ``evalFp1Op32_fabs,
  ``evalFp1Op32_fneg,
  ``evalFp1Op32_fsqrt,
  ``evalFp1Op32_frintn,
  ``evalFp1Op32_frintp,
  ``evalFp1Op32_frintm,
  ``evalFp1Op32_frintz,
  ``evalFp1Op32_frinta,
  ``evalFp1Op32_frintx,
  ``evalFp1Op32_frinti,
  ``evalFp2Op64_fmul,
  ``evalFp2Op64_fdiv,
  ``evalFp2Op64_fadd,
  ``evalFp2Op64_fsub,
  ``evalFp2Op64_fmax,
  ``evalFp2Op64_fmin,
  ``evalFp2Op64_fmaxnm,
  ``evalFp2Op64_fminnm,
  ``evalFp2Op64_fnmul,
  ``evalFp2Op32_fmul,
  ``evalFp2Op32_fdiv,
  ``evalFp2Op32_fadd,
  ``evalFp2Op32_fsub,
  ``evalFp2Op32_fmax,
  ``evalFp2Op32_fmin,
  ``evalFp2Op32_fmaxnm,
  ``evalFp2Op32_fminnm,
  ``evalFp2Op32_fnmul,
  ``evalFp3Op64_fmadd,
  ``evalFp3Op64_fmsub,
  ``evalFp3Op64_fnmadd,
  ``evalFp3Op64_fnmsub,
  ``evalFp3Op32_fmadd,
  ``evalFp3Op32_fmsub,
  ``evalFp3Op32_fnmadd,
  ``evalFp3Op32_fnmsub,
  ``evalFp1OpFlags64_fmov,
  ``evalFp1OpFlags64_fabs,
  ``evalFp1OpFlags64_fneg,
  ``evalFp1OpFlags64_fsqrt,
  ``evalFp1OpFlags64_frintn,
  ``evalFp1OpFlags64_frintp,
  ``evalFp1OpFlags64_frintm,
  ``evalFp1OpFlags64_frintz,
  ``evalFp1OpFlags64_frinta,
  ``evalFp1OpFlags64_frintx,
  ``evalFp1OpFlags64_frinti,
  ``evalFp1OpFlags32_fmov,
  ``evalFp1OpFlags32_fabs,
  ``evalFp1OpFlags32_fneg,
  ``evalFp1OpFlags32_fsqrt,
  ``evalFp1OpFlags32_frintn,
  ``evalFp1OpFlags32_frintp,
  ``evalFp1OpFlags32_frintm,
  ``evalFp1OpFlags32_frintz,
  ``evalFp1OpFlags32_frinta,
  ``evalFp1OpFlags32_frintx,
  ``evalFp1OpFlags32_frinti,
  ``evalFp2OpFlags64_fmul,
  ``evalFp2OpFlags64_fdiv,
  ``evalFp2OpFlags64_fadd,
  ``evalFp2OpFlags64_fsub,
  ``evalFp2OpFlags64_fmax,
  ``evalFp2OpFlags64_fmin,
  ``evalFp2OpFlags64_fmaxnm,
  ``evalFp2OpFlags64_fminnm,
  ``evalFp2OpFlags64_fnmul,
  ``evalFp2OpFlags32_fmul,
  ``evalFp2OpFlags32_fdiv,
  ``evalFp2OpFlags32_fadd,
  ``evalFp2OpFlags32_fsub,
  ``evalFp2OpFlags32_fmax,
  ``evalFp2OpFlags32_fmin,
  ``evalFp2OpFlags32_fmaxnm,
  ``evalFp2OpFlags32_fminnm,
  ``evalFp2OpFlags32_fnmul,
  ``evalFp3OpFlags64_fmadd,
  ``evalFp3OpFlags64_fmsub,
  ``evalFp3OpFlags64_fnmadd,
  ``evalFp3OpFlags64_fnmsub,
  ``evalFp3OpFlags32_fmadd,
  ``evalFp3OpFlags32_fmsub,
  ``evalFp3OpFlags32_fnmadd,
  ``evalFp3OpFlags32_fnmsub,
  ``fpNeg64_fpNeg64,
  ``fpAbs64_fpNeg64,
  ``fpAbs64_fpAbs64,
  ``fpNeg32_fpNeg32,
  ``fpAbs32_fpNeg32,
  ``fpAbs32_fpAbs32,
  ``conditionHolds_eq_evalFpCmp64,
  ``conditionHolds_ne_evalFpCmp64,
  ``conditionHolds_cs_evalFpCmp64,
  ``conditionHolds_cc_evalFpCmp64,
  ``conditionHolds_mi_evalFpCmp64,
  ``conditionHolds_pl_evalFpCmp64,
  ``conditionHolds_vs_evalFpCmp64,
  ``conditionHolds_vc_evalFpCmp64,
  ``conditionHolds_hi_evalFpCmp64,
  ``conditionHolds_ls_evalFpCmp64,
  ``conditionHolds_ge_evalFpCmp64,
  ``conditionHolds_lt_evalFpCmp64,
  ``conditionHolds_gt_evalFpCmp64,
  ``conditionHolds_le_evalFpCmp64,
  ``conditionHolds_eq_evalFpCmp32,
  ``conditionHolds_ne_evalFpCmp32,
  ``conditionHolds_cs_evalFpCmp32,
  ``conditionHolds_cc_evalFpCmp32,
  ``conditionHolds_mi_evalFpCmp32,
  ``conditionHolds_pl_evalFpCmp32,
  ``conditionHolds_vs_evalFpCmp32,
  ``conditionHolds_vc_evalFpCmp32,
  ``conditionHolds_hi_evalFpCmp32,
  ``conditionHolds_ls_evalFpCmp32,
  ``conditionHolds_ge_evalFpCmp32,
  ``conditionHolds_lt_evalFpCmp32,
  ``conditionHolds_gt_evalFpCmp32,
  ``conditionHolds_le_evalFpCmp32
]

/-! ## Instruction-to-`SepWP` Step Rule Dispatch Table -/

/-- Classification of the `SepWP` symbolic step rule for a decoded `Arm64.Instr`. -/
inductive SymInsnStepRule where
  /-- Pure register, flag, PC-relative, branch, or system instruction (`SepWP.step_pure_setPC`,
      `SepWP.step_pure_setMem_setPC`, `SepWP.step_pure`). -/
  | pureStep
  /-- Conditional compare `CCMP`/`CCMN` (register or immediate, 32- or 64-bit): the condition is
      kept inside the flag update (`SepWP.step_ccmp_reg`, `SepWP.step_ccmp_imm`,
      `SepWP.step_ccmn_reg`, `SepWP.step_ccmn_imm`). -/
  | condCompare
  /-- 64-bit general-purpose load `LDR Xt, [addr]` (`SepWP.step_ldr64`). -/
  | ldr64 (rt addr : Expr)
  /-- 64-bit general-purpose store `STR Xt, [addr]` (`SepWP.step_str64`). -/
  | str64 (rt addr : Expr)
  /-- 64-bit unscaled load `LDUR Xt, [addr]` (`SepWP.step_ldur64`). -/
  | ldur64
  /-- 64-bit unscaled store `STUR Xt, [addr]` (`SepWP.step_stur64`). -/
  | stur64
  /-- 64-bit load pair `LDP Xt1, Xt2, [addr]` (`SepWP.step_ldp64`). -/
  | ldp64
  /-- 64-bit store pair `STP Xt1, Xt2, [addr]` (`SepWP.step_stp64`). -/
  | stp64
  /-- 32-bit load `LDR Wt, [addr]` (`SepWP.step_ldr32`, `SepWP.step_ldr32_64`, `SepWP.step_ldr32_hi64`). -/
  | ldr32
  /-- 32-bit unscaled load `LDUR Wt, [addr]` (`SepWP.step_ldur32`, `SepWP.step_ldur32_64`). -/
  | ldur32
  /-- 32-bit signed-extending load `LDRSW Xt, [addr]` (`SepWP.step_ldrsw32`, `SepWP.step_ldrsw32_64`, `SepWP.step_ldrsw32_hi64`). -/
  | ldrsw32
  /-- 32-bit unscaled signed-extending load `LDURSW Xt, [addr]` (`SepWP.step_ldursw32`). -/
  | ldursw32
  /-- 32-bit load pair `LDP Wt1, Wt2, [addr]` (`SepWP.step_ldp32`, `SepWP.step_ldp32_64`). -/
  | ldp32
  /-- 32-bit store `STR Wt, [addr]` (`SepWP.step_str32`, `SepWP.step_str32_64`, `SepWP.step_str32_hi64`). -/
  | str32
  /-- 32-bit unscaled store `STUR Wt, [addr]` (`SepWP.step_stur32`, `SepWP.step_stur32_64`). -/
  | stur32
  /-- 32-bit store pair `STP Wt1, Wt2, [addr]` (`SepWP.step_stp32`, `SepWP.step_stp32_64`, `SepWP.step_stp32_hi_lo64`). -/
  | stp32
  /-- 32-bit load-acquire `LDAR Wt, [Xn]` (`SepWP.step_ldar32_64`). -/
  | ldar32
  /-- 16-bit unsigned halfword load `LDRH Wt, [addr]` (`SepWP.step_ldr16`, `SepWP.step_ldrh_bytes`). -/
  | ldr16
  /-- 16-bit unscaled halfword load `LDURH Wt, [addr]` (`SepWP.step_ldur16`, `SepWP.step_ldurh_bytes`). -/
  | ldur16
  /-- 16-bit signed halfword load `LDRSH Wt/Xt, [addr]` (`SepWP.step_ldrsh16`). -/
  | ldrsh16
  /-- 16-bit unscaled signed halfword load `LDURSH Wt/Xt, [addr]` (`SepWP.step_ldursh16`, `SepWP.step_ldursh_bytes`). -/
  | ldursh16
  /-- 16-bit halfword store `STRH Wt, [addr]` (`SepWP.step_str16`, `SepWP.step_strh_bytes`). -/
  | str16
  /-- 16-bit unscaled halfword store `STURH Wt, [addr]` (`SepWP.step_stur16`, `SepWP.step_sturh_bytes`). -/
  | stur16
  /-- 8-bit unsigned byte load `LDRB Wt, [addr]` (`SepWP.step_ldr8`, `SepWP.step_ldr8_64`). -/
  | ldr8
  /-- 8-bit unscaled byte load `LDURB Wt, [addr]` (`SepWP.step_ldur8`). -/
  | ldur8
  /-- 8-bit signed byte load `LDRSB Wt/Xt, [addr]` (`SepWP.step_ldrsb`). -/
  | ldrsb
  /-- 8-bit unscaled signed byte load `LDURSB Wt/Xt, [addr]` (`SepWP.step_ldursb`). -/
  | ldursb
  /-- 8-bit byte store `STRB Wt, [addr]` (`SepWP.step_str8`, `SepWP.step_str8_64`). -/
  | str8
  /-- 8-bit unscaled byte store `STURB Wt, [addr]` (`SepWP.step_stur8`). -/
  | stur8
  /-- 128-bit SIMD load `LDR Qt, [addr]` (`SepWP.step_ldrSimd128`). -/
  | ldrSimd128
  /-- 128-bit SIMD store `STR Qt, [addr]` (`SepWP.step_strSimd128`). -/
  | strSimd128
  /-- 128-bit SIMD load pair `LDP Qt1, Qt2, [addr]` (`SepWP.step_ldpSimd128`). -/
  | ldpSimd128
  /-- 128-bit SIMD store pair `STP Qt1, Qt2, [addr]` (`SepWP.step_stpSimd128`). -/
  | stpSimd128
  /-- 64-bit / 32-bit SIMD load `LDR Dt|St, [addr]` (`SepWP.step_ldrSimd64`, `SepWP.step_ldrSimd32`). -/
  | ldrSimdDS
  /-- 64-bit / 32-bit SIMD store `STR Dt|St, [addr]` (`SepWP.step_strSimd64`, `SepWP.step_strSimd32`). -/
  | strSimdDS
  /-- 64-bit SIMD load pair `LDP Dt1, Dt2, [addr]` (`SepWP.step_ldpSimd64`). -/
  | ldpSimd64
  /-- 64-bit SIMD store pair `STP Dt1, Dt2, [addr]` (`SepWP.step_stpSimd64`). -/
  | stpSimd64
  /-- Cache block zero by address `DC ZVA, Xt` (`SepWP.step_dcZva_bytes`, `SepWP.step_dcZva`). -/
  | dcZva
  /-- Other memory or special instruction variant handled by `wpStepCoreWithOutcome`. -/
  | otherMemOrSpecial
  deriving BEq, Inhabited

/-- Primary `SepWP.step_*` theorem name(s) associated with each `SymInsnStepRule`. -/
def SymInsnStepRule.theoremNames : SymInsnStepRule → Array Name
  | .pureStep          => #[``SepWP.step_pure_setPC, ``SepWP.step_pure_setMem_setPC, ``SepWP.step_pure]
  | .condCompare       => #[``SepWP.step_ccmp_reg, ``SepWP.step_ccmp_imm,
                            ``SepWP.step_ccmn_reg, ``SepWP.step_ccmn_imm]
  | .ldr64 _ _         => #[``SepWP.step_ldr64]
  | .str64 _ _         => #[``SepWP.step_str64]
  | .ldur64            => #[``SepWP.step_ldur64]
  | .stur64            => #[``SepWP.step_stur64]
  | .ldp64             => #[``SepWP.step_ldp64]
  | .stp64             => #[``SepWP.step_stp64]
  | .ldr32             => #[``SepWP.step_ldr32, ``SepWP.step_ldr32_64, ``SepWP.step_ldr32_hi64]
  | .ldur32            => #[``SepWP.step_ldur32, ``SepWP.step_ldur32_64]
  | .ldrsw32           => #[``SepWP.step_ldrsw32, ``SepWP.step_ldrsw32_64, ``SepWP.step_ldrsw32_hi64]
  | .ldursw32          => #[``SepWP.step_ldursw32]
  | .ldp32             => #[``SepWP.step_ldp32, ``SepWP.step_ldp32_64]
  | .str32             => #[``SepWP.step_str32, ``SepWP.step_str32_64, ``SepWP.step_str32_hi64]
  | .stur32            => #[``SepWP.step_stur32, ``SepWP.step_stur32_64]
  | .stp32             => #[``SepWP.step_stp32, ``SepWP.step_stp32_64, ``SepWP.step_stp32_hi_lo64]
  | .ldar32            => #[``SepWP.step_ldar32_64]
  | .ldr16             => #[``SepWP.step_ldr16, ``SepWP.step_ldrh_bytes]
  | .ldur16            => #[``SepWP.step_ldur16, ``SepWP.step_ldurh_bytes]
  | .ldrsh16           => #[``SepWP.step_ldrsh16]
  | .ldursh16          => #[``SepWP.step_ldursh16, ``SepWP.step_ldursh_bytes]
  | .str16             => #[``SepWP.step_str16, ``SepWP.step_strh_bytes]
  | .stur16            => #[``SepWP.step_stur16, ``SepWP.step_sturh_bytes]
  | .ldr8              => #[``SepWP.step_ldr8, ``SepWP.step_ldr8_64]
  | .ldur8             => #[``SepWP.step_ldur8]
  | .ldrsb             => #[``SepWP.step_ldrsb]
  | .ldursb            => #[``SepWP.step_ldursb]
  | .str8              => #[``SepWP.step_str8, ``SepWP.step_str8_64]
  | .stur8             => #[``SepWP.step_stur8]
  | .ldrSimd128        => #[``SepWP.step_ldrSimd128]
  | .strSimd128        => #[``SepWP.step_strSimd128]
  | .ldpSimd128        => #[``SepWP.step_ldpSimd128]
  | .stpSimd128        => #[``SepWP.step_stpSimd128]
  | .ldrSimdDS         => #[``SepWP.step_ldrSimd64, ``SepWP.step_ldrSimd32]
  | .strSimdDS         => #[``SepWP.step_strSimd64, ``SepWP.step_strSimd32]
  | .ldpSimd64         => #[``SepWP.step_ldpSimd64]
  | .stpSimd64         => #[``SepWP.step_stpSimd64]
  | .dcZva             => #[``SepWP.step_dcZva_bytes, ``SepWP.step_dcZva]
  | .otherMemOrSpecial => #[``SepWP.step_pure]

/-- Classify a decoded `instExpr : Arm64.Instr` into its `SymInsnStepRule` and `WpStepOutcome`. -/
def classifyInsnStepRule (instExpr : Expr) : SymInsnStepRule × WpStepOutcome :=
  let isBl := instExpr.isAppOfArity ``Instr.bl 1 || instExpr.isAppOfArity ``Instr.blr 1
  let isRet := instExpr.isAppOfArity ``Instr.ret 1
  let isUncondB := instExpr.isAppOfArity ``Instr.b 1
  let outcome : WpStepOutcome :=
    if isBl then .steppedCall
    else if isRet then .steppedRet
    else if isUncondB then .steppedBranch
    else .steppedNormal
  let isAnyMemOrSpecial :=
    instExpr.isAppOf ``Instr.ldr || instExpr.isAppOf ``Instr.str ||
    instExpr.isAppOf ``Instr.ldp || instExpr.isAppOf ``Instr.stp ||
    instExpr.isAppOf ``Instr.ldrSimd || instExpr.isAppOf ``Instr.strSimd ||
    instExpr.isAppOf ``Instr.ldpSimd || instExpr.isAppOf ``Instr.stpSimd ||
    instExpr.isAppOf ``Instr.dcZva ||
    instExpr.isAppOf ``Instr.ldarStlr ||
    instExpr.isAppOf ``Instr.ldxr || instExpr.isAppOf ``Instr.stxr
  let isCondCompare :=
    instExpr.isAppOfArity ``Instr.condCompareReg 6 || instExpr.isAppOfArity ``Instr.condCompareImm 6
  let rule : SymInsnStepRule :=
    if isCondCompare then
      .condCompare
    else if !isAnyMemOrSpecial then
      .pureStep
    else if instExpr.isAppOfArity ``Instr.ldr 5 &&
            instExpr.getArg! 0 == mkConst ``RegWidth.W64 &&
            isMemSizeConst (instExpr.getArg! 1) 8 &&
            instExpr.getArg! 2 == mkConst ``Bool.false then
      .ldr64 (instExpr.getArg! 3) (instExpr.getArg! 4)
    else if instExpr.isAppOfArity ``Instr.str 3 &&
            isMemSizeConst (instExpr.getArg! 0) 8 then
      .str64 (instExpr.getArg! 1) (instExpr.getArg! 2)
    else if instExpr.isAppOfArity ``Instr.ldp 5 &&
            instExpr.getArg! 0 == mkConst ``RegWidth.W64 &&
            instExpr.getArg! 1 == mkConst ``Bool.false then
      .ldp64
    else if instExpr.isAppOfArity ``Instr.stp 4 &&
            instExpr.getArg! 0 == mkConst ``RegWidth.W64 then
      .stp64
    else if instExpr.isAppOfArity ``Instr.ldr 5 &&
            instExpr.getArg! 0 == mkConst ``RegWidth.W32 &&
            isMemSizeConst (instExpr.getArg! 1) 4 &&
            instExpr.getArg! 2 == mkConst ``Bool.false then
      .ldr32
    else if instExpr.isAppOfArity ``Instr.ldr 5 &&
            instExpr.getArg! 0 == mkConst ``RegWidth.W64 &&
            isMemSizeConst (instExpr.getArg! 1) 4 &&
            instExpr.getArg! 2 == mkConst ``Bool.true then
      .ldrsw32
    else if instExpr.isAppOfArity ``Instr.ldp 5 &&
            instExpr.getArg! 0 == mkConst ``RegWidth.W32 &&
            instExpr.getArg! 1 == mkConst ``Bool.false then
      .ldp32
    else if instExpr.isAppOfArity ``Instr.str 3 &&
            isMemSizeConst (instExpr.getArg! 0) 4 then
      .str32
    else if instExpr.isAppOfArity ``Instr.stp 4 &&
            instExpr.getArg! 0 == mkConst ``RegWidth.W32 then
      .stp32
    else if instExpr.isAppOfArity ``Instr.ldarStlr 4 &&
            isMemSizeConst (instExpr.getArg! 0) 4 &&
            instExpr.getArg! 1 == mkConst ``Bool.true then
      .ldar32
    else if instExpr.isAppOfArity ``Instr.ldr 5 &&
            instExpr.getArg! 0 == mkConst ``RegWidth.W32 &&
            isMemSizeConst (instExpr.getArg! 1) 2 &&
            instExpr.getArg! 2 == mkConst ``Bool.false then
      .ldr16
    else if instExpr.isAppOfArity ``Instr.ldr 5 &&
            isMemSizeConst (instExpr.getArg! 1) 2 &&
            instExpr.getArg! 2 == mkConst ``Bool.true then
      .ldrsh16
    else if instExpr.isAppOfArity ``Instr.str 3 &&
            isMemSizeConst (instExpr.getArg! 0) 2 then
      .str16
    else if instExpr.isAppOfArity ``Instr.ldr 5 &&
            instExpr.getArg! 0 == mkConst ``RegWidth.W32 &&
            isMemSizeConst (instExpr.getArg! 1) 1 &&
            instExpr.getArg! 2 == mkConst ``Bool.false then
      .ldr8
    else if instExpr.isAppOfArity ``Instr.ldr 5 &&
            isMemSizeConst (instExpr.getArg! 1) 1 &&
            instExpr.getArg! 2 == mkConst ``Bool.true then
      .ldrsb
    else if instExpr.isAppOfArity ``Instr.str 3 &&
            isMemSizeConst (instExpr.getArg! 0) 1 then
      .str8
    else if instExpr.isAppOfArity ``Instr.ldrSimd 3 &&
            instExpr.getArg! 0 == mkConst ``SimdMemSize.Q128 then
      .ldrSimd128
    else if instExpr.isAppOfArity ``Instr.strSimd 3 &&
            instExpr.getArg! 0 == mkConst ``SimdMemSize.Q128 then
      .strSimd128
    else if instExpr.isAppOfArity ``Instr.ldpSimd 4 &&
            instExpr.getArg! 0 == mkConst ``SimdMemSize.Q128 then
      .ldpSimd128
    else if instExpr.isAppOfArity ``Instr.stpSimd 4 &&
            instExpr.getArg! 0 == mkConst ``SimdMemSize.Q128 then
      .stpSimd128
    else if instExpr.isAppOfArity ``Instr.ldrSimd 3 &&
            (instExpr.getArg! 0 == mkConst ``SimdMemSize.D64 ||
             instExpr.getArg! 0 == mkConst ``SimdMemSize.S32) then
      .ldrSimdDS
    else if instExpr.isAppOfArity ``Instr.strSimd 3 &&
            (instExpr.getArg! 0 == mkConst ``SimdMemSize.D64 ||
             instExpr.getArg! 0 == mkConst ``SimdMemSize.S32) then
      .strSimdDS
    else if instExpr.isAppOfArity ``Instr.ldpSimd 4 &&
            instExpr.getArg! 0 == mkConst ``SimdMemSize.D64 then
      .ldpSimd64
    else if instExpr.isAppOfArity ``Instr.stpSimd 4 &&
            instExpr.getArg! 0 == mkConst ``SimdMemSize.D64 then
      .stpSimd64
    else if instExpr.isAppOfArity ``Instr.dcZva 1 then
      .dcZva
    else
      .otherMemOrSpecial
  (rule, outcome)

/-! ## Direct Symbolic Step Constructors -/

/-- Direct symbolic step constructor for pure instructions (`SepWP.step_pure_setPC`,
    `SepWP.step_pure_setMem_setPC`, `SepWP.step_pure`), parameterized over a state-threaded
    expression simplifier `simpLhs : Expr → σ → MetaM ((Expr × Expr) × σ)`. -/
def symStepPureInsn? {σ : Type}
    (simpLhs : Expr → σ → MetaM ((Expr × Expr) × σ))
    (pcExpr instExpr fetchPrf : Expr) (st : σ) : TacticM (Option (MVarId × σ)) := do
  let g ← getMainGoal
  tryTacticCatchRuntime do
    g.withContext do
      let ty := (← instantiateMVars (← g.getType)).consumeMData
      if !ty.isAppOfArity ``SepWP 6 then throwError "not SepWP"
      let prog := ty.getArg! 0
      let targetPc := ty.getArg! 1
      let s := ty.getArg! 2
      let P := ty.getArg! 3
      let post := ty.getArg! 4
      let oom := ty.getArg! 5
      let some hrun ← proveStatusRunningExpr? s | throwError "no status"
      let isSetPC := s.isAppOfArity ``State.setPC 2 && s.getArg! 1 == pcExpr
      let isSetMemSetPC := s.isAppOfArity ``State.setMem 2 &&
        (s.getArg! 0).isAppOfArity ``State.setPC 2 && (s.getArg! 0).getArg! 1 == pcExpr
      let execIn := if isSetPC || isSetMemSetPC then s else mkApp2 (mkConst ``State.setPC) s pcExpr
      let execLhs := mkApp2 (mkConst ``execInst) instExpr execIn
      let ((s', hexec), st') ← simpLhs execLhs st
      let nextTy := mkApp6 (mkConst ``SepWP) prog targetPc s' P post oom
      if isSetPC then
        let s0 := s.getArg! 0
        let some hmem ← proveMemEqExpr? (mkApp (mkConst ``State.mem) s') (mkApp (mkConst ``State.mem) s0)
          | throwError "no mem"
        let gNext ← mkFreshExprMVar nextTy
        let prf := mkAppN (mkConst ``SepWP.step_pure_setPC)
          #[prog, targetPc, s0, s', P, post, oom, pcExpr, instExpr, hrun, fetchPrf, hexec, hmem, gNext]
        g.assign prf
        return (gNext.mvarId!, st')
      if isSetMemSetPC then
        let s0 := (s.getArg! 0).getArg! 0
        let m := s.getArg! 1
        let some hmem ← proveMemEqExpr? (mkApp (mkConst ``State.mem) s') m
          | throwError "no mem"
        let gNext ← mkFreshExprMVar nextTy
        let prf := mkAppN (mkConst ``SepWP.step_pure_setMem_setPC)
          #[prog, targetPc, s0, s', P, post, oom, pcExpr, m, instExpr, hrun, fetchPrf, hexec, hmem, gNext]
        g.assign prf
        return (gNext.mvarId!, st')
      let some hpc ← provePcEqOrLocal? s pcExpr | throwError "no pc"
      let some hmem ← proveMemEqExpr? (mkApp (mkConst ``State.mem) s') (mkApp (mkConst ``State.mem) s)
        | throwError "no mem"
      let gNext ← mkFreshExprMVar nextTy
      let prf := mkAppN (mkConst ``SepWP.step_pure)
        #[prog, targetPc, s, s', P, post, oom, pcExpr, instExpr, hpc, hrun, fetchPrf, hexec, hmem, gNext]
      g.assign prf
      return (gNext.mvarId!, st')

/-- Direct symbolic step constructor for 64-bit `LDR Xt, [addr]` (`SepWP.step_ldr64`),
    parameterized over a state-threaded expression simplifier `simpLhs`. -/
def symStepLdr64Insn? {σ : Type}
    (simpLhs : Expr → σ → MetaM ((Expr × Expr) × σ))
    (pcExpr rt addr fetchPrf : Expr) (st : σ) : TacticM (Option (MVarId × σ)) := do
  let g ← getMainGoal
  tryTacticCatchRuntime do
    g.withContext do
      let ty := (← instantiateMVars (← g.getType)).consumeMData
      let prog := ty.getArg! 0
      let targetPc := ty.getArg! 1
      let s := ty.getArg! 2
      let P := ty.getArg! 3
      let post := ty.getArg! 4
      let oom := ty.getArg! 5
      let some hpc ← provePcEqOrLocal? s pcExpr | throwError "no pc"
      let some hrun ← proveStatusRunningExpr? s | throwError "no status"
      let amExpr := addr
      let spLhs := mkApp2 (mkConst ``checkAddrSPAligned) s amExpr
      let bTrue := mkConst ``Bool.true
      let spGoalTy ← mkEq spLhs bTrue
      let some hsp ← proveCheckAddrSPAligned? spGoalTy spLhs bTrue | throwError "no sp"
      let addrLhs := mkApp2 (mkConst ``evalAddrMode) s amExpr
      let ((addrRhs, haddr), st1) ← simpLhs addrLhs st
      unless addrRhs.isAppOfArity ``Prod.mk 4 do throwError "evalAddrMode not a pair"
      let ea := addrRhs.getArg! 2
      let wb := addrRhs.getArg! 3
      let (v, hload) ← proveSepLoad ``Arm64.pointsTo64 ea P
      let rtReg := rt
      let pcPlus4 ← mkAppM ``HAdd.hAdd #[pcExpr, toExpr (4#64)]
      let execLhs := mkApp2 (mkConst ``State.setPC)
        (mkApp3 (mkConst ``State.writeReg64)
          (mkApp2 (mkConst ``applyWriteback) s wb) rtReg v)
        pcPlus4
      let ((s', hexec), st2) ← simpLhs execLhs st1
      let nextTy := mkApp6 (mkConst ``SepWP) prog targetPc s' P post oom
      let gNext ← mkFreshExprMVar nextTy
      let prf := mkAppN (mkConst ``SepWP.step_ldr64)
        #[prog, targetPc, s, s', P, post, oom, pcExpr, rt, addr, ea, wb, v,
          hpc, hrun, fetchPrf, hsp, haddr, hload, hexec, gNext]
      g.assign prf
      return (gNext.mvarId!, st2)

/-- Direct symbolic step constructor for 64-bit `STR Xt, [addr]` (`SepWP.step_str64`),
    parameterized over a state-threaded expression simplifier `simpLhs`. -/
def symStepStr64Insn? {σ : Type}
    (simpLhs : Expr → σ → MetaM ((Expr × Expr) × σ))
    (pcExpr rt addr fetchPrf : Expr) (st : σ) : TacticM (Option (MVarId × σ)) := do
  let g ← getMainGoal
  let mId ← freshIdent `m
  tryTacticCatchRuntime do
    g.withContext do
      let ty := (← instantiateMVars (← g.getType)).consumeMData
      let prog := ty.getArg! 0
      let targetPc := ty.getArg! 1
      let s := ty.getArg! 2
      let P := ty.getArg! 3
      let post := ty.getArg! 4
      let oom := ty.getArg! 5
      let some hpc ← provePcEqOrLocal? s pcExpr | throwError "no pc"
      let some hrun ← proveStatusRunningExpr? s | throwError "no status"
      let amExpr := addr
      let spLhs := mkApp2 (mkConst ``checkAddrSPAligned) s amExpr
      let bTrue := mkConst ``Bool.true
      let spGoalTy ← mkEq spLhs bTrue
      let some hsp ← proveCheckAddrSPAligned? spGoalTy spLhs bTrue | throwError "no sp"
      let addrLhs := mkApp2 (mkConst ``evalAddrMode) s amExpr
      let ((addrRhs, haddr), st1) ← simpLhs addrLhs st
      unless addrRhs.isAppOfArity ``Prod.mk 4 do throwError "evalAddrMode not a pair"
      let ea := addrRhs.getArg! 2
      let wb := addrRhs.getArg! 3
      let rtReg := rt
      let valLhs := mkApp2 (mkConst ``State.readReg64) s rtReg
      let ((val, hval), st2) ← simpLhs valLhs st1
      let (P', hstore) ← proveSepStore ``Arm64.pointsTo64 ea val P
      let pcPlus4 ← mkAppM ``HAdd.hAdd #[pcExpr, toExpr (4#64)]
      let execLhs := mkApp2 (mkConst ``State.setPC) (mkApp2 (mkConst ``applyWriteback) s wb) pcPlus4
      let ((s', hexec), st3) ← simpLhs execLhs st2
      let memTy := mkConst ``Arm64.Memory
      let forallTy := Lean.mkForall mId.getId .default memTy
        (mkApp6 (mkConst ``SepWP) prog targetPc
          (mkApp2 (mkConst ``State.setMem) s' (mkBVar 0)) P' post oom)
      let gForall ← mkFreshExprMVar forallTy
      let prf := mkAppN (mkConst ``SepWP.step_str64)
        #[prog, targetPc, s, s', P, P', post, oom, pcExpr, rt, addr, ea, wb, val,
          hpc, hrun, fetchPrf, hsp, haddr, hval, hstore, hexec, gForall]
      g.assign prf
      let (mFVar, gIntro) ← gForall.mvarId!.intro mId.getId
      if s'.isAppOfArity ``State.setMem 2 then
        let sInner := s'.getArg! 0
        let mOld := s'.getArg! 1
        if !sInner.isAppOfArity ``State.setMem 2 then
          let mExpr := mkFVar mFVar
          let sOuter := mkApp2 (mkConst ``State.setMem) s' mExpr
          let sClean := mkApp2 (mkConst ``State.setMem) sInner mExpr
          let hs := mkApp3 (mkConst ``State.setMem_setMem) sInner mOld mExpr
          let cleanTy := mkApp6 (mkConst ``SepWP) prog targetPc sClean P' post oom
          let gClean ← gIntro.withContext (mkFreshExprMVar cleanTy)
          let congrPrf := mkAppN (mkConst ``SepWP.congr_state)
            #[prog, targetPc, sOuter, sClean, P', post, oom, hs, gClean]
          gIntro.assign congrPrf
          return (gClean.mvarId!, st3)
      return (gIntro, st3)

/-- Persistent environment extension storing the pre-compiled `Sym.Simp.Theorems` in `SymWP.olean`
    so downstream modules map the discrimination tree directly from `.olean` memory with `m_rc = 0`. -/
initialize symWPTheoremsExt : SimplePersistentEnvExtension Sym.Simp.Theorems (Option Sym.Simp.Theorems) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun as => Id.run do
      for a in as do
        for thms in a do
          return some thms
      return none
    addEntryFn := fun _ thms => some thms
  }

end

end ProofLib

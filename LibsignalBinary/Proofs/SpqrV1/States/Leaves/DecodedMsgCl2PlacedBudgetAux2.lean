/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.SpqrV1.GF.GfCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.PolyPart1CodeSym
public import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangeComplete.Defs
public meta import Lean -- shake: keep
public meta import ProofLib.SepLogic.WP -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.SpqrV1.GF.DivImpl
import LibsignalBinary.Proofs.SpqrV1.GF.Mul2U16
import LibsignalBinary.Proofs.SpqrV1.GF.UnacceleratedMul
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangeComplete.Proof
import ProofLib.SepLogic.WPp

/-!
# `<spqr::encoding::polynomial::Poly>::lagrange_interpolate_complete` (Block `373`): `VmPreserved` Relocatable Proof

Verifies `lagrangeComplete_placed_vmPreserved_ok` on Block `373` under `[LibsignalPlacement]`,
discharging `unaccelerated::mul` (Block `384`), `mul2_u16` (Block `381`), and `GF16::div_impl`
(Block `331`) with `VmPreserved` threaded across `STR`/`STP` segments.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.States.Leaves.DecodedMsgCl2PlacedBudgetAux2

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open scoped CryptoVerification.CodeLayout
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkLib_eq_331 blkLib_eq_373 blkLib_eq_381
   blkPC_331 blkPC_331_rebase_fetch_0x1c blkPC_373 blkPC_373_rebase_fetch_0x164
   blkPC_373_rebase_fetch_0x1f0 blkPC_373_rebase_fetch_0x6c blkPC_381
   blkPC_381_rebase_fetch_0x1c blkPC_384 blkPl_331 blkPl_373 blkPl_381 blkPl_384
   ls_subroutine_ok_cl_of_block ls_subroutine_ok_cl_of_plain lscall_blk lscall_blk_cl
   lsmpl lsρ sepWP_seq_lscl withLsCl withLsCodeLoaded withMemEq)
open CryptoVerification.LibsignalSpqrV1
  (GF16 Poly Pt mul2U16 tokenName tokenStorageName)
open CryptoVerification.SpqrV1.GF.DivImpl
  (divImplStack stackAt_112_merge stackAt_112_split)
open CryptoVerification.SpqrV1.GF.Mul2U16
  (aligned_tokenOnce_placed stackAt_64_merge stackAt_64_split step_ldar32
   tokenInitPlacedAt tokenInitPlacedAt_fold zeroExtend_16_truncate_32_64)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
  (polyMul_asm_eq polyReduce_asm_eq reduceTablePlacedAt reduceTablePlacedAt_focus16
   uxtw1_idx1_eq uxtw1_idx2_eq)
open CryptoVerification.SpqrV1.Poly
  (gf16SliceAt ptSliceAt)
open CryptoVerification.SpqrV1.Poly.LagrangeComplete
  (bv_sub_one_succ cmp32_zext16_eq_zero cmp32_zext16_ne_zero denomStep divLoopPure
   divLoop_step_eq gf16SliceAt_focus gf16SliceAt_focus_assoc gf16SliceAt_update_assoc
   gf16SliceAt_update_one_assoc gf16_beq_iff lagrangeCompletePlacedSpec
   lagrangeCompletePure lagrangeDenominator_eq_foldl lsl_one_eq_two_mul lsl_two_eq_four_mul
   perm_denom_pre perm_div_pre ptSliceAt_focus_x ptSliceAt_focus_y ptr_add_four_step
   ptr_sub_four_mul_ne_zero ptr_sub_two_step stackAt_lagrangeComplete_merge
   stackAt_lagrangeComplete_split truncate16_zext64)
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm] polyReduce_asm_eq
attribute [local arm64_norm, local wp_norm]
  CryptoVerification.blkPl_384_ρ CryptoVerification.blkPl_381_ρ
  CryptoVerification.blkPl_331_ρ CryptoVerification.blkPl_373_ρ

abbrev addVmPreserved {α : Type} (spec : Spec α) : Spec α :=
  { spec with post := fun x s0 sf => ⌜VmPreserved s0 sf⌝ ∗ spec.post x s0 sf }

/-! ## 1. `State` Projection & `TraceVm` Equivalence Normalizers -/

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem pc_setMem_pre (s : State) (m : Memory) : (s.setMem m).pc = s.pc := by
  cases s; rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem status_setMem_pre (s : State) (m : Memory) : (s.setMem m).status = s.status := by
  cases s; rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem pstate_setMem_pre (s : State) (m : Memory) : (s.setMem m).pstate = s.pstate := by
  cases s; rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem trace_setMem_pre (s : State) (m : Memory) : (s.setMem m).trace = s.trace := by
  cases s; rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem tpidrEl0_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).tpidrEl0 = s.tpidrEl0 := by
  cases s; rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem calleeSavedVRegs_setMem_pre (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := by
  cases s; rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setMem_pre (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by
  cases s; rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem spAligned_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).spAligned = s.spAligned := by
  cases s; rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem checkRegSPAligned_setMem_pre (s : State) (m : Memory) (r : Reg) :
    checkRegSPAligned (s.setMem m) r = checkRegSPAligned s r := by
  cases s; rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by
  cases s; rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem readReg32_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg32 r = s.readReg32 r := by
  cases s; rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem readReg_setMem_pre (s : State) (m : Memory) (w : RegWidth) (r : Reg) :
    (s.setMem m).readReg w r = s.readReg w r := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r := State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg32_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg32_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg_setPC_pre (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory)
    (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by cases s; rfl

private structure TraceVm (s0 sf : State) : Prop where
  trace_eq : sf.trace = s0.trace
  vm : VmPreserved s0 sf

private theorem TraceVm.refl (s : State) : TraceVm s s :=
  ⟨rfl, VmPreserved.refl s⟩

private theorem TraceVm.symm {s₁ s₂ : State} (h : TraceVm s₁ s₂) : TraceVm s₂ s₁ :=
  ⟨h.trace_eq.symm, h.vm.symm⟩

private theorem TraceVm.trans {s₀ s₁ s₂ : State} (h01 : TraceVm s₀ s₁) (h12 : TraceVm s₁ s₂) :
    TraceVm s₀ s₂ :=
  ⟨h12.trace_eq.trans h01.trace_eq, h01.vm.trans h12.vm⟩

private theorem traceVm_of_nsp {s0 sf : State}
    (hnsp : ProofLib.NonSyscallPreserved s0 sf) (htr : sf.trace = s0.trace)
    (htp : sf.tpidrEl0 = s0.tpidrEl0) : TraceVm s0 sf :=
  ⟨htr, hnsp.toVmPreserved htp⟩

private theorem traceVm_right_congr {s s₁ s₂ : State} (h : TraceVm s₁ s₂) :
    TraceVm s s₂ ↔ TraceVm s s₁ :=
  ⟨fun h02 => h02.trans h.symm, fun h01 => h01.trans h⟩

private theorem traceVm_left_congr {s₁ s₂ s : State} (h : TraceVm s₁ s₂) :
    TraceVm s₂ s ↔ TraceVm s₁ s :=
  ⟨fun h2 => h.trans h2, fun h1 => h.symm.trans h1⟩

@[local simp, local arm64_norm, local wp_norm]
private theorem traceVm_refl_iff (s : State) : TraceVm s s ↔ True :=
  ⟨fun _ => trivial, fun _ => TraceVm.refl s⟩

private theorem traceVm_step_setPC (s : State) (pc : BitVec 64) : TraceVm s (s.setPC pc) :=
  ⟨by cases s; rfl, by simp [arm64_norm, wp_norm]⟩

private theorem traceVm_step_advancePC (s : State) : TraceVm s s.advancePC :=
  ⟨by cases s; rfl, by simp [arm64_norm, wp_norm]⟩

private theorem traceVm_step_setPState (s : State) (ps : PState) : TraceVm s (s.setPState ps) :=
  ⟨by cases s; rfl, by simp [arm64_norm, wp_norm]⟩

private theorem traceVm_step_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    TraceVm s (s.writeReg64 r v) :=
  ⟨by cases s; rfl, by simp [arm64_norm, wp_norm]⟩

private theorem traceVm_step_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    TraceVm s (s.writeReg32 r v) :=
  ⟨by cases s; rfl, by simp [arm64_norm, wp_norm]⟩

private theorem traceVm_step_writeReg (s : State) (w : RegWidth) (r : Reg) (v : BitVec 64) :
    TraceVm s (s.writeReg w r v) :=
  ⟨by cases w <;> cases s <;> rfl, by simp [arm64_norm, wp_norm]⟩

private theorem traceVm_step_applyWriteback (s : State) (wb : Option (Reg × BitVec 64)) :
    TraceVm s (applyWriteback s wb) :=
  ⟨by cases wb <;> cases s <;> rfl,
   by rcases wb with _ | ⟨base, newBase⟩ <;> simp [applyWriteback, arm64_norm, wp_norm]⟩

private theorem traceVm_step_stepExclLoop (s : State) : TraceVm s s.stepExclLoop :=
  ⟨by cases s; rfl, by simp [arm64_norm, wp_norm]⟩

@[local simp, local arm64_norm, local wp_norm]
private theorem traceVm_setPC_right (s s' : State) (pc : BitVec 64) :
    TraceVm s (s'.setPC pc) ↔ TraceVm s s' := traceVm_right_congr (traceVm_step_setPC s' pc)
@[local simp, local arm64_norm, local wp_norm]
private theorem traceVm_setPC_left (s' s : State) (pc : BitVec 64) :
    TraceVm (s'.setPC pc) s ↔ TraceVm s' s := traceVm_left_congr (traceVm_step_setPC s' pc)

@[local simp, local arm64_norm, local wp_norm]
private theorem traceVm_advancePC_right (s s' : State) :
    TraceVm s s'.advancePC ↔ TraceVm s s' := traceVm_right_congr (traceVm_step_advancePC s')
@[local simp, local arm64_norm, local wp_norm]
private theorem traceVm_advancePC_left (s' s : State) :
    TraceVm s'.advancePC s ↔ TraceVm s' s := traceVm_left_congr (traceVm_step_advancePC s')

@[local simp, local arm64_norm, local wp_norm]
private theorem traceVm_setPState_right (s s' : State) (ps : PState) :
    TraceVm s (s'.setPState ps) ↔ TraceVm s s' := traceVm_right_congr (traceVm_step_setPState s' ps)
@[local simp, local arm64_norm, local wp_norm]
private theorem traceVm_setPState_left (s' s : State) (ps : PState) :
    TraceVm (s'.setPState ps) s ↔ TraceVm s' s := traceVm_left_congr (traceVm_step_setPState s' ps)

@[local simp, local arm64_norm, local wp_norm]
private theorem traceVm_writeReg64_right (s s' : State) (r : Reg) (v : BitVec 64) :
    TraceVm s (s'.writeReg64 r v) ↔ TraceVm s s' :=
  traceVm_right_congr (traceVm_step_writeReg64 s' r v)
@[local simp, local arm64_norm, local wp_norm]
private theorem traceVm_writeReg64_left (s' s : State) (r : Reg) (v : BitVec 64) :
    TraceVm (s'.writeReg64 r v) s ↔ TraceVm s' s :=
  traceVm_left_congr (traceVm_step_writeReg64 s' r v)

@[local simp, local arm64_norm, local wp_norm]
private theorem traceVm_writeReg32_right (s s' : State) (r : Reg) (v : BitVec 32) :
    TraceVm s (s'.writeReg32 r v) ↔ TraceVm s s' :=
  traceVm_right_congr (traceVm_step_writeReg32 s' r v)
@[local simp, local arm64_norm, local wp_norm]
private theorem traceVm_writeReg32_left (s' s : State) (r : Reg) (v : BitVec 32) :
    TraceVm (s'.writeReg32 r v) s ↔ TraceVm s' s :=
  traceVm_left_congr (traceVm_step_writeReg32 s' r v)

@[local simp, local arm64_norm, local wp_norm]
private theorem traceVm_writeReg_right (s s' : State) (w : RegWidth) (r : Reg) (v : BitVec 64) :
    TraceVm s (s'.writeReg w r v) ↔ TraceVm s s' :=
  traceVm_right_congr (traceVm_step_writeReg s' w r v)
@[local simp, local arm64_norm, local wp_norm]
private theorem traceVm_writeReg_left (s' s : State) (w : RegWidth) (r : Reg) (v : BitVec 64) :
    TraceVm (s'.writeReg w r v) s ↔ TraceVm s' s :=
  traceVm_left_congr (traceVm_step_writeReg s' w r v)

@[local simp, local arm64_norm, local wp_norm]
private theorem traceVm_applyWriteback_right (s s' : State) (wb : Option (Reg × BitVec 64)) :
    TraceVm s (applyWriteback s' wb) ↔ TraceVm s s' :=
  traceVm_right_congr (traceVm_step_applyWriteback s' wb)
@[local simp, local arm64_norm, local wp_norm]
private theorem traceVm_applyWriteback_left (s' s : State) (wb : Option (Reg × BitVec 64)) :
    TraceVm (applyWriteback s' wb) s ↔ TraceVm s' s :=
  traceVm_left_congr (traceVm_step_applyWriteback s' wb)

@[local simp, local arm64_norm, local wp_norm]
private theorem traceVm_stepExclLoop_right (s s' : State) :
    TraceVm s s'.stepExclLoop ↔ TraceVm s s' := traceVm_right_congr (traceVm_step_stepExclLoop s')
@[local simp, local arm64_norm, local wp_norm]
private theorem traceVm_stepExclLoop_left (s' s : State) :
    TraceVm s'.stepExclLoop s ↔ TraceVm s' s := traceVm_left_congr (traceVm_step_stepExclLoop s')

private theorem setMem_setMem_comm (s : State) (m₁ m₂ : Memory) :
    (s.setMem m₁).setMem m₂ = s.setMem m₂ := by cases s; rfl
private theorem setPC_setMem_comm (s : State) (pc : BitVec 64) (m : Memory) :
    (s.setPC pc).setMem m = (s.setMem m).setPC pc := by cases s; rfl
private theorem advancePC_setMem_comm (s : State) (m : Memory) :
    s.advancePC.setMem m = (s.setMem m).advancePC := by cases s; rfl
private theorem setPState_setMem_comm (s : State) (ps : PState) (m : Memory) :
    (s.setPState ps).setMem m = (s.setMem m).setPState ps := by cases s; rfl
private theorem writeReg64_setMem_comm (s : State) (r : Reg) (v : BitVec 64) (m : Memory) :
    (s.writeReg64 r v).setMem m = (s.setMem m).writeReg64 r v := by cases s; cases r <;> rfl
private theorem writeReg32_setMem_comm (s : State) (r : Reg) (v : BitVec 32) (m : Memory) :
    (s.writeReg32 r v).setMem m = (s.setMem m).writeReg32 r v := by cases s; cases r <;> rfl
private theorem writeReg_setMem_comm (s : State) (w : RegWidth) (r : Reg) (v : BitVec 64) (m : Memory) :
    (s.writeReg w r v).setMem m = (s.setMem m).writeReg w r v := by cases w <;> cases s <;> cases r <;> rfl
private theorem applyWriteback_setMem_comm (s : State) (wb : Option (Reg × BitVec 64)) (m : Memory) :
    (applyWriteback s wb).setMem m = applyWriteback (s.setMem m) wb := by
  rcases wb with _ | ⟨b, v⟩
  · rfl
  · simp only [applyWriteback, writeReg64_setMem_comm]
private theorem stepExclLoop_setMem_comm (s : State) (m : Memory) :
    s.stepExclLoop.setMem m = (s.setMem m).stepExclLoop := by cases s; rfl

open Lean Meta Elab Tactic in
local elab "solve_traceVm" : tactic => do
  let g ← getMainGoal
  let hs ← g.withContext do
    let mut acc : Array (TSyntax `ident) := #[]
    for decl in ← getLCtx do
      if !decl.isImplementationDetail && !decl.userName.hasMacroScopes then
        let ty := (← instantiateMVars decl.type).consumeMData
        if ty.isAppOfArity ``TraceVm 2 then
          acc := acc.push (mkIdent decl.userName)
    return acc
  for h in hs do
    evalTactic (← `(tactic|
      try simp only [traceVm_refl_iff,
        setMem_setMem_comm, setPC_setMem_comm, advancePC_setMem_comm, setPState_setMem_comm,
        writeReg64_setMem_comm, writeReg32_setMem_comm, writeReg_setMem_comm,
        applyWriteback_setMem_comm, stepExclLoop_setMem_comm,
        traceVm_setPC_right, traceVm_setPC_left,
        traceVm_advancePC_right, traceVm_advancePC_left,
        traceVm_setPState_right, traceVm_setPState_left,
        traceVm_writeReg64_right, traceVm_writeReg64_left,
        traceVm_writeReg32_right, traceVm_writeReg32_left,
        traceVm_writeReg_right, traceVm_writeReg_left,
        traceVm_applyWriteback_right, traceVm_applyWriteback_left,
        traceVm_stepExclLoop_right, traceVm_stepExclLoop_left] at $h:ident))
  evalTactic (← `(tactic| (
    try simp only [traceVm_refl_iff,
      setMem_setMem_comm, setPC_setMem_comm, advancePC_setMem_comm, setPState_setMem_comm,
      writeReg64_setMem_comm, writeReg32_setMem_comm, writeReg_setMem_comm,
      applyWriteback_setMem_comm, stepExclLoop_setMem_comm,
      traceVm_setPC_right, traceVm_setPC_left,
      traceVm_advancePC_right, traceVm_advancePC_left,
      traceVm_setPState_right, traceVm_setPState_left,
      traceVm_writeReg64_right, traceVm_writeReg64_left,
      traceVm_writeReg32_right, traceVm_writeReg32_left,
      traceVm_writeReg_right, traceVm_writeReg_left,
      traceVm_applyWriteback_right, traceVm_applyWriteback_left,
      traceVm_stepExclLoop_right, traceVm_stepExclLoop_left]
    try trivial
    repeat (first | exact TraceVm.refl _ | assumption | refine TraceVm.trans (by assumption) ?_)
    try trivial)))

/-! ## 2. `TraceVm`-Strengthened Callees (`unaccelerated::mul`, `mul2_u16`, `GF16::div_impl`) -/

private def unacceleratedMulTvSpec [LibsignalPlacement] : Spec (BitVec 16 × BitVec 16) where
  pre := fun (a, b_arg) s =>
    ⌜BitVec.truncate 16 (s.readReg64 .x0) = a ∧
      BitVec.truncate 16 (s.readReg64 .x1) = b_arg⌝ ∗
      reduceTablePlacedAt
  post := fun (a, b_arg) s0 sf =>
    ⌜BitVec.truncate 16 (sf.readReg64 .x0) = CryptoVerification.LibsignalSpqrV1.unaccelerated.mul a b_arg ∧
      TraceVm s0 sf⌝ ∗
      reduceTablePlacedAt

private theorem unacceleratedMul_vm_placed_ok [LibsignalPlacement]
    (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_384).rebase (blkPl_384).base H) (blkPl_384).base
      unacceleratedMulTvSpec := by
  simp only [unacceleratedMulTvSpec]
  wp_init ab s0
  wp_steps 52
  rw [polyMul_asm_eq]
  wp_steps 1
  wp_conv_pre =>
    rw [reduceTablePlacedAt_focus16 (BitVec.truncate 8 (CryptoVerification.LibsignalSpqrV1.unaccelerated.polyMul ab.1 ab.2 >>> 24)),
        uxtw1_idx1_eq (CryptoVerification.LibsignalSpqrV1.unaccelerated.polyMul ab.1 ab.2)]
  wp_steps 3
  wp_conv_pre =>
    rw [← uxtw1_idx1_eq (CryptoVerification.LibsignalSpqrV1.unaccelerated.polyMul ab.1 ab.2),
        ← reduceTablePlacedAt_focus16 (BitVec.truncate 8 (CryptoVerification.LibsignalSpqrV1.unaccelerated.polyMul ab.1 ab.2 >>> 24)),
        reduceTablePlacedAt_focus16
          (BitVec.truncate 8
            ((CryptoVerification.LibsignalSpqrV1.unaccelerated.polyMul ab.1 ab.2 ^^^
                BitVec.zeroExtend 32
                    (CryptoVerification.LibsignalSpqrV1.reduce.reduceByteEntry (BitVec.truncate 8 (CryptoVerification.LibsignalSpqrV1.unaccelerated.polyMul ab.1 ab.2 >>> 24))) <<<
                  8) >>>
              16)),
        uxtw1_idx2_eq]
  wp_steps 3
  wp_conv_pre =>
    rw [← uxtw1_idx2_eq,
        ← reduceTablePlacedAt_focus16
          (BitVec.truncate 8
            ((CryptoVerification.LibsignalSpqrV1.unaccelerated.polyMul ab.1 ab.2 ^^^
                BitVec.zeroExtend 32
                    (CryptoVerification.LibsignalSpqrV1.reduce.reduceByteEntry (BitVec.truncate 8 (CryptoVerification.LibsignalSpqrV1.unaccelerated.polyMul ab.1 ab.2 >>> 24))) <<<
                  8) >>>
              16))]
  wp_done

attribute [local wp_norm] zeroExtend_16_truncate_32_64

@[local wp_norm]
private theorem mul2U16_fst (a b1 b2 : BitVec 16) :
    (mul2U16 a b1 b2).1 = CryptoVerification.LibsignalSpqrV1.unaccelerated.mul a b1 := rfl

@[local wp_norm]
private theorem mul2U16_snd (a b1 b2 : BitVec 16) :
    (mul2U16 a b1 b2).2 = CryptoVerification.LibsignalSpqrV1.unaccelerated.mul a b2 := rfl

private def mul2U16TvSpec [LibsignalPlacement] :
    Spec (BitVec 16 × BitVec 16 × BitVec 16) where
  pre := fun (a, b1, b2) s =>
    ⌜BitVec.truncate 16 (s.readReg64 .x0) = a ∧
      BitVec.truncate 16 (s.readReg64 .x1) = b1 ∧
      BitVec.truncate 16 (s.readReg64 .x2) = b2⌝ ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      stackAt s.sp 0x40
  post := fun (a, b1, b2) s0 sf =>
    ⌜BitVec.truncate 16 (sf.readReg64 .x0) = (mul2U16 a b1 b2).1 ∧
      BitVec.truncate 16 (sf.readReg64 .x1) = (mul2U16 a b1 b2).2 ∧
      TraceVm s0 sf⌝ ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      stackAt s0.sp 0x40

private theorem mul2U16_vm_placed_ok [LibsignalPlacement]
    (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_381).rebase (blkPl_381).base H) (blkPl_381).base
      (withLsCodeLoaded lsmpl mul2U16TvSpec) := by
  have hmul0 : subroutine_ok ((blkPC_384).rebase (blkPl_384).base H) (lsmpl.base 384)
      unacceleratedMulTvSpec :=
    unacceleratedMul_vm_placed_ok H
  have hmul := ls_subroutine_ok_cl_of_plain
    (callerProg := (blkPC_381).rebase (blkPl_381).base H) hmul0
  simp only [withLsCl, unacceleratedMulTvSpec] at hmul
  simp only [withLsCodeLoaded, mul2U16TvSpec]
  wp_init args s0
  have halign := aligned_tokenOnce_placed
  wp_simp_pre [stackAt_64_split, tokenInitPlacedAt]
  wp_pull_exists
  apply sepWP_seq_lscl h (mid := (blkPl_381).base + 236#64)
  apply sepWP_seg_ls_vm
    (Q := (blkPC_381).rebase (blkPl_381).base (hooksException H))
    blkLib_eq_381 (mid := (blkPl_381).base + 236#64)
  intro m_strip
  wp_steps 6
  apply step_ldar32
  · wp_norm_lhs
  · wp_norm_lhs
  · exact blkPC_381_rebase_fetch_0x1c (blkPl_381).base (hooksException H)
  · wp_norm_lhs
  · wp_norm_lhs
  · exact halign
  · wp_sep_access
  · wp_norm_lhs
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun m_real hnsp => ?_
  have htv0 := traceVm_of_nsp hnsp (by simp [arm64_norm, wp_norm]) (by simp [arm64_norm, wp_norm])
  apply SepWP.done
  · wp_norm_lhs
  · wp_norm_lhs
  intro hcl1
  wp_call hmul
  wp_steps
  wp_call hmul
  wp_steps
  apply SepWP.fold
    (stackAt_64_merge s0.sp
      (s0.readReg64 (Reg.gpr 29#5))
      (s0.readReg64 (Reg.gpr 30#5))
      (s0.readReg64 (Reg.gpr 21#5))
      (s0.readReg64 (Reg.gpr 20#5))
      (s0.readReg64 (Reg.gpr 19#5)))
    (by sep_focus)
  apply SepWP.fold tokenInitPlacedAt_fold (by sep_focus)
  have htv_final : TraceVm s0 sf_1 := by solve_traceVm
  wp_done

private def divStep (other self : BitVec 16) : Nat → BitVec 16 × BitVec 16
  | 0 => (CryptoVerification.LibsignalSpqrV1.unaccelerated.mul other other, self)
  | k + 1 =>
    let p := divStep other self k
    mul2U16 p.1 p.1 p.2

@[local wp_norm]
private theorem divStep_one (other self : BitVec 16) :
    mul2U16 (CryptoVerification.LibsignalSpqrV1.unaccelerated.mul other other) (CryptoVerification.LibsignalSpqrV1.unaccelerated.mul other other) self =
      divStep other self 1 := rfl

@[local wp_norm]
private theorem divStep_succ (other self : BitVec 16) (k : Nat) :
    mul2U16 (divStep other self k).1 (divStep other self k).1 (divStep other self k).2 =
      divStep other self (k + 1) := rfl

@[local wp_norm]
private theorem divStep_15_snd (self other : GF16) :
    (divStep other.value self.value 15).2 = (GF16.divImpl self other).value := rfl

private def divImplTvSpec [LibsignalPlacement] : Spec (BitVec 64 × BitVec 64 × GF16 × GF16) where
  pre := fun (p_self, p_other, self, other) s =>
    ⌜s.readReg64 .x0 = p_self ∧
      s.readReg64 .x1 = p_other⌝ ∗
      (p_self ↦₁₆ self.value) ∗
      (p_other ↦₁₆ other.value) ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      stackAt s.sp divImplStack
  post := fun (p_self, p_other, self, other) s0 sf =>
    ⌜BitVec.truncate 16 (sf.readReg64 .x0) = (GF16.divImpl self other).value ∧
      TraceVm s0 sf⌝ ∗
      (p_self ↦₁₆ self.value) ∗
      (p_other ↦₁₆ other.value) ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      stackAt s0.sp divImplStack

set_option maxHeartbeats 1600000 in
private theorem divImpl_vm_placed_ok [LibsignalPlacement]
    (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_331).rebase (blkPl_331).base H) (blkPl_331).base
      (withLsCodeLoaded lsmpl divImplTvSpec) := by
  have hmul0 : subroutine_ok ((blkPC_384).rebase (blkPl_384).base H) (lsmpl.base 384)
      unacceleratedMulTvSpec :=
    unacceleratedMul_vm_placed_ok H
  have hmul := ls_subroutine_ok_cl_of_plain
    (callerProg := (blkPC_331).rebase (blkPl_331).base H) hmul0
  have hmul20 : subroutine_ok ((blkPC_381).rebase (blkPl_381).base H) (lsmpl.base 381)
      (withLsCodeLoaded lsmpl mul2U16TvSpec) :=
    mul2U16_vm_placed_ok H
  have hmul2 := ls_subroutine_ok_cl_of_block
    (callerProg := (blkPC_331).rebase (blkPl_331).base H) hmul20
  simp only [withLsCl, unacceleratedMulTvSpec] at hmul
  simp only [withLsCl, mul2U16TvSpec] at hmul2
  simp only [withLsCodeLoaded, divImplTvSpec]
  wp_init args s0
  have halign := aligned_tokenOnce_placed
  wp_simp_pre [stackAt_112_split, tokenInitPlacedAt]
  wp_pull_exists
  apply sepWP_seq_lscl h (mid := (blkPl_331).base + 184#64)
  apply sepWP_seg_ls_vm
    (Q := (blkPC_331).rebase (blkPl_331).base (hooksException H))
    blkLib_eq_331 (mid := (blkPl_331).base + 184#64)
  intro m_strip
  wp_steps 7
  apply step_ldar32
  · wp_norm_lhs
  · wp_norm_lhs
  · exact blkPC_331_rebase_fetch_0x1c (blkPl_331).base (hooksException H)
  · wp_norm_lhs
  · wp_norm_lhs
  · exact halign
  · wp_sep_access
  · wp_norm_lhs
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun m_real hnsp => ?_
  have htv0 := traceVm_of_nsp hnsp (by simp [arm64_norm, wp_norm]) (by simp [arm64_norm, wp_norm])
  apply SepWP.done
  · wp_norm_lhs
  · wp_norm_lhs
  intro hcl1
  apply SepWP.fold tokenInitPlacedAt_fold (by sep_focus)
  wp_call hmul
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2
  wp_steps
  wp_call hmul2
  wp_steps
  refine SepWP.fold
    (stackAt_112_merge s0.sp _
      (s0.readReg64 (Reg.gpr 29#5))
      (s0.readReg64 (Reg.gpr 30#5))
      (s0.readReg64 (Reg.gpr 20#5))
      (s0.readReg64 (Reg.gpr 19#5))
      ?_)
    (by sep_focus)
    ?_
  · wp_norm_lhs
  have htv_final : TraceVm s0 sf_15 := by solve_traceVm
  wp_done

/-! ## 3. `lagrange_interpolate_complete` (Block `373`) with `withVmPreserved` -/

@[local arm64_norm, local wp_norm]
private theorem ptr_sub_two_step_norm (ptr : BitVec 64) (rem : Nat) :
    ptr + BitVec.ofNat 64 (2 * (rem + 1)) + 0xfffffffffffffffe#64 =
      ptr + BitVec.ofNat 64 (2 * rem) :=
  ptr_sub_two_step ptr rem

@[local arm64_norm, local wp_norm]
private theorem ptr_sub_two_step_norm' (ptr : BitVec 64) (rem : Nat) :
    ptr + BitVec.ofNat 64 (2 * (rem + 1)) - 2#64 =
      ptr + BitVec.ofNat 64 (2 * rem) := by
  have h1 : BitVec.ofNat 64 (2 * (rem + 1)) = BitVec.ofNat 64 (2 * rem) + 2#64 := by
    rw [show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, ← BitVec.ofNat_add]
    congr 1
  rw [h1, ← BitVec.add_assoc, BitVec.add_sub_cancel]

@[local arm64_norm, local wp_norm]
private theorem truncate16_eor_zext32 (u : BitVec 16) (v : BitVec 64) :
    BitVec.truncate 16
      (BitVec.zeroExtend 64
        (BitVec.zeroExtend 32 (BitVec.zeroExtend 64 u) ^^^
         BitVec.zeroExtend 32 (BitVec.zeroExtend 64 (BitVec.zeroExtend 32 v)))) =
      u ^^^ BitVec.truncate 16 v := by
  ext i hi
  simp

@[local arm64_norm, local wp_norm]
private theorem truncate16_eor_zext_truncate32 (u : BitVec 16) (v : BitVec 64) :
    BitVec.truncate 16
      (BitVec.zeroExtend 64
        (BitVec.zeroExtend 32 (BitVec.zeroExtend 64 u) ^^^
         BitVec.zeroExtend 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 v)))) =
      u ^^^ BitVec.truncate 16 v := by
  ext i hi
  simp

@[local arm64_norm, local wp_norm]
private theorem truncate16_eor_zext64_truncate32 (u : BitVec 16) (v : BitVec 64) :
    BitVec.truncate 16 (BitVec.zeroExtend 64 u ^^^ BitVec.zeroExtend 64 (BitVec.truncate 32 v)) =
      u ^^^ BitVec.truncate 16 v := by
  ext i hi
  simp

private theorem ule_of_lt_pts {i n : Nat} (hi : i < n) (hn : 4 * n < 2 ^ 64) :
    BitVec.ule (BitVec.ofNat 64 n) (BitVec.ofNat 64 i) = false := by
  simp only [BitVec.ule, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : i < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : n < 2 ^ 64),
    decide_eq_false_iff_not]
  omega

private theorem perm_to_denom (C P T R F : SepProp) :
    C ∗ P ∗ T ∗ R ∗ F = P ∗ T ∗ R ∗ C ∗ F := by
  rw [← sepConj_assoc C, sepConj_comm C P, sepConj_assoc P,
      ← sepConj_assoc C, sepConj_comm C T, sepConj_assoc T,
      ← sepConj_assoc C, sepConj_comm C R, sepConj_assoc R]

@[local arm64_norm, local wp_norm]
private theorem lsl_two_eq_four_mul_norm (n : Nat) :
    (BitVec.ofNat 64 n) <<< 2#64 = BitVec.ofNat 64 (4 * n) := lsl_two_eq_four_mul n

@[local arm64_norm, local wp_norm]
private theorem lsl_two_nat_eq_four_mul_norm (n : Nat) :
    (BitVec.ofNat 64 n) <<< 2 = BitVec.ofNat 64 (4 * n) := lsl_two_eq_four_mul n

@[local arm64_norm, local wp_norm]
private theorem lsl_one_eq_two_mul_norm (n : Nat) :
    (BitVec.ofNat 64 n) <<< 1#64 = BitVec.ofNat 64 (2 * n) := lsl_one_eq_two_mul n

@[local arm64_norm, local wp_norm]
private theorem lsl_one_nat_eq_two_mul_norm (n : Nat) :
    (BitVec.ofNat 64 n) <<< 1 = BitVec.ofNat 64 (2 * n) := lsl_one_eq_two_mul n

private theorem perm_to_div (S1 S2 T R St P C F : SepProp) :
    S1 ∗ S2 ∗ T ∗ R ∗ St ∗ P ∗ C ∗ F =
      C ∗ T ∗ R ∗ S1 ∗ S2 ∗ St ∗ P ∗ F := by
  rw [← sepConj_assoc P C F, sepConj_comm P C, sepConj_assoc C P F,
      ← sepConj_assoc St C, sepConj_comm St C, sepConj_assoc C St,
      ← sepConj_assoc R C, sepConj_comm R C, sepConj_assoc C R,
      ← sepConj_assoc T C, sepConj_comm T C, sepConj_assoc C T,
      ← sepConj_assoc S2 C, sepConj_comm S2 C, sepConj_assoc C S2,
      ← sepConj_assoc S1 C, sepConj_comm S1 C, sepConj_assoc C S1,
      ← sepConj_assoc S2 T, sepConj_comm S2 T, sepConj_assoc T S2,
      ← sepConj_assoc S1 T, sepConj_comm S1 T, sepConj_assoc T S1,
      ← sepConj_assoc S2 R, sepConj_comm S2 R, sepConj_assoc R S2,
      ← sepConj_assoc S1 R, sepConj_comm S1 R, sepConj_assoc R S1]

private theorem truncate16_zext64_truncate32 (v : BitVec 64) :
    BitVec.truncate 16 (BitVec.zeroExtend 64 (BitVec.truncate 32 v)) =
      BitVec.truncate 16 v := by
  ext i hi; simp

set_option maxHeartbeats 1600000 in
private theorem denomLoop_placed_vm_sepWP [LibsignalPlacement] (ext : String → Option (State → State))
    (ptsPtr : BitVec 64) (pts : List Pt) (hpts_len : 4 * pts.length < 2 ^ 64)
    (i : Nat) (hi : i < pts.length)
    (ret_pc : BitVec 64) (Q : State → SepProp → Prop) :
    ∀ (rem j : Nat) (_hrem : j + rem = pts.length) (acc : GF16)
      (s : State) (F : SepProp),
      LibsignalCodeLoaded lsmpl s.mem →
      s.pc = (blkPl_373).base + 84#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      BitVec.truncate 16 (s.readReg64 .x0) = acc.value →
      s.readReg64 .x19 = ptsPtr + BitVec.ofNat 64 (4 * j) →
      s.readReg64 .x24 = lsρ tokenName + 8#64 →
      s.readReg64 .x26 = ptsPtr + BitVec.ofNat 64 (4 * i) →
      s.readReg64 .x27 = Obj.pageOf (lsρ tokenStorageName) →
      s.readReg64 .x28 = ptsPtr + BitVec.ofNat 64 (4 * pts.length) →
      (∀ (sf : State),
        LibsignalCodeLoaded lsmpl sf.mem →
        sf.pc = (blkPl_373).base + 256#64 →
        sf.status = .Running →
        sf.sp = s.sp →
        TraceVm s sf →
        BitVec.truncate 16 (sf.readReg64 .x0) =
          ((pts.drop j).foldl (denomStep (pts[i]'hi).x) acc).value →
        sf.readReg64 .x20 = s.readReg64 .x20 →
        sf.readReg64 .x22 = s.readReg64 .x22 →
        sf.readReg64 .x24 = lsρ tokenName + 8#64 →
        sf.readReg64 .x25 = s.readReg64 .x25 →
        sf.readReg64 .x26 = ptsPtr + BitVec.ofNat 64 (4 * i) →
        sf.readReg64 .x27 = Obj.pageOf (lsρ tokenStorageName) →
        sf.readReg64 .x28 = ptsPtr + BitVec.ofNat 64 (4 * pts.length) →
        sf.readReg64 .x29 = s.readReg64 .x29 →
        calleeSavedVRegs sf = calleeSavedVRegs s →
        SepWP ((blkPC_373).rebase (blkPl_373).base (Rust.withPanics ext)) ret_pc sf
          (ptSliceAt ptsPtr pts ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ F) Q) →
      SepWP ((blkPC_373).rebase (blkPl_373).base (Rust.withPanics ext)) ret_pc s
        (ptSliceAt ptsPtr pts ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ F) Q := by
  intro rem
  induction rem with
  | zero =>
    intro j hrem acc s F hcl hpc hrun hsp_align hx0 hx19 hx24 hx26 hx27 hx28 hnext
    have hj_eq : j = pts.length := by omega
    subst hj_eq
    wp_steps 2
    simp only [List.drop_length, List.foldl_nil] at hnext
    exact hnext _ hcl (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by solve_traceVm)
      (by simpa [arm64_norm] using hx0) (by wp_norm_lhs) (by wp_norm_lhs)
      (by simpa [arm64_norm] using hx24) (by wp_norm_lhs)
      (by simpa [arm64_norm] using hx26) (by simpa [arm64_norm] using hx27)
      (by simpa [arm64_norm] using hx28) (by wp_norm_lhs) (by wp_norm_lhs)
  | succ rem' ih =>
    intro j hrem acc s F hcl hpc hrun hsp_align hx0 hx19 hx24 hx26 hx27 hx28 hnext
    have hj : j < pts.length := by omega
    have hdrop : pts.drop j = (pts[j]'hj) :: pts.drop (j + 1) := List.drop_eq_getElem_cons hj
    have halign_bd8 := aligned_tokenOnce_placed
    rcases ptr_sub_four_mul_ne_zero ptsPtr hj hpts_len with ⟨hne, hne'⟩
    wp_steps 2
    wp_simp_pre [ptSliceAt_focus_x hj ptsPtr]
    wp_steps 1
    wp_conv_pre =>
      rw [← sepConj_assoc, ← ptSliceAt_focus_x hj ptsPtr, ptSliceAt_focus_x hi ptsPtr, sepConj_assoc]
    wp_steps 1
    wp_conv_pre => rw [← sepConj_assoc, ← ptSliceAt_focus_x hi ptsPtr]
    wp_steps 1
    cases hpx : ((pts[i]'hi).x == (pts[j]'hj).x) with
    | false =>
      have hval_ne : (pts[i]'hi).x.value ≠ (pts[j]'hj).x.value := by
        intro heq
        have htrue : ((pts[i]'hi).x == (pts[j]'hj).x) = true := by rw [gf16_beq_iff, beq_iff_eq]; exact heq
        rw [hpx] at htrue; contradiction
      rcases cmp32_zext16_ne_zero _ _ hval_ne with ⟨hcmp1, hcmp2, hcmp3, hcmp4⟩
      have hmul := lscall_blk (callerProg := (blkPC_373).rebase (blkPl_373).base (Rust.withPanics ext))
        (unacceleratedMul_vm_placed_ok (Rust.withPanics ext)) hcl
      simp only [withMemEq, unacceleratedMulTvSpec] at hmul
      apply sepWP_seq_lscl (by exact hcl) (mid := (blkPl_373).base + 84#64)
      wp_steps 1
      wp_simp_pre [tokenInitPlacedAt]
      apply step_ldar32
      · wp_norm_lhs
      · wp_norm_lhs
      · exact blkPC_373_rebase_fetch_0x6c (blkPl_373).base (Rust.withPanics ext)
      · wp_norm_lhs
      · wp_norm_lhs
      · exact halign_bd8
      · wp_sep_access
      · wp_norm_lhs
      wp_steps 6
      apply SepWP.fold tokenInitPlacedAt_fold (by sep_focus)
      wp_call hmul
      wp_steps 1
      apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
      intro hcl_next
      wp_conv_pre => rw [perm_denom_pre]
      apply ih (j + 1) (by omega) (GF16.mul acc (GF16.sub (pts[i]'hi).x (pts[j]'hj).x)) _ F (by exact hcl_next)
      · wp_norm_lhs
      · wp_norm_lhs
      · simpa [arm64_norm, wp_norm, hsp_sf] using hsp_align
      · simp only [arm64_norm, wp_norm, h_10]
        have heor :
            BitVec.truncate 16 (BitVec.zeroExtend 64 (pts[j]'hj).x.value ^^^ BitVec.zeroExtend 64 (pts[i]'hi).x.value) =
              (GF16.sub (pts[i]'hi).x (pts[j]'hj).x).value := by
          change BitVec.truncate 16 (BitVec.zeroExtend 64 (pts[j]'hj).x.value ^^^ BitVec.zeroExtend 64 (pts[i]'hi).x.value) =
            (pts[i]'hi).x.value ^^^ (pts[j]'hj).x.value
          ext k hk; simp [Bool.xor_comm]
        rw [heor]; rfl
      · simp only [arm64_norm, wp_norm, h]; exact ptr_add_four_step ptsPtr j
      · simpa [arm64_norm, wp_norm, h_5] using hx24
      · simpa [arm64_norm, wp_norm, h_7] using hx26
      · simpa [arm64_norm, wp_norm, h_8] using hx27
      · simpa [arm64_norm, wp_norm, h_9] using hx28
      · intro sf' hcl_f hpc_f hrun_f hsp_f htr_f hx0_f hx20_f hx22_f hx24_f hx25_f hx26_f hx27_f hx28_f hx29_f hvregs_f
        refine hnext sf' hcl_f hpc_f hrun_f ?_ ?_ ?_ ?_ ?_ hx24_f ?_ hx26_f hx27_f hx28_f ?_ ?_
        · simpa [arm64_norm, wp_norm, hsp_sf] using hsp_f
        · solve_traceVm
        · rw [hdrop, List.foldl_cons, denomStep]; simp only [hpx, Bool.false_eq_true, ↓reduceIte]; exact hx0_f
        · simpa [arm64_norm, wp_norm, h_1] using hx20_f
        · simpa [arm64_norm, wp_norm, h_3] using hx22_f
        · simpa [arm64_norm, wp_norm, h_6] using hx25_f
        · simpa [arm64_norm, wp_norm, hcs_sf] using hx29_f
        · simpa [arm64_norm, wp_norm, hvregs] using hvregs_f
    | true =>
      have hval_eq : (pts[i]'hi).x.value = (pts[j]'hj).x.value := by rw [gf16_beq_iff, beq_iff_eq] at hpx; exact hpx
      rcases cmp32_zext16_eq_zero _ _ hval_eq with ⟨hcmp1, hcmp2, hcmp3, hcmp4⟩
      wp_steps 1
      apply ih (j + 1) (by omega) acc _ F (by exact hcl)
      · wp_norm_lhs
      · wp_norm_lhs
      · simpa [arm64_norm, wp_norm] using hsp_align
      · simpa [arm64_norm, wp_norm] using hx0
      · simp only [arm64_norm, wp_norm]; exact ptr_add_four_step ptsPtr j
      · simpa [arm64_norm, wp_norm] using hx24
      · simpa [arm64_norm, wp_norm] using hx26
      · simpa [arm64_norm, wp_norm] using hx27
      · simpa [arm64_norm, wp_norm] using hx28
      · intro sf' hcl_f hpc_f hrun_f hsp_f htr_f hx0_f hx20_f hx22_f hx24_f hx25_f hx26_f hx27_f hx28_f hx29_f hvregs_f
        refine hnext sf' hcl_f hpc_f hrun_f ?_ ?_ ?_ ?_ ?_ hx24_f ?_ hx26_f hx27_f hx28_f ?_ ?_
        · simpa [arm64_norm, wp_norm] using hsp_f
        · solve_traceVm
        · rw [hdrop, List.foldl_cons, denomStep]; simp only [hpx, ↓reduceIte]; exact hx0_f
        · simpa [arm64_norm, wp_norm] using hx20_f
        · simpa [arm64_norm, wp_norm] using hx22_f
        · simpa [arm64_norm, wp_norm] using hx25_f
        · simpa [arm64_norm, wp_norm] using hx29_f
        · simpa [arm64_norm, wp_norm] using hvregs_f

set_option maxHeartbeats 1600000 in
private theorem divLoop_placed_vm_sepWP [LibsignalPlacement] (ext : String → Option (State → State))
    (coeffsPtr : BitVec 64) (pix scale : GF16)
    (ret_pc : BitVec 64) (Q : State → SepProp → Prop) :
    ∀ (rem : Nat) (cs : List GF16) (_hrem : rem + 1 < cs.length) (_hlen : 2 * cs.length < 2 ^ 64)
      (s : State) (F : SepProp),
      LibsignalCodeLoaded lsmpl s.mem →
      s.pc = (blkPl_373).base + 352#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      BitVec.truncate 16 (s.readReg64 .x19) = scale.value →
      BitVec.truncate 16 (s.readReg64 .x20) = pix.value →
      s.readReg64 .x21 = coeffsPtr + BitVec.ofNat 64 (2 * (rem + 1)) →
      s.readReg64 .x22 = BitVec.ofNat 64 (rem + 1) →
      s.readReg64 .x24 = lsρ tokenName + 8#64 →
      s.readReg64 .x27 = Obj.pageOf (lsρ tokenStorageName) →
      (∀ (sf : State),
        sf.pc = (blkPl_373).base + 656#64 →
        sf.status = .Running →
        sf.sp = s.sp →
        TraceVm s sf →
        calleeSavedVRegs sf = calleeSavedVRegs s →
        SepWP ((blkPC_373).rebase (blkPl_373).base (Rust.withPanics ext)) ret_pc sf
          (gf16SliceAt coeffsPtr (divLoopPure pix scale (rem + 1) cs) ∗
           tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ F) Q) →
      SepWP ((blkPC_373).rebase (blkPl_373).base (Rust.withPanics ext)) ret_pc s
        (gf16SliceAt coeffsPtr cs ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ F) Q := by
  intro rem
  induction rem with
  | zero =>
    intro cs hrem hlen s F hcl hpc hrun hsp_align hx19 hx20 hx21 hx22 hx24 hx27 hnext
    have hrem1 : 1 < cs.length := hrem
    have halign_bd8 := aligned_tokenOnce_placed
    have hmul := lscall_blk (callerProg := (blkPC_373).rebase (blkPl_373).base (Rust.withPanics ext))
      (unacceleratedMul_vm_placed_ok (Rust.withPanics ext)) hcl
    simp only [withMemEq, unacceleratedMulTvSpec] at hmul
    apply sepWP_seq_lscl hcl (mid := (blkPl_373).base + 492#64)
    wp_simp_pre [gf16SliceAt_focus hrem1 coeffsPtr, tokenInitPlacedAt]
    wp_steps 1
    apply step_ldar32
    · wp_norm_lhs
    · wp_norm_lhs
    · exact blkPC_373_rebase_fetch_0x164 (blkPl_373).base (Rust.withPanics ext)
    · wp_norm_lhs
    · wp_norm_lhs
    · exact halign_bd8
    · wp_sep_access
    · wp_norm_lhs
    wp_steps 6
    apply SepWP.fold tokenInitPlacedAt_fold (by sep_focus)
    wp_call hmul
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    intro hcl1
    have hmul1 := lscall_blk (callerProg := (blkPC_373).rebase (blkPl_373).base (Rust.withPanics ext))
      (unacceleratedMul_vm_placed_ok (Rust.withPanics ext)) hcl1
    simp only [withMemEq, unacceleratedMulTvSpec] at hmul1
    wp_steps 1
    wp_simp_pre [tokenInitPlacedAt]
    apply step_ldar32
    · wp_norm_lhs
    · wp_norm_lhs
    · exact blkPC_373_rebase_fetch_0x1f0 (blkPl_373).base (Rust.withPanics ext)
    · wp_norm_lhs
    · wp_norm_lhs
    · exact halign_bd8
    · wp_sep_access
    · wp_norm_lhs
    wp_steps 7
    apply SepWP.fold tokenInitPlacedAt_fold (by sep_focus)
    wp_call hmul1
    apply sepWP_seg_ls_vm
      (Q := (blkPC_373).rebase (blkPl_373).base (hooksException (Rust.withPanics ext)))
      blkLib_eq_373 (mid := (blkPl_373).base + 656#64)
    intro m_strip
    wp_steps 1
    have hrem0 : 0 < (cs.set 1 ⟨CryptoVerification.LibsignalSpqrV1.unaccelerated.mul (cs[1]'hrem1).value scale.value⟩).length := by
      simp [List.length_set]; omega
    wp_conv_pre => rw [gf16SliceAt_update_one_assoc hrem1 coeffsPtr, gf16SliceAt_focus_assoc hrem0 coeffsPtr]
    wp_steps 5
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun m_real hnsp_z => ?_
    have htv_z := traceVm_of_nsp hnsp_z (by simp [arm64_norm, wp_norm]) (by simp [arm64_norm, wp_norm])
    have hlist :
        (cs.set 1 ⟨CryptoVerification.LibsignalSpqrV1.unaccelerated.mul (cs[1]'hrem1).value scale.value⟩).set 0
          ⟨((cs.set 1 ⟨CryptoVerification.LibsignalSpqrV1.unaccelerated.mul (cs[1]'hrem1).value scale.value⟩)[0]'hrem0).value ^^^
            CryptoVerification.LibsignalSpqrV1.unaccelerated.mul (cs[1]'hrem1).value pix.value⟩ =
        divLoopPure pix scale (0 + 1) cs := by
      simpa [divLoopPure] using divLoop_step_eq pix scale 0 cs hrem
    wp_conv_pre => rw [gf16SliceAt_update_assoc hrem0 coeffsPtr, hlist, perm_div_pre]
    exact hnext _ (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by solve_traceVm)
      (by simp [arm64_norm, wp_norm, hvregs_1, hvregs])
  | succ rem' ih =>
    intro cs hrem hlen s F hcl hpc hrun hsp_align hx19 hx20 hx21 hx22 hx24 hx27 hnext
    have halign_bd8 := aligned_tokenOnce_placed
    rcases bv_sub_one_succ rem' (by omega) with ⟨hsub1, hsub2, hsub3⟩
    have hmul := lscall_blk (callerProg := (blkPC_373).rebase (blkPl_373).base (Rust.withPanics ext))
      (unacceleratedMul_vm_placed_ok (Rust.withPanics ext)) hcl
    simp only [withMemEq, unacceleratedMulTvSpec] at hmul
    apply sepWP_seq_lscl hcl (mid := (blkPl_373).base + 492#64)
    wp_simp_pre [gf16SliceAt_focus hrem coeffsPtr, tokenInitPlacedAt]
    wp_steps 1
    apply step_ldar32
    · wp_norm_lhs
    · wp_norm_lhs
    · exact blkPC_373_rebase_fetch_0x164 (blkPl_373).base (Rust.withPanics ext)
    · wp_norm_lhs
    · wp_norm_lhs
    · exact halign_bd8
    · wp_sep_access
    · wp_norm_lhs
    wp_steps 6
    apply SepWP.fold tokenInitPlacedAt_fold (by sep_focus)
    wp_call hmul
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    intro hcl1
    have hmul1 := lscall_blk (callerProg := (blkPC_373).rebase (blkPl_373).base (Rust.withPanics ext))
      (unacceleratedMul_vm_placed_ok (Rust.withPanics ext)) hcl1
    simp only [withMemEq, unacceleratedMulTvSpec] at hmul1
    apply sepWP_seq_lscl hcl1 (mid := (blkPl_373).base + 352#64)
    wp_steps 1
    wp_simp_pre [tokenInitPlacedAt]
    apply step_ldar32
    · wp_norm_lhs
    · wp_norm_lhs
    · exact blkPC_373_rebase_fetch_0x1f0 (blkPl_373).base (Rust.withPanics ext)
    · wp_norm_lhs
    · wp_norm_lhs
    · exact halign_bd8
    · wp_sep_access
    · wp_norm_lhs
    wp_steps 7
    apply SepWP.fold tokenInitPlacedAt_fold (by sep_focus)
    wp_call hmul1
    apply sepWP_seg_ls_vm
      (Q := (blkPC_373).rebase (blkPl_373).base (hooksException (Rust.withPanics ext)))
      blkLib_eq_373 (mid := (blkPl_373).base + 352#64)
    intro m_strip
    wp_steps 1
    have hrem1 : rem' + 1 < (cs.set (rem' + 1 + 1) ⟨CryptoVerification.LibsignalSpqrV1.unaccelerated.mul (cs[rem' + 1 + 1]'hrem).value scale.value⟩).length := by
      simp [List.length_set]; omega
    wp_conv_pre => rw [gf16SliceAt_update_assoc hrem coeffsPtr, gf16SliceAt_focus_assoc hrem1 coeffsPtr]
    wp_steps 5
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun m_real hnsp_s => ?_
    have htv_s := traceVm_of_nsp hnsp_s (by simp [arm64_norm, wp_norm]) (by simp [arm64_norm, wp_norm])
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    intro hcl2
    let cs_next :=
      let cIdx := cs[rem' + 1 + 1]?.getD GF16.ZERO
      let cPrev := cs[rem' + 1]?.getD GF16.ZERO
      let negativeDelta := GF16.mul cIdx pix
      let coeffs1 := cs.set (rem' + 1 + 1) (GF16.mul cIdx scale)
      coeffs1.set (rem' + 1) (GF16.add cPrev negativeDelta)
    have hlist :
        (cs.set (rem' + 1 + 1) ⟨CryptoVerification.LibsignalSpqrV1.unaccelerated.mul (cs[rem' + 1 + 1]'hrem).value scale.value⟩).set (rem' + 1)
          ⟨((cs.set (rem' + 1 + 1) ⟨CryptoVerification.LibsignalSpqrV1.unaccelerated.mul (cs[rem' + 1 + 1]'hrem).value scale.value⟩)[rem' + 1]'hrem1).value ^^^
            CryptoVerification.LibsignalSpqrV1.unaccelerated.mul (cs[rem' + 1 + 1]'hrem).value pix.value⟩ =
        cs_next := divLoop_step_eq pix scale (rem' + 1) cs hrem
    wp_conv_pre => rw [gf16SliceAt_update_assoc hrem1 coeffsPtr, hlist, perm_div_pre]
    apply ih cs_next (by simp [cs_next, List.length_set]; omega) (by simp [cs_next, List.length_set]; omega) _ F hcl2
    · wp_norm_lhs
    · wp_norm_lhs
    · simpa [arm64_norm, wp_norm, hsp_sf_1, hsp_sf] using hsp_align
    · simpa [arm64_norm, wp_norm, h_11, h] using hx19
    · simpa [arm64_norm, wp_norm, h_12, h_1] using hx20
    · wp_norm_lhs
    · simp [arm64_norm, wp_norm]
    · simpa [arm64_norm, wp_norm, h_16, h_5] using hx24
    · simpa [arm64_norm, wp_norm, h_19, h_8] using hx27
    · intro sf' hpc_f hrun_f hsp_f htr_f hvregs_f
      exact hnext sf' hpc_f hrun_f
        (by simpa [arm64_norm, wp_norm, hsp_sf_1, hsp_sf] using hsp_f)
        (by solve_traceVm)
        (by simpa [arm64_norm, wp_norm, hvregs_1, hvregs] using hvregs_f)

set_option maxHeartbeats 3200000 in
theorem lagrangeComplete_placed_vmPreserved_ok [LibsignalPlacement]
    (ext : String → Option (State → State)) :
    subroutine_ok ((blkPC_373).rebase (blkPl_373).base (Rust.withPanics ext))
      (blkPl_373).base (withLsCodeLoaded lsmpl (addVmPreserved lagrangeCompletePlacedSpec)) := by
  simp only [withLsCodeLoaded, lagrangeCompletePlacedSpec]
  wp_init x s0
  have hule_i : BitVec.ule (BitVec.ofNat 64 x.pts.length) (BitVec.ofNat 64 x.i) = false :=
    ule_of_lt_pts h_7 h_1
  wp_simp_pre [stackAt_lagrangeComplete_split]
  wp_pull_exists
  apply sepWP_seq_lscl h (mid := (blkPl_373).base + 84#64)
  apply sepWP_seg_ls_vm
    (Q := (blkPC_373).rebase (blkPl_373).base (hooksException (Rust.withPanics ext)))
    blkLib_eq_373 (mid := (blkPl_373).base + 84#64)
  intro m_strip
  wp_steps 21
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun m_real hnsp_pro => ?_
  have htv_pro := traceVm_of_nsp hnsp_pro (by simp [arm64_norm, wp_norm]) (by simp [arm64_norm, wp_norm])
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
  intro hcl0
  wp_conv_pre => rw [perm_to_denom]
  apply denomLoop_placed_vm_sepWP ext x.ptsPtr x.pts h_1 x.i h_7 (s0.readReg64 .lr) _
    x.pts.length 0 (by omega) GF16.ONE _ _ hcl0
  · wp_norm_lhs
  · wp_norm_lhs
  · simpa [arm64_norm, wp_norm] using hsp_align
  · rfl
  · simp [arm64_norm, wp_norm]
  · simp [arm64_norm, wp_norm]
  · simp [arm64_norm, wp_norm]
  · simp [arm64_norm, wp_norm]
  · simp [arm64_norm, wp_norm]
  · intro s1 hcl1 hpc1 hrun1 hsp1 htv1 hx0_1 hx20_1 hx22_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs1
    simp only [arm64_norm, wp_norm] at hsp1 htv1 hx20_1 hx22_1 hx25_1 hx29_1 hvregs1
    simp only [List.drop_zero, ← lagrangeDenominator_eq_foldl] at hx0_1
    apply sepWP_seq_lscl hcl1 (mid := (blkPl_373).base + 280#64)
    apply sepWP_seg_ls_vm
      (Q := (blkPC_373).rebase (blkPl_373).base (hooksException (Rust.withPanics ext)))
      blkLib_eq_373 (mid := (blkPl_373).base + 280#64)
    intro m_strip2
    wp_simp_pre [ptSliceAt_focus_y h_7 x.ptsPtr]
    wp_steps 7
    wp_conv_pre =>
      rw [← sepConj_assoc ((x.ptsPtr + BitVec.ofNat 64 (4 * x.i) + 2#64) ↦₁₆ _),
          ← ptSliceAt_focus_y h_7 x.ptsPtr]
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun m_real2 hnsp_pre => ?_
    have htv_pre := traceVm_of_nsp hnsp_pre (by simp [arm64_norm, wp_norm]) (by simp [arm64_norm, wp_norm])
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    intro hcl_div
    have hdiv_call := lscall_blk_cl (callerProg := (blkPC_373).rebase (blkPl_373).base (Rust.withPanics ext))
      (divImpl_vm_placed_ok (Rust.withPanics ext)) hcl_div
    simp only [withMemEq, divImplTvSpec] at hdiv_call
    apply sepWP_seq_lscl hcl_div (mid := (blkPl_373).base + 284#64)
    wp_call hdiv_call
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    intro hcl2
    wp_steps 2
    by_cases hlen2 : x.self.coefficients.length < 2
    · have hult2 : (BitVec.ofNat 64 x.self.coefficients.length).ult 2#64 = true := by
        simp only [BitVec.ult, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : x.self.coefficients.length < 2 ^ 64), decide_eq_true_eq]
        omega
      have hpure_eq : (lagrangeCompletePure x.self x.pts x.i).coefficients = x.self.coefficients := by
        have hsub0 : x.self.coefficients.length - 1 = 0 := by omega
        simp [lagrangeCompletePure, List.getElem?_eq_getElem h_7, hsub0, divLoopPure]
      rw [hsp1]
      wp_steps
      refine SepWP.fold
        (stackAt_lagrangeComplete_merge s0.sp (s0.sp - 128#64) (x.pts[x.i]'h_7).y.value
          (Poly.lagrangeDenominator (x.pts[x.i]'h_7).x x.pts).value
          (s0.readReg64 (Reg.gpr 29#5)) (s0.readReg64 (Reg.gpr 30#5))
          (s0.readReg64 (Reg.gpr 28#5)) (s0.readReg64 (Reg.gpr 27#5))
          (s0.readReg64 (Reg.gpr 26#5)) (s0.readReg64 (Reg.gpr 25#5))
          (s0.readReg64 (Reg.gpr 24#5)) (s0.readReg64 (Reg.gpr 23#5))
          (s0.readReg64 (Reg.gpr 22#5)) (s0.readReg64 (Reg.gpr 21#5))
          (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5)) rfl)
        (by sep_focus) ?_
      rw [hpure_eq]
      have htv_lt2 : TraceVm s0 sf := by solve_traceVm
      rcases htv_lt2 with ⟨htr_lt2, ⟨hbrkS_lt2, hbrk_lt2, htp_lt2⟩, hphys_lt2, hperm_lt2⟩
      wp_done
    · have hult2 : (BitVec.ofNat 64 x.self.coefficients.length).ult 2#64 = false := by
        simp only [BitVec.ult, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : x.self.coefficients.length < 2 ^ 64), decide_eq_false_iff_not]
        omega
      wp_conv_pre => rw [ptSliceAt_focus_x h_7 x.ptsPtr]
      wp_steps 8
      wp_conv_pre => rw [← ptSliceAt_focus_x h_7 x.ptsPtr, perm_to_div]
      let rem := x.self.coefficients.length - 2
      have hrem_eq : rem + 1 + 1 = x.self.coefficients.length := by omega
      let pix := (x.pts[x.i]'h_7).x
      let scale := (x.pts[x.i]'h_7).y.divImpl (Poly.lagrangeDenominator pix x.pts)
      apply divLoop_placed_vm_sepWP ext x.coeffsPtr pix scale (s0.readReg64 .lr) _
        rem x.self.coefficients (by omega) h_8 _ _ (by exact hcl2)
      · wp_norm_lhs
      · wp_norm_lhs
      · simpa [arm64_norm, wp_norm, hsp_sf, hsp1] using hsp_align
      · simp only [arm64_norm, wp_norm, truncate16_zext64_truncate32]; exact h_19
      · simp only [arm64_norm, wp_norm, truncate16_zext64]; rfl
      · simp only [arm64_norm, wp_norm, ← hrem_eq, ptr_sub_two_step_norm']
      · simp only [arm64_norm, wp_norm, ← hrem_eq]
        rw [show (rem + 1 + 1 : Nat) = (rem + 1) + 1 from rfl,
            BitVec.ofNat_add, show BitVec.ofNat 64 1 = 1#64 from rfl, BitVec.add_sub_cancel]
      · simpa [arm64_norm, wp_norm, h_14] using hx24_1
      · simpa [arm64_norm, wp_norm, h_17] using hx27_1
      · intro s2 hpc2 hrun2 hsp2 htv2 hvregs2
        have hpure_eq :
            divLoopPure pix scale (rem + 1) x.self.coefficients =
              (lagrangeCompletePure x.self x.pts x.i).coefficients := by
          have hsub1 : rem + 1 = x.self.coefficients.length - 1 := by omega
          have hnotle1 : ¬ x.self.coefficients.length ≤ 1 := by omega
          simp [lagrangeCompletePure, List.getElem?_eq_getElem h_7, hsub1, hnotle1, GF16.div, pix, scale]
        simp only [arm64_norm, wp_norm, hsp_sf, hsp1, hvregs, hvregs1] at hsp2 hvregs2
        rw [hsp1, hpure_eq]
        wp_steps
        refine SepWP.fold
          (stackAt_lagrangeComplete_merge s0.sp (s0.sp - 128#64) (x.pts[x.i]'h_7).y.value
            (Poly.lagrangeDenominator (x.pts[x.i]'h_7).x x.pts).value
            (s0.readReg64 (Reg.gpr 29#5)) (s0.readReg64 (Reg.gpr 30#5))
            (s0.readReg64 (Reg.gpr 28#5)) (s0.readReg64 (Reg.gpr 27#5))
            (s0.readReg64 (Reg.gpr 26#5)) (s0.readReg64 (Reg.gpr 25#5))
            (s0.readReg64 (Reg.gpr 24#5)) (s0.readReg64 (Reg.gpr 23#5))
            (s0.readReg64 (Reg.gpr 22#5)) (s0.readReg64 (Reg.gpr 21#5))
            (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5)) rfl)
          (by sep_focus) ?_
        have htv_ge2 : TraceVm s0 s2 := by solve_traceVm
        rcases htv_ge2 with ⟨htr_ge2, ⟨hbrkS_ge2, hbrk_ge2, htp_ge2⟩, hphys_ge2, hperm_ge2⟩
        wp_done

end LibsignalBinary.Proofs.SpqrV1.States.Leaves.DecodedMsgCl2PlacedBudgetAux2

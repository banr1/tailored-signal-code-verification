/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.CliHandshakeCodeSymB
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsBPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopErrDefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopErrPlaced
public import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.BaseBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.BaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.LogClosureFrozenPlaced
public import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23Budget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Version-Skip Tail Proof (`+0x1fd4 → +0x2cfc`)

Allocator-budget (`RustCliAllocBudget M`) proof of the previous-session version-skip tail on
Block `518` (`lsProg_518`), advancing `A.pool lim st0 s` with `FreeOnlyEvs` across
`pqxdhLogClosurePlacedSpec` (Block `519`) and `dropSessionStructureLocal2Spec` (Block `512`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopErrPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (SessionState)
open CryptoVerification (
  LibsignalCodeLoaded LibsignalFullPlacement LibsignalPlacement lsmpl lsLogFilterAddr
  withLsCodeLoaded
)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost sessionStateAt)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (
  DropSessionStructureGhost dropSessionStructureLocal2Stack growOneSpeStack
)
open CryptoVerification.E2E.Pqxdh.ResponderStore (pqxdhClosureStack)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe (pqLogLevelCellPlaced)
open CryptoVerification.CliHandshake.Placed (blkLib_eq_519 blkPC_519 blkPl_519)
open CryptoVerification.CliHandshake.RespClosurePlaced (
  blkLib_eq_518 blkPl_518 lsProg_518
)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  dropSessionStructureLocal2Spec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsBPlacedBudget (
  blkLib_518_noSvc0
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopErrDefsPlacedBudget (
  OverPrevErrCliPlacedStmt
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero
attribute [local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg

local macro "wp_steps_sync_518 " ext:term:max mid:term : tactic => `(tactic| (
  apply sepWP_seg_ls_vm (Q := lsProg_518 (hooksException $ext))
    blkLib_eq_518 blkLib_518_noSvc0 (mid := $mid)
  intro _m_strip
  wp_steps
  refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  refine ProofLib.SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))
    (hnext := ?_)
))

/-! ## Basic-block segments (`+0x1fd4 → +0x2cfc`) -/

private theorem cond_ne_subs32_4_of_ne_pl {v : BitVec 32} (h : v ≠ 4#32) :
    ConditionHolds CondCode.NE (subsPState32 4#32 v) = true := by
  unfold subsPState32
  rw [conditionHolds_ne_subs32, bne_iff_ne]
  exact Ne.symm h

/-- Segment `(blkPl_518).base + 0x1fd4 → lsmpl.base 519` on `lsProg_518 ext`, transporting `A.pool`. -/
theorem over_prev_err_seg1_cli_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    (st : M.σ) (s : State) (prevPtr ua90 : BitVec 64) (msgVer ua98 : BitVec 32)
    (hver_ne : msgVer ≠ 4#32)
    (hpc : s.pc = (blkPl_518).base + 0x1fd4#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx8 : s.readReg64 .x8 = 4#64)
    (hx27 : s.readReg64 .x27 = prevPtr) :
    SepWP (lsProg_518 ext)
      (lsmpl.base 519) s
      (((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗
       ((s.sp + 0xa90#64) ↦₆₄ ua90) ∗
       ((s.sp + 0xa98#64) ↦₃₂ ua98) ∗
       A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗
          ((s.sp + 0xa90#64) ↦₆₄ 0x8000000000000006#64) ∗
          ((s.sp + 0xa98#64) ↦₃₂ msgVer) ∗
          A.pool lim st s1) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = s.readReg64 .x19 ∧
        s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg64 .x27 = prevPtr ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x20b4#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hcond_ver := cond_ne_subs32_4_of_ne_pl hver_ne
  have hx8_32 : s.readReg32 (Reg.gpr 8#5) = 4#32 := by simp [State.readReg32, hx8]
  have hx27' : s.readReg64 (Reg.gpr 27#5) = prevPtr := hx27
  wp_steps_sync_518 ext (lsmpl.base 519)
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by sep_ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-- Segment `(blkPl_518).base + 0x20b4 → lsmpl.base 512` on `lsProg_518 ext`, transporting `A.pool`. -/
theorem over_prev_err_seg2_cli_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    (st : M.σ) (s : State)
    (prevPtr errsPtr errTag e1 e2 e3 e4 e5 u_e0 u_e1 u_e2 u_e3 u_e4 u_e5 : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + 0x20b4#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx27 : s.readReg64 .x27 = prevPtr) :
    SepWP (lsProg_518 ext)
      (lsmpl.base 512) s
      (((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗
       ((s.sp + 0xa90#64) ↦₆₄ errTag) ∗
       ((s.sp + 0xa98#64) ↦₆₄ e1) ∗
       ((s.sp + 0xaa0#64) ↦₆₄ e2) ∗
       ((s.sp + 0xaa8#64) ↦₆₄ e3) ∗
       ((s.sp + 0xab0#64) ↦₆₄ e4) ∗
       ((s.sp + 0xab8#64) ↦₆₄ e5) ∗
       ((errsPtr + 48#64) ↦₆₄ u_e0) ∗
       ((errsPtr + 56#64) ↦₆₄ u_e1) ∗
       ((errsPtr + 64#64) ↦₆₄ u_e2) ∗
       ((errsPtr + 72#64) ↦₆₄ u_e3) ∗
       ((errsPtr + 80#64) ↦₆₄ u_e4) ∗
       ((errsPtr + 88#64) ↦₆₄ u_e5) ∗
       A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
          ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 2#64) ∗
          ((s.sp + 0xa90#64) ↦₆₄ errTag) ∗
          ((s.sp + 0xa98#64) ↦₆₄ e1) ∗
          ((s.sp + 0xaa0#64) ↦₆₄ e2) ∗
          ((s.sp + 0xaa8#64) ↦₆₄ e3) ∗
          ((s.sp + 0xab0#64) ↦₆₄ e4) ∗
          ((s.sp + 0xab8#64) ↦₆₄ e5) ∗
          ((errsPtr + 48#64) ↦₆₄ errTag) ∗
          ((errsPtr + 56#64) ↦₆₄ e1) ∗
          ((errsPtr + 64#64) ↦₆₄ e2) ∗
          ((errsPtr + 72#64) ↦₆₄ e3) ∗
          ((errsPtr + 80#64) ↦₆₄ e4) ∗
          ((errsPtr + 88#64) ↦₆₄ e5) ∗
          A.pool lim st s1) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = s.sp + 0x930#64 ∧
        s1.readReg64 .x19 = s.readReg64 .x19 ∧
        s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg64 .x27 = prevPtr ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x20fc#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx27' : s.readReg64 (Reg.gpr 27#5) = prevPtr := hx27
  have herr1 : 1#64 * 0x30#64 + errsPtr = errsPtr + 48#64 := by bv_arith
  wp_steps_sync_518 ext (lsmpl.base 512)
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by sep_ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

/-- Segment `(blkPl_518).base + 0x20fc → (blkPl_518).base + 0x2cfc` on `lsProg_518 ext`, transporting `A.pool`. -/
theorem over_prev_err_seg3_cli_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    (st : M.σ) (s : State) (prevPtr : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + 0x20fc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx27 : s.readReg64 .x27 = prevPtr) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x2cfc#64) s
      (((s.sp + 0xd0#64) ↦₆₄ (prevPtr + 24#64)) ∗
       A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢ ((s.sp + 0xd0#64) ↦₆₄ (prevPtr + 24#64)) ∗ A.pool lim st s1) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = s.readReg64 .x19 ∧
        s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx27' : s.readReg64 (Reg.gpr 27#5) = prevPtr := hx27
  wp_steps_sync_518 ext ((blkPl_518).base + 0x2cfc#64)
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by sep_ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

/-! ## Spatial helpers and `pqxdhLogClosurePlacedSpec` -/

private theorem spA90_344_ver_split_eq_pl (sp : BitVec 64) :
    memRegion (sp + 0xa90#64) 344 = (∃∗ e5 : BitVec 64, ∃∗ e4 : BitVec 64, ∃∗ e3 : BitVec 64,
      ∃∗ e2 : BitVec 64, ∃∗ ua9c : BitVec 32, ∃∗ ua98 : BitVec 32, ∃∗ ua90 : BitVec 64,
      ((sp + 0xa90#64) ↦₆₄ ua90) ∗ ((sp + 0xa98#64) ↦₃₂ ua98) ∗ ((sp + 0xa9c#64) ↦₃₂ ua9c) ∗
      ((sp + 0xaa0#64) ↦₆₄ e2) ∗ ((sp + 0xaa8#64) ↦₆₄ e3) ∗
      ((sp + 0xab0#64) ↦₆₄ e4) ∗ ((sp + 0xab8#64) ↦₆₄ e5) ∗
      memRegion (sp + 0xac0#64) 296) := by
  rw [ProofLib.memRegion_split' (b := sp + 0xa90#64) (n := 8) (k := 336) (b' := sp + 0xa98#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0xa98#64) (n := 4) (k := 332) (b' := sp + 0xa9c#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0xa9c#64) (n := 4) (k := 328) (b' := sp + 0xaa0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0xaa0#64) (n := 8) (k := 320) (b' := sp + 0xaa8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0xaa8#64) (n := 8) (k := 312) (b' := sp + 0xab0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0xab0#64) (n := 8) (k := 304) (b' := sp + 0xab8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0xab8#64) (n := 8) (k := 296) (b' := sp + 0xac0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp + 0xa90#64), ProofLib.memRegion_four (sp + 0xa98#64),
      ProofLib.memRegion_four (sp + 0xa9c#64), ProofLib.memRegion_eight (sp + 0xaa0#64),
      ProofLib.memRegion_eight (sp + 0xaa8#64), ProofLib.memRegion_eight (sp + 0xab0#64),
      ProofLib.memRegion_eight (sp + 0xab8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

private theorem pointsTo32_pair_spA98_pl (sp : BitVec 64) (lo hi : BitVec 32) :
    (((sp + 0xa98#64) ↦₃₂ lo) ∗ ((sp + 0xa9c#64) ↦₃₂ hi)) = ((sp + 0xa98#64) ↦₆₄ (hi ++ lo)) := by
  have h : sp + 0xa9c#64 = (sp + 0xa98#64) + 4#64 := by bv_omega
  rw [h, pointsTo32_pair]

private theorem spA90_344_fold_pl (sp w0 w1 e2 e3 e4 e5 : BitVec 64) :
    ((sp + 0xa90#64) ↦₆₄ w0) ∗ ((sp + 0xa98#64) ↦₆₄ w1) ∗ ((sp + 0xaa0#64) ↦₆₄ e2) ∗
    ((sp + 0xaa8#64) ↦₆₄ e3) ∗ ((sp + 0xab0#64) ↦₆₄ e4) ∗ ((sp + 0xab8#64) ↦₆₄ e5) ∗
    memRegion (sp + 0xac0#64) 296 ⊢
    memRegion (sp + 0xa90#64) 344 := by
  rw [ProofLib.memRegion_split' (b := sp + 0xa90#64) (n := 8) (k := 336) (b' := sp + 0xa98#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0xa98#64) (n := 8) (k := 328) (b' := sp + 0xaa0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0xaa0#64) (n := 8) (k := 320) (b' := sp + 0xaa8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0xaa8#64) (n := 8) (k := 312) (b' := sp + 0xab0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0xab0#64) (n := 8) (k := 304) (b' := sp + 0xab8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0xab8#64) (n := 8) (k := 296) (b' := sp + 0xac0#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _))))))

private theorem errs144_split_eq_at48_pl (errsPtr : BitVec 64) :
    memRegion (errsPtr + 48#64) 144 = (∃∗ u_e5 : BitVec 64, ∃∗ u_e4 : BitVec 64, ∃∗ u_e3 : BitVec 64,
      ∃∗ u_e2 : BitVec 64, ∃∗ u_e1 : BitVec 64, ∃∗ u_e0 : BitVec 64,
      ((errsPtr + 48#64) ↦₆₄ u_e0) ∗ ((errsPtr + 56#64) ↦₆₄ u_e1) ∗
      ((errsPtr + 64#64) ↦₆₄ u_e2) ∗ ((errsPtr + 72#64) ↦₆₄ u_e3) ∗
      ((errsPtr + 80#64) ↦₆₄ u_e4) ∗ ((errsPtr + 88#64) ↦₆₄ u_e5) ∗
      memRegion (errsPtr + 96#64) 96) := by
  rw [ProofLib.memRegion_split' (b := errsPtr + 48#64) (n := 8) (k := 136) (b' := errsPtr + 56#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 56#64) (n := 8) (k := 128) (b' := errsPtr + 64#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 64#64) (n := 8) (k := 120) (b' := errsPtr + 72#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 72#64) (n := 8) (k := 112) (b' := errsPtr + 80#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 80#64) (n := 8) (k := 104) (b' := errsPtr + 88#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 88#64) (n := 8) (k := 96) (b' := errsPtr + 96#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (errsPtr + 48#64), ProofLib.memRegion_eight (errsPtr + 56#64),
      ProofLib.memRegion_eight (errsPtr + 64#64), ProofLib.memRegion_eight (errsPtr + 72#64),
      ProofLib.memRegion_eight (errsPtr + 80#64), ProofLib.memRegion_eight (errsPtr + 88#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

private theorem errs48_fold_ver_at48_pl (errsPtr e2 e3 e4 e5 : BitVec 64) (msgVer ua9c : BitVec 32) :
    ((errsPtr + 48#64) ↦₆₄ 0x8000000000000006#64) ∗ ((errsPtr + 56#64) ↦₆₄ (ua9c ++ msgVer)) ∗
    ((errsPtr + 64#64) ↦₆₄ e2) ∗ ((errsPtr + 72#64) ↦₆₄ e3) ∗ ((errsPtr + 80#64) ↦₆₄ e4) ∗
    ((errsPtr + 88#64) ↦₆₄ e5) ⊢
    ((errsPtr + 48#64) ↦₆₄ 0x8000000000000006#64) ∗ ((errsPtr + 56#64) ↦₃₂ msgVer) ∗
    memRegion (errsPtr + 60#64) 36 := by
  have hpair : ((errsPtr + 56#64) ↦₆₄ (ua9c ++ msgVer)) =
      ((errsPtr + 56#64) ↦₃₂ msgVer) ∗ ((errsPtr + 60#64) ↦₃₂ ua9c) := by
    have h60 : errsPtr + 60#64 = (errsPtr + 56#64) + 4#64 := by bv_omega
    rw [h60, ← pointsTo32_pair]
  rw [hpair, sepConj_assoc,
      ProofLib.memRegion_split' (b := errsPtr + 60#64) (n := 4) (k := 32) (b' := errsPtr + 64#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 64#64) (n := 8) (k := 24) (b' := errsPtr + 72#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 72#64) (n := 8) (k := 16) (b' := errsPtr + 80#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 80#64) (n := 8) (k := 8) (b' := errsPtr + 88#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _) (sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))))))

/-- Budget-threaded (`VmPreserved`-preserving) relocatable `[LibsignalPlacement]` spec for
`pqxdh_log_closure` (Block `519`). -/
def pqxdhLogClosurePlacedSpec [LibsignalPlacement] : Spec Unit where
  pre := fun _ s =>
    ⌜True⌝ ∗ pqLogLevelCellPlaced ∗ stackAt s.sp pqxdhClosureStack
  post := fun _ s sf =>
    ⌜sf.trace = s.trace ∧ VmPreserved s sf⌝ ∗ pqLogLevelCellPlaced ∗ stackAt s.sp pqxdhClosureStack

private theorem stackAt_pqxdhClosure_placed (sp : BitVec 64) :
    stackAt sp pqxdhClosureStack =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        ((sp - 432#64) ↦₆₄ v0) ∗ ((sp - 424#64) ↦₆₄ v1) ∗
        ((sp - 416#64) ↦₆₄ v2) ∗ ((sp - 408#64) ↦₆₄ v3)) ∗
      stackAt (sp - 96#64) 304 ∗
      (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
       ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
       ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ w0) ∗ ((sp - 88#64) ↦₆₄ w1) ∗ ((sp - 80#64) ↦₆₄ w2) ∗
        ((sp - 72#64) ↦₆₄ w3) ∗ ((sp - 64#64) ↦₆₄ w4) ∗ ((sp - 56#64) ↦₆₄ w5) ∗
        ((sp - 48#64) ↦₆₄ w6) ∗ ((sp - 40#64) ↦₆₄ w7) ∗ ((sp - 32#64) ↦₆₄ w8) ∗
        ((sp - 24#64) ↦₆₄ w9) ∗ ((sp - 16#64) ↦₆₄ w10) ∗ ((sp - 8#64) ↦₆₄ w11)) := by
  have h1 := ProofLib.stackAt_split_cells sp 336 12 (by decide)
  have h2 := stackAt_split_bottom (sp - 96#64) 304 32 (by decide)
  have hsub : (sp - 96#64) - BitVec.ofNat 64 (304 + 32) = sp - 432#64 := by
    rw [BitVec.sub_sub]; rfl
  rw [hsub, show (32 : Nat) = 8 * 4 by rfl,
      ProofLib.memRegion_cells (sp - 432#64) 4 (by decide)] at h2
  change stackAt sp pqxdhClosureStack = stackAt (sp - 96#64) 336 ∗ cells (sp - 96#64) 12 at h1
  have hc4 : cells (sp - 432#64) 4 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        ((sp - 432#64) ↦₆₄ v0) ∗ ((sp - 424#64) ↦₆₄ v1) ∗
        ((sp - 416#64) ↦₆₄ v2) ∗ ((sp - 408#64) ↦₆₄ v3)) := by
    cells_unfold
  have hc12 : cells (sp - 96#64) 12 =
      (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
       ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
       ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ w0) ∗ ((sp - 88#64) ↦₆₄ w1) ∗ ((sp - 80#64) ↦₆₄ w2) ∗
        ((sp - 72#64) ↦₆₄ w3) ∗ ((sp - 64#64) ↦₆₄ w4) ∗ ((sp - 56#64) ↦₆₄ w5) ∗
        ((sp - 48#64) ↦₆₄ w6) ∗ ((sp - 40#64) ↦₆₄ w7) ∗ ((sp - 32#64) ↦₆₄ w8) ∗
        ((sp - 24#64) ↦₆₄ w9) ∗ ((sp - 16#64) ↦₆₄ w10) ∗ ((sp - 8#64) ↦₆₄ w11)) := by
    cells_unfold
  rw [h1, h2, hc4, hc12, sepConj_assoc]

section LogClosureVm
attribute [local irreducible] VmPreserved

/-- Block `519` (`pqxdhLogClosurePlacedSpec` with `VmPreserved`) verified under
`[LibsignalFullPlacement]`. -/
theorem pqxdh_log_closure_placed_ok [LibsignalFullPlacement]
    (H : String → Option (State → State)) :
    subroutine_ok
      ((blkPC_519).rebase (blkPl_519).base H)
      (blkPl_519).base
      pqxdhLogClosurePlacedSpec := by
  unfold pqxdhLogClosurePlacedSpec pqLogLevelCellPlaced lsLogFilterAddr
  simp only [pure_true, emp_sepConj, stackAt_pqxdhClosure_placed,
    sepExists_sepConj_left, sepExists_sepConj_right]
  wp_init x s0
  apply sepWP_seg_ls_vm (Q := (blkPC_519).rebase (blkPl_519).base (hooksException H))
    blkLib_eq_519 (mid := s0.readReg64 (Reg.gpr 30#5))
  intro _m_strip
  wp_steps
  refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  simp only [State.setMem_setMem] at _hnsp ⊢
  have _hvm : VmPreserved s0 _ = True :=
    propext ⟨fun _ => trivial,
      fun _ => _hnsp.toVmPreserved (by wp_norm_lhs)⟩
  have _htr : _ = s0.trace := _hnsp.1
  wp_done

end LogClosureVm

/-! ## `LibsignalCodeRoLoaded` composition -/

private theorem weaken_frame {prog : Program} {ret : BitVec 64} {s : State}
    {P T T' F : SepProp} {Q Qp : State → SepProp → Prop}
    (hent : T ⊢ T') (hP : P = T ∗ F)
    (h : SepWPp prog ret s (T' ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  rw [hP]
  exact SepWPp.weaken_pre (sepConj_mono_left hent) h

private theorem bind_sepWP_cro_frame [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P P_step : SepProp} {P_step_post : State → SepProp} {F : SepProp}
    {Q_regs : State → Prop} {Q Qp : State → SepProp → Prop}
    (hL : prog.CodeLoaded s.mem)
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hstep : SepWP prog mid s P_step
      (fun sm P_step' => (P_step' ⊢ P_step_post sm) ∧ Q_regs sm))
    (hP : P = P_step ∗ F)
    (hnext : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      prog.CodeLoaded sm.mem → LibsignalCodeRoLoaded lsmpl sm.mem → Q_regs sm →
      SepWPp prog ret sm (P_step_post sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm _
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpc, hrun, P_step', hmm, hent, hregs⟩ | ⟨_, _hoom⟩⟩ := hstep.elim hm hL
  rotate_left; · first | exact False.elim _hoom | exact (not_satisfies_false_sepConj _hoom).elim
  have hmm' : sm.mem ⊨ (P_step_post sm ∗ F) ∗ R := by
    rw [sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left hent) hmm
  have hLm : prog.CodeLoaded sm.mem := hsteps.codeLoaded hL
  obtain ⟨sf, hsteps', hout'⟩ :=
    hnext sm hpc hrun hLm (hcro.of_keepsFrozen hsteps.keepsFrozen) hregs R hmm' hLm
  exact ⟨sf, hsteps.trans hsteps', hout'⟩

private theorem call_raw_nopanic_cro [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hL : prog.CodeLoaded s.mem)
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      prog.CodeLoaded sf.mem → LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  have h1 : SepWPp prog ret_pc s P
      (fun sm Pm => sm.sp = s.sp ∧ CalleeSavedPreserved s sm ∧
        Pm = (withLsCodeLoaded lsmpl spec).post x s sm ∗ F) Qp := by
    refine SepWPp.call_wpp (x := x) (F := F) hcall hpc hrun hsp hlr ?_
      (fun sf code R' _ hex => by
        dsimp only [withLsCodeLoaded] at hex
        rw [hexit_false] at hex
        exact allowPanic_not_exited hex)
      (fun sf _ ⟨R', hpan⟩ => by
        dsimp only [withLsCodeLoaded] at hpan
        rw [hpan_false] at hpan
        exact (allowPanic_not_exited hpan).elim)
      (fun sm hpcm hrunm hspm hcsm => SepWPp.done hpcm hrunm ⟨hspm, hcsm, rfl⟩)
      (fun sf R' _ hoom_post => by
        dsimp only [withLsCodeLoaded] at hoom_post
        rw [hoom_false] at hoom_post
        exact (not_satisfies_false_sepConj hoom_post).elim)
    intro R hm
    dsimp only [withLsCodeLoaded]
    rw [hspec]
    have hpre1 : s.mem ⊨ ⌜φ⌝ ∗ (⌜LibsignalCodeLoaded lsmpl s.mem⌝ ∗ (T ∗ (F ∗ R))) := by
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
      exact ⟨hφ, hcro.1, hm⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre1
  intro R hm _
  rcases h1 R hm hL with ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hpost, hspm, hcsm, rfl⟩ | hpan | hoom_out⟩
  · dsimp only [withLsCodeLoaded] at hpost
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    have hLm : prog.CodeLoaded sm.mem := hsteps.codeLoaded hL
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hsp_alm hcsm hLm
        (hcro.of_keepsFrozen hsteps.keepsFrozen) R hpost hLm
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inl hpan)⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom_out)⟩

set_option maxHeartbeats 1000000 in
/-- Pointwise budget-threaded `LibsignalCodeRoLoaded` proof of `OverPrevErr`
(`(blkPl_518).base + 0x1fd4 → (blkPl_518).base + 0x2cfc`) on `lsProg_518 ext`. -/
theorem overPrevErr_cro_placed_at [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (hLogClosure : subroutine_ok (lsProg_518 ext) (lsmpl.base 519)
      (withLsCodeLoaded lsmpl pqxdhLogClosurePlacedSpec))
    (hDropSS3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (st0 : M.σ) (s0 s : State) (prevPtr errsPtr : BitVec 64) (msgVer : BitVec 32)
    (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hver_ne : msgVer ≠ 4#32)
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hL : (lsProg_518 ext).CodeLoaded s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x1fd4#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx8 : s.readReg64 .x8 = 4#64)
    (hx27 : s.readReg64 .x27 = prevPtr) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x2cfc#64) s
      (((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗
       ((s.sp + 0xd0#64) ↦₆₄ (prevPtr + 24#64)) ∗
       ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗
       memRegion (errsPtr + 48#64) 144 ∗
       memRegion (s.sp + 0xa90#64) 344 ∗
       sessionStateAt A.repAlloc (s.sp + 0x930#64) G st ∗
       pqLogLevelCellPlaced ∗
       A.pool lim st0 s ∗
       stackAt s.sp growOneSpeStack)
      (fun sf P_f =>
        (P_f ⊢
          ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗
          ((s.sp + 0xd0#64) ↦₆₄ (prevPtr + 24#64)) ∗
          ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
          ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 2#64) ∗
          ((errsPtr + 48#64) ↦₆₄ 0x8000000000000006#64) ∗
          ((errsPtr + 56#64) ↦₃₂ msgVer) ∗
          memRegion (errsPtr + 60#64) 36 ∗
          memRegion (errsPtr + 96#64) 96 ∗
          memRegion (s.sp + 0xa90#64) 344 ∗
          memRegion (s.sp + 0x930#64) 344 ∗
          pqLogLevelCellPlaced ∗
          (∃∗ evs : List AllocEvent,
            ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st0) sf) ∗
          stackAt s.sp growOneSpeStack) ∧
        sf.sp = s.sp ∧
        sf.trace = s0.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        LibsignalCodeRoLoaded lsmpl sf.mem ∧
        (lsProg_518 ext).CodeLoaded sf.mem)
      Qp := by
  refine weaken_frame (Entails.of_eq (spA90_344_ver_split_eq_pl s.sp)) (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun e5 => SepWPp.exists_elim fun e4 =>
    SepWPp.exists_elim fun e3 => SepWPp.exists_elim fun e2 =>
    SepWPp.exists_elim fun ua9c => SepWPp.exists_elim fun ua98 => SepWPp.exists_elim fun ua90 => ?_
  refine bind_sepWP_cro_frame hL hcro
    (over_prev_err_seg1_cli_placed_wp A lim ext st0 s prevPtr ua90 msgVer ua98
      hver_ne hpc hrun hsp_align hx8 hx27)
    (by sep_focus)
    fun s1 hpc1 hrun1 hL1 hcro1 ⟨hsp1, htr1, hx19_1, hx20_1, hx27_1, hx29_1, hlr1, hvregs1⟩ => ?_
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1] using hsp_align
  have hstack_log :
      stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 4176 ∗ stackAt s.sp pqxdhClosureStack :=
    stackAt_split_bottom s.sp pqxdhClosureStack 4176 (by decide)
  refine weaken_frame (Entails.of_eq hstack_log) (by sep_focus) ?_
  refine call_raw_nopanic_cro
    (spec := pqxdhLogClosurePlacedSpec) (x := ()) (φ := True)
    (T := pqLogLevelCellPlaced ∗ stackAt s.sp pqxdhClosureStack)
    hL1 hcro1 hLogClosure hpc1 hrun1 hsp1_al hlr1
    (by dsimp only [pqxdhLogClosurePlacedSpec]; rw [hsp1])
    trivial (by sep_focus)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 _ hcs2 hL2 hcro2 => ?_)
  dsimp only [pqxdhLogClosurePlacedSpec]
  rw [hsp1, sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨htr2_1, hvm2_1⟩ => ?_
  refine weaken_frame (Entails.of_eq (A.pool_of_vmPreserved hvm2_1).symm) (by sep_focus) ?_
  have hstack_restore2 :
      memRegion (s.sp - 4608#64) 4176 ∗ stackAt s.sp pqxdhClosureStack ⊢
        stackAt s.sp growOneSpeStack := by
    rw [hstack_log]; exact Entails.refl _
  refine weaken_frame hstack_restore2 (by sep_focus) ?_
  have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hsp_align
  rcases hcs2 with ⟨hx19_cs2, hx20_cs2, _, _, _, _, _, _, hx27_cs2, _, hx29_cs2, hvregs_cs2⟩
  have hx19_2 : s2.readReg64 .x19 = s.readReg64 .x19 := hx19_cs2.trans hx19_1
  have hx20_2 : s2.readReg64 .x20 = s.readReg64 .x20 := hx20_cs2.trans hx20_1
  have hx27_2 : s2.readReg64 .x27 = prevPtr := hx27_cs2.trans hx27_1
  have hx29_2 : s2.readReg64 .x29 = s.readReg64 .x29 := hx29_cs2.trans hx29_1
  refine weaken_frame (Entails.of_eq (pointsTo32_pair_spA98_pl s.sp msgVer ua9c)) (by sep_focus) ?_
  refine weaken_frame (Entails.of_eq (errs144_split_eq_at48_pl errsPtr)) (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_e5 => SepWPp.exists_elim fun u_e4 =>
    SepWPp.exists_elim fun u_e3 => SepWPp.exists_elim fun u_e2 =>
    SepWPp.exists_elim fun u_e1 => SepWPp.exists_elim fun u_e0 => ?_
  have hseg2 := over_prev_err_seg2_cli_placed_wp A lim ext st0 s2 prevPtr errsPtr
    0x8000000000000006#64 (ua9c ++ msgVer) e2 e3 e4 e5 u_e0 u_e1 u_e2 u_e3 u_e4 u_e5
    hpc2 hrun2 hsp2_align hx27_2
  rw [hsp2] at hseg2
  refine bind_sepWP_cro_frame hL2 hcro2 hseg2 (by sep_focus)
    fun s3 hpc3 hrun3 hL3 hcro3 ⟨hsp3_2, htr3_2, hx0_3, hx19_3, hx20_3, hx27_3, hx29_3, hlr3, hvregs3⟩ => ?_
  refine weaken_frame (errs48_fold_ver_at48_pl errsPtr e2 e3 e4 e5 msgVer ua9c) (by sep_focus) ?_
  refine weaken_frame (spA90_344_fold_pl s.sp 0x8000000000000006#64 (ua9c ++ msgVer) e2 e3 e4 e5)
    (by sep_focus) ?_
  have hsp3 : s3.sp = s.sp := hsp3_2
  have hsp3_al : s3.spAligned = true := by simpa only [State.spAligned, hsp3] using hsp_align
  have hstack_drop2 :
      stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 416 ∗ stackAt s.sp dropSessionStructureLocal2Stack :=
    stackAt_split_bottom s.sp dropSessionStructureLocal2Stack 416 (by decide)
  refine weaken_frame (Entails.of_eq hstack_drop2) (by sep_focus) ?_
  refine call_raw_nopanic_cro
    (spec := dropSessionStructureLocal2Spec M A lim)
    (x := ((⟨s.sp + 0x930#64, G, st⟩ : DropSessionStructureGhost), st0))
    (φ := s3.readReg64 .x0 = s.sp + 0x930#64 ∧
      LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 (s3.readReg64 .lr))
    (T := sessionStateAt A.repAlloc (s.sp + 0x930#64) G st ∗ A.pool lim st0 s3 ∗
      stackAt s.sp dropSessionStructureLocal2Stack)
    hL3 hcro3 hDropSS3 hpc3 hrun3 hsp3_al hlr3
    (by dsimp only [dropSessionStructureLocal2Spec]; rw [hsp3])
    (And.intro hx0_3 (show LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 (s3.readReg64 .lr) by
      simp (config := { decide := true }) [show s3.readReg64 .lr = _ from hlr3, wp_norm]))
    (by sep_focus)
    (hnext := fun s4 hpc4 hrun4 hsp4_3 _ hcs4 hL4 hcro4 => ?_)
  dsimp only [dropSessionStructureLocal2Spec]
  conv => arg 4; simp only [hsp3, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun evs => ?_
  refine SepWPp.pure_elim fun ⟨htr4_3, hfree⟩ => ?_
  have hstack_restore4 :
      memRegion (s.sp - 4608#64) 416 ∗ stackAt s.sp dropSessionStructureLocal2Stack ⊢
        stackAt s.sp growOneSpeStack := by
    rw [hstack_drop2]; exact Entails.refl _
  refine weaken_frame hstack_restore4 (by sep_focus) ?_
  have hsp4 : s4.sp = s.sp := hsp4_3.trans hsp3
  have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := by rw [hsp4]; exact hsp_align
  rcases hcs4 with ⟨hx19_cs4, hx20_cs4, _, _, _, _, _, _, hx27_cs4, _, hx29_cs4, hvregs_cs4⟩
  have hx19_4 : s4.readReg64 .x19 = s.readReg64 .x19 := hx19_cs4.trans (hx19_3.trans hx19_2)
  have hx20_4 : s4.readReg64 .x20 = s.readReg64 .x20 := hx20_cs4.trans (hx20_3.trans hx20_2)
  have hx27_4 : s4.readReg64 .x27 = prevPtr := hx27_cs4.trans hx27_3
  have hx29_4 : s4.readReg64 .x29 = s.readReg64 .x29 := hx29_cs4.trans (hx29_3.trans hx29_2)
  have hseg3 := over_prev_err_seg3_cli_placed_wp A lim ext (M.stepEvents evs st0) s4 prevPtr
    hpc4 hrun4 hsp4_align hx27_4
  rw [hsp4] at hseg3
  refine bind_sepWP_cro_frame hL4 hcro4 hseg3 (by sep_focus)
    fun sf hpcf hrunf hLf hcrof ⟨hspf_4, htrf_4, hx19_f, hx20_f, hx29_f, hvregsf⟩ => ?_
  have htrf : sf.trace = s0.trace := by rw [htrf_4, htr4_3, htr3_2, htr2_1, htr1, htr]
  have hx19f : sf.readReg64 .x19 = s.readReg64 .x19 := hx19_f.trans hx19_4
  have hx20f : sf.readReg64 .x20 = s.readReg64 .x20 := hx20_f.trans hx20_4
  have hx29f : sf.readReg64 .x29 = s.readReg64 .x29 := hx29_f.trans hx29_4
  have hvregsf_s : calleeSavedVRegs sf = calleeSavedVRegs s := by
    rw [hvregsf, hvregs_cs4, hvregs3, hvregs_cs2, hvregs1]
  have hpool_pack :
      A.pool lim (M.stepEvents evs st0) sf ⊢
        ∃∗ evs' : List AllocEvent,
          ⌜FreeOnlyEvs evs'⌝ ∗ A.pool lim (M.stepEvents evs' st0) sf :=
    Entails.sepExists_right evs (Entails.pure_right hfree (Entails.refl _))
  refine SepWPp.done hpcf hrunf ⟨?_, hspf_4, htrf, hx19f, hx20f, hx29f, hvregsf_s, hcrof, hLf⟩
  refine Entails.trans (Entails.of_eq (show _ =
    A.pool lim (M.stepEvents evs st0) sf ∗
      (((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗
       ((s.sp + 0xd0#64) ↦₆₄ (prevPtr + 24#64)) ∗
       ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 2#64) ∗
       ((errsPtr + 48#64) ↦₆₄ 0x8000000000000006#64) ∗
       ((errsPtr + 56#64) ↦₃₂ msgVer) ∗
       memRegion (errsPtr + 60#64) 36 ∗
       memRegion (errsPtr + 96#64) 96 ∗
       memRegion (s.sp + 0xa90#64) 344 ∗
       memRegion (s.sp + 0x930#64) 344 ∗
       pqLogLevelCellPlaced ∗
       stackAt s.sp growOneSpeStack) by sep_ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left hpool_pack) ?_
  exact Entails.of_eq (by ac_rfl)



/-! ## `LibsignalFrozen` / `[LibsignalFullPlacement]` corollaries -/

theorem lscro_of_frozen [LibsignalPlacement] {m : Memory}
    (hfr : CryptoVerification.LibsignalFrozen lsmpl m) :
    LibsignalCodeRoLoaded lsmpl m :=
  ⟨LibsignalCodeLoaded.of_codeLoaded hfr.2, hfr.1⟩

/-- Block `519` own-program `withLsFrozen` contract under `[LibsignalFullPlacement]`. -/
theorem pqxdh_log_closure_frozen_placed_ok [LibsignalFullPlacement]
    (H : CryptoVerification.LibsignalHooks) :
    subroutine_ok
      ((blkPC_519).rebase (blkPl_519).base H)
      (lsmpl.base 519)
      (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl pqxdhLogClosurePlacedSpec) :=
  _root_.LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.subroutine_ok_withLsFrozen_of_plain
    (pqxdh_log_closure_placed_ok H)

/-- Lift Block `519` (`pqxdhLogClosurePlacedSpec`) to any `callerProg` under `[LibsignalFullPlacement]`. -/
theorem pqxdh_log_closure_frozen_placed_ok_of_block [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {H : CryptoVerification.LibsignalHooks}
    [CryptoVerification.IsLsBlockProg callerProg i H] :
    subroutine_ok callerProg (lsmpl.base 519)
      (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl pqxdhLogClosurePlacedSpec) :=
  _root_.LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.ls_subroutine_ok_withLsFrozen_of_block_frc
    (pqxdh_log_closure_frozen_placed_ok H)

theorem bind_sepWP_fr_frame_budget [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P P_step : SepProp} {P_step_post : State → SepProp} {F : SepProp}
    {Q_regs : State → Prop} {Q Qp : State → SepProp → Prop}
    (hL : prog.CodeLoaded s.mem)
    (hfr : CryptoVerification.LibsignalFrozen lsmpl s.mem)
    (hstep : SepWP prog mid s P_step
      (fun sm P_step' => (P_step' ⊢ P_step_post sm) ∧ Q_regs sm))
    (hP : P = P_step ∗ F)
    (hnext : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      prog.CodeLoaded sm.mem → CryptoVerification.LibsignalFrozen lsmpl sm.mem → Q_regs sm →
      SepWPp prog ret sm (P_step_post sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm _
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpc, hrun, P_step', hmm, hent, hregs⟩ | ⟨_, _hoom⟩⟩ := hstep.elim hm hL
  rotate_left; · first | exact False.elim _hoom | exact (not_satisfies_false_sepConj _hoom).elim
  have hmm' : sm.mem ⊨ (P_step_post sm ∗ F) ∗ R := by
    rw [sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left hent) hmm
  have hLm : prog.CodeLoaded sm.mem := hsteps.codeLoaded hL
  obtain ⟨sf, hsteps', hout'⟩ :=
    hnext sm hpc hrun hLm
      (CryptoVerification.libsignalFrozen_of_keepsFrozen hfr hsteps.keepsFrozen) hregs R hmm' hLm
  exact ⟨sf, hsteps.trans hsteps', hout'⟩

theorem call_raw_nopanic_fr_budget [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hL : prog.CodeLoaded s.mem)
    (hfr : CryptoVerification.LibsignalFrozen lsmpl s.mem)
    (hcall : subroutine_ok prog entry (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      prog.CodeLoaded sf.mem → CryptoVerification.LibsignalFrozen lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm _
  have hm' : s.mem ⊨ (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl spec).pre x s ∗ (F ∗ R) := by
    dsimp only [CryptoVerification.LibsignalTripleRatchet.withLsFrozen]
    rw [hspec]
    have h1 : s.mem ⊨ ⌜φ⌝ ∗ (⌜CryptoVerification.LibsignalFrozen lsmpl s.mem⌝ ∗ (T ∗ (F ∗ R))) := by
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
      exact ⟨hφ, hfr, hm⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) h1
  obtain ⟨sm, hsteps, hout, _⟩ := hcall.no_fault_before_outcome x (F ∗ R) s hpc hrun hm' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, _hoom_post⟩
  rotate_right
  · dsimp only [CryptoVerification.LibsignalTripleRatchet.withLsFrozen] at _hoom_post
    rw [hoom_false] at _hoom_post
    exact (not_satisfies_false_sepConj _hoom_post).elim
  · dsimp only [CryptoVerification.LibsignalTripleRatchet.withLsFrozen] at hpost
    rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    have hLm : prog.CodeLoaded sm.mem := hsteps.codeLoaded hL
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hsp_alm hcsm hLm
        (CryptoVerification.libsignalFrozen_of_keepsFrozen hfr hsteps.keepsFrozen) R hpost hLm
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [CryptoVerification.LibsignalTripleRatchet.withLsFrozen] at hpost
    rw [hpan_false] at hpost
    exact (allowPanic_not_exited hpost).elim
  · dsimp only [CryptoVerification.LibsignalTripleRatchet.withLsFrozen] at hpost
    rw [hexit_false] at hpost
    exact (allowPanic_not_exited hpost).elim

set_option maxHeartbeats 1000000 in
/-- Pointwise budget-threaded `LibsignalFrozen` proof of `OverPrevErr`
(`(blkPl_518).base + 0x1fd4 → (blkPl_518).base + 0x2cfc`) on `lsProg_518 ext`. -/
theorem overPrevErr_frozen_placed_at [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (hDropSS3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (st0 : M.σ) (s0 s : State) (prevPtr errsPtr : BitVec 64) (msgVer : BitVec 32)
    (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hver_ne : msgVer ≠ 4#32)
    (hfr : CryptoVerification.LibsignalFrozen lsmpl s.mem)
    (hL : (lsProg_518 ext).CodeLoaded s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x1fd4#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx8 : s.readReg64 .x8 = 4#64)
    (hx27 : s.readReg64 .x27 = prevPtr) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x2cfc#64) s
      (((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗
       ((s.sp + 0xd0#64) ↦₆₄ (prevPtr + 24#64)) ∗
       ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗
       memRegion (errsPtr + 48#64) 144 ∗
       memRegion (s.sp + 0xa90#64) 344 ∗
       sessionStateAt A.repAlloc (s.sp + 0x930#64) G st ∗
       pqLogLevelCellPlaced ∗
       A.pool lim st0 s ∗
       stackAt s.sp growOneSpeStack)
      (fun sf P_f =>
        (P_f ⊢
          ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗
          ((s.sp + 0xd0#64) ↦₆₄ (prevPtr + 24#64)) ∗
          ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
          ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 2#64) ∗
          ((errsPtr + 48#64) ↦₆₄ 0x8000000000000006#64) ∗
          ((errsPtr + 56#64) ↦₃₂ msgVer) ∗
          memRegion (errsPtr + 60#64) 36 ∗
          memRegion (errsPtr + 96#64) 96 ∗
          memRegion (s.sp + 0xa90#64) 344 ∗
          memRegion (s.sp + 0x930#64) 344 ∗
          pqLogLevelCellPlaced ∗
          (∃∗ evs : List AllocEvent,
            ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st0) sf) ∗
          stackAt s.sp growOneSpeStack) ∧
        sf.sp = s.sp ∧
        sf.trace = s0.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        LibsignalCodeRoLoaded lsmpl sf.mem ∧
        (lsProg_518 ext).CodeLoaded sf.mem)
      Qp := by
  refine weaken_frame (Entails.of_eq (spA90_344_ver_split_eq_pl s.sp)) (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun e5 => SepWPp.exists_elim fun e4 =>
    SepWPp.exists_elim fun e3 => SepWPp.exists_elim fun e2 =>
    SepWPp.exists_elim fun ua9c => SepWPp.exists_elim fun ua98 => SepWPp.exists_elim fun ua90 => ?_
  refine bind_sepWP_fr_frame_budget hL hfr
    (over_prev_err_seg1_cli_placed_wp A lim ext st0 s prevPtr ua90 msgVer ua98
      hver_ne hpc hrun hsp_align hx8 hx27)
    (by sep_focus)
    fun s1 hpc1 hrun1 hL1 hfr1 ⟨hsp1, htr1, hx19_1, hx20_1, hx27_1, hx29_1, hlr1, hvregs1⟩ => ?_
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1] using hsp_align
  have hstack_log :
      stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 4176 ∗ stackAt s.sp pqxdhClosureStack :=
    stackAt_split_bottom s.sp pqxdhClosureStack 4176 (by decide)
  refine weaken_frame (Entails.of_eq hstack_log) (by sep_focus) ?_
  refine call_raw_nopanic_fr_budget
    (spec := pqxdhLogClosurePlacedSpec) (x := ()) (φ := True)
    (T := pqLogLevelCellPlaced ∗ stackAt s.sp pqxdhClosureStack)
    hL1 hfr1 (pqxdh_log_closure_frozen_placed_ok_of_block (callerProg := lsProg_518 ext)) hpc1 hrun1 hsp1_al hlr1
    (by dsimp only [pqxdhLogClosurePlacedSpec]; rw [hsp1])
    trivial (by sep_focus)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 _ hcs2 hL2 hfr2 => ?_)
  have hcro2 : LibsignalCodeRoLoaded lsmpl s2.mem := lscro_of_frozen hfr2
  dsimp only [pqxdhLogClosurePlacedSpec]
  rw [hsp1, sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨htr2_1, hvm2_1⟩ => ?_
  refine weaken_frame (Entails.of_eq (A.pool_of_vmPreserved hvm2_1).symm) (by sep_focus) ?_
  have hstack_restore2 :
      memRegion (s.sp - 4608#64) 4176 ∗ stackAt s.sp pqxdhClosureStack ⊢
        stackAt s.sp growOneSpeStack := by
    rw [hstack_log]; exact Entails.refl _
  refine weaken_frame hstack_restore2 (by sep_focus) ?_
  have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hsp_align
  rcases hcs2 with ⟨hx19_cs2, hx20_cs2, _, _, _, _, _, _, hx27_cs2, _, hx29_cs2, hvregs_cs2⟩
  have hx19_2 : s2.readReg64 .x19 = s.readReg64 .x19 := hx19_cs2.trans hx19_1
  have hx20_2 : s2.readReg64 .x20 = s.readReg64 .x20 := hx20_cs2.trans hx20_1
  have hx27_2 : s2.readReg64 .x27 = prevPtr := hx27_cs2.trans hx27_1
  have hx29_2 : s2.readReg64 .x29 = s.readReg64 .x29 := hx29_cs2.trans hx29_1
  refine weaken_frame (Entails.of_eq (pointsTo32_pair_spA98_pl s.sp msgVer ua9c)) (by sep_focus) ?_
  refine weaken_frame (Entails.of_eq (errs144_split_eq_at48_pl errsPtr)) (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_e5 => SepWPp.exists_elim fun u_e4 =>
    SepWPp.exists_elim fun u_e3 => SepWPp.exists_elim fun u_e2 =>
    SepWPp.exists_elim fun u_e1 => SepWPp.exists_elim fun u_e0 => ?_
  have hseg2 := over_prev_err_seg2_cli_placed_wp A lim ext st0 s2 prevPtr errsPtr
    0x8000000000000006#64 (ua9c ++ msgVer) e2 e3 e4 e5 u_e0 u_e1 u_e2 u_e3 u_e4 u_e5
    hpc2 hrun2 hsp2_align hx27_2
  rw [hsp2] at hseg2
  refine bind_sepWP_cro_frame hL2 hcro2 hseg2 (by sep_focus)
    fun s3 hpc3 hrun3 hL3 hcro3 ⟨hsp3_2, htr3_2, hx0_3, hx19_3, hx20_3, hx27_3, hx29_3, hlr3, hvregs3⟩ => ?_
  refine weaken_frame (errs48_fold_ver_at48_pl errsPtr e2 e3 e4 e5 msgVer ua9c) (by sep_focus) ?_
  refine weaken_frame (spA90_344_fold_pl s.sp 0x8000000000000006#64 (ua9c ++ msgVer) e2 e3 e4 e5)
    (by sep_focus) ?_
  have hsp3 : s3.sp = s.sp := hsp3_2
  have hsp3_al : s3.spAligned = true := by simpa only [State.spAligned, hsp3] using hsp_align
  have hstack_drop2 :
      stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 416 ∗ stackAt s.sp dropSessionStructureLocal2Stack :=
    stackAt_split_bottom s.sp dropSessionStructureLocal2Stack 416 (by decide)
  refine weaken_frame (Entails.of_eq hstack_drop2) (by sep_focus) ?_
  refine call_raw_nopanic_cro
    (spec := dropSessionStructureLocal2Spec M A lim)
    (x := ((⟨s.sp + 0x930#64, G, st⟩ : DropSessionStructureGhost), st0))
    (φ := s3.readReg64 .x0 = s.sp + 0x930#64 ∧
      LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 (s3.readReg64 .lr))
    (T := sessionStateAt A.repAlloc (s.sp + 0x930#64) G st ∗ A.pool lim st0 s3 ∗
      stackAt s.sp dropSessionStructureLocal2Stack)
    hL3 hcro3 hDropSS3 hpc3 hrun3 hsp3_al hlr3
    (by dsimp only [dropSessionStructureLocal2Spec]; rw [hsp3])
    (And.intro hx0_3 (show LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 (s3.readReg64 .lr) by
      simp (config := { decide := true }) [show s3.readReg64 .lr = _ from hlr3, wp_norm]))
    (by sep_focus)
    (hnext := fun s4 hpc4 hrun4 hsp4_3 _ hcs4 hL4 hcro4 => ?_)
  dsimp only [dropSessionStructureLocal2Spec]
  conv => arg 4; simp only [hsp3, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun evs => ?_
  refine SepWPp.pure_elim fun ⟨htr4_3, hfree⟩ => ?_
  have hstack_restore4 :
      memRegion (s.sp - 4608#64) 416 ∗ stackAt s.sp dropSessionStructureLocal2Stack ⊢
        stackAt s.sp growOneSpeStack := by
    rw [hstack_drop2]; exact Entails.refl _
  refine weaken_frame hstack_restore4 (by sep_focus) ?_
  have hsp4 : s4.sp = s.sp := hsp4_3.trans hsp3
  have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := by rw [hsp4]; exact hsp_align
  rcases hcs4 with ⟨hx19_cs4, hx20_cs4, _, _, _, _, _, _, hx27_cs4, _, hx29_cs4, hvregs_cs4⟩
  have hx19_4 : s4.readReg64 .x19 = s.readReg64 .x19 := hx19_cs4.trans (hx19_3.trans hx19_2)
  have hx20_4 : s4.readReg64 .x20 = s.readReg64 .x20 := hx20_cs4.trans (hx20_3.trans hx20_2)
  have hx27_4 : s4.readReg64 .x27 = prevPtr := hx27_cs4.trans hx27_3
  have hx29_4 : s4.readReg64 .x29 = s.readReg64 .x29 := hx29_cs4.trans (hx29_3.trans hx29_2)
  have hseg3 := over_prev_err_seg3_cli_placed_wp A lim ext (M.stepEvents evs st0) s4 prevPtr
    hpc4 hrun4 hsp4_align hx27_4
  rw [hsp4] at hseg3
  refine bind_sepWP_cro_frame hL4 hcro4 hseg3 (by sep_focus)
    fun sf hpcf hrunf hLf hcrof ⟨hspf_4, htrf_4, hx19_f, hx20_f, hx29_f, hvregsf⟩ => ?_
  have htrf : sf.trace = s0.trace := by rw [htrf_4, htr4_3, htr3_2, htr2_1, htr1, htr]
  have hx19f : sf.readReg64 .x19 = s.readReg64 .x19 := hx19_f.trans hx19_4
  have hx20f : sf.readReg64 .x20 = s.readReg64 .x20 := hx20_f.trans hx20_4
  have hx29f : sf.readReg64 .x29 = s.readReg64 .x29 := hx29_f.trans hx29_4
  have hvregsf_s : calleeSavedVRegs sf = calleeSavedVRegs s := by
    rw [hvregsf, hvregs_cs4, hvregs3, hvregs_cs2, hvregs1]
  have hpool_pack :
      A.pool lim (M.stepEvents evs st0) sf ⊢
        ∃∗ evs' : List AllocEvent,
          ⌜FreeOnlyEvs evs'⌝ ∗ A.pool lim (M.stepEvents evs' st0) sf :=
    Entails.sepExists_right evs (Entails.pure_right hfree (Entails.refl _))
  refine SepWPp.done hpcf hrunf ⟨?_, hspf_4, htrf, hx19f, hx20f, hx29f, hvregsf_s, hcrof, hLf⟩
  refine Entails.trans (Entails.of_eq (show _ =
    A.pool lim (M.stepEvents evs st0) sf ∗
      (((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗
       ((s.sp + 0xd0#64) ↦₆₄ (prevPtr + 24#64)) ∗
       ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 2#64) ∗
       ((errsPtr + 48#64) ↦₆₄ 0x8000000000000006#64) ∗
       ((errsPtr + 56#64) ↦₃₂ msgVer) ∗
       memRegion (errsPtr + 60#64) 36 ∗
       memRegion (errsPtr + 96#64) 96 ∗
       memRegion (s.sp + 0xa90#64) 344 ∗
       memRegion (s.sp + 0x930#64) 344 ∗
       pqLogLevelCellPlaced ∗
       stackAt s.sp growOneSpeStack) by sep_ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left hpool_pack) ?_
  exact Entails.of_eq (by ac_rfl)

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopErrPlacedBudget

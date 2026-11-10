/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.EpiloguePlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysProof
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysProofPlacedB
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.RodataPlaced
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysConstPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysFallbackExitPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysProofPlacedABudget
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysSetupPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Pure
import ProofLib.SepLogic.WPp

/-!
# `<PolyEncoder as Encoder>::next_chunk` (Block `416`): Budget-Threaded Placed `points_to_polys` Loop

Relocatable `[LibsignalPlacement]` verification of `pointsToPolysStep_placed_sepWPp` and the
16-iteration `points_to_polys` conversion loop (`+976 -> +4424`) threading `RustCliAllocBudget M`,
`BudgetLimits`, `PointsToPolysIterEnv`, and `PointsToPolysLoopEnv`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysProofPlacedBBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkPC_373 blkPC_416 blkPl_373 blkPl_416
   lsmpl withLsCodeLoaded)
open scoped CryptoVerification
open scoped CryptoVerification.CodeLayout
open CryptoVerification.RustHeap (allocHookStack arrayAt)
open CryptoVerification.LibsignalSpqrV1 (Point Poly PolyEncoder)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Poly (pointListOf pointOf polyListOf polyOf)
open CryptoVerification.SpqrV1.Poly.ComputeAt
  (readReg32_setMem_pre readReg64_setMem_pre readReg_setMem_pre sp_setMem_pre)
open CryptoVerification.SpqrV1.Poly.LagrangeComplete (lagrangeCompletePlacedSpec)
open CryptoVerification.SpqrV1.Poly.LagrangePrepare
  (lagrangePrepareStack readReg32_setMem_setPC_pre readReg32_setPC_pre
   readReg64_setMem_setPC_pre readReg64_setPC_pre readReg_setMem_setPC_pre readReg_setPC_pre
   sp_setMem_setPC_pre sp_setPC_pre)
open CryptoVerification.SpqrV1.Poly.NextChunk
  (add_8_add_8_eq completePointsPolysPlacedAt enumeratePts_length memRegion24_off_eq_polyHeader
   memRegion_112_fold_216 memRegion_112_split_216 memRegion_656_fold newPolyBufAt_n0_intro
   newPolyBufAt_pos_intro pointListOf_cons_mul24_off pointToPolyPure polyListOf_cons_mul24_off
   ptVecBufAt ptVecBufAt_pos_fold stackAt_lagrangePrepare_fold_alloc
   stackAt_lagrangePrepare_split_alloc zeroPolySlotsAt zeroPolySlotsAt_entails_polyListOf)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs
   RustCliAllocBudget SeqEnv fitsEvents_append)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsBudget
  (LagrangeSumStepEnv PointsToPolysIterEnv PointsToPolysLoopEnv RepeatSeqEnv
   pointsToPolysIterEnv_nonempty pointsToPolysLoopEnv_nonempty)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.EpiloguePlacedBudget (AllocContractsPlaced)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysConstPlacedBudget
  (basis_n0_placed_sepWPp)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysFallbackExitPlacedBudget
  (BasisPosEnv basis_pos_placed_sepWPp fitsEnv_basisPos_of_pointsToPolysIter
   fitsEnv_lagrangeSumTail_of_pointsToPolysIter fitsEnv_setupPtVec_of_pointsToPolysIter)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysProofPlacedABudget
  (cleanupIter_placed_sepWP lagrangeSumAndFree_placed_sepWPp)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysSetupPlacedBudget
  (SetupPtVecEnv fitsEnv_setupPtVec_iff setupPtVecEvents setupPtVec_placed_sepWPp)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

@[local arm64_norm, local wp_norm] private theorem exists_pow_two_eq_two_p2pb_pl_bud :
    (∃ k : Nat, 2 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨1, rfl⟩

attribute [local simp, local arm64_norm, local wp_norm] add_8_add_8_eq

/-! ## `LibsignalCodeLoaded` CPS Helpers -/

example : ∃ evs, PointsToPolysIterEnv 0 evs := pointsToPolysIterEnv_nonempty 0
example : ∃ evs, PointsToPolysIterEnv 5 evs := pointsToPolysIterEnv_nonempty 5
example : ∃ evs, PointsToPolysIterEnv 8 evs := pointsToPolysIterEnv_nonempty 8
example : ∃ evs, PointsToPolysLoopEnv (List.replicate 16 ⟨[]⟩) evs :=
  pointsToPolysLoopEnv_nonempty (List.replicate 16 ⟨[]⟩)

private def s0WithLrB (s0 : State) (mid : BitVec 64) : State :=
  s0.writeReg64 (Reg.gpr 30#5) mid

private theorem s0WithLrB_trace (s0 : State) (mid : BitVec 64) :
    (s0WithLrB s0 mid).trace = s0.trace := rfl

private theorem s0WithLrB_lr (s0 : State) (mid : BitVec 64) :
    (s0WithLrB s0 mid).readReg64 (Reg.gpr 30#5) = mid := by
  simp [s0WithLrB, arm64_norm, wp_norm]

private theorem sepWPp_seq_lscl_b [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LibsignalCodeLoaded lsmpl sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.seq_frozen (fun _ _ h0 hkf => h0.of_keepsFrozen hkf) hcl h

private theorem sepWPp_bind_lscl_b [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h : SepWPp prog mid s P
      (fun sm Pm => LibsignalCodeLoaded lsmpl sm.mem → SepWPp prog ret sm Pm Q Qp) Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨_, _, Pm, hmm, hcont⟩ | hpan_or_oom⟩ := h R hm hL
  · obtain ⟨sf, hsteps', hout⟩ :=
      hcont (hcl.of_keepsFrozen hsteps.keepsFrozen) R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr hpan_or_oom⟩

private theorem sepWPp_cut_s0WithLrB [LibsignalPlacement]
    {ext : String → Option (State → State)}
    {Q Q_panic : State → SepProp → Prop}
    {s0 s : State} {mid : BitVec 64} {P : SepProp}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h : SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      ((s0WithLrB s0 mid).readReg64 (Reg.gpr 30#5)) s P
      (fun sm Pm => LibsignalCodeLoaded lsmpl sm.mem →
        SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
          (s0.readReg64 (Reg.gpr 30#5)) sm Pm Q Q_panic)
      Q_panic) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s P Q Q_panic := by
  rw [s0WithLrB_lr] at h
  exact sepWPp_bind_lscl_b hcl h

private theorem sepWPp_done_s0WithLrB [LibsignalPlacement]
    {ext : String → Option (State → State)}
    {Q Q_panic : State → SepProp → Prop}
    {s0 s1 : State} {mid : BitVec 64} {P1 : SepProp}
    (hpc1 : s1.pc = mid) (hrun1 : s1.status = .Running)
    (hcont : LibsignalCodeLoaded lsmpl s1.mem →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s1 P1 Q Q_panic) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      ((s0WithLrB s0 mid).readReg64 (Reg.gpr 30#5)) s1 P1
      (fun sm Pm => LibsignalCodeLoaded lsmpl sm.mem →
        SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
          (s0.readReg64 (Reg.gpr 30#5)) sm Pm Q Q_panic)
      Q_panic :=
  SepWPp.done (by rw [s0WithLrB_lr]; exact hpc1) hrun1 hcont

/-! ## 1. Budget-Threaded Per-Iteration `pointsToPolysStep_placed_sepWPp` (`+976 -> +976 / +4424`) -/

/-- One full budget-threaded iteration (`j < 16`, `+976 -> +976 / +4424` in Block `416`) of the
    `points_to_polys` conversion loop: converts `pts[j]` into `pointToPolyPure pts[j]`, stores it
    into slot `j` of `[fsp + 256 .. fsp + 640)`, and steps `st` along
    `PointsToPolysIterEnv pt.value.length`. -/
theorem pointsToPolysStep_placed_sepWPp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)} {Q Q_panic : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (hcomp_ok : subroutine_ok ((blkPC_373).rebase (blkPl_373).base (Rust.withPanics ext))
      (blkPl_373).base (withLsCodeLoaded lsmpl (withVmPreserved lagrangeCompletePlacedSpec)))
    (s0 s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (fsp ptsBase : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (j : Nat) (hj : j < 16)
    (pt : Point) (hbound : pt.value.length ≤ 0x0555555555555555)
    (u16 u24 u32 u40 u64 u72 u80 u96 u640 u648 u1040 u1048 u1056 : BitVec 64)
    (Frame R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 976#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (htrace : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = ptsBase)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 j)
    (hx28 : s.readReg64 .x28 = 24#64)
    (hx29 : s.readReg64 .x29 = fsp + 1104#64)
    (hfit : FitsEnv M lim st (PointsToPolysIterEnv pt.value.length))
    (hcont : ∀ (evs : List AllocEvent) s_out
      u16' u24' u32' u40' u64' u72' u80' u96' u640' u648' u1040' u1048' u1056',
      PointsToPolysIterEnv pt.value.length evs →
      LibsignalCodeLoaded lsmpl s_out.mem →
      s_out.pc = (if j == 15 then (blkPl_416).base + 4424#64 else (blkPl_416).base + 976#64) →
      s_out.status = .Running → s_out.sp = fsp → s_out.trace = s0.trace →
      calleeSavedVRegs s_out = calleeSavedVRegs s →
      s_out.readReg64 .x19 = ptsBase →
      s_out.readReg64 .x20 = BitVec.ofNat 64 (j + 1) →
      s_out.readReg64 .x27 = s.readReg64 .x27 →
      s_out.readReg64 .x28 = 24#64 →
      s_out.readReg64 .x29 = fsp + 1104#64 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s_out
        (A.pool lim (M.stepEvents evs st) s_out ∗
         pointOf A.repAlloc (ptsBase + BitVec.ofNat 64 (24 * j)) pt ∗
         polyOf A.repAlloc ((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) (pointToPolyPure pt) ∗
         ((fsp + 16#64) ↦₆₄ u16') ∗ ((fsp + 24#64) ↦₆₄ u24') ∗
         ((fsp + 32#64) ↦₆₄ u32') ∗ ((fsp + 40#64) ↦₆₄ u40') ∗
         ((fsp + 48#64) ↦₆₄ 2#64) ∗
         ((fsp + 64#64) ↦₆₄ u64') ∗ ((fsp + 72#64) ↦₆₄ u72') ∗ ((fsp + 80#64) ↦₆₄ u80') ∗
         ((fsp + 88#64) ↦₆₄ ptsBase) ∗ ((fsp + 96#64) ↦₆₄ u96') ∗
         memRegion (fsp + 112#64) 120 ∗
         ((fsp + 640#64) ↦₆₄ u640') ∗ ((fsp + 648#64) ↦₆₄ u648') ∗
         memRegion (fsp + 656#64) 24 ∗
         ((fsp + 1040#64) ↦₆₄ u1040') ∗ ((fsp + 1048#64) ↦₆₄ u1048') ∗
         ((fsp + 1056#64) ↦₆₄ u1056') ∗
         completePointsPolysPlacedAt ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
         stackAt fsp lagrangePrepareStack ∗ Frame)
        Q Q_panic) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool lim st s ∗
       pointOf A.repAlloc (ptsBase + BitVec.ofNat 64 (24 * j)) pt ∗
       polyOf A.repAlloc ((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) ⟨[]⟩ ∗
       ((fsp + 16#64) ↦₆₄ u16) ∗ ((fsp + 24#64) ↦₆₄ u24) ∗
       ((fsp + 32#64) ↦₆₄ u32) ∗ ((fsp + 40#64) ↦₆₄ u40) ∗
       ((fsp + 48#64) ↦₆₄ 2#64) ∗
       ((fsp + 64#64) ↦₆₄ u64) ∗ ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ u80) ∗
       ((fsp + 88#64) ↦₆₄ ptsBase) ∗ ((fsp + 96#64) ↦₆₄ u96) ∗
       memRegion (fsp + 112#64) 120 ∗
       ((fsp + 640#64) ↦₆₄ u640) ∗ ((fsp + 648#64) ↦₆₄ u648) ∗
       memRegion (fsp + 656#64) 24 ∗
       ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗
       ((fsp + 1056#64) ↦₆₄ u1056) ∗
       completePointsPolysPlacedAt ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
       stackAt fsp lagrangePrepareStack ∗ Frame)
      Q Q_panic := by
  have hfit_setup : FitsEnv M lim st (SetupPtVecEnv pt.value.length) := by
    by_cases hk0 : pt.value.length = 0
    · rw [hk0, fitsEnv_setupPtVec_iff]
      dsimp only [setupPtVecEvents, ↓reduceIte, FitsEvents]
      trivial
    · exact fitsEnv_setupPtVec_of_pointsToPolysIter hk0 hfit
  rw [stackAt_lagrangePrepare_split_alloc fsp]
  apply sepWPp_cut_s0WithLrB hcl (mid := (blkPl_416).base + 1136#64)
  refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (setupPtVec_placed_sepWPp hA (s0WithLrB s0 ((blkPl_416).base + 1136#64)) s fsp ptsBase
      hfsp_align j hj pt hbound u32 u40
      (polyOf A.repAlloc ((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) ⟨[]⟩ ∗
       ((fsp + 16#64) ↦₆₄ u16) ∗ ((fsp + 24#64) ↦₆₄ u24) ∗
       ((fsp + 64#64) ↦₆₄ u64) ∗ ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ u80) ∗
       ((fsp + 88#64) ↦₆₄ ptsBase) ∗ ((fsp + 96#64) ↦₆₄ u96) ∗
       memRegion (fsp + 112#64) 120 ∗
       ((fsp + 640#64) ↦₆₄ u640) ∗ ((fsp + 648#64) ↦₆₄ u648) ∗
       memRegion (fsp + 656#64) 24 ∗
       ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗
       ((fsp + 1056#64) ↦₆₄ u1056) ∗
       completePointsPolysPlacedAt ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
       memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
         (lagrangePrepareStack - allocHookStack) ∗ Frame) R
      hpc hrun hsp htrace hx19 hx20 hx28 hfit_setup ?_)
  intro s1 ptVecPtr hptVec_ne hpc1 hrun1 hsp1 htr1 hvregs1
    hx20_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  apply sepWPp_done_s0WithLrB hpc1 hrun1; intro hcl1
  rw [s0WithLrB_trace] at htr1
  by_cases hn0 : pt.value.length = 0
  · have hstep0 : M.stepEvents (setupPtVecEvents pt.value.length) st = st := by
      simp [setupPtVecEvents, hn0]
    rw [hstep0, memRegion24_off_eq_polyHeader fsp]
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWPp.exists_elim; intro u672
    apply SepWPp.exists_elim; intro u664
    apply SepWPp.exists_elim; intro u656
    have hx25_0 : s1.readReg64 .x25 = 0#64 := by rw [hx25_1, hn0]
    apply sepWPp_cut_s0WithLrB hcl1 (mid := (blkPl_416).base + 4004#64)
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (basis_n0_placed_sepWPp (M := M) (A := A) (lim := lim) (st := st)
        (s0WithLrB s0 ((blkPl_416).base + 4004#64)) s1 fsp hfsp_align
        u24 u96 u640 u648 u664 u672
        (pointOf A.repAlloc (ptsBase + BitVec.ofNat 64 (24 * j)) pt ∗
         ptVecBufAt A.repAlloc ptVecPtr pt.value ∗
         ((fsp + 32#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
         ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
         ((fsp + 48#64) ↦₆₄ 2#64) ∗
         stackAt fsp allocHookStack ∗
         polyOf A.repAlloc ((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) ⟨[]⟩ ∗
         ((fsp + 16#64) ↦₆₄ u16) ∗
         ((fsp + 64#64) ↦₆₄ u64) ∗ ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ u80) ∗
         ((fsp + 88#64) ↦₆₄ ptsBase) ∗
         memRegion (fsp + 112#64) 120 ∗
         ((fsp + 656#64) ↦₆₄ u656) ∗
         ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗
         ((fsp + 1056#64) ↦₆₄ u1056) ∗
         completePointsPolysPlacedAt ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
         memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
           (lagrangePrepareStack - allocHookStack) ∗ Frame) R
        hpc1 hrun1 hsp1 htr1 hx25_0 ?_)
    intro s2 hpc2 hrun2 hsp2 htr2 hvregs2
      hx19_2 hx20_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2
    apply sepWPp_done_s0WithLrB hpc2 hrun2; intro hcl2
    rw [s0WithLrB_trace] at htr2
    have hx19_2' : s2.readReg64 .x19 = BitVec.ofNat 64 pt.value.length := by
      rw [hx19_2, hn0]
    have h648_eq :
        ((fsp + 648#64) ↦₆₄ 0#64) = ((fsp + 648#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) := by
      rw [hn0]
    rw [h648_eq]
    apply sepWPp_seq_lscl_b hcl2
      (mid := if j == 15 then (blkPl_416).base + 4424#64 else (blkPl_416).base + 976#64)
    refine SepWP.weaken_pre (newPolyBufAt_n0_intro A.repAlloc pt hn0 _) ?_
    refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (cleanupIter_placed_sepWP hA (st := st) s2 fsp ptsBase 2#64 ptVecPtr hfsp_align j hj pt hbound
        (pointOf A.repAlloc (ptsBase + BitVec.ofNat 64 (24 * j)) pt ∗
         ((fsp + 16#64) ↦₆₄ u16) ∗ ((fsp + 24#64) ↦₆₄ 0#64) ∗
         ((fsp + 48#64) ↦₆₄ 2#64) ∗
         ((fsp + 64#64) ↦₆₄ u64) ∗ ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ u80) ∗
         ((fsp + 96#64) ↦₆₄ 0#64) ∗
         memRegion (fsp + 112#64) 120 ∗
         ((fsp + 656#64) ↦₆₄ u656) ∗ ((fsp + 664#64) ↦₆₄ 2#64) ∗ ((fsp + 672#64) ↦₆₄ 0#64) ∗
         ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗
         ((fsp + 1056#64) ↦₆₄ u1056) ∗
         completePointsPolysPlacedAt ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
         memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
           (lagrangePrepareStack - allocHookStack) ∗ Frame)
        hpc2 hrun2 hsp2 hx19_2' (hx20_2.trans hx20_1) (hx26_2.trans hx26_1)
        (hx28_2.trans hx28_1) ?_)
    intro evsClean s3 hevsClean hpc3 hrun3 hsp3 htr3 hvregs3
      hx19_3 hx20_3 hx27_3 hx28_3 hx29_3
    apply SepWP.done hpc3 hrun3
    intro hcl3
    have hiter0 : PointsToPolysIterEnv pt.value.length evsClean := by
      simp [PointsToPolysIterEnv, hn0, hevsClean]
    apply SepWPp.fold (memRegion_656_fold fsp u656 2#64 0#64) (by sep_frame)
    apply SepWPp.fold (stackAt_lagrangePrepare_fold_alloc fsp) (by sep_frame)
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hcont evsClean s3 u16 0#64 (BitVec.ofNat 64 (j + 1)) (BitVec.ofNat 64 pt.value.length)
        u64 u72 u80 0#64 2#64 (BitVec.ofNat 64 pt.value.length) u1040 u1048 u1056
        hiter0 hcl3 hpc3 hrun3 hsp3 (htr3.trans htr2)
        (hvregs3.trans (hvregs2.trans hvregs1)) hx19_3 hx20_3
        (hx27_3.trans (hx27_2.trans hx27_1)) hx28_3
        (hx29_3.trans (hx29_2.trans (hx29_1.trans hx29))))
  · have hpts_len : (PolyEncoder.enumeratePts 0 pt.value).length = pt.value.length :=
      enumeratePts_length 0 pt.value
    have hpts_ne : PolyEncoder.enumeratePts 0 pt.value ≠ [] :=
      List.ne_nil_of_length_pos (by omega)
    have hpts_bound : (PolyEncoder.enumeratePts 0 pt.value).length ≤ 0x0555555555555555 := by
      omega
    have hfit_basis :
        FitsEnv M lim (M.stepEvents (setupPtVecEvents pt.value.length) st)
          (BasisPosEnv (PolyEncoder.enumeratePts 0 pt.value).length) := by
      rw [hpts_len]
      exact fitsEnv_basisPos_of_pointsToPolysIter hn0 hfit
    unfold ptVecBufAt
    simp only [hn0, ↓reduceIte, RustCliAllocBudget.repAlloc_live]
    apply SepWPp.fold (memRegion_112_split_216 fsp) (by sep_frame)
    conv =>
      arg 4
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_pure_left_comm,
        sepConj_assoc]
    apply SepWPp.exists_elim; intro u216
    apply SepWPp.exists_elim; intro u224
    apply SepWPp.pure_left; intro _
    apply SepWPp.fold (stackAt_lagrangePrepare_fold_alloc fsp) (by sep_frame)
    have hx24_1' :
        s1.readReg64 .x24 = BitVec.ofNat 64 (4 * (PolyEncoder.enumeratePts 0 pt.value).length) := by
      rw [hpts_len, hx24_1]
    have hx25_1' :
        s1.readReg64 .x25 = BitVec.ofNat 64 (PolyEncoder.enumeratePts 0 pt.value).length := by
      rw [hpts_len, hx25_1]
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (basis_pos_placed_sepWPp hA hcomp_ok (PolyEncoder.enumeratePts 0 pt.value) hpts_ne hpts_bound
        s0 s1 hcl1 fsp ptVecPtr hfsp_align u24 u72 u80 u96 u216 u224 u1040 u1048 u1056
        (pointOf A.repAlloc (ptsBase + BitVec.ofNat 64 (24 * j)) pt ∗
         A.live ptVecPtr (4 * pt.value.length) 2 ∗
         ((fsp + 32#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
         ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
         ((fsp + 48#64) ↦₆₄ 2#64) ∗
         polyOf A.repAlloc ((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) ⟨[]⟩ ∗
         ((fsp + 16#64) ↦₆₄ u16) ∗
         ((fsp + 64#64) ↦₆₄ u64) ∗
         ((fsp + 88#64) ↦₆₄ ptsBase) ∗
         memRegion (fsp + 112#64) 104 ∗
         ((fsp + 640#64) ↦₆₄ u640) ∗ ((fsp + 648#64) ↦₆₄ u648) ∗ Frame) R
        hpc1 hrun1 hsp1 htr1 hx24_1' hx25_1' hx26_1 (hx29_1.trans hx29) hfit_basis ?_)
    intro evsBasis s2 basisPtr accPtr u72' u80' u216' u224' u1040' u1048' u1056'
      _hevsBasis hextBasis hcl2 hbasis_ne hacc_ne hpc2 hrun2 hsp2 htr2 hvregs2
      hx0_2 hx20_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2
    have hextBasis' :
        ∀ evs_tail,
          SeqEnv (RepeatSeqEnv pt.value.length (LagrangeSumStepEnv pt.value.length))
            FreeOnlyEvs evs_tail →
          PointsToPolysIterEnv pt.value.length
            ((setupPtVecEvents pt.value.length ++ evsBasis) ++ evs_tail) := by
      intro evs_tail htail
      simpa only [hpts_len] using hextBasis evs_tail (by simpa only [hpts_len] using htail)
    have hfit_tail :
        FitsEnv M lim
          (M.stepEvents evsBasis (M.stepEvents (setupPtVecEvents pt.value.length) st))
          (SeqEnv (RepeatSeqEnv pt.value.length (LagrangeSumStepEnv pt.value.length)) FreeOnlyEvs) :=
      fitsEnv_lagrangeSumTail_of_pointsToPolysIter hfit hextBasis'
    have hfit_sum :
        FitsEnv M lim
          (M.stepEvents evsBasis (M.stepEvents (setupPtVecEvents pt.value.length) st))
          (RepeatSeqEnv (PolyEncoder.enumeratePts 0 pt.value).length
            (LagrangeSumStepEnv (PolyEncoder.enumeratePts 0 pt.value).length)) := by
      rw [hpts_len]
      exact fun evs_s hevs_s => hfit_tail evs_s (Or.inl hevs_s)
    apply SepWPp.fold (memRegion_112_fold_216 fsp u216' u224') (by sep_frame)
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (lagrangeSumAndFree_placed_sepWPp hA
        (st := M.stepEvents evsBasis (M.stepEvents (setupPtVecEvents pt.value.length) st))
        (PolyEncoder.enumeratePts 0 pt.value) hpts_ne hpts_bound
        s0 s2 hcl2 fsp accPtr basisPtr ptVecPtr (BitVec.ofNat 64 j) (s.readReg64 .x27)
        hfsp_align u16 u64 u72' u80' u640 u648
        (pointOf A.repAlloc (ptsBase + BitVec.ofNat 64 (24 * j)) pt ∗
         A.live ptVecPtr (4 * pt.value.length) 2 ∗
         ((fsp + 32#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
         ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
         ((fsp + 48#64) ↦₆₄ 2#64) ∗
         polyOf A.repAlloc ((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) ⟨[]⟩ ∗
         ((fsp + 88#64) ↦₆₄ ptsBase) ∗
         ((fsp + 1040#64) ↦₆₄ u1040') ∗ ((fsp + 1048#64) ↦₆₄ u1048') ∗
         ((fsp + 1056#64) ↦₆₄ u1056') ∗
         completePointsPolysPlacedAt ∗ Frame) R
        hpc2 hrun2 hsp2 htr2 hx0_2 (hx20_2.trans hx20_1) hx24_2 hx25_2 hx26_2
        (hx27_2.trans hx27_1) (hx28_2.trans hx28_1) hx29_2 hfit_sum ?_)
    intro evsSum s3 u656' u664' u672' henvSum hcl3 hpc3 hrun3 hsp3 htr3 hvregs3
      hx19_3 hx20_3 hx26_3 hx27_3 hx28_3 hx29_3
    have hx19_3' : s3.readReg64 .x19 = BitVec.ofNat 64 pt.value.length := by
      rw [← hpts_len, hx19_3]
    have hnewPoly := newPolyBufAt_pos_intro A.repAlloc accPtr pt hn0 hacc_ne emp
    simp only [RustCliAllocBudget.repAlloc_live] at hnewPoly
    apply SepWPp.fold hnewPoly (by sep_frame)
    have hptFold := ptVecBufAt_pos_fold A.repAlloc ptVecPtr pt hn0 hptVec_ne emp
    simp only [RustCliAllocBudget.repAlloc_live] at hptFold
    apply SepWPp.fold hptFold (by sep_frame)
    apply SepWPp.fold (memRegion_656_fold fsp u656' u664' u672') (by sep_frame)
    rw [hpts_len, stackAt_lagrangePrepare_split_alloc fsp]
    apply sepWPp_seq_lscl_b hcl3
      (mid := if j == 15 then (blkPl_416).base + 4424#64 else (blkPl_416).base + 976#64)
    refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (cleanupIter_placed_sepWP hA
        (st := M.stepEvents evsSum
          (M.stepEvents evsBasis (M.stepEvents (setupPtVecEvents pt.value.length) st)))
        s3 fsp ptsBase accPtr ptVecPtr hfsp_align j hj pt hbound
        (pointOf A.repAlloc (ptsBase + BitVec.ofNat 64 (24 * j)) pt ∗
         ((fsp + 16#64) ↦₆₄ BitVec.ofNat 64 j) ∗
         ((fsp + 24#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
         ((fsp + 48#64) ↦₆₄ 2#64) ∗
         ((fsp + 64#64) ↦₆₄ s.readReg64 .x27) ∗
         ((fsp + 72#64) ↦₆₄ basisPtr) ∗
         ((fsp + 80#64) ↦₆₄ ptVecPtr) ∗
         ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
         memRegion (fsp + 112#64) 120 ∗
         memRegion (fsp + 656#64) 24 ∗
         ((fsp + 1040#64) ↦₆₄ u1040') ∗ ((fsp + 1048#64) ↦₆₄ u1048') ∗
         ((fsp + 1056#64) ↦₆₄ u1056') ∗
         completePointsPolysPlacedAt ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
         memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
           (lagrangePrepareStack - allocHookStack) ∗ Frame)
        hpc3 hrun3 hsp3 hx19_3' hx20_3 hx26_3 hx28_3 ?_)
    intro evsClean s4 hevsClean hpc4 hrun4 hsp4 htr4 hvregs4
      hx19_4 hx20_4 hx27_4 hx28_4 hx29_4
    apply SepWP.done hpc4 hrun4
    intro hcl4
    have henvSum' :
        SeqEnv (RepeatSeqEnv pt.value.length (LagrangeSumStepEnv pt.value.length))
          FreeOnlyEvs evsSum := by
      simpa only [hpts_len] using henvSum
    have htail_tot :
        SeqEnv (RepeatSeqEnv pt.value.length (LagrangeSumStepEnv pt.value.length))
          FreeOnlyEvs (evsSum ++ evsClean) := by
      rcases henvSum' with hrep | ⟨e1, e2, rfl, hrep, hfree⟩
      · exact SeqEnv.append hrep hevsClean
      · rw [List.append_assoc]
        exact SeqEnv.append hrep (FreeOnlyEvs.append hfree hevsClean)
    have hiter_pos :
        PointsToPolysIterEnv pt.value.length
          ((setupPtVecEvents pt.value.length ++ evsBasis) ++ (evsSum ++ evsClean)) :=
      hextBasis' (evsSum ++ evsClean) htail_tot
    have hstep_tot :
        M.stepEvents evsClean
          (M.stepEvents evsSum
            (M.stepEvents evsBasis (M.stepEvents (setupPtVecEvents pt.value.length) st))) =
        M.stepEvents ((setupPtVecEvents pt.value.length ++ evsBasis) ++ (evsSum ++ evsClean)) st := by
      simp only [M.stepEvents_append]
    apply SepWPp.fold (stackAt_lagrangePrepare_fold_alloc fsp) (by sep_frame)
    refine SepWPp.weaken_pre (by rw [hstep_tot]; exact Entails.of_eq (by sep_ac_rfl))
      (hcont ((setupPtVecEvents pt.value.length ++ evsBasis) ++ (evsSum ++ evsClean))
        s4 (BitVec.ofNat 64 j) (BitVec.ofNat 64 pt.value.length)
        (BitVec.ofNat 64 (j + 1)) (BitVec.ofNat 64 pt.value.length)
        (s.readReg64 .x27) basisPtr ptVecPtr (BitVec.ofNat 64 pt.value.length)
        accPtr (BitVec.ofNat 64 pt.value.length) u1040' u1048' u1056'
        hiter_pos hcl4 hpc4 hrun4 hsp4 (htr4.trans htr3)
        (hvregs4.trans (hvregs3.trans (hvregs2.trans hvregs1))) hx19_4 hx20_4
        (hx27_4.trans hx27_3) hx28_4 (hx29_4.trans hx29_3))

/-! ## 2. Budget-Threaded 16-Iteration `points_to_polys` Loop (`+976 -> +4424`, Block `416`) -/

/-- Tail induction for `points_to_polys` (`+976 -> +4424`) over the remaining `rem + 1` points
    starting at index `j` (`j + (rem + 1) = 16`), stepping `st` along `PointsToPolysLoopEnv pts`. -/
theorem pointsToPolysLoop_tail_placed_sepWPp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {Q Q_panic : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (hcomp_ok : subroutine_ok ((blkPC_373).rebase (blkPl_373).base (Rust.withPanics ext))
      (blkPl_373).base (withLsCodeLoaded lsmpl (withVmPreserved lagrangeCompletePlacedSpec)))
    (s0 : State) (fsp ptsBase : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (R : SepProp) :
    ∀ (rem j : Nat) (pts : List Point)
      (_hlen : pts.length = rem + 1) (_hsum : j + (rem + 1) = 16)
      (_hbounds : ∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555)
      (st : M.σ) (s : State) (_hcl : LibsignalCodeLoaded lsmpl s.mem)
      (u16 u24 u32 u40 u64 u72 u80 u96 u640 u648 u1040 u1048 u1056 : BitVec 64)
      (Frame : SepProp),
      s.pc = (blkPl_416).base + 976#64 →
      s.status = .Running → s.sp = fsp → s.trace = s0.trace →
      s.readReg64 .x19 = ptsBase →
      s.readReg64 .x20 = BitVec.ofNat 64 j →
      s.readReg64 .x28 = 24#64 →
      s.readReg64 .x29 = fsp + 1104#64 →
      FitsEnv M lim st (PointsToPolysLoopEnv pts) →
      (∀ (evs : List AllocEvent) s_out
        u16' u24' u32' u40' u64' u72' u80' u96' u640' u648' u1040' u1048' u1056',
        PointsToPolysLoopEnv pts evs →
        LibsignalCodeLoaded lsmpl s_out.mem →
        s_out.pc = (blkPl_416).base + 4424#64 →
        s_out.status = .Running → s_out.sp = fsp → s_out.trace = s0.trace →
        calleeSavedVRegs s_out = calleeSavedVRegs s →
        s_out.readReg64 .x19 = ptsBase →
        s_out.readReg64 .x20 = 16#64 →
        s_out.readReg64 .x27 = s.readReg64 .x27 →
        s_out.readReg64 .x28 = 24#64 →
        s_out.readReg64 .x29 = fsp + 1104#64 →
        SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
          (s0.readReg64 (Reg.gpr 30#5)) s_out
          (A.pool lim (M.stepEvents evs st) s_out ∗
           pointListOf A.repAlloc (ptsBase + BitVec.ofNat 64 (24 * j)) pts ∗
           polyListOf A.repAlloc ((fsp + 256#64) + BitVec.ofNat 64 (24 * j))
             (pts.map pointToPolyPure) ∗
           ((fsp + 16#64) ↦₆₄ u16') ∗ ((fsp + 24#64) ↦₆₄ u24') ∗
           ((fsp + 32#64) ↦₆₄ u32') ∗ ((fsp + 40#64) ↦₆₄ u40') ∗
           ((fsp + 48#64) ↦₆₄ 2#64) ∗
           ((fsp + 64#64) ↦₆₄ u64') ∗ ((fsp + 72#64) ↦₆₄ u72') ∗ ((fsp + 80#64) ↦₆₄ u80') ∗
           ((fsp + 88#64) ↦₆₄ ptsBase) ∗ ((fsp + 96#64) ↦₆₄ u96') ∗
           memRegion (fsp + 112#64) 120 ∗
           ((fsp + 640#64) ↦₆₄ u640') ∗ ((fsp + 648#64) ↦₆₄ u648') ∗
           memRegion (fsp + 656#64) 24 ∗
           ((fsp + 1040#64) ↦₆₄ u1040') ∗ ((fsp + 1048#64) ↦₆₄ u1048') ∗
           ((fsp + 1056#64) ↦₆₄ u1056') ∗
           completePointsPolysPlacedAt ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
           stackAt fsp lagrangePrepareStack ∗ Frame)
          Q Q_panic) →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s
        (A.pool lim st s ∗
         pointListOf A.repAlloc (ptsBase + BitVec.ofNat 64 (24 * j)) pts ∗
         polyListOf A.repAlloc ((fsp + 256#64) + BitVec.ofNat 64 (24 * j))
           (List.replicate (rem + 1) ⟨[]⟩) ∗
         ((fsp + 16#64) ↦₆₄ u16) ∗ ((fsp + 24#64) ↦₆₄ u24) ∗
         ((fsp + 32#64) ↦₆₄ u32) ∗ ((fsp + 40#64) ↦₆₄ u40) ∗
         ((fsp + 48#64) ↦₆₄ 2#64) ∗
         ((fsp + 64#64) ↦₆₄ u64) ∗ ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ u80) ∗
         ((fsp + 88#64) ↦₆₄ ptsBase) ∗ ((fsp + 96#64) ↦₆₄ u96) ∗
         memRegion (fsp + 112#64) 120 ∗
         ((fsp + 640#64) ↦₆₄ u640) ∗ ((fsp + 648#64) ↦₆₄ u648) ∗
         memRegion (fsp + 656#64) 24 ∗
         ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗
         ((fsp + 1056#64) ↦₆₄ u1056) ∗
         completePointsPolysPlacedAt ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
         stackAt fsp lagrangePrepareStack ∗ Frame)
        Q Q_panic
  | 0, j, pts, hlen, hsum, hbounds, st, s, hcl,
    u16, u24, u32, u40, u64, u72, u80, u96, u640, u648, u1040, u1048, u1056, Frame,
    hpc, hrun, hsp, htrace, hx19, hx20, hx28, hx29, hfit, hcont => by
    cases pts with
    | nil => contradiction
    | cons pt pts_rest =>
      have hnil : pts_rest = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst hnil
      have hj15 : j = 15 := by omega
      subst hj15
      have hbound : pt.value.length ≤ 0x0555555555555555 :=
        hbounds pt List.mem_cons_self
      have hfit1 : FitsEnv M lim st (PointsToPolysIterEnv pt.value.length) :=
        fun evs h1 => hfit evs (Or.inl h1)
      dsimp only [List.replicate, List.map, pointListOf, polyListOf, arrayAt] at hcont ⊢
      simp only [sepConj_emp] at hcont ⊢
      exact pointsToPolysStep_placed_sepWPp hA hcomp_ok s0 s hcl fsp ptsBase hfsp_align
        15 (by decide) pt hbound
        u16 u24 u32 u40 u64 u72 u80 u96 u640 u648 u1040 u1048 u1056 Frame R
        hpc hrun hsp htrace hx19 hx20 hx28 hx29 hfit1
        (fun evs s_out u16' u24' u32' u40' u64' u72' u80' u96' u640' u648' u1040' u1048' u1056'
          h1 hcl_out hpc_out hrun_out hsp_out htr_out hvregs_out
          hx19_out hx20_out hx27_out hx28_out hx29_out =>
          hcont evs s_out u16' u24' u32' u40' u64' u72' u80' u96' u640' u648' u1040' u1048' u1056'
            (Or.inl h1) hcl_out hpc_out hrun_out hsp_out htr_out hvregs_out
            hx19_out hx20_out hx27_out hx28_out hx29_out)
  | rem' + 1, j, pts, hlen, hsum, hbounds, st, s, hcl,
    u16, u24, u32, u40, u64, u72, u80, u96, u640, u648, u1040, u1048, u1056, Frame,
    hpc, hrun, hsp, htrace, hx19, hx20, hx28, hx29, hfit, hcont => by
    cases pts with
    | nil => contradiction
    | cons pt pts_rest =>
      have hlen_rest : pts_rest.length = rem' + 1 := by simpa using hlen
      have hj16 : j < 16 := by omega
      have hj_ne15 : (j == 15) = false := beq_eq_false_iff_ne.mpr (by omega)
      have hbound : pt.value.length ≤ 0x0555555555555555 :=
        hbounds pt List.mem_cons_self
      have hbounds_rest : ∀ pt' ∈ pts_rest, pt'.value.length ≤ 0x0555555555555555 :=
        fun pt' hmem => hbounds pt' (List.mem_cons_of_mem pt hmem)
      have hfit1 : FitsEnv M lim st (PointsToPolysIterEnv pt.value.length) :=
        fun evs1 h1 => hfit evs1 (Or.inl h1)
      rw [List.replicate_succ,
          pointListOf_cons_mul24_off A.repAlloc ptsBase j pt pts_rest,
          polyListOf_cons_mul24_off A.repAlloc (fsp + 256#64) j ⟨[]⟩ (List.replicate (rem' + 1) ⟨[]⟩)]
      refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (pointsToPolysStep_placed_sepWPp hA hcomp_ok s0 s hcl fsp ptsBase hfsp_align j hj16 pt hbound
          u16 u24 u32 u40 u64 u72 u80 u96 u640 u648 u1040 u1048 u1056
          (pointListOf A.repAlloc (ptsBase + BitVec.ofNat 64 (24 * (j + 1))) pts_rest ∗
           polyListOf A.repAlloc ((fsp + 256#64) + BitVec.ofNat 64 (24 * (j + 1)))
             (List.replicate (rem' + 1) ⟨[]⟩) ∗
           Frame) R
          hpc hrun hsp htrace hx19 hx20 hx28 hx29 hfit1 ?_)
      intro evs1 s_mid
        u16_m u24_m u32_m u40_m u64_m u72_m u80_m u96_m u640_m u648_m u1040_m u1048_m u1056_m
        h1 hcl_m hpc_m hrun_m hsp_m htr_m hvregs_m hx19_m hx20_m hx27_m hx28_m hx29_m
      rw [hj_ne15] at hpc_m
      have hfit_rest :
          FitsEnv M lim (M.stepEvents evs1 st) (PointsToPolysLoopEnv pts_rest) :=
        fun evs2 h2 =>
          ((fitsEvents_append M lim evs1 evs2 st).mp (hfit (evs1 ++ evs2) (SeqEnv.append h1 h2))).2
      refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (pointsToPolysLoop_tail_placed_sepWPp hA hcomp_ok s0 fsp ptsBase hfsp_align R
          rem' (j + 1) pts_rest hlen_rest (by omega) hbounds_rest
          (M.stepEvents evs1 st) s_mid hcl_m
          u16_m u24_m u32_m u40_m u64_m u72_m u80_m u96_m u640_m u648_m u1040_m u1048_m u1056_m
          (pointOf A.repAlloc (ptsBase + BitVec.ofNat 64 (24 * j)) pt ∗
           polyOf A.repAlloc ((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) (pointToPolyPure pt) ∗
           Frame)
          hpc_m hrun_m hsp_m htr_m hx19_m hx20_m hx28_m hx29_m hfit_rest ?_)
      intro evs2 s_out u16' u24' u32' u40' u64' u72' u80' u96' u640' u648' u1040' u1048' u1056'
        h2 hcl_out hpc_out hrun_out hsp_out htr_out hvregs_out
        hx19_out hx20_out hx27_out hx28_out hx29_out
      have hstep12 : M.stepEvents evs2 (M.stepEvents evs1 st) = M.stepEvents (evs1 ++ evs2) st :=
        (M.stepEvents_append evs1 evs2 st).symm
      have hfold :
          A.pool lim (M.stepEvents evs2 (M.stepEvents evs1 st)) s_out ∗
          pointListOf A.repAlloc (ptsBase + BitVec.ofNat 64 (24 * (j + 1))) pts_rest ∗
          polyListOf A.repAlloc ((fsp + 256#64) + BitVec.ofNat 64 (24 * (j + 1)))
            (pts_rest.map pointToPolyPure) ∗
          ((fsp + 16#64) ↦₆₄ u16') ∗ ((fsp + 24#64) ↦₆₄ u24') ∗
          ((fsp + 32#64) ↦₆₄ u32') ∗ ((fsp + 40#64) ↦₆₄ u40') ∗
          ((fsp + 48#64) ↦₆₄ 2#64) ∗
          ((fsp + 64#64) ↦₆₄ u64') ∗ ((fsp + 72#64) ↦₆₄ u72') ∗ ((fsp + 80#64) ↦₆₄ u80') ∗
          ((fsp + 88#64) ↦₆₄ ptsBase) ∗ ((fsp + 96#64) ↦₆₄ u96') ∗
          memRegion (fsp + 112#64) 120 ∗
          ((fsp + 640#64) ↦₆₄ u640') ∗ ((fsp + 648#64) ↦₆₄ u648') ∗
          memRegion (fsp + 656#64) 24 ∗
          ((fsp + 1040#64) ↦₆₄ u1040') ∗ ((fsp + 1048#64) ↦₆₄ u1048') ∗
          ((fsp + 1056#64) ↦₆₄ u1056') ∗
          completePointsPolysPlacedAt ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
          stackAt fsp lagrangePrepareStack ∗
          (pointOf A.repAlloc (ptsBase + BitVec.ofNat 64 (24 * j)) pt ∗
           polyOf A.repAlloc ((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) (pointToPolyPure pt) ∗
           Frame) =
          A.pool lim (M.stepEvents (evs1 ++ evs2) st) s_out ∗
          pointListOf A.repAlloc (ptsBase + BitVec.ofNat 64 (24 * j)) (pt :: pts_rest) ∗
          polyListOf A.repAlloc ((fsp + 256#64) + BitVec.ofNat 64 (24 * j))
            ((pt :: pts_rest).map pointToPolyPure) ∗
          ((fsp + 16#64) ↦₆₄ u16') ∗ ((fsp + 24#64) ↦₆₄ u24') ∗
          ((fsp + 32#64) ↦₆₄ u32') ∗ ((fsp + 40#64) ↦₆₄ u40') ∗
          ((fsp + 48#64) ↦₆₄ 2#64) ∗
          ((fsp + 64#64) ↦₆₄ u64') ∗ ((fsp + 72#64) ↦₆₄ u72') ∗ ((fsp + 80#64) ↦₆₄ u80') ∗
          ((fsp + 88#64) ↦₆₄ ptsBase) ∗ ((fsp + 96#64) ↦₆₄ u96') ∗
          memRegion (fsp + 112#64) 120 ∗
          ((fsp + 640#64) ↦₆₄ u640') ∗ ((fsp + 648#64) ↦₆₄ u648') ∗
          memRegion (fsp + 656#64) 24 ∗
          ((fsp + 1040#64) ↦₆₄ u1040') ∗ ((fsp + 1048#64) ↦₆₄ u1048') ∗
          ((fsp + 1056#64) ↦₆₄ u1056') ∗
          completePointsPolysPlacedAt ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
          stackAt fsp lagrangePrepareStack ∗ Frame := by
        rw [hstep12, List.map_cons,
            pointListOf_cons_mul24_off A.repAlloc ptsBase j pt pts_rest,
            polyListOf_cons_mul24_off A.repAlloc (fsp + 256#64) j (pointToPolyPure pt)
              (pts_rest.map pointToPolyPure)]
        sep_ac_rfl
      refine SepWPp.weaken_pre (Entails.of_eq hfold)
        (hcont (evs1 ++ evs2) s_out
          u16' u24' u32' u40' u64' u72' u80' u96' u640' u648' u1040' u1048' u1056'
          (SeqEnv.append h1 h2) hcl_out hpc_out hrun_out hsp_out htr_out
          (hvregs_out.trans hvregs_m) hx19_out hx20_out (hx27_out.trans hx27_m)
          hx28_out hx29_out)

/-- Full budget-threaded 16-iteration `points_to_polys` loop (`+976 -> +4424`) on
    `polyListOf A.repAlloc (fsp + 256) (List.replicate 16 ⟨[]⟩)`, stepping `st` along
    `PointsToPolysLoopEnv pts`. -/
theorem pointsToPolysLoop_polyList_placed_sepWPp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)} {Q Q_panic : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (hcomp_ok : subroutine_ok ((blkPC_373).rebase (blkPl_373).base (Rust.withPanics ext))
      (blkPl_373).base (withLsCodeLoaded lsmpl (withVmPreserved lagrangeCompletePlacedSpec)))
    (s0 s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (fsp ptsBase : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (pts : List Point) (hlen : pts.length = 16)
    (hbounds : ∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555)
    (u16 u24 u32 u40 u64 u72 u80 u96 u640 u648 u1040 u1048 u1056 : BitVec 64)
    (Frame R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 976#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (htrace : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = ptsBase)
    (hx20 : s.readReg64 .x20 = 0#64)
    (hx28 : s.readReg64 .x28 = 24#64)
    (hx29 : s.readReg64 .x29 = fsp + 1104#64)
    (hfit : FitsEnv M lim st (PointsToPolysLoopEnv pts))
    (hcont : ∀ (evs : List AllocEvent) s_out
      u16' u24' u32' u40' u64' u72' u80' u96' u640' u648' u1040' u1048' u1056',
      PointsToPolysLoopEnv pts evs →
      LibsignalCodeLoaded lsmpl s_out.mem →
      s_out.pc = (blkPl_416).base + 4424#64 →
      s_out.status = .Running → s_out.sp = fsp → s_out.trace = s0.trace →
      calleeSavedVRegs s_out = calleeSavedVRegs s →
      s_out.readReg64 .x19 = ptsBase →
      s_out.readReg64 .x20 = 16#64 →
      s_out.readReg64 .x27 = s.readReg64 .x27 →
      s_out.readReg64 .x28 = 24#64 →
      s_out.readReg64 .x29 = fsp + 1104#64 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s_out
        (A.pool lim (M.stepEvents evs st) s_out ∗
         pointListOf A.repAlloc ptsBase pts ∗
         polyListOf A.repAlloc (fsp + 256#64) (pts.map pointToPolyPure) ∗
         ((fsp + 16#64) ↦₆₄ u16') ∗ ((fsp + 24#64) ↦₆₄ u24') ∗
         ((fsp + 32#64) ↦₆₄ u32') ∗ ((fsp + 40#64) ↦₆₄ u40') ∗
         ((fsp + 48#64) ↦₆₄ 2#64) ∗
         ((fsp + 64#64) ↦₆₄ u64') ∗ ((fsp + 72#64) ↦₆₄ u72') ∗ ((fsp + 80#64) ↦₆₄ u80') ∗
         ((fsp + 88#64) ↦₆₄ ptsBase) ∗ ((fsp + 96#64) ↦₆₄ u96') ∗
         memRegion (fsp + 112#64) 120 ∗
         ((fsp + 640#64) ↦₆₄ u640') ∗ ((fsp + 648#64) ↦₆₄ u648') ∗
         memRegion (fsp + 656#64) 24 ∗
         ((fsp + 1040#64) ↦₆₄ u1040') ∗ ((fsp + 1048#64) ↦₆₄ u1048') ∗
         ((fsp + 1056#64) ↦₆₄ u1056') ∗
         completePointsPolysPlacedAt ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
         stackAt fsp lagrangePrepareStack ∗ Frame)
        Q Q_panic) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool lim st s ∗
       pointListOf A.repAlloc ptsBase pts ∗
       polyListOf A.repAlloc (fsp + 256#64) (List.replicate 16 ⟨[]⟩) ∗
       ((fsp + 16#64) ↦₆₄ u16) ∗ ((fsp + 24#64) ↦₆₄ u24) ∗
       ((fsp + 32#64) ↦₆₄ u32) ∗ ((fsp + 40#64) ↦₆₄ u40) ∗
       ((fsp + 48#64) ↦₆₄ 2#64) ∗
       ((fsp + 64#64) ↦₆₄ u64) ∗ ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ u80) ∗
       ((fsp + 88#64) ↦₆₄ ptsBase) ∗ ((fsp + 96#64) ↦₆₄ u96) ∗
       memRegion (fsp + 112#64) 120 ∗
       ((fsp + 640#64) ↦₆₄ u640) ∗ ((fsp + 648#64) ↦₆₄ u648) ∗
       memRegion (fsp + 656#64) 24 ∗
       ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗
       ((fsp + 1056#64) ↦₆₄ u1056) ∗
       completePointsPolysPlacedAt ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
       stackAt fsp lagrangePrepareStack ∗ Frame)
      Q Q_panic := by
  have h0_pts : ptsBase = ptsBase + BitVec.ofNat 64 (24 * 0) := by simp
  have h0_fsp : fsp + 256#64 = (fsp + 256#64) + BitVec.ofNat 64 (24 * 0) := by simp
  refine SepWPp.weaken_pre (Entails.of_eq (by rw [← h0_pts, ← h0_fsp]))
    (pointsToPolysLoop_tail_placed_sepWPp hA hcomp_ok s0 fsp ptsBase hfsp_align R 15 0 pts
      hlen rfl hbounds st s hcl u16 u24 u32 u40 u64 u72 u80 u96 u640 u648 u1040 u1048 u1056 Frame
      hpc hrun hsp htrace hx19 hx20 hx28 hx29 hfit ?_)
  intro evs s_out u16' u24' u32' u40' u64' u72' u80' u96' u640' u648' u1040' u1048' u1056'
    hevs hcl_out hpc_out hrun_out hsp_out htr_out hvregs_out
    hx19_out hx20_out hx27_out hx28_out hx29_out
  rw [← h0_pts, ← h0_fsp]
  exact hcont evs s_out u16' u24' u32' u40' u64' u72' u80' u96' u640' u648' u1040' u1048' u1056'
    hevs hcl_out hpc_out hrun_out hsp_out htr_out hvregs_out
    hx19_out hx20_out hx27_out hx28_out hx29_out

/-- Full budget-threaded 16-iteration `points_to_polys` loop (`+976 -> +4424`):
    converts `pointListOf A.repAlloc ptsBase pts` (`pts.length = 16`) and
    `zeroPolySlotsAt A.repAlloc (fsp + 256#64) 16` into
    `polyListOf A.repAlloc (fsp + 256#64) (pts.map pointToPolyPure)`, stepping `st` along
    `PointsToPolysLoopEnv pts`. -/
theorem pointsToPolysLoop_placed_sepWPp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)} {Q Q_panic : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (hcomp_ok : subroutine_ok ((blkPC_373).rebase (blkPl_373).base (Rust.withPanics ext))
      (blkPl_373).base (withLsCodeLoaded lsmpl (withVmPreserved lagrangeCompletePlacedSpec)))
    (s0 s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (fsp ptsBase : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (pts : List Point) (hlen : pts.length = 16)
    (hbounds : ∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555)
    (u16 u24 u32 u40 u64 u72 u80 u96 u640 u648 u1040 u1048 u1056 : BitVec 64)
    (Frame R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 976#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (htrace : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = ptsBase)
    (hx20 : s.readReg64 .x20 = 0#64)
    (hx28 : s.readReg64 .x28 = 24#64)
    (hx29 : s.readReg64 .x29 = fsp + 1104#64)
    (hfit : FitsEnv M lim st (PointsToPolysLoopEnv pts))
    (hcont : ∀ (evs : List AllocEvent) s_out
      u16' u24' u32' u40' u64' u72' u80' u96' u640' u648' u1040' u1048' u1056',
      PointsToPolysLoopEnv pts evs →
      LibsignalCodeLoaded lsmpl s_out.mem →
      s_out.pc = (blkPl_416).base + 4424#64 →
      s_out.status = .Running → s_out.sp = fsp → s_out.trace = s0.trace →
      calleeSavedVRegs s_out = calleeSavedVRegs s →
      s_out.readReg64 .x19 = ptsBase →
      s_out.readReg64 .x20 = 16#64 →
      s_out.readReg64 .x27 = s.readReg64 .x27 →
      s_out.readReg64 .x28 = 24#64 →
      s_out.readReg64 .x29 = fsp + 1104#64 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s_out
        (A.pool lim (M.stepEvents evs st) s_out ∗
         pointListOf A.repAlloc ptsBase pts ∗
         polyListOf A.repAlloc (fsp + 256#64) (pts.map pointToPolyPure) ∗
         ((fsp + 16#64) ↦₆₄ u16') ∗ ((fsp + 24#64) ↦₆₄ u24') ∗
         ((fsp + 32#64) ↦₆₄ u32') ∗ ((fsp + 40#64) ↦₆₄ u40') ∗
         ((fsp + 48#64) ↦₆₄ 2#64) ∗
         ((fsp + 64#64) ↦₆₄ u64') ∗ ((fsp + 72#64) ↦₆₄ u72') ∗ ((fsp + 80#64) ↦₆₄ u80') ∗
         ((fsp + 88#64) ↦₆₄ ptsBase) ∗ ((fsp + 96#64) ↦₆₄ u96') ∗
         memRegion (fsp + 112#64) 120 ∗
         ((fsp + 640#64) ↦₆₄ u640') ∗ ((fsp + 648#64) ↦₆₄ u648') ∗
         memRegion (fsp + 656#64) 24 ∗
         ((fsp + 1040#64) ↦₆₄ u1040') ∗ ((fsp + 1048#64) ↦₆₄ u1048') ∗
         ((fsp + 1056#64) ↦₆₄ u1056') ∗
         completePointsPolysPlacedAt ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
         stackAt fsp lagrangePrepareStack ∗ Frame)
        Q Q_panic) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool lim st s ∗
       pointListOf A.repAlloc ptsBase pts ∗
       zeroPolySlotsAt A.repAlloc (fsp + 256#64) 16 ∗
       ((fsp + 16#64) ↦₆₄ u16) ∗ ((fsp + 24#64) ↦₆₄ u24) ∗
       ((fsp + 32#64) ↦₆₄ u32) ∗ ((fsp + 40#64) ↦₆₄ u40) ∗
       ((fsp + 48#64) ↦₆₄ 2#64) ∗
       ((fsp + 64#64) ↦₆₄ u64) ∗ ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ u80) ∗
       ((fsp + 88#64) ↦₆₄ ptsBase) ∗ ((fsp + 96#64) ↦₆₄ u96) ∗
       memRegion (fsp + 112#64) 120 ∗
       ((fsp + 640#64) ↦₆₄ u640) ∗ ((fsp + 648#64) ↦₆₄ u648) ∗
       memRegion (fsp + 656#64) 24 ∗
       ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗
       ((fsp + 1056#64) ↦₆₄ u1056) ∗
       completePointsPolysPlacedAt ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
       stackAt fsp lagrangePrepareStack ∗ Frame)
      Q Q_panic := by
  apply SepWPp.fold (zeroPolySlotsAt_entails_polyListOf A.repAlloc 16 (fsp + 256#64)) (by sep_frame)
  exact SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (pointsToPolysLoop_polyList_placed_sepWPp hA hcomp_ok s0 s hcl fsp ptsBase hfsp_align pts hlen
      hbounds u16 u24 u32 u40 u64 u72 u80 u96 u640 u648 u1040 u1048 u1056 Frame R
      hpc hrun hsp htrace hx19 hx20 hx28 hx29 hfit hcont)

/-! ## 3. Bundled Placed Loop Contract (`PointsToPolysLoopPlacedBudgetProp`) -/

/-- Relocatable `[LibsignalPlacement]` budget-threaded contract for the 16-iteration
    `points_to_polys` conversion loop (`+976 -> +4424` in Block `416`), stepping `st` along
    `PointsToPolysLoopEnv pts`. -/
def PointsToPolysLoopPlacedBudgetProp [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  ∀ {st : M.σ} {Q Q_panic : State → SepProp → Prop}
    (s0 s : State) (_hcl : LibsignalCodeLoaded lsmpl s.mem)
    (fsp ptsBase : BitVec 64)
    (_hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (pts : List Point) (_hlen : pts.length = 16)
    (_hbounds : ∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555)
    (u16 u24 u32 u40 u64 u72 u80 u96 u640 u648 u1040 u1048 u1056 : BitVec 64)
    (Frame R : SepProp)
    (_hpc : s.pc = (blkPl_416).base + 976#64)
    (_hrun : s.status = .Running) (_hsp : s.sp = fsp) (_htrace : s.trace = s0.trace)
    (_hx19 : s.readReg64 .x19 = ptsBase)
    (_hx20 : s.readReg64 .x20 = 0#64)
    (_hx28 : s.readReg64 .x28 = 24#64)
    (_hx29 : s.readReg64 .x29 = fsp + 1104#64)
    (_hfit : FitsEnv M lim st (PointsToPolysLoopEnv pts)),
    (∀ (evs : List AllocEvent) s_out
      u16' u24' u32' u40' u64' u72' u80' u96' u640' u648' u1040' u1048' u1056',
      PointsToPolysLoopEnv pts evs →
      LibsignalCodeLoaded lsmpl s_out.mem →
      s_out.pc = (blkPl_416).base + 4424#64 →
      s_out.status = .Running → s_out.sp = fsp → s_out.trace = s0.trace →
      calleeSavedVRegs s_out = calleeSavedVRegs s →
      s_out.readReg64 .x19 = ptsBase →
      s_out.readReg64 .x20 = 16#64 →
      s_out.readReg64 .x27 = s.readReg64 .x27 →
      s_out.readReg64 .x28 = 24#64 →
      s_out.readReg64 .x29 = fsp + 1104#64 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s_out
        (A.pool lim (M.stepEvents evs st) s_out ∗
         pointListOf A.repAlloc ptsBase pts ∗
         polyListOf A.repAlloc (fsp + 256#64) (pts.map pointToPolyPure) ∗
         ((fsp + 16#64) ↦₆₄ u16') ∗ ((fsp + 24#64) ↦₆₄ u24') ∗
         ((fsp + 32#64) ↦₆₄ u32') ∗ ((fsp + 40#64) ↦₆₄ u40') ∗
         ((fsp + 48#64) ↦₆₄ 2#64) ∗
         ((fsp + 64#64) ↦₆₄ u64') ∗ ((fsp + 72#64) ↦₆₄ u72') ∗ ((fsp + 80#64) ↦₆₄ u80') ∗
         ((fsp + 88#64) ↦₆₄ ptsBase) ∗ ((fsp + 96#64) ↦₆₄ u96') ∗
         memRegion (fsp + 112#64) 120 ∗
         ((fsp + 640#64) ↦₆₄ u640') ∗ ((fsp + 648#64) ↦₆₄ u648') ∗
         memRegion (fsp + 656#64) 24 ∗
         ((fsp + 1040#64) ↦₆₄ u1040') ∗ ((fsp + 1048#64) ↦₆₄ u1048') ∗
         ((fsp + 1056#64) ↦₆₄ u1056') ∗
         completePointsPolysPlacedAt ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
         stackAt fsp lagrangePrepareStack ∗ Frame)
        Q Q_panic) →
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool lim st s ∗
       pointListOf A.repAlloc ptsBase pts ∗
       polyListOf A.repAlloc (fsp + 256#64) (List.replicate 16 ⟨[]⟩) ∗
       ((fsp + 16#64) ↦₆₄ u16) ∗ ((fsp + 24#64) ↦₆₄ u24) ∗
       ((fsp + 32#64) ↦₆₄ u32) ∗ ((fsp + 40#64) ↦₆₄ u40) ∗
       ((fsp + 48#64) ↦₆₄ 2#64) ∗
       ((fsp + 64#64) ↦₆₄ u64) ∗ ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ u80) ∗
       ((fsp + 88#64) ↦₆₄ ptsBase) ∗ ((fsp + 96#64) ↦₆₄ u96) ∗
       memRegion (fsp + 112#64) 120 ∗
       ((fsp + 640#64) ↦₆₄ u640) ∗ ((fsp + 648#64) ↦₆₄ u648) ∗
       memRegion (fsp + 656#64) 24 ∗
       ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗
       ((fsp + 1056#64) ↦₆₄ u1056) ∗
       completePointsPolysPlacedAt ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
       stackAt fsp lagrangePrepareStack ∗ Frame)
      Q Q_panic

/-- Discharges `PointsToPolysLoopPlacedBudgetProp M A lim ext` under `[LibsignalPlacement]` via
    `pointsToPolysLoop_polyList_placed_sepWPp`. -/
theorem pointsToPolysLoop_placed_prop [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (hcomp_ok : subroutine_ok ((blkPC_373).rebase (blkPl_373).base (Rust.withPanics ext))
      (blkPl_373).base (withLsCodeLoaded lsmpl (withVmPreserved lagrangeCompletePlacedSpec))) :
    PointsToPolysLoopPlacedBudgetProp M A lim ext :=
  fun s0 s hcl fsp ptsBase hfsp_align pts hlen hbounds
      u16 u24 u32 u40 u64 u72 u80 u96 u640 u648 u1040 u1048 u1056
      Frame R hpc hrun hsp htrace hx19 hx20 hx28 hx29 hfit hcont =>
    pointsToPolysLoop_polyList_placed_sepWPp hA hcomp_ok s0 s hcl fsp ptsBase hfsp_align
      pts hlen hbounds u16 u24 u32 u40 u64 u72 u80 u96 u640 u648 u1040 u1048 u1056
      Frame R hpc hrun hsp htrace hx19 hx20 hx28 hx29 hfit hcont

end LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysProofPlacedBBudget

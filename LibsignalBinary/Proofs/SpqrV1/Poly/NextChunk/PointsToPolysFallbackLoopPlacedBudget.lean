/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Block416SegBudget
public meta import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Block416SegBudget -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.EpiloguePlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysFallbackLoop
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysFallbackLoopPlaced
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangeComplete.Proof
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysDefs
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysFallbackPlaced
import ProofLib.SepLogic.WPp

/-!
# `<PolyEncoder as Encoder>::next_chunk` (Block `416`): Budget-Threaded Placed `lagrangeBasisLoop`

Relocatable `[LibsignalPlacement]` verification of the dynamic Lagrange basis loop
(`+4128 -> +4368`) threading `RustCliAllocBudget M`, `BudgetLimits`, and `FallbackBasisStepEnv`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysFallbackLoopPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalCodeLoaded LibsignalHooks LibsignalPlacement blkPC_373 blkPC_416 blkPl_373 blkPl_416
   lscall_blk_cl lsmpl lsρ withLsCodeLoaded withMemEq)
open scoped CryptoVerification
open scoped CryptoVerification.CodeLayout
open CryptoVerification.RustHeap (LayoutOk RustAlloc allocHookStack arrayAt)
open CryptoVerification.LibsignalTripleRatchet (sessionMemcpySpec)
open CryptoVerification.LibsignalSpqrV1 (GF16 Poly Pt)
open CryptoVerification.SpqrV1.Alloc
  (spqrMemcpySym spqrRustAllocSym spqrRustNoAllocShimSym)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Poly
  (gf16SliceAt polyListOf polyOf ptSliceAt)
open CryptoVerification.SpqrV1.Poly.ComputeAt
  (readReg32_setMem_pre readReg64_setMem_pre readReg_setMem_pre sp_setMem_pre spqrRustDeallocSym)
open CryptoVerification.SpqrV1.Poly.LagrangeComplete
  (LagrangeCompleteArgs lagrangeCompletePlacedSpec lagrangeCompletePure lagrangeCompleteStack)
open CryptoVerification.SpqrV1.Poly.LagrangePrepare
  (LagrangePrepareArgs lagrangePreparePure lagrangePreparePure_length lagrangePrepareStack
   readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre readReg64_setPC_pre
   readReg_setMem_setPC_pre readReg_setPC_pre sp_setMem_setPC_pre sp_setPC_pre)
open CryptoVerification.SpqrV1.Poly.NextChunk
  (adds_one_ne_zero bit62_shl_one_false gf16SliceAt_cons_memRegion2 gf16SliceBytes
   lagrangeBasisFrom lagrangeComplete_prepare_head_tail lagrangeInterpolatePtPure
   lagrangeInterpolatePtPure_length memRegion_recombine_prepare memRegion_split_24_succ
   memRegion_split_polyHeader_fbl ofNat_add_one_eq_succ_fb ofNat_ne_ofNat_false ofNat_pos_ne_zero
   ofNat_succ_add_neg_one_fb ofNat_succ_ne_zero ofNat_succ_sub_one_fb
   polyHeader_entails_memRegion24_off polyOf_of_pointsToBytes polyOf_prepare_unfold
   sepConj_mono_fbl sepWP_exists_left_sep sepWPp_seq_lscl_fb shl_one_cap_toNat_nat
   shl_one_ofNat_eq shl_one_ofNat_eq_nat stackAt_alloc_to_prepare stackAt_complete_to_alloc
   stackAt_lagrangePrepare_split_complete subroutine_ok_keep_lscl ult_max_2n_false withPostLsCl)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvent FitsEvents
   FreeOnlyEvs RustCliAllocBudget RustLayoutOk SeqEnv VmPreserved
   fitsEvents_append rustAllocEvents rustCliAllocNoOomSpec rustCliDeallocBudgetSpec
   rustDeallocEvents)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException)
open LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.DefsBudget
  (LagrangePrepareEnv lagrangePreparePlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Block416SegBudget (sepWP_seg_416)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsBudget
  (FallbackBasisStepEnv RepeatSeqEnv fallbackBasisStepEnv_nonempty repeatSeqEnv_nonempty)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.EpiloguePlacedBudget (AllocContractsPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (noAllocShimBudgetSpec noAllocShimSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyBudgetSpec)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

private theorem pc_setMem_pre (s : State) (m : Memory) : (s.setMem m).pc = s.pc := by cases s; rfl
private theorem status_setMem_pre (s : State) (m : Memory) : (s.setMem m).status = s.status := by
  cases s; rfl
private theorem pstate_setMem_pre (s : State) (m : Memory) : (s.setMem m).pstate = s.pstate := by
  cases s; rfl
private theorem trace_setMem_pre (s : State) (m : Memory) : (s.setMem m).trace = s.trace := by
  cases s; rfl
private theorem fs_setMem_pre (s : State) (m : Memory) : (s.setMem m).fs = s.fs := by cases s; rfl
private theorem sigActions_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).sigActions = s.sigActions := by cases s; rfl
private theorem tpidrEl0_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).tpidrEl0 = s.tpidrEl0 := by cases s; rfl
private theorem brkStart_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).brkStart = s.brkStart := by cases s; rfl
private theorem oracle_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).oracle = s.oracle := by cases s; rfl
private theorem symtab_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).symtab = s.symtab := by cases s; rfl
private theorem calleeSavedVRegs_setMem_pre (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := by cases s; rfl

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre pc_setMem_pre status_setMem_pre pstate_setMem_pre trace_setMem_pre
  fs_setMem_pre sigActions_setMem_pre tpidrEl0_setMem_pre brkStart_setMem_pre
  oracle_setMem_pre symtab_setMem_pre calleeSavedVRegs_setMem_pre
  readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

@[local arm64_norm, local wp_norm] private theorem exists_pow_two_eq_two_fbl_bud :
    (∃ k : Nat, 2 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨1, rfl⟩

@[local arm64_norm, local wp_norm] private theorem exists_pow_two_eq_eight_fbl_bud :
    (∃ k : Nat, 8 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨3, rfl⟩

attribute [local simp, local arm64_norm, local wp_norm]
  ofNat_succ_sub_one_fb ofNat_succ_add_neg_one_fb ofNat_add_one_eq_succ_fb
  shl_one_ofNat_eq shl_one_ofNat_eq_nat

attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  conditionHolds_mi_subsPState64 conditionHolds_pl_subsPState64
  conditionHolds_eq_addsPState64 conditionHolds_ne_addsPState64

/-! ## 1. Envelope Splitting Lemmas -/

/-- Extract the two allocation `FitsEvents` obligations of one `FallbackBasisStepEnv` step. -/
theorem fitsEvents_of_fitsEnv_fallbackBasisStep {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} (k : Nat) (hfit : FitsEnv M lim st (FallbackBasisStepEnv k)) :
    FitsEvents M lim st (rustAllocEvents (2 * (k + 1)) 2) ∧
      FitsEvents M lim (M.stepEvents (rustAllocEvents (2 * (k + 1)) 2) st)
        (rustAllocEvents (2 * k) 2) :=
  (fitsEvents_append M lim _ _ st).mp (hfit _ (Or.inl rfl))

/-- Extract `FitsEnv` for a single step from `RepeatSeqEnv 1 E`. -/
theorem fitsEnv_of_repeatSeqEnv_one {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {E : List AllocEvent → Prop} (hfit : FitsEnv M lim st (RepeatSeqEnv 1 E)) :
    FitsEnv M lim st E := by
  intro evs hevs
  have h1 : RepeatSeqEnv 1 E (evs ++ []) := SeqEnv.append hevs rfl
  rw [List.append_nil] at h1
  exact hfit evs h1

/-- Split `FitsEnv` on `RepeatSeqEnv (r + 2) (FallbackBasisStepEnv k)` into the head step and
    continuation `RepeatSeqEnv (r + 1) (FallbackBasisStepEnv k)` after any `evs1` satisfying
    `FallbackBasisStepEnv k`. -/
theorem fitsEnv_repeatSeqEnv_succ {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (r k : Nat) (hfit : FitsEnv M lim st (RepeatSeqEnv (r + 2) (FallbackBasisStepEnv k))) :
    FitsEnv M lim st (FallbackBasisStepEnv k) ∧
      ∀ evs1 : List AllocEvent, FallbackBasisStepEnv k evs1 →
        FitsEnv M lim (M.stepEvents evs1 st) (RepeatSeqEnv (r + 1) (FallbackBasisStepEnv k)) := by
  constructor
  · intro evs1 hevs1
    rcases repeatSeqEnv_nonempty (fallbackBasisStepEnv_nonempty k) (r + 1) with ⟨evs2, hevs2⟩
    exact ((fitsEvents_append M lim evs1 evs2 st).mp (hfit _ (SeqEnv.append hevs1 hevs2))).1
  · intro evs1 hevs1 evs2 hevs2
    exact ((fitsEvents_append M lim evs1 evs2 st).mp (hfit _ (SeqEnv.append hevs1 hevs2))).2

example : ∃ evs, RepeatSeqEnv 2 (FallbackBasisStepEnv 8) evs :=
  repeatSeqEnv_nonempty (fallbackBasisStepEnv_nonempty 8) 2

/-! ## 2. Block-416 `SepWPp` Segment Combinator -/

private theorem sepWPp_seg_lscl_416 [LibsignalPlacement] {H : LibsignalHooks}
    {mid ret : BitVec 64} {s : State} {Pre : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hseg : ∀ m_strip : Memory,
      SepWP ((blkPC_416).rebase (blkPl_416).base (hooksException H)) mid (s.setMem m_strip) Pre
        (fun sm' Pm =>
          ∀ m_real : Memory,
            ProofLib.NonSyscallPreserved s (sm'.setMem m_real) →
            LibsignalCodeLoaded lsmpl m_real →
            SepWPp ((blkPC_416).rebase (blkPl_416).base H) ret (sm'.setMem m_real) Pm Q Qp)) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base H) ret s Pre Q Qp := by
  apply sepWPp_seq_lscl_fb hcl (mid := mid)
  apply sepWP_seg_416 (mid := mid) (target := mid)
  intro m_strip
  refine SepWP.seq (hseg m_strip) fun sm' Pm hpc hrun hcont => ?_
  refine SepWP.done hpc hrun fun m_real hnsp => ?_
  exact SepWP.done (by cases sm'; exact hpc) (by cases sm'; exact hrun)
    fun hcl' => hcont m_real hnsp (by cases sm'; exact hcl')

/-! ## 3. Budget-Threaded Call Wrappers for `lagrangePrepare` & `lagrangeComplete` -/

theorem call_lagrangePrepare_placed_sepWPp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)}
    {ret_pc ret fsp out ptsPtr : BitVec 64} {pts : List Pt} {s0 s : State} {F P : SepProp}
    {Q Q_panic : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hlen_bound : 4 * (pts.length + 1) < 2 ^ 63)
    (hfit : FitsEvents M lim st (rustAllocEvents (2 * (pts.length + 1)) 2))
    (hpc : s.pc = lsmpl.base 372)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = fsp)
    (hfsp_al : (fsp &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = out)
    (hx1 : s.readReg64 Reg.x1 = ptsPtr)
    (hx2 : s.readReg64 Reg.x2 = BitVec.ofNat 64 pts.length)
    (hP : P = (memRegion out 24 ∗ ptSliceAt ptsPtr pts ∗ reduceTablePlacedAt ∗
      tokenInitPlacedAt ∗ A.pool lim st s ∗ stackAt fsp lagrangePrepareStack) ∗ F)
    (hnext : ∀ sf : State, LibsignalCodeLoaded lsmpl sf.mem →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = fsp → CalleeSavedPreserved s sf →
      sf.trace = s0.trace →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret sf
        ((polyOf A.repAlloc out (lagrangePreparePure pts) ∗ ptSliceAt ptsPtr pts ∗
          reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
          A.pool lim (M.stepEvents (rustAllocEvents (2 * (pts.length + 1)) 2) st) sf ∗
          stackAt fsp lagrangePrepareStack) ∗ F) Q Q_panic) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s P Q Q_panic := by
  have hsp_al : s.spAligned = true := by
    simp [State.spAligned, hsp_eq, beq_iff_eq.mp hfsp_al]
  let a : LagrangePrepareArgs :=
    { out := out, ptsPtr := ptsPtr, pts := pts, hlen_bound := hlen_bound }
  have hfit_env : FitsEnv M lim st (LagrangePrepareEnv a) := by
    intro evs hevs
    rw [hevs]
    exact hfit
  refine SepWPp.call_wpp
    (subroutine_ok_keep_lscl (hA.lagrangePrepare_blk_ok hcl) hcl)
    (x := (a, st)) (F := F)
    hpc hrun hsp_al hlr
    (fun R' hm => ?_)
    (fun _ _ _ _ hex => ?_)
    (fun _ _ ⟨_, hpan⟩ => ?_)
    (fun sf hpcf hrunf hspf hcsf => ?_)
  · rw [hP] at hm
    dsimp only [withMemEq, withPostLsCl, lagrangePreparePlacedSpec, a]
    rw [hsp_eq]
    have hm1 : s.mem ⊨
        (memRegion out 24 ∗ ptSliceAt ptsPtr pts ∗ reduceTablePlacedAt ∗
          tokenInitPlacedAt ∗ A.pool lim st s ∗ stackAt fsp lagrangePrepareStack) ∗
        ⌜s.mem = s.mem⌝ ∗ (F ∗ R') := by
      rw [sepConj_left_comm _ ⌜s.mem = s.mem⌝, satisfies_pure_sepConj]
      exact ⟨rfl, by simpa only [sepConj_assoc] using hm⟩
    have hm2 : s.mem ⊨
        ⌜s.readReg64 Reg.x0 = out ∧ s.readReg64 Reg.x1 = ptsPtr ∧
          s.readReg64 Reg.x2 = BitVec.ofNat 64 pts.length ∧
          FitsEnv M lim st (LagrangePrepareEnv a)⌝ ∗
        ((memRegion out 24 ∗ ptSliceAt ptsPtr pts ∗ reduceTablePlacedAt ∗
          tokenInitPlacedAt ∗ A.pool lim st s ∗ stackAt fsp lagrangePrepareStack) ∗
         ⌜s.mem = s.mem⌝ ∗ (F ∗ R')) := by
      rw [satisfies_pure_sepConj]
      exact ⟨⟨hx0, hx1, hx2, hfit_env⟩, hm1⟩
    simpa only [sepConj_assoc] using hm2
  · dsimp only [withMemEq, withPostLsCl, lagrangePreparePlacedSpec] at hex
    exact not_satisfies_false_sepConj hex
  · dsimp only [withMemEq, withPostLsCl, lagrangePreparePlacedSpec] at hpan
    exact False.elim (not_satisfies_false_sepConj hpan)
  · have hspf' : sf.sp = fsp := hspf.trans hsp_eq
    conv => arg 4; simp only [withMemEq, withPostLsCl, lagrangePreparePlacedSpec, a, hsp_eq,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWPp.exists_elim; intro evs
    apply SepWPp.pure_left; intro hclf
    apply SepWPp.pure_left; rintro ⟨hevs, htrf⟩
    dsimp only [LagrangePrepareEnv, a] at hevs
    subst hevs
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext sf hclf hpcf hrunf hspf' hcsf (htrf.trans htr))

theorem call_lagrangeComplete_placed_sepWPp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)}
    {ret_pc ret fsp coeffsPtr ptsPtr : BitVec 64} {self : Poly} {pts : List Pt} {i : Nat}
    {s0 s : State} {F P : SepProp} {Q Q_panic : State → SepProp → Prop}
    (hcomp_ok : subroutine_ok ((blkPC_373).rebase (blkPl_373).base (Rust.withPanics ext))
      (blkPl_373).base (withLsCodeLoaded lsmpl (withVmPreserved lagrangeCompletePlacedSpec)))
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hi : i < pts.length)
    (hself_bound : 2 * self.coefficients.length < 2 ^ 64)
    (hpts_bound : 4 * pts.length < 2 ^ 64)
    (hpc : s.pc = lsmpl.base 373)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = fsp)
    (hfsp_al : (fsp &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = coeffsPtr)
    (hx1 : s.readReg64 Reg.x1 = BitVec.ofNat 64 self.coefficients.length)
    (hx2 : s.readReg64 Reg.x2 = ptsPtr)
    (hx3 : s.readReg64 Reg.x3 = BitVec.ofNat 64 pts.length)
    (hx4 : s.readReg64 Reg.x4 = BitVec.ofNat 64 i)
    (hP : P = (gf16SliceAt coeffsPtr self.coefficients ∗ ptSliceAt ptsPtr pts ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ stackAt fsp lagrangeCompleteStack) ∗
      (A.pool lim st s ∗ F))
    (hnext : ∀ sf : State, LibsignalCodeLoaded lsmpl sf.mem →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = fsp → CalleeSavedPreserved s sf →
      sf.trace = s0.trace →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret sf
        ((gf16SliceAt coeffsPtr (lagrangeCompletePure self pts i).coefficients ∗
          ptSliceAt ptsPtr pts ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          stackAt fsp lagrangeCompleteStack) ∗ (A.pool lim st sf ∗ F)) Q Q_panic) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s P Q Q_panic := by
  have hsp_al : s.spAligned = true := by
    simp [State.spAligned, hsp_eq, beq_iff_eq.mp hfsp_al]
  let a : LagrangeCompleteArgs :=
    { coeffsPtr := coeffsPtr, ptsPtr := ptsPtr, self := self, pts := pts, i := i }
  refine SepWPp.call_wpp
    (subroutine_ok_keep_lscl (lscall_blk_cl hcomp_ok hcl) hcl)
    (x := a) (F := A.pool lim st s ∗ F)
    hpc hrun hsp_al hlr
    (fun R' hm => ?_)
    (fun _ _ _ _ hex => ?_)
    (fun _ _ ⟨_, hpan⟩ => ?_)
    (fun sf hpcf hrunf hspf hcsf => ?_)
  · rw [hP] at hm
    dsimp only [withMemEq, withPostLsCl, withVmPreserved, lagrangeCompletePlacedSpec, a]
    rw [hsp_eq]
    have hm1 : s.mem ⊨
        (gf16SliceAt coeffsPtr self.coefficients ∗ ptSliceAt ptsPtr pts ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ stackAt fsp lagrangeCompleteStack) ∗
        ⌜s.mem = s.mem⌝ ∗ ((A.pool lim st s ∗ F) ∗ R') := by
      rw [sepConj_left_comm _ ⌜s.mem = s.mem⌝, satisfies_pure_sepConj]
      exact ⟨rfl, by simpa only [sepConj_assoc] using hm⟩
    have hm2 : s.mem ⊨
        ⌜s.readReg64 Reg.x0 = coeffsPtr ∧
          s.readReg64 Reg.x1 = BitVec.ofNat 64 self.coefficients.length ∧
          s.readReg64 Reg.x2 = ptsPtr ∧
          s.readReg64 Reg.x3 = BitVec.ofNat 64 pts.length ∧
          s.readReg64 Reg.x4 = BitVec.ofNat 64 i ∧
          i < pts.length ∧
          2 * self.coefficients.length < 2 ^ 64 ∧
          4 * pts.length < 2 ^ 64⌝ ∗
        ((gf16SliceAt coeffsPtr self.coefficients ∗ ptSliceAt ptsPtr pts ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ stackAt fsp lagrangeCompleteStack) ∗
         ⌜s.mem = s.mem⌝ ∗ ((A.pool lim st s ∗ F) ∗ R')) := by
      rw [satisfies_pure_sepConj]
      exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hi, hself_bound, hpts_bound⟩, hm1⟩
    simpa only [sepConj_assoc] using hm2
  · dsimp only [withMemEq, withPostLsCl, withVmPreserved, lagrangeCompletePlacedSpec] at hex
    exact not_satisfies_false_sepConj hex
  · dsimp only [withMemEq, withPostLsCl, withVmPreserved, lagrangeCompletePlacedSpec] at hpan
    exact False.elim (not_satisfies_false_sepConj hpan)
  · have hspf' : sf.sp = fsp := hspf.trans hsp_eq
    conv => arg 4; simp only [withMemEq, withPostLsCl, withVmPreserved, lagrangeCompletePlacedSpec,
      a, hsp_eq, sepConj_assoc]
    apply SepWPp.pure_left; intro hclf
    apply SepWPp.pure_left; intro hvm
    apply SepWPp.pure_left; intro htrf
    refine SepWPp.transport_budgetPool hvm (hnext := ?_)
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext sf hclf hpcf hrunf hspf' hcsf (htrf.trans htr))

/-! ## 4. Single Iteration & Full Lagrange Basis Loop (`(blkPl_416).base + 4128#64 .. + 4368#64`) -/

/-- Sub-step 1 of the Lagrange basis loop (`+4128 -> +4176`):
    calls `lagrange_interpolate_prepare` (`2 * (ones.length + 1)` bytes, align `2`), unfolds the
    resulting `Poly`, and calls `lagrange_interpolate_complete` with `A.pool` preserved across
    `VmPreserved`. -/
theorem lagrangeBasisLoop_prep_comp_placed_sepWPp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)}
    {Q Q_panic : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (hcomp_ok : subroutine_ok ((blkPC_373).rebase (blkPl_373).base (Rust.withPanics ext))
      (blkPl_373).base (withLsCodeLoaded lsmpl (withVmPreserved lagrangeCompletePlacedSpec)))
    (i : Nat) (ones : List Pt) (_hones_ne : ones ≠ [])
    (hbound : ones.length ≤ 0x0555555555555555) (hi_lt : i < ones.length)
    (s0 s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (fsp xsPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (Frame _R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 4128#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 i)
    (hx20 : s.readReg64 .x20 = xsPtr)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 ones.length)
    (hfit_prep : FitsEvents M lim st (rustAllocEvents (2 * (ones.length + 1)) 2))
    (hcont : ∀ s1 prepCap prepPtr,
      LibsignalCodeLoaded lsmpl s1.mem →
      ones.length + 1 ≤ prepCap.toNat →
      prepCap.toNat * 2 < 2 ^ 63 →
      prepPtr ≠ 0#64 →
      prepCap ≠ 0#64 →
      s1.pc = (blkPl_416).base + 4176#64 →
      s1.status = .Running →
      s1.sp = fsp →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x19 = BitVec.ofNat 64 i →
      s1.readReg64 .x20 = xsPtr →
      s1.readReg64 .x21 = s.readReg64 .x21 →
      s1.readReg64 .x22 = BitVec.ofNat 64 ones.length →
      s1.readReg64 .x23 = BitVec.ofNat 64 (ones.length + 1) →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = prepPtr →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s1
        (A.pool lim (M.stepEvents (rustAllocEvents (2 * (ones.length + 1)) 2) st) s1 ∗
         ptSliceAt xsPtr ones ∗
         ((fsp + 656#64) ↦₆₄ prepCap) ∗
         ((fsp + 664#64) ↦₆₄ prepPtr) ∗
         ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 (ones.length + 1)) ∗
         A.live prepPtr (prepCap.toNat * 2) 2 ∗
         gf16SliceAt prepPtr (lagrangeCompletePure (lagrangePreparePure ones) ones i).coefficients ∗
         memRegion (prepPtr + BitVec.ofNat 64 (2 * (ones.length + 1)))
           (2 * (prepCap.toNat - (ones.length + 1))) ∗
         ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 ones.length) ∗
         reduceTablePlacedAt ∗
         tokenInitPlacedAt ∗
         stackAt fsp lagrangeCompleteStack ∗
         memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
           (lagrangePrepareStack - lagrangeCompleteStack) ∗ Frame)
        Q Q_panic) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool lim st s ∗
       ptSliceAt xsPtr ones ∗
       memRegion (fsp + 656#64) 24 ∗
       ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 ones.length) ∗
       reduceTablePlacedAt ∗
       tokenInitPlacedAt ∗
       stackAt fsp lagrangePrepareStack ∗ Frame)
      Q Q_panic := by
  try dsimp only [BitVec.ofNat_eq_ofNat] at hpc hcont ⊢
  apply sepWPp_seg_lscl_416 hcl (mid := lsmpl.base 372)
  intro _m_strip0
  wp_steps
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) fun _m_real0 _hnsp0 hcl1 => ?_
  refine SepWPp.transport_budgetPool (_hnsp0.toVmPreserved (by simp only [arm64_norm, wp_norm]))
    (hnext := ?_)
  refine call_lagrangePrepare_placed_sepWPp hA hcl1 (by omega) hfit_prep
    (ret_pc := (blkPl_416).base + 4144#64) (fsp := fsp) (out := fsp + 656#64)
    (ptsPtr := xsPtr) (pts := ones) (s0 := s0)
    (by wp_norm_goal)
    (by wp_norm_lhs)
    (by simp only [wp_norm, hsp])
    hfsp_align
    (by wp_norm_lhs)
    (by simp only [arm64_norm, wp_norm, htrace])
    (by simp only [wp_norm, hsp])
    (by simp only [wp_norm, hx20])
    (by simp only [wp_norm, hx22])
    (by sep_frame) ?_
  intro sfPrep hclPrep hpcPrep hrunPrep hspPrep hcsPrep htrPrep
  rcases hcsPrep with ⟨hcsPrep_19, hcsPrep_20, hcsPrep_21, hcsPrep_22, hcsPrep_23,
    hcsPrep_24, hcsPrep_25, hcsPrep_26, hcsPrep_27, hcsPrep_28, hcsPrep_29, hcsPrep_vregs⟩
  refine SepWPp.weaken_pre
    (sepConj_mono_fbl
      (sepConj_mono_fbl (polyOf_prepare_unfold A.repAlloc fsp ones) (Entails.refl _))
      (Entails.refl _)) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWPp.exists_elim; intro prepCap
  apply SepWPp.exists_elim; intro prepPtr
  apply SepWPp.pure_left; rintro ⟨hprep_le, hprep_bound, hprep_ptr, hprep_cap⟩
  apply sepWPp_seg_lscl_416 hclPrep (mid := lsmpl.base 373)
  intro _m_strip1
  wp_steps
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) fun _m_real1 _hnsp1 hcl2 => ?_
  refine SepWPp.transport_budgetPool (_hnsp1.toVmPreserved (by simp only [arm64_norm, wp_norm]))
    (hnext := ?_)
  rw [stackAt_lagrangePrepare_split_complete fsp]
  refine call_lagrangeComplete_placed_sepWPp (A := A) (lim := lim)
    (st := M.stepEvents (rustAllocEvents (2 * (ones.length + 1)) 2) st)
    hcomp_ok hcl2 hi_lt
    (self := lagrangePreparePure ones) (pts := ones) (i := i)
    (ret_pc := (blkPl_416).base + 4176#64) (fsp := fsp) (coeffsPtr := prepPtr)
    (ptsPtr := xsPtr) (s0 := s0)
    (by rw [lagrangePreparePure_length]; omega)
    (by omega)
    (by wp_norm_goal)
    (by wp_norm_lhs)
    (by simp only [wp_norm, hspPrep])
    hfsp_align
    (by wp_norm_lhs)
    (by simp only [arm64_norm, wp_norm, htrPrep])
    (by wp_norm_lhs)
    (by simp only [wp_norm, lagrangePreparePure_length])
    (by simp only [wp_norm, hcsPrep_20, hx20])
    (by simp only [wp_norm, hcsPrep_22, hx22])
    (by simp only [wp_norm, hcsPrep_19, hx19])
    (by sep_frame) ?_
  intro sfComp hclComp hpcComp hrunComp hspComp hcsComp htrComp
  rcases hcsComp with ⟨hcsComp_19, hcsComp_20, hcsComp_21, hcsComp_22, hcsComp_23,
    hcsComp_24, hcsComp_25, hcsComp_26, hcsComp_27, hcsComp_28, hcsComp_29, hcsComp_vregs⟩
  refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (hcont sfComp prepCap prepPtr hclComp hprep_le hprep_bound hprep_ptr hprep_cap
      hpcComp hrunComp hspComp htrComp
      (by rw [hcsComp_vregs]; simp only [arm64_norm, wp_norm, hcsPrep_vregs, *])
      (by rw [hcsComp_19]; simp only [wp_norm, hcsPrep_19, hx19])
      (by rw [hcsComp_20]; simp only [wp_norm, hcsPrep_20, hx20])
      (by rw [hcsComp_21]; simp only [wp_norm, hcsPrep_21])
      (by rw [hcsComp_22]; simp only [wp_norm, hcsPrep_22, hx22])
      (by rw [hcsComp_23]; simp only [wp_norm])
      (by rw [hcsComp_24]; simp only [wp_norm, hcsPrep_24])
      (by rw [hcsComp_25]; simp only [wp_norm, hcsPrep_25])
      (by rw [hcsComp_26]; simp only [wp_norm])
      (by rw [hcsComp_27]; simp only [wp_norm, hcsPrep_27])
      (by rw [hcsComp_28]; simp only [wp_norm, hcsPrep_28])
      (by rw [hcsComp_29]; simp only [wp_norm, hcsPrep_29]))

private theorem trace_eq_of_allocCallPreserved {s sf s0 : State}
    (h : AllocCallPreserved s sf) (htr : s.trace = s0.trace) : sf.trace = s0.trace :=
  h.2.1.trans htr

/-- Sub-step 2 of the Lagrange basis loop (`+4176 -> +4304`):
    allocates the `2 * ones.length`-byte `Poly` coefficient buffer (total under `hfit_out`),
    `memcpy`s the tail coefficients `[1..n]`, and `__rust_dealloc`s the temporary `prepPtr`
    buffer. -/
theorem lagrangeBasisLoop_copy_free_placed_sepWPp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st1 : M.σ}
    {ext : String → Option (State → State)}
    {Q Q_panic : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (i : Nat) (ones : List Pt) (hones_ne : ones ≠ [])
    (hbound : ones.length ≤ 0x0555555555555555)
    (s0 s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (fsp prepCap prepPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hprep_le : ones.length + 1 ≤ prepCap.toNat)
    (hprep_bound : prepCap.toNat * 2 < 2 ^ 63)
    (hprep_ptr : prepPtr ≠ 0#64)
    (hprep_cap : prepCap ≠ 0#64)
    (u216 u224 : BitVec 64) (Frame _R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 4176#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (ones.length + 1))
    (hx26 : s.readReg64 .x26 = prepPtr)
    (hfit_out : FitsEvents M lim st1 (rustAllocEvents (2 * ones.length) 2))
    (hcont : ∀ s1 newPtr,
      LibsignalCodeLoaded lsmpl s1.mem →
      newPtr ≠ 0#64 →
      s1.pc = (blkPl_416).base + 4304#64 →
      s1.status = .Running →
      s1.sp = fsp →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x21 = s.readReg64 .x21 →
      s1.readReg64 .x22 = BitVec.ofNat 64 ones.length →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s1
        (A.pool lim
           (M.stepEvents (rustDeallocEvents (prepCap.toNat * 2) 2)
             (M.stepEvents (rustAllocEvents (2 * ones.length) 2) st1)) s1 ∗
         A.live newPtr (2 * ones.length) 2 ∗
         (newPtr ↦ₛ gf16SliceBytes (lagrangeInterpolatePtPure ones i).coefficients) ∗
         ((fsp + 656#64) ↦₆₄ prepCap) ∗
         ((fsp + 664#64) ↦₆₄ prepPtr) ∗
         ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 ones.length) ∗
         ((fsp + 216#64) ↦₆₄ BitVec.ofNat 64 ones.length) ∗
         ((fsp + 224#64) ↦₆₄ newPtr) ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q Q_panic) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool lim st1 s ∗
       ((fsp + 656#64) ↦₆₄ prepCap) ∗
       ((fsp + 664#64) ↦₆₄ prepPtr) ∗
       A.live prepPtr (prepCap.toNat * 2) 2 ∗
       gf16SliceAt prepPtr (lagrangeCompletePure (lagrangePreparePure ones) ones i).coefficients ∗
       memRegion (prepPtr + BitVec.ofNat 64 (2 * (ones.length + 1)))
         (2 * (prepCap.toNat - (ones.length + 1))) ∗
       ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 ones.length) ∗
       ((fsp + 216#64) ↦₆₄ u216) ∗
       ((fsp + 224#64) ↦₆₄ u224) ∗
       stackAt fsp allocHookStack ∗ Frame)
      Q Q_panic := by
  have hn_pos : 0 < ones.length := List.length_pos_iff.mpr hones_ne
  have hshim := hA.noAllocShim_ok
  dsimp only [noAllocShimSpec, noAllocShimBudgetSpec] at hshim
  have halloc := hA.allocNoOom_ok
  dsimp only [rustCliAllocNoOomSpec] at halloc
  have hmemcpy := hA.session_memcpy_ok allocHookStack
  dsimp only [sessionMemcpyBudgetSpec, sessionMemcpySpec] at hmemcpy
  have hdealloc := hA.dealloc_ok
  dsimp only [rustCliDeallocBudgetSpec] at hdealloc
  clear hA
  try dsimp only [BitVec.ofNat_eq_ofNat] at hpc hshim halloc hmemcpy hdealloc hcont ⊢
  obtain ⟨c0, hc0⟩ := lagrangeComplete_prepare_head_tail ones i
  rw [hc0]
  have hn1_ne0 := ofNat_succ_ne_zero hbound
  obtain ⟨hn_ne0, h2n_ne0⟩ := ofNat_pos_ne_zero hn_pos hbound
  obtain ⟨hmsb1, hmsb2⟩ := bit62_shl_one_false hbound
  have hult := ult_max_2n_false hbound
  have hlayout2n : RustLayoutOk (2 * ones.length) 2 := ⟨⟨by omega, ⟨1, rfl⟩, by omega⟩, by decide⟩
  have hfit_out_ev : FitsEvent M lim st1 (.alloc (2 * ones.length)) := by
    have hle2n : 2 ≤ 2 * ones.length := by omega
    simpa [rustAllocEvents, hle2n] using hfit_out
  rcases hfit_out_ev with ⟨_hwmax_out, henf_out, hram_out, hva_out⟩
  have h2n_toNat : (BitVec.ofNat 64 (2 * ones.length)).toNat = 2 * ones.length :=
    Nat.mod_eq_of_lt (by omega)
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  apply sepWPp_seq_lscl_fb hcl (mid := (blkPl_416).base + 4228#64)
  apply SepWP.fold (gf16SliceAt_cons_memRegion2 prepPtr c0 _) (by sep_frame)
  wp_steps_sync_416 (lsρ spqrRustNoAllocShimSym)
  simp only [State.setMem_setMem]
  wp_call hshim ()
  clear hshim
  have hsp_sf0 : sf.sp = fsp := by simp only [arm64_norm, wp_norm, hsp, *]
  have htr_sf0 : sf.trace = s0.trace := by simp only [arm64_norm, wp_norm, htrace, *]
  refine SepWP.transport_budgetPool h (hnext := ?_)
  clear h
  wp_steps_sync_416 (lsρ spqrRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call halloc (2 * ones.length, 2, st1)
  clear halloc
  have hoom : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq_oom : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
  have htr_sf1 : sf_1.trace = s0.trace := by
    simpa [arm64_norm, wp_norm, htr_sf0] using h_22.2.1
  clear h_22
  have hsp_sf1 : sf_1.sp = fsp := by simp only [arm64_norm, wp_norm, hsp_sf0, *]
  have hx22_sf1 : sf_1.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 ones.length := by
    simp only [arm64_norm, wp_norm, Reg.x22, Reg.x23, hx23, *]
  have hx23_sf1 : sf_1.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 (2 * ones.length) := by
    simp only [arm64_norm, wp_norm, Reg.x23, hx23, *]
  have hx26_sf1 : sf_1.readReg64 (Reg.gpr 26#5) = prepPtr := by
    simp only [arm64_norm, wp_norm, Reg.x26, hx26, *]
  refine SepWP.done hpc_sf_1 hrun_sf_1 ?_
  intro hcl1
  have hlen_interp :
      (gf16SliceBytes (lagrangeInterpolatePtPure ones i).coefficients).length = 2 * ones.length := by
    simp [lagrangeInterpolatePtPure_length]
  apply sepWPp_seq_lscl_fb hcl1 (mid := (blkPl_416).base + 4280#64)
  wp_steps_sync_416 (lsρ spqrMemcpySym)
  simp only [State.setMem_setMem]
  wp_call hmemcpy
    (sf_1.readReg64 (Reg.gpr 0#5), prepPtr + 2#64,
     gf16SliceBytes (lagrangeInterpolatePtPure ones i).coefficients)
  clear hmemcpy
  have hsp_sf2 : sf_2.sp = fsp := by simp only [arm64_norm, wp_norm, hsp_sf1, *]
  have htr_sf2 : sf_2.trace = s0.trace := by simp only [arm64_norm, wp_norm, htr_sf1, *]
  have hx26_sf2 : sf_2.readReg64 (Reg.gpr 26#5) = prepPtr := by
    simp only [arm64_norm, wp_norm, Reg.x26, hx26_sf1, *]
  refine SepWP.transport_budgetPool h_33 (hnext := ?_)
  clear h_33
  refine SepWP.done hpc_sf_2 hrun_sf_2 ?_
  intro hcl2
  have hrecomb := memRegion_recombine_prepare prepPtr prepCap ones.length
    (gf16SliceBytes (lagrangeInterpolatePtPure ones i).coefficients) hlen_interp hprep_le hprep_bound
  have hprep_cap_bne : ¬(prepCap == 0#64) = true := by simpa [beq_iff_eq] using hprep_cap
  have hcap_shl := shl_one_cap_toNat_nat hprep_bound
  have hprep_sz_toNat : (BitVec.ofNat 64 (prepCap.toNat * 2)).toNat = prepCap.toNat * 2 :=
    Nat.mod_eq_of_lt (by omega)
  apply sepWPp_seq_lscl_fb hcl2 (mid := (blkPl_416).base + 4304#64)
  apply SepWP.fold hrecomb (by sep_frame)
  wp_steps_sync_416 (lsρ spqrRustDeallocSym)
  simp only [State.setMem_setMem]
  wp_call hdealloc
    (prepPtr, prepCap.toNat * 2, 2, M.stepEvents (rustAllocEvents (2 * ones.length) 2) st1)
  clear hdealloc
  have hsp_sf3 : sf_3.sp = fsp := by simp only [arm64_norm, wp_norm, hsp_sf2, *]
  have htr_sf3 : sf_3.trace = s0.trace := by
    apply trace_eq_of_allocCallPreserved
    · assumption
    · simp only [arm64_norm, wp_norm, htr_sf2, *]
  refine SepWP.done hpc_sf_3 hrun_sf_3 ?_
  intro hcl3
  refine SepWPp.weaken_pre
    (by
      simp only [arm64_norm, wp_norm, hbeq_oom, Bool.false_eq_true, ↓reduceIte, h2n_toNat,
        hsp_sf3, hsp_sf2, hsp_sf1, hsp_sf0, hsp, hx23, *]
      exact Entails.of_eq (by sep_ac_rfl))
    (hcont sf_3 (sf_1.readReg64 (Reg.gpr 0#5)) hcl3 hoom
      hpc_sf_3 hrun_sf_3
      hsp_sf3
      htr_sf3
      (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, Reg.x19, *])
      (by simp only [arm64_norm, wp_norm, Reg.x20, *])
      (by simp only [arm64_norm, wp_norm, Reg.x21, *])
      (by simp only [arm64_norm, wp_norm, Reg.x22, hx22_sf1, *])
      (by simp only [arm64_norm, wp_norm, Reg.x24, *])
      (by simp only [arm64_norm, wp_norm, Reg.x25, *])
      (by simp only [arm64_norm, wp_norm, Reg.x27, *])
      (by simp only [arm64_norm, wp_norm, Reg.x28, *])
      (by simp only [arm64_norm, wp_norm, Reg.x29, *]))

/-- Sub-step 3 of the Lagrange basis loop (`+4304 -> +4128 / +4368`):
    stores the `Poly` header into `curBasis`, increments `i`, and branches back to `+4128` or
    exits to `+4368` while transporting `A.pool lim st3`. -/
theorem lagrangeBasisLoop_tail_placed_sepWPp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st3 : M.σ}
    {ext : String → Option (State → State)}
    {Q Q_panic : State → SepProp → Prop}
    (rem i : Nat) (ones : List Pt) (hones_ne : ones ≠ [])
    (hbound : ones.length ≤ 0x0555555555555555)
    (hsum : i + (rem + 1) = ones.length)
    (s0 s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (fsp curBasis newPtr : BitVec 64)
    (_hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hnew_ptr : newPtr ≠ 0#64)
    (u656 u664 u1040 u1048 u1056 : BitVec 64) (Frame _R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 4304#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 i)
    (hx21 : s.readReg64 .x21 = curBasis)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 ones.length)
    (hx29 : s.readReg64 .x29 = fsp + 1104#64)
    (hcont : ∀ s1 u216' u224' u1040' u1048' u1056',
      LibsignalCodeLoaded lsmpl s1.mem →
      s1.pc = (if rem == 0 then
          (blkPl_416).base + 4368#64
        else
          (blkPl_416).base + 4128#64) →
      s1.status = .Running →
      s1.sp = fsp →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x19 = BitVec.ofNat 64 (i + 1) →
      s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x21 = curBasis + 24#64 →
      s1.readReg64 .x22 = BitVec.ofNat 64 ones.length →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = fsp + 1104#64 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s1
        (A.pool lim st3 s1 ∗
         polyOf A.repAlloc curBasis (lagrangeInterpolatePtPure ones i) ∗
         memRegion (fsp + 656#64) 24 ∗
         ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 ones.length) ∗
         ((fsp + 216#64) ↦₆₄ u216') ∗
         ((fsp + 224#64) ↦₆₄ u224') ∗
         ((fsp + 1040#64) ↦₆₄ u1040') ∗
         ((fsp + 1048#64) ↦₆₄ u1048') ∗
         ((fsp + 1056#64) ↦₆₄ u1056') ∗ Frame)
        Q Q_panic) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool lim st3 s ∗
       A.live newPtr (2 * ones.length) 2 ∗
       (newPtr ↦ₛ gf16SliceBytes (lagrangeInterpolatePtPure ones i).coefficients) ∗
       memRegion curBasis 24 ∗
       ((fsp + 656#64) ↦₆₄ u656) ∗
       ((fsp + 664#64) ↦₆₄ u664) ∗
       ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 (ones.length + 1)) ∗
       ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 ones.length) ∗
       ((fsp + 216#64) ↦₆₄ BitVec.ofNat 64 ones.length) ∗
       ((fsp + 224#64) ↦₆₄ newPtr) ∗
       ((fsp + 1040#64) ↦₆₄ u1040) ∗
       ((fsp + 1048#64) ↦₆₄ u1048) ∗
       ((fsp + 1056#64) ↦₆₄ u1056) ∗ Frame)
      Q Q_panic := by
  have hn_pos : 0 < ones.length := List.length_pos_iff.mpr hones_ne
  try dsimp only [BitVec.ofNat_eq_ofNat] at hpc hcont ⊢
  obtain ⟨hcmn1, hcmn2, hcmn3, hcmn4⟩ := adds_one_ne_zero (i := i) (by omega)
  have hstur_addr : (fsp + 1104#64) + 0xffffffffffffffd0#64 = fsp + 1056#64 := by bv_omega
  have hpoly_intro := polyOf_of_pointsToBytes A.repAlloc curBasis newPtr
    (lagrangeInterpolatePtPure ones i) ones.length hn_pos (by omega) hnew_ptr
    (lagrangeInterpolatePtPure_length ones i)
  have hmem24 := polyHeader_entails_memRegion24_off fsp
    (BitVec.ofNat 64 ones.length) newPtr (BitVec.ofNat 64 (ones.length + 1))
  apply sepWPp_seg_lscl_416 hcl (mid := (blkPl_416).base + 4348#64)
  intro _m_strip0
  apply SepWP.fold (Entails.of_eq (memRegion_split_polyHeader_fbl curBasis)) (by sep_frame)
  apply sepWP_exists_left_sep; intro uBasis16
  apply sepWP_exists_left_sep; intro uBasis8
  apply sepWP_exists_left_sep; intro uBasis0
  wp_steps
  apply SepWP.fold hpoly_intro (by sep_frame)
  apply SepWP.fold hmem24 (by sep_frame)
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hx19, hcmn1, hcmn2, hcmn3, hcmn4,
          Bool.false_eq_true, ↓reduceIte])
    (by wp_norm_lhs)
    fun _m_real0 _hnsp0 hcl1 => ?_
  refine SepWPp.transport_budgetPool
    (_hnsp0.toVmPreserved
      (by simp only [arm64_norm, wp_norm, hx19, hcmn1, hcmn2, hcmn3, hcmn4,
            Bool.false_eq_true, ↓reduceIte]))
    (hnext := ?_)
  cases rem with
  | zero =>
    have hi1_eq : i + 1 = ones.length := by omega
    have hcmp_eq :
        (BitVec.ofNat 64 ones.length == BitVec.ofNat 64 i + 1#64) = true ∧
        (BitVec.ofNat 64 ones.length != BitVec.ofNat 64 i + 1#64) = false ∧
        (BitVec.ofNat 64 ones.length - (BitVec.ofNat 64 i + 1#64) == 0#64) = true := by
      rw [ofNat_add_one_eq_succ_fb, hi1_eq]
      simp [BitVec.sub_self]
    rcases hcmp_eq with ⟨hcmp1, hcmp2, hcmp3⟩
    apply sepWPp_seg_lscl_416 hcl1 (mid := (blkPl_416).base + 4368#64)
    intro _m_strip1
    wp_steps
    refine SepWP.done
      (by simp only [arm64_norm, wp_norm, hx19, ofNat_add_one_eq_succ_fb, hi1_eq,
            bne_self_eq_false, BitVec.sub_self, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte])
      (by wp_norm_lhs)
      fun _m_real1 _hnsp1 hcl2 => ?_
    refine SepWPp.transport_budgetPool
      (_hnsp1.toVmPreserved
        (by simp only [arm64_norm, wp_norm, hx19, ofNat_add_one_eq_succ_fb, hi1_eq,
              bne_self_eq_false, BitVec.sub_self, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]))
      (hnext := ?_)
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hcont _ (BitVec.ofNat 64 ones.length) newPtr
        (BitVec.ofNat 64 ones.length) newPtr (BitVec.ofNat 64 ones.length) hcl2
        (by simp only [arm64_norm, wp_norm, hx19, ofNat_add_one_eq_succ_fb, hi1_eq,
              bne_self_eq_false, BitVec.sub_self, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte])
        (by wp_norm_lhs)
        (by simp only [arm64_norm, wp_norm, hsp])
        (by simp only [arm64_norm, wp_norm, htrace])
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hx19, ofNat_add_one_eq_succ_fb, hi1_eq])
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hx21])
        (by simp only [arm64_norm, wp_norm, hx22])
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hx29]))
  | succ r =>
    have hi1_ne : ones.length ≠ i + 1 := by omega
    obtain ⟨hcmp1, hcmp2, hcmp3⟩ := ofNat_ne_ofNat_false hi1_ne (by omega) (by omega)
    apply sepWPp_seg_lscl_416 hcl1 (mid := (blkPl_416).base + 4128#64)
    intro _m_strip1
    wp_steps
    refine SepWP.done
      (by simp only [arm64_norm, wp_norm, hx19, ofNat_add_one_eq_succ_fb, hcmp1, hcmp2, hcmp3,
            Bool.false_eq_true, ↓reduceIte])
      (by wp_norm_lhs)
      fun _m_real1 _hnsp1 hcl2 => ?_
    refine SepWPp.transport_budgetPool
      (_hnsp1.toVmPreserved
        (by simp only [arm64_norm, wp_norm, hx19, ofNat_add_one_eq_succ_fb, hcmp1, hcmp2, hcmp3,
              Bool.false_eq_true, ↓reduceIte]))
      (hnext := ?_)
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hcont _ (BitVec.ofNat 64 ones.length) newPtr
        (BitVec.ofNat 64 ones.length) newPtr (BitVec.ofNat 64 ones.length) hcl2
        (by simp only [arm64_norm, wp_norm, hx19, ofNat_add_one_eq_succ_fb, hcmp1, hcmp2, hcmp3,
              Bool.false_eq_true, ↓reduceIte])
        (by wp_norm_lhs)
        (by simp only [arm64_norm, wp_norm, hsp])
        (by simp only [arm64_norm, wp_norm, htrace])
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hx19, ofNat_add_one_eq_succ_fb])
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hx21])
        (by simp only [arm64_norm, wp_norm, hx22])
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hx29]))

/-- Combined single iteration of the Lagrange basis loop (`+4128 -> +4128 / +4368`) under
    `FallbackBasisStepEnv ones.length`. -/
theorem lagrangeBasisLoop_step_placed_sepWPp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)}
    {Q Q_panic : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (hcomp_ok : subroutine_ok ((blkPC_373).rebase (blkPl_373).base (Rust.withPanics ext))
      (blkPl_373).base (withLsCodeLoaded lsmpl (withVmPreserved lagrangeCompletePlacedSpec)))
    (rem i : Nat) (ones : List Pt) (hones_ne : ones ≠ [])
    (hbound : ones.length ≤ 0x0555555555555555) (hsum : i + (rem + 1) = ones.length)
    (s0 s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (fsp xsPtr curBasis : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (u216 u224 u1040 u1048 u1056 : BitVec 64) (Frame R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 4128#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (htrace : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 i) (hx20 : s.readReg64 .x20 = xsPtr)
    (hx21 : s.readReg64 .x21 = curBasis) (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 ones.length)
    (hx29 : s.readReg64 .x29 = fsp + 1104#64)
    (hfit : FitsEnv M lim st (FallbackBasisStepEnv ones.length))
    (hcont : ∀ (evs : List AllocEvent) s1 u216' u224' u1040' u1048' u1056',
      FallbackBasisStepEnv ones.length evs →
      LibsignalCodeLoaded lsmpl s1.mem →
      s1.pc = (if rem == 0 then
          (blkPl_416).base + 4368#64
        else
          (blkPl_416).base + 4128#64) →
      s1.status = .Running → s1.sp = fsp → s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x19 = BitVec.ofNat 64 (i + 1) → s1.readReg64 .x20 = xsPtr →
      s1.readReg64 .x21 = curBasis + 24#64 → s1.readReg64 .x22 = BitVec.ofNat 64 ones.length →
      s1.readReg64 .x24 = s.readReg64 .x24 → s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x27 = s.readReg64 .x27 → s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = fsp + 1104#64 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s1
        (A.pool lim (M.stepEvents evs st) s1 ∗
         ptSliceAt xsPtr ones ∗
         polyOf A.repAlloc curBasis (lagrangeInterpolatePtPure ones i) ∗
         memRegion (fsp + 656#64) 24 ∗ ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 ones.length) ∗
         ((fsp + 216#64) ↦₆₄ u216') ∗ ((fsp + 224#64) ↦₆₄ u224') ∗
         ((fsp + 1040#64) ↦₆₄ u1040') ∗ ((fsp + 1048#64) ↦₆₄ u1048') ∗
         ((fsp + 1056#64) ↦₆₄ u1056') ∗
         reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ stackAt fsp lagrangePrepareStack ∗ Frame)
        Q Q_panic) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool lim st s ∗ ptSliceAt xsPtr ones ∗ memRegion curBasis 24 ∗
       memRegion (fsp + 656#64) 24 ∗
       ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 ones.length) ∗
       ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
       ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗
       ((fsp + 1056#64) ↦₆₄ u1056) ∗
       reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ stackAt fsp lagrangePrepareStack ∗ Frame)
      Q Q_panic := by
  obtain ⟨hfit_prep, hfit_out⟩ := fitsEvents_of_fitsEnv_fallbackBasisStep ones.length hfit
  refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (lagrangeBasisLoop_prep_comp_placed_sepWPp hA hcomp_ok i ones hones_ne hbound (by omega)
      s0 s hcl fsp xsPtr hfsp_align
      (memRegion curBasis 24 ∗ ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
       ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗
       ((fsp + 1056#64) ↦₆₄ u1056) ∗ Frame) R
      hpc hrun hsp htrace hx19 hx20 hx22 hfit_prep ?_)
  intro s1 prepCap prepPtr hcl1 hprep_le hprep_bound hprep_ptr hprep_cap
    hpc1 hrun1 hsp1 htr1 hvregs1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1
    hx27_1 hx28_1 hx29_1
  let st1 := M.stepEvents (rustAllocEvents (2 * (ones.length + 1)) 2) st
  refine SepWPp.weaken_pre
    (by
      have hst := stackAt_complete_to_alloc fsp
      refine Entails.trans (Entails.of_eq (show _ =
        (stackAt fsp lagrangeCompleteStack ∗
         memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
           (lagrangePrepareStack - lagrangeCompleteStack)) ∗
        (A.pool lim st1 s1 ∗
         ((fsp + 656#64) ↦₆₄ prepCap) ∗ ((fsp + 664#64) ↦₆₄ prepPtr) ∗
         A.live prepPtr (prepCap.toNat * 2) 2 ∗
         gf16SliceAt prepPtr
           (lagrangeCompletePure (lagrangePreparePure ones) ones i).coefficients ∗
         memRegion (prepPtr + BitVec.ofNat 64 (2 * (ones.length + 1)))
           (2 * (prepCap.toNat - (ones.length + 1))) ∗
         ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 ones.length) ∗
         ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
         ptSliceAt xsPtr ones ∗ ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 (ones.length + 1)) ∗
         reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ memRegion curBasis 24 ∗
         ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗
         ((fsp + 1056#64) ↦₆₄ u1056) ∗ Frame) by sep_ac_rfl)) ?_
      refine Entails.trans (sepConj_mono_left hst) (Entails.of_eq (by sep_ac_rfl)))
    (lagrangeBasisLoop_copy_free_placed_sepWPp hA i ones hones_ne hbound
      s0 s1 hcl1 fsp prepCap prepPtr hfsp_align hprep_le hprep_bound hprep_ptr hprep_cap u216 u224
      (memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
         (lagrangePrepareStack - allocHookStack) ∗
       ptSliceAt xsPtr ones ∗ ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 (ones.length + 1)) ∗
       reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ memRegion curBasis 24 ∗
       ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗
       ((fsp + 1056#64) ↦₆₄ u1056) ∗ Frame) R
      hpc1 hrun1 hsp1 htr1 hx23_1 hx26_1 hfit_out ?_)
  intro s2 newPtr hcl2 hnew_ptr hpc2 hrun2 hsp2 htr2 hvregs2 hx19_2 hx20_2 hx21_2 hx22_2 hx24_2
    hx25_2 hx27_2 hx28_2 hx29_2
  let evs_step : List AllocEvent :=
    (rustAllocEvents (2 * (ones.length + 1)) 2 ++ rustAllocEvents (2 * ones.length) 2) ++
      rustDeallocEvents (prepCap.toNat * 2) 2
  have hevs_step : FallbackBasisStepEnv ones.length evs_step :=
    SeqEnv.append rfl (FreeOnlyEvs.singleton 2 (prepCap.toNat * 2))
  have hst_step :
      M.stepEvents (rustDeallocEvents (prepCap.toNat * 2) 2)
        (M.stepEvents (rustAllocEvents (2 * ones.length) 2) st1) =
      M.stepEvents evs_step st := by
    dsimp only [evs_step, st1]
    rw [LibsignalBinary.Heap.AllocCostModel.stepEvents_append,
      LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
  refine SepWPp.weaken_pre
    (by
      rw [hst_step]
      have hst := stackAt_alloc_to_prepare fsp
      refine Entails.trans (Entails.of_eq (show _ =
        (stackAt fsp allocHookStack ∗
         memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
           (lagrangePrepareStack - allocHookStack)) ∗
        (A.pool lim (M.stepEvents evs_step st) s2 ∗
         A.live newPtr (2 * ones.length) 2 ∗
         (newPtr ↦ₛ gf16SliceBytes (lagrangeInterpolatePtPure ones i).coefficients) ∗
         memRegion curBasis 24 ∗
         ((fsp + 656#64) ↦₆₄ prepCap) ∗ ((fsp + 664#64) ↦₆₄ prepPtr) ∗
         ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 (ones.length + 1)) ∗
         ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 ones.length) ∗
         ((fsp + 216#64) ↦₆₄ BitVec.ofNat 64 ones.length) ∗ ((fsp + 224#64) ↦₆₄ newPtr) ∗
         ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗
         ((fsp + 1056#64) ↦₆₄ u1056) ∗
         ptSliceAt xsPtr ones ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ Frame) by sep_ac_rfl)) ?_
      refine Entails.trans (sepConj_mono_left hst) (Entails.of_eq (by sep_ac_rfl)))
    (lagrangeBasisLoop_tail_placed_sepWPp (M := M) (A := A) (lim := lim)
      (st3 := M.stepEvents evs_step st) rem i ones hones_ne hbound hsum
      s0 s2 hcl2 fsp curBasis newPtr hfsp_align hnew_ptr prepCap prepPtr u1040 u1048 u1056
      (ptSliceAt xsPtr ones ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
       stackAt fsp lagrangePrepareStack ∗ Frame) R
      hpc2 hrun2 hsp2 htr2
      (by rw [hx19_2, hx19_1]) (by rw [hx21_2, hx21_1, hx21]) hx22_2
      (by rw [hx29_2, hx29_1, hx29]) ?_)
  intro s3 u216' u224' u1040' u1048' u1056' hcl3
    hpc3 hrun3 hsp3 htr3 hvregs3 hx19_3 hx20_3 hx21_3 hx22_3 hx24_3 hx25_3 hx27_3 hx28_3 hx29_3
  refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (hcont evs_step s3 u216' u224' u1040' u1048' u1056' hevs_step hcl3
      hpc3 hrun3 hsp3 htr3 (by rw [hvregs3, hvregs2, hvregs1])
      hx19_3 (by rw [hx20_3, hx20_2, hx20_1]) hx21_3 hx22_3
      (by rw [hx24_3, hx24_2, hx24_1]) (by rw [hx25_3, hx25_2, hx25_1])
      (by rw [hx27_3, hx27_2, hx27_1]) (by rw [hx28_3, hx28_2, hx28_1]) hx29_3)

/-- Full Lagrange basis loop (`+4128 -> +4368`) over `rem + 1` iterations under
    `RepeatSeqEnv (rem + 1) (FallbackBasisStepEnv ones.length)`. -/
theorem lagrangeBasisLoop_placed_sepWPp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)}
    {Q Q_panic : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (hcomp_ok : subroutine_ok ((blkPC_373).rebase (blkPl_373).base (Rust.withPanics ext))
      (blkPl_373).base (withLsCodeLoaded lsmpl (withVmPreserved lagrangeCompletePlacedSpec)))
    (rem i : Nat) (ones : List Pt) (hones_ne : ones ≠ [])
    (hbound : ones.length ≤ 0x0555555555555555) (hsum : i + (rem + 1) = ones.length)
    (s0 s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (fsp xsPtr curBasis : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (u216 u224 u1040 u1048 u1056 : BitVec 64) (Frame R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 4128#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (htrace : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 i) (hx20 : s.readReg64 .x20 = xsPtr)
    (hx21 : s.readReg64 .x21 = curBasis) (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 ones.length)
    (hx29 : s.readReg64 .x29 = fsp + 1104#64)
    (hfit : FitsEnv M lim st (RepeatSeqEnv (rem + 1) (FallbackBasisStepEnv ones.length)))
    (hcont : ∀ (evs : List AllocEvent) s1 u216' u224' u1040' u1048' u1056',
      RepeatSeqEnv (rem + 1) (FallbackBasisStepEnv ones.length) evs →
      LibsignalCodeLoaded lsmpl s1.mem →
      s1.pc = (blkPl_416).base + 4368#64 →
      s1.status = .Running → s1.sp = fsp → s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x20 = xsPtr → s1.readReg64 .x22 = BitVec.ofNat 64 ones.length →
      s1.readReg64 .x24 = s.readReg64 .x24 → s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x27 = s.readReg64 .x27 → s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = fsp + 1104#64 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s1
        (A.pool lim (M.stepEvents evs st) s1 ∗
         ptSliceAt xsPtr ones ∗
         polyListOf A.repAlloc curBasis (lagrangeBasisFrom ones i (rem + 1)) ∗
         memRegion (fsp + 656#64) 24 ∗ ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 ones.length) ∗
         ((fsp + 216#64) ↦₆₄ u216') ∗ ((fsp + 224#64) ↦₆₄ u224') ∗
         ((fsp + 1040#64) ↦₆₄ u1040') ∗ ((fsp + 1048#64) ↦₆₄ u1048') ∗
         ((fsp + 1056#64) ↦₆₄ u1056') ∗
         reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ stackAt fsp lagrangePrepareStack ∗ Frame)
        Q Q_panic) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool lim st s ∗ ptSliceAt xsPtr ones ∗ memRegion curBasis (24 * (rem + 1)) ∗
       memRegion (fsp + 656#64) 24 ∗ ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 ones.length) ∗
       ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
       ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗
       ((fsp + 1056#64) ↦₆₄ u1056) ∗
       reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ stackAt fsp lagrangePrepareStack ∗ Frame)
      Q Q_panic := by
  induction rem generalizing st i s curBasis u216 u224 u1040 u1048 u1056 Frame with
  | zero =>
    have hfit1 : FitsEnv M lim st (FallbackBasisStepEnv ones.length) :=
      fitsEnv_of_repeatSeqEnv_one hfit
    rw [memRegion_split_24_succ curBasis 0 (by omega), Nat.mul_zero, ProofLib.memRegion_zero,
      sepConj_emp]
    refine lagrangeBasisLoop_step_placed_sepWPp hA hcomp_ok 0 i ones hones_ne hbound hsum
      s0 s hcl fsp xsPtr curBasis hfsp_align u216 u224 u1040 u1048 u1056 Frame R
      hpc hrun hsp htrace hx19 hx20 hx21 hx22 hx29 hfit1 ?_
    intro evs s1 u216' u224' u1040' u1048' u1056' hevs hcl1
      hpc1 hrun1 hsp1 htr1 hvregs1 _ hx20_1 _ hx22_1 hx24_1 hx25_1 hx27_1 hx28_1 hx29_1
    have hpoly_one :
        polyListOf A.repAlloc curBasis (lagrangeBasisFrom ones i 1) =
          polyOf A.repAlloc curBasis (lagrangeInterpolatePtPure ones i) := by
      simp [lagrangeBasisFrom, polyListOf, arrayAt]
    have hevs_rep : RepeatSeqEnv 1 (FallbackBasisStepEnv ones.length) evs := by
      have h1 : RepeatSeqEnv 1 (FallbackBasisStepEnv ones.length) (evs ++ []) :=
        SeqEnv.append hevs rfl
      rwa [List.append_nil] at h1
    rw [← hpoly_one]
    exact hcont evs s1 u216' u224' u1040' u1048' u1056' hevs_rep hcl1
      hpc1 hrun1 hsp1 htr1 hvregs1 hx20_1 hx22_1 hx24_1 hx25_1 hx27_1 hx28_1 hx29_1
  | succ r ih =>
    obtain ⟨hfit_head, hfit_tail⟩ := fitsEnv_repeatSeqEnv_succ r ones.length hfit
    rw [memRegion_split_24_succ curBasis (r + 1) (by omega)]
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (lagrangeBasisLoop_step_placed_sepWPp hA hcomp_ok (r + 1) i ones hones_ne hbound hsum
        s0 s hcl fsp xsPtr curBasis hfsp_align u216 u224 u1040 u1048 u1056
        (memRegion (curBasis + 24#64) (24 * (r + 1)) ∗ Frame) R
        hpc hrun hsp htrace hx19 hx20 hx21 hx22 hx29 hfit_head ?_)
    intro evs1 s1 u216' u224' u1040' u1048' u1056' hevs1 hcl1
      hpc1 hrun1 hsp1 htr1 hvregs1 hx19_1 hx20_1 hx21_1 hx22_1 hx24_1 hx25_1 hx27_1 hx28_1 hx29_1
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (ih (i + 1) (by omega) s1 hcl1 (curBasis + 24#64) u216' u224' u1040' u1048' u1056'
        (polyOf A.repAlloc curBasis (lagrangeInterpolatePtPure ones i) ∗ Frame)
        hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx29_1 (hfit_tail evs1 hevs1) ?_)
    intro evs2 s2 u216'' u224'' u1040'' u1048'' u1056'' hevs2 hcl2
      hpc2 hrun2 hsp2 htr2 hvregs2 hx20_2 hx22_2 hx24_2 hx25_2 hx27_2 hx28_2 hx29_2
    have hpoly_cons :
        polyListOf A.repAlloc curBasis (lagrangeBasisFrom ones i (r + 2)) =
          polyOf A.repAlloc curBasis (lagrangeInterpolatePtPure ones i) ∗
          polyListOf A.repAlloc (curBasis + 24#64) (lagrangeBasisFrom ones (i + 1) (r + 1)) := rfl
    have hevs12 :
        RepeatSeqEnv (r + 2) (FallbackBasisStepEnv ones.length) (evs1 ++ evs2) :=
      SeqEnv.append hevs1 hevs2
    refine SepWPp.weaken_pre
      (by
        rw [hpoly_cons, ← LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
        exact Entails.of_eq (by sep_ac_rfl))
      (hcont (evs1 ++ evs2) s2 u216'' u224'' u1040'' u1048'' u1056'' hevs12 hcl2
        hpc2 hrun2 hsp2 htr2 (hvregs2.trans hvregs1) hx20_2 hx22_2
        (by rw [hx24_2, hx24_1]) (by rw [hx25_2, hx25_1])
        (by rw [hx27_2, hx27_1])
        (by rw [hx28_2, hx28_1]) hx29_2)

end LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysFallbackLoopPlacedBudget

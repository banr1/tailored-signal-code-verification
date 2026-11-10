/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysFallbackLoop
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.EpiloguePlaced
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysDefs
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysFallbackPlaced
import ProofLib.SepLogic.WPp

/-!
# `<PolyEncoder as Encoder>::next_chunk` (Block `416`): Placed Dynamic Lagrange Basis Loop

Relocatable `[LibsignalPlacement]` verification of the dynamic Lagrange basis construction loop
(`+4128 -> +4368`) in Block `416`.
-/

@[expose] public section

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Poly.NextChunk

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.ComputeAt
open CryptoVerification.SpqrV1.Poly.LagrangePrepare
open CryptoVerification.SpqrV1.Poly.LagrangeComplete
open CryptoVerification.CodeLayout

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre
  LagrangePrepare.sp_setPC_pre LagrangePrepare.sp_setMem_setPC_pre
  LagrangePrepare.readReg64_setPC_pre LagrangePrepare.readReg64_setMem_setPC_pre
  LagrangePrepare.readReg32_setPC_pre LagrangePrepare.readReg32_setMem_setPC_pre
  LagrangePrepare.readReg_setPC_pre LagrangePrepare.readReg_setMem_setPC_pre

@[local arm64_norm, local wp_norm] private theorem exists_pow_two_eq_two_fbl_pl :
    (∃ k : Nat, 2 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨1, rfl⟩

@[local arm64_norm, local wp_norm] private theorem exists_pow_two_eq_eight_fbl_pl :
    (∃ k : Nat, 8 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨3, rfl⟩

attribute [local simp, local arm64_norm, local wp_norm]
  ofNat_succ_sub_one_fb ofNat_succ_add_neg_one_fb ofNat_add_one_eq_succ_fb
  shl_one_ofNat_eq shl_one_ofNat_eq_nat

attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  conditionHolds_mi_subsPState64 conditionHolds_pl_subsPState64
  conditionHolds_eq_addsPState64 conditionHolds_ne_addsPState64

/-! ## 1. `LibsignalCodeLoaded`-Preserving `SepWPp` Sequencing & Call Helpers -/

/-- Sequence a `SepWP` segment to `mid` followed by `SepWPp` to `ret`, preserving
    `LibsignalCodeLoaded lsmpl ·.mem` across `mid`. -/
theorem sepWPp_seq_lscl_fb [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LibsignalCodeLoaded lsmpl sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.seq_frozen (fun _ _ h0 hkf => h0.of_keepsFrozen hkf) hcl h

/-- Augment `spec.post` with `⌜LibsignalCodeLoaded lsmpl sf.mem⌝`. -/
abbrev withPostLsCl [LibsignalPlacement] {α : Type} (spec : Spec α) : Spec α :=
  { spec with post := fun x s0 sf => ⌜LibsignalCodeLoaded lsmpl sf.mem⌝ ∗ spec.post x s0 sf }

/-- Preserve `LibsignalCodeLoaded lsmpl` across any `subroutine_ok` call on Block `416`
    whose precondition fixes `s0.mem = m` (`withMemEq m spec`). -/
theorem subroutine_ok_keep_lscl [LibsignalPlacement] {α : Type}
    {ext : String → Option (State → State)} {entry : BitVec 64}
    {m : Memory} {spec : Spec α}
    (hcall : subroutine_ok ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      entry (withMemEq m spec))
    (hcl : LibsignalCodeLoaded lsmpl m) :
    subroutine_ok ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      entry (withMemEq m (withPostLsCl spec)) := by
  have hcaller : IsLsBlockProg ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      416 (Rust.withPanics ext) := inferInstance
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  have ⟨hm0, _⟩ := extract_withMemEq hpre
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := hm0 ▸ hcl
  have hQL : ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)).CodeLoaded s0.mem :=
    hcaller.eq_blockProgram ▸
      hcl0 416 (by decide) (by decide) (Rust.withPanics ext) (fun _ => none) Syscall.standard
  obtain ⟨sf, hsteps, hout, _⟩ := hcall.no_fault_before_outcome x R s0 hpc hrun hpre hsp hQL
  refine reaches_outcome_steps hsteps (reaches_outcome.of_outcome ?_)
  rcases hout with ⟨hret, hregs, hpost⟩ | hpan | hexit | hoom
  · refine Or.inl ⟨hret, hregs, ?_⟩
    have hcl_f : LibsignalCodeLoaded lsmpl sf.mem :=
      hcl0.of_keepsFrozen hsteps.keepsFrozen
    dsimp only [withMemEq, withPostLsCl]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hcl_f, hpost⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hexit))
  · exact Or.inr (Or.inr (Or.inr hoom))

theorem call_lagrangePrepare_placed_sepWPp [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    {ret_pc ret fsp out ptsPtr : BitVec 64} {pts : List Pt} {s0 s : State} {F P R : SepProp}
    {Q : State → SepProp → Prop}
    (hA : AllocContractsPlaced A ext)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hlen_bound : 4 * (pts.length + 1) < 2 ^ 63)
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
      tokenInitPlacedAt ∗ A.pool ∗ stackAt fsp lagrangePrepareStack) ∗ F)
    (hnext : ∀ sf : State, LibsignalCodeLoaded lsmpl sf.mem →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = fsp → CalleeSavedPreserved s sf →
      sf.trace = s0.trace →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret sf
        ((polyOf A out (lagrangePreparePure pts) ∗ ptSliceAt ptsPtr pts ∗
          reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool ∗ stackAt fsp lagrangePrepareStack) ∗ F) Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  have hsp_al : s.spAligned = true := by
    simp [State.spAligned, hsp_eq, beq_iff_eq.mp hfsp_al]
  let a : LagrangePrepareArgs := { out := out, ptsPtr := ptsPtr, pts := pts, hlen_bound := hlen_bound }
  refine SepWPp.call (x := a) (ret_pc := ret_pc) (F := F)
    (subroutine_ok_keep_lscl (hA.lagrangePrepare_blk_ok hcl) hcl)
    hpc hrun hsp_al hlr
    (fun R' hm => ?_)
    (fun _ _ _ _ hex => ?_)
    (fun sf _ hm => ?_)
    (fun sf hpcf hrunf hspf hcsf => ?_)
  · rw [hP] at hm
    dsimp only [withMemEq, withPostLsCl, lagrangePreparePlacedSpec, a]
    rw [hsp_eq]
    have hm1 : s.mem ⊨
        (memRegion out 24 ∗ ptSliceAt ptsPtr pts ∗ reduceTablePlacedAt ∗
          tokenInitPlacedAt ∗ A.pool ∗ stackAt fsp lagrangePrepareStack) ∗
        ⌜s.mem = s.mem⌝ ∗ (F ∗ R') := by
      rw [sepConj_left_comm _ ⌜s.mem = s.mem⌝, satisfies_pure_sepConj]
      exact ⟨rfl, by simpa only [sepConj_assoc] using hm⟩
    have hm2 : s.mem ⊨
        ⌜s.readReg64 Reg.x0 = out ∧ s.readReg64 Reg.x1 = ptsPtr ∧
          s.readReg64 Reg.x2 = BitVec.ofNat 64 pts.length⌝ ∗
        ((memRegion out 24 ∗ ptSliceAt ptsPtr pts ∗ reduceTablePlacedAt ∗
          tokenInitPlacedAt ∗ A.pool ∗ stackAt fsp lagrangePrepareStack) ∗
         ⌜s.mem = s.mem⌝ ∗ (F ∗ R')) := by
      rw [satisfies_pure_sepConj]
      exact ⟨⟨hx0, hx1, hx2⟩, hm1⟩
    simpa only [sepConj_assoc] using hm2
  · dsimp only [withMemEq, withPostLsCl, lagrangePreparePlacedSpec] at hex
    exact not_satisfies_false_sepConj hex
  · dsimp only [withMemEq, withPostLsCl, lagrangePreparePlacedSpec] at hm
    have hpan_tr : allocFailedIn s sf = allocFailedIn s0 sf := by
      unfold allocFailedIn; rw [htr]
    rw [hpan_tr, htr, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm
    rcases hm with ⟨hpan, hm2⟩
    rw [← sepConj_assoc] at hm2
    unfold nextChunkOnPanic
    exact allowPanic_panicked (φ := allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) hpan hm2
  · have hspf' : sf.sp = fsp := hspf.trans hsp_eq
    conv => arg 4; simp only [withMemEq, withPostLsCl, lagrangePreparePlacedSpec, a, hsp_eq, sepConj_assoc]
    apply SepWPp.pure_left; intro hclf
    apply SepWPp.pure_left; intro htrf
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext sf hclf hpcf hrunf hspf' hcsf (htrf.trans htr))

theorem call_lagrangeComplete_placed_sepWPp [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    {ret_pc ret fsp coeffsPtr ptsPtr : BitVec 64} {self : Poly} {pts : List Pt} {i : Nat}
    {s0 s : State} {F P R : SepProp} {Q : State → SepProp → Prop}
    (hA : AllocContractsPlaced A ext)
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
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ stackAt fsp lagrangeCompleteStack) ∗ F)
    (hnext : ∀ sf : State, LibsignalCodeLoaded lsmpl sf.mem →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = fsp → CalleeSavedPreserved s sf →
      sf.trace = s0.trace →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret sf
        ((gf16SliceAt coeffsPtr (lagrangeCompletePure self pts i).coefficients ∗
          ptSliceAt ptsPtr pts ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          stackAt fsp lagrangeCompleteStack) ∗ F) Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  have hsp_al : s.spAligned = true := by
    simp [State.spAligned, hsp_eq, beq_iff_eq.mp hfsp_al]
  let a : LagrangeCompleteArgs :=
    { coeffsPtr := coeffsPtr, ptsPtr := ptsPtr, self := self, pts := pts, i := i }
  refine SepWPp.call (x := a) (ret_pc := ret_pc) (F := F)
    (subroutine_ok_keep_lscl (hA.lagrangeComplete_blk_ok hcl) hcl)
    hpc hrun hsp_al hlr
    (fun R' hm => ?_)
    (fun _ _ _ _ hex => ?_)
    (fun _ _ hpan => ?_)
    (fun sf hpcf hrunf hspf hcsf => ?_)
  · rw [hP] at hm
    dsimp only [withMemEq, withPostLsCl, lagrangeCompletePlacedSpec, a]
    rw [hsp_eq]
    have hm1 : s.mem ⊨
        (gf16SliceAt coeffsPtr self.coefficients ∗ ptSliceAt ptsPtr pts ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ stackAt fsp lagrangeCompleteStack) ∗
        ⌜s.mem = s.mem⌝ ∗ (F ∗ R') := by
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
         ⌜s.mem = s.mem⌝ ∗ (F ∗ R')) := by
      rw [satisfies_pure_sepConj]
      exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hi, hself_bound, hpts_bound⟩, hm1⟩
    simpa only [sepConj_assoc] using hm2
  · dsimp only [withMemEq, withPostLsCl, lagrangeCompletePlacedSpec] at hex
    exact not_satisfies_false_sepConj hex
  · dsimp only [withMemEq, withPostLsCl, lagrangeCompletePlacedSpec] at hpan
    rw [sepConj_assoc] at hpan
    exact (not_satisfies_false_sepConj hpan).elim
  · have hspf' : sf.sp = fsp := hspf.trans hsp_eq
    conv => arg 4; simp only [withMemEq, withPostLsCl, lagrangeCompletePlacedSpec, a, hsp_eq, sepConj_assoc]
    apply SepWPp.pure_left; intro hclf
    apply SepWPp.pure_left; intro htrf
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext sf hclf hpcf hrunf hspf' hcsf (htrf.trans htr))

/-! ## 2. Single Iteration & Full Lagrange Basis Loop (`(blkPl_416).base + 4128#64 .. + 4368#64`) -/

/-- Sub-step 1 of the Lagrange basis loop (`+4128 -> +4176`):
    calls `lagrange_interpolate_prepare`, unfolds the resulting `Poly`, and calls
    `lagrange_interpolate_complete`. -/
theorem lagrangeBasisLoop_prep_comp_placed_sepWPp [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} {Q : State → SepProp → Prop}
    (hA : AllocContractsPlaced A ext)
    (i : Nat) (ones : List Pt) (hones_ne : ones ≠ [])
    (hbound : ones.length ≤ 0x0555555555555555) (hi_lt : i < ones.length)
    (s0 s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (fsp xsPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (Frame R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 4128#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 i)
    (hx20 : s.readReg64 .x20 = xsPtr)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 ones.length)
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
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s1
        (A.pool ∗
         ptSliceAt xsPtr ones ∗
         ((fsp + 656#64) ↦₆₄ prepCap) ∗
         ((fsp + 664#64) ↦₆₄ prepPtr) ∗
         ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 (ones.length + 1)) ∗
         A.live prepPtr (prepCap.toNat * 2) 2 ∗
         gf16SliceAt prepPtr (lagrangeCompletePure (lagrangePreparePure ones) ones i).coefficients ∗
         memRegion (prepPtr + BitVec.ofNat 64 (2 * (ones.length + 1))) (2 * (prepCap.toNat - (ones.length + 1))) ∗
         ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 ones.length) ∗
         reduceTablePlacedAt ∗
         tokenInitPlacedAt ∗
         stackAt fsp lagrangeCompleteStack ∗
         memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
           (lagrangePrepareStack - lagrangeCompleteStack) ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗
       ptSliceAt xsPtr ones ∗
       memRegion (fsp + 656#64) 24 ∗
       ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 ones.length) ∗
       reduceTablePlacedAt ∗
       tokenInitPlacedAt ∗
       stackAt fsp lagrangePrepareStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  try dsimp only [BitVec.ofNat_eq_ofNat] at hpc hcont ⊢
  apply sepWPp_seq_lscl_fb hcl (mid := lsmpl.base 372)
  wp_steps
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
  intro hcl1
  refine call_lagrangePrepare_placed_sepWPp hA hcl1 (by omega)
    (ret_pc := (blkPl_416).base + 4144#64) (fsp := fsp) (out := fsp + 656#64) (ptsPtr := xsPtr) (pts := ones)
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
    (sepConj_mono_fbl (sepConj_mono_fbl (polyOf_prepare_unfold A fsp ones) (Entails.refl _)) (Entails.refl _)) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWPp.exists_elim; intro prepCap
  apply SepWPp.exists_elim; intro prepPtr
  apply SepWPp.pure_left; rintro ⟨hprep_le, hprep_bound, hprep_ptr, hprep_cap⟩
  apply sepWPp_seq_lscl_fb hclPrep (mid := lsmpl.base 373)
  wp_steps
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
  intro hcl2
  rw [stackAt_lagrangePrepare_split_complete fsp]
  refine call_lagrangeComplete_placed_sepWPp hA hcl2 hi_lt
    (self := lagrangePreparePure ones) (pts := ones) (i := i)
    (ret_pc := (blkPl_416).base + 4176#64) (fsp := fsp) (coeffsPtr := prepPtr) (ptsPtr := xsPtr)
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
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
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

/-- Sub-step 2 of the Lagrange basis loop (`+4176 -> +4304`):
    allocates the `2 * n`-byte `Poly` coefficient buffer, `memcpy`s the tail coefficients `[1..n]`,
    and `__rust_dealloc`s the temporary `prepPtr` buffer. -/
theorem lagrangeBasisLoop_copy_free_placed_sepWPp [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} {Q : State → SepProp → Prop}
    (hA : AllocContractsPlaced A ext)
    (i : Nat) (ones : List Pt) (hones_ne : ones ≠ [])
    (hbound : ones.length ≤ 0x0555555555555555)
    (s0 s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (fsp prepCap prepPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hprep_le : ones.length + 1 ≤ prepCap.toNat)
    (hprep_bound : prepCap.toNat * 2 < 2 ^ 63)
    (hprep_ptr : prepPtr ≠ 0#64)
    (hprep_cap : prepCap ≠ 0#64)
    (u216 u224 : BitVec 64) (Frame R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 4176#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (ones.length + 1))
    (hx26 : s.readReg64 .x26 = prepPtr)
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
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s1
        (A.pool ∗
         A.live newPtr (2 * ones.length) 2 ∗
         (newPtr ↦ₛ gf16SliceBytes (lagrangeInterpolatePtPure ones i).coefficients) ∗
         ((fsp + 656#64) ↦₆₄ prepCap) ∗
         ((fsp + 664#64) ↦₆₄ prepPtr) ∗
         ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 ones.length) ∗
         ((fsp + 216#64) ↦₆₄ BitVec.ofNat 64 ones.length) ∗
         ((fsp + 224#64) ↦₆₄ newPtr) ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗
       ((fsp + 656#64) ↦₆₄ prepCap) ∗
       ((fsp + 664#64) ↦₆₄ prepPtr) ∗
       A.live prepPtr (prepCap.toNat * 2) 2 ∗
       gf16SliceAt prepPtr (lagrangeCompletePure (lagrangePreparePure ones) ones i).coefficients ∗
       memRegion (prepPtr + BitVec.ofNat 64 (2 * (ones.length + 1))) (2 * (prepCap.toNat - (ones.length + 1))) ∗
       ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 ones.length) ∗
       ((fsp + 216#64) ↦₆₄ u216) ∗
       ((fsp + 224#64) ↦₆₄ u224) ∗
       stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  have hn_pos : 0 < ones.length := List.length_pos_iff.mpr hones_ne
  have hshim := hA.shim_ok
  simp only [sessionShimSpec] at hshim
  have halloc := hA.alloc_ok
  simp only [rustAllocSpec] at halloc
  have hmemcpy := hA.session_memcpy_ok
  simp only [sessionMemcpySpec] at hmemcpy
  have hdealloc := hA.dealloc_ok
  simp only [rustDeallocSpec] at hdealloc
  have hpanic4592 := fun (s : State) (P : SepProp) =>
    @sepWPp_panic_of_sepWP_4592_placed _ ext Q hA.handle_error s0 s P R
  try dsimp only [BitVec.ofNat_eq_ofNat] at hpc hshim halloc hmemcpy hdealloc hpanic4592 hcont ⊢
  obtain ⟨c0, hc0⟩ := lagrangeComplete_prepare_head_tail ones i
  rw [hc0]
  have hn1_ne0 := ofNat_succ_ne_zero hbound
  obtain ⟨hn_ne0, h2n_ne0⟩ := ofNat_pos_ne_zero hn_pos hbound
  obtain ⟨hmsb1, hmsb2⟩ := bit62_shl_one_false hbound
  have hult := ult_max_2n_false hbound
  have hlayout2n : LayoutOk (2 * ones.length) 2 := ⟨by omega, ⟨1, rfl⟩, by omega⟩
  have h2n_toNat : (BitVec.ofNat 64 (2 * ones.length)).toNat = 2 * ones.length :=
    Nat.mod_eq_of_lt (by omega)
  apply sepWPp_seq_lscl_fb hcl (mid := (blkPl_416).base + 4228#64)
  apply SepWP.fold (gf16SliceAt_cons_memRegion2 prepPtr c0 _) (by sep_frame)
  wp_steps; wp_call hshim; wp_steps; wp_call halloc
  refine SepWP.done hpc_sf_1 hrun_sf_1 ?_
  intro hcl1
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · conv => arg 4; simp only [hoom, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; intro htr_oom
    refine hpanic4592 _ _ ?_
    wp_steps
    exact SepWP.done (by simp only [wp_norm, hoom, beq_self_eq_true, ↓reduceIte]) (by wp_norm_lhs)
      (by simp only [arm64_norm, wp_norm]; rw [‹sf.trace = s.trace›, htrace] at htr_oom; exact htr_oom)
  · conv => arg 4; simp only [hoom, ↓reduceIte, sepConj_assoc, hx23, h2n_toNat]
    apply sepWPp_pure_mid; intro ⟨_, htr_alloc⟩
    have hcond_oom : ¬(sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = true := by
      simpa [beq_iff_eq] using hoom
    have hsp_sf1 : sf_1.sp = fsp := by rw [‹sf_1.sp = sf.sp›, ‹sf.sp = s.sp›, hsp]
    have hx22_sf1 : sf_1.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 ones.length := by
      simp only [wp_norm, h_15, h_5, hx23]
    have hx23_sf1 : sf_1.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 (2 * ones.length) := by
      simp only [wp_norm, h_16, h_6, hx23]
    have hx26_sf1 : sf_1.readReg64 (Reg.gpr 26#5) = prepPtr := by
      simp only [wp_norm, h_19, h_9, hx26]
    have hlen_interp : (gf16SliceBytes (lagrangeInterpolatePtPure ones i).coefficients).length = 2 * ones.length := by
      simp [lagrangeInterpolatePtPure_length]
    apply sepWPp_seq_lscl_fb hcl1 (mid := (blkPl_416).base + 4280#64)
    wp_steps; wp_call hmemcpy
    refine SepWP.done hpc_sf_2 hrun_sf_2 ?_
    intro hcl2
    have hrecomb := memRegion_recombine_prepare prepPtr prepCap ones.length
      (gf16SliceBytes (lagrangeInterpolatePtPure ones i).coefficients) hlen_interp hprep_le hprep_bound
    have hprep_cap_bne : ¬(prepCap == 0#64) = true := by simpa [beq_iff_eq] using hprep_cap
    have hcap_shl := shl_one_cap_toNat_nat hprep_bound
    have hsp_sf2 : sf_2.sp = fsp := by rw [‹sf_2.sp = _›]; simp only [wp_norm, hsp_sf1]
    have hx26_sf2 : sf_2.readReg64 (Reg.gpr 26#5) = prepPtr := by
      rw [h_29]; simp only [wp_norm, hx26_sf1]
    apply sepWPp_seq_lscl_fb hcl2 (mid := (blkPl_416).base + 4304#64)
    apply SepWP.fold hrecomb (by sep_frame)
    wp_steps; wp_call hdealloc
    refine SepWP.done hpc_sf_3 hrun_sf_3 ?_
    intro hcl3
    refine SepWPp.weaken_pre (Entails.of_eq (by rw [hsp_sf2]; ac_rfl))
      (hcont sf_3 (sf_1.readReg64 (Reg.gpr 0#5)) hcl3 hoom
        hpc_sf_3 hrun_sf_3
        (by rw [‹sf_3.sp = _›, hsp_sf2])
        (by rw [hpost_1, hpost, htr_alloc, ‹sf.trace = s.trace›, htrace])
        (by simp only [arm64_norm, wp_norm, *])
        (by rw [h_33, h_22, h_12, h_2])
        (by rw [h_34, h_23, h_13, h_3])
        (by rw [h_35, h_24, h_14, h_4])
        (by rw [h_36, h_25]; simp only [wp_norm, hx22_sf1])
        (by rw [h_38, h_27, h_17, h_7])
        (by rw [h_39, h_28, h_18, h_8])
        (by rw [h_41, h_30, h_20, h_10])
        (by rw [h_42, h_31, h_21, h_11])
        (by rw [hcs_sf_2, hcs_sf_1, hcs_sf, hpost_sf]))

/-- Sub-step 3 of the Lagrange basis loop (`+4304 -> +4128 / +4368`):
    stores the `Poly` header into `curBasis`, increments `i`, and branches back to `+4128` or exits to `+4368`. -/
theorem lagrangeBasisLoop_tail_placed_sepWPp [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} {Q : State → SepProp → Prop}
    (rem i : Nat) (ones : List Pt) (hones_ne : ones ≠ [])
    (hbound : ones.length ≤ 0x0555555555555555)
    (hsum : i + (rem + 1) = ones.length)
    (s0 s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (fsp curBasis newPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hnew_ptr : newPtr ≠ 0#64)
    (u656 u664 u1040 u1048 u1056 : BitVec 64) (Frame R : SepProp)
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
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s1
        (polyOf A curBasis (lagrangeInterpolatePtPure ones i) ∗
         memRegion (fsp + 656#64) 24 ∗
         ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 ones.length) ∗
         ((fsp + 216#64) ↦₆₄ u216') ∗
         ((fsp + 224#64) ↦₆₄ u224') ∗
         ((fsp + 1040#64) ↦₆₄ u1040') ∗
         ((fsp + 1048#64) ↦₆₄ u1048') ∗
         ((fsp + 1056#64) ↦₆₄ u1056') ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (A.live newPtr (2 * ones.length) 2 ∗
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
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  have hn_pos : 0 < ones.length := List.length_pos_iff.mpr hones_ne
  try dsimp only [BitVec.ofNat_eq_ofNat] at hpc hcont ⊢
  obtain ⟨hcmn1, hcmn2, hcmn3, hcmn4⟩ := adds_one_ne_zero (i := i) (by omega)
  have hstur_addr : (fsp + 1104#64) + 0xffffffffffffffd0#64 = fsp + 1056#64 := by bv_omega
  have hpoly_intro := polyOf_of_pointsToBytes A curBasis newPtr
    (lagrangeInterpolatePtPure ones i) ones.length hn_pos (by omega) hnew_ptr
    (lagrangeInterpolatePtPure_length ones i)
  have hmem24 := polyHeader_entails_memRegion24_off fsp
    (BitVec.ofNat 64 ones.length) newPtr (BitVec.ofNat 64 (ones.length + 1))
  apply sepWPp_seq_lscl_fb hcl (mid := (blkPl_416).base + 4348#64)
  apply SepWP.fold (Entails.of_eq (memRegion_split_polyHeader_fbl curBasis)) (by sep_frame)
  apply sepWP_exists_left_sep; intro uBasis16
  apply sepWP_exists_left_sep; intro uBasis8
  apply sepWP_exists_left_sep; intro uBasis0
  wp_steps
  apply SepWP.fold hpoly_intro (by sep_frame)
  apply SepWP.fold hmem24 (by sep_frame)
  refine SepWP.done
    (by simp only [wp_norm, hx19, hcmn1, hcmn2, hcmn3, hcmn4, Bool.false_eq_true, ↓reduceIte])
    (by wp_norm_lhs) ?_
  intro hcl1
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
    apply sepWPp_seq_lscl_fb hcl1 (mid := (blkPl_416).base + 4368#64)
    wp_steps
    refine SepWP.done
      (by simp only [wp_norm, hx19, ofNat_add_one_eq_succ_fb, hi1_eq, bne_self_eq_false,
            BitVec.sub_self, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte])
      (by wp_norm_lhs) ?_
    intro hcl2
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hcont _ (BitVec.ofNat 64 ones.length) newPtr
        (BitVec.ofNat 64 ones.length) newPtr (BitVec.ofNat 64 ones.length) hcl2
        (by simp only [wp_norm, hx19, ofNat_add_one_eq_succ_fb, hi1_eq, bne_self_eq_false,
              BitVec.sub_self, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte])
        (by wp_norm_lhs)
        (by simp only [wp_norm, hsp])
        (by simp only [arm64_norm, wp_norm, htrace])
        rfl
        (by simp only [wp_norm, hx19, ofNat_add_one_eq_succ_fb, hi1_eq])
        (by simp only [wp_norm])
        (by simp only [wp_norm, hx21])
        (by simp only [wp_norm, hx22])
        (by simp only [wp_norm])
        (by simp only [wp_norm])
        (by simp only [wp_norm])
        (by simp only [wp_norm])
        (by simp only [wp_norm, hx29]))
  | succ r =>
    have hi1_ne : ones.length ≠ i + 1 := by omega
    obtain ⟨hcmp1, hcmp2, hcmp3⟩ := ofNat_ne_ofNat_false hi1_ne (by omega) (by omega)
    apply sepWPp_seq_lscl_fb hcl1 (mid := (blkPl_416).base + 4128#64)
    wp_steps
    refine SepWP.done
      (by simp only [wp_norm, hx19, ofNat_add_one_eq_succ_fb, hcmp1, hcmp2, hcmp3,
            Bool.false_eq_true, ↓reduceIte])
      (by wp_norm_lhs) ?_
    intro hcl2
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hcont _ (BitVec.ofNat 64 ones.length) newPtr
        (BitVec.ofNat 64 ones.length) newPtr (BitVec.ofNat 64 ones.length) hcl2
        (by simp only [wp_norm, hx19, ofNat_add_one_eq_succ_fb, hcmp1, hcmp2, hcmp3,
              Bool.false_eq_true, ↓reduceIte])
        (by wp_norm_lhs)
        (by simp only [wp_norm, hsp])
        (by simp only [arm64_norm, wp_norm, htrace])
        rfl
        (by simp only [wp_norm, hx19, ofNat_add_one_eq_succ_fb])
        (by simp only [wp_norm])
        (by simp only [wp_norm, hx21])
        (by simp only [wp_norm, hx22])
        (by simp only [wp_norm])
        (by simp only [wp_norm])
        (by simp only [wp_norm])
        (by simp only [wp_norm])
        (by simp only [wp_norm, hx29]))

/-- Combined single iteration of the Lagrange basis loop (`+4128 -> +4128 / +4368`). -/
theorem lagrangeBasisLoop_step_placed_sepWPp [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} {Q : State → SepProp → Prop}
    (hA : AllocContractsPlaced A ext)
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
    (hcont : ∀ s1 u216' u224' u1040' u1048' u1056',
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
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s1
        (A.pool ∗ ptSliceAt xsPtr ones ∗ polyOf A curBasis (lagrangeInterpolatePtPure ones i) ∗
         memRegion (fsp + 656#64) 24 ∗ ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 ones.length) ∗
         ((fsp + 216#64) ↦₆₄ u216') ∗ ((fsp + 224#64) ↦₆₄ u224') ∗
         ((fsp + 1040#64) ↦₆₄ u1040') ∗ ((fsp + 1048#64) ↦₆₄ u1048') ∗ ((fsp + 1056#64) ↦₆₄ u1056') ∗
         reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ stackAt fsp lagrangePrepareStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗ ptSliceAt xsPtr ones ∗ memRegion curBasis 24 ∗ memRegion (fsp + 656#64) 24 ∗
       ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 ones.length) ∗
       ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
       ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗ ((fsp + 1056#64) ↦₆₄ u1056) ∗
       reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ stackAt fsp lagrangePrepareStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (lagrangeBasisLoop_prep_comp_placed_sepWPp hA i ones hones_ne hbound (by omega)
      s0 s hcl fsp xsPtr hfsp_align
      (memRegion curBasis 24 ∗ ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
       ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗ ((fsp + 1056#64) ↦₆₄ u1056) ∗ Frame) R
      hpc hrun hsp htrace hx19 hx20 hx22 ?_)
  intro s1 prepCap prepPtr hcl1 hprep_le hprep_bound hprep_ptr hprep_cap
    hpc1 hrun1 hsp1 htr1 hvregs1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  refine SepWPp.weaken_pre
    (by
      have hst := stackAt_complete_to_alloc fsp
      refine Entails.trans (Entails.of_eq (show _ =
        (stackAt fsp lagrangeCompleteStack ∗
         memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
           (lagrangePrepareStack - lagrangeCompleteStack)) ∗
        (A.pool ∗ ((fsp + 656#64) ↦₆₄ prepCap) ∗ ((fsp + 664#64) ↦₆₄ prepPtr) ∗
         A.live prepPtr (prepCap.toNat * 2) 2 ∗
         gf16SliceAt prepPtr (lagrangeCompletePure (lagrangePreparePure ones) ones i).coefficients ∗
         memRegion (prepPtr + BitVec.ofNat 64 (2 * (ones.length + 1))) (2 * (prepCap.toNat - (ones.length + 1))) ∗
         ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 ones.length) ∗
         ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
         ptSliceAt xsPtr ones ∗ ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 (ones.length + 1)) ∗
         reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ memRegion curBasis 24 ∗
         ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗ ((fsp + 1056#64) ↦₆₄ u1056) ∗ Frame) by ac_rfl)) ?_
      refine Entails.trans (sepConj_mono_left hst) (Entails.of_eq (by ac_rfl)))
    (lagrangeBasisLoop_copy_free_placed_sepWPp hA i ones hones_ne hbound
      s0 s1 hcl1 fsp prepCap prepPtr hfsp_align hprep_le hprep_bound hprep_ptr hprep_cap u216 u224
      (memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
         (lagrangePrepareStack - allocHookStack) ∗
       ptSliceAt xsPtr ones ∗ ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 (ones.length + 1)) ∗
       reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ memRegion curBasis 24 ∗
       ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗ ((fsp + 1056#64) ↦₆₄ u1056) ∗ Frame) R
      hpc1 hrun1 hsp1 htr1 hx23_1 hx26_1 ?_)
  intro s2 newPtr hcl2 hnew_ptr hpc2 hrun2 hsp2 htr2 hvregs2 hx19_2 hx20_2 hx21_2 hx22_2 hx24_2 hx25_2 hx27_2 hx28_2 hx29_2
  refine SepWPp.weaken_pre
    (by
      have hst := stackAt_alloc_to_prepare fsp
      refine Entails.trans (Entails.of_eq (show _ =
        (stackAt fsp allocHookStack ∗
         memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
           (lagrangePrepareStack - allocHookStack)) ∗
        (A.live newPtr (2 * ones.length) 2 ∗
         (newPtr ↦ₛ gf16SliceBytes (lagrangeInterpolatePtPure ones i).coefficients) ∗
         memRegion curBasis 24 ∗
         ((fsp + 656#64) ↦₆₄ prepCap) ∗ ((fsp + 664#64) ↦₆₄ prepPtr) ∗
         ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 (ones.length + 1)) ∗
         ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 ones.length) ∗
         ((fsp + 216#64) ↦₆₄ BitVec.ofNat 64 ones.length) ∗ ((fsp + 224#64) ↦₆₄ newPtr) ∗
         ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗ ((fsp + 1056#64) ↦₆₄ u1056) ∗
         A.pool ∗ ptSliceAt xsPtr ones ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ Frame) by ac_rfl)) ?_
      refine Entails.trans (sepConj_mono_left hst) (Entails.of_eq (by ac_rfl)))
    (lagrangeBasisLoop_tail_placed_sepWPp rem i ones hones_ne hbound hsum
      s0 s2 hcl2 fsp curBasis newPtr hfsp_align hnew_ptr prepCap prepPtr u1040 u1048 u1056
      (A.pool ∗ ptSliceAt xsPtr ones ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
       stackAt fsp lagrangePrepareStack ∗ Frame) R
      hpc2 hrun2 hsp2 htr2
      (by rw [hx19_2, hx19_1]) (by rw [hx21_2, hx21_1, hx21]) hx22_2 (by rw [hx29_2, hx29_1, hx29]) ?_)
  intro s3 u216' u224' u1040' u1048' u1056' hcl3
    hpc3 hrun3 hsp3 htr3 hvregs3 hx19_3 hx20_3 hx21_3 hx22_3 hx24_3 hx25_3 hx27_3 hx28_3 hx29_3
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (hcont s3 u216' u224' u1040' u1048' u1056' hcl3
      hpc3 hrun3 hsp3 htr3 (by rw [hvregs3, hvregs2, hvregs1])
      hx19_3 (by rw [hx20_3, hx20_2, hx20_1]) hx21_3 hx22_3
      (by rw [hx24_3, hx24_2, hx24_1]) (by rw [hx25_3, hx25_2, hx25_1])
      (by rw [hx27_3, hx27_2, hx27_1]) (by rw [hx28_3, hx28_2, hx28_1]) hx29_3)

/-- Full Lagrange basis loop (`+4128 -> +4368`) over `rem + 1` iterations. -/
theorem lagrangeBasisLoop_placed_sepWPp [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} {Q : State → SepProp → Prop}
    (hA : AllocContractsPlaced A ext)
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
    (hcont : ∀ s1 u216' u224' u1040' u1048' u1056',
      LibsignalCodeLoaded lsmpl s1.mem →
      s1.pc = (blkPl_416).base + 4368#64 →
      s1.status = .Running → s1.sp = fsp → s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x20 = xsPtr → s1.readReg64 .x22 = BitVec.ofNat 64 ones.length →
      s1.readReg64 .x24 = s.readReg64 .x24 → s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x27 = s.readReg64 .x27 → s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = fsp + 1104#64 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s1
        (A.pool ∗ ptSliceAt xsPtr ones ∗
         polyListOf A curBasis (lagrangeBasisFrom ones i (rem + 1)) ∗
         memRegion (fsp + 656#64) 24 ∗ ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 ones.length) ∗
         ((fsp + 216#64) ↦₆₄ u216') ∗ ((fsp + 224#64) ↦₆₄ u224') ∗
         ((fsp + 1040#64) ↦₆₄ u1040') ∗ ((fsp + 1048#64) ↦₆₄ u1048') ∗ ((fsp + 1056#64) ↦₆₄ u1056') ∗
         reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ stackAt fsp lagrangePrepareStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗ ptSliceAt xsPtr ones ∗ memRegion curBasis (24 * (rem + 1)) ∗
       memRegion (fsp + 656#64) 24 ∗ ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 ones.length) ∗
       ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
       ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗ ((fsp + 1056#64) ↦₆₄ u1056) ∗
       reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ stackAt fsp lagrangePrepareStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  induction rem generalizing i s curBasis u216 u224 u1040 u1048 u1056 Frame with
  | zero =>
    rw [memRegion_split_24_succ curBasis 0 (by omega), Nat.mul_zero, ProofLib.memRegion_zero, sepConj_emp]
    refine lagrangeBasisLoop_step_placed_sepWPp hA 0 i ones hones_ne hbound hsum
      s0 s hcl fsp xsPtr curBasis hfsp_align u216 u224 u1040 u1048 u1056 Frame R
      hpc hrun hsp htrace hx19 hx20 hx21 hx22 hx29 ?_
    intro s1 u216' u224' u1040' u1048' u1056' hcl1
      hpc1 hrun1 hsp1 htr1 hvregs1 _ hx20_1 _ hx22_1 hx24_1 hx25_1 hx27_1 hx28_1 hx29_1
    have hpoly_one :
        polyListOf A curBasis (lagrangeBasisFrom ones i 1) =
          polyOf A curBasis (lagrangeInterpolatePtPure ones i) := by
      simp [lagrangeBasisFrom, polyListOf, arrayAt]
    rw [← hpoly_one]
    exact hcont s1 u216' u224' u1040' u1048' u1056' hcl1
      hpc1 hrun1 hsp1 htr1 hvregs1 hx20_1 hx22_1 hx24_1 hx25_1 hx27_1 hx28_1 hx29_1
  | succ r ih =>
    rw [memRegion_split_24_succ curBasis (r + 1) (by omega)]
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (lagrangeBasisLoop_step_placed_sepWPp hA (r + 1) i ones hones_ne hbound hsum
        s0 s hcl fsp xsPtr curBasis hfsp_align u216 u224 u1040 u1048 u1056
        (memRegion (curBasis + 24#64) (24 * (r + 1)) ∗ Frame) R
        hpc hrun hsp htrace hx19 hx20 hx21 hx22 hx29 ?_)
    intro s1 u216' u224' u1040' u1048' u1056' hcl1
      hpc1 hrun1 hsp1 htr1 hvregs1 hx19_1 hx20_1 hx21_1 hx22_1 hx24_1 hx25_1 hx27_1 hx28_1 hx29_1
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (ih (i + 1) (by omega) s1 hcl1 (curBasis + 24#64) u216' u224' u1040' u1048' u1056'
        (polyOf A curBasis (lagrangeInterpolatePtPure ones i) ∗ Frame)
        hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx29_1 ?_)
    intro s2 u216'' u224'' u1040'' u1048'' u1056'' hcl2
      hpc2 hrun2 hsp2 htr2 hvregs2 hx20_2 hx22_2 hx24_2 hx25_2 hx27_2 hx28_2 hx29_2
    have hpoly_cons :
        polyListOf A curBasis (lagrangeBasisFrom ones i (r + 2)) =
          polyOf A curBasis (lagrangeInterpolatePtPure ones i) ∗
          polyListOf A (curBasis + 24#64) (lagrangeBasisFrom ones (i + 1) (r + 1)) := rfl
    refine SepWPp.weaken_pre (by rw [hpoly_cons]; exact Entails.of_eq (by ac_rfl))
      (hcont s2 u216'' u224'' u1040'' u1048'' u1056'' hcl2
        hpc2 hrun2 hsp2 htr2 (hvregs2.trans hvregs1) hx20_2 hx22_2
        (by rw [hx24_2, hx24_1]) (by rw [hx25_2, hx25_1])
        (by rw [hx27_2, hx27_1]) (by rw [hx28_2, hx28_1]) hx29_2)

end CryptoVerification.SpqrV1.Poly.NextChunk

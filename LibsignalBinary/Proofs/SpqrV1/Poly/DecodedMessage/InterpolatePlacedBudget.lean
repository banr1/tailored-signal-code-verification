/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.Interpolate
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.Loop
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Inlined `lagrange_interpolate` Loops and Cleanup

Threads `RustCliAllocBudget M`, `VmPreserved`, `FreeOnlyEvs`, and `AllocCallPreserved` through the
inlined `Poly::lagrange_interpolate` loops, temporary-buffer deallocations, and cache-slot updates
on Block `418`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.InterpolatePlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification (LibsignalPlacement blkPC_418 blkPl_418 lsmpl lsρ)
open CryptoVerification.LibsignalSpqrV1 (GF16 Poly Pt)
open CryptoVerification.LibsignalTripleRatchet (sessionMemcpyRegionSpec)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.Alloc (spqrMemcpySym spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Poly (gf16SliceAt ptSliceAt)
open CryptoVerification.SpqrV1.Poly.AddChunk.AddChunkNorm (
  readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre readReg64_setPC_pre
  readReg_setMem_setPC_pre readReg_setPC_pre sp_setMem_setPC_pre sp_setPC_pre
)
open CryptoVerification.SpqrV1.Poly.DecodedMessage (
  bv32_xor_gf16 bv64_add1_norm bv64_add_one_beq_zero_false bv64_eq_succ_false bv64_lsl1_norm
  bv64_neg_add_succ_bne_one bv64_succ_bne_of_le fold_optPolyCacheSlotAt_some gf16ListBytes
  gf16SliceAt_eq_pointsToBytes gf16SliceAt_to_memRegion gf16Slice_spare_to_memRegion
  gf16_add_comm lagrangeAccumulateCoeffsTotal lagrangeAccumulateCoeffsTotal_length
  lagrangeInterpolateLoopTotal memRegion_16_eq_exists_pair memcpy_gf16Slice_pre
  memcpy_memRegion_gf16Slice_pre optPolyCacheSlotAt sp144_add_16 sp144_add_8 sp168_add_8
  sp192_add_8 sp216_add_48 sp672_aligned sp96_sub_120 sp96_sub_32 sp96_sub_40 sp96_sub_48
  sp96_sub_56 sp96_sub_64 sp96_sub_72 sp96_sub_80 sp96_sub_96 spqrRustDeallocSym
  toNat_two_mul_succ_eq_gf16ListBytes traceVRegs umaddl_24_ofNat
)
open CryptoVerification.SpqrV1.Poly.LagrangeComplete (
  lagrangeCompletePlacedSpec lagrangeCompletePure lagrangeCompletePure_length
  lagrangeCompleteStack
)
open CryptoVerification.SpqrV1.Poly.LagrangePrepare (
  gf16SliceAt_focus gf16SliceAt_update gf16SliceRest
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs
  RustCliAllocBudget VmPreserved rustCliDeallocBudgetSpec rustDeallocEvents
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

attribute [local wp_norm, local arm64_norm]
  bv64_lsl1_norm bv64_add1_norm bv32_xor_gf16 umaddl_24_ofNat
attribute [local wp_norm ↓, local arm64_norm ↓]
  sp96_sub_120 sp96_sub_96 sp96_sub_80 sp96_sub_72 sp96_sub_64
  sp96_sub_56 sp96_sub_48 sp96_sub_40 sp96_sub_32
  sp216_add_48 sp192_add_8 sp168_add_8 sp144_add_8 sp144_add_16

private def deallocFreeOnlySpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × Nat × Nat × M.σ) where
  pre := (rustCliDeallocBudgetSpec M A lim).pre
  post := fun (_, size, align, st) s0 sf =>
    ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf⌝ ∗
      A.pool lim (M.stepEvents (rustDeallocEvents size align) st) sf ∗ stackAt s0.sp allocHookStack

private theorem subroutine_ok_deallocFreeOnly [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok prog entry (deallocFreeOnlySpec M A lim) := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [rustCliDeallocBudgetSpec, deallocFreeOnlySpec] at hq ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  exact ⟨⟨hq.1.1.2.1, hq.1.1⟩, hq.2⟩

private theorem seq_vm_clean {P : Program} {b : BitVec 64} {Hk : String → Option (State → State)}
    {mid target : BitVec 64} {s : State}
    {Pre P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP (P.rebase b Hk) mid s Pre (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → VmPreserved s sm → Q sm →
      SepWP (P.rebase b Hk) target sm P_mid post) :
    SepWP (P.rebase b Hk) target s Pre post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨hvm, hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hvm hQ)

private theorem acp_of_PureStep {s sm : State}
    (hfs : sm.fs = s.fs := by first | rfl | (simp only [wp_norm, arm64_norm]; try rfl))
    (htr : sm.trace = s.trace := by first | rfl | (simp only [wp_norm, arm64_norm]; try rfl))
    (hsig : sm.sigActions = s.sigActions := by first | rfl | (simp only [wp_norm, arm64_norm]; try rfl))
    (htp : sm.tpidrEl0 = s.tpidrEl0 := by first | rfl | (simp only [wp_norm, arm64_norm]; try rfl))
    (hbrk : sm.brkStart = s.brkStart := by first | rfl | (simp only [wp_norm, arm64_norm]; try rfl))
    (horc : sm.oracle = s.oracle := by first | rfl | (simp only [wp_norm, arm64_norm]; try rfl))
    (hsym : sm.symtab = s.symtab := by first | rfl | (simp only [wp_norm, arm64_norm]; try rfl)) :
    AllocCallPreserved s sm :=
  ⟨hfs, htr, hsig, htp, hbrk, horc, hsym⟩

private theorem with_vm_cur {P : Program} {target : BitVec 64} {s s' : State}
    {Pre : SepProp} {post : State → SepProp → Prop}
    (hk : VmPreserved s s' → SepWP P target s' Pre post)
    (hvm : VmPreserved s s' := by simp [wp_norm, arm64_norm]) :
    SepWP P target s' Pre post :=
  hk hvm

/-! ## Inner Accumulation Loop (`(blkPl_418).base + 996#64` to `(blkPl_418).base + 1036#64`) -/

theorem lagrangeAccumulateInner_placed_sepWP [LibsignalPlacement]
    {ext : String → Option (State → State)} {ret_pc : BitVec 64}
    (acc_ptr ptr_l : BitVec 64) (k : Nat) (workingCoeffs : List GF16)
    (_hk_pos : 1 ≤ k) (hk_le : k ≤ 65536)
    (hlen_w : workingCoeffs.length = k + 1) :
    ∀ (rem j : Nat) (outCoeffs : List GF16) (s : State) (P : SepProp)
      (post : State → SepProp → Prop),
      rem > 0 →
      j + rem = k →
      outCoeffs.length = k →
      s.pc = (blkPl_418).base + 996#64 →
      s.status = .Running →
      s.readReg64 .x0 = BitVec.ofNat 64 (j + 1) →
      s.readReg64 .x8 = acc_ptr + BitVec.ofNat 64 (2 * j) →
      s.readReg64 .x25 = BitVec.ofNat 64 (k + 1) →
      s.readReg64 .x26 = ptr_l →
      s.readReg64 .x27 = 0#64 - BitVec.ofNat 64 k →
      (∀ sf : State,
        sf.pc = (blkPl_418).base + 1036#64 →
        sf.status = .Running →
        sf.sp = s.sp →
        traceVRegs sf = traceVRegs s →
        VmPreserved s sf →
        AllocCallPreserved s sf →
        sf.readReg64 .x19 = s.readReg64 .x19 →
        sf.readReg64 .x20 = s.readReg64 .x20 →
        sf.readReg64 .x21 = s.readReg64 .x21 →
        sf.readReg64 .x22 = s.readReg64 .x22 →
        sf.readReg64 .x23 = s.readReg64 .x23 →
        sf.readReg64 .x24 = s.readReg64 .x24 →
        sf.readReg64 .x25 = BitVec.ofNat 64 (k + 1) →
        sf.readReg64 .x26 = ptr_l →
        sf.readReg64 .x27 = 0#64 - BitVec.ofNat 64 k →
        sf.readReg64 .x28 = s.readReg64 .x28 →
        sf.readReg64 .x29 = s.readReg64 .x29 →
        sf.readReg64 .x30 = s.readReg64 .x30 →
        SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc sf
          (gf16SliceAt acc_ptr (lagrangeAccumulateCoeffsTotal j rem outCoeffs workingCoeffs) ∗
            gf16SliceAt ptr_l workingCoeffs ∗ P)
          post) →
      SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc s
        (gf16SliceAt acc_ptr outCoeffs ∗ gf16SliceAt ptr_l workingCoeffs ∗ P)
        post := by
  try dsimp only [BitVec.ofNat_eq_ofNat]
  intro rem
  induction rem using Nat.strongRecOn with
  | ind rem ih =>
    intro j outCoeffs s P post hrem hsum hlen_o
      hpc hstat hx0 hx8 hx25 hx26 hx27 hcont
    have hj_lt : j < k := by omega
    have hj_o : j < outCoeffs.length := by omega
    have hj1_w : j + 1 < workingCoeffs.length := by omega
    have heq_false := bv64_eq_succ_false k j hj_lt hk_le
    have hbne := bv64_neg_add_succ_bne_one k j hj_lt hk_le
    have hadd2_ptr : acc_ptr + BitVec.ofNat 64 (2 * j) + 2#64 =
        acc_ptr + BitVec.ofNat 64 (2 * (j + 1)) := by
      rw [BitVec.add_assoc, show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl,
        ← BitVec.ofNat_add, show 2 * j + 2 = 2 * (j + 1) by omega]
    have hreasm_w :
        ((ptr_l + BitVec.ofNat 64 (2 * (j + 1))) ↦₁₆ (workingCoeffs[j + 1]'hj1_w).value) ∗
          gf16SliceRest ptr_l workingCoeffs (j + 1) =
        gf16SliceAt ptr_l workingCoeffs :=
      (gf16SliceAt_focus hj1_w ptr_l).symm
    have hreasm_o :
        ((acc_ptr + BitVec.ofNat 64 (2 * j)) ↦₁₆
          (GF16.add (outCoeffs[j]'hj_o) (workingCoeffs[j + 1]'hj1_w)).value) ∗
          gf16SliceRest acc_ptr outCoeffs j =
        gf16SliceAt acc_ptr
          (outCoeffs.set j (GF16.add (outCoeffs[j]'hj_o) (workingCoeffs[j + 1]'hj1_w))) :=
      gf16SliceAt_update hj_o acc_ptr
        (GF16.add (outCoeffs[j]'hj_o) (workingCoeffs[j + 1]'hj1_w)).value
    have hrem_eq : rem = (rem - 1) + 1 := by omega
    have hstep_pure :
        lagrangeAccumulateCoeffsTotal j rem outCoeffs workingCoeffs =
          lagrangeAccumulateCoeffsTotal (j + 1) (rem - 1)
            (outCoeffs.set j (GF16.add (outCoeffs[j]'hj_o) (workingCoeffs[j + 1]'hj1_w)))
            workingCoeffs := by
      conv => lhs; rw [hrem_eq]
      simp [lagrangeAccumulateCoeffsTotal, List.getElem?_eq_getElem hj_o,
        List.getElem?_eq_getElem hj1_w]
    rw [gf16SliceAt_focus hj_o acc_ptr, gf16SliceAt_focus hj1_w ptr_l]
    refine seq_vm_clean
      (mid := if decide (j + 1 ≠ k) then (blkPl_418).base + 996#64 else (blkPl_418).base + 1036#64)
      (P_mid :=
        gf16SliceAt acc_ptr
          (outCoeffs.set j (GF16.add (outCoeffs[j]'hj_o) (workingCoeffs[j + 1]'hj1_w))) ∗
          gf16SliceAt ptr_l workingCoeffs ∗ P)
      (Q := fun s1 =>
        s1.sp = s.sp ∧
        traceVRegs s1 = traceVRegs s ∧
        AllocCallPreserved s s1 ∧
        s1.readReg64 .x0 = BitVec.ofNat 64 ((j + 1) + 1) ∧
        s1.readReg64 .x8 = acc_ptr + BitVec.ofNat 64 (2 * (j + 1)) ∧
        s1.readReg64 .x19 = s.readReg64 .x19 ∧
        s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg64 .x21 = s.readReg64 .x21 ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = BitVec.ofNat 64 (k + 1) ∧
        s1.readReg64 .x26 = ptr_l ∧
        s1.readReg64 .x27 = 0#64 - BitVec.ofNat 64 k ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = s.readReg64 .x30)
      ?_ ?_
    · by_vm_steps (
        wp_steps 10
        refine SepWP.weaken_pre
          (show _ ⊢
            gf16SliceAt acc_ptr
              (outCoeffs.set j (GF16.add (outCoeffs[j]'hj_o) (workingCoeffs[j + 1]'hj1_w))) ∗
              gf16SliceAt ptr_l workingCoeffs ∗ P by
            rw [gf16_add_comm (workingCoeffs[j + 1]'hj1_w) (outCoeffs[j]'hj_o),
              ← hreasm_o, ← hreasm_w]
            exact Entails.of_eq (by sep_ac_rfl)) ?_
        exact SepWP.done (by simp [wp_norm, arm64_norm, *])
          (by simp [wp_norm, arm64_norm, hstat])
          ⟨by simp [wp_norm, arm64_norm], Entails.refl _,
           by simp [wp_norm, arm64_norm],
           by simp [wp_norm, arm64_norm],
           acp_of_PureStep,
           by simp [wp_norm, arm64_norm],
           by simp [wp_norm, arm64_norm, hadd2_ptr],
           by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
           by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
           by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
           by simp [wp_norm, arm64_norm, hx25], by simp [wp_norm, arm64_norm, hx26],
           by simp [wp_norm, arm64_norm, hx27], by simp [wp_norm, arm64_norm],
           by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm]⟩)
    · rintro s1 hpc1 hstat1 hvm1 ⟨hsp1, htr1, hacp1, hx0_1, hx8_1, hx19_1, hx20_1, hx21_1,
        hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hx30_1⟩
      by_cases hjeq : j + 1 = k
      · have hrem1 : rem - 1 = 0 := by omega
        have hdec : decide (j + 1 ≠ k) = false := by simp [hjeq]
        simp only [hdec, Bool.false_eq_true, ↓reduceIte] at hpc1
        have hdone :
            outCoeffs.set j (GF16.add (outCoeffs[j]'hj_o) (workingCoeffs[j + 1]'hj1_w)) =
              lagrangeAccumulateCoeffsTotal j rem outCoeffs workingCoeffs := by
          rw [hstep_pure, hrem1, lagrangeAccumulateCoeffsTotal]
        rw [hdone]
        exact hcont s1 hpc1 hstat1 hsp1 htr1 hvm1 hacp1 hx19_1 hx20_1 hx21_1 hx22_1
          hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hx30_1
      · have hdec : decide (j + 1 ≠ k) = true := by simp [hjeq]
        simp only [hdec, ↓reduceIte] at hpc1
        refine ih (rem - 1) (by omega) (j + 1)
          (outCoeffs.set j (GF16.add (outCoeffs[j]'hj_o) (workingCoeffs[j + 1]'hj1_w)))
          s1 P post (by omega) (by omega) (by simp [hlen_o])
          hpc1 hstat1 hx0_1 hx8_1 hx25_1 hx26_1 hx27_1
          (fun sf hpc_f hstat_f hsp_f htr_f hvm_f hacp_f hx19_f hx20_f hx21_f hx22_f hx23_f
            hx24_f hx25_f hx26_f hx27_f hx28_f hx29_f hx29_f' => ?_)
        rw [← hstep_pure]
        exact hcont sf hpc_f hstat_f
          (hsp_f.trans hsp1) (htr_f.trans htr1) (hvm1.trans hvm_f) (hacp1.trans hacp_f)
          (hx19_f.trans hx19_1) (hx20_f.trans hx20_1) (hx21_f.trans hx21_1)
          (hx22_f.trans hx22_1) (hx23_f.trans hx23_1) (hx24_f.trans hx24_1)
          hx25_f hx26_f hx27_f
          (hx28_f.trans hx28_1) (hx29_f.trans hx29_1) (hx29_f'.trans hx30_1)

/-! ## Outer Loop (`(blkPl_418).base + 940#64` to `(blkPl_418).base + 1136#64`) -/

theorem lagrangeInterpolateOuterStep_placed_sepWP [LibsignalPlacement]
    {ext : String → Option (State → State)} {ret_pc : BitVec 64}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym
      (withVmPreserved sessionMemcpyRegionSpec))
    (hcomp : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 373) (withVmPreserved lagrangeCompletePlacedSpec))
    (sp0 acc_ptr ptr_l ptr_b pt_ptr : BitVec 64)
    (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (k i : Nat) (b_init : Poly) (pts_slice : List Pt)
    (outCoeffs workingCoeffs : List GF16)
    (hk_pos : 1 ≤ k) (hk_le : k ≤ 65536) (hi_lt : i < k)
    (hb_len : b_init.coefficients.length = k + 1)
    (hpts_len : pts_slice.length = k)
    (hout_len : outCoeffs.length = k)
    (hwork_len : workingCoeffs.length = k + 1)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (blkPl_418).base + 940#64)
    (hstat : s.status = .Running)
    (hsp : s.sp = sp0 - 672#64)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 i)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 k)
    (hx23 : s.readReg64 .x23 = pt_ptr)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (2 * (k + 1)))
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 (k + 1))
    (hx26 : s.readReg64 .x26 = ptr_l)
    (hx27 : s.readReg64 .x27 = 0#64 - BitVec.ofNat 64 k)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hcont : ∀ sf : State,
      sf.pc = (blkPl_418).base + 1036#64 →
      sf.status = .Running →
      sf.sp = sp0 - 672#64 →
      traceVRegs sf = traceVRegs s →
      VmPreserved s sf →
      sf.readReg64 .x19 = BitVec.ofNat 64 (i + 1) →
      sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = BitVec.ofNat 64 k →
      sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = pt_ptr →
      sf.readReg64 .x24 = BitVec.ofNat 64 (2 * (k + 1)) →
      sf.readReg64 .x25 = BitVec.ofNat 64 (k + 1) →
      sf.readReg64 .x26 = ptr_l →
      sf.readReg64 .x27 = 0#64 - BitVec.ofNat 64 k →
      sf.readReg64 .x28 = BitVec.ofNat 64 i →
      sf.readReg64 .x29 = sp0 - 96#64 →
      SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc sf
        (gf16SliceAt acc_ptr
          (lagrangeAccumulateCoeffsTotal 0 k outCoeffs
            (lagrangeCompletePure b_init pts_slice i).coefficients) ∗
          gf16SliceAt ptr_l (lagrangeCompletePure b_init pts_slice i).coefficients ∗
          gf16SliceAt ptr_b b_init.coefficients ∗
          ptSliceAt pt_ptr pts_slice ∗
          ((sp0 - 656#64) ↦₆₄ acc_ptr) ∗
          ((sp0 - 640#64) ↦₆₄ ptr_b) ∗
          tokenInitPlacedAt ∗
          reduceTablePlacedAt ∗
          stackAt (sp0 - 672#64) lagrangeCompleteStack ∗ P)
        post) :
    SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc s
      (gf16SliceAt acc_ptr outCoeffs ∗
        gf16SliceAt ptr_l workingCoeffs ∗
        gf16SliceAt ptr_b b_init.coefficients ∗
        ptSliceAt pt_ptr pts_slice ∗
        ((sp0 - 656#64) ↦₆₄ acc_ptr) ∗
        ((sp0 - 640#64) ↦₆₄ ptr_b) ∗
        tokenInitPlacedAt ∗
        reduceTablePlacedAt ∗
        stackAt (sp0 - 672#64) lagrangeCompleteStack ∗ P)
      post := by
  have hmemcpy : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsρ spqrMemcpySym) (withVmPreserved sessionMemcpyRegionSpec) :=
    spqr_hook_ok_of_mem hmemcpy_sat
  simp only [withVmPreserved, sessionMemcpyRegionSpec] at hmemcpy
  have hcomp' := hcomp
  simp only [withVmPreserved, lagrangeCompletePlacedSpec] at hcomp'
  have hinner := @lagrangeAccumulateInner_placed_sepWP _ ext ret_pc acc_ptr ptr_l k
    (lagrangeCompletePure b_init pts_slice i).coefficients hk_pos hk_le
    (by rw [lagrangeCompletePure_length, hb_len]) k 0 outCoeffs
  try dsimp only [BitVec.ofNat_eq_ofNat] at hmemcpy hcomp' hinner hpc hcont ⊢
  have htoNat_b : (BitVec.ofNat 64 (2 * (k + 1))).toNat = (gf16ListBytes b_init.coefficients).length :=
    toNat_two_mul_succ_eq_gf16ListBytes k b_init.coefficients hk_le hb_len
  refine SepWP.weaken_pre
    (show _ ⊢
      gf16SliceAt ptr_l workingCoeffs ∗ gf16SliceAt ptr_b b_init.coefficients ∗
        (gf16SliceAt acc_ptr outCoeffs ∗ ptSliceAt pt_ptr pts_slice ∗
          ((sp0 - 656#64) ↦₆₄ acc_ptr) ∗ ((sp0 - 640#64) ↦₆₄ ptr_b) ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          stackAt (sp0 - 672#64) lagrangeCompleteStack ∗ P) by
      exact Entails.of_eq (by sep_ac_rfl)) ?_
  refine SepWP.weaken_pre (memcpy_gf16Slice_pre ptr_l ptr_b workingCoeffs b_init.coefficients
    (by omega) _) ?_
  wp_steps 6
  refine with_vm_cur (s := s) fun hvm0 => ?_
  wp_call hmemcpy ⟨ptr_l, ptr_b, gf16ListBytes b_init.coefficients⟩
  wp_conv_pre =>
    rw [← gf16SliceAt_eq_pointsToBytes b_init.coefficients ptr_l,
        ← gf16SliceAt_eq_pointsToBytes b_init.coefficients ptr_b]
  have hvm1 : VmPreserved s sf := hvm0.trans (by assumption)
  have h1_len : BitVec.ofNat 64 (k + 1) = BitVec.ofNat 64 b_init.coefficients.length := by
    rw [hb_len]
  have h3_len : BitVec.ofNat 64 k = BitVec.ofNat 64 pts_slice.length := by
    rw [hpts_len]
  have hi_pts : i < pts_slice.length := by omega
  have h2_lt : 2 * b_init.coefficients.length < 2 ^ 64 := by omega
  have h4_lt : 4 * pts_slice.length < 2 ^ 64 := by omega
  have hsp_al_s : s.spAligned = true := by
    unfold State.spAligned
    rw [hsp, sp672_aligned sp0 hsp0]
    rfl
  wp_steps 6
  refine with_vm_cur (s := sf) fun hvm2_step => ?_
  have hvm2 : VmPreserved s _ := hvm1.trans hvm2_step
  wp_call hcomp' ⟨ptr_l, pt_ptr, b_init, pts_slice, i⟩
  wp_conv_pre => rw [hsp_sf, hsp]
  have hvm3 : VmPreserved s sf_1 := hvm2.trans (by assumption)
  wp_steps 2
  refine with_vm_cur (s := sf_1) fun hvm4_step => ?_
  have hvm4 : VmPreserved s _ := hvm3.trans hvm4_step
  refine SepWP.weaken_pre ?_
    (hinner _
      (gf16SliceAt ptr_b b_init.coefficients ∗
        ptSliceAt pt_ptr pts_slice ∗
        ((sp0 - 656#64) ↦₆₄ acc_ptr) ∗
        ((sp0 - 640#64) ↦₆₄ ptr_b) ∗
        tokenInitPlacedAt ∗
        reduceTablePlacedAt ∗
        stackAt (sp0 - 672#64) lagrangeCompleteStack ∗ P)
      post (by omega) (by omega) hout_len
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hrun_sf_1])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, *])
      (by simp [wp_norm, arm64_norm, *])
      (by simp [wp_norm, arm64_norm, *])
      (fun sf3 hpc3 hstat3 hsp3 htr3 hvm_in _ hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3
        hx25_3 hx26_3 hx27_3 hx28_3 hx29_3 _ => ?_))
  · exact Entails.of_eq (by sep_ac_rfl)
  refine SepWP.weaken_pre ?_
    (hcont sf3 hpc3 hstat3
      (by rw [hsp3]; simp [wp_norm, arm64_norm, *])
      (by rw [htr3]; simp [traceVRegs, wp_norm, arm64_norm, *])
      (hvm4.trans hvm_in)
      (by rw [hx19_3]; simp [wp_norm, arm64_norm, *])
      (by rw [hx20_3]; simp [wp_norm, arm64_norm, *])
      (by rw [hx21_3]; simp [wp_norm, arm64_norm, *])
      (by rw [hx22_3]; simp [wp_norm, arm64_norm, *])
      (by rw [hx23_3]; simp [wp_norm, arm64_norm, *])
      (by rw [hx24_3]; simp [wp_norm, arm64_norm, *])
      hx25_3 hx26_3 hx27_3
      (by rw [hx28_3]; simp [wp_norm, arm64_norm, *])
      (by rw [hx29_3]; simp [wp_norm, arm64_norm, *]))
  · exact Entails.of_eq (by sep_ac_rfl)

theorem lagrangeInterpolateOuter_placed_sepWP [LibsignalPlacement]
    {ext : String → Option (State → State)} {ret_pc : BitVec 64}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym
      (withVmPreserved sessionMemcpyRegionSpec))
    (hcomp : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 373) (withVmPreserved lagrangeCompletePlacedSpec))
    (sp0 acc_ptr ptr_l ptr_b pt_ptr : BitVec 64)
    (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (k : Nat) (b_init : Poly) (pts_slice : List Pt)
    (hk_pos : 1 ≤ k) (hk_le : k ≤ 65536)
    (hb_len : b_init.coefficients.length = k + 1)
    (hpts_len : pts_slice.length = k) :
    ∀ (rem i : Nat) (outCoeffs workingCoeffs : List GF16)
      (s : State) (P : SepProp) (post : State → SepProp → Prop),
      rem > 0 →
      i + rem = k →
      outCoeffs.length = k →
      workingCoeffs.length = k + 1 →
      s.pc = (blkPl_418).base + 940#64 →
      s.status = .Running →
      s.sp = sp0 - 672#64 →
      s.readReg64 .x19 = BitVec.ofNat 64 i →
      s.readReg64 .x21 = BitVec.ofNat 64 k →
      s.readReg64 .x23 = pt_ptr →
      s.readReg64 .x24 = BitVec.ofNat 64 (2 * (k + 1)) →
      s.readReg64 .x25 = BitVec.ofNat 64 (k + 1) →
      s.readReg64 .x26 = ptr_l →
      s.readReg64 .x27 = 0#64 - BitVec.ofNat 64 k →
      s.readReg64 .x29 = sp0 - 96#64 →
      (∀ sf : State,
        sf.pc = (blkPl_418).base + 1136#64 →
        sf.status = .Running →
        sf.sp = sp0 - 672#64 →
        traceVRegs sf = traceVRegs s →
        VmPreserved s sf →
        sf.readReg64 .x20 = s.readReg64 .x20 →
        sf.readReg64 .x21 = BitVec.ofNat 64 k →
        sf.readReg64 .x22 = s.readReg64 .x22 →
        sf.readReg64 .x23 = pt_ptr →
        sf.readReg64 .x24 = BitVec.ofNat 64 (2 * (k + 1)) →
        sf.readReg64 .x25 = BitVec.ofNat 64 (k + 1) →
        sf.readReg64 .x26 = ptr_l →
        sf.readReg64 .x29 = sp0 - 96#64 →
        SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc sf
          (gf16SliceAt acc_ptr
            (lagrangeInterpolateLoopTotal b_init pts_slice i rem outCoeffs) ∗
            memRegion ptr_l (2 * (k + 1)) ∗
            gf16SliceAt ptr_b b_init.coefficients ∗
            ptSliceAt pt_ptr pts_slice ∗
            ((sp0 - 656#64) ↦₆₄ acc_ptr) ∗
            ((sp0 - 640#64) ↦₆₄ ptr_b) ∗
            tokenInitPlacedAt ∗
            reduceTablePlacedAt ∗
            stackAt (sp0 - 672#64) lagrangeCompleteStack ∗ P)
          post) →
      SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc s
        (gf16SliceAt acc_ptr outCoeffs ∗
          gf16SliceAt ptr_l workingCoeffs ∗
          gf16SliceAt ptr_b b_init.coefficients ∗
          ptSliceAt pt_ptr pts_slice ∗
          ((sp0 - 656#64) ↦₆₄ acc_ptr) ∗
          ((sp0 - 640#64) ↦₆₄ ptr_b) ∗
          tokenInitPlacedAt ∗
          reduceTablePlacedAt ∗
          stackAt (sp0 - 672#64) lagrangeCompleteStack ∗ P)
        post := by
  intro rem
  induction rem using Nat.strongRecOn with
  | ind rem ih =>
    intro i outCoeffs workingCoeffs s P post hrem hsum hout_len hwork_len
      hpc hstat hsp hx19 hx21 hx23 hx24 hx25 hx26 hx27 hx29 hcont
    have hi_lt : i < k := by omega
    refine lagrangeInterpolateOuterStep_placed_sepWP hmemcpy_sat hcomp sp0 acc_ptr ptr_l ptr_b pt_ptr hsp0
      k i b_init pts_slice outCoeffs workingCoeffs hk_pos hk_le hi_lt hb_len hpts_len hout_len hwork_len
      s P post hpc hstat hsp hx19 hx21 hx23 hx24 hx25 hx26 hx27 hx29
      (fun s1 hpc1 hstat1 hsp1 htr1 hvm1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 => ?_)
    have hbne := bv64_succ_bne_of_le i k hi_lt hk_le
    have hrem_eq : rem = (rem - 1) + 1 := by omega
    have hstep_pure :
        lagrangeInterpolateLoopTotal b_init pts_slice i rem outCoeffs =
          lagrangeInterpolateLoopTotal b_init pts_slice (i + 1) (rem - 1)
            (lagrangeAccumulateCoeffsTotal 0 k outCoeffs
              (lagrangeCompletePure b_init pts_slice i).coefficients) := by
      conv => lhs; rw [hrem_eq]
      simp [lagrangeInterpolateLoopTotal, hout_len]
    try dsimp only [BitVec.ofNat_eq_ofNat] at hpc1 hcont ⊢
    wp_steps 2
    by_cases hieq : i + 1 = k
    · have hrem1 : rem - 1 = 0 := by omega
      have hdec : decide (i + 1 ≠ k) = false := by simp [hieq]
      simp only [hdec, Bool.false_eq_true, ↓reduceIte]
      wp_steps 1
      have hdone :
          lagrangeAccumulateCoeffsTotal 0 k outCoeffs
            (lagrangeCompletePure b_init pts_slice i).coefficients =
            lagrangeInterpolateLoopTotal b_init pts_slice i rem outCoeffs := by
        rw [hstep_pure, hrem1, lagrangeInterpolateLoopTotal]
      have hlen_w' : (lagrangeCompletePure b_init pts_slice i).coefficients.length = k + 1 := by
        rw [lagrangeCompletePure_length, hb_len]
      have hto_mem :
          gf16SliceAt ptr_l (lagrangeCompletePure b_init pts_slice i).coefficients ⊢
            memRegion ptr_l (2 * (k + 1)) := by
        rw [← hlen_w']
        exact gf16SliceAt_to_memRegion ptr_l _
      rw [hdone]
      refine SepWP.weaken_pre
        (sepConj_mono_right (sepConj_mono_left hto_mem)) ?_
      apply hcont
      · simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm, hstat1]
      · simp [wp_norm, arm64_norm, hsp1]
      · simpa [wp_norm, arm64_norm] using htr1
      · exact hvm1.trans (by simp [wp_norm, arm64_norm])
      · simpa [wp_norm, arm64_norm] using hx20_1
      · simp [wp_norm, arm64_norm, hx21_1]
      · simpa [wp_norm, arm64_norm] using hx22_1
      · simp [wp_norm, arm64_norm, hx23_1]
      · simp [wp_norm, arm64_norm, hx24_1]
      · simp [wp_norm, arm64_norm, hx25_1]
      · simp [wp_norm, arm64_norm, hx26_1]
      · simp [wp_norm, arm64_norm, hx29_1]
    · have hdec : decide (i + 1 ≠ k) = true := by simp [hieq]
      simp only [hdec, ↓reduceIte]
      refine with_vm_cur (s := s1) fun hvm1_step => ?_
      have hvm1' : VmPreserved s _ := hvm1.trans hvm1_step
      refine ih (rem - 1) (by omega) (i + 1)
        (lagrangeAccumulateCoeffsTotal 0 k outCoeffs
          (lagrangeCompletePure b_init pts_slice i).coefficients)
        (lagrangeCompletePure b_init pts_slice i).coefficients
        _ P post (by omega) (by omega)
        (by rw [lagrangeAccumulateCoeffsTotal_length, hout_len])
        (by rw [lagrangeCompletePure_length, hb_len])
        (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hstat1])
        (by simp [wp_norm, arm64_norm, hsp1])
        (by simp [wp_norm, arm64_norm, hx19_1])
        (by simp [wp_norm, arm64_norm, hx21_1])
        (by simp [wp_norm, arm64_norm, hx23_1])
        (by simp [wp_norm, arm64_norm, hx24_1])
        (by simp [wp_norm, arm64_norm, hx25_1])
        (by simp [wp_norm, arm64_norm, hx26_1])
        (by simp [wp_norm, arm64_norm, hx27_1])
        (by simp [wp_norm, arm64_norm, hx29_1])
        (fun sf hpc_f hstat_f hsp_f htr_f hvm_f hx20_f hx21_f hx22_f hx23_f hx24_f hx25_f hx26_f hx29_f => ?_)
      rw [← hstep_pure]
      apply hcont sf hpc_f hstat_f hsp_f
      · rw [htr_f]; simpa [wp_norm, arm64_norm] using htr1
      · exact hvm1'.trans hvm_f
      · rw [hx20_f]; simpa [wp_norm, arm64_norm] using hx20_1
      · exact hx21_f
      · rw [hx22_f]; simpa [wp_norm, arm64_norm] using hx22_1
      · exact hx23_f
      · exact hx24_f
      · exact hx25_f
      · exact hx26_f
      · exact hx29_f

/-! ## Cleanup & Cache Store (`(blkPl_418).base + 1136#64` to `(blkPl_418).base + 1284#64`) -/

theorem lagrangeInterpolateDealloc_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {ret_pc : BitVec 64}
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (sp0 acc_ptr ptr_l ptr_b b_cap : BitVec 64)
    (v192 v184 v176 : BitVec 64)
    (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (k : Nat) (b_init : Poly)
    (hk_le : k ≤ 65536)
    (_hb_len : b_init.coefficients.length = k + 1)
    (hb_cap_ge : b_init.coefficients.length ≤ b_cap.toNat)
    (hb_cap_lt : b_cap.toNat * 2 < 2 ^ 63)
    (st : M.σ)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (blkPl_418).base + 1136#64)
    (hstat : s.status = .Running)
    (hsp : s.sp = sp0 - 672#64)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (2 * (k + 1)))
    (hx26 : s.readReg64 .x26 = ptr_l)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hcont : ∀ (sf : State) (evs : List AllocEvent),
      FreeOnlyEvs evs →
      sf.pc = (blkPl_418).base + 1196#64 →
      sf.status = .Running →
      sf.sp = sp0 - 672#64 →
      traceVRegs sf = traceVRegs s →
      AllocCallPreserved s sf →
      sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x29 = sp0 - 96#64 →
      SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc sf
        (((sp0 - 640#64) ↦₆₄ ptr_b) ∗
          ((sp0 - 192#64) ↦₆₄ BitVec.ofNat 64 k) ∗
          ((sp0 - 184#64) ↦₆₄ acc_ptr) ∗
          ((sp0 - 176#64) ↦₆₄ BitVec.ofNat 64 k) ∗
          ((sp0 - 168#64) ↦₆₄ BitVec.ofNat 64 k) ∗
          ((sp0 - 160#64) ↦₆₄ acc_ptr) ∗
          ((sp0 - 152#64) ↦₆₄ BitVec.ofNat 64 k) ∗
          ((sp0 - 144#64) ↦₆₄ b_cap) ∗
          A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (sp0 - 672#64) allocHookStack ∗ P) post) :
    SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc s
      (A.live ptr_l (2 * (k + 1)) 2 ∗
        memRegion ptr_l (2 * (k + 1)) ∗
        A.live ptr_b (b_cap.toNat * 2) 2 ∗
        gf16SliceAt ptr_b b_init.coefficients ∗
        memRegion (ptr_b + BitVec.ofNat 64 (b_init.coefficients.length * 2))
          ((b_cap.toNat - b_init.coefficients.length) * 2) ∗
        ((sp0 - 640#64) ↦₆₄ ptr_b) ∗
        ((sp0 - 192#64) ↦₆₄ v192) ∗
        ((sp0 - 184#64) ↦₆₄ v184) ∗
        ((sp0 - 176#64) ↦₆₄ v176) ∗
        ((sp0 - 168#64) ↦₆₄ BitVec.ofNat 64 k) ∗
        ((sp0 - 160#64) ↦₆₄ acc_ptr) ∗
        ((sp0 - 152#64) ↦₆₄ BitVec.ofNat 64 k) ∗
        ((sp0 - 144#64) ↦₆₄ b_cap) ∗
        A.pool lim st s ∗ stackAt (sp0 - 672#64) allocHookStack ∗ P) post := by
  have hdealloc1 : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (deallocFreeOnlySpec M A lim) :=
    subroutine_ok_deallocFreeOnly (spqr_hook_ok_of_mem hdealloc_sat)
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc1
  try dsimp only [BitVec.ofNat_eq_ofNat] at hdealloc1 hpc hcont ⊢
  have hsp_al_s : s.spAligned = true := by
    unfold State.spAligned
    rw [hsp, sp672_aligned sp0 hsp0]
    rfl
  have hsp_align : s.sp &&& 15#64 = 0#64 := by
    rw [hsp]; exact sp672_aligned sp0 hsp0
  have htoNat_l : (BitVec.ofNat 64 (2 * (k + 1))).toNat = 2 * (k + 1) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hb_cap_ne0 : (b_cap == 0#64) = false := by
    rw [beq_eq_false_iff_ne]
    intro h
    have h1 := congrArg BitVec.toNat h
    change b_cap.toNat = 0 at h1
    omega
  have hb_cap_shl : (b_cap <<< 1).toNat = b_cap.toNat * 2 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one, Nat.mod_eq_of_lt (by omega)]
  refine seq_vm_clean (mid := lsρ spqrRustDeallocSym)
    (P_mid :=
      A.live ptr_l (2 * (k + 1)) 2 ∗
        memRegion ptr_l (2 * (k + 1)) ∗
        A.pool lim st s ∗
        stackAt (sp0 - 672#64) allocHookStack ∗
        A.live ptr_b (b_cap.toNat * 2) 2 ∗
        gf16SliceAt ptr_b b_init.coefficients ∗
        memRegion (ptr_b + BitVec.ofNat 64 (b_init.coefficients.length * 2))
          ((b_cap.toNat - b_init.coefficients.length) * 2) ∗
        ((sp0 - 640#64) ↦₆₄ ptr_b) ∗
        ((sp0 - 192#64) ↦₆₄ BitVec.ofNat 64 k) ∗
        ((sp0 - 184#64) ↦₆₄ acc_ptr) ∗
        ((sp0 - 176#64) ↦₆₄ BitVec.ofNat 64 k) ∗
        ((sp0 - 168#64) ↦₆₄ BitVec.ofNat 64 k) ∗
        ((sp0 - 160#64) ↦₆₄ acc_ptr) ∗
        ((sp0 - 152#64) ↦₆₄ BitVec.ofNat 64 k) ∗
        ((sp0 - 144#64) ↦₆₄ b_cap) ∗ P)
    (Q := fun s1 =>
      s1.sp = sp0 - 672#64 ∧
      s1.readReg64 .x0 = ptr_l ∧
      s1.readReg64 .x1 = BitVec.ofNat 64 (2 * (k + 1)) ∧
      s1.readReg64 .x2 = 2#64 ∧
      s1.readReg64 .x20 = s.readReg64 .x20 ∧
      s1.readReg64 .x22 = s.readReg64 .x22 ∧
      s1.readReg64 .x29 = sp0 - 96#64 ∧
      s1.readReg64 .x30 = (blkPl_418).base + 1172#64 ∧
      traceVRegs s1 = traceVRegs s ∧
      AllocCallPreserved s s1)
    ?_ ?_
  · by_vm_steps (
      wp_steps 9
      refine SepWP.weaken_pre
        (show _ ⊢
          A.live ptr_l (2 * (k + 1)) 2 ∗
            memRegion ptr_l (2 * (k + 1)) ∗
            A.pool lim st s ∗
            stackAt (sp0 - 672#64) allocHookStack ∗
            A.live ptr_b (b_cap.toNat * 2) 2 ∗
            gf16SliceAt ptr_b b_init.coefficients ∗
            memRegion (ptr_b + BitVec.ofNat 64 (b_init.coefficients.length * 2))
              ((b_cap.toNat - b_init.coefficients.length) * 2) ∗
            ((sp0 - 640#64) ↦₆₄ ptr_b) ∗
            ((sp0 - 192#64) ↦₆₄ BitVec.ofNat 64 k) ∗
            ((sp0 - 184#64) ↦₆₄ acc_ptr) ∗
            ((sp0 - 176#64) ↦₆₄ BitVec.ofNat 64 k) ∗
            ((sp0 - 168#64) ↦₆₄ BitVec.ofNat 64 k) ∗
            ((sp0 - 160#64) ↦₆₄ acc_ptr) ∗
            ((sp0 - 152#64) ↦₆₄ BitVec.ofNat 64 k) ∗
            ((sp0 - 144#64) ↦₆₄ b_cap) ∗ P by
          try simp only [arm64_norm]
          exact Entails.of_eq (by sep_ac_rfl)) ?_
      exact SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hstat])
        ⟨by simp [wp_norm, arm64_norm], Entails.refl _,
         by simpa [wp_norm, arm64_norm] using hsp,
         by simp [wp_norm, arm64_norm, hx26],
         by simp [wp_norm, arm64_norm, hx24],
         by simp [wp_norm, arm64_norm],
         by simp [wp_norm, arm64_norm],
         by simp [wp_norm, arm64_norm],
         by simp [wp_norm, arm64_norm, hx29],
         by simp [wp_norm, arm64_norm],
         by simp [wp_norm, arm64_norm],
         acp_of_PureStep⟩)
  · rintro s1 hpc1 hstat1 hvm1 ⟨hsp1, hx0_1, hx1_1, hx2_1, hx20_1, hx22_1, hx29_1, hx30_1, htr1, hacp1⟩
    simp only [traceVRegs, Prod.mk.injEq] at htr1
    have hsp1_al : s1.spAligned = true := by
      unfold State.spAligned
      rw [hsp1, sp672_aligned sp0 hsp0]
      rfl
    refine SepWP.transport_budgetPool hvm1 (hnext := ?_)
    wp_conv_pre => rw [← hsp1]
    wp_call hdealloc1 ⟨ptr_l, 2 * (k + 1), 2, st⟩
    wp_conv_pre => rw [hsp1]
    have hacp2 : AllocCallPreserved s sf := hacp1.trans (by assumption)
    let st1 := M.stepEvents (rustDeallocEvents (2 * (k + 1)) 2) st
    refine SepWP.weaken_pre
      (show _ ⊢
        gf16SliceAt ptr_b b_init.coefficients ∗
          memRegion (ptr_b + BitVec.ofNat 64 (b_init.coefficients.length * 2))
            ((b_cap.toNat - b_init.coefficients.length) * 2) ∗
          (A.live ptr_b (b_cap.toNat * 2) 2 ∗ A.pool lim st1 sf ∗
            stackAt (sp0 - 672#64) allocHookStack ∗
            ((sp0 - 640#64) ↦₆₄ ptr_b) ∗
            ((sp0 - 192#64) ↦₆₄ BitVec.ofNat 64 k) ∗
            ((sp0 - 184#64) ↦₆₄ acc_ptr) ∗
            ((sp0 - 176#64) ↦₆₄ BitVec.ofNat 64 k) ∗
            ((sp0 - 168#64) ↦₆₄ BitVec.ofNat 64 k) ∗
            ((sp0 - 160#64) ↦₆₄ acc_ptr) ∗
            ((sp0 - 152#64) ↦₆₄ BitVec.ofNat 64 k) ∗
            ((sp0 - 144#64) ↦₆₄ b_cap) ∗ P) by
        exact Entails.of_eq (by sep_ac_rfl)) ?_
    refine SepWP.weaken_pre
      (gf16Slice_spare_to_memRegion ptr_b b_init.coefficients b_cap.toNat hb_cap_ge hb_cap_lt _) ?_
    wp_steps 6
    refine SepWP.transport_budgetPool (by simp [wp_norm, arm64_norm] : VmPreserved sf _)
      (hnext := ?_)
    have hacp3 : AllocCallPreserved s _ := hacp2.trans acp_of_PureStep
    wp_call hdealloc1 ⟨ptr_b, b_cap.toNat * 2, 2, st1⟩
    wp_conv_pre => rw [hsp_sf, hsp1]
    have hacp4 : AllocCallPreserved s sf_1 := hacp3.trans (by assumption)
    dsimp only [st1]
    rw [← AllocCostModel.stepEvents_append]
    refine SepWP.weaken_pre ?_
      (hcont sf_1 (rustDeallocEvents (2 * (k + 1)) 2 ++ rustDeallocEvents (b_cap.toNat * 2) 2)
        ((FreeOnlyEvs.singleton 2 (2 * (k + 1))).append (FreeOnlyEvs.singleton 2 (b_cap.toNat * 2)))
        (by exact hpc_sf_1)
        (by exact hrun_sf_1)
        (by rw [hsp_sf_1, hsp_sf, hsp1])
        (by simp [traceVRegs, wp_norm, arm64_norm, *])
        hacp4
        (by simp [wp_norm, arm64_norm, *])
        (by simp [wp_norm, arm64_norm, *])
        (by simp [wp_norm, arm64_norm, *]))
    exact Entails.of_eq (by sep_ac_rfl)

theorem lagrangeInterpolateStoreSlot_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M}
    {ext : String → Option (State → State)} {ret_pc : BitVec 64}
    (sp0 acc_ptr x19_slot x24_saved v144 v136 v128 : BitVec 64)
    (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (k : Nat) (outCoeffs : List GF16)
    (hk_pos : 1 ≤ k) (hk_le : k ≤ 65536)
    (hout_len : outCoeffs.length = k)
    (hacc_ne : acc_ptr ≠ 0#64)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (blkPl_418).base + 1196#64)
    (hstat : s.status = .Running)
    (hsp : s.sp = sp0 - 672#64)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hcont : ∀ sf : State,
      sf.pc = (blkPl_418).base + 1284#64 →
      sf.status = .Running →
      sf.sp = sp0 - 672#64 →
      traceVRegs sf = traceVRegs s →
      VmPreserved s sf →
      AllocCallPreserved s sf →
      sf.readReg64 .x19 = x19_slot →
      sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x24 = x24_saved →
      sf.readReg64 .x25 = 24#64 →
      sf.readReg64 .x26 = sp0 - 600#64 →
      sf.readReg64 .x29 = sp0 - 96#64 →
      SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc sf
        (optPolyCacheSlotAt A.repAlloc x19_slot (some ⟨outCoeffs⟩) ∗
          ((sp0 - 664#64) ↦₆₄ x19_slot) ∗
          ((sp0 - 648#64) ↦₆₄ x24_saved) ∗
          ((sp0 - 192#64) ↦₆₄ BitVec.ofNat 64 k) ∗
          ((sp0 - 184#64) ↦₆₄ acc_ptr) ∗
          ((sp0 - 176#64) ↦₆₄ BitVec.ofNat 64 k) ∗
          ((sp0 - 144#64) ↦₆₄ BitVec.ofNat 64 k) ∗
          ((sp0 - 136#64) ↦₆₄ acc_ptr) ∗
          ((sp0 - 128#64) ↦₆₄ BitVec.ofNat 64 k) ∗ P) post) :
    SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc s
      (optPolyCacheSlotAt A.repAlloc x19_slot none ∗
        A.live acc_ptr (2 * k) 2 ∗
        gf16SliceAt acc_ptr outCoeffs ∗
        ((sp0 - 664#64) ↦₆₄ x19_slot) ∗
        ((sp0 - 648#64) ↦₆₄ x24_saved) ∗
        ((sp0 - 192#64) ↦₆₄ BitVec.ofNat 64 k) ∗
        ((sp0 - 184#64) ↦₆₄ acc_ptr) ∗
        ((sp0 - 176#64) ↦₆₄ BitVec.ofNat 64 k) ∗
        ((sp0 - 144#64) ↦₆₄ v144) ∗
        ((sp0 - 136#64) ↦₆₄ v136) ∗
        ((sp0 - 128#64) ↦₆₄ v128) ∗ P) post := by
  try dsimp only [BitVec.ofNat_eq_ofNat] at hpc hcont ⊢
  have hsp_al_s : s.spAligned = true := by
    unfold State.spAligned
    rw [hsp, sp672_aligned sp0 hsp0]
    rfl
  have hk1_ne0 : BitVec.ofNat 64 (k + 1) ≠ 0#64 := by
    intro h
    have h1 := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
    omega
  have hk1_beq0 : (BitVec.ofNat 64 (k + 1) == 0#64) = false := beq_eq_false_iff_ne.mpr hk1_ne0
  have hk_add1_ne0 : (BitVec.ofNat 64 k + 1#64 == 0#64) = false :=
    bv64_add_one_beq_zero_false hk_le
  change SepWP _ _ _
    (((x19_slot ↦₆₄ noneCap) ∗ memRegion (x19_slot + 8#64) 16) ∗ _) _
  rw [memRegion_16_eq_exists_pair (x19_slot + 8#64),
    BitVec.add_assoc, show (8#64 : BitVec 64) + 8#64 = 16#64 from rfl,
    sepConj_assoc, sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_left; intro w_slot1
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_left; intro w_slot2
  wp_conv_pre => rw [sepConj_assoc]
  refine seq_vm_clean (mid := (blkPl_418).base + 1284#64)
    (P_mid :=
      optPolyCacheSlotAt A.repAlloc x19_slot (some ⟨outCoeffs⟩) ∗
        ((sp0 - 664#64) ↦₆₄ x19_slot) ∗
        ((sp0 - 648#64) ↦₆₄ x24_saved) ∗
        ((sp0 - 192#64) ↦₆₄ BitVec.ofNat 64 k) ∗
        ((sp0 - 184#64) ↦₆₄ acc_ptr) ∗
        ((sp0 - 176#64) ↦₆₄ BitVec.ofNat 64 k) ∗
        ((sp0 - 144#64) ↦₆₄ BitVec.ofNat 64 k) ∗
        ((sp0 - 136#64) ↦₆₄ acc_ptr) ∗
        ((sp0 - 128#64) ↦₆₄ BitVec.ofNat 64 k) ∗ P)
    (Q := fun sf =>
      sf.sp = sp0 - 672#64 ∧
      traceVRegs sf = traceVRegs s ∧
      AllocCallPreserved s sf ∧
      sf.readReg64 .x19 = x19_slot ∧
      sf.readReg64 .x20 = s.readReg64 .x20 ∧
      sf.readReg64 .x22 = s.readReg64 .x22 ∧
      sf.readReg64 .x24 = x24_saved ∧
      sf.readReg64 .x25 = 24#64 ∧
      sf.readReg64 .x26 = sp0 - 600#64 ∧
      sf.readReg64 .x29 = sp0 - 96#64)
    ?_ ?_
  · by_vm_steps (
      wp_steps 18
      refine SepWP.weaken_pre
        (show _ ⊢
          (x19_slot ↦₆₄ BitVec.ofNat 64 k) ∗
            ((x19_slot + 8#64) ↦₆₄ acc_ptr) ∗
            ((x19_slot + 16#64) ↦₆₄ BitVec.ofNat 64 k) ∗
            A.repAlloc.live acc_ptr (2 * k) 2 ∗
            gf16SliceAt acc_ptr outCoeffs ∗
            (((sp0 - 664#64) ↦₆₄ x19_slot) ∗
              ((sp0 - 648#64) ↦₆₄ x24_saved) ∗
              ((sp0 - 192#64) ↦₆₄ BitVec.ofNat 64 k) ∗
              ((sp0 - 184#64) ↦₆₄ acc_ptr) ∗
              ((sp0 - 176#64) ↦₆₄ BitVec.ofNat 64 k) ∗
              ((sp0 - 144#64) ↦₆₄ BitVec.ofNat 64 k) ∗
              ((sp0 - 136#64) ↦₆₄ acc_ptr) ∗
              ((sp0 - 128#64) ↦₆₄ BitVec.ofNat 64 k) ∗ P) by
          dsimp only [RustCliAllocBudget.repAlloc_live]
          exact Entails.of_eq (by sep_ac_rfl)) ?_
      refine SepWP.weaken_pre
        (fold_optPolyCacheSlotAt_some A.repAlloc x19_slot acc_ptr outCoeffs k hk_pos hk_le hout_len hacc_ne _) ?_
      exact SepWP.done (by simp [wp_norm, arm64_norm, hk1_ne0, hk1_beq0])
        (by simp [wp_norm, arm64_norm, hstat])
        ⟨by simp [wp_norm, arm64_norm], Entails.of_eq (by sep_ac_rfl),
         by simp [wp_norm, arm64_norm, hsp],
         by simp [wp_norm, arm64_norm],
         acp_of_PureStep,
         by simp [wp_norm, arm64_norm],
         by simp [wp_norm, arm64_norm],
         by simp [wp_norm, arm64_norm],
         by simp [wp_norm, arm64_norm],
         by simp [wp_norm, arm64_norm],
         by simp [wp_norm, arm64_norm, hsp],
         by simp [wp_norm, arm64_norm, hx29]⟩)
  · rintro sf hpc_f hstat_f hvm_f ⟨hsp_f, htr_f, hacp_f, hx19_f, hx20_f, hx22_f, hx24_f,
      hx25_f, hx26_f, hx29_f⟩
    exact hcont sf hpc_f hstat_f hsp_f htr_f hvm_f hacp_f hx19_f hx20_f hx22_f hx24_f
      hx25_f hx26_f hx29_f

theorem lagrangeInterpolate_hit_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M}
    {ext : String → Option (State → State)} {ret_pc : BitVec 64}
    (sp0 : BitVec 64) (polyIdx : Nat) (p : Poly)
    (hidx : polyIdx < 16)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (blkPl_418).base + 660#64)
    (hstat : s.status = .Running)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 polyIdx)
    (hx25 : s.readReg64 .x25 = 24#64)
    (hx26 : s.readReg64 .x26 = sp0 - 600#64)
    (hcont : ∀ sf : State,
      sf.pc = (blkPl_418).base + 1284#64 →
      sf.status = .Running →
      sf.sp = s.sp →
      traceVRegs sf = traceVRegs s →
      VmPreserved s sf →
      AllocCallPreserved s sf →
      sf.readReg64 .x19 = (sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx) →
      sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = 24#64 →
      sf.readReg64 .x26 = sp0 - 600#64 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      sf.readReg64 .x30 = s.readReg64 .x30 →
      SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc sf
        (optPolyCacheSlotAt A.repAlloc ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx)) (some p) ∗ P) post) :
    SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc s
      (optPolyCacheSlotAt A.repAlloc ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx)) (some p) ∗ P) post := by
  have hmod : polyIdx % 4294967296 = polyIdx := Nat.mod_eq_of_lt (by omega)
  unfold optPolyCacheSlotAt
  rw [sepExists_sepConj_left]
  apply SepWP.exists_left; intro ptr
  apply SepWP.focus_pure (by sep_focus)
  rintro ⟨hk_pos, hk_le, hptr⟩
  try dsimp only [BitVec.ofNat_eq_ofNat] at hpc hcont ⊢
  have hk1_ne0 : BitVec.ofNat 64 (p.coefficients.length + 1) ≠ 0#64 := by
    intro h
    have h1 := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
    omega
  have hk1_beq0 : (BitVec.ofNat 64 (p.coefficients.length + 1) == 0#64) = false :=
    beq_eq_false_iff_ne.mpr hk1_ne0
  have hk1_bne0 : (BitVec.ofNat 64 (p.coefficients.length + 1) != 0#64) = true :=
    bne_iff_ne.mpr hk1_ne0
  wp_steps 4
  refine SepWP.weaken_pre
    (fold_optPolyCacheSlotAt_some A.repAlloc ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx))
      ptr p.coefficients p.coefficients.length hk_pos hk_le rfl hptr P) ?_
  exact hcont _
    (by simp [wp_norm, arm64_norm, hk1_ne0, hk1_beq0, hk1_bne0])
    (by simp [wp_norm, arm64_norm, hstat])
    (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm])
    acp_of_PureStep
    (by simp [wp_norm, arm64_norm, hmod])
    (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, hx25])
    (by simp [wp_norm, arm64_norm, hx26])
    (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm])

theorem lagrangeInterpolate_copyAndComplete0_placed_sepWP [LibsignalPlacement]
    {ext : String → Option (State → State)} {ret_pc : BitVec 64}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym
      (withVmPreserved sessionMemcpyRegionSpec))
    (hcomp : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 373) (withVmPreserved lagrangeCompletePlacedSpec))
    (sp0 ptr_l ptr_b pt_ptr x19_slot v664 v640 : BitVec 64)
    (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (hptr_l_ne : ptr_l ≠ 0#64)
    (k : Nat) (b_init : Poly) (pts_slice : List Pt)
    (_hk_pos : 1 ≤ k) (hk_le : k ≤ 65536)
    (hb_len : b_init.coefficients.length = k + 1)
    (hpts_len : pts_slice.length = k)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (blkPl_418).base + 796#64)
    (hstat : s.status = .Running)
    (hsp : s.sp = sp0 - 672#64)
    (hx0 : s.readReg64 .x0 = ptr_l)
    (hx19 : s.readReg64 .x19 = x19_slot)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 k)
    (hx23 : s.readReg64 .x23 = ptr_b)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (2 * (k + 1)))
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 (k + 1))
    (hx27 : s.readReg64 .x27 = pt_ptr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hcont : ∀ sf : State,
      sf.pc = (blkPl_418).base + 848#64 →
      sf.status = .Running →
      sf.sp = sp0 - 672#64 →
      traceVRegs sf = traceVRegs s →
      VmPreserved s sf →
      sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = BitVec.ofNat 64 k →
      sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x24 = BitVec.ofNat 64 (2 * (k + 1)) →
      sf.readReg64 .x25 = BitVec.ofNat 64 (k + 1) →
      sf.readReg64 .x26 = ptr_l →
      sf.readReg64 .x27 = pt_ptr →
      sf.readReg64 .x29 = sp0 - 96#64 →
      SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc sf
        (gf16SliceAt ptr_l (lagrangeCompletePure b_init pts_slice 0).coefficients ∗
          gf16SliceAt ptr_b b_init.coefficients ∗
          ptSliceAt pt_ptr pts_slice ∗
          ((sp0 - 664#64) ↦₆₄ x19_slot) ∗
          ((sp0 - 640#64) ↦₆₄ ptr_b) ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          stackAt (sp0 - 672#64) lagrangeCompleteStack ∗ P) post) :
    SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc s
      (memRegion ptr_l (2 * (k + 1)) ∗
        gf16SliceAt ptr_b b_init.coefficients ∗
        ptSliceAt pt_ptr pts_slice ∗
        ((sp0 - 664#64) ↦₆₄ v664) ∗
        ((sp0 - 640#64) ↦₆₄ v640) ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        stackAt (sp0 - 672#64) lagrangeCompleteStack ∗ P) post := by
  have hmemcpy : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsρ spqrMemcpySym) (withVmPreserved sessionMemcpyRegionSpec) :=
    spqr_hook_ok_of_mem hmemcpy_sat
  simp only [withVmPreserved, sessionMemcpyRegionSpec] at hmemcpy
  have hcomp' := hcomp
  simp only [withVmPreserved, lagrangeCompletePlacedSpec] at hcomp'
  try dsimp only [BitVec.ofNat_eq_ofNat] at hmemcpy hcomp' hpc hcont ⊢
  have hsp_align : s.sp &&& 15#64 = 0#64 := by
    rw [hsp]; exact sp672_aligned sp0 hsp0
  have hptr_l_ne0 : (ptr_l == 0#64) = false := beq_eq_false_iff_ne.mpr hptr_l_ne
  have htoNat_b : (BitVec.ofNat 64 (2 * (k + 1))).toNat = (gf16ListBytes b_init.coefficients).length :=
    toNat_two_mul_succ_eq_gf16ListBytes k b_init.coefficients hk_le hb_len
  wp_conv_pre =>
    rw [memcpy_memRegion_gf16Slice_pre ptr_l ptr_b b_init.coefficients (2 * (k + 1)) (by omega)]
  refine seq_vm_clean (mid := lsρ spqrMemcpySym)
    (P_mid :=
      memRegion ptr_l (gf16ListBytes b_init.coefficients).length ∗
        (ptr_b ↦ₛ gf16ListBytes b_init.coefficients) ∗
        ptSliceAt pt_ptr pts_slice ∗
        ((sp0 - 664#64) ↦₆₄ x19_slot) ∗
        ((sp0 - 640#64) ↦₆₄ ptr_b) ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        stackAt (sp0 - 672#64) lagrangeCompleteStack ∗ P)
    (Q := fun s1 =>
      s1.sp = sp0 - 672#64 ∧
      s1.readReg64 .x0 = ptr_l ∧
      s1.readReg64 .x1 = ptr_b ∧
      s1.readReg64 .x2 = BitVec.ofNat 64 (2 * (k + 1)) ∧
      s1.readReg64 .x20 = s.readReg64 .x20 ∧
      s1.readReg64 .x21 = BitVec.ofNat 64 k ∧
      s1.readReg64 .x22 = s.readReg64 .x22 ∧
      s1.readReg64 .x24 = BitVec.ofNat 64 (2 * (k + 1)) ∧
      s1.readReg64 .x25 = BitVec.ofNat 64 (k + 1) ∧
      s1.readReg64 .x26 = ptr_l ∧
      s1.readReg64 .x27 = pt_ptr ∧
      s1.readReg64 .x29 = sp0 - 96#64 ∧
      s1.readReg64 .x30 = (blkPl_418).base + 824#64 ∧
      traceVRegs s1 = traceVRegs s)
    ?_ ?_
  · by_vm_steps (
      wp_steps 7
      exact SepWP.done (by simp [wp_norm, arm64_norm, hptr_l_ne0])
        (by simp [wp_norm, arm64_norm, hstat])
        ⟨by simp [wp_norm, arm64_norm], Entails.of_eq (by sep_ac_rfl),
         by simpa [wp_norm, arm64_norm] using hsp,
         by simp [wp_norm, arm64_norm, hx0],
         by simp [wp_norm, arm64_norm, hx23],
         by simp [wp_norm, arm64_norm, hx24],
         by simp [wp_norm, arm64_norm],
         by simp [wp_norm, arm64_norm, hx21],
         by simp [wp_norm, arm64_norm],
         by simp [wp_norm, arm64_norm, hx24],
         by simp [wp_norm, arm64_norm, hx25],
         by simp [wp_norm, arm64_norm, hx0],
         by simp [wp_norm, arm64_norm, hx27],
         by simp [wp_norm, arm64_norm, hx29],
         by simp [wp_norm, arm64_norm],
         by simp [wp_norm, arm64_norm]⟩)
  · rintro s1 hpc1 hstat1 hvm1 ⟨hsp1, hx0_1, hx1_1, hx2_1, hx20_1, hx21_1, hx22_1,
      hx24_1, hx25_1, hx26_1, hx27_1, hx29_1, hx30_1, htr1⟩
    simp only [traceVRegs, Prod.mk.injEq] at htr1
    have hsp1_al : s1.spAligned = true := by
      unfold State.spAligned
      rw [hsp1, sp672_aligned sp0 hsp0]
      rfl
    wp_call hmemcpy ⟨ptr_l, ptr_b, gf16ListBytes b_init.coefficients⟩
    wp_conv_pre =>
      rw [← gf16SliceAt_eq_pointsToBytes b_init.coefficients ptr_l,
          ← gf16SliceAt_eq_pointsToBytes b_init.coefficients ptr_b]
    have hvm2 : VmPreserved s sf := hvm1.trans (by assumption)
    have h1_len : BitVec.ofNat 64 (k + 1) = BitVec.ofNat 64 b_init.coefficients.length := by
      rw [hb_len]
    have h3_len : BitVec.ofNat 64 k = BitVec.ofNat 64 pts_slice.length := by
      rw [hpts_len]
    have h0_pts : 0 < pts_slice.length := by omega
    have h2_lt : 2 * b_init.coefficients.length < 2 ^ 64 := by omega
    have h4_lt : 4 * pts_slice.length < 2 ^ 64 := by omega
    wp_steps 6
    refine with_vm_cur (s := sf) fun hvm3_step => ?_
    have hvm3 : VmPreserved s _ := hvm2.trans hvm3_step
    wp_call hcomp' ⟨ptr_l, pt_ptr, b_init, pts_slice, 0⟩
    wp_conv_pre => rw [hsp_sf, hsp1]
    have hvm4 : VmPreserved s sf_1 := hvm3.trans (by assumption)
    refine SepWP.weaken_pre ?_
      (hcont sf_1
        (by exact hpc_sf_1)
        (by exact hrun_sf_1)
        (by rw [hsp_sf_1, hsp_sf, hsp1])
        (by simp [traceVRegs, wp_norm, arm64_norm, *])
        hvm4
        (by simp [wp_norm, arm64_norm, *])
        (by simp [wp_norm, arm64_norm, *])
        (by simp [wp_norm, arm64_norm, *])
        (by simp [wp_norm, arm64_norm, *])
        (by simp [wp_norm, arm64_norm, *])
        (by simp [wp_norm, arm64_norm, *])
        (by simp [wp_norm, arm64_norm, *])
        (by simp [wp_norm, arm64_norm, *]))
    exact Entails.of_eq (by sep_ac_rfl)

end LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.InterpolatePlacedBudget

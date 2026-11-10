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
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.InterpolateFull
public import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.DefsBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.Interpolate
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.InterpolatePlacedBudget
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Full Inlined `lagrange_interpolate` for `<PolyDecoder as Decoder>::decoded_message`

Threads `RustCliAllocBudget M` and `LagrangeInterpolateInlinedEnv` through the full inlined
`Poly::lagrange_interpolate` block on Block `418`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.InterpolateFullPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification (LibsignalPlacement blkPC_418 blkPl_418 lsmpl lsρ)
open CryptoVerification.LibsignalSpqrV1 (GF16 Poly Pt)
open CryptoVerification.LibsignalTripleRatchet (sessionMemcpyRegionSpec sessionShimSpec)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.Alloc (
  spqrMemcpySym spqrRustAllocSym spqrRustNoAllocShimSym spqr_hook_ok_of_mem
)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Poly (gf16At gf16SliceAt polyOf ptSliceAt)
open CryptoVerification.SpqrV1.Poly.AddChunk.AddChunkNorm (
  readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre readReg64_setPC_pre
  readReg_setMem_setPC_pre readReg_setPC_pre sp_setMem_setPC_pre sp_setPC_pre
)
open CryptoVerification.SpqrV1.Poly.DecodedMessage (
  bv64_add1_norm' bv64_lsl1_norm bv64_lsl1_norm' bv64_lsl4_norm'
  fold_interpolateScratchAt gf16ListBytes gf16SliceAt_eq_pointsToBytes
  gf16SliceAt_split_first' gf16SliceAt_to_memRegion interpolateScratchAt
  lagrangeInterpolateLoopTotal lagrangeInterpolateTotal
  lagrangeInterpolateTotal_coeffs_eq lagrangeInterpolateTotal_length
  memcpy_memRegion_gf16Slice_pre optPolyCacheSlotAt
  pointsTo64_three_entails_memRegion_24 ptSliceRefAt
  sp144_add_16 sp144_add_8 sp168_add_8 sp192_add_8 sp216_add_48 sp672_aligned
  sp96_sub_120 sp96_sub_32 sp96_sub_40 sp96_sub_48 sp96_sub_56 sp96_sub_64
  sp96_sub_72 sp96_sub_80 sp96_sub_96 spqrRustDeallocSym
  stackAt_alloc_eq_complete stackAt_prepare_eq_alloc
  toNat_two_mul_eq_gf16ListBytes traceVRegs umaddl_24_ofNat'
)
open CryptoVerification.SpqrV1.Poly.LagrangeComplete (
  lagrangeCompletePlacedSpec lagrangeCompletePure lagrangeCompletePure_length
  lagrangeCompleteStack
)
open CryptoVerification.SpqrV1.Poly.LagrangePrepare (
  LagrangePrepareArgs lagrangePreparePure lagrangePreparePure_length
  lagrangePrepareStack polyOf_eq
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents
  FreeOnlyEvs RustCliAllocBudget RustLayoutOk SeqEnv VmPreserved fitsEvents_append
  rustAllocEvents rustCliAllocBudgetSpec rustCliAllocNoOomSpec
  rustCliDeallocBudgetSpec subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget (
  LagrangeInterpolateInlinedEnv LagrangeInterpolateMissEnv
)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.InterpolatePlacedBudget (
  lagrangeInterpolateDealloc_placed_sepWP lagrangeInterpolateOuter_placed_sepWP
  lagrangeInterpolateStoreSlot_placed_sepWP
  lagrangeInterpolate_copyAndComplete0_placed_sepWP
  lagrangeInterpolate_hit_placed_sepWP
)
open LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.DefsBudget (
  LagrangePrepareEnv lagrangePreparePlacedSpec
)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff rustAllocEvents
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

attribute [local wp_norm, local arm64_norm]
  bv64_lsl1_norm' bv64_lsl4_norm' bv64_add1_norm' umaddl_24_ofNat'
attribute [local wp_norm ↓, local arm64_norm ↓]
  sp96_sub_120 sp96_sub_96 sp96_sub_80 sp96_sub_72 sp96_sub_64
  sp96_sub_56 sp96_sub_48 sp96_sub_40 sp96_sub_32
  sp216_add_48 sp192_add_8 sp168_add_8 sp144_add_8 sp144_add_16

private theorem seq_vm_clean {P : Program} {b : BitVec 64} {Hk : String → Option (State → State)}
    {mid target : BitVec 64} {s : State}
    {Pre P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP (P.rebase b Hk) mid s Pre (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → VmPreserved s sm → Q sm →
      SepWP (P.rebase b Hk) target sm P_mid post) :
    SepWP (P.rebase b Hk) target s Pre post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨hvm, hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hvm hQ)

private theorem with_vm_cur {P : Program} {target : BitVec 64} {s s' : State}
    {Pre : SepProp} {post : State → SepProp → Prop}
    (hk : VmPreserved s s' → SepWP P target s' Pre post)
    (hvm : VmPreserved s s' := by simp [wp_norm, arm64_norm]) :
    SepWP P target s' Pre post :=
  hk hvm

private def lagrangePrepareFixedSpec [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (LagrangePrepareArgs × M.σ) where
  pre := (lagrangePreparePlacedSpec M A lim).pre
  post := fun (a, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ polyOf A.repAlloc a.out (lagrangePreparePure a.pts) ∗
      ptSliceAt a.ptsPtr a.pts ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
      A.pool lim (M.stepEvents (rustAllocEvents (2 * (a.pts.length + 1)) 2) st) sf ∗
      stackAt s0.sp lagrangePrepareStack

private theorem subroutine_ok_lagrangePrepare_fixed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {entry : BitVec 64}
    (h : subroutine_ok P entry (lagrangePreparePlacedSpec M A lim)) :
    subroutine_ok P entry (lagrangePrepareFixedSpec M A lim) := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) (fun ⟨a, st⟩ R s0 sf hq => ?_)
  dsimp only [lagrangePreparePlacedSpec, lagrangePrepareFixedSpec, LagrangePrepareEnv] at hq ⊢
  rw [sepExists_sepConj_left, satisfies_sepExists] at hq
  rcases hq with ⟨evs, hq⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq
  rcases hq with ⟨⟨rfl, htr⟩, hrest⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨htr, hrest⟩

/-! ## Second Part of Iteration `i = 0` and Outer Loop -/

theorem lagrangeInterpolate_copyFirstAcc_placed_sepWP [LibsignalPlacement]
    {ext : String → Option (State → State)} {ret_pc : BitVec 64}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym
      (withVmPreserved sessionMemcpyRegionSpec))
    (hcomp : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 373) (withVmPreserved lagrangeCompletePlacedSpec))
    (sp0 acc_ptr ptr_l ptr_b pt_ptr v152 : BitVec 64) (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (k : Nat) (b_init : Poly) (pts_slice : List Pt)
    (hk_pos : 1 ≤ k) (hk_le : k ≤ 65536)
    (hb_eq : b_init = lagrangePreparePure pts_slice) (hpts_len : pts_slice.length = k)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (blkPl_418).base + 848#64) (hstat : s.status = .Running) (hsp : s.sp = sp0 - 672#64)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 k)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (2 * (k + 1)))
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 (k + 1))
    (hx26 : s.readReg64 .x26 = ptr_l) (hx27 : s.readReg64 .x27 = pt_ptr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hcont : ∀ sf : State,
      sf.pc = (blkPl_418).base + 1136#64 → sf.status = .Running → sf.sp = sp0 - 672#64 →
      traceVRegs sf = traceVRegs s → VmPreserved s sf →
      sf.readReg64 .x20 = s.readReg64 .x20 → sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x24 = BitVec.ofNat 64 (2 * (k + 1)) → sf.readReg64 .x26 = ptr_l →
      sf.readReg64 .x29 = sp0 - 96#64 →
      SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc sf
        (gf16SliceAt acc_ptr (lagrangeInterpolateTotal pts_slice).coefficients ∗
          memRegion ptr_l (2 * (k + 1)) ∗ gf16SliceAt ptr_b b_init.coefficients ∗
          ptSliceAt pt_ptr pts_slice ∗ ((sp0 - 656#64) ↦₆₄ acc_ptr) ∗
          ((sp0 - 640#64) ↦₆₄ ptr_b) ∗ ((sp0 - 152#64) ↦₆₄ BitVec.ofNat 64 k) ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          stackAt (sp0 - 672#64) lagrangeCompleteStack ∗ P) post) :
    SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc s
      (memRegion acc_ptr (2 * k) ∗
        gf16SliceAt ptr_l (lagrangeCompletePure b_init pts_slice 0).coefficients ∗
        gf16SliceAt ptr_b b_init.coefficients ∗ ptSliceAt pt_ptr pts_slice ∗
        ((sp0 - 656#64) ↦₆₄ acc_ptr) ∗ ((sp0 - 640#64) ↦₆₄ ptr_b) ∗
        ((sp0 - 152#64) ↦₆₄ v152) ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        stackAt (sp0 - 672#64) lagrangeCompleteStack ∗ P) post := by
  have hb_len : b_init.coefficients.length = k + 1 := by
    rw [hb_eq, lagrangePreparePure_length, hpts_len]
  have hmemcpy : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsρ spqrMemcpySym) (withVmPreserved sessionMemcpyRegionSpec) :=
    spqr_hook_ok_of_mem hmemcpy_sat
  simp only [withVmPreserved, sessionMemcpyRegionSpec] at hmemcpy
  have houter := @lagrangeInterpolateOuter_placed_sepWP _ ext ret_pc hmemcpy_sat hcomp
    sp0 acc_ptr ptr_l ptr_b pt_ptr hsp0 k b_init pts_slice hk_pos hk_le hb_len hpts_len
  try dsimp only [BitVec.ofNat_eq_ofNat] at hmemcpy houter hpc hcont ⊢
  have hsp_al_s : s.spAligned = true := by
    unfold State.spAligned; rw [hsp, sp672_aligned sp0 hsp0]; rfl
  let working0 := lagrangeCompletePure b_init pts_slice 0
  have hw0_len : working0.coefficients.length = k + 1 := by
    dsimp [working0]; rw [lagrangeCompletePure_length, hb_len]
  have htoNat_k : (BitVec.ofNat 64 (2 * k)).toNat = (gf16ListBytes (working0.coefficients.drop 1)).length :=
    toNat_two_mul_eq_gf16ListBytes k (working0.coefficients.drop 1) hk_le
      (by rw [List.length_drop, hw0_len]; omega)
  have hand_k1 : BitVec.ofNat 64 (k + 1) &&& 0x7fffffffffffffff#64 = BitVec.ofNat 64 (k + 1) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    change (k + 1) &&& (2 ^ 63 - 1) = k + 1
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]
  have hsub1_k1 : BitVec.ofNat 64 (k + 1) - 1#64 = BitVec.ofNat 64 k := by
    rw [← bv64_add1_norm' k, BitVec.add_sub_cancel]
  have hand_k : BitVec.ofNat 64 k &&& 0x7fffffffffffffff#64 = BitVec.ofNat 64 k := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    change k &&& (2 ^ 63 - 1) = k
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]
  have hult_k_self : (BitVec.ofNat 64 k).ult (BitVec.ofNat 64 k) = false := by simp [BitVec.ult]
  have hk_ne0 : (BitVec.ofNat 64 k == 0#64) = false := by
    rw [beq_eq_false_iff_ne]; intro h
    have h1 := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1; change k = 0 at h1; omega
  have hlsl_k : (BitVec.ofNat 64 k) <<< 1 = BitVec.ofNat 64 (2 * k) := bv64_lsl1_norm k
  have hsplit_w0 := gf16SliceAt_split_first' ptr_l working0.coefficients (by omega)
  change SepWP _ _ _ (memRegion acc_ptr (2 * k) ∗ gf16SliceAt ptr_l working0.coefficients ∗ _) _
  wp_conv_pre => rw [hsplit_w0]
  wp_steps 15
  refine with_vm_cur (s := s) fun hvm1 => ?_
  refine SepWP.weaken_pre
    (show _ ⊢ memRegion acc_ptr (2 * k) ∗ gf16SliceAt (ptr_l + 2#64) (working0.coefficients.drop 1) ∗
      (gf16At (working0.coefficients[0]'(by omega)) ptr_l ∗ gf16SliceAt ptr_b b_init.coefficients ∗
        ptSliceAt pt_ptr pts_slice ∗ ((sp0 - 656#64) ↦₆₄ acc_ptr) ∗ ((sp0 - 640#64) ↦₆₄ ptr_b) ∗
        ((sp0 - 152#64) ↦₆₄ v152) ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        stackAt (sp0 - 672#64) lagrangeCompleteStack ∗ P) by
      exact Entails.of_eq (by sep_ac_rfl)) ?_
  wp_conv_pre =>
    rw [memcpy_memRegion_gf16Slice_pre acc_ptr (ptr_l + 2#64) (working0.coefficients.drop 1) (2 * k)
      (by rw [List.length_drop, hw0_len]; omega)]
  wp_call hmemcpy ⟨acc_ptr, ptr_l + 2#64, gf16ListBytes (working0.coefficients.drop 1)⟩
  have hvm2 : VmPreserved s sf := hvm1.trans (by assumption)
  wp_conv_pre =>
    rw [← gf16SliceAt_eq_pointsToBytes (working0.coefficients.drop 1) acc_ptr,
        ← gf16SliceAt_eq_pointsToBytes (working0.coefficients.drop 1) (ptr_l + 2#64)]
  refine SepWP.weaken_pre
    (show _ ⊢ (gf16At (working0.coefficients[0]'(by omega)) ptr_l ∗
        gf16SliceAt (ptr_l + 2#64) (working0.coefficients.drop 1)) ∗
      (gf16SliceAt acc_ptr (working0.coefficients.drop 1) ∗ gf16SliceAt ptr_b b_init.coefficients ∗
        ptSliceAt pt_ptr pts_slice ∗ ((sp0 - 656#64) ↦₆₄ acc_ptr) ∗ ((sp0 - 640#64) ↦₆₄ ptr_b) ∗
        ((sp0 - 152#64) ↦₆₄ v152) ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        stackAt (sp0 - 672#64) lagrangeCompleteStack ∗ P) by
      exact Entails.of_eq (by sep_ac_rfl)) ?_
  wp_conv_pre => rw [← hsplit_w0]
  have hbeq_k1 : (BitVec.ofNat 64 k - 1#64 == 0#64) = decide (k = 1) := by
    by_cases hk1 : k = 1
    · subst hk1; rfl
    · simp only [hk1, decide_false, beq_eq_false_iff_ne, ne_eq]; intro h
      have h1 := congrArg (fun x => (x + 1#64).toNat) h
      rw [BitVec.sub_add_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
      exact hk1 h1
  by_cases hk1 : k = 1
  · subst hk1
    refine seq_vm_clean (mid := (blkPl_418).base + 1136#64)
      (P_mid := gf16SliceAt ptr_l working0.coefficients ∗
        gf16SliceAt acc_ptr (working0.coefficients.drop 1) ∗ gf16SliceAt ptr_b b_init.coefficients ∗
        ptSliceAt pt_ptr pts_slice ∗ ((sp0 - 656#64) ↦₆₄ acc_ptr) ∗ ((sp0 - 640#64) ↦₆₄ ptr_b) ∗
        ((sp0 - 152#64) ↦₆₄ BitVec.ofNat 64 1) ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        stackAt (sp0 - 672#64) lagrangeCompleteStack ∗ P)
      (Q := fun s1 =>
        s1.sp = sp0 - 672#64 ∧ traceVRegs s1 = traceVRegs s ∧
        s1.readReg64 .x20 = s.readReg64 .x20 ∧ s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x24 = BitVec.ofNat 64 (2 * (1 + 1)) ∧ s1.readReg64 .x26 = ptr_l ∧
        s1.readReg64 .x29 = sp0 - 96#64) ?_ ?_
    · by_vm_steps (
        wp_steps 5
        exact SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_sf])
          ⟨by simp [wp_norm, arm64_norm], Entails.of_eq (by sep_ac_rfl),
           by simp only [wp_norm, arm64_norm]; rw [hsp_sf, hsp],
           by simp [traceVRegs, wp_norm, arm64_norm, *],
           by simp only [wp_norm, arm64_norm]; exact h_1,
           by simp only [wp_norm, arm64_norm]; exact h_3,
           by simp only [wp_norm, arm64_norm]; rw [h_5]; simp only [wp_norm, arm64_norm, hx24],
           by simp only [wp_norm, arm64_norm]; rw [h_7]; exact hx26,
           by simp only [wp_norm, arm64_norm]; rw [hcs_sf]; exact hx29⟩)
    · rintro s1 hpc1 hrun1 hvm3 ⟨hsp1, htr1, hx20_1, hx22_1, hx24_1, hx26_1, hx29_1⟩
      have hinterp_k1 : working0.coefficients.drop 1 = (lagrangeInterpolateTotal pts_slice).coefficients := by
        have houter0 := lagrangeInterpolateTotal_coeffs_eq pts_slice (by omega)
        rw [hpts_len, Nat.sub_self, ← hb_eq] at houter0
        simpa [lagrangeInterpolateLoopTotal, working0] using houter0.symm
      rw [hinterp_k1]
      have hmem_l := gf16SliceAt_to_memRegion ptr_l working0.coefficients
      rw [hw0_len, Nat.mul_comm] at hmem_l
      refine SepWP.weaken_pre (sepConj_mono_left hmem_l) ?_
      refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (hcont s1 hpc1 hrun1 hsp1 htr1 (hvm2.trans hvm3) hx20_1 hx22_1 hx24_1 hx26_1 hx29_1)
  · have hbeq_false : (BitVec.ofNat 64 k - 1#64 == 0#64) = false := by
      rw [hbeq_k1, decide_eq_false hk1]
    refine seq_vm_clean (mid := (blkPl_418).base + 940#64)
      (P_mid := gf16SliceAt ptr_l working0.coefficients ∗
        gf16SliceAt acc_ptr (working0.coefficients.drop 1) ∗ gf16SliceAt ptr_b b_init.coefficients ∗
        ptSliceAt pt_ptr pts_slice ∗ ((sp0 - 656#64) ↦₆₄ acc_ptr) ∗ ((sp0 - 640#64) ↦₆₄ ptr_b) ∗
        ((sp0 - 152#64) ↦₆₄ BitVec.ofNat 64 k) ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        stackAt (sp0 - 672#64) lagrangeCompleteStack ∗ P)
      (Q := fun s1 =>
        s1.sp = sp0 - 672#64 ∧ traceVRegs s1 = traceVRegs s ∧
        s1.readReg64 .x19 = 1#64 ∧ s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg64 .x21 = BitVec.ofNat 64 k ∧ s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = pt_ptr ∧ s1.readReg64 .x24 = BitVec.ofNat 64 (2 * (k + 1)) ∧
        s1.readReg64 .x25 = BitVec.ofNat 64 (k + 1) ∧ s1.readReg64 .x26 = ptr_l ∧
        s1.readReg64 .x27 = 0#64 - BitVec.ofNat 64 k ∧ s1.readReg64 .x29 = sp0 - 96#64) ?_ ?_
    · by_vm_steps (
        wp_steps 5
        wp_steps 3
        exact SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_sf])
          ⟨by simp [wp_norm, arm64_norm], Entails.of_eq (by sep_ac_rfl),
           by simp only [wp_norm, arm64_norm]; rw [hsp_sf, hsp],
           by simp [traceVRegs, wp_norm, arm64_norm, *],
           by simp [wp_norm, arm64_norm],
           by simp only [wp_norm, arm64_norm]; exact h_1,
           by simp only [wp_norm, arm64_norm]; rw [h_2]; exact hx21,
           by simp only [wp_norm, arm64_norm]; exact h_3,
           by simp only [wp_norm, arm64_norm]; exact h_4,
           by simp only [wp_norm, arm64_norm]; rw [h_5]; exact hx24,
           by simp only [wp_norm, arm64_norm]; rw [h_6]; exact hx25,
           by simp only [wp_norm, arm64_norm]; rw [h_7]; exact hx26,
           by simp [wp_norm, arm64_norm],
           by simp only [wp_norm, arm64_norm]; rw [hcs_sf]; exact hx29⟩)
    · rintro s1 hpc1 hrun1 hvm3 ⟨hsp1, htr1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1,
        hx24_1, hx25_1, hx26_1, hx27_1, hx29_1⟩
      refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (houter (k - 1) 1 (working0.coefficients.drop 1) working0.coefficients s1
          (((sp0 - 152#64) ↦₆₄ BitVec.ofNat 64 k) ∗ P) post (by omega) (by omega)
          (by rw [List.length_drop, hw0_len]; omega) hw0_len
          hpc1 hrun1 hsp1 hx19_1 hx21_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx29_1
          (fun sf_f hpc_f hstat_f hsp_f htr_f hvm_f hx20_f _ hx22_f _ hx24_f _ hx26_f hx29_f => ?_))
      have hinterp_k :
        lagrangeInterpolateLoopTotal b_init pts_slice 1 (k - 1) (working0.coefficients.drop 1) =
          (lagrangeInterpolateTotal pts_slice).coefficients := by
        have houter_eq := lagrangeInterpolateTotal_coeffs_eq pts_slice (by omega)
        rw [hpts_len, ← hb_eq] at houter_eq; exact houter_eq.symm
      rw [hinterp_k]
      refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (hcont sf_f hpc_f hstat_f hsp_f (htr_f.trans htr1)
          ((hvm2.trans hvm3).trans hvm_f) (hx20_f.trans hx20_1) (hx22_f.trans hx22_1)
          hx24_f hx26_f hx29_f)

/-! ## Cache-Miss Sub-Steps and Full Inlined `lagrange_interpolate` -/

theorem lagrangeInterpolate_miss_allocAcc_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {target_pc : BitVec 64}
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym
      (withVmPreserved sessionShimSpec))
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym
      (rustCliAllocBudgetSpec M A lim false))
    (sp0 pts_vec_ptr pt_ptr : BitVec 64) (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (polyIdx k : Nat) (hpoly : polyIdx < 16) (hk_pos : 1 ≤ k) (hk_le : k ≤ 65536)
    (st : M.σ) (hfit : FitsEvents M lim st (rustAllocEvents (2 * k) 2))
    (s0 s : State) (F : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (blkPl_418).base + 660#64) (hstat : s.status = .Running)
    (hsp : s.sp = sp0 - 672#64) (htr : traceVRegs s = traceVRegs s0)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 polyIdx) (hx25 : s.readReg64 .x25 = 24#64)
    (hx26 : s.readReg64 .x26 = sp0 - 600#64) (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hnext : ∀ sf : State,
      sf.pc = (blkPl_418).base + 732#64 → sf.status = .Running → sf.sp = sp0 - 672#64 →
      traceVRegs sf = traceVRegs s0 → sf.readReg64 .x0 ≠ 0#64 →
      sf.readReg64 .x19 = (sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx) →
      sf.readReg64 .x20 = s.readReg64 .x20 → sf.readReg64 .x21 = BitVec.ofNat 64 k →
      sf.readReg64 .x22 = s.readReg64 .x22 → sf.readReg64 .x23 = BitVec.ofNat 64 (2 * k) →
      sf.readReg64 .x27 = pt_ptr → sf.readReg64 .x29 = sp0 - 96#64 →
      SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) target_pc sf
        (A.live (sf.readReg64 .x0) (2 * k) 2 ∗ memRegion (sf.readReg64 .x0) (2 * k) ∗
          optPolyCacheSlotAt A.repAlloc ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx)) none ∗
          ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗ ((sp0 - 608#64) ↦₆₄ 16#64) ∗
          ptSliceRefAt (pts_vec_ptr + BitVec.ofNat 64 (16 * polyIdx)) pt_ptr k ∗
          A.pool lim (M.stepEvents (rustAllocEvents (2 * k) 2) st) sf ∗
          stackAt (sp0 - 672#64) allocHookStack ∗ F) post) :
    SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) target_pc s
      (optPolyCacheSlotAt A.repAlloc ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx)) none ∗
        ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗ ((sp0 - 608#64) ↦₆₄ 16#64) ∗
        ptSliceRefAt (pts_vec_ptr + BitVec.ofNat 64 (16 * polyIdx)) pt_ptr k ∗
        A.pool lim st s ∗ stackAt (sp0 - 672#64) allocHookStack ∗ F) post := by
  have hshim : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) (withVmPreserved sessionShimSpec) :=
    spqr_hook_ok_of_mem hshim_sat
  simp only [withVmPreserved, sessionShimSpec] at hshim
  have halloc : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustCliAllocNoOomSpec M A lim false) :=
    subroutine_ok_allocNoOom_of_budget (spqr_hook_ok_of_mem halloc_sat)
  simp only [rustCliAllocNoOomSpec, Bool.false_eq_true, ↓reduceIte] at halloc
  have hmod : polyIdx % 4294967296 = polyIdx := Nat.mod_eq_of_lt (by omega)
  have hule16 : (16#64).ule (BitVec.ofNat 64 polyIdx) = false := by
    rw [BitVec.ule_eq_decide, decide_eq_false_iff_not]; intro h
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h; omega
  have hk_ne0 : (BitVec.ofNat 64 k == 0#64) = false := by
    rw [beq_eq_false_iff_ne]; intro h
    have h1 := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1; change k = 0 at h1; omega
  have htoNat_2k : (BitVec.ofNat 64 (2 * k)).toNat = 2 * k := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hpow2 : ∃ m, 2 = 2 ^ m := ⟨1, rfl⟩
  have hlay : RustLayoutOk (2 * k) 2 := ⟨⟨by omega, hpow2, by omega⟩, by decide⟩
  rcases Prod.mk.inj htr with ⟨htr_tr, htr_vr⟩
  have hsp_al_s : s.spAligned = true := by
    unfold State.spAligned; rw [hsp, sp672_aligned sp0 hsp0]; rfl
  try dsimp only [BitVec.ofNat_eq_ofNat] at hshim halloc hpc hnext ⊢
  wp_simp_pre only [optPolyCacheSlotAt, noneCap, ptSliceRefAt]
  refine seq_vm_clean (mid := lsρ spqrRustNoAllocShimSym)
    (P_mid := A.pool lim st s ∗ stackAt (sp0 - 672#64) allocHookStack ∗
      (((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx)) ↦₆₄ BitVec.allOnes 64) ∗
      memRegion (((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx)) + 8#64) 16 ∗
      ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗ ((sp0 - 608#64) ↦₆₄ 16#64) ∗
      ((pts_vec_ptr + BitVec.ofNat 64 (16 * polyIdx)) ↦₆₄ pt_ptr) ∗
      (((pts_vec_ptr + BitVec.ofNat 64 (16 * polyIdx)) + 8#64) ↦₆₄ BitVec.ofNat 64 k) ∗ F)
    (Q := fun s1 =>
      s1.sp = sp0 - 672#64 ∧
      s1.readReg64 .x19 = (sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx) ∧
      s1.readReg64 .x20 = s.readReg64 .x20 ∧ s1.readReg64 .x21 = BitVec.ofNat 64 k ∧
      s1.readReg64 .x22 = s.readReg64 .x22 ∧ s1.readReg64 .x23 = BitVec.ofNat 64 (2 * k) ∧
      s1.readReg64 .x27 = pt_ptr ∧ s1.readReg64 .x29 = sp0 - 96#64 ∧
      s1.readReg64 .x30 = (blkPl_418).base + 716#64 ∧ traceVRegs s1 = traceVRegs s) ?_ ?_
  · by_vm_steps (
      wp_steps 14
      exact SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, hstat])
        ⟨by simp [wp_norm, arm64_norm], Entails.of_eq (by sep_ac_rfl),
         by simpa [wp_norm, arm64_norm] using hsp, by simp [wp_norm, arm64_norm, *],
         by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm, *],
         by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm, *],
         by simp [wp_norm, arm64_norm, *], by simp [wp_norm, arm64_norm, *],
         by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm]⟩)
  · rintro s1 hpc1 hstat1 hvm1 ⟨hsp1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx27_1, hx29_1,
      hx30_1, htr1⟩
    simp only [traceVRegs, Prod.mk.injEq] at htr1
    have hsp1_al : s1.spAligned = true := by
      unfold State.spAligned; rw [hsp1, sp672_aligned sp0 hsp0]; rfl
    refine SepWP.transport_budgetPool hvm1 (hnext := ?_)
    wp_call hshim ()
    refine SepWP.weaken_pre
      (show _ ⊢ A.pool lim st s1 ∗ stackAt (sp0 - 672#64) allocHookStack ∗
        (((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx)) ↦₆₄ BitVec.allOnes 64) ∗
        memRegion (((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx)) + 8#64) 16 ∗
        ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗ ((sp0 - 608#64) ↦₆₄ 16#64) ∗
        ((pts_vec_ptr + BitVec.ofNat 64 (16 * polyIdx)) ↦₆₄ pt_ptr) ∗
        (((pts_vec_ptr + BitVec.ofNat 64 (16 * polyIdx)) + 8#64) ↦₆₄ BitVec.ofNat 64 k) ∗ F by
        exact Entails.of_eq (by sep_ac_rfl)) ?_
    refine SepWP.transport_budgetPool (by assumption : VmPreserved s1 sf) (hnext := ?_)
    have hsp_shim : sf.sp = sp0 - 672#64 := (by assumption : sf.sp = s1.sp).trans hsp1
    wp_steps 3
    refine SepWP.transport_budgetPool ?_ (hnext := ?_)
    · simp [wp_norm, arm64_norm]
    wp_conv_pre => rw [← hsp_shim]
    wp_call halloc ⟨2 * k, 2, st⟩
    have hsp_alloc : sf_1.sp = sp0 - 672#64 := (by assumption : sf_1.sp = sf.sp).trans hsp_shim
    have htr_alloc : sf_1.trace = _ := (by assumption : AllocCallPreserved _ sf_1).2.1
    have hptr0_ne : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
    have hcbz : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hptr0_ne
    wp_steps 1
    refine SepWP.weaken_pre
      (show _ ⊢ A.pool lim (M.stepEvents (rustAllocEvents (2 * k) 2) st) sf_1 ∗
        A.live (sf_1.readReg64 (Reg.gpr 0#5)) (2 * k) 2 ∗
        memRegion (sf_1.readReg64 (Reg.gpr 0#5)) (2 * k) ∗
        optPolyCacheSlotAt A.repAlloc ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx)) none ∗
        ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗ ((sp0 - 608#64) ↦₆₄ 16#64) ∗
        ptSliceRefAt (pts_vec_ptr + BitVec.ofNat 64 (16 * polyIdx)) pt_ptr k ∗
        stackAt (sp0 - 672#64) allocHookStack ∗ F by
        simp only [optPolyCacheSlotAt, noneCap, ptSliceRefAt]; rw [hsp_shim]
        exact Entails.of_eq (by sep_ac_rfl)) ?_
    refine SepWP.transport_budgetPool ?_ (hnext := ?_)
    · simp [wp_norm, arm64_norm]
    refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext _ (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_sf_1])
        (by simp [wp_norm, arm64_norm, hsp_alloc])
        (by simp [traceVRegs, wp_norm, arm64_norm, *])
        (by simpa [wp_norm, arm64_norm] using hptr0_ne)
        (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
        (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
        (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
        (by simp [wp_norm, arm64_norm, *]))

theorem lagrangeInterpolate_miss_prepare_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {target_pc : BitVec 64}
    (hprep : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 372) (lagrangePreparePlacedSpec M A lim))
    (sp0 acc_ptr pt_ptr v168 v160 v152 : BitVec 64) (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (k : Nat) (pts_slice : List Pt) (hk_pos : 1 ≤ k) (hk_le : k ≤ 65536)
    (hpts_len : pts_slice.length = k)
    (st : M.σ) (hfit : FitsEvents M lim st (rustAllocEvents (2 * (k + 1)) 2))
    (s0 s : State) (F : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (blkPl_418).base + 732#64) (hstat : s.status = .Running)
    (hsp : s.sp = sp0 - 672#64) (htr : traceVRegs s = traceVRegs s0)
    (hx0 : s.readReg64 .x0 = acc_ptr) (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 k)
    (hx27 : s.readReg64 .x27 = pt_ptr) (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hnext : ∀ (b_cap ptr_b : BitVec 64) (sf : State),
      (lagrangePreparePure pts_slice).coefficients.length ≤ b_cap.toNat →
      b_cap.toNat * 2 < 2 ^ 63 → ptr_b ≠ 0#64 →
      sf.pc = (blkPl_418).base + 760#64 → sf.status = .Running → sf.sp = sp0 - 672#64 →
      traceVRegs sf = traceVRegs s0 →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = BitVec.ofNat 64 k → sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x24 = acc_ptr → sf.readReg64 .x27 = pt_ptr →
      sf.readReg64 .x29 = sp0 - 96#64 →
      SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) target_pc sf
        (((sp0 - 168#64) ↦₆₄ BitVec.ofNat 64 k) ∗ ((sp0 - 160#64) ↦₆₄ acc_ptr) ∗
          ((sp0 - 152#64) ↦₆₄ 0#64) ∗ ((sp0 - 144#64) ↦₆₄ b_cap) ∗
          ((sp0 - 136#64) ↦₆₄ ptr_b) ∗ ((sp0 - 128#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗
          A.live ptr_b (b_cap.toNat * 2) 2 ∗
          gf16SliceAt ptr_b (lagrangePreparePure pts_slice).coefficients ∗
          memRegion (ptr_b + BitVec.ofNat 64 ((lagrangePreparePure pts_slice).coefficients.length * 2))
            ((b_cap.toNat - (lagrangePreparePure pts_slice).coefficients.length) * 2) ∗
          ptSliceAt pt_ptr pts_slice ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
          A.pool lim (M.stepEvents (rustAllocEvents (2 * (k + 1)) 2) st) sf ∗
          stackAt (sp0 - 672#64) lagrangePrepareStack ∗ F) post) :
    SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) target_pc s
      (((sp0 - 168#64) ↦₆₄ v168) ∗ ((sp0 - 160#64) ↦₆₄ v160) ∗ ((sp0 - 152#64) ↦₆₄ v152) ∗
        memRegion (sp0 - 144#64) 24 ∗ ptSliceAt pt_ptr pts_slice ∗
        reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool lim st s ∗
        stackAt (sp0 - 672#64) lagrangePrepareStack ∗ F) post := by
  have hprep' := subroutine_ok_lagrangePrepare_fixed hprep
  simp only [lagrangePrepareFixedSpec, lagrangePreparePlacedSpec] at hprep'
  rcases Prod.mk.inj htr with ⟨htr_tr, htr_vr⟩
  have hsp_al_s : s.spAligned = true := by
    unfold State.spAligned; rw [hsp, sp672_aligned sp0 hsp0]; rfl
  let a : LagrangePrepareArgs := {
    out := sp0 - 144#64, ptsPtr := pt_ptr, pts := pts_slice, hlen_bound := by omega
  }
  have hfit_env : FitsEnv M lim st (LagrangePrepareEnv a) :=
    FitsEnv.eq_iff.mpr (by simpa [LagrangePrepareEnv, a, hpts_len] using hfit)
  try dsimp only [BitVec.ofNat_eq_ofNat] at hprep' hpc hnext ⊢
  refine seq_vm_clean (mid := lsmpl.base 372)
    (P_mid := A.pool lim st s ∗ memRegion a.out 24 ∗ ptSliceAt a.ptsPtr a.pts ∗
      reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ stackAt (sp0 - 672#64) lagrangePrepareStack ∗
      (((sp0 - 168#64) ↦₆₄ BitVec.ofNat 64 k) ∗ ((sp0 - 160#64) ↦₆₄ acc_ptr) ∗
        ((sp0 - 152#64) ↦₆₄ 0#64) ∗ F))
    (Q := fun s1 =>
      s1.sp = sp0 - 672#64 ∧ s1.readReg64 .x0 = a.out ∧ s1.readReg64 .x1 = a.ptsPtr ∧
      s1.readReg64 .x2 = BitVec.ofNat 64 a.pts.length ∧
      s1.readReg64 .x19 = s.readReg64 .x19 ∧ s1.readReg64 .x20 = s.readReg64 .x20 ∧
      s1.readReg64 .x21 = BitVec.ofNat 64 k ∧ s1.readReg64 .x22 = s.readReg64 .x22 ∧
      s1.readReg64 .x24 = acc_ptr ∧ s1.readReg64 .x27 = pt_ptr ∧
      s1.readReg64 .x29 = sp0 - 96#64 ∧ s1.readReg64 .x30 = (blkPl_418).base + 760#64 ∧
      traceVRegs s1 = traceVRegs s) ?_ ?_
  · by_vm_steps (
      wp_steps 7
      exact SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hstat])
        ⟨by simp [wp_norm, arm64_norm], Entails.of_eq (by sep_ac_rfl),
         by simpa [wp_norm, arm64_norm] using hsp, by simp [a, wp_norm, arm64_norm, hx29],
         by simp [a, wp_norm, arm64_norm, hx27], by simp [a, wp_norm, arm64_norm, hx21, hpts_len],
         by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
         by simp [wp_norm, arm64_norm, hx21], by simp [wp_norm, arm64_norm],
         by simp [wp_norm, arm64_norm, hx0], by simp [wp_norm, arm64_norm, hx27],
         by simp [wp_norm, arm64_norm, hx29], by simp [wp_norm, arm64_norm],
         by simp [wp_norm, arm64_norm]⟩)
  · rintro s1 hpc1 hstat1 hvm1 ⟨hsp1, hx0_1, hx1_1, hx2_1, hx19_1, hx20_1, hx21_1, hx22_1,
      hx24_1, hx27_1, hx29_1, hx30_1, htr1⟩
    simp only [traceVRegs, Prod.mk.injEq] at htr1
    have hsp1_al : s1.spAligned = true := by
      unfold State.spAligned; rw [hsp1, sp672_aligned sp0 hsp0]; rfl
    refine SepWP.transport_budgetPool hvm1 (hnext := ?_)
    wp_conv_pre => rw [← hsp1]
    wp_call hprep' ⟨a, st⟩
    wp_conv_pre => rw [hsp1]
    have hb_len : (lagrangePreparePure pts_slice).coefficients.length = k + 1 := by
      rw [lagrangePreparePure_length, hpts_len]
    dsimp only [a] at *
    rw [hpts_len]
    rw [polyOf_eq A.repAlloc (sp0 - 144#64) (lagrangePreparePure pts_slice)]
    dsimp only [RustCliAllocBudget.repAlloc_live]
    rw [sepExists_sepConj_left]; apply SepWP.exists_left; intro b_cap
    rw [sepExists_sepConj_left]; apply SepWP.exists_left; intro ptr_b
    apply SepWP.focus_pure (by sep_focus)
    rintro ⟨hcap_ge, hcap_lt, hptr_b_ne⟩
    have hcap_ne0 : b_cap ≠ 0 := by
      intro h0; rw [h0] at hcap_ge
      change (lagrangePreparePure pts_slice).coefficients.length ≤ 0 at hcap_ge; omega
    conv => arg 4; simp only [hcap_ne0, ↓reduceIte]
    refine SepWP.weaken_pre ?_
      (hnext b_cap ptr_b sf hcap_ge hcap_lt hptr_b_ne hpc_sf hrun_sf (by rw [hsp_sf, hsp1])
        (by simp [traceVRegs, wp_norm, arm64_norm, *])
        (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
        (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
        (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
        (by simp [wp_norm, arm64_norm, *]))
    rw [show (sp0 - 128#64) ↦₆₄ BitVec.ofNat 64 (lagrangePreparePure pts_slice).coefficients.length =
          (sp0 - 128#64) ↦₆₄ BitVec.ofNat 64 (k + 1) by rw [hb_len]]
    exact Entails.of_eq (by sep_ac_rfl)

theorem lagrangeInterpolate_miss_allocL_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {target_pc : BitVec 64}
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym
      (withVmPreserved sessionShimSpec))
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym
      (rustCliAllocBudgetSpec M A lim false))
    (sp0 acc_ptr ptr_b pt_ptr x19_slot v656 : BitVec 64) (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (k : Nat) (_hk_pos : 1 ≤ k) (hk_le : k ≤ 65536)
    (st : M.σ) (hfit : FitsEvents M lim st (rustAllocEvents (2 * (k + 1)) 2))
    (s0 s : State) (F : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (blkPl_418).base + 760#64) (hstat : s.status = .Running)
    (hsp : s.sp = sp0 - 672#64) (htr : traceVRegs s = traceVRegs s0)
    (hx19 : s.readReg64 .x19 = x19_slot) (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 k)
    (hx24 : s.readReg64 .x24 = acc_ptr) (hx27 : s.readReg64 .x27 = pt_ptr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hnext : ∀ sf : State,
      sf.pc = (blkPl_418).base + 796#64 → sf.status = .Running → sf.sp = sp0 - 672#64 →
      traceVRegs sf = traceVRegs s0 → sf.readReg64 .x0 ≠ 0#64 →
      sf.readReg64 .x19 = x19_slot → sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = BitVec.ofNat 64 k → sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = ptr_b → sf.readReg64 .x24 = BitVec.ofNat 64 (2 * (k + 1)) →
      sf.readReg64 .x25 = BitVec.ofNat 64 (k + 1) → sf.readReg64 .x27 = pt_ptr →
      sf.readReg64 .x29 = sp0 - 96#64 →
      SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) target_pc sf
        (A.live (sf.readReg64 .x0) (2 * (k + 1)) 2 ∗
          memRegion (sf.readReg64 .x0) (2 * (k + 1)) ∗ ((sp0 - 656#64) ↦₆₄ acc_ptr) ∗
          ((sp0 - 136#64) ↦₆₄ ptr_b) ∗ ((sp0 - 128#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗
          A.pool lim (M.stepEvents (rustAllocEvents (2 * (k + 1)) 2) st) sf ∗
          stackAt (sp0 - 672#64) allocHookStack ∗ F) post) :
    SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) target_pc s
      (((sp0 - 656#64) ↦₆₄ v656) ∗ ((sp0 - 136#64) ↦₆₄ ptr_b) ∗
        ((sp0 - 128#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗
        A.pool lim st s ∗ stackAt (sp0 - 672#64) allocHookStack ∗ F) post := by
  have hshim : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) (withVmPreserved sessionShimSpec) :=
    spqr_hook_ok_of_mem hshim_sat
  simp only [withVmPreserved, sessionShimSpec] at hshim
  have halloc : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustCliAllocNoOomSpec M A lim false) :=
    subroutine_ok_allocNoOom_of_budget (spqr_hook_ok_of_mem halloc_sat)
  simp only [rustCliAllocNoOomSpec, Bool.false_eq_true, ↓reduceIte] at halloc
  have hk1_ne0 : (BitVec.ofNat 64 (k + 1) == 0#64) = false := by
    rw [beq_eq_false_iff_ne]; intro h
    have h1 := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1; change k + 1 = 0 at h1; omega
  have htoNat_2k1 : (BitVec.ofNat 64 (2 * (k + 1))).toNat = 2 * (k + 1) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hpow2 : ∃ m, 2 = 2 ^ m := ⟨1, rfl⟩
  have hlay : RustLayoutOk (2 * (k + 1)) 2 := ⟨⟨by omega, hpow2, by omega⟩, by decide⟩
  rcases Prod.mk.inj htr with ⟨htr_tr, htr_vr⟩
  have hsp_al_s : s.spAligned = true := by
    unfold State.spAligned; rw [hsp, sp672_aligned sp0 hsp0]; rfl
  try dsimp only [BitVec.ofNat_eq_ofNat] at hshim halloc hpc hnext ⊢
  refine seq_vm_clean (mid := lsρ spqrRustNoAllocShimSym)
    (P_mid := A.pool lim st s ∗ stackAt (sp0 - 672#64) allocHookStack ∗
      ((sp0 - 656#64) ↦₆₄ acc_ptr) ∗ ((sp0 - 136#64) ↦₆₄ ptr_b) ∗
      ((sp0 - 128#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗ F)
    (Q := fun s1 =>
      s1.sp = sp0 - 672#64 ∧ s1.readReg64 .x19 = x19_slot ∧
      s1.readReg64 .x20 = s.readReg64 .x20 ∧ s1.readReg64 .x21 = BitVec.ofNat 64 k ∧
      s1.readReg64 .x22 = s.readReg64 .x22 ∧ s1.readReg64 .x23 = ptr_b ∧
      s1.readReg64 .x24 = BitVec.ofNat 64 (2 * (k + 1)) ∧
      s1.readReg64 .x25 = BitVec.ofNat 64 (k + 1) ∧ s1.readReg64 .x27 = pt_ptr ∧
      s1.readReg64 .x29 = sp0 - 96#64 ∧ s1.readReg64 .x30 = (blkPl_418).base + 784#64 ∧
      traceVRegs s1 = traceVRegs s) ?_ ?_
  · by_vm_steps (
      wp_steps 6
      exact SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, hstat])
        ⟨by simp [wp_norm, arm64_norm], Entails.of_eq (by sep_ac_rfl),
         by simpa [wp_norm, arm64_norm] using hsp, by simp [wp_norm, arm64_norm, *],
         by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm, *],
         by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm, *],
         by simp [wp_norm, arm64_norm, *], by simp [wp_norm, arm64_norm, *],
         by simp [wp_norm, arm64_norm, *], by simp [wp_norm, arm64_norm, *],
         by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm]⟩)
  · rintro s1 hpc1 hstat1 hvm1 ⟨hsp1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1,
      hx27_1, hx29_1, hx30_1, htr1⟩
    simp only [traceVRegs, Prod.mk.injEq] at htr1
    have hsp1_al : s1.spAligned = true := by
      unfold State.spAligned; rw [hsp1, sp672_aligned sp0 hsp0]; rfl
    refine SepWP.transport_budgetPool hvm1 (hnext := ?_)
    wp_call hshim ()
    refine SepWP.weaken_pre
      (show _ ⊢ A.pool lim st s1 ∗ stackAt (sp0 - 672#64) allocHookStack ∗
        ((sp0 - 656#64) ↦₆₄ acc_ptr) ∗ ((sp0 - 136#64) ↦₆₄ ptr_b) ∗
        ((sp0 - 128#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗ F by
        exact Entails.of_eq (by sep_ac_rfl)) ?_
    refine SepWP.transport_budgetPool (by assumption : VmPreserved s1 sf) (hnext := ?_)
    have hsp_shim : sf.sp = sp0 - 672#64 := (by assumption : sf.sp = s1.sp).trans hsp1
    wp_steps 3
    refine SepWP.transport_budgetPool ?_ (hnext := ?_)
    · simp [wp_norm, arm64_norm]
    wp_conv_pre => rw [← hsp_shim]
    wp_call halloc ⟨2 * (k + 1), 2, st⟩
    have hsp_alloc : sf_1.sp = sp0 - 672#64 := (by assumption : sf_1.sp = sf.sp).trans hsp_shim
    have htr_alloc : sf_1.trace = _ := (by assumption : AllocCallPreserved _ sf_1).2.1
    have hptr0_ne : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
    rw [hsp_shim]
    refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext _ hpc_sf_1 hrun_sf_1 hsp_alloc
        (by simp [traceVRegs, wp_norm, arm64_norm, *]) hptr0_ne
        (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
        (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
        (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
        (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
        (by simp [wp_norm, arm64_norm, *]))

/-- Full budget-threaded inlined `lagrange_interpolate` in `SepWP`: under
    `FitsEnv M lim st (LagrangeInterpolateInlinedEnv optPoly pts_slice.length)`, neither OOM nor
    allocation panic can occur. -/
theorem lagrangeInterpolate_inlined_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {target_pc : BitVec 64}
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym
      (withVmPreserved sessionShimSpec))
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym
      (rustCliAllocBudgetSpec M A lim false))
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym
      (withVmPreserved sessionMemcpyRegionSpec))
    (hprep : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 372) (lagrangePreparePlacedSpec M A lim))
    (hcomp : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 373) (withVmPreserved lagrangeCompletePlacedSpec))
    (sp0 pts_vec_ptr pt_ptr x24_saved : BitVec 64) (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (polyIdx : Nat) (optPoly : Option Poly) (pts_slice : List Pt)
    (hpoly : polyIdx < 16) (hk_pos : 1 ≤ pts_slice.length) (hk_le : pts_slice.length ≤ 65536)
    (st : M.σ)
    (hfit : FitsEnv M lim st (LagrangeInterpolateInlinedEnv optPoly pts_slice.length))
    (s0 s : State) (F : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (blkPl_418).base + 660#64)
    (hstat : s.status = .Running) (hsp : s.sp = sp0 - 672#64) (htr : traceVRegs s = traceVRegs s0)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 polyIdx) (hx24 : s.readReg64 .x24 = x24_saved)
    (hx25 : s.readReg64 .x25 = 24#64) (hx26 : s.readReg64 .x26 = sp0 - 600#64)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      LagrangeInterpolateInlinedEnv optPoly pts_slice.length evs →
      sf.pc = (blkPl_418).base + 1284#64 →
      sf.status = .Running → sf.sp = sp0 - 672#64 → traceVRegs sf = traceVRegs s0 →
      sf.readReg64 .x19 = (sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx) →
      sf.readReg64 .x20 = s.readReg64 .x20 → sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x24 = x24_saved → sf.readReg64 .x25 = 24#64 →
      sf.readReg64 .x26 = sp0 - 600#64 → sf.readReg64 .x29 = sp0 - 96#64 →
      SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) target_pc sf
        (optPolyCacheSlotAt A.repAlloc ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx))
            (some (optPoly.getD (lagrangeInterpolateTotal pts_slice))) ∗
          ((sp0 - 648#64) ↦₆₄ x24_saved) ∗ ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
          ((sp0 - 608#64) ↦₆₄ 16#64) ∗
          ptSliceRefAt (pts_vec_ptr + BitVec.ofNat 64 (16 * polyIdx)) pt_ptr pts_slice.length ∗
          ptSliceAt pt_ptr pts_slice ∗ interpolateScratchAt sp0 ∗
          reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (sp0 - 672#64) lagrangePrepareStack ∗ F) post) :
    SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) target_pc s
      (optPolyCacheSlotAt A.repAlloc ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx)) optPoly ∗
        ((sp0 - 648#64) ↦₆₄ x24_saved) ∗ ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
        ((sp0 - 608#64) ↦₆₄ 16#64) ∗
        ptSliceRefAt (pts_vec_ptr + BitVec.ofNat 64 (16 * polyIdx)) pt_ptr pts_slice.length ∗
        ptSliceAt pt_ptr pts_slice ∗ interpolateScratchAt sp0 ∗
        reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool lim st s ∗
        stackAt (sp0 - 672#64) lagrangePrepareStack ∗ F) post := by
  cases optPoly with
  | some p =>
    simp only [Option.getD_some] at hnext
    refine @lagrangeInterpolate_hit_placed_sepWP _ M A ext _ sp0 polyIdx p hpoly s _ _
      hpc hstat hx0 hx25 hx26 ?_
    intro sf hpc_f hrun_f hsp_f htr_f hvm_f _ hx19_f hx20_f hx22_f hx24_f hx25_f hx26_f hx29_f _
    refine SepWP.weaken_pre
      (show _ ⊢ A.pool lim st s ∗
        optPolyCacheSlotAt A.repAlloc ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx)) (some p) ∗
        ((sp0 - 648#64) ↦₆₄ x24_saved) ∗ ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
        ((sp0 - 608#64) ↦₆₄ 16#64) ∗
        ptSliceRefAt (pts_vec_ptr + BitVec.ofNat 64 (16 * polyIdx)) pt_ptr pts_slice.length ∗
        ptSliceAt pt_ptr pts_slice ∗ interpolateScratchAt sp0 ∗ reduceTablePlacedAt ∗
        tokenInitPlacedAt ∗ stackAt (sp0 - 672#64) lagrangePrepareStack ∗ F by
        exact Entails.of_eq (by sep_ac_rfl)) ?_
    refine SepWP.transport_budgetPool hvm_f (hnext := ?_)
    refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext sf [] rfl hpc_f hrun_f (hsp_f.trans hsp) (htr_f.trans htr)
        hx19_f hx20_f hx22_f (hx24_f.trans hx24) hx25_f hx26_f (hx29_f.trans hx29))
  | none =>
    simp only [Option.getD_none] at hnext
    change FitsEnv M lim st (SeqEnv _ FreeOnlyEvs) at hfit
    have hfit_all : FitsEvents M lim st
        (rustAllocEvents (2 * pts_slice.length) 2 ++
          rustAllocEvents (2 * (pts_slice.length + 1)) 2 ++
          rustAllocEvents (2 * (pts_slice.length + 1)) 2) :=
      FitsEnv.eq_iff.mp hfit.seq_left
    rw [List.append_assoc, fitsEvents_append] at hfit_all
    rcases hfit_all with ⟨hfit1, hfit23⟩
    rw [fitsEvents_append] at hfit23
    rcases hfit23 with ⟨hfit2, hfit3⟩
    refine SepWP.weaken_pre
      (show _ ⊢ interpolateScratchAt sp0 ∗
        (optPolyCacheSlotAt A.repAlloc ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx)) none ∗
          ((sp0 - 648#64) ↦₆₄ x24_saved) ∗ ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
          ((sp0 - 608#64) ↦₆₄ 16#64) ∗
          ptSliceRefAt (pts_vec_ptr + BitVec.ofNat 64 (16 * polyIdx)) pt_ptr pts_slice.length ∗
          ptSliceAt pt_ptr pts_slice ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool lim st s ∗
          stackAt (sp0 - 672#64) lagrangePrepareStack ∗ F) by
        exact Entails.of_eq (by sep_ac_rfl)) ?_
    unfold interpolateScratchAt
    rw [sepExists_sepConj_left]; apply SepWP.exists_left; intro v664
    rw [sepExists_sepConj_left]; apply SepWP.exists_left; intro v656
    rw [sepExists_sepConj_left]; apply SepWP.exists_left; intro v640
    rw [sepExists_sepConj_left]; apply SepWP.exists_left; intro v192
    rw [sepExists_sepConj_left]; apply SepWP.exists_left; intro v184
    rw [sepExists_sepConj_left]; apply SepWP.exists_left; intro v176
    rw [sepExists_sepConj_left]; apply SepWP.exists_left; intro v168
    rw [sepExists_sepConj_left]; apply SepWP.exists_left; intro v160
    rw [sepExists_sepConj_left]; apply SepWP.exists_left; intro v152
    refine SepWP.weaken_pre ?_
      (lagrangeInterpolate_miss_allocAcc_placed_sepWP hshim_sat halloc_sat sp0 pts_vec_ptr pt_ptr hsp0
        polyIdx pts_slice.length hpoly hk_pos hk_le st hfit1 s0 s
        (((sp0 - 664#64) ↦₆₄ v664) ∗ ((sp0 - 656#64) ↦₆₄ v656) ∗ ((sp0 - 640#64) ↦₆₄ v640) ∗
          ((sp0 - 192#64) ↦₆₄ v192) ∗ ((sp0 - 184#64) ↦₆₄ v184) ∗ ((sp0 - 176#64) ↦₆₄ v176) ∗
          ((sp0 - 168#64) ↦₆₄ v168) ∗ ((sp0 - 160#64) ↦₆₄ v160) ∗ ((sp0 - 152#64) ↦₆₄ v152) ∗
          memRegion (sp0 - 144#64) 24 ∗ ((sp0 - 648#64) ↦₆₄ x24_saved) ∗
          ptSliceAt pt_ptr pts_slice ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
          memRegion ((sp0 - 672#64) - 4304#64) 208 ∗ F)
        post hpc hstat hsp htr hx0 hx25 hx26 hx29 ?_)
    · rw [stackAt_prepare_eq_alloc (sp0 - 672#64)]; exact Entails.of_eq (by sep_ac_rfl)
    intro sf1 hpc1 hrun1 hsp1 htr1 hacc_ne hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx27_1 hx29_1
    let st1 := M.stepEvents (rustAllocEvents (2 * pts_slice.length) 2) st
    refine SepWP.weaken_pre ?_
      (lagrangeInterpolate_miss_prepare_placed_sepWP hprep sp0 (sf1.readReg64 .x0) pt_ptr v168 v160 v152
        hsp0 pts_slice.length pts_slice hk_pos hk_le rfl st1 hfit2 s0 sf1
        (A.live (sf1.readReg64 .x0) (2 * pts_slice.length) 2 ∗
          memRegion (sf1.readReg64 .x0) (2 * pts_slice.length) ∗
          optPolyCacheSlotAt A.repAlloc ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx)) none ∗
          ((sp0 - 664#64) ↦₆₄ v664) ∗ ((sp0 - 656#64) ↦₆₄ v656) ∗
          ((sp0 - 648#64) ↦₆₄ x24_saved) ∗ ((sp0 - 640#64) ↦₆₄ v640) ∗
          ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗ ((sp0 - 608#64) ↦₆₄ 16#64) ∗
          ptSliceRefAt (pts_vec_ptr + BitVec.ofNat 64 (16 * polyIdx)) pt_ptr pts_slice.length ∗
          ((sp0 - 192#64) ↦₆₄ v192) ∗ ((sp0 - 184#64) ↦₆₄ v184) ∗ ((sp0 - 176#64) ↦₆₄ v176) ∗ F)
        post hpc1 hrun1 hsp1 htr1 rfl hx21_1 hx27_1 hx29_1 ?_)
    · rw [stackAt_prepare_eq_alloc (sp0 - 672#64)]; exact Entails.of_eq (by sep_ac_rfl)
    intro b_cap ptr_b sf2 hb_cap_ge hb_cap_lt hptr_b_ne hpc2 hrun2 hsp2 htr2
      hx19_2 hx20_2 hx21_2 hx22_2 hx24_2 hx27_2 hx29_2
    let st2 := M.stepEvents (rustAllocEvents (2 * (pts_slice.length + 1)) 2) st1
    refine SepWP.weaken_pre ?_
      (lagrangeInterpolate_miss_allocL_placed_sepWP hshim_sat halloc_sat sp0 (sf1.readReg64 .x0) ptr_b pt_ptr
        ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx)) v656 hsp0
        pts_slice.length hk_pos hk_le st2 hfit3 s0 sf2
        (((sp0 - 168#64) ↦₆₄ BitVec.ofNat 64 pts_slice.length) ∗
          ((sp0 - 160#64) ↦₆₄ sf1.readReg64 .x0) ∗ ((sp0 - 152#64) ↦₆₄ 0#64) ∗
          ((sp0 - 144#64) ↦₆₄ b_cap) ∗ A.live ptr_b (b_cap.toNat * 2) 2 ∗
          gf16SliceAt ptr_b (lagrangePreparePure pts_slice).coefficients ∗
          memRegion (ptr_b + BitVec.ofNat 64 ((lagrangePreparePure pts_slice).coefficients.length * 2))
            ((b_cap.toNat - (lagrangePreparePure pts_slice).coefficients.length) * 2) ∗
          ptSliceAt pt_ptr pts_slice ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
          memRegion ((sp0 - 672#64) - 4304#64) 208 ∗
          A.live (sf1.readReg64 .x0) (2 * pts_slice.length) 2 ∗
          memRegion (sf1.readReg64 .x0) (2 * pts_slice.length) ∗
          optPolyCacheSlotAt A.repAlloc ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx)) none ∗
          ((sp0 - 664#64) ↦₆₄ v664) ∗ ((sp0 - 648#64) ↦₆₄ x24_saved) ∗
          ((sp0 - 640#64) ↦₆₄ v640) ∗ ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
          ((sp0 - 608#64) ↦₆₄ 16#64) ∗
          ptSliceRefAt (pts_vec_ptr + BitVec.ofNat 64 (16 * polyIdx)) pt_ptr pts_slice.length ∗
          ((sp0 - 192#64) ↦₆₄ v192) ∗ ((sp0 - 184#64) ↦₆₄ v184) ∗ ((sp0 - 176#64) ↦₆₄ v176) ∗ F)
        post hpc2 hrun2 hsp2 htr2 (hx19_2.trans hx19_1) hx21_2 hx24_2 hx27_2 hx29_2 ?_)
    · rw [stackAt_prepare_eq_alloc (sp0 - 672#64)]; exact Entails.of_eq (by sep_ac_rfl)
    intro sf3 hpc3 hrun3 hsp3 htr3 hptr_l_ne hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx27_3 hx29_3
    let st3 := M.stepEvents (rustAllocEvents (2 * (pts_slice.length + 1)) 2) st2
    have hb_len : (lagrangePreparePure pts_slice).coefficients.length = pts_slice.length + 1 :=
      lagrangePreparePure_length pts_slice
    refine SepWP.weaken_pre ?_
      (lagrangeInterpolate_copyAndComplete0_placed_sepWP hmemcpy_sat hcomp sp0 (sf3.readReg64 .x0) ptr_b pt_ptr
        ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx)) v664 v640 hsp0 hptr_l_ne
        pts_slice.length (lagrangePreparePure pts_slice) pts_slice hk_pos hk_le hb_len rfl sf3
        (A.live (sf3.readReg64 .x0) (2 * (pts_slice.length + 1)) 2 ∗
          A.live ptr_b (b_cap.toNat * 2) 2 ∗
          memRegion (ptr_b + BitVec.ofNat 64 ((lagrangePreparePure pts_slice).coefficients.length * 2))
            ((b_cap.toNat - (lagrangePreparePure pts_slice).coefficients.length) * 2) ∗
          A.live (sf1.readReg64 .x0) (2 * pts_slice.length) 2 ∗
          memRegion (sf1.readReg64 .x0) (2 * pts_slice.length) ∗
          optPolyCacheSlotAt A.repAlloc ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx)) none ∗
          ((sp0 - 656#64) ↦₆₄ sf1.readReg64 .x0) ∗ ((sp0 - 648#64) ↦₆₄ x24_saved) ∗
          ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗ ((sp0 - 608#64) ↦₆₄ 16#64) ∗
          ptSliceRefAt (pts_vec_ptr + BitVec.ofNat 64 (16 * polyIdx)) pt_ptr pts_slice.length ∗
          ((sp0 - 192#64) ↦₆₄ v192) ∗ ((sp0 - 184#64) ↦₆₄ v184) ∗ ((sp0 - 176#64) ↦₆₄ v176) ∗
          ((sp0 - 168#64) ↦₆₄ BitVec.ofNat 64 pts_slice.length) ∗
          ((sp0 - 160#64) ↦₆₄ sf1.readReg64 .x0) ∗ ((sp0 - 152#64) ↦₆₄ 0#64) ∗
          ((sp0 - 144#64) ↦₆₄ b_cap) ∗ ((sp0 - 136#64) ↦₆₄ ptr_b) ∗
          ((sp0 - 128#64) ↦₆₄ BitVec.ofNat 64 (pts_slice.length + 1)) ∗
          A.pool lim st3 sf3 ∗ memRegion ((sp0 - 672#64) - 4096#64) 3856 ∗
          memRegion ((sp0 - 672#64) - 4304#64) 208 ∗ F)
        post hpc3 hrun3 hsp3 rfl hx19_3 hx21_3 hx23_3 hx24_3 hx25_3 hx27_3 hx29_3 ?_)
    · rw [stackAt_alloc_eq_complete (sp0 - 672#64)]; exact Entails.of_eq (by sep_ac_rfl)
    intro sf4 hpc4 hrun4 hsp4 htr4 hvm4 hx20_4 hx21_4 hx22_4 hx24_4 hx25_4 hx26_4 hx27_4 hx29_4
    refine SepWP.weaken_pre ?_
      (lagrangeInterpolate_copyFirstAcc_placed_sepWP hmemcpy_sat hcomp sp0 (sf1.readReg64 .x0) (sf3.readReg64 .x0)
        ptr_b pt_ptr 0#64 hsp0 pts_slice.length (lagrangePreparePure pts_slice) pts_slice
        hk_pos hk_le rfl rfl sf4
        (A.live (sf3.readReg64 .x0) (2 * (pts_slice.length + 1)) 2 ∗
          A.live ptr_b (b_cap.toNat * 2) 2 ∗
          memRegion (ptr_b + BitVec.ofNat 64 ((lagrangePreparePure pts_slice).coefficients.length * 2))
            ((b_cap.toNat - (lagrangePreparePure pts_slice).coefficients.length) * 2) ∗
          A.live (sf1.readReg64 .x0) (2 * pts_slice.length) 2 ∗
          optPolyCacheSlotAt A.repAlloc ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx)) none ∗
          ((sp0 - 664#64) ↦₆₄ ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx))) ∗
          ((sp0 - 648#64) ↦₆₄ x24_saved) ∗ ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
          ((sp0 - 608#64) ↦₆₄ 16#64) ∗
          ptSliceRefAt (pts_vec_ptr + BitVec.ofNat 64 (16 * polyIdx)) pt_ptr pts_slice.length ∗
          ((sp0 - 192#64) ↦₆₄ v192) ∗ ((sp0 - 184#64) ↦₆₄ v184) ∗ ((sp0 - 176#64) ↦₆₄ v176) ∗
          ((sp0 - 168#64) ↦₆₄ BitVec.ofNat 64 pts_slice.length) ∗
          ((sp0 - 160#64) ↦₆₄ sf1.readReg64 .x0) ∗ ((sp0 - 144#64) ↦₆₄ b_cap) ∗
          ((sp0 - 136#64) ↦₆₄ ptr_b) ∗
          ((sp0 - 128#64) ↦₆₄ BitVec.ofNat 64 (pts_slice.length + 1)) ∗
          A.pool lim st3 sf3 ∗ memRegion ((sp0 - 672#64) - 4096#64) 3856 ∗
          memRegion ((sp0 - 672#64) - 4304#64) 208 ∗ F)
        post hpc4 hrun4 hsp4 hx21_4 hx24_4 hx25_4 hx26_4 hx27_4 hx29_4 ?_)
    · exact Entails.of_eq (by sep_ac_rfl)
    intro sf5 hpc5 hrun5 hsp5 htr5 hvm5 hx20_5 hx22_5 hx24_5 hx26_5 hx29_5
    refine SepWP.weaken_pre
      (show _ ⊢ A.pool lim st3 sf3 ∗
        gf16SliceAt (sf1.readReg64 .x0) (lagrangeInterpolateTotal pts_slice).coefficients ∗
        memRegion (sf3.readReg64 .x0) (2 * (pts_slice.length + 1)) ∗
        gf16SliceAt ptr_b (lagrangePreparePure pts_slice).coefficients ∗
        ptSliceAt pt_ptr pts_slice ∗ ((sp0 - 656#64) ↦₆₄ sf1.readReg64 .x0) ∗
        ((sp0 - 640#64) ↦₆₄ ptr_b) ∗ ((sp0 - 152#64) ↦₆₄ BitVec.ofNat 64 pts_slice.length) ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ stackAt (sp0 - 672#64) lagrangeCompleteStack ∗
        (A.live (sf3.readReg64 .x0) (2 * (pts_slice.length + 1)) 2 ∗
          A.live ptr_b (b_cap.toNat * 2) 2 ∗
          memRegion (ptr_b + BitVec.ofNat 64 ((lagrangePreparePure pts_slice).coefficients.length * 2))
            ((b_cap.toNat - (lagrangePreparePure pts_slice).coefficients.length) * 2) ∗
          A.live (sf1.readReg64 .x0) (2 * pts_slice.length) 2 ∗
          optPolyCacheSlotAt A.repAlloc ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx)) none ∗
          ((sp0 - 664#64) ↦₆₄ ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx))) ∗
          ((sp0 - 648#64) ↦₆₄ x24_saved) ∗ ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
          ((sp0 - 608#64) ↦₆₄ 16#64) ∗
          ptSliceRefAt (pts_vec_ptr + BitVec.ofNat 64 (16 * polyIdx)) pt_ptr pts_slice.length ∗
          ((sp0 - 192#64) ↦₆₄ v192) ∗ ((sp0 - 184#64) ↦₆₄ v184) ∗ ((sp0 - 176#64) ↦₆₄ v176) ∗
          ((sp0 - 168#64) ↦₆₄ BitVec.ofNat 64 pts_slice.length) ∗
          ((sp0 - 160#64) ↦₆₄ sf1.readReg64 .x0) ∗ ((sp0 - 144#64) ↦₆₄ b_cap) ∗
          ((sp0 - 136#64) ↦₆₄ ptr_b) ∗
          ((sp0 - 128#64) ↦₆₄ BitVec.ofNat 64 (pts_slice.length + 1)) ∗
          memRegion ((sp0 - 672#64) - 4096#64) 3856 ∗
          memRegion ((sp0 - 672#64) - 4304#64) 208 ∗ F) by
        exact Entails.of_eq (by sep_ac_rfl)) ?_
    refine SepWP.transport_budgetPool (hvm4.trans hvm5) (hnext := ?_)
    refine SepWP.weaken_pre ?_
      (lagrangeInterpolateDealloc_placed_sepWP hdealloc_sat sp0 (sf1.readReg64 .x0) (sf3.readReg64 .x0) ptr_b b_cap
        v192 v184 v176 hsp0 pts_slice.length (lagrangePreparePure pts_slice)
        hk_le hb_len hb_cap_ge hb_cap_lt st3 sf5
        (A.live (sf1.readReg64 .x0) (2 * pts_slice.length) 2 ∗
          gf16SliceAt (sf1.readReg64 .x0) (lagrangeInterpolateTotal pts_slice).coefficients ∗
          optPolyCacheSlotAt A.repAlloc ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx)) none ∗
          ((sp0 - 664#64) ↦₆₄ ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx))) ∗
          ((sp0 - 656#64) ↦₆₄ sf1.readReg64 .x0) ∗ ((sp0 - 648#64) ↦₆₄ x24_saved) ∗
          ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗ ((sp0 - 608#64) ↦₆₄ 16#64) ∗
          ptSliceRefAt (pts_vec_ptr + BitVec.ofNat 64 (16 * polyIdx)) pt_ptr pts_slice.length ∗
          ptSliceAt pt_ptr pts_slice ∗ ((sp0 - 136#64) ↦₆₄ ptr_b) ∗
          ((sp0 - 128#64) ↦₆₄ BitVec.ofNat 64 (pts_slice.length + 1)) ∗
          reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ memRegion ((sp0 - 672#64) - 4304#64) 208 ∗ F)
        post hpc5 hrun5 hsp5 hx24_5 hx26_5 hx29_5 ?_)
    · rw [stackAt_alloc_eq_complete (sp0 - 672#64)]; exact Entails.of_eq (by sep_ac_rfl)
    intro sf6 evs_free hevs_free hpc6 hrun6 hsp6 htr6 _ hx20_6 hx22_6 hx29_6
    have hout_len : (lagrangeInterpolateTotal pts_slice).coefficients.length = pts_slice.length :=
      lagrangeInterpolateTotal_length pts_slice
    refine SepWP.weaken_pre ?_
      (@lagrangeInterpolateStoreSlot_placed_sepWP _ M A ext _ sp0 (sf1.readReg64 .x0)
        ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx)) x24_saved
        b_cap ptr_b (BitVec.ofNat 64 (pts_slice.length + 1))
        hsp0 pts_slice.length (lagrangeInterpolateTotal pts_slice).coefficients
        hk_pos hk_le hout_len hacc_ne sf6
        (((sp0 - 656#64) ↦₆₄ sf1.readReg64 .x0) ∗ ((sp0 - 640#64) ↦₆₄ ptr_b) ∗
          ((sp0 - 168#64) ↦₆₄ BitVec.ofNat 64 pts_slice.length) ∗
          ((sp0 - 160#64) ↦₆₄ sf1.readReg64 .x0) ∗
          ((sp0 - 152#64) ↦₆₄ BitVec.ofNat 64 pts_slice.length) ∗
          ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗ ((sp0 - 608#64) ↦₆₄ 16#64) ∗
          ptSliceRefAt (pts_vec_ptr + BitVec.ofNat 64 (16 * polyIdx)) pt_ptr pts_slice.length ∗
          ptSliceAt pt_ptr pts_slice ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
          A.pool lim (M.stepEvents evs_free st3) sf6 ∗ stackAt (sp0 - 672#64) allocHookStack ∗
          memRegion ((sp0 - 672#64) - 4304#64) 208 ∗ F)
        post hpc6 hrun6 hsp6 hx29_6 ?_)
    · exact Entails.of_eq (by sep_ac_rfl)
    intro sf7 hpc7 hrun7 hsp7 htr7 hvm7 _ hx19_7 hx20_7 hx22_7 hx24_7 hx25_7 hx26_7 hx29_7
    refine SepWP.weaken_pre
      (show _ ⊢ ((sp0 - 144#64) ↦₆₄ BitVec.ofNat 64 pts_slice.length) ∗
        ((sp0 - 136#64) ↦₆₄ sf1.readReg64 .x0) ∗ ((sp0 - 128#64) ↦₆₄ BitVec.ofNat 64 pts_slice.length) ∗
        (((sp0 - 664#64) ↦₆₄ ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx))) ∗
          ((sp0 - 656#64) ↦₆₄ sf1.readReg64 .x0) ∗ ((sp0 - 640#64) ↦₆₄ ptr_b) ∗
          ((sp0 - 192#64) ↦₆₄ BitVec.ofNat 64 pts_slice.length) ∗
          ((sp0 - 184#64) ↦₆₄ sf1.readReg64 .x0) ∗
          ((sp0 - 176#64) ↦₆₄ BitVec.ofNat 64 pts_slice.length) ∗
          ((sp0 - 168#64) ↦₆₄ BitVec.ofNat 64 pts_slice.length) ∗
          ((sp0 - 160#64) ↦₆₄ sf1.readReg64 .x0) ∗
          ((sp0 - 152#64) ↦₆₄ BitVec.ofNat 64 pts_slice.length) ∗
          optPolyCacheSlotAt A.repAlloc ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx))
            (some (lagrangeInterpolateTotal pts_slice)) ∗
          ((sp0 - 648#64) ↦₆₄ x24_saved) ∗ ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
          ((sp0 - 608#64) ↦₆₄ 16#64) ∗
          ptSliceRefAt (pts_vec_ptr + BitVec.ofNat 64 (16 * polyIdx)) pt_ptr pts_slice.length ∗
          ptSliceAt pt_ptr pts_slice ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
          A.pool lim (M.stepEvents evs_free st3) sf6 ∗
          stackAt (sp0 - 672#64) lagrangePrepareStack ∗ F) by
        rw [stackAt_prepare_eq_alloc (sp0 - 672#64)]; exact Entails.of_eq (by sep_ac_rfl)) ?_
    refine SepWP.weaken_pre (pointsTo64_three_entails_memRegion_24 sp0 _ _ _ _) ?_
    refine SepWP.weaken_pre
      (show _ ⊢ ((sp0 - 664#64) ↦₆₄ ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx))) ∗
        ((sp0 - 656#64) ↦₆₄ sf1.readReg64 .x0) ∗ ((sp0 - 640#64) ↦₆₄ ptr_b) ∗
        ((sp0 - 192#64) ↦₆₄ BitVec.ofNat 64 pts_slice.length) ∗
        ((sp0 - 184#64) ↦₆₄ sf1.readReg64 .x0) ∗
        ((sp0 - 176#64) ↦₆₄ BitVec.ofNat 64 pts_slice.length) ∗
        ((sp0 - 168#64) ↦₆₄ BitVec.ofNat 64 pts_slice.length) ∗
        ((sp0 - 160#64) ↦₆₄ sf1.readReg64 .x0) ∗
        ((sp0 - 152#64) ↦₆₄ BitVec.ofNat 64 pts_slice.length) ∗ memRegion (sp0 - 144#64) 24 ∗
        (optPolyCacheSlotAt A.repAlloc ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx))
            (some (lagrangeInterpolateTotal pts_slice)) ∗
          ((sp0 - 648#64) ↦₆₄ x24_saved) ∗ ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
          ((sp0 - 608#64) ↦₆₄ 16#64) ∗
          ptSliceRefAt (pts_vec_ptr + BitVec.ofNat 64 (16 * polyIdx)) pt_ptr pts_slice.length ∗
          ptSliceAt pt_ptr pts_slice ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
          A.pool lim (M.stepEvents evs_free st3) sf6 ∗
          stackAt (sp0 - 672#64) lagrangePrepareStack ∗ F) by
        exact Entails.of_eq (by sep_ac_rfl)) ?_
    refine SepWP.weaken_pre (fold_interpolateScratchAt sp0 _ _ _ _ _ _ _ _ _ _) ?_
    refine SepWP.weaken_pre
      (show _ ⊢ A.pool lim (M.stepEvents evs_free st3) sf6 ∗
        optPolyCacheSlotAt A.repAlloc ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx))
          (some (lagrangeInterpolateTotal pts_slice)) ∗
        ((sp0 - 648#64) ↦₆₄ x24_saved) ∗ ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
        ((sp0 - 608#64) ↦₆₄ 16#64) ∗
        ptSliceRefAt (pts_vec_ptr + BitVec.ofNat 64 (16 * polyIdx)) pt_ptr pts_slice.length ∗
        ptSliceAt pt_ptr pts_slice ∗ interpolateScratchAt sp0 ∗ reduceTablePlacedAt ∗
        tokenInitPlacedAt ∗ stackAt (sp0 - 672#64) lagrangePrepareStack ∗ F by
        exact Entails.of_eq (by sep_ac_rfl)) ?_
    refine SepWP.transport_budgetPool hvm7 (hnext := ?_)
    have hst_eq :
        M.stepEvents evs_free st3 =
          M.stepEvents
            ((rustAllocEvents (2 * pts_slice.length) 2 ++
                rustAllocEvents (2 * (pts_slice.length + 1)) 2 ++
                rustAllocEvents (2 * (pts_slice.length + 1)) 2) ++ evs_free) st := by
      simp only [st3, st2, st1, ← AllocCostModel.stepEvents_append, List.append_assoc]
    rw [hst_eq]
    have hevs_miss :
        LagrangeInterpolateInlinedEnv none pts_slice.length
          ((rustAllocEvents (2 * pts_slice.length) 2 ++
              rustAllocEvents (2 * (pts_slice.length + 1)) 2 ++
              rustAllocEvents (2 * (pts_slice.length + 1)) 2) ++ evs_free) :=
      Or.inr ⟨_, _, rfl, rfl, hevs_free⟩
    refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext sf7 _ hevs_miss hpc7 hrun7 hsp7 (by rw [htr7, htr6, htr5, htr4, htr3]) hx19_7
        (by rw [hx20_7, hx20_6, hx20_5, hx20_4, hx20_3, hx20_2, hx20_1])
        (by rw [hx22_7, hx22_6, hx22_5, hx22_4, hx22_3, hx22_2, hx22_1])
        hx24_7 hx25_7 hx26_7 hx29_7)

theorem lagrangeInterpolate_inlined_placed_wpp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {target_pc : BitVec 64}
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym
      (withVmPreserved sessionShimSpec))
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym
      (rustCliAllocBudgetSpec M A lim false))
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym
      (withVmPreserved sessionMemcpyRegionSpec))
    (hprep : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 372) (lagrangePreparePlacedSpec M A lim))
    (hcomp : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 373) (withVmPreserved lagrangeCompletePlacedSpec))
    (sp0 pts_vec_ptr pt_ptr x24_saved : BitVec 64) (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (polyIdx : Nat) (optPoly : Option Poly) (pts_slice : List Pt)
    (hpoly : polyIdx < 16) (hk_pos : 1 ≤ pts_slice.length) (hk_le : pts_slice.length ≤ 65536)
    (st : M.σ)
    (hfit : FitsEnv M lim st (LagrangeInterpolateInlinedEnv optPoly pts_slice.length))
    (s0 s : State) (F : SepProp)
    (Q Qp : State → SepProp → Prop) (oom : State → SepProp := fun _ => ⌜False⌝)
    (hpc : s.pc = (blkPl_418).base + 660#64)
    (hstat : s.status = .Running) (hsp : s.sp = sp0 - 672#64) (htr : traceVRegs s = traceVRegs s0)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 polyIdx) (hx24 : s.readReg64 .x24 = x24_saved)
    (hx25 : s.readReg64 .x25 = 24#64) (hx26 : s.readReg64 .x26 = sp0 - 600#64)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      LagrangeInterpolateInlinedEnv optPoly pts_slice.length evs →
      sf.pc = (blkPl_418).base + 1284#64 →
      sf.status = .Running → sf.sp = sp0 - 672#64 → traceVRegs sf = traceVRegs s0 →
      sf.readReg64 .x19 = (sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx) →
      sf.readReg64 .x20 = s.readReg64 .x20 → sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x24 = x24_saved → sf.readReg64 .x25 = 24#64 →
      sf.readReg64 .x26 = sp0 - 600#64 → sf.readReg64 .x29 = sp0 - 96#64 →
      SepWPp ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) target_pc sf
        (optPolyCacheSlotAt A.repAlloc ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx))
            (some (optPoly.getD (lagrangeInterpolateTotal pts_slice))) ∗
          ((sp0 - 648#64) ↦₆₄ x24_saved) ∗ ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
          ((sp0 - 608#64) ↦₆₄ 16#64) ∗
          ptSliceRefAt (pts_vec_ptr + BitVec.ofNat 64 (16 * polyIdx)) pt_ptr pts_slice.length ∗
          ptSliceAt pt_ptr pts_slice ∗ interpolateScratchAt sp0 ∗
          reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (sp0 - 672#64) lagrangePrepareStack ∗ F) Q Qp oom) :
    SepWPp ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) target_pc s
      (optPolyCacheSlotAt A.repAlloc ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx)) optPoly ∗
        ((sp0 - 648#64) ↦₆₄ x24_saved) ∗ ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
        ((sp0 - 608#64) ↦₆₄ 16#64) ∗
        ptSliceRefAt (pts_vec_ptr + BitVec.ofNat 64 (16 * polyIdx)) pt_ptr pts_slice.length ∗
        ptSliceAt pt_ptr pts_slice ∗ interpolateScratchAt sp0 ∗
        reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool lim st s ∗
        stackAt (sp0 - 672#64) lagrangePrepareStack ∗ F) Q Qp oom := by
  apply SepWPp.of_sepWP (mid := (blkPl_418).base + 1284#64)
  refine SepWP.mono (oom := fun _ => ⌜False⌝) ?_ (fun _ _ _ _ hp => hp)
  refine lagrangeInterpolate_inlined_placed_sepWP hshim_sat halloc_sat hdealloc_sat hmemcpy_sat
    hprep hcomp sp0 pts_vec_ptr pt_ptr x24_saved hsp0 polyIdx optPoly pts_slice hpoly hk_pos hk_le
    st hfit s0 s F _ hpc hstat hsp htr hx0 hx24 hx25 hx26 hx29 ?_
  intro sf evs hevs hpc_f hrun_f hsp_f htr_f hx19_f hx20_f hx22_f hx24_f hx25_f hx26_f hx29_f
  exact SepWP.done hpc_f hrun_f
    (hnext sf evs hevs hpc_f hrun_f hsp_f htr_f hx19_f hx20_f hx22_f hx24_f hx25_f hx26_f hx29_f)

end LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.InterpolateFullPlacedBudget

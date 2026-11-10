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
public import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DecodedMsgCl1Placed
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.Interpolate
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.InterpolatePlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlaced
import ProofLib.SepLogic.WPp

/-!
# `<PolyDecoder as Decoder>::decoded_message` (Block `418`): `RustCliAllocBudget` `lagrange_interpolate` Sub-Steps

Auxiliary relocatable sub-step lemmas (`lagrangeInterpolateOuter*`, `copyAndComplete0`,
`copyFirstAcc`, `miss_prepare`) on Block `418` under `RustCliAllocBudget M` and
`LibsignalCodeLoaded lsmpl`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.States.Leaves.DecodedMsgCl1PlacedBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement blkPC_418 blkPl_418 lsmpl lsρ withLsCodeLoaded
)
open CryptoVerification.LibsignalSpqrV1 (GF16 Poly Pt)
open CryptoVerification.LibsignalTripleRatchet (sessionMemcpyRegionSpec)
open CryptoVerification.SpqrV1.Alloc (spqrMemcpySym spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Poly (gf16At gf16SliceAt polyOf ptSliceAt)
open CryptoVerification.SpqrV1.Poly.AddChunk.AddChunkNorm (
  readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre readReg64_setPC_pre
  readReg_setMem_setPC_pre readReg_setPC_pre sp_setMem_setPC_pre sp_setPC_pre
)
open CryptoVerification.SpqrV1.Poly.DecodedMessage (
  bv32_xor_gf16 bv64_add1_norm bv64_add1_norm' bv64_lsl1_norm bv64_lsl1_norm' bv64_lsl4_norm'
  bv64_succ_bne_of_le gf16ListBytes gf16SliceAt_eq_pointsToBytes
  gf16SliceAt_split_first' gf16SliceAt_to_memRegion
  lagrangeAccumulateCoeffsTotal lagrangeAccumulateCoeffsTotal_length
  lagrangeInterpolateLoopTotal lagrangeInterpolateTotal lagrangeInterpolateTotal_coeffs_eq
  memcpy_gf16Slice_pre memcpy_memRegion_gf16Slice_pre
  sp144_add_16 sp144_add_8 sp168_add_8 sp192_add_8 sp216_add_48 sp672_aligned
  sp96_sub_120 sp96_sub_32 sp96_sub_40 sp96_sub_48 sp96_sub_56 sp96_sub_64
  sp96_sub_72 sp96_sub_80 sp96_sub_96
  toNat_two_mul_eq_gf16ListBytes toNat_two_mul_succ_eq_gf16ListBytes
  traceVRegs umaddl_24_ofNat umaddl_24_ofNat'
)
open CryptoVerification.SpqrV1.Poly.LagrangeComplete (
  lagrangeCompletePlacedSpec lagrangeCompletePure lagrangeCompletePure_length
  lagrangeCompleteStack
)
open CryptoVerification.SpqrV1.Poly.LagrangePrepare (
  LagrangePrepareArgs lagrangePreparePure lagrangePreparePure_length
  lagrangePrepareStack polyOf_eq
)
open CryptoVerification.SpqrV1.States.Leaves (sepWP_seq_lscl)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits FitsEnv FitsEvents RustCliAllocBudget VmPreserved rustAllocEvents
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.InterpolatePlacedBudget (
  lagrangeAccumulateInner_placed_sepWP
)
open LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.DefsBudget (
  LagrangePrepareEnv lagrangePreparePlacedSpec
)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff rustAllocEvents
attribute [local wp_unfold] withLsCodeLoaded
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

attribute [local wp_norm, local arm64_norm]
  bv64_lsl1_norm bv64_add1_norm bv32_xor_gf16 umaddl_24_ofNat
  bv64_lsl1_norm' bv64_lsl4_norm' bv64_add1_norm' umaddl_24_ofNat'
attribute [local wp_norm ↓, local arm64_norm ↓]
  sp96_sub_120 sp96_sub_96 sp96_sub_80 sp96_sub_72 sp96_sub_64
  sp96_sub_56 sp96_sub_48 sp96_sub_40 sp96_sub_32
  sp216_add_48 sp192_add_8 sp168_add_8 sp144_add_8 sp144_add_16

/-! ## Sequencing & Fixed-Envelope Helpers -/

private theorem seq_vm_clean {P : Program} {b : BitVec 64} {Hk : String → Option (State → State)}
    {mid target : BitVec 64} {s : State}
    {Pre P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP (P.rebase b Hk) mid s Pre (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → VmPreserved s sm → Q sm →
      SepWP (P.rebase b Hk) target sm P_mid post) :
    SepWP (P.rebase b Hk) target s Pre post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨hvm, hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hvm hQ)

private theorem seq_vm_lscl [LibsignalPlacement] {P : Program} {b : BitVec 64}
    {Hk : String → Option (State → State)} {mid target : BitVec 64} {s : State}
    {Pre P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP (P.rebase b Hk) mid s Pre (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, LibsignalCodeLoaded lsmpl sm.mem → sm.pc = mid → sm.status = .Running →
      VmPreserved s sm → Q sm → SepWP (P.rebase b Hk) target sm P_mid post) :
    SepWP (P.rebase b Hk) target s Pre post :=
  sepWP_seq_lscl hcl <|
    SepWP.seq h1 fun sm _Pm hpc hrun ⟨hvm, hent, hQ⟩ =>
      SepWP.done hpc hrun fun hcl' =>
        SepWP.weaken_pre hent (h2 sm hcl' hpc hrun hvm hQ)

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

private theorem subroutine_ok_lagrangePrepare_cl_fixed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {entry : BitVec 64}
    (h : subroutine_ok P entry (withLsCodeLoaded lsmpl (lagrangePreparePlacedSpec M A lim))) :
    subroutine_ok P entry (withLsCodeLoaded lsmpl (lagrangePrepareFixedSpec M A lim)) := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) (fun ⟨a, st⟩ R s0 sf hq => ?_)
  dsimp only [withLsCodeLoaded, lagrangePreparePlacedSpec, lagrangePrepareFixedSpec,
    LagrangePrepareEnv] at hq ⊢
  rw [sepExists_sepConj_left, satisfies_sepExists] at hq
  rcases hq with ⟨evs, hq⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq
  rcases hq with ⟨⟨rfl, htr⟩, hrest⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨htr, hrest⟩

/-! ## 1. Outer Loop with `withLsCodeLoaded lsmpl (withVmPreserved lagrangeCompletePlacedSpec)` -/

theorem lagrangeInterpolateOuterStep_cl_placed_sepWP [LibsignalPlacement]
    {ext : String → Option (State → State)} {ret_pc : BitVec 64}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym
      (withVmPreserved sessionMemcpyRegionSpec))
    (hcomp : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 373) (withLsCodeLoaded lsmpl (withVmPreserved lagrangeCompletePlacedSpec)))
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
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_418).base + 940#64) (hstat : s.status = .Running)
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
      LibsignalCodeLoaded lsmpl sf.mem →
      sf.pc = (blkPl_418).base + 1036#64 → sf.status = .Running → sf.sp = sp0 - 672#64 →
      traceVRegs sf = traceVRegs s → VmPreserved s sf →
      sf.readReg64 .x19 = BitVec.ofNat 64 (i + 1) →
      sf.readReg64 .x20 = s.readReg64 .x20 → sf.readReg64 .x21 = BitVec.ofNat 64 k →
      sf.readReg64 .x22 = s.readReg64 .x22 → sf.readReg64 .x23 = pt_ptr →
      sf.readReg64 .x24 = BitVec.ofNat 64 (2 * (k + 1)) →
      sf.readReg64 .x25 = BitVec.ofNat 64 (k + 1) →
      sf.readReg64 .x26 = ptr_l → sf.readReg64 .x27 = 0#64 - BitVec.ofNat 64 k →
      sf.readReg64 .x28 = BitVec.ofNat 64 i → sf.readReg64 .x29 = sp0 - 96#64 →
      SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc sf
        (gf16SliceAt acc_ptr
            (lagrangeAccumulateCoeffsTotal 0 k outCoeffs
              (lagrangeCompletePure b_init pts_slice i).coefficients) ∗
          gf16SliceAt ptr_l (lagrangeCompletePure b_init pts_slice i).coefficients ∗
          gf16SliceAt ptr_b b_init.coefficients ∗ ptSliceAt pt_ptr pts_slice ∗
          ((sp0 - 656#64) ↦₆₄ acc_ptr) ∗ ((sp0 - 640#64) ↦₆₄ ptr_b) ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          stackAt (sp0 - 672#64) lagrangeCompleteStack ∗ P) post) :
    SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc s
      (gf16SliceAt acc_ptr outCoeffs ∗ gf16SliceAt ptr_l workingCoeffs ∗
        gf16SliceAt ptr_b b_init.coefficients ∗ ptSliceAt pt_ptr pts_slice ∗
        ((sp0 - 656#64) ↦₆₄ acc_ptr) ∗ ((sp0 - 640#64) ↦₆₄ ptr_b) ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        stackAt (sp0 - 672#64) lagrangeCompleteStack ∗ P) post := by
  have hmemcpy : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsρ spqrMemcpySym) (withVmPreserved sessionMemcpyRegionSpec) :=
    spqr_hook_ok_of_mem hmemcpy_sat
  simp only [withVmPreserved, sessionMemcpyRegionSpec] at hmemcpy
  have hcomp' := hcomp
  simp only [withLsCodeLoaded, withVmPreserved, lagrangeCompletePlacedSpec] at hcomp'
  have hinner := @lagrangeAccumulateInner_placed_sepWP _ ext ((blkPl_418).base + 1036#64) acc_ptr ptr_l k
    (lagrangeCompletePure b_init pts_slice i).coefficients hk_pos hk_le
    (by rw [lagrangeCompletePure_length, hb_len]) k 0 outCoeffs
  try dsimp only [BitVec.ofNat_eq_ofNat] at hmemcpy hcomp' hinner hpc hcont ⊢
  have htoNat_b : (BitVec.ofNat 64 (2 * (k + 1))).toNat = (gf16ListBytes b_init.coefficients).length :=
    toNat_two_mul_succ_eq_gf16ListBytes k b_init.coefficients hk_le hb_len
  apply sepWP_seq_lscl hcl (mid := lsmpl.base 373)
  refine SepWP.weaken_pre
    (show _ ⊢ gf16SliceAt ptr_l workingCoeffs ∗ gf16SliceAt ptr_b b_init.coefficients ∗
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
  have h1_len : BitVec.ofNat 64 (k + 1) = BitVec.ofNat 64 b_init.coefficients.length := by rw [hb_len]
  have h3_len : BitVec.ofNat 64 k = BitVec.ofNat 64 pts_slice.length := by rw [hpts_len]
  have hi_pts : i < pts_slice.length := by omega
  have h2_lt : 2 * b_init.coefficients.length < 2 ^ 64 := by omega
  have h4_lt : 4 * pts_slice.length < 2 ^ 64 := by omega
  have hsp_al_s : s.spAligned = true := by
    unfold State.spAligned; rw [hsp, sp672_aligned sp0 hsp0]; rfl
  wp_steps 6
  refine with_vm_cur (s := sf) fun hvm2_step => ?_
  have hvm2 : VmPreserved s _ := hvm1.trans hvm2_step
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_sf])
  intro hcl1
  apply sepWP_seq_lscl hcl1 (mid := (blkPl_418).base + 1036#64)
  wp_call hcomp' ⟨ptr_l, pt_ptr, b_init, pts_slice, i⟩
  wp_conv_pre => rw [hsp_sf, hsp]
  have hvm3 : VmPreserved s sf_1 := hvm2.trans (by assumption)
  wp_steps 2
  refine with_vm_cur (s := sf_1) fun hvm4_step => ?_
  have hvm4 : VmPreserved s _ := hvm3.trans hvm4_step
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (hinner _
      (gf16SliceAt ptr_b b_init.coefficients ∗ ptSliceAt pt_ptr pts_slice ∗
        ((sp0 - 656#64) ↦₆₄ acc_ptr) ∗ ((sp0 - 640#64) ↦₆₄ ptr_b) ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        stackAt (sp0 - 672#64) lagrangeCompleteStack ∗ P)
      _ (by omega) (by omega) hout_len
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_sf_1])
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
      (by simp [wp_norm, arm64_norm, *])
      (fun sf3 hpc3 hstat3 hsp3 htr3 hvm_in _ hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3
        hx25_3 hx26_3 hx27_3 hx28_3 hx29_3 _ => ?_))
  apply SepWP.done hpc3 hstat3
  intro hcl3
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (hcont sf3 hcl3 hpc3 hstat3
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

theorem lagrangeInterpolateOuter_cl_placed_sepWP [LibsignalPlacement]
    {ext : String → Option (State → State)} {ret_pc : BitVec 64}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym
      (withVmPreserved sessionMemcpyRegionSpec))
    (hcomp : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 373) (withLsCodeLoaded lsmpl (withVmPreserved lagrangeCompletePlacedSpec)))
    (sp0 acc_ptr ptr_l ptr_b pt_ptr : BitVec 64)
    (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (k : Nat) (b_init : Poly) (pts_slice : List Pt)
    (hk_pos : 1 ≤ k) (hk_le : k ≤ 65536)
    (hb_len : b_init.coefficients.length = k + 1)
    (hpts_len : pts_slice.length = k) :
    ∀ (rem i : Nat) (outCoeffs workingCoeffs : List GF16)
      (s : State) (P : SepProp) (post : State → SepProp → Prop),
      rem > 0 → i + rem = k → outCoeffs.length = k → workingCoeffs.length = k + 1 →
      LibsignalCodeLoaded lsmpl s.mem →
      s.pc = (blkPl_418).base + 940#64 → s.status = .Running → s.sp = sp0 - 672#64 →
      s.readReg64 .x19 = BitVec.ofNat 64 i → s.readReg64 .x21 = BitVec.ofNat 64 k →
      s.readReg64 .x23 = pt_ptr → s.readReg64 .x24 = BitVec.ofNat 64 (2 * (k + 1)) →
      s.readReg64 .x25 = BitVec.ofNat 64 (k + 1) → s.readReg64 .x26 = ptr_l →
      s.readReg64 .x27 = 0#64 - BitVec.ofNat 64 k → s.readReg64 .x29 = sp0 - 96#64 →
      (∀ sf : State,
        sf.pc = (blkPl_418).base + 1136#64 → sf.status = .Running → sf.sp = sp0 - 672#64 →
        traceVRegs sf = traceVRegs s → VmPreserved s sf →
        sf.readReg64 .x20 = s.readReg64 .x20 → sf.readReg64 .x21 = BitVec.ofNat 64 k →
        sf.readReg64 .x22 = s.readReg64 .x22 → sf.readReg64 .x23 = pt_ptr →
        sf.readReg64 .x24 = BitVec.ofNat 64 (2 * (k + 1)) →
        sf.readReg64 .x25 = BitVec.ofNat 64 (k + 1) →
        sf.readReg64 .x26 = ptr_l → sf.readReg64 .x29 = sp0 - 96#64 →
        SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc sf
          (gf16SliceAt acc_ptr (lagrangeInterpolateLoopTotal b_init pts_slice i rem outCoeffs) ∗
            memRegion ptr_l (2 * (k + 1)) ∗ gf16SliceAt ptr_b b_init.coefficients ∗
            ptSliceAt pt_ptr pts_slice ∗ ((sp0 - 656#64) ↦₆₄ acc_ptr) ∗
            ((sp0 - 640#64) ↦₆₄ ptr_b) ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
            stackAt (sp0 - 672#64) lagrangeCompleteStack ∗ P) post) →
      SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc s
        (gf16SliceAt acc_ptr outCoeffs ∗ gf16SliceAt ptr_l workingCoeffs ∗
          gf16SliceAt ptr_b b_init.coefficients ∗ ptSliceAt pt_ptr pts_slice ∗
          ((sp0 - 656#64) ↦₆₄ acc_ptr) ∗ ((sp0 - 640#64) ↦₆₄ ptr_b) ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          stackAt (sp0 - 672#64) lagrangeCompleteStack ∗ P) post := by
  intro rem
  induction rem using Nat.strongRecOn with
  | ind rem ih =>
    intro i outCoeffs workingCoeffs s P post hrem hsum hout_len hwork_len
      hcl hpc hstat hsp hx19 hx21 hx23 hx24 hx25 hx26 hx27 hx29 hcont
    have hi_lt : i < k := by omega
    refine lagrangeInterpolateOuterStep_cl_placed_sepWP hmemcpy_sat hcomp sp0 acc_ptr ptr_l ptr_b pt_ptr hsp0
      k i b_init pts_slice outCoeffs workingCoeffs hk_pos hk_le hi_lt hb_len hpts_len hout_len hwork_len
      s P post hcl hpc hstat hsp hx19 hx21 hx23 hx24 hx25 hx26 hx27 hx29
      (fun s1 hcl1 hpc1 hstat1 hsp1 htr1 hvm1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 => ?_)
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
        rw [← hlen_w']; exact gf16SliceAt_to_memRegion ptr_l _
      rw [hdone]
      refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left hto_mem)) ?_
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
        (by rw [lagrangeCompletePure_length, hb_len]) hcl1
        (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hstat1])
        (by simp [wp_norm, arm64_norm, hsp1]) (by simp [wp_norm, arm64_norm, hx19_1])
        (by simp [wp_norm, arm64_norm, hx21_1]) (by simp [wp_norm, arm64_norm, hx23_1])
        (by simp [wp_norm, arm64_norm, hx24_1]) (by simp [wp_norm, arm64_norm, hx25_1])
        (by simp [wp_norm, arm64_norm, hx26_1]) (by simp [wp_norm, arm64_norm, hx27_1])
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

/-! ## 2. Iteration `i = 0` and Cache-Miss Sub-Steps -/

theorem lagrangeInterpolate_copyAndComplete0_cl_placed_sepWP [LibsignalPlacement]
    {ext : String → Option (State → State)} {ret_pc : BitVec 64}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym
      (withVmPreserved sessionMemcpyRegionSpec))
    (hcomp : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 373) (withLsCodeLoaded lsmpl (withVmPreserved lagrangeCompletePlacedSpec)))
    (sp0 ptr_l ptr_b pt_ptr x19_slot v664 v640 : BitVec 64)
    (hsp0 : sp0 &&& 0xf#64 = 0#64) (hptr_l_ne : ptr_l ≠ 0#64)
    (k : Nat) (b_init : Poly) (pts_slice : List Pt)
    (_hk_pos : 1 ≤ k) (hk_le : k ≤ 65536)
    (hb_len : b_init.coefficients.length = k + 1) (hpts_len : pts_slice.length = k)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_418).base + 796#64) (hstat : s.status = .Running)
    (hsp : s.sp = sp0 - 672#64)
    (hx0 : s.readReg64 .x0 = ptr_l) (hx19 : s.readReg64 .x19 = x19_slot)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 k) (hx23 : s.readReg64 .x23 = ptr_b)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (2 * (k + 1)))
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 (k + 1))
    (hx27 : s.readReg64 .x27 = pt_ptr) (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hcont : ∀ sf : State,
      LibsignalCodeLoaded lsmpl sf.mem →
      sf.pc = (blkPl_418).base + 848#64 → sf.status = .Running → sf.sp = sp0 - 672#64 →
      traceVRegs sf = traceVRegs s → VmPreserved s sf →
      sf.readReg64 .x20 = s.readReg64 .x20 → sf.readReg64 .x21 = BitVec.ofNat 64 k →
      sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x24 = BitVec.ofNat 64 (2 * (k + 1)) →
      sf.readReg64 .x25 = BitVec.ofNat 64 (k + 1) → sf.readReg64 .x26 = ptr_l →
      sf.readReg64 .x27 = pt_ptr → sf.readReg64 .x29 = sp0 - 96#64 →
      SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc sf
        (gf16SliceAt ptr_l (lagrangeCompletePure b_init pts_slice 0).coefficients ∗
          gf16SliceAt ptr_b b_init.coefficients ∗ ptSliceAt pt_ptr pts_slice ∗
          ((sp0 - 664#64) ↦₆₄ x19_slot) ∗ ((sp0 - 640#64) ↦₆₄ ptr_b) ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          stackAt (sp0 - 672#64) lagrangeCompleteStack ∗ P) post) :
    SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc s
      (memRegion ptr_l (2 * (k + 1)) ∗ gf16SliceAt ptr_b b_init.coefficients ∗
        ptSliceAt pt_ptr pts_slice ∗ ((sp0 - 664#64) ↦₆₄ v664) ∗ ((sp0 - 640#64) ↦₆₄ v640) ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        stackAt (sp0 - 672#64) lagrangeCompleteStack ∗ P) post := by
  have hmemcpy : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsρ spqrMemcpySym) (withVmPreserved sessionMemcpyRegionSpec) :=
    spqr_hook_ok_of_mem hmemcpy_sat
  simp only [withVmPreserved, sessionMemcpyRegionSpec] at hmemcpy
  have hcomp' := hcomp
  simp only [withLsCodeLoaded, withVmPreserved, lagrangeCompletePlacedSpec] at hcomp'
  try dsimp only [BitVec.ofNat_eq_ofNat] at hmemcpy hcomp' hpc hcont ⊢
  have hsp_align : s.sp &&& 15#64 = 0#64 := by rw [hsp]; exact sp672_aligned sp0 hsp0
  have hptr_l_ne0 : (ptr_l == 0#64) = false := beq_eq_false_iff_ne.mpr hptr_l_ne
  have htoNat_b : (BitVec.ofNat 64 (2 * (k + 1))).toNat = (gf16ListBytes b_init.coefficients).length :=
    toNat_two_mul_succ_eq_gf16ListBytes k b_init.coefficients hk_le hb_len
  apply sepWP_seq_lscl hcl (mid := lsmpl.base 373)
  wp_conv_pre =>
    rw [memcpy_memRegion_gf16Slice_pre ptr_l ptr_b b_init.coefficients (2 * (k + 1)) (by omega)]
  refine seq_vm_clean (mid := lsρ spqrMemcpySym)
    (P_mid := memRegion ptr_l (gf16ListBytes b_init.coefficients).length ∗
      (ptr_b ↦ₛ gf16ListBytes b_init.coefficients) ∗ ptSliceAt pt_ptr pts_slice ∗
      ((sp0 - 664#64) ↦₆₄ x19_slot) ∗ ((sp0 - 640#64) ↦₆₄ ptr_b) ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ stackAt (sp0 - 672#64) lagrangeCompleteStack ∗ P)
    (Q := fun s1 =>
      s1.sp = sp0 - 672#64 ∧ s1.readReg64 .x0 = ptr_l ∧ s1.readReg64 .x1 = ptr_b ∧
      s1.readReg64 .x2 = BitVec.ofNat 64 (2 * (k + 1)) ∧ s1.readReg64 .x20 = s.readReg64 .x20 ∧
      s1.readReg64 .x21 = BitVec.ofNat 64 k ∧ s1.readReg64 .x22 = s.readReg64 .x22 ∧
      s1.readReg64 .x24 = BitVec.ofNat 64 (2 * (k + 1)) ∧
      s1.readReg64 .x25 = BitVec.ofNat 64 (k + 1) ∧ s1.readReg64 .x26 = ptr_l ∧
      s1.readReg64 .x27 = pt_ptr ∧ s1.readReg64 .x29 = sp0 - 96#64 ∧
      s1.readReg64 .x30 = (blkPl_418).base + 824#64 ∧ traceVRegs s1 = traceVRegs s) ?_ ?_
  · by_vm_steps (
      wp_steps 7
      exact SepWP.done (by simp [wp_norm, arm64_norm, hptr_l_ne0])
        (by simp [wp_norm, arm64_norm, hstat])
        ⟨by simp [wp_norm, arm64_norm], Entails.of_eq (by sep_ac_rfl),
         by simpa [wp_norm, arm64_norm] using hsp, by simp [wp_norm, arm64_norm, hx0],
         by simp [wp_norm, arm64_norm, hx23], by simp [wp_norm, arm64_norm, hx24],
         by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm, hx21],
         by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm, hx24],
         by simp [wp_norm, arm64_norm, hx25], by simp [wp_norm, arm64_norm, hx0],
         by simp [wp_norm, arm64_norm, hx27], by simp [wp_norm, arm64_norm, hx29],
         by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm]⟩)
  · rintro s1 hpc1 hstat1 hvm1 ⟨hsp1, hx0_1, hx1_1, hx2_1, hx20_1, hx21_1, hx22_1,
      hx24_1, hx25_1, hx26_1, hx27_1, hx29_1, hx30_1, htr1⟩
    simp only [traceVRegs, Prod.mk.injEq] at htr1
    have hsp1_al : s1.spAligned = true := by
      unfold State.spAligned; rw [hsp1, sp672_aligned sp0 hsp0]; rfl
    wp_call hmemcpy ⟨ptr_l, ptr_b, gf16ListBytes b_init.coefficients⟩
    wp_conv_pre =>
      rw [← gf16SliceAt_eq_pointsToBytes b_init.coefficients ptr_l,
          ← gf16SliceAt_eq_pointsToBytes b_init.coefficients ptr_b]
    have hvm2 : VmPreserved s sf := hvm1.trans (by assumption)
    have h1_len : BitVec.ofNat 64 (k + 1) = BitVec.ofNat 64 b_init.coefficients.length := by rw [hb_len]
    have h3_len : BitVec.ofNat 64 k = BitVec.ofNat 64 pts_slice.length := by rw [hpts_len]
    have h0_pts : 0 < pts_slice.length := by omega
    have h2_lt : 2 * b_init.coefficients.length < 2 ^ 64 := by omega
    have h4_lt : 4 * pts_slice.length < 2 ^ 64 := by omega
    wp_steps 6
    refine with_vm_cur (s := sf) fun hvm3_step => ?_
    have hvm3 : VmPreserved s _ := hvm2.trans hvm3_step
    apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_sf])
    intro hcl1
    apply sepWP_seq_lscl hcl1 (mid := (blkPl_418).base + 848#64)
    wp_call hcomp' ⟨ptr_l, pt_ptr, b_init, pts_slice, 0⟩
    wp_conv_pre => rw [hsp_sf, hsp1]
    have hvm4 : VmPreserved s sf_1 := hvm3.trans (by assumption)
    apply SepWP.done hpc_sf_1 hrun_sf_1
    intro hcl2
    refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hcont sf_1 hcl2 hpc_sf_1 hrun_sf_1 (by rw [hsp_sf_1, hsp_sf, hsp1])
        (by simp [traceVRegs, wp_norm, arm64_norm, *]) hvm4
        (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
        (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
        (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
        (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *]))

theorem lagrangeInterpolate_copyFirstAcc_cl_placed_sepWP [LibsignalPlacement]
    {ext : String → Option (State → State)} {ret_pc : BitVec 64}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym
      (withVmPreserved sessionMemcpyRegionSpec))
    (hcomp : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 373) (withLsCodeLoaded lsmpl (withVmPreserved lagrangeCompletePlacedSpec)))
    (sp0 acc_ptr ptr_l ptr_b pt_ptr v152 : BitVec 64) (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (k : Nat) (b_init : Poly) (pts_slice : List Pt)
    (hk_pos : 1 ≤ k) (hk_le : k ≤ 65536)
    (hb_eq : b_init = lagrangePreparePure pts_slice) (hpts_len : pts_slice.length = k)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_418).base + 848#64) (hstat : s.status = .Running)
    (hsp : s.sp = sp0 - 672#64)
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
  have houter := @lagrangeInterpolateOuter_cl_placed_sepWP _ ext ret_pc hmemcpy_sat hcomp
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
  apply sepWP_seq_lscl hcl (mid := (blkPl_418).base + 908#64)
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
  apply SepWP.done hpc_sf hrun_sf
  intro hcl_sf
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
    refine seq_vm_lscl hcl_sf (mid := (blkPl_418).base + 940#64)
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
    · rintro s1 hcl_s1 hpc1 hrun1 hvm3 ⟨hsp1, htr1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1,
        hx24_1, hx25_1, hx26_1, hx27_1, hx29_1⟩
      refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (houter (k - 1) 1 (working0.coefficients.drop 1) working0.coefficients s1
          (((sp0 - 152#64) ↦₆₄ BitVec.ofNat 64 k) ∗ P) post (by omega) (by omega)
          (by rw [List.length_drop, hw0_len]; omega) hw0_len hcl_s1
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

theorem lagrangeInterpolate_miss_prepare_cl_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {target_pc : BitVec 64}
    (hprep : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 372) (withLsCodeLoaded lsmpl (lagrangePreparePlacedSpec M A lim)))
    (sp0 acc_ptr pt_ptr v168 v160 v152 : BitVec 64) (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (k : Nat) (pts_slice : List Pt) (hk_pos : 1 ≤ k) (hk_le : k ≤ 65536)
    (hpts_len : pts_slice.length = k)
    (st : M.σ) (hfit : FitsEvents M lim st (rustAllocEvents (2 * (k + 1)) 2))
    (s0 s : State) (F : SepProp) (post : State → SepProp → Prop)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
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
  have hprep' := subroutine_ok_lagrangePrepare_cl_fixed hprep
  simp only [withLsCodeLoaded, lagrangePrepareFixedSpec, lagrangePreparePlacedSpec] at hprep'
  rcases Prod.mk.inj htr with ⟨htr_tr, htr_vr⟩
  have hsp_al_s : s.spAligned = true := by
    unfold State.spAligned; rw [hsp, sp672_aligned sp0 hsp0]; rfl
  let a : LagrangePrepareArgs := {
    out := sp0 - 144#64, ptsPtr := pt_ptr, pts := pts_slice, hlen_bound := by omega
  }
  have hfit_env : FitsEnv M lim st (LagrangePrepareEnv a) :=
    FitsEnv.eq_iff.mpr (by simpa [LagrangePrepareEnv, a, hpts_len] using hfit)
  try dsimp only [BitVec.ofNat_eq_ofNat] at hprep' hpc hnext ⊢
  refine seq_vm_lscl hcl (mid := lsmpl.base 372)
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
  · rintro s1 hcl1 hpc1 hstat1 hvm1 ⟨hsp1, hx0_1, hx1_1, hx2_1, hx19_1, hx20_1, hx21_1, hx22_1,
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

theorem lagrangeInterpolate_miss_prepare_cl_placed_wpp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {target_pc : BitVec 64}
    (hprep : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 372) (withLsCodeLoaded lsmpl (lagrangePreparePlacedSpec M A lim)))
    (sp0 acc_ptr pt_ptr v168 v160 v152 : BitVec 64) (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (k : Nat) (pts_slice : List Pt) (hk_pos : 1 ≤ k) (hk_le : k ≤ 65536)
    (hpts_len : pts_slice.length = k)
    (st : M.σ) (hfit : FitsEvents M lim st (rustAllocEvents (2 * (k + 1)) 2))
    (s0 s : State) (F : SepProp) (Q Qp : State → SepProp → Prop)
    (oom : State → SepProp := fun _ => ⌜False⌝)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
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
      SepWPp ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) target_pc sf
        (((sp0 - 168#64) ↦₆₄ BitVec.ofNat 64 k) ∗ ((sp0 - 160#64) ↦₆₄ acc_ptr) ∗
          ((sp0 - 152#64) ↦₆₄ 0#64) ∗ ((sp0 - 144#64) ↦₆₄ b_cap) ∗
          ((sp0 - 136#64) ↦₆₄ ptr_b) ∗ ((sp0 - 128#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗
          A.live ptr_b (b_cap.toNat * 2) 2 ∗
          gf16SliceAt ptr_b (lagrangePreparePure pts_slice).coefficients ∗
          memRegion (ptr_b + BitVec.ofNat 64 ((lagrangePreparePure pts_slice).coefficients.length * 2))
            ((b_cap.toNat - (lagrangePreparePure pts_slice).coefficients.length) * 2) ∗
          ptSliceAt pt_ptr pts_slice ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
          A.pool lim (M.stepEvents (rustAllocEvents (2 * (k + 1)) 2) st) sf ∗
          stackAt (sp0 - 672#64) lagrangePrepareStack ∗ F) Q Qp oom) :
    SepWPp ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) target_pc s
      (((sp0 - 168#64) ↦₆₄ v168) ∗ ((sp0 - 160#64) ↦₆₄ v160) ∗ ((sp0 - 152#64) ↦₆₄ v152) ∗
        memRegion (sp0 - 144#64) 24 ∗ ptSliceAt pt_ptr pts_slice ∗
        reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool lim st s ∗
        stackAt (sp0 - 672#64) lagrangePrepareStack ∗ F) Q Qp oom := by
  apply SepWPp.of_sepWP (mid := (blkPl_418).base + 760#64)
  refine SepWP.mono (oom := fun _ => ⌜False⌝) ?_ (fun _ _ _ _ hp => hp)
  refine lagrangeInterpolate_miss_prepare_cl_placed_sepWP hprep sp0 acc_ptr pt_ptr v168 v160 v152
    hsp0 k pts_slice hk_pos hk_le hpts_len st hfit s0 s F _ hcl hpc hstat hsp htr hx0 hx21 hx27
    hx29 ?_
  intro b_cap ptr_b sf hge hlt hne hpc_f hrun_f hsp_f htr_f hx19_f hx20_f hx21_f hx22_f hx24_f
    hx27_f hx29_f
  exact SepWP.done hpc_f hrun_f
    (hnext b_cap ptr_b sf hge hlt hne hpc_f hrun_f hsp_f htr_f hx19_f hx20_f hx21_f hx22_f
      hx24_f hx27_f hx29_f)

end LibsignalBinary.Proofs.SpqrV1.States.Leaves.DecodedMsgCl1PlacedBudgetAux

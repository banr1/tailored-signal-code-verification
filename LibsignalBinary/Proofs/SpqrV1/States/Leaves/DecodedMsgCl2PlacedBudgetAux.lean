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
public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.Loop
public import LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.MainLoop
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.MainLoopPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DecodedMsgCl1PlacedBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlaced
import ProofLib.SepLogic.WPp

/-!
# `<PolyDecoder as Decoder>::decoded_message` (Block `418`): `withLsCodeLoaded` `RustCliAllocBudget` Main Loop

Verifies the per-iteration `compute_at` / interpolation step (`decodedMessage_computeAtStep_cl_placed_*`)
and main evaluation loop (`decodedMessageLoop_cl_placed_*`) of `<PolyDecoder as Decoder>::decoded_message`
(Block `418`) under `RustCliAllocBudget M` and `LibsignalCodeLoaded lsmpl`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.Leaves.DecodedMsgCl2PlacedBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkPC_418 blkPl_418 lsmpl withLsCodeLoaded)
open CryptoVerification.SpqrV1.States.Leaves (sepWP_seq_lscl)
open scoped CryptoVerification.CodeLayout CryptoVerification.SpqrV1.Poly
  CryptoVerification.SpqrV1.Poly.AddChunk CryptoVerification.SpqrV1.Poly.AddChunk.AddChunkNorm
open CryptoVerification.LibsignalSessionRepr (VecPin)
open CryptoVerification.LibsignalSpqrV1 (GF16 Poly PolyDecoder u16ToBeBytes)
open CryptoVerification.LibsignalTripleRatchet (sessionMemcpyRegionSpec sessionShimSpec)
open CryptoVerification.SpqrV1.Alloc
  (spqrMemcpySym spqrRustAllocSym spqrRustNoAllocShimSym)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Poly (gf16SliceAt ptSliceAt sortedSetPtListPinAt)
open CryptoVerification.SpqrV1.Poly.AddChunk
  (PolyDecoderStrictSorted bsearchLoop bsearchLoop_bounds ptSliceAt_split_take_drop)
open CryptoVerification.SpqrV1.Poly.AddChunk.AddChunkNorm
  (readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre readReg64_setPC_pre
   readReg_setMem_setPC_pre readReg_setPC_pre sp_setMem_setPC_pre sp_setPC_pre)
open CryptoVerification.SpqrV1.Poly.ComputeAt (ComputeAtArgs computeAtPure computeAtStack)
open CryptoVerification.SpqrV1.Poly.DecodedMessage
  (bv64_and15_ofNat bv64_bne_ofNat bv64_lsr4_truncate16_ofNat bv64_ofNat_mul2_comm
   bv64_ofNat_one_add_mul2 bv64_orr_w0_truncate8 bv64_ubfx_8_8_truncate8 bv64_umaddl24_mod16
   collectedSlices decodedMessageLoopTotal decodedMessageLoopTotal_step_found
   decodedMessageLoopTotal_step_not_found interpolateScratchAt lagrangeInterpolateTotal
   necessaryPoints_pos_of_lt optPolyCacheListAt optPolyCacheListAt_focus optPolyCacheListAt_set
   optPolyCacheSlotAt polyDecoderStrictSorted_elem_length_le ptSliceRefAt
   ptSliceRefListAt ptSliceRefListAt_focus sortedSetPtListPinAt_focus sortedSetPtPinAt_eq_slice
   sortedSetPtPinRest sp672_aligned sp96_sub104 sp96_sub112 sp96_sub120 spqrRustDeallocSym
   stackAt_computeAt_eq_prepare traceVRegs)
open CryptoVerification.SpqrV1.Poly.LagrangeComplete (lagrangeCompletePlacedSpec)
open CryptoVerification.SpqrV1.Poly.LagrangePrepare (lagrangePrepareStack)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
   rustCliAllocBudgetSpec rustCliDeallocBudgetSpec)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.DefsBudget
  (ComputeAtEnv computeAtEvents computeAtPlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget
  (ComputeAtCallEnv DecodedMessageLoopEnv LagrangeInterpolateInlinedEnv)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.MainLoopPlacedBudgetAux
  (computeAtEvents_mem_callEnv decodedMessageLoopEnv_not_found_split
   decodedMessageLoopEnv_step_found decodedMessage_bsearchStep_placed_sepWP
   decodedMessage_pushTwoBytes_placed_sepWP fitsEvents_of_fitsEnv_computeAtCall)
open LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.DefsBudget (lagrangePreparePlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.DecodedMsgCl1PlacedBudget
  (lagrangeInterpolate_inlined_cl_placed_sepWP)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
  sp96_sub120 sp96_sub112 sp96_sub104
  bv64_and15_ofNat bv64_umaddl24_mod16
  bv64_ofNat_mul2_comm bv64_ofNat_one_add_mul2

theorem decodedMessage_computeAtStep_cl_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {target_pc : BitVec 64}
    (hcomp_at : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 371) (withLsCodeLoaded lsmpl (computeAtPlacedSpec M A lim)))
    (sp0 slot : BitVec 64) (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (i ptsNeeded : Nat) (p : Poly)
    (hi_lt : i < ptsNeeded) (hneed_le : ptsNeeded ≤ 16 * 65536)
    (st : M.σ) (hfit : FitsEnv M lim st (ComputeAtCallEnv p.coefficients.length))
    (s0 s : State) (F : SepProp) (post : State → SepProp → Prop)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_418).base + 1284#64)
    (hstat : s.status = .Running)
    (hsp : s.sp = sp0 - 672#64)
    (htr : traceVRegs s = traceVRegs s0)
    (hx19 : s.readReg64 .x19 = slot)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 i)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      ComputeAtCallEnv p.coefficients.length evs →
      sf.pc = (blkPl_418).base + 1328#64 →
      sf.status = .Running →
      sf.sp = sp0 - 672#64 →
      traceVRegs sf = traceVRegs s0 →
      BitVec.truncate 8 (sf.readReg64 .x19) =
        BitVec.truncate 8 ((computeAtPure p (GF16.new (BitVec.ofNat 16 (i / 16)))).value >>> 8) →
      BitVec.truncate 8 (sf.readReg64 .x21) =
        BitVec.truncate 8 (computeAtPure p (GF16.new (BitVec.ofNat 16 (i / 16)))).value →
      sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x22 = BitVec.ofNat 64 i →
      sf.readReg64 .x23 = BitVec.ofNat 64 (2 * i) →
      sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x29 = sp0 - 96#64 →
      SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) target_pc sf
        (optPolyCacheSlotAt A.repAlloc slot (some p) ∗
          ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗
          ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
          reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (sp0 - 672#64) computeAtStack ∗ F)
        post) :
    SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) target_pc s
      (optPolyCacheSlotAt A.repAlloc slot (some p) ∗
        ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗
        ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
        reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool lim st s ∗
        stackAt (sp0 - 672#64) computeAtStack ∗ F)
      post := by
  rcases Prod.mk.inj htr with ⟨htr_tr, htr_vr⟩
  try dsimp only [BitVec.ofNat_eq_ofNat] at hpc hnext ⊢
  have hslot16 : slot + 8#64 + 8#64 = slot + 16#64 := by bv_omega
  have h2i_ne : (BitVec.ofNat 64 (2 * i) != BitVec.ofNat 64 (2 * ptsNeeded)) = true := by
    rw [bv64_bne_ofNat (by omega) (by omega), decide_eq_true_eq]; omega
  have hfits_ev := fitsEvents_of_fitsEnv_computeAtCall hfit
  unfold optPolyCacheSlotAt
  rw [sepExists_sepConj_left]; apply SepWP.exists_elim; intro ptr_p
  rw [sepConj_assoc]; apply SepWP.pure_elim; rintro ⟨hp_ge1, hp_le, hptr_p_ne⟩
  apply sepWP_seq_lscl hcl (mid := lsmpl.base 371)
  wp_steps 3
  refine SepWP.transport_budgetPool ?_ (hnext := ?_)
  · simp [wp_norm, arm64_norm]
  refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hstat]) fun hcl_call => ?_
  let a : ComputeAtArgs := {
    p_coeffs := ptr_p
    poly := p
    x := GF16.new (BitVec.ofNat 16 (i / 16))
  }
  refine SepWP.call_subroutine_frame (x := (a, st)) (ret_pc := (blkPl_418).base + 1296#64)
    (F := (slot ↦₆₄ BitVec.ofNat 64 p.coefficients.length) ∗
      ((slot + 8#64) ↦₆₄ ptr_p) ∗
      ((slot + 16#64) ↦₆₄ BitVec.ofNat 64 p.coefficients.length) ∗
      A.live ptr_p (2 * p.coefficients.length) 2 ∗
      ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗
      ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗ F)
    hcomp_at
    (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, hstat])
    (by
      unfold State.spAligned
      simp only [wp_norm, arm64_norm, hsp, sp672_aligned sp0 hsp0])
    (by simp [wp_norm, arm64_norm])
    (fun R' hm => ?_)
    (fun R' sf _ hm => ?_)
    (fun R' code sf _ hex => ?_)
    (fun sf_c hpc_c hrun_c hsp_c hcs_c => ?_)
  · have hx2_trunc :
        BitVec.truncate 16 ((BitVec.ofNat 64 i) >>> 4) =
          (GF16.new (BitVec.ofNat 16 (i / 16))).value :=
      bv64_lsr4_truncate16_ofNat (by omega)
    dsimp only [withLsCodeLoaded, computeAtPlacedSpec, a]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl_call, ?_⟩
    simp only [wp_norm, arm64_norm, hsp, sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx2_trunc, by omega, hfits_ev⟩,
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm⟩
  · dsimp only [withLsCodeLoaded, computeAtPlacedSpec] at hm
    exact not_satisfies_false_sepConj hm
  · dsimp only [withLsCodeLoaded, computeAtPlacedSpec, Spec.onExit] at hex
    exact not_satisfies_false_sepConj hex
  · conv => arg 4; dsimp only [withLsCodeLoaded, computeAtPlacedSpec, a]; simp only [wp_norm, arm64_norm, htr_tr, hsp]
    rcases hcs_c with ⟨_, hx20_c, _, hx22_c, _, hx24_c, hx25_c, hx26_c, _, _, hx29_c, hvregs_c⟩
    apply SepWP.pure_elim; rintro ⟨htr_c, hx0_c⟩
    have hsp_c' : sf_c.sp = sp0 - 672#64 := by simpa [wp_norm, arm64_norm, hsp] using hsp_c
    have hx20_c' : sf_c.readReg64 .x20 = s.readReg64 .x20 := by
      simpa [wp_norm, arm64_norm] using hx20_c
    have hx22_c' : sf_c.readReg64 .x22 = BitVec.ofNat 64 i := by
      simpa [wp_norm, arm64_norm, hx22] using hx22_c
    have hx24_c' : sf_c.readReg64 .x24 = s.readReg64 .x24 := by
      simpa [wp_norm, arm64_norm] using hx24_c
    have hx25_c' : sf_c.readReg64 .x25 = s.readReg64 .x25 := by
      simpa [wp_norm, arm64_norm] using hx25_c
    have hx26_c' : sf_c.readReg64 .x26 = s.readReg64 .x26 := by
      simpa [wp_norm, arm64_norm] using hx26_c
    have hx29_c' : sf_c.readReg64 .x29 = sp0 - 96#64 := by
      simpa [wp_norm, arm64_norm, hx29] using hx29_c
    wp_steps 6
    refine SepWP.transport_budgetPool ?_ (hnext := ?_)
    · simp [wp_norm, arm64_norm]
    refine SepWP.weaken_pre ?_
      (hnext _ (computeAtEvents p.coefficients.length) (computeAtEvents_mem_callEnv _)
        (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hrun_c])
        (by simp [wp_norm, arm64_norm, hsp_c'])
        (by simp [traceVRegs, wp_norm, arm64_norm, htr_c, hvregs_c, htr_vr])
        (by simp only [wp_norm, arm64_norm]; exact bv64_ubfx_8_8_truncate8 hx0_c)
        (by simp only [wp_norm, arm64_norm]; exact bv64_orr_w0_truncate8 hx0_c)
        (by simp [wp_norm, arm64_norm, hx20_c'])
        (by simp [wp_norm, arm64_norm, hx22_c'])
        (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hx24_c'])
        (by simp [wp_norm, arm64_norm, hx25_c'])
        (by simp [wp_norm, arm64_norm, hx26_c'])
        (by simp [wp_norm, arm64_norm, hx29_c']))
    dsimp only [optPolyCacheSlotAt, RustCliAllocBudget.repAlloc_live]
    refine Entails.trans ?_
      (sepConj_mono_left
        (Entails.sepExists_right ptr_p
          (Entails.pure_right ⟨hp_ge1, hp_le, hptr_p_ne⟩ (Entails.of_eq rfl))))
    exact Entails.of_eq (by sep_ac_rfl)

theorem decodedMessage_computeAtStep_cl_placed_wpp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {target_pc : BitVec 64}
    (hcomp_at : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 371) (withLsCodeLoaded lsmpl (computeAtPlacedSpec M A lim)))
    (sp0 slot : BitVec 64) (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (i ptsNeeded : Nat) (p : Poly)
    (hi_lt : i < ptsNeeded) (hneed_le : ptsNeeded ≤ 16 * 65536)
    (st : M.σ) (hfit : FitsEnv M lim st (ComputeAtCallEnv p.coefficients.length))
    (s0 s : State) (F : SepProp)
    (Q Qp : State → SepProp → Prop) (oom : State → SepProp := fun _ => ⌜False⌝)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_418).base + 1284#64)
    (hstat : s.status = .Running)
    (hsp : s.sp = sp0 - 672#64)
    (htr : traceVRegs s = traceVRegs s0)
    (hx19 : s.readReg64 .x19 = slot)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 i)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      ComputeAtCallEnv p.coefficients.length evs →
      sf.pc = (blkPl_418).base + 1328#64 →
      sf.status = .Running →
      sf.sp = sp0 - 672#64 →
      traceVRegs sf = traceVRegs s0 →
      BitVec.truncate 8 (sf.readReg64 .x19) =
        BitVec.truncate 8 ((computeAtPure p (GF16.new (BitVec.ofNat 16 (i / 16)))).value >>> 8) →
      BitVec.truncate 8 (sf.readReg64 .x21) =
        BitVec.truncate 8 (computeAtPure p (GF16.new (BitVec.ofNat 16 (i / 16)))).value →
      sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x22 = BitVec.ofNat 64 i →
      sf.readReg64 .x23 = BitVec.ofNat 64 (2 * i) →
      sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x29 = sp0 - 96#64 →
      SepWPp ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) target_pc sf
        (optPolyCacheSlotAt A.repAlloc slot (some p) ∗
          ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗
          ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
          reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (sp0 - 672#64) computeAtStack ∗ F)
        Q Qp oom) :
    SepWPp ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) target_pc s
      (optPolyCacheSlotAt A.repAlloc slot (some p) ∗
        ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * ptsNeeded)) ∗
        ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
        reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool lim st s ∗
        stackAt (sp0 - 672#64) computeAtStack ∗ F)
      Q Qp oom := by
  apply SepWPp.of_sepWP (mid := (blkPl_418).base + 1328#64)
  refine SepWP.mono (oom := fun _ => ⌜False⌝) ?_ (fun _ _ _ _ hp => hp)
  refine decodedMessage_computeAtStep_cl_placed_sepWP hcomp_at sp0 slot hsp0 i ptsNeeded p
    hi_lt hneed_le st hfit s0 s F _ hcl hpc hstat hsp htr hx19 hx22 hx29 ?_
  intro sf evs hevs hpc_f hrun_f hsp_f htr_f hx19_f hx21_f hx20_f hx22_f hx23_f hx24_f hx25_f
    hx26_f hx29_f
  exact SepWP.done hpc_f hrun_f
    (hnext sf evs hevs hpc_f hrun_f hsp_f htr_f hx19_f hx21_f hx20_f hx22_f hx23_f hx24_f hx25_f
      hx26_f hx29_f)

theorem decodedMessageLoop_cl_placed_sepWP [LibsignalPlacement]
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
      (lsmpl.base 372) (withLsCodeLoaded lsmpl (lagrangePreparePlacedSpec M A lim)))
    (hcomp : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 373) (withLsCodeLoaded lsmpl (withVmPreserved lagrangeCompletePlacedSpec)))
    (hcomp_at : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 371) (withLsCodeLoaded lsmpl (computeAtPlacedSpec M A lim)))
    (dec : PolyDecoder) (sp0 pts_base pts_vec_ptr out_ptr : BitVec 64)
    (pins : List VecPin)
    (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (hpts : dec.pts.length = 16) (hpins : pins.length = 16)
    (hsort : PolyDecoderStrictSorted dec)
    (hneed_le : dec.ptsNeeded ≤ 16 * 65536)
    (hall_ge : ∀ k (hk : k < 16), dec.necessaryPoints k ≤ (dec.pts[k]'(by omega)).vec.length)
    (s0 : State) (F : SepProp) (post : State → SepProp → Prop) :
    ∀ (rem i : Nat) (polys : List (Option Poly)) (out : List (BitVec 8)) (st : M.σ) (s : State),
      FitsEnv M lim st (DecodedMessageLoopEnv dec (collectedSlices dec 0 16) i (rem + 1) polys) →
      i + (rem + 1) = dec.ptsNeeded →
      polys.length = 16 →
      out.length = 2 * i →
      LibsignalCodeLoaded lsmpl s.mem →
      s.pc = (blkPl_418).base + 548#64 →
      s.status = .Running →
      s.sp = sp0 - 672#64 →
      traceVRegs s = traceVRegs s0 →
      s.readReg64 .x20 = pts_base →
      s.readReg64 .x22 = BitVec.ofNat 64 i →
      s.readReg64 .x23 = BitVec.ofNat 64 (2 * i) →
      s.readReg64 .x24 = BitVec.ofNat 64 dec.ptsNeeded →
      s.readReg64 .x25 = 24#64 →
      s.readReg64 .x26 = sp0 - 600#64 →
      s.readReg64 .x29 = sp0 - 96#64 →
      (∀ (sf : State) (evs : List AllocEvent),
        DecodedMessageLoopEnv dec (collectedSlices dec 0 16) i (rem + 1) polys evs →
        sf.pc = (blkPl_418).base + 1404#64 →
        sf.status = .Running →
        sf.sp = sp0 - 672#64 →
        traceVRegs sf = traceVRegs s0 →
        sf.readReg64 .x29 = sp0 - 96#64 →
        let (polysFinal, outFinal) :=
          decodedMessageLoopTotal dec (collectedSlices dec 0 16) i (rem + 1) polys out
        SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) target_pc sf
          (optPolyCacheListAt A.repAlloc (sp0 - 600#64) polysFinal ∗
            ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
            ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
            ((sp0 - 608#64) ↦₆₄ 16#64) ∗
            ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗
            ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
            ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗
            ptSliceRefListAt dec 0 pts_vec_ptr pins ∗
            sortedSetPtListPinAt A.repAlloc pts_base pins dec.pts ∗
            (out_ptr ↦ₛ outFinal) ∗
            interpolateScratchAt sp0 ∗
            reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool lim (M.stepEvents evs st) sf ∗
            stackAt (sp0 - 672#64) computeAtStack ∗ F)
          post) →
      SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) target_pc s
        (optPolyCacheListAt A.repAlloc (sp0 - 600#64) polys ∗
          ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
          ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
          ((sp0 - 608#64) ↦₆₄ 16#64) ∗
          ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗
          ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
          ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
          ptSliceRefListAt dec 0 pts_vec_ptr pins ∗
          sortedSetPtListPinAt A.repAlloc pts_base pins dec.pts ∗
          (out_ptr ↦ₛ out) ∗
          memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (2 * (dec.ptsNeeded - i)) ∗
          interpolateScratchAt sp0 ∗
          reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool lim st s ∗
          stackAt (sp0 - 672#64) computeAtStack ∗ F)
        post
  | rem, i, polys, out, st, s, hfit, hsum, hpolys_len, hout_len,
      hcl, hpc, hstat, hsp, htr, hx20, hx22, hx23, hx24, hx25, hx26, hx29, hnext => by
    have hi_lt : i < dec.ptsNeeded := by omega
    have hpoly_lt : i % 16 < 16 := Nat.mod_lt i (by decide)
    have hpoly_pts : i % 16 < dec.pts.length := by omega
    have hpoly_pins : i % 16 < pins.length := by omega
    have hpoly_p : i % 16 < polys.length := by omega
    have hnec_pos : 1 ≤ dec.necessaryPoints (i % 16) := necessaryPoints_pos_of_lt dec hi_lt
    have hnec_le_len : dec.necessaryPoints (i % 16) ≤ (dec.pts[i % 16]'hpoly_pts).vec.length :=
      hall_ge (i % 16) hpoly_lt
    have hle_len : (dec.pts[i % 16]'hpoly_pts).vec.length ≤ 65536 :=
      polyDecoderStrictSorted_elem_length_le hsort hpoly_pts
    have hge_len : 1 ≤ (dec.pts[i % 16]'hpoly_pts).vec.length := by omega
    have ⟨_, hb_lt0⟩ := bsearchLoop_bounds (dec.pts[i % 16]'hpoly_pts).vec
      (BitVec.ofNat 16 (i / 16)) 0 (dec.pts[i % 16]'hpoly_pts).vec.length hge_len (by omega)
    have hb_lt : bsearchLoop (dec.pts[i % 16]'hpoly_pts).vec (BitVec.ofNat 16 (i / 16)) 0
        (dec.pts[i % 16]'hpoly_pts).vec.length < (dec.pts[i % 16]'hpoly_pts).vec.length := by
      omega
    cases hfound :
      ((dec.pts[i % 16]'hpoly_pts).vec[bsearchLoop (dec.pts[i % 16]'hpoly_pts).vec
        (BitVec.ofNat 16 (i / 16)) 0 (dec.pts[i % 16]'hpoly_pts).vec.length]'hb_lt).x.value ==
        BitVec.ofNat 16 (i / 16)
    ·
      apply sepWP_seq_lscl hcl (mid := (blkPl_418).base + 660#64)
      refine SepWP.weaken_pre ?_
        (decodedMessage_bsearchStep_placed_sepWP (ext := ext) (A := A.repAlloc)
          dec sp0 pts_base pins i hpts hpins hi_lt hneed_le hge_len hle_len
          s
          (optPolyCacheListAt A.repAlloc (sp0 - 600#64) polys ∗
            ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
            ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
            ((sp0 - 608#64) ↦₆₄ 16#64) ∗
            ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
            ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
            ptSliceRefListAt dec 0 pts_vec_ptr pins ∗
            (out_ptr ↦ₛ out) ∗
            memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (2 * (dec.ptsNeeded - i)) ∗
            interpolateScratchAt sp0 ∗
            reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool lim st s ∗
            stackAt (sp0 - 672#64) computeAtStack ∗ F)
          _ hpc hstat hx20 hx22 hx23 hx24 hx25 hx26 hx29 ?_ ?_)
      · exact Entails.of_eq (by sep_ac_rfl)
      · dsimp only
        intro _ htrue
        rw [hfound] at htrue
        cases htrue
      · dsimp only
        intro _ hnot_found s1 hpc1 hrun1 hsp1 htr1 hvm1 hx0_1 hx20_1 hx22_1 hx24_1 hx25_1 hx26_1
          hx29_1
        conv => arg 4; rw [← A.pool_of_vmPreserved hvm1]
        have hstep_pure := decodedMessageLoopTotal_step_not_found dec hpts hsort hpolys_len
          (rem := rem) (out := out) rfl hb_lt hnot_found
        obtain ⟨hfit_interp, hsplit_env⟩ :=
          decodedMessageLoopEnv_not_found_split dec hpts hsort hpolys_len rfl hb_lt hnot_found hfit
        let ptsSlice := (dec.pts[i % 16]'hpoly_pts).vec.take (dec.necessaryPoints (i % 16))
        let pInterp := (polys[i % 16]'hpoly_p).getD (lagrangeInterpolateTotal ptsSlice)
        let yInterp := computeAtPure pInterp (GF16.new (BitVec.ofNat 16 (i / 16)))
        have hslice_len : ptsSlice.length = dec.necessaryPoints (i % 16) :=
          List.length_take_of_le hnec_le_len
        have hk_pos : 1 ≤ ptsSlice.length := by rw [hslice_len]; exact hnec_pos
        have hk_le : ptsSlice.length ≤ 65536 := by rw [hslice_len]; omega
        have hfocus_pre :
            sortedSetPtListPinAt A.repAlloc pts_base pins dec.pts ∗
              ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗
              (optPolyCacheListAt A.repAlloc (sp0 - 600#64) polys ∗
                ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
                ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
                ((sp0 - 608#64) ↦₆₄ 16#64) ∗
                ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
                ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
                ptSliceRefListAt dec 0 pts_vec_ptr pins ∗
                (out_ptr ↦ₛ out) ∗
                memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (2 * (dec.ptsNeeded - i)) ∗
                interpolateScratchAt sp0 ∗
                reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool lim st s1 ∗
                stackAt (sp0 - 672#64) computeAtStack ∗ F) =
            optPolyCacheSlotAt A.repAlloc ((sp0 - 600#64) + BitVec.ofNat 64 (24 * (i % 16)))
                (polys[i % 16]'hpoly_p) ∗
              ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
              ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
              ((sp0 - 608#64) ↦₆₄ 16#64) ∗
              ptSliceRefAt (pts_vec_ptr + BitVec.ofNat 64 (16 * (i % 16)))
                (pins[i % 16]'hpoly_pins).ptr ptsSlice.length ∗
              ptSliceAt (pins[i % 16]'hpoly_pins).ptr ptsSlice ∗
              interpolateScratchAt sp0 ∗
              reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool lim st s1 ∗
              stackAt (sp0 - 672#64) lagrangePrepareStack ∗
              (optPolyCacheListAt A.repAlloc (sp0 - 600#64) (polys.take (i % 16)) ∗
                optPolyCacheListAt A.repAlloc
                  ((sp0 - 600#64) + BitVec.ofNat 64 (24 * (i % 16 + 1))) (polys.drop (i % 16 + 1)) ∗
                ptSliceRefListAt dec 0 pts_vec_ptr (pins.take (i % 16)) ∗
                ptSliceRefListAt dec (i % 16 + 1)
                  (pts_vec_ptr + BitVec.ofNat 64 (16 * (i % 16 + 1))) (pins.drop (i % 16 + 1)) ∗
                sortedSetPtListPinAt A.repAlloc pts_base (pins.take (i % 16))
                  (dec.pts.take (i % 16)) ∗
                ((pts_base + BitVec.ofNat 64 (24 * (i % 16))) ↦₆₄ (pins[i % 16]'hpoly_pins).cap) ∗
                ((pts_base + BitVec.ofNat 64 (24 * (i % 16)) + 8#64) ↦₆₄
                  (pins[i % 16]'hpoly_pins).ptr) ∗
                ((pts_base + BitVec.ofNat 64 (24 * (i % 16)) + 16#64) ↦₆₄
                  BitVec.ofNat 64 (dec.pts[i % 16]'hpoly_pts).vec.length) ∗
                ptSliceAt
                  ((pins[i % 16]'hpoly_pins).ptr + BitVec.ofNat 64 (4 * dec.necessaryPoints (i % 16)))
                  ((dec.pts[i % 16]'hpoly_pts).vec.drop (dec.necessaryPoints (i % 16))) ∗
                sortedSetPtPinRest A.repAlloc (pins[i % 16]'hpoly_pins)
                  (dec.pts[i % 16]'hpoly_pts) ∗
                sortedSetPtListPinAt A.repAlloc (pts_base + BitVec.ofNat 64 (24 * (i % 16 + 1)))
                  (pins.drop (i % 16 + 1)) (dec.pts.drop (i % 16 + 1)) ∗
                ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗
                ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
                ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
                (out_ptr ↦ₛ out) ∗
                memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (2 * (dec.ptsNeeded - i)) ∗
                memRegion ((sp0 - 672#64) - 4352#64) 48 ∗ F) := by
          rw [optPolyCacheListAt_focus A.repAlloc polys (i % 16) (sp0 - 600#64) hpoly_p,
            ptSliceRefListAt_focus dec pins (i % 16) pts_vec_ptr hpoly_pins,
            sortedSetPtListPinAt_focus A.repAlloc pins dec.pts (i % 16) pts_base
              (by rw [hpins, hpts]) hpoly_pts,
            sortedSetPtPinAt_eq_slice A.repAlloc (pins[i % 16]'hpoly_pins)
              (dec.pts[i % 16]'hpoly_pts) (pts_base + BitVec.ofNat 64 (24 * (i % 16))),
            ptSliceAt_split_take_drop (dec.pts[i % 16]'hpoly_pts).vec
              (dec.necessaryPoints (i % 16)) (pins[i % 16]'hpoly_pins).ptr hnec_le_len,
            stackAt_computeAt_eq_prepare (sp0 - 672#64), hslice_len]
          sep_ac_rfl
        refine SepWP.done hpc1 hrun1 fun hcl1 => ?_
        apply sepWP_seq_lscl hcl1 (mid := (blkPl_418).base + 1284#64)
        refine SepWP.weaken_pre (Entails.of_eq hfocus_pre)
          (lagrangeInterpolate_inlined_cl_placed_sepWP hshim_sat halloc_sat hdealloc_sat hmemcpy_sat
            hprep hcomp sp0 pts_vec_ptr (pins[i % 16]'hpoly_pins).ptr
            (BitVec.ofNat 64 dec.ptsNeeded) hsp0 (i % 16) (polys[i % 16]'hpoly_p) ptsSlice
            hpoly_lt hk_pos hk_le st hfit_interp s0 s1 _ _
            hcl1 hpc1 hrun1 (by rw [hsp1, hsp]) (by rw [htr1, htr])
            hx0_1 hx24_1 hx25_1 hx26_1 hx29_1 ?_)
        intro s2 evs1 he1 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx22_2 hx24_2 hx25_2 hx26_2 hx29_2
        obtain ⟨hfit_ca, hsplit_ca⟩ := hsplit_env evs1 he1
        have hreasm_mid :
            optPolyCacheSlotAt A.repAlloc ((sp0 - 600#64) + BitVec.ofNat 64 (24 * (i % 16)))
                (some pInterp) ∗
              ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
              ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
              ((sp0 - 608#64) ↦₆₄ 16#64) ∗
              ptSliceRefAt (pts_vec_ptr + BitVec.ofNat 64 (16 * (i % 16)))
                (pins[i % 16]'hpoly_pins).ptr ptsSlice.length ∗
              ptSliceAt (pins[i % 16]'hpoly_pins).ptr ptsSlice ∗
              interpolateScratchAt sp0 ∗
              reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool lim (M.stepEvents evs1 st) s2 ∗
              stackAt (sp0 - 672#64) lagrangePrepareStack ∗
              (optPolyCacheListAt A.repAlloc (sp0 - 600#64) (polys.take (i % 16)) ∗
                optPolyCacheListAt A.repAlloc
                  ((sp0 - 600#64) + BitVec.ofNat 64 (24 * (i % 16 + 1))) (polys.drop (i % 16 + 1)) ∗
                ptSliceRefListAt dec 0 pts_vec_ptr (pins.take (i % 16)) ∗
                ptSliceRefListAt dec (i % 16 + 1)
                  (pts_vec_ptr + BitVec.ofNat 64 (16 * (i % 16 + 1))) (pins.drop (i % 16 + 1)) ∗
                sortedSetPtListPinAt A.repAlloc pts_base (pins.take (i % 16))
                  (dec.pts.take (i % 16)) ∗
                ((pts_base + BitVec.ofNat 64 (24 * (i % 16))) ↦₆₄ (pins[i % 16]'hpoly_pins).cap) ∗
                ((pts_base + BitVec.ofNat 64 (24 * (i % 16)) + 8#64) ↦₆₄
                  (pins[i % 16]'hpoly_pins).ptr) ∗
                ((pts_base + BitVec.ofNat 64 (24 * (i % 16)) + 16#64) ↦₆₄
                  BitVec.ofNat 64 (dec.pts[i % 16]'hpoly_pts).vec.length) ∗
                ptSliceAt
                  ((pins[i % 16]'hpoly_pins).ptr + BitVec.ofNat 64 (4 * dec.necessaryPoints (i % 16)))
                  ((dec.pts[i % 16]'hpoly_pts).vec.drop (dec.necessaryPoints (i % 16))) ∗
                sortedSetPtPinRest A.repAlloc (pins[i % 16]'hpoly_pins)
                  (dec.pts[i % 16]'hpoly_pts) ∗
                sortedSetPtListPinAt A.repAlloc (pts_base + BitVec.ofNat 64 (24 * (i % 16 + 1)))
                  (pins.drop (i % 16 + 1)) (dec.pts.drop (i % 16 + 1)) ∗
                ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗
                ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
                ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
                (out_ptr ↦ₛ out) ∗
                memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (2 * (dec.ptsNeeded - i)) ∗
                memRegion ((sp0 - 672#64) - 4352#64) 48 ∗ F) =
            optPolyCacheSlotAt A.repAlloc ((sp0 - 600#64) + BitVec.ofNat 64 (24 * (i % 16)))
                (some pInterp) ∗
              ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗
              ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
              reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool lim (M.stepEvents evs1 st) s2 ∗
              stackAt (sp0 - 672#64) computeAtStack ∗
              (optPolyCacheListAt A.repAlloc (sp0 - 600#64) (polys.take (i % 16)) ∗
                optPolyCacheListAt A.repAlloc
                  ((sp0 - 600#64) + BitVec.ofNat 64 (24 * (i % 16 + 1))) (polys.drop (i % 16 + 1)) ∗
                ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
                ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
                ((sp0 - 608#64) ↦₆₄ 16#64) ∗
                ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
                ptSliceRefListAt dec 0 pts_vec_ptr pins ∗
                sortedSetPtListPinAt A.repAlloc pts_base pins dec.pts ∗
                (out_ptr ↦ₛ out) ∗
                memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (2 * (dec.ptsNeeded - i)) ∗
                interpolateScratchAt sp0 ∗ F) := by
          rw [ptSliceRefListAt_focus dec pins (i % 16) pts_vec_ptr hpoly_pins,
            sortedSetPtListPinAt_focus A.repAlloc pins dec.pts (i % 16) pts_base
              (by rw [hpins, hpts]) hpoly_pts,
            sortedSetPtPinAt_eq_slice A.repAlloc (pins[i % 16]'hpoly_pins)
              (dec.pts[i % 16]'hpoly_pts) (pts_base + BitVec.ofNat 64 (24 * (i % 16))),
            ptSliceAt_split_take_drop (dec.pts[i % 16]'hpoly_pts).vec
              (dec.necessaryPoints (i % 16)) (pins[i % 16]'hpoly_pins).ptr hnec_le_len,
            stackAt_computeAt_eq_prepare (sp0 - 672#64), hslice_len]
          sep_ac_rfl
        refine SepWP.done hpc2 hrun2 fun hcl2 => ?_
        apply sepWP_seq_lscl hcl2 (mid := (blkPl_418).base + 1328#64)
        refine SepWP.weaken_pre (Entails.of_eq hreasm_mid)
          (decodedMessage_computeAtStep_cl_placed_sepWP hcomp_at sp0
            ((sp0 - 600#64) + BitVec.ofNat 64 (24 * (i % 16))) hsp0 i dec.ptsNeeded pInterp
            hi_lt hneed_le (M.stepEvents evs1 st) hfit_ca s0 s2 _ _
            hcl2 hpc2 hrun2 hsp2 htr2 hx19_2 (by rw [hx22_2, hx22_1]) hx29_2 ?_)
        intro s3 evs2 he2 hpc3 hrun3 hsp3 htr3 hx19_3 hx21_3 hx20_3 hx22_3 hx23_3 hx24_3 hx25_3
          hx26_3 hx29_3
        obtain ⟨hfit_rest, hmk_env⟩ := hsplit_ca evs2 he2
        have hset_polys :
            optPolyCacheListAt A.repAlloc (sp0 - 600#64) (polys.take (i % 16)) ∗
              optPolyCacheSlotAt A.repAlloc ((sp0 - 600#64) + BitVec.ofNat 64 (24 * (i % 16)))
                (some pInterp) ∗
              optPolyCacheListAt A.repAlloc
                ((sp0 - 600#64) + BitVec.ofNat 64 (24 * (i % 16 + 1))) (polys.drop (i % 16 + 1)) =
            optPolyCacheListAt A.repAlloc (sp0 - 600#64) (polys.set (i % 16) (some pInterp)) :=
          (optPolyCacheListAt_set A.repAlloc polys (i % 16) (some pInterp) (sp0 - 600#64) hpoly_p).symm
        refine SepWP.done hpc3 hrun3 fun hcl3 => ?_
        apply sepWP_seq_lscl hcl3
          (mid := if i + 1 = dec.ptsNeeded then (blkPl_418).base + 1404#64 else (blkPl_418).base + 548#64)
        refine SepWP.weaken_pre ?_
          (decodedMessage_pushTwoBytes_placed_sepWP (ext := ext) sp0 out_ptr
            (BitVec.ofNat 64 (2 * i)) i dec.ptsNeeded out yInterp.value hi_lt hneed_le hout_len s3
            (optPolyCacheListAt A.repAlloc (sp0 - 600#64) (polys.set (i % 16) (some pInterp)) ∗
              ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
              ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
              ((sp0 - 608#64) ↦₆₄ 16#64) ∗
              ptSliceRefListAt dec 0 pts_vec_ptr pins ∗
              sortedSetPtListPinAt A.repAlloc pts_base pins dec.pts ∗
              interpolateScratchAt sp0 ∗
              reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
              A.pool lim (M.stepEvents evs2 (M.stepEvents evs1 st)) s3 ∗
              stackAt (sp0 - 672#64) computeAtStack ∗ F)
            _ hpc3 hrun3 hx19_3 hx21_3 hx22_3 hx23_3 (by rw [hx24_3, hx24_2]) hx29_3 ?_)
        · rw [← hset_polys]
          exact Entails.of_eq (by sep_ac_rfl)
        intro s4 hpc4 hrun4 hsp4 htr4 hvm4 hx20_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx29_4
        conv => arg 4; rw [← A.pool_of_vmPreserved hvm4]
        refine SepWP.done hpc4 hrun4 fun hcl4 => ?_
        cases rem with
        | zero =>
          have hi1_eq : i + 1 = dec.ptsNeeded := by omega
          simp only [hi1_eq, ↓reduceIte] at hpc4
          have hrem0 : dec.ptsNeeded - (i + 1) = 0 := by omega
          rw [hrem0, Nat.mul_zero, memRegion_zero]
          have hloop0 :
              decodedMessageLoopTotal dec (collectedSlices dec 0 16) i (0 + 1) polys out =
                (polys.set (i % 16) (some pInterp), out ++ u16ToBeBytes yInterp.value) := by
            rw [hstep_pure]; rfl
          rw [hloop0] at hnext
          have hevs_tot :
              DecodedMessageLoopEnv dec (collectedSlices dec 0 16) i (0 + 1) polys
                (evs1 ++ evs2 ++ []) :=
            hmk_env [] rfl
          have hst_eq :
              M.stepEvents evs2 (M.stepEvents evs1 st) =
                M.stepEvents (evs1 ++ evs2 ++ []) st := by
            simp [← M.stepEvents_append]
          rw [hst_eq]
          refine SepWP.weaken_pre ?_
            (hnext s4 (evs1 ++ evs2 ++ []) hevs_tot hpc4 hrun4
              (by rw [hsp4, hsp3]) (by rw [htr4, htr3]) hx29_4)
          rw [hi1_eq]
          exact Entails.of_eq (by sep_ac_rfl)
        | succ rem' =>
          have hi1_ne : i + 1 ≠ dec.ptsNeeded := by omega
          simp only [hi1_ne, ↓reduceIte] at hpc4
          refine SepWP.weaken_pre ?_
            (decodedMessageLoop_cl_placed_sepWP hshim_sat halloc_sat hdealloc_sat hmemcpy_sat
              hprep hcomp hcomp_at dec sp0 pts_base pts_vec_ptr out_ptr pins
              hsp0 hpts hpins hsort hneed_le hall_ge s0 F post
              rem' (i + 1) (polys.set (i % 16) (some pInterp))
              (out ++ u16ToBeBytes yInterp.value)
              (M.stepEvents evs2 (M.stepEvents evs1 st)) s4 hfit_rest
              (by omega) (by simp [hpolys_len]) (by simp [hout_len, u16ToBeBytes]; omega)
              hcl4 hpc4 hrun4 (by rw [hsp4, hsp3]) (by rw [htr4, htr3])
              (by rw [hx20_4, hx20_3, hx20_2, hx20_1]) hx22_4 hx23_4 hx24_4
              (by rw [hx25_4, hx25_3, hx25_2]) (by rw [hx26_4, hx26_3, hx26_2]) hx29_4
              (fun sf evs3 he3 hpc_f hrun_f hsp_f htr_f hx29_f => ?_))
          · exact Entails.of_eq (by sep_ac_rfl)
          · rw [← hstep_pure]
            have hst_eq :
                M.stepEvents evs3 (M.stepEvents evs2 (M.stepEvents evs1 st)) =
                  M.stepEvents (evs1 ++ evs2 ++ evs3) st := by
              simp [← M.stepEvents_append]
            rw [hst_eq]
            exact hnext sf (evs1 ++ evs2 ++ evs3) (hmk_env evs3 he3) hpc_f hrun_f hsp_f htr_f hx29_f
    ·
      apply sepWP_seq_lscl hcl
        (mid := if i + 1 = dec.ptsNeeded then (blkPl_418).base + 1404#64 else (blkPl_418).base + 548#64)
      refine SepWP.weaken_pre ?_
        (decodedMessage_bsearchStep_placed_sepWP (ext := ext) (A := A.repAlloc)
          dec sp0 pts_base pins i hpts hpins hi_lt hneed_le hge_len hle_len
          s
          (optPolyCacheListAt A.repAlloc (sp0 - 600#64) polys ∗
            ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
            ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
            ((sp0 - 608#64) ↦₆₄ 16#64) ∗
            ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
            ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
            ptSliceRefListAt dec 0 pts_vec_ptr pins ∗
            (out_ptr ↦ₛ out) ∗
            memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (2 * (dec.ptsNeeded - i)) ∗
            interpolateScratchAt sp0 ∗
            reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool lim st s ∗
            stackAt (sp0 - 672#64) computeAtStack ∗ F)
          _ hpc hstat hx20 hx22 hx23 hx24 hx25 hx26 hx29 ?_ ?_)
      · exact Entails.of_eq (by sep_ac_rfl)
      · dsimp only
        intro _ hfound' s1 hpc1 hrun1 hsp1 htr1 hvm1 hx19_1 hx21_1 hx20_1 hx22_1 hx23_1 hx24_1
          hx25_1 hx26_1 hx29_1
        conv => arg 4; rw [← A.pool_of_vmPreserved hvm1]
        have hstep_pure := decodedMessageLoopTotal_step_found dec hpts hsort
          (rem := rem) (polys := polys) (out := out) rfl hb_lt hfound'
        have henv_found := decodedMessageLoopEnv_step_found dec hpts hsort
          (rem := rem) (polys := polys) rfl hb_lt hfound'
        refine SepWP.weaken_pre ?_
          (decodedMessage_pushTwoBytes_placed_sepWP (ext := ext) sp0 out_ptr
            (BitVec.ofNat 64 (2 * i)) i dec.ptsNeeded out
            ((dec.pts[i % 16]'hpoly_pts).vec[bsearchLoop (dec.pts[i % 16]'hpoly_pts).vec
              (BitVec.ofNat 16 (i / 16)) 0 (dec.pts[i % 16]'hpoly_pts).vec.length]'hb_lt).y.value
            hi_lt hneed_le hout_len s1
            (optPolyCacheListAt A.repAlloc (sp0 - 600#64) polys ∗
              ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
              ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
              ((sp0 - 608#64) ↦₆₄ 16#64) ∗
              ptSliceRefListAt dec 0 pts_vec_ptr pins ∗
              sortedSetPtListPinAt A.repAlloc pts_base pins dec.pts ∗
              interpolateScratchAt sp0 ∗
              reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool lim st s1 ∗
              stackAt (sp0 - 672#64) computeAtStack ∗ F)
            _ hpc1 hrun1 hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx29_1 ?_)
        · exact Entails.of_eq (by sep_ac_rfl)
        intro s2 hpc2 hrun2 hsp2 htr2 hvm2 hx20_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx29_2
        conv => arg 4; rw [← A.pool_of_vmPreserved hvm2]
        refine SepWP.done hpc2 hrun2 fun hcl2 => ?_
        cases rem with
        | zero =>
          have hi1_eq : i + 1 = dec.ptsNeeded := by omega
          simp only [hi1_eq, ↓reduceIte] at hpc2
          have hrem0 : dec.ptsNeeded - (i + 1) = 0 := by omega
          rw [hrem0, Nat.mul_zero, memRegion_zero]
          have hloop0 :
              decodedMessageLoopTotal dec (collectedSlices dec 0 16) i (0 + 1) polys out =
                (polys, out ++ u16ToBeBytes
                  ((dec.pts[i % 16]'hpoly_pts).vec[bsearchLoop (dec.pts[i % 16]'hpoly_pts).vec
                    (BitVec.ofNat 16 (i / 16)) 0
                    (dec.pts[i % 16]'hpoly_pts).vec.length]'hb_lt).y.value) := by
            rw [hstep_pure]; rfl
          rw [hloop0] at hnext
          have henv0 : DecodedMessageLoopEnv dec (collectedSlices dec 0 16) i (0 + 1) polys [] := by
            rw [henv_found]; rfl
          have hst_nil : st = M.stepEvents [] st := rfl
          rw [hst_nil]
          refine SepWP.weaken_pre ?_
            (hnext s2 [] henv0 hpc2 hrun2 (by rw [hsp2, hsp1, hsp])
              (by rw [htr2, htr1, htr]) hx29_2)
          rw [hi1_eq]
          exact Entails.of_eq (by sep_ac_rfl)
        | succ rem' =>
          have hi1_ne : i + 1 ≠ dec.ptsNeeded := by omega
          simp only [hi1_ne, ↓reduceIte] at hpc2
          have hfit' :
              FitsEnv M lim st
                (DecodedMessageLoopEnv dec (collectedSlices dec 0 16) (i + 1) (rem' + 1) polys) := by
            rwa [← henv_found]
          refine SepWP.weaken_pre ?_
            (decodedMessageLoop_cl_placed_sepWP hshim_sat halloc_sat hdealloc_sat hmemcpy_sat
              hprep hcomp hcomp_at dec sp0 pts_base pts_vec_ptr out_ptr pins
              hsp0 hpts hpins hsort hneed_le hall_ge s0 F post
              rem' (i + 1) polys
              (out ++ u16ToBeBytes
                ((dec.pts[i % 16]'hpoly_pts).vec[bsearchLoop (dec.pts[i % 16]'hpoly_pts).vec
                  (BitVec.ofNat 16 (i / 16)) 0
                  (dec.pts[i % 16]'hpoly_pts).vec.length]'hb_lt).y.value)
              st s2 hfit' (by omega) hpolys_len (by simp [hout_len, u16ToBeBytes]; omega)
              hcl2 hpc2 hrun2 (by rw [hsp2, hsp1, hsp]) (by rw [htr2, htr1, htr])
              (by rw [hx20_2, hx20_1]) hx22_2 hx23_2 hx24_2
              (by rw [hx25_2, hx25_1]) (by rw [hx26_2, hx26_1]) hx29_2
              (fun sf evs hevs hpc_f hrun_f hsp_f htr_f hx29_f => ?_))
          · exact Entails.of_eq (by sep_ac_rfl)
          · rw [← hstep_pure]
            have hevs' :
                DecodedMessageLoopEnv dec (collectedSlices dec 0 16) i (rem' + 1 + 1) polys evs := by
              rwa [henv_found]
            exact hnext sf evs hevs' hpc_f hrun_f hsp_f htr_f hx29_f
      · dsimp only
        intro _ hfalse
        rw [hfound] at hfalse
        cases hfalse

theorem decodedMessageLoop_cl_placed_wpp [LibsignalPlacement]
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
      (lsmpl.base 372) (withLsCodeLoaded lsmpl (lagrangePreparePlacedSpec M A lim)))
    (hcomp : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 373) (withLsCodeLoaded lsmpl (withVmPreserved lagrangeCompletePlacedSpec)))
    (hcomp_at : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 371) (withLsCodeLoaded lsmpl (computeAtPlacedSpec M A lim)))
    (dec : PolyDecoder) (sp0 pts_base pts_vec_ptr out_ptr : BitVec 64)
    (pins : List VecPin)
    (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (hpts : dec.pts.length = 16) (hpins : pins.length = 16)
    (hsort : PolyDecoderStrictSorted dec)
    (hneed_le : dec.ptsNeeded ≤ 16 * 65536)
    (hall_ge : ∀ k (hk : k < 16), dec.necessaryPoints k ≤ (dec.pts[k]'(by omega)).vec.length)
    (s0 : State) (F : SepProp)
    (Q Qp : State → SepProp → Prop) (oom : State → SepProp := fun _ => ⌜False⌝)
    (rem i : Nat) (polys : List (Option Poly)) (out : List (BitVec 8)) (st : M.σ) (s : State)
    (hfit : FitsEnv M lim st
      (DecodedMessageLoopEnv dec (collectedSlices dec 0 16) i (rem + 1) polys))
    (hsum : i + (rem + 1) = dec.ptsNeeded)
    (hpolys_len : polys.length = 16)
    (hout_len : out.length = 2 * i)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_418).base + 548#64)
    (hstat : s.status = .Running)
    (hsp : s.sp = sp0 - 672#64)
    (htr : traceVRegs s = traceVRegs s0)
    (hx20 : s.readReg64 .x20 = pts_base)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 i)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (2 * i))
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 dec.ptsNeeded)
    (hx25 : s.readReg64 .x25 = 24#64)
    (hx26 : s.readReg64 .x26 = sp0 - 600#64)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      DecodedMessageLoopEnv dec (collectedSlices dec 0 16) i (rem + 1) polys evs →
      sf.pc = (blkPl_418).base + 1404#64 →
      sf.status = .Running →
      sf.sp = sp0 - 672#64 →
      traceVRegs sf = traceVRegs s0 →
      sf.readReg64 .x29 = sp0 - 96#64 →
      let (polysFinal, outFinal) :=
        decodedMessageLoopTotal dec (collectedSlices dec 0 16) i (rem + 1) polys out
      SepWPp ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) target_pc sf
        (optPolyCacheListAt A.repAlloc (sp0 - 600#64) polysFinal ∗
          ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
          ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
          ((sp0 - 608#64) ↦₆₄ 16#64) ∗
          ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗
          ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
          ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗
          ptSliceRefListAt dec 0 pts_vec_ptr pins ∗
          sortedSetPtListPinAt A.repAlloc pts_base pins dec.pts ∗
          (out_ptr ↦ₛ outFinal) ∗
          interpolateScratchAt sp0 ∗
          reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (sp0 - 672#64) computeAtStack ∗ F)
        Q Qp oom) :
    SepWPp ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) target_pc s
      (optPolyCacheListAt A.repAlloc (sp0 - 600#64) polys ∗
        ((sp0 - 648#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
        ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
        ((sp0 - 608#64) ↦₆₄ 16#64) ∗
        ((sp0 - 216#64) ↦₆₄ BitVec.ofNat 64 (2 * dec.ptsNeeded)) ∗
        ((sp0 - 208#64) ↦₆₄ out_ptr) ∗
        ((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
        ptSliceRefListAt dec 0 pts_vec_ptr pins ∗
        sortedSetPtListPinAt A.repAlloc pts_base pins dec.pts ∗
        (out_ptr ↦ₛ out) ∗
        memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (2 * (dec.ptsNeeded - i)) ∗
        interpolateScratchAt sp0 ∗
        reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool lim st s ∗
        stackAt (sp0 - 672#64) computeAtStack ∗ F)
      Q Qp oom := by
  apply SepWPp.of_sepWP (mid := (blkPl_418).base + 1404#64)
  refine SepWP.mono (oom := fun _ => ⌜False⌝) ?_ (fun _ _ _ _ hp => hp)
  refine decodedMessageLoop_cl_placed_sepWP hshim_sat halloc_sat hdealloc_sat hmemcpy_sat
    hprep hcomp hcomp_at dec sp0 pts_base pts_vec_ptr out_ptr pins
    hsp0 hpts hpins hsort hneed_le hall_ge s0 F _
    rem i polys out st s hfit hsum hpolys_len hout_len
    hcl hpc hstat hsp htr hx20 hx22 hx23 hx24 hx25 hx26 hx29 ?_
  intro sf evs hevs hpc_f hrun_f hsp_f htr_f hx29_f
  exact SepWP.done hpc_f hrun_f (hnext sf evs hevs hpc_f hrun_f hsp_f htr_f hx29_f)

end LibsignalBinary.Proofs.SpqrV1.States.Leaves.DecodedMsgCl2PlacedBudgetAux

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
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.InterpolateFullPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DecodedMsgCl1Placed
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DecodedMsgCl1PlacedBudgetAux
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.Interpolate
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.InterpolatePlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlaced
import ProofLib.SepLogic.WPp

/-!
# `<PolyDecoder as Decoder>::decoded_message` (Block `418`, Part 1): `RustCliAllocBudget` Inlined `lagrange_interpolate`

Threads `RustCliAllocBudget M`, `BudgetLimits`, `FitsEnv`, `LagrangeInterpolateInlinedEnv`, and
`LibsignalCodeLoaded lsmpl` across Block `418`'s inlined `Poly::lagrange_interpolate` (calling
`lagrangePrepare` on Block `372` and `lagrangeComplete` on Block `373`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.States.Leaves.DecodedMsgCl1PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement blkPC_418 blkPl_418 lsmpl withLsCodeLoaded
)
open CryptoVerification.LibsignalSpqrV1 (Poly Pt)
open CryptoVerification.LibsignalTripleRatchet (sessionMemcpyRegionSpec sessionShimSpec)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.Alloc (
  spqrMemcpySym spqrRustAllocSym spqrRustNoAllocShimSym
)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Poly (gf16SliceAt ptSliceAt)
open CryptoVerification.SpqrV1.Poly.DecodedMessage (
  fold_interpolateScratchAt interpolateScratchAt
  lagrangeInterpolateTotal lagrangeInterpolateTotal_length
  optPolyCacheSlotAt pointsTo64_three_entails_memRegion_24 ptSliceRefAt
  spqrRustDeallocSym stackAt_alloc_eq_complete stackAt_prepare_eq_alloc traceVRegs
)
open CryptoVerification.SpqrV1.Poly.LagrangeComplete (
  lagrangeCompletePlacedSpec lagrangeCompleteStack
)
open CryptoVerification.SpqrV1.Poly.LagrangePrepare (
  lagrangePreparePure lagrangePreparePure_length lagrangePrepareStack
)
open CryptoVerification.SpqrV1.States.Leaves (sepWP_seq_lscl)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs
  RustCliAllocBudget SeqEnv fitsEvents_append rustAllocEvents
  rustCliAllocBudgetSpec rustCliDeallocBudgetSpec
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget (
  LagrangeInterpolateInlinedEnv
)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.InterpolateFullPlacedBudget (
  lagrangeInterpolate_miss_allocAcc_placed_sepWP
  lagrangeInterpolate_miss_allocL_placed_sepWP
)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.InterpolatePlacedBudget (
  lagrangeInterpolateDealloc_placed_sepWP
  lagrangeInterpolateStoreSlot_placed_sepWP lagrangeInterpolate_hit_placed_sepWP
)
open LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.DefsBudget (
  lagrangePreparePlacedSpec
)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.DecodedMsgCl1PlacedBudgetAux (
  lagrangeInterpolate_copyAndComplete0_cl_placed_sepWP
  lagrangeInterpolate_copyFirstAcc_cl_placed_sepWP
  lagrangeInterpolate_miss_prepare_cl_placed_sepWP
)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff rustAllocEvents

/-! ## Full CodeLoaded Placed Inlined `lagrange_interpolate` -/

theorem lagrangeInterpolate_inlined_cl_placed_sepWP [LibsignalPlacement]
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
    (sp0 pts_vec_ptr pt_ptr x24_saved : BitVec 64) (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (polyIdx : Nat) (optPoly : Option Poly) (pts_slice : List Pt)
    (hpoly : polyIdx < 16) (hk_pos : 1 ≤ pts_slice.length) (hk_le : pts_slice.length ≤ 65536)
    (st : M.σ) (hfit : FitsEnv M lim st (LagrangeInterpolateInlinedEnv optPoly pts_slice.length))
    (s0 s : State) (F : SepProp) (post : State → SepProp → Prop)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
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
    apply sepWP_seq_lscl hcl (mid := (blkPl_418).base + 732#64)
    refine SepWP.weaken_pre ?_
      (lagrangeInterpolate_miss_allocAcc_placed_sepWP hshim_sat halloc_sat sp0 pts_vec_ptr pt_ptr hsp0
        polyIdx pts_slice.length hpoly hk_pos hk_le st hfit1 s0 s
        (((sp0 - 664#64) ↦₆₄ v664) ∗ ((sp0 - 656#64) ↦₆₄ v656) ∗ ((sp0 - 640#64) ↦₆₄ v640) ∗
          ((sp0 - 192#64) ↦₆₄ v192) ∗ ((sp0 - 184#64) ↦₆₄ v184) ∗ ((sp0 - 176#64) ↦₆₄ v176) ∗
          ((sp0 - 168#64) ↦₆₄ v168) ∗ ((sp0 - 160#64) ↦₆₄ v160) ∗ ((sp0 - 152#64) ↦₆₄ v152) ∗
          memRegion (sp0 - 144#64) 24 ∗ ((sp0 - 648#64) ↦₆₄ x24_saved) ∗
          ptSliceAt pt_ptr pts_slice ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
          memRegion ((sp0 - 672#64) - 4304#64) 208 ∗ F)
        _ hpc hstat hsp htr hx0 hx25 hx26 hx29 ?_)
    · rw [stackAt_prepare_eq_alloc (sp0 - 672#64)]; exact Entails.of_eq (by sep_ac_rfl)
    intro sf1 hpc1 hrun1 hsp1 htr1 hacc_ne hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx27_1 hx29_1
    apply SepWP.done hpc1 hrun1
    intro hcl1
    let st1 := M.stepEvents (rustAllocEvents (2 * pts_slice.length) 2) st
    apply sepWP_seq_lscl hcl1 (mid := (blkPl_418).base + 760#64)
    refine SepWP.weaken_pre ?_
      (lagrangeInterpolate_miss_prepare_cl_placed_sepWP hprep sp0 (sf1.readReg64 .x0) pt_ptr v168 v160 v152
        hsp0 pts_slice.length pts_slice hk_pos hk_le rfl st1 hfit2 s0 sf1
        (A.live (sf1.readReg64 .x0) (2 * pts_slice.length) 2 ∗
          memRegion (sf1.readReg64 .x0) (2 * pts_slice.length) ∗
          optPolyCacheSlotAt A.repAlloc ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx)) none ∗
          ((sp0 - 664#64) ↦₆₄ v664) ∗ ((sp0 - 656#64) ↦₆₄ v656) ∗
          ((sp0 - 648#64) ↦₆₄ x24_saved) ∗ ((sp0 - 640#64) ↦₆₄ v640) ∗
          ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗ ((sp0 - 608#64) ↦₆₄ 16#64) ∗
          ptSliceRefAt (pts_vec_ptr + BitVec.ofNat 64 (16 * polyIdx)) pt_ptr pts_slice.length ∗
          ((sp0 - 192#64) ↦₆₄ v192) ∗ ((sp0 - 184#64) ↦₆₄ v184) ∗ ((sp0 - 176#64) ↦₆₄ v176) ∗ F)
        _ hcl1 hpc1 hrun1 hsp1 htr1 rfl hx21_1 hx27_1 hx29_1 ?_)
    · rw [stackAt_prepare_eq_alloc (sp0 - 672#64)]; exact Entails.of_eq (by sep_ac_rfl)
    intro b_cap ptr_b sf2 hb_cap_ge hb_cap_lt hptr_b_ne hpc2 hrun2 hsp2 htr2
      hx19_2 hx20_2 hx21_2 hx22_2 hx24_2 hx27_2 hx29_2
    apply SepWP.done hpc2 hrun2
    intro hcl2
    let st2 := M.stepEvents (rustAllocEvents (2 * (pts_slice.length + 1)) 2) st1
    apply sepWP_seq_lscl hcl2 (mid := (blkPl_418).base + 796#64)
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
        _ hpc2 hrun2 hsp2 htr2 (hx19_2.trans hx19_1) hx21_2 hx24_2 hx27_2 hx29_2 ?_)
    · rw [stackAt_prepare_eq_alloc (sp0 - 672#64)]; exact Entails.of_eq (by sep_ac_rfl)
    intro sf3 hpc3 hrun3 hsp3 htr3 hptr_l_ne hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx27_3 hx29_3
    apply SepWP.done hpc3 hrun3
    intro hcl3
    let st3 := M.stepEvents (rustAllocEvents (2 * (pts_slice.length + 1)) 2) st2
    have hb_len : (lagrangePreparePure pts_slice).coefficients.length = pts_slice.length + 1 :=
      lagrangePreparePure_length pts_slice
    refine SepWP.weaken_pre ?_
      (lagrangeInterpolate_copyAndComplete0_cl_placed_sepWP hmemcpy_sat hcomp sp0 (sf3.readReg64 .x0) ptr_b pt_ptr
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
        post hcl3 hpc3 hrun3 hsp3 rfl hx19_3 hx21_3 hx23_3 hx24_3 hx25_3 hx27_3 hx29_3 ?_)
    · rw [stackAt_alloc_eq_complete (sp0 - 672#64)]; exact Entails.of_eq (by sep_ac_rfl)
    intro sf4 hcl4 hpc4 hrun4 hsp4 htr4 hvm4 hx20_4 hx21_4 hx22_4 hx24_4 hx25_4 hx26_4 hx27_4 hx29_4
    refine SepWP.weaken_pre ?_
      (lagrangeInterpolate_copyFirstAcc_cl_placed_sepWP hmemcpy_sat hcomp sp0 (sf1.readReg64 .x0) (sf3.readReg64 .x0)
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
        post hcl4 hpc4 hrun4 hsp4 hx21_4 hx24_4 hx25_4 hx26_4 hx27_4 hx29_4 ?_)
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
        ((sp0 - 136#64) ↦₆₄ sf1.readReg64 .x0) ∗
        ((sp0 - 128#64) ↦₆₄ BitVec.ofNat 64 pts_slice.length) ∗
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
          A.pool lim (M.stepEvents evs_free st3) sf6 ∗ stackAt (sp0 - 672#64) lagrangePrepareStack ∗ F) by
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
        ((sp0 - 152#64) ↦₆₄ BitVec.ofNat 64 pts_slice.length) ∗
        memRegion (sp0 - 144#64) 24 ∗
        (optPolyCacheSlotAt A.repAlloc ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx))
            (some (lagrangeInterpolateTotal pts_slice)) ∗
          ((sp0 - 648#64) ↦₆₄ x24_saved) ∗ ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
          ((sp0 - 608#64) ↦₆₄ 16#64) ∗
          ptSliceRefAt (pts_vec_ptr + BitVec.ofNat 64 (16 * polyIdx)) pt_ptr pts_slice.length ∗
          ptSliceAt pt_ptr pts_slice ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
          A.pool lim (M.stepEvents evs_free st3) sf6 ∗ stackAt (sp0 - 672#64) lagrangePrepareStack ∗ F) by
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

theorem lagrangeInterpolate_inlined_cl_placed_wpp [LibsignalPlacement]
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
    (sp0 pts_vec_ptr pt_ptr x24_saved : BitVec 64) (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (polyIdx : Nat) (optPoly : Option Poly) (pts_slice : List Pt)
    (hpoly : polyIdx < 16) (hk_pos : 1 ≤ pts_slice.length) (hk_le : pts_slice.length ≤ 65536)
    (st : M.σ) (hfit : FitsEnv M lim st (LagrangeInterpolateInlinedEnv optPoly pts_slice.length))
    (s0 s : State) (F : SepProp) (Q Qp : State → SepProp → Prop)
    (oom : State → SepProp := fun _ => ⌜False⌝)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
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
  refine lagrangeInterpolate_inlined_cl_placed_sepWP hshim_sat halloc_sat hdealloc_sat
    hmemcpy_sat hprep hcomp sp0 pts_vec_ptr pt_ptr x24_saved hsp0 polyIdx optPoly pts_slice
    hpoly hk_pos hk_le st hfit s0 s F _ hcl hpc hstat hsp htr hx0 hx24 hx25 hx26 hx29 ?_
  intro sf evs hevs hpc_f hrun_f hsp_f htr_f hx19_f hx20_f hx22_f hx24_f hx25_f hx26_f hx29_f
  exact SepWP.done hpc_f hrun_f
    (hnext sf evs hevs hpc_f hrun_f hsp_f htr_f hx19_f hx20_f hx22_f hx24_f hx25_f hx26_f hx29_f)

end LibsignalBinary.Proofs.SpqrV1.States.Leaves.DecodedMsgCl1PlacedBudget

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.PolyEncoderBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.UnchunkedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hscPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsd
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsdPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudget
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch3Placed
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Budget-Threaded Variant 2 (`HeaderSent`) — Part D

Cross-block drop/decoder subroutine bridges and `FreeOnlyEvs` cleanup paths (`+9132`, `+9112`,
`+11024`, `+11240`) in Block `333` under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsdPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkLib_eq_333 blkPC_333 blkPl_333 lsProg_280 lsProg_333
   ls_blockPlacement_base lscall_blk_cl lsmpl lsρ subroutine_ok_withLsCodeLoaded_of_plain
   withLsCodeLoaded withMemEq)
open CryptoVerification.LibsignalSpqrV1 (GF16 NUM_POLYS PolyEncoder spqrAuthApi)
open CryptoVerification.RustHeap (RustAlloc allocHookStack)
open CryptoVerification.SpqrV1.Alloc (spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.Drop
  (DropGluePoly16Ghost DropGluePolyEncoderGhost DropUnchunkedEkSentGhost dropGluePoly16Stack
   dropStack32 polyEncoderAt_entails_tag_vecs_tail unchunkedEkSentAt unchunkedEkSentSize
   vecCapPtrDealloc vecGF16ListOf)
open CryptoVerification.SpqrV1.Poly (polyArrayBytes polyEncoderAt polyEncoderSize)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved v2hsc_stackAt_allocHook_to_encoderFromPbStack
   v2hsc_stackAt_encoderFromPbStack_to_allocHook v2hsd_bv_add_add_lit v2hsd_polyEncoder_1392_join
   v2hsd_stackAt_dropStack32_to_encoderFromPbStack
   v2hsd_stackAt_encoderFromPbStack_to_dropStack32)
open CryptoVerification.SpqrV1.Unchunked
  (extractLsb'_0_64_append extractLsb'_64_64_append)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget
   VmPreserved rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget (dropGluePoly16Spec)
open LibsignalBinary.Proofs.SpqrV1.Drop.PolyEncoderBudget (dropGluePolyEncoderSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.UnchunkedBudget
  (dropUnchunkedEkSentSpec drop_unchunked_ek_sent_placed_ok)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (isTotalTrapHooks_withPanics_vmTrapHooks sepWP_lsBlock_vmPreserved
   stripS_calleeSavedVRegs stripS_pc stripS_readReg64 stripS_sp stripS_status stripS_trace
   vmTrapHooks)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
  (FromPbAllocHooksPlacedBudget spqrRustDeallocSym)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
  (align_pre_st deallocFreeOnlySpec sepWP_evs_dealloc sepWP_evs_nil seq_clean_evs seq_clean_st
   subroutine_ok_deallocFreeOnly)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux
  (FromPbAllocHooksBudget blk333_noSvc0 entails_pre_st seq_clean_evs_lscl seq_clean_lscl_st
   withMemEq_of_withLsCodeLoaded)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget (blk333_safeVm)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hscPlacedBudget
  (v2hsc_cleanup_9184_to_9192_of_sub_placed v2hsc_cleanup_9192_to_9212_of_sub_placed
   v2hsc_sub_ok_dealloc_of_dealloc_placed v2hsc_sub_ok_dealloc_of_placedHooks
   v2hsc_sub_ok_dealloc_placed)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudget
  (drop_glue_poly16_cl_on drop_glue_poly16_mem_on drop_glue_poly_encoder_local2_cl_on
   drop_glue_poly_encoder_local2_mem_on)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm, local wp_norm] v2hsd_bv_add_add_lit

private theorem blkPl_333_base [LibsignalPlacement] :
    (blkPl_333).base = lsmpl.base 333 := rfl

local macro "wp_steps_sync_333 " mid:term : tactic => `(tactic| (
  apply sepWP_seg_ls_vm
    (Q := (blkPC_333).rebase (blkPl_333).base (hooksException _))
    blkLib_eq_333 blk333_noSvc0 (mid := $mid)
  intro _m_strip
  try rw [← blkPl_333_base]
  wp_steps
  refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  refine ProofLib.SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))
    (hnext := ?_)
))

/-! ## Subroutine Call Bridges -/

theorem v2hsd_sub_ok_drop_poly16_11028_cl_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 265)
      (withLsCodeLoaded lsmpl (dropGluePoly16Spec M A lim)) :=
  drop_glue_poly16_cl_on (callerProg := lsProg_333 (Rust.withPanics ext)) hdealloc

theorem v2hsd_sub_ok_drop_poly16_11028_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {m : Memory}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hcl : LibsignalCodeLoaded lsmpl m) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsmpl.base 265)
      (withMemEq m (dropGluePoly16Spec M A lim)) :=
  drop_glue_poly16_mem_on
    (callerProg := (blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)) hdealloc hcl

theorem v2hsd_sub_ok_drop_poly16_11028_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {m : Memory}
    (hA : FromPbAllocHooksBudget M A lim ext) (hcl : LibsignalCodeLoaded lsmpl m) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsmpl.base 265)
      (withMemEq m (dropGluePoly16Spec M A lim)) :=
  v2hsd_sub_ok_drop_poly16_11028_of_dealloc_placed hA.dealloc hcl

theorem v2hsd_sub_ok_drop_poly_encoder_11244_cl_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 272)
      (withLsCodeLoaded lsmpl (dropGluePolyEncoderSpec M A lim)) :=
  drop_glue_poly_encoder_local2_cl_on (callerProg := lsProg_333 (Rust.withPanics ext)) hdealloc

theorem v2hsd_sub_ok_drop_poly_encoder_11244_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {m : Memory}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hcl : LibsignalCodeLoaded lsmpl m) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsmpl.base 272)
      (withMemEq m (dropGluePolyEncoderSpec M A lim)) :=
  drop_glue_poly_encoder_local2_mem_on
    (callerProg := (blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)) hdealloc hcl

theorem v2hsd_sub_ok_drop_poly_encoder_11244_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {m : Memory}
    (hA : FromPbAllocHooksBudget M A lim ext) (hcl : LibsignalCodeLoaded lsmpl m) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsmpl.base 272)
      (withMemEq m (dropGluePolyEncoderSpec M A lim)) :=
  v2hsd_sub_ok_drop_poly_encoder_11244_of_dealloc_placed hA.dealloc hcl

theorem drop_unchunked_ek_sent_cl_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_280 (Rust.withPanics ext)) (lsmpl.base 280)
      (withLsCodeLoaded lsmpl (dropUnchunkedEkSentSpec M A lim F)) := by
  rw [← ls_blockPlacement_base (i := 280)]
  exact subroutine_ok_withLsCodeLoaded_of_plain
    (drop_unchunked_ek_sent_placed_ok (spqr_hook_ok_of_mem hdealloc))

theorem v2hsd_sub_ok_drop_unchunked_ek_sent_11252_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)} {m : Memory}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hcl : LibsignalCodeLoaded lsmpl m) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsmpl.base 280)
      (withMemEq m (dropUnchunkedEkSentSpec M A lim F)) :=
  lscall_blk_cl (drop_unchunked_ek_sent_cl_placed_ok hdealloc) hcl (by decide)

theorem v2hsd_sub_ok_drop_unchunked_ek_sent_11252_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)} {m : Memory}
    (hA : FromPbAllocHooksBudget M A lim ext) (hcl : LibsignalCodeLoaded lsmpl m) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsmpl.base 280)
      (withMemEq m (dropUnchunkedEkSentSpec M A lim F)) :=
  v2hsd_sub_ok_drop_unchunked_ek_sent_11252_of_dealloc_placed hA.dealloc hcl

theorem v2hsd_sub_ok_decoder_from_pb_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 376)
      (withLsCodeLoaded lsmpl (DefsBudget.decoderFromPbSpec M A lim)) :=
  hdec

theorem v2hsd_sub_ok_decoder_from_pb_mem_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {m : Memory}
    (hdec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (hcl : LibsignalCodeLoaded lsmpl m) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsmpl.base 376)
      (withMemEq m (DefsBudget.decoderFromPbSpec M A lim)) :=
  withMemEq_of_withLsCodeLoaded hdec hcl

/-! ## Cleanup Paths (`+9132`, `+9112`, `+11256`, `+11240`, `+11024`) -/

theorem v2hsd_drop_poly16_pre_pool (A : RustAlloc) (fsp : BitVec 64)
    (enc : PolyEncoder) (Pool Frame : SepProp) :
    stackAt fsp encoderFromPbStack ∗
      polyEncoderAt A (fsp + 1392#64) enc ∗
      Pool ∗
      Frame ⊢
    ∃∗ tag : BitVec 64, ∃∗ vecs : List (List GF16),
      ⌜vecs.length = NUM_POLYS⌝ ∗
      ((stackAt fsp dropStack32 ∗ memRegion (fsp - 5152#64) 1024) ∗
       ((fsp + 1392#64) ↦₆₄ tag) ∗
       vecGF16ListOf A ((fsp + 1392#64) + 8#64) vecs ∗
       memRegion ((fsp + 1392#64) + 392#64) 8 ∗
       Pool ∗
       Frame) := by
  refine Entails.trans
    (sepConj_mono
      (v2hsd_stackAt_encoderFromPbStack_to_dropStack32 fsp)
      (sepConj_mono_left (polyEncoderAt_entails_tag_vecs_tail A (fsp + 1392#64) enc))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro tag
  apply Entails.sepExists_elim; intro vecs
  refine Entails.sepExists_right tag ?_
  refine Entails.sepExists_right vecs ?_
  exact Entails.of_eq (by sep_ac_rfl)

/-- Cleanup at `+9132 -> +9212`: loads `ca2` from `[sp + 232]` and `pa2` from `[sp + 184]`,
    deallocates `(ca2, pa2)` and `(ca3, pa3)`, and reaches `+9212`. -/
theorem v2hsd_cleanup_9132_to_9212_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (s0 s1 : State) (fsp out d0 ca2 pa2 ca3 pa3 : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9132#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9212#64) s1
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          ((fsp + 184#64) ↦₆₄ pa2) ∗
          ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        TraceCalleeSaved sm s0) := by
  refine seq_clean_evs
    (mid := lsmpl.base 333 + 9192#64)
    (P_evs := fun evs1 sm =>
      stackAt fsp encoderFromPbStack ∗
      ((fsp + 176#64) ↦₆₄ pa3) ∗
      vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
      A.pool lim (M.stepEvents evs1 st) sm ∗
      (((fsp + 184#64) ↦₆₄ pa2) ∗
       ((fsp + 232#64) ↦₆₄ ca2) ∗ Frame))
    (Q := fun sm =>
      sm.sp = fsp ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = d0 ∧
      sm.readReg64 .x26 = ca3 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · rcases htr1 with ⟨htr_1, hvregs_1⟩
    by_cases hca2 : (ca2 == 0#64) = true
    · dsimp only [vecCapPtrDealloc, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      change s1.pc = (blkPl_333).base + 9132#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 9192#64) s1 _ _
      simp only [hca2, ↓reduceIte, emp_sepConj]
      apply sepWP_evs_nil
      simp only [M.stepEvents_nil]
      wp_steps_sync_333 ((blkPl_333).base + 9192#64)
      try simp only [State.setMem_setMem]
      refine align_pre_st (by sep_ac_rfl) ?_
      wp_done
    · have hca2_f : (ca2 == 0#64) = false := Bool.eq_false_iff.mpr hca2
      refine seq_clean_st
        (mid := lsmpl.base 333 + 9184#64)
        (P_mid := fun sm =>
          stackAt fsp encoderFromPbStack ∗
          vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
          A.pool lim st sm ∗
          (((fsp + 176#64) ↦₆₄ pa3) ∗
           vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
           (((fsp + 184#64) ↦₆₄ pa2) ∗
            ((fsp + 232#64) ↦₆₄ ca2) ∗ Frame)))
        (Q := fun sm =>
          sm.sp = fsp ∧
          sm.readReg64 .x0 = pa2 ∧
          sm.readReg64 .x1 = ca2 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x22 = d0 ∧
          sm.readReg64 .x26 = ca3 ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · change s1.pc = (blkPl_333).base + 9132#64 at hpc1
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 9184#64) s1 _ _
        wp_steps_sync_333 ((blkPl_333).base + 9184#64)
        try simp only [State.setMem_setMem]
        refine align_pre_st (by sep_ac_rfl) ?_
        wp_done
      · intro s2 hpc2 hrun2 ⟨hsp2, hx0_2, hx1_2, hx19_2, hx22_2, hx26_2, htr2⟩
        have h9184 := v2hsc_cleanup_9184_to_9192_of_sub_placed hdealloc_ok s0 s2 fsp out d0
          ca2 pa2 ca3 st
          (((fsp + 176#64) ↦₆₄ pa3) ∗
           vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
           (((fsp + 184#64) ↦₆₄ pa2) ∗
            ((fsp + 232#64) ↦₆₄ ca2) ∗ Frame))
          hca2_f hfsp_align hpc2 hrun2 hsp2 hx0_2 hx1_2 hx19_2 hx22_2 hx26_2 htr2
        exact SepWP.mono h9184 fun sm _Pm _ _ ⟨evs, hevs, hPm, hq⟩ =>
          ⟨evs, hevs, Entails.trans hPm (Entails.of_eq (by sep_ac_rfl)), hq⟩
  · intro evs1 s2 hevs1 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, hx26_2, htr2⟩
    have h9192 := v2hsc_cleanup_9192_to_9212_of_sub_placed hdealloc_ok s0 s2 fsp out d0
      ca3 pa3 (M.stepEvents evs1 st)
      (((fsp + 184#64) ↦₆₄ pa2) ∗
       ((fsp + 232#64) ↦₆₄ ca2) ∗ Frame)
      hfsp_align hpc2 hrun2 hsp2 hx19_2 hx22_2 hx26_2 htr2
    refine SepWP.mono h9192 fun sm _Pm _ _ ⟨evs2, hevs2, hPm, hq⟩ => ?_
    refine ⟨evs1 ++ evs2, hevs1.append hevs2, ?_, hq⟩
    rw [M.stepEvents_append]
    exact Entails.trans hPm (Entails.of_eq (by sep_ac_rfl))

theorem v2hsd_cleanup_9132_to_9212_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (s0 s1 : State) (fsp out d0 ca2 pa2 ca3 pa3 : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9132#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9212#64) s1
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          ((fsp + 184#64) ↦₆₄ pa2) ∗
          ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        TraceCalleeSaved sm s0) :=
  v2hsd_cleanup_9132_to_9212_of_sub_placed
    (v2hsc_sub_ok_dealloc_of_dealloc_placed hdealloc) s0 s1 fsp out d0 ca2 pa2 ca3 pa3 st Frame
    hfsp_align hpc1 hrun1 hsp1 hx19_1 hx22_1 hx26_1 htr1

theorem v2hsd_cleanup_9132_to_9212_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 s1 : State) (fsp out d0 ca2 pa2 ca3 pa3 : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9132#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9212#64) s1
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          ((fsp + 184#64) ↦₆₄ pa2) ∗
          ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        TraceCalleeSaved sm s0) :=
  v2hsd_cleanup_9132_to_9212_of_sub_placed
    (v2hsc_sub_ok_dealloc_of_placedHooks hA) s0 s1 fsp out d0 ca2 pa2 ca3 pa3 st Frame
    hfsp_align hpc1 hrun1 hsp1 hx19_1 hx22_1 hx26_1 htr1

theorem v2hsd_cleanup_9132_to_9212_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 s1 : State) (fsp out d0 ca2 pa2 ca3 pa3 : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9132#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9212#64) s1
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          ((fsp + 184#64) ↦₆₄ pa2) ∗
          ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        TraceCalleeSaved sm s0) :=
  v2hsd_cleanup_9132_to_9212_of_sub_placed
    (v2hsc_sub_ok_dealloc_placed hA) s0 s1 fsp out d0 ca2 pa2 ca3 pa3 st Frame
    hfsp_align hpc1 hrun1 hsp1 hx19_1 hx22_1 hx26_1 htr1

/-- Cleanup at `+9112 -> +9212` (`<PolyEncoder>::from_pb = Err`): deallocates `(ca1, pa1)`,
    `(ca2, pa2)`, and `(ca3, pa3)`. -/
theorem v2hsd_cleanup_9112_to_9212_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (s0 s1 : State) (fsp out d0 ca1 pa1 ca2 pa2 ca3 pa3 : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9112#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9212#64) s1
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 200#64) ↦₆₄ ca1) ∗
        ((fsp + 1272#64) ↦₆₄ pa1) ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        vecCapPtrDealloc A.repAlloc ca1 pa1 ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          ((fsp + 200#64) ↦₆₄ ca1) ∗
          ((fsp + 1272#64) ↦₆₄ pa1) ∗
          ((fsp + 184#64) ↦₆₄ pa2) ∗
          ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        TraceCalleeSaved sm s0) := by
  have hdealloc_fo : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (deallocFreeOnlySpec M A lim) :=
    subroutine_ok_deallocFreeOnly hdealloc_ok
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  refine seq_clean_evs
    (mid := lsmpl.base 333 + 9132#64)
    (P_evs := fun evs1 sm =>
      stackAt fsp encoderFromPbStack ∗
      ((fsp + 184#64) ↦₆₄ pa2) ∗
      ((fsp + 232#64) ↦₆₄ ca2) ∗
      ((fsp + 176#64) ↦₆₄ pa3) ∗
      vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
      vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
      A.pool lim (M.stepEvents evs1 st) sm ∗
      (((fsp + 200#64) ↦₆₄ ca1) ∗
       ((fsp + 1272#64) ↦₆₄ pa1) ∗ Frame))
    (Q := fun sm =>
      sm.sp = fsp ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = d0 ∧
      sm.readReg64 .x26 = ca3 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · rcases htr1 with ⟨htr_1, hvregs_1⟩
    refine SepWP.weaken_pre
      (sepConj_mono_left (v2hsc_stackAt_encoderFromPbStack_to_allocHook fsp)) ?_
    have hst := v2hsc_stackAt_allocHook_to_encoderFromPbStack fsp
    rw [show vecCapPtrDealloc A.repAlloc ca1 pa1 =
      (if (ca1 == 0#64) = true then emp else A.live pa1 ca1.toNat 1 ∗ memRegion pa1 ca1.toNat) from rfl]
    change s1.pc = (blkPl_333).base + 9112#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 9132#64) s1 _ _
    by_cases hca1 : (ca1 == 0#64) = true <;>
      simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · apply sepWP_evs_nil
      simp only [M.stepEvents_nil]
      wp_steps_sync_333 ((blkPl_333).base + 9132#64)
      try simp only [State.setMem_setMem]
      refine entails_pre_st ?_ ?_
      · intro sc hsc
        rw [← hsc]
        refine Entails.trans
          (Entails.of_eq (show _ =
            (stackAt fsp allocHookStack ∗ memRegion (fsp - 5152#64) 1056) ∗
            (((fsp + 184#64) ↦₆₄ pa2) ∗
             ((fsp + 232#64) ↦₆₄ ca2) ∗
             ((fsp + 176#64) ↦₆₄ pa3) ∗
             vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
             vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
             A.pool lim st sc ∗
             (((fsp + 200#64) ↦₆₄ ca1) ∗
              ((fsp + 1272#64) ↦₆₄ pa1) ∗ Frame)) by sep_ac_rfl)) ?_
        exact sepConj_mono_left hst
      · wp_done
    · apply sepWP_evs_dealloc ca1.toNat 1
      wp_steps_sync_333 (lsρ spqrRustDeallocSym)
      try simp only [State.setMem_setMem]
      wp_call hdealloc_fo (pa1, ca1.toNat, 1, st)
      have hacp : AllocCallPreserved s1 sf := by
        simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
      have hsp_sf : sf.sp = fsp := ‹sf.sp = _›.trans (by simp [wp_norm, arm64_norm, hsp1])
      have htr_sf : sf.trace = s0.trace := hacp.2.1.trans htr_1
      have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
        ‹calleeSavedVRegs sf = _›.trans hvregs_1
      refine entails_pre_st ?_ ?_
      · intro sc hsc
        rw [← hsc]
        simp only [wp_norm, arm64_norm, hsp1]
        refine Entails.trans
          (Entails.of_eq (show _ =
            (stackAt fsp allocHookStack ∗ memRegion (fsp - 5152#64) 1056) ∗
            (((fsp + 184#64) ↦₆₄ pa2) ∗
             ((fsp + 232#64) ↦₆₄ ca2) ∗
             ((fsp + 176#64) ↦₆₄ pa3) ∗
             vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
             vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
             A.pool lim (M.stepEvents (rustDeallocEvents ca1.toNat 1) st) sc ∗
             (((fsp + 200#64) ↦₆₄ ca1) ∗
              ((fsp + 1272#64) ↦₆₄ pa1) ∗ Frame)) by sep_ac_rfl)) ?_
        exact sepConj_mono_left hst
      · wp_done
  · intro evs1 s2 hevs1 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, hx26_2, htr2⟩
    have h9132 := v2hsd_cleanup_9132_to_9212_of_sub_placed hdealloc_ok s0 s2 fsp out d0
      ca2 pa2 ca3 pa3 (M.stepEvents evs1 st)
      (((fsp + 200#64) ↦₆₄ ca1) ∗
       ((fsp + 1272#64) ↦₆₄ pa1) ∗ Frame)
      hfsp_align hpc2 hrun2 hsp2 hx19_2 hx22_2 hx26_2 htr2
    refine SepWP.mono h9132 fun sm _Pm _ _ ⟨evs2, hevs2, hPm, hq⟩ => ?_
    refine ⟨evs1 ++ evs2, hevs1.append hevs2, ?_, hq⟩
    rw [M.stepEvents_append]
    exact Entails.trans hPm (Entails.of_eq (by sep_ac_rfl))

theorem v2hsd_cleanup_9112_to_9212_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (s0 s1 : State) (fsp out d0 ca1 pa1 ca2 pa2 ca3 pa3 : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9112#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9212#64) s1
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 200#64) ↦₆₄ ca1) ∗
        ((fsp + 1272#64) ↦₆₄ pa1) ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        vecCapPtrDealloc A.repAlloc ca1 pa1 ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          ((fsp + 200#64) ↦₆₄ ca1) ∗
          ((fsp + 1272#64) ↦₆₄ pa1) ∗
          ((fsp + 184#64) ↦₆₄ pa2) ∗
          ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        TraceCalleeSaved sm s0) :=
  v2hsd_cleanup_9112_to_9212_of_sub_placed
    (v2hsc_sub_ok_dealloc_of_dealloc_placed hdealloc) s0 s1 fsp out d0
    ca1 pa1 ca2 pa2 ca3 pa3 st Frame hfsp_align hpc1 hrun1 hsp1 hx19_1 hx22_1 hx26_1 htr1

theorem v2hsd_cleanup_9112_to_9212_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 s1 : State) (fsp out d0 ca1 pa1 ca2 pa2 ca3 pa3 : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9112#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9212#64) s1
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 200#64) ↦₆₄ ca1) ∗
        ((fsp + 1272#64) ↦₆₄ pa1) ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        vecCapPtrDealloc A.repAlloc ca1 pa1 ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          ((fsp + 200#64) ↦₆₄ ca1) ∗
          ((fsp + 1272#64) ↦₆₄ pa1) ∗
          ((fsp + 184#64) ↦₆₄ pa2) ∗
          ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        TraceCalleeSaved sm s0) :=
  v2hsd_cleanup_9112_to_9212_of_sub_placed
    (v2hsc_sub_ok_dealloc_of_placedHooks hA) s0 s1 fsp out d0
    ca1 pa1 ca2 pa2 ca3 pa3 st Frame hfsp_align hpc1 hrun1 hsp1 hx19_1 hx22_1 hx26_1 htr1

theorem v2hsd_cleanup_9112_to_9212_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 s1 : State) (fsp out d0 ca1 pa1 ca2 pa2 ca3 pa3 : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9112#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9212#64) s1
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 200#64) ↦₆₄ ca1) ∗
        ((fsp + 1272#64) ↦₆₄ pa1) ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        vecCapPtrDealloc A.repAlloc ca1 pa1 ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          ((fsp + 200#64) ↦₆₄ ca1) ∗
          ((fsp + 1272#64) ↦₆₄ pa1) ∗
          ((fsp + 184#64) ↦₆₄ pa2) ∗
          ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        TraceCalleeSaved sm s0) :=
  v2hsd_cleanup_9112_to_9212_of_sub_placed
    (v2hsc_sub_ok_dealloc_placed hA) s0 s1 fsp out d0
    ca1 pa1 ca2 pa2 ca3 pa3 st Frame hfsp_align hpc1 hrun1 hsp1 hx19_1 hx22_1 hx26_1 htr1

/-- `VmPreserved`-strengthened segment `+11256 -> +9228` (`mov w23, wzr; b +9228`). -/
theorem v2hsd_cleanup_11256_to_9228_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (fsp out : BitVec 64) (Rest : SepProp)
    (hpc1 : s1.pc = lsmpl.base 333 + 11256#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9228#64) s1
      Rest
      (fun sm Pm =>
        (Pm ⊢ Rest) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x23 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant2hsdPlaced.v2hsd_cleanup_11256_to_9228_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      fsp out Rest
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1) ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sm Pm hvm ⟨hPm, hsp_m, hx19_m, hx23_m, htr_m⟩ =>
      ⟨hPm, hvm, hsp_m, hx19_m, hx23_m, htr_m⟩

theorem v2hsd_cleanup_11256_to_9228_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (fsp out : BitVec 64) (Rest : SepProp)
    (hpc1 : s1.pc = lsmpl.base 333 + 11256#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9228#64) s1
      (A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ A.pool lim st sm ∗ Rest) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x23 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  have hwp := v2hsd_cleanup_11256_to_9228_placed (ext := ext) s0 s1 fsp out
    (A.pool lim st s1 ∗ Rest) hpc1 hrun1 hsp1 hx19_1 htr1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨hPm, hvm, hrest⟩

/-- Cleanup at `+11240 -> +9228` (`<PolyDecoder>::from_pb = Err`):
    drops `polyEncoderAt A.repAlloc (fsp + 1392) enc`, drops `unchunkedEkSentAt A.repAlloc (fsp + 1264) uc`,
    sets `x23 = 0#64`, and jumps to `+9228`. -/
theorem v2hsd_cleanup_11240_to_9228_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (s0 s1 : State) (fsp out : BitVec 64)
    (enc : PolyEncoder)
    (uc : CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.EkSent (spqrAuthApi F))
    (st : M.σ) (Frame : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 11240#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9228#64) s1
      (stackAt fsp encoderFromPbStack ∗
        polyEncoderAt A.repAlloc (fsp + 1392#64) enc ∗
        unchunkedEkSentAt A.repAlloc (fsp + 1264#64) uc ∗
        A.pool lim st s1 ∗
        Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          memRegion (fsp + 1392#64) 400 ∗
          memRegion (fsp + 1264#64) 80 ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x23 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  refine seq_clean_evs
    (mid := lsmpl.base 333 + 11256#64)
    (P_evs := fun evs12 sm =>
      A.pool lim (M.stepEvents evs12 st) sm ∗
      (stackAt fsp encoderFromPbStack ∗
       memRegion (fsp + 1392#64) 400 ∗
       memRegion (fsp + 1264#64) 80 ∗
       Frame))
    (Q := fun sm =>
      sm.sp = fsp ∧
      sm.readReg64 .x19 = out ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · refine SepWP.weaken_pre
      (sepConj_mono_left (v2hsd_stackAt_encoderFromPbStack_to_dropStack32 fsp)) ?_
    refine seq_clean_evs_lscl hcl1
      (mid := lsmpl.base 333 + 11248#64)
      (P_evs := fun evs1 sm =>
        (stackAt fsp dropStack32 ∗ memRegion (fsp - 5152#64) 1024) ∗
        memRegion (fsp + 1392#64) 400 ∗
        unchunkedEkSentAt A.repAlloc (fsp + 1264#64) uc ∗
        A.pool lim (M.stepEvents evs1 st) sm ∗
        Frame)
      (Q := fun sm =>
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · refine seq_clean_lscl_st hcl1
        (mid := lsmpl.base 272)
        (P_mid := fun sm =>
          polyEncoderAt A.repAlloc (fsp + 1392#64) enc ∗
          A.pool lim st sm ∗
          stackAt fsp dropStack32 ∗
          (memRegion (fsp - 5152#64) 1024 ∗
           unchunkedEkSentAt A.repAlloc (fsp + 1264#64) uc ∗
           Frame))
        (Q := fun sm =>
          sm.sp = fsp ∧
          sm.readReg64 .x0 = fsp + 1392#64 ∧
          sm.readReg64 .lr = lsmpl.base 333 + 11248#64 ∧
          sm.readReg64 .x19 = out ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · rcases htr1 with ⟨htr_1, hvregs_1⟩
        rw [← blkPl_333_base] at hpc1
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          (lsmpl.base 272) s1 _ _
        wp_steps_sync_333 (lsmpl.base 272)
        try simp only [State.setMem_setMem]
        refine align_pre_st (by sep_ac_rfl) ?_
        wp_done
      · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx0_2, hlr_2, hx19_2, htr2⟩
        have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := hsp2 ▸ hfsp_align
        have hdrop_enc := v2hsd_sub_ok_drop_poly_encoder_11244_of_dealloc_placed
          (M := M) (A := A) (lim := lim) hdealloc hcl2
        simp only [withMemEq, dropGluePolyEncoderSpec, dropGluePoly16Stack] at hdrop_enc
        dsimp only [polyEncoderSize] at hdrop_enc
        dsimp only [lsProg_333]
        rw [← blkPl_333_base] at hlr_2 ⊢
        rw [show stackAt fsp dropStack32 = stackAt s2.sp dropStack32 from hsp2 ▸ rfl]
        wp_call hdrop_enc ((⟨fsp + 1392#64, enc⟩ : DropGluePolyEncoderGhost), st)
        rw [hsp2]
        rw [hlr_2] at *
        have hevs_w : FreeOnlyEvs w := ‹_›
        have hacp_w : AllocCallPreserved s2 sf := by
          simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
        have hsp_sf : sf.sp = fsp := ‹sf.sp = s2.sp›.trans hsp2
        have htr_sf : sf.trace = s0.trace := hacp_w.2.1.trans htr2.1
        have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
          ‹calleeSavedVRegs sf = calleeSavedVRegs s2›.trans htr2.2
        refine SepWP.mono
          (post := fun sm Pm =>
            (Pm ⊢
              (stackAt fsp dropStack32 ∗ memRegion (fsp - 5152#64) 1024) ∗
              memRegion (fsp + 1392#64) 400 ∗
              unchunkedEkSentAt A.repAlloc (fsp + 1264#64) uc ∗
              A.pool lim (M.stepEvents w st) sm ∗
              Frame) ∧
            sm.sp = fsp ∧
            sm.readReg64 .x19 = out ∧
            TraceCalleeSaved sm s0)
          ?_ (fun _ _ _ _ ⟨hp, hq⟩ => ⟨w, hevs_w, hp, hq⟩)
        refine align_pre_st (by sep_ac_rfl) ?_
        wp_done
    · intro evs1 s2 hevs1 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, htr2⟩
      refine seq_clean_lscl_st hcl2
        (mid := lsmpl.base 280)
        (P_mid := fun sm =>
          unchunkedEkSentAt A.repAlloc (fsp + 1264#64) uc ∗
          A.pool lim (M.stepEvents evs1 st) sm ∗
          stackAt fsp dropStack32 ∗
          (memRegion (fsp - 5152#64) 1024 ∗
           memRegion (fsp + 1392#64) 400 ∗
           Frame))
        (Q := fun sm =>
          sm.sp = fsp ∧
          sm.readReg64 .x0 = fsp + 1264#64 ∧
          sm.readReg64 .lr = lsmpl.base 333 + 11256#64 ∧
          sm.readReg64 .x19 = out ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · rcases htr2 with ⟨htr_2, hvregs_2⟩
        rw [← blkPl_333_base] at hpc2
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          (lsmpl.base 280) s2 _ _
        wp_steps_sync_333 (lsmpl.base 280)
        try simp only [State.setMem_setMem]
        refine align_pre_st (by sep_ac_rfl) ?_
        wp_done
      · intro s3 hpc3 hrun3 hcl3 ⟨hsp3, hx0_3, hlr_3, hx19_3, htr3⟩
        have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := hsp3 ▸ hfsp_align
        have hdrop_uc := v2hsd_sub_ok_drop_unchunked_ek_sent_11252_of_dealloc_placed
          (M := M) (A := A) (lim := lim) (F := F) hdealloc hcl3
        simp only [withMemEq, dropUnchunkedEkSentSpec] at hdrop_uc
        dsimp only [unchunkedEkSentSize] at hdrop_uc
        dsimp only [lsProg_333]
        rw [← blkPl_333_base] at hlr_3 ⊢
        rw [show stackAt fsp dropStack32 = stackAt s3.sp dropStack32 from hsp3 ▸ rfl]
        wp_call hdrop_uc ((⟨fsp + 1264#64, uc⟩ : DropUnchunkedEkSentGhost F), M.stepEvents evs1 st)
        rw [hsp3]
        rw [hlr_3] at *
        have hevs_w : FreeOnlyEvs w := ‹_›
        have hacp_w : AllocCallPreserved s3 sf := by
          simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
        have hsp_sf : sf.sp = fsp := ‹sf.sp = s3.sp›.trans hsp3
        have htr_sf : sf.trace = s0.trace := hacp_w.2.1.trans htr3.1
        have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
          ‹calleeSavedVRegs sf = calleeSavedVRegs s3›.trans htr3.2
        have hst := v2hsd_stackAt_dropStack32_to_encoderFromPbStack fsp
        refine SepWP.mono
          (post := fun sm Pm =>
            (Pm ⊢
              A.pool lim (M.stepEvents (evs1 ++ w) st) sm ∗
              (stackAt fsp encoderFromPbStack ∗
               memRegion (fsp + 1392#64) 400 ∗
               memRegion (fsp + 1264#64) 80 ∗
               Frame)) ∧
            sm.sp = fsp ∧
            sm.readReg64 .x19 = out ∧
            TraceCalleeSaved sm s0)
          ?_ (fun _ _ _ _ ⟨hp, hq⟩ => ⟨evs1 ++ w, hevs1.append hevs_w, hp, hq⟩)
        refine entails_pre_st ?_ ?_
        · intro sc hsc
          rw [← hsc, M.stepEvents_append]
          refine Entails.trans
            (Entails.of_eq (show _ =
              (stackAt fsp dropStack32 ∗ memRegion (fsp - 5152#64) 1024) ∗
              (A.pool lim (M.stepEvents w (M.stepEvents evs1 st)) sc ∗
               memRegion (fsp + 1392#64) 400 ∗
               memRegion (fsp + 1264#64) 80 ∗
               Frame) by sep_ac_rfl)) ?_
          exact Entails.trans (sepConj_mono_left hst) (Entails.of_eq (by sep_ac_rfl))
        · wp_done
  · intro evs12 s3 hevs12 hpc3 hrun3 ⟨hsp3, hx19_3, htr3⟩
    have h11256 := v2hsd_cleanup_11256_to_9228_placed_budget A lim (M.stepEvents evs12 st)
      (ext := ext) s0 s3 fsp out
      (stackAt fsp encoderFromPbStack ∗
       memRegion (fsp + 1392#64) 400 ∗
       memRegion (fsp + 1264#64) 80 ∗
       Frame)
      hpc3 hrun3 hsp3 hx19_3 htr3
    refine SepWP.mono h11256 fun sm _Pm _ _ ⟨hPm, _, hsp_m, hx19_m, hx23_m, htr_m⟩ => ?_
    refine ⟨evs12, hevs12, Entails.trans hPm (Entails.of_eq (by sep_ac_rfl)),
      hsp_m, hx19_m, hx23_m, htr_m⟩

theorem v2hsd_cleanup_11240_to_9228_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 s1 : State) (fsp out : BitVec 64)
    (enc : PolyEncoder)
    (uc : CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.EkSent (spqrAuthApi F))
    (st : M.σ) (Frame : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 11240#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9228#64) s1
      (stackAt fsp encoderFromPbStack ∗
        polyEncoderAt A.repAlloc (fsp + 1392#64) enc ∗
        unchunkedEkSentAt A.repAlloc (fsp + 1264#64) uc ∗
        A.pool lim st s1 ∗
        Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          memRegion (fsp + 1392#64) 400 ∗
          memRegion (fsp + 1264#64) 80 ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x23 = 0#64 ∧
        TraceCalleeSaved sm s0) :=
  v2hsd_cleanup_11240_to_9228_of_dealloc_placed hA.dealloc s0 s1 fsp out enc uc st Frame
    hcl1 hfsp_align hpc1 hrun1 hsp1 hx19_1 htr1

/-- Execution segment `+11024 -> +11032`: drops `[Poly; 16]` at `fsp + 1400#64` (`x23 + 8#64`) and combines
    with the tag and tail to leave `memRegion (fsp + 1392#64) 400`. -/
theorem v2hsd_drop_poly16_11024_to_11032_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (s0 s1 : State) (fsp out ca3 : BitVec 64)
    (enc : PolyEncoder) (st : M.σ) (Frame : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 11024#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = fsp + 1392#64)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 11032#64) s1
      (stackAt fsp encoderFromPbStack ∗
        polyEncoderAt A.repAlloc (fsp + 1392#64) enc ∗
        A.pool lim st s1 ∗
        Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          memRegion (fsp + 1392#64) 400 ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x26 = ca3 ∧
        TraceCalleeSaved sm s0) := by
  refine SepWP.weaken_pre (v2hsd_drop_poly16_pre_pool A.repAlloc fsp enc (A.pool lim st s1) Frame) ?_
  apply ProofLib.SepWP.exists_left; intro tag
  apply ProofLib.SepWP.exists_left; intro vecs
  apply ProofLib.SepWP.pure_elim; intro hvecs_len
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine seq_clean_lscl_st hcl1
    (mid := lsmpl.base 265)
    (P_mid := fun sm =>
      vecGF16ListOf A.repAlloc (fsp + 1400#64) vecs ∗
      A.pool lim st sm ∗
      stackAt fsp dropStack32 ∗
      (memRegion (fsp - 5152#64) 1024 ∗
       ((fsp + 1392#64) ↦₆₄ tag) ∗
       memRegion (fsp + 1784#64) 8 ∗
       Frame))
    (Q := fun sm =>
      sm.sp = fsp ∧
      sm.readReg64 .x0 = fsp + 1400#64 ∧
      sm.readReg64 .lr = lsmpl.base 333 + 11032#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x26 = ca3 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · rcases htr1 with ⟨htr_1, hvregs_1⟩
    rw [← blkPl_333_base] at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsmpl.base 265) s1 _ _
    wp_steps_sync_333 (lsmpl.base 265)
    try simp only [State.setMem_setMem]
    refine align_pre_st (by sep_ac_rfl) ?_
    wp_done
  · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx0_2, hlr_2, hx19_2, hx26_2, htr2⟩
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := hsp2 ▸ hfsp_align
    have hdrop := v2hsd_sub_ok_drop_poly16_11028_of_dealloc_placed
      (M := M) (A := A) (lim := lim) hdealloc hcl2
    simp only [withMemEq, dropGluePoly16Spec, dropGluePoly16Stack] at hdrop
    dsimp only [polyArrayBytes] at hdrop
    dsimp only [lsProg_333]
    rw [← blkPl_333_base] at hlr_2 ⊢
    rw [show stackAt fsp dropStack32 = stackAt s2.sp dropStack32 from hsp2 ▸ rfl]
    wp_call hdrop ((⟨fsp + 1400#64, vecs⟩ : DropGluePoly16Ghost), st)
    rw [hsp2]
    rw [hlr_2] at *
    have hevs_w : FreeOnlyEvs w := ‹_›
    have hacp_w : AllocCallPreserved s2 sf := by
      simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
    have hsp_sf : sf.sp = fsp := ‹sf.sp = s2.sp›.trans hsp2
    have htr_sf : sf.trace = s0.trace := hacp_w.2.1.trans htr2.1
    have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
      ‹calleeSavedVRegs sf = calleeSavedVRegs s2›.trans htr2.2
    have hst := v2hsd_stackAt_dropStack32_to_encoderFromPbStack fsp
    have hjoin := v2hsd_polyEncoder_1392_join fsp tag
    refine SepWP.mono
      (post := fun sm Pm =>
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          memRegion (fsp + 1392#64) 400 ∗
          A.pool lim (M.stepEvents w st) sm ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x26 = ca3 ∧
        TraceCalleeSaved sm s0)
      ?_ (fun _ _ _ _ ⟨hp, hq⟩ => ⟨w, hevs_w, hp, hq⟩)
    refine entails_pre_st ?_ ?_
    · intro sc hsc
      rw [← hsc]
      refine Entails.trans
        (Entails.of_eq (show _ =
          (stackAt fsp dropStack32 ∗ memRegion (fsp - 5152#64) 1024) ∗
          (((fsp + 1392#64) ↦₆₄ tag) ∗
            memRegion (fsp + 1400#64) 384 ∗
            memRegion (fsp + 1784#64) 8) ∗
          (A.pool lim (M.stepEvents w st) sc ∗ Frame) by sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono hst (sepConj_mono_left hjoin)) (Entails.of_eq (by sep_ac_rfl))
    · wp_done

theorem v2hsd_drop_poly16_11024_to_11032_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 s1 : State) (fsp out ca3 : BitVec 64)
    (enc : PolyEncoder) (st : M.σ) (Frame : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 11024#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = fsp + 1392#64)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 11032#64) s1
      (stackAt fsp encoderFromPbStack ∗
        polyEncoderAt A.repAlloc (fsp + 1392#64) enc ∗
        A.pool lim st s1 ∗
        Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          memRegion (fsp + 1392#64) 400 ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x26 = ca3 ∧
        TraceCalleeSaved sm s0) :=
  v2hsd_drop_poly16_11024_to_11032_of_dealloc_placed hA.dealloc s0 s1 fsp out ca3 enc st Frame
    hcl1 hfsp_align hpc1 hrun1 hsp1 hx19_1 hx23_1 hx26_1 htr1

/-- Execution segment `+11072 -> +11256`: deallocates `(ca3, pa3)` (`x26 = ca3`, `[sp + 176] = pa3`). -/
theorem v2hsd_cleanup_11072_to_11256_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (s0 s1 : State) (fsp out ca3 pa3 : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 11072#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 11256#64) s1
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        TraceCalleeSaved sm s0) := by
  rcases htr1 with ⟨htr_1, hvregs_1⟩
  have hdealloc_fo : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (deallocFreeOnlySpec M A lim) :=
    subroutine_ok_deallocFreeOnly hdealloc_ok
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  refine SepWP.weaken_pre
    (sepConj_mono_left (v2hsc_stackAt_encoderFromPbStack_to_allocHook fsp)) ?_
  have hst := v2hsc_stackAt_allocHook_to_encoderFromPbStack fsp
  dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live,
    BitVec.ofNat_eq_ofNat, lsProg_333] at hdealloc_fo hpc1 ⊢
  rw [← blkPl_333_base] at hpc1 ⊢
  by_cases hca3 : (ca3 == 0#64) = true <;>
    simp only [hca3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · apply sepWP_evs_nil
    simp only [M.stepEvents_nil]
    wp_steps_sync_333 (lsmpl.base 333 + 11256#64)
    try simp only [State.setMem_setMem]
    refine entails_pre_st ?_ ?_
    · intro sc hsc
      rw [← hsc]
      refine Entails.trans
        (Entails.of_eq (show _ =
          (stackAt fsp allocHookStack ∗ memRegion (fsp - 5152#64) 1056) ∗
          (((fsp + 176#64) ↦₆₄ pa3) ∗ A.pool lim st sc ∗ Frame) by sep_ac_rfl)) ?_
      exact sepConj_mono_left hst
    · wp_done
  · apply sepWP_evs_dealloc ca3.toNat 1
    wp_steps_sync_333 (lsρ spqrRustDeallocSym)
    try simp only [State.setMem_setMem]
    wp_call hdealloc_fo (pa3, ca3.toNat, 1, st)
    have hacp : AllocCallPreserved s1 sf := by
      simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
    have hsp_sf : sf.sp = fsp := ‹sf.sp = _›.trans (by simp [wp_norm, arm64_norm, hsp1])
    have htr_sf : sf.trace = s0.trace := hacp.2.1.trans htr_1
    have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
      ‹calleeSavedVRegs sf = _›.trans hvregs_1
    wp_steps_sync_333 (lsmpl.base 333 + 11256#64)
    try simp only [State.setMem_setMem]
    refine entails_pre_st ?_ ?_
    · intro sc hsc
      rw [← hsc]
      simp only [wp_norm, arm64_norm, hsp1]
      refine Entails.trans
        (Entails.of_eq (show _ =
          (stackAt fsp allocHookStack ∗ memRegion (fsp - 5152#64) 1056) ∗
          (((fsp + 176#64) ↦₆₄ pa3) ∗
           A.pool lim (M.stepEvents (rustDeallocEvents ca3.toNat 1) st) sc ∗ Frame) by sep_ac_rfl)) ?_
      exact sepConj_mono_left hst
    · wp_done

theorem v2hsd_cleanup_11072_to_11256_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (s0 s1 : State) (fsp out ca3 pa3 : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 11072#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 11256#64) s1
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        TraceCalleeSaved sm s0) :=
  v2hsd_cleanup_11072_to_11256_of_sub_placed
    (v2hsc_sub_ok_dealloc_of_dealloc_placed hdealloc) s0 s1 fsp out ca3 pa3 st Frame
    hfsp_align hpc1 hrun1 hsp1 hx19_1 hx26_1 htr1

theorem v2hsd_cleanup_11072_to_11256_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 s1 : State) (fsp out ca3 pa3 : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 11072#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 11256#64) s1
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        TraceCalleeSaved sm s0) :=
  v2hsd_cleanup_11072_to_11256_of_sub_placed
    (v2hsc_sub_ok_dealloc_of_placedHooks hA) s0 s1 fsp out ca3 pa3 st Frame
    hfsp_align hpc1 hrun1 hsp1 hx19_1 hx26_1 htr1

theorem v2hsd_cleanup_11072_to_11256_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 s1 : State) (fsp out ca3 pa3 : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 11072#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 11256#64) s1
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        TraceCalleeSaved sm s0) :=
  v2hsd_cleanup_11072_to_11256_of_sub_placed
    (v2hsc_sub_ok_dealloc_placed hA) s0 s1 fsp out ca3 pa3 st Frame
    hfsp_align hpc1 hrun1 hsp1 hx19_1 hx26_1 htr1

/-- Execution segment `+11052 -> +11072`: deallocates `(ca2, pa2)` (`[sp + 232] = ca2`, `[sp + 184] = pa2`). -/
theorem v2hsd_cleanup_11052_to_11072_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (s0 s1 : State) (fsp out ca2 pa2 ca3 : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 11052#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 11072#64) s1
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 184#64) ↦₆₄ pa2) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x26 = ca3 ∧
        TraceCalleeSaved sm s0) := by
  rcases htr1 with ⟨htr_1, hvregs_1⟩
  have hdealloc_fo : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (deallocFreeOnlySpec M A lim) :=
    subroutine_ok_deallocFreeOnly hdealloc_ok
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  refine SepWP.weaken_pre
    (sepConj_mono_left (v2hsc_stackAt_encoderFromPbStack_to_allocHook fsp)) ?_
  have hst := v2hsc_stackAt_allocHook_to_encoderFromPbStack fsp
  dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live,
    BitVec.ofNat_eq_ofNat, lsProg_333] at hdealloc_fo hpc1 ⊢
  rw [← blkPl_333_base] at hpc1 ⊢
  by_cases hca2 : (ca2 == 0#64) = true <;>
    simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · apply sepWP_evs_nil
    simp only [M.stepEvents_nil]
    wp_steps_sync_333 (lsmpl.base 333 + 11072#64)
    try simp only [State.setMem_setMem]
    refine entails_pre_st ?_ ?_
    · intro sc hsc
      rw [← hsc]
      refine Entails.trans
        (Entails.of_eq (show _ =
          (stackAt fsp allocHookStack ∗ memRegion (fsp - 5152#64) 1056) ∗
          (((fsp + 232#64) ↦₆₄ ca2) ∗
           ((fsp + 184#64) ↦₆₄ pa2) ∗ A.pool lim st sc ∗ Frame) by sep_ac_rfl)) ?_
      exact sepConj_mono_left hst
    · wp_done
  · apply sepWP_evs_dealloc ca2.toNat 1
    wp_steps_sync_333 (lsρ spqrRustDeallocSym)
    try simp only [State.setMem_setMem]
    wp_call hdealloc_fo (pa2, ca2.toNat, 1, st)
    have hacp : AllocCallPreserved s1 sf := by
      simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
    have hsp_sf : sf.sp = fsp := ‹sf.sp = _›.trans (by simp [wp_norm, arm64_norm, hsp1])
    have htr_sf : sf.trace = s0.trace := hacp.2.1.trans htr_1
    have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
      ‹calleeSavedVRegs sf = _›.trans hvregs_1
    refine entails_pre_st ?_ ?_
    · intro sc hsc
      rw [← hsc]
      simp only [wp_norm, arm64_norm, hsp1]
      refine Entails.trans
        (Entails.of_eq (show _ =
          (stackAt fsp allocHookStack ∗ memRegion (fsp - 5152#64) 1056) ∗
          (((fsp + 232#64) ↦₆₄ ca2) ∗
           ((fsp + 184#64) ↦₆₄ pa2) ∗
           A.pool lim (M.stepEvents (rustDeallocEvents ca2.toNat 1) st) sc ∗ Frame) by sep_ac_rfl)) ?_
      exact sepConj_mono_left hst
    · wp_done

theorem v2hsd_cleanup_11052_to_11072_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (s0 s1 : State) (fsp out ca2 pa2 ca3 : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 11052#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 11072#64) s1
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 184#64) ↦₆₄ pa2) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x26 = ca3 ∧
        TraceCalleeSaved sm s0) :=
  v2hsd_cleanup_11052_to_11072_of_sub_placed
    (v2hsc_sub_ok_dealloc_of_dealloc_placed hdealloc) s0 s1 fsp out ca2 pa2 ca3 st Frame
    hfsp_align hpc1 hrun1 hsp1 hx19_1 hx26_1 htr1

theorem v2hsd_cleanup_11052_to_11072_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 s1 : State) (fsp out ca2 pa2 ca3 : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 11052#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 11072#64) s1
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 184#64) ↦₆₄ pa2) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x26 = ca3 ∧
        TraceCalleeSaved sm s0) :=
  v2hsd_cleanup_11052_to_11072_of_sub_placed
    (v2hsc_sub_ok_dealloc_of_placedHooks hA) s0 s1 fsp out ca2 pa2 ca3 st Frame
    hfsp_align hpc1 hrun1 hsp1 hx19_1 hx26_1 htr1

theorem v2hsd_cleanup_11052_to_11072_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 s1 : State) (fsp out ca2 pa2 ca3 : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 11052#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 11072#64) s1
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 184#64) ↦₆₄ pa2) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x26 = ca3 ∧
        TraceCalleeSaved sm s0) :=
  v2hsd_cleanup_11052_to_11072_of_sub_placed
    (v2hsc_sub_ok_dealloc_placed hA) s0 s1 fsp out ca2 pa2 ca3 st Frame
    hfsp_align hpc1 hrun1 hsp1 hx19_1 hx26_1 htr1

/-- Execution segment `+11032 -> +11052`: deallocates `(ca1, pa1)` (`[sp + 200] = ca1`, `[sp + 1272] = pa1`). -/
theorem v2hsd_cleanup_11032_to_11052_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (s0 s1 : State) (fsp out ca1 pa1 ca3 : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 11032#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 11052#64) s1
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 200#64) ↦₆₄ ca1) ∗
        ((fsp + 1272#64) ↦₆₄ pa1) ∗
        vecCapPtrDealloc A.repAlloc ca1 pa1 ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          ((fsp + 200#64) ↦₆₄ ca1) ∗
          ((fsp + 1272#64) ↦₆₄ pa1) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x26 = ca3 ∧
        TraceCalleeSaved sm s0) := by
  rcases htr1 with ⟨htr_1, hvregs_1⟩
  have hdealloc_fo : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (deallocFreeOnlySpec M A lim) :=
    subroutine_ok_deallocFreeOnly hdealloc_ok
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  refine SepWP.weaken_pre
    (sepConj_mono_left (v2hsc_stackAt_encoderFromPbStack_to_allocHook fsp)) ?_
  have hst := v2hsc_stackAt_allocHook_to_encoderFromPbStack fsp
  dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live,
    BitVec.ofNat_eq_ofNat, lsProg_333] at hdealloc_fo hpc1 ⊢
  rw [← blkPl_333_base] at hpc1 ⊢
  by_cases hca1 : (ca1 == 0#64) = true <;>
    simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · apply sepWP_evs_nil
    simp only [M.stepEvents_nil]
    wp_steps_sync_333 (lsmpl.base 333 + 11052#64)
    try simp only [State.setMem_setMem]
    refine entails_pre_st ?_ ?_
    · intro sc hsc
      rw [← hsc]
      refine Entails.trans
        (Entails.of_eq (show _ =
          (stackAt fsp allocHookStack ∗ memRegion (fsp - 5152#64) 1056) ∗
          (((fsp + 200#64) ↦₆₄ ca1) ∗
           ((fsp + 1272#64) ↦₆₄ pa1) ∗ A.pool lim st sc ∗ Frame) by sep_ac_rfl)) ?_
      exact sepConj_mono_left hst
    · wp_done
  · apply sepWP_evs_dealloc ca1.toNat 1
    wp_steps_sync_333 (lsρ spqrRustDeallocSym)
    try simp only [State.setMem_setMem]
    wp_call hdealloc_fo (pa1, ca1.toNat, 1, st)
    have hacp : AllocCallPreserved s1 sf := by
      simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
    have hsp_sf : sf.sp = fsp := ‹sf.sp = _›.trans (by simp [wp_norm, arm64_norm, hsp1])
    have htr_sf : sf.trace = s0.trace := hacp.2.1.trans htr_1
    have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
      ‹calleeSavedVRegs sf = _›.trans hvregs_1
    refine entails_pre_st ?_ ?_
    · intro sc hsc
      rw [← hsc]
      simp only [wp_norm, arm64_norm, hsp1]
      refine Entails.trans
        (Entails.of_eq (show _ =
          (stackAt fsp allocHookStack ∗ memRegion (fsp - 5152#64) 1056) ∗
          (((fsp + 200#64) ↦₆₄ ca1) ∗
           ((fsp + 1272#64) ↦₆₄ pa1) ∗
           A.pool lim (M.stepEvents (rustDeallocEvents ca1.toNat 1) st) sc ∗ Frame) by sep_ac_rfl)) ?_
      exact sepConj_mono_left hst
    · wp_done

theorem v2hsd_cleanup_11032_to_11052_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (s0 s1 : State) (fsp out ca1 pa1 ca3 : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 11032#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 11052#64) s1
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 200#64) ↦₆₄ ca1) ∗
        ((fsp + 1272#64) ↦₆₄ pa1) ∗
        vecCapPtrDealloc A.repAlloc ca1 pa1 ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          ((fsp + 200#64) ↦₆₄ ca1) ∗
          ((fsp + 1272#64) ↦₆₄ pa1) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x26 = ca3 ∧
        TraceCalleeSaved sm s0) :=
  v2hsd_cleanup_11032_to_11052_of_sub_placed
    (v2hsc_sub_ok_dealloc_of_dealloc_placed hdealloc) s0 s1 fsp out ca1 pa1 ca3 st Frame
    hfsp_align hpc1 hrun1 hsp1 hx19_1 hx26_1 htr1

theorem v2hsd_cleanup_11032_to_11052_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 s1 : State) (fsp out ca1 pa1 ca3 : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 11032#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 11052#64) s1
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 200#64) ↦₆₄ ca1) ∗
        ((fsp + 1272#64) ↦₆₄ pa1) ∗
        vecCapPtrDealloc A.repAlloc ca1 pa1 ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          ((fsp + 200#64) ↦₆₄ ca1) ∗
          ((fsp + 1272#64) ↦₆₄ pa1) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x26 = ca3 ∧
        TraceCalleeSaved sm s0) :=
  v2hsd_cleanup_11032_to_11052_of_sub_placed
    (v2hsc_sub_ok_dealloc_of_placedHooks hA) s0 s1 fsp out ca1 pa1 ca3 st Frame
    hfsp_align hpc1 hrun1 hsp1 hx19_1 hx26_1 htr1

theorem v2hsd_cleanup_11032_to_11052_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 s1 : State) (fsp out ca1 pa1 ca3 : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 11032#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 11052#64) s1
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 200#64) ↦₆₄ ca1) ∗
        ((fsp + 1272#64) ↦₆₄ pa1) ∗
        vecCapPtrDealloc A.repAlloc ca1 pa1 ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          ((fsp + 200#64) ↦₆₄ ca1) ∗
          ((fsp + 1272#64) ↦₆₄ pa1) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x26 = ca3 ∧
        TraceCalleeSaved sm s0) :=
  v2hsd_cleanup_11032_to_11052_of_sub_placed
    (v2hsc_sub_ok_dealloc_placed hA) s0 s1 fsp out ca1 pa1 ca3 st Frame
    hfsp_align hpc1 hrun1 hsp1 hx19_1 hx26_1 htr1

/-- Full cleanup at `+11024 -> +9228` (`receivingCt1 = none`): drops `[Poly; 16]` at `fsp + 1400`,
    deallocates `(ca1, pa1)`, `(ca2, pa2)`, `(ca3, pa3)`, sets `x23 = 0#64`, and reaches `+9228`. -/
theorem v2hsd_cleanup_11024_to_9228_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (s0 s1 : State) (fsp out ca1 pa1 ca2 pa2 ca3 pa3 : BitVec 64)
    (enc : PolyEncoder) (st : M.σ) (Frame : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 11024#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = fsp + 1392#64)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9228#64) s1
      (stackAt fsp encoderFromPbStack ∗
        polyEncoderAt A.repAlloc (fsp + 1392#64) enc ∗
        ((fsp + 200#64) ↦₆₄ ca1) ∗
        ((fsp + 1272#64) ↦₆₄ pa1) ∗
        ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        vecCapPtrDealloc A.repAlloc ca1 pa1 ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          memRegion (fsp + 1392#64) 400 ∗
          ((fsp + 200#64) ↦₆₄ ca1) ∗
          ((fsp + 1272#64) ↦₆₄ pa1) ∗
          ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 184#64) ↦₆₄ pa2) ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x23 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  refine seq_clean_evs
    (mid := lsmpl.base 333 + 11032#64)
    (P_evs := fun evs1 sm =>
      stackAt fsp encoderFromPbStack ∗
      ((fsp + 200#64) ↦₆₄ ca1) ∗
      ((fsp + 1272#64) ↦₆₄ pa1) ∗
      vecCapPtrDealloc A.repAlloc ca1 pa1 ∗
      A.pool lim (M.stepEvents evs1 st) sm ∗
      (memRegion (fsp + 1392#64) 400 ∗
       ((fsp + 232#64) ↦₆₄ ca2) ∗
       ((fsp + 184#64) ↦₆₄ pa2) ∗
       ((fsp + 176#64) ↦₆₄ pa3) ∗
       vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
       vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
       Frame))
    (Q := fun sm =>
      sm.sp = fsp ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x26 = ca3 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · have h11024 := v2hsd_drop_poly16_11024_to_11032_of_dealloc_placed hdealloc s0 s1 fsp out ca3 enc st
      (((fsp + 200#64) ↦₆₄ ca1) ∗
       ((fsp + 1272#64) ↦₆₄ pa1) ∗
       ((fsp + 232#64) ↦₆₄ ca2) ∗
       ((fsp + 184#64) ↦₆₄ pa2) ∗
       ((fsp + 176#64) ↦₆₄ pa3) ∗
       vecCapPtrDealloc A.repAlloc ca1 pa1 ∗
       vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
       vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
       Frame)
      hcl1 hfsp_align hpc1 hrun1 hsp1 hx19_1 hx23_1 hx26_1 htr1
    exact SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (SepWP.mono h11024 fun sm _Pm _ _ ⟨evs, hevs, hPm, hq⟩ =>
        ⟨evs, hevs, Entails.trans hPm (Entails.of_eq (by sep_ac_rfl)), hq⟩)
  · intro evs1 s2 hevs1 hpc2 hrun2 ⟨hsp2, hx19_2, hx26_2, htr2⟩
    refine seq_clean_evs
      (mid := lsmpl.base 333 + 11052#64)
      (P_evs := fun evs2 sm =>
        stackAt fsp encoderFromPbStack ∗
        ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        A.pool lim (M.stepEvents (evs1 ++ evs2) st) sm ∗
        (memRegion (fsp + 1392#64) 400 ∗
         ((fsp + 200#64) ↦₆₄ ca1) ∗
         ((fsp + 1272#64) ↦₆₄ pa1) ∗
         ((fsp + 176#64) ↦₆₄ pa3) ∗
         vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
         Frame))
      (Q := fun sm =>
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x26 = ca3 ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · have h11032 := v2hsd_cleanup_11032_to_11052_of_dealloc_placed hdealloc s0 s2 fsp out
        ca1 pa1 ca3 (M.stepEvents evs1 st)
        (memRegion (fsp + 1392#64) 400 ∗
         ((fsp + 232#64) ↦₆₄ ca2) ∗
         ((fsp + 184#64) ↦₆₄ pa2) ∗
         ((fsp + 176#64) ↦₆₄ pa3) ∗
         vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
         vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
         Frame)
        hfsp_align hpc2 hrun2 hsp2 hx19_2 hx26_2 htr2
      refine SepWP.mono h11032 fun sm _Pm _ _ ⟨evs2, hevs2, hPm, hq⟩ => ?_
      refine ⟨evs2, hevs2, ?_, hq⟩
      rw [M.stepEvents_append]
      exact Entails.trans hPm (Entails.of_eq (by sep_ac_rfl))
    · intro evs2 s3 hevs2 hpc3 hrun3 ⟨hsp3, hx19_3, hx26_3, htr3⟩
      refine seq_clean_evs
        (mid := lsmpl.base 333 + 11072#64)
        (P_evs := fun evs3 sm =>
          stackAt fsp encoderFromPbStack ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
          A.pool lim (M.stepEvents ((evs1 ++ evs2) ++ evs3) st) sm ∗
          (memRegion (fsp + 1392#64) 400 ∗
           ((fsp + 200#64) ↦₆₄ ca1) ∗
           ((fsp + 1272#64) ↦₆₄ pa1) ∗
           ((fsp + 232#64) ↦₆₄ ca2) ∗
           ((fsp + 184#64) ↦₆₄ pa2) ∗
           Frame))
        (Q := fun sm =>
          sm.sp = fsp ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x26 = ca3 ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · have h11052 := v2hsd_cleanup_11052_to_11072_of_dealloc_placed hdealloc s0 s3 fsp out
          ca2 pa2 ca3 (M.stepEvents (evs1 ++ evs2) st)
          (memRegion (fsp + 1392#64) 400 ∗
           ((fsp + 200#64) ↦₆₄ ca1) ∗
           ((fsp + 1272#64) ↦₆₄ pa1) ∗
           ((fsp + 176#64) ↦₆₄ pa3) ∗
           vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
           Frame)
          hfsp_align hpc3 hrun3 hsp3 hx19_3 hx26_3 htr3
        refine SepWP.mono h11052 fun sm _Pm _ _ ⟨evs3, hevs3, hPm, hq⟩ => ?_
        refine ⟨evs3, hevs3, ?_, hq⟩
        rw [M.stepEvents_append]
        exact Entails.trans hPm (Entails.of_eq (by sep_ac_rfl))
      · intro evs3 s4 hevs3 hpc4 hrun4 ⟨hsp4, hx19_4, hx26_4, htr4⟩
        refine seq_clean_evs
          (mid := lsmpl.base 333 + 11256#64)
          (P_evs := fun evs4 sm =>
            A.pool lim (M.stepEvents (((evs1 ++ evs2) ++ evs3) ++ evs4) st) sm ∗
            (stackAt fsp encoderFromPbStack ∗
             memRegion (fsp + 1392#64) 400 ∗
             ((fsp + 200#64) ↦₆₄ ca1) ∗
             ((fsp + 1272#64) ↦₆₄ pa1) ∗
             ((fsp + 232#64) ↦₆₄ ca2) ∗
             ((fsp + 184#64) ↦₆₄ pa2) ∗
             ((fsp + 176#64) ↦₆₄ pa3) ∗
             Frame))
          (Q := fun sm =>
            sm.sp = fsp ∧
            sm.readReg64 .x19 = out ∧
            TraceCalleeSaved sm s0)
          ?_ ?_
        · have h11072 := v2hsd_cleanup_11072_to_11256_of_dealloc_placed hdealloc s0 s4 fsp out
            ca3 pa3 (M.stepEvents ((evs1 ++ evs2) ++ evs3) st)
            (memRegion (fsp + 1392#64) 400 ∗
             ((fsp + 200#64) ↦₆₄ ca1) ∗
             ((fsp + 1272#64) ↦₆₄ pa1) ∗
             ((fsp + 232#64) ↦₆₄ ca2) ∗
             ((fsp + 184#64) ↦₆₄ pa2) ∗
             Frame)
            hfsp_align hpc4 hrun4 hsp4 hx19_4 hx26_4 htr4
          refine SepWP.mono h11072 fun sm _Pm _ _ ⟨evs4, hevs4, hPm, hq⟩ => ?_
          refine ⟨evs4, hevs4, ?_, hq⟩
          rw [M.stepEvents_append]
          exact Entails.trans hPm (Entails.of_eq (by sep_ac_rfl))
        · intro evs4 s5 hevs4 hpc5 hrun5 ⟨hsp5, hx19_5, htr5⟩
          have h11256 := v2hsd_cleanup_11256_to_9228_placed_budget A lim
            (M.stepEvents (((evs1 ++ evs2) ++ evs3) ++ evs4) st)
            (ext := ext) s0 s5 fsp out
            (stackAt fsp encoderFromPbStack ∗
             memRegion (fsp + 1392#64) 400 ∗
             ((fsp + 200#64) ↦₆₄ ca1) ∗
             ((fsp + 1272#64) ↦₆₄ pa1) ∗
             ((fsp + 232#64) ↦₆₄ ca2) ∗
             ((fsp + 184#64) ↦₆₄ pa2) ∗
             ((fsp + 176#64) ↦₆₄ pa3) ∗
             Frame)
            hpc5 hrun5 hsp5 hx19_5 htr5
          refine SepWP.mono h11256 fun sm _Pm _ _ ⟨hPm, _, hsp_m, hx19_m, hx23_m, htr_m⟩ => ?_
          refine ⟨((evs1 ++ evs2) ++ evs3) ++ evs4,
            ((hevs1.append hevs2).append hevs3).append hevs4,
            Entails.trans hPm (Entails.of_eq (by sep_ac_rfl)),
            hsp_m, hx19_m, hx23_m, htr_m⟩

theorem v2hsd_cleanup_11024_to_9228_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 s1 : State) (fsp out ca1 pa1 ca2 pa2 ca3 pa3 : BitVec 64)
    (enc : PolyEncoder) (st : M.σ) (Frame : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 11024#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = fsp + 1392#64)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9228#64) s1
      (stackAt fsp encoderFromPbStack ∗
        polyEncoderAt A.repAlloc (fsp + 1392#64) enc ∗
        ((fsp + 200#64) ↦₆₄ ca1) ∗
        ((fsp + 1272#64) ↦₆₄ pa1) ∗
        ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        vecCapPtrDealloc A.repAlloc ca1 pa1 ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          memRegion (fsp + 1392#64) 400 ∗
          ((fsp + 200#64) ↦₆₄ ca1) ∗
          ((fsp + 1272#64) ↦₆₄ pa1) ∗
          ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 184#64) ↦₆₄ pa2) ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x23 = 0#64 ∧
        TraceCalleeSaved sm s0) :=
  v2hsd_cleanup_11024_to_9228_of_dealloc_placed hA.dealloc s0 s1 fsp out
    ca1 pa1 ca2 pa2 ca3 pa3 enc st Frame hcl1 hfsp_align hpc1 hrun1 hsp1 hx19_1 hx23_1 hx26_1 htr1

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsdPlacedBudget

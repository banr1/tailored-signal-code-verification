/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.GenLsBlock
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommonBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1BudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1ClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag11
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag11ClPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Code-Loaded Helpers for `V1State::merge` Tag Arm 11 (`Ct2Sampled`)

`RustCliAllocBudget`-threaded `[LibsignalPlacement]` error-path heap deallocation, setup, stack
copy, and `withLsCl`-wrapped drop helpers (`271`, `267`) for tag arm 11 (`Ct2Sampled`, Block `298`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag11ClPlacedBudgetAux

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget VmPreserved
   rustCliDeallocBudgetSpec rustDeallocEvents)
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget (dropProtoPolyEncoderSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget (dropOptProtoInnerStatePlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommonBudget
  (ChunkedCt2SampledMergeEnv ChunkedCt2SampledMergePostEnv
   chunkedCt2SampledMergeSpec chunkedCt2SampledMergeSpecOfEnv ct2SampledPolyCapBound)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefsBudget
  (optInnerStatePolyCapBound v1StateErrFramePlaced v1StateLoopPrePlaced v1StateMergePlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1BudgetAux
  (V1StateTagContPlaced V1StateTagEntryBudgetPlaced V1StateTagStepHypPlaced WppPanicFalse
   align_pre ct2SampledPolyCapBound_le deallocFreeOnlySpec freeOnlyEvs_rustDeallocEvents
   optInnerStatePolyCapBound_ge_len optInnerStatePolyCapBound_of_ct2Sampled
   pool_eq_of_vmPreserved sepWPp_congr_state_pre stepEvents_append_eq subroutine_ok_deallocFreeOnly
   tag_err_env_inplace tag_err_env_of_free tag_fitsEnv_sub
   tag_ok_env_inplace tag_ok_env_of_free wppPanicFalse_of_false)
open CryptoVerification (LibsignalCodeLoaded LibsignalPlacement lsmpl lsρ sepWP_seq_lscl withLsCl)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalProtoCodec (WireType)
open CryptoVerification.LibsignalTripleRatchet (decodeErrorAtStackLen withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (pointsToBytes_prefix_join sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join sliceCursorAt)
open CryptoVerification.LibsignalSpqrV1 (PolynomialEncoder V1State pbToProtoPolyEncoder)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.ProtoRepr (noneCap2)
open CryptoVerification.SpqrV1.Poly (optProtoPolynomialEncoderAt protoPolynomialEncoderSize)
open CryptoVerification.SpqrV1.Drop
  (cap_add_one_beq_zero_false dropStack48 dropStack96
   optProtoInnerStateAt optProtoInnerStateJumpTablePlacedAt optProtoInnerStateSize
   optProtoPolyEncoder_none_entails_memRegion_56
   optProtoPolynomialEncoderAt_none' optProtoPolynomialEncoderAt_some'
   protoPolynomialEncoderAt_expose_cap protoPolynomialEncoderAt_unexpose_cap
   vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (InnerStateDiscrFull InnerStatePolyBound OptInnerStatePolyBound OptPolyEncoderBound
   SepWPp.call_frame_lscro SepWPp.of_sepWP_lscro
   V1StateMergeGhost WppPost
   bv64_add_zero bv64_sub_zero
   chunkedCt2SampledPBAt chunkedCt2SampledPBAt_eq_proto
   chunkedCt2SampledPBCapAt chunkedInlStack
   codecWireTypeToProto discrFull_none_add2 discrFull_some_add2
   innerStatePolyBound_of_ct2Sampled memRegion_56_eq_words7
   optInnerStatePolyBound_lt_2_56 optPolyEncoderBound_none
   optPolyEncoderPolysLen optPolyEncoderPtsLen
   optProtoInnerStateAt_entails_exists optProtoInnerStateCapAt optProtoInnerStateCapAt_entails_pb
   protoInnerStateCapAt proto_mergeMessage_len_le
   v1StateBelowRest v1StateBelow_allocHook v1StateBelow_allocHook_entails
   v1StateBelow_dropStack48 v1StateBelow_dropStack48_entails
   v1StateBelow_dropStack96 v1StateBelow_dropStack96_entails
   v1StateJumpTablesPlacedAt v1StateMergeJumpTablePlacedExpanded v1StateSavedRegsAt
   v1State_mergeField_tag11
   v1Tag11_capHeap v1Tag11_discrFull_other v1Tag11_extract_words
   v1Tag11_memRegion_112_eq_words14 v1Tag11_memRegion_112_split_init
   v1Tag11_memRegion_224_split_ok v1Tag11_memRegion_fold_temp v1Tag11_memRegion_split_temp
   v1Tag11_pb_entails_cap_zero v1Tag11_reconstruct_innerState
   v1Tag11_words14At v1Tag11_words14At_entails_memRegion_112
   v1Tag11_words_entails_err_dealloc
   words7At)
open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2 (blkPC_298 blkPl_298)
open scoped CryptoVerification.SpqrV1.Prost.MessageMerge.Part2

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
  v1StateMergeJumpTablePlacedExpanded optProtoInnerStateJumpTablePlacedAt v1StateSavedRegsAt
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  CryptoVerification.SpqrV1.ProtoRepr.EncodedLen.noneCap_add_one_beq_zero
  CryptoVerification.SpqrV1.ProtoRepr.EncodedLen.noneCap_add_one_bne_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero

private theorem repAlloc_live_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (p : BitVec 64) (n a : Nat) : A.repAlloc.live p n a = A.live p n a := rfl

private theorem sepWP_mono_freeOnly {prog : Program} {tgt : BitVec 64} {s : State} {Pre : SepProp}
    {evs : List AllocEvent} (hevs : FreeOnlyEvs evs)
    {Q : List AllocEvent → State → SepProp → Prop}
    (h : SepWP prog tgt s Pre (Q evs)) :
    SepWP prog tgt s Pre (fun sm Pm => ∃ evs', FreeOnlyEvs evs' ∧ Q evs' sm Pm) :=
  SepWP.mono h fun _ _ _ _ hq => ⟨evs, hevs, hq⟩

/-! ## 1. Error-Path Heap Deallocation & Drop Helpers (`+1864..+1944`) -/

private theorem v1Tag11_err_dealloc_w7_1884_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hDealloc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustCliDeallocBudgetSpec M A lim))
    {s : State} {st : M.σ} {fsp w7 w8 w9 w10 w11 w12 w13 : BitVec 64} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1884#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = w7) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 1900#64) s
      (words7At (fsp + 296#64) w7 w8 w9 w10 w11 w12 w13 ∗
        vecCapPtrDealloc A.repAlloc w7 w8 ∗ A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ words7At (fsp + 296#64) w7 w8 w9 w10 w11 w12 w13 ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) := by
  have hDealloc' := subroutine_ok_deallocFreeOnly hDealloc
  dsimp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hDealloc'
  have h304 : (fsp + 296#64) + 8#64 = fsp + 304#64 := by bv_lin
  have h312 : (fsp + 296#64) + 16#64 = fsp + 312#64 := by bv_lin
  have h320 : (fsp + 296#64) + 24#64 = fsp + 320#64 := by bv_lin
  have h328 : (fsp + 296#64) + 32#64 = fsp + 328#64 := by bv_lin
  have h336 : (fsp + 296#64) + 40#64 = fsp + 336#64 := by bv_lin
  have h344 : (fsp + 296#64) + 48#64 = fsp + 344#64 := by bv_lin
  dsimp only [words7At, vecCapPtrDealloc]
  rw [h304, h312, h320, h328, h336, h344]
  by_cases hw7 : (w7 == 0#64) = true <;>
    simp only [hw7, ↓reduceIte, Bool.false_eq_true, emp_sepConj]
  · have hbr : (s.readReg64 (Reg.gpr 1#5) == 0#64) = true := by rw [hx1]; exact hw7
    refine SepWP.mono (post := fun sm Pm =>
      (Pm ⊢ ((fsp + 296#64) ↦₆₄ w7 ∗ (fsp + 304#64) ↦₆₄ w8 ∗ (fsp + 312#64) ↦₆₄ w9 ∗
        (fsp + 320#64) ↦₆₄ w10 ∗ (fsp + 328#64) ↦₆₄ w11 ∗ (fsp + 336#64) ↦₆₄ w12 ∗
        (fsp + 344#64) ↦₆₄ w13) ∗
        A.pool lim (M.stepEvents [] st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
      sm.sp = s.sp ∧ sm.v1TraceEq s ∧
      sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) ?_
      (fun _ _ _ _ h => ⟨[], FreeOnlyEvs.nil, h⟩)
    dsimp only [AllocCostModel.stepEvents]
    wp_steps_sync_pool ((blkPl_298).base + 1900#64)
    wp_done
  · have hbr : (s.readReg64 (Reg.gpr 1#5) == 0#64) = false := by
      rw [hx1]; exact Bool.eq_false_iff.mpr hw7
    refine SepWP.mono (post := fun sm Pm =>
      (Pm ⊢ ((fsp + 296#64) ↦₆₄ w7 ∗ (fsp + 304#64) ↦₆₄ w8 ∗ (fsp + 312#64) ↦₆₄ w9 ∗
        (fsp + 320#64) ↦₆₄ w10 ∗ (fsp + 328#64) ↦₆₄ w11 ∗ (fsp + 336#64) ↦₆₄ w12 ∗
        (fsp + 344#64) ↦₆₄ w13) ∗
        A.pool lim (M.stepEvents (rustDeallocEvents w7.toNat 1) st) sm ∗
        stackAt fsp allocHookStack ∗ Frame) ∧
      sm.sp = s.sp ∧ sm.v1TraceEq s ∧
      sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) ?_
      (fun _ _ _ _ h => ⟨rustDeallocEvents w7.toNat 1, freeOnlyEvs_rustDeallocEvents w7.toNat 1, h⟩)
    rw [repAlloc_live_eq A]
    wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
    wp_apply
    exact align_pre (by rw [hsp]) (by wp_done)

private theorem v1Tag11_err_dealloc_w10_1900_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hDealloc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustCliDeallocBudgetSpec M A lim))
    {s : State} {st : M.σ} {fsp w7 w8 w9 w10 w11 w12 w13 : BitVec 64} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1900#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 1920#64) s
      (words7At (fsp + 296#64) w7 w8 w9 w10 w11 w12 w13 ∗
        vecCapPtrDealloc A.repAlloc w10 w11 ∗ A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ words7At (fsp + 296#64) w7 w8 w9 w10 w11 w12 w13 ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) := by
  have hDealloc' := subroutine_ok_deallocFreeOnly hDealloc
  dsimp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hDealloc'
  have h304 : (fsp + 296#64) + 8#64 = fsp + 304#64 := by bv_lin
  have h312 : (fsp + 296#64) + 16#64 = fsp + 312#64 := by bv_lin
  have h320 : (fsp + 296#64) + 24#64 = fsp + 320#64 := by bv_lin
  have h328 : (fsp + 296#64) + 32#64 = fsp + 328#64 := by bv_lin
  have h336 : (fsp + 296#64) + 40#64 = fsp + 336#64 := by bv_lin
  have h344 : (fsp + 296#64) + 48#64 = fsp + 344#64 := by bv_lin
  dsimp only [words7At, vecCapPtrDealloc]
  rw [h304, h312, h320, h328, h336, h344]
  by_cases hw10 : (w10 == 0#64) = true <;>
    simp only [hw10, ↓reduceIte, Bool.false_eq_true, emp_sepConj]
  · refine SepWP.mono (post := fun sm Pm =>
      (Pm ⊢ ((fsp + 296#64) ↦₆₄ w7 ∗ (fsp + 304#64) ↦₆₄ w8 ∗ (fsp + 312#64) ↦₆₄ w9 ∗
        (fsp + 320#64) ↦₆₄ w10 ∗ (fsp + 328#64) ↦₆₄ w11 ∗ (fsp + 336#64) ↦₆₄ w12 ∗
        (fsp + 344#64) ↦₆₄ w13) ∗
        A.pool lim (M.stepEvents [] st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
      sm.sp = s.sp ∧ sm.v1TraceEq s ∧
      sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) ?_
      (fun _ _ _ _ h => ⟨[], FreeOnlyEvs.nil, h⟩)
    dsimp only [AllocCostModel.stepEvents]
    wp_steps_sync_pool ((blkPl_298).base + 1920#64)
    wp_done
  · have hbr : (w10 == 0#64) = false := Bool.eq_false_iff.mpr hw10
    refine SepWP.mono (post := fun sm Pm =>
      (Pm ⊢ ((fsp + 296#64) ↦₆₄ w7 ∗ (fsp + 304#64) ↦₆₄ w8 ∗ (fsp + 312#64) ↦₆₄ w9 ∗
        (fsp + 320#64) ↦₆₄ w10 ∗ (fsp + 328#64) ↦₆₄ w11 ∗ (fsp + 336#64) ↦₆₄ w12 ∗
        (fsp + 344#64) ↦₆₄ w13) ∗
        A.pool lim (M.stepEvents (rustDeallocEvents w10.toNat 1) st) sm ∗
        stackAt fsp allocHookStack ∗ Frame) ∧
      sm.sp = s.sp ∧ sm.v1TraceEq s ∧
      sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) ?_
      (fun _ _ _ _ h => ⟨rustDeallocEvents w10.toNat 1, freeOnlyEvs_rustDeallocEvents w10.toNat 1, h⟩)
    rw [repAlloc_live_eq A]
    wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
    wp_apply
    exact align_pre (by rw [hsp]) (by wp_done)

theorem v1Tag11_err_uc_1864_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hDealloc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustCliDeallocBudgetSpec M A lim))
    {s : State} {st : M.σ} {fsp w7 w8 w9 w10 w11 w12 w13 : BitVec 64} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1864#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 1920#64) s
      (words7At (fsp + 296#64) w7 w8 w9 w10 w11 w12 w13 ∗
        (if (w7 + 2#64 == 0#64) || (w7 + 1#64 == 0#64) then emp
         else vecCapPtrDealloc A.repAlloc w7 w8 ∗ vecCapPtrDealloc A.repAlloc w10 w11) ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ memRegion (fsp + 296#64) 56 ∗ A.pool lim (M.stepEvents evs st) sm ∗
          stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) := by
  have hfold56 : words7At (fsp + 296#64) w7 w8 w9 w10 w11 w12 w13 ⊢ memRegion (fsp + 296#64) 56 := by
    rw [memRegion_56_eq_words7 (fsp + 296#64)]
    refine Entails.trans ?_ (Entails.sepExists_intro w13); refine Entails.trans ?_ (Entails.sepExists_intro w12)
    refine Entails.trans ?_ (Entails.sepExists_intro w11); refine Entails.trans ?_ (Entails.sepExists_intro w10)
    refine Entails.trans ?_ (Entails.sepExists_intro w9); refine Entails.trans ?_ (Entails.sepExists_intro w8)
    refine Entails.trans ?_ (Entails.sepExists_intro w7); exact Entails.refl _
  by_cases h2 : (w7 + 2#64 == 0#64) = true
  · simp only [h2, Bool.true_or, ↓reduceIte, emp_sepConj]
    dsimp only [words7At] at hfold56 ⊢
    refine SepWP.mono (post := fun sm Pm =>
      (Pm ⊢ memRegion (fsp + 296#64) 56 ∗ A.pool lim (M.stepEvents [] st) sm ∗
        stackAt fsp allocHookStack ∗ Frame) ∧
      sm.sp = s.sp ∧ sm.v1TraceEq s ∧
      sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) ?_
      (fun _ _ _ _ h => ⟨[], FreeOnlyEvs.nil, h⟩)
    dsimp only [AllocCostModel.stepEvents]
    wp_steps_sync_pool ((blkPl_298).base + 1920#64)
    apply SepWP.fold hfold56 (by sep_focus)
    wp_done
  · have h2f : (w7 + 2#64 == 0#64) = false := Bool.eq_false_iff.mpr h2
    by_cases h1 : (w7 + 1#64 == 0#64) = true
    · simp only [h2f, h1, Bool.or_true, ↓reduceIte, emp_sepConj]
      dsimp only [words7At] at hfold56 ⊢
      refine SepWP.mono (post := fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 296#64) 56 ∗ A.pool lim (M.stepEvents [] st) sm ∗
          stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) ?_
        (fun _ _ _ _ h => ⟨[], FreeOnlyEvs.nil, h⟩)
      dsimp only [AllocCostModel.stepEvents]
      wp_steps_sync_pool ((blkPl_298).base + 1920#64)
      apply SepWP.fold hfold56 (by sep_focus)
      wp_done
    · have h1f : (w7 + 1#64 == 0#64) = false := Bool.eq_false_iff.mpr h1
      simp only [h2f, h1f, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
      have hstep1 : SepWP ((blkPC_298).rebase (blkPl_298).base H)
          ((blkPl_298).base + 1884#64) s
          (words7At (fsp + 296#64) w7 w8 w9 w10 w11 w12 w13 ∗
            (vecCapPtrDealloc A.repAlloc w7 w8 ∗ vecCapPtrDealloc A.repAlloc w10 w11) ∗
            A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
          (fun s1 P1 =>
            (P1 ⊢ words7At (fsp + 296#64) w7 w8 w9 w10 w11 w12 w13 ∗
              vecCapPtrDealloc A.repAlloc w7 w8 ∗ A.pool lim st s1 ∗ stackAt fsp allocHookStack ∗
              (vecCapPtrDealloc A.repAlloc w10 w11 ∗ Frame)) ∧
            s1.sp = s.sp ∧ s1.v1TraceEq s ∧
            s1.readReg64 (Reg.gpr 1#5) = w7 ∧
            s1.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) := by
        dsimp only [words7At]
        wp_steps_sync_pool ((blkPl_298).base + 1884#64)
        wp_done
      refine SepWP.seq hstep1 ?_
      rintro s1 P1 hpc1 hrun1 ⟨hP1, hsp1, htr1, hx1_1, hx21_1⟩
      refine SepWP.weaken_pre hP1 ?_
      refine SepWP.seq (v1Tag11_err_dealloc_w7_1884_placed hDealloc hsp_align hpc1 hrun1 (hsp1.trans hsp) hx1_1) ?_
      rintro s2 P2 hpc2 hrun2 ⟨evs1, hevs1, hP2, hsp2, htr2, hx21_2⟩
      refine SepWP.weaken_pre (Entails.trans hP2 (Entails.of_eq (by sep_ac_rfl :
        words7At (fsp + 296#64) w7 w8 w9 w10 w11 w12 w13 ∗ A.pool lim (M.stepEvents evs1 st) s2 ∗
          stackAt fsp allocHookStack ∗ (vecCapPtrDealloc A.repAlloc w10 w11 ∗ Frame) =
        words7At (fsp + 296#64) w7 w8 w9 w10 w11 w12 w13 ∗ vecCapPtrDealloc A.repAlloc w10 w11 ∗
          A.pool lim (M.stepEvents evs1 st) s2 ∗ stackAt fsp allocHookStack ∗ Frame))) ?_
      refine SepWP.mono (v1Tag11_err_dealloc_w10_1900_placed hDealloc hsp_align hpc2 hrun2 (hsp2.trans (hsp1.trans hsp))) ?_
      rintro s3 P3 _ _ ⟨evs2, hevs2, hP3, hsp3, htr3, hx21_3⟩
      rw [← stepEvents_append_eq evs1 evs2 st] at hP3
      exact ⟨evs1 ++ evs2, hevs1.append hevs2,
        Entails.trans hP3 (sepConj_mono_left hfold56),
        hsp3.trans (hsp2.trans hsp1), htr3.trans (htr2.trans htr1),
        hx21_3.trans (hx21_2.trans hx21_1)⟩

theorem v1Tag11_err_enc_1920_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hDropEnc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 271)
      (withLsCl lsmpl (dropProtoPolyEncoderSpec M A lim)))
    {s : State} {st : M.σ} {fsp : BitVec 64} {optEnc : Option PolynomialEncoder} {Frame : SepProp}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1920#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2700#64) s
      (optProtoPolynomialEncoderAt A.repAlloc (fsp + 240#64) (optEnc.map pbToProtoPolyEncoder) ∗
        A.pool lim st s ∗ stackAt fsp dropStack48 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ memRegion (fsp + 240#64) 56 ∗ A.pool lim (M.stepEvents evs st) sm ∗
          stackAt fsp dropStack48 ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) := by
  simp only [withLsCl, dropProtoPolyEncoderSpec] at hDropEnc
  cases optEnc with
  | none =>
    have hnone56 : ((fsp + 240#64) ↦₆₄ noneCap) ∗ memRegion (fsp + 248#64) 48 ⊢ memRegion (fsp + 240#64) 56 := by
      have h248 : (fsp + 240#64) + 8#64 = fsp + 248#64 := by bv_lin
      rw [← h248]; exact optProtoPolyEncoder_none_entails_memRegion_56 (fsp + 240#64)
    simp only [Option.map_none, optProtoPolynomialEncoderAt_none', show (fsp + 240#64) + 8#64 = fsp + 248#64 by bv_lin]
    refine SepWP.mono (post := fun sm Pm =>
      (Pm ⊢ memRegion (fsp + 240#64) 56 ∗ A.pool lim (M.stepEvents [] st) sm ∗
        stackAt fsp dropStack48 ∗ Frame) ∧
      sm.sp = s.sp ∧ sm.v1TraceEq s ∧
      sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) ?_
      (fun _ _ _ _ h => ⟨[], FreeOnlyEvs.nil, h⟩)
    dsimp only [AllocCostModel.stepEvents]
    wp_steps_sync_pool ((blkPl_298).base + 2700#64)
    apply SepWP.fold hnone56 (by sep_focus)
    wp_done
  | some enc =>
    simp only [Option.map_some, optProtoPolynomialEncoderAt_some']
    apply SepWP.fold (protoPolynomialEncoderAt_expose_cap A.repAlloc (fsp + 240#64) (pbToProtoPolyEncoder enc)) (by sep_focus)
    simp only [sepExists_sepConj_left, sepConj_assoc]
    apply SepWP.exists_elim; intro cap; apply SepWP.exists_elim; intro ptr; apply SepWP.pure_elim; intro hcap_lt
    have hne_none : (cap + 1#64 == 0#64) = false :=
      Bool.eq_false_iff.mpr (cap_add_one_beq_zero_false hcap_lt)
    apply sepWP_seq_lscl hcl (mid := lsmpl.base 271)
    wp_steps_sync_pool (lsmpl.base 271)
    apply SepWP.fold (protoPolynomialEncoderAt_unexpose_cap A.repAlloc (fsp + 240#64) cap ptr (pbToProtoPolyEncoder enc)) (by sep_focus)
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _hcl_call => ?_
    wp_apply
    dsimp only [protoPolynomialEncoderSize]
    refine sepWP_mono_freeOnly (by assumption) ?_
    wp_steps_sync_pool ((blkPl_298).base + 2700#64)
    exact align_pre (by rw [hsp]) (by wp_done)

/-! ## 2. Setup, Copy & Post-Drop Lemmas for Tag 11 (`+1800..+1864`, `+3040..+3144`) -/

theorem v1Tag11_setup_1800_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {s : State} {st : M.σ} {fsp w_sp16 w_sp72 : BitVec 64} {restLen : Nat} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1800#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64)
    (hx27 : s.readReg64 (Reg.gpr 27#5) = 0xfffffffffffffffe#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 301) s
      (((fsp + 16#64) ↦₆₄ w_sp16) ∗ memRegion (fsp + 24#64) 48 ∗
        ((fsp + 72#64) ↦₆₄ w_sp72) ∗ memRegion (fsp + 80#64) 48 ∗
        A.pool lim st s ∗ Frame)
      (fun s1 P1 =>
        (P1 ⊢ chunkedCt2SampledPBCapAt A.repAlloc (fsp + 16#64) restLen default ∗
          A.pool lim st s1 ∗ Frame) ∧
        s1.sp = s.sp ∧ s1.v1TraceEq s ∧
        s1.readReg64 (Reg.gpr 0#5) = s.readReg64 (Reg.gpr 0#5) ∧
        s1.readReg64 (Reg.gpr 1#5) = fsp + 16#64 ∧
        s1.readReg64 (Reg.gpr 2#5) = s.readReg64 (Reg.gpr 19#5) ∧
        s1.readReg64 Reg.lr = (blkPl_298).base + 1820#64 ∧
        s1.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
        s1.readReg64 (Reg.gpr 20#5) = s.readReg64 (Reg.gpr 20#5) ∧
        s1.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) ∧
        s1.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 ∧
        s1.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧
        s1.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧
        s1.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
        s1.readReg64 (Reg.gpr 27#5) = 0xfffffffffffffffe#64 ∧
        s1.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
        s1.readReg64 (Reg.gpr 29#5) = s.readReg64 (Reg.gpr 29#5)) := by
  have hdef : ((fsp + 16#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (fsp + 24#64) 48 ∗
      ((fsp + 72#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ memRegion (fsp + 80#64) 48 ⊢
      chunkedCt2SampledPBCapAt A.repAlloc (fsp + 16#64) restLen default := by
    change ((fsp + 16#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (fsp + 24#64) 48 ∗
        ((fsp + 72#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ memRegion (fsp + 80#64) 48 ⊢
      (((fsp + 16#64) ↦₆₄ noneCap) ∗ memRegion ((fsp + 16#64) + 8#64) 48) ∗
      (((fsp + 16#64) + 0x38#64) ↦₆₄ noneCap2 ∗ memRegion (((fsp + 16#64) + 0x38#64) + 8#64) 48)
    have h24 : (fsp + 16#64) + 8#64 = fsp + 24#64 := by bv_lin
    have h72 : (fsp + 16#64) + 0x38#64 = fsp + 72#64 := by bv_lin
    have h80 : (fsp + 72#64) + 8#64 = fsp + 80#64 := by bv_lin
    rw [h24, h72, h80]; exact Entails.of_eq (by unfold noneCap noneCap2; sep_ac_rfl)
  wp_steps_sync_pool (lsmpl.base 301)
  apply SepWP.fold hdef (by sep_focus)
  wp_done

theorem v1Tag11_copy_ok_1820_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {s : State} {st : M.σ} {fsp mPtr w_sp352 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : BitVec 64}
    {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1820#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = 0#64)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 3040#64) s
      (v1Tag11_words14At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
        memRegion (fsp + 240#64) 112 ∗ ((fsp + 352#64) ↦₆₄ w_sp352) ∗
        A.pool lim st s ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ v1Tag11_words14At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
          memRegion (fsp + 240#64) 112 ∗ ((fsp + 352#64) ↦₆₄ mPtr) ∗
          A.pool lim st sm ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
        sm.readReg64 (Reg.gpr 20#5) = mPtr ∧
        sm.readReg64 (Reg.gpr 21#5) = 0#64 ∧
        sm.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) ∧
        sm.readReg64 (Reg.gpr 23#5) = s.readReg64 (Reg.gpr 23#5) ∧
        sm.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧
        sm.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧
        sm.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
        sm.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧
        sm.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
        sm.readReg64 (Reg.gpr 29#5) = s.readReg64 (Reg.gpr 29#5)) := by
  have hfold240 := v1Tag11_words14At_entails_memRegion_112 (fsp + 240#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13
  conv =>
    arg 4
    rw [v1Tag11_memRegion_112_eq_words14 (fsp + 240#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v5
  apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v3
  apply SepWP.exists_elim; intro v2; apply SepWP.exists_elim; intro v1
  apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v13
  apply SepWP.exists_elim; intro v12; apply SepWP.exists_elim; intro v11
  apply SepWP.exists_elim; intro v10; apply SepWP.exists_elim; intro v9
  apply SepWP.exists_elim; intro v8; apply SepWP.exists_elim; intro v7
  have hbr : (s.readReg64 (Reg.gpr 0#5) == 0#64) = true := by rw [hx0]; rfl
  dsimp only [v1Tag11_words14At, words7At] at hfold240 ⊢
  wp_steps_sync_pool ((blkPl_298).base + 3040#64)
  apply SepWP.fold hfold240 (by sep_focus)
  wp_done

theorem v1Tag11_copy_err_1820_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {s : State} {st : M.σ} {fsp mPtr w_sp352 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : BitVec 64}
    {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1820#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) ≠ 0#64)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 1864#64) s
      (v1Tag11_words14At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
        memRegion (fsp + 240#64) 112 ∗ ((fsp + 352#64) ↦₆₄ w_sp352) ∗
        A.pool lim st s ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 16#64) 112 ∗
          v1Tag11_words14At (fsp + 240#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
          ((fsp + 352#64) ↦₆₄ mPtr) ∗ A.pool lim st sm ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 0#5)) := by
  have hfold16 := v1Tag11_words14At_entails_memRegion_112 (fsp + 16#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13
  rw [v1Tag11_memRegion_112_eq_words14 (fsp + 240#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v5
  apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v3
  apply SepWP.exists_elim; intro v2; apply SepWP.exists_elim; intro v1
  apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v13
  apply SepWP.exists_elim; intro v12; apply SepWP.exists_elim; intro v11
  apply SepWP.exists_elim; intro v10; apply SepWP.exists_elim; intro v9
  apply SepWP.exists_elim; intro v8; apply SepWP.exists_elim; intro v7
  have hbr : (s.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0
  dsimp only [v1Tag11_words14At, words7At] at hfold16 ⊢
  wp_steps_sync_pool ((blkPl_298).base + 1864#64)
  apply SepWP.fold hfold16 (by sep_focus)
  wp_done

theorem v1Tag11_pre_drop_3040_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {s : State} {st : M.σ} {fsp mPtr w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : BitVec 64}
    {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 3040#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = fsp + 720#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 3076#64) s
      (v1Tag11_words14At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
        memRegion (fsp + 480#64) 112 ∗ A.pool lim st s ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 16#64) 112 ∗
          v1Tag11_words14At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
          A.pool lim st sm ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 0#5) = mPtr ∧
        sm.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
        sm.readReg64 (Reg.gpr 20#5) = mPtr ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
        sm.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) ∧
        sm.readReg64 (Reg.gpr 23#5) = s.readReg64 (Reg.gpr 23#5) ∧
        sm.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧
        sm.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧
        sm.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
        sm.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧
        sm.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
        sm.readReg64 (Reg.gpr 29#5) = fsp + 720#64) := by
  have hfold16 := v1Tag11_words14At_entails_memRegion_112 (fsp + 16#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13
  rw [v1Tag11_memRegion_112_eq_words14 (fsp + 480#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v5
  apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v3
  apply SepWP.exists_elim; intro v2; apply SepWP.exists_elim; intro v1
  apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v13
  apply SepWP.exists_elim; intro v12; apply SepWP.exists_elim; intro v11
  apply SepWP.exists_elim; intro v10; apply SepWP.exists_elim; intro v9
  apply SepWP.exists_elim; intro v8; apply SepWP.exists_elim; intro v7
  dsimp only [v1Tag11_words14At, words7At] at hfold16 ⊢
  wp_steps_sync_pool ((blkPl_298).base + 3076#64)
  apply SepWP.fold hfold16 (by sep_focus)
  wp_done

theorem v1Tag11_post_drop_3076_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267)
      (withLsCl lsmpl (dropOptProtoInnerStatePlacedSpec M A lim)))
    {s : State} {st : M.σ} {fsp mPtr w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : BitVec 64}
    {is : Option V1State.InnerState} {Frame : SepProp}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 3076#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = mPtr)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = fsp + 720#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2700#64) s
      (optProtoInnerStateAt A.repAlloc mPtr is ∗ A.pool lim st s ∗
        optProtoInnerStateJumpTablePlacedAt ∗ stackAt fsp dropStack96 ∗
        v1Tag11_words14At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
        Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ memRegion (fsp + 480#64) 112 ∗
          (mPtr ↦₆₄ 0x800000000000000a#64) ∗
          v1Tag11_words14At (mPtr + 8#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
          memRegion (mPtr + 120#64) 104 ∗
          A.pool lim (M.stepEvents evs st) sm ∗ optProtoInnerStateJumpTablePlacedAt ∗
          stackAt fsp dropStack96 ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
        sm.readReg64 (Reg.gpr 20#5) = mPtr ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
        sm.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) ∧
        sm.readReg64 (Reg.gpr 23#5) = s.readReg64 (Reg.gpr 23#5) ∧
        sm.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧
        sm.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧
        sm.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
        sm.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧
        sm.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
        sm.readReg64 (Reg.gpr 29#5) = fsp + 720#64) := by
  have hfold480 := v1Tag11_words14At_entails_memRegion_112 (fsp + 480#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13
  simp only [withLsCl, dropOptProtoInnerStatePlacedSpec] at hDropInner
  apply sepWP_seq_lscl hcl (mid := lsmpl.base 267)
  wp_steps_sync_pool (lsmpl.base 267)
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _hcl_call => ?_
  wp_apply
  dsimp only [optProtoInnerStateSize]
  refine sepWP_mono_freeOnly (by assumption) ?_
  rw [v1Tag11_memRegion_224_split_ok mPtr]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWP.exists_elim; intro vd
  apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v5
  apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v3
  apply SepWP.exists_elim; intro v2; apply SepWP.exists_elim; intro v1
  apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v13
  apply SepWP.exists_elim; intro v12; apply SepWP.exists_elim; intro v11
  apply SepWP.exists_elim; intro v10; apply SepWP.exists_elim; intro v9
  apply SepWP.exists_elim; intro v8; apply SepWP.exists_elim; intro v7
  dsimp only [v1Tag11_words14At, words7At] at hfold480 ⊢
  wp_steps_sync_pool ((blkPl_298).base + 2700#64)
  apply SepWP.fold hfold480 (by sep_focus)
  exact align_pre (by rw [hsp]) (by wp_done)

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag11ClPlacedBudgetAux

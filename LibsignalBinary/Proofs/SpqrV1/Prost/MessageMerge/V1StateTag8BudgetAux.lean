/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.UnchunkedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1Budget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag8
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Stepping Helpers for `V1State::merge` Tag Arm 8 (`Ct1Sampled`)

`RustCliAllocBudget`-threaded `[LibsignalPlacement]` inline `Option PolynomialDecoder` drop, error
cleanup, and stack-copy stepping helpers for tag arm 8 (`Ct1Sampled`, Block `298`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

open CryptoVerification (LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalProtoCodec (WireType)
open CryptoVerification.LibsignalSpqrV1 (
  PolynomialDecoder PolynomialEncoder V1State pbToProtoPolyDecoder pbToProtoPolyEncoder
)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage mergeOptMessage)
open CryptoVerification.LibsignalTripleRatchet (
  LibsignalCodeRoLoaded decodeErrorAtStackLen withLsCodeRoLoaded
)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  pointsToBytes_prefix_join sliceCursorAfter sliceCursorAfter_eq_split
  sliceCursorAfter_join sliceCursorAt
)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (allocHookStack arrayAt vecU8)
open CryptoVerification.SpqrV1.Drop (
  DropOptProtoInnerStateGhost add_24_add_8 cap_add_one_beq_zero_false cap_mul_24 cons_len_mul
  ct1SentToCt1SentEkReceived dropStack32 dropStack48 dropStack96
  header_cells_entails_memRegion_24 ofNat_add_one_beq_one_false_24
  ofNat_beq_zero_false_24 ofNat_succ_eq_add_one optProtoInnerStateAt
  optProtoInnerStateJumpTablePlacedAt optProtoInnerStateSize
  optProtoPolyDecoder_none_entails_memRegion_40
  optProtoPolyEncoder_none_entails_memRegion_56
  optProtoPolynomialDecoderAt_none' optProtoPolynomialDecoderAt_some'
  optProtoPolynomialEncoderAt_none' optProtoPolynomialEncoderAt_some'
  optProtoUnchunkedCt1SentEkReceivedAt optProtoUnchunkedCt1SentEkReceivedAt_none
  optProtoUnchunkedCt1SentEkReceivedAt_none_entails_memRegion_128
  optProtoUnchunkedCt1SentEkReceivedAt_some protoChunkedCt1SampledAt
  protoPolyDecoderAt_entails_dealloc protoPolyDecoderHeaders_entails_memRegion_40
  protoPolynomialEncoderAt_expose_cap protoPolynomialEncoderAt_unexpose_cap
  protoUnchunkedCt1SentEkReceivedAt protoUnchunkedCt1SentEkReceivedAt_expose_cap
  protoUnchunkedCt1SentEkReceivedAt_unexpose_cap protoUnchunkedCt1SentEkReceivedSize
  sep_pull_body sep_push_body sep_rejoin_loop tail_len_mul_lt
  vecCapPtrDealloc vecU8_entails_capPtr_dealloc
)
open CryptoVerification.SpqrV1.Poly (
  optProtoPolynomialDecoderAt optProtoPolynomialEncoderAt protoPolynomialEncoderSize
)
open CryptoVerification.SpqrV1.ProtoRepr (
  chunkedCt1SampledPBAt optPolynomialDecoderPBAt optPolynomialEncoderPBAt
)
open CryptoVerification.SpqrV1.Prost.MessageMerge (
  ChunkedCt1SampledMergeGhost
  InnerStateDiscrFull OptInnerStatePolyBound OptPolyDecoderBound OptPolyEncoderBound
  SepWPp.call_frame_lscro SepWPp.of_sepWP_lscro
  V1StateLoopRegsPlaced V1StateMergeGhost V1StateTagEntryHypPlaced WppPost
  bv64_add_zero bv64_sub_zero
  chunkedCt1SampledPBCapAt chunkedCt1SampledPBAt_eq_proto chunkedInlStack chunkedMergeStack
  codecWireTypeToProto
  ct1Sampled_polyBound_extract discrFull_none_add2 discrFull_some_add2
  innerStatePolyBound_of_ct1Sampled optInnerStatePolyBound_lt_2_56
  optPolyDecoderBound_iff optPolyDecoderBound_none optPolyDecoderPtsLen
  optPolyEncoderBound_iff optPolyEncoderBound_none optPolyEncoderPolysLen optPolyEncoderPtsLen
  optProtoInnerStateAt_entails_exists optProtoInnerStateCapAt optProtoInnerStateCapAt_entails_pb
  optUnchunkedCt1SentPBCapAt
  protoInnerStateCapAt protoPrefixStep_chunked_ct1Sampled_mergeField proto_mergeMessage_len_le
  v1StateBelowRest v1StateBelow_allocHook v1StateBelow_allocHook_entails
  v1StateBelow_dropStack32 v1StateBelow_dropStack32_entails
  v1StateBelow_dropStack48 v1StateBelow_dropStack48_entails
  v1StateBelow_dropStack96 v1StateBelow_dropStack96_entails
  v1StateJumpTablesPlacedAt v1StateMergeJumpTablePlacedExpanded v1StateSavedRegsAt
  v1State_mergeField_tag8
  v1Tag8_capHeap v1Tag8_chunkedCt1SampledPBAt_entails_cap_zero
  v1Tag8_extract_words
  v1Tag8_memRegion_224_eq_words28 v1Tag8_memRegion_224_split_init
  v1Tag8_memRegion_fold_temp v1Tag8_memRegion_split_temp v1Tag8_of_words
  v1Tag8_optProtoUnchunkedCt1SentAt_eq v1Tag8_reconstruct_innerState
  v1Tag8_words28At v1Tag8_words28At_entails_memRegion_224
  v1Tag8_words_entails_protoChunkedCt1Sampled
  words16At words13At words10At words7At words5At words3At
)
open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2 (blkPC_298 blkPl_298)
open scoped CryptoVerification.SpqrV1.Prost.MessageMerge.Part2
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs
  RustCliAllocBudget VmPreserved rustCliDeallocBudgetSpec rustDeallocEvents
)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget (dropProtoPolyEncoderSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget (dropOptProtoInnerStatePlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.UnchunkedBudget (
  dropProtoUnchunkedCt1SentEkReceivedSpec
)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget (
  ChunkedCt1SampledMergeEnv ChunkedCt1SampledMergePostEnv
  SpqrMergeIterEnv SpqrMergeLoopEnv chunkedCt1SampledMergeSpec chunkedCt1SampledMergeSpecOfEnv
  ct1SampledPolyCapBound
)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefsBudget (
  optInnerStatePolyCapBound
  v1StateErrFramePlaced v1StateLoopPrePlaced v1StateMergePlacedSpec
)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1BudgetAux (
  V1StateTagContPlaced V1StateTagEntryBudgetPlaced V1StateTagStepHypPlaced WppPanicFalse
  ct1SampledPolyCapBound_le optInnerStatePolyCapBound_of_ct1Sampled
  sepWPp_congr_state_pre wppPanicFalse_of_false
)

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag8BudgetAux

open Arm64 ProofLib SepProp
open ProofLib.ProgramReflection
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local irreducible] v1StateMergeJumpTablePlacedExpanded optProtoInnerStateJumpTablePlacedAt v1StateSavedRegsAt
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero

/-! ## 1. Private Budget `SepWP` Combinators -/

def deallocFreeOnlySpec [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (BitVec 64 × Nat × Nat × M.σ) where
  pre := (rustCliDeallocBudgetSpec M A lim).pre
  post := fun (_, size, align, st) s0 sf =>
    ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf⌝ ∗
      A.pool lim (M.stepEvents (rustDeallocEvents size align) st) sf ∗ stackAt s0.sp allocHookStack

theorem subroutine_ok_deallocFreeOnly [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok prog entry (deallocFreeOnlySpec M A lim) := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [rustCliDeallocBudgetSpec, deallocFreeOnlySpec] at hq ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  exact ⟨⟨hq.1.1.2.1, hq.1.1⟩, hq.2⟩

theorem seq_vm_clean {P : Program} {b : BitVec 64} {Hk : String → Option (State → State)}
    {mid target : BitVec 64} {s : State}
    {Pre P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP (P.rebase b Hk) mid s Pre (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → VmPreserved s sm → Q sm →
      SepWP (P.rebase b Hk) target sm P_mid post) :
    SepWP (P.rebase b Hk) target s Pre post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨hvm, hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hvm hQ)

theorem align_pre_vm {prog : Program} {target : BitVec 64} {s0 s : State}
    {P P_mid : SepProp} {Q : State → Prop}
    (h : P = P_mid)
    (hwp : SepWP prog target s P (fun sm Pm => sm.tpidrEl0 = s0.tpidrEl0 ∧ (Pm ⊢ P) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => sm.tpidrEl0 = s0.tpidrEl0 ∧ (Pm ⊢ P_mid) ∧ Q sm) := by
  subst h; exact hwp

theorem sepWP_vm_evs_nil {P : Program} {b : BitVec 64} {Hk : String → Option (State → State)}
    {target : BitVec 64} {s : State} {Pre : SepProp}
    {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    (hpool : ∀ sm, VmPreserved s sm → P_evs [] s = P_evs [] sm)
    (h : SepWP (P.rebase b Hk) target s Pre
      (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_evs [] s) ∧ Q sm)) :
    SepWP (P.rebase b Hk) target s Pre (fun sm Pm =>
      ∃ evs, FreeOnlyEvs evs ∧ (Pm ⊢ P_evs evs sm) ∧ Q sm) :=
  SepWP.mono h fun sm _Pm _ _ ⟨hvm, hp, hq⟩ =>
    ⟨[], LibsignalBinary.Heap.FreeOnlyEvs.nil, hpool sm hvm ▸ hp, hq⟩

theorem seq_clean_evs {prog : Program} {mid target : BitVec 64}
    {s : State} {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm =>
      ∃ evs, FreeOnlyEvs evs ∧ (Pm ⊢ P_evs evs sm) ∧ Q sm))
    (h2 : ∀ (evs : List AllocEvent) (sm : State),
      FreeOnlyEvs evs → sm.pc = mid → sm.status = .Running → Q sm →
      SepWP prog target sm (P_evs evs sm) post) :
    SepWP prog target s P post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨evs, hevs, hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 evs sm hevs hpc hrun hQ)

theorem sepWP_evs_nil {prog : Program} {target : BitVec 64}
    {s : State} {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    (h : SepWP prog target s P (fun sm Pm => (Pm ⊢ P_evs [] sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm =>
      ∃ evs, FreeOnlyEvs evs ∧ (Pm ⊢ P_evs evs sm) ∧ Q sm) :=
  SepWP.mono h fun _ _ _ _ ⟨hp, hq⟩ => ⟨[], LibsignalBinary.Heap.FreeOnlyEvs.nil, hp, hq⟩

theorem sepWP_evs_dealloc {prog : Program} {target : BitVec 64}
    {s : State} (sz al : Nat)
    {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    (h : SepWP prog target s P (fun sm Pm =>
      (Pm ⊢ P_evs (rustDeallocEvents sz al) sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm =>
      ∃ evs, FreeOnlyEvs evs ∧ (Pm ⊢ P_evs evs sm) ∧ Q sm) :=
  SepWP.mono h fun _ _ _ _ ⟨hp, hq⟩ =>
    ⟨rustDeallocEvents sz al, LibsignalBinary.Heap.FreeOnlyEvs.singleton al sz, hp, hq⟩

/-! ## 2. Shared `+2072..+2112 -> +2692..+2700` & Inline `Option PolynomialDecoder` Drop -/

theorem v1Tag8_err_pts_buf_2072_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hDealloc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    {st : M.σ} {s : State} {fsp ptsPtr ptsCap : BitVec 64} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true) (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = (blkPl_298).base + 2072#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = ptsPtr) (hx23 : s.readReg64 (Reg.gpr 23#5) = ptsCap) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2700#64) s
      ((if ptsCap = 0 then emp else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗ memRegion ptsPtr (ptsCap.toNat * 24)) ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧ AllocCallPreserved s sm ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hDealloc
  clear hDealloc
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  by_cases hc : ptsCap = 0
  · have hc_beq : (ptsCap == 0#64) = true := by rw [beq_iff_eq]; exact hc
    simp only [hc, ↓reduceIte, emp_sepConj] at hx23 ⊢
    apply sepWP_evs_nil
    simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
    wp_steps; wp_done
  · have hc_beq : ¬((ptsCap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
    have hlsl := cap_mul_24 hpts_cap_lt
    simp only [hc, ↓reduceIte]
    apply sepWP_evs_dealloc (ptsCap.toNat * 24) 8
    wp_steps
    wp_apply
    have hacp' : AllocCallPreserved s sf := by assumption
    rcases hacp' with ⟨_, _, _, _, _, _, _⟩
    wp_steps
    rw [hsp]
    wp_done

theorem v1Tag8_err_dec_body_1448_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hDealloc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    {fsp ptsPtr ptsCap : BitVec 64} (hsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (st : M.σ) (s : State) (Frame : SepProp),
      s.pc = (blkPl_298).base + 1448#64 →
      s.status = .Running → s.sp = fsp →
      s.readReg64 (Reg.gpr 22#5) = ptsPtr → s.readReg64 (Reg.gpr 23#5) = ptsCap →
      s.readReg64 (Reg.gpr 24#5) = cnt → s.readReg64 (Reg.gpr 25#5) = cur + 8#64 →
      SepWP ((blkPC_298).rebase (blkPl_298).base H)
        ((blkPl_298).base + 1436#64) s
        (vecU8 A.repAlloc cur bs ∗ A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evs, FreeOnlyEvs evs ∧
          (Pm ⊢ memRegion cur 24 ∗ A.pool lim (M.stepEvents evs st) sm ∗
            stackAt fsp allocHookStack ∗ Frame) ∧
          sm.sp = s.sp ∧ sm.v1TraceEq s ∧ sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
          sm.readReg64 (Reg.gpr 22#5) = ptsPtr ∧ sm.readReg64 (Reg.gpr 23#5) = ptsCap ∧
          sm.readReg64 (Reg.gpr 24#5) = cnt ∧ sm.readReg64 (Reg.gpr 25#5) = cur + 8#64) := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hDealloc
  clear hDealloc
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  intro cur cnt bs st s Frame hpc hrun hsp hx22 hx23 hx24 hx25
  refine SepWP.weaken_pre (sepConj_mono_left (vecU8_entails_capPtr_dealloc A.repAlloc cur bs)) ?_
  rw [sepExists_sepConj_left]; apply SepWP.exists_left; intro cap
  rw [sepExists_sepConj_left]; apply SepWP.exists_left; intro vptr
  dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
  by_cases hcap : (cap == 0#64) = true <;>
    simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
  · apply sepWP_evs_nil
    simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
    have hstep : SepWP ((blkPC_298).rebase (blkPl_298).base H) ((blkPl_298).base + 1436#64) s
        (((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
          A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ ((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
            A.pool lim st sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          sm.sp = s.sp ∧ sm.v1TraceEq s ∧ sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
          sm.readReg64 (Reg.gpr 22#5) = ptsPtr ∧ sm.readReg64 (Reg.gpr 23#5) = ptsCap ∧
          sm.readReg64 (Reg.gpr 24#5) = cnt ∧ sm.readReg64 (Reg.gpr 25#5) = cur + 8#64) := by
      wp_steps; wp_done
    exact SepWP.mono hstep fun sm _Pm _ _ ⟨hp, hq⟩ =>
      ⟨Entails.trans hp (sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)), hq⟩
  · apply sepWP_evs_dealloc cap.toNat 1
    have hstep : SepWP ((blkPC_298).rebase (blkPl_298).base H) ((blkPl_298).base + 1436#64) s
        (((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8 ∗
          (A.live vptr cap.toNat 1 ∗ memRegion vptr cap.toNat)) ∗
          A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ ((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
            A.pool lim (M.stepEvents (rustDeallocEvents cap.toNat 1) st) sm ∗
            stackAt fsp allocHookStack ∗ Frame) ∧
          sm.sp = s.sp ∧ sm.v1TraceEq s ∧ sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
          sm.readReg64 (Reg.gpr 22#5) = ptsPtr ∧ sm.readReg64 (Reg.gpr 23#5) = ptsCap ∧
          sm.readReg64 (Reg.gpr 24#5) = cnt ∧ sm.readReg64 (Reg.gpr 25#5) = cur + 8#64) := by
      wp_steps
      wp_apply
      have hacp' : AllocCallPreserved s sf := by assumption
      rcases hacp' with ⟨_, _, _, _, _, _, _⟩
      wp_steps
      rw [hsp]
      wp_done
    exact SepWP.mono hstep fun sm _Pm _ _ ⟨hp, hq⟩ =>
      ⟨Entails.trans hp (sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)), hq⟩

theorem v1Tag8_err_dec_loop_1448_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hDealloc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    {fsp ptsPtr ptsCap : BitVec 64} (hsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (st : M.σ) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = (blkPl_298).base + 1448#64 →
      s.status = .Running → s.sp = fsp →
      s.readReg64 (Reg.gpr 22#5) = ptsPtr → s.readReg64 (Reg.gpr 23#5) = ptsCap →
      s.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 rest.length →
      s.readReg64 (Reg.gpr 25#5) = cur + 8#64 →
      SepWP ((blkPC_298).rebase (blkPl_298).base H)
        ((blkPl_298).base + 2072#64) s
        (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 cur rest ∗
          A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evs, FreeOnlyEvs evs ∧
          (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool lim (M.stepEvents evs st) sm ∗
            stackAt fsp allocHookStack ∗ Frame) ∧
          sm.sp = s.sp ∧ sm.v1TraceEq s ∧ sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
          sm.readReg64 (Reg.gpr 22#5) = ptsPtr ∧ sm.readReg64 (Reg.gpr 23#5) = ptsCap) := by
  have hbody := v1Tag8_err_dec_body_1448_placed (H := H) hDealloc (ptsPtr := ptsPtr) (ptsCap := ptsCap) hsp_align
  intro rest; induction rest with
  | nil => intro _ _ _ _ hne; exact absurd rfl hne
  | cons bs tl ih =>
    intro cur st s Frame _ hlen hpc hrun hsp hx22 hx23 hx24 hx25
    simp only [arrayAt, BitVec.ofNat_eq_ofNat]; rw [sep_pull_body]
    refine seq_clean_evs (mid := (blkPl_298).base + 1436#64)
      (P_evs := fun evs sm => memRegion cur 24 ∗ A.pool lim (M.stepEvents evs st) sm ∗
        stackAt fsp allocHookStack ∗
        (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (cur + 24#64) tl ∗ Frame))
      (Q := fun sm => sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
        sm.readReg64 (Reg.gpr 22#5) = ptsPtr ∧ sm.readReg64 (Reg.gpr 23#5) = ptsCap ∧
        sm.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 (bs :: tl).length ∧
        sm.readReg64 (Reg.gpr 25#5) = cur + 8#64)
      (hbody cur (BitVec.ofNat 64 (bs :: tl).length) bs st s _ hpc hrun hsp hx22 hx23 hx24 hx25) ?_
    intro evs_hd s1 hevs_hd hpc1 hrun1 ⟨hsp1, ⟨htr1, hvregs1⟩, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1⟩
    rcases tl with _ | ⟨bs2, tl2⟩
    · simp only [List.length_singleton, arrayAt, sepConj_emp, emp_sepConj, Nat.one_mul] at hx24_1 ⊢
      have hfin : SepWP ((blkPC_298).rebase (blkPl_298).base H) ((blkPl_298).base + 2072#64) s1
          (memRegion cur 24 ∗ A.pool lim (M.stepEvents evs_hd st) s1 ∗ stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ memRegion cur 24 ∗ A.pool lim (M.stepEvents evs_hd st) sm ∗
              stackAt fsp allocHookStack ∗ Frame) ∧
            sm.sp = s.sp ∧ sm.v1TraceEq s ∧
            sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
            sm.readReg64 (Reg.gpr 22#5) = ptsPtr ∧ sm.readReg64 (Reg.gpr 23#5) = ptsCap) := by
        wp_steps; wp_done
      exact SepWP.mono hfin fun _ _ _ _ ⟨hp, hq⟩ => ⟨evs_hd, hevs_hd, hp, hq⟩
    · have hlen_tl : (bs2 :: tl2).length * 24 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_add_one_beq_one_false_24 (n := (bs2 :: tl2).length) (by simp) hlen_tl
      rw [List.length_cons, ofNat_succ_eq_add_one] at hx24_1
      rw [sep_push_body]
      refine seq_vm_clean (mid := (blkPl_298).base + 1448#64)
        (P_mid := arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (cur + 24#64) (bs2 :: tl2) ∗
          A.pool lim (M.stepEvents evs_hd st) s1 ∗ stackAt fsp allocHookStack ∗ (memRegion cur 24 ∗ Frame))
        (Q := fun s2 => s2.sp = s.sp ∧ s2.v1TraceEq s ∧
          s2.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
          s2.readReg64 (Reg.gpr 22#5) = ptsPtr ∧ s2.readReg64 (Reg.gpr 23#5) = ptsCap ∧
          s2.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 (bs2 :: tl2).length ∧
          s2.readReg64 (Reg.gpr 25#5) = cur + 32#64)
        (by wp_steps_vm) ?_
      intro s2 hpc2 hrun2 hvm2 ⟨hsp2, htr2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2⟩
      rw [← A.pool_of_vmPreserved hvm2]
      have hrec := ih (cur + 24#64) (M.stepEvents evs_hd st) s2 (memRegion cur 24 ∗ Frame)
        (List.cons_ne_nil _ _) hlen_tl hpc2 hrun2 (hsp2.trans hsp) hx22_2 hx23_2 hx24_2
        (by simp only [hx25_2, add_24_add_8, wp_norm, arm64_norm])
      refine SepWP.mono hrec fun sm _Pm _ _ ⟨evs_tl, hevs_tl, hPm, hspm, htrm, hx21_m, hx22_m, hx23_m⟩ => ?_
      have hsplit := cons_len_mul bs (bs2 :: tl2) 24
      have hbound : 24 + (bs2 :: tl2).length * 24 ≤ 2 ^ 64 := by
        rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
      refine ⟨evs_hd ++ evs_tl, hevs_hd.append hevs_tl, ?_,
        hspm.trans hsp2, htrm.trans htr2, hx21_m.trans hx21_2, hx22_m, hx23_m⟩
      rw [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
      refine Entails.trans hPm ?_
      rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 24 ((bs2 :: tl2).length * 24) hbound]
      exact Entails.refl _

theorem v1Tag8_err_dec_1404_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hDealloc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    {st : M.σ} {s : State} {fsp : BitVec 64} {optDec : Option PolynomialDecoder} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1404#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2700#64) s
      (optProtoPolynomialDecoderAt A.repAlloc (fsp + 424#64) (optDec.map pbToProtoPolyDecoder) ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ memRegion (fsp + 424#64) 40 ∗ A.pool lim (M.stepEvents evs st) sm ∗
          stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) := by
  cases optDec with
  | none =>
    have hnone40 : ((fsp + 424#64) ↦₆₄ noneCap) ∗ memRegion (fsp + 432#64) 32 ⊢ memRegion (fsp + 424#64) 40 := by
      have h432 : (fsp + 424#64) + 8#64 = fsp + 432#64 := by bv_lin
      rw [← h432]; exact optProtoPolyDecoder_none_entails_memRegion_40 (fsp + 424#64)
    simp only [Option.map_none, optProtoPolynomialDecoderAt_none', show (fsp + 424#64) + 8#64 = fsp + 432#64 by bv_lin]
    apply sepWP_evs_nil
    simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
    wp_steps; apply SepWP.fold hnone40 (by sep_focus); wp_done
  | some dec =>
    simp only [Option.map_some, optProtoPolynomialDecoderAt_some']
    let pb := pbToProtoPolyDecoder dec
    apply SepWP.fold (protoPolyDecoderAt_entails_dealloc A.repAlloc (fsp + 424#64) pb) (by sep_focus)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro g; apply SepWP.pure_elim; rintro ⟨hpts_le, hpts_cap_lt, _hpts_ptr_ne⟩
    have hpts_cap_pow : g.cap.toNat < 2 ^ 63 := by omega
    have hne_none := cap_add_one_beq_zero_false hpts_cap_pow
    have h432 : (fsp + 424#64) + 8#64 = fsp + 432#64 := by bv_lin
    have h440 : (fsp + 424#64) + 16#64 = fsp + 440#64 := by bv_lin
    have h448 : (fsp + 424#64) + 24#64 = fsp + 448#64 := by bv_lin
    have hhdr40 : ((fsp + 424#64) ↦₆₄ g.cap) ∗ ((fsp + 432#64) ↦₆₄ g.ptr) ∗
        ((fsp + 440#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗ memRegion (fsp + 448#64) 16 ⊢
        memRegion (fsp + 424#64) 40 := by
      rw [← h432, ← h440, ← h448]
      exact protoPolyDecoderHeaders_entails_memRegion_40 (fsp + 424#64) g.cap g.ptr (BitVec.ofNat 64 pb.pts.length)
    rw [h432, h440, h448]
    dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
    refine seq_clean_evs (mid := (blkPl_298).base + 2072#64)
      (P_evs := fun evs sm =>
        (if g.cap = 0 then emp else A.live g.ptr (g.cap.toNat * 24) 8 ∗ memRegion g.ptr (g.cap.toNat * 24)) ∗
        A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ (memRegion (fsp + 424#64) 40 ∗ Frame))
      (Q := fun sm => sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
        sm.readReg64 (Reg.gpr 22#5) = g.ptr ∧ sm.readReg64 (Reg.gpr 23#5) = g.cap) ?_ ?_
    · generalize hxs : pb.pts = xs at hpts_le hhdr40 ⊢
      cases xs with
      | nil =>
        simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat,
          BitVec.add_zero, arrayAt, emp_sepConj] at hhdr40 ⊢
        apply sepWP_evs_nil
        simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
        wp_steps; apply SepWP.fold hhdr40 (by sep_focus); wp_done
      | cons bs tl =>
        have hlen_pos : 0 < (bs :: tl).length := by simp
        have hlen_lt : (bs :: tl).length * 24 < 2 ^ 63 := by
          have : (bs :: tl).length * 24 ≤ g.cap.toNat * 24 := Nat.mul_le_mul_right 24 hpts_le; omega
        have hne0 := ofNat_beq_zero_false_24 hlen_pos hlen_lt
        have hcap_ne : g.cap ≠ 0 := by intro hc0; rw [hc0] at hpts_le; simp at hpts_le
        simp only [hcap_ne, ↓reduceIte]
        refine seq_vm_clean (mid := (blkPl_298).base + 1448#64)
          (P_mid := arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 g.ptr (bs :: tl) ∗
            A.pool lim st s ∗ stackAt fsp allocHookStack ∗
            (A.live g.ptr (g.cap.toNat * 24) 8 ∗
              memRegion (g.ptr + BitVec.ofNat 64 ((bs :: tl).length * 24)) ((g.cap.toNat - (bs :: tl).length) * 24) ∗
              memRegion (fsp + 424#64) 40 ∗ Frame))
          (Q := fun sm => sm.sp = s.sp ∧ sm.v1TraceEq s ∧
            sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
            sm.readReg64 (Reg.gpr 22#5) = g.ptr ∧ sm.readReg64 (Reg.gpr 23#5) = g.cap ∧
            sm.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 (bs :: tl).length ∧
            sm.readReg64 (Reg.gpr 25#5) = g.ptr + 8#64)
          (by by_vm_steps (wp_steps; apply SepWP.fold hhdr40 (by sep_focus); wp_done)) ?_
        intro s_loop hpc_loop hrun_loop hvm_loop ⟨hsp_loop, htr_loop, hx21_loop, hx22_loop, hx23_loop, hx24_loop, hx25_loop⟩
        rw [← A.pool_of_vmPreserved hvm_loop]
        refine SepWP.mono (v1Tag8_err_dec_loop_1448_placed hDealloc (ptsPtr := g.ptr) (ptsCap := g.cap) hsp_align
          (bs :: tl) g.ptr st s_loop _
          (List.cons_ne_nil _ _) hlen_lt hpc_loop hrun_loop (hsp_loop.trans hsp)
          hx22_loop hx23_loop hx24_loop hx25_loop) ?_
        rintro sm _Pm _ _ ⟨evs_l, hevs_l, hPm, hspm, htrm, hx21_m, hx22_m, hx23_m⟩
        have hsplit : g.cap.toNat * 24 = (bs :: tl).length * 24 + (g.cap.toNat - (bs :: tl).length) * 24 := by
          rw [← Nat.add_mul]; congr 1; omega
        have hbound : (bs :: tl).length * 24 + (g.cap.toNat - (bs :: tl).length) * 24 ≤ 2 ^ 64 := by
          rw [← hsplit]; omega
        refine ⟨evs_l, hevs_l, Entails.trans hPm ?_,
          hspm.trans hsp_loop, htrm.trans htr_loop, hx21_m.trans hx21_loop, hx22_m, hx23_m⟩
        conv_rhs =>
          arg 1; arg 2
          rw [hsplit, ProofLib.memRegion_split g.ptr ((bs :: tl).length * 24)
                ((g.cap.toNat - (bs :: tl).length) * 24) hbound]
        exact Entails.of_eq (by ac_rfl)
    · intro evs1 s2 hevs1 hpc2 hrun2 ⟨hsp2, htr2, hx21_2, hx22_2, hx23_2⟩
      refine SepWP.mono (v1Tag8_err_pts_buf_2072_placed hDealloc (st := M.stepEvents evs1 st)
        hsp_align hpts_cap_lt hpc2 hrun2 (hsp2.trans hsp) hx22_2 hx23_2) ?_
      rintro sm _Pm _ _ ⟨evs2, hevs2, hPm, hspm, htrm, _hacpm, hx21_m⟩
      refine ⟨evs1 ++ evs2, hevs1.append hevs2, ?_,
        hspm.trans hsp2, htrm.trans htr2, hx21_m.trans hx21_2⟩
      rw [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
      exact Entails.trans hPm (Entails.of_eq (by ac_rfl))

/-! ## 3. Error & Pure Stack-Copy Stepping Lemmas for Tag 8 (`Ct1Sampled`) -/

theorem v1Tag8_err_uc_1364_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hDropUc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 286)
      (dropProtoUnchunkedCt1SentEkReceivedSpec M A lim))
    {st : M.σ} {s : State} {fsp : BitVec 64}
    {optUc : Option V1State.Unchunked.Ct1SentEkReceived} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1364#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 1384#64) s
      (optProtoUnchunkedCt1SentEkReceivedAt A.repAlloc (fsp + 240#64) optUc ∗
        A.pool lim st s ∗ stackAt fsp dropStack32 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ memRegion (fsp + 240#64) 128 ∗ A.pool lim (M.stepEvents evs st) sm ∗
          stackAt fsp dropStack32 ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
        sm.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5)) := by
  cases optUc with
  | none =>
    have hnone128 : ((fsp + 240#64) ↦₆₄ noneCap) ∗ memRegion (fsp + 248#64) 120 ⊢ memRegion (fsp + 240#64) 128 := by
      have h248 : (fsp + 240#64) + 8#64 = fsp + 248#64 := by bv_lin
      rw [← h248]; exact optProtoUnchunkedCt1SentEkReceivedAt_none_entails_memRegion_128 A.repAlloc (fsp + 240#64)
    rw [optProtoUnchunkedCt1SentEkReceivedAt_none, show (fsp + 240#64) + 8#64 = fsp + 248#64 by bv_lin]
    apply sepWP_evs_nil
    simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
    wp_steps; apply SepWP.fold hnone128 (by sep_focus); wp_done
  | some u =>
    rw [optProtoUnchunkedCt1SentEkReceivedAt_some]
    apply SepWP.fold (protoUnchunkedCt1SentEkReceivedAt_expose_cap A.repAlloc (fsp + 240#64) u) (by sep_focus)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro cap; apply SepWP.exists_elim; intro ptr; apply SepWP.pure_elim; intro hcap_lt
    have hne_none := cap_add_one_beq_zero_false hcap_lt
    refine seq_vm_clean (mid := lsmpl.base 286)
      (P_mid := protoUnchunkedCt1SentEkReceivedAt A.repAlloc (fsp + 240#64) u ∗
        A.pool lim st s ∗ stackAt fsp dropStack32 ∗ Frame)
      (Q := fun sc => sc.sp = fsp ∧ sc.v1TraceEq s ∧
        sc.readReg64 (Reg.gpr 0#5) = fsp + 240#64 ∧
        sc.readReg64 Reg.lr = (blkPl_298).base + 1384#64 ∧
        sc.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
        sc.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5))
      (by
        by_vm_steps (
          wp_steps
          apply SepWP.fold (protoUnchunkedCt1SentEkReceivedAt_unexpose_cap A.repAlloc (fsp + 240#64) cap ptr u) (by sep_focus)
          wp_done)) ?_
    intro sc hpcc hrunc hvmc ⟨hsp_c, htr_c, hx0_c, hlr_c, hx21_c, hx25_c⟩
    rw [← A.pool_of_vmPreserved hvmc, ← hsp_c]
    have _hlr_sc : LsRetAddr624 (sc.readReg64 (Reg.gpr 30#5)) := by
      change LsRetAddr624 (sc.readReg64 .lr); rw [hlr_c]
      simp (config := { decide := true }) only [arm64_norm, wp_norm]
    wp_call hDropUc (⟨fsp + 240#64, u⟩, st)
    rw [hsp_c]
    have hevs_w : FreeOnlyEvs w := by assumption
    dsimp only [protoUnchunkedCt1SentEkReceivedSize]
    refine SepWP.mono (post := fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 240#64) 128 ∗ A.pool lim (M.stepEvents w st) sm ∗
          stackAt fsp dropStack32 ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
        sm.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5))
      ?_ (fun _ _ _ _ ⟨hp, hq⟩ => ⟨w, hevs_w, hp, hq⟩)
    rcases htr_c with ⟨htr_cs, hvregs_cs⟩
    wp_done

theorem v1Tag8_err_enc_1384_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hDropEnc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 271) (dropProtoPolyEncoderSpec M A lim))
    {st : M.σ} {s : State} {fsp : BitVec 64} {optEnc : Option PolynomialEncoder} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1384#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hx25 : s.readReg64 (Reg.gpr 25#5) = fsp + 240#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 1404#64) s
      (optProtoPolynomialEncoderAt A.repAlloc (fsp + 368#64) (optEnc.map pbToProtoPolyEncoder) ∗
        A.pool lim st s ∗ stackAt fsp dropStack48 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ memRegion (fsp + 368#64) 56 ∗ A.pool lim (M.stepEvents evs st) sm ∗
          stackAt fsp dropStack48 ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) := by
  cases optEnc with
  | none =>
    have hnone56 : ((fsp + 368#64) ↦₆₄ noneCap) ∗ memRegion (fsp + 376#64) 48 ⊢ memRegion (fsp + 368#64) 56 := by
      have h376 : (fsp + 368#64) + 8#64 = fsp + 376#64 := by bv_lin
      rw [← h376]; exact optProtoPolyEncoder_none_entails_memRegion_56 (fsp + 368#64)
    simp only [Option.map_none, optProtoPolynomialEncoderAt_none', show (fsp + 368#64) + 8#64 = fsp + 376#64 by bv_lin]
    apply sepWP_evs_nil
    simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
    wp_steps; apply SepWP.fold hnone56 (by sep_focus); wp_done
  | some enc =>
    simp only [Option.map_some, optProtoPolynomialEncoderAt_some']
    apply SepWP.fold (protoPolynomialEncoderAt_expose_cap A.repAlloc (fsp + 368#64) (pbToProtoPolyEncoder enc)) (by sep_focus)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro cap; apply SepWP.exists_elim; intro ptr; apply SepWP.pure_elim; intro hcap_lt
    have hne_none := cap_add_one_beq_zero_false hcap_lt
    refine seq_vm_clean (mid := lsmpl.base 271)
      (P_mid := CryptoVerification.SpqrV1.Poly.protoPolynomialEncoderAt A.repAlloc (fsp + 368#64) (pbToProtoPolyEncoder enc) ∗
        A.pool lim st s ∗ stackAt fsp dropStack48 ∗ Frame)
      (Q := fun sc => sc.sp = fsp ∧ sc.v1TraceEq s ∧
        sc.readReg64 (Reg.gpr 0#5) = fsp + 368#64 ∧
        sc.readReg64 Reg.lr = (blkPl_298).base + 1404#64 ∧
        sc.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5))
      (by
        by_vm_steps (
          wp_steps
          apply SepWP.fold (protoPolynomialEncoderAt_unexpose_cap A.repAlloc (fsp + 368#64) cap ptr (pbToProtoPolyEncoder enc)) (by sep_focus)
          wp_done)) ?_
    intro sc hpcc hrunc hvmc ⟨hsp_c, htr_c, hx0_c, hlr_c, hx21_c⟩
    rw [← A.pool_of_vmPreserved hvmc, ← hsp_c]
    have _hlr_sc : LsRetAddr624 (sc.readReg64 (Reg.gpr 30#5)) := by
      change LsRetAddr624 (sc.readReg64 .lr); rw [hlr_c]
      simp (config := { decide := true }) only [arm64_norm, wp_norm]
    wp_call hDropEnc (⟨fsp + 368#64, pbToProtoPolyEncoder enc⟩, st)
    rw [hsp_c]
    have hevs_w : FreeOnlyEvs w := by assumption
    dsimp only [protoPolynomialEncoderSize]
    refine SepWP.mono (post := fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 368#64) 56 ∗ A.pool lim (M.stepEvents w st) sm ∗
          stackAt fsp dropStack48 ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5))
      ?_ (fun _ _ _ _ ⟨hp, hq⟩ => ⟨w, hevs_w, hp, hq⟩)
    rcases htr_c with ⟨htr_cs, hvregs_cs⟩
    wp_done

theorem v1Tag8_err_1364_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hDropUc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 286)
      (dropProtoUnchunkedCt1SentEkReceivedSpec M A lim))
    (hDropEnc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 271) (dropProtoPolyEncoderSpec M A lim))
    (hDealloc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    {st : M.σ} {s : State} {fsp : BitVec 64} {cs : V1State.Chunked.Ct1Sampled} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1364#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hx25 : s.readReg64 (Reg.gpr 25#5) = fsp + 240#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2700#64) s
      (protoChunkedCt1SampledAt A.repAlloc (fsp + 240#64) cs ∗
        A.pool lim st s ∗ stackAt fsp chunkedInlStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ memRegion (fsp + 240#64) 224 ∗ A.pool lim (M.stepEvents evs st) sm ∗
          stackAt fsp chunkedInlStack ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) := by
  dsimp only [protoChunkedCt1SampledAt]
  have h368 : (fsp + 240#64) + 128#64 = fsp + 368#64 := by bv_lin
  have h424 : (fsp + 240#64) + 184#64 = fsp + 424#64 := by bv_lin
  have hjoin224 : memRegion (fsp + 240#64) 128 ∗ memRegion (fsp + 368#64) 56 ∗ memRegion (fsp + 424#64) 40 ⊢
      memRegion (fsp + 240#64) 224 := by
    rw [memRegion_split' (b := fsp + 240#64) (b' := fsp + 368#64) (n := 128) (k := 96) (N := 224) rfl (by bv_lin) (by decide),
      memRegion_split' (b := fsp + 368#64) (b' := fsp + 424#64) (n := 56) (k := 40) (N := 96) rfl (by bv_lin) (by decide)]
    exact Entails.of_eq (by ac_rfl)
  refine SepWP.weaken_pre (P' :=
    optProtoUnchunkedCt1SentEkReceivedAt A.repAlloc (fsp + 240#64) (cs.uc.map ct1SentToCt1SentEkReceived) ∗
      A.pool lim st s ∗ stackAt fsp dropStack32 ∗
      (optProtoPolynomialEncoderAt A.repAlloc (fsp + 368#64) (cs.sendingCt1.map pbToProtoPolyEncoder) ∗
        optProtoPolynomialDecoderAt A.repAlloc (fsp + 424#64) (cs.receivingEk.map pbToProtoPolyDecoder) ∗
        v1StateBelowRest fsp dropStack32 ∗ Frame))
    (Entails.of_eq (by rw [v1Tag8_optProtoUnchunkedCt1SentAt_eq, h368, h424, v1StateBelow_dropStack32 fsp]; ac_rfl)) ?_
  refine SepWP.seq (v1Tag8_err_uc_1364_placed hDropUc hsp_align hpc hrun hsp) ?_
  rintro s1 P1 hpc1 hrun1 ⟨evs1, hevs1, hP1, hsp1, htr1, hx21_1, hx25_1⟩
  apply SepWP.weaken_pre hP1; apply SepWP.fold (v1StateBelow_dropStack32_entails fsp) (by sep_focus)
  refine SepWP.weaken_pre (P' :=
    optProtoPolynomialEncoderAt A.repAlloc (fsp + 368#64) (cs.sendingCt1.map pbToProtoPolyEncoder) ∗
      A.pool lim (M.stepEvents evs1 st) s1 ∗ stackAt fsp dropStack48 ∗
      (memRegion (fsp + 240#64) 128 ∗
        optProtoPolynomialDecoderAt A.repAlloc (fsp + 424#64) (cs.receivingEk.map pbToProtoPolyDecoder) ∗
        v1StateBelowRest fsp dropStack48 ∗ Frame))
    (Entails.of_eq (by rw [v1StateBelow_dropStack48 fsp]; ac_rfl)) ?_
  refine SepWP.seq (v1Tag8_err_enc_1384_placed hDropEnc hsp_align hpc1 hrun1 (hsp1.trans hsp) (hx25_1.trans hx25)) ?_
  rintro s2 P2 hpc2 hrun2 ⟨evs2, hevs2, hP2, hsp2, htr2, hx21_2⟩
  apply SepWP.weaken_pre hP2; apply SepWP.fold (v1StateBelow_dropStack48_entails fsp) (by sep_focus)
  refine SepWP.weaken_pre (P' :=
    optProtoPolynomialDecoderAt A.repAlloc (fsp + 424#64) (cs.receivingEk.map pbToProtoPolyDecoder) ∗
      A.pool lim (M.stepEvents evs2 (M.stepEvents evs1 st)) s2 ∗ stackAt fsp allocHookStack ∗
      (memRegion (fsp + 240#64) 128 ∗ memRegion (fsp + 368#64) 56 ∗ v1StateBelowRest fsp allocHookStack ∗ Frame))
    (Entails.of_eq (by rw [v1StateBelow_allocHook fsp]; ac_rfl)) ?_
  refine SepWP.seq (v1Tag8_err_dec_1404_placed hDealloc hsp_align hpc2 hrun2 (hsp2.trans (hsp1.trans hsp))) ?_
  rintro s3 P3 hpc3 hrun3 ⟨evs3, hevs3, hP3, hsp3, htr3, hx21_3⟩
  apply SepWP.weaken_pre hP3; apply SepWP.fold (v1StateBelow_allocHook_entails fsp) (by sep_focus)
  apply SepWP.fold hjoin224 (by sep_focus)
  refine SepWP.done hpc3 hrun3
    ⟨evs1 ++ evs2 ++ evs3, (hevs1.append hevs2).append hevs3, ?_,
      hsp3.trans (hsp2.trans hsp1), htr3.trans (htr2.trans htr1), hx21_3.trans (hx21_2.trans hx21_1)⟩
  simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
  exact Entails.of_eq (by ac_rfl)

theorem v1Tag8_setup_1272_placed [LibsignalPlacement]
    {A : CryptoVerification.RustHeap.RustAlloc} {H : String → Option (State → State)}
    {s : State} {fsp w_sp16 w_sp144 w_sp200 : BitVec 64} {restLen : Nat} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1272#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 300) s
      (((fsp + 16#64) ↦₆₄ w_sp16) ∗ memRegion (fsp + 24#64) 120 ∗
        ((fsp + 144#64) ↦₆₄ w_sp144) ∗ memRegion (fsp + 152#64) 48 ∗
        ((fsp + 200#64) ↦₆₄ w_sp200) ∗ memRegion (fsp + 208#64) 32 ∗ Frame)
      (fun s1 P1 =>
        VmPreserved s s1 ∧
        (P1 ⊢ chunkedCt1SampledPBCapAt A (fsp + 16#64) restLen default ∗ Frame) ∧
        s1.sp = s.sp ∧ s1.v1TraceEq s ∧ s1.readReg64 (Reg.gpr 0#5) = s.readReg64 (Reg.gpr 0#5) ∧
        s1.readReg64 (Reg.gpr 1#5) = fsp + 16#64 ∧ s1.readReg64 (Reg.gpr 2#5) = s.readReg64 (Reg.gpr 19#5) ∧
        s1.readReg64 Reg.lr = (blkPl_298).base + 1296#64 ∧
        s1.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧ s1.readReg64 (Reg.gpr 20#5) = s.readReg64 (Reg.gpr 20#5) ∧
        s1.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) ∧ s1.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 ∧
        s1.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧ s1.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧
        s1.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧ s1.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧
        s1.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧ s1.readReg64 (Reg.gpr 29#5) = s.readReg64 (Reg.gpr 29#5)) := by
  have hdef : ((fsp + 16#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (fsp + 24#64) 120 ∗
      ((fsp + 144#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (fsp + 152#64) 48 ∗
      ((fsp + 200#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (fsp + 208#64) 32 ⊢
      chunkedCt1SampledPBCapAt A (fsp + 16#64) restLen default := by
    change _ ⊢ chunkedCt1SampledPBCapAt A (fsp + 16#64) restLen ⟨none, none, none⟩
    dsimp only [chunkedCt1SampledPBCapAt, optUnchunkedCt1SentPBCapAt, optPolynomialEncoderPBAt, optPolynomialDecoderPBAt, noneCap]
    have h24 : (fsp + 16#64) + 8#64 = fsp + 24#64 := by bv_lin
    have h144 : (fsp + 16#64) + 128#64 = fsp + 144#64 := by bv_lin
    have h152 : (fsp + 144#64) + 8#64 = fsp + 152#64 := by bv_lin
    have h200 : (fsp + 16#64) + 184#64 = fsp + 200#64 := by bv_lin
    have h208 : (fsp + 200#64) + 8#64 = fsp + 208#64 := by bv_lin
    rw [h24, h144, h152, h200, h208]; exact Entails.of_eq (by ac_rfl)
  by_vm_steps (wp_steps; apply SepWP.fold hdef (by sep_focus); wp_done)

theorem v1Tag8_copy_ok_1296_placed [LibsignalPlacement] {H : String → Option (State → State)}
    {s : State} {fsp mPtr w_sp464 : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 : BitVec 64}
    {Frame : SepProp} (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1296#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = 0#64) (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2508#64) s
      (v1Tag8_words28At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 ∗
        memRegion (fsp + 240#64) 224 ∗ ((fsp + 464#64) ↦₆₄ w_sp464) ∗ Frame)
      (fun sm Pm =>
        VmPreserved s sm ∧
        (Pm ⊢ v1Tag8_words28At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 ∗
          memRegion (fsp + 240#64) 224 ∗ ((fsp + 464#64) ↦₆₄ mPtr) ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧ sm.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
        sm.readReg64 (Reg.gpr 20#5) = mPtr ∧ sm.readReg64 (Reg.gpr 21#5) = 0#64 ∧
        sm.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) ∧ sm.readReg64 (Reg.gpr 23#5) = s.readReg64 (Reg.gpr 23#5) ∧
        sm.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧ sm.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧
        sm.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧ sm.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧
        sm.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧ sm.readReg64 (Reg.gpr 29#5) = s.readReg64 (Reg.gpr 29#5)) := by
  have hfold240 := v1Tag8_words28At_entails_memRegion_224 (fsp + 240#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27
  conv => arg 4; rw [v1Tag8_memRegion_224_eq_words28 (fsp + 240#64)]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v2; apply SepWP.exists_elim; intro v1; apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v5
  apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v3; apply SepWP.exists_elim; intro v8; apply SepWP.exists_elim; intro v7
  apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v15; apply SepWP.exists_elim; intro v14; apply SepWP.exists_elim; intro v13
  apply SepWP.exists_elim; intro v12; apply SepWP.exists_elim; intro v11; apply SepWP.exists_elim; intro v10; apply SepWP.exists_elim; intro v9
  apply SepWP.exists_elim; intro v22; apply SepWP.exists_elim; intro v21; apply SepWP.exists_elim; intro v20; apply SepWP.exists_elim; intro v19
  apply SepWP.exists_elim; intro v18; apply SepWP.exists_elim; intro v17; apply SepWP.exists_elim; intro v16; apply SepWP.exists_elim; intro v27
  apply SepWP.exists_elim; intro v26; apply SepWP.exists_elim; intro v25; apply SepWP.exists_elim; intro v24; apply SepWP.exists_elim; intro v23
  have hbr : (s.readReg64 (Reg.gpr 0#5) == 0#64) = true := by rw [hx0]; rfl
  dsimp only [v1Tag8_words28At, words16At, words13At, words10At, words7At, words5At, words3At] at hfold240 ⊢
  by_vm_steps (wp_steps; apply SepWP.fold hfold240 (by sep_focus); wp_done)

theorem v1Tag8_copy_err_1296_placed [LibsignalPlacement] {H : String → Option (State → State)}
    {s : State} {fsp mPtr w_sp464 : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 : BitVec 64}
    {Frame : SepProp} (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1296#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) ≠ 0#64) (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 1364#64) s
      (v1Tag8_words28At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 ∗
        memRegion (fsp + 240#64) 224 ∗ ((fsp + 464#64) ↦₆₄ w_sp464) ∗ Frame)
      (fun sm Pm =>
        VmPreserved s sm ∧
        (Pm ⊢ memRegion (fsp + 16#64) 224 ∗
          v1Tag8_words28At (fsp + 240#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 ∗
          ((fsp + 464#64) ↦₆₄ mPtr) ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 0#5) ∧
        sm.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5)) := by
  have hfold16 := v1Tag8_words28At_entails_memRegion_224 (fsp + 16#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27
  conv => arg 4; rw [v1Tag8_memRegion_224_eq_words28 (fsp + 240#64)]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v2; apply SepWP.exists_elim; intro v1; apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v5
  apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v3; apply SepWP.exists_elim; intro v8; apply SepWP.exists_elim; intro v7
  apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v15; apply SepWP.exists_elim; intro v14; apply SepWP.exists_elim; intro v13
  apply SepWP.exists_elim; intro v12; apply SepWP.exists_elim; intro v11; apply SepWP.exists_elim; intro v10; apply SepWP.exists_elim; intro v9
  apply SepWP.exists_elim; intro v22; apply SepWP.exists_elim; intro v21; apply SepWP.exists_elim; intro v20; apply SepWP.exists_elim; intro v19
  apply SepWP.exists_elim; intro v18; apply SepWP.exists_elim; intro v17; apply SepWP.exists_elim; intro v16; apply SepWP.exists_elim; intro v27
  apply SepWP.exists_elim; intro v26; apply SepWP.exists_elim; intro v25; apply SepWP.exists_elim; intro v24; apply SepWP.exists_elim; intro v23
  have hbr : (s.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0
  dsimp only [v1Tag8_words28At, words16At, words13At, words10At, words7At, words5At, words3At] at hfold16 ⊢
  by_vm_steps (wp_steps; apply SepWP.fold hfold16 (by sep_focus); wp_done)

theorem v1Tag8_pre_drop_2508_placed [LibsignalPlacement] {H : String → Option (State → State)}
    {s : State} {fsp mPtr : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 : BitVec 64}
    {Frame : SepProp} (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 2508#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr) (hx29 : s.readReg64 (Reg.gpr 29#5) = fsp + 720#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2568#64) s
      (v1Tag8_words28At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 ∗
        memRegion (fsp + 480#64) 224 ∗ Frame)
      (fun sm Pm =>
        VmPreserved s sm ∧
        (Pm ⊢ memRegion (fsp + 16#64) 224 ∗
          v1Tag8_words28At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧ sm.readReg64 (Reg.gpr 0#5) = mPtr ∧
        sm.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧ sm.readReg64 (Reg.gpr 20#5) = mPtr ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧ sm.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) ∧
        sm.readReg64 (Reg.gpr 23#5) = s.readReg64 (Reg.gpr 23#5) ∧ sm.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧
        sm.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧ sm.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
        sm.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧ sm.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
        sm.readReg64 (Reg.gpr 29#5) = fsp + 720#64) := by
  have hfold16 := v1Tag8_words28At_entails_memRegion_224 (fsp + 16#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27
  conv => arg 4; rw [v1Tag8_memRegion_224_eq_words28 (fsp + 480#64)]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro u2; apply SepWP.exists_elim; intro u1; apply SepWP.exists_elim; intro u0; apply SepWP.exists_elim; intro u5
  apply SepWP.exists_elim; intro u4; apply SepWP.exists_elim; intro u3; apply SepWP.exists_elim; intro u8; apply SepWP.exists_elim; intro u7
  apply SepWP.exists_elim; intro u6; apply SepWP.exists_elim; intro u15; apply SepWP.exists_elim; intro u14; apply SepWP.exists_elim; intro u13
  apply SepWP.exists_elim; intro u12; apply SepWP.exists_elim; intro u11; apply SepWP.exists_elim; intro u10; apply SepWP.exists_elim; intro u9
  apply SepWP.exists_elim; intro u22; apply SepWP.exists_elim; intro u21; apply SepWP.exists_elim; intro u20; apply SepWP.exists_elim; intro u19
  apply SepWP.exists_elim; intro u18; apply SepWP.exists_elim; intro u17; apply SepWP.exists_elim; intro u16; apply SepWP.exists_elim; intro u27
  apply SepWP.exists_elim; intro u26; apply SepWP.exists_elim; intro u25; apply SepWP.exists_elim; intro u24; apply SepWP.exists_elim; intro u23
  dsimp only [v1Tag8_words28At, words16At, words13At, words10At, words7At, words5At, words3At] at hfold16 ⊢
  by_vm_steps (wp_steps; apply SepWP.fold hfold16 (by sep_focus); wp_done)

theorem v1Tag8_post_drop_2568_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267) (dropOptProtoInnerStatePlacedSpec M A lim))
    {st : M.σ} {s : State} {fsp mPtr : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 : BitVec 64}
    {is : Option V1State.InnerState} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 2568#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = mPtr) (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = fsp + 720#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2700#64) s
      (optProtoInnerStateAt A.repAlloc mPtr is ∗ A.pool lim st s ∗
        optProtoInnerStateJumpTablePlacedAt ∗ stackAt fsp dropStack96 ∗
        v1Tag8_words28At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ v1Tag8_words28At mPtr w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 ∗
          memRegion (fsp + 480#64) 224 ∗ A.pool lim (M.stepEvents evs st) sm ∗
          optProtoInnerStateJumpTablePlacedAt ∗ stackAt fsp dropStack96 ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧ sm.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
        sm.readReg64 (Reg.gpr 20#5) = mPtr ∧ sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
        sm.readReg64 (Reg.gpr 22#5) = 0x8000000000000000#64 ∧
        sm.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 ∧
        sm.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧
        sm.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧
        sm.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
        sm.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧
        sm.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
        sm.readReg64 (Reg.gpr 29#5) = fsp + 720#64) := by
  have hfold480 := v1Tag8_words28At_entails_memRegion_224 (fsp + 480#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27
  simp only [dropOptProtoInnerStatePlacedSpec] at hDropInner
  wp_steps
  wp_call hDropInner (⟨mPtr, is⟩, st)
  have hevs_w : FreeOnlyEvs w := by assumption
  dsimp only [optProtoInnerStateSize]
  conv => arg 4; rw [v1Tag8_memRegion_224_eq_words28 mPtr]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro d2; apply SepWP.exists_elim; intro d1; apply SepWP.exists_elim; intro d0; apply SepWP.exists_elim; intro d5
  apply SepWP.exists_elim; intro d4; apply SepWP.exists_elim; intro d3; apply SepWP.exists_elim; intro d8; apply SepWP.exists_elim; intro d7
  apply SepWP.exists_elim; intro d6; apply SepWP.exists_elim; intro d15; apply SepWP.exists_elim; intro d14; apply SepWP.exists_elim; intro d13
  apply SepWP.exists_elim; intro d12; apply SepWP.exists_elim; intro d11; apply SepWP.exists_elim; intro d10; apply SepWP.exists_elim; intro d9
  apply SepWP.exists_elim; intro d22; apply SepWP.exists_elim; intro d21; apply SepWP.exists_elim; intro d20; apply SepWP.exists_elim; intro d19
  apply SepWP.exists_elim; intro d18; apply SepWP.exists_elim; intro d17; apply SepWP.exists_elim; intro d16; apply SepWP.exists_elim; intro d27
  apply SepWP.exists_elim; intro d26; apply SepWP.exists_elim; intro d25; apply SepWP.exists_elim; intro d24; apply SepWP.exists_elim; intro d23
  dsimp only [v1Tag8_words28At, words16At, words13At, words10At, words7At, words5At, words3At] at hfold480 ⊢
  refine SepWP.mono (post := fun sm Pm =>
      VmPreserved sf sm ∧
      (Pm ⊢ v1Tag8_words28At mPtr w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 ∗
        memRegion (fsp + 480#64) 224 ∗ A.pool lim (M.stepEvents w st) sf ∗
        optProtoInnerStateJumpTablePlacedAt ∗ stackAt fsp dropStack96 ∗ Frame) ∧
      sm.sp = s.sp ∧ sm.v1TraceEq s ∧ sm.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
      sm.readReg64 (Reg.gpr 20#5) = mPtr ∧ sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
      sm.readReg64 (Reg.gpr 22#5) = 0x8000000000000000#64 ∧
      sm.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 ∧
      sm.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧
      sm.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧
      sm.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
      sm.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧
      sm.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
      sm.readReg64 (Reg.gpr 29#5) = fsp + 720#64)
    ?_ (fun sm _Pm _ _ ⟨hvm, hp, hq⟩ => by
      refine ⟨w, hevs_w, ?_, hq⟩
      rw [A.pool_of_vmPreserved hvm]
      exact hp)
  dsimp only [v1Tag8_words28At, words16At, words13At, words10At, words7At, words5At, words3At]
  by_vm_steps (wp_steps; apply SepWP.fold hfold480 (by sep_focus); wp_done)

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag8BudgetAux

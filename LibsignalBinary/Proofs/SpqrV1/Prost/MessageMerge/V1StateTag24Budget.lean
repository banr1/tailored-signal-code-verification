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
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunked1Budget
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1Budget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag24
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Shared 20-Word Helpers and Tag Arm 4 (`Ct1Received`) for `V1State::merge`

`RustCliAllocBudget`-threaded `[LibsignalPlacement]` shared 20-word (`160` B) error-drop and
stack-copy helpers for tags 2 (`KeysSampled`) and 4 (`Ct1Received`), plus verification of tag arm 4
(Block `298`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

open CryptoVerification (LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalProtoCodec (WireType)
open CryptoVerification.LibsignalSpqrV1 (PolynomialEncoder V1State)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage mergeOptMessage)
open CryptoVerification.LibsignalTripleRatchet (
  LibsignalCodeRoLoaded decodeErrorAtStackLen withLsCodeRoLoaded
)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  pointsToBytes_prefix_join sliceCursorAfter sliceCursorAfter_eq_split
  sliceCursorAfter_join sliceCursorAt
)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.SpqrV1.Drop (
  DropOptProtoInnerStateGhost dropStack48 dropStack96 optProtoInnerStateAt
  optProtoInnerStateJumpTablePlacedAt optProtoInnerStateSize protoChunkedCt1ReceivedAt
  protoChunkedCt1ReceivedSize
)
open CryptoVerification.SpqrV1.ProtoRepr (optPolynomialEncoderPBAt)
open CryptoVerification.SpqrV1.Prost.MessageMerge (
  ChunkedCt1ReceivedMergeGhost InnerStateDiscrFull OptInnerStatePolyBound OptPolyEncoderBound
  SepWPp.call_frame_lscro SepWPp.of_sepWP_lscro
  V1StateLoopRegsPlaced V1StateMergeGhost V1StateTagEntryHypPlaced WppPost
  bv64_add_zero bv64_sub_zero
  chunkedCt1ReceivedPBAt chunkedCt1ReceivedPBCapAt chunkedCt1ReceivedPBAt_eq_proto
  chunkedInlStack chunkedMergeStack
  chunkedCt1ReceivedPBAt_entails_cap_zero chunkedKeysSampledPBAt_entails_cap_zero
  codecWireTypeToProto ct1Received_polyBound_extract
  discrFull_none_add2 discrFull_other_tag4 discrFull_some_add2
  innerStatePolyBound_of_ct1Received
  memRegion_160_eq_words20 memRegion_160_split_tag24_init
  memRegion_224_split_tag24_ok memRegion_fold_tag24_temp memRegion_split_tag24_temp
  mergeMessage_measure_lt
  optInnerStatePolyBound_lt_2_56 optPolyEncoderBound_iff optPolyEncoderBound_none
  optPolyEncoderPolysLen optPolyEncoderPtsLen
  optPolyEncoder_getD_default_polys_len optPolyEncoder_getD_default_pts_len
  optProtoInnerStateAt_entails_exists optProtoInnerStateCapAt optProtoInnerStateCapAt_entails_pb
  optUnchunked4CapAt optUnchunkedEkSentCt1ReceivedPBCapAt_eq_optUnchunked4
  polyEncoder_mergeMessage_pts_polys_len protoInnerStateCapAt
  protoPrefixStep_chunked_ct1Received_mergeField proto_mergeMessage_len_le
  tag2_reconstruct_innerState tag24CapHeap tag24_extract_words tag24_of_words
  tag24_words_entails_protoChunkedCt1Received tag4_reconstruct_innerState
  v1StateBelowRest v1StateBelow_dropStack48 v1StateBelow_dropStack48_entails
  v1StateBelow_dropStack96 v1StateBelow_dropStack96_entails
  v1StateJumpTablesPlacedAt v1StateMergeJumpTablePlacedExpanded v1StateSavedRegsAt
  v1State_mergeField_tag4
  words20At words20At_entails_memRegion_160
  words13At words10At words7At words3At
)
open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2 (blkPC_298 blkPl_298)
open scoped CryptoVerification.SpqrV1.Prost.MessageMerge.Part2
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs
  RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunked1Budget (
  dropProtoChunkedCt1ReceivedSpec
)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget (
  dropOptProtoInnerStatePlacedSpec
)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget (
  ChunkedCt1ReceivedMergeEnv ChunkedCt1ReceivedMergePostEnv
  SpqrMergeIterEnv SpqrMergeLoopEnv chunkedCt1ReceivedMergeSpec chunkedCt1ReceivedMergeSpecOfEnv
  ct1ReceivedPolyCapBound
)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefsBudget (
  optInnerStatePolyCapBound
  v1StateErrFramePlaced v1StateLoopPrePlaced v1StateMergePlacedSpec
)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1BudgetAux (
  V1StateTagContPlaced V1StateTagEntryBudgetPlaced V1StateTagStepHypPlaced WppPanicFalse
  ct1ReceivedPolyCapBound_le optInnerStatePolyCapBound_of_ct1Received
  sepWPp_congr_state_pre wppPanicFalse_of_false
)

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag24Budget

open Arm64 ProofLib SepProp
open ProofLib.ProgramReflection
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local irreducible] v1StateMergeJumpTablePlacedExpanded optProtoInnerStateJumpTablePlacedAt v1StateSavedRegsAt
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero

private theorem seq_vm_clean {P : Program} {b : BitVec 64} {Hk : String → Option (State → State)}
    {mid target : BitVec 64} {s : State}
    {Pre P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP (P.rebase b Hk) mid s Pre (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → VmPreserved s sm → Q sm →
      SepWP (P.rebase b Hk) target sm P_mid post) :
    SepWP (P.rebase b Hk) target s Pre post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨hvm, hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hvm hQ)

/-! ## 1. Shared 20-Word (`160`B) Error-Drop & Stack-Copy Helpers for Tag 2 & Tag 4 -/

theorem v1State_tag24_err_1640_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hDropCr : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 282)
      (dropProtoChunkedCt1ReceivedSpec M A lim))
    {st : M.σ} {s : State} {fsp : BitVec 64} {cr : V1State.Chunked.Ct1Received} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1640#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2700#64) s
      (protoChunkedCt1ReceivedAt A.repAlloc (fsp + 240#64) cr ∗
        A.pool lim st s ∗ stackAt fsp dropStack48 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ memRegion (fsp + 240#64) 160 ∗ A.pool lim (M.stepEvents evs st) sm ∗
          stackAt fsp dropStack48 ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) := by
  refine seq_vm_clean (mid := lsmpl.base 282)
    (P_mid := protoChunkedCt1ReceivedAt A.repAlloc (fsp + 240#64) cr ∗
      A.pool lim st s ∗ stackAt fsp dropStack48 ∗ Frame)
    (Q := fun sc => sc.sp = fsp ∧ sc.v1TraceEq s ∧
      sc.readReg64 (Reg.gpr 0#5) = fsp + 240#64 ∧
      sc.readReg64 Reg.lr = (blkPl_298).base + 1648#64 ∧
      sc.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5))
    (by by_vm_steps (wp_steps; wp_done)) ?_
  intro sc hpcc hrunc hvmc ⟨hsp_c, htr_c, hx0_c, hlr_c, hx21_c⟩
  rw [← A.pool_of_vmPreserved hvmc, ← hsp_c]
  have _hlr_sc : LsRetAddr624 (sc.readReg64 (Reg.gpr 30#5)) := by
    change LsRetAddr624 (sc.readReg64 .lr); rw [hlr_c]
    simp (config := { decide := true }) only [arm64_norm, wp_norm]
  wp_call hDropCr (⟨fsp + 240#64, cr⟩, st)
  rw [hsp_c]
  have hevs_w : FreeOnlyEvs w := by assumption
  dsimp only [protoChunkedCt1ReceivedSize]
  refine SepWP.mono (post := fun sm Pm =>
      (Pm ⊢ memRegion (fsp + 240#64) 160 ∗ A.pool lim (M.stepEvents w st) sm ∗
        stackAt fsp dropStack48 ∗ Frame) ∧
      sm.sp = s.sp ∧ sm.v1TraceEq s ∧
      sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5))
    ?_ (fun _ _ _ _ ⟨hp, hq⟩ => ⟨w, hevs_w, hp, hq⟩)
  rcases htr_c with ⟨htr_cs, hvregs_cs⟩
  wp_steps; wp_done

theorem v1State_tag24_setup_placed (isTag4 : Bool) [LibsignalPlacement]
    {A : CryptoVerification.RustHeap.RustAlloc}
    {H : String → Option (State → State)}
    {s : State} {fsp w_sp16 w_sp120 : BitVec 64} {restLen : Nat} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + (if isTag4 then 1140#64 else 1568#64))
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      (if isTag4 then lsmpl.base 303 else lsmpl.base 304) s
      (((fsp + 16#64) ↦₆₄ w_sp16) ∗ memRegion (fsp + 24#64) 96 ∗
        ((fsp + 120#64) ↦₆₄ w_sp120) ∗ memRegion (fsp + 128#64) 48 ∗ Frame)
      (fun s1 P1 =>
        VmPreserved s s1 ∧
        (P1 ⊢ optUnchunked4CapAt A (fsp + 16#64) restLen none ∗
          optPolynomialEncoderPBAt A ((fsp + 16#64) + 104#64) none ∗ Frame) ∧
        s1.sp = s.sp ∧ s1.v1TraceEq s ∧
        s1.readReg64 (Reg.gpr 0#5) = s.readReg64 (Reg.gpr 0#5) ∧
        s1.readReg64 (Reg.gpr 1#5) = fsp + 16#64 ∧
        s1.readReg64 (Reg.gpr 2#5) = s.readReg64 (Reg.gpr 19#5) ∧
        s1.readReg64 Reg.lr = (blkPl_298).base + (if isTag4 then 1160#64 else 1588#64) ∧
        s1.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
        s1.readReg64 (Reg.gpr 20#5) = s.readReg64 (Reg.gpr 20#5) ∧
        s1.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) ∧
        s1.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 ∧
        s1.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧
        s1.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧
        s1.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
        s1.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧
        s1.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
        s1.readReg64 (Reg.gpr 29#5) = s.readReg64 (Reg.gpr 29#5)) := by
  have hdef : ((fsp + 16#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (fsp + 24#64) 96 ∗
      ((fsp + 120#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (fsp + 128#64) 48 ⊢
      optUnchunked4CapAt A (fsp + 16#64) restLen none ∗
        optPolynomialEncoderPBAt A ((fsp + 16#64) + 104#64) none := by
    dsimp only [optUnchunked4CapAt, optPolynomialEncoderPBAt, noneCap]
    have h24 : (fsp + 16#64) + 8#64 = fsp + 24#64 := by bv_lin
    have h120 : (fsp + 16#64) + 104#64 = fsp + 120#64 := by bv_lin
    have h128 : (fsp + 120#64) + 8#64 = fsp + 128#64 := by bv_lin
    rw [h24, h120, h128]; exact Entails.of_eq (by ac_rfl)
  cases isTag4 <;> simp only [Bool.false_eq_true, ↓reduceIte] at hpc ⊢
  · by_vm_steps (wp_steps; apply SepWP.fold hdef (by sep_focus); wp_done)
  · by_vm_steps (wp_steps; apply SepWP.fold hdef (by sep_focus); wp_done)

theorem v1State_tag24_copy_ok_placed (isTag4 : Bool) [LibsignalPlacement]
    {H : String → Option (State → State)}
    {s : State} {fsp mPtr w_sp400 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : BitVec 64}
    {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + (if isTag4 then 1160#64 else 1588#64))
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = 0#64)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + (if isTag4 then 1212#64 else 2712#64)) s
      (words20At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ∗
        memRegion (fsp + 240#64) 160 ∗ ((fsp + 400#64) ↦₆₄ w_sp400) ∗ Frame)
      (fun sm Pm =>
        VmPreserved s sm ∧
        (Pm ⊢ words20At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ∗
          memRegion (fsp + 240#64) 160 ∗ ((fsp + 400#64) ↦₆₄ mPtr) ∗ Frame) ∧
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
  have hfold240 := words20At_entails_memRegion_160 (fsp + 240#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19
  conv =>
    arg 4
    rw [memRegion_160_eq_words20 (fsp + 240#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v2; apply SepWP.exists_elim; intro v1
  apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v5
  apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v3
  apply SepWP.exists_elim; intro v12; apply SepWP.exists_elim; intro v11
  apply SepWP.exists_elim; intro v10; apply SepWP.exists_elim; intro v9
  apply SepWP.exists_elim; intro v8; apply SepWP.exists_elim; intro v7
  apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v19
  apply SepWP.exists_elim; intro v18; apply SepWP.exists_elim; intro v17
  apply SepWP.exists_elim; intro v16; apply SepWP.exists_elim; intro v15
  apply SepWP.exists_elim; intro v14; apply SepWP.exists_elim; intro v13
  cases isTag4 <;> simp only [Bool.false_eq_true, ↓reduceIte] at hpc ⊢
  · have hbr : (s.readReg64 (Reg.gpr 0#5) == 0#64) = true := by rw [hx0]; rfl
    dsimp only [words20At, words13At, words3At, words10At, words7At] at hfold240 ⊢
    by_vm_steps (wp_steps; apply SepWP.fold hfold240 (by sep_focus); wp_done)
  · have hbr : (s.readReg64 (Reg.gpr 0#5) != 0#64) = false := by rw [hx0]; rfl
    dsimp only [words20At, words13At, words3At, words10At, words7At] at hfold240 ⊢
    by_vm_steps (wp_steps; apply SepWP.fold hfold240 (by sep_focus); wp_done)

theorem v1State_tag24_copy_err_placed (isTag4 : Bool) [LibsignalPlacement]
    {H : String → Option (State → State)}
    {s : State} {fsp mPtr w_sp400 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : BitVec 64}
    {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + (if isTag4 then 1160#64 else 1588#64))
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) ≠ 0#64)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 1640#64) s
      (words20At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ∗
        memRegion (fsp + 240#64) 160 ∗ ((fsp + 400#64) ↦₆₄ w_sp400) ∗ Frame)
      (fun sm Pm =>
        VmPreserved s sm ∧
        (Pm ⊢ memRegion (fsp + 16#64) 160 ∗
          words20At (fsp + 240#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ∗
          ((fsp + 400#64) ↦₆₄ mPtr) ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 0#5)) := by
  have hfold16 := words20At_entails_memRegion_160 (fsp + 16#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19
  rw [memRegion_160_eq_words20 (fsp + 240#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v2; apply SepWP.exists_elim; intro v1
  apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v5
  apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v3
  apply SepWP.exists_elim; intro v12; apply SepWP.exists_elim; intro v11
  apply SepWP.exists_elim; intro v10; apply SepWP.exists_elim; intro v9
  apply SepWP.exists_elim; intro v8; apply SepWP.exists_elim; intro v7
  apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v19
  apply SepWP.exists_elim; intro v18; apply SepWP.exists_elim; intro v17
  apply SepWP.exists_elim; intro v16; apply SepWP.exists_elim; intro v15
  apply SepWP.exists_elim; intro v14; apply SepWP.exists_elim; intro v13
  cases isTag4 <;> simp only [Bool.false_eq_true, ↓reduceIte] at hpc ⊢
  · have hbr : (s.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0
    dsimp only [words20At, words13At, words3At, words10At, words7At] at hfold16 ⊢
    by_vm_steps (wp_steps; apply SepWP.fold hfold16 (by sep_focus); wp_done)
  · have hbr : (s.readReg64 (Reg.gpr 0#5) != 0#64) = true := bne_iff_ne.mpr hx0
    dsimp only [words20At, words13At, words3At, words10At, words7At] at hfold16 ⊢
    by_vm_steps (wp_steps; apply SepWP.fold hfold16 (by sep_focus); wp_done)

theorem v1State_tag24_pre_drop_placed (isTag4 : Bool) [LibsignalPlacement]
    {H : String → Option (State → State)}
    {s : State} {fsp mPtr w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : BitVec 64}
    {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + (if isTag4 then 1212#64 else 2712#64))
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = fsp + 720#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + (if isTag4 then 1256#64 else 2756#64)) s
      (words20At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ∗
        memRegion (fsp + 480#64) 160 ∗ Frame)
      (fun sm Pm =>
        VmPreserved s sm ∧
        (Pm ⊢ memRegion (fsp + 16#64) 160 ∗
          words20At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ∗ Frame) ∧
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
  have hfold16 := words20At_entails_memRegion_160 (fsp + 16#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19
  rw [memRegion_160_eq_words20 (fsp + 480#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v2; apply SepWP.exists_elim; intro v1
  apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v5
  apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v3
  apply SepWP.exists_elim; intro v12; apply SepWP.exists_elim; intro v11
  apply SepWP.exists_elim; intro v10; apply SepWP.exists_elim; intro v9
  apply SepWP.exists_elim; intro v8; apply SepWP.exists_elim; intro v7
  apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v19
  apply SepWP.exists_elim; intro v18; apply SepWP.exists_elim; intro v17
  apply SepWP.exists_elim; intro v16; apply SepWP.exists_elim; intro v15
  apply SepWP.exists_elim; intro v14; apply SepWP.exists_elim; intro v13
  cases isTag4 <;> simp only [Bool.false_eq_true, ↓reduceIte] at hpc ⊢
  · dsimp only [words20At, words13At, words3At, words10At, words7At] at hfold16 ⊢
    by_vm_steps (wp_steps; apply SepWP.fold hfold16 (by sep_focus); wp_done)
  · dsimp only [words20At, words13At, words3At, words10At, words7At] at hfold16 ⊢
    by_vm_steps (wp_steps; apply SepWP.fold hfold16 (by sep_focus); wp_done)

theorem v1State_tag24_post_drop_placed (isTag4 : Bool) [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267)
      (dropOptProtoInnerStatePlacedSpec M A lim))
    {st : M.σ} {s : State}
    {fsp mPtr w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : BitVec 64}
    {is : Option V1State.InnerState} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base +
      (if isTag4 then 1256#64 else 2756#64))
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = mPtr)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = fsp + 720#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2700#64) s
      (optProtoInnerStateAt A.repAlloc mPtr is ∗ A.pool lim st s ∗
        optProtoInnerStateJumpTablePlacedAt ∗ stackAt fsp dropStack96 ∗
        words20At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ∗
        Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ memRegion (fsp + 480#64) 160 ∗
          (mPtr ↦₆₄ (if isTag4 then 0x8000000000000003#64 else 0x8000000000000001#64)) ∗
          words20At (mPtr + 8#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ∗
          memRegion (mPtr + 168#64) 56 ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          optProtoInnerStateJumpTablePlacedAt ∗ stackAt fsp dropStack96 ∗ Frame) ∧
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
  have hfold480 := words20At_entails_memRegion_160 (fsp + 480#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19
  simp only [dropOptProtoInnerStatePlacedSpec] at hDropInner
  cases isTag4 <;> simp only [Bool.false_eq_true, ↓reduceIte] at hpc ⊢
  · wp_steps
    wp_call hDropInner (⟨mPtr, is⟩, st)
    have hevs_w : FreeOnlyEvs w := by assumption
    dsimp only [optProtoInnerStateSize]
    rw [memRegion_224_split_tag24_ok mPtr]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro vd
    apply SepWP.exists_elim; intro v2; apply SepWP.exists_elim; intro v1
    apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v5
    apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v3
    apply SepWP.exists_elim; intro v12; apply SepWP.exists_elim; intro v11
    apply SepWP.exists_elim; intro v10; apply SepWP.exists_elim; intro v9
    apply SepWP.exists_elim; intro v8; apply SepWP.exists_elim; intro v7
    apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v19
    apply SepWP.exists_elim; intro v18; apply SepWP.exists_elim; intro v17
    apply SepWP.exists_elim; intro v16; apply SepWP.exists_elim; intro v15
    apply SepWP.exists_elim; intro v14; apply SepWP.exists_elim; intro v13
    dsimp only [words20At, words13At, words3At, words10At, words7At] at hfold480 ⊢
    refine SepWP.mono (post := fun sm Pm =>
        VmPreserved sf sm ∧
        (Pm ⊢ memRegion (fsp + 480#64) 160 ∗
          (mPtr ↦₆₄ 0x8000000000000001#64) ∗
          words20At (mPtr + 8#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ∗
          memRegion (mPtr + 168#64) 56 ∗
          A.pool lim (M.stepEvents w st) sf ∗
          optProtoInnerStateJumpTablePlacedAt ∗ stackAt fsp dropStack96 ∗ Frame) ∧
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
        sm.readReg64 (Reg.gpr 29#5) = fsp + 720#64)
      ?_ (fun sm _Pm _ _ ⟨hvm, hp, hq⟩ => by
        refine ⟨w, hevs_w, ?_, hq⟩
        rw [A.pool_of_vmPreserved hvm]
        exact hp)
    dsimp only [words20At, words13At, words3At, words10At, words7At]
    by_vm_steps (wp_steps; apply SepWP.fold hfold480 (by sep_focus); wp_done)
  · wp_steps
    wp_call hDropInner (⟨mPtr, is⟩, st)
    have hevs_w : FreeOnlyEvs w := by assumption
    dsimp only [optProtoInnerStateSize]
    rw [memRegion_224_split_tag24_ok mPtr]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro vd
    apply SepWP.exists_elim; intro v2; apply SepWP.exists_elim; intro v1
    apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v5
    apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v3
    apply SepWP.exists_elim; intro v12; apply SepWP.exists_elim; intro v11
    apply SepWP.exists_elim; intro v10; apply SepWP.exists_elim; intro v9
    apply SepWP.exists_elim; intro v8; apply SepWP.exists_elim; intro v7
    apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v19
    apply SepWP.exists_elim; intro v18; apply SepWP.exists_elim; intro v17
    apply SepWP.exists_elim; intro v16; apply SepWP.exists_elim; intro v15
    apply SepWP.exists_elim; intro v14; apply SepWP.exists_elim; intro v13
    dsimp only [words20At, words13At, words3At, words10At, words7At] at hfold480 ⊢
    refine SepWP.mono (post := fun sm Pm =>
        VmPreserved sf sm ∧
        (Pm ⊢ memRegion (fsp + 480#64) 160 ∗
          (mPtr ↦₆₄ 0x8000000000000003#64) ∗
          words20At (mPtr + 8#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ∗
          memRegion (mPtr + 168#64) 56 ∗
          A.pool lim (M.stepEvents w st) sf ∗
          optProtoInnerStateJumpTablePlacedAt ∗ stackAt fsp dropStack96 ∗ Frame) ∧
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
        sm.readReg64 (Reg.gpr 29#5) = fsp + 720#64)
      ?_ (fun sm _Pm _ _ ⟨hvm, hp, hq⟩ => by
        refine ⟨w, hevs_w, ?_, hq⟩
        rw [A.pool_of_vmPreserved hvm]
        exact hp)
    dsimp only [words20At, words13At, words3At, words10At, words7At]
    by_vm_steps (wp_steps; apply SepWP.fold hfold480 (by sep_focus); wp_done)

/-! ## 2. Tag Arm 4 (`Ct1Received`) In-Place, Non-In-Place, Branch, & Top-Level Step (`Placed`) -/

private theorem v1State_tag4_inplace_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hCrCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 303)
      (withLsCodeRoLoaded lsmpl (chunkedCt1ReceivedMergeSpec A lim)))
    {s0 s : State} {x : V1StateMergeGhost} {st0 st : M.σ} {R : SepProp} {m : V1State}
    {cr : V1State.Chunked.Ct1Received} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hm_is : m.innerState = some (.ct1Received cr))
    (hbgt : V1StateTagEntryBudgetPlaced lim H s0 x st m rest iwt limit s)
    (hpc : s.pc = (blkPl_298).base + 476#64)
    (hcont : V1StateTagContPlaced A lim H s0 x st0 st R 4 m rest iwt limit) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergePlacedSpec A lim) (x, st0) R s0) (WppPanicFalse R) := by
  obtain ⟨⟨hsp_align, hrest_le, _hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, hx9, hregs, hinv⟩, hpoly_cap, hFit⟩ := hbgt
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  obtain ⟨honErr, honOk⟩ := hcont
  have hx9_eq : s.readReg64 (Reg.gpr 9#5) = 0x8000000000000003#64 := by
    rw [hm_is] at hx9; exact hx9
  have hbr1 : (s.readReg64 (Reg.gpr 9#5) + 2#64 == 0#64) = false := by rw [hx9_eq]; decide
  have hbr2 : (s.readReg64 (Reg.gpr 9#5) != 0x8000000000000003#64) = false := by rw [hx9_eq]; decide
  have hpe_bound : optPolyEncoderPtsLen cr.sendingEk + rest.length < 2 ^ 56 ∧
      optPolyEncoderPolysLen cr.sendingEk + rest.length < 2 ^ 56 := by
    rw [← optPolyEncoderBound_iff]
    exact ct1Received_polyBound_extract (hm_is ▸ hpoly)
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hsub_cap : ct1ReceivedPolyCapBound ⟨iwt, x.msgPtr + 8#64, cr, x.bufRef, x.slot, restPtr, rest⟩ ≤
      optInnerStatePolyCapBound x.msg.innerState x.bs.length := by
    have hle := ct1ReceivedPolyCapBound_le iwt (x.msgPtr + 8#64) x.bufRef x.slot restPtr rest m.innerState
    rw [hm_is] at hle hpoly_cap
    exact Nat.le_trans hle hpoly_cap
  have hFit_sub : FitsEnv M lim st (ChunkedCt1ReceivedMergeEnv ⟨iwt, x.msgPtr + 8#64, cr, x.bufRef, x.slot, restPtr, rest⟩) :=
    hFit.mono fun _ he => he.mono (by dsimp only; omega) hrest_le hsub_cap
  have hstk : chunkedMergeStack = chunkedInlStack := rfl
  refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 303) hinv ?_
  conv =>
    arg 4
    rw [v1StateLoopPrePlaced, hm_is, optProtoInnerStateCapAt, protoInnerStateCapAt,
      sliceCursorAfter_eq_split hrest_le hrest_suf]
  simp only [sepConj_assoc]
  wp_steps_sync_pool (lsmpl.base 303); wp_reach; intro hinv_c
  refine SepWPp.call_frame_lscro (hinv := hinv_c)
    (x := (⟨iwt, x.msgPtr + 8#64, cr, x.bufRef, x.slot, restPtr, rest⟩, st))
    (ret_pc := (blkPl_298).base + 508#64) hCrCall
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [chunkedCt1ReceivedMergeSpec, chunkedCt1ReceivedMergeSpecOfEnv]
        simp only [arm64_norm, hsp, hx0, hx20, hx19]; rfl)
    (⟨rfl, rfl, rfl, hpe_bound.1, hpe_bound.2, hFit_sub⟩ :
      BitVec.ofNat 8 iwt.toNat = BitVec.ofNat 8 iwt.toNat ∧
        x.msgPtr + 8#64 = x.msgPtr + 8#64 ∧ x.bufRef = x.bufRef ∧
        optPolyEncoderPtsLen cr.sendingEk + rest.length < 2 ^ 56 ∧
        optPolyEncoderPolysLen cr.sendingEk + rest.length < 2 ^ 56 ∧
        FitsEnv M lim st (ChunkedCt1ReceivedMergeEnv ⟨iwt, x.msgPtr + 8#64, cr, x.bufRef, x.slot, restPtr, rest⟩))
    (by dsimp only [restPtr]; rw [hstk]; sep_focus)
    (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
    (fun _ _ => wppPanicFalse_of_false) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, _hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp only [arm64_norm, hsp, hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29] at hpcm hrunm hspm hx19_m hx20_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  have hm_field := v1State_mergeField_tag4 m iwt rest 99
  rw [hm_is] at hm_field; dsimp only at hm_field
  cases hcr_res : (mergeMessage V1State.Chunked.Ct1Received.mergeField (codecWireTypeToProto iwt) cr rest 99).toOption with
  | none =>
    rw [hcr_res, Option.map_none] at hm_field
    apply SepWPp.of_sepWP (mid := (blkPl_298).base + 2700#64)
    conv =>
      arg 4
      simp only [chunkedCt1ReceivedMergeSpec, chunkedCt1ReceivedMergeSpecOfEnv,
        ChunkedCt1ReceivedMergePostEnv, hstk, hcr_res,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, and_assoc, hsp]
    apply SepWP.exists_elim; intro evs_m
    apply SepWP.exists_elim; intro cr'; apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; rintro ⟨htrm, hevs_m, hsm0, hn_err⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    have hfold_is : (x.msgPtr ↦₆₄ 0x8000000000000003#64) ∗
        chunkedCt1ReceivedPBAt A.repAlloc (x.msgPtr + 8#64) cr' ∗ memRegion (x.msgPtr + 168#64) 56 ⊢
        ∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A.repAlloc x.msgPtr is' := by
      rw [chunkedCt1ReceivedPBAt_eq_proto]
      exact optProtoInnerStateAt_entails_exists A.repAlloc x.msgPtr (some (.ct1Received cr'))
    apply SepWP.fold hfold_is (by sep_focus)
    wp_steps_sync_pool ((blkPl_298).base + 2700#64); wp_reach
    apply SepWPp.weaken_pre (P' :=
      decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 0#5)) n_err ∗ stackAt (s0.sp - 816#64) chunkedInlStack ∗
        memRegion (s0.sp - 816#64) 720 ∗
        v1StateErrFramePlaced A lim (M.stepEvents evs_m st) s0 _ x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (Entails.of_eq (by dsimp only [v1StateErrFramePlaced]; ac_rfl))
    exact honErr hm_field evs_m _ (sm.readReg64 (Reg.gpr 0#5)) n_err
      (hevs_m.mono (by omega) hrest_le hsub_cap)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm]) hsm0 hn_err
  | some p =>
    rcases p with ⟨cr', rest'⟩
    rw [hcr_res, Option.map_some] at hm_field
    have hrest'_le : rest'.length ≤ rest.length := proto_mergeMessage_len_le hcr_res
    have hpoly' : OptInnerStatePolyBound rest'.length (some (.ct1Received cr')) :=
      innerStatePolyBound_of_ct1Received (by rw [← optPolyEncoderBound_iff] at hpe_bound; exact hpe_bound) hcr_res
    have hcap' : optInnerStatePolyCapBound (some (.ct1Received cr')) rest'.length ≤
        optInnerStatePolyCapBound x.msg.innerState x.bs.length :=
      Nat.le_trans (optInnerStatePolyCapBound_of_ct1Received hcr_res) hsub_cap
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 2700#64) hinv_m ?_
    conv =>
      arg 4
      simp only [chunkedCt1ReceivedMergeSpec, chunkedCt1ReceivedMergeSpecOfEnv,
        ChunkedCt1ReceivedMergePostEnv, hstk, hcr_res,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, and_assoc, hsp]
    apply SepWP.exists_elim; intro evs_m
    apply SepWP.pure_elim; rintro ⟨htrm, hevs_m, hsm0⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    wp_steps_sync_pool ((blkPl_298).base + 2700#64); wp_reach; intro hinv_n
    apply SepWPp.weaken_pre (P' :=
      v1StateLoopPrePlaced A lim (M.stepEvents evs_m st) s0 _ x.msgPtr x.bufRef x.slot x.ptr
        { m with innerState := some (.ct1Received cr') } x.bs rest')
      (Entails.of_eq (by dsimp only [v1StateLoopPrePlaced, optProtoInnerStateCapAt, protoInnerStateCapAt]; ac_rfl))
    exact honOk evs_m { m with innerState := some (.ct1Received cr') } rest' _
      hm_field hpoly' hcap' hrest'_le
      (hevs_m.mono (by omega) hrest_le hsub_cap)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hsm0])
      ⟨by simp only [arm64_norm, hx19_m], by simp only [arm64_norm, hx20_m],
       by simp only [arm64_norm, hx22_m], by simp only [arm64_norm, hx23_m],
       by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m],
       by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
       by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hfp_m]⟩ hinv_n

private theorem v1State_tag4_at_1140_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hCrCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 303) (withLsCodeRoLoaded lsmpl (chunkedCt1ReceivedMergeSpec A lim)))
    (hDropCr : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 282) (dropProtoChunkedCt1ReceivedSpec M A lim))
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267) (dropOptProtoInnerStatePlacedSpec M A lim))
    {s0 s : State} {x : V1StateMergeGhost} {st0 st : M.σ} {R : SepProp} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hm_not : ∀ cr, m.innerState ≠ some (.ct1Received cr))
    (hbgt : V1StateTagEntryBudgetPlaced lim H s0 x st m rest iwt limit s)
    (hpc : s.pc = (blkPl_298).base + 1140#64)
    (hcont : V1StateTagContPlaced A lim H s0 x st0 st R 4 m rest iwt limit) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergePlacedSpec A lim) (x, st0) R s0) (WppPanicFalse R) := by
  obtain ⟨⟨hsp_align, hrest_le, _hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, _hx9, hregs, hinv⟩, hpoly_cap, hFit⟩ := hbgt
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  let fsp : BitVec 64 := s0.sp - 816#64
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := by dsimp only [fsp]; simpa only [arm64_norm] using hsp_align
  have hfsp720 : fsp + 720#64 = s0.sp - 96#64 := by dsimp only [fsp]; bv_lin
  have h56 : rest.length < 2 ^ 56 := optInnerStatePolyBound_lt_2_56 hpoly
  have hdef_pts : optPolyEncoderPtsLen (default : V1State.Chunked.Ct1Received).sendingEk + rest.length < 2 ^ 56 := by
    change 0 + rest.length < 2 ^ 56; omega
  have hdef_polys : optPolyEncoderPolysLen (default : V1State.Chunked.Ct1Received).sendingEk + rest.length < 2 ^ 56 := by
    change 0 + rest.length < 2 ^ 56; omega
  have hsub_cap : ct1ReceivedPolyCapBound ⟨iwt, fsp + 16#64, default, x.bufRef, x.slot, restPtr, rest⟩ ≤
      optInnerStatePolyCapBound x.msg.innerState x.bs.length := by
    have hle : ct1ReceivedPolyCapBound ⟨iwt, fsp + 16#64, default, x.bufRef, x.slot, restPtr, rest⟩ ≤ 0 + rest.length :=
      ct1ReceivedPolyCapBound_le iwt (fsp + 16#64) x.bufRef x.slot restPtr rest none
    have hge := LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1BudgetAux.optInnerStatePolyCapBound_ge_len
      m.innerState rest.length
    omega
  have hFit_sub : FitsEnv M lim st (ChunkedCt1ReceivedMergeEnv ⟨iwt, fsp + 16#64, default, x.bufRef, x.slot, restPtr, rest⟩) :=
    hFit.mono fun _ he => he.mono (by dsimp only; omega) hrest_le hsub_cap
  have hstk : chunkedMergeStack = chunkedInlStack := rfl
  refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 303) hinv ?_
  conv =>
    arg 4
    rw [v1StateLoopPrePlaced, show s0.sp - 816#64 = fsp from rfl,
      memRegion_split_tag24_temp fsp, memRegion_160_split_tag24_init fsp,
      sliceCursorAfter_eq_split hrest_le hrest_suf]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w_sp400; apply SepWP.exists_elim; intro w_sp120; apply SepWP.exists_elim; intro w_sp16
  refine SepWP.weaken_pre (P' :=
    ((fsp + 16#64) ↦₆₄ w_sp16) ∗ memRegion (fsp + 24#64) 96 ∗
      ((fsp + 120#64) ↦₆₄ w_sp120) ∗ memRegion (fsp + 128#64) 48 ∗
      (stackAt fsp chunkedInlStack ∗ memRegion fsp 16 ∗ memRegion (fsp + 176#64) 64 ∗
        memRegion (fsp + 240#64) 160 ∗ ((fsp + 400#64) ↦₆₄ w_sp400) ∗
        memRegion (fsp + 408#64) 72 ∗ memRegion (fsp + 480#64) 160 ∗
        memRegion (fsp + 640#64) 80 ∗ v1StateJumpTablesPlacedAt ∗
        optProtoInnerStateCapAt A.repAlloc x.msgPtr rest.length m.innerState ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot restPtr rest ∗
        (x.ptr ↦ₛ x.bs.take (x.bs.length - rest.length)) ∗ A.pool lim st s ∗ v1StateSavedRegsAt s0.sp s0))
    (Entails.of_eq (by dsimp only [restPtr]; ac_rfl)) ?_
  refine SepWP.mono (v1State_tag24_setup_placed true (A := A.repAlloc) (restLen := rest.length) hfsp_align hpc hrun hsp hx23) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hvm1, hP1, hsp1, htr1, hx0_1, hx1_1, hx2_1, hlr1,
    hx19_1, hx20_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1⟩ hinv_c
  rw [hsp] at hsp1; rw [hx19] at hx2_1 hx19_1; rw [hx20] at hx20_1
  rw [hx22] at hx22_1; rw [hx24] at hx24_1; rw [hx25] at hx25_1
  rw [hx26] at hx26_1; rw [hx27] at hx27_1; rw [hx28] at hx28_1; rw [hx29] at hx29_1
  have hx0_1' : (s1.readReg64 (Reg.gpr 0#5)).setWidth 8 = BitVec.ofNat 8 iwt.toNat := by rw [hx0_1, hx0]
  have hdef_cr : optUnchunked4CapAt A.repAlloc (fsp + 16#64) rest.length none ∗
      optPolynomialEncoderPBAt A.repAlloc ((fsp + 16#64) + 104#64) none =
      chunkedCt1ReceivedPBCapAt A.repAlloc (fsp + 16#64) rest.length default := by
    dsimp only [chunkedCt1ReceivedPBCapAt, default, Inhabited.default]
    rw [optUnchunkedEkSentCt1ReceivedPBCapAt_eq_optUnchunked4]; rfl
  rw [← sepConj_assoc, hdef_cr] at hP1
  apply SepWPp.weaken_pre hP1
  conv => arg 4; rw [← A.pool_of_vmPreserved hvm1]
  refine SepWPp.call_frame_lscro (hinv := hinv_c)
    (x := (⟨iwt, fsp + 16#64, default, x.bufRef, x.slot, restPtr, rest⟩, st))
    (ret_pc := (blkPl_298).base + 1160#64) hCrCall
    hpc1 hrun1 (by simp only [State.spAligned, hsp1]; exact hfsp_align) hlr1
    rfl
    ⟨hx0_1', hx1_1, hx2_1, hdef_pts, hdef_polys, hFit_sub⟩
    (by simp only [hsp1, hstk]; sep_focus)
    (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
    (fun _ _ => wppPanicFalse_of_false) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, _hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  rw [hsp1] at hspm
  rw [hx19_1] at hx19_m; rw [hx20_1] at hx20_m; rw [hx22_1] at hx22_m; rw [hx23_1] at hx23_m
  rw [hx24_1] at hx24_m; rw [hx25_1] at hx25_m; rw [hx26_1] at hx26_m; rw [hx27_1] at hx27_m
  rw [hx28_1] at hx28_m; rw [hx29_1] at hfp_m
  have hm_field : (V1State.mergeField m (BitVec.ofNat 32 4) (codecWireTypeToProto iwt) rest 99).toOption =
      (mergeMessage V1State.Chunked.Ct1Received.mergeField (codecWireTypeToProto iwt) default rest 99).toOption.map
        (fun (v', rest') => ({ m with innerState := some (.ct1Received v') }, rest')) := by
    rw [v1State_mergeField_tag4]
    rcases h : m.innerState with _ | st_is
    · rfl
    · cases st_is with
      | ct1Received cr => exact absurd h (hm_not cr)
      | _ => rfl
  cases hcr_res : (mergeMessage V1State.Chunked.Ct1Received.mergeField (codecWireTypeToProto iwt) default rest 99).toOption with
  | none =>
    rw [hcr_res, Option.map_none] at hm_field
    apply SepWPp.of_sepWP (mid := (blkPl_298).base + 2700#64)
    conv =>
      arg 4
      simp only [chunkedCt1ReceivedMergeSpec, chunkedCt1ReceivedMergeSpecOfEnv,
        ChunkedCt1ReceivedMergePostEnv, hstk, hcr_res,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, and_assoc, hsp1]
    apply SepWP.exists_elim; intro evs_m
    apply SepWP.exists_elim; intro cr'; apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; rintro ⟨htrm, hevs_m, hsm0, hn_err⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    have hcr_words : chunkedCt1ReceivedPBAt A.repAlloc (fsp + 16#64) cr' ⊢
        ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64,
        ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64, ∃∗ w8 : BitVec 64,
        ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w11 : BitVec 64, ∃∗ w12 : BitVec 64,
        ∃∗ w13 : BitVec 64, ∃∗ w14 : BitVec 64, ∃∗ w15 : BitVec 64, ∃∗ w16 : BitVec 64,
        ∃∗ w17 : BitVec 64, ∃∗ w18 : BitVec 64, ∃∗ w19 : BitVec 64,
          words20At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ∗
          tag24CapHeap A.repAlloc 0 (cr'.uc.map fun u => (u.epoch, u.auth, u.dk, u.ct1)) cr'.sendingEk
            w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 := by
      refine Entails.trans (chunkedCt1ReceivedPBAt_entails_cap_zero A.repAlloc (fsp + 16#64) cr') ?_
      dsimp only [chunkedCt1ReceivedPBCapAt]
      rw [optUnchunkedEkSentCt1ReceivedPBCapAt_eq_optUnchunked4]
      exact tag24_extract_words A.repAlloc (fsp + 16#64) 0 (cr'.uc.map fun u => (u.epoch, u.auth, u.dk, u.ct1)) cr'.sendingEk
    apply SepWP.fold hcr_words (by sep_focus)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1
    apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
    apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5
    apply SepWP.exists_elim; intro w6; apply SepWP.exists_elim; intro w7
    apply SepWP.exists_elim; intro w8; apply SepWP.exists_elim; intro w9
    apply SepWP.exists_elim; intro w10; apply SepWP.exists_elim; intro w11
    apply SepWP.exists_elim; intro w12; apply SepWP.exists_elim; intro w13
    apply SepWP.exists_elim; intro w14; apply SepWP.exists_elim; intro w15
    apply SepWP.exists_elim; intro w16; apply SepWP.exists_elim; intro w17
    apply SepWP.exists_elim; intro w18; apply SepWP.exists_elim; intro w19
    apply SepWP.fold (Entails.trans (optProtoInnerStateCapAt_entails_pb A.repAlloc x.msgPtr rest.length m.innerState)
      (optProtoInnerStateAt_entails_exists A.repAlloc x.msgPtr m.innerState)) (by sep_focus)
    rw [v1StateBelow_dropStack48 (s0.sp - 816#64)]
    let Frame_err : SepProp :=
      tag24CapHeap A.repAlloc 0 (cr'.uc.map fun u => (u.epoch, u.auth, u.dk, u.ct1)) cr'.sendingEk
        w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ∗
      A.pool lim (M.stepEvents evs_m st) sm ∗ stackAt fsp dropStack48 ∗
      decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
      v1StateBelowRest fsp dropStack48 ∗
      memRegion fsp 16 ∗ memRegion (fsp + 176#64) 64 ∗
      memRegion (fsp + 408#64) 72 ∗ memRegion (fsp + 480#64) 160 ∗
      memRegion (fsp + 640#64) 80 ∗ v1StateJumpTablesPlacedAt ∗
      (∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A.repAlloc x.msgPtr is') ∗
      (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗
      (x.ptr ↦ₛ x.bs) ∗ v1StateSavedRegsAt s0.sp s0
    refine SepWP.weaken_pre (P' :=
      words20At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ∗
        memRegion (fsp + 240#64) 160 ∗ ((fsp + 400#64) ↦₆₄ w_sp400) ∗ Frame_err)
      (Entails.of_eq (by dsimp only [Frame_err, fsp]; ac_rfl)) ?_
    refine SepWP.seq (v1State_tag24_copy_err_placed true hfsp_align hpcm hrunm hspm hsm0 hx20_m) ?_
    rintro s2 P2 hpc2 hrun2 ⟨hvm2, hP2, hsp2, htr2, hx21_2⟩
    apply SepWP.weaken_pre hP2
    dsimp only [Frame_err]
    conv => arg 4; rw [← A.pool_of_vmPreserved hvm2]
    apply SepWP.fold (tag24_words_entails_protoChunkedCt1Received A.repAlloc (fsp + 240#64)
      (cr'.uc.map fun u => (u.epoch, u.auth, u.dk, u.ct1)) cr'.sendingEk
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19) (by sep_focus)
    refine SepWP.weaken_pre (P' :=
      protoChunkedCt1ReceivedAt A.repAlloc (fsp + 240#64)
        { uc := (cr'.uc.map fun u => (u.epoch, u.auth, u.dk, u.ct1)).map
            (fun (epoch, auth, v3, v4) => { dk := v3, ct1 := v4, auth := auth, epoch := epoch }),
          sendingEk := cr'.sendingEk } ∗
        A.pool lim (M.stepEvents evs_m st) s2 ∗ stackAt fsp dropStack48 ∗
        (memRegion (fsp + 16#64) 160 ∗ ((fsp + 400#64) ↦₆₄ x.msgPtr) ∗
          decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
          v1StateBelowRest fsp dropStack48 ∗
          memRegion fsp 16 ∗ memRegion (fsp + 176#64) 64 ∗
          memRegion (fsp + 408#64) 72 ∗ memRegion (fsp + 480#64) 160 ∗
          memRegion (fsp + 640#64) 80 ∗ v1StateJumpTablesPlacedAt ∗
          (∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A.repAlloc x.msgPtr is') ∗
          (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗
          (x.ptr ↦ₛ x.bs) ∗ v1StateSavedRegsAt s0.sp s0))
      (Entails.of_eq (by ac_rfl)) ?_
    refine SepWP.seq (v1State_tag24_err_1640_placed hDropCr hfsp_align hpc2 hrun2 (hsp2.trans hspm)) ?_
    rintro s3 P3 hpc3 hrun3 ⟨evs_d, hevs_d, hP3, hsp3, htr3, hx21_3⟩
    rw [← LibsignalBinary.Heap.AllocCostModel.stepEvents_append] at hP3
    apply SepWP.weaken_pre hP3
    apply SepWP.fold (v1StateBelow_dropStack48_entails fsp) (by sep_focus)
    apply SepWP.fold (memRegion_fold_tag24_temp fsp x.msgPtr) (by sep_focus)
    refine SepWP.done hpc3 hrun3 ?_
    apply SepWPp.weaken_pre (P' :=
      decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 0#5)) n_err ∗ stackAt (s0.sp - 816#64) chunkedInlStack ∗
        memRegion (s0.sp - 816#64) 720 ∗
        v1StateErrFramePlaced A lim (M.stepEvents (evs_m ++ evs_d) st) s0 s3 x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (Entails.of_eq (by dsimp only [v1StateErrFramePlaced, fsp]; ac_rfl))
    exact hcont.onErr hm_field (evs_m ++ evs_d) s3 (sm.readReg64 (Reg.gpr 0#5)) n_err
      (((hevs_m.mono (Nat.le_refl _) hrest_le hsub_cap).append
        (SpqrMergeLoopEnv.single (fuel := 0) (.deallocs hevs_d))).mono_fuel (by omega))
      hpc3 hrun3 (hsp3.trans (hsp2.trans hspm))
      (htr3.trans (htr2.trans (htrm.trans (htr1.trans htr))))
      (hx21_3.trans hx21_2) hsm0 hn_err
  | some p =>
    rcases p with ⟨cr', rest'⟩
    rw [hcr_res, Option.map_some] at hm_field
    have hrest'_le : rest'.length ≤ rest.length := proto_mergeMessage_len_le hcr_res
    have hpoly' : OptInnerStatePolyBound rest'.length (some (.ct1Received cr')) :=
      innerStatePolyBound_of_ct1Received (bs := rest) (m := default) (optPolyEncoderBound_none h56) hcr_res
    have hcap' : optInnerStatePolyCapBound (some (.ct1Received cr')) rest'.length ≤
        optInnerStatePolyCapBound x.msg.innerState x.bs.length :=
      Nat.le_trans (optInnerStatePolyCapBound_of_ct1Received hcr_res) hsub_cap
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 2700#64) hinv_m ?_
    conv =>
      arg 4
      simp only [chunkedCt1ReceivedMergeSpec, chunkedCt1ReceivedMergeSpecOfEnv,
        ChunkedCt1ReceivedMergePostEnv, hstk, hcr_res,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, and_assoc, hsp1]
    apply SepWP.exists_elim; intro evs_m
    apply SepWP.pure_elim; rintro ⟨htrm, hevs_m, hsm0⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (optProtoInnerStateCapAt_entails_pb A.repAlloc x.msgPtr rest.length m.innerState) (by sep_focus)
    have hcr_words : chunkedCt1ReceivedPBCapAt A.repAlloc (fsp + 16#64) rest'.length cr' ⊢
        ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64,
        ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64, ∃∗ w8 : BitVec 64,
        ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w11 : BitVec 64, ∃∗ w12 : BitVec 64,
        ∃∗ w13 : BitVec 64, ∃∗ w14 : BitVec 64, ∃∗ w15 : BitVec 64, ∃∗ w16 : BitVec 64,
        ∃∗ w17 : BitVec 64, ∃∗ w18 : BitVec 64, ∃∗ w19 : BitVec 64,
          words20At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ∗
          tag24CapHeap A.repAlloc rest'.length (cr'.uc.map fun u => (u.epoch, u.auth, u.dk, u.ct1)) cr'.sendingEk
            w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 := by
      dsimp only [chunkedCt1ReceivedPBCapAt]
      rw [optUnchunkedEkSentCt1ReceivedPBCapAt_eq_optUnchunked4]
      exact tag24_extract_words A.repAlloc (fsp + 16#64) rest'.length (cr'.uc.map fun u => (u.epoch, u.auth, u.dk, u.ct1)) cr'.sendingEk
    apply SepWP.fold hcr_words (by sep_focus)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1
    apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
    apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5
    apply SepWP.exists_elim; intro w6; apply SepWP.exists_elim; intro w7
    apply SepWP.exists_elim; intro w8; apply SepWP.exists_elim; intro w9
    apply SepWP.exists_elim; intro w10; apply SepWP.exists_elim; intro w11
    apply SepWP.exists_elim; intro w12; apply SepWP.exists_elim; intro w13
    apply SepWP.exists_elim; intro w14; apply SepWP.exists_elim; intro w15
    apply SepWP.exists_elim; intro w16; apply SepWP.exists_elim; intro w17
    apply SepWP.exists_elim; intro w18; apply SepWP.exists_elim; intro w19
    rw [v1StateBelow_dropStack96 (s0.sp - 816#64)]
    rw [← hfsp720] at hfp_m
    let Frame_ok : SepProp :=
      tag24CapHeap A.repAlloc rest'.length (cr'.uc.map fun u => (u.epoch, u.auth, u.dk, u.ct1)) cr'.sendingEk
        w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ∗
      optProtoInnerStateAt A.repAlloc x.msgPtr m.innerState ∗ A.pool lim (M.stepEvents evs_m st) sm ∗
      optProtoInnerStateJumpTablePlacedAt ∗ stackAt fsp dropStack96 ∗
      v1StateBelowRest fsp dropStack96 ∗
      memRegion fsp 16 ∗ memRegion (fsp + 176#64) 64 ∗
      memRegion (fsp + 408#64) 72 ∗ memRegion (fsp + 640#64) 80 ∗
      v1StateMergeJumpTablePlacedExpanded ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest' ∗
      v1StateSavedRegsAt s0.sp s0
    refine SepWP.weaken_pre (P' :=
      words20At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ∗
        memRegion (fsp + 240#64) 160 ∗ ((fsp + 400#64) ↦₆₄ w_sp400) ∗
        (memRegion (fsp + 480#64) 160 ∗ Frame_ok))
      (Entails.of_eq (by dsimp only [Frame_ok, v1StateJumpTablesPlacedAt, fsp]; ac_rfl)) ?_
    refine SepWP.seq (v1State_tag24_copy_ok_placed true hfsp_align hpcm hrunm hspm hsm0 hx20_m) ?_
    rintro s2 P2 hpc2 hrun2 ⟨hvm2, hP2, hsp2, htr2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2⟩
    refine SepWP.weaken_pre (Entails.trans hP2 (Entails.of_eq (by ac_rfl :
      words20At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ∗
        memRegion (fsp + 240#64) 160 ∗ ((fsp + 400#64) ↦₆₄ x.msgPtr) ∗
        (memRegion (fsp + 480#64) 160 ∗ Frame_ok) =
      words20At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ∗
        memRegion (fsp + 480#64) 160 ∗
        (memRegion (fsp + 240#64) 160 ∗ ((fsp + 400#64) ↦₆₄ x.msgPtr) ∗ Frame_ok)))) ?_
    refine SepWP.seq (v1State_tag24_pre_drop_placed true hfsp_align hpc2 hrun2 (hsp2.trans hspm) hx20_2 (hx29_2.trans hfp_m)) ?_
    rintro s3 P3 hpc3 hrun3 ⟨hvm3, hP3, hsp3, htr3, hx0_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3⟩
    apply SepWP.weaken_pre hP3
    dsimp only [Frame_ok]
    conv => arg 4; rw [← A.pool_of_vmPreserved (hvm2.trans hvm3)]
    refine SepWP.weaken_pre (P' :=
      optProtoInnerStateAt A.repAlloc x.msgPtr m.innerState ∗ A.pool lim (M.stepEvents evs_m st) s3 ∗ optProtoInnerStateJumpTablePlacedAt ∗
        stackAt fsp dropStack96 ∗
        words20At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ∗
        (memRegion (fsp + 16#64) 160 ∗ memRegion (fsp + 240#64) 160 ∗ ((fsp + 400#64) ↦₆₄ x.msgPtr) ∗
          tag24CapHeap A.repAlloc rest'.length (cr'.uc.map fun u => (u.epoch, u.auth, u.dk, u.ct1)) cr'.sendingEk
            w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ∗
          v1StateBelowRest fsp dropStack96 ∗
          memRegion fsp 16 ∗ memRegion (fsp + 176#64) 64 ∗
          memRegion (fsp + 408#64) 72 ∗ memRegion (fsp + 640#64) 80 ∗
          v1StateMergeJumpTablePlacedExpanded ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest' ∗
          v1StateSavedRegsAt s0.sp s0))
      (Entails.of_eq (by ac_rfl)) ?_
    refine SepWP.seq (v1State_tag24_post_drop_placed true hDropInner hfsp_align hpc3 hrun3
      (hsp3.trans (hsp2.trans hspm)) hx0_3 hx20_3 hx29_3) ?_
    rintro s4 P4 hpc4 hrun4 ⟨evs_d, hevs_d, hP4, hsp4, htr4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4⟩
    rw [← LibsignalBinary.Heap.AllocCostModel.stepEvents_append] at hP4
    apply SepWP.weaken_pre hP4
    simp only [↓reduceIte]
    apply SepWP.fold (v1StateBelow_dropStack96_entails fsp) (by sep_focus)
    apply SepWP.fold (memRegion_fold_tag24_temp fsp x.msgPtr) (by sep_focus)
    apply SepWP.fold (tag4_reconstruct_innerState A.repAlloc x.msgPtr rest'.length cr'
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19) (by sep_focus)
    refine SepWP.done hpc4 hrun4 (fun hinv4 => ?_)
    apply SepWPp.weaken_pre (P' :=
      v1StateLoopPrePlaced A lim (M.stepEvents (evs_m ++ evs_d) st) s0 s4 x.msgPtr x.bufRef x.slot x.ptr
        { m with innerState := some (.ct1Received cr') } x.bs rest')
      (Entails.of_eq (by dsimp only [v1StateLoopPrePlaced, v1StateJumpTablesPlacedAt, fsp]; ac_rfl))
    exact hcont.onOk (evs_m ++ evs_d) { m with innerState := some (.ct1Received cr') } rest' s4 hm_field hpoly' hcap' hrest'_le
      (((hevs_m.mono (Nat.le_refl _) hrest_le hsub_cap).append
        (SpqrMergeLoopEnv.single (fuel := 0) (.deallocs hevs_d))).mono_fuel (by omega))
      hpc4 hrun4 (hsp4.trans (hsp3.trans (hsp2.trans hspm)))
      (htr4.trans (htr3.trans (htr2.trans (htrm.trans (htr1.trans htr)))))
      (hx21_4.trans (hx21_3.trans hx21_2))
      ⟨hx19_4.trans (hx19_3.trans (hx19_2.trans hx19_m)), hx20_4,
       hx22_4.trans (hx22_3.trans (hx22_2.trans hx22_m)), hx23_4.trans (hx23_3.trans (hx23_2.trans hx23_m)),
       hx24_4.trans (hx24_3.trans (hx24_2.trans hx24_m)), hx25_4.trans (hx25_3.trans (hx25_2.trans hx25_m)),
       hx26_4.trans (hx26_3.trans (hx26_2.trans hx26_m)), hx27_4.trans (hx27_3.trans (hx27_2.trans hx27_m)),
       hx28_4.trans (hx28_3.trans (hx28_2.trans hx28_m)), hx29_4.trans hfsp720⟩ hinv4

private theorem v1State_tag4_branch_1140_placed [LibsignalPlacement] {M : AllocCostModel}
    {lim : BudgetLimits} {H : String → Option (State → State)}
    {s0 s : State} {x : V1StateMergeGhost} {st : M.σ} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    {P : State → SepProp} {post panic : State → SepProp → Prop}
    (hpool : ∀ s', VmPreserved s s' → P s = P s')
    (hm_not : ∀ cr, m.innerState ≠ some (.ct1Received cr))
    (hbgt : V1StateTagEntryBudgetPlaced lim H s0 x st m rest iwt limit s)
    (hpc : s.pc = (blkPl_298).base + 476#64)
    (hcont : ∀ s' : State, V1StateTagEntryBudgetPlaced lim H s0 x st m rest iwt limit s' →
      s'.pc = (blkPl_298).base + 1140#64 →
      SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s' (P s') post panic) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s (P s) post panic := by
  obtain ⟨⟨hsp_align, hrest_le, hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, hx9, hregs, hinv⟩, hpoly_cap, hFit⟩ := hbgt
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 1140#64) hinv ?_
  cases hm_is : m.innerState with
  | none =>
    have hx9_n : InnerStateDiscrFull rest.length none (s.readReg64 (Reg.gpr 9#5)) := hm_is ▸ hx9
    have hbr1 : (s.readReg64 (Reg.gpr 9#5) + 2#64 == 0#64) = true := (discrFull_none_add2 hx9_n).1
    wp_steps; wp_reach; intro hinv'
    refine sepWPp_congr_state_pre (hpool _ ⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, fun _ _ _ => rfl⟩) ?_
    exact hcont _
      ⟨⟨hsp_align, hrest_le, hrest_lt, hrest_suf, hpoly,
        by simp only [arm64_norm, hrun], by simp only [arm64_norm, hsp],
        by simp only [arm64_norm, htr], by simp only [arm64_norm]; exact hx0,
        by simp only [arm64_norm]; exact hx9,
        ⟨by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20],
         by simp only [arm64_norm, hx22], by simp only [arm64_norm, hx23],
         by simp only [arm64_norm, hx24], by simp only [arm64_norm, hx25],
         by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27],
         by simp only [arm64_norm, hx28], by simp only [arm64_norm, hx29]⟩, hinv'⟩,
       hpoly_cap, hFit⟩
      (by simp only [arm64_norm])
  | some is =>
    have hne : ∀ cr, is ≠ .ct1Received cr := fun cr h => hm_not cr (by rw [hm_is, h])
    have hx9_s : InnerStateDiscrFull rest.length (some is) (s.readReg64 (Reg.gpr 9#5)) := hm_is ▸ hx9
    have hbr1 : (s.readReg64 (Reg.gpr 9#5) + 2#64 == 0#64) = false := (discrFull_some_add2 hx9_s).1
    have hbr2 : (s.readReg64 (Reg.gpr 9#5) != 0x8000000000000003#64) = true :=
      discrFull_other_tag4 hne hx9_s
    wp_steps; wp_reach; intro hinv'
    refine sepWPp_congr_state_pre (hpool _ ⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, fun _ _ _ => rfl⟩) ?_
    exact hcont _
      ⟨⟨hsp_align, hrest_le, hrest_lt, hrest_suf, hpoly,
        by simp only [arm64_norm, hrun], by simp only [arm64_norm, hsp],
        by simp only [arm64_norm, htr], by simp only [arm64_norm]; exact hx0,
        by simp only [arm64_norm]; exact hx9,
        ⟨by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20],
         by simp only [arm64_norm, hx22], by simp only [arm64_norm, hx23],
         by simp only [arm64_norm, hx24], by simp only [arm64_norm, hx25],
         by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27],
         by simp only [arm64_norm, hx28], by simp only [arm64_norm, hx29]⟩, hinv'⟩,
       hpoly_cap, hFit⟩
      (by simp only [arm64_norm])

theorem v1State_tag4_step_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hCrCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 303) (withLsCodeRoLoaded lsmpl (chunkedCt1ReceivedMergeSpec A lim)))
    (hDropCr : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 282) (dropProtoChunkedCt1ReceivedSpec M A lim))
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267) (dropOptProtoInnerStatePlacedSpec M A lim)) :
    V1StateTagStepHypPlaced A lim H 4 476#64 := by
  intro s0 s x st0 st R m rest iwt limit hbgt hpc hcont
  by_cases hex : ∃ cr, m.innerState = some (.ct1Received cr)
  · rcases hex with ⟨cr, hm_is⟩
    exact v1State_tag4_inplace_placed hCrCall hm_is hbgt hpc hcont
  · have hm_not : ∀ cr, m.innerState ≠ some (.ct1Received cr) := fun cr h => hex ⟨cr, h⟩
    refine v1State_tag4_branch_1140_placed (lim := lim)
      (P := fun s_cur => v1StateLoopPrePlaced A lim st s0 s_cur x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (fun s' hvm => by dsimp only [v1StateLoopPrePlaced]; rw [A.pool_of_vmPreserved hvm])
      hm_not hbgt hpc fun s' hbgt' hpc' => ?_
    exact v1State_tag4_at_1140_placed hCrCall hDropCr hDropInner hm_not hbgt' hpc' hcont

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag24Budget

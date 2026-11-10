/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1ClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag24
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Code-Loaded Shared 20-Word Drop Helpers and Tag Arm 4 (`Ct1Received`) for `V1State::merge`

Verifies shared 20-word (`160` B) error/post-drop helpers (`isTag4`) and tag arm 4 (`Ct1Received`,
entry `+476`) under `[LibsignalPlacement]` (Block `298`) with `withLsCl`-wrapped cross-block drops
(`282`, `267`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Prost.MessageMerge

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen hiding vecU8Buf vecU8At_eq_header_sep_buf
open CryptoVerification.SpqrV1.Auth hiding bv64_sub_zero bv64_add_zero
open CryptoVerification.SpqrV1.Prost.BytesMerge
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.LibsignalSpqrV1 hiding decodeVarint encodeVarint WireType
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2

attribute [local irreducible] v1StateMergeJumpTablePlacedExpanded optProtoInnerStateJumpTablePlacedAt

theorem v1State_tag24_err_1640_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDropCr : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 282)
      (withLsCl lsmpl (dropProtoChunkedCt1ReceivedSpec A)))
    {s : State} {fsp : BitVec 64} {cr : V1State.Chunked.Ct1Received} {Frame : SepProp}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1640#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2700#64) s
      (protoChunkedCt1ReceivedAt A (fsp + 240#64) cr ∗
        A.pool ∗ stackAt fsp dropStack48 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 240#64) 160 ∗ A.pool ∗ stackAt fsp dropStack48 ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) := by
  simp only [withLsCl, dropProtoChunkedCt1ReceivedSpec] at hDropCr
  wp_steps_lscl (lsmpl.base 282)
  wp_apply
  dsimp only [protoChunkedCt1ReceivedSize]
  wp_steps; wp_done

theorem v1State_tag24_post_drop_cl_placed (isTag4 : Bool) [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267)
      (withLsCl lsmpl (dropOptProtoInnerStatePlacedSpec A)))
    {s : State} {fsp mPtr w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : BitVec 64}
    {is : Option V1State.InnerState} {Frame : SepProp}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base +
      (if isTag4 then 1256#64 else 2756#64))
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = mPtr)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = fsp + 720#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2700#64) s
      (optProtoInnerStateAt A mPtr is ∗ A.pool ∗ optProtoInnerStateJumpTablePlacedAt ∗
        stackAt fsp dropStack96 ∗
        words20At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 480#64) 160 ∗
          (mPtr ↦₆₄ (if isTag4 then 0x8000000000000003#64 else 0x8000000000000001#64)) ∗
          words20At (mPtr + 8#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ∗
          memRegion (mPtr + 168#64) 56 ∗
          A.pool ∗ optProtoInnerStateJumpTablePlacedAt ∗ stackAt fsp dropStack96 ∗ Frame) ∧
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
  simp only [withLsCl, dropOptProtoInnerStatePlacedSpec] at hDropInner
  cases isTag4 <;> simp only [Bool.false_eq_true, ↓reduceIte] at hpc ⊢
  · wp_steps_lscl (lsmpl.base 267)
    wp_apply
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
    wp_steps
    apply SepWP.fold hfold480 (by sep_focus)
    wp_done
  · wp_steps_lscl (lsmpl.base 267)
    wp_apply
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
    wp_steps
    apply SepWP.fold hfold480 (by sep_focus)
    wp_done

theorem v1State_tag4_inplace_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hCrCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 303)
      (withLsCodeRoLoaded lsmpl (chunkedCt1ReceivedMergeSpec A)))
    {s0 s : State} {x : V1StateMergeGhost} {R : SepProp} {m : V1State}
    {cr : V1State.Chunked.Ct1Received} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hm_is : m.innerState = some (.ct1Received cr))
    (hentry : V1StateTagEntryHypPlaced H s0 x m rest iwt limit s)
    (hpc : s.pc = (blkPl_298).base + 476#64)
    (hcont : V1StateTagContClPlaced A H s0 x R 4 m rest iwt limit) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergePlacedSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hsp_align, hrest_le, hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, hx9, hregs, hinv⟩ := hentry
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  obtain ⟨honErr, honOk⟩ := hcont
  have hx9_eq : s.readReg64 (Reg.gpr 9#5) = 0x8000000000000003#64 := by
    rw [hm_is] at hx9; exact hx9
  have hbr1 : (s.readReg64 (Reg.gpr 9#5) + 2#64 == 0#64) = false := by
    rw [hx9_eq]; decide
  have hbr2 : (s.readReg64 (Reg.gpr 9#5) != 0x8000000000000003#64) = false := by
    rw [hx9_eq]; decide
  have hpe_bound : optPolyEncoderPtsLen cr.sendingEk + rest.length < 2 ^ 56 ∧
      optPolyEncoderPolysLen cr.sendingEk + rest.length < 2 ^ 56 := by
    rw [← optPolyEncoderBound_iff]
    exact ct1Received_polyBound_extract (hm_is ▸ hpoly)
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 303) hinv ?_
  conv =>
    arg 4
    rw [v1StateLoopPrePlaced, hm_is, optProtoInnerStateCapAt, protoInnerStateCapAt,
      sliceCursorAfter_eq_split hrest_le hrest_suf]
  wp_steps; wp_reach; intro hinv_c
  have hstk : chunkedMergeStack = chunkedInlStack := rfl
  refine SepWPp.call_frame_lscro (hinv := hinv_c)
    (x := ⟨iwt, x.msgPtr + 8#64, cr, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := (blkPl_298).base + 508#64) hCrCall
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [chunkedCt1ReceivedMergeSpec]; simp only [arm64_norm, hsp, hx0, hx20, hx19]; rfl)
    (⟨rfl, rfl, rfl, hpe_bound.1, hpe_bound.2⟩ :
      BitVec.ofNat 8 iwt.toNat = BitVec.ofNat 8 iwt.toNat ∧
        x.msgPtr + 8#64 = x.msgPtr + 8#64 ∧
        x.bufRef = x.bufRef ∧
        optPolyEncoderPtsLen cr.sendingEk + rest.length < 2 ^ 56 ∧
        optPolyEncoderPolysLen cr.sendingEk + rest.length < 2 ^ 56)
    (by rw [hstk]; sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [chunkedCt1ReceivedMergeSpec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp only [arm64_norm, hsp, hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29] at hpcm hrunm hspm hx19_m hx20_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  have hm_field := v1State_mergeField_tag4 m iwt rest 99
  rw [hm_is] at hm_field; dsimp only at hm_field
  cases hcr_res : (Proto.mergeMessage V1State.Chunked.Ct1Received.mergeField (codecWireTypeToProto iwt) cr rest 99).toOption with
  | none =>
    rw [hcr_res, Option.map_none] at hm_field
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 2700#64) hinv_m ?_
    conv =>
      arg 4
      simp only [chunkedCt1ReceivedMergeSpec, chunkedMergeStack, hcr_res,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp]
    apply SepWP.exists_elim; intro cr'; apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hn_err⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    have hfold_is : (x.msgPtr ↦₆₄ 0x8000000000000003#64) ∗
        chunkedCt1ReceivedPBAt A (x.msgPtr + 8#64) cr' ∗ memRegion (x.msgPtr + 168#64) 56 ⊢
        ∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A x.msgPtr is' := by
      rw [chunkedCt1ReceivedPBAt_eq_proto]
      exact optProtoInnerStateAt_entails_exists A x.msgPtr (some (.ct1Received cr'))
    apply SepWP.fold hfold_is (by sep_focus)
    wp_steps; wp_reach; intro hinv_e
    apply SepWPp.weaken_pre (P' :=
      decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗ stackAt (s0.sp - 816#64) chunkedInlStack ∗
        memRegion (s0.sp - 816#64) 720 ∗ v1StateErrFramePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (Entails.of_eq (by dsimp only [v1StateErrFramePlaced, chunkedInlStack]; ac_rfl))
    exact honErr hm_field _ (sm.readReg64 (Reg.gpr 0#5)) n_err
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm]) hsm0 hn_err hinv_e
  | some p =>
    rcases p with ⟨cr', rest'⟩
    rw [hcr_res, Option.map_some] at hm_field
    have hrest'_le : rest'.length ≤ rest.length := proto_mergeMessage_len_le hcr_res
    have hpoly' : OptInnerStatePolyBound rest'.length (some (.ct1Received cr')) :=
      innerStatePolyBound_of_ct1Received (by rw [← optPolyEncoderBound_iff] at hpe_bound; exact hpe_bound) hcr_res
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 2700#64) hinv_m ?_
    conv =>
      arg 4
      simp only [chunkedCt1ReceivedMergeSpec, chunkedMergeStack, hcr_res,
        sepConj_assoc, arm64_norm, hsp]
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    wp_steps; wp_reach; intro hinv_n
    apply SepWPp.weaken_pre (P' :=
      v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr { m with innerState := some (.ct1Received cr') } x.bs rest')
      (Entails.of_eq (by dsimp only [v1StateLoopPrePlaced, optProtoInnerStateCapAt, protoInnerStateCapAt, chunkedInlStack]; ac_rfl))
    exact honOk { m with innerState := some (.ct1Received cr') } rest' _ hm_field hpoly' hrest'_le
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hsm0])
      ⟨by simp only [arm64_norm, hx19_m], by simp only [arm64_norm, hx20_m],
       by simp only [arm64_norm, hx22_m], by simp only [arm64_norm, hx23_m],
       by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m],
       by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
       by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hfp_m]⟩ hinv_n

theorem v1State_tag4_at_1140_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hCrCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 303)
      (withLsCodeRoLoaded lsmpl (chunkedCt1ReceivedMergeSpec A)))
    (hDropCr : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 282)
      (withLsCl lsmpl (dropProtoChunkedCt1ReceivedSpec A)))
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267)
      (withLsCl lsmpl (dropOptProtoInnerStatePlacedSpec A)))
    {s0 s : State} {x : V1StateMergeGhost} {R : SepProp} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hm_not : ∀ cr, m.innerState ≠ some (.ct1Received cr))
    (hentry : V1StateTagEntryHypPlaced H s0 x m rest iwt limit s)
    (hpc : s.pc = (blkPl_298).base + 1140#64)
    (hcont : V1StateTagContClPlaced A H s0 x R 4 m rest iwt limit) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergePlacedSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hsp_align, hrest_le, hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, _hx9, hregs, hinv⟩ := hentry
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  let fsp : BitVec 64 := s0.sp - 816#64
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := by
    dsimp only [fsp]; simpa only [arm64_norm] using hsp_align
  have hfsp720 : fsp + 720#64 = s0.sp - 96#64 := by dsimp only [fsp]; bv_lin
  have h56 : rest.length < 2 ^ 56 := optInnerStatePolyBound_lt_2_56 hpoly
  have hdef_pts : optPolyEncoderPtsLen (default : V1State.Chunked.Ct1Received).sendingEk + rest.length < 2 ^ 56 := by
    change 0 + rest.length < 2 ^ 56; omega
  have hdef_polys : optPolyEncoderPolysLen (default : V1State.Chunked.Ct1Received).sendingEk + rest.length < 2 ^ 56 := by
    change 0 + rest.length < 2 ^ 56; omega
  refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 303) hinv ?_
  conv =>
    arg 4
    rw [v1StateLoopPrePlaced, show s0.sp - 816#64 = fsp from rfl,
      memRegion_split_tag24_temp fsp, memRegion_160_split_tag24_init fsp,
      sliceCursorAfter_eq_split hrest_le hrest_suf]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w_sp400
  apply SepWP.exists_elim; intro w_sp120
  apply SepWP.exists_elim; intro w_sp16
  refine SepWP.weaken_pre (P' :=
    ((fsp + 16#64) ↦₆₄ w_sp16) ∗ memRegion (fsp + 24#64) 96 ∗
      ((fsp + 120#64) ↦₆₄ w_sp120) ∗ memRegion (fsp + 128#64) 48 ∗
      (stackAt fsp chunkedInlStack ∗ memRegion fsp 16 ∗ memRegion (fsp + 176#64) 64 ∗
        memRegion (fsp + 240#64) 160 ∗ ((fsp + 400#64) ↦₆₄ w_sp400) ∗
        memRegion (fsp + 408#64) 72 ∗ memRegion (fsp + 480#64) 160 ∗
        memRegion (fsp + 640#64) 80 ∗ v1StateJumpTablesPlacedAt ∗
        optProtoInnerStateCapAt A x.msgPtr rest.length m.innerState ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot restPtr rest ∗
        (x.ptr ↦ₛ x.bs.take (x.bs.length - rest.length)) ∗ A.pool ∗ v1StateSavedRegsAt s0.sp s0))
    (Entails.of_eq (by dsimp only [restPtr]; ac_rfl)) ?_
  refine SepWP.mono (v1State_tag24_setup_placed true (A := A) (restLen := rest.length) hfsp_align hpc hrun hsp hx23) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hP1, hsp1, htr1, hx0_1, hx1_1, hx2_1, hlr1,
    hx19_1, hx20_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1⟩ hinv_c
  rw [hsp] at hsp1; rw [hx19] at hx2_1 hx19_1; rw [hx20] at hx20_1
  rw [hx22] at hx22_1; rw [hx24] at hx24_1; rw [hx25] at hx25_1
  rw [hx26] at hx26_1; rw [hx27] at hx27_1; rw [hx28] at hx28_1; rw [hx29] at hx29_1
  have hx0_1' : (s1.readReg64 (Reg.gpr 0#5)).setWidth 8 = BitVec.ofNat 8 iwt.toNat := by
    rw [hx0_1, hx0]
  have hdef_cr : optUnchunked4CapAt A (fsp + 16#64) rest.length none ∗
      optPolynomialEncoderPBAt A ((fsp + 16#64) + 104#64) none =
      chunkedCt1ReceivedPBCapAt A (fsp + 16#64) rest.length default := by
    dsimp only [chunkedCt1ReceivedPBCapAt, default, Inhabited.default]
    rw [optUnchunkedEkSentCt1ReceivedPBCapAt_eq_optUnchunked4]; rfl
  rw [← sepConj_assoc, hdef_cr] at hP1
  apply SepWPp.weaken_pre hP1
  have hstk : chunkedMergeStack = chunkedInlStack := rfl
  refine SepWPp.call_frame_lscro (hinv := hinv_c)
    (x := ⟨iwt, fsp + 16#64, default, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := (blkPl_298).base + 1160#64) hCrCall
    hpc1 hrun1
    (by simp only [State.spAligned, hsp1]; exact hfsp_align) hlr1
    (by dsimp only [chunkedCt1ReceivedMergeSpec]; simp only [hx0_1', hx1_1, hx2_1, hsp1]; rfl)
    (⟨rfl, rfl, rfl, hdef_pts, hdef_polys⟩ :
      BitVec.ofNat 8 iwt.toNat = BitVec.ofNat 8 iwt.toNat ∧
        fsp + 16#64 = fsp + 16#64 ∧ x.bufRef = x.bufRef ∧
        optPolyEncoderPtsLen (default : V1State.Chunked.Ct1Received).sendingEk + rest.length < 2 ^ 56 ∧
        optPolyEncoderPolysLen (default : V1State.Chunked.Ct1Received).sendingEk + rest.length < 2 ^ 56)
    (by rw [hstk]; sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [chunkedCt1ReceivedMergeSpec] at hpan; exact allowPanic_frame' (htr1.trans htr) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, _hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  rw [hsp1] at hspm
  rw [hx19_1] at hx19_m; rw [hx20_1] at hx20_m; rw [hx22_1] at hx22_m; rw [hx23_1] at hx23_m
  rw [hx24_1] at hx24_m; rw [hx25_1] at hx25_m; rw [hx26_1] at hx26_m; rw [hx27_1] at hx27_m
  rw [hx28_1] at hx28_m; rw [hx29_1] at hfp_m
  have hm_field : (V1State.mergeField m (BitVec.ofNat 32 4) (codecWireTypeToProto iwt) rest 99).toOption =
      (Proto.mergeMessage V1State.Chunked.Ct1Received.mergeField (codecWireTypeToProto iwt) default rest 99).toOption.map
        (fun (v', rest') => ({ m with innerState := some (.ct1Received v') }, rest')) := by
    rw [v1State_mergeField_tag4]
    rcases h : m.innerState with _ | st
    · rfl
    · cases st with
      | ct1Received cr => exact absurd h (hm_not cr)
      | _ => rfl
  cases hcr_res : (Proto.mergeMessage V1State.Chunked.Ct1Received.mergeField (codecWireTypeToProto iwt) default rest 99).toOption with
  | none =>
    rw [hcr_res, Option.map_none] at hm_field
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 2700#64) hinv_m ?_
    conv =>
      arg 4
      simp only [chunkedCt1ReceivedMergeSpec, hcr_res,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp1]
    apply SepWP.exists_elim; intro cr'; apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hn_err⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    have hcr_words : chunkedCt1ReceivedPBAt A (fsp + 16#64) cr' ⊢
        ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64,
        ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64, ∃∗ w8 : BitVec 64,
        ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w11 : BitVec 64, ∃∗ w12 : BitVec 64,
        ∃∗ w13 : BitVec 64, ∃∗ w14 : BitVec 64, ∃∗ w15 : BitVec 64, ∃∗ w16 : BitVec 64,
        ∃∗ w17 : BitVec 64, ∃∗ w18 : BitVec 64, ∃∗ w19 : BitVec 64,
          words20At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ∗
          tag24CapHeap A 0 (cr'.uc.map fun u => (u.epoch, u.auth, u.dk, u.ct1)) cr'.sendingEk
            w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 := by
      refine Entails.trans (chunkedCt1ReceivedPBAt_entails_cap_zero A (fsp + 16#64) cr') ?_
      dsimp only [chunkedCt1ReceivedPBCapAt]
      rw [optUnchunkedEkSentCt1ReceivedPBCapAt_eq_optUnchunked4]
      exact tag24_extract_words A (fsp + 16#64) 0 (cr'.uc.map fun u => (u.epoch, u.auth, u.dk, u.ct1)) cr'.sendingEk
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
    apply SepWP.fold (Entails.trans (optProtoInnerStateCapAt_entails_pb A x.msgPtr rest.length m.innerState)
      (optProtoInnerStateAt_entails_exists A x.msgPtr m.innerState)) (by sep_focus)
    rw [hstk, v1StateBelow_dropStack48 (s0.sp - 816#64)]
    let Frame_err : SepProp :=
      tag24CapHeap A 0 (cr'.uc.map fun u => (u.epoch, u.auth, u.dk, u.ct1)) cr'.sendingEk
        w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ∗
      A.pool ∗ stackAt fsp dropStack48 ∗
      decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
      v1StateBelowRest fsp dropStack48 ∗
      memRegion fsp 16 ∗ memRegion (fsp + 176#64) 64 ∗
      memRegion (fsp + 408#64) 72 ∗ memRegion (fsp + 480#64) 160 ∗
      memRegion (fsp + 640#64) 80 ∗ v1StateJumpTablesPlacedAt ∗
      (∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A x.msgPtr is') ∗
      (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗
      (x.ptr ↦ₛ x.bs) ∗ v1StateSavedRegsAt s0.sp s0
    refine SepWP.weaken_pre (P' :=
      words20At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ∗
        memRegion (fsp + 240#64) 160 ∗ ((fsp + 400#64) ↦₆₄ w_sp400) ∗ Frame_err)
      (Entails.of_eq (by dsimp only [Frame_err, fsp]; ac_rfl)) ?_
    refine sepWP_seq_keep_lscl hinv_m.1 (v1State_tag24_copy_err_placed true hfsp_align hpcm hrunm hspm hsm0 hx20_m) ?_
    rintro s2 P2 hpc2 hrun2 hcl2 ⟨hP2, hsp2, htr2, hx21_2⟩
    apply SepWP.weaken_pre hP2
    dsimp only [Frame_err]
    apply SepWP.fold (tag24_words_entails_protoChunkedCt1Received A (fsp + 240#64)
      (cr'.uc.map fun u => (u.epoch, u.auth, u.dk, u.ct1)) cr'.sendingEk
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19) (by sep_focus)
    refine SepWP.weaken_pre (P' :=
      protoChunkedCt1ReceivedAt A (fsp + 240#64)
        { uc := (cr'.uc.map fun u => (u.epoch, u.auth, u.dk, u.ct1)).map
            (fun (epoch, auth, v3, v4) => { dk := v3, ct1 := v4, auth := auth, epoch := epoch }),
          sendingEk := cr'.sendingEk } ∗
        A.pool ∗ stackAt fsp dropStack48 ∗
        (memRegion (fsp + 16#64) 160 ∗ ((fsp + 400#64) ↦₆₄ x.msgPtr) ∗
          decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
          v1StateBelowRest fsp dropStack48 ∗
          memRegion fsp 16 ∗ memRegion (fsp + 176#64) 64 ∗
          memRegion (fsp + 408#64) 72 ∗ memRegion (fsp + 480#64) 160 ∗
          memRegion (fsp + 640#64) 80 ∗ v1StateJumpTablesPlacedAt ∗
          (∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A x.msgPtr is') ∗
          (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗
          (x.ptr ↦ₛ x.bs) ∗ v1StateSavedRegsAt s0.sp s0))
      (Entails.of_eq (by ac_rfl)) ?_
    refine SepWP.seq (v1State_tag24_err_1640_cl_placed hDropCr hcl2 hfsp_align hpc2 hrun2 (hsp2.trans hspm)) ?_
    rintro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, htr3, hx21_3⟩
    apply SepWP.weaken_pre hP3
    apply SepWP.fold (v1StateBelow_dropStack48_entails fsp) (by sep_focus)
    apply SepWP.fold (memRegion_fold_tag24_temp fsp x.msgPtr) (by sep_focus)
    refine SepWP.done hpc3 hrun3 (fun hinv3 => ?_)
    apply SepWPp.weaken_pre (P' :=
      decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗ stackAt (s0.sp - 816#64) chunkedInlStack ∗
        memRegion (s0.sp - 816#64) 720 ∗ v1StateErrFramePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (Entails.of_eq (by dsimp only [v1StateErrFramePlaced, fsp]; ac_rfl))
    exact hcont.onErr hm_field s3 (sm.readReg64 (Reg.gpr 0#5)) n_err hpc3 hrun3
      (hsp3.trans (hsp2.trans hspm))
      (htr3.trans (htr2.trans (htrm.trans (htr1.trans htr))))
      (hx21_3.trans hx21_2) hsm0 hn_err hinv3
  | some p =>
    rcases p with ⟨cr', rest'⟩
    rw [hcr_res, Option.map_some] at hm_field
    have hrest'_le : rest'.length ≤ rest.length := proto_mergeMessage_len_le hcr_res
    have hpoly' : OptInnerStatePolyBound rest'.length (some (.ct1Received cr')) :=
      innerStatePolyBound_of_ct1Received (bs := rest) (m := default) (optPolyEncoderBound_none h56) hcr_res
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 2700#64) hinv_m ?_
    conv =>
      arg 4
      simp only [chunkedCt1ReceivedMergeSpec, hcr_res, sepConj_assoc, arm64_norm, hsp1]
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (optProtoInnerStateCapAt_entails_pb A x.msgPtr rest.length m.innerState) (by sep_focus)
    have hcr_words : chunkedCt1ReceivedPBCapAt A (fsp + 16#64) rest'.length cr' ⊢
        ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64,
        ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64, ∃∗ w8 : BitVec 64,
        ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w11 : BitVec 64, ∃∗ w12 : BitVec 64,
        ∃∗ w13 : BitVec 64, ∃∗ w14 : BitVec 64, ∃∗ w15 : BitVec 64, ∃∗ w16 : BitVec 64,
        ∃∗ w17 : BitVec 64, ∃∗ w18 : BitVec 64, ∃∗ w19 : BitVec 64,
          words20At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ∗
          tag24CapHeap A rest'.length (cr'.uc.map fun u => (u.epoch, u.auth, u.dk, u.ct1)) cr'.sendingEk
            w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 := by
      dsimp only [chunkedCt1ReceivedPBCapAt]
      rw [optUnchunkedEkSentCt1ReceivedPBCapAt_eq_optUnchunked4]
      exact tag24_extract_words A (fsp + 16#64) rest'.length (cr'.uc.map fun u => (u.epoch, u.auth, u.dk, u.ct1)) cr'.sendingEk
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
    rw [hstk, v1StateBelow_dropStack96 (s0.sp - 816#64)]
    rw [← hfsp720] at hfp_m
    let Frame_ok : SepProp :=
      tag24CapHeap A rest'.length (cr'.uc.map fun u => (u.epoch, u.auth, u.dk, u.ct1)) cr'.sendingEk
        w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ∗
      optProtoInnerStateAt A x.msgPtr m.innerState ∗ A.pool ∗
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
    refine sepWP_seq_keep_lscl hinv_m.1 (v1State_tag24_copy_ok_placed true hfsp_align hpcm hrunm hspm hsm0 hx20_m) ?_
    rintro s2 P2 hpc2 hrun2 hcl2 ⟨hP2, hsp2, htr2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2⟩
    refine SepWP.weaken_pre (Entails.trans hP2 (Entails.of_eq (by ac_rfl :
      words20At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ∗
        memRegion (fsp + 240#64) 160 ∗ ((fsp + 400#64) ↦₆₄ x.msgPtr) ∗
        (memRegion (fsp + 480#64) 160 ∗ Frame_ok) =
      words20At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ∗
        memRegion (fsp + 480#64) 160 ∗
        (memRegion (fsp + 240#64) 160 ∗ ((fsp + 400#64) ↦₆₄ x.msgPtr) ∗ Frame_ok)))) ?_
    refine sepWP_seq_keep_lscl hcl2 (v1State_tag24_pre_drop_placed true hfsp_align hpc2 hrun2 (hsp2.trans hspm) hx20_2 (hx29_2.trans hfp_m)) ?_
    rintro s3 P3 hpc3 hrun3 hcl3 ⟨hP3, hsp3, htr3, hx0_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3⟩
    apply SepWP.weaken_pre hP3
    dsimp only [Frame_ok]
    refine SepWP.weaken_pre (P' :=
      optProtoInnerStateAt A x.msgPtr m.innerState ∗ A.pool ∗ optProtoInnerStateJumpTablePlacedAt ∗
        stackAt fsp dropStack96 ∗
        words20At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ∗
        (memRegion (fsp + 16#64) 160 ∗ memRegion (fsp + 240#64) 160 ∗ ((fsp + 400#64) ↦₆₄ x.msgPtr) ∗
          tag24CapHeap A rest'.length (cr'.uc.map fun u => (u.epoch, u.auth, u.dk, u.ct1)) cr'.sendingEk
            w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 ∗
          v1StateBelowRest fsp dropStack96 ∗
          memRegion fsp 16 ∗ memRegion (fsp + 176#64) 64 ∗
          memRegion (fsp + 408#64) 72 ∗ memRegion (fsp + 640#64) 80 ∗
          v1StateMergeJumpTablePlacedExpanded ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest' ∗
          v1StateSavedRegsAt s0.sp s0))
      (Entails.of_eq (by ac_rfl)) ?_
    refine SepWP.seq (v1State_tag24_post_drop_cl_placed true hDropInner hcl3 hfsp_align hpc3 hrun3
      (hsp3.trans (hsp2.trans hspm)) hx0_3 hx20_3 hx29_3) ?_
    rintro s4 P4 hpc4 hrun4 ⟨hP4, hsp4, htr4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4⟩
    apply SepWP.weaken_pre hP4
    simp only [↓reduceIte]
    apply SepWP.fold (v1StateBelow_dropStack96_entails fsp) (by sep_focus)
    apply SepWP.fold (memRegion_fold_tag24_temp fsp x.msgPtr) (by sep_focus)
    apply SepWP.fold (tag4_reconstruct_innerState A x.msgPtr rest'.length cr'
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19) (by sep_focus)
    refine SepWP.done hpc4 hrun4 (fun hinv4 => ?_)
    apply SepWPp.weaken_pre (P' :=
      v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr { m with innerState := some (.ct1Received cr') } x.bs rest')
      (Entails.of_eq (by dsimp only [v1StateLoopPrePlaced, v1StateJumpTablesPlacedAt, fsp]; ac_rfl))
    exact hcont.onOk { m with innerState := some (.ct1Received cr') } rest' s4 hm_field hpoly' hrest'_le
      hpc4 hrun4 (hsp4.trans (hsp3.trans (hsp2.trans hspm)))
      (htr4.trans (htr3.trans (htr2.trans (htrm.trans (htr1.trans htr)))))
      (hx21_4.trans (hx21_3.trans hx21_2))
      ⟨hx19_4.trans (hx19_3.trans (hx19_2.trans hx19_m)),
       hx20_4,
       hx22_4.trans (hx22_3.trans (hx22_2.trans hx22_m)),
       hx23_4.trans (hx23_3.trans (hx23_2.trans hx23_m)),
       hx24_4.trans (hx24_3.trans (hx24_2.trans hx24_m)),
       hx25_4.trans (hx25_3.trans (hx25_2.trans hx25_m)),
       hx26_4.trans (hx26_3.trans (hx26_2.trans hx26_m)),
       hx27_4.trans (hx27_3.trans (hx27_2.trans hx27_m)),
       hx28_4.trans (hx28_3.trans (hx28_2.trans hx28_m)),
       hx29_4.trans hfsp720⟩
      hinv4

private theorem v1State_tag4_branch_1140_cl_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {s0 s : State} {x : V1StateMergeGhost} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    {P : SepProp} {post panic : State → SepProp → Prop}
    (hm_not : ∀ cr, m.innerState ≠ some (.ct1Received cr))
    (hentry : V1StateTagEntryHypPlaced H s0 x m rest iwt limit s)
    (hpc : s.pc = (blkPl_298).base + 476#64)
    (hcont : ∀ s' : State,
      V1StateTagEntryHypPlaced H s0 x m rest iwt limit s' →
      s'.pc = (blkPl_298).base + 1140#64 →
      SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s' P post panic) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s P post panic := by
  obtain ⟨hsp_align, hrest_le, hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, hx9, hregs, hinv⟩ := hentry
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 1140#64) hinv ?_
  cases hm_is : m.innerState with
  | none =>
    have hx9_n : InnerStateDiscrFull rest.length none (s.readReg64 (Reg.gpr 9#5)) := hm_is ▸ hx9
    have hbr1 : (s.readReg64 (Reg.gpr 9#5) + 2#64 == 0#64) = true := (discrFull_none_add2 hx9_n).1
    wp_steps; wp_reach; intro hinv'
    exact hcont _
      ⟨hsp_align, hrest_le, hrest_lt, hrest_suf, hpoly,
        by simp only [arm64_norm, hrun], by simp only [arm64_norm, hsp],
        by simp only [arm64_norm, htr], by simp only [arm64_norm]; exact hx0,
        by simp only [arm64_norm]; exact hx9,
        ⟨by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20],
         by simp only [arm64_norm, hx22], by simp only [arm64_norm, hx23],
         by simp only [arm64_norm, hx24], by simp only [arm64_norm, hx25],
         by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27],
         by simp only [arm64_norm, hx28], by simp only [arm64_norm, hx29]⟩, hinv'⟩
      (by simp only [arm64_norm])
  | some is =>
    have hne : ∀ cr, is ≠ .ct1Received cr := fun cr h => hm_not cr (by rw [hm_is, h])
    have hx9_s : InnerStateDiscrFull rest.length (some is) (s.readReg64 (Reg.gpr 9#5)) := hm_is ▸ hx9
    have hbr1 : (s.readReg64 (Reg.gpr 9#5) + 2#64 == 0#64) = false := (discrFull_some_add2 hx9_s).1
    have hbr2 : (s.readReg64 (Reg.gpr 9#5) != 0x8000000000000003#64) = true :=
      discrFull_other_tag4 hne hx9_s
    wp_steps; wp_reach; intro hinv'
    exact hcont _
      ⟨hsp_align, hrest_le, hrest_lt, hrest_suf, hpoly,
        by simp only [arm64_norm, hrun], by simp only [arm64_norm, hsp],
        by simp only [arm64_norm, htr], by simp only [arm64_norm]; exact hx0,
        by simp only [arm64_norm]; exact hx9,
        ⟨by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20],
         by simp only [arm64_norm, hx22], by simp only [arm64_norm, hx23],
         by simp only [arm64_norm, hx24], by simp only [arm64_norm, hx25],
         by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27],
         by simp only [arm64_norm, hx28], by simp only [arm64_norm, hx29]⟩, hinv'⟩
      (by simp only [arm64_norm])

theorem v1State_tag4_step_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hCrCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 303)
      (withLsCodeRoLoaded lsmpl (chunkedCt1ReceivedMergeSpec A)))
    (hDropCr : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 282)
      (withLsCl lsmpl (dropProtoChunkedCt1ReceivedSpec A)))
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267)
      (withLsCl lsmpl (dropOptProtoInnerStatePlacedSpec A)))
    {s0 s : State} {x : V1StateMergeGhost} {R : SepProp} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hentry : V1StateTagEntryHypPlaced H s0 x m rest iwt limit s)
    (hpc : s.pc = (blkPl_298).base + 476#64)
    (hcont : V1StateTagContClPlaced A H s0 x R 4 m rest iwt limit) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergePlacedSpec A) x R s0) (WppPanic R s0) := by
  by_cases hex : ∃ cr, m.innerState = some (.ct1Received cr)
  · rcases hex with ⟨cr, hm_is⟩
    exact v1State_tag4_inplace_cl_placed hCrCall hm_is hentry hpc hcont
  · have hm_not : ∀ cr, m.innerState ≠ some (.ct1Received cr) := fun cr h => hex ⟨cr, h⟩
    refine v1State_tag4_branch_1140_cl_placed hm_not hentry hpc fun s' hentry' hpc' => ?_
    exact v1State_tag4_at_1140_cl_placed hCrCall hDropCr hDropInner hm_not hentry' hpc' hcont

end CryptoVerification.SpqrV1.Prost.MessageMerge

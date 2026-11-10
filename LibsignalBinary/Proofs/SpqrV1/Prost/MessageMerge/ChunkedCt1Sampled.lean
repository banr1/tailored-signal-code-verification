/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.MessageMergePart2CodeSym
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1Acknowledged
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyDecoder
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyEncoder
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedCt1Sent
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import ProofLib.SepLogic.WPp

/-!
# SPQR V1: Verification of `Chunked.Ct1Sampled::merge` (`0x4a390`)

Proves in-image (`0x4a390`) and relocatable `[LibsignalPlacement]` (Block `300`) `subroutine_ok`
contracts for `prost::encoding::message::merge::<spqr::proto::pq_ratchet::v1_state::chunked::Ct1Sampled, &mut &[u8]>`
against `chunkedCt1SampledMergeSpec`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Prost.MessageMerge

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen hiding vecU8Buf vecU8At_eq_header_sep_buf
open CryptoVerification.SpqrV1.Prost.BytesMerge
open _root_.CryptoVerification.SpqrV1.Auth hiding bv64_sub_zero bv64_add_zero
open CryptoVerification.LibsignalSpqrV1 hiding decodeVarint encodeVarint WireType
open CryptoVerification.CodeLayout
open ChunkedMerge

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero chunkedCt1SampledMerge_fnOff

/-! ## 1. Decode Table, Frame Bundles, Loop Invariant, and Shared Exit / Skip Lemmas -/

gen_decodes libsignalSessionCode_tree chunkedCt1SampledMergeBin [ 0x4a390 → 0x4a5f8 ]

macro "chunkedCt1SampledMerge_fetches " b:term:max H:term:max k0:num len:num : tactic =>
  `(tactic| code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.SpqrV1.Prost.MessageMerge.chunkedCt1SampledMergeBin $b $H
    CryptoVerification.SpqrV1.Prost.MessageMerge.chunkedCt1SampledMerge_fnOff 0x4a390 $k0 $len)

def ct1SampledErrFrame (A : RustAlloc) (s0 : State) (msgPtr bufRef slot ptr : BitVec 64)
    (m : V1State.Chunked.Ct1Sampled) (bs : List (BitVec 8)) : SepProp :=
  chunkedCt1SampledPBAt A msgPtr m ∗
    (bufRef ↦₆₄ slot) ∗ memRegion slot 16 ∗ (ptr ↦ₛ bs) ∗ A.pool ∗ chunkedSavedRegs s0

def ct1SampledLoopPre (A : RustAlloc) (s0 : State) (msgPtr bufRef slot ptr : BitVec 64)
    (m : V1State.Chunked.Ct1Sampled) (bs cur : List (BitVec 8)) : SepProp :=
  chunkedCt1SampledPBCapAt A msgPtr cur.length m ∗
    (bufRef ↦₆₄ slot) ∗ sliceCursorAfter slot ptr bs cur ∗ A.pool ∗
    memRegion (s0.sp - 128#64) 48 ∗ chunkedBelow s0.sp ∗ chunkedSavedRegs s0

theorem ct1Sampled_err0_ret_exit {b : BitVec 64} {A : RustAlloc} {H : String → Option (State → State)}
    {x : ChunkedCt1SampledMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.Ct1Sampled} {err : BitVec 64}
    (hnone : (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName + 124#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = err) (herr : err ≠ 0#64) (hcs : ChunkedHighCalleeSaved s0 s) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (decodeErrorAtStackLen A err 0 ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedBelow s0.sp ∗
        ct1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (WppPost (chunkedCt1SampledMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
  chunkedCt1SampledMerge_fetches b H 124 32
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName = entry; examples_hide_fetches
  apply SepWPp.of_sepWP_ret; unfold WppPost chunkedCt1SampledMergeSpec
  simp only [hnone, stackAt_chunkedMerge, ct1SampledErrFrame, chunkedSavedRegs,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp, hx1]
  apply SepWP.fold (decodeErrorWith_zero_entails_le3 A err) (by sep_focus)
  apply SepWP.fold (chunkedCt1SampledPBAt_entails_exists A x.msgPtr m) (by sep_focus)
  wp_steps; wp_done

theorem ct1Sampled_from_err_exit {b : BitVec 64} {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName + 0xffffffffffffb618#64) (decodeErrorFromSpec A))
    {x : ChunkedCt1SampledMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.Ct1Sampled} {w v_stk0 : BitVec 64}
    (hnone : (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hw : KindNoHeap w) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName + 108#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx8 : s.readReg64 (Reg.gpr 8#5) = w) (hcs : ChunkedHighCalleeSaved s0 s) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ v_stk0) ∗ memRegion (s0.sp - 120#64) 40 ∗ chunkedBelow s0.sp ∗
        ct1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (WppPost (chunkedCt1SampledMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
  chunkedCt1SampledMerge_fetches b H 108 48
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName = entry; examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 0xffffffffffffb618#64)
  conv => arg 4; rw [chunkedBelow_err s0.sp, ct1SampledErrFrame, chunkedSavedRegs]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPp.call_frame (x := (s0.sp - 128#64, w)) (ret_pc := entry + 120#64) hFromCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorFromSpec]; simp only [arm64_norm, hsp, hx8]; rfl) hw (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, _, _, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx26, hx27, hx28, hvregs] at hpcm hspm hx26_m hx27_m hx28_m hvregs_m
  apply SepWPp.of_sepWP_ret; unfold WppPost chunkedCt1SampledMergeSpec
  simp only [decodeErrorFromSpec, hnone, stackAt_chunkedMerge,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp, hspm]
  apply SepWP.fold (chunkedBelow_err_entails s0.sp) (by sep_focus)
  wp_steps
  apply SepWP.fold (decodeErrorWith_zero_entails_le3 A _) (by sep_focus)
  apply SepWP.fold (chunkedCt1SampledPBAt_entails_exists A x.msgPtr m) (by sep_focus)
  apply SepWP.fold (memRegion8_memRegion40_entails_48_128 s0.sp) (by sep_focus)
  wp_done

theorem ct1Sampled_push_err_exit {b : BitVec 64} {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName + 0xffffffffffffb320#64) (decodeErrorPushSpec A))
    {x : ChunkedCt1SampledMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.Ct1Sampled} {err : BitVec 64} {n : Nat}
    (hnone : (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (herr : err ≠ 0#64) (hn : n ≤ 2) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName + 604#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = s0.sp - 128#64) (hcs : ChunkedHighCalleeSaved s0 s) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A err n ∗ memRegion (s0.sp - 120#64) 40 ∗
        chunkedBelow s0.sp ∗ ct1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (WppPost (chunkedCt1SampledMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
  chunkedCt1SampledMerge_fetches b H 604 12; chunkedCt1SampledMerge_fetches b H 124 32
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName = entry; examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 0xffffffffffffb320#64)
  conv => arg 4; rw [chunkedBelow_err s0.sp, ct1SampledErrFrame, chunkedSavedRegs]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPp.call_frame (x := (s0.sp - 128#64, err, n)) (ret_pc := entry + 608#64) hPushCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorPushSpec]; simp only [arm64_norm, hsp, hx0]; rfl) (by omega : n < 2 ^ 32) (by sep_focus) (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, _, _, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx26, hx27, hx28, hvregs] at hpcm hspm hx26_m hx27_m hx28_m hvregs_m
  apply SepWPp.of_sepWP_ret; unfold WppPost chunkedCt1SampledMergeSpec
  simp only [decodeErrorPushSpec, hnone, stackAt_chunkedMerge,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp, hspm]
  apply SepWP.fold (chunkedBelow_err_entails s0.sp) (by sep_focus)
  wp_steps
  apply SepWP.fold (decodeErrorWith_succ_entails_le3 A err hn) (by sep_focus)
  apply SepWP.fold (chunkedCt1SampledPBAt_entails_exists A x.msgPtr m) (by sep_focus)
  apply SepWP.fold (pointsTo64_memRegion40_entails_48_128 s0.sp err) (by sep_focus)
  wp_done

theorem ct1Sampled_skip_step {b : BitVec 64} {A : RustAlloc} {H : String → Option (State → State)} {img : Obj.Image}
    (hSkipCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName + 0xffffffffffffc3ec#64) (skipField3Spec A))
    {x : ChunkedCt1SampledMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.Ct1Sampled} {rest : List (BitVec 8)} {iwt : WireType} {tag limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest) (htag_lt : tag < 2 ^ 32)
    (hnone_of_sf : skipField (2 * rest.length + 2) 98 tag iwt rest = none →
      (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (rest' : List (BitVec 8)) (s' : State),
      skipField (2 * rest.length + 2) 98 tag iwt rest = some rest' →
      s'.pc = (libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName + 192#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      ChunkedLoopRegs s0 s' → ImgCallInv img s' →
      SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s'
        (ct1SampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest') (WppPost (chunkedCt1SampledMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName + 172#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : (s.readReg64 (Reg.gpr 1#5)).setWidth 32 = BitVec.ofNat 32 tag)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : ChunkedLoopRegs s0 s) (himg : ImgCallInv img s) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (ct1SampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest) (WppPost (chunkedCt1SampledMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have herr0_exit := @ct1Sampled_err0_ret_exit b A H x R s0
  chunkedCt1SampledMerge_fetches b H 172 20
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName = entry; examples_hide_fetches
  apply SepWPp.of_sepWP_img (mid := entry + 0xffffffffffffc3ec#64) himg
  conv => arg 4; rw [ct1SampledLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf, chunkedBelow_skipField3_98 s0.sp]
  simp only [sepConj_assoc]; wp_steps; wp_reach; intro himg1
  refine SepWPp.call_frame_keep (hinv := himg1) (x := ⟨iwt, tag, 98, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := entry + 184#64) hSkipCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [skipField3Spec]; simp only [arm64_norm, hsp, hx0, hx1, hx19, setWidth8_ofNat64_wt]; rfl)
    (⟨htag_lt, by decide, hrest_lt⟩ : tag < 2 ^ 32 ∧ 98 < 2 ^ 32 ∧ rest.length < 2 ^ 63) (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm himgm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m hvregs_m
  cases hsf : skipField (2 * rest.length + 2) 98 tag iwt rest with
  | none =>
    have hnone := hnone_of_sf hsf; apply SepWPp.of_sepWP (mid := entry + 124#64)
    conv => arg 4; simp only [skipField3Spec, hsf, sepConj_assoc, arm64_norm, hsp]
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (chunkedBelow_skipField3_98_entails s0.sp) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (chunkedCt1SampledPBCapAt_entails_pb A x.msgPtr rest.length m) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPp.weaken_pre (P' :=
      decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ memRegion (s0.sp - 128#64) 48 ∗
        chunkedBelow s0.sp ∗ ct1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (Entails.of_eq (by dsimp only [ct1SampledErrFrame]; ac_rfl))
    exact herr0_exit hnone hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm]) hsm0 ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some rest' =>
    have hrest'_le : rest'.length ≤ rest.length := (skip_length _).1 _ _ _ _ _ hsf
    apply SepWPp.of_sepWP_img (mid := entry + 192#64) himgm
    conv => arg 4; simp only [skipField3Spec, hsf, sepConj_assoc, arm64_norm, hsp]
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    apply SepWP.fold (chunkedBelow_skipField3_98_entails s0.sp) (by sep_focus)
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (chunkedCt1SampledPBCapAt_mono A x.msgPtr m hrest'_le) (by sep_focus)
    wp_steps; wp_reach; intro himg2
    apply SepWPp.weaken_pre (P' := ct1SampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest')
      (Entails.of_eq (by dsimp only [ct1SampledLoopPre]; ac_rfl))
    exact hcont rest' _ hsf (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m]) ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m], ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩⟩ himg2

/-! ## 2. Field Merge Step Lemmas (Tag 1 `uc`, Tag 2 `sending_ct1`, and Tag 3 `receiving_ek`) -/

theorem ct1Sampled_tag1_init_step {b : BitVec 64} {A : RustAlloc} {H : String → Option (State → State)} {img : Obj.Image}
    {a v0 v19 v21 v22 : BitVec 64} {n : Nat} {opt : Option V1State.Unchunked.Ct1Sent}
    {F : SepProp} {s0 s : State} {post panic : State → SepProp → Prop}
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName + 368#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = v0) (hx19 : s.readReg64 (Reg.gpr 19#5) = v19)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = a) (hx21 : s.readReg64 (Reg.gpr 21#5) = v21)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = v22) (hcs : ChunkedLoopRegs s0 s) (himg : ImgCallInv img s)
    (hcont : ∀ s' : State,
      s'.pc = (libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName + 404#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = v0 → s'.readReg64 (Reg.gpr 19#5) = v19 →
      s'.readReg64 (Reg.gpr 20#5) = a → s'.readReg64 (Reg.gpr 21#5) = v21 →
      s'.readReg64 (Reg.gpr 22#5) = v22 → ChunkedLoopRegs s0 s' → ImgCallInv img s' →
      SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s'
        (unchunkedCt1SentPBCapAt A a n (opt.getD default) ∗ F) post panic) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (optUnchunkedCt1SentPBCapAt A a n opt ∗ F) post panic := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  chunkedCt1SampledMerge_fetches b H 368 36
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName = entry; examples_hide_fetches
  cases opt with
  | none =>
    apply SepWPp.of_sepWP_img (mid := entry + 404#64) himg
    conv => arg 4; rw [optUnchunkedCt1SentPBCapAt, memRegion_ct1Sent_none_split a]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro w120; apply SepWP.exists_elim; intro w72; apply SepWP.exists_elim; intro w64
    apply SepWP.exists_elim; intro w56; apply SepWP.exists_elim; intro w48; apply SepWP.exists_elim; intro w40
    apply SepWP.exists_elim; intro w32; apply SepWP.exists_elim; intro w24; apply SepWP.exists_elim; intro w16; apply SepWP.exists_elim; intro w8
    wp_steps; apply SepWP.fold (default_ct1Sent_entails_cap A a n) (by sep_focus); wp_reach; intro himg'
    exact hcont _ (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx0]) (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20]) (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22]) ⟨by simp only [arm64_norm, hx23], by simp only [arm64_norm, hx24], by simp only [arm64_norm, hx25], ⟨by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩⟩ himg'
  | some u =>
    apply SepWPp.of_sepWP_img (mid := entry + 404#64) himg
    conv => arg 4; rw [optUnchunkedCt1SentPBCapAt, unchunkedCt1SentPBCapAt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro cap_ct1; apply SepWP.exists_elim; intro ptr_ct1
    apply SepWP.exists_elim; intro cap_es; apply SepWP.exists_elim; intro ptr_es
    apply SepWP.exists_elim; intro cap_hdr; apply SepWP.exists_elim; intro ptr_hdr; apply SepWP.pure_elim; intro hcap_hdr
    conv => arg 4; rw [vecU8At_eq_header_sep_buf A a cap_hdr ptr_hdr u.hdr, vecHeader]; simp only [sepConj_assoc]
    apply SepWP.fold (vecU8Buf_entails_cap_lt A cap_hdr ptr_hdr u.hdr) (by sep_focus)
    wp_simp_pre [sepConj_assoc]; apply SepWP.pure_elim; intro hcap_lt
    have hcmn1 := cap_add_one_beq_zero_false hcap_lt; have hcmn2 := cap_add_one_bne_zero_true hcap_lt; wp_steps
    have hfold_hdr : (a ↦₆₄ cap_hdr) ∗ ((a + 8#64) ↦₆₄ ptr_hdr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 u.hdr.length) ∗ vecU8Buf A cap_hdr ptr_hdr u.hdr ⊢
        (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap n⌝ ∗ vecU8At A a cap ptr u.hdr) := by
      refine Entails.trans ?_ (Entails.sepExists_right cap_hdr (Entails.sepExists_right ptr_hdr (Entails.refl _)))
      refine Entails.pure_right hcap_hdr ?_; rw [vecU8At_eq_header_sep_buf, vecHeader]; exact Entails.of_eq (by ac_rfl)
    have hfold_es : ⌜BytesMergeCapOk cap_es n⌝ ∗ vecU8At A (a + 24#64) cap_es ptr_es u.es ⊢
        (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap n⌝ ∗ vecU8At A (a + 24#64) cap ptr u.es) :=
      Entails.sepExists_right cap_es (Entails.sepExists_right ptr_es (Entails.refl _))
    have hfold_ct1 : ⌜BytesMergeCapOk cap_ct1 n⌝ ∗ vecU8At A (a + 48#64) cap_ct1 ptr_ct1 u.ct1 ⊢
        (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap n⌝ ∗ vecU8At A (a + 48#64) cap ptr u.ct1) :=
      Entails.sepExists_right cap_ct1 (Entails.sepExists_right ptr_ct1 (Entails.refl _))
    apply SepWP.fold hfold_hdr (by sep_focus); apply SepWP.fold hfold_es (by sep_focus); apply SepWP.fold hfold_ct1 (by sep_focus); wp_reach; intro himg'
    apply SepWPp.weaken_pre (P' := unchunkedCt1SentPBCapAt A a n u ∗ F)
      (Entails.of_eq (by dsimp only [unchunkedCt1SentPBCapAt]; ac_rfl))
    exact hcont _ (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx0]) (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20]) (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22]) ⟨by simp only [arm64_norm, hx23], by simp only [arm64_norm, hx24], by simp only [arm64_norm, hx25], ⟨by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩⟩ himg'

set_option maxHeartbeats 800000 in
theorem ct1Sampled_tag1_step {b : BitVec 64} {A : RustAlloc} {H : String → Option (State → State)} {img : Obj.Image}
    (hUcCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName + 0x2714#64) ((unchunkedCt1SentMergeSpec A).inImage img))
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName + 0xffffffffffffb320#64) (decodeErrorPushSpec A))
    {x : ChunkedCt1SampledMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.Ct1Sampled} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_uc :
      (Proto.mergeMessage V1State.Unchunked.Ct1Sent.mergeField (codecWireTypeToProto iwt) (m.uc.getD default) rest 98).toOption = none →
      (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (u' : V1State.Unchunked.Ct1Sent) (rest' : List (BitVec 8)) (s' : State),
      (Proto.mergeMessage V1State.Unchunked.Ct1Sent.mergeField (codecWireTypeToProto iwt) (m.uc.getD default) rest 98).toOption = some (u', rest') →
      s'.pc = (libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName + 192#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      ChunkedLoopRegs s0 s' → ImgCallInv img s' →
      SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s'
        (ct1SampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with uc := some u' } x.bs rest') (WppPost (chunkedCt1SampledMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName + 368#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : ChunkedLoopRegs s0 s) (himg : ImgCallInv img s) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (ct1SampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest) (WppPost (chunkedCt1SampledMergeSpec A) x R s0) (WppPanic R s0) := by
  apply SepWPp.weaken_pre (P' :=
    optUnchunkedCt1SentPBCapAt A x.msgPtr rest.length m.uc ∗
      (optPolynomialEncoderPBAt A (x.msgPtr + 128#64) m.sendingCt1 ∗
        optPolynomialDecoderPBAt A (x.msgPtr + 184#64) m.receivingEk ∗ (x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedBelow s0.sp ∗ chunkedSavedRegs s0))
    (Entails.of_eq (by dsimp only [ct1SampledLoopPre, chunkedCt1SampledPBCapAt]; ac_rfl))
  refine ct1Sampled_tag1_init_step hpc hrun hsp htr hx0 hx19 hx20 hx21 hx22 hcs himg ?_
  clear hpc hrun hsp htr hx0 hx19 hx20 hx21 hx22 hcs himg s
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hx21_1 hx22_1 hcs1 himg1
  obtain ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1⟩ := hcs1
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hpush_exit := @ct1Sampled_push_err_exit b A H hPushCall x R s0
  chunkedCt1SampledMerge_fetches b H 404 24; chunkedCt1SampledMerge_fetches b H 536 36
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName = entry; examples_hide_fetches
  apply SepWPp.of_sepWP_img (mid := entry + 0x2714#64) himg1
  conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, chunkedBelow_eq_unchunked s0.sp]
  simp only [sepConj_assoc]; wp_steps; wp_reach; intro himg2
  refine SepWPp.call_frame_inImage (hinv := himg2) (x := ⟨iwt, x.msgPtr, m.uc.getD default, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := entry + 416#64) hUcCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
    (by simp only [State.spAligned, hsp1, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [unchunkedCt1SentMergeSpec]; simp only [arm64_norm, hsp1, hx0_1, hx20_1, hx19_1, setWidth8_ofNat64_wt]; rfl)
    (⟨rfl, rfl, rfl, hrest_lt⟩ : BitVec.ofNat 8 iwt.toNat = BitVec.ofNat 8 iwt.toNat ∧ x.msgPtr = x.msgPtr ∧ x.bufRef = x.bufRef ∧ rest.length < 2 ^ 63) (by sep_focus) (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [unchunkedCt1SentMergeSpec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr1]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm himgm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m hvregs_m
  cases huc_res : (Proto.mergeMessage V1State.Unchunked.Ct1Sent.mergeField (codecWireTypeToProto iwt) (m.uc.getD default) rest 98).toOption with
  | none =>
    have hnone := hnone_of_uc huc_res; apply SepWPp.of_sepWP (mid := entry + 604#64)
    conv => arg 4; simp only [unchunkedCt1SentMergeSpec, huc_res, memRegion_48_split_128 s0.sp,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp1]
    apply SepWP.exists_elim; intro v_stk0; apply SepWP.exists_elim; intro u'; apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hn_err⟩
    have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus); wp_steps; wp_reach
    apply SepWPp.weaken_pre (P' :=
      ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
        memRegion (s0.sp - 120#64) 40 ∗ chunkedBelow s0.sp ∗
        ct1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { m with uc := some u' } x.bs)
      (Entails.of_eq (by dsimp only [ct1SampledErrFrame, chunkedCt1SampledPBAt, optCt1SentPBAt, chunkedBelow]; ac_rfl))
    exact hpush_exit hnone hsm0 hn_err hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr1]) (by simp only [arm64_norm, hspm]) ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨u', rest'⟩
    have hrest'_le : rest'.length ≤ rest.length := proto_mergeMessage_len_le huc_res
    apply SepWPp.of_sepWP_img (mid := entry + 192#64) himgm
    conv => arg 4; simp only [unchunkedCt1SentMergeSpec, huc_res, sepConj_assoc, arm64_norm, hsp1]
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus); wp_steps; wp_reach; intro himg3
    apply SepWPp.weaken_pre (P' := ct1SampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with uc := some u' } x.bs rest')
      (Entails.of_eq (by dsimp only [ct1SampledLoopPre, chunkedCt1SampledPBCapAt, optUnchunkedCt1SentPBCapAt, chunkedBelow]; ac_rfl))
    exact hcont u' rest' _ huc_res (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr1]) (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m]) ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m], ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩⟩ himg3

theorem ct1Sampled_tag2_init_step {b : BitVec 64} {A : RustAlloc} {H : String → Option (State → State)} {img : Obj.Image}
    {a v0 v19 v21 v22 : BitVec 64} {opt : Option PolynomialEncoder} {F : SepProp} {s0 s : State} {post panic : State → SepProp → Prop}
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName + 316#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = v0) (hx19 : s.readReg64 (Reg.gpr 19#5) = v19)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = a) (hx21 : s.readReg64 (Reg.gpr 21#5) = v21)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = v22) (hcs : ChunkedLoopRegs s0 s) (himg : ImgCallInv img s)
    (hcont : ∀ s' : State,
      s'.pc = (libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName + 344#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = v0 → s'.readReg64 (Reg.gpr 19#5) = v19 →
      s'.readReg64 (Reg.gpr 20#5) = a → s'.readReg64 (Reg.gpr 21#5) = v21 →
      s'.readReg64 (Reg.gpr 22#5) = v22 → ChunkedLoopRegs s0 s' → ImgCallInv img s' →
      SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s'
        (polynomialEncoderPBAt A (a + 128#64) (opt.getD default) ∗ F) post panic) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (optPolynomialEncoderPBAt A (a + 128#64) opt ∗ F) post panic := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  chunkedCt1SampledMerge_fetches b H 316 28
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName = entry; examples_hide_fetches
  cases opt with
  | none =>
    apply SepWPp.of_sepWP_img (mid := entry + 344#64) himg
    conv => arg 4; rw [optPolynomialEncoderPBAt, memRegion_polyEncoder_none_split (a + 128#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro w48; apply SepWP.exists_elim; intro w40
    apply SepWP.exists_elim; intro w32; apply SepWP.exists_elim; intro w24
    apply SepWP.exists_elim; intro w16; apply SepWP.exists_elim; intro w8; wp_steps
    apply SepWP.fold (default_polyEncoder_entails_pb A (a + 128#64)) (by sep_focus); wp_reach; intro himg'
    exact hcont _ (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx0]) (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20]) (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22]) ⟨by simp only [arm64_norm, hx23], by simp only [arm64_norm, hx24], by simp only [arm64_norm, hx25], ⟨by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩⟩ himg'
  | some pe =>
    apply SepWPp.of_sepWP_img (mid := entry + 344#64) himg
    conv => arg 4; rw [optPolynomialEncoderPBAt, polynomialEncoderPBAt, vecVecU8At_eq_exists_pin A (a + 128#64) pe.pts]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro pin
    conv => arg 4; rw [vecVecU8PinnedAt_eq_header_buf]; simp only [sepConj_assoc]
    apply SepWP.fold (vecVecU8Buf_entails_cap_lt A pin.cap pin.ptr pe.pts) (by sep_focus)
    wp_simp_pre [sepConj_assoc]; apply SepWP.pure_elim; intro hcap_lt
    have hcmn1 := cap_add_one_beq_zero_false hcap_lt; have hcmn2 := cap_add_one_bne_zero_true hcap_lt; wp_steps
    have hfold_pts : ((a + 128#64) ↦₆₄ pin.cap) ∗ ((a + 128#64 + 8#64) ↦₆₄ pin.ptr) ∗
        ((a + 128#64 + 16#64) ↦₆₄ BitVec.ofNat 64 pe.pts.length) ∗ vecVecU8Buf A pin.cap pin.ptr pe.pts ⊢
        vecVecU8At A (a + 128#64) pe.pts := by
      rw [vecVecU8At_eq_exists_pin]; refine Entails.trans ?_ (Entails.sepExists_right pin (Entails.refl _))
      rw [vecVecU8PinnedAt_eq_header_buf]; exact Entails.of_eq (by ac_rfl)
    apply SepWP.fold hfold_pts (by sep_focus); wp_reach; intro himg'
    apply SepWPp.weaken_pre (P' := polynomialEncoderPBAt A (a + 128#64) pe ∗ F)
      (Entails.of_eq (by dsimp only [polynomialEncoderPBAt]; ac_rfl))
    exact hcont _ (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx0]) (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20]) (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22]) ⟨by simp only [arm64_norm, hx23], by simp only [arm64_norm, hx24], by simp only [arm64_norm, hx25], ⟨by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩⟩ himg'

set_option maxHeartbeats 800000 in
theorem ct1Sampled_tag2_step {b : BitVec 64} {A : RustAlloc} {H : String → Option (State → State)} {img : Obj.Image}
    (hPolyEncCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName + 0xffffffffffffed10#64) ((polyEncoderMergeSpec A).inImage img))
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName + 0xffffffffffffb320#64) (decodeErrorPushSpec A))
    {x : ChunkedCt1SampledMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.Ct1Sampled} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length) (hrest_suf : IsDropSuffix x.bs rest)
    (hpts_lt : optPolyEncoderPtsLen m.sendingCt1 + rest.length < 2 ^ 56)
    (hpolys_lt : optPolyEncoderPolysLen m.sendingCt1 + rest.length < 2 ^ 56)
    (hnone_of_pe :
      (Proto.mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto iwt) (m.sendingCt1.getD default) rest 98).toOption = none →
      (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (pe' : PolynomialEncoder) (rest' : List (BitVec 8)) (s' : State),
      (Proto.mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto iwt) (m.sendingCt1.getD default) rest 98).toOption = some (pe', rest') →
      s'.pc = (libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName + 192#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      ChunkedLoopRegs s0 s' → ImgCallInv img s' →
      SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s'
        (ct1SampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with sendingCt1 := some pe' } x.bs rest') (WppPost (chunkedCt1SampledMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName + 316#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : ChunkedLoopRegs s0 s) (himg : ImgCallInv img s) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (ct1SampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest) (WppPost (chunkedCt1SampledMergeSpec A) x R s0) (WppPanic R s0) := by
  apply SepWPp.weaken_pre (P' :=
    optPolynomialEncoderPBAt A (x.msgPtr + 128#64) m.sendingCt1 ∗
      (optUnchunkedCt1SentPBCapAt A x.msgPtr rest.length m.uc ∗
        optPolynomialDecoderPBAt A (x.msgPtr + 184#64) m.receivingEk ∗ (x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedBelow s0.sp ∗ chunkedSavedRegs s0))
    (Entails.of_eq (by dsimp only [ct1SampledLoopPre, chunkedCt1SampledPBCapAt]; ac_rfl))
  refine ct1Sampled_tag2_init_step hpc hrun hsp htr hx0 hx19 hx20 hx21 hx22 hcs himg ?_
  clear hpc hrun hsp htr hx0 hx19 hx20 hx21 hx22 hcs himg s
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hx21_1 hx22_1 hcs1 himg1
  obtain ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1⟩ := hcs1
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hpush_exit := @ct1Sampled_push_err_exit b A H hPushCall x R s0
  chunkedCt1SampledMerge_fetches b H 344 24; chunkedCt1SampledMerge_fetches b H 572 32
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName = entry; examples_hide_fetches
  apply SepWPp.of_sepWP_img (mid := entry + 0xffffffffffffed10#64) himg1
  conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, ← protoPolynomialEncoderAt_eq_pb, chunkedBelow_eq_poly s0.sp]
  simp only [sepConj_assoc]; wp_steps; wp_reach; intro himg2
  refine SepWPp.call_frame_inImage (hinv := himg2) (x := ⟨iwt, x.msgPtr + 128#64, m.sendingCt1.getD default, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := entry + 356#64) hPolyEncCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
    (by simp only [State.spAligned, hsp1, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [polyEncoderMergeSpec]; simp only [arm64_norm, hsp1, hx0_1, hx20_1, hx19_1, setWidth8_ofNat64_wt, optPolyEncoder_getD_default_pts_len, optPolyEncoder_getD_default_polys_len]; rfl)
    (⟨rfl, rfl, rfl, hpts_lt, hpolys_lt⟩ : BitVec.ofNat 8 iwt.toNat = BitVec.ofNat 8 iwt.toNat ∧ x.msgPtr + 128#64 = x.msgPtr + 128#64 ∧ x.bufRef = x.bufRef ∧ optPolyEncoderPtsLen m.sendingCt1 + rest.length < 2 ^ 56 ∧ optPolyEncoderPolysLen m.sendingCt1 + rest.length < 2 ^ 56) (by sep_focus) (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [polyEncoderMergeSpec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr1]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm himgm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m hvregs_m
  cases hpe_res : (Proto.mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto iwt) (m.sendingCt1.getD default) rest 98).toOption with
  | none =>
    have hnone := hnone_of_pe hpe_res; apply SepWPp.of_sepWP (mid := entry + 604#64)
    conv => arg 4; simp only [polyEncoderMergeSpec, hpe_res, protoPolynomialEncoderAt_eq_pb,
      memRegion_48_split_128 s0.sp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp1]
    apply SepWP.exists_elim; intro v_stk0; apply SepWP.exists_elim; intro pe'; apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hn_err⟩
    have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (optUnchunkedCt1SentPBCapAt_entails_optCt1SentPBAt A x.msgPtr rest.length m.uc) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPp.weaken_pre (P' :=
      ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
        memRegion (s0.sp - 120#64) 40 ∗ chunkedBelow s0.sp ∗
        ct1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { m with sendingCt1 := some pe' } x.bs)
      (Entails.of_eq (by dsimp only [ct1SampledErrFrame, chunkedCt1SampledPBAt, optPolynomialEncoderPBAt, chunkedBelow, unchunkedMergeStack, polyMergeStack, authMergeStack, polyBelowStack]; ac_rfl))
    exact hpush_exit hnone hsm0 (by omega : n_err ≤ 2) hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr1]) (by simp only [arm64_norm, hspm]) ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨pe', rest'⟩
    have hrest'_le : rest'.length ≤ rest.length := proto_mergeMessage_len_le hpe_res
    apply SepWPp.of_sepWP_img (mid := entry + 192#64) himgm
    conv => arg 4; simp only [polyEncoderMergeSpec, hpe_res, protoPolynomialEncoderAt_eq_pb, sepConj_assoc, arm64_norm, hsp1]
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (optUnchunkedCt1SentPBCapAt_mono A x.msgPtr m.uc hrest'_le) (by sep_focus)
    wp_steps; wp_reach; intro himg3
    apply SepWPp.weaken_pre (P' := ct1SampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with sendingCt1 := some pe' } x.bs rest')
      (Entails.of_eq (by dsimp only [ct1SampledLoopPre, chunkedCt1SampledPBCapAt, optPolynomialEncoderPBAt, chunkedBelow, unchunkedMergeStack, polyMergeStack, authMergeStack, polyBelowStack]; ac_rfl))
    exact hcont pe' rest' _ hpe_res (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr1]) (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m]) ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m], ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩⟩ himg3

theorem ct1Sampled_tag3_init_step {b : BitVec 64} {A : RustAlloc} {H : String → Option (State → State)} {img : Obj.Image}
    {a v0 v19 v21 v22 : BitVec 64} {opt : Option PolynomialDecoder} {F : SepProp} {s0 s : State} {post panic : State → SepProp → Prop}
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName + 268#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = v0) (hx19 : s.readReg64 (Reg.gpr 19#5) = v19)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = a) (hx21 : s.readReg64 (Reg.gpr 21#5) = v21)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = v22) (hcs : ChunkedLoopRegs s0 s) (himg : ImgCallInv img s)
    (hcont : ∀ s' : State,
      s'.pc = (libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName + 292#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = v0 → s'.readReg64 (Reg.gpr 19#5) = v19 →
      s'.readReg64 (Reg.gpr 20#5) = a → s'.readReg64 (Reg.gpr 21#5) = v21 →
      s'.readReg64 (Reg.gpr 22#5) = v22 → ChunkedLoopRegs s0 s' → ImgCallInv img s' →
      SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s'
        (polynomialDecoderPBAt A (a + 184#64) (opt.getD default) ∗ F) post panic) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (optPolynomialDecoderPBAt A (a + 184#64) opt ∗ F) post panic := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  chunkedCt1SampledMerge_fetches b H 268 24
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName = entry; examples_hide_fetches
  cases opt with
  | none =>
    apply SepWPp.of_sepWP_img (mid := entry + 292#64) himg
    conv => arg 4; rw [optPolynomialDecoderPBAt, memRegion_polyDecoder_none_split (a + 184#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro w32; apply SepWP.exists_elim; intro w24
    apply SepWP.exists_elim; intro w16; apply SepWP.exists_elim; intro w8; wp_steps
    apply SepWP.fold (default_polyDecoder_entails_pb A (a + 184#64)) (by sep_focus); wp_reach; intro himg'
    exact hcont _ (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx0]) (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20]) (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22]) ⟨by simp only [arm64_norm, hx23], by simp only [arm64_norm, hx24], by simp only [arm64_norm, hx25], ⟨by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩⟩ himg'
  | some pe =>
    apply SepWPp.of_sepWP_img (mid := entry + 292#64) himg
    conv => arg 4; rw [optPolynomialDecoderPBAt, polynomialDecoderPBAt, vecVecU8At_eq_exists_pin A (a + 184#64) pe.pts]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro pin
    conv => arg 4; rw [vecVecU8PinnedAt_eq_header_buf]; simp only [sepConj_assoc]
    apply SepWP.fold (vecVecU8Buf_entails_cap_lt A pin.cap pin.ptr pe.pts) (by sep_focus)
    wp_simp_pre [sepConj_assoc]; apply SepWP.pure_elim; intro hcap_lt
    have hcmn1 := cap_add_one_beq_zero_false hcap_lt; have hcmn2 := cap_add_one_bne_zero_true hcap_lt; wp_steps
    have hfold_pts : ((a + 184#64) ↦₆₄ pin.cap) ∗ ((a + 184#64 + 8#64) ↦₆₄ pin.ptr) ∗
        ((a + 184#64 + 16#64) ↦₆₄ BitVec.ofNat 64 pe.pts.length) ∗ vecVecU8Buf A pin.cap pin.ptr pe.pts ⊢
        vecVecU8At A (a + 184#64) pe.pts := by
      rw [vecVecU8At_eq_exists_pin]; refine Entails.trans ?_ (Entails.sepExists_right pin (Entails.refl _))
      rw [vecVecU8PinnedAt_eq_header_buf]; exact Entails.of_eq (by ac_rfl)
    apply SepWP.fold hfold_pts (by sep_focus); wp_reach; intro himg'
    apply SepWPp.weaken_pre (P' := polynomialDecoderPBAt A (a + 184#64) pe ∗ F)
      (Entails.of_eq (by dsimp only [polynomialDecoderPBAt]; ac_rfl))
    exact hcont _ (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx0]) (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20]) (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22]) ⟨by simp only [arm64_norm, hx23], by simp only [arm64_norm, hx24], by simp only [arm64_norm, hx25], ⟨by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩⟩ himg'

set_option maxHeartbeats 800000 in
theorem ct1Sampled_tag3_step {b : BitVec 64} {A : RustAlloc} {H : String → Option (State → State)} {img : Obj.Image}
    (hPolyDecCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName + 0xffffffffffffe984#64) ((polyDecoderMergeSpec A).inImage img))
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName + 0xffffffffffffb320#64) (decodeErrorPushSpec A))
    {x : ChunkedCt1SampledMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.Ct1Sampled} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length) (hrest_suf : IsDropSuffix x.bs rest)
    (hpts_lt : optPolyDecoderPtsLen m.receivingEk + rest.length < 2 ^ 56)
    (hnone_of_pd :
      (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto iwt) (m.receivingEk.getD default) rest 98).toOption = none →
      (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (pd' : PolynomialDecoder) (rest' : List (BitVec 8)) (s' : State),
      (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto iwt) (m.receivingEk.getD default) rest 98).toOption = some (pd', rest') →
      s'.pc = (libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName + 192#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      ChunkedLoopRegs s0 s' → ImgCallInv img s' →
      SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s'
        (ct1SampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with receivingEk := some pd' } x.bs rest') (WppPost (chunkedCt1SampledMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName + 268#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : ChunkedLoopRegs s0 s) (himg : ImgCallInv img s) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (ct1SampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest) (WppPost (chunkedCt1SampledMergeSpec A) x R s0) (WppPanic R s0) := by
  apply SepWPp.weaken_pre (P' :=
    optPolynomialDecoderPBAt A (x.msgPtr + 184#64) m.receivingEk ∗
      (optUnchunkedCt1SentPBCapAt A x.msgPtr rest.length m.uc ∗
        optPolynomialEncoderPBAt A (x.msgPtr + 128#64) m.sendingCt1 ∗ (x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedBelow s0.sp ∗ chunkedSavedRegs s0))
    (Entails.of_eq (by dsimp only [ct1SampledLoopPre, chunkedCt1SampledPBCapAt]; ac_rfl))
  refine ct1Sampled_tag3_init_step hpc hrun hsp htr hx0 hx19 hx20 hx21 hx22 hcs himg ?_
  clear hpc hrun hsp htr hx0 hx19 hx20 hx21 hx22 hcs himg s
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hx21_1 hx22_1 hcs1 himg1
  obtain ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1⟩ := hcs1
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hpush_exit := @ct1Sampled_push_err_exit b A H hPushCall x R s0
  chunkedCt1SampledMerge_fetches b H 292 24; chunkedCt1SampledMerge_fetches b H 500 36
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName = entry; examples_hide_fetches
  apply SepWPp.of_sepWP_img (mid := entry + 0xffffffffffffe984#64) himg1
  conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, ← protoPolynomialDecoderAt_eq_pb, chunkedBelow_eq_poly s0.sp]
  simp only [sepConj_assoc]; wp_steps; wp_reach; intro himg2
  refine SepWPp.call_frame_inImage (hinv := himg2) (x := ⟨iwt, x.msgPtr + 184#64, m.receivingEk.getD default, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := entry + 304#64) hPolyDecCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
    (by simp only [State.spAligned, hsp1, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [polyDecoderMergeSpec]; simp only [arm64_norm, hsp1, hx0_1, hx20_1, hx19_1, setWidth8_ofNat64_wt, optPolyDecoder_getD_default_pts_len]; rfl)
    (⟨rfl, rfl, rfl, hpts_lt⟩ : BitVec.ofNat 8 iwt.toNat = BitVec.ofNat 8 iwt.toNat ∧ x.msgPtr + 184#64 = x.msgPtr + 184#64 ∧ x.bufRef = x.bufRef ∧ optPolyDecoderPtsLen m.receivingEk + rest.length < 2 ^ 56) (by sep_focus) (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [polyDecoderMergeSpec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr1]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm himgm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m hvregs_m
  cases hpd_res : (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto iwt) (m.receivingEk.getD default) rest 98).toOption with
  | none =>
    have hnone := hnone_of_pd hpd_res; apply SepWPp.of_sepWP (mid := entry + 604#64)
    conv => arg 4; simp only [polyDecoderMergeSpec, hpd_res, protoPolynomialDecoderAt_eq_pb,
      memRegion_48_split_128 s0.sp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp1]
    apply SepWP.exists_elim; intro v_stk0; apply SepWP.exists_elim; intro pd'; apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hn_err⟩
    have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (optUnchunkedCt1SentPBCapAt_entails_optCt1SentPBAt A x.msgPtr rest.length m.uc) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPp.weaken_pre (P' :=
      ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
        memRegion (s0.sp - 120#64) 40 ∗ chunkedBelow s0.sp ∗
        ct1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { m with receivingEk := some pd' } x.bs)
      (Entails.of_eq (by dsimp only [ct1SampledErrFrame, chunkedCt1SampledPBAt, optPolynomialDecoderPBAt, chunkedBelow, unchunkedMergeStack, polyMergeStack, authMergeStack, polyBelowStack]; ac_rfl))
    exact hpush_exit hnone hsm0 (by omega : n_err ≤ 2) hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr1]) (by simp only [arm64_norm, hspm]) ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨pd', rest'⟩
    have hrest'_le : rest'.length ≤ rest.length := proto_mergeMessage_len_le hpd_res
    apply SepWPp.of_sepWP_img (mid := entry + 192#64) himgm
    conv => arg 4; simp only [polyDecoderMergeSpec, hpd_res, protoPolynomialDecoderAt_eq_pb, sepConj_assoc, arm64_norm, hsp1]
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (optUnchunkedCt1SentPBCapAt_mono A x.msgPtr m.uc hrest'_le) (by sep_focus)
    wp_steps; wp_reach; intro himg3
    apply SepWPp.weaken_pre (P' := ct1SampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with receivingEk := some pd' } x.bs rest')
      (Entails.of_eq (by dsimp only [ct1SampledLoopPre, chunkedCt1SampledPBCapAt, optPolynomialDecoderPBAt, chunkedBelow, unchunkedMergeStack, polyMergeStack, authMergeStack, polyBelowStack]; ac_rfl))
    exact hcont pd' rest' _ hpd_res (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr1]) (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m]) ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m], ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩⟩ himg3

/-! ## 3. Loop Exit, Key Decode, Main Loop Induction, and Top-Level Theorems -/

theorem ct1Sampled_loop_le_exit {b : BitVec 64} {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName + 0xffffffffffffb618#64) (decodeErrorFromSpec A))
    {x : ChunkedCt1SampledMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.Ct1Sampled} {cur : List (BitVec 8)} {limit : Nat}
    (hle_lim : cur.length ≤ limit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_suf : IsDropSuffix x.bs cur) (hlim_lt : limit < 2 ^ 63)
    (hres_cur : (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
      (mergeLoopBin V1State.Chunked.Ct1Sampled.mergeField (cur.length - limit) m cur limit 98).map
        (fun m' => (m', x.bs.drop (x.bs.length - limit))))
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName + 192#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit) (hcs : ChunkedLoopRegs s0 s) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (ct1SampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs cur) (WppPost (chunkedCt1SampledMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  by_cases heq_lim : cur.length = limit
  · obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq heq_lim
    have hcur_eq_drop : x.bs.drop (x.bs.length - limit) = cur := by rw [← heq_lim]; exact hcur_suf.symm
    have hsome : (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
        some (m, cur) := by
      rw [hres_cur, mergeLoopBin_eq_limit _ _ _ _ _ _ heq_lim, Option.map_some, hcur_eq_drop]
    chunkedCt1SampledMerge_fetches b H 192 12; chunkedCt1SampledMerge_fetches b H 428 12
    chunkedCt1SampledMerge_fetches b H 124 32
    generalize_entry (libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName = entry; examples_hide_fetches
    apply SepWPp.of_sepWP_ret; unfold WppPost chunkedCt1SampledMergeSpec
    simp only [hsome, stackAt_chunkedMerge, ct1SampledLoopPre, chunkedSavedRegs,
      sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp]
    wp_steps; wp_done
  · have hlt_lim : cur.length < limit := Nat.lt_of_le_of_ne hle_lim heq_lim
    obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_lt hlt_lim hlim_lt
    have hnone : (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
      rw [hres_cur, mergeLoopBin_lt_limit _ _ _ _ _ _ hlt_lim, Option.map_none]
    have hfrom_exit := @ct1Sampled_from_err_exit b A H hFromCall x R s0
    chunkedCt1SampledMerge_fetches b H 192 12; chunkedCt1SampledMerge_fetches b H 428 4
    chunkedCt1SampledMerge_fetches b H 484 16
    generalize_entry (libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName = entry; examples_hide_fetches
    apply SepWPp.of_sepWP (mid := entry + 108#64)
    conv => arg 4; rw [ct1SampledLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
      sliceCursorAt, memRegion_48_split_128 s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v_stk0; wp_steps
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot curPtr (BitVec.ofNat 64 cur.length)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    apply SepWP.fold (chunkedCt1SampledPBCapAt_entails_pb A x.msgPtr cur.length m) (by sep_focus)
    wp_reach
    apply SepWPp.weaken_pre (P' :=
      ((s0.sp - 128#64) ↦₆₄ v_stk0) ∗ memRegion (s0.sp - 120#64) 40 ∗
        chunkedBelow s0.sp ∗ ct1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (Entails.of_eq (by dsimp only [ct1SampledErrFrame]; ac_rfl))
    exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000008#64) hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr]) (by simp only [arm64_norm]) ⟨by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩

theorem ct1Sampled_decode_key_step {b : BitVec 64} {A : RustAlloc} {H : String → Option (State → State)} {img : Obj.Image}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName + 0xffffffffffffb618#64) (decodeErrorFromSpec A))
    (hVarintCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName + 0xffffffffffffdd44#64) (decodeVarint2Spec A))
    {x : ChunkedCt1SampledMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.Ct1Sampled} {cur : List (BitVec 8)} {limit : Nat}
    (hgt_lim : ¬ cur.length ≤ limit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_lt : cur.length < 2 ^ 63) (hcur_suf : IsDropSuffix x.bs cur)
    (hres_cur : (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
      (mergeLoopBin V1State.Chunked.Ct1Sampled.mergeField (cur.length - limit) m cur limit 98).map
        (fun m' => (m', x.bs.drop (x.bs.length - limit))))
    (hcont : ∀ (key : BitVec 64) (iwt : WireType) (rest : List (BitVec 8)) (s' : State),
      decodeVarint cur = some (key, rest) → ¬ 2 ^ 32 ≤ key.toNat →
      WireType.ofNat? (key.toNat % 8) = some iwt → ¬ key.toNat / 8 < 1 →
      s'.pc = (libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName + 244#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      ChunkedLoopRegs s0 s' → ImgCallInv img s' →
      SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s'
        (ct1SampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest) (WppPost (chunkedCt1SampledMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName + 192#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : ChunkedLoopRegs s0 s) (himg : ImgCallInv img s) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (ct1SampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs cur) (WppPost (chunkedCt1SampledMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  have herr0_exit := @ct1Sampled_err0_ret_exit b A H x R s0
  have hfrom_exit := @ct1Sampled_from_err_exit b A H hFromCall x R s0
  chunkedCt1SampledMerge_fetches b H 192 52; chunkedCt1SampledMerge_fetches b H 440 44
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName = entry; examples_hide_fetches
  apply SepWPp.of_sepWP_img (mid := entry + 0xffffffffffffdd44#64) himg
  conv => arg 4; rw [ct1SampledLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt, chunkedBelow_leaf s0.sp]
  simp only [sepConj_assoc]; wp_steps; wp_reach; intro himg1
  refine SepWPp.call_frame_keep (hinv := himg1) (x := ⟨x.bufRef, x.slot, curPtr, cur⟩) (ret_pc := entry + 212#64) hVarintCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, hsp, hx19]; rfl)
    hcur_lt (by dsimp only [sliceCursorAt, curPtr]; sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm himgm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m hvregs_m
  cases hd : decodeVarint cur with
  | none =>
    have hnone : (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
      rw [hres_cur, mergeLoopBin_of_decodeVarint_none protoPrefixStep_chunked_ct1Sampled_mergeField hgt_lim hd, Option.map_none]
    apply SepWPp.of_sepWP (mid := entry + 124#64)
    conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
    apply SepWP.fold (chunkedBelow_leaf_entails s0.sp) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    apply SepWP.fold (chunkedCt1SampledPBCapAt_entails_pb A x.msgPtr cur.length m) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPp.weaken_pre (P' :=
      decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ memRegion (s0.sp - 128#64) 48 ∗
        chunkedBelow s0.sp ∗ ct1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (Entails.of_eq (by dsimp only [ct1SampledErrFrame]; ac_rfl))
    exact herr0_exit hnone hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm]) hsm1 ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨key, rest⟩
    have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
    have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
    have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le
    have hrest_suf : IsDropSuffix x.bs rest := suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
    let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
    by_cases hk_ge : 2 ^ 32 ≤ key.toNat
    · have hnone : (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
        rw [hres_cur, mergeLoopBin_of_key_ge protoPrefixStep_chunked_ct1Sampled_mergeField hgt_lim hd hk_ge, Option.map_none]
      have hshr := key_shr32_of_ge hk_ge; apply SepWPp.of_sepWP (mid := entry + 108#64)
      conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]
      apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
      apply SepWP.fold (chunkedBelow_leaf_entails s0.sp) (by sep_focus)
      apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
      apply SepWP.fold (chunkedCt1SampledPBCapAt_entails_pb A x.msgPtr cur.length m) (by sep_focus)
      conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_split2_128 s0.sp]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply SepWP.exists_elim; intro v_err0; apply SepWP.exists_elim; intro v_err1; wp_steps
      apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
      apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
      have h40 : ((s0.sp - 128#64 + 8#64) ↦₆₄ key) ∗ memRegion (s0.sp - 112#64) 32 ⊢ memRegion (s0.sp - 120#64) 40 := by
        rw [bv_sub_add_lit s0.sp 128 8]; exact pointsTo64_memRegion32_entails_40_128 s0.sp key
      apply SepWP.fold h40 (by sep_focus); wp_reach
      apply SepWPp.weaken_pre (P' :=
        ((s0.sp - 128#64) ↦₆₄ v_err1) ∗ memRegion (s0.sp - 120#64) 40 ∗
          chunkedBelow s0.sp ∗ ct1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
        (Entails.of_eq (by dsimp only [ct1SampledErrFrame]; ac_rfl))
      exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000004#64) hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm]) ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
    · have hshr := key_shr32_of_lt hk_ge
      cases hwt : WireType.ofNat? (key.toNat % 8) with
      | none =>
        have hnone : (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
          rw [hres_cur, mergeLoopBin_of_wt_none protoPrefixStep_chunked_ct1Sampled_mergeField hgt_lim hd hk_ge hwt, Option.map_none]
        obtain ⟨hcs1, hcs2⟩ := key_wt_none hwt; apply SepWPp.of_sepWP (mid := entry + 108#64)
        conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]
        apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
        apply SepWP.fold (chunkedBelow_leaf_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
        apply SepWP.fold (chunkedCt1SampledPBCapAt_entails_pb A x.msgPtr cur.length m) (by sep_focus)
        conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_split2_128 s0.sp]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        apply SepWP.exists_elim; intro v_err0; apply SepWP.exists_elim; intro v_err1; wp_steps
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        have h40 : ((s0.sp - 128#64 + 8#64) ↦₆₄ (key &&& 7#64)) ∗ memRegion (s0.sp - 112#64) 32 ⊢ memRegion (s0.sp - 120#64) 40 := by
          rw [bv_sub_add_lit s0.sp 128 8]; exact pointsTo64_memRegion32_entails_40_128 s0.sp (key &&& 7#64)
        apply SepWP.fold h40 (by sep_focus); wp_reach
        apply SepWPp.weaken_pre (P' :=
          ((s0.sp - 128#64) ↦₆₄ v_err1) ∗ memRegion (s0.sp - 120#64) 40 ∗
            chunkedBelow s0.sp ∗ ct1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
          (Entails.of_eq (by dsimp only [ct1SampledErrFrame]; ac_rfl))
        exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000003#64) hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm]) ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
      | some iwt =>
        obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
        obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_ge
        obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
        by_cases hitag0 : key.toNat / 8 < 1
        · have hnone : (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
            rw [hres_cur, mergeLoopBin_of_tag_zero protoPrefixStep_chunked_ct1Sampled_mergeField hgt_lim hd hk_ge hwt hitag0, Option.map_none]
          have htag_zero : key.toNat / 8 = 0 := by omega
          apply SepWPp.of_sepWP (mid := entry + 108#64)
          conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]
          apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
          apply SepWP.fold (chunkedBelow_leaf_entails s0.sp) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          apply SepWP.fold (chunkedCt1SampledPBCapAt_entails_pb A x.msgPtr cur.length m) (by sep_focus)
          conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_split_128 s0.sp]
          simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
          apply SepWP.exists_elim; intro v_err0; wp_steps
          apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
          apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus); wp_reach
          apply SepWPp.weaken_pre (P' :=
            ((s0.sp - 128#64) ↦₆₄ v_err0) ∗ memRegion (s0.sp - 120#64) 40 ∗
              chunkedBelow s0.sp ∗ ct1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
            (Entails.of_eq (by dsimp only [ct1SampledErrFrame]; ac_rfl))
          exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000005#64) hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm]) ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
        · obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_ge hitag0
          have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
            rw [beq_eq_false_iff_ne]; intro h; have h1 := congrArg BitVec.toNat h
            simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1; omega
          apply SepWPp.of_sepWP_img (mid := entry + 244#64) himgm
          conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]
          apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
          apply SepWP.fold (chunkedBelow_leaf_entails s0.sp) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          apply SepWP.fold (chunkedCt1SampledPBCapAt_mono A x.msgPtr m hrest_le_cur) (by sep_focus)
          wp_steps; wp_reach; intro himg'
          apply SepWPp.weaken_pre (P' := ct1SampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
            (Entails.of_eq (by dsimp only [ct1SampledLoopPre]; ac_rfl))
          exact hcont key iwt rest _ hd hk_ge hwt hitag0 (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
            (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm, hsm1, hand_wt])
            (by simp only [arm64_norm, hsm1, hw1, hw1_2, hw1_zext1, hw1_zext2]) (by simp only [arm64_norm, hx19_m])
            (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
            ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m],
             ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩⟩ himg'

theorem ct1Sampled_loop_ok {b : BitVec 64} {A : RustAlloc} {H : String → Option (State → State)} {img : Obj.Image}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName + 0xffffffffffffb618#64) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName + 0xffffffffffffb320#64) (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName + 0xffffffffffffdd44#64) (decodeVarint2Spec A))
    (hSkipCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName + 0xffffffffffffc3ec#64) (skipField3Spec A))
    (hUcCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName + 0x2714#64) ((unchunkedCt1SentMergeSpec A).inImage img))
    (hPolyEncCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName + 0xffffffffffffed10#64) ((polyEncoderMergeSpec A).inImage img))
    (hPolyDecCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName + 0xffffffffffffe984#64) ((polyDecoderMergeSpec A).inImage img))
    {x : ChunkedCt1SampledMergeGhost} {R : SepProp} {s0 : State} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hbs_lt : x.bs.length < 2 ^ 63) (hlim_lt : limit < 2 ^ 63) :
    ∀ (n : Nat) (m : V1State.Chunked.Ct1Sampled) (cur : List (BitVec 8)) (s : State),
      cur.length ≤ n → cur.length ≤ x.bs.length → IsDropSuffix x.bs cur →
      optPolyEncoderPtsLen m.sendingCt1 + cur.length < 2 ^ 56 →
      optPolyEncoderPolysLen m.sendingCt1 + cur.length < 2 ^ 56 →
      optPolyDecoderPtsLen m.receivingEk + cur.length < 2 ^ 56 →
      (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
        (mergeLoopBin V1State.Chunked.Ct1Sampled.mergeField (cur.length - limit) m cur limit 98).map
          (fun m' => (m', x.bs.drop (x.bs.length - limit))) →
      s.pc = (libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName + 192#64 →
      s.status = .Running → s.sp = s0.sp - 128#64 → s.trace = s0.trace →
      s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      ChunkedLoopRegs s0 s → ImgCallInv img s →
      SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
        (ct1SampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs cur) (WppPost (chunkedCt1SampledMergeSpec A) x R s0) (WppPanic R s0) := by
  have htag1_step := fun {s m rest iwt} => @ct1Sampled_tag1_step b A H img hUcCall hPushCall x R s0 s m rest iwt limit
  have htag2_step := fun {s m rest iwt} => @ct1Sampled_tag2_step b A H img hPolyEncCall hPushCall x R s0 s m rest iwt limit
  have htag3_step := fun {s m rest iwt} => @ct1Sampled_tag3_step b A H img hPolyDecCall hPushCall x R s0 s m rest iwt limit
  have hskip_step := fun {s m rest tag iwt} => @ct1Sampled_skip_step b A H img hSkipCall x R s0 s m rest iwt tag limit
  intro n; induction n with
  | zero =>
    intro m cur s hcur_n hcur_le hcur_suf _ _ _ hres_cur hpc hrun hsp htr hx19 hx20 hx21 hx22 hcs _
    exact ct1Sampled_loop_le_exit hFromCall (by omega) hsp_align hcur_le hcur_suf hlim_lt hres_cur hpc hrun hsp htr hx21 hx22 hcs
  | succ n ih =>
    intro m cur s hcur_n hcur_le hcur_suf hpts hpolys hdec_pts hres_cur hpc hrun hsp htr hx19 hx20 hx21 hx22 hcs himg
    by_cases hle_lim : cur.length ≤ limit
    · exact ct1Sampled_loop_le_exit hFromCall hle_lim hsp_align hcur_le hcur_suf hlim_lt hres_cur hpc hrun hsp htr hx21 hx22 hcs
    · have hcur_lt : cur.length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
      refine ct1Sampled_decode_key_step hFromCall hVarintCall hle_lim hsp_align hcur_le hcur_lt hcur_suf hres_cur ?_ hpc hrun hsp htr hx19 hx20 hx21 hx22 hcs himg
      intro key iwt rest s' hd hk_ge hwt hitag0 hpc' hrun' hsp' htr' hx0' hx1' hx19' hx20' hx21' hx22' hcs' himg'
      obtain ⟨hx23', hx24', hx25', hx26', hx27', hx28', hvregs'⟩ := hcs'
      have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
      have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
      have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le
      have hrest_lt : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest_le hbs_lt
      have hrest_suf : IsDropSuffix x.bs rest := suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
      have hloop_ok := mergeLoopBin_of_key_ok (m := m) (depth' := 98) protoPrefixStep_chunked_ct1Sampled_mergeField hle_lim hd hk_ge hwt hitag0
      by_cases htag1 : key.toNat / 8 = 1
      · rw [htag1] at hx1' hloop_ok; rw [chunkedCt1Sampled_mergeField_tag1] at hloop_ok
        chunkedCt1SampledMerge_fetches b H 244 8
        generalize_entry (libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName = entry; examples_hide_fetches
        apply SepWPp.of_sepWP_img (mid := entry + 368#64) himg'; wp_steps; wp_reach; intro himg_s
        have hnone_uc : (Proto.mergeMessage V1State.Unchunked.Ct1Sent.mergeField (codecWireTypeToProto iwt) (m.uc.getD default) rest 98).toOption = none →
            (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
          intro huc; simp only [hres_cur, hloop_ok, huc, Option.map_none]
        refine htag1_step hsp_align hrest_le hrest_lt hrest_suf hnone_uc
          (fun u' rest' s'' huc hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' himg'' => ?_) (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr']) (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20']) (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) ⟨by simp only [arm64_norm, hx23'], by simp only [arm64_norm, hx24'], by simp only [arm64_norm, hx25'], ⟨by simp only [arm64_norm, hx26'], by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩⟩ himg_s
        have huf := proto_mergeMessage_suffix huc
        have hres_next : (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
            (mergeLoopBin V1State.Chunked.Ct1Sampled.mergeField (rest'.length - limit) { m with uc := some u' } rest' limit 98).map
              (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
          simp only [hres_cur, hloop_ok, huc, Option.map_some]
        exact ih { m with uc := some u' } rest' s'' (by have := huf.1; omega) (by have := huf.1; omega)
          (suffix_trans hrest_le hrest_suf huf.1 huf.2)
          (by dsimp only; have := huf.1; omega) (by dsimp only; have := huf.1; omega) (by dsimp only; have := huf.1; omega)
          hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' himg''
      · by_cases htag2 : key.toNat / 8 = 2
        · rw [htag2] at hx1' hloop_ok; rw [chunkedCt1Sampled_mergeField_tag2] at hloop_ok
          chunkedCt1SampledMerge_fetches b H 244 16
          generalize_entry (libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName = entry; examples_hide_fetches
          apply SepWPp.of_sepWP_img (mid := entry + 316#64) himg'; wp_steps; wp_reach; intro himg_s
          have hnone_pe : (Proto.mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto iwt) (m.sendingCt1.getD default) rest 98).toOption = none →
              (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
            intro hpe; simp only [hres_cur, hloop_ok, hpe, Option.map_none]
          refine htag2_step hsp_align hrest_le hrest_suf (by omega) (by omega) hnone_pe
            (fun pe' rest' s'' hpe hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' himg'' => ?_)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
            (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20']) (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22'])
            ⟨by simp only [arm64_norm, hx23'], by simp only [arm64_norm, hx24'], by simp only [arm64_norm, hx25'], ⟨by simp only [arm64_norm, hx26'], by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩⟩ himg_s
          have hpf := proto_mergeMessage_suffix hpe
          obtain ⟨hpts_le, hpolys_le⟩ := polyEncoder_mergeMessage_pts_polys_len hpe
          have hpts_eq : (m.sendingCt1.getD default).pts.length = optPolyEncoderPtsLen m.sendingCt1 := optPolyEncoder_getD_default_pts_len m.sendingCt1
          have hpolys_eq : (m.sendingCt1.getD default).polys.length = optPolyEncoderPolysLen m.sendingCt1 := optPolyEncoder_getD_default_polys_len m.sendingCt1
          have hres_next : (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
              (mergeLoopBin V1State.Chunked.Ct1Sampled.mergeField (rest'.length - limit) { m with sendingCt1 := some pe' } rest' limit 98).map
                (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
            simp only [hres_cur, hloop_ok, hpe, Option.map_some]
          exact ih { m with sendingCt1 := some pe' } rest' s'' (by have := hpf.1; omega) (by have := hpf.1; omega)
            (suffix_trans hrest_le hrest_suf hpf.1 hpf.2)
            (by dsimp only [optPolyEncoderPtsLen]; omega) (by dsimp only [optPolyEncoderPolysLen]; omega) (by dsimp only; have := hpf.1; omega)
            hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' himg''
        · by_cases htag3 : key.toNat / 8 = 3
          · have hitag_lt : key.toNat / 8 < 2 ^ 32 := by omega
            obtain ⟨hb1_1, _⟩ := itag_beq_tag_false htag1 hitag_lt (by decide : 1 < 2 ^ 32)
            obtain ⟨hb2_1, _⟩ := itag_beq_tag_false htag2 hitag_lt (by decide : 2 < 2 ^ 32)
            have hb1_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 1#32) = false := by rw [sf_truncate32_ofNat64]; exact hb1_1
            have hb2_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 2#32) = false := by rw [sf_truncate32_ofNat64]; exact hb2_1
            rw [htag3] at hx1' hloop_ok; rw [chunkedCt1Sampled_mergeField_tag3] at hloop_ok
            chunkedCt1SampledMerge_fetches b H 244 24
            generalize_entry (libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName = entry; examples_hide_fetches
            apply SepWPp.of_sepWP_img (mid := entry + 268#64) himg'; wp_steps; wp_reach; intro himg_s
            have hnone_pd : (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto iwt) (m.receivingEk.getD default) rest 98).toOption = none →
                (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
              intro hpd; simp only [hres_cur, hloop_ok, hpd, Option.map_none]
            refine htag3_step hsp_align hrest_le hrest_suf (by omega) hnone_pd
              (fun pd' rest' s'' hpd hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' himg'' => ?_)
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
              (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20']) (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22'])
              ⟨by simp only [arm64_norm, hx23'], by simp only [arm64_norm, hx24'], by simp only [arm64_norm, hx25'], ⟨by simp only [arm64_norm, hx26'], by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩⟩ himg_s
            have hpf := proto_mergeMessage_suffix hpd
            have hdec_le := polyDecoder_mergeMessage_pts_len hpd
            have hdec_eq : (m.receivingEk.getD default).pts.length = optPolyDecoderPtsLen m.receivingEk := optPolyDecoder_getD_default_pts_len m.receivingEk
            have hres_next : (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
                (mergeLoopBin V1State.Chunked.Ct1Sampled.mergeField (rest'.length - limit) { m with receivingEk := some pd' } rest' limit 98).map
                  (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
              simp only [hres_cur, hloop_ok, hpd, Option.map_some]
            exact ih { m with receivingEk := some pd' } rest' s'' (by have := hpf.1; omega) (by have := hpf.1; omega)
              (suffix_trans hrest_le hrest_suf hpf.1 hpf.2)
              (by dsimp only; have := hpf.1; omega) (by dsimp only; have := hpf.1; omega) (by dsimp only [optPolyDecoderPtsLen]; omega)
              hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' himg''
          · have hitag_lt : key.toNat / 8 < 2 ^ 32 := by omega
            obtain ⟨hb1_1, _⟩ := itag_beq_tag_false htag1 hitag_lt (by decide : 1 < 2 ^ 32)
            obtain ⟨hb2_1, _⟩ := itag_beq_tag_false htag2 hitag_lt (by decide : 2 < 2 ^ 32)
            obtain ⟨hb3_1, _⟩ := itag_beq_tag_false htag3 hitag_lt (by decide : 3 < 2 ^ 32)
            have hb1_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 1#32) = false := by rw [sf_truncate32_ofNat64]; exact hb1_1
            have hb2_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 2#32) = false := by rw [sf_truncate32_ofNat64]; exact hb2_1
            have hb3_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 3#32) = false := by rw [sf_truncate32_ofNat64]; exact hb3_1
            have hb3_bne1 : (BitVec.ofNat 32 (key.toNat / 8) != 3#32) = true := by simp only [bne, hb3_1, Bool.not_false]
            have hb3_bne2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) != 3#32) = true := by simp only [bne, hb3_2, Bool.not_false]
            rw [chunkedCt1Sampled_mergeField_other m iwt rest 98 hitag_lt htag1 htag2 htag3] at hloop_ok
            chunkedCt1SampledMerge_fetches b H 244 24
            generalize_entry (libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName = entry; examples_hide_fetches
            apply SepWPp.of_sepWP_img (mid := entry + 172#64) himg'; wp_steps; wp_reach; intro himg_s
            have hnone_sf : skipField (2 * rest.length + 2) 98 (key.toNat / 8) iwt rest = none →
                (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
              intro hsf; rw [hres_cur, hloop_ok, hsf]; rfl
            refine hskip_step hsp_align hrest_le hrest_lt hrest_suf hitag_lt hnone_sf
              (fun rest' s'' hsf hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' himg'' => ?_)
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
              (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx1', sf_truncate32_ofNat64])
              (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20']) (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22'])
              ⟨by simp only [arm64_norm, hx23'], by simp only [arm64_norm, hx24'], by simp only [arm64_norm, hx25'], ⟨by simp only [arm64_norm, hx26'], by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩⟩ himg_s
            have hrest'_le_rest : rest'.length ≤ rest.length := (skip_length (2 * rest.length + 2)).1 _ _ _ _ _ hsf
            have hres_next : (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
                (mergeLoopBin V1State.Chunked.Ct1Sampled.mergeField (rest'.length - limit) m rest' limit 98).map
                  (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
              rw [hres_cur, hloop_ok, hsf]; rfl
            exact ih m rest' s'' (by omega) (by omega)
              (suffix_trans hrest_le hrest_suf hrest'_le_rest ((skip_suffix (2 * rest.length + 2)).1 _ _ _ _ _ hsf))
              (by omega) (by omega) (by omega)
              hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' himg''

set_option maxHeartbeats 800000 in
theorem chunkedCt1Sampled_merge_ok_of_contracts {b : BitVec 64} {A : RustAlloc} {H : String → Option (State → State)} {img : Obj.Image}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName + 0xffffffffffffb618#64) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName + 0xffffffffffffb320#64) (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName + 0xffffffffffffdd44#64) (decodeVarint2Spec A))
    (hSkipCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName + 0xffffffffffffc3ec#64) (skipField3Spec A))
    (hUcCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName + 0x2714#64) ((unchunkedCt1SentMergeSpec A).inImage img))
    (hPolyEncCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName + 0xffffffffffffed10#64) ((polyEncoderMergeSpec A).inImage img))
    (hPolyDecCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName + 0xffffffffffffe984#64) ((polyDecoderMergeSpec A).inImage img)) :
    subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName) ((chunkedCt1SampledMergeSpec A).inImage img) := by
  apply subroutine_ok_inImage_of_withImgProp
  unfold withImgProp chunkedCt1SampledMergeSpec; wpp_init x s0
  replace hpc : s0.pc = (libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName := by
    simpa only [arm64_norm, chunkedCt1SampledMerge_fnOff] using hpc
  have hx0_wt : (s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = BitVec.ofNat 8 x.wt.toNat := by assumption
  have hpts_0 : optPolyEncoderPtsLen x.msg.sendingCt1 + x.bs.length < 2 ^ 56 := by assumption
  have hpolys_0 : optPolyEncoderPolysLen x.msg.sendingCt1 + x.bs.length < 2 ^ 56 := by assumption
  have hdec_0 : optPolyDecoderPtsLen x.msg.receivingEk + x.bs.length < 2 ^ 56 := by assumption
  have hbs_lt : x.bs.length < 2 ^ 63 := by omega
  conv => arg 6; ext sf P_f; rw [sepConj_assoc, satisfies_pure_sepConj]
  change SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s0 _ (WppPost (chunkedCt1SampledMergeSpec A) x R s0) (WppPanic R s0)
  apply SepWPp.elim_imgCallInvProp; intro himg0
  have herr0_exit := @ct1Sampled_err0_ret_exit b A H x R s0
  have hfrom_exit := @ct1Sampled_from_err_exit b A H hFromCall x R s0
  have hloop := @ct1Sampled_loop_ok b A H img hFromCall hPushCall hVarintCall hSkipCall hUcCall hPolyEncCall hPolyDecCall x R s0
  chunkedCt1SampledMerge_fetches b H 0 112; chunkedCt1SampledMerge_fetches b H 156 16
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName = entry; examples_hide_fetches
  by_cases hwt_ld : x.wt = .lengthDelimited
  · have h_1' : (s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = 2#8 := by rw [hx0_wt, hwt_ld]; rfl
    have hbeq := wt_beq_two_of_lengthDelimited h_1'
    have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = false := by simp only [bne, hbeq, Bool.not_true]
    have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = false := by
      rw [BytesMergeFacts.truncate32_zeroExtend64_and_255_eq, h_1']; decide
    have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = false := by
      revert h_1'; bv_bits
    apply SepWPp.of_sepWP_img (mid := entry + 0xffffffffffffdd44#64) himg0
    conv => arg 4; rw [stackAt_chunkedMerge s0.sp, chunkedBelow_leaf s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v19; apply SepWP.exists_elim; intro v20
    apply SepWP.exists_elim; intro v21; apply SepWP.exists_elim; intro v22
    apply SepWP.exists_elim; intro v23; apply SepWP.exists_elim; intro v24
    apply SepWP.exists_elim; intro v25; apply SepWP.exists_elim; intro v_lr; apply SepWP.exists_elim; intro v_fp
    wp_steps; wp_reach; intro himg1
    refine SepWPp.call_frame_keep (hinv := himg1) (x := ⟨x.bufRef, x.slot, x.ptr, x.bs⟩) (ret_pc := entry + 56#64) hVarintCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
      (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm]; rfl)
      hbs_lt (by sep_focus) (fun _ _ _ _ hex => allowPanic_not_exited hex)
      (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm]) hpan) ?_
    intro sm hpcm hrunm hspm hcsm himgm; simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
    cases hdv0 : decodeVarint x.bs with
    | none =>
      have hnone : (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto .lengthDelimited) x.msg x.bs 99).toOption = none := by
        rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_chunked_ct1Sampled_mergeField]
        simp [mergeMessageBin, codecWireTypeToProto, proto_decodeVarint_toOption, hdv0]
      rw [hwt_ld] at herr0_exit; apply SepWPp.of_sepWP (mid := entry + 124#64)
      conv => arg 4; simp only [decodeVarint2Spec, hdv0, sepConj_assoc, arm64_norm]
      apply SepWP.pure_elim; rintro ⟨hsm0, htrm, hsm1⟩
      apply SepWP.fold (chunkedBelow_leaf_entails s0.sp) (by sep_focus)
      apply SepWP.fold (chunkedCt1SampledPBCapAt_entails_pb A x.msgPtr x.bs.length x.msg) (by sep_focus)
      wp_steps; wp_reach
      apply SepWPp.weaken_pre (P' :=
        decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ memRegion (s0.sp - 128#64) 48 ∗
          chunkedBelow s0.sp ∗ ct1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs)
        (Entails.of_eq (by dsimp only [ct1SampledErrFrame, chunkedSavedRegs]; ac_rfl))
      exact herr0_exit hnone hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm]) (by simp only [arm64_norm]) hsm1 ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
    | some p =>
      rcases p with ⟨len, rest0⟩
      have hrest0_lt_bs : rest0.length < x.bs.length := decodeVarint_length hdv0
      have hrest0_le : rest0.length ≤ x.bs.length := Nat.le_of_lt hrest0_lt_bs
      have hrest0_lt : rest0.length < 2 ^ 63 := Nat.lt_of_lt_of_le hrest0_lt_bs (Nat.le_of_lt hbs_lt)
      have hrest0_suf : IsDropSuffix x.bs rest0 := decodeVarint_suffix hdv0
      let rest0Ptr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length)
      by_cases hlt_len : rest0.length < len.toNat
      · have hule := ule_len_of_lt hlt_len hrest0_lt
        have hnone : (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto .lengthDelimited) x.msg x.bs 99).toOption = none := by
          rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_chunked_ct1Sampled_mergeField]
          rcases hdv0_p : Proto.decodeVarint x.bs with e | ⟨len', rest0'⟩
          · have hdv0' : decodeVarint x.bs = none := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
            rw [hdv0] at hdv0'; nomatch hdv0'
          · have hdv0' : decodeVarint x.bs = some (len', rest0') := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
            rw [hdv0] at hdv0'; injection hdv0' with hpair; injection hpair with hlen hr0; subst hlen hr0
            simp [mergeMessageBin, codecWireTypeToProto, hdv0_p, Except.toOption, hlt_len]
        rw [hwt_ld] at hfrom_exit; apply SepWPp.of_sepWP (mid := entry + 108#64)
        conv => arg 4; simp only [decodeVarint2Spec, hdv0, sliceCursorAfter_eq_split hrest0_le hrest0_suf,
          sliceCursorAt, memRegion_48_split_128 s0.sp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm]
        apply SepWP.exists_elim; intro v_stk0; apply SepWP.pure_elim; rintro ⟨⟨hsm0, hsm1⟩, htrm⟩
        apply SepWP.fold (chunkedBelow_leaf_entails s0.sp) (by sep_focus)
        apply SepWP.fold (chunkedCt1SampledPBCapAt_entails_pb A x.msgPtr x.bs.length x.msg) (by sep_focus)
        wp_steps
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot rest0Ptr (BitVec.ofNat 64 rest0.length)) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus); wp_reach
        apply SepWPp.weaken_pre (P' :=
          ((s0.sp - 128#64) ↦₆₄ v_stk0) ∗ memRegion (s0.sp - 120#64) 40 ∗
            chunkedBelow s0.sp ∗ ct1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs)
          (Entails.of_eq (by dsimp only [ct1SampledErrFrame, chunkedSavedRegs]; ac_rfl))
        exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000007#64) hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm]) (by simp only [arm64_norm]) ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
      · have hule := ule_len_of_ge hlt_len hrest0_lt
        have hsub := bv_len_sub_limit hlt_len
        have hlim_lt : rest0.length - len.toNat < 2 ^ 63 := by omega
        have hres0 : (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto .lengthDelimited) x.msg x.bs 99).toOption =
            (mergeLoopBin V1State.Chunked.Ct1Sampled.mergeField (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 98).map
              (fun m' => (m', x.bs.drop (x.bs.length - (rest0.length - len.toNat)))) := by
          rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_chunked_ct1Sampled_mergeField]
          rcases hdv0_p : Proto.decodeVarint x.bs with e | ⟨len', rest0'⟩
          · have hdv0' : decodeVarint x.bs = none := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
            rw [hdv0] at hdv0'; nomatch hdv0'
          · have hdv0' : decodeVarint x.bs = some (len', rest0') := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
            rw [hdv0] at hdv0'; injection hdv0' with hpair; injection hpair with hlen hr0; subst hlen hr0
            have hdrop_eq : x.bs.drop (x.bs.length - (rest0.length - len.toNat)) = rest0.drop len.toNat := by
              (conv_rhs => rw [hrest0_suf, List.drop_drop]); congr 1; omega
            simp only [mergeMessageBin, codecWireTypeToProto, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hdv0_p, Except.toOption, hlt_len, hdrop_eq]
            rcases mergeLoopBin V1State.Chunked.Ct1Sampled.mergeField (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 98 with _ | m' <;> rfl
        rw [hwt_ld] at hloop; apply SepWPp.of_sepWP_img (mid := entry + 192#64) himgm
        conv => arg 4; simp only [decodeVarint2Spec, hdv0, sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt, sepConj_assoc, arm64_norm]
        apply SepWP.pure_elim; rintro ⟨⟨hsm0, hsm1⟩, htrm⟩
        apply SepWP.fold (chunkedBelow_leaf_entails s0.sp) (by sep_focus)
        apply SepWP.fold (chunkedCt1SampledPBCapAt_mono A x.msgPtr x.msg hrest0_le) (by sep_focus)
        wp_steps; wp_reach; intro himg2
        apply SepWPp.weaken_pre (P' := ct1SampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs rest0)
          (Entails.of_eq (by dsimp only [ct1SampledLoopPre, chunkedSavedRegs]; rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]; ac_rfl))
        exact hloop hsp_align hbs_lt hlim_lt rest0.length x.msg rest0 _ (Nat.le_refl _) hrest0_le hrest0_suf
          (by omega) (by omega) (by omega) hres0 (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm]) (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm]) (by simp only [arm64_norm, hsm1, hsub]) ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm], ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩⟩ himg2
  · have hbeq := wt_beq_two_of_ne_lengthDelimited hx0_wt hwt_ld
    have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = true := by simp only [bne, hbeq, Bool.not_false]
    have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = true := by
      rw [show BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) =
            BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 by bv_bits]; exact hbne1
    have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = true := by
      rw [show BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) =
            BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 by bv_bits]; exact hbne1
    have hnone : (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
      rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_chunked_ct1Sampled_mergeField]
      unfold mergeMessageBin; cases hwt_eq : x.wt <;> simp [hwt_eq, codecWireTypeToProto] at hwt_ld ⊢
    apply SepWPp.of_sepWP (mid := entry + 108#64)
    conv => arg 4; rw [stackAt_chunkedMerge s0.sp, sliceCursorAt, memRegion_48_wtErr128 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v19; apply SepWP.exists_elim; intro v20
    apply SepWP.exists_elim; intro v21; apply SepWP.exists_elim; intro v22
    apply SepWP.exists_elim; intro v23; apply SepWP.exists_elim; intro v24
    apply SepWP.exists_elim; intro v25; apply SepWP.exists_elim; intro v_lr; apply SepWP.exists_elim; intro v_fp
    apply SepWP.exists_elim; intro b_wt1; apply SepWP.exists_elim; intro b_wt0; apply SepWP.exists_elim; intro v_wt0
    wp_steps
    apply SepWP.fold (wtErr128_entails_memRegion40 s0.sp _ _) (by sep_focus)
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot x.ptr (BitVec.ofNat 64 x.bs.length)) (by sep_focus)
    apply SepWP.fold (chunkedCt1SampledPBCapAt_entails_pb A x.msgPtr x.bs.length x.msg) (by sep_focus)
    wp_reach
    apply SepWPp.weaken_pre (P' :=
      ((s0.sp - 128#64) ↦₆₄ v_wt0) ∗ memRegion (s0.sp - 120#64) 40 ∗
        chunkedBelow s0.sp ∗ ct1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs)
      (Entails.of_eq (by dsimp only [ct1SampledErrFrame, chunkedSavedRegs]; ac_rfl))
    exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000006#64) hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩

theorem chunkedCt1Sampled_merge_ok_of_fnAddr {b : BitVec 64} {A : RustAlloc} {H : String → Option (State → State)} {img : Obj.Image}
    (hFrom : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr decodeErrorFromName) (decodeErrorFromSpec A))
    (hPush : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr decodeErrorPushName) (decodeErrorPushSpec A))
    (hVarint : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr Varint.decodeVarint2Name) (decodeVarint2Spec A))
    (hSkip : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr skipField3Name) (skipField3Spec A))
    (hUc : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr unchunkedCt1SentMergeName) ((unchunkedCt1SentMergeSpec A).inImage img))
    (hPolyEnc : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr polyEncoderMergeName) ((polyEncoderMergeSpec A).inImage img))
    (hPolyDec : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName) ((polyDecoderMergeSpec A).inImage img)) :
    subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName) ((chunkedCt1SampledMergeSpec A).inImage img) := by
  have hFromCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName + 0xffffffffffffb618#64) (decodeErrorFromSpec A) := by
    rw [fnAddr_offset_eq_H (name := chunkedCt1SampledMergeName) (callee := decodeErrorFromName)]; exact hFrom
  have hPushCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName + 0xffffffffffffb320#64) (decodeErrorPushSpec A) := by
    rw [fnAddr_offset_eq_H (name := chunkedCt1SampledMergeName) (callee := decodeErrorPushName)]; exact hPush
  have hVarintCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName + 0xffffffffffffdd44#64) (decodeVarint2Spec A) := by
    rw [fnAddr_offset_eq_H (name := chunkedCt1SampledMergeName) (callee := Varint.decodeVarint2Name)]; exact hVarint
  have hSkipCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName + 0xffffffffffffc3ec#64) (skipField3Spec A) := by
    rw [fnAddr_offset_eq_H (name := chunkedCt1SampledMergeName) (callee := skipField3Name)]; exact hSkip
  have hUcCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName + 0x2714#64) ((unchunkedCt1SentMergeSpec A).inImage img) := by
    rw [fnAddr_offset_eq_H (name := chunkedCt1SampledMergeName) (callee := unchunkedCt1SentMergeName)]; exact hUc
  have hPolyEncCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName + 0xffffffffffffed10#64) ((polyEncoderMergeSpec A).inImage img) := by
    rw [fnAddr_offset_eq_H (name := chunkedCt1SampledMergeName) (callee := polyEncoderMergeName)]; exact hPolyEnc
  have hPolyDecCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr chunkedCt1SampledMergeName + 0xffffffffffffe984#64) ((polyDecoderMergeSpec A).inImage img) := by
    rw [fnAddr_offset_eq_H (name := chunkedCt1SampledMergeName) (callee := polyDecoderMergeName)]; exact hPolyDec
  exact chunkedCt1Sampled_merge_ok_of_contracts hFromCall hPushCall hVarintCall hSkipCall hUcCall hPolyEncCall hPolyDecCall

theorem chunkedCt1Sampled_merge_ok_ext {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)} (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext)
    (hBytes : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr bytesMerge3Name) ((bytesMerge3RawSpec A).inImage img))
    (hGrow : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr growOneVecU8Name) (growOneVecU8Spec A)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr chunkedCt1SampledMergeName) ((chunkedCt1SampledMergeSpec A).inImage img) :=
  chunkedCt1Sampled_merge_ok_of_fnAddr hC.decode_error_from hC.decode_error_push
    (decodeVarint2_ok_ext hC) (skipField3_ok_ext hC)
    (unchunkedCt1SentMerge_ok_ext hC hBytes)
    (polyEncoderMerge_ok_ext hC hBytes hGrow) (polyDecoderMerge_ok_ext hC hBytes hGrow)

theorem chunkedCt1Sampled_merge_ok_ext_of_bytes_contracts {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)} (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext)
    (hBC : BytesMerge3Contracts img A ext)
    (hGrow : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr growOneVecU8Name) (growOneVecU8Spec A)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr chunkedCt1SampledMergeName) ((chunkedCt1SampledMergeSpec A).inImage img) :=
  chunkedCt1Sampled_merge_ok_ext hC hBC.ok_ext hGrow

/-! ## 4. Relocatable `[LibsignalPlacement]` Verification (Block `300`) -/

section Placed

open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2

theorem ct1Sampled_err0_ret_exit_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    {x : ChunkedCt1SampledMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.Ct1Sampled} {err : BitVec 64}
    (hnone : (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_300).base + 124#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = err) (herr : err ≠ 0#64) (hcs : ChunkedHighCalleeSaved s0 s) :
    SepWPp ((blkPC_300).rebase (blkPl_300).base H) (s0.readReg64 Reg.lr) s
      (decodeErrorAtStackLen A err 0 ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedBelow s0.sp ∗
        ct1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (WppPost (chunkedCt1SampledMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
  apply SepWPp.of_sepWP_ret; unfold WppPost chunkedCt1SampledMergeSpec
  simp only [hnone, stackAt_chunkedMerge, ct1SampledErrFrame, chunkedSavedRegs,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp, hx1]
  apply SepWP.fold (decodeErrorWith_zero_entails_le3 A err) (by sep_focus)
  apply SepWP.fold (chunkedCt1SampledPBAt_entails_exists A x.msgPtr m) (by sep_focus)
  wp_steps; wp_done

theorem ct1Sampled_from_err_exit_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 261) (decodeErrorFromSpec A))
    {x : ChunkedCt1SampledMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.Ct1Sampled} {w v_stk0 : BitVec 64}
    (hnone : (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hw : KindNoHeap w) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_300).base + 108#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx8 : s.readReg64 (Reg.gpr 8#5) = w) (hcs : ChunkedHighCalleeSaved s0 s) :
    SepWPp ((blkPC_300).rebase (blkPl_300).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ v_stk0) ∗ memRegion (s0.sp - 120#64) 40 ∗ chunkedBelow s0.sp ∗
        ct1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (WppPost (chunkedCt1SampledMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
  apply SepWPp.of_sepWP (mid := lsmpl.base 261)
  conv => arg 4; rw [chunkedBelow_err s0.sp, ct1SampledErrFrame, chunkedSavedRegs]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPp.call_frame (x := (s0.sp - 128#64, w)) (ret_pc := (blkPl_300).base + 120#64) hFromCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorFromSpec]; simp only [arm64_norm, hsp, hx8]; rfl) hw (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, _, _, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx26, hx27, hx28, hvregs] at hpcm hspm hx26_m hx27_m hx28_m hvregs_m
  apply SepWPp.of_sepWP_ret; unfold WppPost chunkedCt1SampledMergeSpec
  simp only [decodeErrorFromSpec, hnone, stackAt_chunkedMerge,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp, hspm]
  apply SepWP.fold (chunkedBelow_err_entails s0.sp) (by sep_focus)
  wp_steps
  apply SepWP.fold (decodeErrorWith_zero_entails_le3 A _) (by sep_focus)
  apply SepWP.fold (chunkedCt1SampledPBAt_entails_exists A x.msgPtr m) (by sep_focus)
  apply SepWP.fold (memRegion8_memRegion40_entails_48_128 s0.sp) (by sep_focus)
  wp_done

theorem ct1Sampled_push_err_exit_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    {x : ChunkedCt1SampledMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.Ct1Sampled} {err : BitVec 64} {n : Nat}
    (hnone : (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (herr : err ≠ 0#64) (hn : n ≤ 2) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_300).base + 604#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = s0.sp - 128#64) (hcs : ChunkedHighCalleeSaved s0 s) :
    SepWPp ((blkPC_300).rebase (blkPl_300).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A err n ∗ memRegion (s0.sp - 120#64) 40 ∗
        chunkedBelow s0.sp ∗ ct1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (WppPost (chunkedCt1SampledMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
  apply SepWPp.of_sepWP (mid := lsmpl.base 257)
  conv => arg 4; rw [chunkedBelow_err s0.sp, ct1SampledErrFrame, chunkedSavedRegs]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPp.call_frame (x := (s0.sp - 128#64, err, n)) (ret_pc := (blkPl_300).base + 608#64) hPushCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorPushSpec]; simp only [arm64_norm, hsp, hx0]; rfl) (by omega : n < 2 ^ 32) (by sep_focus) (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, _, _, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx26, hx27, hx28, hvregs] at hpcm hspm hx26_m hx27_m hx28_m hvregs_m
  apply SepWPp.of_sepWP_ret; unfold WppPost chunkedCt1SampledMergeSpec
  simp only [decodeErrorPushSpec, hnone, stackAt_chunkedMerge,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp, hspm]
  apply SepWP.fold (chunkedBelow_err_entails s0.sp) (by sep_focus)
  wp_steps
  apply SepWP.fold (decodeErrorWith_succ_entails_le3 A err hn) (by sep_focus)
  apply SepWP.fold (chunkedCt1SampledPBAt_entails_exists A x.msgPtr m) (by sep_focus)
  apply SepWP.fold (pointsTo64_memRegion40_entails_48_128 s0.sp err) (by sep_focus)
  wp_done

theorem ct1Sampled_skip_step_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hSkipCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 263) (skipField3Spec A))
    {x : ChunkedCt1SampledMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.Ct1Sampled} {rest : List (BitVec 8)} {iwt : WireType} {tag limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest) (htag_lt : tag < 2 ^ 32)
    (hnone_of_sf : skipField (2 * rest.length + 2) 98 tag iwt rest = none →
      (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (rest' : List (BitVec 8)) (s' : State),
      skipField (2 * rest.length + 2) 98 tag iwt rest = some rest' →
      s'.pc = (blkPl_300).base + 192#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      ChunkedLoopRegs s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_300).rebase (blkPl_300).base H) (s0.readReg64 Reg.lr) s'
        (ct1SampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest') (WppPost (chunkedCt1SampledMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_300).base + 172#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : (s.readReg64 (Reg.gpr 1#5)).setWidth 32 = BitVec.ofNat 32 tag)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : ChunkedLoopRegs s0 s) (himg : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_300).rebase (blkPl_300).base H) (s0.readReg64 Reg.lr) s
      (ct1SampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest) (WppPost (chunkedCt1SampledMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have herr0_exit := @ct1Sampled_err0_ret_exit_placed _ A H x R s0
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 263) himg
  conv => arg 4; rw [ct1SampledLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf, chunkedBelow_skipField3_98 s0.sp]
  simp only [sepConj_assoc]; wp_steps; wp_reach; intro himg1
  refine SepWPp.call_frame_keep_lscro (hinv := himg1) (x := ⟨iwt, tag, 98, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := (blkPl_300).base + 184#64) hSkipCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [skipField3Spec]; simp only [arm64_norm, hsp, hx0, hx1, hx19, setWidth8_ofNat64_wt]; rfl)
    (⟨htag_lt, by decide, hrest_lt⟩ : tag < 2 ^ 32 ∧ 98 < 2 ^ 32 ∧ rest.length < 2 ^ 63) (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm himgm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m hvregs_m
  cases hsf : skipField (2 * rest.length + 2) 98 tag iwt rest with
  | none =>
    have hnone := hnone_of_sf hsf; apply SepWPp.of_sepWP (mid := (blkPl_300).base + 124#64)
    conv => arg 4; simp only [skipField3Spec, hsf, sepConj_assoc, arm64_norm, hsp]
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (chunkedBelow_skipField3_98_entails s0.sp) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (chunkedCt1SampledPBCapAt_entails_pb A x.msgPtr rest.length m) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPp.weaken_pre (P' :=
      decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ memRegion (s0.sp - 128#64) 48 ∗
        chunkedBelow s0.sp ∗ ct1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (Entails.of_eq (by dsimp only [ct1SampledErrFrame]; ac_rfl))
    exact herr0_exit hnone hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm]) hsm0 ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some rest' =>
    have hrest'_le : rest'.length ≤ rest.length := (skip_length _).1 _ _ _ _ _ hsf
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_300).base + 192#64) himgm
    conv => arg 4; simp only [skipField3Spec, hsf, sepConj_assoc, arm64_norm, hsp]
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    apply SepWP.fold (chunkedBelow_skipField3_98_entails s0.sp) (by sep_focus)
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (chunkedCt1SampledPBCapAt_mono A x.msgPtr m hrest'_le) (by sep_focus)
    wp_steps; wp_reach; intro himg2
    apply SepWPp.weaken_pre (P' := ct1SampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest')
      (Entails.of_eq (by dsimp only [ct1SampledLoopPre]; ac_rfl))
    exact hcont rest' _ hsf (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m]) ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m], ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩⟩ himg2

theorem ct1Sampled_tag1_init_step_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    {a v0 v19 v21 v22 : BitVec 64} {n : Nat} {opt : Option V1State.Unchunked.Ct1Sent}
    {F : SepProp} {s0 s : State} {post panic : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_300).base + 368#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = v0) (hx19 : s.readReg64 (Reg.gpr 19#5) = v19)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = a) (hx21 : s.readReg64 (Reg.gpr 21#5) = v21)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = v22) (hcs : ChunkedLoopRegs s0 s) (himg : LibsignalCodeRoLoaded lsmpl s.mem)
    (hcont : ∀ s' : State,
      s'.pc = (blkPl_300).base + 404#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = v0 → s'.readReg64 (Reg.gpr 19#5) = v19 →
      s'.readReg64 (Reg.gpr 20#5) = a → s'.readReg64 (Reg.gpr 21#5) = v21 →
      s'.readReg64 (Reg.gpr 22#5) = v22 → ChunkedLoopRegs s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_300).rebase (blkPl_300).base H) (s0.readReg64 Reg.lr) s'
        (unchunkedCt1SentPBCapAt A a n (opt.getD default) ∗ F) post panic) :
    SepWPp ((blkPC_300).rebase (blkPl_300).base H) (s0.readReg64 Reg.lr) s
      (optUnchunkedCt1SentPBCapAt A a n opt ∗ F) post panic := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  cases opt with
  | none =>
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_300).base + 404#64) himg
    conv => arg 4; rw [optUnchunkedCt1SentPBCapAt, memRegion_ct1Sent_none_split a]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro w120; apply SepWP.exists_elim; intro w72; apply SepWP.exists_elim; intro w64
    apply SepWP.exists_elim; intro w56; apply SepWP.exists_elim; intro w48; apply SepWP.exists_elim; intro w40
    apply SepWP.exists_elim; intro w32; apply SepWP.exists_elim; intro w24; apply SepWP.exists_elim; intro w16; apply SepWP.exists_elim; intro w8
    wp_steps; apply SepWP.fold (default_ct1Sent_entails_cap A a n) (by sep_focus); wp_reach; intro himg'
    exact hcont _ (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx0]) (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20]) (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22]) ⟨by simp only [arm64_norm, hx23], by simp only [arm64_norm, hx24], by simp only [arm64_norm, hx25], ⟨by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩⟩ himg'
  | some u =>
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_300).base + 404#64) himg
    conv => arg 4; rw [optUnchunkedCt1SentPBCapAt, unchunkedCt1SentPBCapAt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro cap_ct1; apply SepWP.exists_elim; intro ptr_ct1
    apply SepWP.exists_elim; intro cap_es; apply SepWP.exists_elim; intro ptr_es
    apply SepWP.exists_elim; intro cap_hdr; apply SepWP.exists_elim; intro ptr_hdr; apply SepWP.pure_elim; intro hcap_hdr
    conv => arg 4; rw [vecU8At_eq_header_sep_buf A a cap_hdr ptr_hdr u.hdr, vecHeader]; simp only [sepConj_assoc]
    apply SepWP.fold (vecU8Buf_entails_cap_lt A cap_hdr ptr_hdr u.hdr) (by sep_focus)
    wp_simp_pre [sepConj_assoc]; apply SepWP.pure_elim; intro hcap_lt
    have hcmn1 := cap_add_one_beq_zero_false hcap_lt; have hcmn2 := cap_add_one_bne_zero_true hcap_lt; wp_steps
    have hfold_hdr : (a ↦₆₄ cap_hdr) ∗ ((a + 8#64) ↦₆₄ ptr_hdr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 u.hdr.length) ∗ vecU8Buf A cap_hdr ptr_hdr u.hdr ⊢
        (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap n⌝ ∗ vecU8At A a cap ptr u.hdr) := by
      refine Entails.trans ?_ (Entails.sepExists_right cap_hdr (Entails.sepExists_right ptr_hdr (Entails.refl _)))
      refine Entails.pure_right hcap_hdr ?_; rw [vecU8At_eq_header_sep_buf, vecHeader]; exact Entails.of_eq (by ac_rfl)
    have hfold_es : ⌜BytesMergeCapOk cap_es n⌝ ∗ vecU8At A (a + 24#64) cap_es ptr_es u.es ⊢
        (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap n⌝ ∗ vecU8At A (a + 24#64) cap ptr u.es) :=
      Entails.sepExists_right cap_es (Entails.sepExists_right ptr_es (Entails.refl _))
    have hfold_ct1 : ⌜BytesMergeCapOk cap_ct1 n⌝ ∗ vecU8At A (a + 48#64) cap_ct1 ptr_ct1 u.ct1 ⊢
        (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap n⌝ ∗ vecU8At A (a + 48#64) cap ptr u.ct1) :=
      Entails.sepExists_right cap_ct1 (Entails.sepExists_right ptr_ct1 (Entails.refl _))
    apply SepWP.fold hfold_hdr (by sep_focus); apply SepWP.fold hfold_es (by sep_focus); apply SepWP.fold hfold_ct1 (by sep_focus); wp_reach; intro himg'
    apply SepWPp.weaken_pre (P' := unchunkedCt1SentPBCapAt A a n u ∗ F)
      (Entails.of_eq (by dsimp only [unchunkedCt1SentPBCapAt]; ac_rfl))
    exact hcont _ (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx0]) (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20]) (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22]) ⟨by simp only [arm64_norm, hx23], by simp only [arm64_norm, hx24], by simp only [arm64_norm, hx25], ⟨by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩⟩ himg'

set_option maxHeartbeats 800000 in
theorem ct1Sampled_tag1_step_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hUcCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 312) (withLsCodeRoLoaded lsmpl (unchunkedCt1SentMergeSpec A)))
    (hPushCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    {x : ChunkedCt1SampledMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.Ct1Sampled} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_uc :
      (Proto.mergeMessage V1State.Unchunked.Ct1Sent.mergeField (codecWireTypeToProto iwt) (m.uc.getD default) rest 98).toOption = none →
      (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (u' : V1State.Unchunked.Ct1Sent) (rest' : List (BitVec 8)) (s' : State),
      (Proto.mergeMessage V1State.Unchunked.Ct1Sent.mergeField (codecWireTypeToProto iwt) (m.uc.getD default) rest 98).toOption = some (u', rest') →
      s'.pc = (blkPl_300).base + 192#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      ChunkedLoopRegs s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_300).rebase (blkPl_300).base H) (s0.readReg64 Reg.lr) s'
        (ct1SampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with uc := some u' } x.bs rest') (WppPost (chunkedCt1SampledMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_300).base + 368#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : ChunkedLoopRegs s0 s) (himg : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_300).rebase (blkPl_300).base H) (s0.readReg64 Reg.lr) s
      (ct1SampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest) (WppPost (chunkedCt1SampledMergeSpec A) x R s0) (WppPanic R s0) := by
  apply SepWPp.weaken_pre (P' :=
    optUnchunkedCt1SentPBCapAt A x.msgPtr rest.length m.uc ∗
      (optPolynomialEncoderPBAt A (x.msgPtr + 128#64) m.sendingCt1 ∗
        optPolynomialDecoderPBAt A (x.msgPtr + 184#64) m.receivingEk ∗ (x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedBelow s0.sp ∗ chunkedSavedRegs s0))
    (Entails.of_eq (by dsimp only [ct1SampledLoopPre, chunkedCt1SampledPBCapAt]; ac_rfl))
  refine ct1Sampled_tag1_init_step_placed hpc hrun hsp htr hx0 hx19 hx20 hx21 hx22 hcs himg ?_
  clear hpc hrun hsp htr hx0 hx19 hx20 hx21 hx22 hcs himg s
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hx21_1 hx22_1 hcs1 himg1
  obtain ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1⟩ := hcs1
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hpush_exit := @ct1Sampled_push_err_exit_placed _ A H hPushCall x R s0
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 312) himg1
  conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, chunkedBelow_eq_unchunked s0.sp]
  simp only [sepConj_assoc]; wp_steps; wp_reach; intro himg2
  refine SepWPp.call_frame_lscro (hinv := himg2) (x := ⟨iwt, x.msgPtr, m.uc.getD default, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := (blkPl_300).base + 416#64) hUcCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
    (by simp only [State.spAligned, hsp1, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [unchunkedCt1SentMergeSpec]; simp only [arm64_norm, hsp1, hx0_1, hx20_1, hx19_1, setWidth8_ofNat64_wt]; rfl)
    (⟨rfl, rfl, rfl, hrest_lt⟩ : BitVec.ofNat 8 iwt.toNat = BitVec.ofNat 8 iwt.toNat ∧ x.msgPtr = x.msgPtr ∧ x.bufRef = x.bufRef ∧ rest.length < 2 ^ 63) (by sep_focus) (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [unchunkedCt1SentMergeSpec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr1]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm himgm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m hvregs_m
  cases huc_res : (Proto.mergeMessage V1State.Unchunked.Ct1Sent.mergeField (codecWireTypeToProto iwt) (m.uc.getD default) rest 98).toOption with
  | none =>
    have hnone := hnone_of_uc huc_res; apply SepWPp.of_sepWP (mid := (blkPl_300).base + 604#64)
    conv => arg 4; simp only [unchunkedCt1SentMergeSpec, huc_res, memRegion_48_split_128 s0.sp,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp1]
    apply SepWP.exists_elim; intro v_stk0; apply SepWP.exists_elim; intro u'; apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hn_err⟩
    have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus); wp_steps; wp_reach
    apply SepWPp.weaken_pre (P' :=
      ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
        memRegion (s0.sp - 120#64) 40 ∗ chunkedBelow s0.sp ∗
        ct1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { m with uc := some u' } x.bs)
      (Entails.of_eq (by dsimp only [ct1SampledErrFrame, chunkedCt1SampledPBAt, optCt1SentPBAt, chunkedBelow]; ac_rfl))
    exact hpush_exit hnone hsm0 hn_err hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr1]) (by simp only [arm64_norm, hspm]) ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨u', rest'⟩
    have hrest'_le : rest'.length ≤ rest.length := proto_mergeMessage_len_le huc_res
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_300).base + 192#64) himgm
    conv => arg 4; simp only [unchunkedCt1SentMergeSpec, huc_res, sepConj_assoc, arm64_norm, hsp1]
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus); wp_steps; wp_reach; intro himg3
    apply SepWPp.weaken_pre (P' := ct1SampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with uc := some u' } x.bs rest')
      (Entails.of_eq (by dsimp only [ct1SampledLoopPre, chunkedCt1SampledPBCapAt, optUnchunkedCt1SentPBCapAt, chunkedBelow]; ac_rfl))
    exact hcont u' rest' _ huc_res (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr1]) (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m]) ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m], ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩⟩ himg3

theorem ct1Sampled_tag2_init_step_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    {a v0 v19 v21 v22 : BitVec 64} {opt : Option PolynomialEncoder} {F : SepProp} {s0 s : State} {post panic : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_300).base + 316#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = v0) (hx19 : s.readReg64 (Reg.gpr 19#5) = v19)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = a) (hx21 : s.readReg64 (Reg.gpr 21#5) = v21)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = v22) (hcs : ChunkedLoopRegs s0 s) (himg : LibsignalCodeRoLoaded lsmpl s.mem)
    (hcont : ∀ s' : State,
      s'.pc = (blkPl_300).base + 344#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = v0 → s'.readReg64 (Reg.gpr 19#5) = v19 →
      s'.readReg64 (Reg.gpr 20#5) = a → s'.readReg64 (Reg.gpr 21#5) = v21 →
      s'.readReg64 (Reg.gpr 22#5) = v22 → ChunkedLoopRegs s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_300).rebase (blkPl_300).base H) (s0.readReg64 Reg.lr) s'
        (polynomialEncoderPBAt A (a + 128#64) (opt.getD default) ∗ F) post panic) :
    SepWPp ((blkPC_300).rebase (blkPl_300).base H) (s0.readReg64 Reg.lr) s
      (optPolynomialEncoderPBAt A (a + 128#64) opt ∗ F) post panic := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  cases opt with
  | none =>
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_300).base + 344#64) himg
    conv => arg 4; rw [optPolynomialEncoderPBAt, memRegion_polyEncoder_none_split (a + 128#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro w48; apply SepWP.exists_elim; intro w40
    apply SepWP.exists_elim; intro w32; apply SepWP.exists_elim; intro w24
    apply SepWP.exists_elim; intro w16; apply SepWP.exists_elim; intro w8; wp_steps
    apply SepWP.fold (default_polyEncoder_entails_pb A (a + 128#64)) (by sep_focus); wp_reach; intro himg'
    exact hcont _ (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx0]) (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20]) (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22]) ⟨by simp only [arm64_norm, hx23], by simp only [arm64_norm, hx24], by simp only [arm64_norm, hx25], ⟨by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩⟩ himg'
  | some pe =>
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_300).base + 344#64) himg
    conv => arg 4; rw [optPolynomialEncoderPBAt, polynomialEncoderPBAt, vecVecU8At_eq_exists_pin A (a + 128#64) pe.pts]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro pin
    conv => arg 4; rw [vecVecU8PinnedAt_eq_header_buf]; simp only [sepConj_assoc]
    apply SepWP.fold (vecVecU8Buf_entails_cap_lt A pin.cap pin.ptr pe.pts) (by sep_focus)
    wp_simp_pre [sepConj_assoc]; apply SepWP.pure_elim; intro hcap_lt
    have hcmn1 := cap_add_one_beq_zero_false hcap_lt; have hcmn2 := cap_add_one_bne_zero_true hcap_lt; wp_steps
    have hfold_pts : ((a + 128#64) ↦₆₄ pin.cap) ∗ ((a + 128#64 + 8#64) ↦₆₄ pin.ptr) ∗
        ((a + 128#64 + 16#64) ↦₆₄ BitVec.ofNat 64 pe.pts.length) ∗ vecVecU8Buf A pin.cap pin.ptr pe.pts ⊢
        vecVecU8At A (a + 128#64) pe.pts := by
      rw [vecVecU8At_eq_exists_pin]; refine Entails.trans ?_ (Entails.sepExists_right pin (Entails.refl _))
      rw [vecVecU8PinnedAt_eq_header_buf]; exact Entails.of_eq (by ac_rfl)
    apply SepWP.fold hfold_pts (by sep_focus); wp_reach; intro himg'
    apply SepWPp.weaken_pre (P' := polynomialEncoderPBAt A (a + 128#64) pe ∗ F)
      (Entails.of_eq (by dsimp only [polynomialEncoderPBAt]; ac_rfl))
    exact hcont _ (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx0]) (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20]) (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22]) ⟨by simp only [arm64_norm, hx23], by simp only [arm64_norm, hx24], by simp only [arm64_norm, hx25], ⟨by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩⟩ himg'

set_option maxHeartbeats 800000 in
theorem ct1Sampled_tag2_step_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hPolyEncCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 297) (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A)))
    (hPushCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    {x : ChunkedCt1SampledMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.Ct1Sampled} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length) (hrest_suf : IsDropSuffix x.bs rest)
    (hpts_lt : optPolyEncoderPtsLen m.sendingCt1 + rest.length < 2 ^ 56)
    (hpolys_lt : optPolyEncoderPolysLen m.sendingCt1 + rest.length < 2 ^ 56)
    (hnone_of_pe :
      (Proto.mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto iwt) (m.sendingCt1.getD default) rest 98).toOption = none →
      (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (pe' : PolynomialEncoder) (rest' : List (BitVec 8)) (s' : State),
      (Proto.mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto iwt) (m.sendingCt1.getD default) rest 98).toOption = some (pe', rest') →
      s'.pc = (blkPl_300).base + 192#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      ChunkedLoopRegs s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_300).rebase (blkPl_300).base H) (s0.readReg64 Reg.lr) s'
        (ct1SampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with sendingCt1 := some pe' } x.bs rest') (WppPost (chunkedCt1SampledMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_300).base + 316#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : ChunkedLoopRegs s0 s) (himg : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_300).rebase (blkPl_300).base H) (s0.readReg64 Reg.lr) s
      (ct1SampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest) (WppPost (chunkedCt1SampledMergeSpec A) x R s0) (WppPanic R s0) := by
  apply SepWPp.weaken_pre (P' :=
    optPolynomialEncoderPBAt A (x.msgPtr + 128#64) m.sendingCt1 ∗
      (optUnchunkedCt1SentPBCapAt A x.msgPtr rest.length m.uc ∗
        optPolynomialDecoderPBAt A (x.msgPtr + 184#64) m.receivingEk ∗ (x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedBelow s0.sp ∗ chunkedSavedRegs s0))
    (Entails.of_eq (by dsimp only [ct1SampledLoopPre, chunkedCt1SampledPBCapAt]; ac_rfl))
  refine ct1Sampled_tag2_init_step_placed hpc hrun hsp htr hx0 hx19 hx20 hx21 hx22 hcs himg ?_
  clear hpc hrun hsp htr hx0 hx19 hx20 hx21 hx22 hcs himg s
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hx21_1 hx22_1 hcs1 himg1
  obtain ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1⟩ := hcs1
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hpush_exit := @ct1Sampled_push_err_exit_placed _ A H hPushCall x R s0
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 297) himg1
  conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, ← protoPolynomialEncoderAt_eq_pb, chunkedBelow_eq_poly s0.sp]
  simp only [sepConj_assoc]; wp_steps; wp_reach; intro himg2
  refine SepWPp.call_frame_lscro (hinv := himg2) (x := ⟨iwt, x.msgPtr + 128#64, m.sendingCt1.getD default, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := (blkPl_300).base + 356#64) hPolyEncCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
    (by simp only [State.spAligned, hsp1, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [polyEncoderMergeSpec]; simp only [arm64_norm, hsp1, hx0_1, hx20_1, hx19_1, setWidth8_ofNat64_wt, optPolyEncoder_getD_default_pts_len, optPolyEncoder_getD_default_polys_len]; rfl)
    (⟨rfl, rfl, rfl, hpts_lt, hpolys_lt⟩ : BitVec.ofNat 8 iwt.toNat = BitVec.ofNat 8 iwt.toNat ∧ x.msgPtr + 128#64 = x.msgPtr + 128#64 ∧ x.bufRef = x.bufRef ∧ optPolyEncoderPtsLen m.sendingCt1 + rest.length < 2 ^ 56 ∧ optPolyEncoderPolysLen m.sendingCt1 + rest.length < 2 ^ 56) (by sep_focus) (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [polyEncoderMergeSpec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr1]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm himgm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m hvregs_m
  cases hpe_res : (Proto.mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto iwt) (m.sendingCt1.getD default) rest 98).toOption with
  | none =>
    have hnone := hnone_of_pe hpe_res; apply SepWPp.of_sepWP (mid := (blkPl_300).base + 604#64)
    conv => arg 4; simp only [polyEncoderMergeSpec, hpe_res, protoPolynomialEncoderAt_eq_pb,
      memRegion_48_split_128 s0.sp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp1]
    apply SepWP.exists_elim; intro v_stk0; apply SepWP.exists_elim; intro pe'; apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hn_err⟩
    have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (optUnchunkedCt1SentPBCapAt_entails_optCt1SentPBAt A x.msgPtr rest.length m.uc) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPp.weaken_pre (P' :=
      ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
        memRegion (s0.sp - 120#64) 40 ∗ chunkedBelow s0.sp ∗
        ct1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { m with sendingCt1 := some pe' } x.bs)
      (Entails.of_eq (by dsimp only [ct1SampledErrFrame, chunkedCt1SampledPBAt, optPolynomialEncoderPBAt, chunkedBelow, unchunkedMergeStack, polyMergeStack, authMergeStack, polyBelowStack]; ac_rfl))
    exact hpush_exit hnone hsm0 (by omega : n_err ≤ 2) hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr1]) (by simp only [arm64_norm, hspm]) ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨pe', rest'⟩
    have hrest'_le : rest'.length ≤ rest.length := proto_mergeMessage_len_le hpe_res
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_300).base + 192#64) himgm
    conv => arg 4; simp only [polyEncoderMergeSpec, hpe_res, protoPolynomialEncoderAt_eq_pb, sepConj_assoc, arm64_norm, hsp1]
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (optUnchunkedCt1SentPBCapAt_mono A x.msgPtr m.uc hrest'_le) (by sep_focus)
    wp_steps; wp_reach; intro himg3
    apply SepWPp.weaken_pre (P' := ct1SampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with sendingCt1 := some pe' } x.bs rest')
      (Entails.of_eq (by dsimp only [ct1SampledLoopPre, chunkedCt1SampledPBCapAt, optPolynomialEncoderPBAt, chunkedBelow, unchunkedMergeStack, polyMergeStack, authMergeStack, polyBelowStack]; ac_rfl))
    exact hcont pe' rest' _ hpe_res (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr1]) (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m]) ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m], ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩⟩ himg3

theorem ct1Sampled_tag3_init_step_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    {a v0 v19 v21 v22 : BitVec 64} {opt : Option PolynomialDecoder} {F : SepProp} {s0 s : State} {post panic : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_300).base + 268#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = v0) (hx19 : s.readReg64 (Reg.gpr 19#5) = v19)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = a) (hx21 : s.readReg64 (Reg.gpr 21#5) = v21)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = v22) (hcs : ChunkedLoopRegs s0 s) (himg : LibsignalCodeRoLoaded lsmpl s.mem)
    (hcont : ∀ s' : State,
      s'.pc = (blkPl_300).base + 292#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = v0 → s'.readReg64 (Reg.gpr 19#5) = v19 →
      s'.readReg64 (Reg.gpr 20#5) = a → s'.readReg64 (Reg.gpr 21#5) = v21 →
      s'.readReg64 (Reg.gpr 22#5) = v22 → ChunkedLoopRegs s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_300).rebase (blkPl_300).base H) (s0.readReg64 Reg.lr) s'
        (polynomialDecoderPBAt A (a + 184#64) (opt.getD default) ∗ F) post panic) :
    SepWPp ((blkPC_300).rebase (blkPl_300).base H) (s0.readReg64 Reg.lr) s
      (optPolynomialDecoderPBAt A (a + 184#64) opt ∗ F) post panic := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  cases opt with
  | none =>
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_300).base + 292#64) himg
    conv => arg 4; rw [optPolynomialDecoderPBAt, memRegion_polyDecoder_none_split (a + 184#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro w32; apply SepWP.exists_elim; intro w24
    apply SepWP.exists_elim; intro w16; apply SepWP.exists_elim; intro w8; wp_steps
    apply SepWP.fold (default_polyDecoder_entails_pb A (a + 184#64)) (by sep_focus); wp_reach; intro himg'
    exact hcont _ (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx0]) (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20]) (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22]) ⟨by simp only [arm64_norm, hx23], by simp only [arm64_norm, hx24], by simp only [arm64_norm, hx25], ⟨by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩⟩ himg'
  | some pe =>
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_300).base + 292#64) himg
    conv => arg 4; rw [optPolynomialDecoderPBAt, polynomialDecoderPBAt, vecVecU8At_eq_exists_pin A (a + 184#64) pe.pts]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro pin
    conv => arg 4; rw [vecVecU8PinnedAt_eq_header_buf]; simp only [sepConj_assoc]
    apply SepWP.fold (vecVecU8Buf_entails_cap_lt A pin.cap pin.ptr pe.pts) (by sep_focus)
    wp_simp_pre [sepConj_assoc]; apply SepWP.pure_elim; intro hcap_lt
    have hcmn1 := cap_add_one_beq_zero_false hcap_lt; have hcmn2 := cap_add_one_bne_zero_true hcap_lt; wp_steps
    have hfold_pts : ((a + 184#64) ↦₆₄ pin.cap) ∗ ((a + 184#64 + 8#64) ↦₆₄ pin.ptr) ∗
        ((a + 184#64 + 16#64) ↦₆₄ BitVec.ofNat 64 pe.pts.length) ∗ vecVecU8Buf A pin.cap pin.ptr pe.pts ⊢
        vecVecU8At A (a + 184#64) pe.pts := by
      rw [vecVecU8At_eq_exists_pin]; refine Entails.trans ?_ (Entails.sepExists_right pin (Entails.refl _))
      rw [vecVecU8PinnedAt_eq_header_buf]; exact Entails.of_eq (by ac_rfl)
    apply SepWP.fold hfold_pts (by sep_focus); wp_reach; intro himg'
    apply SepWPp.weaken_pre (P' := polynomialDecoderPBAt A (a + 184#64) pe ∗ F)
      (Entails.of_eq (by dsimp only [polynomialDecoderPBAt]; ac_rfl))
    exact hcont _ (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx0]) (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20]) (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22]) ⟨by simp only [arm64_norm, hx23], by simp only [arm64_norm, hx24], by simp only [arm64_norm, hx25], ⟨by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩⟩ himg'

set_option maxHeartbeats 800000 in
theorem ct1Sampled_tag3_step_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hPolyDecCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 296) (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A)))
    (hPushCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    {x : ChunkedCt1SampledMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.Ct1Sampled} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length) (hrest_suf : IsDropSuffix x.bs rest)
    (hpts_lt : optPolyDecoderPtsLen m.receivingEk + rest.length < 2 ^ 56)
    (hnone_of_pd :
      (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto iwt) (m.receivingEk.getD default) rest 98).toOption = none →
      (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (pd' : PolynomialDecoder) (rest' : List (BitVec 8)) (s' : State),
      (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto iwt) (m.receivingEk.getD default) rest 98).toOption = some (pd', rest') →
      s'.pc = (blkPl_300).base + 192#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      ChunkedLoopRegs s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_300).rebase (blkPl_300).base H) (s0.readReg64 Reg.lr) s'
        (ct1SampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with receivingEk := some pd' } x.bs rest') (WppPost (chunkedCt1SampledMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_300).base + 268#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : ChunkedLoopRegs s0 s) (himg : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_300).rebase (blkPl_300).base H) (s0.readReg64 Reg.lr) s
      (ct1SampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest) (WppPost (chunkedCt1SampledMergeSpec A) x R s0) (WppPanic R s0) := by
  apply SepWPp.weaken_pre (P' :=
    optPolynomialDecoderPBAt A (x.msgPtr + 184#64) m.receivingEk ∗
      (optUnchunkedCt1SentPBCapAt A x.msgPtr rest.length m.uc ∗
        optPolynomialEncoderPBAt A (x.msgPtr + 128#64) m.sendingCt1 ∗ (x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedBelow s0.sp ∗ chunkedSavedRegs s0))
    (Entails.of_eq (by dsimp only [ct1SampledLoopPre, chunkedCt1SampledPBCapAt]; ac_rfl))
  refine ct1Sampled_tag3_init_step_placed hpc hrun hsp htr hx0 hx19 hx20 hx21 hx22 hcs himg ?_
  clear hpc hrun hsp htr hx0 hx19 hx20 hx21 hx22 hcs himg s
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hx21_1 hx22_1 hcs1 himg1
  obtain ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1⟩ := hcs1
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hpush_exit := @ct1Sampled_push_err_exit_placed _ A H hPushCall x R s0
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 296) himg1
  conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, ← protoPolynomialDecoderAt_eq_pb, chunkedBelow_eq_poly s0.sp]
  simp only [sepConj_assoc]; wp_steps; wp_reach; intro himg2
  refine SepWPp.call_frame_lscro (hinv := himg2) (x := ⟨iwt, x.msgPtr + 184#64, m.receivingEk.getD default, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := (blkPl_300).base + 304#64) hPolyDecCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
    (by simp only [State.spAligned, hsp1, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [polyDecoderMergeSpec]; simp only [arm64_norm, hsp1, hx0_1, hx20_1, hx19_1, setWidth8_ofNat64_wt, optPolyDecoder_getD_default_pts_len]; rfl)
    (⟨rfl, rfl, rfl, hpts_lt⟩ : BitVec.ofNat 8 iwt.toNat = BitVec.ofNat 8 iwt.toNat ∧ x.msgPtr + 184#64 = x.msgPtr + 184#64 ∧ x.bufRef = x.bufRef ∧ optPolyDecoderPtsLen m.receivingEk + rest.length < 2 ^ 56) (by sep_focus) (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [polyDecoderMergeSpec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr1]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm himgm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m hvregs_m
  cases hpd_res : (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto iwt) (m.receivingEk.getD default) rest 98).toOption with
  | none =>
    have hnone := hnone_of_pd hpd_res; apply SepWPp.of_sepWP (mid := (blkPl_300).base + 604#64)
    conv => arg 4; simp only [polyDecoderMergeSpec, hpd_res, protoPolynomialDecoderAt_eq_pb,
      memRegion_48_split_128 s0.sp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp1]
    apply SepWP.exists_elim; intro v_stk0; apply SepWP.exists_elim; intro pd'; apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hn_err⟩
    have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (optUnchunkedCt1SentPBCapAt_entails_optCt1SentPBAt A x.msgPtr rest.length m.uc) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPp.weaken_pre (P' :=
      ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
        memRegion (s0.sp - 120#64) 40 ∗ chunkedBelow s0.sp ∗
        ct1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { m with receivingEk := some pd' } x.bs)
      (Entails.of_eq (by dsimp only [ct1SampledErrFrame, chunkedCt1SampledPBAt, optPolynomialDecoderPBAt, chunkedBelow, unchunkedMergeStack, polyMergeStack, authMergeStack, polyBelowStack]; ac_rfl))
    exact hpush_exit hnone hsm0 (by omega : n_err ≤ 2) hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr1]) (by simp only [arm64_norm, hspm]) ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨pd', rest'⟩
    have hrest'_le : rest'.length ≤ rest.length := proto_mergeMessage_len_le hpd_res
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_300).base + 192#64) himgm
    conv => arg 4; simp only [polyDecoderMergeSpec, hpd_res, protoPolynomialDecoderAt_eq_pb, sepConj_assoc, arm64_norm, hsp1]
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (optUnchunkedCt1SentPBCapAt_mono A x.msgPtr m.uc hrest'_le) (by sep_focus)
    wp_steps; wp_reach; intro himg3
    apply SepWPp.weaken_pre (P' := ct1SampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with receivingEk := some pd' } x.bs rest')
      (Entails.of_eq (by dsimp only [ct1SampledLoopPre, chunkedCt1SampledPBCapAt, optPolynomialDecoderPBAt, chunkedBelow, unchunkedMergeStack, polyMergeStack, authMergeStack, polyBelowStack]; ac_rfl))
    exact hcont pd' rest' _ hpd_res (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr1]) (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m]) ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m], ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩⟩ himg3

theorem ct1Sampled_loop_le_exit_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 261) (decodeErrorFromSpec A))
    {x : ChunkedCt1SampledMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.Ct1Sampled} {cur : List (BitVec 8)} {limit : Nat}
    (hle_lim : cur.length ≤ limit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_suf : IsDropSuffix x.bs cur) (hlim_lt : limit < 2 ^ 63)
    (hres_cur : (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
      (mergeLoopBin V1State.Chunked.Ct1Sampled.mergeField (cur.length - limit) m cur limit 98).map
        (fun m' => (m', x.bs.drop (x.bs.length - limit))))
    (hpc : s.pc = (blkPl_300).base + 192#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit) (hcs : ChunkedLoopRegs s0 s) :
    SepWPp ((blkPC_300).rebase (blkPl_300).base H) (s0.readReg64 Reg.lr) s
      (ct1SampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs cur) (WppPost (chunkedCt1SampledMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  by_cases heq_lim : cur.length = limit
  · obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq heq_lim
    have hcur_eq_drop : x.bs.drop (x.bs.length - limit) = cur := by rw [← heq_lim]; exact hcur_suf.symm
    have hsome : (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
        some (m, cur) := by
      rw [hres_cur, mergeLoopBin_eq_limit _ _ _ _ _ _ heq_lim, Option.map_some, hcur_eq_drop]
    apply SepWPp.of_sepWP_ret; unfold WppPost chunkedCt1SampledMergeSpec
    simp only [hsome, stackAt_chunkedMerge, ct1SampledLoopPre, chunkedSavedRegs,
      sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp]
    wp_steps; wp_done
  · have hlt_lim : cur.length < limit := Nat.lt_of_le_of_ne hle_lim heq_lim
    obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_lt hlt_lim hlim_lt
    have hnone : (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
      rw [hres_cur, mergeLoopBin_lt_limit _ _ _ _ _ _ hlt_lim, Option.map_none]
    have hfrom_exit := @ct1Sampled_from_err_exit_placed _ A H hFromCall x R s0
    apply SepWPp.of_sepWP (mid := (blkPl_300).base + 108#64)
    conv => arg 4; rw [ct1SampledLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
      sliceCursorAt, memRegion_48_split_128 s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v_stk0; wp_steps
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot curPtr (BitVec.ofNat 64 cur.length)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    apply SepWP.fold (chunkedCt1SampledPBCapAt_entails_pb A x.msgPtr cur.length m) (by sep_focus)
    wp_reach
    apply SepWPp.weaken_pre (P' :=
      ((s0.sp - 128#64) ↦₆₄ v_stk0) ∗ memRegion (s0.sp - 120#64) 40 ∗
        chunkedBelow s0.sp ∗ ct1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (Entails.of_eq (by dsimp only [ct1SampledErrFrame]; ac_rfl))
    exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000008#64) hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr]) (by simp only [arm64_norm]) ⟨by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩

theorem ct1Sampled_decode_key_step_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 261) (decodeErrorFromSpec A))
    (hVarintCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 291) (decodeVarint2Spec A))
    {x : ChunkedCt1SampledMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.Ct1Sampled} {cur : List (BitVec 8)} {limit : Nat}
    (hgt_lim : ¬ cur.length ≤ limit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_lt : cur.length < 2 ^ 63) (hcur_suf : IsDropSuffix x.bs cur)
    (hres_cur : (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
      (mergeLoopBin V1State.Chunked.Ct1Sampled.mergeField (cur.length - limit) m cur limit 98).map
        (fun m' => (m', x.bs.drop (x.bs.length - limit))))
    (hcont : ∀ (key : BitVec 64) (iwt : WireType) (rest : List (BitVec 8)) (s' : State),
      decodeVarint cur = some (key, rest) → ¬ 2 ^ 32 ≤ key.toNat →
      WireType.ofNat? (key.toNat % 8) = some iwt → ¬ key.toNat / 8 < 1 →
      s'.pc = (blkPl_300).base + 244#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      ChunkedLoopRegs s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_300).rebase (blkPl_300).base H) (s0.readReg64 Reg.lr) s'
        (ct1SampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest) (WppPost (chunkedCt1SampledMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_300).base + 192#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : ChunkedLoopRegs s0 s) (himg : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_300).rebase (blkPl_300).base H) (s0.readReg64 Reg.lr) s
      (ct1SampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs cur) (WppPost (chunkedCt1SampledMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  have herr0_exit := @ct1Sampled_err0_ret_exit_placed _ A H x R s0
  have hfrom_exit := @ct1Sampled_from_err_exit_placed _ A H hFromCall x R s0
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 291) himg
  conv => arg 4; rw [ct1SampledLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt, chunkedBelow_leaf s0.sp]
  simp only [sepConj_assoc]; wp_steps; wp_reach; intro himg1
  refine SepWPp.call_frame_keep_lscro (hinv := himg1) (x := ⟨x.bufRef, x.slot, curPtr, cur⟩) (ret_pc := (blkPl_300).base + 212#64) hVarintCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, hsp, hx19]; rfl)
    hcur_lt (by dsimp only [sliceCursorAt, curPtr]; sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm himgm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m hvregs_m
  cases hd : decodeVarint cur with
  | none =>
    have hnone : (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
      rw [hres_cur, mergeLoopBin_of_decodeVarint_none protoPrefixStep_chunked_ct1Sampled_mergeField hgt_lim hd, Option.map_none]
    apply SepWPp.of_sepWP (mid := (blkPl_300).base + 124#64)
    conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
    apply SepWP.fold (chunkedBelow_leaf_entails s0.sp) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    apply SepWP.fold (chunkedCt1SampledPBCapAt_entails_pb A x.msgPtr cur.length m) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPp.weaken_pre (P' :=
      decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ memRegion (s0.sp - 128#64) 48 ∗
        chunkedBelow s0.sp ∗ ct1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (Entails.of_eq (by dsimp only [ct1SampledErrFrame]; ac_rfl))
    exact herr0_exit hnone hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm]) hsm1 ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨key, rest⟩
    have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
    have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
    have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le
    have hrest_suf : IsDropSuffix x.bs rest := suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
    let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
    by_cases hk_ge : 2 ^ 32 ≤ key.toNat
    · have hnone : (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
        rw [hres_cur, mergeLoopBin_of_key_ge protoPrefixStep_chunked_ct1Sampled_mergeField hgt_lim hd hk_ge, Option.map_none]
      have hshr := key_shr32_of_ge hk_ge; apply SepWPp.of_sepWP (mid := (blkPl_300).base + 108#64)
      conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]
      apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
      apply SepWP.fold (chunkedBelow_leaf_entails s0.sp) (by sep_focus)
      apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
      apply SepWP.fold (chunkedCt1SampledPBCapAt_entails_pb A x.msgPtr cur.length m) (by sep_focus)
      conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_split2_128 s0.sp]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply SepWP.exists_elim; intro v_err0; apply SepWP.exists_elim; intro v_err1; wp_steps
      apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
      apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
      have h40 : ((s0.sp - 128#64 + 8#64) ↦₆₄ key) ∗ memRegion (s0.sp - 112#64) 32 ⊢ memRegion (s0.sp - 120#64) 40 := by
        rw [bv_sub_add_lit s0.sp 128 8]; exact pointsTo64_memRegion32_entails_40_128 s0.sp key
      apply SepWP.fold h40 (by sep_focus); wp_reach
      apply SepWPp.weaken_pre (P' :=
        ((s0.sp - 128#64) ↦₆₄ v_err1) ∗ memRegion (s0.sp - 120#64) 40 ∗
          chunkedBelow s0.sp ∗ ct1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
        (Entails.of_eq (by dsimp only [ct1SampledErrFrame]; ac_rfl))
      exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000004#64) hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm]) ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
    · have hshr := key_shr32_of_lt hk_ge
      cases hwt : WireType.ofNat? (key.toNat % 8) with
      | none =>
        have hnone : (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
          rw [hres_cur, mergeLoopBin_of_wt_none protoPrefixStep_chunked_ct1Sampled_mergeField hgt_lim hd hk_ge hwt, Option.map_none]
        obtain ⟨hcs1, hcs2⟩ := key_wt_none hwt; apply SepWPp.of_sepWP (mid := (blkPl_300).base + 108#64)
        conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]
        apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
        apply SepWP.fold (chunkedBelow_leaf_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
        apply SepWP.fold (chunkedCt1SampledPBCapAt_entails_pb A x.msgPtr cur.length m) (by sep_focus)
        conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_split2_128 s0.sp]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        apply SepWP.exists_elim; intro v_err0; apply SepWP.exists_elim; intro v_err1; wp_steps
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        have h40 : ((s0.sp - 128#64 + 8#64) ↦₆₄ (key &&& 7#64)) ∗ memRegion (s0.sp - 112#64) 32 ⊢ memRegion (s0.sp - 120#64) 40 := by
          rw [bv_sub_add_lit s0.sp 128 8]; exact pointsTo64_memRegion32_entails_40_128 s0.sp (key &&& 7#64)
        apply SepWP.fold h40 (by sep_focus); wp_reach
        apply SepWPp.weaken_pre (P' :=
          ((s0.sp - 128#64) ↦₆₄ v_err1) ∗ memRegion (s0.sp - 120#64) 40 ∗
            chunkedBelow s0.sp ∗ ct1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
          (Entails.of_eq (by dsimp only [ct1SampledErrFrame]; ac_rfl))
        exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000003#64) hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm]) ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
      | some iwt =>
        obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
        obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_ge
        obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
        by_cases hitag0 : key.toNat / 8 < 1
        · have hnone : (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
            rw [hres_cur, mergeLoopBin_of_tag_zero protoPrefixStep_chunked_ct1Sampled_mergeField hgt_lim hd hk_ge hwt hitag0, Option.map_none]
          have htag_zero : key.toNat / 8 = 0 := by omega
          apply SepWPp.of_sepWP (mid := (blkPl_300).base + 108#64)
          conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]
          apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
          apply SepWP.fold (chunkedBelow_leaf_entails s0.sp) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          apply SepWP.fold (chunkedCt1SampledPBCapAt_entails_pb A x.msgPtr cur.length m) (by sep_focus)
          conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_split_128 s0.sp]
          simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
          apply SepWP.exists_elim; intro v_err0; wp_steps
          apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
          apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus); wp_reach
          apply SepWPp.weaken_pre (P' :=
            ((s0.sp - 128#64) ↦₆₄ v_err0) ∗ memRegion (s0.sp - 120#64) 40 ∗
              chunkedBelow s0.sp ∗ ct1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
            (Entails.of_eq (by dsimp only [ct1SampledErrFrame]; ac_rfl))
          exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000005#64) hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm]) ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
        · obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_ge hitag0
          have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
            rw [beq_eq_false_iff_ne]; intro h; have h1 := congrArg BitVec.toNat h
            simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1; omega
          apply SepWPp.of_sepWP_lscro (mid := (blkPl_300).base + 244#64) himgm
          conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]
          apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
          apply SepWP.fold (chunkedBelow_leaf_entails s0.sp) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          apply SepWP.fold (chunkedCt1SampledPBCapAt_mono A x.msgPtr m hrest_le_cur) (by sep_focus)
          wp_steps; wp_reach; intro himg'
          apply SepWPp.weaken_pre (P' := ct1SampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
            (Entails.of_eq (by dsimp only [ct1SampledLoopPre]; ac_rfl))
          exact hcont key iwt rest _ hd hk_ge hwt hitag0 (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
            (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm, hsm1, hand_wt])
            (by simp only [arm64_norm, hsm1, hw1, hw1_2, hw1_zext1, hw1_zext2]) (by simp only [arm64_norm, hx19_m])
            (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
            ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m],
             ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩⟩ himg'

theorem ct1Sampled_loop_ok_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 261) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 291) (decodeVarint2Spec A))
    (hSkipCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 263) (skipField3Spec A))
    (hUcCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 312) (withLsCodeRoLoaded lsmpl (unchunkedCt1SentMergeSpec A)))
    (hPolyEncCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 297) (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A)))
    (hPolyDecCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 296) (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A)))
    {x : ChunkedCt1SampledMergeGhost} {R : SepProp} {s0 : State} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hbs_lt : x.bs.length < 2 ^ 63) (hlim_lt : limit < 2 ^ 63) :
    ∀ (n : Nat) (m : V1State.Chunked.Ct1Sampled) (cur : List (BitVec 8)) (s : State),
      cur.length ≤ n → cur.length ≤ x.bs.length → IsDropSuffix x.bs cur →
      optPolyEncoderPtsLen m.sendingCt1 + cur.length < 2 ^ 56 →
      optPolyEncoderPolysLen m.sendingCt1 + cur.length < 2 ^ 56 →
      optPolyDecoderPtsLen m.receivingEk + cur.length < 2 ^ 56 →
      (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
        (mergeLoopBin V1State.Chunked.Ct1Sampled.mergeField (cur.length - limit) m cur limit 98).map
          (fun m' => (m', x.bs.drop (x.bs.length - limit))) →
      s.pc = (blkPl_300).base + 192#64 →
      s.status = .Running → s.sp = s0.sp - 128#64 → s.trace = s0.trace →
      s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      ChunkedLoopRegs s0 s → LibsignalCodeRoLoaded lsmpl s.mem →
      SepWPp ((blkPC_300).rebase (blkPl_300).base H) (s0.readReg64 Reg.lr) s
        (ct1SampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs cur) (WppPost (chunkedCt1SampledMergeSpec A) x R s0) (WppPanic R s0) := by
  have htag1_step := fun {s m rest iwt} => @ct1Sampled_tag1_step_placed _ A H hUcCall hPushCall x R s0 s m rest iwt limit
  have htag2_step := fun {s m rest iwt} => @ct1Sampled_tag2_step_placed _ A H hPolyEncCall hPushCall x R s0 s m rest iwt limit
  have htag3_step := fun {s m rest iwt} => @ct1Sampled_tag3_step_placed _ A H hPolyDecCall hPushCall x R s0 s m rest iwt limit
  have hskip_step := fun {s m rest tag iwt} => @ct1Sampled_skip_step_placed _ A H hSkipCall x R s0 s m rest iwt tag limit
  intro n; induction n with
  | zero =>
    intro m cur s hcur_n hcur_le hcur_suf _ _ _ hres_cur hpc hrun hsp htr hx19 hx20 hx21 hx22 hcs _
    exact ct1Sampled_loop_le_exit_placed hFromCall (by omega) hsp_align hcur_le hcur_suf hlim_lt hres_cur hpc hrun hsp htr hx21 hx22 hcs
  | succ n ih =>
    intro m cur s hcur_n hcur_le hcur_suf hpts hpolys hdec_pts hres_cur hpc hrun hsp htr hx19 hx20 hx21 hx22 hcs himg
    by_cases hle_lim : cur.length ≤ limit
    · exact ct1Sampled_loop_le_exit_placed hFromCall hle_lim hsp_align hcur_le hcur_suf hlim_lt hres_cur hpc hrun hsp htr hx21 hx22 hcs
    · have hcur_lt : cur.length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
      refine ct1Sampled_decode_key_step_placed hFromCall hVarintCall hle_lim hsp_align hcur_le hcur_lt hcur_suf hres_cur ?_ hpc hrun hsp htr hx19 hx20 hx21 hx22 hcs himg
      intro key iwt rest s' hd hk_ge hwt hitag0 hpc' hrun' hsp' htr' hx0' hx1' hx19' hx20' hx21' hx22' hcs' himg'
      obtain ⟨hx23', hx24', hx25', hx26', hx27', hx28', hvregs'⟩ := hcs'
      have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
      have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
      have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le
      have hrest_lt : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest_le hbs_lt
      have hrest_suf : IsDropSuffix x.bs rest := suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
      have hloop_ok := mergeLoopBin_of_key_ok (m := m) (depth' := 98) protoPrefixStep_chunked_ct1Sampled_mergeField hle_lim hd hk_ge hwt hitag0
      by_cases htag1 : key.toNat / 8 = 1
      · rw [htag1] at hx1' hloop_ok; rw [chunkedCt1Sampled_mergeField_tag1] at hloop_ok
        apply SepWPp.of_sepWP_lscro (mid := (blkPl_300).base + 368#64) himg'; wp_steps; wp_reach; intro himg_s
        have hnone_uc : (Proto.mergeMessage V1State.Unchunked.Ct1Sent.mergeField (codecWireTypeToProto iwt) (m.uc.getD default) rest 98).toOption = none →
            (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
          intro huc; simp only [hres_cur, hloop_ok, huc, Option.map_none]
        refine htag1_step hsp_align hrest_le hrest_lt hrest_suf hnone_uc
          (fun u' rest' s'' huc hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' himg'' => ?_) (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr']) (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20']) (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) ⟨by simp only [arm64_norm, hx23'], by simp only [arm64_norm, hx24'], by simp only [arm64_norm, hx25'], ⟨by simp only [arm64_norm, hx26'], by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩⟩ himg_s
        have huf := proto_mergeMessage_suffix huc
        have hres_next : (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
            (mergeLoopBin V1State.Chunked.Ct1Sampled.mergeField (rest'.length - limit) { m with uc := some u' } rest' limit 98).map
              (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
          simp only [hres_cur, hloop_ok, huc, Option.map_some]
        exact ih { m with uc := some u' } rest' s'' (by have := huf.1; omega) (by have := huf.1; omega)
          (suffix_trans hrest_le hrest_suf huf.1 huf.2)
          (by dsimp only; have := huf.1; omega) (by dsimp only; have := huf.1; omega) (by dsimp only; have := huf.1; omega)
          hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' himg''
      · by_cases htag2 : key.toNat / 8 = 2
        · rw [htag2] at hx1' hloop_ok; rw [chunkedCt1Sampled_mergeField_tag2] at hloop_ok
          apply SepWPp.of_sepWP_lscro (mid := (blkPl_300).base + 316#64) himg'; wp_steps; wp_reach; intro himg_s
          have hnone_pe : (Proto.mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto iwt) (m.sendingCt1.getD default) rest 98).toOption = none →
              (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
            intro hpe; simp only [hres_cur, hloop_ok, hpe, Option.map_none]
          refine htag2_step hsp_align hrest_le hrest_suf (by omega) (by omega) hnone_pe
            (fun pe' rest' s'' hpe hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' himg'' => ?_)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
            (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20']) (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22'])
            ⟨by simp only [arm64_norm, hx23'], by simp only [arm64_norm, hx24'], by simp only [arm64_norm, hx25'], ⟨by simp only [arm64_norm, hx26'], by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩⟩ himg_s
          have hpf := proto_mergeMessage_suffix hpe
          obtain ⟨hpts_le, hpolys_le⟩ := polyEncoder_mergeMessage_pts_polys_len hpe
          have hpts_eq : (m.sendingCt1.getD default).pts.length = optPolyEncoderPtsLen m.sendingCt1 := optPolyEncoder_getD_default_pts_len m.sendingCt1
          have hpolys_eq : (m.sendingCt1.getD default).polys.length = optPolyEncoderPolysLen m.sendingCt1 := optPolyEncoder_getD_default_polys_len m.sendingCt1
          have hres_next : (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
              (mergeLoopBin V1State.Chunked.Ct1Sampled.mergeField (rest'.length - limit) { m with sendingCt1 := some pe' } rest' limit 98).map
                (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
            simp only [hres_cur, hloop_ok, hpe, Option.map_some]
          exact ih { m with sendingCt1 := some pe' } rest' s'' (by have := hpf.1; omega) (by have := hpf.1; omega)
            (suffix_trans hrest_le hrest_suf hpf.1 hpf.2)
            (by dsimp only [optPolyEncoderPtsLen]; omega) (by dsimp only [optPolyEncoderPolysLen]; omega) (by dsimp only; have := hpf.1; omega)
            hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' himg''
        · by_cases htag3 : key.toNat / 8 = 3
          · have hitag_lt : key.toNat / 8 < 2 ^ 32 := by omega
            obtain ⟨hb1_1, _⟩ := itag_beq_tag_false htag1 hitag_lt (by decide : 1 < 2 ^ 32)
            obtain ⟨hb2_1, _⟩ := itag_beq_tag_false htag2 hitag_lt (by decide : 2 < 2 ^ 32)
            have hb1_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 1#32) = false := by rw [sf_truncate32_ofNat64]; exact hb1_1
            have hb2_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 2#32) = false := by rw [sf_truncate32_ofNat64]; exact hb2_1
            rw [htag3] at hx1' hloop_ok; rw [chunkedCt1Sampled_mergeField_tag3] at hloop_ok
            apply SepWPp.of_sepWP_lscro (mid := (blkPl_300).base + 268#64) himg'; wp_steps; wp_reach; intro himg_s
            have hnone_pd : (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto iwt) (m.receivingEk.getD default) rest 98).toOption = none →
                (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
              intro hpd; simp only [hres_cur, hloop_ok, hpd, Option.map_none]
            refine htag3_step hsp_align hrest_le hrest_suf (by omega) hnone_pd
              (fun pd' rest' s'' hpd hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' himg'' => ?_)
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
              (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20']) (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22'])
              ⟨by simp only [arm64_norm, hx23'], by simp only [arm64_norm, hx24'], by simp only [arm64_norm, hx25'], ⟨by simp only [arm64_norm, hx26'], by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩⟩ himg_s
            have hpf := proto_mergeMessage_suffix hpd
            have hdec_le := polyDecoder_mergeMessage_pts_len hpd
            have hdec_eq : (m.receivingEk.getD default).pts.length = optPolyDecoderPtsLen m.receivingEk := optPolyDecoder_getD_default_pts_len m.receivingEk
            have hres_next : (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
                (mergeLoopBin V1State.Chunked.Ct1Sampled.mergeField (rest'.length - limit) { m with receivingEk := some pd' } rest' limit 98).map
                  (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
              simp only [hres_cur, hloop_ok, hpd, Option.map_some]
            exact ih { m with receivingEk := some pd' } rest' s'' (by have := hpf.1; omega) (by have := hpf.1; omega)
              (suffix_trans hrest_le hrest_suf hpf.1 hpf.2)
              (by dsimp only; have := hpf.1; omega) (by dsimp only; have := hpf.1; omega) (by dsimp only [optPolyDecoderPtsLen]; omega)
              hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' himg''
          · have hitag_lt : key.toNat / 8 < 2 ^ 32 := by omega
            obtain ⟨hb1_1, _⟩ := itag_beq_tag_false htag1 hitag_lt (by decide : 1 < 2 ^ 32)
            obtain ⟨hb2_1, _⟩ := itag_beq_tag_false htag2 hitag_lt (by decide : 2 < 2 ^ 32)
            obtain ⟨hb3_1, _⟩ := itag_beq_tag_false htag3 hitag_lt (by decide : 3 < 2 ^ 32)
            have hb1_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 1#32) = false := by rw [sf_truncate32_ofNat64]; exact hb1_1
            have hb2_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 2#32) = false := by rw [sf_truncate32_ofNat64]; exact hb2_1
            have hb3_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 3#32) = false := by rw [sf_truncate32_ofNat64]; exact hb3_1
            have hb3_bne1 : (BitVec.ofNat 32 (key.toNat / 8) != 3#32) = true := by simp only [bne, hb3_1, Bool.not_false]
            have hb3_bne2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) != 3#32) = true := by simp only [bne, hb3_2, Bool.not_false]
            rw [chunkedCt1Sampled_mergeField_other m iwt rest 98 hitag_lt htag1 htag2 htag3] at hloop_ok
            apply SepWPp.of_sepWP_lscro (mid := (blkPl_300).base + 172#64) himg'; wp_steps; wp_reach; intro himg_s
            have hnone_sf : skipField (2 * rest.length + 2) 98 (key.toNat / 8) iwt rest = none →
                (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
              intro hsf; rw [hres_cur, hloop_ok, hsf]; rfl
            refine hskip_step hsp_align hrest_le hrest_lt hrest_suf hitag_lt hnone_sf
              (fun rest' s'' hsf hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' himg'' => ?_)
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
              (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx1', sf_truncate32_ofNat64])
              (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20']) (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22'])
              ⟨by simp only [arm64_norm, hx23'], by simp only [arm64_norm, hx24'], by simp only [arm64_norm, hx25'], ⟨by simp only [arm64_norm, hx26'], by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩⟩ himg_s
            have hrest'_le_rest : rest'.length ≤ rest.length := (skip_length (2 * rest.length + 2)).1 _ _ _ _ _ hsf
            have hres_next : (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
                (mergeLoopBin V1State.Chunked.Ct1Sampled.mergeField (rest'.length - limit) m rest' limit 98).map
                  (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
              rw [hres_cur, hloop_ok, hsf]; rfl
            exact ih m rest' s'' (by omega) (by omega)
              (suffix_trans hrest_le hrest_suf hrest'_le_rest ((skip_suffix (2 * rest.length + 2)).1 _ _ _ _ _ hsf))
              (by omega) (by omega) (by omega)
              hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' himg''

set_option maxHeartbeats 800000 in
theorem chunkedCt1Sampled_merge_placed_ok_of_contracts [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 261) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 291) (decodeVarint2Spec A))
    (hSkipCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 263) (skipField3Spec A))
    (hUcCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 312) (withLsCodeRoLoaded lsmpl (unchunkedCt1SentMergeSpec A)))
    (hPolyEncCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 297) (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A)))
    (hPolyDecCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 296) (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A))) :
    subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (blkPl_300).base (withLsCodeRoLoaded lsmpl (chunkedCt1SampledMergeSpec A)) := by
  apply subroutine_ok_withLsCodeRoLoaded_of_withLscroProp
  unfold withLscroProp chunkedCt1SampledMergeSpec; wpp_init x s0
  have hx0_wt : (s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = BitVec.ofNat 8 x.wt.toNat := by assumption
  have hpts_0 : optPolyEncoderPtsLen x.msg.sendingCt1 + x.bs.length < 2 ^ 56 := by assumption
  have hpolys_0 : optPolyEncoderPolysLen x.msg.sendingCt1 + x.bs.length < 2 ^ 56 := by assumption
  have hdec_0 : optPolyDecoderPtsLen x.msg.receivingEk + x.bs.length < 2 ^ 56 := by assumption
  have hbs_lt : x.bs.length < 2 ^ 63 := by omega
  conv => arg 6; ext sf P_f; rw [sepConj_assoc, satisfies_pure_sepConj]
  change SepWPp ((blkPC_300).rebase (blkPl_300).base H) (s0.readReg64 Reg.lr) s0 _ (WppPost (chunkedCt1SampledMergeSpec A) x R s0) (WppPanic R s0)
  apply SepWPp.elim_lscroProp; intro himg0
  have herr0_exit := @ct1Sampled_err0_ret_exit_placed _ A H x R s0
  have hfrom_exit := @ct1Sampled_from_err_exit_placed _ A H hFromCall x R s0
  have hloop := @ct1Sampled_loop_ok_placed _ A H hFromCall hPushCall hVarintCall hSkipCall hUcCall hPolyEncCall hPolyDecCall x R s0
  by_cases hwt_ld : x.wt = .lengthDelimited
  · have h_1' : (s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = 2#8 := by rw [hx0_wt, hwt_ld]; rfl
    have hbeq := wt_beq_two_of_lengthDelimited h_1'
    have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = false := by simp only [bne, hbeq, Bool.not_true]
    have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = false := by
      rw [BytesMergeFacts.truncate32_zeroExtend64_and_255_eq, h_1']; decide
    have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = false := by
      revert h_1'; bv_bits
    apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 291) himg0
    conv => arg 4; rw [stackAt_chunkedMerge s0.sp, chunkedBelow_leaf s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v19; apply SepWP.exists_elim; intro v20
    apply SepWP.exists_elim; intro v21; apply SepWP.exists_elim; intro v22
    apply SepWP.exists_elim; intro v23; apply SepWP.exists_elim; intro v24
    apply SepWP.exists_elim; intro v25; apply SepWP.exists_elim; intro v_lr; apply SepWP.exists_elim; intro v_fp
    wp_steps; wp_reach; intro himg1
    refine SepWPp.call_frame_keep_lscro (hinv := himg1) (x := ⟨x.bufRef, x.slot, x.ptr, x.bs⟩) (ret_pc := (blkPl_300).base + 56#64) hVarintCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
      (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm]; rfl)
      hbs_lt (by sep_focus) (fun _ _ _ _ hex => allowPanic_not_exited hex)
      (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm]) hpan) ?_
    intro sm hpcm hrunm hspm hcsm himgm; simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
    cases hdv0 : decodeVarint x.bs with
    | none =>
      have hnone : (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto .lengthDelimited) x.msg x.bs 99).toOption = none := by
        rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_chunked_ct1Sampled_mergeField]
        simp [mergeMessageBin, codecWireTypeToProto, proto_decodeVarint_toOption, hdv0]
      rw [hwt_ld] at herr0_exit; apply SepWPp.of_sepWP (mid := (blkPl_300).base + 124#64)
      conv => arg 4; simp only [decodeVarint2Spec, hdv0, sepConj_assoc, arm64_norm]
      apply SepWP.pure_elim; rintro ⟨hsm0, htrm, hsm1⟩
      apply SepWP.fold (chunkedBelow_leaf_entails s0.sp) (by sep_focus)
      apply SepWP.fold (chunkedCt1SampledPBCapAt_entails_pb A x.msgPtr x.bs.length x.msg) (by sep_focus)
      wp_steps; wp_reach
      apply SepWPp.weaken_pre (P' :=
        decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ memRegion (s0.sp - 128#64) 48 ∗
          chunkedBelow s0.sp ∗ ct1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs)
        (Entails.of_eq (by dsimp only [ct1SampledErrFrame, chunkedSavedRegs]; ac_rfl))
      exact herr0_exit hnone hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm]) (by simp only [arm64_norm]) hsm1 ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
    | some p =>
      rcases p with ⟨len, rest0⟩
      have hrest0_lt_bs : rest0.length < x.bs.length := decodeVarint_length hdv0
      have hrest0_le : rest0.length ≤ x.bs.length := Nat.le_of_lt hrest0_lt_bs
      have hrest0_lt : rest0.length < 2 ^ 63 := Nat.lt_of_lt_of_le hrest0_lt_bs (Nat.le_of_lt hbs_lt)
      have hrest0_suf : IsDropSuffix x.bs rest0 := decodeVarint_suffix hdv0
      let rest0Ptr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length)
      by_cases hlt_len : rest0.length < len.toNat
      · have hule := ule_len_of_lt hlt_len hrest0_lt
        have hnone : (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto .lengthDelimited) x.msg x.bs 99).toOption = none := by
          rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_chunked_ct1Sampled_mergeField]
          rcases hdv0_p : Proto.decodeVarint x.bs with e | ⟨len', rest0'⟩
          · have hdv0' : decodeVarint x.bs = none := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
            rw [hdv0] at hdv0'; nomatch hdv0'
          · have hdv0' : decodeVarint x.bs = some (len', rest0') := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
            rw [hdv0] at hdv0'; injection hdv0' with hpair; injection hpair with hlen hr0; subst hlen hr0
            simp [mergeMessageBin, codecWireTypeToProto, hdv0_p, Except.toOption, hlt_len]
        rw [hwt_ld] at hfrom_exit; apply SepWPp.of_sepWP (mid := (blkPl_300).base + 108#64)
        conv => arg 4; simp only [decodeVarint2Spec, hdv0, sliceCursorAfter_eq_split hrest0_le hrest0_suf,
          sliceCursorAt, memRegion_48_split_128 s0.sp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm]
        apply SepWP.exists_elim; intro v_stk0; apply SepWP.pure_elim; rintro ⟨⟨hsm0, hsm1⟩, htrm⟩
        apply SepWP.fold (chunkedBelow_leaf_entails s0.sp) (by sep_focus)
        apply SepWP.fold (chunkedCt1SampledPBCapAt_entails_pb A x.msgPtr x.bs.length x.msg) (by sep_focus)
        wp_steps
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot rest0Ptr (BitVec.ofNat 64 rest0.length)) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus); wp_reach
        apply SepWPp.weaken_pre (P' :=
          ((s0.sp - 128#64) ↦₆₄ v_stk0) ∗ memRegion (s0.sp - 120#64) 40 ∗
            chunkedBelow s0.sp ∗ ct1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs)
          (Entails.of_eq (by dsimp only [ct1SampledErrFrame, chunkedSavedRegs]; ac_rfl))
        exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000007#64) hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm]) (by simp only [arm64_norm]) ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
      · have hule := ule_len_of_ge hlt_len hrest0_lt
        have hsub := bv_len_sub_limit hlt_len
        have hlim_lt : rest0.length - len.toNat < 2 ^ 63 := by omega
        have hres0 : (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto .lengthDelimited) x.msg x.bs 99).toOption =
            (mergeLoopBin V1State.Chunked.Ct1Sampled.mergeField (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 98).map
              (fun m' => (m', x.bs.drop (x.bs.length - (rest0.length - len.toNat)))) := by
          rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_chunked_ct1Sampled_mergeField]
          rcases hdv0_p : Proto.decodeVarint x.bs with e | ⟨len', rest0'⟩
          · have hdv0' : decodeVarint x.bs = none := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
            rw [hdv0] at hdv0'; nomatch hdv0'
          · have hdv0' : decodeVarint x.bs = some (len', rest0') := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
            rw [hdv0] at hdv0'; injection hdv0' with hpair; injection hpair with hlen hr0; subst hlen hr0
            have hdrop_eq : x.bs.drop (x.bs.length - (rest0.length - len.toNat)) = rest0.drop len.toNat := by
              (conv_rhs => rw [hrest0_suf, List.drop_drop]); congr 1; omega
            simp only [mergeMessageBin, codecWireTypeToProto, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hdv0_p, Except.toOption, hlt_len, hdrop_eq]
            rcases mergeLoopBin V1State.Chunked.Ct1Sampled.mergeField (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 98 with _ | m' <;> rfl
        rw [hwt_ld] at hloop; apply SepWPp.of_sepWP_lscro (mid := (blkPl_300).base + 192#64) himgm
        conv => arg 4; simp only [decodeVarint2Spec, hdv0, sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt, sepConj_assoc, arm64_norm]
        apply SepWP.pure_elim; rintro ⟨⟨hsm0, hsm1⟩, htrm⟩
        apply SepWP.fold (chunkedBelow_leaf_entails s0.sp) (by sep_focus)
        apply SepWP.fold (chunkedCt1SampledPBCapAt_mono A x.msgPtr x.msg hrest0_le) (by sep_focus)
        wp_steps; wp_reach; intro himg2
        apply SepWPp.weaken_pre (P' := ct1SampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs rest0)
          (Entails.of_eq (by dsimp only [ct1SampledLoopPre, chunkedSavedRegs]; rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]; ac_rfl))
        exact hloop hsp_align hbs_lt hlim_lt rest0.length x.msg rest0 _ (Nat.le_refl _) hrest0_le hrest0_suf
          (by omega) (by omega) (by omega) hres0 (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm]) (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm]) (by simp only [arm64_norm, hsm1, hsub]) ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm], ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩⟩ himg2
  · have hbeq := wt_beq_two_of_ne_lengthDelimited hx0_wt hwt_ld
    have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = true := by simp only [bne, hbeq, Bool.not_false]
    have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = true := by
      rw [show BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) =
            BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 by bv_bits]; exact hbne1
    have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = true := by
      rw [show BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) =
            BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 by bv_bits]; exact hbne1
    have hnone : (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
      rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_chunked_ct1Sampled_mergeField]
      unfold mergeMessageBin; cases hwt_eq : x.wt <;> simp [hwt_eq, codecWireTypeToProto] at hwt_ld ⊢
    apply SepWPp.of_sepWP (mid := (blkPl_300).base + 108#64)
    conv => arg 4; rw [stackAt_chunkedMerge s0.sp, sliceCursorAt, memRegion_48_wtErr128 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v19; apply SepWP.exists_elim; intro v20
    apply SepWP.exists_elim; intro v21; apply SepWP.exists_elim; intro v22
    apply SepWP.exists_elim; intro v23; apply SepWP.exists_elim; intro v24
    apply SepWP.exists_elim; intro v25; apply SepWP.exists_elim; intro v_lr; apply SepWP.exists_elim; intro v_fp
    apply SepWP.exists_elim; intro b_wt1; apply SepWP.exists_elim; intro b_wt0; apply SepWP.exists_elim; intro v_wt0
    wp_steps
    apply SepWP.fold (wtErr128_entails_memRegion40 s0.sp _ _) (by sep_focus)
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot x.ptr (BitVec.ofNat 64 x.bs.length)) (by sep_focus)
    apply SepWP.fold (chunkedCt1SampledPBCapAt_entails_pb A x.msgPtr x.bs.length x.msg) (by sep_focus)
    wp_reach
    apply SepWPp.weaken_pre (P' :=
      ((s0.sp - 128#64) ↦₆₄ v_wt0) ∗ memRegion (s0.sp - 120#64) 40 ∗
        chunkedBelow s0.sp ∗ ct1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs)
      (Entails.of_eq (by dsimp only [ct1SampledErrFrame, chunkedSavedRegs]; ac_rfl))
    exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000006#64) hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩

end Placed

end CryptoVerification.SpqrV1.Prost.MessageMerge

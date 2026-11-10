/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommon
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirection
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Verification of `PolynomialDecoder::merge` (`0x4e10c`, Block `296`)

Proves `prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>`
against `(polyDecoderMergeSpec A).inImage img` (`LibsignalSpqrV1.Proto.mergeMessage PolynomialDecoder.mergeField`)
and its relocatable `[LibsignalPlacement]` counterpart on Block `296`.
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
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Prost.BytesMerge
open CryptoVerification.LibsignalSpqrV1 hiding decodeVarint encodeVarint WireType
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Step lemma for tag 1 (`pts_needed : u32` at `msgPtr + 24#64`) at `+0x158` (`entry + 344#64`). -/
theorem polyDecoder_tag1_step {b : BitVec 64} {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName + bv% (2 ^ 64 - ls_rel% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>")) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName + bv% (2 ^ 64 - ls_rel% "<prost::error::DecodeError>::push" "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>")) (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName + bv% (2 ^ 64 - ls_rel% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#2]" "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>")) (decodeVarint2Spec A))
    {x : PolyDecoderMergeGhost} {R : SepProp} {s0 s : State} {m : PolynomialDecoder} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_wt : iwt ≠ .varint →
      (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hnone_of_dv : iwt = .varint → decodeVarint rest = none →
      (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (v : BitVec 64) (rest' : List (BitVec 8)) (s' : State),
      iwt = .varint → decodeVarint rest = some (v, rest') →
      s'.pc = (libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName + 164#64 →
      s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s' → ImgCallInv img s' →
      SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s'
        (polyDecoderLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with ptsNeeded := v.truncate 32 } x.bs rest')
        (WppPost (polyDecoderMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName + 344#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 24#64)
    (hcs : PolyCalleeSaved s0 s) (hinv : ImgCallInv img s) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (polyDecoderLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (polyDecoderMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hpush_exit := @polyDecoder_push_err_exit b A H hPushCall x R s0
  polyDecoderMerge_fetches b H 344 28; polyDecoderMerge_fetches b H 504 12; polyDecoderMerge_fetches b H 660 68
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName = entry; examples_hide_fetches
  by_cases hiwt : iwt = .varint
  · subst hiwt; dsimp [WireType.toNat] at hx0
    apply SepWPp.of_sepWP_img (mid := entry + bv% (2 ^ 64 - ls_rel% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#2]" "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>")) hinv
    conv => arg 4; rw [polyDecoderLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf, polyBelow_decodeVarint2 s0.sp]; simp only [sepConj_assoc]
    wp_steps; wp_reach; intro hinv
    refine SepWPp.call_frame_keep (x := ⟨x.bufRef, x.slot, restPtr, rest⟩)
      (ret_pc := entry + 356#64) hVarintCall hinv (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
      (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, hsp, hx19]; rfl)
      hrest_lt (by sep_focus) (fun _ _ _ _ hex => allowPanic_not_exited hex)
      (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
    intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx26_m hx27_m hx28_m hvregs_m
    cases hdv : decodeVarint rest with
    | none =>
      have hnone := hnone_of_dv rfl hdv
      apply SepWPp.of_sepWP (mid := entry + 896#64)
      (conv => arg 4; simp only [decodeVarint2Spec, hdv, memRegion_48_cells1_160 s0.sp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp])
      apply SepWP.exists_elim; intro v_stk0; apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
      have hcbnz_err : (sm.readReg64 (Reg.gpr 1#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm1
      apply SepWP.fold (polyBelow_decodeVarint2_entails s0.sp) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
      wp_steps; wp_reach
      apply SepWPp.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 1#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 160#64) 32 ∗ polyDecoderErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (by dsimp only [polyDecoderErrFrame]; sep_entail)
      exact hpush_exit hnone hsm1 hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
        (by simp only [arm64_norm, hspm])
        ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
    | some p =>
      rcases p with ⟨v, rest'⟩
      have hrest'_le : rest'.length ≤ rest.length := Nat.le_of_lt (decodeVarint_length hdv)
      apply SepWPp.of_sepWP_img (mid := entry + 164#64) hinvm
      (conv => arg 4; simp only [decodeVarint2Spec, hdv, protoPolynomialDecoderAt, protoPolynomialDecoderPtsNeededOff, sepConj_assoc, arm64_norm, hsp])
      apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
      apply SepWP.fold (polyBelow_decodeVarint2_entails s0.sp) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
      wp_steps; wp_reach; intro hinvm
      apply SepWPp.weaken_pre (P' := polyDecoderLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with ptsNeeded := v.truncate 32 } x.bs rest') (by dsimp only [polyDecoderLoopPre, protoPolynomialDecoderAt, protoPolynomialDecoderPtsNeededOff]; sep_entail)
      exact hcont v rest' _ rfl hdv
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
        (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
        (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m])
        ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm
  · have hnone := hnone_of_wt hiwt; have hcbnz := iwt_cbnz_true_of_ne_varint hiwt
    apply SepWPp.of_sepWP (mid := entry + bv% (2 ^ 64 - ls_rel% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>"))
    conv => arg 4; rw [polyDecoderLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_wtErr160 s0.sp, polyBelow_decodeErrorHook s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro b_wt1; apply SepWP.exists_elim; intro b_wt0; apply SepWP.exists_elim; intro v_wt0
    wp_steps
    apply SepWP.fold (wtErr160_entails_memRegion40 s0.sp _ _) (by sep_focus); apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus); wp_reach
    refine SepWPp.call_frame (x := (s0.sp - 128#64, 0x8000000000000006#64))
      (ret_pc := entry + 688#64) hFromCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
      (by dsimp only [decodeErrorFromSpec]; simp only [arm64_norm, hsp]; rfl)
      (by decide : KindNoHeap 0x8000000000000006#64) (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
    intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨_, _, _, _, _, _, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, hsp, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx26_m hx27_m hx28_m hvregs_m
    apply SepWPp.of_sepWP (mid := entry + 896#64)
    (conv => arg 4; simp only [decodeErrorFromSpec, memRegion_48_cells1_160 s0.sp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp])
    apply SepWP.exists_elim; intro v_stk0; apply SepWP.pure_elim; rintro ⟨hve_ne, htrm⟩
    apply SepWP.fold (polyBelow_decodeErrorHook_entails s0.sp) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPp.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 160#64) 32 ∗ polyDecoderErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (by dsimp only [polyDecoderErrFrame]; sep_entail)
    exact hpush_exit hnone hve_ne hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hspm])
      ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

/-- Step lemma for tag 2 (`polys : u32` at `msgPtr + 28#64`) at `+0x0f0` (`entry + 240#64`). -/
theorem polyDecoder_tag2_step {b : BitVec 64} {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName + bv% (2 ^ 64 - ls_rel% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>")) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName + bv% (2 ^ 64 - ls_rel% "<prost::error::DecodeError>::push" "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>")) (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName + bv% (2 ^ 64 - ls_rel% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#2]" "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>")) (decodeVarint2Spec A))
    {x : PolyDecoderMergeGhost} {R : SepProp} {s0 s : State} {m : PolynomialDecoder} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_wt : iwt ≠ .varint →
      (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hnone_of_dv : iwt = .varint → decodeVarint rest = none →
      (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (v : BitVec 64) (rest' : List (BitVec 8)) (s' : State),
      iwt = .varint → decodeVarint rest = some (v, rest') →
      s'.pc = (libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName + 164#64 →
      s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s' → ImgCallInv img s' →
      SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s'
        (polyDecoderLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with polys := v.truncate 32 } x.bs rest')
        (WppPost (polyDecoderMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName + 240#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 24#64)
    (hcs : PolyCalleeSaved s0 s) (hinv : ImgCallInv img s) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (polyDecoderLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (polyDecoderMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hpush_exit := @polyDecoder_push_err_exit b A H hPushCall x R s0
  polyDecoderMerge_fetches b H 240 28; polyDecoderMerge_fetches b H 472 12; polyDecoderMerge_fetches b H 728 68
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName = entry; examples_hide_fetches
  by_cases hiwt : iwt = .varint
  · subst hiwt; dsimp [WireType.toNat] at hx0
    apply SepWPp.of_sepWP_img (mid := entry + bv% (2 ^ 64 - ls_rel% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#2]" "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>")) hinv
    conv => arg 4; rw [polyDecoderLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf, polyBelow_decodeVarint2 s0.sp]; simp only [sepConj_assoc]
    wp_steps; wp_reach; intro hinv
    refine SepWPp.call_frame_keep (x := ⟨x.bufRef, x.slot, restPtr, rest⟩)
      (ret_pc := entry + 252#64) hVarintCall hinv (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
      (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, hsp, hx19]; rfl)
      hrest_lt (by sep_focus) (fun _ _ _ _ hex => allowPanic_not_exited hex)
      (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
    intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx26_m hx27_m hx28_m hvregs_m
    cases hdv : decodeVarint rest with
    | none =>
      have hnone := hnone_of_dv rfl hdv
      apply SepWPp.of_sepWP (mid := entry + 896#64)
      (conv => arg 4; simp only [decodeVarint2Spec, hdv, memRegion_48_cells1_160 s0.sp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp])
      apply SepWP.exists_elim; intro v_stk0; apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
      have hcbnz_err : (sm.readReg64 (Reg.gpr 1#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm1
      apply SepWP.fold (polyBelow_decodeVarint2_entails s0.sp) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
      wp_steps; wp_reach
      apply SepWPp.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 1#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 160#64) 32 ∗ polyDecoderErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (by dsimp only [polyDecoderErrFrame]; sep_entail)
      exact hpush_exit hnone hsm1 hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
        (by simp only [arm64_norm, hspm])
        ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
    | some p =>
      rcases p with ⟨v, rest'⟩
      have hrest'_le : rest'.length ≤ rest.length := Nat.le_of_lt (decodeVarint_length hdv)
      apply SepWPp.of_sepWP_img (mid := entry + 164#64) hinvm
      (conv => arg 4; simp only [decodeVarint2Spec, hdv, protoPolynomialDecoderAt, protoPolynomialDecoderPolysOff, sepConj_assoc, arm64_norm, hsp])
      apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
      apply SepWP.fold (polyBelow_decodeVarint2_entails s0.sp) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
      wp_steps; wp_reach; intro hinvm
      apply SepWPp.weaken_pre (P' := polyDecoderLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with polys := v.truncate 32 } x.bs rest') (by dsimp only [polyDecoderLoopPre, protoPolynomialDecoderAt, protoPolynomialDecoderPolysOff]; sep_entail)
      exact hcont v rest' _ rfl hdv
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
        (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
        (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m])
        ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm
  · have hnone := hnone_of_wt hiwt; have hcbnz := iwt_cbnz_true_of_ne_varint hiwt
    apply SepWPp.of_sepWP (mid := entry + bv% (2 ^ 64 - ls_rel% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>"))
    conv => arg 4; rw [polyDecoderLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_wtErr160 s0.sp, polyBelow_decodeErrorHook s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro b_wt1; apply SepWP.exists_elim; intro b_wt0; apply SepWP.exists_elim; intro v_wt0
    wp_steps
    apply SepWP.fold (wtErr160_entails_memRegion40 s0.sp _ _) (by sep_focus); apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus); wp_reach
    refine SepWPp.call_frame (x := (s0.sp - 128#64, 0x8000000000000006#64))
      (ret_pc := entry + 756#64) hFromCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
      (by dsimp only [decodeErrorFromSpec]; simp only [arm64_norm, hsp]; rfl)
      (by decide : KindNoHeap 0x8000000000000006#64) (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
    intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨_, _, _, _, _, _, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, hsp, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx26_m hx27_m hx28_m hvregs_m
    apply SepWPp.of_sepWP (mid := entry + 896#64)
    (conv => arg 4; simp only [decodeErrorFromSpec, memRegion_48_cells1_160 s0.sp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp])
    apply SepWP.exists_elim; intro v_stk0; apply SepWP.pure_elim; rintro ⟨hve_ne, htrm⟩
    apply SepWP.fold (polyBelow_decodeErrorHook_entails s0.sp) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPp.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 160#64) 32 ∗ polyDecoderErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (by dsimp only [polyDecoderErrFrame]; sep_entail)
    exact hpush_exit hnone hve_ne hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hspm])
      ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

/-- Step lemma for tag 4 (`is_complete : bool` at `msgPtr + 32#64`) at `+0x120` (`entry + 288#64`). -/
theorem polyDecoder_tag4_step {b : BitVec 64} {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName + bv% (2 ^ 64 - ls_rel% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>")) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName + bv% (2 ^ 64 - ls_rel% "<prost::error::DecodeError>::push" "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>")) (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName + bv% (2 ^ 64 - ls_rel% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#2]" "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>")) (decodeVarint2Spec A))
    {x : PolyDecoderMergeGhost} {R : SepProp} {s0 s : State} {m : PolynomialDecoder} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_wt : iwt ≠ .varint →
      (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hnone_of_dv : iwt = .varint → decodeVarint rest = none →
      (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (v : BitVec 64) (rest' : List (BitVec 8)) (s' : State),
      iwt = .varint → decodeVarint rest = some (v, rest') →
      s'.pc = (libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName + 164#64 →
      s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s' → ImgCallInv img s' →
      SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s'
        (polyDecoderLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with isComplete := v != 0#64 } x.bs rest')
        (WppPost (polyDecoderMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName + 288#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 24#64)
    (hcs : PolyCalleeSaved s0 s) (hinv : ImgCallInv img s) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (polyDecoderLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (polyDecoderMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hpush_exit := @polyDecoder_push_err_exit b A H hPushCall x R s0
  polyDecoderMerge_fetches b H 288 28; polyDecoderMerge_fetches b H 484 20; polyDecoderMerge_fetches b H 592 68
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName = entry; examples_hide_fetches
  by_cases hiwt : iwt = .varint
  · subst hiwt; dsimp [WireType.toNat] at hx0
    apply SepWPp.of_sepWP_img (mid := entry + bv% (2 ^ 64 - ls_rel% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#2]" "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>")) hinv
    conv => arg 4; rw [polyDecoderLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf, polyBelow_decodeVarint2 s0.sp]; simp only [sepConj_assoc]
    wp_steps; wp_reach; intro hinv
    refine SepWPp.call_frame_keep (x := ⟨x.bufRef, x.slot, restPtr, rest⟩)
      (ret_pc := entry + 300#64) hVarintCall hinv (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
      (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, hsp, hx19]; rfl)
      hrest_lt (by sep_focus) (fun _ _ _ _ hex => allowPanic_not_exited hex)
      (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
    intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx26_m hx27_m hx28_m hvregs_m
    cases hdv : decodeVarint rest with
    | none =>
      have hnone := hnone_of_dv rfl hdv
      apply SepWPp.of_sepWP (mid := entry + 896#64)
      (conv => arg 4; simp only [decodeVarint2Spec, hdv, memRegion_48_cells1_160 s0.sp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp])
      apply SepWP.exists_elim; intro v_stk0; apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
      have hcbnz_err : (sm.readReg64 (Reg.gpr 1#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm1
      apply SepWP.fold (polyBelow_decodeVarint2_entails s0.sp) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
      wp_steps; wp_reach
      apply SepWPp.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 1#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 160#64) 32 ∗ polyDecoderErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (by dsimp only [polyDecoderErrFrame]; sep_entail)
      exact hpush_exit hnone hsm1 hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
        (by simp only [arm64_norm, hspm])
        ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
    | some p =>
      rcases p with ⟨v, rest'⟩
      have hrest'_le : rest'.length ≤ rest.length := Nat.le_of_lt (decodeVarint_length hdv)
      apply SepWPp.of_sepWP_img (mid := entry + 164#64) hinvm
      (conv => arg 4; simp only [decodeVarint2Spec, hdv, protoPolynomialDecoderAt, protoPolynomialDecoderIsCompleteOff, sepConj_assoc, arm64_norm, hsp])
      apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
      apply SepWP.fold (polyBelow_decodeVarint2_entails s0.sp) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
      wp_steps; wp_reach; intro hinvm
      apply SepWPp.weaken_pre (P' := polyDecoderLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with isComplete := v != 0#64 } x.bs rest') (by dsimp only [polyDecoderLoopPre, protoPolynomialDecoderAt, protoPolynomialDecoderIsCompleteOff]; sep_entail)
      exact hcont v rest' _ rfl hdv
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
        (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
        (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m])
        ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm
  · have hnone := hnone_of_wt hiwt; have hcbnz := iwt_cbnz_true_of_ne_varint hiwt
    apply SepWPp.of_sepWP (mid := entry + bv% (2 ^ 64 - ls_rel% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>"))
    conv => arg 4; rw [polyDecoderLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_wtErr160 s0.sp, polyBelow_decodeErrorHook s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro b_wt1; apply SepWP.exists_elim; intro b_wt0; apply SepWP.exists_elim; intro v_wt0
    wp_steps
    apply SepWP.fold (wtErr160_entails_memRegion40 s0.sp _ _) (by sep_focus); apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus); wp_reach
    refine SepWPp.call_frame (x := (s0.sp - 128#64, 0x8000000000000006#64))
      (ret_pc := entry + 620#64) hFromCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
      (by dsimp only [decodeErrorFromSpec]; simp only [arm64_norm, hsp]; rfl)
      (by decide : KindNoHeap 0x8000000000000006#64) (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
    intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨_, _, _, _, _, _, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, hsp, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx26_m hx27_m hx28_m hvregs_m
    apply SepWPp.of_sepWP (mid := entry + 896#64)
    (conv => arg 4; simp only [decodeErrorFromSpec, memRegion_48_cells1_160 s0.sp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp])
    apply SepWP.exists_elim; intro v_stk0; apply SepWP.pure_elim; rintro ⟨hve_ne, htrm⟩
    apply SepWP.fold (polyBelow_decodeErrorHook_entails s0.sp) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPp.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 160#64) 32 ∗ polyDecoderErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (by dsimp only [polyDecoderErrFrame]; sep_entail)
    exact hpush_exit hnone hve_ne hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hspm])
      ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

/-- Shared element-copy join block at `+0x1b0` (`entry + 432#64`) for tag 3 (`pts : Vec<Vec<u8>>`). -/
theorem polyDecoder_tag3_copy_step {b : BitVec 64} {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    {x : PolyDecoderMergeGhost} {R : SepProp} {s0 : State} {m : PolynomialDecoder} {s : State}
    {v rest' : List (BitVec 8)} {limit : Nat} {v_stk0 cap' ptr' cap_e ptr_e : BitVec 64}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlt : m.pts.length < cap'.toNat) (hbound : cap'.toNat * 24 < 2 ^ 63) (hptr : ptr' ≠ 0)
    (hcont : ∀ (s' : State),
      s'.pc = (libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName + 164#64 →
      s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s' → ImgCallInv img s' →
      SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s'
        (polyDecoderLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with pts := m.pts ++ [v] } x.bs rest')
        (WppPost (polyDecoderMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName + 432#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 24#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = BitVec.ofNat 64 m.pts.length)
    (hcs : PolyCalleeSaved s0 s) (hinv : ImgCallInv img s) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 160#64) ↦₆₄ v_stk0) ∗ vecU8At A (s0.sp - 152#64) cap_e ptr_e v ∗
        (x.msgPtr ↦₆₄ cap') ∗ ((x.msgPtr + 8#64) ↦₆₄ ptr') ∗
        ((x.msgPtr + 16#64) ↦₆₄ BitVec.ofNat 64 m.pts.length) ∗
        A.live ptr' (cap'.toNat * 24) 8 ∗ arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr' m.pts ∗
        memRegion (ptr' + BitVec.ofNat 64 (m.pts.length * 24)) ((cap'.toNat - m.pts.length) * 24) ∗
        ((x.msgPtr + protoPolynomialDecoderPtsNeededOff) ↦₃₂ m.ptsNeeded) ∗
        ((x.msgPtr + protoPolynomialDecoderPolysOff) ↦₃₂ m.polys) ∗
        ((x.msgPtr + protoPolynomialDecoderIsCompleteOff) ↦₈ boolByte m.isComplete) ∗
        memRegion (x.msgPtr + protoPolynomialDecoderPadOff) protoPolynomialDecoderPadSize ∗
        stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗
        polySavedRegsAny s0.sp s0 ∗ (x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAfter x.slot x.ptr x.bs rest' ∗ A.pool)
      (WppPost (polyDecoderMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
  polyDecoderMerge_fetches b H 432 40
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName = entry; examples_hide_fetches
  apply SepWPp.of_sepWP_img (mid := entry + 164#64) hinv
  conv => arg 4; rw [vecU8At_stack_to_cells A s0.sp cap_e ptr_e v, memRegion_split_24_cells ptr' m.pts.length cap'.toNat hlt hbound]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w1; apply SepWP.exists_elim; intro w0
  wp_steps
  apply SepWP.fold (cells160_entails_memRegion32 s0.sp v_stk0 cap_e ptr_e (BitVec.ofNat 64 v.length)) (by sep_focus)
  apply SepWP.fold (vecVecU8At_after_push A x.msgPtr cap' ptr' cap_e ptr_e m.pts v hlt hbound hptr) (by sep_focus)
  wp_reach; intro hinv
  apply SepWPp.weaken_pre (P' := polyDecoderLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with pts := m.pts ++ [v] } x.bs rest')
    (by dsimp only [polyDecoderLoopPre, protoPolynomialDecoderAt, polyDecoderToProto]; sep_entail)
  exact hcont _
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr])
    (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20]) (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22])
    (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
    ⟨by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩ hinv

/-- Step lemma for tag 3 (`pts : Vec<Vec<u8>>` at `msgPtr`) at `+0x178` (`entry + 376#64`). -/
theorem polyDecoder_tag3_step {b : BitVec 64} {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName + bv% (2 ^ 64 - ls_rel% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>")) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName + bv% (2 ^ 64 - ls_rel% "<prost::error::DecodeError>::push" "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>")) (decodeErrorPushSpec A))
    (hBytesCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName + bv% (2 ^ 64 - ls_rel% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#3]" "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>")) ((bytesMerge3RawSpec A).inImage img))
    (hGrowCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName + bv% (ls_off% "<alloc::raw_vec::RawVec<alloc::vec::Vec<u8>>>::grow_one" - ls_off% "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>")) (growOneVecU8Spec A))
    {x : PolyDecoderMergeGhost} {R : SepProp} {s0 s : State} {m : PolynomialDecoder} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hpts_bound : m.pts.length + rest.length < 2 ^ 56) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_mb : mergeBytes iwt rest = none →
      (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (v : List (BitVec 8)) (rest' : List (BitVec 8)) (s' : State),
      mergeBytes iwt rest = some (v, rest') →
      s'.pc = (libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName + 164#64 →
      s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s' → ImgCallInv img s' →
      SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s'
        (polyDecoderLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with pts := m.pts ++ [v] } x.bs rest')
        (WppPost (polyDecoderMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName + 376#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 24#64)
    (hcs : PolyCalleeSaved s0 s) (hinv : ImgCallInv img s) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (polyDecoderLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (polyDecoderMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hpush_exit := @polyDecoder_push_err_exit b A H hPushCall x R s0
  have hcopy := @polyDecoder_tag3_copy_step b img A H x R s0 m
  polyDecoderMerge_fetches b H 376 56; polyDecoderMerge_fetches b H 796 36; polyDecoderMerge_fetches b H 832 16; polyDecoderMerge_fetches b H 864 32
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName = entry; examples_hide_fetches
  by_cases hiwt : iwt = .lengthDelimited
  · subst hiwt; dsimp [WireType.toNat] at hx0
    apply SepWPp.of_sepWP_img (mid := entry + bv% (2 ^ 64 - ls_rel% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#3]" "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>")) hinv
    conv => arg 4; rw [polyDecoderLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf, memRegion_32_cells160 s0.sp, polyBelow_bytesMerge3 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v_stk3; apply SepWP.exists_elim; intro v_stk2; apply SepWP.exists_elim; intro v_stk1; apply SepWP.exists_elim; intro v_stk0
    wp_steps
    apply SepWP.fold (Entails.of_eq (vecU8At_zero_eq_cells A s0.sp).symm) (by sep_focus)
    wp_reach; intro hinv
    refine SepWPp.call_frame_inImage (x := ⟨.lengthDelimited, s0.sp - 152#64, 0#64, 1#64, [], x.bufRef, x.slot, restPtr, rest⟩)
      (ret_pc := entry + 404#64) hBytesCall hinv (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
      (by (conv => lhs; dsimp only [bytesMerge3RawSpec]; simp only [arm64_norm, hsp, hx0, hx19]); rfl)
      (⟨by omega, Or.inl rfl⟩ : rest.length < 2 ^ 63 ∧ BytesMergeCapOk 0#64 rest.length)
      (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
    intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx26_m hx27_m hx28_m hvregs_m
    cases hmb : mergeBytes .lengthDelimited rest with
    | none =>
      have hnone := hnone_of_mb hmb
      apply SepWPp.of_sepWP (mid := entry + 896#64)
      (conv => arg 4; simp only [bytesMerge3RawSpec, hmb, vecU8At_zero_eq_cells A s0.sp, memRegion_48_cells1_160 s0.sp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp])
      apply SepWP.exists_elim; intro v_err0; apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
      have hcbnz_err : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
      apply SepWP.fold (polyBelow_bytesMerge3_entails s0.sp) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
      wp_steps
      apply SepWP.fold (cells160_entails_memRegion32 s0.sp v_stk0 0#64 1#64 0#64) (by sep_focus)
      wp_reach
      apply SepWPp.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 160#64) 32 ∗ polyDecoderErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (by dsimp only [polyDecoderErrFrame]; sep_entail)
      exact hpush_exit hnone hsm0 hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
        (by simp only [arm64_norm, hspm])
        ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
    | some p =>
      rcases p with ⟨v, rest'⟩
      have hrest'_le : rest'.length ≤ rest.length := mergeBytes_length hmb
      (conv => arg 4; simp only [bytesMerge3RawSpec, hmb, List.nil_append, protoPolynomialDecoderAt, polyDecoderToProto, vecVecU8At, vecHeaderBytes, vecOf, vecAt, vecHeader, vecBuf, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp])
      apply SepWPp.exists_elim; intro cap; apply SepWPp.exists_elim; intro ptr
      apply SepWPp.exists_elim; intro cap_e; apply SepWPp.exists_elim; intro ptr_e
      apply SepWPp.pure_elim; rintro ⟨⟨htrm, hsm0, _⟩, ⟨hlen_le, hcap_bound, hptr_ne⟩⟩
      by_cases hcap_eq : m.pts.length = cap.toNat
      · have hbne : (BitVec.ofNat 64 m.pts.length != cap) = false := len_eq_cap_bne_false hcap_eq
        have hgrow_bound : max (2 * cap.toNat) 4 * 24 + 8 ≤ 2 ^ 63 := by omega
        apply SepWPp.of_sepWP_img (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVec<alloc::vec::Vec<u8>>>::grow_one" - ls_off% "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>")) hinvm
        apply SepWP.fold (polyBelow_bytesMerge3_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
        apply SepWP.fold (vecBuf_vecU8_entails_grow_pre A cap ptr m.pts hcap_eq) (by sep_focus)
        (conv => arg 4; rw [polyBelow_extHook s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro pins; apply SepWP.pure_elim; rintro ⟨hpins_len, hbytes_len⟩
        wp_steps; wp_reach; intro hinvm
        refine SepWPp.call_frame_keep (x := ⟨x.msgPtr, cap, ptr, vecU8ArrayBytes pins m.pts⟩)
          (ret_pc := entry + 432#64) hGrowCall hinvm (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
          (by simp only [State.spAligned, hspm, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
          (by conv => lhs; dsimp only [growOneVecU8Spec]; simp only [arm64_norm, hspm, hx20_m])
          (And.intro hbytes_len (And.intro hptr_ne (by omega : max (2 * cap.toNat) 4 * 24 ≤ 9223372036854775800))) (by sep_focus)
          (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htrm, htr]) hpan) ?_
        intro sm2 hpcm2 hrunm2 hspm2 hcsm2 hinvm2; simp only [CalleeSavedPreserved] at hcsm2
        obtain ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, _, hvregs_2⟩ := hcsm2
        simp (config := { decide := true }) only [arm64_norm, hspm, hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx26_m, hx27_m, hx28_m, hvregs_m] at hpcm2 hrunm2 hspm2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hvregs_2
        (conv => arg 4; simp only [growOneVecU8Spec, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hspm])
        apply SepWPp.exists_elim; intro p'
        apply SepWPp.pure_elim; rintro ⟨htrm2, hp'_ne, _⟩
        have hnew_toNat : (newCapVecU8 cap).toNat = max (2 * cap.toNat) 4 := by
          unfold newCapVecU8; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        have hlt_new : m.pts.length < (newCapVecU8 cap).toNat := by rw [hnew_toNat]; omega
        have hbound_new : (newCapVecU8 cap).toNat * 24 < 2 ^ 63 := by rw [hnew_toNat]; omega
        apply SepWPp.fold (grow_post_entails_ready A cap p' pins m.pts hcap_eq hpins_len hgrow_bound) (by sep_focus)
        apply SepWPp.fold (polyBelow_extHook_entails s0.sp) (by sep_focus)
        apply SepWPp.weaken_pre (P' := ((s0.sp - 160#64) ↦₆₄ v_stk0) ∗ vecU8At A (s0.sp - 152#64) cap_e ptr_e v ∗
          (x.msgPtr ↦₆₄ newCapVecU8 cap) ∗ ((x.msgPtr + 8#64) ↦₆₄ p') ∗
          ((x.msgPtr + 16#64) ↦₆₄ BitVec.ofNat 64 m.pts.length) ∗
          A.live p' ((newCapVecU8 cap).toNat * 24) 8 ∗ arrayAt (fun bs addr => vecU8 A addr bs) 24 p' m.pts ∗
          memRegion (p' + BitVec.ofNat 64 (m.pts.length * 24)) (((newCapVecU8 cap).toNat - m.pts.length) * 24) ∗
          ((x.msgPtr + protoPolynomialDecoderPtsNeededOff) ↦₃₂ m.ptsNeeded) ∗
          ((x.msgPtr + protoPolynomialDecoderPolysOff) ↦₃₂ m.polys) ∗
          ((x.msgPtr + protoPolynomialDecoderIsCompleteOff) ↦₈ boolByte m.isComplete) ∗
          memRegion (x.msgPtr + protoPolynomialDecoderPadOff) protoPolynomialDecoderPadSize ∗
          stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗
          polySavedRegsAny s0.sp s0 ∗ (x.bufRef ↦₆₄ x.slot) ∗
          sliceCursorAfter x.slot x.ptr x.bs rest' ∗ A.pool) (by sep_entail)
        exact hcopy hsp_align hlt_new hbound_new hp'_ne (fun s' => hcont v rest' s' hmb)
          hpcm2 hrunm2 hspm2 (htrm2.trans (htrm.trans htr))
          hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2
          (hx25_2.trans (by rw [hcap_eq, BitVec.ofNat_toNat, BitVec.setWidth_eq])) ⟨hx26_2, hx27_2, hx28_2, hvregs_2⟩ hinvm2
      · have hlt : m.pts.length < cap.toNat := Nat.lt_of_le_of_ne hlen_le hcap_eq
        have hbne : (BitVec.ofNat 64 m.pts.length != cap) = true := len_lt_cap_bne_true hlt
        have hcap_ne0 : cap ≠ 0 := by intro h0; subst h0; change m.pts.length < 0 at hlt; omega
        apply SepWPp.of_sepWP_img (mid := entry + 432#64) hinvm
        (conv => arg 4; simp only [hcap_ne0, ↓reduceIte, sepConj_assoc])
        apply SepWP.fold (polyBelow_bytesMerge3_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
        wp_steps; wp_reach; intro hinvm
        apply SepWPp.weaken_pre (P' := ((s0.sp - 160#64) ↦₆₄ v_stk0) ∗ vecU8At A (s0.sp - 152#64) cap_e ptr_e v ∗
          (x.msgPtr ↦₆₄ cap) ∗ ((x.msgPtr + 8#64) ↦₆₄ ptr) ∗
          ((x.msgPtr + 16#64) ↦₆₄ BitVec.ofNat 64 m.pts.length) ∗
          A.live ptr (cap.toNat * 24) 8 ∗ arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr m.pts ∗
          memRegion (ptr + BitVec.ofNat 64 (m.pts.length * 24)) ((cap.toNat - m.pts.length) * 24) ∗
          ((x.msgPtr + protoPolynomialDecoderPtsNeededOff) ↦₃₂ m.ptsNeeded) ∗
          ((x.msgPtr + protoPolynomialDecoderPolysOff) ↦₃₂ m.polys) ∗
          ((x.msgPtr + protoPolynomialDecoderIsCompleteOff) ↦₈ boolByte m.isComplete) ∗
          memRegion (x.msgPtr + protoPolynomialDecoderPadOff) protoPolynomialDecoderPadSize ∗
          stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗
          polySavedRegsAny s0.sp s0 ∗ (x.bufRef ↦₆₄ x.slot) ∗
          sliceCursorAfter x.slot x.ptr x.bs rest' ∗ A.pool) (by sep_entail)
        exact hcopy hsp_align hlt hcap_bound hptr_ne (fun s' => hcont v rest' s' hmb)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
          (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
          (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m]) (by simp only [arm64_norm])
          ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm
  · have hnone := hnone_of_mb (mergeBytes_eq_none_of_ne_len hiwt)
    obtain ⟨hbne2_64, hbne2_32⟩ := iwt_bne_two_true_of_ne_len hiwt
    apply SepWPp.of_sepWP (mid := entry + bv% (2 ^ 64 - ls_rel% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>"))
    conv => arg 4; rw [polyDecoderLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_wtErr160 s0.sp, polyBelow_decodeErrorHook s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro b_wt1; apply SepWP.exists_elim; intro b_wt0; apply SepWP.exists_elim; intro v_wt0
    wp_steps
    apply SepWP.fold (wtErr160_entails_memRegion40 s0.sp _ _) (by sep_focus); apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus); wp_reach
    refine SepWPp.call_frame (x := (s0.sp - 128#64, 0x8000000000000006#64))
      (ret_pc := entry + 828#64) hFromCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
      (by dsimp only [decodeErrorFromSpec]; simp only [arm64_norm, hsp]; rfl)
      (by decide : KindNoHeap 0x8000000000000006#64) (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
    intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨_, _, _, _, _, _, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, hsp, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx26_m hx27_m hx28_m hvregs_m
    apply SepWPp.of_sepWP (mid := entry + 896#64)
    (conv => arg 4; simp only [decodeErrorFromSpec, memRegion_48_cells1_160 s0.sp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp])
    apply SepWP.exists_elim; intro v_stk0; apply SepWP.pure_elim; rintro ⟨hve_ne, htrm⟩
    apply SepWP.fold (polyBelow_decodeErrorHook_entails s0.sp) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPp.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 160#64) 32 ∗ polyDecoderErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (by dsimp only [polyDecoderErrFrame]; sep_entail)
    exact hpush_exit hnone hve_ne hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hspm])
      ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

/-- Loop exit lemma at `+0x0a4` (`entry + 164#64`) when `cur.length ≤ limit`. -/
theorem polyDecoder_loop_le_exit {b : BitVec 64} {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName + bv% (2 ^ 64 - ls_rel% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>")) (decodeErrorFromSpec A))
    {x : PolyDecoderMergeGhost} {R : SepProp} {s0 s : State} {m : PolynomialDecoder} {cur : List (BitVec 8)} {limit : Nat}
    (hle_lim : cur.length ≤ limit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_suf : IsDropSuffix x.bs cur) (hlim_lt : limit < 2 ^ 63)
    (hres_cur : (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
      (mergeLoopBin PolynomialDecoder.mergeField (cur.length - limit) m cur limit 97).map
        (fun m' => (m', x.bs.drop (x.bs.length - limit))))
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName + 164#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64)
    (htr : s.trace = s0.trace) (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit) (hcs : PolyCalleeSaved s0 s) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (polyDecoderLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (polyDecoderMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs; let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  by_cases heq_lim : cur.length = limit
  · obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq heq_lim
    have hcur_eq_drop : x.bs.drop (x.bs.length - limit) = cur := by rw [← heq_lim]; exact hcur_suf.symm
    have hsome : (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = some (m, cur) := by
      rw [hres_cur, mergeLoopBin_eq_limit _ _ _ _ _ _ heq_lim, Option.map_some, hcur_eq_drop]
    polyDecoderMerge_fetches b H 164 12; polyDecoderMerge_fetches b H 516 12; polyDecoderMerge_fetches b H 124 32
    generalize_entry (libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName = entry; examples_hide_fetches
    apply SepWPp.of_sepWP_ret; unfold WppPost polyDecoderMergeSpec
    simp only [hsome, polyDecoderLoopPre, polySavedRegsAny, polySavedRegs,
      sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp]
    apply SepWP.exists_elim; intro v_pad
    wp_steps
    apply SepWP.fold (stackAt_polyMerge_epilogue s0.sp s0 v_pad) (by unfold polySavedRegs; sep_focus)
    wp_done
  · have hlt_lim : cur.length < limit := Nat.lt_of_le_of_ne hle_lim heq_lim
    obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_lt hlt_lim hlim_lt
    have hnone : (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
      rw [hres_cur, mergeLoopBin_lt_limit _ _ _ _ _ _ hlt_lim, Option.map_none]
    have hfrom_exit := @polyDecoder_from_err_exit b A H hFromCall x R s0
    polyDecoderMerge_fetches b H 164 12; polyDecoderMerge_fetches b H 516 4; polyDecoderMerge_fetches b H 576 16; polyDecoderMerge_fetches b H 80 8
    generalize_entry (libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName = entry; examples_hide_fetches
    apply SepWPp.of_sepWP (mid := entry + 112#64)
    conv => arg 4; rw [polyDecoderLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
      sliceCursorAt, memRegion_48_cells1_160 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v_stk0
    wp_steps
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot curPtr (BitVec.ofNat 64 cur.length)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    wp_reach
    apply SepWPp.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000008#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 160#64) 32 ∗ polyDecoderErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (by dsimp only [polyDecoderErrFrame]; sep_entail)
    exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000008#64) hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr])
      ⟨by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩

/-- Loop key-decoding step at `+0x0a4` (`entry + 164#64`) when `¬ cur.length ≤ limit`. -/
theorem polyDecoder_decode_key_step {b : BitVec 64} {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName + bv% (2 ^ 64 - ls_rel% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>")) (decodeErrorFromSpec A))
    (hVarintCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName + bv% (2 ^ 64 - ls_rel% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#2]" "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>")) (decodeVarint2Spec A))
    {x : PolyDecoderMergeGhost} {R : SepProp} {s0 s : State} {m : PolynomialDecoder} {cur : List (BitVec 8)} {limit : Nat}
    (hgt_lim : ¬ cur.length ≤ limit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_lt : cur.length < 2 ^ 63) (hcur_suf : IsDropSuffix x.bs cur)
    (hres_cur : (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
      (mergeLoopBin PolynomialDecoder.mergeField (cur.length - limit) m cur limit 97).map
        (fun m' => (m', x.bs.drop (x.bs.length - limit))))
    (hcont : ∀ (key : BitVec 64) (iwt : WireType) (rest : List (BitVec 8)) (s' : State),
      decodeVarint cur = some (key, rest) → ¬ 2 ^ 32 ≤ key.toNat →
      WireType.ofNat? (key.toNat % 8) = some iwt → ¬ key.toNat / 8 < 1 →
      s'.pc = (libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName + 216#64 →
      s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s' → ImgCallInv img s' →
      SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s'
        (polyDecoderLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
        (WppPost (polyDecoderMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName + 164#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 24#64)
    (hcs : PolyCalleeSaved s0 s) (hinv : ImgCallInv img s) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (polyDecoderLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (polyDecoderMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs; let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  have herr0_exit := @polyDecoder_err0_ret_exit b A H x R s0; have hfrom_exit := @polyDecoder_from_err_exit b A H hFromCall x R s0
  polyDecoderMerge_fetches b H 164 52; polyDecoderMerge_fetches b H 528 48; polyDecoderMerge_fetches b H 80 8
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName = entry; examples_hide_fetches
  apply SepWPp.of_sepWP_img (mid := entry + bv% (2 ^ 64 - ls_rel% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#2]" "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>")) hinv
  conv => arg 4; rw [polyDecoderLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
    sliceCursorAt, polyBelow_decodeVarint2 s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach; intro hinv
  refine SepWPp.call_frame_keep (x := ⟨x.bufRef, x.slot, curPtr, cur⟩)
    (ret_pc := entry + 184#64) hVarintCall hinv (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, hsp, hx19]; rfl)
    hcur_lt (by dsimp only [sliceCursorAt, curPtr]; sep_focus) (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx26_m hx27_m hx28_m hvregs_m
  cases hd : decodeVarint cur with
  | none =>
    have hnone : (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
      rw [hres_cur, mergeLoopBin_of_decodeVarint_none protoPrefixStep_polynomialDecoder_mergeField hgt_lim hd, Option.map_none]
    apply SepWPp.of_sepWP (mid := entry + 124#64)
    (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
    apply SepWP.fold (polyBelow_decodeVarint2_entails s0.sp) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPp.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 160#64) 32 ∗ memRegion (s0.sp - 128#64) 48 ∗ polyDecoderErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (by dsimp only [polyDecoderErrFrame]; sep_entail)
    exact herr0_exit hnone hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm]) hsm1
      ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨key, rest⟩
    have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd; have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
    have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le; have hrest_suf : IsDropSuffix x.bs rest :=
      suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
    let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
    by_cases hk_ge : 2 ^ 32 ≤ key.toNat
    · have hnone : (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
        rw [hres_cur, mergeLoopBin_of_key_ge protoPrefixStep_polynomialDecoder_mergeField hgt_lim hd hk_ge, Option.map_none]
      have hshr := key_shr32_of_ge hk_ge
      apply SepWPp.of_sepWP (mid := entry + 112#64)
      (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
      apply SepWP.fold (polyBelow_decodeVarint2_entails s0.sp) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
      (conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_cells2_160 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
      apply SepWP.exists_elim; intro v_err1; apply SepWP.exists_elim; intro v_err0
      wp_steps
      apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
      apply SepWP.fold (cells2_memRegion32_entails_40_160 s0.sp key) (by sep_focus); wp_reach
      apply SepWPp.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000004#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 160#64) 32 ∗ polyDecoderErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (by dsimp only [polyDecoderErrFrame]; sep_entail)
      exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000004#64) hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
        ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
    · have hshr := key_shr32_of_lt hk_ge
      cases hwt : WireType.ofNat? (key.toNat % 8) with
      | none =>
        have hnone : (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
          rw [hres_cur, mergeLoopBin_of_wt_none protoPrefixStep_polynomialDecoder_mergeField hgt_lim hd hk_ge hwt, Option.map_none]
        obtain ⟨hcs1, hcs2⟩ := key_wt_none hwt
        apply SepWPp.of_sepWP (mid := entry + 112#64)
        (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
        apply SepWP.fold (polyBelow_decodeVarint2_entails s0.sp) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
        (conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_cells2_160 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro v_err1; apply SepWP.exists_elim; intro v_err0; wp_steps
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        apply SepWP.fold (cells2_memRegion32_entails_40_160 s0.sp (key &&& 7#64)) (by sep_focus); wp_reach
        apply SepWPp.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000003#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 160#64) 32 ∗ polyDecoderErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (by dsimp only [polyDecoderErrFrame]; sep_entail)
        exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000003#64) hsp_align
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
          ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
      | some iwt =>
        obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
        obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_ge
        obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
        by_cases hitag0 : key.toNat / 8 < 1
        · have hnone : (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
            rw [hres_cur, mergeLoopBin_of_tag_zero protoPrefixStep_polynomialDecoder_mergeField hgt_lim hd hk_ge hwt hitag0, Option.map_none]
          have htag_zero : key.toNat / 8 = 0 := by omega
          apply SepWPp.of_sepWP (mid := entry + 112#64)
          (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
          apply SepWP.fold (polyBelow_decodeVarint2_entails s0.sp) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          (conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_cells1_160 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
          apply SepWP.exists_elim; intro v_err0; wp_steps
          apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus); wp_reach
          apply SepWPp.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000005#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 160#64) 32 ∗ polyDecoderErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (by dsimp only [polyDecoderErrFrame]; sep_entail)
          exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000005#64) hsp_align
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
            ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
        · obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_ge hitag0
          have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
            rw [beq_eq_false_iff_ne]; intro h; have h1 := congrArg BitVec.toNat h
            simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1; omega
          apply SepWPp.of_sepWP_img (mid := entry + 216#64) hinvm
          (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
          apply SepWP.fold (polyBelow_decodeVarint2_entails s0.sp) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          wp_steps; wp_reach; intro hinvm
          apply SepWPp.weaken_pre (P' := polyDecoderLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest) (by dsimp only [polyDecoderLoopPre]; sep_entail)
          exact hcont key iwt rest _ hd hk_ge hwt hitag0
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
            (by simp only [arm64_norm, hsm1, hand_wt]) (by simp only [arm64_norm, hsm1, hw1, hw1_2, hw1_zext1, hw1_zext2])
            (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
            (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
            (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m])
            ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm

/-- Main loop induction for `PolynomialDecoder::merge` at `+0x0a4` (`entry + 164#64`). -/
theorem polyDecoder_loop_ok {b : BitVec 64} {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName + bv% (2 ^ 64 - ls_rel% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>")) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName + bv% (2 ^ 64 - ls_rel% "<prost::error::DecodeError>::push" "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>")) (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName + bv% (2 ^ 64 - ls_rel% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#2]" "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>")) (decodeVarint2Spec A))
    (hSkipCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName + bv% (2 ^ 64 - ls_rel% "prost::encoding::skip_field::<&mut &[u8]> [local#3]" "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>")) (skipField3Spec A))
    (hBytesCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName + bv% (2 ^ 64 - ls_rel% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#3]" "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>")) ((bytesMerge3RawSpec A).inImage img))
    (hGrowCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName + bv% (ls_off% "<alloc::raw_vec::RawVec<alloc::vec::Vec<u8>>>::grow_one" - ls_off% "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>")) (growOneVecU8Spec A))
    {x : PolyDecoderMergeGhost} {R : SepProp} {s0 : State} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hlim_lt : limit < 2 ^ 63) :
    ∀ (n : Nat) (m : PolynomialDecoder) (cur : List (BitVec 8)) (s : State),
      cur.length ≤ n → cur.length ≤ x.bs.length → m.pts.length + cur.length < 2 ^ 56 → IsDropSuffix x.bs cur →
      (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
        (mergeLoopBin PolynomialDecoder.mergeField (cur.length - limit) m cur limit 97).map
          (fun m' => (m', x.bs.drop (x.bs.length - limit))) →
      s.pc = (libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName + 164#64 →
      s.status = .Running → s.sp = s0.sp - 160#64 → s.trace = s0.trace →
      s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s.readReg64 (Reg.gpr 23#5) = 1#64 → s.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s → ImgCallInv img s →
      SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
        (polyDecoderLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
        (WppPost (polyDecoderMergeSpec A) x R s0) (WppPanic R s0) := by
  have htag1_step := fun {s m rest iwt} => @polyDecoder_tag1_step b img A H hFromCall hPushCall hVarintCall x R s0 s m rest iwt limit
  have htag2_step := fun {s m rest iwt} => @polyDecoder_tag2_step b img A H hFromCall hPushCall hVarintCall x R s0 s m rest iwt limit
  have htag3_step := fun {s m rest iwt} => @polyDecoder_tag3_step b img A H hFromCall hPushCall hBytesCall hGrowCall x R s0 s m rest iwt limit
  have htag4_step := fun {s m rest iwt} => @polyDecoder_tag4_step b img A H hFromCall hPushCall hVarintCall x R s0 s m rest iwt limit
  have hskip_step := fun {s m rest tag iwt} => @polyDecoder_skip_step b img A H hSkipCall x R s0 s m rest tag iwt limit
  intro n; induction n with
  | zero =>
    intro m cur s hcur_n hcur_le _ hcur_suf hres_cur hpc hrun hsp htr _ _ hx21 hx22 _ _ hcs _
    exact polyDecoder_loop_le_exit hFromCall (by omega) hsp_align hcur_le hcur_suf hlim_lt
      hres_cur hpc hrun hsp htr hx21 hx22 hcs
  | succ n ih =>
    intro m cur s hcur_n hcur_le hpts_bound hcur_suf hres_cur hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hcs hinv
    by_cases hle_lim : cur.length ≤ limit
    · exact polyDecoder_loop_le_exit hFromCall hle_lim hsp_align hcur_le hcur_suf hlim_lt
        hres_cur hpc hrun hsp htr hx21 hx22 hcs
    · have hcur_lt : cur.length < 2 ^ 63 := by omega
      refine polyDecoder_decode_key_step hFromCall hVarintCall hle_lim hsp_align
        hcur_le hcur_lt hcur_suf hres_cur ?_ hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hcs hinv
      intro key iwt rest s' hd hk_ge hwt hitag0 hpc' hrun' hsp' htr' hx0' hx1' hx19' hx20' hx21' hx22' hx23' hx24' hcs' hinv'
      obtain ⟨hx26', hx27', hx28', hvregs'⟩ := hcs'
      have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd; have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
      have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le; have hrest_lt : rest.length < 2 ^ 63 := by omega
      have hrest_suf : IsDropSuffix x.bs rest := suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
      have hloop_ok := mergeLoopBin_of_key_ok (m := m) (depth' := 97) protoPrefixStep_polynomialDecoder_mergeField hle_lim hd hk_ge hwt hitag0
      by_cases htag1 : key.toNat / 8 = 1
      · rw [htag1] at hx1' hloop_ok; rw [polynomialDecoder_mergeField_tag1] at hloop_ok
        polyDecoderMerge_fetches b H 216 16
        generalize_entry (libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName = entry; examples_hide_fetches
        apply SepWPp.of_sepWP_img (mid := entry + 344#64) hinv'; wp_steps; wp_reach; intro hinv'
        refine htag1_step hsp_align hrest_le hrest_lt hrest_suf
          (fun (hiwt : iwt ≠ .varint) => by simp only [hres_cur, hloop_ok, hiwt, ↓reduceIte, Option.map_none])
          (fun (hiwt : iwt = .varint) (hdv : decodeVarint rest = none) => by simp only [hres_cur, hloop_ok, hiwt, ↓reduceIte, hdv, Option.map_none])
          (fun v rest' s'' hiwt hdv hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hcs'' hinv'' => ?_)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
          (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
          (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23']) (by simp only [arm64_norm, hx24'])
          ⟨by simp only [arm64_norm, hx26'], by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩ hinv'
        have hrest'_lt : rest'.length < rest.length := decodeVarint_length hdv; have hrest'_le_rest : rest'.length ≤ rest.length := Nat.le_of_lt hrest'_lt
        have hres_next : (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
            (mergeLoopBin PolynomialDecoder.mergeField (rest'.length - limit) { m with ptsNeeded := v.truncate 32 } rest' limit 97).map
              (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
          simp only [hres_cur, hloop_ok, hiwt, ↓reduceIte, hdv, Option.map_some]
        exact ih { m with ptsNeeded := v.truncate 32 } rest' s'' (by omega) (by omega) (by dsimp; omega)
          (suffix_trans hrest_le hrest_suf hrest'_le_rest (decodeVarint_suffix hdv))
          hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hcs'' hinv''
      · by_cases htag2 : key.toNat / 8 = 2
        · rw [htag2] at hx1' hloop_ok; rw [polynomialDecoder_mergeField_tag2] at hloop_ok
          polyDecoderMerge_fetches b H 216 24
          generalize_entry (libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName = entry; examples_hide_fetches
          apply SepWPp.of_sepWP_img (mid := entry + 240#64) hinv'; wp_steps; wp_reach; intro hinv'
          refine htag2_step hsp_align hrest_le hrest_lt hrest_suf
            (fun (hiwt : iwt ≠ .varint) => by simp only [hres_cur, hloop_ok, hiwt, ↓reduceIte, Option.map_none])
            (fun (hiwt : iwt = .varint) (hdv : decodeVarint rest = none) => by simp only [hres_cur, hloop_ok, hiwt, ↓reduceIte, hdv, Option.map_none])
            (fun v rest' s'' hiwt hdv hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hcs'' hinv'' => ?_)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
            (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
            (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23']) (by simp only [arm64_norm, hx24'])
            ⟨by simp only [arm64_norm, hx26'], by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩ hinv'
          have hrest'_lt : rest'.length < rest.length := decodeVarint_length hdv; have hrest'_le_rest : rest'.length ≤ rest.length := Nat.le_of_lt hrest'_lt
          have hres_next : (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
              (mergeLoopBin PolynomialDecoder.mergeField (rest'.length - limit) { m with polys := v.truncate 32 } rest' limit 97).map
                (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
            simp only [hres_cur, hloop_ok, hiwt, ↓reduceIte, hdv, Option.map_some]
          exact ih { m with polys := v.truncate 32 } rest' s'' (by omega) (by omega) (by dsimp; omega)
            (suffix_trans hrest_le hrest_suf hrest'_le_rest (decodeVarint_suffix hdv))
            hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hcs'' hinv''
        · by_cases htag3 : key.toNat / 8 = 3
          · rw [htag3] at hx1' hloop_ok; rw [polynomialDecoder_mergeField_tag3] at hloop_ok
            polyDecoderMerge_fetches b H 216 8; polyDecoderMerge_fetches b H 272 8
            generalize_entry (libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName = entry; examples_hide_fetches
            apply SepWPp.of_sepWP_img (mid := entry + 376#64) hinv'; wp_steps; wp_reach; intro hinv'
            have hnone_mb : mergeBytes iwt rest = none →
                (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
              intro hmb; simp only [hres_cur, hloop_ok, hmb, Option.map_none]
            refine htag3_step hsp_align hrest_le (by omega) hrest_suf hnone_mb
              (fun v rest' s'' hmb hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hcs'' hinv'' => ?_)
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
              (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
              (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23']) (by simp only [arm64_norm, hx24'])
              ⟨by simp only [arm64_norm, hx26'], by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩ hinv'
            have hrest'_le_rest : rest'.length ≤ rest.length := mergeBytes_length hmb
            have hres_next : (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
                (mergeLoopBin PolynomialDecoder.mergeField (rest'.length - limit) { m with pts := m.pts ++ [v] } rest' limit 97).map
                  (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
              simp only [hres_cur, hloop_ok, hmb, Option.map_some]
            exact ih { m with pts := m.pts ++ [v] } rest' s'' (by omega) (by omega) (by simp; omega)
              (suffix_trans hrest_le hrest_suf hrest'_le_rest (mergeBytes_suffix hmb))
              hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hcs'' hinv''
          · by_cases htag4 : key.toNat / 8 = 4
            · rw [htag4] at hx1' hloop_ok; rw [polynomialDecoder_mergeField_tag4] at hloop_ok
              polyDecoderMerge_fetches b H 216 8; polyDecoderMerge_fetches b H 272 16
              generalize_entry (libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName = entry; examples_hide_fetches
              apply SepWPp.of_sepWP_img (mid := entry + 288#64) hinv'; wp_steps; wp_reach; intro hinv'
              refine htag4_step hsp_align hrest_le hrest_lt hrest_suf
                (fun (hiwt : iwt ≠ .varint) => by simp only [hres_cur, hloop_ok, hiwt, ↓reduceIte, Option.map_none])
                (fun (hiwt : iwt = .varint) (hdv : decodeVarint rest = none) => by simp only [hres_cur, hloop_ok, hiwt, ↓reduceIte, hdv, Option.map_none])
                (fun v rest' s'' hiwt hdv hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hcs'' hinv'' => ?_)
                (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
                (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
                (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23']) (by simp only [arm64_norm, hx24'])
                ⟨by simp only [arm64_norm, hx26'], by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩ hinv'
              have hrest'_lt : rest'.length < rest.length := decodeVarint_length hdv; have hrest'_le_rest : rest'.length ≤ rest.length := Nat.le_of_lt hrest'_lt
              have hres_next : (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
                  (mergeLoopBin PolynomialDecoder.mergeField (rest'.length - limit) { m with isComplete := v != 0#64 } rest' limit 97).map
                    (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
                simp only [hres_cur, hloop_ok, hiwt, ↓reduceIte, hdv, Option.map_some]
              exact ih { m with isComplete := v != 0#64 } rest' s'' (by omega) (by omega) (by dsimp; omega)
                (suffix_trans hrest_le hrest_suf hrest'_le_rest (decodeVarint_suffix hdv))
                hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hcs'' hinv''
            · have hitag_lt : key.toNat / 8 < 2 ^ 32 := by omega
              obtain ⟨hslt1, hslt2⟩ := slt_two_ofNat32_true (n := key.toNat / 8) (by omega) (by omega)
              obtain ⟨hb3_1, _⟩ := itag_beq_tag_false htag3 hitag_lt (by decide : 3 < 2 ^ 32)
              obtain ⟨hb4_1, _⟩ := itag_beq_tag_false htag4 hitag_lt (by decide : 4 < 2 ^ 32)
              have hb3_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 3#32) = false := by rw [sf_truncate32_ofNat64]; exact hb3_1
              have hb4_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 4#32) = false := by rw [sf_truncate32_ofNat64]; exact hb4_1
              have hb4_bne1 : (BitVec.ofNat 32 (key.toNat / 8) != 4#32) = true := by simp only [bne, hb4_1, Bool.not_false]
              have hb4_bne2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) != 4#32) = true := by simp only [bne, hb4_2, Bool.not_false]
              rw [polynomialDecoder_mergeField_other m iwt rest 97 hitag_lt htag1 htag2 htag3 htag4] at hloop_ok
              polyDecoderMerge_fetches b H 216 8; polyDecoderMerge_fetches b H 272 16
              generalize_entry (libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName = entry; examples_hide_fetches
              apply SepWPp.of_sepWP_img (mid := entry + 320#64) hinv'; wp_steps; wp_reach; intro hinv'
              have hnone_sf : skipField (2 * rest.length + 2) 97 (key.toNat / 8) iwt rest = none →
                  (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
                intro hsf; rw [hres_cur, hloop_ok, hsf]; rfl
              refine hskip_step hsp_align hrest_le hrest_lt hrest_suf hitag_lt hnone_sf
                (fun rest' s'' hsf hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hcs'' hinv'' => ?_)
                (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
                (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx1', sf_truncate32_ofNat64])
                (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
                (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23']) (by simp only [arm64_norm, hx24'])
                ⟨by simp only [arm64_norm, hx26'], by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩ hinv'
              have hrest'_le_rest : rest'.length ≤ rest.length := (skip_length (2 * rest.length + 2)).1 _ _ _ _ _ hsf
              have hres_next : (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
                  (mergeLoopBin PolynomialDecoder.mergeField (rest'.length - limit) m rest' limit 97).map
                    (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
                rw [hres_cur, hloop_ok, hsf]; rfl
              exact ih m rest' s'' (by omega) (by omega) (by omega)
                (suffix_trans hrest_le hrest_suf hrest'_le_rest ((skip_suffix (2 * rest.length + 2)).1 _ _ _ _ _ hsf))
                hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hcs'' hinv''

/-- Contract-parameterized verification of `prost::encoding::message::merge::<PolynomialDecoder, &mut &[u8]>`. -/
theorem polyDecoderMerge_ok_of_contracts {b : BitVec 64} {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName + bv% (2 ^ 64 - ls_rel% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>")) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName + bv% (2 ^ 64 - ls_rel% "<prost::error::DecodeError>::push" "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>")) (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName + bv% (2 ^ 64 - ls_rel% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#2]" "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>")) (decodeVarint2Spec A))
    (hSkipCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName + bv% (2 ^ 64 - ls_rel% "prost::encoding::skip_field::<&mut &[u8]> [local#3]" "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>")) (skipField3Spec A))
    (hBytesCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName + bv% (2 ^ 64 - ls_rel% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#3]" "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>")) ((bytesMerge3RawSpec A).inImage img))
    (hGrowCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName + bv% (ls_off% "<alloc::raw_vec::RawVec<alloc::vec::Vec<u8>>>::grow_one" - ls_off% "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>")) (growOneVecU8Spec A)) :
    subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName) ((polyDecoderMergeSpec A).inImage img) := by
  apply subroutine_ok_inImage_of_withImgProp; unfold withImgProp polyDecoderMergeSpec; wpp_init x s0
  apply SepWPp.elim_imgCallInvProp; intro hinv0; replace hpc : s0.pc = (libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName := hpc
  conv => arg 6; ext sf P_f; simp only [polyDecoderMergeSpec, sepConj_assoc, satisfies_pure_sepConj]
  change SepWPp _ _ _ _ (WppPost (polyDecoderMergeSpec A) x R s0) (WppPanic R s0)
  have hbs_lt : x.bs.length < 2 ^ 63 := by omega
  have herr0_exit := @polyDecoder_err0_ret_exit b A H x R s0; have hfrom_exit := @polyDecoder_from_err_exit b A H hFromCall x R s0
  have hloop := fun {limit n m cur s} hlim_lt =>
    @polyDecoder_loop_ok b img A H hFromCall hPushCall hVarintCall hSkipCall hBytesCall hGrowCall x R s0 limit hsp_align hlim_lt n m cur s
  polyDecoderMerge_fetches b H 0 112; polyDecoderMerge_fetches b H 156 8
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr polyDecoderMergeName = entry; examples_hide_fetches
  by_cases hwt_ld : x.wt = .lengthDelimited
  · have h_1' : (s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = 2#8 := by rw [h_1, hwt_ld]; rfl
    have hbeq := wt_beq_two_of_lengthDelimited h_1'
    have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = false := by simp only [bne, hbeq, Bool.not_true]
    have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = false := by
      rw [BytesMergeFacts.truncate32_zeroExtend64_and_255_eq, h_1']; decide
    have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = false := by revert h_1'; bv_bits
    apply SepWPp.of_sepWP_img (mid := entry + bv% (2 ^ 64 - ls_rel% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#2]" "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>")) hinv0
    (conv => arg 4; rw [stackAt_polyMerge_prologue s0.sp, polyBelow_decodeVarint2 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v1; apply SepWP.exists_elim; intro v2; apply SepWP.exists_elim; intro v3
    apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v5; apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v7
    apply SepWP.exists_elim; intro v8; apply SepWP.exists_elim; intro v9
    wp_steps
    apply SepWP.fold (polySavedRegs_entails_any s0.sp s0 v3) (by unfold polySavedRegs; sep_focus)
    wp_reach; intro hinv0
    refine SepWPp.call_frame_keep (x := ⟨x.bufRef, x.slot, x.ptr, x.bs⟩)
      (ret_pc := entry + 56#64) hVarintCall hinv0 (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
      (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, h_3]; rfl) hbs_lt (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm]) hpan) ?_
    intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, h_2, h_3] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
    cases hdv0 : decodeVarint x.bs with
    | none =>
      have hnone : (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
        rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_polynomialDecoder_mergeField]
        simp [mergeMessageBin, codecWireTypeToProto, proto_decodeVarint_toOption, hdv0]
      apply SepWPp.of_sepWP (mid := entry + 124#64)
      (conv => arg 4; simp only [decodeVarint2Spec, hdv0, sepConj_assoc, arm64_norm]); apply SepWP.pure_elim; rintro ⟨hsm0, htrm, hsm1⟩
      apply SepWP.fold (polyBelow_decodeVarint2_entails s0.sp) (by sep_focus)
      wp_steps; wp_reach
      apply SepWPp.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 160#64) 32 ∗ memRegion (s0.sp - 128#64) 48 ∗ polyDecoderErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs) (by dsimp only [polyDecoderErrFrame]; sep_entail)
      exact herr0_exit hnone hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm])
        (by simp only [arm64_norm]) hsm1
        ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
    | some p =>
      rcases p with ⟨len, rest0⟩
      have hrest0_lt_bs : rest0.length < x.bs.length := decodeVarint_length hdv0; have hrest0_le : rest0.length ≤ x.bs.length := Nat.le_of_lt hrest0_lt_bs
      have hrest0_lt : rest0.length < 2 ^ 63 := Nat.lt_of_lt_of_le hrest0_lt_bs (Nat.le_of_lt hbs_lt)
      have hrest0_suf : IsDropSuffix x.bs rest0 := decodeVarint_suffix hdv0
      let rest0Ptr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length)
      by_cases hlt_len : rest0.length < len.toNat
      · have hule := ule_len_of_lt hlt_len hrest0_lt
        have hnone : (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
          rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_polynomialDecoder_mergeField]
          simp [mergeMessageBin, codecWireTypeToProto, proto_decodeVarint_toOption, hdv0, hlt_len]
        apply SepWPp.of_sepWP (mid := entry + 112#64)
        (conv => arg 4; simp only [decodeVarint2Spec, hdv0, sepConj_assoc, arm64_norm]); apply SepWP.pure_elim; rintro ⟨⟨hsm0, hsm1⟩, htrm⟩
        apply SepWP.fold (polyBelow_decodeVarint2_entails s0.sp) (by sep_focus)
        (conv => arg 4; rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt, memRegion_48_cells1_160 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro v_stk0; wp_steps
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot rest0Ptr (BitVec.ofNat 64 rest0.length)) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus); wp_reach
        apply SepWPp.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000007#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 160#64) 32 ∗ polyDecoderErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs) (by dsimp only [polyDecoderErrFrame]; sep_entail)
        exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000007#64) hsp_align
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm])
          ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
      · have hule := ule_len_of_ge hlt_len hrest0_lt; have hsub := bv_len_sub_limit hlt_len; have hlim_lt : rest0.length - len.toNat < 2 ^ 63 := by omega
        have hdrop_eq : x.bs.drop (x.bs.length - (rest0.length - len.toNat)) = rest0.drop len.toNat := by
          have hsuf := hrest0_suf; unfold IsDropSuffix at hsuf; conv => rhs; rw [hsuf, List.drop_drop]
          exact congrArg (List.drop · x.bs) (by omega)
        have hres0 : (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
            (mergeLoopBin PolynomialDecoder.mergeField (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 97).map
              (fun m' => (m', x.bs.drop (x.bs.length - (rest0.length - len.toNat)))) := by
          rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_polynomialDecoder_mergeField]
          simp only [mergeMessageBin, codecWireTypeToProto, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, proto_decodeVarint_toOption, hdv0, hlt_len, hdrop_eq]
          rcases mergeLoopBin PolynomialDecoder.mergeField (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 97 with _ | m' <;> rfl
        apply SepWPp.of_sepWP_img (mid := entry + 164#64) hinvm
        (conv => arg 4; simp only [decodeVarint2Spec, hdv0, sepConj_assoc, arm64_norm]); apply SepWP.pure_elim; rintro ⟨⟨hsm0, hsm1⟩, htrm⟩
        apply SepWP.fold (polyBelow_decodeVarint2_entails s0.sp) (by sep_focus)
        (conv => arg 4; rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]; simp only [sepConj_assoc]); wp_steps; wp_reach; intro hinvm
        apply SepWPp.weaken_pre (P' := polyDecoderLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs rest0) (by rw [polyDecoderLoopPre, sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]; sep_entail)
        exact hloop hlim_lt (Nat.le_refl _) hrest0_le (by omega) hrest0_suf hres0
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm])
          (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm]) (by simp only [arm64_norm, hsm1, hsub])
          (by simp only [arm64_norm]) (by simp only [arm64_norm])
          ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm
  · have hbeq := wt_beq_two_of_ne_lengthDelimited h_1 hwt_ld
    have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = true := by simp only [bne, hbeq, Bool.not_false]
    have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = true := by
      rw [BytesMergeFacts.truncate32_zeroExtend64_and_255_eq, h_1]; cases hxwt : x.wt <;> first | exact absurd hxwt hwt_ld | decide
    have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = true := by
      rw [← hbne1]; congr 2; bv_bits
    have hnone : (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
      rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_polynomialDecoder_mergeField]
      cases hxwt : x.wt <;> first | exact absurd hxwt hwt_ld | rfl
    apply SepWPp.of_sepWP (mid := entry + 112#64)
    conv => arg 4; rw [stackAt_polyMerge_prologue s0.sp, sliceCursorAt, memRegion_48_wtErr160 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v1; apply SepWP.exists_elim; intro v2; apply SepWP.exists_elim; intro v3
    apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v5; apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v7
    apply SepWP.exists_elim; intro v8; apply SepWP.exists_elim; intro v9
    apply SepWP.exists_elim; intro b_wt1; apply SepWP.exists_elim; intro b_wt0; apply SepWP.exists_elim; intro v_wt0
    wp_steps
    apply SepWP.fold (polySavedRegs_entails_any s0.sp s0 v3) (by unfold polySavedRegs; sep_focus)
    apply SepWP.fold (wtErr160_entails_memRegion40 s0.sp _ _) (by sep_focus)
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot x.ptr (BitVec.ofNat 64 x.bs.length)) (by sep_focus)
    wp_reach
    apply SepWPp.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000006#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 160#64) 32 ∗ polyDecoderErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs) (by dsimp only [polyDecoderErrFrame]; sep_entail)
    exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000006#64) hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩

/-- `prost::encoding::message::merge::<PolynomialDecoder, &mut &[u8]>` meets
`(polyDecoderMergeSpec A).inImage img` on `tripleRatchetProgAtExt img.base ext` given `((bytesMerge3RawSpec A).inImage img)`
and `growOneVecU8Spec A`. -/
theorem polyDecoderMerge_ok_ext {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext)
    (hBytes : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr bytesMerge3Name) ((bytesMerge3RawSpec A).inImage img))
    (hGrow : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr growOneVecU8Name) (growOneVecU8Spec A)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr polyDecoderMergeName)
      ((polyDecoderMergeSpec A).inImage img) := by
  refine polyDecoderMerge_ok_of_contracts ?_ ?_ ?_ ?_ ?_ ?_
  · rw [fnAddr_offset_eq_H (name := polyDecoderMergeName) (callee := decodeErrorFromName)]; exact hC.decode_error_from
  · rw [fnAddr_offset_eq_H (name := polyDecoderMergeName) (callee := decodeErrorPushName)]; exact hC.decode_error_push
  · rw [fnAddr_offset_eq_H (name := polyDecoderMergeName) (callee := Varint.decodeVarint2Name)]; exact decodeVarint2_ok_ext hC
  · rw [fnAddr_offset_eq_H (name := polyDecoderMergeName) (callee := skipField3Name)]; exact skipField3_ok_ext hC
  · have h_off : (tripleRatchetProgAtExt img.base ext).fnAddr polyDecoderMergeName + bv% (2 ^ 64 - ls_rel% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#3]" "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>") =
        (tripleRatchetProgAtExt img.base ext).fnAddr bytesMerge3Name := by
      change (img.base + BitVec.ofNat 64 (libsignalSessionCode.fnOff polyDecoderMergeName)) + bv% (2 ^ 64 - ls_rel% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#3]" "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>") =
        img.base + BitVec.ofNat 64 (libsignalSessionCode.fnOff bytesMerge3Name)
      rw [(ls_lemma% fnOff "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>"), (ls_lemma% fnOff "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#3]")]; bv_omega
    rw [h_off]; exact hBytes
  · have h_off : (tripleRatchetProgAtExt img.base ext).fnAddr polyDecoderMergeName + bv% (ls_off% "<alloc::raw_vec::RawVec<alloc::vec::Vec<u8>>>::grow_one" - ls_off% "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>") =
        (tripleRatchetProgAtExt img.base ext).fnAddr growOneVecU8Name := by
      change (img.base + BitVec.ofNat 64 (libsignalSessionCode.fnOff polyDecoderMergeName)) + bv% (ls_off% "<alloc::raw_vec::RawVec<alloc::vec::Vec<u8>>>::grow_one" - ls_off% "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>") =
        img.base + BitVec.ofNat 64 (libsignalSessionCode.fnOff growOneVecU8Name)
      rw [(ls_lemma% fnOff "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>"), (ls_lemma% fnOff "<alloc::raw_vec::RawVec<alloc::vec::Vec<u8>>>::grow_one")]; bv_omega
    rw [h_off]; exact hGrow

/-- End-to-end `.inImage img` contract for `PolynomialDecoder::merge` discharging `hBytes` via `bytes_merge_3_ok_ext`. -/
theorem polyDecoderMerge_ok_ext_of_bytes_contracts {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext) (hBC : BytesMerge3Contracts img A ext)
    (hGrow : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr growOneVecU8Name) (growOneVecU8Spec A)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr polyDecoderMergeName)
      ((polyDecoderMergeSpec A).inImage img) :=
  polyDecoderMerge_ok_ext hC hBC.ok_ext hGrow

/-! ## Relocatable `[LibsignalPlacement]` Verification (Block `296`) -/

attribute [local arm64_norm] growOneVecU8Name

/-- Placed step lemma for tag 1 (`pts_needed : u32` at `msgPtr + 24#64`) at `+0x158` (`(blkPl_296).base + 344#64`). -/
theorem polyDecoder_tag1_step_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 261) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 291) (decodeVarint2Spec A))
    {x : PolyDecoderMergeGhost} {R : SepProp} {s0 s : State} {m : PolynomialDecoder} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_wt : iwt ≠ .varint →
      (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hnone_of_dv : iwt = .varint → decodeVarint rest = none →
      (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (v : BitVec 64) (rest' : List (BitVec 8)) (s' : State),
      iwt = .varint → decodeVarint rest = some (v, rest') →
      s'.pc = (blkPl_296).base + 164#64 →
      s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s'
        (polyDecoderLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with ptsNeeded := v.truncate 32 } x.bs rest')
        (WppPost (polyDecoderMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_296).base + 344#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 24#64)
    (hcs : PolyCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s
      (polyDecoderLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (polyDecoderMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hpush_exit := @polyDecoder_push_err_exit_placed _ A H hPushCall x R s0
  by_cases hiwt : iwt = .varint
  · subst hiwt; dsimp [WireType.toNat] at hx0
    apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 291) hinv
    conv => arg 4; rw [polyDecoderLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf, polyBelow_decodeVarint2 s0.sp]; simp only [sepConj_assoc]
    wp_steps; wp_reach; intro hinv
    refine SepWPp.call_frame_keep_lscro (x := ⟨x.bufRef, x.slot, restPtr, rest⟩)
      (ret_pc := (blkPl_296).base + 356#64) hVarintCall hinv (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
      (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, hsp, hx19]; rfl)
      hrest_lt (by sep_focus) (fun _ _ _ _ hex => allowPanic_not_exited hex)
      (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
    intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx26_m hx27_m hx28_m hvregs_m
    cases hdv : decodeVarint rest with
    | none =>
      have hnone := hnone_of_dv rfl hdv
      apply SepWPp.of_sepWP (mid := (blkPl_296).base + 896#64)
      (conv => arg 4; simp only [decodeVarint2Spec, hdv, memRegion_48_cells1_160 s0.sp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp])
      apply SepWP.exists_elim; intro v_stk0; apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
      have hcbnz_err : (sm.readReg64 (Reg.gpr 1#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm1
      apply SepWP.fold (polyBelow_decodeVarint2_entails s0.sp) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
      wp_steps; wp_reach
      apply SepWPp.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 1#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 160#64) 32 ∗ polyDecoderErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (by dsimp only [polyDecoderErrFrame]; sep_entail)
      exact hpush_exit hnone hsm1 hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
        (by simp only [arm64_norm, hspm])
        ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
    | some p =>
      rcases p with ⟨v, rest'⟩
      have hrest'_le : rest'.length ≤ rest.length := Nat.le_of_lt (decodeVarint_length hdv)
      apply SepWPp.of_sepWP_lscro (mid := (blkPl_296).base + 164#64) hinvm
      (conv => arg 4; simp only [decodeVarint2Spec, hdv, protoPolynomialDecoderAt, protoPolynomialDecoderPtsNeededOff, sepConj_assoc, arm64_norm, hsp])
      apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
      apply SepWP.fold (polyBelow_decodeVarint2_entails s0.sp) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
      wp_steps; wp_reach; intro hinvm
      apply SepWPp.weaken_pre (P' := polyDecoderLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with ptsNeeded := v.truncate 32 } x.bs rest') (by dsimp only [polyDecoderLoopPre, protoPolynomialDecoderAt, protoPolynomialDecoderPtsNeededOff]; sep_entail)
      exact hcont v rest' _ rfl hdv
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
        (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
        (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m])
        ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm
  · have hnone := hnone_of_wt hiwt; have hcbnz := iwt_cbnz_true_of_ne_varint hiwt
    apply SepWPp.of_sepWP (mid := lsmpl.base 261)
    conv => arg 4; rw [polyDecoderLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_wtErr160 s0.sp, polyBelow_decodeErrorHook s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro b_wt1; apply SepWP.exists_elim; intro b_wt0; apply SepWP.exists_elim; intro v_wt0
    wp_steps
    apply SepWP.fold (wtErr160_entails_memRegion40 s0.sp _ _) (by sep_focus); apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus); wp_reach
    refine SepWPp.call_frame (x := (s0.sp - 128#64, 0x8000000000000006#64))
      (ret_pc := (blkPl_296).base + 688#64) hFromCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
      (by dsimp only [decodeErrorFromSpec]; simp only [arm64_norm, hsp]; rfl)
      (by decide : KindNoHeap 0x8000000000000006#64) (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
    intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨_, _, _, _, _, _, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, hsp, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx26_m hx27_m hx28_m hvregs_m
    apply SepWPp.of_sepWP (mid := (blkPl_296).base + 896#64)
    (conv => arg 4; simp only [decodeErrorFromSpec, memRegion_48_cells1_160 s0.sp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp])
    apply SepWP.exists_elim; intro v_stk0; apply SepWP.pure_elim; rintro ⟨hve_ne, htrm⟩
    apply SepWP.fold (polyBelow_decodeErrorHook_entails s0.sp) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPp.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 160#64) 32 ∗ polyDecoderErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (by dsimp only [polyDecoderErrFrame]; sep_entail)
    exact hpush_exit hnone hve_ne hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hspm])
      ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

/-- Placed step lemma for tag 2 (`polys : u32` at `msgPtr + 28#64`) at `+0x0f0` (`(blkPl_296).base + 240#64`). -/
theorem polyDecoder_tag2_step_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 261) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 291) (decodeVarint2Spec A))
    {x : PolyDecoderMergeGhost} {R : SepProp} {s0 s : State} {m : PolynomialDecoder} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_wt : iwt ≠ .varint →
      (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hnone_of_dv : iwt = .varint → decodeVarint rest = none →
      (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (v : BitVec 64) (rest' : List (BitVec 8)) (s' : State),
      iwt = .varint → decodeVarint rest = some (v, rest') →
      s'.pc = (blkPl_296).base + 164#64 →
      s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s'
        (polyDecoderLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with polys := v.truncate 32 } x.bs rest')
        (WppPost (polyDecoderMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_296).base + 240#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 24#64)
    (hcs : PolyCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s
      (polyDecoderLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (polyDecoderMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hpush_exit := @polyDecoder_push_err_exit_placed _ A H hPushCall x R s0
  by_cases hiwt : iwt = .varint
  · subst hiwt; dsimp [WireType.toNat] at hx0
    apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 291) hinv
    conv => arg 4; rw [polyDecoderLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf, polyBelow_decodeVarint2 s0.sp]; simp only [sepConj_assoc]
    wp_steps; wp_reach; intro hinv
    refine SepWPp.call_frame_keep_lscro (x := ⟨x.bufRef, x.slot, restPtr, rest⟩)
      (ret_pc := (blkPl_296).base + 252#64) hVarintCall hinv (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
      (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, hsp, hx19]; rfl)
      hrest_lt (by sep_focus) (fun _ _ _ _ hex => allowPanic_not_exited hex)
      (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
    intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx26_m hx27_m hx28_m hvregs_m
    cases hdv : decodeVarint rest with
    | none =>
      have hnone := hnone_of_dv rfl hdv
      apply SepWPp.of_sepWP (mid := (blkPl_296).base + 896#64)
      (conv => arg 4; simp only [decodeVarint2Spec, hdv, memRegion_48_cells1_160 s0.sp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp])
      apply SepWP.exists_elim; intro v_stk0; apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
      have hcbnz_err : (sm.readReg64 (Reg.gpr 1#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm1
      apply SepWP.fold (polyBelow_decodeVarint2_entails s0.sp) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
      wp_steps; wp_reach
      apply SepWPp.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 1#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 160#64) 32 ∗ polyDecoderErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (by dsimp only [polyDecoderErrFrame]; sep_entail)
      exact hpush_exit hnone hsm1 hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
        (by simp only [arm64_norm, hspm])
        ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
    | some p =>
      rcases p with ⟨v, rest'⟩
      have hrest'_le : rest'.length ≤ rest.length := Nat.le_of_lt (decodeVarint_length hdv)
      apply SepWPp.of_sepWP_lscro (mid := (blkPl_296).base + 164#64) hinvm
      (conv => arg 4; simp only [decodeVarint2Spec, hdv, protoPolynomialDecoderAt, protoPolynomialDecoderPolysOff, sepConj_assoc, arm64_norm, hsp])
      apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
      apply SepWP.fold (polyBelow_decodeVarint2_entails s0.sp) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
      wp_steps; wp_reach; intro hinvm
      apply SepWPp.weaken_pre (P' := polyDecoderLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with polys := v.truncate 32 } x.bs rest') (by dsimp only [polyDecoderLoopPre, protoPolynomialDecoderAt, protoPolynomialDecoderPolysOff]; sep_entail)
      exact hcont v rest' _ rfl hdv
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
        (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
        (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m])
        ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm
  · have hnone := hnone_of_wt hiwt; have hcbnz := iwt_cbnz_true_of_ne_varint hiwt
    apply SepWPp.of_sepWP (mid := lsmpl.base 261)
    conv => arg 4; rw [polyDecoderLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_wtErr160 s0.sp, polyBelow_decodeErrorHook s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro b_wt1; apply SepWP.exists_elim; intro b_wt0; apply SepWP.exists_elim; intro v_wt0
    wp_steps
    apply SepWP.fold (wtErr160_entails_memRegion40 s0.sp _ _) (by sep_focus); apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus); wp_reach
    refine SepWPp.call_frame (x := (s0.sp - 128#64, 0x8000000000000006#64))
      (ret_pc := (blkPl_296).base + 756#64) hFromCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
      (by dsimp only [decodeErrorFromSpec]; simp only [arm64_norm, hsp]; rfl)
      (by decide : KindNoHeap 0x8000000000000006#64) (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
    intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨_, _, _, _, _, _, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, hsp, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx26_m hx27_m hx28_m hvregs_m
    apply SepWPp.of_sepWP (mid := (blkPl_296).base + 896#64)
    (conv => arg 4; simp only [decodeErrorFromSpec, memRegion_48_cells1_160 s0.sp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp])
    apply SepWP.exists_elim; intro v_stk0; apply SepWP.pure_elim; rintro ⟨hve_ne, htrm⟩
    apply SepWP.fold (polyBelow_decodeErrorHook_entails s0.sp) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPp.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 160#64) 32 ∗ polyDecoderErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (by dsimp only [polyDecoderErrFrame]; sep_entail)
    exact hpush_exit hnone hve_ne hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hspm])
      ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

/-- Placed step lemma for tag 4 (`is_complete : bool` at `msgPtr + 32#64`) at `+0x120` (`(blkPl_296).base + 288#64`). -/
theorem polyDecoder_tag4_step_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 261) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 291) (decodeVarint2Spec A))
    {x : PolyDecoderMergeGhost} {R : SepProp} {s0 s : State} {m : PolynomialDecoder} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_wt : iwt ≠ .varint →
      (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hnone_of_dv : iwt = .varint → decodeVarint rest = none →
      (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (v : BitVec 64) (rest' : List (BitVec 8)) (s' : State),
      iwt = .varint → decodeVarint rest = some (v, rest') →
      s'.pc = (blkPl_296).base + 164#64 →
      s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s'
        (polyDecoderLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with isComplete := v != 0#64 } x.bs rest')
        (WppPost (polyDecoderMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_296).base + 288#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 24#64)
    (hcs : PolyCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s
      (polyDecoderLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (polyDecoderMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hpush_exit := @polyDecoder_push_err_exit_placed _ A H hPushCall x R s0
  by_cases hiwt : iwt = .varint
  · subst hiwt; dsimp [WireType.toNat] at hx0
    apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 291) hinv
    conv => arg 4; rw [polyDecoderLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf, polyBelow_decodeVarint2 s0.sp]; simp only [sepConj_assoc]
    wp_steps; wp_reach; intro hinv
    refine SepWPp.call_frame_keep_lscro (x := ⟨x.bufRef, x.slot, restPtr, rest⟩)
      (ret_pc := (blkPl_296).base + 300#64) hVarintCall hinv (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
      (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, hsp, hx19]; rfl)
      hrest_lt (by sep_focus) (fun _ _ _ _ hex => allowPanic_not_exited hex)
      (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
    intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx26_m hx27_m hx28_m hvregs_m
    cases hdv : decodeVarint rest with
    | none =>
      have hnone := hnone_of_dv rfl hdv
      apply SepWPp.of_sepWP (mid := (blkPl_296).base + 896#64)
      (conv => arg 4; simp only [decodeVarint2Spec, hdv, memRegion_48_cells1_160 s0.sp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp])
      apply SepWP.exists_elim; intro v_stk0; apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
      have hcbnz_err : (sm.readReg64 (Reg.gpr 1#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm1
      apply SepWP.fold (polyBelow_decodeVarint2_entails s0.sp) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
      wp_steps; wp_reach
      apply SepWPp.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 1#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 160#64) 32 ∗ polyDecoderErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (by dsimp only [polyDecoderErrFrame]; sep_entail)
      exact hpush_exit hnone hsm1 hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
        (by simp only [arm64_norm, hspm])
        ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
    | some p =>
      rcases p with ⟨v, rest'⟩
      have hrest'_le : rest'.length ≤ rest.length := Nat.le_of_lt (decodeVarint_length hdv)
      apply SepWPp.of_sepWP_lscro (mid := (blkPl_296).base + 164#64) hinvm
      (conv => arg 4; simp only [decodeVarint2Spec, hdv, protoPolynomialDecoderAt, protoPolynomialDecoderIsCompleteOff, sepConj_assoc, arm64_norm, hsp])
      apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
      apply SepWP.fold (polyBelow_decodeVarint2_entails s0.sp) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
      wp_steps; wp_reach; intro hinvm
      apply SepWPp.weaken_pre (P' := polyDecoderLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with isComplete := v != 0#64 } x.bs rest') (by dsimp only [polyDecoderLoopPre, protoPolynomialDecoderAt, protoPolynomialDecoderIsCompleteOff]; sep_entail)
      exact hcont v rest' _ rfl hdv
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
        (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
        (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m])
        ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm
  · have hnone := hnone_of_wt hiwt; have hcbnz := iwt_cbnz_true_of_ne_varint hiwt
    apply SepWPp.of_sepWP (mid := lsmpl.base 261)
    conv => arg 4; rw [polyDecoderLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_wtErr160 s0.sp, polyBelow_decodeErrorHook s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro b_wt1; apply SepWP.exists_elim; intro b_wt0; apply SepWP.exists_elim; intro v_wt0
    wp_steps
    apply SepWP.fold (wtErr160_entails_memRegion40 s0.sp _ _) (by sep_focus); apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus); wp_reach
    refine SepWPp.call_frame (x := (s0.sp - 128#64, 0x8000000000000006#64))
      (ret_pc := (blkPl_296).base + 620#64) hFromCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
      (by dsimp only [decodeErrorFromSpec]; simp only [arm64_norm, hsp]; rfl)
      (by decide : KindNoHeap 0x8000000000000006#64) (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
    intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨_, _, _, _, _, _, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, hsp, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx26_m hx27_m hx28_m hvregs_m
    apply SepWPp.of_sepWP (mid := (blkPl_296).base + 896#64)
    (conv => arg 4; simp only [decodeErrorFromSpec, memRegion_48_cells1_160 s0.sp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp])
    apply SepWP.exists_elim; intro v_stk0; apply SepWP.pure_elim; rintro ⟨hve_ne, htrm⟩
    apply SepWP.fold (polyBelow_decodeErrorHook_entails s0.sp) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPp.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 160#64) 32 ∗ polyDecoderErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (by dsimp only [polyDecoderErrFrame]; sep_entail)
    exact hpush_exit hnone hve_ne hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hspm])
      ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

/-- Placed shared element-copy join block at `+0x1b0` (`(blkPl_296).base + 432#64`) for tag 3 (`pts : Vec<Vec<u8>>`). -/
theorem polyDecoder_tag3_copy_step_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    {x : PolyDecoderMergeGhost} {R : SepProp} {s0 : State} {m : PolynomialDecoder} {s : State}
    {v rest' : List (BitVec 8)} {limit : Nat} {v_stk0 cap' ptr' cap_e ptr_e : BitVec 64}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlt : m.pts.length < cap'.toNat) (hbound : cap'.toNat * 24 < 2 ^ 63) (hptr : ptr' ≠ 0)
    (hcont : ∀ (s' : State),
      s'.pc = (blkPl_296).base + 164#64 →
      s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s'
        (polyDecoderLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with pts := m.pts ++ [v] } x.bs rest')
        (WppPost (polyDecoderMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_296).base + 432#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 24#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = BitVec.ofNat 64 m.pts.length)
    (hcs : PolyCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 160#64) ↦₆₄ v_stk0) ∗ vecU8At A (s0.sp - 152#64) cap_e ptr_e v ∗
        (x.msgPtr ↦₆₄ cap') ∗ ((x.msgPtr + 8#64) ↦₆₄ ptr') ∗
        ((x.msgPtr + 16#64) ↦₆₄ BitVec.ofNat 64 m.pts.length) ∗
        A.live ptr' (cap'.toNat * 24) 8 ∗ arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr' m.pts ∗
        memRegion (ptr' + BitVec.ofNat 64 (m.pts.length * 24)) ((cap'.toNat - m.pts.length) * 24) ∗
        ((x.msgPtr + protoPolynomialDecoderPtsNeededOff) ↦₃₂ m.ptsNeeded) ∗
        ((x.msgPtr + protoPolynomialDecoderPolysOff) ↦₃₂ m.polys) ∗
        ((x.msgPtr + protoPolynomialDecoderIsCompleteOff) ↦₈ boolByte m.isComplete) ∗
        memRegion (x.msgPtr + protoPolynomialDecoderPadOff) protoPolynomialDecoderPadSize ∗
        stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗
        polySavedRegsAny s0.sp s0 ∗ (x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAfter x.slot x.ptr x.bs rest' ∗ A.pool)
      (WppPost (polyDecoderMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
  apply SepWPp.of_sepWP_lscro (mid := (blkPl_296).base + 164#64) hinv
  conv => arg 4; rw [vecU8At_stack_to_cells A s0.sp cap_e ptr_e v, memRegion_split_24_cells ptr' m.pts.length cap'.toNat hlt hbound]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w1; apply SepWP.exists_elim; intro w0
  wp_steps
  apply SepWP.fold (cells160_entails_memRegion32 s0.sp v_stk0 cap_e ptr_e (BitVec.ofNat 64 v.length)) (by sep_focus)
  apply SepWP.fold (vecVecU8At_after_push A x.msgPtr cap' ptr' cap_e ptr_e m.pts v hlt hbound hptr) (by sep_focus)
  wp_reach; intro hinv
  apply SepWPp.weaken_pre (P' := polyDecoderLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with pts := m.pts ++ [v] } x.bs rest')
    (by dsimp only [polyDecoderLoopPre, protoPolynomialDecoderAt, polyDecoderToProto]; sep_entail)
  exact hcont _
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr])
    (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20]) (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22])
    (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
    ⟨by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩ hinv

/-- Placed step lemma for tag 3 (`pts : Vec<Vec<u8>>` at `msgPtr`) at `+0x178` (`(blkPl_296).base + 376#64`). -/
theorem polyDecoder_tag3_step_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 261) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    (hBytesCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A)))
    (hGrowCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 621) (withLsCodeRoLoaded lsmpl (growOneVecU8Spec A)))
    {x : PolyDecoderMergeGhost} {R : SepProp} {s0 s : State} {m : PolynomialDecoder} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hpts_bound : m.pts.length + rest.length < 2 ^ 56) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_mb : mergeBytes iwt rest = none →
      (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (v : List (BitVec 8)) (rest' : List (BitVec 8)) (s' : State),
      mergeBytes iwt rest = some (v, rest') →
      s'.pc = (blkPl_296).base + 164#64 →
      s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s'
        (polyDecoderLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with pts := m.pts ++ [v] } x.bs rest')
        (WppPost (polyDecoderMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_296).base + 376#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 24#64)
    (hcs : PolyCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s
      (polyDecoderLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (polyDecoderMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hpush_exit := @polyDecoder_push_err_exit_placed _ A H hPushCall x R s0
  have hcopy := @polyDecoder_tag3_copy_step_placed _ A H x R s0 m
  by_cases hiwt : iwt = .lengthDelimited
  · subst hiwt; dsimp [WireType.toNat] at hx0
    apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 290) hinv
    conv => arg 4; rw [polyDecoderLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf, memRegion_32_cells160 s0.sp, polyBelow_bytesMerge3 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v_stk3; apply SepWP.exists_elim; intro v_stk2; apply SepWP.exists_elim; intro v_stk1; apply SepWP.exists_elim; intro v_stk0
    wp_steps
    apply SepWP.fold (Entails.of_eq (vecU8At_zero_eq_cells A s0.sp).symm) (by sep_focus)
    wp_reach; intro hinv
    refine SepWPp.call_frame_lscro (x := ⟨.lengthDelimited, s0.sp - 152#64, 0#64, 1#64, [], x.bufRef, x.slot, restPtr, rest⟩)
      (ret_pc := (blkPl_296).base + 404#64) hBytesCall hinv (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
      (by (conv => lhs; dsimp only [bytesMerge3RawSpec]; simp only [arm64_norm, hsp, hx0, hx19]); rfl)
      (⟨by omega, Or.inl rfl⟩ : rest.length < 2 ^ 63 ∧ BytesMergeCapOk 0#64 rest.length)
      (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
    intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx26_m hx27_m hx28_m hvregs_m
    cases hmb : mergeBytes .lengthDelimited rest with
    | none =>
      have hnone := hnone_of_mb hmb
      apply SepWPp.of_sepWP (mid := (blkPl_296).base + 896#64)
      (conv => arg 4; simp only [bytesMerge3RawSpec, hmb, vecU8At_zero_eq_cells A s0.sp, memRegion_48_cells1_160 s0.sp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp])
      apply SepWP.exists_elim; intro v_err0; apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
      have hcbnz_err : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
      apply SepWP.fold (polyBelow_bytesMerge3_entails s0.sp) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
      wp_steps
      apply SepWP.fold (cells160_entails_memRegion32 s0.sp v_stk0 0#64 1#64 0#64) (by sep_focus)
      wp_reach
      apply SepWPp.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 160#64) 32 ∗ polyDecoderErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (by dsimp only [polyDecoderErrFrame]; sep_entail)
      exact hpush_exit hnone hsm0 hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
        (by simp only [arm64_norm, hspm])
        ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
    | some p =>
      rcases p with ⟨v, rest'⟩
      have hrest'_le : rest'.length ≤ rest.length := mergeBytes_length hmb
      (conv => arg 4; simp only [bytesMerge3RawSpec, hmb, List.nil_append, protoPolynomialDecoderAt, polyDecoderToProto, vecVecU8At, vecHeaderBytes, vecOf, vecAt, vecHeader, vecBuf, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp])
      apply SepWPp.exists_elim; intro cap; apply SepWPp.exists_elim; intro ptr
      apply SepWPp.exists_elim; intro cap_e; apply SepWPp.exists_elim; intro ptr_e
      apply SepWPp.pure_elim; rintro ⟨⟨htrm, hsm0, _⟩, ⟨hlen_le, hcap_bound, hptr_ne⟩⟩
      by_cases hcap_eq : m.pts.length = cap.toNat
      · have hbne : (BitVec.ofNat 64 m.pts.length != cap) = false := len_eq_cap_bne_false hcap_eq
        have hgrow_bound : max (2 * cap.toNat) 4 * 24 + 8 ≤ 2 ^ 63 := by omega
        apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 621) hinvm
        apply SepWP.fold (polyBelow_bytesMerge3_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
        apply SepWP.fold (vecBuf_vecU8_entails_grow_pre A cap ptr m.pts hcap_eq) (by sep_focus)
        (conv => arg 4; rw [polyBelow_extHook s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro pins; apply SepWP.pure_elim; rintro ⟨hpins_len, hbytes_len⟩
        wp_steps; wp_reach; intro hinvm
        refine SepWPp.call_frame_lscro (x := ⟨x.msgPtr, cap, ptr, vecU8ArrayBytes pins m.pts⟩)
          (ret_pc := (blkPl_296).base + 432#64) hGrowCall hinvm (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
          (by simp only [State.spAligned, hspm, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
          (by conv => lhs; dsimp only [growOneVecU8Spec]; simp only [arm64_norm, hspm, hx20_m])
          (And.intro hbytes_len (And.intro hptr_ne (by omega : max (2 * cap.toNat) 4 * 24 ≤ 9223372036854775800))) (by sep_focus)
          (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htrm, htr]) hpan) ?_
        intro sm2 hpcm2 hrunm2 hspm2 hcsm2 hinvm2; simp only [CalleeSavedPreserved] at hcsm2
        obtain ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, _, hvregs_2⟩ := hcsm2
        simp (config := { decide := true }) only [arm64_norm, hspm, hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx26_m, hx27_m, hx28_m, hvregs_m] at hpcm2 hrunm2 hspm2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hvregs_2
        (conv => arg 4; simp only [growOneVecU8Spec, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hspm])
        apply SepWPp.exists_elim; intro p'
        apply SepWPp.pure_elim; rintro ⟨htrm2, hp'_ne, _⟩
        have hnew_toNat : (newCapVecU8 cap).toNat = max (2 * cap.toNat) 4 := by
          unfold newCapVecU8; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        have hlt_new : m.pts.length < (newCapVecU8 cap).toNat := by rw [hnew_toNat]; omega
        have hbound_new : (newCapVecU8 cap).toNat * 24 < 2 ^ 63 := by rw [hnew_toNat]; omega
        apply SepWPp.fold (grow_post_entails_ready A cap p' pins m.pts hcap_eq hpins_len hgrow_bound) (by sep_focus)
        apply SepWPp.fold (polyBelow_extHook_entails s0.sp) (by sep_focus)
        apply SepWPp.weaken_pre (P' := ((s0.sp - 160#64) ↦₆₄ v_stk0) ∗ vecU8At A (s0.sp - 152#64) cap_e ptr_e v ∗
          (x.msgPtr ↦₆₄ newCapVecU8 cap) ∗ ((x.msgPtr + 8#64) ↦₆₄ p') ∗
          ((x.msgPtr + 16#64) ↦₆₄ BitVec.ofNat 64 m.pts.length) ∗
          A.live p' ((newCapVecU8 cap).toNat * 24) 8 ∗ arrayAt (fun bs addr => vecU8 A addr bs) 24 p' m.pts ∗
          memRegion (p' + BitVec.ofNat 64 (m.pts.length * 24)) (((newCapVecU8 cap).toNat - m.pts.length) * 24) ∗
          ((x.msgPtr + protoPolynomialDecoderPtsNeededOff) ↦₃₂ m.ptsNeeded) ∗
          ((x.msgPtr + protoPolynomialDecoderPolysOff) ↦₃₂ m.polys) ∗
          ((x.msgPtr + protoPolynomialDecoderIsCompleteOff) ↦₈ boolByte m.isComplete) ∗
          memRegion (x.msgPtr + protoPolynomialDecoderPadOff) protoPolynomialDecoderPadSize ∗
          stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗
          polySavedRegsAny s0.sp s0 ∗ (x.bufRef ↦₆₄ x.slot) ∗
          sliceCursorAfter x.slot x.ptr x.bs rest' ∗ A.pool) (by sep_entail)
        exact hcopy hsp_align hlt_new hbound_new hp'_ne (fun s' => hcont v rest' s' hmb)
          hpcm2 hrunm2 hspm2 (htrm2.trans (htrm.trans htr))
          hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2
          (hx25_2.trans (by rw [hcap_eq, BitVec.ofNat_toNat, BitVec.setWidth_eq])) ⟨hx26_2, hx27_2, hx28_2, hvregs_2⟩ hinvm2
      · have hlt : m.pts.length < cap.toNat := Nat.lt_of_le_of_ne hlen_le hcap_eq
        have hbne : (BitVec.ofNat 64 m.pts.length != cap) = true := len_lt_cap_bne_true hlt
        have hcap_ne0 : cap ≠ 0 := by intro h0; subst h0; change m.pts.length < 0 at hlt; omega
        apply SepWPp.of_sepWP_lscro (mid := (blkPl_296).base + 432#64) hinvm
        (conv => arg 4; simp only [hcap_ne0, ↓reduceIte, sepConj_assoc])
        apply SepWP.fold (polyBelow_bytesMerge3_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
        wp_steps; wp_reach; intro hinvm
        apply SepWPp.weaken_pre (P' := ((s0.sp - 160#64) ↦₆₄ v_stk0) ∗ vecU8At A (s0.sp - 152#64) cap_e ptr_e v ∗
          (x.msgPtr ↦₆₄ cap) ∗ ((x.msgPtr + 8#64) ↦₆₄ ptr) ∗
          ((x.msgPtr + 16#64) ↦₆₄ BitVec.ofNat 64 m.pts.length) ∗
          A.live ptr (cap.toNat * 24) 8 ∗ arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr m.pts ∗
          memRegion (ptr + BitVec.ofNat 64 (m.pts.length * 24)) ((cap.toNat - m.pts.length) * 24) ∗
          ((x.msgPtr + protoPolynomialDecoderPtsNeededOff) ↦₃₂ m.ptsNeeded) ∗
          ((x.msgPtr + protoPolynomialDecoderPolysOff) ↦₃₂ m.polys) ∗
          ((x.msgPtr + protoPolynomialDecoderIsCompleteOff) ↦₈ boolByte m.isComplete) ∗
          memRegion (x.msgPtr + protoPolynomialDecoderPadOff) protoPolynomialDecoderPadSize ∗
          stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗
          polySavedRegsAny s0.sp s0 ∗ (x.bufRef ↦₆₄ x.slot) ∗
          sliceCursorAfter x.slot x.ptr x.bs rest' ∗ A.pool) (by sep_entail)
        exact hcopy hsp_align hlt hcap_bound hptr_ne (fun s' => hcont v rest' s' hmb)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
          (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
          (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m]) (by simp only [arm64_norm])
          ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm
  · have hnone := hnone_of_mb (mergeBytes_eq_none_of_ne_len hiwt)
    obtain ⟨hbne2_64, hbne2_32⟩ := iwt_bne_two_true_of_ne_len hiwt
    apply SepWPp.of_sepWP (mid := lsmpl.base 261)
    conv => arg 4; rw [polyDecoderLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_wtErr160 s0.sp, polyBelow_decodeErrorHook s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro b_wt1; apply SepWP.exists_elim; intro b_wt0; apply SepWP.exists_elim; intro v_wt0
    wp_steps
    apply SepWP.fold (wtErr160_entails_memRegion40 s0.sp _ _) (by sep_focus); apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus); wp_reach
    refine SepWPp.call_frame (x := (s0.sp - 128#64, 0x8000000000000006#64))
      (ret_pc := (blkPl_296).base + 828#64) hFromCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
      (by dsimp only [decodeErrorFromSpec]; simp only [arm64_norm, hsp]; rfl)
      (by decide : KindNoHeap 0x8000000000000006#64) (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
    intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨_, _, _, _, _, _, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, hsp, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx26_m hx27_m hx28_m hvregs_m
    apply SepWPp.of_sepWP (mid := (blkPl_296).base + 896#64)
    (conv => arg 4; simp only [decodeErrorFromSpec, memRegion_48_cells1_160 s0.sp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp])
    apply SepWP.exists_elim; intro v_stk0; apply SepWP.pure_elim; rintro ⟨hve_ne, htrm⟩
    apply SepWP.fold (polyBelow_decodeErrorHook_entails s0.sp) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPp.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 160#64) 32 ∗ polyDecoderErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (by dsimp only [polyDecoderErrFrame]; sep_entail)
    exact hpush_exit hnone hve_ne hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hspm])
      ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

/-- Placed loop exit lemma at `+0x0a4` (`(blkPl_296).base + 164#64`) when `cur.length ≤ limit`. -/
theorem polyDecoder_loop_le_exit_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 261) (decodeErrorFromSpec A))
    {x : PolyDecoderMergeGhost} {R : SepProp} {s0 s : State} {m : PolynomialDecoder} {cur : List (BitVec 8)} {limit : Nat}
    (hle_lim : cur.length ≤ limit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_suf : IsDropSuffix x.bs cur) (hlim_lt : limit < 2 ^ 63)
    (hres_cur : (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
      (mergeLoopBin PolynomialDecoder.mergeField (cur.length - limit) m cur limit 97).map
        (fun m' => (m', x.bs.drop (x.bs.length - limit))))
    (hpc : s.pc = (blkPl_296).base + 164#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64)
    (htr : s.trace = s0.trace) (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit) (hcs : PolyCalleeSaved s0 s) :
    SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s
      (polyDecoderLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (polyDecoderMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs; let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  by_cases heq_lim : cur.length = limit
  · obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq heq_lim
    have hcur_eq_drop : x.bs.drop (x.bs.length - limit) = cur := by rw [← heq_lim]; exact hcur_suf.symm
    have hsome : (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = some (m, cur) := by
      rw [hres_cur, mergeLoopBin_eq_limit _ _ _ _ _ _ heq_lim, Option.map_some, hcur_eq_drop]
    apply SepWPp.of_sepWP_ret; unfold WppPost polyDecoderMergeSpec
    simp only [hsome, polyDecoderLoopPre, polySavedRegsAny, polySavedRegs,
      sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp]
    apply SepWP.exists_elim; intro v_pad
    wp_steps
    apply SepWP.fold (stackAt_polyMerge_epilogue s0.sp s0 v_pad) (by unfold polySavedRegs; sep_focus)
    wp_done
  · have hlt_lim : cur.length < limit := Nat.lt_of_le_of_ne hle_lim heq_lim
    obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_lt hlt_lim hlim_lt
    have hnone : (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
      rw [hres_cur, mergeLoopBin_lt_limit _ _ _ _ _ _ hlt_lim, Option.map_none]
    have hfrom_exit := @polyDecoder_from_err_exit_placed _ A H hFromCall x R s0
    apply SepWPp.of_sepWP (mid := (blkPl_296).base + 112#64)
    conv => arg 4; rw [polyDecoderLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
      sliceCursorAt, memRegion_48_cells1_160 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v_stk0
    wp_steps
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot curPtr (BitVec.ofNat 64 cur.length)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    wp_reach
    apply SepWPp.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000008#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 160#64) 32 ∗ polyDecoderErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (by dsimp only [polyDecoderErrFrame]; sep_entail)
    exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000008#64) hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr])
      ⟨by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩

/-- Placed loop key-decoding step at `+0x0a4` (`(blkPl_296).base + 164#64`) when `¬ cur.length ≤ limit`. -/
theorem polyDecoder_decode_key_step_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 261) (decodeErrorFromSpec A))
    (hVarintCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 291) (decodeVarint2Spec A))
    {x : PolyDecoderMergeGhost} {R : SepProp} {s0 s : State} {m : PolynomialDecoder} {cur : List (BitVec 8)} {limit : Nat}
    (hgt_lim : ¬ cur.length ≤ limit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_lt : cur.length < 2 ^ 63) (hcur_suf : IsDropSuffix x.bs cur)
    (hres_cur : (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
      (mergeLoopBin PolynomialDecoder.mergeField (cur.length - limit) m cur limit 97).map
        (fun m' => (m', x.bs.drop (x.bs.length - limit))))
    (hcont : ∀ (key : BitVec 64) (iwt : WireType) (rest : List (BitVec 8)) (s' : State),
      decodeVarint cur = some (key, rest) → ¬ 2 ^ 32 ≤ key.toNat →
      WireType.ofNat? (key.toNat % 8) = some iwt → ¬ key.toNat / 8 < 1 →
      s'.pc = (blkPl_296).base + 216#64 →
      s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s'
        (polyDecoderLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
        (WppPost (polyDecoderMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_296).base + 164#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 24#64)
    (hcs : PolyCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s
      (polyDecoderLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (polyDecoderMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs; let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  have herr0_exit := @polyDecoder_err0_ret_exit_placed _ A H x R s0; have hfrom_exit := @polyDecoder_from_err_exit_placed _ A H hFromCall x R s0
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 291) hinv
  conv => arg 4; rw [polyDecoderLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
    sliceCursorAt, polyBelow_decodeVarint2 s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach; intro hinv
  refine SepWPp.call_frame_keep_lscro (x := ⟨x.bufRef, x.slot, curPtr, cur⟩)
    (ret_pc := (blkPl_296).base + 184#64) hVarintCall hinv (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, hsp, hx19]; rfl)
    hcur_lt (by dsimp only [sliceCursorAt, curPtr]; sep_focus) (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx26_m hx27_m hx28_m hvregs_m
  cases hd : decodeVarint cur with
  | none =>
    have hnone : (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
      rw [hres_cur, mergeLoopBin_of_decodeVarint_none protoPrefixStep_polynomialDecoder_mergeField hgt_lim hd, Option.map_none]
    apply SepWPp.of_sepWP (mid := (blkPl_296).base + 124#64)
    (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
    apply SepWP.fold (polyBelow_decodeVarint2_entails s0.sp) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPp.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 160#64) 32 ∗ memRegion (s0.sp - 128#64) 48 ∗ polyDecoderErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (by dsimp only [polyDecoderErrFrame]; sep_entail)
    exact herr0_exit hnone hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm]) hsm1
      ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨key, rest⟩
    have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd; have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
    have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le; have hrest_suf : IsDropSuffix x.bs rest :=
      suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
    let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
    by_cases hk_ge : 2 ^ 32 ≤ key.toNat
    · have hnone : (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
        rw [hres_cur, mergeLoopBin_of_key_ge protoPrefixStep_polynomialDecoder_mergeField hgt_lim hd hk_ge, Option.map_none]
      have hshr := key_shr32_of_ge hk_ge
      apply SepWPp.of_sepWP (mid := (blkPl_296).base + 112#64)
      (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
      apply SepWP.fold (polyBelow_decodeVarint2_entails s0.sp) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
      (conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_cells2_160 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
      apply SepWP.exists_elim; intro v_err1; apply SepWP.exists_elim; intro v_err0
      wp_steps
      apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
      apply SepWP.fold (cells2_memRegion32_entails_40_160 s0.sp key) (by sep_focus); wp_reach
      apply SepWPp.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000004#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 160#64) 32 ∗ polyDecoderErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (by dsimp only [polyDecoderErrFrame]; sep_entail)
      exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000004#64) hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
        ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
    · have hshr := key_shr32_of_lt hk_ge
      cases hwt : WireType.ofNat? (key.toNat % 8) with
      | none =>
        have hnone : (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
          rw [hres_cur, mergeLoopBin_of_wt_none protoPrefixStep_polynomialDecoder_mergeField hgt_lim hd hk_ge hwt, Option.map_none]
        obtain ⟨hcs1, hcs2⟩ := key_wt_none hwt
        apply SepWPp.of_sepWP (mid := (blkPl_296).base + 112#64)
        (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
        apply SepWP.fold (polyBelow_decodeVarint2_entails s0.sp) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
        (conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_cells2_160 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro v_err1; apply SepWP.exists_elim; intro v_err0; wp_steps
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        apply SepWP.fold (cells2_memRegion32_entails_40_160 s0.sp (key &&& 7#64)) (by sep_focus); wp_reach
        apply SepWPp.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000003#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 160#64) 32 ∗ polyDecoderErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (by dsimp only [polyDecoderErrFrame]; sep_entail)
        exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000003#64) hsp_align
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
          ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
      | some iwt =>
        obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
        obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_ge
        obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
        by_cases hitag0 : key.toNat / 8 < 1
        · have hnone : (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
            rw [hres_cur, mergeLoopBin_of_tag_zero protoPrefixStep_polynomialDecoder_mergeField hgt_lim hd hk_ge hwt hitag0, Option.map_none]
          have htag_zero : key.toNat / 8 = 0 := by omega
          apply SepWPp.of_sepWP (mid := (blkPl_296).base + 112#64)
          (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
          apply SepWP.fold (polyBelow_decodeVarint2_entails s0.sp) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          (conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_cells1_160 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
          apply SepWP.exists_elim; intro v_err0; wp_steps
          apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus); wp_reach
          apply SepWPp.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000005#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 160#64) 32 ∗ polyDecoderErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (by dsimp only [polyDecoderErrFrame]; sep_entail)
          exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000005#64) hsp_align
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
            ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
        · obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_ge hitag0
          have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
            rw [beq_eq_false_iff_ne]; intro h; have h1 := congrArg BitVec.toNat h
            simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1; omega
          apply SepWPp.of_sepWP_lscro (mid := (blkPl_296).base + 216#64) hinvm
          (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
          apply SepWP.fold (polyBelow_decodeVarint2_entails s0.sp) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          wp_steps; wp_reach; intro hinvm
          apply SepWPp.weaken_pre (P' := polyDecoderLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest) (by dsimp only [polyDecoderLoopPre]; sep_entail)
          exact hcont key iwt rest _ hd hk_ge hwt hitag0
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
            (by simp only [arm64_norm, hsm1, hand_wt]) (by simp only [arm64_norm, hsm1, hw1, hw1_2, hw1_zext1, hw1_zext2])
            (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
            (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
            (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m])
            ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm

/-- Placed main loop induction for `PolynomialDecoder::merge` at `+0x0a4` (`(blkPl_296).base + 164#64`). -/
theorem polyDecoder_loop_ok_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 261) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 291) (decodeVarint2Spec A))
    (hSkipCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 263) (skipField3Spec A))
    (hBytesCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A)))
    (hGrowCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 621) (withLsCodeRoLoaded lsmpl (growOneVecU8Spec A)))
    {x : PolyDecoderMergeGhost} {R : SepProp} {s0 : State} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hlim_lt : limit < 2 ^ 63) :
    ∀ (n : Nat) (m : PolynomialDecoder) (cur : List (BitVec 8)) (s : State),
      cur.length ≤ n → cur.length ≤ x.bs.length → m.pts.length + cur.length < 2 ^ 56 → IsDropSuffix x.bs cur →
      (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
        (mergeLoopBin PolynomialDecoder.mergeField (cur.length - limit) m cur limit 97).map
          (fun m' => (m', x.bs.drop (x.bs.length - limit))) →
      s.pc = (blkPl_296).base + 164#64 →
      s.status = .Running → s.sp = s0.sp - 160#64 → s.trace = s0.trace →
      s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s.readReg64 (Reg.gpr 23#5) = 1#64 → s.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s → LibsignalCodeRoLoaded lsmpl s.mem →
      SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s
        (polyDecoderLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
        (WppPost (polyDecoderMergeSpec A) x R s0) (WppPanic R s0) := by
  have htag1_step := fun {s m rest iwt} => @polyDecoder_tag1_step_placed _ A H hFromCall hPushCall hVarintCall x R s0 s m rest iwt limit
  have htag2_step := fun {s m rest iwt} => @polyDecoder_tag2_step_placed _ A H hFromCall hPushCall hVarintCall x R s0 s m rest iwt limit
  have htag3_step := fun {s m rest iwt} => @polyDecoder_tag3_step_placed _ A H hFromCall hPushCall hBytesCall hGrowCall x R s0 s m rest iwt limit
  have htag4_step := fun {s m rest iwt} => @polyDecoder_tag4_step_placed _ A H hFromCall hPushCall hVarintCall x R s0 s m rest iwt limit
  have hskip_step := fun {s m rest tag iwt} => @polyDecoder_skip_step_placed _ A H hSkipCall x R s0 s m rest tag iwt limit
  intro n; induction n with
  | zero =>
    intro m cur s hcur_n hcur_le _ hcur_suf hres_cur hpc hrun hsp htr _ _ hx21 hx22 _ _ hcs _
    exact polyDecoder_loop_le_exit_placed hFromCall (by omega) hsp_align hcur_le hcur_suf hlim_lt
      hres_cur hpc hrun hsp htr hx21 hx22 hcs
  | succ n ih =>
    intro m cur s hcur_n hcur_le hpts_bound hcur_suf hres_cur hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hcs hinv
    by_cases hle_lim : cur.length ≤ limit
    · exact polyDecoder_loop_le_exit_placed hFromCall hle_lim hsp_align hcur_le hcur_suf hlim_lt
        hres_cur hpc hrun hsp htr hx21 hx22 hcs
    · have hcur_lt : cur.length < 2 ^ 63 := by omega
      refine polyDecoder_decode_key_step_placed hFromCall hVarintCall hle_lim hsp_align
        hcur_le hcur_lt hcur_suf hres_cur ?_ hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hcs hinv
      intro key iwt rest s' hd hk_ge hwt hitag0 hpc' hrun' hsp' htr' hx0' hx1' hx19' hx20' hx21' hx22' hx23' hx24' hcs' hinv'
      obtain ⟨hx26', hx27', hx28', hvregs'⟩ := hcs'
      have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd; have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
      have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le; have hrest_lt : rest.length < 2 ^ 63 := by omega
      have hrest_suf : IsDropSuffix x.bs rest := suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
      have hloop_ok := mergeLoopBin_of_key_ok (m := m) (depth' := 97) protoPrefixStep_polynomialDecoder_mergeField hle_lim hd hk_ge hwt hitag0
      by_cases htag1 : key.toNat / 8 = 1
      · rw [htag1] at hx1' hloop_ok; rw [polynomialDecoder_mergeField_tag1] at hloop_ok
        apply SepWPp.of_sepWP_lscro (mid := (blkPl_296).base + 344#64) hinv'; wp_steps; wp_reach; intro hinv'
        refine htag1_step hsp_align hrest_le hrest_lt hrest_suf
          (fun (hiwt : iwt ≠ .varint) => by simp only [hres_cur, hloop_ok, hiwt, ↓reduceIte, Option.map_none])
          (fun (hiwt : iwt = .varint) (hdv : decodeVarint rest = none) => by simp only [hres_cur, hloop_ok, hiwt, ↓reduceIte, hdv, Option.map_none])
          (fun v rest' s'' hiwt hdv hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hcs'' hinv'' => ?_)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
          (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
          (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23']) (by simp only [arm64_norm, hx24'])
          ⟨by simp only [arm64_norm, hx26'], by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩ hinv'
        have hrest'_lt : rest'.length < rest.length := decodeVarint_length hdv; have hrest'_le_rest : rest'.length ≤ rest.length := Nat.le_of_lt hrest'_lt
        have hres_next : (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
            (mergeLoopBin PolynomialDecoder.mergeField (rest'.length - limit) { m with ptsNeeded := v.truncate 32 } rest' limit 97).map
              (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
          simp only [hres_cur, hloop_ok, hiwt, ↓reduceIte, hdv, Option.map_some]
        exact ih { m with ptsNeeded := v.truncate 32 } rest' s'' (by omega) (by omega) (by dsimp; omega)
          (suffix_trans hrest_le hrest_suf hrest'_le_rest (decodeVarint_suffix hdv))
          hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hcs'' hinv''
      · by_cases htag2 : key.toNat / 8 = 2
        · rw [htag2] at hx1' hloop_ok; rw [polynomialDecoder_mergeField_tag2] at hloop_ok
          apply SepWPp.of_sepWP_lscro (mid := (blkPl_296).base + 240#64) hinv'; wp_steps; wp_reach; intro hinv'
          refine htag2_step hsp_align hrest_le hrest_lt hrest_suf
            (fun (hiwt : iwt ≠ .varint) => by simp only [hres_cur, hloop_ok, hiwt, ↓reduceIte, Option.map_none])
            (fun (hiwt : iwt = .varint) (hdv : decodeVarint rest = none) => by simp only [hres_cur, hloop_ok, hiwt, ↓reduceIte, hdv, Option.map_none])
            (fun v rest' s'' hiwt hdv hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hcs'' hinv'' => ?_)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
            (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
            (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23']) (by simp only [arm64_norm, hx24'])
            ⟨by simp only [arm64_norm, hx26'], by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩ hinv'
          have hrest'_lt : rest'.length < rest.length := decodeVarint_length hdv; have hrest'_le_rest : rest'.length ≤ rest.length := Nat.le_of_lt hrest'_lt
          have hres_next : (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
              (mergeLoopBin PolynomialDecoder.mergeField (rest'.length - limit) { m with polys := v.truncate 32 } rest' limit 97).map
                (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
            simp only [hres_cur, hloop_ok, hiwt, ↓reduceIte, hdv, Option.map_some]
          exact ih { m with polys := v.truncate 32 } rest' s'' (by omega) (by omega) (by dsimp; omega)
            (suffix_trans hrest_le hrest_suf hrest'_le_rest (decodeVarint_suffix hdv))
            hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hcs'' hinv''
        · by_cases htag3 : key.toNat / 8 = 3
          · rw [htag3] at hx1' hloop_ok; rw [polynomialDecoder_mergeField_tag3] at hloop_ok
            apply SepWPp.of_sepWP_lscro (mid := (blkPl_296).base + 376#64) hinv'; wp_steps; wp_reach; intro hinv'
            have hnone_mb : mergeBytes iwt rest = none →
                (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
              intro hmb; simp only [hres_cur, hloop_ok, hmb, Option.map_none]
            refine htag3_step hsp_align hrest_le (by omega) hrest_suf hnone_mb
              (fun v rest' s'' hmb hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hcs'' hinv'' => ?_)
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
              (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
              (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23']) (by simp only [arm64_norm, hx24'])
              ⟨by simp only [arm64_norm, hx26'], by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩ hinv'
            have hrest'_le_rest : rest'.length ≤ rest.length := mergeBytes_length hmb
            have hres_next : (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
                (mergeLoopBin PolynomialDecoder.mergeField (rest'.length - limit) { m with pts := m.pts ++ [v] } rest' limit 97).map
                  (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
              simp only [hres_cur, hloop_ok, hmb, Option.map_some]
            exact ih { m with pts := m.pts ++ [v] } rest' s'' (by omega) (by omega) (by simp; omega)
              (suffix_trans hrest_le hrest_suf hrest'_le_rest (mergeBytes_suffix hmb))
              hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hcs'' hinv''
          · by_cases htag4 : key.toNat / 8 = 4
            · rw [htag4] at hx1' hloop_ok; rw [polynomialDecoder_mergeField_tag4] at hloop_ok
              apply SepWPp.of_sepWP_lscro (mid := (blkPl_296).base + 288#64) hinv'; wp_steps; wp_reach; intro hinv'
              refine htag4_step hsp_align hrest_le hrest_lt hrest_suf
                (fun (hiwt : iwt ≠ .varint) => by simp only [hres_cur, hloop_ok, hiwt, ↓reduceIte, Option.map_none])
                (fun (hiwt : iwt = .varint) (hdv : decodeVarint rest = none) => by simp only [hres_cur, hloop_ok, hiwt, ↓reduceIte, hdv, Option.map_none])
                (fun v rest' s'' hiwt hdv hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hcs'' hinv'' => ?_)
                (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
                (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
                (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23']) (by simp only [arm64_norm, hx24'])
                ⟨by simp only [arm64_norm, hx26'], by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩ hinv'
              have hrest'_lt : rest'.length < rest.length := decodeVarint_length hdv; have hrest'_le_rest : rest'.length ≤ rest.length := Nat.le_of_lt hrest'_lt
              have hres_next : (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
                  (mergeLoopBin PolynomialDecoder.mergeField (rest'.length - limit) { m with isComplete := v != 0#64 } rest' limit 97).map
                    (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
                simp only [hres_cur, hloop_ok, hiwt, ↓reduceIte, hdv, Option.map_some]
              exact ih { m with isComplete := v != 0#64 } rest' s'' (by omega) (by omega) (by dsimp; omega)
                (suffix_trans hrest_le hrest_suf hrest'_le_rest (decodeVarint_suffix hdv))
                hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hcs'' hinv''
            · have hitag_lt : key.toNat / 8 < 2 ^ 32 := by omega
              obtain ⟨hslt1, hslt2⟩ := slt_two_ofNat32_true (n := key.toNat / 8) (by omega) (by omega)
              obtain ⟨hb3_1, _⟩ := itag_beq_tag_false htag3 hitag_lt (by decide : 3 < 2 ^ 32)
              obtain ⟨hb4_1, _⟩ := itag_beq_tag_false htag4 hitag_lt (by decide : 4 < 2 ^ 32)
              have hb3_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 3#32) = false := by rw [sf_truncate32_ofNat64]; exact hb3_1
              have hb4_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 4#32) = false := by rw [sf_truncate32_ofNat64]; exact hb4_1
              have hb4_bne1 : (BitVec.ofNat 32 (key.toNat / 8) != 4#32) = true := by simp only [bne, hb4_1, Bool.not_false]
              have hb4_bne2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) != 4#32) = true := by simp only [bne, hb4_2, Bool.not_false]
              rw [polynomialDecoder_mergeField_other m iwt rest 97 hitag_lt htag1 htag2 htag3 htag4] at hloop_ok
              apply SepWPp.of_sepWP_lscro (mid := (blkPl_296).base + 320#64) hinv'; wp_steps; wp_reach; intro hinv'
              have hnone_sf : skipField (2 * rest.length + 2) 97 (key.toNat / 8) iwt rest = none →
                  (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
                intro hsf; rw [hres_cur, hloop_ok, hsf]; rfl
              refine hskip_step hsp_align hrest_le hrest_lt hrest_suf hitag_lt hnone_sf
                (fun rest' s'' hsf hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hcs'' hinv'' => ?_)
                (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
                (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx1', sf_truncate32_ofNat64])
                (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
                (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23']) (by simp only [arm64_norm, hx24'])
                ⟨by simp only [arm64_norm, hx26'], by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩ hinv'
              have hrest'_le_rest : rest'.length ≤ rest.length := (skip_length (2 * rest.length + 2)).1 _ _ _ _ _ hsf
              have hres_next : (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
                  (mergeLoopBin PolynomialDecoder.mergeField (rest'.length - limit) m rest' limit 97).map
                    (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
                rw [hres_cur, hloop_ok, hsf]; rfl
              exact ih m rest' s'' (by omega) (by omega) (by omega)
                (suffix_trans hrest_le hrest_suf hrest'_le_rest ((skip_suffix (2 * rest.length + 2)).1 _ _ _ _ _ hsf))
                hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hcs'' hinv''

/-- Contract-parameterized placed verification of `prost::encoding::message::merge::<PolynomialDecoder, &mut &[u8]>` (Block `296`). -/
theorem polyDecoderMerge_placed_ok_of_contracts [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 261) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 291) (decodeVarint2Spec A))
    (hSkipCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 263) (skipField3Spec A))
    (hBytesCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A)))
    (hGrowCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 621) (withLsCodeRoLoaded lsmpl (growOneVecU8Spec A))) :
    subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (blkPl_296).base (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A)) := by
  apply subroutine_ok_withLsCodeRoLoaded_of_withLscroProp; unfold withLscroProp polyDecoderMergeSpec; wpp_init x s0
  apply SepWPp.elim_lscroProp; intro hinv0; replace hpc : s0.pc = (blkPl_296).base := hpc
  conv => arg 6; ext sf P_f; simp only [polyDecoderMergeSpec, sepConj_assoc, satisfies_pure_sepConj]
  change SepWPp _ _ _ _ (WppPost (polyDecoderMergeSpec A) x R s0) (WppPanic R s0)
  have hbs_lt : x.bs.length < 2 ^ 63 := by omega
  have herr0_exit := @polyDecoder_err0_ret_exit_placed _ A H x R s0; have hfrom_exit := @polyDecoder_from_err_exit_placed _ A H hFromCall x R s0
  have hloop := fun {limit n m cur s} hlim_lt =>
    @polyDecoder_loop_ok_placed _ A H hFromCall hPushCall hVarintCall hSkipCall hBytesCall hGrowCall x R s0 limit hsp_align hlim_lt n m cur s
  by_cases hwt_ld : x.wt = .lengthDelimited
  · have h_1' : (s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = 2#8 := by rw [h_1, hwt_ld]; rfl
    have hbeq := wt_beq_two_of_lengthDelimited h_1'
    have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = false := by simp only [bne, hbeq, Bool.not_true]
    have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = false := by
      rw [BytesMergeFacts.truncate32_zeroExtend64_and_255_eq, h_1']; decide
    have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = false := by revert h_1'; bv_bits
    apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 291) hinv0
    (conv => arg 4; rw [stackAt_polyMerge_prologue s0.sp, polyBelow_decodeVarint2 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v1; apply SepWP.exists_elim; intro v2; apply SepWP.exists_elim; intro v3
    apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v5; apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v7
    apply SepWP.exists_elim; intro v8; apply SepWP.exists_elim; intro v9
    wp_steps
    apply SepWP.fold (polySavedRegs_entails_any s0.sp s0 v3) (by unfold polySavedRegs; sep_focus)
    wp_reach; intro hinv0
    refine SepWPp.call_frame_keep_lscro (x := ⟨x.bufRef, x.slot, x.ptr, x.bs⟩)
      (ret_pc := (blkPl_296).base + 56#64) hVarintCall hinv0 (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
      (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, h_3]; rfl) hbs_lt (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm]) hpan) ?_
    intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, h_2, h_3] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
    cases hdv0 : decodeVarint x.bs with
    | none =>
      have hnone : (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
        rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_polynomialDecoder_mergeField]
        simp [mergeMessageBin, codecWireTypeToProto, proto_decodeVarint_toOption, hdv0]
      apply SepWPp.of_sepWP (mid := (blkPl_296).base + 124#64)
      (conv => arg 4; simp only [decodeVarint2Spec, hdv0, sepConj_assoc, arm64_norm]); apply SepWP.pure_elim; rintro ⟨hsm0, htrm, hsm1⟩
      apply SepWP.fold (polyBelow_decodeVarint2_entails s0.sp) (by sep_focus)
      wp_steps; wp_reach
      apply SepWPp.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 160#64) 32 ∗ memRegion (s0.sp - 128#64) 48 ∗ polyDecoderErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs) (by dsimp only [polyDecoderErrFrame]; sep_entail)
      exact herr0_exit hnone hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm])
        (by simp only [arm64_norm]) hsm1
        ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
    | some p =>
      rcases p with ⟨len, rest0⟩
      have hrest0_lt_bs : rest0.length < x.bs.length := decodeVarint_length hdv0; have hrest0_le : rest0.length ≤ x.bs.length := Nat.le_of_lt hrest0_lt_bs
      have hrest0_lt : rest0.length < 2 ^ 63 := Nat.lt_of_lt_of_le hrest0_lt_bs (Nat.le_of_lt hbs_lt)
      have hrest0_suf : IsDropSuffix x.bs rest0 := decodeVarint_suffix hdv0
      let rest0Ptr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length)
      by_cases hlt_len : rest0.length < len.toNat
      · have hule := ule_len_of_lt hlt_len hrest0_lt
        have hnone : (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
          rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_polynomialDecoder_mergeField]
          simp [mergeMessageBin, codecWireTypeToProto, proto_decodeVarint_toOption, hdv0, hlt_len]
        apply SepWPp.of_sepWP (mid := (blkPl_296).base + 112#64)
        (conv => arg 4; simp only [decodeVarint2Spec, hdv0, sepConj_assoc, arm64_norm]); apply SepWP.pure_elim; rintro ⟨⟨hsm0, hsm1⟩, htrm⟩
        apply SepWP.fold (polyBelow_decodeVarint2_entails s0.sp) (by sep_focus)
        (conv => arg 4; rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt, memRegion_48_cells1_160 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro v_stk0; wp_steps
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot rest0Ptr (BitVec.ofNat 64 rest0.length)) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus); wp_reach
        apply SepWPp.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000007#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 160#64) 32 ∗ polyDecoderErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs) (by dsimp only [polyDecoderErrFrame]; sep_entail)
        exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000007#64) hsp_align
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm])
          ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
      · have hule := ule_len_of_ge hlt_len hrest0_lt; have hsub := bv_len_sub_limit hlt_len; have hlim_lt : rest0.length - len.toNat < 2 ^ 63 := by omega
        have hdrop_eq : x.bs.drop (x.bs.length - (rest0.length - len.toNat)) = rest0.drop len.toNat := by
          have hsuf := hrest0_suf; unfold IsDropSuffix at hsuf; conv => rhs; rw [hsuf, List.drop_drop]
          exact congrArg (List.drop · x.bs) (by omega)
        have hres0 : (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
            (mergeLoopBin PolynomialDecoder.mergeField (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 97).map
              (fun m' => (m', x.bs.drop (x.bs.length - (rest0.length - len.toNat)))) := by
          rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_polynomialDecoder_mergeField]
          simp only [mergeMessageBin, codecWireTypeToProto, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, proto_decodeVarint_toOption, hdv0, hlt_len, hdrop_eq]
          rcases mergeLoopBin PolynomialDecoder.mergeField (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 97 with _ | m' <;> rfl
        apply SepWPp.of_sepWP_lscro (mid := (blkPl_296).base + 164#64) hinvm
        (conv => arg 4; simp only [decodeVarint2Spec, hdv0, sepConj_assoc, arm64_norm]); apply SepWP.pure_elim; rintro ⟨⟨hsm0, hsm1⟩, htrm⟩
        apply SepWP.fold (polyBelow_decodeVarint2_entails s0.sp) (by sep_focus)
        (conv => arg 4; rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]; simp only [sepConj_assoc]); wp_steps; wp_reach; intro hinvm
        apply SepWPp.weaken_pre (P' := polyDecoderLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs rest0) (by rw [polyDecoderLoopPre, sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]; sep_entail)
        exact hloop hlim_lt (Nat.le_refl _) hrest0_le (by omega) hrest0_suf hres0
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm])
          (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm]) (by simp only [arm64_norm, hsm1, hsub])
          (by simp only [arm64_norm]) (by simp only [arm64_norm])
          ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm
  · have hbeq := wt_beq_two_of_ne_lengthDelimited h_1 hwt_ld
    have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = true := by simp only [bne, hbeq, Bool.not_false]
    have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = true := by
      rw [BytesMergeFacts.truncate32_zeroExtend64_and_255_eq, h_1]; cases hxwt : x.wt <;> first | exact absurd hxwt hwt_ld | decide
    have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = true := by
      rw [← hbne1]; congr 2; bv_bits
    have hnone : (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
      rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_polynomialDecoder_mergeField]
      cases hxwt : x.wt <;> first | exact absurd hxwt hwt_ld | rfl
    apply SepWPp.of_sepWP (mid := (blkPl_296).base + 112#64)
    conv => arg 4; rw [stackAt_polyMerge_prologue s0.sp, sliceCursorAt, memRegion_48_wtErr160 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v1; apply SepWP.exists_elim; intro v2; apply SepWP.exists_elim; intro v3
    apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v5; apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v7
    apply SepWP.exists_elim; intro v8; apply SepWP.exists_elim; intro v9
    apply SepWP.exists_elim; intro b_wt1; apply SepWP.exists_elim; intro b_wt0; apply SepWP.exists_elim; intro v_wt0
    wp_steps
    apply SepWP.fold (polySavedRegs_entails_any s0.sp s0 v3) (by unfold polySavedRegs; sep_focus)
    apply SepWP.fold (wtErr160_entails_memRegion40 s0.sp _ _) (by sep_focus)
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot x.ptr (BitVec.ofNat 64 x.bs.length)) (by sep_focus)
    wp_reach
    apply SepWPp.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000006#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 160#64) 32 ∗ polyDecoderErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs) (by dsimp only [polyDecoderErrFrame]; sep_entail)
    exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000006#64) hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩

end CryptoVerification.SpqrV1.Prost.MessageMerge

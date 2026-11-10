/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedNoHeaderReceivedUc
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Verification of `Chunked.NoHeaderReceived::merge` (`0x511b4`, Block `308`)

Proves `prost::encoding::message::merge::<spqr::proto::pq_ratchet::v1_state::chunked::NoHeaderReceived, &mut &[u8]>`
against `(chunkedNoHeaderReceivedMergeSpec A).inImage img` and its `[LibsignalPlacement]`
counterpart on Block `308`, composing the inlined `Unchunked.NoHeaderReceived` loop (`tag = 1`)
with `receivingHdr` (`tag = 2`).
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
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Prost.BytesMerge
open CryptoVerification.LibsignalSpqrV1 hiding decodeVarint encodeVarint WireType
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero chunkedNoHeaderReceivedMerge_fnOff

/-! ## 1. Representation & `Option::get_or_insert_with` Helpers for `receivingHdr` and `uc` -/

theorem cap_add_two_beq_zero_false {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 2#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]; intro heq; have h1 := congrArg BitVec.toNat heq; revert h1; bv_omega

theorem cap_add_two_bne_zero_true {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 2#64 != 0#64) = true := by
  simp only [bne, cap_add_two_beq_zero_false h, Bool.not_false]

theorem iwt64_beq_two_of_ne_ld {iwt : WireType} (hne : iwt ≠ .lengthDelimited) :
    (BitVec.ofNat 64 iwt.toNat == 2#64) = false ∧ (BitVec.ofNat 64 iwt.toNat != 2#64) = true := by
  cases iwt <;> simp_all [WireType.toNat]

theorem setWidth8_zext64_trunc32_ofNat64_wt_nhr (wt : WireType) :
    BitVec.setWidth 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 wt.toNat))) =
      BitVec.ofNat 8 wt.toNat := by
  cases wt <;> decide

def polyDecoderRestAt (A : RustAlloc) (a : BitVec 64) (pin : VecPin) (d : PolynomialDecoder) : SepProp :=
  ((a + 8#64) ↦₆₄ pin.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 d.pts.length) ∗
    vecVecU8Buf A pin.cap pin.ptr d.pts ∗ ((a + 24#64) ↦₃₂ d.ptsNeeded) ∗ ((a + 28#64) ↦₃₂ d.polys) ∗
    ((a + 32#64) ↦₈ ProtoRepr.boolByte d.isComplete) ∗ memRegion (a + 33#64) 7

theorem vecVecU8Buf_cap_lt (A : RustAlloc) (cap ptr : BitVec 64) (pts : List (List (BitVec 8))) :
    vecVecU8Buf A cap ptr pts ⊢ ⌜cap.toNat < 2 ^ 63⌝ ∗ vecVecU8Buf A cap ptr pts := by
  unfold vecVecU8Buf vecBuf
  refine Entails.pure_left fun h => ?_
  have hlt : cap.toNat < 2 ^ 63 := by omega
  exact Entails.pure_right hlt (Entails.pure_right h (Entails.refl _))

theorem protoPolynomialDecoderAt_entails_cmn (A : RustAlloc) (a : BitVec 64) (d : PolynomialDecoder) :
    protoPolynomialDecoderAt A a (polyDecoderToProto d) ⊢
      ∃∗ pin : VecPin, ⌜pin.cap.toNat < 2 ^ 63⌝ ∗ (a ↦₆₄ pin.cap) ∗ polyDecoderRestAt A a pin d := by
  rw [← optPolynomialDecoderPBAt_some_eq]; dsimp only [optPolynomialDecoderPBAt, polynomialDecoderPBAt, polyDecoderRestAt]
  rw [vecVecU8At_eq_exists_pin, sepExists_sepConj_left]; refine ProofLib.Entails.sepExists_elim fun pin => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro pin)
  rw [vecVecU8PinnedAt_eq_header_buf]
  refine Entails.trans (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (vecVecU8Buf_cap_lt A pin.cap pin.ptr d.pts))))) ?_
  sep_entail

theorem cmn_entails_protoPolynomialDecoderAt (A : RustAlloc) (a : BitVec 64) (pin : VecPin) (d : PolynomialDecoder) :
    (a ↦₆₄ pin.cap) ∗ polyDecoderRestAt A a pin d ⊢
      protoPolynomialDecoderAt A a (polyDecoderToProto d) := by
  rw [← optPolynomialDecoderPBAt_some_eq]; dsimp only [optPolynomialDecoderPBAt, polynomialDecoderPBAt, polyDecoderRestAt]
  rw [vecVecU8At_eq_exists_pin]
  refine Entails.trans (Entails.of_eq (show _ = (((a ↦₆₄ pin.cap) ∗ ((a + 8#64) ↦₆₄ pin.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 d.pts.length)) ∗ vecVecU8Buf A pin.cap pin.ptr d.pts) ∗ ((a + 24#64) ↦₃₂ d.ptsNeeded) ∗ ((a + 28#64) ↦₃₂ d.polys) ∗ ((a + 32#64) ↦₈ ProtoRepr.boolByte d.isComplete) ∗ memRegion (a + 33#64) 7 by ac_rfl)) ?_
  refine sepConj_mono_left ?_
  refine Entails.trans ?_ (Entails.sepExists_intro pin)
  rw [vecVecU8PinnedAt_eq_header_buf]; simp only [sepConj_assoc]; exact Entails.refl _

/-! ## 2. Outer Loop Step Lemmas -/

/-- Outer loop `skip_field` step at `+0x15c` (`entry + 348#64`) for unknown tags (`tag ∉ {1, 2}`, `depth' = 98`). -/
theorem chunkedNoHeaderReceived_skip_step {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hSkipCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 0xffffffffffffa9c0#64) (skipField3Spec A))
    {x : ChunkedNoHeaderReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.NoHeaderReceived} {rest : List (BitVec 8)} {iwt : WireType} {tag outerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest) (htag_lt : tag < 2 ^ 32)
    (hnone_of_skip : skipField (2 * rest.length + 2) 98 tag iwt rest = none →
      (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (rest' : List (BitVec 8)) (s' : State),
      skipField (2 * rest.length + 2) 98 tag iwt rest = some rest' →
      s'.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 168#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s'
        (chunkedNoHeaderReceivedLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest')
        (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 348#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx8 : s.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : (s.readReg64 (Reg.gpr 1#5)).setWidth 32 = BitVec.ofNat 32 tag)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
      (chunkedNoHeaderReceivedLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hret_err := @chunkedNoHeaderReceived_ret_err_exit img A H x R s0 m
  chunkedNoHeaderReceivedMerge_fetches img.base H 348 24
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName = entry; examples_hide_fetches
  apply SepWPpIn.of_sepWP (mid := entry + 0xffffffffffffa9c0#64)
  conv => arg 4; rw [chunkedNoHeaderReceivedLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
    chunkedInlBelow_skipField98 s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpIn.call_frame (x := ⟨iwt, tag, 98, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := entry + 364#64) hSkipCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [skipField3Spec]; simp only [arm64_norm, hsp, hx8, hx1, hx19, setWidth8_zext64_trunc32_ofNat64_wt_nhr]; rfl)
    (⟨htag_lt, by decide, hrest_lt⟩ : tag < 2 ^ 32 ∧ 98 < 2 ^ 32 ∧ rest.length < 2 ^ 63) (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx27_m hx28_m hvregs_m
  cases hsf : skipField (2 * rest.length + 2) 98 tag iwt rest with
  | none =>
    have hnone := hnone_of_skip hsf
    apply SepWPpIn.of_sepWP (mid := entry + 128#64)
    (conv => arg 4; simp only [skipField3Spec, hsf, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    have hcbz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (chunkedInlBelow_skipField98_entails s0.sp) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (chunkedNoHeaderReceivedPBCapAt_entails_pb A x.msgPtr rest.length m) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPpIn.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (by dsimp only [chunkedNoHeaderReceivedErrFrame]; sep_entail)
    exact hret_err hnone (by decide : 0 ≤ 3) hsm0 hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])
      ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some rest' =>
    have hrest'_le : rest'.length ≤ rest.length := (skip_length _).1 _ _ _ _ _ hsf
    apply SepWPpIn.of_sepWP (mid := entry + 168#64)
    (conv => arg 4; simp only [skipField3Spec, hsf, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    apply SepWP.fold (chunkedInlBelow_skipField98_entails s0.sp) (by sep_focus)
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (chunkedNoHeaderReceivedPBCapAt_mono A x.msgPtr m hrest'_le) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPpIn.weaken_pre (P' := chunkedNoHeaderReceivedLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest')
      (by dsimp only [chunkedNoHeaderReceivedLoopPre]; sep_entail)
    exact hcont rest' _ hsf (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m])
      (by simp only [arm64_norm, hx22_m]) (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m])
      (by simp only [arm64_norm, hx25_m])
      ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

/-- Initializes `m.receivingHdr` (`Option::get_or_insert_with(Default::default)`) at `+0x0f4` (`entry + 244#64`)
to `+0x10c` (`entry + 268#64`). -/
theorem chunkedNoHeaderReceived_hdr_init {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    {x : ChunkedNoHeaderReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.NoHeaderReceived} {rest : List (BitVec 8)}
    (hcont : ∀ (s' : State),
      s'.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 268#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s.trace →
      s'.readReg64 (Reg.gpr 8#5) = s.readReg64 (Reg.gpr 8#5) →
      s'.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) → s'.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) →
      s'.readReg64 (Reg.gpr 23#5) = s.readReg64 (Reg.gpr 23#5) → s'.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s'
        (protoPolynomialDecoderAt A x.msgPtr (polyDecoderToProto (m.receivingHdr.getD default)) ∗
          optNoHeaderReceivedPBCapAt A (x.msgPtr + 0x28#64) rest.length m.uc ∗
          stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗
          chunkedInlSavedRegs10 s0.sp s0 ∗ (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool)
        (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 244#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr) (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
      (chunkedNoHeaderReceivedLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; chunkedNoHeaderReceivedMerge_fetches img.base H 244 24
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName = entry; examples_hide_fetches
  rcases hhdr : m.receivingHdr with _ | d
  · rw [hhdr] at hcont
    apply SepWPpIn.of_sepWP (mid := entry + 268#64)
    conv => arg 4; rw [chunkedNoHeaderReceivedLoopPre, chunkedNoHeaderReceivedPBCapAt, hhdr,
      optPolynomialDecoderPBAt, memRegion_polyDecoder_none_split_inl x.msgPtr]
    simp only [noneCap, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm]
    apply SepWP.exists_elim; intro b32; apply SepWP.exists_elim; intro v24
    apply SepWP.exists_elim; intro v16; apply SepWP.exists_elim; intro v8
    wp_steps
    apply SepWP.fold (default_polyDecoder_entails_pb_inl A x.msgPtr) (by sep_focus); wp_reach
    apply SepWPpIn.weaken_pre (P' := protoPolynomialDecoderAt A x.msgPtr (polyDecoderToProto (Option.getD none default)) ∗ optNoHeaderReceivedPBCapAt A (x.msgPtr + 0x28#64) rest.length m.uc ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedInlSavedRegs10 s0.sp s0 ∗ (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool)
      (Entails.of_eq rfl)
    exact hcont _ (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
      (by try simp only [arm64_norm]) (by try simp only [arm64_norm]) (by try simp only [arm64_norm])
      (by simp only [arm64_norm, hx20]) (by try simp only [arm64_norm]) (by try simp only [arm64_norm])
      (by try simp only [arm64_norm]) (by try simp only [arm64_norm]) (by simp only [arm64_norm, hx25])
      ⟨by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩
  · rw [hhdr] at hcont
    apply SepWPpIn.of_sepWP (mid := entry + 268#64)
    conv => arg 4; rw [chunkedNoHeaderReceivedLoopPre, chunkedNoHeaderReceivedPBCapAt, hhdr, optPolynomialDecoderPBAt_some_eq]
    simp only [sepConj_assoc, arm64_norm]
    apply SepWP.fold (protoPolynomialDecoderAt_entails_cmn A x.msgPtr d) (by sep_focus)
    wp_simp_pre [sepExists_sepConj_left, sepConj_assoc, arm64_norm]
    apply SepWP.exists_elim; intro pin; apply SepWP.pure_elim; intro hcap_lt
    have hcmn1 := cap_add_one_beq_zero_false hcap_lt; have hcmn2 := cap_add_one_bne_zero_true hcap_lt
    wp_steps
    apply SepWP.fold (cmn_entails_protoPolynomialDecoderAt A x.msgPtr pin d) (by sep_focus); wp_reach
    apply SepWPpIn.weaken_pre (P' := protoPolynomialDecoderAt A x.msgPtr (polyDecoderToProto (Option.getD (some d) default)) ∗ optNoHeaderReceivedPBCapAt A (x.msgPtr + 0x28#64) rest.length m.uc ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedInlSavedRegs10 s0.sp s0 ∗ (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool)
      (Entails.of_eq rfl)
    exact hcont _ (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
      (by try simp only [arm64_norm]) (by try simp only [arm64_norm]) (by try simp only [arm64_norm])
      (by simp only [arm64_norm, hx20]) (by try simp only [arm64_norm]) (by try simp only [arm64_norm])
      (by try simp only [arm64_norm]) (by try simp only [arm64_norm]) (by simp only [arm64_norm, hx25])
      ⟨by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩

/-- Outer loop tag 2 (`receivingHdr : Option<PolynomialDecoder>`) step at `+0x0f4` (`entry + 244#64`). -/
theorem chunkedNoHeaderReceived_tag2_step {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 0xffffffffffff98f4#64) (decodeErrorPushSpec A))
    (hPolyCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 0xffffffffffffcf58#64) ((polyDecoderMergeSpec A).inImage img))
    {x : ChunkedNoHeaderReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.NoHeaderReceived} {rest : List (BitVec 8)} {iwt : WireType} {outerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_suf : IsDropSuffix x.bs rest) (hbound : OptPolyDecoderBound m.receivingHdr rest.length)
    (hnone_of_poly :
      (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto iwt) (m.receivingHdr.getD default) rest 98).toOption = none →
      (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (d' : PolynomialDecoder) (rest' : List (BitVec 8)) (s' : State),
      (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto iwt) (m.receivingHdr.getD default) rest 98).toOption = some (d', rest') →
      s'.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 168#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s'
        (chunkedNoHeaderReceivedLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with receivingHdr := some d' } x.bs rest')
        (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 244#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx8 : s.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
      (chunkedNoHeaderReceivedLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  have hpush_ret := fun {d' : PolynomialDecoder} => @chunkedNoHeaderReceived_push_ret_exit img A H hPushCall x R s0 { receivingHdr := some d', uc := m.uc }
  refine chunkedNoHeaderReceived_hdr_init ?_ hpc hrun hsp hx20 hx25 hcs
  intro s1 hpc1 hrun1 hsp1 htr1 hx8_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hcs1
  rw [htr] at htr1; rw [hx8] at hx8_1; rw [hx19] at hx19_1; rw [hx21] at hx21_1
  rw [hx22] at hx22_1; rw [hx23] at hx23_1; rw [hx24] at hx24_1
  obtain ⟨hx27_1, hx28_1, hvregs_1⟩ := hcs1
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  chunkedNoHeaderReceivedMerge_fetches img.base H 268 24; chunkedNoHeaderReceivedMerge_fetches img.base H 784 36
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName = entry; examples_hide_fetches
  apply SepWPpIn.of_sepWP (mid := entry + 0xffffffffffffcf58#64)
  conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, chunkedInlBelow_eq_polyMerge s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpIn.call_frame_inImage (x := ⟨iwt, x.msgPtr, m.receivingHdr.getD default, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := entry + 284#64) hPolyCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
    (by simp only [State.spAligned, hsp1, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [polyDecoderMergeSpec]; simp only [arm64_norm, hsp1, hx8_1, hx20_1, hx19_1, setWidth8_zext64_trunc32_ofNat64_wt_nhr]; rfl)
    hbound (by sep_focus) (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [polyDecoderMergeSpec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr1]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx27_1, hx28_1, hvregs_1] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx27_m hx28_m hvregs_m
  cases hpoly_res : (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto iwt) (m.receivingHdr.getD default) rest 98).toOption with
  | none =>
    have hnone := hnone_of_poly hpoly_res
    apply SepWPpIn.of_sepWP (mid := entry + 728#64)
    (conv => arg 4; simp only [polyDecoderMergeSpec, hpoly_res, memRegion_48_cells1_160 s0.sp,
      ← chunkedInlBelow_eq_polyMerge s0.sp,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp1])
    apply SepWP.exists_elim; intro v_stk0; apply SepWP.exists_elim; intro d'; apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; intro hpure
    have htrm : sm.trace = _ := hpure.1; have hsm0 : sm.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hpure.2.1; have hn_err : n_err ≤ 1 := hpure.2.2
    have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (optNoHeaderReceivedPBCapAt_entails A (x.msgPtr + 0x28#64) rest.length m.uc) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPpIn.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { receivingHdr := some d', uc := m.uc } x.bs)
      (by dsimp only [chunkedNoHeaderReceivedErrFrame, chunkedNoHeaderReceivedPBAt]; rw [optPolynomialDecoderPBAt_some_eq]; sep_entail)
    exact hpush_ret hnone (by omega : n_err ≤ 2) hsm0 hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr1]) (by simp only [arm64_norm, hspm])
      ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨d', rest'⟩
    have hrest'_le : rest'.length ≤ rest.length := (proto_mergeMessage_suffix hpoly_res).1
    apply SepWPpIn.of_sepWP (mid := entry + 168#64)
    (conv => arg 4; simp only [polyDecoderMergeSpec, hpoly_res, ← chunkedInlBelow_eq_polyMerge s0.sp,
      sepConj_assoc, arm64_norm, hsp1])
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (optNoHeaderReceivedPBCapAt_mono A (x.msgPtr + 0x28#64) m.uc hrest'_le) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPpIn.weaken_pre (P' := chunkedNoHeaderReceivedLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with receivingHdr := some d' } x.bs rest')
      (by dsimp only [chunkedNoHeaderReceivedLoopPre, chunkedNoHeaderReceivedPBCapAt]; rw [optPolynomialDecoderPBAt_some_eq]; sep_entail)
    exact hcont d' rest' _ hpoly_res
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr1])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m])
      (by simp only [arm64_norm, hx22_m]) (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m])
      (by simp only [arm64_norm, hx25_m])
      ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

/-- Prepares `chunkedNoHeaderReceivedLoopPre` at `+0x128` (`entry + 296#64`) into `chunkedNoHeaderReceivedUcLoopPre` at `+0x13c` (`entry + 316#64`). -/
theorem chunkedNoHeaderReceived_uc_init {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    {x : ChunkedNoHeaderReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.NoHeaderReceived} {rest : List (BitVec 8)}
    (hcont : ∀ (s' : State),
      s'.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 316#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s.trace →
      s'.readReg64 (Reg.gpr 8#5) = s.readReg64 (Reg.gpr 8#5) →
      s'.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) → s'.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) →
      s'.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s'
        (chunkedNoHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m.receivingHdr (m.uc.getD default) x.bs rest)
        (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 296#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr) (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
      (chunkedNoHeaderReceivedLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; chunkedNoHeaderReceivedMerge_fetches img.base H 296 20
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName = entry; examples_hide_fetches
  rcases huc : m.uc with _ | uc
  · rw [huc] at hcont; dsimp only [Option.getD] at hcont
    apply SepWPpIn.of_sepWP (mid := entry + 316#64)
    conv => arg 4; rw [chunkedNoHeaderReceivedLoopPre, chunkedNoHeaderReceivedPBCapAt, huc, optNoHeaderReceivedPBCapAt, memRegion_48_split_40_8 (x.msgPtr + 40#64)]
    simp only [noneCap2, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm]
    apply SepWP.exists_elim; intro v48; wp_steps
    have hdef : ((x.msgPtr + 40#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (x.msgPtr + 48#64) 40 ∗ ((x.msgPtr + 88#64) ↦₆₄ 0#64) ⊢
        unchunked2CapAt A (x.msgPtr + 40#64) rest.length
          (default : V1State.Unchunked.NoHeaderReceived).epoch
          (default : V1State.Unchunked.NoHeaderReceived).auth := by
      change ((x.msgPtr + 40#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (x.msgPtr + 48#64) 40 ∗ ((x.msgPtr + 88#64) ↦₆₄ 0#64) ⊢
        unchunked2CapAt A (x.msgPtr + 40#64) rest.length 0#64 none
      simpa only [noneCap, arm64_norm] using default_unchunked2_entails_cap A (x.msgPtr + 40#64) rest.length
    apply SepWP.fold hdef (by sep_focus); wp_reach
    apply SepWPpIn.weaken_pre (P' := chunkedNoHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m.receivingHdr default x.bs rest)
      (by dsimp only [chunkedNoHeaderReceivedUcLoopPre]; sep_entail)
    exact hcont _ (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
      (by try simp only [arm64_norm]) (by try simp only [arm64_norm]) (by try simp only [arm64_norm])
      (by simp only [arm64_norm, hx20]) (by try simp only [arm64_norm]) (by try simp only [arm64_norm])
      (by simp only [arm64_norm, hx23]) (by try simp only [arm64_norm]) (by try simp only [arm64_norm])
      ⟨by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩
  · rw [huc] at hcont; dsimp only [Option.getD] at hcont
    rcases hauth : uc.auth with _ | auth
    · apply SepWPpIn.of_sepWP (mid := entry + 316#64)
      conv => arg 4; rw [chunkedNoHeaderReceivedLoopPre, chunkedNoHeaderReceivedPBCapAt, huc, optNoHeaderReceivedPBCapAt,
        unchunked2CapAt, hauth, optAuthenticatorPBCapAt]
      simp only [noneCap, sepConj_assoc, arm64_norm]; wp_steps; wp_reach
      apply SepWPpIn.weaken_pre (P' := chunkedNoHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m.receivingHdr uc x.bs rest)
        (by dsimp only [chunkedNoHeaderReceivedUcLoopPre, unchunked2CapAt]; rw [hauth, optAuthenticatorPBCapAt, noneCap]; simp only [arm64_norm]; sep_entail)
      exact hcont _ (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
        (by try simp only [arm64_norm]) (by try simp only [arm64_norm]) (by try simp only [arm64_norm])
        (by simp only [arm64_norm, hx20]) (by try simp only [arm64_norm]) (by try simp only [arm64_norm])
        (by simp only [arm64_norm, hx23]) (by try simp only [arm64_norm]) (by try simp only [arm64_norm])
        ⟨by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩
    · apply SepWPpIn.of_sepWP (mid := entry + 316#64)
      conv => arg 4; rw [chunkedNoHeaderReceivedLoopPre, chunkedNoHeaderReceivedPBCapAt, huc, optNoHeaderReceivedPBCapAt,
        unchunked2CapAt, hauth, optAuthenticatorPBCapAt]
      simp only [sepConj_assoc, arm64_norm]
      have hcmn_in := authenticatorPBCapAt_entails_cmn A (x.msgPtr + 40#64) rest.length auth
      simp only [arm64_norm] at hcmn_in; apply SepWP.fold hcmn_in (by sep_focus)
      wp_simp_pre [sepExists_sepConj_left, sepConj_assoc, arm64_norm]
      apply SepWP.exists_elim; intro cap_ik; apply SepWP.exists_elim; intro ptr_ik
      apply SepWP.pure_elim; rintro ⟨hcap_lt, hcap_ik⟩
      have hcmn1 := cap_add_two_beq_zero_false hcap_lt; have hcmn2 := cap_add_two_bne_zero_true hcap_lt
      wp_steps
      have hcmn_out := cmn_entails_authenticatorPBCapAt A (x.msgPtr + 40#64) rest.length auth cap_ik ptr_ik hcap_ik
      simp only [arm64_norm] at hcmn_out; apply SepWP.fold hcmn_out (by sep_focus); wp_reach
      apply SepWPpIn.weaken_pre (P' := chunkedNoHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m.receivingHdr uc x.bs rest)
        (by dsimp only [chunkedNoHeaderReceivedUcLoopPre, unchunked2CapAt]; rw [hauth, optAuthenticatorPBCapAt]; simp only [arm64_norm]; sep_entail)
      exact hcont _ (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
        (by try simp only [arm64_norm]) (by try simp only [arm64_norm]) (by try simp only [arm64_norm])
        (by simp only [arm64_norm, hx20]) (by try simp only [arm64_norm]) (by try simp only [arm64_norm])
        (by simp only [arm64_norm, hx23]) (by try simp only [arm64_norm]) (by try simp only [arm64_norm])
        ⟨by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩

/-- Outer loop tag 1 (`uc : Option<Unchunked.NoHeaderReceived>`) step at `+0x128` (`entry + 296#64`). -/
theorem chunkedNoHeaderReceived_tag1_step {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 0xffffffffffff9bec#64) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 0xffffffffffff98f4#64) (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 0xffffffffffffc318#64) (decodeVarint2Spec A))
    (hSkipCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 0xffffffffffffa9c0#64) (skipField3Spec A))
    (hAuthCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 0xffffffffffffcd84#64) ((authMergeSpec A).inImage img))
    {x : ChunkedNoHeaderReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.NoHeaderReceived} {rest : List (BitVec 8)} {iwt : WireType} {outerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hbs_lt : x.bs.length < 2 ^ 63)
    (hrest_le : rest.length ≤ x.bs.length) (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_uc :
      (Proto.mergeMessage V1State.Unchunked.NoHeaderReceived.mergeField (codecWireTypeToProto iwt) (m.uc.getD default) rest 98).toOption = none →
      (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (uc' : V1State.Unchunked.NoHeaderReceived) (rest' : List (BitVec 8)) (s' : State),
      (Proto.mergeMessage V1State.Unchunked.NoHeaderReceived.mergeField (codecWireTypeToProto iwt) (m.uc.getD default) rest 98).toOption = some (uc', rest') →
      s'.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 168#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s'
        (chunkedNoHeaderReceivedLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with uc := some uc' } x.bs rest')
        (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 296#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx8 : s.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
      (chunkedNoHeaderReceivedLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  let uc0 : V1State.Unchunked.NoHeaderReceived := m.uc.getD default
  have hpush_exit := @chunkedNoHeaderReceived_uc_push_exit img A H hPushCall x R s0 { receivingHdr := m.receivingHdr, uc := some uc0 }
  have hfrom_push := @chunkedNoHeaderReceived_uc_from_push_exit img A H hFromCall hPushCall x R s0 { receivingHdr := m.receivingHdr, uc := some uc0 }
  have huc_loop := fun (innerLimit : Nat) (hlim_lt : innerLimit < 2 ^ 63) =>
    @chunkedNoHeaderReceived_uc_loop_ok img A H hFromCall hPushCall hVarintCall hSkipCall hAuthCall x R s0 m.receivingHdr outerLimit innerLimit hsp_align hbs_lt hlim_lt
  refine chunkedNoHeaderReceived_uc_init ?_ hpc hrun hsp hx20 hx23 hcs
  intro s1 hpc1 hrun1 hsp1 htr1 hx8_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hcs1
  rw [htr] at htr1; rw [hx8] at hx8_1; rw [hx19] at hx19_1; rw [hx21] at hx21_1; rw [hx22] at hx22_1; rw [hx24] at hx24_1; rw [hx25] at hx25_1
  obtain ⟨hx27_1, hx28_1, hvregs_1⟩ := hcs1
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  chunkedNoHeaderReceivedMerge_fetches img.base H 316 32; chunkedNoHeaderReceivedMerge_fetches img.base H 372 16
  chunkedNoHeaderReceivedMerge_fetches img.base H 756 28; chunkedNoHeaderReceivedMerge_fetches img.base H 932 8
  chunkedNoHeaderReceivedMerge_fetches img.base H 680 4
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName = entry; examples_hide_fetches
  by_cases hiwt : iwt = .lengthDelimited
  · subst hiwt
    apply SepWPpIn.of_sepWP (mid := entry + 0xffffffffffffc318#64)
    conv => arg 4; rw [chunkedNoHeaderReceivedUcLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
      chunkedInlBelow_decodeVarint2 s0.sp]; simp only [sepConj_assoc]
    wp_steps; wp_reach
    refine SepWPpIn.call_frame (x := ⟨x.bufRef, x.slot, restPtr, rest⟩)
      (ret_pc := entry + 332#64) hVarintCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
      (by simp only [State.spAligned, hsp1, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
      (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, hsp1, hx19_1]; rfl)
      hrest_lt (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr1]) hpan) ?_
    intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, hsp1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx27_1, hx28_1, hvregs_1] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx27_m hx28_m hvregs_m
    cases hdv0 : decodeVarint rest with
    | none =>
      have hnone : (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
        apply hnone_of_uc
        rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_unchunked_noHeaderReceived_mergeField]
        simp [mergeMessageBin, codecWireTypeToProto, proto_decodeVarint_toOption, hdv0]
      apply SepWPpIn.of_sepWP (mid := entry + 696#64)
      (conv => arg 4; simp only [decodeVarint2Spec, hdv0, sepConj_assoc, arm64_norm, hsp1])
      apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
      have hcbnz : (sm.readReg64 (Reg.gpr 1#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm1
      apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
      apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
      apply SepWP.fold (unchunked2CapAt_entails_chunkedNoHeaderReceivedPBAt A x.msgPtr rest.length m.receivingHdr uc0) (by sep_focus)
      wp_steps; wp_reach
      apply SepWPpIn.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { receivingHdr := m.receivingHdr, uc := some uc0 } x.bs)
        (by dsimp only [chunkedNoHeaderReceivedErrFrame]; sep_entail)
      exact hpush_exit hnone (by decide : 0 ≤ 2) hsm1 hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
        (by simp only [arm64_norm, htrm, htr1]) (by simp only [arm64_norm])
        ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
    | some p =>
      rcases p with ⟨len, rest0⟩
      have hrest0_lt_rest : rest0.length < rest.length := decodeVarint_length hdv0
      have hrest0_le_rest : rest0.length ≤ rest.length := Nat.le_of_lt hrest0_lt_rest
      have hrest0_le : rest0.length ≤ x.bs.length := Nat.le_trans hrest0_le_rest hrest_le
      have hrest0_lt : rest0.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest0_le hbs_lt
      have hrest0_suf : IsDropSuffix x.bs rest0 := suffix_trans hrest_le hrest_suf hrest0_le_rest (decodeVarint_suffix hdv0)
      let rest0Ptr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length)
      by_cases hlt_len : rest0.length < len.toNat
      · have hule := ule_len_of_lt hlt_len hrest0_lt
        have hnone : (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
          apply hnone_of_uc
          rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_unchunked_noHeaderReceived_mergeField]
          rcases hdv0_p : Proto.decodeVarint rest with e | ⟨len', rest0'⟩
          · have hdv0' : decodeVarint rest = none := by rw [← proto_decodeVarint_toOption rest, hdv0_p]; rfl
            rw [hdv0] at hdv0'; nomatch hdv0'
          · have hdv0' : decodeVarint rest = some (len', rest0') := by rw [← proto_decodeVarint_toOption rest, hdv0_p]; rfl
            rw [hdv0] at hdv0'; injection hdv0' with hp; injection hp with hl hr0; subst hl hr0
            simp [mergeMessageBin, codecWireTypeToProto, hdv0_p, Except.toOption, hlt_len]
        apply SepWPpIn.of_sepWP (mid := entry + 684#64)
        (conv => arg 4; simp only [decodeVarint2Spec, hdv0, memRegion_48_cells1_160 s0.sp,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp1])
        apply SepWP.exists_elim; intro v_stk0; apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
        apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest0_le_rest) (by sep_focus)
        apply SepWP.fold (unchunked2CapAt_entails_chunkedNoHeaderReceivedPBAt A x.msgPtr rest.length m.receivingHdr uc0) (by sep_focus)
        conv => arg 4; rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]
        simp only [sepConj_assoc]; wp_steps
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot rest0Ptr (BitVec.ofNat 64 rest0.length)) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus)
        wp_reach
        apply SepWPpIn.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000007#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { receivingHdr := m.receivingHdr, uc := some uc0 } x.bs)
          (by dsimp only [chunkedNoHeaderReceivedErrFrame]; sep_entail)
        exact hfrom_push hnone (by decide : KindNoHeap 0x8000000000000007#64) hsp_align
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr1])
          ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
      · have hule := ule_len_of_ge hlt_len hrest0_lt
        have hsub := bv_len_sub_limit hlt_len
        have hlim_lt : rest0.length - len.toNat < 2 ^ 63 := by omega
        have hres0 : (Proto.mergeMessage V1State.Unchunked.NoHeaderReceived.mergeField (codecWireTypeToProto .lengthDelimited) uc0 rest 98).toOption =
            (mergeLoopBin V1State.Unchunked.NoHeaderReceived.mergeField (rest0.length - (rest0.length - len.toNat)) uc0 rest0 (rest0.length - len.toNat) 97).map
              (fun uc' => (uc', x.bs.drop (x.bs.length - (rest0.length - len.toNat)))) := by
          rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_unchunked_noHeaderReceived_mergeField]
          rcases hdv0_p : Proto.decodeVarint rest with e | ⟨len', rest0'⟩
          · have hdv0' : decodeVarint rest = none := by rw [← proto_decodeVarint_toOption rest, hdv0_p]; rfl
            rw [hdv0] at hdv0'; nomatch hdv0'
          · have hdv0' : decodeVarint rest = some (len', rest0') := by rw [← proto_decodeVarint_toOption rest, hdv0_p]; rfl
            rw [hdv0] at hdv0'; injection hdv0' with hp; injection hp with hl hr0; subst hl hr0
            have hdrop_eq : x.bs.drop (x.bs.length - (rest0.length - len.toNat)) = rest0.drop len.toNat := by
              conv_rhs => rw [hrest0_suf, List.drop_drop]
              congr 1; omega
            simp only [mergeMessageBin, codecWireTypeToProto, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
              hdv0_p, Except.toOption, hlt_len, hdrop_eq]
            rcases mergeLoopBin V1State.Unchunked.NoHeaderReceived.mergeField (rest0.length - (rest0.length - len.toNat)) uc0 rest0 (rest0.length - len.toNat) 97 with _ | uc' <;> rfl
        apply SepWPpIn.of_sepWP (mid := entry + 408#64)
        (conv => arg 4; simp only [decodeVarint2Spec, hdv0, sepConj_assoc, arm64_norm, hsp1])
        apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
        apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest0_le_rest) (by sep_focus)
        apply SepWP.fold (unchunked2CapAt_mono A (x.msgPtr + 0x28#64) uc0.epoch uc0.auth hrest0_le_rest) (by sep_focus)
        conv => arg 4; rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]
        simp only [sepConj_assoc]; wp_steps
        apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus)
        wp_reach
        apply SepWPpIn.weaken_pre (P' := chunkedNoHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m.receivingHdr uc0 x.bs rest0)
          (by dsimp only [chunkedNoHeaderReceivedUcLoopPre, sliceCursorAfter]; sep_entail)
        exact huc_loop (rest0.length - len.toNat) hlim_lt rest0.length uc0 rest0 _ (Nat.le_refl _) hrest0_le hrest0_suf
          (fun uc' r' sf hr_eq hr_le hr_suf hml hpc_f hrun_f hsp_f htr_f hx19_f hx20_f hx21_f hx22_f hx23_f hx24_f hx25_f hcs_f => by
            have hr'_eq : r' = x.bs.drop (x.bs.length - (rest0.length - len.toNat)) := by rw [hr_suf, hr_eq]
            refine hcont uc' r' sf ?_ hpc_f hrun_f hsp_f htr_f hx19_f hx20_f hx21_f hx22_f hx23_f hx24_f hx25_f hcs_f
            rw [hres0, hml, hr'_eq]; rfl)
          (fun hml => hnone_of_uc (by rw [hres0, hml]; rfl))
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr1])
          (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
          (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m]) (by simp only [arm64_norm, hx25_m]) (by simp only [arm64_norm, hsm1, hsub])
          ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  · obtain ⟨hcmp1, hcmp2⟩ := iwt64_beq_two_of_ne_ld hiwt
    have hnone : (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
      apply hnone_of_uc
      rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_unchunked_noHeaderReceived_mergeField]
      unfold mergeMessageBin; revert hiwt; cases iwt <;> intro hiwt <;> first | contradiction | rfl
    apply SepWPpIn.of_sepWP (mid := entry + 684#64)
    conv => arg 4; rw [chunkedNoHeaderReceivedUcLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
      sliceCursorAt, memRegion_48_wtErr160 s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro b_wt1; apply SepWP.exists_elim; intro b_wt0; apply SepWP.exists_elim; intro v_wt0
    wp_steps
    apply SepWP.fold (wtErr160_entails_memRegion40 s0.sp _ _) (by sep_focus)
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (unchunked2CapAt_entails_chunkedNoHeaderReceivedPBAt A x.msgPtr rest.length m.receivingHdr uc0) (by sep_focus)
    wp_reach
    apply SepWPpIn.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000006#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { receivingHdr := m.receivingHdr, uc := some uc0 } x.bs)
      (by dsimp only [chunkedNoHeaderReceivedErrFrame]; sep_entail)
    exact hfrom_push hnone (by decide : KindNoHeap 0x8000000000000006#64) hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) (by simp only [arm64_norm, htr1])
      ⟨by simp only [arm64_norm, hx27_1], by simp only [arm64_norm, hx28_1], by simp only [arm64_norm, hvregs_1]⟩

/-- Outer loop exit at `+0x0a8` (`entry + 168#64`) when `cur.length ≤ outerLimit`. -/
theorem chunkedNoHeaderReceived_loop_le_exit {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 0xffffffffffff9bec#64) (decodeErrorFromSpec A))
    {x : ChunkedNoHeaderReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.NoHeaderReceived} {cur : List (BitVec 8)} {outerLimit : Nat}
    (hle_lim : cur.length ≤ outerLimit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_suf : IsDropSuffix x.bs cur) (hlim_lt : outerLimit < 2 ^ 63)
    (hnone_of_lt : cur.length < outerLimit →
      (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hsome_of_eq : cur.length = outerLimit →
      (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = some (m, cur))
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 168#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (_hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (_hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (_hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64) (_hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (_hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
      (chunkedNoHeaderReceivedLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  by_cases heq_lim : cur.length = outerLimit
  · obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq heq_lim
    have hsome := hsome_of_eq heq_lim
    chunkedNoHeaderReceivedMerge_fetches img.base H 168 12; chunkedNoHeaderReceivedMerge_fetches img.base H 576 12
    chunkedNoHeaderReceivedMerge_fetches img.base H 128 28
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName = entry; examples_hide_fetches
    apply SepWPpIn.of_sepWP_ret; unfold WppPost chunkedNoHeaderReceivedMergeSpec
    simp only [hsome, chunkedNoHeaderReceivedLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
      sliceCursorAt, chunkedInlSavedRegs10, sepConj_assoc, arm64_norm, htr, hsp]
    wp_steps
    apply SepWP.fold (stackAt_chunkedInl10_epilogue s0.sp s0) (by unfold chunkedInlSavedRegs10; sep_focus)
    wp_done
  · have hlt_lim : cur.length < outerLimit := Nat.lt_of_le_of_ne hle_lim heq_lim
    obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_lt hlt_lim hlim_lt
    have hnone := hnone_of_lt hlt_lim
    have hfrom_err := @chunkedNoHeaderReceived_from_err_exit img A H hFromCall x R s0 m
    chunkedNoHeaderReceivedMerge_fetches img.base H 168 12; chunkedNoHeaderReceivedMerge_fetches img.base H 576 4
    chunkedNoHeaderReceivedMerge_fetches img.base H 740 16; chunkedNoHeaderReceivedMerge_fetches img.base H 88 8
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName = entry; examples_hide_fetches
    apply SepWPpIn.of_sepWP (mid := entry + 120#64)
    conv => arg 4; rw [chunkedNoHeaderReceivedLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
      sliceCursorAt, memRegion_48_cells1_160 s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v_stk0; wp_steps
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot curPtr (BitVec.ofNat 64 cur.length)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    apply SepWP.fold (chunkedNoHeaderReceivedPBCapAt_entails_pb A x.msgPtr cur.length m) (by sep_focus)
    wp_reach
    apply SepWPpIn.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000008#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (by dsimp only [chunkedNoHeaderReceivedErrFrame]; sep_entail)
    exact hfrom_err hnone (by decide : KindNoHeap 0x8000000000000008#64) hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr])
      ⟨by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩

/-- Outer loop key-decode step at `+0x0a8` (`entry + 168#64`) when `¬ cur.length ≤ outerLimit`. -/
theorem chunkedNoHeaderReceived_decode_key_step {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 0xffffffffffff9bec#64) (decodeErrorFromSpec A))
    (hVarintCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 0xffffffffffffc318#64) (decodeVarint2Spec A))
    {x : ChunkedNoHeaderReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.NoHeaderReceived} {cur : List (BitVec 8)} {outerLimit : Nat}
    (hgt_lim : ¬ cur.length ≤ outerLimit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_lt : cur.length < 2 ^ 63) (hcur_suf : IsDropSuffix x.bs cur)
    (hnone_of_loop_none :
      mergeLoopBin V1State.Chunked.NoHeaderReceived.mergeField (cur.length - outerLimit) m cur outerLimit 98 = none →
      (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (key : BitVec 64) (iwt : WireType) (rest : List (BitVec 8)) (s' : State),
      decodeVarint cur = some (key, rest) → ¬ 2 ^ 32 ≤ key.toNat →
      WireType.ofNat? (key.toNat % 8) = some iwt → ¬ key.toNat / 8 < 1 →
      s'.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 228#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s'
        (chunkedNoHeaderReceivedLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
        (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 168#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
      (chunkedNoHeaderReceivedLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  have hret_err := @chunkedNoHeaderReceived_ret_err_exit img A H x R s0 m
  have hfrom_err := @chunkedNoHeaderReceived_from_err_exit img A H hFromCall x R s0 m
  chunkedNoHeaderReceivedMerge_fetches img.base H 168 60; chunkedNoHeaderReceivedMerge_fetches img.base H 588 20
  chunkedNoHeaderReceivedMerge_fetches img.base H 608 12; chunkedNoHeaderReceivedMerge_fetches img.base H 620 16
  chunkedNoHeaderReceivedMerge_fetches img.base H 88 8
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName = entry; examples_hide_fetches
  apply SepWPpIn.of_sepWP (mid := entry + 0xffffffffffffc318#64)
  conv => arg 4; rw [chunkedNoHeaderReceivedLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
    sliceCursorAt, chunkedInlBelow_decodeVarint2 s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpIn.call_frame (x := ⟨x.bufRef, x.slot, curPtr, cur⟩)
    (ret_pc := entry + 188#64) hVarintCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, hsp, hx19]; rfl)
    hcur_lt (by dsimp only [sliceCursorAt, curPtr]; sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx27_m hx28_m hvregs_m
  cases hd : decodeVarint cur with
  | none =>
    have hnone := hnone_of_loop_none (mergeLoopBin_of_decodeVarint_none protoPrefixStep_chunked_noHeaderReceived_mergeField hgt_lim hd)
    apply SepWPpIn.of_sepWP (mid := entry + 128#64)
    (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
    apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    apply SepWP.fold (chunkedNoHeaderReceivedPBCapAt_entails_pb A x.msgPtr cur.length m) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPpIn.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (by dsimp only [chunkedNoHeaderReceivedErrFrame]; sep_entail)
    exact hret_err hnone (by decide : 0 ≤ 3) hsm1 hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])
      ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨key, rest⟩
    have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
    have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
    have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le
    have hrest_suf : IsDropSuffix x.bs rest := suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
    let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
    by_cases hk_ge : 2 ^ 32 ≤ key.toNat
    · have hnone := hnone_of_loop_none (mergeLoopBin_of_key_ge protoPrefixStep_chunked_noHeaderReceived_mergeField hgt_lim hd hk_ge)
      have hshr := key_shr32_of_ge hk_ge
      apply SepWPpIn.of_sepWP (mid := entry + 120#64)
      (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
      apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
      apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
      apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
      apply SepWP.fold (chunkedNoHeaderReceivedPBCapAt_entails_pb A x.msgPtr cur.length m) (by sep_focus)
      conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_cells2_160 s0.sp]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply SepWP.exists_elim; intro v_err0; apply SepWP.exists_elim; intro v_err1; wp_steps
      apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
      apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
      have h40 : ((s0.sp - 128#64 + 8#64) ↦₆₄ key) ∗ memRegion (s0.sp - 112#64) 32 ⊢ memRegion (s0.sp - 120#64) 40 := by
        rw [bv_sub_add_lit s0.sp 128 8]; exact cells2_memRegion32_entails_40_160 s0.sp key
      apply SepWP.fold h40 (by sep_focus); wp_reach
      apply SepWPpIn.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000004#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
        (by dsimp only [chunkedNoHeaderReceivedErrFrame]; sep_entail)
      exact hfrom_err hnone (by decide : KindNoHeap 0x8000000000000004#64) hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
        ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
    · have hshr := key_shr32_of_lt hk_ge
      cases hwt : WireType.ofNat? (key.toNat % 8) with
      | none =>
        have hnone := hnone_of_loop_none (mergeLoopBin_of_wt_none protoPrefixStep_chunked_noHeaderReceived_mergeField hgt_lim hd hk_ge hwt)
        obtain ⟨hcs1, hcs2⟩ := key_wt_none hwt
        apply SepWPpIn.of_sepWP (mid := entry + 120#64)
        (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
        apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
        apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
        apply SepWP.fold (chunkedNoHeaderReceivedPBCapAt_entails_pb A x.msgPtr cur.length m) (by sep_focus)
        conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_cells2_160 s0.sp]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        apply SepWP.exists_elim; intro v_err0; apply SepWP.exists_elim; intro v_err1; wp_steps
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        have h40 : ((s0.sp - 128#64 + 8#64) ↦₆₄ (key &&& 7#64)) ∗ memRegion (s0.sp - 112#64) 32 ⊢ memRegion (s0.sp - 120#64) 40 := by
          rw [bv_sub_add_lit s0.sp 128 8]; exact cells2_memRegion32_entails_40_160 s0.sp (key &&& 7#64)
        apply SepWP.fold h40 (by sep_focus); wp_reach
        apply SepWPpIn.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000003#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
          (by dsimp only [chunkedNoHeaderReceivedErrFrame]; sep_entail)
        exact hfrom_err hnone (by decide : KindNoHeap 0x8000000000000003#64) hsp_align
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
          ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
      | some iwt =>
        obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
        obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_ge
        obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
        by_cases hitag0 : key.toNat / 8 < 1
        · have hnone := hnone_of_loop_none (mergeLoopBin_of_tag_zero protoPrefixStep_chunked_noHeaderReceived_mergeField hgt_lim hd hk_ge hwt hitag0)
          have htag_zero : key.toNat / 8 = 0 := by omega
          apply SepWPpIn.of_sepWP (mid := entry + 120#64)
          (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
          apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
          apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          apply SepWP.fold (chunkedNoHeaderReceivedPBCapAt_entails_pb A x.msgPtr cur.length m) (by sep_focus)
          conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_cells1_160 s0.sp]
          simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
          apply SepWP.exists_elim; intro v_err0; wp_steps
          apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
          apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
          wp_reach
          apply SepWPpIn.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000005#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
            (by dsimp only [chunkedNoHeaderReceivedErrFrame]; sep_entail)
          exact hfrom_err hnone (by decide : KindNoHeap 0x8000000000000005#64) hsp_align
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
            ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
        · obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_ge hitag0
          have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
            rw [beq_eq_false_iff_ne]; intro h; have h1 := congrArg BitVec.toNat h
            simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1; omega
          apply SepWPpIn.of_sepWP (mid := entry + 228#64)
          (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
          apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
          apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          apply SepWP.fold (chunkedNoHeaderReceivedPBCapAt_mono A x.msgPtr m hrest_le_cur) (by sep_focus)
          wp_steps; wp_reach
          apply SepWPpIn.weaken_pre (P' := chunkedNoHeaderReceivedLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
            (by dsimp only [chunkedNoHeaderReceivedLoopPre]; sep_entail)
          exact hcont key iwt rest _ hd hk_ge hwt hitag0
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
            (by simp only [arm64_norm, hsm1, hand_wt]) (by simp only [arm64_norm, hsm1, hw1, hw1_2, hw1_zext1, hw1_zext2])
            (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
            (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m]) (by simp only [arm64_norm, hx25_m])
            ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

/-- Main outer loop induction at `+0x0a8` (`entry + 168#64`) for `V1State.Chunked.NoHeaderReceived.mergeField`. -/
theorem chunkedNoHeaderReceived_loop_ok {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 0xffffffffffff9bec#64) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 0xffffffffffff98f4#64) (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 0xffffffffffffc318#64) (decodeVarint2Spec A))
    (hSkipCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 0xffffffffffffa9c0#64) (skipField3Spec A))
    (hAuthCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 0xffffffffffffcd84#64) ((authMergeSpec A).inImage img))
    (hPolyCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 0xffffffffffffcf58#64) ((polyDecoderMergeSpec A).inImage img))
    {x : ChunkedNoHeaderReceivedMergeGhost} {R : SepProp} {s0 : State} {outerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hbs_lt : x.bs.length < 2 ^ 63) (hlim_lt : outerLimit < 2 ^ 63) :
    ∀ (n : Nat) (m : V1State.Chunked.NoHeaderReceived) (cur : List (BitVec 8)) (s : State),
      cur.length ≤ n → cur.length ≤ x.bs.length → IsDropSuffix x.bs cur →
      OptPolyDecoderBound m.receivingHdr cur.length →
      (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
        (mergeLoopBin V1State.Chunked.NoHeaderReceived.mergeField (cur.length - outerLimit) m cur outerLimit 98).map
          (fun m' => (m', x.bs.drop (x.bs.length - outerLimit))) →
      s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 168#64 →
      s.status = .Running → s.sp = s0.sp - 128#64 → s.trace = s0.trace →
      s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s.readReg64 (Reg.gpr 24#5) = 1#64 →
      s.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s →
      SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
        (chunkedNoHeaderReceivedLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
        (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  have htag1_step := fun {s m rest} (iwt : WireType) =>
    @chunkedNoHeaderReceived_tag1_step img A H hFromCall hPushCall hVarintCall hSkipCall hAuthCall x R s0 s m rest iwt outerLimit
  have htag2_step := fun {s m rest} (iwt : WireType) =>
    @chunkedNoHeaderReceived_tag2_step img A H hPushCall hPolyCall x R s0 s m rest iwt outerLimit
  have hskip_step := fun {s m rest} (iwt : WireType) (tag : Nat) =>
    @chunkedNoHeaderReceived_skip_step img A H hSkipCall x R s0 s m rest iwt tag outerLimit
  intro n; induction n with
  | zero =>
    intro m cur s hcur_n hcur_le hcur_suf _ hres hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hcs
    exact chunkedNoHeaderReceived_loop_le_exit hFromCall (by omega) hsp_align hcur_le hcur_suf hlim_lt
      (fun hlt => by rw [hres, mergeLoopBin_lt_limit _ _ _ _ _ _ hlt]; rfl)
      (fun heq => by rw [hres, mergeLoopBin_eq_limit _ _ _ _ _ _ heq, ← heq, ← hcur_suf]; rfl)
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hcs
  | succ n ih =>
    intro m cur s hcur_n hcur_le hcur_suf hbound hres hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hcs
    by_cases hle_lim : cur.length ≤ outerLimit
    · exact chunkedNoHeaderReceived_loop_le_exit hFromCall hle_lim hsp_align hcur_le hcur_suf hlim_lt
        (fun hlt => by rw [hres, mergeLoopBin_lt_limit _ _ _ _ _ _ hlt]; rfl)
        (fun heq => by rw [hres, mergeLoopBin_eq_limit _ _ _ _ _ _ heq, ← heq, ← hcur_suf]; rfl)
        hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hcs
    · have hcur_lt : cur.length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
      refine chunkedNoHeaderReceived_decode_key_step hFromCall hVarintCall hle_lim hsp_align
        hcur_le hcur_lt hcur_suf (fun hml => by rw [hres, hml]; rfl) ?_ hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hcs
      intro key iwt rest s' hd hk_ge hwt hitag0 hpc' hrun' hsp' htr' hx8' hx1' hx19' hx20' hx21' hx22' hx23' hx24' hx25' hcs'
      obtain ⟨hx27', hx28', hvregs'⟩ := hcs'
      have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
      have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
      have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le
      have hrest_lt : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest_le hbs_lt
      have hrest_suf : IsDropSuffix x.bs rest := suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
      have hbound_rest : OptPolyDecoderBound m.receivingHdr rest.length := optPolyDecoderBound_mono hbound hrest_le_cur
      have htag_lt : key.toNat / 8 < 2 ^ 32 := by omega
      have hstep := mergeLoopBin_of_key_ok (m := m) (depth' := 98)
        protoPrefixStep_chunked_noHeaderReceived_mergeField hle_lim hd hk_ge hwt hitag0
      by_cases htag1 : key.toNat / 8 = 1
      · rw [htag1] at hx1' hstep; rw [chunkedNoHeaderReceived_mergeField_tag1] at hstep
        chunkedNoHeaderReceivedMerge_fetches img.base H 228 16
        generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName = entry; examples_hide_fetches
        apply SepWPpIn.of_sepWP (mid := entry + 296#64); wp_steps; wp_reach
        refine htag1_step iwt hsp_align hbs_lt hrest_le hrest_lt hrest_suf
          (fun huc_none => by rw [hres, hstep, huc_none]; rfl)
          (fun uc' rest' s'' huc_some hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hcs'' => ?_)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
          (by simp only [arm64_norm, hx8']) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
          (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23'])
          (by simp only [arm64_norm, hx24']) (by simp only [arm64_norm, hx25'])
          ⟨by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩
        have hr'_le : rest'.length ≤ rest.length := (proto_mergeMessage_suffix huc_some).1
        exact ih { m with uc := some uc' } rest' s'' (by omega) (Nat.le_trans hr'_le hrest_le)
          (suffix_trans hrest_le hrest_suf hr'_le (proto_mergeMessage_suffix huc_some).2)
          (optPolyDecoderBound_mono hbound_rest hr'_le)
          (by rw [hres, hstep, huc_some]; rfl)
          hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hcs''
      · by_cases htag2 : key.toNat / 8 = 2
        · rw [htag2] at hx1' hstep; rw [chunkedNoHeaderReceived_mergeField_tag2] at hstep
          chunkedNoHeaderReceivedMerge_fetches img.base H 228 16
          generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName = entry; examples_hide_fetches
          apply SepWPpIn.of_sepWP (mid := entry + 244#64); wp_steps; wp_reach
          refine htag2_step iwt hsp_align hrest_le hrest_suf hbound_rest
            (fun hpoly_none => by rw [hres, hstep, hpoly_none]; rfl)
            (fun d' rest' s'' hpoly_some hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hcs'' => ?_)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
            (by simp only [arm64_norm, hx8']) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
            (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23'])
            (by simp only [arm64_norm, hx24']) (by simp only [arm64_norm, hx25'])
            ⟨by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩
          have hr'_le : rest'.length ≤ rest.length := (proto_mergeMessage_suffix hpoly_some).1
          exact ih { m with receivingHdr := some d' } rest' s'' (by omega) (Nat.le_trans hr'_le hrest_le)
            (suffix_trans hrest_le hrest_suf hr'_le (proto_mergeMessage_suffix hpoly_some).2)
            (optPolyDecoderBound_of_merge hbound_rest hpoly_some)
            (by rw [hres, hstep, hpoly_some]; rfl)
            hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hcs''
        · obtain ⟨hb1_1, _⟩ := itag_beq_tag_false htag1 htag_lt (by decide : 1 < 2 ^ 32)
          obtain ⟨hb2_1, _⟩ := itag_beq_tag_false htag2 htag_lt (by decide : 2 < 2 ^ 32)
          have hb1_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 1#32) = false := by rw [sf_truncate32_ofNat64]; exact hb1_1
          have hb2_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 2#32) = false := by rw [sf_truncate32_ofNat64]; exact hb2_1
          have hb2_bne1 : (BitVec.ofNat 32 (key.toNat / 8) != 2#32) = true := by simp only [bne, hb2_1, Bool.not_false]
          have hb2_bne2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) != 2#32) = true := by simp only [bne, hb2_2, Bool.not_false]
          rw [chunkedNoHeaderReceived_mergeField_other m iwt rest 98 htag_lt htag1 htag2] at hstep
          chunkedNoHeaderReceivedMerge_fetches img.base H 228 16
          generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName = entry; examples_hide_fetches
          apply SepWPpIn.of_sepWP (mid := entry + 348#64); wp_steps; wp_reach
          refine hskip_step iwt (key.toNat / 8) hsp_align hrest_le hrest_lt hrest_suf htag_lt
            (fun hsf_none => by rw [hres, hstep, hsf_none]; rfl)
            (fun rest' s'' hsf_some hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hcs'' => ?_)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
            (by simp only [arm64_norm, hx8']) (by simp only [arm64_norm, hx1', sf_truncate32_ofNat64])
            (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
            (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23'])
            (by simp only [arm64_norm, hx24']) (by simp only [arm64_norm, hx25'])
            ⟨by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩
          have hr'_le : rest'.length ≤ rest.length := (skip_length (2 * rest.length + 2)).1 _ _ _ _ _ hsf_some
          exact ih m rest' s'' (by omega) (Nat.le_trans hr'_le hrest_le)
            (suffix_trans hrest_le hrest_suf hr'_le ((skip_suffix (2 * rest.length + 2)).1 _ _ _ _ _ hsf_some))
            (optPolyDecoderBound_mono hbound_rest hr'_le)
            (by rw [hres, hstep, hsf_some]; rfl)
            hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hcs''

/-! ## 3. Top-Level X-World Verification of `chunkedNoHeaderReceivedMergeSpec` (`0x511b4`) -/

/-- Verification of `prost::encoding::message::merge::<V1State.Chunked.NoHeaderReceived, &mut &[u8]>` (`0x511b4`)
against `(chunkedNoHeaderReceivedMergeSpec A).inImage img` from offset-form callee contracts. -/
theorem chunked_no_header_received_merge_ok_of_contracts {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 0xffffffffffff9bec#64)
      (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 0xffffffffffff98f4#64)
      (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 0xffffffffffffc318#64)
      (decodeVarint2Spec A))
    (hSkipCall : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 0xffffffffffffa9c0#64)
      (skipField3Spec A))
    (hAuthCall : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 0xffffffffffffcd84#64)
      ((authMergeSpec A).inImage img))
    (hPolyCall : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 0xffffffffffffcf58#64)
      ((polyDecoderMergeSpec A).inImage img)) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName)
      ((chunkedNoHeaderReceivedMergeSpec A).inImage img) := by
  unfold Spec.inImage chunkedNoHeaderReceivedMergeSpec
  wpp_init x s0
  have ⟨h_1, h_2, h_3, hbound⟩ :
      (s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s0.readReg64 (Reg.gpr 1#5) = x.msgPtr ∧
      s0.readReg64 (Reg.gpr 2#5) = x.bufRef ∧
      OptPolyDecoderBound x.msg.receivingHdr x.bs.length := ⟨h_3, h_4, h_5, h⟩
  have hbs_lt : x.bs.length < 2 ^ 63 := by unfold OptPolyDecoderBound at hbound; omega
  replace hpc : s0.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName := by
    simpa only [arm64_norm, chunkedNoHeaderReceivedMerge_fnOff] using hpc
  conv => arg 6; ext sf P_f; rw [sepConj_assoc, satisfies_pure_sepConj]
  change SepWPp (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s0
    _ (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0)
  have hinv : ImgCallInv img s0 := ⟨‹_›, ‹_›⟩
  revert hinv; change SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s0
    _ (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0)
  have hret_err := @chunkedNoHeaderReceived_ret_err_exit img A H x R s0 x.msg
  have hfrom_err := @chunkedNoHeaderReceived_from_err_exit img A H hFromCall x R s0 x.msg
  have hloop := fun (outerLimit : Nat) (hlim_lt : outerLimit < 2 ^ 63) =>
    @chunkedNoHeaderReceived_loop_ok img A H hFromCall hPushCall hVarintCall hSkipCall hAuthCall hPolyCall x R s0 outerLimit hsp_align hbs_lt hlim_lt
  have hsaved :
      ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ⊢
      chunkedInlSavedRegs10 s0.sp s0 := Entails.refl _
  chunkedNoHeaderReceivedMerge_fetches img.base H 0 120; chunkedNoHeaderReceivedMerge_fetches img.base H 156 12
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName = entry; examples_hide_fetches
  by_cases hwt_ld : x.wt = .lengthDelimited
  · have h_1' : (s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = 2#8 := by rw [h_1, hwt_ld]; rfl
    have hbeq := wt_beq_two_of_lengthDelimited h_1'
    have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = false := by
      simp only [bne, hbeq, Bool.not_true]
    have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = false := by
      rw [BytesMergeFacts.truncate32_zeroExtend64_and_255_eq, h_1']; decide
    have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = false := by
      revert h_1'; bv_bits
    apply SepWPpIn.of_sepWP (mid := entry + 0xffffffffffffc318#64)
    conv => arg 4; rw [stackAt_chunkedInl_prologue s0.sp, chunkedInlBelow_decodeVarint2 s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v1; apply SepWP.exists_elim; intro v2
    apply SepWP.exists_elim; intro v3; apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v5
    apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v7; apply SepWP.exists_elim; intro v8
    apply SepWP.exists_elim; intro v9
    wp_steps; apply SepWP.fold hsaved (by sep_focus); wp_reach
    refine SepWPpIn.call_frame (x := ⟨x.bufRef, x.slot, x.ptr, x.bs⟩)
      (ret_pc := entry + 56#64) hVarintCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
      (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, h_3]; rfl)
      hbs_lt (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm]) hpan) ?_
    intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, _, _, _, _, _, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, h_2, h_3] at hpcm hrunm hspm hx19_m hx20_m hx27_m hx28_m hvregs_m
    cases hdv0 : decodeVarint x.bs with
    | none =>
      have hnone : (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
        rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_chunked_noHeaderReceived_mergeField]
        simp [mergeMessageBin, codecWireTypeToProto, proto_decodeVarint_toOption, hdv0]
      apply SepWPpIn.of_sepWP (mid := entry + 128#64)
      (conv => arg 4; simp only [decodeVarint2Spec, hdv0, sepConj_assoc, arm64_norm])
      apply SepWP.pure_elim; rintro ⟨hsm0, htrm, hsm1⟩
      apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
      apply SepWP.fold (chunkedNoHeaderReceivedPBCapAt_entails_pb A x.msgPtr x.bs.length x.msg) (by sep_focus)
      wp_steps; wp_reach
      apply SepWPpIn.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs)
        (by dsimp only [chunkedNoHeaderReceivedErrFrame]; sep_entail)
      exact hret_err hnone (by decide : 0 ≤ 3) hsm1 hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
        (by simp only [arm64_norm, htrm]) (by simp only [arm64_norm])
        ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
    | some p =>
      rcases p with ⟨len, rest0⟩
      have hrest0_lt_bs : rest0.length < x.bs.length := decodeVarint_length hdv0
      have hrest0_le : rest0.length ≤ x.bs.length := Nat.le_of_lt hrest0_lt_bs
      have hrest0_lt : rest0.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest0_le hbs_lt
      have hrest0_suf : IsDropSuffix x.bs rest0 := decodeVarint_suffix hdv0
      let rest0Ptr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length)
      by_cases hlt_len : rest0.length < len.toNat
      · have hule := ule_len_of_lt hlt_len hrest0_lt
        have hnone : (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
          rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_chunked_noHeaderReceived_mergeField]
          rcases hdv0_p : Proto.decodeVarint x.bs with e | ⟨len', rest0'⟩
          · have hdv0' : decodeVarint x.bs = none := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
            rw [hdv0] at hdv0'; nomatch hdv0'
          · have hdv0' : decodeVarint x.bs = some (len', rest0') := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
            rw [hdv0] at hdv0'; injection hdv0' with hp; injection hp with hl hr0; subst hl hr0
            simp [mergeMessageBin, codecWireTypeToProto, hdv0_p, Except.toOption, hlt_len]
        apply SepWPpIn.of_sepWP (mid := entry + 120#64)
        (conv => arg 4; simp only [decodeVarint2Spec, hdv0, sliceCursorAfter_eq_split hrest0_le hrest0_suf,
          sliceCursorAt, memRegion_48_cells1_160 s0.sp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm])
        apply SepWP.exists_elim; intro v_stk0; apply SepWP.pure_elim; rintro ⟨⟨hsm0, hsm1⟩, htrm⟩
        apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
        apply SepWP.fold (chunkedNoHeaderReceivedPBCapAt_entails_pb A x.msgPtr x.bs.length x.msg) (by sep_focus)
        wp_steps
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot rest0Ptr (BitVec.ofNat 64 rest0.length)) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus)
        wp_reach
        apply SepWPpIn.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000007#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs)
          (by dsimp only [chunkedNoHeaderReceivedErrFrame]; sep_entail)
        exact hfrom_err hnone (by decide : KindNoHeap 0x8000000000000007#64) hsp_align
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm])
          ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
      · have hule := ule_len_of_ge hlt_len hrest0_lt
        have hsub := bv_len_sub_limit hlt_len
        have hlim_lt : rest0.length - len.toNat < 2 ^ 63 := by omega
        have hres0 : (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
            (mergeLoopBin V1State.Chunked.NoHeaderReceived.mergeField (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 98).map
              (fun m' => (m', x.bs.drop (x.bs.length - (rest0.length - len.toNat)))) := by
          rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_chunked_noHeaderReceived_mergeField]
          rcases hdv0_p : Proto.decodeVarint x.bs with e | ⟨len', rest0'⟩
          · have hdv0' : decodeVarint x.bs = none := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
            rw [hdv0] at hdv0'; nomatch hdv0'
          · have hdv0' : decodeVarint x.bs = some (len', rest0') := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
            rw [hdv0] at hdv0'; injection hdv0' with hp; injection hp with hl hr0; subst hl hr0
            have hdrop_eq : x.bs.drop (x.bs.length - (rest0.length - len.toNat)) = rest0.drop len.toNat := by
              conv_rhs => rw [hrest0_suf, List.drop_drop]
              congr 1; omega
            simp only [mergeMessageBin, codecWireTypeToProto, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
              hdv0_p, Except.toOption, hlt_len, hdrop_eq]
            rcases mergeLoopBin V1State.Chunked.NoHeaderReceived.mergeField (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 98 with _ | m' <;> rfl
        apply SepWPpIn.of_sepWP (mid := entry + 168#64)
        (conv => arg 4; simp only [decodeVarint2Spec, hdv0, sliceCursorAfter_eq_split hrest0_le hrest0_suf,
          sliceCursorAt, sepConj_assoc, arm64_norm])
        apply SepWP.pure_elim; rintro ⟨⟨hsm0, hsm1⟩, htrm⟩
        apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
        apply SepWP.fold (chunkedNoHeaderReceivedPBCapAt_mono A x.msgPtr x.msg hrest0_le) (by sep_focus)
        wp_steps
        apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus)
        wp_reach
        apply SepWPpIn.weaken_pre (P' := chunkedNoHeaderReceivedLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs rest0)
          (by dsimp only [chunkedNoHeaderReceivedLoopPre, sliceCursorAfter]; sep_entail)
        exact hloop (rest0.length - len.toNat) hlim_lt rest0.length x.msg rest0 _ (Nat.le_refl _) hrest0_le hrest0_suf
          (optPolyDecoderBound_mono hbound hrest0_le) hres0
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm])
          (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm])
          (by simp only [arm64_norm, hsm1, hsub]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  · have hbeq := wt_beq_two_of_ne_lengthDelimited h_1 hwt_ld
    have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = true := by
      simp only [bne, hbeq, Bool.not_false]
    have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = true := by
      rw [BytesMergeFacts.truncate32_zeroExtend64_and_255_eq, h_1]
      revert hwt_ld; cases x.wt <;> intro hwt_ld <;> first | contradiction | decide
    have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = true := by
      rw [show BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) =
            BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 by bv_bits]; exact hbne1
    have hnone : (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
      rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_chunked_noHeaderReceived_mergeField]
      unfold mergeMessageBin; revert hwt_ld; cases x.wt <;> intro hwt_ld <;> first | contradiction | rfl
    apply SepWPpIn.of_sepWP (mid := entry + 120#64)
    conv => arg 4; rw [stackAt_chunkedInl_prologue s0.sp, sliceCursorAt, memRegion_48_wtErr160 s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v1; apply SepWP.exists_elim; intro v2
    apply SepWP.exists_elim; intro v3; apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v5
    apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v7; apply SepWP.exists_elim; intro v8
    apply SepWP.exists_elim; intro v9; apply SepWP.exists_elim; intro b_wt1
    apply SepWP.exists_elim; intro b_wt0; apply SepWP.exists_elim; intro v_wt0
    wp_steps; apply SepWP.fold hsaved (by sep_focus)
    apply SepWP.fold (wtErr160_entails_memRegion40 s0.sp _ _) (by sep_focus)
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot x.ptr (BitVec.ofNat 64 x.bs.length)) (by sep_focus)
    apply SepWP.fold (chunkedNoHeaderReceivedPBCapAt_entails_pb A x.msgPtr x.bs.length x.msg) (by sep_focus); wp_reach
    apply SepWPpIn.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000006#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs)
      (by dsimp only [chunkedNoHeaderReceivedErrFrame]; sep_entail)
    exact hfrom_err hnone (by decide : KindNoHeap 0x8000000000000006#64) hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      ⟨by simp only [arm64_norm], by simp only [arm64_norm]⟩

/-- Address-resolved X-world verification of `prost::encoding::message::merge::<V1State.Chunked.NoHeaderReceived, &mut &[u8]>` (`0x511b4`). -/
theorem chunked_no_header_received_merge_ok_of_fnAddr {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFrom : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr decodeErrorFromName) (decodeErrorFromSpec A))
    (hPush : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr decodeErrorPushName) (decodeErrorPushSpec A))
    (hVarint : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr Varint.decodeVarint2Name) (decodeVarint2Spec A))
    (hSkip : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr skipField3Name) (skipField3Spec A))
    (hAuth : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr authMergeName) ((authMergeSpec A).inImage img))
    (hPoly : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr polyDecoderMergeName) ((polyDecoderMergeSpec A).inImage img)) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName)
      ((chunkedNoHeaderReceivedMergeSpec A).inImage img) := by
  refine chunked_no_header_received_merge_ok_of_contracts ?_ ?_ ?_ ?_ ?_ ?_
  · rw [fnAddr_offset_eq_H (name := chunkedNoHeaderReceivedMergeName) (callee := decodeErrorFromName)]; exact hFrom
  · rw [fnAddr_offset_eq_H (name := chunkedNoHeaderReceivedMergeName) (callee := decodeErrorPushName)]; exact hPush
  · rw [fnAddr_offset_eq_H (name := chunkedNoHeaderReceivedMergeName) (callee := Varint.decodeVarint2Name)]; exact hVarint
  · rw [fnAddr_offset_eq_H (name := chunkedNoHeaderReceivedMergeName) (callee := skipField3Name)]; exact hSkip
  · rw [fnAddr_offset_eq_H (name := chunkedNoHeaderReceivedMergeName) (callee := authMergeName)]; exact hAuth
  · rw [fnAddr_offset_eq_H (name := chunkedNoHeaderReceivedMergeName) (callee := polyDecoderMergeName)]; exact hPoly

/-- `prost::encoding::message::merge::<V1State.Chunked.NoHeaderReceived, &mut &[u8]>` (`0x511b4`) meets
`(chunkedNoHeaderReceivedMergeSpec A).inImage img` on `tripleRatchetProgAtExt img.base ext`. -/
def ChunkedNoHeaderReceivedMergeOkX (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr chunkedNoHeaderReceivedMergeName)
    ((chunkedNoHeaderReceivedMergeSpec A).inImage img)

theorem chunked_no_header_received_merge_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hFrom : subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr decodeErrorFromName) (decodeErrorFromSpec A))
    (hPush : subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr decodeErrorPushName) (decodeErrorPushSpec A))
    (hVarint : subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr Varint.decodeVarint2Name) (decodeVarint2Spec A))
    (hSkip : subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr skipField3Name) (skipField3Spec A))
    (hAuth : AuthMergeOkX img A ext)
    (hPoly : subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr polyDecoderMergeName) ((polyDecoderMergeSpec A).inImage img)) :
    ChunkedNoHeaderReceivedMergeOkX img A ext :=
  chunked_no_header_received_merge_ok_of_fnAddr hFrom hPush hVarint hSkip hAuth hPoly

/-! ## 4. Placed (`[LibsignalPlacement]`) Outer Loop & Top-Level Verification for Block `308` -/

set_option quotPrecheck false in
local notation "entry" => (blkPl_308).base

theorem chunkedNoHeaderReceived_skip_step_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hSkipCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 263) (skipField3Spec A))
    {x : ChunkedNoHeaderReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.NoHeaderReceived} {rest : List (BitVec 8)} {iwt : WireType} {tag outerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest) (htag_lt : tag < 2 ^ 32)
    (hnone_of_skip : skipField (2 * rest.length + 2) 98 tag iwt rest = none →
      (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (rest' : List (BitVec 8)) (s' : State),
      skipField (2 * rest.length + 2) 98 tag iwt rest = some rest' →
      s'.pc = (blkPl_308).base + 168#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_308).rebase (blkPl_308).base H) (s0.readReg64 Reg.lr) s'
        (chunkedNoHeaderReceivedLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest')
        (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_308).base + 348#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx8 : s.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : (s.readReg64 (Reg.gpr 1#5)).setWidth 32 = BitVec.ofNat 32 tag)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_308).rebase (blkPl_308).base H) (s0.readReg64 Reg.lr) s
      (chunkedNoHeaderReceivedLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hret_err := @chunkedNoHeaderReceived_ret_err_exit_placed _ A H x R s0 m
  apply SepWPpLscro.of_sepWP (mid := lsmpl.base 263)
  conv => arg 4; rw [chunkedNoHeaderReceivedLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
    chunkedInlBelow_skipField98 s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpLscro.call_frame (x := ⟨iwt, tag, 98, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := entry + 364#64) hSkipCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [skipField3Spec]; simp only [arm64_norm, hsp, hx8, hx1, hx19, setWidth8_zext64_trunc32_ofNat64_wt_nhr]; rfl)
    (⟨htag_lt, by decide, hrest_lt⟩ : tag < 2 ^ 32 ∧ 98 < 2 ^ 32 ∧ rest.length < 2 ^ 63) (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx27_m hx28_m hvregs_m
  cases hsf : skipField (2 * rest.length + 2) 98 tag iwt rest with
  | none =>
    have hnone := hnone_of_skip hsf
    apply SepWPpLscro.of_sepWP (mid := entry + 128#64)
    (conv => arg 4; simp only [skipField3Spec, hsf, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    have hcbz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (chunkedInlBelow_skipField98_entails s0.sp) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (chunkedNoHeaderReceivedPBCapAt_entails_pb A x.msgPtr rest.length m) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPpLscro.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (by dsimp only [chunkedNoHeaderReceivedErrFrame]; sep_entail)
    exact hret_err hnone (by decide : 0 ≤ 3) hsm0 hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])
      ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some rest' =>
    have hrest'_le : rest'.length ≤ rest.length := (skip_length _).1 _ _ _ _ _ hsf
    apply SepWPpLscro.of_sepWP (mid := entry + 168#64)
    (conv => arg 4; simp only [skipField3Spec, hsf, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    apply SepWP.fold (chunkedInlBelow_skipField98_entails s0.sp) (by sep_focus)
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (chunkedNoHeaderReceivedPBCapAt_mono A x.msgPtr m hrest'_le) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPpLscro.weaken_pre (P' := chunkedNoHeaderReceivedLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest')
      (by dsimp only [chunkedNoHeaderReceivedLoopPre]; sep_entail)
    exact hcont rest' _ hsf (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m])
      (by simp only [arm64_norm, hx22_m]) (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m])
      (by simp only [arm64_norm, hx25_m])
      ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

theorem chunkedNoHeaderReceived_hdr_init_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    {x : ChunkedNoHeaderReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.NoHeaderReceived} {rest : List (BitVec 8)}
    (hcont : ∀ (s' : State),
      s'.pc = (blkPl_308).base + 268#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s.trace →
      s'.readReg64 (Reg.gpr 8#5) = s.readReg64 (Reg.gpr 8#5) →
      s'.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) → s'.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) →
      s'.readReg64 (Reg.gpr 23#5) = s.readReg64 (Reg.gpr 23#5) → s'.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_308).rebase (blkPl_308).base H) (s0.readReg64 Reg.lr) s'
        (protoPolynomialDecoderAt A x.msgPtr (polyDecoderToProto (m.receivingHdr.getD default)) ∗
          optNoHeaderReceivedPBCapAt A (x.msgPtr + 0x28#64) rest.length m.uc ∗
          stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗
          chunkedInlSavedRegs10 s0.sp s0 ∗ (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool)
        (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_308).base + 244#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr) (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_308).rebase (blkPl_308).base H) (s0.readReg64 Reg.lr) s
      (chunkedNoHeaderReceivedLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  rcases hhdr : m.receivingHdr with _ | d
  · rw [hhdr] at hcont
    apply SepWPpLscro.of_sepWP (mid := entry + 268#64)
    conv => arg 4; rw [chunkedNoHeaderReceivedLoopPre, chunkedNoHeaderReceivedPBCapAt, hhdr,
      optPolynomialDecoderPBAt, memRegion_polyDecoder_none_split_inl x.msgPtr]
    simp only [noneCap, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm]
    apply SepWP.exists_elim; intro b32; apply SepWP.exists_elim; intro v24
    apply SepWP.exists_elim; intro v16; apply SepWP.exists_elim; intro v8
    wp_steps
    apply SepWP.fold (default_polyDecoder_entails_pb_inl A x.msgPtr) (by sep_focus); wp_reach
    apply SepWPpLscro.weaken_pre (P' := protoPolynomialDecoderAt A x.msgPtr (polyDecoderToProto (Option.getD none default)) ∗ optNoHeaderReceivedPBCapAt A (x.msgPtr + 0x28#64) rest.length m.uc ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedInlSavedRegs10 s0.sp s0 ∗ (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool)
      (Entails.of_eq rfl)
    exact hcont _ (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
      (by try simp only [arm64_norm]) (by try simp only [arm64_norm]) (by try simp only [arm64_norm])
      (by simp only [arm64_norm, hx20]) (by try simp only [arm64_norm]) (by try simp only [arm64_norm])
      (by try simp only [arm64_norm]) (by try simp only [arm64_norm]) (by simp only [arm64_norm, hx25])
      ⟨by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩
  · rw [hhdr] at hcont
    apply SepWPpLscro.of_sepWP (mid := entry + 268#64)
    conv => arg 4; rw [chunkedNoHeaderReceivedLoopPre, chunkedNoHeaderReceivedPBCapAt, hhdr, optPolynomialDecoderPBAt_some_eq]
    simp only [sepConj_assoc, arm64_norm]
    apply SepWP.fold (protoPolynomialDecoderAt_entails_cmn A x.msgPtr d) (by sep_focus)
    wp_simp_pre [sepExists_sepConj_left, sepConj_assoc, arm64_norm]
    apply SepWP.exists_elim; intro pin; apply SepWP.pure_elim; intro hcap_lt
    have hcmn1 := cap_add_one_beq_zero_false hcap_lt; have hcmn2 := cap_add_one_bne_zero_true hcap_lt
    wp_steps
    apply SepWP.fold (cmn_entails_protoPolynomialDecoderAt A x.msgPtr pin d) (by sep_focus); wp_reach
    apply SepWPpLscro.weaken_pre (P' := protoPolynomialDecoderAt A x.msgPtr (polyDecoderToProto (Option.getD (some d) default)) ∗ optNoHeaderReceivedPBCapAt A (x.msgPtr + 0x28#64) rest.length m.uc ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedInlSavedRegs10 s0.sp s0 ∗ (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool)
      (Entails.of_eq rfl)
    exact hcont _ (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
      (by try simp only [arm64_norm]) (by try simp only [arm64_norm]) (by try simp only [arm64_norm])
      (by simp only [arm64_norm, hx20]) (by try simp only [arm64_norm]) (by try simp only [arm64_norm])
      (by try simp only [arm64_norm]) (by try simp only [arm64_norm]) (by simp only [arm64_norm, hx25])
      ⟨by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩

theorem chunkedNoHeaderReceived_tag2_step_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    (hPolyCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 296) (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A)))
    {x : ChunkedNoHeaderReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.NoHeaderReceived} {rest : List (BitVec 8)} {iwt : WireType} {outerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_suf : IsDropSuffix x.bs rest) (hbound : OptPolyDecoderBound m.receivingHdr rest.length)
    (hnone_of_poly :
      (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto iwt) (m.receivingHdr.getD default) rest 98).toOption = none →
      (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (d' : PolynomialDecoder) (rest' : List (BitVec 8)) (s' : State),
      (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto iwt) (m.receivingHdr.getD default) rest 98).toOption = some (d', rest') →
      s'.pc = (blkPl_308).base + 168#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_308).rebase (blkPl_308).base H) (s0.readReg64 Reg.lr) s'
        (chunkedNoHeaderReceivedLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with receivingHdr := some d' } x.bs rest')
        (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_308).base + 244#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx8 : s.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_308).rebase (blkPl_308).base H) (s0.readReg64 Reg.lr) s
      (chunkedNoHeaderReceivedLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  have hpush_ret := fun {d' : PolynomialDecoder} => @chunkedNoHeaderReceived_push_ret_exit_placed _ A H hPushCall x R s0 { receivingHdr := some d', uc := m.uc }
  refine chunkedNoHeaderReceived_hdr_init_placed ?_ hpc hrun hsp hx20 hx25 hcs
  intro s1 hpc1 hrun1 hsp1 htr1 hx8_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hcs1
  rw [htr] at htr1; rw [hx8] at hx8_1; rw [hx19] at hx19_1; rw [hx21] at hx21_1
  rw [hx22] at hx22_1; rw [hx23] at hx23_1; rw [hx24] at hx24_1
  obtain ⟨hx27_1, hx28_1, hvregs_1⟩ := hcs1
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  apply SepWPpLscro.of_sepWP (mid := lsmpl.base 296)
  conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, chunkedInlBelow_eq_polyMerge s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpLscro.call_frame_lscro (x := ⟨iwt, x.msgPtr, m.receivingHdr.getD default, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := entry + 284#64) hPolyCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
    (by simp only [State.spAligned, hsp1, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [polyDecoderMergeSpec]; simp only [arm64_norm, hsp1, hx8_1, hx20_1, hx19_1, setWidth8_zext64_trunc32_ofNat64_wt_nhr]; rfl)
    hbound (by sep_focus) (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [polyDecoderMergeSpec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr1]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx27_1, hx28_1, hvregs_1] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx27_m hx28_m hvregs_m
  cases hpoly_res : (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto iwt) (m.receivingHdr.getD default) rest 98).toOption with
  | none =>
    have hnone := hnone_of_poly hpoly_res
    apply SepWPpLscro.of_sepWP (mid := entry + 728#64)
    (conv => arg 4; simp only [polyDecoderMergeSpec, hpoly_res, memRegion_48_cells1_160 s0.sp,
      ← chunkedInlBelow_eq_polyMerge s0.sp,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp1])
    apply SepWP.exists_elim; intro v_stk0; apply SepWP.exists_elim; intro d'; apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; intro hpure
    have htrm : sm.trace = _ := hpure.1; have hsm0 : sm.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hpure.2.1; have hn_err : n_err ≤ 1 := hpure.2.2
    have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (optNoHeaderReceivedPBCapAt_entails A (x.msgPtr + 0x28#64) rest.length m.uc) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { receivingHdr := some d', uc := m.uc } x.bs)
      (by dsimp only [chunkedNoHeaderReceivedErrFrame, chunkedNoHeaderReceivedPBAt]; rw [optPolynomialDecoderPBAt_some_eq]; sep_entail)
    exact hpush_ret hnone (by omega : n_err ≤ 2) hsm0 hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr1]) (by simp only [arm64_norm, hspm])
      ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨d', rest'⟩
    have hrest'_le : rest'.length ≤ rest.length := (proto_mergeMessage_suffix hpoly_res).1
    apply SepWPpLscro.of_sepWP (mid := entry + 168#64)
    (conv => arg 4; simp only [polyDecoderMergeSpec, hpoly_res, ← chunkedInlBelow_eq_polyMerge s0.sp,
      sepConj_assoc, arm64_norm, hsp1])
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (optNoHeaderReceivedPBCapAt_mono A (x.msgPtr + 0x28#64) m.uc hrest'_le) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPpLscro.weaken_pre (P' := chunkedNoHeaderReceivedLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with receivingHdr := some d' } x.bs rest')
      (by dsimp only [chunkedNoHeaderReceivedLoopPre, chunkedNoHeaderReceivedPBCapAt]; rw [optPolynomialDecoderPBAt_some_eq]; sep_entail)
    exact hcont d' rest' _ hpoly_res
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr1])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m])
      (by simp only [arm64_norm, hx22_m]) (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m])
      (by simp only [arm64_norm, hx25_m])
      ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

theorem chunkedNoHeaderReceived_uc_init_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    {x : ChunkedNoHeaderReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.NoHeaderReceived} {rest : List (BitVec 8)}
    (hcont : ∀ (s' : State),
      s'.pc = (blkPl_308).base + 316#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s.trace →
      s'.readReg64 (Reg.gpr 8#5) = s.readReg64 (Reg.gpr 8#5) →
      s'.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) → s'.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) →
      s'.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_308).rebase (blkPl_308).base H) (s0.readReg64 Reg.lr) s'
        (chunkedNoHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m.receivingHdr (m.uc.getD default) x.bs rest)
        (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_308).base + 296#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr) (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_308).rebase (blkPl_308).base H) (s0.readReg64 Reg.lr) s
      (chunkedNoHeaderReceivedLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  rcases huc : m.uc with _ | uc
  · rw [huc] at hcont; dsimp only [Option.getD] at hcont
    apply SepWPpLscro.of_sepWP (mid := entry + 316#64)
    conv => arg 4; rw [chunkedNoHeaderReceivedLoopPre, chunkedNoHeaderReceivedPBCapAt, huc, optNoHeaderReceivedPBCapAt, memRegion_48_split_40_8 (x.msgPtr + 40#64)]
    simp only [noneCap2, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm]
    apply SepWP.exists_elim; intro v48; wp_steps
    have hdef : ((x.msgPtr + 40#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (x.msgPtr + 48#64) 40 ∗ ((x.msgPtr + 88#64) ↦₆₄ 0#64) ⊢
        unchunked2CapAt A (x.msgPtr + 40#64) rest.length
          (default : V1State.Unchunked.NoHeaderReceived).epoch
          (default : V1State.Unchunked.NoHeaderReceived).auth := by
      change ((x.msgPtr + 40#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (x.msgPtr + 48#64) 40 ∗ ((x.msgPtr + 88#64) ↦₆₄ 0#64) ⊢
        unchunked2CapAt A (x.msgPtr + 40#64) rest.length 0#64 none
      simpa only [noneCap, arm64_norm] using default_unchunked2_entails_cap A (x.msgPtr + 40#64) rest.length
    apply SepWP.fold hdef (by sep_focus); wp_reach
    apply SepWPpLscro.weaken_pre (P' := chunkedNoHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m.receivingHdr default x.bs rest)
      (by dsimp only [chunkedNoHeaderReceivedUcLoopPre]; sep_entail)
    exact hcont _ (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
      (by try simp only [arm64_norm]) (by try simp only [arm64_norm]) (by try simp only [arm64_norm])
      (by simp only [arm64_norm, hx20]) (by try simp only [arm64_norm]) (by try simp only [arm64_norm])
      (by simp only [arm64_norm, hx23]) (by try simp only [arm64_norm]) (by try simp only [arm64_norm])
      ⟨by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩
  · rw [huc] at hcont; dsimp only [Option.getD] at hcont
    rcases hauth : uc.auth with _ | auth
    · apply SepWPpLscro.of_sepWP (mid := entry + 316#64)
      conv => arg 4; rw [chunkedNoHeaderReceivedLoopPre, chunkedNoHeaderReceivedPBCapAt, huc, optNoHeaderReceivedPBCapAt,
        unchunked2CapAt, hauth, optAuthenticatorPBCapAt]
      simp only [noneCap, sepConj_assoc, arm64_norm]; wp_steps; wp_reach
      apply SepWPpLscro.weaken_pre (P' := chunkedNoHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m.receivingHdr uc x.bs rest)
        (by dsimp only [chunkedNoHeaderReceivedUcLoopPre, unchunked2CapAt]; rw [hauth, optAuthenticatorPBCapAt, noneCap]; simp only [arm64_norm]; sep_entail)
      exact hcont _ (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
        (by try simp only [arm64_norm]) (by try simp only [arm64_norm]) (by try simp only [arm64_norm])
        (by simp only [arm64_norm, hx20]) (by try simp only [arm64_norm]) (by try simp only [arm64_norm])
        (by simp only [arm64_norm, hx23]) (by try simp only [arm64_norm]) (by try simp only [arm64_norm])
        ⟨by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩
    · apply SepWPpLscro.of_sepWP (mid := entry + 316#64)
      conv => arg 4; rw [chunkedNoHeaderReceivedLoopPre, chunkedNoHeaderReceivedPBCapAt, huc, optNoHeaderReceivedPBCapAt,
        unchunked2CapAt, hauth, optAuthenticatorPBCapAt]
      simp only [sepConj_assoc, arm64_norm]
      have hcmn_in := authenticatorPBCapAt_entails_cmn A (x.msgPtr + 40#64) rest.length auth
      simp only [arm64_norm] at hcmn_in; apply SepWP.fold hcmn_in (by sep_focus)
      wp_simp_pre [sepExists_sepConj_left, sepConj_assoc, arm64_norm]
      apply SepWP.exists_elim; intro cap_ik; apply SepWP.exists_elim; intro ptr_ik
      apply SepWP.pure_elim; rintro ⟨hcap_lt, hcap_ik⟩
      have hcmn1 := cap_add_two_beq_zero_false hcap_lt; have hcmn2 := cap_add_two_bne_zero_true hcap_lt
      wp_steps
      have hcmn_out := cmn_entails_authenticatorPBCapAt A (x.msgPtr + 40#64) rest.length auth cap_ik ptr_ik hcap_ik
      simp only [arm64_norm] at hcmn_out; apply SepWP.fold hcmn_out (by sep_focus); wp_reach
      apply SepWPpLscro.weaken_pre (P' := chunkedNoHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m.receivingHdr uc x.bs rest)
        (by dsimp only [chunkedNoHeaderReceivedUcLoopPre, unchunked2CapAt]; rw [hauth, optAuthenticatorPBCapAt]; simp only [arm64_norm]; sep_entail)
      exact hcont _ (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
        (by try simp only [arm64_norm]) (by try simp only [arm64_norm]) (by try simp only [arm64_norm])
        (by simp only [arm64_norm, hx20]) (by try simp only [arm64_norm]) (by try simp only [arm64_norm])
        (by simp only [arm64_norm, hx23]) (by try simp only [arm64_norm]) (by try simp only [arm64_norm])
        ⟨by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩

theorem chunkedNoHeaderReceived_tag1_step_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 261) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 291) (decodeVarint2Spec A))
    (hSkipCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 263) (skipField3Spec A))
    (hAuthCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A)))
    {x : ChunkedNoHeaderReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.NoHeaderReceived} {rest : List (BitVec 8)} {iwt : WireType} {outerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hbs_lt : x.bs.length < 2 ^ 63)
    (hrest_le : rest.length ≤ x.bs.length) (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_uc :
      (Proto.mergeMessage V1State.Unchunked.NoHeaderReceived.mergeField (codecWireTypeToProto iwt) (m.uc.getD default) rest 98).toOption = none →
      (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (uc' : V1State.Unchunked.NoHeaderReceived) (rest' : List (BitVec 8)) (s' : State),
      (Proto.mergeMessage V1State.Unchunked.NoHeaderReceived.mergeField (codecWireTypeToProto iwt) (m.uc.getD default) rest 98).toOption = some (uc', rest') →
      s'.pc = (blkPl_308).base + 168#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_308).rebase (blkPl_308).base H) (s0.readReg64 Reg.lr) s'
        (chunkedNoHeaderReceivedLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with uc := some uc' } x.bs rest')
        (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_308).base + 296#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx8 : s.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_308).rebase (blkPl_308).base H) (s0.readReg64 Reg.lr) s
      (chunkedNoHeaderReceivedLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  let uc0 : V1State.Unchunked.NoHeaderReceived := m.uc.getD default
  have hpush_exit := @chunkedNoHeaderReceived_uc_push_exit_placed _ A H hPushCall x R s0 { receivingHdr := m.receivingHdr, uc := some uc0 }
  have hfrom_push := @chunkedNoHeaderReceived_uc_from_push_exit_placed _ A H hFromCall hPushCall x R s0 { receivingHdr := m.receivingHdr, uc := some uc0 }
  have huc_loop := fun (innerLimit : Nat) (hlim_lt : innerLimit < 2 ^ 63) =>
    @chunkedNoHeaderReceived_uc_loop_ok_placed _ A H hFromCall hPushCall hVarintCall hSkipCall hAuthCall x R s0 m.receivingHdr outerLimit innerLimit hsp_align hbs_lt hlim_lt
  refine chunkedNoHeaderReceived_uc_init_placed ?_ hpc hrun hsp hx20 hx23 hcs
  intro s1 hpc1 hrun1 hsp1 htr1 hx8_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hcs1
  rw [htr] at htr1; rw [hx8] at hx8_1; rw [hx19] at hx19_1; rw [hx21] at hx21_1; rw [hx22] at hx22_1; rw [hx24] at hx24_1; rw [hx25] at hx25_1
  obtain ⟨hx27_1, hx28_1, hvregs_1⟩ := hcs1
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  by_cases hiwt : iwt = .lengthDelimited
  · subst hiwt
    apply SepWPpLscro.of_sepWP (mid := lsmpl.base 291)
    conv => arg 4; rw [chunkedNoHeaderReceivedUcLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
      chunkedInlBelow_decodeVarint2 s0.sp]; simp only [sepConj_assoc]
    wp_steps; wp_reach
    refine SepWPpLscro.call_frame (x := ⟨x.bufRef, x.slot, restPtr, rest⟩)
      (ret_pc := entry + 332#64) hVarintCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
      (by simp only [State.spAligned, hsp1, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
      (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, hsp1, hx19_1]; rfl)
      hrest_lt (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr1]) hpan) ?_
    intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, hsp1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx27_1, hx28_1, hvregs_1] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx27_m hx28_m hvregs_m
    cases hdv0 : decodeVarint rest with
    | none =>
      have hnone : (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
        apply hnone_of_uc
        rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_unchunked_noHeaderReceived_mergeField]
        simp [mergeMessageBin, codecWireTypeToProto, proto_decodeVarint_toOption, hdv0]
      apply SepWPpLscro.of_sepWP (mid := entry + 696#64)
      (conv => arg 4; simp only [decodeVarint2Spec, hdv0, sepConj_assoc, arm64_norm, hsp1])
      apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
      have hcbnz : (sm.readReg64 (Reg.gpr 1#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm1
      apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
      apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
      apply SepWP.fold (unchunked2CapAt_entails_chunkedNoHeaderReceivedPBAt A x.msgPtr rest.length m.receivingHdr uc0) (by sep_focus)
      wp_steps; wp_reach
      apply SepWPpLscro.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { receivingHdr := m.receivingHdr, uc := some uc0 } x.bs)
        (by dsimp only [chunkedNoHeaderReceivedErrFrame]; sep_entail)
      exact hpush_exit hnone (by decide : 0 ≤ 2) hsm1 hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
        (by simp only [arm64_norm, htrm, htr1]) (by simp only [arm64_norm])
        ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
    | some p =>
      rcases p with ⟨len, rest0⟩
      have hrest0_lt_rest : rest0.length < rest.length := decodeVarint_length hdv0
      have hrest0_le_rest : rest0.length ≤ rest.length := Nat.le_of_lt hrest0_lt_rest
      have hrest0_le : rest0.length ≤ x.bs.length := Nat.le_trans hrest0_le_rest hrest_le
      have hrest0_lt : rest0.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest0_le hbs_lt
      have hrest0_suf : IsDropSuffix x.bs rest0 := suffix_trans hrest_le hrest_suf hrest0_le_rest (decodeVarint_suffix hdv0)
      let rest0Ptr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length)
      by_cases hlt_len : rest0.length < len.toNat
      · have hule := ule_len_of_lt hlt_len hrest0_lt
        have hnone : (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
          apply hnone_of_uc
          rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_unchunked_noHeaderReceived_mergeField]
          rcases hdv0_p : Proto.decodeVarint rest with e | ⟨len', rest0'⟩
          · have hdv0' : decodeVarint rest = none := by rw [← proto_decodeVarint_toOption rest, hdv0_p]; rfl
            rw [hdv0] at hdv0'; nomatch hdv0'
          · have hdv0' : decodeVarint rest = some (len', rest0') := by rw [← proto_decodeVarint_toOption rest, hdv0_p]; rfl
            rw [hdv0] at hdv0'; injection hdv0' with hp; injection hp with hl hr0; subst hl hr0
            simp [mergeMessageBin, codecWireTypeToProto, hdv0_p, Except.toOption, hlt_len]
        apply SepWPpLscro.of_sepWP (mid := entry + 684#64)
        (conv => arg 4; simp only [decodeVarint2Spec, hdv0, memRegion_48_cells1_160 s0.sp,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp1])
        apply SepWP.exists_elim; intro v_stk0; apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
        apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest0_le_rest) (by sep_focus)
        apply SepWP.fold (unchunked2CapAt_entails_chunkedNoHeaderReceivedPBAt A x.msgPtr rest.length m.receivingHdr uc0) (by sep_focus)
        conv => arg 4; rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]
        simp only [sepConj_assoc]; wp_steps
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot rest0Ptr (BitVec.ofNat 64 rest0.length)) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus)
        wp_reach
        apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000007#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { receivingHdr := m.receivingHdr, uc := some uc0 } x.bs)
          (by dsimp only [chunkedNoHeaderReceivedErrFrame]; sep_entail)
        exact hfrom_push hnone (by decide : KindNoHeap 0x8000000000000007#64) hsp_align
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr1])
          ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
      · have hule := ule_len_of_ge hlt_len hrest0_lt
        have hsub := bv_len_sub_limit hlt_len
        have hlim_lt : rest0.length - len.toNat < 2 ^ 63 := by omega
        have hres0 : (Proto.mergeMessage V1State.Unchunked.NoHeaderReceived.mergeField (codecWireTypeToProto .lengthDelimited) uc0 rest 98).toOption =
            (mergeLoopBin V1State.Unchunked.NoHeaderReceived.mergeField (rest0.length - (rest0.length - len.toNat)) uc0 rest0 (rest0.length - len.toNat) 97).map
              (fun uc' => (uc', x.bs.drop (x.bs.length - (rest0.length - len.toNat)))) := by
          rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_unchunked_noHeaderReceived_mergeField]
          rcases hdv0_p : Proto.decodeVarint rest with e | ⟨len', rest0'⟩
          · have hdv0' : decodeVarint rest = none := by rw [← proto_decodeVarint_toOption rest, hdv0_p]; rfl
            rw [hdv0] at hdv0'; nomatch hdv0'
          · have hdv0' : decodeVarint rest = some (len', rest0') := by rw [← proto_decodeVarint_toOption rest, hdv0_p]; rfl
            rw [hdv0] at hdv0'; injection hdv0' with hp; injection hp with hl hr0; subst hl hr0
            have hdrop_eq : x.bs.drop (x.bs.length - (rest0.length - len.toNat)) = rest0.drop len.toNat := by
              conv_rhs => rw [hrest0_suf, List.drop_drop]
              congr 1; omega
            simp only [mergeMessageBin, codecWireTypeToProto, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
              hdv0_p, Except.toOption, hlt_len, hdrop_eq]
            rcases mergeLoopBin V1State.Unchunked.NoHeaderReceived.mergeField (rest0.length - (rest0.length - len.toNat)) uc0 rest0 (rest0.length - len.toNat) 97 with _ | uc' <;> rfl
        apply SepWPpLscro.of_sepWP (mid := entry + 408#64)
        (conv => arg 4; simp only [decodeVarint2Spec, hdv0, sepConj_assoc, arm64_norm, hsp1])
        apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
        apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest0_le_rest) (by sep_focus)
        apply SepWP.fold (unchunked2CapAt_mono A (x.msgPtr + 0x28#64) uc0.epoch uc0.auth hrest0_le_rest) (by sep_focus)
        conv => arg 4; rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]
        simp only [sepConj_assoc]; wp_steps
        apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus)
        wp_reach
        apply SepWPpLscro.weaken_pre (P' := chunkedNoHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m.receivingHdr uc0 x.bs rest0)
          (by dsimp only [chunkedNoHeaderReceivedUcLoopPre, sliceCursorAfter]; sep_entail)
        exact huc_loop (rest0.length - len.toNat) hlim_lt rest0.length uc0 rest0 _ (Nat.le_refl _) hrest0_le hrest0_suf
          (fun uc' r' sf hr_eq hr_le hr_suf hml hpc_f hrun_f hsp_f htr_f hx19_f hx20_f hx21_f hx22_f hx23_f hx24_f hx25_f hcs_f => by
            have hr'_eq : r' = x.bs.drop (x.bs.length - (rest0.length - len.toNat)) := by rw [hr_suf, hr_eq]
            refine hcont uc' r' sf ?_ hpc_f hrun_f hsp_f htr_f hx19_f hx20_f hx21_f hx22_f hx23_f hx24_f hx25_f hcs_f
            rw [hres0, hml, hr'_eq]; rfl)
          (fun hml => hnone_of_uc (by rw [hres0, hml]; rfl))
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr1])
          (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
          (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m]) (by simp only [arm64_norm, hx25_m]) (by simp only [arm64_norm, hsm1, hsub])
          ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  · obtain ⟨hcmp1, hcmp2⟩ := iwt64_beq_two_of_ne_ld hiwt
    have hnone : (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
      apply hnone_of_uc
      rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_unchunked_noHeaderReceived_mergeField]
      unfold mergeMessageBin; revert hiwt; cases iwt <;> intro hiwt <;> first | contradiction | rfl
    apply SepWPpLscro.of_sepWP (mid := entry + 684#64)
    conv => arg 4; rw [chunkedNoHeaderReceivedUcLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
      sliceCursorAt, memRegion_48_wtErr160 s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro b_wt1; apply SepWP.exists_elim; intro b_wt0; apply SepWP.exists_elim; intro v_wt0
    wp_steps
    apply SepWP.fold (wtErr160_entails_memRegion40 s0.sp _ _) (by sep_focus)
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (unchunked2CapAt_entails_chunkedNoHeaderReceivedPBAt A x.msgPtr rest.length m.receivingHdr uc0) (by sep_focus)
    wp_reach
    apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000006#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { receivingHdr := m.receivingHdr, uc := some uc0 } x.bs)
      (by dsimp only [chunkedNoHeaderReceivedErrFrame]; sep_entail)
    exact hfrom_push hnone (by decide : KindNoHeap 0x8000000000000006#64) hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) (by simp only [arm64_norm, htr1])
      ⟨by simp only [arm64_norm, hx27_1], by simp only [arm64_norm, hx28_1], by simp only [arm64_norm, hvregs_1]⟩

theorem chunkedNoHeaderReceived_loop_le_exit_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 261) (decodeErrorFromSpec A))
    {x : ChunkedNoHeaderReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.NoHeaderReceived} {cur : List (BitVec 8)} {outerLimit : Nat}
    (hle_lim : cur.length ≤ outerLimit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_suf : IsDropSuffix x.bs cur) (hlim_lt : outerLimit < 2 ^ 63)
    (hnone_of_lt : cur.length < outerLimit →
      (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hsome_of_eq : cur.length = outerLimit →
      (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = some (m, cur))
    (hpc : s.pc = (blkPl_308).base + 168#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (_hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (_hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (_hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64) (_hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (_hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_308).rebase (blkPl_308).base H) (s0.readReg64 Reg.lr) s
      (chunkedNoHeaderReceivedLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  by_cases heq_lim : cur.length = outerLimit
  · obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq heq_lim
    have hsome := hsome_of_eq heq_lim
    apply SepWPpLscro.of_sepWP_ret; unfold WppPost chunkedNoHeaderReceivedMergeSpec
    simp only [hsome, chunkedNoHeaderReceivedLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
      sliceCursorAt, chunkedInlSavedRegs10, sepConj_assoc, arm64_norm, htr, hsp]
    wp_steps
    apply SepWP.fold (stackAt_chunkedInl10_epilogue s0.sp s0) (by unfold chunkedInlSavedRegs10; sep_focus)
    wp_done
  · have hlt_lim : cur.length < outerLimit := Nat.lt_of_le_of_ne hle_lim heq_lim
    obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_lt hlt_lim hlim_lt
    have hnone := hnone_of_lt hlt_lim
    have hfrom_err := @chunkedNoHeaderReceived_from_err_exit_placed _ A H hFromCall x R s0 m
    apply SepWPpLscro.of_sepWP (mid := entry + 120#64)
    conv => arg 4; rw [chunkedNoHeaderReceivedLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
      sliceCursorAt, memRegion_48_cells1_160 s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v_stk0; wp_steps
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot curPtr (BitVec.ofNat 64 cur.length)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    apply SepWP.fold (chunkedNoHeaderReceivedPBCapAt_entails_pb A x.msgPtr cur.length m) (by sep_focus)
    wp_reach
    apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000008#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (by dsimp only [chunkedNoHeaderReceivedErrFrame]; sep_entail)
    exact hfrom_err hnone (by decide : KindNoHeap 0x8000000000000008#64) hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr])
      ⟨by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩

theorem chunkedNoHeaderReceived_decode_key_step_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 261) (decodeErrorFromSpec A))
    (hVarintCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 291) (decodeVarint2Spec A))
    {x : ChunkedNoHeaderReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.NoHeaderReceived} {cur : List (BitVec 8)} {outerLimit : Nat}
    (hgt_lim : ¬ cur.length ≤ outerLimit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_lt : cur.length < 2 ^ 63) (hcur_suf : IsDropSuffix x.bs cur)
    (hnone_of_loop_none :
      mergeLoopBin V1State.Chunked.NoHeaderReceived.mergeField (cur.length - outerLimit) m cur outerLimit 98 = none →
      (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (key : BitVec 64) (iwt : WireType) (rest : List (BitVec 8)) (s' : State),
      decodeVarint cur = some (key, rest) → ¬ 2 ^ 32 ≤ key.toNat →
      WireType.ofNat? (key.toNat % 8) = some iwt → ¬ key.toNat / 8 < 1 →
      s'.pc = (blkPl_308).base + 228#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_308).rebase (blkPl_308).base H) (s0.readReg64 Reg.lr) s'
        (chunkedNoHeaderReceivedLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
        (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_308).base + 168#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_308).rebase (blkPl_308).base H) (s0.readReg64 Reg.lr) s
      (chunkedNoHeaderReceivedLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  have hret_err := @chunkedNoHeaderReceived_ret_err_exit_placed _ A H x R s0 m
  have hfrom_err := @chunkedNoHeaderReceived_from_err_exit_placed _ A H hFromCall x R s0 m
  apply SepWPpLscro.of_sepWP (mid := lsmpl.base 291)
  conv => arg 4; rw [chunkedNoHeaderReceivedLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
    sliceCursorAt, chunkedInlBelow_decodeVarint2 s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpLscro.call_frame (x := ⟨x.bufRef, x.slot, curPtr, cur⟩)
    (ret_pc := entry + 188#64) hVarintCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, hsp, hx19]; rfl)
    hcur_lt (by dsimp only [sliceCursorAt, curPtr]; sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx27_m hx28_m hvregs_m
  cases hd : decodeVarint cur with
  | none =>
    have hnone := hnone_of_loop_none (mergeLoopBin_of_decodeVarint_none protoPrefixStep_chunked_noHeaderReceived_mergeField hgt_lim hd)
    apply SepWPpLscro.of_sepWP (mid := entry + 128#64)
    (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
    apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    apply SepWP.fold (chunkedNoHeaderReceivedPBCapAt_entails_pb A x.msgPtr cur.length m) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPpLscro.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (by dsimp only [chunkedNoHeaderReceivedErrFrame]; sep_entail)
    exact hret_err hnone (by decide : 0 ≤ 3) hsm1 hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])
      ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨key, rest⟩
    have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
    have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
    have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le
    have hrest_suf : IsDropSuffix x.bs rest := suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
    let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
    by_cases hk_ge : 2 ^ 32 ≤ key.toNat
    · have hnone := hnone_of_loop_none (mergeLoopBin_of_key_ge protoPrefixStep_chunked_noHeaderReceived_mergeField hgt_lim hd hk_ge)
      have hshr := key_shr32_of_ge hk_ge
      apply SepWPpLscro.of_sepWP (mid := entry + 120#64)
      (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
      apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
      apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
      apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
      apply SepWP.fold (chunkedNoHeaderReceivedPBCapAt_entails_pb A x.msgPtr cur.length m) (by sep_focus)
      conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_cells2_160 s0.sp]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply SepWP.exists_elim; intro v_err0; apply SepWP.exists_elim; intro v_err1; wp_steps
      apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
      apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
      have h40 : ((s0.sp - 128#64 + 8#64) ↦₆₄ key) ∗ memRegion (s0.sp - 112#64) 32 ⊢ memRegion (s0.sp - 120#64) 40 := by
        rw [bv_sub_add_lit s0.sp 128 8]; exact cells2_memRegion32_entails_40_160 s0.sp key
      apply SepWP.fold h40 (by sep_focus); wp_reach
      apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000004#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
        (by dsimp only [chunkedNoHeaderReceivedErrFrame]; sep_entail)
      exact hfrom_err hnone (by decide : KindNoHeap 0x8000000000000004#64) hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
        ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
    · have hshr := key_shr32_of_lt hk_ge
      cases hwt : WireType.ofNat? (key.toNat % 8) with
      | none =>
        have hnone := hnone_of_loop_none (mergeLoopBin_of_wt_none protoPrefixStep_chunked_noHeaderReceived_mergeField hgt_lim hd hk_ge hwt)
        obtain ⟨hcs1, hcs2⟩ := key_wt_none hwt
        apply SepWPpLscro.of_sepWP (mid := entry + 120#64)
        (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
        apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
        apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
        apply SepWP.fold (chunkedNoHeaderReceivedPBCapAt_entails_pb A x.msgPtr cur.length m) (by sep_focus)
        conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_cells2_160 s0.sp]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        apply SepWP.exists_elim; intro v_err0; apply SepWP.exists_elim; intro v_err1; wp_steps
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        have h40 : ((s0.sp - 128#64 + 8#64) ↦₆₄ (key &&& 7#64)) ∗ memRegion (s0.sp - 112#64) 32 ⊢ memRegion (s0.sp - 120#64) 40 := by
          rw [bv_sub_add_lit s0.sp 128 8]; exact cells2_memRegion32_entails_40_160 s0.sp (key &&& 7#64)
        apply SepWP.fold h40 (by sep_focus); wp_reach
        apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000003#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
          (by dsimp only [chunkedNoHeaderReceivedErrFrame]; sep_entail)
        exact hfrom_err hnone (by decide : KindNoHeap 0x8000000000000003#64) hsp_align
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
          ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
      | some iwt =>
        obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
        obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_ge
        obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
        by_cases hitag0 : key.toNat / 8 < 1
        · have hnone := hnone_of_loop_none (mergeLoopBin_of_tag_zero protoPrefixStep_chunked_noHeaderReceived_mergeField hgt_lim hd hk_ge hwt hitag0)
          have htag_zero : key.toNat / 8 = 0 := by omega
          apply SepWPpLscro.of_sepWP (mid := entry + 120#64)
          (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
          apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
          apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          apply SepWP.fold (chunkedNoHeaderReceivedPBCapAt_entails_pb A x.msgPtr cur.length m) (by sep_focus)
          conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_cells1_160 s0.sp]
          simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
          apply SepWP.exists_elim; intro v_err0; wp_steps
          apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
          apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
          wp_reach
          apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000005#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
            (by dsimp only [chunkedNoHeaderReceivedErrFrame]; sep_entail)
          exact hfrom_err hnone (by decide : KindNoHeap 0x8000000000000005#64) hsp_align
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
            ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
        · obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_ge hitag0
          have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
            rw [beq_eq_false_iff_ne]; intro h; have h1 := congrArg BitVec.toNat h
            simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1; omega
          apply SepWPpLscro.of_sepWP (mid := entry + 228#64)
          (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
          apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
          apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          apply SepWP.fold (chunkedNoHeaderReceivedPBCapAt_mono A x.msgPtr m hrest_le_cur) (by sep_focus)
          wp_steps; wp_reach
          apply SepWPpLscro.weaken_pre (P' := chunkedNoHeaderReceivedLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
            (by dsimp only [chunkedNoHeaderReceivedLoopPre]; sep_entail)
          exact hcont key iwt rest _ hd hk_ge hwt hitag0
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
            (by simp only [arm64_norm, hsm1, hand_wt]) (by simp only [arm64_norm, hsm1, hw1, hw1_2, hw1_zext1, hw1_zext2])
            (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
            (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m]) (by simp only [arm64_norm, hx25_m])
            ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

theorem chunkedNoHeaderReceived_loop_ok_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 261) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 291) (decodeVarint2Spec A))
    (hSkipCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 263) (skipField3Spec A))
    (hAuthCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A)))
    (hPolyCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 296) (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A)))
    {x : ChunkedNoHeaderReceivedMergeGhost} {R : SepProp} {s0 : State} {outerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hbs_lt : x.bs.length < 2 ^ 63) (hlim_lt : outerLimit < 2 ^ 63) :
    ∀ (n : Nat) (m : V1State.Chunked.NoHeaderReceived) (cur : List (BitVec 8)) (s : State),
      cur.length ≤ n → cur.length ≤ x.bs.length → IsDropSuffix x.bs cur →
      OptPolyDecoderBound m.receivingHdr cur.length →
      (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
        (mergeLoopBin V1State.Chunked.NoHeaderReceived.mergeField (cur.length - outerLimit) m cur outerLimit 98).map
          (fun m' => (m', x.bs.drop (x.bs.length - outerLimit))) →
      s.pc = (blkPl_308).base + 168#64 →
      s.status = .Running → s.sp = s0.sp - 128#64 → s.trace = s0.trace →
      s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s.readReg64 (Reg.gpr 24#5) = 1#64 →
      s.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s →
      SepWPpLscro lsmpl ((blkPC_308).rebase (blkPl_308).base H) (s0.readReg64 Reg.lr) s
        (chunkedNoHeaderReceivedLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
        (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  have htag1_step := fun {s m rest} (iwt : WireType) =>
    @chunkedNoHeaderReceived_tag1_step_placed _ A H hFromCall hPushCall hVarintCall hSkipCall hAuthCall x R s0 s m rest iwt outerLimit
  have htag2_step := fun {s m rest} (iwt : WireType) =>
    @chunkedNoHeaderReceived_tag2_step_placed _ A H hPushCall hPolyCall x R s0 s m rest iwt outerLimit
  have hskip_step := fun {s m rest} (iwt : WireType) (tag : Nat) =>
    @chunkedNoHeaderReceived_skip_step_placed _ A H hSkipCall x R s0 s m rest iwt tag outerLimit
  intro n; induction n with
  | zero =>
    intro m cur s hcur_n hcur_le hcur_suf _ hres hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hcs
    exact chunkedNoHeaderReceived_loop_le_exit_placed hFromCall (by omega) hsp_align hcur_le hcur_suf hlim_lt
      (fun hlt => by rw [hres, mergeLoopBin_lt_limit _ _ _ _ _ _ hlt]; rfl)
      (fun heq => by rw [hres, mergeLoopBin_eq_limit _ _ _ _ _ _ heq, ← heq, ← hcur_suf]; rfl)
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hcs
  | succ n ih =>
    intro m cur s hcur_n hcur_le hcur_suf hbound hres hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hcs
    by_cases hle_lim : cur.length ≤ outerLimit
    · exact chunkedNoHeaderReceived_loop_le_exit_placed hFromCall hle_lim hsp_align hcur_le hcur_suf hlim_lt
        (fun hlt => by rw [hres, mergeLoopBin_lt_limit _ _ _ _ _ _ hlt]; rfl)
        (fun heq => by rw [hres, mergeLoopBin_eq_limit _ _ _ _ _ _ heq, ← heq, ← hcur_suf]; rfl)
        hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hcs
    · have hcur_lt : cur.length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
      refine chunkedNoHeaderReceived_decode_key_step_placed hFromCall hVarintCall hle_lim hsp_align
        hcur_le hcur_lt hcur_suf (fun hml => by rw [hres, hml]; rfl) ?_ hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hcs
      intro key iwt rest s' hd hk_ge hwt hitag0 hpc' hrun' hsp' htr' hx8' hx1' hx19' hx20' hx21' hx22' hx23' hx24' hx25' hcs'
      obtain ⟨hx27', hx28', hvregs'⟩ := hcs'
      have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
      have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
      have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le
      have hrest_lt : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest_le hbs_lt
      have hrest_suf : IsDropSuffix x.bs rest := suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
      have hbound_rest : OptPolyDecoderBound m.receivingHdr rest.length := optPolyDecoderBound_mono hbound hrest_le_cur
      have htag_lt : key.toNat / 8 < 2 ^ 32 := by omega
      have hstep := mergeLoopBin_of_key_ok (m := m) (depth' := 98)
        protoPrefixStep_chunked_noHeaderReceived_mergeField hle_lim hd hk_ge hwt hitag0
      by_cases htag1 : key.toNat / 8 = 1
      · rw [htag1] at hx1' hstep; rw [chunkedNoHeaderReceived_mergeField_tag1] at hstep
        apply SepWPpLscro.of_sepWP (mid := entry + 296#64); wp_steps; wp_reach
        refine htag1_step iwt hsp_align hbs_lt hrest_le hrest_lt hrest_suf
          (fun huc_none => by rw [hres, hstep, huc_none]; rfl)
          (fun uc' rest' s'' huc_some hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hcs'' => ?_)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
          (by simp only [arm64_norm, hx8']) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
          (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23'])
          (by simp only [arm64_norm, hx24']) (by simp only [arm64_norm, hx25'])
          ⟨by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩
        have hr'_le : rest'.length ≤ rest.length := (proto_mergeMessage_suffix huc_some).1
        exact ih { m with uc := some uc' } rest' s'' (by omega) (Nat.le_trans hr'_le hrest_le)
          (suffix_trans hrest_le hrest_suf hr'_le (proto_mergeMessage_suffix huc_some).2)
          (optPolyDecoderBound_mono hbound_rest hr'_le)
          (by rw [hres, hstep, huc_some]; rfl)
          hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hcs''
      · by_cases htag2 : key.toNat / 8 = 2
        · rw [htag2] at hx1' hstep; rw [chunkedNoHeaderReceived_mergeField_tag2] at hstep
          apply SepWPpLscro.of_sepWP (mid := entry + 244#64); wp_steps; wp_reach
          refine htag2_step iwt hsp_align hrest_le hrest_suf hbound_rest
            (fun hpoly_none => by rw [hres, hstep, hpoly_none]; rfl)
            (fun d' rest' s'' hpoly_some hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hcs'' => ?_)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
            (by simp only [arm64_norm, hx8']) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
            (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23'])
            (by simp only [arm64_norm, hx24']) (by simp only [arm64_norm, hx25'])
            ⟨by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩
          have hr'_le : rest'.length ≤ rest.length := (proto_mergeMessage_suffix hpoly_some).1
          exact ih { m with receivingHdr := some d' } rest' s'' (by omega) (Nat.le_trans hr'_le hrest_le)
            (suffix_trans hrest_le hrest_suf hr'_le (proto_mergeMessage_suffix hpoly_some).2)
            (optPolyDecoderBound_of_merge hbound_rest hpoly_some)
            (by rw [hres, hstep, hpoly_some]; rfl)
            hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hcs''
        · obtain ⟨hb1_1, _⟩ := itag_beq_tag_false htag1 htag_lt (by decide : 1 < 2 ^ 32)
          obtain ⟨hb2_1, _⟩ := itag_beq_tag_false htag2 htag_lt (by decide : 2 < 2 ^ 32)
          have hb1_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 1#32) = false := by rw [sf_truncate32_ofNat64]; exact hb1_1
          have hb2_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 2#32) = false := by rw [sf_truncate32_ofNat64]; exact hb2_1
          have hb2_bne1 : (BitVec.ofNat 32 (key.toNat / 8) != 2#32) = true := by simp only [bne, hb2_1, Bool.not_false]
          have hb2_bne2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) != 2#32) = true := by simp only [bne, hb2_2, Bool.not_false]
          rw [chunkedNoHeaderReceived_mergeField_other m iwt rest 98 htag_lt htag1 htag2] at hstep
          apply SepWPpLscro.of_sepWP (mid := entry + 348#64); wp_steps; wp_reach
          refine hskip_step iwt (key.toNat / 8) hsp_align hrest_le hrest_lt hrest_suf htag_lt
            (fun hsf_none => by rw [hres, hstep, hsf_none]; rfl)
            (fun rest' s'' hsf_some hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hcs'' => ?_)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
            (by simp only [arm64_norm, hx8']) (by simp only [arm64_norm, hx1', sf_truncate32_ofNat64])
            (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
            (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23'])
            (by simp only [arm64_norm, hx24']) (by simp only [arm64_norm, hx25'])
            ⟨by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩
          have hr'_le : rest'.length ≤ rest.length := (skip_length (2 * rest.length + 2)).1 _ _ _ _ _ hsf_some
          exact ih m rest' s'' (by omega) (Nat.le_trans hr'_le hrest_le)
            (suffix_trans hrest_le hrest_suf hr'_le ((skip_suffix (2 * rest.length + 2)).1 _ _ _ _ _ hsf_some))
            (optPolyDecoderBound_mono hbound_rest hr'_le)
            (by rw [hres, hstep, hsf_some]; rfl)
            hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hcs''

theorem chunked_no_header_received_merge_placed_ok_of_contracts [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 261) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 291) (decodeVarint2Spec A))
    (hSkipCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 263) (skipField3Spec A))
    (hAuthCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A)))
    (hPolyCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 296) (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A))) :
    subroutine_ok ((blkPC_308).rebase (blkPl_308).base H)
      (blkPl_308).base
      (withLsCodeRoLoaded lsmpl (chunkedNoHeaderReceivedMergeSpec A)) := by
  apply subroutine_ok_withLsCodeRoLoaded_of_withLscroProp
  unfold withLscroProp chunkedNoHeaderReceivedMergeSpec
  wpp_init x s0
  have hbound : OptPolyDecoderBound x.msg.receivingHdr x.bs.length := h
  have hbs_lt : x.bs.length < 2 ^ 63 := by unfold OptPolyDecoderBound at hbound; omega
  replace hpc : s0.pc = (blkPl_308).base := hpc
  conv => arg 6; ext sf P_f; simp only [chunkedNoHeaderReceivedMergeSpec, sepConj_assoc, satisfies_pure_sepConj]
  change SepWPp ((blkPC_308).rebase (blkPl_308).base H) (s0.readReg64 Reg.lr) s0
    _ (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0)
  apply SepWPp.elim_lscroProp; intro hinv
  revert hinv; change SepWPpLscro lsmpl ((blkPC_308).rebase (blkPl_308).base H) (s0.readReg64 Reg.lr) s0
    _ (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0)
  have hret_err := @chunkedNoHeaderReceived_ret_err_exit_placed _ A H x R s0 x.msg
  have hfrom_err := @chunkedNoHeaderReceived_from_err_exit_placed _ A H hFromCall x R s0 x.msg
  have hloop := fun (outerLimit : Nat) (hlim_lt : outerLimit < 2 ^ 63) =>
    @chunkedNoHeaderReceived_loop_ok_placed _ A H hFromCall hPushCall hVarintCall hSkipCall hAuthCall hPolyCall x R s0 outerLimit hsp_align hbs_lt hlim_lt
  have hsaved :
      ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ⊢
      chunkedInlSavedRegs10 s0.sp s0 := Entails.refl _
  by_cases hwt_ld : x.wt = .lengthDelimited
  · have h_1' : (s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = 2#8 := by rw [h_1, hwt_ld]; rfl
    have hbeq := wt_beq_two_of_lengthDelimited h_1'
    have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = false := by
      simp only [bne, hbeq, Bool.not_true]
    have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = false := by
      rw [BytesMergeFacts.truncate32_zeroExtend64_and_255_eq, h_1']; decide
    have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = false := by
      revert h_1'; bv_bits
    apply SepWPpLscro.of_sepWP (mid := lsmpl.base 291)
    conv => arg 4; rw [stackAt_chunkedInl_prologue s0.sp, chunkedInlBelow_decodeVarint2 s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v1; apply SepWP.exists_elim; intro v2
    apply SepWP.exists_elim; intro v3; apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v5
    apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v7; apply SepWP.exists_elim; intro v8
    apply SepWP.exists_elim; intro v9
    wp_steps; apply SepWP.fold hsaved (by sep_focus); wp_reach
    refine SepWPpLscro.call_frame (x := ⟨x.bufRef, x.slot, x.ptr, x.bs⟩)
      (ret_pc := entry + 56#64) hVarintCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
      (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, h_3]; rfl)
      hbs_lt (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm]) hpan) ?_
    intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, _, _, _, _, _, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, h_2, h_3] at hpcm hrunm hspm hx19_m hx20_m hx27_m hx28_m hvregs_m
    cases hdv0 : decodeVarint x.bs with
    | none =>
      have hnone : (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
        rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_chunked_noHeaderReceived_mergeField]
        simp [mergeMessageBin, codecWireTypeToProto, proto_decodeVarint_toOption, hdv0]
      apply SepWPpLscro.of_sepWP (mid := entry + 128#64)
      (conv => arg 4; simp only [decodeVarint2Spec, hdv0, sepConj_assoc, arm64_norm])
      apply SepWP.pure_elim; rintro ⟨hsm0, htrm, hsm1⟩
      apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
      apply SepWP.fold (chunkedNoHeaderReceivedPBCapAt_entails_pb A x.msgPtr x.bs.length x.msg) (by sep_focus)
      wp_steps; wp_reach
      apply SepWPpLscro.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs)
        (by dsimp only [chunkedNoHeaderReceivedErrFrame]; sep_entail)
      exact hret_err hnone (by decide : 0 ≤ 3) hsm1 hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
        (by simp only [arm64_norm, htrm]) (by simp only [arm64_norm])
        ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
    | some p =>
      rcases p with ⟨len, rest0⟩
      have hrest0_lt_bs : rest0.length < x.bs.length := decodeVarint_length hdv0
      have hrest0_le : rest0.length ≤ x.bs.length := Nat.le_of_lt hrest0_lt_bs
      have hrest0_lt : rest0.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest0_le hbs_lt
      have hrest0_suf : IsDropSuffix x.bs rest0 := decodeVarint_suffix hdv0
      let rest0Ptr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length)
      by_cases hlt_len : rest0.length < len.toNat
      · have hule := ule_len_of_lt hlt_len hrest0_lt
        have hnone : (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
          rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_chunked_noHeaderReceived_mergeField]
          rcases hdv0_p : Proto.decodeVarint x.bs with e | ⟨len', rest0'⟩
          · have hdv0' : decodeVarint x.bs = none := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
            rw [hdv0] at hdv0'; nomatch hdv0'
          · have hdv0' : decodeVarint x.bs = some (len', rest0') := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
            rw [hdv0] at hdv0'; injection hdv0' with hp; injection hp with hl hr0; subst hl hr0
            simp [mergeMessageBin, codecWireTypeToProto, hdv0_p, Except.toOption, hlt_len]
        apply SepWPpLscro.of_sepWP (mid := entry + 120#64)
        (conv => arg 4; simp only [decodeVarint2Spec, hdv0, sliceCursorAfter_eq_split hrest0_le hrest0_suf,
          sliceCursorAt, memRegion_48_cells1_160 s0.sp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm])
        apply SepWP.exists_elim; intro v_stk0; apply SepWP.pure_elim; rintro ⟨⟨hsm0, hsm1⟩, htrm⟩
        apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
        apply SepWP.fold (chunkedNoHeaderReceivedPBCapAt_entails_pb A x.msgPtr x.bs.length x.msg) (by sep_focus)
        wp_steps
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot rest0Ptr (BitVec.ofNat 64 rest0.length)) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus)
        wp_reach
        apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000007#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs)
          (by dsimp only [chunkedNoHeaderReceivedErrFrame]; sep_entail)
        exact hfrom_err hnone (by decide : KindNoHeap 0x8000000000000007#64) hsp_align
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm])
          ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
      · have hule := ule_len_of_ge hlt_len hrest0_lt
        have hsub := bv_len_sub_limit hlt_len
        have hlim_lt : rest0.length - len.toNat < 2 ^ 63 := by omega
        have hres0 : (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
            (mergeLoopBin V1State.Chunked.NoHeaderReceived.mergeField (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 98).map
              (fun m' => (m', x.bs.drop (x.bs.length - (rest0.length - len.toNat)))) := by
          rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_chunked_noHeaderReceived_mergeField]
          rcases hdv0_p : Proto.decodeVarint x.bs with e | ⟨len', rest0'⟩
          · have hdv0' : decodeVarint x.bs = none := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
            rw [hdv0] at hdv0'; nomatch hdv0'
          · have hdv0' : decodeVarint x.bs = some (len', rest0') := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
            rw [hdv0] at hdv0'; injection hdv0' with hp; injection hp with hl hr0; subst hl hr0
            have hdrop_eq : x.bs.drop (x.bs.length - (rest0.length - len.toNat)) = rest0.drop len.toNat := by
              conv_rhs => rw [hrest0_suf, List.drop_drop]
              congr 1; omega
            simp only [mergeMessageBin, codecWireTypeToProto, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
              hdv0_p, Except.toOption, hlt_len, hdrop_eq]
            rcases mergeLoopBin V1State.Chunked.NoHeaderReceived.mergeField (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 98 with _ | m' <;> rfl
        apply SepWPpLscro.of_sepWP (mid := entry + 168#64)
        (conv => arg 4; simp only [decodeVarint2Spec, hdv0, sliceCursorAfter_eq_split hrest0_le hrest0_suf,
          sliceCursorAt, sepConj_assoc, arm64_norm])
        apply SepWP.pure_elim; rintro ⟨⟨hsm0, hsm1⟩, htrm⟩
        apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
        apply SepWP.fold (chunkedNoHeaderReceivedPBCapAt_mono A x.msgPtr x.msg hrest0_le) (by sep_focus)
        wp_steps
        apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus)
        wp_reach
        apply SepWPpLscro.weaken_pre (P' := chunkedNoHeaderReceivedLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs rest0)
          (by dsimp only [chunkedNoHeaderReceivedLoopPre, sliceCursorAfter]; sep_entail)
        exact hloop (rest0.length - len.toNat) hlim_lt rest0.length x.msg rest0 _ (Nat.le_refl _) hrest0_le hrest0_suf
          (optPolyDecoderBound_mono hbound hrest0_le) hres0
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm])
          (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm])
          (by simp only [arm64_norm, hsm1, hsub]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  · have hbeq := wt_beq_two_of_ne_lengthDelimited h_1 hwt_ld
    have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = true := by
      simp only [bne, hbeq, Bool.not_false]
    have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = true := by
      rw [BytesMergeFacts.truncate32_zeroExtend64_and_255_eq, h_1]
      revert hwt_ld; cases x.wt <;> intro hwt_ld <;> first | contradiction | decide
    have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = true := by
      rw [show BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) =
            BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 by bv_bits]; exact hbne1
    have hnone : (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
      rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_chunked_noHeaderReceived_mergeField]
      unfold mergeMessageBin; revert hwt_ld; cases x.wt <;> intro hwt_ld <;> first | contradiction | rfl
    apply SepWPpLscro.of_sepWP (mid := entry + 120#64)
    conv => arg 4; rw [stackAt_chunkedInl_prologue s0.sp, sliceCursorAt, memRegion_48_wtErr160 s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v1; apply SepWP.exists_elim; intro v2
    apply SepWP.exists_elim; intro v3; apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v5
    apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v7; apply SepWP.exists_elim; intro v8
    apply SepWP.exists_elim; intro v9; apply SepWP.exists_elim; intro b_wt1
    apply SepWP.exists_elim; intro b_wt0; apply SepWP.exists_elim; intro v_wt0
    wp_steps; apply SepWP.fold hsaved (by sep_focus)
    apply SepWP.fold (wtErr160_entails_memRegion40 s0.sp _ _) (by sep_focus)
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot x.ptr (BitVec.ofNat 64 x.bs.length)) (by sep_focus)
    apply SepWP.fold (chunkedNoHeaderReceivedPBCapAt_entails_pb A x.msgPtr x.bs.length x.msg) (by sep_focus); wp_reach
    apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000006#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs)
      (by dsimp only [chunkedNoHeaderReceivedErrFrame]; sep_entail)
    exact hfrom_err hnone (by decide : KindNoHeap 0x8000000000000006#64) hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      ⟨by simp only [arm64_norm], by simp only [arm64_norm]⟩

end CryptoVerification.SpqrV1.Prost.MessageMerge

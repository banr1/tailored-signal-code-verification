/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommon
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirection
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Inner `Unchunked.EkSent` Merge & Exit Lemmas for `Chunked.HeaderSent::merge` (`0x4fdb0`, Block `302`)

Proves the epilogue, decode-error exits, and inlined `Unchunked.EkSent` field-merge loop inside
`prost::encoding::message::merge::<spqr::proto::pq_ratchet::v1_state::chunked::HeaderSent, &mut &[u8]>`
in both `.inImage img` and `[LibsignalPlacement]` forms.
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
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
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
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero

gen_decodes libsignalSessionCode_tree chunkedHeaderSentMergeBin [
  0x4a9b8 → 0x4ae0c
]

macro "chunkedHeaderSentMerge_fetches " b:term:max H:term:max k0:num len:num : tactic =>
  `(tactic| code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.SpqrV1.Prost.MessageMerge.chunkedHeaderSentMergeBin $b $H
    CryptoVerification.SpqrV1.Prost.MessageMerge.chunkedHeaderSentMerge_fnOff 0x4a9b8 $k0 $len)

/-! ## 1. Pure `mergeField` Step Lemmas -/

theorem unchunkedEkSent_mergeField_tag1 (m : V1State.Unchunked.EkSent) (iwt : WireType) (rest : List (BitVec 8)) (depth' : Nat) :
    (V1State.Unchunked.EkSent.mergeField m (BitVec.ofNat 32 1) (codecWireTypeToProto iwt) rest depth').toOption =
      if iwt = .varint then (decodeVarint rest).map (fun (v, rest') => ({ m with epoch := v }, rest')) else none := by
  unfold V1State.Unchunked.EkSent.mergeField
  simp only [show (BitVec.ofNat 32 1 == 1#32) = true from rfl, ↓reduceIte]
  unfold Proto.mergeUint64 Proto.checkWireType
  cases iwt <;> simp only [codecWireTypeToProto, beq_self_eq_true, ↓reduceIte]
  case varint =>
    rcases hdv : Proto.decodeVarint rest with e | ⟨v, rest'⟩
    · have hdv' : decodeVarint rest = none := by rw [← proto_decodeVarint_toOption rest, hdv]; rfl
      simp [hdv', Bind.bind, Except.bind, Except.toOption]
    · have hdv' : decodeVarint rest = some (v, rest') := by rw [← proto_decodeVarint_toOption rest, hdv]; rfl
      simp [hdv', Bind.bind, Except.bind, Except.toOption]
  all_goals rfl

theorem unchunkedEkSent_mergeField_tag2 (m : V1State.Unchunked.EkSent) (iwt : WireType) (rest : List (BitVec 8)) (depth' : Nat) :
    (V1State.Unchunked.EkSent.mergeField m (BitVec.ofNat 32 2) (codecWireTypeToProto iwt) rest depth').toOption =
      (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto iwt) (m.auth.getD default) rest depth').toOption.map
        (fun (v, rest') => ({ m with auth := some v }, rest')) := by
  unfold V1State.Unchunked.EkSent.mergeField Proto.mergeOptMessage
  simp only [show (BitVec.ofNat 32 2 == 1#32) = false from rfl, show (BitVec.ofNat 32 2 == 2#32) = true from rfl, Bool.false_eq_true, ↓reduceIte]
  rcases Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto iwt) (m.auth.getD default) rest depth' with _ | ⟨v, r⟩ <;> rfl

theorem unchunkedEkSent_mergeField_tag3 (m : V1State.Unchunked.EkSent) (iwt : WireType) (rest : List (BitVec 8)) (depth' : Nat) :
    (V1State.Unchunked.EkSent.mergeField m (BitVec.ofNat 32 3) (codecWireTypeToProto iwt) rest depth').toOption =
      (mergeBytes iwt rest).map (fun (v, rest') => ({ m with dk := v }, rest')) := by
  unfold V1State.Unchunked.EkSent.mergeField
  simp only [show (BitVec.ofNat 32 3 == 1#32) = false from rfl, show (BitVec.ofNat 32 3 == 2#32) = false from rfl,
    show (BitVec.ofNat 32 3 == 3#32) = true from rfl, Bool.false_eq_true, ↓reduceIte]
  have hbm := proto_mergeBytes_toOption (codecWireTypeToProto iwt) rest
  rw [protoWireTypeToCodec_codecWireTypeToProto] at hbm
  rcases h : Proto.mergeBytes (codecWireTypeToProto iwt) rest with _ | ⟨v, r⟩ <;> { rw [h] at hbm; dsimp [Except.toOption] at hbm; rw [← hbm]; rfl }

theorem unchunkedEkSent_mergeField_other (m : V1State.Unchunked.EkSent) {tag : Nat} (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) (htag_lt : tag < 2 ^ 32) (hne1 : tag ≠ 1) (hne2 : tag ≠ 2) (hne3 : tag ≠ 3) :
    (V1State.Unchunked.EkSent.mergeField m (BitVec.ofNat 32 tag) (codecWireTypeToProto iwt) rest depth').toOption =
      (skipField (2 * rest.length + 2) depth' tag iwt rest).map (fun rest' => (m, rest')) := by
  have hb1 : (BitVec.ofNat 32 tag == 1#32) = false := (itag_beq_tag_false hne1 htag_lt (by decide)).1
  have hb2 : (BitVec.ofNat 32 tag == 2#32) = false := (itag_beq_tag_false hne2 htag_lt (by decide)).1
  have hb3 : (BitVec.ofNat 32 tag == 3#32) = false := (itag_beq_tag_false hne3 htag_lt (by decide)).1
  have htag_toNat : (BitVec.ofNat 32 tag).toNat = tag := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htag_lt]
  unfold V1State.Unchunked.EkSent.mergeField; simp only [hb1, hb2, hb3, Bool.false_eq_true, ↓reduceIte]
  have hsf' := proto_skipField_toOption (codecWireTypeToProto iwt) (BitVec.ofNat 32 tag) rest depth'
  rw [htag_toNat, protoWireTypeToCodec_codecWireTypeToProto] at hsf'
  rcases hsf : Proto.skipField (codecWireTypeToProto iwt) (BitVec.ofNat 32 tag) rest depth' with _ | rest' <;>
    { rw [hsf] at hsf'; dsimp [Except.toOption] at hsf'; rw [← hsf']; rfl }

theorem chunkedHeaderSent_mergeField_tag1 (m : V1State.Chunked.HeaderSent) (iwt : WireType) (rest : List (BitVec 8)) (depth' : Nat) :
    (V1State.Chunked.HeaderSent.mergeField m (BitVec.ofNat 32 1) (codecWireTypeToProto iwt) rest depth').toOption =
      (Proto.mergeMessage V1State.Unchunked.EkSent.mergeField (codecWireTypeToProto iwt) (m.uc.getD default) rest depth').toOption.map
        (fun (v, rest') => ({ m with uc := some v }, rest')) := by
  unfold V1State.Chunked.HeaderSent.mergeField Proto.mergeOptMessage; simp only [beq_self_eq_true, ↓reduceIte]
  rcases Proto.mergeMessage V1State.Unchunked.EkSent.mergeField (codecWireTypeToProto iwt) (m.uc.getD default) rest depth' with _ | ⟨v, r⟩ <;> rfl

theorem chunkedHeaderSent_mergeField_tag2 (m : V1State.Chunked.HeaderSent) (iwt : WireType) (rest : List (BitVec 8)) (depth' : Nat) :
    (V1State.Chunked.HeaderSent.mergeField m (BitVec.ofNat 32 2) (codecWireTypeToProto iwt) rest depth').toOption =
      (Proto.mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto iwt) (m.sendingEk.getD default) rest depth').toOption.map
        (fun (v, rest') => ({ m with sendingEk := some v }, rest')) := by
  unfold V1State.Chunked.HeaderSent.mergeField Proto.mergeOptMessage
  simp only [show (BitVec.ofNat 32 2 == 1#32) = false from rfl, show (BitVec.ofNat 32 2 == 2#32) = true from rfl, Bool.false_eq_true, ↓reduceIte]
  rcases Proto.mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto iwt) (m.sendingEk.getD default) rest depth' with _ | ⟨v, r⟩ <;> rfl

theorem chunkedHeaderSent_mergeField_tag3 (m : V1State.Chunked.HeaderSent) (iwt : WireType) (rest : List (BitVec 8)) (depth' : Nat) :
    (V1State.Chunked.HeaderSent.mergeField m (BitVec.ofNat 32 3) (codecWireTypeToProto iwt) rest depth').toOption =
      (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto iwt) (m.receivingCt1.getD default) rest depth').toOption.map
        (fun (v, rest') => ({ m with receivingCt1 := some v }, rest')) := by
  unfold V1State.Chunked.HeaderSent.mergeField Proto.mergeOptMessage
  simp only [show (BitVec.ofNat 32 3 == 1#32) = false from rfl, show (BitVec.ofNat 32 3 == 2#32) = false from rfl,
    show (BitVec.ofNat 32 3 == 3#32) = true from rfl, Bool.false_eq_true, ↓reduceIte]
  rcases Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto iwt) (m.receivingCt1.getD default) rest depth' with _ | ⟨v, r⟩ <;> rfl

theorem chunkedHeaderSent_mergeField_other (m : V1State.Chunked.HeaderSent) {tag : Nat} (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) (htag_lt : tag < 2 ^ 32) (hne1 : tag ≠ 1) (hne2 : tag ≠ 2) (hne3 : tag ≠ 3) :
    (V1State.Chunked.HeaderSent.mergeField m (BitVec.ofNat 32 tag) (codecWireTypeToProto iwt) rest depth').toOption =
      (skipField (2 * rest.length + 2) depth' tag iwt rest).map (fun rest' => (m, rest')) := by
  have hb1 : (BitVec.ofNat 32 tag == 1#32) = false := (itag_beq_tag_false hne1 htag_lt (by decide)).1
  have hb2 : (BitVec.ofNat 32 tag == 2#32) = false := (itag_beq_tag_false hne2 htag_lt (by decide)).1
  have hb3 : (BitVec.ofNat 32 tag == 3#32) = false := (itag_beq_tag_false hne3 htag_lt (by decide)).1
  have htag_toNat : (BitVec.ofNat 32 tag).toNat = tag := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htag_lt]
  unfold V1State.Chunked.HeaderSent.mergeField; simp only [hb1, hb2, hb3, Bool.false_eq_true, ↓reduceIte]
  have hsf' := proto_skipField_toOption (codecWireTypeToProto iwt) (BitVec.ofNat 32 tag) rest depth'
  rw [htag_toNat, protoWireTypeToCodec_codecWireTypeToProto] at hsf'
  rcases hsf : Proto.skipField (codecWireTypeToProto iwt) (BitVec.ofNat 32 tag) rest depth' with _ | rest' <;>
    { rw [hsf] at hsf'; dsimp [Except.toOption] at hsf'; rw [← hsf']; rfl }

/-! ## 2. Loop Preconditions and Shared Error Exits -/

/-- Outer loop-header separation-logic bundle at `+0x0a8` (`entry + 168#64`). -/
def chunkedHeaderSentLoopPre (A : RustAlloc) (s0 : State) (msgPtr bufRef slot ptr : BitVec 64)
    (m : V1State.Chunked.HeaderSent) (bs cur : List (BitVec 8)) : SepProp :=
  chunkedHeaderSentPBCapAt A msgPtr cur.length m ∗
    stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
    memRegion (s0.sp - 128#64) 48 ∗
    chunkedInlSavedRegs10 s0.sp s0 ∗ (bufRef ↦₆₄ slot) ∗ sliceCursorAfter slot ptr bs cur ∗ A.pool

/-- Inner `Unchunked.EkSent` loop-header separation-logic bundle at `+0x1d0` (`entry + 464#64`). -/
def chunkedHeaderSentUcLoopPre (A : RustAlloc) (s0 : State) (msgPtr bufRef slot ptr : BitVec 64)
    (uc : V1State.Unchunked.EkSent) (sendingEk : Option PolynomialEncoder) (receivingCt1 : Option PolynomialDecoder) (bs cur : List (BitVec 8)) : SepProp :=
  unchunked3CapAt A msgPtr cur.length uc.epoch uc.auth uc.dk ∗
    optPolynomialEncoderPBAt A (msgPtr + 80#64) sendingEk ∗
    optPolynomialDecoderPBAt A (msgPtr + 136#64) receivingCt1 ∗
    stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
    memRegion (s0.sp - 128#64) 48 ∗
    chunkedInlSavedRegs10 s0.sp s0 ∗ (bufRef ↦₆₄ slot) ∗ sliceCursorAfter slot ptr bs cur ∗ A.pool

/-- Error-exit separation-logic bundle (with `chunkedHeaderSentPBAt`). -/
def chunkedHeaderSentErrFrame (A : RustAlloc) (s0 : State) (msgPtr bufRef slot ptr : BitVec 64) (m : V1State.Chunked.HeaderSent) (bs : List (BitVec 8)) : SepProp :=
  chunkedInlSavedRegs10 s0.sp s0 ∗
    chunkedHeaderSentPBAt A msgPtr m ∗ (bufRef ↦₆₄ slot) ∗ memRegion slot 16 ∗ (ptr ↦ₛ bs) ∗ A.pool

theorem unchunked3CapAt_entails_chunkedHeaderSentPBAt (A : RustAlloc) (a : BitVec 64)
    (n : Nat) (uc : V1State.Unchunked.EkSent) (sendingEk : Option PolynomialEncoder) (receivingCt1 : Option PolynomialDecoder) :
    unchunked3CapAt A a n uc.epoch uc.auth uc.dk ∗
      optPolynomialEncoderPBAt A (a + 80#64) sendingEk ∗
      optPolynomialDecoderPBAt A (a + 136#64) receivingCt1 ⊢
      chunkedHeaderSentPBAt A a { uc := some uc, sendingEk := sendingEk, receivingCt1 := receivingCt1 } :=
  sepConj_mono_left (unchunked3CapAt_entails_unchunked3At A a n uc.epoch uc.auth uc.dk)

/-- Shared error return from `+0x07c` (`entry + 124#64`) when `x1 = err ≠ 0#64` owns `decodeErrorAtStackLen A err n` (`n ≤ 3`). -/
theorem chunkedHeaderSent_ret_err_exit {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    {x : ChunkedHeaderSentMergeGhost} {R : SepProp} {s0 : State} {m : V1State.Chunked.HeaderSent} {s : State} {err : BitVec 64} {n : Nat}
    (hnone : (Proto.mergeMessage V1State.Chunked.HeaderSent.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hn : n ≤ 3) (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName + 124#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hx1 : s.readReg64 (Reg.gpr 1#5) = err)
    (hcs : ChunkedInl10CalleeSaved s0 s) : SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
      (decodeErrorAtStackLen A err n ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
        memRegion (s0.sp - 128#64) 48 ∗
        chunkedHeaderSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (WppPost (chunkedHeaderSentMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; chunkedHeaderSentMerge_fetches img.base H 124 32
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName = entry; examples_hide_fetches
  apply SepWPpIn.of_sepWP_ret; unfold WppPost chunkedHeaderSentMergeSpec
  simp only [hnone, chunkedHeaderSentErrFrame, chunkedInlSavedRegs10,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp, hx1]
  wp_steps
  have hle3 : decodeErrorAtStackLen A err n ⊢ ∃∗ k : Nat, ⌜k ≤ 3⌝ ∗ decodeErrorAtStackLen A err k := by
    refine Entails.trans ?_ (Entails.sepExists_intro n)
    rw [pure_sepConj_of_true hn]; exact Entails.refl _
  apply SepWP.fold hle3 (by sep_focus); apply SepWP.fold (chunkedHeaderSentPBAt_entails_exists A x.msgPtr m) (by sep_focus)
  apply SepWP.fold (stackAt_chunkedInl10_epilogue s0.sp s0) (by unfold chunkedInlSavedRegs10; sep_focus)
  wp_done

/-- Shared exit from `+0x070` (`entry + 112#64`): calls `DecodeError::from` on `(s0.sp - 128#64, w)` and returns. -/
theorem chunkedHeaderSent_from_err_exit {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName + 0xffffffffffffaff0#64) (decodeErrorFromSpec A))
    {x : ChunkedHeaderSentMergeGhost} {R : SepProp} {s0 : State} {m : V1State.Chunked.HeaderSent} {s : State} {w : BitVec 64}
    (hnone : (Proto.mergeMessage V1State.Chunked.HeaderSent.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hw : KindNoHeap w) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName + 112#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s (((s0.sp - 128#64) ↦₆₄ w) ∗ memRegion (s0.sp - 120#64) 40 ∗
        stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
        chunkedHeaderSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (WppPost (chunkedHeaderSentMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; chunkedHeaderSentMerge_fetches img.base H 112 44
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName = entry; examples_hide_fetches
  apply SepWPpIn.of_sepWP (mid := entry + 0xffffffffffffaff0#64)
  conv => arg 4; rw [chunkedInlBelow_decodeErrorHook s0.sp, chunkedHeaderSentErrFrame]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpIn.call_frame (x := (s0.sp - 128#64, w)) (ret_pc := entry + 120#64) hFromCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorFromSpec]; simp only [arm64_norm, hsp]; rfl)
    hw (by sep_focus) (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, _, _, _, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx27, hx28, hvregs] at hpcm hspm hx27_m hx28_m hvregs_m
  apply SepWPpIn.of_sepWP_ret; unfold WppPost chunkedHeaderSentMergeSpec
  simp only [decodeErrorFromSpec, hnone, chunkedInlSavedRegs10,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp, hspm]
  apply SepWP.fold (chunkedInlBelow_decodeErrorHook_entails s0.sp) (by sep_focus); apply SepWP.fold (memRegion8_memRegion40_entails_48_160 s0.sp) (by sep_focus)
  wp_steps; apply SepWP.fold (decodeErrorWith_zero_entails_le3_inl A _) (by sep_focus)
  apply SepWP.fold (chunkedHeaderSentPBAt_entails_exists A x.msgPtr m) (by sep_focus)
  apply SepWP.fold (stackAt_chunkedInl10_epilogue s0.sp s0) (by unfold chunkedInlSavedRegs10; sep_focus)
  wp_done

/-- Inner error exit at `+0x318` (`entry + 792#64`): pushes `("HeaderSent", "uc")` onto `x1 = err` (`n ≤ 2`) and returns. -/
theorem chunkedHeaderSent_uc_push_exit {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName + 0xffffffffffffacf8#64) (decodeErrorPushSpec A))
    {x : ChunkedHeaderSentMergeGhost} {R : SepProp} {s0 : State} {m : V1State.Chunked.HeaderSent} {s : State} {err : BitVec 64} {n : Nat}
    (hnone : (Proto.mergeMessage V1State.Chunked.HeaderSent.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hn : n ≤ 2) (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName + 792#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hx1 : s.readReg64 (Reg.gpr 1#5) = err)
    (hcs : ChunkedInl10CalleeSaved s0 s) : SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
      (decodeErrorAtStackLen A err n ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
        memRegion (s0.sp - 128#64) 48 ∗
        chunkedHeaderSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (WppPost (chunkedHeaderSentMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  have hret := @chunkedHeaderSent_ret_err_exit img A H x R s0 m; chunkedHeaderSentMerge_fetches img.base H 792 44
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName = entry; examples_hide_fetches
  apply SepWPpIn.of_sepWP (mid := entry + 0xffffffffffffacf8#64)
  conv => arg 4; rw [chunkedInlBelow_decodeErrorHook s0.sp, memRegion_48_cells1_160 s0.sp, chunkedHeaderSentErrFrame]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v_stk0; wp_steps; wp_reach
  refine SepWPpIn.call_frame (x := (s0.sp - 128#64, err, n)) (ret_pc := entry + 828#64) hPushCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorPushSpec]; simp only [arm64_norm, hsp, hx1]; rfl) (by omega : n < 2 ^ 32) (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, _, _, _, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx27, hx28, hvregs] at hpcm hspm hx27_m hx28_m hvregs_m
  apply SepWPpIn.of_sepWP (mid := entry + 124#64); (conv => arg 4; simp only [decodeErrorPushSpec, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; intro htrm
  apply SepWP.fold (chunkedInlBelow_decodeErrorHook_entails s0.sp) (by sep_focus); wp_steps
  apply SepWP.fold (pointsTo64_memRegion40_entails_48_160 s0.sp err) (by sep_focus); wp_reach
  apply SepWPpIn.weaken_pre (P' := decodeErrorAtStackLen A err (n + 1) ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedHeaderSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
    (by dsimp only [chunkedHeaderSentErrFrame]; sep_entail)
  exact hret hnone (by omega : n + 1 ≤ 3) herr hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
    (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm]) ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

/-- Inner error exit at `+0x30c` (`entry + 780#64`): calls `DecodeError::from` on `(s0.sp - 128#64, w)` and chains into `uc_push_exit`. -/
theorem chunkedHeaderSent_uc_from_push_exit {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName + 0xffffffffffffaff0#64) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName + 0xffffffffffffacf8#64) (decodeErrorPushSpec A))
    {x : ChunkedHeaderSentMergeGhost} {R : SepProp} {s0 : State} {m : V1State.Chunked.HeaderSent} {s : State} {w : BitVec 64}
    (hnone : (Proto.mergeMessage V1State.Chunked.HeaderSent.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hw : KindNoHeap w) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName + 780#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s (((s0.sp - 128#64) ↦₆₄ w) ∗ memRegion (s0.sp - 120#64) 40 ∗
        stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
        chunkedHeaderSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (WppPost (chunkedHeaderSentMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  have hpush := @chunkedHeaderSent_uc_push_exit img A H hPushCall x R s0 m; chunkedHeaderSentMerge_fetches img.base H 780 12
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName = entry; examples_hide_fetches
  apply SepWPpIn.of_sepWP (mid := entry + 0xffffffffffffaff0#64)
  conv => arg 4; rw [chunkedInlBelow_decodeErrorHook s0.sp, chunkedHeaderSentErrFrame]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpIn.call_frame (x := (s0.sp - 128#64, w)) (ret_pc := entry + 788#64) hFromCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorFromSpec]; simp only [arm64_norm, hsp]; rfl)
    hw (by sep_focus) (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, _, _, _, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx27, hx28, hvregs] at hpcm hspm hx27_m hx28_m hvregs_m
  apply SepWPpIn.of_sepWP (mid := entry + 792#64)
  (conv => arg 4; simp only [decodeErrorFromSpec, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨hsm0, htrm⟩
  apply SepWP.fold (chunkedInlBelow_decodeErrorHook_entails s0.sp) (by sep_focus); apply SepWP.fold (memRegion8_memRegion40_entails_48_160 s0.sp) (by sep_focus)
  wp_steps; wp_reach
  apply SepWPpIn.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedHeaderSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
    (by dsimp only [chunkedHeaderSentErrFrame]; sep_entail)
  exact hpush hnone (by decide : 0 ≤ 2) hsm0 hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
    (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm]) ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

/-- Inner field error exit at `+0x430` (`entry + 1072#64`): calls `DecodeError::push` on `(s0.sp - 128#64, err, n)` (`n ≤ 1`),
loads `x1` from `[sp]`, and jumps to `uc_push_exit` (`+0x318`). -/
theorem chunkedHeaderSent_uc_field_push_exit {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName + 0xffffffffffffacf8#64) (decodeErrorPushSpec A))
    {x : ChunkedHeaderSentMergeGhost} {R : SepProp} {s0 : State} {m : V1State.Chunked.HeaderSent} {s : State} {err : BitVec 64} {n : Nat}
    (hnone : (Proto.mergeMessage V1State.Chunked.HeaderSent.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hn : n ≤ 1) (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName + 1072#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = s0.sp - 128#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s (((s0.sp - 128#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A err n ∗
        memRegion (s0.sp - 120#64) 40 ∗
        stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
        chunkedHeaderSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (WppPost (chunkedHeaderSentMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  have hpush := @chunkedHeaderSent_uc_push_exit img A H hPushCall x R s0 m; chunkedHeaderSentMerge_fetches img.base H 1072 12
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName = entry; examples_hide_fetches
  apply SepWPpIn.of_sepWP (mid := entry + 0xffffffffffffacf8#64)
  conv => arg 4; rw [chunkedInlBelow_decodeErrorHook s0.sp, chunkedHeaderSentErrFrame]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpIn.call_frame (x := (s0.sp - 128#64, err, n)) (ret_pc := entry + 1076#64) hPushCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorPushSpec]; simp only [arm64_norm, hsp, hx0]; rfl) (by omega : n < 2 ^ 32) (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, _, _, _, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx27, hx28, hvregs] at hpcm hspm hx27_m hx28_m hvregs_m
  apply SepWPpIn.of_sepWP (mid := entry + 792#64); (conv => arg 4; simp only [decodeErrorPushSpec, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; intro htrm
  apply SepWP.fold (chunkedInlBelow_decodeErrorHook_entails s0.sp) (by sep_focus); wp_steps
  apply SepWP.fold (pointsTo64_memRegion40_entails_48_160 s0.sp err) (by sep_focus); wp_reach
  apply SepWPpIn.weaken_pre (P' := decodeErrorAtStackLen A err (n + 1) ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedHeaderSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
    (by dsimp only [chunkedHeaderSentErrFrame]; sep_entail)
  exact hpush hnone (by omega : n + 1 ≤ 2) herr hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
    (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm]) ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

/-- Shared outer error exit at `+0x338` (`entry + 824#64`): calls `DecodeError::push` on `(s0.sp - 128#64, err, n)` (`n ≤ 2`),
loads `x1` from `[sp]`, and jumps to `ret_err_exit` (`+0x07c`). -/
theorem chunkedHeaderSent_push_ret_exit {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName + 0xffffffffffffacf8#64) (decodeErrorPushSpec A))
    {x : ChunkedHeaderSentMergeGhost} {R : SepProp} {s0 : State} {m : V1State.Chunked.HeaderSent} {s : State} {err : BitVec 64} {n : Nat}
    (hnone : (Proto.mergeMessage V1State.Chunked.HeaderSent.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hn : n ≤ 2) (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName + 824#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = s0.sp - 128#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s (((s0.sp - 128#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A err n ∗
        memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
        chunkedHeaderSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (WppPost (chunkedHeaderSentMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  have hret := @chunkedHeaderSent_ret_err_exit img A H x R s0 m; chunkedHeaderSentMerge_fetches img.base H 824 12
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName = entry; examples_hide_fetches
  apply SepWPpIn.of_sepWP (mid := entry + 0xffffffffffffacf8#64)
  conv => arg 4; rw [chunkedInlBelow_decodeErrorHook s0.sp, chunkedHeaderSentErrFrame]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpIn.call_frame (x := (s0.sp - 128#64, err, n)) (ret_pc := entry + 828#64) hPushCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorPushSpec]; simp only [arm64_norm, hsp, hx0]; rfl) (by omega : n < 2 ^ 32) (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, _, _, _, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx27, hx28, hvregs] at hpcm hspm hx27_m hx28_m hvregs_m
  apply SepWPpIn.of_sepWP (mid := entry + 124#64); (conv => arg 4; simp only [decodeErrorPushSpec, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; intro htrm
  apply SepWP.fold (chunkedInlBelow_decodeErrorHook_entails s0.sp) (by sep_focus); wp_steps
  apply SepWP.fold (pointsTo64_memRegion40_entails_48_160 s0.sp err) (by sep_focus); wp_reach
  apply SepWPpIn.weaken_pre (P' := decodeErrorAtStackLen A err (n + 1) ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedHeaderSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
    (by dsimp only [chunkedHeaderSentErrFrame]; sep_entail)
  exact hret hnone (by omega : n + 1 ≤ 3) herr hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
    (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm]) ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

/-! ## 3. Inner `Unchunked.EkSent` Field Steps -/

@[local simp, local arm64_norm]
private theorem bv64_add24_add24 (a : BitVec 64) : a + 24#64 + 24#64 = a + 48#64 := by bv_omega
@[local simp, local arm64_norm]
private theorem bv64_add24_add32 (a : BitVec 64) : a + 24#64 + 32#64 = a + 56#64 := by bv_omega
@[local simp, local arm64_norm]
private theorem bv64_add24_add40 (a : BitVec 64) : a + 24#64 + 40#64 = a + 64#64 := by bv_omega
@[local simp, local arm64_norm]
private theorem bv64_add40_add8 (a : BitVec 64) : a + 40#64 + 8#64 = a + 48#64 := by bv_omega
@[local simp, local arm64_norm]
private theorem bv64_add56_add8 (a : BitVec 64) : a + 56#64 + 8#64 = a + 64#64 := by bv_omega

/-- Step lemma for unknown field tags in `Unchunked.EkSent` (`tag ∉ {1, 2, 3}`) at `+0x21c` (`entry + 540#64`). -/
theorem chunkedHeaderSent_uc_skip_step {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName + 0xffffffffffffacf8#64) (decodeErrorPushSpec A))
    (hSkipCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName + 0xffffffffffffbdc4#64) (skipField3Spec A))
    {x : ChunkedHeaderSentMergeGhost} {R : SepProp} {s0 s : State} {uc : V1State.Unchunked.EkSent} {sendingEk : Option PolynomialEncoder}
    {receivingCt1 : Option PolynomialDecoder} {rest : List (BitVec 8)} {iwt : WireType} {tag outerLimit innerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest) (htag_lt : tag < 2 ^ 32)
    (hnone_of_sf : skipField (2 * rest.length + 2) 97 tag iwt rest = none →
      (Proto.mergeMessage V1State.Chunked.HeaderSent.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (rest' : List (BitVec 8)) (s' : State),
      skipField (2 * rest.length + 2) 97 tag iwt rest = some rest' → s'.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName + 464#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace → s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit → ChunkedInl10CalleeSaved s0 s' →
      SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s'
        (chunkedHeaderSentUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr uc sendingEk receivingCt1 x.bs rest')
        (WppPost (chunkedHeaderSentMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName + 540#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : (s.readReg64 (Reg.gpr 1#5)).setWidth 32 = BitVec.ofNat 32 tag)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
      (chunkedHeaderSentUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr uc sendingEk receivingCt1 x.bs rest)
      (WppPost (chunkedHeaderSentMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hpush_exit := @chunkedHeaderSent_uc_push_exit img A H hPushCall x R s0 { uc := some uc, sendingEk := sendingEk, receivingCt1 := receivingCt1 }
  chunkedHeaderSentMerge_fetches img.base H 540 20; chunkedHeaderSentMerge_fetches img.base H 460 4
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName = entry; examples_hide_fetches
  apply SepWPpIn.of_sepWP (mid := entry + 0xffffffffffffbdc4#64)
  conv => arg 4; rw [chunkedHeaderSentUcLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
    chunkedInlBelow_skipField97 s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpIn.call_frame (x := ⟨iwt, tag, 97, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := entry + 552#64) hSkipCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [skipField3Spec]; simp only [arm64_norm, hsp, hx0, hx1, hx19, setWidth8_ofNat64_wt]; rfl)
    (⟨htag_lt, by decide, hrest_lt⟩ : tag < 2 ^ 32 ∧ 97 < 2 ^ 32 ∧ rest.length < 2 ^ 63) (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
  cases hsf : skipField (2 * rest.length + 2) 97 tag iwt rest with
  | none =>
    have hnone := hnone_of_sf hsf
    apply SepWPpIn.of_sepWP (mid := entry + 792#64)
    (conv => arg 4; simp only [skipField3Spec, hsf, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (chunkedInlBelow_skipField97_entails s0.sp) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (unchunked3CapAt_entails_chunkedHeaderSentPBAt A x.msgPtr rest.length uc sendingEk receivingCt1) (by sep_focus); wp_steps; wp_reach
    apply SepWPpIn.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedHeaderSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc, sendingEk := sendingEk, receivingCt1 := receivingCt1 } x.bs)
      (by dsimp only [chunkedHeaderSentErrFrame]; sep_entail)
    exact hpush_exit hnone (by decide : 0 ≤ 2) hsm0 hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm]) ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some rest' =>
    have hrest'_le : rest'.length ≤ rest.length := (skip_length _).1 _ _ _ _ _ hsf
    apply SepWPpIn.of_sepWP (mid := entry + 464#64)
    (conv => arg 4; simp only [skipField3Spec, hsf, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    apply SepWP.fold (chunkedInlBelow_skipField97_entails s0.sp) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (unchunked3CapAt_mono A x.msgPtr uc.epoch uc.auth uc.dk hrest'_le) (by sep_focus); wp_steps; wp_reach
    apply SepWPpIn.weaken_pre (P' := chunkedHeaderSentUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr uc sendingEk receivingCt1 x.bs rest')
      (by dsimp only [chunkedHeaderSentUcLoopPre]; sep_entail)
    exact hcont rest' _ hsf (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
      (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m]) (by simp only [arm64_norm, hx25_m]) (by simp only [arm64_norm, hx26_m])
      ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

private def vecU8CapAt (A : RustAlloc) (a : BitVec 64) (bsLen : Nat) (bs : List (BitVec 8)) : SepProp :=
  ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap bsLen⌝ ∗ vecU8At A a cap ptr bs

private theorem unchunked3CapAt_eq (A : RustAlloc) (a : BitVec 64) (bsLen : Nat) (epoch : BitVec 64) (auth : Option ProtoAuthenticator) (v3 : List (BitVec 8)) :
    unchunked3CapAt A a bsLen epoch auth v3 =
      vecU8CapAt A a bsLen v3 ∗ optAuthenticatorPBCapAt A (a + 0x18#64) bsLen auth ∗ ((a + 0x48#64) ↦₆₄ epoch) := rfl

private theorem unchunked3CapAt_eq_auth (A : RustAlloc) (a : BitVec 64) (bsLen : Nat) (epoch : BitVec 64) (auth : Option ProtoAuthenticator) (v3 : List (BitVec 8)) :
    unchunked3CapAt A a bsLen epoch auth v3 =
      optAuthenticatorPBCapAt A (a + 0x18#64) bsLen auth ∗ vecU8CapAt A a bsLen v3 ∗ ((a + 0x48#64) ↦₆₄ epoch) := by
  rw [unchunked3CapAt_eq]; ac_rfl

private theorem vecU8CapAt_mono' (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) {m n : Nat} (hle : m ≤ n) :
    vecU8CapAt A a n bs ⊢ vecU8CapAt A a m bs :=
  vecU8CapAt_mono A a bs hle

private theorem vecU8CapAt_entails_vecU8' (A : RustAlloc) (a : BitVec 64) (n : Nat) (bs : List (BitVec 8)) :
    vecU8CapAt A a n bs ⊢ rustBytesVecAt A a bs :=
  vecU8CapAt_entails_vecU8 A a n bs

private theorem vecU8At_entails_vecU8CapAt (A : RustAlloc) (a cap ptr : BitVec 64) (n : Nat) (bs : List (BitVec 8)) (hcap : BytesMergeCapOk cap n) :
    vecU8At A a cap ptr bs ⊢ vecU8CapAt A a n bs := by
  unfold vecU8CapAt
  refine Entails.trans (Entails.pure_right hcap (Entails.refl _)) ?_
  exact Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _))

/-- Step lemma for tag 1 (`epoch : u64`) in `Unchunked.EkSent` when `iwt = .varint` at `+0x25c` (`entry + 604#64`). -/
theorem chunkedHeaderSent_uc_tag1_varint_step {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName + 0xffffffffffffacf8#64) (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName + 0xffffffffffffd71c#64) (decodeVarint2Spec A))
    {x : ChunkedHeaderSentMergeGhost} {R : SepProp} {s0 s : State} {uc : V1State.Unchunked.EkSent} {sendingEk : Option PolynomialEncoder}
    {receivingCt1 : Option PolynomialDecoder} {rest : List (BitVec 8)} {outerLimit innerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest) (hnone_of_dv : decodeVarint rest = none →
      (Proto.mergeMessage V1State.Chunked.HeaderSent.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (v : BitVec 64) (rest' : List (BitVec 8)) (s' : State),
      decodeVarint rest = some (v, rest') → s'.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName + 464#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace → s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit → ChunkedInl10CalleeSaved s0 s' →
      SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s'
        (chunkedHeaderSentUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { uc with epoch := v } sendingEk receivingCt1 x.bs rest')
        (WppPost (chunkedHeaderSentMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName + 604#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = 0#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
      (chunkedHeaderSentUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr uc sendingEk receivingCt1 x.bs rest)
      (WppPost (chunkedHeaderSentMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hfpush := @chunkedHeaderSent_uc_field_push_exit img A H hPushCall x R s0 { uc := some uc, sendingEk := sendingEk, receivingCt1 := receivingCt1 }
  chunkedHeaderSentMerge_fetches img.base H 604 40; chunkedHeaderSentMerge_fetches img.base H 456 8; chunkedHeaderSentMerge_fetches img.base H 1040 32
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName = entry; examples_hide_fetches
  apply SepWPpIn.of_sepWP (mid := entry + 0xffffffffffffd71c#64)
  conv => arg 4; rw [chunkedHeaderSentUcLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
    chunkedInlBelow_decodeVarint2 s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpIn.call_frame (x := ⟨x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := entry + 616#64) hVarintCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, hsp, hx19]; rfl)
    hrest_lt (by sep_focus) (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
  cases hdv : decodeVarint rest with
  | none =>
    have hnone := hnone_of_dv hdv
    apply SepWPpIn.of_sepWP (mid := entry + 1072#64); (conv => arg 4; simp only [decodeVarint2Spec, hdv, memRegion_48_cells1_160 s0.sp,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp])
    apply SepWP.exists_elim; intro v_stk0; apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
    have hcbnz_err : (sm.readReg64 (Reg.gpr 1#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm1
    apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (unchunked3CapAt_entails_chunkedHeaderSentPBAt A x.msgPtr rest.length uc sendingEk receivingCt1) (by sep_focus); wp_steps; wp_reach
    apply SepWPpIn.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 1#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedHeaderSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc, sendingEk := sendingEk, receivingCt1 := receivingCt1 } x.bs)
      (by dsimp only [chunkedHeaderSentErrFrame]; sep_entail)
    exact hfpush hnone (by decide : 0 ≤ 1) hsm1 hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm, hspm]) ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨v, rest'⟩
    have hrest'_le : rest'.length ≤ rest.length := Nat.le_of_lt (decodeVarint_length hdv)
    apply SepWPpIn.of_sepWP (mid := entry + 464#64); (conv => arg 4; simp only [decodeVarint2Spec, hdv, unchunked3CapAt_eq, sepConj_assoc, arm64_norm, hsp])
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩; apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (vecU8CapAt_mono' A x.msgPtr uc.dk hrest'_le) (by sep_focus)
    apply SepWP.fold (optAuthenticatorPBCapAt_mono A (x.msgPtr + 0x18#64) uc.auth hrest'_le) (by sep_focus); wp_steps; wp_reach
    apply SepWPpIn.weaken_pre (P' := chunkedHeaderSentUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { uc with epoch := v } sendingEk receivingCt1 x.bs rest')
      (by dsimp only [chunkedHeaderSentUcLoopPre]; rw [unchunked3CapAt_eq]; sep_entail)
    exact hcont v rest' _ hdv (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
      (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m]) (by simp only [arm64_norm, hx25_m]) (by simp only [arm64_norm, hx26_m])
      ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

/-- Step lemma for tag 1 (`epoch : u64`) wire-type error (`iwt ≠ .varint`) at `+0x25c` (`entry + 604#64`). -/
theorem chunkedHeaderSent_uc_tag1_wt_err_step {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName + 0xffffffffffffaff0#64) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName + 0xffffffffffffacf8#64) (decodeErrorPushSpec A))
    {x : ChunkedHeaderSentMergeGhost} {R : SepProp} {s0 s : State} {uc : V1State.Unchunked.EkSent} {sendingEk : Option PolynomialEncoder}
    {receivingCt1 : Option PolynomialDecoder} {rest : List (BitVec 8)} {iwt : WireType}
    (hiwt : iwt ≠ .varint) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone : (Proto.mergeMessage V1State.Chunked.HeaderSent.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName + 604#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hcs : ChunkedInl10CalleeSaved s0 s) : SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
      (chunkedHeaderSentUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr uc sendingEk receivingCt1 x.bs rest)
      (WppPost (chunkedHeaderSentMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hcbnz_wt : (BitVec.ofNat 64 iwt.toNat == 0#64) = false := iwt_cbnz_true_of_ne_varint hiwt
  have hfpush := @chunkedHeaderSent_uc_field_push_exit img A H hPushCall x R s0 { uc := some uc, sendingEk := sendingEk, receivingCt1 := receivingCt1 }
  chunkedHeaderSentMerge_fetches img.base H 604 4; chunkedHeaderSentMerge_fetches img.base H 1008 64
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName = entry; examples_hide_fetches
  apply SepWPpIn.of_sepWP (mid := entry + 0xffffffffffffaff0#64)
  conv => arg 4; rw [chunkedHeaderSentUcLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
    sliceCursorAt, chunkedInlBelow_decodeErrorHook s0.sp, memRegion_48_wtErr160 s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro b_wt1; apply SepWP.exists_elim; intro b_wt0; apply SepWP.exists_elim; intro v_wt0; wp_steps
  apply SepWP.fold (wtErr160_entails_memRegion40 s0.sp _ _) (by sep_focus)
  apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
  apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
  apply SepWP.fold (unchunked3CapAt_entails_chunkedHeaderSentPBAt A x.msgPtr rest.length uc sendingEk receivingCt1) (by sep_focus); wp_reach
  refine SepWPpIn.call_frame (x := (s0.sp - 128#64, 0x8000000000000006#64))
    (ret_pc := entry + 1036#64) hFromCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorFromSpec]; simp only [arm64_norm, hsp]; rfl) (by decide : KindNoHeap 0x8000000000000006#64) (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, _, _, _, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx27, hx28, hvregs] at hpcm hspm hx27_m hx28_m hvregs_m
  apply SepWPpIn.of_sepWP (mid := entry + 1072#64)
  (conv => arg 4; simp only [decodeErrorFromSpec, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨hsm0, htrm⟩
  apply SepWP.fold (chunkedInlBelow_decodeErrorHook_entails s0.sp) (by sep_focus); apply SepWP.fold (memRegion8_memRegion40_entails_48_160 s0.sp) (by sep_focus)
  conv => arg 4; rw [memRegion_48_cells1_160 s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v_stk0; wp_steps; wp_reach
  apply SepWPpIn.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedHeaderSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc, sendingEk := sendingEk, receivingCt1 := receivingCt1 } x.bs)
    (by dsimp only [chunkedHeaderSentErrFrame]; sep_entail)
  exact hfpush hnone (by decide : 0 ≤ 1) hsm0 hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
    (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm, hspm]) ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

private theorem chunkedHeaderSent_uc_auth_init {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    {x : ChunkedHeaderSentMergeGhost} {R : SepProp} {s0 s : State} {uc : V1State.Unchunked.EkSent} {sendingEk : Option PolynomialEncoder}
    {receivingCt1 : Option PolynomialDecoder} {rest : List (BitVec 8)} (hcont : ∀ (s' : State),
      s'.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName + 584#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s.trace → s'.readReg64 (Reg.gpr 0#5) = s.readReg64 (Reg.gpr 0#5) →
      s'.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) → s'.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) →
      s'.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) → s'.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) → ChunkedInl10CalleeSaved s0 s' →
      SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s' (vecU8CapAt A x.msgPtr rest.length uc.dk ∗
          authenticatorPBCapAt A (x.msgPtr + 0x18#64) rest.length (uc.auth.getD default) ∗ ((x.msgPtr + 0x48#64) ↦₆₄ uc.epoch) ∗
          optPolynomialEncoderPBAt A (x.msgPtr + 80#64) sendingEk ∗
          optPolynomialDecoderPBAt A (x.msgPtr + 136#64) receivingCt1 ∗
          stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
          memRegion (s0.sp - 128#64) 48 ∗ chunkedInlSavedRegs10 s0.sp s0 ∗ (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool)
        (WppPost (chunkedHeaderSentMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName + 560#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr) (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) : SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
      (chunkedHeaderSentUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr uc sendingEk receivingCt1 x.bs rest)
      (WppPost (chunkedHeaderSentMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; chunkedHeaderSentMerge_fetches img.base H 560 24
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName = entry; examples_hide_fetches
  rcases hauth : uc.auth with _ | auth
  · rw [hauth] at hcont; dsimp only [Option.getD] at hcont
    apply SepWPpIn.of_sepWP (mid := entry + 584#64)
    conv => arg 4; rw [chunkedHeaderSentUcLoopPre, unchunked3CapAt_eq_auth, hauth, optAuthenticatorPBCapAt, memRegion_40_cells (x.msgPtr + 0x18#64)]
    simp only [noneCap, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm]
    apply SepWP.exists_elim; intro w1; apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
    apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5; wp_steps
    have hdef := default_cells_entails_authenticatorPBCapAt A (x.msgPtr + 0x18#64) rest.length
    simp only [arm64_norm] at hdef
    apply SepWP.fold hdef (by sep_focus); wp_reach
    apply SepWPpIn.weaken_pre (P' := vecU8CapAt A x.msgPtr rest.length uc.dk ∗ authenticatorPBCapAt A (x.msgPtr + 0x18#64) rest.length default ∗ ((x.msgPtr + 0x48#64) ↦₆₄ uc.epoch) ∗ optPolynomialEncoderPBAt A (x.msgPtr + 80#64) sendingEk ∗ optPolynomialDecoderPBAt A (x.msgPtr + 136#64) receivingCt1 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedInlSavedRegs10 s0.sp s0 ∗ (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool)
      (by sep_entail)
    exact hcont _ (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm, hrun]) (by simp (config := { failIfUnchanged := false }) only [arm64_norm, hsp])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm]) (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm]) (by simp (config := { failIfUnchanged := false }) only [arm64_norm, hx20])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm]) (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm, hx23]) (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm]) (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
      ⟨by simp (config := { failIfUnchanged := false }) only [arm64_norm, hx27],
       by simp (config := { failIfUnchanged := false }) only [arm64_norm, hx28],
       by simp (config := { failIfUnchanged := false }) only [arm64_norm, hvregs]⟩
  · rw [hauth] at hcont; dsimp only [Option.getD] at hcont
    let macCap : SepProp := ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap rest.length⌝ ∗ vecU8At A (x.msgPtr + 0x18#64 + 0x18#64) cap ptr auth.macKey
    have hcmn_in : authenticatorPBCapAt A (x.msgPtr + 0x18#64) rest.length auth ⊢
        ∃∗ cap_ik : BitVec 64, ∃∗ ptr_ik : BitVec 64,
          ⌜cap_ik.toNat < 2 ^ 63 ∧ BytesMergeCapOk cap_ik rest.length⌝ ∗ ((x.msgPtr + 24#64) ↦₆₄ cap_ik) ∗ ((x.msgPtr + 32#64) ↦₆₄ ptr_ik) ∗
          ((x.msgPtr + 40#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
          vecU8Buf A cap_ik ptr_ik auth.rootKey ∗ macCap := by
      have hlt_buf : ∀ (cap ptr : BitVec 64) (bs : List (BitVec 8)),
          vecU8Buf A cap ptr bs ⊢ ⌜cap.toNat < 2 ^ 63⌝ ∗ vecU8Buf A cap ptr bs := by
        intro cap ptr bs; unfold vecU8Buf
        refine Entails.pure_left fun h => Entails.pure_right h.2.1 (Entails.pure_right h (Entails.refl _))
      have hlt_at : ∀ (a cap ptr : BitVec 64) (bs : List (BitVec 8)),
          vecU8At A a cap ptr bs ⊢ ⌜cap.toNat < 2 ^ 63⌝ ∗ (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗
            ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ vecU8Buf A cap ptr bs := by
        intro a cap ptr bs; rw [vecU8At_eq_header_sep_buf, vecHeader]
        exact Entails.trans (sepConj_mono_right (hlt_buf cap ptr bs)) (by sep_entail)
      change (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap rest.length⌝ ∗ vecU8At A (x.msgPtr + 0x18#64) cap ptr auth.rootKey) ∗ macCap ⊢ _
      rw [sepExists_sepConj_left]; refine ProofLib.Entails.sepExists_elim fun cap_ik => ?_
      rw [sepExists_sepConj_left]; refine ProofLib.Entails.sepExists_elim fun ptr_ik => ?_
      refine Entails.trans ?_ (Entails.sepExists_intro cap_ik); refine Entails.trans ?_ (Entails.sepExists_intro ptr_ik)
      rw [sepConj_assoc]; refine Entails.pure_left fun hcap => ?_
      refine Entails.trans (sepConj_mono_left (hlt_at (x.msgPtr + 0x18#64) cap_ik ptr_ik auth.rootKey)) ?_
      simp only [sepConj_assoc, bv64_add24_add8, bv64_add24_add16]
      exact Entails.pure_left fun hlt => Entails.pure_right ⟨hlt, hcap⟩ (Entails.refl _)
    apply SepWPpIn.of_sepWP (mid := entry + 584#64)
    conv => arg 4; rw [chunkedHeaderSentUcLoopPre, unchunked3CapAt_eq_auth, hauth, optAuthenticatorPBCapAt]
    simp only [sepConj_assoc]
    apply SepWP.fold hcmn_in (by sep_focus)
    wp_simp_pre [sepExists_sepConj_left, sepConj_assoc]
    apply SepWP.exists_elim; intro cap_ik; apply SepWP.exists_elim; intro ptr_ik; apply SepWP.pure_elim; rintro ⟨hcap_lt, hcap_ik⟩
    have hcmn1 := cap_add_one_beq_zero_false hcap_lt; have hcmn2 := cap_add_one_bne_zero_true hcap_lt; wp_steps
    have hcmn_out : ((x.msgPtr + 24#64) ↦₆₄ cap_ik) ∗ ((x.msgPtr + 32#64) ↦₆₄ ptr_ik) ∗ ((x.msgPtr + 40#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
          vecU8Buf A cap_ik ptr_ik auth.rootKey ∗ macCap ⊢
          authenticatorPBCapAt A (x.msgPtr + 0x18#64) rest.length auth := by
      change ((x.msgPtr + 24#64) ↦₆₄ cap_ik) ∗ ((x.msgPtr + 32#64) ↦₆₄ ptr_ik) ∗ ((x.msgPtr + 40#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
          vecU8Buf A cap_ik ptr_ik auth.rootKey ∗ macCap ⊢
          (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap rest.length⌝ ∗ vecU8At A (x.msgPtr + 0x18#64) cap ptr auth.rootKey) ∗ macCap
      refine Entails.trans (Entails.of_eq (show _ = (((x.msgPtr + 24#64) ↦₆₄ cap_ik) ∗ ((x.msgPtr + 32#64) ↦₆₄ ptr_ik) ∗ ((x.msgPtr + 40#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗ vecU8Buf A cap_ik ptr_ik auth.rootKey) ∗ macCap by ac_rfl)) ?_
      refine sepConj_mono_left ?_
      have hhdr : ((x.msgPtr + 24#64) ↦₆₄ cap_ik) ∗ ((x.msgPtr + 32#64) ↦₆₄ ptr_ik) ∗
          ((x.msgPtr + 40#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗ vecU8Buf A cap_ik ptr_ik auth.rootKey ⊢
          vecU8At A (x.msgPtr + 0x18#64) cap_ik ptr_ik auth.rootKey := by
        rw [vecU8At_eq_header_sep_buf, vecHeader]; simp only [bv64_add24_add8, bv64_add24_add16]; sep_entail
      refine Entails.trans hhdr ?_
      refine Entails.trans ?_ (Entails.sepExists_intro cap_ik); refine Entails.trans ?_ (Entails.sepExists_intro ptr_ik)
      exact Entails.pure_right hcap_ik (Entails.refl _)
    apply SepWP.fold hcmn_out (by sep_focus); wp_reach
    apply SepWPpIn.weaken_pre (P' := vecU8CapAt A x.msgPtr rest.length uc.dk ∗ authenticatorPBCapAt A (x.msgPtr + 0x18#64) rest.length auth ∗ ((x.msgPtr + 0x48#64) ↦₆₄ uc.epoch) ∗ optPolynomialEncoderPBAt A (x.msgPtr + 80#64) sendingEk ∗ optPolynomialDecoderPBAt A (x.msgPtr + 136#64) receivingCt1 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedInlSavedRegs10 s0.sp s0 ∗ (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool)
      (by sep_entail)
    exact hcont _ (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm, hrun]) (by simp (config := { failIfUnchanged := false }) only [arm64_norm, hsp])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm]) (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm]) (by simp (config := { failIfUnchanged := false }) only [arm64_norm, hx20])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm]) (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm, hx23]) (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm]) (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
      ⟨by simp (config := { failIfUnchanged := false }) only [arm64_norm, hx27],
       by simp (config := { failIfUnchanged := false }) only [arm64_norm, hx28],
       by simp (config := { failIfUnchanged := false }) only [arm64_norm, hvregs]⟩

/-- Step lemma for tag 2 (`auth : Option<Authenticator>`) in `Unchunked.EkSent` at `+0x230` (`entry + 560#64`). -/
theorem chunkedHeaderSent_uc_tag2_step {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName + 0xffffffffffffacf8#64) (decodeErrorPushSpec A))
    (hAuthCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName + 0xffffffffffffe188#64) ((authMergeSpec A).inImage img))
    {x : ChunkedHeaderSentMergeGhost} {R : SepProp} {s0 s : State} {uc : V1State.Unchunked.EkSent} {sendingEk : Option PolynomialEncoder}
    {receivingCt1 : Option PolynomialDecoder} {rest : List (BitVec 8)} {iwt : WireType} {outerLimit innerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length) (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_auth : (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto iwt) (uc.auth.getD default) rest 97).toOption = none →
      (Proto.mergeMessage V1State.Chunked.HeaderSent.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (auth' : ProtoAuthenticator) (rest' : List (BitVec 8)) (s' : State),
      (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto iwt) (uc.auth.getD default) rest 97).toOption = some (auth', rest') →
      s'.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName + 464#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace → s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit → ChunkedInl10CalleeSaved s0 s' →
      SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s'
        (chunkedHeaderSentUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { uc with auth := some auth' } sendingEk receivingCt1 x.bs rest')
        (WppPost (chunkedHeaderSentMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName + 560#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
      (chunkedHeaderSentUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr uc sendingEk receivingCt1 x.bs rest)
      (WppPost (chunkedHeaderSentMergeSpec A) x R s0) (WppPanic R s0) := by
  refine chunkedHeaderSent_uc_auth_init ?_ hpc hrun hsp hx20 hx23 hcs
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hcs1
  rw [htr] at htr1; rw [hx0] at hx0_1; rw [hx19] at hx19_1; rw [hx21] at hx21_1
  rw [hx22] at hx22_1; rw [hx24] at hx24_1; rw [hx25] at hx25_1; rw [hx26] at hx26_1
  obtain ⟨hx27_1, hx28_1, hvregs_1⟩ := hcs1
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hfpush := fun (auth' : ProtoAuthenticator) =>
    @chunkedHeaderSent_uc_field_push_exit img A H hPushCall x R s0 { uc := some { uc with auth := some auth' }, sendingEk := sendingEk, receivingCt1 := receivingCt1 }
  chunkedHeaderSentMerge_fetches img.base H 584 20; chunkedHeaderSentMerge_fetches img.base H 456 8; chunkedHeaderSentMerge_fetches img.base H 936 36
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName = entry; examples_hide_fetches
  apply SepWPpIn.of_sepWP (mid := entry + 0xffffffffffffe188#64)
  conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, chunkedInlBelow_authMerge s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpIn.call_frame_inImage (x := ⟨iwt, x.msgPtr + 0x18#64, uc.auth.getD default, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := entry + 596#64) hAuthCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
    (by simp only [State.spAligned, hsp1, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [authMergeSpec]; simp only [arm64_norm, hsp1, hx0_1, hx20_1, hx19_1, setWidth8_ofNat64_wt]; rfl)
    hrest_lt (by sep_focus) (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [authMergeSpec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr1]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
  cases hauth_res : (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto iwt) (uc.auth.getD default) rest 97).toOption with
  | none =>
    have hnone := hnone_of_auth hauth_res
    apply SepWPpIn.of_sepWP (mid := entry + 1072#64); (conv => arg 4; simp only [authMergeSpec, hauth_res, memRegion_48_cells1_160 s0.sp,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp1])
    apply SepWP.exists_elim; intro v_stk0; apply SepWP.exists_elim; intro auth'; apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hn_err⟩
    have hcbz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (chunkedInlBelow_authMerge_entails s0.sp) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (vecU8CapAt_entails_vecU8' A x.msgPtr rest.length uc.dk) (by sep_focus); wp_steps; wp_reach
    apply SepWPpIn.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedHeaderSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some { uc with auth := some auth' }, sendingEk := sendingEk, receivingCt1 := receivingCt1 } x.bs)
      (by dsimp only [chunkedHeaderSentErrFrame, chunkedHeaderSentPBAt, optEkSentPBAt, ekSentPBAt, unchunked3At, optAuthenticatorPBAt]; sep_entail)
    exact hfpush auth' hnone hn_err hsm0 hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr1]) (by simp only [arm64_norm, hspm]) ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨auth', rest'⟩
    have hrest'_le : rest'.length ≤ rest.length := (proto_mergeMessage_suffix hauth_res).1
    apply SepWPpIn.of_sepWP (mid := entry + 464#64); (conv => arg 4; simp only [authMergeSpec, hauth_res, sepConj_assoc, arm64_norm, hsp1])
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩; apply SepWP.fold (chunkedInlBelow_authMerge_entails s0.sp) (by sep_focus)
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (vecU8CapAt_mono' A x.msgPtr uc.dk hrest'_le) (by sep_focus); wp_steps; wp_reach
    apply SepWPpIn.weaken_pre (P' := chunkedHeaderSentUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { uc with auth := some auth' } sendingEk receivingCt1 x.bs rest')
      (by dsimp only [chunkedHeaderSentUcLoopPre]; rw [unchunked3CapAt_eq]; dsimp only [optAuthenticatorPBCapAt]; sep_entail)
    exact hcont auth' rest' _ hauth_res
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr1])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
      (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m]) (by simp only [arm64_norm, hx25_m]) (by simp only [arm64_norm, hx26_m])
      ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

/-- Step lemma for tag 3 (`dk : Vec<u8>` at `x.msgPtr`) in `Unchunked.EkSent` at `+0x1b8` (`entry + 440#64`). -/
theorem chunkedHeaderSent_uc_tag3_step {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName + 0xffffffffffffacf8#64) (decodeErrorPushSpec A))
    (hBytesCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName + 0xffffffffffffd38c#64) ((bytesMerge3RawSpec A).inImage img))
    {x : ChunkedHeaderSentMergeGhost} {R : SepProp} {s0 s : State} {uc : V1State.Unchunked.EkSent} {sendingEk : Option PolynomialEncoder}
    {receivingCt1 : Option PolynomialDecoder} {rest : List (BitVec 8)} {iwt : WireType} {outerLimit innerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest) (hnone_of_mb : mergeBytes iwt rest = none →
      (Proto.mergeMessage V1State.Chunked.HeaderSent.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (v rest' : List (BitVec 8)) (s' : State),
      mergeBytes iwt rest = some (v, rest') → s'.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName + 464#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace → s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit → ChunkedInl10CalleeSaved s0 s' →
      SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s'
        (chunkedHeaderSentUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { uc with dk := v } sendingEk receivingCt1 x.bs rest')
        (WppPost (chunkedHeaderSentMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName + 440#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
      (chunkedHeaderSentUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr uc sendingEk receivingCt1 x.bs rest)
      (WppPost (chunkedHeaderSentMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hfpush := @chunkedHeaderSent_uc_field_push_exit img A H hPushCall x R s0 { uc := some uc, sendingEk := sendingEk, receivingCt1 := receivingCt1 }
  chunkedHeaderSentMerge_fetches img.base H 440 24; chunkedHeaderSentMerge_fetches img.base H 972 36
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName = entry; examples_hide_fetches
  apply SepWPpIn.of_sepWP (mid := entry + 0xffffffffffffd38c#64)
  conv => arg 4; rw [chunkedHeaderSentUcLoopPre, unchunked3CapAt_eq, vecU8CapAt,
    sliceCursorAfter_eq_split hrest_le hrest_suf, chunkedInlBelow_bytesMerge3 s0.sp]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWP.exists_elim; intro cap1; apply SepWP.exists_elim; intro ptr1; apply SepWP.pure_elim; intro hcap1; wp_steps; wp_reach
  refine SepWPpIn.call_frame_inImage (x := ⟨iwt, x.msgPtr, cap1, ptr1, uc.dk, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := entry + 452#64) hBytesCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [bytesMerge3RawSpec]; simp only [arm64_norm, hsp, hx0, hx19, hx20, setWidth8_ofNat64_wt]; rfl)
    (⟨hrest_lt, hcap1⟩ : rest.length < 2 ^ 63 ∧ BytesMergeCapOk cap1 rest.length) (by sep_focus) (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [bytesMerge3RawSpec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
  cases hmb : mergeBytes iwt rest with
  | none =>
    have hnone := hnone_of_mb hmb
    apply SepWPpIn.of_sepWP (mid := entry + 1072#64); (conv => arg 4; simp only [bytesMerge3RawSpec, hmb, memRegion_48_cells1_160 s0.sp,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp])
    apply SepWP.exists_elim; intro v_stk0; apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (chunkedInlBelow_bytesMerge3_entails s0.sp) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (vecU8At_entails_rustBytesVecAt A x.msgPtr cap1 ptr1 uc.dk) (by sep_focus)
    apply SepWP.fold (optAuthenticatorPBCapAt_entails_optAuthenticatorPBAt A (x.msgPtr + 0x18#64) rest.length uc.auth) (by sep_focus); wp_steps; wp_reach
    apply SepWPpIn.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedHeaderSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc, sendingEk := sendingEk, receivingCt1 := receivingCt1 } x.bs)
      (by dsimp only [chunkedHeaderSentErrFrame, chunkedHeaderSentPBAt, optEkSentPBAt, ekSentPBAt, unchunked3At]; sep_entail)
    exact hfpush hnone (by decide : 0 ≤ 1) hsm0 hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm, hspm]) ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨v, rest'⟩
    have hrest'_le : rest'.length ≤ rest.length := mergeBytes_length hmb
    apply SepWPpIn.of_sepWP (mid := entry + 464#64); (conv => arg 4; simp only [bytesMerge3RawSpec, hmb, sepExists_sepConj_left, sepExists_sepConj_right,
      sepConj_assoc, arm64_norm, hsp])
    apply SepWP.exists_elim; intro cap1'; apply SepWP.exists_elim; intro ptr1'; apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hcap1'⟩
    apply SepWP.fold (chunkedInlBelow_bytesMerge3_entails s0.sp) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (vecU8At_entails_vecU8CapAt A x.msgPtr cap1' ptr1' rest'.length v hcap1') (by sep_focus)
    apply SepWP.fold (optAuthenticatorPBCapAt_mono A (x.msgPtr + 0x18#64) uc.auth hrest'_le) (by sep_focus); wp_steps; wp_reach
    apply SepWPpIn.weaken_pre (P' := chunkedHeaderSentUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { uc with dk := v } sendingEk receivingCt1 x.bs rest')
      (by dsimp only [chunkedHeaderSentUcLoopPre]; rw [unchunked3CapAt_eq]; sep_entail)
    exact hcont v rest' _ hmb (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
      (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m]) (by simp only [arm64_norm, hx25_m]) (by simp only [arm64_norm, hx26_m])
      ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

/-! ## 4. Inner Loop Exit, Key Decode, and Induction (`chunkedHeaderSent_uc_loop_ok`) -/

/-- Inner loop exit at `+0x1d0` (`entry + 464#64`) when `cur.length ≤ innerLimit`. -/
theorem chunkedHeaderSent_uc_loop_le_exit {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName + 0xffffffffffffaff0#64) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName + 0xffffffffffffacf8#64) (decodeErrorPushSpec A))
    {x : ChunkedHeaderSentMergeGhost} {R : SepProp} {s0 s : State} {uc : V1State.Unchunked.EkSent} {sendingEk : Option PolynomialEncoder}
    {receivingCt1 : Option PolynomialDecoder} {cur : List (BitVec 8)} {outerLimit innerLimit : Nat}
    (hle_lim : cur.length ≤ innerLimit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_suf : IsDropSuffix x.bs cur) (hlim_lt : innerLimit < 2 ^ 63) (hnone_of_lt : cur.length < innerLimit →
      (Proto.mergeMessage V1State.Chunked.HeaderSent.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none) (hcont_eq : ∀ s' : State,
      cur.length = innerLimit → s'.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName + 168#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace → s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 25#5) = 8#64 → ChunkedInl10CalleeSaved s0 s' →
      SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s' (chunkedHeaderSentLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr
          { uc := some uc, sendingEk := sendingEk, receivingCt1 := receivingCt1 } x.bs cur) (WppPost (chunkedHeaderSentMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName + 464#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
      (chunkedHeaderSentUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr uc sendingEk receivingCt1 x.bs cur)
      (WppPost (chunkedHeaderSentMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  have hfrom_push := @chunkedHeaderSent_uc_from_push_exit img A H hFromCall hPushCall x R s0 { uc := some uc, sendingEk := sendingEk, receivingCt1 := receivingCt1 }
  chunkedHeaderSentMerge_fetches img.base H 464 12; chunkedHeaderSentMerge_fetches img.base H 644 12
  chunkedHeaderSentMerge_fetches img.base H 1092 16; chunkedHeaderSentMerge_fetches img.base H 776 4
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName = entry; examples_hide_fetches
  by_cases heq_lim : cur.length = innerLimit
  · obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq heq_lim
    apply SepWPpIn.of_sepWP (mid := entry + 168#64)
    conv => arg 4; rw [chunkedHeaderSentUcLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt]
    simp only [sepConj_assoc]
    wp_steps; apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus); wp_reach
    apply SepWPpIn.weaken_pre (P' := chunkedHeaderSentLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc, sendingEk := sendingEk, receivingCt1 := receivingCt1 } x.bs cur)
      (by dsimp only [chunkedHeaderSentLoopPre, chunkedHeaderSentPBCapAt, optEkSentPBCapAt, sliceCursorAfter]; sep_entail)
    exact hcont_eq _ heq_lim (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr])
      (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20]) (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22])
      (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24]) (by simp only [arm64_norm, hx25])
      ⟨by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩
  · have hlt_lim : cur.length < innerLimit := Nat.lt_of_le_of_ne hle_lim heq_lim
    obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_lt hlt_lim hlim_lt
    have hnone := hnone_of_lt hlt_lim
    apply SepWPpIn.of_sepWP (mid := entry + 780#64)
    conv => arg 4; rw [chunkedHeaderSentUcLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
      sliceCursorAt, memRegion_48_cells1_160 s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v_stk0; wp_steps; apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot curPtr (BitVec.ofNat 64 cur.length)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    apply SepWP.fold (unchunked3CapAt_entails_chunkedHeaderSentPBAt A x.msgPtr cur.length uc sendingEk receivingCt1) (by sep_focus); wp_reach
    apply SepWPpIn.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000008#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedHeaderSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc, sendingEk := sendingEk, receivingCt1 := receivingCt1 } x.bs)
      (by dsimp only [chunkedHeaderSentErrFrame]; sep_entail)
    exact hfrom_push hnone (by decide : KindNoHeap 0x8000000000000008#64) hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr])
      ⟨by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩

/-- Inner loop key-decode step at `+0x1d0` (`entry + 464#64`) when `¬ cur.length ≤ innerLimit`. -/
theorem chunkedHeaderSent_uc_decode_key_step {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName + 0xffffffffffffaff0#64) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName + 0xffffffffffffacf8#64) (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName + 0xffffffffffffd71c#64) (decodeVarint2Spec A))
    {x : ChunkedHeaderSentMergeGhost} {R : SepProp} {s0 s : State} {uc : V1State.Unchunked.EkSent} {sendingEk : Option PolynomialEncoder}
    {receivingCt1 : Option PolynomialDecoder} {cur : List (BitVec 8)} {outerLimit innerLimit : Nat}
    (hgt_lim : ¬ cur.length ≤ innerLimit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_lt : cur.length < 2 ^ 63) (hcur_suf : IsDropSuffix x.bs cur) (hnone_of_loop_none :
      mergeLoopBin V1State.Unchunked.EkSent.mergeField (cur.length - innerLimit) uc cur innerLimit 97 = none →
      (Proto.mergeMessage V1State.Chunked.HeaderSent.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (key : BitVec 64) (iwt : WireType) (rest : List (BitVec 8)) (s' : State),
      decodeVarint cur = some (key, rest) → ¬ 2 ^ 32 ≤ key.toNat →
      WireType.ofNat? (key.toNat % 8) = some iwt → ¬ key.toNat / 8 < 1 →
      s'.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName + 516#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace → s'.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) → s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit → ChunkedInl10CalleeSaved s0 s' →
      SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s'
        (chunkedHeaderSentUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr uc sendingEk receivingCt1 x.bs rest)
        (WppPost (chunkedHeaderSentMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName + 464#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
      (chunkedHeaderSentUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr uc sendingEk receivingCt1 x.bs cur)
      (WppPost (chunkedHeaderSentMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  have hpush_exit := @chunkedHeaderSent_uc_push_exit img A H hPushCall x R s0 { uc := some uc, sendingEk := sendingEk, receivingCt1 := receivingCt1 }
  have hfrom_push := @chunkedHeaderSent_uc_from_push_exit img A H hFromCall hPushCall x R s0 { uc := some uc, sendingEk := sendingEk, receivingCt1 := receivingCt1 }
  chunkedHeaderSentMerge_fetches img.base H 464 52; chunkedHeaderSentMerge_fetches img.base H 732 20
  chunkedHeaderSentMerge_fetches img.base H 752 12; chunkedHeaderSentMerge_fetches img.base H 764 16
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName = entry; examples_hide_fetches
  apply SepWPpIn.of_sepWP (mid := entry + 0xffffffffffffd71c#64)
  conv => arg 4; rw [chunkedHeaderSentUcLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
    sliceCursorAt, chunkedInlBelow_decodeVarint2 s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpIn.call_frame (x := ⟨x.bufRef, x.slot, curPtr, cur⟩)
    (ret_pc := entry + 484#64) hVarintCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, hsp, hx19]; rfl)
    hcur_lt (by dsimp only [sliceCursorAt, curPtr]; sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
  cases hd : decodeVarint cur with
  | none =>
    have hnone := hnone_of_loop_none (mergeLoopBin_of_decodeVarint_none protoPrefixStep_unchunked_ekSent_mergeField hgt_lim hd)
    apply SepWPpIn.of_sepWP (mid := entry + 792#64)
    (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
    apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    apply SepWP.fold (unchunked3CapAt_entails_chunkedHeaderSentPBAt A x.msgPtr cur.length uc sendingEk receivingCt1) (by sep_focus); wp_steps; wp_reach
    apply SepWPpIn.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedHeaderSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc, sendingEk := sendingEk, receivingCt1 := receivingCt1 } x.bs)
      (by dsimp only [chunkedHeaderSentErrFrame]; sep_entail)
    exact hpush_exit hnone (by decide : 0 ≤ 2) hsm1 hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm]) ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨key, rest⟩
    have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd; have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
    have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le; have hrest_suf : IsDropSuffix x.bs rest := suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
    let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
    by_cases hk_ge : 2 ^ 32 ≤ key.toNat
    · have hnone := hnone_of_loop_none (mergeLoopBin_of_key_ge protoPrefixStep_unchunked_ekSent_mergeField hgt_lim hd hk_ge)
      have hshr := key_shr32_of_ge hk_ge; apply SepWPpIn.of_sepWP (mid := entry + 780#64)
      (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
      apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
      apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
      apply SepWP.fold (unchunked3CapAt_entails_chunkedHeaderSentPBAt A x.msgPtr cur.length uc sendingEk receivingCt1) (by sep_focus)
      conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_cells2_160 s0.sp]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply SepWP.exists_elim; intro v_err0; apply SepWP.exists_elim; intro v_err1; wp_steps
      apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
      apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
      have h40 : ((s0.sp - 128#64 + 8#64) ↦₆₄ key) ∗ memRegion (s0.sp - 112#64) 32 ⊢ memRegion (s0.sp - 120#64) 40 := by
        rw [bv_sub_add_lit s0.sp 128 8]; exact cells2_memRegion32_entails_40_160 s0.sp key
      apply SepWP.fold h40 (by sep_focus); wp_reach
      apply SepWPpIn.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000004#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedHeaderSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc, sendingEk := sendingEk, receivingCt1 := receivingCt1 } x.bs)
        (by dsimp only [chunkedHeaderSentErrFrame]; sep_entail)
      exact hfrom_push hnone (by decide : KindNoHeap 0x8000000000000004#64) hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
        ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
    · have hshr := key_shr32_of_lt hk_ge
      cases hwt : WireType.ofNat? (key.toNat % 8) with
      | none =>
        have hnone := hnone_of_loop_none (mergeLoopBin_of_wt_none protoPrefixStep_unchunked_ekSent_mergeField hgt_lim hd hk_ge hwt)
        obtain ⟨hcs1, hcs2⟩ := key_wt_none hwt
        apply SepWPpIn.of_sepWP (mid := entry + 780#64); (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
        apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
        apply SepWP.fold (unchunked3CapAt_entails_chunkedHeaderSentPBAt A x.msgPtr cur.length uc sendingEk receivingCt1) (by sep_focus)
        conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_cells2_160 s0.sp]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]; apply SepWP.exists_elim; intro v_err0; apply SepWP.exists_elim; intro v_err1; wp_steps
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        have h40 : ((s0.sp - 128#64 + 8#64) ↦₆₄ (key &&& 7#64)) ∗ memRegion (s0.sp - 112#64) 32 ⊢ memRegion (s0.sp - 120#64) 40 := by
          rw [bv_sub_add_lit s0.sp 128 8]; exact cells2_memRegion32_entails_40_160 s0.sp (key &&& 7#64)
        apply SepWP.fold h40 (by sep_focus); wp_reach
        apply SepWPpIn.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000003#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedHeaderSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc, sendingEk := sendingEk, receivingCt1 := receivingCt1 } x.bs)
          (by dsimp only [chunkedHeaderSentErrFrame]; sep_entail)
        exact hfrom_push hnone (by decide : KindNoHeap 0x8000000000000003#64) hsp_align
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
          ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
      | some iwt =>
        obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt; obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_ge
        obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
        by_cases hitag0 : key.toNat / 8 < 1
        · have hnone := hnone_of_loop_none (mergeLoopBin_of_tag_zero protoPrefixStep_unchunked_ekSent_mergeField hgt_lim hd hk_ge hwt hitag0)
          have htag_zero : key.toNat / 8 = 0 := by omega
          apply SepWPpIn.of_sepWP (mid := entry + 780#64); (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
          apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩; apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          apply SepWP.fold (unchunked3CapAt_entails_chunkedHeaderSentPBAt A x.msgPtr cur.length uc sendingEk receivingCt1) (by sep_focus)
          conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_cells1_160 s0.sp]
          simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]; apply SepWP.exists_elim; intro v_err0; wp_steps
          apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
          apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus); wp_reach
          apply SepWPpIn.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000005#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedHeaderSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc, sendingEk := sendingEk, receivingCt1 := receivingCt1 } x.bs)
            (by dsimp only [chunkedHeaderSentErrFrame]; sep_entail)
          exact hfrom_push hnone (by decide : KindNoHeap 0x8000000000000005#64) hsp_align
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
            ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
        · obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_ge hitag0
          have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
            rw [beq_eq_false_iff_ne]; intro h; have h1 := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1; omega
          apply SepWPpIn.of_sepWP (mid := entry + 516#64); (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
          apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          apply SepWP.fold (unchunked3CapAt_mono A x.msgPtr uc.epoch uc.auth uc.dk hrest_le_cur) (by sep_focus); wp_steps; wp_reach
          apply SepWPpIn.weaken_pre (P' := chunkedHeaderSentUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr uc sendingEk receivingCt1 x.bs rest)
            (by dsimp only [chunkedHeaderSentUcLoopPre]; sep_entail)
          exact hcont key iwt rest _ hd hk_ge hwt hitag0
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
            (by simp only [arm64_norm, hsm1, hand_wt]) (by simp only [arm64_norm, hsm1, hw1, hw1_2, hw1_zext1, hw1_zext2])
            (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
            (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m]) (by simp only [arm64_norm, hx25_m]) (by simp only [arm64_norm, hx26_m])
            ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

/-- Inner loop induction at `+0x1d0` (`entry + 464#64`) for `V1State.Unchunked.EkSent.mergeField`. -/
theorem chunkedHeaderSent_uc_loop_ok {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName + 0xffffffffffffaff0#64) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName + 0xffffffffffffacf8#64) (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName + 0xffffffffffffd71c#64) (decodeVarint2Spec A))
    (hSkipCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName + 0xffffffffffffbdc4#64) (skipField3Spec A))
    (hBytesCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName + 0xffffffffffffd38c#64) ((bytesMerge3RawSpec A).inImage img))
    (hAuthCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName + 0xffffffffffffe188#64) ((authMergeSpec A).inImage img))
    {x : ChunkedHeaderSentMergeGhost} {R : SepProp} {s0 : State} (sendingEk : Option PolynomialEncoder) (receivingCt1 : Option PolynomialDecoder)
    (outerLimit innerLimit : Nat) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hbs_lt : x.bs.length < 2 ^ 63) (hlim_lt : innerLimit < 2 ^ 63) :
    ∀ (n : Nat) (uc : V1State.Unchunked.EkSent) (cur : List (BitVec 8)) (s : State),
      cur.length ≤ n → cur.length ≤ x.bs.length → IsDropSuffix x.bs cur → (∀ (uc' : V1State.Unchunked.EkSent) (rest' : List (BitVec 8)) (s' : State),
        rest'.length = innerLimit → rest'.length ≤ x.bs.length → IsDropSuffix x.bs rest' →
        mergeLoopBin V1State.Unchunked.EkSent.mergeField (cur.length - innerLimit) uc cur innerLimit 97 = some uc' →
        s'.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName + 168#64 →
        s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace → s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
        s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
        s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 25#5) = 8#64 →
        ChunkedInl10CalleeSaved s0 s' → SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s'
          (chunkedHeaderSentLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc', sendingEk := sendingEk, receivingCt1 := receivingCt1 } x.bs rest')
          (WppPost (chunkedHeaderSentMergeSpec A) x R s0) (WppPanic R s0)) →
      (mergeLoopBin V1State.Unchunked.EkSent.mergeField (cur.length - innerLimit) uc cur innerLimit 97 = none →
        (Proto.mergeMessage V1State.Chunked.HeaderSent.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none) →
      s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName + 464#64 →
      s.status = .Running → s.sp = s0.sp - 128#64 → s.trace = s0.trace → s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s.readReg64 (Reg.gpr 23#5) = 1#64 → s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s.readReg64 (Reg.gpr 25#5) = 8#64 → s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit → ChunkedInl10CalleeSaved s0 s →
      SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
        (chunkedHeaderSentUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr uc sendingEk receivingCt1 x.bs cur)
        (WppPost (chunkedHeaderSentMergeSpec A) x R s0) (WppPanic R s0) := by
  have htag1_varint := fun {s uc rest} =>
    @chunkedHeaderSent_uc_tag1_varint_step img A H hPushCall hVarintCall x R s0 s uc sendingEk receivingCt1 rest outerLimit innerLimit
  have htag1_wt_err := fun {s uc rest} =>
    @chunkedHeaderSent_uc_tag1_wt_err_step img A H hFromCall hPushCall x R s0 s uc sendingEk receivingCt1 rest
  have htag2_step := fun {s uc rest} (iwt : WireType) =>
    @chunkedHeaderSent_uc_tag2_step img A H hPushCall hAuthCall x R s0 s uc sendingEk receivingCt1 rest iwt outerLimit innerLimit
  have htag3_step := fun {s uc rest} (iwt : WireType) =>
    @chunkedHeaderSent_uc_tag3_step img A H hPushCall hBytesCall x R s0 s uc sendingEk receivingCt1 rest iwt outerLimit innerLimit
  have hskip_step := fun {s uc rest} (iwt : WireType) (tag : Nat) =>
    @chunkedHeaderSent_uc_skip_step img A H hPushCall hSkipCall x R s0 s uc sendingEk receivingCt1 rest iwt tag outerLimit innerLimit
  intro n; induction n with
  | zero =>
    intro uc cur s hcur_n hcur_le hcur_suf hcont_ok hnone_loop hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
    exact chunkedHeaderSent_uc_loop_le_exit hFromCall hPushCall (by omega) hsp_align hcur_le hcur_suf hlim_lt
      (fun hlt => hnone_loop (mergeLoopBin_lt_limit _ _ _ _ _ _ hlt)) (fun s' heq => hcont_ok uc cur s' heq hcur_le hcur_suf (mergeLoopBin_eq_limit _ _ _ _ _ _ heq))
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
  | succ n ih =>
    intro uc cur s hcur_n hcur_le hcur_suf hcont_ok hnone_loop hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
    by_cases hle_lim : cur.length ≤ innerLimit
    · exact chunkedHeaderSent_uc_loop_le_exit hFromCall hPushCall hle_lim hsp_align hcur_le hcur_suf hlim_lt
        (fun hlt => hnone_loop (mergeLoopBin_lt_limit _ _ _ _ _ _ hlt))
        (fun s' heq => hcont_ok uc cur s' heq hcur_le hcur_suf (mergeLoopBin_eq_limit _ _ _ _ _ _ heq))
        hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
    · have hcur_lt : cur.length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
      refine chunkedHeaderSent_uc_decode_key_step hFromCall hPushCall hVarintCall hle_lim hsp_align
        hcur_le hcur_lt hcur_suf hnone_loop ?_ hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
      intro key iwt rest s' hd hk_ge hwt hitag0 hpc' hrun' hsp' htr' hx0' hx1' hx19' hx20' hx21' hx22' hx23' hx24' hx25' hx26' hcs'
      obtain ⟨hx27', hx28', hvregs'⟩ := hcs'; have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd; have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
      have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le; have hrest_lt : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest_le hbs_lt
      have hrest_suf : IsDropSuffix x.bs rest := suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd); have htag_lt : key.toNat / 8 < 2 ^ 32 := by omega
      have hstep := mergeLoopBin_of_key_ok (m := uc) (depth' := 97) protoPrefixStep_unchunked_ekSent_mergeField hle_lim hd hk_ge hwt hitag0
      by_cases htag1 : key.toNat / 8 = 1
      · rw [htag1] at hx1' hstep; rw [unchunkedEkSent_mergeField_tag1] at hstep
        chunkedHeaderSentMerge_fetches img.base H 516 24; generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName = entry; examples_hide_fetches
        apply SepWPpIn.of_sepWP (mid := entry + 604#64); wp_steps; wp_reach
        by_cases hiwt : iwt = .varint
        · subst hiwt
          refine htag1_varint hsp_align hrest_le hrest_lt hrest_suf (fun hdv_none => hnone_loop (by rw [hstep]; simp [hdv_none]))
            (fun v rest' s'' hdv_some hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs'' => ?_)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
            (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20']) (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23'])
            (by simp only [arm64_norm, hx24']) (by simp only [arm64_norm, hx25']) (by simp only [arm64_norm, hx26']) ⟨by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩
          have hr'_lt : rest'.length < rest.length := decodeVarint_length hdv_some; have hr'_le : rest'.length ≤ rest.length := Nat.le_of_lt hr'_lt
          exact ih { uc with epoch := v } rest' s'' (by omega) (Nat.le_trans hr'_le hrest_le) (suffix_trans hrest_le hrest_suf hr'_le (decodeVarint_suffix hdv_some))
            (fun uc' r' sf hr_eq hr_le hr_suf hml => hcont_ok uc' r' sf hr_eq hr_le hr_suf (by rw [hstep]; simpa [hdv_some] using hml))
            (fun hml => hnone_loop (by rw [hstep]; simpa [hdv_some] using hml))
            hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs''
        · exact htag1_wt_err hiwt hsp_align hrest_le hrest_suf (hnone_loop (by rw [hstep]; simp [hiwt]))
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
            (by simp only [arm64_norm, hx0']) ⟨by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩
      · by_cases htag2 : key.toNat / 8 = 2
        · obtain ⟨hb1_1, _⟩ := itag_beq_tag_false htag1 htag_lt (by decide : 1 < 2 ^ 32)
          have hb1_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 1#32) = false := by rw [sf_truncate32_ofNat64]; exact hb1_1
          rw [htag2] at hx1' hstep; rw [unchunkedEkSent_mergeField_tag2] at hstep
          chunkedHeaderSentMerge_fetches img.base H 516 24; generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName = entry; examples_hide_fetches
          apply SepWPpIn.of_sepWP (mid := entry + 560#64); wp_steps; wp_reach
          refine htag2_step iwt hsp_align hrest_le hrest_lt hrest_suf (fun hauth_none => hnone_loop (by rw [hstep, hauth_none]; rfl))
            (fun auth' rest' s'' hauth_some hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs'' => ?_)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
            (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20']) (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23'])
            (by simp only [arm64_norm, hx24']) (by simp only [arm64_norm, hx25']) (by simp only [arm64_norm, hx26']) ⟨by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩
          have hr'_le : rest'.length ≤ rest.length := (proto_mergeMessage_suffix hauth_some).1
          exact ih { uc with auth := some auth' } rest' s'' (by omega) (Nat.le_trans hr'_le hrest_le)
            (suffix_trans hrest_le hrest_suf hr'_le (proto_mergeMessage_suffix hauth_some).2)
            (fun uc' r' sf hr_eq hr_le hr_suf hml => hcont_ok uc' r' sf hr_eq hr_le hr_suf (by rw [hstep, hauth_some]; exact hml))
            (fun hml => hnone_loop (by rw [hstep, hauth_some]; exact hml))
            hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs''
        · by_cases htag3 : key.toNat / 8 = 3
          · rw [htag3] at hx1' hstep; rw [unchunkedEkSent_mergeField_tag3] at hstep
            chunkedHeaderSentMerge_fetches img.base H 516 24
            generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName = entry; examples_hide_fetches; apply SepWPpIn.of_sepWP (mid := entry + 440#64); wp_steps; wp_reach
            refine htag3_step iwt hsp_align hrest_le hrest_lt hrest_suf (fun hmb_none => hnone_loop (by rw [hstep, hmb_none]; rfl))
              (fun v rest' s'' hmb_some hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs'' => ?_)
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
              (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
              (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23'])
              (by simp only [arm64_norm, hx24']) (by simp only [arm64_norm, hx25']) (by simp only [arm64_norm, hx26']) ⟨by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩
            have hr'_le : rest'.length ≤ rest.length := mergeBytes_length hmb_some
            exact ih { uc with dk := v } rest' s'' (by omega) (Nat.le_trans hr'_le hrest_le) (suffix_trans hrest_le hrest_suf hr'_le (mergeBytes_suffix hmb_some))
              (fun uc' r' sf hr_eq hr_le hr_suf hml => hcont_ok uc' r' sf hr_eq hr_le hr_suf (by rw [hstep, hmb_some]; exact hml))
              (fun hml => hnone_loop (by rw [hstep, hmb_some]; exact hml))
              hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs''
          · obtain ⟨hb1_1, _⟩ := itag_beq_tag_false htag1 htag_lt (by decide : 1 < 2 ^ 32)
            obtain ⟨hb2_1, _⟩ := itag_beq_tag_false htag2 htag_lt (by decide : 2 < 2 ^ 32)
            obtain ⟨hb3_1, _⟩ := itag_beq_tag_false htag3 htag_lt (by decide : 3 < 2 ^ 32)
            have hb1_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 1#32) = false := by rw [sf_truncate32_ofNat64]; exact hb1_1
            have hb2_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 2#32) = false := by rw [sf_truncate32_ofNat64]; exact hb2_1
            have hb3_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 3#32) = false := by rw [sf_truncate32_ofNat64]; exact hb3_1
            rw [unchunkedEkSent_mergeField_other uc iwt rest 97 htag_lt htag1 htag2 htag3] at hstep
            chunkedHeaderSentMerge_fetches img.base H 516 24
            generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderSentMergeName = entry; examples_hide_fetches
            apply SepWPpIn.of_sepWP (mid := entry + 540#64); wp_steps; wp_reach
            refine hskip_step iwt (key.toNat / 8) hsp_align hrest_le hrest_lt hrest_suf htag_lt (fun hsf_none => hnone_loop (by rw [hstep, hsf_none]; rfl))
              (fun rest' s'' hsf_some hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs'' => ?_)
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
              (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx1', sf_truncate32_ofNat64]) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
              (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23'])
              (by simp only [arm64_norm, hx24']) (by simp only [arm64_norm, hx25']) (by simp only [arm64_norm, hx26']) ⟨by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩
            have hr'_le : rest'.length ≤ rest.length := (skip_length (2 * rest.length + 2)).1 _ _ _ _ _ hsf_some
            exact ih uc rest' s'' (by omega) (Nat.le_trans hr'_le hrest_le)
              (suffix_trans hrest_le hrest_suf hr'_le ((skip_suffix (2 * rest.length + 2)).1 _ _ _ _ _ hsf_some))
              (fun uc' r' sf hr_eq hr_le hr_suf hml => hcont_ok uc' r' sf hr_eq hr_le hr_suf (by rw [hstep, hsf_some]; exact hml))
              (fun hml => hnone_loop (by rw [hstep, hsf_some]; exact hml))
              hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs''

set_option quotPrecheck false in
local notation "entry" => (blkPl_302).base

theorem chunkedHeaderSent_ret_err_exit_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    {x : ChunkedHeaderSentMergeGhost} {R : SepProp} {s0 : State} {m : V1State.Chunked.HeaderSent} {s : State} {err : BitVec 64} {n : Nat}
    (hnone : (Proto.mergeMessage V1State.Chunked.HeaderSent.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hn : n ≤ 3) (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_302).base + 124#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hx1 : s.readReg64 (Reg.gpr 1#5) = err)
    (hcs : ChunkedInl10CalleeSaved s0 s) : SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s
      (decodeErrorAtStackLen A err n ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
        memRegion (s0.sp - 128#64) 48 ∗
        chunkedHeaderSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (WppPost (chunkedHeaderSentMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  apply SepWPpLscro.of_sepWP_ret; unfold WppPost chunkedHeaderSentMergeSpec
  simp only [hnone, chunkedHeaderSentErrFrame, chunkedInlSavedRegs10, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp, hx1]
  wp_steps
  have hle3 : decodeErrorAtStackLen A err n ⊢ ∃∗ k : Nat, ⌜k ≤ 3⌝ ∗ decodeErrorAtStackLen A err k := by
    refine Entails.trans ?_ (Entails.sepExists_intro n)
    rw [pure_sepConj_of_true hn]; exact Entails.refl _
  apply SepWP.fold hle3 (by sep_focus); apply SepWP.fold (chunkedHeaderSentPBAt_entails_exists A x.msgPtr m) (by sep_focus)
  apply SepWP.fold (stackAt_chunkedInl10_epilogue s0.sp s0) (by unfold chunkedInlSavedRegs10; sep_focus)
  wp_done

theorem chunkedHeaderSent_from_err_exit_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 261) (decodeErrorFromSpec A))
    {x : ChunkedHeaderSentMergeGhost} {R : SepProp} {s0 : State} {m : V1State.Chunked.HeaderSent} {s : State} {w : BitVec 64}
    (hnone : (Proto.mergeMessage V1State.Chunked.HeaderSent.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hw : KindNoHeap w) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_302).base + 112#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s (((s0.sp - 128#64) ↦₆₄ w) ∗ memRegion (s0.sp - 120#64) 40 ∗
        stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
        chunkedHeaderSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (WppPost (chunkedHeaderSentMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  apply SepWPpLscro.of_sepWP (mid := lsmpl.base 261)
  conv => arg 4; rw [chunkedInlBelow_decodeErrorHook s0.sp, chunkedHeaderSentErrFrame]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpLscro.call_frame (x := (s0.sp - 128#64, w)) (ret_pc := entry + 120#64) hFromCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorFromSpec]; simp only [arm64_norm, hsp]; rfl)
    hw (by sep_focus) (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, _, _, _, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx27, hx28, hvregs] at hpcm hspm hx27_m hx28_m hvregs_m
  apply SepWPpLscro.of_sepWP_ret; unfold WppPost chunkedHeaderSentMergeSpec
  simp only [decodeErrorFromSpec, hnone, chunkedInlSavedRegs10, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp, hspm]
  apply SepWP.fold (chunkedInlBelow_decodeErrorHook_entails s0.sp) (by sep_focus); apply SepWP.fold (memRegion8_memRegion40_entails_48_160 s0.sp) (by sep_focus)
  wp_steps; apply SepWP.fold (decodeErrorWith_zero_entails_le3_inl A _) (by sep_focus)
  apply SepWP.fold (chunkedHeaderSentPBAt_entails_exists A x.msgPtr m) (by sep_focus)
  apply SepWP.fold (stackAt_chunkedInl10_epilogue s0.sp s0) (by unfold chunkedInlSavedRegs10; sep_focus)
  wp_done

theorem chunkedHeaderSent_uc_push_exit_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    {x : ChunkedHeaderSentMergeGhost} {R : SepProp} {s0 : State} {m : V1State.Chunked.HeaderSent} {s : State} {err : BitVec 64} {n : Nat}
    (hnone : (Proto.mergeMessage V1State.Chunked.HeaderSent.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hn : n ≤ 2) (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_302).base + 792#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hx1 : s.readReg64 (Reg.gpr 1#5) = err)
    (hcs : ChunkedInl10CalleeSaved s0 s) : SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s
      (decodeErrorAtStackLen A err n ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
        memRegion (s0.sp - 128#64) 48 ∗
        chunkedHeaderSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (WppPost (chunkedHeaderSentMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  have hret := @chunkedHeaderSent_ret_err_exit_placed _ A H x R s0 m
  apply SepWPpLscro.of_sepWP (mid := lsmpl.base 257)
  conv => arg 4; rw [chunkedInlBelow_decodeErrorHook s0.sp, memRegion_48_cells1_160 s0.sp, chunkedHeaderSentErrFrame]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v_stk0; wp_steps; wp_reach
  refine SepWPpLscro.call_frame (x := (s0.sp - 128#64, err, n)) (ret_pc := entry + 828#64) hPushCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorPushSpec]; simp only [arm64_norm, hsp, hx1]; rfl) (by omega : n < 2 ^ 32) (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, _, _, _, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx27, hx28, hvregs] at hpcm hspm hx27_m hx28_m hvregs_m
  apply SepWPpLscro.of_sepWP (mid := entry + 124#64); (conv => arg 4; simp only [decodeErrorPushSpec, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; intro htrm
  apply SepWP.fold (chunkedInlBelow_decodeErrorHook_entails s0.sp) (by sep_focus); wp_steps
  apply SepWP.fold (pointsTo64_memRegion40_entails_48_160 s0.sp err) (by sep_focus); wp_reach
  apply SepWPpLscro.weaken_pre (P' := decodeErrorAtStackLen A err (n + 1) ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedHeaderSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
    (by dsimp only [chunkedHeaderSentErrFrame]; sep_entail)
  exact hret hnone (by omega : n + 1 ≤ 3) herr hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
    (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm]) ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

theorem chunkedHeaderSent_uc_from_push_exit_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 261) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    {x : ChunkedHeaderSentMergeGhost} {R : SepProp} {s0 : State} {m : V1State.Chunked.HeaderSent} {s : State} {w : BitVec 64}
    (hnone : (Proto.mergeMessage V1State.Chunked.HeaderSent.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hw : KindNoHeap w) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_302).base + 780#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s (((s0.sp - 128#64) ↦₆₄ w) ∗ memRegion (s0.sp - 120#64) 40 ∗
        stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
        chunkedHeaderSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (WppPost (chunkedHeaderSentMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  have hpush := @chunkedHeaderSent_uc_push_exit_placed _ A H hPushCall x R s0 m
  apply SepWPpLscro.of_sepWP (mid := lsmpl.base 261)
  conv => arg 4; rw [chunkedInlBelow_decodeErrorHook s0.sp, chunkedHeaderSentErrFrame]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpLscro.call_frame (x := (s0.sp - 128#64, w)) (ret_pc := entry + 788#64) hFromCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorFromSpec]; simp only [arm64_norm, hsp]; rfl)
    hw (by sep_focus) (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, _, _, _, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx27, hx28, hvregs] at hpcm hspm hx27_m hx28_m hvregs_m
  apply SepWPpLscro.of_sepWP (mid := entry + 792#64)
  (conv => arg 4; simp only [decodeErrorFromSpec, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨hsm0, htrm⟩
  apply SepWP.fold (chunkedInlBelow_decodeErrorHook_entails s0.sp) (by sep_focus); apply SepWP.fold (memRegion8_memRegion40_entails_48_160 s0.sp) (by sep_focus)
  wp_steps; wp_reach
  apply SepWPpLscro.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedHeaderSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
    (by dsimp only [chunkedHeaderSentErrFrame]; sep_entail)
  exact hpush hnone (by decide : 0 ≤ 2) hsm0 hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
    (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm]) ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

theorem chunkedHeaderSent_uc_field_push_exit_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    {x : ChunkedHeaderSentMergeGhost} {R : SepProp} {s0 : State} {m : V1State.Chunked.HeaderSent} {s : State} {err : BitVec 64} {n : Nat}
    (hnone : (Proto.mergeMessage V1State.Chunked.HeaderSent.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hn : n ≤ 1) (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_302).base + 1072#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = s0.sp - 128#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s (((s0.sp - 128#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A err n ∗
        memRegion (s0.sp - 120#64) 40 ∗
        stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
        chunkedHeaderSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (WppPost (chunkedHeaderSentMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  have hpush := @chunkedHeaderSent_uc_push_exit_placed _ A H hPushCall x R s0 m
  apply SepWPpLscro.of_sepWP (mid := lsmpl.base 257)
  conv => arg 4; rw [chunkedInlBelow_decodeErrorHook s0.sp, chunkedHeaderSentErrFrame]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpLscro.call_frame (x := (s0.sp - 128#64, err, n)) (ret_pc := entry + 1076#64) hPushCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorPushSpec]; simp only [arm64_norm, hsp, hx0]; rfl) (by omega : n < 2 ^ 32) (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, _, _, _, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx27, hx28, hvregs] at hpcm hspm hx27_m hx28_m hvregs_m
  apply SepWPpLscro.of_sepWP (mid := entry + 792#64); (conv => arg 4; simp only [decodeErrorPushSpec, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; intro htrm
  apply SepWP.fold (chunkedInlBelow_decodeErrorHook_entails s0.sp) (by sep_focus); wp_steps
  apply SepWP.fold (pointsTo64_memRegion40_entails_48_160 s0.sp err) (by sep_focus); wp_reach
  apply SepWPpLscro.weaken_pre (P' := decodeErrorAtStackLen A err (n + 1) ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedHeaderSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
    (by dsimp only [chunkedHeaderSentErrFrame]; sep_entail)
  exact hpush hnone (by omega : n + 1 ≤ 2) herr hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
    (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm]) ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

theorem chunkedHeaderSent_push_ret_exit_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    {x : ChunkedHeaderSentMergeGhost} {R : SepProp} {s0 : State} {m : V1State.Chunked.HeaderSent} {s : State} {err : BitVec 64} {n : Nat}
    (hnone : (Proto.mergeMessage V1State.Chunked.HeaderSent.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hn : n ≤ 2) (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_302).base + 824#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = s0.sp - 128#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s (((s0.sp - 128#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A err n ∗
        memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
        chunkedHeaderSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (WppPost (chunkedHeaderSentMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  have hret := @chunkedHeaderSent_ret_err_exit_placed _ A H x R s0 m
  apply SepWPpLscro.of_sepWP (mid := lsmpl.base 257)
  conv => arg 4; rw [chunkedInlBelow_decodeErrorHook s0.sp, chunkedHeaderSentErrFrame]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpLscro.call_frame (x := (s0.sp - 128#64, err, n)) (ret_pc := entry + 828#64) hPushCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorPushSpec]; simp only [arm64_norm, hsp, hx0]; rfl) (by omega : n < 2 ^ 32) (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, _, _, _, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx27, hx28, hvregs] at hpcm hspm hx27_m hx28_m hvregs_m
  apply SepWPpLscro.of_sepWP (mid := entry + 124#64); (conv => arg 4; simp only [decodeErrorPushSpec, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; intro htrm
  apply SepWP.fold (chunkedInlBelow_decodeErrorHook_entails s0.sp) (by sep_focus); wp_steps
  apply SepWP.fold (pointsTo64_memRegion40_entails_48_160 s0.sp err) (by sep_focus); wp_reach
  apply SepWPpLscro.weaken_pre (P' := decodeErrorAtStackLen A err (n + 1) ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedHeaderSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
    (by dsimp only [chunkedHeaderSentErrFrame]; sep_entail)
  exact hret hnone (by omega : n + 1 ≤ 3) herr hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
    (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm]) ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

theorem chunkedHeaderSent_uc_skip_step_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    (hSkipCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 263) (skipField3Spec A))
    {x : ChunkedHeaderSentMergeGhost} {R : SepProp} {s0 s : State} {uc : V1State.Unchunked.EkSent} {sendingEk : Option PolynomialEncoder}
    {receivingCt1 : Option PolynomialDecoder} {rest : List (BitVec 8)} {iwt : WireType} {tag outerLimit innerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest) (htag_lt : tag < 2 ^ 32)
    (hnone_of_sf : skipField (2 * rest.length + 2) 97 tag iwt rest = none →
      (Proto.mergeMessage V1State.Chunked.HeaderSent.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (rest' : List (BitVec 8)) (s' : State),
      skipField (2 * rest.length + 2) 97 tag iwt rest = some rest' → s'.pc = (blkPl_302).base + 464#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace → s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit → ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s'
        (chunkedHeaderSentUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr uc sendingEk receivingCt1 x.bs rest')
        (WppPost (chunkedHeaderSentMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_302).base + 540#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : (s.readReg64 (Reg.gpr 1#5)).setWidth 32 = BitVec.ofNat 32 tag)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s
      (chunkedHeaderSentUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr uc sendingEk receivingCt1 x.bs rest)
      (WppPost (chunkedHeaderSentMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hpush_exit := @chunkedHeaderSent_uc_push_exit_placed _ A H hPushCall x R s0 { uc := some uc, sendingEk := sendingEk, receivingCt1 := receivingCt1 }
  apply SepWPpLscro.of_sepWP (mid := lsmpl.base 263)
  conv => arg 4; rw [chunkedHeaderSentUcLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf, chunkedInlBelow_skipField97 s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpLscro.call_frame (x := ⟨iwt, tag, 97, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := entry + 552#64) hSkipCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [skipField3Spec]; simp only [arm64_norm, hsp, hx0, hx1, hx19, setWidth8_ofNat64_wt]; rfl)
    (⟨htag_lt, by decide, hrest_lt⟩ : tag < 2 ^ 32 ∧ 97 < 2 ^ 32 ∧ rest.length < 2 ^ 63) (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
  cases hsf : skipField (2 * rest.length + 2) 97 tag iwt rest with
  | none =>
    have hnone := hnone_of_sf hsf
    apply SepWPpLscro.of_sepWP (mid := entry + 792#64)
    (conv => arg 4; simp only [skipField3Spec, hsf, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (chunkedInlBelow_skipField97_entails s0.sp) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (unchunked3CapAt_entails_chunkedHeaderSentPBAt A x.msgPtr rest.length uc sendingEk receivingCt1) (by sep_focus); wp_steps; wp_reach
    apply SepWPpLscro.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedHeaderSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc, sendingEk := sendingEk, receivingCt1 := receivingCt1 } x.bs)
      (by dsimp only [chunkedHeaderSentErrFrame]; sep_entail)
    exact hpush_exit hnone (by decide : 0 ≤ 2) hsm0 hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm]) ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some rest' =>
    have hrest'_le : rest'.length ≤ rest.length := (skip_length _).1 _ _ _ _ _ hsf
    apply SepWPpLscro.of_sepWP (mid := entry + 464#64)
    (conv => arg 4; simp only [skipField3Spec, hsf, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    apply SepWP.fold (chunkedInlBelow_skipField97_entails s0.sp) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (unchunked3CapAt_mono A x.msgPtr uc.epoch uc.auth uc.dk hrest'_le) (by sep_focus); wp_steps; wp_reach
    apply SepWPpLscro.weaken_pre (P' := chunkedHeaderSentUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr uc sendingEk receivingCt1 x.bs rest')
      (by dsimp only [chunkedHeaderSentUcLoopPre]; sep_entail)
    exact hcont rest' _ hsf (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
      (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m]) (by simp only [arm64_norm, hx25_m]) (by simp only [arm64_norm, hx26_m])
      ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

theorem chunkedHeaderSent_uc_tag1_varint_step_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 291) (decodeVarint2Spec A))
    {x : ChunkedHeaderSentMergeGhost} {R : SepProp} {s0 s : State} {uc : V1State.Unchunked.EkSent} {sendingEk : Option PolynomialEncoder}
    {receivingCt1 : Option PolynomialDecoder} {rest : List (BitVec 8)} {outerLimit innerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest) (hnone_of_dv : decodeVarint rest = none →
      (Proto.mergeMessage V1State.Chunked.HeaderSent.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (v : BitVec 64) (rest' : List (BitVec 8)) (s' : State),
      decodeVarint rest = some (v, rest') → s'.pc = (blkPl_302).base + 464#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace → s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit → ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s'
        (chunkedHeaderSentUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { uc with epoch := v } sendingEk receivingCt1 x.bs rest')
        (WppPost (chunkedHeaderSentMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_302).base + 604#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = 0#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s
      (chunkedHeaderSentUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr uc sendingEk receivingCt1 x.bs rest)
      (WppPost (chunkedHeaderSentMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hfpush := @chunkedHeaderSent_uc_field_push_exit_placed _ A H hPushCall x R s0 { uc := some uc, sendingEk := sendingEk, receivingCt1 := receivingCt1 }
  apply SepWPpLscro.of_sepWP (mid := lsmpl.base 291)
  conv => arg 4; rw [chunkedHeaderSentUcLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf, chunkedInlBelow_decodeVarint2 s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpLscro.call_frame (x := ⟨x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := entry + 616#64) hVarintCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, hsp, hx19]; rfl)
    hrest_lt (by sep_focus) (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
  cases hdv : decodeVarint rest with
  | none =>
    have hnone := hnone_of_dv hdv
    apply SepWPpLscro.of_sepWP (mid := entry + 1072#64); (conv => arg 4; simp only [decodeVarint2Spec, hdv, memRegion_48_cells1_160 s0.sp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp])
    apply SepWP.exists_elim; intro v_stk0; apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
    have hcbnz_err : (sm.readReg64 (Reg.gpr 1#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm1
    apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (unchunked3CapAt_entails_chunkedHeaderSentPBAt A x.msgPtr rest.length uc sendingEk receivingCt1) (by sep_focus); wp_steps; wp_reach
    apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 1#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedHeaderSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc, sendingEk := sendingEk, receivingCt1 := receivingCt1 } x.bs)
      (by dsimp only [chunkedHeaderSentErrFrame]; sep_entail)
    exact hfpush hnone (by decide : 0 ≤ 1) hsm1 hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm, hspm]) ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨v, rest'⟩
    have hrest'_le : rest'.length ≤ rest.length := Nat.le_of_lt (decodeVarint_length hdv)
    apply SepWPpLscro.of_sepWP (mid := entry + 464#64); (conv => arg 4; simp only [decodeVarint2Spec, hdv, unchunked3CapAt_eq, sepConj_assoc, arm64_norm, hsp])
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩; apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (vecU8CapAt_mono' A x.msgPtr uc.dk hrest'_le) (by sep_focus)
    apply SepWP.fold (optAuthenticatorPBCapAt_mono A (x.msgPtr + 0x18#64) uc.auth hrest'_le) (by sep_focus); wp_steps; wp_reach
    apply SepWPpLscro.weaken_pre (P' := chunkedHeaderSentUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { uc with epoch := v } sendingEk receivingCt1 x.bs rest')
      (by dsimp only [chunkedHeaderSentUcLoopPre]; rw [unchunked3CapAt_eq]; sep_entail)
    exact hcont v rest' _ hdv (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
      (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m]) (by simp only [arm64_norm, hx25_m]) (by simp only [arm64_norm, hx26_m])
      ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

theorem chunkedHeaderSent_uc_tag1_wt_err_step_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 261) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    {x : ChunkedHeaderSentMergeGhost} {R : SepProp} {s0 s : State} {uc : V1State.Unchunked.EkSent} {sendingEk : Option PolynomialEncoder}
    {receivingCt1 : Option PolynomialDecoder} {rest : List (BitVec 8)} {iwt : WireType}
    (hiwt : iwt ≠ .varint) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone : (Proto.mergeMessage V1State.Chunked.HeaderSent.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hpc : s.pc = (blkPl_302).base + 604#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hcs : ChunkedInl10CalleeSaved s0 s) : SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s
      (chunkedHeaderSentUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr uc sendingEk receivingCt1 x.bs rest)
      (WppPost (chunkedHeaderSentMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hcbnz_wt : (BitVec.ofNat 64 iwt.toNat == 0#64) = false := iwt_cbnz_true_of_ne_varint hiwt
  have hfpush := @chunkedHeaderSent_uc_field_push_exit_placed _ A H hPushCall x R s0 { uc := some uc, sendingEk := sendingEk, receivingCt1 := receivingCt1 }
  apply SepWPpLscro.of_sepWP (mid := lsmpl.base 261)
  conv => arg 4; rw [chunkedHeaderSentUcLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, chunkedInlBelow_decodeErrorHook s0.sp, memRegion_48_wtErr160 s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro b_wt1; apply SepWP.exists_elim; intro b_wt0; apply SepWP.exists_elim; intro v_wt0; wp_steps
  apply SepWP.fold (wtErr160_entails_memRegion40 s0.sp _ _) (by sep_focus)
  apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
  apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
  apply SepWP.fold (unchunked3CapAt_entails_chunkedHeaderSentPBAt A x.msgPtr rest.length uc sendingEk receivingCt1) (by sep_focus); wp_reach
  refine SepWPpLscro.call_frame (x := (s0.sp - 128#64, 0x8000000000000006#64))
    (ret_pc := entry + 1036#64) hFromCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorFromSpec]; simp only [arm64_norm, hsp]; rfl) (by decide : KindNoHeap 0x8000000000000006#64) (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, _, _, _, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx27, hx28, hvregs] at hpcm hspm hx27_m hx28_m hvregs_m
  apply SepWPpLscro.of_sepWP (mid := entry + 1072#64)
  (conv => arg 4; simp only [decodeErrorFromSpec, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨hsm0, htrm⟩
  apply SepWP.fold (chunkedInlBelow_decodeErrorHook_entails s0.sp) (by sep_focus); apply SepWP.fold (memRegion8_memRegion40_entails_48_160 s0.sp) (by sep_focus)
  conv => arg 4; rw [memRegion_48_cells1_160 s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v_stk0; wp_steps; wp_reach
  apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedHeaderSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc, sendingEk := sendingEk, receivingCt1 := receivingCt1 } x.bs)
    (by dsimp only [chunkedHeaderSentErrFrame]; sep_entail)
  exact hfpush hnone (by decide : 0 ≤ 1) hsm0 hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
    (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm, hspm]) ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

private theorem chunkedHeaderSent_uc_auth_init_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    {x : ChunkedHeaderSentMergeGhost} {R : SepProp} {s0 s : State} {uc : V1State.Unchunked.EkSent} {sendingEk : Option PolynomialEncoder}
    {receivingCt1 : Option PolynomialDecoder} {rest : List (BitVec 8)} (hcont : ∀ (s' : State),
      s'.pc = (blkPl_302).base + 584#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s.trace → s'.readReg64 (Reg.gpr 0#5) = s.readReg64 (Reg.gpr 0#5) →
      s'.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) → s'.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) →
      s'.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) → s'.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) → ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s' (vecU8CapAt A x.msgPtr rest.length uc.dk ∗
          authenticatorPBCapAt A (x.msgPtr + 0x18#64) rest.length (uc.auth.getD default) ∗ ((x.msgPtr + 0x48#64) ↦₆₄ uc.epoch) ∗
          optPolynomialEncoderPBAt A (x.msgPtr + 80#64) sendingEk ∗
          optPolynomialDecoderPBAt A (x.msgPtr + 136#64) receivingCt1 ∗
          stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
          memRegion (s0.sp - 128#64) 48 ∗ chunkedInlSavedRegs10 s0.sp s0 ∗ (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool)
        (WppPost (chunkedHeaderSentMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_302).base + 560#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr) (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) : SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s
      (chunkedHeaderSentUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr uc sendingEk receivingCt1 x.bs rest)
      (WppPost (chunkedHeaderSentMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  rcases hauth : uc.auth with _ | auth
  · rw [hauth] at hcont; dsimp only [Option.getD] at hcont
    apply SepWPpLscro.of_sepWP (mid := entry + 584#64)
    conv => arg 4; rw [chunkedHeaderSentUcLoopPre, unchunked3CapAt_eq_auth, hauth, optAuthenticatorPBCapAt, memRegion_40_cells (x.msgPtr + 0x18#64)]
    simp only [noneCap, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm]
    apply SepWP.exists_elim; intro w1; apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
    apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5; wp_steps
    have hdef := default_cells_entails_authenticatorPBCapAt A (x.msgPtr + 0x18#64) rest.length
    simp only [arm64_norm] at hdef
    apply SepWP.fold hdef (by sep_focus); wp_reach
    apply SepWPpLscro.weaken_pre (P' := vecU8CapAt A x.msgPtr rest.length uc.dk ∗ authenticatorPBCapAt A (x.msgPtr + 0x18#64) rest.length default ∗ ((x.msgPtr + 0x48#64) ↦₆₄ uc.epoch) ∗ optPolynomialEncoderPBAt A (x.msgPtr + 80#64) sendingEk ∗ optPolynomialDecoderPBAt A (x.msgPtr + 136#64) receivingCt1 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedInlSavedRegs10 s0.sp s0 ∗ (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool)
      (by sep_entail)
    exact hcont _ (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm, hrun]) (by simp (config := { failIfUnchanged := false }) only [arm64_norm, hsp])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm]) (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm]) (by simp (config := { failIfUnchanged := false }) only [arm64_norm, hx20])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm]) (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm, hx23]) (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm]) (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
      ⟨by simp (config := { failIfUnchanged := false }) only [arm64_norm, hx27],
       by simp (config := { failIfUnchanged := false }) only [arm64_norm, hx28],
       by simp (config := { failIfUnchanged := false }) only [arm64_norm, hvregs]⟩
  · rw [hauth] at hcont; dsimp only [Option.getD] at hcont
    let macCap : SepProp := ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap rest.length⌝ ∗ vecU8At A (x.msgPtr + 0x18#64 + 0x18#64) cap ptr auth.macKey
    have hcmn_in : authenticatorPBCapAt A (x.msgPtr + 0x18#64) rest.length auth ⊢
        ∃∗ cap_ik : BitVec 64, ∃∗ ptr_ik : BitVec 64,
          ⌜cap_ik.toNat < 2 ^ 63 ∧ BytesMergeCapOk cap_ik rest.length⌝ ∗ ((x.msgPtr + 24#64) ↦₆₄ cap_ik) ∗ ((x.msgPtr + 32#64) ↦₆₄ ptr_ik) ∗
          ((x.msgPtr + 40#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
          vecU8Buf A cap_ik ptr_ik auth.rootKey ∗ macCap := by
      have hlt_buf : ∀ (cap ptr : BitVec 64) (bs : List (BitVec 8)),
          vecU8Buf A cap ptr bs ⊢ ⌜cap.toNat < 2 ^ 63⌝ ∗ vecU8Buf A cap ptr bs := by
        intro cap ptr bs; unfold vecU8Buf
        refine Entails.pure_left fun h => Entails.pure_right h.2.1 (Entails.pure_right h (Entails.refl _))
      have hlt_at : ∀ (a cap ptr : BitVec 64) (bs : List (BitVec 8)),
          vecU8At A a cap ptr bs ⊢ ⌜cap.toNat < 2 ^ 63⌝ ∗ (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗
            ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ vecU8Buf A cap ptr bs := by
        intro a cap ptr bs; rw [vecU8At_eq_header_sep_buf, vecHeader]
        exact Entails.trans (sepConj_mono_right (hlt_buf cap ptr bs)) (by sep_entail)
      change (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap rest.length⌝ ∗ vecU8At A (x.msgPtr + 0x18#64) cap ptr auth.rootKey) ∗ macCap ⊢ _
      rw [sepExists_sepConj_left]; refine ProofLib.Entails.sepExists_elim fun cap_ik => ?_
      rw [sepExists_sepConj_left]; refine ProofLib.Entails.sepExists_elim fun ptr_ik => ?_
      refine Entails.trans ?_ (Entails.sepExists_intro cap_ik); refine Entails.trans ?_ (Entails.sepExists_intro ptr_ik)
      rw [sepConj_assoc]; refine Entails.pure_left fun hcap => ?_
      refine Entails.trans (sepConj_mono_left (hlt_at (x.msgPtr + 0x18#64) cap_ik ptr_ik auth.rootKey)) ?_
      simp only [sepConj_assoc, bv64_add24_add8, bv64_add24_add16]
      exact Entails.pure_left fun hlt => Entails.pure_right ⟨hlt, hcap⟩ (Entails.refl _)
    apply SepWPpLscro.of_sepWP (mid := entry + 584#64)
    conv => arg 4; rw [chunkedHeaderSentUcLoopPre, unchunked3CapAt_eq_auth, hauth, optAuthenticatorPBCapAt]
    simp only [sepConj_assoc]
    apply SepWP.fold hcmn_in (by sep_focus)
    wp_simp_pre [sepExists_sepConj_left, sepConj_assoc]
    apply SepWP.exists_elim; intro cap_ik; apply SepWP.exists_elim; intro ptr_ik; apply SepWP.pure_elim; rintro ⟨hcap_lt, hcap_ik⟩
    have hcmn1 := cap_add_one_beq_zero_false hcap_lt; have hcmn2 := cap_add_one_bne_zero_true hcap_lt; wp_steps
    have hcmn_out : ((x.msgPtr + 24#64) ↦₆₄ cap_ik) ∗ ((x.msgPtr + 32#64) ↦₆₄ ptr_ik) ∗ ((x.msgPtr + 40#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
          vecU8Buf A cap_ik ptr_ik auth.rootKey ∗ macCap ⊢
          authenticatorPBCapAt A (x.msgPtr + 0x18#64) rest.length auth := by
      change ((x.msgPtr + 24#64) ↦₆₄ cap_ik) ∗ ((x.msgPtr + 32#64) ↦₆₄ ptr_ik) ∗ ((x.msgPtr + 40#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
          vecU8Buf A cap_ik ptr_ik auth.rootKey ∗ macCap ⊢
          (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap rest.length⌝ ∗ vecU8At A (x.msgPtr + 0x18#64) cap ptr auth.rootKey) ∗ macCap
      refine Entails.trans (Entails.of_eq (show _ = (((x.msgPtr + 24#64) ↦₆₄ cap_ik) ∗ ((x.msgPtr + 32#64) ↦₆₄ ptr_ik) ∗ ((x.msgPtr + 40#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗ vecU8Buf A cap_ik ptr_ik auth.rootKey) ∗ macCap by ac_rfl)) ?_
      refine sepConj_mono_left ?_
      have hhdr : ((x.msgPtr + 24#64) ↦₆₄ cap_ik) ∗ ((x.msgPtr + 32#64) ↦₆₄ ptr_ik) ∗
          ((x.msgPtr + 40#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗ vecU8Buf A cap_ik ptr_ik auth.rootKey ⊢
          vecU8At A (x.msgPtr + 0x18#64) cap_ik ptr_ik auth.rootKey := by
        rw [vecU8At_eq_header_sep_buf, vecHeader]; simp only [bv64_add24_add8, bv64_add24_add16]; sep_entail
      refine Entails.trans hhdr ?_
      refine Entails.trans ?_ (Entails.sepExists_intro cap_ik); refine Entails.trans ?_ (Entails.sepExists_intro ptr_ik)
      exact Entails.pure_right hcap_ik (Entails.refl _)
    apply SepWP.fold hcmn_out (by sep_focus); wp_reach
    apply SepWPpLscro.weaken_pre (P' := vecU8CapAt A x.msgPtr rest.length uc.dk ∗ authenticatorPBCapAt A (x.msgPtr + 0x18#64) rest.length auth ∗ ((x.msgPtr + 0x48#64) ↦₆₄ uc.epoch) ∗ optPolynomialEncoderPBAt A (x.msgPtr + 80#64) sendingEk ∗ optPolynomialDecoderPBAt A (x.msgPtr + 136#64) receivingCt1 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedInlSavedRegs10 s0.sp s0 ∗ (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool)
      (by sep_entail)
    exact hcont _ (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm, hrun]) (by simp (config := { failIfUnchanged := false }) only [arm64_norm, hsp])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm]) (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm]) (by simp (config := { failIfUnchanged := false }) only [arm64_norm, hx20])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm]) (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm, hx23]) (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm]) (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
      ⟨by simp (config := { failIfUnchanged := false }) only [arm64_norm, hx27],
       by simp (config := { failIfUnchanged := false }) only [arm64_norm, hx28],
       by simp (config := { failIfUnchanged := false }) only [arm64_norm, hvregs]⟩

theorem chunkedHeaderSent_uc_tag2_step_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    (hAuthCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A)))
    {x : ChunkedHeaderSentMergeGhost} {R : SepProp} {s0 s : State} {uc : V1State.Unchunked.EkSent} {sendingEk : Option PolynomialEncoder}
    {receivingCt1 : Option PolynomialDecoder} {rest : List (BitVec 8)} {iwt : WireType} {outerLimit innerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length) (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_auth : (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto iwt) (uc.auth.getD default) rest 97).toOption = none →
      (Proto.mergeMessage V1State.Chunked.HeaderSent.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (auth' : ProtoAuthenticator) (rest' : List (BitVec 8)) (s' : State),
      (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto iwt) (uc.auth.getD default) rest 97).toOption = some (auth', rest') →
      s'.pc = (blkPl_302).base + 464#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace → s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit → ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s'
        (chunkedHeaderSentUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { uc with auth := some auth' } sendingEk receivingCt1 x.bs rest')
        (WppPost (chunkedHeaderSentMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_302).base + 560#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s
      (chunkedHeaderSentUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr uc sendingEk receivingCt1 x.bs rest)
      (WppPost (chunkedHeaderSentMergeSpec A) x R s0) (WppPanic R s0) := by
  refine chunkedHeaderSent_uc_auth_init_placed ?_ hpc hrun hsp hx20 hx23 hcs
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hcs1
  rw [htr] at htr1; rw [hx0] at hx0_1; rw [hx19] at hx19_1; rw [hx21] at hx21_1
  rw [hx22] at hx22_1; rw [hx24] at hx24_1; rw [hx25] at hx25_1; rw [hx26] at hx26_1
  obtain ⟨hx27_1, hx28_1, hvregs_1⟩ := hcs1
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hfpush := fun (auth' : ProtoAuthenticator) =>
    @chunkedHeaderSent_uc_field_push_exit_placed _ A H hPushCall x R s0 { uc := some { uc with auth := some auth' }, sendingEk := sendingEk, receivingCt1 := receivingCt1 }
  apply SepWPpLscro.of_sepWP (mid := lsmpl.base 295)
  conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, chunkedInlBelow_authMerge s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpLscro.call_frame_lscro (x := ⟨iwt, x.msgPtr + 0x18#64, uc.auth.getD default, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := entry + 596#64) hAuthCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
    (by simp only [State.spAligned, hsp1, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [authMergeSpec]; simp only [arm64_norm, hsp1, hx0_1, hx20_1, hx19_1, setWidth8_ofNat64_wt]; rfl)
    hrest_lt (by sep_focus) (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [authMergeSpec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr1]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
  cases hauth_res : (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto iwt) (uc.auth.getD default) rest 97).toOption with
  | none =>
    have hnone := hnone_of_auth hauth_res
    apply SepWPpLscro.of_sepWP (mid := entry + 1072#64); (conv => arg 4; simp only [authMergeSpec, hauth_res, memRegion_48_cells1_160 s0.sp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp1])
    apply SepWP.exists_elim; intro v_stk0; apply SepWP.exists_elim; intro auth'; apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hn_err⟩
    have hcbz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (chunkedInlBelow_authMerge_entails s0.sp) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (vecU8CapAt_entails_vecU8' A x.msgPtr rest.length uc.dk) (by sep_focus); wp_steps; wp_reach
    apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedHeaderSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some { uc with auth := some auth' }, sendingEk := sendingEk, receivingCt1 := receivingCt1 } x.bs)
      (by dsimp only [chunkedHeaderSentErrFrame, chunkedHeaderSentPBAt, optEkSentPBAt, ekSentPBAt, unchunked3At, optAuthenticatorPBAt]; sep_entail)
    exact hfpush auth' hnone hn_err hsm0 hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr1]) (by simp only [arm64_norm, hspm]) ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨auth', rest'⟩
    have hrest'_le : rest'.length ≤ rest.length := (proto_mergeMessage_suffix hauth_res).1
    apply SepWPpLscro.of_sepWP (mid := entry + 464#64); (conv => arg 4; simp only [authMergeSpec, hauth_res, sepConj_assoc, arm64_norm, hsp1])
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩; apply SepWP.fold (chunkedInlBelow_authMerge_entails s0.sp) (by sep_focus)
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (vecU8CapAt_mono' A x.msgPtr uc.dk hrest'_le) (by sep_focus); wp_steps; wp_reach
    apply SepWPpLscro.weaken_pre (P' := chunkedHeaderSentUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { uc with auth := some auth' } sendingEk receivingCt1 x.bs rest')
      (by dsimp only [chunkedHeaderSentUcLoopPre]; rw [unchunked3CapAt_eq]; dsimp only [optAuthenticatorPBCapAt]; sep_entail)
    exact hcont auth' rest' _ hauth_res
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr1])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
      (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m]) (by simp only [arm64_norm, hx25_m]) (by simp only [arm64_norm, hx26_m])
      ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

theorem chunkedHeaderSent_uc_tag3_step_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    (hBytesCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A)))
    {x : ChunkedHeaderSentMergeGhost} {R : SepProp} {s0 s : State} {uc : V1State.Unchunked.EkSent} {sendingEk : Option PolynomialEncoder}
    {receivingCt1 : Option PolynomialDecoder} {rest : List (BitVec 8)} {iwt : WireType} {outerLimit innerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest) (hnone_of_mb : mergeBytes iwt rest = none →
      (Proto.mergeMessage V1State.Chunked.HeaderSent.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (v rest' : List (BitVec 8)) (s' : State),
      mergeBytes iwt rest = some (v, rest') → s'.pc = (blkPl_302).base + 464#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace → s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit → ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s'
        (chunkedHeaderSentUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { uc with dk := v } sendingEk receivingCt1 x.bs rest')
        (WppPost (chunkedHeaderSentMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_302).base + 440#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s
      (chunkedHeaderSentUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr uc sendingEk receivingCt1 x.bs rest)
      (WppPost (chunkedHeaderSentMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hfpush := @chunkedHeaderSent_uc_field_push_exit_placed _ A H hPushCall x R s0 { uc := some uc, sendingEk := sendingEk, receivingCt1 := receivingCt1 }
  apply SepWPpLscro.of_sepWP (mid := lsmpl.base 290)
  conv => arg 4; rw [chunkedHeaderSentUcLoopPre, unchunked3CapAt_eq, vecU8CapAt, sliceCursorAfter_eq_split hrest_le hrest_suf, chunkedInlBelow_bytesMerge3 s0.sp]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWP.exists_elim; intro cap1; apply SepWP.exists_elim; intro ptr1; apply SepWP.pure_elim; intro hcap1; wp_steps; wp_reach
  refine SepWPpLscro.call_frame_lscro (x := ⟨iwt, x.msgPtr, cap1, ptr1, uc.dk, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := entry + 452#64) hBytesCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [bytesMerge3RawSpec]; simp only [arm64_norm, hsp, hx0, hx19, hx20, setWidth8_ofNat64_wt]; rfl)
    (⟨hrest_lt, hcap1⟩ : rest.length < 2 ^ 63 ∧ BytesMergeCapOk cap1 rest.length) (by sep_focus) (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [bytesMerge3RawSpec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
  cases hmb : mergeBytes iwt rest with
  | none =>
    have hnone := hnone_of_mb hmb
    apply SepWPpLscro.of_sepWP (mid := entry + 1072#64); (conv => arg 4; simp only [bytesMerge3RawSpec, hmb, memRegion_48_cells1_160 s0.sp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp])
    apply SepWP.exists_elim; intro v_stk0; apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (chunkedInlBelow_bytesMerge3_entails s0.sp) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (vecU8At_entails_rustBytesVecAt A x.msgPtr cap1 ptr1 uc.dk) (by sep_focus)
    apply SepWP.fold (optAuthenticatorPBCapAt_entails_optAuthenticatorPBAt A (x.msgPtr + 0x18#64) rest.length uc.auth) (by sep_focus); wp_steps; wp_reach
    apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedHeaderSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc, sendingEk := sendingEk, receivingCt1 := receivingCt1 } x.bs)
      (by dsimp only [chunkedHeaderSentErrFrame, chunkedHeaderSentPBAt, optEkSentPBAt, ekSentPBAt, unchunked3At]; sep_entail)
    exact hfpush hnone (by decide : 0 ≤ 1) hsm0 hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm, hspm]) ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨v, rest'⟩
    have hrest'_le : rest'.length ≤ rest.length := mergeBytes_length hmb
    apply SepWPpLscro.of_sepWP (mid := entry + 464#64); (conv => arg 4; simp only [bytesMerge3RawSpec, hmb, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp])
    apply SepWP.exists_elim; intro cap1'; apply SepWP.exists_elim; intro ptr1'; apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hcap1'⟩
    apply SepWP.fold (chunkedInlBelow_bytesMerge3_entails s0.sp) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (vecU8At_entails_vecU8CapAt A x.msgPtr cap1' ptr1' rest'.length v hcap1') (by sep_focus)
    apply SepWP.fold (optAuthenticatorPBCapAt_mono A (x.msgPtr + 0x18#64) uc.auth hrest'_le) (by sep_focus); wp_steps; wp_reach
    apply SepWPpLscro.weaken_pre (P' := chunkedHeaderSentUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { uc with dk := v } sendingEk receivingCt1 x.bs rest')
      (by dsimp only [chunkedHeaderSentUcLoopPre]; rw [unchunked3CapAt_eq]; sep_entail)
    exact hcont v rest' _ hmb (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
      (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m]) (by simp only [arm64_norm, hx25_m]) (by simp only [arm64_norm, hx26_m])
      ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

theorem chunkedHeaderSent_uc_loop_le_exit_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 261) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    {x : ChunkedHeaderSentMergeGhost} {R : SepProp} {s0 s : State} {uc : V1State.Unchunked.EkSent} {sendingEk : Option PolynomialEncoder}
    {receivingCt1 : Option PolynomialDecoder} {cur : List (BitVec 8)} {outerLimit innerLimit : Nat}
    (hle_lim : cur.length ≤ innerLimit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_suf : IsDropSuffix x.bs cur) (hlim_lt : innerLimit < 2 ^ 63) (hnone_of_lt : cur.length < innerLimit →
      (Proto.mergeMessage V1State.Chunked.HeaderSent.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none) (hcont_eq : ∀ s' : State,
      cur.length = innerLimit → s'.pc = (blkPl_302).base + 168#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace → s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 25#5) = 8#64 → ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s' (chunkedHeaderSentLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr
          { uc := some uc, sendingEk := sendingEk, receivingCt1 := receivingCt1 } x.bs cur) (WppPost (chunkedHeaderSentMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_302).base + 464#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s
      (chunkedHeaderSentUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr uc sendingEk receivingCt1 x.bs cur)
      (WppPost (chunkedHeaderSentMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  have hfrom_push := @chunkedHeaderSent_uc_from_push_exit_placed _ A H hFromCall hPushCall x R s0 { uc := some uc, sendingEk := sendingEk, receivingCt1 := receivingCt1 }
  by_cases heq_lim : cur.length = innerLimit
  · obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq heq_lim
    apply SepWPpLscro.of_sepWP (mid := entry + 168#64)
    conv => arg 4; rw [chunkedHeaderSentUcLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt]
    simp only [sepConj_assoc]
    wp_steps; apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus); wp_reach
    apply SepWPpLscro.weaken_pre (P' := chunkedHeaderSentLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc, sendingEk := sendingEk, receivingCt1 := receivingCt1 } x.bs cur)
      (by dsimp only [chunkedHeaderSentLoopPre, chunkedHeaderSentPBCapAt, optEkSentPBCapAt, sliceCursorAfter]; sep_entail)
    exact hcont_eq _ heq_lim (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr])
      (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20]) (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22])
      (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24]) (by simp only [arm64_norm, hx25])
      ⟨by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩
  · have hlt_lim : cur.length < innerLimit := Nat.lt_of_le_of_ne hle_lim heq_lim
    obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_lt hlt_lim hlim_lt
    have hnone := hnone_of_lt hlt_lim
    apply SepWPpLscro.of_sepWP (mid := entry + 780#64)
    conv => arg 4; rw [chunkedHeaderSentUcLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt, memRegion_48_cells1_160 s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v_stk0; wp_steps; apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot curPtr (BitVec.ofNat 64 cur.length)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    apply SepWP.fold (unchunked3CapAt_entails_chunkedHeaderSentPBAt A x.msgPtr cur.length uc sendingEk receivingCt1) (by sep_focus); wp_reach
    apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000008#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedHeaderSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc, sendingEk := sendingEk, receivingCt1 := receivingCt1 } x.bs)
      (by dsimp only [chunkedHeaderSentErrFrame]; sep_entail)
    exact hfrom_push hnone (by decide : KindNoHeap 0x8000000000000008#64) hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr])
      ⟨by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩

theorem chunkedHeaderSent_uc_decode_key_step_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 261) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 291) (decodeVarint2Spec A))
    {x : ChunkedHeaderSentMergeGhost} {R : SepProp} {s0 s : State} {uc : V1State.Unchunked.EkSent} {sendingEk : Option PolynomialEncoder}
    {receivingCt1 : Option PolynomialDecoder} {cur : List (BitVec 8)} {outerLimit innerLimit : Nat}
    (hgt_lim : ¬ cur.length ≤ innerLimit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_lt : cur.length < 2 ^ 63) (hcur_suf : IsDropSuffix x.bs cur) (hnone_of_loop_none :
      mergeLoopBin V1State.Unchunked.EkSent.mergeField (cur.length - innerLimit) uc cur innerLimit 97 = none →
      (Proto.mergeMessage V1State.Chunked.HeaderSent.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (key : BitVec 64) (iwt : WireType) (rest : List (BitVec 8)) (s' : State),
      decodeVarint cur = some (key, rest) → ¬ 2 ^ 32 ≤ key.toNat →
      WireType.ofNat? (key.toNat % 8) = some iwt → ¬ key.toNat / 8 < 1 →
      s'.pc = (blkPl_302).base + 516#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace → s'.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) → s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit → ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s'
        (chunkedHeaderSentUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr uc sendingEk receivingCt1 x.bs rest)
        (WppPost (chunkedHeaderSentMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_302).base + 464#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s
      (chunkedHeaderSentUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr uc sendingEk receivingCt1 x.bs cur)
      (WppPost (chunkedHeaderSentMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  have hpush_exit := @chunkedHeaderSent_uc_push_exit_placed _ A H hPushCall x R s0 { uc := some uc, sendingEk := sendingEk, receivingCt1 := receivingCt1 }
  have hfrom_push := @chunkedHeaderSent_uc_from_push_exit_placed _ A H hFromCall hPushCall x R s0 { uc := some uc, sendingEk := sendingEk, receivingCt1 := receivingCt1 }
  apply SepWPpLscro.of_sepWP (mid := lsmpl.base 291)
  conv => arg 4; rw [chunkedHeaderSentUcLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt, chunkedInlBelow_decodeVarint2 s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpLscro.call_frame (x := ⟨x.bufRef, x.slot, curPtr, cur⟩)
    (ret_pc := entry + 484#64) hVarintCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, hsp, hx19]; rfl)
    hcur_lt (by dsimp only [sliceCursorAt, curPtr]; sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
  cases hd : decodeVarint cur with
  | none =>
    have hnone := hnone_of_loop_none (mergeLoopBin_of_decodeVarint_none protoPrefixStep_unchunked_ekSent_mergeField hgt_lim hd)
    apply SepWPpLscro.of_sepWP (mid := entry + 792#64)
    (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
    apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    apply SepWP.fold (unchunked3CapAt_entails_chunkedHeaderSentPBAt A x.msgPtr cur.length uc sendingEk receivingCt1) (by sep_focus); wp_steps; wp_reach
    apply SepWPpLscro.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedHeaderSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc, sendingEk := sendingEk, receivingCt1 := receivingCt1 } x.bs)
      (by dsimp only [chunkedHeaderSentErrFrame]; sep_entail)
    exact hpush_exit hnone (by decide : 0 ≤ 2) hsm1 hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm]) ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨key, rest⟩
    have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd; have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
    have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le; have hrest_suf : IsDropSuffix x.bs rest := suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
    let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
    by_cases hk_ge : 2 ^ 32 ≤ key.toNat
    · have hnone := hnone_of_loop_none (mergeLoopBin_of_key_ge protoPrefixStep_unchunked_ekSent_mergeField hgt_lim hd hk_ge)
      have hshr := key_shr32_of_ge hk_ge; apply SepWPpLscro.of_sepWP (mid := entry + 780#64)
      (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
      apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
      apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
      apply SepWP.fold (unchunked3CapAt_entails_chunkedHeaderSentPBAt A x.msgPtr cur.length uc sendingEk receivingCt1) (by sep_focus)
      conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_cells2_160 s0.sp]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply SepWP.exists_elim; intro v_err0; apply SepWP.exists_elim; intro v_err1; wp_steps
      apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
      apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
      have h40 : ((s0.sp - 128#64 + 8#64) ↦₆₄ key) ∗ memRegion (s0.sp - 112#64) 32 ⊢ memRegion (s0.sp - 120#64) 40 := by
        rw [bv_sub_add_lit s0.sp 128 8]; exact cells2_memRegion32_entails_40_160 s0.sp key
      apply SepWP.fold h40 (by sep_focus); wp_reach
      apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000004#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedHeaderSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc, sendingEk := sendingEk, receivingCt1 := receivingCt1 } x.bs)
        (by dsimp only [chunkedHeaderSentErrFrame]; sep_entail)
      exact hfrom_push hnone (by decide : KindNoHeap 0x8000000000000004#64) hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
        ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
    · have hshr := key_shr32_of_lt hk_ge
      cases hwt : WireType.ofNat? (key.toNat % 8) with
      | none =>
        have hnone := hnone_of_loop_none (mergeLoopBin_of_wt_none protoPrefixStep_unchunked_ekSent_mergeField hgt_lim hd hk_ge hwt)
        obtain ⟨hcs1, hcs2⟩ := key_wt_none hwt
        apply SepWPpLscro.of_sepWP (mid := entry + 780#64); (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
        apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
        apply SepWP.fold (unchunked3CapAt_entails_chunkedHeaderSentPBAt A x.msgPtr cur.length uc sendingEk receivingCt1) (by sep_focus)
        conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_cells2_160 s0.sp]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]; apply SepWP.exists_elim; intro v_err0; apply SepWP.exists_elim; intro v_err1; wp_steps
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        have h40 : ((s0.sp - 128#64 + 8#64) ↦₆₄ (key &&& 7#64)) ∗ memRegion (s0.sp - 112#64) 32 ⊢ memRegion (s0.sp - 120#64) 40 := by
          rw [bv_sub_add_lit s0.sp 128 8]; exact cells2_memRegion32_entails_40_160 s0.sp (key &&& 7#64)
        apply SepWP.fold h40 (by sep_focus); wp_reach
        apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000003#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedHeaderSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc, sendingEk := sendingEk, receivingCt1 := receivingCt1 } x.bs)
          (by dsimp only [chunkedHeaderSentErrFrame]; sep_entail)
        exact hfrom_push hnone (by decide : KindNoHeap 0x8000000000000003#64) hsp_align
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
          ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
      | some iwt =>
        obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt; obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_ge
        obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
        by_cases hitag0 : key.toNat / 8 < 1
        · have hnone := hnone_of_loop_none (mergeLoopBin_of_tag_zero protoPrefixStep_unchunked_ekSent_mergeField hgt_lim hd hk_ge hwt hitag0)
          have htag_zero : key.toNat / 8 = 0 := by omega
          apply SepWPpLscro.of_sepWP (mid := entry + 780#64); (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
          apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩; apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          apply SepWP.fold (unchunked3CapAt_entails_chunkedHeaderSentPBAt A x.msgPtr cur.length uc sendingEk receivingCt1) (by sep_focus)
          conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_cells1_160 s0.sp]
          simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]; apply SepWP.exists_elim; intro v_err0; wp_steps
          apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
          apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus); wp_reach
          apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000005#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedHeaderSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc, sendingEk := sendingEk, receivingCt1 := receivingCt1 } x.bs)
            (by dsimp only [chunkedHeaderSentErrFrame]; sep_entail)
          exact hfrom_push hnone (by decide : KindNoHeap 0x8000000000000005#64) hsp_align
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
            ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
        · obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_ge hitag0
          have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
            rw [beq_eq_false_iff_ne]; intro h; have h1 := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1; omega
          apply SepWPpLscro.of_sepWP (mid := entry + 516#64); (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
          apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          apply SepWP.fold (unchunked3CapAt_mono A x.msgPtr uc.epoch uc.auth uc.dk hrest_le_cur) (by sep_focus); wp_steps; wp_reach
          apply SepWPpLscro.weaken_pre (P' := chunkedHeaderSentUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr uc sendingEk receivingCt1 x.bs rest)
            (by dsimp only [chunkedHeaderSentUcLoopPre]; sep_entail)
          exact hcont key iwt rest _ hd hk_ge hwt hitag0
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
            (by simp only [arm64_norm, hsm1, hand_wt]) (by simp only [arm64_norm, hsm1, hw1, hw1_2, hw1_zext1, hw1_zext2])
            (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
            (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m]) (by simp only [arm64_norm, hx25_m]) (by simp only [arm64_norm, hx26_m])
            ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

theorem chunkedHeaderSent_uc_loop_ok_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 261) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 291) (decodeVarint2Spec A))
    (hSkipCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 263) (skipField3Spec A))
    (hBytesCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A)))
    (hAuthCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A)))
    {x : ChunkedHeaderSentMergeGhost} {R : SepProp} {s0 : State} (sendingEk : Option PolynomialEncoder) (receivingCt1 : Option PolynomialDecoder)
    (outerLimit innerLimit : Nat) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hbs_lt : x.bs.length < 2 ^ 63) (hlim_lt : innerLimit < 2 ^ 63) :
    ∀ (n : Nat) (uc : V1State.Unchunked.EkSent) (cur : List (BitVec 8)) (s : State),
      cur.length ≤ n → cur.length ≤ x.bs.length → IsDropSuffix x.bs cur → (∀ (uc' : V1State.Unchunked.EkSent) (rest' : List (BitVec 8)) (s' : State),
        rest'.length = innerLimit → rest'.length ≤ x.bs.length → IsDropSuffix x.bs rest' →
        mergeLoopBin V1State.Unchunked.EkSent.mergeField (cur.length - innerLimit) uc cur innerLimit 97 = some uc' →
        s'.pc = (blkPl_302).base + 168#64 →
        s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace → s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
        s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
        s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 25#5) = 8#64 →
        ChunkedInl10CalleeSaved s0 s' → SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s'
          (chunkedHeaderSentLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc', sendingEk := sendingEk, receivingCt1 := receivingCt1 } x.bs rest')
          (WppPost (chunkedHeaderSentMergeSpec A) x R s0) (WppPanic R s0)) →
      (mergeLoopBin V1State.Unchunked.EkSent.mergeField (cur.length - innerLimit) uc cur innerLimit 97 = none →
        (Proto.mergeMessage V1State.Chunked.HeaderSent.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none) →
      s.pc = (blkPl_302).base + 464#64 →
      s.status = .Running → s.sp = s0.sp - 128#64 → s.trace = s0.trace → s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s.readReg64 (Reg.gpr 23#5) = 1#64 → s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s.readReg64 (Reg.gpr 25#5) = 8#64 → s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit → ChunkedInl10CalleeSaved s0 s →
      SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s
        (chunkedHeaderSentUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr uc sendingEk receivingCt1 x.bs cur)
        (WppPost (chunkedHeaderSentMergeSpec A) x R s0) (WppPanic R s0) := by
  have htag1_varint := fun {s uc rest} =>
    @chunkedHeaderSent_uc_tag1_varint_step_placed _ A H hPushCall hVarintCall x R s0 s uc sendingEk receivingCt1 rest outerLimit innerLimit
  have htag1_wt_err := fun {s uc rest} =>
    @chunkedHeaderSent_uc_tag1_wt_err_step_placed _ A H hFromCall hPushCall x R s0 s uc sendingEk receivingCt1 rest
  have htag2_step := fun {s uc rest} (iwt : WireType) =>
    @chunkedHeaderSent_uc_tag2_step_placed _ A H hPushCall hAuthCall x R s0 s uc sendingEk receivingCt1 rest iwt outerLimit innerLimit
  have htag3_step := fun {s uc rest} (iwt : WireType) =>
    @chunkedHeaderSent_uc_tag3_step_placed _ A H hPushCall hBytesCall x R s0 s uc sendingEk receivingCt1 rest iwt outerLimit innerLimit
  have hskip_step := fun {s uc rest} (iwt : WireType) (tag : Nat) =>
    @chunkedHeaderSent_uc_skip_step_placed _ A H hPushCall hSkipCall x R s0 s uc sendingEk receivingCt1 rest iwt tag outerLimit innerLimit
  intro n; induction n with
  | zero =>
    intro uc cur s hcur_n hcur_le hcur_suf hcont_ok hnone_loop hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
    exact chunkedHeaderSent_uc_loop_le_exit_placed hFromCall hPushCall (by omega) hsp_align hcur_le hcur_suf hlim_lt
      (fun hlt => hnone_loop (mergeLoopBin_lt_limit _ _ _ _ _ _ hlt)) (fun s' heq => hcont_ok uc cur s' heq hcur_le hcur_suf (mergeLoopBin_eq_limit _ _ _ _ _ _ heq))
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
  | succ n ih =>
    intro uc cur s hcur_n hcur_le hcur_suf hcont_ok hnone_loop hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
    by_cases hle_lim : cur.length ≤ innerLimit
    · exact chunkedHeaderSent_uc_loop_le_exit_placed hFromCall hPushCall hle_lim hsp_align hcur_le hcur_suf hlim_lt
        (fun hlt => hnone_loop (mergeLoopBin_lt_limit _ _ _ _ _ _ hlt))
        (fun s' heq => hcont_ok uc cur s' heq hcur_le hcur_suf (mergeLoopBin_eq_limit _ _ _ _ _ _ heq))
        hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
    · have hcur_lt : cur.length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
      refine chunkedHeaderSent_uc_decode_key_step_placed hFromCall hPushCall hVarintCall hle_lim hsp_align
        hcur_le hcur_lt hcur_suf hnone_loop ?_ hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
      intro key iwt rest s' hd hk_ge hwt hitag0 hpc' hrun' hsp' htr' hx0' hx1' hx19' hx20' hx21' hx22' hx23' hx24' hx25' hx26' hcs'
      obtain ⟨hx27', hx28', hvregs'⟩ := hcs'; have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd; have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
      have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le; have hrest_lt : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest_le hbs_lt
      have hrest_suf : IsDropSuffix x.bs rest := suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd); have htag_lt : key.toNat / 8 < 2 ^ 32 := by omega
      have hstep := mergeLoopBin_of_key_ok (m := uc) (depth' := 97) protoPrefixStep_unchunked_ekSent_mergeField hle_lim hd hk_ge hwt hitag0
      by_cases htag1 : key.toNat / 8 = 1
      · rw [htag1] at hx1' hstep; rw [unchunkedEkSent_mergeField_tag1] at hstep
        apply SepWPpLscro.of_sepWP (mid := entry + 604#64); wp_steps; wp_reach
        by_cases hiwt : iwt = .varint
        · subst hiwt
          refine htag1_varint hsp_align hrest_le hrest_lt hrest_suf (fun hdv_none => hnone_loop (by rw [hstep]; simp [hdv_none]))
            (fun v rest' s'' hdv_some hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs'' => ?_)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
            (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20']) (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23'])
            (by simp only [arm64_norm, hx24']) (by simp only [arm64_norm, hx25']) (by simp only [arm64_norm, hx26']) ⟨by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩
          have hr'_lt : rest'.length < rest.length := decodeVarint_length hdv_some; have hr'_le : rest'.length ≤ rest.length := Nat.le_of_lt hr'_lt
          exact ih { uc with epoch := v } rest' s'' (by omega) (Nat.le_trans hr'_le hrest_le) (suffix_trans hrest_le hrest_suf hr'_le (decodeVarint_suffix hdv_some))
            (fun uc' r' sf hr_eq hr_le hr_suf hml => hcont_ok uc' r' sf hr_eq hr_le hr_suf (by rw [hstep]; simpa [hdv_some] using hml))
            (fun hml => hnone_loop (by rw [hstep]; simpa [hdv_some] using hml))
            hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs''
        · exact htag1_wt_err hiwt hsp_align hrest_le hrest_suf (hnone_loop (by rw [hstep]; simp [hiwt]))
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
            (by simp only [arm64_norm, hx0']) ⟨by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩
      · by_cases htag2 : key.toNat / 8 = 2
        · obtain ⟨hb1_1, _⟩ := itag_beq_tag_false htag1 htag_lt (by decide : 1 < 2 ^ 32)
          have hb1_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 1#32) = false := by rw [sf_truncate32_ofNat64]; exact hb1_1
          rw [htag2] at hx1' hstep; rw [unchunkedEkSent_mergeField_tag2] at hstep
          apply SepWPpLscro.of_sepWP (mid := entry + 560#64); wp_steps; wp_reach
          refine htag2_step iwt hsp_align hrest_le hrest_lt hrest_suf (fun hauth_none => hnone_loop (by rw [hstep, hauth_none]; rfl))
            (fun auth' rest' s'' hauth_some hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs'' => ?_)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
            (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20']) (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23'])
            (by simp only [arm64_norm, hx24']) (by simp only [arm64_norm, hx25']) (by simp only [arm64_norm, hx26']) ⟨by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩
          have hr'_le : rest'.length ≤ rest.length := (proto_mergeMessage_suffix hauth_some).1
          exact ih { uc with auth := some auth' } rest' s'' (by omega) (Nat.le_trans hr'_le hrest_le)
            (suffix_trans hrest_le hrest_suf hr'_le (proto_mergeMessage_suffix hauth_some).2)
            (fun uc' r' sf hr_eq hr_le hr_suf hml => hcont_ok uc' r' sf hr_eq hr_le hr_suf (by rw [hstep, hauth_some]; exact hml))
            (fun hml => hnone_loop (by rw [hstep, hauth_some]; exact hml))
            hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs''
        · by_cases htag3 : key.toNat / 8 = 3
          · rw [htag3] at hx1' hstep; rw [unchunkedEkSent_mergeField_tag3] at hstep
            apply SepWPpLscro.of_sepWP (mid := entry + 440#64); wp_steps; wp_reach
            refine htag3_step iwt hsp_align hrest_le hrest_lt hrest_suf (fun hmb_none => hnone_loop (by rw [hstep, hmb_none]; rfl))
              (fun v rest' s'' hmb_some hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs'' => ?_)
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
              (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
              (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23'])
              (by simp only [arm64_norm, hx24']) (by simp only [arm64_norm, hx25']) (by simp only [arm64_norm, hx26']) ⟨by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩
            have hr'_le : rest'.length ≤ rest.length := mergeBytes_length hmb_some
            exact ih { uc with dk := v } rest' s'' (by omega) (Nat.le_trans hr'_le hrest_le) (suffix_trans hrest_le hrest_suf hr'_le (mergeBytes_suffix hmb_some))
              (fun uc' r' sf hr_eq hr_le hr_suf hml => hcont_ok uc' r' sf hr_eq hr_le hr_suf (by rw [hstep, hmb_some]; exact hml))
              (fun hml => hnone_loop (by rw [hstep, hmb_some]; exact hml))
              hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs''
          · obtain ⟨hb1_1, _⟩ := itag_beq_tag_false htag1 htag_lt (by decide : 1 < 2 ^ 32)
            obtain ⟨hb2_1, _⟩ := itag_beq_tag_false htag2 htag_lt (by decide : 2 < 2 ^ 32)
            obtain ⟨hb3_1, _⟩ := itag_beq_tag_false htag3 htag_lt (by decide : 3 < 2 ^ 32)
            have hb1_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 1#32) = false := by rw [sf_truncate32_ofNat64]; exact hb1_1
            have hb2_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 2#32) = false := by rw [sf_truncate32_ofNat64]; exact hb2_1
            have hb3_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 3#32) = false := by rw [sf_truncate32_ofNat64]; exact hb3_1
            rw [unchunkedEkSent_mergeField_other uc iwt rest 97 htag_lt htag1 htag2 htag3] at hstep
            apply SepWPpLscro.of_sepWP (mid := entry + 540#64); wp_steps; wp_reach
            refine hskip_step iwt (key.toNat / 8) hsp_align hrest_le hrest_lt hrest_suf htag_lt (fun hsf_none => hnone_loop (by rw [hstep, hsf_none]; rfl))
              (fun rest' s'' hsf_some hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs'' => ?_)
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
              (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx1', sf_truncate32_ofNat64]) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
              (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23'])
              (by simp only [arm64_norm, hx24']) (by simp only [arm64_norm, hx25']) (by simp only [arm64_norm, hx26']) ⟨by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩
            have hr'_le : rest'.length ≤ rest.length := (skip_length (2 * rest.length + 2)).1 _ _ _ _ _ hsf_some
            exact ih uc rest' s'' (by omega) (Nat.le_trans hr'_le hrest_le)
              (suffix_trans hrest_le hrest_suf hr'_le ((skip_suffix (2 * rest.length + 2)).1 _ _ _ _ _ hsf_some))
              (fun uc' r' sf hr_eq hr_le hr_suf hml => hcont_ok uc' r' sf hr_eq hr_le hr_suf (by rw [hstep, hsf_some]; exact hml))
              (fun hml => hnone_loop (by rw [hstep, hsf_some]; exact hml))
              hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs''

end CryptoVerification.SpqrV1.Prost.MessageMerge

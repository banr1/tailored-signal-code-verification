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
# Inner `Unchunked.HeaderReceived` Merge & Exit Lemmas for `Chunked.HeaderReceived::merge` (`0x50bac`, Block `306`)

Proves the epilogue, decode-error exits, and inlined `Unchunked.HeaderReceived` field-merge loop
inside `prost::encoding::message::merge::<spqr::proto::pq_ratchet::v1_state::chunked::HeaderReceived, &mut &[u8]>`
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

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero chunkedHeaderReceivedMerge_fnOff

gen_decodes libsignalSessionCode_tree chunkedHeaderReceivedMergeBin [
  0x4b7b4 → 0x4bbb4
]

macro "chunkedHeaderReceivedMerge_fetches " b:term:max H:term:max k0:num len:num : tactic =>
  `(tactic| code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.SpqrV1.Prost.MessageMerge.chunkedHeaderReceivedMergeBin $b $H
    chunkedHeaderReceivedMerge_fnOff 0x4b7b4 $k0 $len)

/-! ## 1. Pure `mergeField` Step Lemmas and Helpers -/

theorem vecU8Buf_entails_cap_lt_hr (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8Buf A cap ptr bs ⊢ ⌜cap.toNat < 2 ^ 63⌝ ∗ vecU8Buf A cap ptr bs := by
  unfold vecU8Buf; refine Entails.pure_left fun h => Entails.pure_right h.2.1 (Entails.pure_right h (Entails.refl _))

theorem vecU8At_entails_header_cap_lt_hr (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A a cap ptr bs ⊢
      ⌜cap.toNat < 2 ^ 63⌝ ∗ (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ vecU8Buf A cap ptr bs := by
  rw [vecU8At_eq_header_sep_buf, vecHeader]
  refine Entails.trans (sepConj_mono_right (vecU8Buf_entails_cap_lt_hr A cap ptr bs)) (by sep_entail)

theorem header_buf_entails_vecU8At_hr (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      vecU8Buf A cap ptr bs ⊢ vecU8At A a cap ptr bs := by
  rw [vecU8At_eq_header_sep_buf, vecHeader]; sep_entail

@[irreducible] def vecU8CapAt_hr (A : RustAlloc) (a : BitVec 64) (bsLen : Nat) (bs : List (BitVec 8)) : SepProp :=
  ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap bsLen⌝ ∗ vecU8At A a cap ptr bs

theorem unchunked3CapAt_eq_hr (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (epoch : BitVec 64) (auth : Option ProtoAuthenticator) (v3 : List (BitVec 8)) :
    unchunked3CapAt A a bsLen epoch auth v3 =
      vecU8CapAt_hr A a bsLen v3 ∗ optAuthenticatorPBCapAt A (a + 0x18#64) bsLen auth ∗ ((a + 0x48#64) ↦₆₄ epoch) := by
  unfold vecU8CapAt_hr unchunked3CapAt; rfl

theorem vecU8CapAt_hr_mono (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) {m n : Nat} (hle : m ≤ n) :
    vecU8CapAt_hr A a n bs ⊢ vecU8CapAt_hr A a m bs := by
  unfold vecU8CapAt_hr; exact vecU8CapAt_mono A a bs hle

theorem vecU8CapAt_hr_entails_vecU8 (A : RustAlloc) (a : BitVec 64) (n : Nat) (bs : List (BitVec 8)) :
    vecU8CapAt_hr A a n bs ⊢ rustBytesVecAt A a bs := by
  unfold vecU8CapAt_hr; exact vecU8CapAt_entails_vecU8 A a n bs

def authMacKeyCapAt_hr (A : RustAlloc) (a : BitVec 64) (bsLen : Nat) (auth : ProtoAuthenticator) : SepProp :=
  ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap bsLen⌝ ∗ vecU8At A (a + 0x18#64) cap ptr auth.macKey

theorem authenticatorPBCapAt_entails_cmn_hr (A : RustAlloc) (a : BitVec 64) (bsLen : Nat) (auth : ProtoAuthenticator) :
    authenticatorPBCapAt A a bsLen auth ⊢
      ∃∗ cap_ik : BitVec 64, ∃∗ ptr_ik : BitVec 64,
        ⌜cap_ik.toNat < 2 ^ 63⌝ ∗ ⌜BytesMergeCapOk cap_ik bsLen⌝ ∗
        (a ↦₆₄ cap_ik) ∗ ((a + 8#64) ↦₆₄ ptr_ik) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
        vecU8Buf A cap_ik ptr_ik auth.rootKey ∗ authMacKeyCapAt_hr A a bsLen auth := by
  unfold authenticatorPBCapAt authMacKeyCapAt_hr
  rw [sepExists_sepConj_left]; refine ProofLib.Entails.sepExists_elim fun cap_ik => ?_
  rw [sepExists_sepConj_left]; refine ProofLib.Entails.sepExists_elim fun ptr_ik => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro cap_ik); refine Entails.trans ?_ (Entails.sepExists_intro ptr_ik)
  rw [sepConj_assoc]; refine Entails.pure_left fun hcap => ?_
  refine Entails.trans (sepConj_mono_left (vecU8At_entails_header_cap_lt_hr A a cap_ik ptr_ik auth.rootKey)) ?_
  simp only [sepConj_assoc]; exact Entails.pure_left fun hlt => Entails.pure_right hlt (Entails.pure_right hcap (Entails.refl _))

theorem cmn_entails_authenticatorPBCapAt_hr (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (auth : ProtoAuthenticator) (cap_ik ptr_ik : BitVec 64) (hcap : BytesMergeCapOk cap_ik bsLen) :
    (a ↦₆₄ cap_ik) ∗ ((a + 8#64) ↦₆₄ ptr_ik) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
      vecU8Buf A cap_ik ptr_ik auth.rootKey ∗ authMacKeyCapAt_hr A a bsLen auth ⊢
      authenticatorPBCapAt A a bsLen auth := by
  unfold authenticatorPBCapAt
  refine Entails.trans (Entails.of_eq (show _ = ((a ↦₆₄ cap_ik) ∗ ((a + 8#64) ↦₆₄ ptr_ik) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗ vecU8Buf A cap_ik ptr_ik auth.rootKey) ∗ authMacKeyCapAt_hr A a bsLen auth by ac_rfl)) ?_
  unfold authMacKeyCapAt_hr; refine sepConj_mono_left ?_
  refine Entails.trans (header_buf_entails_vecU8At_hr A a cap_ik ptr_ik auth.rootKey) ?_
  refine Entails.trans ?_ (Entails.sepExists_intro cap_ik); refine Entails.trans ?_ (Entails.sepExists_intro ptr_ik)
  exact Entails.pure_right hcap (Entails.refl _)

theorem decodeErrorWith_le3_hr (A : RustAlloc) (e : BitVec 64) {n : Nat} (hn : n ≤ 3) :
    decodeErrorAtStackLen A e n ⊢ ∃∗ k : Nat, ⌜k ≤ 3⌝ ∗ decodeErrorAtStackLen A e k := by
  refine Entails.trans ?_ (Entails.sepExists_intro n); rw [pure_sepConj_of_true hn]; exact Entails.refl _

theorem unchunkedHeaderReceived_mergeField_tag1 (m : V1State.Unchunked.HeaderReceived) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (V1State.Unchunked.HeaderReceived.mergeField m (BitVec.ofNat 32 1) (codecWireTypeToProto iwt) rest depth').toOption =
      if iwt = .varint then (decodeVarint rest).map (fun (v, rest') => ({ m with epoch := v }, rest')) else none := by
  unfold V1State.Unchunked.HeaderReceived.mergeField Proto.mergeUint64 Proto.checkWireType
  simp only [beq_self_eq_true, ↓reduceIte]
  by_cases h : iwt = .varint
  · subst h; have hdv := proto_decodeVarint_toOption rest
    rcases hp : Proto.decodeVarint rest with _ | ⟨v, rest'⟩ <;>
      { rw [hp] at hdv; dsimp [Except.toOption, Bind.bind, Except.bind] at hdv ⊢; rw [← hdv]; rfl }
  · cases iwt <;> first | contradiction | rfl

theorem unchunkedHeaderReceived_mergeField_tag2 (m : V1State.Unchunked.HeaderReceived) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (V1State.Unchunked.HeaderReceived.mergeField m (BitVec.ofNat 32 2) (codecWireTypeToProto iwt) rest depth').toOption =
      (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto iwt) (m.auth.getD default) rest depth').toOption.map
        (fun (v, rest') => ({ m with auth := some v }, rest')) := by
  unfold V1State.Unchunked.HeaderReceived.mergeField Proto.mergeOptMessage
  simp only [show (BitVec.ofNat 32 2 == 1#32) = false from rfl, show (BitVec.ofNat 32 2 == 2#32) = true from rfl, Bool.false_eq_true, ↓reduceIte]
  rcases Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto iwt) (m.auth.getD default) rest depth' with _ | ⟨v, r⟩ <;> rfl

theorem unchunkedHeaderReceived_mergeField_tag3 (m : V1State.Unchunked.HeaderReceived) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (V1State.Unchunked.HeaderReceived.mergeField m (BitVec.ofNat 32 3) (codecWireTypeToProto iwt) rest depth').toOption =
      (mergeBytes iwt rest).map (fun (v, rest') => ({ m with hdr := v }, rest')) := by
  unfold V1State.Unchunked.HeaderReceived.mergeField
  simp only [show (BitVec.ofNat 32 3 == 1#32) = false from rfl, show (BitVec.ofNat 32 3 == 2#32) = false from rfl,
    show (BitVec.ofNat 32 3 == 3#32) = true from rfl, Bool.false_eq_true, ↓reduceIte]
  have hmb := proto_mergeBytes_toOption (codecWireTypeToProto iwt) rest
  rw [protoWireTypeToCodec_codecWireTypeToProto] at hmb
  rcases hp : Proto.mergeBytes (codecWireTypeToProto iwt) rest with _ | ⟨v, rest'⟩ <;>
    { rw [hp] at hmb; dsimp [Except.toOption, Bind.bind, Except.bind] at hmb ⊢; rw [← hmb]; rfl }

theorem unchunkedHeaderReceived_mergeField_other (m : V1State.Unchunked.HeaderReceived) {tag : Nat} (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) (htag_lt : tag < 2 ^ 32) (hne1 : tag ≠ 1) (hne2 : tag ≠ 2) (hne3 : tag ≠ 3) :
    (V1State.Unchunked.HeaderReceived.mergeField m (BitVec.ofNat 32 tag) (codecWireTypeToProto iwt) rest depth').toOption =
      (skipField (2 * rest.length + 2) depth' tag iwt rest).map (fun rest' => (m, rest')) := by
  have hb1 : (BitVec.ofNat 32 tag == 1#32) = false := (itag_beq_tag_false hne1 htag_lt (by decide)).1
  have hb2 : (BitVec.ofNat 32 tag == 2#32) = false := (itag_beq_tag_false hne2 htag_lt (by decide)).1
  have hb3 : (BitVec.ofNat 32 tag == 3#32) = false := (itag_beq_tag_false hne3 htag_lt (by decide)).1
  have htag_toNat : (BitVec.ofNat 32 tag).toNat = tag := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htag_lt]
  unfold V1State.Unchunked.HeaderReceived.mergeField; simp only [hb1, hb2, hb3, Bool.false_eq_true, ↓reduceIte]
  have hsf' := proto_skipField_toOption (codecWireTypeToProto iwt) (BitVec.ofNat 32 tag) rest depth'
  rw [htag_toNat, protoWireTypeToCodec_codecWireTypeToProto] at hsf'
  rcases hsf : Proto.skipField (codecWireTypeToProto iwt) (BitVec.ofNat 32 tag) rest depth' with _ | rest' <;>
    { rw [hsf] at hsf'; dsimp [Except.toOption] at hsf'; rw [← hsf']; rfl }


theorem chunkedHeaderReceived_mergeField_tag1 (m : V1State.Chunked.HeaderReceived) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (V1State.Chunked.HeaderReceived.mergeField m (BitVec.ofNat 32 1) (codecWireTypeToProto iwt) rest depth').toOption =
      (Proto.mergeMessage V1State.Unchunked.HeaderReceived.mergeField (codecWireTypeToProto iwt) (m.uc.getD default) rest depth').toOption.map
        (fun (v, rest') => ({ m with uc := some v }, rest')) := by
  unfold V1State.Chunked.HeaderReceived.mergeField Proto.mergeOptMessage; simp only [beq_self_eq_true, ↓reduceIte]
  rcases Proto.mergeMessage V1State.Unchunked.HeaderReceived.mergeField (codecWireTypeToProto iwt) (m.uc.getD default) rest depth' with _ | ⟨v, r⟩ <;> rfl

theorem chunkedHeaderReceived_mergeField_tag2 (m : V1State.Chunked.HeaderReceived) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (V1State.Chunked.HeaderReceived.mergeField m (BitVec.ofNat 32 2) (codecWireTypeToProto iwt) rest depth').toOption =
      (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto iwt) (m.receivingEk.getD default) rest depth').toOption.map
        (fun (v, rest') => ({ m with receivingEk := some v }, rest')) := by
  unfold V1State.Chunked.HeaderReceived.mergeField Proto.mergeOptMessage
  simp only [show (BitVec.ofNat 32 2 == 1#32) = false from rfl, show (BitVec.ofNat 32 2 == 2#32) = true from rfl, Bool.false_eq_true, ↓reduceIte]
  rcases Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto iwt) (m.receivingEk.getD default) rest depth' with _ | ⟨v, r⟩ <;> rfl

theorem chunkedHeaderReceived_mergeField_other (m : V1State.Chunked.HeaderReceived) {tag : Nat} (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) (htag_lt : tag < 2 ^ 32) (hne1 : tag ≠ 1) (hne2 : tag ≠ 2) :
    (V1State.Chunked.HeaderReceived.mergeField m (BitVec.ofNat 32 tag) (codecWireTypeToProto iwt) rest depth').toOption =
      (skipField (2 * rest.length + 2) depth' tag iwt rest).map (fun rest' => (m, rest')) := by
  have hb1 : (BitVec.ofNat 32 tag == 1#32) = false := (itag_beq_tag_false hne1 htag_lt (by decide)).1
  have hb2 : (BitVec.ofNat 32 tag == 2#32) = false := (itag_beq_tag_false hne2 htag_lt (by decide)).1
  have htag_toNat : (BitVec.ofNat 32 tag).toNat = tag := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htag_lt]
  unfold V1State.Chunked.HeaderReceived.mergeField; simp only [hb1, hb2, Bool.false_eq_true, ↓reduceIte]
  have hsf' := proto_skipField_toOption (codecWireTypeToProto iwt) (BitVec.ofNat 32 tag) rest depth'
  rw [htag_toNat, protoWireTypeToCodec_codecWireTypeToProto] at hsf'
  rcases hsf : Proto.skipField (codecWireTypeToProto iwt) (BitVec.ofNat 32 tag) rest depth' with _ | rest' <;>
    { rw [hsf] at hsf'; dsimp [Except.toOption] at hsf'; rw [← hsf']; rfl }

/-! ## 2. Loop Preconditions and Shared Error Exits -/

def chunkedHeaderReceivedLoopPre (A : RustAlloc) (s0 : State) (msgPtr bufRef slot ptr : BitVec 64)
    (m : V1State.Chunked.HeaderReceived) (bs cur : List (BitVec 8)) : SepProp :=
  chunkedHeaderReceivedPBCapAt A msgPtr cur.length m ∗
    stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗
    chunkedInlSavedRegs10 s0.sp s0 ∗ (bufRef ↦₆₄ slot) ∗ sliceCursorAfter slot ptr bs cur ∗ A.pool

def chunkedHeaderReceivedUcLoopPre (A : RustAlloc) (s0 : State) (msgPtr bufRef slot ptr : BitVec 64)
    (ek : Option PolynomialDecoder) (uc : V1State.Unchunked.HeaderReceived) (bs cur : List (BitVec 8)) : SepProp :=
  unchunked3CapAt A msgPtr cur.length uc.epoch uc.auth uc.hdr ∗
    optPolynomialDecoderPBAt A (msgPtr + 80#64) ek ∗
    stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗
    chunkedInlSavedRegs10 s0.sp s0 ∗ (bufRef ↦₆₄ slot) ∗ sliceCursorAfter slot ptr bs cur ∗ A.pool

theorem unchunked3CapAt_entails_chunkedHeaderReceivedPBAt (A : RustAlloc) (a : BitVec 64)
    (n : Nat) (ek : Option PolynomialDecoder) (uc : V1State.Unchunked.HeaderReceived) :
    unchunked3CapAt A a n uc.epoch uc.auth uc.hdr ∗ optPolynomialDecoderPBAt A (a + 80#64) ek ⊢
      chunkedHeaderReceivedPBAt A a { uc := some uc, receivingEk := ek } :=
  sepConj_mono_left (unchunked3CapAt_entails_unchunked3At A a n uc.epoch uc.auth uc.hdr)

def chunkedHeaderReceivedErrFrame (A : RustAlloc) (s0 : State) (msgPtr bufRef slot ptr : BitVec 64)
    (m : V1State.Chunked.HeaderReceived) (bs : List (BitVec 8)) : SepProp :=
  chunkedInlSavedRegs10 s0.sp s0 ∗ chunkedHeaderReceivedPBAt A msgPtr m ∗
    (bufRef ↦₆₄ slot) ∗ memRegion slot 16 ∗ (ptr ↦ₛ bs) ∗ A.pool

theorem chunkedHeaderReceived_ret_err_exit {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    {x : ChunkedHeaderReceivedMergeGhost} {R : SepProp} {s0 : State} {m : V1State.Chunked.HeaderReceived} {s : State}
    {err : BitVec 64} {n : Nat}
    (hnone : (Proto.mergeMessage V1State.Chunked.HeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none) (hn : n ≤ 3) (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName + 128#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = err) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
      (decodeErrorAtStackLen A err n ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
        memRegion (s0.sp - 128#64) 48 ∗ chunkedHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chunkedHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; chunkedHeaderReceivedMerge_fetches img.base H 128 28
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName = entry; examples_hide_fetches
  apply SepWPpIn.of_sepWP_ret; unfold WppPost chunkedHeaderReceivedMergeSpec
  simp only [hnone, chunkedHeaderReceivedErrFrame, chunkedInlSavedRegs10,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp, hx0]
  apply SepWP.fold (decodeErrorWith_le3_hr A err hn) (by sep_focus)
  apply SepWP.fold (chunkedHeaderReceivedPBAt_entails_exists A x.msgPtr m) (by sep_focus)
  wp_steps; apply SepWP.fold (stackAt_chunkedInl10_epilogue s0.sp s0) (by unfold chunkedInlSavedRegs10; sep_focus); wp_done

theorem chunkedHeaderReceived_from_err_exit {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName + 0xffffffffffffa1f4#64) (decodeErrorFromSpec A))
    {x : ChunkedHeaderReceivedMergeGhost} {R : SepProp} {s0 : State} {m : V1State.Chunked.HeaderReceived} {s : State} {w : BitVec 64}
    (hnone : (Proto.mergeMessage V1State.Chunked.HeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none) (hw : KindNoHeap w) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName + 120#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ w) ∗ memRegion (s0.sp - 120#64) 40 ∗
        stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chunkedHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; chunkedHeaderReceivedMerge_fetches img.base H 120 36
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName = entry; examples_hide_fetches
  apply SepWPpIn.of_sepWP (mid := entry + 0xffffffffffffa1f4#64)
  conv => arg 4; rw [chunkedHeaderReceivedErrFrame, chunkedInlBelow_decodeErrorHook s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpIn.call_frame (x := (s0.sp - 128#64, w))
    (ret_pc := entry + 128#64) hFromCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorFromSpec]; simp only [arm64_norm, hsp]; rfl) hw (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, _, _, _, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx27, hx28, hvregs] at hpcm hspm hx27_m hx28_m hvregs_m
  apply SepWPpIn.of_sepWP_ret; unfold WppPost chunkedHeaderReceivedMergeSpec
  simp only [decodeErrorFromSpec, hnone, chunkedHeaderReceivedErrFrame, chunkedInlSavedRegs10,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp, hspm]
  apply SepWP.fold (chunkedInlBelow_decodeErrorHook_entails s0.sp) (by sep_focus)
  apply SepWP.fold (memRegion8_memRegion40_entails_48_160 s0.sp) (by sep_focus)
  apply SepWP.fold (decodeErrorWith_le3_hr A (sm.readReg64 (Reg.gpr 0#5)) (by decide : 0 ≤ 3)) (by sep_focus)
  apply SepWP.fold (chunkedHeaderReceivedPBAt_entails_exists A x.msgPtr m) (by sep_focus)
  wp_steps; apply SepWP.fold (stackAt_chunkedInl10_epilogue s0.sp s0) (by unfold chunkedInlSavedRegs10; sep_focus); wp_done

theorem chunkedHeaderReceived_push_ret_exit {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName + 0xffffffffffff9efc#64) (decodeErrorPushSpec A))
    {x : ChunkedHeaderReceivedMergeGhost} {R : SepProp} {s0 : State} {m : V1State.Chunked.HeaderReceived} {s : State}
    {err : BitVec 64} {n : Nat}
    (hnone : (Proto.mergeMessage V1State.Chunked.HeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none) (hn : n ≤ 2) (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName + 760#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = s0.sp - 128#64) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A err n ∗ memRegion (s0.sp - 120#64) 40 ∗
        stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chunkedHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; have hret := @chunkedHeaderReceived_ret_err_exit img A H x R s0 m
  chunkedHeaderReceivedMerge_fetches img.base H 760 12
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName = entry; examples_hide_fetches
  apply SepWPpIn.of_sepWP (mid := entry + 0xffffffffffff9efc#64)
  conv => arg 4; rw [chunkedHeaderReceivedErrFrame, chunkedInlBelow_decodeErrorHook s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpIn.call_frame (x := (s0.sp - 128#64, err, n))
    (ret_pc := entry + 764#64) hPushCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorPushSpec]; simp only [arm64_norm, hsp, hx0]; rfl)
    (by omega : n < 2 ^ 32) (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, _, _, _, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx27, hx28, hvregs] at hpcm hspm hx27_m hx28_m hvregs_m
  apply SepWPpIn.of_sepWP (mid := entry + 128#64)
  (conv => arg 4; simp only [decodeErrorPushSpec, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; intro htrm
  apply SepWP.fold (chunkedInlBelow_decodeErrorHook_entails s0.sp) (by sep_focus); wp_steps
  apply SepWP.fold (pointsTo64_memRegion40_entails_48_160 s0.sp err) (by sep_focus); wp_reach
  apply SepWPpIn.weaken_pre (P' := decodeErrorAtStackLen A err (n + 1) ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
    (by dsimp only [chunkedHeaderReceivedErrFrame]; sep_entail)
  exact hret hnone (by omega : n + 1 ≤ 3) herr hsp_align
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])
    ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

theorem chunkedHeaderReceived_uc_push_exit {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName + 0xffffffffffff9efc#64) (decodeErrorPushSpec A))
    {x : ChunkedHeaderReceivedMergeGhost} {R : SepProp} {s0 : State} {m : V1State.Chunked.HeaderReceived} {s : State}
    {err : BitVec 64} {n : Nat}
    (hnone : (Proto.mergeMessage V1State.Chunked.HeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none) (hn : n ≤ 2) (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName + 728#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hx1 : s.readReg64 (Reg.gpr 1#5) = err) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
      (decodeErrorAtStackLen A err n ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
        memRegion (s0.sp - 128#64) 48 ∗ chunkedHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chunkedHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; have hpush := @chunkedHeaderReceived_push_ret_exit img A H hPushCall x R s0 m
  chunkedHeaderReceivedMerge_fetches img.base H 728 32
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName = entry; examples_hide_fetches
  apply SepWPpIn.of_sepWP (mid := entry + 760#64)
  conv => arg 4; rw [memRegion_48_cells1_160 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, hx1]
  apply SepWP.exists_elim; intro v_stk0; wp_steps; wp_reach
  apply SepWPpIn.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A err n ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
    (by sep_entail)
  exact hpush hnone hn herr hsp_align
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hsp])
    ⟨by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩

theorem chunkedHeaderReceived_uc_from_push_exit {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName + 0xffffffffffffa1f4#64) (decodeErrorFromSpec A)) (hPushCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName + 0xffffffffffff9efc#64) (decodeErrorPushSpec A))
    {x : ChunkedHeaderReceivedMergeGhost} {R : SepProp} {s0 : State} {m : V1State.Chunked.HeaderReceived} {s : State} {w : BitVec 64}
    (hnone : (Proto.mergeMessage V1State.Chunked.HeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none) (hw : KindNoHeap w) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName + 716#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ w) ∗ memRegion (s0.sp - 120#64) 40 ∗
        stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
        chunkedHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chunkedHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  have hpush := @chunkedHeaderReceived_uc_push_exit img A H hPushCall x R s0 m
  chunkedHeaderReceivedMerge_fetches img.base H 716 12
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName = entry; examples_hide_fetches
  apply SepWPpIn.of_sepWP (mid := entry + 0xffffffffffffa1f4#64)
  conv => arg 4; rw [chunkedHeaderReceivedErrFrame, chunkedInlBelow_decodeErrorHook s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpIn.call_frame (x := (s0.sp - 128#64, w))
    (ret_pc := entry + 724#64) hFromCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorFromSpec]; simp only [arm64_norm, hsp]; rfl)
    hw (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, _, _, _, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx27, hx28, hvregs] at hpcm hspm hx27_m hx28_m hvregs_m
  apply SepWPpIn.of_sepWP (mid := entry + 728#64)
  (conv => arg 4; simp only [decodeErrorFromSpec, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨hsm0, htrm⟩
  apply SepWP.fold (chunkedInlBelow_decodeErrorHook_entails s0.sp) (by sep_focus)
  apply SepWP.fold (memRegion8_memRegion40_entails_48_160 s0.sp) (by sep_focus)
  wp_steps; wp_reach
  apply SepWPpIn.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
    (by dsimp only [chunkedHeaderReceivedErrFrame]; sep_entail)
  exact hpush hnone (by decide : 0 ≤ 2) hsm0 hsp_align
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])
    ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

theorem chunkedHeaderReceived_uc_field_push_exit {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName + 0xffffffffffff9efc#64) (decodeErrorPushSpec A))
    {x : ChunkedHeaderReceivedMergeGhost} {R : SepProp} {s0 : State} {m : V1State.Chunked.HeaderReceived} {s : State}
    {err : BitVec 64} {n : Nat}
    (hnone : (Proto.mergeMessage V1State.Chunked.HeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none) (hn : n ≤ 1) (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName + 988#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = s0.sp - 128#64) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A err n ∗ memRegion (s0.sp - 120#64) 40 ∗
        stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
        chunkedHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chunkedHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  have hpush := @chunkedHeaderReceived_uc_push_exit img A H hPushCall x R s0 m
  chunkedHeaderReceivedMerge_fetches img.base H 988 12
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName = entry; examples_hide_fetches
  apply SepWPpIn.of_sepWP (mid := entry + 0xffffffffffff9efc#64)
  conv => arg 4; rw [chunkedHeaderReceivedErrFrame, chunkedInlBelow_decodeErrorHook s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpIn.call_frame (x := (s0.sp - 128#64, err, n))
    (ret_pc := entry + 992#64) hPushCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorPushSpec]; simp only [arm64_norm, hsp, hx0]; rfl)
    (by omega : n < 2 ^ 32)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, _, _, _, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx27, hx28, hvregs] at hpcm hspm hx27_m hx28_m hvregs_m
  apply SepWPpIn.of_sepWP (mid := entry + 728#64)
  (conv => arg 4; simp only [decodeErrorPushSpec, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; intro htrm
  apply SepWP.fold (chunkedInlBelow_decodeErrorHook_entails s0.sp) (by sep_focus)
  wp_steps
  apply SepWP.fold (pointsTo64_memRegion40_entails_48_160 s0.sp err) (by sep_focus)
  wp_reach
  apply SepWPpIn.weaken_pre (P' := decodeErrorAtStackLen A err (n + 1) ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
    (by dsimp only [chunkedHeaderReceivedErrFrame]; sep_entail)
  exact hpush hnone (by omega : n + 1 ≤ 2) herr hsp_align
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])
    ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

/-! ## 3. Inner `Unchunked.HeaderReceived` Field Steps and Loop Induction -/

theorem chunkedHeaderReceived_uc_skip_step {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName + 0xffffffffffff9efc#64) (decodeErrorPushSpec A)) (hSkipCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName + 0xffffffffffffafc8#64) (skipField3Spec A))
    {x : ChunkedHeaderReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {ek : Option PolynomialDecoder} {uc : V1State.Unchunked.HeaderReceived}
    {rest : List (BitVec 8)} {iwt : WireType} {tag outerLimit innerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length) (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest) (htag_lt : tag < 2 ^ 32) (hnone_of_sf : skipField (2 * rest.length + 2) 97 tag iwt rest = none →
      (Proto.mergeMessage V1State.Chunked.HeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (rest' : List (BitVec 8)) (s' : State),
      skipField (2 * rest.length + 2) 97 tag iwt rest = some rest' →
      s'.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName + 416#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr → s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit → s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s'
        (chunkedHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr ek uc x.bs rest')
        (WppPost (chunkedHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName + 492#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat) (hx1 : (s.readReg64 (Reg.gpr 1#5)).setWidth 32 = BitVec.ofNat 32 tag) (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr) (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit) (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64) (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
      (chunkedHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr ek uc x.bs rest)
      (WppPost (chunkedHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hpush_exit := @chunkedHeaderReceived_uc_push_exit img A H hPushCall x R s0 { uc := some uc, receivingEk := ek }
  chunkedHeaderReceivedMerge_fetches img.base H 492 20; chunkedHeaderReceivedMerge_fetches img.base H 412 4
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName = entry; examples_hide_fetches
  apply SepWPpIn.of_sepWP (mid := entry + 0xffffffffffffafc8#64)
  conv => arg 4; rw [chunkedHeaderReceivedUcLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
    chunkedInlBelow_skipField97 s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpIn.call_frame (x := ⟨iwt, tag, 97, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := entry + 504#64) hSkipCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [skipField3Spec]; simp only [arm64_norm, hsp, hx0, hx1, hx19, setWidth8_ofNat64_wt]; rfl)
    (⟨htag_lt, by decide, hrest_lt⟩ : tag < 2 ^ 32 ∧ 97 < 2 ^ 32 ∧ rest.length < 2 ^ 63)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
  cases hsf : skipField (2 * rest.length + 2) 97 tag iwt rest with
  | none =>
    have hnone := hnone_of_sf hsf
    apply SepWPpIn.of_sepWP (mid := entry + 728#64)
    (conv => arg 4; simp only [skipField3Spec, hsf, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (chunkedInlBelow_skipField97_entails s0.sp) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus); apply SepWP.fold (unchunked3CapAt_entails_chunkedHeaderReceivedPBAt A x.msgPtr rest.length ek uc) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPpIn.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc, receivingEk := ek } x.bs)
      (by dsimp only [chunkedHeaderReceivedErrFrame]; sep_entail)
    exact hpush_exit hnone (by decide : 0 ≤ 2) hsm0 hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])
      ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some rest' =>
    have hrest'_le : rest'.length ≤ rest.length := (skip_length _).1 _ _ _ _ _ hsf
    apply SepWPpIn.of_sepWP (mid := entry + 416#64)
    (conv => arg 4; simp only [skipField3Spec, hsf, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    apply SepWP.fold (chunkedInlBelow_skipField97_entails s0.sp) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus); apply SepWP.fold (unchunked3CapAt_mono A x.msgPtr uc.epoch uc.auth uc.hdr hrest'_le) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPpIn.weaken_pre (P' := chunkedHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr ek uc x.bs rest')
      (by dsimp only [chunkedHeaderReceivedUcLoopPre]; sep_entail)
    exact hcont rest' _ hsf
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m]) (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m]) (by simp only [arm64_norm, hx25_m]) (by simp only [arm64_norm, hx26_m])
      ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

theorem chunkedHeaderReceived_uc_tag1_varint_step {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName + 0xffffffffffff9efc#64) (decodeErrorPushSpec A)) (hVarintCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName + 0xffffffffffffc920#64) (decodeVarint2Spec A))
    {x : ChunkedHeaderReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {ek : Option PolynomialDecoder} {uc : V1State.Unchunked.HeaderReceived}
    {rest : List (BitVec 8)} {outerLimit innerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length) (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest) (hnone_of_dv : decodeVarint rest = none →
      (Proto.mergeMessage V1State.Chunked.HeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (v : BitVec 64) (rest' : List (BitVec 8)) (s' : State),
      decodeVarint rest = some (v, rest') →
      s'.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName + 416#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr → s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit → s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s'
        (chunkedHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr ek { uc with epoch := v } x.bs rest')
        (WppPost (chunkedHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName + 556#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = 0#64) (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr) (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit) (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64) (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
      (chunkedHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr ek uc x.bs rest)
      (WppPost (chunkedHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hfpush := @chunkedHeaderReceived_uc_field_push_exit img A H hPushCall x R s0 { uc := some uc, receivingEk := ek }
  chunkedHeaderReceivedMerge_fetches img.base H 556 40; chunkedHeaderReceivedMerge_fetches img.base H 408 8; chunkedHeaderReceivedMerge_fetches img.base H 956 32
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName = entry; examples_hide_fetches
  apply SepWPpIn.of_sepWP (mid := entry + 0xffffffffffffc920#64)
  conv => arg 4; rw [chunkedHeaderReceivedUcLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
    chunkedInlBelow_decodeVarint2 s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpIn.call_frame (x := ⟨x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := entry + 568#64) hVarintCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, hsp, hx19]; rfl)
    hrest_lt (by sep_focus) (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
  cases hdv : decodeVarint rest with
  | none =>
    have hnone := hnone_of_dv hdv
    apply SepWPpIn.of_sepWP (mid := entry + 988#64)
    (conv => arg 4; simp only [decodeVarint2Spec, hdv, memRegion_48_cells1_160 s0.sp,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp])
    apply SepWP.exists_elim; intro v_stk0; apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
    have hcbnz_err : (sm.readReg64 (Reg.gpr 1#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm1
    apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus); apply SepWP.fold (unchunked3CapAt_entails_chunkedHeaderReceivedPBAt A x.msgPtr rest.length ek uc) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPpIn.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 1#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc, receivingEk := ek } x.bs)
      (by dsimp only [chunkedHeaderReceivedErrFrame]; sep_entail)
    exact hfpush hnone (by decide : 0 ≤ 1) hsm1 hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm, hspm])
      ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨v, rest'⟩
    have hrest'_le : rest'.length ≤ rest.length := Nat.le_of_lt (decodeVarint_length hdv)
    apply SepWPpIn.of_sepWP (mid := entry + 416#64)
    (conv => arg 4; simp only [decodeVarint2Spec, hdv, unchunked3CapAt_eq_hr, sepConj_assoc, arm64_norm, hsp])
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
    apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus); apply SepWP.fold (vecU8CapAt_hr_mono A x.msgPtr uc.hdr hrest'_le) (by sep_focus); apply SepWP.fold (optAuthenticatorPBCapAt_mono A (x.msgPtr + 0x18#64) uc.auth hrest'_le) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPpIn.weaken_pre (P' := chunkedHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr ek { uc with epoch := v } x.bs rest')
      (by dsimp only [chunkedHeaderReceivedUcLoopPre]; rw [unchunked3CapAt_eq_hr]; simp only [arm64_norm]; sep_entail)
    exact hcont v rest' _ hdv
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m]) (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m]) (by simp only [arm64_norm, hx25_m]) (by simp only [arm64_norm, hx26_m])
      ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

theorem chunkedHeaderReceived_uc_tag1_wt_err_step {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName + 0xffffffffffffa1f4#64) (decodeErrorFromSpec A)) (hPushCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName + 0xffffffffffff9efc#64) (decodeErrorPushSpec A))
    {x : ChunkedHeaderReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {ek : Option PolynomialDecoder} {uc : V1State.Unchunked.HeaderReceived}
    {rest : List (BitVec 8)} {iwt : WireType}
    (hiwt : iwt ≠ .varint) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length) (hrest_suf : IsDropSuffix x.bs rest) (hnone : (Proto.mergeMessage V1State.Chunked.HeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none) (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName + 556#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
      (chunkedHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr ek uc x.bs rest)
      (WppPost (chunkedHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hcbnz_wt : (BitVec.ofNat 64 iwt.toNat == 0#64) = false := iwt_cbnz_true_of_ne_varint hiwt
  have hfpush := @chunkedHeaderReceived_uc_field_push_exit img A H hPushCall x R s0 { uc := some uc, receivingEk := ek }
  chunkedHeaderReceivedMerge_fetches img.base H 556 4; chunkedHeaderReceivedMerge_fetches img.base H 924 64
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName = entry; examples_hide_fetches
  apply SepWPpIn.of_sepWP (mid := entry + 0xffffffffffffa1f4#64)
  conv => arg 4; rw [chunkedHeaderReceivedUcLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
    sliceCursorAt, chunkedInlBelow_decodeErrorHook s0.sp, memRegion_48_wtErr160 s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro b_wt1; apply SepWP.exists_elim; intro b_wt0; apply SepWP.exists_elim; intro v_wt0
  wp_steps
  apply SepWP.fold (wtErr160_entails_memRegion40 s0.sp _ _) (by sep_focus)
  apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
  apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
  apply SepWP.fold (unchunked3CapAt_entails_chunkedHeaderReceivedPBAt A x.msgPtr rest.length ek uc) (by sep_focus)
  wp_reach
  refine SepWPpIn.call_frame (x := (s0.sp - 128#64, 0x8000000000000006#64))
    (ret_pc := entry + 952#64) hFromCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorFromSpec]; simp only [arm64_norm, hsp]; rfl)
    (by decide : KindNoHeap 0x8000000000000006#64) (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, _, _, _, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx27, hx28, hvregs] at hpcm hspm hx27_m hx28_m hvregs_m
  apply SepWPpIn.of_sepWP (mid := entry + 988#64)
  (conv => arg 4; simp only [decodeErrorFromSpec, memRegion_48_cells1_160 s0.sp,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp])
  apply SepWP.exists_elim; intro v_stk0; apply SepWP.pure_elim; rintro ⟨hsm0, htrm⟩
  apply SepWP.fold (chunkedInlBelow_decodeErrorHook_entails s0.sp) (by sep_focus)
  wp_steps; wp_reach
  apply SepWPpIn.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc, receivingEk := ek } x.bs)
    (by dsimp only [chunkedHeaderReceivedErrFrame]; sep_entail)
  exact hfpush hnone (by decide : 0 ≤ 1) hsm0 hsp_align
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm, hspm])
    ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩


theorem chunkedHeaderReceived_uc_auth_init {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    {x : ChunkedHeaderReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {ek : Option PolynomialDecoder} {uc : V1State.Unchunked.HeaderReceived} {rest : List (BitVec 8)}
    (hcont : ∀ (s' : State),
      s'.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName + 536#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s.trace →
      s'.readReg64 (Reg.gpr 0#5) = s.readReg64 (Reg.gpr 0#5) → s'.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr → s'.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) → s'.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) → s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) → s'.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) → s'.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s'
        (authenticatorPBCapAt A (x.msgPtr + 0x18#64) rest.length (uc.auth.getD default) ∗
          vecU8CapAt_hr A x.msgPtr rest.length uc.hdr ∗
          ((x.msgPtr + 0x48#64) ↦₆₄ uc.epoch) ∗ optPolynomialDecoderPBAt A (x.msgPtr + 80#64) ek ∗
          stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗
          chunkedInlSavedRegs10 s0.sp s0 ∗ (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool)
        (WppPost (chunkedHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName + 512#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr) (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
      (chunkedHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr ek uc x.bs rest)
      (WppPost (chunkedHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; chunkedHeaderReceivedMerge_fetches img.base H 512 24
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName = entry; examples_hide_fetches
  rcases hauth : uc.auth with _ | auth
  · rw [hauth] at hcont
    apply SepWPpIn.of_sepWP (mid := entry + 536#64)
    conv => arg 4; rw [chunkedHeaderReceivedUcLoopPre, unchunked3CapAt_eq_hr, hauth, optAuthenticatorPBCapAt,
      memRegion_40_cells (x.msgPtr + 0x18#64)]
    simp only [noneCap, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm]
    apply SepWP.exists_elim; intro w1; apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3; apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5
    wp_steps
    have hdef := default_cells_entails_authenticatorPBCapAt A (x.msgPtr + 0x18#64) rest.length
    simp only [arm64_norm] at hdef; apply SepWP.fold hdef (by sep_focus); wp_reach
    apply SepWPpIn.weaken_pre (P' := authenticatorPBCapAt A (x.msgPtr + 0x18#64) rest.length (Option.getD none default) ∗ vecU8CapAt_hr A x.msgPtr rest.length uc.hdr ∗ ((x.msgPtr + 0x48#64) ↦₆₄ uc.epoch) ∗ optPolynomialDecoderPBAt A (x.msgPtr + 80#64) ek ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedInlSavedRegs10 s0.sp s0 ∗ (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool)
      (Entails.of_eq rfl)
    exact hcont _ (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
      (by try simp only [arm64_norm]) (by try simp only [arm64_norm]) (by try simp only [arm64_norm])
      (by simp only [arm64_norm, hx20]) (by try simp only [arm64_norm]) (by try simp only [arm64_norm]) (by simp only [arm64_norm, hx23]) (by try simp only [arm64_norm]) (by try simp only [arm64_norm]) (by try simp only [arm64_norm])
      ⟨by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩
  · rw [hauth] at hcont
    apply SepWPpIn.of_sepWP (mid := entry + 536#64)
    conv => arg 4; rw [chunkedHeaderReceivedUcLoopPre, unchunked3CapAt_eq_hr, hauth, optAuthenticatorPBCapAt]
    simp only [sepConj_assoc, arm64_norm]
    have hcmn_in := authenticatorPBCapAt_entails_cmn_hr A (x.msgPtr + 0x18#64) rest.length auth
    simp only [arm64_norm] at hcmn_in; apply SepWP.fold hcmn_in (by sep_focus)
    wp_simp_pre [sepExists_sepConj_left, sepConj_assoc, arm64_norm]
    apply SepWP.exists_elim; intro cap_ik; apply SepWP.exists_elim; intro ptr_ik
    apply SepWP.pure_elim; rintro ⟨hcap_lt, hcap_ok⟩
    have hcmn1 := cap_add_one_beq_zero_false hcap_lt; have hcmn2 := cap_add_one_bne_zero_true hcap_lt
    wp_steps
    have hcmn_out := cmn_entails_authenticatorPBCapAt_hr A (x.msgPtr + 0x18#64) rest.length auth cap_ik ptr_ik hcap_ok
    simp only [arm64_norm] at hcmn_out; apply SepWP.fold hcmn_out (by sep_focus); wp_reach
    apply SepWPpIn.weaken_pre (P' := authenticatorPBCapAt A (x.msgPtr + 0x18#64) rest.length (Option.getD (some auth) default) ∗ vecU8CapAt_hr A x.msgPtr rest.length uc.hdr ∗ ((x.msgPtr + 0x48#64) ↦₆₄ uc.epoch) ∗ optPolynomialDecoderPBAt A (x.msgPtr + 80#64) ek ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedInlSavedRegs10 s0.sp s0 ∗ (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool)
      (Entails.of_eq rfl)
    exact hcont _ (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
      (by try simp only [arm64_norm]) (by try simp only [arm64_norm]) (by try simp only [arm64_norm])
      (by simp only [arm64_norm, hx20]) (by try simp only [arm64_norm]) (by try simp only [arm64_norm]) (by simp only [arm64_norm, hx23]) (by try simp only [arm64_norm]) (by try simp only [arm64_norm]) (by try simp only [arm64_norm])
      ⟨by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩

theorem chunkedHeaderReceived_uc_tag2_step {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName + 0xffffffffffff9efc#64) (decodeErrorPushSpec A)) (hAuthCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName + 0xffffffffffffd38c#64) ((authMergeSpec A).inImage img))
    {x : ChunkedHeaderReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {ek : Option PolynomialDecoder} {uc : V1State.Unchunked.HeaderReceived} {rest : List (BitVec 8)}
    {iwt : WireType} {outerLimit innerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length) (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest) (hnone_of_auth :
      (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto iwt) (uc.auth.getD default) rest 97).toOption = none →
      (Proto.mergeMessage V1State.Chunked.HeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (auth' : ProtoAuthenticator) (rest' : List (BitVec 8)) (s' : State),
      (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto iwt) (uc.auth.getD default) rest 97).toOption = some (auth', rest') →
      s'.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName + 416#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr → s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit → s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s'
        (chunkedHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr ek { uc with auth := some auth' } x.bs rest')
        (WppPost (chunkedHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName + 512#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat) (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr) (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit) (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64) (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
      (chunkedHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr ek uc x.bs rest)
      (WppPost (chunkedHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  have hfpush := fun {auth' : ProtoAuthenticator} => @chunkedHeaderReceived_uc_field_push_exit img A H hPushCall x R s0 { uc := some { epoch := uc.epoch, auth := some auth', hdr := uc.hdr }, receivingEk := ek }
  refine chunkedHeaderReceived_uc_auth_init ?_ hpc hrun hsp hx20 hx23 hcs
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hcs1
  rw [htr] at htr1; rw [hx0] at hx0_1; rw [hx19] at hx19_1; rw [hx21] at hx21_1
  rw [hx22] at hx22_1; rw [hx24] at hx24_1; rw [hx25] at hx25_1; rw [hx26] at hx26_1
  obtain ⟨hx27_1, hx28_1, hvregs_1⟩ := hcs1; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  chunkedHeaderReceivedMerge_fetches img.base H 536 20
  chunkedHeaderReceivedMerge_fetches img.base H 408 8; chunkedHeaderReceivedMerge_fetches img.base H 888 36
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName = entry; examples_hide_fetches
  apply SepWPpIn.of_sepWP (mid := entry + 0xffffffffffffd38c#64)
  conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, chunkedInlBelow_authMerge s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpIn.call_frame_inImage (x := ⟨iwt, x.msgPtr + 0x18#64, uc.auth.getD default, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := entry + 548#64) hAuthCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
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
    apply SepWPpIn.of_sepWP (mid := entry + 988#64)
    (conv => arg 4; simp only [authMergeSpec, hauth_res, memRegion_48_cells1_160 s0.sp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp1])
    apply SepWP.exists_elim; intro v_stk0; apply SepWP.exists_elim; intro auth'; apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; intro hpure
    have htrm : sm.trace = _ := hpure.1; have hsm0 : sm.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hpure.2.1; have hn_err : n_err ≤ 1 := hpure.2.2
    have hcbz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (chunkedInlBelow_authMerge_entails s0.sp) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus); apply SepWP.fold (vecU8CapAt_hr_entails_vecU8 A x.msgPtr rest.length uc.hdr) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPpIn.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some { epoch := uc.epoch, auth := some auth', hdr := uc.hdr }, receivingEk := ek } x.bs)
      (by dsimp only [chunkedHeaderReceivedErrFrame, chunkedHeaderReceivedPBAt, optHeaderReceivedPBAt, headerReceivedPBAt, unchunked3At, optAuthenticatorPBAt]; simp only [arm64_norm]; sep_entail)
    exact hfpush hnone hn_err hsm0 hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr1]) (by simp only [arm64_norm, hspm]) ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨auth', rest'⟩
    have hrest'_le : rest'.length ≤ rest.length := (proto_mergeMessage_suffix hauth_res).1
    apply SepWPpIn.of_sepWP (mid := entry + 416#64)
    (conv => arg 4; simp only [authMergeSpec, hauth_res, sepConj_assoc, arm64_norm, hsp1])
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    apply SepWP.fold (chunkedInlBelow_authMerge_entails s0.sp) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus); apply SepWP.fold (vecU8CapAt_hr_mono A x.msgPtr uc.hdr hrest'_le) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPpIn.weaken_pre (P' := chunkedHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr ek { uc with auth := some auth' } x.bs rest')
      (by dsimp only [chunkedHeaderReceivedUcLoopPre]; rw [unchunked3CapAt_eq_hr]; dsimp only [optAuthenticatorPBCapAt]; simp only [arm64_norm]; sep_entail)
    exact hcont auth' rest' _ hauth_res (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr1])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m]) (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m]) (by simp only [arm64_norm, hx25_m]) (by simp only [arm64_norm, hx26_m]) ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

theorem chunkedHeaderReceived_uc_tag3_step {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName + 0xffffffffffff9efc#64) (decodeErrorPushSpec A)) (hBytesCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName + 0xffffffffffffc590#64) ((bytesMerge3RawSpec A).inImage img))
    {x : ChunkedHeaderReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {ek : Option PolynomialDecoder} {uc : V1State.Unchunked.HeaderReceived} {rest : List (BitVec 8)}
    {iwt : WireType} {outerLimit innerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length) (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest) (hnone_of_mb : mergeBytes iwt rest = none →
      (Proto.mergeMessage V1State.Chunked.HeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (v rest' : List (BitVec 8)) (s' : State),
      mergeBytes iwt rest = some (v, rest') →
      s'.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName + 416#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr → s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit → s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s'
        (chunkedHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr ek { uc with hdr := v } x.bs rest')
        (WppPost (chunkedHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName + 392#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat) (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr) (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit) (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64) (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
      (chunkedHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr ek uc x.bs rest)
      (WppPost (chunkedHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hfpush := @chunkedHeaderReceived_uc_field_push_exit img A H hPushCall x R s0 { uc := some uc, receivingEk := ek }
  chunkedHeaderReceivedMerge_fetches img.base H 392 24; chunkedHeaderReceivedMerge_fetches img.base H 852 36
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName = entry; examples_hide_fetches
  apply SepWPpIn.of_sepWP (mid := entry + 0xffffffffffffc590#64)
  conv => arg 4; rw [chunkedHeaderReceivedUcLoopPre, unchunked3CapAt, sliceCursorAfter_eq_split hrest_le hrest_suf,
    chunkedInlBelow_bytesMerge3 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro cap_hdr; apply SepWP.exists_elim; intro ptr_hdr; apply SepWP.pure_elim; intro hcap_hdr
  wp_steps; wp_reach
  refine SepWPpIn.call_frame_inImage (x := ⟨iwt, x.msgPtr, cap_hdr, ptr_hdr, uc.hdr, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := entry + 404#64) hBytesCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [bytesMerge3RawSpec]; simp only [arm64_norm, hsp, hx0, hx20, hx19, setWidth8_ofNat64_wt]; rfl)
    (⟨hrest_lt, hcap_hdr⟩ : rest.length < 2 ^ 63 ∧ BytesMergeCapOk cap_hdr rest.length) (by sep_focus) (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [bytesMerge3RawSpec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
  cases hmb : mergeBytes iwt rest with
  | none =>
    have hnone := hnone_of_mb hmb
    apply SepWPpIn.of_sepWP (mid := entry + 988#64)
    (conv => arg 4; simp only [bytesMerge3RawSpec, hmb, memRegion_48_cells1_160 s0.sp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp])
    apply SepWP.exists_elim; intro v_stk0; apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (chunkedInlBelow_bytesMerge3_entails s0.sp) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    have hhdr : vecU8At A x.msgPtr cap_hdr ptr_hdr uc.hdr ⊢ rustBytesVecAt A x.msgPtr uc.hdr :=
      Entails.sepExists_right cap_hdr (Entails.sepExists_right ptr_hdr (Entails.refl _))
    apply SepWP.fold hhdr (by sep_focus); apply SepWP.fold (optAuthenticatorPBCapAt_entails_optAuthenticatorPBAt A (x.msgPtr + 0x18#64) rest.length uc.auth) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPpIn.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc, receivingEk := ek } x.bs)
      (by dsimp only [chunkedHeaderReceivedErrFrame, chunkedHeaderReceivedPBAt, optHeaderReceivedPBAt, headerReceivedPBAt, unchunked3At]; sep_entail)
    exact hfpush hnone (by decide : 0 ≤ 1) hsm0 hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm, hspm]) ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨v, rest'⟩
    have hrest'_le : rest'.length ≤ rest.length := mergeBytes_length hmb
    apply SepWPpIn.of_sepWP (mid := entry + 416#64)
    (conv => arg 4; simp only [bytesMerge3RawSpec, hmb, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp])
    apply SepWP.exists_elim; intro cap_hdr'; apply SepWP.exists_elim; intro ptr_hdr'
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hcap_hdr'⟩
    apply SepWP.fold (chunkedInlBelow_bytesMerge3_entails s0.sp) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    have hhdr_cap : vecU8At A x.msgPtr cap_hdr' ptr_hdr' v ⊢ (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap rest'.length⌝ ∗ vecU8At A x.msgPtr cap ptr v) :=
      Entails.trans (Entails.pure_right hcap_hdr' (Entails.refl _)) (Entails.sepExists_right cap_hdr' (Entails.sepExists_right ptr_hdr' (Entails.refl _)))
    apply SepWP.fold hhdr_cap (by sep_focus); apply SepWP.fold (optAuthenticatorPBCapAt_mono A (x.msgPtr + 0x18#64) uc.auth hrest'_le) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPpIn.weaken_pre (P' := chunkedHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr ek { uc with hdr := v } x.bs rest')
      (by dsimp only [chunkedHeaderReceivedUcLoopPre, unchunked3CapAt]; sep_entail)
    exact hcont v rest' _ hmb (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m]) (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m]) (by simp only [arm64_norm, hx25_m]) (by simp only [arm64_norm, hx26_m]) ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩


theorem chunkedHeaderReceived_uc_loop_le_exit {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName + 0xffffffffffffa1f4#64) (decodeErrorFromSpec A)) (hPushCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName + 0xffffffffffff9efc#64) (decodeErrorPushSpec A))
    {x : ChunkedHeaderReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {ek : Option PolynomialDecoder} {uc : V1State.Unchunked.HeaderReceived}
    {cur : List (BitVec 8)} {outerLimit innerLimit : Nat}
    (hle_lim : cur.length ≤ innerLimit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hcur_le : cur.length ≤ x.bs.length) (hcur_suf : IsDropSuffix x.bs cur) (hlim_lt : innerLimit < 2 ^ 63) (hnone_of_lt : cur.length < innerLimit →
      (Proto.mergeMessage V1State.Chunked.HeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (s' : State),
      cur.length = innerLimit →
      s'.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName + 168#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr → s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit → s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s'
        (chunkedHeaderReceivedLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc, receivingEk := ek } x.bs cur)
        (WppPost (chunkedHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName + 416#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr) (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit) (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64) (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
      (chunkedHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr ek uc x.bs cur)
      (WppPost (chunkedHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  by_cases heq_lim : cur.length = innerLimit
  · obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq heq_lim
    chunkedHeaderReceivedMerge_fetches img.base H 416 12; chunkedHeaderReceivedMerge_fetches img.base H 596 12
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName = entry; examples_hide_fetches
    apply SepWPpIn.of_sepWP (mid := entry + 168#64)
    conv => arg 4; rw [chunkedHeaderReceivedUcLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt]
    simp only [sepConj_assoc]; wp_steps
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus); wp_reach
    apply SepWPpIn.weaken_pre (P' := chunkedHeaderReceivedLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc, receivingEk := ek } x.bs cur)
      (by dsimp only [chunkedHeaderReceivedLoopPre, chunkedHeaderReceivedPBCapAt, optHeaderReceivedPBCapAt, unchunked3CapAt, sliceCursorAfter]; sep_entail)
    exact hcont _ heq_lim
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20]) (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24]) (by simp only [arm64_norm, hx25])
      ⟨by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩
  · have hlt_lim : cur.length < innerLimit := Nat.lt_of_le_of_ne hle_lim heq_lim
    obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_lt hlt_lim hlim_lt
    have hnone := hnone_of_lt hlt_lim
    have hfrom_push := @chunkedHeaderReceived_uc_from_push_exit img A H hFromCall hPushCall x R s0 { uc := some uc, receivingEk := ek }
    chunkedHeaderReceivedMerge_fetches img.base H 416 12; chunkedHeaderReceivedMerge_fetches img.base H 596 4
    chunkedHeaderReceivedMerge_fetches img.base H 1008 16; chunkedHeaderReceivedMerge_fetches img.base H 712 4
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName = entry; examples_hide_fetches
    apply SepWPpIn.of_sepWP (mid := entry + 716#64)
    conv => arg 4; rw [chunkedHeaderReceivedUcLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
      sliceCursorAt, memRegion_48_cells1_160 s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v_stk0; wp_steps
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot curPtr (BitVec.ofNat 64 cur.length)) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus); apply SepWP.fold (unchunked3CapAt_entails_chunkedHeaderReceivedPBAt A x.msgPtr cur.length ek uc) (by sep_focus); wp_reach
    apply SepWPpIn.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000008#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc, receivingEk := ek } x.bs)
      (by dsimp only [chunkedHeaderReceivedErrFrame]; sep_entail)
    exact hfrom_push hnone (by decide : KindNoHeap 0x8000000000000008#64) hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr])
      ⟨by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩

theorem chunkedHeaderReceived_uc_decode_key_step {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName + 0xffffffffffffa1f4#64) (decodeErrorFromSpec A)) (hPushCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName + 0xffffffffffff9efc#64) (decodeErrorPushSpec A)) (hVarintCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName + 0xffffffffffffc920#64) (decodeVarint2Spec A))
    {x : ChunkedHeaderReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {ek : Option PolynomialDecoder} {uc : V1State.Unchunked.HeaderReceived}
    {cur : List (BitVec 8)} {outerLimit innerLimit : Nat}
    (hgt_lim : ¬ cur.length ≤ innerLimit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hcur_le : cur.length ≤ x.bs.length) (hcur_lt : cur.length < 2 ^ 63) (hcur_suf : IsDropSuffix x.bs cur) (hnone_of_uc_none :
      mergeLoopBin V1State.Unchunked.HeaderReceived.mergeField (cur.length - innerLimit) uc cur innerLimit 97 = none →
      (Proto.mergeMessage V1State.Chunked.HeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (key : BitVec 64) (iwt : WireType) (rest : List (BitVec 8)) (s' : State),
      decodeVarint cur = some (key, rest) → ¬ 2 ^ 32 ≤ key.toNat →
      WireType.ofNat? (key.toNat % 8) = some iwt → ¬ key.toNat / 8 < 1 →
      s'.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName + 468#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat → s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) → s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr → s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit → s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s'
        (chunkedHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr ek uc x.bs rest)
        (WppPost (chunkedHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName + 416#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr) (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit) (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64) (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
      (chunkedHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr ek uc x.bs cur)
      (WppPost (chunkedHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  have hpush_exit := @chunkedHeaderReceived_uc_push_exit img A H hPushCall x R s0 { uc := some uc, receivingEk := ek }
  have hfrom_push := @chunkedHeaderReceived_uc_from_push_exit img A H hFromCall hPushCall x R s0 { uc := some uc, receivingEk := ek }
  chunkedHeaderReceivedMerge_fetches img.base H 416 52; chunkedHeaderReceivedMerge_fetches img.base H 668 48
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName = entry; examples_hide_fetches
  apply SepWPpIn.of_sepWP (mid := entry + 0xffffffffffffc920#64)
  conv => arg 4; rw [chunkedHeaderReceivedUcLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
    sliceCursorAt, chunkedInlBelow_decodeVarint2 s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpIn.call_frame (x := ⟨x.bufRef, x.slot, curPtr, cur⟩)
    (ret_pc := entry + 436#64) hVarintCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, hsp, hx19]; rfl)
    hcur_lt (by dsimp only [sliceCursorAt, curPtr]; sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
  cases hd : decodeVarint cur with
  | none =>
    have hnone := hnone_of_uc_none (mergeLoopBin_of_decodeVarint_none protoPrefixStep_unchunked_headerReceived_mergeField hgt_lim hd)
    apply SepWPpIn.of_sepWP (mid := entry + 728#64)
    (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
    apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus); apply SepWP.fold (unchunked3CapAt_entails_chunkedHeaderReceivedPBAt A x.msgPtr cur.length ek uc) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPpIn.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc, receivingEk := ek } x.bs)
      (by dsimp only [chunkedHeaderReceivedErrFrame]; sep_entail)
    exact hpush_exit hnone (by decide : 0 ≤ 2) hsm1 hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])
      ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨key, rest⟩
    have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
    have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
    have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le
    have hrest_suf : IsDropSuffix x.bs rest := suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
    let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
    by_cases hk_ge : 2 ^ 32 ≤ key.toNat
    · have hnone := hnone_of_uc_none (mergeLoopBin_of_key_ge protoPrefixStep_unchunked_headerReceived_mergeField hgt_lim hd hk_ge)
      have hshr := key_shr32_of_ge hk_ge
      apply SepWPpIn.of_sepWP (mid := entry + 716#64)
      (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
      apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
      apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus); apply SepWP.fold (unchunked3CapAt_entails_chunkedHeaderReceivedPBAt A x.msgPtr cur.length ek uc) (by sep_focus)
      conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_cells2_160 s0.sp]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply SepWP.exists_elim; intro v_err0; apply SepWP.exists_elim; intro v_err1; wp_steps
      apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
      have h40 : ((s0.sp - 128#64 + 8#64) ↦₆₄ key) ∗ memRegion (s0.sp - 112#64) 32 ⊢ memRegion (s0.sp - 120#64) 40 := by
        rw [bv_sub_add_lit s0.sp 128 8]; exact cells2_memRegion32_entails_40_160 s0.sp key
      apply SepWP.fold h40 (by sep_focus); wp_reach
      apply SepWPpIn.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000004#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc, receivingEk := ek } x.bs)
        (by dsimp only [chunkedHeaderReceivedErrFrame]; sep_entail)
      exact hfrom_push hnone (by decide : KindNoHeap 0x8000000000000004#64) hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
        ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
    · have hshr := key_shr32_of_lt hk_ge
      cases hwt : WireType.ofNat? (key.toNat % 8) with
      | none =>
        have hnone := hnone_of_uc_none (mergeLoopBin_of_wt_none protoPrefixStep_unchunked_headerReceived_mergeField hgt_lim hd hk_ge hwt)
        obtain ⟨hcs1, hcs2⟩ := key_wt_none hwt
        apply SepWPpIn.of_sepWP (mid := entry + 716#64)
        (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
        apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
        apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus); apply SepWP.fold (unchunked3CapAt_entails_chunkedHeaderReceivedPBAt A x.msgPtr cur.length ek uc) (by sep_focus)
        conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_cells2_160 s0.sp]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        apply SepWP.exists_elim; intro v_err0; apply SepWP.exists_elim; intro v_err1; wp_steps
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        have h40 : ((s0.sp - 128#64 + 8#64) ↦₆₄ (key &&& 7#64)) ∗ memRegion (s0.sp - 112#64) 32 ⊢ memRegion (s0.sp - 120#64) 40 := by
          rw [bv_sub_add_lit s0.sp 128 8]; exact cells2_memRegion32_entails_40_160 s0.sp (key &&& 7#64)
        apply SepWP.fold h40 (by sep_focus); wp_reach
        apply SepWPpIn.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000003#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc, receivingEk := ek } x.bs)
          (by dsimp only [chunkedHeaderReceivedErrFrame]; sep_entail)
        exact hfrom_push hnone (by decide : KindNoHeap 0x8000000000000003#64) hsp_align
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
          ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
      | some iwt =>
        obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt; obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_ge; obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
        by_cases hitag0 : key.toNat / 8 < 1
        · have hnone := hnone_of_uc_none (mergeLoopBin_of_tag_zero protoPrefixStep_unchunked_headerReceived_mergeField hgt_lim hd hk_ge hwt hitag0)
          have htag_zero : key.toNat / 8 = 0 := by omega
          apply SepWPpIn.of_sepWP (mid := entry + 716#64)
          (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
          apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
          apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus); apply SepWP.fold (unchunked3CapAt_entails_chunkedHeaderReceivedPBAt A x.msgPtr cur.length ek uc) (by sep_focus)
          conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_cells1_160 s0.sp]
          simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
          apply SepWP.exists_elim; intro v_err0; wp_steps
          apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus); wp_reach
          apply SepWPpIn.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000005#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc, receivingEk := ek } x.bs)
            (by dsimp only [chunkedHeaderReceivedErrFrame]; sep_entail)
          exact hfrom_push hnone (by decide : KindNoHeap 0x8000000000000005#64) hsp_align
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
            ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
        · obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_ge hitag0
          have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
            rw [beq_eq_false_iff_ne]; intro h; have h1 := congrArg BitVec.toNat h
            simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1; omega
          apply SepWPpIn.of_sepWP (mid := entry + 468#64)
          (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
          apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
          apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus); apply SepWP.fold (unchunked3CapAt_mono A x.msgPtr uc.epoch uc.auth uc.hdr hrest_le_cur) (by sep_focus)
          wp_steps; wp_reach
          apply SepWPpIn.weaken_pre (P' := chunkedHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr ek uc x.bs rest)
            (by dsimp only [chunkedHeaderReceivedUcLoopPre]; sep_entail)
          exact hcont key iwt rest _ hd hk_ge hwt hitag0
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm, hsm1, hand_wt]) (by simp only [arm64_norm, hsm1, hw1, hw1_2, hw1_zext1, hw1_zext2]) (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m]) (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m]) (by simp only [arm64_norm, hx25_m]) (by simp only [arm64_norm, hx26_m])
            ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

theorem chunkedHeaderReceived_uc_loop_ok {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName + 0xffffffffffffa1f4#64) (decodeErrorFromSpec A)) (hPushCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName + 0xffffffffffff9efc#64) (decodeErrorPushSpec A)) (hVarintCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName + 0xffffffffffffc920#64) (decodeVarint2Spec A)) (hSkipCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName + 0xffffffffffffafc8#64) (skipField3Spec A)) (hAuthCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName + 0xffffffffffffd38c#64) ((authMergeSpec A).inImage img)) (hBytesCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName + 0xffffffffffffc590#64) ((bytesMerge3RawSpec A).inImage img))
    {x : ChunkedHeaderReceivedMergeGhost} {R : SepProp} {s0 : State} {ek : Option PolynomialDecoder} {outerLimit innerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hbs_lt : x.bs.length < 2 ^ 63) (hlim_lt : innerLimit < 2 ^ 63) :
    ∀ (n : Nat) (uc : V1State.Unchunked.HeaderReceived) (cur : List (BitVec 8)) (s : State),
      cur.length ≤ n → cur.length ≤ x.bs.length → IsDropSuffix x.bs cur →
      (∀ (uc' : V1State.Unchunked.HeaderReceived) (rest' : List (BitVec 8)) (s' : State),
        rest'.length = innerLimit → rest'.length ≤ x.bs.length → IsDropSuffix x.bs rest' →
        mergeLoopBin V1State.Unchunked.HeaderReceived.mergeField (cur.length - innerLimit) uc cur innerLimit 97 = some uc' →
        s'.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName + 168#64 →
        s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
        s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr → s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit → s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 25#5) = 8#64 → ChunkedInl10CalleeSaved s0 s' →
        SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s'
          (chunkedHeaderReceivedLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc', receivingEk := ek } x.bs rest')
          (WppPost (chunkedHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0)) →
      (mergeLoopBin V1State.Unchunked.HeaderReceived.mergeField (cur.length - innerLimit) uc cur innerLimit 97 = none →
        (Proto.mergeMessage V1State.Chunked.HeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none) →
      s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName + 416#64 →
      s.status = .Running → s.sp = s0.sp - 128#64 → s.trace = s0.trace →
      s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr → s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit → s.readReg64 (Reg.gpr 23#5) = 1#64 → s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 → s.readReg64 (Reg.gpr 25#5) = 8#64 → s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s →
      SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
        (chunkedHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr ek uc x.bs cur)
        (WppPost (chunkedHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  have htag1_varint := fun {s uc rest} => @chunkedHeaderReceived_uc_tag1_varint_step img A H hPushCall hVarintCall x R s0 s ek uc rest outerLimit innerLimit
  have htag1_wt_err := fun {s uc rest iwt} => @chunkedHeaderReceived_uc_tag1_wt_err_step img A H hFromCall hPushCall x R s0 s ek uc rest iwt
  have htag2_step := fun {s uc rest} (iwt : WireType) => @chunkedHeaderReceived_uc_tag2_step img A H hPushCall hAuthCall x R s0 s ek uc rest iwt outerLimit innerLimit
  have htag3_step := fun {s uc rest} (iwt : WireType) => @chunkedHeaderReceived_uc_tag3_step img A H hPushCall hBytesCall x R s0 s ek uc rest iwt outerLimit innerLimit
  have hskip_step := fun {s uc rest} (iwt : WireType) (tag : Nat) => @chunkedHeaderReceived_uc_skip_step img A H hPushCall hSkipCall x R s0 s ek uc rest iwt tag outerLimit innerLimit
  intro n; induction n with
  | zero =>
    intro uc cur s hcur_n hcur_le hcur_suf hok_cont hnone_cont hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
    exact chunkedHeaderReceived_uc_loop_le_exit hFromCall hPushCall (by omega) hsp_align hcur_le hcur_suf hlim_lt
      (fun hlt => hnone_cont (mergeLoopBin_lt_limit _ _ _ _ _ _ hlt))
      (fun s' heq => hok_cont uc cur s' heq hcur_le hcur_suf (mergeLoopBin_eq_limit _ _ _ _ _ _ heq))
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
  | succ n ih =>
    intro uc cur s hcur_n hcur_le hcur_suf hok_cont hnone_cont hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
    by_cases hle_lim : cur.length ≤ innerLimit
    · exact chunkedHeaderReceived_uc_loop_le_exit hFromCall hPushCall hle_lim hsp_align hcur_le hcur_suf hlim_lt
        (fun hlt => hnone_cont (mergeLoopBin_lt_limit _ _ _ _ _ _ hlt))
        (fun s' heq => hok_cont uc cur s' heq hcur_le hcur_suf (mergeLoopBin_eq_limit _ _ _ _ _ _ heq))
        hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
    · have hcur_lt : cur.length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
      refine chunkedHeaderReceived_uc_decode_key_step hFromCall hPushCall hVarintCall hle_lim hsp_align
        hcur_le hcur_lt hcur_suf hnone_cont ?_ hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
      intro key iwt rest s' hd hk_ge hwt hitag0 hpc' hrun' hsp' htr' hx0' hx1' hx19' hx20' hx21' hx22' hx23' hx24' hx25' hx26' hcs'
      obtain ⟨hx27', hx28', hvregs'⟩ := hcs'
      have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd; have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
      have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le; have hrest_lt : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest_le hbs_lt
      have hrest_suf : IsDropSuffix x.bs rest := suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
      have htag_lt : key.toNat / 8 < 2 ^ 32 := by omega
      have hstep := mergeLoopBin_of_key_ok (m := uc) (depth' := 97)
        protoPrefixStep_unchunked_headerReceived_mergeField hle_lim hd hk_ge hwt hitag0
      by_cases htag1 : key.toNat / 8 = 1
      · rw [htag1] at hx1' hstep; rw [unchunkedHeaderReceived_mergeField_tag1] at hstep
        chunkedHeaderReceivedMerge_fetches img.base H 468 24
        generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName = entry; examples_hide_fetches
        by_cases hiwt : iwt = .varint
        · subst hiwt; apply SepWPpIn.of_sepWP (mid := entry + 556#64); wp_steps; wp_reach
          refine htag1_varint hsp_align hrest_le hrest_lt hrest_suf
            (fun hdv => hnone_cont (by simp [hstep, hdv]))
            (fun v rest' s'' hdv hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs'' => ?_)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr']) (by simp only [arm64_norm, hx0', WireType.toNat]) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20']) (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23']) (by simp only [arm64_norm, hx24']) (by simp only [arm64_norm, hx25']) (by simp only [arm64_norm, hx26'])
            ⟨by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩
          have hr'_lt : rest'.length < rest.length := decodeVarint_length hdv; have hr'_le : rest'.length ≤ rest.length := Nat.le_of_lt hr'_lt
          have hstep1 : mergeLoopBin V1State.Unchunked.HeaderReceived.mergeField (cur.length - innerLimit) uc cur innerLimit 97 =
              mergeLoopBin V1State.Unchunked.HeaderReceived.mergeField (rest'.length - innerLimit) { uc with epoch := v } rest' innerLimit 97 := by simp [hstep, hdv]
          exact ih { uc with epoch := v } rest' s'' (by omega) (Nat.le_trans hr'_le hrest_le)
            (suffix_trans hrest_le hrest_suf hr'_le (decodeVarint_suffix hdv))
            (fun uc' r'' s3 heq hr''_le hr''_suf hml => hok_cont uc' r'' s3 heq hr''_le hr''_suf (hstep1.trans hml))
            (fun hml => hnone_cont (hstep1.trans hml))
            hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs''
        · apply SepWPpIn.of_sepWP (mid := entry + 556#64); wp_steps; wp_reach
          exact htag1_wt_err hiwt hsp_align hrest_le hrest_suf (hnone_cont (by simp [hstep, hiwt]))
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr']) (by simp only [arm64_norm, hx0']) ⟨by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩
      · by_cases htag2 : key.toNat / 8 = 2
        · rw [htag2] at hx1' hstep; rw [unchunkedHeaderReceived_mergeField_tag2] at hstep
          chunkedHeaderReceivedMerge_fetches img.base H 468 24
          generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName = entry; examples_hide_fetches
          apply SepWPpIn.of_sepWP (mid := entry + 512#64); wp_steps; wp_reach
          refine htag2_step iwt hsp_align hrest_le hrest_lt hrest_suf
            (fun hauth => hnone_cont (by simp [hstep, hauth]))
            (fun auth' rest' s'' hauth hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs'' => ?_)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr']) (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20']) (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23']) (by simp only [arm64_norm, hx24']) (by simp only [arm64_norm, hx25']) (by simp only [arm64_norm, hx26'])
            ⟨by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩
          have hr'_le : rest'.length ≤ rest.length := (proto_mergeMessage_suffix hauth).1
          have hstep2 : mergeLoopBin V1State.Unchunked.HeaderReceived.mergeField (cur.length - innerLimit) uc cur innerLimit 97 =
              mergeLoopBin V1State.Unchunked.HeaderReceived.mergeField (rest'.length - innerLimit) { uc with auth := some auth' } rest' innerLimit 97 := by simp [hstep, hauth]
          exact ih { uc with auth := some auth' } rest' s'' (by omega) (Nat.le_trans hr'_le hrest_le)
            (suffix_trans hrest_le hrest_suf hr'_le (proto_mergeMessage_suffix hauth).2)
            (fun uc' r'' s3 heq hr''_le hr''_suf hml => hok_cont uc' r'' s3 heq hr''_le hr''_suf (hstep2.trans hml))
            (fun hml => hnone_cont (hstep2.trans hml))
            hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs''
        · by_cases htag3 : key.toNat / 8 = 3
          · rw [htag3] at hx1' hstep; rw [unchunkedHeaderReceived_mergeField_tag3] at hstep
            chunkedHeaderReceivedMerge_fetches img.base H 468 24
            generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName = entry; examples_hide_fetches
            apply SepWPpIn.of_sepWP (mid := entry + 392#64); wp_steps; wp_reach
            refine htag3_step iwt hsp_align hrest_le hrest_lt hrest_suf
              (fun hmb => hnone_cont (by simp [hstep, hmb]))
              (fun v rest' s'' hmb hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs'' => ?_)
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr']) (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20']) (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23']) (by simp only [arm64_norm, hx24']) (by simp only [arm64_norm, hx25']) (by simp only [arm64_norm, hx26'])
              ⟨by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩
            have hr'_le : rest'.length ≤ rest.length := mergeBytes_length hmb
            have hstep3 : mergeLoopBin V1State.Unchunked.HeaderReceived.mergeField (cur.length - innerLimit) uc cur innerLimit 97 =
                mergeLoopBin V1State.Unchunked.HeaderReceived.mergeField (rest'.length - innerLimit) { uc with hdr := v } rest' innerLimit 97 := by simp [hstep, hmb]
            exact ih { uc with hdr := v } rest' s'' (by omega) (Nat.le_trans hr'_le hrest_le)
              (suffix_trans hrest_le hrest_suf hr'_le (mergeBytes_suffix hmb))
              (fun uc' r'' s3 heq hr''_le hr''_suf hml => hok_cont uc' r'' s3 heq hr''_le hr''_suf (hstep3.trans hml))
              (fun hml => hnone_cont (hstep3.trans hml))
              hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs''
          · obtain ⟨hb1_1, _⟩ := itag_beq_tag_false htag1 htag_lt (by decide : 1 < 2 ^ 32)
            obtain ⟨hb2_1, _⟩ := itag_beq_tag_false htag2 htag_lt (by decide : 2 < 2 ^ 32); obtain ⟨hb3_1, _⟩ := itag_beq_tag_false htag3 htag_lt (by decide : 3 < 2 ^ 32)
            have hb1_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 1#32) = false := by rw [sf_truncate32_ofNat64]; exact hb1_1
            have hb2_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 2#32) = false := by rw [sf_truncate32_ofNat64]; exact hb2_1
            have hb3_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 3#32) = false := by rw [sf_truncate32_ofNat64]; exact hb3_1
            rw [unchunkedHeaderReceived_mergeField_other uc iwt rest 97 htag_lt htag1 htag2 htag3] at hstep
            chunkedHeaderReceivedMerge_fetches img.base H 468 24
            generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedHeaderReceivedMergeName = entry; examples_hide_fetches
            apply SepWPpIn.of_sepWP (mid := entry + 492#64); wp_steps; wp_reach
            refine hskip_step iwt (key.toNat / 8) hsp_align hrest_le hrest_lt hrest_suf htag_lt
              (fun hsf => hnone_cont (by simp [hstep, hsf]))
              (fun rest' s'' hsf hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs'' => ?_)
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr']) (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx1', sf_truncate32_ofNat64]) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20']) (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23']) (by simp only [arm64_norm, hx24']) (by simp only [arm64_norm, hx25']) (by simp only [arm64_norm, hx26'])
              ⟨by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩
            have hr'_le : rest'.length ≤ rest.length := (skip_length (2 * rest.length + 2)).1 _ _ _ _ _ hsf
            have hstep_other : mergeLoopBin V1State.Unchunked.HeaderReceived.mergeField (cur.length - innerLimit) uc cur innerLimit 97 =
                mergeLoopBin V1State.Unchunked.HeaderReceived.mergeField (rest'.length - innerLimit) uc rest' innerLimit 97 := by simp [hstep, hsf]
            exact ih uc rest' s'' (by omega) (Nat.le_trans hr'_le hrest_le)
              (suffix_trans hrest_le hrest_suf hr'_le ((skip_suffix (2 * rest.length + 2)).1 _ _ _ _ _ hsf))
              (fun uc' r'' s3 heq hr''_le hr''_suf hml => hok_cont uc' r'' s3 heq hr''_le hr''_suf (hstep_other.trans hml))
              (fun hml => hnone_cont (hstep_other.trans hml))
              hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs''

set_option quotPrecheck false in
local notation "entry" => (blkPl_306).base

theorem chunkedHeaderReceived_ret_err_exit_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    {x : ChunkedHeaderReceivedMergeGhost} {R : SepProp} {s0 : State} {m : V1State.Chunked.HeaderReceived} {s : State} {err : BitVec 64} {n : Nat}
    (hnone : (Proto.mergeMessage V1State.Chunked.HeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none) (hn : n ≤ 3) (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hpc : s.pc = (blkPl_306).base + 128#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = err) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_306).rebase (blkPl_306).base H) (s0.readReg64 Reg.lr) s
      (decodeErrorAtStackLen A err n ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chunkedHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  apply SepWPpLscro.of_sepWP_ret; unfold WppPost chunkedHeaderReceivedMergeSpec
  simp only [hnone, chunkedHeaderReceivedErrFrame, chunkedInlSavedRegs10, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp, hx0]
  apply SepWP.fold (decodeErrorWith_le3_hr A err hn) (by sep_focus)
  apply SepWP.fold (chunkedHeaderReceivedPBAt_entails_exists A x.msgPtr m) (by sep_focus)
  wp_steps; apply SepWP.fold (stackAt_chunkedInl10_epilogue s0.sp s0) (by unfold chunkedInlSavedRegs10; sep_focus); wp_done

theorem chunkedHeaderReceived_from_err_exit_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 261) (decodeErrorFromSpec A))
    {x : ChunkedHeaderReceivedMergeGhost} {R : SepProp} {s0 : State} {m : V1State.Chunked.HeaderReceived} {s : State} {w : BitVec 64}
    (hnone : (Proto.mergeMessage V1State.Chunked.HeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none) (hw : KindNoHeap w) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hpc : s.pc = (blkPl_306).base + 120#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_306).rebase (blkPl_306).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ w) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chunkedHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  apply SepWPpLscro.of_sepWP (mid := lsmpl.base 261)
  conv => arg 4; rw [chunkedHeaderReceivedErrFrame, chunkedInlBelow_decodeErrorHook s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpLscro.call_frame (x := (s0.sp - 128#64, w))
    (ret_pc := entry + 128#64) hFromCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorFromSpec]; simp only [arm64_norm, hsp]; rfl) hw (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, _, _, _, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx27, hx28, hvregs] at hpcm hspm hx27_m hx28_m hvregs_m
  apply SepWPpLscro.of_sepWP_ret; unfold WppPost chunkedHeaderReceivedMergeSpec
  simp only [decodeErrorFromSpec, hnone, chunkedHeaderReceivedErrFrame, chunkedInlSavedRegs10, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp, hspm]
  apply SepWP.fold (chunkedInlBelow_decodeErrorHook_entails s0.sp) (by sep_focus)
  apply SepWP.fold (memRegion8_memRegion40_entails_48_160 s0.sp) (by sep_focus)
  apply SepWP.fold (decodeErrorWith_le3_hr A (sm.readReg64 (Reg.gpr 0#5)) (by decide : 0 ≤ 3)) (by sep_focus)
  apply SepWP.fold (chunkedHeaderReceivedPBAt_entails_exists A x.msgPtr m) (by sep_focus)
  wp_steps; apply SepWP.fold (stackAt_chunkedInl10_epilogue s0.sp s0) (by unfold chunkedInlSavedRegs10; sep_focus); wp_done

theorem chunkedHeaderReceived_push_ret_exit_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    {x : ChunkedHeaderReceivedMergeGhost} {R : SepProp} {s0 : State} {m : V1State.Chunked.HeaderReceived} {s : State} {err : BitVec 64} {n : Nat}
    (hnone : (Proto.mergeMessage V1State.Chunked.HeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none) (hn : n ≤ 2) (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hpc : s.pc = (blkPl_306).base + 760#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = s0.sp - 128#64) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_306).rebase (blkPl_306).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A err n ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chunkedHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; have hret := @chunkedHeaderReceived_ret_err_exit_placed _ A H x R s0 m
  apply SepWPpLscro.of_sepWP (mid := lsmpl.base 257)
  conv => arg 4; rw [chunkedHeaderReceivedErrFrame, chunkedInlBelow_decodeErrorHook s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpLscro.call_frame (x := (s0.sp - 128#64, err, n))
    (ret_pc := entry + 764#64) hPushCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorPushSpec]; simp only [arm64_norm, hsp, hx0]; rfl)
    (by omega : n < 2 ^ 32) (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, _, _, _, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx27, hx28, hvregs] at hpcm hspm hx27_m hx28_m hvregs_m
  apply SepWPpLscro.of_sepWP (mid := entry + 128#64)
  (conv => arg 4; simp only [decodeErrorPushSpec, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; intro htrm
  apply SepWP.fold (chunkedInlBelow_decodeErrorHook_entails s0.sp) (by sep_focus); wp_steps
  apply SepWP.fold (pointsTo64_memRegion40_entails_48_160 s0.sp err) (by sep_focus); wp_reach
  apply SepWPpLscro.weaken_pre (P' := decodeErrorAtStackLen A err (n + 1) ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
    (by dsimp only [chunkedHeaderReceivedErrFrame]; sep_entail)
  exact hret hnone (by omega : n + 1 ≤ 3) herr hsp_align
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])
    ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

theorem chunkedHeaderReceived_uc_push_exit_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    {x : ChunkedHeaderReceivedMergeGhost} {R : SepProp} {s0 : State} {m : V1State.Chunked.HeaderReceived} {s : State} {err : BitVec 64} {n : Nat}
    (hnone : (Proto.mergeMessage V1State.Chunked.HeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none) (hn : n ≤ 2) (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hpc : s.pc = (blkPl_306).base + 728#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hx1 : s.readReg64 (Reg.gpr 1#5) = err) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_306).rebase (blkPl_306).base H) (s0.readReg64 Reg.lr) s
      (decodeErrorAtStackLen A err n ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chunkedHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; have hpush := @chunkedHeaderReceived_push_ret_exit_placed _ A H hPushCall x R s0 m
  apply SepWPpLscro.of_sepWP (mid := entry + 760#64)
  conv => arg 4; rw [memRegion_48_cells1_160 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, hx1]
  apply SepWP.exists_elim; intro v_stk0; wp_steps; wp_reach
  apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A err n ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
    (by sep_entail)
  exact hpush hnone hn herr hsp_align
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hsp])
    ⟨by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩

theorem chunkedHeaderReceived_uc_from_push_exit_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 261) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    {x : ChunkedHeaderReceivedMergeGhost} {R : SepProp} {s0 : State} {m : V1State.Chunked.HeaderReceived} {s : State} {w : BitVec 64}
    (hnone : (Proto.mergeMessage V1State.Chunked.HeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none) (hw : KindNoHeap w) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hpc : s.pc = (blkPl_306).base + 716#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_306).rebase (blkPl_306).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ w) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chunkedHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; have hpush := @chunkedHeaderReceived_uc_push_exit_placed _ A H hPushCall x R s0 m
  apply SepWPpLscro.of_sepWP (mid := lsmpl.base 261)
  conv => arg 4; rw [chunkedHeaderReceivedErrFrame, chunkedInlBelow_decodeErrorHook s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpLscro.call_frame (x := (s0.sp - 128#64, w))
    (ret_pc := entry + 724#64) hFromCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorFromSpec]; simp only [arm64_norm, hsp]; rfl) hw (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, _, _, _, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx27, hx28, hvregs] at hpcm hspm hx27_m hx28_m hvregs_m
  apply SepWPpLscro.of_sepWP (mid := entry + 728#64)
  (conv => arg 4; simp only [decodeErrorFromSpec, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨hsm0, htrm⟩
  apply SepWP.fold (chunkedInlBelow_decodeErrorHook_entails s0.sp) (by sep_focus)
  apply SepWP.fold (memRegion8_memRegion40_entails_48_160 s0.sp) (by sep_focus)
  wp_steps; wp_reach
  apply SepWPpLscro.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
    (by dsimp only [chunkedHeaderReceivedErrFrame]; sep_entail)
  exact hpush hnone (by decide : 0 ≤ 2) hsm0 hsp_align
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])
    ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

theorem chunkedHeaderReceived_uc_field_push_exit_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    {x : ChunkedHeaderReceivedMergeGhost} {R : SepProp} {s0 : State} {m : V1State.Chunked.HeaderReceived} {s : State} {err : BitVec 64} {n : Nat}
    (hnone : (Proto.mergeMessage V1State.Chunked.HeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none) (hn : n ≤ 1) (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hpc : s.pc = (blkPl_306).base + 988#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = s0.sp - 128#64) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_306).rebase (blkPl_306).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A err n ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chunkedHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; have hpush := @chunkedHeaderReceived_uc_push_exit_placed _ A H hPushCall x R s0 m
  apply SepWPpLscro.of_sepWP (mid := lsmpl.base 257)
  conv => arg 4; rw [chunkedHeaderReceivedErrFrame, chunkedInlBelow_decodeErrorHook s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpLscro.call_frame (x := (s0.sp - 128#64, err, n))
    (ret_pc := entry + 992#64) hPushCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorPushSpec]; simp only [arm64_norm, hsp, hx0]; rfl) (by omega : n < 2 ^ 32) (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, _, _, _, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx27, hx28, hvregs] at hpcm hspm hx27_m hx28_m hvregs_m
  apply SepWPpLscro.of_sepWP (mid := entry + 728#64)
  (conv => arg 4; simp only [decodeErrorPushSpec, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; intro htrm
  apply SepWP.fold (chunkedInlBelow_decodeErrorHook_entails s0.sp) (by sep_focus); wp_steps
  apply SepWP.fold (pointsTo64_memRegion40_entails_48_160 s0.sp err) (by sep_focus); wp_reach
  apply SepWPpLscro.weaken_pre (P' := decodeErrorAtStackLen A err (n + 1) ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
    (by dsimp only [chunkedHeaderReceivedErrFrame]; sep_entail)
  exact hpush hnone (by omega : n + 1 ≤ 2) herr hsp_align
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])
    ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

theorem chunkedHeaderReceived_uc_skip_step_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    (hSkipCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 263) (skipField3Spec A))
    {x : ChunkedHeaderReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {ek : Option PolynomialDecoder} {uc : V1State.Unchunked.HeaderReceived}
    {rest : List (BitVec 8)} {iwt : WireType} {tag outerLimit innerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length) (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest) (htag_lt : tag < 2 ^ 32) (hnone_of_sf : skipField (2 * rest.length + 2) 97 tag iwt rest = none →
      (Proto.mergeMessage V1State.Chunked.HeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (rest' : List (BitVec 8)) (s' : State),
      skipField (2 * rest.length + 2) 97 tag iwt rest = some rest' →
      s'.pc = (blkPl_306).base + 416#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr → s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit → s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_306).rebase (blkPl_306).base H) (s0.readReg64 Reg.lr) s'
        (chunkedHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr ek uc x.bs rest')
        (WppPost (chunkedHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_306).base + 492#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat) (hx1 : (s.readReg64 (Reg.gpr 1#5)).setWidth 32 = BitVec.ofNat 32 tag) (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr) (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit) (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64) (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_306).rebase (blkPl_306).base H) (s0.readReg64 Reg.lr) s
      (chunkedHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr ek uc x.bs rest)
      (WppPost (chunkedHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hpush_exit := @chunkedHeaderReceived_uc_push_exit_placed _ A H hPushCall x R s0 { uc := some uc, receivingEk := ek }
  apply SepWPpLscro.of_sepWP (mid := lsmpl.base 263)
  conv => arg 4; rw [chunkedHeaderReceivedUcLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf, chunkedInlBelow_skipField97 s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpLscro.call_frame (x := ⟨iwt, tag, 97, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := entry + 504#64) hSkipCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
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
    apply SepWPpLscro.of_sepWP (mid := entry + 728#64)
    (conv => arg 4; simp only [skipField3Spec, hsf, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (chunkedInlBelow_skipField97_entails s0.sp) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus); apply SepWP.fold (unchunked3CapAt_entails_chunkedHeaderReceivedPBAt A x.msgPtr rest.length ek uc) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPpLscro.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc, receivingEk := ek } x.bs)
      (by dsimp only [chunkedHeaderReceivedErrFrame]; sep_entail)
    exact hpush_exit hnone (by decide : 0 ≤ 2) hsm0 hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])
      ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some rest' =>
    have hrest'_le : rest'.length ≤ rest.length := (skip_length _).1 _ _ _ _ _ hsf
    apply SepWPpLscro.of_sepWP (mid := entry + 416#64)
    (conv => arg 4; simp only [skipField3Spec, hsf, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    apply SepWP.fold (chunkedInlBelow_skipField97_entails s0.sp) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus); apply SepWP.fold (unchunked3CapAt_mono A x.msgPtr uc.epoch uc.auth uc.hdr hrest'_le) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPpLscro.weaken_pre (P' := chunkedHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr ek uc x.bs rest')
      (by dsimp only [chunkedHeaderReceivedUcLoopPre]; sep_entail)
    exact hcont rest' _ hsf
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m]) (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m]) (by simp only [arm64_norm, hx25_m]) (by simp only [arm64_norm, hx26_m])
      ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

theorem chunkedHeaderReceived_uc_tag1_varint_step_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 291) (decodeVarint2Spec A))
    {x : ChunkedHeaderReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {ek : Option PolynomialDecoder} {uc : V1State.Unchunked.HeaderReceived}
    {rest : List (BitVec 8)} {outerLimit innerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length) (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest) (hnone_of_dv : decodeVarint rest = none →
      (Proto.mergeMessage V1State.Chunked.HeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (v : BitVec 64) (rest' : List (BitVec 8)) (s' : State),
      decodeVarint rest = some (v, rest') →
      s'.pc = (blkPl_306).base + 416#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr → s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit → s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_306).rebase (blkPl_306).base H) (s0.readReg64 Reg.lr) s'
        (chunkedHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr ek { uc with epoch := v } x.bs rest')
        (WppPost (chunkedHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_306).base + 556#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = 0#64) (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr) (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit) (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64) (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_306).rebase (blkPl_306).base H) (s0.readReg64 Reg.lr) s
      (chunkedHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr ek uc x.bs rest)
      (WppPost (chunkedHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hfpush := @chunkedHeaderReceived_uc_field_push_exit_placed _ A H hPushCall x R s0 { uc := some uc, receivingEk := ek }
  apply SepWPpLscro.of_sepWP (mid := lsmpl.base 291)
  conv => arg 4; rw [chunkedHeaderReceivedUcLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf, chunkedInlBelow_decodeVarint2 s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpLscro.call_frame (x := ⟨x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := entry + 568#64) hVarintCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, hsp, hx19]; rfl)
    hrest_lt (by sep_focus) (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
  cases hdv : decodeVarint rest with
  | none =>
    have hnone := hnone_of_dv hdv
    apply SepWPpLscro.of_sepWP (mid := entry + 988#64)
    (conv => arg 4; simp only [decodeVarint2Spec, hdv, memRegion_48_cells1_160 s0.sp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp])
    apply SepWP.exists_elim; intro v_stk0; apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
    have hcbnz_err : (sm.readReg64 (Reg.gpr 1#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm1
    apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus); apply SepWP.fold (unchunked3CapAt_entails_chunkedHeaderReceivedPBAt A x.msgPtr rest.length ek uc) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 1#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc, receivingEk := ek } x.bs)
      (by dsimp only [chunkedHeaderReceivedErrFrame]; sep_entail)
    exact hfpush hnone (by decide : 0 ≤ 1) hsm1 hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm, hspm])
      ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨v, rest'⟩
    have hrest'_le : rest'.length ≤ rest.length := Nat.le_of_lt (decodeVarint_length hdv)
    apply SepWPpLscro.of_sepWP (mid := entry + 416#64)
    (conv => arg 4; simp only [decodeVarint2Spec, hdv, unchunked3CapAt_eq_hr, sepConj_assoc, arm64_norm, hsp])
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
    apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus); apply SepWP.fold (vecU8CapAt_hr_mono A x.msgPtr uc.hdr hrest'_le) (by sep_focus); apply SepWP.fold (optAuthenticatorPBCapAt_mono A (x.msgPtr + 0x18#64) uc.auth hrest'_le) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPpLscro.weaken_pre (P' := chunkedHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr ek { uc with epoch := v } x.bs rest')
      (by dsimp only [chunkedHeaderReceivedUcLoopPre]; rw [unchunked3CapAt_eq_hr]; simp only [arm64_norm]; sep_entail)
    exact hcont v rest' _ hdv
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m]) (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m]) (by simp only [arm64_norm, hx25_m]) (by simp only [arm64_norm, hx26_m])
      ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

theorem chunkedHeaderReceived_uc_tag1_wt_err_step_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 261) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    {x : ChunkedHeaderReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {ek : Option PolynomialDecoder} {uc : V1State.Unchunked.HeaderReceived}
    {rest : List (BitVec 8)} {iwt : WireType}
    (hiwt : iwt ≠ .varint) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length) (hrest_suf : IsDropSuffix x.bs rest) (hnone : (Proto.mergeMessage V1State.Chunked.HeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none) (hpc : s.pc = (blkPl_306).base + 556#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_306).rebase (blkPl_306).base H) (s0.readReg64 Reg.lr) s
      (chunkedHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr ek uc x.bs rest)
      (WppPost (chunkedHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hcbnz_wt : (BitVec.ofNat 64 iwt.toNat == 0#64) = false := iwt_cbnz_true_of_ne_varint hiwt
  have hfpush := @chunkedHeaderReceived_uc_field_push_exit_placed _ A H hPushCall x R s0 { uc := some uc, receivingEk := ek }
  apply SepWPpLscro.of_sepWP (mid := lsmpl.base 261)
  conv => arg 4; rw [chunkedHeaderReceivedUcLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, chunkedInlBelow_decodeErrorHook s0.sp, memRegion_48_wtErr160 s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro b_wt1; apply SepWP.exists_elim; intro b_wt0; apply SepWP.exists_elim; intro v_wt0
  wp_steps
  apply SepWP.fold (wtErr160_entails_memRegion40 s0.sp _ _) (by sep_focus)
  apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
  apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
  apply SepWP.fold (unchunked3CapAt_entails_chunkedHeaderReceivedPBAt A x.msgPtr rest.length ek uc) (by sep_focus)
  wp_reach
  refine SepWPpLscro.call_frame (x := (s0.sp - 128#64, 0x8000000000000006#64))
    (ret_pc := entry + 952#64) hFromCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorFromSpec]; simp only [arm64_norm, hsp]; rfl)
    (by decide : KindNoHeap 0x8000000000000006#64) (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, _, _, _, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx27, hx28, hvregs] at hpcm hspm hx27_m hx28_m hvregs_m
  apply SepWPpLscro.of_sepWP (mid := entry + 988#64)
  (conv => arg 4; simp only [decodeErrorFromSpec, memRegion_48_cells1_160 s0.sp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp])
  apply SepWP.exists_elim; intro v_stk0; apply SepWP.pure_elim; rintro ⟨hsm0, htrm⟩
  apply SepWP.fold (chunkedInlBelow_decodeErrorHook_entails s0.sp) (by sep_focus)
  wp_steps; wp_reach
  apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc, receivingEk := ek } x.bs)
    (by dsimp only [chunkedHeaderReceivedErrFrame]; sep_entail)
  exact hfpush hnone (by decide : 0 ≤ 1) hsm0 hsp_align
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm, hspm])
    ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

theorem chunkedHeaderReceived_uc_auth_init_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    {x : ChunkedHeaderReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {ek : Option PolynomialDecoder} {uc : V1State.Unchunked.HeaderReceived} {rest : List (BitVec 8)}
    (hcont : ∀ (s' : State),
      s'.pc = (blkPl_306).base + 536#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s.trace →
      s'.readReg64 (Reg.gpr 0#5) = s.readReg64 (Reg.gpr 0#5) → s'.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr → s'.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) → s'.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) → s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) → s'.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) → s'.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_306).rebase (blkPl_306).base H) (s0.readReg64 Reg.lr) s'
        (authenticatorPBCapAt A (x.msgPtr + 0x18#64) rest.length (uc.auth.getD default) ∗
          vecU8CapAt_hr A x.msgPtr rest.length uc.hdr ∗
          ((x.msgPtr + 0x48#64) ↦₆₄ uc.epoch) ∗ optPolynomialDecoderPBAt A (x.msgPtr + 80#64) ek ∗
          stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗
          chunkedInlSavedRegs10 s0.sp s0 ∗ (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool)
        (WppPost (chunkedHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_306).base + 512#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr) (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_306).rebase (blkPl_306).base H) (s0.readReg64 Reg.lr) s
      (chunkedHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr ek uc x.bs rest)
      (WppPost (chunkedHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  rcases hauth : uc.auth with _ | auth
  · rw [hauth] at hcont
    apply SepWPpLscro.of_sepWP (mid := entry + 536#64)
    conv => arg 4; rw [chunkedHeaderReceivedUcLoopPre, unchunked3CapAt_eq_hr, hauth, optAuthenticatorPBCapAt, memRegion_40_cells (x.msgPtr + 0x18#64)]
    simp only [noneCap, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm]
    apply SepWP.exists_elim; intro w1; apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3; apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5
    wp_steps
    have hdef := default_cells_entails_authenticatorPBCapAt A (x.msgPtr + 0x18#64) rest.length
    simp only [arm64_norm] at hdef; apply SepWP.fold hdef (by sep_focus); wp_reach
    apply SepWPpLscro.weaken_pre (P' := authenticatorPBCapAt A (x.msgPtr + 0x18#64) rest.length (Option.getD none default) ∗ vecU8CapAt_hr A x.msgPtr rest.length uc.hdr ∗ ((x.msgPtr + 0x48#64) ↦₆₄ uc.epoch) ∗ optPolynomialDecoderPBAt A (x.msgPtr + 80#64) ek ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedInlSavedRegs10 s0.sp s0 ∗ (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool)
      (Entails.of_eq rfl)
    exact hcont _ (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
      (by try simp only [arm64_norm]) (by try simp only [arm64_norm]) (by try simp only [arm64_norm])
      (by simp only [arm64_norm, hx20]) (by try simp only [arm64_norm]) (by try simp only [arm64_norm]) (by simp only [arm64_norm, hx23]) (by try simp only [arm64_norm]) (by try simp only [arm64_norm]) (by try simp only [arm64_norm])
      ⟨by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩
  · rw [hauth] at hcont
    apply SepWPpLscro.of_sepWP (mid := entry + 536#64)
    conv => arg 4; rw [chunkedHeaderReceivedUcLoopPre, unchunked3CapAt_eq_hr, hauth, optAuthenticatorPBCapAt]
    simp only [sepConj_assoc, arm64_norm]
    have hcmn_in := authenticatorPBCapAt_entails_cmn_hr A (x.msgPtr + 0x18#64) rest.length auth
    simp only [arm64_norm] at hcmn_in; apply SepWP.fold hcmn_in (by sep_focus)
    wp_simp_pre [sepExists_sepConj_left, sepConj_assoc, arm64_norm]
    apply SepWP.exists_elim; intro cap_ik; apply SepWP.exists_elim; intro ptr_ik
    apply SepWP.pure_elim; rintro ⟨hcap_lt, hcap_ok⟩
    have hcmn1 := cap_add_one_beq_zero_false hcap_lt; have hcmn2 := cap_add_one_bne_zero_true hcap_lt
    wp_steps
    have hcmn_out := cmn_entails_authenticatorPBCapAt_hr A (x.msgPtr + 0x18#64) rest.length auth cap_ik ptr_ik hcap_ok
    simp only [arm64_norm] at hcmn_out; apply SepWP.fold hcmn_out (by sep_focus); wp_reach
    apply SepWPpLscro.weaken_pre (P' := authenticatorPBCapAt A (x.msgPtr + 0x18#64) rest.length (Option.getD (some auth) default) ∗ vecU8CapAt_hr A x.msgPtr rest.length uc.hdr ∗ ((x.msgPtr + 0x48#64) ↦₆₄ uc.epoch) ∗ optPolynomialDecoderPBAt A (x.msgPtr + 80#64) ek ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedInlSavedRegs10 s0.sp s0 ∗ (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool)
      (Entails.of_eq rfl)
    exact hcont _ (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
      (by try simp only [arm64_norm]) (by try simp only [arm64_norm]) (by try simp only [arm64_norm])
      (by simp only [arm64_norm, hx20]) (by try simp only [arm64_norm]) (by try simp only [arm64_norm]) (by simp only [arm64_norm, hx23]) (by try simp only [arm64_norm]) (by try simp only [arm64_norm]) (by try simp only [arm64_norm])
      ⟨by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩

theorem chunkedHeaderReceived_uc_tag2_step_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    (hAuthCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A)))
    {x : ChunkedHeaderReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {ek : Option PolynomialDecoder} {uc : V1State.Unchunked.HeaderReceived} {rest : List (BitVec 8)}
    {iwt : WireType} {outerLimit innerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length) (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest) (hnone_of_auth :
      (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto iwt) (uc.auth.getD default) rest 97).toOption = none →
      (Proto.mergeMessage V1State.Chunked.HeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (auth' : ProtoAuthenticator) (rest' : List (BitVec 8)) (s' : State),
      (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto iwt) (uc.auth.getD default) rest 97).toOption = some (auth', rest') →
      s'.pc = (blkPl_306).base + 416#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr → s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit → s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_306).rebase (blkPl_306).base H) (s0.readReg64 Reg.lr) s'
        (chunkedHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr ek { uc with auth := some auth' } x.bs rest')
        (WppPost (chunkedHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_306).base + 512#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat) (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr) (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit) (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64) (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_306).rebase (blkPl_306).base H) (s0.readReg64 Reg.lr) s
      (chunkedHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr ek uc x.bs rest)
      (WppPost (chunkedHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  have hfpush := fun {auth' : ProtoAuthenticator} => @chunkedHeaderReceived_uc_field_push_exit_placed _ A H hPushCall x R s0 { uc := some { epoch := uc.epoch, auth := some auth', hdr := uc.hdr }, receivingEk := ek }
  refine chunkedHeaderReceived_uc_auth_init_placed ?_ hpc hrun hsp hx20 hx23 hcs
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hcs1
  rw [htr] at htr1; rw [hx0] at hx0_1; rw [hx19] at hx19_1; rw [hx21] at hx21_1
  rw [hx22] at hx22_1; rw [hx24] at hx24_1; rw [hx25] at hx25_1; rw [hx26] at hx26_1
  obtain ⟨hx27_1, hx28_1, hvregs_1⟩ := hcs1; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  apply SepWPpLscro.of_sepWP (mid := lsmpl.base 295)
  conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, chunkedInlBelow_authMerge s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpLscro.call_frame_lscro (x := ⟨iwt, x.msgPtr + 0x18#64, uc.auth.getD default, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := entry + 548#64) hAuthCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
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
    apply SepWPpLscro.of_sepWP (mid := entry + 988#64)
    (conv => arg 4; simp only [authMergeSpec, hauth_res, memRegion_48_cells1_160 s0.sp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp1])
    apply SepWP.exists_elim; intro v_stk0; apply SepWP.exists_elim; intro auth'; apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; intro hpure
    have htrm : sm.trace = _ := hpure.1; have hsm0 : sm.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hpure.2.1; have hn_err : n_err ≤ 1 := hpure.2.2
    have hcbz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (chunkedInlBelow_authMerge_entails s0.sp) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus); apply SepWP.fold (vecU8CapAt_hr_entails_vecU8 A x.msgPtr rest.length uc.hdr) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some { epoch := uc.epoch, auth := some auth', hdr := uc.hdr }, receivingEk := ek } x.bs)
      (by dsimp only [chunkedHeaderReceivedErrFrame, chunkedHeaderReceivedPBAt, optHeaderReceivedPBAt, headerReceivedPBAt, unchunked3At, optAuthenticatorPBAt]; simp only [arm64_norm]; sep_entail)
    exact hfpush hnone hn_err hsm0 hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr1]) (by simp only [arm64_norm, hspm]) ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨auth', rest'⟩
    have hrest'_le : rest'.length ≤ rest.length := (proto_mergeMessage_suffix hauth_res).1
    apply SepWPpLscro.of_sepWP (mid := entry + 416#64)
    (conv => arg 4; simp only [authMergeSpec, hauth_res, sepConj_assoc, arm64_norm, hsp1])
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    apply SepWP.fold (chunkedInlBelow_authMerge_entails s0.sp) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus); apply SepWP.fold (vecU8CapAt_hr_mono A x.msgPtr uc.hdr hrest'_le) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPpLscro.weaken_pre (P' := chunkedHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr ek { uc with auth := some auth' } x.bs rest')
      (by dsimp only [chunkedHeaderReceivedUcLoopPre]; rw [unchunked3CapAt_eq_hr]; dsimp only [optAuthenticatorPBCapAt]; simp only [arm64_norm]; sep_entail)
    exact hcont auth' rest' _ hauth_res (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr1])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m]) (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m]) (by simp only [arm64_norm, hx25_m]) (by simp only [arm64_norm, hx26_m]) ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

theorem chunkedHeaderReceived_uc_tag3_step_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    (hBytesCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A)))
    {x : ChunkedHeaderReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {ek : Option PolynomialDecoder} {uc : V1State.Unchunked.HeaderReceived} {rest : List (BitVec 8)}
    {iwt : WireType} {outerLimit innerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length) (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest) (hnone_of_mb : mergeBytes iwt rest = none →
      (Proto.mergeMessage V1State.Chunked.HeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (v rest' : List (BitVec 8)) (s' : State),
      mergeBytes iwt rest = some (v, rest') →
      s'.pc = (blkPl_306).base + 416#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr → s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit → s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_306).rebase (blkPl_306).base H) (s0.readReg64 Reg.lr) s'
        (chunkedHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr ek { uc with hdr := v } x.bs rest')
        (WppPost (chunkedHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_306).base + 392#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat) (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr) (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit) (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64) (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_306).rebase (blkPl_306).base H) (s0.readReg64 Reg.lr) s
      (chunkedHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr ek uc x.bs rest)
      (WppPost (chunkedHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hfpush := @chunkedHeaderReceived_uc_field_push_exit_placed _ A H hPushCall x R s0 { uc := some uc, receivingEk := ek }
  apply SepWPpLscro.of_sepWP (mid := lsmpl.base 290)
  conv => arg 4; rw [chunkedHeaderReceivedUcLoopPre, unchunked3CapAt, sliceCursorAfter_eq_split hrest_le hrest_suf, chunkedInlBelow_bytesMerge3 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro cap_hdr; apply SepWP.exists_elim; intro ptr_hdr; apply SepWP.pure_elim; intro hcap_hdr
  wp_steps; wp_reach
  refine SepWPpLscro.call_frame_lscro (x := ⟨iwt, x.msgPtr, cap_hdr, ptr_hdr, uc.hdr, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := entry + 404#64) hBytesCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [bytesMerge3RawSpec]; simp only [arm64_norm, hsp, hx0, hx20, hx19, setWidth8_ofNat64_wt]; rfl)
    (⟨hrest_lt, hcap_hdr⟩ : rest.length < 2 ^ 63 ∧ BytesMergeCapOk cap_hdr rest.length) (by sep_focus) (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [bytesMerge3RawSpec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
  cases hmb : mergeBytes iwt rest with
  | none =>
    have hnone := hnone_of_mb hmb
    apply SepWPpLscro.of_sepWP (mid := entry + 988#64)
    (conv => arg 4; simp only [bytesMerge3RawSpec, hmb, memRegion_48_cells1_160 s0.sp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp])
    apply SepWP.exists_elim; intro v_stk0; apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (chunkedInlBelow_bytesMerge3_entails s0.sp) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    have hhdr : vecU8At A x.msgPtr cap_hdr ptr_hdr uc.hdr ⊢ rustBytesVecAt A x.msgPtr uc.hdr :=
      Entails.sepExists_right cap_hdr (Entails.sepExists_right ptr_hdr (Entails.refl _))
    apply SepWP.fold hhdr (by sep_focus); apply SepWP.fold (optAuthenticatorPBCapAt_entails_optAuthenticatorPBAt A (x.msgPtr + 0x18#64) rest.length uc.auth) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc, receivingEk := ek } x.bs)
      (by dsimp only [chunkedHeaderReceivedErrFrame, chunkedHeaderReceivedPBAt, optHeaderReceivedPBAt, headerReceivedPBAt, unchunked3At]; sep_entail)
    exact hfpush hnone (by decide : 0 ≤ 1) hsm0 hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm, hspm]) ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨v, rest'⟩
    have hrest'_le : rest'.length ≤ rest.length := mergeBytes_length hmb
    apply SepWPpLscro.of_sepWP (mid := entry + 416#64)
    (conv => arg 4; simp only [bytesMerge3RawSpec, hmb, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp])
    apply SepWP.exists_elim; intro cap_hdr'; apply SepWP.exists_elim; intro ptr_hdr'
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hcap_hdr'⟩
    apply SepWP.fold (chunkedInlBelow_bytesMerge3_entails s0.sp) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    have hhdr_cap : vecU8At A x.msgPtr cap_hdr' ptr_hdr' v ⊢ (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap rest'.length⌝ ∗ vecU8At A x.msgPtr cap ptr v) :=
      Entails.trans (Entails.pure_right hcap_hdr' (Entails.refl _)) (Entails.sepExists_right cap_hdr' (Entails.sepExists_right ptr_hdr' (Entails.refl _)))
    apply SepWP.fold hhdr_cap (by sep_focus); apply SepWP.fold (optAuthenticatorPBCapAt_mono A (x.msgPtr + 0x18#64) uc.auth hrest'_le) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPpLscro.weaken_pre (P' := chunkedHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr ek { uc with hdr := v } x.bs rest')
      (by dsimp only [chunkedHeaderReceivedUcLoopPre, unchunked3CapAt]; sep_entail)
    exact hcont v rest' _ hmb (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m]) (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m]) (by simp only [arm64_norm, hx25_m]) (by simp only [arm64_norm, hx26_m]) ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

theorem chunkedHeaderReceived_uc_loop_le_exit_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 261) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    {x : ChunkedHeaderReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {ek : Option PolynomialDecoder} {uc : V1State.Unchunked.HeaderReceived}
    {cur : List (BitVec 8)} {outerLimit innerLimit : Nat}
    (hle_lim : cur.length ≤ innerLimit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hcur_le : cur.length ≤ x.bs.length) (hcur_suf : IsDropSuffix x.bs cur) (hlim_lt : innerLimit < 2 ^ 63) (hnone_of_lt : cur.length < innerLimit →
      (Proto.mergeMessage V1State.Chunked.HeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (s' : State),
      cur.length = innerLimit →
      s'.pc = (blkPl_306).base + 168#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr → s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit → s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_306).rebase (blkPl_306).base H) (s0.readReg64 Reg.lr) s'
        (chunkedHeaderReceivedLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc, receivingEk := ek } x.bs cur)
        (WppPost (chunkedHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_306).base + 416#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr) (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit) (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64) (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_306).rebase (blkPl_306).base H) (s0.readReg64 Reg.lr) s
      (chunkedHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr ek uc x.bs cur)
      (WppPost (chunkedHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  by_cases heq_lim : cur.length = innerLimit
  · obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq heq_lim
    apply SepWPpLscro.of_sepWP (mid := entry + 168#64)
    conv => arg 4; rw [chunkedHeaderReceivedUcLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt]
    simp only [sepConj_assoc]; wp_steps
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus); wp_reach
    apply SepWPpLscro.weaken_pre (P' := chunkedHeaderReceivedLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc, receivingEk := ek } x.bs cur)
      (by dsimp only [chunkedHeaderReceivedLoopPre, chunkedHeaderReceivedPBCapAt, optHeaderReceivedPBCapAt, unchunked3CapAt, sliceCursorAfter]; sep_entail)
    exact hcont _ heq_lim
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20]) (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24]) (by simp only [arm64_norm, hx25])
      ⟨by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩
  · have hlt_lim : cur.length < innerLimit := Nat.lt_of_le_of_ne hle_lim heq_lim
    obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_lt hlt_lim hlim_lt
    have hnone := hnone_of_lt hlt_lim
    have hfrom_push := @chunkedHeaderReceived_uc_from_push_exit_placed _ A H hFromCall hPushCall x R s0 { uc := some uc, receivingEk := ek }
    apply SepWPpLscro.of_sepWP (mid := entry + 716#64)
    conv => arg 4; rw [chunkedHeaderReceivedUcLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt, memRegion_48_cells1_160 s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v_stk0; wp_steps
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot curPtr (BitVec.ofNat 64 cur.length)) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus); apply SepWP.fold (unchunked3CapAt_entails_chunkedHeaderReceivedPBAt A x.msgPtr cur.length ek uc) (by sep_focus); wp_reach
    apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000008#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc, receivingEk := ek } x.bs)
      (by dsimp only [chunkedHeaderReceivedErrFrame]; sep_entail)
    exact hfrom_push hnone (by decide : KindNoHeap 0x8000000000000008#64) hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr])
      ⟨by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩

theorem chunkedHeaderReceived_uc_decode_key_step_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 261) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 291) (decodeVarint2Spec A))
    {x : ChunkedHeaderReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {ek : Option PolynomialDecoder} {uc : V1State.Unchunked.HeaderReceived}
    {cur : List (BitVec 8)} {outerLimit innerLimit : Nat}
    (hgt_lim : ¬ cur.length ≤ innerLimit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hcur_le : cur.length ≤ x.bs.length) (hcur_lt : cur.length < 2 ^ 63) (hcur_suf : IsDropSuffix x.bs cur) (hnone_of_uc_none :
      mergeLoopBin V1State.Unchunked.HeaderReceived.mergeField (cur.length - innerLimit) uc cur innerLimit 97 = none →
      (Proto.mergeMessage V1State.Chunked.HeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (key : BitVec 64) (iwt : WireType) (rest : List (BitVec 8)) (s' : State),
      decodeVarint cur = some (key, rest) → ¬ 2 ^ 32 ≤ key.toNat →
      WireType.ofNat? (key.toNat % 8) = some iwt → ¬ key.toNat / 8 < 1 →
      s'.pc = (blkPl_306).base + 468#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat → s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) → s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr → s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit → s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_306).rebase (blkPl_306).base H) (s0.readReg64 Reg.lr) s'
        (chunkedHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr ek uc x.bs rest)
        (WppPost (chunkedHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_306).base + 416#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr) (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit) (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64) (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_306).rebase (blkPl_306).base H) (s0.readReg64 Reg.lr) s
      (chunkedHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr ek uc x.bs cur)
      (WppPost (chunkedHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  have hpush_exit := @chunkedHeaderReceived_uc_push_exit_placed _ A H hPushCall x R s0 { uc := some uc, receivingEk := ek }
  have hfrom_push := @chunkedHeaderReceived_uc_from_push_exit_placed _ A H hFromCall hPushCall x R s0 { uc := some uc, receivingEk := ek }
  apply SepWPpLscro.of_sepWP (mid := lsmpl.base 291)
  conv => arg 4; rw [chunkedHeaderReceivedUcLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt, chunkedInlBelow_decodeVarint2 s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpLscro.call_frame (x := ⟨x.bufRef, x.slot, curPtr, cur⟩)
    (ret_pc := entry + 436#64) hVarintCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, hsp, hx19]; rfl)
    hcur_lt (by dsimp only [sliceCursorAt, curPtr]; sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
  cases hd : decodeVarint cur with
  | none =>
    have hnone := hnone_of_uc_none (mergeLoopBin_of_decodeVarint_none protoPrefixStep_unchunked_headerReceived_mergeField hgt_lim hd)
    apply SepWPpLscro.of_sepWP (mid := entry + 728#64)
    (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
    apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus); apply SepWP.fold (unchunked3CapAt_entails_chunkedHeaderReceivedPBAt A x.msgPtr cur.length ek uc) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPpLscro.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc, receivingEk := ek } x.bs)
      (by dsimp only [chunkedHeaderReceivedErrFrame]; sep_entail)
    exact hpush_exit hnone (by decide : 0 ≤ 2) hsm1 hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])
      ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨key, rest⟩
    have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
    have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
    have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le
    have hrest_suf : IsDropSuffix x.bs rest := suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
    let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
    by_cases hk_ge : 2 ^ 32 ≤ key.toNat
    · have hnone := hnone_of_uc_none (mergeLoopBin_of_key_ge protoPrefixStep_unchunked_headerReceived_mergeField hgt_lim hd hk_ge)
      have hshr := key_shr32_of_ge hk_ge
      apply SepWPpLscro.of_sepWP (mid := entry + 716#64)
      (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
      apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
      apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus); apply SepWP.fold (unchunked3CapAt_entails_chunkedHeaderReceivedPBAt A x.msgPtr cur.length ek uc) (by sep_focus)
      conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_cells2_160 s0.sp]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply SepWP.exists_elim; intro v_err0; apply SepWP.exists_elim; intro v_err1; wp_steps
      apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
      have h40 : ((s0.sp - 128#64 + 8#64) ↦₆₄ key) ∗ memRegion (s0.sp - 112#64) 32 ⊢ memRegion (s0.sp - 120#64) 40 := by
        rw [bv_sub_add_lit s0.sp 128 8]; exact cells2_memRegion32_entails_40_160 s0.sp key
      apply SepWP.fold h40 (by sep_focus); wp_reach
      apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000004#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc, receivingEk := ek } x.bs)
        (by dsimp only [chunkedHeaderReceivedErrFrame]; sep_entail)
      exact hfrom_push hnone (by decide : KindNoHeap 0x8000000000000004#64) hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
        ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
    · have hshr := key_shr32_of_lt hk_ge
      cases hwt : WireType.ofNat? (key.toNat % 8) with
      | none =>
        have hnone := hnone_of_uc_none (mergeLoopBin_of_wt_none protoPrefixStep_unchunked_headerReceived_mergeField hgt_lim hd hk_ge hwt)
        obtain ⟨hcs1, hcs2⟩ := key_wt_none hwt
        apply SepWPpLscro.of_sepWP (mid := entry + 716#64)
        (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
        apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
        apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus); apply SepWP.fold (unchunked3CapAt_entails_chunkedHeaderReceivedPBAt A x.msgPtr cur.length ek uc) (by sep_focus)
        conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_cells2_160 s0.sp]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        apply SepWP.exists_elim; intro v_err0; apply SepWP.exists_elim; intro v_err1; wp_steps
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        have h40 : ((s0.sp - 128#64 + 8#64) ↦₆₄ (key &&& 7#64)) ∗ memRegion (s0.sp - 112#64) 32 ⊢ memRegion (s0.sp - 120#64) 40 := by
          rw [bv_sub_add_lit s0.sp 128 8]; exact cells2_memRegion32_entails_40_160 s0.sp (key &&& 7#64)
        apply SepWP.fold h40 (by sep_focus); wp_reach
        apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000003#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc, receivingEk := ek } x.bs)
          (by dsimp only [chunkedHeaderReceivedErrFrame]; sep_entail)
        exact hfrom_push hnone (by decide : KindNoHeap 0x8000000000000003#64) hsp_align
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
          ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
      | some iwt =>
        obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt; obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_ge; obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
        by_cases hitag0 : key.toNat / 8 < 1
        · have hnone := hnone_of_uc_none (mergeLoopBin_of_tag_zero protoPrefixStep_unchunked_headerReceived_mergeField hgt_lim hd hk_ge hwt hitag0)
          have htag_zero : key.toNat / 8 = 0 := by omega
          apply SepWPpLscro.of_sepWP (mid := entry + 716#64)
          (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
          apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
          apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus); apply SepWP.fold (unchunked3CapAt_entails_chunkedHeaderReceivedPBAt A x.msgPtr cur.length ek uc) (by sep_focus)
          conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_cells1_160 s0.sp]
          simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
          apply SepWP.exists_elim; intro v_err0; wp_steps
          apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus); wp_reach
          apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000005#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc, receivingEk := ek } x.bs)
            (by dsimp only [chunkedHeaderReceivedErrFrame]; sep_entail)
          exact hfrom_push hnone (by decide : KindNoHeap 0x8000000000000005#64) hsp_align
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
            ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
        · obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_ge hitag0
          have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
            rw [beq_eq_false_iff_ne]; intro h; have h1 := congrArg BitVec.toNat h
            simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1; omega
          apply SepWPpLscro.of_sepWP (mid := entry + 468#64)
          (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
          apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
          apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus); apply SepWP.fold (unchunked3CapAt_mono A x.msgPtr uc.epoch uc.auth uc.hdr hrest_le_cur) (by sep_focus)
          wp_steps; wp_reach
          apply SepWPpLscro.weaken_pre (P' := chunkedHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr ek uc x.bs rest)
            (by dsimp only [chunkedHeaderReceivedUcLoopPre]; sep_entail)
          exact hcont key iwt rest _ hd hk_ge hwt hitag0
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm, hsm1, hand_wt]) (by simp only [arm64_norm, hsm1, hw1, hw1_2, hw1_zext1, hw1_zext2]) (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m]) (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m]) (by simp only [arm64_norm, hx25_m]) (by simp only [arm64_norm, hx26_m])
            ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

theorem chunkedHeaderReceived_uc_loop_ok_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 261) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 291) (decodeVarint2Spec A))
    (hSkipCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 263) (skipField3Spec A))
    (hAuthCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A)))
    (hBytesCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A)))
    {x : ChunkedHeaderReceivedMergeGhost} {R : SepProp} {s0 : State} {ek : Option PolynomialDecoder} {outerLimit innerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hbs_lt : x.bs.length < 2 ^ 63) (hlim_lt : innerLimit < 2 ^ 63) :
    ∀ (n : Nat) (uc : V1State.Unchunked.HeaderReceived) (cur : List (BitVec 8)) (s : State),
      cur.length ≤ n → cur.length ≤ x.bs.length → IsDropSuffix x.bs cur →
      (∀ (uc' : V1State.Unchunked.HeaderReceived) (rest' : List (BitVec 8)) (s' : State),
        rest'.length = innerLimit → rest'.length ≤ x.bs.length → IsDropSuffix x.bs rest' →
        mergeLoopBin V1State.Unchunked.HeaderReceived.mergeField (cur.length - innerLimit) uc cur innerLimit 97 = some uc' →
        s'.pc = (blkPl_306).base + 168#64 →
        s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
        s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr → s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit → s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 25#5) = 8#64 → ChunkedInl10CalleeSaved s0 s' →
        SepWPpLscro lsmpl ((blkPC_306).rebase (blkPl_306).base H) (s0.readReg64 Reg.lr) s'
          (chunkedHeaderReceivedLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc', receivingEk := ek } x.bs rest')
          (WppPost (chunkedHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0)) →
      (mergeLoopBin V1State.Unchunked.HeaderReceived.mergeField (cur.length - innerLimit) uc cur innerLimit 97 = none →
        (Proto.mergeMessage V1State.Chunked.HeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none) →
      s.pc = (blkPl_306).base + 416#64 →
      s.status = .Running → s.sp = s0.sp - 128#64 → s.trace = s0.trace →
      s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr → s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit → s.readReg64 (Reg.gpr 23#5) = 1#64 → s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 → s.readReg64 (Reg.gpr 25#5) = 8#64 → s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s →
      SepWPpLscro lsmpl ((blkPC_306).rebase (blkPl_306).base H) (s0.readReg64 Reg.lr) s
        (chunkedHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr ek uc x.bs cur)
        (WppPost (chunkedHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  have htag1_varint := fun {s uc rest} => @chunkedHeaderReceived_uc_tag1_varint_step_placed _ A H hPushCall hVarintCall x R s0 s ek uc rest outerLimit innerLimit
  have htag1_wt_err := fun {s uc rest iwt} => @chunkedHeaderReceived_uc_tag1_wt_err_step_placed _ A H hFromCall hPushCall x R s0 s ek uc rest iwt
  have htag2_step := fun {s uc rest} (iwt : WireType) => @chunkedHeaderReceived_uc_tag2_step_placed _ A H hPushCall hAuthCall x R s0 s ek uc rest iwt outerLimit innerLimit
  have htag3_step := fun {s uc rest} (iwt : WireType) => @chunkedHeaderReceived_uc_tag3_step_placed _ A H hPushCall hBytesCall x R s0 s ek uc rest iwt outerLimit innerLimit
  have hskip_step := fun {s uc rest} (iwt : WireType) (tag : Nat) => @chunkedHeaderReceived_uc_skip_step_placed _ A H hPushCall hSkipCall x R s0 s ek uc rest iwt tag outerLimit innerLimit
  intro n; induction n with
  | zero =>
    intro uc cur s hcur_n hcur_le hcur_suf hok_cont hnone_cont hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
    exact chunkedHeaderReceived_uc_loop_le_exit_placed hFromCall hPushCall (by omega) hsp_align hcur_le hcur_suf hlim_lt
      (fun hlt => hnone_cont (mergeLoopBin_lt_limit _ _ _ _ _ _ hlt))
      (fun s' heq => hok_cont uc cur s' heq hcur_le hcur_suf (mergeLoopBin_eq_limit _ _ _ _ _ _ heq))
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
  | succ n ih =>
    intro uc cur s hcur_n hcur_le hcur_suf hok_cont hnone_cont hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
    by_cases hle_lim : cur.length ≤ innerLimit
    · exact chunkedHeaderReceived_uc_loop_le_exit_placed hFromCall hPushCall hle_lim hsp_align hcur_le hcur_suf hlim_lt
        (fun hlt => hnone_cont (mergeLoopBin_lt_limit _ _ _ _ _ _ hlt))
        (fun s' heq => hok_cont uc cur s' heq hcur_le hcur_suf (mergeLoopBin_eq_limit _ _ _ _ _ _ heq))
        hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
    · have hcur_lt : cur.length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
      refine chunkedHeaderReceived_uc_decode_key_step_placed hFromCall hPushCall hVarintCall hle_lim hsp_align
        hcur_le hcur_lt hcur_suf hnone_cont ?_ hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
      intro key iwt rest s' hd hk_ge hwt hitag0 hpc' hrun' hsp' htr' hx0' hx1' hx19' hx20' hx21' hx22' hx23' hx24' hx25' hx26' hcs'
      obtain ⟨hx27', hx28', hvregs'⟩ := hcs'
      have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd; have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
      have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le; have hrest_lt : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest_le hbs_lt
      have hrest_suf : IsDropSuffix x.bs rest := suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
      have htag_lt : key.toNat / 8 < 2 ^ 32 := by omega
      have hstep := mergeLoopBin_of_key_ok (m := uc) (depth' := 97)
        protoPrefixStep_unchunked_headerReceived_mergeField hle_lim hd hk_ge hwt hitag0
      by_cases htag1 : key.toNat / 8 = 1
      · rw [htag1] at hx1' hstep; rw [unchunkedHeaderReceived_mergeField_tag1] at hstep
        by_cases hiwt : iwt = .varint
        · subst hiwt; apply SepWPpLscro.of_sepWP (mid := entry + 556#64); wp_steps; wp_reach
          refine htag1_varint hsp_align hrest_le hrest_lt hrest_suf
            (fun hdv => hnone_cont (by simp [hstep, hdv]))
            (fun v rest' s'' hdv hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs'' => ?_)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr']) (by simp only [arm64_norm, hx0', WireType.toNat]) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20']) (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23']) (by simp only [arm64_norm, hx24']) (by simp only [arm64_norm, hx25']) (by simp only [arm64_norm, hx26'])
            ⟨by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩
          have hr'_lt : rest'.length < rest.length := decodeVarint_length hdv; have hr'_le : rest'.length ≤ rest.length := Nat.le_of_lt hr'_lt
          have hstep1 : mergeLoopBin V1State.Unchunked.HeaderReceived.mergeField (cur.length - innerLimit) uc cur innerLimit 97 =
              mergeLoopBin V1State.Unchunked.HeaderReceived.mergeField (rest'.length - innerLimit) { uc with epoch := v } rest' innerLimit 97 := by simp [hstep, hdv]
          exact ih { uc with epoch := v } rest' s'' (by omega) (Nat.le_trans hr'_le hrest_le)
            (suffix_trans hrest_le hrest_suf hr'_le (decodeVarint_suffix hdv))
            (fun uc' r'' s3 heq hr''_le hr''_suf hml => hok_cont uc' r'' s3 heq hr''_le hr''_suf (hstep1.trans hml))
            (fun hml => hnone_cont (hstep1.trans hml))
            hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs''
        · apply SepWPpLscro.of_sepWP (mid := entry + 556#64); wp_steps; wp_reach
          exact htag1_wt_err hiwt hsp_align hrest_le hrest_suf (hnone_cont (by simp [hstep, hiwt]))
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr']) (by simp only [arm64_norm, hx0']) ⟨by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩
      · by_cases htag2 : key.toNat / 8 = 2
        · rw [htag2] at hx1' hstep; rw [unchunkedHeaderReceived_mergeField_tag2] at hstep
          apply SepWPpLscro.of_sepWP (mid := entry + 512#64); wp_steps; wp_reach
          refine htag2_step iwt hsp_align hrest_le hrest_lt hrest_suf
            (fun hauth => hnone_cont (by simp [hstep, hauth]))
            (fun auth' rest' s'' hauth hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs'' => ?_)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr']) (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20']) (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23']) (by simp only [arm64_norm, hx24']) (by simp only [arm64_norm, hx25']) (by simp only [arm64_norm, hx26'])
            ⟨by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩
          have hr'_le : rest'.length ≤ rest.length := (proto_mergeMessage_suffix hauth).1
          have hstep2 : mergeLoopBin V1State.Unchunked.HeaderReceived.mergeField (cur.length - innerLimit) uc cur innerLimit 97 =
              mergeLoopBin V1State.Unchunked.HeaderReceived.mergeField (rest'.length - innerLimit) { uc with auth := some auth' } rest' innerLimit 97 := by simp [hstep, hauth]
          exact ih { uc with auth := some auth' } rest' s'' (by omega) (Nat.le_trans hr'_le hrest_le)
            (suffix_trans hrest_le hrest_suf hr'_le (proto_mergeMessage_suffix hauth).2)
            (fun uc' r'' s3 heq hr''_le hr''_suf hml => hok_cont uc' r'' s3 heq hr''_le hr''_suf (hstep2.trans hml))
            (fun hml => hnone_cont (hstep2.trans hml))
            hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs''
        · by_cases htag3 : key.toNat / 8 = 3
          · rw [htag3] at hx1' hstep; rw [unchunkedHeaderReceived_mergeField_tag3] at hstep
            apply SepWPpLscro.of_sepWP (mid := entry + 392#64); wp_steps; wp_reach
            refine htag3_step iwt hsp_align hrest_le hrest_lt hrest_suf
              (fun hmb => hnone_cont (by simp [hstep, hmb]))
              (fun v rest' s'' hmb hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs'' => ?_)
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr']) (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20']) (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23']) (by simp only [arm64_norm, hx24']) (by simp only [arm64_norm, hx25']) (by simp only [arm64_norm, hx26'])
              ⟨by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩
            have hr'_le : rest'.length ≤ rest.length := mergeBytes_length hmb
            have hstep3 : mergeLoopBin V1State.Unchunked.HeaderReceived.mergeField (cur.length - innerLimit) uc cur innerLimit 97 =
                mergeLoopBin V1State.Unchunked.HeaderReceived.mergeField (rest'.length - innerLimit) { uc with hdr := v } rest' innerLimit 97 := by simp [hstep, hmb]
            exact ih { uc with hdr := v } rest' s'' (by omega) (Nat.le_trans hr'_le hrest_le)
              (suffix_trans hrest_le hrest_suf hr'_le (mergeBytes_suffix hmb))
              (fun uc' r'' s3 heq hr''_le hr''_suf hml => hok_cont uc' r'' s3 heq hr''_le hr''_suf (hstep3.trans hml))
              (fun hml => hnone_cont (hstep3.trans hml))
              hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs''
          · obtain ⟨hb1_1, _⟩ := itag_beq_tag_false htag1 htag_lt (by decide : 1 < 2 ^ 32)
            obtain ⟨hb2_1, _⟩ := itag_beq_tag_false htag2 htag_lt (by decide : 2 < 2 ^ 32); obtain ⟨hb3_1, _⟩ := itag_beq_tag_false htag3 htag_lt (by decide : 3 < 2 ^ 32)
            have hb1_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 1#32) = false := by rw [sf_truncate32_ofNat64]; exact hb1_1
            have hb2_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 2#32) = false := by rw [sf_truncate32_ofNat64]; exact hb2_1
            have hb3_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 3#32) = false := by rw [sf_truncate32_ofNat64]; exact hb3_1
            rw [unchunkedHeaderReceived_mergeField_other uc iwt rest 97 htag_lt htag1 htag2 htag3] at hstep
            apply SepWPpLscro.of_sepWP (mid := entry + 492#64); wp_steps; wp_reach
            refine hskip_step iwt (key.toNat / 8) hsp_align hrest_le hrest_lt hrest_suf htag_lt
              (fun hsf => hnone_cont (by simp [hstep, hsf]))
              (fun rest' s'' hsf hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs'' => ?_)
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr']) (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx1', sf_truncate32_ofNat64]) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20']) (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23']) (by simp only [arm64_norm, hx24']) (by simp only [arm64_norm, hx25']) (by simp only [arm64_norm, hx26'])
              ⟨by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩
            have hr'_le : rest'.length ≤ rest.length := (skip_length (2 * rest.length + 2)).1 _ _ _ _ _ hsf
            have hstep_other : mergeLoopBin V1State.Unchunked.HeaderReceived.mergeField (cur.length - innerLimit) uc cur innerLimit 97 =
                mergeLoopBin V1State.Unchunked.HeaderReceived.mergeField (rest'.length - innerLimit) uc rest' innerLimit 97 := by simp [hstep, hsf]
            exact ih uc rest' s'' (by omega) (Nat.le_trans hr'_le hrest_le)
              (suffix_trans hrest_le hrest_suf hr'_le ((skip_suffix (2 * rest.length + 2)).1 _ _ _ _ _ hsf))
              (fun uc' r'' s3 heq hr''_le hr''_suf hml => hok_cont uc' r'' s3 heq hr''_le hr''_suf (hstep_other.trans hml))
              (fun hml => hnone_cont (hstep_other.trans hml))
              hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs''

end CryptoVerification.SpqrV1.Prost.MessageMerge

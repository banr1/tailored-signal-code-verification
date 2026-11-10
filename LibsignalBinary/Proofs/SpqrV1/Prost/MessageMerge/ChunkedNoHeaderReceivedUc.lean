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
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Inner `Unchunked.NoHeaderReceived` Merge & Exit Lemmas for `Chunked.NoHeaderReceived::merge` (`0x511b4`, Block `308`)

Proves the epilogue, decode-error exits, and inlined `Unchunked.NoHeaderReceived` field-merge loop
inside `prost::encoding::message::merge::<spqr::proto::pq_ratchet::v1_state::chunked::NoHeaderReceived, &mut &[u8]>`
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
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero chunkedNoHeaderReceivedMerge_fnOff

gen_decodes libsignalSessionCode_tree chunkedNoHeaderReceivedMergeBin [
  0x4bdbc → 0x4c178
]

macro "chunkedNoHeaderReceivedMerge_fetches " b:term:max H:term:max k0:num len:num : tactic =>
  `(tactic| code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.SpqrV1.Prost.MessageMerge.chunkedNoHeaderReceivedMergeBin $b $H
    chunkedNoHeaderReceivedMerge_fnOff 0x4bdbc $k0 $len)

/-! ## 1. Pure `mergeField` Step Lemmas and Helpers -/

theorem vecU8Buf_entails_cap_lt_nhr (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8Buf A cap ptr bs ⊢ ⌜cap.toNat < 2 ^ 63⌝ ∗ vecU8Buf A cap ptr bs := by
  unfold vecU8Buf; refine Entails.pure_left fun h => Entails.pure_right h.2.1 (Entails.pure_right h (Entails.refl _))

theorem vecU8At_entails_header_cap_lt (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A a cap ptr bs ⊢
      ⌜cap.toNat < 2 ^ 63⌝ ∗ (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ vecU8Buf A cap ptr bs := by
  rw [vecU8At_eq_header_sep_buf, vecHeader]
  refine Entails.trans (sepConj_mono_right (vecU8Buf_entails_cap_lt_nhr A cap ptr bs)) (by sep_entail)

theorem header_buf_entails_vecU8At (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      vecU8Buf A cap ptr bs ⊢ vecU8At A a cap ptr bs := by
  rw [vecU8At_eq_header_sep_buf, vecHeader]; sep_entail

def authMacKeyCapAt (A : RustAlloc) (a : BitVec 64) (bsLen : Nat) (auth : ProtoAuthenticator) : SepProp :=
  ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap bsLen⌝ ∗ vecU8At A (a + 0x18#64) cap ptr auth.macKey

theorem authenticatorPBCapAt_entails_cmn (A : RustAlloc) (a : BitVec 64) (bsLen : Nat) (auth : ProtoAuthenticator) :
    authenticatorPBCapAt A a bsLen auth ⊢
      ∃∗ cap_ik : BitVec 64, ∃∗ ptr_ik : BitVec 64,
        ⌜cap_ik.toNat < 2 ^ 63⌝ ∗ ⌜BytesMergeCapOk cap_ik bsLen⌝ ∗
        (a ↦₆₄ cap_ik) ∗ ((a + 8#64) ↦₆₄ ptr_ik) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
        vecU8Buf A cap_ik ptr_ik auth.rootKey ∗ authMacKeyCapAt A a bsLen auth := by
  unfold authenticatorPBCapAt authMacKeyCapAt
  rw [sepExists_sepConj_left]; refine ProofLib.Entails.sepExists_elim fun cap_ik => ?_
  rw [sepExists_sepConj_left]; refine ProofLib.Entails.sepExists_elim fun ptr_ik => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro cap_ik); refine Entails.trans ?_ (Entails.sepExists_intro ptr_ik)
  rw [sepConj_assoc]; refine Entails.pure_left fun hcap => ?_
  refine Entails.trans (sepConj_mono_left (vecU8At_entails_header_cap_lt A a cap_ik ptr_ik auth.rootKey)) ?_
  simp only [sepConj_assoc]; exact Entails.pure_left fun hlt => Entails.pure_right hlt (Entails.pure_right hcap (Entails.refl _))

theorem cmn_entails_authenticatorPBCapAt (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (auth : ProtoAuthenticator) (cap_ik ptr_ik : BitVec 64) (hcap : BytesMergeCapOk cap_ik bsLen) :
    (a ↦₆₄ cap_ik) ∗ ((a + 8#64) ↦₆₄ ptr_ik) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
      vecU8Buf A cap_ik ptr_ik auth.rootKey ∗ authMacKeyCapAt A a bsLen auth ⊢
      authenticatorPBCapAt A a bsLen auth := by
  unfold authenticatorPBCapAt
  refine Entails.trans (Entails.of_eq (show _ = ((a ↦₆₄ cap_ik) ∗ ((a + 8#64) ↦₆₄ ptr_ik) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗ vecU8Buf A cap_ik ptr_ik auth.rootKey) ∗ authMacKeyCapAt A a bsLen auth by ac_rfl)) ?_
  unfold authMacKeyCapAt; refine sepConj_mono_left ?_
  refine Entails.trans (header_buf_entails_vecU8At A a cap_ik ptr_ik auth.rootKey) ?_
  refine Entails.trans ?_ (Entails.sepExists_intro cap_ik); refine Entails.trans ?_ (Entails.sepExists_intro ptr_ik)
  exact Entails.pure_right hcap (Entails.refl _)

theorem decodeErrorWith_le3_nhr (A : RustAlloc) (e : BitVec 64) {n : Nat} (hn : n ≤ 3) :
    decodeErrorAtStackLen A e n ⊢ ∃∗ k : Nat, ⌜k ≤ 3⌝ ∗ decodeErrorAtStackLen A e k := by
  refine Entails.trans ?_ (Entails.sepExists_intro n); rw [pure_sepConj_of_true hn]; exact Entails.refl _

theorem unchunkedNoHeaderReceived_mergeField_tag1 (m : V1State.Unchunked.NoHeaderReceived) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (V1State.Unchunked.NoHeaderReceived.mergeField m (BitVec.ofNat 32 1) (codecWireTypeToProto iwt) rest depth').toOption =
      if iwt = .varint then (decodeVarint rest).map (fun (v, rest') => ({ m with epoch := v }, rest')) else none := by
  unfold V1State.Unchunked.NoHeaderReceived.mergeField Proto.mergeUint64 Proto.checkWireType
  simp only [beq_self_eq_true, ↓reduceIte]
  by_cases h : iwt = .varint
  · subst h; have hdv := proto_decodeVarint_toOption rest
    rcases hp : Proto.decodeVarint rest with _ | ⟨v, rest'⟩ <;>
      { rw [hp] at hdv; dsimp [Except.toOption, Bind.bind, Except.bind] at hdv ⊢; rw [← hdv]; rfl }
  · cases iwt <;> first | contradiction | rfl

theorem unchunkedNoHeaderReceived_mergeField_tag2 (m : V1State.Unchunked.NoHeaderReceived) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (V1State.Unchunked.NoHeaderReceived.mergeField m (BitVec.ofNat 32 2) (codecWireTypeToProto iwt) rest depth').toOption =
      (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto iwt) (m.auth.getD default) rest depth').toOption.map
        (fun (v, rest') => ({ m with auth := some v }, rest')) := by
  unfold V1State.Unchunked.NoHeaderReceived.mergeField Proto.mergeOptMessage
  simp only [show (BitVec.ofNat 32 2 == 1#32) = false from rfl, show (BitVec.ofNat 32 2 == 2#32) = true from rfl, Bool.false_eq_true, ↓reduceIte]
  rcases Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto iwt) (m.auth.getD default) rest depth' with _ | ⟨v, r⟩ <;> rfl

theorem unchunkedNoHeaderReceived_mergeField_other (m : V1State.Unchunked.NoHeaderReceived) {tag : Nat} (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) (htag_lt : tag < 2 ^ 32) (hne1 : tag ≠ 1) (hne2 : tag ≠ 2) :
    (V1State.Unchunked.NoHeaderReceived.mergeField m (BitVec.ofNat 32 tag) (codecWireTypeToProto iwt) rest depth').toOption =
      (skipField (2 * rest.length + 2) depth' tag iwt rest).map (fun rest' => (m, rest')) := by
  have hb1 : (BitVec.ofNat 32 tag == 1#32) = false := (itag_beq_tag_false hne1 htag_lt (by decide)).1
  have hb2 : (BitVec.ofNat 32 tag == 2#32) = false := (itag_beq_tag_false hne2 htag_lt (by decide)).1
  have htag_toNat : (BitVec.ofNat 32 tag).toNat = tag := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htag_lt]
  unfold V1State.Unchunked.NoHeaderReceived.mergeField; simp only [hb1, hb2, Bool.false_eq_true, ↓reduceIte]
  have hsf' := proto_skipField_toOption (codecWireTypeToProto iwt) (BitVec.ofNat 32 tag) rest depth'
  rw [htag_toNat, protoWireTypeToCodec_codecWireTypeToProto] at hsf'
  rcases hsf : Proto.skipField (codecWireTypeToProto iwt) (BitVec.ofNat 32 tag) rest depth' with _ | rest' <;>
    { rw [hsf] at hsf'; dsimp [Except.toOption] at hsf'; rw [← hsf']; rfl }

theorem chunkedNoHeaderReceived_mergeField_tag1 (m : V1State.Chunked.NoHeaderReceived) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (V1State.Chunked.NoHeaderReceived.mergeField m (BitVec.ofNat 32 1) (codecWireTypeToProto iwt) rest depth').toOption =
      (Proto.mergeMessage V1State.Unchunked.NoHeaderReceived.mergeField (codecWireTypeToProto iwt) (m.uc.getD default) rest depth').toOption.map
        (fun (v, rest') => ({ m with uc := some v }, rest')) := by
  unfold V1State.Chunked.NoHeaderReceived.mergeField Proto.mergeOptMessage; simp only [beq_self_eq_true, ↓reduceIte]
  rcases Proto.mergeMessage V1State.Unchunked.NoHeaderReceived.mergeField (codecWireTypeToProto iwt) (m.uc.getD default) rest depth' with _ | ⟨v, r⟩ <;> rfl

theorem chunkedNoHeaderReceived_mergeField_tag2 (m : V1State.Chunked.NoHeaderReceived) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (V1State.Chunked.NoHeaderReceived.mergeField m (BitVec.ofNat 32 2) (codecWireTypeToProto iwt) rest depth').toOption =
      (Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto iwt) (m.receivingHdr.getD default) rest depth').toOption.map
        (fun (v, rest') => ({ m with receivingHdr := some v }, rest')) := by
  unfold V1State.Chunked.NoHeaderReceived.mergeField Proto.mergeOptMessage
  simp only [show (BitVec.ofNat 32 2 == 1#32) = false from rfl, show (BitVec.ofNat 32 2 == 2#32) = true from rfl, Bool.false_eq_true, ↓reduceIte]
  rcases Proto.mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto iwt) (m.receivingHdr.getD default) rest depth' with _ | ⟨v, r⟩ <;> rfl

theorem chunkedNoHeaderReceived_mergeField_other (m : V1State.Chunked.NoHeaderReceived) {tag : Nat} (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) (htag_lt : tag < 2 ^ 32) (hne1 : tag ≠ 1) (hne2 : tag ≠ 2) :
    (V1State.Chunked.NoHeaderReceived.mergeField m (BitVec.ofNat 32 tag) (codecWireTypeToProto iwt) rest depth').toOption =
      (skipField (2 * rest.length + 2) depth' tag iwt rest).map (fun rest' => (m, rest')) := by
  have hb1 : (BitVec.ofNat 32 tag == 1#32) = false := (itag_beq_tag_false hne1 htag_lt (by decide)).1
  have hb2 : (BitVec.ofNat 32 tag == 2#32) = false := (itag_beq_tag_false hne2 htag_lt (by decide)).1
  have htag_toNat : (BitVec.ofNat 32 tag).toNat = tag := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htag_lt]
  unfold V1State.Chunked.NoHeaderReceived.mergeField; simp only [hb1, hb2, Bool.false_eq_true, ↓reduceIte]
  have hsf' := proto_skipField_toOption (codecWireTypeToProto iwt) (BitVec.ofNat 32 tag) rest depth'
  rw [htag_toNat, protoWireTypeToCodec_codecWireTypeToProto] at hsf'
  rcases hsf : Proto.skipField (codecWireTypeToProto iwt) (BitVec.ofNat 32 tag) rest depth' with _ | rest' <;>
    { rw [hsf] at hsf'; dsimp [Except.toOption] at hsf'; rw [← hsf']; rfl }

/-! ## 2. Loop Preconditions and Shared Error Exits -/

/-- Outer loop-header separation-logic bundle at `+0x0a8` (`entry + 168#64`). -/
def chunkedNoHeaderReceivedLoopPre (A : RustAlloc) (s0 : State) (msgPtr bufRef slot ptr : BitVec 64)
    (m : V1State.Chunked.NoHeaderReceived) (bs cur : List (BitVec 8)) : SepProp :=
  chunkedNoHeaderReceivedPBCapAt A msgPtr cur.length m ∗
    stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗
    chunkedInlSavedRegs10 s0.sp s0 ∗ (bufRef ↦₆₄ slot) ∗ sliceCursorAfter slot ptr bs cur ∗ A.pool

/-- Inner `Unchunked.NoHeaderReceived` loop-header separation-logic bundle at `+0x198` (`entry + 408#64`). -/
def chunkedNoHeaderReceivedUcLoopPre (A : RustAlloc) (s0 : State) (msgPtr bufRef slot ptr : BitVec 64)
    (hdr : Option PolynomialDecoder) (uc : V1State.Unchunked.NoHeaderReceived) (bs cur : List (BitVec 8)) : SepProp :=
  optPolynomialDecoderPBAt A msgPtr hdr ∗
    unchunked2CapAt A (msgPtr + 0x28#64) cur.length uc.epoch uc.auth ∗
    stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗
    chunkedInlSavedRegs10 s0.sp s0 ∗ (bufRef ↦₆₄ slot) ∗ sliceCursorAfter slot ptr bs cur ∗ A.pool

theorem unchunked2CapAt_entails_chunkedNoHeaderReceivedPBAt (A : RustAlloc) (a : BitVec 64)
    (n : Nat) (hdr : Option PolynomialDecoder) (uc : V1State.Unchunked.NoHeaderReceived) :
    optPolynomialDecoderPBAt A a hdr ∗ unchunked2CapAt A (a + 0x28#64) n uc.epoch uc.auth ⊢
      chunkedNoHeaderReceivedPBAt A a { receivingHdr := hdr, uc := some uc } :=
  sepConj_mono_right (unchunked2CapAt_entails_unchunked2At A (a + 0x28#64) n uc.epoch uc.auth)

/-- Error-exit separation-logic bundle (with `chunkedNoHeaderReceivedPBAt`). -/
def chunkedNoHeaderReceivedErrFrame (A : RustAlloc) (s0 : State) (msgPtr bufRef slot ptr : BitVec 64)
    (m : V1State.Chunked.NoHeaderReceived) (bs : List (BitVec 8)) : SepProp :=
  chunkedInlSavedRegs10 s0.sp s0 ∗ chunkedNoHeaderReceivedPBAt A msgPtr m ∗
    (bufRef ↦₆₄ slot) ∗ memRegion slot 16 ∗ (ptr ↦ₛ bs) ∗ A.pool

/-- Shared error return from `+0x080` (`entry + 128#64`) when `x0 = err ≠ 0#64` owns `decodeErrorAtStackLen A err n` (`n ≤ 3`). -/
theorem chunkedNoHeaderReceived_ret_err_exit {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    {x : ChunkedNoHeaderReceivedMergeGhost} {R : SepProp} {s0 : State} {m : V1State.Chunked.NoHeaderReceived} {s : State}
    {err : BitVec 64} {n : Nat}
    (hnone : (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hn : n ≤ 3) (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 128#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = err) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
      (decodeErrorAtStackLen A err n ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
        memRegion (s0.sp - 128#64) 48 ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; chunkedNoHeaderReceivedMerge_fetches img.base H 128 28
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName = entry; examples_hide_fetches
  apply SepWPpIn.of_sepWP_ret; unfold WppPost chunkedNoHeaderReceivedMergeSpec
  simp only [hnone, chunkedNoHeaderReceivedErrFrame, chunkedInlSavedRegs10,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp, hx0]
  apply SepWP.fold (decodeErrorWith_le3_nhr A err hn) (by sep_focus)
  apply SepWP.fold (chunkedNoHeaderReceivedPBAt_entails_exists A x.msgPtr m) (by sep_focus)
  wp_steps; apply SepWP.fold (stackAt_chunkedInl10_epilogue s0.sp s0) (by unfold chunkedInlSavedRegs10; sep_focus); wp_done

/-- Shared exit from `+0x078` (`entry + 120#64`): calls `DecodeError::from` on `(s0.sp - 128#64, w)` and returns. -/
theorem chunkedNoHeaderReceived_from_err_exit {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 0xffffffffffff9bec#64) (decodeErrorFromSpec A))
    {x : ChunkedNoHeaderReceivedMergeGhost} {R : SepProp} {s0 : State} {m : V1State.Chunked.NoHeaderReceived} {s : State} {w : BitVec 64}
    (hnone : (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hw : KindNoHeap w) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 120#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ w) ∗ memRegion (s0.sp - 120#64) 40 ∗
        stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; chunkedNoHeaderReceivedMerge_fetches img.base H 120 36
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName = entry; examples_hide_fetches
  apply SepWPpIn.of_sepWP (mid := entry + 0xffffffffffff9bec#64)
  conv => arg 4; rw [chunkedNoHeaderReceivedErrFrame, chunkedInlBelow_decodeErrorHook s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpIn.call_frame (x := (s0.sp - 128#64, w))
    (ret_pc := entry + 128#64) hFromCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorFromSpec]; simp only [arm64_norm, hsp]; rfl) hw (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, _, _, _, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx27, hx28, hvregs] at hpcm hspm hx27_m hx28_m hvregs_m
  apply SepWPpIn.of_sepWP_ret; unfold WppPost chunkedNoHeaderReceivedMergeSpec
  simp only [decodeErrorFromSpec, hnone, chunkedNoHeaderReceivedErrFrame, chunkedInlSavedRegs10,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp, hspm]
  apply SepWP.fold (chunkedInlBelow_decodeErrorHook_entails s0.sp) (by sep_focus)
  apply SepWP.fold (memRegion8_memRegion40_entails_48_160 s0.sp) (by sep_focus)
  apply SepWP.fold (decodeErrorWith_le3_nhr A (sm.readReg64 (Reg.gpr 0#5)) (by decide : 0 ≤ 3)) (by sep_focus)
  apply SepWP.fold (chunkedNoHeaderReceivedPBAt_entails_exists A x.msgPtr m) (by sep_focus)
  wp_steps; apply SepWP.fold (stackAt_chunkedInl10_epilogue s0.sp s0) (by unfold chunkedInlSavedRegs10; sep_focus); wp_done

/-- Shared exit from `+0x2d8` (`entry + 728#64`): calls `DecodeError::push` with `[sp] = err` (`n ≤ 2`), loads `x0`, and jumps to `+0x080` (`entry + 128#64`). -/
theorem chunkedNoHeaderReceived_push_ret_exit {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 0xffffffffffff98f4#64) (decodeErrorPushSpec A))
    {x : ChunkedNoHeaderReceivedMergeGhost} {R : SepProp} {s0 : State} {m : V1State.Chunked.NoHeaderReceived} {s : State}
    {err : BitVec 64} {n : Nat}
    (hnone : (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hn : n ≤ 2) (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 728#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = s0.sp - 128#64) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A err n ∗ memRegion (s0.sp - 120#64) 40 ∗
        stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; have hret := @chunkedNoHeaderReceived_ret_err_exit img A H x R s0 m
  chunkedNoHeaderReceivedMerge_fetches img.base H 728 12
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName = entry; examples_hide_fetches
  apply SepWPpIn.of_sepWP (mid := entry + 0xffffffffffff98f4#64)
  conv => arg 4; rw [chunkedNoHeaderReceivedErrFrame, chunkedInlBelow_decodeErrorHook s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpIn.call_frame (x := (s0.sp - 128#64, err, n))
    (ret_pc := entry + 732#64) hPushCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
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
  apply SepWPpIn.weaken_pre (P' := decodeErrorAtStackLen A err (n + 1) ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
    (by dsimp only [chunkedNoHeaderReceivedErrFrame]; sep_entail)
  exact hret hnone (by omega : n + 1 ≤ 3) herr hsp_align
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
    (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])
    ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

/-- Shared exit from `+0x2b8` (`entry + 696#64`): stores `x1 = err` (`n ≤ 2`) at `[sp]`, sets up outer `uc` field context, and enters `push_ret_exit` at `+0x2d8`. -/
theorem chunkedNoHeaderReceived_uc_push_exit {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 0xffffffffffff98f4#64) (decodeErrorPushSpec A))
    {x : ChunkedNoHeaderReceivedMergeGhost} {R : SepProp} {s0 : State} {m : V1State.Chunked.NoHeaderReceived} {s : State}
    {err : BitVec 64} {n : Nat}
    (hnone : (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hn : n ≤ 2) (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 696#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 (Reg.gpr 1#5) = err) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
      (decodeErrorAtStackLen A err n ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
        memRegion (s0.sp - 128#64) 48 ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; have hpush := @chunkedNoHeaderReceived_push_ret_exit img A H hPushCall x R s0 m
  chunkedNoHeaderReceivedMerge_fetches img.base H 696 32
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName = entry; examples_hide_fetches
  apply SepWPpIn.of_sepWP (mid := entry + 728#64)
  conv => arg 4; rw [memRegion_48_cells1_160 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, hx1]
  apply SepWP.exists_elim; intro v_stk0; wp_steps; wp_reach
  apply SepWPpIn.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A err n ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
    (by sep_entail)
  exact hpush hnone hn herr hsp_align
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hsp])
    ⟨by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩

/-- Shared exit from `+0x2ac` (`entry + 684#64`): calls `DecodeError::from` on `(s0.sp - 128#64, w)` and enters `uc_push_exit` at `+0x2b8`. -/
theorem chunkedNoHeaderReceived_uc_from_push_exit {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 0xffffffffffff9bec#64) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 0xffffffffffff98f4#64) (decodeErrorPushSpec A))
    {x : ChunkedNoHeaderReceivedMergeGhost} {R : SepProp} {s0 : State} {m : V1State.Chunked.NoHeaderReceived} {s : State} {w : BitVec 64}
    (hnone : (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hw : KindNoHeap w) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 684#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64)
    (htr : s.trace = s0.trace) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ w) ∗ memRegion (s0.sp - 120#64) 40 ∗
        stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
        chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  have hpush := @chunkedNoHeaderReceived_uc_push_exit img A H hPushCall x R s0 m
  chunkedNoHeaderReceivedMerge_fetches img.base H 684 12
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName = entry; examples_hide_fetches
  apply SepWPpIn.of_sepWP (mid := entry + 0xffffffffffff9bec#64)
  conv => arg 4; rw [chunkedNoHeaderReceivedErrFrame, chunkedInlBelow_decodeErrorHook s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpIn.call_frame (x := (s0.sp - 128#64, w))
    (ret_pc := entry + 692#64) hFromCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorFromSpec]; simp only [arm64_norm, hsp]; rfl)
    hw (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, _, _, _, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx27, hx28, hvregs] at hpcm hspm hx27_m hx28_m hvregs_m
  apply SepWPpIn.of_sepWP (mid := entry + 696#64)
  (conv => arg 4; simp only [decodeErrorFromSpec, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨hsm0, htrm⟩
  apply SepWP.fold (chunkedInlBelow_decodeErrorHook_entails s0.sp) (by sep_focus)
  apply SepWP.fold (memRegion8_memRegion40_entails_48_160 s0.sp) (by sep_focus)
  wp_steps; wp_reach
  apply SepWPpIn.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
    (by dsimp only [chunkedNoHeaderReceivedErrFrame]; sep_entail)
  exact hpush hnone (by decide : 0 ≤ 2) hsm0 hsp_align
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
    (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])
    ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

/-- Shared exit from `+0x398` (`entry + 920#64`): calls `DecodeError::push` for an inner `uc` field (`n ≤ 1`), loads `x1 = err`, and jumps to `uc_push_exit` at `+0x2b8` (`entry + 696#64`). -/
theorem chunkedNoHeaderReceived_uc_field_push_exit {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 0xffffffffffff98f4#64) (decodeErrorPushSpec A))
    {x : ChunkedNoHeaderReceivedMergeGhost} {R : SepProp} {s0 : State} {m : V1State.Chunked.NoHeaderReceived} {s : State}
    {err : BitVec 64} {n : Nat}
    (hnone : (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hn : n ≤ 1) (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 920#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = s0.sp - 128#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A err n ∗ memRegion (s0.sp - 120#64) 40 ∗
        stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
        chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  have hpush := @chunkedNoHeaderReceived_uc_push_exit img A H hPushCall x R s0 m
  chunkedNoHeaderReceivedMerge_fetches img.base H 920 12
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName = entry; examples_hide_fetches
  apply SepWPpIn.of_sepWP (mid := entry + 0xffffffffffff98f4#64)
  conv => arg 4; rw [chunkedNoHeaderReceivedErrFrame, chunkedInlBelow_decodeErrorHook s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpIn.call_frame (x := (s0.sp - 128#64, err, n))
    (ret_pc := entry + 924#64) hPushCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorPushSpec]; simp only [arm64_norm, hsp, hx0]; rfl)
    (by omega : n < 2 ^ 32)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, _, _, _, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx27, hx28, hvregs] at hpcm hspm hx27_m hx28_m hvregs_m
  apply SepWPpIn.of_sepWP (mid := entry + 696#64)
  (conv => arg 4; simp only [decodeErrorPushSpec, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; intro htrm
  apply SepWP.fold (chunkedInlBelow_decodeErrorHook_entails s0.sp) (by sep_focus)
  wp_steps
  apply SepWP.fold (pointsTo64_memRegion40_entails_48_160 s0.sp err) (by sep_focus)
  wp_reach
  apply SepWPpIn.weaken_pre (P' := decodeErrorAtStackLen A err (n + 1) ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
    (by dsimp only [chunkedNoHeaderReceivedErrFrame]; sep_entail)
  exact hpush hnone (by omega : n + 1 ≤ 2) herr hsp_align
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
    (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])
    ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

/-! ## 3. Inner `Unchunked.NoHeaderReceived` Field Steps and Loop Induction -/

/-- Step lemma for unknown field tags in `Unchunked.NoHeaderReceived` (`tag ∉ {1, 2}`) at `+0x184` (`entry + 388#64`). -/
theorem chunkedNoHeaderReceived_uc_skip_step {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 0xffffffffffff98f4#64) (decodeErrorPushSpec A))
    (hSkipCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 0xffffffffffffa9c0#64) (skipField3Spec A))
    {x : ChunkedNoHeaderReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {hdr : Option PolynomialDecoder} {uc : V1State.Unchunked.NoHeaderReceived}
    {rest : List (BitVec 8)} {iwt : WireType} {tag outerLimit innerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (htag_lt : tag < 2 ^ 32)
    (hnone_of_sf : skipField (2 * rest.length + 2) 97 tag iwt rest = none →
      (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (rest' : List (BitVec 8)) (s' : State),
      skipField (2 * rest.length + 2) 97 tag iwt rest = some rest' →
      s'.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 408#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s'
        (chunkedNoHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr hdr uc x.bs rest')
        (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 388#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : (s.readReg64 (Reg.gpr 1#5)).setWidth 32 = BitVec.ofNat 32 tag)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
      (chunkedNoHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr hdr uc x.bs rest)
      (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hpush_exit := @chunkedNoHeaderReceived_uc_push_exit img A H hPushCall x R s0 { receivingHdr := hdr, uc := some uc }
  chunkedNoHeaderReceivedMerge_fetches img.base H 388 20
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName = entry; examples_hide_fetches
  apply SepWPpIn.of_sepWP (mid := entry + 0xffffffffffffa9c0#64)
  conv => arg 4; rw [chunkedNoHeaderReceivedUcLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
    chunkedInlBelow_skipField97 s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpIn.call_frame (x := ⟨iwt, tag, 97, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := entry + 400#64) hSkipCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
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
    apply SepWPpIn.of_sepWP (mid := entry + 696#64)
    (conv => arg 4; simp only [skipField3Spec, hsf, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (chunkedInlBelow_skipField97_entails s0.sp) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (unchunked2CapAt_entails_chunkedNoHeaderReceivedPBAt A x.msgPtr rest.length hdr uc) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPpIn.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { receivingHdr := hdr, uc := some uc } x.bs)
      (by dsimp only [chunkedNoHeaderReceivedErrFrame]; sep_entail)
    exact hpush_exit hnone (by decide : 0 ≤ 2) hsm0 hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])
      ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some rest' =>
    have hrest'_le : rest'.length ≤ rest.length := (skip_length _).1 _ _ _ _ _ hsf
    apply SepWPpIn.of_sepWP (mid := entry + 408#64)
    (conv => arg 4; simp only [skipField3Spec, hsf, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    apply SepWP.fold (chunkedInlBelow_skipField97_entails s0.sp) (by sep_focus)
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (unchunked2CapAt_mono A (x.msgPtr + 0x28#64) uc.epoch uc.auth hrest'_le) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPpIn.weaken_pre (P' := chunkedNoHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr hdr uc x.bs rest')
      (by dsimp only [chunkedNoHeaderReceivedUcLoopPre]; sep_entail)
    exact hcont rest' _ hsf
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm, hx19_m])
      (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m])
      (by simp only [arm64_norm, hx22_m]) (by simp only [arm64_norm, hx23_m])
      (by simp only [arm64_norm, hx24_m]) (by simp only [arm64_norm, hx25_m])
      (by simp only [arm64_norm, hx26_m])
      ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

/-- Step lemma for tag 1 (`epoch : u64`) in `Unchunked.NoHeaderReceived` when `iwt = .varint` at `+0x208` (`entry + 520#64`). -/
theorem chunkedNoHeaderReceived_uc_tag1_varint_step {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 0xffffffffffff98f4#64) (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 0xffffffffffffc318#64) (decodeVarint2Spec A))
    {x : ChunkedNoHeaderReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {hdr : Option PolynomialDecoder} {uc : V1State.Unchunked.NoHeaderReceived}
    {rest : List (BitVec 8)} {outerLimit innerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_dv : decodeVarint rest = none →
      (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (v : BitVec 64) (rest' : List (BitVec 8)) (s' : State),
      decodeVarint rest = some (v, rest') →
      s'.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 408#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s'
        (chunkedNoHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr hdr { uc with epoch := v } x.bs rest')
        (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 520#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = 0#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
      (chunkedNoHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr hdr uc x.bs rest)
      (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hfpush := @chunkedNoHeaderReceived_uc_field_push_exit img A H hPushCall x R s0 { receivingHdr := hdr, uc := some uc }
  chunkedNoHeaderReceivedMerge_fetches img.base H 520 44; chunkedNoHeaderReceivedMerge_fetches img.base H 404 4; chunkedNoHeaderReceivedMerge_fetches img.base H 852 36
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName = entry; examples_hide_fetches
  apply SepWPpIn.of_sepWP (mid := entry + 0xffffffffffffc318#64)
  conv => arg 4; rw [chunkedNoHeaderReceivedUcLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
    chunkedInlBelow_decodeVarint2 s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpIn.call_frame (x := ⟨x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := entry + 532#64) hVarintCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
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
    apply SepWPpIn.of_sepWP (mid := entry + 920#64)
    (conv => arg 4; simp only [decodeVarint2Spec, hdv, memRegion_48_cells1_160 s0.sp,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp])
    apply SepWP.exists_elim; intro v_stk0; apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
    have hcbnz_err : (sm.readReg64 (Reg.gpr 1#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm1
    apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (unchunked2CapAt_entails_chunkedNoHeaderReceivedPBAt A x.msgPtr rest.length hdr uc) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPpIn.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 1#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { receivingHdr := hdr, uc := some uc } x.bs)
      (by dsimp only [chunkedNoHeaderReceivedErrFrame]; sep_entail)
    exact hfpush hnone (by decide : 0 ≤ 1) hsm1 hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm, hspm])
      ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨v, rest'⟩
    have hrest'_le : rest'.length ≤ rest.length := Nat.le_of_lt (decodeVarint_length hdv)
    apply SepWPpIn.of_sepWP (mid := entry + 408#64)
    (conv => arg 4; simp only [decodeVarint2Spec, hdv, unchunked2CapAt, sepConj_assoc, arm64_norm, hsp])
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
    apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (optAuthenticatorPBCapAt_mono A (x.msgPtr + 0x28#64) uc.auth hrest'_le) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPpIn.weaken_pre (P' := chunkedNoHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr hdr { uc with epoch := v } x.bs rest')
      (by dsimp only [chunkedNoHeaderReceivedUcLoopPre, unchunked2CapAt]; simp only [arm64_norm]; sep_entail)
    exact hcont v rest' _ hdv
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
      (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m]) (by simp only [arm64_norm, hx25_m]) (by simp only [arm64_norm, hx26_m])
      ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

/-- Step lemma for tag 1 (`epoch : u64`) wire-type error (`iwt ≠ .varint`) at `+0x208` (`entry + 520#64`). -/
theorem chunkedNoHeaderReceived_uc_tag1_wt_err_step {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 0xffffffffffff9bec#64) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 0xffffffffffff98f4#64) (decodeErrorPushSpec A))
    {x : ChunkedNoHeaderReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {hdr : Option PolynomialDecoder} {uc : V1State.Unchunked.NoHeaderReceived}
    {rest : List (BitVec 8)} {iwt : WireType}
    (hiwt : iwt ≠ .varint) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone : (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 520#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
      (chunkedNoHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr hdr uc x.bs rest)
      (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hcbnz_wt : (BitVec.ofNat 64 iwt.toNat == 0#64) = false := iwt_cbnz_true_of_ne_varint hiwt
  have hfpush := @chunkedNoHeaderReceived_uc_field_push_exit img A H hPushCall x R s0 { receivingHdr := hdr, uc := some uc }
  chunkedNoHeaderReceivedMerge_fetches img.base H 520 4; chunkedNoHeaderReceivedMerge_fetches img.base H 820 68
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName = entry; examples_hide_fetches
  apply SepWPpIn.of_sepWP (mid := entry + 0xffffffffffff9bec#64)
  conv => arg 4; rw [chunkedNoHeaderReceivedUcLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
    sliceCursorAt, chunkedInlBelow_decodeErrorHook s0.sp, memRegion_48_wtErr160 s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro b_wt1; apply SepWP.exists_elim; intro b_wt0; apply SepWP.exists_elim; intro v_wt0
  wp_steps
  apply SepWP.fold (wtErr160_entails_memRegion40 s0.sp _ _) (by sep_focus)
  apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
  apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
  apply SepWP.fold (unchunked2CapAt_entails_chunkedNoHeaderReceivedPBAt A x.msgPtr rest.length hdr uc) (by sep_focus)
  wp_reach
  refine SepWPpIn.call_frame (x := (s0.sp - 128#64, 0x8000000000000006#64))
    (ret_pc := entry + 848#64) hFromCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorFromSpec]; simp only [arm64_norm, hsp]; rfl)
    (by decide : KindNoHeap 0x8000000000000006#64) (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, _, _, _, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx27, hx28, hvregs] at hpcm hspm hx27_m hx28_m hvregs_m
  apply SepWPpIn.of_sepWP (mid := entry + 920#64)
  (conv => arg 4; simp only [decodeErrorFromSpec, memRegion_48_cells1_160 s0.sp,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp])
  apply SepWP.exists_elim; intro v_stk0; apply SepWP.pure_elim; rintro ⟨hsm0, htrm⟩
  apply SepWP.fold (chunkedInlBelow_decodeErrorHook_entails s0.sp) (by sep_focus)
  wp_steps; wp_reach
  apply SepWPpIn.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { receivingHdr := hdr, uc := some uc } x.bs)
    (by dsimp only [chunkedNoHeaderReceivedErrFrame]; sep_entail)
  exact hfpush hnone (by decide : 0 ≤ 1) hsm0 hsp_align
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
    (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm, hspm])
    ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

/-- Prepares `optAuthenticatorPBCapAt` at `+0x1dc` (`entry + 476#64`) into `authenticatorPBCapAt` at `+0x1f4` (`entry + 500#64`). -/
theorem chunkedNoHeaderReceived_uc_auth_init {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    {x : ChunkedNoHeaderReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {hdr : Option PolynomialDecoder} {uc : V1State.Unchunked.NoHeaderReceived} {rest : List (BitVec 8)}
    (hcont : ∀ (s' : State),
      s'.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 500#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s.trace →
      s'.readReg64 (Reg.gpr 0#5) = s.readReg64 (Reg.gpr 0#5) →
      s'.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) →
      s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) →
      s'.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) →
      s'.readReg64 (Reg.gpr 23#5) = s.readReg64 (Reg.gpr 23#5) →
      s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      s'.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) →
      s'.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s'
        (optPolynomialDecoderPBAt A x.msgPtr hdr ∗
          authenticatorPBCapAt A (x.msgPtr + 0x28#64) rest.length (uc.auth.getD default) ∗
          ((x.msgPtr + 0x58#64) ↦₆₄ uc.epoch) ∗
          stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
          memRegion (s0.sp - 128#64) 48 ∗
          chunkedInlSavedRegs10 s0.sp s0 ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool)
        (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 476#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr) (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
      (chunkedNoHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr hdr uc x.bs rest)
      (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  chunkedNoHeaderReceivedMerge_fetches img.base H 476 24
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName = entry; examples_hide_fetches
  rcases hauth : uc.auth with _ | auth
  · rw [hauth] at hcont; apply SepWPpIn.of_sepWP (mid := entry + 500#64)
    conv => arg 4; rw [chunkedNoHeaderReceivedUcLoopPre, unchunked2CapAt, hauth, optAuthenticatorPBCapAt,
      memRegion_40_cells (x.msgPtr + 0x28#64)]
    simp only [noneCap, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm]
    apply SepWP.exists_elim; intro w1; apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
    apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5
    wp_steps
    have hdef := default_cells_entails_authenticatorPBCapAt A (x.msgPtr + 0x28#64) rest.length
    simp only [arm64_norm] at hdef; apply SepWP.fold hdef (by sep_focus); wp_reach
    apply SepWPpIn.weaken_pre (P' := optPolynomialDecoderPBAt A x.msgPtr hdr ∗ authenticatorPBCapAt A (x.msgPtr + 0x28#64) rest.length (Option.getD none default) ∗ ((x.msgPtr + 0x58#64) ↦₆₄ uc.epoch) ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedInlSavedRegs10 s0.sp s0 ∗ (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool)
      (Entails.of_eq (by dsimp only [Option.getD]; ac_rfl))
    exact hcont _ (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
      (by try simp only [arm64_norm]) (by try simp only [arm64_norm]) (by try simp only [arm64_norm])
      (by simp only [arm64_norm, hx20]) (by try simp only [arm64_norm]) (by try simp only [arm64_norm])
      (by try simp only [arm64_norm]) (by simp only [arm64_norm, hx24]) (by try simp only [arm64_norm]) (by try simp only [arm64_norm])
      ⟨by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩
  · rw [hauth] at hcont; apply SepWPpIn.of_sepWP (mid := entry + 500#64)
    conv => arg 4; rw [chunkedNoHeaderReceivedUcLoopPre, unchunked2CapAt, hauth, optAuthenticatorPBCapAt]
    simp only [sepConj_assoc, arm64_norm]
    have hcmn_in := authenticatorPBCapAt_entails_cmn A (x.msgPtr + 0x28#64) rest.length auth
    simp only [arm64_norm] at hcmn_in; apply SepWP.fold hcmn_in (by sep_focus)
    wp_simp_pre [sepExists_sepConj_left, sepConj_assoc, arm64_norm]
    apply SepWP.exists_elim; intro cap_ik; apply SepWP.exists_elim; intro ptr_ik
    apply SepWP.pure_elim; rintro ⟨hcap_lt, hcap_ik⟩
    have hcmn1 := cap_add_one_beq_zero_false hcap_lt; have hcmn2 := cap_add_one_bne_zero_true hcap_lt
    wp_steps
    have hcmn_out := cmn_entails_authenticatorPBCapAt A (x.msgPtr + 0x28#64) rest.length auth cap_ik ptr_ik hcap_ik
    simp only [arm64_norm] at hcmn_out; apply SepWP.fold hcmn_out (by sep_focus); wp_reach
    apply SepWPpIn.weaken_pre (P' := optPolynomialDecoderPBAt A x.msgPtr hdr ∗ authenticatorPBCapAt A (x.msgPtr + 0x28#64) rest.length (Option.getD (some auth) default) ∗ ((x.msgPtr + 0x58#64) ↦₆₄ uc.epoch) ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedInlSavedRegs10 s0.sp s0 ∗ (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool)
      (Entails.of_eq (by dsimp only [Option.getD]; ac_rfl))
    exact hcont _ (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
      (by try simp only [arm64_norm]) (by try simp only [arm64_norm]) (by try simp only [arm64_norm])
      (by simp only [arm64_norm, hx20]) (by try simp only [arm64_norm]) (by try simp only [arm64_norm])
      (by try simp only [arm64_norm]) (by simp only [arm64_norm, hx24]) (by try simp only [arm64_norm]) (by try simp only [arm64_norm])
      ⟨by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩

/-- Step lemma for tag 2 (`auth : Option<Authenticator>`) in `Unchunked.NoHeaderReceived` at `+0x1dc` (`entry + 476#64`). -/
theorem chunkedNoHeaderReceived_uc_tag2_step {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 0xffffffffffff98f4#64) (decodeErrorPushSpec A))
    (hAuthCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 0xffffffffffffcd84#64) ((authMergeSpec A).inImage img))
    {x : ChunkedNoHeaderReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {hdr : Option PolynomialDecoder} {uc : V1State.Unchunked.NoHeaderReceived}
    {rest : List (BitVec 8)} {iwt : WireType} {outerLimit innerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_auth : (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto iwt) (uc.auth.getD default) rest 97).toOption = none →
      (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (auth' : ProtoAuthenticator) (rest' : List (BitVec 8)) (s' : State),
      (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto iwt) (uc.auth.getD default) rest 97).toOption = some (auth', rest') →
      s'.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 408#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s'
        (chunkedNoHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr hdr { uc with auth := some auth' } x.bs rest')
        (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 476#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
      (chunkedNoHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr hdr uc x.bs rest)
      (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  have hfpush := fun {auth' : ProtoAuthenticator} => @chunkedNoHeaderReceived_uc_field_push_exit img A H hPushCall x R s0 { receivingHdr := hdr, uc := some { epoch := uc.epoch, auth := some auth' } }
  refine chunkedNoHeaderReceived_uc_auth_init ?_ hpc hrun hsp hx20 hx24 hcs
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hcs1
  rw [htr] at htr1; rw [hx0] at hx0_1; rw [hx19] at hx19_1; rw [hx21] at hx21_1
  rw [hx22] at hx22_1; rw [hx23] at hx23_1; rw [hx25] at hx25_1; rw [hx26] at hx26_1
  obtain ⟨hx27_1, hx28_1, hvregs_1⟩ := hcs1
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  chunkedNoHeaderReceivedMerge_fetches img.base H 500 20; chunkedNoHeaderReceivedMerge_fetches img.base H 544 8
  chunkedNoHeaderReceivedMerge_fetches img.base H 404 4; chunkedNoHeaderReceivedMerge_fetches img.base H 888 32
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName = entry; examples_hide_fetches
  apply SepWPpIn.of_sepWP (mid := entry + 0xffffffffffffcd84#64)
  conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, chunkedInlBelow_authMerge s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpIn.call_frame_inImage (x := ⟨iwt, x.msgPtr + 0x28#64, uc.auth.getD default, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := entry + 512#64) hAuthCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
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
    apply SepWPpIn.of_sepWP (mid := entry + 920#64)
    (conv => arg 4; simp only [authMergeSpec, hauth_res, memRegion_48_cells1_160 s0.sp,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp1])
    apply SepWP.exists_elim; intro v_stk0; apply SepWP.exists_elim; intro auth'; apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; intro hpure
    have htrm : sm.trace = _ := hpure.1; have hsm0 : sm.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hpure.2.1; have hn_err : n_err ≤ 1 := hpure.2.2
    have hcbz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (chunkedInlBelow_authMerge_entails s0.sp) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPpIn.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { receivingHdr := hdr, uc := some { epoch := uc.epoch, auth := some auth' } } x.bs)
      (by dsimp only [chunkedNoHeaderReceivedErrFrame, chunkedNoHeaderReceivedPBAt, optNoHeaderReceivedPBAt, noHeaderReceivedPBAt, unchunked2At, optAuthenticatorPBAt]; simp only [arm64_norm]; sep_entail)
    exact hfpush hnone hn_err hsm0 hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr1]) (by simp only [arm64_norm, hspm])
      ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨auth', rest'⟩
    have hrest'_le : rest'.length ≤ rest.length := (proto_mergeMessage_suffix hauth_res).1
    apply SepWPpIn.of_sepWP (mid := entry + 408#64)
    (conv => arg 4; simp only [authMergeSpec, hauth_res, sepConj_assoc, arm64_norm, hsp1])
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    apply SepWP.fold (chunkedInlBelow_authMerge_entails s0.sp) (by sep_focus)
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPpIn.weaken_pre (P' := chunkedNoHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr hdr { uc with auth := some auth' } x.bs rest')
      (by dsimp only [chunkedNoHeaderReceivedUcLoopPre, unchunked2CapAt, optAuthenticatorPBCapAt]; simp only [arm64_norm]; sep_entail)
    exact hcont auth' rest' _ hauth_res
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr1])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
      (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m]) (by simp only [arm64_norm, hx25_m]) (by simp only [arm64_norm, hx26_m])
      ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

/-- Inner loop exit at `+0x198` (`entry + 408#64`) when `cur.length ≤ innerLimit`:
if `cur.length = innerLimit`, branches to outer loop header `+0x0a8` (`entry + 168#64`);
if `cur.length < innerLimit`, branches to `+0x3ac -> +0x2a8` and returns `Err(Truncated)` with `("NoHeaderReceived", "uc")` pushed. -/
theorem chunkedNoHeaderReceived_uc_loop_le_exit {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 0xffffffffffff9bec#64) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 0xffffffffffff98f4#64) (decodeErrorPushSpec A))
    {x : ChunkedNoHeaderReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {hdr : Option PolynomialDecoder} {uc : V1State.Unchunked.NoHeaderReceived}
    {cur : List (BitVec 8)} {outerLimit innerLimit : Nat}
    (hle_lim : cur.length ≤ innerLimit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_suf : IsDropSuffix x.bs cur) (hlim_lt : innerLimit < 2 ^ 63)
    (hnone_of_lt : cur.length < innerLimit →
      (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (s' : State),
      cur.length = innerLimit →
      s'.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 168#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s'
        (chunkedNoHeaderReceivedLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { receivingHdr := hdr, uc := some uc } x.bs cur)
        (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 408#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
      (chunkedNoHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr hdr uc x.bs cur)
      (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  by_cases heq_lim : cur.length = innerLimit
  · obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq heq_lim
    chunkedNoHeaderReceivedMerge_fetches img.base H 408 12; chunkedNoHeaderReceivedMerge_fetches img.base H 564 12
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName = entry; examples_hide_fetches
    apply SepWPpIn.of_sepWP (mid := entry + 168#64)
    conv => arg 4; rw [chunkedNoHeaderReceivedUcLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt]
    simp only [sepConj_assoc]; wp_steps
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    wp_reach
    apply SepWPpIn.weaken_pre (P' := chunkedNoHeaderReceivedLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { receivingHdr := hdr, uc := some uc } x.bs cur)
      (by dsimp only [chunkedNoHeaderReceivedLoopPre, chunkedNoHeaderReceivedPBCapAt, optNoHeaderReceivedPBCapAt, unchunked2CapAt, sliceCursorAfter]; sep_entail)
    exact hcont _ heq_lim
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr])
      (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20]) (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22])
      (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24]) (by simp only [arm64_norm, hx25])
      ⟨by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩
  · have hlt_lim : cur.length < innerLimit := Nat.lt_of_le_of_ne hle_lim heq_lim
    obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_lt hlt_lim hlim_lt
    have hnone := hnone_of_lt hlt_lim
    have hfrom_push := @chunkedNoHeaderReceived_uc_from_push_exit img A H hFromCall hPushCall x R s0 { receivingHdr := hdr, uc := some uc }
    chunkedNoHeaderReceivedMerge_fetches img.base H 408 12; chunkedNoHeaderReceivedMerge_fetches img.base H 564 4
    chunkedNoHeaderReceivedMerge_fetches img.base H 940 16; chunkedNoHeaderReceivedMerge_fetches img.base H 680 4
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName = entry; examples_hide_fetches
    apply SepWPpIn.of_sepWP (mid := entry + 684#64)
    conv => arg 4; rw [chunkedNoHeaderReceivedUcLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
      sliceCursorAt, memRegion_48_cells1_160 s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v_stk0; wp_steps
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot curPtr (BitVec.ofNat 64 cur.length)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    apply SepWP.fold (unchunked2CapAt_entails_chunkedNoHeaderReceivedPBAt A x.msgPtr cur.length hdr uc) (by sep_focus)
    wp_reach
    apply SepWPpIn.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000008#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { receivingHdr := hdr, uc := some uc } x.bs)
      (by dsimp only [chunkedNoHeaderReceivedErrFrame]; sep_entail)
    exact hfrom_push hnone (by decide : KindNoHeap 0x8000000000000008#64) hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr])
      ⟨by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩

/-- Inner loop key-decode step at `+0x198` (`entry + 408#64`) when `¬ cur.length ≤ innerLimit`:
decodes the field key varint and validates `key < 2^32`, `WireType.ofNat? (key % 8) = some iwt`, and `1 ≤ key / 8`,
reaching `+0x1cc` (`entry + 460#64`) on success or exiting via `uc_push_exit` / `uc_from_push_exit` on error. -/
theorem chunkedNoHeaderReceived_uc_decode_key_step {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 0xffffffffffff9bec#64) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 0xffffffffffff98f4#64) (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 0xffffffffffffc318#64) (decodeVarint2Spec A))
    {x : ChunkedNoHeaderReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {hdr : Option PolynomialDecoder} {uc : V1State.Unchunked.NoHeaderReceived}
    {cur : List (BitVec 8)} {outerLimit innerLimit : Nat}
    (hgt_lim : ¬ cur.length ≤ innerLimit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_lt : cur.length < 2 ^ 63) (hcur_suf : IsDropSuffix x.bs cur)
    (hnone_of_uc_none :
      mergeLoopBin V1State.Unchunked.NoHeaderReceived.mergeField (cur.length - innerLimit) uc cur innerLimit 97 = none →
      (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (key : BitVec 64) (iwt : WireType) (rest : List (BitVec 8)) (s' : State),
      decodeVarint cur = some (key, rest) → ¬ 2 ^ 32 ≤ key.toNat →
      WireType.ofNat? (key.toNat % 8) = some iwt → ¬ key.toNat / 8 < 1 →
      s'.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 460#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s'
        (chunkedNoHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr hdr uc x.bs rest)
        (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 408#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
      (chunkedNoHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr hdr uc x.bs cur)
      (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  have hpush_exit := @chunkedNoHeaderReceived_uc_push_exit img A H hPushCall x R s0 { receivingHdr := hdr, uc := some uc }
  have hfrom_push := @chunkedNoHeaderReceived_uc_from_push_exit img A H hFromCall hPushCall x R s0 { receivingHdr := hdr, uc := some uc }
  chunkedNoHeaderReceivedMerge_fetches img.base H 408 52; chunkedNoHeaderReceivedMerge_fetches img.base H 636 48
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName = entry; examples_hide_fetches
  apply SepWPpIn.of_sepWP (mid := entry + 0xffffffffffffc318#64)
  conv => arg 4; rw [chunkedNoHeaderReceivedUcLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
    sliceCursorAt, chunkedInlBelow_decodeVarint2 s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpIn.call_frame (x := ⟨x.bufRef, x.slot, curPtr, cur⟩)
    (ret_pc := entry + 428#64) hVarintCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, hsp, hx19]; rfl)
    hcur_lt (by dsimp only [sliceCursorAt, curPtr]; sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
  cases hd : decodeVarint cur with
  | none =>
    have hnone := hnone_of_uc_none (mergeLoopBin_of_decodeVarint_none protoPrefixStep_unchunked_noHeaderReceived_mergeField hgt_lim hd)
    apply SepWPpIn.of_sepWP (mid := entry + 696#64)
    (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
    apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    apply SepWP.fold (unchunked2CapAt_entails_chunkedNoHeaderReceivedPBAt A x.msgPtr cur.length hdr uc) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPpIn.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { receivingHdr := hdr, uc := some uc } x.bs)
      (by dsimp only [chunkedNoHeaderReceivedErrFrame]; sep_entail)
    exact hpush_exit hnone (by decide : 0 ≤ 2) hsm1 hsp_align
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
    · have hnone := hnone_of_uc_none (mergeLoopBin_of_key_ge protoPrefixStep_unchunked_noHeaderReceived_mergeField hgt_lim hd hk_ge)
      have hshr := key_shr32_of_ge hk_ge
      apply SepWPpIn.of_sepWP (mid := entry + 684#64)
      (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
      apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
      apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
      apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
      apply SepWP.fold (unchunked2CapAt_entails_chunkedNoHeaderReceivedPBAt A x.msgPtr cur.length hdr uc) (by sep_focus)
      conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_cells2_160 s0.sp]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply SepWP.exists_elim; intro v_err0; apply SepWP.exists_elim; intro v_err1; wp_steps
      apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
      apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
      have h40 : ((s0.sp - 128#64 + 8#64) ↦₆₄ key) ∗ memRegion (s0.sp - 112#64) 32 ⊢ memRegion (s0.sp - 120#64) 40 := by
        rw [bv_sub_add_lit s0.sp 128 8]; exact cells2_memRegion32_entails_40_160 s0.sp key
      apply SepWP.fold h40 (by sep_focus); wp_reach
      apply SepWPpIn.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000004#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { receivingHdr := hdr, uc := some uc } x.bs)
        (by dsimp only [chunkedNoHeaderReceivedErrFrame]; sep_entail)
      exact hfrom_push hnone (by decide : KindNoHeap 0x8000000000000004#64) hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
        ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
    · have hshr := key_shr32_of_lt hk_ge
      cases hwt : WireType.ofNat? (key.toNat % 8) with
      | none =>
        have hnone := hnone_of_uc_none (mergeLoopBin_of_wt_none protoPrefixStep_unchunked_noHeaderReceived_mergeField hgt_lim hd hk_ge hwt)
        obtain ⟨hcs1, hcs2⟩ := key_wt_none hwt
        apply SepWPpIn.of_sepWP (mid := entry + 684#64)
        (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
        apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
        apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
        apply SepWP.fold (unchunked2CapAt_entails_chunkedNoHeaderReceivedPBAt A x.msgPtr cur.length hdr uc) (by sep_focus)
        conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_cells2_160 s0.sp]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        apply SepWP.exists_elim; intro v_err0; apply SepWP.exists_elim; intro v_err1; wp_steps
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        have h40 : ((s0.sp - 128#64 + 8#64) ↦₆₄ (key &&& 7#64)) ∗ memRegion (s0.sp - 112#64) 32 ⊢ memRegion (s0.sp - 120#64) 40 := by
          rw [bv_sub_add_lit s0.sp 128 8]; exact cells2_memRegion32_entails_40_160 s0.sp (key &&& 7#64)
        apply SepWP.fold h40 (by sep_focus); wp_reach
        apply SepWPpIn.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000003#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { receivingHdr := hdr, uc := some uc } x.bs)
          (by dsimp only [chunkedNoHeaderReceivedErrFrame]; sep_entail)
        exact hfrom_push hnone (by decide : KindNoHeap 0x8000000000000003#64) hsp_align
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
          ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
      | some iwt =>
        obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
        obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_ge; obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
        by_cases hitag0 : key.toNat / 8 < 1
        · have hnone := hnone_of_uc_none (mergeLoopBin_of_tag_zero protoPrefixStep_unchunked_noHeaderReceived_mergeField hgt_lim hd hk_ge hwt hitag0)
          have htag_zero : key.toNat / 8 = 0 := by omega
          apply SepWPpIn.of_sepWP (mid := entry + 684#64)
          (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
          apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
          apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          apply SepWP.fold (unchunked2CapAt_entails_chunkedNoHeaderReceivedPBAt A x.msgPtr cur.length hdr uc) (by sep_focus)
          conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_cells1_160 s0.sp]
          simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
          apply SepWP.exists_elim; intro v_err0; wp_steps
          apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
          apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus); wp_reach
          apply SepWPpIn.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000005#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { receivingHdr := hdr, uc := some uc } x.bs)
            (by dsimp only [chunkedNoHeaderReceivedErrFrame]; sep_entail)
          exact hfrom_push hnone (by decide : KindNoHeap 0x8000000000000005#64) hsp_align
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
            ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
        · obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_ge hitag0
          have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
            rw [beq_eq_false_iff_ne]; intro h; have h1 := congrArg BitVec.toNat h
            simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1; omega
          apply SepWPpIn.of_sepWP (mid := entry + 460#64)
          (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
          apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
          apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          apply SepWP.fold (unchunked2CapAt_mono A (x.msgPtr + 0x28#64) uc.epoch uc.auth hrest_le_cur) (by sep_focus)
          wp_steps; wp_reach
          apply SepWPpIn.weaken_pre (P' := chunkedNoHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr hdr uc x.bs rest)
            (by dsimp only [chunkedNoHeaderReceivedUcLoopPre]; sep_entail)
          exact hcont key iwt rest _ hd hk_ge hwt hitag0
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
            (by simp only [arm64_norm, hsm1, hand_wt]) (by simp only [arm64_norm, hsm1, hw1, hw1_2, hw1_zext1, hw1_zext2])
            (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
            (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m]) (by simp only [arm64_norm, hx25_m]) (by simp only [arm64_norm, hx26_m])
            ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

/-- Main inner loop induction at `+0x198` (`entry + 408#64`) for `V1State.Unchunked.NoHeaderReceived.mergeField`. -/
theorem chunkedNoHeaderReceived_uc_loop_ok {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 0xffffffffffff9bec#64) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 0xffffffffffff98f4#64) (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 0xffffffffffffc318#64) (decodeVarint2Spec A))
    (hSkipCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 0xffffffffffffa9c0#64) (skipField3Spec A))
    (hAuthCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 0xffffffffffffcd84#64) ((authMergeSpec A).inImage img))
    {x : ChunkedNoHeaderReceivedMergeGhost} {R : SepProp} {s0 : State} {hdr : Option PolynomialDecoder} {outerLimit innerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hbs_lt : x.bs.length < 2 ^ 63) (hlim_lt : innerLimit < 2 ^ 63) :
    ∀ (n : Nat) (uc : V1State.Unchunked.NoHeaderReceived) (cur : List (BitVec 8)) (s : State),
      cur.length ≤ n → cur.length ≤ x.bs.length → IsDropSuffix x.bs cur →
      (∀ (uc' : V1State.Unchunked.NoHeaderReceived) (rest' : List (BitVec 8)) (s' : State),
        rest'.length = innerLimit → rest'.length ≤ x.bs.length → IsDropSuffix x.bs rest' →
        mergeLoopBin V1State.Unchunked.NoHeaderReceived.mergeField (cur.length - innerLimit) uc cur innerLimit 97 = some uc' →
        s'.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 168#64 →
        s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
        s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
        s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
        s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 24#5) = 1#64 →
        s'.readReg64 (Reg.gpr 25#5) = 8#64 → ChunkedInl10CalleeSaved s0 s' →
        SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s'
          (chunkedNoHeaderReceivedLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { receivingHdr := hdr, uc := some uc' } x.bs rest')
          (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0)) →
      (mergeLoopBin V1State.Unchunked.NoHeaderReceived.mergeField (cur.length - innerLimit) uc cur innerLimit 97 = none →
        (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none) →
      s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName + 408#64 →
      s.status = .Running → s.sp = s0.sp - 128#64 → s.trace = s0.trace →
      s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s.readReg64 (Reg.gpr 24#5) = 1#64 →
      s.readReg64 (Reg.gpr 25#5) = 8#64 → s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s →
      SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
        (chunkedNoHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr hdr uc x.bs cur)
        (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  have htag1_varint := fun {s uc rest} => @chunkedNoHeaderReceived_uc_tag1_varint_step img A H hPushCall hVarintCall x R s0 s hdr uc rest outerLimit innerLimit
  have htag1_wt_err := fun {s uc rest iwt} => @chunkedNoHeaderReceived_uc_tag1_wt_err_step img A H hFromCall hPushCall x R s0 s hdr uc rest iwt
  have htag2_step := fun {s uc rest} (iwt : WireType) => @chunkedNoHeaderReceived_uc_tag2_step img A H hPushCall hAuthCall x R s0 s hdr uc rest iwt outerLimit innerLimit
  have hskip_step := fun {s uc rest} (iwt : WireType) (tag : Nat) => @chunkedNoHeaderReceived_uc_skip_step img A H hPushCall hSkipCall x R s0 s hdr uc rest iwt tag outerLimit innerLimit
  intro n; induction n with
  | zero =>
    intro uc cur s hcur_n hcur_le hcur_suf hok_cont hnone_cont hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
    exact chunkedNoHeaderReceived_uc_loop_le_exit hFromCall hPushCall (by omega) hsp_align hcur_le hcur_suf hlim_lt
      (fun hlt => hnone_cont (mergeLoopBin_lt_limit _ _ _ _ _ _ hlt))
      (fun s' heq => hok_cont uc cur s' heq hcur_le hcur_suf (mergeLoopBin_eq_limit _ _ _ _ _ _ heq))
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
  | succ n ih =>
    intro uc cur s hcur_n hcur_le hcur_suf hok_cont hnone_cont hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
    by_cases hle_lim : cur.length ≤ innerLimit
    · exact chunkedNoHeaderReceived_uc_loop_le_exit hFromCall hPushCall hle_lim hsp_align hcur_le hcur_suf hlim_lt
        (fun hlt => hnone_cont (mergeLoopBin_lt_limit _ _ _ _ _ _ hlt))
        (fun s' heq => hok_cont uc cur s' heq hcur_le hcur_suf (mergeLoopBin_eq_limit _ _ _ _ _ _ heq))
        hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
    · have hcur_lt : cur.length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
      refine chunkedNoHeaderReceived_uc_decode_key_step hFromCall hPushCall hVarintCall hle_lim hsp_align
        hcur_le hcur_lt hcur_suf hnone_cont ?_ hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
      intro key iwt rest s' hd hk_ge hwt hitag0 hpc' hrun' hsp' htr' hx0' hx1' hx19' hx20' hx21' hx22' hx23' hx24' hx25' hx26' hcs'
      obtain ⟨hx27', hx28', hvregs'⟩ := hcs'
      have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd; have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
      have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le; have hrest_lt : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest_le hbs_lt
      have hrest_suf : IsDropSuffix x.bs rest := suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
      have htag_lt : key.toNat / 8 < 2 ^ 32 := by omega
      have hstep := mergeLoopBin_of_key_ok (m := uc) (depth' := 97)
        protoPrefixStep_unchunked_noHeaderReceived_mergeField hle_lim hd hk_ge hwt hitag0
      by_cases htag1 : key.toNat / 8 = 1
      · rw [htag1] at hx1' hstep; rw [unchunkedNoHeaderReceived_mergeField_tag1] at hstep
        chunkedNoHeaderReceivedMerge_fetches img.base H 460 16
        generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName = entry; examples_hide_fetches
        by_cases hiwt : iwt = .varint
        · subst hiwt; apply SepWPpIn.of_sepWP (mid := entry + 520#64); wp_steps; wp_reach
          refine htag1_varint hsp_align hrest_le hrest_lt hrest_suf
            (fun hdv => hnone_cont (by simp [hstep, hdv]))
            (fun v rest' s'' hdv hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs'' => ?_)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
            (by simp only [arm64_norm, hx0', WireType.toNat])
            (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20']) (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22'])
            (by simp only [arm64_norm, hx23']) (by simp only [arm64_norm, hx24']) (by simp only [arm64_norm, hx25']) (by simp only [arm64_norm, hx26'])
            ⟨by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩
          have hr'_lt : rest'.length < rest.length := decodeVarint_length hdv; have hr'_le : rest'.length ≤ rest.length := Nat.le_of_lt hr'_lt
          have hstep1 : mergeLoopBin V1State.Unchunked.NoHeaderReceived.mergeField (cur.length - innerLimit) uc cur innerLimit 97 =
              mergeLoopBin V1State.Unchunked.NoHeaderReceived.mergeField (rest'.length - innerLimit) { uc with epoch := v } rest' innerLimit 97 := by simp [hstep, hdv]
          exact ih { uc with epoch := v } rest' s'' (by omega) (Nat.le_trans hr'_le hrest_le)
            (suffix_trans hrest_le hrest_suf hr'_le (decodeVarint_suffix hdv))
            (fun uc' r'' s3 heq hr''_le hr''_suf hml => hok_cont uc' r'' s3 heq hr''_le hr''_suf (hstep1.trans hml))
            (fun hml => hnone_cont (hstep1.trans hml))
            hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs''
        · apply SepWPpIn.of_sepWP (mid := entry + 520#64); wp_steps; wp_reach
          exact htag1_wt_err hiwt hsp_align hrest_le hrest_suf (hnone_cont (by simp [hstep, hiwt]))
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
            (by simp only [arm64_norm, hx0']) ⟨by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩
      · by_cases htag2 : key.toNat / 8 = 2
        · rw [htag2] at hx1' hstep; rw [unchunkedNoHeaderReceived_mergeField_tag2] at hstep
          chunkedNoHeaderReceivedMerge_fetches img.base H 460 16
          generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName = entry; examples_hide_fetches
          apply SepWPpIn.of_sepWP (mid := entry + 476#64); wp_steps; wp_reach
          refine htag2_step iwt hsp_align hrest_le hrest_lt hrest_suf
            (fun hauth => hnone_cont (by simp [hstep, hauth]))
            (fun auth' rest' s'' hauth hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs'' => ?_)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
            (by simp only [arm64_norm, hx0'])
            (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20']) (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22'])
            (by simp only [arm64_norm, hx23']) (by simp only [arm64_norm, hx24']) (by simp only [arm64_norm, hx25']) (by simp only [arm64_norm, hx26'])
            ⟨by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩
          have hr'_le : rest'.length ≤ rest.length := (proto_mergeMessage_suffix hauth).1
          have hstep2 : mergeLoopBin V1State.Unchunked.NoHeaderReceived.mergeField (cur.length - innerLimit) uc cur innerLimit 97 =
              mergeLoopBin V1State.Unchunked.NoHeaderReceived.mergeField (rest'.length - innerLimit) { uc with auth := some auth' } rest' innerLimit 97 := by simp [hstep, hauth]
          exact ih { uc with auth := some auth' } rest' s'' (by omega) (Nat.le_trans hr'_le hrest_le)
            (suffix_trans hrest_le hrest_suf hr'_le (proto_mergeMessage_suffix hauth).2)
            (fun uc' r'' s3 heq hr''_le hr''_suf hml => hok_cont uc' r'' s3 heq hr''_le hr''_suf (hstep2.trans hml))
            (fun hml => hnone_cont (hstep2.trans hml))
            hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs''
        · obtain ⟨hb1_1, _⟩ := itag_beq_tag_false htag1 htag_lt (by decide : 1 < 2 ^ 32)
          obtain ⟨hb2_1, _⟩ := itag_beq_tag_false htag2 htag_lt (by decide : 2 < 2 ^ 32)
          have hb1_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 1#32) = false := by rw [sf_truncate32_ofNat64]; exact hb1_1
          have hb2_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 2#32) = false := by rw [sf_truncate32_ofNat64]; exact hb2_1
          have hb2_bne1 : (BitVec.ofNat 32 (key.toNat / 8) != 2#32) = true := by simp only [bne, hb2_1, Bool.not_false]
          have hb2_bne2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) != 2#32) = true := by simp only [bne, hb2_2, Bool.not_false]
          rw [unchunkedNoHeaderReceived_mergeField_other uc iwt rest 97 htag_lt htag1 htag2] at hstep
          chunkedNoHeaderReceivedMerge_fetches img.base H 460 16
          generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedNoHeaderReceivedMergeName = entry; examples_hide_fetches
          apply SepWPpIn.of_sepWP (mid := entry + 388#64); wp_steps; wp_reach
          refine hskip_step iwt (key.toNat / 8) hsp_align hrest_le hrest_lt hrest_suf htag_lt
            (fun hsf => hnone_cont (by simp [hstep, hsf]))
            (fun rest' s'' hsf hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs'' => ?_)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
            (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx1', sf_truncate32_ofNat64])
            (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20']) (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22'])
            (by simp only [arm64_norm, hx23']) (by simp only [arm64_norm, hx24']) (by simp only [arm64_norm, hx25']) (by simp only [arm64_norm, hx26'])
            ⟨by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩
          have hr'_le : rest'.length ≤ rest.length := (skip_length (2 * rest.length + 2)).1 _ _ _ _ _ hsf
          have hstep_other : mergeLoopBin V1State.Unchunked.NoHeaderReceived.mergeField (cur.length - innerLimit) uc cur innerLimit 97 =
              mergeLoopBin V1State.Unchunked.NoHeaderReceived.mergeField (rest'.length - innerLimit) uc rest' innerLimit 97 := by simp [hstep, hsf]
          exact ih uc rest' s'' (by omega) (Nat.le_trans hr'_le hrest_le)
            (suffix_trans hrest_le hrest_suf hr'_le ((skip_suffix (2 * rest.length + 2)).1 _ _ _ _ _ hsf))
            (fun uc' r'' s3 heq hr''_le hr''_suf hml => hok_cont uc' r'' s3 heq hr''_le hr''_suf (hstep_other.trans hml))
            (fun hml => hnone_cont (hstep_other.trans hml))
            hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs''

/-! ## 4. Placed (`[LibsignalPlacement]`) Exit, Step, and Inner Loop Lemmas for Block `308` -/

set_option quotPrecheck false in
local notation "entry" => (blkPl_308).base

theorem chunkedNoHeaderReceived_ret_err_exit_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    {x : ChunkedNoHeaderReceivedMergeGhost} {R : SepProp} {s0 : State} {m : V1State.Chunked.NoHeaderReceived} {s : State}
    {err : BitVec 64} {n : Nat}
    (hnone : (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hn : n ≤ 3) (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_308).base + 128#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = err) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_308).rebase (blkPl_308).base H) (s0.readReg64 Reg.lr) s
      (decodeErrorAtStackLen A err n ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
        memRegion (s0.sp - 128#64) 48 ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  apply SepWPpLscro.of_sepWP_ret; unfold WppPost chunkedNoHeaderReceivedMergeSpec
  simp only [hnone, chunkedNoHeaderReceivedErrFrame, chunkedInlSavedRegs10,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp, hx0]
  apply SepWP.fold (decodeErrorWith_le3_nhr A err hn) (by sep_focus)
  apply SepWP.fold (chunkedNoHeaderReceivedPBAt_entails_exists A x.msgPtr m) (by sep_focus)
  wp_steps; apply SepWP.fold (stackAt_chunkedInl10_epilogue s0.sp s0) (by unfold chunkedInlSavedRegs10; sep_focus); wp_done

theorem chunkedNoHeaderReceived_from_err_exit_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 261) (decodeErrorFromSpec A))
    {x : ChunkedNoHeaderReceivedMergeGhost} {R : SepProp} {s0 : State} {m : V1State.Chunked.NoHeaderReceived} {s : State} {w : BitVec 64}
    (hnone : (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hw : KindNoHeap w) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_308).base + 120#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_308).rebase (blkPl_308).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ w) ∗ memRegion (s0.sp - 120#64) 40 ∗
        stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  apply SepWPpLscro.of_sepWP (mid := lsmpl.base 261)
  conv => arg 4; rw [chunkedNoHeaderReceivedErrFrame, chunkedInlBelow_decodeErrorHook s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpLscro.call_frame (x := (s0.sp - 128#64, w))
    (ret_pc := entry + 128#64) hFromCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorFromSpec]; simp only [arm64_norm, hsp]; rfl) hw (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, _, _, _, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx27, hx28, hvregs] at hpcm hspm hx27_m hx28_m hvregs_m
  apply SepWPpLscro.of_sepWP_ret; unfold WppPost chunkedNoHeaderReceivedMergeSpec
  simp only [decodeErrorFromSpec, hnone, chunkedNoHeaderReceivedErrFrame, chunkedInlSavedRegs10,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp, hspm]
  apply SepWP.fold (chunkedInlBelow_decodeErrorHook_entails s0.sp) (by sep_focus)
  apply SepWP.fold (memRegion8_memRegion40_entails_48_160 s0.sp) (by sep_focus)
  apply SepWP.fold (decodeErrorWith_le3_nhr A (sm.readReg64 (Reg.gpr 0#5)) (by decide : 0 ≤ 3)) (by sep_focus)
  apply SepWP.fold (chunkedNoHeaderReceivedPBAt_entails_exists A x.msgPtr m) (by sep_focus)
  wp_steps; apply SepWP.fold (stackAt_chunkedInl10_epilogue s0.sp s0) (by unfold chunkedInlSavedRegs10; sep_focus); wp_done

theorem chunkedNoHeaderReceived_push_ret_exit_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    {x : ChunkedNoHeaderReceivedMergeGhost} {R : SepProp} {s0 : State} {m : V1State.Chunked.NoHeaderReceived} {s : State}
    {err : BitVec 64} {n : Nat}
    (hnone : (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hn : n ≤ 2) (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_308).base + 728#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = s0.sp - 128#64) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_308).rebase (blkPl_308).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A err n ∗ memRegion (s0.sp - 120#64) 40 ∗
        stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; have hret := @chunkedNoHeaderReceived_ret_err_exit_placed _ A H x R s0 m
  apply SepWPpLscro.of_sepWP (mid := lsmpl.base 257)
  conv => arg 4; rw [chunkedNoHeaderReceivedErrFrame, chunkedInlBelow_decodeErrorHook s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpLscro.call_frame (x := (s0.sp - 128#64, err, n))
    (ret_pc := entry + 732#64) hPushCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
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
  apply SepWPpLscro.weaken_pre (P' := decodeErrorAtStackLen A err (n + 1) ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
    (by dsimp only [chunkedNoHeaderReceivedErrFrame]; sep_entail)
  exact hret hnone (by omega : n + 1 ≤ 3) herr hsp_align
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
    (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])
    ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

theorem chunkedNoHeaderReceived_uc_push_exit_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    {x : ChunkedNoHeaderReceivedMergeGhost} {R : SepProp} {s0 : State} {m : V1State.Chunked.NoHeaderReceived} {s : State}
    {err : BitVec 64} {n : Nat}
    (hnone : (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hn : n ≤ 2) (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_308).base + 696#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 (Reg.gpr 1#5) = err) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_308).rebase (blkPl_308).base H) (s0.readReg64 Reg.lr) s
      (decodeErrorAtStackLen A err n ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
        memRegion (s0.sp - 128#64) 48 ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; have hpush := @chunkedNoHeaderReceived_push_ret_exit_placed _ A H hPushCall x R s0 m
  apply SepWPpLscro.of_sepWP (mid := entry + 728#64)
  conv => arg 4; rw [memRegion_48_cells1_160 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, hx1]
  apply SepWP.exists_elim; intro v_stk0; wp_steps; wp_reach
  apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A err n ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
    (by sep_entail)
  exact hpush hnone hn herr hsp_align
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hsp])
    ⟨by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩

theorem chunkedNoHeaderReceived_uc_from_push_exit_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 261) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    {x : ChunkedNoHeaderReceivedMergeGhost} {R : SepProp} {s0 : State} {m : V1State.Chunked.NoHeaderReceived} {s : State} {w : BitVec 64}
    (hnone : (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hw : KindNoHeap w) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_308).base + 684#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64)
    (htr : s.trace = s0.trace) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_308).rebase (blkPl_308).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ w) ∗ memRegion (s0.sp - 120#64) 40 ∗
        stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
        chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  have hpush := @chunkedNoHeaderReceived_uc_push_exit_placed _ A H hPushCall x R s0 m
  apply SepWPpLscro.of_sepWP (mid := lsmpl.base 261)
  conv => arg 4; rw [chunkedNoHeaderReceivedErrFrame, chunkedInlBelow_decodeErrorHook s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpLscro.call_frame (x := (s0.sp - 128#64, w))
    (ret_pc := entry + 692#64) hFromCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorFromSpec]; simp only [arm64_norm, hsp]; rfl)
    hw (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, _, _, _, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx27, hx28, hvregs] at hpcm hspm hx27_m hx28_m hvregs_m
  apply SepWPpLscro.of_sepWP (mid := entry + 696#64)
  (conv => arg 4; simp only [decodeErrorFromSpec, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨hsm0, htrm⟩
  apply SepWP.fold (chunkedInlBelow_decodeErrorHook_entails s0.sp) (by sep_focus)
  apply SepWP.fold (memRegion8_memRegion40_entails_48_160 s0.sp) (by sep_focus)
  wp_steps; wp_reach
  apply SepWPpLscro.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
    (by dsimp only [chunkedNoHeaderReceivedErrFrame]; sep_entail)
  exact hpush hnone (by decide : 0 ≤ 2) hsm0 hsp_align
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
    (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])
    ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

theorem chunkedNoHeaderReceived_uc_field_push_exit_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    {x : ChunkedNoHeaderReceivedMergeGhost} {R : SepProp} {s0 : State} {m : V1State.Chunked.NoHeaderReceived} {s : State}
    {err : BitVec 64} {n : Nat}
    (hnone : (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hn : n ≤ 1) (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_308).base + 920#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = s0.sp - 128#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_308).rebase (blkPl_308).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A err n ∗ memRegion (s0.sp - 120#64) 40 ∗
        stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
        chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  have hpush := @chunkedNoHeaderReceived_uc_push_exit_placed _ A H hPushCall x R s0 m
  apply SepWPpLscro.of_sepWP (mid := lsmpl.base 257)
  conv => arg 4; rw [chunkedNoHeaderReceivedErrFrame, chunkedInlBelow_decodeErrorHook s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpLscro.call_frame (x := (s0.sp - 128#64, err, n))
    (ret_pc := entry + 924#64) hPushCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorPushSpec]; simp only [arm64_norm, hsp, hx0]; rfl)
    (by omega : n < 2 ^ 32)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, _, _, _, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx27, hx28, hvregs] at hpcm hspm hx27_m hx28_m hvregs_m
  apply SepWPpLscro.of_sepWP (mid := entry + 696#64)
  (conv => arg 4; simp only [decodeErrorPushSpec, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; intro htrm
  apply SepWP.fold (chunkedInlBelow_decodeErrorHook_entails s0.sp) (by sep_focus)
  wp_steps
  apply SepWP.fold (pointsTo64_memRegion40_entails_48_160 s0.sp err) (by sep_focus)
  wp_reach
  apply SepWPpLscro.weaken_pre (P' := decodeErrorAtStackLen A err (n + 1) ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
    (by dsimp only [chunkedNoHeaderReceivedErrFrame]; sep_entail)
  exact hpush hnone (by omega : n + 1 ≤ 2) herr hsp_align
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
    (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])
    ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

theorem chunkedNoHeaderReceived_uc_skip_step_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    (hSkipCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 263) (skipField3Spec A))
    {x : ChunkedNoHeaderReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {hdr : Option PolynomialDecoder} {uc : V1State.Unchunked.NoHeaderReceived}
    {rest : List (BitVec 8)} {iwt : WireType} {tag outerLimit innerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (htag_lt : tag < 2 ^ 32)
    (hnone_of_sf : skipField (2 * rest.length + 2) 97 tag iwt rest = none →
      (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (rest' : List (BitVec 8)) (s' : State),
      skipField (2 * rest.length + 2) 97 tag iwt rest = some rest' →
      s'.pc = (blkPl_308).base + 408#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_308).rebase (blkPl_308).base H) (s0.readReg64 Reg.lr) s'
        (chunkedNoHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr hdr uc x.bs rest')
        (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_308).base + 388#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : (s.readReg64 (Reg.gpr 1#5)).setWidth 32 = BitVec.ofNat 32 tag)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_308).rebase (blkPl_308).base H) (s0.readReg64 Reg.lr) s
      (chunkedNoHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr hdr uc x.bs rest)
      (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hpush_exit := @chunkedNoHeaderReceived_uc_push_exit_placed _ A H hPushCall x R s0 { receivingHdr := hdr, uc := some uc }
  apply SepWPpLscro.of_sepWP (mid := lsmpl.base 263)
  conv => arg 4; rw [chunkedNoHeaderReceivedUcLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
    chunkedInlBelow_skipField97 s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpLscro.call_frame (x := ⟨iwt, tag, 97, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := entry + 400#64) hSkipCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
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
    apply SepWPpLscro.of_sepWP (mid := entry + 696#64)
    (conv => arg 4; simp only [skipField3Spec, hsf, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (chunkedInlBelow_skipField97_entails s0.sp) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (unchunked2CapAt_entails_chunkedNoHeaderReceivedPBAt A x.msgPtr rest.length hdr uc) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPpLscro.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { receivingHdr := hdr, uc := some uc } x.bs)
      (by dsimp only [chunkedNoHeaderReceivedErrFrame]; sep_entail)
    exact hpush_exit hnone (by decide : 0 ≤ 2) hsm0 hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])
      ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some rest' =>
    have hrest'_le : rest'.length ≤ rest.length := (skip_length _).1 _ _ _ _ _ hsf
    apply SepWPpLscro.of_sepWP (mid := entry + 408#64)
    (conv => arg 4; simp only [skipField3Spec, hsf, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    apply SepWP.fold (chunkedInlBelow_skipField97_entails s0.sp) (by sep_focus)
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (unchunked2CapAt_mono A (x.msgPtr + 0x28#64) uc.epoch uc.auth hrest'_le) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPpLscro.weaken_pre (P' := chunkedNoHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr hdr uc x.bs rest')
      (by dsimp only [chunkedNoHeaderReceivedUcLoopPre]; sep_entail)
    exact hcont rest' _ hsf
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm, hx19_m])
      (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m])
      (by simp only [arm64_norm, hx22_m]) (by simp only [arm64_norm, hx23_m])
      (by simp only [arm64_norm, hx24_m]) (by simp only [arm64_norm, hx25_m])
      (by simp only [arm64_norm, hx26_m])
      ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

theorem chunkedNoHeaderReceived_uc_tag1_varint_step_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 291) (decodeVarint2Spec A))
    {x : ChunkedNoHeaderReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {hdr : Option PolynomialDecoder} {uc : V1State.Unchunked.NoHeaderReceived}
    {rest : List (BitVec 8)} {outerLimit innerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_dv : decodeVarint rest = none →
      (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (v : BitVec 64) (rest' : List (BitVec 8)) (s' : State),
      decodeVarint rest = some (v, rest') →
      s'.pc = (blkPl_308).base + 408#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_308).rebase (blkPl_308).base H) (s0.readReg64 Reg.lr) s'
        (chunkedNoHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr hdr { uc with epoch := v } x.bs rest')
        (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_308).base + 520#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = 0#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_308).rebase (blkPl_308).base H) (s0.readReg64 Reg.lr) s
      (chunkedNoHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr hdr uc x.bs rest)
      (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hfpush := @chunkedNoHeaderReceived_uc_field_push_exit_placed _ A H hPushCall x R s0 { receivingHdr := hdr, uc := some uc }
  apply SepWPpLscro.of_sepWP (mid := lsmpl.base 291)
  conv => arg 4; rw [chunkedNoHeaderReceivedUcLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
    chunkedInlBelow_decodeVarint2 s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpLscro.call_frame (x := ⟨x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := entry + 532#64) hVarintCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
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
    apply SepWPpLscro.of_sepWP (mid := entry + 920#64)
    (conv => arg 4; simp only [decodeVarint2Spec, hdv, memRegion_48_cells1_160 s0.sp,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp])
    apply SepWP.exists_elim; intro v_stk0; apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
    have hcbnz_err : (sm.readReg64 (Reg.gpr 1#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm1
    apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (unchunked2CapAt_entails_chunkedNoHeaderReceivedPBAt A x.msgPtr rest.length hdr uc) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 1#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { receivingHdr := hdr, uc := some uc } x.bs)
      (by dsimp only [chunkedNoHeaderReceivedErrFrame]; sep_entail)
    exact hfpush hnone (by decide : 0 ≤ 1) hsm1 hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm, hspm])
      ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨v, rest'⟩
    have hrest'_le : rest'.length ≤ rest.length := Nat.le_of_lt (decodeVarint_length hdv)
    apply SepWPpLscro.of_sepWP (mid := entry + 408#64)
    (conv => arg 4; simp only [decodeVarint2Spec, hdv, unchunked2CapAt, sepConj_assoc, arm64_norm, hsp])
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
    apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (optAuthenticatorPBCapAt_mono A (x.msgPtr + 0x28#64) uc.auth hrest'_le) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPpLscro.weaken_pre (P' := chunkedNoHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr hdr { uc with epoch := v } x.bs rest')
      (by dsimp only [chunkedNoHeaderReceivedUcLoopPre, unchunked2CapAt]; simp only [arm64_norm]; sep_entail)
    exact hcont v rest' _ hdv
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
      (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m]) (by simp only [arm64_norm, hx25_m]) (by simp only [arm64_norm, hx26_m])
      ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

theorem chunkedNoHeaderReceived_uc_tag1_wt_err_step_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 261) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    {x : ChunkedNoHeaderReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {hdr : Option PolynomialDecoder} {uc : V1State.Unchunked.NoHeaderReceived}
    {rest : List (BitVec 8)} {iwt : WireType}
    (hiwt : iwt ≠ .varint) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone : (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hpc : s.pc = (blkPl_308).base + 520#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_308).rebase (blkPl_308).base H) (s0.readReg64 Reg.lr) s
      (chunkedNoHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr hdr uc x.bs rest)
      (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hcbnz_wt : (BitVec.ofNat 64 iwt.toNat == 0#64) = false := iwt_cbnz_true_of_ne_varint hiwt
  have hfpush := @chunkedNoHeaderReceived_uc_field_push_exit_placed _ A H hPushCall x R s0 { receivingHdr := hdr, uc := some uc }
  apply SepWPpLscro.of_sepWP (mid := lsmpl.base 261)
  conv => arg 4; rw [chunkedNoHeaderReceivedUcLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
    sliceCursorAt, chunkedInlBelow_decodeErrorHook s0.sp, memRegion_48_wtErr160 s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro b_wt1; apply SepWP.exists_elim; intro b_wt0; apply SepWP.exists_elim; intro v_wt0
  wp_steps
  apply SepWP.fold (wtErr160_entails_memRegion40 s0.sp _ _) (by sep_focus)
  apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
  apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
  apply SepWP.fold (unchunked2CapAt_entails_chunkedNoHeaderReceivedPBAt A x.msgPtr rest.length hdr uc) (by sep_focus)
  wp_reach
  refine SepWPpLscro.call_frame (x := (s0.sp - 128#64, 0x8000000000000006#64))
    (ret_pc := entry + 848#64) hFromCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorFromSpec]; simp only [arm64_norm, hsp]; rfl)
    (by decide : KindNoHeap 0x8000000000000006#64) (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, _, _, _, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx27, hx28, hvregs] at hpcm hspm hx27_m hx28_m hvregs_m
  apply SepWPpLscro.of_sepWP (mid := entry + 920#64)
  (conv => arg 4; simp only [decodeErrorFromSpec, memRegion_48_cells1_160 s0.sp,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp])
  apply SepWP.exists_elim; intro v_stk0; apply SepWP.pure_elim; rintro ⟨hsm0, htrm⟩
  apply SepWP.fold (chunkedInlBelow_decodeErrorHook_entails s0.sp) (by sep_focus)
  wp_steps; wp_reach
  apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { receivingHdr := hdr, uc := some uc } x.bs)
    (by dsimp only [chunkedNoHeaderReceivedErrFrame]; sep_entail)
  exact hfpush hnone (by decide : 0 ≤ 1) hsm0 hsp_align
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
    (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm, hspm])
    ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

theorem chunkedNoHeaderReceived_uc_auth_init_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    {x : ChunkedNoHeaderReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {hdr : Option PolynomialDecoder} {uc : V1State.Unchunked.NoHeaderReceived} {rest : List (BitVec 8)}
    (hcont : ∀ (s' : State),
      s'.pc = (blkPl_308).base + 500#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s.trace →
      s'.readReg64 (Reg.gpr 0#5) = s.readReg64 (Reg.gpr 0#5) →
      s'.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) →
      s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) →
      s'.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) →
      s'.readReg64 (Reg.gpr 23#5) = s.readReg64 (Reg.gpr 23#5) →
      s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      s'.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) →
      s'.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_308).rebase (blkPl_308).base H) (s0.readReg64 Reg.lr) s'
        (optPolynomialDecoderPBAt A x.msgPtr hdr ∗
          authenticatorPBCapAt A (x.msgPtr + 0x28#64) rest.length (uc.auth.getD default) ∗
          ((x.msgPtr + 0x58#64) ↦₆₄ uc.epoch) ∗
          stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
          memRegion (s0.sp - 128#64) 48 ∗
          chunkedInlSavedRegs10 s0.sp s0 ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool)
        (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_308).base + 476#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr) (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_308).rebase (blkPl_308).base H) (s0.readReg64 Reg.lr) s
      (chunkedNoHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr hdr uc x.bs rest)
      (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  rcases hauth : uc.auth with _ | auth
  · rw [hauth] at hcont; apply SepWPpLscro.of_sepWP (mid := entry + 500#64)
    conv => arg 4; rw [chunkedNoHeaderReceivedUcLoopPre, unchunked2CapAt, hauth, optAuthenticatorPBCapAt,
      memRegion_40_cells (x.msgPtr + 0x28#64)]
    simp only [noneCap, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm]
    apply SepWP.exists_elim; intro w1; apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
    apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5
    wp_steps
    have hdef := default_cells_entails_authenticatorPBCapAt A (x.msgPtr + 0x28#64) rest.length
    simp only [arm64_norm] at hdef; apply SepWP.fold hdef (by sep_focus); wp_reach
    apply SepWPpLscro.weaken_pre (P' := optPolynomialDecoderPBAt A x.msgPtr hdr ∗ authenticatorPBCapAt A (x.msgPtr + 0x28#64) rest.length (Option.getD none default) ∗ ((x.msgPtr + 0x58#64) ↦₆₄ uc.epoch) ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedInlSavedRegs10 s0.sp s0 ∗ (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool)
      (Entails.of_eq (by dsimp only [Option.getD]; ac_rfl))
    exact hcont _ (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
      (by try simp only [arm64_norm]) (by try simp only [arm64_norm]) (by try simp only [arm64_norm])
      (by simp only [arm64_norm, hx20]) (by try simp only [arm64_norm]) (by try simp only [arm64_norm])
      (by try simp only [arm64_norm]) (by simp only [arm64_norm, hx24]) (by try simp only [arm64_norm]) (by try simp only [arm64_norm])
      ⟨by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩
  · rw [hauth] at hcont; apply SepWPpLscro.of_sepWP (mid := entry + 500#64)
    conv => arg 4; rw [chunkedNoHeaderReceivedUcLoopPre, unchunked2CapAt, hauth, optAuthenticatorPBCapAt]
    simp only [sepConj_assoc, arm64_norm]
    have hcmn_in := authenticatorPBCapAt_entails_cmn A (x.msgPtr + 0x28#64) rest.length auth
    simp only [arm64_norm] at hcmn_in; apply SepWP.fold hcmn_in (by sep_focus)
    wp_simp_pre [sepExists_sepConj_left, sepConj_assoc, arm64_norm]
    apply SepWP.exists_elim; intro cap_ik; apply SepWP.exists_elim; intro ptr_ik
    apply SepWP.pure_elim; rintro ⟨hcap_lt, hcap_ik⟩
    have hcmn1 := cap_add_one_beq_zero_false hcap_lt; have hcmn2 := cap_add_one_bne_zero_true hcap_lt
    wp_steps
    have hcmn_out := cmn_entails_authenticatorPBCapAt A (x.msgPtr + 0x28#64) rest.length auth cap_ik ptr_ik hcap_ik
    simp only [arm64_norm] at hcmn_out; apply SepWP.fold hcmn_out (by sep_focus); wp_reach
    apply SepWPpLscro.weaken_pre (P' := optPolynomialDecoderPBAt A x.msgPtr hdr ∗ authenticatorPBCapAt A (x.msgPtr + 0x28#64) rest.length (Option.getD (some auth) default) ∗ ((x.msgPtr + 0x58#64) ↦₆₄ uc.epoch) ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedInlSavedRegs10 s0.sp s0 ∗ (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool)
      (Entails.of_eq (by dsimp only [Option.getD]; ac_rfl))
    exact hcont _ (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
      (by try simp only [arm64_norm]) (by try simp only [arm64_norm]) (by try simp only [arm64_norm])
      (by simp only [arm64_norm, hx20]) (by try simp only [arm64_norm]) (by try simp only [arm64_norm])
      (by try simp only [arm64_norm]) (by simp only [arm64_norm, hx24]) (by try simp only [arm64_norm]) (by try simp only [arm64_norm])
      ⟨by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩

theorem chunkedNoHeaderReceived_uc_tag2_step_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    (hAuthCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A)))
    {x : ChunkedNoHeaderReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {hdr : Option PolynomialDecoder} {uc : V1State.Unchunked.NoHeaderReceived}
    {rest : List (BitVec 8)} {iwt : WireType} {outerLimit innerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_auth : (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto iwt) (uc.auth.getD default) rest 97).toOption = none →
      (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (auth' : ProtoAuthenticator) (rest' : List (BitVec 8)) (s' : State),
      (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto iwt) (uc.auth.getD default) rest 97).toOption = some (auth', rest') →
      s'.pc = (blkPl_308).base + 408#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_308).rebase (blkPl_308).base H) (s0.readReg64 Reg.lr) s'
        (chunkedNoHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr hdr { uc with auth := some auth' } x.bs rest')
        (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_308).base + 476#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_308).rebase (blkPl_308).base H) (s0.readReg64 Reg.lr) s
      (chunkedNoHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr hdr uc x.bs rest)
      (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  have hfpush := fun {auth' : ProtoAuthenticator} => @chunkedNoHeaderReceived_uc_field_push_exit_placed _ A H hPushCall x R s0 { receivingHdr := hdr, uc := some { epoch := uc.epoch, auth := some auth' } }
  refine chunkedNoHeaderReceived_uc_auth_init_placed ?_ hpc hrun hsp hx20 hx24 hcs
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hcs1
  rw [htr] at htr1; rw [hx0] at hx0_1; rw [hx19] at hx19_1; rw [hx21] at hx21_1
  rw [hx22] at hx22_1; rw [hx23] at hx23_1; rw [hx25] at hx25_1; rw [hx26] at hx26_1
  obtain ⟨hx27_1, hx28_1, hvregs_1⟩ := hcs1
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  apply SepWPpLscro.of_sepWP (mid := lsmpl.base 295)
  conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, chunkedInlBelow_authMerge s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpLscro.call_frame_lscro (x := ⟨iwt, x.msgPtr + 0x28#64, uc.auth.getD default, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := entry + 512#64) hAuthCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
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
    apply SepWPpLscro.of_sepWP (mid := entry + 920#64)
    (conv => arg 4; simp only [authMergeSpec, hauth_res, memRegion_48_cells1_160 s0.sp,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp1])
    apply SepWP.exists_elim; intro v_stk0; apply SepWP.exists_elim; intro auth'; apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; intro hpure
    have htrm : sm.trace = _ := hpure.1; have hsm0 : sm.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hpure.2.1; have hn_err : n_err ≤ 1 := hpure.2.2
    have hcbz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (chunkedInlBelow_authMerge_entails s0.sp) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { receivingHdr := hdr, uc := some { epoch := uc.epoch, auth := some auth' } } x.bs)
      (by dsimp only [chunkedNoHeaderReceivedErrFrame, chunkedNoHeaderReceivedPBAt, optNoHeaderReceivedPBAt, noHeaderReceivedPBAt, unchunked2At, optAuthenticatorPBAt]; simp only [arm64_norm]; sep_entail)
    exact hfpush hnone hn_err hsm0 hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr1]) (by simp only [arm64_norm, hspm])
      ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨auth', rest'⟩
    have hrest'_le : rest'.length ≤ rest.length := (proto_mergeMessage_suffix hauth_res).1
    apply SepWPpLscro.of_sepWP (mid := entry + 408#64)
    (conv => arg 4; simp only [authMergeSpec, hauth_res, sepConj_assoc, arm64_norm, hsp1])
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    apply SepWP.fold (chunkedInlBelow_authMerge_entails s0.sp) (by sep_focus)
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPpLscro.weaken_pre (P' := chunkedNoHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr hdr { uc with auth := some auth' } x.bs rest')
      (by dsimp only [chunkedNoHeaderReceivedUcLoopPre, unchunked2CapAt, optAuthenticatorPBCapAt]; simp only [arm64_norm]; sep_entail)
    exact hcont auth' rest' _ hauth_res
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr1])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
      (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m]) (by simp only [arm64_norm, hx25_m]) (by simp only [arm64_norm, hx26_m])
      ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

theorem chunkedNoHeaderReceived_uc_loop_le_exit_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 261) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    {x : ChunkedNoHeaderReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {hdr : Option PolynomialDecoder} {uc : V1State.Unchunked.NoHeaderReceived}
    {cur : List (BitVec 8)} {outerLimit innerLimit : Nat}
    (hle_lim : cur.length ≤ innerLimit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_suf : IsDropSuffix x.bs cur) (hlim_lt : innerLimit < 2 ^ 63)
    (hnone_of_lt : cur.length < innerLimit →
      (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (s' : State),
      cur.length = innerLimit →
      s'.pc = (blkPl_308).base + 168#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_308).rebase (blkPl_308).base H) (s0.readReg64 Reg.lr) s'
        (chunkedNoHeaderReceivedLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { receivingHdr := hdr, uc := some uc } x.bs cur)
        (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_308).base + 408#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_308).rebase (blkPl_308).base H) (s0.readReg64 Reg.lr) s
      (chunkedNoHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr hdr uc x.bs cur)
      (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  by_cases heq_lim : cur.length = innerLimit
  · obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq heq_lim
    apply SepWPpLscro.of_sepWP (mid := entry + 168#64)
    conv => arg 4; rw [chunkedNoHeaderReceivedUcLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt]
    simp only [sepConj_assoc]; wp_steps
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    wp_reach
    apply SepWPpLscro.weaken_pre (P' := chunkedNoHeaderReceivedLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { receivingHdr := hdr, uc := some uc } x.bs cur)
      (by dsimp only [chunkedNoHeaderReceivedLoopPre, chunkedNoHeaderReceivedPBCapAt, optNoHeaderReceivedPBCapAt, unchunked2CapAt, sliceCursorAfter]; sep_entail)
    exact hcont _ heq_lim
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr])
      (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20]) (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22])
      (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24]) (by simp only [arm64_norm, hx25])
      ⟨by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩
  · have hlt_lim : cur.length < innerLimit := Nat.lt_of_le_of_ne hle_lim heq_lim
    obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_lt hlt_lim hlim_lt
    have hnone := hnone_of_lt hlt_lim
    have hfrom_push := @chunkedNoHeaderReceived_uc_from_push_exit_placed _ A H hFromCall hPushCall x R s0 { receivingHdr := hdr, uc := some uc }
    apply SepWPpLscro.of_sepWP (mid := entry + 684#64)
    conv => arg 4; rw [chunkedNoHeaderReceivedUcLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
      sliceCursorAt, memRegion_48_cells1_160 s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v_stk0; wp_steps
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot curPtr (BitVec.ofNat 64 cur.length)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    apply SepWP.fold (unchunked2CapAt_entails_chunkedNoHeaderReceivedPBAt A x.msgPtr cur.length hdr uc) (by sep_focus)
    wp_reach
    apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000008#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { receivingHdr := hdr, uc := some uc } x.bs)
      (by dsimp only [chunkedNoHeaderReceivedErrFrame]; sep_entail)
    exact hfrom_push hnone (by decide : KindNoHeap 0x8000000000000008#64) hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr])
      ⟨by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩

theorem chunkedNoHeaderReceived_uc_decode_key_step_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 261) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 291) (decodeVarint2Spec A))
    {x : ChunkedNoHeaderReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {hdr : Option PolynomialDecoder} {uc : V1State.Unchunked.NoHeaderReceived}
    {cur : List (BitVec 8)} {outerLimit innerLimit : Nat}
    (hgt_lim : ¬ cur.length ≤ innerLimit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_lt : cur.length < 2 ^ 63) (hcur_suf : IsDropSuffix x.bs cur)
    (hnone_of_uc_none :
      mergeLoopBin V1State.Unchunked.NoHeaderReceived.mergeField (cur.length - innerLimit) uc cur innerLimit 97 = none →
      (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (key : BitVec 64) (iwt : WireType) (rest : List (BitVec 8)) (s' : State),
      decodeVarint cur = some (key, rest) → ¬ 2 ^ 32 ≤ key.toNat →
      WireType.ofNat? (key.toNat % 8) = some iwt → ¬ key.toNat / 8 < 1 →
      s'.pc = (blkPl_308).base + 460#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_308).rebase (blkPl_308).base H) (s0.readReg64 Reg.lr) s'
        (chunkedNoHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr hdr uc x.bs rest)
        (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_308).base + 408#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_308).rebase (blkPl_308).base H) (s0.readReg64 Reg.lr) s
      (chunkedNoHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr hdr uc x.bs cur)
      (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  have hpush_exit := @chunkedNoHeaderReceived_uc_push_exit_placed _ A H hPushCall x R s0 { receivingHdr := hdr, uc := some uc }
  have hfrom_push := @chunkedNoHeaderReceived_uc_from_push_exit_placed _ A H hFromCall hPushCall x R s0 { receivingHdr := hdr, uc := some uc }
  apply SepWPpLscro.of_sepWP (mid := lsmpl.base 291)
  conv => arg 4; rw [chunkedNoHeaderReceivedUcLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
    sliceCursorAt, chunkedInlBelow_decodeVarint2 s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpLscro.call_frame (x := ⟨x.bufRef, x.slot, curPtr, cur⟩)
    (ret_pc := entry + 428#64) hVarintCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, hsp, hx19]; rfl)
    hcur_lt (by dsimp only [sliceCursorAt, curPtr]; sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
  cases hd : decodeVarint cur with
  | none =>
    have hnone := hnone_of_uc_none (mergeLoopBin_of_decodeVarint_none protoPrefixStep_unchunked_noHeaderReceived_mergeField hgt_lim hd)
    apply SepWPpLscro.of_sepWP (mid := entry + 696#64)
    (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
    apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    apply SepWP.fold (unchunked2CapAt_entails_chunkedNoHeaderReceivedPBAt A x.msgPtr cur.length hdr uc) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPpLscro.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { receivingHdr := hdr, uc := some uc } x.bs)
      (by dsimp only [chunkedNoHeaderReceivedErrFrame]; sep_entail)
    exact hpush_exit hnone (by decide : 0 ≤ 2) hsm1 hsp_align
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
    · have hnone := hnone_of_uc_none (mergeLoopBin_of_key_ge protoPrefixStep_unchunked_noHeaderReceived_mergeField hgt_lim hd hk_ge)
      have hshr := key_shr32_of_ge hk_ge
      apply SepWPpLscro.of_sepWP (mid := entry + 684#64)
      (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
      apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
      apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
      apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
      apply SepWP.fold (unchunked2CapAt_entails_chunkedNoHeaderReceivedPBAt A x.msgPtr cur.length hdr uc) (by sep_focus)
      conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_cells2_160 s0.sp]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply SepWP.exists_elim; intro v_err0; apply SepWP.exists_elim; intro v_err1; wp_steps
      apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
      apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
      have h40 : ((s0.sp - 128#64 + 8#64) ↦₆₄ key) ∗ memRegion (s0.sp - 112#64) 32 ⊢ memRegion (s0.sp - 120#64) 40 := by
        rw [bv_sub_add_lit s0.sp 128 8]; exact cells2_memRegion32_entails_40_160 s0.sp key
      apply SepWP.fold h40 (by sep_focus); wp_reach
      apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000004#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { receivingHdr := hdr, uc := some uc } x.bs)
        (by dsimp only [chunkedNoHeaderReceivedErrFrame]; sep_entail)
      exact hfrom_push hnone (by decide : KindNoHeap 0x8000000000000004#64) hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
        ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
    · have hshr := key_shr32_of_lt hk_ge
      cases hwt : WireType.ofNat? (key.toNat % 8) with
      | none =>
        have hnone := hnone_of_uc_none (mergeLoopBin_of_wt_none protoPrefixStep_unchunked_noHeaderReceived_mergeField hgt_lim hd hk_ge hwt)
        obtain ⟨hcs1, hcs2⟩ := key_wt_none hwt
        apply SepWPpLscro.of_sepWP (mid := entry + 684#64)
        (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
        apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
        apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
        apply SepWP.fold (unchunked2CapAt_entails_chunkedNoHeaderReceivedPBAt A x.msgPtr cur.length hdr uc) (by sep_focus)
        conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_cells2_160 s0.sp]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        apply SepWP.exists_elim; intro v_err0; apply SepWP.exists_elim; intro v_err1; wp_steps
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        have h40 : ((s0.sp - 128#64 + 8#64) ↦₆₄ (key &&& 7#64)) ∗ memRegion (s0.sp - 112#64) 32 ⊢ memRegion (s0.sp - 120#64) 40 := by
          rw [bv_sub_add_lit s0.sp 128 8]; exact cells2_memRegion32_entails_40_160 s0.sp (key &&& 7#64)
        apply SepWP.fold h40 (by sep_focus); wp_reach
        apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000003#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { receivingHdr := hdr, uc := some uc } x.bs)
          (by dsimp only [chunkedNoHeaderReceivedErrFrame]; sep_entail)
        exact hfrom_push hnone (by decide : KindNoHeap 0x8000000000000003#64) hsp_align
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
          ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
      | some iwt =>
        obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
        obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_ge; obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
        by_cases hitag0 : key.toNat / 8 < 1
        · have hnone := hnone_of_uc_none (mergeLoopBin_of_tag_zero protoPrefixStep_unchunked_noHeaderReceived_mergeField hgt_lim hd hk_ge hwt hitag0)
          have htag_zero : key.toNat / 8 = 0 := by omega
          apply SepWPpLscro.of_sepWP (mid := entry + 684#64)
          (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
          apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
          apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          apply SepWP.fold (unchunked2CapAt_entails_chunkedNoHeaderReceivedPBAt A x.msgPtr cur.length hdr uc) (by sep_focus)
          conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_cells1_160 s0.sp]
          simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
          apply SepWP.exists_elim; intro v_err0; wp_steps
          apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
          apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus); wp_reach
          apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000005#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedNoHeaderReceivedErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { receivingHdr := hdr, uc := some uc } x.bs)
            (by dsimp only [chunkedNoHeaderReceivedErrFrame]; sep_entail)
          exact hfrom_push hnone (by decide : KindNoHeap 0x8000000000000005#64) hsp_align
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
            ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
        · obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_ge hitag0
          have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
            rw [beq_eq_false_iff_ne]; intro h; have h1 := congrArg BitVec.toNat h
            simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1; omega
          apply SepWPpLscro.of_sepWP (mid := entry + 460#64)
          (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
          apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
          apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          apply SepWP.fold (unchunked2CapAt_mono A (x.msgPtr + 0x28#64) uc.epoch uc.auth hrest_le_cur) (by sep_focus)
          wp_steps; wp_reach
          apply SepWPpLscro.weaken_pre (P' := chunkedNoHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr hdr uc x.bs rest)
            (by dsimp only [chunkedNoHeaderReceivedUcLoopPre]; sep_entail)
          exact hcont key iwt rest _ hd hk_ge hwt hitag0
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
            (by simp only [arm64_norm, hsm1, hand_wt]) (by simp only [arm64_norm, hsm1, hw1, hw1_2, hw1_zext1, hw1_zext2])
            (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
            (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m]) (by simp only [arm64_norm, hx25_m]) (by simp only [arm64_norm, hx26_m])
            ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

theorem chunkedNoHeaderReceived_uc_loop_ok_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 261) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 291) (decodeVarint2Spec A))
    (hSkipCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 263) (skipField3Spec A))
    (hAuthCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A)))
    {x : ChunkedNoHeaderReceivedMergeGhost} {R : SepProp} {s0 : State} {hdr : Option PolynomialDecoder} {outerLimit innerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hbs_lt : x.bs.length < 2 ^ 63) (hlim_lt : innerLimit < 2 ^ 63) :
    ∀ (n : Nat) (uc : V1State.Unchunked.NoHeaderReceived) (cur : List (BitVec 8)) (s : State),
      cur.length ≤ n → cur.length ≤ x.bs.length → IsDropSuffix x.bs cur →
      (∀ (uc' : V1State.Unchunked.NoHeaderReceived) (rest' : List (BitVec 8)) (s' : State),
        rest'.length = innerLimit → rest'.length ≤ x.bs.length → IsDropSuffix x.bs rest' →
        mergeLoopBin V1State.Unchunked.NoHeaderReceived.mergeField (cur.length - innerLimit) uc cur innerLimit 97 = some uc' →
        s'.pc = (blkPl_308).base + 168#64 →
        s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
        s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
        s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
        s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 24#5) = 1#64 →
        s'.readReg64 (Reg.gpr 25#5) = 8#64 → ChunkedInl10CalleeSaved s0 s' →
        SepWPpLscro lsmpl ((blkPC_308).rebase (blkPl_308).base H) (s0.readReg64 Reg.lr) s'
          (chunkedNoHeaderReceivedLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { receivingHdr := hdr, uc := some uc' } x.bs rest')
          (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0)) →
      (mergeLoopBin V1State.Unchunked.NoHeaderReceived.mergeField (cur.length - innerLimit) uc cur innerLimit 97 = none →
        (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none) →
      s.pc = (blkPl_308).base + 408#64 →
      s.status = .Running → s.sp = s0.sp - 128#64 → s.trace = s0.trace →
      s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s.readReg64 (Reg.gpr 24#5) = 1#64 →
      s.readReg64 (Reg.gpr 25#5) = 8#64 → s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s →
      SepWPpLscro lsmpl ((blkPC_308).rebase (blkPl_308).base H) (s0.readReg64 Reg.lr) s
        (chunkedNoHeaderReceivedUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr hdr uc x.bs cur)
        (WppPost (chunkedNoHeaderReceivedMergeSpec A) x R s0) (WppPanic R s0) := by
  have htag1_varint := fun {s uc rest} => @chunkedNoHeaderReceived_uc_tag1_varint_step_placed _ A H hPushCall hVarintCall x R s0 s hdr uc rest outerLimit innerLimit
  have htag1_wt_err := fun {s uc rest iwt} => @chunkedNoHeaderReceived_uc_tag1_wt_err_step_placed _ A H hFromCall hPushCall x R s0 s hdr uc rest iwt
  have htag2_step := fun {s uc rest} (iwt : WireType) => @chunkedNoHeaderReceived_uc_tag2_step_placed _ A H hPushCall hAuthCall x R s0 s hdr uc rest iwt outerLimit innerLimit
  have hskip_step := fun {s uc rest} (iwt : WireType) (tag : Nat) => @chunkedNoHeaderReceived_uc_skip_step_placed _ A H hPushCall hSkipCall x R s0 s hdr uc rest iwt tag outerLimit innerLimit
  intro n; induction n with
  | zero =>
    intro uc cur s hcur_n hcur_le hcur_suf hok_cont hnone_cont hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
    exact chunkedNoHeaderReceived_uc_loop_le_exit_placed hFromCall hPushCall (by omega) hsp_align hcur_le hcur_suf hlim_lt
      (fun hlt => hnone_cont (mergeLoopBin_lt_limit _ _ _ _ _ _ hlt))
      (fun s' heq => hok_cont uc cur s' heq hcur_le hcur_suf (mergeLoopBin_eq_limit _ _ _ _ _ _ heq))
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
  | succ n ih =>
    intro uc cur s hcur_n hcur_le hcur_suf hok_cont hnone_cont hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
    by_cases hle_lim : cur.length ≤ innerLimit
    · exact chunkedNoHeaderReceived_uc_loop_le_exit_placed hFromCall hPushCall hle_lim hsp_align hcur_le hcur_suf hlim_lt
        (fun hlt => hnone_cont (mergeLoopBin_lt_limit _ _ _ _ _ _ hlt))
        (fun s' heq => hok_cont uc cur s' heq hcur_le hcur_suf (mergeLoopBin_eq_limit _ _ _ _ _ _ heq))
        hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
    · have hcur_lt : cur.length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
      refine chunkedNoHeaderReceived_uc_decode_key_step_placed hFromCall hPushCall hVarintCall hle_lim hsp_align
        hcur_le hcur_lt hcur_suf hnone_cont ?_ hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
      intro key iwt rest s' hd hk_ge hwt hitag0 hpc' hrun' hsp' htr' hx0' hx1' hx19' hx20' hx21' hx22' hx23' hx24' hx25' hx26' hcs'
      obtain ⟨hx27', hx28', hvregs'⟩ := hcs'
      have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd; have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
      have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le; have hrest_lt : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest_le hbs_lt
      have hrest_suf : IsDropSuffix x.bs rest := suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
      have htag_lt : key.toNat / 8 < 2 ^ 32 := by omega
      have hstep := mergeLoopBin_of_key_ok (m := uc) (depth' := 97)
        protoPrefixStep_unchunked_noHeaderReceived_mergeField hle_lim hd hk_ge hwt hitag0
      by_cases htag1 : key.toNat / 8 = 1
      · rw [htag1] at hx1' hstep; rw [unchunkedNoHeaderReceived_mergeField_tag1] at hstep
        by_cases hiwt : iwt = .varint
        · subst hiwt; apply SepWPpLscro.of_sepWP (mid := entry + 520#64); wp_steps; wp_reach
          refine htag1_varint hsp_align hrest_le hrest_lt hrest_suf
            (fun hdv => hnone_cont (by simp [hstep, hdv]))
            (fun v rest' s'' hdv hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs'' => ?_)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
            (by simp only [arm64_norm, hx0', WireType.toNat])
            (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20']) (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22'])
            (by simp only [arm64_norm, hx23']) (by simp only [arm64_norm, hx24']) (by simp only [arm64_norm, hx25']) (by simp only [arm64_norm, hx26'])
            ⟨by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩
          have hr'_lt : rest'.length < rest.length := decodeVarint_length hdv; have hr'_le : rest'.length ≤ rest.length := Nat.le_of_lt hr'_lt
          have hstep1 : mergeLoopBin V1State.Unchunked.NoHeaderReceived.mergeField (cur.length - innerLimit) uc cur innerLimit 97 =
              mergeLoopBin V1State.Unchunked.NoHeaderReceived.mergeField (rest'.length - innerLimit) { uc with epoch := v } rest' innerLimit 97 := by simp [hstep, hdv]
          exact ih { uc with epoch := v } rest' s'' (by omega) (Nat.le_trans hr'_le hrest_le)
            (suffix_trans hrest_le hrest_suf hr'_le (decodeVarint_suffix hdv))
            (fun uc' r'' s3 heq hr''_le hr''_suf hml => hok_cont uc' r'' s3 heq hr''_le hr''_suf (hstep1.trans hml))
            (fun hml => hnone_cont (hstep1.trans hml))
            hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs''
        · apply SepWPpLscro.of_sepWP (mid := entry + 520#64); wp_steps; wp_reach
          exact htag1_wt_err hiwt hsp_align hrest_le hrest_suf (hnone_cont (by simp [hstep, hiwt]))
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
            (by simp only [arm64_norm, hx0']) ⟨by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩
      · by_cases htag2 : key.toNat / 8 = 2
        · rw [htag2] at hx1' hstep; rw [unchunkedNoHeaderReceived_mergeField_tag2] at hstep
          apply SepWPpLscro.of_sepWP (mid := entry + 476#64); wp_steps; wp_reach
          refine htag2_step iwt hsp_align hrest_le hrest_lt hrest_suf
            (fun hauth => hnone_cont (by simp [hstep, hauth]))
            (fun auth' rest' s'' hauth hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs'' => ?_)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
            (by simp only [arm64_norm, hx0'])
            (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20']) (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22'])
            (by simp only [arm64_norm, hx23']) (by simp only [arm64_norm, hx24']) (by simp only [arm64_norm, hx25']) (by simp only [arm64_norm, hx26'])
            ⟨by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩
          have hr'_le : rest'.length ≤ rest.length := (proto_mergeMessage_suffix hauth).1
          have hstep2 : mergeLoopBin V1State.Unchunked.NoHeaderReceived.mergeField (cur.length - innerLimit) uc cur innerLimit 97 =
              mergeLoopBin V1State.Unchunked.NoHeaderReceived.mergeField (rest'.length - innerLimit) { uc with auth := some auth' } rest' innerLimit 97 := by simp [hstep, hauth]
          exact ih { uc with auth := some auth' } rest' s'' (by omega) (Nat.le_trans hr'_le hrest_le)
            (suffix_trans hrest_le hrest_suf hr'_le (proto_mergeMessage_suffix hauth).2)
            (fun uc' r'' s3 heq hr''_le hr''_suf hml => hok_cont uc' r'' s3 heq hr''_le hr''_suf (hstep2.trans hml))
            (fun hml => hnone_cont (hstep2.trans hml))
            hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs''
        · obtain ⟨hb1_1, _⟩ := itag_beq_tag_false htag1 htag_lt (by decide : 1 < 2 ^ 32)
          obtain ⟨hb2_1, _⟩ := itag_beq_tag_false htag2 htag_lt (by decide : 2 < 2 ^ 32)
          have hb1_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 1#32) = false := by rw [sf_truncate32_ofNat64]; exact hb1_1
          have hb2_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 2#32) = false := by rw [sf_truncate32_ofNat64]; exact hb2_1
          have hb2_bne1 : (BitVec.ofNat 32 (key.toNat / 8) != 2#32) = true := by simp only [bne, hb2_1, Bool.not_false]
          have hb2_bne2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) != 2#32) = true := by simp only [bne, hb2_2, Bool.not_false]
          rw [unchunkedNoHeaderReceived_mergeField_other uc iwt rest 97 htag_lt htag1 htag2] at hstep
          apply SepWPpLscro.of_sepWP (mid := entry + 388#64); wp_steps; wp_reach
          refine hskip_step iwt (key.toNat / 8) hsp_align hrest_le hrest_lt hrest_suf htag_lt
            (fun hsf => hnone_cont (by simp [hstep, hsf]))
            (fun rest' s'' hsf hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs'' => ?_)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
            (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx1', sf_truncate32_ofNat64])
            (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20']) (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22'])
            (by simp only [arm64_norm, hx23']) (by simp only [arm64_norm, hx24']) (by simp only [arm64_norm, hx25']) (by simp only [arm64_norm, hx26'])
            ⟨by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩
          have hr'_le : rest'.length ≤ rest.length := (skip_length (2 * rest.length + 2)).1 _ _ _ _ _ hsf
          have hstep_other : mergeLoopBin V1State.Unchunked.NoHeaderReceived.mergeField (cur.length - innerLimit) uc cur innerLimit 97 =
              mergeLoopBin V1State.Unchunked.NoHeaderReceived.mergeField (rest'.length - innerLimit) uc rest' innerLimit 97 := by simp [hstep, hsf]
          exact ih uc rest' s'' (by omega) (Nat.le_trans hr'_le hrest_le)
            (suffix_trans hrest_le hrest_suf hr'_le ((skip_suffix (2 * rest.length + 2)).1 _ _ _ _ _ hsf))
            (fun uc' r'' s3 heq hr''_le hr''_suf hml => hok_cont uc' r'' s3 heq hr''_le hr''_suf (hstep_other.trans hml))
            (fun hml => hnone_cont (hstep_other.trans hml))
            hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs''

end CryptoVerification.SpqrV1.Prost.MessageMerge

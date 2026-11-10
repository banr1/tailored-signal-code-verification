/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.SignedDeps
public import LibsignalBinary.Proofs.RecordCodecs.RecordCodecsCodeSymD
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoop
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.RecordCodecs.Deps

/-!
# `SignedPreKeyRecordStructure::decode` Offsets, Stack Layout, and Loop State

Control-flow cut offsets, relative-offset and `[LibsignalPlacement]` (Block `562`) callee bundles,
`spkActualDecode`, stack-allocated 88-byte `SignedPreKeyRecordStructure` (`sp' + 16`), and
loop/convergence state invariants (`+656`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.RecordCodecs
open CryptoVerification.RecordCodecsBinary

abbrev spkDecOff : Nat :=
  num% (ls_off% "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>")

theorem spkDec_fnOff :
    libsignalSessionCode.fnOff signedDecodeName = spkDecOff :=
  ls_lemma% fnOff "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>"

gen_decodes CryptoVerification.libsignalSessionCode_tree spkDec
  [(num% (ls_off% "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>")) →
   (num% (ls_off% "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>" + 824))]

/-! ## Function-relative control-flow cut offsets -/

@[arm64_norm] def spkOff_tag3 : BitVec 64 := 76#64
@[arm64_norm] def spkOff_tag3Ret : BitVec 64 := 88#64
@[arm64_norm] def spkOff_latch : BitVec 64 := 92#64
@[arm64_norm] def spkOff_key : BitVec 64 := 104#64
@[arm64_norm] def spkOff_keyRet : BitVec 64 := 112#64
@[arm64_norm] def spkOff_dispatch : BitVec 64 := 144#64
@[arm64_norm] def spkOff_tag5 : BitVec 64 := 176#64
@[arm64_norm] def spkOff_le2 : BitVec 64 := 220#64
@[arm64_norm] def spkOff_tag2 : BitVec 64 := 236#64
@[arm64_norm] def spkOff_tag2Ret : BitVec 64 := 248#64
@[arm64_norm] def spkOff_tag4 : BitVec 64 := 256#64
@[arm64_norm] def spkOff_tag4Ret : BitVec 64 := 268#64
@[arm64_norm] def spkOff_tag1 : BitVec 64 := 276#64
@[arm64_norm] def spkOff_tag1Ret : BitVec 64 := 288#64
@[arm64_norm] def spkOff_skip : BitVec 64 := 300#64
@[arm64_norm] def spkOff_skipRet : BitVec 64 := 312#64
@[arm64_norm] def spkOff_tag1Ok : BitVec 64 := 320#64
@[arm64_norm] def spkOff_fromCommon : BitVec 64 := 372#64
@[arm64_norm] def spkOff_fromRet : BitVec 64 := 384#64
@[arm64_norm] def spkOff_okEmpty : BitVec 64 := 392#64
@[arm64_norm] def spkOff_pushTag4 : BitVec 64 := 400#64
@[arm64_norm] def spkOff_pushTag2 : BitVec 64 := 424#64
@[arm64_norm] def spkOff_tag1BadWt : BitVec 64 := 460#64
@[arm64_norm] def spkOff_tag1FromRet : BitVec 64 := 488#64
@[arm64_norm] def spkOff_pushTag1 : BitVec 64 := 492#64
@[arm64_norm] def spkOff_pushTag3 : BitVec 64 := 528#64
@[arm64_norm] def spkOff_tag5BadWt : BitVec 64 := 564#64
@[arm64_norm] def spkOff_skipErr : BitVec 64 := 592#64
@[arm64_norm] def spkOff_tag5Eof : BitVec 64 := 600#64
@[arm64_norm] def spkOff_tag5FromCommon : BitVec 64 := 608#64
@[arm64_norm] def spkOff_tag5FromRet : BitVec 64 := 616#64
@[arm64_norm] def spkOff_pushCall : BitVec 64 := 648#64
@[arm64_norm] def spkOff_pushRet : BitVec 64 := 652#64
@[arm64_norm] def spkOff_converge : BitVec 64 := 656#64
@[arm64_norm] def spkOff_freePub : BitVec 64 := 680#64
@[arm64_norm] def spkOff_freePubRet : BitVec 64 := 696#64
@[arm64_norm] def spkOff_freePrivRet : BitVec 64 := 716#64
@[arm64_norm] def spkOff_freeSigRet : BitVec 64 := 736#64
@[arm64_norm] def spkOff_okCopy : BitVec 64 := 760#64
@[arm64_norm] def spkOff_retOk : BitVec 64 := 800#64

/-! ## Callee contracts at symbol-relative offsets from `signedDecodeName` -/

theorem spk_decodeVarint6_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (d : SignedPortDeps img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName +
        bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#5]") -
          ls_off% "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>"))
      ((SpqrV1.Varint.decodeVarint2Spec A).inImage img) := by
  have heq :
      (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName +
        bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#5]") -
          ls_off% "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>") =
      (tripleRatchetProgAtExt img.base ext).fnAddr decodeVarint6Name := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>"),
      (ls_lemma% fnOff "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#5]")]
    bv_omega
  rw [heq]
  exact subroutine_ok_inImage_of_subroutine_ok img d.decodeVarint6

theorem spk_skipField7_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (d : SignedPortDeps img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName +
        bv% (2 ^ 64 + (ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#6]") -
          ls_off% "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>"))
      ((SpqrV1.Varint.skipField3Spec A).inImage img) := by
  have heq :
      (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName +
        bv% (2 ^ 64 + (ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#6]") -
          ls_off% "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>") =
      (tripleRatchetProgAtExt img.base ext).fnAddr skipField7Name := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>"),
      (ls_lemma% fnOff "prost::encoding::skip_field::<&mut &[u8]> [local#6]")]
    bv_omega
  rw [heq]
  exact subroutine_ok_inImage_of_subroutine_ok img d.skipField7

theorem spk_bytesMerge7_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (d : SignedPortDeps img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName +
        bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#6]") -
          ls_off% "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>"))
      ((SpqrV1.Prost.BytesMerge.bytesMerge3RawSpec A).inImage img) := by
  have heq :
      (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName +
        bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#6]") -
          ls_off% "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>") =
      (tripleRatchetProgAtExt img.base ext).fnAddr bytesMerge7Name := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>"),
      (ls_lemma% fnOff "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#6]")]
    bv_omega
  rw [heq]
  exact d.bytesMerge7

theorem spk_decodeErrorFrom_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hH : SignedHooks img.base A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName +
        bv% (2 ^ 64 + (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from") -
          ls_off% "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>"))
      ((decodeErrorFromSpec A).inImage img) := by
  have heq :
      (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName +
        bv% (2 ^ 64 + (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from") -
          ls_off% "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>") =
      (tripleRatchetProgAtExt img.base ext).fnAddr decodeErrorFromName := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>"),
      (ls_lemma% fnOff "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from")]
    bv_omega
  rw [heq]
  exact subroutine_ok_inImage_of_subroutine_ok img hH.decodeErrorFrom

theorem spk_decodeErrorPush_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hH : SignedHooks img.base A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName +
        bv% (2 ^ 64 + (ls_off% "<prost::error::DecodeError>::push") -
          ls_off% "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>"))
      ((decodeErrorPushSpec A).inImage img) := by
  have heq :
      (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName +
        bv% (2 ^ 64 + (ls_off% "<prost::error::DecodeError>::push") -
          ls_off% "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>") =
      (tripleRatchetProgAtExt img.base ext).fnAddr decodeErrorPushName := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>"),
      (ls_lemma% fnOff "<prost::error::DecodeError>::push")]
    bv_omega
  rw [heq]
  exact subroutine_ok_inImage_of_subroutine_ok img hH.decodeErrorPush

theorem spk_dealloc_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hH : SignedHooks img.base A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName +
        bv% (ls_off% "__rustc::__rust_dealloc" -
          ls_off% "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>"))
      ((rustDeallocSpec A).inImage img) :=
  subroutine_ok_inImage_of_subroutine_ok img
    (sub_ok_at_of_fnAddr hH.alloc.dealloc signedDecodeName
      (num% (ls_off% "__rustc::__rust_dealloc" -
        ls_off% "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>")))

/-! ## Pure codec & little-endian fixed64 helpers -/

/-- Actual behavior of the compiled `SignedPreKeyRecordStructure::decode::<&[u8]>` binary:
because LLVM IPSCCP proved `bytes.len() > 0` across all CLI callers, the prologue at `+0x048`
branches unconditionally to `decode_varint` (`+0x068`), rejecting `[]` with `Err(UnexpectedEof)`
while matching `SignedPreKeyRecordStructure.decode` on every non-empty slice. -/
def spkActualDecode (bs : List (BitVec 8)) : Option SignedPreKeyRecordStructure :=
  match bs with
  | [] => none
  | _ :: _ => SignedPreKeyRecordStructure.decode bs

theorem spkActualDecode_of_nonempty {bs : List (BitVec 8)} (hne : bs ≠ []) :
    spkActualDecode bs = SignedPreKeyRecordStructure.decode bs := by
  cases bs with
  | nil => exact (hne rfl).elim
  | cons _ _ => rfl

private theorem bv64_concat8 (b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ : BitVec 8) :
    b₇ ++ b₆ ++ b₅ ++ b₄ ++ b₃ ++ b₂ ++ b₁ ++ b₀ =
      b₀.setWidth 64 + 256#64 * b₁.setWidth 64 + 65536#64 * b₂.setWidth 64 +
        16777216#64 * b₃.setWidth 64 + 4294967296#64 * b₄.setWidth 64 +
        1099511627776#64 * b₅.setWidth 64 + 281474976710656#64 * b₆.setWidth 64 +
        72057594037927936#64 * b₇.setWidth 64 := by
  bv_kernel

theorem le64_eq_concat (b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ : BitVec 8) :
    b₇ ++ b₆ ++ b₅ ++ b₄ ++ b₃ ++ b₂ ++ b₁ ++ b₀ =
      le64 b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ := by
  rw [bv64_concat8]
  unfold le64
  bv_omega

theorem mergeFixed64_suffix {wt : WireType} {bs rest : List (BitVec 8)} {v : BitVec 64}
    (h : mergeFixed64 wt bs = some (v, rest)) :
    ∃ k, k ≤ bs.length ∧ rest = bs.drop k := by
  unfold mergeFixed64 at h
  split at h
  · simp at h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨_, rfl⟩
      exact ⟨8, by simp, rfl⟩
    · simp at h

theorem spkMergeField_suffix {m m' : SignedPreKeyRecordStructure} {tag : ℕ} {wt : WireType}
    {bs rest : List (BitVec 8)}
    (h : SignedPreKeyRecordStructure.mergeField m tag wt bs = some (m', rest)) :
    ∃ k, k ≤ bs.length ∧ rest = bs.drop k := by
  unfold SignedPreKeyRecordStructure.mergeField skipUnknown at h
  rcases tag with _ | _ | _ | _ | _ | _ | tag6 <;>
    simp only [Option.map_eq_some_iff] at h
  · rcases h with ⟨r, hs, _, rfl⟩; exact skipField_suffix hs
  · rcases h with ⟨⟨v, r⟩, hm, _, rfl⟩; exact mergeUint32_suffix hm
  · rcases h with ⟨⟨v, r⟩, hm, _, rfl⟩; obtain ⟨k, hkl, hr, _⟩ := mergeBytes_suffix hm; exact ⟨k, hkl, hr⟩
  · rcases h with ⟨⟨v, r⟩, hm, _, rfl⟩; obtain ⟨k, hkl, hr, _⟩ := mergeBytes_suffix hm; exact ⟨k, hkl, hr⟩
  · rcases h with ⟨⟨v, r⟩, hm, _, rfl⟩; obtain ⟨k, hkl, hr, _⟩ := mergeBytes_suffix hm; exact ⟨k, hkl, hr⟩
  · rcases h with ⟨⟨v, r⟩, hm, _, rfl⟩; exact mergeFixed64_suffix hm
  · rcases h with ⟨r, hs, _, rfl⟩; exact skipField_suffix hs

/-! ## Stack-allocated `SignedPreKeyRecordStructure` at `sp' + 16` (`88` bytes) -/

structure SpkGhost where
  pub : VecPin
  priv : VecPin
  sig : VecPin

structure SpkGhostCapOk (g : SpkGhost) (n : ℕ) : Prop where
  pub : BytesMergeCapOk g.pub.cap n
  priv : BytesMergeCapOk g.priv.cap n
  sig : BytesMergeCapOk g.sig.cap n

theorem SpkGhostCapOk.mono {g : SpkGhost} {m n : ℕ}
    (hg : SpkGhostCapOk g n) (hle : m ≤ n) :
    SpkGhostCapOk g m :=
  ⟨bytesMergeCapOk_mono hg.pub hle,
   bytesMergeCapOk_mono hg.priv hle,
   bytesMergeCapOk_mono hg.sig hle⟩

/-- Concrete pin version of `signedPreKeyStructAt` at `sp' + 16`. -/
def spkStructAt (A : RustAlloc) (g : SpkGhost) (sp' : BitVec 64)
    (m : SignedPreKeyRecordStructure) : SepProp :=
  vecU8At A (sp' + 16#64) g.pub.cap g.pub.ptr m.publicKey ∗
    vecU8At A (sp' + 40#64) g.priv.cap g.priv.ptr m.privateKey ∗
    vecU8At A (sp' + 64#64) g.sig.cap g.sig.ptr m.signature ∗
    ((sp' + 88#64) ↦₆₄ m.timestamp) ∗
    ((sp' + 96#64) ↦₃₂ m.id) ∗
    memRegion (sp' + 100#64) 4

def spkStructOf (A : RustAlloc) (sp' : BitVec 64)
    (m : SignedPreKeyRecordStructure) : SepProp :=
  ∃∗ g : SpkGhost, spkStructAt A g sp' m

def spkStructLoopOf (A : RustAlloc) (sp' : BitVec 64) (n : ℕ)
    (m : SignedPreKeyRecordStructure) : SepProp :=
  ∃∗ g : SpkGhost, ⌜SpkGhostCapOk g n⌝ ∗ spkStructAt A g sp' m

theorem spkStructAt_entails_of (A : RustAlloc) (g : SpkGhost) (sp' : BitVec 64)
    (m : SignedPreKeyRecordStructure) :
    spkStructAt A g sp' m ⊢ spkStructOf A sp' m :=
  Entails.sepExists_intro (P := fun g' => spkStructAt A g' sp' m) g

theorem spkStructAt_entails_loopOf (A : RustAlloc) (g : SpkGhost) (sp' : BitVec 64)
    (n : ℕ) (m : SignedPreKeyRecordStructure) (hg : SpkGhostCapOk g n) :
    spkStructAt A g sp' m ⊢ spkStructLoopOf A sp' n m := by
  unfold spkStructLoopOf
  refine Entails.trans ?_
    (Entails.sepExists_intro (P := fun g' => ⌜SpkGhostCapOk g' n⌝ ∗ spkStructAt A g' sp' m) g)
  rw [pure_true_emp hg, emp_sepConj]
  exact Entails.refl _

theorem spkStructLoopOf_entails_of (A : RustAlloc) (sp' : BitVec 64) (n : ℕ)
    (m : SignedPreKeyRecordStructure) :
    spkStructLoopOf A sp' n m ⊢ spkStructOf A sp' m :=
  Entails.sepExists_elim fun g =>
    Entails.pure_left fun _ => spkStructAt_entails_of A g sp' m

theorem spkStructLoopOf_mono (A : RustAlloc) (sp' : BitVec 64) {m n : ℕ}
    (st : SignedPreKeyRecordStructure) (hle : m ≤ n) :
    spkStructLoopOf A sp' n st ⊢ spkStructLoopOf A sp' m st :=
  Entails.sepExists_elim fun g =>
    Entails.pure_left fun hg =>
      spkStructAt_entails_loopOf A g sp' m st (hg.mono hle)

theorem vecU8At_entails_vecU8 (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A a cap ptr bs ⊢ vecU8 A a bs := by
  unfold vecU8
  exact Entails.trans
    (Entails.sepExists_intro (P := fun p => vecU8At A a cap p bs) ptr)
    (Entails.sepExists_intro (P := fun c => ∃∗ p, vecU8At A a c p bs) cap)

/-! ## Unified selector for the three `bytes` fields (tags 2, 3, 4) -/

inductive SpkBytesField
  | pub
  | priv
  | sig

namespace SpkBytesField

def slotOff : SpkBytesField → BitVec 64
  | .pub => 16#64
  | .priv => 40#64
  | .sig => 64#64

def pin (g : SpkGhost) : SpkBytesField → VecPin
  | .pub => g.pub
  | .priv => g.priv
  | .sig => g.sig

def setPin (g : SpkGhost) (p : VecPin) : SpkBytesField → SpkGhost
  | .pub => { g with pub := p }
  | .priv => { g with priv := p }
  | .sig => { g with sig := p }

def getBytes (m : SignedPreKeyRecordStructure) : SpkBytesField → List (BitVec 8)
  | .pub => m.publicKey
  | .priv => m.privateKey
  | .sig => m.signature

def setBytes (m : SignedPreKeyRecordStructure) (v : List (BitVec 8)) :
    SpkBytesField → SignedPreKeyRecordStructure
  | .pub => { m with publicKey := v }
  | .priv => { m with privateKey := v }
  | .sig => { m with signature := v }

def rest (A : RustAlloc) (g : SpkGhost) (sp' : BitVec 64)
    (m : SignedPreKeyRecordStructure) : SpkBytesField → SepProp
  | .pub =>
    vecU8At A (sp' + 40#64) g.priv.cap g.priv.ptr m.privateKey ∗
      vecU8At A (sp' + 64#64) g.sig.cap g.sig.ptr m.signature ∗
      ((sp' + 88#64) ↦₆₄ m.timestamp) ∗ ((sp' + 96#64) ↦₃₂ m.id) ∗ memRegion (sp' + 100#64) 4
  | .priv =>
    vecU8At A (sp' + 16#64) g.pub.cap g.pub.ptr m.publicKey ∗
      vecU8At A (sp' + 64#64) g.sig.cap g.sig.ptr m.signature ∗
      ((sp' + 88#64) ↦₆₄ m.timestamp) ∗ ((sp' + 96#64) ↦₃₂ m.id) ∗ memRegion (sp' + 100#64) 4
  | .sig =>
    vecU8At A (sp' + 16#64) g.pub.cap g.pub.ptr m.publicKey ∗
      vecU8At A (sp' + 40#64) g.priv.cap g.priv.ptr m.privateKey ∗
      ((sp' + 88#64) ↦₆₄ m.timestamp) ∗ ((sp' + 96#64) ↦₃₂ m.id) ∗ memRegion (sp' + 100#64) 4

theorem capOk_pin {g : SpkGhost} {n : ℕ} (hg : SpkGhostCapOk g n) (f : SpkBytesField) :
    BytesMergeCapOk (f.pin g).cap n := by
  cases f
  · exact hg.pub
  · exact hg.priv
  · exact hg.sig

theorem capOk_update {g : SpkGhost} {n m : ℕ} (hg : SpkGhostCapOk g n) (hle : m ≤ n)
    {p : VecPin} (hp : BytesMergeCapOk p.cap m) (f : SpkBytesField) :
    SpkGhostCapOk (f.setPin g p) m := by
  have hm := hg.mono hle
  cases f
  · exact ⟨hp, hm.priv, hm.sig⟩
  · exact ⟨hm.pub, hp, hm.sig⟩
  · exact ⟨hm.pub, hm.priv, hp⟩

theorem split_field (A : RustAlloc) (g : SpkGhost) (sp' : BitVec 64)
    (m : SignedPreKeyRecordStructure) (f : SpkBytesField) :
    spkStructAt A g sp' m =
      vecU8At A (sp' + f.slotOff) (f.pin g).cap (f.pin g).ptr (f.getBytes m) ∗
        f.rest A g sp' m := by
  cases f <;> (unfold spkStructAt slotOff pin getBytes rest; dsimp only; try ac_rfl)

theorem unsplit_field (A : RustAlloc) (g : SpkGhost) (sp' : BitVec 64)
    (m : SignedPreKeyRecordStructure) (p : VecPin) (v : List (BitVec 8)) (f : SpkBytesField) :
    vecU8At A (sp' + f.slotOff) p.cap p.ptr v ∗ f.rest A g sp' m =
      spkStructAt A (f.setPin g p) sp' (f.setBytes m v) := by
  cases f <;> (unfold spkStructAt slotOff setPin setBytes rest; dsimp only; try ac_rfl)

end SpkBytesField

theorem spkStructAt_split_id (A : RustAlloc) (g : SpkGhost) (sp' : BitVec 64)
    (m : SignedPreKeyRecordStructure) :
    spkStructAt A g sp' m =
      ((sp' + 96#64) ↦₃₂ m.id) ∗
        (vecU8At A (sp' + 16#64) g.pub.cap g.pub.ptr m.publicKey ∗
          vecU8At A (sp' + 40#64) g.priv.cap g.priv.ptr m.privateKey ∗
          vecU8At A (sp' + 64#64) g.sig.cap g.sig.ptr m.signature ∗
          ((sp' + 88#64) ↦₆₄ m.timestamp) ∗
          memRegion (sp' + 100#64) 4) := by
  unfold spkStructAt; ac_rfl

theorem spkStructAt_split_timestamp (A : RustAlloc) (g : SpkGhost) (sp' : BitVec 64)
    (m : SignedPreKeyRecordStructure) :
    spkStructAt A g sp' m =
      ((sp' + 88#64) ↦₆₄ m.timestamp) ∗
        (vecU8At A (sp' + 16#64) g.pub.cap g.pub.ptr m.publicKey ∗
          vecU8At A (sp' + 40#64) g.priv.cap g.priv.ptr m.privateKey ∗
          vecU8At A (sp' + 64#64) g.sig.cap g.sig.ptr m.signature ∗
          ((sp' + 96#64) ↦₃₂ m.id) ∗
          memRegion (sp' + 100#64) 4) := by
  unfold spkStructAt; ac_rfl

/-! ## Saved callee registers & loop / convergence invariants -/

/-- Saved callee-saved GPRs in `[sp' + 160 .. sp' + 224)` (`64` bytes). -/
def spkCalleeSavedAt (sp' : BitVec 64) (s0 : State) : SepProp :=
  ((sp' + 160#64) ↦₆₄ s0.readReg64 .x29) ∗
    ((sp' + 168#64) ↦₆₄ s0.readReg64 .x30) ∗
    ((sp' + 176#64) ↦₆₄ s0.readReg64 .x24) ∗
    ((sp' + 184#64) ↦₆₄ s0.readReg64 .x23) ∗
    ((sp' + 192#64) ↦₆₄ s0.readReg64 .x22) ∗
    ((sp' + 200#64) ↦₆₄ s0.readReg64 .x21) ∗
    ((sp' + 208#64) ↦₆₄ s0.readReg64 .x20) ∗
    ((sp' + 216#64) ↦₆₄ s0.readReg64 .x19)

/-- Callee-saved GPRs NOT spilled to stack (`x25..x28`), preserved across every basic block and call. -/
structure SpkSavedRegs (s0 s : State) : Prop where
  x25 : s.readReg64 .x25 = s0.readReg64 .x25
  x26 : s.readReg64 .x26 = s0.readReg64 .x26
  x27 : s.readReg64 .x27 = s0.readReg64 .x27
  x28 : s.readReg64 .x28 = s0.readReg64 .x28

/-- Live register invariant across the decode loop (`+0x05c .. +0x28c`). -/
structure SpkLoopRegs (s0 : State) (sp' x19 : BitVec 64) (s : State) : Prop where
  sp : s.sp = sp'
  x29 : s.readReg64 .x29 = sp' + 160#64
  x24 : s.readReg64 .x24 = sp' + 16#64
  x19_eq : s.readReg64 .x19 = x19
  saved : SpkSavedRegs s0 s

/-- State invariant at the shared `Ok` / `Err` convergence point `+656` (`spkOff_converge`). -/
structure SpkConvergeState (img : Obj.Image) (s0 : State) (sp' x19 : BitVec 64) (s : State) : Prop where
  sp : s.sp = sp'
  spAlign : s.spAligned = true
  frozen : img.FrozenLoaded s
  sym : s.symtab = img.symtab
  tr : s.trace = s0.trace
  x24 : s.readReg64 .x24 = sp' + 16#64
  x19_eq : s.readReg64 .x19 = x19
  saved : SpkSavedRegs s0 s

/-- Separation-logic state at `+656` (`spkOff_converge`), parameterized by `out : Option SignedPreKeyRecordStructure`
and the error pointer `x1Val` (`0#64` for `some m`, nonzero `err` for `none`). -/
def spkConvergeMem (A : RustAlloc) (sp' x19 ptr : BitVec 64)
    (bs : List (BitVec 8)) (out : Option SignedPreKeyRecordStructure) (x1Val : BitVec 64) : SepProp :=
  match out with
  | some m =>
    ⌜x1Val = 0#64⌝ ∗
      spkStructOf A sp' m ∗
      memRegion sp' 16 ∗
      ((sp' + 104#64) ↦₆₄ sp') ∗
      memRegion (sp' + 112#64) 48 ∗
      memRegion x19 88 ∗
      (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt sp' (SpqrV1.Varint.skipField3Stack 100)
  | none =>
    ⌜x1Val ≠ 0#64⌝ ∗
      (∃∗ mErr : SignedPreKeyRecordStructure, spkStructOf A sp' mErr) ∗
      decodeErrorAt A x1Val ∗
      memRegion sp' 16 ∗
      ((sp' + 104#64) ↦₆₄ sp') ∗
      memRegion (sp' + 112#64) 48 ∗
      memRegion x19 88 ∗
      (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt sp' (SpqrV1.Varint.skipField3Stack 100)

def spkConvergePost (img : Obj.Image) (A : RustAlloc) (s0 : State)
    (sp' x19 ptr : BitVec 64) (bs : List (BitVec 8))
    (out : Option SignedPreKeyRecordStructure) : State → SepProp → Prop :=
  fun sf Pf =>
    SpkConvergeState img s0 sp' x19 sf ∧
      (Pf ⊢ spkConvergeMem A sp' x19 ptr bs out (sf.readReg64 .x1))

theorem spkConvergePost_append_prefix (img : Obj.Image) (A : RustAlloc) (s0 : State)
    (sp' x19 ptr : BitVec 64) (bs : List (BitVec 8)) (k : ℕ) (hkl : k ≤ bs.length)
    (out : Option SignedPreKeyRecordStructure) (sf : State) (Pf : SepProp)
    (hq : spkConvergePost img A s0 sp' x19 (ptr + BitVec.ofNat 64 k) (bs.drop k) out sf Pf) :
    spkConvergePost img A s0 sp' x19 ptr bs out sf (Pf ∗ (ptr ↦ₛ bs.take k)) := by
  rcases hq with ⟨hst, hent⟩
  refine ⟨hst, ?_⟩
  have hcat : (ptr ↦ₛ bs.take k) ∗ ((ptr + BitVec.ofNat 64 k) ↦ₛ bs.drop k) = (ptr ↦ₛ bs) := by
    have ht : (bs.take k).length = k := by simp [Nat.min_eq_left hkl]
    have hp := (pointsToBytes_append ptr (bs.take k) (bs.drop k)).symm
    rw [ht, List.take_append_drop] at hp
    exact hp
  cases out with
  | some m =>
    dsimp only [spkConvergeMem] at hent ⊢
    refine Entails.trans (sepConj_mono_left hent) ?_
    apply entails_of_eq
    rw [← hcat]; ac_rfl
  | none =>
    dsimp only [spkConvergeMem] at hent ⊢
    refine Entails.trans (sepConj_mono_left hent) ?_
    apply entails_of_eq
    rw [← hcat]; ac_rfl

/-- Active loop memory bundle at latch (`+92`) and key decode (`+104`). -/
def spkLoopMem (A : RustAlloc) (sp' x19 ptr : BitVec 64)
    (bs : List (BitVec 8)) (m : SignedPreKeyRecordStructure) : SepProp :=
  sliceCursorAt sp' ptr bs ∗
    ((sp' + 104#64) ↦₆₄ sp') ∗
    memRegion (sp' + 112#64) 48 ∗
    spkStructLoopOf A sp' bs.length m ∗
    memRegion x19 88 ∗
    A.pool ∗
    stackAt sp' (SpqrV1.Varint.skipField3Stack 100)

/-- Post-varint/field cursor memory before advancing `ptr` past consumed prefix bytes. -/
def spkAfterVarintMem (A : RustAlloc) (sp' x19 ptr : BitVec 64)
    (bs rest : List (BitVec 8)) (n : ℕ) (m : SignedPreKeyRecordStructure) : SepProp :=
  sliceCursorAfter sp' ptr bs rest ∗
    ((sp' + 104#64) ↦₆₄ sp') ∗
    memRegion (sp' + 112#64) 48 ∗
    spkStructLoopOf A sp' n m ∗
    memRegion x19 88 ∗
    A.pool ∗
    stackAt sp' (SpqrV1.Varint.skipField3Stack 100)

theorem spkAdvanceCursor {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {s0 s : State} {sp' x19 ptr : BitVec 64}
    {bs rest : List (BitVec 8)} {out : Option SignedPreKeyRecordStructure} {R : SepProp}
    (hsuf : ∃ k, k ≤ bs.length ∧ rest = bs.drop k)
    (h : Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_converge) s
      (sliceCursorAt sp' (ptr + BitVec.ofNat 64 (bs.length - rest.length)) rest ∗ R)
      (spkConvergePost img A s0 sp' x19
        (ptr + BitVec.ofNat 64 (bs.length - rest.length)) rest out)
      (tryFromQp s0)) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_converge) s
      (sliceCursorAfter sp' ptr bs rest ∗ R)
      (spkConvergePost img A s0 sp' x19 ptr bs out)
      (tryFromQp s0) := by
  rw [sliceCursorAfter_eq_take_cursorAt sp' ptr bs rest hsuf]
  rcases hsuf with ⟨k, hkl, rfl⟩
  have hk : bs.length - (bs.drop k).length = k := by simp; omega
  rw [hk] at h ⊢
  refine Wire.SepWPp.mono_pre
    (P' := (sliceCursorAt sp' (ptr + BitVec.ofNat 64 k) (bs.drop k) ∗ R) ∗
      (ptr ↦ₛ bs.take k))
    (by apply entails_of_eq; ac_rfl) ?_
  exact Wire.SepWPp.frame_tryFrom h
    (fun sf Pf hqm => spkConvergePost_append_prefix img A s0 sp' x19 ptr bs k hkl out sf Pf hqm)

/-! ## Stack-parametric callee bundle (`SpkCfg` / `SpkBundle`) unifying Legacy and X-form -/

structure SpkCfg where
  varintStk : Nat
  mergeStk : Nat
  errStk : Nat
  deallocStk : Nat
  skipStk : Nat → Nat
  h_varint : varintStk ≤ skipStk 100
  h_merge : mergeStk ≤ skipStk 100
  h_err : errStk ≤ skipStk 100
  h_dealloc : deallocStk ≤ skipStk 100
  h_total_lt : 224 + skipStk 100 < 2 ^ 64

abbrev SpkCfg.subStack (cfg : SpkCfg) : Nat := cfg.skipStk 100

def spkCfgLegacy : SpkCfg where
  varintStk := SpqrV1.Varint.decodeVarint2Stack
  mergeStk := SpqrV1.Prost.BytesMerge.bytesMerge3Stack
  errStk := decodeErrorHookStack
  deallocStk := allocHookStack
  skipStk := SpqrV1.Varint.skipField3Stack
  h_varint := by decide
  h_merge := by decide
  h_err := by decide
  h_dealloc := by decide
  h_total_lt := by decide

def spkCfgX : SpkCfg where
  varintStk := SpqrV1.Varint.decodeVarint2StackX
  mergeStk := bytesMerge3StackX
  errStk := 2 * extHookStack
  deallocStk := extHookStack
  skipStk := skipField3StackX
  h_varint := by decide
  h_merge := by decide
  h_err := by decide
  h_dealloc := by decide
  h_total_lt := by decide

def spkDecodeVarintSpecAt (stk : Nat) (A : RustAlloc) : Spec DecodeVarintSlowGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.bufRef ∧ x.bs.length < 2 ^ 63⌝ ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool ∗ stackAt s.sp stk
  post := fun x s0 sf =>
    (match decodeVarint x.bs with
      | some (v, _) => ⌜sf.readReg64 .x0 = 0#64 ∧ sf.readReg64 .x1 = v⌝
      | none => ⌜sf.readReg64 .x0 = 1#64⌝) ∗
      ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗
      stackAt s0.sp stk ∗
      match decodeVarint x.bs with
      | some (_, rest) =>
        sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x1 ≠ 0#64⌝ ∗
          decodeErrorAtStackLen A (sf.readReg64 .x1) 0 ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def spkSkipFieldSpecAt (skipStk : Nat → Nat) (A : RustAlloc) : Spec SkipFieldGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 x.tag ∧ x.tag < 2 ^ 32 ∧
      s.readReg64 .x2 = x.bufRef ∧
      (s.readReg64 .x3).setWidth 32 = BitVec.ofNat 32 x.depth ∧ x.depth < 2 ^ 32 ∧
      x.bs.length < 2 ^ 63⌝ ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool ∗ stackAt s.sp (skipStk x.depth)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗
      stackAt s0.sp (skipStk x.depth) ∗
      match skipField (2 * x.bs.length + 2) x.depth x.tag x.wt x.bs with
      | some rest =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ decodeErrorAtStackLen A (sf.readReg64 .x0) 0 ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def spkBytesMergeRawSpecAt (stk : Nat) (A : RustAlloc) : Spec BytesMergeGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.valPtr ∧ s.readReg64 .x2 = x.bufRef ∧ x.bs.length < 2 ^ 63 ∧
      BytesMergeCapOk x.valCap x.bs.length⌝ ∗
      vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool ∗ stackAt s.sp stk
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗ stackAt s0.sp stk ∗
      match mergeBytes x.wt x.bs with
      | some (v, rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗
          (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
            ⌜BytesMergeCapOk cap' rest.length⌝ ∗ vecU8At A x.valPtr cap' ptr' v) ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ decodeErrorAtStackLen A (sf.readReg64 .x0) 0 ∗
          vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Unified callee bundle at relative offsets from `signedDecodeName` for any `cfg : SpkCfg`. -/
structure SpkBundle (cfg : SpkCfg) (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop where
  decodeVarint6 :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName +
        bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#5]") -
          ls_off% "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>"))
      ((spkDecodeVarintSpecAt cfg.varintStk A).inImage img)
  skipField7 :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName +
        bv% (2 ^ 64 + (ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#6]") -
          ls_off% "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>"))
      ((spkSkipFieldSpecAt cfg.skipStk A).inImage img)
  bytesMerge7 :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName +
        bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#6]") -
          ls_off% "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>"))
      ((spkBytesMergeRawSpecAt cfg.mergeStk A).inImage img)
  decodeErrorFrom :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName +
        bv% (2 ^ 64 + (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from") -
          ls_off% "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>"))
      ((decodeErrorFromSpecWithStack A cfg.errStk).inImage img)
  decodeErrorPush :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName +
        bv% (2 ^ 64 + (ls_off% "<prost::error::DecodeError>::push") -
          ls_off% "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>"))
      ((decodeErrorPushExternSpecWithStack A cfg.errStk).inImage img)
  dealloc :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName +
        bv% (ls_off% "__rustc::__rust_dealloc" -
          ls_off% "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>"))
      ((rustDeallocExternSpecWithStack A cfg.deallocStk).inImage img)

theorem SpkBundle.of_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hH : SignedHooksX img A ext) (d : SignedPortDepsX img A ext) :
    SpkBundle spkCfgX img A ext where
  decodeVarint6 := by
    have heq :
        (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName +
          bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#5]") -
            ls_off% "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>") =
        (tripleRatchetProgAtExt img.base ext).fnAddr decodeVarint6Name := by
      rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
        (ls_lemma% fnOff "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>"),
        (ls_lemma% fnOff "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#5]")]
      bv_omega
    rw [heq]
    exact d.decodeVarint6
  skipField7 := by
    have heq :
        (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName +
          bv% (2 ^ 64 + (ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#6]") -
            ls_off% "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>") =
        (tripleRatchetProgAtExt img.base ext).fnAddr skipField7Name := by
      rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
        (ls_lemma% fnOff "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>"),
        (ls_lemma% fnOff "prost::encoding::skip_field::<&mut &[u8]> [local#6]")]
      bv_omega
    rw [heq]
    exact d.skipField7
  bytesMerge7 := by
    have heq :
        (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName +
          bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#6]") -
            ls_off% "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>") =
        (tripleRatchetProgAtExt img.base ext).fnAddr bytesMerge7Name := by
      rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
        (ls_lemma% fnOff "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>"),
        (ls_lemma% fnOff "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#6]")]
      bv_omega
    rw [heq]
    exact d.bytesMerge7
  decodeErrorFrom := by
    have heq :
        (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName +
          bv% (2 ^ 64 + (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from") -
            ls_off% "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>") =
        (tripleRatchetProgAtExt img.base ext).fnAddr decodeErrorFromName := by
      rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
        (ls_lemma% fnOff "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>"),
        (ls_lemma% fnOff "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from")]
      bv_omega
    rw [heq]
    exact hH.decodeErrorFrom
  decodeErrorPush := by
    have heq :
        (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName +
          bv% (2 ^ 64 + (ls_off% "<prost::error::DecodeError>::push") -
            ls_off% "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>") =
        (tripleRatchetProgAtExt img.base ext).fnAddr decodeErrorPushName := by
      rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
        (ls_lemma% fnOff "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>"),
        (ls_lemma% fnOff "<prost::error::DecodeError>::push")]
      bv_omega
    rw [heq]
    exact hH.decodeErrorPush
  dealloc :=
    sub_ok_at_of_fnAddr hH.alloc.dealloc signedDecodeName
      (num% (ls_off% "__rustc::__rust_dealloc" -
        ls_off% "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>"))

theorem SpkBundle.of_legacy {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hH : SignedHooks img.base A ext) (d : SignedPortDeps img A ext) :
    SpkBundle spkCfgLegacy img A ext where
  decodeVarint6 := spk_decodeVarint6_ok d
  skipField7 := spk_skipField7_ok d
  bytesMerge7 := spk_bytesMerge7_ok d
  decodeErrorFrom := by
    have h := decodeErrorFromWithStack_of_decodeErrorFrom hH.decodeErrorFrom
      (hookStack := decodeErrorHookStack)
    have heq :
        (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName +
          bv% (2 ^ 64 + (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from") -
            ls_off% "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>") =
        (tripleRatchetProgAtExt img.base ext).fnAddr decodeErrorFromName := by
      rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
        (ls_lemma% fnOff "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>"),
        (ls_lemma% fnOff "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from")]
      bv_omega
    rw [heq]
    exact subroutine_ok_inImage_of_subroutine_ok img h
  decodeErrorPush := by
    have h1 := decodeErrorPushWithStack_of_decodeErrorPush hH.decodeErrorPush
      (hookStack := decodeErrorHookStack)
    have h2 := decodeErrorPushExtern_of_decodeErrorPush h1
    have heq :
        (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName +
          bv% (2 ^ 64 + (ls_off% "<prost::error::DecodeError>::push") -
            ls_off% "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>") =
        (tripleRatchetProgAtExt img.base ext).fnAddr decodeErrorPushName := by
      rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
        (ls_lemma% fnOff "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>"),
        (ls_lemma% fnOff "<prost::error::DecodeError>::push")]
      bv_omega
    rw [heq]
    exact subroutine_ok_inImage_of_subroutine_ok img h2
  dealloc := by
    have h := rustDeallocExternWithStack_of_rustDealloc hH.alloc.dealloc
      (hookStack := allocHookStack)
    exact subroutine_ok_inImage_of_subroutine_ok img
      (sub_ok_at_of_fnAddr h signedDecodeName
        (num% (ls_off% "__rustc::__rust_dealloc" -
          ls_off% "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>")))

def spkConvergeMemAt (subStack : Nat) (A : RustAlloc) (sp' x19 ptr : BitVec 64)
    (bs : List (BitVec 8)) (out : Option SignedPreKeyRecordStructure) (x1Val : BitVec 64) : SepProp :=
  match out with
  | some m =>
    ⌜x1Val = 0#64⌝ ∗
      spkStructOf A sp' m ∗
      memRegion sp' 16 ∗
      ((sp' + 104#64) ↦₆₄ sp') ∗
      memRegion (sp' + 112#64) 48 ∗
      memRegion x19 88 ∗
      (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt sp' subStack
  | none =>
    ⌜x1Val ≠ 0#64⌝ ∗
      (∃∗ mErr : SignedPreKeyRecordStructure, spkStructOf A sp' mErr) ∗
      decodeErrorAt A x1Val ∗
      memRegion sp' 16 ∗
      ((sp' + 104#64) ↦₆₄ sp') ∗
      memRegion (sp' + 112#64) 48 ∗
      memRegion x19 88 ∗
      (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt sp' subStack

def spkConvergePostAt (subStack : Nat) (img : Obj.Image) (A : RustAlloc) (s0 : State)
    (sp' x19 ptr : BitVec 64) (bs : List (BitVec 8))
    (out : Option SignedPreKeyRecordStructure) : State → SepProp → Prop :=
  fun sf Pf =>
    SpkConvergeState img s0 sp' x19 sf ∧
      (Pf ⊢ spkConvergeMemAt subStack A sp' x19 ptr bs out (sf.readReg64 .x1))

theorem spkConvergePostAt_append_prefix (subStack : Nat) (img : Obj.Image) (A : RustAlloc) (s0 : State)
    (sp' x19 ptr : BitVec 64) (bs : List (BitVec 8)) (k : ℕ) (hkl : k ≤ bs.length)
    (out : Option SignedPreKeyRecordStructure) (sf : State) (Pf : SepProp)
    (hq : spkConvergePostAt subStack img A s0 sp' x19 (ptr + BitVec.ofNat 64 k) (bs.drop k) out sf Pf) :
    spkConvergePostAt subStack img A s0 sp' x19 ptr bs out sf (Pf ∗ (ptr ↦ₛ bs.take k)) := by
  rcases hq with ⟨hst, hent⟩
  refine ⟨hst, ?_⟩
  have hcat : (ptr ↦ₛ bs.take k) ∗ ((ptr + BitVec.ofNat 64 k) ↦ₛ bs.drop k) = (ptr ↦ₛ bs) := by
    have ht : (bs.take k).length = k := by simp [Nat.min_eq_left hkl]
    have hp := (pointsToBytes_append ptr (bs.take k) (bs.drop k)).symm
    rw [ht, List.take_append_drop] at hp
    exact hp
  cases out with
  | some m =>
    dsimp only [spkConvergeMemAt] at hent ⊢
    refine Entails.trans (sepConj_mono_left hent) ?_
    apply entails_of_eq
    rw [← hcat]; ac_rfl
  | none =>
    dsimp only [spkConvergeMemAt] at hent ⊢
    refine Entails.trans (sepConj_mono_left hent) ?_
    apply entails_of_eq
    rw [← hcat]; ac_rfl

def spkLoopMemAt (subStack : Nat) (A : RustAlloc) (sp' x19 ptr : BitVec 64)
    (bs : List (BitVec 8)) (m : SignedPreKeyRecordStructure) : SepProp :=
  sliceCursorAt sp' ptr bs ∗
    ((sp' + 104#64) ↦₆₄ sp') ∗
    memRegion (sp' + 112#64) 48 ∗
    spkStructLoopOf A sp' bs.length m ∗
    memRegion x19 88 ∗
    A.pool ∗
    stackAt sp' subStack

def spkAfterVarintMemAt (subStack : Nat) (A : RustAlloc) (sp' x19 ptr : BitVec 64)
    (bs rest : List (BitVec 8)) (n : ℕ) (m : SignedPreKeyRecordStructure) : SepProp :=
  sliceCursorAfter sp' ptr bs rest ∗
    ((sp' + 104#64) ↦₆₄ sp') ∗
    memRegion (sp' + 112#64) 48 ∗
    spkStructLoopOf A sp' n m ∗
    memRegion x19 88 ∗
    A.pool ∗
    stackAt sp' subStack

theorem spkAdvanceCursorAt {subStack : Nat} {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {s0 s : State} {sp' x19 ptr : BitVec 64}
    {bs rest : List (BitVec 8)} {out : Option SignedPreKeyRecordStructure} {R : SepProp}
    (hsuf : ∃ k, k ≤ bs.length ∧ rest = bs.drop k)
    (h : Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_converge) s
      (sliceCursorAt sp' (ptr + BitVec.ofNat 64 (bs.length - rest.length)) rest ∗ R)
      (spkConvergePostAt subStack img A s0 sp' x19
        (ptr + BitVec.ofNat 64 (bs.length - rest.length)) rest out)
      (tryFromQp s0)) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_converge) s
      (sliceCursorAfter sp' ptr bs rest ∗ R)
      (spkConvergePostAt subStack img A s0 sp' x19 ptr bs out)
      (tryFromQp s0) := by
  rw [sliceCursorAfter_eq_take_cursorAt sp' ptr bs rest hsuf]
  rcases hsuf with ⟨k, hkl, rfl⟩
  have hk : bs.length - (bs.drop k).length = k := by simp; omega
  rw [hk] at h ⊢
  refine Wire.SepWPp.mono_pre
    (P' := (sliceCursorAt sp' (ptr + BitVec.ofNat 64 k) (bs.drop k) ∗ R) ∗
      (ptr ↦ₛ bs.take k))
    (by apply entails_of_eq; ac_rfl) ?_
  exact Wire.SepWPp.frame_tryFrom h
    (fun sf Pf hqm => spkConvergePostAt_append_prefix subStack img A s0 sp' x19 ptr bs k hkl out sf Pf hqm)

/-! ## Relocatable `[LibsignalPlacement]` Callee Wrappers & Convergence State (Block `562`) -/

section Placed

open CryptoVerification.RecordCodecs.Placed

theorem spk_decodeVarint6_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (d : SignedPortDepsPlaced A H) :
    subroutine_ok (lsProg_562 H) (lsmpl.base 559)
      (withLsCodeRoLoaded lsmpl (SpqrV1.Varint.decodeVarint2Spec A)) :=
  ls_subroutine_ok_lscro_of_cl (callerProg := lsProg_562 H) d.decodeVarint6

theorem spk_skipField7_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (d : SignedPortDepsPlaced A H) :
    subroutine_ok (lsProg_562 H) (lsmpl.base 546)
      (withLsCodeRoLoaded lsmpl (SpqrV1.Varint.skipField3Spec A)) :=
  ls_subroutine_ok_lscro_of_cl (callerProg := lsProg_562 H) d.skipField7

theorem spk_bytesMerge7_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (d : SignedPortDepsPlaced A H) :
    subroutine_ok (lsProg_562 H) (lsmpl.base 558)
      (withLsCodeRoLoaded lsmpl (SpqrV1.Prost.BytesMerge.bytesMerge3RawSpec A)) :=
  ls_subroutine_ok_lscro_of_block (callerProg := lsProg_562 H) d.bytesMerge7

theorem spk_decodeErrorFrom_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hH : SignedHooksPlaced A H) :
    subroutine_ok (lsProg_562 H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromSpec A)) :=
  ls_subroutine_ok_lscro_of_cl (callerProg := lsProg_562 H) hH.decodeErrorFrom

theorem spk_decodeErrorPush_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hH : SignedHooksPlaced A H) :
    subroutine_ok (lsProg_562 H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushSpec A)) :=
  ls_subroutine_ok_lscro_of_cl (callerProg := lsProg_562 H) hH.decodeErrorPush

theorem spk_dealloc_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hH : SignedHooksPlaced A H) :
    subroutine_ok (lsProg_562 H) (lsρ lsRustDeallocSym)
      (withLsCodeRoLoaded lsmpl (rustDeallocSpec A)) :=
  subroutine_ok_withLsCodeRoLoaded_of_plain
    (ls_hook_ok_of_mem hH.dealloc (by decide) (by decide) (by decide))

theorem spk_call_noPanic_lscro {α : Type} {prog : Program} {pl : Obj.MultiPlacement}
    {ret entry ret_pc : BitVec 64} {s0 s : State} {P T F : SepProp} {φ : Prop}
    {Q : State → SepProp → Prop} {spec : Spec α} (x : α)
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded pl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded pl s.mem)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F := by sep_focus)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → LibsignalCodeRoLoaded pl sf.mem →
      CalleeSavedPreserved s sf →
      Wire.SepWPp prog ret sf (spec.post x s sf ∗ F) Q (Wire.tryFromQp s0))
    (hexit : ∀ sf code, spec.onExit x code s sf = ⌜False⌝ := by intros; rfl)
    (hpan : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intros; rfl)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    Wire.SepWPp prog ret s P Q (Wire.tryFromQp s0) := by
  intro R' hm hL
  have hpre : s.mem ⊨ (withLsCodeRoLoaded pl spec).pre x s ∗ (F ∗ R') := by
    dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl, ?_⟩
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R') s hpc hrun hpre hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hoom⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hspm_align : sm.spAligned = true := by
      rw [State.spAligned, hspm, ← State.spAligned]; exact hsp
    have hcrl_m := hcrl.of_keepsFrozen hsteps.keepsFrozen
    obtain ⟨sf, hsteps', ⟨hpcf, hrunf, Pf, hmf, hqf, hvf⟩ | hpanf⟩ :=
      hnext sm hpcm hrunm hspm hspm_align hcrl_m hcsm R' hpost (hsteps.codeLoaded hL)
    · exact ⟨sf, hsteps.trans hsteps',
        Or.inl ⟨hpcf, hrunf, Pf, hmf, hqf, hvf.trans hcsm.2.2.2.2.2.2.2.2.2.2.2⟩⟩
    · exact ⟨sf, hsteps.trans hsteps', Or.inr hpanf⟩
  · dsimp only [withLsCodeRoLoaded] at hpost; rw [hpan sm] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · dsimp only [withLsCodeRoLoaded] at hpost; rw [hexit sm code] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · dsimp only [withLsCodeRoLoaded] at hoom; rw [hoom_eq sm] at hoom
    exact (not_satisfies_false_sepConj hoom).elim

structure SpkConvergeStatePlaced [LibsignalPlacement] (s0 : State) (sp' x19 : BitVec 64)
    (s : State) : Prop where
  sp : s.sp = sp'
  spAlign : s.spAligned = true
  crl : LibsignalCodeRoLoaded lsmpl s.mem
  tr : s.trace = s0.trace
  x24 : s.readReg64 .x24 = sp' + 16#64
  x19_eq : s.readReg64 .x19 = x19
  saved : SpkSavedRegs s0 s

def spkConvergePostPlaced [LibsignalPlacement] (A : RustAlloc) (s0 : State)
    (sp' x19 ptr : BitVec 64) (bs : List (BitVec 8))
    (out : Option SignedPreKeyRecordStructure) : State → SepProp → Prop :=
  fun sf Pf =>
    SpkConvergeStatePlaced s0 sp' x19 sf ∧
      (Pf ⊢ spkConvergeMem A sp' x19 ptr bs out (sf.readReg64 .x1))

theorem spkConvergePostPlaced_append_prefix [LibsignalPlacement] (A : RustAlloc) (s0 : State)
    (sp' x19 ptr : BitVec 64) (bs : List (BitVec 8)) (k : ℕ) (hkl : k ≤ bs.length)
    (out : Option SignedPreKeyRecordStructure) (sf : State) (Pf : SepProp)
    (hq : spkConvergePostPlaced A s0 sp' x19 (ptr + BitVec.ofNat 64 k) (bs.drop k) out sf Pf) :
    spkConvergePostPlaced A s0 sp' x19 ptr bs out sf (Pf ∗ (ptr ↦ₛ bs.take k)) := by
  rcases hq with ⟨hst, hent⟩
  refine ⟨hst, ?_⟩
  have hcat : (ptr ↦ₛ bs.take k) ∗ ((ptr + BitVec.ofNat 64 k) ↦ₛ bs.drop k) = (ptr ↦ₛ bs) := by
    have ht : (bs.take k).length = k := by simp [Nat.min_eq_left hkl]
    have hp := (pointsToBytes_append ptr (bs.take k) (bs.drop k)).symm
    rw [ht, List.take_append_drop] at hp
    exact hp
  cases out <;> (
    dsimp only [spkConvergeMem] at hent ⊢
    refine Entails.trans (sepConj_mono_left hent) ?_
    apply entails_of_eq; rw [← hcat]; ac_rfl)

theorem spkAdvanceCursor_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {s0 s : State} {sp' x19 ptr : BitVec 64}
    {bs rest : List (BitVec 8)} {out : Option SignedPreKeyRecordStructure} {R : SepProp}
    (hsuf : ∃ k, k ≤ bs.length ∧ rest = bs.drop k)
    (h : Wire.SepWPp (lsProg_562 H)
      ((blkPl_562).base + spkOff_converge) s
      (sliceCursorAt sp' (ptr + BitVec.ofNat 64 (bs.length - rest.length)) rest ∗ R)
      (spkConvergePostPlaced A s0 sp' x19
        (ptr + BitVec.ofNat 64 (bs.length - rest.length)) rest out)
      (tryFromQp s0)) :
    Wire.SepWPp (lsProg_562 H)
      ((blkPl_562).base + spkOff_converge) s
      (sliceCursorAfter sp' ptr bs rest ∗ R)
      (spkConvergePostPlaced A s0 sp' x19 ptr bs out)
      (tryFromQp s0) := by
  rw [sliceCursorAfter_eq_take_cursorAt sp' ptr bs rest hsuf]
  rcases hsuf with ⟨k, hkl, rfl⟩
  have hk : bs.length - (bs.drop k).length = k := by simp; omega
  rw [hk] at h ⊢
  refine Wire.SepWPp.mono_pre
    (P' := (sliceCursorAt sp' (ptr + BitVec.ofNat 64 k) (bs.drop k) ∗ R) ∗
      (ptr ↦ₛ bs.take k))
    (by apply entails_of_eq; ac_rfl) ?_
  exact Wire.SepWPp.frame_tryFrom h
    (fun sf Pf hqm => spkConvergePostPlaced_append_prefix A s0 sp' x19 ptr bs k hkl out sf Pf hqm)

end Placed

end CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers

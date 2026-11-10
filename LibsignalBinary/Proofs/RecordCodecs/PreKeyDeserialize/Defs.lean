/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.Deps
public import LibsignalBinary.Proofs.RecordCodecs.RecordCodecsCodeSymA
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBody

/-!
# `PreKeyRecord::deserialize` Callee Wrappers, Stack Layout, and Epilogue State

Relative-offset and `[LibsignalPlacement]` (Block `65`) callee wrappers, `PreKeyDeserializeHooks`,
stack-slot layout for `PreKeyRecordStructure` (`sp' + 56`), and epilogue state at `+0x224`.
-/

@[expose] public section

namespace CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers

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

abbrev pkDecOff : Nat :=
  num% (ls_off% "<libsignal_protocol::state::prekey::PreKeyRecord>::deserialize")

theorem pkDec_fnOff :
    libsignalSessionCode.fnOff preKeyDeserializeName = pkDecOff :=
  ls_lemma% fnOff "<libsignal_protocol::state::prekey::PreKeyRecord>::deserialize"

gen_decodes CryptoVerification.libsignalSessionCode_tree pkDec
  [(num% (ls_off% "<libsignal_protocol::state::prekey::PreKeyRecord>::deserialize")) →
   (num% (ls_off% "<libsignal_protocol::state::prekey::PreKeyRecord>::deserialize" + 736))]

/-! ## Callee contracts at relative offsets from `preKeyDeserializeName` -/

theorem varintSlice_ok_sub {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (d : DecodeDeps img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName +
        bv% (ls_off% "prost::encoding::varint::decode_varint_slice" -
          ls_off% "<libsignal_protocol::state::prekey::PreKeyRecord>::deserialize"))
      ((decodeVarintSliceSpecX A).inImage img) :=
  sub_ok_at_of_fnAddr d.varintSlice preKeyDeserializeName
    (num% (ls_off% "prost::encoding::varint::decode_varint_slice" -
      ls_off% "<libsignal_protocol::state::prekey::PreKeyRecord>::deserialize"))

theorem int32Merge_ok_sub {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (d : DecodeDeps img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName +
        bv% (2 ^ 64 + (ls_off% "prost::encoding::int32::merge::<&mut &[u8]>") -
          ls_off% "<libsignal_protocol::state::prekey::PreKeyRecord>::deserialize"))
      ((int32MergeSpecX A).inImage img) := by
  have heq :
      (tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName +
        bv% (2 ^ 64 + (ls_off% "prost::encoding::int32::merge::<&mut &[u8]>") -
          ls_off% "<libsignal_protocol::state::prekey::PreKeyRecord>::deserialize") =
      (tripleRatchetProgAtExt img.base ext).fnAddr int32MergeName := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "<libsignal_protocol::state::prekey::PreKeyRecord>::deserialize"),
      (ls_lemma% fnOff "prost::encoding::int32::merge::<&mut &[u8]>")]
    bv_omega
  rw [heq]; exact d.int32Merge

theorem skipField_ok_sub {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (d : DecodeDeps img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName +
        bv% (2 ^ 64 + (ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]") -
          ls_off% "<libsignal_protocol::state::prekey::PreKeyRecord>::deserialize"))
      ((skipFieldSpecX A).inImage img) := by
  have heq :
      (tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName +
        bv% (2 ^ 64 + (ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]") -
          ls_off% "<libsignal_protocol::state::prekey::PreKeyRecord>::deserialize") =
      (tripleRatchetProgAtExt img.base ext).fnAddr skipFieldName := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "<libsignal_protocol::state::prekey::PreKeyRecord>::deserialize"),
      (ls_lemma% fnOff "prost::encoding::skip_field::<&mut &[u8]> [local#1]")]
    bv_omega
  rw [heq]; exact d.skipField

theorem dropDecodeError_ok_sub {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (d : DecodeDeps img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName +
        bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<prost::error::DecodeError> [local#1]") -
          ls_off% "<libsignal_protocol::state::prekey::PreKeyRecord>::deserialize"))
      ((dropDecodeErrorSpecX A).inImage img) := by
  have heq :
      (tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName +
        bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<prost::error::DecodeError> [local#1]") -
          ls_off% "<libsignal_protocol::state::prekey::PreKeyRecord>::deserialize") =
      (tripleRatchetProgAtExt img.base ext).fnAddr dropDecodeErrorName := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "<libsignal_protocol::state::prekey::PreKeyRecord>::deserialize"),
      (ls_lemma% fnOff "core::ptr::drop_glue::<prost::error::DecodeError> [local#1]")]
    bv_omega
  rw [heq]; exact d.dropDecodeError

theorem bytesMerge_ok_sub {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (d : DecodeDeps img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName +
        bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") -
          ls_off% "<libsignal_protocol::state::prekey::PreKeyRecord>::deserialize"))
      ((bytesMergeRawSpecX A).inImage img) := by
  have heq :
      (tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName +
        bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") -
          ls_off% "<libsignal_protocol::state::prekey::PreKeyRecord>::deserialize") =
      (tripleRatchetProgAtExt img.base ext).fnAddr bytesMergeName := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "<libsignal_protocol::state::prekey::PreKeyRecord>::deserialize"),
      (ls_lemma% fnOff "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]")]
    bv_omega
  rw [heq]; exact d.bytesMerge

/-- Minimal 4-field hook bundle used by `PreKeyRecord::deserialize` (drops unused `spqr_recv`
and cipher hooks from `Stage2ContractsX`). -/
structure PreKeyDeserializeHooks (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop where
  dealloc :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr deallocName)
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img)
  decode_varint_slow :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr varintSlowName)
      ((decodeVarintSlowSpecWithStack A (64 + 2 * extHookStack)).inImage img)
  decode_error_from :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodeErrorFromName)
      ((decodeErrorFromSpecWithStack A (2 * extHookStack)).inImage img)
  decode_error_push :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodeErrorPushName)
      ((decodeErrorPushExternSpecWithStack A (2 * extHookStack)).inImage img)

theorem PreKeyDeserializeHooks.of_stage2 {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8)}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {ext : String → Option (State → State)}
    (hC : Stage2ContractsX img C A encFn decFn ext) :
    PreKeyDeserializeHooks img A ext where
  dealloc := hC.dealloc
  decode_varint_slow := hC.decode_varint_slow
  decode_error_from := hC.decode_error_from
  decode_error_push := hC.decode_error_push

theorem dealloc_ok_sub {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : PreKeyDeserializeHooks img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName +
        bv% (ls_off% "__rustc::__rust_dealloc" -
          ls_off% "<libsignal_protocol::state::prekey::PreKeyRecord>::deserialize"))
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img) :=
  sub_ok_at_of_fnAddr hC.dealloc preKeyDeserializeName
    (num% (ls_off% "__rustc::__rust_dealloc" -
      ls_off% "<libsignal_protocol::state::prekey::PreKeyRecord>::deserialize"))

theorem varintSlow_ok_sub {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : PreKeyDeserializeHooks img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName +
        bv% (ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>" -
          ls_off% "<libsignal_protocol::state::prekey::PreKeyRecord>::deserialize"))
      ((decodeVarintSlowSpecWithStack A (64 + 2 * extHookStack)).inImage img) :=
  sub_ok_at_of_fnAddr hC.decode_varint_slow preKeyDeserializeName
    (num% (ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>" -
      ls_off% "<libsignal_protocol::state::prekey::PreKeyRecord>::deserialize"))

theorem decodeErrorFrom_ok_sub {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : PreKeyDeserializeHooks img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName +
        bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" -
          ls_off% "<libsignal_protocol::state::prekey::PreKeyRecord>::deserialize"))
      ((decodeErrorFromSpecWithStack A (2 * extHookStack)).inImage img) :=
  sub_ok_at_of_fnAddr hC.decode_error_from preKeyDeserializeName
    (num% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" -
      ls_off% "<libsignal_protocol::state::prekey::PreKeyRecord>::deserialize"))

theorem decodeErrorPush_ok_sub {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : PreKeyDeserializeHooks img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName +
        bv% (ls_off% "<prost::error::DecodeError>::push" -
          ls_off% "<libsignal_protocol::state::prekey::PreKeyRecord>::deserialize"))
      ((decodeErrorPushExternSpecWithStack A (2 * extHookStack)).inImage img) :=
  sub_ok_at_of_fnAddr hC.decode_error_push preKeyDeserializeName
    (num% (ls_off% "<prost::error::DecodeError>::push" -
      ls_off% "<libsignal_protocol::state::prekey::PreKeyRecord>::deserialize"))

/-! ## Pure codec suffix & model lemmas -/

theorem pkMergeField_suffix {m m' : PreKeyRecordStructure} {tag : ℕ} {wt : WireType}
    {bs rest : List (BitVec 8)} (h : PreKeyRecordStructure.mergeField m tag wt bs = some (m', rest)) :
    ∃ k, k ≤ bs.length ∧ rest = bs.drop k := by
  unfold PreKeyRecordStructure.mergeField skipUnknown at h
  rcases tag with _ | _ | _ | _ | tag4 <;>
    simp only [Option.map_eq_some_iff] at h
  · rcases h with ⟨r, hs, _, rfl⟩; exact skipField_suffix hs
  · rcases h with ⟨⟨v, r⟩, hm, _, rfl⟩; exact mergeUint32_suffix hm
  · rcases h with ⟨⟨v, r⟩, hm, _, rfl⟩; obtain ⟨k, hkl, hr, _⟩ := mergeBytes_suffix hm; exact ⟨k, hkl, hr⟩
  · rcases h with ⟨⟨v, r⟩, hm, _, rfl⟩; obtain ⟨k, hkl, hr, _⟩ := mergeBytes_suffix hm; exact ⟨k, hkl, hr⟩
  · rcases h with ⟨r, hs, _, rfl⟩; exact skipField_suffix hs

theorem pkDeserialize_eq_of_decodeLoop (bs : List (BitVec 8)) :
    PreKeyRecord.deserialize bs =
      match decodeFieldsLoop PreKeyRecordStructure.mergeField bs.length
          PreKeyRecordStructure.empty bs with
      | some m => .ok ⟨m⟩
      | none => .error .invalidProtobufEncoding := by
  unfold PreKeyRecord.deserialize PreKeyRecordStructure.decode
  cases decodeFieldsLoop PreKeyRecordStructure.mergeField bs.length PreKeyRecordStructure.empty bs <;> rfl

/-! ## Stack-slot layout for `PreKeyRecordStructure` at `sp' + 56` -/

structure PreKeyGhost where
  pub : VecPin
  priv : VecPin

structure PreKeyGhostCapOk (g : PreKeyGhost) (n : ℕ) : Prop where
  pub : BytesMergeCapOk g.pub.cap n
  priv : BytesMergeCapOk g.priv.cap n

theorem PreKeyGhostCapOk.mono {g : PreKeyGhost} {m n : ℕ}
    (hg : PreKeyGhostCapOk g n) (hle : m ≤ n) :
    PreKeyGhostCapOk g m :=
  ⟨bytesMergeCapOk_mono hg.pub hle, bytesMergeCapOk_mono hg.priv hle⟩

def preKeyStructAt (A : RustAlloc) (g : PreKeyGhost) (a : BitVec 64)
    (m : PreKeyRecordStructure) : SepProp :=
  vecU8At A a g.pub.cap g.pub.ptr m.publicKey ∗
    vecU8At A (a + 0x18#64) g.priv.cap g.priv.ptr m.privateKey ∗
    ((a + 0x30#64) ↦₃₂ m.id) ∗
    memRegion (a + 0x34#64) 4

def preKeyStructOf (A : RustAlloc) (a : BitVec 64) (m : PreKeyRecordStructure) : SepProp :=
  ∃∗ g : PreKeyGhost, preKeyStructAt A g a m

def preKeyStructLoopOf (A : RustAlloc) (a : BitVec 64) (n : ℕ)
    (m : PreKeyRecordStructure) : SepProp :=
  ∃∗ g : PreKeyGhost, ⌜PreKeyGhostCapOk g n⌝ ∗ preKeyStructAt A g a m

theorem preKeyStructAt_entails_of (A : RustAlloc) (g : PreKeyGhost) (a : BitVec 64)
    (m : PreKeyRecordStructure) :
    preKeyStructAt A g a m ⊢ preKeyStructOf A a m := by
  unfold preKeyStructOf
  exact Entails.sepExists_intro (P := fun g' => preKeyStructAt A g' a m) g

theorem preKeyStructAt_entails_loopOf (A : RustAlloc) (g : PreKeyGhost) (a : BitVec 64)
    (n : ℕ) (m : PreKeyRecordStructure) (hg : PreKeyGhostCapOk g n) :
    preKeyStructAt A g a m ⊢ preKeyStructLoopOf A a n m := by
  unfold preKeyStructLoopOf
  refine Entails.trans ?_
    (Entails.sepExists_intro (P := fun g' => ⌜PreKeyGhostCapOk g' n⌝ ∗ preKeyStructAt A g' a m) g)
  rw [pure_true_emp hg, emp_sepConj]
  exact Entails.refl _

theorem preKeyStructLoopOf_entails_of (A : RustAlloc) (a : BitVec 64) (n : ℕ)
    (m : PreKeyRecordStructure) :
    preKeyStructLoopOf A a n m ⊢ preKeyStructOf A a m :=
  Entails.sepExists_elim fun g =>
    Entails.pure_left fun _ => preKeyStructAt_entails_of A g a m

theorem preKeyStructLoopOf_mono (A : RustAlloc) (a : BitVec 64) {m n : ℕ}
    (st : PreKeyRecordStructure) (hle : m ≤ n) :
    preKeyStructLoopOf A a n st ⊢ preKeyStructLoopOf A a m st :=
  Entails.sepExists_elim fun g =>
    Entails.pure_left fun hg =>
      preKeyStructAt_entails_loopOf A g a m st (hg.mono hle)

theorem vecU8At_entails_vecU8 (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A a cap ptr bs ⊢ vecU8 A a bs := by
  unfold vecU8
  exact Entails.trans
    (Entails.sepExists_intro (P := fun p => vecU8At A a cap p bs) ptr)
    (Entails.sepExists_intro (P := fun c => ∃∗ p, vecU8At A a c p bs) cap)

theorem preKeyStructAt_entails_recordAt (A : RustAlloc) (g : PreKeyGhost) (a : BitVec 64)
    (m : PreKeyRecordStructure) :
    preKeyStructAt A g a m ⊢ preKeyRecordAt A a ⟨m⟩ := by
  unfold preKeyStructAt preKeyRecordAt
  exact sepConj_mono (vecU8At_entails_vecU8 A a g.pub.cap g.pub.ptr m.publicKey)
    (sepConj_mono_left (vecU8At_entails_vecU8 A (a + 0x18#64) g.priv.cap g.priv.ptr m.privateKey))

theorem preKeyStructAt_split_pub (A : RustAlloc) (g : PreKeyGhost) (sp' : BitVec 64)
    (m : PreKeyRecordStructure) :
    preKeyStructAt A g (sp' + 56#64) m =
      vecU8At A (sp' + 56#64) g.pub.cap g.pub.ptr m.publicKey ∗
        (vecU8At A (sp' + 80#64) g.priv.cap g.priv.ptr m.privateKey ∗
          ((sp' + 104#64) ↦₃₂ m.id) ∗ memRegion (sp' + 108#64) 4) := by
  unfold preKeyStructAt
  have h1 : sp' + 56#64 + 0x18#64 = sp' + 80#64 := by bv_omega
  have h2 : sp' + 56#64 + 0x30#64 = sp' + 104#64 := by bv_omega
  have h3 : sp' + 56#64 + 0x34#64 = sp' + 108#64 := by bv_omega
  rw [h1, h2, h3]

theorem preKeyStructAt_split_priv (A : RustAlloc) (g : PreKeyGhost) (sp' : BitVec 64)
    (m : PreKeyRecordStructure) :
    preKeyStructAt A g (sp' + 56#64) m =
      vecU8At A (sp' + 80#64) g.priv.cap g.priv.ptr m.privateKey ∗
        (vecU8At A (sp' + 56#64) g.pub.cap g.pub.ptr m.publicKey ∗
          ((sp' + 104#64) ↦₃₂ m.id) ∗ memRegion (sp' + 108#64) 4) := by
  rw [preKeyStructAt_split_pub]
  ac_rfl

theorem preKeyStructAt_split_id (A : RustAlloc) (g : PreKeyGhost) (sp' : BitVec 64)
    (m : PreKeyRecordStructure) :
    preKeyStructAt A g (sp' + 56#64) m =
      (((sp' + 104#64) ↦₃₂ m.id) ∗ memRegion (sp' + 108#64) 4) ∗
        (vecU8At A (sp' + 56#64) g.pub.cap g.pub.ptr m.publicKey ∗
          vecU8At A (sp' + 80#64) g.priv.cap g.priv.ptr m.privateKey) := by
  rw [preKeyStructAt_split_pub]
  ac_rfl

/-! ## Saved registers, loop registers, and epilogue state at `+0x224` -/

structure PkSavedRegs (s0 s : State) : Prop where
  x24 : s.readReg64 .x24 = s0.readReg64 .x24
  x25 : s.readReg64 .x25 = s0.readReg64 .x25
  x26 : s.readReg64 .x26 = s0.readReg64 .x26
  x27 : s.readReg64 .x27 = s0.readReg64 .x27
  x28 : s.readReg64 .x28 = s0.readReg64 .x28

theorem PkSavedRegs.refl (s0 : State) : PkSavedRegs s0 s0 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem PkSavedRegs.of_calleeSaved {s0 s1 s2 : State}
    (h1 : PkSavedRegs s0 s1) (hcs : CalleeSavedPreserved s1 s2) :
    PkSavedRegs s0 s2 where
  x24 := hcs.2.2.2.2.2.1.trans h1.x24
  x25 := hcs.2.2.2.2.2.2.1.trans h1.x25
  x26 := hcs.2.2.2.2.2.2.2.1.trans h1.x26
  x27 := hcs.2.2.2.2.2.2.2.2.1.trans h1.x27
  x28 := hcs.2.2.2.2.2.2.2.2.2.1.trans h1.x28

structure PkLoopRegs (s0 : State) (sp' x19 : BitVec 64) (s : State) : Prop where
  sp : s.sp = sp'
  x29 : s.readReg64 .x29 = sp' + 160#64
  x22 : s.readReg64 .x22 = 0x8000000000000002#64
  x20 : s.readReg64 .x20 = sp' + 56#64
  x19_eq : s.readReg64 .x19 = x19
  saved : PkSavedRegs s0 s

theorem PkLoopRegs.of_calleeSaved {s0 : State} {sp' x19 : BitVec 64} {s1 s2 : State}
    (h1 : PkLoopRegs s0 sp' x19 s1) (hsp : s2.sp = s1.sp)
    (hcs : CalleeSavedPreserved s1 s2) :
    PkLoopRegs s0 sp' x19 s2 where
  sp := hsp.trans h1.sp
  x29 := hcs.2.2.2.2.2.2.2.2.2.2.1.trans h1.x29
  x22 := hcs.2.2.2.1.trans h1.x22
  x20 := hcs.2.1.trans h1.x20
  x19_eq := hcs.1.trans h1.x19_eq
  saved := PkSavedRegs.of_calleeSaved h1.saved hcs

structure PkEpilogueState (img : Obj.Image) (s0 : State) (sp' : BitVec 64) (s : State) : Prop where
  sp : s.sp = sp'
  sp_align : s.spAligned = true
  frozen : img.FrozenLoaded s
  sym : s.symtab = img.symtab
  trace : s.trace = s0.trace
  saved : PkSavedRegs s0 s

theorem PkEpilogueState.of_steps {img : Obj.Image} {s0 : State} {sp' : BitVec 64} {s : State}
    (hfz : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hsp : s.sp = sp') (_hsp0 : sp' = sp') (hal : s.spAligned = true)
    (htr : s.trace = s0.trace) (hsaved : PkSavedRegs s0 s) :
    PkEpilogueState img s0 sp' s :=
  ⟨hsp, hal, hfz, hsym, htr, hsaved⟩

def pkCalleeSavedAt (sp' : BitVec 64) (s0 : State) : SepProp :=
  ((sp' + 160#64) ↦₆₄ s0.readReg64 .x29) ∗
    ((sp' + 168#64) ↦₆₄ s0.readReg64 .x30) ∗
    ((sp' + 176#64) ↦₆₄ s0.readReg64 .x23) ∗
    ((sp' + 192#64) ↦₆₄ s0.readReg64 .x22) ∗
    ((sp' + 200#64) ↦₆₄ s0.readReg64 .x21) ∗
    ((sp' + 208#64) ↦₆₄ s0.readReg64 .x20) ∗
    ((sp' + 216#64) ↦₆₄ s0.readReg64 .x19)

def pkEpilogueMem (A : RustAlloc) (sp' x19 ptr : BitVec 64) (bs : List (BitVec 8))
    (out : Except SignalProtocolError PreKeyRecord) : SepProp :=
  memRegion sp' 160 ∗
    ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
    preKeyResultAt A x19 out ∗
    (ptr ↦ₛ bs) ∗
    A.pool ∗
    stackAt sp' (skipFieldStackX 100)

def pkEpiloguePost (img : Obj.Image) (A : RustAlloc) (s0 : State)
    (sp' x19 ptr : BitVec 64) (bs : List (BitVec 8))
    (out : Except SignalProtocolError PreKeyRecord) : State → SepProp → Prop :=
  fun sf Pf => PkEpilogueState img s0 sp' sf ∧ (Pf ⊢ pkEpilogueMem A sp' x19 ptr bs out)

theorem pkEpiloguePost_append_prefix (img : Obj.Image) (A : RustAlloc) (s0 : State)
    (sp' x19 ptr : BitVec 64) (bs : List (BitVec 8)) (k : ℕ) (hk : k ≤ bs.length)
    (out : Except SignalProtocolError PreKeyRecord)
    (sf : State) (Pf : SepProp)
    (h : pkEpiloguePost img A s0 sp' x19 (ptr + BitVec.ofNat 64 k) (bs.drop k) out sf Pf) :
    pkEpiloguePost img A s0 sp' x19 ptr bs out sf (Pf ∗ (ptr ↦ₛ bs.take k)) := by
  rcases h with ⟨hst, hent⟩
  refine ⟨hst, ?_⟩
  refine Entails.trans (sepConj_mono_left hent) ?_
  unfold pkEpilogueMem
  rw [← pointsToBytes_take_drop ptr bs k hk]
  apply entails_of_eq
  ac_rfl

/-! ## Scratch memory splitting helpers at `sp' + 112` (`x29 - 48`) -/

theorem pkMemRegion48_split24 (sp' : BitVec 64) :
    memRegion (sp' + 112#64) 48 =
      memRegion (sp' + 112#64) 24 ∗ memRegion (sp' + 136#64) 24 := by
  have hs := ProofLib.memRegion_split (sp' + 112#64) 24 24 (by decide)
  have ha : sp' + 112#64 + 24#64 = sp' + 136#64 := by bv_omega
  rw [ha] at hs
  exact hs

theorem pkMemRegion48_split8 (sp' : BitVec 64) :
    memRegion (sp' + 112#64) 48 =
      memRegion (sp' + 112#64) 8 ∗ memRegion (sp' + 120#64) 40 := by
  have hs := ProofLib.memRegion_split (sp' + 112#64) 8 40 (by decide)
  have ha : sp' + 112#64 + 8#64 = sp' + 120#64 := by bv_omega
  rw [ha] at hs
  exact hs

theorem pkMemRegion48_split_112_120_128 (sp' : BitVec 64) :
    memRegion (sp' + 112#64) 48 =
      (∃∗ w0 : BitVec 64, (sp' + 112#64) ↦₆₄ w0) ∗
      (∃∗ w1 : BitVec 64, (sp' + 120#64) ↦₆₄ w1) ∗
      memRegion (sp' + 128#64) 32 := by
  rw [ProofLib.memRegion_split (sp' + 112#64) 8 40 (by decide),
    ProofLib.memRegion_split (sp' + 112#64 + 8#64) 8 32 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  have ha1 : sp' + 112#64 + 8#64 = sp' + 120#64 := by bv_omega
  have ha2 : sp' + 120#64 + 8#64 = sp' + 128#64 := by bv_omega
  rw [ha1, ha2]

theorem pkScratch24_ok_entails_memRegion48 (sp' v w : BitVec 64) :
    ((sp' + 112#64) ↦₃₂ 0#32) ∗ ((sp' + 116#64) ↦₃₂ 0#32) ∗
      ((sp' + 120#64) ↦₆₄ v) ∗ ((sp' + 128#64) ↦₆₄ w) ∗
      memRegion (sp' + 136#64) 24 ⊢
      memRegion (sp' + 112#64) 48 := by
  have h0 : ((sp' + 112#64) ↦₃₂ 0#32) ∗ ((sp' + 116#64) ↦₃₂ 0#32) =
      ((sp' + 112#64) ↦₆₄ 0#64) := by
    have hs := (pointsTo64_zero_split32 (sp' + 112#64)).symm
    have ha : sp' + 112#64 + 4#64 = sp' + 116#64 := by bv_omega
    rw [ha] at hs; exact hs
  rw [← sepConj_assoc, h0, pkMemRegion48_split24 sp',
    ProofLib.memRegion_split (sp' + 112#64) 8 16 (by decide),
    ProofLib.memRegion_split (sp' + 112#64 + 8#64) 8 8 (by decide)]
  have ha1 : sp' + 112#64 + 8#64 = sp' + 120#64 := by bv_omega
  have ha2 : sp' + 120#64 + 8#64 = sp' + 128#64 := by bv_omega
  rw [ha1, ha2]
  refine Entails.trans ?_
    (sepConj_mono
      (sepConj_mono (pointsTo64_entails_memRegion (sp' + 112#64) 0#64)
        (sepConj_mono (pointsTo64_entails_memRegion (sp' + 120#64) v)
          (pointsTo64_entails_memRegion (sp' + 128#64) w)))
      (Entails.refl _))
  apply entails_of_eq; ac_rfl

theorem pkScratch24_err_entails_memRegion48 (sp' e : BitVec 64) :
    ((sp' + 112#64) ↦₃₂ 1#32) ∗ ((sp' + 116#64) ↦₃₂ 0#32) ∗
      ((sp' + 120#64) ↦₆₄ e) ∗ memRegion (sp' + 128#64) 8 ∗
      memRegion (sp' + 136#64) 24 ⊢
      memRegion (sp' + 112#64) 48 := by
  have h1 : ((sp' + 112#64) ↦₃₂ 1#32) ∗ ((sp' + 116#64) ↦₃₂ 0#32) =
      ((sp' + 112#64) ↦₆₄ 1#64) := by
    have hs := (pointsTo64_one_split32 (sp' + 112#64)).symm
    have ha : sp' + 112#64 + 4#64 = sp' + 116#64 := by bv_omega
    rw [ha] at hs; exact hs
  rw [← sepConj_assoc, h1, pkMemRegion48_split24 sp',
    ProofLib.memRegion_split (sp' + 112#64) 8 16 (by decide),
    ProofLib.memRegion_split (sp' + 112#64 + 8#64) 8 8 (by decide)]
  have ha1 : sp' + 112#64 + 8#64 = sp' + 120#64 := by bv_omega
  have ha2 : sp' + 120#64 + 8#64 = sp' + 128#64 := by bv_omega
  rw [ha1, ha2]
  refine Entails.trans ?_
    (sepConj_mono
      (sepConj_mono (pointsTo64_entails_memRegion (sp' + 112#64) 1#64)
        (sepConj_mono (pointsTo64_entails_memRegion (sp' + 120#64) e)
          (Entails.refl _)))
      (Entails.refl _))
  apply entails_of_eq; ac_rfl

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem status_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).status = s.status := by cases s; rfl

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem status_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).status = s.status := by cases s; rfl

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem trace_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).trace = s.trace := by cases s; rfl

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem trace_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).trace = s.trace := by cases s; rfl

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem sp_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem sp_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).sp = s.sp := by cases s; rfl

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem pc_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).pc = pc := by cases s; rfl

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem pc_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).pc = s.pc := by cases s; rfl

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem readReg64_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem readReg64_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem readReg32_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem readReg32_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem readReg_setPC_pre (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem readReg_setMem_pre (s : State) (m : Memory) (w : RegWidth) (r : Reg) :
    (s.setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

/-! ## Relocatable `[LibsignalPlacement]` Callee Wrappers & Epilogue State (Block `65`) -/

section Placed

open CryptoVerification.RecordCodecs.Placed

theorem pk_varintSlice_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (d : PortDepsPlaced A H) :
    subroutine_ok (lsProg_65 H) (lsmpl.base 76)
      (withLsCodeRoLoaded lsmpl (decodeVarintSliceSpecX A)) :=
  ls_subroutine_ok_lscro_of_cl (callerProg := lsProg_65 H) d.varintSlice

theorem pk_int32Merge_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (d : PortDepsPlaced A H) :
    subroutine_ok (lsProg_65 H) (lsmpl.base 8)
      (withLsCodeRoLoaded lsmpl (int32MergeSpecX A)) :=
  ls_subroutine_ok_lscro_of_cl (callerProg := lsProg_65 H) d.int32Merge

theorem pk_skipField_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (d : PortDepsPlaced A H) :
    subroutine_ok (lsProg_65 H) (lsmpl.base 1)
      (withLsCodeRoLoaded lsmpl (skipFieldSpecX A)) :=
  ls_subroutine_ok_lscro_of_cl (callerProg := lsProg_65 H) d.skipField

theorem pk_dropDecodeError_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (d : PortDepsPlaced A H) :
    subroutine_ok (lsProg_65 H) (lsmpl.base 4)
      (withLsCodeRoLoaded lsmpl (dropDecodeErrorSpecX A)) :=
  ls_subroutine_ok_lscro_of_plain (callerProg := lsProg_65 H) d.dropDecodeError

theorem pk_bytesMerge_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (d : PortDepsPlaced A H) :
    subroutine_ok (lsProg_65 H) (lsmpl.base 7)
      (withLsCodeRoLoaded lsmpl (bytesMergeRawSpecX A)) :=
  ls_subroutine_ok_lscro_of_block (callerProg := lsProg_65 H) d.bytesMerge

theorem pk_varintSlow_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (d : PortDepsPlaced A H) :
    subroutine_ok (lsProg_65 H) (lsmpl.base 293)
      (withLsCodeRoLoaded lsmpl (decodeVarintSlowSpecWithStack A (64 + 2 * extHookStack))) :=
  ls_subroutine_ok_lscro_of_cl (callerProg := lsProg_65 H) d.varintSlow

theorem pk_decodeErrorFrom_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (d : PortDepsPlaced A H) :
    subroutine_ok (lsProg_65 H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromSpecWithStack A (2 * extHookStack))) :=
  ls_subroutine_ok_lscro_of_plain (callerProg := lsProg_65 H) d.decodeErrorFrom

theorem pk_decodeErrorPush_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (d : PortDepsPlaced A H) :
    subroutine_ok (lsProg_65 H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushExternSpecWithStack A (2 * extHookStack))) :=
  ls_subroutine_ok_lscro_of_cl (callerProg := lsProg_65 H) d.decodeErrorPush

theorem pk_dealloc_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (d : PortDepsPlaced A H) :
    subroutine_ok (lsProg_65 H) (lsρ lsRustDeallocSym)
      (withLsCodeRoLoaded lsmpl (rustDeallocExternSpecWithStack A extHookStack)) :=
  ls_dealloc_lscro_ok (callerProg := lsProg_65 H) d.dealloc

theorem sepWPp_call_noPanic_lscro {α : Type} {prog : Program} {pl : Obj.MultiPlacement}
    {ret entry ret_pc : BitVec 64} {s0 s : State} {P T F : SepProp} {φ : Prop}
    {Q : State → SepProp → Prop} {spec : Spec α} (x : α)
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded pl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded pl s.mem)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F := by sep_focus)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → LibsignalCodeRoLoaded pl sf.mem →
      CalleeSavedPreserved s sf →
      Wire.SepWPp prog ret sf (spec.post x s sf ∗ F) Q (Wire.tryFromQp s0))
    (hexit : ∀ sf code, spec.onExit x code s sf = ⌜False⌝ := by intros; rfl)
    (hpan_eq : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intros; rfl)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    Wire.SepWPp prog ret s P Q (Wire.tryFromQp s0) :=
  sepWPp_call_lscro x hcall hpc hrun hsp hcrl hlr htr hspec hφ hP hnext hexit
    (fun sf => by rw [hpan_eq sf, ← sepConj_emp ⌜False⌝]; exact Entails.pure_left False.elim) hoom_eq

structure PkEpilogueStatePlaced [LibsignalPlacement] (s0 : State) (sp' : BitVec 64) (s : State) : Prop where
  sp : s.sp = sp'
  sp_align : s.spAligned = true
  crl : LibsignalCodeRoLoaded lsmpl s.mem
  trace : s.trace = s0.trace
  saved : PkSavedRegs s0 s

def pkEpiloguePostPlaced [LibsignalPlacement] (A : RustAlloc) (s0 : State)
    (sp' x19 ptr : BitVec 64) (bs : List (BitVec 8))
    (out : Except SignalProtocolError PreKeyRecord) : State → SepProp → Prop :=
  fun sf Pf => PkEpilogueStatePlaced s0 sp' sf ∧ (Pf ⊢ pkEpilogueMem A sp' x19 ptr bs out)

theorem pkEpiloguePostPlaced_append_prefix [LibsignalPlacement] (A : RustAlloc) (s0 : State)
    (sp' x19 ptr : BitVec 64) (bs : List (BitVec 8)) (k : ℕ) (hk : k ≤ bs.length)
    (out : Except SignalProtocolError PreKeyRecord)
    (sf : State) (Pf : SepProp)
    (h : pkEpiloguePostPlaced A s0 sp' x19 (ptr + BitVec.ofNat 64 k) (bs.drop k) out sf Pf) :
    pkEpiloguePostPlaced A s0 sp' x19 ptr bs out sf (Pf ∗ (ptr ↦ₛ bs.take k)) := by
  rcases h with ⟨hst, hent⟩
  refine ⟨hst, ?_⟩
  refine Entails.trans (sepConj_mono_left hent) ?_
  unfold pkEpilogueMem
  rw [← pointsToBytes_take_drop ptr bs k hk]
  apply entails_of_eq
  ac_rfl

end Placed

end CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers

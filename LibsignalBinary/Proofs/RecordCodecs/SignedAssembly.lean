/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.RecordCodecsCodeSymD
public import LibsignalBinary.Proofs.RecordCodecs.SignedDeps
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.RecordCodecs.DecodeKyberPreKey
import LibsignalBinary.Proofs.RecordCodecs.DecodeKyberPreKey.Fetches
import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.PublicKeyTryFrom
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostRkSome
import ProofLib.SepLogic.WPp

/-!
# Signed and Kyber Pre-Key Record Decoder Assembly

Connects `<SignedPreKeyRecordStructure as Message>::decode::<&[u8]>` and
`signal_session::stores::decode_kyber_pre_key` to top-level `Program.ofImage`, X-form
(`AllocContractsX`), and relocatable `[LibsignalPlacement]` (Block `595`) specifications:
* `kyberDeserialize_eq`, `signedDeserialize_eq`: relate the record deserializers to
  `SignedPreKeyRecordStructure.decode`.
* `decodeSignedPreKeySpec_eq`, `decodeSignedPreKeyPlacedSpec_eq`: establish that the signed and
  Kyber pre-key wrapper contracts coincide (LLVM shares one compiled function for both).
* `decodeKyberPreKey_run`, `decodeSignedPreKey_run`, `decodeKyberPreKey_placed_ok`,
  `decodeSignedPreKey_placed_ok`: lift the proved wrapper to image and block-placed entrypoints.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.RecordCodecsBinary.SignedAssembly

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.RecordCodecs

theorem kyberDeserialize_eq (bs : List (BitVec 8)) :
    KyberPreKeyRecord.deserialize bs =
      match SignedPreKeyRecordStructure.decode bs with
      | none => .error .invalidProtobufEncoding
      | some m => .ok ⟨m⟩ := by
  unfold KyberPreKeyRecord.deserialize
  cases SignedPreKeyRecordStructure.decode bs <;> rfl

theorem signedDeserialize_eq (bs : List (BitVec 8)) :
    SignedPreKeyRecord.deserialize bs =
      match SignedPreKeyRecordStructure.decode bs with
      | none => .error .invalidProtobufEncoding
      | some m => .ok ⟨m⟩ := by
  unfold SignedPreKeyRecord.deserialize
  cases SignedPreKeyRecordStructure.decode bs <;> rfl

/-- Both result predicates hold the same bytes for the same input. -/
theorem signedPreKeyResultAt_deserialize (A : RustAlloc) (r : BitVec 64) (bs : List (BitVec 8)) :
    signedPreKeyResultAt A r (SignedPreKeyRecord.deserialize bs) =
      kyberPreKeyResultAt A r (KyberPreKeyRecord.deserialize bs) := by
  rw [signedDeserialize_eq, kyberDeserialize_eq]
  cases SignedPreKeyRecordStructure.decode bs <;> rfl

/-- The signed and the Kyber binding specs are the same spec. -/
theorem decodeSignedPreKeySpec_eq (A : RustAlloc) (img : Obj.Image) :
    decodeSignedPreKeySpec A img = decodeKyberPreKeySpec A img := by
  simp only [decodeSignedPreKeySpec, decodeKyberPreKeySpec, signedPreKeyResultAt_deserialize]

/-- `decode_kyber_pre_key` in the loaded image `img` (any base): `decodeKyberPreKeySpec`. -/
theorem decodeKyberPreKey_run {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hH : SignedHooks img.base A ext) (d : SignedPortDeps img A ext) :
    subroutine_ok (Program.ofImage img (Rust.withPanics ext))
      (entryOf img decodeKyberPreKeyName) (decodeKyberPreKeySpec A img) :=
  root_of_tripleRatchetProgAtExt himg
    (DecodeKyberPreKey.decodeKyberPreKey_ok_of_decode
      (SignedPreKeyDecode.signedDecode_ok_of_deps hH d (Wire.base_aligned himg))
      d.dropDecodeError3 (Wire.base_aligned himg))

/-- `decode_kyber_pre_key` as `decode_signed_pre_key` (LLVM keeps one function for both) in
the loaded image `img` (any base): `decodeSignedPreKeySpec`. -/
theorem decodeSignedPreKey_run {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hH : SignedHooks img.base A ext) (d : SignedPortDeps img A ext) :
    subroutine_ok (Program.ofImage img (Rust.withPanics ext))
      (entryOf img decodeKyberPreKeyName) (decodeSignedPreKeySpec A img) := by
  rw [decodeSignedPreKeySpec_eq]
  exact decodeKyberPreKey_run himg hH d

/-! ## X-form (`AllocContractsX` / `SignedHooksX` / `SignedPortDepsX`) wrapper & entrypoints -/

section XForm

open ProofLib.ProgramReflection
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.RecordCodecsBinary.DecodeKyberPreKey.Helpers

attribute [local irreducible] Program.fetch Program.externAt?

private theorem kpkStack_smallRoot_split_x (sp : BitVec 64) :
    stackAt sp smallRootStack =
      stackAt (sp - 128#64) signedDecodeStackX ∗
        memRegion (sp - 128#64 - BitVec.ofNat 64 kpkSubStack) (kpkSubStack - signedDecodeStackX) ∗
        memRegion (sp - 128#64) 8 ∗
        memRegion (sp - 128#64 + 8#64) 88 ∗
        memRegion (sp - 128#64 + 96#64) 32 := by
  have h1 := Wire.stackAt_sub_split sp 128 smallRootStack
  have h2 : memRegion (sp - BitVec.ofNat 64 smallRootStack) kpkSubStack =
      stackAt (sp - 128#64) kpkSubStack := by
    unfold stackAt
    have ha : sp - BitVec.ofNat 64 smallRootStack =
        sp - 128#64 - BitVec.ofNat 64 kpkSubStack := by
      change sp - 65536#64 = sp - 128#64 - 65408#64
      bv_omega
    rw [ha]
  have h3 := Wire.stackAt_sub_split (sp - 128#64) signedDecodeStackX kpkSubStack
  have h4 : stackAt sp 128 =
      memRegion (sp - 128#64) 8 ∗
        memRegion (sp - 128#64 + 8#64) 88 ∗
        memRegion (sp - 128#64 + 96#64) 32 := by
    unfold stackAt
    rw [show (128 : Nat) = 8 + (88 + 32) by decide,
      ProofLib.memRegion_split (sp - 128#64) 8 120 (by decide),
      ProofLib.memRegion_split (sp - 128#64 + 8#64) 88 32 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [h1, h2, h3, h4]
  ac_rfl

private theorem kpkStack_exit_pack_x (sp c0 c1 c2 c3 : BitVec 64) :
    memRegion (sp - 128#64) 8 ∗
      memRegion (sp - 128#64 + 8#64) 88 ∗
      ((sp - 128#64 + 96#64) ↦₆₄ c0) ∗
      ((sp - 128#64 + 104#64) ↦₆₄ c1) ∗
      ((sp - 128#64 + 112#64) ↦₆₄ c2) ∗
      ((sp - 128#64 + 120#64) ↦₆₄ c3) ∗
      stackAt (sp - 128#64) signedDecodeStackX ∗
      memRegion (sp - 128#64 - BitVec.ofNat 64 kpkSubStack) (kpkSubStack - signedDecodeStackX) ⊢
      stackAt sp smallRootStack := by
  rw [kpkStack_smallRoot_split_x sp]
  have hf32 := kpkFrame32_pack (sp - 128#64) c0 c1 c2 c3
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hf32))))
  apply entails_of_eq; ac_rfl

private theorem kpkDecodeStack_drop_split_x (sp' : BitVec 64) :
    stackAt sp' signedDecodeStackX =
      stackAt sp' Prost.dropDecodeErrorStackX ∗
        memRegion (sp' - BitVec.ofNat 64 signedDecodeStackX)
          (signedDecodeStackX - Prost.dropDecodeErrorStackX) := by
  have hs := Wire.stackAt_sub_split sp' Prost.dropDecodeErrorStackX signedDecodeStackX
  rw [hs]
  ac_rfl

private theorem okExit_pack_x (A : RustAlloc) (sp ret bytesA : BitVec 64) (bytes : List (BitVec 8))
    (pubCap pubPtr privCap privPtr sigCap sigPtr c0 c1 c2 c3 : BitVec 64) (pad32 : BitVec 32)
    (m : SignedPreKeyRecordStructure) :
    words88Ret ret pubCap pubPtr (BitVec.ofNat 64 m.publicKey.length)
        privCap privPtr (BitVec.ofNat 64 m.privateKey.length)
        sigCap sigPtr (BitVec.ofNat 64 m.signature.length)
        m.timestamp (pad32 ++ m.id) ∗
      signedPreKeyBufs A pubCap pubPtr privCap privPtr sigCap sigPtr m ∗
      (bytesA ↦ₛ bytes) ∗
      (memRegion (sp - 128#64) 8 ∗
        words88Sp (sp - 128#64) pubCap pubPtr (BitVec.ofNat 64 m.publicKey.length)
          privCap privPtr (BitVec.ofNat 64 m.privateKey.length)
          sigCap sigPtr (BitVec.ofNat 64 m.signature.length)
          m.timestamp (pad32 ++ m.id) ∗
        ((sp - 128#64 + 96#64) ↦₆₄ c0) ∗
        ((sp - 128#64 + 104#64) ↦₆₄ c1) ∗
        ((sp - 128#64 + 112#64) ↦₆₄ c2) ∗
        ((sp - 128#64 + 120#64) ↦₆₄ c3) ∗
        stackAt (sp - 128#64) signedDecodeStackX ∗
        memRegion (sp - 128#64 - BitVec.ofNat 64 kpkSubStack) (kpkSubStack - signedDecodeStackX)) ∗
      A.pool ⊢
      kyberPreKeyResultAt A ret (.ok ⟨m⟩) ∗
        (bytesA ↦ₛ bytes) ∗
        stackAt sp smallRootStack ∗
        A.pool := by
  have hsp88 := words88Sp_pack (sp - 128#64) pubCap pubPtr (BitVec.ofNat 64 m.publicKey.length)
    privCap privPtr (BitVec.ofNat 64 m.privateKey.length)
    sigCap sigPtr (BitVec.ofNat 64 m.signature.length) m.timestamp (pad32 ++ m.id)
  have hret := signedPreKeyStructAt_ret_pack A ret pubCap pubPtr privCap privPtr sigCap sigPtr pad32 m
  have hstk := kpkStack_exit_pack_x sp c0 c1 c2 c3
  have hstk' :
      memRegion (sp - 128#64) 8 ∗
        words88Sp (sp - 128#64) pubCap pubPtr (BitVec.ofNat 64 m.publicKey.length)
          privCap privPtr (BitVec.ofNat 64 m.privateKey.length)
          sigCap sigPtr (BitVec.ofNat 64 m.signature.length)
          m.timestamp (pad32 ++ m.id) ∗
        ((sp - 128#64 + 96#64) ↦₆₄ c0) ∗
        ((sp - 128#64 + 104#64) ↦₆₄ c1) ∗
        ((sp - 128#64 + 112#64) ↦₆₄ c2) ∗
        ((sp - 128#64 + 120#64) ↦₆₄ c3) ∗
        stackAt (sp - 128#64) signedDecodeStackX ∗
        memRegion (sp - 128#64 - BitVec.ofNat 64 kpkSubStack) (kpkSubStack - signedDecodeStackX) ⊢
      stackAt sp smallRootStack :=
    Entails.trans (sepConj_mono_right (sepConj_mono_left hsp88)) hstk
  rw [← sepConj_assoc (words88Ret ret pubCap pubPtr (BitVec.ofNat 64 m.publicKey.length)
      privCap privPtr (BitVec.ofNat 64 m.privateKey.length)
      sigCap sigPtr (BitVec.ofNat 64 m.signature.length)
      m.timestamp (pad32 ++ m.id))]
  exact sepConj_mono hret (sepConj_mono_right (sepConj_mono_left hstk'))

private theorem errExit_pack_x (A : RustAlloc) (sp ret bytesA e c0 c1 c2 c3 : BitVec 64)
    (bytes : List (BitVec 8)) :
    ((ret ↦₆₄ errTag) ∗ ((ret + 8#64) ↦₆₄ 0x8000000000000002#64) ∗ memRegion (ret + 16#64) 72) ∗
      (bytesA ↦ₛ bytes) ∗
      (memRegion (sp - 128#64) 8 ∗
        (((sp - 128#64 + 8#64) ↦₆₄ errTag) ∗ ((sp - 128#64 + 16#64) ↦₆₄ e) ∗
          memRegion (sp - 128#64 + 24#64) 72) ∗
        ((sp - 128#64 + 96#64) ↦₆₄ c0) ∗
        ((sp - 128#64 + 104#64) ↦₆₄ c1) ∗
        ((sp - 128#64 + 112#64) ↦₆₄ c2) ∗
        ((sp - 128#64 + 120#64) ↦₆₄ c3) ∗
        stackAt (sp - 128#64) signedDecodeStackX ∗
        memRegion (sp - 128#64 - BitVec.ofNat 64 kpkSubStack) (kpkSubStack - signedDecodeStackX)) ∗
      A.pool ⊢
      kyberPreKeyResultAt A ret (.error .invalidProtobufEncoding) ∗
        (bytesA ↦ₛ bytes) ∗
        stackAt sp smallRootStack ∗
        A.pool := by
  have hsp88 := errLocal88_pack (sp - 128#64) e
  have hret := kyberErr88_pack A ret
  have hstk := kpkStack_exit_pack_x sp c0 c1 c2 c3
  have hstk' :
      memRegion (sp - 128#64) 8 ∗
        (((sp - 128#64 + 8#64) ↦₆₄ errTag) ∗ ((sp - 128#64 + 16#64) ↦₆₄ e) ∗
          memRegion (sp - 128#64 + 24#64) 72) ∗
        ((sp - 128#64 + 96#64) ↦₆₄ c0) ∗
        ((sp - 128#64 + 104#64) ↦₆₄ c1) ∗
        ((sp - 128#64 + 112#64) ↦₆₄ c2) ∗
        ((sp - 128#64 + 120#64) ↦₆₄ c3) ∗
        stackAt (sp - 128#64) signedDecodeStackX ∗
        memRegion (sp - 128#64 - BitVec.ofNat 64 kpkSubStack) (kpkSubStack - signedDecodeStackX) ⊢
      stackAt sp smallRootStack :=
    Entails.trans (sepConj_mono_right (sepConj_mono_left hsp88)) hstk
  exact sepConj_mono hret (sepConj_mono_right (sepConj_mono_left hstk'))

private theorem signedDecode_call_ok_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hDecode : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName) (signedDecodeSpecX A img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodeKyberPreKeyName + signedDecodeRelOff)
      (signedDecodeSpecX A img) := by
  have heq :
      (tripleRatchetProgAtExt img.base ext).fnAddr decodeKyberPreKeyName + signedDecodeRelOff =
      (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName := by
    dsimp only [signedDecodeRelOff]
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "libsignal_cli::stores::decode_kyber_pre_key"),
      (ls_lemma% fnOff "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>")]
    bv_omega
  rw [heq]; exact hDecode

private theorem dropDecodeError3_call_ok_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hDrop : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dropDecodeError3Name)
      ((Prost.dropDecodeErrorSpecX A).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodeKyberPreKeyName + dropDecodeError3RelOff)
      ((Prost.dropDecodeErrorSpecX A).inImage img) := by
  have heq :
      (tripleRatchetProgAtExt img.base ext).fnAddr decodeKyberPreKeyName + dropDecodeError3RelOff =
      (tripleRatchetProgAtExt img.base ext).fnAddr dropDecodeError3Name := by
    dsimp only [dropDecodeError3RelOff]
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "libsignal_cli::stores::decode_kyber_pre_key"),
      (ls_lemma% fnOff "core::ptr::drop_glue::<prost::error::DecodeError> [local#3]")]
    bv_omega
  rw [heq]; exact hDrop

private theorem epilogue_ok_wp_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {x : DecodeGhost} {s0 s : State} {m : SignedPreKeyRecordStructure}
    (hdec : SignedPreKeyRecordStructure.decode x.bytes = some m)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decodeKyberPreKeyName + bv% (28))
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = s0.sp - 128#64)
    (hsp : s.spAligned = true)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hsaved : KpkSavedRegs s0 s) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      (s0.readReg64 .x30) s
      (signedPreKeyStructAt A (s0.sp - 128#64 + 8#64) m ∗
        memRegion x.ret 88 ∗
        memRegion (s0.sp - 128#64) 8 ∗
        ((s0.sp - 128#64 + 96#64) ↦₆₄ s0.readReg64 .x29) ∗
        ((s0.sp - 128#64 + 104#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((s0.sp - 128#64 + 112#64) ↦₆₄ s0.readReg64 .x20) ∗
        ((s0.sp - 128#64 + 120#64) ↦₆₄ s0.readReg64 .x19) ∗
        (x.bytesA ↦ₛ x.bytes) ∗
        stackAt (s0.sp - 128#64) signedDecodeStackX ∗
        memRegion (s0.sp - 128#64 - BitVec.ofNat 64 kpkSubStack) (kpkSubStack - signedDecodeStackX) ∗
        A.pool)
      (kpkPost img A x s0)
      (tryFromQp s0) := by
  set sp' := s0.sp - 128#64
  refine Wire.SepWPp.mono_pre
    (sepConj_mono (signedPreKeyStructAt_sp8_unpack A sp' m)
      (sepConj_mono_left (memRegion88_unpack x.ret))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Wire.SepWPp.exists_pre fun r0 => Wire.SepWPp.exists_pre fun r1 =>
    Wire.SepWPp.exists_pre fun r2 => Wire.SepWPp.exists_pre fun r3 =>
    Wire.SepWPp.exists_pre fun r4 => Wire.SepWPp.exists_pre fun r5 =>
    Wire.SepWPp.exists_pre fun r6 => Wire.SepWPp.exists_pre fun r7 =>
    Wire.SepWPp.exists_pre fun r8 => Wire.SepWPp.exists_pre fun r9 =>
    Wire.SepWPp.exists_pre fun r10 =>
    Wire.SepWPp.exists_pre fun pubCap => Wire.SepWPp.exists_pre fun pubPtr =>
    Wire.SepWPp.exists_pre fun privCap => Wire.SepWPp.exists_pre fun privPtr =>
    Wire.SepWPp.exists_pre fun sigCap => Wire.SepWPp.exists_pre fun sigPtr =>
    Wire.SepWPp.exists_pre fun pad32 => ?_
  rw [sepConj_assoc]
  refine Wire.SepWPp.pure_pre fun hpub_lt => ?_
  have hc := cap_add1_eq_of_lt hpub_lt
  unfold words88Sp words88Ret
  simp only [sepConj_assoc]
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.DecodeKyberPreKey.Helpers.kpkDec
    img.base (Rust.withPanics ext) kpkDec_fnOff kpkDecOff 28 68
  dsimp only [tripleRatchetProgAtExt, decodeKyberPreKeyName] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    "libsignal_cli::stores::decode_kyber_pre_key" = entry
  examples_hide_fetches
  have h19 : s.readReg64 (Reg.gpr 19#5) = x.ret := hx19
  refine Wire.SepWPp.of_sepWP_end hF hsym ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro _ _
  have hsp_ret : s0.sp - 128#64 + 128#64 = s0.sp := by bv_omega
  refine ⟨by simp [sp', hsp_ret, arm64_norm], fun hv => ?_, ?_⟩
  · refine ⟨by simp [arm64_norm],
      by simp [arm64_norm],
      by simpa [arm64_norm] using hsaved.x21,
      by simpa [arm64_norm] using hsaved.x22,
      by simpa [arm64_norm] using hsaved.x23,
      by simpa [arm64_norm] using hsaved.x24,
      by simpa [arm64_norm] using hsaved.x25,
      by simpa [arm64_norm] using hsaved.x26,
      by simpa [arm64_norm] using hsaved.x27,
      by simpa [arm64_norm] using hsaved.x28,
      by simp [arm64_norm],
      hv⟩
  · dsimp only [decodeKyberPreKeySpec, Spec.inImage]
    rw [kyberDeserialize_of_some hdec, pure_true_emp (by simp [htr, arm64_norm]), emp_sepConj]
    have hpack := okExit_pack_x A s0.sp x.ret x.bytesA x.bytes
      pubCap pubPtr privCap privPtr sigCap sigPtr
      (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x20) (s0.readReg64 .x19)
      pad32 m
    refine Entails.trans ?_ hpack
    unfold words88Sp words88Ret
    simp only [sp', arm64_norm]
    apply entails_of_eq; ac_rfl

private theorem epilogue_err_wp_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hDrop : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dropDecodeError3Name)
      ((Prost.dropDecodeErrorSpecX A).inImage img))
    {x : DecodeGhost} {s0 s : State} {e : BitVec 64}
    (hdec : SignedPreKeyRecordStructure.decode x.bytes = none)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decodeKyberPreKeyName + bv% (28))
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = s0.sp - 128#64)
    (hsp : s.spAligned = true)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hsaved : KpkSavedRegs s0 s) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      (s0.readReg64 .x30) s
      (((s0.sp - 128#64 + 8#64) ↦₆₄ errTag) ∗
        ((s0.sp - 128#64 + 16#64) ↦₆₄ e) ∗
        decodeErrorAt A e ∗
        memRegion (s0.sp - 128#64 + 24#64) 72 ∗
        memRegion x.ret 88 ∗
        memRegion (s0.sp - 128#64) 8 ∗
        ((s0.sp - 128#64 + 96#64) ↦₆₄ s0.readReg64 .x29) ∗
        ((s0.sp - 128#64 + 104#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((s0.sp - 128#64 + 112#64) ↦₆₄ s0.readReg64 .x20) ∗
        ((s0.sp - 128#64 + 120#64) ↦₆₄ s0.readReg64 .x19) ∗
        (x.bytesA ↦ₛ x.bytes) ∗
        stackAt (s0.sp - 128#64) signedDecodeStackX ∗
        memRegion (s0.sp - 128#64 - BitVec.ofNat 64 kpkSubStack) (kpkSubStack - signedDecodeStackX) ∗
        A.pool)
      (kpkPost img A x s0)
      (tryFromQp s0) := by
  set sp' := s0.sp - 128#64
  have hcall := dropDecodeError3_call_ok_x hDrop
  clear hDrop
  have hstack := kpkDecodeStack_drop_split_x sp'
  let retDropOff : BitVec 64 := bv% (104)
  refine Wire.SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left (memRegion88_err_unpack x.ret)))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Wire.SepWPp.exists_pre fun r0 => Wire.SepWPp.exists_pre fun r1 => ?_
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.DecodeKyberPreKey.Helpers.kpkDec
    img.base (Rust.withPanics ext) kpkDec_fnOff kpkDecOff 28 12
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.DecodeKyberPreKey.Helpers.kpkDec
    img.base (Rust.withPanics ext) kpkDec_fnOff kpkDecOff 96 36
  dsimp only [tripleRatchetProgAtExt, decodeKyberPreKeyName] at hcall hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    "libsignal_cli::stores::decode_kyber_pre_key" = entry
  examples_hide_fetches
  refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + dropDecodeError3RelOff) ?_
  wp_steps
  refine Wire.SepWP.done (by dsimp only [dropDecodeError3RelOff]; simp [arm64_norm])
    (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine Wire.SepWPp.call_noPanic_tryFrom e hcall
    (by dsimp only [dropDecodeError3RelOff]; simp [arm64_norm])
    (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1
    (ret_pc := entry + retDropOff) (by dsimp only [retDropOff]; simp [arm64_norm])
    (T := decodeErrorAt A e ∗ A.pool ∗ stackAt sp' Prost.dropDecodeErrorStackX)
    (φ := e = e)
    (by simp [Prost.dropDecodeErrorSpecX, sp', hsp_eq, arm64_norm])
    rfl
    (by rw [hstack]; sep_focus)
    ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  dsimp only [Prost.dropDecodeErrorSpecX]
  rw [sepConj_assoc]
  refine Wire.SepWPp.pure_pre fun htr2 => ?_
  have hsp2_eq : s2.sp = sp' := by simpa [sp', hsp_eq, arm64_norm] using hsp2
  have hx19_2 : s2.readReg64 (Reg.gpr 19#5) = x.ret := by simpa [hx19, arm64_norm] using hcs2.1
  have hx20_2 : s2.readReg64 (Reg.gpr 20#5) = errTag := by simpa [arm64_norm] using hcs2.2.1
  have hsaved2 : KpkSavedRegs s0 s2 := KpkSavedRegs.of_calleeSaved
    ⟨by simpa [arm64_norm] using hsaved.x21,
     by simpa [arm64_norm] using hsaved.x22,
     by simpa [arm64_norm] using hsaved.x23,
     by simpa [arm64_norm] using hsaved.x24,
     by simpa [arm64_norm] using hsaved.x25,
     by simpa [arm64_norm] using hsaved.x26,
     by simpa [arm64_norm] using hsaved.x27,
     by simpa [arm64_norm] using hsaved.x28⟩ hcs2
  dsimp only [retDropOff] at hpc2
  refine Wire.SepWPp.of_sepWP_end hF2 hsym2 ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
  intro _ _
  have hsp_ret : s0.sp - 128#64 + 128#64 = s0.sp := by bv_omega
  refine ⟨by simp [sp', hsp_ret, arm64_norm], fun hv => ?_, ?_⟩
  · refine ⟨by simp [arm64_norm],
      by simp [arm64_norm],
      by simpa [arm64_norm] using hsaved2.x21,
      by simpa [arm64_norm] using hsaved2.x22,
      by simpa [arm64_norm] using hsaved2.x23,
      by simpa [arm64_norm] using hsaved2.x24,
      by simpa [arm64_norm] using hsaved2.x25,
      by simpa [arm64_norm] using hsaved2.x26,
      by simpa [arm64_norm] using hsaved2.x27,
      by simpa [arm64_norm] using hsaved2.x28,
      by simp [arm64_norm],
      hv⟩
  · dsimp only [decodeKyberPreKeySpec, Spec.inImage]
    rw [kyberDeserialize_of_none hdec, pure_true_emp (by simp [htr2, htr, arm64_norm]), emp_sepConj]
    have hpack := errExit_pack_x A s0.sp x.ret x.bytesA e
      (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x20) (s0.readReg64 .x19) x.bytes
    refine Entails.trans ?_ hpack
    simp only [sp', hstack, hsp_eq, arm64_norm]
    apply entails_of_eq; ac_rfl

/-- X-form (`signedDecodeSpecX` + `Prost.dropDecodeErrorSpecX`) wrapper proof for
`signal_session::stores::decode_kyber_pre_key` at any 4 KiB-aligned image base. -/
theorem decodeKyberPreKey_ok_of_decode_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hDecode : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName) (signedDecodeSpecX A img))
    (hDrop : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dropDecodeError3Name)
      ((Prost.dropDecodeErrorSpecX A).inImage img))
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodeKyberPreKeyName)
      (decodeKyberPreKeySpec A img) := by
  let _ := hb
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hsp hL => ?_
  dsimp only [decodeKyberPreKeySpec, Spec.inImage] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hsym⟩, ⟨hx0, hx1, hx2_nat, hne, hlt⟩, hmem⟩
  have hmem' : s0.mem ⊨
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 88 ∗
        stackAt s0.sp smallRootStack ∗ A.pool) ∗ R := by
    ac_nf at hmem ⊢
  have hcall := signedDecode_call_ok_x hDecode
  have hsp128 := kpkSpAligned_sub128 hsp
  let retDecOff : BitVec 64 := bv% (28)
  have hfull : Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      (s0.readReg64 .x30) s0
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 88 ∗
        stackAt s0.sp smallRootStack ∗ A.pool)
      (kpkPost img A x s0)
      (tryFromQp s0) := by
    rw [kpkStack_smallRoot_split_x s0.sp]
    refine Wire.SepWPp.mono_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (kpkFrame32_unpack (s0.sp - 128#64))))))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine Wire.SepWPp.exists_pre fun c0 => Wire.SepWPp.exists_pre fun c1 =>
      Wire.SepWPp.exists_pre fun c2 => Wire.SepWPp.exists_pre fun c3 => ?_
    have heok := @epilogue_ok_wp_x img A ext x s0
    have heerr := @epilogue_err_wp_x img A ext hDrop x s0
    clear hDecode hDrop
    code_fetches_from CryptoVerification.libsignalSessionCode
      CryptoVerification.RecordCodecsBinary.DecodeKyberPreKey.Helpers.kpkDec
      img.base (Rust.withPanics ext) kpkDec_fnOff kpkDecOff 0 28
    dsimp only [tripleRatchetProgAtExt, decodeKyberPreKeyName] at hcall heok heerr hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      "libsignal_cli::stores::decode_kyber_pre_key" = entry
    examples_hide_fetches
    have h0 : s0.readReg64 (Reg.gpr 0#5) = x.ret := hx0
    have h1 : s0.readReg64 (Reg.gpr 1#5) = x.bytesA := hx1
    refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + signedDecodeRelOff) ?_
    wp_steps
    refine Wire.SepWP.done (by dsimp only [signedDecodeRelOff]; simp [arm64_norm])
      (by simp [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    have hsp120 : s0.sp - 120#64 = s0.sp - 128#64 + 8#64 := by bv_omega
    refine Wire.SepWPp.call_tryFrom ⟨x.bytesA, x.bytes, s0.sp - 128#64 + 8#64⟩ hcall
      (by dsimp only [signedDecodeRelOff]; simp [arm64_norm])
      (by simp [hrun, arm64_norm])
      (by simpa [State.spAligned, arm64_norm] using hsp128) hF1 hsym1
      (ret_pc := entry + retDecOff) (by dsimp only [retDecOff]; simp [arm64_norm])
      (by simp [arm64_norm])
      (T := (x.bytesA ↦ₛ x.bytes) ∗ memRegion (s0.sp - 128#64 + 8#64) 88 ∗
        stackAt (s0.sp - 128#64) signedDecodeStackX ∗ A.pool)
      (φ := (s0.readReg64 .x2).toNat = x.bytes.length ∧
        0 < x.bytes.length ∧ x.bytes.length < 2 ^ 32)
      (by simp [h1, hsp120, arm64_norm])
      ⟨hx2_nat, hne, hlt⟩
      (by sep_focus)
      ?_
    clear hcall
    intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
    rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    have hsp2_eq : s2.sp = s0.sp - 128#64 := by simpa [arm64_norm] using hsp2
    have hx19_2 : s2.readReg64 .x19 = x.ret := by simpa [h0, arm64_norm] using hcs2.1
    have hsaved2 : KpkSavedRegs s0 s2 := KpkSavedRegs.of_calleeSaved
      ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
       by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩ hcs2
    have hasub : s0.sp - 128#64 - 65408#64 = s0.sp - 65536#64 := by bv_omega
    have ha96 : s0.sp - 128#64 + 96#64 = s0.sp - 32#64 := by bv_omega
    have ha104 : s0.sp - 128#64 + 104#64 = s0.sp - 24#64 := by bv_omega
    have ha112 : s0.sp - 128#64 + 112#64 = s0.sp - 16#64 := by bv_omega
    have ha120 : s0.sp - 128#64 + 120#64 = s0.sp - 8#64 := by bv_omega
    dsimp only [retDecOff] at hpc2
    dsimp only
    cases hdec : CryptoVerification.RecordCodecs.SignedPreKeyRecordStructure.decode x.bytes with
    | none =>
      dsimp only [signedDecodeResultAt]
      have ha16 : s0.sp - 128#64 + 8#64 + 8#64 = s0.sp - 128#64 + 16#64 := by bv_omega
      have ha24 : s0.sp - 128#64 + 8#64 + 16#64 = s0.sp - 128#64 + 24#64 := by bv_omega
      rw [ha16, ha24]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine Wire.SepWPp.exists_pre fun e => ?_
      have he := @heerr s2 e hdec hpc2 hrun2 hsp2_eq hsp2_align hF2 hsym2
        (by simpa [arm64_norm] using htr2) hx19_2 hsaved2
      refine Wire.SepWPp.mono_pre ?_ he
      simp only [kpkSubStack, arm64_norm]
      rw [hasub, ha96, ha104, ha112, ha120]
      apply entails_of_eq; ac_rfl
    | some m =>
      dsimp only [signedDecodeResultAt]
      have he := @heok s2 m hdec hpc2 hrun2 hsp2_eq hsp2_align hF2 hsym2
        (by simpa [arm64_norm] using htr2) hx19_2 hsaved2
      refine Wire.SepWPp.mono_pre ?_ he
      simp only [kpkSubStack, arm64_norm]
      rw [hasub, ha96, ha104, ha112, ha120]
      apply entails_of_eq; ac_rfl
  obtain ⟨sf, hsteps, hex⟩ := hfull R hmem' hL
  refine reaches_outcome_steps hsteps (reaches_outcome.of_outcome ?_)
  rcases hex with ⟨hpc_f, hrun_f, Pf, hmf, ⟨hsp_f, hcs_f, hent_f⟩, hv_f⟩ | ⟨hpan, Pf, hmf, htr_f⟩ | ⟨_, hoom⟩
  · exact Or.inl ⟨⟨hpc_f, hsp_f, hrun_f⟩, ⟨hsp_f, hcs_f hv_f⟩,
      Satisfies.mono (sepConj_mono_left hent_f) hmf⟩
  · exact Or.inr (Or.inl ⟨hpan, htr_f R hmf⟩)
  · exact (allowPanic_not_exited hoom).elim

end XForm

/-- X-form (`SignedHooksX` + `SignedPortDepsX`): `decode_kyber_pre_key` on
`tripleRatchetProgAtExt img.base ext` meets `decodeKyberPreKeySpec A img` at any 4 KiB-aligned
image base. -/
theorem decodeKyberPreKey_ok_of_hooks_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hH : SignedHooksX img A ext) (d : SignedPortDepsX img A ext)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodeKyberPreKeyName)
      (decodeKyberPreKeySpec A img) :=
  decodeKyberPreKey_ok_of_decode_x
    (SignedPreKeyDecode.signedDecode_ok_of_deps_x hH d hb) d.dropDecodeError3 hb

/-- X-form (`SignedHooksX` + `SignedPortDepsX`): `decode_kyber_pre_key` as
`decode_signed_pre_key` on `tripleRatchetProgAtExt img.base ext` meets
`decodeSignedPreKeySpec A img` at any 4 KiB-aligned image base. -/
theorem decodeSignedPreKey_ok_of_hooks_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hH : SignedHooksX img A ext) (d : SignedPortDepsX img A ext)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodeKyberPreKeyName)
      (decodeSignedPreKeySpec A img) := by
  rw [decodeSignedPreKeySpec_eq]
  exact decodeKyberPreKey_ok_of_hooks_x hH d hb

/-- X-form (`SignedHooksX` + `SignedPortDepsX`): `decode_kyber_pre_key` in the loaded image
`img` (any base) meets `decodeKyberPreKeySpec A img`. -/
theorem decodeKyberPreKey_run_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hH : SignedHooksX img A ext) (d : SignedPortDepsX img A ext) :
    subroutine_ok (Program.ofImage img (Rust.withPanics ext))
      (entryOf img decodeKyberPreKeyName) (decodeKyberPreKeySpec A img) :=
  root_of_tripleRatchetProgAtExt himg
    (decodeKyberPreKey_ok_of_hooks_x hH d (Wire.base_aligned himg))

/-- X-form (`SignedHooksX` + `SignedPortDepsX`): `decode_kyber_pre_key` as
`decode_signed_pre_key` in the loaded image `img` (any base) meets `decodeSignedPreKeySpec A img`. -/
theorem decodeSignedPreKey_run_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hH : SignedHooksX img A ext) (d : SignedPortDepsX img A ext) :
    subroutine_ok (Program.ofImage img (Rust.withPanics ext))
      (entryOf img decodeKyberPreKeyName) (decodeSignedPreKeySpec A img) := by
  rw [decodeSignedPreKeySpec_eq]
  exact decodeKyberPreKey_run_x himg hH d

/-! ## Relocatable `[LibsignalPlacement]` Assembly (Block `595`) -/

section Placed

open CryptoVerification.RecordCodecs.Placed

/-- The image-free signed and Kyber binding specs are the same spec. -/
theorem decodeSignedPreKeyRawSpec_eq (A : RustAlloc) :
    decodeSignedPreKeyRawSpec A = decodeKyberPreKeyRawSpec A := by
  simp only [decodeSignedPreKeyRawSpec, decodeKyberPreKeyRawSpec, signedPreKeyResultAt_deserialize]

/-- The relocatable `[LibsignalPlacement]` signed and Kyber binding specs are the same spec. -/
theorem decodeSignedPreKeyPlacedSpec_eq [LibsignalPlacement] (A : RustAlloc) :
    decodeSignedPreKeyPlacedSpec A = decodeKyberPreKeyPlacedSpec A := by
  simp only [decodeSignedPreKeyPlacedSpec, decodeKyberPreKeyPlacedSpec, decodeSignedPreKeyRawSpec_eq]

/-- `decode_kyber_pre_key` (block `595`) under `[LibsignalPlacement]` meets
`decodeKyberPreKeyPlacedSpec A` from `SignedHooksPlaced` and `SignedPortDepsPlaced`. -/
theorem decodeKyberPreKey_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hH : SignedHooksPlaced A H) (d : SignedPortDepsPlaced A H) :
    subroutine_ok (lsProg_595 H) (blkPl_595).base (decodeKyberPreKeyPlacedSpec A) :=
  DecodeKyberPreKey.decodeKyberPreKey_placed_ok_of_decode
    (SignedPreKeyDecode.signedDecode_placed_ok_of_deps hH d) d.dropDecodeError3

/-- `decode_kyber_pre_key` as `decode_signed_pre_key` (block `595`, LLVM keeps one function
for both) under `[LibsignalPlacement]` meets `decodeSignedPreKeyPlacedSpec A` from
`SignedHooksPlaced` and `SignedPortDepsPlaced`. -/
theorem decodeSignedPreKey_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hH : SignedHooksPlaced A H) (d : SignedPortDepsPlaced A H) :
    subroutine_ok (lsProg_595 H) (blkPl_595).base (decodeSignedPreKeyPlacedSpec A) := by
  rw [decodeSignedPreKeyPlacedSpec_eq]
  exact decodeKyberPreKey_placed_ok hH d

end Placed

end CryptoVerification.RecordCodecsBinary.SignedAssembly

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeatedCommon
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.Defs
import ProofLib.SepLogic.WPp

/-!
# Shared Specifications and Step Lemmas for `encode<Authenticator>` (`[local#1, 2]`)

Provides instruction decode tables (`0x372d4..0x37520` and `0x522c0..0x52544`), pure
Protobuf equivalence lemmas (`encodeAuthMsg`), specifications (`authEncodePinnedSpec`,
`authEncodeSpec`), callee wrappers, and shared basic-block step lemmas for both
monomorphizations of `prost::encoding::message::encode::<Authenticator, Vec<u8>>`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Auth

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (zeroExtend64_beq_zero32 hwVarintLen_eq_ofNat_varintLen_norm
   hwVarintLen_bvShift_eq_ofNat_varintLen_norm
   ule_self_64 ult_self_64
   ofNat_length_beq_zero_of_lt bv_bytesField_nonempty adds_no_overflow_of_eq)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  zeroExtend64_beq_zero32 ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 hwVarintLen_eq_ofNat_varintLen_norm
  hwVarintLen_bvShift_eq_ofNat_varintLen_norm
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  ule_zero_64 ult_zero_64 ule_self_64 ult_self_64

/-! ## Instruction Decode Tables and Symbols -/

gen_decodes libsignalSessionCode_tree libsignalSessionBin [0x373b8 → 0x37604, 0x4cec8 → 0x4d14c]

abbrev authEncode1Name : String :=
  "prost::encoding::message::encode::<spqr::proto::pq_ratchet::Authenticator, alloc::vec::Vec<u8>> [local#1]"

abbrev authEncode2Name : String :=
  "prost::encoding::message::encode::<spqr::proto::pq_ratchet::Authenticator, alloc::vec::Vec<u8>> [local#2]"

@[simp, arm64_norm] theorem authEncode1_fnOff :
    libsignalSessionCode.fnOff authEncode1Name = 0x373b8 :=
  libsignalSessionCode_fnOff_0x373b8

@[simp, arm64_norm] theorem authEncode2_fnOff :
    libsignalSessionCode.fnOff authEncode2Name = 0x4cec8 :=
  libsignalSessionCode_fnOff_0x4cec8

/-- Stack budget `64 + (0x30 + resStack)` for `encode<Authenticator>` (`64` B frame plus `encode_varint`). -/
abbrev authEncodeStackOf (resStack : Nat) : Nat := 64 + (0x30 + resStack)

abbrev authEncodeStack : Nat := authEncodeStackOf doReserveStack

abbrev authEncodeStackX : Nat := authEncodeStackOf doReserveStackX

/-! ## Pure Model Equivalence and Decomposition Lemmas -/

/-- Length-delimited Protobuf bytes (`tag = 2`) appended by `encode<Authenticator>`. -/
abbrev encodeAuthMsg (auth : AuthenticatorPB) : List (BitVec 8) :=
  Proto.encodeMessage ProtoAuthenticator.encodeRaw 2#32 auth

private theorem or_80_truncate8_and_7f (a : BitVec 64) :
    (a.truncate 8 ||| 0x80#8) = ((a &&& 0x7F#64) ||| 0x80#64).setWidth 8 := by
  bv_bits

private theorem protoEncodeVarintAux_eq_codec_of_lt (fuel : Nat) (a : BitVec 64)
    (hbound : a >>> (7 * fuel) < 0x80#64) :
    Proto.encodeVarintAux (fuel + 1) a =
      CryptoVerification.LibsignalProtoCodec.encodeVarintAux (fuel + 1) a := by
  induction fuel generalizing a with
  | zero =>
    simp only [Nat.mul_zero, BitVec.ushiftRight_zero] at hbound
    have h' : a.toNat < 0x80 := BitVec.lt_def.mp hbound
    simp only [Proto.encodeVarintAux, CryptoVerification.LibsignalProtoCodec.encodeVarintAux,
      hbound, h', ↓reduceIte]
  | succ fuel ih =>
    rw [Proto.encodeVarintAux, CryptoVerification.LibsignalProtoCodec.encodeVarintAux]
    have hlt_iff : (a < 0x80#64) ↔ (a.toNat < 0x80) := BitVec.lt_def
    by_cases h : a < 0x80#64
    · have h' : a.toNat < 0x80 := hlt_iff.mp h
      simp only [h, h', ↓reduceIte]
    · have h' : ¬ a.toNat < 0x80 := fun hc => h (hlt_iff.mpr hc)
      have hb' : (a >>> 7) >>> (7 * fuel) < 0x80#64 := by
        have hsh : (a >>> 7) >>> (7 * fuel) = a >>> (7 * (fuel + 1)) := by
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
            ← Nat.pow_add]
          congr 2; omega
        rw [hsh]; exact hbound
      simp only [h, h', ↓reduceIte, or_80_truncate8_and_7f a, ih (a >>> 7) hb']
      rfl

theorem protoEncodeVarint_eq_codec (a : BitVec 64) :
    Proto.encodeVarint a = CryptoVerification.LibsignalProtoCodec.encodeVarint a := by
  refine protoEncodeVarintAux_eq_codec_of_lt 9 a ?_
  change a >>> 63 < 0x80#64
  bv_bits

theorem protoEncodeKey_1_lengthDelimited :
    Proto.encodeKey 1#32 .lengthDelimited = [0x0a#8] := rfl

theorem protoEncodeKey_2_lengthDelimited :
    Proto.encodeKey 2#32 .lengthDelimited = [0x12#8] := rfl

theorem protoEncodeBytesField_nil (tag : BitVec 32) :
    Proto.encodeBytesField tag [] = [] := rfl

theorem protoEncodeBytesField_1_of_ne_nil {bs : List (BitVec 8)} (hne : bs ≠ []) :
    Proto.encodeBytesField 1#32 bs =
      [0x0a#8] ++ CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 bs.length) ++ bs := by
  have hemp : bs.isEmpty = false := List.isEmpty_eq_false_iff.mpr hne
  simp only [Proto.encodeBytesField, hemp, Bool.false_eq_true, ↓reduceIte,
    Proto.encodeBytesUncond, protoEncodeKey_1_lengthDelimited, protoEncodeVarint_eq_codec]

theorem protoEncodeBytesField_2_of_ne_nil {bs : List (BitVec 8)} (hne : bs ≠ []) :
    Proto.encodeBytesField 2#32 bs =
      [0x12#8] ++ CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 bs.length) ++ bs := by
  have hemp : bs.isEmpty = false := List.isEmpty_eq_false_iff.mpr hne
  simp only [Proto.encodeBytesField, hemp, Bool.false_eq_true, ↓reduceIte,
    Proto.encodeBytesUncond, protoEncodeKey_2_lengthDelimited, protoEncodeVarint_eq_codec]

theorem encodeAuthMsg_eq_parts (auth : AuthenticatorPB) :
    encodeAuthMsg auth =
      [0x12#8] ++
        CryptoVerification.LibsignalProtoCodec.encodeVarint
          (BitVec.ofNat 64 (authenticatorPBEncodedLen auth)) ++
        Proto.encodeBytesField 1#32 auth.rootKey ++
        Proto.encodeBytesField 2#32 auth.macKey := by
  have hlen : (ProtoAuthenticator.encodeRaw auth).length = authenticatorPBEncodedLen auth :=
    authenticatorPBEncodedLen_eq_proto auth
  dsimp only [encodeAuthMsg, Proto.encodeMessage]
  rw [hlen, protoEncodeKey_2_lengthDelimited, protoEncodeVarint_eq_codec]
  simp only [ProtoAuthenticator.encodeRaw, List.append_assoc]

theorem encodeAuthMsg_length (auth : AuthenticatorPB) :
    (encodeAuthMsg auth).length =
      1 + (CryptoVerification.LibsignalProtoCodec.encodeVarint
            (BitVec.ofNat 64 (authenticatorPBEncodedLen auth))).length +
        (Proto.encodeBytesField 1#32 auth.rootKey).length +
        (Proto.encodeBytesField 2#32 auth.macKey).length := by
  rw [encodeAuthMsg_eq_parts]
  simp only [List.length_append, List.length_singleton, Nat.add_assoc]

theorem bytesField_1_length_of_ne_nil {bs : List (BitVec 8)} (hne : bs ≠ []) :
    (Proto.encodeBytesField 1#32 bs).length =
      1 + (CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 bs.length)).length + bs.length := by
  rw [protoEncodeBytesField_1_of_ne_nil hne]
  simp only [List.length_append, List.length_singleton]

theorem bytesField_2_length_of_ne_nil {bs : List (BitVec 8)} (hne : bs ≠ []) :
    (Proto.encodeBytesField 2#32 bs).length =
      1 + (CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 bs.length)).length + bs.length := by
  rw [protoEncodeBytesField_2_of_ne_nil hne]
  simp only [List.length_append, List.length_singleton]

theorem authenticatorPBEncodedLen_eq_fields_len (auth : AuthenticatorPB) :
    authenticatorPBEncodedLen auth =
      (Proto.encodeBytesField 1#32 auth.rootKey).length +
        (Proto.encodeBytesField 2#32 auth.macKey).length := by
  have h : (ProtoAuthenticator.encodeRaw auth).length = authenticatorPBEncodedLen auth :=
    authenticatorPBEncodedLen_eq_proto auth
  rw [← h]
  simp only [ProtoAuthenticator.encodeRaw, List.length_append]

/-! ## Specifications of `encode<Authenticator> [local#1, 2]` -/

/-- Pinned ghost arguments `(authA, g, auth, v, cap, ptr, bs)` for
`prost::encoding::message::encode::<Authenticator, Vec<u8>>`. -/
structure AuthEncodePinnedGhost where
  authA : BitVec 64
  g : AuthenticatorPBGhost
  auth : AuthenticatorPB
  v : BitVec 64
  cap : BitVec 64
  ptr : BitVec 64
  bs : List (BitVec 8)

/-- Unpinned ghost arguments for `encode<Authenticator>`. -/
structure AuthEncodeGhost where
  authA : BitVec 64
  auth : AuthenticatorPB
  v : BitVec 64
  cap : BitVec 64
  ptr : BitVec 64
  bs : List (BitVec 8)

/-- Pinned specification of `encode<Authenticator>` parameterized by `resStack`. -/
def authEncodePinnedSpecOf (resStack : Nat) (A : RustAlloc) : Spec AuthEncodePinnedGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.authA ∧
      s.readReg64 .x1 = x.v ∧
      (x.bs.length + (encodeAuthMsg x.auth).length ≤ x.cap.toNat ∨
        x.bs.length + (encodeAuthMsg x.auth).length + 10 < 2 ^ 62)⌝ ∗
      authenticatorPBPinnedAt A x.g x.authA x.auth ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp (authEncodeStackOf resStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      authenticatorPBPinnedAt A x.g x.authA x.auth ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodeAuthMsg x.auth).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A x.v cap' ptr' (x.bs ++ encodeAuthMsg x.auth)) ∗
      A.pool ∗ stackAt s0.sp (authEncodeStackOf resStack)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Unpinned specification of `encode<Authenticator>` parameterized by `resStack`. -/
def authEncodeSpecOf (resStack : Nat) (A : RustAlloc) : Spec AuthEncodeGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.authA ∧
      s.readReg64 .x1 = x.v ∧
      (x.bs.length + (encodeAuthMsg x.auth).length ≤ x.cap.toNat ∨
        x.bs.length + (encodeAuthMsg x.auth).length + 10 < 2 ^ 62)⌝ ∗
      authenticatorPBAt A x.authA x.auth ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp (authEncodeStackOf resStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      authenticatorPBAt A x.authA x.auth ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodeAuthMsg x.auth).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A x.v cap' ptr' (x.bs ++ encodeAuthMsg x.auth)) ∗
      A.pool ∗ stackAt s0.sp (authEncodeStackOf resStack)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

abbrev authEncodePinnedSpec (A : RustAlloc) : Spec AuthEncodePinnedGhost :=
  authEncodePinnedSpecOf doReserveStack A

abbrev authEncodePinnedSpecX (A : RustAlloc) : Spec AuthEncodePinnedGhost :=
  authEncodePinnedSpecOf doReserveStackX A

abbrev authEncodeSpec (A : RustAlloc) : Spec AuthEncodeGhost :=
  authEncodeSpecOf doReserveStack A

abbrev authEncodeSpecX (A : RustAlloc) : Spec AuthEncodeGhost :=
  authEncodeSpecOf doReserveStackX A

def AuthEncode1PinnedOkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr authEncode1Name)
    (authEncodePinnedSpec A)

def AuthEncode1OkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr authEncode1Name)
    (authEncodeSpec A)

def AuthEncode1PinnedOkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr authEncode1Name)
    ((authEncodePinnedSpecX A).inImage img)

def AuthEncode1OkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr authEncode1Name)
    ((authEncodeSpecX A).inImage img)

def AuthEncode2PinnedOkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr authEncode2Name)
    (authEncodePinnedSpec A)

def AuthEncode2OkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr authEncode2Name)
    (authEncodeSpec A)

def AuthEncode2PinnedOkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr authEncode2Name)
    ((authEncodePinnedSpecX A).inImage img)

def AuthEncode2OkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr authEncode2Name)
    ((authEncodeSpecX A).inImage img)

/-! ## Stack, Memory, and Callee Helpers -/

theorem stackAt_authEncode {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    (sp : BitVec 64) :
    stackAt sp (authEncodeStackOf resStack) =
      stackAt (sp - 64#64) (0x30 + resStack) ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
         ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
          ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
          ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
          ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
  have h1 := ProofLib.stackAt_split_cells sp (0x30 + resStack) 8 (by omega)
  have heq : 0x30 + resStack + 8 * 8 = authEncodeStackOf resStack := by
    dsimp [authEncodeStackOf]; omega
  rw [heq] at h1
  have hc8 : cells (sp - 64#64) 8 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
        ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
        ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
    cells_unfold
  rw [h1, hc8]

theorem stackAt_encodeVarint_eq_doReserve64 {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    (sp1 : BitVec 64) :
    stackAt sp1 (0x30 + resStack) =
      memRegion (sp1 - BitVec.ofNat 64 (0x30 + resStack)) 48 ∗ stackAt sp1 resStack := by
  have h := ProofLib.stackAt_split_bottom sp1 resStack 48 (by omega)
  have heq : resStack + 48 = 0x30 + resStack := by omega
  simpa only [heq] using h

theorem sp_sub_64_aligned {sp : BitVec 64} (h : sp &&& 15#64 = 0#64) :
    (sp - 64#64) &&& 15#64 = 0#64 := by
  bv_bits

/-- Pointer and length fields of `AuthenticatorPB` read by `encode<Authenticator>`. -/
def authPBElemsAt (authA rkPtr mkPtr : BitVec 64) (auth : AuthenticatorPB) : SepProp :=
  ((authA + 8#64) ↦₆₄ rkPtr) ∗
  ((authA + 16#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
  (rkPtr ↦ₛ auth.rootKey) ∗
  ((authA + 32#64) ↦₆₄ mkPtr) ∗
  ((authA + 40#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
  (mkPtr ↦ₛ auth.macKey)

/-- Frame remainder of `authenticatorPBPinnedAt` after extracting `authPBElemsAt`. -/
def authPBRestAt (A : RustAlloc) (g : AuthenticatorPBGhost) (authA : BitVec 64)
    (auth : AuthenticatorPB) : SepProp :=
  vecU8ElemRestAt A authA g.rootKey.cap g.rootKey.ptr auth.rootKey ∗
  vecU8ElemRestAt A (authA + 24#64) g.macKey.cap g.macKey.ptr auth.macKey

theorem authenticatorPBPinnedAt_eq_elems (A : RustAlloc) (g : AuthenticatorPBGhost)
    (authA : BitVec 64) (auth : AuthenticatorPB)
    (hrk : g.rootKey.cap = 0 → auth.rootKey = [])
    (hmk : g.macKey.cap = 0 → auth.macKey = []) :
    authenticatorPBPinnedAt A g authA auth =
      authPBElemsAt authA g.rootKey.ptr g.macKey.ptr auth ∗
      authPBRestAt A g authA auth := by
  unfold authenticatorPBPinnedAt authPBElemsAt authPBRestAt
  rw [vecU8At_eq_repeatedBytesElemAt A authA g.rootKey.cap g.rootKey.ptr auth.rootKey hrk,
    vecU8At_eq_repeatedBytesElemAt A (authA + 24#64) g.macKey.cap g.macKey.ptr auth.macKey hmk]
  unfold repeatedBytesElemAt
  have h32 : authA + 24#64 + 8#64 = authA + 32#64 := by bv_omega
  have h40 : authA + 24#64 + 16#64 = authA + 40#64 := by bv_omega
  rw [h32, h40]
  ac_rfl

theorem sepWPp_extract_vecU8At_bounds {A : RustAlloc} {v cap ptr : BitVec 64} {bs : List (BitVec 8)}
    {prog : Program} {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hP : P = vecU8At A v cap ptr bs ∗ F)
    (h : bs.length ≤ cap.toNat → cap.toNat < 2 ^ 63 → ptr ≠ 0 → SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hhm : s.mem ⊨ vecU8Buf A cap ptr bs ∗ (vecHeader v cap ptr (BitVec.ofNat 64 bs.length) ∗ F ∗ R) := by
    rw [hP, vecU8At_eq_header_sep_buf] at hm
    convert hm using 1; ac_rfl
  unfold vecU8Buf at hhm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hhm
  exact h hhm.1.1 hhm.1.2.1 hhm.1.2.2 R hm hL

theorem vecU8At_open_one (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hlt : bs.length < cap.toNat) :
    vecU8At A v cap ptr bs =
      ∃∗ y : BitVec 8,
        (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ((ptr + BitVec.ofNat 64 bs.length) ↦₈ y) ∗ vecRest A cap ptr bs := by
  rw [vecU8At_eq_header_sep_buf, vecHeader, vecU8Buf_eq_open_one A cap ptr bs hlt]
  simp only [sepExists_sepConj_right]
  congr 1; funext y; ac_rfl

theorem vecU8At_close_one (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8))
    (byte : BitVec 8) (hlt : bs.length < cap.toNat) :
    ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
      ((v + 16#64) ↦₆₄ (BitVec.ofNat 64 bs.length + 1#64)) ∗
      ((ptr + BitVec.ofNat 64 bs.length) ↦₈ byte) ∗ vecRest A cap ptr bs) =
    vecU8At A v cap ptr (bs ++ [byte]) := by
  rw [bv_len_add_one bs byte, vecU8At_eq_header_sep_buf, vecHeader,
    ← vecU8Buf_snoc_eq A cap ptr bs byte hlt]
  ac_rfl

/-- Preservation of callee-saved registers `x25..x28` and `StepInv s0 s`. -/
def AuthEncodeCalleeSaved (s0 s : State) : Prop :=
  s.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5) ∧
  s.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) ∧
  s.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) ∧
  s.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) ∧
  calleeSavedVRegs s = calleeSavedVRegs s0 ∧
  StepInv s0 s

theorem AuthEncodeCalleeSaved.refl (s0 : State) : AuthEncodeCalleeSaved s0 s0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, StepInv.refl s0⟩

theorem AuthEncodeCalleeSaved.trans {s0 s1 s2 : State}
    (h01 : AuthEncodeCalleeSaved s0 s1) (h12 : AuthEncodeCalleeSaved s1 s2) :
    AuthEncodeCalleeSaved s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
    h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1,
    h01.2.2.2.2.2.trans h12.2.2.2.2.2⟩

theorem AuthEncodeCalleeSaved.of_calleeSavedPreserved {s1 s2 : State}
    (hcs : CalleeSavedPreserved s1 s2) (hinv : StepInv s1 s2) : AuthEncodeCalleeSaved s1 s2 :=
  ⟨hcs.2.2.2.2.2.2.1, hcs.2.2.2.2.2.2.2.1, hcs.2.2.2.2.2.2.2.2.1, hcs.2.2.2.2.2.2.2.2.2.1,
    hcs.2.2.2.2.2.2.2.2.2.2.2, hinv⟩

theorem AuthEncodeCalleeSaved.step {s0 s1 s2 : State}
    (h01 : AuthEncodeCalleeSaved s0 s1)
    (hx25 : s2.readReg64 (Reg.gpr 25#5) = s1.readReg64 (Reg.gpr 25#5))
    (hx26 : s2.readReg64 (Reg.gpr 26#5) = s1.readReg64 (Reg.gpr 26#5))
    (hx27 : s2.readReg64 (Reg.gpr 27#5) = s1.readReg64 (Reg.gpr 27#5))
    (hx28 : s2.readReg64 (Reg.gpr 28#5) = s1.readReg64 (Reg.gpr 28#5))
    (hinv : StepInv s1 s2)
    (hvregs : calleeSavedVRegs s2 = calleeSavedVRegs s1 := by simp only [arm64_norm]) :
    AuthEncodeCalleeSaved s0 s2 :=
  h01.trans ⟨hx25, hx26, hx27, hx28, hvregs, hinv⟩

def withAuthEncodeCS {α : Type} (s0 : State) (spec : Spec α) : Spec α where
  pre := fun x s => ⌜AuthEncodeCalleeSaved s0 s⌝ ∗ spec.pre x s
  post := spec.post
  onPanic := spec.onPanic
  onExit := spec.onExit
  onOom := spec.onOom

theorem subroutine_ok_withAuthEncodeCS {α : Type} {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (s0 : State) (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (withAuthEncodeCS s0 spec) := by
  refine subroutine_ok_mono h (fun x R s hpre => ?_) (fun _ _ _ _ hpost => hpost)
  rw [withAuthEncodeCS, sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hpre.2

theorem subroutine_ok_withAuthEncodeCS_x {α : Type} {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (img : Obj.Image) (s0 : State) (hinv0 : ImgCallInv img s0)
    (h : subroutine_ok prog entry (spec.inImage img)) :
    subroutine_ok prog entry (withAuthEncodeCS s0 spec) := by
  refine subroutine_ok_mono h (fun x R s hpre => ?_) (fun _ _ _ _ hpost => hpost)
  rw [withAuthEncodeCS, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rw [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hpre.1.2.2.2.2.2 img hinv0, hpre.2⟩

/-- Executes `bl memcpy` with `s.sp = sp - 64#64`. -/
theorem step_auth_memcpy_call (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    {call_pc : BitVec 64}
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext) call_pc sessionMemcpyRegionSpec)
    (dst src sp ret_pc : BitVec 64) (bs : List (BitVec 8))
    {s0 s : State} {x0 : AuthEncodePinnedGhost} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = bs.length)
    (hcs : AuthEncodeCalleeSaved s0 s)
    (hP : P = (memRegion dst bs.length ∗ (src ↦ₛ bs)) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp - 64#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      AuthEncodeCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        (((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (authEncodePinnedSpec A).onPanic x0 s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (authEncodePinnedSpec A).onPanic x0 s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_64_aligned halign
  refine SepWPp.call_cs (x := (dst, src, bs)) (F := F)
    hmemcpy hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    simp only [sessionMemcpyRegionSpec, memcpyRegionSpec, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [sessionMemcpyRegionSpec, sepConj_assoc, satisfies_pure_sepConj] at hm
    exact hm.1.elim
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    simp only [sessionMemcpyRegionSpec, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨_, htrm⟩ => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPp.weaken_pre ?_
      (hnext sm hpcm hrunm hspm htrm' hcsm
        (hcs.trans (AuthEncodeCalleeSaved.of_calleeSavedPreserved hcsm hinv_call)))
    exact Entails.of_eq (by ac_rfl)

/-- Executes `bl encode_varint` with `s.sp = sp - 64#64`. -/
theorem step_auth_encode_varint_call {resStack : Nat} (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    {call_pc : BitVec 64} {s0 s : State}
    (henc : subroutine_ok (tripleRatchetProgAtExt b ext) call_pc
      (withAuthEncodeCS s0 (encodeVarintFitSpecOf resStack A)))
    (val v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length + (CryptoVerification.LibsignalProtoCodec.encodeVarint val).length ≤ curCap.toNat ∨
      curBs.length + 10 < 2 ^ 62)
    {x0 : AuthEncodePinnedGhost} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = val)
    (hx1 : s.readReg64 .x1 = v)
    (hcs : AuthEncodeCalleeSaved s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt (sp - 64#64) (0x30 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp - 64#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      AuthEncodeCalleeSaved s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (CryptoVerification.LibsignalProtoCodec.encodeVarint val).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((vecU8At A v nextCap nextPtr (curBs ++ CryptoVerification.LibsignalProtoCodec.encodeVarint val) ∗ A.pool ∗
          stackAt (sp - 64#64) (0x30 + resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (authEncodePinnedSpec A).onPanic x0 s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (authEncodePinnedSpec A).onPanic x0 s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_64_aligned halign
  refine SepWPp.call_cs (x := EncodeVarintGhost.mk val v curCap curPtr curBs) (F := F)
    henc hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    simp only [withAuthEncodeCS, encodeVarintFitSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hx1, hlen_lt⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [withAuthEncodeCS, encodeVarintFitSpecOf, encodeVarintSpec, encodeVarintSpecOf,
      authEncodePinnedSpec, authEncodePinnedSpecOf, allocFailedIn] at hm ⊢
    rw [htr] at hm
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withAuthEncodeCS, encodeVarintFitSpecOf, encodeVarintSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun nextCap => ?_
    refine SepWPp.exists_elim fun nextPtr => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hge, hpres⟩ => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPp.weaken_pre ?_
      (hnext sm nextCap nextPtr hpcm hrunm hspm htrm' hcsm
        (hcs.trans (AuthEncodeCalleeSaved.of_calleeSavedPreserved hcsm hinv_call)) hge hpres)
    exact Entails.of_eq (by ac_rfl)

/-- Executes `bl do_reserve_and_handle [local#2]` with `s.sp = sp - 64#64`. -/
theorem step_auth_do_reserve2_call {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    {call_pc : BitVec 64} {s0 s : State}
    (hdoReserve : subroutine_ok (tripleRatchetProgAtExt b ext) call_pc
      (withAuthEncodeCS s0 (doReserve2SpecOf resStack A)))
    (v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8)) (additional : Nat)
    (hbound : reserveCap curCap.toNat curBs.length additional + 1 ≤ 2 ^ 63)
    {x0 : AuthEncodePinnedGhost} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v)
    (hx1 : (s.readReg64 .x1).toNat = curBs.length)
    (hx2 : (s.readReg64 .x2).toNat = additional)
    (hcs : AuthEncodeCalleeSaved s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt (sp - 64#64) (0x30 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (newPtr : BitVec 64),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp - 64#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      AuthEncodeCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((vecU8At A v (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length additional)) newPtr curBs ∗
          A.pool ∗ stackAt (sp - 64#64) (0x30 + resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (authEncodePinnedSpec A).onPanic x0 s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (authEncodePinnedSpec A).onPanic x0 s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_64_aligned halign
  refine SepWPp.call_cs (x := DoReserveCall.mk v curCap curPtr curBs additional)
    (F := memRegion (sp - 64#64 - BitVec.ofNat 64 (0x30 + resStack)) 48 ∗ F)
    hdoReserve hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_encodeVarint_eq_doReserve64 hres (sp - 64#64)] at hm
    simp only [withAuthEncodeCS, doReserve2SpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hx1, hx2, hbound⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [withAuthEncodeCS, doReserve2SpecOf, doReserveSpec, authEncodePinnedSpec,
      authEncodePinnedSpecOf, allocFailedIn] at hm ⊢
    rw [htr] at hm
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withAuthEncodeCS, doReserve2SpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun newPtr => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPp.weaken_pre ?_
      (hnext sm newPtr hpcm hrunm hspm htrm' hcsm
        (hcs.trans (AuthEncodeCalleeSaved.of_calleeSavedPreserved hcsm hinv_call)))
    rw [stackAt_encodeVarint_eq_doReserve64 hres (sp - 64#64)]
    exact Entails.of_eq (by ac_rfl)

/-- Executes `bl do_reserve_and_handle [local#7]` with `s.sp = sp - 64#64`. -/
theorem step_auth_do_reserve7_call {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    {call_pc : BitVec 64} {s0 s : State}
    (hdoReserve : subroutine_ok (tripleRatchetProgAtExt b ext) call_pc
      (withAuthEncodeCS s0 (doReserveSpecOf resStack A)))
    (v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8)) (additional : Nat)
    (hbound : reserveCap curCap.toNat curBs.length additional + 1 ≤ 2 ^ 63)
    {x0 : AuthEncodePinnedGhost} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v)
    (hx1 : (s.readReg64 .x1).toNat = curBs.length)
    (hx2 : (s.readReg64 .x2).toNat = additional)
    (hx3 : s.readReg64 .x3 = 1#64)
    (hx4 : s.readReg64 .x4 = 1#64)
    (hcs : AuthEncodeCalleeSaved s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt (sp - 64#64) (0x30 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (newPtr : BitVec 64),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp - 64#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      AuthEncodeCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((vecU8At A v (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length additional)) newPtr curBs ∗
          A.pool ∗ stackAt (sp - 64#64) (0x30 + resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (authEncodePinnedSpec A).onPanic x0 s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (authEncodePinnedSpec A).onPanic x0 s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_64_aligned halign
  refine SepWPp.call_cs (x := DoReserveCall.mk v curCap curPtr curBs additional)
    (F := memRegion (sp - 64#64 - BitVec.ofNat 64 (0x30 + resStack)) 48 ∗ F)
    hdoReserve hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_encodeVarint_eq_doReserve64 hres (sp - 64#64)] at hm
    simp only [withAuthEncodeCS, doReserveSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hx1, hx2, hx3, hx4, hbound⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [withAuthEncodeCS, doReserveSpecOf, doReserveSpec, authEncodePinnedSpec,
      authEncodePinnedSpecOf, allocFailedIn] at hm ⊢
    rw [htr] at hm
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withAuthEncodeCS, doReserveSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun newPtr => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPp.weaken_pre ?_
      (hnext sm newPtr hpcm hrunm hspm htrm' hcsm
        (hcs.trans (AuthEncodeCalleeSaved.of_calleeSavedPreserved hcsm hinv_call)))
    rw [stackAt_encodeVarint_eq_doReserve64 hres (sp - 64#64)]
    exact Entails.of_eq (by ac_rfl)

/-! ## Shared Fetch and Basic-Block Step Lemmas -/

/-- Entry-address predicate for `encode<Authenticator> [local#1]` or `[local#2]`. -/
def IsAuthEncodeEntry (b : BitVec 64) (ext : String → Option (State → State))
    (entry : BitVec 64) : Prop :=
  (tripleRatchetProgAtExt b ext).fnAddr authEncode1Name = entry ∨
  (tripleRatchetProgAtExt b ext).fnAddr authEncode2Name = entry

theorem authEncode_fetch_entry {b : BitVec 64} {ext : String → Option (State → State)}
    {entry : BitVec 64} (hfn : IsAuthEncodeEntry b ext entry) {ins : Instr}
    (h1 : (tripleRatchetProgAtExt b ext).fetch
      ((tripleRatchetProgAtExt b ext).fnAddr authEncode1Name) = some ins)
    (h2 : (tripleRatchetProgAtExt b ext).fetch
      ((tripleRatchetProgAtExt b ext).fnAddr authEncode2Name) = some ins) :
    (tripleRatchetProgAtExt b ext).fetch entry = some ins := by
  rcases hfn with rfl | rfl
  · exact h1
  · exact h2

theorem authEncode_fetch_add {b : BitVec 64} {ext : String → Option (State → State)}
    {entry : BitVec 64} (hfn : IsAuthEncodeEntry b ext entry) {k : Nat} {ins : Instr}
    (h1 : (tripleRatchetProgAtExt b ext).fetch
      ((tripleRatchetProgAtExt b ext).fnAddr authEncode1Name + BitVec.ofNat 64 k) = some ins)
    (h2 : (tripleRatchetProgAtExt b ext).fetch
      ((tripleRatchetProgAtExt b ext).fnAddr authEncode2Name + BitVec.ofNat 64 k) = some ins) :
    (tripleRatchetProgAtExt b ext).fetch (entry + BitVec.ofNat 64 k) = some ins := by
  rcases hfn with rfl | rfl
  · exact h1
  · exact h2

open Lean Elab Tactic in
/-- Instruction-fetch tactic for byte ranges `[kStart, kEnd)` shared by `[local#1]` and `[local#2]`. -/
elab "auth_enc_fetches_range " b:term:max H:term:max _entry:term:max hfn:ident
    kStart:num kEnd:num : tactic => do
  let off1 := 0x373b8
  let off2 := 0x4cec8
  let kStart := kStart.getNat
  let kEnd := kEnd.getNat
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  let fnOff1 := mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x373b8
  let fnOff2 := mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x4cec8
  for i in [kStart / 4 : kEnd / 4] do
    let k := 4 * i
    let dec1 := mkIdent (`CryptoVerification.SpqrV1.Auth |>.str
      s!"libsignalSessionBin_decode_0x{String.ofList (Nat.toDigits 16 (off1 + k))}")
    let dec2 := mkIdent (`CryptoVerification.SpqrV1.Auth |>.str
      s!"libsignalSessionBin_decode_0x{String.ofList (Nat.toDigits 16 (off2 + k))}")
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := authEncode_fetch_entry $hfn
          ($fetchEntry (b := $b) (H := $H) $fnOff1 (by decide) $dec1)
          ($fetchEntry (b := $b) (H := $H) $fnOff2 (by decide) $dec2)))
    else
      evalTactic (← `(tactic|
        have := authEncode_fetch_add $hfn (k := $kq)
          ($fetchAdd (b := $b) (H := $H) (k := $kq) $fnOff1 (by decide) $dec1)
          ($fetchAdd (b := $b) (H := $H) (k := $kq) $fnOff2 (by decide) $dec2)))

/-- Pushes header tag `0x12#8` (`+0x02c..+0x048`) and loads `root_key` and `mac_key` lengths. -/
theorem step_auth_push_hdr (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : IsAuthEncodeEntry b ext entry)
    (v curCap curPtr authA rkPtr mkPtr sp : BitVec 64)
    (curBs : List (BitVec 8)) (auth : AuthenticatorPB)
    (hlt : curBs.length < curCap.toNat)
    {s0 s : State} {x0 : AuthEncodePinnedGhost} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 44#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64)
    (htr : s.trace = s0.trace)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx19 : s.readReg64 .x19 = v)
    (hx21 : s.readReg64 .x21 = authA)
    (hcs : AuthEncodeCalleeSaved s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ authPBElemsAt authA rkPtr mkPtr auth) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = entry + 72#64 →
      sm.status = .Running →
      sm.sp = sp - 64#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = BitVec.ofNat 64 auth.macKey.length →
      sm.readReg64 .x21 = authA →
      sm.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length →
      AuthEncodeCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((vecU8At A v curCap curPtr (curBs ++ [0x12#8]) ∗ authPBElemsAt authA rkPtr mkPtr auth) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (authEncodePinnedSpec A).onPanic x0 s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (authEncodePinnedSpec A).onPanic x0 s0 sf ∗ R)) := by
  auth_enc_fetches_range b (Rust.withPanics ext) entry hfn 44 72
  examples_hide_fetches
  subst hP
  rw [vecU8At_open_one A v curCap curPtr curBs hlt, authPBElemsAt]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_cs (mid := entry + 72#64)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv
  refine SepWPp.weaken_pre ?_
    (hnext _
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv))
  rw [← vecU8At_close_one A v curCap curPtr curBs 0x12#8 hlt, authPBElemsAt]
  exact Entails.of_eq (by ac_rfl)

/-- Computes `x0 = authenticatorPBEncodedLen auth` (`+0x048..+0x08c`, `+0x17c..+0x188`). -/
theorem step_auth_len (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : IsAuthEncodeEntry b ext entry)
    (v authA sp : BitVec 64) (auth : AuthenticatorPB)
    (hrk_lt : auth.rootKey.length < 2 ^ 63)
    (hmk_lt : auth.macKey.length < 2 ^ 63)
    (hlen_fit : authenticatorPBEncodedLen auth < 2 ^ 64)
    {s0 s : State} {x0 : AuthEncodePinnedGhost} {R : SepProp}
    {ret : BitVec 64} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 72#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 auth.macKey.length)
    (hx21 : s.readReg64 .x21 = authA)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length)
    (hcs : AuthEncodeCalleeSaved s0 s)
    (hnext : ∀ (sm : State),
      sm.pc = entry + 144#64 →
      sm.status = .Running →
      sm.sp = sp - 64#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 (authenticatorPBEncodedLen auth) →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = BitVec.ofNat 64 auth.macKey.length →
      sm.readReg64 .x21 = authA →
      sm.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length →
      AuthEncodeCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm P
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (authEncodePinnedSpec A).onPanic x0 s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (authEncodePinnedSpec A).onPanic x0 s0 sf ∗ R)) := by
  auth_enc_fetches_range b (Rust.withPanics ext) entry hfn 72 144
  auth_enc_fetches_range b (Rust.withPanics ext) entry hfn 380 396
  examples_hide_fetches
  obtain ⟨hrk_beq, _⟩ := ofNat_length_beq_zero_of_lt (bs := auth.rootKey) (by omega)
  obtain ⟨hmk_beq, hmk_bne⟩ := ofNat_length_beq_zero_of_lt (bs := auth.macKey) (by omega)
  cases hrk : auth.rootKey.isEmpty <;> cases hmk : auth.macKey.isEmpty
  · -- rootKey non-empty, macKey non-empty
    have hrk_val := bv_bytesField_nonempty hrk
    have hmk_val := bv_bytesField_nonempty hmk
    obtain ⟨hadd, hult1, hule1, hult2, hule2⟩ :=
      adds_no_overflow_of_eq
        (a := bytesFieldEncodedLen auth.macKey)
        (b := bytesFieldEncodedLen auth.rootKey)
        (c := authenticatorPBEncodedLen auth) rfl hlen_fit
    apply SepWPp.of_sepWP_cs (mid := entry + 144#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv
    exact hnext _
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv)
  · -- rootKey non-empty, macKey empty
    have hrk_val := bv_bytesField_nonempty hrk
    have htot_eq : authenticatorPBEncodedLen auth = bytesFieldEncodedLen auth.rootKey := by
      simp [authenticatorPBEncodedLen, bytesFieldEncodedLen, hmk]
    apply SepWPp.of_sepWP_cs (mid := entry + 144#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv
    exact hnext _
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [htot_eq]; simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv)
  · -- rootKey empty, macKey non-empty
    have hmk_val := bv_bytesField_nonempty hmk
    have htot_eq : authenticatorPBEncodedLen auth = bytesFieldEncodedLen auth.macKey := by
      simp [authenticatorPBEncodedLen, bytesFieldEncodedLen, hrk]
    apply SepWPp.of_sepWP_cs (mid := entry + 144#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv
    exact hnext _
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [htot_eq]; simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv)
  · -- rootKey empty, macKey empty
    have htot_eq : authenticatorPBEncodedLen auth = 0 := by
      simp [authenticatorPBEncodedLen, bytesFieldEncodedLen, hrk, hmk]
    apply SepWPp.of_sepWP_cs (mid := entry + 144#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv
    exact hnext _
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [htot_eq]; simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv)

/-- Pushes `root_key` field tag `0x0a#8` (`+0x0b0..+0x0cc`). -/
theorem step_auth_push_rk_tag (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : IsAuthEncodeEntry b ext entry)
    (v curCap curPtr authA rkPtr sp : BitVec 64)
    (curBs : List (BitVec 8)) (auth : AuthenticatorPB)
    (hlt : curBs.length < curCap.toNat)
    {s0 s : State} {x0 : AuthEncodePinnedGhost} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 176#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64)
    (htr : s.trace = s0.trace)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 auth.macKey.length)
    (hx21 : s.readReg64 .x21 = authA)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length)
    (hx23 : s.readReg64 .x23 = rkPtr)
    (hcs : AuthEncodeCalleeSaved s0 s)
    (hP : P = vecU8At A v curCap curPtr curBs ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = entry + 204#64 →
      sm.status = .Running →
      sm.sp = sp - 64#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 auth.rootKey.length →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = BitVec.ofNat 64 auth.macKey.length →
      sm.readReg64 .x21 = authA →
      sm.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length →
      sm.readReg64 .x23 = rkPtr →
      AuthEncodeCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        (vecU8At A v curCap curPtr (curBs ++ [0x0a#8]) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (authEncodePinnedSpec A).onPanic x0 s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (authEncodePinnedSpec A).onPanic x0 s0 sf ∗ R)) := by
  auth_enc_fetches_range b (Rust.withPanics ext) entry hfn 176 204
  examples_hide_fetches
  subst hP
  rw [vecU8At_open_one A v curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_cs (mid := entry + 204#64)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv
  refine SepWPp.weaken_pre ?_
    (hnext _
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv))
  rw [← vecU8At_close_one A v curCap curPtr curBs 0x0a#8 hlt]
  exact Entails.of_eq (by ac_rfl)

/-- Pushes `mac_key` field tag `0x12#8` (`+0x118..+0x134`). -/
theorem step_auth_push_mk_tag (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : IsAuthEncodeEntry b ext entry)
    (v curCap curPtr mkPtr sp : BitVec 64)
    (curBs : List (BitVec 8)) (auth : AuthenticatorPB)
    (hlt : curBs.length < curCap.toNat)
    {s0 s : State} {x0 : AuthEncodePinnedGhost} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 280#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64)
    (htr : s.trace = s0.trace)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 auth.macKey.length)
    (hx21 : s.readReg64 .x21 = mkPtr)
    (hcs : AuthEncodeCalleeSaved s0 s)
    (hP : P = vecU8At A v curCap curPtr curBs ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = entry + 308#64 →
      sm.status = .Running →
      sm.sp = sp - 64#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 auth.macKey.length →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = BitVec.ofNat 64 auth.macKey.length →
      sm.readReg64 .x21 = mkPtr →
      AuthEncodeCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        (vecU8At A v curCap curPtr (curBs ++ [0x12#8]) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (authEncodePinnedSpec A).onPanic x0 s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (authEncodePinnedSpec A).onPanic x0 s0 sf ∗ R)) := by
  auth_enc_fetches_range b (Rust.withPanics ext) entry hfn 280 308
  examples_hide_fetches
  subst hP
  rw [vecU8At_open_one A v curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_cs (mid := entry + 308#64)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv
  refine SepWPp.weaken_pre ?_
    (hnext _
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv))
  rw [← vecU8At_close_one A v curCap curPtr curBs 0x12#8 hlt]
  exact Entails.of_eq (by ac_rfl)

/-- Restores callee-saved registers, deallocates the 64-byte frame, and returns (`+0x168..+0x178`). -/
theorem step_auth_epilogue {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : IsAuthEncodeEntry b ext entry)
    (sp : BitVec 64)
    {s0 s : State} {x0 : AuthEncodePinnedGhost} {R : SepProp}
    {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 360#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hcs : AuthEncodeCalleeSaved s0 s)
    (hP : P = (stackAt (sp - 64#64) (0x30 + resStack) ∗
      ((sp - 64#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 56#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
      ((sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ∗ F)
    (hnext : ∀ (sf : State),
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf →
      StepInv s0 sf →
      Q sf (stackAt sp (authEncodeStackOf resStack) ∗ F)) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (authEncodePinnedSpec A).onPanic x0 s0 sf ∗ R)) := by
  auth_enc_fetches_range b (Rust.withPanics ext) entry hfn 360 380
  examples_hide_fetches
  subst hP
  have hsp_aligned := sp_sub_64_aligned halign
  rcases hcs with ⟨h25, h26, h27, h28, hvregs, hinv0⟩
  apply SepWPp.of_sepWP_cs (mid := s0.readReg64 .lr)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv1
  refine SepWPp.weaken_pre ?_
    (SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hnext _
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by epochEncLen_cc_close) (hinv0.trans hinv1)))
  rw [stackAt_authEncode hres sp]
  refine sepConj_mono_left (sepConj_mono_right ?_)
  exact Entails.sepExists_right (s0.readReg64 .fp)
    (Entails.sepExists_right (s0.readReg64 .lr)
      (Entails.sepExists_right (s0.readReg64 .x24)
        (Entails.sepExists_right (s0.readReg64 .x23)
          (Entails.sepExists_right (s0.readReg64 .x22)
            (Entails.sepExists_right (s0.readReg64 .x21)
              (Entails.sepExists_right (s0.readReg64 .x20)
                (Entails.sepExists_right (s0.readReg64 .x19) (Entails.refl _))))))))

end CryptoVerification.SpqrV1.Auth

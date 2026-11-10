/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.Defs

/-!
# Shared Representation & Pure Helpers for `PolynomialDecoder` and `PolynomialEncoder` `encoded_len`

Provides:
- Unpacking and bounds lemmas for `Poly.protoPolynomialDecoderPinnedAt` and
  `Poly.protoPolynomialEncoderPinnedAt` (from `LibsignalBinary/Proofs/SpqrV1/Poly/EncoderRepr.lean`),
- Pure `encodedLen` models (`polynomialDecoderPBEncodedLen`, `polynomialEncoderPBEncodedLen`) and
  bridge lemmas to `PolynomialDecoder.encodedLen` / `PolynomialEncoder.encodedLen`,
- Hoare `Spec`s (`polynomialDecoderEncodedLenPinnedSpec`, `polynomialEncoderEncodedLenPinnedSpec`)
  and `withMsgEnc48CS` lifting for non-panicking leaf functions.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Prost.MessageEncode

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-! ## 1. `Vec<Vec<u8>>` (`Poly.vecVecU8PinnedAt` / `Poly.vecVecU8At`) Unpacking -/

/-- Heap buffer of `Vec<Vec<u8>>` (element stride `24`, align `8`) detached from its 24-byte `vecHeader`. -/
def vecVecU8Buf (A : RustAlloc) (cap ptr : BitVec 64) (bss : List (List (BitVec 8))) : SepProp :=
  vecBuf A vecHeaderBytes 8 (fun bs addr => vecU8 A addr bs) cap ptr bss

theorem vecVecU8PinnedAt_eq_header_buf (A : RustAlloc) (pin : VecPin) (h : BitVec 64)
    (bss : List (List (BitVec 8))) :
    Poly.vecVecU8PinnedAt A pin h bss =
      (h ↦₆₄ pin.cap) ∗ ((h + 8#64) ↦₆₄ pin.ptr) ∗ ((h + 16#64) ↦₆₄ BitVec.ofNat 64 bss.length) ∗
        vecVecU8Buf A pin.cap pin.ptr bss := by
  simp only [Poly.vecVecU8PinnedAt, vecAt, vecHeader, vecVecU8Buf, sepConj_assoc]

theorem vecVecU8Buf_eq_of_ne_zero {A : RustAlloc} {cap ptr : BitVec 64} {bss : List (List (BitVec 8))}
    (hcap : cap ≠ 0) :
    vecVecU8Buf A cap ptr bss =
      arrayAt (fun bs addr => rustBytesVecAt A addr bs) 24 ptr bss ∗
        (⌜bss.length ≤ cap.toNat ∧ cap.toNat * 24 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
          A.live ptr (cap.toNat * 24) 8 ∗
          memRegion (ptr + BitVec.ofNat 64 (bss.length * 24)) ((cap.toNat - bss.length) * 24)) := by
  unfold vecVecU8Buf vecBuf vecHeaderBytes rustBytesVecAt
  simp only [hcap, ↓reduceIte]
  ac_rfl

theorem vecVecU8Buf_bounds {A : RustAlloc} {cap ptr : BitVec 64} {bss : List (List (BitVec 8))}
    {R : SepProp} {m : Memory} (hm : m ⊨ vecVecU8Buf A cap ptr bss ∗ R) :
    bss.length ≤ cap.toNat ∧ cap.toNat * 24 < 2 ^ 63 := by
  unfold vecVecU8Buf vecBuf vecHeaderBytes at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact ⟨hm.1.1, hm.1.2.1⟩

theorem ofNat_vecVec_length_beq_zero_of_lt {bss : List (List (BitVec 8))} (hlt : bss.length < 2 ^ 64) :
    (BitVec.ofNat 64 bss.length == 0#64) = bss.isEmpty ∧
      (BitVec.ofNat 64 bss.length != 0#64) = !bss.isEmpty := by
  cases bss with
  | nil => exact ⟨rfl, rfl⟩
  | cons bs rest =>
    simp only [List.isEmpty_cons, Bool.not_false]
    have hne : BitVec.ofNat 64 (bs :: rest).length ≠ 0#64 := by
      intro heq
      have h1 := congrArg BitVec.toNat heq
      simp only [BitVec.toNat_ofNat, Nat.zero_mod] at h1
      rw [Nat.mod_eq_of_lt hlt] at h1
      simp only [List.length_cons] at h1
      omega
    exact ⟨beq_eq_false_iff_ne.mpr hne, bne_iff_ne.mpr hne⟩

/-- Remainder of an element `rustBytesVecAt A p bs` (`cap` at `p`, `ptr` at `p + 8`, and heap buffer)
    detached from its `.len` word at `p + 16#64`. -/
def vecU8ElemRest (A : RustAlloc) (p : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
    (p ↦₆₄ cap) ∗ ((p + 8#64) ↦₆₄ ptr) ∗ vecU8Buf A cap ptr bs

theorem rustBytesVecAt_eq_len_sep_rest (A : RustAlloc) (p : BitVec 64) (bs : List (BitVec 8)) :
    rustBytesVecAt A p bs =
      ((p + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ vecU8ElemRest A p bs := by
  simp only [rustBytesVecAt, vecU8, vecU8At_eq_header_sep_buf, vecHeader, vecU8ElemRest,
    sepExists_sepConj_right]
  congr 1; funext cap; congr 1; funext ptr; ac_rfl

theorem vecVecU8At_eq_exists_pin (A : RustAlloc) (v : BitVec 64) (bss : List (List (BitVec 8))) :
    Poly.vecVecU8At A v bss = ∃∗ pin : VecPin, Poly.vecVecU8PinnedAt A pin v bss := by
  unfold Poly.vecVecU8At Poly.vecVecU8PinnedAt vecOf
  apply sepProp_eq_of_entails
  · exact Entails.sepExists_elim fun c => Entails.sepExists_elim fun p =>
      Entails.sepExists_right ⟨c, p⟩ (Entails.refl _)
  · exact Entails.sepExists_elim fun ⟨c, p⟩ =>
      Entails.sepExists_right c (Entails.sepExists_right p (Entails.refl _))

theorem protoPolynomialDecoderAt_eq_exists_pinned (A : RustAlloc) (a : BitVec 64)
    (pb : ProtoPolynomialDecoder) :
    Poly.protoPolynomialDecoderAt A a pb =
      ∃∗ g : Poly.ProtoPolynomialDecoderGhost, Poly.protoPolynomialDecoderPinnedAt A g a pb := by
  simp only [Poly.protoPolynomialDecoderAt, Poly.protoPolynomialDecoderPinnedAt,
    vecVecU8At_eq_exists_pin, sepExists_sepConj_left]
  apply sepProp_eq_of_entails
  · exact Entails.sepExists_elim fun p1 => Entails.sepExists_right ⟨p1⟩ (Entails.refl _)
  · exact Entails.sepExists_elim fun ⟨p1⟩ => Entails.sepExists_right p1 (Entails.refl _)

theorem protoPolynomialEncoderAt_eq_exists_pinned (A : RustAlloc) (a : BitVec 64)
    (pb : ProtoPolynomialEncoder) :
    Poly.protoPolynomialEncoderAt A a pb =
      ∃∗ g : Poly.ProtoPolynomialEncoderGhost, Poly.protoPolynomialEncoderPinnedAt A g a pb := by
  simp only [Poly.protoPolynomialEncoderAt, Poly.protoPolynomialEncoderPinnedAt,
    vecVecU8At_eq_exists_pin, sepExists_sepConj_left, sepExists_sepConj_right]
  apply sepProp_eq_of_entails
  · exact Entails.sepExists_elim fun p2 => Entails.sepExists_elim fun p1 =>
      Entails.sepExists_right ⟨p1, p2⟩ (Entails.refl _)
  · exact Entails.sepExists_elim fun ⟨p1, p2⟩ =>
      Entails.sepExists_right p2 (Entails.sepExists_right p1 (Entails.refl _))

/-! ## 2. Pure `encodedLen` Models & `LibsignalSpqrV1.Proto` Bridge Lemmas -/

/-- Proto3 encoded length of a `bool` field with a 1-byte tag (`tag ∈ 1..15`):
    `2` when `v = true`, `0` when `v = false`. -/
def boolFieldEncodedLen (v : Bool) : Nat :=
  if v then 2 else 0

/-- Per-element body length (without 1-byte tag) of `bs : List (BitVec 8)` in a repeated `bytes` field:
    `bs.length + varintLen (BitVec.ofNat 64 bs.length)`. -/
def bytesElemBodyEncodedLen (bs : List (BitVec 8)) : Nat :=
  bs.length + varintLen (BitVec.ofNat 64 bs.length)

/-- Sum of `bytesElemBodyEncodedLen` over `vs : List (List (BitVec 8))`. -/
def repeatedBytesBodiesEncodedLen (vs : List (List (BitVec 8))) : Nat :=
  vs.foldl (fun acc bs => acc + bytesElemBodyEncodedLen bs) 0

/-- Proto3 encoded length of a `repeated bytes` (`Vec<Vec<u8>>`) field with a 1-byte tag (`tag ∈ 1..15`):
    `repeatedBytesBodiesEncodedLen vs + vs.length`. -/
def repeatedBytesFieldEncodedLen (vs : List (List (BitVec 8))) : Nat :=
  repeatedBytesBodiesEncodedLen vs + vs.length

private theorem foldl_bytesElemBody_add (init : Nat) (vs : List (List (BitVec 8))) :
    vs.foldl (fun acc bs => acc + bytesElemBodyEncodedLen bs) init =
      init + vs.foldl (fun acc bs => acc + bytesElemBodyEncodedLen bs) 0 := by
  induction vs generalizing init with
  | nil => simp
  | cons bs rest ih =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [ih (init + bytesElemBodyEncodedLen bs), ih (bytesElemBodyEncodedLen bs)]
    omega

theorem repeatedBytesBodiesEncodedLen_cons (bs : List (BitVec 8)) (rest : List (List (BitVec 8))) :
    repeatedBytesBodiesEncodedLen (bs :: rest) =
      bytesElemBodyEncodedLen bs + repeatedBytesBodiesEncodedLen rest := by
  unfold repeatedBytesBodiesEncodedLen
  simp only [List.foldl_cons, Nat.zero_add]
  exact foldl_bytesElemBody_add (bytesElemBodyEncodedLen bs) rest

private theorem protoEncodeKey_len_one (tag : BitVec 32) (wt : Proto.WireType)
    (htag : tag ≥ 1#32 ∧ tag ≤ 15#32) :
    (Proto.encodeKey tag wt).length = 1 := by
  have hlt : ((tag <<< 3) ||| wt.toU32).zeroExtend 64 < 0x80#64 := by
    rcases htag with ⟨_, h2⟩
    cases wt <;> dsimp [Proto.WireType.toU32] <;> bv_bits
  dsimp only [Proto.encodeKey, Proto.encodeVarint, Proto.encodeVarintAux]
  split
  · rfl
  · contradiction

theorem boolFieldEncodedLen_eq_proto (tag : BitVec 32) (v : Bool)
    (htag : tag ≥ 1#32 ∧ tag ≤ 15#32) :
    (Proto.encodeBoolField tag v).length = boolFieldEncodedLen v := by
  unfold Proto.encodeBoolField boolFieldEncodedLen
  cases v
  · rfl
  · simp only [↓reduceIte, List.length_append, List.length_singleton,
      protoEncodeKey_len_one tag .varint htag]

theorem repeatedBytesFieldEncodedLen_eq_proto (tag : BitVec 32) (vs : List (List (BitVec 8)))
    (htag : tag ≥ 1#32 ∧ tag ≤ 15#32) :
    (Proto.encodeRepeatedBytes tag vs).length = repeatedBytesFieldEncodedLen vs := by
  unfold repeatedBytesFieldEncodedLen
  induction vs with
  | nil => rfl
  | cons bs rest ih =>
    change (Proto.encodeBytesUncond tag bs ++ Proto.encodeRepeatedBytes tag rest).length =
      repeatedBytesBodiesEncodedLen (bs :: rest) + (bs :: rest).length
    rw [List.length_append, List.length_cons, repeatedBytesBodiesEncodedLen_cons, ih]
    unfold Proto.encodeBytesUncond bytesElemBodyEncodedLen
    simp only [List.length_append, protoEncodeKey_len_one tag .lengthDelimited htag,
      ← protoEncodedLenVarint_eq_varintLen, Proto.encodedLenVarint]
    omega

/-- Convert `ProtoPolynomialDecoder` to `PolynomialDecoder`. -/
def ProtoPolynomialDecoder.toPB (pb : ProtoPolynomialDecoder) : PolynomialDecoder :=
  { ptsNeeded := pb.ptsNeeded, polys := pb.polys, pts := pb.pts, isComplete := pb.isComplete }

/-- Convert `ProtoPolynomialEncoder` to `PolynomialEncoder`. -/
def ProtoPolynomialEncoder.toPB (pb : ProtoPolynomialEncoder) : PolynomialEncoder :=
  { idx := pb.idx, pts := pb.pts, polys := pb.polys }

/-- Encoded length of `spqr::proto::pq_ratchet::PolynomialDecoder`:
    tag 1 `pts_needed: u32` + tag 2 `polys: u32` + tag 3 `pts: Vec<Vec<u8>>` + tag 4 `is_complete: bool`. -/
def polynomialDecoderPBEncodedLen (pb : ProtoPolynomialDecoder) : Nat :=
  u32VarintFieldEncodedLen pb.ptsNeeded +
    u32VarintFieldEncodedLen pb.polys +
    repeatedBytesFieldEncodedLen pb.pts +
    boolFieldEncodedLen pb.isComplete

theorem polynomialDecoderPBEncodedLen_eq_proto (pb : ProtoPolynomialDecoder) :
    PolynomialDecoder.encodedLen (ProtoPolynomialDecoder.toPB pb) = polynomialDecoderPBEncodedLen pb := by
  unfold PolynomialDecoder.encodedLen PolynomialDecoder.encodeRaw
    ProtoPolynomialDecoder.toPB polynomialDecoderPBEncodedLen
  simp only [List.length_append,
    u32VarintFieldEncodedLen_eq_proto 1#32 pb.ptsNeeded ⟨by decide, by decide⟩,
    u32VarintFieldEncodedLen_eq_proto 2#32 pb.polys ⟨by decide, by decide⟩,
    repeatedBytesFieldEncodedLen_eq_proto 3#32 pb.pts ⟨by decide, by decide⟩,
    boolFieldEncodedLen_eq_proto 4#32 pb.isComplete ⟨by decide, by decide⟩]

/-- Encoded length of `spqr::proto::pq_ratchet::PolynomialEncoder`:
    tag 1 `idx: u32` + tag 2 `pts: Vec<Vec<u8>>` + tag 3 `polys: Vec<Vec<u8>>`. -/
def polynomialEncoderPBEncodedLen (pb : ProtoPolynomialEncoder) : Nat :=
  u32VarintFieldEncodedLen pb.idx +
    repeatedBytesFieldEncodedLen pb.pts +
    repeatedBytesFieldEncodedLen pb.polys

theorem polynomialEncoderPBEncodedLen_eq_proto (pb : ProtoPolynomialEncoder) :
    PolynomialEncoder.encodedLen (ProtoPolynomialEncoder.toPB pb) = polynomialEncoderPBEncodedLen pb := by
  unfold PolynomialEncoder.encodedLen PolynomialEncoder.encodeRaw
    ProtoPolynomialEncoder.toPB polynomialEncoderPBEncodedLen
  simp only [List.length_append,
    u32VarintFieldEncodedLen_eq_proto 1#32 pb.idx ⟨by decide, by decide⟩,
    repeatedBytesFieldEncodedLen_eq_proto 2#32 pb.pts ⟨by decide, by decide⟩,
    repeatedBytesFieldEncodedLen_eq_proto 3#32 pb.polys ⟨by decide, by decide⟩]

/-! ## 3. Symbol Names, Stack Budget, and Hoare `Spec`s -/

abbrev polynomialDecoderEncodedLenLocal1Name : String :=
  "<spqr::proto::pq_ratchet::PolynomialDecoder as prost::message::Message>::encoded_len [local#1]"
abbrev polynomialDecoderEncodedLenLocal2Name : String :=
  "<spqr::proto::pq_ratchet::PolynomialDecoder as prost::message::Message>::encoded_len [local#2]"

abbrev polynomialEncoderEncodedLenLocal1Name : String :=
  "<spqr::proto::pq_ratchet::PolynomialEncoder as prost::message::Message>::encoded_len [local#1]"
abbrev polynomialEncoderEncodedLenLocal2Name : String :=
  "<spqr::proto::pq_ratchet::PolynomialEncoder as prost::message::Message>::encoded_len [local#2]"

/-- Stack budget for `PolynomialDecoder::encoded_len` and `PolynomialEncoder::encoded_len` (`0x10` bytes). -/
abbrev polyEncodedLenStack : Nat := 0x10

abbrev PolynomialDecoderEncodedLenPinnedGhost :=
  PinnedEncLenGhost Poly.ProtoPolynomialDecoderGhost ProtoPolynomialDecoder
abbrev PolynomialDecoderEncodedLenGhost :=
  UnpinnedEncLenGhost ProtoPolynomialDecoder

def polynomialDecoderEncodedLenPinnedSpec (A : RustAlloc) :
    Spec PolynomialDecoderEncodedLenPinnedGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a ∧ polynomialDecoderPBEncodedLen x.m < 2 ^ 64⌝ ∗
      Poly.protoPolynomialDecoderPinnedAt A x.g x.a x.m ∗ stackAt s.sp polyEncodedLenStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (polynomialDecoderPBEncodedLen x.m) ∧ sf.trace = s0.trace⌝ ∗
      Poly.protoPolynomialDecoderPinnedAt A x.g x.a x.m ∗ stackAt s0.sp polyEncodedLenStack

def polynomialDecoderEncodedLenSpec (A : RustAlloc) :
    Spec PolynomialDecoderEncodedLenGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a ∧ polynomialDecoderPBEncodedLen x.m < 2 ^ 64⌝ ∗
      Poly.protoPolynomialDecoderAt A x.a x.m ∗ stackAt s.sp polyEncodedLenStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (polynomialDecoderPBEncodedLen x.m) ∧ sf.trace = s0.trace⌝ ∗
      Poly.protoPolynomialDecoderAt A x.a x.m ∗ stackAt s0.sp polyEncodedLenStack

abbrev PolynomialEncoderEncodedLenPinnedGhost :=
  PinnedEncLenGhost Poly.ProtoPolynomialEncoderGhost ProtoPolynomialEncoder
abbrev PolynomialEncoderEncodedLenGhost :=
  UnpinnedEncLenGhost ProtoPolynomialEncoder

def polynomialEncoderEncodedLenPinnedSpec (A : RustAlloc) :
    Spec PolynomialEncoderEncodedLenPinnedGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a ∧ polynomialEncoderPBEncodedLen x.m < 2 ^ 64⌝ ∗
      Poly.protoPolynomialEncoderPinnedAt A x.g x.a x.m ∗ stackAt s.sp polyEncodedLenStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (polynomialEncoderPBEncodedLen x.m) ∧ sf.trace = s0.trace⌝ ∗
      Poly.protoPolynomialEncoderPinnedAt A x.g x.a x.m ∗ stackAt s0.sp polyEncodedLenStack

def polynomialEncoderEncodedLenSpec (A : RustAlloc) :
    Spec PolynomialEncoderEncodedLenGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a ∧ polynomialEncoderPBEncodedLen x.m < 2 ^ 64⌝ ∗
      Poly.protoPolynomialEncoderAt A x.a x.m ∗ stackAt s.sp polyEncodedLenStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (polynomialEncoderPBEncodedLen x.m) ∧ sf.trace = s0.trace⌝ ∗
      Poly.protoPolynomialEncoderAt A x.a x.m ∗ stackAt s0.sp polyEncodedLenStack

/-- Any non-panicking `subroutine_ok` (`spec.onPanic = fun _ _ _ => ⌜False⌝`) automatically lifts
    to `withMsgEnc48CS s0 spec`. -/
theorem subroutine_ok_withMsgEnc48CS_of_no_panic {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} (hok : subroutine_ok prog entry spec)
    (_hnoPanic : ∀ x s1 sf, spec.onPanic x s1 sf = ⌜False⌝) (s0 : State) :
    subroutine_ok prog entry (withMsgEnc48CS s0 spec) :=
  subroutine_ok_withMsgEnc48CS_ext s0 hok

/-! ## 4. Shared Helpers for `repeated bytes` (`Vec<Vec<u8>>`) Loops & Unpacked Representations -/

theorem bv_repeatedBytes_elem_step (acc : Nat) (bs : List (BitVec 8)) :
    BitVec.ofNat 64 bs.length + BitVec.ofNat 64 acc +
      BitVec.ofNat 64 (varintLen (BitVec.ofNat 64 bs.length)) =
    BitVec.ofNat 64 (acc + bytesElemBodyEncodedLen bs) := by
  unfold bytesElemBodyEncodedLen
  simp only [← BitVec.ofNat_add]
  congr 1; omega

theorem ofNat_cons_length_sub_one {α : Type _} (bs : α) (rest : List α) :
    BitVec.ofNat 64 (bs :: rest).length - 1#64 = BitVec.ofNat 64 rest.length := by
  rw [List.length_cons, BitVec.ofNat_add, BitVec.add_sub_cancel]

theorem cons_cons_length_sub_one_flags {α : Type _} (bs bs' : α) (rest' : List α)
    (hlen : (bs :: bs' :: rest').length < 2 ^ 64) :
    BitVec.ofNat 64 (bs :: bs' :: rest').length - 1#64 = BitVec.ofNat 64 (bs' :: rest').length ∧
    (BitVec.ofNat 64 (bs :: bs' :: rest').length == 1#64) = false ∧
    (BitVec.ofNat 64 (bs :: bs' :: rest').length != 1#64) = true ∧
    (BitVec.ofNat 64 (bs' :: rest').length == 0#64) = false ∧
    (BitVec.ofNat 64 (bs' :: rest').length != 0#64) = true := by
  have hsub := ofNat_cons_length_sub_one bs (bs' :: rest')
  have h1 : 1 < (bs :: bs' :: rest').length := by simp
  have ⟨_, _, _, hsub_z, h_eq1⟩ := cmp_ls_false_of_lt h1 hlen
  have h_ne1 : (BitVec.ofNat 64 (bs :: bs' :: rest').length != 1#64) = true := by
    rw [bne, h_eq1]; rfl
  rw [hsub] at hsub_z
  have h_ne0 : (BitVec.ofNat 64 (bs' :: rest').length != 0#64) = true := by
    rw [bne, hsub_z]; rfl
  exact ⟨hsub, h_eq1, h_ne1, hsub_z, h_ne0⟩

theorem boolByte_zext64_shl_one (b : Bool) :
    (boolByte b).zeroExtend 64 <<< 1#64 = BitVec.ofNat 64 (boolFieldEncodedLen b) := by
  cases b <;> rfl

theorem boolByte_zext64_shl_one_nat (b : Bool) :
    (boolByte b).zeroExtend 64 <<< 1 = BitVec.ofNat 64 (boolFieldEncodedLen b) := by
  cases b <;> rfl

theorem bv_repeatedBytesField_nonempty (vs : List (List (BitVec 8))) :
    BitVec.ofNat 64 (repeatedBytesBodiesEncodedLen vs) + BitVec.ofNat 64 vs.length =
      BitVec.ofNat 64 (repeatedBytesFieldEncodedLen vs) := by
  unfold repeatedBytesFieldEncodedLen
  rw [← BitVec.ofNat_add]

theorem vecVecU8Buf_ne_zero_of_cons {A : RustAlloc} {cap ptr : BitVec 64}
    {bs : List (BitVec 8)} {rest : List (List (BitVec 8))} {R : SepProp} {m : Memory}
    (hm : m ⊨ vecVecU8Buf A cap ptr (bs :: rest) ∗ R) :
    cap ≠ 0 := by
  have ⟨hle, _⟩ := vecVecU8Buf_bounds hm
  simp only [List.length_cons] at hle
  intro hzero
  subst hzero
  simp at hle

/-- Unpacked representation of `Poly.protoPolynomialDecoderPinnedAt`. -/
def polynomialDecoderUnpacked (A : RustAlloc) (g : Poly.ProtoPolynomialDecoderGhost)
    (a : BitVec 64) (pb : ProtoPolynomialDecoder) : SepProp :=
  (a ↦₆₄ g.pts.cap) ∗ ((a + 8#64) ↦₆₄ g.pts.ptr) ∗
    ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
    vecVecU8Buf A g.pts.cap g.pts.ptr pb.pts ∗
    ((a + 24#64) ↦₃₂ pb.ptsNeeded) ∗
    ((a + 28#64) ↦₃₂ pb.polys) ∗
    ((a + 32#64) ↦₈ boolByte pb.isComplete) ∗
    memRegion (a + 33#64) 7

theorem protoPolynomialDecoderPinnedAt_eq_unpacked (A : RustAlloc) (g : Poly.ProtoPolynomialDecoderGhost)
    (a : BitVec 64) (pb : ProtoPolynomialDecoder) :
    Poly.protoPolynomialDecoderPinnedAt A g a pb = polynomialDecoderUnpacked A g a pb := by
  simp only [Poly.protoPolynomialDecoderPinnedAt, Poly.protoPolynomialDecoderPtsNeededOff,
    Poly.protoPolynomialDecoderPolysOff, Poly.protoPolynomialDecoderIsCompleteOff,
    Poly.protoPolynomialDecoderPadOff, Poly.protoPolynomialDecoderPadSize,
    polynomialDecoderUnpacked, vecVecU8PinnedAt_eq_header_buf, sepConj_assoc, arm64_norm]

theorem polynomialDecoderUnpacked_pts_bounds {A : RustAlloc} {g : Poly.ProtoPolynomialDecoderGhost}
    {a : BitVec 64} {pb : ProtoPolynomialDecoder} {R : SepProp} {m : Memory}
    (hm : m ⊨ polynomialDecoderUnpacked A g a pb ∗ R) :
    pb.pts.length < 2 ^ 63 ∧
    (BitVec.ofNat 64 pb.pts.length == 0#64) = pb.pts.isEmpty ∧
    (BitVec.ofNat 64 pb.pts.length != 0#64) = !pb.pts.isEmpty ∧
    (∀ bs rest, pb.pts = bs :: rest → g.pts.cap ≠ 0) := by
  unfold polynomialDecoderUnpacked at hm
  have hbuf : m ⊨ vecVecU8Buf A g.pts.cap g.pts.ptr pb.pts ∗
      ((a ↦₆₄ g.pts.cap) ∗ ((a + 8#64) ↦₆₄ g.pts.ptr) ∗
       ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
       ((a + 24#64) ↦₃₂ pb.ptsNeeded) ∗
       ((a + 28#64) ↦₃₂ pb.polys) ∗
       ((a + 32#64) ↦₈ boolByte pb.isComplete) ∗
       memRegion (a + 33#64) 7 ∗ R) := by
    convert hm using 1; ac_rfl
  have ⟨hle, hcap⟩ := vecVecU8Buf_bounds hbuf
  have hlt : pb.pts.length < 2 ^ 63 := by omega
  have hz := ofNat_vecVec_length_beq_zero_of_lt (by omega : pb.pts.length < 2 ^ 64)
  refine ⟨hlt, hz.1, hz.2, ?_⟩
  intro bs rest heq
  rw [heq] at hbuf
  exact vecVecU8Buf_ne_zero_of_cons hbuf

/-- Unpacked representation of `Poly.protoPolynomialEncoderPinnedAt`. -/
def polynomialEncoderUnpacked (A : RustAlloc) (g : Poly.ProtoPolynomialEncoderGhost)
    (a : BitVec 64) (pb : ProtoPolynomialEncoder) : SepProp :=
  (a ↦₆₄ g.pts.cap) ∗ ((a + 8#64) ↦₆₄ g.pts.ptr) ∗
    ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
    vecVecU8Buf A g.pts.cap g.pts.ptr pb.pts ∗
    ((a + 24#64) ↦₆₄ g.polys.cap) ∗ ((a + 32#64) ↦₆₄ g.polys.ptr) ∗
    ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
    vecVecU8Buf A g.polys.cap g.polys.ptr pb.polys ∗
    ((a + 48#64) ↦₃₂ pb.idx) ∗
    memRegion (a + 52#64) 4

theorem protoPolynomialEncoderPinnedAt_eq_unpacked (A : RustAlloc) (g : Poly.ProtoPolynomialEncoderGhost)
    (a : BitVec 64) (pb : ProtoPolynomialEncoder) :
    Poly.protoPolynomialEncoderPinnedAt A g a pb = polynomialEncoderUnpacked A g a pb := by
  simp only [Poly.protoPolynomialEncoderPinnedAt, Poly.protoPolynomialEncoderPolysOff,
    Poly.protoPolynomialEncoderIdxOff, Poly.protoPolynomialEncoderPadOff,
    Poly.protoPolynomialEncoderPadSize,
    polynomialEncoderUnpacked, vecVecU8PinnedAt_eq_header_buf, sepConj_assoc, arm64_norm]

theorem polynomialEncoderUnpacked_bounds {A : RustAlloc} {g : Poly.ProtoPolynomialEncoderGhost}
    {a : BitVec 64} {pb : ProtoPolynomialEncoder} {R : SepProp} {m : Memory}
    (hm : m ⊨ polynomialEncoderUnpacked A g a pb ∗ R) :
    pb.pts.length < 2 ^ 63 ∧
    (BitVec.ofNat 64 pb.pts.length == 0#64) = pb.pts.isEmpty ∧
    (BitVec.ofNat 64 pb.pts.length != 0#64) = !pb.pts.isEmpty ∧
    (∀ bs rest, pb.pts = bs :: rest → g.pts.cap ≠ 0) ∧
    pb.polys.length < 2 ^ 63 ∧
    (BitVec.ofNat 64 pb.polys.length == 0#64) = pb.polys.isEmpty ∧
    (BitVec.ofNat 64 pb.polys.length != 0#64) = !pb.polys.isEmpty ∧
    (∀ bs rest, pb.polys = bs :: rest → g.polys.cap ≠ 0) := by
  unfold polynomialEncoderUnpacked at hm
  have hpts_buf : m ⊨ vecVecU8Buf A g.pts.cap g.pts.ptr pb.pts ∗
      ((a ↦₆₄ g.pts.cap) ∗ ((a + 8#64) ↦₆₄ g.pts.ptr) ∗
       ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
       ((a + 24#64) ↦₆₄ g.polys.cap) ∗ ((a + 32#64) ↦₆₄ g.polys.ptr) ∗
       ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
       vecVecU8Buf A g.polys.cap g.polys.ptr pb.polys ∗
       ((a + 48#64) ↦₃₂ pb.idx) ∗
       memRegion (a + 52#64) 4 ∗ R) := by
    convert hm using 1; ac_rfl
  have hpolys_buf : m ⊨ vecVecU8Buf A g.polys.cap g.polys.ptr pb.polys ∗
      ((a ↦₆₄ g.pts.cap) ∗ ((a + 8#64) ↦₆₄ g.pts.ptr) ∗
       ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
       vecVecU8Buf A g.pts.cap g.pts.ptr pb.pts ∗
       ((a + 24#64) ↦₆₄ g.polys.cap) ∗ ((a + 32#64) ↦₆₄ g.polys.ptr) ∗
       ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
       ((a + 48#64) ↦₃₂ pb.idx) ∗
       memRegion (a + 52#64) 4 ∗ R) := by
    convert hm using 1; ac_rfl
  have ⟨hle1, hcap1⟩ := vecVecU8Buf_bounds hpts_buf
  have ⟨hle2, hcap2⟩ := vecVecU8Buf_bounds hpolys_buf
  have hlt1 : pb.pts.length < 2 ^ 63 := by omega
  have hlt2 : pb.polys.length < 2 ^ 63 := by omega
  have hz1 := ofNat_vecVec_length_beq_zero_of_lt (by omega : pb.pts.length < 2 ^ 64)
  have hz2 := ofNat_vecVec_length_beq_zero_of_lt (by omega : pb.polys.length < 2 ^ 64)
  refine ⟨hlt1, hz1.1, hz1.2, ?_, hlt2, hz2.1, hz2.2, ?_⟩
  · intro bs rest heq; rw [heq] at hpts_buf; exact vecVecU8Buf_ne_zero_of_cons hpts_buf
  · intro bs rest heq; rw [heq] at hpolys_buf; exact vecVecU8Buf_ne_zero_of_cons hpolys_buf

end CryptoVerification.SpqrV1.Prost.MessageEncode


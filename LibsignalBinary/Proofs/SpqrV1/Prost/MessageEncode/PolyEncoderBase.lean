/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncodedLenBase
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint2Base
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBase
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Decodes
import ProofLib.SepLogic.WPp

/-!
# Shared Specification, Pure Lemmas, and Stepping Helpers for `PolynomialEncoder::encode`

Covers shared definitions and stepping blocks for:
- `prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialEncoder, alloc::vec::Vec<u8>> [local#1]`
  (`0x37690..0x3776c`, 55 insns)
- `prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialEncoder, alloc::vec::Vec<u8>> [local#2]`
  (`0x526d4..0x527c0`, 59 insns)
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Prost.MessageEncode

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification.RustHeap
  CryptoGames.LibsignalSession CryptoVerification.LibsignalTripleRatchetRepr
  CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
  CryptoVerification.LibsignalProtoCodec
  CryptoVerification.LibsignalTripleRatchet.Prost
  CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
  CryptoVerification.CodeLayout
  CryptoVerification.LibsignalSpqrV1
  CryptoVerification.SpqrV1.Alloc
  CryptoVerification.SpqrV1.Varint
  CryptoVerification.SpqrV1.ProtoRepr
  CryptoVerification.SpqrV1.Poly
  CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  EncodedLen.zeroExtend64_beq_zero32
  EncodedLen.ofNat_countLeadingZeros_64 EncodedLen.ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 EncodedLen.hwVarintLen_eq_ofNat_varintLen_norm
  EncodedLen.hwVarintLen_bvShift_eq_ofNat_varintLen_norm EncodedLen.zext64_truncate32
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
  EncodedLen.ule_zero_64 EncodedLen.ult_zero_64 EncodedLen.ule_self_64 EncodedLen.ult_self_64

/-! ## 1. Pure Model & `LibsignalSpqrV1.Proto` Bridge Lemmas -/

/-- Full encoded bytes produced by `prost::encoding::message::encode::<PolynomialEncoder, Vec<u8>>`
(hardcoded tag `2#32`, wire type `lengthDelimited` = `2`). -/
def encodePolyEncoderMsg (pb : ProtoPolynomialEncoder) : List (BitVec 8) :=
  Proto.encodeMessage PolynomialEncoder.encodeRaw 2#32 (ProtoPolynomialEncoder.toPB pb)

/-- Header bytes (`[0x12#8] ++ encodeVarint (encoded_len)`) of `PolynomialEncoder::encode`. -/
def polyEncoderHeaderBytes (pb : ProtoPolynomialEncoder) : List (BitVec 8) :=
  [0x12#8] ++ LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 (polynomialEncoderPBEncodedLen pb))

private theorem codec_encodeKey_2_eq_proto :
    LibsignalProtoCodec.encodeKey 2 .lengthDelimited = Proto.encodeKey 2#32 .lengthDelimited := by
  decide

private theorem codec_encodeKey_3_eq_proto :
    LibsignalProtoCodec.encodeKey 3 .lengthDelimited = Proto.encodeKey 3#32 .lengthDelimited := by
  decide

theorem varintEncodeRepeatedBytes_2_eq_proto :
    ∀ (vs : List (List (BitVec 8))),
      Varint.encodeRepeatedBytes 2 vs = Proto.encodeRepeatedBytes 2#32 vs
  | [] => rfl
  | bs :: rest => by
      dsimp only [Varint.encodeRepeatedBytes, encodeBytesField]
      rw [varintEncodeRepeatedBytes_2_eq_proto rest, codec_encodeKey_2_eq_proto]
      dsimp only [Proto.encodeRepeatedBytes, List.foldr, Proto.encodeBytesUncond]
      rw [protoEncodeVarint_eq_codec]

theorem varintEncodeRepeatedBytes_3_eq_proto :
    ∀ (vs : List (List (BitVec 8))),
      Varint.encodeRepeatedBytes 3 vs = Proto.encodeRepeatedBytes 3#32 vs
  | [] => rfl
  | bs :: rest => by
      dsimp only [Varint.encodeRepeatedBytes, encodeBytesField]
      rw [varintEncodeRepeatedBytes_3_eq_proto rest, codec_encodeKey_3_eq_proto]
      dsimp only [Proto.encodeRepeatedBytes, List.foldr, Proto.encodeBytesUncond]
      rw [protoEncodeVarint_eq_codec]

theorem encodePolyEncoderMsg_eq (pb : ProtoPolynomialEncoder) :
    encodePolyEncoderMsg pb =
      polyEncoderHeaderBytes pb ++
        Proto.encodeUint32Field 1#32 pb.idx ++
        Varint.encodeRepeatedBytes 2 pb.pts ++
        Varint.encodeRepeatedBytes 3 pb.polys := by
  have hlen : (PolynomialEncoder.encodeRaw (ProtoPolynomialEncoder.toPB pb)).length =
      polynomialEncoderPBEncodedLen pb :=
    polynomialEncoderPBEncodedLen_eq_proto pb
  dsimp only [encodePolyEncoderMsg, Proto.encodeMessage, polyEncoderHeaderBytes]
  rw [protoEncodeKey_lengthDelimited_2, protoEncodeVarint_eq_codec, hlen]
  dsimp only [PolynomialEncoder.encodeRaw, ProtoPolynomialEncoder.toPB]
  rw [← varintEncodeRepeatedBytes_2_eq_proto, ← varintEncodeRepeatedBytes_3_eq_proto]
  simp only [List.append_assoc]

theorem bs0_append_encodePolyEncoderMsg (bs0 : List (BitVec 8)) (pb : ProtoPolynomialEncoder) :
    bs0 ++ encodePolyEncoderMsg pb =
      (((bs0 ++ polyEncoderHeaderBytes pb) ++
        Proto.encodeUint32Field 1#32 pb.idx) ++
        Varint.encodeRepeatedBytes 2 pb.pts) ++
        Varint.encodeRepeatedBytes 3 pb.polys := by
  rw [encodePolyEncoderMsg_eq]; simp only [List.append_assoc]

theorem bs0_append_polyEncoderHeaderBytes (bs0 : List (BitVec 8)) (pb : ProtoPolynomialEncoder) :
    (bs0 ++ [0x12#8]) ++
      LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 (polynomialEncoderPBEncodedLen pb)) =
    bs0 ++ polyEncoderHeaderBytes pb := by
  rw [polyEncoderHeaderBytes, List.append_assoc]

theorem polyEncoderHeaderBytes_len_bounds (pb : ProtoPolynomialEncoder) :
    (polyEncoderHeaderBytes pb).length =
      1 + (LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 (polynomialEncoderPBEncodedLen pb))).length ∧
    2 ≤ (polyEncoderHeaderBytes pb).length := by
  have hb := Varint.encodeVarint_length_bounds (BitVec.ofNat 64 (polynomialEncoderPBEncodedLen pb))
  rw [polyEncoderHeaderBytes, List.length_append, List.length_singleton]
  omega

theorem bs_append_idx_of_ne_zero (bs : List (BitVec 8)) (pb : ProtoPolynomialEncoder)
    (hidx : (pb.idx == 0#32) = false) :
    (bs ++ [0x08#8]) ++ LibsignalProtoCodec.encodeVarint (pb.idx.zeroExtend 64) =
      bs ++ Proto.encodeUint32Field 1#32 pb.idx := by
  rw [protoEncodeUint32Field_1_of_ne_zero (beq_eq_false_iff_ne.mp hidx), List.append_assoc]

theorem bs_append_idx_of_zero (bs : List (BitVec 8)) (pb : ProtoPolynomialEncoder)
    (hidx : (pb.idx == 0#32) = true) :
    bs ++ Proto.encodeUint32Field 1#32 pb.idx = bs := by
  rw [eq_of_beq hidx, protoEncodeUint32Field_zero, List.append_nil]

theorem idx_field_len_of_ne_zero (pb : ProtoPolynomialEncoder) (hidx : (pb.idx == 0#32) = false) :
    (Proto.encodeUint32Field 1#32 pb.idx).length =
      1 + (LibsignalProtoCodec.encodeVarint (pb.idx.zeroExtend 64)).length ∧
    2 ≤ (Proto.encodeUint32Field 1#32 pb.idx).length := by
  have hb := (Varint.encodeVarint_length_bounds (pb.idx.zeroExtend 64)).1
  rw [protoEncodeUint32Field_1_of_ne_zero (beq_eq_false_iff_ne.mp hidx),
    List.length_append, List.length_singleton]
  omega

theorem encodePolyEncoderMsg_len_split (pb : ProtoPolynomialEncoder) :
    (encodePolyEncoderMsg pb).length =
      (polyEncoderHeaderBytes pb).length +
        (Proto.encodeUint32Field 1#32 pb.idx).length +
        (Varint.encodeRepeatedBytes 2 pb.pts).length +
        (Varint.encodeRepeatedBytes 3 pb.polys).length := by
  rw [encodePolyEncoderMsg_eq, List.length_append, List.length_append, List.length_append]

theorem polynomialEncoderPBEncodedLen_le_msg_len (pb : ProtoPolynomialEncoder) :
    polynomialEncoderPBEncodedLen pb + 2 ≤ (encodePolyEncoderMsg pb).length := by
  have hraw : (PolynomialEncoder.encodeRaw (ProtoPolynomialEncoder.toPB pb)).length =
      polynomialEncoderPBEncodedLen pb :=
    polynomialEncoderPBEncodedLen_eq_proto pb
  have h1 : (PolynomialEncoder.encodeRaw (ProtoPolynomialEncoder.toPB pb)).length =
      (Proto.encodeUint32Field 1#32 pb.idx).length +
        (Varint.encodeRepeatedBytes 2 pb.pts).length +
        (Varint.encodeRepeatedBytes 3 pb.polys).length := by
    dsimp only [PolynomialEncoder.encodeRaw, ProtoPolynomialEncoder.toPB]
    rw [← varintEncodeRepeatedBytes_2_eq_proto, ← varintEncodeRepeatedBytes_3_eq_proto]
    simp only [List.length_append]
  have hhdr := (polyEncoderHeaderBytes_len_bounds pb).2
  rw [encodePolyEncoderMsg_len_split]
  omega

theorem encodeBytesField_some_length_ge_two (tag : Nat) (bs : List (BitVec 8)) :
    2 ≤ (encodeBytesField tag (some bs)).length := by
  dsimp only [encodeBytesField, encodeKey]
  rw [List.length_append, List.length_append]
  have h1 := (Varint.encodeVarint_length_bounds (BitVec.ofNat 64 (tag * 8 + WireType.lengthDelimited.toNat))).1
  have h2 := (Varint.encodeVarint_length_bounds (BitVec.ofNat 64 bs.length)).1
  omega

theorem encodeRepeatedBytes_length_ge_two_mul (tag : Nat) (vs : List (List (BitVec 8))) :
    2 * vs.length ≤ (Varint.encodeRepeatedBytes tag vs).length := by
  induction vs with
  | nil => simp [Varint.encodeRepeatedBytes]
  | cons bs rest ih =>
    simp only [Varint.encodeRepeatedBytes, List.length_append, List.length_cons]
    have h1 := encodeBytesField_some_length_ge_two tag bs
    omega

theorem polyEncoder_pts_polys_lt_of_msg_len_lt {pb : ProtoPolynomialEncoder}
    (h : (encodePolyEncoderMsg pb).length < 2 ^ 59) :
    pb.pts.length < 2 ^ 58 ∧ pb.polys.length < 2 ^ 58 := by
  have h1 := encodeRepeatedBytes_length_ge_two_mul 2 pb.pts
  have h2 := encodeRepeatedBytes_length_ge_two_mul 3 pb.polys
  rw [encodePolyEncoderMsg_len_split] at h
  omega


/-! ## 2. Unpacking `Poly.protoPolynomialEncoderPinnedAt` via `satisfies_vecVecU8PinnedAt_iff` -/

/-- Active fields of `ProtoPolynomialEncoder` accessed during `+76..+168` of `PolynomialEncoder::encode`. -/
def polyEncoderElemsAt (encA : BitVec 64) (g : Poly.ProtoPolynomialEncoderGhost)
    (pb : ProtoPolynomialEncoder)
    (ptsElems polysElems : List (BitVec 64 × List (BitVec 8))) : SepProp :=
  ((encA + 8#64) ↦₆₄ g.pts.ptr) ∗
    ((encA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
    ((encA + 32#64) ↦₆₄ g.polys.ptr) ∗
    ((encA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
    ((encA + 48#64) ↦₃₂ pb.idx) ∗
    repeatedBytesSliceAt g.pts.ptr ptsElems ∗
    repeatedBytesSliceAt g.polys.ptr polysElems

/-- Framed remainder of `Poly.protoPolynomialEncoderPinnedAt A g encA pb` after extracting
`polyEncoderElemsAt encA g pb ptsElems polysElems`. -/
def polyEncoderRestAt (A : RustAlloc) (encA : BitVec 64) (g : Poly.ProtoPolynomialEncoderGhost)
    (ptsElems polysElems : List (BitVec 64 × List (BitVec 8))) : SepProp :=
  (encA ↦₆₄ g.pts.cap) ∗
    ((encA + 24#64) ↦₆₄ g.polys.cap) ∗
    vecVecU8PinnedRestAt A g.pts ptsElems ∗
    vecVecU8PinnedRestAt A g.polys polysElems ∗
    memRegion (encA + 0x34#64) 4

theorem satisfies_protoPolynomialEncoderPinnedAt_iff (A : RustAlloc)
    (g : Poly.ProtoPolynomialEncoderGhost) (encA : BitVec 64) (pb : ProtoPolynomialEncoder)
    (R : SepProp) (m : Memory) :
    (m ⊨ Poly.protoPolynomialEncoderPinnedAt A g encA pb ∗ R) ↔
    ∃ ptsElems polysElems : List (BitVec 64 × List (BitVec 8)),
      ptsElems.map Prod.snd = pb.pts ∧ pb.pts.length * 24 < 2 ^ 63 ∧
      polysElems.map Prod.snd = pb.polys ∧ pb.polys.length * 24 < 2 ^ 63 ∧
      (m ⊨ (polyEncoderElemsAt encA g pb ptsElems polysElems ∗
        polyEncoderRestAt A encA g ptsElems polysElems) ∗ R) := by
  dsimp only [Poly.protoPolynomialEncoderPinnedAt, Poly.protoPolynomialEncoderPolysOff,
    Poly.protoPolynomialEncoderIdxOff, Poly.protoPolynomialEncoderPadOff,
    Poly.protoPolynomialEncoderPadSize, polyEncoderElemsAt, polyEncoderRestAt]
  have ha32 : encA + 24#64 + 8#64 = encA + 32#64 := by bv_omega
  have ha40 : encA + 24#64 + 16#64 = encA + 40#64 := by bv_omega
  have ha48 : encA + 0x30#64 = encA + 48#64 := rfl
  constructor
  · intro hm
    have hm0 : m ⊨ Poly.vecVecU8PinnedAt A g.pts encA pb.pts ∗
        (Poly.vecVecU8PinnedAt A g.polys (encA + 24#64) pb.polys ∗
          ((encA + 48#64) ↦₃₂ pb.idx) ∗ memRegion (encA + 0x34#64) 4 ∗ R) := by
      rw [ha48] at hm; convert hm using 1; ac_rfl
    obtain ⟨ptsElems, hpts_eq, hpts_lt, hm1⟩ :=
      (satisfies_vecVecU8PinnedAt_iff A g.pts encA pb.pts _ m).mp hm0
    have hm1' : m ⊨ Poly.vecVecU8PinnedAt A g.polys (encA + 24#64) pb.polys ∗
        (((encA ↦₆₄ g.pts.cap) ∗ ((encA + 8#64) ↦₆₄ g.pts.ptr) ∗
          ((encA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
          repeatedBytesSliceAt g.pts.ptr ptsElems ∗ vecVecU8PinnedRestAt A g.pts ptsElems) ∗
          ((encA + 48#64) ↦₃₂ pb.idx) ∗ memRegion (encA + 0x34#64) 4 ∗ R) := by
      convert hm1 using 1; ac_rfl
    obtain ⟨polysElems, hpolys_eq, hpolys_lt, hm2⟩ :=
      (satisfies_vecVecU8PinnedAt_iff A g.polys (encA + 24#64) pb.polys _ m).mp hm1'
    rw [ha32, ha40] at hm2
    refine ⟨ptsElems, polysElems, hpts_eq, hpts_lt, hpolys_eq, hpolys_lt, ?_⟩
    convert hm2 using 1; ac_rfl
  · rintro ⟨ptsElems, polysElems, hpts_eq, hpts_lt, hpolys_eq, hpolys_lt, hm⟩
    have hm2 : m ⊨ (((encA + 24#64) ↦₆₄ g.polys.cap) ∗
        ((encA + 24#64 + 8#64) ↦₆₄ g.polys.ptr) ∗
        ((encA + 24#64 + 16#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
        repeatedBytesSliceAt g.polys.ptr polysElems ∗
        vecVecU8PinnedRestAt A g.polys polysElems) ∗
        (((encA ↦₆₄ g.pts.cap) ∗ ((encA + 8#64) ↦₆₄ g.pts.ptr) ∗
          ((encA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
          repeatedBytesSliceAt g.pts.ptr ptsElems ∗ vecVecU8PinnedRestAt A g.pts ptsElems) ∗
          ((encA + 48#64) ↦₃₂ pb.idx) ∗ memRegion (encA + 0x34#64) 4 ∗ R) := by
      rw [ha32, ha40]; convert hm using 1; ac_rfl
    have hm1' := (satisfies_vecVecU8PinnedAt_iff A g.polys (encA + 24#64) pb.polys _ m).mpr
      ⟨polysElems, hpolys_eq, hpolys_lt, hm2⟩
    have hm1 : m ⊨ ((encA ↦₆₄ g.pts.cap) ∗ ((encA + 8#64) ↦₆₄ g.pts.ptr) ∗
        ((encA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
        repeatedBytesSliceAt g.pts.ptr ptsElems ∗ vecVecU8PinnedRestAt A g.pts ptsElems) ∗
        (Poly.vecVecU8PinnedAt A g.polys (encA + 24#64) pb.polys ∗
          ((encA + 48#64) ↦₃₂ pb.idx) ∗ memRegion (encA + 0x34#64) 4 ∗ R) := by
      convert hm1' using 1; ac_rfl
    have hm0 := (satisfies_vecVecU8PinnedAt_iff A g.pts encA pb.pts _ m).mpr
      ⟨ptsElems, hpts_eq, hpts_lt, hm1⟩
    rw [ha48]; convert hm0 using 1; ac_rfl

/-- Variant of `polynomialEncoderEncodedLenPinnedSpec` whose postcondition exposes
`polyEncoderElemsAt` and `polyEncoderRestAt` for the subsequent field encodes. -/
def polynomialEncoderEncodedLenElemsOutSpec (A : RustAlloc) :
    Spec PolynomialEncoderEncodedLenPinnedGhost where
  pre := (polynomialEncoderEncodedLenPinnedSpec A).pre
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (polynomialEncoderPBEncodedLen x.m) ∧ sf.trace = s0.trace⌝ ∗
      (∃∗ ptsElems : List (BitVec 64 × List (BitVec 8)),
       ∃∗ polysElems : List (BitVec 64 × List (BitVec 8)),
        ⌜ptsElems.map Prod.snd = x.m.pts ∧ x.m.pts.length * 24 < 2 ^ 63 ∧
          polysElems.map Prod.snd = x.m.polys ∧ x.m.polys.length * 24 < 2 ^ 63⌝ ∗
        polyEncoderElemsAt x.a x.g x.m ptsElems polysElems ∗
        polyEncoderRestAt A x.a x.g ptsElems polysElems) ∗
      stackAt s0.sp polyEncodedLenStack

theorem subroutine_ok_polyEncLenElemsOut_of_pinned {prog : Program} {entry : BitVec 64}
    {A : RustAlloc}
    (hok : subroutine_ok prog entry (polynomialEncoderEncodedLenPinnedSpec A)) :
    subroutine_ok prog entry (polynomialEncoderEncodedLenElemsOutSpec A) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  refine (hok.to_outcome x R s0 hpc hrun hpre hsp).mono_outcome ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | hrest)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [polynomialEncoderEncodedLenPinnedSpec] at hq
    dsimp only [polynomialEncoderEncodedLenElemsOutSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    obtain ⟨hpure, hq_mem⟩ := hq
    refine ⟨hpure, ?_⟩
    have hq_mem' : sf.mem ⊨ Poly.protoPolynomialEncoderPinnedAt A x.g x.a x.m ∗
        (stackAt s0.sp polyEncodedLenStack ∗ R) := by
      convert hq_mem using 1; ac_rfl
    obtain ⟨ptsElems, polysElems, hpts_eq, hpts_lt, hpolys_eq, hpolys_lt, hm_unp⟩ :=
      (satisfies_protoPolynomialEncoderPinnedAt_iff A x.g x.a x.m _ sf.mem).mp hq_mem'
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨ptsElems, polysElems, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hpts_eq, hpts_lt, hpolys_eq, hpolys_lt⟩, ?_⟩
    convert hm_unp using 1; ac_rfl
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr hrest)

/-! ## 3. Shared `encodeRepeatedStackOf`-Frame Call Helpers (`step_msg48rep_*`) -/

theorem calleeSavedPreserved_setPC {s0 s : State} (pc : BitVec 64)
    (hcc : CalleeSavedPreserved s0 s) :
    CalleeSavedPreserved s0 (s.setPC pc) := by
  simpa only [CalleeSavedPreserved, State.readReg64_setPC, calleeSavedVRegs_setPC] using hcc

theorem msgEnc48CalleeSaved_setPC {s0 s : State} (pc : BitVec 64)
    (hcs : MsgEnc48CalleeSaved s0 s) (hinv : StepInv s (s.setPC pc)) :
    MsgEnc48CalleeSaved s0 (s.setPC pc) :=
  hcs.step (State.readReg64_setPC _ _ _) (State.readReg64_setPC _ _ _)
    (State.readReg64_setPC _ _ _) (State.readReg64_setPC _ _ _)
    (State.readReg64_setPC _ _ _) (State.readReg64_setPC _ _ _)
    (State.readReg64_setPC _ _ _) hinv

theorem step_msg48rep_encode_varint_call {resStack : Nat} (hres : resStack + 128 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {call_pc : BitVec 64} {s0 s : State}
    (henc : subroutine_ok (tripleRatchetProgAtExt b ext) call_pc
      (withMsgEnc48CS s0 (encodeVarintFitSpecOf resStack A)))
    (val v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length + (LibsignalProtoCodec.encodeVarint val).length ≤ curCap.toNat ∨
      curBs.length + 10 < 2 ^ 62)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hcs : MsgEnc48CalleeSaved s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ A.pool ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → MsgEnc48CalleeSaved s0 sm → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (LibsignalProtoCodec.encodeVarint val).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((vecU8At A v nextCap nextPtr (curBs ++ LibsignalProtoCodec.encodeVarint val) ∗
          A.pool ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  refine step_msg48_encode_varint_call b A ext henc val v curCap curPtr sp ret_pc curBs hlen_lt
    (F := memRegion (sp - 48#64 - BitVec.ofNat 64 (encodeRepeatedStackOf resStack)) 80 ∗ F)
    hpc hrun hsp halign htr hlr hx0 hx1 hcs
    (by rw [hP, stackAt_encodeRepeated_eq_varint hres (sp - 48#64)]; ac_rfl) ?_
  intro sm nextCap nextPtr hpcm hrunm hspm htrm hcsm hcs_m hge hpres
  refine SepWPp.weaken_pre ?_
    (hnext sm nextCap nextPtr hpcm hrunm hspm htrm hcsm hcs_m hge hpres)
  rw [stackAt_encodeRepeated_eq_varint hres (sp - 48#64)]
  exact Entails.of_eq (by ac_rfl)

theorem step_msg48rep_do_reserve2_call {resStack : Nat} (hres : resStack + 128 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {call_pc : BitVec 64} {s0 s : State}
    (hdoReserve : subroutine_ok (tripleRatchetProgAtExt b ext) call_pc
      (withMsgEnc48CS s0 (doReserve2SpecOf resStack A)))
    (v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8)) (add : Nat)
    (hres_bound : reserveCap curCap.toNat curBs.length add + 1 ≤ 2 ^ 63)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = v)
    (hx1 : (s.readReg64 .x1).toNat = curBs.length)
    (hx2 : (s.readReg64 .x2).toNat = add)
    (hcs : MsgEnc48CalleeSaved s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ A.pool ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (newPtr : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → MsgEnc48CalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((vecU8At A v (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length add)) newPtr curBs ∗
          A.pool ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  refine step_msg48_do_reserve2_call (by omega) b A ext hdoReserve v curCap curPtr sp ret_pc curBs add
    hres_bound
    (F := memRegion (sp - 48#64 - BitVec.ofNat 64 (encodeRepeatedStackOf resStack)) 80 ∗ F)
    hpc hrun hsp halign htr hlr hx0 hx1 hx2 hcs
    (by rw [hP, stackAt_encodeRepeated_eq_varint hres (sp - 48#64)]; ac_rfl) ?_
  intro sm newPtr hpcm hrunm hspm htrm hcsm hcs_m
  refine SepWPp.weaken_pre ?_ (hnext sm newPtr hpcm hrunm hspm htrm hcsm hcs_m)
  rw [stackAt_encodeRepeated_eq_varint hres (sp - 48#64)]
  exact Entails.of_eq (by ac_rfl)

theorem step_msg48rep_do_reserve7_call {resStack : Nat} (hres : resStack + 128 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {call_pc : BitVec 64} {s0 s : State}
    (hdoReserve : subroutine_ok (tripleRatchetProgAtExt b ext) call_pc
      (withMsgEnc48CS s0 (doReserveSpecOf resStack A)))
    (v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8)) (add : Nat)
    (hres_bound : reserveCap curCap.toNat curBs.length add + 1 ≤ 2 ^ 63)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = v)
    (hx1 : (s.readReg64 .x1).toNat = curBs.length)
    (hx2 : (s.readReg64 .x2).toNat = add)
    (hx3 : s.readReg64 .x3 = 1#64) (hx4 : s.readReg64 .x4 = 1#64)
    (hcs : MsgEnc48CalleeSaved s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ A.pool ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (newPtr : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → MsgEnc48CalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((vecU8At A v (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length add)) newPtr curBs ∗
          A.pool ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  refine step_msg48_do_reserve7_call (by omega) b A ext hdoReserve v curCap curPtr sp ret_pc curBs add
    hres_bound
    (F := memRegion (sp - 48#64 - BitVec.ofNat 64 (encodeRepeatedStackOf resStack)) 80 ∗ F)
    hpc hrun hsp halign htr hlr hx0 hx1 hx2 hx3 hx4 hcs
    (by rw [hP, stackAt_encodeRepeated_eq_varint hres (sp - 48#64)]; ac_rfl) ?_
  intro sm newPtr hpcm hrunm hspm htrm hcsm hcs_m
  refine SepWPp.weaken_pre ?_ (hnext sm newPtr hpcm hrunm hspm htrm hcsm hcs_m)
  rw [stackAt_encodeRepeated_eq_varint hres (sp - 48#64)]
  exact Entails.of_eq (by ac_rfl)

/-- Execute `bl PolynomialEncoder::encoded_len` (via `polynomialEncoderEncodedLenElemsOutSpec`)
at `call_pc` when the stack at `sp - 48#64` is `stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)`. -/
theorem step_msg48rep_polyEncLen_call {resStack : Nat} (hres : resStack + 128 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {call_pc : BitVec 64} {s0 s : State}
    (hencLen : subroutine_ok (tripleRatchetProgAtExt b ext) call_pc
      (withMsgEnc48CS s0 (polynomialEncoderEncodedLenElemsOutSpec A)))
    (encA sp ret_pc : BitVec 64) (g : Poly.ProtoPolynomialEncoderGhost)
    (pb : ProtoPolynomialEncoder)
    (hlen_lt : polynomialEncoderPBEncodedLen pb < 2 ^ 64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = encA)
    (hcs : MsgEnc48CalleeSaved s0 s)
    (hP : P = (Poly.protoPolynomialEncoderPinnedAt A g encA pb ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (ptsElems polysElems : List (BitVec 64 × List (BitVec 8))),
      ptsElems.map Prod.snd = pb.pts → pb.pts.length * 24 < 2 ^ 63 →
      polysElems.map Prod.snd = pb.polys → pb.polys.length * 24 < 2 ^ 63 →
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 (polynomialEncoderPBEncodedLen pb) →
      CalleeSavedPreserved s sm → MsgEnc48CalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((polyEncoderElemsAt encA g pb ptsElems polysElems ∗
          polyEncoderRestAt A encA g ptsElems polysElems ∗
          stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_48_aligned halign
  have hst : stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) =
      memRegion (sp - 48#64 - BitVec.ofNat 64 (encodeRepeatedStackOf resStack)) 80 ∗
      (memRegion (sp - 48#64 - BitVec.ofNat 64 (0x30 + resStack)) (32 + resStack) ∗
        stackAt (sp - 48#64) polyEncodedLenStack) := by
    rw [stackAt_encodeRepeated_eq_varint hres (sp - 48#64),
      stackAt_varint_eq_stack16 (by omega) (sp - 48#64)]
  refine SepWPp.call_cs (x := PinnedEncLenGhost.mk encA g pb)
    (F := memRegion (sp - 48#64 - BitVec.ofNat 64 (encodeRepeatedStackOf resStack)) 80 ∗
      memRegion (sp - 48#64 - BitVec.ofNat 64 (0x30 + resStack)) (32 + resStack) ∗ F)
    hencLen hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, hst] at hm
    simp only [withMsgEnc48CS, polynomialEncoderEncodedLenElemsOutSpec,
      polynomialEncoderEncodedLenPinnedSpec, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hlen_lt⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [withMsgEnc48CS, polynomialEncoderEncodedLenElemsOutSpec,
      sepConj_assoc, satisfies_pure_sepConj] at hm
    exact False.elim hm.1
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withMsgEnc48CS, polynomialEncoderEncodedLenElemsOutSpec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx0m, htrm⟩ => ?_
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun ptsElems => ?_
    refine SepWPp.exists_elim fun polysElems => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hpts_eq, hpts_lt, hpolys_eq, hpolys_lt⟩ => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPp.weaken_pre ?_
      (hnext sm ptsElems polysElems hpts_eq hpts_lt hpolys_eq hpolys_lt
        hpcm hrunm hspm htrm' hx0m hcsm
        (hcs.trans (MsgEnc48CalleeSaved.of_calleeSavedPreserved hcsm hinv_call)))
    rw [hst]
    exact Entails.of_eq (by ac_rfl)

/-! ## 4. Specifications & Symbol Address Lemmas for `PolynomialEncoder::encode` -/

/-- Pinned ghost inputs for `prost::encoding::message::encode::<PolynomialEncoder, Vec<u8>>`. -/
structure EncodePolyEncoderPinnedGhost where
  encA : BitVec 64
  g    : Poly.ProtoPolynomialEncoderGhost
  enc  : ProtoPolynomialEncoder
  v    : BitVec 64
  cap  : BitVec 64
  ptr  : BitVec 64
  bs   : List (BitVec 8)

/-- Unpinned ghost inputs for `prost::encoding::message::encode::<PolynomialEncoder, Vec<u8>>`. -/
structure EncodePolyEncoderGhost where
  encA : BitVec 64
  enc  : ProtoPolynomialEncoder
  v    : BitVec 64
  cap  : BitVec 64
  ptr  : BitVec 64
  bs   : List (BitVec 8)

/-- Pinned specification of `prost::encoding::message::encode::<PolynomialEncoder, Vec<u8>>`
(`[local#1, 2]`), parameterized by `resStack`. Callers establish `x.enc.pts.length < 2 ^ 58`,
`x.enc.polys.length < 2 ^ 58`, and either spare capacity
(`x.bs.length + (encodePolyEncoderMsg x.enc).length ≤ x.cap.toNat`) or the growth bound
`x.bs.length + (encodePolyEncoderMsg x.enc).length + 10 < 2 ^ 62`. -/
def encodePolyEncoderPinnedSpecOf (resStack : Nat) (A : RustAlloc) :
    Spec EncodePolyEncoderPinnedGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.encA ∧
      s.readReg64 .x1 = x.v ∧
      x.enc.pts.length < 2 ^ 58 ∧
      x.enc.polys.length < 2 ^ 58 ∧
      (x.bs.length + (encodePolyEncoderMsg x.enc).length ≤ x.cap.toNat ∨
        x.bs.length + (encodePolyEncoderMsg x.enc).length + 10 < 2 ^ 62)⌝ ∗
      Poly.protoPolynomialEncoderPinnedAt A x.g x.encA x.enc ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp (msgEnc48RepeatedStackOf resStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      Poly.protoPolynomialEncoderPinnedAt A x.g x.encA x.enc ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodePolyEncoderMsg x.enc).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A x.v cap' ptr' (x.bs ++ encodePolyEncoderMsg x.enc)) ∗
      A.pool ∗ stackAt s0.sp (msgEnc48RepeatedStackOf resStack)
  onPanic := fun _ s0 sf => msgEncOnPanic s0 sf

/-- Unpinned specification of `prost::encoding::message::encode::<PolynomialEncoder, Vec<u8>>`
(`[local#1, 2]`), parameterized by `resStack`. -/
def encodePolyEncoderSpecOf (resStack : Nat) (A : RustAlloc) :
    Spec EncodePolyEncoderGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.encA ∧
      s.readReg64 .x1 = x.v ∧
      x.enc.pts.length < 2 ^ 58 ∧
      x.enc.polys.length < 2 ^ 58 ∧
      (x.bs.length + (encodePolyEncoderMsg x.enc).length ≤ x.cap.toNat ∨
        x.bs.length + (encodePolyEncoderMsg x.enc).length + 10 < 2 ^ 62)⌝ ∗
      Poly.protoPolynomialEncoderAt A x.encA x.enc ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp (msgEnc48RepeatedStackOf resStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      Poly.protoPolynomialEncoderAt A x.encA x.enc ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodePolyEncoderMsg x.enc).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A x.v cap' ptr' (x.bs ++ encodePolyEncoderMsg x.enc)) ∗
      A.pool ∗ stackAt s0.sp (msgEnc48RepeatedStackOf resStack)
  onPanic := fun _ s0 sf => msgEncOnPanic s0 sf

abbrev encodePolyEncoderPinnedSpec (A : RustAlloc) : Spec EncodePolyEncoderPinnedGhost :=
  encodePolyEncoderPinnedSpecOf doReserveStack A

abbrev encodePolyEncoderSpec (A : RustAlloc) : Spec EncodePolyEncoderGhost :=
  encodePolyEncoderSpecOf doReserveStack A

abbrev encodePolyEncoderPinnedSpecX (A : RustAlloc) : Spec EncodePolyEncoderPinnedGhost :=
  encodePolyEncoderPinnedSpecOf doReserveStackX A

abbrev encodePolyEncoderSpecX (A : RustAlloc) : Spec EncodePolyEncoderGhost :=
  encodePolyEncoderSpecOf doReserveStackX A

def EncodePolyEncoder1PinnedOkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder1Name)
    (encodePolyEncoderPinnedSpec A)

def EncodePolyEncoder1OkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder1Name)
    (encodePolyEncoderSpec A)

def EncodePolyEncoder1PinnedOkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr encodePolyEncoder1Name)
    ((encodePolyEncoderPinnedSpecX A).inImage img)

def EncodePolyEncoder1OkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr encodePolyEncoder1Name)
    ((encodePolyEncoderSpecX A).inImage img)

def EncodePolyEncoder2PinnedOkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder2Name)
    (encodePolyEncoderPinnedSpec A)

def EncodePolyEncoder2OkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder2Name)
    (encodePolyEncoderSpec A)

def EncodePolyEncoder2PinnedOkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr encodePolyEncoder2Name)
    ((encodePolyEncoderPinnedSpecX A).inImage img)

def EncodePolyEncoder2OkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr encodePolyEncoder2Name)
    ((encodePolyEncoderSpecX A).inImage img)

theorem polyEncoder_post_unpinned_of_pinned {resStack : Nat} {A : RustAlloc}
    {x : EncodePolyEncoderGhost} {g : Poly.ProtoPolynomialEncoderGhost} {s0 sf : State} {R : SepProp}
    (hq : sf.mem ⊨ (encodePolyEncoderPinnedSpecOf resStack A).post
      ⟨x.encA, g, x.enc, x.v, x.cap, x.ptr, x.bs⟩ s0 sf ∗ R) :
    sf.mem ⊨ (encodePolyEncoderSpecOf resStack A).post x s0 sf ∗ R := by
  dsimp only [encodePolyEncoderPinnedSpecOf] at hq
  dsimp only [encodePolyEncoderSpecOf]
  let Rest : SepProp := ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
      ⌜x.cap.toNat ≤ cap'.toNat ∧
        (x.bs.length + (encodePolyEncoderMsg x.enc).length ≤ x.cap.toNat → cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
        vecU8At A x.v cap' ptr' (x.bs ++ encodePolyEncoderMsg x.enc)) ∗
    A.pool ∗ stackAt s0.sp (msgEnc48RepeatedStackOf resStack) ∗ R
  have hq' : sf.mem ⊨ Poly.protoPolynomialEncoderPinnedAt A g x.encA x.enc ∗ Rest := by
    convert hq using 1; dsimp only [Rest]; ac_rfl
  have hgoal : sf.mem ⊨ Poly.protoPolynomialEncoderAt A x.encA x.enc ∗ Rest := by
    rw [protoPolynomialEncoderAt_eq_exists_pinned, sepExists_sepConj_left, satisfies_sepExists]
    exact ⟨g, hq'⟩
  convert hgoal using 1; dsimp only [Rest]; ac_rfl

theorem polyEncoder_unpinned_of_pinned {resStack : Nat} {prog : Program} {entry : BitVec 64}
    {A : RustAlloc} (hpinned : subroutine_ok prog entry (encodePolyEncoderPinnedSpecOf resStack A)) :
    subroutine_ok prog entry (encodePolyEncoderSpecOf resStack A) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  dsimp only [encodePolyEncoderSpecOf] at hpre
  rw [protoPolynomialEncoderAt_eq_exists_pinned] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  refine (hpinned.to_outcome ⟨x.encA, g, x.enc, x.v, x.cap, x.ptr, x.bs⟩ R s0 hpc hrun hpre hsp).mono_outcome ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | hrest)
  · exact Or.inl ⟨hret, hcc, polyEncoder_post_unpinned_of_pinned hq⟩
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr hrest)

theorem polyEncoder_unpinned_of_pinned_x {resStack : Nat} {img : Obj.Image}
    {prog : Program} {entry : BitVec 64} {A : RustAlloc}
    (hpinned : subroutine_ok prog entry ((encodePolyEncoderPinnedSpecOf resStack A).inImage img)) :
    subroutine_ok prog entry ((encodePolyEncoderSpecOf resStack A).inImage img) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  rw [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre; obtain ⟨hinv0, hpre⟩ := hpre
  dsimp only [encodePolyEncoderSpecOf] at hpre
  rw [protoPolynomialEncoderAt_eq_exists_pinned] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  have hpre' : s0.mem ⊨ ((encodePolyEncoderPinnedSpecOf resStack A).inImage img).pre
      ⟨x.encA, g, x.enc, x.v, x.cap, x.ptr, x.bs⟩ s0 ∗ R := by
    rw [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj]; exact ⟨hinv0, hpre⟩
  refine (hpinned.to_outcome ⟨x.encA, g, x.enc, x.v, x.cap, x.ptr, x.bs⟩ R s0 hpc hrun hpre' hsp).mono_outcome ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | hrest)
  · exact Or.inl ⟨hret, hcc, polyEncoder_post_unpinned_of_pinned hq⟩
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr hrest)

theorem encodePolyEncoder1_encodedLen1_fnAddr_eq (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder1Name + 5884#64 =
      (tripleRatchetProgAtExt b ext).fnAddr polynomialEncoderEncodedLenLocal1Name := by
  have h1 := libsignalSessionCode_fnOff_0x37774
  have h2 := libsignalSessionCode_fnOff_0x38e70
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, encodePolyEncoder1Name,
    polynomialEncoderEncodedLenLocal1Name, h1, h2]
  bv_omega

theorem encodePolyEncoder1_encodeVarint2_fnAddr_eq (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder1Name + 18446744073709547416#64 =
      (tripleRatchetProgAtExt b ext).fnAddr encodeVarint2Name := by
  have h1 := libsignalSessionCode_fnOff_0x37774
  have h2 := libsignalSessionCode_fnOff_0x3670c
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, encodePolyEncoder1Name,
    encodeVarint2Name, h1, h2]
  bv_omega

theorem encodePolyEncoder1_encodeRepeated1_fnAddr_eq (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder1Name + 18446744073709545712#64 =
      (tripleRatchetProgAtExt b ext).fnAddr encodeRepeated1Name := by
  have h1 := libsignalSessionCode_fnOff_0x37774
  have h2 := libsignalSessionCode_fnOff_0x36064
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, encodePolyEncoder1Name,
    encodeRepeated1Name, h1, h2]
  bv_omega

theorem encodePolyEncoder1_doReserve2_fnAddr_eq (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder1Name + 2284#64 =
      (tripleRatchetProgAtExt b ext).fnAddr doReserve2Name := by
  have h1 := libsignalSessionCode_fnOff_0x37774
  have h2 := libsignalSessionCode_fnOff_0x38060
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, encodePolyEncoder1Name,
    doReserve2Name, h1, h2]
  bv_omega

theorem encodePolyEncoder2_encodedLen2_fnAddr_eq (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder2Name + 82712#64 =
      (tripleRatchetProgAtExt b ext).fnAddr polynomialEncoderEncodedLenLocal2Name := by
  have h1 := libsignalSessionCode_fnOff_0x4d2dc
  have h2 := libsignalSessionCode_fnOff_0x615f4
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, encodePolyEncoder2Name,
    polynomialEncoderEncodedLenLocal2Name, h1, h2]
  bv_omega

theorem encodePolyEncoder2_encodeVarint4_fnAddr_eq (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder2Name + 18446744073709531196#64 =
      (tripleRatchetProgAtExt b ext).fnAddr encodeVarint4Name := by
  have h1 := libsignalSessionCode_fnOff_0x4d2dc
  have h2 := libsignalSessionCode_fnOff_0x48318
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, encodePolyEncoder2Name,
    encodeVarint4Name, h1, h2]
  bv_omega

theorem encodePolyEncoder2_encodeRepeated2_fnAddr_eq (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder2Name + 18446744073709529452#64 =
      (tripleRatchetProgAtExt b ext).fnAddr encodeRepeated2Name := by
  have h1 := libsignalSessionCode_fnOff_0x4d2dc
  have h2 := libsignalSessionCode_fnOff_0x47c48
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, encodePolyEncoder2Name,
    encodeRepeated2Name, h1, h2]
  bv_omega

theorem encodePolyEncoder2_doReserve7_fnAddr_eq (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder2Name + 2508#64 =
      (tripleRatchetProgAtExt b ext).fnAddr doReserve7Name := by
  have h1 := libsignalSessionCode_fnOff_0x4d2dc
  have h2 := libsignalSessionCode_fnOff_0x4dca8
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, encodePolyEncoder2Name,
    doReserve7Name, h1, h2]
  bv_omega

/-! ## 5. Instruction Fetch Infrastructure & Shared Stepping Lemmas -/

def IsPolyEncoderEncodeEntry (b : BitVec 64) (ext : String → Option (State → State))
    (entry : BitVec 64) : Prop :=
  (tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder1Name = entry ∨
    (tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder2Name = entry

theorem polyEncoderEncode_fetch_entry {b : BitVec 64} {ext : String → Option (State → State)}
    {entry : BitVec 64} (hfn : IsPolyEncoderEncodeEntry b ext entry) {ins : Instr}
    (h1 : (tripleRatchetProgAtExt b ext).fetch
      ((tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder1Name) = some ins)
    (h2 : (tripleRatchetProgAtExt b ext).fetch
      ((tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder2Name) = some ins) :
    (tripleRatchetProgAtExt b ext).fetch entry = some ins := by
  rcases hfn with rfl | rfl
  · exact h1
  · exact h2

theorem polyEncoderEncode_fetch_add {b : BitVec 64} {ext : String → Option (State → State)}
    {entry : BitVec 64} (hfn : IsPolyEncoderEncodeEntry b ext entry) {k : Nat} {ins : Instr}
    (h1 : (tripleRatchetProgAtExt b ext).fetch
      ((tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder1Name + BitVec.ofNat 64 k) = some ins)
    (h2 : (tripleRatchetProgAtExt b ext).fetch
      ((tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder2Name + BitVec.ofNat 64 k) = some ins) :
    (tripleRatchetProgAtExt b ext).fetch (entry + BitVec.ofNat 64 k) = some ins := by
  rcases hfn with rfl | rfl
  · exact h1
  · exact h2

open Lean Elab Tactic in
elab "polyEncoder_fetches_range " b:term:max H:term:max _entry:term:max hfn:ident
    kStart:num kEnd:num : tactic => do
  let off1 := 0x37774
  let off2 := 0x4d2dc
  let kStart := kStart.getNat
  let kEnd := kEnd.getNat
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  let fnOff1 := mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x37774
  let fnOff2 := mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x4d2dc
  for i in [kStart / 4 : kEnd / 4] do
    let k := 4 * i
    let dec1 := mkIdent (`CryptoVerification.SpqrV1.Prost.MessageEncode |>.str
      s!"libsignalSessionBin_decode_0x{String.ofList (Nat.toDigits 16 (off1 + k))}")
    let dec2 := mkIdent (`CryptoVerification.SpqrV1.Prost.MessageEncode |>.str
      s!"libsignalSessionBin_decode_0x{String.ofList (Nat.toDigits 16 (off2 + k))}")
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := polyEncoderEncode_fetch_entry $hfn
          ($fetchEntry (b := $b) (H := $H) $fnOff1 (by decide) $dec1)
          ($fetchEntry (b := $b) (H := $H) $fnOff2 (by decide) $dec2)))
    else
      evalTactic (← `(tactic|
        have := polyEncoderEncode_fetch_add $hfn (k := $kq)
          ($fetchAdd (b := $b) (H := $H) (k := $kq) $fnOff1 (by decide) $dec1)
          ($fetchAdd (b := $b) (H := $H) (k := $kq) $fnOff2 (by decide) $dec2)))

open Lean Elab Tactic in
elab "polyEncoder1_fetches_range " b:term:max H:term:max _entry:term:max
    kStart:num kEnd:num : tactic => do
  let off := 0x37774
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  let fnOff := mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x37774
  for i in [kStart.getNat / 4 : kEnd.getNat / 4] do
    let k := 4 * i
    let dec := mkIdent (`CryptoVerification.SpqrV1.Prost.MessageEncode |>.str
      s!"libsignalSessionBin_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic| have := $fetchEntry (b := $b) (H := $H) $fnOff (by decide) $dec))
    else
      evalTactic (← `(tactic| have := $fetchAdd (b := $b) (H := $H) (k := $kq) $fnOff (by decide) $dec))

open Lean Elab Tactic in
elab "polyEncoder2_fetches_range " b:term:max H:term:max _entry:term:max
    kStart:num kEnd:num : tactic => do
  let off := 0x4d2dc
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  let fnOff := mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x4d2dc
  for i in [kStart.getNat / 4 : kEnd.getNat / 4] do
    let k := 4 * i
    let dec := mkIdent (`CryptoVerification.SpqrV1.Prost.MessageEncode |>.str
      s!"libsignalSessionBin_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic| have := $fetchEntry (b := $b) (H := $H) $fnOff (by decide) $dec))
    else
      evalTactic (← `(tactic| have := $fetchAdd (b := $b) (H := $H) (k := $kq) $fnOff (by decide) $dec))

/-- Shared prologue (`+0x000..+0x014`, offsets `0..20`):
allocates the 48-byte stack frame, saves `x29, x30, x21, x20, x19`, and sets `x19 = v`. -/
theorem step_polyEncoder_prologue {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    (b : BitVec 64) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : IsPolyEncoderEncodeEntry b ext entry) (encA v sp : BitVec 64)
    {s0 s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hhs0 : s = s0) (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = encA) (hx1 : s.readReg64 .x1 = v) (hcs : MsgEnc48CalleeSaved s0 s)
    (hP : P = stackAt sp (msgEnc48RepeatedStackOf resStack) ∗ F)
    (hnext : ∀ (sm : State) (sv3 : BitVec 64),
      sm.pc = entry + 20#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = encA → sm.readReg64 .x1 = v → sm.readReg64 .x19 = v →
      MsgEnc48CalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
          msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  polyEncoder_fetches_range b (Rust.withPanics ext) entry hfn 0 20
  examples_hide_fetches; subst hP hhs0
  have hsp_aligned := sp_sub_48_aligned halign
  rw [stackAt_msgEnc48_repeated hres sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun sv0 => SepWPp.exists_elim fun sv1 =>
    SepWPp.exists_elim fun sv2 => SepWPp.exists_elim fun sv3 =>
    SepWPp.exists_elim fun sv4 => SepWPp.exists_elim fun sv5 => ?_
  apply SepWPp.of_sepWP_cs (mid := entry + 20#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
  refine SepWPp.weaken_pre (by dsimp only [msgEnc48SavedFrame]; exact Entails.of_eq (by ac_rfl))
    (hnext _ sv3
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv))

/-- Shared header tag push (`+0x028..+0x040`, offsets `40..64`):
given `curBs.length < curCap.toNat`, pushes `0x12#8` (`tag = 2`, `lengthDelimited`) to `buf`
and sets `x0 = encA`. -/
theorem step_polyEncoder_push_hdr_tag (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : IsPolyEncoderEncodeEntry b ext entry)
    (encA v curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8)) (hlt : curBs.length < curCap.toNat)
    {s0 s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 40#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = encA) (hcs : MsgEnc48CalleeSaved s0 s)
    (hP : P = vecU8At A v curCap curPtr curBs ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = entry + 64#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = encA → sm.readReg64 .x19 = v → sm.readReg64 .x20 = encA →
      MsgEnc48CalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        (vecU8At A v curCap curPtr (curBs ++ [0x12#8]) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  polyEncoder_fetches_range b (Rust.withPanics ext) entry hfn 40 64
  examples_hide_fetches; subst hP
  rw [vecU8At_open_one A v curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_cs (mid := entry + 64#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
  refine SepWPp.weaken_pre (by rw [← vecU8At_close_one A v curCap curPtr curBs 0x12#8 hlt]; exact Entails.of_eq (by ac_rfl))
    (hnext _
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv))

theorem step_polyEncoder_mov_x1_x19_68 (b : BitVec 64) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : IsPolyEncoderEncodeEntry b ext entry) (val encA v sp : BitVec 64)
    {s0 s : State} {R : SepProp} {ret : BitVec 64} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 68#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = val)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = encA) (hcs : MsgEnc48CalleeSaved s0 s)
    (hnext : ∀ (sm : State),
      sm.pc = entry + 72#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = val → sm.readReg64 .x1 = v → sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = encA → MsgEnc48CalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm P Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  polyEncoder_fetches_range b (Rust.withPanics ext) entry hfn 68 72
  examples_hide_fetches
  apply SepWPp.of_sepWP_cs (mid := entry + 72#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
  exact hnext _
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) hinv)

/-- Shared `idx` load and zero check (`+0x04c..+0x054`, offsets `76..84`):
loads `w0 = [x20, #0x30]` (`pb.idx`) and branches to `entry + 128#64` if `pb.idx == 0#32`,
else falls through to `entry + 84#64`. -/
theorem step_polyEncoder_check_idx (b : BitVec 64) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : IsPolyEncoderEncodeEntry b ext entry)
    (encA v sp : BitVec 64) (g : Poly.ProtoPolynomialEncoderGhost) (pb : ProtoPolynomialEncoder)
    (ptsElems polysElems : List (BitVec 64 × List (BitVec 8)))
    {s0 s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 76#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = encA)
    (hcs : MsgEnc48CalleeSaved s0 s) (hP : P = polyEncoderElemsAt encA g pb ptsElems polysElems ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = entry + (if pb.idx == 0#32 then 128#64 else 84#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = pb.idx.zeroExtend 64 → sm.readReg64 .x19 = v → sm.readReg64 .x20 = encA →
      MsgEnc48CalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        (polyEncoderElemsAt encA g pb ptsElems polysElems ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  polyEncoder_fetches_range b (Rust.withPanics ext) entry hfn 76 84
  examples_hide_fetches; subst hP; dsimp only [polyEncoderElemsAt]
  cases hidx : (pb.idx == 0#32)
  · have hidx64 : (BitVec.zeroExtend 64 pb.idx == 0#64) = false := by
      rw [EncodedLen.zeroExtend64_beq_zero32, hidx]
    apply SepWPp.of_sepWP_cs (mid := entry + 84#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    refine SepWPp.weaken_pre (by dsimp only [polyEncoderElemsAt]; exact Entails.of_eq (by ac_rfl))
      (hnext _ (by simp only [Bool.false_eq_true, ↓reduceIte, arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv))
  · have hidx64 : (BitVec.zeroExtend 64 pb.idx == 0#64) = true := by
      rw [EncodedLen.zeroExtend64_beq_zero32, hidx]
    apply SepWPp.of_sepWP_cs (mid := entry + 128#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    refine SepWPp.weaken_pre (by dsimp only [polyEncoderElemsAt]; exact Entails.of_eq (by ac_rfl))
      (hnext _ (by simp only [↓reduceIte, arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv))

/-- Shared `idx` tag push (`+0x064..+0x07c`, offsets `100..124`):
given `curBs.length < curCap.toNat`, pushes `0x08#8` (`tag = 1`, varint) to `buf`
and sets `x1 = v`, preserving `x0 = pb.idx.zeroExtend 64`. -/
theorem step_polyEncoder_push_idx_tag (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : IsPolyEncoderEncodeEntry b ext entry)
    (encA v curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8))
    (pb : ProtoPolynomialEncoder) (hlt : curBs.length < curCap.toNat)
    {s0 s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 100#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = pb.idx.zeroExtend 64)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = encA) (hcs : MsgEnc48CalleeSaved s0 s)
    (hP : P = vecU8At A v curCap curPtr curBs ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = entry + 124#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = pb.idx.zeroExtend 64 → sm.readReg64 .x1 = v →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = encA → MsgEnc48CalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        (vecU8At A v curCap curPtr (curBs ++ [0x08#8]) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  polyEncoder_fetches_range b (Rust.withPanics ext) entry hfn 100 124
  examples_hide_fetches; subst hP
  rw [vecU8At_open_one A v curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_cs (mid := entry + 124#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
  refine SepWPp.weaken_pre (by rw [← vecU8At_close_one A v curCap curPtr curBs 0x08#8 hlt]; exact Entails.of_eq (by ac_rfl))
    (hnext _
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv))

/-- Shared `pts` argument setup (`+0x080..+0x08c`, offsets `128..140`):
loads `x1 = g.pts.ptr`, `x2 = BitVec.ofNat 64 pb.pts.length`, sets `w0 = 2#32`, `x3 = v`. -/
theorem step_polyEncoder_prep_pts (b : BitVec 64) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : IsPolyEncoderEncodeEntry b ext entry)
    (encA v sp : BitVec 64) (g : Poly.ProtoPolynomialEncoderGhost) (pb : ProtoPolynomialEncoder)
    (ptsElems polysElems : List (BitVec 64 × List (BitVec 8)))
    {s0 s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 128#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = encA)
    (hcs : MsgEnc48CalleeSaved s0 s) (hP : P = polyEncoderElemsAt encA g pb ptsElems polysElems ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = entry + 140#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg32 .x0 = 2#32 → sm.readReg64 .x1 = g.pts.ptr →
      sm.readReg64 .x2 = BitVec.ofNat 64 pb.pts.length → sm.readReg64 .x3 = v →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = encA → MsgEnc48CalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        (polyEncoderElemsAt encA g pb ptsElems polysElems ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  polyEncoder_fetches_range b (Rust.withPanics ext) entry hfn 128 140
  examples_hide_fetches; subst hP; dsimp only [polyEncoderElemsAt]
  apply SepWPp.of_sepWP_cs (mid := entry + 140#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
  refine SepWPp.weaken_pre (by dsimp only [polyEncoderElemsAt]; exact Entails.of_eq (by ac_rfl))
    (hnext _
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by dsimp only [State.readReg32, Reg.x0]; simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv))

/-- Shared `polys` argument setup + frame restore (`+0x090..+0x0a8`, offsets `144..168`):
loads `x1 = g.polys.ptr`, `x2 = BitVec.ofNat 64 pb.polys.length`, sets `w0 = 3#32`, `x3 = v`,
and restores the 48-byte stack frame (`sp = sp`, `lr = s0.readReg64 .lr`), arriving at
`entry + 168#64` (`+0x0a8`, the `b encode_repeated` tailcall). -/
theorem step_polyEncoder_prep_polys_epilogue (b : BitVec 64) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : IsPolyEncoderEncodeEntry b ext entry)
    (encA v sp sv3 : BitVec 64) (g : Poly.ProtoPolynomialEncoderGhost) (pb : ProtoPolynomialEncoder)
    (ptsElems polysElems : List (BitVec 64 × List (BitVec 8)))
    {s0 s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 144#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = encA) (hcs : MsgEnc48CalleeSaved s0 s)
    (hP : P = (polyEncoderElemsAt encA g pb ptsElems polysElems ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = entry + 168#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .lr = s0.readReg64 .lr → sm.readReg32 .x0 = 3#32 →
      sm.readReg64 .x1 = g.polys.ptr → sm.readReg64 .x2 = BitVec.ofNat 64 pb.polys.length →
      sm.readReg64 .x3 = v → CalleeSavedPreserved s0 sm → MsgEnc48CalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((polyEncoderElemsAt encA g pb ptsElems polysElems ∗
          msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  polyEncoder_fetches_range b (Rust.withPanics ext) entry hfn 144 168
  examples_hide_fetches; subst hP
  have hsp_aligned := sp_sub_48_aligned halign
  rcases hcs with ⟨h22, h23, h24, h25, h26, h27, h28, hvregs, hinv0⟩
  dsimp only [polyEncoderElemsAt, msgEnc48SavedFrame]
  apply SepWPp.of_sepWP_cs (mid := entry + 168#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  refine SepWPp.weaken_pre (by dsimp only [polyEncoderElemsAt, msgEnc48SavedFrame]; exact Entails.of_eq (by ac_rfl))
    (hnext _
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by dsimp only [State.readReg32, Reg.x0]; simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by epochEncLen_cc_close)
      ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *], hinv0.trans hinv1⟩)

end CryptoVerification.SpqrV1.Prost.MessageEncode

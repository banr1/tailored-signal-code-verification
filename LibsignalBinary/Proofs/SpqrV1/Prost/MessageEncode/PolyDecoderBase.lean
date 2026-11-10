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
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncoderBase
import ProofLib.SepLogic.WPp

/-!
# Shared Specification, Pure Lemmas, and Stepping Helpers for `PolynomialDecoder::encode`

Covers shared definitions and stepping blocks for:
- `prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialDecoder, alloc::vec::Vec<u8>> [local#1]`
  (`0x37520..0x37690`, 92 insns)
- `prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialDecoder, alloc::vec::Vec<u8>> [local#2]`
  (`0x52544..0x526d4`, 100 insns)
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

/-- Full encoded bytes produced by `prost::encoding::message::encode::<PolynomialDecoder, Vec<u8>>`
for wire tag `tag : BitVec 32` (`w0 = tag`, wire type `lengthDelimited` = `2`). -/
def encodePolyDecoderMsg (tag : BitVec 32) (pb : ProtoPolynomialDecoder) : List (BitVec 8) :=
  Proto.encodeMessage PolynomialDecoder.encodeRaw tag (ProtoPolynomialDecoder.toPB pb)

/-- Header bytes (`Proto.encodeKey tag .lengthDelimited ++ encodeVarint (encoded_len)`) of `PolynomialDecoder::encode`. -/
def polyDecoderHeaderBytes (tag : BitVec 32) (pb : ProtoPolynomialDecoder) : List (BitVec 8) :=
  Proto.encodeKey tag .lengthDelimited ++
    LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 (polynomialDecoderPBEncodedLen pb))

theorem polyDecoder_tag_orr_eq (tag : BitVec 32) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (2#64 ||| BitVec.zeroExtend 64 (tag <<< 3))) =
      ((tag <<< 3) ||| (Proto.WireType.lengthDelimited).toU32).zeroExtend 64 := by
  dsimp [Proto.WireType.toU32]; bv_bits

theorem encodeVarint_polyDecoder_tag_eq_proto (tag : BitVec 32) :
    LibsignalProtoCodec.encodeVarint
      (((tag <<< 3) ||| (Proto.WireType.lengthDelimited).toU32).zeroExtend 64) =
      Proto.encodeKey tag .lengthDelimited := by
  rw [Proto.encodeKey, protoEncodeVarint_eq_codec]

theorem bs_append_boolField_4_true (bs : List (BitVec 8)) :
    (bs ++ [0x20#8]) ++ [0x01#8] = bs ++ Proto.encodeBoolField 4#32 true := by
  rw [protoEncodeBoolField_4_true, List.append_assoc]; rfl

theorem bs_append_boolField_4_false (bs : List (BitVec 8)) :
    bs ++ Proto.encodeBoolField 4#32 false = bs := by
  rw [protoEncodeBoolField_4_false, List.append_nil]

theorem encodePolyDecoderMsg_eq (tag : BitVec 32) (pb : ProtoPolynomialDecoder) :
    encodePolyDecoderMsg tag pb =
      polyDecoderHeaderBytes tag pb ++ Proto.encodeUint32Field 1#32 pb.ptsNeeded ++
        Proto.encodeUint32Field 2#32 pb.polys ++ Varint.encodeRepeatedBytes 3 pb.pts ++
        Proto.encodeBoolField 4#32 pb.isComplete := by
  have hlen : (PolynomialDecoder.encodeRaw (ProtoPolynomialDecoder.toPB pb)).length =
      polynomialDecoderPBEncodedLen pb := polynomialDecoderPBEncodedLen_eq_proto pb
  dsimp only [encodePolyDecoderMsg, Proto.encodeMessage, polyDecoderHeaderBytes]
  rw [protoEncodeVarint_eq_codec, hlen]
  dsimp only [PolynomialDecoder.encodeRaw, ProtoPolynomialDecoder.toPB]
  rw [← varintEncodeRepeatedBytes_3_eq_proto]; simp only [List.append_assoc]

theorem bs0_append_encodePolyDecoderMsg (bs0 : List (BitVec 8)) (tag : BitVec 32)
    (pb : ProtoPolynomialDecoder) :
    bs0 ++ encodePolyDecoderMsg tag pb =
      ((((bs0 ++ polyDecoderHeaderBytes tag pb) ++
        Proto.encodeUint32Field 1#32 pb.ptsNeeded) ++
        Proto.encodeUint32Field 2#32 pb.polys) ++
        Varint.encodeRepeatedBytes 3 pb.pts) ++
        Proto.encodeBoolField 4#32 pb.isComplete := by
  rw [encodePolyDecoderMsg_eq]; simp only [List.append_assoc]

theorem bs0_append_polyDecoderHeaderBytes (bs0 : List (BitVec 8)) (tag : BitVec 32)
    (pb : ProtoPolynomialDecoder) :
    (bs0 ++ Proto.encodeKey tag .lengthDelimited) ++
      LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 (polynomialDecoderPBEncodedLen pb)) =
    bs0 ++ polyDecoderHeaderBytes tag pb := by
  rw [polyDecoderHeaderBytes, List.append_assoc]

theorem polyDecoderHeaderBytes_len_bounds (tag : BitVec 32) (pb : ProtoPolynomialDecoder) :
    (polyDecoderHeaderBytes tag pb).length =
      (Proto.encodeKey tag .lengthDelimited).length +
        (LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 (polynomialDecoderPBEncodedLen pb))).length ∧
    1 ≤ (Proto.encodeKey tag .lengthDelimited).length ∧
    2 ≤ (polyDecoderHeaderBytes tag pb).length := by
  have hk := (Varint.encodeVarint_length_bounds
    (((tag <<< 3) ||| (Proto.WireType.lengthDelimited).toU32).zeroExtend 64)).1
  rw [encodeVarint_polyDecoder_tag_eq_proto] at hk
  have hb := (Varint.encodeVarint_length_bounds (BitVec.ofNat 64 (polynomialDecoderPBEncodedLen pb))).1
  rw [polyDecoderHeaderBytes, List.length_append]; omega

theorem bs_append_ptsNeeded_of_ne_zero (bs : List (BitVec 8)) (pb : ProtoPolynomialDecoder)
    (hpn : (pb.ptsNeeded == 0#32) = false) :
    (bs ++ [0x08#8]) ++ LibsignalProtoCodec.encodeVarint (pb.ptsNeeded.zeroExtend 64) =
      bs ++ Proto.encodeUint32Field 1#32 pb.ptsNeeded := by
  rw [protoEncodeUint32Field_1_of_ne_zero (beq_eq_false_iff_ne.mp hpn), List.append_assoc]

theorem bs_append_ptsNeeded_of_zero (bs : List (BitVec 8)) (pb : ProtoPolynomialDecoder)
    (hpn : (pb.ptsNeeded == 0#32) = true) :
    bs ++ Proto.encodeUint32Field 1#32 pb.ptsNeeded = bs := by
  rw [eq_of_beq hpn, protoEncodeUint32Field_zero, List.append_nil]

theorem ptsNeeded_field_len_of_ne_zero (pb : ProtoPolynomialDecoder)
    (hpn : (pb.ptsNeeded == 0#32) = false) :
    (Proto.encodeUint32Field 1#32 pb.ptsNeeded).length =
      1 + (LibsignalProtoCodec.encodeVarint (pb.ptsNeeded.zeroExtend 64)).length ∧
    2 ≤ (Proto.encodeUint32Field 1#32 pb.ptsNeeded).length := by
  have hb := (Varint.encodeVarint_length_bounds (pb.ptsNeeded.zeroExtend 64)).1
  rw [protoEncodeUint32Field_1_of_ne_zero (beq_eq_false_iff_ne.mp hpn),
    List.length_append, List.length_singleton]; omega

theorem bs_append_polys_of_ne_zero (bs : List (BitVec 8)) (pb : ProtoPolynomialDecoder)
    (hpl : (pb.polys == 0#32) = false) :
    (bs ++ [0x10#8]) ++ LibsignalProtoCodec.encodeVarint (pb.polys.zeroExtend 64) =
      bs ++ Proto.encodeUint32Field 2#32 pb.polys := by
  rw [protoEncodeUint32Field_2_of_ne_zero (beq_eq_false_iff_ne.mp hpl), List.append_assoc]

theorem bs_append_polys_of_zero (bs : List (BitVec 8)) (pb : ProtoPolynomialDecoder)
    (hpl : (pb.polys == 0#32) = true) :
    bs ++ Proto.encodeUint32Field 2#32 pb.polys = bs := by
  rw [eq_of_beq hpl, protoEncodeUint32Field_zero, List.append_nil]

theorem polys_field_len_of_ne_zero (pb : ProtoPolynomialDecoder)
    (hpl : (pb.polys == 0#32) = false) :
    (Proto.encodeUint32Field 2#32 pb.polys).length =
      1 + (LibsignalProtoCodec.encodeVarint (pb.polys.zeroExtend 64)).length ∧
    2 ≤ (Proto.encodeUint32Field 2#32 pb.polys).length := by
  have hb := (Varint.encodeVarint_length_bounds (pb.polys.zeroExtend 64)).1
  rw [protoEncodeUint32Field_2_of_ne_zero (beq_eq_false_iff_ne.mp hpl),
    List.length_append, List.length_singleton]; omega

theorem encodePolyDecoderMsg_len_split (tag : BitVec 32) (pb : ProtoPolynomialDecoder) :
    (encodePolyDecoderMsg tag pb).length =
      (polyDecoderHeaderBytes tag pb).length +
        (Proto.encodeUint32Field 1#32 pb.ptsNeeded).length +
        (Proto.encodeUint32Field 2#32 pb.polys).length +
        (Varint.encodeRepeatedBytes 3 pb.pts).length +
        (Proto.encodeBoolField 4#32 pb.isComplete).length := by
  rw [encodePolyDecoderMsg_eq, List.length_append, List.length_append,
    List.length_append, List.length_append]

theorem polynomialDecoderPBEncodedLen_le_msg_len (tag : BitVec 32) (pb : ProtoPolynomialDecoder) :
    polynomialDecoderPBEncodedLen pb + 2 ≤ (encodePolyDecoderMsg tag pb).length := by
  have hraw : (PolynomialDecoder.encodeRaw (ProtoPolynomialDecoder.toPB pb)).length =
      polynomialDecoderPBEncodedLen pb :=
    polynomialDecoderPBEncodedLen_eq_proto pb
  have h1 : (PolynomialDecoder.encodeRaw (ProtoPolynomialDecoder.toPB pb)).length =
      (Proto.encodeUint32Field 1#32 pb.ptsNeeded).length +
        (Proto.encodeUint32Field 2#32 pb.polys).length +
        (Varint.encodeRepeatedBytes 3 pb.pts).length +
        (Proto.encodeBoolField 4#32 pb.isComplete).length := by
    dsimp only [PolynomialDecoder.encodeRaw, ProtoPolynomialDecoder.toPB]
    rw [← varintEncodeRepeatedBytes_3_eq_proto]
    simp only [List.length_append]
  have hhdr := (polyDecoderHeaderBytes_len_bounds tag pb).2.2
  rw [encodePolyDecoderMsg_len_split]
  omega

theorem polyDecoder_pts_lt_of_msg_len_lt {tag : BitVec 32} {pb : ProtoPolynomialDecoder}
    (h : (encodePolyDecoderMsg tag pb).length < 2 ^ 59) :
    pb.pts.length < 2 ^ 58 := by
  have h1 := encodeRepeatedBytes_length_ge_two_mul 3 pb.pts
  rw [encodePolyDecoderMsg_len_split] at h
  omega

/-! ## 2. Unpacking `Poly.protoPolynomialDecoderPinnedAt` via `satisfies_vecVecU8PinnedAt_iff` -/

/-- Active fields of `ProtoPolynomialDecoder` accessed during `+56..+248` of `PolynomialDecoder::encode`. -/
def polyDecoderElemsAt (decA : BitVec 64) (g : Poly.ProtoPolynomialDecoderGhost)
    (pb : ProtoPolynomialDecoder)
    (ptsElems : List (BitVec 64 × List (BitVec 8))) : SepProp :=
  ((decA + 8#64) ↦₆₄ g.pts.ptr) ∗
    ((decA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
    ((decA + 24#64) ↦₃₂ pb.ptsNeeded) ∗
    ((decA + 28#64) ↦₃₂ pb.polys) ∗
    ((decA + 32#64) ↦₈ boolByte pb.isComplete) ∗
    repeatedBytesSliceAt g.pts.ptr ptsElems

/-- Framed remainder of `Poly.protoPolynomialDecoderPinnedAt A g decA pb` after extracting
`polyDecoderElemsAt decA g pb ptsElems`. -/
def polyDecoderRestAt (A : RustAlloc) (decA : BitVec 64) (g : Poly.ProtoPolynomialDecoderGhost)
    (ptsElems : List (BitVec 64 × List (BitVec 8))) : SepProp :=
  (decA ↦₆₄ g.pts.cap) ∗
    vecVecU8PinnedRestAt A g.pts ptsElems ∗
    memRegion (decA + 0x21#64) 7

theorem satisfies_protoPolynomialDecoderPinnedAt_iff (A : RustAlloc)
    (g : Poly.ProtoPolynomialDecoderGhost) (decA : BitVec 64) (pb : ProtoPolynomialDecoder)
    (R : SepProp) (m : Memory) :
    (m ⊨ Poly.protoPolynomialDecoderPinnedAt A g decA pb ∗ R) ↔
    ∃ ptsElems : List (BitVec 64 × List (BitVec 8)),
      ptsElems.map Prod.snd = pb.pts ∧ pb.pts.length * 24 < 2 ^ 63 ∧
      (m ⊨ (polyDecoderElemsAt decA g pb ptsElems ∗
        polyDecoderRestAt A decA g ptsElems) ∗ R) := by
  dsimp only [Poly.protoPolynomialDecoderPinnedAt, Poly.protoPolynomialDecoderPtsNeededOff,
    Poly.protoPolynomialDecoderPolysOff, Poly.protoPolynomialDecoderIsCompleteOff,
    Poly.protoPolynomialDecoderPadOff, Poly.protoPolynomialDecoderPadSize,
    polyDecoderElemsAt, polyDecoderRestAt]
  constructor
  · intro hm
    have hm1 : m ⊨ vecVecU8PinnedAt A g.pts decA pb.pts ∗
        (((decA + 24#64) ↦₃₂ pb.ptsNeeded) ∗
          ((decA + 28#64) ↦₃₂ pb.polys) ∗
          ((decA + 32#64) ↦₈ boolByte pb.isComplete) ∗
          memRegion (decA + 33#64) 7 ∗ R) := by
      convert hm using 1; ac_rfl
    rcases (satisfies_vecVecU8PinnedAt_iff A g.pts decA pb.pts _ m).mp hm1 with
      ⟨ptsElems, hpts_eq, hpts_lt, hm2⟩
    refine ⟨ptsElems, hpts_eq, hpts_lt, ?_⟩
    convert hm2 using 1; ac_rfl
  · rintro ⟨ptsElems, hpts_eq, hpts_lt, hm⟩
    have hm1 : m ⊨ ((decA ↦₆₄ g.pts.cap) ∗ ((decA + 8#64) ↦₆₄ g.pts.ptr) ∗
        ((decA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
        repeatedBytesSliceAt g.pts.ptr ptsElems ∗ vecVecU8PinnedRestAt A g.pts ptsElems) ∗
        (((decA + 24#64) ↦₃₂ pb.ptsNeeded) ∗
          ((decA + 28#64) ↦₃₂ pb.polys) ∗
          ((decA + 32#64) ↦₈ boolByte pb.isComplete) ∗
          memRegion (decA + 33#64) 7 ∗ R) := by
      convert hm using 1; ac_rfl
    have hm2 := (satisfies_vecVecU8PinnedAt_iff A g.pts decA pb.pts _ m).mpr
      ⟨ptsElems, hpts_eq, hpts_lt, hm1⟩
    convert hm2 using 1; ac_rfl

/-- Variant of `polynomialDecoderEncodedLenPinnedSpec` whose postcondition unpacks
`Poly.protoPolynomialDecoderPinnedAt` into `polyDecoderElemsAt ∗ polyDecoderRestAt`. -/
def polynomialDecoderEncodedLenElemsOutSpec (A : RustAlloc) :
    Spec PolynomialDecoderEncodedLenPinnedGhost where
  pre := (polynomialDecoderEncodedLenPinnedSpec A).pre
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (polynomialDecoderPBEncodedLen x.m) ∧
      sf.trace = s0.trace⌝ ∗
      (∃∗ ptsElems : List (BitVec 64 × List (BitVec 8)),
        ⌜ptsElems.map Prod.snd = x.m.pts ∧ x.m.pts.length * 24 < 2 ^ 63⌝ ∗
          polyDecoderElemsAt x.a x.g x.m ptsElems ∗
          polyDecoderRestAt A x.a x.g ptsElems) ∗
      stackAt s0.sp polyEncodedLenStack
  onPanic := (polynomialDecoderEncodedLenPinnedSpec A).onPanic
  onExit := (polynomialDecoderEncodedLenPinnedSpec A).onExit

theorem subroutine_ok_polyDecLenElemsOut_of_pinned {prog : Program} {entry : BitVec 64} {A : RustAlloc}
    (h : subroutine_ok prog entry (polynomialDecoderEncodedLenPinnedSpec A)) :
    subroutine_ok prog entry (polynomialDecoderEncodedLenElemsOutSpec A) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  refine h.mono_outcome x R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [polynomialDecoderEncodedLenPinnedSpec] at hq
    dsimp only [polynomialDecoderEncodedLenElemsOutSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨hpure, hq⟩
    refine ⟨hpure, ?_⟩
    have hq' : sf.mem ⊨ Poly.protoPolynomialDecoderPinnedAt A x.g x.a x.m ∗
        (stackAt s0.sp polyEncodedLenStack ∗ R) := by
      convert hq using 1; ac_rfl
    rcases (satisfies_protoPolynomialDecoderPinnedAt_iff A x.g x.a x.m _ sf.mem).mp hq' with
      ⟨ptsElems, hpts_eq, hpts_lt, hm⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨ptsElems, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hpts_eq, hpts_lt⟩, ?_⟩
    convert hm using 1; ac_rfl
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr hrest)

/-- Execute `bl PolynomialDecoder::encoded_len` (via `polynomialDecoderEncodedLenElemsOutSpec`)
at `call_pc` when the stack at `sp - 48#64` is `stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)`. -/
theorem step_msg48rep_polyDecLen_call {resStack : Nat} (hres : resStack + 128 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {call_pc : BitVec 64} {s0 s : State}
    (hencLen : subroutine_ok (tripleRatchetProgAtExt b ext) call_pc
      (withMsgEnc48CS s0 (polynomialDecoderEncodedLenElemsOutSpec A)))
    (decA sp ret_pc : BitVec 64) (g : Poly.ProtoPolynomialDecoderGhost)
    (pb : ProtoPolynomialDecoder)
    (hlen_lt : polynomialDecoderPBEncodedLen pb < 2 ^ 64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = decA)
    (hcs : MsgEnc48CalleeSaved s0 s)
    (hP : P = (Poly.protoPolynomialDecoderPinnedAt A g decA pb ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (ptsElems : List (BitVec 64 × List (BitVec 8))),
      ptsElems.map Prod.snd = pb.pts → pb.pts.length * 24 < 2 ^ 63 →
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 (polynomialDecoderPBEncodedLen pb) →
      CalleeSavedPreserved s sm → MsgEnc48CalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((polyDecoderElemsAt decA g pb ptsElems ∗
          polyDecoderRestAt A decA g ptsElems ∗
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
  refine SepWPp.call_cs (x := PinnedEncLenGhost.mk decA g pb)
    (F := memRegion (sp - 48#64 - BitVec.ofNat 64 (encodeRepeatedStackOf resStack)) 80 ∗
      memRegion (sp - 48#64 - BitVec.ofNat 64 (0x30 + resStack)) (32 + resStack) ∗ F)
    hencLen hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, hst] at hm
    simp only [withMsgEnc48CS, polynomialDecoderEncodedLenElemsOutSpec,
      polynomialDecoderEncodedLenPinnedSpec, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hlen_lt⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [withMsgEnc48CS, polynomialDecoderEncodedLenElemsOutSpec,
      polynomialDecoderEncodedLenPinnedSpec, sepConj_assoc, satisfies_pure_sepConj] at hm
    exact False.elim hm.1
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withMsgEnc48CS, polynomialDecoderEncodedLenElemsOutSpec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx0m, htrm⟩ => ?_
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun ptsElems => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hpts_eq, hpts_lt⟩ => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPp.weaken_pre ?_
      (hnext sm ptsElems hpts_eq hpts_lt
        hpcm hrunm hspm htrm' hx0m hcsm
        (hcs.trans (MsgEnc48CalleeSaved.of_calleeSavedPreserved hcsm hinv_call)))
    rw [hst]
    exact Entails.of_eq (by ac_rfl)

/-! ## 3. Specifications & Symbol Address Lemmas for `PolynomialDecoder::encode` -/

/-- Pinned ghost inputs for `prost::encoding::message::encode::<PolynomialDecoder, Vec<u8>>`. -/
structure EncodePolyDecoderPinnedGhost where
  tag  : BitVec 32
  decA : BitVec 64
  g    : Poly.ProtoPolynomialDecoderGhost
  dec  : ProtoPolynomialDecoder
  v    : BitVec 64
  cap  : BitVec 64
  ptr  : BitVec 64
  bs   : List (BitVec 8)

/-- Unpinned ghost inputs for `prost::encoding::message::encode::<PolynomialDecoder, Vec<u8>>`. -/
structure EncodePolyDecoderGhost where
  tag  : BitVec 32
  decA : BitVec 64
  dec  : ProtoPolynomialDecoder
  v    : BitVec 64
  cap  : BitVec 64
  ptr  : BitVec 64
  bs   : List (BitVec 8)

/-- Pinned specification of `prost::encoding::message::encode::<PolynomialDecoder, Vec<u8>>`
(`[local#1, 2]`), parameterized by `resStack`. Callers establish `x.dec.pts.length < 2 ^ 58`
and either spare capacity (`x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length ≤ x.cap.toNat`)
or the growth bound `x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length + 10 < 2 ^ 62`. -/
def encodePolyDecoderPinnedSpecOf (resStack : Nat) (A : RustAlloc) :
    Spec EncodePolyDecoderPinnedGhost where
  pre := fun x s =>
    ⌜s.readReg32 .x0 = x.tag ∧
      s.readReg64 .x1 = x.decA ∧
      s.readReg64 .x2 = x.v ∧
      x.dec.pts.length < 2 ^ 58 ∧
      (x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length ≤ x.cap.toNat ∨
        x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length + 10 < 2 ^ 62)⌝ ∗
      Poly.protoPolynomialDecoderPinnedAt A x.g x.decA x.dec ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp (msgEnc48RepeatedStackOf resStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      Poly.protoPolynomialDecoderPinnedAt A x.g x.decA x.dec ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A x.v cap' ptr' (x.bs ++ encodePolyDecoderMsg x.tag x.dec)) ∗
      A.pool ∗ stackAt s0.sp (msgEnc48RepeatedStackOf resStack)
  onPanic := fun _ s0 sf => msgEncOnPanic s0 sf

/-- Unpinned specification of `prost::encoding::message::encode::<PolynomialDecoder, Vec<u8>>`
(`[local#1, 2]`), parameterized by `resStack`. -/
def encodePolyDecoderSpecOf (resStack : Nat) (A : RustAlloc) :
    Spec EncodePolyDecoderGhost where
  pre := fun x s =>
    ⌜s.readReg32 .x0 = x.tag ∧
      s.readReg64 .x1 = x.decA ∧
      s.readReg64 .x2 = x.v ∧
      x.dec.pts.length < 2 ^ 58 ∧
      (x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length ≤ x.cap.toNat ∨
        x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length + 10 < 2 ^ 62)⌝ ∗
      Poly.protoPolynomialDecoderAt A x.decA x.dec ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp (msgEnc48RepeatedStackOf resStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      Poly.protoPolynomialDecoderAt A x.decA x.dec ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A x.v cap' ptr' (x.bs ++ encodePolyDecoderMsg x.tag x.dec)) ∗
      A.pool ∗ stackAt s0.sp (msgEnc48RepeatedStackOf resStack)
  onPanic := fun _ s0 sf => msgEncOnPanic s0 sf

abbrev encodePolyDecoderPinnedSpec (A : RustAlloc) : Spec EncodePolyDecoderPinnedGhost :=
  encodePolyDecoderPinnedSpecOf doReserveStack A
abbrev encodePolyDecoderSpec (A : RustAlloc) : Spec EncodePolyDecoderGhost :=
  encodePolyDecoderSpecOf doReserveStack A
abbrev encodePolyDecoderPinnedSpecX (A : RustAlloc) : Spec EncodePolyDecoderPinnedGhost :=
  encodePolyDecoderPinnedSpecOf doReserveStackX A
abbrev encodePolyDecoderSpecX (A : RustAlloc) : Spec EncodePolyDecoderGhost :=
  encodePolyDecoderSpecOf doReserveStackX A

def EncodePolyDecoder1PinnedOkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr encodePolyDecoder1Name) (encodePolyDecoderPinnedSpec A)
def EncodePolyDecoder1OkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr encodePolyDecoder1Name) (encodePolyDecoderSpec A)
def EncodePolyDecoder1PinnedOkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr encodePolyDecoder1Name)
    ((encodePolyDecoderPinnedSpecX A).inImage img)
def EncodePolyDecoder1OkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr encodePolyDecoder1Name)
    ((encodePolyDecoderSpecX A).inImage img)

def EncodePolyDecoder2PinnedOkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr encodePolyDecoder2Name) (encodePolyDecoderPinnedSpec A)
def EncodePolyDecoder2OkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr encodePolyDecoder2Name) (encodePolyDecoderSpec A)
def EncodePolyDecoder2PinnedOkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr encodePolyDecoder2Name)
    ((encodePolyDecoderPinnedSpecX A).inImage img)
def EncodePolyDecoder2OkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr encodePolyDecoder2Name)
    ((encodePolyDecoderSpecX A).inImage img)

theorem polyDecoder_post_unpinned_of_pinned {resStack : Nat} {A : RustAlloc}
    {x : EncodePolyDecoderGhost} {g : Poly.ProtoPolynomialDecoderGhost} {s0 sf : State} {R : SepProp}
    (hq : sf.mem ⊨ (encodePolyDecoderPinnedSpecOf resStack A).post
      ⟨x.tag, x.decA, g, x.dec, x.v, x.cap, x.ptr, x.bs⟩ s0 sf ∗ R) :
    sf.mem ⊨ (encodePolyDecoderSpecOf resStack A).post x s0 sf ∗ R := by
  dsimp only [encodePolyDecoderPinnedSpecOf] at hq
  dsimp only [encodePolyDecoderSpecOf]
  let Rest : SepProp := ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
      ⌜x.cap.toNat ≤ cap'.toNat ∧
        (x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length ≤ x.cap.toNat →
          cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
        vecU8At A x.v cap' ptr' (x.bs ++ encodePolyDecoderMsg x.tag x.dec)) ∗
    A.pool ∗ stackAt s0.sp (msgEnc48RepeatedStackOf resStack) ∗ R
  have hq' : sf.mem ⊨ Poly.protoPolynomialDecoderPinnedAt A g x.decA x.dec ∗ Rest := by
    convert hq using 1; dsimp only [Rest]; ac_rfl
  have hgoal : sf.mem ⊨ Poly.protoPolynomialDecoderAt A x.decA x.dec ∗ Rest := by
    rw [protoPolynomialDecoderAt_eq_exists_pinned, sepExists_sepConj_left, satisfies_sepExists]
    exact ⟨g, hq'⟩
  convert hgoal using 1; dsimp only [Rest]; ac_rfl

theorem polyDecoder_unpinned_of_pinned {resStack : Nat} {prog : Program} {entry : BitVec 64}
    {A : RustAlloc} (hpinned : subroutine_ok prog entry (encodePolyDecoderPinnedSpecOf resStack A)) :
    subroutine_ok prog entry (encodePolyDecoderSpecOf resStack A) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  dsimp only [encodePolyDecoderSpecOf] at hpre
  rw [protoPolynomialDecoderAt_eq_exists_pinned] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  refine hpinned.mono_outcome ⟨x.tag, x.decA, g, x.dec, x.v, x.cap, x.ptr, x.bs⟩
    R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | hrest
  · exact Or.inl ⟨hret, hcc, polyDecoder_post_unpinned_of_pinned hq⟩
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr hrest)

theorem polyDecoder_unpinned_of_pinned_x {resStack : Nat} {img : Obj.Image}
    {prog : Program} {entry : BitVec 64} {A : RustAlloc}
    (hpinned : subroutine_ok prog entry ((encodePolyDecoderPinnedSpecOf resStack A).inImage img)) :
    subroutine_ok prog entry ((encodePolyDecoderSpecOf resStack A).inImage img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  rw [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre; obtain ⟨hinv0, hpre⟩ := hpre
  dsimp only [encodePolyDecoderSpecOf] at hpre
  rw [protoPolynomialDecoderAt_eq_exists_pinned] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  have hpre' : s0.mem ⊨ ((encodePolyDecoderPinnedSpecOf resStack A).inImage img).pre
      ⟨x.tag, x.decA, g, x.dec, x.v, x.cap, x.ptr, x.bs⟩ s0 ∗ R := by
    rw [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj]; exact ⟨hinv0, hpre⟩
  refine hpinned.mono_outcome ⟨x.tag, x.decA, g, x.dec, x.v, x.cap, x.ptr, x.bs⟩
    R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | hrest
  · exact Or.inl ⟨hret, hcc, polyDecoder_post_unpinned_of_pinned hq⟩
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr hrest)

theorem encodePolyDecoder1_encodedLen1_fnAddr_eq (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr encodePolyDecoder1Name + 10616#64 =
      (tripleRatchetProgAtExt b ext).fnAddr polynomialDecoderEncodedLenLocal1Name := by
  have h1 := libsignalSessionCode_fnOff_0x37604; have h2 := libsignalSessionCode_fnOff_0x39f7c
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, encodePolyDecoder1Name,
    polynomialDecoderEncodedLenLocal1Name, h1, h2]; bv_omega

theorem encodePolyDecoder1_encodeVarint2_fnAddr_eq (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr encodePolyDecoder1Name + 18446744073709547784#64 =
      (tripleRatchetProgAtExt b ext).fnAddr encodeVarint2Name := by
  have h1 := libsignalSessionCode_fnOff_0x37604; have h2 := libsignalSessionCode_fnOff_0x3670c
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, encodePolyDecoder1Name,
    encodeVarint2Name, h1, h2]; bv_omega

theorem encodePolyDecoder1_encodeRepeated1_fnAddr_eq (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr encodePolyDecoder1Name + 18446744073709546080#64 =
      (tripleRatchetProgAtExt b ext).fnAddr encodeRepeated1Name := by
  have h1 := libsignalSessionCode_fnOff_0x37604; have h2 := libsignalSessionCode_fnOff_0x36064
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, encodePolyDecoder1Name,
    encodeRepeated1Name, h1, h2]; bv_omega

theorem encodePolyDecoder1_doReserve2_fnAddr_eq (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr encodePolyDecoder1Name + 2652#64 =
      (tripleRatchetProgAtExt b ext).fnAddr doReserve2Name := by
  have h1 := libsignalSessionCode_fnOff_0x37604; have h2 := libsignalSessionCode_fnOff_0x38060
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, encodePolyDecoder1Name,
    doReserve2Name, h1, h2]; bv_omega

theorem encodePolyDecoder2_encodedLen2_fnAddr_eq (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr encodePolyDecoder2Name + 94640#64 =
      (tripleRatchetProgAtExt b ext).fnAddr polynomialDecoderEncodedLenLocal2Name := by
  have h1 := libsignalSessionCode_fnOff_0x4d14c; have h2 := libsignalSessionCode_fnOff_0x642fc
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, encodePolyDecoder2Name,
    polynomialDecoderEncodedLenLocal2Name, h1, h2]; bv_omega

theorem encodePolyDecoder2_encodeVarint4_fnAddr_eq (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr encodePolyDecoder2Name + 18446744073709531596#64 =
      (tripleRatchetProgAtExt b ext).fnAddr encodeVarint4Name := by
  have h1 := libsignalSessionCode_fnOff_0x4d14c; have h2 := libsignalSessionCode_fnOff_0x48318
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, encodePolyDecoder2Name,
    encodeVarint4Name, h1, h2]; bv_omega

theorem encodePolyDecoder2_encodeRepeated2_fnAddr_eq (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr encodePolyDecoder2Name + 18446744073709529852#64 =
      (tripleRatchetProgAtExt b ext).fnAddr encodeRepeated2Name := by
  have h1 := libsignalSessionCode_fnOff_0x4d14c; have h2 := libsignalSessionCode_fnOff_0x47c48
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, encodePolyDecoder2Name,
    encodeRepeated2Name, h1, h2]; bv_omega

theorem encodePolyDecoder2_doReserve7_fnAddr_eq (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr encodePolyDecoder2Name + 2908#64 =
      (tripleRatchetProgAtExt b ext).fnAddr doReserve7Name := by
  have h1 := libsignalSessionCode_fnOff_0x4d14c; have h2 := libsignalSessionCode_fnOff_0x4dca8
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, encodePolyDecoder2Name,
    doReserve7Name, h1, h2]; bv_omega

/-! ## 4. Instruction Fetch Infrastructure & Shared Stepping Lemmas -/

def IsPolyDecoderEncodeEntry (b : BitVec 64) (ext : String → Option (State → State))
    (entry : BitVec 64) : Prop :=
  (tripleRatchetProgAtExt b ext).fnAddr encodePolyDecoder1Name = entry ∨
    (tripleRatchetProgAtExt b ext).fnAddr encodePolyDecoder2Name = entry

theorem polyDecoderEncode_fetch_entry {b : BitVec 64} {ext : String → Option (State → State)}
    {entry : BitVec 64} (hfn : IsPolyDecoderEncodeEntry b ext entry) {ins : Instr}
    (h1 : (tripleRatchetProgAtExt b ext).fetch
      ((tripleRatchetProgAtExt b ext).fnAddr encodePolyDecoder1Name) = some ins)
    (h2 : (tripleRatchetProgAtExt b ext).fetch
      ((tripleRatchetProgAtExt b ext).fnAddr encodePolyDecoder2Name) = some ins) :
    (tripleRatchetProgAtExt b ext).fetch entry = some ins := by
  rcases hfn with rfl | rfl
  · exact h1
  · exact h2

theorem polyDecoderEncode_fetch_add {b : BitVec 64} {ext : String → Option (State → State)}
    {entry : BitVec 64} (hfn : IsPolyDecoderEncodeEntry b ext entry) {k : Nat} {ins : Instr}
    (h1 : (tripleRatchetProgAtExt b ext).fetch
      ((tripleRatchetProgAtExt b ext).fnAddr encodePolyDecoder1Name + BitVec.ofNat 64 k) = some ins)
    (h2 : (tripleRatchetProgAtExt b ext).fetch
      ((tripleRatchetProgAtExt b ext).fnAddr encodePolyDecoder2Name + BitVec.ofNat 64 k) = some ins) :
    (tripleRatchetProgAtExt b ext).fetch (entry + BitVec.ofNat 64 k) = some ins := by
  rcases hfn with rfl | rfl
  · exact h1
  · exact h2

open Lean Elab Tactic in
scoped elab "pd_fetches" b:term:arg H:term:arg hfn:ident lo:num hi:num : tactic => do
  let off1 := 0x37604
  let off2 := 0x4d14c
  let loN := lo.getNat
  let hiN := hi.getNat
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  let fnOff1 := mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x37604
  let fnOff2 := mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x4d14c
  for i in [loN / 4 : hiN / 4] do
    let k := 4 * i
    let dec1 := mkIdent (`CryptoVerification.SpqrV1.Prost.MessageEncode |>.str
      s!"libsignalSessionBin_decode_0x{String.ofList (Nat.toDigits 16 (off1 + k))}")
    let dec2 := mkIdent (`CryptoVerification.SpqrV1.Prost.MessageEncode |>.str
      s!"libsignalSessionBin_decode_0x{String.ofList (Nat.toDigits 16 (off2 + k))}")
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := polyDecoderEncode_fetch_entry $hfn
          ($fetchEntry (b := $b) (H := $H) $fnOff1 (by decide) $dec1)
          ($fetchEntry (b := $b) (H := $H) $fnOff2 (by decide) $dec2)))
    else
      evalTactic (← `(tactic|
        have := polyDecoderEncode_fetch_add $hfn (k := $kq)
          ($fetchAdd (b := $b) (H := $H) (k := $kq) $fnOff1 (by decide) $dec1)
          ($fetchAdd (b := $b) (H := $H) (k := $kq) $fnOff2 (by decide) $dec2)))

/-- Step `+0..+36` (`0x37520..0x37544` / `0x52544..0x52568`):
allocates 48B frame (`msgEnc48SavedFrame`), saves `fp, lr, x21, x20, x19`, sets `x20 = decA`,
`x1 = v`, `x19 = v`, and `x0 = ((tag <<< 3) ||| 2#32).zeroExtend 64`. -/
theorem step_polyDecoder_prologue {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    (b : BitVec 64) (ext : String → Option (State → State)) {entry : BitVec 64} {s0 s : State}
    (hfn : IsPolyDecoderEncodeEntry b ext entry) (tag : BitVec 32) (decA v sp : BitVec 64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hhs0 : s = s0) (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hw0 : s.readReg32 .x0 = tag) (hx1 : s.readReg64 .x1 = decA) (hx2 : s.readReg64 .x2 = v)
    (hcs : MsgEnc48CalleeSaved s0 s) (hP : P = stackAt sp (msgEnc48RepeatedStackOf resStack) ∗ F)
    (hnext : ∀ (s1 : State) (sv3 : BitVec 64),
      s1.pc = entry + 36#64 → s1.status = .Running → s1.sp = sp - 48#64 → s1.trace = s0.trace →
      s1.readReg64 .x0 = ((tag <<< 3) ||| (Proto.WireType.lengthDelimited).toU32).zeroExtend 64 →
      s1.readReg64 .x1 = v → s1.readReg64 .x19 = v → s1.readReg64 .x20 = decA →
      MsgEnc48CalleeSaved s0 s1 →
      SepWPp (tripleRatchetProgAtExt b ext) ret s1
        ((stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
          msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  pd_fetches b (Rust.withPanics ext) hfn 0 36; examples_hide_fetches
  subst hP hhs0
  have hsp_aligned := sp_sub_48_aligned halign
  have hw0' : BitVec.truncate 32 (s.readReg64 .x0) = tag := hw0
  rw [stackAt_msgEnc48_repeated hres sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun sv0 => SepWPp.exists_elim fun sv1 =>
    SepWPp.exists_elim fun sv2 => SepWPp.exists_elim fun sv3 =>
    SepWPp.exists_elim fun sv4 => SepWPp.exists_elim fun sv5 => ?_
  apply SepWPp.of_sepWP_cs (mid := entry + 36#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  refine SepWPp.weaken_pre (by dsimp only [msgEnc48SavedFrame]; exact Entails.of_eq (by ac_rfl))
    (hnext _ sv3 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by dsimp only [State.readReg32, Reg.x0] at hw0' ⊢; simp only [arm64_norm]
          exact polyDecoder_tag_orr_eq tag)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv1))

theorem step_polyDecoder_mov_x0_x20_40
    (b : BitVec 64) (ext : String → Option (State → State)) {entry : BitVec 64} {s0 s : State}
    (hfn : IsPolyDecoderEncodeEntry b ext entry) (decA v sp : BitVec 64)
    {R : SepProp} {ret : BitVec 64} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 40#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA)
    (hcs : MsgEnc48CalleeSaved s0 s)
    (hnext : ∀ s1 : State,
      s1.pc = entry + 44#64 → s1.status = .Running → s1.sp = sp - 48#64 → s1.trace = s0.trace →
      s1.readReg64 .x0 = decA → s1.readReg64 .x19 = v → s1.readReg64 .x20 = decA →
      MsgEnc48CalleeSaved s0 s1 →
      SepWPp (tripleRatchetProgAtExt b ext) ret s1 P Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  pd_fetches b (Rust.withPanics ext) hfn 40 44; examples_hide_fetches
  apply SepWPp.of_sepWP_cs (mid := entry + 44#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) hinv1)

theorem step_polyDecoder_mov_x1_x19_48
    (b : BitVec 64) (ext : String → Option (State → State)) {entry : BitVec 64} {s0 s : State}
    (hfn : IsPolyDecoderEncodeEntry b ext entry) (decA v x0v sp : BitVec 64)
    {R : SepProp} {ret : BitVec 64} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 48#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = x0v) (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = decA) (hcs : MsgEnc48CalleeSaved s0 s)
    (hnext : ∀ s1 : State,
      s1.pc = entry + 52#64 → s1.status = .Running → s1.sp = sp - 48#64 → s1.trace = s0.trace →
      s1.readReg64 .x0 = x0v → s1.readReg64 .x1 = v → s1.readReg64 .x19 = v →
      s1.readReg64 .x20 = decA → MsgEnc48CalleeSaved s0 s1 →
      SepWPp (tripleRatchetProgAtExt b ext) ret s1 P Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  pd_fetches b (Rust.withPanics ext) hfn 48 52; examples_hide_fetches
  apply SepWPp.of_sepWP_cs (mid := entry + 52#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) hinv1)

/-- Step `+56..+64` (`0x37558..0x37560` / `0x5257c..0x52584`):
loads `w0 = [x20, #0x18]` (`pb.ptsNeeded`) and branches to `entry + 108#64` if `pb.ptsNeeded == 0#32`,
else falls through to `entry + 64#64`. -/
theorem step_polyDecoder_check_ptsNeeded (b : BitVec 64) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : IsPolyDecoderEncodeEntry b ext entry)
    (decA v sp : BitVec 64) (g : Poly.ProtoPolynomialDecoderGhost) (pb : ProtoPolynomialDecoder)
    (ptsElems : List (BitVec 64 × List (BitVec 8)))
    {s0 s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 56#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA)
    (hcs : MsgEnc48CalleeSaved s0 s) (hP : P = polyDecoderElemsAt decA g pb ptsElems ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = entry + (if pb.ptsNeeded == 0#32 then 108#64 else 64#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = pb.ptsNeeded.zeroExtend 64 → sm.readReg64 .x19 = v → sm.readReg64 .x20 = decA →
      MsgEnc48CalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        (polyDecoderElemsAt decA g pb ptsElems ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  pd_fetches b (Rust.withPanics ext) hfn 56 64
  examples_hide_fetches; subst hP; dsimp only [polyDecoderElemsAt]
  cases hpn : (pb.ptsNeeded == 0#32)
  · have hpn64 : (BitVec.zeroExtend 64 pb.ptsNeeded == 0#64) = false := by
      rw [EncodedLen.zeroExtend64_beq_zero32, hpn]
    apply SepWPp.of_sepWP_cs (mid := entry + 64#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    refine SepWPp.weaken_pre (by dsimp only [polyDecoderElemsAt]; exact Entails.of_eq (by ac_rfl))
      (hnext _ (by simp only [Bool.false_eq_true, ↓reduceIte, arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv))
  · have hpn64 : (BitVec.zeroExtend 64 pb.ptsNeeded == 0#64) = true := by
      rw [EncodedLen.zeroExtend64_beq_zero32, hpn]
    apply SepWPp.of_sepWP_cs (mid := entry + 108#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    refine SepWPp.weaken_pre (by dsimp only [polyDecoderElemsAt]; exact Entails.of_eq (by ac_rfl))
      (hnext _ (by simp only [↓reduceIte, arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv))

/-- Step `+80..+104` (`0x37570..0x37588` / `0x52594..0x525ac`):
stores tag byte `0x08#8` (`field 1, wire type varint`) into `curBs` and sets `x1 = v`. -/
theorem step_polyDecoder_push_ptsNeeded_tag (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : IsPolyDecoderEncodeEntry b ext entry)
    (decA v curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8))
    (pb : ProtoPolynomialDecoder) (hlt : curBs.length < curCap.toNat)
    {s0 s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 80#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = pb.ptsNeeded.zeroExtend 64)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA) (hcs : MsgEnc48CalleeSaved s0 s)
    (hP : P = vecU8At A v curCap curPtr curBs ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = entry + 104#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = pb.ptsNeeded.zeroExtend 64 → sm.readReg64 .x1 = v →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = decA → MsgEnc48CalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        (vecU8At A v curCap curPtr (curBs ++ [0x08#8]) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  pd_fetches b (Rust.withPanics ext) hfn 80 104
  examples_hide_fetches; subst hP
  rw [vecU8At_open_one A v curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_cs (mid := entry + 104#64); wp_steps
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

/-- Step `+108..+116` (`0x3758c..0x37594` / `0x525b0..0x525b8`):
loads `w0 = [x20, #0x1c]` (`pb.polys`) and branches to `entry + 160#64` if `pb.polys == 0#32`,
else falls through to `entry + 116#64`. -/
theorem step_polyDecoder_check_polys (b : BitVec 64) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : IsPolyDecoderEncodeEntry b ext entry)
    (decA v sp : BitVec 64) (g : Poly.ProtoPolynomialDecoderGhost) (pb : ProtoPolynomialDecoder)
    (ptsElems : List (BitVec 64 × List (BitVec 8)))
    {s0 s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 108#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA)
    (hcs : MsgEnc48CalleeSaved s0 s) (hP : P = polyDecoderElemsAt decA g pb ptsElems ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = entry + (if pb.polys == 0#32 then 160#64 else 116#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = pb.polys.zeroExtend 64 → sm.readReg64 .x19 = v → sm.readReg64 .x20 = decA →
      MsgEnc48CalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        (polyDecoderElemsAt decA g pb ptsElems ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  pd_fetches b (Rust.withPanics ext) hfn 108 116
  examples_hide_fetches; subst hP; dsimp only [polyDecoderElemsAt]
  cases hpl : (pb.polys == 0#32)
  · have hpl64 : (BitVec.zeroExtend 64 pb.polys == 0#64) = false := by
      rw [EncodedLen.zeroExtend64_beq_zero32, hpl]
    apply SepWPp.of_sepWP_cs (mid := entry + 116#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    refine SepWPp.weaken_pre (by dsimp only [polyDecoderElemsAt]; exact Entails.of_eq (by ac_rfl))
      (hnext _ (by simp only [Bool.false_eq_true, ↓reduceIte, arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv))
  · have hpl64 : (BitVec.zeroExtend 64 pb.polys == 0#64) = true := by
      rw [EncodedLen.zeroExtend64_beq_zero32, hpl]
    apply SepWPp.of_sepWP_cs (mid := entry + 160#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    refine SepWPp.weaken_pre (by dsimp only [polyDecoderElemsAt]; exact Entails.of_eq (by ac_rfl))
      (hnext _ (by simp only [↓reduceIte, arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv))

/-- Step `+132..+156` (`0x375a4..0x375bc` / `0x525c8..0x525e0`):
stores tag byte `0x10#8` (`field 2, wire type varint`) into `curBs` and sets `x1 = v`. -/
theorem step_polyDecoder_push_polys_tag (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : IsPolyDecoderEncodeEntry b ext entry)
    (decA v curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8))
    (pb : ProtoPolynomialDecoder) (hlt : curBs.length < curCap.toNat)
    {s0 s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 132#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = pb.polys.zeroExtend 64)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA) (hcs : MsgEnc48CalleeSaved s0 s)
    (hP : P = vecU8At A v curCap curPtr curBs ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = entry + 156#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = pb.polys.zeroExtend 64 → sm.readReg64 .x1 = v →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = decA → MsgEnc48CalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        (vecU8At A v curCap curPtr (curBs ++ [0x10#8]) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  pd_fetches b (Rust.withPanics ext) hfn 132 156
  examples_hide_fetches; subst hP
  rw [vecU8At_open_one A v curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_cs (mid := entry + 156#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
  refine SepWPp.weaken_pre (by rw [← vecU8At_close_one A v curCap curPtr curBs 0x10#8 hlt]; exact Entails.of_eq (by ac_rfl))
    (hnext _
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv))

/-- Step `+160..+172` (`0x375c0..0x375cc` / `0x525e4..0x525f0`):
loads `x1 = g.pts.ptr`, `x2 = BitVec.ofNat 64 pb.pts.length`, sets `w0 = 3#32`, `x3 = v`. -/
theorem step_polyDecoder_prep_pts
    (b : BitVec 64) (ext : String → Option (State → State)) {entry : BitVec 64} {s0 s : State}
    (hfn : IsPolyDecoderEncodeEntry b ext entry) (decA v sp : BitVec 64)
    (g : Poly.ProtoPolynomialDecoderGhost) (pb : ProtoPolynomialDecoder)
    (ptsElems : List (BitVec 64 × List (BitVec 8)))
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 160#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA)
    (hcs : MsgEnc48CalleeSaved s0 s) (hP : P = polyDecoderElemsAt decA g pb ptsElems ∗ F)
    (hnext : ∀ s1 : State,
      s1.pc = entry + 172#64 → s1.status = .Running → s1.sp = sp - 48#64 → s1.trace = s0.trace →
      s1.readReg32 .x0 = 3#32 → s1.readReg64 .x1 = g.pts.ptr →
      s1.readReg64 .x2 = BitVec.ofNat 64 pb.pts.length → s1.readReg64 .x3 = v →
      s1.readReg64 .x19 = v → s1.readReg64 .x20 = decA → MsgEnc48CalleeSaved s0 s1 →
      SepWPp (tripleRatchetProgAtExt b ext) ret s1 (polyDecoderElemsAt decA g pb ptsElems ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  pd_fetches b (Rust.withPanics ext) hfn 160 172; examples_hide_fetches; subst hP
  dsimp only [polyDecoderElemsAt]
  apply SepWPp.of_sepWP_cs (mid := entry + 172#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  refine SepWPp.weaken_pre (by dsimp only [polyDecoderElemsAt]; exact Entails.of_eq (by ac_rfl))
    (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by dsimp only [State.readReg32, Reg.x0]; simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv1))

/-- Step `+176..+188` / `+248..+264` (`0x375d0..0x375dc` / `0x525f4..0x52600`):
loads `w8 = [decA + 0x20]` (`boolByte pb.isComplete`).
- If `pb.isComplete = false`, branches to `+248` and executes the epilogue (`ldp x20, x19; ldr x21; ldp x29, x30, [sp], #0x30; ret`).
- If `pb.isComplete = true`, falls through to `+188`. -/
theorem step_polyDecoder_check_isComplete {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    (b : BitVec 64) (ext : String → Option (State → State))
    {entry : BitVec 64} {s0 s : State} (hfn : IsPolyDecoderEncodeEntry b ext entry)
    (decA v sp sv3 : BitVec 64) (g : Poly.ProtoPolynomialDecoderGhost)
    (pb : ProtoPolynomialDecoder) (ptsElems : List (BitVec 64 × List (BitVec 8)))
    {R : SepProp} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 176#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = decA) (hcs : MsgEnc48CalleeSaved s0 s)
    (hP : P = (polyDecoderElemsAt decA g pb ptsElems ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
    (hfalse : pb.isComplete = false → ∀ sf : State,
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp → sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf → MsgEnc48CalleeSaved s0 sf →
      Q sf ((polyDecoderElemsAt decA g pb ptsElems ∗
        stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F))
    (htrue : pb.isComplete = true → ∀ s1 : State,
      s1.pc = entry + 188#64 → s1.status = .Running → s1.sp = sp - 48#64 → s1.trace = s0.trace →
      s1.readReg64 .x19 = v → s1.readReg64 .x20 = decA → MsgEnc48CalleeSaved s0 s1 →
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .lr) s1
        ((polyDecoderElemsAt decA g pb ptsElems ∗
          stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
          msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  pd_fetches b (Rust.withPanics ext) hfn 176 188
  pd_fetches b (Rust.withPanics ext) hfn 248 264; examples_hide_fetches; subst hP
  have hsp_aligned := sp_sub_48_aligned halign
  cases hc : pb.isComplete
  · have hbyte : boolByte pb.isComplete = 0#8 := by rw [hc]; rfl
    rcases hcs with ⟨h22, h23, h24, h25, h26, h27, h28, hvregs, hinv0⟩
    apply SepWPp.of_sepWP_cs (mid := s0.readReg64 .lr)
    dsimp only [polyDecoderElemsAt, msgEnc48SavedFrame]
    rw [hbyte]; wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinvf
    refine SepWPp.weaken_pre
      (show _ ⊢ (polyDecoderElemsAt decA g pb ptsElems ∗ stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F from ?_)
      (SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) ?_)
    · rw [← hbyte]
      have hrecomb := stackAt_msgEnc48_repeated_recombine hres sp
        (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x21) sv3
        (s0.readReg64 .x20) (s0.readReg64 .x19)
      refine Entails.trans (Entails.of_eq ?_) (sepConj_mono_left (sepConj_mono_right hrecomb))
      dsimp only [polyDecoderElemsAt, msgEnc48SavedFrame]
    · apply (hfalse hc)
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · epochEncLen_cc_close
      · exact ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
               by simp only [arm64_norm, *], by simp only [arm64_norm, *],
               by simp only [arm64_norm, *], by simp only [arm64_norm, *],
               by simp only [arm64_norm, *], by simp only [arm64_norm, *], hinv0.trans hinvf⟩
  · have hbyte : boolByte pb.isComplete = 1#8 := by rw [hc]; rfl
    apply SepWPp.of_sepWP_cs (mid := entry + 188#64)
    dsimp only [polyDecoderElemsAt]; rw [hbyte]; wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
    refine SepWPp.weaken_pre (by rw [← hbyte]; dsimp only [polyDecoderElemsAt]; exact Entails.of_eq (by ac_rfl))
      (htrue hc _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv1))

/-- Step `+204..+228` (`0x375ec..0x37604` / `0x52610..0x52628`):
stores tag byte `0x20#8` (`field 4, wire type varint`) into `curBs`, sets `x9 = curPtr`,
`x10 = BitVec.ofNat 64 (curBs ++ [0x20#8]).length`, and compares `x8 = curCap` with `x10` at `+228`. -/
theorem step_polyDecoder_push_isComplete_tag (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) {entry : BitVec 64} {s0 s : State}
    (hfn : IsPolyDecoderEncodeEntry b ext entry) (decA v curCap curPtr sp : BitVec 64)
    (curBs : List (BitVec 8)) (hlt : curBs.length < curCap.toNat)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 204#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx8 : s.readReg64 .x8 = curCap) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA)
    (hcs : MsgEnc48CalleeSaved s0 s) (hP : P = vecU8At A v curCap curPtr curBs ∗ F)
    (hnext : ∀ s1 : State,
      s1.pc = entry + 228#64 → s1.status = .Running → s1.sp = sp - 48#64 → s1.trace = s0.trace →
      s1.readReg64 .x8 = curCap → s1.readReg64 .x9 = curPtr →
      s1.readReg64 .x10 = BitVec.ofNat 64 (curBs ++ [0x20#8]).length →
      s1.readReg64 .x19 = v → s1.readReg64 .x20 = decA →
      s1.pstate = subsPState64 curCap (BitVec.ofNat 64 (curBs ++ [0x20#8]).length) →
      MsgEnc48CalleeSaved s0 s1 →
      SepWPp (tripleRatchetProgAtExt b ext) ret s1
        (vecU8At A v curCap curPtr (curBs ++ [0x20#8]) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  pd_fetches b (Rust.withPanics ext) hfn 204 228; examples_hide_fetches; subst hP
  rw [vecU8At_open_one A v curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left]; refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_cs (mid := entry + 228#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  have hlen1 : BitVec.ofNat 64 curBs.length + 1#64 = BitVec.ofNat 64 (curBs ++ [0x20#8]).length := by
    rw [List.length_append, List.length_singleton]; exact (BitVec.ofNat_add curBs.length 1).symm
  refine SepWPp.weaken_pre (by rw [← vecU8At_close_one A v curCap curPtr curBs 0x20#8 hlt]; exact Entails.of_eq (by ac_rfl))
    (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv1))

/-- Step `+232..+264` (`0x37608..0x37628` / `0x5262c..0x5264c`):
stores value byte `0x01#8` into `curBs`, updates `[v + 16] = curBs.length + 1`, and executes
the epilogue (`ldp x20, x19; ldr x21; ldp x29, x30, [sp], #0x30; ret`). -/
theorem step_polyDecoder_push_isComplete_val_epilogue {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} {s0 s : State} (hfn : IsPolyDecoderEncodeEntry b ext entry)
    (v curCap curPtr sp sv3 : BitVec 64) (curBs : List (BitVec 8))
    (hlt : curBs.length < curCap.toNat)
    {R : SepProp} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 232#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hx9 : s.readReg64 .x9 = curPtr)
    (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 curBs.length) (hx19 : s.readReg64 .x19 = v)
    (hcs : MsgEnc48CalleeSaved s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp → sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf → MsgEnc48CalleeSaved s0 sf →
      Q sf ((vecU8At A v curCap curPtr (curBs ++ [0x01#8]) ∗
        stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F)) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  pd_fetches b (Rust.withPanics ext) hfn 232 264; examples_hide_fetches; subst hP
  have hsp_aligned := sp_sub_48_aligned halign
  rcases hcs with ⟨h22, h23, h24, h25, h26, h27, h28, hvregs, hinv0⟩
  rw [vecU8At_open_one A v curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left]; refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_cs (mid := s0.readReg64 .lr); dsimp only [msgEnc48SavedFrame]; wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinvf
  refine SepWPp.weaken_pre
    (show _ ⊢ (vecU8At A v curCap curPtr (curBs ++ [0x01#8]) ∗ stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F from ?_)
    (SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) ?_)
  · rw [← vecU8At_close_one A v curCap curPtr curBs 0x01#8 hlt]
    have hrecomb := stackAt_msgEnc48_repeated_recombine hres sp
      (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x21) sv3
      (s0.readReg64 .x20) (s0.readReg64 .x19)
    refine Entails.trans (Entails.of_eq ?_) (sepConj_mono_left (sepConj_mono_right hrecomb))
    dsimp only [msgEnc48SavedFrame]
  · apply hnext
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · epochEncLen_cc_close
    · exact ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
             by simp only [arm64_norm, *], by simp only [arm64_norm, *],
             by simp only [arm64_norm, *], by simp only [arm64_norm, *],
             by simp only [arm64_norm, *], by simp only [arm64_norm, *], hinv0.trans hinvf⟩

end CryptoVerification.SpqrV1.Prost.MessageEncode

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.Proof
public import LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.Append
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Shared Leaf `prost::encoding::message::merge` Definitions

Symbol names, offsets, instruction-fetch macros, suffix laws for `Proto` primitives and
`mergeMessage`, and `SepWPp` framing combinators (`ImgCallInv` and `LibsignalCodeRoLoaded`) for the
leaf SPQR V1 `prost::encoding::message::merge` subroutines (`ChainParams`, `EpochDirection`,
`PolynomialDecoder`, and `PolynomialEncoder`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Prost.MessageMerge

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-- `prost::encoding::message::merge::<spqr::proto::pq_ratchet::ChainParams, &mut &[u8]>`
(`0x4dcf8`, 144 instructions). -/
abbrev chainParamsMergeName : String :=
  "prost::encoding::message::merge::<spqr::proto::pq_ratchet::ChainParams, &mut &[u8]>"

/-- `prost::encoding::message::merge::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, &mut &[u8]>`
(`0x4f544`, 145 instructions). -/
abbrev epochDirectionMergeName : String :=
  "prost::encoding::message::merge::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, &mut &[u8]>"

/-- `prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>`
(`0x4e10c`, 227 instructions). -/
abbrev polyDecoderMergeName : String :=
  "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>"

/-- `prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialEncoder, &mut &[u8]>`
(`0x4e498`, 212 instructions). -/
abbrev polyEncoderMergeName : String :=
  "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialEncoder, &mut &[u8]>"

theorem chainParamsMerge_fnOff :
    libsignalSessionCode.fnOff chainParamsMergeName = ls_off% "prost::encoding::message::merge::<spqr::proto::pq_ratchet::ChainParams, &mut &[u8]>" :=
  ls_lemma% fnOff "prost::encoding::message::merge::<spqr::proto::pq_ratchet::ChainParams, &mut &[u8]>"

theorem epochDirectionMerge_fnOff :
    libsignalSessionCode.fnOff epochDirectionMergeName = ls_off% "prost::encoding::message::merge::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, &mut &[u8]>" :=
  ls_lemma% fnOff "prost::encoding::message::merge::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, &mut &[u8]>"

theorem polyDecoderMerge_fnOff :
    libsignalSessionCode.fnOff polyDecoderMergeName = ls_off% "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>" :=
  ls_lemma% fnOff "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>"

theorem polyEncoderMerge_fnOff :
    libsignalSessionCode.fnOff polyEncoderMergeName = ls_off% "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialEncoder, &mut &[u8]>" :=
  ls_lemma% fnOff "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialEncoder, &mut &[u8]>"

gen_decodes libsignalSessionCode_tree chainParamsMergeBin [
  0x48900 → 0x48b3c
]

gen_decodes libsignalSessionCode_tree epochDirectionMergeBin [
  0x4a14c → 0x4a38c
]

gen_decodes libsignalSessionCode_tree polyDecoderMergeBin [
  0x48d14 → 0x4909c
]

gen_decodes libsignalSessionCode_tree polyEncoderMergeBin [
  0x490a0 → 0x493ec
]

open Lean Elab Tactic in
/-- `code_fetches_from <code> <decPrefix> b H hfn off k0 len` adds `<code>_fetch_fnAddr`
    hypotheses for the instructions `k = k0, k0 + 4, …, k0 + len - 4` of the function at offset
    `off` (`hfn : <code>.fnOff name = off`), using `<decPrefix>_decode_0x<off+k>`. -/
elab "code_fetches_from " codeId:ident decPrefix:ident b:term:max H:term:max hfn:ident
    off:num k0:num len:num : tactic => do
  let off := off.getNat
  let k0 := k0.getNat
  let len := len.getNat
  let codeBase := codeId.getId.eraseMacroScopes
  let decBase := decPrefix.getId.eraseMacroScopes
  let fetchEntry := mkIdent (codeBase.appendAfter "_fetch_fnAddr_entry")
  let fetchAdd := mkIdent (codeBase.appendAfter "_fetch_fnAddr")
  for i in [0:len / 4] do
    let k := k0 + 4 * i
    let dec := mkIdent (decBase.appendAfter s!"_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := $fetchEntry (b := $b) (H := $H) $hfn (by decide) $dec))
    else
      evalTactic (← `(tactic|
        have := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec))

/-- Fetch hypotheses for `ChainParams::merge` (`0x4dcf8`), from fn-relative offset `k0`, `len` bytes. -/
macro "chainParamsMerge_fetches " b:term:max H:term:max k0:num len:num : tactic =>
  `(tactic| code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.SpqrV1.Prost.MessageMerge.chainParamsMergeBin $b $H
    chainParamsMerge_fnOff 0x48900 $k0 $len)

/-- Fetch hypotheses for `EpochDirection::merge` (`0x4f544`), from fn-relative offset `k0`, `len` bytes. -/
macro "epochDirectionMerge_fetches " b:term:max H:term:max k0:num len:num : tactic =>
  `(tactic| code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.SpqrV1.Prost.MessageMerge.epochDirectionMergeBin $b $H
    epochDirectionMerge_fnOff 0x4a14c $k0 $len)

/-- Fetch hypotheses for `PolynomialDecoder::merge` (`0x4e10c`), from fn-relative offset `k0`, `len` bytes. -/
macro "polyDecoderMerge_fetches " b:term:max H:term:max k0:num len:num : tactic =>
  `(tactic| code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.SpqrV1.Prost.MessageMerge.polyDecoderMergeBin $b $H
    polyDecoderMerge_fnOff 0x48d14 $k0 $len)

/-- Fetch hypotheses for `PolynomialEncoder::merge` (`0x4e498`), from fn-relative offset `k0`, `len` bytes. -/
macro "polyEncoderMerge_fetches " b:term:max H:term:max k0:num len:num : tactic =>
  `(tactic| code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.SpqrV1.Prost.MessageMerge.polyEncoderMergeBin $b $H
    polyEncoderMerge_fnOff 0x490a0 $k0 $len)

/-! ## 1. Bridges between `LibsignalSpqrV1.Proto` and `LibsignalProtoCodec` -/

open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.SpqrV1.Prost.BytesMerge
open CryptoVerification.LibsignalSpqrV1 hiding decodeVarint encodeVarint WireType

set_option linter.unusedSimpArgs false

/-- Convert `LibsignalProtoCodec.WireType` to `LibsignalSpqrV1.Proto.WireType`. -/
def codecWireTypeToProto : CryptoVerification.LibsignalProtoCodec.WireType → Proto.WireType
  | .varint => .varint
  | .sixtyFourBit => .SixtyFourBit
  | .lengthDelimited => .lengthDelimited
  | .startGroup => .startGroup
  | .endGroup => .endGroup
  | .thirtyTwoBit => .ThirtyTwoBit

@[simp]
theorem codecWireTypeToProto_protoWireTypeToCodec (wt : Proto.WireType) :
    codecWireTypeToProto (protoWireTypeToCodec wt) = wt := by
  cases wt <;> rfl

@[simp]
theorem protoWireTypeToCodec_codecWireTypeToProto (wt : CryptoVerification.LibsignalProtoCodec.WireType) :
    protoWireTypeToCodec (codecWireTypeToProto wt) = wt := by
  cases wt <;> rfl

@[simp]
theorem proto_dropExact_toOption (n : Nat) (bs : List (BitVec 8)) :
    (Proto.dropExact n bs).toOption = skipBytes n bs := by
  induction n generalizing bs with
  | zero =>
    simp [Proto.dropExact, skipBytes, Except.toOption]
  | succ n ih =>
    cases bs with
    | nil =>
      simp [Proto.dropExact, skipBytes, Except.toOption]
    | cons b rest =>
      simp only [Proto.dropExact, ih rest, skipBytes, List.length_cons,
        Nat.add_lt_add_iff_right, List.drop_succ_cons]

private theorem key_gt_u32Max_iff (key : BitVec 64) :
    (0xffffffff#64 < key) ↔ 2 ^ 32 ≤ key.toNat := by
  rw [BitVec.lt_def]
  change 0xffffffff < key.toNat ↔ 4294967296 ≤ key.toNat
  omega

private theorem wireType_ofU64_eq_ofNat (key : BitVec 64) :
    Proto.WireType.ofU64? (key &&& 0x7#64) =
      (CryptoVerification.LibsignalProtoCodec.WireType.ofNat? (key.toNat % 8)).map codecWireTypeToProto := by
  have hmod : (key &&& 0x7#64).toNat = key.toNat % 8 := by
    rw [BitVec.toNat_and, show (0x7#64).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have hlt : key.toNat % 8 < 8 := Nat.mod_lt _ (by decide)
  rcases h : key.toNat % 8 with _ | _ | _ | _ | _ | _ | _ | n
  · have hb : (key &&& 0x7#64) = 0#64 := BitVec.eq_of_toNat_eq (by rw [hmod, h]; rfl)
    simp [hb, Proto.WireType.ofU64?, CryptoVerification.LibsignalProtoCodec.WireType.ofNat?, codecWireTypeToProto]
  · have hb : (key &&& 0x7#64) = 1#64 := BitVec.eq_of_toNat_eq (by rw [hmod, h]; rfl)
    simp [hb, Proto.WireType.ofU64?, CryptoVerification.LibsignalProtoCodec.WireType.ofNat?, codecWireTypeToProto]
  · have hb : (key &&& 0x7#64) = 2#64 := BitVec.eq_of_toNat_eq (by rw [hmod, h]; rfl)
    simp [hb, Proto.WireType.ofU64?, CryptoVerification.LibsignalProtoCodec.WireType.ofNat?, codecWireTypeToProto]
  · have hb : (key &&& 0x7#64) = 3#64 := BitVec.eq_of_toNat_eq (by rw [hmod, h]; rfl)
    simp [hb, Proto.WireType.ofU64?, CryptoVerification.LibsignalProtoCodec.WireType.ofNat?, codecWireTypeToProto]
  · have hb : (key &&& 0x7#64) = 4#64 := BitVec.eq_of_toNat_eq (by rw [hmod, h]; rfl)
    simp [hb, Proto.WireType.ofU64?, CryptoVerification.LibsignalProtoCodec.WireType.ofNat?, codecWireTypeToProto]
  · have hb : (key &&& 0x7#64) = 5#64 := BitVec.eq_of_toNat_eq (by rw [hmod, h]; rfl)
    simp [hb, Proto.WireType.ofU64?, CryptoVerification.LibsignalProtoCodec.WireType.ofNat?, codecWireTypeToProto]
  · have hb : (key &&& 0x7#64) = 6#64 := BitVec.eq_of_toNat_eq (by rw [hmod, h]; rfl)
    simp [hb, Proto.WireType.ofU64?, CryptoVerification.LibsignalProtoCodec.WireType.ofNat?]
  · have hb : (key &&& 0x7#64) = BitVec.ofNat 64 (n + 7) := BitVec.eq_of_toNat_eq (by
      rw [hmod, h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
    have hn0 : n = 0 := by omega
    subst hn0
    simp [hb, Proto.WireType.ofU64?, CryptoVerification.LibsignalProtoCodec.WireType.ofNat?]

private theorem key_tag_toNat_of_lt (key : BitVec 64) (h : key.toNat < 2 ^ 32) :
    ((key >>> 3).truncate 32).toNat = key.toNat / 8 := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  change (key.toNat / 8) % 4294967296 = key.toNat / 8
  exact Nat.mod_eq_of_lt (by omega)

theorem proto_decodeKey_toOption (bs : List (BitVec 8)) :
    (Proto.decodeKey bs).toOption =
      (decodeKey bs).map (fun ((tag, wt), rest) => ((BitVec.ofNat 32 tag, codecWireTypeToProto wt), rest)) := by
  unfold Proto.decodeKey decodeKey
  rcases hdv : Proto.decodeVarint bs with err | ⟨key, rest⟩
  · have hdv' : decodeVarint bs = none := by
      rw [← proto_decodeVarint_toOption bs, hdv]; rfl
    simp [hdv', Bind.bind, Except.bind, Except.toOption]
  · have hdv' : decodeVarint bs = some (key, rest) := by
      rw [← proto_decodeVarint_toOption bs, hdv]; rfl
    simp only [hdv, hdv', Bind.bind, Except.bind, gt_iff_lt]
    by_cases hk : 2 ^ 32 ≤ key.toNat
    · have hk' : 0xffffffff#64 < key := (key_gt_u32Max_iff key).mpr hk
      simp only [hk, hk', ↓reduceIte, Option.map_none, Except.toOption]
    · have hk' : ¬ (0xffffffff#64 < key) := fun h => hk ((key_gt_u32Max_iff key).mp h)
      simp only [hk, hk', ↓reduceIte, wireType_ofU64_eq_ofNat]
      rcases hwt : CryptoVerification.LibsignalProtoCodec.WireType.ofNat? (key.toNat % 8) with _ | wt
      · simp [Except.toOption]
      · simp only [Option.map_some]
        have htag_nat : ((key >>> 3).truncate 32).toNat = key.toNat / 8 :=
          key_tag_toNat_of_lt key (by omega)
        have hmin : ((key >>> 3).truncate 32 < Proto.MIN_TAG) ↔ key.toNat / 8 < 1 := by
          rw [BitVec.lt_def, htag_nat]; rfl
        by_cases ht : key.toNat / 8 < 1
        · have ht' : (key >>> 3).truncate 32 < Proto.MIN_TAG := hmin.mpr ht
          simp [ht, ht', Except.toOption]
        · have ht' : ¬ ((key >>> 3).truncate 32 < Proto.MIN_TAG) := fun h => ht (hmin.mp h)
          have htag_bv : BitVec.ofNat 32 (key.toNat / 8) = (key >>> 3).truncate 32 := by
            apply BitVec.eq_of_toNat_eq
            rw [htag_nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          simp [ht, ht', htag_bv, Except.toOption]

theorem proto_skipFieldNonGroup_toOption (wt : Proto.WireType) (bs : List (BitVec 8))
    (hng : wt ≠ .startGroup) :
    (Proto.skipFieldNonGroup wt bs).toOption =
      if wt == .endGroup then none else skipScalar (protoWireTypeToCodec wt) bs := by
  cases wt <;> simp only [Proto.skipFieldNonGroup, protoWireTypeToCodec, skipScalar]
  case varint =>
    rcases hdv : Proto.decodeVarint bs with err | ⟨v, rest⟩
    · have hdv' : decodeVarint bs = none := by rw [← proto_decodeVarint_toOption bs, hdv]; rfl
      simp [hdv', Bind.bind, Except.bind, Except.toOption]
    · have hdv' : decodeVarint bs = some (v, rest) := by rw [← proto_decodeVarint_toOption bs, hdv]; rfl
      simp [hdv', Bind.bind, Except.bind, Except.toOption]
  case SixtyFourBit =>
    exact proto_dropExact_toOption 8 bs
  case lengthDelimited =>
    rcases hdv : Proto.decodeVarint bs with err | ⟨len, rest⟩
    · have hdv' : decodeVarint bs = none := by rw [← proto_decodeVarint_toOption bs, hdv]; rfl
      simp [hdv', Bind.bind, Except.bind, Except.toOption]
    · have hdv' : decodeVarint bs = some (len, rest) := by rw [← proto_decodeVarint_toOption bs, hdv]; rfl
      simp [hdv', Bind.bind, Except.bind, proto_dropExact_toOption]
  case startGroup =>
    exact (hng rfl).elim
  case endGroup =>
    rfl
  case ThirtyTwoBit =>
    exact proto_dropExact_toOption 4 bs

theorem proto_skipGroupLoop_toOption (depth' : Nat)
    (ih : ∀ (wt : Proto.WireType) (tag : BitVec 32) (bs : List (BitVec 8)),
      (Proto.skipFieldAux depth' wt tag bs).toOption =
        skipField (2 * bs.length + 2) depth' tag.toNat (protoWireTypeToCodec wt) bs) :
    ∀ (fuel : Nat) (tag : BitVec 32) (bs : List (BitVec 8)),
      bs.length ≤ fuel →
      (Proto.skipGroupLoop (Proto.skipFieldAux depth') fuel tag bs).toOption =
        skipGroup (2 * bs.length + 1) (depth' + 1) tag.toNat bs := by
  intro fuel
  induction fuel with
  | zero =>
    intro tag bs hlen
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hbs
    rfl
  | succ fuel ihFuel =>
    intro tag bs hlen
    unfold Proto.skipGroupLoop
    rw [skipGroup.eq_def]
    simp only [Nat.add_eq]
    rcases hdk : Proto.decodeKey bs with err | ⟨⟨itag, iwt⟩, rest⟩
    · have hdk' : decodeKey bs = none := by
        have h := proto_decodeKey_toOption bs
        rw [hdk] at h
        cases hd : decodeKey bs <;> simp [hd, Except.toOption] at h ⊢
      simp [hdk', Bind.bind, Except.bind, Except.toOption]
    · have hdk_opt := proto_decodeKey_toOption bs
      rw [hdk] at hdk_opt
      rcases hdk' : decodeKey bs with _ | ⟨⟨itag_n, iwt_c⟩, rest'⟩
      · simp [hdk', Except.toOption] at hdk_opt
      · simp only [hdk', Option.map_some, Except.toOption, Option.some.injEq, Prod.mk.injEq] at hdk_opt
        rcases hdk_opt with ⟨⟨hitag, hiwt⟩, hrest⟩
        subst hitag hiwt hrest
        have hlt_len : rest.length < bs.length := decodeKey_length hdk'
        have hitag_lt : itag_n < 2 ^ 32 := by
          unfold decodeKey at hdk'
          cases hd : decodeVarint bs with
          | none => simp [hd] at hdk'
          | some p =>
            simp only [hd] at hdk'
            split at hdk'
            · simp at hdk'
            · cases hwt : WireType.ofNat? (p.1.toNat % 8) with
              | none => simp [hwt] at hdk'
              | some w =>
                simp only [hwt] at hdk'
                split at hdk'
                · simp at hdk'
                · simp only [Option.some.injEq, Prod.mk.injEq] at hdk'
                  omega
        have hitag_toNat : (BitVec.ofNat 32 itag_n).toNat = itag_n := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hitag_lt]
        have hih := ih (codecWireTypeToProto iwt_c) (BitVec.ofNat 32 itag_n) rest
        rw [hitag_toNat, protoWireTypeToCodec_codecWireTypeToProto] at hih
        have hfuel_sf : skipField (2 * bs.length) depth' itag_n iwt_c rest =
            skipField (2 * rest.length + 2) depth' itag_n iwt_c rest :=
          skipField_fuel (2 * bs.length) depth' itag_n iwt_c rest (by omega)
        have hstep :
            (do
              let rest' ← Proto.skipFieldAux depth' (codecWireTypeToProto iwt_c) (BitVec.ofNat 32 itag_n) rest
              Proto.skipGroupLoop (Proto.skipFieldAux depth') fuel tag rest').toOption =
            (match skipField (2 * bs.length) depth' itag_n iwt_c rest with
              | none => none
              | some rest' => skipGroup (2 * bs.length) (depth' + 1) tag.toNat rest') := by
          rw [hfuel_sf]
          rcases hsf : Proto.skipFieldAux depth' (codecWireTypeToProto iwt_c) (BitVec.ofNat 32 itag_n) rest with err | rest2
          · rw [hsf] at hih
            dsimp [Except.toOption] at hih
            rw [← hih]
            rfl
          · rw [hsf] at hih
            dsimp [Except.toOption] at hih
            rw [← hih]
            dsimp only [Bind.bind, Except.bind]
            have hle_rest2 : rest2.length ≤ rest.length :=
              (skip_length (2 * rest.length + 2)).1 depth' itag_n iwt_c rest rest2 hih.symm
            rw [ihFuel tag rest2 (by omega)]
            exact ((skip_fuel (2 * rest2.length + 1)).2 (2 * bs.length) (depth' + 1) tag.toNat rest2
              (Nat.le_refl _) (by omega))
        cases iwt_c <;> simp only [codecWireTypeToProto, Bind.bind, Except.bind]
        case endGroup =>
          simp only [beq_self_eq_true, ↓reduceIte]
          by_cases heq : itag_n = tag.toNat
          · have hbeq : (BitVec.ofNat 32 itag_n != tag) = false := by
              rw [bne_eq_false_iff_eq]
              apply BitVec.eq_of_toNat_eq
              rw [hitag_toNat, heq]
            simp [heq, hbeq, Except.toOption]
          · have hbeq : (BitVec.ofNat 32 itag_n != tag) = true := by
              rw [bne_iff_ne]
              intro h
              apply heq
              have := congrArg BitVec.toNat h
              rwa [hitag_toNat] at this
            simp [heq, hbeq, Except.toOption]
        all_goals
          exact hstep

@[simp]
theorem proto_skipFieldAux_toOption (depth : Nat) (wt : Proto.WireType) (tag : BitVec 32)
    (bs : List (BitVec 8)) :
    (Proto.skipFieldAux depth wt tag bs).toOption =
      skipField (2 * bs.length + 2) depth tag.toNat (protoWireTypeToCodec wt) bs := by
  induction depth generalizing wt tag bs with
  | zero =>
    simp [Proto.skipFieldAux, skipField, Except.toOption]
  | succ depth' ih =>
    unfold Proto.skipFieldAux
    rw [skipField.eq_def]
    simp only [Nat.add_eq, Nat.succ_ne_zero, ↓reduceIte]
    by_cases hsg : wt = .startGroup
    · subst hsg
      simp only [beq_self_eq_true, ↓reduceIte, protoWireTypeToCodec]
      exact proto_skipGroupLoop_toOption depth' ih bs.length tag bs (Nat.le_refl _)
    · have hbeq : (wt == .startGroup) = false := beq_false_of_ne hsg
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
      rw [proto_skipFieldNonGroup_toOption wt bs hsg]
      cases wt <;> simp [protoWireTypeToCodec]
      case startGroup => exact (hsg rfl).elim

@[simp]
theorem proto_skipField_toOption (wt : Proto.WireType) (tag : BitVec 32)
    (bs : List (BitVec 8)) (depth : Nat) :
    (Proto.skipField wt tag bs depth).toOption =
      skipField (2 * bs.length + 2) depth tag.toNat (protoWireTypeToCodec wt) bs :=
  proto_skipFieldAux_toOption depth wt tag bs

/-! ## 2. Suffix Laws for `Proto` Primitives & `mergeMessage` -/

open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.RustHeap

theorem proto_decodeVarint_suffix {bs r : List (BitVec 8)} {v : BitVec 64}
    (h : (Proto.decodeVarint bs).toOption = some (v, r)) :
    r.length < bs.length ∧ r = bs.drop (bs.length - r.length) := by
  rw [proto_decodeVarint_toOption] at h
  exact ⟨decodeVarint_length h, decodeVarint_suffix h⟩

theorem proto_takeExact_suffix {n : Nat} {bs sub after : List (BitVec 8)}
    (h : Proto.takeExact n bs = .ok (sub, after)) :
    after.length ≤ bs.length ∧ after = bs.drop (bs.length - after.length) := by
  rw [takeExact_eq_take_drop] at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨_, rfl⟩
    refine ⟨by simp, ?_⟩
    rw [List.length_drop, Nat.sub_sub_self (by omega)]
  · simp at h

theorem proto_mergeBytes_suffix {wt : Proto.WireType} {bs v r : List (BitVec 8)}
    (h : (Proto.mergeBytes wt bs).toOption = some (v, r)) :
    r.length ≤ bs.length ∧ r = bs.drop (bs.length - r.length) := by
  unfold Proto.mergeBytes at h
  rcases hcw : Proto.checkWireType .lengthDelimited wt with e | ⟨⟩
  · simp [hcw, Bind.bind, Except.bind, Except.toOption] at h
  · simp only [hcw, Bind.bind, Except.bind] at h
    rcases hdv : Proto.decodeVarint bs with e | ⟨len64, rest⟩
    · simp [hdv, Except.toOption] at h
    · simp only [hdv] at h
      rcases hte : Proto.takeExact len64.toNat rest with e | ⟨sub, after⟩
      · simp [hte, Except.toOption] at h
      · simp only [hte, Except.toOption, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨_, rfl⟩
        obtain ⟨hlt1, hsuf1⟩ := proto_decodeVarint_suffix (by rw [hdv]; rfl)
        obtain ⟨hle2, hsuf2⟩ := proto_takeExact_suffix hte
        exact ⟨by omega, suffix_trans (Nat.le_of_lt hlt1) hsuf1 hle2 hsuf2⟩

theorem proto_mergeRepeatedBytes_suffix {wt : Proto.WireType}
    {acc : List (List (BitVec 8))} {bs r : List (BitVec 8)} {acc' : List (List (BitVec 8))}
    (h : (Proto.mergeRepeatedBytes wt acc bs).toOption = some (acc', r)) :
    r.length ≤ bs.length ∧ r = bs.drop (bs.length - r.length) := by
  unfold Proto.mergeRepeatedBytes at h
  rcases hmb : Proto.mergeBytes wt bs with e | ⟨v, r'⟩
  · simp [hmb, Bind.bind, Except.bind, Except.toOption] at h
  · simp only [hmb, Bind.bind, Except.bind, Pure.pure, Except.pure, Except.toOption,
      Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨_, rfl⟩
    exact proto_mergeBytes_suffix (by rw [hmb]; rfl)

theorem proto_mergeMessage_suffix {M : Type}
    {mergeField : M → BitVec 32 → Proto.WireType → List (BitVec 8) → Nat → Except Proto.DecodeErr (M × List (BitVec 8))}
    {wt : Proto.WireType} {m m' : M} {bs r : List (BitVec 8)} {depth : Nat}
    (h : (Proto.mergeMessage mergeField wt m bs depth).toOption = some (m', r)) :
    r.length ≤ bs.length ∧ r = bs.drop (bs.length - r.length) := by
  cases depth with
  | zero =>
    rcases hcw : Proto.checkWireType .lengthDelimited wt with e | ⟨⟩ <;>
      simp [Proto.mergeMessage, hcw, Bind.bind, Except.bind, Except.toOption] at h
  | succ depth' =>
    simp only [Proto.mergeMessage, Bind.bind, Except.bind] at h
    rcases hcw : Proto.checkWireType .lengthDelimited wt with e | ⟨⟩
    · simp [hcw, Except.toOption] at h
    · simp only [hcw] at h
      rcases hdv : Proto.decodeVarint bs with e | ⟨len64, rest⟩
      · simp [hdv, Except.toOption] at h
      · simp only [hdv] at h
        rcases hte : Proto.takeExact len64.toNat rest with e | ⟨sub, after⟩
        · simp [hte, Except.toOption] at h
        · simp only [hte] at h
          rcases hloop : Proto.mergeFieldsLoop mergeField sub.length m sub depth' with e | m2
          · simp [hloop, Except.toOption] at h
          · simp only [hloop, Pure.pure, Except.pure, Except.toOption, Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨_, rfl⟩
            obtain ⟨hlt1, hsuf1⟩ := proto_decodeVarint_suffix (by rw [hdv]; rfl)
            obtain ⟨hle2, hsuf2⟩ := proto_takeExact_suffix hte
            exact ⟨by omega, suffix_trans (Nat.le_of_lt hlt1) hsuf1 hle2 hsuf2⟩

theorem proto_mergeOptMessage_suffix {M : Type} [Inhabited M]
    {mergeField : M → BitVec 32 → Proto.WireType → List (BitVec 8) → Nat → Except Proto.DecodeErr (M × List (BitVec 8))}
    {wt : Proto.WireType} {cur : Option M} {m' : Option M} {bs r : List (BitVec 8)} {depth : Nat}
    (h : (Proto.mergeOptMessage mergeField wt cur bs depth).toOption = some (m', r)) :
    r.length ≤ bs.length ∧ r = bs.drop (bs.length - r.length) := by
  unfold Proto.mergeOptMessage at h
  rcases hmsg : Proto.mergeMessage mergeField wt (cur.getD default) bs depth with e | ⟨v, r'⟩
  · simp [hmsg, Bind.bind, Except.bind, Except.toOption] at h
  · simp only [hmsg, Bind.bind, Except.bind, Pure.pure, Except.pure, Except.toOption,
      Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨_, rfl⟩
    exact proto_mergeMessage_suffix (by rw [hmsg]; rfl)

theorem proto_mergeRepeatedMessage_suffix {M : Type} [Inhabited M]
    {mergeField : M → BitVec 32 → Proto.WireType → List (BitVec 8) → Nat → Except Proto.DecodeErr (M × List (BitVec 8))}
    {wt : Proto.WireType} {acc acc' : List M} {bs r : List (BitVec 8)} {depth : Nat}
    (h : (Proto.mergeRepeatedMessage mergeField wt acc bs depth).toOption = some (acc', r)) :
    r.length ≤ bs.length ∧ r = bs.drop (bs.length - r.length) := by
  unfold Proto.mergeRepeatedMessage at h
  rcases hmsg : Proto.mergeMessage mergeField wt default bs depth with e | ⟨v, r'⟩
  · simp [hmsg, Bind.bind, Except.bind, Except.toOption] at h
  · simp only [hmsg, Bind.bind, Except.bind, Pure.pure, Except.pure, Except.toOption,
      Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨_, rfl⟩
    exact proto_mergeMessage_suffix (by rw [hmsg]; rfl)

theorem proto_skipField_suffix {wt : Proto.WireType} {tag : BitVec 32}
    {bs r : List (BitVec 8)} {depth : Nat}
    (h : (Proto.skipField wt tag bs depth).toOption = some r) :
    r.length ≤ bs.length ∧ r = bs.drop (bs.length - r.length) := by
  rw [proto_skipField_toOption] at h
  exact ⟨(skip_length (2 * bs.length + 2)).1 depth tag.toNat (protoWireTypeToCodec wt) bs r h,
    (skip_suffix (2 * bs.length + 2)).1 depth tag.toNat (protoWireTypeToCodec wt) bs r h⟩

theorem proto_decodeKey_suffix {bs r : List (BitVec 8)} {k : BitVec 32 × Proto.WireType}
    (h : (Proto.decodeKey bs).toOption = some (k, r)) :
    r.length < bs.length ∧ r = bs.drop (bs.length - r.length) := by
  rw [proto_decodeKey_toOption, Option.map_eq_some_iff] at h
  obtain ⟨⟨⟨tag, wt⟩, r'⟩, hdk, heq⟩ := h
  injection heq with _ hr
  subst hr
  exact ⟨decodeKey_length hdk, decodeKey_suffix hdk⟩

theorem proto_mergeUint32_suffix {wt : Proto.WireType} {bs r : List (BitVec 8)} {v : BitVec 32}
    (h : (Proto.mergeUint32 wt bs).toOption = some (v, r)) :
    r.length ≤ bs.length ∧ r = bs.drop (bs.length - r.length) := by
  unfold Proto.mergeUint32 at h
  rcases hcw : Proto.checkWireType .varint wt with e | ⟨⟩
  · simp [hcw, Bind.bind, Except.bind, Except.toOption] at h
  · simp only [hcw, Bind.bind, Except.bind] at h
    rcases hdv : Proto.decodeVarint bs with e | ⟨v64, r'⟩
    · simp [hdv, Except.toOption] at h
    · simp only [hdv, Pure.pure, Except.pure, Except.toOption, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨_, rfl⟩
      obtain ⟨hlt, hsuf⟩ := proto_decodeVarint_suffix (by rw [hdv]; rfl)
      exact ⟨Nat.le_of_lt hlt, hsuf⟩

theorem proto_mergeUint64_suffix {wt : Proto.WireType} {bs r : List (BitVec 8)} {v : BitVec 64}
    (h : (Proto.mergeUint64 wt bs).toOption = some (v, r)) :
    r.length ≤ bs.length ∧ r = bs.drop (bs.length - r.length) := by
  unfold Proto.mergeUint64 at h
  rcases hcw : Proto.checkWireType .varint wt with e | ⟨⟩
  · simp [hcw, Bind.bind, Except.bind, Except.toOption] at h
  · simp only [hcw, Bind.bind, Except.bind] at h
    exact ⟨Nat.le_of_lt (proto_decodeVarint_suffix h).1, (proto_decodeVarint_suffix h).2⟩

theorem proto_mergeInt32_suffix {wt : Proto.WireType} {bs r : List (BitVec 8)} {v : BitVec 32}
    (h : (Proto.mergeInt32 wt bs).toOption = some (v, r)) :
    r.length ≤ bs.length ∧ r = bs.drop (bs.length - r.length) :=
  proto_mergeUint32_suffix h

theorem proto_mergeBool_suffix {wt : Proto.WireType} {bs r : List (BitVec 8)} {v : Bool}
    (h : (Proto.mergeBool wt bs).toOption = some (v, r)) :
    r.length ≤ bs.length ∧ r = bs.drop (bs.length - r.length) := by
  unfold Proto.mergeBool at h
  rcases hcw : Proto.checkWireType .varint wt with e | ⟨⟩
  · simp [hcw, Bind.bind, Except.bind, Except.toOption] at h
  · simp only [hcw, Bind.bind, Except.bind] at h
    rcases hdv : Proto.decodeVarint bs with e | ⟨v64, r'⟩
    · simp [hdv, Except.toOption] at h
    · simp only [hdv, Pure.pure, Except.pure, Except.toOption, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨_, rfl⟩
      obtain ⟨hlt, hsuf⟩ := proto_decodeVarint_suffix (by rw [hdv]; rfl)
      exact ⟨Nat.le_of_lt hlt, hsuf⟩

theorem mergeLoopBin_top {M : Type}
    {mergeField : M → BitVec 32 → Proto.WireType → List (BitVec 8) → Nat → Except Proto.DecodeErr (M × List (BitVec 8))}
    (hmf : ∀ m tag wt depth', ProtoPrefixStep (fun bs => mergeField m tag wt bs depth'))
    (m : M) (bs : List (BitVec 8)) (depth' : Nat) :
    mergeLoopBin mergeField bs.length m bs 0 depth' =
      (Proto.mergeFieldsLoop mergeField bs.length m bs depth').toOption := by
  have h := mergeLoopBin_append_eq hmf bs.length bs [] bs.length m depth' (Nat.le_refl _) (Nat.le_refl _)
  simpa using h

/-! ## 3. `mergeLoopBin` Unfolding & Step Lemmas -/

theorem mergeLoopBin_eq_limit {M : Type}
    (mergeField : M → BitVec 32 → Proto.WireType → List (BitVec 8) → Nat → Except Proto.DecodeErr (M × List (BitVec 8)))
    (fuel : Nat) (m : M) (cur : List (BitVec 8)) (limit depth' : Nat)
    (heq : cur.length = limit) :
    mergeLoopBin mergeField fuel m cur limit depth' = some m := by
  rw [mergeLoopBin.eq_def]
  simp [heq]

theorem mergeLoopBin_lt_limit {M : Type}
    (mergeField : M → BitVec 32 → Proto.WireType → List (BitVec 8) → Nat → Except Proto.DecodeErr (M × List (BitVec 8)))
    (fuel : Nat) (m : M) (cur : List (BitVec 8)) (limit depth' : Nat)
    (hlt : cur.length < limit) :
    mergeLoopBin mergeField fuel m cur limit depth' = none := by
  rw [mergeLoopBin.eq_def]
  have hle : cur.length ≤ limit := Nat.le_of_lt hlt
  have hne : (cur.length == limit) = false := beq_false_of_ne (Nat.ne_of_lt hlt)
  simp [hle, hne]

theorem mergeLoopBin_gt_unfold {M : Type}
    {mergeField : M → BitVec 32 → Proto.WireType → List (BitVec 8) → Nat → Except Proto.DecodeErr (M × List (BitVec 8))}
    (hmf : ∀ m tag wt depth', ProtoPrefixStep (fun bs => mergeField m tag wt bs depth'))
    (m : M) (cur : List (BitVec 8)) (limit depth' : Nat)
    (hgt : ¬ cur.length ≤ limit) :
    mergeLoopBin mergeField (cur.length - limit) m cur limit depth' =
      match decodeKey cur with
      | none => none
      | some ((tag, wt), rest) =>
        match (mergeField m (BitVec.ofNat 32 tag) (codecWireTypeToProto wt) rest depth').toOption with
        | none => none
        | some (m', rest') =>
          mergeLoopBin mergeField (rest'.length - limit) m' rest' limit depth' := by
  obtain ⟨f, hf⟩ : ∃ f, cur.length - limit = f + 1 := ⟨cur.length - limit - 1, by omega⟩
  rw [hf, mergeLoopBin.eq_def]
  simp only [hgt, ↓reduceIte, proto_decodeKey_toOption]
  cases hdk : decodeKey cur with
  | none => rfl
  | some p =>
    rcases p with ⟨⟨tag, wt⟩, rest⟩
    dsimp only [Option.map_some]
    have hlt1 : rest.length < cur.length := decodeKey_length hdk
    cases hstep : (mergeField m (BitVec.ofNat 32 tag) (codecWireTypeToProto wt) rest depth').toOption with
    | none => rfl
    | some mr =>
      rcases mr with ⟨m', rest'⟩
      dsimp only
      rcases hmf_ex : mergeField m (BitVec.ofNat 32 tag) (codecWireTypeToProto wt) rest depth' with e | ⟨m2, rest2⟩
      · simp [hmf_ex, Except.toOption] at hstep
      · simp only [hmf_ex, Except.toOption, Option.some.injEq, Prod.mk.injEq] at hstep
        rcases hstep with ⟨hm, hr⟩
        subst m2 rest2
        have hle2 : rest'.length ≤ rest.length := (hmf m _ _ depth').length_le hmf_ex
        exact mergeLoopBin_fuel hmf (rest'.length - limit) rest' limit f (rest'.length - limit) m' depth'
          (Nat.le_refl _) (by omega) (Nat.le_refl _)

theorem mergeLoopBin_of_decodeVarint_none {M : Type}
    {mergeField : M → BitVec 32 → Proto.WireType → List (BitVec 8) → Nat → Except Proto.DecodeErr (M × List (BitVec 8))}
    (hmf : ∀ m tag wt depth', ProtoPrefixStep (fun bs => mergeField m tag wt bs depth'))
    {m : M} {cur : List (BitVec 8)} {limit depth' : Nat}
    (hgt : ¬ cur.length ≤ limit) (hd : decodeVarint cur = none) :
    mergeLoopBin mergeField (cur.length - limit) m cur limit depth' = none := by
  rw [mergeLoopBin_gt_unfold hmf m cur limit depth' hgt, decodeKey, hd]

theorem mergeLoopBin_of_key_ge {M : Type}
    {mergeField : M → BitVec 32 → Proto.WireType → List (BitVec 8) → Nat → Except Proto.DecodeErr (M × List (BitVec 8))}
    (hmf : ∀ m tag wt depth', ProtoPrefixStep (fun bs => mergeField m tag wt bs depth'))
    {m : M} {cur rest : List (BitVec 8)} {key : BitVec 64} {limit depth' : Nat}
    (hgt : ¬ cur.length ≤ limit) (hd : decodeVarint cur = some (key, rest))
    (hk : 2 ^ 32 ≤ key.toNat) :
    mergeLoopBin mergeField (cur.length - limit) m cur limit depth' = none := by
  have hk' : 4294967296 ≤ key.toNat := hk
  rw [mergeLoopBin_gt_unfold hmf m cur limit depth' hgt, decodeKey, hd]
  simp [hk']

theorem mergeLoopBin_of_wt_none {M : Type}
    {mergeField : M → BitVec 32 → Proto.WireType → List (BitVec 8) → Nat → Except Proto.DecodeErr (M × List (BitVec 8))}
    (hmf : ∀ m tag wt depth', ProtoPrefixStep (fun bs => mergeField m tag wt bs depth'))
    {m : M} {cur rest : List (BitVec 8)} {key : BitVec 64} {limit depth' : Nat}
    (hgt : ¬ cur.length ≤ limit) (hd : decodeVarint cur = some (key, rest))
    (hk : ¬ 2 ^ 32 ≤ key.toNat) (hwt : WireType.ofNat? (key.toNat % 8) = none) :
    mergeLoopBin mergeField (cur.length - limit) m cur limit depth' = none := by
  have hk' : ¬ 4294967296 ≤ key.toNat := hk
  rw [mergeLoopBin_gt_unfold hmf m cur limit depth' hgt, decodeKey, hd]
  simp [hk', hwt]

theorem mergeLoopBin_of_tag_zero {M : Type}
    {mergeField : M → BitVec 32 → Proto.WireType → List (BitVec 8) → Nat → Except Proto.DecodeErr (M × List (BitVec 8))}
    (hmf : ∀ m tag wt depth', ProtoPrefixStep (fun bs => mergeField m tag wt bs depth'))
    {m : M} {cur rest : List (BitVec 8)} {key : BitVec 64} {iwt : WireType} {limit depth' : Nat}
    (hgt : ¬ cur.length ≤ limit) (hd : decodeVarint cur = some (key, rest))
    (hk : ¬ 2 ^ 32 ≤ key.toNat) (hwt : WireType.ofNat? (key.toNat % 8) = some iwt)
    (htag : key.toNat / 8 < 1) :
    mergeLoopBin mergeField (cur.length - limit) m cur limit depth' = none := by
  have hk' : ¬ 4294967296 ≤ key.toNat := hk
  have htag' : key.toNat < 8 := by omega
  rw [mergeLoopBin_gt_unfold hmf m cur limit depth' hgt, decodeKey, hd]
  simp [hk', hwt, htag']

theorem mergeLoopBin_of_key_ok {M : Type}
    {mergeField : M → BitVec 32 → Proto.WireType → List (BitVec 8) → Nat → Except Proto.DecodeErr (M × List (BitVec 8))}
    (hmf : ∀ m tag wt depth', ProtoPrefixStep (fun bs => mergeField m tag wt bs depth'))
    {m : M} {cur rest : List (BitVec 8)} {key : BitVec 64} {iwt : WireType} {limit depth' : Nat}
    (hgt : ¬ cur.length ≤ limit) (hd : decodeVarint cur = some (key, rest))
    (hk : ¬ 2 ^ 32 ≤ key.toNat) (hwt : WireType.ofNat? (key.toNat % 8) = some iwt)
    (htag : ¬ key.toNat / 8 < 1) :
    mergeLoopBin mergeField (cur.length - limit) m cur limit depth' =
      match (mergeField m (BitVec.ofNat 32 (key.toNat / 8)) (codecWireTypeToProto iwt) rest depth').toOption with
      | none => none
      | some (m', rest') =>
        mergeLoopBin mergeField (rest'.length - limit) m' rest' limit depth' := by
  have hk' : ¬ 4294967296 ≤ key.toNat := hk
  have htag' : ¬ key.toNat < 8 := by omega
  rw [mergeLoopBin_gt_unfold hmf m cur limit depth' hgt, decodeKey, hd]
  simp [hk', hwt, htag']

/-! ## 3. Shared Bitvector, Cursor, and 96-Byte Frame Helpers -/

theorem wt_beq_two_of_lengthDelimited {w : BitVec 64} (h : w.setWidth 8 = 2#8) :
    (BitVec.truncate 32 w &&& 255#32 == 2#32) = true := by
  revert h; bv_bits

theorem wt_beq_two_of_ne_lengthDelimited {w : BitVec 64} {wt : WireType}
    (h : w.setWidth 8 = BitVec.ofNat 8 wt.toNat) (hne : wt ≠ .lengthDelimited) :
    (BitVec.truncate 32 w &&& 255#32 == 2#32) = false := by
  cases wt <;> first | contradiction | (dsimp [WireType.toNat] at h; revert h; bv_bits)

theorem bv_len_sub_limit {rest_len : Nat} {len : BitVec 64}
    (hge : ¬ rest_len < len.toNat) :
    BitVec.ofNat 64 rest_len - len = BitVec.ofNat 64 (rest_len - len.toNat) := by
  have hsplit : rest_len = (rest_len - len.toNat) + len.toNat := by omega
  conv => lhs; arg 1; rw [hsplit]
  rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_sub_cancel]

theorem cmp_len_limit_of_gt {cur_len limit : Nat} (hgt : ¬ cur_len ≤ limit)
    (hcur : cur_len < 2 ^ 63) :
    (BitVec.ofNat 64 limit).ult (BitVec.ofNat 64 cur_len) = true ∧
      (BitVec.ofNat 64 cur_len).ule (BitVec.ofNat 64 limit) = false := by
  simp only [BitVec.ult, BitVec.ule, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : limit < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : cur_len < 2 ^ 64),
    decide_eq_true_eq, decide_eq_false_iff_not]
  omega

theorem cmp_len_limit_of_eq {cur_len limit : Nat} (heq : cur_len = limit) :
    (BitVec.ofNat 64 limit).ult (BitVec.ofNat 64 cur_len) = false ∧
      (BitVec.ofNat 64 cur_len).ule (BitVec.ofNat 64 limit) = true ∧
      (BitVec.ofNat 64 cur_len == BitVec.ofNat 64 limit) = true := by
  subst heq
  simp [BitVec.ult, BitVec.ule]

theorem cmp_len_limit_of_lt {cur_len limit : Nat} (hlt : cur_len < limit)
    (hlim : limit < 2 ^ 63) :
    (BitVec.ofNat 64 limit).ult (BitVec.ofNat 64 cur_len) = false ∧
      (BitVec.ofNat 64 cur_len).ule (BitVec.ofNat 64 limit) = true ∧
      (BitVec.ofNat 64 cur_len == BitVec.ofNat 64 limit) = false := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [BitVec.ult, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : limit < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : cur_len < 2 ^ 64),
      decide_eq_false_iff_not]
    omega
  · simp only [BitVec.ule, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : limit < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : cur_len < 2 ^ 64),
      decide_eq_true_eq]
    omega
  · rw [beq_eq_false_iff_ne]
    intro h
    have h1 := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : limit < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : cur_len < 2 ^ 64)] at h1
    omega

theorem suffix_eq_drop_of_len_eq {bs rest0 cur : List (BitVec 8)} {len_nat : Nat}
    (hle0 : rest0.length ≤ bs.length) (hsuf0 : IsDropSuffix bs rest0)
    (hge : ¬ rest0.length < len_nat)
    (hle : cur.length ≤ bs.length) (hsuf : IsDropSuffix bs cur)
    (heq : cur.length = rest0.length - len_nat) :
    cur = rest0.drop len_nat := by
  unfold IsDropSuffix at hsuf0 hsuf
  rw [hsuf, hsuf0, List.drop_drop]
  congr 1
  omega

theorem memRegion_48_wtErr96 (sp : BitVec 64) :
    memRegion (sp - 96#64) 48 =
      (∃∗ b1 : BitVec 8, ∃∗ b0 : BitVec 8, ∃∗ v0 : BitVec 64,
        ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₈ b0) ∗ ((sp - 87#64) ↦₈ b1)) ∗
        memRegion (sp - 86#64) 38 := by
  have s1 := ProofLib.memRegion_split (sp - 96#64) 8 40 (by decide)
  rw [ProofLib.bv_sub_add_lit sp 96 8] at s1
  have s2 := ProofLib.memRegion_split (sp - 88#64) 1 39 (by decide)
  rw [ProofLib.bv_sub_add_lit sp 88 1] at s2
  have s3 := ProofLib.memRegion_split (sp - 87#64) 1 38 (by decide)
  rw [ProofLib.bv_sub_add_lit sp 87 1] at s3
  change memRegion (sp - 87#64) 39 = memRegion (sp - 87#64) 1 ∗ memRegion (sp - 86#64) 38 at s3
  rw [s1, s2, s3, ProofLib.memRegion_eight (sp - 96#64),
    ProofLib.memRegion_one (sp - 88#64), ProofLib.memRegion_one (sp - 87#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  ac_rfl

theorem wtErr96_entails_memRegion40 (sp : BitVec 64) (b0 b1 : BitVec 8) :
    ((sp - 88#64) ↦₈ b0) ∗ ((sp - 87#64) ↦₈ b1) ∗ memRegion (sp - 86#64) 38 ⊢
      memRegion (sp - 88#64) 40 := by
  have s2 := ProofLib.memRegion_split (sp - 88#64) 1 39 (by decide)
  rw [ProofLib.bv_sub_add_lit sp 88 1] at s2
  have s3 := ProofLib.memRegion_split (sp - 87#64) 1 38 (by decide)
  rw [ProofLib.bv_sub_add_lit sp 87 1] at s3
  rw [s2, s3]
  exact sepConj_mono (pointsTo8_entails_memRegion1 _ b0)
    (sepConj_mono (pointsTo8_entails_memRegion1 _ b1) (Entails.refl _))

theorem pointsTo64_memRegion40_entails_48 (sp v0 : BitVec 64) :
    ((sp - 96#64) ↦₆₄ v0) ∗ memRegion (sp - 88#64) 40 ⊢
      memRegion (sp - 96#64) 48 := by
  have s1 := ProofLib.memRegion_split (sp - 96#64) 8 40 (by decide)
  rw [ProofLib.bv_sub_add_lit sp 96 8] at s1
  rw [s1]
  exact sepConj_mono_left (pointsTo64_entails_memRegion (sp - 96#64) v0)

abbrev skipBytesMergeRest3 (sp : BitVec 64) (depth : Nat) : SepProp :=
  memRegion (sp - 96#64 - BitVec.ofNat 64 (depth * 0x60 + decodeVarint2Stack))
    (depth * 0x60 - 0xe0)

private theorem bv_sub_96_add_cancel' (sp u w : BitVec 64) :
    sp - 96#64 - w = sp - 96#64 - (u + w) + u := by bv_lin

theorem skipBelow3_bytesMerge3 (sp : BitVec 64) (depth : Nat)
    (hlo : 3 ≤ depth) (hdepth : depth < 2 ^ 32) :
    skipBelow3 sp depth =
      skipBytesMergeRest3 sp depth ∗ stackAt (sp - 96#64) bytesMerge3Stack := by
  simp only [skipBelow3, skipBytesMergeRest3, stackAt]
  have hlen : depth * 0x60 + decodeVarint2Stack =
      (depth * 0x60 - 0xe0) + bytesMerge3Stack := by
    simp only [bytesMerge3Stack]; omega
  have hbound : depth * 0x60 + decodeVarint2Stack ≤ 2 ^ 64 := by
    simp only [decodeVarint2Stack, decodeVarintSlowStack, decodeErrorHookStack, allocHookStack]
    omega
  have hbit : BitVec.ofNat 64 (depth * 0x60 + decodeVarint2Stack) =
      BitVec.ofNat 64 (depth * 0x60 - 0xe0) + BitVec.ofNat 64 bytesMerge3Stack := by
    rw [hlen, BitVec.ofNat_add]
  exact memRegion_split'
    (b := sp - 96#64 - BitVec.ofNat 64 (depth * 0x60 + decodeVarint2Stack))
    (b' := sp - 96#64 - BitVec.ofNat 64 bytesMerge3Stack)
    (n := depth * 0x60 - 0xe0) (k := bytesMerge3Stack)
    (N := depth * 0x60 + decodeVarint2Stack) hlen
    (by rw [hbit]; exact bv_sub_96_add_cancel' sp _ _)
    hbound

theorem skipBelow3_bytesMerge3_entails (sp : BitVec 64) (depth : Nat)
    (hlo : 3 ≤ depth) (hdepth : depth < 2 ^ 32) :
    skipBytesMergeRest3 sp depth ∗ stackAt (sp - 96#64) bytesMerge3Stack ⊢
      skipBelow3 sp depth :=
  Entails.of_eq (skipBelow3_bytesMerge3 sp depth hlo hdepth).symm

theorem decodeErrorWith_zero_entails_le1 (A : RustAlloc) (e : BitVec 64) :
    decodeErrorAtStackLen A e 0 ⊢ ∃∗ n : Nat, ⌜n ≤ 1⌝ ∗ decodeErrorAtStackLen A e n := by
  refine Entails.trans ?_ (Entails.sepExists_intro 0)
  simp only [Nat.zero_le, pure_true, emp_sepConj]
  exact Entails.refl _

theorem decodeErrorWith_one_entails_le1 (A : RustAlloc) (e : BitVec 64) :
    decodeErrorAtStackLen A e 1 ⊢ ∃∗ n : Nat, ⌜n ≤ 1⌝ ∗ decodeErrorAtStackLen A e n := by
  refine Entails.trans ?_ (Entails.sepExists_intro 1)
  simp only [Nat.le_refl, pure_true, emp_sepConj]
  exact Entails.refl _

/-! ## 4. `ImgCallInv` Threading Combinators for `SepWPp` in `message::merge` -/

/-- Run a `SepWP` segment to `mid` while preserving `ImgCallInv img` (`FrozenLoaded ∧ symtab`). -/
theorem SepWPp.of_sepWP_img {prog : Program} {img : Obj.Image} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hinv : ImgCallInv img s)
    (h : SepWP prog mid s P (fun sm Pm =>
      ImgCallInv img sm → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | ⟨hoom, hfalse⟩⟩ := h.elim hm hL
  · obtain ⟨sf, hsteps', hout⟩ :=
      hnext (hinv.of_steps hsteps) R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom, hfalse⟩)⟩

/-- Framed `SepWPp.call` to an `(spec.inImage img)` callee, threading `ImgCallInv img` to `hnext`. -/
theorem SepWPp.call_frame_inImage {α : Type} {prog : Program} {img : Obj.Image}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {φ : Prop}
    {T F : SepProp} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry (spec.inImage img))
    (hinv : ImgCallInv img s)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → ImgCallInv img sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) →
      (sf.mem ⊨ (⌜False⌝ : SepProp) ∗ R') := by wp_close_oom_default) :
    SepWPp prog ret s P Q Qp :=
  ProofLib.SepWPp.call_inImage_frame hcall hinv.1 hinv.2 hpc hrun hsp hlr hspec hφ hP hexit hpanic
    (fun sf hpcf hrunf hspf hcsf hfz hsym => hnext sf hpcf hrunf hspf hcsf ⟨hfz, hsym⟩) hoom

/-- Framed `SepWPp.call` to a raw `spec` callee, preserving `ImgCallInv img` for `hnext`. -/
theorem SepWPp.call_frame_keep {α : Type} {prog : Program} {img : Obj.Image}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {φ : Prop}
    {T F : SepProp} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry spec)
    (hinv : ImgCallInv img s)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → ImgCallInv img sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) →
      (sf.mem ⊨ (⌜False⌝ : SepProp) ∗ R') := by wp_close_oom_default) :
    SepWPp prog ret s P Q Qp :=
  ProofLib.SepWPp.call_frame_frozen hcall hinv.1 hinv.2 hpc hrun hsp hlr hspec hφ hP hexit hpanic
    (fun sf hpcf hrunf hspf hcsf hfz hsym => hnext sf hpcf hrunf hspf hcsf ⟨hfz, hsym⟩) hoom

/-- Irreducible wrapper around `⌜ImgCallInv img s⌝` so `wpp_init` keeps it as a spatial atom
without shifting pure-hypothesis names (`h_1`, `h_2`, `h_3`, `h`). -/
@[irreducible]
def imgCallInvProp (img : Obj.Image) (s : State) : SepProp :=
  ⌜ImgCallInv img s⌝

/-- Variant of `Spec.inImage` that wraps `ImgCallInv img s` in `imgCallInvProp` for `wpp_init`. -/
def withImgProp {α : Type} (spec : Spec α) (img : Obj.Image) : Spec α where
  pre := fun x s => imgCallInvProp img s ∗ spec.pre x s
  post := spec.post
  onExit := spec.onExit
  onPanic := spec.onPanic
  onOom := spec.onOom

theorem withImgProp_eq_inImage {α : Type} (spec : Spec α) (img : Obj.Image) :
    withImgProp spec img = spec.inImage img := by
  unfold withImgProp Spec.inImage imgCallInvProp ImgCallInv
  rfl

theorem subroutine_ok_inImage_of_withImgProp {α : Type} {prog : Program} {img : Obj.Image}
    {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry (withImgProp spec img)) :
    subroutine_ok prog entry (spec.inImage img) :=
  withImgProp_eq_inImage spec img ▸ h

theorem SepWPp.elim_imgCallInvProp {prog : Program} {img : Obj.Image} {ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : ImgCallInv img s → SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s (imgCallInvProp img s ∗ P) Q Qp := by
  unfold imgCallInvProp
  exact ProofLib.SepWPp.pure_elim h

open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.Prost.BytesMerge

/-- Bundle of the contract hypotheses of `bytes_merge_3_ok_ext` (`0x4d13c`) on `tripleRatchetProgAtExt img.base ext`. -/
structure BytesMerge3Contracts (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop where
  loads : Obj.Loads libsignalSessionImage img
  alloc : AllocContracts img.base A ext
  decode_error_from : subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr decodeErrorFromName) (decodeErrorFromSpec A)
  decode_varint2 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr BytesMerge.decodeVarint2Name)
    ((decodeVarint2Spec A).inImage img)
  bytes_from_vec : subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr bytesFromVecName)
    ((bytesFromVecSpec A img.base).inImage img)
  reserve7 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr doReserve7Name) (doReserveSpec A)
  vtable_slot : BytesVtableSlotLoadedStmt
  vtable_drop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      (bytesDropFnAddr img.base tmpPtr v.length)
      ((bytesVtableDropSpec A tmpPtr v v.length).inImage img)

theorem BytesMerge3Contracts.ok_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hBC : BytesMerge3Contracts img A ext) :
    BytesMerge3OkExt img A ext :=
  bytes_merge_3_ok_ext hBC.loads hBC.alloc hBC.decode_error_from hBC.decode_varint2
    hBC.bytes_from_vec hBC.reserve7 hBC.vtable_slot hBC.vtable_drop

/-! ## 5. Relocatable `[LibsignalPlacement]` `LibsignalCodeRoLoaded` Threading Combinators -/

/-- Run a `SepWP` segment to `mid` while preserving `LibsignalCodeRoLoaded pl` (`KeepsFrozen`). -/
theorem SepWPp.of_sepWP_lscro {prog : Program} {pl : Obj.MultiPlacement} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hinv : LibsignalCodeRoLoaded pl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LibsignalCodeRoLoaded pl sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  sepWPp_seq_lscro hinv h

/-- Framed `SepWPp.call` to a `(withLsCodeRoLoaded pl spec)` callee, threading `LibsignalCodeRoLoaded pl` to `hnext`. -/
theorem SepWPp.call_frame_lscro {α : Type} {prog : Program} {pl : Obj.MultiPlacement}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {φ : Prop}
    {T F : SepProp} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded pl spec))
    (hinv : LibsignalCodeRoLoaded pl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → LibsignalCodeRoLoaded pl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) →
      (sf.mem ⊨ (⌜False⌝ : SepProp) ∗ R') := by wp_close_oom_default) :
    SepWPp prog ret s P Q Qp := by
  have h1 : SepWPp prog ret_pc s P
      (fun sm Pm => sm.sp = s.sp ∧ CalleeSavedPreserved s sm ∧
        Pm = spec.post x s sm ∗ F) Qp := by
    refine ProofLib.SepWPp.call (x := x) (F := F) hcall hpc hrun hsp hlr
      (fun R hm => ?_) hexit hpanic
      (fun sm hpcm hrunm hspm hcsm => ProofLib.SepWPp.done hpcm hrunm ⟨hspm, hcsm, rfl⟩)
      hoom
    dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hinv, ?_⟩
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hpost, hspm, hcsm, rfl⟩ | hpan_or_oom⟩ := h1 R hm hL
  · obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm (hinv.of_keepsFrozen hsteps.keepsFrozen) R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr hpan_or_oom⟩

/-- Framed `SepWPp.call` to a raw `spec` callee, preserving `LibsignalCodeRoLoaded pl` for `hnext`. -/
theorem SepWPp.call_frame_keep_lscro {α : Type} {prog : Program} {pl : Obj.MultiPlacement}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {φ : Prop}
    {T F : SepProp} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry spec)
    (hinv : LibsignalCodeRoLoaded pl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → LibsignalCodeRoLoaded pl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) →
      (sf.mem ⊨ (⌜False⌝ : SepProp) ∗ R') := by wp_close_oom_default) :
    SepWPp prog ret s P Q Qp := by
  have h1 : SepWPp prog ret_pc s P
      (fun sm Pm => sm.sp = s.sp ∧ CalleeSavedPreserved s sm ∧
        Pm = spec.post x s sm ∗ F) Qp :=
    ProofLib.SepWPp.call_frame (x := x) (F := F) hcall hpc hrun hsp hlr hspec hφ hP hexit hpanic
      (fun sm hpcm hrunm hspm hcsm => ProofLib.SepWPp.done hpcm hrunm ⟨hspm, hcsm, rfl⟩)
      hoom
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hpost, hspm, hcsm, rfl⟩ | hpan_or_oom⟩ := h1 R hm hL
  · obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm (hinv.of_keepsFrozen hsteps.keepsFrozen) R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr hpan_or_oom⟩

/-- Irreducible wrapper around `⌜LibsignalCodeRoLoaded pl s.mem⌝` so `wpp_init` keeps it as a spatial atom
without shifting pure-hypothesis names (`h_1`, `h_2`, `h_3`, `h`). -/
@[irreducible]
def lscroProp (pl : Obj.MultiPlacement) (s : State) : SepProp :=
  ⌜LibsignalCodeRoLoaded pl s.mem⌝

/-- Variant of `withLsCodeRoLoaded` that wraps `LibsignalCodeRoLoaded pl s.mem` in `lscroProp` for `wpp_init`. -/
def withLscroProp {α : Type} (pl : Obj.MultiPlacement) (spec : Spec α) : Spec α where
  pre := fun x s => lscroProp pl s ∗ spec.pre x s
  post := spec.post
  onExit := spec.onExit
  onPanic := spec.onPanic
  onOom := spec.onOom

theorem subroutine_ok_withLsCodeRoLoaded_of_withLscroProp {α : Type} {prog : Program} {pl : Obj.MultiPlacement}
    {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry (withLscroProp pl spec)) :
    subroutine_ok prog entry (withLsCodeRoLoaded pl spec) := by
  refine subroutine_ok_mono h ?_ (fun _ _ _ _ hq => hq)
  intro x R s0 hp
  obtain ⟨hfr, hp⟩ := extract_withLsCodeRoLoaded hp
  dsimp only [withLscroProp]
  unfold lscroProp
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hfr, hp⟩

theorem SepWPp.elim_lscroProp {prog : Program} {pl : Obj.MultiPlacement} {ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : LibsignalCodeRoLoaded pl s.mem → SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s (lscroProp pl s ∗ P) Q Qp := by
  unfold lscroProp
  exact ProofLib.SepWPp.pure_elim h

end CryptoVerification.SpqrV1.Prost.MessageMerge

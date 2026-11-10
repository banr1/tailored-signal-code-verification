/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.Bridge
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.Fetch -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChain -- shake: keep
public import ProofLib -- shake: keep
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.Defs
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.LibsignalSpqrV1.Top -- shake: keep

/-!
# Binary Verification of `spqr::decode_state` (`0x5349c`, 745 insns) — Definitions & Layouts

**Checked by Lean.**

Defines callee symbol names, stack-frame offsets (`1392` bytes), `Option`/`Result` niche constants,
and pure protobuf merge step lemmas for `VersionNegotiationPB`, `ChainEpochPB`, `ChainPB`, and
`PqRatchetState`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.DecodeState

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.Prost.BytesMerge
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.LibsignalSpqrV1 hiding decodeVarint encodeVarint WireType
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Callee symbol names called by `spqr::decode_state` (`0x5349c`).
    `v1StateMergeName` (`0x4e7e8`) is imported from `CryptoVerification.SpqrV1.Prost.MessageMerge`. -/
def skipField3Name : String :=
  "prost::encoding::skip_field::<&mut &[u8]> [local#3]"

def chainParamsMergeName : String :=
  "prost::encoding::message::merge::<spqr::proto::pq_ratchet::ChainParams, &mut &[u8]>"

def dropOptProtoInnerStateName : String :=
  "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>"

def epochDirectionMergeName : String :=
  "prost::encoding::message::merge::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, &mut &[u8]>"

def dropProtoPqRatchetStateName : String :=
  "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PqRatchetState>"

@[simp, arm64_norm]
theorem skipField3_fnOff :
    libsignalSessionCode.fnOff skipField3Name = 0x4677c :=
  libsignalSessionCode_fnOff_0x4677c

@[simp, arm64_norm]
theorem chainParamsMerge_fnOff :
    libsignalSessionCode.fnOff chainParamsMergeName = 0x48900 :=
  libsignalSessionCode_fnOff_0x48900

@[simp, arm64_norm]
theorem dropOptProtoInnerState_fnOff :
    libsignalSessionCode.fnOff dropOptProtoInnerStateName = 0x46cdc :=
  libsignalSessionCode_fnOff_0x46cdc

@[simp, arm64_norm]
theorem epochDirectionMerge_fnOff :
    libsignalSessionCode.fnOff epochDirectionMergeName = 0x4a14c :=
  libsignalSessionCode_fnOff_0x4a14c

@[simp, arm64_norm]
theorem dropProtoPqRatchetState_fnOff :
    libsignalSessionCode.fnOff dropProtoPqRatchetStateName = 0x47068 :=
  libsignalSessionCode_fnOff_0x47068

macro "decodeState_fetches " b:term:max H:term:max k0:num len:num : tactic =>
  `(tactic| code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.SpqrV1.Top.DecodeState.decodeStateBin $b $H
    CryptoVerification.SpqrV1.Top.DecodeState.decodeState_fnOff 0x4e0a4 $k0 $len)

/-- Own stack frame size of `spqr::decode_state`: `0x60 + 0x510 = 0x570 = 1392` bytes. -/
abbrev decodeStateOwnFrame : Nat := 1392

/-- Niche value `-2` (`0xfffffffffffffffe`) used for `Option<InnerState>::None` and `Result::Err`. -/
def none2Cap : BitVec 64 := 0xfffffffffffffffe#64

/-- Niche value `-3` (`0xfffffffffffffffd`) used for `Option<PqRatchetState.Inner>::None`. -/
def none3Cap : BitVec 64 := 0xfffffffffffffffd#64

@[simp, arm64_norm]
theorem noneCap_add_one_beq_zero : (noneCap + 1#64 == 0#64) = true := rfl

@[simp, arm64_norm]
theorem none2Cap_add_two_beq_zero : (none2Cap + 2#64 == 0#64) = true := rfl

@[simp, arm64_norm]
theorem none3Cap_add_three_beq_zero : (none3Cap + 3#64 == 0#64) = true := rfl

@[simp, arm64_norm]
theorem noneCap_add_two_beq_zero : (noneCap + 2#64 == 0#64) = false := rfl

@[simp, arm64_norm]
theorem noneCap_add_three_beq_zero : (noneCap + 3#64 == 0#64) = false := rfl

@[simp, arm64_norm]
theorem none2Cap_add_three_beq_zero : (none2Cap + 3#64 == 0#64) = false := rfl

theorem cap_add_one_beq_zero_false {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    ¬((cap + 1#64 == 0#64) = true) := by
  rw [beq_iff_eq]
  intro heq
  have hmax : cap = 0xffffffffffffffff#64 := by bv_omega
  subst hmax
  revert h
  decide

theorem cap_add_two_beq_zero_false {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    ¬((cap + 2#64 == 0#64) = true) := by
  rw [beq_iff_eq]
  intro heq
  have hmax : cap = 0xfffffffffffffffe#64 := by bv_omega
  subst hmax
  revert h
  decide

theorem cap_add_three_beq_zero_false {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    ¬((cap + 3#64 == 0#64) = true) := by
  rw [beq_iff_eq]
  intro heq
  have hmax : cap = 0xfffffffffffffffd#64 := by bv_omega
  subst hmax
  revert h
  decide

/-! ## 1. Pure Model Step Lemmas for `VersionNegotiationPB`, `ChainEpochPB`, `ChainPB`, `PqRatchetState` -/

private theorem tag2_beq_1 : (2#32 == 1#32) = false := rfl
private theorem tag3_beq_1 : (3#32 == 1#32) = false := rfl
private theorem tag3_beq_2 : (3#32 == 2#32) = false := rfl
private theorem tag4_beq_1 : (4#32 == 1#32) = false := rfl
private theorem tag4_beq_2 : (4#32 == 2#32) = false := rfl
private theorem tag4_beq_3 : (4#32 == 3#32) = false := rfl
private theorem tag5_beq_1 : (5#32 == 1#32) = false := rfl
private theorem tag5_beq_2 : (5#32 == 2#32) = false := rfl
private theorem tag5_beq_3 : (5#32 == 3#32) = false := rfl
private theorem tag5_beq_4 : (5#32 == 4#32) = false := rfl
private theorem tag6_beq_1 : (6#32 == 1#32) = false := rfl
private theorem tag6_beq_2 : (6#32 == 2#32) = false := rfl
private theorem tag6_beq_3 : (6#32 == 3#32) = false := rfl
private theorem tag6_beq_4 : (6#32 == 4#32) = false := rfl
private theorem tag6_beq_5 : (6#32 == 5#32) = false := rfl

attribute [local simp] tag2_beq_1 tag3_beq_1 tag3_beq_2 tag4_beq_1 tag4_beq_2 tag4_beq_3
  tag5_beq_1 tag5_beq_2 tag5_beq_3 tag5_beq_4 tag6_beq_1 tag6_beq_2 tag6_beq_3 tag6_beq_4 tag6_beq_5

theorem versionNegotiationPB_mergeField_tag1 (m : VersionNegotiationPB) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (VersionNegotiationPB.mergeField m 1#32 (codecWireTypeToProto iwt) rest depth').toOption =
      (Proto.mergeBytes (codecWireTypeToProto iwt) rest).toOption.map
        (fun (v, rest') => ({ m with authKey := v }, rest')) := by
  unfold VersionNegotiationPB.mergeField
  simp only [beq_self_eq_true, ↓reduceIte]
  rcases Proto.mergeBytes (codecWireTypeToProto iwt) rest with e | ⟨v, rest'⟩ <;> rfl

theorem versionNegotiationPB_mergeField_tag2 (m : VersionNegotiationPB) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (VersionNegotiationPB.mergeField m 2#32 (codecWireTypeToProto iwt) rest depth').toOption =
      if iwt = .varint then
        (decodeVarint rest).map (fun (v, rest') => ({ m with direction := v.truncate 32 }, rest'))
      else none := by
  unfold VersionNegotiationPB.mergeField Proto.mergeInt32 Proto.checkWireType
  cases iwt <;> simp only [codecWireTypeToProto, tag2_beq_1, beq_self_eq_true, ↓reduceIte, Bool.false_eq_true]
  case varint =>
    rcases hdv : Proto.decodeVarint rest with e | ⟨v, rest'⟩
    · have hdv' : decodeVarint rest = none := by rw [← proto_decodeVarint_toOption rest, hdv]; rfl
      simp [hdv', Bind.bind, Except.bind, Except.toOption]
    · have hdv' : decodeVarint rest = some (v, rest') := by rw [← proto_decodeVarint_toOption rest, hdv]; rfl
      simp [hdv', Bind.bind, Except.bind, Except.toOption]
  all_goals rfl

theorem versionNegotiationPB_mergeField_tag3 (m : VersionNegotiationPB) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (VersionNegotiationPB.mergeField m 3#32 (codecWireTypeToProto iwt) rest depth').toOption =
      if iwt = .varint then
        (decodeVarint rest).map (fun (v, rest') => ({ m with minVersion := v.truncate 32 }, rest'))
      else none := by
  unfold VersionNegotiationPB.mergeField Proto.mergeInt32 Proto.checkWireType
  cases iwt <;> simp only [codecWireTypeToProto, tag3_beq_1, tag3_beq_2, beq_self_eq_true, ↓reduceIte, Bool.false_eq_true]
  case varint =>
    rcases hdv : Proto.decodeVarint rest with e | ⟨v, rest'⟩
    · have hdv' : decodeVarint rest = none := by rw [← proto_decodeVarint_toOption rest, hdv]; rfl
      simp [hdv', Bind.bind, Except.bind, Except.toOption]
    · have hdv' : decodeVarint rest = some (v, rest') := by rw [← proto_decodeVarint_toOption rest, hdv]; rfl
      simp [hdv', Bind.bind, Except.bind, Except.toOption]
  all_goals rfl

theorem versionNegotiationPB_mergeField_tag4 (m : VersionNegotiationPB) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (VersionNegotiationPB.mergeField m 4#32 (codecWireTypeToProto iwt) rest depth').toOption =
      (Proto.mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto iwt)
        (m.chainParams.getD default) rest depth').toOption.map
        (fun (v, rest') => ({ m with chainParams := some v }, rest')) := by
  unfold VersionNegotiationPB.mergeField Proto.mergeOptMessage
  simp only [tag4_beq_1, tag4_beq_2, tag4_beq_3, beq_self_eq_true, ↓reduceIte, Bool.false_eq_true]
  rcases Proto.mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto iwt)
    (m.chainParams.getD default) rest depth' with e | ⟨v, rest'⟩ <;> rfl

theorem versionNegotiationPB_mergeField_other (m : VersionNegotiationPB) (tag : Nat)
    (ht1 : tag ≠ 1) (ht2 : tag ≠ 2) (ht3 : tag ≠ 3) (ht4 : tag ≠ 4) (ht_lt : tag < 2 ^ 32)
    (iwt : WireType) (rest : List (BitVec 8)) (depth' : Nat) :
    (VersionNegotiationPB.mergeField m (BitVec.ofNat 32 tag) (codecWireTypeToProto iwt) rest depth').toOption =
      (skipField (2 * rest.length + 2) depth' tag iwt rest).map (fun rest' => (m, rest')) := by
  have hb1 : (BitVec.ofNat 32 tag == 1#32) = false := (itag_beq_tag_false ht1 ht_lt (by decide)).1
  have hb2 : (BitVec.ofNat 32 tag == 2#32) = false := (itag_beq_tag_false ht2 ht_lt (by decide)).1
  have hb3 : (BitVec.ofNat 32 tag == 3#32) = false := (itag_beq_tag_false ht3 ht_lt (by decide)).1
  have hb4 : (BitVec.ofNat 32 tag == 4#32) = false := (itag_beq_tag_false ht4 ht_lt (by decide)).1
  have htag_toNat : (BitVec.ofNat 32 tag).toNat = tag := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ht_lt]
  unfold VersionNegotiationPB.mergeField
  simp only [hb1, hb2, hb3, hb4, Bool.false_eq_true, ↓reduceIte]
  rcases hsf : Proto.skipField (codecWireTypeToProto iwt) (BitVec.ofNat 32 tag) rest depth' with e | rest'
  · have hsf' := proto_skipField_toOption (codecWireTypeToProto iwt) (BitVec.ofNat 32 tag) rest depth'
    rw [hsf, htag_toNat, protoWireTypeToCodec_codecWireTypeToProto] at hsf'
    dsimp [Except.toOption] at hsf'
    rw [← hsf']; rfl
  · have hsf' := proto_skipField_toOption (codecWireTypeToProto iwt) (BitVec.ofNat 32 tag) rest depth'
    rw [hsf, htag_toNat, protoWireTypeToCodec_codecWireTypeToProto] at hsf'
    dsimp [Except.toOption] at hsf'
    rw [← hsf']; rfl

theorem chainEpochPB_mergeField_tag1 (m : ChainEpochPB) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (ChainEpochPB.mergeField m 1#32 (codecWireTypeToProto iwt) rest depth').toOption =
      (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt)
        (m.send.getD default) rest depth').toOption.map
        (fun (v, rest') => ({ m with send := some v }, rest')) := by
  unfold ChainEpochPB.mergeField Proto.mergeOptMessage
  simp only [beq_self_eq_true, ↓reduceIte]
  rcases Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt)
    (m.send.getD default) rest depth' with e | ⟨v, rest'⟩ <;> rfl

theorem chainEpochPB_mergeField_tag2 (m : ChainEpochPB) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (ChainEpochPB.mergeField m 2#32 (codecWireTypeToProto iwt) rest depth').toOption =
      (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt)
        (m.recv.getD default) rest depth').toOption.map
        (fun (v, rest') => ({ m with recv := some v }, rest')) := by
  unfold ChainEpochPB.mergeField Proto.mergeOptMessage
  simp only [tag2_beq_1, beq_self_eq_true, ↓reduceIte, Bool.false_eq_true]
  rcases Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt)
    (m.recv.getD default) rest depth' with e | ⟨v, rest'⟩ <;> rfl

theorem chainEpochPB_mergeField_other (m : ChainEpochPB) (tag : Nat)
    (ht1 : tag ≠ 1) (ht2 : tag ≠ 2) (ht_lt : tag < 2 ^ 32)
    (iwt : WireType) (rest : List (BitVec 8)) (depth' : Nat) :
    (ChainEpochPB.mergeField m (BitVec.ofNat 32 tag) (codecWireTypeToProto iwt) rest depth').toOption =
      (skipField (2 * rest.length + 2) depth' tag iwt rest).map (fun rest' => (m, rest')) := by
  have hb1 : (BitVec.ofNat 32 tag == 1#32) = false := (itag_beq_tag_false ht1 ht_lt (by decide)).1
  have hb2 : (BitVec.ofNat 32 tag == 2#32) = false := (itag_beq_tag_false ht2 ht_lt (by decide)).1
  have htag_toNat : (BitVec.ofNat 32 tag).toNat = tag := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ht_lt]
  unfold ChainEpochPB.mergeField
  simp only [hb1, hb2, Bool.false_eq_true, ↓reduceIte]
  rcases hsf : Proto.skipField (codecWireTypeToProto iwt) (BitVec.ofNat 32 tag) rest depth' with e | rest'
  · have hsf' := proto_skipField_toOption (codecWireTypeToProto iwt) (BitVec.ofNat 32 tag) rest depth'
    rw [hsf, htag_toNat, protoWireTypeToCodec_codecWireTypeToProto] at hsf'
    dsimp [Except.toOption] at hsf'
    rw [← hsf']; rfl
  · have hsf' := proto_skipField_toOption (codecWireTypeToProto iwt) (BitVec.ofNat 32 tag) rest depth'
    rw [hsf, htag_toNat, protoWireTypeToCodec_codecWireTypeToProto] at hsf'
    dsimp [Except.toOption] at hsf'
    rw [← hsf']; rfl

theorem chainPB_mergeField_tag1 (m : ChainPB) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (ChainPB.mergeField m 1#32 (codecWireTypeToProto iwt) rest depth').toOption =
      if iwt = .varint then
        (decodeVarint rest).map (fun (v, rest') => ({ m with direction := v.truncate 32 }, rest'))
      else none := by
  unfold ChainPB.mergeField Proto.mergeInt32 Proto.checkWireType
  cases iwt <;> simp only [codecWireTypeToProto, beq_self_eq_true, ↓reduceIte, Bool.false_eq_true]
  case varint =>
    rcases hdv : Proto.decodeVarint rest with e | ⟨v, rest'⟩
    · have hdv' : decodeVarint rest = none := by rw [← proto_decodeVarint_toOption rest, hdv]; rfl
      simp [hdv', Bind.bind, Except.bind, Except.toOption]
    · have hdv' : decodeVarint rest = some (v, rest') := by rw [← proto_decodeVarint_toOption rest, hdv]; rfl
      simp [hdv', Bind.bind, Except.bind, Except.toOption]
  all_goals rfl

theorem chainPB_mergeField_tag2 (m : ChainPB) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (ChainPB.mergeField m 2#32 (codecWireTypeToProto iwt) rest depth').toOption =
      if iwt = .varint then
        (decodeVarint rest).map (fun (v, rest') => ({ m with currentEpoch := v }, rest'))
      else none := by
  unfold ChainPB.mergeField Proto.mergeUint64 Proto.checkWireType
  cases iwt <;> simp only [codecWireTypeToProto, tag2_beq_1, beq_self_eq_true, ↓reduceIte, Bool.false_eq_true]
  case varint =>
    rcases hdv : Proto.decodeVarint rest with e | ⟨v, rest'⟩
    · have hdv' : decodeVarint rest = none := by rw [← proto_decodeVarint_toOption rest, hdv]; rfl
      simp [hdv', Bind.bind, Except.bind, Except.toOption]
    · have hdv' : decodeVarint rest = some (v, rest') := by rw [← proto_decodeVarint_toOption rest, hdv]; rfl
      simp [hdv', Bind.bind, Except.bind, Except.toOption]
  all_goals rfl

theorem chainPB_mergeField_tag3 (m : ChainPB) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (ChainPB.mergeField m 3#32 (codecWireTypeToProto iwt) rest depth').toOption =
      (Proto.mergeMessage ChainEpochPB.mergeField (codecWireTypeToProto iwt)
        default rest depth').toOption.map
        (fun (v, rest') => ({ m with links := m.links ++ [v] }, rest')) := by
  unfold ChainPB.mergeField Proto.mergeRepeatedMessage
  simp only [tag3_beq_1, tag3_beq_2, beq_self_eq_true, ↓reduceIte, Bool.false_eq_true]
  rcases Proto.mergeMessage ChainEpochPB.mergeField (codecWireTypeToProto iwt)
    default rest depth' with e | ⟨v, rest'⟩ <;> rfl

theorem chainPB_mergeField_tag4 (m : ChainPB) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (ChainPB.mergeField m 4#32 (codecWireTypeToProto iwt) rest depth').toOption =
      (Proto.mergeBytes (codecWireTypeToProto iwt) rest).toOption.map
        (fun (v, rest') => ({ m with nextRoot := v }, rest')) := by
  unfold ChainPB.mergeField
  simp only [tag4_beq_1, tag4_beq_2, tag4_beq_3, beq_self_eq_true, ↓reduceIte, Bool.false_eq_true]
  rcases Proto.mergeBytes (codecWireTypeToProto iwt) rest with e | ⟨v, rest'⟩ <;> rfl

theorem chainPB_mergeField_tag5 (m : ChainPB) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (ChainPB.mergeField m 5#32 (codecWireTypeToProto iwt) rest depth').toOption =
      if iwt = .varint then
        (decodeVarint rest).map (fun (v, rest') => ({ m with sendEpoch := v }, rest'))
      else none := by
  unfold ChainPB.mergeField Proto.mergeUint64 Proto.checkWireType
  cases iwt <;> simp only [codecWireTypeToProto, tag5_beq_1, tag5_beq_2, tag5_beq_3, tag5_beq_4,
    beq_self_eq_true, ↓reduceIte, Bool.false_eq_true]
  case varint =>
    rcases hdv : Proto.decodeVarint rest with e | ⟨v, rest'⟩
    · have hdv' : decodeVarint rest = none := by rw [← proto_decodeVarint_toOption rest, hdv]; rfl
      simp [hdv', Bind.bind, Except.bind, Except.toOption]
    · have hdv' : decodeVarint rest = some (v, rest') := by rw [← proto_decodeVarint_toOption rest, hdv]; rfl
      simp [hdv', Bind.bind, Except.bind, Except.toOption]
  all_goals rfl

theorem chainPB_mergeField_tag6 (m : ChainPB) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (ChainPB.mergeField m 6#32 (codecWireTypeToProto iwt) rest depth').toOption =
      (Proto.mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto iwt)
        (m.params.getD default) rest depth').toOption.map
        (fun (v, rest') => ({ m with params := some v }, rest')) := by
  unfold ChainPB.mergeField Proto.mergeOptMessage
  simp only [tag6_beq_1, tag6_beq_2, tag6_beq_3, tag6_beq_4, tag6_beq_5,
    beq_self_eq_true, ↓reduceIte, Bool.false_eq_true]
  rcases Proto.mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto iwt)
    (m.params.getD default) rest depth' with e | ⟨v, rest'⟩ <;> rfl

theorem chainPB_mergeField_other (m : ChainPB) (tag : Nat)
    (ht1 : tag ≠ 1) (ht2 : tag ≠ 2) (ht3 : tag ≠ 3) (ht4 : tag ≠ 4)
    (ht5 : tag ≠ 5) (ht6 : tag ≠ 6) (ht_lt : tag < 2 ^ 32)
    (iwt : WireType) (rest : List (BitVec 8)) (depth' : Nat) :
    (ChainPB.mergeField m (BitVec.ofNat 32 tag) (codecWireTypeToProto iwt) rest depth').toOption =
      (skipField (2 * rest.length + 2) depth' tag iwt rest).map (fun rest' => (m, rest')) := by
  have hb1 : (BitVec.ofNat 32 tag == 1#32) = false := (itag_beq_tag_false ht1 ht_lt (by decide)).1
  have hb2 : (BitVec.ofNat 32 tag == 2#32) = false := (itag_beq_tag_false ht2 ht_lt (by decide)).1
  have hb3 : (BitVec.ofNat 32 tag == 3#32) = false := (itag_beq_tag_false ht3 ht_lt (by decide)).1
  have hb4 : (BitVec.ofNat 32 tag == 4#32) = false := (itag_beq_tag_false ht4 ht_lt (by decide)).1
  have hb5 : (BitVec.ofNat 32 tag == 5#32) = false := (itag_beq_tag_false ht5 ht_lt (by decide)).1
  have hb6 : (BitVec.ofNat 32 tag == 6#32) = false := (itag_beq_tag_false ht6 ht_lt (by decide)).1
  have htag_toNat : (BitVec.ofNat 32 tag).toNat = tag := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ht_lt]
  unfold ChainPB.mergeField
  simp only [hb1, hb2, hb3, hb4, hb5, hb6, Bool.false_eq_true, ↓reduceIte]
  rcases hsf : Proto.skipField (codecWireTypeToProto iwt) (BitVec.ofNat 32 tag) rest depth' with e | rest'
  · have hsf' := proto_skipField_toOption (codecWireTypeToProto iwt) (BitVec.ofNat 32 tag) rest depth'
    rw [hsf, htag_toNat, protoWireTypeToCodec_codecWireTypeToProto] at hsf'
    dsimp [Except.toOption] at hsf'
    rw [← hsf']; rfl
  · have hsf' := proto_skipField_toOption (codecWireTypeToProto iwt) (BitVec.ofNat 32 tag) rest depth'
    rw [hsf, htag_toNat, protoWireTypeToCodec_codecWireTypeToProto] at hsf'
    dsimp [Except.toOption] at hsf'
    rw [← hsf']; rfl

theorem pqRatchetState_mergeField_tag1 (m : PqRatchetState) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (PqRatchetState.mergeField m 1#32 (codecWireTypeToProto iwt) rest depth').toOption =
      (Proto.mergeMessage VersionNegotiationPB.mergeField (codecWireTypeToProto iwt)
        (m.versionNegotiation.getD default) rest depth').toOption.map
        (fun (v, rest') => ({ m with versionNegotiation := some v }, rest')) := by
  unfold PqRatchetState.mergeField Proto.mergeOptMessage
  simp only [beq_self_eq_true, ↓reduceIte]
  rcases Proto.mergeMessage VersionNegotiationPB.mergeField (codecWireTypeToProto iwt)
    (m.versionNegotiation.getD default) rest depth' with e | ⟨v, rest'⟩ <;> rfl

theorem pqRatchetState_mergeField_tag2 (m : PqRatchetState) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (PqRatchetState.mergeField m 2#32 (codecWireTypeToProto iwt) rest depth').toOption =
      (Proto.mergeMessage ChainPB.mergeField (codecWireTypeToProto iwt)
        (m.chain.getD default) rest depth').toOption.map
        (fun (v, rest') => ({ m with chain := some v }, rest')) := by
  unfold PqRatchetState.mergeField Proto.mergeOptMessage
  simp only [tag2_beq_1, beq_self_eq_true, ↓reduceIte, Bool.false_eq_true]
  rcases Proto.mergeMessage ChainPB.mergeField (codecWireTypeToProto iwt)
    (m.chain.getD default) rest depth' with e | ⟨v, rest'⟩ <;> rfl

theorem pqRatchetState_mergeField_tag3 (m : PqRatchetState) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (PqRatchetState.mergeField m 3#32 (codecWireTypeToProto iwt) rest depth').toOption =
      (Proto.mergeMessage V1State.mergeField (codecWireTypeToProto iwt)
        (match m.inner with | some (.v1 v) => v | none => default) rest depth').toOption.map
        (fun (v, rest') => ({ m with inner := some (.v1 v) }, rest')) := by
  unfold PqRatchetState.mergeField PqRatchetState.Inner.merge
  simp only [tag3_beq_1, tag3_beq_2, beq_self_eq_true, ↓reduceIte, Bool.false_eq_true]
  rcases Proto.mergeMessage V1State.mergeField (codecWireTypeToProto iwt)
    (match m.inner with | some (.v1 v) => v | none => default) rest depth' with e | ⟨v, rest'⟩ <;> rfl

theorem pqRatchetState_mergeField_other (m : PqRatchetState) (tag : Nat)
    (ht1 : tag ≠ 1) (ht2 : tag ≠ 2) (ht3 : tag ≠ 3) (ht_lt : tag < 2 ^ 32)
    (iwt : WireType) (rest : List (BitVec 8)) (depth' : Nat) :
    (PqRatchetState.mergeField m (BitVec.ofNat 32 tag) (codecWireTypeToProto iwt) rest depth').toOption =
      (skipField (2 * rest.length + 2) depth' tag iwt rest).map (fun rest' => (m, rest')) := by
  have hb1 : (BitVec.ofNat 32 tag == 1#32) = false := (itag_beq_tag_false ht1 ht_lt (by decide)).1
  have hb2 : (BitVec.ofNat 32 tag == 2#32) = false := (itag_beq_tag_false ht2 ht_lt (by decide)).1
  have hb3 : (BitVec.ofNat 32 tag == 3#32) = false := (itag_beq_tag_false ht3 ht_lt (by decide)).1
  have htag_toNat : (BitVec.ofNat 32 tag).toNat = tag := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ht_lt]
  unfold PqRatchetState.mergeField
  simp only [hb1, hb2, hb3, Bool.false_eq_true, ↓reduceIte]
  rcases hsf : Proto.skipField (codecWireTypeToProto iwt) (BitVec.ofNat 32 tag) rest depth' with e | rest'
  · have hsf' := proto_skipField_toOption (codecWireTypeToProto iwt) (BitVec.ofNat 32 tag) rest depth'
    rw [hsf, htag_toNat, protoWireTypeToCodec_codecWireTypeToProto] at hsf'
    dsimp [Except.toOption] at hsf'
    rw [← hsf']; rfl
  · have hsf' := proto_skipField_toOption (codecWireTypeToProto iwt) (BitVec.ofNat 32 tag) rest depth'
    rw [hsf, htag_toNat, protoWireTypeToCodec_codecWireTypeToProto] at hsf'
    dsimp [Except.toOption] at hsf'
    rw [← hsf']; rfl

@[simp]
theorem pqRatchetState_default_eq :
    (default : PqRatchetState) =
      { versionNegotiation := none, chain := none, inner := none } := rfl

@[simp]
theorem versionNegotiationPB_default_eq :
    (default : VersionNegotiationPB) =
      { authKey := [], direction := 0#32, minVersion := 0#32, chainParams := none } := rfl

@[simp]
theorem chainPB_default_eq :
    (default : ChainPB) =
      { direction := 0#32, currentEpoch := 0#64, links := [], nextRoot := [],
        sendEpoch := 0#64, params := none } := rfl

@[simp]
theorem chainEpochPB_default_eq :
    (default : ChainEpochPB) = { send := none, recv := none } := rfl

@[simp]
theorem epochDirectionPB_default_eq :
    (default : EpochDirectionPB) = { ctr := 0#32, next := [], prev := [] } := rfl

@[simp]
theorem chainParamsPB_default_eq :
    (default : ChainParamsPB) = { maxJump := 0#32, maxOooKeys := 0#32 } := rfl

@[simp]
theorem v1State_default_eq :
    (default : V1State) = { innerState := none } := rfl

@[simp]
theorem spqrDecodeState_nil :
    Proto.spqrDecodeState [] = .ok default := rfl

theorem spqrDecodeState_eq_of_ne_nil {bs : List (BitVec 8)} (hne : bs ≠ []) :
    (Proto.spqrDecodeState bs).toOption = (PqRatchetState.decode bs).toOption := by
  cases bs with
  | nil => exact (hne rfl).elim
  | cons b tl =>
    unfold Proto.spqrDecodeState
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
    rcases PqRatchetState.decode (b :: tl) with e | st <;> rfl

theorem pqRatchetState_decode_toOption_eq_mergeLoopBin (bs : List (BitVec 8)) :
    (PqRatchetState.decode bs).toOption =
      mergeLoopBin PqRatchetState.mergeField bs.length default bs 0 100 := by
  have h := mergeLoopBin_append_eq protoPrefixStep_pqRatchetState_mergeField
    bs.length bs [] bs.length default 100 (Nat.le_refl _) (Nat.le_refl _)
  simp only [List.append_nil, List.length_nil] at h
  exact h.symm

theorem spqrDecodeState_toOption_eq_mergeLoopBin {bs : List (BitVec 8)} (hne : bs ≠ []) :
    (Proto.spqrDecodeState bs).toOption =
      mergeLoopBin PqRatchetState.mergeField bs.length default bs 0 100 := by
  rw [spqrDecodeState_eq_of_ne_nil hne, pqRatchetState_decode_toOption_eq_mergeLoopBin]

end CryptoVerification.SpqrV1.Top.DecodeState

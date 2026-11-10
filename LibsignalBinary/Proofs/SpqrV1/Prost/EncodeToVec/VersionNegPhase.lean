/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhase
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.Decodes
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodedLenVn
import ProofLib.SepLogic.WPp

/-!
# Phase 2b (`0x6d254 .. 0x6d4cc`): `Option<VersionNegotiation>` Encoding

Proves symbolic execution of the inline `Option<VersionNegotiation>` encoding phase
(`+580 .. +1212`, `0x6d254 .. 0x6d4cc`) in
`<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec`,
producing `vecU8At A (sp - 120#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr
  (Proto.encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 st.versionNegotiation)` at
`entry + 1212#64` (`0x6d4cc`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Prost.EncodeToVec

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  EncodedLen.zeroExtend64_beq_zero32
  EncodedLen.ofNat_countLeadingZeros_64 EncodedLen.ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 EncodedLen.hwVarintLen_eq_ofNat_varintLen_norm
  EncodedLen.hwVarintLen_bvShift_eq_ofNat_varintLen_norm EncodedLen.zext64_truncate32
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
  EncodedLen.ule_zero_64 EncodedLen.ult_zero_64 ule_self_64 ult_self_64

/-! ## 1. Pure Protobuf Encoding Bridge Lemmas for `VersionNegotiationPB` -/

theorem encodeKey_1_lengthDelimited :
    Proto.encodeKey 1#32 .lengthDelimited = [0x0a#8] := by decide

theorem encodeKey_2_varint :
    Proto.encodeKey 2#32 .varint = [0x10#8] := by decide

theorem encodeKey_3_varint :
    Proto.encodeKey 3#32 .varint = [0x18#8] := by decide

theorem encodeBytesField_1_eq (bs : List (BitVec 8)) :
    Proto.encodeBytesField 1#32 bs =
      if bs.isEmpty then []
      else [0x0a#8] ++ Proto.encodeVarint (BitVec.ofNat 64 bs.length) ++ bs := by
  unfold Proto.encodeBytesField Proto.encodeBytesUncond
  rw [encodeKey_1_lengthDelimited]

theorem encodeInt32Field_2_eq (v : BitVec 32) :
    Proto.encodeInt32Field 2#32 v =
      if v == 0#32 then []
      else [0x10#8] ++ Proto.encodeVarint (v.signExtend 64) := by
  unfold Proto.encodeInt32Field
  rw [encodeKey_2_varint]

theorem encodeInt32Field_3_eq (v : BitVec 32) :
    Proto.encodeInt32Field 3#32 v =
      if v == 0#32 then []
      else [0x18#8] ++ Proto.encodeVarint (v.signExtend 64) := by
  unfold Proto.encodeInt32Field
  rw [encodeKey_3_varint]

theorem encodeOptMessage_versionNeg_some (vn : VersionNegotiationPB) :
    Proto.encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 (some vn) =
      [0x0a#8] ++ Proto.encodeVarint (BitVec.ofNat 64 (versionNegotiationPBEncodedLen vn)) ++
        Proto.encodeBytesField 1#32 vn.authKey ++
        Proto.encodeInt32Field 2#32 vn.direction ++
        Proto.encodeInt32Field 3#32 vn.minVersion ++
        Proto.encodeOptMessage ChainParamsPB.encodeRaw 4#32 vn.chainParams := by
  have hlen : (VersionNegotiationPB.encodeRaw vn).length = versionNegotiationPBEncodedLen vn :=
    versionNegotiationPBEncodedLen_eq_proto vn
  dsimp only [Proto.encodeOptMessage, Proto.encodeMessage]
  rw [encodeKey_1_lengthDelimited, hlen]
  dsimp only [VersionNegotiationPB.encodeRaw, Proto.encodeOptMessage, Proto.encodeMessage]
  simp only [List.append_assoc]

theorem optVersionNegotiationPB_encode_len_le (st : PqRatchetState) :
    (Proto.encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 st.versionNegotiation).length ≤
      pqRatchetStatePBEncodedLen st := by
  rw [optVersionNegotiationPBFieldEncodedLen_eq_proto 1#32 st.versionNegotiation ⟨by decide, by decide⟩]
  unfold pqRatchetStatePBEncodedLen
  omega

/-- Discriminant tag (`0#32` or `1#32`) of `Option<ChainParamsPB>`. -/
def optChainParamsTag : Option ChainParamsPB → BitVec 32
  | none => 0#32
  | some _ => 1#32

@[simp, arm64_norm] theorem optChainParamsTag_zext_trunc (opt : Option ChainParamsPB) :
    ((optChainParamsTag opt).zeroExtend 64).truncate 32 = optChainParamsTag opt := by
  cases opt <;> rfl

@[simp, arm64_norm] theorem optChainParamsTag_zext_zext (opt : Option ChainParamsPB) :
    (((optChainParamsTag opt).zeroExtend 64).truncate 32).zeroExtend 64 =
      (optChainParamsTag opt).zeroExtend 64 := by
  cases opt <;> rfl

/-! ## 2. Sub-Step Lemmas for `VersionNegotiationPB` Encoding (`0x6d254 .. 0x6d4cc`) -/

/-- Step `+580 .. +604` (`0x6d254 .. 0x6d268`): writes the outer `VersionNegotiation` tag `0x0a#8`
into `vecU8At A (sp - 120#64) cap ptr []` and loads `x25 = BitVec.ofNat 64 vn.authKey.length`. -/
theorem step_encodeToVec_vn_push_tag (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry)
    (a sp cap ptr : BitVec 64) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB)
    (hpos : 0 < cap.toNat) (halign : sp &&& 15#64 = 0#64)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 580#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (hx0 : s.readReg64 .x0 = ptr)
    (hx20 : s.readReg64 .x20 = a) (hinv0 : StepInv s0 s)
    (hP : P = (versionNegotiationRest A g a vn ∗ vecU8At A (sp - 120#64) cap ptr []) ∗ F)
    (hnext : ∀ s1 : State,
      s1.pc = entry + 604#64 → s1.status = .Running → s1.sp = sp - 144#64 → s1.trace = s.trace →
      s1.readReg64 .x19 = s.readReg64 .x19 → s1.readReg64 .x20 = a →
      s1.readReg64 .x21 = s.readReg64 .x21 → s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x25 = BitVec.ofNat 64 vn.authKey.length →
      s1.readReg64 .x27 = s.readReg64 .x27 → s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .fp = s.readReg64 .fp → StepInv s0 s1 →
      SepWPp (spqrProgAtExt b ext) ret s1
        ((versionNegotiationRest A g a vn ∗ vecU8At A (sp - 120#64) cap ptr [0x0a#8]) ∗ F) Q Qp) :
    SepWPp (spqrProgAtExt b ext) ret s P Q Qp := by
  etv_fetches b (Rust.withPanics ext) hfn 580 604
  examples_hide_fetches; subst hP
  have hsp_align : (sp - 144#64) &&& 15#64 = 0#64 := sp_sub_144_aligned halign
  refine sepWPp_extract_vecU8At_bounds (v := sp - 120#64) (cap := cap) (ptr := ptr) (bs := [])
    (F := versionNegotiationRest A g a vn ∗ F) (by ac_rfl) fun _ hcap hptr => ?_
  rw [vecU8At_expose_one A (sp - 120#64) cap ptr [] (by simpa using hpos) hcap hptr]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun b0 => ?_
  dsimp only [versionNegotiationRest, List.length_nil, BitVec.ofNat_eq_ofNat]
  have h112 : (sp - 120#64) + 8#64 = sp - 112#64 := by bv_omega
  have h104 : (sp - 120#64) + 16#64 = sp - 104#64 := by bv_omega
  have hptr0 : ptr + 0#64 = ptr := by bv_omega
  rw [h112, h104, hptr0]
  apply SepWPp.of_sepWP_cs (mid := entry + 604#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
  refine SepWPp.weaken_pre ?_
    (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv))
  have hpack := vecU8At_pack_one A (sp - 120#64) cap ptr [] 0x0a#8 (by simpa using hpos) hcap hptr
  dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat, List.nil_append] at hpack
  have h01 : (0#64 : BitVec 64) + 1#64 = 1#64 := rfl
  rw [h112, h104, hptr0, h01] at hpack; rw [← hpack]
  dsimp only [versionNegotiationRest]; exact Entails.of_eq (by ac_rfl)

/-- Step `+604 .. +640/+872` (`0x6d26c .. 0x6d290/0x6d378`): computes
`x8 = BitVec.ofNat 64 (bytesFieldEncodedLen vn.authKey)` and loads `x24 = vn.direction.signExtend 64`. -/
theorem step_encodeToVec_vn_authKey_len (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry)
    (a : BitVec 64) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB)
    (hlen : vn.authKey.length < 2 ^ 64)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 604#64) (hrun : s.status = .Running)
    (hx20 : s.readReg64 .x20 = a) (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 vn.authKey.length)
    (hinv0 : StepInv s0 s) (hP : P = versionNegotiationRest A g a vn ∗ F)
    (hnext : ∀ s1 : State,
      (s1.pc = entry + 640#64 ∨ s1.pc = entry + 872#64) →
      s1.status = .Running → s1.sp = s.sp → s1.trace = s.trace →
      s1.readReg64 .x8 = BitVec.ofNat 64 (bytesFieldEncodedLen vn.authKey) →
      s1.readReg64 .x19 = s.readReg64 .x19 → s1.readReg64 .x20 = a →
      s1.readReg64 .x21 = s.readReg64 .x21 → s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x24 = vn.direction.signExtend 64 →
      s1.readReg64 .x25 = BitVec.ofNat 64 vn.authKey.length →
      s1.readReg64 .x27 = s.readReg64 .x27 → s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .fp = s.readReg64 .fp → StepInv s0 s1 →
      SepWPp (spqrProgAtExt b ext) ret s1 (versionNegotiationRest A g a vn ∗ F) Q Qp) :
    SepWPp (spqrProgAtExt b ext) ret s P Q Qp := by
  etv_fetches b (Rust.withPanics ext) hfn 604 640
  etv_fetches b (Rust.withPanics ext) hfn 864 872
  examples_hide_fetches; subst hP; dsimp only [versionNegotiationRest]
  obtain ⟨hbeqz, hbnez⟩ := EncodedLen.ofNat_length_beq_zero_of_lt hlen
  cases hemp : vn.authKey.isEmpty
  · have hstep := EncodedLen.bv_bytesField_nonempty hemp
    simp only [hemp, Bool.not_false] at hbeqz hbnez
    apply SepWPp.of_sepWP_cs (mid := entry + 640#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    exact hnext _ (Or.inl (by simp only [arm64_norm, *]))
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (hinv0.trans hinv)
  · simp only [hemp, Bool.not_true] at hbeqz hbnez
    have hzero : bytesFieldEncodedLen vn.authKey = 0 := by unfold bytesFieldEncodedLen; simp [hemp]
    apply SepWPp.of_sepWP_cs (mid := entry + 872#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    exact hnext _ (Or.inr (by simp only [arm64_norm, *]))
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, hzero, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (hinv0.trans hinv)

/-- Step `+640/+872 .. +676/+884` (`0x6d290/0x6d378 .. 0x6d2b4/0x6d384`): computes
`x9 = BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.direction)` and loads `x23 = vn.minVersion.signExtend 64`. -/
theorem step_encodeToVec_vn_dir_len (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry)
    (a : BitVec 64) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 640#64 ∨ s.pc = entry + 872#64) (hrun : s.status = .Running)
    (hx20 : s.readReg64 .x20 = a) (hx24 : s.readReg64 .x24 = vn.direction.signExtend 64)
    (hinv0 : StepInv s0 s) (hP : P = versionNegotiationRest A g a vn ∗ F)
    (hnext : ∀ s1 : State,
      (s1.pc = entry + 676#64 ∨ s1.pc = entry + 884#64) →
      s1.status = .Running → s1.sp = s.sp → s1.trace = s.trace →
      s1.readReg64 .x8 = s.readReg64 .x8 →
      s1.readReg64 .x9 = BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.direction) →
      s1.readReg64 .x19 = s.readReg64 .x19 → s1.readReg64 .x20 = a →
      s1.readReg64 .x21 = s.readReg64 .x21 → s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x23 = vn.minVersion.signExtend 64 →
      s1.readReg64 .x24 = vn.direction.signExtend 64 → s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x27 = s.readReg64 .x27 → s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .fp = s.readReg64 .fp → StepInv s0 s1 →
      SepWPp (spqrProgAtExt b ext) ret s1 (versionNegotiationRest A g a vn ∗ F) Q Qp) :
    SepWPp (spqrProgAtExt b ext) ret s P Q Qp := by
  etv_fetches b (Rust.withPanics ext) hfn 640 676
  etv_fetches b (Rust.withPanics ext) hfn 872 884
  examples_hide_fetches; subst hP; dsimp only [versionNegotiationRest]
  have hw24 : s.readReg32 .x24 = vn.direction := by simp only [State.readReg32, hx24, sext64_truncate32]
  by_cases hdir : vn.direction = 0#32
  · have hdir_eq : i32VarintFieldEncodedLen vn.direction = 0 := by simp [i32VarintFieldEncodedLen, hdir]
    have hbeq_d : (vn.direction == 0#32) = true := beq_iff_eq.mpr hdir
    have hbne_d : (vn.direction != 0#32) = false := by simp [hdir]
    rcases hpc with hpc | hpc <;>
      (apply SepWPp.of_sepWP_cs (mid := entry + 884#64); wp_steps;
       apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv;
       exact hnext _ (Or.inr (by simp only [arm64_norm, *]))
         (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
         (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hdir_eq, *])
         (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
         (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
         (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
         (by simp only [arm64_norm, *]) (hinv0.trans hinv))
  · have hbeq_d : (vn.direction == 0#32) = false := beq_eq_false_iff_ne.mpr hdir
    have hbne_d : (vn.direction != 0#32) = true := bne_iff_ne.mpr hdir
    have hstep_d := bv_i32VarintField_nonzero hdir
    rcases hpc with hpc | hpc <;>
      (apply SepWPp.of_sepWP_cs (mid := entry + 676#64); wp_steps;
       apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv;
       exact hnext _ (Or.inl (by simp only [arm64_norm, *]))
         (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
         (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
         (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
         (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
         (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
         (by simp only [arm64_norm, *]) (hinv0.trans hinv))

/-- Step `+676/+884 .. +708/+892` (`0x6d2b4/0x6d384 .. 0x6d2d4/0x6d38c`): computes
`x10 = BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.minVersion)`. -/
theorem step_encodeToVec_vn_minVer_len (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry)
    (a : BitVec 64) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 676#64 ∨ s.pc = entry + 884#64) (hrun : s.status = .Running)
    (hx20 : s.readReg64 .x20 = a) (hx23 : s.readReg64 .x23 = vn.minVersion.signExtend 64)
    (hinv0 : StepInv s0 s) (hP : P = versionNegotiationRest A g a vn ∗ F)
    (hnext : ∀ s1 : State,
      (s1.pc = entry + 708#64 ∨ s1.pc = entry + 892#64) →
      s1.status = .Running → s1.sp = s.sp → s1.trace = s.trace →
      s1.readReg64 .x8 = s.readReg64 .x8 → s1.readReg64 .x9 = s.readReg64 .x9 →
      s1.readReg64 .x10 = BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.minVersion) →
      s1.readReg64 .x19 = s.readReg64 .x19 → s1.readReg64 .x20 = a →
      s1.readReg64 .x21 = s.readReg64 .x21 → s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x23 = vn.minVersion.signExtend 64 →
      s1.readReg64 .x24 = s.readReg64 .x24 → s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x27 = s.readReg64 .x27 → s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .fp = s.readReg64 .fp → StepInv s0 s1 →
      SepWPp (spqrProgAtExt b ext) ret s1 (versionNegotiationRest A g a vn ∗ F) Q Qp) :
    SepWPp (spqrProgAtExt b ext) ret s P Q Qp := by
  etv_fetches b (Rust.withPanics ext) hfn 676 708
  etv_fetches b (Rust.withPanics ext) hfn 884 892
  examples_hide_fetches; subst hP; dsimp only [versionNegotiationRest]
  have hw23 : s.readReg32 .x23 = vn.minVersion := by simp only [State.readReg32, hx23, sext64_truncate32]
  by_cases hmv : vn.minVersion = 0#32
  · have hmv_eq : i32VarintFieldEncodedLen vn.minVersion = 0 := by simp [i32VarintFieldEncodedLen, hmv]
    have hbeq_m : (vn.minVersion == 0#32) = true := beq_iff_eq.mpr hmv
    have hbne_m : (vn.minVersion != 0#32) = false := by simp [hmv]
    rcases hpc with hpc | hpc <;>
      (apply SepWPp.of_sepWP_cs (mid := entry + 892#64); wp_steps;
       apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv;
       exact hnext _ (Or.inr (by simp only [arm64_norm, *]))
         (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
         (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hmv_eq, *])
         (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
         (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
         (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
         (by simp only [arm64_norm, *]) (hinv0.trans hinv))
  · have hbeq_m : (vn.minVersion == 0#32) = false := beq_eq_false_iff_ne.mpr hmv
    have hbne_m : (vn.minVersion != 0#32) = true := bne_iff_ne.mpr hmv
    have hstep_m := bv_i32VarintField_nonzero hmv
    rcases hpc with hpc | hpc <;>
      (apply SepWPp.of_sepWP_cs (mid := entry + 708#64); wp_steps;
       apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv;
       exact hnext _ (Or.inl (by simp only [arm64_norm, *]))
         (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
         (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
         (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
         (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
         (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
         (by simp only [arm64_norm, *]) (hinv0.trans hinv))

theorem bv_versionNegLen_none_combine (vn : VersionNegotiationPB) (hcp : vn.chainParams = none) :
    (BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.direction) +
      BitVec.ofNat 64 (bytesFieldEncodedLen vn.authKey)) +
      (BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.minVersion) + 0#64) =
      BitVec.ofNat 64 (versionNegotiationPBEncodedLen vn) := by
  unfold versionNegotiationPBEncodedLen; rw [hcp]; dsimp only [optChainParamsPBFieldEncodedLen]
  simp only [← BitVec.ofNat_add, BitVec.add_zero]; congr 1; omega

theorem bv_versionNegLen_some_combine (vn : VersionNegotiationPB) :
    (BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.direction) +
      BitVec.ofNat 64 (bytesFieldEncodedLen vn.authKey)) +
      (BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.minVersion) +
        BitVec.ofNat 64 (optChainParamsPBFieldEncodedLen vn.chainParams)) =
      BitVec.ofNat 64 (versionNegotiationPBEncodedLen vn) := by
  unfold versionNegotiationPBEncodedLen; simp only [← BitVec.ofNat_add]; congr 1; omega

/-- Step `+708/+892 .. +920/+964` (`0x6d2d4/0x6d38c .. 0x6d3a8/0x6d3d4`): computes
`x0 = BitVec.ofNat 64 (versionNegotiationPBEncodedLen vn)`, sets `x1 = sp - 120#64` and
`x26 = (optChainParamsTag vn.chainParams).zeroExtend 64`, and steps `bl 0x4d710` to
`entry + 18446744073709422336#64` with
`lr = if vn.chainParams.isSome then entry + 968#64 else entry + 924#64`. -/
theorem step_encodeToVec_vn_chainParams_len (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry)
    (a sp : BitVec 64) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 708#64 ∨ s.pc = entry + 892#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (bytesFieldEncodedLen vn.authKey))
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.direction))
    (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.minVersion))
    (hx20 : s.readReg64 .x20 = a) (hinv0 : StepInv s0 s)
    (hP : P = versionNegotiationRest A g a vn ∗ F)
    (hnext : ∀ s1 : State,
      s1.pc = entry + 18446744073709422336#64 →
      s1.status = .Running → s1.sp = sp - 144#64 → s1.trace = s.trace →
      s1.readReg64 .x0 = BitVec.ofNat 64 (versionNegotiationPBEncodedLen vn) →
      s1.readReg64 .x1 = sp - 120#64 →
      s1.readReg64 .lr = (if vn.chainParams.isSome then entry + 968#64 else entry + 924#64) →
      s1.readReg64 .x19 = s.readReg64 .x19 → s1.readReg64 .x20 = a →
      s1.readReg64 .x21 = s.readReg64 .x21 → s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x23 = s.readReg64 .x23 → s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = (optChainParamsTag vn.chainParams).zeroExtend 64 →
      s1.readReg64 .x27 = s.readReg64 .x27 → s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .fp = s.readReg64 .fp → StepInv s0 s1 →
      SepWPp (spqrProgAtExt b ext) ret s1 (versionNegotiationRest A g a vn ∗ F) Q Qp) :
    SepWPp (spqrProgAtExt b ext) ret s P Q Qp := by
  etv_fetches b (Rust.withPanics ext) hfn 708 792
  etv_fetches b (Rust.withPanics ext) hfn 892 924
  etv_fetches b (Rust.withPanics ext) hfn 932 968
  examples_hide_fetches; subst hP; dsimp only [versionNegotiationRest]
  cases hcp : vn.chainParams with
  | none =>
    dsimp only [optChainParamsPBAt, optChainParamsTag, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    have hcomb := bv_versionNegLen_none_combine vn hcp
    rcases hpc with hpc | hpc <;>
      (apply SepWPp.of_sepWP_cs (mid := entry + 18446744073709422336#64); wp_steps;
       apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv;
       refine SepWPp.weaken_pre
         (by dsimp only [versionNegotiationRest]; rw [hcp]; dsimp only [optChainParamsPBAt]
             simp only [BitVec.add_assoc, BitVec.reduceAdd]; exact Entails.of_eq (by ac_rfl))
         (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
           (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
           (by rw [← hcomb]; simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
           (by rw [hcp]; simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, arm64_norm, *])
           (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
           (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
           (by simp only [arm64_norm, *]) (by rw [hcp]; simp only [optChainParamsTag, arm64_norm, *])
           (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
           (hinv0.trans hinv)))
  | some cp =>
    simp only [optChainParamsPBAt, chainParamsPBAt, BitVec.add_assoc, BitVec.reduceAdd]
    suffices h720 : ∀ s_mid : State,
        s_mid.pc = entry + 720#64 → s_mid.status = .Running → s_mid.sp = sp - 144#64 → s_mid.trace = s.trace →
        s_mid.readReg64 .x8 = BitVec.ofNat 64 (bytesFieldEncodedLen vn.authKey) →
        s_mid.readReg64 .x9 = BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.direction) →
        s_mid.readReg64 .x10 = BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.minVersion) →
        s_mid.readReg64 .x19 = s.readReg64 .x19 → s_mid.readReg64 .x20 = a →
        s_mid.readReg64 .x21 = s.readReg64 .x21 → s_mid.readReg64 .x22 = s.readReg64 .x22 →
        s_mid.readReg64 .x23 = s.readReg64 .x23 → s_mid.readReg64 .x24 = s.readReg64 .x24 →
        s_mid.readReg64 .x25 = s.readReg64 .x25 → s_mid.readReg64 .x26 = 1#64 →
        s_mid.readReg64 .x27 = s.readReg64 .x27 → s_mid.readReg64 .x28 = s.readReg64 .x28 →
        s_mid.readReg64 .fp = s.readReg64 .fp → StepInv s0 s_mid →
        SepWPp (spqrProgAtExt b ext) ret s_mid
          (((a + 8#64) ↦₆₄ g.authKey.ptr) ∗
           ((a + 16#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
           EncodedLen.vecU8Buf A g.authKey.cap g.authKey.ptr vn.authKey ∗
           ((a + 24#64) ↦₃₂ 1#32) ∗ ((a + 28#64) ↦₃₂ cp.maxJump) ∗ ((a + 32#64) ↦₃₂ cp.maxOooKeys) ∗
           ((a + 36#64) ↦₃₂ vn.direction) ∗ ((a + 40#64) ↦₃₂ vn.minVersion) ∗
           memRegion (a + 44#64) 4 ∗ F) Q Qp by
      rcases hpc with hpc | hpc <;>
        (apply SepWPp.of_sepWP_cs (mid := entry + 720#64); wp_steps;
         apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv;
         refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
           (h720 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
             (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
             (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
             (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
             (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
             (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
             (by simp only [arm64_norm, *]) (hinv0.trans hinv)))
    intro s_mid hpc_m hrun_m hsp_m htr_m hx8_m hx9_m hx10_m hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hinv_m
    have hcomb := bv_versionNegLen_some_combine vn
    by_cases hmj : cp.maxJump = 0#32 <;> by_cases hmo : cp.maxOooKeys = 0#32
    · have hmj_eq : u32VarintFieldEncodedLen cp.maxJump = 0 := by simp [u32VarintFieldEncodedLen, hmj]
      have hmo_eq : u32VarintFieldEncodedLen cp.maxOooKeys = 0 := by simp [u32VarintFieldEncodedLen, hmo]
      have hbeq_mj : (cp.maxJump == 0#32) = true := beq_iff_eq.mpr hmj
      have hbne_mj : (cp.maxJump != 0#32) = false := by simp [hmj]
      have hbeq_mo : (cp.maxOooKeys == 0#32) = true := beq_iff_eq.mpr hmo
      have hbne_mo : (cp.maxOooKeys != 0#32) = false := by simp [hmo]
      apply SepWPp.of_sepWP_cs (mid := entry + 18446744073709422336#64); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
      refine SepWPp.weaken_pre
        (by dsimp only [versionNegotiationRest]; rw [hcp]
            simp only [optChainParamsPBAt, chainParamsPBAt, BitVec.add_assoc, BitVec.reduceAdd]
            exact Entails.of_eq (by ac_rfl))
        (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by rw [← hcomb, hcp, ← bv_optChainParams_some_combine]; simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by rw [hcp]; simp only [Option.isSome_some, ↓reduceIte, arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by rw [hcp]; simp only [optChainParamsTag, arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hinv_m.trans hinv))
    · have hmj_eq : u32VarintFieldEncodedLen cp.maxJump = 0 := by simp [u32VarintFieldEncodedLen, hmj]
      have hbeq_mj : (cp.maxJump == 0#32) = true := beq_iff_eq.mpr hmj
      have hbne_mj : (cp.maxJump != 0#32) = false := by simp [hmj]
      have hbeq_mo : (cp.maxOooKeys == 0#32) = false := beq_eq_false_iff_ne.mpr hmo
      have hbne_mo : (cp.maxOooKeys != 0#32) = true := bne_iff_ne.mpr hmo
      have hstep_mo := EncodedLen.bv_u32VarintField_nonzero hmo
      apply SepWPp.of_sepWP_cs (mid := entry + 18446744073709422336#64); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
      refine SepWPp.weaken_pre
        (by dsimp only [versionNegotiationRest]; rw [hcp]
            simp only [optChainParamsPBAt, chainParamsPBAt, BitVec.add_assoc, BitVec.reduceAdd]
            exact Entails.of_eq (by ac_rfl))
        (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by rw [← hcomb, hcp, ← bv_optChainParams_some_combine]; simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by rw [hcp]; simp only [Option.isSome_some, ↓reduceIte, arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by rw [hcp]; simp only [optChainParamsTag, arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hinv_m.trans hinv))
    · have hmo_eq : u32VarintFieldEncodedLen cp.maxOooKeys = 0 := by simp [u32VarintFieldEncodedLen, hmo]
      have hbeq_mj : (cp.maxJump == 0#32) = false := beq_eq_false_iff_ne.mpr hmj
      have hbne_mj : (cp.maxJump != 0#32) = true := bne_iff_ne.mpr hmj
      have hstep_mj := bv_chainParams_maxJump_nonzero hmj
      have hbeq_mo : (cp.maxOooKeys == 0#32) = true := beq_iff_eq.mpr hmo
      have hbne_mo : (cp.maxOooKeys != 0#32) = false := by simp [hmo]
      apply SepWPp.of_sepWP_cs (mid := entry + 18446744073709422336#64); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
      refine SepWPp.weaken_pre
        (by dsimp only [versionNegotiationRest]; rw [hcp]
            simp only [optChainParamsPBAt, chainParamsPBAt, BitVec.add_assoc, BitVec.reduceAdd]
            exact Entails.of_eq (by ac_rfl))
        (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by rw [← hcomb, hcp, ← bv_optChainParams_some_combine]; simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by rw [hcp]; simp only [Option.isSome_some, ↓reduceIte, arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by rw [hcp]; simp only [optChainParamsTag, arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hinv_m.trans hinv))
    · have hbeq_mj : (cp.maxJump == 0#32) = false := beq_eq_false_iff_ne.mpr hmj
      have hbne_mj : (cp.maxJump != 0#32) = true := bne_iff_ne.mpr hmj
      have hstep_mj := bv_chainParams_maxJump_nonzero hmj
      have hbeq_mo : (cp.maxOooKeys == 0#32) = false := beq_eq_false_iff_ne.mpr hmo
      have hbne_mo : (cp.maxOooKeys != 0#32) = true := bne_iff_ne.mpr hmo
      have hstep_mo := EncodedLen.bv_u32VarintField_nonzero hmo
      apply SepWPp.of_sepWP_cs (mid := entry + 18446744073709422336#64); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
      refine SepWPp.weaken_pre
        (by dsimp only [versionNegotiationRest]; rw [hcp]
            simp only [optChainParamsPBAt, chainParamsPBAt, BitVec.add_assoc, BitVec.reduceAdd]
            exact Entails.of_eq (by ac_rfl))
        (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by rw [← hcomb, hcp, ← bv_optChainParams_some_combine]; simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by rw [hcp]; simp only [Option.isSome_some, ↓reduceIte, arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by rw [hcp]; simp only [optChainParamsTag, arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hinv_m.trans hinv))

/-- Step `+924/+968 .. +972/+1088` (`0x6d3ac/0x6d3d8 .. 0x6d3dc/0x6d450`): branches on `x25`
(`vn.authKey.length`) to either `+972` (nonempty) or `+1088` (empty). -/
theorem step_encodeToVec_vn_branch_authKey (b : BitVec 64)
    (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry)
    (vn : VersionNegotiationPB) (hlen : vn.authKey.length < 2 ^ 64)
    {s0 s : State} {ret : BitVec 64} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = if vn.chainParams.isSome then entry + 968#64 else entry + 924#64)
    (hrun : s.status = .Running) (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 vn.authKey.length)
    (hinv0 : StepInv s0 s)
    (hnext : ∀ s1 : State,
      s1.pc = (if vn.authKey.isEmpty then entry + 1088#64 else entry + 972#64) →
      s1.status = .Running → s1.sp = s.sp → s1.trace = s.trace →
      s1.readReg64 .x19 = s.readReg64 .x19 → s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x21 = s.readReg64 .x21 → s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x23 = s.readReg64 .x23 → s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = s.readReg64 .x25 → s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 → s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .fp = s.readReg64 .fp → StepInv s0 s1 →
      SepWPp (spqrProgAtExt b ext) ret s1 P Q Qp) :
    SepWPp (spqrProgAtExt b ext) ret s P Q Qp := by
  etv_fetches b (Rust.withPanics ext) hfn 924 932
  etv_fetches b (Rust.withPanics ext) hfn 968 972
  examples_hide_fetches
  obtain ⟨hbeqz, hbnez⟩ := EncodedLen.ofNat_length_beq_zero_of_lt hlen
  cases hcp : vn.chainParams.isSome <;> rw [hcp] at hpc <;>
    simp only [Bool.false_eq_true, ↓reduceIte] at hpc <;>
    cases hemp : vn.authKey.isEmpty <;>
    simp only [hemp, Bool.not_false, Bool.not_true, ↓reduceIte] at hbeqz hbnez ⊢ <;>
    (apply SepWPp.of_sepWP_cs (mid := if vn.authKey.isEmpty then entry + 1088#64 else entry + 972#64);
     rw [hemp]; simp only [Bool.false_eq_true, ↓reduceIte]; wp_steps;
     apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv;
     exact hnext _
       (by rw [hemp]; simp only [Bool.false_eq_true, ↓reduceIte, arm64_norm, *])
       (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
       (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
       (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
       (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
       (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv))

/-- Step `+972/+1088 .. +1088` (`0x6d3dc/0x6d450 .. 0x6d450`): encodes `vn.authKey`
(`Proto.encodeBytesField 1#32 vn.authKey`). -/
theorem step_encodeToVec_vn_encode_authKey {resStack : Nat}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry)
    {s0 s : State}
    (hvarint : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709422336#64)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hmemcpy : subroutine_ok (spqrProgAtExt b ext)
      (entry + bv% (ls_off% "memcpy" - ls_off% "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec"))
      etvMemcpyRegionSpec)
    (a sp cap ptr v1 v2 : BitVec 64) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB)
    (bs : List (BitVec 8))
    (hfit : bs.length + (Proto.encodeBytesField 1#32 vn.authKey).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (if vn.authKey.isEmpty then entry + 1088#64 else entry + 972#64))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64)
    (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = a)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 vn.authKey.length)
    (hx26 : s.readReg64 .x26 = (optChainParamsTag vn.chainParams).zeroExtend 64)
    (hinv0 : StepInv s0 s)
    (hP : P = (versionNegotiationRest A g a vn ∗
      vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
      ((sp - 136#64) ↦₆₄ v1) ∗ ((sp - 128#64) ↦₆₄ v2)) ∗ F)
    (hnext : ∀ (sm : State) (w1 w2 : BitVec 64),
      sm.pc = entry + 1088#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x22 = s.readReg64 .x22 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x24 = s.readReg64 .x24 →
      sm.readReg64 .x26 = (optChainParamsTag vn.chainParams).zeroExtend 64 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrProgAtExt b ext) ret sm
        ((versionNegotiationRest A g a vn ∗
          vecU8At A (sp - 120#64) cap ptr (bs ++ Proto.encodeBytesField 1#32 vn.authKey) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
          ((sp - 136#64) ↦₆₄ w1) ∗ ((sp - 128#64) ↦₆₄ w2)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  subst hP
  cases hemp : vn.authKey.isEmpty
  · rw [hemp] at hpc; simp only [Bool.false_eq_true, ↓reduceIte] at hpc
    have hsp_align : (sp - 144#64) &&& 15#64 = 0#64 := sp_sub_144_aligned halign
    have h112 : (sp - 120#64) + 8#64 = sp - 112#64 := by bv_omega
    have h104 : (sp - 120#64) + 16#64 = sp - 104#64 := by bv_omega
    have h132 : (sp - 136#64) + 4#64 = sp - 132#64 := by bv_omega
    have hpos_ak : 0 < vn.authKey.length := List.length_pos_of_ne_nil (List.isEmpty_eq_false_iff.mp hemp)
    have hne_ak : vn.authKey ≠ [] := List.isEmpty_eq_false_iff.mp hemp
    have henc_eq : Proto.encodeBytesField 1#32 vn.authKey =
        [0x0a#8] ++ Proto.encodeVarint (BitVec.ofNat 64 vn.authKey.length) ++ vn.authKey := by
      rw [encodeBytesField_1_eq, hemp]; simp only [Bool.false_eq_true, ↓reduceIte]
    have hfit_all :
        bs.length + 1 + (Proto.encodeVarint (BitVec.ofNat 64 vn.authKey.length)).length +
          vn.authKey.length ≤ cap.toNat := by
      rw [henc_eq] at hfit; simp only [List.length_append, List.length_singleton] at hfit; omega
    have hlt_tag : bs.length < cap.toNat := by omega
    refine sepWPp_extract_vecU8At_bounds (v := sp - 120#64) (cap := cap) (ptr := ptr) (bs := bs)
      (F := versionNegotiationRest A g a vn ∗ A.pool ∗
        stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
        ((sp - 136#64) ↦₆₄ v1) ∗ ((sp - 128#64) ↦₆₄ v2) ∗ F) (by ac_rfl) fun _ hcap hptr => ?_
    refine sepWPp_extract_pure
      (vn.authKey.length ≤ g.authKey.cap.toNat ∧ g.authKey.cap.toNat < 2 ^ 63)
      (fun R' hm => by
        dsimp only [versionNegotiationRest] at hm
        have hm' : s.mem ⊨ EncodedLen.vecU8Buf A g.authKey.cap g.authKey.ptr vn.authKey ∗
            (((a + 8#64) ↦₆₄ g.authKey.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
             optChainParamsPBAt (a + 24#64) vn.chainParams ∗
             ((a + 36#64) ↦₃₂ vn.direction) ∗ ((a + 40#64) ↦₃₂ vn.minVersion) ∗
             memRegion (a + 44#64) 4 ∗ vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗
             stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
             ((sp - 136#64) ↦₆₄ v1) ∗ ((sp - 128#64) ↦₆₄ v2) ∗ F ∗ R') := by
          convert hm using 1; ac_rfl
        exact EncodedLen.vecU8Buf_bounds hm')
      fun ⟨hak_le, hak_cap⟩ => ?_
    etv_fetches b (Rust.withPanics ext) hfn 972 1088
    examples_hide_fetches
    have hcmp_tag := cap_beq_len_false_of_lt hlt_tag hcap
    refine sepWPp_split_pointsTo64 (sp - 136#64) v1
      (vecU8At A (sp - 120#64) cap ptr bs ∗ versionNegotiationRest A g a vn ∗ A.pool ∗
        stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ ((sp - 128#64) ↦₆₄ v2) ∗ F)
      (by ac_rfl) fun v1_lo v1_hi => ?_
    rw [h132, vecU8At_expose_one A (sp - 120#64) cap ptr bs hlt_tag hcap hptr, h112, h104]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun b0 => ?_
    dsimp only [versionNegotiationRest]
    apply SepWPp.of_sepWP_cs (mid := entry + 18446744073709422336#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
    have hpack_tag := vecU8At_pack_one A (sp - 120#64) cap ptr bs 0x0a#8 hlt_tag hcap hptr
    rw [h112, h104] at hpack_tag
    refine step_etv_encode_varint_call b A ext hvarint
      (BitVec.ofNat 64 vn.authKey.length) (sp - 120#64) cap ptr sp (entry + 1032#64) (bs ++ [0x0a#8])
      (by simp only [List.length_append, List.length_singleton]; omega)
      (F := versionNegotiationRest A g a vn ∗ ((sp - 136#64) ↦₃₂ v1_lo) ∗
        ((sp - 132#64) ↦₃₂ optChainParamsTag vn.chainParams) ∗
        ((sp - 128#64) ↦₆₄ s.readReg64 .x27) ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
      (by rw [← hpack_tag]; dsimp only [versionNegotiationRest]; ac_rfl) ?_
    intro s1 hpcs1 hruns1 hsps1 htrs1 hcss1 hinv_s1
    rcases hcss1 with ⟨hs1_19, hs1_20, hs1_21, hs1_22, hs1_23, hs1_24, hs1_25, hs1_26, hs1_27, hs1_28, hs1_fp, _⟩
    simp only [arm64_norm, hx20, hx25] at hs1_19 hs1_20 hs1_21 hs1_22 hs1_23 hs1_24 hs1_25 hs1_26 hs1_27 hs1_28 hs1_fp
    let bs1 := (bs ++ [0x0a#8]) ++ Proto.encodeVarint (BitVec.ofNat 64 vn.authKey.length)
    have hfit_mc : bs1.length + vn.authKey.length ≤ cap.toNat := by
      dsimp only [bs1]; simp only [List.length_append, List.length_singleton]; omega
    have hcmp_mc := elem_len_ult_spare_false_of_le hfit_mc hcap
    rw [vecU8At_expose_slice A (sp - 120#64) cap ptr bs1 vn.authKey.length hfit_mc hcap hptr hpos_ak, h112, h104]
    dsimp only [versionNegotiationRest]
    rw [vecU8Buf_eq_of_nonempty A g.authKey.cap g.authKey.ptr vn.authKey hemp hak_le]
    apply SepWPp.of_sepWP_cs (mid := entry + bv% (ls_off% "memcpy" - ls_off% "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec")); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
    have hlen_ak_toNat : (BitVec.ofNat 64 vn.authKey.length).toNat = vn.authKey.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    refine step_etv_memcpy_call b ext hmemcpy
      (ptr + BitVec.ofNat 64 bs1.length) g.authKey.ptr sp (entry + 1072#64) vn.authKey
      (F := ((sp - 120#64) ↦₆₄ cap) ∗ ((sp - 112#64) ↦₆₄ ptr) ∗
        ((sp - 104#64) ↦₆₄ BitVec.ofNat 64 bs1.length) ∗
        A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs1) ∗
        memRegion (ptr + BitVec.ofNat 64 bs1.length + BitVec.ofNat 64 vn.authKey.length)
          (cap.toNat - bs1.length - vn.authKey.length) ∗
        A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
        ((a + 8#64) ↦₆₄ g.authKey.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
        (⌜vn.authKey.length ≤ g.authKey.cap.toNat ∧ g.authKey.cap.toNat < 2 ^ 63 ∧ g.authKey.ptr ≠ 0⌝ ∗
          A.live g.authKey.ptr g.authKey.cap.toNat 1 ∗
          memRegion (g.authKey.ptr + BitVec.ofNat 64 vn.authKey.length)
            (g.authKey.cap.toNat - vn.authKey.length)) ∗
        optChainParamsPBAt (a + 24#64) vn.chainParams ∗
        ((a + 36#64) ↦₃₂ vn.direction) ∗ ((a + 40#64) ↦₃₂ vn.minVersion) ∗
        memRegion (a + 44#64) 4 ∗
        ((sp - 136#64) ↦₃₂ v1_lo) ∗ ((sp - 132#64) ↦₃₂ optChainParamsTag vn.chainParams) ∗
        ((sp - 128#64) ↦₆₄ s.readReg64 .x27) ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, hlen_ak_toNat, *]) (hinv_s1.trans hinv2) (by ac_rfl) ?_
    intro s2 hpcs2 hruns2 hsps2 htrs2 hcss2 hinv_s2
    rcases hcss2 with ⟨hs2_19, hs2_20, hs2_21, hs2_22, hs2_23, hs2_24, hs2_25, hs2_26, hs2_27, hs2_28, hs2_fp, _⟩
    simp only [arm64_norm, hs1_19, hs1_20, hs1_21, hs1_22, hs1_23, hs1_24, hs1_25, hs1_26, hs1_28, hs1_fp]
      at hs2_19 hs2_20 hs2_21 hs2_22 hs2_23 hs2_24 hs2_25 hs2_26 hs2_27 hs2_28 hs2_fp
    apply SepWPp.of_sepWP_cs (mid := entry + 1088#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
    have hpack_mc := vecU8At_pack_slice A (sp - 120#64) cap ptr bs1 vn.authKey hfit_mc hcap hptr hne_ak
    have hbs_eq : bs1 ++ vn.authKey = bs ++ Proto.encodeBytesField 1#32 vn.authKey := by
      dsimp only [bs1]; rw [henc_eq]; simp only [List.append_assoc]
    rw [h112, h104, hbs_eq] at hpack_mc
    refine sepWPp_merge_pointsTo32 (sp - 136#64) v1_lo (optChainParamsTag vn.chainParams)
      (versionNegotiationRest A g a vn ∗
        vecU8At A (sp - 120#64) cap ptr (bs ++ Proto.encodeBytesField 1#32 vn.authKey) ∗
        A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
        ((sp - 128#64) ↦₆₄ s.readReg64 .x27) ∗ F)
      (by rw [h132, ← hpack_mc]; dsimp only [versionNegotiationRest]
          rw [vecU8Buf_eq_of_nonempty A g.authKey.cap g.authKey.ptr vn.authKey hemp hak_le]; ac_rfl)
      fun w1 => ?_
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext _ w1 (s.readReg64 .x27)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_s2.trans hinv3))
  · rw [hemp] at hpc; simp only [↓reduceIte] at hpc
    have henc_nil : Proto.encodeBytesField 1#32 vn.authKey = [] := by
      rw [encodeBytesField_1_eq, hemp]; simp only [↓reduceIte]
    refine SepWPp.weaken_pre
      (by rw [henc_nil, List.append_nil]; exact Entails.of_eq (by ac_rfl))
      (hnext s v1 v2 hpc hrun hsp htr rfl hx20 rfl rfl rfl rfl hx26 rfl rfl rfl hinv0)

/-- Step `+1088 .. +1140` (`0x6d450 .. 0x6d484`): encodes `vn.direction`
(`Proto.encodeInt32Field 2#32 vn.direction`). -/
theorem step_encodeToVec_vn_encode_dir {resStack : Nat}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry)
    {s0 s : State}
    (hvarint : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709422336#64)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (sp cap ptr : BitVec 64) (vn : VersionNegotiationPB) (bs : List (BitVec 8))
    (hfit : bs.length + (Proto.encodeInt32Field 2#32 vn.direction).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 1088#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hx24 : s.readReg64 .x24 = vn.direction.signExtend 64) (hinv0 : StepInv s0 s)
    (hP : P = (vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 1140#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x22 = s.readReg64 .x22 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x26 = s.readReg64 .x26 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrProgAtExt b ext) ret sm
        ((vecU8At A (sp - 120#64) cap ptr (bs ++ Proto.encodeInt32Field 2#32 vn.direction) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  etv_fetches b (Rust.withPanics ext) hfn 1088 1140
  examples_hide_fetches; subst hP
  have hsp_align : (sp - 144#64) &&& 15#64 = 0#64 := sp_sub_144_aligned halign
  have h112 : (sp - 120#64) + 8#64 = sp - 112#64 := by bv_omega
  have h104 : (sp - 120#64) + 16#64 = sp - 104#64 := by bv_omega
  have hw24 : s.readReg32 .x24 = vn.direction := by simp only [State.readReg32, hx24, sext64_truncate32]
  by_cases hdir : vn.direction = 0#32
  · have hbeq_d : (vn.direction == 0#32) = true := beq_iff_eq.mpr hdir
    have hbne_d : (vn.direction != 0#32) = false := by simp [hdir]
    have henc_nil : Proto.encodeInt32Field 2#32 vn.direction = [] := by
      rw [encodeInt32Field_2_eq, hbeq_d]; simp only [↓reduceIte]
    apply SepWPp.of_sepWP_cs (mid := entry + 1140#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    refine SepWPp.weaken_pre
      (by rw [henc_nil, List.append_nil]; exact Entails.of_eq (by ac_rfl))
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (hinv0.trans hinv))
  · have hbeq_d : (vn.direction == 0#32) = false := beq_eq_false_iff_ne.mpr hdir
    have hbne_d : (vn.direction != 0#32) = true := bne_iff_ne.mpr hdir
    have henc_eq : Proto.encodeInt32Field 2#32 vn.direction =
        [0x10#8] ++ Proto.encodeVarint (vn.direction.signExtend 64) := by
      rw [encodeInt32Field_2_eq, hbeq_d]; simp only [Bool.false_eq_true, ↓reduceIte]
    have hvpos := encodeVarint_length_pos (vn.direction.signExtend 64)
    have hfit' : bs.length + 1 + (Proto.encodeVarint (vn.direction.signExtend 64)).length ≤ cap.toNat := by
      rw [henc_eq] at hfit; simp only [List.length_append, List.length_singleton] at hfit; omega
    have hlt : bs.length < cap.toNat := by omega
    refine sepWPp_extract_vecU8At_bounds (v := sp - 120#64) (cap := cap) (ptr := ptr) (bs := bs)
      (F := A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F) (by ac_rfl)
      fun _ hcap hptr => ?_
    have hcmp := cap_beq_len_false_of_lt hlt hcap
    rw [vecU8At_expose_one A (sp - 120#64) cap ptr bs hlt hcap hptr, h112, h104]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun b0 => ?_
    apply SepWPp.of_sepWP_cs (mid := entry + 18446744073709422336#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
    have hpack := vecU8At_pack_one A (sp - 120#64) cap ptr bs 0x10#8 hlt hcap hptr
    rw [h112, h104] at hpack
    refine step_etv_encode_varint_call b A ext hvarint
      (vn.direction.signExtend 64) (sp - 120#64) cap ptr sp (entry + 1140#64) (bs ++ [0x10#8])
      (by simp only [List.length_append, List.length_singleton]; omega) (F := F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
      (by rw [← hpack]) ?_
    intro sm hpcm hrunm hspm htrm hcsm hinv_m
    rcases hcsm with ⟨hm19, hm20, hm21, hm22, hm23, _, _, hm26, hm27, hm28, hmfp, _⟩
    simp only [arm64_norm] at hm19 hm20 hm21 hm22 hm23 hm26 hm27 hm28 hmfp
    refine SepWPp.weaken_pre
      (by rw [henc_eq, ← List.append_assoc]; exact Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm htrm hm19 hm20 hm21 hm22 hm23 hm26 hm27 hm28 hmfp hinv_m)

/-- Step `+1140 .. +1192` (`0x6d484 .. 0x6d4b8`): encodes `vn.minVersion`
(`Proto.encodeInt32Field 3#32 vn.minVersion`). -/
theorem step_encodeToVec_vn_encode_minVer {resStack : Nat}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry)
    {s0 s : State}
    (hvarint : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709422336#64)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (sp cap ptr : BitVec 64) (vn : VersionNegotiationPB) (bs : List (BitVec 8))
    (hfit : bs.length + (Proto.encodeInt32Field 3#32 vn.minVersion).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 1140#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hx23 : s.readReg64 .x23 = vn.minVersion.signExtend 64) (hinv0 : StepInv s0 s)
    (hP : P = (vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 1192#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x22 = s.readReg64 .x22 →
      sm.readReg64 .x26 = s.readReg64 .x26 → sm.readReg64 .x27 = s.readReg64 .x27 →
      sm.readReg64 .x28 = s.readReg64 .x28 → sm.readReg64 .fp = s.readReg64 .fp →
      StepInv s0 sm →
      SepWPp (spqrProgAtExt b ext) ret sm
        ((vecU8At A (sp - 120#64) cap ptr (bs ++ Proto.encodeInt32Field 3#32 vn.minVersion) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  etv_fetches b (Rust.withPanics ext) hfn 1140 1192
  examples_hide_fetches; subst hP
  have hsp_align : (sp - 144#64) &&& 15#64 = 0#64 := sp_sub_144_aligned halign
  have h112 : (sp - 120#64) + 8#64 = sp - 112#64 := by bv_omega
  have h104 : (sp - 120#64) + 16#64 = sp - 104#64 := by bv_omega
  have hw23 : s.readReg32 .x23 = vn.minVersion := by simp only [State.readReg32, hx23, sext64_truncate32]
  by_cases hmv : vn.minVersion = 0#32
  · have hbeq_m : (vn.minVersion == 0#32) = true := beq_iff_eq.mpr hmv
    have hbne_m : (vn.minVersion != 0#32) = false := by simp [hmv]
    have henc_nil : Proto.encodeInt32Field 3#32 vn.minVersion = [] := by
      rw [encodeInt32Field_3_eq, hbeq_m]; simp only [↓reduceIte]
    apply SepWPp.of_sepWP_cs (mid := entry + 1192#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    refine SepWPp.weaken_pre
      (by rw [henc_nil, List.append_nil]; exact Entails.of_eq (by ac_rfl))
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv))
  · have hbeq_m : (vn.minVersion == 0#32) = false := beq_eq_false_iff_ne.mpr hmv
    have hbne_m : (vn.minVersion != 0#32) = true := bne_iff_ne.mpr hmv
    have henc_eq : Proto.encodeInt32Field 3#32 vn.minVersion =
        [0x18#8] ++ Proto.encodeVarint (vn.minVersion.signExtend 64) := by
      rw [encodeInt32Field_3_eq, hbeq_m]; simp only [Bool.false_eq_true, ↓reduceIte]
    have hvpos := encodeVarint_length_pos (vn.minVersion.signExtend 64)
    have hfit' : bs.length + 1 + (Proto.encodeVarint (vn.minVersion.signExtend 64)).length ≤ cap.toNat := by
      rw [henc_eq] at hfit; simp only [List.length_append, List.length_singleton] at hfit; omega
    have hlt : bs.length < cap.toNat := by omega
    refine sepWPp_extract_vecU8At_bounds (v := sp - 120#64) (cap := cap) (ptr := ptr) (bs := bs)
      (F := A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F) (by ac_rfl)
      fun _ hcap hptr => ?_
    have hcmp := cap_beq_len_false_of_lt hlt hcap
    rw [vecU8At_expose_one A (sp - 120#64) cap ptr bs hlt hcap hptr, h112, h104]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun b0 => ?_
    apply SepWPp.of_sepWP_cs (mid := entry + 18446744073709422336#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
    have hpack := vecU8At_pack_one A (sp - 120#64) cap ptr bs 0x18#8 hlt hcap hptr
    rw [h112, h104] at hpack
    refine step_etv_encode_varint_call b A ext hvarint
      (vn.minVersion.signExtend 64) (sp - 120#64) cap ptr sp (entry + 1192#64) (bs ++ [0x18#8])
      (by simp only [List.length_append, List.length_singleton]; omega) (F := F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
      (by rw [← hpack]) ?_
    intro sm hpcm hrunm hspm htrm hcsm hinv_m
    rcases hcsm with ⟨hm19, hm20, hm21, hm22, _, _, _, hm26, hm27, hm28, hmfp, _⟩
    simp only [arm64_norm] at hm19 hm20 hm21 hm22 hm26 hm27 hm28 hmfp
    refine SepWPp.weaken_pre
      (by rw [henc_eq, ← List.append_assoc]; exact Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm htrm hm19 hm20 hm21 hm22 hm26 hm27 hm28 hmfp hinv_m)

/-- Step `+1192 .. +1212` (`0x6d4b8 .. 0x6d4cc`): encodes `vn.chainParams`
(`Proto.encodeOptMessage ChainParamsPB.encodeRaw 4#32 vn.chainParams`). -/
theorem step_encodeToVec_vn_encode_chainParams {resStack : Nat}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry)
    {s0 s : State}
    (hcp_call : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709441376#64)
      (withStepInv s0 (encodeChainParamsExactSpecOf resStack A)))
    (a sp cap ptr : BitVec 64) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB)
    (bs : List (BitVec 8))
    (hfit : bs.length + (Proto.encodeOptMessage ChainParamsPB.encodeRaw 4#32 vn.chainParams).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 1192#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = a)
    (hx26 : s.readReg64 .x26 = (optChainParamsTag vn.chainParams).zeroExtend 64)
    (hinv0 : StepInv s0 s)
    (hP : P = (versionNegotiationRest A g a vn ∗
      vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 1212#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x22 = s.readReg64 .x22 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrProgAtExt b ext) ret sm
        ((versionNegotiationRest A g a vn ∗
          vecU8At A (sp - 120#64) cap ptr
            (bs ++ Proto.encodeOptMessage ChainParamsPB.encodeRaw 4#32 vn.chainParams) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  etv_fetches b (Rust.withPanics ext) hfn 1192 1212
  examples_hide_fetches; subst hP; dsimp only [versionNegotiationRest]
  cases hcp : vn.chainParams with
  | none =>
    rw [hcp] at hx26
    dsimp only [optChainParamsTag, optChainParamsPBAt, Proto.encodeOptMessage] at hx26 ⊢
    apply SepWPp.of_sepWP_cs (mid := entry + 1212#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    refine SepWPp.weaken_pre
      (by dsimp only [versionNegotiationRest]; rw [hcp]; dsimp only [optChainParamsPBAt, Proto.encodeOptMessage]
          rw [List.append_nil]; exact Entails.of_eq (by ac_rfl))
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (hinv0.trans hinv))
  | some cp =>
    rw [hcp] at hx26 hfit
    dsimp only [optChainParamsTag, Proto.encodeOptMessage] at hx26 hfit
    simp only [optChainParamsPBAt, chainParamsPBAt, BitVec.add_assoc, BitVec.reduceAdd]
    apply SepWPp.of_sepWP_cs (mid := entry + 18446744073709441376#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
    refine step_etv_encode_chainParams_call b A ext hcp_call
      4#32 cp (sp - 120#64) cap ptr sp (entry + 1212#64) bs
      (by decide) (by decide) hfit
      (F := ((a + 8#64) ↦₆₄ g.authKey.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
        EncodedLen.vecU8Buf A g.authKey.cap g.authKey.ptr vn.authKey ∗
        ((a + 24#64) ↦₃₂ 1#32) ∗ ((a + 28#64) ↦₃₂ cp.maxJump) ∗ ((a + 32#64) ↦₃₂ cp.maxOooKeys) ∗
        ((a + 36#64) ↦₃₂ vn.direction) ∗ ((a + 40#64) ↦₃₂ vn.minVersion) ∗
        memRegion (a + 44#64) 4 ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1) (by ac_rfl) ?_
    intro sm hpcm hrunm hspm htrm hcsm hinv_m
    rcases hcsm with ⟨hm19, hm20, hm21, hm22, _, _, _, _, hm27, hm28, hmfp, _⟩
    simp only [arm64_norm, hx20] at hm19 hm20 hm21 hm22 hm27 hm28 hmfp
    refine SepWPp.weaken_pre
      (by dsimp only [versionNegotiationRest]; rw [hcp]
          simp only [optChainParamsPBAt, chainParamsPBAt, Proto.encodeOptMessage,
            BitVec.add_assoc, BitVec.reduceAdd]
          exact Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm htrm hm19 hm20 hm21 hm22 hm27 hm28 hmfp hinv_m)

/-! ## 3. Full Phase 2b Theorem: `step_encodeToVec_versionNeg` (`+580/+1212 .. +1212`) -/

/-- Step `+580/+1212 .. +1212` (`0x6d254/0x6d4cc .. 0x6d4cc`): encodes `st.versionNegotiation`
into `vecU8At A (sp - 120#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr
  (Proto.encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 st.versionNegotiation)`. -/
theorem step_encodeToVec_versionNeg {resStack : Nat}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry)
    {s0 s : State}
    (hvarint : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709422336#64)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hmemcpy : subroutine_ok (spqrProgAtExt b ext)
      (entry + bv% (ls_off% "memcpy" - ls_off% "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec"))
      etvMemcpyRegionSpec)
    (hcp_call : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709441376#64)
      (withStepInv s0 (encodeChainParamsExactSpecOf resStack A)))
    (sret a sp ptr v0 v1 v2 : BitVec 64) (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63) (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (if st.versionNegotiation.isSome then entry + 580#64 else entry + 1212#64))
    (hrun : s.status = .Running) (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hx0 : st.versionNegotiation.isSome → s.readReg64 .x0 = ptr)
    (hx19 : s.readReg64 .x19 = optChainCap g.chain st.chain)
    (hx20 : s.readReg64 .x20 = a) (hx21 : s.readReg64 .x21 = a + 128#64)
    (hx22 : s.readReg64 .x22 = a + 48#64) (hx27 : s.readReg64 .x27 = sret)
    (hx28 : s.readReg64 .x28 = optPqRatchetInnerCap g.inner st.inner)
    (hfp : s.readReg64 .fp = sp - 96#64) (hinv0 : StepInv s0 s)
    (hP : P = (pqRatchetStatePBPinnedAt A g a st ∗
      vecU8At A (sp - 120#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr [] ∗
      A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
      ((sp - 144#64) ↦₆₄ v0) ∗ ((sp - 136#64) ↦₆₄ v1) ∗ ((sp - 128#64) ↦₆₄ v2) ∗
      encodeToVecSavedRegs sp s0) ∗ F)
    (hnext : ∀ (sm : State) (w1 w2 : BitVec 64),
      sm.pc = entry + 1212#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = optChainCap g.chain st.chain → sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = a + 128#64 → sm.readReg64 .x22 = a + 48#64 →
      sm.readReg64 .x27 = sret → sm.readReg64 .x28 = optPqRatchetInnerCap g.inner st.inner →
      sm.readReg64 .fp = sp - 96#64 → StepInv s0 sm →
      SepWPp (spqrProgAtExt b ext) ret sm
        ((pqRatchetStatePBPinnedAt A g a st ∗
          vecU8At A (sp - 120#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr
            (Proto.encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 st.versionNegotiation) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
          ((sp - 144#64) ↦₆₄ v0) ∗ ((sp - 136#64) ↦₆₄ w1) ∗ ((sp - 128#64) ↦₆₄ w2) ∗
          encodeToVecSavedRegs sp s0) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  subst hP
  cases hvn : st.versionNegotiation with
  | none =>
    rw [hvn] at hpc; simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hpc
    refine SepWPp.weaken_pre (by rw [hvn]; exact Entails.refl _)
      (hnext s v1 v2 hpc hrun hsp htr hx19 hx20 hx21 hx22 hx27 hx28 hfp hinv0)
  | some vn =>
    rw [hvn] at hpc hx0; simp only [Option.isSome_some, ↓reduceIte] at hpc hx0
    have hx0' := hx0 trivial
    let cap := BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)
    have hcap_toNat : cap.toNat = pqRatchetStatePBEncodedLen st := by
      dsimp only [cap]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hvn_len_le :
        (Proto.encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 (some vn)).length ≤ cap.toNat := by
      rw [hcap_toNat, ← hvn]; exact optVersionNegotiationPB_encode_len_le st
    rw [encodeOptMessage_versionNeg_some vn] at hvn_len_le
    simp only [List.length_append, List.length_singleton] at hvn_len_le
    have hpos : 0 < cap.toNat := by
      have := encodeVarint_length_pos (BitVec.ofNat 64 (versionNegotiationPBEncodedLen vn)); omega
    have hak_lt : vn.authKey.length < 2 ^ 64 := vn_authKey_len_lt_of_state hvn hlen
    let F_rest : SepProp :=
      (a ↦₆₄ g.vn.authKey.cap) ∗ optChainPBPinnedAt A g.chain (a + 48#64) st.chain ∗
        optPqRatchetInnerPBPinnedAt A g.inner (a + 128#64) st.inner ∗
        ((sp - 144#64) ↦₆₄ v0) ∗ encodeToVecSavedRegs sp s0 ∗ F
    refine step_encodeToVec_vn_push_tag b A ext hfn a sp cap ptr g.vn vn hpos halign
      (F := A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
        ((sp - 136#64) ↦₆₄ v1) ∗ ((sp - 128#64) ↦₆₄ v2) ∗ F_rest)
      hpc hrun hsp hx0' hx20 hinv0
      (by unfold pqRatchetStatePBPinnedAt
          rw [hvn, optVersionNegotiationPBPinnedAt_eq A g.vn a (some vn)]
          dsimp only [optVersionNegCap, optVersionNegRest, cap, F_rest]; ac_rfl) ?_
    intro s1 hpcs1 hruns1 hsps1 htrs1 hs1_19 hs1_20 hs1_21 hs1_22 hs1_25 hs1_27 hs1_28 hs1_fp hinv1
    refine step_encodeToVec_vn_authKey_len b A ext hfn a g.vn vn hak_lt
      (F := vecU8At A (sp - 120#64) cap ptr [0x0a#8] ∗ A.pool ∗
        stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
        ((sp - 136#64) ↦₆₄ v1) ∗ ((sp - 128#64) ↦₆₄ v2) ∗ F_rest)
      hpcs1 hruns1 hs1_20 hs1_25 hinv1 (by ac_rfl) ?_
    intro s2 hpcs2 hruns2 hsps2 htrs2 hs2_8 hs2_19 hs2_20 hs2_21 hs2_22 hs2_24 hs2_25 hs2_27 hs2_28 hs2_fp hinv2
    refine step_encodeToVec_vn_dir_len b A ext hfn a g.vn vn
      (F := vecU8At A (sp - 120#64) cap ptr [0x0a#8] ∗ A.pool ∗
        stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
        ((sp - 136#64) ↦₆₄ v1) ∗ ((sp - 128#64) ↦₆₄ v2) ∗ F_rest)
      hpcs2 hruns2 hs2_20 hs2_24 hinv2 (by ac_rfl) ?_
    intro s3 hpcs3 hruns3 hsps3 htrs3 hs3_8 hs3_9 hs3_19 hs3_20 hs3_21 hs3_22 hs3_23 hs3_24 hs3_25 hs3_27 hs3_28 hs3_fp hinv3
    refine step_encodeToVec_vn_minVer_len b A ext hfn a g.vn vn
      (F := vecU8At A (sp - 120#64) cap ptr [0x0a#8] ∗ A.pool ∗
        stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
        ((sp - 136#64) ↦₆₄ v1) ∗ ((sp - 128#64) ↦₆₄ v2) ∗ F_rest)
      hpcs3 hruns3 hs3_20 hs3_23 hinv3 (by ac_rfl) ?_
    intro s4 hpcs4 hruns4 hsps4 htrs4 hs4_8 hs4_9 hs4_10 hs4_19 hs4_20 hs4_21 hs4_22 hs4_23 hs4_24 hs4_25 hs4_27 hs4_28 hs4_fp hinv4
    have hsps4' : s4.sp = sp - 144#64 := by rw [hsps4, hsps3, hsps2, hsps1]
    have hs4_8' : s4.readReg64 .x8 = BitVec.ofNat 64 (bytesFieldEncodedLen vn.authKey) := by rw [hs4_8, hs3_8, hs2_8]
    have hs4_9' : s4.readReg64 .x9 = BitVec.ofNat 64 (i32VarintFieldEncodedLen vn.direction) := by rw [hs4_9, hs3_9]
    refine step_encodeToVec_vn_chainParams_len b A ext hfn a sp g.vn vn
      (F := vecU8At A (sp - 120#64) cap ptr [0x0a#8] ∗ A.pool ∗
        stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
        ((sp - 136#64) ↦₆₄ v1) ∗ ((sp - 128#64) ↦₆₄ v2) ∗ F_rest)
      hpcs4 hruns4 hsps4' hs4_8' hs4_9' hs4_10 hs4_20 hinv4 (by ac_rfl) ?_
    intro s5 hpcs5 hruns5 hsps5 htrs5 hs5_0 hs5_1 hs5_lr hs5_19 hs5_20 hs5_21 hs5_22 hs5_23 hs5_24 hs5_25 hs5_26 hs5_27 hs5_28 hs5_fp hinv5
    have htrs5' : s5.trace = s0.trace := by rw [htrs5, htrs4, htrs3, htrs2, htrs1, htr]
    refine step_etv_encode_varint_call b A ext hvarint
      (BitVec.ofNat 64 (versionNegotiationPBEncodedLen vn)) (sp - 120#64) cap ptr sp
      (if vn.chainParams.isSome then entry + 968#64 else entry + 924#64) [0x0a#8]
      (by simp only [List.length_singleton]; omega)
      (F := versionNegotiationRest A g.vn a vn ∗
        ((sp - 136#64) ↦₆₄ v1) ∗ ((sp - 128#64) ↦₆₄ v2) ∗ F_rest)
      hpcs5 hruns5 hsps5 halign htrs5' hs5_lr hs5_0 hs5_1 hinv5 (by ac_rfl) ?_
    intro s6 hpcs6 hruns6 hsps6 htrs6 hcsm6 hinv6
    have hs6_19 : s6.readReg64 .x19 = optChainCap g.chain st.chain := by
      rw [hcsm6.1, hs5_19, hs4_19, hs3_19, hs2_19, hs1_19, hx19]
    have hs6_20 : s6.readReg64 .x20 = a := by rw [hcsm6.2.1, hs5_20]
    have hs6_21 : s6.readReg64 .x21 = a + 128#64 := by
      rw [hcsm6.2.2.1, hs5_21, hs4_21, hs3_21, hs2_21, hs1_21, hx21]
    have hs6_22 : s6.readReg64 .x22 = a + 48#64 := by
      rw [hcsm6.2.2.2.1, hs5_22, hs4_22, hs3_22, hs2_22, hs1_22, hx22]
    have hs6_23 : s6.readReg64 .x23 = vn.minVersion.signExtend 64 := by rw [hcsm6.2.2.2.2.1, hs5_23, hs4_23]
    have hs6_24 : s6.readReg64 .x24 = vn.direction.signExtend 64 := by rw [hcsm6.2.2.2.2.2.1, hs5_24, hs4_24, hs3_24]
    have hs6_25 : s6.readReg64 .x25 = BitVec.ofNat 64 vn.authKey.length := by
      rw [hcsm6.2.2.2.2.2.2.1, hs5_25, hs4_25, hs3_25, hs2_25]
    have hs6_26 : s6.readReg64 .x26 = (optChainParamsTag vn.chainParams).zeroExtend 64 := by
      rw [hcsm6.2.2.2.2.2.2.2.1, hs5_26]
    have hs6_27 : s6.readReg64 .x27 = sret := by
      rw [hcsm6.2.2.2.2.2.2.2.2.1, hs5_27, hs4_27, hs3_27, hs2_27, hs1_27, hx27]
    have hs6_28 : s6.readReg64 .x28 = optPqRatchetInnerCap g.inner st.inner := by
      rw [hcsm6.2.2.2.2.2.2.2.2.2.1, hs5_28, hs4_28, hs3_28, hs2_28, hs1_28, hx28]
    have hs6_fp : s6.readReg64 .fp = sp - 96#64 := by
      rw [hcsm6.2.2.2.2.2.2.2.2.2.2.1, hs5_fp, hs4_fp, hs3_fp, hs2_fp, hs1_fp, hfp]
    refine step_encodeToVec_vn_branch_authKey b ext hfn vn hak_lt hpcs6 hruns6 hs6_25 hinv6 ?_
    intro s7 hpcs7 hruns7 hsps7 htrs7 hs7_19 hs7_20 hs7_21 hs7_22 hs7_23 hs7_24 hs7_25 hs7_26 hs7_27 hs7_28 hs7_fp hinv7
    rw [hsps6] at hsps7; rw [htrs6] at htrs7
    rw [hs6_19] at hs7_19; rw [hs6_20] at hs7_20; rw [hs6_21] at hs7_21; rw [hs6_22] at hs7_22
    rw [hs6_23] at hs7_23; rw [hs6_24] at hs7_24; rw [hs6_25] at hs7_25
    rw [hs6_26] at hs7_26; rw [hs6_27] at hs7_27; rw [hs6_28] at hs7_28; rw [hs6_fp] at hs7_fp
    refine step_encodeToVec_vn_encode_authKey b A ext hfn hvarint hmemcpy
      a sp cap ptr v1 v2 g.vn vn
      ([0x0a#8] ++ Proto.encodeVarint (BitVec.ofNat 64 (versionNegotiationPBEncodedLen vn)))
      (by simp only [List.length_append, List.length_singleton]; omega) halign
      (F := F_rest) hpcs7 hruns7 hsps7 htrs7 hs7_20 hs7_25 hs7_26 hinv7 (by ac_rfl) ?_
    intro s8 w1 w2 hpcs8 hruns8 hsps8 htrs8 hs8_19 hs8_20 hs8_21 hs8_22 hs8_23 hs8_24 hs8_26 hs8_27 hs8_28 hs8_fp hinv8
    rw [hs7_19] at hs8_19; rw [hs7_21] at hs8_21; rw [hs7_22] at hs8_22; rw [hs7_23] at hs8_23
    rw [hs7_24] at hs8_24; rw [hs7_27] at hs8_27; rw [hs7_28] at hs8_28; rw [hs7_fp] at hs8_fp
    refine step_encodeToVec_vn_encode_dir b A ext hfn hvarint sp cap ptr vn
      (([0x0a#8] ++ Proto.encodeVarint (BitVec.ofNat 64 (versionNegotiationPBEncodedLen vn))) ++
        Proto.encodeBytesField 1#32 vn.authKey)
      (by simp only [List.length_append, List.length_singleton]; omega) halign
      (F := versionNegotiationRest A g.vn a vn ∗ ((sp - 136#64) ↦₆₄ w1) ∗ ((sp - 128#64) ↦₆₄ w2) ∗ F_rest)
      hpcs8 hruns8 hsps8 htrs8 hs8_24 hinv8 (by ac_rfl) ?_
    intro s9 hpcs9 hruns9 hsps9 htrs9 hs9_19 hs9_20 hs9_21 hs9_22 hs9_23 hs9_26 hs9_27 hs9_28 hs9_fp hinv9
    rw [hs8_19] at hs9_19; rw [hs8_20] at hs9_20; rw [hs8_21] at hs9_21; rw [hs8_22] at hs9_22
    rw [hs8_23] at hs9_23; rw [hs8_26] at hs9_26; rw [hs8_27] at hs9_27
    rw [hs8_28] at hs9_28; rw [hs8_fp] at hs9_fp
    refine step_encodeToVec_vn_encode_minVer b A ext hfn hvarint sp cap ptr vn
      ((([0x0a#8] ++ Proto.encodeVarint (BitVec.ofNat 64 (versionNegotiationPBEncodedLen vn))) ++
        Proto.encodeBytesField 1#32 vn.authKey) ++ Proto.encodeInt32Field 2#32 vn.direction)
      (by simp only [List.length_append, List.length_singleton]; omega) halign
      (F := versionNegotiationRest A g.vn a vn ∗ ((sp - 136#64) ↦₆₄ w1) ∗ ((sp - 128#64) ↦₆₄ w2) ∗ F_rest)
      hpcs9 hruns9 hsps9 htrs9 hs9_23 hinv9 (by ac_rfl) ?_
    intro s10 hpcs10 hruns10 hsps10 htrs10 hs10_19 hs10_20 hs10_21 hs10_22 hs10_26 hs10_27 hs10_28 hs10_fp hinv10
    rw [hs9_19] at hs10_19; rw [hs9_20] at hs10_20; rw [hs9_21] at hs10_21; rw [hs9_22] at hs10_22
    rw [hs9_26] at hs10_26; rw [hs9_27] at hs10_27; rw [hs9_28] at hs10_28; rw [hs9_fp] at hs10_fp
    refine step_encodeToVec_vn_encode_chainParams b A ext hfn hcp_call a sp cap ptr g.vn vn
      (((([0x0a#8] ++ Proto.encodeVarint (BitVec.ofNat 64 (versionNegotiationPBEncodedLen vn))) ++
        Proto.encodeBytesField 1#32 vn.authKey) ++
        Proto.encodeInt32Field 2#32 vn.direction) ++ Proto.encodeInt32Field 3#32 vn.minVersion)
      (by simp only [List.length_append, List.length_singleton]; omega) halign
      (F := ((sp - 136#64) ↦₆₄ w1) ∗ ((sp - 128#64) ↦₆₄ w2) ∗ F_rest)
      hpcs10 hruns10 hsps10 htrs10 hs10_20 hs10_26 hinv10 (by ac_rfl) ?_
    intro s11 hpcs11 hruns11 hsps11 htrs11 hs11_19 hs11_20 hs11_21 hs11_22 hs11_27 hs11_28 hs11_fp hinv11
    rw [hs10_19] at hs11_19; rw [hs10_21] at hs11_21; rw [hs10_22] at hs11_22; rw [hs10_27] at hs11_27
    rw [hs10_28] at hs11_28; rw [hs10_fp] at hs11_fp
    refine SepWPp.weaken_pre ?_
      (hnext s11 w1 w2 hpcs11 hruns11 hsps11 htrs11 hs11_19 hs11_20 hs11_21 hs11_22 hs11_27 hs11_28 hs11_fp hinv11)
    unfold pqRatchetStatePBPinnedAt
    rw [hvn, optVersionNegotiationPBPinnedAt_eq A g.vn a (some vn), encodeOptMessage_versionNeg_some vn]
    dsimp only [optVersionNegCap, optVersionNegRest, cap, F_rest]
    simp only [List.append_assoc]
    exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SpqrV1.Prost.EncodeToVec

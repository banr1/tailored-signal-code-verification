/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.Proof
import all Init.Data.Nat.Bitwise.Basic
public import LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBase
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Auth.Encode
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.CalleeBridges
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.Decodes
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodedLenVn
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked2
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked3
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked3a
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParams
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Ct1Sent
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EkSentCt1Received
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EpochDirection
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesChunkedHeaderSent
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesPoly
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked59_71
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked82_93
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.V1State
import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4
import ProofLib.SepLogic.WPp

/-!
# Final Composition for `PqRatchetState::encode_to_vec` (`0x6d010`)

Discharges the remaining 7 `StepInnerStateAt1880` jump-table variant bridges via
`V1StateChunked2`, `V1StateChunked3`, and `V1StateChunked3a`, and establishes the
unconditional top-level `subroutine_ok` contracts for `PqRatchetState::encode_to_vec`.
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
  noneCap2_add_two_beq_zero noneCap2_add_two_bne_zero
  noneCap_add_two_beq_zero noneCap_add_two_bne_zero
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
  EncodedLen.ule_zero_64 EncodedLen.ult_zero_64 ule_self_64 ult_self_64

/-! ## Remaining 7 `StepInnerStateAt1880` Variant Bridges (`V1StateChunked2/3`) -/

theorem step_encodeToVec_v1_keysUnsampled_at_1880 {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry roBase : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry) {s0 : State}
    (hkuLen : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709524916#64)
      (withStepInv s0 (leafEncLen16Spec (keysUnsampledPBPinnedAt A) keysUnsampledPBEncodedLen)))
    (hvarint : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709422336#64)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hauthEnc : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709441712#64)
      (withStepInv s0 (authEncodeExactSpecOf resStack A)))
    (v : V1State.Chunked.KeysUnsampled) :
    StepInnerStateAt1880 resStack b A ext entry roBase s0 (.keysUnsampled v) := by
  intro a sp cap ptr g bs hv_len hfit halign R ret s P F Q hpc hrun hsp htr hx8 hx9 hx20 hx21 hx28 hinv0 hP hnext
  etv_fetches b (Rust.withPanics ext) hfn 1880 1896; examples_hide_fetches; subst hP
  have hx8 : s.readReg64 .x8 = 0#64 := hx8.trans (by simp [v1StateInnerCap])
  rw [encodeToVecJumpTableBytes_eq roBase]; step_etv_jump16_to entry 1896 s 0#64 hx8; intro hinv1
  have h136 : (a + 128#64) + 8#64 = a + 136#64 := by bv_omega
  dsimp only [v1StateInnerPBPinnedAt]; rw [h136]
  refine step_encodeToVec_v1_keysUnsampled hres b A ext hfn hkuLen hvarint hauthEnc
    a sp cap ptr g.a.gKeysUnsampled v bs hv_len hfit halign
    (F := ((a + 128#64) ↦₆₄ 0x8000000000000000#64) ∗ memRegion (a + 128#64 + 64#64) 160 ∗ encodeToVecJumpTableBytesAt roBase ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
    (by dsimp only [encodeToVecJumpTableBytesAt]; ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hx27m hfpm hinv_m; simp only [arm64_norm] at hx27m hfpm
  refine SepWPp.weaken_pre ?_ (hnext sm hpcm hrunm hspm htrm hx27m hfpm hinv_m)
  dsimp only [v1StateInnerPBPinnedAt]; rw [h136, encodeToVecJumpTableBytes_eq roBase]; exact Entails.of_eq (by ac_rfl)

theorem step_encodeToVec_v1_keysSampled_at_1880 {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry roBase : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry) {s0 : State}
    (hhsLen : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709535892#64)
      (withStepInv s0 (leafEncLen16Spec (headerSentPBPinnedAt A) headerSentPBEncodedLen)))
    (hpolyEncLen : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709525468#64)
      (withStepInv s0 (leafEncLen16Spec (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen)))
    (hvarint : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709422336#64)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hauthEnc : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709441712#64)
      (withStepInv s0 (authEncodeExactSpecOf resStack A)))
    (hmemcpy : subroutine_ok (spqrProgAtExt b ext) (entry + bv% (ls_off% "memcpy" - ls_off% "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec")) etvMemcpyRegionSpec)
    (hpolyEnc : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709442756#64)
      (withStepInv s0 (etvPolyEncoderExactSpecOf resStack A)))
    (v : V1State.Chunked.KeysSampled) :
    StepInnerStateAt1880 resStack b A ext entry roBase s0 (.keysSampled v) := by
  intro a sp cap ptr g bs hv_len hfit halign R ret s P F Q hpc hrun hsp htr hx8 hx9 hx20 hx21 hx28 hinv0 hP hnext
  etv_fetches b (Rust.withPanics ext) hfn 1880 1896; examples_hide_fetches; subst hP
  have hx8 : s.readReg64 .x8 = 1#64 := hx8.trans (by simp [v1StateInnerCap])
  rw [encodeToVecJumpTableBytes_eq roBase]; step_etv_jump16_to entry 2748 s 1#64 hx8; intro hinv1
  have h136 : (a + 128#64) + 8#64 = a + 136#64 := by bv_omega
  have h240 : (a + 128#64) + 112#64 = a + 240#64 := by bv_omega
  dsimp only [v1StateInnerPBPinnedAt]; rw [h136, h240]
  refine step_encodeToVec_v1_keysSampled hres b A ext hfn hhsLen hpolyEncLen hvarint hauthEnc hmemcpy hpolyEnc
    a sp cap ptr g.a.gKeysSampled v bs hv_len hfit halign
    (F := ((a + 128#64) ↦₆₄ 0x8000000000000001#64) ∗ memRegion (a + 128#64 + 168#64) 56 ∗ encodeToVecJumpTableBytesAt roBase ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
    (by dsimp only [encodeToVecJumpTableBytesAt]; ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hx27m hfpm hinv_m; simp only [arm64_norm] at hx27m hfpm
  refine SepWPp.weaken_pre ?_ (hnext sm hpcm hrunm hspm htrm hx27m hfpm hinv_m)
  dsimp only [v1StateInnerPBPinnedAt]; rw [h136, h240, encodeToVecJumpTableBytes_eq roBase]; exact Entails.of_eq (by ac_rfl)

theorem step_encodeToVec_v1_headerSent_at_1880 {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry roBase : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry) {s0 : State}
    (hhsLen : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709539168#64)
      (withStepInv s0 (leafEncLen48Spec (chunkedHeaderSentPBPinnedAt A) chunkedHeaderSentPBEncodedLen)))
    (hekSentLen : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709539708#64)
      (withStepInv s0 (leafEncLen16Spec (ekSentPBPinnedAt A) ekSentPBEncodedLen)))
    (hvarint : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709422336#64)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hauthEnc : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709441712#64)
      (withStepInv s0 (authEncodeExactSpecOf resStack A)))
    (hmemcpy : subroutine_ok (spqrProgAtExt b ext) (entry + bv% (ls_off% "memcpy" - ls_off% "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec")) etvMemcpyRegionSpec)
    (hpolyEnc : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709442756#64)
      (withStepInv s0 (etvPolyEncoderExactSpecOf resStack A)))
    (hpolyDec : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709442356#64)
      (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A)))
    (v : V1State.Chunked.HeaderSent) :
    StepInnerStateAt1880 resStack b A ext entry roBase s0 (.headerSent v) := by
  intro a sp cap ptr g bs hv_len hfit halign R ret s P F Q hpc hrun hsp htr hx8 hx9 hx20 hx21 hx28 hinv0 hP hnext
  etv_fetches b (Rust.withPanics ext) hfn 1880 1896; examples_hide_fetches; subst hP
  have hx8 : s.readReg64 .x8 = 2#64 := hx8.trans (by simp [v1StateInnerCap])
  rw [encodeToVecJumpTableBytes_eq roBase]; step_etv_jump16_to entry 2176 s 2#64 hx8; intro hinv1
  have h136 : (a + 128#64) + 8#64 = a + 136#64 := by bv_omega
  dsimp only [v1StateInnerPBPinnedAt]; rw [h136]
  refine step_encodeToVec_v1_headerSent hres b A ext hfn hhsLen hekSentLen hvarint hauthEnc hmemcpy hpolyEnc hpolyDec
    a sp cap ptr g.a.gHeaderSent v bs hv_len hfit halign
    (F := ((a + 128#64) ↦₆₄ 0x8000000000000002#64) ∗ memRegion (a + 128#64 + 184#64) 40 ∗ encodeToVecJumpTableBytesAt roBase ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
    (by dsimp only [encodeToVecJumpTableBytesAt]; ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hx27m hfpm hinv_m; simp only [arm64_norm] at hx27m hfpm
  refine SepWPp.weaken_pre ?_ (hnext sm hpcm hrunm hspm htrm hx27m hfpm hinv_m)
  dsimp only [v1StateInnerPBPinnedAt]; rw [h136, encodeToVecJumpTableBytes_eq roBase]; exact Entails.of_eq (by ac_rfl)

theorem step_encodeToVec_v1_noHeaderReceived_at_1880 {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry roBase : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry) {s0 : State}
    (hnhrLen : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709550932#64)
      (withStepInv s0 (leafEncLen16Spec (noHeaderReceivedPBPinnedAt A) noHeaderReceivedPBEncodedLen)))
    (hpolyDecLen : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709536996#64)
      (withStepInv s0 (leafEncLen16Spec (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen)))
    (hvarint : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709422336#64)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hauthEnc : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709441712#64)
      (withStepInv s0 (authEncodeExactSpecOf resStack A)))
    (hpolyDec : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709442356#64)
      (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A)))
    (v : V1State.Chunked.NoHeaderReceived) :
    StepInnerStateAt1880 resStack b A ext entry roBase s0 (.noHeaderReceived v) := by
  intro a sp cap ptr g bs hv_len hfit halign R ret s P F Q hpc hrun hsp htr hx8 hx9 hx20 hx21 hx28 hinv0 hP hnext
  etv_fetches b (Rust.withPanics ext) hfn 1880 1896; examples_hide_fetches; subst hP
  have hx8 : s.readReg64 .x8 = 5#64 := hx8.trans (by simp [v1StateInnerCap])
  rw [encodeToVecJumpTableBytes_eq roBase]; step_etv_jump16_to entry 2848 s 5#64 hx8; intro hinv1
  have h136 : (a + 128#64) + 8#64 = a + 136#64 := by bv_omega
  have h176 : (a + 128#64) + 48#64 = a + 176#64 := by bv_omega
  dsimp only [v1StateInnerPBPinnedAt]; rw [h136, h176]
  refine step_encodeToVec_v1_noHeaderReceived hres b A ext hfn hnhrLen hpolyDecLen hvarint hauthEnc hpolyDec
    a sp cap ptr g.a.gNoHeaderReceived v bs hv_len hfit halign
    (F := ((a + 128#64) ↦₆₄ 0x8000000000000005#64) ∗ memRegion (a + 128#64 + 104#64) 120 ∗ encodeToVecJumpTableBytesAt roBase ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
    (by dsimp only [encodeToVecJumpTableBytesAt]; ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hx27m hfpm hinv_m; simp only [arm64_norm] at hx27m hfpm
  refine SepWPp.weaken_pre ?_ (hnext sm hpcm hrunm hspm htrm hx27m hfpm hinv_m)
  dsimp only [v1StateInnerPBPinnedAt]; rw [h136, h176, encodeToVecJumpTableBytes_eq roBase]; exact Entails.of_eq (by ac_rfl)

theorem step_encodeToVec_v1_headerReceived_at_1880 {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry roBase : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry) {s0 : State}
    (hhrLen : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709529772#64)
      (withStepInv s0 (leafEncLen16Spec (headerReceivedPBPinnedAt A) headerReceivedPBEncodedLen)))
    (hpolyDecLen : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709536996#64)
      (withStepInv s0 (leafEncLen16Spec (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen)))
    (hvarint : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709422336#64)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hauthEnc : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709441712#64)
      (withStepInv s0 (authEncodeExactSpecOf resStack A)))
    (hmemcpy : subroutine_ok (spqrProgAtExt b ext) (entry + bv% (ls_off% "memcpy" - ls_off% "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec")) etvMemcpyRegionSpec)
    (hpolyDec : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709442356#64)
      (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A)))
    (v : V1State.Chunked.HeaderReceived) :
    StepInnerStateAt1880 resStack b A ext entry roBase s0 (.headerReceived v) := by
  intro a sp cap ptr g bs hv_len hfit halign R ret s P F Q hpc hrun hsp htr hx8 hx9 hx20 hx21 hx28 hinv0 hP hnext
  etv_fetches b (Rust.withPanics ext) hfn 1880 1896; examples_hide_fetches; subst hP
  have hx8 : s.readReg64 .x8 = 6#64 := hx8.trans (by simp [v1StateInnerCap])
  rw [encodeToVecJumpTableBytes_eq roBase]; step_etv_jump16_to entry 2908 s 6#64 hx8; intro hinv1
  have h136 : (a + 128#64) + 8#64 = a + 136#64 := by bv_omega
  have h216 : (a + 128#64) + 88#64 = a + 216#64 := by bv_omega
  dsimp only [v1StateInnerPBPinnedAt]; rw [h136, h216]
  refine step_encodeToVec_v1_headerReceived hres b A ext hfn hhrLen hpolyDecLen hvarint hauthEnc hmemcpy hpolyDec
    a sp cap ptr g.b.gHeaderReceived v bs hv_len hfit halign
    (F := ((a + 128#64) ↦₆₄ 0x8000000000000006#64) ∗ memRegion (a + 128#64 + 128#64) 96 ∗ encodeToVecJumpTableBytesAt roBase ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
    (by dsimp only [encodeToVecJumpTableBytesAt]; ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hx27m hfpm hinv_m; simp only [arm64_norm] at hx27m hfpm
  refine SepWPp.weaken_pre ?_ (hnext sm hpcm hrunm hspm htrm hx27m hfpm hinv_m)
  dsimp only [v1StateInnerPBPinnedAt]; rw [h136, h216, encodeToVecJumpTableBytes_eq roBase]; exact Entails.of_eq (by ac_rfl)

theorem step_encodeToVec_v1_ekReceivedCt1Sampled_at_1880 {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry roBase : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry) {s0 : State}
    (hct1Len : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709515116#64)
      (withStepInv s0 (leafEncLen16Spec (ct1SentEkReceivedPBPinnedAt A) ct1SentEkReceivedPBEncodedLen)))
    (hpolyEncLen : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709525468#64)
      (withStepInv s0 (leafEncLen16Spec (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen)))
    (hvarint : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709422336#64)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hauthEnc : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709441712#64)
      (withStepInv s0 (authEncodeExactSpecOf resStack A)))
    (hmemcpy : subroutine_ok (spqrProgAtExt b ext) (entry + bv% (ls_off% "memcpy" - ls_off% "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec")) etvMemcpyRegionSpec)
    (hpolyEnc : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709442756#64)
      (withStepInv s0 (etvPolyEncoderExactSpecOf resStack A)))
    (v : V1State.Chunked.EkReceivedCt1Sampled) :
    StepInnerStateAt1880 resStack b A ext entry roBase s0 (.ekReceivedCt1Sampled v) := by
  intro a sp cap ptr g bs hv_len hfit halign R ret s P F Q hpc hrun hsp htr hx8 hx9 hx20 hx21 hx28 hinv0 hP hnext
  etv_fetches b (Rust.withPanics ext) hfn 1880 1896; examples_hide_fetches; subst hP
  have hx8 : s.readReg64 .x8 = 8#64 := hx8.trans (by simp [v1StateInnerCap])
  rw [encodeToVecJumpTableBytes_eq roBase]; step_etv_jump16_to entry 3068 s 8#64 hx8; intro hinv1
  have h136 : (a + 128#64) + 8#64 = a + 136#64 := by bv_omega
  have h264 : (a + 128#64) + 136#64 = a + 264#64 := by bv_omega
  dsimp only [v1StateInnerPBPinnedAt]; rw [h136, h264]
  refine step_encodeToVec_v1_ekReceivedCt1Sampled hres b A ext hfn hct1Len hpolyEncLen hvarint hauthEnc hmemcpy hpolyEnc
    a sp cap ptr g.b.gEkReceivedCt1Sampled v bs hv_len hfit halign
    (F := ((a + 128#64) ↦₆₄ 0x8000000000000008#64) ∗ memRegion (a + 128#64 + 192#64) 32 ∗ encodeToVecJumpTableBytesAt roBase ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
    (by dsimp only [encodeToVecJumpTableBytesAt]; ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hx27m hfpm hinv_m; simp only [arm64_norm] at hx27m hfpm
  refine SepWPp.weaken_pre ?_ (hnext sm hpcm hrunm hspm htrm hx27m hfpm hinv_m)
  dsimp only [v1StateInnerPBPinnedAt]; rw [h136, h264, encodeToVecJumpTableBytes_eq roBase]; exact Entails.of_eq (by ac_rfl)

theorem step_encodeToVec_v1_ct2Sampled_at_1880 {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry roBase : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry) {s0 : State}
    (hct2Len : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709516504#64)
      (withStepInv s0 (leafEncLen16Spec (ct2SentPBPinnedAt A) ct2SentPBEncodedLen)))
    (hpolyEncLen : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709525468#64)
      (withStepInv s0 (leafEncLen16Spec (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen)))
    (hvarint : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709422336#64)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hauthEnc : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709441712#64)
      (withStepInv s0 (authEncodeExactSpecOf resStack A)))
    (hpolyEnc : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709442756#64)
      (withStepInv s0 (etvPolyEncoderExactSpecOf resStack A)))
    (v : V1State.Chunked.Ct2Sampled) :
    StepInnerStateAt1880 resStack b A ext entry roBase s0 (.ct2Sampled v) := by
  intro a sp cap ptr g bs hv_len hfit halign R ret s P F Q hpc hrun hsp htr hx8 hx9 hx20 hx21 hx28 hinv0 hP hnext
  etv_fetches b (Rust.withPanics ext) hfn 1880 1896; examples_hide_fetches; subst hP
  have hx8 : s.readReg64 .x8 = 10#64 := hx8.trans (by simp [v1StateInnerCap])
  rw [encodeToVecJumpTableBytes_eq roBase]; step_etv_jump16_to entry 3008 s 10#64 hx8; intro hinv1
  have h136 : (a + 128#64) + 8#64 = a + 136#64 := by bv_omega
  have h192 : (a + 128#64) + 64#64 = a + 192#64 := by bv_omega
  dsimp only [v1StateInnerPBPinnedAt]; rw [h136, h192]
  refine step_encodeToVec_v1_ct2Sampled hres b A ext hfn hct2Len hpolyEncLen hvarint hauthEnc hpolyEnc
    a sp cap ptr g.b.gCt2Sampled v bs hv_len hfit halign
    (F := ((a + 128#64) ↦₆₄ 0x800000000000000a#64) ∗ memRegion (a + 128#64 + 120#64) 104 ∗ encodeToVecJumpTableBytesAt roBase ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
    (by dsimp only [encodeToVecJumpTableBytesAt]; ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hx27m hfpm hinv_m; simp only [arm64_norm] at hx27m hfpm
  refine SepWPp.weaken_pre ?_ (hnext sm hpcm hrunm hspm htrm hx27m hfpm hinv_m)
  dsimp only [v1StateInnerPBPinnedAt]; rw [h136, h192, encodeToVecJumpTableBytes_eq roBase]; exact Entails.of_eq (by ac_rfl)

/-! ## Unconditional Top-Level `subroutine_ok` Theorems for `PqRatchetState::encode_to_vec` (`0x6d010`) -/

section UnconditionalTopLevel
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.SpqrV1.Alloc CryptoVerification.SpqrV1.Varint
  CryptoVerification.SpqrV1.Auth CryptoVerification.SpqrV1.Prost.MessageEncode

theorem encodeToVec_authEncode2_fnAddr_eq (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709441712#64 =
      (spqrProgAtExt b ext).fnAddr authEncode2Name := by
  have h2 := (ls_lemma% fnOff "prost::encoding::message::encode::<spqr::proto::pq_ratchet::Authenticator, alloc::vec::Vec<u8>> [local#2]")
  simp only [spqrProgAtExt, Program.fnAddr_rebase, spqrEncodeToVec_fnOff, authEncode2Name, h2]
  bv_omega

/-- Unified dispatcher for all 11 `V1State.InnerState` variants at `StepInnerStateAt1880`. -/
theorem step_encodeToVec_inner_at_1880_all {resStack : Nat}
    (hres : resStack + 320 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) (s0 : State)
    (hvarint : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709422336#64)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hauthEnc : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709441712#64)
      (withStepInv s0 (authEncodeExactSpecOf resStack A)))
    (hpolyEnc : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709442756#64)
      (withStepInv s0 (etvPolyEncoderExactSpecOf resStack A)))
    (hpolyDec : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709442356#64)
      (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A)))
    (hekEnc : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709443724#64)
      (withStepInv s0 (etvEkSentCt1ReceivedEncodeSpecOf resStack A)))
    (hct1SentEnc : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709444388#64)
      (withStepInv s0 (etvCt1SentEncodeSpecOf resStack A)))
    (hmemcpy : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + bv% (ls_off% "memcpy" - ls_off% "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec"))
      etvMemcpyRegionSpec) :
    ∀ is : V1State.InnerState,
      StepInnerStateAt1880 resStack b A ext
        ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName) (b + bv% (ls_bytes% "0000d50046009c001400ee00fd00b50025012d001601")) s0 is := by
  have hkuLen : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709524916#64)
      (withStepInv s0 (leafEncLen16Spec (keysUnsampledPBPinnedAt A) keysUnsampledPBEncodedLen)) := by
    apply etv_leafEncLen16_withStepInv
    rw [encodeToVec_keysUnsampledEncodedLen2_fnAddr_eq]
    exact keysUnsampledEncodedLen_local2_pinned_ok_ext b A ext
  have hhs16Len : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709535892#64)
      (withStepInv s0 (leafEncLen16Spec (headerSentPBPinnedAt A) headerSentPBEncodedLen)) := by
    apply etv_leafEncLen16_withStepInv
    rw [encodeToVec_headerSentEncodedLen2_fnAddr_eq]
    exact headerSentEncodedLen_local2_pinned_ok_ext b A ext
  have hhs48Len : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709539168#64)
      (withStepInv s0 (leafEncLen48Spec (chunkedHeaderSentPBPinnedAt A) chunkedHeaderSentPBEncodedLen)) := by
    apply etv_leafEncLen48_withStepInv
    rw [encodeToVec_chunkedHeaderSentEncodedLen2_fnAddr_eq]
    exact chunkedHeaderSentEncodedLen_local2_pinned_ok_ext b A ext
  have hekSentLen : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709539708#64)
      (withStepInv s0 (leafEncLen16Spec (ekSentPBPinnedAt A) ekSentPBEncodedLen)) := by
    apply etv_leafEncLen16_withStepInv
    rw [encodeToVec_ekSentEncodedLen2_fnAddr_eq]
    exact ekSentEncodedLen_local2_pinned_ok_ext b A ext
  have hekLen : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709549660#64)
      (withStepInv s0 (leafEncLen16Spec (ekSentCt1ReceivedPBPinnedAt A) ekSentCt1ReceivedPBEncodedLen)) := by
    apply etv_leafEncLen16_withStepInv
    rw [encodeToVec_ekSentCt1ReceivedEncodedLen2_fnAddr_eq]
    exact ekSentCt1ReceivedEncodedLen_local2_pinned_ok_ext b A ext
  have hct1SentLen : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709534512#64)
      (withStepInv s0 (leafEncLen16Spec (ct1SentPBPinnedAt A) ct1SentPBEncodedLen)) := by
    apply etv_leafEncLen16_withStepInv
    rw [encodeToVec_ct1SentEncodedLen2_fnAddr_eq]
    exact ct1SentEncodedLen_local2_pinned_ok_ext b A ext
  have hnhrLen : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709550932#64)
      (withStepInv s0 (leafEncLen16Spec (noHeaderReceivedPBPinnedAt A) noHeaderReceivedPBEncodedLen)) := by
    apply etv_leafEncLen16_withStepInv
    rw [encodeToVec_noHeaderReceivedEncodedLen2_fnAddr_eq]
    exact noHeaderReceivedEncodedLen_local2_pinned_ok_ext b A ext
  have hhrLen : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709529772#64)
      (withStepInv s0 (leafEncLen16Spec (headerReceivedPBPinnedAt A) headerReceivedPBEncodedLen)) := by
    apply etv_leafEncLen16_withStepInv
    rw [encodeToVec_headerReceivedEncodedLen2_fnAddr_eq]
    exact headerReceivedEncodedLen_local2_pinned_ok_ext b A ext
  have hct1SampledLen : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709534032#64)
      (withStepInv s0 (leafEncLen48Spec (chunkedCt1SampledPBPinnedAt A) chunkedCt1SampledPBEncodedLen)) := by
    apply etv_leafEncLen48_withStepInv
    rw [encodeToVec_chunkedCt1SampledEncodedLen2_fnAddr_eq]
    exact chunkedCt1SampledEncodedLen_local2_pinned_ok_ext b A ext
  have hct1EkLen : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709515116#64)
      (withStepInv s0 (leafEncLen16Spec (ct1SentEkReceivedPBPinnedAt A) ct1SentEkReceivedPBEncodedLen)) := by
    apply etv_leafEncLen16_withStepInv
    rw [encodeToVec_ct1SentEkReceivedEncodedLen2_fnAddr_eq]
    exact ct1SentEkReceivedEncodedLen_local2_pinned_ok_ext b A ext
  have hct2Len : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709516504#64)
      (withStepInv s0 (leafEncLen16Spec (ct2SentPBPinnedAt A) ct2SentPBEncodedLen)) := by
    apply etv_leafEncLen16_withStepInv
    rw [encodeToVec_ct2SentEncodedLen2_fnAddr_eq]
    exact ct2SentEncodedLen_local2_pinned_ok_ext b A ext
  have hpolyDecLen : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709536996#64)
      (withStepInv s0 (leafEncLen16Spec (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen)) := by
    apply etv_leafEncLen16_withStepInv
    rw [encodeToVec_polyDecoderEncodedLen2_fnAddr_eq]
    exact polynomialDecoderEncodedLen_local2_pinned_ok_ext b A ext
  have hpolyEncLen : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709525468#64)
      (withStepInv s0 (leafEncLen16Spec (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen)) := by
    apply etv_leafEncLen16_withStepInv
    rw [encodeToVec_polyEncoderEncodedLen2_fnAddr_eq]
    exact polynomialEncoderEncodedLen_local2_pinned_ok_ext b A ext
  intro is; cases is with
  | keysUnsampled v =>
    exact step_encodeToVec_v1_keysUnsampled_at_1880 hres b A ext rfl hkuLen hvarint hauthEnc v
  | keysSampled v =>
    exact step_encodeToVec_v1_keysSampled_at_1880 hres b A ext rfl
      hhs16Len hpolyEncLen hvarint hauthEnc hmemcpy hpolyEnc v
  | headerSent v =>
    exact step_encodeToVec_v1_headerSent_at_1880 hres b A ext rfl
      hhs48Len hekSentLen hvarint hauthEnc hmemcpy hpolyEnc hpolyDec v
  | ct1Received v =>
    exact step_encodeToVec_v1_ct1Received_at_1880 hres b A ext rfl
      hekLen hpolyEncLen hvarint hekEnc hpolyEnc v
  | ekSentCt1Received v =>
    exact step_encodeToVec_v1_ekSentCt1Received_at_1880 hres b A ext rfl
      hekLen hpolyDecLen hvarint hekEnc hpolyDec v
  | noHeaderReceived v =>
    exact step_encodeToVec_v1_noHeaderReceived_at_1880 hres b A ext rfl
      hnhrLen hpolyDecLen hvarint hauthEnc hpolyDec v
  | headerReceived v =>
    exact step_encodeToVec_v1_headerReceived_at_1880 hres b A ext rfl
      hhrLen hpolyDecLen hvarint hauthEnc hmemcpy hpolyDec v
  | ct1Sampled v =>
    exact step_encodeToVec_v1_ct1Sampled_at_1880 hres b A ext rfl
      hct1SampledLen hvarint hct1SentEnc hpolyEnc hpolyDec v
  | ekReceivedCt1Sampled v =>
    exact step_encodeToVec_v1_ekReceivedCt1Sampled_at_1880 hres b A ext rfl
      hct1EkLen hpolyEncLen hvarint hauthEnc hmemcpy hpolyEnc v
  | ct1Acknowledged v =>
    exact step_encodeToVec_v1_ct1Acknowledged_at_1880 hres b A ext rfl
      hct1SentLen hpolyDecLen hvarint hct1SentEnc hpolyDec v
  | ct2Sampled v =>
    exact step_encodeToVec_v1_ct2Sampled_at_1880 hres b A ext rfl
      hct2Len hpolyEncLen hvarint hauthEnc hpolyEnc v

/-- Top-level `subroutine_ok` for `PqRatchetState::encode_to_vec` (`0x6d010`) on
`pqRatchetStateEncodeToVecRoPinnedSpecOf doReserveStack b A`. -/
theorem pqRatchetStateEncodeToVec_ro_pinned_ok_ext
    {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (hb : b &&& 0xfff#64 = 0#64) :
    subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName)
      (pqRatchetStateEncodeToVecRoPinnedSpecOf doReserveStack b A) := by
  apply subroutine_ok_of_sepWPp; intro x R s0 hpc hrun hpre hsp
  have hvarint : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709422336#64)
      (withStepInv s0 (encodeVarintExactSpecOf doReserveStack A)) := by
    apply etv_encodeVarint_exact_of_fit (by decide)
    rw [encodeToVec_encodeVarint4_fnAddr_eq]
    exact subroutine_ok_withStepInv s0 (encode_varint4_fit_ok_ext hA)
  have hcp_call : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709441376#64)
      (withStepInv s0 (encodeChainParamsExactSpecOf doReserveStack A)) := by
    apply etv_encodeChainParams_exact_of_spec (by decide)
    rw [encodeToVec_encodeChainParams2_fnAddr_eq]
    exact subroutine_ok_withStepInv s0 (encode_chainParams_2_ok_ext hA)
  have hep_call : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709524204#64)
      (withStepInv s0 (epochEncLenStackSpecOf doReserveStack A)) := by
    rw [encodeToVec_epochEncodedLen2_fnAddr_eq]
    exact etv_epochEncodedLen_ok (by decide) b A ext s0
  have hed_call : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709442992#64)
      (withStepInv s0 (encodeEpochDirectionExactSpecOf doReserveStack A)) := by
    apply etv_encodeEpochDirection_exact_of_spec (by decide)
    rw [encodeToVec_encodeEpochDirection2_fnAddr_eq]
    exact subroutine_ok_withStepInv s0 (encode_epochDirection_2_pinned_ok_ext hA)
  have hauthEnc : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709441712#64)
      (withStepInv s0 (authEncodeExactSpecOf doReserveStack A)) := by
    apply etv_authEncode_exact_of_spec (by decide)
    rw [encodeToVec_authEncode2_fnAddr_eq]
    exact subroutine_ok_withStepInv s0 (auth_encode_2_pinned_ok_ext hA)
  have hpolyEnc : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709442756#64)
      (withStepInv s0 (etvPolyEncoderExactSpecOf doReserveStack A)) := by
    apply etv_polyEncoderEncode_exact_of_spec
    rw [encodeToVec_polyEncoderEncode2_fnAddr_eq]
    exact subroutine_ok_withStepInv s0 (encode_polyEncoder_2_exact_pinned_ok_ext hA)
  have hpolyDec : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709442356#64)
      (withStepInv s0 (etvPolyDecoderExactSpecOf doReserveStack A)) := by
    apply etv_polyDecoderEncode_exact_of_spec
    rw [encodeToVec_polyDecoderEncode2_fnAddr_eq]
    exact subroutine_ok_withStepInv s0 (encode_polyDecoder_2_exact_pinned_ok_ext hA)
  have hekEnc : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709443724#64)
      (withStepInv s0 (etvEkSentCt1ReceivedEncodeSpecOf doReserveStack A)) := by
    apply etv_ekSentCt1ReceivedEncode_of_spec
    rw [encodeToVec_ekSentCt1ReceivedEncode2_fnAddr_eq]
    exact subroutine_ok_withStepInv s0 (ek_sent_ct1_received_encode_2_pinned_ok_ext hA)
  have hct1SentEnc : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709444388#64)
      (withStepInv s0 (etvCt1SentEncodeSpecOf doReserveStack A)) := by
    apply etv_ct1SentEncode_of_spec
    rw [encodeToVec_ct1SentEncode2_fnAddr_eq]
    exact subroutine_ok_withStepInv s0 (ct1_sent_encode_2_pinned_ok_ext hA)
  obtain ⟨P, hP, hwp⟩ := pqRatchetStateEncodeToVec_gen_ok_ext (by decide)
    (hasEncodeToVecJumpTableAddr b ext hb)
    (etv_chainEncodedLen_ok b A ext s0)
    (etv_v1StateEncodedLen_ok b A ext hb s0)
    (etv_shim_ok hA rfl s0)
    (etv_rustAlloc_ok (by decide) (by decide) hA rfl s0)
    (etv_handle_alloc_error b ext rfl)
    hvarint
    (etv_memcpy_ok hA rfl)
    hcp_call hep_call hed_call
    (step_encodeToVec_inner_at_1880_all (by decide) b A ext s0
      hvarint hauthEnc hpolyEnc hpolyDec hekEnc hct1SentEnc (etv_memcpy_ok hA rfl))
    hpc hrun hpre hsp
  exact ⟨P, R, hP, sepWPp_mono_post (fun sf Q ⟨hq, hspf, hcsf⟩ => ⟨fun hm => (hq hm).2, hspf, hcsf⟩) hwp⟩

theorem pqRatchetStateEncodeToVec_ro_ok_ext
    {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (hb : b &&& 0xfff#64 = 0#64) :
    subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName)
      (pqRatchetStateEncodeToVecRoSpecOf doReserveStack b A) :=
  pqRatchetStateEncodeToVec_ro_ok_of_pinned (pqRatchetStateEncodeToVec_ro_pinned_ok_ext hA hb)

/-- Top-level `subroutine_ok` for `PqRatchetState::encode_to_vec` (`0x6d010`) on
`(pqRatchetStateEncodeToVecPinnedSpecOf doReserveStackX A).inImage img` (eliminating both `.rodata`
jump-table atoms via `Obj.Loads libsignalSessionImage img`). -/
theorem pqRatchetStateEncodeToVec_pinned_ok_ext_x
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext)
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (spqrProgAtExt img.base ext)
      ((spqrProgAtExt img.base ext).fnAddr spqrEncodeToVecName)
      ((pqRatchetStateEncodeToVecPinnedSpecOf doReserveStackX A).inImage img) := by
  have hb : img.base &&& 0xfff#64 = 0#64 := ProofLib.ObjectLoad.base_aligned_of_loads himg
  have hdoReserve := do_reserve_7_ok_ext_x (img := img) hA
  apply subroutine_ok_of_sepWPp; intro x R s0 hpc hrun hpre hsp
  rw [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hinv0, hpre⟩ := hpre
  have hro0 : img.RoDataLoaded s0.mem := (Obj.Image.frozenLoaded_iff.mp hinv0.1).2.1
  have hpre_ro1 := rodata_v1StateJumpTable_local2_intro himg hro0 hpre
  have hpre_ro2 := rodata_encodeToVecJumpTable_intro himg hro0 hpre_ro1
  have hpre_ro : s0.mem ⊨
      (pqRatchetStateEncodeToVecRoPinnedSpecOf doReserveStackX img.base A).pre x s0 ∗ R := by
    dsimp only [pqRatchetStateEncodeToVecPinnedSpecOf,
      pqRatchetStateEncodeToVecRoPinnedSpecOf] at hpre_ro2 ⊢
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre_ro2
  have hvarint : subroutine_ok (spqrProgAtExt img.base ext)
      ((spqrProgAtExt img.base ext).fnAddr spqrEncodeToVecName + 18446744073709422336#64)
      (withStepInv s0 (encodeVarintExactSpecOf doReserveStackX A)) := by
    apply etv_encodeVarint_exact_of_fit (by decide)
    rw [encodeToVec_encodeVarint4_fnAddr_eq]
    exact subroutine_ok_withStepInv_x img s0 hinv0 (encodeVarint4_fit_ok_ext_x img A ext hdoReserve)
  have hcp_call : subroutine_ok (spqrProgAtExt img.base ext)
      ((spqrProgAtExt img.base ext).fnAddr spqrEncodeToVecName + 18446744073709441376#64)
      (withStepInv s0 (encodeChainParamsExactSpecOf doReserveStackX A)) := by
    apply etv_encodeChainParams_exact_of_spec (by decide)
    rw [encodeToVec_encodeChainParams2_fnAddr_eq]
    exact subroutine_ok_withStepInv_x img s0 hinv0 (encode_chainParams_2_ok_ext_x hA)
  have hep_call : subroutine_ok (spqrProgAtExt img.base ext)
      ((spqrProgAtExt img.base ext).fnAddr spqrEncodeToVecName + 18446744073709524204#64)
      (withStepInv s0 (epochEncLenStackSpecOf doReserveStackX A)) := by
    rw [encodeToVec_epochEncodedLen2_fnAddr_eq]
    exact etv_epochEncodedLen_ok (by decide) img.base A ext s0
  have hed_call : subroutine_ok (spqrProgAtExt img.base ext)
      ((spqrProgAtExt img.base ext).fnAddr spqrEncodeToVecName + 18446744073709442992#64)
      (withStepInv s0 (encodeEpochDirectionExactSpecOf doReserveStackX A)) := by
    apply etv_encodeEpochDirection_exact_of_spec (by decide)
    rw [encodeToVec_encodeEpochDirection2_fnAddr_eq]
    exact subroutine_ok_withStepInv_x img s0 hinv0 (encode_epochDirection_2_pinned_ok_ext_x hA)
  have hauthEnc : subroutine_ok (spqrProgAtExt img.base ext)
      ((spqrProgAtExt img.base ext).fnAddr spqrEncodeToVecName + 18446744073709441712#64)
      (withStepInv s0 (authEncodeExactSpecOf doReserveStackX A)) := by
    apply etv_authEncode_exact_of_spec (by decide)
    rw [encodeToVec_authEncode2_fnAddr_eq]
    exact subroutine_ok_withStepInv_x img s0 hinv0 (auth_encode_2_pinned_ok_ext_x hA)
  have hpolyEnc : subroutine_ok (spqrProgAtExt img.base ext)
      ((spqrProgAtExt img.base ext).fnAddr spqrEncodeToVecName + 18446744073709442756#64)
      (withStepInv s0 (etvPolyEncoderExactSpecOf doReserveStackX A)) := by
    apply etv_polyEncoderEncode_exact_of_spec
    rw [encodeToVec_polyEncoderEncode2_fnAddr_eq]
    exact subroutine_ok_withStepInv_x img s0 hinv0 (encode_polyEncoder_2_exact_pinned_ok_ext_x hA)
  have hpolyDec : subroutine_ok (spqrProgAtExt img.base ext)
      ((spqrProgAtExt img.base ext).fnAddr spqrEncodeToVecName + 18446744073709442356#64)
      (withStepInv s0 (etvPolyDecoderExactSpecOf doReserveStackX A)) := by
    apply etv_polyDecoderEncode_exact_of_spec
    rw [encodeToVec_polyDecoderEncode2_fnAddr_eq]
    exact subroutine_ok_withStepInv_x img s0 hinv0 (encode_polyDecoder_2_exact_pinned_ok_ext_x hA)
  have hekEnc : subroutine_ok (spqrProgAtExt img.base ext)
      ((spqrProgAtExt img.base ext).fnAddr spqrEncodeToVecName + 18446744073709443724#64)
      (withStepInv s0 (etvEkSentCt1ReceivedEncodeSpecOf doReserveStackX A)) := by
    apply etv_ekSentCt1ReceivedEncode_of_spec
    rw [encodeToVec_ekSentCt1ReceivedEncode2_fnAddr_eq]
    exact subroutine_ok_withStepInv_x img s0 hinv0 (ek_sent_ct1_received_encode_2_pinned_ok_ext_x hA)
  have hct1SentEnc : subroutine_ok (spqrProgAtExt img.base ext)
      ((spqrProgAtExt img.base ext).fnAddr spqrEncodeToVecName + 18446744073709444388#64)
      (withStepInv s0 (etvCt1SentEncodeSpecOf doReserveStackX A)) := by
    apply etv_ct1SentEncode_of_spec
    rw [encodeToVec_ct1SentEncode2_fnAddr_eq]
    exact subroutine_ok_withStepInv_x img s0 hinv0 (ct1_sent_encode_2_pinned_ok_ext_x hA)
  obtain ⟨P, hP, hwp⟩ := pqRatchetStateEncodeToVec_gen_ok_ext (by decide)
    (hasEncodeToVecJumpTableAddr img.base ext hb)
    (etv_chainEncodedLen_ok img.base A ext s0)
    (etv_v1StateEncodedLen_ok img.base A ext hb s0)
    (etv_shim_ok hA rfl s0)
    (etv_rustAlloc_ok (by decide) (by decide) hA rfl s0)
    (etv_handle_alloc_error img.base ext rfl)
    hvarint
    (etv_memcpy_ok hA rfl)
    hcp_call hep_call hed_call
    (step_encodeToVec_inner_at_1880_all (by decide) img.base A ext s0
      hvarint hauthEnc hpolyEnc hpolyDec hekEnc hct1SentEnc (etv_memcpy_ok hA rfl))
    hpc hrun hpre_ro hsp
  refine ⟨P, R, hP, sepWPp_mono_post (fun sf Q ⟨hq, hspf, hcsf⟩ => ⟨fun hm => ?_, hspf, hcsf⟩) hwp⟩
  obtain ⟨_, hpost_ro⟩ := hq hm
  dsimp only [Spec.inImage, pqRatchetStateEncodeToVecRoPinnedSpecOf,
    pqRatchetStateEncodeToVecPinnedSpecOf] at hpost_ro ⊢
  have hpost_perm : sf.mem ⊨
      (((img.base + bv% (ls_xref% 0x62a38 0x62a3c)) ↦ᵣ v1StateJumpTableBytes) ∗
       ((img.base + bv% (ls_bytes% "0000d50046009c001400ee00fd00b50025012d001601")) ↦ᵣ encodeToVecJumpTableBytes)) ∗
      ((⌜sf.trace = s0.trace⌝ ∗
        vecU8 A x.sret (PqRatchetState.encodeRaw x.st) ∗
        pqRatchetStatePBPinnedAt A x.g x.a x.st ∗
        A.pool ∗ stackAt s0.sp (encodeToVecStackOf doReserveStackX)) ∗ R) := by
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost_ro
  exact Satisfies.of_sep_right hpost_perm

theorem pqRatchetStateEncodeToVec_ok_ext_x
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext)
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (spqrProgAtExt img.base ext)
      ((spqrProgAtExt img.base ext).fnAddr spqrEncodeToVecName)
      ((pqRatchetStateEncodeToVecSpecOf doReserveStackX A).inImage img) :=
  pqRatchetStateEncodeToVec_ok_x_of_pinned
    (pqRatchetStateEncodeToVec_pinned_ok_ext_x hA himg)

theorem pqRatchetStateEncodeToVec_pinned_okX
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext)
    (himg : Obj.Loads libsignalSessionImage img) :
    PqRatchetStateEncodeToVecPinnedOkX img A ext :=
  pqRatchetStateEncodeToVec_pinned_ok_ext_x hA himg

theorem pqRatchetStateEncodeToVec_okX
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext)
    (himg : Obj.Loads libsignalSessionImage img) :
    PqRatchetStateEncodeToVecOkX img A ext :=
  pqRatchetStateEncodeToVec_ok_ext_x hA himg

end UnconditionalTopLevel

end CryptoVerification.SpqrV1.Prost.EncodeToVec

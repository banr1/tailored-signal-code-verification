/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import all Init.Data.Nat.Bitwise.Basic
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.Proof
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Auth.Encode
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhaseExt
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.CalleeBridges
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.Decodes
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodedLenVn
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.Final
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyExactExt
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1ChainPhaseExt
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked2Ext
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked3Ext
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked3aExt
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.VersionNegPhaseExt
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParamsExt
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
# Bounded-Stack Top-Level Composition for `PqRatchetState::encode_to_vec` (`AllocContractsX`)

Combines the bounded-stack phase proofs and `AllocContractsX` callee specifications to prove
`pqRatchetStateEncodeToVec_okX_ax` and `pqRatchetStateEncodeToVec_pinned_okX_ax` under
`AllocContractsX img A ext`.
-/

@[expose] public section

set_option autoImplicit false


namespace CryptoVerification.SpqrV1.Prost.EncodeToVec.Ext

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.SpqrV1.Alloc CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
open CryptoVerification.SpqrV1.Prost.EncodeToVec
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Prost.MessageEncode

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
    (hmemcpy : subroutine_ok (spqrProgAtExt b ext)
      (entry + bv% (ls_off% "memcpy" - ls_off% "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec"))
      (withStepInv s0 (withStack etvMemcpyRegionSpec (encodeToVecCalleeStackOf resStack))))
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
  refine Ext.step_encodeToVec_v1_keysSampled hres b A ext hfn hhsLen hpolyEncLen hvarint hauthEnc hmemcpy hpolyEnc
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
    (hmemcpy : subroutine_ok (spqrProgAtExt b ext)
      (entry + bv% (ls_off% "memcpy" - ls_off% "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec"))
      (withStepInv s0 (withStack etvMemcpyRegionSpec (encodeToVecCalleeStackOf resStack))))
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
  refine Ext.step_encodeToVec_v1_headerSent hres b A ext hfn hhsLen hekSentLen hvarint hauthEnc hmemcpy hpolyEnc hpolyDec
    a sp cap ptr g.a.gHeaderSent v bs hv_len hfit halign
    (F := ((a + 128#64) ↦₆₄ 0x8000000000000002#64) ∗ memRegion (a + 128#64 + 184#64) 40 ∗ encodeToVecJumpTableBytesAt roBase ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
    (by dsimp only [encodeToVecJumpTableBytesAt]; ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hx27m hfpm hinv_m; simp only [arm64_norm] at hx27m hfpm
  refine SepWPp.weaken_pre ?_ (hnext sm hpcm hrunm hspm htrm hx27m hfpm hinv_m)
  dsimp only [v1StateInnerPBPinnedAt]; rw [h136, encodeToVecJumpTableBytes_eq roBase]; exact Entails.of_eq (by ac_rfl)

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
    (hmemcpy : subroutine_ok (spqrProgAtExt b ext)
      (entry + bv% (ls_off% "memcpy" - ls_off% "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec"))
      (withStepInv s0 (withStack etvMemcpyRegionSpec (encodeToVecCalleeStackOf resStack))))
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
  refine Ext.step_encodeToVec_v1_headerReceived hres b A ext hfn hhrLen hpolyDecLen hvarint hauthEnc hmemcpy hpolyDec
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
    (hmemcpy : subroutine_ok (spqrProgAtExt b ext)
      (entry + bv% (ls_off% "memcpy" - ls_off% "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec"))
      (withStepInv s0 (withStack etvMemcpyRegionSpec (encodeToVecCalleeStackOf resStack))))
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
  refine Ext.step_encodeToVec_v1_ekReceivedCt1Sampled hres b A ext hfn hct1Len hpolyEncLen hvarint hauthEnc hmemcpy hpolyEnc
    a sp cap ptr g.b.gEkReceivedCt1Sampled v bs hv_len hfit halign
    (F := ((a + 128#64) ↦₆₄ 0x8000000000000008#64) ∗ memRegion (a + 128#64 + 192#64) 32 ∗ encodeToVecJumpTableBytesAt roBase ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
    (by dsimp only [encodeToVecJumpTableBytesAt]; ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hx27m hfpm hinv_m; simp only [arm64_norm] at hx27m hfpm
  refine SepWPp.weaken_pre ?_ (hnext sm hpcm hrunm hspm htrm hx27m hfpm hinv_m)
  dsimp only [v1StateInnerPBPinnedAt]; rw [h136, h264, encodeToVecJumpTableBytes_eq roBase]; exact Entails.of_eq (by ac_rfl)

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
      (withStepInv s0 (withStack etvMemcpyRegionSpec (encodeToVecCalleeStackOf resStack)))) :
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
    exact CryptoVerification.SpqrV1.Prost.EncodeToVec.step_encodeToVec_v1_keysUnsampled_at_1880
      hres b A ext rfl hkuLen hvarint hauthEnc v
  | keysSampled v =>
    exact Ext.step_encodeToVec_v1_keysSampled_at_1880 hres b A ext rfl
      hhs16Len hpolyEncLen hvarint hauthEnc hmemcpy hpolyEnc v
  | headerSent v =>
    exact Ext.step_encodeToVec_v1_headerSent_at_1880 hres b A ext rfl
      hhs48Len hekSentLen hvarint hauthEnc hmemcpy hpolyEnc hpolyDec v
  | ct1Received v =>
    exact CryptoVerification.SpqrV1.Prost.EncodeToVec.step_encodeToVec_v1_ct1Received_at_1880
      hres b A ext rfl hekLen hpolyEncLen hvarint hekEnc hpolyEnc v
  | ekSentCt1Received v =>
    exact CryptoVerification.SpqrV1.Prost.EncodeToVec.step_encodeToVec_v1_ekSentCt1Received_at_1880
      hres b A ext rfl hekLen hpolyDecLen hvarint hekEnc hpolyDec v
  | noHeaderReceived v =>
    exact CryptoVerification.SpqrV1.Prost.EncodeToVec.step_encodeToVec_v1_noHeaderReceived_at_1880
      hres b A ext rfl hnhrLen hpolyDecLen hvarint hauthEnc hpolyDec v
  | headerReceived v =>
    exact Ext.step_encodeToVec_v1_headerReceived_at_1880 hres b A ext rfl
      hhrLen hpolyDecLen hvarint hauthEnc hmemcpy hpolyDec v
  | ct1Sampled v =>
    exact CryptoVerification.SpqrV1.Prost.EncodeToVec.step_encodeToVec_v1_ct1Sampled_at_1880
      hres b A ext rfl hct1SampledLen hvarint hct1SentEnc hpolyEnc hpolyDec v
  | ekReceivedCt1Sampled v =>
    exact Ext.step_encodeToVec_v1_ekReceivedCt1Sampled_at_1880 hres b A ext rfl
      hct1EkLen hpolyEncLen hvarint hauthEnc hmemcpy hpolyEnc v
  | ct1Acknowledged v =>
    exact CryptoVerification.SpqrV1.Prost.EncodeToVec.step_encodeToVec_v1_ct1Acknowledged_at_1880
      hres b A ext rfl hct1SentLen hpolyDecLen hvarint hct1SentEnc hpolyDec v
  | ct2Sampled v =>
    exact CryptoVerification.SpqrV1.Prost.EncodeToVec.step_encodeToVec_v1_ct2Sampled_at_1880
      hres b A ext rfl hct2Len hpolyEncLen hvarint hauthEnc hpolyEnc v

theorem pqRatchetStateEncodeToVec_gen_ok_ext {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    {x : PqRatchetStateEncodeToVecPinnedGhost} {R : SepProp} {s0 : State}
    (hjt : HasEncodeToVecJumpTableAddr b ext
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName) (b + bv% (ls_bytes% "0000d50046009c001400ee00fd00b50025012d001601")))
    (hChainLen : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr chainEncodedLenLocal2Name)
      (withStepInv s0 (chainEncodedLenPinnedSpec A)))
    (hV1StateLen : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr v1StateEncodedLenLocal2Name)
      (withStepInv s0 (v1StateEncodedLenRoPinnedSpec A (b + bv% (ls_xref% 0x62a38 0x62a3c)))))
    (hshim : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec"))
      (withStepInv s0 (shimStackSpecOf resStack)))
    (halloc : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec"))
      (withStepInv s0 (rustAllocStackSpecOf resStack A)))
    (hhandle : (spqrProgAtExt b ext).externAt?
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec")) = some Rust.panicked)
    (hvarint : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709422336#64)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hmemcpy : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + bv% (ls_off% "memcpy" - ls_off% "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec"))
      (withStepInv s0 (withStack etvMemcpyRegionSpec (encodeToVecCalleeStackOf resStack))))
    (hcp_call : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709441376#64)
      (withStepInv s0 (encodeChainParamsExactSpecOf resStack A)))
    (hep_call : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709524204#64)
      (withStepInv s0 (epochEncLenStackSpecOf resStack A)))
    (hed_call : subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName + 18446744073709442992#64)
      (withStepInv s0 (encodeEpochDirectionExactSpecOf resStack A)))
    (hInnerAt1880 : ∀ is : V1State.InnerState,
      StepInnerStateAt1880 resStack b A ext
        ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName) (b + bv% (ls_bytes% "0000d50046009c001400ee00fd00b50025012d001601")) s0 is)
    (hpc : s0.pc = (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (pqRatchetStateEncodeToVecRoPinnedSpecOf resStack b A).pre x s0 ∗ R)
    (hsp_align : s0.spAligned = true) :
    ∃ P, (s0.mem ⊨ P ∗ R) ∧
      SepWPp (spqrProgAtExt b ext) (s0.readReg64 .lr) s0 P
        (fun sf Q =>
          ((sf.mem ⊨ Q ∗ R) →
            StepInv s0 sf ∧
            (sf.mem ⊨ (pqRatchetStateEncodeToVecRoPinnedSpecOf resStack b A).post x s0 sf ∗ R)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ (pqRatchetStateEncodeToVecRoPinnedSpecOf resStack b A).onPanic x s0 sf ∗ R)) := by
  let entry := (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName
  have hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry := rfl
  have halign : s0.sp &&& 15#64 = 0#64 := by simpa only [State.spAligned, beq_iff_eq] using hsp_align
  have hpre_pure := hpre; dsimp only [pqRatchetStateEncodeToVecRoPinnedSpecOf] at hpre_pure
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_pure
  obtain ⟨⟨hx0, hx1, hlen_raw⟩, hpre_mem⟩ := hpre_pure
  have hlen : pqRatchetStatePBEncodedLen x.st < 2 ^ 63 := by
    rw [← pqRatchetStatePBEncodedLen_eq_proto x.st]; exact hlen_raw
  have hv1Len_call : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709530600#64)
      (withStepInv s0 (v1StateEncodedLenRoPinnedSpec A (b + bv% (ls_xref% 0x62a38 0x62a3c)))) := by
    rw [encodeToVec_v1StateEncodedLen_fnAddr_eq b ext hfn]; exact hV1StateLen
  have hpre_rewritten : s0.mem ⊨
      ((pqRatchetStatePBPinnedAt A x.g x.a x.st ∗
        ((b + bv% (ls_xref% 0x62a38 0x62a3c)) ↦ᵣ v1StateJumpTableBytes) ∗
        stackAt s0.sp (encodeToVecStackOf resStack)) ∗
       (memRegion x.sret 24 ∗ ((b + bv% (ls_bytes% "0000d50046009c001400ee00fd00b50025012d001601")) ↦ᵣ encodeToVecJumpTableBytes) ∗ A.pool)) ∗ R := by
    convert hpre_mem using 1; ac_rfl
  refine ⟨_, hpre_rewritten, ?_⟩
  refine step_encodeToVec_phase1 hres b A ext hfn hChainLen hV1StateLen
    x.sret x.a s0.sp x.g x.st hlen halign
    hpc hrun rfl hx0 hx1 rfl ?_
  intro s1 v0 v1 v2 v3 v4 v5 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx25_1 hx27_1 hx28_1 hfp1 hinv1
  refine step_encodeToVec_alloc b A ext hfn hshim halloc hhandle
    x.sret x.a s0.sp v0 v1 v2 v3 v4 v5 x.g x.st hlen halign
    (F := memRegion x.sret 24 ∗
      ((b + bv% (ls_xref% 0x62a38 0x62a3c)) ↦ᵣ v1StateJumpTableBytes) ∗
      ((b + bv% (ls_bytes% "0000d50046009c001400ee00fd00b50025012d001601")) ↦ᵣ encodeToVecJumpTableBytes))
    hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx25_1 hx27_1 hx28_1 hfp1 hinv1
    (by ac_rfl) ?_
  intro s2 ptr hpc2 hrun2 hsp2 htr2 hx0_2 hx19_2 hx20_2 hx21_2 hx22_2 hx25_2 hx27_2 hx28_2 hfp2 hinv2
  refine Ext.step_encodeToVec_versionNeg b A ext hfn hvarint hmemcpy hcp_call
    x.sret x.a s0.sp ptr v0 v1 v2 x.g x.st hlen halign
    (F := memRegion x.sret 24 ∗
      ((b + bv% (ls_xref% 0x62a38 0x62a3c)) ↦ᵣ v1StateJumpTableBytes) ∗
      ((b + bv% (ls_bytes% "0000d50046009c001400ee00fd00b50025012d001601")) ↦ᵣ encodeToVecJumpTableBytes))
    hpc2 hrun2 hsp2 htr2 hx0_2 hx19_2 hx20_2 hx21_2 hx22_2 hx27_2 hx28_2 hfp2 hinv2
    rfl ?_
  intro s3 w1 w2 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx21_3 hx22_3 hx27_3 hx28_3 hfp3 hinv3
  refine Ext.step_encodeToVec_chain hres b A ext hfn hChainLen hep_call hvarint hmemcpy hed_call hcp_call
    x.sret x.a s0.sp ptr x.g x.st hlen halign
    (F := ((s0.sp - 144#64) ↦₆₄ v0) ∗ ((s0.sp - 136#64) ↦₆₄ w1) ∗ ((s0.sp - 128#64) ↦₆₄ w2) ∗
      encodeToVecSavedRegs s0.sp s0 ∗ memRegion x.sret 24 ∗
      ((b + bv% (ls_xref% 0x62a38 0x62a3c)) ↦ᵣ v1StateJumpTableBytes) ∗
      ((b + bv% (ls_bytes% "0000d50046009c001400ee00fd00b50025012d001601")) ↦ᵣ encodeToVecJumpTableBytes))
    hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx21_3 hx22_3 hx27_3 hx28_3 hfp3 hinv3
    (by ac_rfl) ?_
  intro s4 hpc4 hrun4 hsp4 htr4 hx20_4 hx21_4 hx27_4 hx28_4 hfp4 hinv4
  refine step_encodeToVec_phase2d hres b A ext hfn hjt hv1Len_call hvarint hInnerAt1880
    x.sret x.a s0.sp ptr x.g x.st hlen halign
    (F := memRegion x.sret 24 ∗
      ((s0.sp - 144#64) ↦₆₄ v0) ∗ ((s0.sp - 136#64) ↦₆₄ w1) ∗ ((s0.sp - 128#64) ↦₆₄ w2) ∗
      encodeToVecSavedRegs s0.sp s0)
    hpc4 hrun4 hsp4 htr4 hx20_4 hx21_4 hx27_4 hx28_4 hfp4 hinv4
    (by ac_rfl) ?_
  intro s5 hpc5 hrun5 hsp5 htr5 hx27_5 hfp5 hinv5
  refine step_encodeToVec_epilogue hres b A ext hfn
    x.sret s0.sp (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen x.st)) ptr v0 w1 w2
    (PqRatchetState.encodeRaw x.st)
    (F := pqRatchetStatePBPinnedAt A x.g x.a x.st ∗
      ((b + bv% (ls_xref% 0x62a38 0x62a3c)) ↦ᵣ v1StateJumpTableBytes) ∗
      ((b + bv% (ls_bytes% "0000d50046009c001400ee00fd00b50025012d001601")) ↦ᵣ encodeToVecJumpTableBytes) ∗ A.pool)
    hpc5 hrun5 hsp5 halign htr5 hx27_5 hinv5
    (by ac_rfl) ?_
  intro sf _ _ hspf htrf hcsf hinvf
  refine ⟨fun hm => ⟨hinvf, ?_⟩, hspf, hcsf⟩
  dsimp only [pqRatchetStateEncodeToVecRoPinnedSpecOf]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htrf, ?_⟩
  convert hm using 1; ac_rfl

end CryptoVerification.SpqrV1.Prost.EncodeToVec.Ext

namespace CryptoVerification.SpqrV1.Prost.EncodeToVec

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.SpqrV1.Alloc CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Prost.MessageEncode

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr

/-- Top-level `subroutine_ok` for `PqRatchetState::encode_to_vec` on
`(pqRatchetStateEncodeToVecPinnedSpecOf doReserveStackX A).inImage img` under `AllocContractsX img A ext`. -/
theorem pqRatchetStateEncodeToVec_pinned_ok_ext_xa
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hAx : AllocContractsX img A ext)
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (spqrProgAtExt img.base ext)
      ((spqrProgAtExt img.base ext).fnAddr spqrEncodeToVecName)
      ((pqRatchetStateEncodeToVecPinnedSpecOf doReserveStackX A).inImage img) := by
  have hb : img.base &&& 0xfff#64 = 0#64 := ProofLib.ObjectLoad.base_aligned_of_loads himg
  have hdoReserve := do_reserve_7_ok_ext_xa (img := img) hAx
  have hauth := auth_encode_2_pinned_ok_ext_xa hAx
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
    exact Ext.subroutine_ok_withStepInv_x img s0 hinv0 (encodeVarint4_fit_ok_ext_x img A ext hdoReserve)
  have hcp_call : subroutine_ok (spqrProgAtExt img.base ext)
      ((spqrProgAtExt img.base ext).fnAddr spqrEncodeToVecName + 18446744073709441376#64)
      (withStepInv s0 (encodeChainParamsExactSpecOf doReserveStackX A)) := by
    apply etv_encodeChainParams_exact_of_spec (by decide)
    rw [encodeToVec_encodeChainParams2_fnAddr_eq]
    exact Ext.subroutine_ok_withStepInv_x img s0 hinv0 (encode_chainParams_2_ok_ext_xa hAx)
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
    exact Ext.subroutine_ok_withStepInv_x img s0 hinv0 (encode_epochDirection_2_pinned_ok_ext_xa hAx)
  have hauthEnc : subroutine_ok (spqrProgAtExt img.base ext)
      ((spqrProgAtExt img.base ext).fnAddr spqrEncodeToVecName + 18446744073709441712#64)
      (withStepInv s0 (authEncodeExactSpecOf doReserveStackX A)) := by
    apply etv_authEncode_exact_of_spec (by decide)
    rw [encodeToVec_authEncode2_fnAddr_eq]
    exact Ext.subroutine_ok_withStepInv_x img s0 hinv0 hauth
  have hpolyEnc : subroutine_ok (spqrProgAtExt img.base ext)
      ((spqrProgAtExt img.base ext).fnAddr spqrEncodeToVecName + 18446744073709442756#64)
      (withStepInv s0 (etvPolyEncoderExactSpecOf doReserveStackX A)) := by
    apply etv_polyEncoderEncode_exact_of_spec
    rw [encodeToVec_polyEncoderEncode2_fnAddr_eq]
    exact Ext.subroutine_ok_withStepInv_x img s0 hinv0 (encode_polyEncoder_2_exact_pinned_ok_ext_xa hAx)
  have hpolyDec : subroutine_ok (spqrProgAtExt img.base ext)
      ((spqrProgAtExt img.base ext).fnAddr spqrEncodeToVecName + 18446744073709442356#64)
      (withStepInv s0 (etvPolyDecoderExactSpecOf doReserveStackX A)) := by
    apply etv_polyDecoderEncode_exact_of_spec
    rw [encodeToVec_polyDecoderEncode2_fnAddr_eq]
    exact Ext.subroutine_ok_withStepInv_x img s0 hinv0 (encode_polyDecoder_2_exact_pinned_ok_ext_xa hAx)
  have hekEnc : subroutine_ok (spqrProgAtExt img.base ext)
      ((spqrProgAtExt img.base ext).fnAddr spqrEncodeToVecName + 18446744073709443724#64)
      (withStepInv s0 (etvEkSentCt1ReceivedEncodeSpecOf doReserveStackX A)) := by
    apply etv_ekSentCt1ReceivedEncode_of_spec
    rw [encodeToVec_ekSentCt1ReceivedEncode2_fnAddr_eq]
    exact Ext.subroutine_ok_withStepInv_x img s0 hinv0 (ek_sent_ct1_received_encode_2_pinned_ok_of_auth hAx hauth)
  have hct1SentEnc : subroutine_ok (spqrProgAtExt img.base ext)
      ((spqrProgAtExt img.base ext).fnAddr spqrEncodeToVecName + 18446744073709444388#64)
      (withStepInv s0 (etvCt1SentEncodeSpecOf doReserveStackX A)) := by
    apply etv_ct1SentEncode_of_spec
    rw [encodeToVec_ct1SentEncode2_fnAddr_eq]
    exact Ext.subroutine_ok_withStepInv_x img s0 hinv0 (ct1_sent_encode_2_pinned_ok_of_auth hAx hauth)
  have hmemcpy := Ext.etv_memcpy_ok (resStack := doReserveStackX) (by decide) (by decide) hAx rfl s0 hinv0
  obtain ⟨P, hP, hwp⟩ := Ext.pqRatchetStateEncodeToVec_gen_ok_ext (by decide)
    (hasEncodeToVecJumpTableAddr img.base ext hb)
    (etv_chainEncodedLen_ok img.base A ext s0)
    (etv_v1StateEncodedLen_ok img.base A ext hb s0)
    (Ext.etv_shim_ok (by decide) (by decide) hAx rfl s0 hinv0)
    (Ext.etv_rustAlloc_ok (by decide) (by decide) hAx rfl s0 hinv0)
    (etv_handle_alloc_error img.base ext rfl)
    hvarint hmemcpy hcp_call hep_call hed_call
    (Ext.step_encodeToVec_inner_at_1880_all (by decide) img.base A ext s0
      hvarint hauthEnc hpolyEnc hpolyDec hekEnc hct1SentEnc hmemcpy)
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

theorem pqRatchetStateEncodeToVec_ok_ext_xa
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hAx : AllocContractsX img A ext)
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (spqrProgAtExt img.base ext)
      ((spqrProgAtExt img.base ext).fnAddr spqrEncodeToVecName)
      ((pqRatchetStateEncodeToVecSpecOf doReserveStackX A).inImage img) :=
  pqRatchetStateEncodeToVec_ok_x_of_pinned
    (pqRatchetStateEncodeToVec_pinned_ok_ext_xa hAx himg)

theorem pqRatchetStateEncodeToVec_pinned_okX_ax
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hAx : AllocContractsX img A ext)
    (himg : Obj.Loads libsignalSessionImage img) :
    PqRatchetStateEncodeToVecPinnedOkX img A ext :=
  pqRatchetStateEncodeToVec_pinned_ok_ext_xa hAx himg

theorem pqRatchetStateEncodeToVec_okX_ax
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hAx : AllocContractsX img A ext)
    (himg : Obj.Loads libsignalSessionImage img) :
    PqRatchetStateEncodeToVecOkX img A ext :=
  pqRatchetStateEncodeToVec_ok_ext_xa hAx himg

end CryptoVerification.SpqrV1.Prost.EncodeToVec

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.ProofPlaced
import all Init.Data.Nat.Bitwise.Basic
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.CalleeBridgesPlaced
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked2Placed
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked3Placed
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked3aPlaced
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesChunkedHeaderSent
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesPoly
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked59_71
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked82_93
import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Relocatable `[LibsignalPlacement]` Final Composition for `PqRatchetState::encode_to_vec` (`Block 426`)

Discharges the remaining 7 `StepInnerStateAt1880Placed` jump-table variant bridges and proves
the top-level `[LibsignalPlacement]` `subroutine_ok` contracts for `PqRatchetState::encode_to_vec`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Prost.EncodeToVec

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalSpqrV1 hiding WireType DecodeErr decodeVarint encodeVarint
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
open CryptoVerification.SpqrV1.Varint

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr Obj.lookup
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

/-! ## Remaining 7 `StepInnerStateAt1880Placed` Variant Bridges (`V1StateChunked2/3Placed`) -/

theorem step_encodeToVec_v1_keysUnsampled_at_1880_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (A : RustAlloc) (H : String → Option (State → State)) {s0 : State}
    (hkuLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 400)
      (withStepInv s0 (leafEncLen16Spec (keysUnsampledPBPinnedAt A) keysUnsampledPBEncodedLen)))
    (hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hauthEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 314)
      (withStepInv s0 (authEncodeExactSpecOf resStack A)))
    (v : V1State.Chunked.KeysUnsampled) :
    StepInnerStateAt1880Placed resStack A H s0 (.keysUnsampled v) := by
  intro a sp cap ptr g bs hv_len hfit halign R ret s P F Q hpc hrun hsp htr hx8 hx9 hx20 hx21 hx28 hinv0 hP hnext
  subst hP
  have hx8 : s.readReg64 .x8 = 0#64 := hx8.trans (by simp [v1StateInnerCap])
  rw [encodeToVecJumpTableBytes_eq ((blkPl_426).ρ etvJumpTableRoSym)]
  step_etv_jump16_to_placed 1896 s 0#64 hx8; intro hinv1
  have h136 : (a + 128#64) + 8#64 = a + 136#64 := by bv_omega
  dsimp only [v1StateInnerPBPinnedAt]; rw [h136]
  refine step_encodeToVec_v1_keysUnsampled_placed hres A H hkuLen hvarint hauthEnc
    a sp cap ptr g.a.gKeysUnsampled v bs hv_len hfit halign
    (F := ((a + 128#64) ↦₆₄ 0x8000000000000000#64) ∗ memRegion (a + 128#64 + 64#64) 160 ∗
      encodeToVecJumpTableBytesAt ((blkPl_426).ρ etvJumpTableRoSym) ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
    (by dsimp only [encodeToVecJumpTableBytesAt]; ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hx27m hfpm hinv_m; simp only [arm64_norm] at hx27m hfpm
  refine SepWPp.weaken_pre ?_ (hnext sm hpcm hrunm hspm htrm hx27m hfpm hinv_m)
  dsimp only [v1StateInnerPBPinnedAt]; rw [h136, encodeToVecJumpTableBytes_eq ((blkPl_426).ρ etvJumpTableRoSym)]
  exact Entails.of_eq (by ac_rfl)

theorem step_encodeToVec_v1_keysSampled_at_1880_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (A : RustAlloc) (H : String → Option (State → State)) {s0 : State}
    (hhsLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 411)
      (withStepInv s0 (leafEncLen16Spec (headerSentPBPinnedAt A) headerSentPBEncodedLen)))
    (hpolyEncLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 401)
      (withStepInv s0 (leafEncLen16Spec (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen)))
    (hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hauthEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 314)
      (withStepInv s0 (authEncodeExactSpecOf resStack A)))
    (hmemcpy : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) ((blkPl_426).ρ "memcpy") etvMemcpyRegionSpec)
    (hpolyEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 316)
      (withStepInv s0 (etvPolyEncoderExactSpecOf resStack A)))
    (v : V1State.Chunked.KeysSampled) :
    StepInnerStateAt1880Placed resStack A H s0 (.keysSampled v) := by
  intro a sp cap ptr g bs hv_len hfit halign R ret s P F Q hpc hrun hsp htr hx8 hx9 hx20 hx21 hx28 hinv0 hP hnext
  subst hP
  have hx8 : s.readReg64 .x8 = 1#64 := hx8.trans (by simp [v1StateInnerCap])
  rw [encodeToVecJumpTableBytes_eq ((blkPl_426).ρ etvJumpTableRoSym)]
  step_etv_jump16_to_placed 2748 s 1#64 hx8; intro hinv1
  have h136 : (a + 128#64) + 8#64 = a + 136#64 := by bv_omega
  have h240 : (a + 128#64) + 112#64 = a + 240#64 := by bv_omega
  dsimp only [v1StateInnerPBPinnedAt]; rw [h136, h240]
  refine step_encodeToVec_v1_keysSampled_placed hres A H hhsLen hpolyEncLen hvarint hauthEnc hmemcpy hpolyEnc
    a sp cap ptr g.a.gKeysSampled v bs hv_len hfit halign
    (F := ((a + 128#64) ↦₆₄ 0x8000000000000001#64) ∗ memRegion (a + 128#64 + 168#64) 56 ∗
      encodeToVecJumpTableBytesAt ((blkPl_426).ρ etvJumpTableRoSym) ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
    (by dsimp only [encodeToVecJumpTableBytesAt]; ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hx27m hfpm hinv_m; simp only [arm64_norm] at hx27m hfpm
  refine SepWPp.weaken_pre ?_ (hnext sm hpcm hrunm hspm htrm hx27m hfpm hinv_m)
  dsimp only [v1StateInnerPBPinnedAt]; rw [h136, h240, encodeToVecJumpTableBytes_eq ((blkPl_426).ρ etvJumpTableRoSym)]
  exact Entails.of_eq (by ac_rfl)

theorem step_encodeToVec_v1_headerSent_at_1880_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (A : RustAlloc) (H : String → Option (State → State)) {s0 : State}
    (hhsLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 414)
      (withStepInv s0 (leafEncLen48Spec (chunkedHeaderSentPBPinnedAt A) chunkedHeaderSentPBEncodedLen)))
    (hekSentLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 415)
      (withStepInv s0 (leafEncLen16Spec (ekSentPBPinnedAt A) ekSentPBEncodedLen)))
    (hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hauthEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 314)
      (withStepInv s0 (authEncodeExactSpecOf resStack A)))
    (hmemcpy : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) ((blkPl_426).ρ "memcpy") etvMemcpyRegionSpec)
    (hpolyEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 316)
      (withStepInv s0 (etvPolyEncoderExactSpecOf resStack A)))
    (hpolyDec : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 315)
      (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A)))
    (v : V1State.Chunked.HeaderSent) :
    StepInnerStateAt1880Placed resStack A H s0 (.headerSent v) := by
  intro a sp cap ptr g bs hv_len hfit halign R ret s P F Q hpc hrun hsp htr hx8 hx9 hx20 hx21 hx28 hinv0 hP hnext
  subst hP
  have hx8 : s.readReg64 .x8 = 2#64 := hx8.trans (by simp [v1StateInnerCap])
  rw [encodeToVecJumpTableBytes_eq ((blkPl_426).ρ etvJumpTableRoSym)]
  step_etv_jump16_to_placed 2176 s 2#64 hx8; intro hinv1
  have h136 : (a + 128#64) + 8#64 = a + 136#64 := by bv_omega
  dsimp only [v1StateInnerPBPinnedAt]; rw [h136]
  refine step_encodeToVec_v1_headerSent_placed hres A H hhsLen hekSentLen hvarint hauthEnc hmemcpy hpolyEnc hpolyDec
    a sp cap ptr g.a.gHeaderSent v bs hv_len hfit halign
    (F := ((a + 128#64) ↦₆₄ 0x8000000000000002#64) ∗ memRegion (a + 128#64 + 184#64) 40 ∗
      encodeToVecJumpTableBytesAt ((blkPl_426).ρ etvJumpTableRoSym) ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
    (by dsimp only [encodeToVecJumpTableBytesAt]; ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hx27m hfpm hinv_m; simp only [arm64_norm] at hx27m hfpm
  refine SepWPp.weaken_pre ?_ (hnext sm hpcm hrunm hspm htrm hx27m hfpm hinv_m)
  dsimp only [v1StateInnerPBPinnedAt]; rw [h136, encodeToVecJumpTableBytes_eq ((blkPl_426).ρ etvJumpTableRoSym)]
  exact Entails.of_eq (by ac_rfl)

theorem step_encodeToVec_v1_noHeaderReceived_at_1880_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (A : RustAlloc) (H : String → Option (State → State)) {s0 : State}
    (hnhrLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 424)
      (withStepInv s0 (leafEncLen16Spec (noHeaderReceivedPBPinnedAt A) noHeaderReceivedPBEncodedLen)))
    (hpolyDecLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 413)
      (withStepInv s0 (leafEncLen16Spec (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen)))
    (hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hauthEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 314)
      (withStepInv s0 (authEncodeExactSpecOf resStack A)))
    (hpolyDec : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 315)
      (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A)))
    (v : V1State.Chunked.NoHeaderReceived) :
    StepInnerStateAt1880Placed resStack A H s0 (.noHeaderReceived v) := by
  intro a sp cap ptr g bs hv_len hfit halign R ret s P F Q hpc hrun hsp htr hx8 hx9 hx20 hx21 hx28 hinv0 hP hnext
  subst hP
  have hx8 : s.readReg64 .x8 = 5#64 := hx8.trans (by simp [v1StateInnerCap])
  rw [encodeToVecJumpTableBytes_eq ((blkPl_426).ρ etvJumpTableRoSym)]
  step_etv_jump16_to_placed 2848 s 5#64 hx8; intro hinv1
  have h136 : (a + 128#64) + 8#64 = a + 136#64 := by bv_omega
  have h176 : (a + 128#64) + 48#64 = a + 176#64 := by bv_omega
  dsimp only [v1StateInnerPBPinnedAt]; rw [h136, h176]
  refine step_encodeToVec_v1_noHeaderReceived_placed hres A H hnhrLen hpolyDecLen hvarint hauthEnc hpolyDec
    a sp cap ptr g.a.gNoHeaderReceived v bs hv_len hfit halign
    (F := ((a + 128#64) ↦₆₄ 0x8000000000000005#64) ∗ memRegion (a + 128#64 + 104#64) 120 ∗
      encodeToVecJumpTableBytesAt ((blkPl_426).ρ etvJumpTableRoSym) ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
    (by dsimp only [encodeToVecJumpTableBytesAt]; ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hx27m hfpm hinv_m; simp only [arm64_norm] at hx27m hfpm
  refine SepWPp.weaken_pre ?_ (hnext sm hpcm hrunm hspm htrm hx27m hfpm hinv_m)
  dsimp only [v1StateInnerPBPinnedAt]; rw [h136, h176, encodeToVecJumpTableBytes_eq ((blkPl_426).ρ etvJumpTableRoSym)]
  exact Entails.of_eq (by ac_rfl)

theorem step_encodeToVec_v1_headerReceived_at_1880_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (A : RustAlloc) (H : String → Option (State → State)) {s0 : State}
    (hhrLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 404)
      (withStepInv s0 (leafEncLen16Spec (headerReceivedPBPinnedAt A) headerReceivedPBEncodedLen)))
    (hpolyDecLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 413)
      (withStepInv s0 (leafEncLen16Spec (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen)))
    (hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hauthEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 314)
      (withStepInv s0 (authEncodeExactSpecOf resStack A)))
    (hmemcpy : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) ((blkPl_426).ρ "memcpy") etvMemcpyRegionSpec)
    (hpolyDec : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 315)
      (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A)))
    (v : V1State.Chunked.HeaderReceived) :
    StepInnerStateAt1880Placed resStack A H s0 (.headerReceived v) := by
  intro a sp cap ptr g bs hv_len hfit halign R ret s P F Q hpc hrun hsp htr hx8 hx9 hx20 hx21 hx28 hinv0 hP hnext
  subst hP
  have hx8 : s.readReg64 .x8 = 6#64 := hx8.trans (by simp [v1StateInnerCap])
  rw [encodeToVecJumpTableBytes_eq ((blkPl_426).ρ etvJumpTableRoSym)]
  step_etv_jump16_to_placed 2908 s 6#64 hx8; intro hinv1
  have h136 : (a + 128#64) + 8#64 = a + 136#64 := by bv_omega
  have h216 : (a + 128#64) + 88#64 = a + 216#64 := by bv_omega
  dsimp only [v1StateInnerPBPinnedAt]; rw [h136, h216]
  refine step_encodeToVec_v1_headerReceived_placed hres A H hhrLen hpolyDecLen hvarint hauthEnc hmemcpy hpolyDec
    a sp cap ptr g.b.gHeaderReceived v bs hv_len hfit halign
    (F := ((a + 128#64) ↦₆₄ 0x8000000000000006#64) ∗ memRegion (a + 128#64 + 128#64) 96 ∗
      encodeToVecJumpTableBytesAt ((blkPl_426).ρ etvJumpTableRoSym) ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
    (by dsimp only [encodeToVecJumpTableBytesAt]; ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hx27m hfpm hinv_m; simp only [arm64_norm] at hx27m hfpm
  refine SepWPp.weaken_pre ?_ (hnext sm hpcm hrunm hspm htrm hx27m hfpm hinv_m)
  dsimp only [v1StateInnerPBPinnedAt]; rw [h136, h216, encodeToVecJumpTableBytes_eq ((blkPl_426).ρ etvJumpTableRoSym)]
  exact Entails.of_eq (by ac_rfl)

theorem step_encodeToVec_v1_ekReceivedCt1Sampled_at_1880_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (A : RustAlloc) (H : String → Option (State → State)) {s0 : State}
    (hct1Len : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 387)
      (withStepInv s0 (leafEncLen16Spec (ct1SentEkReceivedPBPinnedAt A) ct1SentEkReceivedPBEncodedLen)))
    (hpolyEncLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 401)
      (withStepInv s0 (leafEncLen16Spec (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen)))
    (hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hauthEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 314)
      (withStepInv s0 (authEncodeExactSpecOf resStack A)))
    (hmemcpy : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) ((blkPl_426).ρ "memcpy") etvMemcpyRegionSpec)
    (hpolyEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 316)
      (withStepInv s0 (etvPolyEncoderExactSpecOf resStack A)))
    (v : V1State.Chunked.EkReceivedCt1Sampled) :
    StepInnerStateAt1880Placed resStack A H s0 (.ekReceivedCt1Sampled v) := by
  intro a sp cap ptr g bs hv_len hfit halign R ret s P F Q hpc hrun hsp htr hx8 hx9 hx20 hx21 hx28 hinv0 hP hnext
  subst hP
  have hx8 : s.readReg64 .x8 = 8#64 := hx8.trans (by simp [v1StateInnerCap])
  rw [encodeToVecJumpTableBytes_eq ((blkPl_426).ρ etvJumpTableRoSym)]
  step_etv_jump16_to_placed 3068 s 8#64 hx8; intro hinv1
  have h136 : (a + 128#64) + 8#64 = a + 136#64 := by bv_omega
  have h264 : (a + 128#64) + 136#64 = a + 264#64 := by bv_omega
  dsimp only [v1StateInnerPBPinnedAt]; rw [h136, h264]
  refine step_encodeToVec_v1_ekReceivedCt1Sampled_placed hres A H hct1Len hpolyEncLen hvarint hauthEnc hmemcpy hpolyEnc
    a sp cap ptr g.b.gEkReceivedCt1Sampled v bs hv_len hfit halign
    (F := ((a + 128#64) ↦₆₄ 0x8000000000000008#64) ∗ memRegion (a + 128#64 + 192#64) 32 ∗
      encodeToVecJumpTableBytesAt ((blkPl_426).ρ etvJumpTableRoSym) ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
    (by dsimp only [encodeToVecJumpTableBytesAt]; ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hx27m hfpm hinv_m; simp only [arm64_norm] at hx27m hfpm
  refine SepWPp.weaken_pre ?_ (hnext sm hpcm hrunm hspm htrm hx27m hfpm hinv_m)
  dsimp only [v1StateInnerPBPinnedAt]; rw [h136, h264, encodeToVecJumpTableBytes_eq ((blkPl_426).ρ etvJumpTableRoSym)]
  exact Entails.of_eq (by ac_rfl)

theorem step_encodeToVec_v1_ct2Sampled_at_1880_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (A : RustAlloc) (H : String → Option (State → State)) {s0 : State}
    (hct2Len : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 389)
      (withStepInv s0 (leafEncLen16Spec (ct2SentPBPinnedAt A) ct2SentPBEncodedLen)))
    (hpolyEncLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 401)
      (withStepInv s0 (leafEncLen16Spec (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen)))
    (hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hauthEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 314)
      (withStepInv s0 (authEncodeExactSpecOf resStack A)))
    (hpolyEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 316)
      (withStepInv s0 (etvPolyEncoderExactSpecOf resStack A)))
    (v : V1State.Chunked.Ct2Sampled) :
    StepInnerStateAt1880Placed resStack A H s0 (.ct2Sampled v) := by
  intro a sp cap ptr g bs hv_len hfit halign R ret s P F Q hpc hrun hsp htr hx8 hx9 hx20 hx21 hx28 hinv0 hP hnext
  subst hP
  have hx8 : s.readReg64 .x8 = 10#64 := hx8.trans (by simp [v1StateInnerCap])
  rw [encodeToVecJumpTableBytes_eq ((blkPl_426).ρ etvJumpTableRoSym)]
  step_etv_jump16_to_placed 3008 s 10#64 hx8; intro hinv1
  have h136 : (a + 128#64) + 8#64 = a + 136#64 := by bv_omega
  have h192 : (a + 128#64) + 64#64 = a + 192#64 := by bv_omega
  dsimp only [v1StateInnerPBPinnedAt]; rw [h136, h192]
  refine step_encodeToVec_v1_ct2Sampled_placed hres A H hct2Len hpolyEncLen hvarint hauthEnc hpolyEnc
    a sp cap ptr g.b.gCt2Sampled v bs hv_len hfit halign
    (F := ((a + 128#64) ↦₆₄ 0x800000000000000a#64) ∗ memRegion (a + 128#64 + 120#64) 104 ∗
      encodeToVecJumpTableBytesAt ((blkPl_426).ρ etvJumpTableRoSym) ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
    (by dsimp only [encodeToVecJumpTableBytesAt]; ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hx27m hfpm hinv_m; simp only [arm64_norm] at hx27m hfpm
  refine SepWPp.weaken_pre ?_ (hnext sm hpcm hrunm hspm htrm hx27m hfpm hinv_m)
  dsimp only [v1StateInnerPBPinnedAt]; rw [h136, h192, encodeToVecJumpTableBytes_eq ((blkPl_426).ρ etvJumpTableRoSym)]
  exact Entails.of_eq (by ac_rfl)

/-! ## Unified Dispatcher and Top-Level `[LibsignalPlacement]` `subroutine_ok` Theorems -/

/-- Unified dispatcher for all 11 `V1State.InnerState` variants at `StepInnerStateAt1880Placed`. -/
theorem step_encodeToVec_inner_at_1880_all_placed [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 320 < 2 ^ 64)
    (A : RustAlloc) (ext : String → Option (State → State)) (s0 : State)
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hauthEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 314)
      (withStepInv s0 (authEncodeExactSpecOf resStack A)))
    (hpolyEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 316)
      (withStepInv s0 (etvPolyEncoderExactSpecOf resStack A)))
    (hpolyDec : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 315)
      (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A)))
    (hekEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 318)
      (withStepInv s0 (etvEkSentCt1ReceivedEncodeSpecOf resStack A)))
    (hct1SentEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 319)
      (withStepInv s0 (etvCt1SentEncodeSpecOf resStack A)))
    (hmemcpy : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext))
      ((blkPl_426).ρ "memcpy")
      etvMemcpyRegionSpec) :
    ∀ is : V1State.InnerState,
      StepInnerStateAt1880Placed resStack A (Rust.withPanics ext) s0 is := by
  have hkuLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 400)
      (withStepInv s0 (leafEncLen16Spec (keysUnsampledPBPinnedAt A) keysUnsampledPBEncodedLen)) :=
    etv_subroutine_ok_placed_of_plain hcl0
      (keysUnsampledEncodedLen_local2_pinned_placed_ok_ext A ext)
  have hhs16Len : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 411)
      (withStepInv s0 (leafEncLen16Spec (headerSentPBPinnedAt A) headerSentPBEncodedLen)) :=
    etv_subroutine_ok_placed_of_plain hcl0
      (headerSentEncodedLen_local2_pinned_placed_ok_ext A ext)
  have hhs48Len : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 414)
      (withStepInv s0 (leafEncLen48Spec (chunkedHeaderSentPBPinnedAt A) chunkedHeaderSentPBEncodedLen)) :=
    etv_subroutine_ok_placed_of_lscl hcl0
      (chunkedHeaderSentEncodedLen_local2_pinned_placed_ok_ext A ext)
  have hekSentLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 415)
      (withStepInv s0 (leafEncLen16Spec (ekSentPBPinnedAt A) ekSentPBEncodedLen)) :=
    etv_subroutine_ok_placed_of_plain hcl0
      (ekSentEncodedLen_local2_pinned_placed_ok_ext A ext)
  have hekLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 421)
      (withStepInv s0 (leafEncLen16Spec (ekSentCt1ReceivedPBPinnedAt A) ekSentCt1ReceivedPBEncodedLen)) :=
    etv_subroutine_ok_placed_of_plain hcl0
      (ekSentCt1ReceivedEncodedLen_local2_pinned_placed_ok_ext A ext)
  have hct1SentLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 408)
      (withStepInv s0 (leafEncLen16Spec (ct1SentPBPinnedAt A) ct1SentPBEncodedLen)) :=
    etv_subroutine_ok_placed_of_plain hcl0
      (ct1SentEncodedLen_local2_pinned_placed_ok_ext A ext)
  have hnhrLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 424)
      (withStepInv s0 (leafEncLen16Spec (noHeaderReceivedPBPinnedAt A) noHeaderReceivedPBEncodedLen)) :=
    etv_subroutine_ok_placed_of_plain hcl0
      (noHeaderReceivedEncodedLen_local2_pinned_placed_ok_ext A ext)
  have hhrLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 404)
      (withStepInv s0 (leafEncLen16Spec (headerReceivedPBPinnedAt A) headerReceivedPBEncodedLen)) :=
    etv_subroutine_ok_placed_of_plain hcl0
      (headerReceivedEncodedLen_local2_pinned_placed_ok_ext A ext)
  have hct1SampledLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 407)
      (withStepInv s0 (leafEncLen48Spec (chunkedCt1SampledPBPinnedAt A) chunkedCt1SampledPBEncodedLen)) :=
    etv_subroutine_ok_placed_of_lscl hcl0
      (chunkedCt1SampledEncodedLen_local2_pinned_placed_ok_ext A ext)
  have hct1EkLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 387)
      (withStepInv s0 (leafEncLen16Spec (ct1SentEkReceivedPBPinnedAt A) ct1SentEkReceivedPBEncodedLen)) :=
    etv_subroutine_ok_placed_of_plain hcl0
      (ct1SentEkReceivedEncodedLen_local2_pinned_placed_ok_ext A ext)
  have hct2Len : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 389)
      (withStepInv s0 (leafEncLen16Spec (ct2SentPBPinnedAt A) ct2SentPBEncodedLen)) :=
    etv_subroutine_ok_placed_of_plain hcl0
      (ct2SentEncodedLen_local2_pinned_placed_ok_ext A ext)
  have hpolyDecLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 413)
      (withStepInv s0 (leafEncLen16Spec (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen)) :=
    etv_subroutine_ok_placed_of_plain hcl0
      (polynomialDecoderEncodedLen_local2_pinned_placed_ok_ext A ext)
  have hpolyEncLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 401)
      (withStepInv s0 (leafEncLen16Spec (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen)) :=
    etv_subroutine_ok_placed_of_plain hcl0
      (polynomialEncoderEncodedLen_local2_pinned_placed_ok_ext A ext)
  intro is; cases is with
  | keysUnsampled v =>
    exact step_encodeToVec_v1_keysUnsampled_at_1880_placed hres A (Rust.withPanics ext) hkuLen hvarint hauthEnc v
  | keysSampled v =>
    exact step_encodeToVec_v1_keysSampled_at_1880_placed hres A (Rust.withPanics ext)
      hhs16Len hpolyEncLen hvarint hauthEnc hmemcpy hpolyEnc v
  | headerSent v =>
    exact step_encodeToVec_v1_headerSent_at_1880_placed hres A (Rust.withPanics ext)
      hhs48Len hekSentLen hvarint hauthEnc hmemcpy hpolyEnc hpolyDec v
  | ct1Received v =>
    exact step_encodeToVec_v1_ct1Received_at_1880_placed hres A (Rust.withPanics ext)
      hekLen hpolyEncLen hvarint hekEnc hpolyEnc v
  | ekSentCt1Received v =>
    exact step_encodeToVec_v1_ekSentCt1Received_at_1880_placed hres A (Rust.withPanics ext)
      hekLen hpolyDecLen hvarint hekEnc hpolyDec v
  | noHeaderReceived v =>
    exact step_encodeToVec_v1_noHeaderReceived_at_1880_placed hres A (Rust.withPanics ext)
      hnhrLen hpolyDecLen hvarint hauthEnc hpolyDec v
  | headerReceived v =>
    exact step_encodeToVec_v1_headerReceived_at_1880_placed hres A (Rust.withPanics ext)
      hhrLen hpolyDecLen hvarint hauthEnc hmemcpy hpolyDec v
  | ct1Sampled v =>
    exact step_encodeToVec_v1_ct1Sampled_at_1880_placed hres A (Rust.withPanics ext)
      hct1SampledLen hvarint hct1SentEnc hpolyEnc hpolyDec v
  | ekReceivedCt1Sampled v =>
    exact step_encodeToVec_v1_ekReceivedCt1Sampled_at_1880_placed hres A (Rust.withPanics ext)
      hct1EkLen hpolyEncLen hvarint hauthEnc hmemcpy hpolyEnc v
  | ct1Acknowledged v =>
    exact step_encodeToVec_v1_ct1Acknowledged_at_1880_placed hres A (Rust.withPanics ext)
      hct1SentLen hpolyDecLen hvarint hct1SentEnc hpolyDec v
  | ct2Sampled v =>
    exact step_encodeToVec_v1_ct2Sampled_at_1880_placed hres A (Rust.withPanics ext)
      hct2Len hpolyEncLen hvarint hauthEnc hpolyEnc v

def PqRatchetStateEncodeToVecPinnedPlacedOkExt [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext))
    (blkPl_426).base
    (withLsRoLoaded lsmpl (withLsCodeLoaded lsmpl (pqRatchetStateEncodeToVecPinnedSpecOf doReserveStackX A)))

def PqRatchetStateEncodeToVecPlacedOkExt [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext))
    (blkPl_426).base
    (withLsRoLoaded lsmpl (withLsCodeLoaded lsmpl (pqRatchetStateEncodeToVecSpecOf doReserveStackX A)))

def PqRatchetStateEncodeToVecPinnedPlacedOk [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  PqRatchetStateEncodeToVecPinnedPlacedOkExt A (tripleRatchetExterns C ctl abs)

def PqRatchetStateEncodeToVecPlacedOk [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  PqRatchetStateEncodeToVecPlacedOkExt A (tripleRatchetExterns C ctl abs)

/-- Top-level `subroutine_ok` for `PqRatchetState::encode_to_vec` (`Block 426`) on
`withLsCodeLoaded lsmpl (pqRatchetStateEncodeToVecRoPinnedPlacedSpecOf doReserveStack A)`
(discharging all `encoded_len` callees, `encode_varint4`, and allocator/memcpy hooks). -/
theorem pqRatchetStateEncodeToVec_ro_pinned_placed_ok_of_contracts [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionSpec)
    (hcp_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 313)
      (withLsCodeLoaded lsmpl (encodeChainParamsExactSpecOf doReserveStack A)))
    (hed_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 317)
      (withLsCodeLoaded lsmpl (encodeEpochDirectionExactSpecOf doReserveStack A)))
    (hauth_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 314)
      (withLsCodeLoaded lsmpl (authEncodeExactSpecOf doReserveStack A)))
    (hpolyEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 316)
      (withLsCodeLoaded lsmpl (etvPolyEncoderExactSpecOf doReserveStack A)))
    (hpolyDec_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 315)
      (withLsCodeLoaded lsmpl (etvPolyDecoderExactSpecOf doReserveStack A)))
    (hekEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 318)
      (withLsCodeLoaded lsmpl (etvEkSentCt1ReceivedEncodeSpecOf doReserveStack A)))
    (hct1SentEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 319)
      (withLsCodeLoaded lsmpl (etvCt1SentEncodeSpecOf doReserveStack A))) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext))
      (blkPl_426).base
      (withLsCodeLoaded lsmpl (pqRatchetStateEncodeToVecRoPinnedPlacedSpecOf doReserveStack A)) := by
  apply subroutine_ok_of_sepWPp; intro x R s0 hpc hrun hpre hsp
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  have hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf doReserveStack A)) :=
    etv_encodeVarint_placed_ok h_panic hshim halloc hrealloc s0 hcl0
  have hcp_call : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 313)
      (withStepInv s0 (encodeChainParamsExactSpecOf doReserveStack A)) :=
    subroutine_ok_withStepInv_lscl hcl0 hcp_ok
  have hep_call : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 399)
      (withStepInv s0 (epochEncLenStackSpecOf doReserveStack A)) :=
    etv_epochEncodedLen_placed_ok (by decide) A ext s0 hcl0
  have hed_call : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 317)
      (withStepInv s0 (encodeEpochDirectionExactSpecOf doReserveStack A)) :=
    subroutine_ok_withStepInv_lscl hcl0 hed_ok
  have hauthEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 314)
      (withStepInv s0 (authEncodeExactSpecOf doReserveStack A)) :=
    subroutine_ok_withStepInv_lscl hcl0 hauth_ok
  have hpolyEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 316)
      (withStepInv s0 (etvPolyEncoderExactSpecOf doReserveStack A)) :=
    subroutine_ok_withStepInv_lscl hcl0 hpolyEnc_ok
  have hpolyDec : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 315)
      (withStepInv s0 (etvPolyDecoderExactSpecOf doReserveStack A)) :=
    subroutine_ok_withStepInv_lscl hcl0 hpolyDec_ok
  have hekEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 318)
      (withStepInv s0 (etvEkSentCt1ReceivedEncodeSpecOf doReserveStack A)) :=
    subroutine_ok_withStepInv_lscl hcl0 hekEnc_ok
  have hct1SentEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 319)
      (withStepInv s0 (etvCt1SentEncodeSpecOf doReserveStack A)) :=
    subroutine_ok_withStepInv_lscl hcl0 hct1SentEnc_ok
  obtain ⟨P, hP, hwp⟩ := pqRatchetStateEncodeToVec_gen_placed_ok (by decide)
    (etv_chainEncodedLen_placed_ok A ext s0 hcl0)
    (etv_v1StateEncodedLen_placed_ok A ext s0 hcl0)
    (etv_shim_placed_ok hshim s0)
    (etv_rustAlloc_placed_ok (by decide) (by decide) halloc s0)
    (etv_handle_alloc_error_placed h_panic)
    hvarint
    (etv_memcpy_placed_ok hmc)
    hcp_call hep_call hed_call
    (step_encodeToVec_inner_at_1880_all_placed (by decide) A ext s0 hcl0
      hvarint hauthEnc hpolyEnc hpolyDec hekEnc hct1SentEnc (etv_memcpy_placed_ok hmc))
    hpc hrun hpre hsp
  exact ⟨P, R, hP, etv_sepWPp_mono_post (fun sf Q ⟨hq, hspf, hcsf⟩ => ⟨fun hm => (hq hm).2, hspf, hcsf⟩) hwp⟩

theorem pqRatchetStateEncodeToVec_ro_placed_ok_of_contracts [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionSpec)
    (hcp_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 313)
      (withLsCodeLoaded lsmpl (encodeChainParamsExactSpecOf doReserveStack A)))
    (hed_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 317)
      (withLsCodeLoaded lsmpl (encodeEpochDirectionExactSpecOf doReserveStack A)))
    (hauth_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 314)
      (withLsCodeLoaded lsmpl (authEncodeExactSpecOf doReserveStack A)))
    (hpolyEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 316)
      (withLsCodeLoaded lsmpl (etvPolyEncoderExactSpecOf doReserveStack A)))
    (hpolyDec_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 315)
      (withLsCodeLoaded lsmpl (etvPolyDecoderExactSpecOf doReserveStack A)))
    (hekEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 318)
      (withLsCodeLoaded lsmpl (etvEkSentCt1ReceivedEncodeSpecOf doReserveStack A)))
    (hct1SentEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 319)
      (withLsCodeLoaded lsmpl (etvCt1SentEncodeSpecOf doReserveStack A))) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext))
      (blkPl_426).base
      (withLsCodeLoaded lsmpl (pqRatchetStateEncodeToVecRoPlacedSpecOf doReserveStack A)) :=
  pqRatchetStateEncodeToVec_ro_placed_ok_of_pinned
    (pqRatchetStateEncodeToVec_ro_pinned_placed_ok_of_contracts
      h_panic hshim halloc hrealloc hmc
      hcp_ok hed_ok hauth_ok hpolyEnc_ok hpolyDec_ok hekEnc_ok hct1SentEnc_ok)

/-- Top-level `subroutine_ok` for `PqRatchetState::encode_to_vec` (`Block 426`) on
`withLsRoLoaded lsmpl (withLsCodeLoaded lsmpl (pqRatchetStateEncodeToVecPinnedSpecOf doReserveStackX A))`
(discharging all `encoded_len` callees, `encode_varint4`, allocator/memcpy hooks, and `.rodata` jump tables). -/
theorem pqRatchetStateEncodeToVec_pinned_placed_ok_of_contracts [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionSpec)
    (hcp_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 313)
      (withLsCodeLoaded lsmpl (encodeChainParamsExactSpecOf doReserveStackX A)))
    (hed_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 317)
      (withLsCodeLoaded lsmpl (encodeEpochDirectionExactSpecOf doReserveStackX A)))
    (hauth_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 314)
      (withLsCodeLoaded lsmpl (authEncodeExactSpecOf doReserveStackX A)))
    (hpolyEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 316)
      (withLsCodeLoaded lsmpl (etvPolyEncoderExactSpecOf doReserveStackX A)))
    (hpolyDec_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 315)
      (withLsCodeLoaded lsmpl (etvPolyDecoderExactSpecOf doReserveStackX A)))
    (hekEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 318)
      (withLsCodeLoaded lsmpl (etvEkSentCt1ReceivedEncodeSpecOf doReserveStackX A)))
    (hct1SentEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 319)
      (withLsCodeLoaded lsmpl (etvCt1SentEncodeSpecOf doReserveStackX A))) :
    PqRatchetStateEncodeToVecPinnedPlacedOkExt A ext := by
  apply subroutine_ok_of_sepWPp; intro x R s0 hpc hrun hpre hsp
  dsimp only [withLsRoLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  obtain ⟨hro0, hpre⟩ := hpre
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  have hpre_ro1 := v1StateJumpTableBytes_lsro_local2_intro hro0 hpre
  have hpre_ro2 := etvJumpTableBytes_lsro_intro hro0 hpre_ro1
  have hpre_ro : s0.mem ⊨
      (pqRatchetStateEncodeToVecRoPinnedPlacedSpecOf doReserveStackX A).pre x s0 ∗ R := by
    dsimp only [pqRatchetStateEncodeToVecPinnedSpecOf,
      pqRatchetStateEncodeToVecRoPinnedPlacedSpecOf, lsρ] at hpre_ro2 ⊢
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre_ro2
  have hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf doReserveStackX A)) :=
    etv_encodeVarint_exact_of_fit_placed (by decide)
      (etv_subroutine_ok_placed_of_lscl hcl0
        (encode_varint4_fit_placed_ok_x h_panic hshim halloc hrealloc))
  have hcp_call : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 313)
      (withStepInv s0 (encodeChainParamsExactSpecOf doReserveStackX A)) :=
    subroutine_ok_withStepInv_lscl hcl0 hcp_ok
  have hep_call : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 399)
      (withStepInv s0 (epochEncLenStackSpecOf doReserveStackX A)) :=
    etv_epochEncodedLen_placed_ok (by decide) A ext s0 hcl0
  have hed_call : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 317)
      (withStepInv s0 (encodeEpochDirectionExactSpecOf doReserveStackX A)) :=
    subroutine_ok_withStepInv_lscl hcl0 hed_ok
  have hauthEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 314)
      (withStepInv s0 (authEncodeExactSpecOf doReserveStackX A)) :=
    subroutine_ok_withStepInv_lscl hcl0 hauth_ok
  have hpolyEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 316)
      (withStepInv s0 (etvPolyEncoderExactSpecOf doReserveStackX A)) :=
    subroutine_ok_withStepInv_lscl hcl0 hpolyEnc_ok
  have hpolyDec : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 315)
      (withStepInv s0 (etvPolyDecoderExactSpecOf doReserveStackX A)) :=
    subroutine_ok_withStepInv_lscl hcl0 hpolyDec_ok
  have hekEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 318)
      (withStepInv s0 (etvEkSentCt1ReceivedEncodeSpecOf doReserveStackX A)) :=
    subroutine_ok_withStepInv_lscl hcl0 hekEnc_ok
  have hct1SentEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 319)
      (withStepInv s0 (etvCt1SentEncodeSpecOf doReserveStackX A)) :=
    subroutine_ok_withStepInv_lscl hcl0 hct1SentEnc_ok
  obtain ⟨P, hP, hwp⟩ := pqRatchetStateEncodeToVec_gen_placed_ok (by decide)
    (etv_chainEncodedLen_placed_ok A ext s0 hcl0)
    (etv_v1StateEncodedLen_placed_ok A ext s0 hcl0)
    (etv_shim_placed_ok hshim s0)
    (etv_rustAlloc_placed_ok (by decide) (by decide) halloc s0)
    (etv_handle_alloc_error_placed h_panic)
    hvarint
    (etv_memcpy_placed_ok hmc)
    hcp_call hep_call hed_call
    (step_encodeToVec_inner_at_1880_all_placed (by decide) A ext s0 hcl0
      hvarint hauthEnc hpolyEnc hpolyDec hekEnc hct1SentEnc (etv_memcpy_placed_ok hmc))
    hpc hrun hpre_ro hsp
  refine ⟨P, R, hP, etv_sepWPp_mono_post (fun sf Q ⟨hq, hspf, hcsf⟩ => ⟨fun hm => ?_, hspf, hcsf⟩) hwp⟩
  obtain ⟨_, hpost_ro⟩ := hq hm
  dsimp only [withLsRoLoaded, withLsCodeLoaded, pqRatchetStateEncodeToVecRoPinnedPlacedSpecOf,
    pqRatchetStateEncodeToVecPinnedSpecOf] at hpost_ro ⊢
  have hpost_perm : sf.mem ⊨
      ((lsρ v1StateJtSymLocal2 ↦ᵣ v1StateJumpTableBytes) ∗
       ((blkPl_426).ρ etvJumpTableRoSym ↦ᵣ encodeToVecJumpTableBytes)) ∗
      ((⌜sf.trace = s0.trace⌝ ∗
        vecU8 A x.sret (PqRatchetState.encodeRaw x.st) ∗
        pqRatchetStatePBPinnedAt A x.g x.a x.st ∗
        A.pool ∗ stackAt s0.sp (encodeToVecStackOf doReserveStackX)) ∗ R) := by
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost_ro
  exact Satisfies.of_sep_right hpost_perm

theorem pqRatchetStateEncodeToVec_placed_ok_of_contracts [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionSpec)
    (hcp_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 313)
      (withLsCodeLoaded lsmpl (encodeChainParamsExactSpecOf doReserveStackX A)))
    (hed_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 317)
      (withLsCodeLoaded lsmpl (encodeEpochDirectionExactSpecOf doReserveStackX A)))
    (hauth_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 314)
      (withLsCodeLoaded lsmpl (authEncodeExactSpecOf doReserveStackX A)))
    (hpolyEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 316)
      (withLsCodeLoaded lsmpl (etvPolyEncoderExactSpecOf doReserveStackX A)))
    (hpolyDec_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 315)
      (withLsCodeLoaded lsmpl (etvPolyDecoderExactSpecOf doReserveStackX A)))
    (hekEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 318)
      (withLsCodeLoaded lsmpl (etvEkSentCt1ReceivedEncodeSpecOf doReserveStackX A)))
    (hct1SentEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 319)
      (withLsCodeLoaded lsmpl (etvCt1SentEncodeSpecOf doReserveStackX A))) :
    PqRatchetStateEncodeToVecPlacedOkExt A ext :=
  pqRatchetStateEncodeToVec_placed_ok_of_pinned
    (pqRatchetStateEncodeToVec_pinned_placed_ok_of_contracts
      h_panic hshim halloc hrealloc hmc
      hcp_ok hed_ok hauth_ok hpolyEnc_ok hpolyDec_ok hekEnc_ok hct1SentEnc_ok)

end CryptoVerification.SpqrV1.Prost.EncodeToVec

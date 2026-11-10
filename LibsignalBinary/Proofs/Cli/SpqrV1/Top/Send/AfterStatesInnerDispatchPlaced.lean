/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerHeaderPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesEncodedLen
import LibsignalBinary.Proofs.Cli.SpqrV1.Auth.Encode1Placed
import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.ChainParams1Placed
import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.Ct1SentPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.EkSentCt1ReceivedPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.EpochDirection1Placed
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesChunkedHeaderSentPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesChunkedPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesPolyPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked59_71Placed
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked82_93Placed
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesChainEncodePlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesEncodePlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesEncodedLenPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerChunked1Placed
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerChunked2Placed
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerChunked3Placed
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerChunked3aPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesPolyDecExactPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesPolyExactPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesVnEncodePlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint2Placed
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.CalleeBridges
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.CalleeBridgesPlaced
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.V1StateHelpers
import ProofLib.SepLogic.WPp

/-!
# Relocatable `spqr::send::<signal_session_ratchet::Coins>` Phase 3e Dispatch & Master Encode (Block `427`)

Dispatches all 11 `V1State` variants at `+6616` and composes full `PqRatchetState`
encoded-length, buffer allocation, and encoding (`+4288/+4364 -> +6216`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace CryptoVerification.Cli.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SpqrV1.Poly.NextChunk (AllocContractsPlaced)
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.ProtoRepr hiding tripleRatchetProgAtExt
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.Auth hiding SepWPp.pure_elim
open CryptoVerification.SpqrV1.Prost.MessageEncode
open CryptoVerification.SpqrV1.Prost.EncodeToVec hiding allowPanic_not_exited
open CryptoVerification.SpqrV1
open CryptoVerification.SpqrV1.Top.Send
open CryptoVerification.Cli.SpqrV1.Top.Send.CodePlaced
open CryptoVerification.Cli.SpqrV1.ProtoRepr
open CryptoVerification.Cli.SpqrV1.ProtoRepr.EncodedLen
open CryptoVerification.Cli.SpqrV1.Prost.MessageEncode
open CryptoVerification.Cli.SpqrV1.Varint
open CryptoVerification.Cli.SpqrV1.Auth

variable [LibsignalPlacement]

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero spqrSendPlacedEntry blkPl_427_ρ
  EncodedLen.zeroExtend64_beq_zero32
  EncodedLen.ofNat_countLeadingZeros_64 EncodedLen.ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 EncodedLen.hwVarintLen_eq_ofNat_varintLen_norm
  EncodedLen.hwVarintLen_bvShift_eq_ofNat_varintLen_norm EncodedLen.zext64_truncate32
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
  Prost.EncodeToVec.noneCap2_add_two_beq_zero Prost.EncodeToVec.noneCap2_add_two_bne_zero
  ProtoRepr.noneCap_add_two_beq_zero ProtoRepr.noneCap_add_two_bne_zero
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
  EncodedLen.ule_zero_64 EncodedLen.ult_zero_64 EncodedLen.ule_self_64 EncodedLen.ult_self_64

/-! ## 1. `[local#1]` Callee `subroutine_ok` Bridges for `spqr::send` (Block `427`) -/

private theorem hookSat_sessionMemcpyRegion_of_alloc {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced A ext) :
    HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionSpec := by
  obtain ⟨f, hf, hsat⟩ := hA.session_memcpy 0
  refine ⟨f, hf, fun ⟨dst, src, srcBytes⟩ R s0 hrun hpre hal => ?_⟩
  have hpre' : s0.mem ⊨ (sessionMemcpySpec 0).pre (dst, src, srcBytes) s0 ∗ R := by
    dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec, sessionMemcpySpec, libcMemcpySpec, stackAt] at hpre ⊢
    rw [ProofLib.memRegion_zero]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
  obtain ⟨hF, hsym, ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩⟩ :=
    hsat (dst, src, srcBytes) R s0 hrun hpre' hal
  · refine ⟨hF, hsym, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [sessionMemcpyRegionSpec, sessionMemcpySpec, stackAt] at hpost ⊢
    rw [ProofLib.memRegion_zero] at hpost
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
  · exact (ProofLib.allowPanic_not_exited hpan).elim
  · exact (ProofLib.allowPanic_not_exited hex).elim
  · exact (ProofLib.allowPanic_not_exited hoom).elim

theorem spqrSend_encodeVarint_ok_placed {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced A ext)
    {s0 : State} (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf doReserveStack A)) := by
  apply etv_encodeVarint_exact_of_fit_placed (by decide)
  exact spqrSend_subroutine_ok_placed_of_lscl hcl0
    (encode_varint2_fit_placed_ok hA.handle_error hA.shim hA.alloc hA.realloc)

theorem spqrSend_encodeVarint_ok_x_placed {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced A ext)
    {s0 : State} (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf doReserveStackX A)) := by
  apply etv_encodeVarint_exact_of_fit_placed (by decide)
  exact spqrSend_subroutine_ok_placed_of_lscl hcl0
    (encode_varint2_fit_placed_ok_x hA.handle_error hA.shim hA.alloc hA.realloc)

theorem spqrSend_encodeChainParams_ok_placed {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced A ext)
    {s0 : State} (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 453)
      (withStepInv s0 (encodeChainParamsExactSpecOf doReserveStack A)) := by
  apply etv_encodeChainParams_exact_of_spec (by decide)
  exact spqrSend_subroutine_ok_placed_of_lscl hcl0
    (encode_chainParams_1_placed_ok hA.handle_error hA.shim hA.alloc hA.realloc)

theorem spqrSend_encodeChainParams_ok_x_placed {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced A ext)
    {s0 : State} (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 453)
      (withStepInv s0 (encodeChainParamsExactSpecOf doReserveStackX A)) := by
  apply etv_encodeChainParams_exact_of_spec (by decide)
  exact spqrSend_subroutine_ok_placed_of_lscl hcl0
    (encode_chainParams_1_placed_ok_x hA.handle_error hA.shim hA.alloc hA.realloc)

theorem spqrSend_encodeEpochDirection_ok_placed {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced A ext)
    {s0 : State} (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 457)
      (withStepInv s0 (encodeEpochDirectionExactSpecOf doReserveStack A)) := by
  apply etv_encodeEpochDirection_exact_of_spec (by decide)
  exact spqrSend_subroutine_ok_placed_of_lscl hcl0
    (encode_epochDirection_1_pinned_placed_ok hA.handle_error hA.shim hA.alloc hA.realloc
      (hookSat_sessionMemcpyRegion_of_alloc hA))

theorem spqrSend_encodeEpochDirection_ok_x_placed {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced A ext)
    {s0 : State} (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 457)
      (withStepInv s0 (encodeEpochDirectionExactSpecOf doReserveStackX A)) := by
  apply etv_encodeEpochDirection_exact_of_spec (by decide)
  exact spqrSend_subroutine_ok_placed_of_lscl hcl0
    (encode_epochDirection_1_pinned_placed_ok_x hA.handle_error hA.shim hA.alloc hA.realloc
      (hookSat_sessionMemcpyRegion_of_alloc hA))

theorem spqrSend_authEncode_ok_placed {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced A ext)
    {s0 : State} (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 454)
      (withStepInv s0 (authEncodeExactSpecOf doReserveStack A)) := by
  apply etv_authEncode_exact_of_spec (by decide)
  exact spqrSend_subroutine_ok_placed_of_lscl hcl0
    (auth_encode_1_pinned_placed_ok hA.handle_error hA.shim hA.alloc hA.realloc
      (hookSat_sessionMemcpyRegion_of_alloc hA))

theorem spqrSend_authEncode_ok_x_placed {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced A ext)
    {s0 : State} (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 454)
      (withStepInv s0 (authEncodeExactSpecOf doReserveStackX A)) := by
  apply etv_authEncode_exact_of_spec (by decide)
  exact spqrSend_subroutine_ok_placed_of_lscl hcl0
    (auth_encode_1_pinned_placed_ok_x hA.handle_error hA.shim hA.alloc hA.realloc
      (hookSat_sessionMemcpyRegion_of_alloc hA))

theorem spqrSend_polyEncoderEncode_ok_placed {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced A ext)
    {s0 : State} (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 456)
      (withStepInv s0 (etvPolyEncoderExactSpecOf doReserveStack A)) := by
  apply etv_polyEncoderEncode_exact_of_spec
  exact spqrSend_subroutine_ok_placed_of_lscl hcl0
    (encode_polyEncoder_1_exact_pinned_placed_ok hA.handle_error hA.shim hA.alloc hA.realloc
      (hookSat_sessionMemcpyRegion_of_alloc hA))

theorem spqrSend_polyEncoderEncode_ok_x_placed {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced A ext)
    {s0 : State} (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 456)
      (withStepInv s0 (etvPolyEncoderExactSpecOf doReserveStackX A)) := by
  apply etv_polyEncoderEncode_exact_of_spec
  exact spqrSend_subroutine_ok_placed_of_lscl hcl0
    (encode_polyEncoder_1_exact_pinned_placed_ok_x hA.handle_error hA.shim hA.alloc hA.realloc
      (hookSat_sessionMemcpyRegion_of_alloc hA))

theorem spqrSend_polyDecoderEncode_ok_placed {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced A ext)
    {s0 : State} (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 455)
      (withStepInv s0 (etvPolyDecoderExactSpecOf doReserveStack A)) := by
  apply etv_polyDecoderEncode_exact_of_spec
  exact spqrSend_subroutine_ok_placed_of_lscl hcl0
    (encode_polyDecoder_1_exact_pinned_placed_ok hA.handle_error hA.shim hA.alloc hA.realloc
      (hookSat_sessionMemcpyRegion_of_alloc hA))

theorem spqrSend_polyDecoderEncode_ok_x_placed {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced A ext)
    {s0 : State} (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 455)
      (withStepInv s0 (etvPolyDecoderExactSpecOf doReserveStackX A)) := by
  apply etv_polyDecoderEncode_exact_of_spec
  exact spqrSend_subroutine_ok_placed_of_lscl hcl0
    (encode_polyDecoder_1_exact_pinned_placed_ok_x hA.handle_error hA.shim hA.alloc hA.realloc
      (hookSat_sessionMemcpyRegion_of_alloc hA))

theorem spqrSend_ekSentCt1ReceivedEncode_ok_placed {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced A ext)
    {s0 : State} (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 458)
      (withStepInv s0 (etvEkSentCt1ReceivedEncodeSpecOf doReserveStack A)) := by
  apply etv_ekSentCt1ReceivedEncode_of_spec
  exact spqrSend_subroutine_ok_placed_of_lscl hcl0
    (ek_sent_ct1_received_encode_1_pinned_placed_ok hA.handle_error hA.shim hA.alloc hA.realloc
      (hookSat_sessionMemcpyRegion_of_alloc hA))

theorem spqrSend_ekSentCt1ReceivedEncode_ok_x_placed {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced A ext)
    {s0 : State} (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 458)
      (withStepInv s0 (etvEkSentCt1ReceivedEncodeSpecOf doReserveStackX A)) := by
  apply etv_ekSentCt1ReceivedEncode_of_spec
  exact spqrSend_subroutine_ok_placed_of_lscl hcl0
    (ek_sent_ct1_received_encode_1_pinned_placed_ok_x hA.handle_error hA.shim hA.alloc hA.realloc
      (hookSat_sessionMemcpyRegion_of_alloc hA))

theorem spqrSend_ct1SentEncode_ok_placed {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced A ext)
    {s0 : State} (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 459)
      (withStepInv s0 (etvCt1SentEncodeSpecOf doReserveStack A)) := by
  have hmc := hookSat_sessionMemcpyRegion_of_alloc hA
  apply etv_ct1SentEncode_of_spec
  exact spqrSend_subroutine_ok_placed_of_lscl hcl0
    (CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.ct1_sent_encode_1_pinned_placed_ok hA.handle_error hA.shim hA.alloc hA.realloc hmc)

theorem spqrSend_ct1SentEncode_ok_x_placed {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced A ext)
    {s0 : State} (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 459)
      (withStepInv s0 (etvCt1SentEncodeSpecOf doReserveStackX A)) := by
  have hmc := hookSat_sessionMemcpyRegion_of_alloc hA
  apply etv_ct1SentEncode_of_spec
  exact spqrSend_subroutine_ok_placed_of_lscl hcl0
    (CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.ct1_sent_encode_1_pinned_placed_ok_x hA.handle_error hA.shim hA.alloc hA.realloc hmc)

theorem spqrSend_keysUnsampledEncodedLen_ok_placed (A : RustAlloc)
    (ext : String → Option (State → State)) (s0 : State)
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 479)
      (withStepInv s0 (leafEncLen16Spec (keysUnsampledPBPinnedAt A) keysUnsampledPBEncodedLen)) :=
  spqrSend_subroutine_ok_placed_of_plain hcl0
    (keysUnsampledEncodedLen_local1_pinned_placed_ok_ext A ext)

theorem spqrSend_headerSentEncodedLen_ok_placed (A : RustAlloc)
    (ext : String → Option (State → State)) (s0 : State)
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 492)
      (withStepInv s0 (leafEncLen16Spec (headerSentPBPinnedAt A) headerSentPBEncodedLen)) :=
  spqrSend_subroutine_ok_placed_of_plain hcl0
    (headerSentEncodedLen_local1_pinned_placed_ok_ext A ext)

theorem spqrSend_chunkedHeaderSentEncodedLen_ok_placed (A : RustAlloc)
    (ext : String → Option (State → State)) (s0 : State)
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 495)
      (withStepInv s0 (leafEncLen48Spec (chunkedHeaderSentPBPinnedAt A) chunkedHeaderSentPBEncodedLen)) :=
  spqrSend_subroutine_ok_placed_of_lscl hcl0
    (chunkedHeaderSentEncodedLen_local1_pinned_placed_ok_ext A ext)

theorem spqrSend_ekSentEncodedLen_ok_placed (A : RustAlloc)
    (ext : String → Option (State → State)) (s0 : State)
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 496)
      (withStepInv s0 (leafEncLen16Spec (ekSentPBPinnedAt A) ekSentPBEncodedLen)) :=
  spqrSend_subroutine_ok_placed_of_plain hcl0
    (ekSentEncodedLen_local1_pinned_placed_ok_ext A ext)

theorem spqrSend_ekSentCt1ReceivedEncodedLen_ok_placed (A : RustAlloc)
    (ext : String → Option (State → State)) (s0 : State)
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 499)
      (withStepInv s0 (leafEncLen16Spec (ekSentCt1ReceivedPBPinnedAt A) ekSentCt1ReceivedPBEncodedLen)) :=
  spqrSend_subroutine_ok_placed_of_plain hcl0
    (ekSentCt1ReceivedEncodedLen_local1_pinned_placed_ok_ext A ext)

theorem spqrSend_ct1SentEncodedLen_ok_placed (A : RustAlloc)
    (ext : String → Option (State → State)) (s0 : State)
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 487)
      (withStepInv s0 (leafEncLen16Spec (ct1SentPBPinnedAt A) ct1SentPBEncodedLen)) :=
  spqrSend_subroutine_ok_placed_of_plain hcl0
    (ct1SentEncodedLen_local1_pinned_placed_ok_ext A ext)

theorem spqrSend_noHeaderReceivedEncodedLen_ok_placed (A : RustAlloc)
    (ext : String → Option (State → State)) (s0 : State)
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 500)
      (withStepInv s0 (leafEncLen16Spec (noHeaderReceivedPBPinnedAt A) noHeaderReceivedPBEncodedLen)) :=
  spqrSend_subroutine_ok_placed_of_plain hcl0
    (noHeaderReceivedEncodedLen_local1_pinned_placed_ok_ext A ext)

theorem spqrSend_headerReceivedEncodedLen_ok_placed (A : RustAlloc)
    (ext : String → Option (State → State)) (s0 : State)
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 482)
      (withStepInv s0 (leafEncLen16Spec (headerReceivedPBPinnedAt A) headerReceivedPBEncodedLen)) :=
  spqrSend_subroutine_ok_placed_of_plain hcl0
    (headerReceivedEncodedLen_local1_pinned_placed_ok_ext A ext)

theorem spqrSend_chunkedCt1SampledEncodedLen_ok_placed (A : RustAlloc)
    (ext : String → Option (State → State)) (s0 : State)
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 486)
      (withStepInv s0 (chunkedCt1SampledEncodedLenPinnedSpec A)) :=
  spqrSend_subroutine_ok_placed_of_lscl hcl0
    (chunkedCt1SampledEncodedLen_local1_pinned_placed_ok_ext A ext)

theorem spqrSend_ct1SentEkReceivedEncodedLen_ok_placed (A : RustAlloc)
    (ext : String → Option (State → State)) (s0 : State)
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 469)
      (withStepInv s0 (leafEncLen16Spec (ct1SentEkReceivedPBPinnedAt A) ct1SentEkReceivedPBEncodedLen)) :=
  spqrSend_subroutine_ok_placed_of_plain hcl0
    (ct1SentEkReceivedEncodedLen_local1_pinned_placed_ok_ext A ext)

theorem spqrSend_ct2SentEncodedLen_ok_placed (A : RustAlloc)
    (ext : String → Option (State → State)) (s0 : State)
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 470)
      (withStepInv s0 (leafEncLen16Spec (ct2SentPBPinnedAt A) ct2SentPBEncodedLen)) :=
  spqrSend_subroutine_ok_placed_of_plain hcl0
    (ct2SentEncodedLen_local1_pinned_placed_ok_ext A ext)

theorem spqrSend_polyDecoderEncodedLen_ok_placed (A : RustAlloc)
    (ext : String → Option (State → State)) (s0 : State)
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 493)
      (withStepInv s0 (leafEncLen16Spec (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen)) :=
  spqrSend_subroutine_ok_placed_of_plain hcl0
    (polynomialDecoderEncodedLen_local1_pinned_placed_ok_ext A ext)

theorem spqrSend_polyEncoderEncodedLen_ok_placed (A : RustAlloc)
    (ext : String → Option (State → State)) (s0 : State)
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 480)
      (withStepInv s0 (leafEncLen16Spec (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen)) :=
  spqrSend_subroutine_ok_placed_of_plain hcl0
    (polynomialEncoderEncodedLen_local1_pinned_placed_ok_ext A ext)

/-! ## 2. Unified `StepSendInnerStateAt6616Placed` Dispatch across All 11 Variants -/

theorem step_send_inner_at_6616_of_variants_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (A : RustAlloc) (ext : String → Option (State → State))
    {roBase : BitVec 64} {s0 : State}
    (hkuLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 479)
      (withStepInv s0 (leafEncLen16Spec (keysUnsampledPBPinnedAt A) keysUnsampledPBEncodedLen)))
    (hhs16Len : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 492)
      (withStepInv s0 (leafEncLen16Spec (headerSentPBPinnedAt A) headerSentPBEncodedLen)))
    (hhsLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 495)
      (withStepInv s0 (leafEncLen48Spec (chunkedHeaderSentPBPinnedAt A) chunkedHeaderSentPBEncodedLen)))
    (hekSentLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 496)
      (withStepInv s0 (leafEncLen16Spec (ekSentPBPinnedAt A) ekSentPBEncodedLen)))
    (hekLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 499)
      (withStepInv s0 (leafEncLen16Spec (ekSentCt1ReceivedPBPinnedAt A) ekSentCt1ReceivedPBEncodedLen)))
    (hnhrLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 500)
      (withStepInv s0 (leafEncLen16Spec (noHeaderReceivedPBPinnedAt A) noHeaderReceivedPBEncodedLen)))
    (hhrLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 482)
      (withStepInv s0 (leafEncLen16Spec (headerReceivedPBPinnedAt A) headerReceivedPBEncodedLen)))
    (hct1SampledLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 486)
      (withStepInv s0 (chunkedCt1SampledEncodedLenPinnedSpec A)))
    (hct1SentEkLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 469)
      (withStepInv s0 (leafEncLen16Spec (ct1SentEkReceivedPBPinnedAt A) ct1SentEkReceivedPBEncodedLen)))
    (hct1SentLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 487)
      (withStepInv s0 (leafEncLen16Spec (ct1SentPBPinnedAt A) ct1SentPBEncodedLen)))
    (hct2Len : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 470)
      (withStepInv s0 (leafEncLen16Spec (ct2SentPBPinnedAt A) ct2SentPBEncodedLen)))
    (hpolyEncLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 480)
      (withStepInv s0 (leafEncLen16Spec (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen)))
    (hpolyDecLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 493)
      (withStepInv s0 (leafEncLen16Spec (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hauthEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 454)
      (withStepInv s0 (authEncodeExactSpecOf resStack A)))
    (hmemcpy : subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy") etvMemcpyRegionSpec)
    (hekEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 458)
      (withStepInv s0 (etvEkSentCt1ReceivedEncodeSpecOf resStack A)))
    (hct1SentEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 459)
      (withStepInv s0 (etvCt1SentEncodeSpecOf resStack A)))
    (hpolyEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 456)
      (withStepInv s0 (etvPolyEncoderExactSpecOf resStack A)))
    (hpolyDec : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 455)
      (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A)))
    (is : V1State.InnerState) :
    StepSendInnerStateAt6616Placed resStack A ext roBase s0 is := by
  cases is with
  | keysUnsampled v =>
    exact step_send_v1_keysUnsampled_at_6616_placed hres A ext hkuLen hvarint hauthEnc v
  | keysSampled v =>
    exact step_send_v1_keysSampled_at_6616_placed hres A ext
      hhs16Len hpolyEncLen hvarint hauthEnc hmemcpy hpolyEnc v
  | headerSent v =>
    exact step_send_v1_headerSent_at_6616_placed hres A ext
      hhsLen hekSentLen hvarint hauthEnc hmemcpy hpolyEnc hpolyDec v
  | ct1Received v =>
    exact step_send_v1_ct1Received_at_6616_placed hres A ext
      hekLen hpolyEncLen hvarint hekEnc hpolyEnc v
  | ekSentCt1Received v =>
    exact step_send_v1_ekSentCt1Received_at_6616_placed hres A ext
      hekLen hpolyDecLen hvarint hekEnc hpolyDec v
  | noHeaderReceived v =>
    exact step_send_v1_noHeaderReceived_at_6616_placed hres A ext
      hnhrLen hpolyDecLen hvarint hauthEnc hpolyDec v
  | headerReceived v =>
    exact step_send_v1_headerReceived_at_6616_placed hres A ext
      hhrLen hpolyDecLen hvarint hauthEnc hmemcpy hpolyDec v
  | ct1Sampled v =>
    exact step_send_v1_ct1Sampled_at_6616_placed hres A ext
      hct1SampledLen hvarint hct1SentEnc hpolyEnc hpolyDec v
  | ekReceivedCt1Sampled v =>
    exact step_send_v1_ekReceivedCt1Sampled_at_6616_placed hres A ext
      hct1SentEkLen hpolyEncLen hvarint hauthEnc hmemcpy hpolyEnc v
  | ct1Acknowledged v =>
    exact step_send_v1_ct1Acknowledged_at_6616_placed hres A ext
      hct1SentLen hpolyDecLen hvarint hct1SentEnc hpolyDec v
  | ct2Sampled v =>
    exact step_send_v1_ct2Sampled_at_6616_placed hres A ext
      hct2Len hpolyEncLen hvarint hauthEnc hpolyEnc v

theorem step_send_inner_at_6616_placed {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced A ext)
    {roBase : BitVec 64} {s0 : State} (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (is : V1State.InnerState) :
    StepSendInnerStateAt6616Placed doReserveStack A ext roBase s0 is :=
  step_send_inner_at_6616_of_variants_placed (by decide) A ext
    (spqrSend_keysUnsampledEncodedLen_ok_placed A ext s0 hcl0)
    (spqrSend_headerSentEncodedLen_ok_placed A ext s0 hcl0)
    (spqrSend_chunkedHeaderSentEncodedLen_ok_placed A ext s0 hcl0)
    (spqrSend_ekSentEncodedLen_ok_placed A ext s0 hcl0)
    (spqrSend_ekSentCt1ReceivedEncodedLen_ok_placed A ext s0 hcl0)
    (spqrSend_noHeaderReceivedEncodedLen_ok_placed A ext s0 hcl0)
    (spqrSend_headerReceivedEncodedLen_ok_placed A ext s0 hcl0)
    (spqrSend_chunkedCt1SampledEncodedLen_ok_placed A ext s0 hcl0)
    (spqrSend_ct1SentEkReceivedEncodedLen_ok_placed A ext s0 hcl0)
    (spqrSend_ct1SentEncodedLen_ok_placed A ext s0 hcl0)
    (spqrSend_ct2SentEncodedLen_ok_placed A ext s0 hcl0)
    (spqrSend_polyEncoderEncodedLen_ok_placed A ext s0 hcl0)
    (spqrSend_polyDecoderEncodedLen_ok_placed A ext s0 hcl0)
    (spqrSend_encodeVarint_ok_placed hA hcl0)
    (spqrSend_authEncode_ok_placed hA hcl0)
    (spqrSend_etvMemcpy_ok_placed hA)
    (spqrSend_ekSentCt1ReceivedEncode_ok_placed hA hcl0)
    (spqrSend_ct1SentEncode_ok_placed hA hcl0)
    (spqrSend_polyEncoderEncode_ok_placed hA hcl0)
    (spqrSend_polyDecoderEncode_ok_placed hA hcl0)
    is

theorem step_send_inner_at_6616_x_placed {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced A ext)
    {roBase : BitVec 64} {s0 : State} (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (is : V1State.InnerState) :
    StepSendInnerStateAt6616Placed doReserveStackX A ext roBase s0 is :=
  step_send_inner_at_6616_of_variants_placed (by decide) A ext
    (spqrSend_keysUnsampledEncodedLen_ok_placed A ext s0 hcl0)
    (spqrSend_headerSentEncodedLen_ok_placed A ext s0 hcl0)
    (spqrSend_chunkedHeaderSentEncodedLen_ok_placed A ext s0 hcl0)
    (spqrSend_ekSentEncodedLen_ok_placed A ext s0 hcl0)
    (spqrSend_ekSentCt1ReceivedEncodedLen_ok_placed A ext s0 hcl0)
    (spqrSend_noHeaderReceivedEncodedLen_ok_placed A ext s0 hcl0)
    (spqrSend_headerReceivedEncodedLen_ok_placed A ext s0 hcl0)
    (spqrSend_chunkedCt1SampledEncodedLen_ok_placed A ext s0 hcl0)
    (spqrSend_ct1SentEkReceivedEncodedLen_ok_placed A ext s0 hcl0)
    (spqrSend_ct1SentEncodedLen_ok_placed A ext s0 hcl0)
    (spqrSend_ct2SentEncodedLen_ok_placed A ext s0 hcl0)
    (spqrSend_polyEncoderEncodedLen_ok_placed A ext s0 hcl0)
    (spqrSend_polyDecoderEncodedLen_ok_placed A ext s0 hcl0)
    (spqrSend_encodeVarint_ok_x_placed hA hcl0)
    (spqrSend_authEncode_ok_x_placed hA hcl0)
    (spqrSend_etvMemcpy_ok_placed hA)
    (spqrSend_ekSentCt1ReceivedEncode_ok_x_placed hA hcl0)
    (spqrSend_ct1SentEncode_ok_x_placed hA hcl0)
    (spqrSend_polyEncoderEncode_ok_x_placed hA hcl0)
    (spqrSend_polyDecoderEncode_ok_x_placed hA hcl0)
    is

/-! ## 3. Master `PqRatchetState` Serialization in `spqr::send` (`+4288/+4364 -> +6216`) -/

/-- Step `spqrSendPlacedEntry + 4996#64 / +5604#64 -> spqrSendPlacedEntry + 6216#64`:
serializes `st.versionNegotiation`, `st.chain`, and `st.inner` into
`vecU8At A (sp + 1424#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr (PqRatchetState.encodeRaw st)`. -/
theorem step_send_encode_fields_31be0_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (A : RustAlloc) (ext : String → Option (State → State))
    {roV1 : BitVec 64} {s0 s : State}
    (hChainLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 485)
      (withStepInv s0 (chainEncodedLenPinnedSpec A)))
    (hv1Len : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 484)
      (withStepInv s0 (v1StateEncodedLenRoPinnedSpec A roV1)))
    (hep_call : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 478)
      (withStepInv s0 (epochEncLenStackSpecOf resStack A)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hmemcpy : subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy") etvMemcpyRegionSpec)
    (hed_call : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 457)
      (withStepInv s0 (encodeEpochDirectionExactSpecOf resStack A)))
    (hcp_call : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 453)
      (withStepInv s0 (encodeChainParamsExactSpecOf resStack A)))
    (hInnerAt6616 : ∀ is : V1State.InnerState,
      StepSendInnerStateAt6616Placed resStack A ext (lsρ spqrSendRoSym + 22#64) s0 is)
    (sp ptr v0 : BitVec 64) (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63) (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (if st.versionNegotiation.isSome then spqrSendPlacedEntry + 4996#64 else spqrSendPlacedEntry + 5604#64))
    (hrun : s.status = .Running) (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx0 : st.versionNegotiation.isSome → s.readReg64 .x0 = ptr)
    (hx20 : s.readReg64 .x20 = optPqRatchetInnerCap g.inner st.inner)
    (hx25 : s.readReg64 .x25 = optChainCap g.chain st.chain)
    (hx28 : s.readReg64 .x28 = sp + 4192#64)
    (hinv0 : StepInv s0 s)
    (hP : P = (pqRatchetStatePBPinnedAt A g (sp + 4704#64) st ∗
      (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
      ((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
      vecU8At A (sp + 1424#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr [] ∗
      A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗
      (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ optChainCap g.chain st.chain)) ∗ F)
    (hnext : ∀ (sm : State) (w0 : BitVec 64),
      sm.pc = spqrSendPlacedEntry + 6216#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = optChainCap g.chain st.chain →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = sp + 4192#64 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((pqRatchetStatePBPinnedAt A g (sp + 4704#64) st ∗
          (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
          ((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
          vecU8At A (sp + 1424#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr
            (PqRatchetState.encodeRaw st) ∗
          A.pool ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗
          (sp ↦₆₄ w0) ∗ ((sp + 16#64) ↦₆₄ optChainCap g.chain st.chain)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  subst hP
  refine step_send_versionNeg_31be0_placed A ext hvarint hmemcpy hcp_call
    sp ptr v0 g st hlen halign
    (F := (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
      ((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗ F)
    hpc hrun hsp htr hx0 hx25 hx28 hinv0 (by ac_rfl) ?_
  intro s1 w0 hpcs1 hruns1 hsps1 htrs1 hs1_19 hs1_20 hs1_21 hs1_23 hs1_25 hs1_27 hs1_28 hs1_fp hinv_s1
  rw [hx20] at hs1_20
  refine step_send_chain_31e40_placed hres A ext hChainLen hep_call hvarint hmemcpy hed_call hcp_call
    sp ptr g st hlen halign
    (F := (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
      ((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
      (sp ↦₆₄ w0) ∗ F)
    hpcs1 hruns1 hsps1 htrs1 hs1_25 hinv_s1 (by ac_rfl) ?_
  intro s2 hpcs2 hruns2 hsps2 htrs2 hs2_19 hs2_20 hs2_21 hs2_23 hs2_25 hs2_27 hs2_28 hs2_fp hinv_s2
  rw [hs1_19] at hs2_19; rw [hs1_20] at hs2_20; rw [hs1_21] at hs2_21; rw [hs1_23] at hs2_23
  rw [hs1_27] at hs2_27; rw [hs1_28] at hs2_28; rw [hs1_fp] at hs2_fp
  refine step_send_inner_32058_placed hres A ext hv1Len hvarint hInnerAt6616
    sp ptr (optChainCap g.chain st.chain) g st hlen halign
    (F := (sp ↦₆₄ w0) ∗ F)
    hpcs2 hruns2 hsps2 htrs2 hs2_20 hs2_25 hinv_s2 (by ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m
  rw [hs2_19] at hm19; rw [hs2_21] at hm21; rw [hs2_23] at hm23
  rw [hs2_27] at hm27; rw [hs2_28] at hm28; rw [hs2_fp] at hmfp
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (hnext sm w0 hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m)

/-- Step `spqrSendPlacedEntry + 4768#64 -> spqrSendPlacedEntry + 6216#64`:
computes `Option<Chain>::encoded_len`, `Option<pq_ratchet_state::Inner>::encoded_len`, allocates
the output buffer via `__rust_alloc`, and serializes all 3 fields of `st : PqRatchetState`. -/
theorem step_send_encode_from_31afc_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (hle_stack : encodeToVecCalleeStackOf resStack ≤ spqrSendCalleeStack)
    (A : RustAlloc) (ext : String → Option (State → State))
    {roV1 : BitVec 64} {s0 s1 : State}
    (hChainLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 485)
      (withStepInv s0 (chainEncodedLenPinnedSpec A)))
    (hv1Len : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 484)
      (withStepInv s0 (v1StateEncodedLenRoPinnedSpec A roV1)))
    (hshim : subroutine_ok (spqrSendPlacedProg ext) (lsρ spqrRustNoAllocShimSym)
      (withStepInv s0 spqrSendShimStackSpec))
    (halloc : subroutine_ok (spqrSendPlacedProg ext) (lsρ spqrRustAllocSym)
      (withStepInv s0 (spqrSendRustAllocStackSpec A)))
    (hhandle : (spqrSendPlacedProg ext).externAt? (lsρ spqrHandleErrorSym) = some Rust.panicked)
    (hep_call : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 478)
      (withStepInv s0 (epochEncLenStackSpecOf resStack A)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hmemcpy : subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy") etvMemcpyRegionSpec)
    (hed_call : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 457)
      (withStepInv s0 (encodeEpochDirectionExactSpecOf resStack A)))
    (hcp_call : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 453)
      (withStepInv s0 (encodeChainParamsExactSpecOf resStack A)))
    (hInnerAt6616 : ∀ is : V1State.InnerState,
      StepSendInnerStateAt6616Placed resStack A ext (lsρ spqrSendRoSym + 22#64) s0 is)
    (sp msg_cap v0 v_sp10 v_sp18 v_590 v_598 v_5a0 : BitVec 64)
    (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (hpos : 0 < pqRatchetStatePBEncodedLen st)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63) (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s1.pc = spqrSendPlacedEntry + 4768#64) (hrun : s1.status = .Running)
    (hsp : s1.sp = sp) (htr : s1.trace = s0.trace)
    (hx20 : s1.readReg64 .x20 =
      BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen st.versionNegotiation))
    (hx22 : s1.readReg64 .x22 = msg_cap)
    (hx24 : s1.readReg64 .x24 = sp + 4704#64)
    (hx25 : s1.readReg64 .x25 = optChainCap g.chain st.chain)
    (hx26 : s1.readReg64 .x26 = optVersionNegCap g.vn st.versionNegotiation)
    (hx28 : s1.readReg64 .x28 = sp + 4192#64)
    (hinv1 : StepInv s0 s1)
    (hP : P = (pqRatchetStatePBPinnedAt A g (sp + 4704#64) st ∗
      (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
      ((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
      A.pool ∗ stackAt sp spqrSendCalleeStack ∗
      (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ v_sp10) ∗ ((sp + 24#64) ↦₆₄ v_sp18) ∗
      ((sp + 1424#64) ↦₆₄ v_590) ∗ ((sp + 1432#64) ↦₆₄ v_598) ∗ ((sp + 1440#64) ↦₆₄ v_5a0)) ∗ F)
    (hnext : ∀ (sm : State) (ptr w0 : BitVec 64),
      sm.pc = spqrSendPlacedEntry + 6216#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s1.readReg64 .x19 → sm.readReg64 .x21 = s1.readReg64 .x21 →
      sm.readReg64 .x23 = s1.readReg64 .x23 → sm.readReg64 .x25 = optChainCap g.chain st.chain →
      sm.readReg64 .x27 = s1.readReg64 .x27 → sm.readReg64 .x28 = sp + 4192#64 →
      sm.readReg64 .fp = s1.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((pqRatchetStatePBPinnedAt A g (sp + 4704#64) st ∗
          (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
          ((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
          vecU8At A (sp + 1424#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr
            (PqRatchetState.encodeRaw st) ∗
          A.pool ∗ stackAt sp spqrSendCalleeStack ∗
          (sp ↦₆₄ w0) ∗ ((sp + 16#64) ↦₆₄ optChainCap g.chain st.chain) ∗
          ((sp + 24#64) ↦₆₄ msg_cap)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrSendPlacedProg ext) ret s1 P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  subst hP
  let F_stack := memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack)
    (spqrSendCalleeStack - encodeToVecCalleeStackOf resStack)
  refine step_send_chain_len_31afc_placed A ext hChainLen sp msg_cap v_sp18 g st hlen halign
    (F := (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
      ((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
      A.pool ∗ (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ v_sp10) ∗
      ((sp + 1424#64) ↦₆₄ v_590) ∗ ((sp + 1432#64) ↦₆₄ v_598) ∗ ((sp + 1440#64) ↦₆₄ v_5a0) ∗ F)
    hpc hrun hsp htr hx20 hx22 hx24 hx25 hinv1 (by ac_rfl) ?_
  intro s2 hpcs2 hruns2 hsps2 htrs2 hs2_19 hs2_21 hs2_22 hs2_23 hs2_24 hs2_25 hs2_26 hs2_27 hs2_28 hs2_fp hinv2
  rw [hx26] at hs2_26; rw [hx28] at hs2_28
  refine step_send_inner_len_31b48_ro_placed hres A ext hv1Len sp g st hlen halign
    (F := F_stack ∗ ((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗ A.pool ∗
      (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ v_sp10) ∗ ((sp + 24#64) ↦₆₄ msg_cap) ∗
      ((sp + 1424#64) ↦₆₄ v_590) ∗ ((sp + 1432#64) ↦₆₄ v_598) ∗ ((sp + 1440#64) ↦₆₄ v_5a0) ∗ F)
    hpcs2 hruns2 hsps2 htrs2 hs2_22 hs2_24 hinv2
    (by rw [stackAt_spqrSendCallee_split_enc sp (encodeToVecCalleeStackOf resStack) hle_stack]
        dsimp only [F_stack]; ac_rfl) ?_
  intro s3 hpcs3 hruns3 hsps3 htrs3 hs3_19 hs3_20 hs3_21 _ hs3_23 hs3_24 hs3_25 hs3_26 hs3_27 hs3_28 hs3_fp hinv3
  rw [hs2_19] at hs3_19; rw [hs2_21] at hs3_21; rw [hs2_23] at hs3_23; rw [hs2_25] at hs3_25
  rw [hs2_26] at hs3_26; rw [hs2_27] at hs3_27; rw [hs2_28] at hs3_28; rw [hs2_fp] at hs3_fp
  refine step_send_alloc_31b94_placed A ext hshim halloc hhandle
    sp v_sp10 v_590 v_598 v_5a0 g st hpos hlen halign
    (F := (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
      ((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
      (sp ↦₆₄ v0) ∗ ((sp + 24#64) ↦₆₄ msg_cap) ∗ F)
    hpcs3 hruns3 hsps3 htrs3 hs3_24 hs3_25 hs3_26 hinv3
    (by rw [stackAt_spqrSendCallee_split_enc sp (encodeToVecCalleeStackOf resStack) hle_stack]
        dsimp only [F_stack]; ac_rfl) ?_
  intro s4 ptr hpcs4 hruns4 hsps4 htrs4 hs4_0 hs4_19 hs4_20 hs4_21 _ hs4_23 _ hs4_25 _ hs4_27 hs4_28 hs4_fp hinv4
  rw [hs3_19] at hs4_19; rw [hs3_20] at hs4_20; rw [hs3_21] at hs4_21; rw [hs3_23] at hs4_23
  rw [hs3_27] at hs4_27; rw [hs3_28] at hs4_28; rw [hs3_fp] at hs4_fp
  refine step_send_encode_fields_31be0_placed hres A ext
    hChainLen hv1Len hep_call hvarint hmemcpy hed_call hcp_call hInnerAt6616
    sp ptr v0 g st hlen halign
    (F := F_stack ∗ ((sp + 24#64) ↦₆₄ msg_cap) ∗ F)
    hpcs4 hruns4 hsps4 htrs4 (fun _ => hs4_0) hs4_20 hs4_25 hs4_28 hinv4
    (by rw [stackAt_spqrSendCallee_split_enc sp (encodeToVecCalleeStackOf resStack) hle_stack]
        dsimp only [F_stack]; ac_rfl) ?_
  intro sm w0 hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m
  rw [hs4_19] at hm19; rw [hs4_21] at hm21; rw [hs4_23] at hm23
  rw [hs4_27] at hm27; rw [hs4_fp] at hmfp
  refine SepWPp.weaken_pre ?_
    (hnext sm ptr w0 hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m)
  rw [stackAt_spqrSendCallee_split_enc sp (encodeToVecCalleeStackOf resStack) hle_stack]
  dsimp only [F_stack]
  exact Entails.of_eq (by ac_rfl)

/-- Master `PqRatchetState` serialization step in `spqr::send` (`+4288 / +4364 -> +6216`):
from the entry of `Option<VersionNegotiation>::encoded_len`, computes all 3 field lengths,
allocates the output `Vec<u8>` buffer via `__rust_alloc`, and serializes all 3 fields of
`st : PqRatchetState` into `vecU8At A (sp + 1424#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr (PqRatchetState.encodeRaw st)`. -/
theorem step_vn_len_some_3191c_vregs_placed {ext : String → Option (State → State)}
    (A : RustAlloc) (s : State) (g : VersionNegotiationPBGhost) (vn : VersionNegotiationPB) (F : SepProp)
    (hpc : s.pc = spqrSendPlacedEntry + 4288#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hlen : vn.authKey.length < 2 ^ 64) :
    SepWP (spqrSendPlacedProg ext)
      (spqrSendPlacedEntry + 4768#64) s
      (versionNegotiationRest A g (s.sp + 4704#64) vn ∗ F)
      (fun s' P' => VRegsAt s s' ∧
        s'.status = .Running ∧ s'.sp = s.sp ∧ s'.trace = s.trace ∧
        s'.readReg64 .x19 = s.readReg64 .x19 ∧
        s'.readReg64 .x20 = BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen (some vn)) ∧
        s'.readReg64 .x21 = s.readReg64 .x21 ∧ s'.readReg64 .x22 = s.readReg64 .x22 ∧
        s'.readReg64 .x23 = s.readReg64 .x23 ∧ s'.readReg64 .x24 = s.readReg64 .x24 ∧
        s'.readReg64 .x25 = s.readReg64 .x25 ∧ s'.readReg64 .x26 = s.readReg64 .x26 ∧
        s'.readReg64 .x27 = s.readReg64 .x27 ∧ s'.readReg64 .x28 = s.readReg64 .x28 ∧
        s'.readReg64 .fp = s.readReg64 .fp ∧
        (P' ⊢ versionNegotiationRest A g (s.sp + 4704#64) vn ∗ F)) := by
  refine SepWP.seq (step_vn_len_authKey_3191c_vregs_placed A s g vn F hpc hrun hsp_align hlen) ?_
  intro s1 P1 hpc1 _ ⟨hv1, hrun1, hsp1, htr1, hx8_1, hx19_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp1, hP1⟩
  rw [← hsp1] at hP1
  refine SepWP.weaken_pre hP1 ?_
  refine SepWP.seq (step_vn_len_dir_31940_vregs_placed A s1 g vn F hpc1 hrun1 (by rw [hsp1]; exact hsp_align)) ?_
  intro s2 P2 hpc2 _ ⟨hv2, hrun2, hsp2, htr2, hx8_2, hx9_2, hx19_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp2, hP2⟩
  rw [← hsp2] at hP2
  refine SepWP.weaken_pre hP2 ?_
  refine SepWP.seq (step_vn_len_minVer_31974_vregs_placed A s2 g vn F hpc2 hrun2 (by rw [hsp2, hsp1]; exact hsp_align)) ?_
  intro s3 P3 hpc3 _ ⟨hv3, hrun3, hsp3, htr3, hx8_3, hx9_3, hx10_3, hx19_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hfp3, hP3⟩
  rw [← hsp3] at hP3
  refine SepWP.weaken_pre hP3 ?_
  refine SepWP.seq (step_vn_len_chainParams_319a0_vregs_placed A s3 g vn F hpc3 hrun3 (by rw [hsp3, hsp2, hsp1]; exact hsp_align)) ?_
  intro s4 P4 hpc4 _ ⟨hv4, hrun4, hsp4, htr4, hx8_4, hx9_4, hx10_4, hx11_4, hx19_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hfp4, hP4⟩
  have hsp3_eq : s3.sp = s.sp := hsp3.trans (hsp2.trans hsp1)
  rw [hsp3_eq] at hP4
  refine SepWP.weaken_pre hP4 ?_
  refine SepWP.mono (step_vn_len_combine_31ad4_vregs_placed s4 vn (versionNegotiationRest A g (s.sp + 4704#64) vn ∗ F)
    hpc4 hrun4 (hx8_4.trans (hx8_3.trans (hx8_2.trans hx8_1)))
    (hx9_4.trans (hx9_3.trans hx9_2)) (hx10_4.trans hx10_3) hx11_4) ?_
  intro s5 P5 _ _ ⟨hv5, hrun5, hsp5, htr5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, hfp5, hP5⟩
  exact ⟨⟨hv5.eq.trans (hv4.eq.trans (hv3.eq.trans (hv2.eq.trans hv1.eq)))⟩, hrun5, hsp5.trans (hsp4.trans hsp3_eq),
    htr5.trans (htr4.trans (htr3.trans (htr2.trans htr1))),
    hx19_5.trans (hx19_4.trans (hx19_3.trans (hx19_2.trans hx19_1))),
    hx20_5,
    hx21_5.trans (hx21_4.trans (hx21_3.trans (hx21_2.trans hx21_1))),
    hx22_5.trans (hx22_4.trans (hx22_3.trans (hx22_2.trans hx22_1))),
    hx23_5.trans (hx23_4.trans (hx23_3.trans (hx23_2.trans hx23_1))),
    hx24_5.trans (hx24_4.trans (hx24_3.trans (hx24_2.trans hx24_1))),
    hx25_5.trans (hx25_4.trans (hx25_3.trans (hx25_2.trans hx25_1))),
    hx26_5.trans (hx26_4.trans (hx26_3.trans (hx26_2.trans hx26_1))),
    hx27_5.trans (hx27_4.trans (hx27_3.trans (hx27_2.trans hx27_1))),
    hx28_5.trans (hx28_4.trans (hx28_3.trans (hx28_2.trans hx28_1))),
    hfp5.trans (hfp4.trans (hfp3.trans (hfp2.trans hfp1))),
    hP5⟩

theorem step_vn_len_unified_vregs_placed {ext : String → Option (State → State)}
    (A : RustAlloc) (s : State) (g : PqRatchetStatePBGhost) (st : PqRatchetState) (F : SepProp)
    (hpc : s.pc = spqrSendPlacedEntry +
      (if st.versionNegotiation.isSome then 4288#64 else 4364#64))
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63) :
    SepWP (spqrSendPlacedProg ext)
      (spqrSendPlacedEntry + 4768#64) s
      (optVersionNegotiationPBPinnedAt A g.vn (s.sp + 4704#64) st.versionNegotiation ∗ F)
      (fun s' P' => VRegsAt s s' ∧
        s'.status = .Running ∧ s'.sp = s.sp ∧ s'.trace = s.trace ∧
        s'.readReg64 .x19 = s.readReg64 .x19 ∧
        s'.readReg64 .x20 = BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen st.versionNegotiation) ∧
        s'.readReg64 .x21 = s.readReg64 .x21 ∧ s'.readReg64 .x22 = s.readReg64 .x22 ∧
        s'.readReg64 .x23 = s.readReg64 .x23 ∧ s'.readReg64 .x24 = s.readReg64 .x24 ∧
        s'.readReg64 .x25 = s.readReg64 .x25 ∧ s'.readReg64 .x26 = s.readReg64 .x26 ∧
        s'.readReg64 .x27 = s.readReg64 .x27 ∧ s'.readReg64 .x28 = s.readReg64 .x28 ∧
        s'.readReg64 .fp = s.readReg64 .fp ∧
        (P' ⊢ optVersionNegotiationPBPinnedAt A g.vn (s.sp + 4704#64) st.versionNegotiation ∗ F)) := by
  cases hvn : st.versionNegotiation with
  | none =>
    rw [hvn] at hpc
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hpc
    exact step_vn_len_none_31968_vregs_placed s (optVersionNegotiationPBPinnedAt A g.vn (s.sp + 4704#64) none ∗ F) hpc hrun
  | some vn =>
    rw [hvn] at hpc
    simp only [Option.isSome_some, ↓reduceIte] at hpc
    have hlen_vn := vn_authKey_len_lt_of_state hvn hlen
    have hpre_eq :
        optVersionNegotiationPBPinnedAt A g.vn (s.sp + 4704#64) (some vn) ∗ F =
        versionNegotiationRest A g.vn (s.sp + 4704#64) vn ∗
          (((s.sp + 4704#64) ↦₆₄ optVersionNegCap g.vn (some vn)) ∗ F) := by
      rw [optVersionNegotiationPBPinnedAt_eq A g.vn (s.sp + 4704#64) (some vn)]
      dsimp only [optVersionNegRest]
      ac_rfl
    refine SepWP.weaken_pre (Entails.of_eq hpre_eq) ?_
    refine SepWP.mono (step_vn_len_some_3191c_vregs_placed A s g.vn vn
      (((s.sp + 4704#64) ↦₆₄ optVersionNegCap g.vn (some vn)) ∗ F) hpc hrun hsp_align hlen_vn) ?_
    intro s' P' _ _ ⟨hv', hrun', hsp', htr', hx19', hx20', hx21', hx22', hx23', hx24', hx25', hx26', hx27', hx28', hfp', hP'⟩
    refine ⟨hv', hrun', hsp', htr', hx19', hx20', hx21', hx22', hx23', hx24', hx25', hx26', hx27', hx28', hfp', ?_⟩
    exact Entails.trans hP' (Entails.of_eq hpre_eq.symm)

theorem step_send_encode_from_vn_len_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (hle_stack : encodeToVecCalleeStackOf resStack ≤ spqrSendCalleeStack)
    (A : RustAlloc) (ext : String → Option (State → State))
    {roV1 : BitVec 64} {s0 s : State}
    (hChainLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 485)
      (withStepInv s0 (chainEncodedLenPinnedSpec A)))
    (hv1Len : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 484)
      (withStepInv s0 (v1StateEncodedLenRoPinnedSpec A roV1)))
    (hshim : subroutine_ok (spqrSendPlacedProg ext) (lsρ spqrRustNoAllocShimSym)
      (withStepInv s0 spqrSendShimStackSpec))
    (halloc : subroutine_ok (spqrSendPlacedProg ext) (lsρ spqrRustAllocSym)
      (withStepInv s0 (spqrSendRustAllocStackSpec A)))
    (hhandle : (spqrSendPlacedProg ext).externAt? (lsρ spqrHandleErrorSym) = some Rust.panicked)
    (hep_call : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 478)
      (withStepInv s0 (epochEncLenStackSpecOf resStack A)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (hmemcpy : subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy") etvMemcpyRegionSpec)
    (hed_call : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 457)
      (withStepInv s0 (encodeEpochDirectionExactSpecOf resStack A)))
    (hcp_call : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 453)
      (withStepInv s0 (encodeChainParamsExactSpecOf resStack A)))
    (hInnerAt6616 : ∀ is : V1State.InnerState,
      StepSendInnerStateAt6616Placed resStack A ext (lsρ spqrSendRoSym + 22#64) s0 is)
    (sp msg_cap v0 v_sp10 v_sp18 v_590 v_598 v_5a0 : BitVec 64)
    (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (hpos : 0 < pqRatchetStatePBEncodedLen st)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63) (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = spqrSendPlacedEntry + (if st.versionNegotiation.isSome then 4288#64 else 4364#64))
    (hrun : s.status = .Running) (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx22 : s.readReg64 .x22 = msg_cap)
    (hx24 : s.readReg64 .x24 = sp + 4704#64)
    (hx25 : s.readReg64 .x25 = optChainCap g.chain st.chain)
    (hx26 : s.readReg64 .x26 = optVersionNegCap g.vn st.versionNegotiation)
    (hx28 : s.readReg64 .x28 = sp + 4192#64)
    (hinv0 : StepInv s0 s)
    (hP : P = (pqRatchetStatePBPinnedAt A g (sp + 4704#64) st ∗
      (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
      ((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
      A.pool ∗ stackAt sp spqrSendCalleeStack ∗
      (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ v_sp10) ∗ ((sp + 24#64) ↦₆₄ v_sp18) ∗
      ((sp + 1424#64) ↦₆₄ v_590) ∗ ((sp + 1432#64) ↦₆₄ v_598) ∗ ((sp + 1440#64) ↦₆₄ v_5a0)) ∗ F)
    (hnext : ∀ (sm : State) (ptr w0 : BitVec 64),
      sm.pc = spqrSendPlacedEntry + 6216#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = optChainCap g.chain st.chain →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = sp + 4192#64 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((pqRatchetStatePBPinnedAt A g (sp + 4704#64) st ∗
          (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
          ((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
          vecU8At A (sp + 1424#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr
            (PqRatchetState.encodeRaw st) ∗
          A.pool ∗ stackAt sp spqrSendCalleeStack ∗
          (sp ↦₆₄ w0) ∗ ((sp + 16#64) ↦₆₄ optChainCap g.chain st.chain) ∗
          ((sp + 24#64) ↦₆₄ msg_cap)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  subst hP
  have halign_b : (s.sp &&& 15#64 == 0#64) = true := by rw [hsp, beq_iff_eq]; exact halign
  let F_vn : SepProp :=
    optChainPBPinnedAt A g.chain ((sp + 4704#64) + 48#64) st.chain ∗
      optPqRatchetInnerPBPinnedAt A g.inner ((sp + 4704#64) + 128#64) st.inner ∗
      (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
      ((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
      A.pool ∗ stackAt sp spqrSendCalleeStack ∗
      (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ v_sp10) ∗ ((sp + 24#64) ↦₆₄ v_sp18) ∗
      ((sp + 1424#64) ↦₆₄ v_590) ∗ ((sp + 1432#64) ↦₆₄ v_598) ∗ ((sp + 1440#64) ↦₆₄ v_5a0) ∗ F
  have hP_vn :
      (pqRatchetStatePBPinnedAt A g (sp + 4704#64) st ∗
        (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
        ((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
        A.pool ∗ stackAt sp spqrSendCalleeStack ∗
        (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ v_sp10) ∗ ((sp + 24#64) ↦₆₄ v_sp18) ∗
        ((sp + 1424#64) ↦₆₄ v_590) ∗ ((sp + 1432#64) ↦₆₄ v_598) ∗ ((sp + 1440#64) ↦₆₄ v_5a0)) ∗ F =
      optVersionNegotiationPBPinnedAt A g.vn (s.sp + 4704#64) st.versionNegotiation ∗ F_vn := by
    unfold pqRatchetStatePBPinnedAt
    rw [hsp]; dsimp only [F_vn]; ac_rfl
  rw [hP_vn]
  apply SepWPp.of_sepWP_cs (mid := spqrSendPlacedEntry + 4768#64)
  refine SepWP.mono
    (step_vn_len_unified_vregs_placed (ext := ext) A s g st F_vn hpc hrun halign_b hlen) ?_
  intro s1 P1 hpc1 _ ⟨hv1, hrun1, hsp1, htr1, hs1_19, hs1_20, hs1_21, hs1_22, hs1_23, hs1_24, hs1_25, hs1_26, hs1_27, hs1_28, hs1_fp, hP1⟩
  refine ⟨hv1, fun hinv_s1 => ?_⟩
  rw [hsp] at hsp1; rw [htr] at htr1
  rw [hx22] at hs1_22; rw [hx24] at hs1_24; rw [hx25] at hs1_25; rw [hx26] at hs1_26; rw [hx28] at hs1_28
  refine SepWPp.weaken_pre (Entails.trans hP1 (Entails.of_eq hP_vn.symm)) ?_
  refine step_send_encode_from_31afc_placed hres hle_stack A ext
    hChainLen hv1Len hshim halloc hhandle hep_call hvarint hmemcpy hed_call hcp_call hInnerAt6616
    sp msg_cap v0 v_sp10 v_sp18 v_590 v_598 v_5a0 g st hpos hlen halign
    hpc1 hrun1 hsp1 htr1 hs1_20 hs1_22 hs1_24 hs1_25 hs1_26 hs1_28 (hinv0.trans hinv_s1) rfl ?_
  intro sm ptr w0 hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m
  rw [hs1_19] at hm19; rw [hs1_21] at hm21; rw [hs1_23] at hm23
  rw [hs1_27] at hm27; rw [hs1_fp] at hmfp
  exact hnext sm ptr w0 hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m

/-- Self-contained `doReserveStack` version of `step_send_encode_from_vn_len_placed`, deriving all
`[local#1]` callee and allocator contracts from `hA : AllocContractsPlaced A ext` and
`hcl0 : LibsignalCodeLoaded lsmpl s0.mem`. -/
theorem step_send_encode_from_vn_len_self_contained_placed
    {A : RustAlloc} {ext : String → Option (State → State)} (hA : AllocContractsPlaced A ext)
    {s0 s : State} (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (sp msg_cap v0 v_sp10 v_sp18 v_590 v_598 v_5a0 : BitVec 64)
    (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (hpos : 0 < pqRatchetStatePBEncodedLen st)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63) (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = spqrSendPlacedEntry + (if st.versionNegotiation.isSome then 4288#64 else 4364#64))
    (hrun : s.status = .Running) (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx22 : s.readReg64 .x22 = msg_cap)
    (hx24 : s.readReg64 .x24 = sp + 4704#64)
    (hx25 : s.readReg64 .x25 = optChainCap g.chain st.chain)
    (hx26 : s.readReg64 .x26 = optVersionNegCap g.vn st.versionNegotiation)
    (hx28 : s.readReg64 .x28 = sp + 4192#64)
    (hinv0 : StepInv s0 s)
    (hP : P = (pqRatchetStatePBPinnedAt A g (sp + 4704#64) st ∗
      ((lsρ cliV1StateJtSym) ↦ᵣ v1StateJumpTableBytes) ∗
      ((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
      A.pool ∗ stackAt sp spqrSendCalleeStack ∗
      (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ v_sp10) ∗ ((sp + 24#64) ↦₆₄ v_sp18) ∗
      ((sp + 1424#64) ↦₆₄ v_590) ∗ ((sp + 1432#64) ↦₆₄ v_598) ∗ ((sp + 1440#64) ↦₆₄ v_5a0)) ∗ F)
    (hnext : ∀ (sm : State) (ptr w0 : BitVec 64),
      sm.pc = spqrSendPlacedEntry + 6216#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = optChainCap g.chain st.chain →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = sp + 4192#64 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((pqRatchetStatePBPinnedAt A g (sp + 4704#64) st ∗
          ((lsρ cliV1StateJtSym) ↦ᵣ v1StateJumpTableBytes) ∗
          ((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
          vecU8At A (sp + 1424#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr
            (PqRatchetState.encodeRaw st) ∗
          A.pool ∗ stackAt sp spqrSendCalleeStack ∗
          (sp ↦₆₄ w0) ∗ ((sp + 16#64) ↦₆₄ optChainCap g.chain st.chain) ∗
          ((sp + 24#64) ↦₆₄ msg_cap)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) :=
  step_send_encode_from_vn_len_placed (by decide) (by decide) A ext
    (spqrSend_chainEncodedLen1_ok_placed A ext s0 hcl0)
    (spqrSend_v1StateEncodedLen1_ok_placed A ext s0 hcl0)
    (spqrSend_shim_ok_enc_placed hA s0)
    (spqrSend_rustAlloc_ok_placed hA s0)
    (spqrSend_handle_alloc_error_placed hA)
    (spqrSend_epochEncodedLen1_ok_placed (by decide) A ext s0 hcl0)
    (spqrSend_encodeVarint_ok_placed hA hcl0)
    (spqrSend_etvMemcpy_ok_placed hA)
    (spqrSend_encodeEpochDirection_ok_placed hA hcl0)
    (spqrSend_encodeChainParams_ok_placed hA hcl0)
    (step_send_inner_at_6616_placed hA hcl0)
    sp msg_cap v0 v_sp10 v_sp18 v_590 v_598 v_5a0 g st hpos hlen halign
    hpc hrun hsp htr hx22 hx24 hx25 hx26 hx28 hinv0 hP hnext

/-- Self-contained `doReserveStackX` version of `step_send_encode_from_vn_len_placed`, deriving all
`[local#1]` callee and allocator contracts from `hA : AllocContractsPlaced A ext` and
`hcl0 : LibsignalCodeLoaded lsmpl s0.mem`. -/
theorem step_send_encode_from_vn_len_x_placed
    {A : RustAlloc} {ext : String → Option (State → State)} (hA : AllocContractsPlaced A ext)
    {s0 s : State} (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (sp msg_cap v0 v_sp10 v_sp18 v_590 v_598 v_5a0 : BitVec 64)
    (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (hpos : 0 < pqRatchetStatePBEncodedLen st)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63) (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = spqrSendPlacedEntry + (if st.versionNegotiation.isSome then 4288#64 else 4364#64))
    (hrun : s.status = .Running) (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx22 : s.readReg64 .x22 = msg_cap)
    (hx24 : s.readReg64 .x24 = sp + 4704#64)
    (hx25 : s.readReg64 .x25 = optChainCap g.chain st.chain)
    (hx26 : s.readReg64 .x26 = optVersionNegCap g.vn st.versionNegotiation)
    (hx28 : s.readReg64 .x28 = sp + 4192#64)
    (hinv0 : StepInv s0 s)
    (hP : P = (pqRatchetStatePBPinnedAt A g (sp + 4704#64) st ∗
      ((lsρ cliV1StateJtSym) ↦ᵣ v1StateJumpTableBytes) ∗
      ((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
      A.pool ∗ stackAt sp spqrSendCalleeStack ∗
      (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ v_sp10) ∗ ((sp + 24#64) ↦₆₄ v_sp18) ∗
      ((sp + 1424#64) ↦₆₄ v_590) ∗ ((sp + 1432#64) ↦₆₄ v_598) ∗ ((sp + 1440#64) ↦₆₄ v_5a0)) ∗ F)
    (hnext : ∀ (sm : State) (ptr w0 : BitVec 64),
      sm.pc = spqrSendPlacedEntry + 6216#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = optChainCap g.chain st.chain →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = sp + 4192#64 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((pqRatchetStatePBPinnedAt A g (sp + 4704#64) st ∗
          ((lsρ cliV1StateJtSym) ↦ᵣ v1StateJumpTableBytes) ∗
          ((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
          vecU8At A (sp + 1424#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr
            (PqRatchetState.encodeRaw st) ∗
          A.pool ∗ stackAt sp spqrSendCalleeStack ∗
          (sp ↦₆₄ w0) ∗ ((sp + 16#64) ↦₆₄ optChainCap g.chain st.chain) ∗
          ((sp + 24#64) ↦₆₄ msg_cap)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) :=
  step_send_encode_from_vn_len_placed (by decide) (by decide) A ext
    (spqrSend_chainEncodedLen1_ok_placed A ext s0 hcl0)
    (spqrSend_v1StateEncodedLen1_ok_placed A ext s0 hcl0)
    (spqrSend_shim_ok_enc_placed hA s0)
    (spqrSend_rustAlloc_ok_placed hA s0)
    (spqrSend_handle_alloc_error_placed hA)
    (spqrSend_epochEncodedLen1_ok_placed (by decide) A ext s0 hcl0)
    (spqrSend_encodeVarint_ok_x_placed hA hcl0)
    (spqrSend_etvMemcpy_ok_placed hA)
    (spqrSend_encodeEpochDirection_ok_x_placed hA hcl0)
    (spqrSend_encodeChainParams_ok_x_placed hA hcl0)
    (step_send_inner_at_6616_x_placed hA hcl0)
    sp msg_cap v0 v_sp10 v_sp18 v_590 v_598 v_5a0 g st hpos hlen halign
    hpc hrun hsp htr hx22 hx24 hx25 hx26 hx28 hinv0 hP hnext

end CryptoVerification.Cli.SpqrV1.Top.Send

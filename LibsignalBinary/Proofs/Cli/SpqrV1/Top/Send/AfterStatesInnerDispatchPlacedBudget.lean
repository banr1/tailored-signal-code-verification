/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesEncodedLenPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerHeaderPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsChunkedV1Budget
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsV1StateBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesEncodedLenBudget
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.Cli.SpqrV1.Auth.Encode1PlacedBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.ChainParams1PlacedBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.Ct1SentPlacedBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.EkSentCt1ReceivedPlacedBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.EpochDirection1PlacedBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.PolyDecoder1PlacedBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.PolyEncoder1PlacedBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesChunkedHeaderSentPlacedBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesChunkedPlacedBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesPolyPlacedBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked59_71PlacedBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked82_93PlacedBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesChainEncodePlacedBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerChunked1PlacedBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerChunked2PlacedBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerChunked3PlacedBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerChunked3aPlacedBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesVnEncodePlacedBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint2PlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.CalleeBridgesBudget
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.CalleeBridgesPlacedBudget
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Phase 3e Dispatch & Master `PqRatchetState` Encode (Block `427`)

Dispatches all 11 budget-threaded `V1State` variants at `+6616` and proves master `PqRatchetState`
serialization (`+4288/+4364 -> +6216`) charging the single output-buffer allocation.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerDispatchPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement libsignalSessionCode lsMemcpySym lsmpl lsρ)
open CryptoVerification.RustHeap (RustAlloc vecU8At)
open CryptoVerification.LibsignalTripleRatchet
  (doReserveStack doReserveStackX sessionMemcpyRegionSpec sessionMemcpySpec sessionShimSpec)
open CryptoVerification.LibsignalSpqrV1 (ChainPB PqRatchetState V1State VersionNegotiationPB)
open CryptoVerification.LibsignalSpqrV1.Proto (encodeOptMessage)
open CryptoVerification.SpqrV1.Alloc
  (spqrHandleErrorSym spqrRustAllocSym spqrRustNoAllocShimSym)
open CryptoVerification.SpqrV1.ProtoRepr
  (ct1SentEkReceivedPBEncodedLen ct1SentEkReceivedPBPinnedAt
   ct1SentPBEncodedLen ct1SentPBPinnedAt
   ct2SentPBEncodedLen ct2SentPBPinnedAt
   ekSentCt1ReceivedPBEncodedLen ekSentCt1ReceivedPBPinnedAt
   ekSentPBEncodedLen ekSentPBPinnedAt
   headerReceivedPBEncodedLen headerReceivedPBPinnedAt
   headerSentPBEncodedLen headerSentPBPinnedAt
   keysUnsampledPBEncodedLen keysUnsampledPBPinnedAt
   noHeaderReceivedPBEncodedLen noHeaderReceivedPBPinnedAt
   noneCap_add_two_beq_zero noneCap_add_two_bne_zero
   optChainPBPinnedAt optVersionNegotiationPBPinnedAt
   polynomialDecoderPBEncodedLen polynomialDecoderPBPinnedAt
   polynomialEncoderPBEncodedLen polynomialEncoderPBPinnedAt
   v1StateJumpTableBytes)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (hwVarintLen_bvShift_eq_ofNat_varintLen_norm hwVarintLen_eq_ofNat_varintLen_norm
   noneCap_add_one_beq_zero noneCap_add_one_bne_zero
   ofNat_countLeadingZeros_32 ofNat_countLeadingZeros_64
   ule_self_64 ule_zero_64 ult_self_64 ult_zero_64
   zeroExtend64_beq_zero32 zext64_truncate32)
open CryptoVerification.SpqrV1.Prost.EncodeToVec
  (PqRatchetStatePBGhost StepInv encodeToVecCalleeStackOf
   noneCap2_add_two_beq_zero noneCap2_add_two_bne_zero
   noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
   optChainCap optPqRatchetInnerCap optPqRatchetInnerPBPinnedAt optVersionNegCap
   optVersionNegotiationPBFieldEncodedLen pqRatchetStatePBEncodedLen pqRatchetStatePBPinnedAt
   withStepInv)
open CryptoVerification.SpqrV1.Top.Send
  (spqrSendCalleeStack spqrSendEncodeJumpTableBytes stackAt_spqrSendCallee_split_enc)
open CryptoVerification.Cli.SpqrV1.ProtoRepr (cliV1StateJtSym)
open CryptoVerification.Cli.SpqrV1.Top.Send.CodePlaced (blkPl_427_ρ)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits FitsEvents RustCliAllocBudget rustAllocEvents)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (noAllocShimSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyBudgetSpec sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget
  (chainEncodedLenPinnedSpec withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsChunkedV1Budget
  (chunkedCt1SampledEncodedLenPinnedSpec chunkedHeaderSentEncodedLenPinnedSpec)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsV1StateBudget
  (v1StateEncodedLenRoPinnedSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhaseBudget
  (authEncodeExactSpecOf encodeChainParamsExactSpecOf encodeEpochDirectionExactSpecOf
   encodeVarintExactSpecOf epochEncLenStackSpecOf etvMemcpyRegionSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.CalleeBridgesBudget
  (etv_authEncode_exact_of_spec etv_polyDecoderEncode_budget_exact_of_spec
   etv_polyEncoderEncode_budget_exact_of_spec)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.CalleeBridgesPlacedBudget
  (etv_encodeVarint_exact_of_fit_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsPlacedBudget
  (sepWPp_of_sepWP_cs_vm)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonBudget (leafEncLen16Spec)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonPlacedBudget
  (etvCt1SentBudgetExactSpecOf etvEkSentCt1ReceivedBudgetExactSpecOf
   etvPolyDecoderBudgetExactSpecOf etvPolyEncoderBudgetExactSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesEncodedLenBudget
  (spqrSendRustAllocNoOomStackSpec)
open LibsignalBinary.Proofs.Cli.SpqrV1.Auth.Encode1PlacedBudget
  (auth_encode_1_pinned_placed_ok auth_encode_1_pinned_placed_ok_x)
open LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.ChainParams1PlacedBudget
  (etv_encodeChainParams_1_exact_placed_ok etv_encodeChainParams_1_exact_placed_ok_x)
open LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.Ct1SentPlacedBudget
  (etv_ct1SentEncode_1_placed_ok etv_ct1SentEncode_1_placed_ok_x)
open LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.EkSentCt1ReceivedPlacedBudget
  (etv_ekSentCt1ReceivedEncode_1_placed_ok etv_ekSentCt1ReceivedEncode_1_placed_ok_x)
open LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.EpochDirection1PlacedBudget
  (etv_encodeEpochDirection_1_exact_placed_ok etv_encodeEpochDirection_1_exact_placed_ok_x)
open LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.PolyDecoder1PlacedBudget
  (encode_polyDecoder_1_exact_pinned_placed_ok_of_memcpy
   encode_polyDecoder_1_exact_pinned_placed_ok_of_memcpy_x)
open LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.PolyEncoder1PlacedBudget
  (encode_polyEncoder_1_exact_pinned_placed_ok_of_memcpy
   encode_polyEncoder_1_exact_pinned_placed_ok_of_memcpy_x)
open LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesChunkedHeaderSentPlacedBudget
  (chunkedHeaderSentEncodedLen_local1_pinned_placed_ok_ext)
open LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesChunkedPlacedBudget
  (chunkedCt1SampledEncodedLen_local1_pinned_placed_ok_ext)
open LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesPolyPlacedBudget
  (polynomialDecoderEncodedLen_local1_pinned_placed_ok_ext
   polynomialEncoderEncodedLen_local1_pinned_placed_ok_ext)
open LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked59_71PlacedBudget
  (ct2SentEncodedLen_local1_pinned_placed_ok_ext
   ekSentEncodedLen_local1_pinned_placed_ok_ext
   headerReceivedEncodedLen_local1_pinned_placed_ok_ext
   keysUnsampledEncodedLen_local1_pinned_placed_ok_ext
   noHeaderReceivedEncodedLen_local1_pinned_placed_ok_ext)
open LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked82_93PlacedBudget
  (ct1SentEkReceivedEncodedLen_local1_pinned_placed_ok_ext
   ct1SentEncodedLen_local1_pinned_placed_ok_ext
   ekSentCt1ReceivedEncodedLen_local1_pinned_placed_ok_ext
   headerSentEncodedLen_local1_pinned_placed_ok_ext)
open LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint2PlacedBudget
  (encode_varint2_fit_placed_ok encode_varint2_fit_placed_ok_x)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
  (AllocContractsPlaced spqrSendPlacedEntry spqrSendPlacedProg spqrSendRoSym)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesEncodedLenPlacedBudget
  (spqrSendShimVmStackSpec spqrSend_handle_alloc_error_placed spqrSend_rustAllocNoOom_ok_placed
   spqrSend_rustAlloc_ok_placed spqrSend_shim_ok_enc_placed
   step_send_alloc_31b94_placed step_send_chain_len_31afc_pool_placed
   step_send_inner_len_31b48_pool_placed
   step_vn_len_some_3191c_vregs_placed step_vn_len_unified_vregs_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerHeaderPlacedBudget
  (StepSendInnerStateAt6616Placed
   spqrSend_chainEncodedLen1_ok_placed spqrSend_epochEncodedLen1_ok_placed
   spqrSend_etvMemcpy_ok_placed spqrSend_subroutine_ok_placed_of_lscl
   spqrSend_subroutine_ok_placed_of_plain spqrSend_v1StateEncodedLen1_ok_placed
   step_send_inner_32058_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesVnEncodePlacedBudget
  (step_send_versionNeg_31be0_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesChainEncodePlacedBudget
  (step_send_chain_31e40_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerChunked1PlacedBudget
  (step_send_v1_ct1Acknowledged_at_6616_placed step_send_v1_ct1Received_at_6616_placed
   step_send_v1_ct1Sampled_at_6616_placed step_send_v1_ekSentCt1Received_at_6616_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerChunked2PlacedBudget
  (step_send_v1_headerSent_at_6616_placed step_send_v1_keysUnsampled_at_6616_placed
   step_send_v1_noHeaderReceived_at_6616_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerChunked3PlacedBudget
  (step_send_v1_ekReceivedCt1Sampled_at_6616_placed step_send_v1_keysSampled_at_6616_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerChunked3aPlacedBudget
  (step_send_v1_ct2Sampled_at_6616_placed step_send_v1_headerReceived_at_6616_placed)

variable [LibsignalPlacement]

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero spqrSendPlacedEntry blkPl_427_ρ
  zeroExtend64_beq_zero32
  ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 hwVarintLen_eq_ofNat_varintLen_norm
  hwVarintLen_bvShift_eq_ofNat_varintLen_norm zext64_truncate32
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  noneCap2_add_two_beq_zero noneCap2_add_two_bne_zero
  noneCap_add_two_beq_zero noneCap_add_two_bne_zero
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
  ule_zero_64 ult_zero_64 ule_self_64 ult_self_64

/-! ## Re-Exports from `AfterStatesInnerHeaderPlacedBudget` & `AfterStatesEncodedLenPlacedBudget` -/

export LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerHeaderPlacedBudget
  (spqrSend_subroutine_ok_placed_of_plain spqrSend_subroutine_ok_placed_of_lscl
   spqrSend_etvMemcpy_ok_placed spqrSend_chainEncodedLen1_ok_placed
   spqrSend_v1StateEncodedLen1_ok_placed)

export LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerHeaderPlacedBudget
  (spqrSend_epochEncodedLen1_ok_placed)

export LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesEncodedLenPlacedBudget
  (spqrSend_shim_ok_enc_placed spqrSend_rustAlloc_ok_placed spqrSend_rustAllocNoOom_ok_placed
   spqrSend_handle_alloc_error_placed
   step_vn_len_some_3191c_vregs_placed)

export LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesEncodedLenPlacedBudget
  (step_vn_len_unified_vregs_placed)

/-! ## 1. `[local#1]` / `[local#3]` Callee `subroutine_ok` Bridges for `spqr::send` (Block `427`) -/

private theorem hookSat_noAllocShim_of_alloc {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext) :
    HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec := by
  rcases hA.shim with ⟨f, hf, hsat⟩
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hsat x R s0 hrun hpre hsp with ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [sessionShimBudgetSpec, sessionShimSpec, noAllocShimSpec,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.noAllocShimBudgetSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost
    rw [satisfies_pure_sepConj]
    exact ⟨⟨hpost.2.1, hpost.1⟩, hpost.2.2⟩
  · exact Or.inr hrest

private theorem hookSat_sessionMemcpyRegionBudget_of_alloc {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced M A lim ext) :
    HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec := by
  obtain ⟨f, hf, hsat⟩ := hA.session_memcpy 0
  refine ⟨f, hf, fun ⟨dst, src, srcBytes⟩ R s0 hrun hpre hal => ?_⟩
  have hpre' : s0.mem ⊨ (sessionMemcpyBudgetSpec 0).pre (dst, src, srcBytes) s0 ∗ R := by
    dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyBudgetSpec,
      sessionMemcpyRegionSpec, memcpyRegionSpec, sessionMemcpySpec, libcMemcpySpec, stackAt] at hpre ⊢
    rw [ProofLib.memRegion_zero]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  obtain ⟨hF, hsym, ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩⟩ :=
    hsat (dst, src, srcBytes) R s0 hrun hpre' hal
  · refine ⟨hF, hsym, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyBudgetSpec,
      sessionMemcpyRegionSpec, sessionMemcpySpec, stackAt] at hpost ⊢
    rw [ProofLib.memRegion_zero] at hpost
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
  · exact (ProofLib.allowPanic_not_exited hpan).elim
  · exact (ProofLib.allowPanic_not_exited hex).elim
  · exact (ProofLib.allowPanic_not_exited hoom).elim

theorem spqrSend_encodeVarint_ok_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext) {s0 : State}
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf doReserveStack A lim)) :=
  etv_encodeVarint_exact_of_fit_placed (by decide)
    (spqrSend_subroutine_ok_placed_of_lscl hcl0
      (encode_varint2_fit_placed_ok hA.handle_error (hookSat_noAllocShim_of_alloc hA)
        hA.alloc hA.realloc))

theorem spqrSend_encodeVarint_ok_x_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext) {s0 : State}
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf doReserveStackX A lim)) :=
  etv_encodeVarint_exact_of_fit_placed (by decide)
    (spqrSend_subroutine_ok_placed_of_lscl hcl0
      (encode_varint2_fit_placed_ok_x hA.handle_error (hookSat_noAllocShim_of_alloc hA)
        hA.alloc hA.realloc))

theorem spqrSend_encodeChainParams_ok_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext) {s0 : State}
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 453)
      (withStepInv s0 (encodeChainParamsExactSpecOf doReserveStack A lim)) :=
  spqrSend_subroutine_ok_placed_of_lscl hcl0
    (etv_encodeChainParams_1_exact_placed_ok hA.handle_error (hookSat_noAllocShim_of_alloc hA)
      hA.alloc hA.realloc)

theorem spqrSend_encodeChainParams_ok_x_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext) {s0 : State}
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 453)
      (withStepInv s0 (encodeChainParamsExactSpecOf doReserveStackX A lim)) :=
  spqrSend_subroutine_ok_placed_of_lscl hcl0
    (etv_encodeChainParams_1_exact_placed_ok_x hA.handle_error (hookSat_noAllocShim_of_alloc hA)
      hA.alloc hA.realloc)

theorem spqrSend_encodeEpochDirection_ok_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext) {s0 : State}
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 457)
      (withStepInv s0 (encodeEpochDirectionExactSpecOf doReserveStack A lim)) :=
  spqrSend_subroutine_ok_placed_of_lscl hcl0
    (etv_encodeEpochDirection_1_exact_placed_ok hA.handle_error (hookSat_noAllocShim_of_alloc hA)
      hA.alloc hA.realloc (hookSat_sessionMemcpyRegionBudget_of_alloc hA))

theorem spqrSend_encodeEpochDirection_ok_x_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext) {s0 : State}
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 457)
      (withStepInv s0 (encodeEpochDirectionExactSpecOf doReserveStackX A lim)) :=
  spqrSend_subroutine_ok_placed_of_lscl hcl0
    (etv_encodeEpochDirection_1_exact_placed_ok_x hA.handle_error (hookSat_noAllocShim_of_alloc hA)
      hA.alloc hA.realloc (hookSat_sessionMemcpyRegionBudget_of_alloc hA))

theorem spqrSend_authEncode_ok_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext) {s0 : State}
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 454)
      (withStepInv s0 (authEncodeExactSpecOf doReserveStack A lim)) :=
  etv_authEncode_exact_of_spec (by decide)
    (spqrSend_subroutine_ok_placed_of_lscl hcl0
      (auth_encode_1_pinned_placed_ok hA.handle_error (hookSat_noAllocShim_of_alloc hA)
        hA.alloc hA.realloc (hookSat_sessionMemcpyRegionBudget_of_alloc hA)))

theorem spqrSend_authEncode_ok_x_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext) {s0 : State}
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 454)
      (withStepInv s0 (authEncodeExactSpecOf doReserveStackX A lim)) :=
  etv_authEncode_exact_of_spec (by decide)
    (spqrSend_subroutine_ok_placed_of_lscl hcl0
      (auth_encode_1_pinned_placed_ok_x hA.handle_error (hookSat_noAllocShim_of_alloc hA)
        hA.alloc hA.realloc (hookSat_sessionMemcpyRegionBudget_of_alloc hA)))

theorem spqrSend_polyEncoderEncode_ok_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext) {s0 : State}
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 456)
      (withStepInv s0 (etvPolyEncoderBudgetExactSpecOf doReserveStack A lim)) :=
  etv_polyEncoderEncode_budget_exact_of_spec
    (spqrSend_subroutine_ok_placed_of_lscl hcl0
      (encode_polyEncoder_1_exact_pinned_placed_ok_of_memcpy
        (hookSat_sessionMemcpyRegionBudget_of_alloc hA)))

theorem spqrSend_polyEncoderEncode_ok_x_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext) {s0 : State}
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 456)
      (withStepInv s0 (etvPolyEncoderBudgetExactSpecOf doReserveStackX A lim)) :=
  etv_polyEncoderEncode_budget_exact_of_spec
    (spqrSend_subroutine_ok_placed_of_lscl hcl0
      (encode_polyEncoder_1_exact_pinned_placed_ok_of_memcpy_x
        (hookSat_sessionMemcpyRegionBudget_of_alloc hA)))

theorem spqrSend_polyDecoderEncode_ok_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext) {s0 : State}
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 455)
      (withStepInv s0 (etvPolyDecoderBudgetExactSpecOf doReserveStack A lim)) :=
  etv_polyDecoderEncode_budget_exact_of_spec
    (spqrSend_subroutine_ok_placed_of_lscl hcl0
      (encode_polyDecoder_1_exact_pinned_placed_ok_of_memcpy
        (hookSat_sessionMemcpyRegionBudget_of_alloc hA)))

theorem spqrSend_polyDecoderEncode_ok_x_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext) {s0 : State}
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 455)
      (withStepInv s0 (etvPolyDecoderBudgetExactSpecOf doReserveStackX A lim)) :=
  etv_polyDecoderEncode_budget_exact_of_spec
    (spqrSend_subroutine_ok_placed_of_lscl hcl0
      (encode_polyDecoder_1_exact_pinned_placed_ok_of_memcpy_x
        (hookSat_sessionMemcpyRegionBudget_of_alloc hA)))

theorem spqrSend_ekSentCt1ReceivedEncode_ok_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext) {s0 : State}
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 458)
      (withStepInv s0 (etvEkSentCt1ReceivedBudgetExactSpecOf doReserveStack A lim)) :=
  spqrSend_subroutine_ok_placed_of_lscl hcl0
    (etv_ekSentCt1ReceivedEncode_1_placed_ok hA.handle_error (hookSat_noAllocShim_of_alloc hA)
      hA.alloc hA.realloc (hookSat_sessionMemcpyRegionBudget_of_alloc hA))

theorem spqrSend_ekSentCt1ReceivedEncode_ok_x_placed {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext) {s0 : State}
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 458)
      (withStepInv s0 (etvEkSentCt1ReceivedBudgetExactSpecOf doReserveStackX A lim)) :=
  spqrSend_subroutine_ok_placed_of_lscl hcl0
    (etv_ekSentCt1ReceivedEncode_1_placed_ok_x hA.handle_error (hookSat_noAllocShim_of_alloc hA)
      hA.alloc hA.realloc (hookSat_sessionMemcpyRegionBudget_of_alloc hA))

theorem spqrSend_ct1SentEncode_ok_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext) {s0 : State}
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 459)
      (withStepInv s0 (etvCt1SentBudgetExactSpecOf doReserveStack A lim)) :=
  spqrSend_subroutine_ok_placed_of_lscl hcl0
    (etv_ct1SentEncode_1_placed_ok hA.handle_error (hookSat_noAllocShim_of_alloc hA)
      hA.alloc hA.realloc (hookSat_sessionMemcpyRegionBudget_of_alloc hA))

theorem spqrSend_ct1SentEncode_ok_x_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext) {s0 : State}
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 459)
      (withStepInv s0 (etvCt1SentBudgetExactSpecOf doReserveStackX A lim)) :=
  spqrSend_subroutine_ok_placed_of_lscl hcl0
    (etv_ct1SentEncode_1_placed_ok_x hA.handle_error (hookSat_noAllocShim_of_alloc hA)
      hA.alloc hA.realloc (hookSat_sessionMemcpyRegionBudget_of_alloc hA))

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
      (withStepInv s0 (chunkedHeaderSentEncodedLenPinnedSpec A)) :=
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
      (withStepInv s0
        (leafEncLen16Spec (ekSentCt1ReceivedPBPinnedAt A) ekSentCt1ReceivedPBEncodedLen)) :=
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
      (withStepInv s0
        (leafEncLen16Spec (noHeaderReceivedPBPinnedAt A) noHeaderReceivedPBEncodedLen)) :=
  spqrSend_subroutine_ok_placed_of_plain hcl0
    (noHeaderReceivedEncodedLen_local1_pinned_placed_ok_ext A ext)

theorem spqrSend_headerReceivedEncodedLen_ok_placed (A : RustAlloc)
    (ext : String → Option (State → State)) (s0 : State)
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 482)
      (withStepInv s0
        (leafEncLen16Spec (headerReceivedPBPinnedAt A) headerReceivedPBEncodedLen)) :=
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
      (withStepInv s0
        (leafEncLen16Spec (ct1SentEkReceivedPBPinnedAt A) ct1SentEkReceivedPBEncodedLen)) :=
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
      (withStepInv s0
        (leafEncLen16Spec (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen)) :=
  spqrSend_subroutine_ok_placed_of_plain hcl0
    (polynomialDecoderEncodedLen_local1_pinned_placed_ok_ext A ext)

theorem spqrSend_polyEncoderEncodedLen_ok_placed (A : RustAlloc)
    (ext : String → Option (State → State)) (s0 : State)
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 480)
      (withStepInv s0
        (leafEncLen16Spec (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen)) :=
  spqrSend_subroutine_ok_placed_of_plain hcl0
    (polynomialEncoderEncodedLen_local1_pinned_placed_ok_ext A ext)

/-! ## 2. Unified `StepSendInnerStateAt6616Placed` Dispatch across All 11 Variants -/

theorem step_send_inner_at_6616_of_variants_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (ext : String → Option (State → State))
    {roBase : BitVec 64} {s0 : State}
    (hkuLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 479)
      (withStepInv s0
        (leafEncLen16Spec (keysUnsampledPBPinnedAt A.repAlloc) keysUnsampledPBEncodedLen)))
    (hhs16Len : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 492)
      (withStepInv s0
        (leafEncLen16Spec (headerSentPBPinnedAt A.repAlloc) headerSentPBEncodedLen)))
    (hhsLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 495)
      (withStepInv s0 (chunkedHeaderSentEncodedLenPinnedSpec A.repAlloc)))
    (hekSentLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 496)
      (withStepInv s0 (leafEncLen16Spec (ekSentPBPinnedAt A.repAlloc) ekSentPBEncodedLen)))
    (hekLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 499)
      (withStepInv s0
        (leafEncLen16Spec (ekSentCt1ReceivedPBPinnedAt A.repAlloc) ekSentCt1ReceivedPBEncodedLen)))
    (hnhrLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 500)
      (withStepInv s0
        (leafEncLen16Spec (noHeaderReceivedPBPinnedAt A.repAlloc) noHeaderReceivedPBEncodedLen)))
    (hhrLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 482)
      (withStepInv s0
        (leafEncLen16Spec (headerReceivedPBPinnedAt A.repAlloc) headerReceivedPBEncodedLen)))
    (hct1SampledLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 486)
      (withStepInv s0 (chunkedCt1SampledEncodedLenPinnedSpec A.repAlloc)))
    (hct1SentEkLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 469)
      (withStepInv s0
        (leafEncLen16Spec (ct1SentEkReceivedPBPinnedAt A.repAlloc) ct1SentEkReceivedPBEncodedLen)))
    (hct1SentLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 487)
      (withStepInv s0 (leafEncLen16Spec (ct1SentPBPinnedAt A.repAlloc) ct1SentPBEncodedLen)))
    (hct2Len : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 470)
      (withStepInv s0 (leafEncLen16Spec (ct2SentPBPinnedAt A.repAlloc) ct2SentPBEncodedLen)))
    (hpolyEncLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 480)
      (withStepInv s0
        (leafEncLen16Spec (polynomialEncoderPBPinnedAt A.repAlloc) polynomialEncoderPBEncodedLen)))
    (hpolyDecLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 493)
      (withStepInv s0
        (leafEncLen16Spec (polynomialDecoderPBPinnedAt A.repAlloc) polynomialDecoderPBEncodedLen)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hauthEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 454)
      (withStepInv s0 (authEncodeExactSpecOf resStack A lim)))
    (hmemcpy : subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy") etvMemcpyRegionSpec)
    (hekEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 458)
      (withStepInv s0 (etvEkSentCt1ReceivedBudgetExactSpecOf resStack A lim)))
    (hct1SentEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 459)
      (withStepInv s0 (etvCt1SentBudgetExactSpecOf resStack A lim)))
    (hpolyEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 456)
      (withStepInv s0 (etvPolyEncoderBudgetExactSpecOf resStack A lim)))
    (hpolyDec : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 455)
      (withStepInv s0 (etvPolyDecoderBudgetExactSpecOf resStack A lim)))
    (is : V1State.InnerState) :
    StepSendInnerStateAt6616Placed resStack A lim st0 ext roBase s0 is := by
  cases is with
  | keysUnsampled v =>
    exact step_send_v1_keysUnsampled_at_6616_placed hres A lim st0 ext hkuLen hvarint hauthEnc v
  | keysSampled v =>
    exact step_send_v1_keysSampled_at_6616_placed hres A lim st0 ext
      hhs16Len hpolyEncLen hvarint hauthEnc hmemcpy hpolyEnc v
  | headerSent v =>
    exact step_send_v1_headerSent_at_6616_placed hres A lim st0 ext
      hhsLen hekSentLen hvarint hauthEnc hmemcpy hpolyEnc hpolyDec v
  | ct1Received v =>
    exact step_send_v1_ct1Received_at_6616_placed hres A lim st0 ext
      hekLen hpolyEncLen hvarint hekEnc hpolyEnc v
  | ekSentCt1Received v =>
    exact step_send_v1_ekSentCt1Received_at_6616_placed hres A lim st0 ext
      hekLen hpolyDecLen hvarint hekEnc hpolyDec v
  | noHeaderReceived v =>
    exact step_send_v1_noHeaderReceived_at_6616_placed hres A lim st0 ext
      hnhrLen hpolyDecLen hvarint hauthEnc hpolyDec v
  | headerReceived v =>
    exact step_send_v1_headerReceived_at_6616_placed hres A lim st0 ext
      hhrLen hpolyDecLen hvarint hauthEnc hmemcpy hpolyDec v
  | ct1Sampled v =>
    exact step_send_v1_ct1Sampled_at_6616_placed hres A lim st0 ext
      hct1SampledLen hvarint hct1SentEnc hpolyEnc hpolyDec v
  | ekReceivedCt1Sampled v =>
    exact step_send_v1_ekReceivedCt1Sampled_at_6616_placed hres A lim st0 ext
      hct1SentEkLen hpolyEncLen hvarint hauthEnc hmemcpy hpolyEnc v
  | ct1Acknowledged v =>
    exact step_send_v1_ct1Acknowledged_at_6616_placed hres A lim st0 ext
      hct1SentLen hpolyDecLen hvarint hct1SentEnc hpolyDec v
  | ct2Sampled v =>
    exact step_send_v1_ct2Sampled_at_6616_placed hres A lim st0 ext
      hct2Len hpolyEncLen hvarint hauthEnc hpolyEnc v

theorem step_send_inner_at_6616_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st0 : M.σ} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext)
    {roBase : BitVec 64} {s0 : State} (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (is : V1State.InnerState) :
    StepSendInnerStateAt6616Placed doReserveStack A lim st0 ext roBase s0 is :=
  step_send_inner_at_6616_of_variants_placed (by decide) A lim st0 ext
    (spqrSend_keysUnsampledEncodedLen_ok_placed A.repAlloc ext s0 hcl0)
    (spqrSend_headerSentEncodedLen_ok_placed A.repAlloc ext s0 hcl0)
    (spqrSend_chunkedHeaderSentEncodedLen_ok_placed A.repAlloc ext s0 hcl0)
    (spqrSend_ekSentEncodedLen_ok_placed A.repAlloc ext s0 hcl0)
    (spqrSend_ekSentCt1ReceivedEncodedLen_ok_placed A.repAlloc ext s0 hcl0)
    (spqrSend_noHeaderReceivedEncodedLen_ok_placed A.repAlloc ext s0 hcl0)
    (spqrSend_headerReceivedEncodedLen_ok_placed A.repAlloc ext s0 hcl0)
    (spqrSend_chunkedCt1SampledEncodedLen_ok_placed A.repAlloc ext s0 hcl0)
    (spqrSend_ct1SentEkReceivedEncodedLen_ok_placed A.repAlloc ext s0 hcl0)
    (spqrSend_ct1SentEncodedLen_ok_placed A.repAlloc ext s0 hcl0)
    (spqrSend_ct2SentEncodedLen_ok_placed A.repAlloc ext s0 hcl0)
    (spqrSend_polyEncoderEncodedLen_ok_placed A.repAlloc ext s0 hcl0)
    (spqrSend_polyDecoderEncodedLen_ok_placed A.repAlloc ext s0 hcl0)
    (spqrSend_encodeVarint_ok_placed hA hcl0)
    (spqrSend_authEncode_ok_placed hA hcl0)
    (spqrSend_etvMemcpy_ok_placed hA)
    (spqrSend_ekSentCt1ReceivedEncode_ok_placed hA hcl0)
    (spqrSend_ct1SentEncode_ok_placed hA hcl0)
    (spqrSend_polyEncoderEncode_ok_placed hA hcl0)
    (spqrSend_polyDecoderEncode_ok_placed hA hcl0)
    is

theorem step_send_inner_at_6616_x_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st0 : M.σ} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext)
    {roBase : BitVec 64} {s0 : State} (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (is : V1State.InnerState) :
    StepSendInnerStateAt6616Placed doReserveStackX A lim st0 ext roBase s0 is :=
  step_send_inner_at_6616_of_variants_placed (by decide) A lim st0 ext
    (spqrSend_keysUnsampledEncodedLen_ok_placed A.repAlloc ext s0 hcl0)
    (spqrSend_headerSentEncodedLen_ok_placed A.repAlloc ext s0 hcl0)
    (spqrSend_chunkedHeaderSentEncodedLen_ok_placed A.repAlloc ext s0 hcl0)
    (spqrSend_ekSentEncodedLen_ok_placed A.repAlloc ext s0 hcl0)
    (spqrSend_ekSentCt1ReceivedEncodedLen_ok_placed A.repAlloc ext s0 hcl0)
    (spqrSend_noHeaderReceivedEncodedLen_ok_placed A.repAlloc ext s0 hcl0)
    (spqrSend_headerReceivedEncodedLen_ok_placed A.repAlloc ext s0 hcl0)
    (spqrSend_chunkedCt1SampledEncodedLen_ok_placed A.repAlloc ext s0 hcl0)
    (spqrSend_ct1SentEkReceivedEncodedLen_ok_placed A.repAlloc ext s0 hcl0)
    (spqrSend_ct1SentEncodedLen_ok_placed A.repAlloc ext s0 hcl0)
    (spqrSend_ct2SentEncodedLen_ok_placed A.repAlloc ext s0 hcl0)
    (spqrSend_polyEncoderEncodedLen_ok_placed A.repAlloc ext s0 hcl0)
    (spqrSend_polyDecoderEncodedLen_ok_placed A.repAlloc ext s0 hcl0)
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
`vecU8At A.repAlloc (sp + 1424#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr (PqRatchetState.encodeRaw st)`
while preserving `A.pool lim st0`. -/
theorem step_send_encode_fields_31be0_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (ext : String → Option (State → State))
    {roV1 : BitVec 64} {s0 s : State}
    (hChainLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 485)
      (withStepInv s0 (chainEncodedLenPinnedSpec A.repAlloc)))
    (hv1Len : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 484)
      (withStepInv s0 (v1StateEncodedLenRoPinnedSpec A.repAlloc roV1)))
    (hep_call : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 478)
      (withStepInv s0 (epochEncLenStackSpecOf resStack A.repAlloc)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hmemcpy : subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy") etvMemcpyRegionSpec)
    (hed_call : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 457)
      (withStepInv s0 (encodeEpochDirectionExactSpecOf resStack A lim)))
    (hcp_call : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 453)
      (withStepInv s0 (encodeChainParamsExactSpecOf resStack A lim)))
    (hInnerAt6616 : ∀ is : V1State.InnerState,
      StepSendInnerStateAt6616Placed resStack A lim st0 ext (lsρ spqrSendRoSym + 22#64) s0 is)
    (sp ptr v0 : BitVec 64) (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63) (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc =
      (if st.versionNegotiation.isSome then spqrSendPlacedEntry + 4996#64
       else spqrSendPlacedEntry + 5604#64))
    (hrun : s.status = .Running) (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx0 : st.versionNegotiation.isSome → s.readReg64 .x0 = ptr)
    (hx20 : s.readReg64 .x20 = optPqRatchetInnerCap g.inner st.inner)
    (hx25 : s.readReg64 .x25 = optChainCap g.chain st.chain)
    (hx28 : s.readReg64 .x28 = sp + 4192#64)
    (hinv0 : StepInv s0 s)
    (hP : P = (pqRatchetStatePBPinnedAt A.repAlloc g (sp + 4704#64) st ∗
      (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
      ((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
      vecU8At A.repAlloc (sp + 1424#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr [] ∗
      A.pool lim st0 s ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗
      (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ optChainCap g.chain st.chain)) ∗ F)
    (hnext : ∀ (sm : State) (w0 : BitVec 64),
      sm.pc = spqrSendPlacedEntry + 6216#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = optChainCap g.chain st.chain →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = sp + 4192#64 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((pqRatchetStatePBPinnedAt A.repAlloc g (sp + 4704#64) st ∗
          (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
          ((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
          vecU8At A.repAlloc (sp + 1424#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr
            (PqRatchetState.encodeRaw st) ∗
          A.pool lim st0 sm ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗
          (sp ↦₆₄ w0) ∗ ((sp + 16#64) ↦₆₄ optChainCap g.chain st.chain)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  subst hP
  refine step_send_versionNeg_31be0_placed A lim st0 ext hvarint hmemcpy hcp_call
    sp ptr v0 g st hlen halign
    (F := (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
      ((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗ F)
    hpc hrun hsp htr hx0 hx25 hx28 hinv0 (by sep_ac_rfl) ?_
  intro s1 w0 hpcs1 hruns1 hsps1 htrs1 hs1_19 hs1_20 hs1_21 hs1_23 hs1_25 hs1_27 hs1_28 hs1_fp hinv_s1
  rw [hx20] at hs1_20
  refine step_send_chain_31e40_placed hres A lim st0 ext hChainLen hep_call hvarint hmemcpy hed_call hcp_call
    sp ptr g st hlen halign
    (F := (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
      ((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
      (sp ↦₆₄ w0) ∗ F)
    hpcs1 hruns1 hsps1 htrs1 hs1_25 hinv_s1 (by sep_ac_rfl) ?_
  intro s2 hpcs2 hruns2 hsps2 htrs2 hs2_19 hs2_20 hs2_21 hs2_23 hs2_25 hs2_27 hs2_28 hs2_fp hinv_s2
  rw [hs1_19] at hs2_19; rw [hs1_20] at hs2_20; rw [hs1_21] at hs2_21; rw [hs1_23] at hs2_23
  rw [hs1_27] at hs2_27; rw [hs1_28] at hs2_28; rw [hs1_fp] at hs2_fp
  refine step_send_inner_32058_placed hres A lim st0 ext hv1Len hvarint hInnerAt6616
    sp ptr (optChainCap g.chain st.chain) g st hlen halign
    (F := (sp ↦₆₄ w0) ∗ F)
    hpcs2 hruns2 hsps2 htrs2 hs2_20 hs2_25 hinv_s2 (by sep_ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m
  rw [hs2_19] at hm19; rw [hs2_21] at hm21; rw [hs2_23] at hm23
  rw [hs2_27] at hm27; rw [hs2_28] at hm28; rw [hs2_fp] at hmfp
  refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (hnext sm w0 hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m)

/-- Step `spqrSendPlacedEntry + 4768#64 -> spqrSendPlacedEntry + 6216#64`:
computes `Option<Chain>::encoded_len`, `Option<pq_ratchet_state::Inner>::encoded_len`, allocates
the output buffer via `__rust_alloc` (charging `rustAllocEvents (pqRatchetStatePBEncodedLen st) 1`),
and serializes all 3 fields of `st : PqRatchetState`. -/
theorem step_send_encode_from_31afc_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (hle_stack : encodeToVecCalleeStackOf resStack ≤ spqrSendCalleeStack)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (ext : String → Option (State → State))
    {roV1 : BitVec 64} {s0 s1 : State}
    (hChainLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 485)
      (withStepInv s0 (chainEncodedLenPinnedSpec A.repAlloc)))
    (hv1Len : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 484)
      (withStepInv s0 (v1StateEncodedLenRoPinnedSpec A.repAlloc roV1)))
    (hshim : subroutine_ok (spqrSendPlacedProg ext) (lsρ spqrRustNoAllocShimSym)
      (withStepInv s0 spqrSendShimVmStackSpec))
    (halloc : subroutine_ok (spqrSendPlacedProg ext) (lsρ spqrRustAllocSym)
      (withStepInv s0 (spqrSendRustAllocNoOomStackSpec M A lim)))
    (hep_call : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 478)
      (withStepInv s0 (epochEncLenStackSpecOf resStack A.repAlloc)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hmemcpy : subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy") etvMemcpyRegionSpec)
    (hed_call : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 457)
      (withStepInv s0 (encodeEpochDirectionExactSpecOf resStack A lim)))
    (hcp_call : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 453)
      (withStepInv s0 (encodeChainParamsExactSpecOf resStack A lim)))
    (hInnerAt6616 : ∀ (st_in : M.σ) (is : V1State.InnerState),
      StepSendInnerStateAt6616Placed resStack A lim st_in ext (lsρ spqrSendRoSym + 22#64) s0 is)
    (sp msg_cap v0 v_sp10 v_sp18 v_590 v_598 v_5a0 : BitVec 64)
    (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (hpos : 0 < pqRatchetStatePBEncodedLen st)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63)
    (hfits : FitsEvents M lim st0 (rustAllocEvents (pqRatchetStatePBEncodedLen st) 1))
    (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
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
    (hP : P = (pqRatchetStatePBPinnedAt A.repAlloc g (sp + 4704#64) st ∗
      (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
      ((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
      A.pool lim st0 s1 ∗ stackAt sp spqrSendCalleeStack ∗
      (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ v_sp10) ∗ ((sp + 24#64) ↦₆₄ v_sp18) ∗
      ((sp + 1424#64) ↦₆₄ v_590) ∗ ((sp + 1432#64) ↦₆₄ v_598) ∗ ((sp + 1440#64) ↦₆₄ v_5a0)) ∗ F)
    (hnext : ∀ (sm : State) (ptr w0 : BitVec 64),
      sm.pc = spqrSendPlacedEntry + 6216#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s1.readReg64 .x19 → sm.readReg64 .x21 = s1.readReg64 .x21 →
      sm.readReg64 .x23 = s1.readReg64 .x23 → sm.readReg64 .x25 = optChainCap g.chain st.chain →
      sm.readReg64 .x27 = s1.readReg64 .x27 → sm.readReg64 .x28 = sp + 4192#64 →
      sm.readReg64 .fp = s1.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((pqRatchetStatePBPinnedAt A.repAlloc g (sp + 4704#64) st ∗
          (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
          ((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
          vecU8At A.repAlloc (sp + 1424#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr
            (PqRatchetState.encodeRaw st) ∗
          A.pool lim (M.stepEvents (rustAllocEvents (pqRatchetStatePBEncodedLen st) 1) st0) sm ∗
          stackAt sp spqrSendCalleeStack ∗
          (sp ↦₆₄ w0) ∗ ((sp + 16#64) ↦₆₄ optChainCap g.chain st.chain) ∗
          ((sp + 24#64) ↦₆₄ msg_cap)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s1 P Q Qp oom := by
  subst hP
  let F_stack := memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack)
    (spqrSendCalleeStack - encodeToVecCalleeStackOf resStack)
  refine step_send_chain_len_31afc_pool_placed A lim st0 ext hChainLen sp msg_cap v_sp18 g st hlen halign
    (F := (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
      ((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
      (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ v_sp10) ∗
      ((sp + 1424#64) ↦₆₄ v_590) ∗ ((sp + 1432#64) ↦₆₄ v_598) ∗ ((sp + 1440#64) ↦₆₄ v_5a0) ∗ F)
    hpc hrun hsp htr hx20 hx22 hx24 hx25 hinv1 (by sep_ac_rfl) ?_
  intro s2 hpcs2 hruns2 hsps2 htrs2 hs2_19 hs2_21 hs2_22 hs2_23 hs2_24 hs2_25 hs2_26 hs2_27 hs2_28 hs2_fp hinv2
  rw [hx26] at hs2_26; rw [hx28] at hs2_28
  refine step_send_inner_len_31b48_pool_placed A lim st0 ext hv1Len sp g st hlen halign
    (F := ((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
      (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ v_sp10) ∗ ((sp + 24#64) ↦₆₄ msg_cap) ∗
      ((sp + 1424#64) ↦₆₄ v_590) ∗ ((sp + 1432#64) ↦₆₄ v_598) ∗ ((sp + 1440#64) ↦₆₄ v_5a0) ∗ F)
    hpcs2 hruns2 hsps2 htrs2 hs2_22 hs2_24 hinv2 (by sep_ac_rfl) ?_
  intro s3 hpcs3 hruns3 hsps3 htrs3 hs3_19 hs3_20 hs3_21 _ hs3_23 hs3_24 hs3_25 hs3_26 hs3_27 hs3_28 hs3_fp hinv3
  rw [hs2_19] at hs3_19; rw [hs2_21] at hs3_21; rw [hs2_23] at hs3_23; rw [hs2_25] at hs3_25
  rw [hs2_26] at hs3_26; rw [hs2_27] at hs3_27; rw [hs2_28] at hs3_28; rw [hs2_fp] at hs3_fp
  refine step_send_alloc_31b94_placed A lim st0 ext hshim halloc
    sp v_sp10 v_590 v_598 v_5a0 g st hpos hlen hfits halign
    (F := (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
      ((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
      (sp ↦₆₄ v0) ∗ ((sp + 24#64) ↦₆₄ msg_cap) ∗ F)
    hpcs3 hruns3 hsps3 htrs3 hs3_24 hs3_25 hs3_26 hinv3 (by sep_ac_rfl) ?_
  intro s4 ptr hpcs4 hruns4 hsps4 htrs4 hs4_0 hs4_19 hs4_20 hs4_21 _ hs4_23 _ hs4_25 _ hs4_27 hs4_28 hs4_fp hinv4
  rw [hs3_19] at hs4_19; rw [hs3_20] at hs4_20; rw [hs3_21] at hs4_21; rw [hs3_23] at hs4_23
  rw [hs3_27] at hs4_27; rw [hs3_28] at hs4_28; rw [hs3_fp] at hs4_fp
  refine step_send_encode_fields_31be0_placed hres A lim
    (M.stepEvents (rustAllocEvents (pqRatchetStatePBEncodedLen st) 1) st0) ext
    hChainLen hv1Len hep_call hvarint hmemcpy hed_call hcp_call
    (hInnerAt6616 (M.stepEvents (rustAllocEvents (pqRatchetStatePBEncodedLen st) 1) st0))
    sp ptr v0 g st hlen halign
    (F := F_stack ∗ ((sp + 24#64) ↦₆₄ msg_cap) ∗ F)
    hpcs4 hruns4 hsps4 htrs4 (fun _ => hs4_0) hs4_20 hs4_25 hs4_28 hinv4
    (by rw [stackAt_spqrSendCallee_split_enc sp (encodeToVecCalleeStackOf resStack) hle_stack]
        dsimp only [F_stack]; sep_ac_rfl) ?_
  intro sm w0 hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m
  rw [hs4_19] at hm19; rw [hs4_21] at hm21; rw [hs4_23] at hm23
  rw [hs4_27] at hm27; rw [hs4_fp] at hmfp
  refine SepWPp.weaken_pre ?_
    (hnext sm ptr w0 hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m)
  rw [stackAt_spqrSendCallee_split_enc sp (encodeToVecCalleeStackOf resStack) hle_stack]
  dsimp only [F_stack]
  exact Entails.of_eq (by sep_ac_rfl)

/-- Master `PqRatchetState` serialization step in `spqr::send` (`+4288 / +4364 -> +6216`):
from the entry of `Option<VersionNegotiation>::encoded_len`, computes all 3 field lengths,
allocates the output `Vec<u8>` buffer via `__rust_alloc` (charging
`rustAllocEvents (pqRatchetStatePBEncodedLen st) 1`), and serializes all 3 fields of
`st : PqRatchetState` into `vecU8At A.repAlloc (sp + 1424#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr (PqRatchetState.encodeRaw st)`. -/
theorem step_send_encode_from_vn_len_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (hle_stack : encodeToVecCalleeStackOf resStack ≤ spqrSendCalleeStack)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (ext : String → Option (State → State))
    {roV1 : BitVec 64} {s0 s : State}
    (hChainLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 485)
      (withStepInv s0 (chainEncodedLenPinnedSpec A.repAlloc)))
    (hv1Len : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 484)
      (withStepInv s0 (v1StateEncodedLenRoPinnedSpec A.repAlloc roV1)))
    (hshim : subroutine_ok (spqrSendPlacedProg ext) (lsρ spqrRustNoAllocShimSym)
      (withStepInv s0 spqrSendShimVmStackSpec))
    (halloc : subroutine_ok (spqrSendPlacedProg ext) (lsρ spqrRustAllocSym)
      (withStepInv s0 (spqrSendRustAllocNoOomStackSpec M A lim)))
    (hep_call : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 478)
      (withStepInv s0 (epochEncLenStackSpecOf resStack A.repAlloc)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hmemcpy : subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy") etvMemcpyRegionSpec)
    (hed_call : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 457)
      (withStepInv s0 (encodeEpochDirectionExactSpecOf resStack A lim)))
    (hcp_call : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 453)
      (withStepInv s0 (encodeChainParamsExactSpecOf resStack A lim)))
    (hInnerAt6616 : ∀ (st_in : M.σ) (is : V1State.InnerState),
      StepSendInnerStateAt6616Placed resStack A lim st_in ext (lsρ spqrSendRoSym + 22#64) s0 is)
    (sp msg_cap v0 v_sp10 v_sp18 v_590 v_598 v_5a0 : BitVec 64)
    (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (hpos : 0 < pqRatchetStatePBEncodedLen st)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63)
    (hfits : FitsEvents M lim st0 (rustAllocEvents (pqRatchetStatePBEncodedLen st) 1))
    (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = spqrSendPlacedEntry + (if st.versionNegotiation.isSome then 4288#64 else 4364#64))
    (hrun : s.status = .Running) (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx22 : s.readReg64 .x22 = msg_cap)
    (hx24 : s.readReg64 .x24 = sp + 4704#64)
    (hx25 : s.readReg64 .x25 = optChainCap g.chain st.chain)
    (hx26 : s.readReg64 .x26 = optVersionNegCap g.vn st.versionNegotiation)
    (hx28 : s.readReg64 .x28 = sp + 4192#64)
    (hinv0 : StepInv s0 s)
    (hP : P = (pqRatchetStatePBPinnedAt A.repAlloc g (sp + 4704#64) st ∗
      (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
      ((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
      A.pool lim st0 s ∗ stackAt sp spqrSendCalleeStack ∗
      (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ v_sp10) ∗ ((sp + 24#64) ↦₆₄ v_sp18) ∗
      ((sp + 1424#64) ↦₆₄ v_590) ∗ ((sp + 1432#64) ↦₆₄ v_598) ∗ ((sp + 1440#64) ↦₆₄ v_5a0)) ∗ F)
    (hnext : ∀ (sm : State) (ptr w0 : BitVec 64),
      sm.pc = spqrSendPlacedEntry + 6216#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = optChainCap g.chain st.chain →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = sp + 4192#64 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((pqRatchetStatePBPinnedAt A.repAlloc g (sp + 4704#64) st ∗
          (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
          ((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
          vecU8At A.repAlloc (sp + 1424#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr
            (PqRatchetState.encodeRaw st) ∗
          A.pool lim (M.stepEvents (rustAllocEvents (pqRatchetStatePBEncodedLen st) 1) st0) sm ∗
          stackAt sp spqrSendCalleeStack ∗
          (sp ↦₆₄ w0) ∗ ((sp + 16#64) ↦₆₄ optChainCap g.chain st.chain) ∗
          ((sp + 24#64) ↦₆₄ msg_cap)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  subst hP
  have halign_b : (s.sp &&& 15#64 == 0#64) = true := by rw [hsp, beq_iff_eq]; exact halign
  let F_vn : SepProp :=
    optChainPBPinnedAt A.repAlloc g.chain ((sp + 4704#64) + 48#64) st.chain ∗
      optPqRatchetInnerPBPinnedAt A.repAlloc g.inner ((sp + 4704#64) + 128#64) st.inner ∗
      (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
      ((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
      A.pool lim st0 s ∗ stackAt sp spqrSendCalleeStack ∗
      (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ v_sp10) ∗ ((sp + 24#64) ↦₆₄ v_sp18) ∗
      ((sp + 1424#64) ↦₆₄ v_590) ∗ ((sp + 1432#64) ↦₆₄ v_598) ∗ ((sp + 1440#64) ↦₆₄ v_5a0) ∗ F
  have hP_vn :
      (pqRatchetStatePBPinnedAt A.repAlloc g (sp + 4704#64) st ∗
        (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
        ((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
        A.pool lim st0 s ∗ stackAt sp spqrSendCalleeStack ∗
        (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ v_sp10) ∗ ((sp + 24#64) ↦₆₄ v_sp18) ∗
        ((sp + 1424#64) ↦₆₄ v_590) ∗ ((sp + 1432#64) ↦₆₄ v_598) ∗ ((sp + 1440#64) ↦₆₄ v_5a0)) ∗ F =
      optVersionNegotiationPBPinnedAt A.repAlloc g.vn (s.sp + 4704#64) st.versionNegotiation ∗ F_vn := by
    unfold pqRatchetStatePBPinnedAt
    rw [hsp]; dsimp only [F_vn]; sep_ac_rfl
  rw [hP_vn]
  apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 4768#64)
  refine SepWP.mono
    (step_vn_len_unified_vregs_placed (ext := ext) A s g st F_vn hpc hrun halign_b hlen) ?_
  intro s1 P1 hpc1 _ ⟨hvm1, hv1, hrun1, hsp1, htr1, hs1_19, hs1_20, hs1_21, hs1_22, hs1_23, hs1_24, hs1_25, hs1_26, hs1_27, hs1_28, hs1_fp, hP1⟩
  refine ⟨hvm1, hv1, fun hinv_s1 => ?_⟩
  rw [hsp] at hsp1; rw [htr] at htr1
  rw [hx22] at hs1_22; rw [hx24] at hs1_24; rw [hx25] at hs1_25; rw [hx26] at hs1_26; rw [hx28] at hs1_28
  have hpool : A.pool lim st0 s = A.pool lim st0 s1 := (A.pool_of_vmPreserved hinv_s1.2).symm
  have hP1' : P1 ⊢
      (pqRatchetStatePBPinnedAt A.repAlloc g (sp + 4704#64) st ∗
        (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
        ((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
        A.pool lim st0 s1 ∗ stackAt sp spqrSendCalleeStack ∗
        (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ v_sp10) ∗ ((sp + 24#64) ↦₆₄ v_sp18) ∗
        ((sp + 1424#64) ↦₆₄ v_590) ∗ ((sp + 1432#64) ↦₆₄ v_598) ∗ ((sp + 1440#64) ↦₆₄ v_5a0)) ∗ F := by
    refine Entails.trans hP1 ?_
    rw [← hP_vn, hpool]
    exact Entails.refl _
  refine SepWPp.weaken_pre hP1' ?_
  refine step_send_encode_from_31afc_placed hres hle_stack A lim st0 ext
    hChainLen hv1Len hshim halloc hep_call hvarint hmemcpy hed_call hcp_call hInnerAt6616
    sp msg_cap v0 v_sp10 v_sp18 v_590 v_598 v_5a0 g st hpos hlen hfits halign
    hpc1 hrun1 hsp1 htr1 hs1_20 hs1_22 hs1_24 hs1_25 hs1_26 hs1_28 (hinv0.trans hinv_s1.1) rfl ?_
  intro sm ptr w0 hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m
  rw [hs1_19] at hm19; rw [hs1_21] at hm21; rw [hs1_23] at hm23
  rw [hs1_27] at hm27; rw [hs1_fp] at hmfp
  exact hnext sm ptr w0 hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m

/-- Self-contained `doReserveStack` version of `step_send_encode_from_vn_len_placed`, deriving all
`[local#1]` / `[local#3]` callee and allocator contracts from `hA : AllocContractsPlaced M A lim ext`
and `hcl0 : LibsignalCodeLoaded lsmpl s0.mem`. -/
theorem step_send_encode_from_vn_len_self_contained_placed
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st0 : M.σ}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced M A lim ext)
    {s0 s : State} (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (sp msg_cap v0 v_sp10 v_sp18 v_590 v_598 v_5a0 : BitVec 64)
    (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (hpos : 0 < pqRatchetStatePBEncodedLen st)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63)
    (hfits : FitsEvents M lim st0 (rustAllocEvents (pqRatchetStatePBEncodedLen st) 1))
    (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = spqrSendPlacedEntry + (if st.versionNegotiation.isSome then 4288#64 else 4364#64))
    (hrun : s.status = .Running) (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx22 : s.readReg64 .x22 = msg_cap)
    (hx24 : s.readReg64 .x24 = sp + 4704#64)
    (hx25 : s.readReg64 .x25 = optChainCap g.chain st.chain)
    (hx26 : s.readReg64 .x26 = optVersionNegCap g.vn st.versionNegotiation)
    (hx28 : s.readReg64 .x28 = sp + 4192#64)
    (hinv0 : StepInv s0 s)
    (hP : P = (pqRatchetStatePBPinnedAt A.repAlloc g (sp + 4704#64) st ∗
      ((lsρ cliV1StateJtSym) ↦ᵣ v1StateJumpTableBytes) ∗
      ((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
      A.pool lim st0 s ∗ stackAt sp spqrSendCalleeStack ∗
      (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ v_sp10) ∗ ((sp + 24#64) ↦₆₄ v_sp18) ∗
      ((sp + 1424#64) ↦₆₄ v_590) ∗ ((sp + 1432#64) ↦₆₄ v_598) ∗ ((sp + 1440#64) ↦₆₄ v_5a0)) ∗ F)
    (hnext : ∀ (sm : State) (ptr w0 : BitVec 64),
      sm.pc = spqrSendPlacedEntry + 6216#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = optChainCap g.chain st.chain →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = sp + 4192#64 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((pqRatchetStatePBPinnedAt A.repAlloc g (sp + 4704#64) st ∗
          ((lsρ cliV1StateJtSym) ↦ᵣ v1StateJumpTableBytes) ∗
          ((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
          vecU8At A.repAlloc (sp + 1424#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr
            (PqRatchetState.encodeRaw st) ∗
          A.pool lim (M.stepEvents (rustAllocEvents (pqRatchetStatePBEncodedLen st) 1) st0) sm ∗
          stackAt sp spqrSendCalleeStack ∗
          (sp ↦₆₄ w0) ∗ ((sp + 16#64) ↦₆₄ optChainCap g.chain st.chain) ∗
          ((sp + 24#64) ↦₆₄ msg_cap)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom :=
  step_send_encode_from_vn_len_placed (by decide) (by decide) A lim st0 ext
    (spqrSend_chainEncodedLen1_ok_placed A.repAlloc ext s0 hcl0)
    (spqrSend_v1StateEncodedLen1_ok_placed A.repAlloc ext s0 hcl0)
    (spqrSend_shim_ok_enc_placed hA s0)
    (spqrSend_rustAllocNoOom_ok_placed hA s0)
    (spqrSend_epochEncodedLen1_ok_placed (by decide) A.repAlloc ext s0 hcl0)
    (spqrSend_encodeVarint_ok_placed hA hcl0)
    (spqrSend_etvMemcpy_ok_placed hA)
    (spqrSend_encodeEpochDirection_ok_placed hA hcl0)
    (spqrSend_encodeChainParams_ok_placed hA hcl0)
    (fun _ => step_send_inner_at_6616_placed hA hcl0)
    sp msg_cap v0 v_sp10 v_sp18 v_590 v_598 v_5a0 g st hpos hlen hfits halign
    hpc hrun hsp htr hx22 hx24 hx25 hx26 hx28 hinv0 hP hnext

/-- Self-contained `doReserveStackX` version of `step_send_encode_from_vn_len_placed`, deriving all
`[local#1]` / `[local#3]` callee and allocator contracts from `hA : AllocContractsPlaced M A lim ext`
and `hcl0 : LibsignalCodeLoaded lsmpl s0.mem`. -/
theorem step_send_encode_from_vn_len_x_placed
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st0 : M.σ}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced M A lim ext)
    {s0 s : State} (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (sp msg_cap v0 v_sp10 v_sp18 v_590 v_598 v_5a0 : BitVec 64)
    (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (hpos : 0 < pqRatchetStatePBEncodedLen st)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63)
    (hfits : FitsEvents M lim st0 (rustAllocEvents (pqRatchetStatePBEncodedLen st) 1))
    (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = spqrSendPlacedEntry + (if st.versionNegotiation.isSome then 4288#64 else 4364#64))
    (hrun : s.status = .Running) (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx22 : s.readReg64 .x22 = msg_cap)
    (hx24 : s.readReg64 .x24 = sp + 4704#64)
    (hx25 : s.readReg64 .x25 = optChainCap g.chain st.chain)
    (hx26 : s.readReg64 .x26 = optVersionNegCap g.vn st.versionNegotiation)
    (hx28 : s.readReg64 .x28 = sp + 4192#64)
    (hinv0 : StepInv s0 s)
    (hP : P = (pqRatchetStatePBPinnedAt A.repAlloc g (sp + 4704#64) st ∗
      ((lsρ cliV1StateJtSym) ↦ᵣ v1StateJumpTableBytes) ∗
      ((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
      A.pool lim st0 s ∗ stackAt sp spqrSendCalleeStack ∗
      (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ v_sp10) ∗ ((sp + 24#64) ↦₆₄ v_sp18) ∗
      ((sp + 1424#64) ↦₆₄ v_590) ∗ ((sp + 1432#64) ↦₆₄ v_598) ∗ ((sp + 1440#64) ↦₆₄ v_5a0)) ∗ F)
    (hnext : ∀ (sm : State) (ptr w0 : BitVec 64),
      sm.pc = spqrSendPlacedEntry + 6216#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = optChainCap g.chain st.chain →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = sp + 4192#64 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((pqRatchetStatePBPinnedAt A.repAlloc g (sp + 4704#64) st ∗
          ((lsρ cliV1StateJtSym) ↦ᵣ v1StateJumpTableBytes) ∗
          ((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
          vecU8At A.repAlloc (sp + 1424#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr
            (PqRatchetState.encodeRaw st) ∗
          A.pool lim (M.stepEvents (rustAllocEvents (pqRatchetStatePBEncodedLen st) 1) st0) sm ∗
          stackAt sp spqrSendCalleeStack ∗
          (sp ↦₆₄ w0) ∗ ((sp + 16#64) ↦₆₄ optChainCap g.chain st.chain) ∗
          ((sp + 24#64) ↦₆₄ msg_cap)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom :=
  step_send_encode_from_vn_len_placed (by decide) (by decide) A lim st0 ext
    (spqrSend_chainEncodedLen1_ok_placed A.repAlloc ext s0 hcl0)
    (spqrSend_v1StateEncodedLen1_ok_placed A.repAlloc ext s0 hcl0)
    (spqrSend_shim_ok_enc_placed hA s0)
    (spqrSend_rustAllocNoOom_ok_placed hA s0)
    (spqrSend_epochEncodedLen1_ok_placed (by decide) A.repAlloc ext s0 hcl0)
    (spqrSend_encodeVarint_ok_x_placed hA hcl0)
    (spqrSend_etvMemcpy_ok_placed hA)
    (spqrSend_encodeEpochDirection_ok_x_placed hA hcl0)
    (spqrSend_encodeChainParams_ok_x_placed hA hcl0)
    (fun _ => step_send_inner_at_6616_x_placed hA hcl0)
    sp msg_cap v0 v_sp10 v_sp18 v_590 v_598 v_5a0 g st hpos hlen hfits halign
    hpc hrun hsp htr hx22 hx24 hx25 hx26 hx28 hinv0 hP hnext

end LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerDispatchPlacedBudget

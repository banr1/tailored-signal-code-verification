/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.ProofPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked2PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked3PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked3aPlacedBudget
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesChunkedHeaderSentBudget
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesPolyBudget
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked59_71Budget
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked82_93Budget
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `[LibsignalPlacement]` Final Composition for `PqRatchetState::encode_to_vec` (`Block 426`)

Discharges the remaining 7 `StepInnerStateAt1880Placed` jump-table variant bridges (`idx = 0, 1, 2, 5, 6, 8, 10`),
builds the 11-variant dispatcher `step_encodeToVec_inner_at_1880_all_placed`, and proves the
budget-threaded `[LibsignalPlacement]` `subroutine_ok` contracts for `PqRatchetState::encode_to_vec`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.FinalPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (Crypto)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget
   rustCliAllocBudgetSpec rustCliReallocBudgetSpec)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement extract_withLsCodeLoaded
   lsMemcpySym lsmpl withLsCodeLoaded)
open CryptoVerification.LibsignalTripleRatchet
  (doReserveStack doReserveStackX tripleRatchetExterns)
open CryptoVerification.LibsignalSpqrV1 (V1State)
open CryptoVerification.SpqrV1.Alloc
  (spqrHandleErrorSym spqrRustAllocSym spqrRustNoAllocShimSym spqrRustReallocSym)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (noAllocShimSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)
open CryptoVerification.SpqrV1.ProtoRepr
  (chunkedCt1SampledPBEncodedLen chunkedCt1SampledPBPinnedAt
   chunkedHeaderSentPBEncodedLen chunkedHeaderSentPBPinnedAt
   ct1SentEkReceivedPBEncodedLen ct1SentEkReceivedPBPinnedAt
   ct1SentPBEncodedLen ct1SentPBPinnedAt
   ct2SentPBEncodedLen ct2SentPBPinnedAt
   ekSentCt1ReceivedPBEncodedLen ekSentCt1ReceivedPBPinnedAt
   ekSentPBEncodedLen ekSentPBPinnedAt
   headerReceivedPBEncodedLen headerReceivedPBPinnedAt
   headerSentPBEncodedLen headerSentPBPinnedAt
   keysUnsampledPBEncodedLen keysUnsampledPBPinnedAt
   noHeaderReceivedPBEncodedLen noHeaderReceivedPBPinnedAt
   polynomialDecoderPBEncodedLen polynomialDecoderPBPinnedAt
   polynomialEncoderPBEncodedLen polynomialEncoderPBPinnedAt
   v1StateInnerPBPinnedAt)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (hwVarintLen_bvShift_eq_ofNat_varintLen_norm hwVarintLen_eq_ofNat_varintLen_norm
   noneCap_add_one_beq_zero noneCap_add_one_bne_zero
   ofNat_countLeadingZeros_32 ofNat_countLeadingZeros_64
   ule_self_64 ule_zero_64 ult_self_64 ult_zero_64
   zeroExtend64_beq_zero32 zext64_truncate32)
open CryptoVerification.SpqrV1.Prost.EncodeToVec
  (StepInv blkPC_426 blkPl_426
   encodeToVecJumpTableBytesAt encodeToVecJumpTableBytes_eq etvJumpTableRoSym
   noneCap2_add_two_beq_zero noneCap2_add_two_bne_zero
   noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
   noneCap_add_two_beq_zero noneCap_add_two_bne_zero
   v1StateInnerCap withStepInv)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget (withLsRoLoaded)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesChunkedHeaderSentBudget
  (chunkedCt1SampledEncodedLen_local2_pinned_placed_ok_ext
   chunkedHeaderSentEncodedLen_local2_pinned_placed_ok_ext)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesPolyBudget
  (polynomialDecoderEncodedLen_local2_pinned_placed_ok_ext
   polynomialEncoderEncodedLen_local2_pinned_placed_ok_ext)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked59_71Budget
  (ct2SentEncodedLen_local2_pinned_placed_ok_ext
   ekSentEncodedLen_local2_pinned_placed_ok_ext
   headerReceivedEncodedLen_local2_pinned_placed_ok_ext
   keysUnsampledEncodedLen_local2_pinned_placed_ok_ext
   noHeaderReceivedEncodedLen_local2_pinned_placed_ok_ext)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked82_93Budget
  (ct1SentEkReceivedEncodedLen_local2_pinned_placed_ok_ext
   ct1SentEncodedLen_local2_pinned_placed_ok_ext
   ekSentCt1ReceivedEncodedLen_local2_pinned_placed_ok_ext
   headerSentEncodedLen_local2_pinned_placed_ok_ext)
open LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBaseBudget (authEncodePinnedSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParamsBaseBudget
  (encodeChainParamsSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EpochDirectionBaseBudget
  (encodeEpochDirectionPinnedSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.UnchunkedBaseBudget
  (ct1SentEncodePinnedSpecOf ekSentCt1ReceivedEncodePinnedSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyDecoderExactBudget
  (encodePolyDecoderExactSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyEncoderExactBudget
  (encodePolyEncoderExactSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsBudget
  (pqRatchetStateEncodeToVecNoOomSpecOf pqRatchetStateEncodeToVecPinnedNoOomSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsPlacedBudget
  (sepWP_done_vm sepWPp_of_sepWP_cs_vm subroutine_ok_withStepInv_lscl)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhaseBudget
  (authEncodeExactSpecOf encodeChainParamsExactSpecOf encodeEpochDirectionExactSpecOf
   encodeVarintExactSpecOf etvMemcpyRegionSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.CalleeBridgesBudget
  (etv_authEncode_exact_of_spec etv_encodeChainParams_exact_of_spec
   etv_encodeEpochDirection_exact_of_spec
   etv_polyDecoderEncode_budget_exact_of_spec etv_polyEncoderEncode_budget_exact_of_spec)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.CalleeBridgesPlacedBudget
  (etv_encodeVarint_placed_ok etv_encodeVarint_placed_ok_x etv_memcpy_placed_ok
   etv_subroutine_ok_placed_of_lscl etv_subroutine_ok_placed_of_plain)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonBudget
  (leafEncLen16Spec leafEncLen48Spec)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonPlacedBudget
  (etvCt1SentBudgetExactSpecOf etvEkSentCt1ReceivedBudgetExactSpecOf
   etvPolyDecoderBudgetExactSpecOf etvPolyEncoderBudgetExactSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked2PlacedBudget
  (step_encodeToVec_v1_headerSent_placed
   step_encodeToVec_v1_keysUnsampled_placed
   step_encodeToVec_v1_noHeaderReceived_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked3PlacedBudget
  (step_encodeToVec_v1_ekReceivedCt1Sampled_placed
   step_encodeToVec_v1_keysSampled_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked3aPlacedBudget
  (step_encodeToVec_v1_ct2Sampled_placed
   step_encodeToVec_v1_headerReceived_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.ProofPlacedBudget
  (StepInnerStateAt1880Placed
   pqRatchetStateEncodeToVecRoNoOomPlacedSpecOf
   pqRatchetStateEncodeToVecRoPinnedNoOomPlacedSpecOf
   pqRatchetStateEncodeToVecRoPinnedPlacedSpecOf
   pqRatchetStateEncodeToVecRoPlacedSpecOf
   pqRatchetStateEncodeToVec_noOom_placed_ok_of_variants
   pqRatchetStateEncodeToVec_pinned_noOom_placed_ok_of_variants
   pqRatchetStateEncodeToVec_pinned_placed_ok_of_variants
   pqRatchetStateEncodeToVec_placed_ok_of_pinned
   pqRatchetStateEncodeToVec_placed_ok_of_variants
   pqRatchetStateEncodeToVec_ro_noOom_placed_ok_of_pinned
   pqRatchetStateEncodeToVec_ro_pinned_noOom_placed_ok_of_variants
   pqRatchetStateEncodeToVec_ro_pinned_placed_ok_of_variants
   pqRatchetStateEncodeToVec_ro_placed_ok_of_variants
   step_encodeToVec_v1_ct1Acknowledged_at_1880_placed
   step_encodeToVec_v1_ct1Received_at_1880_placed
   step_encodeToVec_v1_ct1Sampled_at_1880_placed
   step_encodeToVec_v1_ekSentCt1Received_at_1880_placed)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  zeroExtend64_beq_zero32
  ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 hwVarintLen_eq_ofNat_varintLen_norm
  hwVarintLen_bvShift_eq_ofNat_varintLen_norm zext64_truncate32
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  noneCap2_add_two_beq_zero noneCap2_add_two_bne_zero
  noneCap_add_two_beq_zero noneCap_add_two_bne_zero
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
  ule_zero_64 ult_zero_64 ule_self_64 ult_self_64

/-! ## 1. Remaining 7 `StepInnerStateAt1880Placed` Variant Bridges (`V1StateChunked{2,3,3a}PlacedBudget`) -/

private theorem cap_xor_top_eq_of_eq {cap x : BitVec 64}
    (hx : x < 0x8000000000000000#64) (hcap : cap = 0x8000000000000000#64 + x) :
    cap ^^^ 0x8000000000000000#64 = x := by
  bv_bits

/-- Execute the `.rodata` half-word (`↦₁₆ᵣ`) jump-table dispatch at `+1880 .. +1896` (`Block 426`)
from `(blkPl_426).base + 1880#64` to `(blkPl_426).base + off`, preserving `StepInvVm`. -/
local macro "etv_jump16_placed " off:num s1:term:max idx:term:max hx8:term:max : tactic =>
  `(tactic| (
    have _hx8 : ($s1).readReg64 .x8 = $idx := $hx8
    generalize _hro : (blkPl_426).ρ etvJumpTableRoSym = roBase at *
    dsimp only [encodeToVecJumpTableBytesAt]
    apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + BitVec.ofNat 64 $off)
    wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    subst _hro))

theorem step_encodeToVec_v1_keysUnsampled_at_1880_placed [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (H : String → Option (State → State)) {s0 : State}
    (hkuLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 400)
      (withStepInv s0 (leafEncLen16Spec (keysUnsampledPBPinnedAt A.repAlloc) keysUnsampledPBEncodedLen)))
    (hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hauthEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 314)
      (withStepInv s0 (authEncodeExactSpecOf resStack A lim)))
    (v : V1State.Chunked.KeysUnsampled) :
    StepInnerStateAt1880Placed resStack A lim st H s0 (.keysUnsampled v) := by
  intro a sp cap ptr g bs hv_len hfit halign ret s P F Q Qp oom
    hpc hrun hsp htr hx8 hx9 hx20 hx21 hx28 hinv0 hP hnext
  subst hP
  have hx8' : s.readReg64 .x8 = 0#64 := by
    rw [hx8, show v1StateInnerCap g (.keysUnsampled v) = 0x8000000000000000#64 from rfl,
      cap_xor_top_eq_of_eq (cap := 0x8000000000000000#64) (x := 0#64) (by decide) rfl]
    decide
  clear hx8
  rw [encodeToVecJumpTableBytes_eq ((blkPl_426).ρ etvJumpTableRoSym)]
  etv_jump16_placed 1896 s 0#64 hx8'
  intro hinv1
  have h136 : (a + 128#64) + 8#64 = a + 136#64 := by bv_omega
  dsimp only [v1StateInnerPBPinnedAt]
  rw [h136]
  refine step_encodeToVec_v1_keysUnsampled_placed hres A lim st H hkuLen hvarint hauthEnc
    a sp cap ptr g.a.gKeysUnsampled v bs hv_len hfit halign
    (F := ((a + 128#64) ↦₆₄ 0x8000000000000000#64) ∗ memRegion (a + 128#64 + 64#64) 160 ∗
      encodeToVecJumpTableBytesAt ((blkPl_426).ρ etvJumpTableRoSym) ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1.1)
    (by dsimp only [encodeToVecJumpTableBytesAt]; rw [← A.pool_of_vmPreserved hinv1.2]; sep_ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hx27m hfpm hinv_m
  simp only [arm64_norm] at hx27m hfpm
  refine SepWPp.weaken_pre ?_ (hnext sm hpcm hrunm hspm htrm hx27m hfpm hinv_m)
  dsimp only [v1StateInnerPBPinnedAt]
  rw [h136, encodeToVecJumpTableBytes_eq ((blkPl_426).ρ etvJumpTableRoSym)]
  exact Entails.of_eq (by sep_ac_rfl)

theorem step_encodeToVec_v1_keysSampled_at_1880_placed [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (H : String → Option (State → State)) {s0 : State}
    (hhsLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 411)
      (withStepInv s0 (leafEncLen16Spec (headerSentPBPinnedAt A.repAlloc) headerSentPBEncodedLen)))
    (hpolyEncLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 401)
      (withStepInv s0 (leafEncLen16Spec (polynomialEncoderPBPinnedAt A.repAlloc) polynomialEncoderPBEncodedLen)))
    (hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hauthEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 314)
      (withStepInv s0 (authEncodeExactSpecOf resStack A lim)))
    (hmemcpy : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) ((blkPl_426).ρ "memcpy") etvMemcpyRegionSpec)
    (hpolyEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 316)
      (withStepInv s0 (etvPolyEncoderBudgetExactSpecOf resStack A lim)))
    (v : V1State.Chunked.KeysSampled) :
    StepInnerStateAt1880Placed resStack A lim st H s0 (.keysSampled v) := by
  intro a sp cap ptr g bs hv_len hfit halign ret s P F Q Qp oom
    hpc hrun hsp htr hx8 hx9 hx20 hx21 hx28 hinv0 hP hnext
  subst hP
  have hx8' : s.readReg64 .x8 = 1#64 := by
    rw [hx8, show v1StateInnerCap g (.keysSampled v) = 0x8000000000000001#64 from rfl,
      cap_xor_top_eq_of_eq (cap := 0x8000000000000001#64) (x := 1#64) (by decide) rfl]
    decide
  clear hx8
  rw [encodeToVecJumpTableBytes_eq ((blkPl_426).ρ etvJumpTableRoSym)]
  etv_jump16_placed 2748 s 1#64 hx8'
  intro hinv1
  have h136 : (a + 128#64) + 8#64 = a + 136#64 := by bv_omega
  have h240 : (a + 128#64) + 112#64 = a + 240#64 := by bv_omega
  dsimp only [v1StateInnerPBPinnedAt]
  rw [h136, h240]
  refine step_encodeToVec_v1_keysSampled_placed hres A lim st H hhsLen hpolyEncLen hvarint hauthEnc hmemcpy hpolyEnc
    a sp cap ptr g.a.gKeysSampled v bs hv_len hfit halign
    (F := ((a + 128#64) ↦₆₄ 0x8000000000000001#64) ∗ memRegion (a + 128#64 + 168#64) 56 ∗
      encodeToVecJumpTableBytesAt ((blkPl_426).ρ etvJumpTableRoSym) ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1.1)
    (by dsimp only [encodeToVecJumpTableBytesAt]; rw [← A.pool_of_vmPreserved hinv1.2]; sep_ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hx27m hfpm hinv_m
  simp only [arm64_norm] at hx27m hfpm
  refine SepWPp.weaken_pre ?_ (hnext sm hpcm hrunm hspm htrm hx27m hfpm hinv_m)
  dsimp only [v1StateInnerPBPinnedAt]
  rw [h136, h240, encodeToVecJumpTableBytes_eq ((blkPl_426).ρ etvJumpTableRoSym)]
  exact Entails.of_eq (by sep_ac_rfl)

theorem step_encodeToVec_v1_headerSent_at_1880_placed [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (H : String → Option (State → State)) {s0 : State}
    (hhsLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 414)
      (withStepInv s0 (leafEncLen48Spec (chunkedHeaderSentPBPinnedAt A.repAlloc) chunkedHeaderSentPBEncodedLen)))
    (hekSentLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 415)
      (withStepInv s0 (leafEncLen16Spec (ekSentPBPinnedAt A.repAlloc) ekSentPBEncodedLen)))
    (hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hauthEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 314)
      (withStepInv s0 (authEncodeExactSpecOf resStack A lim)))
    (hmemcpy : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) ((blkPl_426).ρ "memcpy") etvMemcpyRegionSpec)
    (hpolyEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 316)
      (withStepInv s0 (etvPolyEncoderBudgetExactSpecOf resStack A lim)))
    (hpolyDec : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 315)
      (withStepInv s0 (etvPolyDecoderBudgetExactSpecOf resStack A lim)))
    (v : V1State.Chunked.HeaderSent) :
    StepInnerStateAt1880Placed resStack A lim st H s0 (.headerSent v) := by
  intro a sp cap ptr g bs hv_len hfit halign ret s P F Q Qp oom
    hpc hrun hsp htr hx8 hx9 hx20 hx21 hx28 hinv0 hP hnext
  subst hP
  have hx8' : s.readReg64 .x8 = 2#64 := by
    rw [hx8, show v1StateInnerCap g (.headerSent v) = 0x8000000000000002#64 from rfl,
      cap_xor_top_eq_of_eq (cap := 0x8000000000000002#64) (x := 2#64) (by decide) rfl]
    decide
  clear hx8
  rw [encodeToVecJumpTableBytes_eq ((blkPl_426).ρ etvJumpTableRoSym)]
  etv_jump16_placed 2176 s 2#64 hx8'
  intro hinv1
  have h136 : (a + 128#64) + 8#64 = a + 136#64 := by bv_omega
  dsimp only [v1StateInnerPBPinnedAt]
  rw [h136]
  refine step_encodeToVec_v1_headerSent_placed hres A lim st H
    hhsLen hekSentLen hvarint hauthEnc hmemcpy hpolyEnc hpolyDec
    a sp cap ptr g.a.gHeaderSent v bs hv_len hfit halign
    (F := ((a + 128#64) ↦₆₄ 0x8000000000000002#64) ∗ memRegion (a + 128#64 + 184#64) 40 ∗
      encodeToVecJumpTableBytesAt ((blkPl_426).ρ etvJumpTableRoSym) ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1.1)
    (by dsimp only [encodeToVecJumpTableBytesAt]; rw [← A.pool_of_vmPreserved hinv1.2]; sep_ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hx27m hfpm hinv_m
  simp only [arm64_norm] at hx27m hfpm
  refine SepWPp.weaken_pre ?_ (hnext sm hpcm hrunm hspm htrm hx27m hfpm hinv_m)
  dsimp only [v1StateInnerPBPinnedAt]
  rw [h136, encodeToVecJumpTableBytes_eq ((blkPl_426).ρ etvJumpTableRoSym)]
  exact Entails.of_eq (by sep_ac_rfl)

theorem step_encodeToVec_v1_noHeaderReceived_at_1880_placed [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (H : String → Option (State → State)) {s0 : State}
    (hnhrLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 424)
      (withStepInv s0 (leafEncLen16Spec (noHeaderReceivedPBPinnedAt A.repAlloc) noHeaderReceivedPBEncodedLen)))
    (hpolyDecLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 413)
      (withStepInv s0 (leafEncLen16Spec (polynomialDecoderPBPinnedAt A.repAlloc) polynomialDecoderPBEncodedLen)))
    (hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hauthEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 314)
      (withStepInv s0 (authEncodeExactSpecOf resStack A lim)))
    (hpolyDec : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 315)
      (withStepInv s0 (etvPolyDecoderBudgetExactSpecOf resStack A lim)))
    (v : V1State.Chunked.NoHeaderReceived) :
    StepInnerStateAt1880Placed resStack A lim st H s0 (.noHeaderReceived v) := by
  intro a sp cap ptr g bs hv_len hfit halign ret s P F Q Qp oom
    hpc hrun hsp htr hx8 hx9 hx20 hx21 hx28 hinv0 hP hnext
  subst hP
  have hx8' : s.readReg64 .x8 = 5#64 := by
    rw [hx8, show v1StateInnerCap g (.noHeaderReceived v) = 0x8000000000000005#64 from rfl,
      cap_xor_top_eq_of_eq (cap := 0x8000000000000005#64) (x := 5#64) (by decide) rfl]
    decide
  clear hx8
  rw [encodeToVecJumpTableBytes_eq ((blkPl_426).ρ etvJumpTableRoSym)]
  etv_jump16_placed 2848 s 5#64 hx8'
  intro hinv1
  have h136 : (a + 128#64) + 8#64 = a + 136#64 := by bv_omega
  have h176 : (a + 128#64) + 48#64 = a + 176#64 := by bv_omega
  dsimp only [v1StateInnerPBPinnedAt]
  rw [h136, h176]
  refine step_encodeToVec_v1_noHeaderReceived_placed hres A lim st H
    hnhrLen hpolyDecLen hvarint hauthEnc hpolyDec
    a sp cap ptr g.a.gNoHeaderReceived v bs hv_len hfit halign
    (F := ((a + 128#64) ↦₆₄ 0x8000000000000005#64) ∗ memRegion (a + 128#64 + 104#64) 120 ∗
      encodeToVecJumpTableBytesAt ((blkPl_426).ρ etvJumpTableRoSym) ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1.1)
    (by dsimp only [encodeToVecJumpTableBytesAt]; rw [← A.pool_of_vmPreserved hinv1.2]; sep_ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hx27m hfpm hinv_m
  simp only [arm64_norm] at hx27m hfpm
  refine SepWPp.weaken_pre ?_ (hnext sm hpcm hrunm hspm htrm hx27m hfpm hinv_m)
  dsimp only [v1StateInnerPBPinnedAt]
  rw [h136, h176, encodeToVecJumpTableBytes_eq ((blkPl_426).ρ etvJumpTableRoSym)]
  exact Entails.of_eq (by sep_ac_rfl)

theorem step_encodeToVec_v1_headerReceived_at_1880_placed [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (H : String → Option (State → State)) {s0 : State}
    (hhrLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 404)
      (withStepInv s0 (leafEncLen16Spec (headerReceivedPBPinnedAt A.repAlloc) headerReceivedPBEncodedLen)))
    (hpolyDecLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 413)
      (withStepInv s0 (leafEncLen16Spec (polynomialDecoderPBPinnedAt A.repAlloc) polynomialDecoderPBEncodedLen)))
    (hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hauthEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 314)
      (withStepInv s0 (authEncodeExactSpecOf resStack A lim)))
    (hmemcpy : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) ((blkPl_426).ρ "memcpy") etvMemcpyRegionSpec)
    (hpolyDec : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 315)
      (withStepInv s0 (etvPolyDecoderBudgetExactSpecOf resStack A lim)))
    (v : V1State.Chunked.HeaderReceived) :
    StepInnerStateAt1880Placed resStack A lim st H s0 (.headerReceived v) := by
  intro a sp cap ptr g bs hv_len hfit halign ret s P F Q Qp oom
    hpc hrun hsp htr hx8 hx9 hx20 hx21 hx28 hinv0 hP hnext
  subst hP
  have hx8' : s.readReg64 .x8 = 6#64 := by
    rw [hx8, show v1StateInnerCap g (.headerReceived v) = 0x8000000000000006#64 from rfl,
      cap_xor_top_eq_of_eq (cap := 0x8000000000000006#64) (x := 6#64) (by decide) rfl]
    decide
  clear hx8
  rw [encodeToVecJumpTableBytes_eq ((blkPl_426).ρ etvJumpTableRoSym)]
  etv_jump16_placed 2908 s 6#64 hx8'
  intro hinv1
  have h136 : (a + 128#64) + 8#64 = a + 136#64 := by bv_omega
  have h216 : (a + 128#64) + 88#64 = a + 216#64 := by bv_omega
  dsimp only [v1StateInnerPBPinnedAt]
  rw [h136, h216]
  refine step_encodeToVec_v1_headerReceived_placed hres A lim st H
    hhrLen hpolyDecLen hvarint hauthEnc hmemcpy hpolyDec
    a sp cap ptr g.b.gHeaderReceived v bs hv_len hfit halign
    (F := ((a + 128#64) ↦₆₄ 0x8000000000000006#64) ∗ memRegion (a + 128#64 + 128#64) 96 ∗
      encodeToVecJumpTableBytesAt ((blkPl_426).ρ etvJumpTableRoSym) ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1.1)
    (by dsimp only [encodeToVecJumpTableBytesAt]; rw [← A.pool_of_vmPreserved hinv1.2]; sep_ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hx27m hfpm hinv_m
  simp only [arm64_norm] at hx27m hfpm
  refine SepWPp.weaken_pre ?_ (hnext sm hpcm hrunm hspm htrm hx27m hfpm hinv_m)
  dsimp only [v1StateInnerPBPinnedAt]
  rw [h136, h216, encodeToVecJumpTableBytes_eq ((blkPl_426).ρ etvJumpTableRoSym)]
  exact Entails.of_eq (by sep_ac_rfl)

theorem step_encodeToVec_v1_ekReceivedCt1Sampled_at_1880_placed [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (H : String → Option (State → State)) {s0 : State}
    (hct1Len : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 387)
      (withStepInv s0 (leafEncLen16Spec (ct1SentEkReceivedPBPinnedAt A.repAlloc) ct1SentEkReceivedPBEncodedLen)))
    (hpolyEncLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 401)
      (withStepInv s0 (leafEncLen16Spec (polynomialEncoderPBPinnedAt A.repAlloc) polynomialEncoderPBEncodedLen)))
    (hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hauthEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 314)
      (withStepInv s0 (authEncodeExactSpecOf resStack A lim)))
    (hmemcpy : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) ((blkPl_426).ρ "memcpy") etvMemcpyRegionSpec)
    (hpolyEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 316)
      (withStepInv s0 (etvPolyEncoderBudgetExactSpecOf resStack A lim)))
    (v : V1State.Chunked.EkReceivedCt1Sampled) :
    StepInnerStateAt1880Placed resStack A lim st H s0 (.ekReceivedCt1Sampled v) := by
  intro a sp cap ptr g bs hv_len hfit halign ret s P F Q Qp oom
    hpc hrun hsp htr hx8 hx9 hx20 hx21 hx28 hinv0 hP hnext
  subst hP
  have hx8' : s.readReg64 .x8 = 8#64 := by
    rw [hx8, show v1StateInnerCap g (.ekReceivedCt1Sampled v) = 0x8000000000000008#64 from rfl,
      cap_xor_top_eq_of_eq (cap := 0x8000000000000008#64) (x := 8#64) (by decide) rfl]
    decide
  clear hx8
  rw [encodeToVecJumpTableBytes_eq ((blkPl_426).ρ etvJumpTableRoSym)]
  etv_jump16_placed 3068 s 8#64 hx8'
  intro hinv1
  have h136 : (a + 128#64) + 8#64 = a + 136#64 := by bv_omega
  have h264 : (a + 128#64) + 136#64 = a + 264#64 := by bv_omega
  dsimp only [v1StateInnerPBPinnedAt]
  rw [h136, h264]
  refine step_encodeToVec_v1_ekReceivedCt1Sampled_placed hres A lim st H
    hct1Len hpolyEncLen hvarint hauthEnc hmemcpy hpolyEnc
    a sp cap ptr g.b.gEkReceivedCt1Sampled v bs hv_len hfit halign
    (F := ((a + 128#64) ↦₆₄ 0x8000000000000008#64) ∗ memRegion (a + 128#64 + 192#64) 32 ∗
      encodeToVecJumpTableBytesAt ((blkPl_426).ρ etvJumpTableRoSym) ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1.1)
    (by dsimp only [encodeToVecJumpTableBytesAt]; rw [← A.pool_of_vmPreserved hinv1.2]; sep_ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hx27m hfpm hinv_m
  simp only [arm64_norm] at hx27m hfpm
  refine SepWPp.weaken_pre ?_ (hnext sm hpcm hrunm hspm htrm hx27m hfpm hinv_m)
  dsimp only [v1StateInnerPBPinnedAt]
  rw [h136, h264, encodeToVecJumpTableBytes_eq ((blkPl_426).ρ etvJumpTableRoSym)]
  exact Entails.of_eq (by sep_ac_rfl)

theorem step_encodeToVec_v1_ct2Sampled_at_1880_placed [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (H : String → Option (State → State)) {s0 : State}
    (hct2Len : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 389)
      (withStepInv s0 (leafEncLen16Spec (ct2SentPBPinnedAt A.repAlloc) ct2SentPBEncodedLen)))
    (hpolyEncLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 401)
      (withStepInv s0 (leafEncLen16Spec (polynomialEncoderPBPinnedAt A.repAlloc) polynomialEncoderPBEncodedLen)))
    (hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hauthEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 314)
      (withStepInv s0 (authEncodeExactSpecOf resStack A lim)))
    (hpolyEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 316)
      (withStepInv s0 (etvPolyEncoderBudgetExactSpecOf resStack A lim)))
    (v : V1State.Chunked.Ct2Sampled) :
    StepInnerStateAt1880Placed resStack A lim st H s0 (.ct2Sampled v) := by
  intro a sp cap ptr g bs hv_len hfit halign ret s P F Q Qp oom
    hpc hrun hsp htr hx8 hx9 hx20 hx21 hx28 hinv0 hP hnext
  subst hP
  have hx8' : s.readReg64 .x8 = 10#64 := by
    rw [hx8, show v1StateInnerCap g (.ct2Sampled v) = 0x800000000000000a#64 from rfl,
      cap_xor_top_eq_of_eq (cap := 0x800000000000000a#64) (x := 10#64) (by decide) rfl]
    decide
  clear hx8
  rw [encodeToVecJumpTableBytes_eq ((blkPl_426).ρ etvJumpTableRoSym)]
  etv_jump16_placed 3008 s 10#64 hx8'
  intro hinv1
  have h136 : (a + 128#64) + 8#64 = a + 136#64 := by bv_omega
  have h192 : (a + 128#64) + 64#64 = a + 192#64 := by bv_omega
  dsimp only [v1StateInnerPBPinnedAt]
  rw [h136, h192]
  refine step_encodeToVec_v1_ct2Sampled_placed hres A lim st H
    hct2Len hpolyEncLen hvarint hauthEnc hpolyEnc
    a sp cap ptr g.b.gCt2Sampled v bs hv_len hfit halign
    (F := ((a + 128#64) ↦₆₄ 0x800000000000000a#64) ∗ memRegion (a + 128#64 + 120#64) 104 ∗
      encodeToVecJumpTableBytesAt ((blkPl_426).ρ etvJumpTableRoSym) ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1.1)
    (by dsimp only [encodeToVecJumpTableBytesAt]; rw [← A.pool_of_vmPreserved hinv1.2]; sep_ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hx27m hfpm hinv_m
  simp only [arm64_norm] at hx27m hfpm
  refine SepWPp.weaken_pre ?_ (hnext sm hpcm hrunm hspm htrm hx27m hfpm hinv_m)
  dsimp only [v1StateInnerPBPinnedAt]
  rw [h136, h192, encodeToVecJumpTableBytes_eq ((blkPl_426).ρ etvJumpTableRoSym)]
  exact Entails.of_eq (by sep_ac_rfl)

/-! ## 2. Unified 11-Variant Dispatcher at `StepInnerStateAt1880Placed` -/

/-- Unified dispatcher for all 11 `V1State.InnerState` variants at `StepInnerStateAt1880Placed`. -/
theorem step_encodeToVec_inner_at_1880_all_placed [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State)) (s0 : State)
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hauthEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 314)
      (withStepInv s0 (authEncodeExactSpecOf resStack A lim)))
    (hpolyEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 316)
      (withStepInv s0 (etvPolyEncoderBudgetExactSpecOf resStack A lim)))
    (hpolyDec : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 315)
      (withStepInv s0 (etvPolyDecoderBudgetExactSpecOf resStack A lim)))
    (hekEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 318)
      (withStepInv s0 (etvEkSentCt1ReceivedBudgetExactSpecOf resStack A lim)))
    (hct1SentEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 319)
      (withStepInv s0 (etvCt1SentBudgetExactSpecOf resStack A lim)))
    (hmemcpy : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext))
      ((blkPl_426).ρ "memcpy")
      etvMemcpyRegionSpec) :
    ∀ is : V1State.InnerState,
      StepInnerStateAt1880Placed resStack A lim st (Rust.withPanics ext) s0 is := by
  have hkuLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 400)
      (withStepInv s0 (leafEncLen16Spec (keysUnsampledPBPinnedAt A.repAlloc) keysUnsampledPBEncodedLen)) :=
    etv_subroutine_ok_placed_of_plain hcl0
      (keysUnsampledEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext)
  have hhs16Len : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 411)
      (withStepInv s0 (leafEncLen16Spec (headerSentPBPinnedAt A.repAlloc) headerSentPBEncodedLen)) :=
    etv_subroutine_ok_placed_of_plain hcl0
      (headerSentEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext)
  have hhs48Len : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 414)
      (withStepInv s0 (leafEncLen48Spec (chunkedHeaderSentPBPinnedAt A.repAlloc) chunkedHeaderSentPBEncodedLen)) :=
    etv_subroutine_ok_placed_of_lscl hcl0
      (chunkedHeaderSentEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext)
  have hekSentLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 415)
      (withStepInv s0 (leafEncLen16Spec (ekSentPBPinnedAt A.repAlloc) ekSentPBEncodedLen)) :=
    etv_subroutine_ok_placed_of_plain hcl0
      (ekSentEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext)
  have hekLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 421)
      (withStepInv s0 (leafEncLen16Spec (ekSentCt1ReceivedPBPinnedAt A.repAlloc) ekSentCt1ReceivedPBEncodedLen)) :=
    etv_subroutine_ok_placed_of_plain hcl0
      (ekSentCt1ReceivedEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext)
  have hct1SentLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 408)
      (withStepInv s0 (leafEncLen16Spec (ct1SentPBPinnedAt A.repAlloc) ct1SentPBEncodedLen)) :=
    etv_subroutine_ok_placed_of_plain hcl0
      (ct1SentEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext)
  have hnhrLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 424)
      (withStepInv s0 (leafEncLen16Spec (noHeaderReceivedPBPinnedAt A.repAlloc) noHeaderReceivedPBEncodedLen)) :=
    etv_subroutine_ok_placed_of_plain hcl0
      (noHeaderReceivedEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext)
  have hhrLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 404)
      (withStepInv s0 (leafEncLen16Spec (headerReceivedPBPinnedAt A.repAlloc) headerReceivedPBEncodedLen)) :=
    etv_subroutine_ok_placed_of_plain hcl0
      (headerReceivedEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext)
  have hct1SampledLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 407)
      (withStepInv s0 (leafEncLen48Spec (chunkedCt1SampledPBPinnedAt A.repAlloc) chunkedCt1SampledPBEncodedLen)) :=
    etv_subroutine_ok_placed_of_lscl hcl0
      (chunkedCt1SampledEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext)
  have hct1EkLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 387)
      (withStepInv s0 (leafEncLen16Spec (ct1SentEkReceivedPBPinnedAt A.repAlloc) ct1SentEkReceivedPBEncodedLen)) :=
    etv_subroutine_ok_placed_of_plain hcl0
      (ct1SentEkReceivedEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext)
  have hct2Len : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 389)
      (withStepInv s0 (leafEncLen16Spec (ct2SentPBPinnedAt A.repAlloc) ct2SentPBEncodedLen)) :=
    etv_subroutine_ok_placed_of_plain hcl0
      (ct2SentEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext)
  have hpolyDecLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 413)
      (withStepInv s0 (leafEncLen16Spec (polynomialDecoderPBPinnedAt A.repAlloc) polynomialDecoderPBEncodedLen)) :=
    etv_subroutine_ok_placed_of_plain hcl0
      (polynomialDecoderEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext)
  have hpolyEncLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 401)
      (withStepInv s0 (leafEncLen16Spec (polynomialEncoderPBPinnedAt A.repAlloc) polynomialEncoderPBEncodedLen)) :=
    etv_subroutine_ok_placed_of_plain hcl0
      (polynomialEncoderEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext)
  intro is
  cases is with
  | keysUnsampled v =>
    exact step_encodeToVec_v1_keysUnsampled_at_1880_placed hres A lim st (Rust.withPanics ext)
      hkuLen hvarint hauthEnc v
  | keysSampled v =>
    exact step_encodeToVec_v1_keysSampled_at_1880_placed hres A lim st (Rust.withPanics ext)
      hhs16Len hpolyEncLen hvarint hauthEnc hmemcpy hpolyEnc v
  | headerSent v =>
    exact step_encodeToVec_v1_headerSent_at_1880_placed hres A lim st (Rust.withPanics ext)
      hhs48Len hekSentLen hvarint hauthEnc hmemcpy hpolyEnc hpolyDec v
  | ct1Received v =>
    exact step_encodeToVec_v1_ct1Received_at_1880_placed hres A lim st (Rust.withPanics ext)
      hekLen hpolyEncLen hvarint hekEnc hpolyEnc v
  | ekSentCt1Received v =>
    exact step_encodeToVec_v1_ekSentCt1Received_at_1880_placed hres A lim st (Rust.withPanics ext)
      hekLen hpolyDecLen hvarint hekEnc hpolyDec v
  | noHeaderReceived v =>
    exact step_encodeToVec_v1_noHeaderReceived_at_1880_placed hres A lim st (Rust.withPanics ext)
      hnhrLen hpolyDecLen hvarint hauthEnc hpolyDec v
  | headerReceived v =>
    exact step_encodeToVec_v1_headerReceived_at_1880_placed hres A lim st (Rust.withPanics ext)
      hhrLen hpolyDecLen hvarint hauthEnc hmemcpy hpolyDec v
  | ct1Sampled v =>
    exact step_encodeToVec_v1_ct1Sampled_at_1880_placed hres A lim st (Rust.withPanics ext)
      hct1SampledLen hvarint hct1SentEnc hpolyEnc hpolyDec v
  | ekReceivedCt1Sampled v =>
    exact step_encodeToVec_v1_ekReceivedCt1Sampled_at_1880_placed hres A lim st (Rust.withPanics ext)
      hct1EkLen hpolyEncLen hvarint hauthEnc hmemcpy hpolyEnc v
  | ct1Acknowledged v =>
    exact step_encodeToVec_v1_ct1Acknowledged_at_1880_placed hres A lim st (Rust.withPanics ext)
      hct1SentLen hpolyDecLen hvarint hct1SentEnc hpolyDec v
  | ct2Sampled v =>
    exact step_encodeToVec_v1_ct2Sampled_at_1880_placed hres A lim st (Rust.withPanics ext)
      hct2Len hpolyEncLen hvarint hauthEnc hpolyEnc v

/-! ## 3. Placed Contract Propositions & Top-Level `subroutine_ok` Theorems (`Block 426`) -/

abbrev PqRatchetStateEncodeToVecPinnedPlacedOkExt :=
  @DefsBudget.PqRatchetStateEncodeToVecPinnedPlacedOkExt

abbrev PqRatchetStateEncodeToVecPlacedOkExt :=
  @DefsBudget.PqRatchetStateEncodeToVecPlacedOkExt

def PqRatchetStateEncodeToVecPinnedPlacedOk [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  PqRatchetStateEncodeToVecPinnedPlacedOkExt A lim (tripleRatchetExterns C ctl abs)

def PqRatchetStateEncodeToVecPlacedOk [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  PqRatchetStateEncodeToVecPlacedOkExt A lim (tripleRatchetExterns C ctl abs)

/-- Top-level `NoOom` `subroutine_ok` for `PqRatchetState::encode_to_vec` (`Block 426`) on
`withLsCodeLoaded lsmpl (pqRatchetStateEncodeToVecRoPinnedNoOomPlacedSpecOf doReserveStack A lim)`. -/
theorem pqRatchetStateEncodeToVec_ro_pinned_noOom_placed_ok_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hcp_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 313)
      (withLsCodeLoaded lsmpl (encodeChainParamsExactSpecOf doReserveStack A lim)))
    (hed_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 317)
      (withLsCodeLoaded lsmpl (encodeEpochDirectionExactSpecOf doReserveStack A lim)))
    (hauth_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 314)
      (withLsCodeLoaded lsmpl (authEncodeExactSpecOf doReserveStack A lim)))
    (hpolyEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 316)
      (withLsCodeLoaded lsmpl (etvPolyEncoderBudgetExactSpecOf doReserveStack A lim)))
    (hpolyDec_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 315)
      (withLsCodeLoaded lsmpl (etvPolyDecoderBudgetExactSpecOf doReserveStack A lim)))
    (hekEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 318)
      (withLsCodeLoaded lsmpl (etvEkSentCt1ReceivedBudgetExactSpecOf doReserveStack A lim)))
    (hct1SentEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 319)
      (withLsCodeLoaded lsmpl (etvCt1SentBudgetExactSpecOf doReserveStack A lim))) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext))
      (blkPl_426).base
      (withLsCodeLoaded lsmpl (pqRatchetStateEncodeToVecRoPinnedNoOomPlacedSpecOf doReserveStack A lim)) :=
  pqRatchetStateEncodeToVec_ro_pinned_noOom_placed_ok_of_variants
    h_panic hshim halloc hrealloc hmc
    hcp_ok hed_ok hpolyEnc_ok hpolyDec_ok hekEnc_ok hct1SentEnc_ok
    (fun s0 st1 hcl0 v => step_encodeToVec_v1_keysUnsampled_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
      (etv_subroutine_ok_placed_of_plain hcl0 (keysUnsampledEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_encodeVarint_placed_ok h_panic hshim halloc hrealloc s0 hcl0)
      (subroutine_ok_withStepInv_lscl hcl0 hauth_ok) v)
    (fun s0 st1 hcl0 v => step_encodeToVec_v1_keysSampled_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
      (etv_subroutine_ok_placed_of_plain hcl0 (headerSentEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_subroutine_ok_placed_of_plain hcl0 (polynomialEncoderEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_encodeVarint_placed_ok h_panic hshim halloc hrealloc s0 hcl0)
      (subroutine_ok_withStepInv_lscl hcl0 hauth_ok)
      (etv_memcpy_placed_ok hmc)
      (subroutine_ok_withStepInv_lscl hcl0 hpolyEnc_ok) v)
    (fun s0 st1 hcl0 v => step_encodeToVec_v1_headerSent_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
      (etv_subroutine_ok_placed_of_lscl hcl0 (chunkedHeaderSentEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_subroutine_ok_placed_of_plain hcl0 (ekSentEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_encodeVarint_placed_ok h_panic hshim halloc hrealloc s0 hcl0)
      (subroutine_ok_withStepInv_lscl hcl0 hauth_ok)
      (etv_memcpy_placed_ok hmc)
      (subroutine_ok_withStepInv_lscl hcl0 hpolyEnc_ok)
      (subroutine_ok_withStepInv_lscl hcl0 hpolyDec_ok) v)
    (fun s0 st1 hcl0 v => step_encodeToVec_v1_noHeaderReceived_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
      (etv_subroutine_ok_placed_of_plain hcl0 (noHeaderReceivedEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_subroutine_ok_placed_of_plain hcl0 (polynomialDecoderEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_encodeVarint_placed_ok h_panic hshim halloc hrealloc s0 hcl0)
      (subroutine_ok_withStepInv_lscl hcl0 hauth_ok)
      (subroutine_ok_withStepInv_lscl hcl0 hpolyDec_ok) v)
    (fun s0 st1 hcl0 v => step_encodeToVec_v1_headerReceived_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
      (etv_subroutine_ok_placed_of_plain hcl0 (headerReceivedEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_subroutine_ok_placed_of_plain hcl0 (polynomialDecoderEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_encodeVarint_placed_ok h_panic hshim halloc hrealloc s0 hcl0)
      (subroutine_ok_withStepInv_lscl hcl0 hauth_ok)
      (etv_memcpy_placed_ok hmc)
      (subroutine_ok_withStepInv_lscl hcl0 hpolyDec_ok) v)
    (fun s0 st1 hcl0 v => step_encodeToVec_v1_ekReceivedCt1Sampled_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
      (etv_subroutine_ok_placed_of_plain hcl0 (ct1SentEkReceivedEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_subroutine_ok_placed_of_plain hcl0 (polynomialEncoderEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_encodeVarint_placed_ok h_panic hshim halloc hrealloc s0 hcl0)
      (subroutine_ok_withStepInv_lscl hcl0 hauth_ok)
      (etv_memcpy_placed_ok hmc)
      (subroutine_ok_withStepInv_lscl hcl0 hpolyEnc_ok) v)
    (fun s0 st1 hcl0 v => step_encodeToVec_v1_ct2Sampled_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
      (etv_subroutine_ok_placed_of_plain hcl0 (ct2SentEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_subroutine_ok_placed_of_plain hcl0 (polynomialEncoderEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_encodeVarint_placed_ok h_panic hshim halloc hrealloc s0 hcl0)
      (subroutine_ok_withStepInv_lscl hcl0 hauth_ok)
      (subroutine_ok_withStepInv_lscl hcl0 hpolyEnc_ok) v)

theorem pqRatchetStateEncodeToVec_ro_noOom_placed_ok_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hcp_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 313)
      (withLsCodeLoaded lsmpl (encodeChainParamsExactSpecOf doReserveStack A lim)))
    (hed_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 317)
      (withLsCodeLoaded lsmpl (encodeEpochDirectionExactSpecOf doReserveStack A lim)))
    (hauth_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 314)
      (withLsCodeLoaded lsmpl (authEncodeExactSpecOf doReserveStack A lim)))
    (hpolyEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 316)
      (withLsCodeLoaded lsmpl (etvPolyEncoderBudgetExactSpecOf doReserveStack A lim)))
    (hpolyDec_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 315)
      (withLsCodeLoaded lsmpl (etvPolyDecoderBudgetExactSpecOf doReserveStack A lim)))
    (hekEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 318)
      (withLsCodeLoaded lsmpl (etvEkSentCt1ReceivedBudgetExactSpecOf doReserveStack A lim)))
    (hct1SentEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 319)
      (withLsCodeLoaded lsmpl (etvCt1SentBudgetExactSpecOf doReserveStack A lim))) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext))
      (blkPl_426).base
      (withLsCodeLoaded lsmpl (pqRatchetStateEncodeToVecRoNoOomPlacedSpecOf doReserveStack A lim)) :=
  pqRatchetStateEncodeToVec_ro_noOom_placed_ok_of_pinned
    (pqRatchetStateEncodeToVec_ro_pinned_noOom_placed_ok_of_contracts
      h_panic hshim halloc hrealloc hmc
      hcp_ok hed_ok hauth_ok hpolyEnc_ok hpolyDec_ok hekEnc_ok hct1SentEnc_ok)

/-- Top-level `subroutine_ok` for `PqRatchetState::encode_to_vec` (`Block 426`) on
`withLsCodeLoaded lsmpl (pqRatchetStateEncodeToVecRoPinnedPlacedSpecOf doReserveStack A lim)`
(discharging all `encoded_len` callees, `encode_varint4`, and allocator/memcpy hooks). -/
theorem pqRatchetStateEncodeToVec_ro_pinned_placed_ok_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hcp_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 313)
      (withLsCodeLoaded lsmpl (encodeChainParamsExactSpecOf doReserveStack A lim)))
    (hed_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 317)
      (withLsCodeLoaded lsmpl (encodeEpochDirectionExactSpecOf doReserveStack A lim)))
    (hauth_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 314)
      (withLsCodeLoaded lsmpl (authEncodeExactSpecOf doReserveStack A lim)))
    (hpolyEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 316)
      (withLsCodeLoaded lsmpl (etvPolyEncoderBudgetExactSpecOf doReserveStack A lim)))
    (hpolyDec_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 315)
      (withLsCodeLoaded lsmpl (etvPolyDecoderBudgetExactSpecOf doReserveStack A lim)))
    (hekEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 318)
      (withLsCodeLoaded lsmpl (etvEkSentCt1ReceivedBudgetExactSpecOf doReserveStack A lim)))
    (hct1SentEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 319)
      (withLsCodeLoaded lsmpl (etvCt1SentBudgetExactSpecOf doReserveStack A lim))) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext))
      (blkPl_426).base
      (withLsCodeLoaded lsmpl (pqRatchetStateEncodeToVecRoPinnedPlacedSpecOf doReserveStack A lim)) :=
  pqRatchetStateEncodeToVec_ro_pinned_placed_ok_of_variants
    h_panic hshim halloc hrealloc hmc
    hcp_ok hed_ok hpolyEnc_ok hpolyDec_ok hekEnc_ok hct1SentEnc_ok
    (fun s0 st1 hcl0 v => step_encodeToVec_v1_keysUnsampled_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
      (etv_subroutine_ok_placed_of_plain hcl0 (keysUnsampledEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_encodeVarint_placed_ok h_panic hshim halloc hrealloc s0 hcl0)
      (subroutine_ok_withStepInv_lscl hcl0 hauth_ok) v)
    (fun s0 st1 hcl0 v => step_encodeToVec_v1_keysSampled_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
      (etv_subroutine_ok_placed_of_plain hcl0 (headerSentEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_subroutine_ok_placed_of_plain hcl0 (polynomialEncoderEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_encodeVarint_placed_ok h_panic hshim halloc hrealloc s0 hcl0)
      (subroutine_ok_withStepInv_lscl hcl0 hauth_ok)
      (etv_memcpy_placed_ok hmc)
      (subroutine_ok_withStepInv_lscl hcl0 hpolyEnc_ok) v)
    (fun s0 st1 hcl0 v => step_encodeToVec_v1_headerSent_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
      (etv_subroutine_ok_placed_of_lscl hcl0 (chunkedHeaderSentEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_subroutine_ok_placed_of_plain hcl0 (ekSentEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_encodeVarint_placed_ok h_panic hshim halloc hrealloc s0 hcl0)
      (subroutine_ok_withStepInv_lscl hcl0 hauth_ok)
      (etv_memcpy_placed_ok hmc)
      (subroutine_ok_withStepInv_lscl hcl0 hpolyEnc_ok)
      (subroutine_ok_withStepInv_lscl hcl0 hpolyDec_ok) v)
    (fun s0 st1 hcl0 v => step_encodeToVec_v1_noHeaderReceived_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
      (etv_subroutine_ok_placed_of_plain hcl0 (noHeaderReceivedEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_subroutine_ok_placed_of_plain hcl0 (polynomialDecoderEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_encodeVarint_placed_ok h_panic hshim halloc hrealloc s0 hcl0)
      (subroutine_ok_withStepInv_lscl hcl0 hauth_ok)
      (subroutine_ok_withStepInv_lscl hcl0 hpolyDec_ok) v)
    (fun s0 st1 hcl0 v => step_encodeToVec_v1_headerReceived_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
      (etv_subroutine_ok_placed_of_plain hcl0 (headerReceivedEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_subroutine_ok_placed_of_plain hcl0 (polynomialDecoderEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_encodeVarint_placed_ok h_panic hshim halloc hrealloc s0 hcl0)
      (subroutine_ok_withStepInv_lscl hcl0 hauth_ok)
      (etv_memcpy_placed_ok hmc)
      (subroutine_ok_withStepInv_lscl hcl0 hpolyDec_ok) v)
    (fun s0 st1 hcl0 v => step_encodeToVec_v1_ekReceivedCt1Sampled_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
      (etv_subroutine_ok_placed_of_plain hcl0 (ct1SentEkReceivedEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_subroutine_ok_placed_of_plain hcl0 (polynomialEncoderEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_encodeVarint_placed_ok h_panic hshim halloc hrealloc s0 hcl0)
      (subroutine_ok_withStepInv_lscl hcl0 hauth_ok)
      (etv_memcpy_placed_ok hmc)
      (subroutine_ok_withStepInv_lscl hcl0 hpolyEnc_ok) v)
    (fun s0 st1 hcl0 v => step_encodeToVec_v1_ct2Sampled_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
      (etv_subroutine_ok_placed_of_plain hcl0 (ct2SentEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_subroutine_ok_placed_of_plain hcl0 (polynomialEncoderEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_encodeVarint_placed_ok h_panic hshim halloc hrealloc s0 hcl0)
      (subroutine_ok_withStepInv_lscl hcl0 hauth_ok)
      (subroutine_ok_withStepInv_lscl hcl0 hpolyEnc_ok) v)

theorem pqRatchetStateEncodeToVec_ro_placed_ok_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hcp_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 313)
      (withLsCodeLoaded lsmpl (encodeChainParamsExactSpecOf doReserveStack A lim)))
    (hed_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 317)
      (withLsCodeLoaded lsmpl (encodeEpochDirectionExactSpecOf doReserveStack A lim)))
    (hauth_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 314)
      (withLsCodeLoaded lsmpl (authEncodeExactSpecOf doReserveStack A lim)))
    (hpolyEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 316)
      (withLsCodeLoaded lsmpl (etvPolyEncoderBudgetExactSpecOf doReserveStack A lim)))
    (hpolyDec_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 315)
      (withLsCodeLoaded lsmpl (etvPolyDecoderBudgetExactSpecOf doReserveStack A lim)))
    (hekEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 318)
      (withLsCodeLoaded lsmpl (etvEkSentCt1ReceivedBudgetExactSpecOf doReserveStack A lim)))
    (hct1SentEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 319)
      (withLsCodeLoaded lsmpl (etvCt1SentBudgetExactSpecOf doReserveStack A lim))) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext))
      (blkPl_426).base
      (withLsCodeLoaded lsmpl (pqRatchetStateEncodeToVecRoPlacedSpecOf doReserveStack A lim)) :=
  pqRatchetStateEncodeToVec_ro_placed_ok_of_variants
    h_panic hshim halloc hrealloc hmc
    hcp_ok hed_ok hpolyEnc_ok hpolyDec_ok hekEnc_ok hct1SentEnc_ok
    (fun s0 st1 hcl0 v => step_encodeToVec_v1_keysUnsampled_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
      (etv_subroutine_ok_placed_of_plain hcl0 (keysUnsampledEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_encodeVarint_placed_ok h_panic hshim halloc hrealloc s0 hcl0)
      (subroutine_ok_withStepInv_lscl hcl0 hauth_ok) v)
    (fun s0 st1 hcl0 v => step_encodeToVec_v1_keysSampled_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
      (etv_subroutine_ok_placed_of_plain hcl0 (headerSentEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_subroutine_ok_placed_of_plain hcl0 (polynomialEncoderEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_encodeVarint_placed_ok h_panic hshim halloc hrealloc s0 hcl0)
      (subroutine_ok_withStepInv_lscl hcl0 hauth_ok)
      (etv_memcpy_placed_ok hmc)
      (subroutine_ok_withStepInv_lscl hcl0 hpolyEnc_ok) v)
    (fun s0 st1 hcl0 v => step_encodeToVec_v1_headerSent_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
      (etv_subroutine_ok_placed_of_lscl hcl0 (chunkedHeaderSentEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_subroutine_ok_placed_of_plain hcl0 (ekSentEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_encodeVarint_placed_ok h_panic hshim halloc hrealloc s0 hcl0)
      (subroutine_ok_withStepInv_lscl hcl0 hauth_ok)
      (etv_memcpy_placed_ok hmc)
      (subroutine_ok_withStepInv_lscl hcl0 hpolyEnc_ok)
      (subroutine_ok_withStepInv_lscl hcl0 hpolyDec_ok) v)
    (fun s0 st1 hcl0 v => step_encodeToVec_v1_noHeaderReceived_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
      (etv_subroutine_ok_placed_of_plain hcl0 (noHeaderReceivedEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_subroutine_ok_placed_of_plain hcl0 (polynomialDecoderEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_encodeVarint_placed_ok h_panic hshim halloc hrealloc s0 hcl0)
      (subroutine_ok_withStepInv_lscl hcl0 hauth_ok)
      (subroutine_ok_withStepInv_lscl hcl0 hpolyDec_ok) v)
    (fun s0 st1 hcl0 v => step_encodeToVec_v1_headerReceived_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
      (etv_subroutine_ok_placed_of_plain hcl0 (headerReceivedEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_subroutine_ok_placed_of_plain hcl0 (polynomialDecoderEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_encodeVarint_placed_ok h_panic hshim halloc hrealloc s0 hcl0)
      (subroutine_ok_withStepInv_lscl hcl0 hauth_ok)
      (etv_memcpy_placed_ok hmc)
      (subroutine_ok_withStepInv_lscl hcl0 hpolyDec_ok) v)
    (fun s0 st1 hcl0 v => step_encodeToVec_v1_ekReceivedCt1Sampled_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
      (etv_subroutine_ok_placed_of_plain hcl0 (ct1SentEkReceivedEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_subroutine_ok_placed_of_plain hcl0 (polynomialEncoderEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_encodeVarint_placed_ok h_panic hshim halloc hrealloc s0 hcl0)
      (subroutine_ok_withStepInv_lscl hcl0 hauth_ok)
      (etv_memcpy_placed_ok hmc)
      (subroutine_ok_withStepInv_lscl hcl0 hpolyEnc_ok) v)
    (fun s0 st1 hcl0 v => step_encodeToVec_v1_ct2Sampled_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
      (etv_subroutine_ok_placed_of_plain hcl0 (ct2SentEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_subroutine_ok_placed_of_plain hcl0 (polynomialEncoderEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_encodeVarint_placed_ok h_panic hshim halloc hrealloc s0 hcl0)
      (subroutine_ok_withStepInv_lscl hcl0 hauth_ok)
      (subroutine_ok_withStepInv_lscl hcl0 hpolyEnc_ok) v)

/-- Top-level `NoOom` `subroutine_ok` for `PqRatchetState::encode_to_vec` (`Block 426`) on
`withLsRoLoaded lsmpl (withLsCodeLoaded lsmpl (pqRatchetStateEncodeToVecPinnedNoOomSpecOf doReserveStackX A lim))`. -/
theorem pqRatchetStateEncodeToVec_pinned_noOom_placed_ok_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hcp_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 313)
      (withLsCodeLoaded lsmpl (encodeChainParamsExactSpecOf doReserveStackX A lim)))
    (hed_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 317)
      (withLsCodeLoaded lsmpl (encodeEpochDirectionExactSpecOf doReserveStackX A lim)))
    (hauth_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 314)
      (withLsCodeLoaded lsmpl (authEncodeExactSpecOf doReserveStackX A lim)))
    (hpolyEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 316)
      (withLsCodeLoaded lsmpl (etvPolyEncoderBudgetExactSpecOf doReserveStackX A lim)))
    (hpolyDec_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 315)
      (withLsCodeLoaded lsmpl (etvPolyDecoderBudgetExactSpecOf doReserveStackX A lim)))
    (hekEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 318)
      (withLsCodeLoaded lsmpl (etvEkSentCt1ReceivedBudgetExactSpecOf doReserveStackX A lim)))
    (hct1SentEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 319)
      (withLsCodeLoaded lsmpl (etvCt1SentBudgetExactSpecOf doReserveStackX A lim))) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext))
      (blkPl_426).base
      (withLsRoLoaded lsmpl (withLsCodeLoaded lsmpl
        (pqRatchetStateEncodeToVecPinnedNoOomSpecOf doReserveStackX A lim))) :=
  pqRatchetStateEncodeToVec_pinned_noOom_placed_ok_of_variants
    h_panic hshim halloc hrealloc hmc
    hcp_ok hed_ok hpolyEnc_ok hpolyDec_ok hekEnc_ok hct1SentEnc_ok
    (fun s0 st1 hcl0 v => step_encodeToVec_v1_keysUnsampled_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
      (etv_subroutine_ok_placed_of_plain hcl0 (keysUnsampledEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_encodeVarint_placed_ok_x h_panic hshim halloc hrealloc s0 hcl0)
      (subroutine_ok_withStepInv_lscl hcl0 hauth_ok) v)
    (fun s0 st1 hcl0 v => step_encodeToVec_v1_keysSampled_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
      (etv_subroutine_ok_placed_of_plain hcl0 (headerSentEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_subroutine_ok_placed_of_plain hcl0 (polynomialEncoderEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_encodeVarint_placed_ok_x h_panic hshim halloc hrealloc s0 hcl0)
      (subroutine_ok_withStepInv_lscl hcl0 hauth_ok)
      (etv_memcpy_placed_ok hmc)
      (subroutine_ok_withStepInv_lscl hcl0 hpolyEnc_ok) v)
    (fun s0 st1 hcl0 v => step_encodeToVec_v1_headerSent_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
      (etv_subroutine_ok_placed_of_lscl hcl0 (chunkedHeaderSentEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_subroutine_ok_placed_of_plain hcl0 (ekSentEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_encodeVarint_placed_ok_x h_panic hshim halloc hrealloc s0 hcl0)
      (subroutine_ok_withStepInv_lscl hcl0 hauth_ok)
      (etv_memcpy_placed_ok hmc)
      (subroutine_ok_withStepInv_lscl hcl0 hpolyEnc_ok)
      (subroutine_ok_withStepInv_lscl hcl0 hpolyDec_ok) v)
    (fun s0 st1 hcl0 v => step_encodeToVec_v1_noHeaderReceived_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
      (etv_subroutine_ok_placed_of_plain hcl0 (noHeaderReceivedEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_subroutine_ok_placed_of_plain hcl0 (polynomialDecoderEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_encodeVarint_placed_ok_x h_panic hshim halloc hrealloc s0 hcl0)
      (subroutine_ok_withStepInv_lscl hcl0 hauth_ok)
      (subroutine_ok_withStepInv_lscl hcl0 hpolyDec_ok) v)
    (fun s0 st1 hcl0 v => step_encodeToVec_v1_headerReceived_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
      (etv_subroutine_ok_placed_of_plain hcl0 (headerReceivedEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_subroutine_ok_placed_of_plain hcl0 (polynomialDecoderEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_encodeVarint_placed_ok_x h_panic hshim halloc hrealloc s0 hcl0)
      (subroutine_ok_withStepInv_lscl hcl0 hauth_ok)
      (etv_memcpy_placed_ok hmc)
      (subroutine_ok_withStepInv_lscl hcl0 hpolyDec_ok) v)
    (fun s0 st1 hcl0 v => step_encodeToVec_v1_ekReceivedCt1Sampled_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
      (etv_subroutine_ok_placed_of_plain hcl0 (ct1SentEkReceivedEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_subroutine_ok_placed_of_plain hcl0 (polynomialEncoderEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_encodeVarint_placed_ok_x h_panic hshim halloc hrealloc s0 hcl0)
      (subroutine_ok_withStepInv_lscl hcl0 hauth_ok)
      (etv_memcpy_placed_ok hmc)
      (subroutine_ok_withStepInv_lscl hcl0 hpolyEnc_ok) v)
    (fun s0 st1 hcl0 v => step_encodeToVec_v1_ct2Sampled_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
      (etv_subroutine_ok_placed_of_plain hcl0 (ct2SentEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_subroutine_ok_placed_of_plain hcl0 (polynomialEncoderEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_encodeVarint_placed_ok_x h_panic hshim halloc hrealloc s0 hcl0)
      (subroutine_ok_withStepInv_lscl hcl0 hauth_ok)
      (subroutine_ok_withStepInv_lscl hcl0 hpolyEnc_ok) v)

theorem pqRatchetStateEncodeToVec_noOom_placed_ok_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hcp_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 313)
      (withLsCodeLoaded lsmpl (encodeChainParamsExactSpecOf doReserveStackX A lim)))
    (hed_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 317)
      (withLsCodeLoaded lsmpl (encodeEpochDirectionExactSpecOf doReserveStackX A lim)))
    (hauth_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 314)
      (withLsCodeLoaded lsmpl (authEncodeExactSpecOf doReserveStackX A lim)))
    (hpolyEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 316)
      (withLsCodeLoaded lsmpl (etvPolyEncoderBudgetExactSpecOf doReserveStackX A lim)))
    (hpolyDec_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 315)
      (withLsCodeLoaded lsmpl (etvPolyDecoderBudgetExactSpecOf doReserveStackX A lim)))
    (hekEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 318)
      (withLsCodeLoaded lsmpl (etvEkSentCt1ReceivedBudgetExactSpecOf doReserveStackX A lim)))
    (hct1SentEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 319)
      (withLsCodeLoaded lsmpl (etvCt1SentBudgetExactSpecOf doReserveStackX A lim))) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext))
      (blkPl_426).base
      (withLsRoLoaded lsmpl (withLsCodeLoaded lsmpl
        (pqRatchetStateEncodeToVecNoOomSpecOf doReserveStackX A lim))) :=
  pqRatchetStateEncodeToVec_noOom_placed_ok_of_variants
    h_panic hshim halloc hrealloc hmc
    hcp_ok hed_ok hpolyEnc_ok hpolyDec_ok hekEnc_ok hct1SentEnc_ok
    (fun s0 st1 hcl0 v => step_encodeToVec_v1_keysUnsampled_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
      (etv_subroutine_ok_placed_of_plain hcl0 (keysUnsampledEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_encodeVarint_placed_ok_x h_panic hshim halloc hrealloc s0 hcl0)
      (subroutine_ok_withStepInv_lscl hcl0 hauth_ok) v)
    (fun s0 st1 hcl0 v => step_encodeToVec_v1_keysSampled_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
      (etv_subroutine_ok_placed_of_plain hcl0 (headerSentEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_subroutine_ok_placed_of_plain hcl0 (polynomialEncoderEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_encodeVarint_placed_ok_x h_panic hshim halloc hrealloc s0 hcl0)
      (subroutine_ok_withStepInv_lscl hcl0 hauth_ok)
      (etv_memcpy_placed_ok hmc)
      (subroutine_ok_withStepInv_lscl hcl0 hpolyEnc_ok) v)
    (fun s0 st1 hcl0 v => step_encodeToVec_v1_headerSent_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
      (etv_subroutine_ok_placed_of_lscl hcl0 (chunkedHeaderSentEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_subroutine_ok_placed_of_plain hcl0 (ekSentEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_encodeVarint_placed_ok_x h_panic hshim halloc hrealloc s0 hcl0)
      (subroutine_ok_withStepInv_lscl hcl0 hauth_ok)
      (etv_memcpy_placed_ok hmc)
      (subroutine_ok_withStepInv_lscl hcl0 hpolyEnc_ok)
      (subroutine_ok_withStepInv_lscl hcl0 hpolyDec_ok) v)
    (fun s0 st1 hcl0 v => step_encodeToVec_v1_noHeaderReceived_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
      (etv_subroutine_ok_placed_of_plain hcl0 (noHeaderReceivedEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_subroutine_ok_placed_of_plain hcl0 (polynomialDecoderEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_encodeVarint_placed_ok_x h_panic hshim halloc hrealloc s0 hcl0)
      (subroutine_ok_withStepInv_lscl hcl0 hauth_ok)
      (subroutine_ok_withStepInv_lscl hcl0 hpolyDec_ok) v)
    (fun s0 st1 hcl0 v => step_encodeToVec_v1_headerReceived_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
      (etv_subroutine_ok_placed_of_plain hcl0 (headerReceivedEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_subroutine_ok_placed_of_plain hcl0 (polynomialDecoderEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_encodeVarint_placed_ok_x h_panic hshim halloc hrealloc s0 hcl0)
      (subroutine_ok_withStepInv_lscl hcl0 hauth_ok)
      (etv_memcpy_placed_ok hmc)
      (subroutine_ok_withStepInv_lscl hcl0 hpolyDec_ok) v)
    (fun s0 st1 hcl0 v => step_encodeToVec_v1_ekReceivedCt1Sampled_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
      (etv_subroutine_ok_placed_of_plain hcl0 (ct1SentEkReceivedEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_subroutine_ok_placed_of_plain hcl0 (polynomialEncoderEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_encodeVarint_placed_ok_x h_panic hshim halloc hrealloc s0 hcl0)
      (subroutine_ok_withStepInv_lscl hcl0 hauth_ok)
      (etv_memcpy_placed_ok hmc)
      (subroutine_ok_withStepInv_lscl hcl0 hpolyEnc_ok) v)
    (fun s0 st1 hcl0 v => step_encodeToVec_v1_ct2Sampled_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
      (etv_subroutine_ok_placed_of_plain hcl0 (ct2SentEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_subroutine_ok_placed_of_plain hcl0 (polynomialEncoderEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_encodeVarint_placed_ok_x h_panic hshim halloc hrealloc s0 hcl0)
      (subroutine_ok_withStepInv_lscl hcl0 hauth_ok)
      (subroutine_ok_withStepInv_lscl hcl0 hpolyEnc_ok) v)

/-- Top-level `subroutine_ok` for `PqRatchetState::encode_to_vec` (`Block 426`) discharging
`PqRatchetStateEncodeToVecPinnedPlacedOkExt A lim ext` from callee contracts. -/
theorem pqRatchetStateEncodeToVec_pinned_placed_ok_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hcp_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 313)
      (withLsCodeLoaded lsmpl (encodeChainParamsExactSpecOf doReserveStackX A lim)))
    (hed_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 317)
      (withLsCodeLoaded lsmpl (encodeEpochDirectionExactSpecOf doReserveStackX A lim)))
    (hauth_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 314)
      (withLsCodeLoaded lsmpl (authEncodeExactSpecOf doReserveStackX A lim)))
    (hpolyEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 316)
      (withLsCodeLoaded lsmpl (etvPolyEncoderBudgetExactSpecOf doReserveStackX A lim)))
    (hpolyDec_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 315)
      (withLsCodeLoaded lsmpl (etvPolyDecoderBudgetExactSpecOf doReserveStackX A lim)))
    (hekEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 318)
      (withLsCodeLoaded lsmpl (etvEkSentCt1ReceivedBudgetExactSpecOf doReserveStackX A lim)))
    (hct1SentEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 319)
      (withLsCodeLoaded lsmpl (etvCt1SentBudgetExactSpecOf doReserveStackX A lim))) :
    PqRatchetStateEncodeToVecPinnedPlacedOkExt A lim ext :=
  pqRatchetStateEncodeToVec_pinned_placed_ok_of_variants
    h_panic hshim halloc hrealloc hmc
    hcp_ok hed_ok hpolyEnc_ok hpolyDec_ok hekEnc_ok hct1SentEnc_ok
    (fun s0 st1 hcl0 v => step_encodeToVec_v1_keysUnsampled_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
      (etv_subroutine_ok_placed_of_plain hcl0 (keysUnsampledEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_encodeVarint_placed_ok_x h_panic hshim halloc hrealloc s0 hcl0)
      (subroutine_ok_withStepInv_lscl hcl0 hauth_ok) v)
    (fun s0 st1 hcl0 v => step_encodeToVec_v1_keysSampled_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
      (etv_subroutine_ok_placed_of_plain hcl0 (headerSentEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_subroutine_ok_placed_of_plain hcl0 (polynomialEncoderEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_encodeVarint_placed_ok_x h_panic hshim halloc hrealloc s0 hcl0)
      (subroutine_ok_withStepInv_lscl hcl0 hauth_ok)
      (etv_memcpy_placed_ok hmc)
      (subroutine_ok_withStepInv_lscl hcl0 hpolyEnc_ok) v)
    (fun s0 st1 hcl0 v => step_encodeToVec_v1_headerSent_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
      (etv_subroutine_ok_placed_of_lscl hcl0 (chunkedHeaderSentEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_subroutine_ok_placed_of_plain hcl0 (ekSentEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_encodeVarint_placed_ok_x h_panic hshim halloc hrealloc s0 hcl0)
      (subroutine_ok_withStepInv_lscl hcl0 hauth_ok)
      (etv_memcpy_placed_ok hmc)
      (subroutine_ok_withStepInv_lscl hcl0 hpolyEnc_ok)
      (subroutine_ok_withStepInv_lscl hcl0 hpolyDec_ok) v)
    (fun s0 st1 hcl0 v => step_encodeToVec_v1_noHeaderReceived_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
      (etv_subroutine_ok_placed_of_plain hcl0 (noHeaderReceivedEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_subroutine_ok_placed_of_plain hcl0 (polynomialDecoderEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_encodeVarint_placed_ok_x h_panic hshim halloc hrealloc s0 hcl0)
      (subroutine_ok_withStepInv_lscl hcl0 hauth_ok)
      (subroutine_ok_withStepInv_lscl hcl0 hpolyDec_ok) v)
    (fun s0 st1 hcl0 v => step_encodeToVec_v1_headerReceived_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
      (etv_subroutine_ok_placed_of_plain hcl0 (headerReceivedEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_subroutine_ok_placed_of_plain hcl0 (polynomialDecoderEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_encodeVarint_placed_ok_x h_panic hshim halloc hrealloc s0 hcl0)
      (subroutine_ok_withStepInv_lscl hcl0 hauth_ok)
      (etv_memcpy_placed_ok hmc)
      (subroutine_ok_withStepInv_lscl hcl0 hpolyDec_ok) v)
    (fun s0 st1 hcl0 v => step_encodeToVec_v1_ekReceivedCt1Sampled_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
      (etv_subroutine_ok_placed_of_plain hcl0 (ct1SentEkReceivedEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_subroutine_ok_placed_of_plain hcl0 (polynomialEncoderEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_encodeVarint_placed_ok_x h_panic hshim halloc hrealloc s0 hcl0)
      (subroutine_ok_withStepInv_lscl hcl0 hauth_ok)
      (etv_memcpy_placed_ok hmc)
      (subroutine_ok_withStepInv_lscl hcl0 hpolyEnc_ok) v)
    (fun s0 st1 hcl0 v => step_encodeToVec_v1_ct2Sampled_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
      (etv_subroutine_ok_placed_of_plain hcl0 (ct2SentEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_subroutine_ok_placed_of_plain hcl0 (polynomialEncoderEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_encodeVarint_placed_ok_x h_panic hshim halloc hrealloc s0 hcl0)
      (subroutine_ok_withStepInv_lscl hcl0 hauth_ok)
      (subroutine_ok_withStepInv_lscl hcl0 hpolyEnc_ok) v)

/-- Top-level `subroutine_ok` for `PqRatchetState::encode_to_vec` (`Block 426`) discharging
`PqRatchetStateEncodeToVecPlacedOkExt A lim ext` from callee contracts. -/
theorem pqRatchetStateEncodeToVec_placed_ok_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hcp_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 313)
      (withLsCodeLoaded lsmpl (encodeChainParamsExactSpecOf doReserveStackX A lim)))
    (hed_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 317)
      (withLsCodeLoaded lsmpl (encodeEpochDirectionExactSpecOf doReserveStackX A lim)))
    (hauth_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 314)
      (withLsCodeLoaded lsmpl (authEncodeExactSpecOf doReserveStackX A lim)))
    (hpolyEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 316)
      (withLsCodeLoaded lsmpl (etvPolyEncoderBudgetExactSpecOf doReserveStackX A lim)))
    (hpolyDec_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 315)
      (withLsCodeLoaded lsmpl (etvPolyDecoderBudgetExactSpecOf doReserveStackX A lim)))
    (hekEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 318)
      (withLsCodeLoaded lsmpl (etvEkSentCt1ReceivedBudgetExactSpecOf doReserveStackX A lim)))
    (hct1SentEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 319)
      (withLsCodeLoaded lsmpl (etvCt1SentBudgetExactSpecOf doReserveStackX A lim))) :
    PqRatchetStateEncodeToVecPlacedOkExt A lim ext :=
  pqRatchetStateEncodeToVec_placed_ok_of_pinned
    (pqRatchetStateEncodeToVec_pinned_placed_ok_of_contracts
      h_panic hshim halloc hrealloc hmc
      hcp_ok hed_ok hauth_ok hpolyEnc_ok hpolyDec_ok hekEnc_ok hct1SentEnc_ok)

/-! ## 4. `withLsCodeLoaded` Bridges & Callee Convenience Wrappers -/

private theorem lift_withLsCodeLoaded_bridge [LibsignalPlacement] {α β : Type}
    {prog : Program} {entry : BitVec 64} {spec1 : Spec α} {spec2 : Spec β}
    (hbr : ∀ s0 : State, subroutine_ok prog entry (withStepInv s0 spec1) →
      subroutine_ok prog entry (withStepInv s0 spec2))
    (hok : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec1)) :
    subroutine_ok prog entry (withLsCodeLoaded lsmpl spec2) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  have h1 : subroutine_ok prog entry (withStepInv s0 spec1) :=
    subroutine_ok_withStepInv_lscl hcl0 hok
  have h2 := hbr s0 h1
  have hpre2 : s0.mem ⊨ (withStepInv s0 spec2).pre x s0 ∗ R := by
    dsimp only [withStepInv]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨StepInv.refl s0, hpre⟩
  exact h2.mono_outcome x R s0 hpc hrun hpre2 hsp fun _ hout => hout

theorem etv_encodeChainParams_exact_of_lscl [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 176 < 2 ^ 64) {M : AllocCostModel} {prog : Program} {call_pc : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hcp_ok : subroutine_ok prog call_pc (withLsCodeLoaded lsmpl (encodeChainParamsSpecOf resStack A lim))) :
    subroutine_ok prog call_pc (withLsCodeLoaded lsmpl (encodeChainParamsExactSpecOf resStack A lim)) :=
  lift_withLsCodeLoaded_bridge (fun _ => etv_encodeChainParams_exact_of_spec (resStack := resStack) hres) hcp_ok

theorem etv_encodeEpochDirection_exact_of_lscl [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 176 < 2 ^ 64) {M : AllocCostModel} {prog : Program} {call_pc : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hed_ok : subroutine_ok prog call_pc
      (withLsCodeLoaded lsmpl (encodeEpochDirectionPinnedSpecOf resStack A lim))) :
    subroutine_ok prog call_pc
      (withLsCodeLoaded lsmpl (encodeEpochDirectionExactSpecOf resStack A lim)) :=
  lift_withLsCodeLoaded_bridge (fun _ => etv_encodeEpochDirection_exact_of_spec (resStack := resStack) hres) hed_ok

theorem etv_authEncode_exact_of_lscl [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 176 < 2 ^ 64) {M : AllocCostModel} {prog : Program} {call_pc : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hauth_ok : subroutine_ok prog call_pc
      (withLsCodeLoaded lsmpl (authEncodePinnedSpecOf resStack A lim))) :
    subroutine_ok prog call_pc
      (withLsCodeLoaded lsmpl (authEncodeExactSpecOf resStack A lim)) :=
  lift_withLsCodeLoaded_bridge (fun _ => etv_authEncode_exact_of_spec (resStack := resStack) hres) hauth_ok

theorem pqRatchetStateEncodeToVec_pinned_placed_ok_of_raw_callees [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hcp_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 313)
      (withLsCodeLoaded lsmpl (encodeChainParamsSpecOf doReserveStackX A lim)))
    (hed_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 317)
      (withLsCodeLoaded lsmpl (encodeEpochDirectionPinnedSpecOf doReserveStackX A lim)))
    (hauth_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 314)
      (withLsCodeLoaded lsmpl (authEncodePinnedSpecOf doReserveStackX A lim)))
    (hpolyEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 316)
      (withLsCodeLoaded lsmpl (encodePolyEncoderExactSpecOf doReserveStackX A lim)))
    (hpolyDec_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 315)
      (withLsCodeLoaded lsmpl (encodePolyDecoderExactSpecOf doReserveStackX A lim)))
    (hekEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 318)
      (withLsCodeLoaded lsmpl (ekSentCt1ReceivedEncodePinnedSpecOf doReserveStackX A lim)))
    (hct1SentEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 319)
      (withLsCodeLoaded lsmpl (ct1SentEncodePinnedSpecOf doReserveStackX A lim))) :
    PqRatchetStateEncodeToVecPinnedPlacedOkExt A lim ext := by
  have hauth_exact := etv_authEncode_exact_of_lscl (by decide) hauth_ok
  exact ProofPlacedBudget.pqRatchetStateEncodeToVec_pinned_placed_ok_of_raw_callees
    h_panic hshim halloc hrealloc hmc
    hcp_ok hed_ok hpolyEnc_ok hpolyDec_ok hekEnc_ok hct1SentEnc_ok
    (fun s0 st1 hcl0 v => step_encodeToVec_v1_keysUnsampled_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
      (etv_subroutine_ok_placed_of_plain hcl0 (keysUnsampledEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_encodeVarint_placed_ok_x h_panic hshim halloc hrealloc s0 hcl0)
      (subroutine_ok_withStepInv_lscl hcl0 hauth_exact) v)
    (fun s0 st1 hcl0 v => step_encodeToVec_v1_keysSampled_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
      (etv_subroutine_ok_placed_of_plain hcl0 (headerSentEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_subroutine_ok_placed_of_plain hcl0 (polynomialEncoderEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_encodeVarint_placed_ok_x h_panic hshim halloc hrealloc s0 hcl0)
      (subroutine_ok_withStepInv_lscl hcl0 hauth_exact)
      (etv_memcpy_placed_ok hmc)
      (etv_polyEncoderEncode_budget_exact_of_spec (subroutine_ok_withStepInv_lscl hcl0 hpolyEnc_ok)) v)
    (fun s0 st1 hcl0 v => step_encodeToVec_v1_headerSent_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
      (etv_subroutine_ok_placed_of_lscl hcl0 (chunkedHeaderSentEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_subroutine_ok_placed_of_plain hcl0 (ekSentEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_encodeVarint_placed_ok_x h_panic hshim halloc hrealloc s0 hcl0)
      (subroutine_ok_withStepInv_lscl hcl0 hauth_exact)
      (etv_memcpy_placed_ok hmc)
      (etv_polyEncoderEncode_budget_exact_of_spec (subroutine_ok_withStepInv_lscl hcl0 hpolyEnc_ok))
      (etv_polyDecoderEncode_budget_exact_of_spec (subroutine_ok_withStepInv_lscl hcl0 hpolyDec_ok)) v)
    (fun s0 st1 hcl0 v => step_encodeToVec_v1_noHeaderReceived_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
      (etv_subroutine_ok_placed_of_plain hcl0 (noHeaderReceivedEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_subroutine_ok_placed_of_plain hcl0 (polynomialDecoderEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_encodeVarint_placed_ok_x h_panic hshim halloc hrealloc s0 hcl0)
      (subroutine_ok_withStepInv_lscl hcl0 hauth_exact)
      (etv_polyDecoderEncode_budget_exact_of_spec (subroutine_ok_withStepInv_lscl hcl0 hpolyDec_ok)) v)
    (fun s0 st1 hcl0 v => step_encodeToVec_v1_headerReceived_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
      (etv_subroutine_ok_placed_of_plain hcl0 (headerReceivedEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_subroutine_ok_placed_of_plain hcl0 (polynomialDecoderEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_encodeVarint_placed_ok_x h_panic hshim halloc hrealloc s0 hcl0)
      (subroutine_ok_withStepInv_lscl hcl0 hauth_exact)
      (etv_memcpy_placed_ok hmc)
      (etv_polyDecoderEncode_budget_exact_of_spec (subroutine_ok_withStepInv_lscl hcl0 hpolyDec_ok)) v)
    (fun s0 st1 hcl0 v => step_encodeToVec_v1_ekReceivedCt1Sampled_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
      (etv_subroutine_ok_placed_of_plain hcl0 (ct1SentEkReceivedEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_subroutine_ok_placed_of_plain hcl0 (polynomialEncoderEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_encodeVarint_placed_ok_x h_panic hshim halloc hrealloc s0 hcl0)
      (subroutine_ok_withStepInv_lscl hcl0 hauth_exact)
      (etv_memcpy_placed_ok hmc)
      (etv_polyEncoderEncode_budget_exact_of_spec (subroutine_ok_withStepInv_lscl hcl0 hpolyEnc_ok)) v)
    (fun s0 st1 hcl0 v => step_encodeToVec_v1_ct2Sampled_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
      (etv_subroutine_ok_placed_of_plain hcl0 (ct2SentEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_subroutine_ok_placed_of_plain hcl0 (polynomialEncoderEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
      (etv_encodeVarint_placed_ok_x h_panic hshim halloc hrealloc s0 hcl0)
      (subroutine_ok_withStepInv_lscl hcl0 hauth_exact)
      (etv_polyEncoderEncode_budget_exact_of_spec (subroutine_ok_withStepInv_lscl hcl0 hpolyEnc_ok)) v)

theorem pqRatchetStateEncodeToVec_placed_ok_of_raw_callees [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hcp_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 313)
      (withLsCodeLoaded lsmpl (encodeChainParamsSpecOf doReserveStackX A lim)))
    (hed_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 317)
      (withLsCodeLoaded lsmpl (encodeEpochDirectionPinnedSpecOf doReserveStackX A lim)))
    (hauth_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 314)
      (withLsCodeLoaded lsmpl (authEncodePinnedSpecOf doReserveStackX A lim)))
    (hpolyEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 316)
      (withLsCodeLoaded lsmpl (encodePolyEncoderExactSpecOf doReserveStackX A lim)))
    (hpolyDec_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 315)
      (withLsCodeLoaded lsmpl (encodePolyDecoderExactSpecOf doReserveStackX A lim)))
    (hekEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 318)
      (withLsCodeLoaded lsmpl (ekSentCt1ReceivedEncodePinnedSpecOf doReserveStackX A lim)))
    (hct1SentEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 319)
      (withLsCodeLoaded lsmpl (ct1SentEncodePinnedSpecOf doReserveStackX A lim))) :
    PqRatchetStateEncodeToVecPlacedOkExt A lim ext :=
  pqRatchetStateEncodeToVec_placed_ok_of_pinned
    (pqRatchetStateEncodeToVec_pinned_placed_ok_of_raw_callees
      h_panic hshim halloc hrealloc hmc
      hcp_ok hed_ok hauth_ok hpolyEnc_ok hpolyDec_ok hekEnc_ok hct1SentEnc_ok)

end LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.FinalPlacedBudget

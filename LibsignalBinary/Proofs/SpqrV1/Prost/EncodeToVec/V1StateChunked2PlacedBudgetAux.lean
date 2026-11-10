/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodeToVecCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked1PlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked2
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked2Placed
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.ProtoReprCodeSym
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `[LibsignalPlacement]` Phase 2c (Part 2a): `V1State::encode_raw` Variants `idx = 0, 2` (`Block 426`)

Proves `step_encodeToVec_v1_keysUnsampled_placed` (`idx = 0`), the shared `memcpy` slice helper
`etv2_step_memcpy_slice_placed`, and `step_encodeToVec_v1_headerSent_placed` (`idx = 2`) in `Block 426`,
threading `A.pool lim st`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked2PlacedBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.RustHeap (RustAlloc vecHeader vecU8At)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalSpqrV1
  (PolynomialDecoder PolynomialEncoder ProtoAuthenticator V1State)
open CryptoVerification.LibsignalSpqrV1.Proto
  (encodeBytesField encodeMessage encodeOptMessage encodeUint64Field encodeVarint)
open CryptoVerification.SpqrV1.ProtoRepr
  (ChunkedHeaderSentPBGhost Unchunked2PBGhost Unchunked3PBGhost
   chunkedHeaderSentPBEncodedLen chunkedHeaderSentPBPinnedAt
   ekSentPBEncodedLen ekSentPBEncodedLen_eq_proto ekSentPBPinnedAt
   keysUnsampledPBEncodedLen keysUnsampledPBPinnedAt
   noneCap2 optAuthCap optAuthenticatorPBPinnedAt optAuthenticatorPBPinnedAt_eq
   optEkSentPBPinnedAt optKeysUnsampledPBPinnedAt
   optPolynomialDecoderPBPinnedAt optPolynomialEncoderPBPinnedAt
   unchunked2PinnedAt unchunked3PinnedAt
   v1StateInnerPayloadEncodedLen v1StatePBEncodedLen varintLen)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (hwVarintLen_bvShift_eq_ofNat_varintLen_norm hwVarintLen_eq_ofNat_varintLen_norm
   noneCap_add_one_beq_zero noneCap_add_one_bne_zero
   ofNat_countLeadingZeros_32 ofNat_countLeadingZeros_64 ofNat_length_beq_zero_of_lt
   ule_self_64 ule_zero_64 ult_self_64 ult_zero_64
   vecU8At_eq_header_sep_buf vecU8Buf
   zeroExtend64_beq_zero32 zext64_truncate32)
open CryptoVerification.SpqrV1.Prost.EncodeToVec
  (StepInv blkPC_426 blkPl_426
   cap_beq_len_false_of_lt elem_len_ult_spare_false_of_le
   encodeToVecCalleeStackOf encodeVarint_length_pos
   etv2_bv_msgFieldLen etv2_encodeBytesField_3_eq
   etv2_encodeInnerState_headerSent_eq etv2_encodeInnerState_keysUnsampled_eq
   etv2_encodeOptEkSent_some_eq etv2_encodeOptKeysUnsampled_some_eq
   etv2_encodeUint64Field_1_eq etv2_optAuth_cap_bounds etv2_optEkSentPBPinnedAt_cap_bounds
   noneCap2_add_two_beq_zero noneCap2_add_two_bne_zero
   noneCap3 noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
   noneCap_add_two_beq_zero noneCap_add_two_bne_zero
   optEkSentCap optEkSentPBPinnedAt_eq optEkSentRest
   optKeysUnsampledCap optKeysUnsampledPBPinnedAt_cap_bounds optKeysUnsampledPBPinnedAt_eq
   optKeysUnsampledRest optPolyDecCap optPolyEncCap
   optPolynomialDecoderPBPinnedAt_cap_bounds optPolynomialDecoderPBPinnedAt_eq
   optPolynomialEncoderPBPinnedAt_cap_bounds optPolynomialEncoderPBPinnedAt_eq
   vecU8At_expose_one vecU8At_expose_slice vecU8At_pack_one vecU8At_pack_slice
   vecU8Buf_eq_of_nonempty withStepInv)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsPlacedBudget
  (sepWP_done_tpidr sepWP_done_vm sepWPp_of_sepWP_cs_vm)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhaseBudget
  (authEncodeExactSpecOf encodeVarintExactSpecOf etvMemcpyRegionSpec
   step_etv_encode_auth_call_prog step_etv_encode_varint_call_prog step_etv_memcpy_call_prog)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonBudget
  (leafEncLen16Spec leafEncLen48Spec)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonPlacedBudget
  (etvPolyDecoderBudgetExactSpecOf etvPolyEncoderBudgetExactSpecOf
   step_etv_chunked_encLen48_call_placed step_etv_encode_polyEncoder_budget_call_placed
   step_etv_leaf_encLen16_call_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked1PlacedBudgetAux
  (sepWPp_extract_pure sepWPp_extract_vecU8At_bounds step_encodeToVec_tail_2732_polyDec3_placed)

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

/-! ## 1. Variant `idx = 0`: `.keysUnsampled` (`+1896 .. +1976`, `+3168 .. +3352`) -/

theorem step_encodeToVec_v1_keysUnsampled_placed [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (H : String → Option (State → State)) {s0 s : State}
    (hkuLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 400)
      (withStepInv s0 (leafEncLen16Spec (keysUnsampledPBPinnedAt A.repAlloc) keysUnsampledPBEncodedLen)))
    (hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hauthEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 314)
      (withStepInv s0 (authEncodeExactSpecOf resStack A lim)))
    (a sp cap ptr : BitVec 64) (g : Unchunked2PBGhost) (v : V1State.Chunked.KeysUnsampled)
    (bs : List (BitVec 8))
    (hv_len : v1StatePBEncodedLen ⟨some (.keysUnsampled v)⟩ < 2 ^ 64)
    (hfit : bs.length + (V1State.InnerState.encode (.keysUnsampled v)).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_426).base + 1896#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = a) (hinv0 : StepInv s0 s)
    (hP : P = (optKeysUnsampledPBPinnedAt A.repAlloc g (a + 136#64) v.uc ∗
      vecU8At A.repAlloc (sp - 120#64) cap ptr bs ∗ A.pool lim st s ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_426).base + 1808#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm
        ((optKeysUnsampledPBPinnedAt A.repAlloc g (a + 136#64) v.uc ∗
          vecU8At A.repAlloc (sp - 120#64) cap ptr (bs ++ V1State.InnerState.encode (.keysUnsampled v)) ∗
          A.pool lim st sm ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q Qp oom := by
  subst hP
  rw [etv2_encodeInnerState_keysUnsampled_eq] at hfit
  simp only [List.length_append, List.length_singleton] at hfit
  have ⟨h112, h104⟩ : (sp - 120#64) + 8#64 = sp - 112#64 ∧ (sp - 120#64) + 16#64 = sp - 104#64 :=
    ⟨by bv_omega, by bv_omega⟩
  refine sepWPp_extract_pure
    ((optKeysUnsampledCap g v.uc + 2#64 == 0#64) = !v.uc.isSome ∧
     (optKeysUnsampledCap g v.uc + 2#64 != 0#64) = v.uc.isSome)
    (fun R' hm => optKeysUnsampledPBPinnedAt_cap_bounds (p := a + 136#64)
      (R := vecU8At A.repAlloc (sp - 120#64) cap ptr bs ∗ A.pool lim st s ∗
        stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
      (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm))
    fun ⟨hcap_uc_beq, hcap_uc_bne⟩ => ?_
  cases huc : v.uc with
  | none =>
    have huc_eq : v = ⟨none⟩ := by cases v; subst huc; rfl
    subst huc_eq
    simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
    rw [optKeysUnsampledPBPinnedAt_eq A.repAlloc g (a + 136#64) none]
    have hvar0 : encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.keysUnsampled ⟨none⟩))) = [0x00#8] := rfl
    have hlt1 : bs.length < cap.toNat := by change bs.length + (1 + 1) + 0 ≤ cap.toNat at hfit; omega
    have hlt2 : (bs ++ [0x0a#8]).length < cap.toNat := by
      simp only [List.length_append, List.length_singleton]; change bs.length + (1 + 1) + 0 ≤ cap.toNat at hfit; omega
    refine sepWPp_extract_vecU8At_bounds (v := sp - 120#64) (cap := cap) (ptr := ptr) (bs := bs)
      (F := ((a + 136#64) ↦₆₄ optKeysUnsampledCap g none) ∗ optKeysUnsampledRest A.repAlloc g (a + 136#64) none ∗
        A.pool lim st s ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F)
      (by sep_ac_rfl) fun _ hcap hptr => ?_
    have hbeq1 := cap_beq_len_false_of_lt hlt1 hcap
    have hbeq2 : (cap == BitVec.ofNat 64 bs.length + 1#64) = false := by
      simpa only [List.length_append, List.length_singleton, BitVec.ofNat_add] using cap_beq_len_false_of_lt hlt2 hcap
    rw [vecU8At_expose_one A.repAlloc (sp - 120#64) cap ptr bs hlt1 hcap hptr, h112, h104]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun b0 => ?_
    apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 1944#64)
    by_vm_steps
      wp_steps
      apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv1
      have hpack1 := vecU8At_pack_one A.repAlloc (sp - 120#64) cap ptr bs 0x0a#8 hlt1 hcap hptr
      rw [h112, h104] at hpack1
      refine SepWPp.weaken_pre
        (P' := ((a + 136#64) ↦₆₄ optKeysUnsampledCap g none) ∗ optKeysUnsampledRest A.repAlloc g (a + 136#64) none ∗
          vecU8At A.repAlloc (sp - 120#64) cap ptr (bs ++ [0x0a#8]) ∗ A.pool lim st s ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F)
        (by rw [← hpack1]; exact Entails.of_eq (by sep_ac_rfl)) ?_
      rw [vecU8At_expose_one A.repAlloc (sp - 120#64) cap ptr (bs ++ [0x0a#8]) hlt2 hcap hptr, h112, h104]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPp.exists_elim fun b1 => ?_
      have hlen_add1 : BitVec.ofNat 64 (bs ++ [0x0a#8]).length = BitVec.ofNat 64 bs.length + 1#64 := by
        simp [List.length_append, BitVec.ofNat_add]
      rw [hlen_add1]
      apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 1808#64)
      by_vm_steps
        wp_steps
        apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv2
        have hpool12 := (A.pool_of_vmPreserved (lim := lim) (st := st) (hinv1.2.trans hinv2.2)).symm
        have hpack2 := vecU8At_pack_one A.repAlloc (sp - 120#64) cap ptr (bs ++ [0x0a#8]) 0x00#8 hlt2 hcap hptr
        rw [h112, h104, hlen_add1] at hpack2
        rw [show BitVec.ofNat 64 bs.length + 1#64 + 1#64 = BitVec.ofNat 64 bs.length + 2#64 by bv_omega] at hpack2
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ((hinv0.trans hinv1.1).trans hinv2.1))
        rw [optKeysUnsampledPBPinnedAt_eq A.repAlloc g (a + 136#64), hpack2, hpool12,
          etv2_encodeInnerState_keysUnsampled_eq, hvar0]
        simp only [encodeOptMessage, List.append_nil, List.append_assoc]; sep_ac_rfl
  | some u =>
    simp only [huc, Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
    rw [optKeysUnsampledPBPinnedAt_eq A.repAlloc g (a + 136#64) (some u)]
    have hpay_eq : v1StateInnerPayloadEncodedLen (.keysUnsampled v) =
        1 + varintLen (BitVec.ofNat 64 (keysUnsampledPBEncodedLen u)) + keysUnsampledPBEncodedLen u := by
      rw [v1StateInnerPayloadEncodedLen, huc]; rfl
    have hpay_lt : 1 + varintLen (BitVec.ofNat 64 (keysUnsampledPBEncodedLen u)) + keysUnsampledPBEncodedLen u < 2 ^ 64 := by
      dsimp only [v1StatePBEncodedLen] at hv_len; rw [hpay_eq] at hv_len; omega
    have hu_lt : keysUnsampledPBEncodedLen u < 2 ^ 64 := by omega
    obtain ⟨hbv_sum, hbv_ule, hbv_ult⟩ := etv2_bv_msgFieldLen hpay_lt
    have hlt1 : bs.length < cap.toNat := by omega
    refine sepWPp_extract_vecU8At_bounds (v := sp - 120#64) (cap := cap) (ptr := ptr) (bs := bs)
      (F := ((a + 136#64) ↦₆₄ optKeysUnsampledCap g (some u)) ∗
        optKeysUnsampledRest A.repAlloc g (a + 136#64) (some u) ∗
        A.pool lim st s ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F)
      (by sep_ac_rfl) fun _ hcap hptr => ?_
    have hbeq1 := cap_beq_len_false_of_lt hlt1 hcap
    rw [vecU8At_expose_one A.repAlloc (sp - 120#64) cap ptr bs hlt1 hcap hptr, h112, h104]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun b0 => ?_
    apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 400)
    by_vm_steps
      wp_steps
      apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv1
      have hpack1 := vecU8At_pack_one A.repAlloc (sp - 120#64) cap ptr bs 0x0a#8 hlt1 hcap hptr
      rw [h112, h104] at hpack1
      have hku_pin : ((a + 136#64) ↦₆₄ optKeysUnsampledCap g (some u)) ∗
          optKeysUnsampledRest A.repAlloc g (a + 136#64) (some u) =
          keysUnsampledPBPinnedAt A.repAlloc g (a + 136#64) u := by
        simpa only [optKeysUnsampledPBPinnedAt] using
          (optKeysUnsampledPBPinnedAt_eq A.repAlloc g (a + 136#64) (some u)).symm
      refine step_etv_leaf_encLen16_call_placed hres (keysUnsampledPBPinnedAt A.repAlloc)
        keysUnsampledPBEncodedLen hkuLen
        (a + 136#64) sp ((blkPl_426).base + 3176#64) g u hu_lt
        (F := vecU8At A.repAlloc (sp - 120#64) cap ptr (bs ++ [0x0a#8]) ∗ A.pool lim st s ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (hinv0.trans hinv1.1) (by rw [← hpack1, ← hku_pin]; sep_ac_rfl) ?_
      intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1 hcsm1 hinv_m1 hvm_m1
      rcases hcsm1 with ⟨hm19, hm20, _, _, _, _, _, _, hm27, _, hmfp, _⟩
      simp only [arm64_norm, hx20] at hm19 hm20 hm27 hmfp
      apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 292)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv2
      set bs1 := (bs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.keysUnsampled v)))
      have hfit_var1 : (bs ++ [0x0a#8]).length +
          (encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.keysUnsampled v)))).length ≤ cap.toNat := by
        simp only [List.length_append, List.length_singleton]; omega
      refine step_etv_encode_varint_call_prog A lim st hvarint
        (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.keysUnsampled v)))
        (sp - 120#64) cap ptr sp ((blkPl_426).base + 3224#64) (bs ++ [0x0a#8]) hfit_var1
        (F := keysUnsampledPBPinnedAt A.repAlloc g (a + 136#64) u ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
        (by rw [hpay_eq]; simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hinv_m1.trans hinv2.1)
        (by rw [A.pool_of_vmPreserved (lim := lim) (st := st) (hinv1.2.trans (hvm_m1.trans hinv2.2))]; sep_ac_rfl) ?_
      intro sm2 hpcm2 hrunm2 hspm2 htrm2 hcsm2 hinv_m2
      rcases hcsm2 with ⟨hm2_19, hm2_20, _, _, _, _, _, _, hm2_27, _, hm2_fp, _⟩
      simp only [arm64_norm, hm19, hm20, hm27, hmfp] at hm2_19 hm2_20 hm2_27 hm2_fp
      rw [huc, etv2_encodeOptKeysUnsampled_some_eq] at hfit
      simp only [List.length_append, List.length_singleton] at hfit
      have hlt2 : bs1.length < cap.toNat := by dsimp only [bs1]; simp only [List.length_append, List.length_singleton]; omega
      have hbeq2 := cap_beq_len_false_of_lt hlt2 hcap
      rw [vecU8At_expose_one A.repAlloc (sp - 120#64) cap ptr bs1 hlt2 hcap hptr, h112, h104]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPp.exists_elim fun b1 => ?_
      apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 400)
      by_vm_steps
        wp_steps
        apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv3
        have hpack2 := vecU8At_pack_one A.repAlloc (sp - 120#64) cap ptr bs1 0x0a#8 hlt2 hcap hptr
        rw [h112, h104] at hpack2
        refine step_etv_leaf_encLen16_call_placed hres (keysUnsampledPBPinnedAt A.repAlloc)
          keysUnsampledPBEncodedLen hkuLen
          (a + 136#64) sp ((blkPl_426).base + 3268#64) g u hu_lt
          (F := vecU8At A.repAlloc (sp - 120#64) cap ptr (bs1 ++ [0x0a#8]) ∗ A.pool lim st sm2 ∗ F)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
          (hinv_m2.trans hinv3.1) (by rw [← hpack2]; sep_ac_rfl) ?_
        intro sm3 hpcm3 hrunm3 hspm3 htrm3 hx0m3 hcsm3 hinv_m3 hvm_m3
        rcases hcsm3 with ⟨hm3_19, hm3_20, _, _, _, _, _, _, hm3_27, _, hm3_fp, _⟩
        simp only [arm64_norm, hm2_19, hm2_20, hm2_27, hm2_fp] at hm3_19 hm3_20 hm3_27 hm3_fp
        apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 292)
        wp_steps
        apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv4
        set bs2 := (bs1 ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 (keysUnsampledPBEncodedLen u))
        have hfit_var2 : (bs1 ++ [0x0a#8]).length +
            (encodeVarint (BitVec.ofNat 64 (keysUnsampledPBEncodedLen u))).length ≤ cap.toNat := by
          dsimp only [bs1]; simp only [List.length_append, List.length_singleton]; omega
        refine step_etv_encode_varint_call_prog A lim st hvarint
          (BitVec.ofNat 64 (keysUnsampledPBEncodedLen u))
          (sp - 120#64) cap ptr sp ((blkPl_426).base + 3276#64) (bs1 ++ [0x0a#8]) hfit_var2
          (F := keysUnsampledPBPinnedAt A.repAlloc g (a + 136#64) u ∗ F)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hinv_m3.trans hinv4.1)
          (by rw [A.pool_of_vmPreserved (lim := lim) (st := st) (hinv3.2.trans (hvm_m3.trans hinv4.2))]; sep_ac_rfl) ?_
        intro sm4 hpcm4 hrunm4 hspm4 htrm4 hcsm4 hinv_m4
        rcases hcsm4 with ⟨hm4_19, hm4_20, _, _, _, _, _, _, hm4_27, _, hm4_fp, _⟩
        simp only [arm64_norm, hm3_19, hm3_20, hm3_27, hm3_fp] at hm4_19 hm4_20 hm4_27 hm4_fp
        dsimp only [keysUnsampledPBPinnedAt, unchunked2PinnedAt]
        have h136_48 : (a + 136#64) + 0x30#64 = a + 184#64 := by bv_omega
        rw [h136_48]
        refine sepWPp_extract_pure
          ((optAuthCap g u.auth + 1#64 == 0#64) = !u.auth.isSome ∧
           (optAuthCap g u.auth + 1#64 != 0#64) = u.auth.isSome)
          (fun R' hm => etv2_optAuth_cap_bounds (A := A.repAlloc) (p := a + 136#64)
            (R := ((a + 184#64) ↦₆₄ u.epoch) ∗ vecU8At A.repAlloc (sp - 120#64) cap ptr bs2 ∗ A.pool lim st sm4 ∗
              stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
            (Satisfies.mono (Entails.of_eq (by dsimp +zetaDelta only [bs2, bs1]; sep_ac_rfl)) hm))
          fun ⟨hcap_auth_beq, hcap_auth_bne⟩ => ?_
        set bs3 := bs2 ++ encodeUint64Field 1#32 u.epoch
        suffices h3328 : ∀ sm5 : State,
            sm5.pc = (blkPl_426).base + 3328#64 → sm5.status = .Running → sm5.sp = sp - 144#64 → sm5.trace = s0.trace →
            sm5.readReg64 .x19 = optKeysUnsampledCap g (some u) → sm5.readReg64 .x20 = a →
            sm5.readReg64 .x27 = s.readReg64 .x27 → sm5.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm5 →
            SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm5
              (((optAuthenticatorPBPinnedAt A.repAlloc g (a + 136#64) u.auth ∗ ((a + 184#64) ↦₆₄ u.epoch)) ∗
                vecU8At A.repAlloc (sp - 120#64) cap ptr bs3 ∗ A.pool lim st sm5 ∗
                stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
              Q Qp oom by
          cases hep : u.epoch == 0#64
          · have hfit_ep : bs2.length + 1 + (encodeVarint u.epoch).length ≤ cap.toNat := by
              rw [etv2_encodeUint64Field_1_eq, hep] at hfit; dsimp only [bs2, bs1]
              simp only [Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_singleton] at hfit ⊢; omega
            have hlt_ep : bs2.length < cap.toNat := by have := encodeVarint_length_pos u.epoch; omega
            have hbeq_ep := cap_beq_len_false_of_lt hlt_ep hcap
            rw [vecU8At_expose_one A.repAlloc (sp - 120#64) cap ptr bs2 hlt_ep hcap hptr, h112, h104]
            simp only [sepExists_sepConj_left, sepExists_sepConj_right]
            refine SepWPp.exists_elim fun b2 => ?_
            apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 292)
            by_vm_steps
              wp_steps
              apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, wp_norm, *])
              intro hinv5
              have hpool5 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv5.2).symm
              have hpack_ep := vecU8At_pack_one A.repAlloc (sp - 120#64) cap ptr bs2 0x08#8 hlt_ep hcap hptr
              rw [h112, h104] at hpack_ep
              refine step_etv_encode_varint_call_prog A lim st hvarint
                u.epoch (sp - 120#64) cap ptr sp ((blkPl_426).base + 3328#64) (bs2 ++ [0x08#8])
                (by simpa only [List.length_append, List.length_singleton] using hfit_ep)
                (F := (optAuthenticatorPBPinnedAt A.repAlloc g (a + 136#64) u.auth ∗ ((a + 184#64) ↦₆₄ u.epoch)) ∗ F)
                (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (hinv_m4.trans hinv5.1) (by rw [← hpack_ep, hpool5]) ?_
              intro sm5 hpcm5 hrunm5 hspm5 htrm5 hcsm5 hinv_m5
              rcases hcsm5 with ⟨hm5_19, hm5_20, _, _, _, _, _, _, hm5_27, _, hm5_fp, _⟩
              simp only [arm64_norm, hm4_19, hm4_20, hm4_27, hm4_fp] at hm5_19 hm5_20 hm5_27 hm5_fp
              refine SepWPp.weaken_pre (Entails.of_eq ?_)
                (h3328 sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_19 hm5_20 hm5_27 hm5_fp hinv_m5)
              simp +zetaDelta only [bs3, bs2, bs1, etv2_encodeUint64Field_1_eq, hep, Bool.false_eq_true, ↓reduceIte,
                List.append_assoc]; sep_ac_rfl
          · apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 3328#64)
            wp_steps
            apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, wp_norm, *])
            intro hinv5
            have hpool5 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv5.2).symm
            refine SepWPp.weaken_pre (Entails.of_eq ?_)
              (h3328 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m4.trans hinv5.1))
            rw [hpool5]
            simp +zetaDelta only [bs3, bs2, bs1, etv2_encodeUint64Field_1_eq, hep, ↓reduceIte, List.append_nil]; sep_ac_rfl
        intro sm5 hpcm5 hrunm5 hspm5 htrm5 hx19_5 hx20_5 hx27_5 hfp_5 hinv_5
        have hx19_cap : optKeysUnsampledCap g (some u) = optAuthCap g u.auth := rfl
        rw [hx19_cap] at hx19_5
        cases hauth : u.auth with
        | none =>
          simp only [hauth, Option.isSome_none, Bool.not_false] at hcap_auth_beq hcap_auth_bne
          apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 1808#64)
          wp_steps
          apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, wp_norm, *])
          intro hinv6
          have hpool6 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv6.2).symm
          refine SepWPp.weaken_pre (Entails.of_eq ?_)
            (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_5.trans hinv6.1))
          rw [hpool6, etv2_encodeInnerState_keysUnsampled_eq, huc, etv2_encodeOptKeysUnsampled_some_eq, hauth]
          simp +zetaDelta only [bs3, bs2, bs1, huc, hauth, encodeOptMessage, optKeysUnsampledPBPinnedAt,
            keysUnsampledPBPinnedAt, unchunked2PinnedAt, h136_48, List.append_nil, List.append_assoc]
        | some auth =>
          simp only [hauth, Option.isSome_some, Bool.not_true] at hcap_auth_beq hcap_auth_bne
          have hfit_auth : bs3.length + (encodeMessage ProtoAuthenticator.encodeRaw 2#32 auth).length ≤ cap.toNat := by
            rw [hauth] at hfit; dsimp only [bs3, bs2, bs1, encodeOptMessage] at hfit ⊢
            simp only [List.length_append, List.length_singleton] at hfit ⊢; omega
          apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 314)
          wp_steps
          apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, wp_norm, *])
          intro hinv6
          have hpool6 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv6.2).symm
          refine step_etv_encode_auth_call_prog A lim st hauthEnc
            (a + 136#64) (sp - 120#64) cap ptr sp ((blkPl_426).base + 3348#64) g auth bs3 hfit_auth
            (F := ((a + 184#64) ↦₆₄ u.epoch) ∗ F)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hinv_5.trans hinv6.1) (by rw [hpool6]; simp +zetaDelta only [bs3, bs2, bs1, hauth, optAuthenticatorPBPinnedAt]; sep_ac_rfl) ?_
          intro sm6 hpcm6 hrunm6 hspm6 htrm6 hcsm6 hinv_m6
          rcases hcsm6 with ⟨_, _, _, _, _, _, _, _, hm6_27, _, hm6_fp, _⟩
          simp only [arm64_norm, hx27_5, hfp_5] at hm6_27 hm6_fp
          apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 1808#64)
          wp_steps
          apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, wp_norm, *])
          intro hinv7
          have hpool7 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv7.2).symm
          refine SepWPp.weaken_pre (Entails.of_eq ?_)
            (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m6.trans hinv7.1))
          rw [hpool7, etv2_encodeInnerState_keysUnsampled_eq, huc, etv2_encodeOptKeysUnsampled_some_eq, hauth]
          simp +zetaDelta only [bs3, bs2, bs1, huc, hauth, encodeOptMessage, optKeysUnsampledPBPinnedAt,
            keysUnsampledPBPinnedAt, unchunked2PinnedAt, optAuthenticatorPBPinnedAt, h136_48, List.append_assoc]; sep_ac_rfl

/-! ## 2. Shared `memcpy` Slice Helper & Variant `idx = 2`: `.headerSent` (`+2176 .. +2520`, `+2732 .. +2748`) -/

theorem etv2_step_memcpy_slice_placed [LibsignalPlacement] {resStack : Nat}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (H : String → Option (State → State)) {s0 s : State}
    (hmemcpy : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      ((blkPl_426).ρ "memcpy") etvMemcpyRegionSpec)
    (sp cap ptr srcCap srcPtr ret_pc : BitVec 64) (bs4 srcBs : List (BitVec 8))
    (hemp : srcBs.isEmpty = false) (hsrc_le : srcBs.length ≤ srcCap.toNat) (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_426).ρ "memcpy") (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .x30 = ret_pc)
    (hx0 : s.readReg64 .x0 = ptr + BitVec.ofNat 64 bs4.length) (hx1 : s.readReg64 .x1 = srcPtr)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 srcBs.length) (hsrc_lt : srcBs.length < 2 ^ 64) (hinv0 : StepInv s0 s)
    (hP : P = ((((sp - 120#64) ↦₆₄ cap) ∗ ((sp - 112#64) ↦₆₄ ptr) ∗
        ((sp - 104#64) ↦₆₄ BitVec.ofNat 64 bs4.length) ∗ A.repAlloc.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs4) ∗
        memRegion (ptr + BitVec.ofNat 64 bs4.length) srcBs.length ∗
        memRegion (ptr + BitVec.ofNat 64 bs4.length + BitVec.ofNat 64 srcBs.length)
          (cap.toNat - bs4.length - srcBs.length)) ∗ vecU8Buf A.repAlloc srcCap srcPtr srcBs ∗
      A.pool lim st s ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → StepInv s0 sm →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm
        (((((sp - 120#64) ↦₆₄ cap) ∗ ((sp - 112#64) ↦₆₄ ptr) ∗
            ((sp - 104#64) ↦₆₄ BitVec.ofNat 64 bs4.length) ∗ A.repAlloc.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs4) ∗
            ((ptr + BitVec.ofNat 64 bs4.length) ↦ₛ srcBs) ∗
            memRegion (ptr + BitVec.ofNat 64 bs4.length + BitVec.ofNat 64 srcBs.length)
              (cap.toNat - bs4.length - srcBs.length)) ∗ vecU8Buf A.repAlloc srcCap srcPtr srcBs ∗
          A.pool lim st sm ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q Qp oom := by
  subst hP
  rw [vecU8Buf_eq_of_nonempty A.repAlloc srcCap srcPtr srcBs hemp hsrc_le]
  have hlen_toNat : (BitVec.ofNat 64 srcBs.length).toNat = srcBs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsrc_lt]
  refine step_etv_memcpy_call_prog A lim st hmemcpy (ptr + BitVec.ofNat 64 bs4.length) srcPtr sp ret_pc srcBs
    (F := ((sp - 120#64) ↦₆₄ cap) ∗ ((sp - 112#64) ↦₆₄ ptr) ∗ ((sp - 104#64) ↦₆₄ BitVec.ofNat 64 bs4.length) ∗
      A.repAlloc.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs4) ∗
      memRegion (ptr + BitVec.ofNat 64 bs4.length + BitVec.ofNat 64 srcBs.length) (cap.toNat - bs4.length - srcBs.length) ∗
      (⌜srcBs.length ≤ srcCap.toNat ∧ srcCap.toNat < 2 ^ 63 ∧ srcPtr ≠ 0⌝ ∗ A.repAlloc.live srcPtr srcCap.toNat 1 ∗
        memRegion (srcPtr + BitVec.ofNat 64 srcBs.length) (srcCap.toNat - srcBs.length)) ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F)
    hpc hrun hsp halign htr hlr hx0 hx1 (by simp only [hx2, hlen_toNat]) hinv0 (by sep_ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm _hvmm hcsm hinvm
  refine SepWPp.weaken_pre (Entails.of_eq ?_) (hnext sm hpcm hrunm hspm htrm hcsm hinvm)
  rw [vecU8Buf_eq_of_nonempty A.repAlloc srcCap srcPtr srcBs hemp hsrc_le]; sep_ac_rfl

/-- Step `+2228 .. +2476` (`Block 426`): inline encoding of `v.uc : Option EkSent` at `a + 136#64`,
threading `A.pool lim st`. -/
theorem etv2_step_headerSent_uc_placed [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (H : String → Option (State → State)) {s0 s : State}
    (hekSentLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 415)
      (withStepInv s0 (leafEncLen16Spec (ekSentPBPinnedAt A.repAlloc) ekSentPBEncodedLen)))
    (hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hauthEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 314)
      (withStepInv s0 (authEncodeExactSpecOf resStack A lim)))
    (hmemcpy : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      ((blkPl_426).ρ "memcpy") etvMemcpyRegionSpec)
    (a sp cap ptr : BitVec 64) (g : Unchunked3PBGhost) (opt : Option V1State.Unchunked.EkSent)
    (bs : List (BitVec 8))
    (hfit : bs.length + (encodeOptMessage V1State.Unchunked.EkSent.encodeRaw 1#32 opt).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_426).base + 2228#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = a) (hinv0 : StepInv s0 s)
    (hP : P = (optEkSentPBPinnedAt A.repAlloc g (a + 136#64) opt ∗
      vecU8At A.repAlloc (sp - 120#64) cap ptr bs ∗ A.pool lim st s ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_426).base + 2476#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x20 = a → sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .fp = s.readReg64 .fp →
      StepInv s0 sm →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm
        ((optEkSentPBPinnedAt A.repAlloc g (a + 136#64) opt ∗
          vecU8At A.repAlloc (sp - 120#64) cap ptr
            (bs ++ encodeOptMessage V1State.Unchunked.EkSent.encodeRaw 1#32 opt) ∗
          A.pool lim st sm ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q Qp oom := by
  subst hP
  have ⟨h112, h104⟩ : (sp - 120#64) + 8#64 = sp - 112#64 ∧ (sp - 120#64) + 16#64 = sp - 104#64 :=
    ⟨by bv_omega, by bv_omega⟩
  refine sepWPp_extract_pure
    ((optEkSentCap g opt + 1#64 == 0#64) = !opt.isSome ∧
     (optEkSentCap g opt + 1#64 != 0#64) = opt.isSome)
    (fun R' hm => etv2_optEkSentPBPinnedAt_cap_bounds (p := a + 136#64)
      (R := vecU8At A.repAlloc (sp - 120#64) cap ptr bs ∗ A.pool lim st s ∗
        stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
      (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm))
    fun ⟨hcap_uc_beq, hcap_uc_bne⟩ => ?_
  cases huc : opt with
  | none =>
    simp only [huc, Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
    rw [optEkSentPBPinnedAt_eq A.repAlloc g (a + 136#64) none]
    apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 2476#64)
    wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv1
    have hpool1 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv1.2).symm
    refine SepWPp.weaken_pre (Entails.of_eq ?_)
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (hinv0.trans hinv1.1))
    rw [optEkSentPBPinnedAt_eq A.repAlloc g (a + 136#64), huc, hpool1]
    simp only [encodeOptMessage, List.append_nil]
  | some u =>
    simp only [huc, Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
    rw [huc, etv2_encodeOptEkSent_some_eq] at hfit
    simp only [List.length_append, List.length_singleton] at hfit
    have hu_lt : ekSentPBEncodedLen u < 2 ^ 64 := by
      rw [← ekSentPBEncodedLen_eq_proto, V1State.Unchunked.EkSent.encodedLen]
      dsimp only [V1State.Unchunked.EkSent.encodeRaw]
      simp only [List.length_append]; have := BitVec.isLt cap; omega
    have hlt1 : bs.length < cap.toNat := by omega
    refine sepWPp_extract_vecU8At_bounds (v := sp - 120#64) (cap := cap) (ptr := ptr) (bs := bs)
      (F := optEkSentPBPinnedAt A.repAlloc g (a + 136#64) (some u) ∗ A.pool lim st s ∗
        stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F)
      (by sep_ac_rfl) fun _ hcap hptr => ?_
    have hbeq1 := cap_beq_len_false_of_lt hlt1 hcap
    rw [optEkSentPBPinnedAt_eq A.repAlloc g (a + 136#64) (some u),
      vecU8At_expose_one A.repAlloc (sp - 120#64) cap ptr bs hlt1 hcap hptr, h112, h104]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun b0 => ?_
    apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 415)
    by_vm_steps
      wp_steps
      apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv1
      have hpack1 := vecU8At_pack_one A.repAlloc (sp - 120#64) cap ptr bs 0x0a#8 hlt1 hcap hptr
      rw [h112, h104] at hpack1
      have hek_pin : ((a + 136#64) ↦₆₄ optEkSentCap g (some u)) ∗
          optEkSentRest A.repAlloc g (a + 136#64) (some u) =
          ekSentPBPinnedAt A.repAlloc g (a + 136#64) u := by
        simpa only [optEkSentPBPinnedAt] using
          (optEkSentPBPinnedAt_eq A.repAlloc g (a + 136#64) (some u)).symm
      refine step_etv_leaf_encLen16_call_placed hres (ekSentPBPinnedAt A.repAlloc)
        ekSentPBEncodedLen hekSentLen
        (a + 136#64) sp ((blkPl_426).base + 2284#64) g u hu_lt
        (F := vecU8At A.repAlloc (sp - 120#64) cap ptr (bs ++ [0x0a#8]) ∗ A.pool lim st s ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (hinv0.trans hinv1.1) (by rw [← hpack1, ← hek_pin]; sep_ac_rfl) ?_
      intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1 hcsm1 hinv_m1 hvm_m1
      rcases hcsm1 with ⟨_, hm20, _, _, _, _, _, _, hm27, _, hmfp, _⟩
      simp only [arm64_norm, hx20] at hm20 hm27 hmfp
      apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 292)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv2
      set bs1 := (bs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 (ekSentPBEncodedLen u))
      have hfit_var : (bs ++ [0x0a#8]).length +
          (encodeVarint (BitVec.ofNat 64 (ekSentPBEncodedLen u))).length ≤ cap.toNat := by
        simp only [List.length_append, List.length_singleton]; omega
      refine step_etv_encode_varint_call_prog A lim st hvarint
        (BitVec.ofNat 64 (ekSentPBEncodedLen u))
        (sp - 120#64) cap ptr sp ((blkPl_426).base + 2292#64) (bs ++ [0x0a#8]) hfit_var
        (F := ekSentPBPinnedAt A.repAlloc g (a + 136#64) u ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hinv_m1.trans hinv2.1)
        (by rw [A.pool_of_vmPreserved (lim := lim) (st := st) (hinv1.2.trans (hvm_m1.trans hinv2.2))]; sep_ac_rfl) ?_
      intro sm2 hpcm2 hrunm2 hspm2 htrm2 hcsm2 hinv_m2
      rcases hcsm2 with ⟨_, hm2_20, _, _, _, _, _, _, hm2_27, _, hm2_fp, _⟩
      simp only [arm64_norm, hm20, hm27, hmfp] at hm2_20 hm2_27 hm2_fp
      dsimp only [ekSentPBPinnedAt, unchunked3PinnedAt]
      have ⟨h136_24, h136_72⟩ :
          (a + 136#64) + 0x18#64 = a + 160#64 ∧ (a + 136#64) + 0x48#64 = a + 208#64 :=
        ⟨by bv_omega, by bv_omega⟩
      rw [h136_24, h136_72]
      refine sepWPp_extract_pure
        ((optAuthCap g.auth u.auth + 1#64 == 0#64) = !u.auth.isSome ∧
         (optAuthCap g.auth u.auth + 1#64 != 0#64) = u.auth.isSome)
        (fun R' hm => etv2_optAuth_cap_bounds (A := A.repAlloc) (p := a + 160#64)
          (R := vecU8At A.repAlloc (a + 136#64) g.f3.cap g.f3.ptr u.dk ∗ ((a + 208#64) ↦₆₄ u.epoch) ∗
            vecU8At A.repAlloc (sp - 120#64) cap ptr bs1 ∗ A.pool lim st sm2 ∗
            stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
          (Satisfies.mono (Entails.of_eq (by dsimp +zetaDelta only [bs1]; sep_ac_rfl)) hm))
        fun ⟨hcap_auth_beq, hcap_auth_bne⟩ => ?_
      set bs2 := bs1 ++ encodeUint64Field 1#32 u.epoch
      suffices h2344 : ∀ sm3 : State,
          sm3.pc = (blkPl_426).base + 2344#64 → sm3.status = .Running → sm3.sp = sp - 144#64 → sm3.trace = s0.trace →
          sm3.readReg64 .x20 = a → sm3.readReg64 .x27 = s.readReg64 .x27 → sm3.readReg64 .fp = s.readReg64 .fp →
          StepInv s0 sm3 →
          SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm3
            (((vecU8At A.repAlloc (a + 136#64) g.f3.cap g.f3.ptr u.dk ∗
              optAuthenticatorPBPinnedAt A.repAlloc g.auth (a + 160#64) u.auth ∗ ((a + 208#64) ↦₆₄ u.epoch)) ∗
              vecU8At A.repAlloc (sp - 120#64) cap ptr bs2 ∗ A.pool lim st sm3 ∗
              stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
            Q Qp oom by
        cases hep : u.epoch == 0#64
        · have hfit_ep : bs1.length + 1 + (encodeVarint u.epoch).length ≤ cap.toNat := by
            rw [etv2_encodeUint64Field_1_eq, hep] at hfit; dsimp only [bs1]
            simp only [Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_singleton] at hfit ⊢; omega
          have hlt_ep : bs1.length < cap.toNat := by have := encodeVarint_length_pos u.epoch; omega
          have hbeq_ep := cap_beq_len_false_of_lt hlt_ep hcap
          rw [vecU8At_expose_one A.repAlloc (sp - 120#64) cap ptr bs1 hlt_ep hcap hptr, h112, h104]
          simp only [sepExists_sepConj_left, sepExists_sepConj_right]
          refine SepWPp.exists_elim fun b1 => ?_
          apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 292)
          by_vm_steps
            wp_steps
            apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, wp_norm, *])
            intro hinv3
            have hpool3 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv3.2).symm
            have hpack_ep := vecU8At_pack_one A.repAlloc (sp - 120#64) cap ptr bs1 0x08#8 hlt_ep hcap hptr
            rw [h112, h104] at hpack_ep
            refine step_etv_encode_varint_call_prog A lim st hvarint
              u.epoch (sp - 120#64) cap ptr sp ((blkPl_426).base + 2344#64) (bs1 ++ [0x08#8])
              (by simpa only [List.length_append, List.length_singleton] using hfit_ep)
              (F := (vecU8At A.repAlloc (a + 136#64) g.f3.cap g.f3.ptr u.dk ∗
                optAuthenticatorPBPinnedAt A.repAlloc g.auth (a + 160#64) u.auth ∗
                ((a + 208#64) ↦₆₄ u.epoch)) ∗ F)
              (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (hinv_m2.trans hinv3.1) (by rw [← hpack_ep, hpool3]) ?_
            intro sm3 hpcm3 hrunm3 hspm3 htrm3 hcsm3 hinv_m3
            rcases hcsm3 with ⟨_, hm3_20, _, _, _, _, _, _, hm3_27, _, hm3_fp, _⟩
            simp only [arm64_norm, hm2_20, hm2_27, hm2_fp] at hm3_20 hm3_27 hm3_fp
            refine SepWPp.weaken_pre (Entails.of_eq ?_)
              (h2344 sm3 hpcm3 hrunm3 hspm3 htrm3 hm3_20 hm3_27 hm3_fp hinv_m3)
            simp +zetaDelta only [bs2, bs1, etv2_encodeUint64Field_1_eq, hep, Bool.false_eq_true, ↓reduceIte,
              List.append_assoc]; sep_ac_rfl
        · apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 2344#64)
          wp_steps
          apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, wp_norm, *])
          intro hinv3
          have hpool3 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv3.2).symm
          refine SepWPp.weaken_pre (Entails.of_eq ?_)
            (h2344 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (hinv_m2.trans hinv3.1))
          rw [hpool3]
          simp +zetaDelta only [bs2, bs1, etv2_encodeUint64Field_1_eq, hep, ↓reduceIte, List.append_nil]; sep_ac_rfl
      intro sm3 hpcm3 hrunm3 hspm3 htrm3 hx20_3 hx27_3 hfp_3 hinv_3
      set bs3 := bs2 ++ encodeOptMessage ProtoAuthenticator.encodeRaw 2#32 u.auth
      suffices h2368 : ∀ sm4 : State,
          sm4.pc = (blkPl_426).base + 2368#64 → sm4.status = .Running → sm4.sp = sp - 144#64 → sm4.trace = s0.trace →
          sm4.readReg64 .x20 = a → sm4.readReg64 .x27 = s.readReg64 .x27 → sm4.readReg64 .fp = s.readReg64 .fp →
          StepInv s0 sm4 →
          SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm4
            (((vecU8At A.repAlloc (a + 136#64) g.f3.cap g.f3.ptr u.dk ∗
              optAuthenticatorPBPinnedAt A.repAlloc g.auth (a + 160#64) u.auth ∗ ((a + 208#64) ↦₆₄ u.epoch)) ∗
              vecU8At A.repAlloc (sp - 120#64) cap ptr bs3 ∗ A.pool lim st sm4 ∗
              stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
            Q Qp oom by
        cases hauth : u.auth with
        | none =>
          rw [optAuthenticatorPBPinnedAt_eq A.repAlloc g.auth (a + 160#64) none]
          simp only [hauth, Option.isSome_none, Bool.not_false] at hcap_auth_beq hcap_auth_bne
          apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 2368#64)
          wp_steps
          apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, wp_norm, *])
          intro hinv4
          have hpool4 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv4.2).symm
          refine SepWPp.weaken_pre (Entails.of_eq ?_)
            (h2368 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (hinv_3.trans hinv4.1))
          rw [← optAuthenticatorPBPinnedAt_eq A.repAlloc g.auth (a + 160#64) none, hpool4]
          simp +zetaDelta only [bs3, bs2, bs1, hauth, encodeOptMessage, List.append_nil]
        | some auth =>
          rw [optAuthenticatorPBPinnedAt_eq A.repAlloc g.auth (a + 160#64) (some auth)]
          simp only [hauth, Option.isSome_some, Bool.not_true] at hcap_auth_beq hcap_auth_bne
          have hfit_auth : bs2.length + (encodeMessage ProtoAuthenticator.encodeRaw 2#32 auth).length ≤ cap.toNat := by
            rw [hauth] at hfit; dsimp only [bs2, bs1, encodeOptMessage] at hfit ⊢
            simp only [List.length_append, List.length_singleton] at hfit ⊢; omega
          apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 314)
          wp_steps
          apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, wp_norm, *])
          intro hinv4
          have hpool4 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv4.2).symm
          rw [← optAuthenticatorPBPinnedAt_eq A.repAlloc g.auth (a + 160#64) (some auth)]
          refine step_etv_encode_auth_call_prog A lim st hauthEnc
            (a + 160#64) (sp - 120#64) cap ptr sp ((blkPl_426).base + 2368#64) g.auth auth bs2 hfit_auth
            (F := (vecU8At A.repAlloc (a + 136#64) g.f3.cap g.f3.ptr u.dk ∗ ((a + 208#64) ↦₆₄ u.epoch)) ∗ F)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hinv_3.trans hinv4.1) (by rw [hpool4]; dsimp +zetaDelta only [bs2, bs1, optAuthenticatorPBPinnedAt]; sep_ac_rfl) ?_
          intro sm4 hpcm4 hrunm4 hspm4 htrm4 hcsm4 hinv_m4
          rcases hcsm4 with ⟨_, hm4_20, _, _, _, _, _, _, hm4_27, _, hm4_fp, _⟩
          simp only [arm64_norm, hx20_3, hx27_3, hfp_3] at hm4_20 hm4_27 hm4_fp
          refine SepWPp.weaken_pre (Entails.of_eq ?_)
            (h2368 sm4 hpcm4 hrunm4 hspm4 htrm4 hm4_20 hm4_27 hm4_fp hinv_m4)
          simp +zetaDelta only [bs3, bs2, bs1, hauth, encodeOptMessage, optAuthenticatorPBPinnedAt]; sep_ac_rfl
      intro sm4 hpcm4 hrunm4 hspm4 htrm4 hx20_4 hx27_4 hfp_4 hinv_4
      refine sepWPp_extract_vecU8At_bounds (A := A.repAlloc) (v := a + 136#64) (cap := g.f3.cap)
        (ptr := g.f3.ptr) (bs := u.dk)
        (F := optAuthenticatorPBPinnedAt A.repAlloc g.auth (a + 160#64) u.auth ∗ ((a + 208#64) ↦₆₄ u.epoch) ∗
          vecU8At A.repAlloc (sp - 120#64) cap ptr bs3 ∗ A.pool lim st sm4 ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F)
        (by dsimp +zetaDelta only [bs3, bs2, bs1]; sep_ac_rfl) fun hdk_le hdk_cap _ => ?_
      have ⟨h144, h152⟩ : (a + 136#64) + 8#64 = a + 144#64 ∧ (a + 136#64) + 16#64 = a + 152#64 :=
        ⟨by bv_omega, by bv_omega⟩
      rw [vecU8At_eq_header_sep_buf A.repAlloc (a + 136#64), vecHeader, h144, h152]
      have hdk_lt : u.dk.length < 2 ^ 64 := by omega
      obtain ⟨hbeqz, hbnez⟩ := ofNat_length_beq_zero_of_lt hdk_lt
      cases hemp : u.dk.isEmpty
      · simp only [hemp, Bool.not_false] at hbeqz hbnez
        have hpos_dk : 0 < u.dk.length := List.length_pos_of_ne_nil (List.isEmpty_eq_false_iff.mp hemp)
        have hne_dk : u.dk ≠ [] := List.isEmpty_eq_false_iff.mp hemp
        have henc_eq : encodeBytesField 3#32 u.dk =
            [0x1a#8] ++ encodeVarint (BitVec.ofNat 64 u.dk.length) ++ u.dk := by
          rw [etv2_encodeBytesField_3_eq, hemp]; simp only [Bool.false_eq_true, ↓reduceIte]
        have hfit_all : bs3.length + 1 + (encodeVarint (BitVec.ofNat 64 u.dk.length)).length + u.dk.length ≤ cap.toNat := by
          rw [henc_eq] at hfit; dsimp only [bs3, bs2, bs1] at hfit ⊢
          simp only [List.length_append, List.length_singleton] at hfit ⊢; omega
        have hlt_tag : bs3.length < cap.toNat := by omega
        have hcmp_tag := cap_beq_len_false_of_lt hlt_tag hcap
        rw [vecU8At_expose_one A.repAlloc (sp - 120#64) cap ptr bs3 hlt_tag hcap hptr, h112, h104]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        refine SepWPp.exists_elim fun b2 => ?_
        apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 292)
        by_vm_steps
          wp_steps
          apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, wp_norm, *])
          intro hinv5
          have hpool5 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv5.2).symm
          have hpack_tag := vecU8At_pack_one A.repAlloc (sp - 120#64) cap ptr bs3 0x1a#8 hlt_tag hcap hptr
          rw [h112, h104] at hpack_tag
          refine step_etv_encode_varint_call_prog A lim st hvarint
            (BitVec.ofNat 64 u.dk.length) (sp - 120#64) cap ptr sp ((blkPl_426).base + 2428#64)
            (bs3 ++ [0x1a#8]) (by simp only [List.length_append, List.length_singleton]; omega)
            (F := ((((a + 136#64) ↦₆₄ g.f3.cap) ∗ ((a + 144#64) ↦₆₄ g.f3.ptr) ∗
              ((a + 152#64) ↦₆₄ BitVec.ofNat 64 u.dk.length)) ∗
              vecU8Buf A.repAlloc g.f3.cap g.f3.ptr u.dk ∗
              optAuthenticatorPBPinnedAt A.repAlloc g.auth (a + 160#64) u.auth ∗
              ((a + 208#64) ↦₆₄ u.epoch)) ∗ F)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hinv_4.trans hinv5.1) (by rw [← hpack_tag, hpool5]; sep_ac_rfl) ?_
          intro sm5 hpcm5 hrunm5 hspm5 htrm5 hcsm5 hinv_m5
          rcases hcsm5 with ⟨_, hm5_20, hm5_21, hm5_22, _, _, _, _, hm5_27, _, hm5_fp, _⟩
          simp only [arm64_norm, hx20_4, hx27_4, hfp_4] at hm5_20 hm5_21 hm5_22 hm5_27 hm5_fp
          let bs4 := (bs3 ++ [0x1a#8]) ++ encodeVarint (BitVec.ofNat 64 u.dk.length)
          have hfit_mc : bs4.length + u.dk.length ≤ cap.toNat := by
            dsimp only [bs4]; simp only [List.length_append, List.length_singleton]; omega
          have hcmp_mc := elem_len_ult_spare_false_of_le hfit_mc hcap
          rw [vecU8At_expose_slice A.repAlloc (sp - 120#64) cap ptr bs4 u.dk.length hfit_mc hcap hptr hpos_dk,
            h112, h104]
          apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).ρ "memcpy")
          by_vm_steps
            wp_steps
            apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, wp_norm, *])
            intro hinv6
            have hpool6 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv6.2).symm
            refine etv2_step_memcpy_slice_placed A lim st H hmemcpy
              sp cap ptr g.f3.cap g.f3.ptr ((blkPl_426).base + 2468#64) bs4 u.dk hemp hdk_le halign
              (F := (((a + 136#64) ↦₆₄ g.f3.cap) ∗ ((a + 144#64) ↦₆₄ g.f3.ptr) ∗
                ((a + 152#64) ↦₆₄ BitVec.ofNat 64 u.dk.length)) ∗
                optAuthenticatorPBPinnedAt A.repAlloc g.auth (a + 160#64) u.auth ∗
                ((a + 208#64) ↦₆₄ u.epoch) ∗ F)
              (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              hdk_lt (hinv_m5.trans hinv6.1) (by rw [hpool6]; sep_ac_rfl) ?_
            intro sm6 hpcm6 hrunm6 hspm6 htrm6 hcsm6 hinv_m6
            rcases hcsm6 with ⟨_, hm6_20, hm6_21, hm6_22, hm6_23, _, _, _, hm6_27, _, hm6_fp, _⟩
            simp only [arm64_norm, hm5_20, hm5_21, hm5_22, hm5_27, hm5_fp]
              at hm6_20 hm6_21 hm6_22 hm6_23 hm6_27 hm6_fp
            apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 2476#64)
            by_vm_steps
              wp_steps
              apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, wp_norm, *])
              intro hinv7
              have hpool7 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv7.2).symm
              have hpack_mc := vecU8At_pack_slice A.repAlloc (sp - 120#64) cap ptr bs4 u.dk hfit_mc hcap hptr hne_dk
              have hbs_eq : bs4 ++ u.dk = bs ++ encodeOptMessage V1State.Unchunked.EkSent.encodeRaw 1#32 (some u) := by
                rw [etv2_encodeOptEkSent_some_eq, henc_eq]; dsimp only [bs4, bs3, bs2, bs1]
                simp only [List.append_assoc]
              rw [h112, h104, hbs_eq] at hpack_mc
              refine SepWPp.weaken_pre (Entails.of_eq ?_)
                (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                  (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                  (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                  (by simp only [arm64_norm, *]) (hinv_m6.trans hinv7.1))
              rw [huc]; dsimp only [optEkSentPBPinnedAt, ekSentPBPinnedAt, unchunked3PinnedAt]
              rw [h136_24, h136_72, vecU8At_eq_header_sep_buf A.repAlloc (a + 136#64), vecHeader,
                h144, h152, ← hpack_mc, hpool7]
              sep_ac_rfl
      · simp only [hemp, Bool.not_true] at hbeqz hbnez
        have henc_nil : encodeBytesField 3#32 u.dk = [] := by
          rw [etv2_encodeBytesField_3_eq, hemp]; simp only [↓reduceIte]
        apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 2476#64)
        wp_steps
        apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv5
        have hpool5 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv5.2).symm
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (hinv_4.trans hinv5.1))
        rw [huc]; dsimp only [optEkSentPBPinnedAt, ekSentPBPinnedAt, unchunked3PinnedAt]
        rw [h136_24, h136_72, vecU8At_eq_header_sep_buf A.repAlloc (a + 136#64), vecHeader,
          h144, h152, etv2_encodeOptEkSent_some_eq, henc_nil, hpool5]
        dsimp +zetaDelta only [bs3, bs2, bs1]; simp only [List.append_nil, List.append_assoc]

theorem step_encodeToVec_v1_headerSent_placed [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (H : String → Option (State → State))
    {s0 s : State}
    (hhsLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 414)
      (withStepInv s0 (leafEncLen48Spec (chunkedHeaderSentPBPinnedAt A.repAlloc) chunkedHeaderSentPBEncodedLen)))
    (hekSentLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 415)
      (withStepInv s0 (leafEncLen16Spec (ekSentPBPinnedAt A.repAlloc) ekSentPBEncodedLen)))
    (hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hauthEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 314)
      (withStepInv s0 (authEncodeExactSpecOf resStack A lim)))
    (hmemcpy : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      ((blkPl_426).ρ "memcpy") etvMemcpyRegionSpec)
    (hpolyEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 316)
      (withStepInv s0 (etvPolyEncoderBudgetExactSpecOf resStack A lim)))
    (hpolyDec : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 315)
      (withStepInv s0 (etvPolyDecoderBudgetExactSpecOf resStack A lim)))
    (a sp cap ptr : BitVec 64) (g : ChunkedHeaderSentPBGhost) (v : V1State.Chunked.HeaderSent)
    (bs : List (BitVec 8))
    (hv_len : v1StatePBEncodedLen ⟨some (.headerSent v)⟩ < 2 ^ 64)
    (hfit : bs.length + (V1State.InnerState.encode (.headerSent v)).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_426).base + 2176#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = a) (hinv0 : StepInv s0 s)
    (hP : P = (chunkedHeaderSentPBPinnedAt A.repAlloc g (a + 136#64) v ∗
      vecU8At A.repAlloc (sp - 120#64) cap ptr bs ∗ A.pool lim st s ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_426).base + 1808#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm
        ((chunkedHeaderSentPBPinnedAt A.repAlloc g (a + 136#64) v ∗
          vecU8At A.repAlloc (sp - 120#64) cap ptr (bs ++ V1State.InnerState.encode (.headerSent v)) ∗
          A.pool lim st sm ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q Qp oom := by
  subst hP
  rw [etv2_encodeInnerState_headerSent_eq] at hfit
  simp only [List.length_append, List.length_singleton] at hfit
  have hsub_len : chunkedHeaderSentPBEncodedLen v < 2 ^ 64 := by
    dsimp only [v1StatePBEncodedLen, v1StateInnerPayloadEncodedLen] at hv_len; omega
  have hlt1 : bs.length < cap.toNat := by omega
  have hfit_var : (bs ++ [0x1a#8]).length +
      (encodeVarint (BitVec.ofNat 64 (chunkedHeaderSentPBEncodedLen v))).length ≤ cap.toNat := by
    simp only [List.length_append, List.length_singleton]; omega
  refine sepWPp_extract_vecU8At_bounds (v := sp - 120#64) (cap := cap) (ptr := ptr) (bs := bs)
    (F := chunkedHeaderSentPBPinnedAt A.repAlloc g (a + 136#64) v ∗ A.pool lim st s ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F)
    (by sep_ac_rfl) fun _ hcap hptr => ?_
  have hbeq_false := cap_beq_len_false_of_lt hlt1 hcap
  have ⟨h112, h104⟩ : (sp - 120#64) + 8#64 = sp - 112#64 ∧ (sp - 120#64) + 16#64 = sp - 104#64 :=
    ⟨by bv_omega, by bv_omega⟩
  rw [vecU8At_expose_one A.repAlloc (sp - 120#64) cap ptr bs hlt1 hcap hptr, h112, h104]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun b0 => ?_
  apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 414)
  by_vm_steps
    wp_steps
    apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv1
    have hpack := vecU8At_pack_one A.repAlloc (sp - 120#64) cap ptr bs 0x1a#8 hlt1 hcap hptr
    rw [h112, h104] at hpack
    refine step_etv_chunked_encLen48_call_placed hres
      (chunkedHeaderSentPBPinnedAt A.repAlloc) chunkedHeaderSentPBEncodedLen hhsLen
      (a + 136#64) sp ((blkPl_426).base + 2220#64) g v hsub_len
      (F := vecU8At A.repAlloc (sp - 120#64) cap ptr (bs ++ [0x1a#8]) ∗ A.pool lim st s ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
      (hinv0.trans hinv1.1) (by rw [← hpack]; sep_ac_rfl) ?_
    intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1 hcsm1 hinv_m1 hvm_m1
    rcases hcsm1 with ⟨_, hm20, _, _, _, _, _, _, hm27, _, hmfp, _⟩
    simp only [arm64_norm, hx20] at hm20 hm27 hmfp
    apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 292)
    wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv2
    set bs1 := (bs ++ [0x1a#8]) ++ encodeVarint (BitVec.ofNat 64 (chunkedHeaderSentPBEncodedLen v))
    refine step_etv_encode_varint_call_prog A lim st hvarint
      (BitVec.ofNat 64 (chunkedHeaderSentPBEncodedLen v)) (sp - 120#64) cap ptr sp ((blkPl_426).base + 2228#64)
      (bs ++ [0x1a#8]) hfit_var (F := chunkedHeaderSentPBPinnedAt A.repAlloc g (a + 136#64) v ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hinv_m1.trans hinv2.1)
      (by rw [A.pool_of_vmPreserved (lim := lim) (st := st) (hinv1.2.trans (hvm_m1.trans hinv2.2))]; sep_ac_rfl) ?_
    intro sm2 hpcm2 hrunm2 hspm2 htrm2 hcsm2 hinv_m2
    rcases hcsm2 with ⟨_, hm2_20, _, _, _, _, _, _, hm2_27, _, hm2_fp, _⟩
    simp only [arm64_norm, hm20, hm27, hmfp] at hm2_20 hm2_27 hm2_fp
    dsimp only [chunkedHeaderSentPBPinnedAt]
    have ⟨h136_80, h136_136⟩ :
        (a + 136#64) + 80#64 = a + 216#64 ∧ (a + 136#64) + 136#64 = a + 272#64 :=
      ⟨by bv_omega, by bv_omega⟩
    rw [h136_80, h136_136]
    have hfit_uc : bs1.length + (encodeOptMessage V1State.Unchunked.EkSent.encodeRaw 1#32 v.uc).length ≤ cap.toNat := by
      dsimp only [bs1]; simp only [List.length_append, List.length_singleton]; omega
    refine etv2_step_headerSent_uc_placed hres A lim st H hekSentLen hvarint hauthEnc hmemcpy
      a sp cap ptr g.uc v.uc bs1 hfit_uc halign
      (F := optPolynomialEncoderPBPinnedAt A.repAlloc g.sendingEk (a + 216#64) v.sendingEk ∗
        optPolynomialDecoderPBPinnedAt A.repAlloc g.receivingCt1 (a + 272#64) v.receivingCt1 ∗ F)
      hpcm2 hrunm2 hspm2 htrm2 hm2_20 hinv_m2 (by dsimp +zetaDelta only [bs1]; sep_ac_rfl) ?_
    intro sm3 hpcm3 hrunm3 hspm3 htrm3 hx20_3 hx27_3 hfp_3 hinv_3
    simp only [arm64_norm, hm2_27, hm2_fp] at hx27_3 hfp_3
    set bs2 := bs1 ++ encodeOptMessage V1State.Unchunked.EkSent.encodeRaw 1#32 v.uc
    refine sepWPp_extract_pure
      (((optPolyEncCap g.sendingEk v.sendingEk + 1#64 == 0#64) = !v.sendingEk.isSome ∧
        (optPolyEncCap g.sendingEk v.sendingEk + 1#64 != 0#64) = v.sendingEk.isSome) ∧
       ((optPolyDecCap g.receivingCt1 v.receivingCt1 + 1#64 == 0#64) = !v.receivingCt1.isSome ∧
        (optPolyDecCap g.receivingCt1 v.receivingCt1 + 1#64 != 0#64) = v.receivingCt1.isSome))
      (fun R' hm =>
        ⟨optPolynomialEncoderPBPinnedAt_cap_bounds (p := a + 216#64)
          (R := optEkSentPBPinnedAt A.repAlloc g.uc (a + 136#64) v.uc ∗
            optPolynomialDecoderPBPinnedAt A.repAlloc g.receivingCt1 (a + 272#64) v.receivingCt1 ∗
            vecU8At A.repAlloc (sp - 120#64) cap ptr bs2 ∗ A.pool lim st sm3 ∗
            stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
          (Satisfies.mono (Entails.of_eq (by dsimp +zetaDelta only [bs2, bs1]; sep_ac_rfl)) hm),
         optPolynomialDecoderPBPinnedAt_cap_bounds (p := a + 272#64)
          (R := optEkSentPBPinnedAt A.repAlloc g.uc (a + 136#64) v.uc ∗
            optPolynomialEncoderPBPinnedAt A.repAlloc g.sendingEk (a + 216#64) v.sendingEk ∗
            vecU8At A.repAlloc (sp - 120#64) cap ptr bs2 ∗ A.pool lim st sm3 ∗
            stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
          (Satisfies.mono (Entails.of_eq (by dsimp +zetaDelta only [bs2, bs1]; sep_ac_rfl)) hm)⟩)
      fun ⟨⟨hcap_enc_beq, hcap_enc_bne⟩, ⟨hcap_dec_beq, hcap_dec_bne⟩⟩ => ?_
    set bs3 := bs2 ++ encodeOptMessage PolynomialEncoder.encodeRaw 2#32 v.sendingEk
    suffices h2500 : ∀ sm4 : State,
        sm4.pc = (blkPl_426).base + 2500#64 → sm4.status = .Running → sm4.sp = sp - 144#64 → sm4.trace = s0.trace →
        sm4.readReg64 .x20 = a → sm4.readReg64 .x27 = s.readReg64 .x27 → sm4.readReg64 .fp = s.readReg64 .fp →
        StepInv s0 sm4 →
        SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm4
          (((optEkSentPBPinnedAt A.repAlloc g.uc (a + 136#64) v.uc ∗
            optPolynomialEncoderPBPinnedAt A.repAlloc g.sendingEk (a + 216#64) v.sendingEk ∗
            optPolynomialDecoderPBPinnedAt A.repAlloc g.receivingCt1 (a + 272#64) v.receivingCt1) ∗
            vecU8At A.repAlloc (sp - 120#64) cap ptr bs3 ∗ A.pool lim st sm4 ∗
            stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
          Q Qp oom by
      cases henc : v.sendingEk with
      | none =>
        rw [optPolynomialEncoderPBPinnedAt_eq A.repAlloc g.sendingEk (a + 216#64) none]
        simp only [henc, Option.isSome_none, Bool.not_false] at hcap_enc_beq hcap_enc_bne
        apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 2500#64)
        wp_steps
        apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv4
        have hpool4 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv4.2).symm
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (h2500 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (hinv_3.trans hinv4.1))
        rw [← optPolynomialEncoderPBPinnedAt_eq A.repAlloc g.sendingEk (a + 216#64) none, hpool4]
        simp +zetaDelta only [bs3, bs2, bs1, henc, encodeOptMessage, List.append_nil]; sep_ac_rfl
      | some enc =>
        rw [optPolynomialEncoderPBPinnedAt_eq A.repAlloc g.sendingEk (a + 216#64) (some enc)]
        simp only [henc, Option.isSome_some, Bool.not_true] at hcap_enc_beq hcap_enc_bne
        have hfit_enc : bs2.length + (encodeMessage PolynomialEncoder.encodeRaw 2#32 enc).length ≤ cap.toNat := by
          rw [henc] at hfit
          simp +zetaDelta only [bs2, bs1, encodeOptMessage, List.length_append, List.length_singleton] at hfit ⊢; omega
        apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 316)
        wp_steps
        apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv4
        have hpool4 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv4.2).symm
        rw [← optPolynomialEncoderPBPinnedAt_eq A.repAlloc g.sendingEk (a + 216#64) (some enc)]
        refine step_etv_encode_polyEncoder_budget_call_placed A lim st hpolyEnc
          (a + 216#64) (sp - 120#64) cap ptr sp ((blkPl_426).base + 2500#64) g.sendingEk enc bs2 hfit_enc
          (F := optEkSentPBPinnedAt A.repAlloc g.uc (a + 136#64) v.uc ∗
            optPolynomialDecoderPBPinnedAt A.repAlloc g.receivingCt1 (a + 272#64) v.receivingCt1 ∗ F)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hinv_3.trans hinv4.1)
          (by rw [hpool4]; dsimp +zetaDelta only [bs2, bs1, optPolynomialEncoderPBPinnedAt]; sep_ac_rfl) ?_
        intro sm4 hpcm4 hrunm4 hspm4 htrm4 hcsm4 hinv_m4
        rcases hcsm4 with ⟨_, hm4_20, _, _, _, _, _, _, hm4_27, _, hm4_fp, _⟩
        simp only [arm64_norm, hx20_3, hx27_3, hfp_3] at hm4_20 hm4_27 hm4_fp
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (h2500 sm4 hpcm4 hrunm4 hspm4 htrm4 hm4_20 hm4_27 hm4_fp hinv_m4)
        simp +zetaDelta only [bs3, bs2, bs1, henc, encodeOptMessage, optPolynomialEncoderPBPinnedAt]; sep_ac_rfl
    intro sm4 hpcm4 hrunm4 hspm4 htrm4 hx20_4 hx27_4 hfp_4 hinv_4
    cases hdec : v.receivingCt1 with
    | none =>
      rw [optPolynomialDecoderPBPinnedAt_eq A.repAlloc g.receivingCt1 (a + 272#64) none]
      simp only [hdec, Option.isSome_none, Bool.not_false] at hcap_dec_beq hcap_dec_bne
      apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 1808#64)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv5
      have hpool5 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv5.2).symm
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_4.trans hinv5.1))
      rw [← optPolynomialDecoderPBPinnedAt_eq A.repAlloc g.receivingCt1 (a + 272#64) none,
        etv2_encodeInnerState_headerSent_eq, hpool5]
      simp +zetaDelta only [bs3, bs2, bs1, hdec, encodeOptMessage, chunkedHeaderSentPBPinnedAt,
        List.append_nil, h136_80, h136_136, List.append_assoc]
    | some dec =>
      rw [optPolynomialDecoderPBPinnedAt_eq A.repAlloc g.receivingCt1 (a + 272#64) (some dec)]
      simp only [hdec, Option.isSome_some, Bool.not_true] at hcap_dec_beq hcap_dec_bne
      have hfit_dec : bs3.length + (encodeMessage PolynomialDecoder.encodeRaw 3#32 dec).length ≤ cap.toNat := by
        rw [hdec] at hfit
        simp +zetaDelta only [bs3, bs2, bs1, encodeOptMessage, List.length_append, List.length_singleton] at hfit ⊢; omega
      apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 2732#64)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv5
      have hpool5 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv5.2).symm
      rw [← optPolynomialDecoderPBPinnedAt_eq A.repAlloc g.receivingCt1 (a + 272#64) (some dec)]
      refine step_encodeToVec_tail_2732_polyDec3_placed A lim st H hpolyDec
        (a + 272#64) sp cap ptr g.receivingCt1 dec bs3 hfit_dec halign
        (F := optEkSentPBPinnedAt A.repAlloc g.uc (a + 136#64) v.uc ∗
          optPolynomialEncoderPBPinnedAt A.repAlloc g.sendingEk (a + 216#64) v.sendingEk ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_4.trans hinv5.1)
        (by rw [hpool5]; dsimp +zetaDelta only [bs3, bs2, bs1, optPolynomialDecoderPBPinnedAt]; sep_ac_rfl) ?_
      intro sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_27 hm5_fp hinv_m5
      simp only [arm64_norm, hx27_4, hfp_4] at hm5_27 hm5_fp
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (hnext sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_27 hm5_fp hinv_m5)
      rw [etv2_encodeInnerState_headerSent_eq]
      simp +zetaDelta only [bs3, bs2, bs1, hdec, encodeOptMessage,
        chunkedHeaderSentPBPinnedAt, optPolynomialDecoderPBPinnedAt, h136_80, h136_136, List.append_assoc]
      sep_ac_rfl

end LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked2PlacedBudgetAux

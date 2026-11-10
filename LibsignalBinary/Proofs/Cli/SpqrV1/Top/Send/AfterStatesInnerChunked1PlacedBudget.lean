/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerChunked1PlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonBudget
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.CalleeBridgesBudget
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked1
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateHeader
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.V1StateHelpers
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesVnEncode
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Phase 3e (Part 1): Delegating `V1State` Variants (`idx = 9, 3`)

Threads `RustCliAllocBudget` and `VmPreserved` through `V1State::encode_raw` variants
`ct1Acknowledged` (`idx = 9`) and `ct1Received` (`idx = 3`), re-exporting `idx = 7, 4` from `Aux`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerChunked1PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open CryptoVerification (LibsignalPlacement libsignalSessionCode lsmpl)
open CryptoVerification.RustHeap (vecU8At)
open CryptoVerification.LibsignalSpqrV1 (PolynomialDecoder PolynomialEncoder V1State)
open CryptoVerification.LibsignalSpqrV1.Proto (encodeMessage encodeOptMessage encodeVarint)
open CryptoVerification.SpqrV1.ProtoRepr
  (ChunkedCt1SampledPBGhost PolynomialDecoderPBGhost PolynomialEncoderPBGhost
   Unchunked4PBGhost Unchunked5PBGhost
   chunkedCt1SampledPBPinnedAt
   ct1SentPBEncodedLen ct1SentPBPinnedAt
   ekSentCt1ReceivedPBEncodedLen ekSentCt1ReceivedPBPinnedAt
   noneCap_add_two_beq_zero noneCap_add_two_bne_zero
   optCt1SentPBFieldEncodedLen optCt1SentPBPinnedAt
   optEkSentCt1ReceivedPBFieldEncodedLen optEkSentCt1ReceivedPBPinnedAt
   optPolynomialDecoderPBFieldEncodedLen optPolynomialDecoderPBPinnedAt
   optPolynomialEncoderPBFieldEncodedLen optPolynomialEncoderPBPinnedAt
   polynomialDecoderPBEncodedLen polynomialDecoderPBPinnedAt
   polynomialEncoderPBEncodedLen polynomialEncoderPBPinnedAt
   v1StateInnerPBPinnedAt v1StateInnerPayloadEncodedLen v1StatePBEncodedLen varintLen)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (adds_no_overflow_of_eq cmp_ls_false_of_lt
   hwVarintLen_bvShift_eq_ofNat_varintLen_norm hwVarintLen_eq_ofNat_varintLen_norm
   noneCap_add_one_beq_zero noneCap_add_one_bne_zero
   ofNat_countLeadingZeros_32 ofNat_countLeadingZeros_64
   ule_self_64 ule_zero_64 ult_self_64 ult_zero_64
   zeroExtend64_beq_zero32 zext64_truncate32)
open CryptoVerification.SpqrV1.Prost.EncodeToVec
  (StepInv bv_optCt1Sent_some_eq bv_optEkSentCt1Received_some_eq
   bv_optPolyDec_some_eq bv_optPolyEnc_some_eq
   cap_beq_len_false_of_lt
   encodeInnerState_ct1Acknowledged_eq encodeInnerState_ct1Received_eq
   encodeToVecCalleeStackOf
   noneCap2_add_two_beq_zero noneCap2_add_two_bne_zero
   noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
   optCt1SentCap optCt1SentPBPinnedAt_cap_bounds optCt1SentPBPinnedAt_eq
   optCt1SentRest optCt1SentRest_disc_bounds
   optEkSentCt1ReceivedCap optEkSentCt1ReceivedPBPinnedAt_cap_bounds optEkSentCt1ReceivedPBPinnedAt_eq
   optPolyDecCap optPolyEncCap
   optPolynomialDecoderPBPinnedAt_cap_bounds optPolynomialDecoderPBPinnedAt_eq
   optPolynomialEncoderPBPinnedAt_cap_bounds optPolynomialEncoderPBPinnedAt_eq
   ult_of_lt_of_fit v1StateInnerCap
   vecU8At_expose_one vecU8At_pack_one withStepInv)
open CryptoVerification.SpqrV1.Top.Send
  (spqrSendEncodeJumpTableBytes spqrSendEncodeJumpTableBytesAt spqrSendEncodeJumpTableBytes_eq)
open CryptoVerification.Cli.SpqrV1.Top.Send.CodePlaced (blkPl_427_ρ)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
  (spqrSendPlacedEntry spqrSendPlacedProg)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerHeaderPlacedBudget
  (StepSendInnerStateAt6616Placed
   step_send_encode_ct1Sent_budget_call_placed
   step_send_encode_ekSentCt1Received_budget_call_placed
   step_send_encode_varint_call_placed
   step_send_leaf_encLen16_call_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhaseBudget
  (encodeVarintExactSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.CalleeBridgesBudget
  (etv_ct1SentEncode_of_vecEnv_spec etv_ekSentCt1ReceivedEncode_of_vecEnv_spec)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsPlacedBudget
  (sepWP_done_tpidr sepWP_done_vm sepWPp_of_sepWP_cs_vm)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonBudget
  (etvCt1SentEncodeSpecOf etvEkSentCt1ReceivedEncodeSpecOf
   etvPolyDecoderExactSpecOf etvPolyEncoderExactSpecOf leafEncLen16Spec)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonPlacedBudget
  (etvCt1SentBudgetExactSpecOf etvEkSentCt1ReceivedBudgetExactSpecOf
   etvPolyDecoderBudgetExactSpecOf etvPolyEncoderBudgetExactSpecOf)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsChunkedV1Budget
  (chunkedCt1SampledEncodedLenPinnedSpec)

open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerChunked1PlacedBudgetAux
  (etvPolyDecoderBudgetExact_of_vm etvPolyEncoderBudgetExact_of_vm
   sepWPp_extract_pure sepWPp_extract_vecU8At_bounds)

export LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerChunked1PlacedBudgetAux
  (step_send_tail_10352_polyDec3_placed step_send_tail_11208_polyDec2_placed
   step_send_tail_11748_polyEnc_placed
   step_send_v1_ct1Sampled_placed step_send_v1_ekSentCt1Received_placed)

variable [LibsignalPlacement]

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] spqrSendPlacedEntry blkPl_427_ρ
  bv_sub_add_lit BitVec.toNat_zero
  zeroExtend64_beq_zero32
  ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 hwVarintLen_eq_ofNat_varintLen_norm
  hwVarintLen_bvShift_eq_ofNat_varintLen_norm zext64_truncate32
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  noneCap2_add_two_beq_zero noneCap2_add_two_bne_zero
  noneCap_add_two_beq_zero noneCap_add_two_bne_zero
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
  ule_zero_64 ult_zero_64 ule_self_64 ult_self_64

/-! ## 4. Variant `idx = 9`: `.ct1Acknowledged` (`+7892 .. +11220`) -/

/-- Step `+7892 .. +6216` for `is = .ct1Acknowledged v`, threading `A.pool lim st`. -/
theorem step_send_v1_ct1Acknowledged_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    {s0 s : State}
    (hct1SentLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 487)
      (withStepInv s0 (leafEncLen16Spec (ct1SentPBPinnedAt A.repAlloc) ct1SentPBEncodedLen)))
    (hpolyDecLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 493)
      (withStepInv s0 (leafEncLen16Spec (polynomialDecoderPBPinnedAt A.repAlloc) polynomialDecoderPBEncodedLen)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hct1SentEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 459)
      (withStepInv s0 (etvCt1SentBudgetExactSpecOf resStack A lim)))
    (hpolyDec : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 455)
      (withStepInv s0 (etvPolyDecoderBudgetExactSpecOf resStack A lim)))
    (sp cap ptr w25 : BitVec 64) (g : Unchunked5PBGhost × PolynomialDecoderPBGhost)
    (v : V1State.Chunked.Ct1Acknowledged) (bs : List (BitVec 8))
    (hv_len : v1StatePBEncodedLen ⟨some (.ct1Acknowledged v)⟩ < 2 ^ 64)
    (hfit : bs.length + (V1State.InnerState.encode (.ct1Acknowledged v)).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = spqrSendPlacedEntry + 7892#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace) (hinv0 : StepInv s0 s)
    (hP : P = ((optCt1SentPBPinnedAt A.repAlloc g.1 (sp + 4840#64) v.uc ∗
      optPolynomialDecoderPBPinnedAt A.repAlloc g.2 (sp + 4968#64) v.receivingEk) ∗
      ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A.repAlloc (sp + 1424#64) cap ptr bs ∗ A.pool lim st s ∗
      stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = spqrSendPlacedEntry + 6216#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = w25 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        (((optCt1SentPBPinnedAt A.repAlloc g.1 (sp + 4840#64) v.uc ∗
          optPolynomialDecoderPBPinnedAt A.repAlloc g.2 (sp + 4968#64) v.receivingEk) ∗
          ((sp + 16#64) ↦₆₄ w25) ∗
          vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs ++ V1State.InnerState.encode (.ct1Acknowledged v)) ∗
          A.pool lim st sm ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  subst hP
  rcases v with ⟨uc, receivingEk⟩
  rw [encodeInnerState_ct1Acknowledged_eq] at hfit
  simp only [List.length_append, List.length_singleton] at hfit
  have hsub_len : v1StateInnerPayloadEncodedLen (.ct1Acknowledged ⟨uc, receivingEk⟩) < 2 ^ 64 := by
    dsimp only [v1StatePBEncodedLen] at hv_len; omega
  have hlt1 : bs.length < cap.toNat := by omega
  have hfit_var : (bs ++ [0x52#8]).length +
      (encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ct1Acknowledged ⟨uc, receivingEk⟩)))).length ≤
        cap.toNat := by
    simp only [List.length_append, List.length_singleton]; omega
  refine sepWPp_extract_vecU8At_bounds (v := sp + 1424#64) (cap := cap) (ptr := ptr) (bs := bs)
    (F := optCt1SentPBPinnedAt A.repAlloc g.1 (sp + 4840#64) uc ∗
      optPolynomialDecoderPBPinnedAt A.repAlloc g.2 (sp + 4968#64) receivingEk ∗
      ((sp + 16#64) ↦₆₄ w25) ∗ A.pool lim st s ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F)
    (by sep_ac_rfl) fun _ hcap hptr => ?_
  refine sepWPp_extract_pure
    (((optCt1SentCap g.1 uc + 1#64 == 0#64) = !uc.isSome ∧
      (optCt1SentCap g.1 uc + 1#64 != 0#64) = uc.isSome) ∧
     ((optPolyDecCap g.2 receivingEk + 1#64 == 0#64) = !receivingEk.isSome ∧
      (optPolyDecCap g.2 receivingEk + 1#64 != 0#64) = receivingEk.isSome))
    (fun R' hm =>
      ⟨optCt1SentPBPinnedAt_cap_bounds (p := sp + 4840#64)
        (R := optPolynomialDecoderPBPinnedAt A.repAlloc g.2 (sp + 4968#64) receivingEk ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A.repAlloc (sp + 1424#64) cap ptr bs ∗
          A.pool lim st s ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm),
       optPolynomialDecoderPBPinnedAt_cap_bounds (p := sp + 4968#64)
        (R := optCt1SentPBPinnedAt A.repAlloc g.1 (sp + 4840#64) uc ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A.repAlloc (sp + 1424#64) cap ptr bs ∗
          A.pool lim st s ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm)⟩)
    fun ⟨⟨hcap_uc_beq, hcap_uc_bne⟩, ⟨hcap_dec_beq, hcap_dec_bne⟩⟩ => ?_
  have hbeq_false := cap_beq_len_false_of_lt hlt1 hcap
  have ⟨h1432, h1440⟩ : (sp + 1424#64) + 8#64 = sp + 1432#64 ∧
      (sp + 1424#64) + 16#64 = sp + 1440#64 := ⟨by bv_omega, by bv_omega⟩
  have hpack := vecU8At_pack_one A.repAlloc (sp + 1424#64) cap ptr bs 0x52#8 hlt1 hcap hptr
  simp only [arm64_norm, h1432, h1440] at hpack
  suffices h9568 : ∀ sm1 : State,
      sm1.pc = spqrSendPlacedEntry + 9568#64 → sm1.status = .Running → sm1.sp = sp → sm1.trace = s0.trace →
      sm1.readReg64 .x19 = s.readReg64 .x19 → sm1.readReg64 .x20 = sp + 4704#64 →
      sm1.readReg64 .x21 = s.readReg64 .x21 → sm1.readReg64 .x22 = optCt1SentCap g.1 uc →
      sm1.readReg64 .x23 = s.readReg64 .x23 →
      sm1.readReg64 .x26 = BitVec.ofNat 64 (optCt1SentPBFieldEncodedLen uc) →
      sm1.readReg64 .x27 = s.readReg64 .x27 → sm1.readReg64 .x28 = s.readReg64 .x28 →
      sm1.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm1 →
      SepWPp (spqrSendPlacedProg ext) ret sm1
        (((optCt1SentPBPinnedAt A.repAlloc g.1 (sp + 4840#64) uc ∗
          optPolynomialDecoderPBPinnedAt A.repAlloc g.2 (sp + 4968#64) receivingEk) ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs ++ [0x52#8]) ∗
          A.pool lim st sm1 ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom by
    rw [vecU8At_expose_one A.repAlloc (sp + 1424#64) cap ptr bs hlt1 hcap hptr, h1432, h1440]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun b0 => ?_
    cases uc with
    | none =>
      rw [optCt1SentPBPinnedAt_eq A.repAlloc g.1 (sp + 4840#64) none]
      simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
      dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
      apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 9568#64)
      by_vm_steps
        wp_steps
        apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv1
        have hpool1 : A.pool lim st s = A.pool lim st _ := (A.pool_of_vmPreserved hinv1.2).symm
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (h9568 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [optCt1SentPBFieldEncodedLen, arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1.1))
        rw [← optCt1SentPBPinnedAt_eq A.repAlloc g.1 (sp + 4840#64) none, ← hpack, hpool1]; rfl
    | some u =>
      rw [optCt1SentPBPinnedAt_eq A.repAlloc g.1 (sp + 4840#64) (some u)]
      simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      have ⟨hu_fit, hopt_u_lt⟩ :
          ct1SentPBEncodedLen u < 2 ^ 64 ∧ optCt1SentPBFieldEncodedLen (some u) < 2 ^ 64 :=
        ⟨by dsimp only [v1StateInnerPayloadEncodedLen, optCt1SentPBFieldEncodedLen] at hsub_len; omega,
         by dsimp only [v1StateInnerPayloadEncodedLen] at hsub_len; omega⟩
      have hvar_u_lt :
          varintLen (BitVec.ofNat 64 (ct1SentPBEncodedLen u)) <
            optCt1SentPBFieldEncodedLen (some u) := by
        dsimp only [optCt1SentPBFieldEncodedLen]; omega
      have ⟨⟨_, _, _, _, _⟩, hult_u, hopt_u_eq⟩ :=
        (⟨cmp_ls_false_of_lt hvar_u_lt hopt_u_lt,
          ult_of_lt_of_fit hvar_u_lt hopt_u_lt,
          bv_optCt1Sent_some_eq u⟩ : _ ∧ _ ∧ _)
      dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
      apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 487)
      by_vm_steps
        wp_steps
        apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv1
        rw [← optCt1SentPBPinnedAt_eq A.repAlloc g.1 (sp + 4840#64) (some u)]
        refine step_send_leaf_encLen16_call_placed hres ext
          (ct1SentPBPinnedAt A.repAlloc) ct1SentPBEncodedLen hct1SentLen
          (sp + 4840#64) sp (spqrSendPlacedEntry + 7956#64) g.1 u hu_fit
          (F := optPolynomialDecoderPBPinnedAt A.repAlloc g.2 (sp + 4968#64) receivingEk ∗
            ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs ++ [0x52#8]) ∗
            A.pool lim st s ∗ F)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
          (hinv0.trans hinv1.1) (by rw [← hpack]; dsimp only [optCt1SentPBPinnedAt]; sep_ac_rfl) ?_
        intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1 hcsm1 hinv_m1 hvm_m1
        rcases hcsm1 with ⟨hm19, hm20, hm21, hm22, hm23, _, _, _, hm27, hm28, hmfp, _⟩
        simp only [arm64_norm] at hm19 hm20 hm21 hm22 hm23 hm27 hm28 hmfp
        dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
        apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 9568#64)
        wp_steps
        apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv2
        have hpool2 : A.pool lim st s = A.pool lim st _ :=
          (A.pool_of_vmPreserved (hinv1.2.trans (hvm_m1.trans hinv2.2))).symm
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (h9568 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (hinv_m1.trans hinv2.1))
        dsimp only [optCt1SentPBPinnedAt]; rw [hpool2]; sep_ac_rfl
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx26_1 hx27_1 hx28_1 hfp_1 hinv_1
  suffices h10372 : ∀ sm2 : State,
      sm2.pc = spqrSendPlacedEntry + 10372#64 → sm2.status = .Running → sm2.sp = sp → sm2.trace = s0.trace →
      sm2.readReg64 .x8 = BitVec.ofNat 64 (optPolynomialDecoderPBFieldEncodedLen receivingEk) →
      sm2.readReg64 .x19 = s.readReg64 .x19 → sm2.readReg64 .x20 = sp + 4704#64 →
      sm2.readReg64 .x21 = s.readReg64 .x21 → sm2.readReg64 .x22 = optCt1SentCap g.1 uc →
      sm2.readReg64 .x23 = s.readReg64 .x23 → sm2.readReg64 .x24 = sp + 4704#64 →
      sm2.readReg64 .x25 = optPolyDecCap g.2 receivingEk →
      sm2.readReg64 .x26 = BitVec.ofNat 64 (optCt1SentPBFieldEncodedLen uc) →
      sm2.readReg64 .x27 = s.readReg64 .x27 → sm2.readReg64 .x28 = s.readReg64 .x28 →
      sm2.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm2 →
      SepWPp (spqrSendPlacedProg ext) ret sm2
        (((optCt1SentPBPinnedAt A.repAlloc g.1 (sp + 4840#64) uc ∗
          optPolynomialDecoderPBPinnedAt A.repAlloc g.2 (sp + 4968#64) receivingEk) ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs ++ [0x52#8]) ∗
          A.pool lim st sm2 ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom by
    cases receivingEk with
    | none =>
      rw [optPolynomialDecoderPBPinnedAt_eq A.repAlloc g.2 (sp + 4968#64) none]
      simp only [Option.isSome_none, Bool.not_false] at hcap_dec_beq hcap_dec_bne
      dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
      apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 10372#64)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv2
      have hpool2 : A.pool lim st sm1 = A.pool lim st _ := (A.pool_of_vmPreserved hinv2.2).symm
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h10372 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [optPolynomialDecoderPBFieldEncodedLen, arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (hinv_1.trans hinv2.1))
      rw [← optPolynomialDecoderPBPinnedAt_eq A.repAlloc g.2 (sp + 4968#64) none, hpool2]
    | some dec =>
      rw [optPolynomialDecoderPBPinnedAt_eq A.repAlloc g.2 (sp + 4968#64) (some dec)]
      simp only [Option.isSome_some, Bool.not_true] at hcap_dec_beq hcap_dec_bne
      have ⟨hdec_fit, hopt_d_lt⟩ :
          polynomialDecoderPBEncodedLen dec < 2 ^ 64 ∧ optPolynomialDecoderPBFieldEncodedLen (some dec) < 2 ^ 64 :=
        ⟨by dsimp only [v1StateInnerPayloadEncodedLen, optPolynomialDecoderPBFieldEncodedLen] at hsub_len; omega,
         by dsimp only [v1StateInnerPayloadEncodedLen] at hsub_len; omega⟩
      have hvar_d_lt :
          varintLen (BitVec.ofNat 64 (polynomialDecoderPBEncodedLen dec)) <
            optPolynomialDecoderPBFieldEncodedLen (some dec) := by
        dsimp only [optPolynomialDecoderPBFieldEncodedLen]; omega
      have ⟨⟨_, _, _, _, _⟩, hult_d, hopt_d_eq⟩ :=
        (⟨cmp_ls_false_of_lt hvar_d_lt hopt_d_lt,
          ult_of_lt_of_fit hvar_d_lt hopt_d_lt,
          bv_optPolyDec_some_eq dec⟩ : _ ∧ _ ∧ _)
      dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
      apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 493)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv2
      rw [← optPolynomialDecoderPBPinnedAt_eq A.repAlloc g.2 (sp + 4968#64) (some dec)]
      refine step_send_leaf_encLen16_call_placed hres ext
        (polynomialDecoderPBPinnedAt A.repAlloc) polynomialDecoderPBEncodedLen hpolyDecLen
        (sp + 4968#64) sp (spqrSendPlacedEntry + 9596#64) g.2 dec hdec_fit
        (F := optCt1SentPBPinnedAt A.repAlloc g.1 (sp + 4840#64) uc ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs ++ [0x52#8]) ∗
          A.pool lim st sm1 ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (hinv_1.trans hinv2.1) (by dsimp only [optPolynomialDecoderPBPinnedAt]; sep_ac_rfl) ?_
      intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx0m2 hcsm2 hinv_m2 hvm_m2
      rcases hcsm2 with ⟨hm2_19, hm2_20, hm2_21, hm2_22, hm2_23, hm2_24, hm2_25, hm2_26, hm2_27, hm2_28, hm2_fp, _⟩
      simp only [arm64_norm, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx26_1, hx27_1, hx28_1, hfp_1]
        at hm2_19 hm2_20 hm2_21 hm2_22 hm2_23 hm2_24 hm2_25 hm2_26 hm2_27 hm2_28 hm2_fp
      dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
      apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 10372#64)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv3
      have hpool3 : A.pool lim st sm1 = A.pool lim st _ :=
        (A.pool_of_vmPreserved (hinv2.2.trans (hvm_m2.trans hinv3.2))).symm
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h10372 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hinv_m2.trans hinv3.1))
      dsimp only [optPolynomialDecoderPBPinnedAt]; rw [hpool3]; sep_ac_rfl
  intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx8_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hinv_2
  have ⟨hadd_sum, hult_sum, hule_sum, hult_sum2, hule_sum2⟩ := adds_no_overflow_of_eq
      (a := optPolynomialDecoderPBFieldEncodedLen receivingEk)
      (b := optCt1SentPBFieldEncodedLen uc)
      (c := v1StateInnerPayloadEncodedLen (.ct1Acknowledged ⟨uc, receivingEk⟩))
      rfl hsub_len
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
  apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 451)
  wp_steps
  apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, wp_norm, *])
  intro hinv3
  have hpool3 : A.pool lim st sm2 = A.pool lim st _ := (A.pool_of_vmPreserved hinv3.2).symm
  set bs1 := (bs ++ [0x52#8]) ++
    encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ct1Acknowledged ⟨uc, receivingEk⟩)))
  refine step_send_encode_varint_call_placed A lim st hvarint
    (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ct1Acknowledged ⟨uc, receivingEk⟩)))
    (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 10388#64) (bs ++ [0x52#8]) hfit_var
    (F := (optCt1SentPBPinnedAt A.repAlloc g.1 (sp + 4840#64) uc ∗
      optPolynomialDecoderPBPinnedAt A.repAlloc g.2 (sp + 4968#64) receivingEk) ∗
      ((sp + 16#64) ↦₆₄ w25) ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hinv_2.trans hinv3.1) (by rw [hpool3]; sep_ac_rfl) ?_
  intro sm3 hpcm3 hrunm3 hspm3 htrm3 hcsm3 hinv_m3
  rcases hcsm3 with ⟨hm3_19, hm3_20, hm3_21, hm3_22, hm3_23, hm3_24, hm3_25, _, hm3_27, hm3_28, hm3_fp, _⟩
  simp only [arm64_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx27_2, hx28_2, hfp_2]
    at hm3_19 hm3_20 hm3_21 hm3_22 hm3_23 hm3_24 hm3_25 hm3_27 hm3_28 hm3_fp
  set bs2 := bs1 ++ encodeOptMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 uc
  suffices h10408 : ∀ sm4 : State,
      sm4.pc = spqrSendPlacedEntry + 10408#64 → sm4.status = .Running → sm4.sp = sp → sm4.trace = s0.trace →
      sm4.readReg64 .x19 = s.readReg64 .x19 → sm4.readReg64 .x21 = s.readReg64 .x21 →
      sm4.readReg64 .x23 = s.readReg64 .x23 → sm4.readReg64 .x24 = sp + 4704#64 →
      sm4.readReg64 .x25 = optPolyDecCap g.2 receivingEk →
      sm4.readReg64 .x27 = s.readReg64 .x27 → sm4.readReg64 .x28 = s.readReg64 .x28 →
      sm4.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm4 →
      SepWPp (spqrSendPlacedProg ext) ret sm4
        (((optCt1SentPBPinnedAt A.repAlloc g.1 (sp + 4840#64) uc ∗
          optPolynomialDecoderPBPinnedAt A.repAlloc g.2 (sp + 4968#64) receivingEk) ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A.repAlloc (sp + 1424#64) cap ptr bs2 ∗
          A.pool lim st sm4 ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom by
    cases uc with
    | none =>
      simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
      dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
      apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 10408#64)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv4
      have hpool4 : A.pool lim st sm3 = A.pool lim st _ := (A.pool_of_vmPreserved hinv4.2).symm
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h10408 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hinv_m3.trans hinv4.1))
      rw [hpool4]
      simp +zetaDelta only [bs2, bs1, encodeOptMessage, List.append_nil]; sep_ac_rfl
    | some u =>
      simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      have hfit_uc :
          bs1.length + (encodeMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 u).length ≤ cap.toNat := by
        simp +zetaDelta only [bs1, encodeOptMessage, List.length_append, List.length_singleton] at hfit ⊢
        omega
      dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
      apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 459)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv4
      have hpool4 : A.pool lim st sm3 = A.pool lim st _ := (A.pool_of_vmPreserved hinv4.2).symm
      refine step_send_encode_ct1Sent_budget_call_placed A lim st ext hct1SentEnc
        (sp + 4840#64) (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 10408#64) g.1 u bs1 hfit_uc
        (F := optPolynomialDecoderPBPinnedAt A.repAlloc g.2 (sp + 4968#64) receivingEk ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m3.trans hinv4.1)
        (by dsimp +zetaDelta only [bs1, optCt1SentPBPinnedAt]; rw [hpool4]; sep_ac_rfl) ?_
      intro sm4 hpcm4 hrunm4 hspm4 htrm4 hcsm4 hinv_m4
      rcases hcsm4 with ⟨hm4_19, _, hm4_21, _, hm4_23, hm4_24, hm4_25, _, hm4_27, hm4_28, hm4_fp, _⟩
      simp only [arm64_norm, hm3_19, hm3_21, hm3_23, hm3_24, hm3_25, hm3_27, hm3_28, hm3_fp]
        at hm4_19 hm4_21 hm4_23 hm4_24 hm4_25 hm4_27 hm4_28 hm4_fp
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h10408 sm4 hpcm4 hrunm4 hspm4 htrm4 hm4_19 hm4_21 hm4_23 hm4_24 hm4_25 hm4_27 hm4_28 hm4_fp hinv_m4)
      simp +zetaDelta only [bs2, bs1, encodeOptMessage, optCt1SentPBPinnedAt]; sep_ac_rfl
  intro sm4 hpcm4 hrunm4 hspm4 htrm4 hx19_4 hx21_4 hx23_4 hx24_4 hx25_4 hx27_4 hx28_4 hfp_4 hinv_4
  cases receivingEk with
  | none =>
    simp only [Option.isSome_none, Bool.not_false] at hcap_dec_beq hcap_dec_bne
    dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
    apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 6216#64)
    wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv5
    have hpool5 : A.pool lim st sm4 = A.pool lim st _ := (A.pool_of_vmPreserved hinv5.2).symm
    refine SepWPp.weaken_pre (Entails.of_eq ?_)
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (hinv_4.trans hinv5.1))
    rw [encodeInnerState_ct1Acknowledged_eq, hpool5]
    simp +zetaDelta only [bs2, bs1, encodeOptMessage, List.append_nil, List.append_assoc]
  | some dec =>
    simp only [Option.isSome_some, Bool.not_true] at hcap_dec_beq hcap_dec_bne
    have hfit_dec :
        bs2.length + (encodeMessage PolynomialDecoder.encodeRaw 2#32 dec).length ≤ cap.toNat := by
      simp +zetaDelta only [bs2, bs1, encodeOptMessage, List.length_append, List.length_singleton] at hfit ⊢
      omega
    dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
    apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 11208#64)
    wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv5
    have hpool5 : A.pool lim st sm4 = A.pool lim st _ := (A.pool_of_vmPreserved hinv5.2).symm
    refine step_send_tail_11208_polyDec2_placed A lim st ext hpolyDec
      (sp + 4968#64) sp cap ptr g.2 dec bs2 hfit_dec halign
      (F := optCt1SentPBPinnedAt A.repAlloc g.1 (sp + 4840#64) uc ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hinv_4.trans hinv5.1)
      (by dsimp +zetaDelta only [optPolynomialDecoderPBPinnedAt, bs2, bs1]; rw [hpool5]; sep_ac_rfl) ?_
    intro sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp hinv_m5
    simp only [arm64_norm, hx19_4, hx21_4, hx23_4, hx27_4, hx28_4, hfp_4]
      at hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp
    refine SepWPp.weaken_pre (Entails.of_eq ?_)
      (hnext sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp hinv_m5)
    rw [encodeInnerState_ct1Acknowledged_eq]
    simp +zetaDelta only [bs2, bs1, encodeOptMessage,
      optPolynomialDecoderPBPinnedAt, List.append_assoc]; sep_ac_rfl

/-! ## 5. Variant `idx = 3`: `.ct1Received` (`+8372 .. +11756`) -/

/-- Step `+8372 .. +6216` for `is = .ct1Received v`, threading `A.pool lim st`. -/
theorem step_send_v1_ct1Received_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    {s0 s : State}
    (hekLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 499)
      (withStepInv s0 (leafEncLen16Spec (ekSentCt1ReceivedPBPinnedAt A.repAlloc) ekSentCt1ReceivedPBEncodedLen)))
    (hpolyEncLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 480)
      (withStepInv s0 (leafEncLen16Spec (polynomialEncoderPBPinnedAt A.repAlloc) polynomialEncoderPBEncodedLen)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hekEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 458)
      (withStepInv s0 (etvEkSentCt1ReceivedBudgetExactSpecOf resStack A lim)))
    (hpolyEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 456)
      (withStepInv s0 (etvPolyEncoderBudgetExactSpecOf resStack A lim)))
    (sp cap ptr w25 : BitVec 64) (g : Unchunked4PBGhost × PolynomialEncoderPBGhost)
    (v : V1State.Chunked.Ct1Received) (bs : List (BitVec 8))
    (hv_len : v1StatePBEncodedLen ⟨some (.ct1Received v)⟩ < 2 ^ 64)
    (hfit : bs.length + (V1State.InnerState.encode (.ct1Received v)).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = spqrSendPlacedEntry + 8372#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace) (hinv0 : StepInv s0 s)
    (hP : P = ((optEkSentCt1ReceivedPBPinnedAt A.repAlloc g.1 (sp + 4840#64) v.uc ∗
      optPolynomialEncoderPBPinnedAt A.repAlloc g.2 (sp + 4944#64) v.sendingEk) ∗
      ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A.repAlloc (sp + 1424#64) cap ptr bs ∗ A.pool lim st s ∗
      stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = spqrSendPlacedEntry + 6216#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = w25 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        (((optEkSentCt1ReceivedPBPinnedAt A.repAlloc g.1 (sp + 4840#64) v.uc ∗
          optPolynomialEncoderPBPinnedAt A.repAlloc g.2 (sp + 4944#64) v.sendingEk) ∗
          ((sp + 16#64) ↦₆₄ w25) ∗
          vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs ++ V1State.InnerState.encode (.ct1Received v)) ∗
          A.pool lim st sm ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  subst hP
  rcases v with ⟨uc, sendingEk⟩
  rw [encodeInnerState_ct1Received_eq] at hfit
  simp only [List.length_append, List.length_singleton] at hfit
  have hsub_len : v1StateInnerPayloadEncodedLen (.ct1Received ⟨uc, sendingEk⟩) < 2 ^ 64 := by
    dsimp only [v1StatePBEncodedLen] at hv_len; omega
  have hlt1 : bs.length < cap.toNat := by omega
  have hfit_var : (bs ++ [0x22#8]).length +
      (encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ct1Received ⟨uc, sendingEk⟩)))).length ≤
        cap.toNat := by
    simp only [List.length_append, List.length_singleton]; omega
  refine sepWPp_extract_vecU8At_bounds (v := sp + 1424#64) (cap := cap) (ptr := ptr) (bs := bs)
    (F := optEkSentCt1ReceivedPBPinnedAt A.repAlloc g.1 (sp + 4840#64) uc ∗
      optPolynomialEncoderPBPinnedAt A.repAlloc g.2 (sp + 4944#64) sendingEk ∗
      ((sp + 16#64) ↦₆₄ w25) ∗ A.pool lim st s ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F)
    (by sep_ac_rfl) fun _ hcap hptr => ?_
  refine sepWPp_extract_pure
    (((optEkSentCt1ReceivedCap g.1 uc + 1#64 == 0#64) = !uc.isSome ∧
      (optEkSentCt1ReceivedCap g.1 uc + 1#64 != 0#64) = uc.isSome) ∧
     ((optPolyEncCap g.2 sendingEk + 1#64 == 0#64) = !sendingEk.isSome ∧
      (optPolyEncCap g.2 sendingEk + 1#64 != 0#64) = sendingEk.isSome))
    (fun R' hm =>
      ⟨optEkSentCt1ReceivedPBPinnedAt_cap_bounds (p := sp + 4840#64)
        (R := optPolynomialEncoderPBPinnedAt A.repAlloc g.2 (sp + 4944#64) sendingEk ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A.repAlloc (sp + 1424#64) cap ptr bs ∗
          A.pool lim st s ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm),
       optPolynomialEncoderPBPinnedAt_cap_bounds (p := sp + 4944#64)
        (R := optEkSentCt1ReceivedPBPinnedAt A.repAlloc g.1 (sp + 4840#64) uc ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A.repAlloc (sp + 1424#64) cap ptr bs ∗
          A.pool lim st s ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm)⟩)
    fun ⟨⟨hcap_uc_beq, hcap_uc_bne⟩, ⟨hcap_enc_beq, hcap_enc_bne⟩⟩ => ?_
  have hbeq_false := cap_beq_len_false_of_lt hlt1 hcap
  have ⟨h1432, h1440⟩ : (sp + 1424#64) + 8#64 = sp + 1432#64 ∧
      (sp + 1424#64) + 16#64 = sp + 1440#64 := ⟨by bv_omega, by bv_omega⟩
  have hpack := vecU8At_pack_one A.repAlloc (sp + 1424#64) cap ptr bs 0x22#8 hlt1 hcap hptr
  simp only [arm64_norm, h1432, h1440] at hpack
  suffices h9644 : ∀ sm1 : State,
      sm1.pc = spqrSendPlacedEntry + 9644#64 → sm1.status = .Running → sm1.sp = sp → sm1.trace = s0.trace →
      sm1.readReg64 .x19 = s.readReg64 .x19 → sm1.readReg64 .x20 = sp + 4704#64 →
      sm1.readReg64 .x21 = s.readReg64 .x21 → sm1.readReg64 .x22 = optEkSentCt1ReceivedCap g.1 uc →
      sm1.readReg64 .x23 = s.readReg64 .x23 →
      sm1.readReg64 .x26 = BitVec.ofNat 64 (optEkSentCt1ReceivedPBFieldEncodedLen uc) →
      sm1.readReg64 .x27 = s.readReg64 .x27 → sm1.readReg64 .x28 = s.readReg64 .x28 →
      sm1.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm1 →
      SepWPp (spqrSendPlacedProg ext) ret sm1
        (((optEkSentCt1ReceivedPBPinnedAt A.repAlloc g.1 (sp + 4840#64) uc ∗
          optPolynomialEncoderPBPinnedAt A.repAlloc g.2 (sp + 4944#64) sendingEk) ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs ++ [0x22#8]) ∗
          A.pool lim st sm1 ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom by
    rw [vecU8At_expose_one A.repAlloc (sp + 1424#64) cap ptr bs hlt1 hcap hptr, h1432, h1440]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun b0 => ?_
    cases uc with
    | none =>
      rw [optEkSentCt1ReceivedPBPinnedAt_eq A.repAlloc g.1 (sp + 4840#64) none]
      simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
      dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
      apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 9644#64)
      by_vm_steps
        wp_steps
        apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv1
        have hpool1 : A.pool lim st s = A.pool lim st _ := (A.pool_of_vmPreserved hinv1.2).symm
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (h9644 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [optEkSentCt1ReceivedPBFieldEncodedLen, arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1.1))
        rw [← optEkSentCt1ReceivedPBPinnedAt_eq A.repAlloc g.1 (sp + 4840#64) none, ← hpack, hpool1]; rfl
    | some u =>
      rw [optEkSentCt1ReceivedPBPinnedAt_eq A.repAlloc g.1 (sp + 4840#64) (some u)]
      simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      have ⟨hu_fit, hopt_u_lt⟩ :
          ekSentCt1ReceivedPBEncodedLen u < 2 ^ 64 ∧ optEkSentCt1ReceivedPBFieldEncodedLen (some u) < 2 ^ 64 :=
        ⟨by dsimp only [v1StateInnerPayloadEncodedLen, optEkSentCt1ReceivedPBFieldEncodedLen] at hsub_len; omega,
         by dsimp only [v1StateInnerPayloadEncodedLen] at hsub_len; omega⟩
      have hvar_u_lt :
          varintLen (BitVec.ofNat 64 (ekSentCt1ReceivedPBEncodedLen u)) <
            optEkSentCt1ReceivedPBFieldEncodedLen (some u) := by
        dsimp only [optEkSentCt1ReceivedPBFieldEncodedLen]; omega
      have ⟨⟨_, _, _, _, _⟩, hult_u, hopt_u_eq⟩ :=
        (⟨cmp_ls_false_of_lt hvar_u_lt hopt_u_lt,
          ult_of_lt_of_fit hvar_u_lt hopt_u_lt,
          bv_optEkSentCt1Received_some_eq u⟩ : _ ∧ _ ∧ _)
      dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
      apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 499)
      by_vm_steps
        wp_steps
        apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv1
        rw [← optEkSentCt1ReceivedPBPinnedAt_eq A.repAlloc g.1 (sp + 4840#64) (some u)]
        refine step_send_leaf_encLen16_call_placed hres ext
          (ekSentCt1ReceivedPBPinnedAt A.repAlloc) ekSentCt1ReceivedPBEncodedLen hekLen
          (sp + 4840#64) sp (spqrSendPlacedEntry + 8436#64) g.1 u hu_fit
          (F := optPolynomialEncoderPBPinnedAt A.repAlloc g.2 (sp + 4944#64) sendingEk ∗
            ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs ++ [0x22#8]) ∗
            A.pool lim st s ∗ F)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
          (hinv0.trans hinv1.1) (by rw [← hpack]; dsimp only [optEkSentCt1ReceivedPBPinnedAt]; sep_ac_rfl) ?_
        intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1 hcsm1 hinv_m1 hvm_m1
        rcases hcsm1 with ⟨hm19, hm20, hm21, hm22, hm23, _, _, _, hm27, hm28, hmfp, _⟩
        simp only [arm64_norm] at hm19 hm20 hm21 hm22 hm23 hm27 hm28 hmfp
        dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
        apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 9644#64)
        wp_steps
        apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv2
        have hpool2 : A.pool lim st s = A.pool lim st _ :=
          (A.pool_of_vmPreserved (hinv1.2.trans (hvm_m1.trans hinv2.2))).symm
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (h9644 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (hinv_m1.trans hinv2.1))
        dsimp only [optEkSentCt1ReceivedPBPinnedAt]; rw [hpool2]; sep_ac_rfl
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx26_1 hx27_1 hx28_1 hfp_1 hinv_1
  suffices h10432 : ∀ sm2 : State,
      sm2.pc = spqrSendPlacedEntry + 10432#64 → sm2.status = .Running → sm2.sp = sp → sm2.trace = s0.trace →
      sm2.readReg64 .x8 = BitVec.ofNat 64 (optPolynomialEncoderPBFieldEncodedLen sendingEk) →
      sm2.readReg64 .x19 = s.readReg64 .x19 → sm2.readReg64 .x20 = sp + 4704#64 →
      sm2.readReg64 .x21 = s.readReg64 .x21 → sm2.readReg64 .x22 = optEkSentCt1ReceivedCap g.1 uc →
      sm2.readReg64 .x23 = s.readReg64 .x23 → sm2.readReg64 .x24 = sp + 4704#64 →
      sm2.readReg64 .x25 = optPolyEncCap g.2 sendingEk →
      sm2.readReg64 .x26 = BitVec.ofNat 64 (optEkSentCt1ReceivedPBFieldEncodedLen uc) →
      sm2.readReg64 .x27 = s.readReg64 .x27 → sm2.readReg64 .x28 = s.readReg64 .x28 →
      sm2.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm2 →
      SepWPp (spqrSendPlacedProg ext) ret sm2
        (((optEkSentCt1ReceivedPBPinnedAt A.repAlloc g.1 (sp + 4840#64) uc ∗
          optPolynomialEncoderPBPinnedAt A.repAlloc g.2 (sp + 4944#64) sendingEk) ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs ++ [0x22#8]) ∗
          A.pool lim st sm2 ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom by
    cases sendingEk with
    | none =>
      rw [optPolynomialEncoderPBPinnedAt_eq A.repAlloc g.2 (sp + 4944#64) none]
      simp only [Option.isSome_none, Bool.not_false] at hcap_enc_beq hcap_enc_bne
      dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
      apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 10432#64)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv2
      have hpool2 : A.pool lim st sm1 = A.pool lim st _ := (A.pool_of_vmPreserved hinv2.2).symm
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h10432 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [optPolynomialEncoderPBFieldEncodedLen, arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (hinv_1.trans hinv2.1))
      rw [← optPolynomialEncoderPBPinnedAt_eq A.repAlloc g.2 (sp + 4944#64) none, hpool2]
    | some enc =>
      rw [optPolynomialEncoderPBPinnedAt_eq A.repAlloc g.2 (sp + 4944#64) (some enc)]
      simp only [Option.isSome_some, Bool.not_true] at hcap_enc_beq hcap_enc_bne
      have ⟨henc_fit, hopt_e_lt⟩ :
          polynomialEncoderPBEncodedLen enc < 2 ^ 64 ∧ optPolynomialEncoderPBFieldEncodedLen (some enc) < 2 ^ 64 :=
        ⟨by dsimp only [v1StateInnerPayloadEncodedLen, optPolynomialEncoderPBFieldEncodedLen] at hsub_len; omega,
         by dsimp only [v1StateInnerPayloadEncodedLen] at hsub_len; omega⟩
      have hvar_e_lt :
          varintLen (BitVec.ofNat 64 (polynomialEncoderPBEncodedLen enc)) <
            optPolynomialEncoderPBFieldEncodedLen (some enc) := by
        dsimp only [optPolynomialEncoderPBFieldEncodedLen]; omega
      have ⟨⟨_, _, _, _, _⟩, hult_e, hopt_e_eq⟩ :=
        (⟨cmp_ls_false_of_lt hvar_e_lt hopt_e_lt,
          ult_of_lt_of_fit hvar_e_lt hopt_e_lt,
          bv_optPolyEnc_some_eq enc⟩ : _ ∧ _ ∧ _)
      dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
      apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 480)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv2
      rw [← optPolynomialEncoderPBPinnedAt_eq A.repAlloc g.2 (sp + 4944#64) (some enc)]
      refine step_send_leaf_encLen16_call_placed hres ext
        (polynomialEncoderPBPinnedAt A.repAlloc) polynomialEncoderPBEncodedLen hpolyEncLen
        (sp + 4944#64) sp (spqrSendPlacedEntry + 9672#64) g.2 enc henc_fit
        (F := optEkSentCt1ReceivedPBPinnedAt A.repAlloc g.1 (sp + 4840#64) uc ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs ++ [0x22#8]) ∗
          A.pool lim st sm1 ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (hinv_1.trans hinv2.1) (by dsimp only [optPolynomialEncoderPBPinnedAt]; sep_ac_rfl) ?_
      intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx0m2 hcsm2 hinv_m2 hvm_m2
      rcases hcsm2 with ⟨hm2_19, hm2_20, hm2_21, hm2_22, hm2_23, hm2_24, hm2_25, hm2_26, hm2_27, hm2_28, hm2_fp, _⟩
      simp only [arm64_norm, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx26_1, hx27_1, hx28_1, hfp_1]
        at hm2_19 hm2_20 hm2_21 hm2_22 hm2_23 hm2_24 hm2_25 hm2_26 hm2_27 hm2_28 hm2_fp
      dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
      apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 10432#64)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv3
      have hpool3 : A.pool lim st sm1 = A.pool lim st _ :=
        (A.pool_of_vmPreserved (hinv2.2.trans (hvm_m2.trans hinv3.2))).symm
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h10432 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hinv_m2.trans hinv3.1))
      dsimp only [optPolynomialEncoderPBPinnedAt]; rw [hpool3]; sep_ac_rfl
  intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx8_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hinv_2
  have ⟨hadd_sum, hult_sum, hule_sum, hult_sum2, hule_sum2⟩ := adds_no_overflow_of_eq
      (a := optPolynomialEncoderPBFieldEncodedLen sendingEk)
      (b := optEkSentCt1ReceivedPBFieldEncodedLen uc)
      (c := v1StateInnerPayloadEncodedLen (.ct1Received ⟨uc, sendingEk⟩))
      rfl hsub_len
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
  apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 451)
  wp_steps
  apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, wp_norm, *])
  intro hinv3
  have hpool3 : A.pool lim st sm2 = A.pool lim st _ := (A.pool_of_vmPreserved hinv3.2).symm
  set bs1 := (bs ++ [0x22#8]) ++
    encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ct1Received ⟨uc, sendingEk⟩)))
  refine step_send_encode_varint_call_placed A lim st hvarint
    (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ct1Received ⟨uc, sendingEk⟩)))
    (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 10448#64) (bs ++ [0x22#8]) hfit_var
    (F := (optEkSentCt1ReceivedPBPinnedAt A.repAlloc g.1 (sp + 4840#64) uc ∗
      optPolynomialEncoderPBPinnedAt A.repAlloc g.2 (sp + 4944#64) sendingEk) ∗
      ((sp + 16#64) ↦₆₄ w25) ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hinv_2.trans hinv3.1) (by rw [hpool3]; sep_ac_rfl) ?_
  intro sm3 hpcm3 hrunm3 hspm3 htrm3 hcsm3 hinv_m3
  rcases hcsm3 with ⟨hm3_19, hm3_20, hm3_21, hm3_22, hm3_23, hm3_24, hm3_25, _, hm3_27, hm3_28, hm3_fp, _⟩
  simp only [arm64_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx27_2, hx28_2, hfp_2]
    at hm3_19 hm3_20 hm3_21 hm3_22 hm3_23 hm3_24 hm3_25 hm3_27 hm3_28 hm3_fp
  set bs2 := bs1 ++ encodeOptMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 uc
  suffices h10468 : ∀ sm4 : State,
      sm4.pc = spqrSendPlacedEntry + 10468#64 → sm4.status = .Running → sm4.sp = sp → sm4.trace = s0.trace →
      sm4.readReg64 .x19 = s.readReg64 .x19 → sm4.readReg64 .x21 = s.readReg64 .x21 →
      sm4.readReg64 .x23 = s.readReg64 .x23 → sm4.readReg64 .x24 = sp + 4704#64 →
      sm4.readReg64 .x25 = optPolyEncCap g.2 sendingEk →
      sm4.readReg64 .x27 = s.readReg64 .x27 → sm4.readReg64 .x28 = s.readReg64 .x28 →
      sm4.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm4 →
      SepWPp (spqrSendPlacedProg ext) ret sm4
        (((optEkSentCt1ReceivedPBPinnedAt A.repAlloc g.1 (sp + 4840#64) uc ∗
          optPolynomialEncoderPBPinnedAt A.repAlloc g.2 (sp + 4944#64) sendingEk) ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A.repAlloc (sp + 1424#64) cap ptr bs2 ∗
          A.pool lim st sm4 ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom by
    cases uc with
    | none =>
      simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
      dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
      apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 10468#64)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv4
      have hpool4 : A.pool lim st sm3 = A.pool lim st _ := (A.pool_of_vmPreserved hinv4.2).symm
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h10468 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hinv_m3.trans hinv4.1))
      rw [hpool4]
      simp +zetaDelta only [bs2, bs1, encodeOptMessage, List.append_nil]; sep_ac_rfl
    | some u =>
      simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      have hfit_uc :
          bs1.length + (encodeMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 u).length ≤ cap.toNat := by
        simp +zetaDelta only [bs1, encodeOptMessage, List.length_append, List.length_singleton] at hfit ⊢
        omega
      dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
      apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 458)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv4
      have hpool4 : A.pool lim st sm3 = A.pool lim st _ := (A.pool_of_vmPreserved hinv4.2).symm
      refine step_send_encode_ekSentCt1Received_budget_call_placed A lim st ext hekEnc
        (sp + 4840#64) (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 10468#64) g.1 u bs1 hfit_uc
        (F := optPolynomialEncoderPBPinnedAt A.repAlloc g.2 (sp + 4944#64) sendingEk ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m3.trans hinv4.1)
        (by dsimp +zetaDelta only [bs1, optEkSentCt1ReceivedPBPinnedAt]; rw [hpool4]; sep_ac_rfl) ?_
      intro sm4 hpcm4 hrunm4 hspm4 htrm4 hcsm4 hinv_m4
      rcases hcsm4 with ⟨hm4_19, _, hm4_21, _, hm4_23, hm4_24, hm4_25, _, hm4_27, hm4_28, hm4_fp, _⟩
      simp only [arm64_norm, hm3_19, hm3_21, hm3_23, hm3_24, hm3_25, hm3_27, hm3_28, hm3_fp]
        at hm4_19 hm4_21 hm4_23 hm4_24 hm4_25 hm4_27 hm4_28 hm4_fp
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h10468 sm4 hpcm4 hrunm4 hspm4 htrm4 hm4_19 hm4_21 hm4_23 hm4_24 hm4_25 hm4_27 hm4_28 hm4_fp hinv_m4)
      simp +zetaDelta only [bs2, bs1, encodeOptMessage, optEkSentCt1ReceivedPBPinnedAt]; sep_ac_rfl
  intro sm4 hpcm4 hrunm4 hspm4 htrm4 hx19_4 hx21_4 hx23_4 hx24_4 hx25_4 hx27_4 hx28_4 hfp_4 hinv_4
  cases sendingEk with
  | none =>
    simp only [Option.isSome_none, Bool.not_false] at hcap_enc_beq hcap_enc_bne
    dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
    apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 6216#64)
    wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv5
    have hpool5 : A.pool lim st sm4 = A.pool lim st _ := (A.pool_of_vmPreserved hinv5.2).symm
    refine SepWPp.weaken_pre (Entails.of_eq ?_)
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (hinv_4.trans hinv5.1))
    rw [encodeInnerState_ct1Received_eq, hpool5]
    simp +zetaDelta only [bs2, bs1, encodeOptMessage, List.append_nil, List.append_assoc]
  | some enc =>
    simp only [Option.isSome_some, Bool.not_true] at hcap_enc_beq hcap_enc_bne
    have hfit_enc :
        bs2.length + (encodeMessage PolynomialEncoder.encodeRaw 2#32 enc).length ≤ cap.toNat := by
      simp +zetaDelta only [bs2, bs1, encodeOptMessage, List.length_append, List.length_singleton] at hfit ⊢
      omega
    dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
    apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 11748#64)
    wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv5
    have hpool5 : A.pool lim st sm4 = A.pool lim st _ := (A.pool_of_vmPreserved hinv5.2).symm
    refine step_send_tail_11748_polyEnc_placed A lim st ext hpolyEnc
      (sp + 4944#64) sp cap ptr g.2 enc bs2 hfit_enc halign
      (F := optEkSentCt1ReceivedPBPinnedAt A.repAlloc g.1 (sp + 4840#64) uc ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hinv_4.trans hinv5.1)
      (by dsimp +zetaDelta only [optPolynomialEncoderPBPinnedAt, bs2, bs1]; rw [hpool5]; sep_ac_rfl) ?_
    intro sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp hinv_m5
    simp only [arm64_norm, hx19_4, hx21_4, hx23_4, hx27_4, hx28_4, hfp_4]
      at hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp
    refine SepWPp.weaken_pre (Entails.of_eq ?_)
      (hnext sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp hinv_m5)
    rw [encodeInnerState_ct1Received_eq]
    simp +zetaDelta only [bs2, bs1, encodeOptMessage,
      optPolynomialEncoderPBPinnedAt, List.append_assoc]; sep_ac_rfl

/-! ## 6. `StepSendInnerStateAt6616Placed` Bridges for the 4 Variants -/

theorem step_send_v1_ct1Sampled_at_6616_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (ext : String → Option (State → State))
    {roBase : BitVec 64} {s0 : State}
    (hct1SampledLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 486)
      (withStepInv s0 (chunkedCt1SampledEncodedLenPinnedSpec A.repAlloc)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hct1SentEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 459)
      (withStepInv s0 (etvCt1SentBudgetExactSpecOf resStack A lim)))
    (hpolyEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 456)
      (withStepInv s0 (etvPolyEncoderBudgetExactSpecOf resStack A lim)))
    (hpolyDec : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 455)
      (withStepInv s0 (etvPolyDecoderBudgetExactSpecOf resStack A lim)))
    (v : V1State.Chunked.Ct1Sampled) :
    StepSendInnerStateAt6616Placed resStack A lim st0 ext roBase s0 (.ct1Sampled v) := by
  intro sp cap ptr w25 g bs hv_len hfit halign ret s P F Q Qp oom
    hpc hrun hsp htr hx8 hx9 hx20 hx25 hinv0 hP hnext
  subst hP
  simp only [v1StateInnerPBPinnedAt, v1StateInnerCap] at hx8 hx20 ⊢
  refine sepWPp_extract_pure
    (((optCt1SentCap g.b.gCt1Sampled.uc v.uc ^^^ 0x8000000000000000#64).ult 11#64) = false)
    (fun R' hm => by
      dsimp only [chunkedCt1SampledPBPinnedAt] at hm
      rw [optCt1SentPBPinnedAt_eq A.repAlloc g.b.gCt1Sampled.uc (sp + 4832#64) v.uc] at hm
      have hm' : s.mem ⊨ optCt1SentRest A.repAlloc g.b.gCt1Sampled.uc (sp + 4832#64) v.uc ∗
          (((sp + 4832#64) ↦₆₄ optCt1SentCap g.b.gCt1Sampled.uc v.uc) ∗
           optPolynomialEncoderPBPinnedAt A.repAlloc g.b.gCt1Sampled.sendingCt1 (sp + 4832#64 + 128#64) v.sendingCt1 ∗
           optPolynomialDecoderPBPinnedAt A.repAlloc g.b.gCt1Sampled.receivingEk (sp + 4832#64 + 184#64) v.receivingEk ∗
           ((sp + 16#64) ↦₆₄ w25) ∗
           (roBase ↦ᵣ spqrSendEncodeJumpTableBytes) ∗ vecU8At A.repAlloc (sp + 1424#64) cap ptr bs ∗
           A.pool lim st0 s ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R') := by
        convert hm using 1; sep_ac_rfl
      exact (optCt1SentRest_disc_bounds hm').2.2)
    fun hult => ?_
  simp only [hult, Bool.false_eq_true, ↓reduceIte] at hx8
  rw [spqrSendEncodeJumpTableBytes_eq roBase]; dsimp only [spqrSendEncodeJumpTableBytesAt]
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
  apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 8480#64)
  wp_steps
  apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, wp_norm, *])
  intro hinv1
  have hpool1 : A.pool lim st0 s = A.pool lim st0 _ := (A.pool_of_vmPreserved hinv1.2).symm
  refine step_send_v1_ct1Sampled_placed hres A lim st0 ext
    hct1SampledLen hvarint hct1SentEnc hpolyEnc hpolyDec
    sp cap ptr g.b.gCt1Sampled v bs hv_len hfit halign
    (F := ((sp + 16#64) ↦₆₄ w25) ∗ spqrSendEncodeJumpTableBytesAt roBase ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1.1)
    (by dsimp only [spqrSendEncodeJumpTableBytesAt]; rw [hpool1]; sep_ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m
  simp only [arm64_norm, hx25] at hm19 hm21 hm23 hm25 hm27 hm28 hmfp
  refine SepWPp.weaken_pre ?_
    (hnext sm hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m)
  rw [spqrSendEncodeJumpTableBytes_eq roBase]
  exact Entails.of_eq (by sep_ac_rfl)

theorem step_send_v1_ekSentCt1Received_at_6616_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (ext : String → Option (State → State))
    {roBase : BitVec 64} {s0 : State}
    (hekLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 499)
      (withStepInv s0 (leafEncLen16Spec (ekSentCt1ReceivedPBPinnedAt A.repAlloc) ekSentCt1ReceivedPBEncodedLen)))
    (hpolyDecLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 493)
      (withStepInv s0 (leafEncLen16Spec (polynomialDecoderPBPinnedAt A.repAlloc) polynomialDecoderPBEncodedLen)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hekEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 458)
      (withStepInv s0 (etvEkSentCt1ReceivedBudgetExactSpecOf resStack A lim)))
    (hpolyDec : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 455)
      (withStepInv s0 (etvPolyDecoderBudgetExactSpecOf resStack A lim)))
    (v : V1State.Chunked.EkSentCt1Received) :
    StepSendInnerStateAt6616Placed resStack A lim st0 ext roBase s0 (.ekSentCt1Received v) := by
  intro sp cap ptr w25 g bs hv_len hfit halign ret s P F Q Qp oom
    hpc hrun hsp htr hx8 hx9 hx20 hx25 hinv0 hP hnext
  subst hP
  replace hx8 : s.readReg64 .x8 = 4#64 := hx8.trans (by rw [show v1StateInnerCap g (.ekSentCt1Received v) = 0x8000000000000004#64 from rfl]; decide +kernel)
  rw [spqrSendEncodeJumpTableBytes_eq roBase]; dsimp only [spqrSendEncodeJumpTableBytesAt]
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
  apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 7784#64)
  wp_steps
  apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, wp_norm, *])
  intro hinv1
  have hpool1 : A.pool lim st0 s = A.pool lim st0 _ := (A.pool_of_vmPreserved hinv1.2).symm
  have ⟨h4840, h4944⟩ : (sp + 4832#64) + 8#64 = sp + 4840#64 ∧
      (sp + 4832#64) + 112#64 = sp + 4944#64 := ⟨by bv_omega, by bv_omega⟩
  dsimp only [v1StateInnerPBPinnedAt]; rw [h4840, h4944]
  refine step_send_v1_ekSentCt1Received_placed hres A lim st0 ext
    hekLen hpolyDecLen hvarint hekEnc hpolyDec
    sp cap ptr w25 g.a.gEkSentCt1Received v bs hv_len hfit halign
    (F := ((sp + 4832#64) ↦₆₄ 0x8000000000000004#64) ∗ memRegion (sp + 4832#64 + 152#64) 72 ∗
      spqrSendEncodeJumpTableBytesAt roBase ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1.1)
    (by dsimp only [spqrSendEncodeJumpTableBytesAt]; rw [hpool1]; sep_ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m
  simp only [arm64_norm] at hm19 hm21 hm23 hm27 hm28 hmfp
  refine SepWPp.weaken_pre ?_
    (hnext sm hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m)
  dsimp only [v1StateInnerPBPinnedAt]; rw [h4840, h4944, spqrSendEncodeJumpTableBytes_eq roBase]
  exact Entails.of_eq (by sep_ac_rfl)

theorem step_send_v1_ct1Acknowledged_at_6616_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (ext : String → Option (State → State))
    {roBase : BitVec 64} {s0 : State}
    (hct1SentLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 487)
      (withStepInv s0 (leafEncLen16Spec (ct1SentPBPinnedAt A.repAlloc) ct1SentPBEncodedLen)))
    (hpolyDecLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 493)
      (withStepInv s0 (leafEncLen16Spec (polynomialDecoderPBPinnedAt A.repAlloc) polynomialDecoderPBEncodedLen)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hct1SentEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 459)
      (withStepInv s0 (etvCt1SentBudgetExactSpecOf resStack A lim)))
    (hpolyDec : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 455)
      (withStepInv s0 (etvPolyDecoderBudgetExactSpecOf resStack A lim)))
    (v : V1State.Chunked.Ct1Acknowledged) :
    StepSendInnerStateAt6616Placed resStack A lim st0 ext roBase s0 (.ct1Acknowledged v) := by
  intro sp cap ptr w25 g bs hv_len hfit halign ret s P F Q Qp oom
    hpc hrun hsp htr hx8 hx9 hx20 hx25 hinv0 hP hnext
  subst hP
  replace hx8 : s.readReg64 .x8 = 9#64 := hx8.trans (by rw [show v1StateInnerCap g (.ct1Acknowledged v) = 0x8000000000000009#64 from rfl]; decide +kernel)
  rw [spqrSendEncodeJumpTableBytes_eq roBase]; dsimp only [spqrSendEncodeJumpTableBytesAt]
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
  apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 7892#64)
  wp_steps
  apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, wp_norm, *])
  intro hinv1
  have hpool1 : A.pool lim st0 s = A.pool lim st0 _ := (A.pool_of_vmPreserved hinv1.2).symm
  have ⟨h4840, h4968⟩ : (sp + 4832#64) + 8#64 = sp + 4840#64 ∧
      (sp + 4832#64) + 136#64 = sp + 4968#64 := ⟨by bv_omega, by bv_omega⟩
  dsimp only [v1StateInnerPBPinnedAt]; rw [h4840, h4968]
  refine step_send_v1_ct1Acknowledged_placed hres A lim st0 ext
    hct1SentLen hpolyDecLen hvarint hct1SentEnc hpolyDec
    sp cap ptr w25 g.b.gCt1Acknowledged v bs hv_len hfit halign
    (F := ((sp + 4832#64) ↦₆₄ 0x8000000000000009#64) ∗ memRegion (sp + 4832#64 + 176#64) 48 ∗
      spqrSendEncodeJumpTableBytesAt roBase ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1.1)
    (by dsimp only [spqrSendEncodeJumpTableBytesAt]; rw [hpool1]; sep_ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m
  simp only [arm64_norm] at hm19 hm21 hm23 hm27 hm28 hmfp
  refine SepWPp.weaken_pre ?_
    (hnext sm hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m)
  dsimp only [v1StateInnerPBPinnedAt]; rw [h4840, h4968, spqrSendEncodeJumpTableBytes_eq roBase]
  exact Entails.of_eq (by sep_ac_rfl)

theorem step_send_v1_ct1Received_at_6616_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (ext : String → Option (State → State))
    {roBase : BitVec 64} {s0 : State}
    (hekLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 499)
      (withStepInv s0 (leafEncLen16Spec (ekSentCt1ReceivedPBPinnedAt A.repAlloc) ekSentCt1ReceivedPBEncodedLen)))
    (hpolyEncLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 480)
      (withStepInv s0 (leafEncLen16Spec (polynomialEncoderPBPinnedAt A.repAlloc) polynomialEncoderPBEncodedLen)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hekEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 458)
      (withStepInv s0 (etvEkSentCt1ReceivedBudgetExactSpecOf resStack A lim)))
    (hpolyEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 456)
      (withStepInv s0 (etvPolyEncoderBudgetExactSpecOf resStack A lim)))
    (v : V1State.Chunked.Ct1Received) :
    StepSendInnerStateAt6616Placed resStack A lim st0 ext roBase s0 (.ct1Received v) := by
  intro sp cap ptr w25 g bs hv_len hfit halign ret s P F Q Qp oom
    hpc hrun hsp htr hx8 hx9 hx20 hx25 hinv0 hP hnext
  subst hP
  replace hx8 : s.readReg64 .x8 = 3#64 := hx8.trans (by rw [show v1StateInnerCap g (.ct1Received v) = 0x8000000000000003#64 from rfl]; decide +kernel)
  rw [spqrSendEncodeJumpTableBytes_eq roBase]; dsimp only [spqrSendEncodeJumpTableBytesAt]
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
  apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 8372#64)
  wp_steps
  apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, wp_norm, *])
  intro hinv1
  have hpool1 : A.pool lim st0 s = A.pool lim st0 _ := (A.pool_of_vmPreserved hinv1.2).symm
  have ⟨h4840, h4944⟩ : (sp + 4832#64) + 8#64 = sp + 4840#64 ∧
      (sp + 4832#64) + 112#64 = sp + 4944#64 := ⟨by bv_omega, by bv_omega⟩
  dsimp only [v1StateInnerPBPinnedAt]; rw [h4840, h4944]
  refine step_send_v1_ct1Received_placed hres A lim st0 ext
    hekLen hpolyEncLen hvarint hekEnc hpolyEnc
    sp cap ptr w25 g.a.gCt1Received v bs hv_len hfit halign
    (F := ((sp + 4832#64) ↦₆₄ 0x8000000000000003#64) ∗ memRegion (sp + 4832#64 + 168#64) 56 ∗
      spqrSendEncodeJumpTableBytesAt roBase ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1.1)
    (by dsimp only [spqrSendEncodeJumpTableBytesAt]; rw [hpool1]; sep_ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m
  simp only [arm64_norm] at hm19 hm21 hm23 hm27 hm28 hmfp
  refine SepWPp.weaken_pre ?_
    (hnext sm hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m)
  dsimp only [v1StateInnerPBPinnedAt]; rw [h4840, h4944, spqrSendEncodeJumpTableBytes_eq roBase]
  exact Entails.of_eq (by sep_ac_rfl)

/-! ### `VecU8EncodeEnv` / `VmPreserved` Callee-Spec Corollaries -/

theorem step_send_v1_ct1Sampled_at_6616_vm_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (ext : String → Option (State → State))
    {roBase : BitVec 64} {s0 : State}
    (hct1SampledLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 486)
      (withStepInv s0 (chunkedCt1SampledEncodedLenPinnedSpec A.repAlloc)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hct1SentEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 459)
      (withStepInv s0 (etvCt1SentEncodeSpecOf resStack A lim)))
    (hpolyEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 456)
      (withStepInv s0 (etvPolyEncoderExactSpecOf resStack A.repAlloc)))
    (hpolyDec : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 455)
      (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A.repAlloc)))
    (v : V1State.Chunked.Ct1Sampled) :
    StepSendInnerStateAt6616Placed resStack A lim st0 ext roBase s0 (.ct1Sampled v) :=
  step_send_v1_ct1Sampled_at_6616_placed hres A lim st0 ext
    hct1SampledLen hvarint
    (etv_ct1SentEncode_of_vecEnv_spec hct1SentEnc)
    (etvPolyEncoderBudgetExact_of_vm hpolyEnc)
    (etvPolyDecoderBudgetExact_of_vm hpolyDec) v

theorem step_send_v1_ekSentCt1Received_at_6616_vm_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (ext : String → Option (State → State))
    {roBase : BitVec 64} {s0 : State}
    (hekLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 499)
      (withStepInv s0 (leafEncLen16Spec (ekSentCt1ReceivedPBPinnedAt A.repAlloc) ekSentCt1ReceivedPBEncodedLen)))
    (hpolyDecLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 493)
      (withStepInv s0 (leafEncLen16Spec (polynomialDecoderPBPinnedAt A.repAlloc) polynomialDecoderPBEncodedLen)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hekEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 458)
      (withStepInv s0 (etvEkSentCt1ReceivedEncodeSpecOf resStack A lim)))
    (hpolyDec : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 455)
      (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A.repAlloc)))
    (v : V1State.Chunked.EkSentCt1Received) :
    StepSendInnerStateAt6616Placed resStack A lim st0 ext roBase s0 (.ekSentCt1Received v) :=
  step_send_v1_ekSentCt1Received_at_6616_placed hres A lim st0 ext
    hekLen hpolyDecLen hvarint
    (etv_ekSentCt1ReceivedEncode_of_vecEnv_spec hekEnc)
    (etvPolyDecoderBudgetExact_of_vm hpolyDec) v

theorem step_send_v1_ct1Acknowledged_at_6616_vm_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (ext : String → Option (State → State))
    {roBase : BitVec 64} {s0 : State}
    (hct1SentLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 487)
      (withStepInv s0 (leafEncLen16Spec (ct1SentPBPinnedAt A.repAlloc) ct1SentPBEncodedLen)))
    (hpolyDecLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 493)
      (withStepInv s0 (leafEncLen16Spec (polynomialDecoderPBPinnedAt A.repAlloc) polynomialDecoderPBEncodedLen)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hct1SentEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 459)
      (withStepInv s0 (etvCt1SentEncodeSpecOf resStack A lim)))
    (hpolyDec : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 455)
      (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A.repAlloc)))
    (v : V1State.Chunked.Ct1Acknowledged) :
    StepSendInnerStateAt6616Placed resStack A lim st0 ext roBase s0 (.ct1Acknowledged v) :=
  step_send_v1_ct1Acknowledged_at_6616_placed hres A lim st0 ext
    hct1SentLen hpolyDecLen hvarint
    (etv_ct1SentEncode_of_vecEnv_spec hct1SentEnc)
    (etvPolyDecoderBudgetExact_of_vm hpolyDec) v

theorem step_send_v1_ct1Received_at_6616_vm_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (ext : String → Option (State → State))
    {roBase : BitVec 64} {s0 : State}
    (hekLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 499)
      (withStepInv s0 (leafEncLen16Spec (ekSentCt1ReceivedPBPinnedAt A.repAlloc) ekSentCt1ReceivedPBEncodedLen)))
    (hpolyEncLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 480)
      (withStepInv s0 (leafEncLen16Spec (polynomialEncoderPBPinnedAt A.repAlloc) polynomialEncoderPBEncodedLen)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hekEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 458)
      (withStepInv s0 (etvEkSentCt1ReceivedEncodeSpecOf resStack A lim)))
    (hpolyEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 456)
      (withStepInv s0 (etvPolyEncoderExactSpecOf resStack A.repAlloc)))
    (v : V1State.Chunked.Ct1Received) :
    StepSendInnerStateAt6616Placed resStack A lim st0 ext roBase s0 (.ct1Received v) :=
  step_send_v1_ct1Received_at_6616_placed hres A lim st0 ext
    hekLen hpolyEncLen hvarint
    (etv_ekSentCt1ReceivedEncode_of_vecEnv_spec hekEnc)
    (etvPolyEncoderBudgetExact_of_vm hpolyEnc) v

end LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerChunked1PlacedBudget

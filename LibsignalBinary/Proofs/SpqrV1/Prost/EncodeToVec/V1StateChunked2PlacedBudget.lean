/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked2PlacedBudgetAux
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked1
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked2
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked2Placed
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.ProtoReprCodeSym
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `[LibsignalPlacement]` Phase 2c (Part 2): `V1State::encode_raw` Variants `idx = 0, 2, 5` (`Block 426`)

Re-exports variants `idx = 0` (`.keysUnsampled`) and `idx = 2` (`.headerSent`) from
`V1StateChunked2PlacedBudgetAux` and proves `step_encodeToVec_v1_noHeaderReceived_placed` (`idx = 5`),
threading `A.pool lim st`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked2PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.RustHeap (RustAlloc vecU8At)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalSpqrV1
  (PolynomialDecoder ProtoAuthenticator V1State)
open CryptoVerification.LibsignalSpqrV1.Proto
  (encodeMessage encodeOptMessage encodeUint64Field encodeVarint)
open CryptoVerification.SpqrV1.ProtoRepr
  (PolynomialDecoderPBGhost Unchunked2PBGhost
   noHeaderReceivedPBEncodedLen noHeaderReceivedPBPinnedAt
   noneCap2 optAuthCap optAuthenticatorPBPinnedAt
   optNoHeaderReceivedPBFieldEncodedLen optNoHeaderReceivedPBPinnedAt
   optPolynomialDecoderPBFieldEncodedLen optPolynomialDecoderPBPinnedAt
   polynomialDecoderPBEncodedLen polynomialDecoderPBPinnedAt
   unchunked2PinnedAt v1StateInnerPayloadEncodedLen v1StatePBEncodedLen varintLen)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (adds_no_overflow_of_eq cmp_ls_false_of_lt
   hwVarintLen_bvShift_eq_ofNat_varintLen_norm hwVarintLen_eq_ofNat_varintLen_norm
   noneCap_add_one_beq_zero noneCap_add_one_bne_zero
   ofNat_countLeadingZeros_32 ofNat_countLeadingZeros_64
   ule_self_64 ule_zero_64 ult_self_64 ult_zero_64
   zeroExtend64_beq_zero32 zext64_truncate32)
open CryptoVerification.SpqrV1.Prost.EncodeToVec
  (StepInv blkPC_426 blkPl_426 bv_optPolyDec_some_eq
   cap_beq_len_false_of_lt encodeToVecCalleeStackOf encodeVarint_length_pos
   etv2_bv_optNoHeaderReceived_some_eq etv2_encodeInnerState_noHeaderReceived_eq
   etv2_encodeOptNoHeaderReceived_some_eq etv2_encodeUint64Field_1_eq etv2_optAuth_cap_bounds
   noneCap2_add_two_beq_zero noneCap2_add_two_bne_zero
   noneCap3 noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
   noneCap_add_two_beq_zero noneCap_add_two_bne_zero
   optNoHeaderReceivedCap optNoHeaderReceivedPBPinnedAt_cap_bounds optNoHeaderReceivedPBPinnedAt_eq
   optPolyDecCap optPolynomialDecoderPBPinnedAt_cap_bounds optPolynomialDecoderPBPinnedAt_eq
   ult_of_lt_of_fit vecU8At_expose_one vecU8At_pack_one withStepInv)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsPlacedBudget
  (sepWP_done_tpidr sepWP_done_vm sepWPp_of_sepWP_cs_vm)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhaseBudget
  (authEncodeExactSpecOf encodeVarintExactSpecOf
   step_etv_encode_auth_call_prog step_etv_encode_varint_call_prog)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonBudget
  (leafEncLen16Spec)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonPlacedBudget
  (etvPolyDecoderBudgetExactSpecOf step_etv_leaf_encLen16_call_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked1PlacedBudgetAux
  (sepWPp_extract_pure sepWPp_extract_vecU8At_bounds step_encodeToVec_tail_4456_polyDec2_placed)

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

/-! ## 1. Re-Exports from `V1StateChunked2PlacedBudgetAux` -/

abbrev step_encodeToVec_v1_keysUnsampled_placed :=
  @V1StateChunked2PlacedBudgetAux.step_encodeToVec_v1_keysUnsampled_placed

abbrev etv2_step_memcpy_slice_placed :=
  @V1StateChunked2PlacedBudgetAux.etv2_step_memcpy_slice_placed

abbrev etv2_step_headerSent_uc_placed :=
  @V1StateChunked2PlacedBudgetAux.etv2_step_headerSent_uc_placed

abbrev step_encodeToVec_v1_headerSent_placed :=
  @V1StateChunked2PlacedBudgetAux.step_encodeToVec_v1_headerSent_placed

/-! ## 2. Variant `idx = 5`: `.noHeaderReceived` (`+2848 .. +4472`) -/

theorem step_encodeToVec_v1_noHeaderReceived_placed [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (H : String → Option (State → State)) {s0 s : State}
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
    (a sp cap ptr : BitVec 64) (g : PolynomialDecoderPBGhost × Unchunked2PBGhost)
    (v : V1State.Chunked.NoHeaderReceived) (bs : List (BitVec 8))
    (hv_len : v1StatePBEncodedLen ⟨some (.noHeaderReceived v)⟩ < 2 ^ 64)
    (hfit : bs.length + (V1State.InnerState.encode (.noHeaderReceived v)).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_426).base + 2848#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = a) (hinv0 : StepInv s0 s)
    (hP : P = ((optPolynomialDecoderPBPinnedAt A.repAlloc g.1 (a + 136#64) v.receivingHdr ∗
      optNoHeaderReceivedPBPinnedAt A.repAlloc g.2 (a + 176#64) v.uc) ∗
      vecU8At A.repAlloc (sp - 120#64) cap ptr bs ∗ A.pool lim st s ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_426).base + 1808#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm
        (((optPolynomialDecoderPBPinnedAt A.repAlloc g.1 (a + 136#64) v.receivingHdr ∗
          optNoHeaderReceivedPBPinnedAt A.repAlloc g.2 (a + 176#64) v.uc) ∗
          vecU8At A.repAlloc (sp - 120#64) cap ptr (bs ++ V1State.InnerState.encode (.noHeaderReceived v)) ∗
          A.pool lim st sm ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q Qp oom := by
  subst hP
  rcases v with ⟨uc, receivingHdr⟩
  rw [etv2_encodeInnerState_noHeaderReceived_eq] at hfit
  simp only [List.length_append, List.length_singleton] at hfit
  have hsub_len : v1StateInnerPayloadEncodedLen (.noHeaderReceived ⟨uc, receivingHdr⟩) < 2 ^ 64 := by
    dsimp only [v1StatePBEncodedLen] at hv_len; omega
  have hlt1 : bs.length < cap.toNat := by omega
  have hfit_var : (bs ++ [0x32#8]).length +
      (encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.noHeaderReceived ⟨uc, receivingHdr⟩)))).length ≤
      cap.toNat := by
    simp only [List.length_append, List.length_singleton]; omega
  refine sepWPp_extract_vecU8At_bounds (v := sp - 120#64) (cap := cap) (ptr := ptr) (bs := bs)
    (F := optPolynomialDecoderPBPinnedAt A.repAlloc g.1 (a + 136#64) receivingHdr ∗
      optNoHeaderReceivedPBPinnedAt A.repAlloc g.2 (a + 176#64) uc ∗ A.pool lim st s ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F)
    (by sep_ac_rfl) fun _ hcap hptr => ?_
  refine sepWPp_extract_pure
    (((optNoHeaderReceivedCap g.2 uc + 2#64 == 0#64) = !uc.isSome ∧
      (optNoHeaderReceivedCap g.2 uc + 2#64 != 0#64) = uc.isSome) ∧
     ((optPolyDecCap g.1 receivingHdr + 1#64 == 0#64) = !receivingHdr.isSome ∧
      (optPolyDecCap g.1 receivingHdr + 1#64 != 0#64) = receivingHdr.isSome))
    (fun R' hm =>
      ⟨optNoHeaderReceivedPBPinnedAt_cap_bounds (p := a + 176#64)
        (R := optPolynomialDecoderPBPinnedAt A.repAlloc g.1 (a + 136#64) receivingHdr ∗
          vecU8At A.repAlloc (sp - 120#64) cap ptr bs ∗ A.pool lim st s ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm),
       optPolynomialDecoderPBPinnedAt_cap_bounds (p := a + 136#64)
        (R := optNoHeaderReceivedPBPinnedAt A.repAlloc g.2 (a + 176#64) uc ∗
          vecU8At A.repAlloc (sp - 120#64) cap ptr bs ∗ A.pool lim st s ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm)⟩)
    fun ⟨⟨hcap_uc_beq, hcap_uc_bne⟩, ⟨hcap_dec_beq, hcap_dec_bne⟩⟩ => ?_
  have hbeq_false := cap_beq_len_false_of_lt hlt1 hcap
  have ⟨h112, h104⟩ : (sp - 120#64) + 8#64 = sp - 112#64 ∧ (sp - 120#64) + 16#64 = sp - 104#64 :=
    ⟨by bv_omega, by bv_omega⟩
  have hpack := vecU8At_pack_one A.repAlloc (sp - 120#64) cap ptr bs 0x32#8 hlt1 hcap hptr
  rw [h112, h104] at hpack
  suffices h3400 : ∀ sm1 : State,
      sm1.pc = (blkPl_426).base + 3400#64 → sm1.status = .Running → sm1.sp = sp - 144#64 → sm1.trace = s0.trace →
      sm1.readReg64 .x19 = optNoHeaderReceivedCap g.2 uc → sm1.readReg64 .x20 = a → sm1.readReg64 .x21 = a + 176#64 →
      sm1.readReg64 .x23 = BitVec.ofNat 64 (optNoHeaderReceivedPBFieldEncodedLen uc) →
      sm1.readReg64 .x27 = s.readReg64 .x27 → sm1.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm1 →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm1
        (((optPolynomialDecoderPBPinnedAt A.repAlloc g.1 (a + 136#64) receivingHdr ∗
          optNoHeaderReceivedPBPinnedAt A.repAlloc g.2 (a + 176#64) uc) ∗
          vecU8At A.repAlloc (sp - 120#64) cap ptr (bs ++ [0x32#8]) ∗ A.pool lim st sm1 ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom by
    rw [vecU8At_expose_one A.repAlloc (sp - 120#64) cap ptr bs hlt1 hcap hptr, h112, h104]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun b0 => ?_
    cases uc with
    | none =>
      rw [optNoHeaderReceivedPBPinnedAt_eq A.repAlloc g.2 (a + 176#64) none]
      simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
      apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 3400#64)
      by_vm_steps
        wp_steps
        apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv1
        have hpool1 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv1.2).symm
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (h3400 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *])
            (by simp only [optNoHeaderReceivedPBFieldEncodedLen, arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1.1))
        rw [← optNoHeaderReceivedPBPinnedAt_eq A.repAlloc g.2 (a + 176#64) none, ← hpack, hpool1]
    | some u =>
      rw [optNoHeaderReceivedPBPinnedAt_eq A.repAlloc g.2 (a + 176#64) (some u)]
      simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      have ⟨hu_fit, hopt_u_lt⟩ :
          noHeaderReceivedPBEncodedLen u < 2 ^ 64 ∧ optNoHeaderReceivedPBFieldEncodedLen (some u) < 2 ^ 64 :=
        ⟨by dsimp only [v1StateInnerPayloadEncodedLen, optNoHeaderReceivedPBFieldEncodedLen] at hsub_len; omega,
         by dsimp only [v1StateInnerPayloadEncodedLen] at hsub_len; omega⟩
      have hvar_u_lt : varintLen (BitVec.ofNat 64 (noHeaderReceivedPBEncodedLen u)) <
          optNoHeaderReceivedPBFieldEncodedLen (some u) := by
        dsimp only [optNoHeaderReceivedPBFieldEncodedLen]; omega
      have ⟨⟨hu1, hu2, hu3, hu4, hu5⟩, hult_u, hopt_u_eq⟩ :=
        (⟨cmp_ls_false_of_lt hvar_u_lt hopt_u_lt, ult_of_lt_of_fit hvar_u_lt hopt_u_lt,
          etv2_bv_optNoHeaderReceived_some_eq u⟩ : _ ∧ _ ∧ _)
      apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 424)
      by_vm_steps
        wp_steps
        apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv1
        rw [← optNoHeaderReceivedPBPinnedAt_eq A.repAlloc g.2 (a + 176#64) (some u)]
        refine step_etv_leaf_encLen16_call_placed hres (noHeaderReceivedPBPinnedAt A.repAlloc)
          noHeaderReceivedPBEncodedLen hnhrLen
          (a + 176#64) sp ((blkPl_426).base + 3360#64) g.2 u hu_fit
          (F := optPolynomialDecoderPBPinnedAt A.repAlloc g.1 (a + 136#64) receivingHdr ∗
            vecU8At A.repAlloc (sp - 120#64) cap ptr (bs ++ [0x32#8]) ∗ A.pool lim st s ∗ F)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
          (hinv0.trans hinv1.1)
          (by rw [← hpack]; dsimp only [optNoHeaderReceivedPBPinnedAt]; sep_ac_rfl) ?_
        intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1 hcsm1 hinv_m1 hvm_m1
        rcases hcsm1 with ⟨hm19, hm20, hm21, _, _, _, _, _, hm27, _, hmfp, _⟩
        simp only [arm64_norm, hx20] at hm19 hm20 hm21 hm27 hmfp
        apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 3400#64)
        wp_steps
        apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv2
        have hpool12 := (A.pool_of_vmPreserved (lim := lim) (st := st) (hinv1.2.trans (hvm_m1.trans hinv2.2))).symm
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (h3400 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m1.trans hinv2.1))
        rw [hpool12]; dsimp only [optNoHeaderReceivedPBPinnedAt]; sep_ac_rfl
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx19_1 hx20_1 hx21_1 hx23_1 hx27_1 hfp_1 hinv_1
  suffices h4012 : ∀ sm2 : State,
      sm2.pc = (blkPl_426).base + 4012#64 → sm2.status = .Running → sm2.sp = sp - 144#64 → sm2.trace = s0.trace →
      sm2.readReg64 .x8 = BitVec.ofNat 64 (optPolynomialDecoderPBFieldEncodedLen receivingHdr) →
      sm2.readReg64 .x19 = optNoHeaderReceivedCap g.2 uc → sm2.readReg64 .x20 = a → sm2.readReg64 .x21 = a + 176#64 →
      sm2.readReg64 .x22 = optPolyDecCap g.1 receivingHdr →
      sm2.readReg64 .x23 = BitVec.ofNat 64 (optNoHeaderReceivedPBFieldEncodedLen uc) →
      sm2.readReg64 .x27 = s.readReg64 .x27 → sm2.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm2 →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm2
        (((optPolynomialDecoderPBPinnedAt A.repAlloc g.1 (a + 136#64) receivingHdr ∗
          optNoHeaderReceivedPBPinnedAt A.repAlloc g.2 (a + 176#64) uc) ∗
          vecU8At A.repAlloc (sp - 120#64) cap ptr (bs ++ [0x32#8]) ∗ A.pool lim st sm2 ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom by
    cases receivingHdr with
    | none =>
      rw [optPolynomialDecoderPBPinnedAt_eq A.repAlloc g.1 (a + 136#64) none]
      simp only [Option.isSome_none, Bool.not_false] at hcap_dec_beq hcap_dec_bne
      apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 4012#64)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv2
      have hpool2 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv2.2).symm
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h4012 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [optPolynomialDecoderPBFieldEncodedLen, arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (hinv_1.trans hinv2.1))
      rw [← optPolynomialDecoderPBPinnedAt_eq A.repAlloc g.1 (a + 136#64) none, hpool2]
    | some dec =>
      rw [optPolynomialDecoderPBPinnedAt_eq A.repAlloc g.1 (a + 136#64) (some dec)]
      simp only [Option.isSome_some, Bool.not_true] at hcap_dec_beq hcap_dec_bne
      have ⟨hdec_fit, hopt_d_lt⟩ :
          polynomialDecoderPBEncodedLen dec < 2 ^ 64 ∧ optPolynomialDecoderPBFieldEncodedLen (some dec) < 2 ^ 64 :=
        ⟨by dsimp only [v1StateInnerPayloadEncodedLen, optPolynomialDecoderPBFieldEncodedLen] at hsub_len; omega,
         by dsimp only [v1StateInnerPayloadEncodedLen] at hsub_len; omega⟩
      have hvar_d_lt : varintLen (BitVec.ofNat 64 (polynomialDecoderPBEncodedLen dec)) <
          optPolynomialDecoderPBFieldEncodedLen (some dec) := by
        dsimp only [optPolynomialDecoderPBFieldEncodedLen]; omega
      have ⟨⟨hd1, hd2, hd3, hd4, hd5⟩, hult_d, hopt_d_eq⟩ :=
        (⟨cmp_ls_false_of_lt hvar_d_lt hopt_d_lt, ult_of_lt_of_fit hvar_d_lt hopt_d_lt,
          bv_optPolyDec_some_eq dec⟩ : _ ∧ _ ∧ _)
      apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 413)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv2
      rw [← optPolynomialDecoderPBPinnedAt_eq A.repAlloc g.1 (a + 136#64) (some dec)]
      refine step_etv_leaf_encLen16_call_placed hres (polynomialDecoderPBPinnedAt A.repAlloc)
        polynomialDecoderPBEncodedLen hpolyDecLen
        (a + 136#64) sp ((blkPl_426).base + 3420#64) g.1 dec hdec_fit
        (F := optNoHeaderReceivedPBPinnedAt A.repAlloc g.2 (a + 176#64) uc ∗
          vecU8At A.repAlloc (sp - 120#64) cap ptr (bs ++ [0x32#8]) ∗ A.pool lim st sm1 ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (hinv_1.trans hinv2.1)
        (by dsimp only [optPolynomialDecoderPBPinnedAt]; sep_ac_rfl) ?_
      intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx0m2 hcsm2 hinv_m2 hvm_m2
      rcases hcsm2 with ⟨hm2_19, hm2_20, hm2_21, hm2_22, hm2_23, _, _, _, hm2_27, _, hm2_fp, _⟩
      simp only [arm64_norm, hx19_1, hx20_1, hx21_1, hx23_1, hx27_1, hfp_1]
        at hm2_19 hm2_20 hm2_21 hm2_22 hm2_23 hm2_27 hm2_fp
      apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 4012#64)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv3
      have hpool23 := (A.pool_of_vmPreserved (lim := lim) (st := st) (hinv2.2.trans (hvm_m2.trans hinv3.2))).symm
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h4012 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m2.trans hinv3.1))
      rw [hpool23]; dsimp only [optPolynomialDecoderPBPinnedAt]; sep_ac_rfl
  intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx8_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx27_2 hfp_2 hinv_2
  have ⟨hadd_sum, hult_sum, hule_sum, hult_sum2, hule_sum2⟩ := adds_no_overflow_of_eq
      (a := optPolynomialDecoderPBFieldEncodedLen receivingHdr)
      (b := optNoHeaderReceivedPBFieldEncodedLen uc)
      (c := v1StateInnerPayloadEncodedLen (.noHeaderReceived ⟨uc, receivingHdr⟩)) rfl hsub_len
  apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 292)
  wp_steps
  apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, wp_norm, *])
  intro hinv3
  have hpool3 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv3.2).symm
  set bs1 := (bs ++ [0x32#8]) ++
    encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.noHeaderReceived ⟨uc, receivingHdr⟩)))
  refine step_etv_encode_varint_call_prog A lim st hvarint
    (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.noHeaderReceived ⟨uc, receivingHdr⟩)))
    (sp - 120#64) cap ptr sp ((blkPl_426).base + 4028#64) (bs ++ [0x32#8]) hfit_var
    (F := (optPolynomialDecoderPBPinnedAt A.repAlloc g.1 (a + 136#64) receivingHdr ∗
      optNoHeaderReceivedPBPinnedAt A.repAlloc g.2 (a + 176#64) uc) ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hinv_2.trans hinv3.1) (by rw [hpool3]; sep_ac_rfl) ?_
  intro sm3 hpcm3 hrunm3 hspm3 htrm3 hcsm3 hinv_m3
  rcases hcsm3 with ⟨hm3_19, hm3_20, hm3_21, hm3_22, _, _, _, _, hm3_27, _, hm3_fp, _⟩
  simp only [arm64_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx27_2, hfp_2]
    at hm3_19 hm3_20 hm3_21 hm3_22 hm3_27 hm3_fp
  set bs2 := bs1 ++ encodeOptMessage V1State.Unchunked.NoHeaderReceived.encodeRaw 1#32 uc
  suffices h4160 : ∀ sm4 : State,
      sm4.pc = (blkPl_426).base + 4160#64 → sm4.status = .Running → sm4.sp = sp - 144#64 → sm4.trace = s0.trace →
      sm4.readReg64 .x20 = a → sm4.readReg64 .x22 = optPolyDecCap g.1 receivingHdr →
      sm4.readReg64 .x27 = s.readReg64 .x27 → sm4.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm4 →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm4
        (((optPolynomialDecoderPBPinnedAt A.repAlloc g.1 (a + 136#64) receivingHdr ∗
          optNoHeaderReceivedPBPinnedAt A.repAlloc g.2 (a + 176#64) uc) ∗
          vecU8At A.repAlloc (sp - 120#64) cap ptr bs2 ∗ A.pool lim st sm4 ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom by
    cases uc with
    | none =>
      simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
      apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 4160#64)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv4
      have hpool4 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv4.2).symm
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h4160 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m3.trans hinv4.1))
      rw [hpool4]; simp +zetaDelta only [bs2, bs1, encodeOptMessage, List.append_nil]; sep_ac_rfl
    | some u =>
      simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      rw [etv2_encodeOptNoHeaderReceived_some_eq] at hfit
      simp only [List.length_append, List.length_singleton] at hfit
      have hu_lt : noHeaderReceivedPBEncodedLen u < 2 ^ 64 := by
        dsimp only [v1StateInnerPayloadEncodedLen, optNoHeaderReceivedPBFieldEncodedLen] at hsub_len; omega
      have hlt_tag : bs1.length < cap.toNat := by
        dsimp only [bs1]; simp only [List.length_append, List.length_singleton]; omega
      have hbeq_tag := cap_beq_len_false_of_lt hlt_tag hcap
      rw [vecU8At_expose_one A.repAlloc (sp - 120#64) cap ptr bs1 hlt_tag hcap hptr, h112, h104]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPp.exists_elim fun b1 => ?_
      apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 424)
      by_vm_steps
        wp_steps
        apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv4
        have hpack_tag := vecU8At_pack_one A.repAlloc (sp - 120#64) cap ptr bs1 0x0a#8 hlt_tag hcap hptr
        rw [h112, h104] at hpack_tag
        refine step_etv_leaf_encLen16_call_placed hres (noHeaderReceivedPBPinnedAt A.repAlloc)
          noHeaderReceivedPBEncodedLen hnhrLen
          (a + 176#64) sp ((blkPl_426).base + 4080#64) g.2 u hu_lt
          (F := optPolynomialDecoderPBPinnedAt A.repAlloc g.1 (a + 136#64) receivingHdr ∗
            vecU8At A.repAlloc (sp - 120#64) cap ptr (bs1 ++ [0x0a#8]) ∗ A.pool lim st sm3 ∗ F)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
          (hinv_m3.trans hinv4.1)
          (by rw [← hpack_tag]; dsimp +zetaDelta only [bs1, optNoHeaderReceivedPBPinnedAt]; sep_ac_rfl) ?_
        intro sm4 hpcm4 hrunm4 hspm4 htrm4 hx0m4 hcsm4 hinv_m4 hvm_m4
        rcases hcsm4 with ⟨hm4_19, hm4_20, hm4_21, hm4_22, _, _, _, _, hm4_27, _, hm4_fp, _⟩
        simp only [arm64_norm, hm3_19, hm3_20, hm3_21, hm3_22, hm3_27, hm3_fp]
          at hm4_19 hm4_20 hm4_21 hm4_22 hm4_27 hm4_fp
        apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 292)
        wp_steps
        apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv5
        set bs_u1 := (bs1 ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 (noHeaderReceivedPBEncodedLen u))
        have hfit_uvar : (bs1 ++ [0x0a#8]).length +
            (encodeVarint (BitVec.ofNat 64 (noHeaderReceivedPBEncodedLen u))).length ≤ cap.toNat := by
          dsimp only [bs1]; simp only [List.length_append, List.length_singleton]; omega
        refine step_etv_encode_varint_call_prog A lim st hvarint
          (BitVec.ofNat 64 (noHeaderReceivedPBEncodedLen u))
          (sp - 120#64) cap ptr sp ((blkPl_426).base + 4088#64) (bs1 ++ [0x0a#8]) hfit_uvar
          (F := optPolynomialDecoderPBPinnedAt A.repAlloc g.1 (a + 136#64) receivingHdr ∗
            noHeaderReceivedPBPinnedAt A.repAlloc g.2 (a + 176#64) u ∗ F)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hinv_m4.trans hinv5.1)
          (by rw [A.pool_of_vmPreserved (lim := lim) (st := st) (hinv4.2.trans (hvm_m4.trans hinv5.2))]; dsimp +zetaDelta only [bs1]; sep_ac_rfl) ?_
        intro sm5 hpcm5 hrunm5 hspm5 htrm5 hcsm5 hinv_m5
        rcases hcsm5 with ⟨hm5_19, hm5_20, hm5_21, hm5_22, _, _, _, _, hm5_27, _, hm5_fp, _⟩
        simp only [arm64_norm, hm4_19, hm4_20, hm4_21, hm4_22, hm4_27, hm4_fp]
          at hm5_19 hm5_20 hm5_21 hm5_22 hm5_27 hm5_fp
        dsimp only [noHeaderReceivedPBPinnedAt, unchunked2PinnedAt]
        have h176_48 : (a + 176#64) + 0x30#64 = a + 224#64 := by bv_omega
        rw [h176_48]
        refine sepWPp_extract_pure
          ((optAuthCap g.2 u.auth + 1#64 == 0#64) = !u.auth.isSome ∧
           (optAuthCap g.2 u.auth + 1#64 != 0#64) = u.auth.isSome)
          (fun R' hm => etv2_optAuth_cap_bounds (A := A.repAlloc) (p := a + 176#64)
            (R := optPolynomialDecoderPBPinnedAt A.repAlloc g.1 (a + 136#64) receivingHdr ∗
              ((a + 224#64) ↦₆₄ u.epoch) ∗ vecU8At A.repAlloc (sp - 120#64) cap ptr bs_u1 ∗ A.pool lim st sm5 ∗
              stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
            (Satisfies.mono (Entails.of_eq (by dsimp +zetaDelta only [bs_u1, bs1]; sep_ac_rfl)) hm))
          fun ⟨hcap_auth_beq, hcap_auth_bne⟩ => ?_
        set bs_u2 := bs_u1 ++ encodeUint64Field 1#32 u.epoch
        suffices h4140 : ∀ sm6 : State,
            sm6.pc = (blkPl_426).base + 4140#64 → sm6.status = .Running → sm6.sp = sp - 144#64 → sm6.trace = s0.trace →
            sm6.readReg64 .x19 = optNoHeaderReceivedCap g.2 (some u) → sm6.readReg64 .x20 = a →
            sm6.readReg64 .x21 = a + 176#64 → sm6.readReg64 .x22 = optPolyDecCap g.1 receivingHdr →
            sm6.readReg64 .x27 = s.readReg64 .x27 → sm6.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm6 →
            SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm6
              (((optPolynomialDecoderPBPinnedAt A.repAlloc g.1 (a + 136#64) receivingHdr ∗
                optAuthenticatorPBPinnedAt A.repAlloc g.2 (a + 176#64) u.auth ∗ ((a + 224#64) ↦₆₄ u.epoch)) ∗
                vecU8At A.repAlloc (sp - 120#64) cap ptr bs_u2 ∗ A.pool lim st sm6 ∗
                stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
              Q Qp oom by
          cases hep : u.epoch == 0#64
          · have hfit_ep : bs_u1.length + 1 + (encodeVarint u.epoch).length ≤ cap.toNat := by
              rw [etv2_encodeUint64Field_1_eq, hep] at hfit; dsimp only [bs_u1, bs1]
              simp only [Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_singleton] at hfit ⊢; omega
            have hlt_ep : bs_u1.length < cap.toNat := by have := encodeVarint_length_pos u.epoch; omega
            have hbeq_ep := cap_beq_len_false_of_lt hlt_ep hcap
            rw [vecU8At_expose_one A.repAlloc (sp - 120#64) cap ptr bs_u1 hlt_ep hcap hptr, h112, h104]
            simp only [sepExists_sepConj_left, sepExists_sepConj_right]
            refine SepWPp.exists_elim fun b2 => ?_
            apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 292)
            by_vm_steps
              wp_steps
              apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, wp_norm, *])
              intro hinv6
              have hpool6 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv6.2).symm
              have hpack_ep := vecU8At_pack_one A.repAlloc (sp - 120#64) cap ptr bs_u1 0x08#8 hlt_ep hcap hptr
              rw [h112, h104] at hpack_ep
              refine step_etv_encode_varint_call_prog A lim st hvarint
                u.epoch (sp - 120#64) cap ptr sp ((blkPl_426).base + 4140#64) (bs_u1 ++ [0x08#8])
                (by simpa only [List.length_append, List.length_singleton] using hfit_ep)
                (F := (optPolynomialDecoderPBPinnedAt A.repAlloc g.1 (a + 136#64) receivingHdr ∗
                  optAuthenticatorPBPinnedAt A.repAlloc g.2 (a + 176#64) u.auth ∗
                  ((a + 224#64) ↦₆₄ u.epoch)) ∗ F)
                (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (hinv_m5.trans hinv6.1) (by rw [← hpack_ep, hpool6]; sep_ac_rfl) ?_
              intro sm6 hpcm6 hrunm6 hspm6 htrm6 hcsm6 hinv_m6
              rcases hcsm6 with ⟨hm6_19, hm6_20, hm6_21, hm6_22, _, _, _, _, hm6_27, _, hm6_fp, _⟩
              simp only [arm64_norm, hm5_19, hm5_20, hm5_21, hm5_22, hm5_27, hm5_fp]
                at hm6_19 hm6_20 hm6_21 hm6_22 hm6_27 hm6_fp
              refine SepWPp.weaken_pre (Entails.of_eq ?_)
                (h4140 sm6 hpcm6 hrunm6 hspm6 htrm6 hm6_19 hm6_20 hm6_21 hm6_22 hm6_27 hm6_fp hinv_m6)
              simp +zetaDelta only [bs_u2, bs_u1, bs1, etv2_encodeUint64Field_1_eq, hep, Bool.false_eq_true, ↓reduceIte,
                List.append_assoc]; sep_ac_rfl
          · apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 4140#64)
            wp_steps
            apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, wp_norm, *])
            intro hinv6
            have hpool6 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv6.2).symm
            refine SepWPp.weaken_pre (Entails.of_eq ?_)
              (h4140 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m5.trans hinv6.1))
            rw [hpool6]
            simp +zetaDelta only [bs_u2, bs_u1, bs1, etv2_encodeUint64Field_1_eq, hep, ↓reduceIte, List.append_nil]; sep_ac_rfl
        intro sm6 hpcm6 hrunm6 hspm6 htrm6 hx19_6 hx20_6 hx21_6 hx22_6 hx27_6 hfp_6 hinv_6
        have hx19_eq : optNoHeaderReceivedCap g.2 (some u) = optAuthCap g.2 u.auth := rfl
        rw [hx19_eq] at hx19_6
        cases hauth : u.auth with
        | none =>
          simp only [hauth, Option.isSome_none, Bool.not_false] at hcap_auth_beq hcap_auth_bne
          apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 4160#64)
          wp_steps
          apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, wp_norm, *])
          intro hinv7
          have hpool7 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv7.2).symm
          refine SepWPp.weaken_pre (Entails.of_eq ?_)
            (h4160 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_6.trans hinv7.1))
          dsimp only [bs2]; rw [etv2_encodeOptNoHeaderReceived_some_eq, hpool7]
          simp +zetaDelta only [bs_u2, bs_u1, bs1, hauth, encodeOptMessage,
            optNoHeaderReceivedPBPinnedAt, noHeaderReceivedPBPinnedAt, unchunked2PinnedAt, h176_48,
            List.append_nil, List.append_assoc]
        | some auth =>
          simp only [hauth, Option.isSome_some, Bool.not_true] at hcap_auth_beq hcap_auth_bne
          have hfit_auth : bs_u2.length + (encodeMessage ProtoAuthenticator.encodeRaw 2#32 auth).length ≤ cap.toNat := by
            rw [hauth] at hfit; dsimp only [bs_u2, bs_u1, bs1, encodeOptMessage] at hfit ⊢
            simp only [List.length_append, List.length_singleton] at hfit ⊢; omega
          apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 314)
          wp_steps
          apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, wp_norm, *])
          intro hinv7
          have hpool7 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv7.2).symm
          refine step_etv_encode_auth_call_prog A lim st hauthEnc
            (a + 176#64) (sp - 120#64) cap ptr sp ((blkPl_426).base + 4160#64) g.2 auth bs_u2 hfit_auth
            (F := (optPolynomialDecoderPBPinnedAt A.repAlloc g.1 (a + 136#64) receivingHdr ∗
              ((a + 224#64) ↦₆₄ u.epoch)) ∗ F)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hinv_6.trans hinv7.1)
            (by rw [hpool7]; simp +zetaDelta only [bs_u2, bs_u1, bs1, hauth, optAuthenticatorPBPinnedAt]; sep_ac_rfl) ?_
          intro sm7 hpcm7 hrunm7 hspm7 htrm7 hcsm7 hinv_m7
          rcases hcsm7 with ⟨_, hm7_20, _, hm7_22, _, _, _, _, hm7_27, _, hm7_fp, _⟩
          simp only [arm64_norm, hx20_6, hx22_6, hx27_6, hfp_6] at hm7_20 hm7_22 hm7_27 hm7_fp
          refine SepWPp.weaken_pre (Entails.of_eq ?_)
            (h4160 sm7 hpcm7 hrunm7 hspm7 htrm7 hm7_20 hm7_22 hm7_27 hm7_fp hinv_m7)
          dsimp only [bs2]; rw [etv2_encodeOptNoHeaderReceived_some_eq]
          simp +zetaDelta only [bs_u2, bs_u1, bs1, hauth, encodeOptMessage,
            optNoHeaderReceivedPBPinnedAt, noHeaderReceivedPBPinnedAt, unchunked2PinnedAt,
            optAuthenticatorPBPinnedAt, h176_48, List.append_assoc]; sep_ac_rfl
  intro sm4 hpcm4 hrunm4 hspm4 htrm4 hx20_4 hx22_4 hx27_4 hfp_4 hinv_4
  cases receivingHdr with
  | none =>
    simp only [Option.isSome_none, Bool.not_false] at hcap_dec_beq hcap_dec_bne
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
    rw [etv2_encodeInnerState_noHeaderReceived_eq, hpool5]
    simp +zetaDelta only [bs2, bs1, encodeOptMessage, List.append_nil, List.append_assoc]
  | some dec =>
    simp only [Option.isSome_some, Bool.not_true] at hcap_dec_beq hcap_dec_bne
    have hfit_dec : bs2.length + (encodeMessage PolynomialDecoder.encodeRaw 2#32 dec).length ≤ cap.toNat := by
      simp +zetaDelta only [bs2, bs1, encodeOptMessage, List.length_append, List.length_singleton] at hfit ⊢; omega
    apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 4456#64)
    wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv5
    have hpool5 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv5.2).symm
    refine step_encodeToVec_tail_4456_polyDec2_placed A lim st H hpolyDec
      (a + 136#64) sp cap ptr g.1 dec bs2 hfit_dec halign
      (F := optNoHeaderReceivedPBPinnedAt A.repAlloc g.2 (a + 176#64) uc ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hinv_4.trans hinv5.1)
      (by rw [hpool5]; dsimp +zetaDelta only [bs2, bs1, optPolynomialDecoderPBPinnedAt]; sep_ac_rfl) ?_
    intro sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_27 hm5_fp hinv_m5
    simp only [arm64_norm, hx27_4, hfp_4] at hm5_27 hm5_fp
    refine SepWPp.weaken_pre (Entails.of_eq ?_)
      (hnext sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_27 hm5_fp hinv_m5)
    rw [etv2_encodeInnerState_noHeaderReceived_eq]
    simp +zetaDelta only [bs2, bs1, encodeOptMessage,
      optPolynomialDecoderPBPinnedAt, List.append_assoc]; sep_ac_rfl

end LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked2PlacedBudget

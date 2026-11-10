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
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked1
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked2
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked3a
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked3aPlaced
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.ProtoReprCodeSym
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `[LibsignalPlacement]` Phase 2c (Part 3a Aux): `V1State::encode_raw` Variant `idx = 10` (`Block 426`)

Proves `etv3_step_bytes_varint_placed` and `step_encodeToVec_v1_ct2Sampled_placed` (`idx = 10`,
`+3008 .. +1808`) in `Block 426`, threading `A.pool lim st`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked3aPlacedBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.RustHeap (RustAlloc vecU8At)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalSpqrV1
  (PolynomialEncoder ProtoAuthenticator V1State)
open CryptoVerification.LibsignalSpqrV1.Proto
  (encodeMessage encodeOptMessage encodeUint64Field encodeVarint)
open CryptoVerification.SpqrV1.ProtoRepr
  (PolynomialEncoderPBGhost Unchunked2PBGhost
   ct2SentPBEncodedLen ct2SentPBPinnedAt
   noneCap2 optAuthCap optAuthenticatorPBPinnedAt
   optCt2SentPBFieldEncodedLen optCt2SentPBPinnedAt
   optPolynomialEncoderPBFieldEncodedLen optPolynomialEncoderPBPinnedAt
   polynomialEncoderPBEncodedLen polynomialEncoderPBPinnedAt
   unchunked2PinnedAt v1StateInnerPayloadEncodedLen v1StatePBEncodedLen varintLen)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (adds_no_overflow_of_eq cmp_ls_false_of_lt
   hwVarintLen_bvShift_eq_ofNat_varintLen_norm hwVarintLen_eq_ofNat_varintLen_norm
   noneCap_add_one_beq_zero noneCap_add_one_bne_zero
   ofNat_countLeadingZeros_32 ofNat_countLeadingZeros_64
   ule_self_64 ule_zero_64 ult_self_64 ult_zero_64
   zeroExtend64_beq_zero32 zext64_truncate32)
open CryptoVerification.SpqrV1.Prost.EncodeToVec
  (StepInv blkPC_426 blkPl_426
   bv_optPolyEnc_some_eq
   cap_beq_len_false_of_lt elem_len_ult_spare_false_of_le
   encodeToVecCalleeStackOf encodeVarint_length_pos
   etv2_encodeUint64Field_1_eq etv2_optAuth_cap_bounds
   etv3_bv_optCt2Sent_some_eq
   etv3_encodeInnerState_ct2Sampled_eq
   etv3_encodeOptCt2Sent_some_eq
   noneCap2_add_two_beq_zero noneCap2_add_two_bne_zero
   noneCap3 noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
   noneCap_add_two_beq_zero noneCap_add_two_bne_zero
   optCt2SentCap optCt2SentPBPinnedAt_cap_bounds optCt2SentPBPinnedAt_eq
   optPolyEncCap
   optPolynomialEncoderPBPinnedAt_cap_bounds optPolynomialEncoderPBPinnedAt_eq
   ult_of_lt_of_fit
   vecU8At_expose_one vecU8At_expose_slice vecU8At_pack_one
   withStepInv)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsPlacedBudget
  (sepWP_done_tpidr sepWP_done_vm sepWPp_of_sepWP_cs_vm)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhaseBudget
  (authEncodeExactSpecOf encodeVarintExactSpecOf
   step_etv_encode_auth_call_prog step_etv_encode_varint_call_prog)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonBudget
  (leafEncLen16Spec)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonPlacedBudget
  (etvPolyEncoderBudgetExactSpecOf step_etv_leaf_encLen16_call_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked1PlacedBudgetAux
  (sepWPp_extract_pure sepWPp_extract_vecU8At_bounds step_encodeToVec_tail_5700_polyEnc_placed)

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

/-! ## 1. Shared Stepping Helper -/

/-- Shared helper for `BL encode_varint` + slice exposure inside non-empty `Vec<u8>` bytes fields
(`[LibsignalPlacement]`), threading `A.pool lim st`. -/
theorem etv3_step_bytes_varint_placed [LibsignalPlacement] {resStack : Nat}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (H : String → Option (State → State)) {s0 s : State}
    (hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (bytesToWord64LE : BitVec 8) (sp cap ptr ret_pc : BitVec 64)
    (bs srcBs : List (BitVec 8)) (hemp : srcBs.isEmpty = false)
    (hfit : bs.length + 1 + (encodeVarint (BitVec.ofNat 64 srcBs.length)).length + srcBs.length ≤ cap.toNat)
    (hcap : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0) (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = lsmpl.base 292) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .x30 = ret_pc)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 srcBs.length) (hx1 : s.readReg64 .x1 = sp - 120#64)
    (hinv0 : StepInv s0 s)
    (hP : P = ((((sp - 120#64) ↦₆₄ cap) ∗ ((sp - 112#64) ↦₆₄ ptr) ∗
        ((sp - 104#64) ↦₆₄ (BitVec.ofNat 64 bs.length + 1#64)) ∗
        A.repAlloc.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
        ((ptr + BitVec.ofNat 64 bs.length) ↦₈ bytesToWord64LE) ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length + 1#64) (cap.toNat - bs.length - 1)) ∗
      A.pool lim st s ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      let bs_mid := (bs ++ [bytesToWord64LE]) ++ encodeVarint (BitVec.ofNat 64 srcBs.length)
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → StepInv s0 sm → bs_mid.length + srcBs.length ≤ cap.toNat →
      BitVec.ult (cap - BitVec.ofNat 64 bs_mid.length) (BitVec.ofNat 64 srcBs.length) = false →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm
        (((((sp - 120#64) ↦₆₄ cap) ∗ ((sp - 112#64) ↦₆₄ ptr) ∗
            ((sp - 104#64) ↦₆₄ BitVec.ofNat 64 bs_mid.length) ∗
            A.repAlloc.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs_mid) ∗
            memRegion (ptr + BitVec.ofNat 64 bs_mid.length) srcBs.length ∗
            memRegion (ptr + BitVec.ofNat 64 bs_mid.length + BitVec.ofNat 64 srcBs.length)
              (cap.toNat - bs_mid.length - srcBs.length)) ∗
          A.pool lim st sm ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q Qp oom := by
  subst hP
  have ⟨h112, h104⟩ : (sp - 120#64) + 8#64 = sp - 112#64 ∧ (sp - 120#64) + 16#64 = sp - 104#64 :=
    ⟨by bv_omega, by bv_omega⟩
  have hlt_tag : bs.length < cap.toNat := by omega
  have hpack_tag := vecU8At_pack_one A.repAlloc (sp - 120#64) cap ptr bs bytesToWord64LE hlt_tag hcap hptr
  rw [h112, h104] at hpack_tag
  refine step_etv_encode_varint_call_prog A lim st hvarint (BitVec.ofNat 64 srcBs.length)
    (sp - 120#64) cap ptr sp ret_pc (bs ++ [bytesToWord64LE])
    (by simp only [List.length_append, List.length_singleton]; omega)
    (F := F) hpc hrun hsp halign htr hlr hx0 hx1 hinv0 (by rw [← hpack_tag]) ?_
  intro sm hpcm hrunm hspm htrm hcsm hinvm
  let bs_mid := (bs ++ [bytesToWord64LE]) ++ encodeVarint (BitVec.ofNat 64 srcBs.length)
  have hpos : 0 < srcBs.length := List.length_pos_of_ne_nil (List.isEmpty_eq_false_iff.mp hemp)
  have hfit_mc : bs_mid.length + srcBs.length ≤ cap.toNat := by
    dsimp only [bs_mid]; simp only [List.length_append, List.length_singleton]; omega
  have hcmp_mc := elem_len_ult_spare_false_of_le hfit_mc hcap
  refine SepWPp.weaken_pre
    (Entails.of_eq (by rw [vecU8At_expose_slice A.repAlloc (sp - 120#64) cap ptr bs_mid srcBs.length hfit_mc hcap hptr hpos, h112, h104]))
    (hnext sm hpcm hrunm hspm htrm hcsm hinvm hfit_mc hcmp_mc)

/-! ## 2. Variant `idx = 10`: `.ct2Sampled` (`+3008 .. +5712`) -/

theorem step_encodeToVec_v1_ct2Sampled_placed [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (H : String → Option (State → State)) {s0 s : State}
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
    (a sp cap ptr : BitVec 64) (g : PolynomialEncoderPBGhost × Unchunked2PBGhost)
    (v : V1State.Chunked.Ct2Sampled) (bs : List (BitVec 8))
    (hv_len : v1StatePBEncodedLen ⟨some (.ct2Sampled v)⟩ < 2 ^ 64)
    (hfit : bs.length + (V1State.InnerState.encode (.ct2Sampled v)).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_426).base + 3008#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = a) (hinv0 : StepInv s0 s)
    (hP : P = ((optPolynomialEncoderPBPinnedAt A.repAlloc g.1 (a + 136#64) v.sendingCt2 ∗
      optCt2SentPBPinnedAt A.repAlloc g.2 (a + 192#64) v.uc) ∗
      vecU8At A.repAlloc (sp - 120#64) cap ptr bs ∗ A.pool lim st s ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_426).base + 1808#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm
        (((optPolynomialEncoderPBPinnedAt A.repAlloc g.1 (a + 136#64) v.sendingCt2 ∗
          optCt2SentPBPinnedAt A.repAlloc g.2 (a + 192#64) v.uc) ∗
          vecU8At A.repAlloc (sp - 120#64) cap ptr (bs ++ V1State.InnerState.encode (.ct2Sampled v)) ∗
          A.pool lim st sm ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q Qp oom := by
  subst hP
  rcases v with ⟨uc, sendingCt2⟩
  rw [etv3_encodeInnerState_ct2Sampled_eq] at hfit
  simp only [List.length_append, List.length_singleton] at hfit
  have hsub_len : v1StateInnerPayloadEncodedLen (.ct2Sampled ⟨uc, sendingCt2⟩) < 2 ^ 64 := by
    dsimp only [v1StatePBEncodedLen] at hv_len; omega
  have hlt1 : bs.length < cap.toNat := by omega
  have hfit_var : (bs ++ [0x5a#8]).length +
      (encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ct2Sampled ⟨uc, sendingCt2⟩)))).length ≤
      cap.toNat := by
    simp only [List.length_append, List.length_singleton]; omega
  refine sepWPp_extract_vecU8At_bounds (v := sp - 120#64) (cap := cap) (ptr := ptr) (bs := bs)
    (F := optPolynomialEncoderPBPinnedAt A.repAlloc g.1 (a + 136#64) sendingCt2 ∗
      optCt2SentPBPinnedAt A.repAlloc g.2 (a + 192#64) uc ∗ A.pool lim st s ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F)
    (by sep_ac_rfl) fun _ hcap hptr => ?_
  refine sepWPp_extract_pure
    (((optCt2SentCap g.2 uc + 2#64 == 0#64) = !uc.isSome ∧
      (optCt2SentCap g.2 uc + 2#64 != 0#64) = uc.isSome) ∧
     ((optPolyEncCap g.1 sendingCt2 + 1#64 == 0#64) = !sendingCt2.isSome ∧
      (optPolyEncCap g.1 sendingCt2 + 1#64 != 0#64) = sendingCt2.isSome))
    (fun R' hm =>
      ⟨optCt2SentPBPinnedAt_cap_bounds (p := a + 192#64)
        (R := optPolynomialEncoderPBPinnedAt A.repAlloc g.1 (a + 136#64) sendingCt2 ∗
          vecU8At A.repAlloc (sp - 120#64) cap ptr bs ∗ A.pool lim st s ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm),
       optPolynomialEncoderPBPinnedAt_cap_bounds (p := a + 136#64)
        (R := optCt2SentPBPinnedAt A.repAlloc g.2 (a + 192#64) uc ∗
          vecU8At A.repAlloc (sp - 120#64) cap ptr bs ∗ A.pool lim st s ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm)⟩)
    fun ⟨⟨hcap_uc_beq, hcap_uc_bne⟩, ⟨hcap_enc_beq, hcap_enc_bne⟩⟩ => ?_
  have hbeq_false := cap_beq_len_false_of_lt hlt1 hcap
  have ⟨h112, h104⟩ : (sp - 120#64) + 8#64 = sp - 112#64 ∧ (sp - 120#64) + 16#64 = sp - 104#64 :=
    ⟨by bv_omega, by bv_omega⟩
  have hpack := vecU8At_pack_one A.repAlloc (sp - 120#64) cap ptr bs 0x5a#8 hlt1 hcap hptr
  rw [h112, h104] at hpack
  suffices h3512 : ∀ sm1 : State,
      sm1.pc = (blkPl_426).base + 3512#64 → sm1.status = .Running → sm1.sp = sp - 144#64 → sm1.trace = s0.trace →
      sm1.readReg64 .x19 = optCt2SentCap g.2 uc → sm1.readReg64 .x20 = a → sm1.readReg64 .x21 = a + 192#64 →
      sm1.readReg64 .x23 = BitVec.ofNat 64 (optCt2SentPBFieldEncodedLen uc) →
      sm1.readReg64 .x27 = s.readReg64 .x27 → sm1.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm1 →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm1
        (((optPolynomialEncoderPBPinnedAt A.repAlloc g.1 (a + 136#64) sendingCt2 ∗
          optCt2SentPBPinnedAt A.repAlloc g.2 (a + 192#64) uc) ∗
          vecU8At A.repAlloc (sp - 120#64) cap ptr (bs ++ [0x5a#8]) ∗ A.pool lim st sm1 ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom by
    rw [vecU8At_expose_one A.repAlloc (sp - 120#64) cap ptr bs hlt1 hcap hptr, h112, h104]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun b0 => ?_
    cases uc with
    | none =>
      rw [optCt2SentPBPinnedAt_eq A.repAlloc g.2 (a + 192#64) none]
      simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
      apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 3512#64)
      by_vm_steps
        wp_steps
        apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv1
        have hpool1 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv1.2).symm
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (h3512 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *])
            (by simp only [optCt2SentPBFieldEncodedLen, arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1.1))
        rw [← optCt2SentPBPinnedAt_eq A.repAlloc g.2 (a + 192#64) none, ← hpack, hpool1]
    | some u =>
      rw [optCt2SentPBPinnedAt_eq A.repAlloc g.2 (a + 192#64) (some u)]
      simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      have ⟨hu_fit, hopt_u_lt⟩ :
          ct2SentPBEncodedLen u < 2 ^ 64 ∧ optCt2SentPBFieldEncodedLen (some u) < 2 ^ 64 :=
        ⟨by dsimp only [v1StateInnerPayloadEncodedLen, optCt2SentPBFieldEncodedLen] at hsub_len; omega,
         by dsimp only [v1StateInnerPayloadEncodedLen] at hsub_len; omega⟩
      have hvar_u_lt : varintLen (BitVec.ofNat 64 (ct2SentPBEncodedLen u)) <
          optCt2SentPBFieldEncodedLen (some u) := by
        dsimp only [optCt2SentPBFieldEncodedLen]; omega
      have ⟨⟨hu1, hu2, hu3, hu4, hu5⟩, hult_u, hopt_u_eq⟩ :=
        (⟨cmp_ls_false_of_lt hvar_u_lt hopt_u_lt, ult_of_lt_of_fit hvar_u_lt hopt_u_lt,
          etv3_bv_optCt2Sent_some_eq u⟩ : _ ∧ _ ∧ _)
      apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 389)
      by_vm_steps
        wp_steps
        apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv1
        rw [← optCt2SentPBPinnedAt_eq A.repAlloc g.2 (a + 192#64) (some u)]
        refine step_etv_leaf_encLen16_call_placed hres (ct2SentPBPinnedAt A.repAlloc)
          ct2SentPBEncodedLen hct2Len
          (a + 192#64) sp ((blkPl_426).base + 3472#64) g.2 u hu_fit
          (F := optPolynomialEncoderPBPinnedAt A.repAlloc g.1 (a + 136#64) sendingCt2 ∗
            vecU8At A.repAlloc (sp - 120#64) cap ptr (bs ++ [0x5a#8]) ∗ A.pool lim st s ∗ F)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
          (hinv0.trans hinv1.1)
          (by rw [← hpack]; dsimp only [optCt2SentPBPinnedAt]; sep_ac_rfl) ?_
        intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1 hcsm1 hinv_m1 hvm_m1
        rcases hcsm1 with ⟨hm19, hm20, hm21, _, _, _, _, _, hm27, _, hmfp, _⟩
        simp only [arm64_norm, hx20] at hm19 hm20 hm21 hm27 hmfp
        apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 3512#64)
        wp_steps
        apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv2
        have hpool12 := (A.pool_of_vmPreserved (lim := lim) (st := st) (hinv1.2.trans (hvm_m1.trans hinv2.2))).symm
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (h3512 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m1.trans hinv2.1))
        rw [hpool12]; dsimp only [optCt2SentPBPinnedAt]; sep_ac_rfl
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx19_1 hx20_1 hx21_1 hx23_1 hx27_1 hfp_1 hinv_1
  suffices h4180 : ∀ sm2 : State,
      sm2.pc = (blkPl_426).base + 4180#64 → sm2.status = .Running → sm2.sp = sp - 144#64 → sm2.trace = s0.trace →
      sm2.readReg64 .x8 = BitVec.ofNat 64 (optPolynomialEncoderPBFieldEncodedLen sendingCt2) →
      sm2.readReg64 .x19 = optCt2SentCap g.2 uc → sm2.readReg64 .x20 = a → sm2.readReg64 .x21 = a + 192#64 →
      sm2.readReg64 .x22 = optPolyEncCap g.1 sendingCt2 →
      sm2.readReg64 .x23 = BitVec.ofNat 64 (optCt2SentPBFieldEncodedLen uc) →
      sm2.readReg64 .x27 = s.readReg64 .x27 → sm2.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm2 →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm2
        (((optPolynomialEncoderPBPinnedAt A.repAlloc g.1 (a + 136#64) sendingCt2 ∗
          optCt2SentPBPinnedAt A.repAlloc g.2 (a + 192#64) uc) ∗
          vecU8At A.repAlloc (sp - 120#64) cap ptr (bs ++ [0x5a#8]) ∗ A.pool lim st sm2 ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom by
    cases sendingCt2 with
    | none =>
      rw [optPolynomialEncoderPBPinnedAt_eq A.repAlloc g.1 (a + 136#64) none]
      simp only [Option.isSome_none, Bool.not_false] at hcap_enc_beq hcap_enc_bne
      apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 4180#64)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv2
      have hpool2 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv2.2).symm
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h4180 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [optPolynomialEncoderPBFieldEncodedLen, arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (hinv_1.trans hinv2.1))
      rw [← optPolynomialEncoderPBPinnedAt_eq A.repAlloc g.1 (a + 136#64) none, hpool2]
    | some enc =>
      rw [optPolynomialEncoderPBPinnedAt_eq A.repAlloc g.1 (a + 136#64) (some enc)]
      simp only [Option.isSome_some, Bool.not_true] at hcap_enc_beq hcap_enc_bne
      have ⟨henc_fit, hopt_e_lt⟩ :
          polynomialEncoderPBEncodedLen enc < 2 ^ 64 ∧ optPolynomialEncoderPBFieldEncodedLen (some enc) < 2 ^ 64 :=
        ⟨by dsimp only [v1StateInnerPayloadEncodedLen, optPolynomialEncoderPBFieldEncodedLen] at hsub_len; omega,
         by dsimp only [v1StateInnerPayloadEncodedLen] at hsub_len; omega⟩
      have hvar_e_lt : varintLen (BitVec.ofNat 64 (polynomialEncoderPBEncodedLen enc)) <
          optPolynomialEncoderPBFieldEncodedLen (some enc) := by
        dsimp only [optPolynomialEncoderPBFieldEncodedLen]; omega
      have ⟨⟨he1, he2, he3, he4, he5⟩, hult_e, hopt_e_eq⟩ :=
        (⟨cmp_ls_false_of_lt hvar_e_lt hopt_e_lt, ult_of_lt_of_fit hvar_e_lt hopt_e_lt,
          bv_optPolyEnc_some_eq enc⟩ : _ ∧ _ ∧ _)
      apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 401)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv2
      rw [← optPolynomialEncoderPBPinnedAt_eq A.repAlloc g.1 (a + 136#64) (some enc)]
      refine step_etv_leaf_encLen16_call_placed hres (polynomialEncoderPBPinnedAt A.repAlloc)
        polynomialEncoderPBEncodedLen hpolyEncLen
        (a + 136#64) sp ((blkPl_426).base + 3532#64) g.1 enc henc_fit
        (F := optCt2SentPBPinnedAt A.repAlloc g.2 (a + 192#64) uc ∗
          vecU8At A.repAlloc (sp - 120#64) cap ptr (bs ++ [0x5a#8]) ∗ A.pool lim st sm1 ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (hinv_1.trans hinv2.1)
        (by dsimp only [optPolynomialEncoderPBPinnedAt]; sep_ac_rfl) ?_
      intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx0m2 hcsm2 hinv_m2 hvm_m2
      rcases hcsm2 with ⟨hm2_19, hm2_20, hm2_21, hm2_22, hm2_23, _, _, _, hm2_27, _, hm2_fp, _⟩
      simp only [arm64_norm, hx19_1, hx20_1, hx21_1, hx23_1, hx27_1, hfp_1]
        at hm2_19 hm2_20 hm2_21 hm2_22 hm2_23 hm2_27 hm2_fp
      apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 4180#64)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv3
      have hpool23 := (A.pool_of_vmPreserved (lim := lim) (st := st) (hinv2.2.trans (hvm_m2.trans hinv3.2))).symm
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h4180 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m2.trans hinv3.1))
      rw [hpool23]; dsimp only [optPolynomialEncoderPBPinnedAt]; sep_ac_rfl
  intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx8_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx27_2 hfp_2 hinv_2
  have ⟨hadd_sum, hult_sum, hule_sum, hult_sum2, hule_sum2⟩ := adds_no_overflow_of_eq
      (a := optPolynomialEncoderPBFieldEncodedLen sendingCt2)
      (b := optCt2SentPBFieldEncodedLen uc)
      (c := v1StateInnerPayloadEncodedLen (.ct2Sampled ⟨uc, sendingCt2⟩)) rfl hsub_len
  apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 292)
  wp_steps
  apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, wp_norm, *])
  intro hinv3
  have hpool3 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv3.2).symm
  set bs1 := (bs ++ [0x5a#8]) ++
    encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ct2Sampled ⟨uc, sendingCt2⟩)))
  refine step_etv_encode_varint_call_prog A lim st hvarint
    (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ct2Sampled ⟨uc, sendingCt2⟩)))
    (sp - 120#64) cap ptr sp ((blkPl_426).base + 4196#64) (bs ++ [0x5a#8]) hfit_var
    (F := (optPolynomialEncoderPBPinnedAt A.repAlloc g.1 (a + 136#64) sendingCt2 ∗
      optCt2SentPBPinnedAt A.repAlloc g.2 (a + 192#64) uc) ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hinv_2.trans hinv3.1) (by rw [hpool3]; sep_ac_rfl) ?_
  intro sm3 hpcm3 hrunm3 hspm3 htrm3 hcsm3 hinv_m3
  rcases hcsm3 with ⟨hm3_19, hm3_20, hm3_21, hm3_22, _, _, _, _, hm3_27, _, hm3_fp, _⟩
  simp only [arm64_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx27_2, hfp_2]
    at hm3_19 hm3_20 hm3_21 hm3_22 hm3_27 hm3_fp
  set bs2 := bs1 ++ encodeOptMessage V1State.Unchunked.Ct2Sent.encodeRaw 1#32 uc
  suffices h4328 : ∀ sm4 : State,
      sm4.pc = (blkPl_426).base + 4328#64 → sm4.status = .Running → sm4.sp = sp - 144#64 → sm4.trace = s0.trace →
      sm4.readReg64 .x20 = a → sm4.readReg64 .x22 = optPolyEncCap g.1 sendingCt2 →
      sm4.readReg64 .x27 = s.readReg64 .x27 → sm4.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm4 →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm4
        (((optPolynomialEncoderPBPinnedAt A.repAlloc g.1 (a + 136#64) sendingCt2 ∗
          optCt2SentPBPinnedAt A.repAlloc g.2 (a + 192#64) uc) ∗
          vecU8At A.repAlloc (sp - 120#64) cap ptr bs2 ∗ A.pool lim st sm4 ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom by
    cases uc with
    | none =>
      simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
      apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 4328#64)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv4
      have hpool4 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv4.2).symm
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h4328 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m3.trans hinv4.1))
      rw [hpool4]; simp +zetaDelta only [bs2, bs1, encodeOptMessage, List.append_nil]; sep_ac_rfl
    | some u =>
      simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      rw [etv3_encodeOptCt2Sent_some_eq] at hfit
      simp only [List.length_append, List.length_singleton] at hfit
      have hu_lt : ct2SentPBEncodedLen u < 2 ^ 64 := by
        dsimp only [v1StateInnerPayloadEncodedLen, optCt2SentPBFieldEncodedLen] at hsub_len; omega
      have hlt_tag : bs1.length < cap.toNat := by
        dsimp only [bs1]; simp only [List.length_append, List.length_singleton]; omega
      have hbeq_tag := cap_beq_len_false_of_lt hlt_tag hcap
      rw [vecU8At_expose_one A.repAlloc (sp - 120#64) cap ptr bs1 hlt_tag hcap hptr, h112, h104]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPp.exists_elim fun b1 => ?_
      apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 389)
      by_vm_steps
        wp_steps
        apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv4
        have hpack_tag := vecU8At_pack_one A.repAlloc (sp - 120#64) cap ptr bs1 0x0a#8 hlt_tag hcap hptr
        rw [h112, h104] at hpack_tag
        refine step_etv_leaf_encLen16_call_placed hres (ct2SentPBPinnedAt A.repAlloc)
          ct2SentPBEncodedLen hct2Len
          (a + 192#64) sp ((blkPl_426).base + 4248#64) g.2 u hu_lt
          (F := optPolynomialEncoderPBPinnedAt A.repAlloc g.1 (a + 136#64) sendingCt2 ∗
            vecU8At A.repAlloc (sp - 120#64) cap ptr (bs1 ++ [0x0a#8]) ∗ A.pool lim st sm3 ∗ F)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
          (hinv_m3.trans hinv4.1)
          (by rw [← hpack_tag]; dsimp +zetaDelta only [bs1, optCt2SentPBPinnedAt]; sep_ac_rfl) ?_
        intro sm4 hpcm4 hrunm4 hspm4 htrm4 hx0m4 hcsm4 hinv_m4 hvm_m4
        rcases hcsm4 with ⟨hm4_19, hm4_20, hm4_21, hm4_22, _, _, _, _, hm4_27, _, hm4_fp, _⟩
        simp only [arm64_norm, hm3_19, hm3_20, hm3_21, hm3_22, hm3_27, hm3_fp]
          at hm4_19 hm4_20 hm4_21 hm4_22 hm4_27 hm4_fp
        apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 292)
        wp_steps
        apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv5
        set bs_u1 := (bs1 ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 (ct2SentPBEncodedLen u))
        have hfit_uvar : (bs1 ++ [0x0a#8]).length +
            (encodeVarint (BitVec.ofNat 64 (ct2SentPBEncodedLen u))).length ≤ cap.toNat := by
          dsimp only [bs1]; simp only [List.length_append, List.length_singleton]; omega
        refine step_etv_encode_varint_call_prog A lim st hvarint
          (BitVec.ofNat 64 (ct2SentPBEncodedLen u))
          (sp - 120#64) cap ptr sp ((blkPl_426).base + 4256#64) (bs1 ++ [0x0a#8]) hfit_uvar
          (F := optPolynomialEncoderPBPinnedAt A.repAlloc g.1 (a + 136#64) sendingCt2 ∗
            ct2SentPBPinnedAt A.repAlloc g.2 (a + 192#64) u ∗ F)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hinv_m4.trans hinv5.1)
          (by rw [A.pool_of_vmPreserved (lim := lim) (st := st) (hinv4.2.trans (hvm_m4.trans hinv5.2))]; dsimp +zetaDelta only [bs1]; sep_ac_rfl) ?_
        intro sm5 hpcm5 hrunm5 hspm5 htrm5 hcsm5 hinv_m5
        rcases hcsm5 with ⟨hm5_19, hm5_20, hm5_21, hm5_22, _, _, _, _, hm5_27, _, hm5_fp, _⟩
        simp only [arm64_norm, hm4_19, hm4_20, hm4_21, hm4_22, hm4_27, hm4_fp]
          at hm5_19 hm5_20 hm5_21 hm5_22 hm5_27 hm5_fp
        dsimp only [ct2SentPBPinnedAt, unchunked2PinnedAt]
        have h192_48 : (a + 192#64) + 0x30#64 = a + 240#64 := by bv_omega
        rw [h192_48]
        refine sepWPp_extract_pure
          ((optAuthCap g.2 u.auth + 1#64 == 0#64) = !u.auth.isSome ∧
           (optAuthCap g.2 u.auth + 1#64 != 0#64) = u.auth.isSome)
          (fun R' hm => etv2_optAuth_cap_bounds (A := A.repAlloc) (p := a + 192#64)
            (R := optPolynomialEncoderPBPinnedAt A.repAlloc g.1 (a + 136#64) sendingCt2 ∗
              ((a + 240#64) ↦₆₄ u.epoch) ∗ vecU8At A.repAlloc (sp - 120#64) cap ptr bs_u1 ∗ A.pool lim st sm5 ∗
              stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
            (Satisfies.mono (Entails.of_eq (by dsimp +zetaDelta only [bs_u1, bs1]; sep_ac_rfl)) hm))
          fun ⟨hcap_auth_beq, hcap_auth_bne⟩ => ?_
        set bs_u2 := bs_u1 ++ encodeUint64Field 1#32 u.epoch
        suffices h4308 : ∀ sm6 : State,
            sm6.pc = (blkPl_426).base + 4308#64 → sm6.status = .Running → sm6.sp = sp - 144#64 → sm6.trace = s0.trace →
            sm6.readReg64 .x19 = optCt2SentCap g.2 (some u) → sm6.readReg64 .x20 = a →
            sm6.readReg64 .x21 = a + 192#64 → sm6.readReg64 .x22 = optPolyEncCap g.1 sendingCt2 →
            sm6.readReg64 .x27 = s.readReg64 .x27 → sm6.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm6 →
            SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm6
              (((optPolynomialEncoderPBPinnedAt A.repAlloc g.1 (a + 136#64) sendingCt2 ∗
                optAuthenticatorPBPinnedAt A.repAlloc g.2 (a + 192#64) u.auth ∗ ((a + 240#64) ↦₆₄ u.epoch)) ∗
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
                u.epoch (sp - 120#64) cap ptr sp ((blkPl_426).base + 4308#64) (bs_u1 ++ [0x08#8])
                (by simpa only [List.length_append, List.length_singleton] using hfit_ep)
                (F := (optPolynomialEncoderPBPinnedAt A.repAlloc g.1 (a + 136#64) sendingCt2 ∗
                  optAuthenticatorPBPinnedAt A.repAlloc g.2 (a + 192#64) u.auth ∗
                  ((a + 240#64) ↦₆₄ u.epoch)) ∗ F)
                (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (hinv_m5.trans hinv6.1) (by rw [← hpack_ep, hpool6]; sep_ac_rfl) ?_
              intro sm6 hpcm6 hrunm6 hspm6 htrm6 hcsm6 hinv_m6
              rcases hcsm6 with ⟨hm6_19, hm6_20, hm6_21, hm6_22, _, _, _, _, hm6_27, _, hm6_fp, _⟩
              simp only [arm64_norm, hm5_19, hm5_20, hm5_21, hm5_22, hm5_27, hm5_fp]
                at hm6_19 hm6_20 hm6_21 hm6_22 hm6_27 hm6_fp
              refine SepWPp.weaken_pre (Entails.of_eq ?_)
                (h4308 sm6 hpcm6 hrunm6 hspm6 htrm6 hm6_19 hm6_20 hm6_21 hm6_22 hm6_27 hm6_fp hinv_m6)
              simp +zetaDelta only [bs_u2, bs_u1, bs1, etv2_encodeUint64Field_1_eq, hep, Bool.false_eq_true, ↓reduceIte,
                List.append_assoc]; sep_ac_rfl
          · apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 4308#64)
            wp_steps
            apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, wp_norm, *])
            intro hinv6
            have hpool6 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv6.2).symm
            refine SepWPp.weaken_pre (Entails.of_eq ?_)
              (h4308 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m5.trans hinv6.1))
            rw [hpool6]
            simp +zetaDelta only [bs_u2, bs_u1, bs1, etv2_encodeUint64Field_1_eq, hep, ↓reduceIte, List.append_nil]; sep_ac_rfl
        intro sm6 hpcm6 hrunm6 hspm6 htrm6 hx19_6 hx20_6 hx21_6 hx22_6 hx27_6 hfp_6 hinv_6
        have hx19_eq : optCt2SentCap g.2 (some u) = optAuthCap g.2 u.auth := rfl
        rw [hx19_eq] at hx19_6
        cases hauth : u.auth with
        | none =>
          simp only [hauth, Option.isSome_none, Bool.not_false] at hcap_auth_beq hcap_auth_bne
          apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 4328#64)
          wp_steps
          apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, wp_norm, *])
          intro hinv7
          have hpool7 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv7.2).symm
          refine SepWPp.weaken_pre (Entails.of_eq ?_)
            (h4328 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_6.trans hinv7.1))
          dsimp only [bs2]; rw [etv3_encodeOptCt2Sent_some_eq, hpool7]
          simp +zetaDelta only [bs_u2, bs_u1, bs1, hauth, encodeOptMessage,
            optCt2SentPBPinnedAt, ct2SentPBPinnedAt, unchunked2PinnedAt, h192_48,
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
            (a + 192#64) (sp - 120#64) cap ptr sp ((blkPl_426).base + 4328#64) g.2 auth bs_u2 hfit_auth
            (F := (optPolynomialEncoderPBPinnedAt A.repAlloc g.1 (a + 136#64) sendingCt2 ∗
              ((a + 240#64) ↦₆₄ u.epoch)) ∗ F)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hinv_6.trans hinv7.1)
            (by rw [hpool7]; simp +zetaDelta only [bs_u2, bs_u1, bs1, hauth, optAuthenticatorPBPinnedAt]; sep_ac_rfl) ?_
          intro sm7 hpcm7 hrunm7 hspm7 htrm7 hcsm7 hinv_m7
          rcases hcsm7 with ⟨_, hm7_20, _, hm7_22, _, _, _, _, hm7_27, _, hm7_fp, _⟩
          simp only [arm64_norm, hx20_6, hx22_6, hx27_6, hfp_6] at hm7_20 hm7_22 hm7_27 hm7_fp
          refine SepWPp.weaken_pre (Entails.of_eq ?_)
            (h4328 sm7 hpcm7 hrunm7 hspm7 htrm7 hm7_20 hm7_22 hm7_27 hm7_fp hinv_m7)
          dsimp only [bs2]; rw [etv3_encodeOptCt2Sent_some_eq]
          simp +zetaDelta only [bs_u2, bs_u1, bs1, hauth, encodeOptMessage,
            optCt2SentPBPinnedAt, ct2SentPBPinnedAt, unchunked2PinnedAt,
            optAuthenticatorPBPinnedAt, h192_48, List.append_assoc]; sep_ac_rfl
  intro sm4 hpcm4 hrunm4 hspm4 htrm4 hx20_4 hx22_4 hx27_4 hfp_4 hinv_4
  cases sendingCt2 with
  | none =>
    simp only [Option.isSome_none, Bool.not_false] at hcap_enc_beq hcap_enc_bne
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
    rw [etv3_encodeInnerState_ct2Sampled_eq, hpool5]
    simp +zetaDelta only [bs2, bs1, encodeOptMessage, List.append_nil, List.append_assoc]
  | some enc =>
    simp only [Option.isSome_some, Bool.not_true] at hcap_enc_beq hcap_enc_bne
    have hfit_enc : bs2.length + (encodeMessage PolynomialEncoder.encodeRaw 2#32 enc).length ≤ cap.toNat := by
      simp +zetaDelta only [bs2, bs1, encodeOptMessage, List.length_append, List.length_singleton] at hfit ⊢; omega
    apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 5700#64)
    wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv5
    have hpool5 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv5.2).symm
    refine step_encodeToVec_tail_5700_polyEnc_placed A lim st H hpolyEnc
      (a + 136#64) sp cap ptr g.1 enc bs2 hfit_enc halign
      (F := optCt2SentPBPinnedAt A.repAlloc g.2 (a + 192#64) uc ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hinv_4.trans hinv5.1)
      (by rw [hpool5]; dsimp +zetaDelta only [bs2, bs1, optPolynomialEncoderPBPinnedAt]; sep_ac_rfl) ?_
    intro sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_27 hm5_fp hinv_m5
    simp only [arm64_norm, hx27_4, hfp_4] at hm5_27 hm5_fp
    refine SepWPp.weaken_pre (Entails.of_eq ?_)
      (hnext sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_27 hm5_fp hinv_m5)
    rw [etv3_encodeInnerState_ct2Sampled_eq]
    simp +zetaDelta only [bs2, bs1, encodeOptMessage,
      optPolynomialEncoderPBPinnedAt, List.append_assoc]; sep_ac_rfl

end LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked3aPlacedBudgetAux

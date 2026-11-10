/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked2PlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked3aPlacedBudgetAux
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked1
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked2
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked3a
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked3Placed
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.ProtoReprCodeSym
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `[LibsignalPlacement]` Phase 2c (Part 3b Aux): `V1State::encode_raw` Variant `idx = 1` (`Block 426`)

Proves `etv3_step_keysSampled_some_placed` (`+4552 .. +4896`) and
`step_encodeToVec_v1_keysSampled_placed` (`idx = 1`, `+2748 .. +1808`) in `Block 426`,
threading `A.pool lim st`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked3PlacedBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.RustHeap (RustAlloc vecHeader vecU8At)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalSpqrV1
  (PolynomialEncoder ProtoAuthenticator V1State)
open CryptoVerification.LibsignalSpqrV1.Proto
  (encodeBytesField encodeMessage encodeOptMessage encodeUint64Field encodeVarint)
open CryptoVerification.SpqrV1.ProtoRepr
  (PolynomialEncoderPBGhost Unchunked4PBGhost
   headerSentPBEncodedLen headerSentPBPinnedAt
   noneCap2 optAuthCap optAuthenticatorPBPinnedAt optAuthenticatorPBPinnedAt_eq
   optHeaderSentPBFieldEncodedLen optHeaderSentPBPinnedAt
   optPolynomialEncoderPBFieldEncodedLen optPolynomialEncoderPBPinnedAt
   polynomialEncoderPBEncodedLen polynomialEncoderPBPinnedAt
   unchunked4PinnedAt v1StateInnerPayloadEncodedLen v1StatePBEncodedLen varintLen)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (adds_no_overflow_of_eq cmp_ls_false_of_lt
   hwVarintLen_bvShift_eq_ofNat_varintLen_norm hwVarintLen_eq_ofNat_varintLen_norm
   noneCap_add_one_beq_zero noneCap_add_one_bne_zero
   ofNat_countLeadingZeros_32 ofNat_countLeadingZeros_64 ofNat_length_beq_zero_of_lt
   ule_self_64 ule_zero_64 ult_self_64 ult_zero_64
   vecU8At_eq_header_sep_buf vecU8Buf
   zeroExtend64_beq_zero32 zext64_truncate32)
open CryptoVerification.SpqrV1.Prost.EncodeToVec
  (StepInv blkPC_426 blkPl_426
   bv_optPolyEnc_some_eq
   cap_beq_len_false_of_lt
   encodeToVecCalleeStackOf encodeVarint_length_pos
   etv2_encodeBytesField_3_eq etv2_encodeBytesField_4_eq
   etv2_encodeInnerState_keysSampled_eq
   etv2_encodeOptHeaderSent_some_eq
   etv2_encodeUint64Field_1_eq etv2_optAuth_cap_bounds
   etv3_bv_optHeaderSent_some_eq
   noneCap2_add_two_beq_zero noneCap2_add_two_bne_zero
   noneCap3 noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
   noneCap_add_two_beq_zero noneCap_add_two_bne_zero
   optHeaderSentCap optHeaderSentPBPinnedAt_cap_bounds optHeaderSentPBPinnedAt_eq
   optPolyEncCap
   optPolynomialEncoderPBPinnedAt_cap_bounds optPolynomialEncoderPBPinnedAt_eq
   ult_of_lt_of_fit
   vecU8At_expose_one vecU8At_pack_one vecU8At_pack_slice
   withStepInv)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsPlacedBudget
  (sepWP_done_tpidr sepWP_done_vm sepWPp_of_sepWP_cs_vm)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhaseBudget
  (authEncodeExactSpecOf encodeVarintExactSpecOf etvMemcpyRegionSpec
   step_etv_encode_auth_call_prog step_etv_encode_varint_call_prog)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonBudget
  (leafEncLen16Spec)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonPlacedBudget
  (etvPolyEncoderBudgetExactSpecOf
   step_etv_encode_polyEncoder_budget_call_placed
   step_etv_leaf_encLen16_call_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked1PlacedBudgetAux
  (sepWPp_extract_pure sepWPp_extract_vecU8At_bounds)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked2PlacedBudgetAux
  (etv2_step_memcpy_slice_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked3aPlacedBudgetAux
  (etv3_step_bytes_varint_placed)

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

/-! ## 1. Variant `idx = 1`: `.keysSampled` (`+2748 .. +4916`, `+5704 .. +5712`) -/

/-- Step `+4552 .. +4896` (`Block 426`): inline encoding of `u : HeaderSent` at `a + 136#64`,
threading `A.pool lim st`. -/
theorem etv3_step_keysSampled_some_placed [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (H : String → Option (State → State)) {s0 s : State}
    (hhsLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 411)
      (withStepInv s0 (leafEncLen16Spec (headerSentPBPinnedAt A.repAlloc) headerSentPBEncodedLen)))
    (hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hauthEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 314)
      (withStepInv s0 (authEncodeExactSpecOf resStack A lim)))
    (hmemcpy : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      ((blkPl_426).ρ "memcpy") etvMemcpyRegionSpec)
    (a sp cap ptr : BitVec 64) (g : Unchunked4PBGhost) (u : V1State.Unchunked.HeaderSent)
    (bs : List (BitVec 8))
    (hu_lt : headerSentPBEncodedLen u < 2 ^ 64)
    (hfit : bs.length + (encodeOptMessage V1State.Unchunked.HeaderSent.encodeRaw 1#32 (some u)).length ≤ cap.toNat)
    (hcap : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0) (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_426).base + 4552#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = a) (hinv0 : StepInv s0 s)
    (hP : P = (headerSentPBPinnedAt A.repAlloc g (a + 136#64) u ∗
      vecU8At A.repAlloc (sp - 120#64) cap ptr bs ∗ A.pool lim st s ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_426).base + 4896#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm
        ((headerSentPBPinnedAt A.repAlloc g (a + 136#64) u ∗
          vecU8At A.repAlloc (sp - 120#64) cap ptr
            (bs ++ encodeOptMessage V1State.Unchunked.HeaderSent.encodeRaw 1#32 (some u)) ∗
          A.pool lim st sm ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q Qp oom := by
  subst hP
  have ⟨h112, h104⟩ : (sp - 120#64) + 8#64 = sp - 112#64 ∧ (sp - 120#64) + 16#64 = sp - 104#64 :=
    ⟨by bv_omega, by bv_omega⟩
  rw [etv2_encodeOptHeaderSent_some_eq] at hfit
  simp only [List.length_append, List.length_singleton] at hfit
  have hlt1 : bs.length < cap.toNat := by omega
  have hbeq1 := cap_beq_len_false_of_lt hlt1 hcap
  rw [vecU8At_expose_one A.repAlloc (sp - 120#64) cap ptr bs hlt1 hcap hptr, h112, h104]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun b0 => ?_
  apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 411)
  by_vm_steps
    wp_steps
    apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv1
    have hpack1 := vecU8At_pack_one A.repAlloc (sp - 120#64) cap ptr bs 0x0a#8 hlt1 hcap hptr
    rw [h112, h104] at hpack1
    refine step_etv_leaf_encLen16_call_placed hres (headerSentPBPinnedAt A.repAlloc)
      headerSentPBEncodedLen hhsLen
      (a + 136#64) sp ((blkPl_426).base + 4596#64) g u hu_lt
      (F := vecU8At A.repAlloc (sp - 120#64) cap ptr (bs ++ [0x0a#8]) ∗ A.pool lim st s ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
      (hinv0.trans hinv1.1) (by rw [← hpack1]; sep_ac_rfl) ?_
    intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1 hcsm1 hinv_m1 hvm_m1
    rcases hcsm1 with ⟨hm19, hm20, hm21, _, _, _, _, _, hm27, _, hmfp, _⟩
    simp only [arm64_norm, hx20] at hm19 hm20 hm21 hm27 hmfp
    apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 292)
    wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv2
    set bs1 := (bs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 (headerSentPBEncodedLen u))
    have hfit_var : (bs ++ [0x0a#8]).length +
        (encodeVarint (BitVec.ofNat 64 (headerSentPBEncodedLen u))).length ≤ cap.toNat := by
      simp only [List.length_append, List.length_singleton]; omega
    refine step_etv_encode_varint_call_prog A lim st hvarint
      (BitVec.ofNat 64 (headerSentPBEncodedLen u))
      (sp - 120#64) cap ptr sp ((blkPl_426).base + 4604#64) (bs ++ [0x0a#8]) hfit_var
      (F := headerSentPBPinnedAt A.repAlloc g (a + 136#64) u ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hinv_m1.trans hinv2.1)
      (by rw [A.pool_of_vmPreserved (lim := lim) (st := st) (hinv1.2.trans (hvm_m1.trans hinv2.2))]; sep_ac_rfl) ?_
    intro sm2 hpcm2 hrunm2 hspm2 htrm2 hcsm2 hinv_m2
    rcases hcsm2 with ⟨hm2_19, hm2_20, hm2_21, _, _, _, _, _, hm2_27, _, hm2_fp, _⟩
    simp only [arm64_norm, hm19, hm20, hm21, hm27, hmfp]
      at hm2_19 hm2_20 hm2_21 hm2_27 hm2_fp
    dsimp only [headerSentPBPinnedAt, unchunked4PinnedAt]
    have ⟨h136_24, h136_48, h136_96⟩ :
        (a + 136#64) + 0x18#64 = a + 160#64 ∧
        (a + 136#64) + 0x30#64 = a + 184#64 ∧
        (a + 136#64) + 0x60#64 = a + 232#64 :=
      ⟨by bv_omega, by bv_omega, by bv_omega⟩
    rw [h136_24, h136_48, h136_96]
    refine sepWPp_extract_pure
      ((optAuthCap g.auth u.auth + 1#64 == 0#64) = !u.auth.isSome ∧
       (optAuthCap g.auth u.auth + 1#64 != 0#64) = u.auth.isSome)
      (fun R' hm => etv2_optAuth_cap_bounds (A := A.repAlloc) (p := a + 184#64)
        (R := vecU8At A.repAlloc (a + 136#64) g.f3.cap g.f3.ptr u.ek ∗
          vecU8At A.repAlloc (a + 160#64) g.f4.cap g.f4.ptr u.dk ∗
          ((a + 232#64) ↦₆₄ u.epoch) ∗
          vecU8At A.repAlloc (sp - 120#64) cap ptr bs1 ∗ A.pool lim st sm2 ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by dsimp only [bs1]; sep_ac_rfl)) hm))
      fun ⟨hcap_auth_beq, hcap_auth_bne⟩ => ?_
    set bs2 := bs1 ++ encodeUint64Field 1#32 u.epoch
    suffices h4656 : ∀ sm3 : State,
        sm3.pc = (blkPl_426).base + 4656#64 → sm3.status = .Running → sm3.sp = sp - 144#64 → sm3.trace = s0.trace →
        sm3.readReg64 .x19 = s.readReg64 .x19 → sm3.readReg64 .x20 = a → sm3.readReg64 .x21 = s.readReg64 .x21 →
        sm3.readReg64 .x27 = s.readReg64 .x27 → sm3.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm3 →
        SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm3
          (((vecU8At A.repAlloc (a + 136#64) g.f3.cap g.f3.ptr u.ek ∗
            vecU8At A.repAlloc (a + 160#64) g.f4.cap g.f4.ptr u.dk ∗
            optAuthenticatorPBPinnedAt A.repAlloc g.auth (a + 184#64) u.auth ∗
            ((a + 232#64) ↦₆₄ u.epoch)) ∗
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
            u.epoch (sp - 120#64) cap ptr sp ((blkPl_426).base + 4656#64) (bs1 ++ [0x08#8])
            (by simpa only [List.length_append, List.length_singleton] using hfit_ep)
            (F := (vecU8At A.repAlloc (a + 136#64) g.f3.cap g.f3.ptr u.ek ∗
              vecU8At A.repAlloc (a + 160#64) g.f4.cap g.f4.ptr u.dk ∗
              optAuthenticatorPBPinnedAt A.repAlloc g.auth (a + 184#64) u.auth ∗
              ((a + 232#64) ↦₆₄ u.epoch)) ∗ F)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hinv_m2.trans hinv3.1) (by rw [← hpack_ep, hpool3]) ?_
          intro sm3 hpcm3 hrunm3 hspm3 htrm3 hcsm3 hinv_m3
          rcases hcsm3 with ⟨hm3_19, hm3_20, hm3_21, _, _, _, _, _, hm3_27, _, hm3_fp, _⟩
          simp only [arm64_norm, hm2_19, hm2_20, hm2_21, hm2_27, hm2_fp]
            at hm3_19 hm3_20 hm3_21 hm3_27 hm3_fp
          refine SepWPp.weaken_pre (Entails.of_eq ?_)
            (h4656 sm3 hpcm3 hrunm3 hspm3 htrm3 hm3_19 hm3_20 hm3_21 hm3_27 hm3_fp hinv_m3)
          simp +zetaDelta only [bs2, bs1, etv2_encodeUint64Field_1_eq, hep, Bool.false_eq_true, ↓reduceIte,
            List.append_assoc]; sep_ac_rfl
      · apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 4656#64)
        wp_steps
        apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv3
        have hpool3 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv3.2).symm
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (h4656 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (hinv_m2.trans hinv3.1))
        rw [hpool3]
        simp +zetaDelta only [bs2, bs1, etv2_encodeUint64Field_1_eq, hep, ↓reduceIte, List.append_nil]; sep_ac_rfl
    intro sm3 hpcm3 hrunm3 hspm3 htrm3 hx19_3 hx20_3 hx21_3 hx27_3 hfp_3 hinv_3
    set bs3 := bs2 ++ encodeOptMessage ProtoAuthenticator.encodeRaw 2#32 u.auth
    suffices h4680 : ∀ sm4 : State,
        sm4.pc = (blkPl_426).base + 4680#64 → sm4.status = .Running → sm4.sp = sp - 144#64 → sm4.trace = s0.trace →
        sm4.readReg64 .x19 = s.readReg64 .x19 → sm4.readReg64 .x20 = a → sm4.readReg64 .x21 = s.readReg64 .x21 →
        sm4.readReg64 .x27 = s.readReg64 .x27 → sm4.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm4 →
        SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm4
          (((vecU8At A.repAlloc (a + 136#64) g.f3.cap g.f3.ptr u.ek ∗
            vecU8At A.repAlloc (a + 160#64) g.f4.cap g.f4.ptr u.dk ∗
            optAuthenticatorPBPinnedAt A.repAlloc g.auth (a + 184#64) u.auth ∗
            ((a + 232#64) ↦₆₄ u.epoch)) ∗
            vecU8At A.repAlloc (sp - 120#64) cap ptr bs3 ∗ A.pool lim st sm4 ∗
            stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
          Q Qp oom by
      cases hauth : u.auth with
      | none =>
        rw [optAuthenticatorPBPinnedAt_eq A.repAlloc g.auth (a + 184#64) none]
        simp only [hauth, Option.isSome_none, Bool.not_false] at hcap_auth_beq hcap_auth_bne
        apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 4680#64)
        wp_steps
        apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv4
        have hpool4 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv4.2).symm
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (h4680 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (hinv_3.trans hinv4.1))
        rw [← optAuthenticatorPBPinnedAt_eq A.repAlloc g.auth (a + 184#64) none, hpool4]
        simp +zetaDelta only [bs3, bs2, bs1, hauth, encodeOptMessage, List.append_nil]
      | some auth =>
        rw [optAuthenticatorPBPinnedAt_eq A.repAlloc g.auth (a + 184#64) (some auth)]
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
        rw [← optAuthenticatorPBPinnedAt_eq A.repAlloc g.auth (a + 184#64) (some auth)]
        refine step_etv_encode_auth_call_prog A lim st hauthEnc
          (a + 184#64) (sp - 120#64) cap ptr sp ((blkPl_426).base + 4680#64) g.auth auth bs2 hfit_auth
          (F := (vecU8At A.repAlloc (a + 136#64) g.f3.cap g.f3.ptr u.ek ∗
            vecU8At A.repAlloc (a + 160#64) g.f4.cap g.f4.ptr u.dk ∗
            ((a + 232#64) ↦₆₄ u.epoch)) ∗ F)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hinv_3.trans hinv4.1)
          (by rw [hpool4]; dsimp +zetaDelta only [bs2, bs1, optAuthenticatorPBPinnedAt]; sep_ac_rfl) ?_
        intro sm4 hpcm4 hrunm4 hspm4 htrm4 hcsm4 hinv_m4
        rcases hcsm4 with ⟨hm4_19, hm4_20, hm4_21, _, _, _, _, _, hm4_27, _, hm4_fp, _⟩
        simp only [arm64_norm, hx19_3, hx20_3, hx21_3, hx27_3, hfp_3]
          at hm4_19 hm4_20 hm4_21 hm4_27 hm4_fp
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (h4680 sm4 hpcm4 hrunm4 hspm4 htrm4 hm4_19 hm4_20 hm4_21 hm4_27 hm4_fp hinv_m4)
        simp +zetaDelta only [bs3, bs2, bs1, hauth, encodeOptMessage, optAuthenticatorPBPinnedAt]; sep_ac_rfl
    intro sm4 hpcm4 hrunm4 hspm4 htrm4 hx19_4 hx20_4 hx21_4 hx27_4 hfp_4 hinv_4
    refine sepWPp_extract_vecU8At_bounds (A := A.repAlloc) (v := a + 136#64) (cap := g.f3.cap)
      (ptr := g.f3.ptr) (bs := u.ek)
      (F := vecU8At A.repAlloc (a + 160#64) g.f4.cap g.f4.ptr u.dk ∗
        optAuthenticatorPBPinnedAt A.repAlloc g.auth (a + 184#64) u.auth ∗
        ((a + 232#64) ↦₆₄ u.epoch) ∗
        vecU8At A.repAlloc (sp - 120#64) cap ptr bs3 ∗ A.pool lim st sm4 ∗
        stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F)
      (by dsimp +zetaDelta only [bs3, bs2, bs1]; sep_ac_rfl) fun hek_le hek_cap _ => ?_
    have ⟨h144, h152⟩ : (a + 136#64) + 8#64 = a + 144#64 ∧ (a + 136#64) + 16#64 = a + 152#64 :=
      ⟨by bv_omega, by bv_omega⟩
    rw [vecU8At_eq_header_sep_buf A.repAlloc (a + 136#64), vecHeader, h144, h152]
    have hek_lt : u.ek.length < 2 ^ 64 := by omega
    obtain ⟨hbeqz_ek, hbnez_ek⟩ := ofNat_length_beq_zero_of_lt hek_lt
    set bs4 := bs3 ++ encodeBytesField 3#32 u.ek
    suffices h4788 : ∀ sm7 : State,
        sm7.pc = (blkPl_426).base + 4788#64 → sm7.status = .Running → sm7.sp = sp - 144#64 → sm7.trace = s0.trace →
        sm7.readReg64 .x19 = s.readReg64 .x19 → sm7.readReg64 .x20 = a → sm7.readReg64 .x21 = s.readReg64 .x21 →
        sm7.readReg64 .x27 = s.readReg64 .x27 → sm7.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm7 →
        SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm7
          (((vecU8At A.repAlloc (a + 136#64) g.f3.cap g.f3.ptr u.ek ∗
            vecU8At A.repAlloc (a + 160#64) g.f4.cap g.f4.ptr u.dk ∗
            optAuthenticatorPBPinnedAt A.repAlloc g.auth (a + 184#64) u.auth ∗
            ((a + 232#64) ↦₆₄ u.epoch)) ∗
            vecU8At A.repAlloc (sp - 120#64) cap ptr bs4 ∗ A.pool lim st sm7 ∗
            stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
          Q Qp oom by
      cases hemp : u.ek.isEmpty
      · simp only [hemp, Bool.not_false] at hbeqz_ek hbnez_ek
        have hne_ek : u.ek ≠ [] := List.isEmpty_eq_false_iff.mp hemp
        have henc_eq : encodeBytesField 3#32 u.ek =
            [0x1a#8] ++ encodeVarint (BitVec.ofNat 64 u.ek.length) ++ u.ek := by
          rw [etv2_encodeBytesField_3_eq, hemp]; simp only [Bool.false_eq_true, ↓reduceIte]
        have hfit_all : bs3.length + 1 + (encodeVarint (BitVec.ofNat 64 u.ek.length)).length + u.ek.length ≤ cap.toNat := by
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
          refine etv3_step_bytes_varint_placed A lim st H hvarint
            0x1a#8 sp cap ptr ((blkPl_426).base + 4740#64) bs3 u.ek hemp hfit_all hcap hptr halign
            (F := (((a + 136#64) ↦₆₄ g.f3.cap) ∗ ((a + 144#64) ↦₆₄ g.f3.ptr) ∗
              ((a + 152#64) ↦₆₄ BitVec.ofNat 64 u.ek.length)) ∗
              vecU8Buf A.repAlloc g.f3.cap g.f3.ptr u.ek ∗
              vecU8At A.repAlloc (a + 160#64) g.f4.cap g.f4.ptr u.dk ∗
              optAuthenticatorPBPinnedAt A.repAlloc g.auth (a + 184#64) u.auth ∗
              ((a + 232#64) ↦₆₄ u.epoch) ∗ F)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hinv_4.trans hinv5.1) (by rw [hpool5]; dsimp +zetaDelta only [bs3, bs2, bs1]; sep_ac_rfl) ?_
          intro sm5 bs_ek hpcm5 hrunm5 hspm5 htrm5 hcsm5 hinv_m5 hfit_mc hcmp_mc
          rcases hcsm5 with ⟨hm5_19, hm5_20, hm5_21, hm5_22, hm5_23, _, _, _, hm5_27, _, hm5_fp, _⟩
          simp only [arm64_norm, hx19_4, hx20_4, hx21_4, hx27_4, hfp_4]
            at hm5_19 hm5_20 hm5_21 hm5_22 hm5_23 hm5_27 hm5_fp
          apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).ρ "memcpy")
          by_vm_steps
            wp_steps
            apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, wp_norm, *])
            intro hinv6
            have hpool6 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv6.2).symm
            refine etv2_step_memcpy_slice_placed A lim st H hmemcpy
              sp cap ptr g.f3.cap g.f3.ptr ((blkPl_426).base + 4780#64) bs_ek u.ek hemp hek_le halign
              (F := (((a + 136#64) ↦₆₄ g.f3.cap) ∗ ((a + 144#64) ↦₆₄ g.f3.ptr) ∗
                ((a + 152#64) ↦₆₄ BitVec.ofNat 64 u.ek.length)) ∗
                vecU8At A.repAlloc (a + 160#64) g.f4.cap g.f4.ptr u.dk ∗
                optAuthenticatorPBPinnedAt A.repAlloc g.auth (a + 184#64) u.auth ∗
                ((a + 232#64) ↦₆₄ u.epoch) ∗ F)
              (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              hek_lt (hinv_m5.trans hinv6.1) (by rw [hpool6]; dsimp +zetaDelta only [bs_ek, bs3, bs2, bs1]; sep_ac_rfl) ?_
            intro sm6 hpcm6 hrunm6 hspm6 htrm6 hcsm6 hinv_m6
            rcases hcsm6 with ⟨hm6_19, hm6_20, hm6_21, hm6_22, _, hm6_24, _, _, hm6_27, _, hm6_fp, _⟩
            simp only [arm64_norm, hm5_19, hm5_20, hm5_21, hm5_22, hm5_27, hm5_fp]
              at hm6_19 hm6_20 hm6_21 hm6_22 hm6_24 hm6_27 hm6_fp
            apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 4788#64)
            by_vm_steps
              wp_steps
              apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, wp_norm, *])
              intro hinv7
              have hpool7 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv7.2).symm
              have hpack_mc := vecU8At_pack_slice A.repAlloc (sp - 120#64) cap ptr bs_ek u.ek hfit_mc hcap hptr hne_ek
              have hbs_eq : bs_ek ++ u.ek = bs4 := by
                dsimp only [bs4, bs_ek]; rw [henc_eq]; simp only [List.append_assoc]
              rw [h112, h104, hbs_eq] at hpack_mc
              refine SepWPp.weaken_pre (Entails.of_eq ?_)
                (h4788 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                  (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                  (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                  (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                  (by simp only [arm64_norm, *]) (hinv_m6.trans hinv7.1))
              rw [vecU8At_eq_header_sep_buf A.repAlloc (a + 136#64), vecHeader, h144, h152, ← hpack_mc, hpool7]
              dsimp +zetaDelta only [bs4, bs3, bs2, bs1]; sep_ac_rfl
      · simp only [hemp, Bool.not_true] at hbeqz_ek hbnez_ek
        have henc_nil : encodeBytesField 3#32 u.ek = [] := by
          rw [etv2_encodeBytesField_3_eq, hemp]; simp only [↓reduceIte]
        apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 4788#64)
        wp_steps
        apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv5
        have hpool5 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv5.2).symm
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (h4788 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (hinv_4.trans hinv5.1))
        rw [vecU8At_eq_header_sep_buf A.repAlloc (a + 136#64), vecHeader, h144, h152, hpool5]
        simp +zetaDelta only [bs4, bs3, bs2, bs1, henc_nil, List.append_nil]
    intro sm7 hpcm7 hrunm7 hspm7 htrm7 hx19_7 hx20_7 hx21_7 hx27_7 hfp_7 hinv_7
    refine sepWPp_extract_vecU8At_bounds (A := A.repAlloc) (v := a + 160#64) (cap := g.f4.cap)
      (ptr := g.f4.ptr) (bs := u.dk)
      (F := vecU8At A.repAlloc (a + 136#64) g.f3.cap g.f3.ptr u.ek ∗
        optAuthenticatorPBPinnedAt A.repAlloc g.auth (a + 184#64) u.auth ∗
        ((a + 232#64) ↦₆₄ u.epoch) ∗
        vecU8At A.repAlloc (sp - 120#64) cap ptr bs4 ∗ A.pool lim st sm7 ∗
        stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F)
      (by dsimp +zetaDelta only [bs4, bs3, bs2, bs1]; sep_ac_rfl) fun hdk_le hdk_cap _ => ?_
    have ⟨h168, h176⟩ : (a + 160#64) + 8#64 = a + 168#64 ∧ (a + 160#64) + 16#64 = a + 176#64 :=
      ⟨by bv_omega, by bv_omega⟩
    rw [vecU8At_eq_header_sep_buf A.repAlloc (a + 160#64), vecHeader, h168, h176]
    have hdk_lt : u.dk.length < 2 ^ 64 := by omega
    obtain ⟨hbeqz_dk, hbnez_dk⟩ := ofNat_length_beq_zero_of_lt hdk_lt
    cases hemp_dk : u.dk.isEmpty
    · simp only [hemp_dk, Bool.not_false] at hbeqz_dk hbnez_dk
      have hne_dk : u.dk ≠ [] := List.isEmpty_eq_false_iff.mp hemp_dk
      have henc_dk : encodeBytesField 4#32 u.dk =
          [0x22#8] ++ encodeVarint (BitVec.ofNat 64 u.dk.length) ++ u.dk := by
        rw [etv2_encodeBytesField_4_eq, hemp_dk]; simp only [Bool.false_eq_true, ↓reduceIte]
      have hfit_dk : bs4.length + 1 + (encodeVarint (BitVec.ofNat 64 u.dk.length)).length + u.dk.length ≤ cap.toNat := by
        rw [henc_dk] at hfit; dsimp only [bs4, bs3, bs2, bs1] at hfit ⊢
        simp only [List.length_append, List.length_singleton] at hfit ⊢; omega
      have hlt_tag : bs4.length < cap.toNat := by omega
      have hcmp_tag := cap_beq_len_false_of_lt hlt_tag hcap
      rw [vecU8At_expose_one A.repAlloc (sp - 120#64) cap ptr bs4 hlt_tag hcap hptr, h112, h104]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPp.exists_elim fun b3 => ?_
      apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 292)
      by_vm_steps
        wp_steps
        apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv8
        have hpool8 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv8.2).symm
        refine etv3_step_bytes_varint_placed A lim st H hvarint
          0x22#8 sp cap ptr ((blkPl_426).base + 4848#64) bs4 u.dk hemp_dk hfit_dk hcap hptr halign
          (F := vecU8At A.repAlloc (a + 136#64) g.f3.cap g.f3.ptr u.ek ∗
            (((a + 160#64) ↦₆₄ g.f4.cap) ∗ ((a + 168#64) ↦₆₄ g.f4.ptr) ∗
              ((a + 176#64) ↦₆₄ BitVec.ofNat 64 u.dk.length)) ∗
            vecU8Buf A.repAlloc g.f4.cap g.f4.ptr u.dk ∗
            optAuthenticatorPBPinnedAt A.repAlloc g.auth (a + 184#64) u.auth ∗
            ((a + 232#64) ↦₆₄ u.epoch) ∗ F)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hinv_7.trans hinv8.1) (by rw [hpool8]; dsimp +zetaDelta only [bs4, bs3, bs2, bs1]; sep_ac_rfl) ?_
        intro sm8 bs_dk hpcm8 hrunm8 hspm8 htrm8 hcsm8 hinv_m8 hfit_mc hcmp_mc
        rcases hcsm8 with ⟨hm8_19, hm8_20, hm8_21, hm8_22, _, _, _, _, hm8_27, _, hm8_fp, _⟩
        simp only [arm64_norm, hx19_7, hx20_7, hx21_7, hx27_7, hfp_7]
          at hm8_19 hm8_20 hm8_21 hm8_22 hm8_27 hm8_fp
        apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).ρ "memcpy")
        by_vm_steps
          wp_steps
          apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, wp_norm, *])
          intro hinv9
          have hpool9 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv9.2).symm
          refine etv2_step_memcpy_slice_placed A lim st H hmemcpy
            sp cap ptr g.f4.cap g.f4.ptr ((blkPl_426).base + 4888#64) bs_dk u.dk hemp_dk hdk_le halign
            (F := vecU8At A.repAlloc (a + 136#64) g.f3.cap g.f3.ptr u.ek ∗
              (((a + 160#64) ↦₆₄ g.f4.cap) ∗ ((a + 168#64) ↦₆₄ g.f4.ptr) ∗
                ((a + 176#64) ↦₆₄ BitVec.ofNat 64 u.dk.length)) ∗
              optAuthenticatorPBPinnedAt A.repAlloc g.auth (a + 184#64) u.auth ∗
              ((a + 232#64) ↦₆₄ u.epoch) ∗ F)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            hdk_lt (hinv_m8.trans hinv9.1) (by rw [hpool9]; dsimp +zetaDelta only [bs_dk, bs4, bs3, bs2, bs1]; sep_ac_rfl) ?_
          intro sm9 hpcm9 hrunm9 hspm9 htrm9 hcsm9 hinv_m9
          rcases hcsm9 with ⟨hm9_19, _, hm9_21, hm9_22, hm9_23, _, _, _, hm9_27, _, hm9_fp, _⟩
          simp only [arm64_norm, hm8_19, hm8_21, hm8_22, hm8_27, hm8_fp]
            at hm9_19 hm9_21 hm9_22 hm9_23 hm9_27 hm9_fp
          apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 4896#64)
          by_vm_steps
            wp_steps
            apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, wp_norm, *])
            intro hinv10
            have hpool10 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv10.2).symm
            have hpack_mc := vecU8At_pack_slice A.repAlloc (sp - 120#64) cap ptr bs_dk u.dk hfit_mc hcap hptr hne_dk
            have hbs_eq : bs_dk ++ u.dk = bs ++ encodeOptMessage V1State.Unchunked.HeaderSent.encodeRaw 1#32 (some u) := by
              rw [etv2_encodeOptHeaderSent_some_eq, henc_dk]; dsimp only [bs_dk, bs4, bs3, bs2, bs1]
              simp only [List.append_assoc]
            rw [h112, h104, hbs_eq] at hpack_mc
            refine SepWPp.weaken_pre (Entails.of_eq ?_)
              (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m9.trans hinv10.1))
            dsimp only [headerSentPBPinnedAt, unchunked4PinnedAt]
            rw [h136_24, h136_48, h136_96, vecU8At_eq_header_sep_buf A.repAlloc (a + 160#64), vecHeader,
              h168, h176, ← hpack_mc, hpool10]; sep_ac_rfl
    · simp only [hemp_dk, Bool.not_true] at hbeqz_dk hbnez_dk
      have henc_nil : encodeBytesField 4#32 u.dk = [] := by
        rw [etv2_encodeBytesField_4_eq, hemp_dk]; simp only [↓reduceIte]
      apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 4896#64)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv8
      have hpool8 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv8.2).symm
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_7.trans hinv8.1))
      dsimp only [headerSentPBPinnedAt, unchunked4PinnedAt]
      rw [h136_24, h136_48, h136_96, vecU8At_eq_header_sep_buf A.repAlloc (a + 160#64), vecHeader,
        h168, h176, etv2_encodeOptHeaderSent_some_eq, henc_nil, hpool8]
      dsimp only [bs4, bs3, bs2, bs1]; simp only [List.append_nil, List.append_assoc]

theorem step_encodeToVec_v1_keysSampled_placed [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (H : String → Option (State → State)) {s0 s : State}
    (hhsLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 411)
      (withStepInv s0 (leafEncLen16Spec (headerSentPBPinnedAt A.repAlloc) headerSentPBEncodedLen)))
    (hpolyEncLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 401)
      (withStepInv s0 (leafEncLen16Spec (polynomialEncoderPBPinnedAt A.repAlloc) polynomialEncoderPBEncodedLen)))
    (hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hauthEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 314)
      (withStepInv s0 (authEncodeExactSpecOf resStack A lim)))
    (hmemcpy : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      ((blkPl_426).ρ "memcpy") etvMemcpyRegionSpec)
    (hpolyEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 316)
      (withStepInv s0 (etvPolyEncoderBudgetExactSpecOf resStack A lim)))
    (a sp cap ptr : BitVec 64) (g : Unchunked4PBGhost × PolynomialEncoderPBGhost)
    (v : V1State.Chunked.KeysSampled) (bs : List (BitVec 8))
    (hv_len : v1StatePBEncodedLen ⟨some (.keysSampled v)⟩ < 2 ^ 64)
    (hfit : bs.length + (V1State.InnerState.encode (.keysSampled v)).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_426).base + 2748#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = a) (hinv0 : StepInv s0 s)
    (hP : P = ((optHeaderSentPBPinnedAt A.repAlloc g.1 (a + 136#64) v.uc ∗
      optPolynomialEncoderPBPinnedAt A.repAlloc g.2 (a + 240#64) v.sendingHdr) ∗
      vecU8At A.repAlloc (sp - 120#64) cap ptr bs ∗ A.pool lim st s ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_426).base + 1808#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm
        (((optHeaderSentPBPinnedAt A.repAlloc g.1 (a + 136#64) v.uc ∗
          optPolynomialEncoderPBPinnedAt A.repAlloc g.2 (a + 240#64) v.sendingHdr) ∗
          vecU8At A.repAlloc (sp - 120#64) cap ptr (bs ++ V1State.InnerState.encode (.keysSampled v)) ∗
          A.pool lim st sm ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q Qp oom := by
  subst hP
  rcases v with ⟨uc, sendingHdr⟩
  rw [etv2_encodeInnerState_keysSampled_eq] at hfit
  simp only [List.length_append, List.length_singleton] at hfit
  have hsub_len : v1StateInnerPayloadEncodedLen (.keysSampled ⟨uc, sendingHdr⟩) < 2 ^ 64 := by
    dsimp only [v1StatePBEncodedLen] at hv_len; omega
  have hlt1 : bs.length < cap.toNat := by omega
  have hfit_var : (bs ++ [0x12#8]).length +
      (encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.keysSampled ⟨uc, sendingHdr⟩)))).length ≤
      cap.toNat := by
    simp only [List.length_append, List.length_singleton]; omega
  refine sepWPp_extract_vecU8At_bounds (v := sp - 120#64) (cap := cap) (ptr := ptr) (bs := bs)
    (F := optHeaderSentPBPinnedAt A.repAlloc g.1 (a + 136#64) uc ∗
      optPolynomialEncoderPBPinnedAt A.repAlloc g.2 (a + 240#64) sendingHdr ∗ A.pool lim st s ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F)
    (by sep_ac_rfl) fun _ hcap hptr => ?_
  refine sepWPp_extract_pure
    (((optHeaderSentCap g.1 uc + 1#64 == 0#64) = !uc.isSome ∧
      (optHeaderSentCap g.1 uc + 1#64 != 0#64) = uc.isSome) ∧
     ((optPolyEncCap g.2 sendingHdr + 1#64 == 0#64) = !sendingHdr.isSome ∧
      (optPolyEncCap g.2 sendingHdr + 1#64 != 0#64) = sendingHdr.isSome))
    (fun R' hm =>
      ⟨optHeaderSentPBPinnedAt_cap_bounds (p := a + 136#64)
        (R := optPolynomialEncoderPBPinnedAt A.repAlloc g.2 (a + 240#64) sendingHdr ∗
          vecU8At A.repAlloc (sp - 120#64) cap ptr bs ∗ A.pool lim st s ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm),
       optPolynomialEncoderPBPinnedAt_cap_bounds (p := a + 240#64)
        (R := optHeaderSentPBPinnedAt A.repAlloc g.1 (a + 136#64) uc ∗
          vecU8At A.repAlloc (sp - 120#64) cap ptr bs ∗ A.pool lim st s ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm)⟩)
    fun ⟨⟨hcap_uc_beq, hcap_uc_bne⟩, ⟨hcap_enc_beq, hcap_enc_bne⟩⟩ => ?_
  have hbeq_false := cap_beq_len_false_of_lt hlt1 hcap
  have ⟨h112, h104⟩ : (sp - 120#64) + 8#64 = sp - 112#64 ∧ (sp - 120#64) + 16#64 = sp - 104#64 :=
    ⟨by bv_omega, by bv_omega⟩
  have hpack := vecU8At_pack_one A.repAlloc (sp - 120#64) cap ptr bs 0x12#8 hlt1 hcap hptr
  rw [h112, h104] at hpack
  suffices h3792 : ∀ sm1 : State,
      sm1.pc = (blkPl_426).base + 3792#64 → sm1.status = .Running → sm1.sp = sp - 144#64 → sm1.trace = s0.trace →
      sm1.readReg64 .x20 = a → sm1.readReg64 .x22 = optHeaderSentCap g.1 uc →
      sm1.readReg64 .x23 = BitVec.ofNat 64 (optHeaderSentPBFieldEncodedLen uc) →
      sm1.readReg64 .x27 = s.readReg64 .x27 → sm1.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm1 →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm1
        (((optHeaderSentPBPinnedAt A.repAlloc g.1 (a + 136#64) uc ∗
          optPolynomialEncoderPBPinnedAt A.repAlloc g.2 (a + 240#64) sendingHdr) ∗
          vecU8At A.repAlloc (sp - 120#64) cap ptr (bs ++ [0x12#8]) ∗ A.pool lim st sm1 ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom by
    rw [vecU8At_expose_one A.repAlloc (sp - 120#64) cap ptr bs hlt1 hcap hptr, h112, h104]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun b0 => ?_
    cases uc with
    | none =>
      rw [optHeaderSentPBPinnedAt_eq A.repAlloc g.1 (a + 136#64) none]
      simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
      apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 3792#64)
      by_vm_steps
        wp_steps
        apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv1
        have hpool1 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv1.2).symm
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (h3792 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [optHeaderSentPBFieldEncodedLen, arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1.1))
        rw [← optHeaderSentPBPinnedAt_eq A.repAlloc g.1 (a + 136#64) none, ← hpack, hpool1]
    | some u =>
      rw [optHeaderSentPBPinnedAt_eq A.repAlloc g.1 (a + 136#64) (some u)]
      simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      have ⟨hu_fit, hopt_u_lt⟩ :
          headerSentPBEncodedLen u < 2 ^ 64 ∧ optHeaderSentPBFieldEncodedLen (some u) < 2 ^ 64 :=
        ⟨by dsimp only [v1StateInnerPayloadEncodedLen, optHeaderSentPBFieldEncodedLen] at hsub_len; omega,
         by dsimp only [v1StateInnerPayloadEncodedLen] at hsub_len; omega⟩
      have hvar_u_lt : varintLen (BitVec.ofNat 64 (headerSentPBEncodedLen u)) <
          optHeaderSentPBFieldEncodedLen (some u) := by
        dsimp only [optHeaderSentPBFieldEncodedLen]; omega
      have ⟨⟨hu1, hu2, hu3, hu4, hu5⟩, hult_u, hopt_u_eq⟩ :=
        (⟨cmp_ls_false_of_lt hvar_u_lt hopt_u_lt, ult_of_lt_of_fit hvar_u_lt hopt_u_lt,
          etv3_bv_optHeaderSent_some_eq u⟩ : _ ∧ _ ∧ _)
      apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 411)
      by_vm_steps
        wp_steps
        apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv1
        rw [← optHeaderSentPBPinnedAt_eq A.repAlloc g.1 (a + 136#64) (some u)]
        refine step_etv_leaf_encLen16_call_placed hres (headerSentPBPinnedAt A.repAlloc)
          headerSentPBEncodedLen hhsLen
          (a + 136#64) sp ((blkPl_426).base + 2804#64) g.1 u hu_fit
          (F := optPolynomialEncoderPBPinnedAt A.repAlloc g.2 (a + 240#64) sendingHdr ∗
            vecU8At A.repAlloc (sp - 120#64) cap ptr (bs ++ [0x12#8]) ∗ A.pool lim st s ∗ F)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
          (hinv0.trans hinv1.1)
          (by rw [← hpack]; dsimp only [optHeaderSentPBPinnedAt]; sep_ac_rfl) ?_
        intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1 hcsm1 hinv_m1 hvm_m1
        rcases hcsm1 with ⟨_, hm20, _, hm22, _, _, _, _, hm27, _, hmfp, _⟩
        simp only [arm64_norm, hx20] at hm20 hm22 hm27 hmfp
        apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 3792#64)
        wp_steps
        apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv2
        have hpool12 := (A.pool_of_vmPreserved (lim := lim) (st := st) (hinv1.2.trans (hvm_m1.trans hinv2.2))).symm
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (h3792 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (hinv_m1.trans hinv2.1))
        rw [hpool12]; dsimp only [optHeaderSentPBPinnedAt]; sep_ac_rfl
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx20_1 hx22_1 hx23_1 hx27_1 hfp_1 hinv_1
  suffices h4528 : ∀ sm2 : State,
      sm2.pc = (blkPl_426).base + 4528#64 → sm2.status = .Running → sm2.sp = sp - 144#64 → sm2.trace = s0.trace →
      sm2.readReg64 .x8 = BitVec.ofNat 64 (optPolynomialEncoderPBFieldEncodedLen sendingHdr) →
      sm2.readReg64 .x19 = optPolyEncCap g.2 sendingHdr → sm2.readReg64 .x20 = a → sm2.readReg64 .x21 = a + 240#64 →
      sm2.readReg64 .x22 = optHeaderSentCap g.1 uc →
      sm2.readReg64 .x23 = BitVec.ofNat 64 (optHeaderSentPBFieldEncodedLen uc) →
      sm2.readReg64 .x27 = s.readReg64 .x27 → sm2.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm2 →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm2
        (((optHeaderSentPBPinnedAt A.repAlloc g.1 (a + 136#64) uc ∗
          optPolynomialEncoderPBPinnedAt A.repAlloc g.2 (a + 240#64) sendingHdr) ∗
          vecU8At A.repAlloc (sp - 120#64) cap ptr (bs ++ [0x12#8]) ∗ A.pool lim st sm2 ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom by
    cases sendingHdr with
    | none =>
      rw [optPolynomialEncoderPBPinnedAt_eq A.repAlloc g.2 (a + 240#64) none]
      simp only [Option.isSome_none, Bool.not_false] at hcap_enc_beq hcap_enc_bne
      apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 4528#64)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv2
      have hpool2 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv2.2).symm
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h4528 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [optPolynomialEncoderPBFieldEncodedLen, arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (hinv_1.trans hinv2.1))
      rw [← optPolynomialEncoderPBPinnedAt_eq A.repAlloc g.2 (a + 240#64) none, hpool2]
    | some enc =>
      rw [optPolynomialEncoderPBPinnedAt_eq A.repAlloc g.2 (a + 240#64) (some enc)]
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
      rw [← optPolynomialEncoderPBPinnedAt_eq A.repAlloc g.2 (a + 240#64) (some enc)]
      refine step_etv_leaf_encLen16_call_placed hres (polynomialEncoderPBPinnedAt A.repAlloc)
        polynomialEncoderPBEncodedLen hpolyEncLen
        (a + 240#64) sp ((blkPl_426).base + 3816#64) g.2 enc henc_fit
        (F := optHeaderSentPBPinnedAt A.repAlloc g.1 (a + 136#64) uc ∗
          vecU8At A.repAlloc (sp - 120#64) cap ptr (bs ++ [0x12#8]) ∗ A.pool lim st sm1 ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (hinv_1.trans hinv2.1)
        (by dsimp only [optPolynomialEncoderPBPinnedAt]; sep_ac_rfl) ?_
      intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx0m2 hcsm2 hinv_m2 hvm_m2
      rcases hcsm2 with ⟨hm2_19, hm2_20, hm2_21, hm2_22, hm2_23, _, _, _, hm2_27, _, hm2_fp, _⟩
      simp only [arm64_norm, hx20_1, hx22_1, hx23_1, hx27_1, hfp_1]
        at hm2_19 hm2_20 hm2_21 hm2_22 hm2_23 hm2_27 hm2_fp
      apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 4528#64)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv3
      have hpool23 := (A.pool_of_vmPreserved (lim := lim) (st := st) (hinv2.2.trans (hvm_m2.trans hinv3.2))).symm
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h4528 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m2.trans hinv3.1))
      rw [hpool23]; dsimp only [optPolynomialEncoderPBPinnedAt]; sep_ac_rfl
  intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx8_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx27_2 hfp_2 hinv_2
  have ⟨hadd_sum, hult_sum, hule_sum, hult_sum2, hule_sum2⟩ := adds_no_overflow_of_eq
      (a := optPolynomialEncoderPBFieldEncodedLen sendingHdr)
      (b := optHeaderSentPBFieldEncodedLen uc)
      (c := v1StateInnerPayloadEncodedLen (.keysSampled ⟨uc, sendingHdr⟩)) rfl hsub_len
  apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 292)
  wp_steps
  apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, wp_norm, *])
  intro hinv3
  have hpool3 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv3.2).symm
  set bs1 := (bs ++ [0x12#8]) ++
    encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.keysSampled ⟨uc, sendingHdr⟩)))
  refine step_etv_encode_varint_call_prog A lim st hvarint
    (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.keysSampled ⟨uc, sendingHdr⟩)))
    (sp - 120#64) cap ptr sp ((blkPl_426).base + 4544#64) (bs ++ [0x12#8]) hfit_var
    (F := (optHeaderSentPBPinnedAt A.repAlloc g.1 (a + 136#64) uc ∗
      optPolynomialEncoderPBPinnedAt A.repAlloc g.2 (a + 240#64) sendingHdr) ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hinv_2.trans hinv3.1) (by rw [hpool3]; sep_ac_rfl) ?_
  intro sm3 hpcm3 hrunm3 hspm3 htrm3 hcsm3 hinv_m3
  rcases hcsm3 with ⟨hm3_19, hm3_20, hm3_21, hm3_22, _, _, _, _, hm3_27, _, hm3_fp, _⟩
  simp only [arm64_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx27_2, hfp_2]
    at hm3_19 hm3_20 hm3_21 hm3_22 hm3_27 hm3_fp
  set bs2 := bs1 ++ encodeOptMessage V1State.Unchunked.HeaderSent.encodeRaw 1#32 uc
  suffices h4896 : ∀ sm4 : State,
      sm4.pc = (blkPl_426).base + 4896#64 → sm4.status = .Running → sm4.sp = sp - 144#64 → sm4.trace = s0.trace →
      sm4.readReg64 .x19 = optPolyEncCap g.2 sendingHdr → sm4.readReg64 .x21 = a + 240#64 →
      sm4.readReg64 .x27 = s.readReg64 .x27 → sm4.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm4 →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm4
        (((optHeaderSentPBPinnedAt A.repAlloc g.1 (a + 136#64) uc ∗
          optPolynomialEncoderPBPinnedAt A.repAlloc g.2 (a + 240#64) sendingHdr) ∗
          vecU8At A.repAlloc (sp - 120#64) cap ptr bs2 ∗ A.pool lim st sm4 ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom by
    cases uc with
    | none =>
      simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
      apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 4896#64)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv4
      have hpool4 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv4.2).symm
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h4896 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m3.trans hinv4.1))
      rw [hpool4]; simp +zetaDelta only [bs2, bs1, encodeOptMessage, List.append_nil]; sep_ac_rfl
    | some u =>
      simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      have hu_lt : headerSentPBEncodedLen u < 2 ^ 64 := by
        dsimp only [v1StateInnerPayloadEncodedLen, optHeaderSentPBFieldEncodedLen] at hsub_len; omega
      have hfit_u : bs1.length + (encodeOptMessage V1State.Unchunked.HeaderSent.encodeRaw 1#32 (some u)).length ≤ cap.toNat := by
        dsimp only [bs1]; simp only [List.length_append, List.length_singleton] at hfit ⊢; omega
      apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 4552#64)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv4
      have hpool4 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv4.2).symm
      refine etv3_step_keysSampled_some_placed hres A lim st H hhsLen hvarint hauthEnc hmemcpy
        a sp cap ptr g.1 u bs1 hu_lt hfit_u hcap hptr halign
        (F := optPolynomialEncoderPBPinnedAt A.repAlloc g.2 (a + 240#64) sendingHdr ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hinv_m3.trans hinv4.1)
        (by rw [hpool4]; dsimp +zetaDelta only [bs1, optHeaderSentPBPinnedAt]; simp only [List.append_assoc]; sep_ac_rfl) ?_
      intro sm4 hpcm4 hrunm4 hspm4 htrm4 hm4_19 hm4_21 hm4_27 hm4_fp hinv_m4
      simp only [arm64_norm, hm3_19, hm3_21, hm3_27, hm3_fp]
        at hm4_19 hm4_21 hm4_27 hm4_fp
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h4896 sm4 hpcm4 hrunm4 hspm4 htrm4 hm4_19 hm4_21 hm4_27 hm4_fp hinv_m4)
      dsimp only [bs2, optHeaderSentPBPinnedAt]; sep_ac_rfl
  intro sm4 hpcm4 hrunm4 hspm4 htrm4 hx19_4 hx21_4 hx27_4 hfp_4 hinv_4
  cases sendingHdr with
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
    rw [etv2_encodeInnerState_keysSampled_eq, hpool5]
    simp +zetaDelta only [bs2, bs1, encodeOptMessage, List.append_nil, List.append_assoc]
  | some enc =>
    simp only [Option.isSome_some, Bool.not_true] at hcap_enc_beq hcap_enc_bne
    have hfit_enc : bs2.length + (encodeMessage PolynomialEncoder.encodeRaw 2#32 enc).length ≤ cap.toNat := by
      simp +zetaDelta only [bs2, bs1, encodeOptMessage, List.length_append, List.length_singleton] at hfit ⊢; omega
    apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 316)
    wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv5
    refine step_etv_encode_polyEncoder_budget_call_placed A lim st hpolyEnc
      (a + 240#64) (sp - 120#64) cap ptr sp ((blkPl_426).base + 5708#64) g.2 enc bs2 hfit_enc
      (F := optHeaderSentPBPinnedAt A.repAlloc g.1 (a + 136#64) uc ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hinv_4.trans hinv5.1)
      (by rw [A.pool_of_vmPreserved hinv5.2]; dsimp +zetaDelta only [bs2, bs1, optPolynomialEncoderPBPinnedAt]; sep_ac_rfl) ?_
    intro sm5 hpcm5 hrunm5 hspm5 htrm5 hcsm5 hinv_m5
    rcases hcsm5 with ⟨_, _, _, _, _, _, _, _, hm5_27, _, hm5_fp, _⟩
    simp only [arm64_norm, hx27_4, hfp_4] at hm5_27 hm5_fp
    apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 1808#64)
    wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv6
    refine SepWPp.weaken_pre (Entails.of_eq ?_)
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m5.trans hinv6.1))
    rw [A.pool_of_vmPreserved hinv6.2, etv2_encodeInnerState_keysSampled_eq]
    simp +zetaDelta only [bs2, bs1, encodeOptMessage,
      optPolynomialEncoderPBPinnedAt, List.append_assoc]; sep_ac_rfl

end LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked3PlacedBudgetAux

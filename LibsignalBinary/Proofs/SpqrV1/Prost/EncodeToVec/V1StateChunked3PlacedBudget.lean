/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked2PlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked3aPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked3PlacedBudgetAux
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
# Budget-Threaded `[LibsignalPlacement]` Phase 2c (Part 3b): `V1State::encode_raw` Variants `idx = 1, 8` (`Block 426`)

Re-exports `idx = 1` (`.keysSampled`) from `V1StateChunked3PlacedBudgetAux` and proves
`etv3_step_ekReceivedCt1Sampled_some_placed` (`+5236 .. +5688`) and
`step_encodeToVec_v1_ekReceivedCt1Sampled_placed` (`idx = 8`, `+3068 .. +1808`), threading `A.pool lim st`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked3PlacedBudget

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
  (PolynomialEncoderPBGhost Unchunked5PBGhost
   ct1SentEkReceivedPBEncodedLen ct1SentEkReceivedPBPinnedAt
   noneCap2 optAuthCap optAuthenticatorPBPinnedAt optAuthenticatorPBPinnedAt_eq
   optCt1SentEkReceivedPBFieldEncodedLen optCt1SentEkReceivedPBPinnedAt
   optPolynomialEncoderPBFieldEncodedLen optPolynomialEncoderPBPinnedAt
   polynomialEncoderPBEncodedLen polynomialEncoderPBPinnedAt
   unchunked5PinnedAt v1StateInnerPayloadEncodedLen v1StatePBEncodedLen varintLen)
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
   etv2_encodeUint64Field_1_eq etv2_optAuth_cap_bounds
   etv3_bv_optCt1SentEkReceived_some_eq
   etv3_encodeBytesField_5_eq
   etv3_encodeInnerState_ekReceivedCt1Sampled_eq
   etv3_encodeOptCt1SentEkReceived_some_eq
   noneCap2_add_two_beq_zero noneCap2_add_two_bne_zero
   noneCap3 noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
   noneCap_add_two_beq_zero noneCap_add_two_bne_zero
   optCt1SentEkReceivedCap optCt1SentEkReceivedPBPinnedAt_cap_bounds optCt1SentEkReceivedPBPinnedAt_eq
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
  (etvPolyEncoderBudgetExactSpecOf step_etv_leaf_encLen16_call_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked1PlacedBudgetAux
  (sepWPp_extract_pure sepWPp_extract_vecU8At_bounds step_encodeToVec_tail_5700_polyEnc_placed)
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

/-! ## 1. Re-Exports from `V1StateChunked3PlacedBudgetAux` -/

abbrev etv3_step_keysSampled_some_placed :=
  @V1StateChunked3PlacedBudgetAux.etv3_step_keysSampled_some_placed

abbrev step_encodeToVec_v1_keysSampled_placed :=
  @V1StateChunked3PlacedBudgetAux.step_encodeToVec_v1_keysSampled_placed

/-! ## 2. Variant `idx = 8`: `.ekReceivedCt1Sampled` (`+3068 .. +5700`) -/

/-- Step `+5236 .. +5688` (`Block 426`): inline encoding of `u : Ct1SentEkReceived` at `a + 136#64`,
threading `A.pool lim st`. -/
theorem etv3_step_ekReceivedCt1Sampled_some_placed [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (H : String → Option (State → State)) {s0 s : State}
    (hct1Len : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 387)
      (withStepInv s0 (leafEncLen16Spec (ct1SentEkReceivedPBPinnedAt A.repAlloc) ct1SentEkReceivedPBEncodedLen)))
    (hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hauthEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 314)
      (withStepInv s0 (authEncodeExactSpecOf resStack A lim)))
    (hmemcpy : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      ((blkPl_426).ρ "memcpy") etvMemcpyRegionSpec)
    (a sp cap ptr : BitVec 64) (g : Unchunked5PBGhost) (u : V1State.Unchunked.Ct1SentEkReceived)
    (bs : List (BitVec 8))
    (hu_lt : ct1SentEkReceivedPBEncodedLen u < 2 ^ 64)
    (hfit : bs.length + (encodeOptMessage V1State.Unchunked.Ct1SentEkReceived.encodeRaw 1#32 (some u)).length ≤ cap.toNat)
    (hcap : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0) (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_426).base + 5236#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = a) (hinv0 : StepInv s0 s)
    (hP : P = (ct1SentEkReceivedPBPinnedAt A.repAlloc g (a + 136#64) u ∗
      vecU8At A.repAlloc (sp - 120#64) cap ptr bs ∗ A.pool lim st s ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_426).base + 5688#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = a →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm
        ((ct1SentEkReceivedPBPinnedAt A.repAlloc g (a + 136#64) u ∗
          vecU8At A.repAlloc (sp - 120#64) cap ptr
            (bs ++ encodeOptMessage V1State.Unchunked.Ct1SentEkReceived.encodeRaw 1#32 (some u)) ∗
          A.pool lim st sm ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q Qp oom := by
  subst hP
  have ⟨h112, h104⟩ : (sp - 120#64) + 8#64 = sp - 112#64 ∧ (sp - 120#64) + 16#64 = sp - 104#64 :=
    ⟨by bv_omega, by bv_omega⟩
  rw [etv3_encodeOptCt1SentEkReceived_some_eq] at hfit
  simp only [List.length_append, List.length_singleton] at hfit
  have hlt1 : bs.length < cap.toNat := by omega
  have hbeq1 := cap_beq_len_false_of_lt hlt1 hcap
  rw [vecU8At_expose_one A.repAlloc (sp - 120#64) cap ptr bs hlt1 hcap hptr, h112, h104]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun b0 => ?_
  apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 387)
  by_vm_steps
    wp_steps
    apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv1
    have hpack1 := vecU8At_pack_one A.repAlloc (sp - 120#64) cap ptr bs 0x0a#8 hlt1 hcap hptr
    rw [h112, h104] at hpack1
    refine step_etv_leaf_encLen16_call_placed hres (ct1SentEkReceivedPBPinnedAt A.repAlloc)
      ct1SentEkReceivedPBEncodedLen hct1Len
      (a + 136#64) sp ((blkPl_426).base + 5280#64) g u hu_lt
      (F := vecU8At A.repAlloc (sp - 120#64) cap ptr (bs ++ [0x0a#8]) ∗ A.pool lim st s ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
      (hinv0.trans hinv1.1) (by rw [← hpack1]; sep_ac_rfl) ?_
    intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1 hcsm1 hinv_m1 hvm_m1
    rcases hcsm1 with ⟨hm19, hm20, _, _, _, _, _, _, hm27, _, hmfp, _⟩
    simp only [arm64_norm, hx20] at hm19 hm20 hm27 hmfp
    apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 292)
    wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv2
    set bs1 := (bs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 (ct1SentEkReceivedPBEncodedLen u))
    have hfit_var : (bs ++ [0x0a#8]).length +
        (encodeVarint (BitVec.ofNat 64 (ct1SentEkReceivedPBEncodedLen u))).length ≤ cap.toNat := by
      simp only [List.length_append, List.length_singleton]; omega
    refine step_etv_encode_varint_call_prog A lim st hvarint
      (BitVec.ofNat 64 (ct1SentEkReceivedPBEncodedLen u))
      (sp - 120#64) cap ptr sp ((blkPl_426).base + 5288#64) (bs ++ [0x0a#8]) hfit_var
      (F := ct1SentEkReceivedPBPinnedAt A.repAlloc g (a + 136#64) u ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hinv_m1.trans hinv2.1)
      (by rw [A.pool_of_vmPreserved (lim := lim) (st := st) (hinv1.2.trans (hvm_m1.trans hinv2.2))]; sep_ac_rfl) ?_
    intro sm2 hpcm2 hrunm2 hspm2 htrm2 hcsm2 hinv_m2
    rcases hcsm2 with ⟨hm2_19, hm2_20, _, _, _, _, _, _, hm2_27, _, hm2_fp, _⟩
    simp only [arm64_norm, hm19, hm20, hm27, hmfp]
      at hm2_19 hm2_20 hm2_27 hm2_fp
    dsimp only [ct1SentEkReceivedPBPinnedAt, unchunked5PinnedAt]
    have ⟨h136_24, h136_48, h136_72, h136_120⟩ :
        (a + 136#64) + 0x18#64 = a + 160#64 ∧
        (a + 136#64) + 0x30#64 = a + 184#64 ∧
        (a + 136#64) + 0x48#64 = a + 208#64 ∧
        (a + 136#64) + 0x78#64 = a + 256#64 :=
      ⟨by bv_omega, by bv_omega, by bv_omega, by bv_omega⟩
    rw [h136_24, h136_48, h136_72, h136_120]
    refine sepWPp_extract_pure
      ((optAuthCap g.auth u.auth + 1#64 == 0#64) = !u.auth.isSome ∧
       (optAuthCap g.auth u.auth + 1#64 != 0#64) = u.auth.isSome)
      (fun R' hm => etv2_optAuth_cap_bounds (A := A.repAlloc) (p := a + 208#64)
        (R := vecU8At A.repAlloc (a + 136#64) g.f3.cap g.f3.ptr u.es ∗
          vecU8At A.repAlloc (a + 160#64) g.f4.cap g.f4.ptr u.ek ∗
          vecU8At A.repAlloc (a + 184#64) g.f5.cap g.f5.ptr u.ct1 ∗
          ((a + 256#64) ↦₆₄ u.epoch) ∗
          vecU8At A.repAlloc (sp - 120#64) cap ptr bs1 ∗ A.pool lim st sm2 ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by dsimp only [bs1]; sep_ac_rfl)) hm))
      fun ⟨hcap_auth_beq, hcap_auth_bne⟩ => ?_
    set bs2 := bs1 ++ encodeUint64Field 1#32 u.epoch
    suffices h5340 : ∀ sm3 : State,
        sm3.pc = (blkPl_426).base + 5340#64 → sm3.status = .Running → sm3.sp = sp - 144#64 → sm3.trace = s0.trace →
        sm3.readReg64 .x19 = s.readReg64 .x19 → sm3.readReg64 .x20 = a →
        sm3.readReg64 .x27 = s.readReg64 .x27 → sm3.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm3 →
        SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm3
          (((vecU8At A.repAlloc (a + 136#64) g.f3.cap g.f3.ptr u.es ∗
            vecU8At A.repAlloc (a + 160#64) g.f4.cap g.f4.ptr u.ek ∗
            vecU8At A.repAlloc (a + 184#64) g.f5.cap g.f5.ptr u.ct1 ∗
            optAuthenticatorPBPinnedAt A.repAlloc g.auth (a + 208#64) u.auth ∗
            ((a + 256#64) ↦₆₄ u.epoch)) ∗
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
            u.epoch (sp - 120#64) cap ptr sp ((blkPl_426).base + 5340#64) (bs1 ++ [0x08#8])
            (by simpa only [List.length_append, List.length_singleton] using hfit_ep)
            (F := (vecU8At A.repAlloc (a + 136#64) g.f3.cap g.f3.ptr u.es ∗
              vecU8At A.repAlloc (a + 160#64) g.f4.cap g.f4.ptr u.ek ∗
              vecU8At A.repAlloc (a + 184#64) g.f5.cap g.f5.ptr u.ct1 ∗
              optAuthenticatorPBPinnedAt A.repAlloc g.auth (a + 208#64) u.auth ∗
              ((a + 256#64) ↦₆₄ u.epoch)) ∗ F)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hinv_m2.trans hinv3.1) (by rw [← hpack_ep, hpool3]) ?_
          intro sm3 hpcm3 hrunm3 hspm3 htrm3 hcsm3 hinv_m3
          rcases hcsm3 with ⟨hm3_19, hm3_20, _, _, _, _, _, _, hm3_27, _, hm3_fp, _⟩
          simp only [arm64_norm, hm2_19, hm2_20, hm2_27, hm2_fp]
            at hm3_19 hm3_20 hm3_27 hm3_fp
          refine SepWPp.weaken_pre (Entails.of_eq ?_)
            (h5340 sm3 hpcm3 hrunm3 hspm3 htrm3 hm3_19 hm3_20 hm3_27 hm3_fp hinv_m3)
          simp +zetaDelta only [bs2, bs1, etv2_encodeUint64Field_1_eq, hep, Bool.false_eq_true, ↓reduceIte,
            List.append_assoc]; sep_ac_rfl
      · apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 5340#64)
        wp_steps
        apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv3
        have hpool3 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv3.2).symm
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (h5340 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m2.trans hinv3.1))
        rw [hpool3]
        simp +zetaDelta only [bs2, bs1, etv2_encodeUint64Field_1_eq, hep, ↓reduceIte, List.append_nil]; sep_ac_rfl
    intro sm3 hpcm3 hrunm3 hspm3 htrm3 hx19_3 hx20_3 hx27_3 hfp_3 hinv_3
    set bs3 := bs2 ++ encodeOptMessage ProtoAuthenticator.encodeRaw 2#32 u.auth
    suffices h5364 : ∀ sm4 : State,
        sm4.pc = (blkPl_426).base + 5364#64 → sm4.status = .Running → sm4.sp = sp - 144#64 → sm4.trace = s0.trace →
        sm4.readReg64 .x19 = s.readReg64 .x19 → sm4.readReg64 .x20 = a →
        sm4.readReg64 .x27 = s.readReg64 .x27 → sm4.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm4 →
        SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm4
          (((vecU8At A.repAlloc (a + 136#64) g.f3.cap g.f3.ptr u.es ∗
            vecU8At A.repAlloc (a + 160#64) g.f4.cap g.f4.ptr u.ek ∗
            vecU8At A.repAlloc (a + 184#64) g.f5.cap g.f5.ptr u.ct1 ∗
            optAuthenticatorPBPinnedAt A.repAlloc g.auth (a + 208#64) u.auth ∗
            ((a + 256#64) ↦₆₄ u.epoch)) ∗
            vecU8At A.repAlloc (sp - 120#64) cap ptr bs3 ∗ A.pool lim st sm4 ∗
            stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
          Q Qp oom by
      cases hauth : u.auth with
      | none =>
        rw [optAuthenticatorPBPinnedAt_eq A.repAlloc g.auth (a + 208#64) none]
        simp only [hauth, Option.isSome_none, Bool.not_false] at hcap_auth_beq hcap_auth_bne
        apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 5364#64)
        wp_steps
        apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv4
        have hpool4 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv4.2).symm
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (h5364 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_3.trans hinv4.1))
        rw [← optAuthenticatorPBPinnedAt_eq A.repAlloc g.auth (a + 208#64) none, hpool4]
        simp +zetaDelta only [bs3, bs2, bs1, hauth, encodeOptMessage, List.append_nil]
      | some auth =>
        rw [optAuthenticatorPBPinnedAt_eq A.repAlloc g.auth (a + 208#64) (some auth)]
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
        rw [← optAuthenticatorPBPinnedAt_eq A.repAlloc g.auth (a + 208#64) (some auth)]
        refine step_etv_encode_auth_call_prog A lim st hauthEnc
          (a + 208#64) (sp - 120#64) cap ptr sp ((blkPl_426).base + 5364#64) g.auth auth bs2 hfit_auth
          (F := (vecU8At A.repAlloc (a + 136#64) g.f3.cap g.f3.ptr u.es ∗
            vecU8At A.repAlloc (a + 160#64) g.f4.cap g.f4.ptr u.ek ∗
            vecU8At A.repAlloc (a + 184#64) g.f5.cap g.f5.ptr u.ct1 ∗
            ((a + 256#64) ↦₆₄ u.epoch)) ∗ F)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hinv_3.trans hinv4.1)
          (by rw [hpool4]; dsimp +zetaDelta only [bs2, bs1, optAuthenticatorPBPinnedAt]; sep_ac_rfl) ?_
        intro sm4 hpcm4 hrunm4 hspm4 htrm4 hcsm4 hinv_m4
        rcases hcsm4 with ⟨hm4_19, hm4_20, _, _, _, _, _, _, hm4_27, _, hm4_fp, _⟩
        simp only [arm64_norm, hx19_3, hx20_3, hx27_3, hfp_3]
          at hm4_19 hm4_20 hm4_27 hm4_fp
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (h5364 sm4 hpcm4 hrunm4 hspm4 htrm4 hm4_19 hm4_20 hm4_27 hm4_fp hinv_m4)
        simp +zetaDelta only [bs3, bs2, bs1, hauth, encodeOptMessage, optAuthenticatorPBPinnedAt]; sep_ac_rfl
    intro sm4 hpcm4 hrunm4 hspm4 htrm4 hx19_4 hx20_4 hx27_4 hfp_4 hinv_4
    set bs4 := bs3 ++ encodeBytesField 3#32 u.es
    suffices h5472 : ∀ sm7 : State,
        sm7.pc = (blkPl_426).base + 5472#64 → sm7.status = .Running → sm7.sp = sp - 144#64 → sm7.trace = s0.trace →
        sm7.readReg64 .x19 = s.readReg64 .x19 → sm7.readReg64 .x20 = a →
        sm7.readReg64 .x27 = s.readReg64 .x27 → sm7.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm7 →
        SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm7
          (((vecU8At A.repAlloc (a + 136#64) g.f3.cap g.f3.ptr u.es ∗
            vecU8At A.repAlloc (a + 160#64) g.f4.cap g.f4.ptr u.ek ∗
            vecU8At A.repAlloc (a + 184#64) g.f5.cap g.f5.ptr u.ct1 ∗
            optAuthenticatorPBPinnedAt A.repAlloc g.auth (a + 208#64) u.auth ∗
            ((a + 256#64) ↦₆₄ u.epoch)) ∗
            vecU8At A.repAlloc (sp - 120#64) cap ptr bs4 ∗ A.pool lim st sm7 ∗
            stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
          Q Qp oom by
      refine sepWPp_extract_vecU8At_bounds (A := A.repAlloc) (v := a + 136#64) (cap := g.f3.cap)
        (ptr := g.f3.ptr) (bs := u.es)
        (F := vecU8At A.repAlloc (a + 160#64) g.f4.cap g.f4.ptr u.ek ∗
          vecU8At A.repAlloc (a + 184#64) g.f5.cap g.f5.ptr u.ct1 ∗
          optAuthenticatorPBPinnedAt A.repAlloc g.auth (a + 208#64) u.auth ∗
          ((a + 256#64) ↦₆₄ u.epoch) ∗
          vecU8At A.repAlloc (sp - 120#64) cap ptr bs3 ∗ A.pool lim st sm4 ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F)
        (by dsimp +zetaDelta only [bs3, bs2, bs1]; sep_ac_rfl) fun hes_le hes_cap _ => ?_
      have ⟨h144, h152⟩ : (a + 136#64) + 8#64 = a + 144#64 ∧ (a + 136#64) + 16#64 = a + 152#64 :=
        ⟨by bv_omega, by bv_omega⟩
      rw [vecU8At_eq_header_sep_buf A.repAlloc (a + 136#64), vecHeader, h144, h152]
      have hes_lt : u.es.length < 2 ^ 64 := by omega
      obtain ⟨hbeqz_es, hbnez_es⟩ := ofNat_length_beq_zero_of_lt hes_lt
      cases hemp_es : u.es.isEmpty
      · simp only [hemp_es, Bool.not_false] at hbeqz_es hbnez_es
        have hne_es : u.es ≠ [] := List.isEmpty_eq_false_iff.mp hemp_es
        have henc_es : encodeBytesField 3#32 u.es =
            [0x1a#8] ++ encodeVarint (BitVec.ofNat 64 u.es.length) ++ u.es := by
          rw [etv2_encodeBytesField_3_eq, hemp_es]; simp only [Bool.false_eq_true, ↓reduceIte]
        have hfit_es : bs3.length + 1 + (encodeVarint (BitVec.ofNat 64 u.es.length)).length + u.es.length ≤ cap.toNat := by
          rw [henc_es] at hfit; dsimp only [bs3, bs2, bs1] at hfit ⊢
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
            0x1a#8 sp cap ptr ((blkPl_426).base + 5424#64) bs3 u.es hemp_es hfit_es hcap hptr halign
            (F := (((a + 136#64) ↦₆₄ g.f3.cap) ∗ ((a + 144#64) ↦₆₄ g.f3.ptr) ∗
              ((a + 152#64) ↦₆₄ BitVec.ofNat 64 u.es.length)) ∗
              vecU8Buf A.repAlloc g.f3.cap g.f3.ptr u.es ∗
              vecU8At A.repAlloc (a + 160#64) g.f4.cap g.f4.ptr u.ek ∗
              vecU8At A.repAlloc (a + 184#64) g.f5.cap g.f5.ptr u.ct1 ∗
              optAuthenticatorPBPinnedAt A.repAlloc g.auth (a + 208#64) u.auth ∗
              ((a + 256#64) ↦₆₄ u.epoch) ∗ F)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hinv_4.trans hinv5.1) (by rw [hpool5]; dsimp +zetaDelta only [bs3, bs2, bs1]; sep_ac_rfl) ?_
          intro sm5 bs_es hpcm5 hrunm5 hspm5 htrm5 hcsm5 hinv_m5 hfit_mc hcmp_mc
          rcases hcsm5 with ⟨hm5_19, hm5_20, hm5_21, hm5_22, hm5_23, hm5_24, _, _, hm5_27, _, hm5_fp, _⟩
          simp only [arm64_norm, hx19_4, hx20_4, hx27_4, hfp_4]
            at hm5_19 hm5_20 hm5_21 hm5_22 hm5_23 hm5_24 hm5_27 hm5_fp
          apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).ρ "memcpy")
          by_vm_steps
            wp_steps
            apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, wp_norm, *])
            intro hinv6
            have hpool6 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv6.2).symm
            refine etv2_step_memcpy_slice_placed A lim st H hmemcpy
              sp cap ptr g.f3.cap g.f3.ptr ((blkPl_426).base + 5464#64) bs_es u.es hemp_es hes_le halign
              (F := (((a + 136#64) ↦₆₄ g.f3.cap) ∗ ((a + 144#64) ↦₆₄ g.f3.ptr) ∗
                ((a + 152#64) ↦₆₄ BitVec.ofNat 64 u.es.length)) ∗
                vecU8At A.repAlloc (a + 160#64) g.f4.cap g.f4.ptr u.ek ∗
                vecU8At A.repAlloc (a + 184#64) g.f5.cap g.f5.ptr u.ct1 ∗
                optAuthenticatorPBPinnedAt A.repAlloc g.auth (a + 208#64) u.auth ∗
                ((a + 256#64) ↦₆₄ u.epoch) ∗ F)
              (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              hes_lt (hinv_m5.trans hinv6.1) (by rw [hpool6]; dsimp +zetaDelta only [bs_es, bs3, bs2, bs1]; sep_ac_rfl) ?_
            intro sm6 hpcm6 hrunm6 hspm6 htrm6 hcsm6 hinv_m6
            rcases hcsm6 with ⟨hm6_19, hm6_20, hm6_21, hm6_22, hm6_23, hm6_24, _, _, hm6_27, _, hm6_fp, _⟩
            simp only [arm64_norm, hm5_19, hm5_20, hm5_21, hm5_22, hm5_23, hm5_24, hm5_27, hm5_fp]
              at hm6_19 hm6_20 hm6_21 hm6_22 hm6_23 hm6_24 hm6_27 hm6_fp
            apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 5472#64)
            by_vm_steps
              wp_steps
              apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, wp_norm, *])
              intro hinv7
              have hpool7 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv7.2).symm
              have hpack_mc := vecU8At_pack_slice A.repAlloc (sp - 120#64) cap ptr bs_es u.es hfit_mc hcap hptr hne_es
              have hbs_eq : bs_es ++ u.es = bs4 := by
                dsimp only [bs4, bs_es]; rw [henc_es]; simp only [List.append_assoc]
              rw [h112, h104, hbs_eq] at hpack_mc
              refine SepWPp.weaken_pre (Entails.of_eq ?_)
                (h5472 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                  (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                  (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                  (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m6.trans hinv7.1))
              rw [vecU8At_eq_header_sep_buf A.repAlloc (a + 136#64), vecHeader, h144, h152, ← hpack_mc, hpool7]
              dsimp +zetaDelta only [bs4, bs3, bs2, bs1]; sep_ac_rfl
      · simp only [hemp_es, Bool.not_true] at hbeqz_es hbnez_es
        have henc_nil : encodeBytesField 3#32 u.es = [] := by
          rw [etv2_encodeBytesField_3_eq, hemp_es]; simp only [↓reduceIte]
        apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 5472#64)
        wp_steps
        apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv5
        have hpool5 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv5.2).symm
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (h5472 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_4.trans hinv5.1))
        rw [vecU8At_eq_header_sep_buf A.repAlloc (a + 136#64), vecHeader, h144, h152, hpool5]
        simp +zetaDelta only [bs4, bs3, bs2, bs1, henc_nil, List.append_nil]
    intro sm7 hpcm7 hrunm7 hspm7 htrm7 hx19_7 hx20_7 hx27_7 hfp_7 hinv_7
    set bs5 := bs4 ++ encodeBytesField 4#32 u.ek
    suffices h5580 : ∀ sm10 : State,
        sm10.pc = (blkPl_426).base + 5580#64 → sm10.status = .Running → sm10.sp = sp - 144#64 → sm10.trace = s0.trace →
        sm10.readReg64 .x19 = s.readReg64 .x19 → sm10.readReg64 .x20 = a →
        sm10.readReg64 .x27 = s.readReg64 .x27 → sm10.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm10 →
        SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm10
          (((vecU8At A.repAlloc (a + 136#64) g.f3.cap g.f3.ptr u.es ∗
            vecU8At A.repAlloc (a + 160#64) g.f4.cap g.f4.ptr u.ek ∗
            vecU8At A.repAlloc (a + 184#64) g.f5.cap g.f5.ptr u.ct1 ∗
            optAuthenticatorPBPinnedAt A.repAlloc g.auth (a + 208#64) u.auth ∗
            ((a + 256#64) ↦₆₄ u.epoch)) ∗
            vecU8At A.repAlloc (sp - 120#64) cap ptr bs5 ∗ A.pool lim st sm10 ∗
            stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
          Q Qp oom by
      refine sepWPp_extract_vecU8At_bounds (A := A.repAlloc) (v := a + 160#64) (cap := g.f4.cap)
        (ptr := g.f4.ptr) (bs := u.ek)
        (F := vecU8At A.repAlloc (a + 136#64) g.f3.cap g.f3.ptr u.es ∗
          vecU8At A.repAlloc (a + 184#64) g.f5.cap g.f5.ptr u.ct1 ∗
          optAuthenticatorPBPinnedAt A.repAlloc g.auth (a + 208#64) u.auth ∗
          ((a + 256#64) ↦₆₄ u.epoch) ∗
          vecU8At A.repAlloc (sp - 120#64) cap ptr bs4 ∗ A.pool lim st sm7 ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F)
        (by dsimp +zetaDelta only [bs4, bs3, bs2, bs1]; sep_ac_rfl) fun hek_le hek_cap _ => ?_
      have ⟨h168, h176⟩ : (a + 160#64) + 8#64 = a + 168#64 ∧ (a + 160#64) + 16#64 = a + 176#64 :=
        ⟨by bv_omega, by bv_omega⟩
      rw [vecU8At_eq_header_sep_buf A.repAlloc (a + 160#64), vecHeader, h168, h176]
      have hek_lt : u.ek.length < 2 ^ 64 := by omega
      obtain ⟨hbeqz_ek, hbnez_ek⟩ := ofNat_length_beq_zero_of_lt hek_lt
      cases hemp_ek : u.ek.isEmpty
      · simp only [hemp_ek, Bool.not_false] at hbeqz_ek hbnez_ek
        have hne_ek : u.ek ≠ [] := List.isEmpty_eq_false_iff.mp hemp_ek
        have henc_ek : encodeBytesField 4#32 u.ek =
            [0x22#8] ++ encodeVarint (BitVec.ofNat 64 u.ek.length) ++ u.ek := by
          rw [etv2_encodeBytesField_4_eq, hemp_ek]; simp only [Bool.false_eq_true, ↓reduceIte]
        have hfit_ek : bs4.length + 1 + (encodeVarint (BitVec.ofNat 64 u.ek.length)).length + u.ek.length ≤ cap.toNat := by
          rw [henc_ek] at hfit; dsimp only [bs4, bs3, bs2, bs1] at hfit ⊢
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
            0x22#8 sp cap ptr ((blkPl_426).base + 5532#64) bs4 u.ek hemp_ek hfit_ek hcap hptr halign
            (F := vecU8At A.repAlloc (a + 136#64) g.f3.cap g.f3.ptr u.es ∗
              (((a + 160#64) ↦₆₄ g.f4.cap) ∗ ((a + 168#64) ↦₆₄ g.f4.ptr) ∗
                ((a + 176#64) ↦₆₄ BitVec.ofNat 64 u.ek.length)) ∗
              vecU8Buf A.repAlloc g.f4.cap g.f4.ptr u.ek ∗
              vecU8At A.repAlloc (a + 184#64) g.f5.cap g.f5.ptr u.ct1 ∗
              optAuthenticatorPBPinnedAt A.repAlloc g.auth (a + 208#64) u.auth ∗
              ((a + 256#64) ↦₆₄ u.epoch) ∗ F)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hinv_7.trans hinv8.1) (by rw [hpool8]; dsimp +zetaDelta only [bs4, bs3, bs2, bs1]; sep_ac_rfl) ?_
          intro sm8 bs_ek hpcm8 hrunm8 hspm8 htrm8 hcsm8 hinv_m8 hfit_mc hcmp_mc
          rcases hcsm8 with ⟨hm8_19, hm8_20, hm8_21, hm8_22, hm8_23, hm8_24, _, _, hm8_27, _, hm8_fp, _⟩
          simp only [arm64_norm, hx19_7, hx20_7, hx27_7, hfp_7]
            at hm8_19 hm8_20 hm8_21 hm8_22 hm8_23 hm8_24 hm8_27 hm8_fp
          apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).ρ "memcpy")
          by_vm_steps
            wp_steps
            apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, wp_norm, *])
            intro hinv9
            have hpool9 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv9.2).symm
            refine etv2_step_memcpy_slice_placed A lim st H hmemcpy
              sp cap ptr g.f4.cap g.f4.ptr ((blkPl_426).base + 5572#64) bs_ek u.ek hemp_ek hek_le halign
              (F := vecU8At A.repAlloc (a + 136#64) g.f3.cap g.f3.ptr u.es ∗
                (((a + 160#64) ↦₆₄ g.f4.cap) ∗ ((a + 168#64) ↦₆₄ g.f4.ptr) ∗
                  ((a + 176#64) ↦₆₄ BitVec.ofNat 64 u.ek.length)) ∗
                vecU8At A.repAlloc (a + 184#64) g.f5.cap g.f5.ptr u.ct1 ∗
                optAuthenticatorPBPinnedAt A.repAlloc g.auth (a + 208#64) u.auth ∗
                ((a + 256#64) ↦₆₄ u.epoch) ∗ F)
              (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              hek_lt (hinv_m8.trans hinv9.1) (by rw [hpool9]; dsimp +zetaDelta only [bs_ek, bs4, bs3, bs2, bs1]; sep_ac_rfl) ?_
            intro sm9 hpcm9 hrunm9 hspm9 htrm9 hcsm9 hinv_m9
            rcases hcsm9 with ⟨hm9_19, hm9_20, hm9_21, hm9_22, hm9_23, hm9_24, _, _, hm9_27, _, hm9_fp, _⟩
            simp only [arm64_norm, hm8_19, hm8_20, hm8_21, hm8_22, hm8_23, hm8_24, hm8_27, hm8_fp]
              at hm9_19 hm9_20 hm9_21 hm9_22 hm9_23 hm9_24 hm9_27 hm9_fp
            apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 5580#64)
            by_vm_steps
              wp_steps
              apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, wp_norm, *])
              intro hinv10
              have hpool10 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv10.2).symm
              have hpack_mc := vecU8At_pack_slice A.repAlloc (sp - 120#64) cap ptr bs_ek u.ek hfit_mc hcap hptr hne_ek
              have hbs_eq : bs_ek ++ u.ek = bs5 := by
                dsimp only [bs5, bs_ek]; rw [henc_ek]; simp only [List.append_assoc]
              rw [h112, h104, hbs_eq] at hpack_mc
              refine SepWPp.weaken_pre (Entails.of_eq ?_)
                (h5580 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                  (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                  (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                  (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m9.trans hinv10.1))
              rw [vecU8At_eq_header_sep_buf A.repAlloc (a + 160#64), vecHeader, h168, h176, ← hpack_mc, hpool10]
              dsimp +zetaDelta only [bs5, bs4, bs3, bs2, bs1]; sep_ac_rfl
      · simp only [hemp_ek, Bool.not_true] at hbeqz_ek hbnez_ek
        have henc_nil : encodeBytesField 4#32 u.ek = [] := by
          rw [etv2_encodeBytesField_4_eq, hemp_ek]; simp only [↓reduceIte]
        apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 5580#64)
        wp_steps
        apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv8
        have hpool8 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv8.2).symm
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (h5580 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_7.trans hinv8.1))
        rw [vecU8At_eq_header_sep_buf A.repAlloc (a + 160#64), vecHeader, h168, h176, hpool8]
        simp +zetaDelta only [bs5, bs4, bs3, bs2, bs1, henc_nil, List.append_nil]
    intro sm10 hpcm10 hrunm10 hspm10 htrm10 hx19_10 hx20_10 hx27_10 hfp_10 hinv_10
    refine sepWPp_extract_vecU8At_bounds (A := A.repAlloc) (v := a + 184#64) (cap := g.f5.cap)
      (ptr := g.f5.ptr) (bs := u.ct1)
      (F := vecU8At A.repAlloc (a + 136#64) g.f3.cap g.f3.ptr u.es ∗
        vecU8At A.repAlloc (a + 160#64) g.f4.cap g.f4.ptr u.ek ∗
        optAuthenticatorPBPinnedAt A.repAlloc g.auth (a + 208#64) u.auth ∗
        ((a + 256#64) ↦₆₄ u.epoch) ∗
        vecU8At A.repAlloc (sp - 120#64) cap ptr bs5 ∗ A.pool lim st sm10 ∗
        stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F)
      (by dsimp +zetaDelta only [bs5, bs4, bs3, bs2, bs1]; sep_ac_rfl) fun hct1_le hct1_cap _ => ?_
    have ⟨h192, h200⟩ : (a + 184#64) + 8#64 = a + 192#64 ∧ (a + 184#64) + 16#64 = a + 200#64 :=
      ⟨by bv_omega, by bv_omega⟩
    rw [vecU8At_eq_header_sep_buf A.repAlloc (a + 184#64), vecHeader, h192, h200]
    have hct1_lt : u.ct1.length < 2 ^ 64 := by omega
    obtain ⟨hbeqz_ct1, hbnez_ct1⟩ := ofNat_length_beq_zero_of_lt hct1_lt
    cases hemp_ct1 : u.ct1.isEmpty
    · simp only [hemp_ct1, Bool.not_false] at hbeqz_ct1 hbnez_ct1
      have hne_ct1 : u.ct1 ≠ [] := List.isEmpty_eq_false_iff.mp hemp_ct1
      have henc_ct1 : encodeBytesField 5#32 u.ct1 =
          [0x2a#8] ++ encodeVarint (BitVec.ofNat 64 u.ct1.length) ++ u.ct1 := by
        rw [etv3_encodeBytesField_5_eq, hemp_ct1]; simp only [Bool.false_eq_true, ↓reduceIte]
      have hfit_ct1 : bs5.length + 1 + (encodeVarint (BitVec.ofNat 64 u.ct1.length)).length + u.ct1.length ≤ cap.toNat := by
        rw [henc_ct1] at hfit; dsimp only [bs5, bs4, bs3, bs2, bs1] at hfit ⊢
        simp only [List.length_append, List.length_singleton] at hfit ⊢; omega
      have hlt_tag : bs5.length < cap.toNat := by omega
      have hcmp_tag := cap_beq_len_false_of_lt hlt_tag hcap
      rw [vecU8At_expose_one A.repAlloc (sp - 120#64) cap ptr bs5 hlt_tag hcap hptr, h112, h104]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPp.exists_elim fun b4 => ?_
      apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 292)
      by_vm_steps
        wp_steps
        apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv11
        have hpool11 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv11.2).symm
        refine etv3_step_bytes_varint_placed A lim st H hvarint
          0x2a#8 sp cap ptr ((blkPl_426).base + 5640#64) bs5 u.ct1 hemp_ct1 hfit_ct1 hcap hptr halign
          (F := vecU8At A.repAlloc (a + 136#64) g.f3.cap g.f3.ptr u.es ∗
            vecU8At A.repAlloc (a + 160#64) g.f4.cap g.f4.ptr u.ek ∗
            (((a + 184#64) ↦₆₄ g.f5.cap) ∗ ((a + 192#64) ↦₆₄ g.f5.ptr) ∗
              ((a + 200#64) ↦₆₄ BitVec.ofNat 64 u.ct1.length)) ∗
            vecU8Buf A.repAlloc g.f5.cap g.f5.ptr u.ct1 ∗
            optAuthenticatorPBPinnedAt A.repAlloc g.auth (a + 208#64) u.auth ∗
            ((a + 256#64) ↦₆₄ u.epoch) ∗ F)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hinv_10.trans hinv11.1) (by rw [hpool11]; dsimp +zetaDelta only [bs5, bs4, bs3, bs2, bs1]; sep_ac_rfl) ?_
        intro sm11 bs_ct1 hpcm11 hrunm11 hspm11 htrm11 hcsm11 hinv_m11 hfit_mc hcmp_mc
        rcases hcsm11 with ⟨hm11_19, hm11_20, hm11_21, hm11_22, hm11_23, hm11_24, _, _, hm11_27, _, hm11_fp, _⟩
        simp only [arm64_norm, hx19_10, hx20_10, hx27_10, hfp_10]
          at hm11_19 hm11_20 hm11_21 hm11_22 hm11_23 hm11_24 hm11_27 hm11_fp
        apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).ρ "memcpy")
        by_vm_steps
          wp_steps
          apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, wp_norm, *])
          intro hinv12
          have hpool12 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv12.2).symm
          refine etv2_step_memcpy_slice_placed A lim st H hmemcpy
            sp cap ptr g.f5.cap g.f5.ptr ((blkPl_426).base + 5680#64) bs_ct1 u.ct1 hemp_ct1 hct1_le halign
            (F := vecU8At A.repAlloc (a + 136#64) g.f3.cap g.f3.ptr u.es ∗
              vecU8At A.repAlloc (a + 160#64) g.f4.cap g.f4.ptr u.ek ∗
              (((a + 184#64) ↦₆₄ g.f5.cap) ∗ ((a + 192#64) ↦₆₄ g.f5.ptr) ∗
                ((a + 200#64) ↦₆₄ BitVec.ofNat 64 u.ct1.length)) ∗
              optAuthenticatorPBPinnedAt A.repAlloc g.auth (a + 208#64) u.auth ∗
              ((a + 256#64) ↦₆₄ u.epoch) ∗ F)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            hct1_lt (hinv_m11.trans hinv12.1) (by rw [hpool12]; dsimp +zetaDelta only [bs_ct1, bs5, bs4, bs3, bs2, bs1]; sep_ac_rfl) ?_
          intro sm12 hpcm12 hrunm12 hspm12 htrm12 hcsm12 hinv_m12
          rcases hcsm12 with ⟨hm12_19, hm12_20, hm12_21, hm12_22, hm12_23, hm12_24, _, _, hm12_27, _, hm12_fp, _⟩
          simp only [arm64_norm, hm11_19, hm11_20, hm11_21, hm11_22, hm11_23, hm11_24, hm11_27, hm11_fp]
            at hm12_19 hm12_20 hm12_21 hm12_22 hm12_23 hm12_24 hm12_27 hm12_fp
          apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 5688#64)
          by_vm_steps
            wp_steps
            apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, wp_norm, *])
            intro hinv13
            have hpool13 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv13.2).symm
            have hpack_mc := vecU8At_pack_slice A.repAlloc (sp - 120#64) cap ptr bs_ct1 u.ct1 hfit_mc hcap hptr hne_ct1
            have hbs_eq : bs_ct1 ++ u.ct1 = bs ++ encodeOptMessage V1State.Unchunked.Ct1SentEkReceived.encodeRaw 1#32 (some u) := by
              rw [etv3_encodeOptCt1SentEkReceived_some_eq, henc_ct1]
              dsimp only [bs_ct1, bs5, bs4, bs3, bs2, bs1]; simp only [List.append_assoc]
            rw [h112, h104, hbs_eq] at hpack_mc
            refine SepWPp.weaken_pre (Entails.of_eq ?_)
              (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m12.trans hinv13.1))
            dsimp only [ct1SentEkReceivedPBPinnedAt, unchunked5PinnedAt]
            rw [h136_24, h136_48, h136_72, h136_120, vecU8At_eq_header_sep_buf A.repAlloc (a + 184#64), vecHeader,
              h192, h200, ← hpack_mc, hpool13]; sep_ac_rfl
    · simp only [hemp_ct1, Bool.not_true] at hbeqz_ct1 hbnez_ct1
      have henc_nil : encodeBytesField 5#32 u.ct1 = [] := by
        rw [etv3_encodeBytesField_5_eq, hemp_ct1]; simp only [↓reduceIte]
      apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 5688#64)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv11
      have hpool11 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv11.2).symm
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_10.trans hinv11.1))
      dsimp only [ct1SentEkReceivedPBPinnedAt, unchunked5PinnedAt]
      rw [h136_24, h136_48, h136_72, h136_120, vecU8At_eq_header_sep_buf A.repAlloc (a + 184#64), vecHeader,
        h192, h200, etv3_encodeOptCt1SentEkReceived_some_eq, henc_nil, hpool11]
      dsimp only [bs5, bs4, bs3, bs2, bs1]; simp only [List.append_nil, List.append_assoc]

theorem step_encodeToVec_v1_ekReceivedCt1Sampled_placed [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (H : String → Option (State → State)) {s0 s : State}
    (hct1Len : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 387)
      (withStepInv s0 (leafEncLen16Spec (ct1SentEkReceivedPBPinnedAt A.repAlloc) ct1SentEkReceivedPBEncodedLen)))
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
    (a sp cap ptr : BitVec 64) (g : Unchunked5PBGhost × PolynomialEncoderPBGhost)
    (v : V1State.Chunked.EkReceivedCt1Sampled) (bs : List (BitVec 8))
    (hv_len : v1StatePBEncodedLen ⟨some (.ekReceivedCt1Sampled v)⟩ < 2 ^ 64)
    (hfit : bs.length + (V1State.InnerState.encode (.ekReceivedCt1Sampled v)).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_426).base + 3068#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = a) (hinv0 : StepInv s0 s)
    (hP : P = ((optCt1SentEkReceivedPBPinnedAt A.repAlloc g.1 (a + 136#64) v.uc ∗
      optPolynomialEncoderPBPinnedAt A.repAlloc g.2 (a + 264#64) v.sendingCt1) ∗
      vecU8At A.repAlloc (sp - 120#64) cap ptr bs ∗ A.pool lim st s ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_426).base + 1808#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm
        (((optCt1SentEkReceivedPBPinnedAt A.repAlloc g.1 (a + 136#64) v.uc ∗
          optPolynomialEncoderPBPinnedAt A.repAlloc g.2 (a + 264#64) v.sendingCt1) ∗
          vecU8At A.repAlloc (sp - 120#64) cap ptr (bs ++ V1State.InnerState.encode (.ekReceivedCt1Sampled v)) ∗
          A.pool lim st sm ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q Qp oom := by
  subst hP
  rcases v with ⟨uc, sendingCt1⟩
  rw [etv3_encodeInnerState_ekReceivedCt1Sampled_eq] at hfit
  simp only [List.length_append, List.length_singleton] at hfit
  have hsub_len : v1StateInnerPayloadEncodedLen (.ekReceivedCt1Sampled ⟨uc, sendingCt1⟩) < 2 ^ 64 := by
    dsimp only [v1StatePBEncodedLen] at hv_len; omega
  have hlt1 : bs.length < cap.toNat := by omega
  have hfit_var : (bs ++ [0x4a#8]).length +
      (encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ekReceivedCt1Sampled ⟨uc, sendingCt1⟩)))).length ≤
      cap.toNat := by
    simp only [List.length_append, List.length_singleton]; omega
  refine sepWPp_extract_vecU8At_bounds (v := sp - 120#64) (cap := cap) (ptr := ptr) (bs := bs)
    (F := optCt1SentEkReceivedPBPinnedAt A.repAlloc g.1 (a + 136#64) uc ∗
      optPolynomialEncoderPBPinnedAt A.repAlloc g.2 (a + 264#64) sendingCt1 ∗ A.pool lim st s ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F)
    (by sep_ac_rfl) fun _ hcap hptr => ?_
  refine sepWPp_extract_pure
    (((optCt1SentEkReceivedCap g.1 uc + 1#64 == 0#64) = !uc.isSome ∧
      (optCt1SentEkReceivedCap g.1 uc + 1#64 != 0#64) = uc.isSome) ∧
     ((optPolyEncCap g.2 sendingCt1 + 1#64 == 0#64) = !sendingCt1.isSome ∧
      (optPolyEncCap g.2 sendingCt1 + 1#64 != 0#64) = sendingCt1.isSome))
    (fun R' hm =>
      ⟨optCt1SentEkReceivedPBPinnedAt_cap_bounds (p := a + 136#64)
        (R := optPolynomialEncoderPBPinnedAt A.repAlloc g.2 (a + 264#64) sendingCt1 ∗
          vecU8At A.repAlloc (sp - 120#64) cap ptr bs ∗ A.pool lim st s ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm),
       optPolynomialEncoderPBPinnedAt_cap_bounds (p := a + 264#64)
        (R := optCt1SentEkReceivedPBPinnedAt A.repAlloc g.1 (a + 136#64) uc ∗
          vecU8At A.repAlloc (sp - 120#64) cap ptr bs ∗ A.pool lim st s ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm)⟩)
    fun ⟨⟨hcap_uc_beq, hcap_uc_bne⟩, ⟨hcap_enc_beq, hcap_enc_bne⟩⟩ => ?_
  have hbeq_false := cap_beq_len_false_of_lt hlt1 hcap
  have ⟨h112, h104⟩ : (sp - 120#64) + 8#64 = sp - 112#64 ∧ (sp - 120#64) + 16#64 = sp - 104#64 :=
    ⟨by bv_omega, by bv_omega⟩
  have hpack := vecU8At_pack_one A.repAlloc (sp - 120#64) cap ptr bs 0x4a#8 hlt1 hcap hptr
  rw [h112, h104] at hpack
  suffices h3936 : ∀ sm1 : State,
      sm1.pc = (blkPl_426).base + 3936#64 → sm1.status = .Running → sm1.sp = sp - 144#64 → sm1.trace = s0.trace →
      sm1.readReg64 .x20 = a → sm1.readReg64 .x21 = optCt1SentEkReceivedCap g.1 uc →
      sm1.readReg64 .x22 = BitVec.ofNat 64 (optCt1SentEkReceivedPBFieldEncodedLen uc) →
      sm1.readReg64 .x27 = s.readReg64 .x27 → sm1.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm1 →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm1
        (((optCt1SentEkReceivedPBPinnedAt A.repAlloc g.1 (a + 136#64) uc ∗
          optPolynomialEncoderPBPinnedAt A.repAlloc g.2 (a + 264#64) sendingCt1) ∗
          vecU8At A.repAlloc (sp - 120#64) cap ptr (bs ++ [0x4a#8]) ∗ A.pool lim st sm1 ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom by
    rw [vecU8At_expose_one A.repAlloc (sp - 120#64) cap ptr bs hlt1 hcap hptr, h112, h104]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun b0 => ?_
    cases uc with
    | none =>
      rw [optCt1SentEkReceivedPBPinnedAt_eq A.repAlloc g.1 (a + 136#64) none]
      simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
      apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 3936#64)
      by_vm_steps
        wp_steps
        apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv1
        have hpool1 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv1.2).symm
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (h3936 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [optCt1SentEkReceivedPBFieldEncodedLen, arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1.1))
        rw [← optCt1SentEkReceivedPBPinnedAt_eq A.repAlloc g.1 (a + 136#64) none, ← hpack, hpool1]
    | some u =>
      rw [optCt1SentEkReceivedPBPinnedAt_eq A.repAlloc g.1 (a + 136#64) (some u)]
      simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      have ⟨hu_fit, hopt_u_lt⟩ :
          ct1SentEkReceivedPBEncodedLen u < 2 ^ 64 ∧ optCt1SentEkReceivedPBFieldEncodedLen (some u) < 2 ^ 64 :=
        ⟨by dsimp only [v1StateInnerPayloadEncodedLen, optCt1SentEkReceivedPBFieldEncodedLen] at hsub_len; omega,
         by dsimp only [v1StateInnerPayloadEncodedLen] at hsub_len; omega⟩
      have hvar_u_lt : varintLen (BitVec.ofNat 64 (ct1SentEkReceivedPBEncodedLen u)) <
          optCt1SentEkReceivedPBFieldEncodedLen (some u) := by
        dsimp only [optCt1SentEkReceivedPBFieldEncodedLen]; omega
      have ⟨⟨hu1, hu2, hu3, hu4, hu5⟩, hult_u, hopt_u_eq⟩ :=
        (⟨cmp_ls_false_of_lt hvar_u_lt hopt_u_lt, ult_of_lt_of_fit hvar_u_lt hopt_u_lt,
          etv3_bv_optCt1SentEkReceived_some_eq u⟩ : _ ∧ _ ∧ _)
      apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 387)
      by_vm_steps
        wp_steps
        apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv1
        rw [← optCt1SentEkReceivedPBPinnedAt_eq A.repAlloc g.1 (a + 136#64) (some u)]
        refine step_etv_leaf_encLen16_call_placed hres (ct1SentEkReceivedPBPinnedAt A.repAlloc)
          ct1SentEkReceivedPBEncodedLen hct1Len
          (a + 136#64) sp ((blkPl_426).base + 3124#64) g.1 u hu_fit
          (F := optPolynomialEncoderPBPinnedAt A.repAlloc g.2 (a + 264#64) sendingCt1 ∗
            vecU8At A.repAlloc (sp - 120#64) cap ptr (bs ++ [0x4a#8]) ∗ A.pool lim st s ∗ F)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
          (hinv0.trans hinv1.1)
          (by rw [← hpack]; dsimp only [optCt1SentEkReceivedPBPinnedAt]; sep_ac_rfl) ?_
        intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1 hcsm1 hinv_m1 hvm_m1
        rcases hcsm1 with ⟨_, hm20, hm21, _, _, _, _, _, hm27, _, hmfp, _⟩
        simp only [arm64_norm, hx20] at hm20 hm21 hm27 hmfp
        apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 3936#64)
        wp_steps
        apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv2
        have hpool12 := (A.pool_of_vmPreserved (lim := lim) (st := st) (hinv1.2.trans (hvm_m1.trans hinv2.2))).symm
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (h3936 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (hinv_m1.trans hinv2.1))
        rw [hpool12]; dsimp only [optCt1SentEkReceivedPBPinnedAt]; sep_ac_rfl
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx20_1 hx21_1 hx22_1 hx27_1 hfp_1 hinv_1
  suffices h5212 : ∀ sm2 : State,
      sm2.pc = (blkPl_426).base + 5212#64 → sm2.status = .Running → sm2.sp = sp - 144#64 → sm2.trace = s0.trace →
      sm2.readReg64 .x8 = BitVec.ofNat 64 (optPolynomialEncoderPBFieldEncodedLen sendingCt1) →
      sm2.readReg64 .x19 = optPolyEncCap g.2 sendingCt1 → sm2.readReg64 .x20 = a →
      sm2.readReg64 .x21 = optCt1SentEkReceivedCap g.1 uc →
      sm2.readReg64 .x22 = BitVec.ofNat 64 (optCt1SentEkReceivedPBFieldEncodedLen uc) →
      sm2.readReg64 .x27 = s.readReg64 .x27 → sm2.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm2 →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm2
        (((optCt1SentEkReceivedPBPinnedAt A.repAlloc g.1 (a + 136#64) uc ∗
          optPolynomialEncoderPBPinnedAt A.repAlloc g.2 (a + 264#64) sendingCt1) ∗
          vecU8At A.repAlloc (sp - 120#64) cap ptr (bs ++ [0x4a#8]) ∗ A.pool lim st sm2 ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom by
    cases sendingCt1 with
    | none =>
      rw [optPolynomialEncoderPBPinnedAt_eq A.repAlloc g.2 (a + 264#64) none]
      simp only [Option.isSome_none, Bool.not_false] at hcap_enc_beq hcap_enc_bne
      apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 5212#64)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv2
      have hpool2 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv2.2).symm
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h5212 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [optPolynomialEncoderPBFieldEncodedLen, arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_1.trans hinv2.1))
      rw [← optPolynomialEncoderPBPinnedAt_eq A.repAlloc g.2 (a + 264#64) none, hpool2]
    | some enc =>
      rw [optPolynomialEncoderPBPinnedAt_eq A.repAlloc g.2 (a + 264#64) (some enc)]
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
      rw [← optPolynomialEncoderPBPinnedAt_eq A.repAlloc g.2 (a + 264#64) (some enc)]
      refine step_etv_leaf_encLen16_call_placed hres (polynomialEncoderPBPinnedAt A.repAlloc)
        polynomialEncoderPBEncodedLen hpolyEncLen
        (a + 264#64) sp ((blkPl_426).base + 3956#64) g.2 enc henc_fit
        (F := optCt1SentEkReceivedPBPinnedAt A.repAlloc g.1 (a + 136#64) uc ∗
          vecU8At A.repAlloc (sp - 120#64) cap ptr (bs ++ [0x4a#8]) ∗ A.pool lim st sm1 ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (hinv_1.trans hinv2.1)
        (by dsimp only [optPolynomialEncoderPBPinnedAt]; sep_ac_rfl) ?_
      intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx0m2 hcsm2 hinv_m2 hvm_m2
      rcases hcsm2 with ⟨hm2_19, hm2_20, hm2_21, hm2_22, _, _, _, _, hm2_27, _, hm2_fp, _⟩
      simp only [arm64_norm, hx20_1, hx21_1, hx22_1, hx27_1, hfp_1]
        at hm2_19 hm2_20 hm2_21 hm2_22 hm2_27 hm2_fp
      apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 5212#64)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv3
      have hpool23 := (A.pool_of_vmPreserved (lim := lim) (st := st) (hinv2.2.trans (hvm_m2.trans hinv3.2))).symm
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h5212 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (hinv_m2.trans hinv3.1))
      rw [hpool23]; dsimp only [optPolynomialEncoderPBPinnedAt]; sep_ac_rfl
  intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx8_2 hx19_2 hx20_2 hx21_2 hx22_2 hx27_2 hfp_2 hinv_2
  have ⟨hadd_sum, hult_sum, hule_sum, hult_sum2, hule_sum2⟩ := adds_no_overflow_of_eq
      (a := optPolynomialEncoderPBFieldEncodedLen sendingCt1)
      (b := optCt1SentEkReceivedPBFieldEncodedLen uc)
      (c := v1StateInnerPayloadEncodedLen (.ekReceivedCt1Sampled ⟨uc, sendingCt1⟩)) rfl hsub_len
  apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 292)
  wp_steps
  apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, wp_norm, *])
  intro hinv3
  have hpool3 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv3.2).symm
  set bs1 := (bs ++ [0x4a#8]) ++
    encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ekReceivedCt1Sampled ⟨uc, sendingCt1⟩)))
  refine step_etv_encode_varint_call_prog A lim st hvarint
    (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ekReceivedCt1Sampled ⟨uc, sendingCt1⟩)))
    (sp - 120#64) cap ptr sp ((blkPl_426).base + 5228#64) (bs ++ [0x4a#8]) hfit_var
    (F := (optCt1SentEkReceivedPBPinnedAt A.repAlloc g.1 (a + 136#64) uc ∗
      optPolynomialEncoderPBPinnedAt A.repAlloc g.2 (a + 264#64) sendingCt1) ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hinv_2.trans hinv3.1) (by rw [hpool3]; sep_ac_rfl) ?_
  intro sm3 hpcm3 hrunm3 hspm3 htrm3 hcsm3 hinv_m3
  rcases hcsm3 with ⟨hm3_19, hm3_20, hm3_21, _, _, _, _, _, hm3_27, _, hm3_fp, _⟩
  simp only [arm64_norm, hx19_2, hx20_2, hx21_2, hx27_2, hfp_2]
    at hm3_19 hm3_20 hm3_21 hm3_27 hm3_fp
  set bs2 := bs1 ++ encodeOptMessage V1State.Unchunked.Ct1SentEkReceived.encodeRaw 1#32 uc
  suffices h5688 : ∀ sm4 : State,
      sm4.pc = (blkPl_426).base + 5688#64 → sm4.status = .Running → sm4.sp = sp - 144#64 → sm4.trace = s0.trace →
      sm4.readReg64 .x19 = optPolyEncCap g.2 sendingCt1 → sm4.readReg64 .x20 = a →
      sm4.readReg64 .x27 = s.readReg64 .x27 → sm4.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm4 →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm4
        (((optCt1SentEkReceivedPBPinnedAt A.repAlloc g.1 (a + 136#64) uc ∗
          optPolynomialEncoderPBPinnedAt A.repAlloc g.2 (a + 264#64) sendingCt1) ∗
          vecU8At A.repAlloc (sp - 120#64) cap ptr bs2 ∗ A.pool lim st sm4 ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom by
    cases uc with
    | none =>
      simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
      apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 5688#64)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv4
      have hpool4 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv4.2).symm
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h5688 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m3.trans hinv4.1))
      rw [hpool4]; simp +zetaDelta only [bs2, bs1, encodeOptMessage, List.append_nil]; sep_ac_rfl
    | some u =>
      simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      have hu_lt : ct1SentEkReceivedPBEncodedLen u < 2 ^ 64 := by
        dsimp only [v1StateInnerPayloadEncodedLen, optCt1SentEkReceivedPBFieldEncodedLen] at hsub_len; omega
      have hfit_u : bs1.length + (encodeOptMessage V1State.Unchunked.Ct1SentEkReceived.encodeRaw 1#32 (some u)).length ≤ cap.toNat := by
        dsimp only [bs1]; simp only [List.length_append, List.length_singleton] at hfit ⊢; omega
      apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 5236#64)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv4
      have hpool4 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv4.2).symm
      refine etv3_step_ekReceivedCt1Sampled_some_placed hres A lim st H hct1Len hvarint hauthEnc hmemcpy
        a sp cap ptr g.1 u bs1 hu_lt hfit_u hcap hptr halign
        (F := optPolynomialEncoderPBPinnedAt A.repAlloc g.2 (a + 264#64) sendingCt1 ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hinv_m3.trans hinv4.1)
        (by rw [hpool4]; dsimp +zetaDelta only [bs1, optCt1SentEkReceivedPBPinnedAt]; simp only [List.append_assoc]; sep_ac_rfl) ?_
      intro sm4 hpcm4 hrunm4 hspm4 htrm4 hm4_19 hm4_20 hm4_27 hm4_fp hinv_m4
      simp only [arm64_norm, hm3_19, hm3_27, hm3_fp]
        at hm4_19 hm4_27 hm4_fp
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h5688 sm4 hpcm4 hrunm4 hspm4 htrm4 hm4_19 hm4_20 hm4_27 hm4_fp hinv_m4)
      dsimp only [bs2, optCt1SentEkReceivedPBPinnedAt]; sep_ac_rfl
  intro sm4 hpcm4 hrunm4 hspm4 htrm4 hx19_4 hx20_4 hx27_4 hfp_4 hinv_4
  cases sendingCt1 with
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
    rw [etv3_encodeInnerState_ekReceivedCt1Sampled_eq, hpool5]
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
      (a + 264#64) sp cap ptr g.2 enc bs2 hfit_enc halign
      (F := optCt1SentEkReceivedPBPinnedAt A.repAlloc g.1 (a + 136#64) uc ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hinv_4.trans hinv5.1)
      (by rw [hpool5]; dsimp +zetaDelta only [bs2, bs1, optPolynomialEncoderPBPinnedAt]; sep_ac_rfl) ?_
    intro sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_27 hm5_fp hinv_m5
    simp only [arm64_norm, hx27_4, hfp_4] at hm5_27 hm5_fp
    refine SepWPp.weaken_pre (Entails.of_eq ?_)
      (hnext sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_27 hm5_fp hinv_m5)
    rw [etv3_encodeInnerState_ekReceivedCt1Sampled_eq]
    simp +zetaDelta only [bs2, bs1, encodeOptMessage,
      optPolynomialEncoderPBPinnedAt, List.append_assoc]; sep_ac_rfl

end LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked3PlacedBudget

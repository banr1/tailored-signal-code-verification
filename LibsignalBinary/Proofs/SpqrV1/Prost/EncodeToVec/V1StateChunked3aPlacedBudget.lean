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
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked3aPlaced
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.ProtoReprCodeSym
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `[LibsignalPlacement]` Phase 2c (Part 3a): `V1State::encode_raw` Variants `idx = 10, 6` (`Block 426`)

Re-exports `etv3_step_bytes_varint_placed` and `idx = 10` (`.ct2Sampled`) from
`V1StateChunked3aPlacedBudgetAux`, and proves `etv3_step_headerReceived_some_placed` (`+4944 .. +5180`)
and `step_encodeToVec_v1_headerReceived_placed` (`idx = 6`, `+2908 .. +1808`), threading `A.pool lim st`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked3aPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.RustHeap (RustAlloc vecHeader vecU8At)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalSpqrV1
  (PolynomialDecoder ProtoAuthenticator V1State)
open CryptoVerification.LibsignalSpqrV1.Proto
  (encodeBytesField encodeMessage encodeOptMessage encodeUint64Field encodeVarint)
open CryptoVerification.SpqrV1.ProtoRepr
  (PolynomialDecoderPBGhost Unchunked3PBGhost
   headerReceivedPBEncodedLen headerReceivedPBPinnedAt
   noneCap2 optAuthCap optAuthenticatorPBPinnedAt optAuthenticatorPBPinnedAt_eq
   optHeaderReceivedPBFieldEncodedLen optHeaderReceivedPBPinnedAt
   optPolynomialDecoderPBFieldEncodedLen optPolynomialDecoderPBPinnedAt
   polynomialDecoderPBEncodedLen polynomialDecoderPBPinnedAt
   unchunked3PinnedAt v1StateInnerPayloadEncodedLen v1StatePBEncodedLen varintLen)
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
   bv_optPolyDec_some_eq
   cap_beq_len_false_of_lt
   encodeToVecCalleeStackOf encodeVarint_length_pos
   etv2_encodeBytesField_3_eq etv2_encodeUint64Field_1_eq etv2_optAuth_cap_bounds
   etv3_bv_optHeaderReceived_some_eq
   etv3_encodeInnerState_headerReceived_eq
   etv3_encodeOptHeaderReceived_some_eq
   noneCap2_add_two_beq_zero noneCap2_add_two_bne_zero
   noneCap3 noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
   noneCap_add_two_beq_zero noneCap_add_two_bne_zero
   optHeaderReceivedCap optHeaderReceivedPBPinnedAt_cap_bounds optHeaderReceivedPBPinnedAt_eq
   optPolyDecCap
   optPolynomialDecoderPBPinnedAt_cap_bounds optPolynomialDecoderPBPinnedAt_eq
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
  (etvPolyDecoderBudgetExactSpecOf step_etv_leaf_encLen16_call_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked1PlacedBudgetAux
  (sepWPp_extract_pure sepWPp_extract_vecU8At_bounds step_encodeToVec_tail_5196_polyDec_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked2PlacedBudgetAux
  (etv2_step_memcpy_slice_placed)

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

/-! ## 1. Re-Exports from `V1StateChunked3aPlacedBudgetAux` -/

abbrev etv3_step_bytes_varint_placed :=
  @V1StateChunked3aPlacedBudgetAux.etv3_step_bytes_varint_placed

abbrev step_encodeToVec_v1_ct2Sampled_placed :=
  @V1StateChunked3aPlacedBudgetAux.step_encodeToVec_v1_ct2Sampled_placed

/-! ## 2. Variant `idx = 6`: `.headerReceived` (`+2908 .. +5208`) -/

/-- Step `+4944 .. +5180` (`Block 426`): inline encoding of `u : HeaderReceived` at `a + 136#64`,
threading `A.pool lim st`. -/
theorem etv3_step_headerReceived_some_placed [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (H : String → Option (State → State)) {s0 s : State}
    (hhrLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 404)
      (withStepInv s0 (leafEncLen16Spec (headerReceivedPBPinnedAt A.repAlloc) headerReceivedPBEncodedLen)))
    (hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hauthEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 314)
      (withStepInv s0 (authEncodeExactSpecOf resStack A lim)))
    (hmemcpy : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      ((blkPl_426).ρ "memcpy") etvMemcpyRegionSpec)
    (a sp cap ptr : BitVec 64) (g : Unchunked3PBGhost) (u : V1State.Unchunked.HeaderReceived)
    (bs : List (BitVec 8))
    (hu_lt : headerReceivedPBEncodedLen u < 2 ^ 64)
    (hfit : bs.length + (encodeOptMessage V1State.Unchunked.HeaderReceived.encodeRaw 1#32 (some u)).length ≤ cap.toNat)
    (hcap : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0) (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_426).base + 4944#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = a) (hinv0 : StepInv s0 s)
    (hP : P = (headerReceivedPBPinnedAt A.repAlloc g (a + 136#64) u ∗
      vecU8At A.repAlloc (sp - 120#64) cap ptr bs ∗ A.pool lim st s ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_426).base + 5180#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm
        ((headerReceivedPBPinnedAt A.repAlloc g (a + 136#64) u ∗
          vecU8At A.repAlloc (sp - 120#64) cap ptr
            (bs ++ encodeOptMessage V1State.Unchunked.HeaderReceived.encodeRaw 1#32 (some u)) ∗
          A.pool lim st sm ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q Qp oom := by
  subst hP
  have ⟨h112, h104⟩ : (sp - 120#64) + 8#64 = sp - 112#64 ∧ (sp - 120#64) + 16#64 = sp - 104#64 :=
    ⟨by bv_omega, by bv_omega⟩
  rw [etv3_encodeOptHeaderReceived_some_eq] at hfit
  simp only [List.length_append, List.length_singleton] at hfit
  have hlt1 : bs.length < cap.toNat := by omega
  have hbeq1 := cap_beq_len_false_of_lt hlt1 hcap
  rw [vecU8At_expose_one A.repAlloc (sp - 120#64) cap ptr bs hlt1 hcap hptr, h112, h104]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun b0 => ?_
  apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 404)
  by_vm_steps
    wp_steps
    apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv1
    have hpack1 := vecU8At_pack_one A.repAlloc (sp - 120#64) cap ptr bs 0x0a#8 hlt1 hcap hptr
    rw [h112, h104] at hpack1
    refine step_etv_leaf_encLen16_call_placed hres (headerReceivedPBPinnedAt A.repAlloc)
      headerReceivedPBEncodedLen hhrLen
      (a + 136#64) sp ((blkPl_426).base + 4988#64) g u hu_lt
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
    set bs1 := (bs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 (headerReceivedPBEncodedLen u))
    have hfit_var : (bs ++ [0x0a#8]).length +
        (encodeVarint (BitVec.ofNat 64 (headerReceivedPBEncodedLen u))).length ≤ cap.toNat := by
      simp only [List.length_append, List.length_singleton]; omega
    refine step_etv_encode_varint_call_prog A lim st hvarint
      (BitVec.ofNat 64 (headerReceivedPBEncodedLen u))
      (sp - 120#64) cap ptr sp ((blkPl_426).base + 4996#64) (bs ++ [0x0a#8]) hfit_var
      (F := headerReceivedPBPinnedAt A.repAlloc g (a + 136#64) u ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hinv_m1.trans hinv2.1)
      (by rw [A.pool_of_vmPreserved (lim := lim) (st := st) (hinv1.2.trans (hvm_m1.trans hinv2.2))]; sep_ac_rfl) ?_
    intro sm2 hpcm2 hrunm2 hspm2 htrm2 hcsm2 hinv_m2
    rcases hcsm2 with ⟨hm2_19, hm2_20, hm2_21, _, _, _, _, _, hm2_27, _, hm2_fp, _⟩
    simp only [arm64_norm, hm19, hm20, hm21, hm27, hmfp]
      at hm2_19 hm2_20 hm2_21 hm2_27 hm2_fp
    dsimp only [headerReceivedPBPinnedAt, unchunked3PinnedAt]
    have ⟨h136_24, h136_72⟩ : (a + 136#64) + 0x18#64 = a + 160#64 ∧ (a + 136#64) + 0x48#64 = a + 208#64 :=
      ⟨by bv_omega, by bv_omega⟩
    rw [h136_24, h136_72]
    refine sepWPp_extract_pure
      ((optAuthCap g.auth u.auth + 1#64 == 0#64) = !u.auth.isSome ∧
       (optAuthCap g.auth u.auth + 1#64 != 0#64) = u.auth.isSome)
      (fun R' hm => etv2_optAuth_cap_bounds (A := A.repAlloc) (p := a + 160#64)
        (R := vecU8At A.repAlloc (a + 136#64) g.f3.cap g.f3.ptr u.hdr ∗ ((a + 208#64) ↦₆₄ u.epoch) ∗
          vecU8At A.repAlloc (sp - 120#64) cap ptr bs1 ∗ A.pool lim st sm2 ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by dsimp only [bs1]; sep_ac_rfl)) hm))
      fun ⟨hcap_auth_beq, hcap_auth_bne⟩ => ?_
    set bs2 := bs1 ++ encodeUint64Field 1#32 u.epoch
    suffices h5048 : ∀ sm3 : State,
        sm3.pc = (blkPl_426).base + 5048#64 → sm3.status = .Running → sm3.sp = sp - 144#64 → sm3.trace = s0.trace →
        sm3.readReg64 .x19 = s.readReg64 .x19 → sm3.readReg64 .x20 = a → sm3.readReg64 .x21 = s.readReg64 .x21 →
        sm3.readReg64 .x27 = s.readReg64 .x27 → sm3.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm3 →
        SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm3
          (((vecU8At A.repAlloc (a + 136#64) g.f3.cap g.f3.ptr u.hdr ∗
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
            u.epoch (sp - 120#64) cap ptr sp ((blkPl_426).base + 5048#64) (bs1 ++ [0x08#8])
            (by simpa only [List.length_append, List.length_singleton] using hfit_ep)
            (F := (vecU8At A.repAlloc (a + 136#64) g.f3.cap g.f3.ptr u.hdr ∗
              optAuthenticatorPBPinnedAt A.repAlloc g.auth (a + 160#64) u.auth ∗
              ((a + 208#64) ↦₆₄ u.epoch)) ∗ F)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hinv_m2.trans hinv3.1) (by rw [← hpack_ep, hpool3]) ?_
          intro sm3 hpcm3 hrunm3 hspm3 htrm3 hcsm3 hinv_m3
          rcases hcsm3 with ⟨hm3_19, hm3_20, hm3_21, _, _, _, _, _, hm3_27, _, hm3_fp, _⟩
          simp only [arm64_norm, hm2_19, hm2_20, hm2_21, hm2_27, hm2_fp]
            at hm3_19 hm3_20 hm3_21 hm3_27 hm3_fp
          refine SepWPp.weaken_pre (Entails.of_eq ?_)
            (h5048 sm3 hpcm3 hrunm3 hspm3 htrm3 hm3_19 hm3_20 hm3_21 hm3_27 hm3_fp hinv_m3)
          simp +zetaDelta only [bs2, bs1, etv2_encodeUint64Field_1_eq, hep, Bool.false_eq_true, ↓reduceIte,
            List.append_assoc]; sep_ac_rfl
      · apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 5048#64)
        wp_steps
        apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv3
        have hpool3 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv3.2).symm
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (h5048 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (hinv_m2.trans hinv3.1))
        rw [hpool3]
        simp +zetaDelta only [bs2, bs1, etv2_encodeUint64Field_1_eq, hep, ↓reduceIte, List.append_nil]; sep_ac_rfl
    intro sm3 hpcm3 hrunm3 hspm3 htrm3 hx19_3 hx20_3 hx21_3 hx27_3 hfp_3 hinv_3
    set bs3 := bs2 ++ encodeOptMessage ProtoAuthenticator.encodeRaw 2#32 u.auth
    suffices h5072 : ∀ sm4 : State,
        sm4.pc = (blkPl_426).base + 5072#64 → sm4.status = .Running → sm4.sp = sp - 144#64 → sm4.trace = s0.trace →
        sm4.readReg64 .x19 = s.readReg64 .x19 → sm4.readReg64 .x20 = a → sm4.readReg64 .x21 = s.readReg64 .x21 →
        sm4.readReg64 .x27 = s.readReg64 .x27 → sm4.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm4 →
        SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm4
          (((vecU8At A.repAlloc (a + 136#64) g.f3.cap g.f3.ptr u.hdr ∗
            optAuthenticatorPBPinnedAt A.repAlloc g.auth (a + 160#64) u.auth ∗ ((a + 208#64) ↦₆₄ u.epoch)) ∗
            vecU8At A.repAlloc (sp - 120#64) cap ptr bs3 ∗ A.pool lim st sm4 ∗
            stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
          Q Qp oom by
      cases hauth : u.auth with
      | none =>
        rw [optAuthenticatorPBPinnedAt_eq A.repAlloc g.auth (a + 160#64) none]
        simp only [hauth, Option.isSome_none, Bool.not_false] at hcap_auth_beq hcap_auth_bne
        apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 5072#64)
        wp_steps
        apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv4
        have hpool4 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv4.2).symm
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (h5072 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
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
          (a + 160#64) (sp - 120#64) cap ptr sp ((blkPl_426).base + 5072#64) g.auth auth bs2 hfit_auth
          (F := (vecU8At A.repAlloc (a + 136#64) g.f3.cap g.f3.ptr u.hdr ∗ ((a + 208#64) ↦₆₄ u.epoch)) ∗ F)
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
          (h5072 sm4 hpcm4 hrunm4 hspm4 htrm4 hm4_19 hm4_20 hm4_21 hm4_27 hm4_fp hinv_m4)
        simp +zetaDelta only [bs3, bs2, bs1, hauth, encodeOptMessage, optAuthenticatorPBPinnedAt]; sep_ac_rfl
    intro sm4 hpcm4 hrunm4 hspm4 htrm4 hx19_4 hx20_4 hx21_4 hx27_4 hfp_4 hinv_4
    refine sepWPp_extract_vecU8At_bounds (A := A.repAlloc) (v := a + 136#64) (cap := g.f3.cap)
      (ptr := g.f3.ptr) (bs := u.hdr)
      (F := optAuthenticatorPBPinnedAt A.repAlloc g.auth (a + 160#64) u.auth ∗ ((a + 208#64) ↦₆₄ u.epoch) ∗
        vecU8At A.repAlloc (sp - 120#64) cap ptr bs3 ∗ A.pool lim st sm4 ∗
        stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F)
      (by dsimp +zetaDelta only [bs3, bs2, bs1]; sep_ac_rfl) fun hhdr_le hhdr_cap _ => ?_
    have ⟨h144, h152⟩ : (a + 136#64) + 8#64 = a + 144#64 ∧ (a + 136#64) + 16#64 = a + 152#64 :=
      ⟨by bv_omega, by bv_omega⟩
    rw [vecU8At_eq_header_sep_buf A.repAlloc (a + 136#64), vecHeader, h144, h152]
    have hhdr_lt : u.hdr.length < 2 ^ 64 := by omega
    obtain ⟨hbeqz, hbnez⟩ := ofNat_length_beq_zero_of_lt hhdr_lt
    cases hemp : u.hdr.isEmpty
    · simp only [hemp, Bool.not_false] at hbeqz hbnez
      have hne_hdr : u.hdr ≠ [] := List.isEmpty_eq_false_iff.mp hemp
      have henc_eq : encodeBytesField 3#32 u.hdr =
          [0x1a#8] ++ encodeVarint (BitVec.ofNat 64 u.hdr.length) ++ u.hdr := by
        rw [etv2_encodeBytesField_3_eq, hemp]; simp only [Bool.false_eq_true, ↓reduceIte]
      have hfit_all : bs3.length + 1 + (encodeVarint (BitVec.ofNat 64 u.hdr.length)).length + u.hdr.length ≤ cap.toNat := by
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
          0x1a#8 sp cap ptr ((blkPl_426).base + 5132#64) bs3 u.hdr hemp hfit_all hcap hptr halign
          (F := (((a + 136#64) ↦₆₄ g.f3.cap) ∗ ((a + 144#64) ↦₆₄ g.f3.ptr) ∗
            ((a + 152#64) ↦₆₄ BitVec.ofNat 64 u.hdr.length)) ∗
            vecU8Buf A.repAlloc g.f3.cap g.f3.ptr u.hdr ∗
            optAuthenticatorPBPinnedAt A.repAlloc g.auth (a + 160#64) u.auth ∗
            ((a + 208#64) ↦₆₄ u.epoch) ∗ F)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hinv_4.trans hinv5.1) (by rw [hpool5]; dsimp +zetaDelta only [bs3, bs2, bs1]; sep_ac_rfl) ?_
        intro sm5 bs4 hpcm5 hrunm5 hspm5 htrm5 hcsm5 hinv_m5 hfit_mc hcmp_mc
        rcases hcsm5 with ⟨hm5_19, hm5_20, hm5_21, hm5_22, _, _, _, _, hm5_27, _, hm5_fp, _⟩
        simp only [arm64_norm, hx19_4, hx20_4, hx21_4, hx27_4, hfp_4]
          at hm5_19 hm5_20 hm5_21 hm5_22 hm5_27 hm5_fp
        apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).ρ "memcpy")
        by_vm_steps
          wp_steps
          apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, wp_norm, *])
          intro hinv6
          have hpool6 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv6.2).symm
          refine etv2_step_memcpy_slice_placed A lim st H hmemcpy
            sp cap ptr g.f3.cap g.f3.ptr ((blkPl_426).base + 5172#64) bs4 u.hdr hemp hhdr_le halign
            (F := (((a + 136#64) ↦₆₄ g.f3.cap) ∗ ((a + 144#64) ↦₆₄ g.f3.ptr) ∗
              ((a + 152#64) ↦₆₄ BitVec.ofNat 64 u.hdr.length)) ∗
              optAuthenticatorPBPinnedAt A.repAlloc g.auth (a + 160#64) u.auth ∗
              ((a + 208#64) ↦₆₄ u.epoch) ∗ F)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            hhdr_lt (hinv_m5.trans hinv6.1) (by rw [hpool6]; sep_ac_rfl) ?_
          intro sm6 hpcm6 hrunm6 hspm6 htrm6 hcsm6 hinv_m6
          rcases hcsm6 with ⟨hm6_19, _, hm6_21, hm6_22, hm6_23, _, _, _, hm6_27, _, hm6_fp, _⟩
          simp only [arm64_norm, hm5_19, hm5_21, hm5_22, hm5_27, hm5_fp]
            at hm6_19 hm6_21 hm6_22 hm6_23 hm6_27 hm6_fp
          apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 5180#64)
          by_vm_steps
            wp_steps
            apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, wp_norm, *])
            intro hinv7
            have hpool7 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv7.2).symm
            have hpack_mc := vecU8At_pack_slice A.repAlloc (sp - 120#64) cap ptr bs4 u.hdr hfit_mc hcap hptr hne_hdr
            have hbs_eq : bs4 ++ u.hdr = bs ++ encodeOptMessage V1State.Unchunked.HeaderReceived.encodeRaw 1#32 (some u) := by
              rw [etv3_encodeOptHeaderReceived_some_eq, henc_eq]; dsimp only [bs4, bs3, bs2, bs1]
              simp only [List.append_assoc]
            rw [h112, h104, hbs_eq] at hpack_mc
            refine SepWPp.weaken_pre (Entails.of_eq ?_)
              (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m6.trans hinv7.1))
            dsimp only [headerReceivedPBPinnedAt, unchunked3PinnedAt]
            rw [h136_24, h136_72, vecU8At_eq_header_sep_buf A.repAlloc (a + 136#64), vecHeader,
              h144, h152, ← hpack_mc, hpool7]; sep_ac_rfl
    · simp only [hemp, Bool.not_true] at hbeqz hbnez
      have henc_nil : encodeBytesField 3#32 u.hdr = [] := by
        rw [etv2_encodeBytesField_3_eq, hemp]; simp only [↓reduceIte]
      apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 5180#64)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv5
      have hpool5 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv5.2).symm
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_4.trans hinv5.1))
      dsimp only [headerReceivedPBPinnedAt, unchunked3PinnedAt]
      rw [h136_24, h136_72, vecU8At_eq_header_sep_buf A.repAlloc (a + 136#64), vecHeader,
        h144, h152, etv3_encodeOptHeaderReceived_some_eq, henc_nil, hpool5]
      dsimp only [bs3, bs2, bs1]; simp only [List.append_nil, List.append_assoc]

theorem step_encodeToVec_v1_headerReceived_placed [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (H : String → Option (State → State)) {s0 s : State}
    (hhrLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 404)
      (withStepInv s0 (leafEncLen16Spec (headerReceivedPBPinnedAt A.repAlloc) headerReceivedPBEncodedLen)))
    (hpolyDecLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 413)
      (withStepInv s0 (leafEncLen16Spec (polynomialDecoderPBPinnedAt A.repAlloc) polynomialDecoderPBEncodedLen)))
    (hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hauthEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 314)
      (withStepInv s0 (authEncodeExactSpecOf resStack A lim)))
    (hmemcpy : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      ((blkPl_426).ρ "memcpy") etvMemcpyRegionSpec)
    (hpolyDec : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 315)
      (withStepInv s0 (etvPolyDecoderBudgetExactSpecOf resStack A lim)))
    (a sp cap ptr : BitVec 64) (g : Unchunked3PBGhost × PolynomialDecoderPBGhost)
    (v : V1State.Chunked.HeaderReceived) (bs : List (BitVec 8))
    (hv_len : v1StatePBEncodedLen ⟨some (.headerReceived v)⟩ < 2 ^ 64)
    (hfit : bs.length + (V1State.InnerState.encode (.headerReceived v)).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_426).base + 2908#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = a) (hinv0 : StepInv s0 s)
    (hP : P = ((optHeaderReceivedPBPinnedAt A.repAlloc g.1 (a + 136#64) v.uc ∗
      optPolynomialDecoderPBPinnedAt A.repAlloc g.2 (a + 216#64) v.receivingEk) ∗
      vecU8At A.repAlloc (sp - 120#64) cap ptr bs ∗ A.pool lim st s ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_426).base + 1808#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm
        (((optHeaderReceivedPBPinnedAt A.repAlloc g.1 (a + 136#64) v.uc ∗
          optPolynomialDecoderPBPinnedAt A.repAlloc g.2 (a + 216#64) v.receivingEk) ∗
          vecU8At A.repAlloc (sp - 120#64) cap ptr (bs ++ V1State.InnerState.encode (.headerReceived v)) ∗
          A.pool lim st sm ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q Qp oom := by
  subst hP
  rcases v with ⟨uc, receivingEk⟩
  rw [etv3_encodeInnerState_headerReceived_eq] at hfit
  simp only [List.length_append, List.length_singleton] at hfit
  have hsub_len : v1StateInnerPayloadEncodedLen (.headerReceived ⟨uc, receivingEk⟩) < 2 ^ 64 := by
    dsimp only [v1StatePBEncodedLen] at hv_len; omega
  have hlt1 : bs.length < cap.toNat := by omega
  have hfit_var : (bs ++ [0x3a#8]).length +
      (encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.headerReceived ⟨uc, receivingEk⟩)))).length ≤
      cap.toNat := by
    simp only [List.length_append, List.length_singleton]; omega
  refine sepWPp_extract_vecU8At_bounds (v := sp - 120#64) (cap := cap) (ptr := ptr) (bs := bs)
    (F := optHeaderReceivedPBPinnedAt A.repAlloc g.1 (a + 136#64) uc ∗
      optPolynomialDecoderPBPinnedAt A.repAlloc g.2 (a + 216#64) receivingEk ∗ A.pool lim st s ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F)
    (by sep_ac_rfl) fun _ hcap hptr => ?_
  refine sepWPp_extract_pure
    (((optHeaderReceivedCap g.1 uc + 1#64 == 0#64) = !uc.isSome ∧
      (optHeaderReceivedCap g.1 uc + 1#64 != 0#64) = uc.isSome) ∧
     ((optPolyDecCap g.2 receivingEk + 1#64 == 0#64) = !receivingEk.isSome ∧
      (optPolyDecCap g.2 receivingEk + 1#64 != 0#64) = receivingEk.isSome))
    (fun R' hm =>
      ⟨optHeaderReceivedPBPinnedAt_cap_bounds (p := a + 136#64)
        (R := optPolynomialDecoderPBPinnedAt A.repAlloc g.2 (a + 216#64) receivingEk ∗
          vecU8At A.repAlloc (sp - 120#64) cap ptr bs ∗ A.pool lim st s ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm),
       optPolynomialDecoderPBPinnedAt_cap_bounds (p := a + 216#64)
        (R := optHeaderReceivedPBPinnedAt A.repAlloc g.1 (a + 136#64) uc ∗
          vecU8At A.repAlloc (sp - 120#64) cap ptr bs ∗ A.pool lim st s ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm)⟩)
    fun ⟨⟨hcap_uc_beq, hcap_uc_bne⟩, ⟨hcap_dec_beq, hcap_dec_bne⟩⟩ => ?_
  have hbeq_false := cap_beq_len_false_of_lt hlt1 hcap
  have ⟨h112, h104⟩ : (sp - 120#64) + 8#64 = sp - 112#64 ∧ (sp - 120#64) + 16#64 = sp - 104#64 :=
    ⟨by bv_omega, by bv_omega⟩
  have hpack := vecU8At_pack_one A.repAlloc (sp - 120#64) cap ptr bs 0x3a#8 hlt1 hcap hptr
  rw [h112, h104] at hpack
  suffices h3864 : ∀ sm1 : State,
      sm1.pc = (blkPl_426).base + 3864#64 → sm1.status = .Running → sm1.sp = sp - 144#64 → sm1.trace = s0.trace →
      sm1.readReg64 .x20 = a → sm1.readReg64 .x22 = optHeaderReceivedCap g.1 uc →
      sm1.readReg64 .x23 = BitVec.ofNat 64 (optHeaderReceivedPBFieldEncodedLen uc) →
      sm1.readReg64 .x27 = s.readReg64 .x27 → sm1.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm1 →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm1
        (((optHeaderReceivedPBPinnedAt A.repAlloc g.1 (a + 136#64) uc ∗
          optPolynomialDecoderPBPinnedAt A.repAlloc g.2 (a + 216#64) receivingEk) ∗
          vecU8At A.repAlloc (sp - 120#64) cap ptr (bs ++ [0x3a#8]) ∗ A.pool lim st sm1 ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom by
    rw [vecU8At_expose_one A.repAlloc (sp - 120#64) cap ptr bs hlt1 hcap hptr, h112, h104]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun b0 => ?_
    cases uc with
    | none =>
      rw [optHeaderReceivedPBPinnedAt_eq A.repAlloc g.1 (a + 136#64) none]
      simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
      apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 3864#64)
      by_vm_steps
        wp_steps
        apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv1
        have hpool1 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv1.2).symm
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (h3864 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [optHeaderReceivedPBFieldEncodedLen, arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1.1))
        rw [← optHeaderReceivedPBPinnedAt_eq A.repAlloc g.1 (a + 136#64) none, ← hpack, hpool1]
    | some u =>
      rw [optHeaderReceivedPBPinnedAt_eq A.repAlloc g.1 (a + 136#64) (some u)]
      simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      have ⟨hu_fit, hopt_u_lt⟩ :
          headerReceivedPBEncodedLen u < 2 ^ 64 ∧ optHeaderReceivedPBFieldEncodedLen (some u) < 2 ^ 64 :=
        ⟨by dsimp only [v1StateInnerPayloadEncodedLen, optHeaderReceivedPBFieldEncodedLen] at hsub_len; omega,
         by dsimp only [v1StateInnerPayloadEncodedLen] at hsub_len; omega⟩
      have hvar_u_lt : varintLen (BitVec.ofNat 64 (headerReceivedPBEncodedLen u)) <
          optHeaderReceivedPBFieldEncodedLen (some u) := by
        dsimp only [optHeaderReceivedPBFieldEncodedLen]; omega
      have ⟨⟨hu1, hu2, hu3, hu4, hu5⟩, hult_u, hopt_u_eq⟩ :=
        (⟨cmp_ls_false_of_lt hvar_u_lt hopt_u_lt, ult_of_lt_of_fit hvar_u_lt hopt_u_lt,
          etv3_bv_optHeaderReceived_some_eq u⟩ : _ ∧ _ ∧ _)
      apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 404)
      by_vm_steps
        wp_steps
        apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv1
        rw [← optHeaderReceivedPBPinnedAt_eq A.repAlloc g.1 (a + 136#64) (some u)]
        refine step_etv_leaf_encLen16_call_placed hres (headerReceivedPBPinnedAt A.repAlloc)
          headerReceivedPBEncodedLen hhrLen
          (a + 136#64) sp ((blkPl_426).base + 2964#64) g.1 u hu_fit
          (F := optPolynomialDecoderPBPinnedAt A.repAlloc g.2 (a + 216#64) receivingEk ∗
            vecU8At A.repAlloc (sp - 120#64) cap ptr (bs ++ [0x3a#8]) ∗ A.pool lim st s ∗ F)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
          (hinv0.trans hinv1.1)
          (by rw [← hpack]; dsimp only [optHeaderReceivedPBPinnedAt]; sep_ac_rfl) ?_
        intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1 hcsm1 hinv_m1 hvm_m1
        rcases hcsm1 with ⟨_, hm20, _, hm22, _, _, _, _, hm27, _, hmfp, _⟩
        simp only [arm64_norm, hx20] at hm20 hm22 hm27 hmfp
        apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 3864#64)
        wp_steps
        apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv2
        have hpool12 := (A.pool_of_vmPreserved (lim := lim) (st := st) (hinv1.2.trans (hvm_m1.trans hinv2.2))).symm
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (h3864 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (hinv_m1.trans hinv2.1))
        rw [hpool12]; dsimp only [optHeaderReceivedPBPinnedAt]; sep_ac_rfl
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx20_1 hx22_1 hx23_1 hx27_1 hfp_1 hinv_1
  suffices h4920 : ∀ sm2 : State,
      sm2.pc = (blkPl_426).base + 4920#64 → sm2.status = .Running → sm2.sp = sp - 144#64 → sm2.trace = s0.trace →
      sm2.readReg64 .x8 = BitVec.ofNat 64 (optPolynomialDecoderPBFieldEncodedLen receivingEk) →
      sm2.readReg64 .x19 = optPolyDecCap g.2 receivingEk → sm2.readReg64 .x20 = a → sm2.readReg64 .x21 = a + 216#64 →
      sm2.readReg64 .x22 = optHeaderReceivedCap g.1 uc →
      sm2.readReg64 .x23 = BitVec.ofNat 64 (optHeaderReceivedPBFieldEncodedLen uc) →
      sm2.readReg64 .x27 = s.readReg64 .x27 → sm2.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm2 →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm2
        (((optHeaderReceivedPBPinnedAt A.repAlloc g.1 (a + 136#64) uc ∗
          optPolynomialDecoderPBPinnedAt A.repAlloc g.2 (a + 216#64) receivingEk) ∗
          vecU8At A.repAlloc (sp - 120#64) cap ptr (bs ++ [0x3a#8]) ∗ A.pool lim st sm2 ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom by
    cases receivingEk with
    | none =>
      rw [optPolynomialDecoderPBPinnedAt_eq A.repAlloc g.2 (a + 216#64) none]
      simp only [Option.isSome_none, Bool.not_false] at hcap_dec_beq hcap_dec_bne
      apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 4920#64)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv2
      have hpool2 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv2.2).symm
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h4920 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [optPolynomialDecoderPBFieldEncodedLen, arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (hinv_1.trans hinv2.1))
      rw [← optPolynomialDecoderPBPinnedAt_eq A.repAlloc g.2 (a + 216#64) none, hpool2]
    | some dec =>
      rw [optPolynomialDecoderPBPinnedAt_eq A.repAlloc g.2 (a + 216#64) (some dec)]
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
      rw [← optPolynomialDecoderPBPinnedAt_eq A.repAlloc g.2 (a + 216#64) (some dec)]
      refine step_etv_leaf_encLen16_call_placed hres (polynomialDecoderPBPinnedAt A.repAlloc)
        polynomialDecoderPBEncodedLen hpolyDecLen
        (a + 216#64) sp ((blkPl_426).base + 3888#64) g.2 dec hdec_fit
        (F := optHeaderReceivedPBPinnedAt A.repAlloc g.1 (a + 136#64) uc ∗
          vecU8At A.repAlloc (sp - 120#64) cap ptr (bs ++ [0x3a#8]) ∗ A.pool lim st sm1 ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (hinv_1.trans hinv2.1)
        (by dsimp only [optPolynomialDecoderPBPinnedAt]; sep_ac_rfl) ?_
      intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx0m2 hcsm2 hinv_m2 hvm_m2
      rcases hcsm2 with ⟨hm2_19, hm2_20, hm2_21, hm2_22, hm2_23, _, _, _, hm2_27, _, hm2_fp, _⟩
      simp only [arm64_norm, hx20_1, hx22_1, hx23_1, hx27_1, hfp_1]
        at hm2_19 hm2_20 hm2_21 hm2_22 hm2_23 hm2_27 hm2_fp
      apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 4920#64)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv3
      have hpool23 := (A.pool_of_vmPreserved (lim := lim) (st := st) (hinv2.2.trans (hvm_m2.trans hinv3.2))).symm
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h4920 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m2.trans hinv3.1))
      rw [hpool23]; dsimp only [optPolynomialDecoderPBPinnedAt]; sep_ac_rfl
  intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx8_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx27_2 hfp_2 hinv_2
  have ⟨hadd_sum, hult_sum, hule_sum, hult_sum2, hule_sum2⟩ := adds_no_overflow_of_eq
      (a := optPolynomialDecoderPBFieldEncodedLen receivingEk)
      (b := optHeaderReceivedPBFieldEncodedLen uc)
      (c := v1StateInnerPayloadEncodedLen (.headerReceived ⟨uc, receivingEk⟩)) rfl hsub_len
  apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 292)
  wp_steps
  apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, wp_norm, *])
  intro hinv3
  have hpool3 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv3.2).symm
  set bs1 := (bs ++ [0x3a#8]) ++
    encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.headerReceived ⟨uc, receivingEk⟩)))
  refine step_etv_encode_varint_call_prog A lim st hvarint
    (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.headerReceived ⟨uc, receivingEk⟩)))
    (sp - 120#64) cap ptr sp ((blkPl_426).base + 4936#64) (bs ++ [0x3a#8]) hfit_var
    (F := (optHeaderReceivedPBPinnedAt A.repAlloc g.1 (a + 136#64) uc ∗
      optPolynomialDecoderPBPinnedAt A.repAlloc g.2 (a + 216#64) receivingEk) ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hinv_2.trans hinv3.1) (by rw [hpool3]; sep_ac_rfl) ?_
  intro sm3 hpcm3 hrunm3 hspm3 htrm3 hcsm3 hinv_m3
  rcases hcsm3 with ⟨hm3_19, hm3_20, hm3_21, hm3_22, _, _, _, _, hm3_27, _, hm3_fp, _⟩
  simp only [arm64_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx27_2, hfp_2]
    at hm3_19 hm3_20 hm3_21 hm3_22 hm3_27 hm3_fp
  set bs2 := bs1 ++ encodeOptMessage V1State.Unchunked.HeaderReceived.encodeRaw 1#32 uc
  suffices h5180 : ∀ sm4 : State,
      sm4.pc = (blkPl_426).base + 5180#64 → sm4.status = .Running → sm4.sp = sp - 144#64 → sm4.trace = s0.trace →
      sm4.readReg64 .x19 = optPolyDecCap g.2 receivingEk → sm4.readReg64 .x21 = a + 216#64 →
      sm4.readReg64 .x27 = s.readReg64 .x27 → sm4.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm4 →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm4
        (((optHeaderReceivedPBPinnedAt A.repAlloc g.1 (a + 136#64) uc ∗
          optPolynomialDecoderPBPinnedAt A.repAlloc g.2 (a + 216#64) receivingEk) ∗
          vecU8At A.repAlloc (sp - 120#64) cap ptr bs2 ∗ A.pool lim st sm4 ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom by
    cases uc with
    | none =>
      simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
      apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 5180#64)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv4
      have hpool4 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv4.2).symm
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h5180 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m3.trans hinv4.1))
      rw [hpool4]; simp +zetaDelta only [bs2, bs1, encodeOptMessage, List.append_nil]; sep_ac_rfl
    | some u =>
      simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      have hu_lt : headerReceivedPBEncodedLen u < 2 ^ 64 := by
        dsimp only [v1StateInnerPayloadEncodedLen, optHeaderReceivedPBFieldEncodedLen] at hsub_len; omega
      have hfit_u : bs1.length + (encodeOptMessage V1State.Unchunked.HeaderReceived.encodeRaw 1#32 (some u)).length ≤ cap.toNat := by
        dsimp only [bs1]; simp only [List.length_append, List.length_singleton] at hfit ⊢; omega
      apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 4944#64)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv4
      have hpool4 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv4.2).symm
      refine etv3_step_headerReceived_some_placed hres A lim st H hhrLen hvarint hauthEnc hmemcpy
        a sp cap ptr g.1 u bs1 hu_lt hfit_u hcap hptr halign
        (F := optPolynomialDecoderPBPinnedAt A.repAlloc g.2 (a + 216#64) receivingEk ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hinv_m3.trans hinv4.1)
        (by rw [hpool4]; dsimp +zetaDelta only [bs1, optHeaderReceivedPBPinnedAt]; simp only [List.append_assoc]; sep_ac_rfl) ?_
      intro sm4 hpcm4 hrunm4 hspm4 htrm4 hm4_19 hm4_21 hm4_27 hm4_fp hinv_m4
      simp only [arm64_norm, hm3_19, hm3_21, hm3_27, hm3_fp]
        at hm4_19 hm4_21 hm4_27 hm4_fp
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h5180 sm4 hpcm4 hrunm4 hspm4 htrm4 hm4_19 hm4_21 hm4_27 hm4_fp hinv_m4)
      dsimp only [bs2, optHeaderReceivedPBPinnedAt]; sep_ac_rfl
  intro sm4 hpcm4 hrunm4 hspm4 htrm4 hx19_4 hx21_4 hx27_4 hfp_4 hinv_4
  cases receivingEk with
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
    rw [etv3_encodeInnerState_headerReceived_eq, hpool5]
    simp +zetaDelta only [bs2, bs1, encodeOptMessage, List.append_nil, List.append_assoc]
  | some dec =>
    simp only [Option.isSome_some, Bool.not_true] at hcap_dec_beq hcap_dec_bne
    have hfit_dec : bs2.length + (encodeMessage PolynomialDecoder.encodeRaw 2#32 dec).length ≤ cap.toNat := by
      simp +zetaDelta only [bs2, bs1, encodeOptMessage, List.length_append, List.length_singleton] at hfit ⊢; omega
    apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 5196#64)
    wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv5
    have hpool5 := (A.pool_of_vmPreserved (lim := lim) (st := st) hinv5.2).symm
    refine step_encodeToVec_tail_5196_polyDec_placed A lim st H hpolyDec
      2#32 (a + 216#64) sp cap ptr g.2 dec bs2 hfit_dec halign
      (F := optHeaderReceivedPBPinnedAt A.repAlloc g.1 (a + 136#64) uc ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hinv_4.trans hinv5.1)
      (by rw [hpool5]; dsimp +zetaDelta only [bs2, bs1, optPolynomialDecoderPBPinnedAt]; sep_ac_rfl) ?_
    intro sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_27 hm5_fp hinv_m5
    simp only [arm64_norm, hx27_4, hfp_4] at hm5_27 hm5_fp
    refine SepWPp.weaken_pre (Entails.of_eq ?_)
      (hnext sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_27 hm5_fp hinv_m5)
    rw [etv3_encodeInnerState_headerReceived_eq]
    simp +zetaDelta only [bs2, bs1, encodeOptMessage,
      optPolynomialDecoderPBPinnedAt, List.append_assoc]; sep_ac_rfl

end LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked3aPlacedBudget

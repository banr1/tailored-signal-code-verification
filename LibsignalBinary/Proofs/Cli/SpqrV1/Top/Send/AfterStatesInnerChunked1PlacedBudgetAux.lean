/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerChunked1Placed
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerHeaderPlacedBudget
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsChunkedV1Budget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.CalleeBridgesBudget
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked1
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateHeader
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.V1StateHelpers
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesVnEncode
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Phase 3e (Part 1a): Tail Blocks & Variants `ct1Sampled`, `ekSentCt1Received`

Threads `RustCliAllocBudget` and `VmPreserved` through the shared `PolynomialDecoder` / `PolynomialEncoder`
tail blocks and `V1State::encode_raw` variants `idx = 7` (`ct1Sampled`) and `idx = 4` (`ekSentCt1Received`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerChunked1PlacedBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open CryptoVerification (LibsignalPlacement libsignalSessionCode lsmpl)
open CryptoVerification.RustHeap (RustAlloc vecU8At)
open CryptoVerification.LibsignalSpqrV1 (PolynomialDecoder PolynomialEncoder V1State)
open CryptoVerification.LibsignalSpqrV1.Proto (encodeMessage encodeOptMessage encodeVarint)
open CryptoVerification.SpqrV1.ProtoRepr
  (ChunkedCt1SampledPBGhost PolynomialDecoderPBGhost PolynomialEncoderPBGhost
   Unchunked4PBGhost Unchunked5PBGhost
   chunkedCt1SampledPBEncodedLen chunkedCt1SampledPBPinnedAt
   ct1SentPBPinnedAt ekSentCt1ReceivedPBEncodedLen ekSentCt1ReceivedPBPinnedAt
   noneCap_add_two_beq_zero noneCap_add_two_bne_zero
   optCt1SentPBPinnedAt
   optEkSentCt1ReceivedPBFieldEncodedLen optEkSentCt1ReceivedPBPinnedAt
   optPolynomialDecoderPBFieldEncodedLen optPolynomialDecoderPBPinnedAt
   optPolynomialEncoderPBPinnedAt
   polynomialDecoderPBEncodedLen polynomialDecoderPBPinnedAt
   polynomialEncoderPBPinnedAt
   v1StateInnerPayloadEncodedLen v1StatePBEncodedLen varintLen)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (adds_no_overflow_of_eq cmp_ls_false_of_lt
   hwVarintLen_bvShift_eq_ofNat_varintLen_norm hwVarintLen_eq_ofNat_varintLen_norm
   noneCap_add_one_beq_zero noneCap_add_one_bne_zero
   ofNat_countLeadingZeros_32 ofNat_countLeadingZeros_64
   ule_self_64 ule_zero_64 ult_self_64 ult_zero_64
   zeroExtend64_beq_zero32 zext64_truncate32)
open CryptoVerification.SpqrV1.Prost.EncodeToVec
  (StepInv bv_optEkSentCt1Received_some_eq bv_optPolyDec_some_eq
   cap_beq_len_false_of_lt
   encodeInnerState_ct1Sampled_eq encodeInnerState_ekSentCt1Received_eq
   encodeToVecCalleeStackOf
   noneCap2_add_two_beq_zero noneCap2_add_two_bne_zero
   noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
   optCt1SentCap optCt1SentPBPinnedAt_cap_bounds
   optEkSentCt1ReceivedCap optEkSentCt1ReceivedPBPinnedAt_cap_bounds optEkSentCt1ReceivedPBPinnedAt_eq
   optPolyDecCap optPolyEncCap
   optPolynomialDecoderPBPinnedAt_cap_bounds optPolynomialDecoderPBPinnedAt_eq
   optPolynomialEncoderPBPinnedAt_cap_bounds optPolynomialEncoderPBPinnedAt_eq
   ult_of_lt_of_fit
   vecU8At_expose_header vecU8At_expose_one vecU8At_pack_one withStepInv)
open CryptoVerification.Cli.SpqrV1.Top.Send.CodePlaced (blkPl_427_ρ)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
  (spqrSendPlacedEntry spqrSendPlacedProg)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerHeaderPlacedBudget
  (step_send_chunked_encLen48_call_placed
   step_send_encode_ct1Sent_budget_call_placed
   step_send_encode_ekSentCt1Received_budget_call_placed
   step_send_encode_polyDecoder_budget_call_placed
   step_send_encode_polyEncoder_budget_call_placed
   step_send_encode_varint_call_placed
   step_send_leaf_encLen16_call_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhaseBudget
  (encodeVarintExactSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsPlacedBudget
  (sepWP_done_tpidr sepWP_done_vm sepWPp_of_sepWP_cs_vm)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonBudget
  (etvPolyDecoderExactSpecOf etvPolyEncoderExactSpecOf leafEncLen16Spec)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonPlacedBudget
  (etvCt1SentBudgetExactSpecOf etvEkSentCt1ReceivedBudgetExactSpecOf
   etvPolyDecoderBudgetExactSpecOf etvPolyEncoderBudgetExactSpecOf)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsChunkedV1Budget
  (chunkedCt1SampledEncodedLenPinnedSpec)

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

/-! ## 1. Pure / `vecU8At` Extraction & `VmPreserved` → `BudgetExact` Callee Spec Bridges -/

omit [LibsignalPlacement] in
theorem sepWPp_extract_pure {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp} (φ : Prop)
    (hφ : ∀ R : SepProp, s.mem ⊨ P ∗ R → φ)
    (hnext : φ → SepWPp prog ret s P Q Qp oom) :
    SepWPp prog ret s P Q Qp oom :=
  fun R hm hL => hnext (hφ R hm) R hm hL

omit [LibsignalPlacement] in
theorem sepWPp_extract_vecU8At_bounds {A : RustAlloc} {v cap ptr : BitVec 64}
    {bs : List (BitVec 8)} {prog : Program} {ret : BitVec 64} {s : State} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hP : P = vecU8At A v cap ptr bs ∗ F)
    (h : bs.length ≤ cap.toNat → cap.toNat < 2 ^ 63 → ptr ≠ 0 → SepWPp prog ret s P Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  have hhm : s.mem ⊨
      (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ : SepProp) ∗
        ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (if cap = 0 then emp
           else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
             memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ∗ F ∗ R) := by
    rw [hP, vecU8At_expose_header] at hm
    convert hm using 1; sep_ac_rfl
  rw [satisfies_pure_sepConj] at hhm
  exact h hhm.1.1 hhm.1.2.1 hhm.1.2.2 R hm hL

omit [LibsignalPlacement] in
/-- Lift 0-allocation (`VmPreserved`) `etvPolyEncoderExactSpecOf resStack A.repAlloc` to
`etvPolyEncoderBudgetExactSpecOf resStack A lim` by framing `A.pool lim st`. -/
theorem etvPolyEncoderBudgetExact_of_vm {resStack : Nat}
    {M : AllocCostModel} {prog : Program} {call_pc : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {s0 : State}
    (hpe_ok : subroutine_ok prog call_pc
      (withStepInv s0 (etvPolyEncoderExactSpecOf resStack A.repAlloc))) :
    subroutine_ok prog call_pc
      (withStepInv s0 (etvPolyEncoderBudgetExactSpecOf resStack A lim)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s hpc hrun hpre hal => ?_
  have hpre' : s.mem ⊨
      (withStepInv s0 (etvPolyEncoderExactSpecOf resStack A.repAlloc)).pre x s ∗
        (A.pool lim st s ∗ R) := by
    dsimp only [withStepInv, etvPolyEncoderBudgetExactSpecOf,
      etvPolyEncoderExactSpecOf] at hpre ⊢
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  refine hpe_ok.mono_outcome x (A.pool lim st s ∗ R) s hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStepInv, etvPolyEncoderBudgetExactSpecOf,
      etvPolyEncoderExactSpecOf] at hpost ⊢
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hinvf, hm⟩
    rw [A.pool_of_vmPreserved hinvf.1, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinvf.2, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm⟩
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

omit [LibsignalPlacement] in
/-- Lift 0-allocation (`VmPreserved`) `etvPolyDecoderExactSpecOf resStack A.repAlloc` to
`etvPolyDecoderBudgetExactSpecOf resStack A lim` by framing `A.pool lim st`. -/
theorem etvPolyDecoderBudgetExact_of_vm {resStack : Nat}
    {M : AllocCostModel} {prog : Program} {call_pc : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {s0 : State}
    (hpd_ok : subroutine_ok prog call_pc
      (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A.repAlloc))) :
    subroutine_ok prog call_pc
      (withStepInv s0 (etvPolyDecoderBudgetExactSpecOf resStack A lim)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s hpc hrun hpre hal => ?_
  have hpre' : s.mem ⊨
      (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A.repAlloc)).pre x s ∗
        (A.pool lim st s ∗ R) := by
    dsimp only [withStepInv, etvPolyDecoderBudgetExactSpecOf,
      etvPolyDecoderExactSpecOf] at hpre ⊢
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  refine hpd_ok.mono_outcome x (A.pool lim st s ∗ R) s hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStepInv, etvPolyDecoderBudgetExactSpecOf,
      etvPolyDecoderExactSpecOf] at hpost ⊢
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hinvf, hm⟩
    rw [A.pool_of_vmPreserved hinvf.1, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinvf.2, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm⟩
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

/-! ## 2. Shared `PolynomialDecoder` / `PolynomialEncoder` Tail Blocks -/

/-- Step `+10352 .. +6216`: sets `x2 = sp + 1424#64`, `w0 = 3#32`, calls
`encode<PolynomialDecoder> [local#1]` (Block `455`) with `x1 = dec_ptr`, and branches to `+6216`,
threading `A.pool lim st`. -/
theorem step_send_tail_10352_polyDec3_placed {resStack : Nat} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    {s0 s : State}
    (hpolyDec : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 455)
      (withStepInv s0 (etvPolyDecoderBudgetExactSpecOf resStack A lim)))
    (dec_ptr sp cap ptr : BitVec 64) (g : PolynomialDecoderPBGhost) (dec : PolynomialDecoder)
    (bs : List (BitVec 8))
    (hfit : bs.length + (encodeMessage PolynomialDecoder.encodeRaw 3#32 dec).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = spqrSendPlacedEntry + 10352#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = dec_ptr) (hinv0 : StepInv s0 s)
    (hP : P = (polynomialDecoderPBPinnedAt A.repAlloc g dec_ptr dec ∗
      vecU8At A.repAlloc (sp + 1424#64) cap ptr bs ∗ A.pool lim st s ∗
      stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = spqrSendPlacedEntry + 6216#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = s.readReg64 .x25 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((polynomialDecoderPBPinnedAt A.repAlloc g dec_ptr dec ∗
          vecU8At A.repAlloc (sp + 1424#64) cap ptr
            (bs ++ encodeMessage PolynomialDecoder.encodeRaw 3#32 dec) ∗
          A.pool lim st sm ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  subst hP
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
  apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 455)
  wp_steps
  apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, wp_norm, *])
  intro hinv1
  have hpool1 : A.pool lim st s = A.pool lim st _ := (A.pool_of_vmPreserved hinv1.2).symm
  refine step_send_encode_polyDecoder_budget_call_placed A lim st ext hpolyDec 3#32 dec_ptr
    (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 10364#64) g dec bs hfit (F := F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1.1)
    (by rw [hpool1]) ?_
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hcsm1 hinv_m1
  rcases hcsm1 with ⟨hm19, _, hm21, _, hm23, _, hm25, _, hm27, hm28, hmfp, _⟩
  simp only [arm64_norm] at hm19 hm21 hm23 hm25 hm27 hm28 hmfp
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
  apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 6216#64)
  wp_steps
  apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, wp_norm, *])
  intro hinv2
  have hpool2 : A.pool lim st sm1 = A.pool lim st _ := (A.pool_of_vmPreserved hinv2.2).symm
  refine SepWPp.weaken_pre (by rw [hpool2]; exact Entails.of_eq (by sep_ac_rfl))
    (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (hinv_m1.trans hinv2.1))

/-- Step `+11208 .. +6216`: sets `x2 = sp + 1424#64`, `w0 = 2#32`, calls
`encode<PolynomialDecoder> [local#1]` (Block `455`) with `x1 = dec_ptr`, and branches to `+6216`,
threading `A.pool lim st`. -/
theorem step_send_tail_11208_polyDec2_placed {resStack : Nat} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    {s0 s : State}
    (hpolyDec : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 455)
      (withStepInv s0 (etvPolyDecoderBudgetExactSpecOf resStack A lim)))
    (dec_ptr sp cap ptr : BitVec 64) (g : PolynomialDecoderPBGhost) (dec : PolynomialDecoder)
    (bs : List (BitVec 8))
    (hfit : bs.length + (encodeMessage PolynomialDecoder.encodeRaw 2#32 dec).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = spqrSendPlacedEntry + 11208#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = dec_ptr) (hinv0 : StepInv s0 s)
    (hP : P = (polynomialDecoderPBPinnedAt A.repAlloc g dec_ptr dec ∗
      vecU8At A.repAlloc (sp + 1424#64) cap ptr bs ∗ A.pool lim st s ∗
      stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = spqrSendPlacedEntry + 6216#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = s.readReg64 .x25 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((polynomialDecoderPBPinnedAt A.repAlloc g dec_ptr dec ∗
          vecU8At A.repAlloc (sp + 1424#64) cap ptr
            (bs ++ encodeMessage PolynomialDecoder.encodeRaw 2#32 dec) ∗
          A.pool lim st sm ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  subst hP
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
  apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 455)
  wp_steps
  apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, wp_norm, *])
  intro hinv1
  have hpool1 : A.pool lim st s = A.pool lim st _ := (A.pool_of_vmPreserved hinv1.2).symm
  refine step_send_encode_polyDecoder_budget_call_placed A lim st ext hpolyDec 2#32 dec_ptr
    (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 11220#64) g dec bs hfit (F := F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1.1)
    (by rw [hpool1]) ?_
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hcsm1 hinv_m1
  rcases hcsm1 with ⟨hm19, _, hm21, _, hm23, _, hm25, _, hm27, hm28, hmfp, _⟩
  simp only [arm64_norm] at hm19 hm21 hm23 hm25 hm27 hm28 hmfp
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
  apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 6216#64)
  wp_steps
  apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, wp_norm, *])
  intro hinv2
  have hpool2 : A.pool lim st sm1 = A.pool lim st _ := (A.pool_of_vmPreserved hinv2.2).symm
  refine SepWPp.weaken_pre (by rw [hpool2]; exact Entails.of_eq (by sep_ac_rfl))
    (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (hinv_m1.trans hinv2.1))

/-- Step `+11748 .. +6216`: sets `x1 = sp + 1424#64`, calls
`encode<PolynomialEncoder> [local#1]` (Block `456`) with `x0 = enc_ptr`, and branches to `+6216`,
threading `A.pool lim st`. -/
theorem step_send_tail_11748_polyEnc_placed {resStack : Nat} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    {s0 s : State}
    (hpolyEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 456)
      (withStepInv s0 (etvPolyEncoderBudgetExactSpecOf resStack A lim)))
    (enc_ptr sp cap ptr : BitVec 64) (g : PolynomialEncoderPBGhost) (enc : PolynomialEncoder)
    (bs : List (BitVec 8))
    (hfit : bs.length + (encodeMessage PolynomialEncoder.encodeRaw 2#32 enc).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = spqrSendPlacedEntry + 11748#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = enc_ptr) (hinv0 : StepInv s0 s)
    (hP : P = (polynomialEncoderPBPinnedAt A.repAlloc g enc_ptr enc ∗
      vecU8At A.repAlloc (sp + 1424#64) cap ptr bs ∗ A.pool lim st s ∗
      stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = spqrSendPlacedEntry + 6216#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = s.readReg64 .x25 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((polynomialEncoderPBPinnedAt A.repAlloc g enc_ptr enc ∗
          vecU8At A.repAlloc (sp + 1424#64) cap ptr
            (bs ++ encodeMessage PolynomialEncoder.encodeRaw 2#32 enc) ∗
          A.pool lim st sm ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  subst hP
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
  apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 456)
  wp_steps
  apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, wp_norm, *])
  intro hinv1
  have hpool1 : A.pool lim st s = A.pool lim st _ := (A.pool_of_vmPreserved hinv1.2).symm
  refine step_send_encode_polyEncoder_budget_call_placed A lim st ext hpolyEnc enc_ptr
    (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 11756#64) g enc bs hfit (F := F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1.1)
    (by rw [hpool1]) ?_
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hcsm1 hinv_m1
  rcases hcsm1 with ⟨hm19, _, hm21, _, hm23, _, hm25, _, hm27, hm28, hmfp, _⟩
  simp only [arm64_norm] at hm19 hm21 hm23 hm25 hm27 hm28 hmfp
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
  apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 6216#64)
  wp_steps
  apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, wp_norm, *])
  intro hinv2
  have hpool2 : A.pool lim st sm1 = A.pool lim st _ := (A.pool_of_vmPreserved hinv2.2).symm
  refine SepWPp.weaken_pre (by rw [hpool2]; exact Entails.of_eq (by sep_ac_rfl))
    (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (hinv_m1.trans hinv2.1))

/-! ## 3. Variant `idx = 7`: `.ct1Sampled` (`+8480 .. +8608`) -/

/-- Step `+8480 .. +6216` for `is = .ct1Sampled v`, threading `A.pool lim st`. -/
theorem step_send_v1_ct1Sampled_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    {s0 s : State}
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
    (sp cap ptr : BitVec 64) (g : ChunkedCt1SampledPBGhost) (v : V1State.Chunked.Ct1Sampled)
    (bs : List (BitVec 8)) (hv_len : v1StatePBEncodedLen ⟨some (.ct1Sampled v)⟩ < 2 ^ 64)
    (hfit : bs.length + (V1State.InnerState.encode (.ct1Sampled v)).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = spqrSendPlacedEntry + 8480#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = optCt1SentCap g.uc v.uc) (hinv0 : StepInv s0 s)
    (hP : P = (chunkedCt1SampledPBPinnedAt A.repAlloc g (sp + 4832#64) v ∗
      vecU8At A.repAlloc (sp + 1424#64) cap ptr bs ∗ A.pool lim st s ∗
      stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = spqrSendPlacedEntry + 6216#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = s.readReg64 .x25 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((chunkedCt1SampledPBPinnedAt A.repAlloc g (sp + 4832#64) v ∗
          vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs ++ V1State.InnerState.encode (.ct1Sampled v)) ∗
          A.pool lim st sm ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  subst hP
  rcases v with ⟨uc, sendingCt1, receivingEk⟩
  rw [encodeInnerState_ct1Sampled_eq] at hfit
  simp only [List.length_append, List.length_singleton] at hfit
  have hsub_len : chunkedCt1SampledPBEncodedLen ⟨uc, sendingCt1, receivingEk⟩ < 2 ^ 64 := by
    dsimp only [v1StatePBEncodedLen, v1StateInnerPayloadEncodedLen] at hv_len; omega
  have hlt1 : bs.length < cap.toNat := by omega
  have hfit_var : (bs ++ [0x42#8]).length +
      (encodeVarint (BitVec.ofNat 64 (chunkedCt1SampledPBEncodedLen ⟨uc, sendingCt1, receivingEk⟩))).length ≤
        cap.toNat := by
    simp only [List.length_append, List.length_singleton]; omega
  refine sepWPp_extract_vecU8At_bounds (v := sp + 1424#64) (cap := cap) (ptr := ptr) (bs := bs)
    (F := chunkedCt1SampledPBPinnedAt A.repAlloc g (sp + 4832#64) ⟨uc, sendingCt1, receivingEk⟩ ∗
      A.pool lim st s ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F)
    (by sep_ac_rfl) fun _ hcap hptr => ?_
  have hbeq_false := cap_beq_len_false_of_lt hlt1 hcap
  have ⟨h1432, h1440⟩ : (sp + 1424#64) + 8#64 = sp + 1432#64 ∧
      (sp + 1424#64) + 16#64 = sp + 1440#64 := ⟨by bv_omega, by bv_omega⟩
  have hpack := vecU8At_pack_one A.repAlloc (sp + 1424#64) cap ptr bs 0x42#8 hlt1 hcap hptr
  simp only [arm64_norm, h1432, h1440] at hpack
  suffices h8532 : ∀ sm1 : State,
      sm1.pc = spqrSendPlacedEntry + 8532#64 → sm1.status = .Running → sm1.sp = sp → sm1.trace = s0.trace →
      sm1.readReg64 .x0 = BitVec.ofNat 64 (chunkedCt1SampledPBEncodedLen ⟨uc, sendingCt1, receivingEk⟩) →
      sm1.readReg64 .x19 = s.readReg64 .x19 → sm1.readReg64 .x20 = optCt1SentCap g.uc uc →
      sm1.readReg64 .x21 = s.readReg64 .x21 → sm1.readReg64 .x22 = sp + 4704#64 →
      sm1.readReg64 .x23 = s.readReg64 .x23 → sm1.readReg64 .x25 = s.readReg64 .x25 →
      sm1.readReg64 .x27 = s.readReg64 .x27 → sm1.readReg64 .x28 = s.readReg64 .x28 →
      sm1.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm1 →
      SepWPp (spqrSendPlacedProg ext) ret sm1
        ((chunkedCt1SampledPBPinnedAt A.repAlloc g (sp + 4832#64) ⟨uc, sendingCt1, receivingEk⟩ ∗
          vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs ++ [0x42#8]) ∗ A.pool lim st sm1 ∗
          stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom by
    rw [vecU8At_expose_one A.repAlloc (sp + 1424#64) cap ptr bs hlt1 hcap hptr, h1432, h1440]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun b0 => ?_
    dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
    apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 486)
    by_vm_steps
      wp_steps
      apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv1
      refine step_send_chunked_encLen48_call_placed hres ext
        (chunkedCt1SampledPBPinnedAt A.repAlloc) chunkedCt1SampledPBEncodedLen hct1SampledLen
        (sp + 4832#64) sp (spqrSendPlacedEntry + 8532#64) g ⟨uc, sendingCt1, receivingEk⟩ hsub_len
        (F := vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs ++ [0x42#8]) ∗ A.pool lim st s ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (hinv0.trans hinv1.1) (by rw [← hpack]; sep_ac_rfl) ?_
      intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1 hcsm1 hinv_m1 hvm_m1
      rcases hcsm1 with ⟨hm19, hm20, hm21, hm22, hm23, _, hm25, _, hm27, hm28, hmfp, _⟩
      simp only [arm64_norm, hx20] at hm19 hm20 hm21 hm22 hm23 hm25 hm27 hm28 hmfp
      have hpool1 : A.pool lim st s = A.pool lim st sm1 :=
        (A.pool_of_vmPreserved (hinv1.2.trans hvm_m1)).symm
      refine SepWPp.weaken_pre (by rw [hpool1]; exact Entails.of_eq (by sep_ac_rfl))
        (h8532 sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1 hm19 hm20 hm21 hm22 hm23 hm25 hm27 hm28 hmfp hinv_m1)
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1 hm19 hm20 hm21 hm22 hm23 hm25 hm27 hm28 hmfp hinv_m1
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
  apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 451)
  wp_steps
  apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, wp_norm, *])
  intro hinv2
  have hpool2 : A.pool lim st sm1 = A.pool lim st _ := (A.pool_of_vmPreserved hinv2.2).symm
  set bs1 := (bs ++ [0x42#8]) ++
    encodeVarint (BitVec.ofNat 64 (chunkedCt1SampledPBEncodedLen ⟨uc, sendingCt1, receivingEk⟩))
  refine step_send_encode_varint_call_placed A lim st hvarint
    (BitVec.ofNat 64 (chunkedCt1SampledPBEncodedLen ⟨uc, sendingCt1, receivingEk⟩))
    (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 8540#64) (bs ++ [0x42#8]) hfit_var
    (F := chunkedCt1SampledPBPinnedAt A.repAlloc g (sp + 4832#64) ⟨uc, sendingCt1, receivingEk⟩ ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hinv_m1.trans hinv2.1) (by rw [hpool2]; sep_ac_rfl) ?_
  intro sm2 hpcm2 hrunm2 hspm2 htrm2 hcsm2 hinv_m2
  rcases hcsm2 with ⟨hm2_19, hm2_20, hm2_21, hm2_22, hm2_23, _, hm2_25, _, hm2_27, hm2_28, hm2_fp, _⟩
  simp only [arm64_norm, hm19, hm20, hm21, hm22, hm23, hm25, hm27, hm28, hmfp]
    at hm2_19 hm2_20 hm2_21 hm2_22 hm2_23 hm2_25 hm2_27 hm2_28 hm2_fp
  have ⟨h4960, h5016⟩ : (sp + 4832#64) + 128#64 = sp + 4960#64 ∧
      (sp + 4832#64) + 184#64 = sp + 5016#64 := ⟨by bv_omega, by bv_omega⟩
  refine SepWPp.weaken_pre
    (P' := ((optCt1SentPBPinnedAt A.repAlloc g.uc (sp + 4832#64) uc ∗
      optPolynomialEncoderPBPinnedAt A.repAlloc g.sendingCt1 (sp + 4960#64) sendingCt1 ∗
      optPolynomialDecoderPBPinnedAt A.repAlloc g.receivingEk (sp + 5016#64) receivingEk) ∗
      vecU8At A.repAlloc (sp + 1424#64) cap ptr bs1 ∗ A.pool lim st sm2 ∗
      stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (Entails.of_eq (by dsimp +zetaDelta only [chunkedCt1SampledPBPinnedAt, bs1]; rw [h4960, h5016]; sep_ac_rfl)) ?_
  refine sepWPp_extract_pure
    (((optCt1SentCap g.uc uc + 1#64 == 0#64) = !uc.isSome ∧
      (optCt1SentCap g.uc uc + 1#64 != 0#64) = uc.isSome) ∧
     ((optPolyEncCap g.sendingCt1 sendingCt1 + 1#64 == 0#64) = !sendingCt1.isSome ∧
      (optPolyEncCap g.sendingCt1 sendingCt1 + 1#64 != 0#64) = sendingCt1.isSome) ∧
     ((optPolyDecCap g.receivingEk receivingEk + 1#64 == 0#64) = !receivingEk.isSome ∧
      (optPolyDecCap g.receivingEk receivingEk + 1#64 != 0#64) = receivingEk.isSome))
    (fun R' hm =>
      ⟨optCt1SentPBPinnedAt_cap_bounds (p := sp + 4832#64)
        (R := optPolynomialEncoderPBPinnedAt A.repAlloc g.sendingCt1 (sp + 4960#64) sendingCt1 ∗
          optPolynomialDecoderPBPinnedAt A.repAlloc g.receivingEk (sp + 5016#64) receivingEk ∗
          vecU8At A.repAlloc (sp + 1424#64) cap ptr bs1 ∗ A.pool lim st sm2 ∗
          stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm),
       optPolynomialEncoderPBPinnedAt_cap_bounds (p := sp + 4960#64)
        (R := optCt1SentPBPinnedAt A.repAlloc g.uc (sp + 4832#64) uc ∗
          optPolynomialDecoderPBPinnedAt A.repAlloc g.receivingEk (sp + 5016#64) receivingEk ∗
          vecU8At A.repAlloc (sp + 1424#64) cap ptr bs1 ∗ A.pool lim st sm2 ∗
          stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm),
       optPolynomialDecoderPBPinnedAt_cap_bounds (p := sp + 5016#64)
        (R := optCt1SentPBPinnedAt A.repAlloc g.uc (sp + 4832#64) uc ∗
          optPolynomialEncoderPBPinnedAt A.repAlloc g.sendingCt1 (sp + 4960#64) sendingCt1 ∗
          vecU8At A.repAlloc (sp + 1424#64) cap ptr bs1 ∗ A.pool lim st sm2 ∗
          stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm)⟩)
    fun ⟨⟨hcap_uc_beq, hcap_uc_bne⟩, ⟨hcap_enc_beq, hcap_enc_bne⟩, ⟨hcap_dec_beq, hcap_dec_bne⟩⟩ => ?_
  set bs2 := bs1 ++ encodeOptMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 uc
  suffices h8560 : ∀ sm3 : State,
      sm3.pc = spqrSendPlacedEntry + 8560#64 → sm3.status = .Running → sm3.sp = sp → sm3.trace = s0.trace →
      sm3.readReg64 .x19 = s.readReg64 .x19 → sm3.readReg64 .x21 = s.readReg64 .x21 →
      sm3.readReg64 .x23 = s.readReg64 .x23 → sm3.readReg64 .x25 = s.readReg64 .x25 →
      sm3.readReg64 .x27 = s.readReg64 .x27 → sm3.readReg64 .x28 = s.readReg64 .x28 →
      sm3.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm3 →
      SepWPp (spqrSendPlacedProg ext) ret sm3
        (((optCt1SentPBPinnedAt A.repAlloc g.uc (sp + 4832#64) uc ∗
          optPolynomialEncoderPBPinnedAt A.repAlloc g.sendingCt1 (sp + 4960#64) sendingCt1 ∗
          optPolynomialDecoderPBPinnedAt A.repAlloc g.receivingEk (sp + 5016#64) receivingEk) ∗
          vecU8At A.repAlloc (sp + 1424#64) cap ptr bs2 ∗ A.pool lim st sm3 ∗
          stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom by
    cases uc with
    | none =>
      simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
      dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
      apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 8560#64)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv3
      have hpool3 : A.pool lim st sm2 = A.pool lim st _ := (A.pool_of_vmPreserved hinv3.2).symm
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h8560 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (hinv_m2.trans hinv3.1))
      rw [hpool3]
      simp +zetaDelta only [bs2, bs1, encodeOptMessage, List.append_nil]
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
      intro hinv3
      have hpool3 : A.pool lim st sm2 = A.pool lim st _ := (A.pool_of_vmPreserved hinv3.2).symm
      refine step_send_encode_ct1Sent_budget_call_placed A lim st ext hct1SentEnc
        (sp + 4832#64) (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 8560#64) g.uc u bs1 hfit_uc
        (F := optPolynomialEncoderPBPinnedAt A.repAlloc g.sendingCt1 (sp + 4960#64) sendingCt1 ∗
          optPolynomialDecoderPBPinnedAt A.repAlloc g.receivingEk (sp + 5016#64) receivingEk ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m2.trans hinv3.1)
        (by dsimp +zetaDelta only [optCt1SentPBPinnedAt, bs1]; rw [hpool3]; sep_ac_rfl) ?_
      intro sm3 hpcm3 hrunm3 hspm3 htrm3 hcsm3 hinv_m3
      rcases hcsm3 with ⟨hm3_19, _, hm3_21, _, hm3_23, _, hm3_25, _, hm3_27, hm3_28, hm3_fp, _⟩
      simp only [arm64_norm, hm2_19, hm2_21, hm2_23, hm2_25, hm2_27, hm2_28, hm2_fp]
        at hm3_19 hm3_21 hm3_23 hm3_25 hm3_27 hm3_28 hm3_fp
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h8560 sm3 hpcm3 hrunm3 hspm3 htrm3 hm3_19 hm3_21 hm3_23 hm3_25 hm3_27 hm3_28 hm3_fp hinv_m3)
      simp +zetaDelta only [bs2, bs1, encodeOptMessage, optCt1SentPBPinnedAt]; sep_ac_rfl
  intro sm3 hpcm3 hrunm3 hspm3 htrm3 hx19_3 hx21_3 hx23_3 hx25_3 hx27_3 hx28_3 hfp_3 hinv_3
  set bs3 := bs2 ++ encodeOptMessage PolynomialEncoder.encodeRaw 2#32 sendingCt1
  suffices h8592 : ∀ sm4 : State,
      sm4.pc = spqrSendPlacedEntry + 8592#64 → sm4.status = .Running → sm4.sp = sp → sm4.trace = s0.trace →
      sm4.readReg64 .x19 = s.readReg64 .x19 → sm4.readReg64 .x20 = sp + 4704#64 →
      sm4.readReg64 .x21 = s.readReg64 .x21 → sm4.readReg64 .x23 = s.readReg64 .x23 →
      sm4.readReg64 .x25 = s.readReg64 .x25 → sm4.readReg64 .x27 = s.readReg64 .x27 →
      sm4.readReg64 .x28 = s.readReg64 .x28 → sm4.readReg64 .fp = s.readReg64 .fp →
      StepInv s0 sm4 →
      SepWPp (spqrSendPlacedProg ext) ret sm4
        (((optCt1SentPBPinnedAt A.repAlloc g.uc (sp + 4832#64) uc ∗
          optPolynomialEncoderPBPinnedAt A.repAlloc g.sendingCt1 (sp + 4960#64) sendingCt1 ∗
          optPolynomialDecoderPBPinnedAt A.repAlloc g.receivingEk (sp + 5016#64) receivingEk) ∗
          vecU8At A.repAlloc (sp + 1424#64) cap ptr bs3 ∗ A.pool lim st sm4 ∗
          stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom by
    cases sendingCt1 with
    | none =>
      rw [optPolynomialEncoderPBPinnedAt_eq A.repAlloc g.sendingCt1 (sp + 4960#64) none]
      simp only [Option.isSome_none, Bool.not_false] at hcap_enc_beq hcap_enc_bne
      dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
      apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 8592#64)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv4
      have hpool4 : A.pool lim st sm3 = A.pool lim st _ := (A.pool_of_vmPreserved hinv4.2).symm
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h8592 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_3.trans hinv4.1))
      rw [← optPolynomialEncoderPBPinnedAt_eq A.repAlloc g.sendingCt1 (sp + 4960#64) none, hpool4]
      simp +zetaDelta only [bs3, bs2, bs1, encodeOptMessage, List.append_nil]
    | some enc =>
      rw [optPolynomialEncoderPBPinnedAt_eq A.repAlloc g.sendingCt1 (sp + 4960#64) (some enc)]
      simp only [Option.isSome_some, Bool.not_true] at hcap_enc_beq hcap_enc_bne
      have hfit_enc :
          bs2.length + (encodeMessage PolynomialEncoder.encodeRaw 2#32 enc).length ≤ cap.toNat := by
        simp +zetaDelta only [bs2, bs1, encodeOptMessage, List.length_append, List.length_singleton] at hfit ⊢
        omega
      dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
      apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 456)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv4
      have hpool4 : A.pool lim st sm3 = A.pool lim st _ := (A.pool_of_vmPreserved hinv4.2).symm
      rw [← optPolynomialEncoderPBPinnedAt_eq A.repAlloc g.sendingCt1 (sp + 4960#64) (some enc)]
      refine step_send_encode_polyEncoder_budget_call_placed A lim st ext hpolyEnc
        (sp + 4960#64) (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 8592#64) g.sendingCt1 enc bs2 hfit_enc
        (F := optCt1SentPBPinnedAt A.repAlloc g.uc (sp + 4832#64) uc ∗
          optPolynomialDecoderPBPinnedAt A.repAlloc g.receivingEk (sp + 5016#64) receivingEk ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_3.trans hinv4.1)
        (by dsimp +zetaDelta only [optPolynomialEncoderPBPinnedAt, bs2, bs1]; rw [hpool4]; sep_ac_rfl) ?_
      intro sm4 hpcm4 hrunm4 hspm4 htrm4 hcsm4 hinv_m4
      rcases hcsm4 with ⟨hm4_19, hm4_20, hm4_21, _, hm4_23, _, hm4_25, _, hm4_27, hm4_28, hm4_fp, _⟩
      simp only [arm64_norm, hx19_3, hx21_3, hx23_3, hx25_3, hx27_3, hx28_3, hfp_3]
        at hm4_19 hm4_20 hm4_21 hm4_23 hm4_25 hm4_27 hm4_28 hm4_fp
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h8592 sm4 hpcm4 hrunm4 hspm4 htrm4 hm4_19 hm4_20 hm4_21 hm4_23 hm4_25 hm4_27 hm4_28 hm4_fp hinv_m4)
      simp +zetaDelta only [bs3, bs2, bs1, encodeOptMessage, optPolynomialEncoderPBPinnedAt]; sep_ac_rfl
  intro sm4 hpcm4 hrunm4 hspm4 htrm4 hx19_4 hx20_4 hx21_4 hx23_4 hx25_4 hx27_4 hx28_4 hfp_4 hinv_4
  cases receivingEk with
  | none =>
    rw [optPolynomialDecoderPBPinnedAt_eq A.repAlloc g.receivingEk (sp + 5016#64) none]
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
    rw [← optPolynomialDecoderPBPinnedAt_eq A.repAlloc g.receivingEk (sp + 5016#64) none,
      encodeInnerState_ct1Sampled_eq, hpool5]
    simp +zetaDelta only [bs3, bs2, bs1, encodeOptMessage, chunkedCt1SampledPBPinnedAt,
      List.append_nil, h4960, h5016, List.append_assoc]
  | some dec =>
    rw [optPolynomialDecoderPBPinnedAt_eq A.repAlloc g.receivingEk (sp + 5016#64) (some dec)]
    simp only [Option.isSome_some, Bool.not_true] at hcap_dec_beq hcap_dec_bne
    have hfit_dec :
        bs3.length + (encodeMessage PolynomialDecoder.encodeRaw 3#32 dec).length ≤ cap.toNat := by
      simp +zetaDelta only [bs3, bs2, bs1, encodeOptMessage, List.length_append, List.length_singleton] at hfit ⊢
      omega
    dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
    apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 10352#64)
    wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv5
    have hpool5 : A.pool lim st sm4 = A.pool lim st _ := (A.pool_of_vmPreserved hinv5.2).symm
    rw [← optPolynomialDecoderPBPinnedAt_eq A.repAlloc g.receivingEk (sp + 5016#64) (some dec)]
    refine step_send_tail_10352_polyDec3_placed A lim st ext hpolyDec
      (sp + 5016#64) sp cap ptr g.receivingEk dec bs3 hfit_dec halign
      (F := optCt1SentPBPinnedAt A.repAlloc g.uc (sp + 4832#64) uc ∗
        optPolynomialEncoderPBPinnedAt A.repAlloc g.sendingCt1 (sp + 4960#64) sendingCt1 ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hinv_4.trans hinv5.1)
      (by dsimp +zetaDelta only [optPolynomialDecoderPBPinnedAt, bs3, bs2, bs1]; rw [hpool5]; sep_ac_rfl) ?_
    intro sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp hinv_m5
    simp only [arm64_norm, hx19_4, hx21_4, hx23_4, hx25_4, hx27_4, hx28_4, hfp_4]
      at hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp
    refine SepWPp.weaken_pre (Entails.of_eq ?_)
      (hnext sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp hinv_m5)
    rw [encodeInnerState_ct1Sampled_eq]
    simp +zetaDelta only [bs3, bs2, bs1, encodeOptMessage,
      chunkedCt1SampledPBPinnedAt, optPolynomialDecoderPBPinnedAt,
      h4960, h5016, List.append_assoc]; sep_ac_rfl

/-! ## 4. Variant `idx = 4`: `.ekSentCt1Received` (`+7784 .. +10352`) -/

/-- Step `+7784 .. +6216` for `is = .ekSentCt1Received v`, threading `A.pool lim st`. -/
theorem step_send_v1_ekSentCt1Received_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    {s0 s : State}
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
    (sp cap ptr w25 : BitVec 64) (g : Unchunked4PBGhost × PolynomialDecoderPBGhost)
    (v : V1State.Chunked.EkSentCt1Received) (bs : List (BitVec 8))
    (hv_len : v1StatePBEncodedLen ⟨some (.ekSentCt1Received v)⟩ < 2 ^ 64)
    (hfit : bs.length + (V1State.InnerState.encode (.ekSentCt1Received v)).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = spqrSendPlacedEntry + 7784#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace) (hinv0 : StepInv s0 s)
    (hP : P = ((optEkSentCt1ReceivedPBPinnedAt A.repAlloc g.1 (sp + 4840#64) v.uc ∗
      optPolynomialDecoderPBPinnedAt A.repAlloc g.2 (sp + 4944#64) v.receivingCt2) ∗
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
          optPolynomialDecoderPBPinnedAt A.repAlloc g.2 (sp + 4944#64) v.receivingCt2) ∗
          ((sp + 16#64) ↦₆₄ w25) ∗
          vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs ++ V1State.InnerState.encode (.ekSentCt1Received v)) ∗
          A.pool lim st sm ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  subst hP
  rcases v with ⟨uc, receivingCt2⟩
  rw [encodeInnerState_ekSentCt1Received_eq] at hfit
  simp only [List.length_append, List.length_singleton] at hfit
  have hsub_len : v1StateInnerPayloadEncodedLen (.ekSentCt1Received ⟨uc, receivingCt2⟩) < 2 ^ 64 := by
    dsimp only [v1StatePBEncodedLen] at hv_len; omega
  have hlt1 : bs.length < cap.toNat := by omega
  have hfit_var : (bs ++ [0x2a#8]).length +
      (encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ekSentCt1Received ⟨uc, receivingCt2⟩)))).length ≤
        cap.toNat := by
    simp only [List.length_append, List.length_singleton]; omega
  refine sepWPp_extract_vecU8At_bounds (v := sp + 1424#64) (cap := cap) (ptr := ptr) (bs := bs)
    (F := optEkSentCt1ReceivedPBPinnedAt A.repAlloc g.1 (sp + 4840#64) uc ∗
      optPolynomialDecoderPBPinnedAt A.repAlloc g.2 (sp + 4944#64) receivingCt2 ∗
      ((sp + 16#64) ↦₆₄ w25) ∗ A.pool lim st s ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F)
    (by sep_ac_rfl) fun _ hcap hptr => ?_
  refine sepWPp_extract_pure
    (((optEkSentCt1ReceivedCap g.1 uc + 1#64 == 0#64) = !uc.isSome ∧
      (optEkSentCt1ReceivedCap g.1 uc + 1#64 != 0#64) = uc.isSome) ∧
     ((optPolyDecCap g.2 receivingCt2 + 1#64 == 0#64) = !receivingCt2.isSome ∧
      (optPolyDecCap g.2 receivingCt2 + 1#64 != 0#64) = receivingCt2.isSome))
    (fun R' hm =>
      ⟨optEkSentCt1ReceivedPBPinnedAt_cap_bounds (p := sp + 4840#64)
        (R := optPolynomialDecoderPBPinnedAt A.repAlloc g.2 (sp + 4944#64) receivingCt2 ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A.repAlloc (sp + 1424#64) cap ptr bs ∗
          A.pool lim st s ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm),
       optPolynomialDecoderPBPinnedAt_cap_bounds (p := sp + 4944#64)
        (R := optEkSentCt1ReceivedPBPinnedAt A.repAlloc g.1 (sp + 4840#64) uc ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A.repAlloc (sp + 1424#64) cap ptr bs ∗
          A.pool lim st s ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm)⟩)
    fun ⟨⟨hcap_uc_beq, hcap_uc_bne⟩, ⟨hcap_dec_beq, hcap_dec_bne⟩⟩ => ?_
  have hbeq_false := cap_beq_len_false_of_lt hlt1 hcap
  have ⟨h1432, h1440⟩ : (sp + 1424#64) + 8#64 = sp + 1432#64 ∧
      (sp + 1424#64) + 16#64 = sp + 1440#64 := ⟨by bv_omega, by bv_omega⟩
  have hpack := vecU8At_pack_one A.repAlloc (sp + 1424#64) cap ptr bs 0x2a#8 hlt1 hcap hptr
  simp only [arm64_norm, h1432, h1440] at hpack
  suffices h9492 : ∀ sm1 : State,
      sm1.pc = spqrSendPlacedEntry + 9492#64 → sm1.status = .Running → sm1.sp = sp → sm1.trace = s0.trace →
      sm1.readReg64 .x19 = s.readReg64 .x19 → sm1.readReg64 .x20 = sp + 4704#64 →
      sm1.readReg64 .x21 = s.readReg64 .x21 → sm1.readReg64 .x22 = optEkSentCt1ReceivedCap g.1 uc →
      sm1.readReg64 .x23 = s.readReg64 .x23 →
      sm1.readReg64 .x26 = BitVec.ofNat 64 (optEkSentCt1ReceivedPBFieldEncodedLen uc) →
      sm1.readReg64 .x27 = s.readReg64 .x27 → sm1.readReg64 .x28 = s.readReg64 .x28 →
      sm1.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm1 →
      SepWPp (spqrSendPlacedProg ext) ret sm1
        (((optEkSentCt1ReceivedPBPinnedAt A.repAlloc g.1 (sp + 4840#64) uc ∗
          optPolynomialDecoderPBPinnedAt A.repAlloc g.2 (sp + 4944#64) receivingCt2) ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs ++ [0x2a#8]) ∗
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
      apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 9492#64)
      by_vm_steps
        wp_steps
        apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv1
        have hpool1 : A.pool lim st s = A.pool lim st _ := (A.pool_of_vmPreserved hinv1.2).symm
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (h9492 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *])
            (by simp only [optEkSentCt1ReceivedPBFieldEncodedLen, arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (hinv0.trans hinv1.1))
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
          (sp + 4840#64) sp (spqrSendPlacedEntry + 7848#64) g.1 u hu_fit
          (F := optPolynomialDecoderPBPinnedAt A.repAlloc g.2 (sp + 4944#64) receivingCt2 ∗
            ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs ++ [0x2a#8]) ∗
            A.pool lim st s ∗ F)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
          (hinv0.trans hinv1.1) (by rw [← hpack]; dsimp only [optEkSentCt1ReceivedPBPinnedAt]; sep_ac_rfl) ?_
        intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1 hcsm1 hinv_m1 hvm_m1
        rcases hcsm1 with ⟨hm19, hm20, hm21, hm22, hm23, _, _, _, hm27, hm28, hmfp, _⟩
        simp only [arm64_norm] at hm19 hm20 hm21 hm22 hm23 hm27 hm28 hmfp
        dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
        apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 9492#64)
        wp_steps
        apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv2
        have hpool2 : A.pool lim st s = A.pool lim st _ :=
          (A.pool_of_vmPreserved (hinv1.2.trans (hvm_m1.trans hinv2.2))).symm
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (h9492 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (hinv_m1.trans hinv2.1))
        dsimp only [optEkSentCt1ReceivedPBPinnedAt]; rw [hpool2]; sep_ac_rfl
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx26_1 hx27_1 hx28_1 hfp_1 hinv_1
  suffices h10300 : ∀ sm2 : State,
      sm2.pc = spqrSendPlacedEntry + 10300#64 → sm2.status = .Running → sm2.sp = sp → sm2.trace = s0.trace →
      sm2.readReg64 .x8 = BitVec.ofNat 64 (optPolynomialDecoderPBFieldEncodedLen receivingCt2) →
      sm2.readReg64 .x19 = s.readReg64 .x19 → sm2.readReg64 .x20 = sp + 4704#64 →
      sm2.readReg64 .x21 = s.readReg64 .x21 → sm2.readReg64 .x22 = optEkSentCt1ReceivedCap g.1 uc →
      sm2.readReg64 .x23 = s.readReg64 .x23 → sm2.readReg64 .x24 = sp + 4704#64 →
      sm2.readReg64 .x25 = optPolyDecCap g.2 receivingCt2 →
      sm2.readReg64 .x26 = BitVec.ofNat 64 (optEkSentCt1ReceivedPBFieldEncodedLen uc) →
      sm2.readReg64 .x27 = s.readReg64 .x27 → sm2.readReg64 .x28 = s.readReg64 .x28 →
      sm2.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm2 →
      SepWPp (spqrSendPlacedProg ext) ret sm2
        (((optEkSentCt1ReceivedPBPinnedAt A.repAlloc g.1 (sp + 4840#64) uc ∗
          optPolynomialDecoderPBPinnedAt A.repAlloc g.2 (sp + 4944#64) receivingCt2) ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs ++ [0x2a#8]) ∗
          A.pool lim st sm2 ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom by
    cases receivingCt2 with
    | none =>
      rw [optPolynomialDecoderPBPinnedAt_eq A.repAlloc g.2 (sp + 4944#64) none]
      simp only [Option.isSome_none, Bool.not_false] at hcap_dec_beq hcap_dec_bne
      dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
      apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 10300#64)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv2
      have hpool2 : A.pool lim st sm1 = A.pool lim st _ := (A.pool_of_vmPreserved hinv2.2).symm
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h10300 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [optPolynomialDecoderPBFieldEncodedLen, arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (hinv_1.trans hinv2.1))
      rw [← optPolynomialDecoderPBPinnedAt_eq A.repAlloc g.2 (sp + 4944#64) none, hpool2]
    | some dec =>
      rw [optPolynomialDecoderPBPinnedAt_eq A.repAlloc g.2 (sp + 4944#64) (some dec)]
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
      rw [← optPolynomialDecoderPBPinnedAt_eq A.repAlloc g.2 (sp + 4944#64) (some dec)]
      refine step_send_leaf_encLen16_call_placed hres ext
        (polynomialDecoderPBPinnedAt A.repAlloc) polynomialDecoderPBEncodedLen hpolyDecLen
        (sp + 4944#64) sp (spqrSendPlacedEntry + 9520#64) g.2 dec hdec_fit
        (F := optEkSentCt1ReceivedPBPinnedAt A.repAlloc g.1 (sp + 4840#64) uc ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs ++ [0x2a#8]) ∗
          A.pool lim st sm1 ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (hinv_1.trans hinv2.1) (by dsimp only [optPolynomialDecoderPBPinnedAt]; sep_ac_rfl) ?_
      intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx0m2 hcsm2 hinv_m2 hvm_m2
      rcases hcsm2 with ⟨hm2_19, hm2_20, hm2_21, hm2_22, hm2_23, hm2_24, hm2_25, hm2_26, hm2_27, hm2_28, hm2_fp, _⟩
      simp only [arm64_norm, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx26_1, hx27_1, hx28_1, hfp_1]
        at hm2_19 hm2_20 hm2_21 hm2_22 hm2_23 hm2_24 hm2_25 hm2_26 hm2_27 hm2_28 hm2_fp
      dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
      apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 10300#64)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv3
      have hpool3 : A.pool lim st sm1 = A.pool lim st _ :=
        (A.pool_of_vmPreserved (hinv2.2.trans (hvm_m2.trans hinv3.2))).symm
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h10300 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hinv_m2.trans hinv3.1))
      dsimp only [optPolynomialDecoderPBPinnedAt]; rw [hpool3]; sep_ac_rfl
  intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx8_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hinv_2
  have ⟨hadd_sum, hult_sum, hule_sum, hult_sum2, hule_sum2⟩ := adds_no_overflow_of_eq
      (a := optPolynomialDecoderPBFieldEncodedLen receivingCt2)
      (b := optEkSentCt1ReceivedPBFieldEncodedLen uc)
      (c := v1StateInnerPayloadEncodedLen (.ekSentCt1Received ⟨uc, receivingCt2⟩))
      rfl hsub_len
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
  apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 451)
  wp_steps
  apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, wp_norm, *])
  intro hinv3
  have hpool3 : A.pool lim st sm2 = A.pool lim st _ := (A.pool_of_vmPreserved hinv3.2).symm
  set bs1 := (bs ++ [0x2a#8]) ++
    encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ekSentCt1Received ⟨uc, receivingCt2⟩)))
  refine step_send_encode_varint_call_placed A lim st hvarint
    (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ekSentCt1Received ⟨uc, receivingCt2⟩)))
    (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 10316#64) (bs ++ [0x2a#8]) hfit_var
    (F := (optEkSentCt1ReceivedPBPinnedAt A.repAlloc g.1 (sp + 4840#64) uc ∗
      optPolynomialDecoderPBPinnedAt A.repAlloc g.2 (sp + 4944#64) receivingCt2) ∗
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
  suffices h10336 : ∀ sm4 : State,
      sm4.pc = spqrSendPlacedEntry + 10336#64 → sm4.status = .Running → sm4.sp = sp → sm4.trace = s0.trace →
      sm4.readReg64 .x19 = s.readReg64 .x19 → sm4.readReg64 .x21 = s.readReg64 .x21 →
      sm4.readReg64 .x23 = s.readReg64 .x23 → sm4.readReg64 .x24 = sp + 4704#64 →
      sm4.readReg64 .x25 = optPolyDecCap g.2 receivingCt2 →
      sm4.readReg64 .x27 = s.readReg64 .x27 → sm4.readReg64 .x28 = s.readReg64 .x28 →
      sm4.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm4 →
      SepWPp (spqrSendPlacedProg ext) ret sm4
        (((optEkSentCt1ReceivedPBPinnedAt A.repAlloc g.1 (sp + 4840#64) uc ∗
          optPolynomialDecoderPBPinnedAt A.repAlloc g.2 (sp + 4944#64) receivingCt2) ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A.repAlloc (sp + 1424#64) cap ptr bs2 ∗
          A.pool lim st sm4 ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom by
    cases uc with
    | none =>
      simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
      dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
      apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 10336#64)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv4
      have hpool4 : A.pool lim st sm3 = A.pool lim st _ := (A.pool_of_vmPreserved hinv4.2).symm
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h10336 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
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
        (sp + 4840#64) (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 10336#64) g.1 u bs1 hfit_uc
        (F := optPolynomialDecoderPBPinnedAt A.repAlloc g.2 (sp + 4944#64) receivingCt2 ∗
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
        (h10336 sm4 hpcm4 hrunm4 hspm4 htrm4 hm4_19 hm4_21 hm4_23 hm4_24 hm4_25 hm4_27 hm4_28 hm4_fp hinv_m4)
      simp +zetaDelta only [bs2, bs1, encodeOptMessage, optEkSentCt1ReceivedPBPinnedAt]; sep_ac_rfl
  intro sm4 hpcm4 hrunm4 hspm4 htrm4 hx19_4 hx21_4 hx23_4 hx24_4 hx25_4 hx27_4 hx28_4 hfp_4 hinv_4
  cases receivingCt2 with
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
    rw [encodeInnerState_ekSentCt1Received_eq, hpool5]
    simp +zetaDelta only [bs2, bs1, encodeOptMessage, List.append_nil, List.append_assoc]
  | some dec =>
    simp only [Option.isSome_some, Bool.not_true] at hcap_dec_beq hcap_dec_bne
    have hfit_dec :
        bs2.length + (encodeMessage PolynomialDecoder.encodeRaw 3#32 dec).length ≤ cap.toNat := by
      simp +zetaDelta only [bs2, bs1, encodeOptMessage, List.length_append, List.length_singleton] at hfit ⊢
      omega
    dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
    apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 10352#64)
    wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv5
    have hpool5 : A.pool lim st sm4 = A.pool lim st _ := (A.pool_of_vmPreserved hinv5.2).symm
    refine step_send_tail_10352_polyDec3_placed A lim st ext hpolyDec
      (sp + 4944#64) sp cap ptr g.2 dec bs2 hfit_dec halign
      (F := optEkSentCt1ReceivedPBPinnedAt A.repAlloc g.1 (sp + 4840#64) uc ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hinv_4.trans hinv5.1)
      (by dsimp +zetaDelta only [optPolynomialDecoderPBPinnedAt, bs2, bs1]; rw [hpool5]; sep_ac_rfl) ?_
    intro sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp hinv_m5
    simp only [arm64_norm, hx19_4, hx21_4, hx23_4, hx27_4, hx28_4, hfp_4]
      at hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp
    refine SepWPp.weaken_pre (Entails.of_eq ?_)
      (hnext sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp hinv_m5)
    rw [encodeInnerState_ekSentCt1Received_eq]
    simp +zetaDelta only [bs2, bs1, encodeOptMessage,
      optPolynomialDecoderPBPinnedAt, List.append_assoc]; sep_ac_rfl

end LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerChunked1PlacedBudgetAux

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerChunked3Placed
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerChunked3aPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonBudget
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public meta import Lean -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked1
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked2
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked3a
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.V1StateHelpers
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesVnEncode
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Phase 3e (Part 3b Aux): `V1State` Variant `keysSampled` (`idx = 1`)

Threads `RustCliAllocBudget` and `VmPreserved` through `V1State::encode_raw` arm
`keysSampled` (`+8612..+10912`) in Block `427`.
-/

@[expose] public section

set_option linter.style.longLine false
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerChunked3PlacedBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open CryptoVerification (LibsignalPlacement libsignalSessionCode lsmpl lsρ)
open CryptoVerification.RustHeap (vecHeader vecU8At)
open CryptoVerification.LibsignalSpqrV1
  (PolynomialEncoder ProtoAuthenticator V1State)
open CryptoVerification.LibsignalSpqrV1.Proto
  (encodeBytesField encodeMessage encodeOptMessage encodeUint64Field encodeVarint)
open CryptoVerification.SpqrV1.ProtoRepr
  (PolynomialEncoderPBGhost Unchunked4PBGhost
   headerSentPBEncodedLen headerSentPBPinnedAt
   noneCap_add_two_beq_zero noneCap_add_two_bne_zero
   optAuthCap optAuthenticatorPBPinnedAt optAuthenticatorPBPinnedAt_eq
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
  (StepInv bv_optPolyEnc_some_eq
   cap_beq_len_false_of_lt
   encodeToVecCalleeStackOf encodeVarint_length_pos
   etv2_encodeBytesField_3_eq etv2_encodeBytesField_4_eq
   etv2_encodeInnerState_keysSampled_eq etv2_encodeOptHeaderSent_some_eq
   etv2_encodeUint64Field_1_eq etv2_optAuth_cap_bounds
   etv3_bv_optHeaderSent_some_eq
   noneCap2_add_two_beq_zero noneCap2_add_two_bne_zero
   noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
   optHeaderSentCap optHeaderSentPBPinnedAt_cap_bounds optHeaderSentPBPinnedAt_eq
   optPolyEncCap
   optPolynomialEncoderPBPinnedAt_cap_bounds optPolynomialEncoderPBPinnedAt_eq
   ult_of_lt_of_fit
   vecU8At_expose_one vecU8At_pack_one vecU8At_pack_slice
   withStepInv)
open CryptoVerification.Cli.SpqrV1.Top.Send.CodePlaced (blkPl_427_ρ)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
  (spqrSendPlacedEntry spqrSendPlacedProg)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerHeaderPlacedBudget
  (step_send_encode_auth_call_placed step_send_encode_varint_call_placed
   step_send_leaf_encLen16_call_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerChunked1PlacedBudgetAux
  (sepWPp_extract_pure sepWPp_extract_vecU8At_bounds step_send_tail_11748_polyEnc_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerChunked3aPlacedBudgetAux
  (send3a_step_bytes_varint_placed send3a_step_memcpy_slice_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhaseBudget
  (authEncodeExactSpecOf encodeVarintExactSpecOf etvMemcpyRegionSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsPlacedBudget
  (sepWP_done_tpidr sepWP_done_vm sepWPp_of_sepWP_cs_vm)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonBudget
  (leafEncLen16Spec)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonPlacedBudget
  (etvPolyEncoderBudgetExactSpecOf)

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

local elab "erase_bv64_add_one" : command => Lean.Elab.Command.liftCoreM do
  Lean.Attribute.erase ``CryptoVerification.SpqrV1.Prost.MessageMerge.bv64_ofNat_add_one `simp
  Lean.Attribute.erase ``CryptoVerification.SpqrV1.Prost.MessageMerge.bv64_ofNat_add_one `arm64_norm
erase_bv64_add_one

local syntax "by_vm_steps_safe " tacticSeq : tactic
local elab_rules : tactic
  | `(tactic| by_vm_steps_safe $tac:tacticSeq) => do
    Lean.Elab.Tactic.evalTactic
      (← `(tactic| apply LibsignalBinary.Proofs.Placed.BudgetVmSteps.sepWP_rebase_vmPreserved))
    let g ← Lean.Elab.Tactic.getMainGoal
    g.withContext do
      let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData
      unless ty.getAppFn.isConstOf ``ProofLib.SepWP && ty.getAppNumArgs == 6 do
        throwError "by_vm_steps_safe: expected SepWP"
      let e2 := ty.getArg! 0
      unless e2.getAppFn.isConstOf ``Arm64.Program.withSvc && e2.getAppNumArgs == 2 do
        throwError "by_vm_steps_safe: program is not Program.withSvc"
      let e1 := e2.getArg! 0
      let ty1 := Lean.mkAppN ty.getAppFn
        #[e1, ty.getArg! 1, ty.getArg! 2, ty.getArg! 3, ty.getArg! 4, ty.getArg! 5]
      let g1 ← Lean.Meta.mkFreshExprMVar ty1
      let savedGoals ← Lean.Elab.Tactic.getGoals
      Lean.Elab.Tactic.setGoals [g1.mvarId!]
      Lean.Elab.Tactic.evalTactic (← `(tactic| ($tac)))
      let rem ← Lean.Elab.Tactic.getGoals
      unless rem.isEmpty do
        throwError "by_vm_steps_safe: inner tactic left {rem.length} unsolved goal(s)"
      Lean.Elab.Tactic.setGoals savedGoals.tail!
      let prf1 ← Lean.instantiateMVars g1
      let prf2 := prf1.replace fun sub =>
        if sub.eqv e2 then some e2 else if sub.eqv e1 then some e2 else none
      g.assign prf2

/-! ## 1. Variant `idx = 1`: `.keysSampled` (`+8612 .. +10916`) -/

set_option maxHeartbeats 800000 in
theorem send3_step_keysSampled_some_1_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State)) {s0 s : State}
    (hhsLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 492)
      (withStepInv s0 (leafEncLen16Spec (headerSentPBPinnedAt A.repAlloc) headerSentPBEncodedLen)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hauthEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 454)
      (withStepInv s0 (authEncodeExactSpecOf resStack A lim)))
    (sp cap ptr w25 : BitVec 64) (g : Unchunked4PBGhost) (u : V1State.Unchunked.HeaderSent)
    (bs : List (BitVec 8))
    (hu_lt : headerSentPBEncodedLen u < 2 ^ 64)
    (hfit : bs.length + (encodeOptMessage V1State.Unchunked.HeaderSent.encodeRaw 1#32 (some u)).length ≤
      cap.toNat)
    (hcap : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0) (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = spqrSendPlacedEntry + 10520#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx22 : s.readReg64 .x22 = sp + 4704#64) (hx25 : s.readReg64 .x25 = w25)
    (hx26 : s.readReg64 .x26 = sp + 4704#64) (hinv0 : StepInv s0 s)
    (hP : P = (headerSentPBPinnedAt A.repAlloc g (sp + 4840#64) u ∗ ((sp + 16#64) ↦₆₄ w25) ∗
      vecU8At A.repAlloc (sp + 1424#64) cap ptr bs ∗ A.pool lim st s ∗
      stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (h10656 : ∀ sm4 : State,
      sm4.pc = spqrSendPlacedEntry + 10656#64 → sm4.status = .Running → sm4.sp = sp → sm4.trace = s0.trace →
      sm4.readReg64 .x19 = s.readReg64 .x19 → sm4.readReg64 .x20 = s.readReg64 .x20 →
      sm4.readReg64 .x21 = s.readReg64 .x21 → sm4.readReg64 .x23 = s.readReg64 .x23 →
      sm4.readReg64 .x25 = w25 → sm4.readReg64 .x26 = sp + 4704#64 →
      sm4.readReg64 .x27 = s.readReg64 .x27 → sm4.readReg64 .x28 = s.readReg64 .x28 →
      sm4.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm4 →
      SepWPp (spqrSendPlacedProg ext) ret sm4
        (((vecU8At A.repAlloc (sp + 4840#64) g.f3.cap g.f3.ptr u.ek ∗
            vecU8At A.repAlloc (sp + 4864#64) g.f4.cap g.f4.ptr u.dk ∗
            optAuthenticatorPBPinnedAt A.repAlloc g.auth (sp + 4888#64) u.auth ∗
            ((sp + 4936#64) ↦₆₄ u.epoch)) ∗
          ((sp + 16#64) ↦₆₄ w25) ∗
          vecU8At A.repAlloc (sp + 1424#64) cap ptr
            ((((bs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 (headerSentPBEncodedLen u))) ++
              encodeUint64Field 1#32 u.epoch) ++ encodeOptMessage ProtoAuthenticator.encodeRaw 2#32 u.auth) ∗
          A.pool lim st sm4 ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  subst hP
  have ⟨h1432, h1440⟩ : (sp + 1424#64) + 8#64 = sp + 1432#64 ∧ (sp + 1424#64) + 16#64 = sp + 1440#64 :=
    ⟨by bv_omega, by bv_omega⟩
  rw [etv2_encodeOptHeaderSent_some_eq] at hfit; simp only [List.length_append, List.length_singleton] at hfit
  have hlt1 : bs.length < cap.toNat := by omega
  have hbeq1 := cap_beq_len_false_of_lt hlt1 hcap
  rw [vecU8At_expose_one A.repAlloc (sp + 1424#64) cap ptr bs hlt1 hcap hptr, h1432, h1440]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b0 => ?_
  (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
  apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 492)
  by_vm_steps_safe
    wp_steps
    apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv1
    have hpack1 := vecU8At_pack_one A.repAlloc (sp + 1424#64) cap ptr bs 0x0a#8 hlt1 hcap hptr
    rw [h1432, h1440] at hpack1
    refine step_send_leaf_encLen16_call_placed hres ext (headerSentPBPinnedAt A.repAlloc)
      headerSentPBEncodedLen hhsLen (sp + 4840#64) sp (spqrSendPlacedEntry + 10564#64) g u hu_lt
      (F := ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs ++ [0x0a#8]) ∗
        A.pool lim st s ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
      (hinv0.trans hinv1.1) (by rw [← hpack1]; (try sep_ac_rfl)) ?_
    intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1
      ⟨hm19, hm20, hm21, hm22, hm23, _, hm25, hm26, hm27, hm28, hmfp, _⟩ hinv_m1 hvm_m1
    simp only [arm64_norm, hx22, hx25, hx26] at hm19 hm20 hm21 hm22 hm23 hm25 hm26 hm27 hm28 hmfp
    (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
    apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 451)
    wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv2
    have hpool2 : A.pool lim st s = A.pool lim st _ :=
      (A.pool_of_vmPreserved (hinv1.2.trans (hvm_m1.trans hinv2.2))).symm
    set bs1 := (bs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 (headerSentPBEncodedLen u))
    have hfit_var : (bs ++ [0x0a#8]).length +
        (encodeVarint (BitVec.ofNat 64 (headerSentPBEncodedLen u))).length ≤ cap.toNat := by
      simp only [List.length_append, List.length_singleton]; omega
    refine step_send_encode_varint_call_placed A lim st hvarint
      (BitVec.ofNat 64 (headerSentPBEncodedLen u)) (sp + 1424#64) cap ptr sp
      (spqrSendPlacedEntry + 10572#64) (bs ++ [0x0a#8]) hfit_var
      (F := headerSentPBPinnedAt A.repAlloc g (sp + 4840#64) u ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hinv_m1.trans hinv2.1) (by rw [hpool2]; (try sep_ac_rfl)) ?_
    intro sm2 hpcm2 hrunm2 hspm2 htrm2
      ⟨hm2_19, hm2_20, hm2_21, hm2_22, hm2_23, _, hm2_25, hm2_26, hm2_27, hm2_28, hm2_fp, _⟩ hinv_m2
    simp only [arm64_norm, hm19, hm20, hm21, hm22, hm23, hm25, hm26, hm27, hm28, hmfp]
      at hm2_19 hm2_20 hm2_21 hm2_22 hm2_23 hm2_25 hm2_26 hm2_27 hm2_28 hm2_fp
    dsimp only [headerSentPBPinnedAt, unchunked4PinnedAt]
    have ⟨h4840_24, h4840_48, h4840_96⟩ :
        (sp + 4840#64) + 0x18#64 = sp + 4864#64 ∧
        (sp + 4840#64) + 0x30#64 = sp + 4888#64 ∧
        (sp + 4840#64) + 0x60#64 = sp + 4936#64 := ⟨by bv_omega, by bv_omega, by bv_omega⟩
    rw [h4840_24, h4840_48, h4840_96]
    refine sepWPp_extract_pure
      ((optAuthCap g.auth u.auth + 1#64 == 0#64) = !u.auth.isSome ∧
       (optAuthCap g.auth u.auth + 1#64 != 0#64) = u.auth.isSome)
      (fun R' hm => etv2_optAuth_cap_bounds (A := A.repAlloc) (p := sp + 4888#64)
        (R := vecU8At A.repAlloc (sp + 4840#64) g.f3.cap g.f3.ptr u.ek ∗
          vecU8At A.repAlloc (sp + 4864#64) g.f4.cap g.f4.ptr u.dk ∗
          ((sp + 4936#64) ↦₆₄ u.epoch) ∗ ((sp + 16#64) ↦₆₄ w25) ∗
          vecU8At A.repAlloc (sp + 1424#64) cap ptr bs1 ∗
          A.pool lim st sm2 ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by dsimp only [bs1]; (try sep_ac_rfl))) hm))
      fun ⟨hcap_auth_beq, hcap_auth_bne⟩ => ?_
    set bs2 := bs1 ++ encodeUint64Field 1#32 u.epoch
    suffices h10624 : ∀ sm3 : State,
        sm3.pc = spqrSendPlacedEntry + 10624#64 → sm3.status = .Running → sm3.sp = sp → sm3.trace = s0.trace →
        sm3.readReg64 .x19 = s.readReg64 .x19 → sm3.readReg64 .x20 = s.readReg64 .x20 →
        sm3.readReg64 .x21 = s.readReg64 .x21 → sm3.readReg64 .x22 = sp + 4704#64 →
        sm3.readReg64 .x23 = s.readReg64 .x23 → sm3.readReg64 .x25 = w25 →
        sm3.readReg64 .x26 = sp + 4704#64 → sm3.readReg64 .x27 = s.readReg64 .x27 →
        sm3.readReg64 .x28 = s.readReg64 .x28 → sm3.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm3 →
        SepWPp (spqrSendPlacedProg ext) ret sm3
          (((vecU8At A.repAlloc (sp + 4840#64) g.f3.cap g.f3.ptr u.ek ∗
              vecU8At A.repAlloc (sp + 4864#64) g.f4.cap g.f4.ptr u.dk ∗
              optAuthenticatorPBPinnedAt A.repAlloc g.auth (sp + 4888#64) u.auth ∗
              ((sp + 4936#64) ↦₆₄ u.epoch)) ∗
            ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A.repAlloc (sp + 1424#64) cap ptr bs2 ∗
            A.pool lim st sm3 ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
          Q Qp oom by
      cases hep : u.epoch == 0#64
      · have hfit_ep : bs1.length + 1 + (encodeVarint u.epoch).length ≤ cap.toNat := by
          rw [etv2_encodeUint64Field_1_eq, hep] at hfit; dsimp only [bs1]
          simp only [Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_singleton] at hfit ⊢; omega
        have hlt_ep : bs1.length < cap.toNat := by have := encodeVarint_length_pos u.epoch; omega
        have hbeq_ep := cap_beq_len_false_of_lt hlt_ep hcap
        rw [vecU8At_expose_one A.repAlloc (sp + 1424#64) cap ptr bs1 hlt_ep hcap hptr, h1432, h1440]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b1 => ?_
        (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
        apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 451)
        by_vm_steps_safe
          wp_steps
          apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, wp_norm, *])
          intro hinv3
          have hpool3 : A.pool lim st sm2 = A.pool lim st _ := (A.pool_of_vmPreserved hinv3.2).symm
          have hpack_ep := vecU8At_pack_one A.repAlloc (sp + 1424#64) cap ptr bs1 0x08#8 hlt_ep hcap hptr
          rw [h1432, h1440] at hpack_ep
          refine step_send_encode_varint_call_placed A lim st hvarint u.epoch
            (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 10624#64) (bs1 ++ [0x08#8])
            (by simpa only [List.length_append, List.length_singleton] using hfit_ep)
            (F := (vecU8At A.repAlloc (sp + 4840#64) g.f3.cap g.f3.ptr u.ek ∗
              vecU8At A.repAlloc (sp + 4864#64) g.f4.cap g.f4.ptr u.dk ∗
              optAuthenticatorPBPinnedAt A.repAlloc g.auth (sp + 4888#64) u.auth ∗
              ((sp + 4936#64) ↦₆₄ u.epoch)) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hinv_m2.trans hinv3.1) (by rw [← hpack_ep, hpool3]; (try sep_ac_rfl)) ?_
          intro sm3 hpcm3 hrunm3 hspm3 htrm3
            ⟨hm3_19, hm3_20, hm3_21, hm3_22, hm3_23, _, hm3_25, hm3_26, hm3_27, hm3_28, hm3_fp, _⟩ hinv_m3
          simp only [arm64_norm, hm2_19, hm2_20, hm2_21, hm2_22, hm2_23, hm2_25, hm2_26, hm2_27, hm2_28, hm2_fp]
            at hm3_19 hm3_20 hm3_21 hm3_22 hm3_23 hm3_25 hm3_26 hm3_27 hm3_28 hm3_fp
          refine SepWPp.weaken_pre (Entails.of_eq ?_)
            (h10624 sm3 hpcm3 hrunm3 hspm3 htrm3 hm3_19 hm3_20 hm3_21 hm3_22 hm3_23 hm3_25 hm3_26
              hm3_27 hm3_28 hm3_fp hinv_m3)
          simp +zetaDelta only [bs2, etv2_encodeUint64Field_1_eq, hep, Bool.false_eq_true, ↓reduceIte,
            List.append_assoc]; (try sep_ac_rfl)
      · (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
        apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 10624#64)
        wp_steps
        apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv3
        have hpool3 : A.pool lim st sm2 = A.pool lim st _ := (A.pool_of_vmPreserved hinv3.2).symm
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (h10624 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (hinv_m2.trans hinv3.1))
        rw [hpool3]; simp +zetaDelta only [bs2, etv2_encodeUint64Field_1_eq, hep, ↓reduceIte, List.append_nil]
        (try sep_ac_rfl)
    intro sm3 hpcm3 hrunm3 hspm3 htrm3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx25_3 hx26_3 hx27_3 hx28_3 hfp_3 hinv_3
    cases hauth : u.auth with
    | none =>
      rw [optAuthenticatorPBPinnedAt_eq A.repAlloc g.auth (sp + 4888#64) none]
      simp only [hauth, Option.isSome_none, Bool.not_false] at hcap_auth_beq hcap_auth_bne
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
      apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 10656#64)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv4
      have hpool4 : A.pool lim st sm3 = A.pool lim st _ := (A.pool_of_vmPreserved hinv4.2).symm
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h10656 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hinv_3.trans hinv4.1))
      rw [← optAuthenticatorPBPinnedAt_eq A.repAlloc g.auth (sp + 4888#64) none, hpool4]
      simp +zetaDelta only [bs2, bs1, hauth, encodeOptMessage, List.append_nil]; (try sep_ac_rfl)
    | some auth =>
      rw [optAuthenticatorPBPinnedAt_eq A.repAlloc g.auth (sp + 4888#64) (some auth)]
      simp only [hauth, Option.isSome_some, Bool.not_true] at hcap_auth_beq hcap_auth_bne
      have hfit_auth : bs2.length + (encodeMessage ProtoAuthenticator.encodeRaw 2#32 auth).length ≤ cap.toNat := by
        rw [hauth] at hfit; dsimp only [bs2, bs1, encodeOptMessage] at hfit ⊢
        simp only [List.length_append, List.length_singleton] at hfit ⊢; omega
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
      apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 454)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv4
      have hpool4 : A.pool lim st sm3 = A.pool lim st _ := (A.pool_of_vmPreserved hinv4.2).symm
      rw [← optAuthenticatorPBPinnedAt_eq A.repAlloc g.auth (sp + 4888#64) (some auth)]
      refine step_send_encode_auth_call_placed A lim st ext hauthEnc
        (sp + 4888#64) (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 10656#64) g.auth auth bs2 hfit_auth
        (F := (vecU8At A.repAlloc (sp + 4840#64) g.f3.cap g.f3.ptr u.ek ∗
          vecU8At A.repAlloc (sp + 4864#64) g.f4.cap g.f4.ptr u.dk ∗
          ((sp + 4936#64) ↦₆₄ u.epoch)) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hinv_3.trans hinv4.1) (by dsimp only [optAuthenticatorPBPinnedAt]; rw [hpool4]; (try sep_ac_rfl)) ?_
      intro sm4 hpcm4 hrunm4 hspm4 htrm4
        ⟨hm4_19, hm4_20, hm4_21, _, hm4_23, _, hm4_25, hm4_26, hm4_27, hm4_28, hm4_fp, _⟩ hinv_m4
      simp only [arm64_norm, hx19_3, hx20_3, hx21_3, hx23_3, hx25_3, hx26_3, hx27_3, hx28_3, hfp_3]
        at hm4_19 hm4_20 hm4_21 hm4_23 hm4_25 hm4_26 hm4_27 hm4_28 hm4_fp
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h10656 sm4 hpcm4 hrunm4 hspm4 htrm4 hm4_19 hm4_20 hm4_21 hm4_23 hm4_25 hm4_26
          hm4_27 hm4_28 hm4_fp hinv_m4)
      simp +zetaDelta only [bs2, bs1, hauth, encodeOptMessage, optAuthenticatorPBPinnedAt]; (try sep_ac_rfl)

set_option maxHeartbeats 800000 in
theorem send3_step_keysSampled_some_2_placed {resStack : Nat}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State)) {s0 sm4 : State}
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hmemcpy : subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy") etvMemcpyRegionSpec)
    (sp cap ptr w25 : BitVec 64) (g : Unchunked4PBGhost) (u : V1State.Unchunked.HeaderSent)
    (bs3 : List (BitVec 8))
    (hfit3 : bs3.length + (encodeBytesField 3#32 u.ek).length ≤ cap.toNat)
    (hcap : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0) (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpcm4 : sm4.pc = spqrSendPlacedEntry + 10656#64) (hrunm4 : sm4.status = .Running)
    (hspm4 : sm4.sp = sp) (htrm4 : sm4.trace = s0.trace)
    (hx25_4 : sm4.readReg64 .x25 = w25) (hx26_4 : sm4.readReg64 .x26 = sp + 4704#64)
    (hinv_4 : StepInv s0 sm4)
    (h10776 : ∀ sm7 : State,
      sm7.pc = spqrSendPlacedEntry + 10776#64 → sm7.status = .Running → sm7.sp = sp → sm7.trace = s0.trace →
      sm7.readReg64 .x19 = sm4.readReg64 .x19 → sm7.readReg64 .x20 = sm4.readReg64 .x20 →
      sm7.readReg64 .x21 = sm4.readReg64 .x21 → sm7.readReg64 .x23 = sm4.readReg64 .x23 →
      sm7.readReg64 .x25 = w25 → sm7.readReg64 .x26 = sp + 4704#64 →
      sm7.readReg64 .x27 = sm4.readReg64 .x27 → sm7.readReg64 .x28 = sm4.readReg64 .x28 →
      sm7.readReg64 .fp = sm4.readReg64 .fp → StepInv s0 sm7 →
      SepWPp (spqrSendPlacedProg ext) ret sm7
        (((vecU8At A.repAlloc (sp + 4840#64) g.f3.cap g.f3.ptr u.ek ∗
            vecU8At A.repAlloc (sp + 4864#64) g.f4.cap g.f4.ptr u.dk ∗
            optAuthenticatorPBPinnedAt A.repAlloc g.auth (sp + 4888#64) u.auth ∗
            ((sp + 4936#64) ↦₆₄ u.epoch)) ∗
          ((sp + 16#64) ↦₆₄ w25) ∗
          vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs3 ++ encodeBytesField 3#32 u.ek) ∗
          A.pool lim st sm7 ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret sm4
      (((vecU8At A.repAlloc (sp + 4840#64) g.f3.cap g.f3.ptr u.ek ∗
          vecU8At A.repAlloc (sp + 4864#64) g.f4.cap g.f4.ptr u.dk ∗
          optAuthenticatorPBPinnedAt A.repAlloc g.auth (sp + 4888#64) u.auth ∗
          ((sp + 4936#64) ↦₆₄ u.epoch)) ∗
        ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A.repAlloc (sp + 1424#64) cap ptr bs3 ∗
        A.pool lim st sm4 ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
      Q Qp oom := by
  have ⟨h1432, h1440⟩ : (sp + 1424#64) + 8#64 = sp + 1432#64 ∧ (sp + 1424#64) + 16#64 = sp + 1440#64 :=
    ⟨by bv_omega, by bv_omega⟩
  refine sepWPp_extract_vecU8At_bounds (A := A.repAlloc) (v := sp + 4840#64) (cap := g.f3.cap)
    (ptr := g.f3.ptr) (bs := u.ek)
    (F := vecU8At A.repAlloc (sp + 4864#64) g.f4.cap g.f4.ptr u.dk ∗
      optAuthenticatorPBPinnedAt A.repAlloc g.auth (sp + 4888#64) u.auth ∗
      ((sp + 4936#64) ↦₆₄ u.epoch) ∗ ((sp + 16#64) ↦₆₄ w25) ∗
      vecU8At A.repAlloc (sp + 1424#64) cap ptr bs3 ∗
      A.pool lim st sm4 ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F)
    (by sep_ac_rfl) fun hek_le hek_cap _ => ?_
  have ⟨h4848, h4856⟩ : (sp + 4840#64) + 8#64 = sp + 4848#64 ∧ (sp + 4840#64) + 16#64 = sp + 4856#64 :=
    ⟨by bv_omega, by bv_omega⟩
  rw [vecU8At_eq_header_sep_buf A.repAlloc (sp + 4840#64), vecHeader, h4848, h4856]
  have hek_lt : u.ek.length < 2 ^ 64 := by omega
  obtain ⟨hbeqz_ek, hbnez_ek⟩ := ofNat_length_beq_zero_of_lt hek_lt
  cases hemp : u.ek.isEmpty
  · simp only [hemp, Bool.not_false] at hbeqz_ek hbnez_ek
    have hne_ek : u.ek ≠ [] := List.isEmpty_eq_false_iff.mp hemp
    have henc_eq : encodeBytesField 3#32 u.ek =
        [0x1a#8] ++ encodeVarint (BitVec.ofNat 64 u.ek.length) ++ u.ek := by
      rw [etv2_encodeBytesField_3_eq, hemp]; simp only [Bool.false_eq_true, ↓reduceIte]
    have hfit_all : bs3.length + 1 + (encodeVarint (BitVec.ofNat 64 u.ek.length)).length + u.ek.length ≤
        cap.toNat := by
      rw [henc_eq] at hfit3; simp only [List.length_append, List.length_singleton] at hfit3 ⊢; omega
    have hlt_tag : bs3.length < cap.toNat := by omega
    have hcmp_tag := cap_beq_len_false_of_lt hlt_tag hcap
    rw [vecU8At_expose_one A.repAlloc (sp + 1424#64) cap ptr bs3 hlt_tag hcap hptr, h1432, h1440]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b2 => ?_
    (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
    apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 451)
    by_vm_steps_safe
      wp_steps
      apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv5
      have hpool5 : A.pool lim st sm4 = A.pool lim st _ := (A.pool_of_vmPreserved hinv5.2).symm
      refine send3a_step_bytes_varint_placed A lim st ext hvarint 0x1a#8 sp cap ptr
        (spqrSendPlacedEntry + 10716#64) bs3 u.ek hemp hfit_all hcap hptr halign
        (F := (((sp + 4840#64) ↦₆₄ g.f3.cap) ∗ ((sp + 4848#64) ↦₆₄ g.f3.ptr) ∗
            ((sp + 4856#64) ↦₆₄ BitVec.ofNat 64 u.ek.length)) ∗
          vecU8Buf A.repAlloc g.f3.cap g.f3.ptr u.ek ∗
          vecU8At A.repAlloc (sp + 4864#64) g.f4.cap g.f4.ptr u.dk ∗
          optAuthenticatorPBPinnedAt A.repAlloc g.auth (sp + 4888#64) u.auth ∗
          ((sp + 4936#64) ↦₆₄ u.epoch) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (hinv_4.trans hinv5.1) (by rw [hpool5]; (try sep_ac_rfl)) ?_
      intro sm5 bs_ek hpcm5 hrunm5 hspm5 htrm5
        ⟨hm5_19, hm5_20, hm5_21, hm5_22, hm5_23, hm5_24, hm5_25, hm5_26, hm5_27, hm5_28, hm5_fp, _⟩
        hinv_m5 hfit_mc hcmp_mc
      simp only [arm64_norm, hx25_4, hx26_4]
        at hm5_19 hm5_20 hm5_21 hm5_22 hm5_23 hm5_24 hm5_25 hm5_26 hm5_27 hm5_28 hm5_fp
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
      apply sepWPp_of_sepWP_cs_vm (mid := lsρ "memcpy")
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv6
      have hpool6 : A.pool lim st sm5 = A.pool lim st _ := (A.pool_of_vmPreserved hinv6.2).symm
      refine send3a_step_memcpy_slice_placed A lim st ext hmemcpy sp cap ptr g.f3.cap g.f3.ptr
        (spqrSendPlacedEntry + 10756#64) bs_ek u.ek hemp hek_le halign
        (F := (((sp + 4840#64) ↦₆₄ g.f3.cap) ∗ ((sp + 4848#64) ↦₆₄ g.f3.ptr) ∗
            ((sp + 4856#64) ↦₆₄ BitVec.ofNat 64 u.ek.length)) ∗
          vecU8At A.repAlloc (sp + 4864#64) g.f4.cap g.f4.ptr u.dk ∗
          optAuthenticatorPBPinnedAt A.repAlloc g.auth (sp + 4888#64) u.auth ∗
          ((sp + 4936#64) ↦₆₄ u.epoch) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hek_lt
        (hinv_m5.trans hinv6.1) (by rw [hpool6]; (try sep_ac_rfl)) ?_
      intro sm6 hpcm6 hrunm6 hspm6 htrm6
        ⟨hm6_19, hm6_20, hm6_21, hm6_22, hm6_23, hm6_24, _, hm6_26, hm6_27, hm6_28, hm6_fp, _⟩ hinv_m6
      simp only [arm64_norm, hm5_19, hm5_20, hm5_21, hm5_22, hm5_23, hm5_24, hm5_26, hm5_27, hm5_28, hm5_fp]
        at hm6_19 hm6_20 hm6_21 hm6_22 hm6_23 hm6_24 hm6_26 hm6_27 hm6_28 hm6_fp
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
      apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 10776#64)
      by_vm_steps_safe
        wp_steps
        apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv7
        have hpool7 : A.pool lim st sm6 = A.pool lim st _ := (A.pool_of_vmPreserved hinv7.2).symm
        have hpack_mc := vecU8At_pack_slice A.repAlloc (sp + 1424#64) cap ptr bs_ek u.ek hfit_mc hcap hptr hne_ek
        have hbs_eq : bs_ek ++ u.ek = bs3 ++ encodeBytesField 3#32 u.ek := by
          dsimp only [bs_ek]; rw [henc_eq]; simp only [List.append_assoc]
        rw [h1432, h1440, hbs_eq] at hpack_mc
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (h10776 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hinv_m6.trans hinv7.1))
        rw [hpool7, vecU8At_eq_header_sep_buf A.repAlloc (sp + 4840#64), vecHeader, h4848, h4856, ← hpack_mc]
        (try sep_ac_rfl)
  · simp only [hemp, Bool.not_true] at hbeqz_ek hbnez_ek
    have henc_nil : encodeBytesField 3#32 u.ek = [] := by
      rw [etv2_encodeBytesField_3_eq, hemp]; simp only [↓reduceIte]
    (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
    apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 10776#64)
    wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv5
    have hpool5 : A.pool lim st sm4 = A.pool lim st _ := (A.pool_of_vmPreserved hinv5.2).symm
    refine SepWPp.weaken_pre (Entails.of_eq ?_)
      (h10776 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hinv_4.trans hinv5.1))
    rw [hpool5, vecU8At_eq_header_sep_buf A.repAlloc (sp + 4840#64), vecHeader, h4848, h4856]
    simp +zetaDelta only [henc_nil, List.append_nil]; (try sep_ac_rfl)

set_option maxHeartbeats 800000 in
theorem send3_step_keysSampled_some_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State)) {s0 s : State}
    (hhsLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 492)
      (withStepInv s0 (leafEncLen16Spec (headerSentPBPinnedAt A.repAlloc) headerSentPBEncodedLen)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hauthEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 454)
      (withStepInv s0 (authEncodeExactSpecOf resStack A lim)))
    (hmemcpy : subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy") etvMemcpyRegionSpec)
    (sp cap ptr w25 : BitVec 64) (g : Unchunked4PBGhost) (u : V1State.Unchunked.HeaderSent)
    (bs : List (BitVec 8))
    (hu_lt : headerSentPBEncodedLen u < 2 ^ 64)
    (hfit : bs.length + (encodeOptMessage V1State.Unchunked.HeaderSent.encodeRaw 1#32 (some u)).length ≤
      cap.toNat)
    (hcap : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0) (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = spqrSendPlacedEntry + 10520#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx22 : s.readReg64 .x22 = sp + 4704#64) (hx25 : s.readReg64 .x25 = w25)
    (hx26 : s.readReg64 .x26 = sp + 4704#64) (hinv0 : StepInv s0 s)
    (hP : P = (headerSentPBPinnedAt A.repAlloc g (sp + 4840#64) u ∗ ((sp + 16#64) ↦₆₄ w25) ∗
      vecU8At A.repAlloc (sp + 1424#64) cap ptr bs ∗ A.pool lim st s ∗
      stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = spqrSendPlacedEntry + 10896#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x23 = s.readReg64 .x23 →
      sm.readReg64 .x25 = w25 → sm.readReg64 .x26 = sp + 4704#64 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((headerSentPBPinnedAt A.repAlloc g (sp + 4840#64) u ∗ ((sp + 16#64) ↦₆₄ w25) ∗
          vecU8At A.repAlloc (sp + 1424#64) cap ptr
            (bs ++ encodeOptMessage V1State.Unchunked.HeaderSent.encodeRaw 1#32 (some u)) ∗
          A.pool lim st sm ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  refine send3_step_keysSampled_some_1_placed hres A lim st ext hhsLen hvarint hauthEnc
    sp cap ptr w25 g u bs hu_lt hfit hcap hptr halign hpc hrun hsp htr hx22 hx25 hx26 hinv0 hP ?_
  intro sm4 hpcm4 hrunm4 hspm4 htrm4 hx19_4 hx20_4 hx21_4 hx23_4 hx25_4 hx26_4 hx27_4 hx28_4 hfp_4 hinv_4
  rw [etv2_encodeOptHeaderSent_some_eq] at hfit; simp only [List.length_append, List.length_singleton] at hfit
  set bs1 := (bs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 (headerSentPBEncodedLen u))
  set bs2 := bs1 ++ encodeUint64Field 1#32 u.epoch
  set bs3 := bs2 ++ encodeOptMessage ProtoAuthenticator.encodeRaw 2#32 u.auth
  have hfit3 : bs3.length + (encodeBytesField 3#32 u.ek).length ≤ cap.toNat := by
    dsimp only [bs3, bs2, bs1]; simp only [List.length_append, List.length_singleton]; omega
  refine send3_step_keysSampled_some_2_placed A lim st ext hvarint hmemcpy sp cap ptr w25 g u bs3
    hfit3 hcap hptr halign hpcm4 hrunm4 hspm4 htrm4 hx25_4 hx26_4 hinv_4 ?_
  intro sm7 hpcm7 hrunm7 hspm7 htrm7 hx19_7 hx20_7 hx21_7 hx23_7 hx25_7 hx26_7 hx27_7 hx28_7 hfp_7 hinv_7
  rw [hx19_4] at hx19_7; rw [hx20_4] at hx20_7; rw [hx21_4] at hx21_7; rw [hx23_4] at hx23_7
  rw [hx27_4] at hx27_7; rw [hx28_4] at hx28_7; rw [hfp_4] at hfp_7
  have ⟨h1432, h1440⟩ : (sp + 1424#64) + 8#64 = sp + 1432#64 ∧ (sp + 1424#64) + 16#64 = sp + 1440#64 :=
    ⟨by bv_omega, by bv_omega⟩
  have ⟨h4840_24, h4840_48, h4840_96⟩ :
      (sp + 4840#64) + 0x18#64 = sp + 4864#64 ∧
      (sp + 4840#64) + 0x30#64 = sp + 4888#64 ∧
      (sp + 4840#64) + 0x60#64 = sp + 4936#64 := ⟨by bv_omega, by bv_omega, by bv_omega⟩
  set bs4 := bs3 ++ encodeBytesField 3#32 u.ek
  refine sepWPp_extract_vecU8At_bounds (A := A.repAlloc) (v := sp + 4864#64) (cap := g.f4.cap)
    (ptr := g.f4.ptr) (bs := u.dk)
    (F := vecU8At A.repAlloc (sp + 4840#64) g.f3.cap g.f3.ptr u.ek ∗
      optAuthenticatorPBPinnedAt A.repAlloc g.auth (sp + 4888#64) u.auth ∗
      ((sp + 4936#64) ↦₆₄ u.epoch) ∗ ((sp + 16#64) ↦₆₄ w25) ∗
      vecU8At A.repAlloc (sp + 1424#64) cap ptr bs4 ∗
      A.pool lim st sm7 ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F)
    (by dsimp only [bs4]; (try sep_ac_rfl)) fun hdk_le hdk_cap _ => ?_
  have ⟨h4872, h4880⟩ : (sp + 4864#64) + 8#64 = sp + 4872#64 ∧ (sp + 4864#64) + 16#64 = sp + 4880#64 :=
    ⟨by bv_omega, by bv_omega⟩
  rw [vecU8At_eq_header_sep_buf A.repAlloc (sp + 4864#64), vecHeader, h4872, h4880]
  have hdk_lt : u.dk.length < 2 ^ 64 := by omega
  obtain ⟨hbeqz_dk, hbnez_dk⟩ := ofNat_length_beq_zero_of_lt hdk_lt
  cases hemp_dk : u.dk.isEmpty
  · simp only [hemp_dk, Bool.not_false] at hbeqz_dk hbnez_dk
    have hne_dk : u.dk ≠ [] := List.isEmpty_eq_false_iff.mp hemp_dk
    have henc_dk : encodeBytesField 4#32 u.dk =
        [0x22#8] ++ encodeVarint (BitVec.ofNat 64 u.dk.length) ++ u.dk := by
      rw [etv2_encodeBytesField_4_eq, hemp_dk]; simp only [Bool.false_eq_true, ↓reduceIte]
    have hfit_dk : bs4.length + 1 + (encodeVarint (BitVec.ofNat 64 u.dk.length)).length + u.dk.length ≤
        cap.toNat := by
      rw [henc_dk] at hfit; dsimp only [bs4, bs3, bs2, bs1] at hfit ⊢
      simp only [List.length_append, List.length_singleton] at hfit ⊢; omega
    have hlt_tag : bs4.length < cap.toNat := by omega
    have hcmp_tag := cap_beq_len_false_of_lt hlt_tag hcap
    rw [vecU8At_expose_one A.repAlloc (sp + 1424#64) cap ptr bs4 hlt_tag hcap hptr, h1432, h1440]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b3 => ?_
    (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
    apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 451)
    by_vm_steps_safe
      wp_steps
      apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv8
      have hpool8 : A.pool lim st sm7 = A.pool lim st _ := (A.pool_of_vmPreserved hinv8.2).symm
      refine send3a_step_bytes_varint_placed A lim st ext hvarint 0x22#8 sp cap ptr
        (spqrSendPlacedEntry + 10836#64) bs4 u.dk hemp_dk hfit_dk hcap hptr halign
        (F := vecU8At A.repAlloc (sp + 4840#64) g.f3.cap g.f3.ptr u.ek ∗
          (((sp + 4864#64) ↦₆₄ g.f4.cap) ∗ ((sp + 4872#64) ↦₆₄ g.f4.ptr) ∗
            ((sp + 4880#64) ↦₆₄ BitVec.ofNat 64 u.dk.length)) ∗
          vecU8Buf A.repAlloc g.f4.cap g.f4.ptr u.dk ∗
          optAuthenticatorPBPinnedAt A.repAlloc g.auth (sp + 4888#64) u.auth ∗
          ((sp + 4936#64) ↦₆₄ u.epoch) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (hinv_7.trans hinv8.1) (by rw [hpool8]; (try sep_ac_rfl)) ?_
      intro sm8 bs_dk hpcm8 hrunm8 hspm8 htrm8
        ⟨hm8_19, hm8_20, hm8_21, hm8_22, hm8_23, hm8_24, hm8_25, hm8_26, hm8_27, hm8_28, hm8_fp, _⟩
        hinv_m8 hfit_mc hcmp_mc
      simp only [arm64_norm, hx19_7, hx20_7, hx21_7, hx23_7, hx26_7, hx27_7, hx28_7, hfp_7]
        at hm8_19 hm8_20 hm8_21 hm8_22 hm8_23 hm8_24 hm8_25 hm8_26 hm8_27 hm8_28 hm8_fp
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
      apply sepWPp_of_sepWP_cs_vm (mid := lsρ "memcpy")
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv9
      have hpool9 : A.pool lim st sm8 = A.pool lim st _ := (A.pool_of_vmPreserved hinv9.2).symm
      refine send3a_step_memcpy_slice_placed A lim st ext hmemcpy sp cap ptr g.f4.cap g.f4.ptr
        (spqrSendPlacedEntry + 10876#64) bs_dk u.dk hemp_dk hdk_le halign
        (F := vecU8At A.repAlloc (sp + 4840#64) g.f3.cap g.f3.ptr u.ek ∗
          (((sp + 4864#64) ↦₆₄ g.f4.cap) ∗ ((sp + 4872#64) ↦₆₄ g.f4.ptr) ∗
            ((sp + 4880#64) ↦₆₄ BitVec.ofNat 64 u.dk.length)) ∗
          optAuthenticatorPBPinnedAt A.repAlloc g.auth (sp + 4888#64) u.auth ∗
          ((sp + 4936#64) ↦₆₄ u.epoch) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hdk_lt
        (hinv_m8.trans hinv9.1) (by rw [hpool9]; (try sep_ac_rfl)) ?_
      intro sm9 hpcm9 hrunm9 hspm9 htrm9
        ⟨hm9_19, hm9_20, hm9_21, hm9_22, hm9_23, hm9_24, _, hm9_26, hm9_27, hm9_28, hm9_fp, _⟩ hinv_m9
      simp only [arm64_norm, hm8_19, hm8_20, hm8_21, hm8_22, hm8_23, hm8_24, hm8_26, hm8_27, hm8_28, hm8_fp]
        at hm9_19 hm9_20 hm9_21 hm9_22 hm9_23 hm9_24 hm9_26 hm9_27 hm9_28 hm9_fp
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
      apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 10896#64)
      by_vm_steps_safe
        wp_steps
        apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv10
        have hpool10 : A.pool lim st sm9 = A.pool lim st _ := (A.pool_of_vmPreserved hinv10.2).symm
        have hpack_mc := vecU8At_pack_slice A.repAlloc (sp + 1424#64) cap ptr bs_dk u.dk hfit_mc hcap hptr hne_dk
        have hbs_eq : bs_dk ++ u.dk = bs ++ encodeOptMessage V1State.Unchunked.HeaderSent.encodeRaw 1#32 (some u) := by
          rw [etv2_encodeOptHeaderSent_some_eq, henc_dk]
          dsimp only [bs_dk, bs4, bs3, bs2, bs1]; simp only [List.append_assoc]
        rw [h1432, h1440, hbs_eq] at hpack_mc
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hinv_m9.trans hinv10.1))
        rw [hpool10]; dsimp only [headerSentPBPinnedAt, unchunked4PinnedAt]
        rw [h4840_24, h4840_48, h4840_96, vecU8At_eq_header_sep_buf A.repAlloc (sp + 4864#64),
          vecHeader, h4872, h4880, ← hpack_mc]; (try sep_ac_rfl)
  · simp only [hemp_dk, Bool.not_true] at hbeqz_dk hbnez_dk
    have henc_nil : encodeBytesField 4#32 u.dk = [] := by
      rw [etv2_encodeBytesField_4_eq, hemp_dk]; simp only [↓reduceIte]
    (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
    apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 10896#64)
    wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv8
    have hpool8 : A.pool lim st sm7 = A.pool lim st _ := (A.pool_of_vmPreserved hinv8.2).symm
    refine SepWPp.weaken_pre (Entails.of_eq ?_)
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hinv_7.trans hinv8.1))
    rw [hpool8]; dsimp only [headerSentPBPinnedAt, unchunked4PinnedAt]
    rw [h4840_24, h4840_48, h4840_96, vecU8At_eq_header_sep_buf A.repAlloc (sp + 4864#64),
      vecHeader, h4872, h4880, etv2_encodeOptHeaderSent_some_eq, henc_nil]
    dsimp only [bs4, bs3, bs2, bs1]; simp only [List.append_nil, List.append_assoc]; (try sep_ac_rfl)

theorem step_send_v1_keysSampled_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State)) {s0 s : State}
    (hhsLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 492)
      (withStepInv s0 (leafEncLen16Spec (headerSentPBPinnedAt A.repAlloc) headerSentPBEncodedLen)))
    (hpolyEncLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 480)
      (withStepInv s0 (leafEncLen16Spec (polynomialEncoderPBPinnedAt A.repAlloc) polynomialEncoderPBEncodedLen)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hauthEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 454)
      (withStepInv s0 (authEncodeExactSpecOf resStack A lim)))
    (hmemcpy : subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy") etvMemcpyRegionSpec)
    (hpolyEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 456)
      (withStepInv s0 (etvPolyEncoderBudgetExactSpecOf resStack A lim)))
    (sp cap ptr w25 : BitVec 64) (g : Unchunked4PBGhost × PolynomialEncoderPBGhost)
    (v : V1State.Chunked.KeysSampled) (bs : List (BitVec 8))
    (hv_len : v1StatePBEncodedLen ⟨some (.keysSampled v)⟩ < 2 ^ 64)
    (hfit : bs.length + (V1State.InnerState.encode (.keysSampled v)).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = spqrSendPlacedEntry + 8612#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace) (hinv0 : StepInv s0 s)
    (hP : P = ((optHeaderSentPBPinnedAt A.repAlloc g.1 (sp + 4840#64) v.uc ∗
        optPolynomialEncoderPBPinnedAt A.repAlloc g.2 (sp + 4944#64) v.sendingHdr) ∗
      ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A.repAlloc (sp + 1424#64) cap ptr bs ∗
      A.pool lim st s ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = spqrSendPlacedEntry + 6216#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = w25 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        (((optHeaderSentPBPinnedAt A.repAlloc g.1 (sp + 4840#64) v.uc ∗
            optPolynomialEncoderPBPinnedAt A.repAlloc g.2 (sp + 4944#64) v.sendingHdr) ∗
          ((sp + 16#64) ↦₆₄ w25) ∗
          vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs ++ V1State.InnerState.encode (.keysSampled v)) ∗
          A.pool lim st sm ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  subst hP; rcases v with ⟨uc, sendingHdr⟩
  rw [etv2_encodeInnerState_keysSampled_eq] at hfit; simp only [List.length_append, List.length_singleton] at hfit
  have hsub_len : v1StateInnerPayloadEncodedLen (.keysSampled ⟨uc, sendingHdr⟩) < 2 ^ 64 := by
    dsimp only [v1StatePBEncodedLen] at hv_len; omega
  have hlt1 : bs.length < cap.toNat := by omega
  have hfit_var : (bs ++ [0x12#8]).length +
      (encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.keysSampled ⟨uc, sendingHdr⟩)))).length ≤
      cap.toNat := by
    simp only [List.length_append, List.length_singleton]; omega
  refine sepWPp_extract_vecU8At_bounds (v := sp + 1424#64) (cap := cap) (ptr := ptr) (bs := bs)
    (F := optHeaderSentPBPinnedAt A.repAlloc g.1 (sp + 4840#64) uc ∗
      optPolynomialEncoderPBPinnedAt A.repAlloc g.2 (sp + 4944#64) sendingHdr ∗
      ((sp + 16#64) ↦₆₄ w25) ∗ A.pool lim st s ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F)
    (by sep_ac_rfl) fun _ hcap hptr => ?_
  refine sepWPp_extract_pure
    (((optHeaderSentCap g.1 uc + 1#64 == 0#64) = !uc.isSome ∧
      (optHeaderSentCap g.1 uc + 1#64 != 0#64) = uc.isSome) ∧
     ((optPolyEncCap g.2 sendingHdr + 1#64 == 0#64) = !sendingHdr.isSome ∧
      (optPolyEncCap g.2 sendingHdr + 1#64 != 0#64) = sendingHdr.isSome))
    (fun R' hm => ⟨optHeaderSentPBPinnedAt_cap_bounds (p := sp + 4840#64)
        (R := optPolynomialEncoderPBPinnedAt A.repAlloc g.2 (sp + 4944#64) sendingHdr ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A.repAlloc (sp + 1424#64) cap ptr bs ∗
          A.pool lim st s ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm),
      optPolynomialEncoderPBPinnedAt_cap_bounds (p := sp + 4944#64)
        (R := optHeaderSentPBPinnedAt A.repAlloc g.1 (sp + 4840#64) uc ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A.repAlloc (sp + 1424#64) cap ptr bs ∗
          A.pool lim st s ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm)⟩)
    fun ⟨⟨hcap_uc_beq, hcap_uc_bne⟩, ⟨hcap_enc_beq, hcap_enc_bne⟩⟩ => ?_
  have hbeq_false := cap_beq_len_false_of_lt hlt1 hcap
  have ⟨h1432, h1440⟩ : (sp + 1424#64) + 8#64 = sp + 1432#64 ∧ (sp + 1424#64) + 16#64 = sp + 1440#64 :=
    ⟨by bv_omega, by bv_omega⟩
  have hpack := vecU8At_pack_one A.repAlloc (sp + 1424#64) cap ptr bs 0x12#8 hlt1 hcap hptr
  rw [h1432, h1440] at hpack
  suffices h9720 : ∀ sm1 : State,
      sm1.pc = spqrSendPlacedEntry + 9720#64 → sm1.status = .Running → sm1.sp = sp → sm1.trace = s0.trace →
      sm1.readReg64 .x19 = s.readReg64 .x19 → sm1.readReg64 .x20 = s.readReg64 .x27 →
      sm1.readReg64 .x21 = s.readReg64 .x21 → sm1.readReg64 .x22 = sp + 4704#64 →
      sm1.readReg64 .x23 = s.readReg64 .x23 → sm1.readReg64 .x24 = optHeaderSentCap g.1 uc →
      sm1.readReg64 .x25 = BitVec.ofNat 64 (optHeaderSentPBFieldEncodedLen uc) →
      sm1.readReg64 .x28 = s.readReg64 .x28 → sm1.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm1 →
      SepWPp (spqrSendPlacedProg ext) ret sm1
        (((optHeaderSentPBPinnedAt A.repAlloc g.1 (sp + 4840#64) uc ∗
            optPolynomialEncoderPBPinnedAt A.repAlloc g.2 (sp + 4944#64) sendingHdr) ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs ++ [0x12#8]) ∗
          A.pool lim st sm1 ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom by
    rw [vecU8At_expose_one A.repAlloc (sp + 1424#64) cap ptr bs hlt1 hcap hptr, h1432, h1440]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b0 => ?_
    cases uc with
    | none =>
      rw [optHeaderSentPBPinnedAt_eq A.repAlloc g.1 (sp + 4840#64) none]
      simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
      apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 9720#64)
      by_vm_steps_safe
        wp_steps
        apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv1
        have hpool1 : A.pool lim st s = A.pool lim st _ := (A.pool_of_vmPreserved hinv1.2).symm
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (h9720 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [optHeaderSentPBFieldEncodedLen, arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1.1))
        rw [← optHeaderSentPBPinnedAt_eq A.repAlloc g.1 (sp + 4840#64) none, ← hpack, hpool1]; (try sep_ac_rfl)
    | some u =>
      rw [optHeaderSentPBPinnedAt_eq A.repAlloc g.1 (sp + 4840#64) (some u)]
      simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      have ⟨hu_fit, hopt_u_lt⟩ :
          headerSentPBEncodedLen u < 2 ^ 64 ∧ optHeaderSentPBFieldEncodedLen (some u) < 2 ^ 64 :=
        ⟨by dsimp only [v1StateInnerPayloadEncodedLen, optHeaderSentPBFieldEncodedLen] at hsub_len; omega,
         by dsimp only [v1StateInnerPayloadEncodedLen] at hsub_len; omega⟩
      have hvar_u_lt : varintLen (BitVec.ofNat 64 (headerSentPBEncodedLen u)) <
          optHeaderSentPBFieldEncodedLen (some u) := by
        dsimp only [optHeaderSentPBFieldEncodedLen]; omega
      have ⟨⟨_, _, _, _, _⟩, hult_u, hopt_u_eq⟩ :=
        (⟨cmp_ls_false_of_lt hvar_u_lt hopt_u_lt, ult_of_lt_of_fit hvar_u_lt hopt_u_lt,
          etv3_bv_optHeaderSent_some_eq u⟩ : _ ∧ _ ∧ _)
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
      apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 492)
      by_vm_steps_safe
        wp_steps
        apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv1
        rw [← optHeaderSentPBPinnedAt_eq A.repAlloc g.1 (sp + 4840#64) (some u)]
        refine step_send_leaf_encLen16_call_placed hres ext (headerSentPBPinnedAt A.repAlloc)
          headerSentPBEncodedLen hhsLen (sp + 4840#64) sp (spqrSendPlacedEntry + 8680#64) g.1 u hu_fit
          (F := optPolynomialEncoderPBPinnedAt A.repAlloc g.2 (sp + 4944#64) sendingHdr ∗
            ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs ++ [0x12#8]) ∗
            A.pool lim st s ∗ F)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
          (hinv0.trans hinv1.1) (by rw [← hpack]; dsimp only [optHeaderSentPBPinnedAt]; (try sep_ac_rfl)) ?_
        intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1
          ⟨hm19, hm20, hm21, hm22, hm23, hm24, _, _, _, hm28, hmfp, _⟩ hinv_m1 hvm_m1
        simp only [arm64_norm] at hm19 hm20 hm21 hm22 hm23 hm24 hm28 hmfp
        (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
        apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 9720#64)
        wp_steps
        apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv2
        have hpool2 : A.pool lim st s = A.pool lim st _ :=
          (A.pool_of_vmPreserved (hinv1.2.trans (hvm_m1.trans hinv2.2))).symm
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (h9720 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hinv_m1.trans hinv2.1))
        dsimp only [optHeaderSentPBPinnedAt]; rw [hpool2]; (try sep_ac_rfl)
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx28_1 hfp_1 hinv_1
  suffices h10492 : ∀ sm2 : State,
      sm2.pc = spqrSendPlacedEntry + 10492#64 → sm2.status = .Running → sm2.sp = sp → sm2.trace = s0.trace →
      sm2.readReg64 .x8 = BitVec.ofNat 64 (optPolynomialEncoderPBFieldEncodedLen sendingHdr) →
      sm2.readReg64 .x19 = s.readReg64 .x19 → sm2.readReg64 .x20 = s.readReg64 .x27 →
      sm2.readReg64 .x21 = s.readReg64 .x21 → sm2.readReg64 .x22 = sp + 4704#64 →
      sm2.readReg64 .x23 = s.readReg64 .x23 → sm2.readReg64 .x24 = optHeaderSentCap g.1 uc →
      sm2.readReg64 .x25 = BitVec.ofNat 64 (optHeaderSentPBFieldEncodedLen uc) →
      sm2.readReg64 .x26 = sp + 4704#64 → sm2.readReg64 .x27 = optPolyEncCap g.2 sendingHdr →
      sm2.readReg64 .x28 = s.readReg64 .x28 → sm2.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm2 →
      SepWPp (spqrSendPlacedProg ext) ret sm2
        (((optHeaderSentPBPinnedAt A.repAlloc g.1 (sp + 4840#64) uc ∗
            optPolynomialEncoderPBPinnedAt A.repAlloc g.2 (sp + 4944#64) sendingHdr) ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs ++ [0x12#8]) ∗
          A.pool lim st sm2 ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom by
    cases sendingHdr with
    | none =>
      rw [optPolynomialEncoderPBPinnedAt_eq A.repAlloc g.2 (sp + 4944#64) none]
      simp only [Option.isSome_none, Bool.not_false] at hcap_enc_beq hcap_enc_bne
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
      apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 10492#64)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv2
      have hpool2 : A.pool lim st sm1 = A.pool lim st _ := (A.pool_of_vmPreserved hinv2.2).symm
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h10492 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [optPolynomialEncoderPBFieldEncodedLen, arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_1.trans hinv2.1))
      rw [← optPolynomialEncoderPBPinnedAt_eq A.repAlloc g.2 (sp + 4944#64) none, hpool2]; (try sep_ac_rfl)
    | some enc =>
      rw [optPolynomialEncoderPBPinnedAt_eq A.repAlloc g.2 (sp + 4944#64) (some enc)]
      simp only [Option.isSome_some, Bool.not_true] at hcap_enc_beq hcap_enc_bne
      have ⟨henc_fit, hopt_e_lt⟩ :
          polynomialEncoderPBEncodedLen enc < 2 ^ 64 ∧ optPolynomialEncoderPBFieldEncodedLen (some enc) < 2 ^ 64 :=
        ⟨by dsimp only [v1StateInnerPayloadEncodedLen, optPolynomialEncoderPBFieldEncodedLen] at hsub_len; omega,
         by dsimp only [v1StateInnerPayloadEncodedLen] at hsub_len; omega⟩
      have hvar_e_lt : varintLen (BitVec.ofNat 64 (polynomialEncoderPBEncodedLen enc)) <
          optPolynomialEncoderPBFieldEncodedLen (some enc) := by
        dsimp only [optPolynomialEncoderPBFieldEncodedLen]; omega
      have ⟨⟨_, _, _, _, _⟩, hult_e, hopt_e_eq⟩ :=
        (⟨cmp_ls_false_of_lt hvar_e_lt hopt_e_lt, ult_of_lt_of_fit hvar_e_lt hopt_e_lt,
          bv_optPolyEnc_some_eq enc⟩ : _ ∧ _ ∧ _)
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
      apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 480)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv2
      rw [← optPolynomialEncoderPBPinnedAt_eq A.repAlloc g.2 (sp + 4944#64) (some enc)]
      refine step_send_leaf_encLen16_call_placed hres ext (polynomialEncoderPBPinnedAt A.repAlloc)
        polynomialEncoderPBEncodedLen hpolyEncLen (sp + 4944#64) sp (spqrSendPlacedEntry + 9748#64) g.2 enc henc_fit
        (F := optHeaderSentPBPinnedAt A.repAlloc g.1 (sp + 4840#64) uc ∗ ((sp + 16#64) ↦₆₄ w25) ∗
          vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs ++ [0x12#8]) ∗ A.pool lim st sm1 ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (hinv_1.trans hinv2.1) (by dsimp only [optPolynomialEncoderPBPinnedAt]; (try sep_ac_rfl)) ?_
      intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx0m2
        ⟨hm2_19, hm2_20, hm2_21, hm2_22, hm2_23, hm2_24, hm2_25, hm2_26, hm2_27, hm2_28, hm2_fp, _⟩
        hinv_m2 hvm_m2
      simp only [arm64_norm, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx28_1, hfp_1]
        at hm2_19 hm2_20 hm2_21 hm2_22 hm2_23 hm2_24 hm2_25 hm2_26 hm2_27 hm2_28 hm2_fp
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
      apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 10492#64)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv3
      have hpool3 : A.pool lim st sm1 = A.pool lim st _ :=
        (A.pool_of_vmPreserved (hinv2.2.trans (hvm_m2.trans hinv3.2))).symm
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h10492 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hinv_m2.trans hinv3.1))
      dsimp only [optPolynomialEncoderPBPinnedAt]; rw [hpool3]; (try sep_ac_rfl)
  intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx8_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hinv_2
  have ⟨hadd_sum, hult_sum, hule_sum, hult_sum2, hule_sum2⟩ := adds_no_overflow_of_eq
    (a := optPolynomialEncoderPBFieldEncodedLen sendingHdr) (b := optHeaderSentPBFieldEncodedLen uc)
    (c := v1StateInnerPayloadEncodedLen (.keysSampled ⟨uc, sendingHdr⟩)) rfl hsub_len
  (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
  apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 451)
  wp_steps
  apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, wp_norm, *])
  intro hinv3
  have hpool3 : A.pool lim st sm2 = A.pool lim st _ := (A.pool_of_vmPreserved hinv3.2).symm
  set bs1 := (bs ++ [0x12#8]) ++
    encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.keysSampled ⟨uc, sendingHdr⟩)))
  refine step_send_encode_varint_call_placed A lim st hvarint
    (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.keysSampled ⟨uc, sendingHdr⟩)))
    (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 10508#64) (bs ++ [0x12#8]) hfit_var
    (F := (optHeaderSentPBPinnedAt A.repAlloc g.1 (sp + 4840#64) uc ∗
      optPolynomialEncoderPBPinnedAt A.repAlloc g.2 (sp + 4944#64) sendingHdr) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_2.trans hinv3.1)
    (by rw [hpool3]; (try sep_ac_rfl)) ?_
  intro sm3 hpcm3 hrunm3 hspm3 htrm3
    ⟨hm3_19, hm3_20, hm3_21, hm3_22, hm3_23, hm3_24, _, hm3_26, hm3_27, hm3_28, hm3_fp, _⟩ hinv_m3
  simp only [arm64_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx26_2, hx27_2, hx28_2, hfp_2]
    at hm3_19 hm3_20 hm3_21 hm3_22 hm3_23 hm3_24 hm3_26 hm3_27 hm3_28 hm3_fp
  set bs2 := bs1 ++ encodeOptMessage V1State.Unchunked.HeaderSent.encodeRaw 1#32 uc
  suffices h10896 : ∀ sm4 : State,
      sm4.pc = spqrSendPlacedEntry + 10896#64 → sm4.status = .Running → sm4.sp = sp → sm4.trace = s0.trace →
      sm4.readReg64 .x19 = s.readReg64 .x19 → sm4.readReg64 .x20 = s.readReg64 .x27 →
      sm4.readReg64 .x21 = s.readReg64 .x21 → sm4.readReg64 .x23 = s.readReg64 .x23 →
      sm4.readReg64 .x25 = w25 → sm4.readReg64 .x26 = sp + 4704#64 →
      sm4.readReg64 .x27 = optPolyEncCap g.2 sendingHdr → sm4.readReg64 .x28 = s.readReg64 .x28 →
      sm4.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm4 →
      SepWPp (spqrSendPlacedProg ext) ret sm4
        (((optHeaderSentPBPinnedAt A.repAlloc g.1 (sp + 4840#64) uc ∗
            optPolynomialEncoderPBPinnedAt A.repAlloc g.2 (sp + 4944#64) sendingHdr) ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A.repAlloc (sp + 1424#64) cap ptr bs2 ∗
          A.pool lim st sm4 ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom by
    cases uc with
    | none =>
      simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
      apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 10896#64)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv4
      have hpool4 : A.pool lim st sm3 = A.pool lim st _ := (A.pool_of_vmPreserved hinv4.2).symm
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h10896 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hinv_m3.trans hinv4.1))
      rw [hpool4]; simp +zetaDelta only [bs2, bs1, encodeOptMessage, List.append_nil]; (try sep_ac_rfl)
    | some u =>
      simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      have hu_lt : headerSentPBEncodedLen u < 2 ^ 64 := by
        dsimp only [v1StateInnerPayloadEncodedLen, optHeaderSentPBFieldEncodedLen] at hsub_len; omega
      have hfit_u : bs1.length +
          (encodeOptMessage V1State.Unchunked.HeaderSent.encodeRaw 1#32 (some u)).length ≤ cap.toNat := by
        dsimp only [bs1]; simp only [List.length_append, List.length_singleton] at hfit ⊢; omega
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
      apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 10520#64)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv4
      have hpool4 : A.pool lim st sm3 = A.pool lim st _ := (A.pool_of_vmPreserved hinv4.2).symm
      refine send3_step_keysSampled_some_placed hres A lim st ext hhsLen hvarint hauthEnc hmemcpy
        sp cap ptr w25 g.1 u bs1 hu_lt hfit_u hcap hptr halign
        (F := optPolynomialEncoderPBPinnedAt A.repAlloc g.2 (sp + 4944#64) sendingHdr ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (hinv_m3.trans hinv4.1)
        (by dsimp only [bs1, optHeaderSentPBPinnedAt]; rw [hpool4]; (try sep_ac_rfl)) ?_
      intro sm4 hpcm4 hrunm4 hspm4 htrm4 hm4_19 hm4_20 hm4_21 hm4_23 hm4_25 hm4_26 hm4_27 hm4_28 hm4_fp hinv_m4
      simp only [arm64_norm, hm3_19, hm3_20, hm3_21, hm3_23, hm3_27, hm3_28, hm3_fp]
        at hm4_19 hm4_20 hm4_21 hm4_23 hm4_25 hm4_26 hm4_27 hm4_28 hm4_fp
      refine SepWPp.weaken_pre
        (Entails.of_eq (by dsimp only [bs2, bs1, optHeaderSentPBPinnedAt]; (try sep_ac_rfl)))
        (h10896 sm4 hpcm4 hrunm4 hspm4 htrm4 hm4_19 hm4_20 hm4_21 hm4_23 hm4_25 hm4_26
          hm4_27 hm4_28 hm4_fp hinv_m4)
  intro sm4 hpcm4 hrunm4 hspm4 htrm4 hx19_4 hx20_4 hx21_4 hx23_4 hx25_4 hx26_4 hx27_4 hx28_4 hfp_4 hinv_4
  cases sendingHdr with
  | none =>
    simp only [Option.isSome_none, Bool.not_false] at hcap_enc_beq hcap_enc_bne
    (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
    apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 6216#64)
    wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv5
    have hpool5 : A.pool lim st sm4 = A.pool lim st _ := (A.pool_of_vmPreserved hinv5.2).symm
    refine SepWPp.weaken_pre (Entails.of_eq ?_)
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (hinv_4.trans hinv5.1))
    rw [hpool5, etv2_encodeInnerState_keysSampled_eq]
    simp +zetaDelta only [bs2, bs1, encodeOptMessage, List.append_nil, List.append_assoc]; (try sep_ac_rfl)
  | some enc =>
    simp only [Option.isSome_some, Bool.not_true] at hcap_enc_beq hcap_enc_bne
    have hfit_enc : bs2.length + (encodeMessage PolynomialEncoder.encodeRaw 2#32 enc).length ≤ cap.toNat := by
      simp +zetaDelta only [bs2, bs1, encodeOptMessage, List.length_append, List.length_singleton] at hfit ⊢; omega
    (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
    apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 11748#64)
    wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv5
    have hpool5 : A.pool lim st sm4 = A.pool lim st _ := (A.pool_of_vmPreserved hinv5.2).symm
    refine step_send_tail_11748_polyEnc_placed A lim st ext hpolyEnc
      (sp + 4944#64) sp cap ptr g.2 enc bs2 hfit_enc halign
      (F := optHeaderSentPBPinnedAt A.repAlloc g.1 (sp + 4840#64) uc ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hinv_4.trans hinv5.1) (by dsimp only [optPolynomialEncoderPBPinnedAt]; rw [hpool5]; (try sep_ac_rfl)) ?_
    intro sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp hinv_m5
    simp only [arm64_norm, hx19_4, hx20_4, hx21_4, hx23_4, hx25_4, hx28_4, hfp_4]
      at hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp
    refine SepWPp.weaken_pre (Entails.of_eq ?_)
      (hnext sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp hinv_m5)
    rw [etv2_encodeInnerState_keysSampled_eq]
    simp +zetaDelta only [bs2, bs1, encodeOptMessage, optPolynomialEncoderPBPinnedAt, List.append_assoc]
    (try sep_ac_rfl)

end LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerChunked3PlacedBudgetAux

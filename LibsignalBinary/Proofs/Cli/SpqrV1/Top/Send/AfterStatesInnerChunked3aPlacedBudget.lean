/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerChunked3aPlaced
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
# Budget-Threaded Relocatable Phase 3e (Part 3a): `V1State` Variants `idx = 10, 6`

Threads `RustCliAllocBudget` and `VmPreserved` through `V1State::encode_raw` arm
`headerReceived` (`idx = 6`), re-exporting bytes helpers and `ct2Sampled` (`idx = 10`) from `Aux`.
-/

@[expose] public section

set_option linter.style.longLine false
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerChunked3aPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open CryptoVerification (LibsignalPlacement libsignalSessionCode lsmpl lsρ)
open CryptoVerification.RustHeap (vecHeader vecU8At)
open CryptoVerification.LibsignalSpqrV1
  (PolynomialDecoder PolynomialEncoder ProtoAuthenticator V1State)
open CryptoVerification.LibsignalSpqrV1.Proto
  (encodeBytesField encodeMessage encodeOptMessage encodeUint64Field encodeVarint)
open CryptoVerification.SpqrV1.ProtoRepr
  (PolynomialDecoderPBGhost PolynomialEncoderPBGhost Unchunked2PBGhost Unchunked3PBGhost
   ct2SentPBEncodedLen ct2SentPBPinnedAt
   headerReceivedPBEncodedLen headerReceivedPBPinnedAt
   noneCap_add_two_beq_zero noneCap_add_two_bne_zero
   optAuthCap optAuthenticatorPBPinnedAt optAuthenticatorPBPinnedAt_eq
   optCt2SentPBFieldEncodedLen optCt2SentPBPinnedAt
   optHeaderReceivedPBFieldEncodedLen optHeaderReceivedPBPinnedAt
   optPolynomialDecoderPBFieldEncodedLen optPolynomialDecoderPBPinnedAt
   optPolynomialEncoderPBFieldEncodedLen optPolynomialEncoderPBPinnedAt
   polynomialDecoderPBEncodedLen polynomialDecoderPBPinnedAt
   polynomialEncoderPBEncodedLen polynomialEncoderPBPinnedAt
   unchunked2PinnedAt unchunked3PinnedAt
   v1StateInnerPBPinnedAt v1StateInnerPayloadEncodedLen v1StatePBEncodedLen varintLen)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (adds_no_overflow_of_eq cmp_ls_false_of_lt
   hwVarintLen_bvShift_eq_ofNat_varintLen_norm hwVarintLen_eq_ofNat_varintLen_norm
   noneCap_add_one_beq_zero noneCap_add_one_bne_zero
   ofNat_countLeadingZeros_32 ofNat_countLeadingZeros_64 ofNat_length_beq_zero_of_lt
   ule_self_64 ule_zero_64 ult_self_64 ult_zero_64
   vecU8At_eq_header_sep_buf vecU8Buf
   zeroExtend64_beq_zero32 zext64_truncate32)
open CryptoVerification.SpqrV1.Prost.EncodeToVec
  (StepInv bv_optPolyDec_some_eq bv_optPolyEnc_some_eq
   cap_beq_len_false_of_lt elem_len_ult_spare_false_of_le
   encodeToVecCalleeStackOf encodeVarint_length_pos
   etv2_encodeBytesField_3_eq etv2_encodeUint64Field_1_eq etv2_optAuth_cap_bounds
   etv3_bv_optCt2Sent_some_eq etv3_bv_optHeaderReceived_some_eq
   etv3_encodeInnerState_ct2Sampled_eq etv3_encodeInnerState_headerReceived_eq
   etv3_encodeOptCt2Sent_some_eq etv3_encodeOptHeaderReceived_some_eq
   noneCap2_add_two_beq_zero noneCap2_add_two_bne_zero
   noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
   optCt2SentCap optCt2SentPBPinnedAt_cap_bounds optCt2SentPBPinnedAt_eq
   optHeaderReceivedCap optHeaderReceivedPBPinnedAt_cap_bounds optHeaderReceivedPBPinnedAt_eq
   optPolyDecCap optPolyEncCap
   optPolynomialDecoderPBPinnedAt_cap_bounds optPolynomialDecoderPBPinnedAt_eq
   optPolynomialEncoderPBPinnedAt_cap_bounds optPolynomialEncoderPBPinnedAt_eq
   ult_of_lt_of_fit v1StateInnerCap
   vecU8At_expose_one vecU8At_expose_slice vecU8At_pack_one vecU8At_pack_slice
   withStepInv)
open CryptoVerification.SpqrV1.Top.Send
  (spqrSendEncodeJumpTableBytesAt spqrSendEncodeJumpTableBytes_eq)
open CryptoVerification.Cli.SpqrV1.Top.Send.CodePlaced (blkPl_427_ρ)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
  (spqrSendPlacedEntry spqrSendPlacedProg)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerHeaderPlacedBudget
  (StepSendInnerStateAt6616Placed step_send_encode_auth_call_placed
   step_send_encode_varint_call_placed step_send_leaf_encLen16_call_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerChunked1PlacedBudgetAux
  (etvPolyDecoderBudgetExact_of_vm etvPolyEncoderBudgetExact_of_vm
   sepWPp_extract_pure sepWPp_extract_vecU8At_bounds
   step_send_tail_11208_polyDec2_placed step_send_tail_11748_polyEnc_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhaseBudget
  (authEncodeExactSpecOf encodeVarintExactSpecOf etvMemcpyRegionSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsPlacedBudget
  (sepWP_done_tpidr sepWP_done_vm sepWPp_of_sepWP_cs_vm)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonBudget
  (etvPolyDecoderExactSpecOf etvPolyEncoderExactSpecOf leafEncLen16Spec)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonPlacedBudget
  (etvPolyDecoderBudgetExactSpecOf etvPolyEncoderBudgetExactSpecOf)

variable [LibsignalPlacement]

export LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerChunked3aPlacedBudgetAux
  (send3a_step_memcpy_slice_placed send3a_step_bytes_varint_placed step_send_v1_ct2Sampled_placed)

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

/-! ## 3. Variant `idx = 6`: `.headerReceived` (`+8788 .. +11208`) -/

theorem send3a_step_headerReceived_some_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State)) {s0 s : State}
    (hhrLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 482)
      (withStepInv s0 (leafEncLen16Spec (headerReceivedPBPinnedAt A.repAlloc) headerReceivedPBEncodedLen)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hauthEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 454)
      (withStepInv s0 (authEncodeExactSpecOf resStack A lim)))
    (hmemcpy : subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy") etvMemcpyRegionSpec)
    (sp cap ptr w25 : BitVec 64) (g : Unchunked3PBGhost) (u : V1State.Unchunked.HeaderReceived)
    (bs : List (BitVec 8))
    (hu_lt : headerReceivedPBEncodedLen u < 2 ^ 64)
    (hfit : bs.length + (encodeOptMessage V1State.Unchunked.HeaderReceived.encodeRaw 1#32 (some u)).length ≤
      cap.toNat)
    (hcap : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0) (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = spqrSendPlacedEntry + 10948#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx24 : s.readReg64 .x24 = sp + 4704#64) (hx25 : s.readReg64 .x25 = w25) (hinv0 : StepInv s0 s)
    (hP : P = (headerReceivedPBPinnedAt A.repAlloc g (sp + 4840#64) u ∗ ((sp + 16#64) ↦₆₄ w25) ∗
      vecU8At A.repAlloc (sp + 1424#64) cap ptr bs ∗ A.pool lim st s ∗
      stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = spqrSendPlacedEntry + 11196#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x22 = s.readReg64 .x22 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = w25 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((headerReceivedPBPinnedAt A.repAlloc g (sp + 4840#64) u ∗ ((sp + 16#64) ↦₆₄ w25) ∗
          vecU8At A.repAlloc (sp + 1424#64) cap ptr
            (bs ++ encodeOptMessage V1State.Unchunked.HeaderReceived.encodeRaw 1#32 (some u)) ∗
          A.pool lim st sm ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  subst hP
  have ⟨h1432, h1440⟩ : (sp + 1424#64) + 8#64 = sp + 1432#64 ∧ (sp + 1424#64) + 16#64 = sp + 1440#64 :=
    ⟨by bv_omega, by bv_omega⟩
  rw [etv3_encodeOptHeaderReceived_some_eq] at hfit; simp only [List.length_append, List.length_singleton] at hfit
  have hlt1 : bs.length < cap.toNat := by omega
  have hbeq1 := cap_beq_len_false_of_lt hlt1 hcap
  rw [vecU8At_expose_one A.repAlloc (sp + 1424#64) cap ptr bs hlt1 hcap hptr, h1432, h1440]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b0 => ?_
  (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
  apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 482)
  by_vm_steps_safe
    wp_steps
    apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv1
    have hpack1 := vecU8At_pack_one A.repAlloc (sp + 1424#64) cap ptr bs 0x0a#8 hlt1 hcap hptr
    rw [h1432, h1440] at hpack1
    refine step_send_leaf_encLen16_call_placed hres ext (headerReceivedPBPinnedAt A.repAlloc)
      headerReceivedPBEncodedLen hhrLen (sp + 4840#64) sp (spqrSendPlacedEntry + 10992#64) g u hu_lt
      (F := ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs ++ [0x0a#8]) ∗
        A.pool lim st s ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
      (hinv0.trans hinv1.1) (by rw [← hpack1]; (try sep_ac_rfl)) ?_
    intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1
      ⟨hm19, hm20, hm21, hm22, hm23, hm24, hm25, _, hm27, hm28, hmfp, _⟩ hinv_m1 hvm_m1
    simp only [arm64_norm, hx24, hx25] at hm19 hm20 hm21 hm22 hm23 hm24 hm25 hm27 hm28 hmfp
    (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
    apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 451)
    wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv2
    have hpool2 : A.pool lim st s = A.pool lim st _ :=
      (A.pool_of_vmPreserved (hinv1.2.trans (hvm_m1.trans hinv2.2))).symm
    set bs1 := (bs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 (headerReceivedPBEncodedLen u))
    have hfit_var : (bs ++ [0x0a#8]).length +
        (encodeVarint (BitVec.ofNat 64 (headerReceivedPBEncodedLen u))).length ≤ cap.toNat := by
      simp only [List.length_append, List.length_singleton]; omega
    refine step_send_encode_varint_call_placed A lim st hvarint
      (BitVec.ofNat 64 (headerReceivedPBEncodedLen u)) (sp + 1424#64) cap ptr sp
      (spqrSendPlacedEntry + 11000#64) (bs ++ [0x0a#8]) hfit_var
      (F := headerReceivedPBPinnedAt A.repAlloc g (sp + 4840#64) u ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hinv_m1.trans hinv2.1) (by rw [hpool2]; (try sep_ac_rfl)) ?_
    intro sm2 hpcm2 hrunm2 hspm2 htrm2
      ⟨hm2_19, hm2_20, hm2_21, hm2_22, hm2_23, hm2_24, hm2_25, _, hm2_27, hm2_28, hm2_fp, _⟩ hinv_m2
    simp only [arm64_norm, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm27, hm28, hmfp]
      at hm2_19 hm2_20 hm2_21 hm2_22 hm2_23 hm2_24 hm2_25 hm2_27 hm2_28 hm2_fp
    dsimp only [headerReceivedPBPinnedAt, unchunked3PinnedAt]
    have ⟨h4840_24, h4840_72⟩ : (sp + 4840#64) + 0x18#64 = sp + 4864#64 ∧
        (sp + 4840#64) + 0x48#64 = sp + 4912#64 := ⟨by bv_omega, by bv_omega⟩
    rw [h4840_24, h4840_72]
    refine sepWPp_extract_pure
      ((optAuthCap g.auth u.auth + 1#64 == 0#64) = !u.auth.isSome ∧
       (optAuthCap g.auth u.auth + 1#64 != 0#64) = u.auth.isSome)
      (fun R' hm => etv2_optAuth_cap_bounds (A := A.repAlloc) (p := sp + 4864#64)
        (R := vecU8At A.repAlloc (sp + 4840#64) g.f3.cap g.f3.ptr u.hdr ∗
          ((sp + 4912#64) ↦₆₄ u.epoch) ∗ ((sp + 16#64) ↦₆₄ w25) ∗
          vecU8At A.repAlloc (sp + 1424#64) cap ptr bs1 ∗
          A.pool lim st sm2 ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by dsimp only [bs1]; (try sep_ac_rfl))) hm))
      fun ⟨hcap_auth_beq, hcap_auth_bne⟩ => ?_
    set bs2 := bs1 ++ encodeUint64Field 1#32 u.epoch
    suffices h11052 : ∀ sm3 : State,
        sm3.pc = spqrSendPlacedEntry + 11052#64 → sm3.status = .Running → sm3.sp = sp → sm3.trace = s0.trace →
        sm3.readReg64 .x19 = s.readReg64 .x19 → sm3.readReg64 .x20 = s.readReg64 .x20 →
        sm3.readReg64 .x21 = s.readReg64 .x21 → sm3.readReg64 .x22 = s.readReg64 .x22 →
        sm3.readReg64 .x23 = s.readReg64 .x23 → sm3.readReg64 .x24 = sp + 4704#64 →
        sm3.readReg64 .x25 = w25 → sm3.readReg64 .x27 = s.readReg64 .x27 →
        sm3.readReg64 .x28 = s.readReg64 .x28 → sm3.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm3 →
        SepWPp (spqrSendPlacedProg ext) ret sm3
          (((vecU8At A.repAlloc (sp + 4840#64) g.f3.cap g.f3.ptr u.hdr ∗
              optAuthenticatorPBPinnedAt A.repAlloc g.auth (sp + 4864#64) u.auth ∗ ((sp + 4912#64) ↦₆₄ u.epoch)) ∗
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
            (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 11052#64) (bs1 ++ [0x08#8])
            (by simpa only [List.length_append, List.length_singleton] using hfit_ep)
            (F := (vecU8At A.repAlloc (sp + 4840#64) g.f3.cap g.f3.ptr u.hdr ∗
              optAuthenticatorPBPinnedAt A.repAlloc g.auth (sp + 4864#64) u.auth ∗
              ((sp + 4912#64) ↦₆₄ u.epoch)) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hinv_m2.trans hinv3.1) (by rw [← hpack_ep, hpool3]; (try sep_ac_rfl)) ?_
          intro sm3 hpcm3 hrunm3 hspm3 htrm3
            ⟨hm3_19, hm3_20, hm3_21, hm3_22, hm3_23, hm3_24, hm3_25, _, hm3_27, hm3_28, hm3_fp, _⟩ hinv_m3
          simp only [arm64_norm, hm2_19, hm2_20, hm2_21, hm2_22, hm2_23, hm2_24, hm2_25, hm2_27, hm2_28, hm2_fp]
            at hm3_19 hm3_20 hm3_21 hm3_22 hm3_23 hm3_24 hm3_25 hm3_27 hm3_28 hm3_fp
          refine SepWPp.weaken_pre (Entails.of_eq ?_)
            (h11052 sm3 hpcm3 hrunm3 hspm3 htrm3 hm3_19 hm3_20 hm3_21 hm3_22 hm3_23 hm3_24 hm3_25
              hm3_27 hm3_28 hm3_fp hinv_m3)
          simp +zetaDelta only [bs2, etv2_encodeUint64Field_1_eq, hep, Bool.false_eq_true, ↓reduceIte,
            List.append_assoc]; (try sep_ac_rfl)
      · (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
        apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 11052#64)
        wp_steps
        apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv3
        have hpool3 : A.pool lim st sm2 = A.pool lim st _ := (A.pool_of_vmPreserved hinv3.2).symm
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (h11052 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (hinv_m2.trans hinv3.1))
        rw [hpool3]; simp +zetaDelta only [bs2, etv2_encodeUint64Field_1_eq, hep, ↓reduceIte, List.append_nil]
        (try sep_ac_rfl)
    intro sm3 hpcm3 hrunm3 hspm3 htrm3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx27_3 hx28_3 hfp_3 hinv_3
    set bs3 := bs2 ++ encodeOptMessage ProtoAuthenticator.encodeRaw 2#32 u.auth
    suffices h11084 : ∀ sm4 : State,
        sm4.pc = spqrSendPlacedEntry + 11084#64 → sm4.status = .Running → sm4.sp = sp → sm4.trace = s0.trace →
        sm4.readReg64 .x19 = s.readReg64 .x19 → sm4.readReg64 .x20 = s.readReg64 .x20 →
        sm4.readReg64 .x21 = s.readReg64 .x21 → sm4.readReg64 .x22 = s.readReg64 .x22 →
        sm4.readReg64 .x23 = s.readReg64 .x23 → sm4.readReg64 .x25 = w25 →
        sm4.readReg64 .x27 = s.readReg64 .x27 → sm4.readReg64 .x28 = s.readReg64 .x28 →
        sm4.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm4 →
        SepWPp (spqrSendPlacedProg ext) ret sm4
          (((vecU8At A.repAlloc (sp + 4840#64) g.f3.cap g.f3.ptr u.hdr ∗
              optAuthenticatorPBPinnedAt A.repAlloc g.auth (sp + 4864#64) u.auth ∗ ((sp + 4912#64) ↦₆₄ u.epoch)) ∗
            ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A.repAlloc (sp + 1424#64) cap ptr bs3 ∗
            A.pool lim st sm4 ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
          Q Qp oom by
      cases hauth : u.auth with
      | none =>
        rw [optAuthenticatorPBPinnedAt_eq A.repAlloc g.auth (sp + 4864#64) none]
        simp only [hauth, Option.isSome_none, Bool.not_false] at hcap_auth_beq hcap_auth_bne
        (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
        apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 11084#64)
        wp_steps
        apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv4
        have hpool4 : A.pool lim st sm3 = A.pool lim st _ := (A.pool_of_vmPreserved hinv4.2).symm
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (h11084 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hinv_3.trans hinv4.1))
        rw [← optAuthenticatorPBPinnedAt_eq A.repAlloc g.auth (sp + 4864#64) none, hpool4]
        simp +zetaDelta only [bs3, hauth, encodeOptMessage, List.append_nil]; (try sep_ac_rfl)
      | some auth =>
        rw [optAuthenticatorPBPinnedAt_eq A.repAlloc g.auth (sp + 4864#64) (some auth)]
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
        rw [← optAuthenticatorPBPinnedAt_eq A.repAlloc g.auth (sp + 4864#64) (some auth)]
        refine step_send_encode_auth_call_placed A lim st ext hauthEnc
          (sp + 4864#64) (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 11084#64) g.auth auth bs2 hfit_auth
          (F := (vecU8At A.repAlloc (sp + 4840#64) g.f3.cap g.f3.ptr u.hdr ∗
            ((sp + 4912#64) ↦₆₄ u.epoch)) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hinv_3.trans hinv4.1) (by dsimp only [optAuthenticatorPBPinnedAt]; rw [hpool4]; (try sep_ac_rfl)) ?_
        intro sm4 hpcm4 hrunm4 hspm4 htrm4
          ⟨hm4_19, hm4_20, hm4_21, hm4_22, hm4_23, _, hm4_25, _, hm4_27, hm4_28, hm4_fp, _⟩ hinv_m4
        simp only [arm64_norm, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx25_3, hx27_3, hx28_3, hfp_3]
          at hm4_19 hm4_20 hm4_21 hm4_22 hm4_23 hm4_25 hm4_27 hm4_28 hm4_fp
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (h11084 sm4 hpcm4 hrunm4 hspm4 htrm4 hm4_19 hm4_20 hm4_21 hm4_22 hm4_23 hm4_25
            hm4_27 hm4_28 hm4_fp hinv_m4)
        simp +zetaDelta only [bs3, hauth, encodeOptMessage, optAuthenticatorPBPinnedAt]; (try sep_ac_rfl)
    intro sm4 hpcm4 hrunm4 hspm4 htrm4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx25_4 hx27_4 hx28_4 hfp_4 hinv_4
    refine sepWPp_extract_vecU8At_bounds (A := A.repAlloc) (v := sp + 4840#64) (cap := g.f3.cap)
      (ptr := g.f3.ptr) (bs := u.hdr)
      (F := optAuthenticatorPBPinnedAt A.repAlloc g.auth (sp + 4864#64) u.auth ∗
        ((sp + 4912#64) ↦₆₄ u.epoch) ∗ ((sp + 16#64) ↦₆₄ w25) ∗
        vecU8At A.repAlloc (sp + 1424#64) cap ptr bs3 ∗
        A.pool lim st sm4 ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F)
      (by dsimp only [bs3]; (try sep_ac_rfl)) fun hhdr_le hhdr_cap _ => ?_
    have ⟨h4848, h4856⟩ : (sp + 4840#64) + 8#64 = sp + 4848#64 ∧
        (sp + 4840#64) + 16#64 = sp + 4856#64 := ⟨by bv_omega, by bv_omega⟩
    rw [vecU8At_eq_header_sep_buf A.repAlloc (sp + 4840#64), vecHeader, h4848, h4856]
    have hhdr_lt : u.hdr.length < 2 ^ 64 := by omega
    obtain ⟨hbeqz, hbnez⟩ := ofNat_length_beq_zero_of_lt hhdr_lt
    cases hemp : u.hdr.isEmpty
    · simp only [hemp, Bool.not_false] at hbeqz hbnez
      have hne_hdr : u.hdr ≠ [] := List.isEmpty_eq_false_iff.mp hemp
      have henc_eq : encodeBytesField 3#32 u.hdr =
          [0x1a#8] ++ encodeVarint (BitVec.ofNat 64 u.hdr.length) ++ u.hdr := by
        rw [etv2_encodeBytesField_3_eq, hemp]; simp only [Bool.false_eq_true, ↓reduceIte]
      have hfit_all : bs3.length + 1 + (encodeVarint (BitVec.ofNat 64 u.hdr.length)).length + u.hdr.length ≤
          cap.toNat := by
        rw [henc_eq] at hfit; dsimp only [bs3, bs2, bs1] at hfit ⊢
        simp only [List.length_append, List.length_singleton] at hfit ⊢; omega
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
          (spqrSendPlacedEntry + 11144#64) bs3 u.hdr hemp hfit_all hcap hptr halign
          (F := (((sp + 4840#64) ↦₆₄ g.f3.cap) ∗ ((sp + 4848#64) ↦₆₄ g.f3.ptr) ∗
              ((sp + 4856#64) ↦₆₄ BitVec.ofNat 64 u.hdr.length)) ∗
            vecU8Buf A.repAlloc g.f3.cap g.f3.ptr u.hdr ∗
            optAuthenticatorPBPinnedAt A.repAlloc g.auth (sp + 4864#64) u.auth ∗
            ((sp + 4912#64) ↦₆₄ u.epoch) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (hinv_4.trans hinv5.1) (by rw [hpool5]; (try sep_ac_rfl)) ?_
        intro sm5 bs4 hpcm5 hrunm5 hspm5 htrm5
          ⟨hm5_19, hm5_20, hm5_21, hm5_22, hm5_23, hm5_24, hm5_25, hm5_26, hm5_27, hm5_28, hm5_fp, _⟩
          hinv_m5 hfit_mc hcmp_mc
        simp only [arm64_norm, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx27_4, hx28_4, hfp_4]
          at hm5_19 hm5_20 hm5_21 hm5_22 hm5_23 hm5_24 hm5_25 hm5_26 hm5_27 hm5_28 hm5_fp
        (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
        apply sepWPp_of_sepWP_cs_vm (mid := lsρ "memcpy")
        wp_steps
        apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv6
        have hpool6 : A.pool lim st sm5 = A.pool lim st _ := (A.pool_of_vmPreserved hinv6.2).symm
        refine send3a_step_memcpy_slice_placed A lim st ext hmemcpy sp cap ptr g.f3.cap g.f3.ptr
          (spqrSendPlacedEntry + 11184#64) bs4 u.hdr hemp hhdr_le halign
          (F := (((sp + 4840#64) ↦₆₄ g.f3.cap) ∗ ((sp + 4848#64) ↦₆₄ g.f3.ptr) ∗
              ((sp + 4856#64) ↦₆₄ BitVec.ofNat 64 u.hdr.length)) ∗
            optAuthenticatorPBPinnedAt A.repAlloc g.auth (sp + 4864#64) u.auth ∗
            ((sp + 4912#64) ↦₆₄ u.epoch) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hhdr_lt
          (hinv_m5.trans hinv6.1) (by rw [hpool6]; (try sep_ac_rfl)) ?_
        intro sm6 hpcm6 hrunm6 hspm6 htrm6
          ⟨hm6_19, hm6_20, hm6_21, hm6_22, hm6_23, hm6_24, _, hm6_26, hm6_27, hm6_28, hm6_fp, _⟩ hinv_m6
        simp only [arm64_norm, hm5_19, hm5_20, hm5_21, hm5_22, hm5_23, hm5_24, hm5_26, hm5_27, hm5_28, hm5_fp]
          at hm6_19 hm6_20 hm6_21 hm6_22 hm6_23 hm6_24 hm6_26 hm6_27 hm6_28 hm6_fp
        (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
        apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 11196#64)
        by_vm_steps_safe
          wp_steps
          apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, wp_norm, *])
          intro hinv7
          have hpool7 : A.pool lim st sm6 = A.pool lim st _ := (A.pool_of_vmPreserved hinv7.2).symm
          have hpack_mc := vecU8At_pack_slice A.repAlloc (sp + 1424#64) cap ptr bs4 u.hdr hfit_mc hcap hptr hne_hdr
          have hbs_eq : bs4 ++ u.hdr = bs ++ encodeOptMessage V1State.Unchunked.HeaderReceived.encodeRaw 1#32 (some u) := by
            rw [etv3_encodeOptHeaderReceived_some_eq, henc_eq]
            dsimp only [bs4, bs3, bs2, bs1]; simp only [List.append_assoc]
          rw [h1432, h1440, hbs_eq] at hpack_mc
          refine SepWPp.weaken_pre (Entails.of_eq ?_)
            (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (hinv_m6.trans hinv7.1))
          rw [hpool7]; dsimp only [headerReceivedPBPinnedAt, unchunked3PinnedAt]
          rw [h4840_24, h4840_72, vecU8At_eq_header_sep_buf A.repAlloc (sp + 4840#64), vecHeader,
            h4848, h4856, ← hpack_mc]; (try sep_ac_rfl)
    · simp only [hemp, Bool.not_true] at hbeqz hbnez
      have henc_nil : encodeBytesField 3#32 u.hdr = [] := by
        rw [etv2_encodeBytesField_3_eq, hemp]; simp only [↓reduceIte]
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
      apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 11196#64)
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
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hinv_4.trans hinv5.1))
      rw [hpool5]; dsimp only [headerReceivedPBPinnedAt, unchunked3PinnedAt]
      rw [h4840_24, h4840_72, vecU8At_eq_header_sep_buf A.repAlloc (sp + 4840#64), vecHeader,
        h4848, h4856, etv3_encodeOptHeaderReceived_some_eq, henc_nil]
      dsimp only [bs3, bs2, bs1]; simp only [List.append_nil, List.append_assoc]; (try sep_ac_rfl)

theorem step_send_v1_headerReceived_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State)) {s0 s : State}
    (hhrLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 482)
      (withStepInv s0 (leafEncLen16Spec (headerReceivedPBPinnedAt A.repAlloc) headerReceivedPBEncodedLen)))
    (hpolyDecLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 493)
      (withStepInv s0 (leafEncLen16Spec (polynomialDecoderPBPinnedAt A.repAlloc) polynomialDecoderPBEncodedLen)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hauthEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 454)
      (withStepInv s0 (authEncodeExactSpecOf resStack A lim)))
    (hmemcpy : subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy") etvMemcpyRegionSpec)
    (hpolyDec : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 455)
      (withStepInv s0 (etvPolyDecoderBudgetExactSpecOf resStack A lim)))
    (sp cap ptr w25 : BitVec 64) (g : Unchunked3PBGhost × PolynomialDecoderPBGhost)
    (v : V1State.Chunked.HeaderReceived) (bs : List (BitVec 8))
    (hv_len : v1StatePBEncodedLen ⟨some (.headerReceived v)⟩ < 2 ^ 64)
    (hfit : bs.length + (V1State.InnerState.encode (.headerReceived v)).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = spqrSendPlacedEntry + 8788#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace) (hinv0 : StepInv s0 s)
    (hP : P = ((optHeaderReceivedPBPinnedAt A.repAlloc g.1 (sp + 4840#64) v.uc ∗
        optPolynomialDecoderPBPinnedAt A.repAlloc g.2 (sp + 4920#64) v.receivingEk) ∗
      ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A.repAlloc (sp + 1424#64) cap ptr bs ∗
      A.pool lim st s ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = spqrSendPlacedEntry + 6216#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = w25 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        (((optHeaderReceivedPBPinnedAt A.repAlloc g.1 (sp + 4840#64) v.uc ∗
            optPolynomialDecoderPBPinnedAt A.repAlloc g.2 (sp + 4920#64) v.receivingEk) ∗
          ((sp + 16#64) ↦₆₄ w25) ∗
          vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs ++ V1State.InnerState.encode (.headerReceived v)) ∗
          A.pool lim st sm ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  subst hP; rcases v with ⟨uc, receivingEk⟩
  rw [etv3_encodeInnerState_headerReceived_eq] at hfit; simp only [List.length_append, List.length_singleton] at hfit
  have hsub_len : v1StateInnerPayloadEncodedLen (.headerReceived ⟨uc, receivingEk⟩) < 2 ^ 64 := by
    dsimp only [v1StatePBEncodedLen] at hv_len; omega
  have hlt1 : bs.length < cap.toNat := by omega
  have hfit_var : (bs ++ [0x3a#8]).length +
      (encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.headerReceived ⟨uc, receivingEk⟩)))).length ≤
      cap.toNat := by
    simp only [List.length_append, List.length_singleton]; omega
  refine sepWPp_extract_vecU8At_bounds (v := sp + 1424#64) (cap := cap) (ptr := ptr) (bs := bs)
    (F := optHeaderReceivedPBPinnedAt A.repAlloc g.1 (sp + 4840#64) uc ∗
      optPolynomialDecoderPBPinnedAt A.repAlloc g.2 (sp + 4920#64) receivingEk ∗
      ((sp + 16#64) ↦₆₄ w25) ∗ A.pool lim st s ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F)
    (by sep_ac_rfl) fun _ hcap hptr => ?_
  refine sepWPp_extract_pure
    (((optHeaderReceivedCap g.1 uc + 1#64 == 0#64) = !uc.isSome ∧
      (optHeaderReceivedCap g.1 uc + 1#64 != 0#64) = uc.isSome) ∧
     ((optPolyDecCap g.2 receivingEk + 1#64 == 0#64) = !receivingEk.isSome ∧
      (optPolyDecCap g.2 receivingEk + 1#64 != 0#64) = receivingEk.isSome))
    (fun R' hm => ⟨optHeaderReceivedPBPinnedAt_cap_bounds (p := sp + 4840#64)
        (R := optPolynomialDecoderPBPinnedAt A.repAlloc g.2 (sp + 4920#64) receivingEk ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A.repAlloc (sp + 1424#64) cap ptr bs ∗
          A.pool lim st s ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm),
      optPolynomialDecoderPBPinnedAt_cap_bounds (p := sp + 4920#64)
        (R := optHeaderReceivedPBPinnedAt A.repAlloc g.1 (sp + 4840#64) uc ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A.repAlloc (sp + 1424#64) cap ptr bs ∗
          A.pool lim st s ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm)⟩)
    fun ⟨⟨hcap_uc_beq, hcap_uc_bne⟩, ⟨hcap_dec_beq, hcap_dec_bne⟩⟩ => ?_
  have hbeq_false := cap_beq_len_false_of_lt hlt1 hcap
  have ⟨h1432, h1440⟩ : (sp + 1424#64) + 8#64 = sp + 1432#64 ∧ (sp + 1424#64) + 16#64 = sp + 1440#64 :=
    ⟨by bv_omega, by bv_omega⟩
  have hpack := vecU8At_pack_one A.repAlloc (sp + 1424#64) cap ptr bs 0x3a#8 hlt1 hcap hptr
  rw [h1432, h1440] at hpack
  suffices h9796 : ∀ sm1 : State,
      sm1.pc = spqrSendPlacedEntry + 9796#64 → sm1.status = .Running → sm1.sp = sp → sm1.trace = s0.trace →
      sm1.readReg64 .x19 = s.readReg64 .x19 → sm1.readReg64 .x21 = s.readReg64 .x21 →
      sm1.readReg64 .x23 = s.readReg64 .x23 → sm1.readReg64 .x24 = sp + 4704#64 →
      sm1.readReg64 .x25 = optHeaderReceivedCap g.1 uc →
      sm1.readReg64 .x26 = BitVec.ofNat 64 (optHeaderReceivedPBFieldEncodedLen uc) →
      sm1.readReg64 .x27 = s.readReg64 .x27 → sm1.readReg64 .x28 = s.readReg64 .x28 →
      sm1.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm1 →
      SepWPp (spqrSendPlacedProg ext) ret sm1
        (((optHeaderReceivedPBPinnedAt A.repAlloc g.1 (sp + 4840#64) uc ∗
            optPolynomialDecoderPBPinnedAt A.repAlloc g.2 (sp + 4920#64) receivingEk) ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs ++ [0x3a#8]) ∗
          A.pool lim st sm1 ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom by
    rw [vecU8At_expose_one A.repAlloc (sp + 1424#64) cap ptr bs hlt1 hcap hptr, h1432, h1440]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b0 => ?_
    cases uc with
    | none =>
      rw [optHeaderReceivedPBPinnedAt_eq A.repAlloc g.1 (sp + 4840#64) none]
      simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
      apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 9796#64)
      by_vm_steps_safe
        wp_steps
        apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv1
        have hpool1 : A.pool lim st s = A.pool lim st _ := (A.pool_of_vmPreserved hinv1.2).symm
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (h9796 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *])
            (by simp only [optHeaderReceivedPBFieldEncodedLen, arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (hinv0.trans hinv1.1))
        rw [← optHeaderReceivedPBPinnedAt_eq A.repAlloc g.1 (sp + 4840#64) none, ← hpack, hpool1]; (try sep_ac_rfl)
    | some u =>
      rw [optHeaderReceivedPBPinnedAt_eq A.repAlloc g.1 (sp + 4840#64) (some u)]
      simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      have ⟨hu_fit, hopt_u_lt⟩ :
          headerReceivedPBEncodedLen u < 2 ^ 64 ∧ optHeaderReceivedPBFieldEncodedLen (some u) < 2 ^ 64 :=
        ⟨by dsimp only [v1StateInnerPayloadEncodedLen, optHeaderReceivedPBFieldEncodedLen] at hsub_len; omega,
         by dsimp only [v1StateInnerPayloadEncodedLen] at hsub_len; omega⟩
      have hvar_u_lt : varintLen (BitVec.ofNat 64 (headerReceivedPBEncodedLen u)) <
          optHeaderReceivedPBFieldEncodedLen (some u) := by
        dsimp only [optHeaderReceivedPBFieldEncodedLen]; omega
      have ⟨⟨_, _, _, _, _⟩, hult_u, hopt_u_eq⟩ :=
        (⟨cmp_ls_false_of_lt hvar_u_lt hopt_u_lt, ult_of_lt_of_fit hvar_u_lt hopt_u_lt,
          etv3_bv_optHeaderReceived_some_eq u⟩ : _ ∧ _ ∧ _)
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
      apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 482)
      by_vm_steps_safe
        wp_steps
        apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv1
        rw [← optHeaderReceivedPBPinnedAt_eq A.repAlloc g.1 (sp + 4840#64) (some u)]
        refine step_send_leaf_encLen16_call_placed hres ext (headerReceivedPBPinnedAt A.repAlloc)
          headerReceivedPBEncodedLen hhrLen (sp + 4840#64) sp (spqrSendPlacedEntry + 8852#64) g.1 u hu_fit
          (F := optPolynomialDecoderPBPinnedAt A.repAlloc g.2 (sp + 4920#64) receivingEk ∗
            ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs ++ [0x3a#8]) ∗
            A.pool lim st s ∗ F)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
          (hinv0.trans hinv1.1) (by rw [← hpack]; dsimp only [optHeaderReceivedPBPinnedAt]; (try sep_ac_rfl)) ?_
        intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1
          ⟨hm19, _, hm21, _, hm23, hm24, hm25, _, hm27, hm28, hmfp, _⟩ hinv_m1 hvm_m1
        simp only [arm64_norm] at hm19 hm21 hm23 hm24 hm25 hm27 hm28 hmfp
        (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
        apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 9796#64)
        wp_steps
        apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv2
        have hpool2 : A.pool lim st s = A.pool lim st _ :=
          (A.pool_of_vmPreserved (hinv1.2.trans (hvm_m1.trans hinv2.2))).symm
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (h9796 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hinv_m1.trans hinv2.1))
        dsimp only [optHeaderReceivedPBPinnedAt]; rw [hpool2]; (try sep_ac_rfl)
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx19_1 hx21_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hinv_1
  suffices h10920 : ∀ sm2 : State,
      sm2.pc = spqrSendPlacedEntry + 10920#64 → sm2.status = .Running → sm2.sp = sp → sm2.trace = s0.trace →
      sm2.readReg64 .x8 = BitVec.ofNat 64 (optPolynomialDecoderPBFieldEncodedLen receivingEk) →
      sm2.readReg64 .x19 = s.readReg64 .x19 → sm2.readReg64 .x20 = sp + 4704#64 →
      sm2.readReg64 .x21 = s.readReg64 .x21 → sm2.readReg64 .x22 = optPolyDecCap g.2 receivingEk →
      sm2.readReg64 .x23 = s.readReg64 .x23 → sm2.readReg64 .x24 = sp + 4704#64 →
      sm2.readReg64 .x25 = optHeaderReceivedCap g.1 uc →
      sm2.readReg64 .x26 = BitVec.ofNat 64 (optHeaderReceivedPBFieldEncodedLen uc) →
      sm2.readReg64 .x27 = s.readReg64 .x27 → sm2.readReg64 .x28 = s.readReg64 .x28 →
      sm2.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm2 →
      SepWPp (spqrSendPlacedProg ext) ret sm2
        (((optHeaderReceivedPBPinnedAt A.repAlloc g.1 (sp + 4840#64) uc ∗
            optPolynomialDecoderPBPinnedAt A.repAlloc g.2 (sp + 4920#64) receivingEk) ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs ++ [0x3a#8]) ∗
          A.pool lim st sm2 ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom by
    cases receivingEk with
    | none =>
      rw [optPolynomialDecoderPBPinnedAt_eq A.repAlloc g.2 (sp + 4920#64) none]
      simp only [Option.isSome_none, Bool.not_false] at hcap_dec_beq hcap_dec_bne
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
      apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 10920#64)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv2
      have hpool2 : A.pool lim st sm1 = A.pool lim st _ := (A.pool_of_vmPreserved hinv2.2).symm
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h10920 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [optPolynomialDecoderPBFieldEncodedLen, arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_1.trans hinv2.1))
      rw [← optPolynomialDecoderPBPinnedAt_eq A.repAlloc g.2 (sp + 4920#64) none, hpool2]; (try sep_ac_rfl)
    | some dec =>
      rw [optPolynomialDecoderPBPinnedAt_eq A.repAlloc g.2 (sp + 4920#64) (some dec)]
      simp only [Option.isSome_some, Bool.not_true] at hcap_dec_beq hcap_dec_bne
      have ⟨hdec_fit, hopt_d_lt⟩ :
          polynomialDecoderPBEncodedLen dec < 2 ^ 64 ∧ optPolynomialDecoderPBFieldEncodedLen (some dec) < 2 ^ 64 :=
        ⟨by dsimp only [v1StateInnerPayloadEncodedLen, optPolynomialDecoderPBFieldEncodedLen] at hsub_len; omega,
         by dsimp only [v1StateInnerPayloadEncodedLen] at hsub_len; omega⟩
      have hvar_d_lt : varintLen (BitVec.ofNat 64 (polynomialDecoderPBEncodedLen dec)) <
          optPolynomialDecoderPBFieldEncodedLen (some dec) := by
        dsimp only [optPolynomialDecoderPBFieldEncodedLen]; omega
      have ⟨⟨_, _, _, _, _⟩, hult_d, hopt_d_eq⟩ :=
        (⟨cmp_ls_false_of_lt hvar_d_lt hopt_d_lt, ult_of_lt_of_fit hvar_d_lt hopt_d_lt,
          bv_optPolyDec_some_eq dec⟩ : _ ∧ _ ∧ _)
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
      apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 493)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv2
      rw [← optPolynomialDecoderPBPinnedAt_eq A.repAlloc g.2 (sp + 4920#64) (some dec)]
      refine step_send_leaf_encLen16_call_placed hres ext (polynomialDecoderPBPinnedAt A.repAlloc)
        polynomialDecoderPBEncodedLen hpolyDecLen (sp + 4920#64) sp (spqrSendPlacedEntry + 9824#64) g.2 dec hdec_fit
        (F := optHeaderReceivedPBPinnedAt A.repAlloc g.1 (sp + 4840#64) uc ∗ ((sp + 16#64) ↦₆₄ w25) ∗
          vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs ++ [0x3a#8]) ∗ A.pool lim st sm1 ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (hinv_1.trans hinv2.1) (by dsimp only [optPolynomialDecoderPBPinnedAt]; (try sep_ac_rfl)) ?_
      intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx0m2
        ⟨hm2_19, hm2_20, hm2_21, hm2_22, hm2_23, hm2_24, hm2_25, hm2_26, hm2_27, hm2_28, hm2_fp, _⟩
        hinv_m2 hvm_m2
      simp only [arm64_norm, hx19_1, hx21_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1]
        at hm2_19 hm2_20 hm2_21 hm2_22 hm2_23 hm2_24 hm2_25 hm2_26 hm2_27 hm2_28 hm2_fp
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
      apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 10920#64)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv3
      have hpool3 : A.pool lim st sm1 = A.pool lim st _ :=
        (A.pool_of_vmPreserved (hinv2.2.trans (hvm_m2.trans hinv3.2))).symm
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h10920 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hinv_m2.trans hinv3.1))
      dsimp only [optPolynomialDecoderPBPinnedAt]; rw [hpool3]; (try sep_ac_rfl)
  intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx8_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hinv_2
  have ⟨hadd_sum, hult_sum, hule_sum, hult_sum2, hule_sum2⟩ := adds_no_overflow_of_eq
    (a := optPolynomialDecoderPBFieldEncodedLen receivingEk) (b := optHeaderReceivedPBFieldEncodedLen uc)
    (c := v1StateInnerPayloadEncodedLen (.headerReceived ⟨uc, receivingEk⟩)) rfl hsub_len
  (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
  apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 451)
  wp_steps
  apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, wp_norm, *])
  intro hinv3
  have hpool3 : A.pool lim st sm2 = A.pool lim st _ := (A.pool_of_vmPreserved hinv3.2).symm
  set bs1 := (bs ++ [0x3a#8]) ++
    encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.headerReceived ⟨uc, receivingEk⟩)))
  refine step_send_encode_varint_call_placed A lim st hvarint
    (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.headerReceived ⟨uc, receivingEk⟩)))
    (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 10936#64) (bs ++ [0x3a#8]) hfit_var
    (F := (optHeaderReceivedPBPinnedAt A.repAlloc g.1 (sp + 4840#64) uc ∗
      optPolynomialDecoderPBPinnedAt A.repAlloc g.2 (sp + 4920#64) receivingEk) ∗
      ((sp + 16#64) ↦₆₄ w25) ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_2.trans hinv3.1)
    (by rw [hpool3]; (try sep_ac_rfl)) ?_
  intro sm3 hpcm3 hrunm3 hspm3 htrm3
    ⟨hm3_19, hm3_20, hm3_21, hm3_22, hm3_23, hm3_24, hm3_25, _, hm3_27, hm3_28, hm3_fp, _⟩ hinv_m3
  simp only [arm64_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx27_2, hx28_2, hfp_2]
    at hm3_19 hm3_20 hm3_21 hm3_22 hm3_23 hm3_24 hm3_25 hm3_27 hm3_28 hm3_fp
  set bs2 := bs1 ++ encodeOptMessage V1State.Unchunked.HeaderReceived.encodeRaw 1#32 uc
  suffices h11196 : ∀ sm4 : State,
      sm4.pc = spqrSendPlacedEntry + 11196#64 → sm4.status = .Running → sm4.sp = sp → sm4.trace = s0.trace →
      sm4.readReg64 .x19 = s.readReg64 .x19 → sm4.readReg64 .x20 = sp + 4704#64 →
      sm4.readReg64 .x21 = s.readReg64 .x21 → sm4.readReg64 .x22 = optPolyDecCap g.2 receivingEk →
      sm4.readReg64 .x23 = s.readReg64 .x23 → sm4.readReg64 .x25 = w25 →
      sm4.readReg64 .x27 = s.readReg64 .x27 → sm4.readReg64 .x28 = s.readReg64 .x28 →
      sm4.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm4 →
      SepWPp (spqrSendPlacedProg ext) ret sm4
        (((optHeaderReceivedPBPinnedAt A.repAlloc g.1 (sp + 4840#64) uc ∗
            optPolynomialDecoderPBPinnedAt A.repAlloc g.2 (sp + 4920#64) receivingEk) ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A.repAlloc (sp + 1424#64) cap ptr bs2 ∗
          A.pool lim st sm4 ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom by
    cases uc with
    | none =>
      simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
      apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 11196#64)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv4
      have hpool4 : A.pool lim st sm3 = A.pool lim st _ := (A.pool_of_vmPreserved hinv4.2).symm
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h11196 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hinv_m3.trans hinv4.1))
      rw [hpool4]; simp +zetaDelta only [bs2, bs1, encodeOptMessage, List.append_nil]; (try sep_ac_rfl)
    | some u =>
      simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      have hu_lt : headerReceivedPBEncodedLen u < 2 ^ 64 := by
        dsimp only [v1StateInnerPayloadEncodedLen, optHeaderReceivedPBFieldEncodedLen] at hsub_len; omega
      have hfit_u : bs1.length + (encodeOptMessage V1State.Unchunked.HeaderReceived.encodeRaw 1#32 (some u)).length ≤
          cap.toNat := by
        dsimp only [bs1]; simp only [List.length_append, List.length_singleton] at hfit ⊢; omega
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
      apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 10948#64)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv4
      have hpool4 : A.pool lim st sm3 = A.pool lim st _ := (A.pool_of_vmPreserved hinv4.2).symm
      refine send3a_step_headerReceived_some_placed hres A lim st ext
        hhrLen hvarint hauthEnc hmemcpy sp cap ptr w25 g.1 u bs1 hu_lt hfit_u hcap hptr halign
        (F := optPolynomialDecoderPBPinnedAt A.repAlloc g.2 (sp + 4920#64) receivingEk ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hinv_m3.trans hinv4.1)
        (by dsimp only [bs1, optHeaderReceivedPBPinnedAt]; rw [hpool4]; (try sep_ac_rfl)) ?_
      intro sm4 hpcm4 hrunm4 hspm4 htrm4 hm4_19 hm4_20 hm4_21 hm4_22 hm4_23 hm4_25 hm4_27 hm4_28 hm4_fp hinv_m4
      simp only [arm64_norm, hm3_19, hm3_20, hm3_21, hm3_22, hm3_23, hm3_27, hm3_28, hm3_fp]
        at hm4_19 hm4_20 hm4_21 hm4_22 hm4_23 hm4_25 hm4_27 hm4_28 hm4_fp
      refine SepWPp.weaken_pre
        (Entails.of_eq (by dsimp only [bs2, bs1, optHeaderReceivedPBPinnedAt]; (try sep_ac_rfl)))
        (h11196 sm4 hpcm4 hrunm4 hspm4 htrm4 hm4_19 hm4_20 hm4_21 hm4_22 hm4_23 hm4_25
          hm4_27 hm4_28 hm4_fp hinv_m4)
  intro sm4 hpcm4 hrunm4 hspm4 htrm4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx25_4 hx27_4 hx28_4 hfp_4 hinv_4
  cases receivingEk with
  | none =>
    simp only [Option.isSome_none, Bool.not_false] at hcap_dec_beq hcap_dec_bne
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
    rw [hpool5, etv3_encodeInnerState_headerReceived_eq]
    simp +zetaDelta only [bs2, bs1, encodeOptMessage, List.append_nil, List.append_assoc]; (try sep_ac_rfl)
  | some dec =>
    simp only [Option.isSome_some, Bool.not_true] at hcap_dec_beq hcap_dec_bne
    have hfit_dec : bs2.length + (encodeMessage PolynomialDecoder.encodeRaw 2#32 dec).length ≤ cap.toNat := by
      simp +zetaDelta only [bs2, bs1, encodeOptMessage, List.length_append, List.length_singleton] at hfit ⊢; omega
    (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
    apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 11208#64)
    wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv5
    have hpool5 : A.pool lim st sm4 = A.pool lim st _ := (A.pool_of_vmPreserved hinv5.2).symm
    refine step_send_tail_11208_polyDec2_placed A lim st ext hpolyDec
      (sp + 4920#64) sp cap ptr g.2 dec bs2 hfit_dec halign
      (F := optHeaderReceivedPBPinnedAt A.repAlloc g.1 (sp + 4840#64) uc ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hinv_4.trans hinv5.1) (by dsimp only [optPolynomialDecoderPBPinnedAt]; rw [hpool5]; (try sep_ac_rfl)) ?_
    intro sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp hinv_m5
    simp only [arm64_norm, hx19_4, hx21_4, hx23_4, hx25_4, hx27_4, hx28_4, hfp_4]
      at hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp
    refine SepWPp.weaken_pre (Entails.of_eq ?_)
      (hnext sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp hinv_m5)
    rw [etv3_encodeInnerState_headerReceived_eq]
    simp +zetaDelta only [bs2, bs1, encodeOptMessage, optPolynomialDecoderPBPinnedAt, List.append_assoc]
    (try sep_ac_rfl)

/-! ## 4. `StepSendInnerStateAt6616Placed` Bridges (`idx = 10, 6`) -/

theorem step_send_v1_ct2Sampled_at_6616_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (ext : String → Option (State → State))
    {roBase : BitVec 64} {s0 : State}
    (hct2Len : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 470)
      (withStepInv s0 (leafEncLen16Spec (ct2SentPBPinnedAt A.repAlloc) ct2SentPBEncodedLen)))
    (hpolyEncLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 480)
      (withStepInv s0 (leafEncLen16Spec (polynomialEncoderPBPinnedAt A.repAlloc) polynomialEncoderPBEncodedLen)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hauthEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 454)
      (withStepInv s0 (authEncodeExactSpecOf resStack A lim)))
    (hpolyEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 456)
      (withStepInv s0 (etvPolyEncoderBudgetExactSpecOf resStack A lim)))
    (v : V1State.Chunked.Ct2Sampled) :
    StepSendInnerStateAt6616Placed resStack A lim st0 ext roBase s0 (.ct2Sampled v) := by
  intro sp cap ptr w25 g bs hv_len hfit halign ret s P F Q Qp oom
    hpc hrun hsp htr hx8 hx9 hx20 hx25 hinv0 hP hnext
  subst hP
  replace hx8 : s.readReg64 .x8 = 10#64 :=
    hx8.trans (by rw [show v1StateInnerCap g (.ct2Sampled v) = 0x800000000000000a#64 from rfl]; decide +kernel)
  rw [spqrSendEncodeJumpTableBytes_eq roBase]; dsimp only [spqrSendEncodeJumpTableBytesAt]
  (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
  apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 8896#64)
  wp_steps
  apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, wp_norm, *])
  intro hinv1
  have hpool1 : A.pool lim st0 s = A.pool lim st0 _ := (A.pool_of_vmPreserved hinv1.2).symm
  have ⟨h4840, h4896⟩ : (sp + 4832#64) + 8#64 = sp + 4840#64 ∧
      (sp + 4832#64) + 64#64 = sp + 4896#64 := ⟨by bv_omega, by bv_omega⟩
  dsimp only [v1StateInnerPBPinnedAt]; rw [h4840, h4896]
  refine step_send_v1_ct2Sampled_placed hres A lim st0 ext
    hct2Len hpolyEncLen hvarint hauthEnc hpolyEnc
    sp cap ptr w25 g.b.gCt2Sampled v bs hv_len hfit halign
    (F := ((sp + 4832#64) ↦₆₄ 0x800000000000000a#64) ∗
      memRegion (sp + 4832#64 + 120#64) 104 ∗ spqrSendEncodeJumpTableBytesAt roBase ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1.1)
    (by dsimp only [spqrSendEncodeJumpTableBytesAt]; rw [hpool1]; (try sep_ac_rfl)) ?_
  intro sm hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m
  simp only [arm64_norm] at hm19 hm21 hm23 hm27 hm28 hmfp
  refine SepWPp.weaken_pre ?_
    (hnext sm hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m)
  dsimp only [v1StateInnerPBPinnedAt]; rw [h4840, h4896, spqrSendEncodeJumpTableBytes_eq roBase]
  exact Entails.of_eq (by sep_ac_rfl)

theorem step_send_v1_headerReceived_at_6616_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (ext : String → Option (State → State))
    {roBase : BitVec 64} {s0 : State}
    (hhrLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 482)
      (withStepInv s0 (leafEncLen16Spec (headerReceivedPBPinnedAt A.repAlloc) headerReceivedPBEncodedLen)))
    (hpolyDecLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 493)
      (withStepInv s0 (leafEncLen16Spec (polynomialDecoderPBPinnedAt A.repAlloc) polynomialDecoderPBEncodedLen)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hauthEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 454)
      (withStepInv s0 (authEncodeExactSpecOf resStack A lim)))
    (hmemcpy : subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy") etvMemcpyRegionSpec)
    (hpolyDec : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 455)
      (withStepInv s0 (etvPolyDecoderBudgetExactSpecOf resStack A lim)))
    (v : V1State.Chunked.HeaderReceived) :
    StepSendInnerStateAt6616Placed resStack A lim st0 ext roBase s0 (.headerReceived v) := by
  intro sp cap ptr w25 g bs hv_len hfit halign ret s P F Q Qp oom
    hpc hrun hsp htr hx8 hx9 hx20 hx25 hinv0 hP hnext
  subst hP
  replace hx8 : s.readReg64 .x8 = 6#64 :=
    hx8.trans (by rw [show v1StateInnerCap g (.headerReceived v) = 0x8000000000000006#64 from rfl]; decide +kernel)
  rw [spqrSendEncodeJumpTableBytes_eq roBase]; dsimp only [spqrSendEncodeJumpTableBytesAt]
  (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
  apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 8788#64)
  wp_steps
  apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, wp_norm, *])
  intro hinv1
  have hpool1 : A.pool lim st0 s = A.pool lim st0 _ := (A.pool_of_vmPreserved hinv1.2).symm
  have ⟨h4840, h4920⟩ : (sp + 4832#64) + 8#64 = sp + 4840#64 ∧
      (sp + 4832#64) + 88#64 = sp + 4920#64 := ⟨by bv_omega, by bv_omega⟩
  dsimp only [v1StateInnerPBPinnedAt]; rw [h4840, h4920]
  refine step_send_v1_headerReceived_placed hres A lim st0 ext
    hhrLen hpolyDecLen hvarint hauthEnc hmemcpy hpolyDec
    sp cap ptr w25 g.b.gHeaderReceived v bs hv_len hfit halign
    (F := ((sp + 4832#64) ↦₆₄ 0x8000000000000006#64) ∗
      memRegion (sp + 4832#64 + 128#64) 96 ∗ spqrSendEncodeJumpTableBytesAt roBase ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1.1)
    (by dsimp only [spqrSendEncodeJumpTableBytesAt]; rw [hpool1]; (try sep_ac_rfl)) ?_
  intro sm hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m
  simp only [arm64_norm] at hm19 hm21 hm23 hm27 hm28 hmfp
  refine SepWPp.weaken_pre ?_
    (hnext sm hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m)
  dsimp only [v1StateInnerPBPinnedAt]; rw [h4840, h4920, spqrSendEncodeJumpTableBytes_eq roBase]
  exact Entails.of_eq (by sep_ac_rfl)

/-! ### `VmPreserved` Callee-Spec Corollaries -/

theorem step_send_v1_ct2Sampled_at_6616_vm_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (ext : String → Option (State → State))
    {roBase : BitVec 64} {s0 : State}
    (hct2Len : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 470)
      (withStepInv s0 (leafEncLen16Spec (ct2SentPBPinnedAt A.repAlloc) ct2SentPBEncodedLen)))
    (hpolyEncLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 480)
      (withStepInv s0 (leafEncLen16Spec (polynomialEncoderPBPinnedAt A.repAlloc) polynomialEncoderPBEncodedLen)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hauthEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 454)
      (withStepInv s0 (authEncodeExactSpecOf resStack A lim)))
    (hpolyEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 456)
      (withStepInv s0 (etvPolyEncoderExactSpecOf resStack A.repAlloc)))
    (v : V1State.Chunked.Ct2Sampled) :
    StepSendInnerStateAt6616Placed resStack A lim st0 ext roBase s0 (.ct2Sampled v) :=
  step_send_v1_ct2Sampled_at_6616_placed hres A lim st0 ext
    hct2Len hpolyEncLen hvarint hauthEnc
    (etvPolyEncoderBudgetExact_of_vm hpolyEnc) v

theorem step_send_v1_headerReceived_at_6616_vm_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (ext : String → Option (State → State))
    {roBase : BitVec 64} {s0 : State}
    (hhrLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 482)
      (withStepInv s0 (leafEncLen16Spec (headerReceivedPBPinnedAt A.repAlloc) headerReceivedPBEncodedLen)))
    (hpolyDecLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 493)
      (withStepInv s0 (leafEncLen16Spec (polynomialDecoderPBPinnedAt A.repAlloc) polynomialDecoderPBEncodedLen)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hauthEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 454)
      (withStepInv s0 (authEncodeExactSpecOf resStack A lim)))
    (hmemcpy : subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy") etvMemcpyRegionSpec)
    (hpolyDec : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 455)
      (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A.repAlloc)))
    (v : V1State.Chunked.HeaderReceived) :
    StepSendInnerStateAt6616Placed resStack A lim st0 ext roBase s0 (.headerReceived v) :=
  step_send_v1_headerReceived_at_6616_placed hres A lim st0 ext
    hhrLen hpolyDecLen hvarint hauthEnc hmemcpy
    (etvPolyDecoderBudgetExact_of_vm hpolyDec) v

end LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerChunked3aPlacedBudget

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerChunked2PlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonBudget
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public meta import Lean -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked1
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked2
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.V1StateHelpers
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesVnEncode
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Phase 3e (Part 2): `V1State` Variants `idx = 0, 2, 5`

Threads `RustCliAllocBudget` and `VmPreserved` through `V1State::encode_raw` arm
`noHeaderReceived` (`idx = 5`), re-exporting `keysUnsampled` and `headerSent` from `Aux`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerChunked2PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open CryptoVerification (LibsignalPlacement libsignalSessionCode lsmpl lsρ)
open CryptoVerification.RustHeap (vecU8At)
open CryptoVerification.LibsignalSpqrV1
  (PolynomialDecoder ProtoAuthenticator V1State)
open CryptoVerification.LibsignalSpqrV1.Proto
  (encodeMessage encodeOptMessage encodeUint64Field encodeVarint)
open CryptoVerification.SpqrV1.ProtoRepr
  (PolynomialDecoderPBGhost Unchunked2PBGhost
   chunkedHeaderSentPBPinnedAt ekSentPBEncodedLen ekSentPBPinnedAt
   keysUnsampledPBEncodedLen keysUnsampledPBPinnedAt
   noHeaderReceivedPBEncodedLen noHeaderReceivedPBPinnedAt
   noneCap_add_two_beq_zero noneCap_add_two_bne_zero
   optAuthCap optAuthenticatorPBPinnedAt
   optNoHeaderReceivedPBFieldEncodedLen optNoHeaderReceivedPBPinnedAt
   optPolynomialDecoderPBFieldEncodedLen optPolynomialDecoderPBPinnedAt
   polynomialDecoderPBEncodedLen polynomialDecoderPBPinnedAt
   unchunked2PinnedAt
   v1StateInnerPBPinnedAt v1StateInnerPayloadEncodedLen v1StatePBEncodedLen varintLen)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (adds_no_overflow_of_eq cmp_ls_false_of_lt
   hwVarintLen_bvShift_eq_ofNat_varintLen_norm hwVarintLen_eq_ofNat_varintLen_norm
   noneCap_add_one_beq_zero noneCap_add_one_bne_zero
   ofNat_countLeadingZeros_32 ofNat_countLeadingZeros_64
   ule_self_64 ule_zero_64 ult_self_64 ult_zero_64
   zeroExtend64_beq_zero32 zext64_truncate32)
open CryptoVerification.SpqrV1.Prost.EncodeToVec
  (StepInv bv_optPolyDec_some_eq cap_beq_len_false_of_lt
   encodeToVecCalleeStackOf encodeVarint_length_pos
   etv2_bv_optNoHeaderReceived_some_eq
   etv2_encodeInnerState_noHeaderReceived_eq etv2_encodeOptNoHeaderReceived_some_eq
   etv2_encodeUint64Field_1_eq etv2_optAuth_cap_bounds
   noneCap2_add_two_beq_zero noneCap2_add_two_bne_zero
   noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
   optNoHeaderReceivedCap optNoHeaderReceivedPBPinnedAt_cap_bounds
   optNoHeaderReceivedPBPinnedAt_eq
   optPolyDecCap optPolynomialDecoderPBPinnedAt_cap_bounds optPolynomialDecoderPBPinnedAt_eq
   ult_of_lt_of_fit v1StateInnerCap
   vecU8At_expose_one vecU8At_pack_one withStepInv)
open CryptoVerification.SpqrV1.Top.Send
  (spqrSendEncodeJumpTableBytes spqrSendEncodeJumpTableBytesAt spqrSendEncodeJumpTableBytes_eq)
open CryptoVerification.Cli.SpqrV1.Top.Send.CodePlaced (blkPl_427_ρ)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
  (spqrSendPlacedEntry spqrSendPlacedProg)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerHeaderPlacedBudget
  (StepSendInnerStateAt6616Placed step_send_encode_auth_call_placed
   step_send_encode_varint_call_placed step_send_leaf_encLen16_call_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerChunked1PlacedBudgetAux
  (etvPolyDecoderBudgetExact_of_vm etvPolyEncoderBudgetExact_of_vm
   sepWPp_extract_pure sepWPp_extract_vecU8At_bounds step_send_tail_11208_polyDec2_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhaseBudget
  (authEncodeExactSpecOf encodeVarintExactSpecOf etvMemcpyRegionSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsPlacedBudget
  (sepWP_done_tpidr sepWP_done_vm sepWPp_of_sepWP_cs_vm)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonBudget
  (etvPolyDecoderExactSpecOf etvPolyEncoderExactSpecOf leafEncLen16Spec)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonPlacedBudget
  (etvPolyDecoderBudgetExactSpecOf etvPolyEncoderBudgetExactSpecOf)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsChunkedV1Budget
  (chunkedHeaderSentEncodedLenPinnedSpec)

variable [LibsignalPlacement]

/-! ## 1. Re-Exports from `AfterStatesInnerChunked2PlacedBudgetAux` -/

export LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerChunked2PlacedBudgetAux
  (send2_step_memcpy_slice_placed step_send_v1_keysUnsampled_placed
   step_send_v1_headerSent_placed)

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

/-! ## 2. Variant `idx = 5`: `.noHeaderReceived` (`+8724 .. +11220`) -/

/-- Step `+8724 .. +6216` for `is = .noHeaderReceived v`, threading `A.pool lim st`. -/
theorem step_send_v1_noHeaderReceived_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State)) {s0 s : State}
    (hnhrLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 500)
      (withStepInv s0 (leafEncLen16Spec (noHeaderReceivedPBPinnedAt A.repAlloc) noHeaderReceivedPBEncodedLen)))
    (hpolyDecLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 493)
      (withStepInv s0 (leafEncLen16Spec (polynomialDecoderPBPinnedAt A.repAlloc) polynomialDecoderPBEncodedLen)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hauthEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 454)
      (withStepInv s0 (authEncodeExactSpecOf resStack A lim)))
    (hpolyDec : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 455)
      (withStepInv s0 (etvPolyDecoderBudgetExactSpecOf resStack A lim)))
    (sp cap ptr w25 : BitVec 64) (g : PolynomialDecoderPBGhost × Unchunked2PBGhost)
    (v : V1State.Chunked.NoHeaderReceived) (bs : List (BitVec 8))
    (hv_len : v1StatePBEncodedLen ⟨some (.noHeaderReceived v)⟩ < 2 ^ 64)
    (hfit : bs.length + (V1State.InnerState.encode (.noHeaderReceived v)).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = spqrSendPlacedEntry + 8724#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace) (hinv0 : StepInv s0 s)
    (hP : P = ((optPolynomialDecoderPBPinnedAt A.repAlloc g.1 (sp + 4840#64) v.receivingHdr ∗
      optNoHeaderReceivedPBPinnedAt A.repAlloc g.2 (sp + 4880#64) v.uc) ∗
      vecU8At A.repAlloc (sp + 1424#64) cap ptr bs ∗ A.pool lim st s ∗
      ((sp + 16#64) ↦₆₄ w25) ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = spqrSendPlacedEntry + 6216#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = w25 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        (((optPolynomialDecoderPBPinnedAt A.repAlloc g.1 (sp + 4840#64) v.receivingHdr ∗
          optNoHeaderReceivedPBPinnedAt A.repAlloc g.2 (sp + 4880#64) v.uc) ∗
          vecU8At A.repAlloc (sp + 1424#64) cap ptr
            (bs ++ V1State.InnerState.encode (.noHeaderReceived v)) ∗
          A.pool lim st sm ∗ ((sp + 16#64) ↦₆₄ w25) ∗
          stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  subst hP; rcases v with ⟨uc, receivingHdr⟩
  rw [etv2_encodeInnerState_noHeaderReceived_eq] at hfit
  simp only [List.length_append, List.length_singleton] at hfit
  have hsub_len : v1StateInnerPayloadEncodedLen (.noHeaderReceived ⟨uc, receivingHdr⟩) < 2 ^ 64 := by
    dsimp only [v1StatePBEncodedLen] at hv_len; omega
  have hlt1 : bs.length < cap.toNat := by omega
  have hfit_var : (bs ++ [0x32#8]).length +
      (encodeVarint
        (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.noHeaderReceived ⟨uc, receivingHdr⟩)))).length ≤
        cap.toNat := by
    simp only [List.length_append, List.length_singleton]; omega
  refine sepWPp_extract_vecU8At_bounds (v := sp + 1424#64) (cap := cap) (ptr := ptr) (bs := bs)
    (F := optPolynomialDecoderPBPinnedAt A.repAlloc g.1 (sp + 4840#64) receivingHdr ∗
      optNoHeaderReceivedPBPinnedAt A.repAlloc g.2 (sp + 4880#64) uc ∗ A.pool lim st s ∗
      ((sp + 16#64) ↦₆₄ w25) ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F)
    (by sep_ac_rfl) fun _ hcap hptr => ?_
  refine sepWPp_extract_pure
    (((optNoHeaderReceivedCap g.2 uc + 2#64 == 0#64) = !uc.isSome ∧
      (optNoHeaderReceivedCap g.2 uc + 2#64 != 0#64) = uc.isSome) ∧
     ((optPolyDecCap g.1 receivingHdr + 1#64 == 0#64) = !receivingHdr.isSome ∧
      (optPolyDecCap g.1 receivingHdr + 1#64 != 0#64) = receivingHdr.isSome))
    (fun R' hm =>
      ⟨optNoHeaderReceivedPBPinnedAt_cap_bounds (p := sp + 4880#64)
        (R := optPolynomialDecoderPBPinnedAt A.repAlloc g.1 (sp + 4840#64) receivingHdr ∗
          vecU8At A.repAlloc (sp + 1424#64) cap ptr bs ∗ A.pool lim st s ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm),
       optPolynomialDecoderPBPinnedAt_cap_bounds (p := sp + 4840#64)
        (R := optNoHeaderReceivedPBPinnedAt A.repAlloc g.2 (sp + 4880#64) uc ∗
          vecU8At A.repAlloc (sp + 1424#64) cap ptr bs ∗ A.pool lim st s ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm)⟩)
    fun ⟨⟨hcap_uc_beq, hcap_uc_bne⟩, ⟨hcap_dec_beq, hcap_dec_bne⟩⟩ => ?_
  have hbeq_false := cap_beq_len_false_of_lt hlt1 hcap
  have ⟨h1432, h1440⟩ : (sp + 1424#64) + 8#64 = sp + 1432#64 ∧
      (sp + 1424#64) + 16#64 = sp + 1440#64 := ⟨by bv_omega, by bv_omega⟩
  have ⟨h4704, h4840, h4880⟩ :
      (sp + 4096#64) + 608#64 = sp + 4704#64 ∧
      (sp + 4704#64) + 136#64 = sp + 4840#64 ∧
      (sp + 4704#64) + 176#64 = sp + 4880#64 := ⟨by bv_omega, by bv_omega, by bv_omega⟩
  have hpack := vecU8At_pack_one A.repAlloc (sp + 1424#64) cap ptr bs 0x32#8 hlt1 hcap hptr
  rw [h1432, h1440] at hpack
  suffices h9312 : ∀ sm1 : State,
      sm1.pc = spqrSendPlacedEntry + 9312#64 → sm1.status = .Running →
      sm1.sp = sp → sm1.trace = s0.trace →
      sm1.readReg64 .x19 = s.readReg64 .x19 → sm1.readReg64 .x20 = sp + 4704#64 →
      sm1.readReg64 .x21 = s.readReg64 .x21 → sm1.readReg64 .x22 = optNoHeaderReceivedCap g.2 uc →
      sm1.readReg64 .x23 = s.readReg64 .x23 →
      sm1.readReg64 .x25 = BitVec.ofNat 64 (optNoHeaderReceivedPBFieldEncodedLen uc) →
      sm1.readReg64 .x27 = s.readReg64 .x27 → sm1.readReg64 .x28 = s.readReg64 .x28 →
      sm1.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm1 →
      SepWPp (spqrSendPlacedProg ext) ret sm1
        (((optPolynomialDecoderPBPinnedAt A.repAlloc g.1 (sp + 4840#64) receivingHdr ∗
          optNoHeaderReceivedPBPinnedAt A.repAlloc g.2 (sp + 4880#64) uc) ∗
          vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs ++ [0x32#8]) ∗ A.pool lim st sm1 ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom by
    rw [vecU8At_expose_one A.repAlloc (sp + 1424#64) cap ptr bs hlt1 hcap hptr, h1432, h1440]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun b0 => ?_
    cases uc with
    | none =>
      rw [optNoHeaderReceivedPBPinnedAt_eq A.repAlloc g.2 (sp + 4880#64) none]
      simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
      apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 9312#64)
      by_vm_steps_safe
        wp_steps
        apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv1
        have hpool1 : A.pool lim st s = A.pool lim st _ := (A.pool_of_vmPreserved hinv1.2).symm
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (h9312 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by rw [← h4704]; simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [optNoHeaderReceivedPBFieldEncodedLen, arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (hinv0.trans hinv1.1))
        rw [← optNoHeaderReceivedPBPinnedAt_eq A.repAlloc g.2 (sp + 4880#64) none, ← hpack, hpool1]
        (try sep_ac_rfl)
    | some u =>
      rw [optNoHeaderReceivedPBPinnedAt_eq A.repAlloc g.2 (sp + 4880#64) (some u)]
      simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      have ⟨hu_fit, hopt_u_lt⟩ :
          noHeaderReceivedPBEncodedLen u < 2 ^ 64 ∧
          optNoHeaderReceivedPBFieldEncodedLen (some u) < 2 ^ 64 :=
        ⟨by dsimp only [v1StateInnerPayloadEncodedLen, optNoHeaderReceivedPBFieldEncodedLen] at hsub_len; omega,
         by dsimp only [v1StateInnerPayloadEncodedLen] at hsub_len; omega⟩
      have hvar_u_lt :
          varintLen (BitVec.ofNat 64 (noHeaderReceivedPBEncodedLen u)) <
            optNoHeaderReceivedPBFieldEncodedLen (some u) := by
        dsimp only [optNoHeaderReceivedPBFieldEncodedLen]; omega
      have ⟨⟨hu1, hu2, hu3, hu4, hu5⟩, hult_u, hopt_u_eq⟩ :=
        (⟨cmp_ls_false_of_lt hvar_u_lt hopt_u_lt, ult_of_lt_of_fit hvar_u_lt hopt_u_lt,
          etv2_bv_optNoHeaderReceived_some_eq u⟩ : _ ∧ _ ∧ _)
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
      apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 500)
      by_vm_steps_safe
        wp_steps
        apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv1
        rw [← optNoHeaderReceivedPBPinnedAt_eq A.repAlloc g.2 (sp + 4880#64) (some u)]
        refine step_send_leaf_encLen16_call_placed hres ext
          (noHeaderReceivedPBPinnedAt A.repAlloc) noHeaderReceivedPBEncodedLen hnhrLen
          (sp + 4880#64) sp (spqrSendPlacedEntry + 9272#64) g.2 u hu_fit
          (F := optPolynomialDecoderPBPinnedAt A.repAlloc g.1 (sp + 4840#64) receivingHdr ∗
            vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs ++ [0x32#8]) ∗
            A.pool lim st s ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) halign
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
          (by rw [← h4880, ← h4704]; simp only [arm64_norm, *]) (hinv0.trans hinv1.1)
          (by rw [← hpack]; dsimp only [optNoHeaderReceivedPBPinnedAt]; sep_ac_rfl) ?_
        intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1 hcsm1 hinv_m1 hvm_m1
        rcases hcsm1 with ⟨hm19, hm20, hm21, hm22, hm23, _, _, _, hm27, hm28, hmfp, _⟩
        simp only [arm64_norm, h4704] at hm19 hm20 hm21 hm22 hm23 hm27 hm28 hmfp
        (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
        apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 9312#64)
        wp_steps
        apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv2
        have hpool2 : A.pool lim st s = A.pool lim st _ :=
          (A.pool_of_vmPreserved (hinv1.2.trans (hvm_m1.trans hinv2.2))).symm
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (h9312 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (hinv_m1.trans hinv2.1))
        dsimp only [optNoHeaderReceivedPBPinnedAt]; rw [hpool2]; sep_ac_rfl
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx25_1 hx27_1 hx28_1 hfp_1 hinv_1
  suffices h9956 : ∀ sm2 : State,
      sm2.pc = spqrSendPlacedEntry + 9956#64 → sm2.status = .Running →
      sm2.sp = sp → sm2.trace = s0.trace →
      sm2.readReg64 .x8 = BitVec.ofNat 64 (optPolynomialDecoderPBFieldEncodedLen receivingHdr) →
      sm2.readReg64 .x19 = s.readReg64 .x19 → sm2.readReg64 .x20 = sp + 4704#64 →
      sm2.readReg64 .x21 = s.readReg64 .x21 → sm2.readReg64 .x22 = optNoHeaderReceivedCap g.2 uc →
      sm2.readReg64 .x23 = s.readReg64 .x23 → sm2.readReg64 .x24 = optPolyDecCap g.1 receivingHdr →
      sm2.readReg64 .x25 = BitVec.ofNat 64 (optNoHeaderReceivedPBFieldEncodedLen uc) →
      sm2.readReg64 .x27 = s.readReg64 .x27 → sm2.readReg64 .x28 = s.readReg64 .x28 →
      sm2.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm2 →
      SepWPp (spqrSendPlacedProg ext) ret sm2
        (((optPolynomialDecoderPBPinnedAt A.repAlloc g.1 (sp + 4840#64) receivingHdr ∗
          optNoHeaderReceivedPBPinnedAt A.repAlloc g.2 (sp + 4880#64) uc) ∗
          vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs ++ [0x32#8]) ∗ A.pool lim st sm2 ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom by
    cases receivingHdr with
    | none =>
      rw [optPolynomialDecoderPBPinnedAt_eq A.repAlloc g.1 (sp + 4840#64) none]
      simp only [Option.isSome_none, Bool.not_false] at hcap_dec_beq hcap_dec_bne
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
      apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 9956#64)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv2
      have hpool2 : A.pool lim st sm1 = A.pool lim st _ := (A.pool_of_vmPreserved hinv2.2).symm
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h9956 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [optPolynomialDecoderPBFieldEncodedLen, arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_1.trans hinv2.1))
      rw [← optPolynomialDecoderPBPinnedAt_eq A.repAlloc g.1 (sp + 4840#64) none, hpool2]
      (try sep_ac_rfl)
    | some dec =>
      rw [optPolynomialDecoderPBPinnedAt_eq A.repAlloc g.1 (sp + 4840#64) (some dec)]
      simp only [Option.isSome_some, Bool.not_true] at hcap_dec_beq hcap_dec_bne
      have ⟨hdec_fit, hopt_d_lt⟩ :
          polynomialDecoderPBEncodedLen dec < 2 ^ 64 ∧
          optPolynomialDecoderPBFieldEncodedLen (some dec) < 2 ^ 64 :=
        ⟨by dsimp only [v1StateInnerPayloadEncodedLen, optPolynomialDecoderPBFieldEncodedLen] at hsub_len; omega,
         by dsimp only [v1StateInnerPayloadEncodedLen] at hsub_len; omega⟩
      have hvar_d_lt :
          varintLen (BitVec.ofNat 64 (polynomialDecoderPBEncodedLen dec)) <
            optPolynomialDecoderPBFieldEncodedLen (some dec) := by
        dsimp only [optPolynomialDecoderPBFieldEncodedLen]; omega
      have ⟨⟨hd1, hd2, hd3, hd4, hd5⟩, hult_d, hopt_d_eq⟩ :=
        (⟨cmp_ls_false_of_lt hvar_d_lt hopt_d_lt, ult_of_lt_of_fit hvar_d_lt hopt_d_lt,
          bv_optPolyDec_some_eq dec⟩ : _ ∧ _ ∧ _)
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
      apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 493)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv2
      rw [← optPolynomialDecoderPBPinnedAt_eq A.repAlloc g.1 (sp + 4840#64) (some dec)]
      refine step_send_leaf_encLen16_call_placed hres ext
        (polynomialDecoderPBPinnedAt A.repAlloc) polynomialDecoderPBEncodedLen hpolyDecLen
        (sp + 4840#64) sp (spqrSendPlacedEntry + 9332#64) g.1 dec hdec_fit
        (F := optNoHeaderReceivedPBPinnedAt A.repAlloc g.2 (sp + 4880#64) uc ∗
          vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs ++ [0x32#8]) ∗
          A.pool lim st sm1 ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
        (by rw [← h4840]; simp only [arm64_norm, *]) (hinv_1.trans hinv2.1)
        (by dsimp only [optPolynomialDecoderPBPinnedAt]; sep_ac_rfl) ?_
      intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx0m2 hcsm2 hinv_m2 hvm_m2
      rcases hcsm2 with ⟨hm2_19, hm2_20, hm2_21, hm2_22, hm2_23, hm2_24, hm2_25, _, hm2_27, hm2_28, hm2_fp, _⟩
      simp only [arm64_norm, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx25_1, hx27_1, hx28_1, hfp_1]
        at hm2_19 hm2_20 hm2_21 hm2_22 hm2_23 hm2_24 hm2_25 hm2_27 hm2_28 hm2_fp
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
      apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 9956#64)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv3
      have hpool3 : A.pool lim st sm1 = A.pool lim st _ :=
        (A.pool_of_vmPreserved (hinv2.2.trans (hvm_m2.trans hinv3.2))).symm
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h9956 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (hinv_m2.trans hinv3.1))
      dsimp only [optPolynomialDecoderPBPinnedAt]; rw [hpool3]; sep_ac_rfl
  intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx8_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx27_2 hx28_2 hfp_2 hinv_2
  have ⟨hadd_sum, hult_sum, hule_sum, hult_sum2, hule_sum2⟩ := adds_no_overflow_of_eq
      (a := optPolynomialDecoderPBFieldEncodedLen receivingHdr)
      (b := optNoHeaderReceivedPBFieldEncodedLen uc)
      (c := v1StateInnerPayloadEncodedLen (.noHeaderReceived ⟨uc, receivingHdr⟩)) rfl hsub_len
  (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
  apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 451)
  wp_steps
  apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, wp_norm, *])
  intro hinv3
  have hpool3 : A.pool lim st sm2 = A.pool lim st _ := (A.pool_of_vmPreserved hinv3.2).symm
  set bs1 := (bs ++ [0x32#8]) ++
    encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.noHeaderReceived ⟨uc, receivingHdr⟩)))
  refine step_send_encode_varint_call_placed A lim st hvarint
    (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.noHeaderReceived ⟨uc, receivingHdr⟩)))
    (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 9972#64) (bs ++ [0x32#8]) hfit_var
    (F := (optPolynomialDecoderPBPinnedAt A.repAlloc g.1 (sp + 4840#64) receivingHdr ∗
      optNoHeaderReceivedPBPinnedAt A.repAlloc g.2 (sp + 4880#64) uc) ∗
      ((sp + 16#64) ↦₆₄ w25) ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hinv_2.trans hinv3.1) (by rw [hpool3]; sep_ac_rfl) ?_
  intro sm3 hpcm3 hrunm3 hspm3 htrm3 hcsm3 hinv_m3
  rcases hcsm3 with ⟨hm3_19, hm3_20, hm3_21, hm3_22, hm3_23, hm3_24, _, _, hm3_27, hm3_28, hm3_fp, _⟩
  simp only [arm64_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx27_2, hx28_2, hfp_2]
    at hm3_19 hm3_20 hm3_21 hm3_22 hm3_23 hm3_24 hm3_27 hm3_28 hm3_fp
  set bs2 := bs1 ++ encodeOptMessage V1State.Unchunked.NoHeaderReceived.encodeRaw 1#32 uc
  suffices h10108 : ∀ sm4 : State,
      sm4.pc = spqrSendPlacedEntry + 10108#64 → sm4.status = .Running →
      sm4.sp = sp → sm4.trace = s0.trace →
      sm4.readReg64 .x19 = s.readReg64 .x19 → sm4.readReg64 .x20 = sp + 4704#64 →
      sm4.readReg64 .x21 = s.readReg64 .x21 → sm4.readReg64 .x23 = s.readReg64 .x23 →
      sm4.readReg64 .x24 = optPolyDecCap g.1 receivingHdr → sm4.readReg64 .x25 = w25 →
      sm4.readReg64 .x27 = s.readReg64 .x27 → sm4.readReg64 .x28 = s.readReg64 .x28 →
      sm4.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm4 →
      SepWPp (spqrSendPlacedProg ext) ret sm4
        (((optPolynomialDecoderPBPinnedAt A.repAlloc g.1 (sp + 4840#64) receivingHdr ∗
          optNoHeaderReceivedPBPinnedAt A.repAlloc g.2 (sp + 4880#64) uc) ∗
          vecU8At A.repAlloc (sp + 1424#64) cap ptr bs2 ∗ A.pool lim st sm4 ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom by
    cases uc with
    | none =>
      simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
      apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 10108#64)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv4
      have hpool4 : A.pool lim st sm3 = A.pool lim st _ := (A.pool_of_vmPreserved hinv4.2).symm
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h10108 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (hinv_m3.trans hinv4.1))
      rw [hpool4]; simp +zetaDelta only [bs2, encodeOptMessage, List.append_nil]; (try sep_ac_rfl)
    | some u =>
      simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      rw [etv2_encodeOptNoHeaderReceived_some_eq] at hfit
      simp only [List.length_append, List.length_singleton] at hfit
      have hu_lt : noHeaderReceivedPBEncodedLen u < 2 ^ 64 := by
        dsimp only [v1StateInnerPayloadEncodedLen, optNoHeaderReceivedPBFieldEncodedLen] at hsub_len; omega
      have hlt_tag : bs1.length < cap.toNat := by
        dsimp only [bs1]; simp only [List.length_append, List.length_singleton]; omega
      have hbeq_tag := cap_beq_len_false_of_lt hlt_tag hcap
      rw [vecU8At_expose_one A.repAlloc (sp + 1424#64) cap ptr bs1 hlt_tag hcap hptr, h1432, h1440]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPp.exists_elim fun b1 => ?_
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
      apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 500)
      by_vm_steps_safe
        wp_steps
        apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv4
        have hpack_tag := vecU8At_pack_one A.repAlloc (sp + 1424#64) cap ptr bs1 0x0a#8 hlt_tag hcap hptr
        rw [h1432, h1440] at hpack_tag
        refine step_send_leaf_encLen16_call_placed hres ext
          (noHeaderReceivedPBPinnedAt A.repAlloc) noHeaderReceivedPBEncodedLen hnhrLen
          (sp + 4880#64) sp (spqrSendPlacedEntry + 10028#64) g.2 u hu_lt
          (F := optPolynomialDecoderPBPinnedAt A.repAlloc g.1 (sp + 4840#64) receivingHdr ∗
            vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs1 ++ [0x0a#8]) ∗
            A.pool lim st sm3 ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) halign
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
          (by rw [← h4880]; simp only [arm64_norm, *]) (hinv_m3.trans hinv4.1)
          (by rw [← hpack_tag]; dsimp only [optNoHeaderReceivedPBPinnedAt]; (try sep_ac_rfl)) ?_
        intro sm4 hpcm4 hrunm4 hspm4 htrm4 hx0m4 hcsm4 hinv_m4 hvm_m4
        rcases hcsm4 with ⟨hm4_19, hm4_20, hm4_21, hm4_22, hm4_23, hm4_24, hm4_25, _, hm4_27, hm4_28, hm4_fp, _⟩
        simp only [arm64_norm, hm3_19, hm3_20, hm3_21, hm3_22, hm3_23, hm3_24, hm3_27, hm3_28, hm3_fp]
          at hm4_19 hm4_20 hm4_21 hm4_22 hm4_23 hm4_24 hm4_25 hm4_27 hm4_28 hm4_fp
        (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
        apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 451)
        wp_steps
        apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv5
        have hpool5 : A.pool lim st sm3 = A.pool lim st _ :=
          (A.pool_of_vmPreserved (hinv4.2.trans (hvm_m4.trans hinv5.2))).symm
        set bs_u1 := (bs1 ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 (noHeaderReceivedPBEncodedLen u))
        have hfit_uvar : (bs1 ++ [0x0a#8]).length +
            (encodeVarint (BitVec.ofNat 64 (noHeaderReceivedPBEncodedLen u))).length ≤ cap.toNat := by
          dsimp only [bs1]; simp only [List.length_append, List.length_singleton]; omega
        refine step_send_encode_varint_call_placed A lim st hvarint
          (BitVec.ofNat 64 (noHeaderReceivedPBEncodedLen u))
          (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 10036#64) (bs1 ++ [0x0a#8]) hfit_uvar
          (F := optPolynomialDecoderPBPinnedAt A.repAlloc g.1 (sp + 4840#64) receivingHdr ∗
            noHeaderReceivedPBPinnedAt A.repAlloc g.2 (sp + 4880#64) u ∗
            ((sp + 16#64) ↦₆₄ w25) ∗ F)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) halign
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hinv_m4.trans hinv5.1) (by rw [hpool5]; (try sep_ac_rfl)) ?_
        intro sm5 hpcm5 hrunm5 hspm5 htrm5 hcsm5 hinv_m5
        rcases hcsm5 with ⟨hm5_19, hm5_20, hm5_21, hm5_22, hm5_23, hm5_24, hm5_25, _, hm5_27, hm5_28, hm5_fp, _⟩
        simp only [arm64_norm, hm4_19, hm4_20, hm4_21, hm4_22, hm4_23, hm4_24, hm4_25, hm4_27, hm4_28, hm4_fp]
          at hm5_19 hm5_20 hm5_21 hm5_22 hm5_23 hm5_24 hm5_25 hm5_27 hm5_28 hm5_fp
        dsimp only [noHeaderReceivedPBPinnedAt, unchunked2PinnedAt]
        have h4880_48 : (sp + 4880#64) + 0x30#64 = sp + 4928#64 := by clear *- ; bv_omega
        rw [h4880_48]
        refine sepWPp_extract_pure
          ((optAuthCap g.2 u.auth + 1#64 == 0#64) = !u.auth.isSome ∧
            (optAuthCap g.2 u.auth + 1#64 != 0#64) = u.auth.isSome)
          (fun R' hm => etv2_optAuth_cap_bounds (A := A.repAlloc) (p := sp + 4880#64)
            (R := optPolynomialDecoderPBPinnedAt A.repAlloc g.1 (sp + 4840#64) receivingHdr ∗
              ((sp + 4928#64) ↦₆₄ u.epoch) ∗
              vecU8At A.repAlloc (sp + 1424#64) cap ptr bs_u1 ∗ A.pool lim st sm5 ∗
              ((sp + 16#64) ↦₆₄ w25) ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
            (Satisfies.mono (Entails.of_eq (by dsimp only [bs_u1]; sep_ac_rfl)) hm))
          fun ⟨hcap_auth_beq, hcap_auth_bne⟩ => ?_
        set bs_u2 := bs_u1 ++ encodeUint64Field 1#32 u.epoch
        suffices h10088 : ∀ sm6 : State,
            sm6.pc = spqrSendPlacedEntry + 10088#64 → sm6.status = .Running →
            sm6.sp = sp → sm6.trace = s0.trace →
            sm6.readReg64 .x19 = s.readReg64 .x19 → sm6.readReg64 .x20 = sp + 4704#64 →
            sm6.readReg64 .x21 = s.readReg64 .x21 →
            sm6.readReg64 .x22 = optNoHeaderReceivedCap g.2 (some u) →
            sm6.readReg64 .x23 = s.readReg64 .x23 →
            sm6.readReg64 .x24 = optPolyDecCap g.1 receivingHdr →
            sm6.readReg64 .x25 = w25 → sm6.readReg64 .x27 = s.readReg64 .x27 →
            sm6.readReg64 .x28 = s.readReg64 .x28 → sm6.readReg64 .fp = s.readReg64 .fp →
            StepInv s0 sm6 →
            SepWPp (spqrSendPlacedProg ext) ret sm6
              (((optPolynomialDecoderPBPinnedAt A.repAlloc g.1 (sp + 4840#64) receivingHdr ∗
                optAuthenticatorPBPinnedAt A.repAlloc g.2 (sp + 4880#64) u.auth ∗
                ((sp + 4928#64) ↦₆₄ u.epoch)) ∗
                vecU8At A.repAlloc (sp + 1424#64) cap ptr bs_u2 ∗ A.pool lim st sm6 ∗
                ((sp + 16#64) ↦₆₄ w25) ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
              Q Qp oom by
          cases hep : u.epoch == 0#64
          · have hfit_ep : bs_u1.length + 1 + (encodeVarint u.epoch).length ≤ cap.toNat := by
              rw [etv2_encodeUint64Field_1_eq, hep] at hfit; dsimp only [bs_u1, bs1]
              simp only [Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_singleton]
                at hfit ⊢; omega
            have hlt_ep : bs_u1.length < cap.toNat := by have := encodeVarint_length_pos u.epoch; omega
            have hbeq_ep := cap_beq_len_false_of_lt hlt_ep hcap
            rw [vecU8At_expose_one A.repAlloc (sp + 1424#64) cap ptr bs_u1 hlt_ep hcap hptr, h1432, h1440]
            simp only [sepExists_sepConj_left, sepExists_sepConj_right]
            refine SepWPp.exists_elim fun b2 => ?_
            (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
            apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 451)
            by_vm_steps_safe
              wp_steps
              apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, wp_norm, *])
              intro hinv6
              have hpool6 : A.pool lim st sm5 = A.pool lim st _ :=
                (A.pool_of_vmPreserved hinv6.2).symm
              have hpack_ep :=
                vecU8At_pack_one A.repAlloc (sp + 1424#64) cap ptr bs_u1 0x08#8 hlt_ep hcap hptr
              rw [h1432, h1440] at hpack_ep
              refine step_send_encode_varint_call_placed A lim st hvarint
                u.epoch (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 10088#64) (bs_u1 ++ [0x08#8])
                (by simpa only [List.length_append, List.length_singleton] using hfit_ep)
                (F := (optPolynomialDecoderPBPinnedAt A.repAlloc g.1 (sp + 4840#64) receivingHdr ∗
                  optAuthenticatorPBPinnedAt A.repAlloc g.2 (sp + 4880#64) u.auth ∗
                  ((sp + 4928#64) ↦₆₄ u.epoch)) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
                (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) halign
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (hinv_m5.trans hinv6.1)
                (by rw [← hpack_ep, hpool6]; (try sep_ac_rfl)) ?_
              intro sm6 hpcm6 hrunm6 hspm6 htrm6 hcsm6 hinv_m6
              rcases hcsm6 with
                ⟨hm6_19, hm6_20, hm6_21, hm6_22, hm6_23, hm6_24, hm6_25, _, hm6_27, hm6_28, hm6_fp, _⟩
              simp only [arm64_norm, hm5_19, hm5_20, hm5_21, hm5_22, hm5_23, hm5_24, hm5_25, hm5_27, hm5_28, hm5_fp]
                at hm6_19 hm6_20 hm6_21 hm6_22 hm6_23 hm6_24 hm6_25 hm6_27 hm6_28 hm6_fp
              refine SepWPp.weaken_pre (Entails.of_eq ?_)
                (h10088 sm6 hpcm6 hrunm6 hspm6 htrm6 hm6_19 hm6_20 hm6_21 hm6_22 hm6_23 hm6_24
                  hm6_25 hm6_27 hm6_28 hm6_fp hinv_m6)
              simp +zetaDelta only [bs_u2, etv2_encodeUint64Field_1_eq, hep,
                Bool.false_eq_true, ↓reduceIte, List.append_assoc]; (try sep_ac_rfl)
          · (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
            apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 10088#64)
            wp_steps
            apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, wp_norm, *])
            intro hinv6
            have hpool6 : A.pool lim st sm5 = A.pool lim st _ :=
              (A.pool_of_vmPreserved hinv6.2).symm
            refine SepWPp.weaken_pre (Entails.of_eq ?_)
              (h10088 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (hinv_m5.trans hinv6.1))
            rw [hpool6]
            simp +zetaDelta only [bs_u2, etv2_encodeUint64Field_1_eq, hep,
              ↓reduceIte, List.append_nil]; (try sep_ac_rfl)
        intro sm6 hpcm6 hrunm6 hspm6 htrm6 hx19_6 hx20_6 hx21_6 hx22_6 hx23_6 hx24_6 hx25_6 hx27_6 hx28_6 hfp_6 hinv_6
        have hx22_eq : optNoHeaderReceivedCap g.2 (some u) = optAuthCap g.2 u.auth := rfl
        rw [hx22_eq] at hx22_6
        cases hauth : u.auth with
        | none =>
          simp only [hauth, Option.isSome_none, Bool.not_false] at hcap_auth_beq hcap_auth_bne
          (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
          apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 10108#64)
          wp_steps
          apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, wp_norm, *])
          intro hinv7
          have hpool7 : A.pool lim st sm6 = A.pool lim st _ :=
            (A.pool_of_vmPreserved hinv7.2).symm
          refine SepWPp.weaken_pre (Entails.of_eq ?_)
            (h10108 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (hinv_6.trans hinv7.1))
          dsimp only [bs2]; rw [hpool7, etv2_encodeOptNoHeaderReceived_some_eq]
          simp +zetaDelta only [bs_u2, bs_u1, bs1, hauth, encodeOptMessage,
            optNoHeaderReceivedPBPinnedAt, noHeaderReceivedPBPinnedAt, unchunked2PinnedAt, h4880_48,
            List.append_nil, List.append_assoc]; (try sep_ac_rfl)
        | some auth =>
          simp only [hauth, Option.isSome_some, Bool.not_true] at hcap_auth_beq hcap_auth_bne
          have hfit_auth :
              bs_u2.length + (encodeMessage ProtoAuthenticator.encodeRaw 2#32 auth).length ≤ cap.toNat := by
            rw [hauth] at hfit; dsimp only [bs_u2, bs_u1, bs1, encodeOptMessage] at hfit ⊢
            simp only [List.length_append, List.length_singleton] at hfit ⊢; omega
          (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
          apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 454)
          wp_steps
          apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, wp_norm, *])
          intro hinv7
          have hpool7 : A.pool lim st sm6 = A.pool lim st _ :=
            (A.pool_of_vmPreserved hinv7.2).symm
          refine step_send_encode_auth_call_placed A lim st ext hauthEnc
            (sp + 4880#64) (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 10108#64) g.2 auth bs_u2 hfit_auth
            (F := (optPolynomialDecoderPBPinnedAt A.repAlloc g.1 (sp + 4840#64) receivingHdr ∗
              ((sp + 4928#64) ↦₆₄ u.epoch)) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) halign
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
            (by rw [← h4880]; simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hinv_6.trans hinv7.1)
            (by rw [hpool7]; simp only [hauth, optAuthenticatorPBPinnedAt]; (try sep_ac_rfl)) ?_
          intro sm7 hpcm7 hrunm7 hspm7 htrm7 hcsm7 hinv_m7
          rcases hcsm7 with ⟨hm7_19, hm7_20, hm7_21, _, hm7_23, hm7_24, hm7_25, _, hm7_27, hm7_28, hm7_fp, _⟩
          simp only [arm64_norm, hx19_6, hx20_6, hx21_6, hx23_6, hx24_6, hx25_6, hx27_6, hx28_6, hfp_6]
            at hm7_19 hm7_20 hm7_21 hm7_23 hm7_24 hm7_25 hm7_27 hm7_28 hm7_fp
          refine SepWPp.weaken_pre (Entails.of_eq ?_)
            (h10108 sm7 hpcm7 hrunm7 hspm7 htrm7 hm7_19 hm7_20 hm7_21 hm7_23 hm7_24 hm7_25
              hm7_27 hm7_28 hm7_fp hinv_m7)
          dsimp only [bs2]; rw [etv2_encodeOptNoHeaderReceived_some_eq]
          simp +zetaDelta only [bs_u2, bs_u1, bs1, hauth, encodeOptMessage,
            optNoHeaderReceivedPBPinnedAt, noHeaderReceivedPBPinnedAt, unchunked2PinnedAt,
            optAuthenticatorPBPinnedAt, h4880_48, List.append_assoc]; (try sep_ac_rfl)
  intro sm4 hpcm4 hrunm4 hspm4 htrm4 hx19_4 hx20_4 hx21_4 hx23_4 hx24_4 hx25_4 hx27_4 hx28_4 hfp_4 hinv_4
  cases receivingHdr with
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
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (hinv_4.trans hinv5.1))
    rw [hpool5, etv2_encodeInnerState_noHeaderReceived_eq]
    simp +zetaDelta only [bs2, bs1, encodeOptMessage, List.append_nil, List.append_assoc]; (try sep_ac_rfl)
  | some dec =>
    simp only [Option.isSome_some, Bool.not_true] at hcap_dec_beq hcap_dec_bne
    have hfit_dec : bs2.length + (encodeMessage PolynomialDecoder.encodeRaw 2#32 dec).length ≤ cap.toNat := by
      simp +zetaDelta only [bs2, bs1, encodeOptMessage, List.length_append, List.length_singleton]
        at hfit ⊢; omega
    (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
    apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 11208#64)
    wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv5
    have hpool5 : A.pool lim st sm4 = A.pool lim st _ := (A.pool_of_vmPreserved hinv5.2).symm
    refine step_send_tail_11208_polyDec2_placed A lim st ext hpolyDec
      (sp + 4840#64) sp cap ptr g.1 dec bs2 hfit_dec halign
      (F := optNoHeaderReceivedPBPinnedAt A.repAlloc g.2 (sp + 4880#64) uc ∗
        ((sp + 16#64) ↦₆₄ w25) ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by rw [← h4840]; simp only [arm64_norm, *])
      (hinv_4.trans hinv5.1)
      (by dsimp only [optPolynomialDecoderPBPinnedAt]; rw [hpool5]; (try sep_ac_rfl)) ?_
    intro sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp hinv_m5
    simp only [arm64_norm, hx19_4, hx21_4, hx23_4, hx25_4, hx27_4, hx28_4, hfp_4]
      at hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp
    refine SepWPp.weaken_pre (Entails.of_eq ?_)
      (hnext sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp hinv_m5)
    rw [etv2_encodeInnerState_noHeaderReceived_eq]
    simp +zetaDelta only [bs2, bs1, encodeOptMessage, optPolynomialDecoderPBPinnedAt,
      List.append_assoc]; (try sep_ac_rfl)

/-! ## 3. `StepSendInnerStateAt6616Placed` Bridges (`idx = 0, 2, 5`) -/

theorem step_send_v1_keysUnsampled_at_6616_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (ext : String → Option (State → State))
    {roBase : BitVec 64} {s0 : State}
    (hkuLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 479)
      (withStepInv s0 (leafEncLen16Spec (keysUnsampledPBPinnedAt A.repAlloc) keysUnsampledPBEncodedLen)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hauthEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 454)
      (withStepInv s0 (authEncodeExactSpecOf resStack A lim)))
    (v : V1State.Chunked.KeysUnsampled) :
    StepSendInnerStateAt6616Placed resStack A lim st0 ext roBase s0 (.keysUnsampled v) := by
  intro sp cap ptr w25 g bs hv_len hfit halign ret s P F Q Qp oom
    hpc hrun hsp htr hx8 hx9 hx20 hx25 hinv0 hP hnext
  subst hP
  replace hx8 : s.readReg64 .x8 = 0#64 :=
    hx8.trans (by rw [show v1StateInnerCap g (.keysUnsampled v) = 0x8000000000000000#64 from rfl]; decide +kernel)
  rw [spqrSendEncodeJumpTableBytes_eq roBase]; dsimp only [spqrSendEncodeJumpTableBytesAt]
  (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
  apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 6632#64)
  wp_steps
  apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, wp_norm, *])
  intro hinv1
  have hpool1 : A.pool lim st0 s = A.pool lim st0 _ := (A.pool_of_vmPreserved hinv1.2).symm
  have h4840 : (sp + 4832#64) + 8#64 = sp + 4840#64 := by bv_omega
  dsimp only [v1StateInnerPBPinnedAt]; rw [h4840]
  refine step_send_v1_keysUnsampled_placed hres A lim st0 ext hkuLen hvarint hauthEnc
    sp cap ptr g.a.gKeysUnsampled v bs hv_len hfit halign
    (F := ((sp + 4832#64) ↦₆₄ 0x8000000000000000#64) ∗ ((sp + 16#64) ↦₆₄ w25) ∗
      memRegion (sp + 4832#64 + 64#64) 160 ∗ spqrSendEncodeJumpTableBytesAt roBase ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1.1)
    (by dsimp only [spqrSendEncodeJumpTableBytesAt]; rw [hpool1]; sep_ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m
  simp only [arm64_norm, hx25] at hm19 hm21 hm23 hm25 hm27 hm28 hmfp
  refine SepWPp.weaken_pre ?_
    (hnext sm hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m)
  dsimp only [v1StateInnerPBPinnedAt]; rw [h4840, spqrSendEncodeJumpTableBytes_eq roBase]
  exact Entails.of_eq (by sep_ac_rfl)

theorem step_send_v1_headerSent_at_6616_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (ext : String → Option (State → State))
    {roBase : BitVec 64} {s0 : State}
    (hhsLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 495)
      (withStepInv s0 (chunkedHeaderSentEncodedLenPinnedSpec A.repAlloc)))
    (hekSentLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 496)
      (withStepInv s0 (leafEncLen16Spec (ekSentPBPinnedAt A.repAlloc) ekSentPBEncodedLen)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hauthEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 454)
      (withStepInv s0 (authEncodeExactSpecOf resStack A lim)))
    (hmemcpy : subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy") etvMemcpyRegionSpec)
    (hpolyEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 456)
      (withStepInv s0 (etvPolyEncoderBudgetExactSpecOf resStack A lim)))
    (hpolyDec : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 455)
      (withStepInv s0 (etvPolyDecoderBudgetExactSpecOf resStack A lim)))
    (v : V1State.Chunked.HeaderSent) :
    StepSendInnerStateAt6616Placed resStack A lim st0 ext roBase s0 (.headerSent v) := by
  intro sp cap ptr w25 g bs hv_len hfit halign ret s P F Q Qp oom
    hpc hrun hsp htr hx8 hx9 hx20 hx25 hinv0 hP hnext
  subst hP
  replace hx8 : s.readReg64 .x8 = 2#64 :=
    hx8.trans (by rw [show v1StateInnerCap g (.headerSent v) = 0x8000000000000002#64 from rfl]; decide +kernel)
  rw [spqrSendEncodeJumpTableBytes_eq roBase]; dsimp only [spqrSendEncodeJumpTableBytesAt]
  (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
  apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 8000#64)
  wp_steps
  apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, wp_norm, *])
  intro hinv1
  have hpool1 : A.pool lim st0 s = A.pool lim st0 _ := (A.pool_of_vmPreserved hinv1.2).symm
  have h4840 : (sp + 4832#64) + 8#64 = sp + 4840#64 := by bv_omega
  dsimp only [v1StateInnerPBPinnedAt]; rw [h4840]
  refine step_send_v1_headerSent_placed hres A lim st0 ext
    hhsLen hekSentLen hvarint hauthEnc hmemcpy hpolyEnc hpolyDec
    sp cap ptr w25 g.a.gHeaderSent v bs hv_len hfit halign
    (F := ((sp + 4832#64) ↦₆₄ 0x8000000000000002#64) ∗
      memRegion (sp + 4832#64 + 184#64) 40 ∗ spqrSendEncodeJumpTableBytesAt roBase ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (hinv0.trans hinv1.1)
    (by dsimp only [spqrSendEncodeJumpTableBytesAt]; rw [hpool1]; sep_ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m
  simp only [arm64_norm] at hm19 hm21 hm23 hm27 hm28 hmfp
  refine SepWPp.weaken_pre ?_
    (hnext sm hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m)
  dsimp only [v1StateInnerPBPinnedAt]; rw [h4840, spqrSendEncodeJumpTableBytes_eq roBase]
  exact Entails.of_eq (by sep_ac_rfl)

theorem step_send_v1_noHeaderReceived_at_6616_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (ext : String → Option (State → State))
    {roBase : BitVec 64} {s0 : State}
    (hnhrLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 500)
      (withStepInv s0 (leafEncLen16Spec (noHeaderReceivedPBPinnedAt A.repAlloc) noHeaderReceivedPBEncodedLen)))
    (hpolyDecLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 493)
      (withStepInv s0 (leafEncLen16Spec (polynomialDecoderPBPinnedAt A.repAlloc) polynomialDecoderPBEncodedLen)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hauthEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 454)
      (withStepInv s0 (authEncodeExactSpecOf resStack A lim)))
    (hpolyDec : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 455)
      (withStepInv s0 (etvPolyDecoderBudgetExactSpecOf resStack A lim)))
    (v : V1State.Chunked.NoHeaderReceived) :
    StepSendInnerStateAt6616Placed resStack A lim st0 ext roBase s0 (.noHeaderReceived v) := by
  intro sp cap ptr w25 g bs hv_len hfit halign ret s P F Q Qp oom
    hpc hrun hsp htr hx8 hx9 hx20 hx25 hinv0 hP hnext
  subst hP
  replace hx8 : s.readReg64 .x8 = 5#64 :=
    hx8.trans (by rw [show v1StateInnerCap g (.noHeaderReceived v) = 0x8000000000000005#64 from rfl]; decide +kernel)
  rw [spqrSendEncodeJumpTableBytes_eq roBase]; dsimp only [spqrSendEncodeJumpTableBytesAt]
  (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
  apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 8724#64)
  wp_steps
  apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, wp_norm, *])
  intro hinv1
  have hpool1 : A.pool lim st0 s = A.pool lim st0 _ := (A.pool_of_vmPreserved hinv1.2).symm
  have ⟨h4840, h4880⟩ : (sp + 4832#64) + 8#64 = sp + 4840#64 ∧
      (sp + 4832#64) + 48#64 = sp + 4880#64 := ⟨by bv_omega, by bv_omega⟩
  dsimp only [v1StateInnerPBPinnedAt]; rw [h4840, h4880]
  refine step_send_v1_noHeaderReceived_placed hres A lim st0 ext
    hnhrLen hpolyDecLen hvarint hauthEnc hpolyDec
    sp cap ptr w25 g.a.gNoHeaderReceived v bs hv_len hfit halign
    (F := ((sp + 4832#64) ↦₆₄ 0x8000000000000005#64) ∗
      memRegion (sp + 4832#64 + 104#64) 120 ∗ spqrSendEncodeJumpTableBytesAt roBase ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1.1)
    (by dsimp only [spqrSendEncodeJumpTableBytesAt]; rw [hpool1]; sep_ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m
  simp only [arm64_norm] at hm19 hm21 hm23 hm27 hm28 hmfp
  refine SepWPp.weaken_pre ?_
    (hnext sm hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m)
  dsimp only [v1StateInnerPBPinnedAt]; rw [h4840, h4880, spqrSendEncodeJumpTableBytes_eq roBase]
  exact Entails.of_eq (by sep_ac_rfl)

/-! ### `VmPreserved` Callee-Spec Corollaries -/

theorem step_send_v1_headerSent_at_6616_vm_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (ext : String → Option (State → State))
    {roBase : BitVec 64} {s0 : State}
    (hhsLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 495)
      (withStepInv s0 (chunkedHeaderSentEncodedLenPinnedSpec A.repAlloc)))
    (hekSentLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 496)
      (withStepInv s0 (leafEncLen16Spec (ekSentPBPinnedAt A.repAlloc) ekSentPBEncodedLen)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hauthEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 454)
      (withStepInv s0 (authEncodeExactSpecOf resStack A lim)))
    (hmemcpy : subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy") etvMemcpyRegionSpec)
    (hpolyEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 456)
      (withStepInv s0 (etvPolyEncoderExactSpecOf resStack A.repAlloc)))
    (hpolyDec : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 455)
      (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A.repAlloc)))
    (v : V1State.Chunked.HeaderSent) :
    StepSendInnerStateAt6616Placed resStack A lim st0 ext roBase s0 (.headerSent v) :=
  step_send_v1_headerSent_at_6616_placed hres A lim st0 ext
    hhsLen hekSentLen hvarint hauthEnc hmemcpy
    (etvPolyEncoderBudgetExact_of_vm hpolyEnc)
    (etvPolyDecoderBudgetExact_of_vm hpolyDec) v

theorem step_send_v1_noHeaderReceived_at_6616_vm_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (ext : String → Option (State → State))
    {roBase : BitVec 64} {s0 : State}
    (hnhrLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 500)
      (withStepInv s0 (leafEncLen16Spec (noHeaderReceivedPBPinnedAt A.repAlloc) noHeaderReceivedPBEncodedLen)))
    (hpolyDecLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 493)
      (withStepInv s0 (leafEncLen16Spec (polynomialDecoderPBPinnedAt A.repAlloc) polynomialDecoderPBEncodedLen)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hauthEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 454)
      (withStepInv s0 (authEncodeExactSpecOf resStack A lim)))
    (hpolyDec : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 455)
      (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A.repAlloc)))
    (v : V1State.Chunked.NoHeaderReceived) :
    StepSendInnerStateAt6616Placed resStack A lim st0 ext roBase s0 (.noHeaderReceived v) :=
  step_send_v1_noHeaderReceived_at_6616_placed hres A lim st0 ext
    hnhrLen hpolyDecLen hvarint hauthEnc
    (etvPolyDecoderBudgetExact_of_vm hpolyDec) v

end LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerChunked2PlacedBudget

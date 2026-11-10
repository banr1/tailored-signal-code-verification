/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerChunked1PlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerChunked2Placed
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesVnEncodePlacedBudgetAux
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public meta import Lean -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsChunkedV1Budget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked1
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked2
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.V1StateHelpers
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesVnEncode
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Phase 3e (Part 2a): Slice `memcpy` & Variants `keysUnsampled`, `headerSent`

Proves `VmPreserved` slice `memcpy` helpers and threads `RustCliAllocBudget` through
`V1State::encode_raw` arms `keysUnsampled` (`idx = 0`) and `headerSent` (`idx = 2`).
-/

@[expose] public section

set_option linter.style.longLine false
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerChunked2PlacedBudgetAux

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
  (ChunkedHeaderSentPBGhost Unchunked2PBGhost Unchunked3PBGhost
   chunkedHeaderSentPBEncodedLen chunkedHeaderSentPBPinnedAt
   ekSentPBEncodedLen ekSentPBEncodedLen_eq_proto ekSentPBPinnedAt
   keysUnsampledPBEncodedLen keysUnsampledPBPinnedAt
   noneCap_add_two_beq_zero noneCap_add_two_bne_zero
   optAuthCap optAuthenticatorPBPinnedAt optAuthenticatorPBPinnedAt_eq
   optEkSentPBPinnedAt optKeysUnsampledPBPinnedAt
   optPolynomialDecoderPBPinnedAt optPolynomialEncoderPBPinnedAt
   unchunked2PinnedAt unchunked3PinnedAt
   v1StateInnerPayloadEncodedLen v1StatePBEncodedLen varintLen)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (hwVarintLen_bvShift_eq_ofNat_varintLen_norm hwVarintLen_eq_ofNat_varintLen_norm
   noneCap_add_one_beq_zero noneCap_add_one_bne_zero
   ofNat_countLeadingZeros_32 ofNat_countLeadingZeros_64 ofNat_length_beq_zero_of_lt
   ule_self_64 ule_zero_64 ult_self_64 ult_zero_64
   vecU8At_eq_header_sep_buf vecU8Buf
   zeroExtend64_beq_zero32 zext64_truncate32)
open CryptoVerification.SpqrV1.Prost.EncodeToVec
  (StepInv cap_beq_len_false_of_lt elem_len_ult_spare_false_of_le
   encodeToVecCalleeStackOf encodeVarint_length_pos
   etv2_bv_msgFieldLen etv2_encodeBytesField_3_eq
   etv2_encodeInnerState_headerSent_eq etv2_encodeInnerState_keysUnsampled_eq
   etv2_encodeOptEkSent_some_eq etv2_encodeOptKeysUnsampled_some_eq
   etv2_encodeUint64Field_1_eq
   etv2_optAuth_cap_bounds etv2_optEkSentPBPinnedAt_cap_bounds
   noneCap2_add_two_beq_zero noneCap2_add_two_bne_zero
   noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
   optEkSentCap optEkSentPBPinnedAt_eq optEkSentRest
   optKeysUnsampledCap optKeysUnsampledPBPinnedAt_cap_bounds
   optKeysUnsampledPBPinnedAt_eq optKeysUnsampledRest
   optPolyDecCap optPolyEncCap
   optPolynomialDecoderPBPinnedAt_cap_bounds optPolynomialDecoderPBPinnedAt_eq
   optPolynomialEncoderPBPinnedAt_cap_bounds optPolynomialEncoderPBPinnedAt_eq
   vecU8At_expose_one vecU8At_expose_slice vecU8At_pack_one vecU8At_pack_slice
   vecU8Buf_eq_of_nonempty withStepInv)
open CryptoVerification.Cli.SpqrV1.Top.Send.CodePlaced (blkPl_427_ρ)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
  (spqrSendPlacedEntry spqrSendPlacedProg)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerHeaderPlacedBudget
  (step_send_chunked_encLen48_call_placed step_send_encode_auth_call_placed
   step_send_encode_polyEncoder_budget_call_placed step_send_encode_varint_call_placed
   step_send_leaf_encLen16_call_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerChunked1PlacedBudgetAux
  (sepWPp_extract_pure sepWPp_extract_vecU8At_bounds step_send_tail_10352_polyDec3_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesVnEncodePlacedBudgetAux
  (step_send_memcpy_call_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhaseBudget
  (authEncodeExactSpecOf encodeVarintExactSpecOf etvMemcpyRegionSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsPlacedBudget
  (sepWP_done_tpidr sepWP_done_vm sepWPp_of_sepWP_cs_vm)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonBudget
  (leafEncLen16Spec)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonPlacedBudget
  (etvPolyDecoderBudgetExactSpecOf etvPolyEncoderBudgetExactSpecOf)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsChunkedV1Budget
  (chunkedHeaderSentEncodedLenPinnedSpec)

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

/-! ## 1. Slice `memcpy` Helper at `s.sp = sp` (`vecU8At` at `sp + 1424#64`) -/

/-- Execute `bl memcpy` (`lsρ "memcpy"`) on a non-empty `Vec<u8>` buffer slice at `sp + 1424#64`,
threading `A.pool lim st`. -/
theorem send2_step_memcpy_slice_placed {resStack : Nat} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State)) {s0 s : State}
    (hmemcpy : subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy") etvMemcpyRegionSpec)
    (sp cap ptr srcCap srcPtr ret_pc : BitVec 64) (bs4 srcBs : List (BitVec 8))
    (hemp : srcBs.isEmpty = false) (hsrc_le : srcBs.length ≤ srcCap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = lsρ "memcpy") (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace) (hlr : s.readReg64 .x30 = ret_pc)
    (hx0 : s.readReg64 .x0 = ptr + BitVec.ofNat 64 bs4.length) (hx1 : s.readReg64 .x1 = srcPtr)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 srcBs.length)
    (hsrc_lt : srcBs.length < 2 ^ 64) (hinv0 : StepInv s0 s)
    (hP : P = ((((sp + 1424#64) ↦₆₄ cap) ∗ ((sp + 1432#64) ↦₆₄ ptr) ∗
        ((sp + 1440#64) ↦₆₄ BitVec.ofNat 64 bs4.length) ∗ A.repAlloc.live ptr cap.toNat 1 ∗
        (ptr ↦ₛ bs4) ∗
        memRegion (ptr + BitVec.ofNat 64 bs4.length) srcBs.length ∗
        memRegion (ptr + BitVec.ofNat 64 bs4.length + BitVec.ofNat 64 srcBs.length)
          (cap.toNat - bs4.length - srcBs.length)) ∗ vecU8Buf A.repAlloc srcCap srcPtr srcBs ∗
      A.pool lim st s ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        (((((sp + 1424#64) ↦₆₄ cap) ∗ ((sp + 1432#64) ↦₆₄ ptr) ∗
            ((sp + 1440#64) ↦₆₄ BitVec.ofNat 64 bs4.length) ∗ A.repAlloc.live ptr cap.toNat 1 ∗
            (ptr ↦ₛ bs4) ∗
            ((ptr + BitVec.ofNat 64 bs4.length) ↦ₛ srcBs) ∗
            memRegion (ptr + BitVec.ofNat 64 bs4.length + BitVec.ofNat 64 srcBs.length)
              (cap.toNat - bs4.length - srcBs.length)) ∗ vecU8Buf A.repAlloc srcCap srcPtr srcBs ∗
          A.pool lim st sm ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  subst hP; rw [vecU8Buf_eq_of_nonempty A.repAlloc srcCap srcPtr srcBs hemp hsrc_le]
  have hlen_toNat : (BitVec.ofNat 64 srcBs.length).toNat = srcBs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsrc_lt]
  refine step_send_memcpy_call_placed A lim st hmemcpy
    (ptr + BitVec.ofNat 64 bs4.length) srcPtr sp ret_pc srcBs
    (F := ((sp + 1424#64) ↦₆₄ cap) ∗ ((sp + 1432#64) ↦₆₄ ptr) ∗
      ((sp + 1440#64) ↦₆₄ BitVec.ofNat 64 bs4.length) ∗
      A.repAlloc.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs4) ∗
      memRegion (ptr + BitVec.ofNat 64 bs4.length + BitVec.ofNat 64 srcBs.length)
        (cap.toNat - bs4.length - srcBs.length) ∗
      (⌜srcBs.length ≤ srcCap.toNat ∧ srcCap.toNat < 2 ^ 63 ∧ srcPtr ≠ 0⌝ ∗
        A.repAlloc.live srcPtr srcCap.toNat 1 ∗
        memRegion (srcPtr + BitVec.ofNat 64 srcBs.length) (srcCap.toNat - srcBs.length)) ∗
      stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F)
    hpc hrun hsp halign htr hlr hx0 hx1 (by simp only [hx2, hlen_toNat]) hinv0 (by sep_ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm _hvmm hcsm hinvm
  refine SepWPp.weaken_pre (Entails.of_eq ?_) (hnext sm hpcm hrunm hspm htrm hcsm hinvm)
  rw [vecU8Buf_eq_of_nonempty A.repAlloc srcCap srcPtr srcBs hemp hsrc_le]; sep_ac_rfl

/-! ## 2. Variant `idx = 0`: `.keysUnsampled` (`+6632 .. +6708`, `+9072 .. +9260`, join `+6216`) -/

/-- Step `+6632 .. +6216` for `is = .keysUnsampled v`, threading `A.pool lim st`. -/
theorem step_send_v1_keysUnsampled_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    {s0 s : State}
    (hkuLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 479)
      (withStepInv s0 (leafEncLen16Spec (keysUnsampledPBPinnedAt A.repAlloc) keysUnsampledPBEncodedLen)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hauthEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 454)
      (withStepInv s0 (authEncodeExactSpecOf resStack A lim)))
    (sp cap ptr : BitVec 64) (g : Unchunked2PBGhost)
    (v : V1State.Chunked.KeysUnsampled) (bs : List (BitVec 8))
    (hv_len : v1StatePBEncodedLen ⟨some (.keysUnsampled v)⟩ < 2 ^ 64)
    (hfit : bs.length + (V1State.InnerState.encode (.keysUnsampled v)).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = spqrSendPlacedEntry + 6632#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace) (hinv0 : StepInv s0 s)
    (hP : P = (optKeysUnsampledPBPinnedAt A.repAlloc g (sp + 4840#64) v.uc ∗
      vecU8At A.repAlloc (sp + 1424#64) cap ptr bs ∗ A.pool lim st s ∗
      stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = spqrSendPlacedEntry + 6216#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = s.readReg64 .x25 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((optKeysUnsampledPBPinnedAt A.repAlloc g (sp + 4840#64) v.uc ∗
          vecU8At A.repAlloc (sp + 1424#64) cap ptr
            (bs ++ V1State.InnerState.encode (.keysUnsampled v)) ∗
          A.pool lim st sm ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  subst hP
  rw [etv2_encodeInnerState_keysUnsampled_eq] at hfit
  simp only [List.length_append, List.length_singleton] at hfit
  have ⟨h1432, h1440⟩ : (sp + 1424#64) + 8#64 = sp + 1432#64 ∧
      (sp + 1424#64) + 16#64 = sp + 1440#64 := ⟨by bv_omega, by bv_omega⟩
  have h4840_48 : (sp + 4840#64) + 48#64 = sp + 4888#64 := by bv_omega
  refine sepWPp_extract_pure
    ((optKeysUnsampledCap g v.uc + 2#64 == 0#64) = !v.uc.isSome ∧
      (optKeysUnsampledCap g v.uc + 2#64 != 0#64) = v.uc.isSome)
    (fun R' hm => optKeysUnsampledPBPinnedAt_cap_bounds (p := sp + 4840#64)
      (R := vecU8At A.repAlloc (sp + 1424#64) cap ptr bs ∗ A.pool lim st s ∗
        stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
      (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm))
    fun ⟨hcap_uc_beq, hcap_uc_bne⟩ => ?_
  cases huc : v.uc with
  | none =>
    have huc_eq : v = ⟨none⟩ := by cases v; subst huc; rfl
    subst huc_eq; simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
    rw [optKeysUnsampledPBPinnedAt_eq A.repAlloc g (sp + 4840#64) none]
    have hvar0 : encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.keysUnsampled ⟨none⟩))) =
        [0x00#8] := rfl
    have hlt1 : bs.length < cap.toNat := by change bs.length + (1 + 1) + 0 ≤ cap.toNat at hfit; omega
    have hlt2 : (bs ++ [0x0a#8]).length < cap.toNat := by
      simp only [List.length_append, List.length_singleton]
      change bs.length + (1 + 1) + 0 ≤ cap.toNat at hfit; omega
    refine sepWPp_extract_vecU8At_bounds (v := sp + 1424#64) (cap := cap) (ptr := ptr) (bs := bs)
      (F := ((sp + 4840#64) ↦₆₄ optKeysUnsampledCap g none) ∗
        optKeysUnsampledRest A.repAlloc g (sp + 4840#64) none ∗
        A.pool lim st s ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F)
      (by sep_ac_rfl) fun _ hcap hptr => ?_
    have hbeq1 := cap_beq_len_false_of_lt hlt1 hcap
    have hbeq2 : (cap == BitVec.ofNat 64 bs.length + 1#64) = false := by
      simpa only [List.length_append, List.length_singleton, BitVec.ofNat_add] using
        cap_beq_len_false_of_lt hlt2 hcap
    rw [vecU8At_expose_one A.repAlloc (sp + 1424#64) cap ptr bs hlt1 hcap hptr, h1432, h1440]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b0 => ?_
    (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
    apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 6680#64)
    by_vm_steps_safe
      wp_steps; apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *]); intro hinv1
      have hpack1 := vecU8At_pack_one A.repAlloc (sp + 1424#64) cap ptr bs 0x0a#8 hlt1 hcap hptr; rw [h1432, h1440] at hpack1
      refine SepWPp.weaken_pre
        (P' := ((sp + 4840#64) ↦₆₄ optKeysUnsampledCap g none) ∗ optKeysUnsampledRest A.repAlloc g (sp + 4840#64) none ∗
          vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs ++ [0x0a#8]) ∗ A.pool lim st s ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F)
        (by rw [← hpack1]; exact Entails.of_eq (by sep_ac_rfl)) ?_
      rw [vecU8At_expose_one A.repAlloc (sp + 1424#64) cap ptr (bs ++ [0x0a#8]) hlt2 hcap hptr, h1432, h1440]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b1 => ?_
      have hlen_add1 : BitVec.ofNat 64 (bs ++ [0x0a#8]).length = BitVec.ofNat 64 bs.length + 1#64 := by
        simp only [List.length_append, List.length_singleton, BitVec.ofNat_add]
      rw [hlen_add1]; (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
      apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 6216#64)
      by_vm_steps_safe
        wp_steps; apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *]); intro hinv2
        have hpool12 : A.pool lim st s = A.pool lim st _ := (A.pool_of_vmPreserved (hinv1.2.trans hinv2.2)).symm
        have hpack2 := vecU8At_pack_one A.repAlloc (sp + 1424#64) cap ptr (bs ++ [0x0a#8]) 0x00#8 hlt2 hcap hptr
        rw [h1432, h1440, hlen_add1, show BitVec.ofNat 64 bs.length + 1#64 + 1#64 = BitVec.ofNat 64 bs.length + 2#64 by bv_omega] at hpack2
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) ((hinv0.trans hinv1.1).trans hinv2.1))
        rw [optKeysUnsampledPBPinnedAt_eq A.repAlloc g (sp + 4840#64), hpack2, hpool12, etv2_encodeInnerState_keysUnsampled_eq, hvar0]
        simp only [encodeOptMessage, List.append_nil, List.append_assoc]; sep_ac_rfl
  | some u =>
    simp only [huc, Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
    rw [optKeysUnsampledPBPinnedAt_eq A.repAlloc g (sp + 4840#64) (some u)]
    have hpay_eq : v1StateInnerPayloadEncodedLen (.keysUnsampled v) =
        1 + varintLen (BitVec.ofNat 64 (keysUnsampledPBEncodedLen u)) + keysUnsampledPBEncodedLen u := by
      rw [v1StateInnerPayloadEncodedLen, huc]; rfl
    have hpay_lt : 1 + varintLen (BitVec.ofNat 64 (keysUnsampledPBEncodedLen u)) + keysUnsampledPBEncodedLen u < 2 ^ 64 := by
      dsimp only [v1StatePBEncodedLen] at hv_len; rw [hpay_eq] at hv_len; omega
    have hu_lt : keysUnsampledPBEncodedLen u < 2 ^ 64 := by omega
    obtain ⟨hbv_sum, hbv_ule, hbv_ult⟩ := etv2_bv_msgFieldLen hpay_lt
    have hlt1 : bs.length < cap.toNat := by omega
    refine sepWPp_extract_vecU8At_bounds (v := sp + 1424#64) (cap := cap) (ptr := ptr) (bs := bs)
      (F := ((sp + 4840#64) ↦₆₄ optKeysUnsampledCap g (some u)) ∗ optKeysUnsampledRest A.repAlloc g (sp + 4840#64) (some u) ∗
        A.pool lim st s ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F)
      (by sep_ac_rfl) fun _ hcap hptr => ?_
    have hbeq1 := cap_beq_len_false_of_lt hlt1 hcap
    rw [vecU8At_expose_one A.repAlloc (sp + 1424#64) cap ptr bs hlt1 hcap hptr, h1432, h1440]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b0 => ?_
    (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 479)
    by_vm_steps_safe
      wp_steps; apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *]); intro hinv1
      have hpack1 := vecU8At_pack_one A.repAlloc (sp + 1424#64) cap ptr bs 0x0a#8 hlt1 hcap hptr; rw [h1432, h1440] at hpack1
      have hku_pin : ((sp + 4840#64) ↦₆₄ optKeysUnsampledCap g (some u)) ∗ optKeysUnsampledRest A.repAlloc g (sp + 4840#64) (some u) =
          keysUnsampledPBPinnedAt A.repAlloc g (sp + 4840#64) u := by
        simpa only [optKeysUnsampledPBPinnedAt] using (optKeysUnsampledPBPinnedAt_eq A.repAlloc g (sp + 4840#64) (some u)).symm
      refine step_send_leaf_encLen16_call_placed hres ext (keysUnsampledPBPinnedAt A.repAlloc) keysUnsampledPBEncodedLen hkuLen
        (sp + 4840#64) sp (spqrSendPlacedEntry + 9088#64) g u hu_lt
        (F := vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs ++ [0x0a#8]) ∗ A.pool lim st s ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (hinv0.trans hinv1.1) (by rw [← hpack1, ← hku_pin]; sep_ac_rfl) ?_
      intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1 ⟨hm19, hm20, hm21, hm22, hm23, _, hm25, _, hm27, hm28, hmfp, _⟩ hinv_m1 hvm_m1
      simp only [arm64_norm] at hm19 hm20 hm21 hm22 hm23 hm25 hm27 hm28 hmfp
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 451)
      wp_steps; apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *]); intro hinv2
      have hpool2 : A.pool lim st s = A.pool lim st _ := (A.pool_of_vmPreserved (hinv1.2.trans (hvm_m1.trans hinv2.2))).symm
      set bs1 := (bs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.keysUnsampled v)))
      have hfit_var1 : (bs ++ [0x0a#8]).length + (encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.keysUnsampled v)))).length ≤ cap.toNat := by
        simp only [List.length_append, List.length_singleton]; omega
      refine step_send_encode_varint_call_placed A lim st hvarint
        (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.keysUnsampled v))) (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 9136#64) (bs ++ [0x0a#8]) hfit_var1
        (F := keysUnsampledPBPinnedAt A.repAlloc g (sp + 4840#64) u ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
        (by rw [hpay_eq]; simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m1.trans hinv2.1) (by rw [hpool2]; sep_ac_rfl) ?_
      intro sm2 hpcm2 hrunm2 hspm2 htrm2 ⟨hm2_19, hm2_20, hm2_21, hm2_22, hm2_23, _, hm2_25, _, hm2_27, hm2_28, hm2_fp, _⟩ hinv_m2
      simp only [arm64_norm, hm19, hm20, hm21, hm22, hm23, hm25, hm27, hm28, hmfp] at hm2_19 hm2_20 hm2_21 hm2_22 hm2_23 hm2_25 hm2_27 hm2_28 hm2_fp
      rw [huc, etv2_encodeOptKeysUnsampled_some_eq] at hfit; simp only [List.length_append, List.length_singleton] at hfit
      have hlt2 : bs1.length < cap.toNat := by dsimp only [bs1]; simp only [List.length_append, List.length_singleton]; omega
      have hbeq2 := cap_beq_len_false_of_lt hlt2 hcap
      rw [vecU8At_expose_one A.repAlloc (sp + 1424#64) cap ptr bs1 hlt2 hcap hptr, h1432, h1440]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b1 => ?_
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 479)
      by_vm_steps_safe
        wp_steps; apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *]); intro hinv3
        have hpack2 := vecU8At_pack_one A.repAlloc (sp + 1424#64) cap ptr bs1 0x0a#8 hlt2 hcap hptr; rw [h1432, h1440] at hpack2
        refine step_send_leaf_encLen16_call_placed hres ext (keysUnsampledPBPinnedAt A.repAlloc) keysUnsampledPBEncodedLen hkuLen
          (sp + 4840#64) sp (spqrSendPlacedEntry + 9180#64) g u hu_lt
          (F := vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs1 ++ [0x0a#8]) ∗ A.pool lim st sm2 ∗ F)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
          (hinv_m2.trans hinv3.1) (by rw [← hpack2]; sep_ac_rfl) ?_
        intro sm3 hpcm3 hrunm3 hspm3 htrm3 hx0m3 ⟨hm3_19, hm3_20, hm3_21, hm3_22, hm3_23, _, hm3_25, _, hm3_27, hm3_28, hm3_fp, _⟩ hinv_m3 hvm_m3
        simp only [arm64_norm, hm2_19, hm2_20, hm2_21, hm2_22, hm2_23, hm2_25, hm2_27, hm2_28, hm2_fp] at hm3_19 hm3_20 hm3_21 hm3_22 hm3_23 hm3_25 hm3_27 hm3_28 hm3_fp
        (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 451)
        wp_steps; apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *]); intro hinv4
        have hpool4 : A.pool lim st sm2 = A.pool lim st _ := (A.pool_of_vmPreserved (hinv3.2.trans (hvm_m3.trans hinv4.2))).symm
        set bs2 := (bs1 ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 (keysUnsampledPBEncodedLen u))
        have hfit_var2 : (bs1 ++ [0x0a#8]).length + (encodeVarint (BitVec.ofNat 64 (keysUnsampledPBEncodedLen u))).length ≤ cap.toNat := by
          dsimp only [bs1]; simp only [List.length_append, List.length_singleton]; omega
        refine step_send_encode_varint_call_placed A lim st hvarint (BitVec.ofNat 64 (keysUnsampledPBEncodedLen u))
          (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 9188#64) (bs1 ++ [0x0a#8]) hfit_var2
          (F := keysUnsampledPBPinnedAt A.repAlloc g (sp + 4840#64) u ∗ F)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hinv_m3.trans hinv4.1) (by rw [hpool4]; (try sep_ac_rfl)) ?_
        intro sm4 hpcm4 hrunm4 hspm4 htrm4 ⟨hm4_19, hm4_20, hm2_21', hm4_22, hm4_23, _, hm4_25, _, hm4_27, hm4_28, hm4_fp, _⟩ hinv_m4
        simp only [arm64_norm, hm3_19, hm3_20, hm3_21, hm3_22, hm3_23, hm3_25, hm3_27, hm3_28, hm3_fp] at hm4_19 hm4_20 hm2_21' hm4_22 hm4_23 hm4_25 hm4_27 hm4_28 hm4_fp
        dsimp only [keysUnsampledPBPinnedAt, unchunked2PinnedAt]; rw [h4840_48]
        refine sepWPp_extract_pure
          ((optAuthCap g u.auth + 1#64 == 0#64) = !u.auth.isSome ∧ (optAuthCap g u.auth + 1#64 != 0#64) = u.auth.isSome)
          (fun R' hm => etv2_optAuth_cap_bounds (A := A.repAlloc) (p := sp + 4840#64)
            (R := ((sp + 4888#64) ↦₆₄ u.epoch) ∗ vecU8At A.repAlloc (sp + 1424#64) cap ptr bs2 ∗ A.pool lim st sm4 ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
            (Satisfies.mono (Entails.of_eq (by dsimp only [bs2]; sep_ac_rfl)) hm))
          fun ⟨hcap_auth_beq, hcap_auth_bne⟩ => ?_
        let bs3 := bs2 ++ encodeUint64Field 1#32 u.epoch
        suffices h9240 : ∀ sm5 : State, sm5.pc = spqrSendPlacedEntry + 9240#64 → sm5.status = .Running → sm5.sp = sp → sm5.trace = s0.trace →
            sm5.readReg64 .x19 = s.readReg64 .x19 → sm5.readReg64 .x20 = optKeysUnsampledCap g (some u) → sm5.readReg64 .x21 = s.readReg64 .x21 →
            sm5.readReg64 .x22 = sp + 4704#64 → sm5.readReg64 .x23 = s.readReg64 .x23 → sm5.readReg64 .x25 = s.readReg64 .x25 →
            sm5.readReg64 .x27 = s.readReg64 .x27 → sm5.readReg64 .x28 = s.readReg64 .x28 → sm5.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm5 →
            SepWPp (spqrSendPlacedProg ext) ret sm5 (((optAuthenticatorPBPinnedAt A.repAlloc g (sp + 4840#64) u.auth ∗ ((sp + 4888#64) ↦₆₄ u.epoch)) ∗
              vecU8At A.repAlloc (sp + 1424#64) cap ptr bs3 ∗ A.pool lim st sm5 ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F) Q Qp oom by
          cases hep : (u.epoch == 0#64)
          · have hfit_ep : bs2.length + 1 + (encodeVarint u.epoch).length ≤ cap.toNat := by
              rw [etv2_encodeUint64Field_1_eq, hep] at hfit; dsimp only [bs2, bs1]
              simp only [Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_singleton] at hfit ⊢; omega
            have hlt_ep : bs2.length < cap.toNat := by have := encodeVarint_length_pos u.epoch; omega
            have hbeq_ep := cap_beq_len_false_of_lt hlt_ep hcap
            rw [vecU8At_expose_one A.repAlloc (sp + 1424#64) cap ptr bs2 hlt_ep hcap hptr, h1432, h1440]
            simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b2 => ?_
            (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 451)
            by_vm_steps_safe
              wp_steps; apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *]); intro hinv5
              have hpool5 : A.pool lim st sm4 = A.pool lim st _ := (A.pool_of_vmPreserved hinv5.2).symm
              have hpack_ep := vecU8At_pack_one A.repAlloc (sp + 1424#64) cap ptr bs2 0x08#8 hlt_ep hcap hptr; rw [h1432, h1440] at hpack_ep
              refine step_send_encode_varint_call_placed A lim st hvarint u.epoch (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 9240#64) (bs2 ++ [0x08#8])
                (by simpa only [List.length_append, List.length_singleton] using hfit_ep)
                (F := (optAuthenticatorPBPinnedAt A.repAlloc g (sp + 4840#64) u.auth ∗ ((sp + 4888#64) ↦₆₄ u.epoch)) ∗ F)
                (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (hinv_m4.trans hinv5.1) (by rw [← hpack_ep, hpool5]; (try sep_ac_rfl)) ?_
              intro sm5 hpcm5 hrunm5 hspm5 htrm5 ⟨hm5_19, hm5_20, hm5_21, hm5_22, hm5_23, _, hm5_25, _, hm5_27, hm5_28, hm5_fp, _⟩ hinv_m5
              simp only [arm64_norm, hm4_19, hm4_20, hm2_21', hm4_22, hm4_23, hm4_25, hm4_27, hm4_28, hm4_fp] at hm5_19 hm5_20 hm5_21 hm5_22 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp
              refine SepWPp.weaken_pre (Entails.of_eq ?_)
                (h9240 sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_19 hm5_20 hm5_21 hm5_22 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp hinv_m5)
              simp +zetaDelta only [bs3, etv2_encodeUint64Field_1_eq, hep, Bool.false_eq_true, ↓reduceIte, List.append_assoc]; (try sep_ac_rfl)
          · (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 9240#64)
            wp_steps; apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *]); intro hinv5
            have hpool5 : A.pool lim st sm4 = A.pool lim st _ := (A.pool_of_vmPreserved hinv5.2).symm
            refine SepWPp.weaken_pre (Entails.of_eq (by rw [hpool5]; simp +zetaDelta only [bs3, etv2_encodeUint64Field_1_eq, hep, ↓reduceIte, List.append_nil]; (try sep_ac_rfl)))
              (h9240 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (hinv_m4.trans hinv5.1))
        intro sm5 hpcm5 hrunm5 hspm5 htrm5 hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 hx25_5 hx27_5 hx28_5 hfp_5 hinv_5
        have hx20_cap : optKeysUnsampledCap g (some u) = optAuthCap g u.auth := rfl; rw [hx20_cap] at hx20_5
        cases hauth : u.auth with
        | none =>
          simp only [hauth, Option.isSome_none, Bool.not_false] at hcap_auth_beq hcap_auth_bne
          (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 6216#64)
          wp_steps; apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *]); intro hinv6
          have hpool6 : A.pool lim st sm5 = A.pool lim st _ := (A.pool_of_vmPreserved hinv6.2).symm
          refine SepWPp.weaken_pre (Entails.of_eq ?_)
            (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_5.trans hinv6.1))
          rw [hpool6, etv2_encodeInnerState_keysUnsampled_eq, huc, etv2_encodeOptKeysUnsampled_some_eq, hauth]
          simp +zetaDelta only [bs3, bs2, bs1, huc, hauth, encodeOptMessage, optKeysUnsampledPBPinnedAt, keysUnsampledPBPinnedAt, unchunked2PinnedAt, h4840_48, List.append_nil, List.append_assoc]; (try sep_ac_rfl)
        | some auth =>
          simp only [hauth, Option.isSome_some, Bool.not_true] at hcap_auth_beq hcap_auth_bne
          have hfit_auth : bs3.length + (encodeMessage ProtoAuthenticator.encodeRaw 2#32 auth).length ≤ cap.toNat := by
            rw [hauth] at hfit; dsimp only [bs3, bs2, bs1, encodeOptMessage] at hfit ⊢; simp only [List.length_append, List.length_singleton] at hfit ⊢; omega
          (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 454)
          wp_steps; apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *]); intro hinv6
          have hpool6 : A.pool lim st sm5 = A.pool lim st _ := (A.pool_of_vmPreserved hinv6.2).symm
          refine step_send_encode_auth_call_placed A lim st ext hauthEnc
            (sp + 4840#64) (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 9260#64) g auth bs3 hfit_auth (F := ((sp + 4888#64) ↦₆₄ u.epoch) ∗ F)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hinv_5.trans hinv6.1) (by rw [hpool6]; simp only [hauth, optAuthenticatorPBPinnedAt]; (try sep_ac_rfl)) ?_
          intro sm6 hpcm6 hrunm6 hspm6 htrm6 ⟨hm6_19, _, hm6_21, _, hm6_23, _, hm6_25, _, hm6_27, hm6_28, hm6_fp, _⟩ hinv_m6
          simp only [arm64_norm, hx19_5, hx21_5, hx23_5, hx25_5, hx27_5, hx28_5, hfp_5] at hm6_19 hm6_21 hm6_23 hm6_25 hm6_27 hm6_28 hm6_fp
          (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 6216#64)
          wp_steps; apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *]); intro hinv7
          have hpool7 : A.pool lim st sm6 = A.pool lim st _ := (A.pool_of_vmPreserved hinv7.2).symm
          refine SepWPp.weaken_pre (Entails.of_eq ?_)
            (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m6.trans hinv7.1))
          rw [hpool7, etv2_encodeInnerState_keysUnsampled_eq, huc, etv2_encodeOptKeysUnsampled_some_eq, hauth]
          simp +zetaDelta only [bs3, bs2, bs1, huc, hauth, encodeOptMessage, optKeysUnsampledPBPinnedAt, keysUnsampledPBPinnedAt, unchunked2PinnedAt, optAuthenticatorPBPinnedAt, h4840_48, List.append_assoc]; (try sep_ac_rfl)

/-! ## 3. Variant `idx = 2`: `.headerSent` (`+8000 .. +8368`, `+10352 .. +10364`) -/

/-- Sub-step `+8060 .. +8320`: encode field 1 (`v.uc : Option EkSent`) of `HeaderSent`,
threading `A.pool lim st`. -/
private theorem send2_step_headerSent_uc_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    {s0 s : State}
    (hekSentLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 496)
      (withStepInv s0 (leafEncLen16Spec (ekSentPBPinnedAt A.repAlloc) ekSentPBEncodedLen)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hauthEnc : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 454)
      (withStepInv s0 (authEncodeExactSpecOf resStack A lim)))
    (hmemcpy : subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy") etvMemcpyRegionSpec)
    (sp cap ptr w25 : BitVec 64) (g : Unchunked3PBGhost) (uc : Option V1State.Unchunked.EkSent)
    (bs : List (BitVec 8))
    (hfit : bs.length + (encodeOptMessage V1State.Unchunked.EkSent.encodeRaw 1#32 uc).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = spqrSendPlacedEntry + 8060#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = sp + 4704#64) (hx25 : s.readReg64 .x25 = w25) (hinv0 : StepInv s0 s)
    (hP : P = (optEkSentPBPinnedAt A.repAlloc g (sp + 4840#64) uc ∗
      vecU8At A.repAlloc (sp + 1424#64) cap ptr bs ∗ A.pool lim st s ∗
      ((sp + 16#64) ↦₆₄ w25) ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = spqrSendPlacedEntry + 8320#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = w25 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((optEkSentPBPinnedAt A.repAlloc g (sp + 4840#64) uc ∗
          vecU8At A.repAlloc (sp + 1424#64) cap ptr
            (bs ++ encodeOptMessage V1State.Unchunked.EkSent.encodeRaw 1#32 uc) ∗
          A.pool lim st sm ∗ ((sp + 16#64) ↦₆₄ w25) ∗
          stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  subst hP
  refine sepWPp_extract_vecU8At_bounds (v := sp + 1424#64) (cap := cap) (ptr := ptr) (bs := bs)
    (F := optEkSentPBPinnedAt A.repAlloc g (sp + 4840#64) uc ∗ A.pool lim st s ∗
      ((sp + 16#64) ↦₆₄ w25) ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F)
    (by sep_ac_rfl) fun _ hcap hptr => ?_
  refine sepWPp_extract_pure
    ((optEkSentCap g uc + 1#64 == 0#64) = !uc.isSome ∧
      (optEkSentCap g uc + 1#64 != 0#64) = uc.isSome)
    (fun R' hm => etv2_optEkSentPBPinnedAt_cap_bounds (p := sp + 4840#64)
      (R := vecU8At A.repAlloc (sp + 1424#64) cap ptr bs ∗ A.pool lim st s ∗
        ((sp + 16#64) ↦₆₄ w25) ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
      (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm))
    fun ⟨hcap_uc_beq, hcap_uc_bne⟩ => ?_
  have ⟨h1432, h1440⟩ : (sp + 1424#64) + 8#64 = sp + 1432#64 ∧
      (sp + 1424#64) + 16#64 = sp + 1440#64 := ⟨by bv_omega, by bv_omega⟩
  have h4704_136 : (sp + 4704#64) + 136#64 = sp + 4840#64 := by bv_omega
  cases huc : uc with
  | none =>
    rw [optEkSentPBPinnedAt_eq A.repAlloc g (sp + 4840#64) none]
    simp only [huc, Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
    (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
    apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 8320#64)
    wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv1
    have hpool1 : A.pool lim st s = A.pool lim st _ := (A.pool_of_vmPreserved hinv1.2).symm
    refine SepWPp.weaken_pre (Entails.of_eq ?_)
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (hinv0.trans hinv1.1))
    rw [← optEkSentPBPinnedAt_eq A.repAlloc g (sp + 4840#64) none, huc, hpool1]
    simp only [encodeOptMessage, List.append_nil]
  | some u =>
    rw [optEkSentPBPinnedAt_eq A.repAlloc g (sp + 4840#64) (some u)]
    simp only [huc, Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
    rw [huc, etv2_encodeOptEkSent_some_eq] at hfit
    simp only [List.length_append, List.length_singleton] at hfit
    have hlt1 : bs.length < cap.toNat := by omega
    have hu_lt : ekSentPBEncodedLen u < 2 ^ 64 := by
      rw [← ekSentPBEncodedLen_eq_proto, V1State.Unchunked.EkSent.encodedLen]
      dsimp only [V1State.Unchunked.EkSent.encodeRaw]
      simp only [List.length_append]; have := BitVec.isLt cap; omega
    have hbeq_false := cap_beq_len_false_of_lt hlt1 hcap
    rw [vecU8At_expose_one A.repAlloc (sp + 1424#64) cap ptr bs hlt1 hcap hptr, h1432, h1440]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b0 => ?_
    (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
    apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 496)
    by_vm_steps_safe
      wp_steps
      apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv1
      have hpack1 := vecU8At_pack_one A.repAlloc (sp + 1424#64) cap ptr bs 0x0a#8 hlt1 hcap hptr
      rw [h1432, h1440] at hpack1
      have hek_pin :
          ((sp + 4840#64) ↦₆₄ optEkSentCap g (some u)) ∗
            optEkSentRest A.repAlloc g (sp + 4840#64) (some u) =
          ekSentPBPinnedAt A.repAlloc g (sp + 4840#64) u := by
        simpa only [optEkSentPBPinnedAt] using
          (optEkSentPBPinnedAt_eq A.repAlloc g (sp + 4840#64) (some u)).symm
      refine step_send_leaf_encLen16_call_placed hres ext
        (ekSentPBPinnedAt A.repAlloc) ekSentPBEncodedLen hekSentLen
        (sp + 4840#64) sp (spqrSendPlacedEntry + 8116#64) g u hu_lt
        (F := vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs ++ [0x0a#8]) ∗
          A.pool lim st s ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (hinv0.trans hinv1.1) (by rw [← hpack1, ← hek_pin]; sep_ac_rfl) ?_
      intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1 hcsm1 hinv_m1 hvm_m1
      rcases hcsm1 with ⟨hm19, hm20, hm21, _, hm23, _, hm25, _, hm27, hm28, hmfp, _⟩
      simp only [arm64_norm, hx20, hx25] at hm19 hm20 hm21 hm23 hm25 hm27 hm28 hmfp
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
      apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 451)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv2
      have hpool2 : A.pool lim st s = A.pool lim st _ :=
        (A.pool_of_vmPreserved (hinv1.2.trans (hvm_m1.trans hinv2.2))).symm
      set bs1 := (bs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 (ekSentPBEncodedLen u))
      have hfit_var : (bs ++ [0x0a#8]).length +
          (encodeVarint (BitVec.ofNat 64 (ekSentPBEncodedLen u))).length ≤ cap.toNat := by
        simp only [List.length_append, List.length_singleton]; omega
      refine step_send_encode_varint_call_placed A lim st hvarint
        (BitVec.ofNat 64 (ekSentPBEncodedLen u))
        (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 8124#64) (bs ++ [0x0a#8]) hfit_var
        (F := ekSentPBPinnedAt A.repAlloc g (sp + 4840#64) u ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hinv_m1.trans hinv2.1) (by rw [hpool2]; sep_ac_rfl) ?_
      intro sm2 hpcm2 hrunm2 hspm2 htrm2 hcsm2 hinv_m2
      rcases hcsm2 with ⟨hm2_19, hm2_20, hm2_21, _, hm2_23, _, hm2_25, _, hm2_27, hm2_28, hm2_fp, _⟩
      simp only [arm64_norm, hm19, hm20, hm21, hm23, hm25, hm27, hm28, hmfp]
        at hm2_19 hm2_20 hm2_21 hm2_23 hm2_25 hm2_27 hm2_28 hm2_fp
      dsimp only [ekSentPBPinnedAt, unchunked3PinnedAt]
      have ⟨h4840_24, h4840_72⟩ :
          (sp + 4840#64) + 0x18#64 = sp + 4864#64 ∧
          (sp + 4840#64) + 0x48#64 = sp + 4912#64 := ⟨by bv_omega, by bv_omega⟩
      rw [h4840_24, h4840_72]
      refine sepWPp_extract_pure
        ((optAuthCap g.auth u.auth + 1#64 == 0#64) = !u.auth.isSome ∧
          (optAuthCap g.auth u.auth + 1#64 != 0#64) = u.auth.isSome)
        (fun R' hm => etv2_optAuth_cap_bounds (A := A.repAlloc) (p := sp + 4864#64)
          (R := vecU8At A.repAlloc (sp + 4840#64) g.f3.cap g.f3.ptr u.dk ∗
            ((sp + 4912#64) ↦₆₄ u.epoch) ∗
            vecU8At A.repAlloc (sp + 1424#64) cap ptr bs1 ∗ A.pool lim st sm2 ∗
            ((sp + 16#64) ↦₆₄ w25) ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
          (Satisfies.mono (Entails.of_eq (by dsimp only [bs1]; sep_ac_rfl)) hm))
        fun ⟨hcap_auth_beq, hcap_auth_bne⟩ => ?_
      set bs2 := bs1 ++ encodeUint64Field 1#32 u.epoch
      suffices h8176 : ∀ sm3 : State,
          sm3.pc = spqrSendPlacedEntry + 8176#64 → sm3.status = .Running →
          sm3.sp = sp → sm3.trace = s0.trace →
          sm3.readReg64 .x19 = s.readReg64 .x19 → sm3.readReg64 .x21 = s.readReg64 .x21 →
          sm3.readReg64 .x23 = s.readReg64 .x23 → sm3.readReg64 .x25 = w25 →
          sm3.readReg64 .x27 = s.readReg64 .x27 → sm3.readReg64 .x28 = s.readReg64 .x28 →
          sm3.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm3 →
          SepWPp (spqrSendPlacedProg ext) ret sm3
            (((vecU8At A.repAlloc (sp + 4840#64) g.f3.cap g.f3.ptr u.dk ∗
              optAuthenticatorPBPinnedAt A.repAlloc g.auth (sp + 4864#64) u.auth ∗
              ((sp + 4912#64) ↦₆₄ u.epoch)) ∗
              vecU8At A.repAlloc (sp + 1424#64) cap ptr bs2 ∗ A.pool lim st sm3 ∗
              ((sp + 16#64) ↦₆₄ w25) ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
            Q Qp oom by
        cases hep : u.epoch == 0#64
        · have hfit_ep : bs1.length + 1 + (encodeVarint u.epoch).length ≤ cap.toNat := by
            rw [etv2_encodeUint64Field_1_eq, hep] at hfit; dsimp only [bs1]
            simp only [Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_singleton]
              at hfit ⊢; omega
          have hlt_ep : bs1.length < cap.toNat := by have := encodeVarint_length_pos u.epoch; omega
          have hbeq_ep := cap_beq_len_false_of_lt hlt_ep hcap
          rw [vecU8At_expose_one A.repAlloc (sp + 1424#64) cap ptr bs1 hlt_ep hcap hptr, h1432, h1440]
          simp only [sepExists_sepConj_left, sepExists_sepConj_right]
          refine SepWPp.exists_elim fun b1 => ?_
          (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
          apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 451)
          by_vm_steps_safe
            wp_steps
            apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, wp_norm, *])
            intro hinv3
            have hpool3 : A.pool lim st sm2 = A.pool lim st _ :=
              (A.pool_of_vmPreserved hinv3.2).symm
            have hpack_ep :=
              vecU8At_pack_one A.repAlloc (sp + 1424#64) cap ptr bs1 0x08#8 hlt_ep hcap hptr
            rw [h1432, h1440] at hpack_ep
            refine step_send_encode_varint_call_placed A lim st hvarint u.epoch
              (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 8176#64) (bs1 ++ [0x08#8])
              (by simpa only [List.length_append, List.length_singleton] using hfit_ep)
              (F := (vecU8At A.repAlloc (sp + 4840#64) g.f3.cap g.f3.ptr u.dk ∗
                optAuthenticatorPBPinnedAt A.repAlloc g.auth (sp + 4864#64) u.auth ∗
                ((sp + 4912#64) ↦₆₄ u.epoch)) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
              (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) halign
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (hinv_m2.trans hinv3.1)
              (by rw [← hpack_ep, hpool3]; (try sep_ac_rfl)) ?_
            intro sm3 hpcm3 hrunm3 hspm3 htrm3 hcsm3 hinv_m3
            rcases hcsm3 with ⟨hm3_19, _, hm3_21, _, hm3_23, _, hm3_25, _, hm3_27, hm3_28, hm3_fp, _⟩
            simp only [arm64_norm, hm2_19, hm2_21, hm2_23, hm2_25, hm2_27, hm2_28, hm2_fp]
              at hm3_19 hm3_21 hm3_23 hm3_25 hm3_27 hm3_28 hm3_fp
            refine SepWPp.weaken_pre (Entails.of_eq ?_)
              (h8176 sm3 hpcm3 hrunm3 hspm3 htrm3 hm3_19 hm3_21 hm3_23 hm3_25 hm3_27 hm3_28 hm3_fp hinv_m3)
            simp +zetaDelta only [bs2, etv2_encodeUint64Field_1_eq, hep,
              Bool.false_eq_true, ↓reduceIte, List.append_assoc]; (try sep_ac_rfl)
        · (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
          apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 8176#64)
          wp_steps
          apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, wp_norm, *])
          intro hinv3
          have hpool3 : A.pool lim st sm2 = A.pool lim st _ :=
            (A.pool_of_vmPreserved hinv3.2).symm
          refine SepWPp.weaken_pre (Entails.of_eq ?_)
            (h8176 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (hinv_m2.trans hinv3.1))
          rw [hpool3]
          simp +zetaDelta only [bs2, etv2_encodeUint64Field_1_eq, hep,
            ↓reduceIte, List.append_nil]; (try sep_ac_rfl)
      intro sm3 hpcm3 hrunm3 hspm3 htrm3 hx19_3 hx21_3 hx23_3 hx25_3 hx27_3 hx28_3 hfp_3 hinv_3
      set bs3 := bs2 ++ encodeOptMessage ProtoAuthenticator.encodeRaw 2#32 u.auth
      suffices h8208 : ∀ sm4 : State,
          sm4.pc = spqrSendPlacedEntry + 8208#64 → sm4.status = .Running →
          sm4.sp = sp → sm4.trace = s0.trace →
          sm4.readReg64 .x19 = s.readReg64 .x19 → sm4.readReg64 .x21 = s.readReg64 .x21 →
          sm4.readReg64 .x23 = s.readReg64 .x23 → sm4.readReg64 .x25 = w25 →
          sm4.readReg64 .x27 = s.readReg64 .x27 → sm4.readReg64 .x28 = s.readReg64 .x28 →
          sm4.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm4 →
          SepWPp (spqrSendPlacedProg ext) ret sm4
            (((vecU8At A.repAlloc (sp + 4840#64) g.f3.cap g.f3.ptr u.dk ∗
              optAuthenticatorPBPinnedAt A.repAlloc g.auth (sp + 4864#64) u.auth ∗
              ((sp + 4912#64) ↦₆₄ u.epoch)) ∗
              vecU8At A.repAlloc (sp + 1424#64) cap ptr bs3 ∗ A.pool lim st sm4 ∗
              ((sp + 16#64) ↦₆₄ w25) ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
            Q Qp oom by
        cases hauth : u.auth with
        | none =>
          rw [optAuthenticatorPBPinnedAt_eq A.repAlloc g.auth (sp + 4864#64) none]
          simp only [hauth, Option.isSome_none, Bool.not_false] at hcap_auth_beq hcap_auth_bne
          (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
          apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 8208#64)
          wp_steps
          apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, wp_norm, *])
          intro hinv4
          have hpool4 : A.pool lim st sm3 = A.pool lim st _ :=
            (A.pool_of_vmPreserved hinv4.2).symm
          refine SepWPp.weaken_pre (Entails.of_eq ?_)
            (h8208 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (hinv_3.trans hinv4.1))
          rw [← optAuthenticatorPBPinnedAt_eq A.repAlloc g.auth (sp + 4864#64) none, hpool4]
          simp +zetaDelta only [bs3, hauth, encodeOptMessage, List.append_nil]; (try sep_ac_rfl)
        | some auth =>
          rw [optAuthenticatorPBPinnedAt_eq A.repAlloc g.auth (sp + 4864#64) (some auth)]
          simp only [hauth, Option.isSome_some, Bool.not_true] at hcap_auth_beq hcap_auth_bne
          have hfit_auth :
              bs2.length + (encodeMessage ProtoAuthenticator.encodeRaw 2#32 auth).length ≤ cap.toNat := by
            rw [hauth] at hfit; dsimp only [bs2, bs1, encodeOptMessage] at hfit ⊢
            simp only [List.length_append, List.length_singleton] at hfit ⊢; omega
          (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
          apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 454)
          wp_steps
          apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, wp_norm, *])
          intro hinv4
          have hpool4 : A.pool lim st sm3 = A.pool lim st _ :=
            (A.pool_of_vmPreserved hinv4.2).symm
          rw [← optAuthenticatorPBPinnedAt_eq A.repAlloc g.auth (sp + 4864#64) (some auth)]
          have h4704_160 : ((sp + 4096#64) + 608#64) + 160#64 = sp + 4864#64 := by bv_omega
          refine step_send_encode_auth_call_placed A lim st ext hauthEnc
            (sp + 4864#64) (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 8208#64) g.auth auth bs2 hfit_auth
            (F := (vecU8At A.repAlloc (sp + 4840#64) g.f3.cap g.f3.ptr u.dk ∗
              ((sp + 4912#64) ↦₆₄ u.epoch)) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) halign
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
            (by rw [← h4704_160]; simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hinv_3.trans hinv4.1)
            (by dsimp only [optAuthenticatorPBPinnedAt]; rw [hpool4]; (try sep_ac_rfl)) ?_
          intro sm4 hpcm4 hrunm4 hspm4 htrm4 hcsm4 hinv_m4
          rcases hcsm4 with ⟨hm4_19, _, hm4_21, _, hm4_23, _, hm4_25, _, hm4_27, hm4_28, hm4_fp, _⟩
          simp only [arm64_norm, hx19_3, hx21_3, hx23_3, hx25_3, hx27_3, hx28_3, hfp_3]
            at hm4_19 hm4_21 hm4_23 hm4_25 hm4_27 hm4_28 hm4_fp
          refine SepWPp.weaken_pre (Entails.of_eq ?_)
            (h8208 sm4 hpcm4 hrunm4 hspm4 htrm4 hm4_19 hm4_21 hm4_23 hm4_25 hm4_27 hm4_28 hm4_fp hinv_m4)
          simp +zetaDelta only [bs3, hauth, encodeOptMessage, optAuthenticatorPBPinnedAt]
          (try sep_ac_rfl)
      intro sm4 hpcm4 hrunm4 hspm4 htrm4 hx19_4 hx21_4 hx23_4 hx25_4 hx27_4 hx28_4 hfp_4 hinv_4
      refine sepWPp_extract_vecU8At_bounds (A := A.repAlloc) (v := sp + 4840#64)
        (cap := g.f3.cap) (ptr := g.f3.ptr) (bs := u.dk)
        (F := optAuthenticatorPBPinnedAt A.repAlloc g.auth (sp + 4864#64) u.auth ∗
          ((sp + 4912#64) ↦₆₄ u.epoch) ∗
          vecU8At A.repAlloc (sp + 1424#64) cap ptr bs3 ∗ A.pool lim st sm4 ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F)
        (by sep_ac_rfl) fun hdk_le hdk_cap _ => ?_
      have ⟨h4848, h4856⟩ :
          (sp + 4840#64) + 8#64 = sp + 4848#64 ∧
          (sp + 4840#64) + 16#64 = sp + 4856#64 := ⟨by bv_omega, by bv_omega⟩
      rw [vecU8At_eq_header_sep_buf A.repAlloc (sp + 4840#64), vecHeader, h4848, h4856]
      have hdk_lt : u.dk.length < 2 ^ 64 := by omega
      obtain ⟨hbeqz, hbnez⟩ := ofNat_length_beq_zero_of_lt hdk_lt
      cases hemp : u.dk.isEmpty
      · simp only [hemp, Bool.not_false] at hbeqz hbnez
        have hpos_dk : 0 < u.dk.length := List.length_pos_of_ne_nil (List.isEmpty_eq_false_iff.mp hemp)
        have hne_dk : u.dk ≠ [] := List.isEmpty_eq_false_iff.mp hemp
        have henc_eq : encodeBytesField 3#32 u.dk =
            [0x1a#8] ++ encodeVarint (BitVec.ofNat 64 u.dk.length) ++ u.dk := by
          rw [etv2_encodeBytesField_3_eq, hemp]; simp only [Bool.false_eq_true, ↓reduceIte]
        have hfit_all :
            bs3.length + 1 + (encodeVarint (BitVec.ofNat 64 u.dk.length)).length + u.dk.length ≤ cap.toNat := by
          rw [henc_eq] at hfit; dsimp only [bs3, bs2, bs1] at hfit ⊢
          simp only [List.length_append, List.length_singleton] at hfit ⊢; omega
        have hlt_tag : bs3.length < cap.toNat := by omega
        have hcmp_tag := cap_beq_len_false_of_lt hlt_tag hcap
        rw [vecU8At_expose_one A.repAlloc (sp + 1424#64) cap ptr bs3 hlt_tag hcap hptr, h1432, h1440]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        refine SepWPp.exists_elim fun b2 => ?_
        (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
        apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 451)
        by_vm_steps_safe
          wp_steps
          apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, wp_norm, *])
          intro hinv5
          have hpool5 : A.pool lim st sm4 = A.pool lim st _ :=
            (A.pool_of_vmPreserved hinv5.2).symm
          have hpack_tag :=
            vecU8At_pack_one A.repAlloc (sp + 1424#64) cap ptr bs3 0x1a#8 hlt_tag hcap hptr
          rw [h1432, h1440] at hpack_tag
          refine step_send_encode_varint_call_placed A lim st hvarint
            (BitVec.ofNat 64 u.dk.length) (sp + 1424#64) cap ptr sp
            (spqrSendPlacedEntry + 8268#64) (bs3 ++ [0x1a#8])
            (by simp only [List.length_append, List.length_singleton]; omega)
            (F := ((((sp + 4840#64) ↦₆₄ g.f3.cap) ∗ ((sp + 4848#64) ↦₆₄ g.f3.ptr) ∗
              ((sp + 4856#64) ↦₆₄ BitVec.ofNat 64 u.dk.length)) ∗
              vecU8Buf A.repAlloc g.f3.cap g.f3.ptr u.dk ∗
              optAuthenticatorPBPinnedAt A.repAlloc g.auth (sp + 4864#64) u.auth ∗
              ((sp + 4912#64) ↦₆₄ u.epoch)) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) halign
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hinv_4.trans hinv5.1)
            (by rw [← hpack_tag, hpool5]; (try sep_ac_rfl)) ?_
          intro sm5 hpcm5 hrunm5 hspm5 htrm5 hcsm5 hinv_m5
          rcases hcsm5 with ⟨hm5_19, _, hm5_21, _, hm5_23, hm5_24, hm5_25, _, hm5_27, hm5_28, hm5_fp, _⟩
          simp only [arm64_norm, hx19_4, hx21_4, hx23_4, hx27_4, hx28_4, hfp_4]
            at hm5_19 hm5_21 hm5_23 hm5_24 hm5_25 hm5_27 hm5_28 hm5_fp
          let bs4 := (bs3 ++ [0x1a#8]) ++ encodeVarint (BitVec.ofNat 64 u.dk.length)
          have hfit_mc : bs4.length + u.dk.length ≤ cap.toNat := by
            dsimp only [bs4]; simp only [List.length_append, List.length_singleton]; omega
          have hcmp_mc := elem_len_ult_spare_false_of_le hfit_mc hcap
          rw [vecU8At_expose_slice A.repAlloc (sp + 1424#64) cap ptr bs4 u.dk.length
            hfit_mc hcap hptr hpos_dk, h1432, h1440]
          (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
          apply sepWPp_of_sepWP_cs_vm (mid := lsρ "memcpy")
          wp_steps
          apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, wp_norm, *])
          intro hinv6
          have hpool6 : A.pool lim st sm5 = A.pool lim st _ :=
            (A.pool_of_vmPreserved hinv6.2).symm
          refine send2_step_memcpy_slice_placed A lim st ext hmemcpy
            sp cap ptr g.f3.cap g.f3.ptr (spqrSendPlacedEntry + 8308#64) bs4 u.dk hemp hdk_le halign
            (F := (((sp + 4840#64) ↦₆₄ g.f3.cap) ∗ ((sp + 4848#64) ↦₆₄ g.f3.ptr) ∗
              ((sp + 4856#64) ↦₆₄ BitVec.ofNat 64 u.dk.length)) ∗
              optAuthenticatorPBPinnedAt A.repAlloc g.auth (sp + 4864#64) u.auth ∗
              ((sp + 4912#64) ↦₆₄ u.epoch) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            hdk_lt (hinv_m5.trans hinv6.1)
            (by rw [hpool6]; (try sep_ac_rfl)) ?_
          intro sm6 hpcm6 hrunm6 hspm6 htrm6 hcsm6 hinv_m6
          rcases hcsm6 with ⟨hm6_19, _, hm6_21, _, hm6_23, hm6_24, _, hm6_26, hm6_27, hm6_28, hm6_fp, _⟩
          simp only [arm64_norm, hm5_19, hm5_21, hm5_23, hm5_24, hm5_27, hm5_28, hm5_fp]
            at hm6_19 hm6_21 hm6_23 hm6_24 hm6_26 hm6_27 hm6_28 hm6_fp
          (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
          apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 8320#64)
          by_vm_steps_safe
            wp_steps
            apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, wp_norm, *])
            intro hinv7
            have hpool7 : A.pool lim st sm6 = A.pool lim st _ :=
              (A.pool_of_vmPreserved hinv7.2).symm
            have hpack_mc :=
              vecU8At_pack_slice A.repAlloc (sp + 1424#64) cap ptr bs4 u.dk hfit_mc hcap hptr hne_dk
            have hbs_eq :
                bs4 ++ u.dk = bs ++ encodeOptMessage V1State.Unchunked.EkSent.encodeRaw 1#32 (some u) := by
              rw [etv2_encodeOptEkSent_some_eq, henc_eq]
              dsimp only [bs4, bs3, bs2, bs1]; simp only [List.append_assoc]
            rw [h1432, h1440, hbs_eq] at hpack_mc
            refine SepWPp.weaken_pre (Entails.of_eq ?_)
              (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (hinv_m6.trans hinv7.1))
            rw [huc, hpool7]; dsimp only [optEkSentPBPinnedAt, ekSentPBPinnedAt, unchunked3PinnedAt]
            rw [h4840_24, h4840_72, vecU8At_eq_header_sep_buf A.repAlloc (sp + 4840#64), vecHeader,
              h4848, h4856, ← hpack_mc]; (try sep_ac_rfl)
      · simp only [hemp, Bool.not_true] at hbeqz hbnez
        have henc_nil : encodeBytesField 3#32 u.dk = [] := by
          rw [etv2_encodeBytesField_3_eq, hemp]; simp only [↓reduceIte]
        (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
        apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 8320#64)
        wp_steps
        apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv5
        have hpool5 : A.pool lim st sm4 = A.pool lim st _ :=
          (A.pool_of_vmPreserved hinv5.2).symm
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (hinv_4.trans hinv5.1))
        rw [huc, hpool5]; dsimp only [optEkSentPBPinnedAt, ekSentPBPinnedAt, unchunked3PinnedAt]
        rw [h4840_24, h4840_72, vecU8At_eq_header_sep_buf A.repAlloc (sp + 4840#64), vecHeader,
          h4848, h4856, etv2_encodeOptEkSent_some_eq, henc_nil]
        dsimp only [bs3, bs2, bs1]; simp only [List.append_nil, List.append_assoc]; (try sep_ac_rfl)

/-- Step `+8000 .. +6216` for `is = .headerSent v`, threading `A.pool lim st`. -/
theorem step_send_v1_headerSent_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State)) {s0 s : State}
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
    (sp cap ptr w25 : BitVec 64) (g : ChunkedHeaderSentPBGhost) (v : V1State.Chunked.HeaderSent)
    (bs : List (BitVec 8))
    (hv_len : v1StatePBEncodedLen ⟨some (.headerSent v)⟩ < 2 ^ 64)
    (hfit : bs.length + (V1State.InnerState.encode (.headerSent v)).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = spqrSendPlacedEntry + 8000#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace) (hx25 : s.readReg64 .x25 = w25) (hinv0 : StepInv s0 s)
    (hP : P = (chunkedHeaderSentPBPinnedAt A.repAlloc g (sp + 4840#64) v ∗
      vecU8At A.repAlloc (sp + 1424#64) cap ptr bs ∗ A.pool lim st s ∗
      ((sp + 16#64) ↦₆₄ w25) ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = spqrSendPlacedEntry + 6216#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = w25 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((chunkedHeaderSentPBPinnedAt A.repAlloc g (sp + 4840#64) v ∗
          vecU8At A.repAlloc (sp + 1424#64) cap ptr
            (bs ++ V1State.InnerState.encode (.headerSent v)) ∗
          A.pool lim st sm ∗ ((sp + 16#64) ↦₆₄ w25) ∗
          stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  subst hP
  rw [etv2_encodeInnerState_headerSent_eq] at hfit
  simp only [List.length_append, List.length_singleton] at hfit
  have hsub_len : chunkedHeaderSentPBEncodedLen v < 2 ^ 64 := by
    dsimp only [v1StatePBEncodedLen, v1StateInnerPayloadEncodedLen] at hv_len; omega
  have hlt1 : bs.length < cap.toNat := by omega
  have hfit_var : (bs ++ [0x1a#8]).length +
      (encodeVarint (BitVec.ofNat 64 (chunkedHeaderSentPBEncodedLen v))).length ≤ cap.toNat := by
    simp only [List.length_append, List.length_singleton]; omega
  refine sepWPp_extract_vecU8At_bounds (v := sp + 1424#64) (cap := cap) (ptr := ptr) (bs := bs)
    (F := chunkedHeaderSentPBPinnedAt A.repAlloc g (sp + 4840#64) v ∗ A.pool lim st s ∗
      ((sp + 16#64) ↦₆₄ w25) ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F)
    (by sep_ac_rfl) fun _ hcap hptr => ?_
  have hbeq_false := cap_beq_len_false_of_lt hlt1 hcap
  have ⟨h1432, h1440⟩ : (sp + 1424#64) + 8#64 = sp + 1432#64 ∧
      (sp + 1424#64) + 16#64 = sp + 1440#64 := ⟨by bv_omega, by bv_omega⟩
  have ⟨h4704, h4840⟩ : (sp + 4096#64) + 608#64 = sp + 4704#64 ∧
      (sp + 4704#64) + 136#64 = sp + 4840#64 := ⟨by bv_omega, by bv_omega⟩
  rw [vecU8At_expose_one A.repAlloc (sp + 1424#64) cap ptr bs hlt1 hcap hptr, h1432, h1440]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b0 => ?_
  (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
  apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 495)
  by_vm_steps_safe
    wp_steps
    apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv1
    have hpack := vecU8At_pack_one A.repAlloc (sp + 1424#64) cap ptr bs 0x1a#8 hlt1 hcap hptr
    rw [h1432, h1440] at hpack
    refine step_send_chunked_encLen48_call_placed hres ext
      (chunkedHeaderSentPBPinnedAt A.repAlloc) chunkedHeaderSentPBEncodedLen hhsLen
      (sp + 4840#64) sp (spqrSendPlacedEntry + 8052#64) g v hsub_len
      (F := vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs ++ [0x1a#8]) ∗
        A.pool lim st s ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
      (by rw [← h4840, ← h4704]; simp only [arm64_norm, *]) (hinv0.trans hinv1.1)
      (by rw [← hpack]; sep_ac_rfl) ?_
    intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1 hcsm1 hinv_m1 hvm_m1
    rcases hcsm1 with ⟨hm19, hm20, hm21, _, hm23, _, hm25, _, hm27, hm28, hmfp, _⟩
    simp only [arm64_norm, h4704, hx25] at hm19 hm20 hm21 hm23 hm25 hm27 hm28 hmfp
    (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
    apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 451)
    wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv2
    have hpool2 : A.pool lim st s = A.pool lim st _ :=
      (A.pool_of_vmPreserved (hinv1.2.trans (hvm_m1.trans hinv2.2))).symm
    set bs1 := (bs ++ [0x1a#8]) ++ encodeVarint (BitVec.ofNat 64 (chunkedHeaderSentPBEncodedLen v))
    refine step_send_encode_varint_call_placed A lim st hvarint
      (BitVec.ofNat 64 (chunkedHeaderSentPBEncodedLen v))
      (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 8060#64)
      (bs ++ [0x1a#8]) hfit_var
      (F := chunkedHeaderSentPBPinnedAt A.repAlloc g (sp + 4840#64) v ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hinv_m1.trans hinv2.1) (by rw [hpool2]; sep_ac_rfl) ?_
    intro sm2 hpcm2 hrunm2 hspm2 htrm2 hcsm2 hinv_m2
    rcases hcsm2 with ⟨hm2_19, hm2_20, hm2_21, _, hm2_23, _, hm2_25, _, hm2_27, hm2_28, hm2_fp, _⟩
    simp only [arm64_norm, hm19, hm20, hm21, hm23, hm25, hm27, hm28, hmfp]
      at hm2_19 hm2_20 hm2_21 hm2_23 hm2_25 hm2_27 hm2_28 hm2_fp
    dsimp only [chunkedHeaderSentPBPinnedAt]
    have ⟨h4840_80, h4840_136⟩ :
        (sp + 4840#64) + 80#64 = sp + 4920#64 ∧
        (sp + 4840#64) + 136#64 = sp + 4976#64 := ⟨by bv_omega, by bv_omega⟩
    rw [h4840_80, h4840_136]
    have hfit_uc :
        bs1.length + (encodeOptMessage V1State.Unchunked.EkSent.encodeRaw 1#32 v.uc).length ≤
          cap.toNat := by
      dsimp only [bs1]; simp only [List.length_append, List.length_singleton]; omega
    refine send2_step_headerSent_uc_placed hres A lim st ext hekSentLen hvarint hauthEnc hmemcpy
      sp cap ptr w25 g.uc v.uc bs1 hfit_uc halign
      (F := optPolynomialEncoderPBPinnedAt A.repAlloc g.sendingEk (sp + 4920#64) v.sendingEk ∗
        optPolynomialDecoderPBPinnedAt A.repAlloc g.receivingCt1 (sp + 4976#64) v.receivingCt1 ∗ F)
      hpcm2 hrunm2 hspm2 htrm2 hm2_20 hm2_25 hinv_m2 (by dsimp only [bs1]; sep_ac_rfl) ?_
    intro sm3 hpcm3 hrunm3 hspm3 htrm3 hx19_3 hx21_3 hx23_3 hx25_3 hx27_3 hx28_3 hfp_3 hinv_3
    simp only [arm64_norm, hm2_19, hm2_21, hm2_23, hm2_27, hm2_28, hm2_fp]
      at hx19_3 hx21_3 hx23_3 hx27_3 hx28_3 hfp_3
    set bs2 := bs1 ++ encodeOptMessage V1State.Unchunked.EkSent.encodeRaw 1#32 v.uc
    refine sepWPp_extract_pure
      (((optPolyEncCap g.sendingEk v.sendingEk + 1#64 == 0#64) = !v.sendingEk.isSome ∧
        (optPolyEncCap g.sendingEk v.sendingEk + 1#64 != 0#64) = v.sendingEk.isSome) ∧
       ((optPolyDecCap g.receivingCt1 v.receivingCt1 + 1#64 == 0#64) = !v.receivingCt1.isSome ∧
        (optPolyDecCap g.receivingCt1 v.receivingCt1 + 1#64 != 0#64) = v.receivingCt1.isSome))
      (fun R' hm =>
        ⟨optPolynomialEncoderPBPinnedAt_cap_bounds (p := sp + 4920#64)
          (R := optEkSentPBPinnedAt A.repAlloc g.uc (sp + 4840#64) v.uc ∗
            optPolynomialDecoderPBPinnedAt A.repAlloc g.receivingCt1 (sp + 4976#64) v.receivingCt1 ∗
            vecU8At A.repAlloc (sp + 1424#64) cap ptr bs2 ∗ A.pool lim st sm3 ∗
            ((sp + 16#64) ↦₆₄ w25) ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
          (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm),
         optPolynomialDecoderPBPinnedAt_cap_bounds (p := sp + 4976#64)
          (R := optEkSentPBPinnedAt A.repAlloc g.uc (sp + 4840#64) v.uc ∗
            optPolynomialEncoderPBPinnedAt A.repAlloc g.sendingEk (sp + 4920#64) v.sendingEk ∗
            vecU8At A.repAlloc (sp + 1424#64) cap ptr bs2 ∗ A.pool lim st sm3 ∗
            ((sp + 16#64) ↦₆₄ w25) ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
          (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm)⟩)
      fun ⟨⟨hcap_enc_beq, hcap_enc_bne⟩, ⟨hcap_dec_beq, hcap_dec_bne⟩⟩ => ?_
    set bs3 := bs2 ++ encodeOptMessage PolynomialEncoder.encodeRaw 2#32 v.sendingEk
    have ⟨h4920, h4976⟩ :
        (sp + 4704#64) + 216#64 = sp + 4920#64 ∧
        (sp + 4704#64) + 272#64 = sp + 4976#64 := ⟨by bv_omega, by bv_omega⟩
    suffices h8352 : ∀ sm4 : State,
        sm4.pc = spqrSendPlacedEntry + 8352#64 → sm4.status = .Running →
        sm4.sp = sp → sm4.trace = s0.trace →
        sm4.readReg64 .x19 = s.readReg64 .x19 → sm4.readReg64 .x20 = sp + 4704#64 →
        sm4.readReg64 .x21 = s.readReg64 .x21 → sm4.readReg64 .x23 = s.readReg64 .x23 →
        sm4.readReg64 .x25 = w25 → sm4.readReg64 .x27 = s.readReg64 .x27 →
        sm4.readReg64 .x28 = s.readReg64 .x28 → sm4.readReg64 .fp = s.readReg64 .fp →
        StepInv s0 sm4 →
        SepWPp (spqrSendPlacedProg ext) ret sm4
          (((optEkSentPBPinnedAt A.repAlloc g.uc (sp + 4840#64) v.uc ∗
            optPolynomialEncoderPBPinnedAt A.repAlloc g.sendingEk (sp + 4920#64) v.sendingEk ∗
            optPolynomialDecoderPBPinnedAt A.repAlloc g.receivingCt1 (sp + 4976#64) v.receivingCt1) ∗
            vecU8At A.repAlloc (sp + 1424#64) cap ptr bs3 ∗ A.pool lim st sm4 ∗
            ((sp + 16#64) ↦₆₄ w25) ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
          Q Qp oom by
      cases henc : v.sendingEk with
      | none =>
        rw [optPolynomialEncoderPBPinnedAt_eq A.repAlloc g.sendingEk (sp + 4920#64) none]
        simp only [henc, Option.isSome_none, Bool.not_false] at hcap_enc_beq hcap_enc_bne
        (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 8352#64)
        wp_steps; apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *]); intro hinv4
        have hpool4 : A.pool lim st sm3 = A.pool lim st _ := (A.pool_of_vmPreserved hinv4.2).symm
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (h8352 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by rw [← h4704]; simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_3.trans hinv4.1))
        rw [← optPolynomialEncoderPBPinnedAt_eq A.repAlloc g.sendingEk (sp + 4920#64) none, hpool4]
        simp +zetaDelta only [bs3, henc, encodeOptMessage, List.append_nil]; (try sep_ac_rfl)
      | some enc =>
        rw [optPolynomialEncoderPBPinnedAt_eq A.repAlloc g.sendingEk (sp + 4920#64) (some enc)]
        simp only [henc, Option.isSome_some, Bool.not_true] at hcap_enc_beq hcap_enc_bne
        have hfit_enc : bs2.length + (encodeMessage PolynomialEncoder.encodeRaw 2#32 enc).length ≤ cap.toNat := by
          rw [henc] at hfit; simp +zetaDelta only [bs2, bs1, encodeOptMessage, List.length_append, List.length_singleton] at hfit ⊢; omega
        (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 456)
        wp_steps; apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *]); intro hinv4
        have hpool4 : A.pool lim st sm3 = A.pool lim st _ := (A.pool_of_vmPreserved hinv4.2).symm
        rw [← optPolynomialEncoderPBPinnedAt_eq A.repAlloc g.sendingEk (sp + 4920#64) (some enc)]
        refine step_send_encode_polyEncoder_budget_call_placed A lim st ext hpolyEnc
          (sp + 4920#64) (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 8352#64) g.sendingEk enc bs2 hfit_enc
          (F := optEkSentPBPinnedAt A.repAlloc g.uc (sp + 4840#64) v.uc ∗ optPolynomialDecoderPBPinnedAt A.repAlloc g.receivingCt1 (sp + 4976#64) v.receivingCt1 ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by rw [← h4920, ← h4704]; simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hinv_3.trans hinv4.1) (by dsimp only [optPolynomialEncoderPBPinnedAt]; rw [hpool4]; (try sep_ac_rfl)) ?_
        intro sm4 hpcm4 hrunm4 hspm4 htrm4 ⟨hm4_19, hm4_20, hm4_21, _, hm4_23, _, hm4_25, _, hm4_27, hm4_28, hm4_fp, _⟩ hinv_m4
        simp only [arm64_norm, h4704, hx19_3, hx21_3, hx23_3, hx25_3, hx27_3, hx28_3, hfp_3] at hm4_19 hm4_20 hm4_21 hm4_23 hm4_25 hm4_27 hm4_28 hm4_fp
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (h8352 sm4 hpcm4 hrunm4 hspm4 htrm4 hm4_19 hm4_20 hm4_21 hm4_23 hm4_25 hm4_27 hm4_28 hm4_fp hinv_m4)
        simp +zetaDelta only [bs3, henc, encodeOptMessage, optPolynomialEncoderPBPinnedAt]; (try sep_ac_rfl)
    intro sm4 hpcm4 hrunm4 hspm4 htrm4 hx19_4 hx20_4 hx21_4 hx23_4 hx25_4 hx27_4 hx28_4 hfp_4 hinv_4
    cases hdec : v.receivingCt1 with
    | none =>
      rw [optPolynomialDecoderPBPinnedAt_eq A.repAlloc g.receivingCt1 (sp + 4976#64) none]
      simp only [hdec, Option.isSome_none, Bool.not_false] at hcap_dec_beq hcap_dec_bne
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 6216#64)
      wp_steps; apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *]); intro hinv5
      have hpool5 : A.pool lim st sm4 = A.pool lim st _ := (A.pool_of_vmPreserved hinv5.2).symm
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_4.trans hinv5.1))
      rw [← optPolynomialDecoderPBPinnedAt_eq A.repAlloc g.receivingCt1 (sp + 4976#64) none, hpool5, etv2_encodeInnerState_headerSent_eq]
      simp +zetaDelta only [bs3, bs2, bs1, hdec, encodeOptMessage, chunkedHeaderSentPBPinnedAt, List.append_nil, h4840_80, h4840_136, List.append_assoc]; (try sep_ac_rfl)
    | some dec =>
      rw [optPolynomialDecoderPBPinnedAt_eq A.repAlloc g.receivingCt1 (sp + 4976#64) (some dec)]
      simp only [hdec, Option.isSome_some, Bool.not_true] at hcap_dec_beq hcap_dec_bne
      have hfit_dec : bs3.length + (encodeMessage PolynomialDecoder.encodeRaw 3#32 dec).length ≤ cap.toNat := by
        rw [hdec] at hfit; simp +zetaDelta only [bs3, bs2, bs1, encodeOptMessage, List.length_append, List.length_singleton] at hfit ⊢; omega
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *); apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 10352#64)
      wp_steps; apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *]); intro hinv5
      have hpool5 : A.pool lim st sm4 = A.pool lim st _ := (A.pool_of_vmPreserved hinv5.2).symm
      rw [← optPolynomialDecoderPBPinnedAt_eq A.repAlloc g.receivingCt1 (sp + 4976#64) (some dec)]
      refine step_send_tail_10352_polyDec3_placed A lim st ext hpolyDec
        (sp + 4976#64) sp cap ptr g.receivingCt1 dec bs3 hfit_dec halign
        (F := optEkSentPBPinnedAt A.repAlloc g.uc (sp + 4840#64) v.uc ∗ optPolynomialEncoderPBPinnedAt A.repAlloc g.sendingEk (sp + 4920#64) v.sendingEk ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by rw [← h4976]; simp only [arm64_norm, *]) (hinv_4.trans hinv5.1)
        (by dsimp only [optPolynomialDecoderPBPinnedAt]; rw [hpool5]; (try sep_ac_rfl)) ?_
      intro sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp hinv_m5
      simp only [arm64_norm, hx19_4, hx21_4, hx23_4, hx25_4, hx27_4, hx28_4, hfp_4] at hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (hnext sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp hinv_m5)
      rw [etv2_encodeInnerState_headerSent_eq]
      simp +zetaDelta only [bs3, bs2, bs1, hdec, encodeOptMessage, chunkedHeaderSentPBPinnedAt, optPolynomialDecoderPBPinnedAt, h4840_80, h4840_136, List.append_assoc]; (try sep_ac_rfl)

end LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerChunked2PlacedBudgetAux

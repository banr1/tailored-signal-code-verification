/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerChunked2PlacedBudgetAux
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerChunked3aPlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonBudget
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
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
# Budget-Threaded Relocatable Phase 3e (Part 3a Aux): Bytes Helpers & Variant `ct2Sampled` (`idx = 10`)

Proves `VmPreserved` bytes-field stepping helpers and threads `RustCliAllocBudget` through
`V1State::encode_raw` arm `ct2Sampled` (`idx = 10`) in Block `427`.
-/

@[expose] public section

set_option linter.style.longLine false
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerChunked3aPlacedBudgetAux

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
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerChunked2PlacedBudgetAux
  (send2_step_memcpy_slice_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhaseBudget
  (authEncodeExactSpecOf encodeVarintExactSpecOf etvMemcpyRegionSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsPlacedBudget
  (sepWP_done_tpidr sepWP_done_vm sepWPp_of_sepWP_cs_vm)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonBudget
  (etvPolyDecoderExactSpecOf etvPolyEncoderExactSpecOf leafEncLen16Spec)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonPlacedBudget
  (etvPolyDecoderBudgetExactSpecOf etvPolyEncoderBudgetExactSpecOf)

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

/-! ## 1. Shared Stepping Helpers for Bytes Fields -/

theorem send3a_step_memcpy_slice_placed {resStack : Nat} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State)) {s0 s : State}
    (hmemcpy : subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy") etvMemcpyRegionSpec)
    (sp cap ptr srcCap srcPtr ret_pc : BitVec 64) (bs4 srcBs : List (BitVec 8))
    (hemp : srcBs.isEmpty = false) (hsrc_le : srcBs.length ≤ srcCap.toNat) (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = lsρ "memcpy") (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace) (hlr : s.readReg64 .x30 = ret_pc)
    (hx0 : s.readReg64 .x0 = ptr + BitVec.ofNat 64 bs4.length) (hx1 : s.readReg64 .x1 = srcPtr)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 srcBs.length) (hsrc_lt : srcBs.length < 2 ^ 64) (hinv0 : StepInv s0 s)
    (hP : P = ((((sp + 1424#64) ↦₆₄ cap) ∗ ((sp + 1432#64) ↦₆₄ ptr) ∗
        ((sp + 1440#64) ↦₆₄ BitVec.ofNat 64 bs4.length) ∗ A.repAlloc.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs4) ∗
        memRegion (ptr + BitVec.ofNat 64 bs4.length) srcBs.length ∗
        memRegion (ptr + BitVec.ofNat 64 bs4.length + BitVec.ofNat 64 srcBs.length)
          (cap.toNat - bs4.length - srcBs.length)) ∗ vecU8Buf A.repAlloc srcCap srcPtr srcBs ∗
      A.pool lim st s ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        (((((sp + 1424#64) ↦₆₄ cap) ∗ ((sp + 1432#64) ↦₆₄ ptr) ∗
            ((sp + 1440#64) ↦₆₄ BitVec.ofNat 64 bs4.length) ∗ A.repAlloc.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs4) ∗
            ((ptr + BitVec.ofNat 64 bs4.length) ↦ₛ srcBs) ∗
            memRegion (ptr + BitVec.ofNat 64 bs4.length + BitVec.ofNat 64 srcBs.length)
              (cap.toNat - bs4.length - srcBs.length)) ∗ vecU8Buf A.repAlloc srcCap srcPtr srcBs ∗
          A.pool lim st sm ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom :=
  send2_step_memcpy_slice_placed A lim st ext hmemcpy sp cap ptr srcCap srcPtr ret_pc bs4 srcBs
    hemp hsrc_le halign hpc hrun hsp htr hlr hx0 hx1 hx2 hsrc_lt hinv0 hP hnext

theorem send3a_step_bytes_varint_placed {resStack : Nat} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State)) {s0 s : State}
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (bytesToWord64LE : BitVec 8) (sp cap ptr ret_pc : BitVec 64) (bs srcBs : List (BitVec 8))
    (hemp : srcBs.isEmpty = false)
    (hfit : bs.length + 1 + (encodeVarint (BitVec.ofNat 64 srcBs.length)).length + srcBs.length ≤ cap.toNat)
    (hcap : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0) (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = lsmpl.base 451) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace) (hlr : s.readReg64 .x30 = ret_pc)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 srcBs.length) (hx1 : s.readReg64 .x1 = sp + 1424#64)
    (hinv0 : StepInv s0 s)
    (hP : P = ((((sp + 1424#64) ↦₆₄ cap) ∗ ((sp + 1432#64) ↦₆₄ ptr) ∗
        ((sp + 1440#64) ↦₆₄ (BitVec.ofNat 64 bs.length + 1#64)) ∗
        A.repAlloc.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗ ((ptr + BitVec.ofNat 64 bs.length) ↦₈ bytesToWord64LE) ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length + 1#64) (cap.toNat - bs.length - 1)) ∗
      A.pool lim st s ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      let bs_mid := (bs ++ [bytesToWord64LE]) ++ encodeVarint (BitVec.ofNat 64 srcBs.length)
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → StepInv s0 sm → bs_mid.length + srcBs.length ≤ cap.toNat →
      BitVec.ult (cap - BitVec.ofNat 64 bs_mid.length) (BitVec.ofNat 64 srcBs.length) = false →
      SepWPp (spqrSendPlacedProg ext) ret sm
        (((((sp + 1424#64) ↦₆₄ cap) ∗ ((sp + 1432#64) ↦₆₄ ptr) ∗
            ((sp + 1440#64) ↦₆₄ BitVec.ofNat 64 bs_mid.length) ∗
            A.repAlloc.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs_mid) ∗
            memRegion (ptr + BitVec.ofNat 64 bs_mid.length) srcBs.length ∗
            memRegion (ptr + BitVec.ofNat 64 bs_mid.length + BitVec.ofNat 64 srcBs.length)
              (cap.toNat - bs_mid.length - srcBs.length)) ∗
          A.pool lim st sm ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  subst hP
  have ⟨h1432, h1440⟩ : (sp + 1424#64) + 8#64 = sp + 1432#64 ∧ (sp + 1424#64) + 16#64 = sp + 1440#64 :=
    ⟨by bv_omega, by bv_omega⟩
  have hlt_tag : bs.length < cap.toNat := by omega
  have hpack_tag := vecU8At_pack_one A.repAlloc (sp + 1424#64) cap ptr bs bytesToWord64LE hlt_tag hcap hptr
  rw [h1432, h1440] at hpack_tag
  refine step_send_encode_varint_call_placed A lim st hvarint (BitVec.ofNat 64 srcBs.length)
    (sp + 1424#64) cap ptr sp ret_pc (bs ++ [bytesToWord64LE])
    (by simp only [List.length_append, List.length_singleton]; omega) (F := F)
    hpc hrun hsp halign htr hlr hx0 hx1 hinv0 (by rw [← hpack_tag]; (try sep_ac_rfl)) ?_
  intro sm hpcm hrunm hspm htrm hcsm hinvm
  let bs_mid := (bs ++ [bytesToWord64LE]) ++ encodeVarint (BitVec.ofNat 64 srcBs.length)
  have hpos : 0 < srcBs.length := List.length_pos_of_ne_nil (List.isEmpty_eq_false_iff.mp hemp)
  have hfit_mc : bs_mid.length + srcBs.length ≤ cap.toNat := by
    dsimp only [bs_mid]; simp only [List.length_append, List.length_singleton]; omega
  have hcmp_mc := elem_len_ult_spare_false_of_le hfit_mc hcap
  refine SepWPp.weaken_pre
    (Entails.of_eq (by
      rw [vecU8At_expose_slice A.repAlloc (sp + 1424#64) cap ptr bs_mid srcBs.length hfit_mc hcap hptr hpos,
        h1432, h1440]; (try sep_ac_rfl)))
    (hnext sm hpcm hrunm hspm htrm hcsm hinvm hfit_mc hcmp_mc)

/-! ## 2. Variant `idx = 10`: `.ct2Sampled` (`+8896 .. +10296`) -/

theorem step_send_v1_ct2Sampled_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State)) {s0 s : State}
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
    (sp cap ptr w25 : BitVec 64) (g : PolynomialEncoderPBGhost × Unchunked2PBGhost)
    (v : V1State.Chunked.Ct2Sampled) (bs : List (BitVec 8))
    (hv_len : v1StatePBEncodedLen ⟨some (.ct2Sampled v)⟩ < 2 ^ 64)
    (hfit : bs.length + (V1State.InnerState.encode (.ct2Sampled v)).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = spqrSendPlacedEntry + 8896#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace) (hinv0 : StepInv s0 s)
    (hP : P = ((optPolynomialEncoderPBPinnedAt A.repAlloc g.1 (sp + 4840#64) v.sendingCt2 ∗
        optCt2SentPBPinnedAt A.repAlloc g.2 (sp + 4896#64) v.uc) ∗
      ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A.repAlloc (sp + 1424#64) cap ptr bs ∗
      A.pool lim st s ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = spqrSendPlacedEntry + 6216#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = w25 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        (((optPolynomialEncoderPBPinnedAt A.repAlloc g.1 (sp + 4840#64) v.sendingCt2 ∗
            optCt2SentPBPinnedAt A.repAlloc g.2 (sp + 4896#64) v.uc) ∗
          ((sp + 16#64) ↦₆₄ w25) ∗
          vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs ++ V1State.InnerState.encode (.ct2Sampled v)) ∗
          A.pool lim st sm ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  subst hP; rcases v with ⟨uc, sendingCt2⟩
  rw [etv3_encodeInnerState_ct2Sampled_eq] at hfit; simp only [List.length_append, List.length_singleton] at hfit
  have hsub_len : v1StateInnerPayloadEncodedLen (.ct2Sampled ⟨uc, sendingCt2⟩) < 2 ^ 64 := by
    dsimp only [v1StatePBEncodedLen] at hv_len; omega
  have hlt1 : bs.length < cap.toNat := by omega
  have hfit_var : (bs ++ [0x5a#8]).length +
      (encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ct2Sampled ⟨uc, sendingCt2⟩)))).length ≤
      cap.toNat := by
    simp only [List.length_append, List.length_singleton]; omega
  refine sepWPp_extract_vecU8At_bounds (v := sp + 1424#64) (cap := cap) (ptr := ptr) (bs := bs)
    (F := optPolynomialEncoderPBPinnedAt A.repAlloc g.1 (sp + 4840#64) sendingCt2 ∗
      optCt2SentPBPinnedAt A.repAlloc g.2 (sp + 4896#64) uc ∗
      ((sp + 16#64) ↦₆₄ w25) ∗ A.pool lim st s ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F)
    (by sep_ac_rfl) fun _ hcap hptr => ?_
  refine sepWPp_extract_pure
    (((optCt2SentCap g.2 uc + 2#64 == 0#64) = !uc.isSome ∧
      (optCt2SentCap g.2 uc + 2#64 != 0#64) = uc.isSome) ∧
     ((optPolyEncCap g.1 sendingCt2 + 1#64 == 0#64) = !sendingCt2.isSome ∧
      (optPolyEncCap g.1 sendingCt2 + 1#64 != 0#64) = sendingCt2.isSome))
    (fun R' hm => ⟨optCt2SentPBPinnedAt_cap_bounds (p := sp + 4896#64)
        (R := optPolynomialEncoderPBPinnedAt A.repAlloc g.1 (sp + 4840#64) sendingCt2 ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A.repAlloc (sp + 1424#64) cap ptr bs ∗
          A.pool lim st s ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm),
      optPolynomialEncoderPBPinnedAt_cap_bounds (p := sp + 4840#64)
        (R := optCt2SentPBPinnedAt A.repAlloc g.2 (sp + 4896#64) uc ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A.repAlloc (sp + 1424#64) cap ptr bs ∗
          A.pool lim st s ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm)⟩)
    fun ⟨⟨hcap_uc_beq, hcap_uc_bne⟩, ⟨hcap_enc_beq, hcap_enc_bne⟩⟩ => ?_
  have hbeq_false := cap_beq_len_false_of_lt hlt1 hcap
  have ⟨h1432, h1440⟩ : (sp + 1424#64) + 8#64 = sp + 1432#64 ∧ (sp + 1424#64) + 16#64 = sp + 1440#64 :=
    ⟨by bv_omega, by bv_omega⟩
  have hpack := vecU8At_pack_one A.repAlloc (sp + 1424#64) cap ptr bs 0x5a#8 hlt1 hcap hptr
  rw [h1432, h1440] at hpack
  suffices h9424 : ∀ sm1 : State,
      sm1.pc = spqrSendPlacedEntry + 9424#64 → sm1.status = .Running → sm1.sp = sp → sm1.trace = s0.trace →
      sm1.readReg64 .x19 = s.readReg64 .x19 → sm1.readReg64 .x20 = sp + 4704#64 →
      sm1.readReg64 .x21 = s.readReg64 .x21 → sm1.readReg64 .x22 = optCt2SentCap g.2 uc →
      sm1.readReg64 .x23 = s.readReg64 .x23 →
      sm1.readReg64 .x25 = BitVec.ofNat 64 (optCt2SentPBFieldEncodedLen uc) →
      sm1.readReg64 .x27 = s.readReg64 .x27 → sm1.readReg64 .x28 = s.readReg64 .x28 →
      sm1.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm1 →
      SepWPp (spqrSendPlacedProg ext) ret sm1
        (((optPolynomialEncoderPBPinnedAt A.repAlloc g.1 (sp + 4840#64) sendingCt2 ∗
            optCt2SentPBPinnedAt A.repAlloc g.2 (sp + 4896#64) uc) ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs ++ [0x5a#8]) ∗
          A.pool lim st sm1 ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom by
    rw [vecU8At_expose_one A.repAlloc (sp + 1424#64) cap ptr bs hlt1 hcap hptr, h1432, h1440]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b0 => ?_
    cases uc with
    | none =>
      rw [optCt2SentPBPinnedAt_eq A.repAlloc g.2 (sp + 4896#64) none]
      simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
      apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 9424#64)
      by_vm_steps_safe
        wp_steps
        apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv1
        have hpool1 : A.pool lim st s = A.pool lim st _ := (A.pool_of_vmPreserved hinv1.2).symm
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (h9424 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *])
            (by simp only [optCt2SentPBFieldEncodedLen, arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (hinv0.trans hinv1.1))
        rw [← optCt2SentPBPinnedAt_eq A.repAlloc g.2 (sp + 4896#64) none, ← hpack, hpool1]; (try sep_ac_rfl)
    | some u =>
      rw [optCt2SentPBPinnedAt_eq A.repAlloc g.2 (sp + 4896#64) (some u)]
      simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      have ⟨hu_fit, hopt_u_lt⟩ : ct2SentPBEncodedLen u < 2 ^ 64 ∧ optCt2SentPBFieldEncodedLen (some u) < 2 ^ 64 :=
        ⟨by dsimp only [v1StateInnerPayloadEncodedLen, optCt2SentPBFieldEncodedLen] at hsub_len; omega,
         by dsimp only [v1StateInnerPayloadEncodedLen] at hsub_len; omega⟩
      have hvar_u_lt : varintLen (BitVec.ofNat 64 (ct2SentPBEncodedLen u)) < optCt2SentPBFieldEncodedLen (some u) := by
        dsimp only [optCt2SentPBFieldEncodedLen]; omega
      have ⟨⟨_, _, _, _, _⟩, hult_u, hopt_u_eq⟩ :=
        (⟨cmp_ls_false_of_lt hvar_u_lt hopt_u_lt, ult_of_lt_of_fit hvar_u_lt hopt_u_lt,
          etv3_bv_optCt2Sent_some_eq u⟩ : _ ∧ _ ∧ _)
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
      apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 470)
      by_vm_steps_safe
        wp_steps
        apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv1
        rw [← optCt2SentPBPinnedAt_eq A.repAlloc g.2 (sp + 4896#64) (some u)]
        refine step_send_leaf_encLen16_call_placed hres ext (ct2SentPBPinnedAt A.repAlloc)
          ct2SentPBEncodedLen hct2Len (sp + 4896#64) sp (spqrSendPlacedEntry + 9384#64) g.2 u hu_fit
          (F := optPolynomialEncoderPBPinnedAt A.repAlloc g.1 (sp + 4840#64) sendingCt2 ∗
            ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs ++ [0x5a#8]) ∗
            A.pool lim st s ∗ F)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
          (hinv0.trans hinv1.1) (by rw [← hpack]; dsimp only [optCt2SentPBPinnedAt]; (try sep_ac_rfl)) ?_
        intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1 ⟨hm19, hm20, hm21, hm22, hm23, _, _, _, hm27, hm28, hmfp, _⟩
          hinv_m1 hvm_m1
        simp only [arm64_norm] at hm19 hm20 hm21 hm22 hm23 hm27 hm28 hmfp
        (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
        apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 9424#64)
        wp_steps
        apply sepWP_done_vm (by simp only [arm64_norm, Bool.false_eq_true, ↓reduceIte, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *])
        intro hinv2
        have hpool2 : A.pool lim st s = A.pool lim st _ :=
          (A.pool_of_vmPreserved (hinv1.2.trans (hvm_m1.trans hinv2.2))).symm
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (h9424 _ (by simp only [arm64_norm, Bool.false_eq_true, ↓reduceIte, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hinv_m1.trans hinv2.1))
        dsimp only [optCt2SentPBPinnedAt]; rw [hpool2]; (try sep_ac_rfl)
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx25_1 hx27_1 hx28_1 hfp_1 hinv_1
  suffices h10128 : ∀ sm2 : State,
      sm2.pc = spqrSendPlacedEntry + 10128#64 → sm2.status = .Running → sm2.sp = sp → sm2.trace = s0.trace →
      sm2.readReg64 .x8 = BitVec.ofNat 64 (optPolynomialEncoderPBFieldEncodedLen sendingCt2) →
      sm2.readReg64 .x19 = s.readReg64 .x19 → sm2.readReg64 .x20 = sp + 4704#64 →
      sm2.readReg64 .x21 = s.readReg64 .x21 → sm2.readReg64 .x22 = optCt2SentCap g.2 uc →
      sm2.readReg64 .x23 = s.readReg64 .x23 → sm2.readReg64 .x24 = optPolyEncCap g.1 sendingCt2 →
      sm2.readReg64 .x25 = BitVec.ofNat 64 (optCt2SentPBFieldEncodedLen uc) →
      sm2.readReg64 .x27 = s.readReg64 .x27 → sm2.readReg64 .x28 = s.readReg64 .x28 →
      sm2.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm2 →
      SepWPp (spqrSendPlacedProg ext) ret sm2
        (((optPolynomialEncoderPBPinnedAt A.repAlloc g.1 (sp + 4840#64) sendingCt2 ∗
            optCt2SentPBPinnedAt A.repAlloc g.2 (sp + 4896#64) uc) ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs ++ [0x5a#8]) ∗
          A.pool lim st sm2 ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom by
    cases sendingCt2 with
    | none =>
      rw [optPolynomialEncoderPBPinnedAt_eq A.repAlloc g.1 (sp + 4840#64) none]
      simp only [Option.isSome_none, Bool.not_false] at hcap_enc_beq hcap_enc_bne
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
      apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 10128#64)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv2
      have hpool2 : A.pool lim st sm1 = A.pool lim st _ := (A.pool_of_vmPreserved hinv2.2).symm
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h10128 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [optPolynomialEncoderPBFieldEncodedLen, arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (hinv_1.trans hinv2.1))
      rw [← optPolynomialEncoderPBPinnedAt_eq A.repAlloc g.1 (sp + 4840#64) none, hpool2]; (try sep_ac_rfl)
    | some enc =>
      rw [optPolynomialEncoderPBPinnedAt_eq A.repAlloc g.1 (sp + 4840#64) (some enc)]
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
      rw [← optPolynomialEncoderPBPinnedAt_eq A.repAlloc g.1 (sp + 4840#64) (some enc)]
      refine step_send_leaf_encLen16_call_placed hres ext (polynomialEncoderPBPinnedAt A.repAlloc)
        polynomialEncoderPBEncodedLen hpolyEncLen (sp + 4840#64) sp (spqrSendPlacedEntry + 9444#64) g.1 enc henc_fit
        (F := optCt2SentPBPinnedAt A.repAlloc g.2 (sp + 4896#64) uc ∗ ((sp + 16#64) ↦₆₄ w25) ∗
          vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs ++ [0x5a#8]) ∗ A.pool lim st sm1 ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (hinv_1.trans hinv2.1) (by dsimp only [optPolynomialEncoderPBPinnedAt]; (try sep_ac_rfl)) ?_
      intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx0m2 ⟨hm2_19, hm2_20, hm2_21, hm2_22, hm2_23, hm2_24, hm2_25, _, hm2_27, hm2_28, hm2_fp, _⟩
        hinv_m2 hvm_m2
      simp only [arm64_norm, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx25_1, hx27_1, hx28_1, hfp_1]
        at hm2_19 hm2_20 hm2_21 hm2_22 hm2_23 hm2_24 hm2_25 hm2_27 hm2_28 hm2_fp
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
      apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 10128#64)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv3
      have hpool3 : A.pool lim st sm1 = A.pool lim st _ :=
        (A.pool_of_vmPreserved (hinv2.2.trans (hvm_m2.trans hinv3.2))).symm
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h10128 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_m2.trans hinv3.1))
      dsimp only [optPolynomialEncoderPBPinnedAt]; rw [hpool3]; (try sep_ac_rfl)
  intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx8_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx27_2 hx28_2 hfp_2 hinv_2
  have ⟨hadd_sum, hult_sum, hule_sum, hult_sum2, hule_sum2⟩ := adds_no_overflow_of_eq
    (a := optPolynomialEncoderPBFieldEncodedLen sendingCt2) (b := optCt2SentPBFieldEncodedLen uc)
    (c := v1StateInnerPayloadEncodedLen (.ct2Sampled ⟨uc, sendingCt2⟩)) rfl hsub_len
  (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
  apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 451)
  wp_steps
  apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, wp_norm, *])
  intro hinv3
  have hpool3 : A.pool lim st sm2 = A.pool lim st _ := (A.pool_of_vmPreserved hinv3.2).symm
  set bs1 := (bs ++ [0x5a#8]) ++
    encodeVarint (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ct2Sampled ⟨uc, sendingCt2⟩)))
  refine step_send_encode_varint_call_placed A lim st hvarint
    (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen (.ct2Sampled ⟨uc, sendingCt2⟩)))
    (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 10144#64) (bs ++ [0x5a#8]) hfit_var
    (F := (optPolynomialEncoderPBPinnedAt A.repAlloc g.1 (sp + 4840#64) sendingCt2 ∗
      optCt2SentPBPinnedAt A.repAlloc g.2 (sp + 4896#64) uc) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_2.trans hinv3.1)
    (by rw [hpool3]; (try sep_ac_rfl)) ?_
  intro sm3 hpcm3 hrunm3 hspm3 htrm3 ⟨hm3_19, hm3_20, hm3_21, hm3_22, hm3_23, hm3_24, _, _, hm3_27, hm3_28, hm3_fp, _⟩
    hinv_m3
  simp only [arm64_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx27_2, hx28_2, hfp_2]
    at hm3_19 hm3_20 hm3_21 hm3_22 hm3_23 hm3_24 hm3_27 hm3_28 hm3_fp
  set bs2 := bs1 ++ encodeOptMessage V1State.Unchunked.Ct2Sent.encodeRaw 1#32 uc
  suffices h10280 : ∀ sm4 : State,
      sm4.pc = spqrSendPlacedEntry + 10280#64 → sm4.status = .Running → sm4.sp = sp → sm4.trace = s0.trace →
      sm4.readReg64 .x19 = s.readReg64 .x19 → sm4.readReg64 .x20 = sp + 4704#64 →
      sm4.readReg64 .x21 = s.readReg64 .x21 → sm4.readReg64 .x23 = s.readReg64 .x23 →
      sm4.readReg64 .x24 = optPolyEncCap g.1 sendingCt2 → sm4.readReg64 .x25 = w25 →
      sm4.readReg64 .x27 = s.readReg64 .x27 → sm4.readReg64 .x28 = s.readReg64 .x28 →
      sm4.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm4 →
      SepWPp (spqrSendPlacedProg ext) ret sm4
        (((optPolynomialEncoderPBPinnedAt A.repAlloc g.1 (sp + 4840#64) sendingCt2 ∗
            optCt2SentPBPinnedAt A.repAlloc g.2 (sp + 4896#64) uc) ∗
          ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A.repAlloc (sp + 1424#64) cap ptr bs2 ∗
          A.pool lim st sm4 ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom by
    cases uc with
    | none =>
      simp only [Option.isSome_none, Bool.not_false] at hcap_uc_beq hcap_uc_bne
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
      apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 10280#64)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv4
      have hpool4 : A.pool lim st sm3 = A.pool lim st _ := (A.pool_of_vmPreserved hinv4.2).symm
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (h10280 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hinv_m3.trans hinv4.1))
      rw [hpool4]; simp +zetaDelta only [bs2, bs1, encodeOptMessage, List.append_nil]; (try sep_ac_rfl)
    | some u =>
      simp only [Option.isSome_some, Bool.not_true] at hcap_uc_beq hcap_uc_bne
      rw [etv3_encodeOptCt2Sent_some_eq] at hfit; simp only [List.length_append, List.length_singleton] at hfit
      have hu_lt : ct2SentPBEncodedLen u < 2 ^ 64 := by
        dsimp only [v1StateInnerPayloadEncodedLen, optCt2SentPBFieldEncodedLen] at hsub_len; omega
      have hlt_tag : bs1.length < cap.toNat := by
        dsimp only [bs1]; simp only [List.length_append, List.length_singleton]; omega
      have hbeq_tag := cap_beq_len_false_of_lt hlt_tag hcap
      rw [vecU8At_expose_one A.repAlloc (sp + 1424#64) cap ptr bs1 hlt_tag hcap hptr, h1432, h1440]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b1 => ?_
      (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
      apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 470)
      by_vm_steps_safe
        wp_steps
        apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv4
        have hpack_tag := vecU8At_pack_one A.repAlloc (sp + 1424#64) cap ptr bs1 0x0a#8 hlt_tag hcap hptr
        rw [h1432, h1440] at hpack_tag
        refine step_send_leaf_encLen16_call_placed hres ext (ct2SentPBPinnedAt A.repAlloc)
          ct2SentPBEncodedLen hct2Len (sp + 4896#64) sp (spqrSendPlacedEntry + 10200#64) g.2 u hu_lt
          (F := optPolynomialEncoderPBPinnedAt A.repAlloc g.1 (sp + 4840#64) sendingCt2 ∗
            ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs1 ++ [0x0a#8]) ∗
            A.pool lim st sm3 ∗ F)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
          (hinv_m3.trans hinv4.1) (by rw [← hpack_tag]; dsimp only [optCt2SentPBPinnedAt]; (try sep_ac_rfl)) ?_
        intro sm4 hpcm4 hrunm4 hspm4 htrm4 hx0m4
          ⟨hm4_19, hm4_20, hm4_21, hm4_22, hm4_23, hm4_24, hm4_25, _, hm4_27, hm4_28, hm4_fp, _⟩ hinv_m4 hvm_m4
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
        set bs_u1 := (bs1 ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 (ct2SentPBEncodedLen u))
        have hfit_uvar : (bs1 ++ [0x0a#8]).length +
            (encodeVarint (BitVec.ofNat 64 (ct2SentPBEncodedLen u))).length ≤ cap.toNat := by
          dsimp only [bs1]; simp only [List.length_append, List.length_singleton]; omega
        refine step_send_encode_varint_call_placed A lim st hvarint
          (BitVec.ofNat 64 (ct2SentPBEncodedLen u)) (sp + 1424#64) cap ptr sp
          (spqrSendPlacedEntry + 10208#64) (bs1 ++ [0x0a#8]) hfit_uvar
          (F := optPolynomialEncoderPBPinnedAt A.repAlloc g.1 (sp + 4840#64) sendingCt2 ∗
            ct2SentPBPinnedAt A.repAlloc g.2 (sp + 4896#64) u ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hinv_m4.trans hinv5.1) (by rw [hpool5]; (try sep_ac_rfl)) ?_
        intro sm5 hpcm5 hrunm5 hspm5 htrm5
          ⟨hm5_19, hm5_20, hm5_21, hm5_22, hm5_23, hm5_24, hm5_25, _, hm5_27, hm5_28, hm5_fp, _⟩ hinv_m5
        simp only [arm64_norm, hm4_19, hm4_20, hm4_21, hm4_22, hm4_23, hm4_24, hm4_25, hm4_27, hm4_28, hm4_fp]
          at hm5_19 hm5_20 hm5_21 hm5_22 hm5_23 hm5_24 hm5_25 hm5_27 hm5_28 hm5_fp
        dsimp only [ct2SentPBPinnedAt, unchunked2PinnedAt]
        have h4896_48 : (sp + 4896#64) + 0x30#64 = sp + 4944#64 := by bv_omega
        rw [h4896_48]
        refine sepWPp_extract_pure
          ((optAuthCap g.2 u.auth + 1#64 == 0#64) = !u.auth.isSome ∧
           (optAuthCap g.2 u.auth + 1#64 != 0#64) = u.auth.isSome)
          (fun R' hm => etv2_optAuth_cap_bounds (A := A.repAlloc) (p := sp + 4896#64)
            (R := optPolynomialEncoderPBPinnedAt A.repAlloc g.1 (sp + 4840#64) sendingCt2 ∗
              ((sp + 4944#64) ↦₆₄ u.epoch) ∗ ((sp + 16#64) ↦₆₄ w25) ∗
              vecU8At A.repAlloc (sp + 1424#64) cap ptr bs_u1 ∗
              A.pool lim st sm5 ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
            (Satisfies.mono (Entails.of_eq (by dsimp only [bs_u1]; (try sep_ac_rfl))) hm))
          fun ⟨hcap_auth_beq, hcap_auth_bne⟩ => ?_
        set bs_u2 := bs_u1 ++ encodeUint64Field 1#32 u.epoch
        suffices h10260 : ∀ sm6 : State,
            sm6.pc = spqrSendPlacedEntry + 10260#64 → sm6.status = .Running → sm6.sp = sp → sm6.trace = s0.trace →
            sm6.readReg64 .x19 = s.readReg64 .x19 → sm6.readReg64 .x20 = sp + 4704#64 →
            sm6.readReg64 .x21 = s.readReg64 .x21 → sm6.readReg64 .x22 = optCt2SentCap g.2 (some u) →
            sm6.readReg64 .x23 = s.readReg64 .x23 → sm6.readReg64 .x24 = optPolyEncCap g.1 sendingCt2 →
            sm6.readReg64 .x25 = w25 → sm6.readReg64 .x27 = s.readReg64 .x27 →
            sm6.readReg64 .x28 = s.readReg64 .x28 → sm6.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm6 →
            SepWPp (spqrSendPlacedProg ext) ret sm6
              (((optPolynomialEncoderPBPinnedAt A.repAlloc g.1 (sp + 4840#64) sendingCt2 ∗
                  optAuthenticatorPBPinnedAt A.repAlloc g.2 (sp + 4896#64) u.auth ∗ ((sp + 4944#64) ↦₆₄ u.epoch)) ∗
                ((sp + 16#64) ↦₆₄ w25) ∗ vecU8At A.repAlloc (sp + 1424#64) cap ptr bs_u2 ∗
                A.pool lim st sm6 ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
              Q Qp oom by
          cases hep : u.epoch == 0#64
          · have hfit_ep : bs_u1.length + 1 + (encodeVarint u.epoch).length ≤ cap.toNat := by
              rw [etv2_encodeUint64Field_1_eq, hep] at hfit; dsimp only [bs_u1, bs1]
              simp only [Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_singleton] at hfit ⊢; omega
            have hlt_ep : bs_u1.length < cap.toNat := by have := encodeVarint_length_pos u.epoch; omega
            have hbeq_ep := cap_beq_len_false_of_lt hlt_ep hcap
            rw [vecU8At_expose_one A.repAlloc (sp + 1424#64) cap ptr bs_u1 hlt_ep hcap hptr, h1432, h1440]
            simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun b2 => ?_
            (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
            apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 451)
            by_vm_steps_safe
              wp_steps
              apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, wp_norm, *])
              intro hinv6
              have hpool6 : A.pool lim st sm5 = A.pool lim st _ := (A.pool_of_vmPreserved hinv6.2).symm
              have hpack_ep := vecU8At_pack_one A.repAlloc (sp + 1424#64) cap ptr bs_u1 0x08#8 hlt_ep hcap hptr
              rw [h1432, h1440] at hpack_ep
              refine step_send_encode_varint_call_placed A lim st hvarint u.epoch
                (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 10260#64) (bs_u1 ++ [0x08#8])
                (by simpa only [List.length_append, List.length_singleton] using hfit_ep)
                (F := (optPolynomialEncoderPBPinnedAt A.repAlloc g.1 (sp + 4840#64) sendingCt2 ∗
                  optAuthenticatorPBPinnedAt A.repAlloc g.2 (sp + 4896#64) u.auth ∗
                  ((sp + 4944#64) ↦₆₄ u.epoch)) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
                (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (hinv_m5.trans hinv6.1) (by rw [← hpack_ep, hpool6]; (try sep_ac_rfl)) ?_
              intro sm6 hpcm6 hrunm6 hspm6 htrm6
                ⟨hm6_19, hm6_20, hm6_21, hm6_22, hm6_23, hm6_24, hm6_25, _, hm6_27, hm6_28, hm6_fp, _⟩ hinv_m6
              simp only [arm64_norm, hm5_19, hm5_20, hm5_21, hm5_22, hm5_23, hm5_24, hm5_25, hm5_27, hm5_28, hm5_fp]
                at hm6_19 hm6_20 hm6_21 hm6_22 hm6_23 hm6_24 hm6_25 hm6_27 hm6_28 hm6_fp
              refine SepWPp.weaken_pre (Entails.of_eq ?_)
                (h10260 sm6 hpcm6 hrunm6 hspm6 htrm6 hm6_19 hm6_20 hm6_21 hm6_22 hm6_23 hm6_24 hm6_25
                  hm6_27 hm6_28 hm6_fp hinv_m6)
              simp +zetaDelta only [bs_u2, etv2_encodeUint64Field_1_eq, hep, Bool.false_eq_true, ↓reduceIte,
                List.append_assoc]; (try sep_ac_rfl)
          · (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
            apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 10260#64)
            wp_steps
            apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, wp_norm, *])
            intro hinv6
            have hpool6 : A.pool lim st sm5 = A.pool lim st _ := (A.pool_of_vmPreserved hinv6.2).symm
            refine SepWPp.weaken_pre (Entails.of_eq ?_)
              (h10260 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (hinv_m5.trans hinv6.1))
            rw [hpool6]; simp +zetaDelta only [bs_u2, etv2_encodeUint64Field_1_eq, hep, ↓reduceIte, List.append_nil]
            (try sep_ac_rfl)
        intro sm6 hpcm6 hrunm6 hspm6 htrm6 hx19_6 hx20_6 hx21_6 hx22_6 hx23_6 hx24_6 hx25_6 hx27_6 hx28_6 hfp_6 hinv_6
        have hx22_eq : optCt2SentCap g.2 (some u) = optAuthCap g.2 u.auth := rfl; rw [hx22_eq] at hx22_6
        cases hauth : u.auth with
        | none =>
          simp only [hauth, Option.isSome_none, Bool.not_false] at hcap_auth_beq hcap_auth_bne
          (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
          apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 10280#64)
          wp_steps
          apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, wp_norm, *])
          intro hinv7
          have hpool7 : A.pool lim st sm6 = A.pool lim st _ := (A.pool_of_vmPreserved hinv7.2).symm
          refine SepWPp.weaken_pre (Entails.of_eq ?_)
            (h10280 _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (hinv_6.trans hinv7.1))
          dsimp only [bs2]; rw [hpool7, etv3_encodeOptCt2Sent_some_eq]
          simp +zetaDelta only [bs_u2, bs_u1, bs1, hauth, encodeOptMessage, optCt2SentPBPinnedAt,
            ct2SentPBPinnedAt, unchunked2PinnedAt, h4896_48, List.append_nil, List.append_assoc]
          (try sep_ac_rfl)
        | some auth =>
          simp only [hauth, Option.isSome_some, Bool.not_true] at hcap_auth_beq hcap_auth_bne
          have hfit_auth : bs_u2.length + (encodeMessage ProtoAuthenticator.encodeRaw 2#32 auth).length ≤ cap.toNat := by
            rw [hauth] at hfit; dsimp only [bs_u2, bs_u1, bs1, encodeOptMessage] at hfit ⊢
            simp only [List.length_append, List.length_singleton] at hfit ⊢; omega
          (try dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *)
          apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 454)
          wp_steps
          apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, wp_norm, *])
          intro hinv7
          have hpool7 : A.pool lim st sm6 = A.pool lim st _ := (A.pool_of_vmPreserved hinv7.2).symm
          refine step_send_encode_auth_call_placed A lim st ext hauthEnc
            (sp + 4896#64) (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 10280#64) g.2 auth bs_u2 hfit_auth
            (F := (optPolynomialEncoderPBPinnedAt A.repAlloc g.1 (sp + 4840#64) sendingCt2 ∗
              ((sp + 4944#64) ↦₆₄ u.epoch)) ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hinv_6.trans hinv7.1)
            (by rw [hpool7]; simp only [hauth, optAuthenticatorPBPinnedAt]; (try sep_ac_rfl)) ?_
          intro sm7 hpcm7 hrunm7 hspm7 htrm7
            ⟨hm7_19, hm7_20, hm7_21, _, hm7_23, hm7_24, hm7_25, _, hm7_27, hm7_28, hm7_fp, _⟩ hinv_m7
          simp only [arm64_norm, hx19_6, hx20_6, hx21_6, hx23_6, hx24_6, hx25_6, hx27_6, hx28_6, hfp_6]
            at hm7_19 hm7_20 hm7_21 hm7_23 hm7_24 hm7_25 hm7_27 hm7_28 hm7_fp
          refine SepWPp.weaken_pre (Entails.of_eq ?_)
            (h10280 sm7 hpcm7 hrunm7 hspm7 htrm7 hm7_19 hm7_20 hm7_21 hm7_23 hm7_24 hm7_25
              hm7_27 hm7_28 hm7_fp hinv_m7)
          dsimp only [bs2]; rw [etv3_encodeOptCt2Sent_some_eq]
          simp +zetaDelta only [bs_u2, bs_u1, bs1, hauth, encodeOptMessage, optCt2SentPBPinnedAt,
            ct2SentPBPinnedAt, unchunked2PinnedAt, optAuthenticatorPBPinnedAt, h4896_48, List.append_assoc]
          (try sep_ac_rfl)
  intro sm4 hpcm4 hrunm4 hspm4 htrm4 hx19_4 hx20_4 hx21_4 hx23_4 hx24_4 hx25_4 hx27_4 hx28_4 hfp_4 hinv_4
  cases sendingCt2 with
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
    rw [hpool5, etv3_encodeInnerState_ct2Sampled_eq]
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
      (sp + 4840#64) sp cap ptr g.1 enc bs2 hfit_enc halign
      (F := optCt2SentPBPinnedAt A.repAlloc g.2 (sp + 4896#64) uc ∗ ((sp + 16#64) ↦₆₄ w25) ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hinv_4.trans hinv5.1) (by dsimp only [optPolynomialEncoderPBPinnedAt]; rw [hpool5]; (try sep_ac_rfl)) ?_
    intro sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp hinv_m5
    simp only [arm64_norm, hx19_4, hx21_4, hx23_4, hx25_4, hx27_4, hx28_4, hfp_4]
      at hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp
    refine SepWPp.weaken_pre (Entails.of_eq ?_)
      (hnext sm5 hpcm5 hrunm5 hspm5 htrm5 hm5_19 hm5_21 hm5_23 hm5_25 hm5_27 hm5_28 hm5_fp hinv_m5)
    rw [etv3_encodeInnerState_ct2Sampled_eq]
    simp +zetaDelta only [bs2, bs1, encodeOptMessage, optPolynomialEncoderPBPinnedAt, List.append_assoc]
    (try sep_ac_rfl)

end LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerChunked3aPlacedBudgetAux

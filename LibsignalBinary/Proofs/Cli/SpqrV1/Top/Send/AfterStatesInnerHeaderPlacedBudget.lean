/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerHeaderPlacedBudgetAux
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateHeader
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.V1StateHelpers
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesVnEncode
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Phase 3d Header & Jump-Table Dispatch (Block `427`)

Threads `RustCliAllocBudget` and `VmPreserved` through the `PqRatchetState.inner` header
and jump-table dispatch steps (`+6140..+6616`), re-exporting callee bridges from `Aux`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerHeaderPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalPlacement libsignalSessionCode lsmpl lsρ)
open CryptoVerification.RustHeap (RustAlloc vecU8At)
open CryptoVerification.LibsignalSpqrV1
  (ChainPB PqRatchetState V1State VersionNegotiationPB)
open CryptoVerification.LibsignalSpqrV1.Proto (encodeOptMessage encodeVarint)
open CryptoVerification.SpqrV1.ProtoRepr
  (V1StatePBGhost noneCap2 noneCap_add_two_beq_zero noneCap_add_two_bne_zero
   optChainPBPinnedAt optVersionNegotiationPBPinnedAt
   v1StateInnerPBPinnedAt
   v1StateJumpTableBytes v1StatePBEncodedLen v1StatePBEncodedLen_eq_proto v1StatePBPinnedAt)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (hwVarintLen_bvShift_eq_ofNat_varintLen_norm hwVarintLen_eq_ofNat_varintLen_norm
   noneCap_add_one_beq_zero noneCap_add_one_bne_zero
   ofNat_countLeadingZeros_32 ofNat_countLeadingZeros_64
   ule_self_64 ule_zero_64 ult_self_64 ult_zero_64
   zeroExtend64_beq_zero32 zext64_truncate32)
open CryptoVerification.SpqrV1.Prost.EncodeToVec
  (PqRatchetStatePBGhost StepInv cap_beq_len_false_of_lt encodeInner_v1_eq
   encodeToVecCalleeStackOf noneCap2_add_two_beq_zero noneCap2_add_two_bne_zero
   noneCap3 noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
   optPqRatchetInnerCap optPqRatchetInnerPBPinnedAt
   optPqRatchetInnerPBPinnedAt_cap_bounds
   pqRatchetStatePBEncodedLen pqRatchetStatePBEncodedLen_eq_proto pqRatchetStatePBPinnedAt
   v1StateInnerCap v1StateInnerCap_add_two_bounds v1StatePBEncodedLen_lt_of_state
   vecU8At_expose_header vecU8At_expose_one vecU8At_pack_one withStepInv)
open CryptoVerification.SpqrV1.Top.Send (spqrSendEncodeJumpTableBytes)
open CryptoVerification.Cli.SpqrV1.Top.Send.CodePlaced
  (blkPC_427 blkPl_427 ls_resolve_rel_427_blk_451 ls_resolve_rel_427_blk_484)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
  (spqrSendPlacedEntry spqrSendPlacedProg spqrSendRoSym)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhaseBudget
  (encodeVarintExactSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsPlacedBudget
  (sepWP_done_tpidr sepWP_done_vm sepWPp_of_sepWP_cs_vm)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsV1StateBudget
  (v1StateEncodedLenRoPinnedSpec)

variable [LibsignalPlacement]

/-! ## 1. Re-Exports from `AfterStatesInnerHeaderPlacedBudgetAux` -/

export LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerHeaderPlacedBudgetAux
  (spqrSendEncodeJumpTablePlacedAt_eq_bytes spqrSend_subroutine_ok_placed_of_plain
   spqrSend_subroutine_ok_placed_of_lscl spqrSend_etvMemcpy_ok_placed
   spqrSend_chainEncodedLen1_ok_placed)

export LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerHeaderPlacedBudgetAux
  (spqrSend_v1StateEncodedLen1_ok_placed spqrSend_epochEncodedLen1_ok_placed
   step_send_encode_varint_call_placed step_send_v1State_encLen_call_placed
   step_send_leaf_encLen16_call_placed)

export LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerHeaderPlacedBudgetAux
  (step_send_chunked_encLen48_call_placed step_send_encode_auth_call_placed
   step_send_encode_polyEncoder_call_placed step_send_encode_polyEncoder_budget_call_placed
   step_send_encode_polyDecoder_call_placed)

export LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerHeaderPlacedBudgetAux
  (step_send_encode_polyDecoder_budget_call_placed
   step_send_encode_ekSentCt1Received_call_placed
   step_send_encode_ekSentCt1Received_budget_call_placed
   step_send_encode_ct1Sent_call_placed
   step_send_encode_ct1Sent_budget_call_placed)

export LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerHeaderPlacedBudgetAux
  (step_send_inner_len_31b48_ro_placed step_send_inner_len_31b48_ro_pool_placed)

private theorem sepWPp_extract_pure {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp} (φ : Prop)
    (hφ : ∀ R : SepProp, s.mem ⊨ P ∗ R → φ)
    (hnext : φ → SepWPp prog ret s P Q Qp oom) :
    SepWPp prog ret s P Q Qp oom :=
  fun R hm hL => hnext (hφ R hm) R hm hL

private theorem sepWPp_extract_vecU8At_bounds {A : RustAlloc} {v cap ptr : BitVec 64}
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

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero spqrSendPlacedEntry
  zeroExtend64_beq_zero32
  ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 hwVarintLen_eq_ofNat_varintLen_norm
  hwVarintLen_bvShift_eq_ofNat_varintLen_norm zext64_truncate32
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  noneCap2_add_two_beq_zero noneCap2_add_two_bne_zero
  noneCap_add_two_beq_zero noneCap_add_two_bne_zero
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
  ule_zero_64 ult_zero_64 ule_self_64 ult_self_64

/-! ## 2. Header Steps (`+6140..+6216` and `+6592..+6616`) -/

/-- Step `spqrSendPlacedEntry + 6140#64 .. spqrSendPlacedEntry + 6216#64` when `st.inner = none`
(`x20 = noneCap3`), exposing `VmPreserved s sm`. -/
theorem step_send_inner_none_32058_placed
    (ext : String → Option (State → State))
    {s0 s : State} (sp : BitVec 64)
    {ret : BitVec 64} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = spqrSendPlacedEntry + 6140#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = noneCap3) (hinv0 : StepInv s0 s)
    (hnext : ∀ sm : State,
      sm.pc = spqrSendPlacedEntry + 6216#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = s.readReg64 .x25 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm → VmPreserved s sm →
      SepWPp (spqrSendPlacedProg ext) ret sm P Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
  apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_427).base + 6216#64)
  wp_steps
  apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, wp_norm, *])
  intro hinv
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (hinv0.trans hinv.1) hinv.2

theorem step_send_inner_none_32058_pool_placed
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    {s0 s : State} (sp : BitVec 64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = spqrSendPlacedEntry + 6140#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = noneCap3) (hinv0 : StepInv s0 s)
    (hP : P = A.pool lim st s ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = spqrSendPlacedEntry + 6216#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = s.readReg64 .x25 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm (A.pool lim st sm ∗ F) Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  subst hP
  refine step_send_inner_none_32058_placed ext sp hpc hrun hsp htr hx20 hinv0 ?_
  intro sm hpcm hrunm hspm htrm h19 h21 h23 h25 h27 h28 hfp hinvm hvm
  rw [← A.pool_of_vmPreserved hvm]
  exact hnext sm hpcm hrunm hspm htrm h19 h21 h23 h25 h27 h28 hfp hinvm

/-- Step `spqrSendPlacedEntry + 6140#64 .. spqrSendPlacedEntry + 6208#64` when `st.inner = some (.v1 v1)`:
writes outer tag `0x1a#8`, calls `V1State::encoded_len [local#3]` (Block `484`), and calls
`encode_varint` (Block `451`), threading `A.pool lim st`. -/
theorem step_send_inner_some_hdr_32058_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    {roV1 : BitVec 64} {s0 s : State}
    (hv1Len : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 484)
      (withStepInv s0 (v1StateEncodedLenRoPinnedSpec A.repAlloc roV1)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (sp cap ptr : BitVec 64) (g : V1StatePBGhost) (v1 : V1State) (bs : List (BitVec 8))
    (hv1_len : v1StatePBEncodedLen v1 < 2 ^ 64)
    (hfit : bs.length + 1 +
      (encodeVarint (BitVec.ofNat 64 (v1StatePBEncodedLen v1))).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = spqrSendPlacedEntry + 6140#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = optPqRatchetInnerCap g (some (.v1 v1))) (hinv0 : StepInv s0 s)
    (hP : P = (v1StatePBPinnedAt A.repAlloc g (sp + 4832#64) v1 ∗
      (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
      vecU8At A.repAlloc (sp + 1424#64) cap ptr bs ∗ A.pool lim st s ∗
      stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = spqrSendPlacedEntry + 6208#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 →
      sm.readReg64 .x20 = optPqRatchetInnerCap g (some (.v1 v1)) →
      sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x23 = s.readReg64 .x23 →
      sm.readReg64 .x25 = s.readReg64 .x25 → sm.readReg64 .x27 = s.readReg64 .x27 →
      sm.readReg64 .x28 = s.readReg64 .x28 → sm.readReg64 .fp = s.readReg64 .fp →
      StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((v1StatePBPinnedAt A.repAlloc g (sp + 4832#64) v1 ∗
          (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
          vecU8At A.repAlloc (sp + 1424#64) cap ptr
            ((bs ++ [0x1a#8]) ++ encodeVarint (BitVec.ofNat 64 (v1StatePBEncodedLen v1))) ∗
          A.pool lim st sm ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  subst hP
  refine sepWPp_extract_pure
    ((optPqRatchetInnerCap g (some (.v1 v1)) + 3#64 == 0#64) = false ∧
      (optPqRatchetInnerCap g (some (.v1 v1)) + 3#64 != 0#64) = true)
    (fun R' hm => by
      have hm' : s.mem ⊨ optPqRatchetInnerPBPinnedAt A.repAlloc g (sp + 4832#64) (some (.v1 v1)) ∗
          ((roV1 ↦ᵣ v1StateJumpTableBytes) ∗
           vecU8At A.repAlloc (sp + 1424#64) cap ptr bs ∗ A.pool lim st s ∗
           stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R') := by
        dsimp only [optPqRatchetInnerPBPinnedAt]; convert hm using 1; sep_ac_rfl
      exact optPqRatchetInnerPBPinnedAt_cap_bounds hm')
    fun ⟨hw_beq3, hw_bne3⟩ => ?_
  have hlt1 : bs.length < cap.toNat := by omega
  refine sepWPp_extract_vecU8At_bounds (v := sp + 1424#64) (cap := cap) (ptr := ptr) (bs := bs)
    (F := v1StatePBPinnedAt A.repAlloc g (sp + 4832#64) v1 ∗
      (roV1 ↦ᵣ v1StateJumpTableBytes) ∗ A.pool lim st s ∗
      stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F)
    (by sep_ac_rfl) fun _ hcap hptr => ?_
  have hbeq_false := cap_beq_len_false_of_lt hlt1 hcap
  rw [vecU8At_expose_one A.repAlloc (sp + 1424#64) cap ptr bs hlt1 hcap hptr]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun b0 => ?_
  have h1432 : (sp + 1424#64) + 8#64 = sp + 1432#64 := by bv_omega
  have h1440 : (sp + 1424#64) + 16#64 = sp + 1440#64 := by bv_omega
  rw [h1432, h1440]
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
  apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 484)
  by_vm_steps
    wp_steps
    apply sepWP_done_tpidr
      (by simp only [arm64_norm, ls_resolve_rel_427_blk_484, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv1
    have hpack := vecU8At_pack_one A.repAlloc (sp + 1424#64) cap ptr bs 0x1a#8 hlt1 hcap hptr
    simp only [arm64_norm, h1432, h1440] at hpack
    refine step_send_v1State_encLen_call_placed hres A.repAlloc ext hv1Len
      (sp + 4832#64) sp ((blkPl_427).base + 6200#64) g v1 hv1_len
      (F := vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs ++ [0x1a#8]) ∗ A.pool lim st s ∗ F)
      (by simp only [arm64_norm, ls_resolve_rel_427_blk_484])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
      (by simp only [arm64_norm, *]) (hinv0.trans hinv1.1)
      (by rw [← hpack]; sep_ac_rfl) ?_
    intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1 hcsm1 hinv_m1 hvm_m1
    rcases hcsm1 with ⟨hm19, hm20, hm21, _, hm23, _, hm25, _, hm27, hm28, hmfp, _⟩
    simp only [arm64_norm, hx20] at hm19 hm20 hm21 hm23 hm25 hm27 hm28 hmfp
    dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
    apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 451)
    wp_steps
    apply sepWP_done_vm
      (by simp only [arm64_norm, ls_resolve_rel_427_blk_451, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv2
    have hpool2 : A.pool lim st s = A.pool lim st _ :=
      (A.pool_of_vmPreserved (hinv1.2.trans (hvm_m1.trans hinv2.2))).symm
    refine step_send_encode_varint_call_placed A lim st hvarint
      (BitVec.ofNat 64 (v1StatePBEncodedLen v1)) (sp + 1424#64) cap ptr sp ((blkPl_427).base + 6208#64)
      (bs ++ [0x1a#8]) (by simpa only [List.length_append, List.length_singleton] using hfit)
      (F := v1StatePBPinnedAt A.repAlloc g (sp + 4832#64) v1 ∗
        (roV1 ↦ᵣ v1StateJumpTableBytes) ∗ F)
      (by simp only [arm64_norm, ls_resolve_rel_427_blk_451])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hinv_m1.trans hinv2.1) (by rw [hpool2]; sep_ac_rfl) ?_
    intro sm2 hpcm2 hrunm2 hspm2 htrm2 hcsm2 hinv_m2
    rcases hcsm2 with ⟨hm2_19, hm2_20, hm2_21, _, hm2_23, _, hm2_25, _, hm2_27, hm2_28, hm2_fp, _⟩
    simp only [arm64_norm, hm19, hm20, hm21, hm23, hm25, hm27, hm28, hmfp]
      at hm2_19 hm2_20 hm2_21 hm2_23 hm2_25 hm2_27 hm2_28 hm2_fp
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext sm2 hpcm2 hrunm2 hspm2 htrm2 hm2_19 hm2_20 hm2_21 hm2_23 hm2_25 hm2_27 hm2_28 hm2_fp hinv_m2)

/-- Step `spqrSendPlacedEntry + 6208#64 .. spqrSendPlacedEntry + 6216#64` when `v1.innerState = none`
(`x20 = noneCap2`), exposing `VmPreserved s sm`. -/
theorem step_send_inner_v1_none_32094_placed
    (A : RustAlloc) (ext : String → Option (State → State))
    {s0 s : State} (sp cap ptr : BitVec 64) (bs : List (BitVec 8))
    (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = spqrSendPlacedEntry + 6208#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = noneCap2) (hinv0 : StepInv s0 s)
    (hP : P = vecU8At A (sp + 1424#64) cap ptr bs ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = spqrSendPlacedEntry + 6216#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = s.readReg64 .x25 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm → VmPreserved s sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        (vecU8At A (sp + 1424#64) cap ptr bs ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  subst hP
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
  apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_427).base + 6216#64)
  wp_steps
  apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, wp_norm, *])
  intro hinv
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (hinv0.trans hinv.1) hinv.2

theorem step_send_inner_v1_none_32094_pool_placed
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    {s0 s : State} (sp cap ptr : BitVec 64) (bs : List (BitVec 8))
    (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = spqrSendPlacedEntry + 6208#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = noneCap2) (hinv0 : StepInv s0 s)
    (hP : P = vecU8At A.repAlloc (sp + 1424#64) cap ptr bs ∗ A.pool lim st s ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = spqrSendPlacedEntry + 6216#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = s.readReg64 .x25 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        (vecU8At A.repAlloc (sp + 1424#64) cap ptr bs ∗ A.pool lim st sm ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  subst hP
  refine step_send_inner_v1_none_32094_placed A.repAlloc ext sp cap ptr bs halign
    (F := A.pool lim st s ∗ F)
    hpc hrun hsp htr hx20 hinv0 rfl ?_
  intro sm hpcm hrunm hspm htrm h19 h21 h23 h25 h27 h28 hfp hinvm hvm
  rw [← A.pool_of_vmPreserved hvm]
  exact hnext sm hpcm hrunm hspm htrm h19 h21 h23 h25 h27 h28 hfp hinvm

/-- Step `spqrSendPlacedEntry + 6208#64 .. spqrSendPlacedEntry + 6616#64` when `v1.innerState = some is`:
branches to `+6592`, computes jump-table index in `x8`, and loads `.rodata`
jump-table base address `lsρ spqrSendRoSym + 22#64` into `x9`, exposing `VmPreserved s sm`. -/
theorem step_send_inner_to_6616_placed
    (ext : String → Option (State → State))
    {s0 s : State} (sp w : BitVec 64)
    (hw_beq : (w + 2#64 == 0#64) = false) (hw_bne : (w + 2#64 != 0#64) = true)
    {ret : BitVec 64} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = spqrSendPlacedEntry + 6208#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = w) (hinv0 : StepInv s0 s)
    (hnext : ∀ sm : State,
      sm.pc = spqrSendPlacedEntry + 6616#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x8 =
        (if BitVec.ult (w ^^^ 0x8000000000000000#64) 11#64
         then w ^^^ 0x8000000000000000#64 else 7#64) →
      sm.readReg64 .x9 = lsρ spqrSendRoSym + 22#64 →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = w →
      sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x23 = s.readReg64 .x23 →
      sm.readReg64 .x25 = s.readReg64 .x25 → sm.readReg64 .x27 = s.readReg64 .x27 →
      sm.readReg64 .x28 = s.readReg64 .x28 → sm.readReg64 .fp = s.readReg64 .fp →
      StepInv s0 sm → VmPreserved s sm →
      SepWPp (spqrSendPlacedProg ext) ret sm P Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
  apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_427).base + 6616#64)
  wp_steps
  apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, wp_norm, *])
  intro hinv
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, spqrSendRoSym, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hinv0.trans hinv.1) hinv.2

theorem step_send_inner_to_6616_pool_placed
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    {s0 s : State} (sp w : BitVec 64)
    (hw_beq : (w + 2#64 == 0#64) = false) (hw_bne : (w + 2#64 != 0#64) = true)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = spqrSendPlacedEntry + 6208#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = w) (hinv0 : StepInv s0 s)
    (hP : P = A.pool lim st s ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = spqrSendPlacedEntry + 6616#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x8 =
        (if BitVec.ult (w ^^^ 0x8000000000000000#64) 11#64
         then w ^^^ 0x8000000000000000#64 else 7#64) →
      sm.readReg64 .x9 = lsρ spqrSendRoSym + 22#64 →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = w →
      sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x23 = s.readReg64 .x23 →
      sm.readReg64 .x25 = s.readReg64 .x25 → sm.readReg64 .x27 = s.readReg64 .x27 →
      sm.readReg64 .x28 = s.readReg64 .x28 → sm.readReg64 .fp = s.readReg64 .fp →
      StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm (A.pool lim st sm ∗ F) Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  subst hP
  refine step_send_inner_to_6616_placed ext sp w hw_beq hw_bne hpc hrun hsp htr hx20 hinv0 ?_
  intro sm hpcm hrunm hspm htrm h8 h9 h19 h20 h21 h23 h25 h27 h28 hfp hinvm hvm
  rw [← A.pool_of_vmPreserved hvm]
  exact hnext sm hpcm hrunm hspm htrm h8 h9 h19 h20 h21 h23 h25 h27 h28 hfp hinvm

/-! ## 3. Budget-Threaded `StepSendInnerStateAt6616Placed` and Master `step_send_inner_32058_placed` (`+6140..+6216`) -/

/-- Budget-threaded unified stepping obligation from `spqrSendPlacedEntry + 6616#64` (jump-table
dispatch) to `spqrSendPlacedEntry + 6216#64` (post-encode join) for a `V1State.InnerState` value `is`,
preserving `A.pool lim st0`. -/
def StepSendInnerStateAt6616Placed (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (ext : String → Option (State → State)) (roBase : BitVec 64)
    (s0 : State) (is : V1State.InnerState) : Prop :=
  ∀ (sp cap ptr w25 : BitVec 64) (g : V1StatePBGhost) (bs : List (BitVec 8)),
    v1StatePBEncodedLen ⟨some is⟩ < 2 ^ 64 →
    bs.length + (V1State.InnerState.encode is).length ≤ cap.toNat →
    sp &&& 15#64 = 0#64 →
    ∀ {ret : BitVec 64} {s : State} {P F : SepProp}
      {Q Qp : State → SepProp → Prop} {oom : State → SepProp},
      s.pc = spqrSendPlacedEntry + 6616#64 →
      s.status = .Running →
      s.sp = sp →
      s.trace = s0.trace →
      s.readReg64 .x8 =
        (if BitVec.ult (v1StateInnerCap g is ^^^ 0x8000000000000000#64) 11#64
         then v1StateInnerCap g is ^^^ 0x8000000000000000#64 else 7#64) →
      s.readReg64 .x9 = roBase →
      s.readReg64 .x20 = v1StateInnerCap g is →
      s.readReg64 .x25 = w25 →
      StepInv s0 s →
      P = (v1StateInnerPBPinnedAt A.repAlloc g (sp + 4832#64) is ∗
        ((sp + 16#64) ↦₆₄ w25) ∗
        (roBase ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
        vecU8At A.repAlloc (sp + 1424#64) cap ptr bs ∗ A.pool lim st0 s ∗
        stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F →
      (∀ sm : State,
        sm.pc = spqrSendPlacedEntry + 6216#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
        sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 →
        sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = w25 →
        sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 →
        sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
        SepWPp (spqrSendPlacedProg ext) ret sm
          ((v1StateInnerPBPinnedAt A.repAlloc g (sp + 4832#64) is ∗
            ((sp + 16#64) ↦₆₄ w25) ∗
            (roBase ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
            vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs ++ V1State.InnerState.encode is) ∗
            A.pool lim st0 sm ∗
            stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
          Q Qp oom) →
      SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom

/-- Step `spqrSendPlacedEntry + 6140#64 .. spqrSendPlacedEntry + 6216#64`: encodes `st.inner`
into `vecU8At A.repAlloc (sp + 1424#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr`,
producing `PqRatchetState.encodeRaw st` while threading `A.pool lim st0`. -/
theorem step_send_inner_32058_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (ext : String → Option (State → State))
    {roV1 : BitVec 64} {s0 s : State}
    (hv1Len : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 484)
      (withStepInv s0 (v1StateEncodedLenRoPinnedSpec A.repAlloc roV1)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hInnerAt6616 : ∀ is : V1State.InnerState,
      StepSendInnerStateAt6616Placed resStack A lim st0 ext (lsρ spqrSendRoSym + 22#64) s0 is)
    (sp ptr w25 : BitVec 64) (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63) (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = spqrSendPlacedEntry + 6140#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = optPqRatchetInnerCap g.inner st.inner)
    (hx25 : s.readReg64 .x25 = w25) (hinv0 : StepInv s0 s)
    (hP : P = (pqRatchetStatePBPinnedAt A.repAlloc g (sp + 4704#64) st ∗
      ((sp + 16#64) ↦₆₄ w25) ∗
      (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
      ((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
      vecU8At A.repAlloc (sp + 1424#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr
        (encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 st.versionNegotiation ++
          encodeOptMessage ChainPB.encodeRaw 2#32 st.chain) ∗
      A.pool lim st0 s ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = spqrSendPlacedEntry + 6216#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x25 = w25 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((pqRatchetStatePBPinnedAt A.repAlloc g (sp + 4704#64) st ∗
          ((sp + 16#64) ↦₆₄ w25) ∗
          (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
          ((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
          vecU8At A.repAlloc (sp + 1424#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr
            (PqRatchetState.encodeRaw st) ∗
          A.pool lim st0 sm ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  subst hP
  have h4832 : (sp + 4704#64) + 128#64 = sp + 4832#64 := by bv_omega
  let cap := BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)
  let bs0 := encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 st.versionNegotiation ++
    encodeOptMessage ChainPB.encodeRaw 2#32 st.chain
  have hcap_toNat : cap.toNat = pqRatchetStatePBEncodedLen st := by
    dsimp only [cap]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  cases hin : st.inner with
  | none =>
    rw [hin] at hx20
    refine step_send_inner_none_32058_pool_placed A lim st0 ext sp
      (F := pqRatchetStatePBPinnedAt A.repAlloc g (sp + 4704#64) st ∗
        ((sp + 16#64) ↦₆₄ w25) ∗
        (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
        ((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
        vecU8At A.repAlloc (sp + 1424#64) cap ptr bs0 ∗
        stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F)
      hpc hrun hsp htr hx20 hinv0 (by dsimp only [cap, bs0]; sep_ac_rfl) ?_
    intro sm hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m
    rw [hx25] at hm25
    refine SepWPp.weaken_pre ?_
      (hnext sm hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m)
    have henc : PqRatchetState.encodeRaw st = bs0 := by
      unfold PqRatchetState.encodeRaw
      rw [hin]; simp only [bs0, List.append_nil]
    rw [henc]
    dsimp only [cap, bs0]
    exact Entails.of_eq (by sep_ac_rfl)
  | some inner =>
    cases inner with
    | v1 v1 =>
      rw [hin] at hx20
      have ⟨hv1_len64, _, _⟩ := v1StatePBEncodedLen_lt_of_state hin hlen
      have hv1_all : bs0.length + (PqRatchetState.Inner.encode (.v1 v1)).length ≤ cap.toNat := by
        rw [hcap_toNat, ← pqRatchetStatePBEncodedLen_eq_proto st]
        unfold PqRatchetState.encodeRaw
        rw [hin]; simp only [bs0, List.length_append]
        exact Nat.le_refl _
      rw [encodeInner_v1_eq v1] at hv1_all
      simp only [List.length_append, List.length_singleton,
        show (V1State.encodeRaw v1).length = v1StatePBEncodedLen v1 from v1StatePBEncodedLen_eq_proto v1] at hv1_all
      let F_outer : SepProp :=
        optVersionNegotiationPBPinnedAt A.repAlloc g.vn (sp + 4704#64) st.versionNegotiation ∗
          optChainPBPinnedAt A.repAlloc g.chain ((sp + 4704#64) + 48#64) st.chain ∗
          ((sp + 16#64) ↦₆₄ w25) ∗
          ((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗ F
      refine step_send_inner_some_hdr_32058_placed hres A lim st0 ext hv1Len hvarint
        sp cap ptr g.inner v1 bs0 hv1_len64 (by omega) halign
        (F := F_outer)
        hpc hrun hsp htr hx20 hinv0
        (by unfold pqRatchetStatePBPinnedAt; rw [hin, h4832]
            dsimp only [optPqRatchetInnerPBPinnedAt, cap, bs0, F_outer]; sep_ac_rfl) ?_
      intro s1 hpcs1 hruns1 hsps1 htrs1 hs1_19 hs1_20 hs1_21 hs1_23 hs1_25 hs1_27 hs1_28 hs1_fp hinv_s1
      rw [hx25] at hs1_25
      let bs_hdr := (bs0 ++ [0x1a#8]) ++ encodeVarint (BitVec.ofNat 64 (v1StatePBEncodedLen v1))
      cases his : v1.innerState with
      | none =>
        have hx20_none : s1.readReg64 .x20 = noneCap2 := by
          rw [hs1_20]; dsimp only [optPqRatchetInnerCap]; rw [his]
        refine step_send_inner_v1_none_32094_pool_placed A lim st0 ext sp cap ptr bs_hdr halign
          (F := v1StatePBPinnedAt A.repAlloc g.inner (sp + 4832#64) v1 ∗
            (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
            stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F_outer)
          hpcs1 hruns1 hsps1 htrs1 hx20_none hinv_s1 (by dsimp only [bs_hdr]; sep_ac_rfl) ?_
        intro sm hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m
        rw [hs1_19] at hm19; rw [hs1_21] at hm21; rw [hs1_23] at hm23; rw [hs1_25] at hm25
        rw [hs1_27] at hm27; rw [hs1_28] at hm28; rw [hs1_fp] at hmfp
        refine SepWPp.weaken_pre ?_
          (hnext sm hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m)
        have henc : PqRatchetState.encodeRaw st = bs_hdr := by
          unfold PqRatchetState.encodeRaw
          rw [hin]; dsimp only
          rw [encodeInner_v1_eq v1]
          dsimp only [V1State.encodeRaw]
          rw [his]
          simp only [List.append_nil, bs0, bs_hdr, List.append_assoc]
        rw [henc]
        unfold pqRatchetStatePBPinnedAt
        rw [hin, h4832]
        dsimp only [optPqRatchetInnerPBPinnedAt, cap, bs_hdr, F_outer]
        exact Entails.of_eq (by sep_ac_rfl)
      | some is =>
        have hx20_some : s1.readReg64 .x20 = v1StateInnerCap g.inner is := by
          rw [hs1_20]; dsimp only [optPqRatchetInnerCap]; rw [his]
        refine sepWPp_extract_pure
          ((v1StateInnerCap g.inner is + 2#64 == 0#64) = false ∧
            (v1StateInnerCap g.inner is + 2#64 != 0#64) = true)
          (fun R' hm => by
            dsimp only [v1StatePBPinnedAt] at hm
            rw [his] at hm
            dsimp only at hm
            have hm' : s1.mem ⊨ v1StateInnerPBPinnedAt A.repAlloc g.inner (sp + 4832#64) is ∗
                ((roV1 ↦ᵣ v1StateJumpTableBytes) ∗
                 vecU8At A.repAlloc (sp + 1424#64) cap ptr bs_hdr ∗ A.pool lim st0 s1 ∗
                 stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F_outer ∗ R') := by
              convert hm using 1; dsimp only [bs_hdr]; sep_ac_rfl
            exact v1StateInnerCap_add_two_bounds hm')
          fun ⟨hw_beq2, hw_bne2⟩ => ?_
        refine step_send_inner_to_6616_pool_placed A lim st0 ext sp (v1StateInnerCap g.inner is)
          hw_beq2 hw_bne2
          (F := v1StatePBPinnedAt A.repAlloc g.inner (sp + 4832#64) v1 ∗
            (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
            vecU8At A.repAlloc (sp + 1424#64) cap ptr bs_hdr ∗
            stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F_outer)
          hpcs1 hruns1 hsps1 htrs1 hx20_some hinv_s1 (by dsimp only [bs_hdr]; sep_ac_rfl) ?_
        intro s2 hpcs2 hruns2 hsps2 htrs2 hs2_8 hs2_9 hs2_19 hs2_20 hs2_21 hs2_23 hs2_25 hs2_27 hs2_28 hs2_fp hinv_s2
        rw [hs1_19] at hs2_19; rw [hs1_21] at hs2_21; rw [hs1_23] at hs2_23; rw [hs1_25] at hs2_25
        rw [hs1_27] at hs2_27; rw [hs1_28] at hs2_28; rw [hs1_fp] at hs2_fp
        have hv_len64' : v1StatePBEncodedLen ⟨some is⟩ < 2 ^ 64 := by
          have : v1 = ⟨some is⟩ := by cases v1; subst his; rfl
          rw [← this]; exact hv1_len64
        have his_fit : bs_hdr.length + (V1State.InnerState.encode is).length ≤ cap.toNat := by
          have hlen_is : (V1State.InnerState.encode is).length = v1StatePBEncodedLen v1 := by
            rw [← v1StatePBEncodedLen_eq_proto v1]
            dsimp only [V1State.encodedLen, V1State.encodeRaw]; rw [his]
          simp only [bs_hdr, List.length_append, List.length_singleton, hlen_is]
          omega
        refine hInnerAt6616 is sp cap ptr w25 g.inner bs_hdr hv_len64' his_fit halign
          hpcs2 hruns2 hsps2 htrs2 hs2_8 hs2_9 hs2_20 hs2_25 hinv_s2
          (F := optVersionNegotiationPBPinnedAt A.repAlloc g.vn (sp + 4704#64) st.versionNegotiation ∗
            optChainPBPinnedAt A.repAlloc g.chain ((sp + 4704#64) + 48#64) st.chain ∗
            (roV1 ↦ᵣ v1StateJumpTableBytes) ∗ F)
          (by dsimp only [v1StatePBPinnedAt, bs_hdr, F_outer]; rw [his]; dsimp only; sep_ac_rfl) ?_
        intro sm hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m
        rw [hs2_19] at hm19; rw [hs2_21] at hm21; rw [hs2_23] at hm23
        rw [hs2_27] at hm27; rw [hs2_28] at hm28; rw [hs2_fp] at hmfp
        refine SepWPp.weaken_pre ?_
          (hnext sm hpcm hrunm hspm htrm hm19 hm21 hm23 hm25 hm27 hm28 hmfp hinv_m)
        have henc : PqRatchetState.encodeRaw st = bs_hdr ++ V1State.InnerState.encode is := by
          unfold PqRatchetState.encodeRaw
          rw [hin]; dsimp only
          rw [encodeInner_v1_eq v1]
          dsimp only [V1State.encodeRaw]
          rw [his]
          simp only [bs0, bs_hdr, List.append_assoc]
        rw [henc]
        unfold pqRatchetStatePBPinnedAt
        rw [hin, h4832]
        dsimp only [optPqRatchetInnerPBPinnedAt, v1StatePBPinnedAt, cap]
        rw [his]
        exact Entails.of_eq (by sep_ac_rfl)

end LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerHeaderPlacedBudget

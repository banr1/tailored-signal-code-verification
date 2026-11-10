/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.DefsV1StatePlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerHeaderPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsV1StateBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.ChainEncodedLenPlacedBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.V1StatePlacedBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EpochEncodedLenPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateHeader
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.V1StateHelpers
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesVnEncode
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Phase 3d Callee Bridges & Inner Length Step (Block `427`)

Provides budget-ready `[local#3]` callee bridges, polymorphic `s.sp = sp` call wrappers,
and the `VmPreserved` inner encoded-length step (`+4844..+4920`) for Block `427`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerHeaderPlacedBudgetAux

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement extract_withLsCodeLoaded libsignalSessionCode
   ls_subroutine_ok_of_block lsmpl lsρ subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded)
open CryptoVerification.RustHeap (RustAlloc vecU8At)
open CryptoVerification.LibsignalTripleRatchet
  (sessionMemcpyRegionSpec sessionMemcpySpec)
open CryptoVerification.LibsignalSpqrV1
  (AuthenticatorPB ChainEpochPB PolynomialDecoder PolynomialEncoder PqRatchetState
   ProtoAuthenticator V1State)
open CryptoVerification.LibsignalSpqrV1.Proto (encodeMessage encodeVarint)
open CryptoVerification.SpqrV1.Alloc (spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.ProtoRepr
  (AuthenticatorPBGhost ChainEpochPBGhost EpochEncodedLenFits PinnedEncLenGhost
   PolynomialDecoderPBGhost PolynomialEncoderPBGhost Unchunked4PBGhost Unchunked5PBGhost
   V1StatePBGhost authenticatorPBPinnedAt chainEpochPBEncodedLen chainEpochPBPinnedAt
   ct1SentPBPinnedAt ekSentCt1ReceivedPBPinnedAt epochEncodedLenStack
   noneCap_add_two_beq_zero noneCap_add_two_bne_zero
   optChainPBPinnedAt optVersionNegotiationPBPinnedAt
   polynomialDecoderPBPinnedAt polynomialEncoderPBPinnedAt unchunkedEncodedLenStack
   v1StateEncodedLenStack v1StateJumpTableBytes v1StatePBEncodedLen v1StatePBPinnedAt)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (adds_no_overflow_of_eq cmp_ls_false_of_lt
   hwVarintLen_bvShift_eq_ofNat_varintLen_norm hwVarintLen_eq_ofNat_varintLen_norm
   noneCap_add_one_beq_zero noneCap_add_one_bne_zero
   ofNat_countLeadingZeros_32 ofNat_countLeadingZeros_64
   ule_self_64 ule_zero_64 ult_self_64 ult_zero_64
   zeroExtend64_beq_zero32 zext64_truncate32)
open CryptoVerification.SpqrV1.Prost.EncodeToVec
  (PqRatchetStatePBGhost StepInv bv_optInner_some_eq encodeToVecCalleeStackOf
   noneCap2_add_two_beq_zero noneCap2_add_two_bne_zero
   noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
   optChainPBFieldEncodedLen optPqRatchetInnerCap
   optPqRatchetInnerPBFieldEncodedLen optPqRatchetInnerPBPinnedAt
   optPqRatchetInnerPBPinnedAt_cap_bounds optPqRatchetInnerPBPinnedAt_eq
   optVersionNegotiationPBFieldEncodedLen
   pqRatchetStatePBEncodedLen pqRatchetStatePBPinnedAt
   stackAt_callee_eq_unchunkedEncodedLen stackAt_callee_eq_v1StateEncodedLen
   subroutine_ok_withStepInv_lscl v1StatePBEncodedLen_lt_of_state withStepInv)
open CryptoVerification.Cli.SpqrV1.ProtoRepr (cliV1StateJtSym)
open CryptoVerification.Cli.SpqrV1.Top.Send.CodePlaced
  (blkPC_427 blkPl_427 ls_resolve_rel_427_blk_484)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.ChainEncodedLenPlacedBudget
  (chainEncodedLen_local1_pinned_placed_ok_ext)
open LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.V1StatePlacedBudget
  (v1StateEncodedLen_local1_pinned_placed_ok_ext)
open LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EpochEncodedLenPlacedBudget
  (epochEncodedLen_local1_pinned_placed_ok_ext)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
  (AllocContractsPlaced spqrSendPlacedEntry spqrSendPlacedProg)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhaseBudget
  (authEncodeExactSpecOf encodeVarintExactSpecOf epochEncLenStackSpecOf etvMemcpyRegionSpec
   step_etv_encode_auth_call_prog step_etv_encode_varint_call_prog)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsPlacedBudget
  (sepWP_done_vm sepWPp_call_cs_noPanic sepWPp_of_sepWP_cs_vm)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonBudget
  (etvCt1SentEncodeSpecOf etvEkSentCt1ReceivedEncodeSpecOf etvPolyDecoderExactSpecOf
   etvPolyEncoderExactSpecOf leafEncLen16Spec leafEncLen48Spec)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonPlacedBudget
  (etvCt1SentBudgetExactSpecOf etvEkSentCt1ReceivedBudgetExactSpecOf
   etvPolyDecoderBudgetExactSpecOf etvPolyEncoderBudgetExactSpecOf
   step_etv_chunked_encLen48_call_placed step_etv_encode_ct1Sent_budget_call_placed
   step_etv_encode_ct1Sent_call_placed step_etv_encode_ekSentCt1Received_budget_call_placed
   step_etv_encode_ekSentCt1Received_call_placed step_etv_encode_polyDecoder_budget_call_placed
   step_etv_encode_polyDecoder_call_placed step_etv_encode_polyEncoder_budget_call_placed
   step_etv_encode_polyEncoder_call_placed step_etv_leaf_encLen16_call_placed
   step_etv_v1State_encLen_call_placed)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget
  (chainEncodedLenPinnedSpec epochEncodedLenPinnedSpec withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsV1StateBudget
  (v1StateEncodedLenRoPinnedSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyBudgetSpec sessionMemcpyRegionBudgetSpec)

variable [LibsignalPlacement]

/-! ## 1. Re-Exports of Jump-Table Identity & Block `427` `subroutine_ok` Lifting Helpers -/

export CryptoVerification.Cli.SpqrV1.Top.Send
  (spqrSendEncodeJumpTablePlacedAt_eq_bytes spqrSend_subroutine_ok_placed_of_plain
   spqrSend_subroutine_ok_placed_of_lscl)

private theorem sp_add_144_sub_144 (sp : BitVec 64) : (sp + 144#64) - 144#64 = sp := by
  bv_omega

private theorem sp_add_144_aligned {sp : BitVec 64} (h : sp &&& 15#64 = 0#64) :
    (sp + 144#64) &&& 15#64 = 0#64 := by
  clear *- h; bv_bits

private theorem sepWPp_extract_pure {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp} (φ : Prop)
    (hφ : ∀ R : SepProp, s.mem ⊨ P ∗ R → φ)
    (hnext : φ → SepWPp prog ret s P Q Qp oom) :
    SepWPp prog ret s P Q Qp oom :=
  fun R hm hL => hnext (hφ R hm) R hm hL

/-! ## 2. Budget-Ready `[local#3]` Callee `subroutine_ok` Bridges for `spqr::send::<Coins>` (Block `427`) -/

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

/-- Derive `subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy") etvMemcpyRegionSpec`
    (carrying `⌜VmPreserved s0 sf⌝`) from `AllocContractsPlaced M A lim ext`. -/
theorem spqrSend_etvMemcpy_ok_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext) :
    subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy") etvMemcpyRegionSpec := by
  have h0 : subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy") (sessionMemcpyBudgetSpec 0) :=
    spqr_hook_ok_of_mem (hA.session_memcpy 0)
  refine subroutine_ok_mono h0 ?_ ?_
  · intro ⟨dst, src, srcBytes⟩ R s hm
    dsimp only [etvMemcpyRegionSpec, sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec,
      memcpyRegionSpec, sessionMemcpyBudgetSpec, sessionMemcpySpec, libcMemcpySpec, stackAt] at hm ⊢
    rw [ProofLib.memRegion_zero]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  · intro ⟨dst, src, srcBytes⟩ R s0 sf hm
    dsimp only [etvMemcpyRegionSpec, sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec,
      sessionMemcpyBudgetSpec, sessionMemcpySpec, stackAt] at hm ⊢
    rw [ProofLib.memRegion_zero] at hm
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm

/-- `Chain::encoded_len [local#3]` (Block `485`) with `⌜VmPreserved s0 sf⌝` on `spqrSendPlacedProg ext`. -/
theorem spqrSend_chainEncodedLen1_ok_placed (A : RustAlloc)
    (ext : String → Option (State → State)) (s0 : State)
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 485)
      (withStepInv s0 (chainEncodedLenPinnedSpec A)) :=
  spqrSend_subroutine_ok_placed_of_lscl hcl0
    (chainEncodedLen_local1_pinned_placed_ok_ext A ext)

/-- `V1State::encoded_len [local#3]` (Block `484`) with `⌜VmPreserved s0 sf⌝` on `spqrSendPlacedProg ext`. -/
theorem spqrSend_v1StateEncodedLen1_ok_placed (A : RustAlloc)
    (ext : String → Option (State → State)) (s0 : State)
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 484)
      (withStepInv s0 (v1StateEncodedLenRoPinnedSpec A (lsρ cliV1StateJtSym))) :=
  spqrSend_subroutine_ok_placed_of_lscl hcl0
    (v1StateEncodedLen_local1_pinned_placed_ok_ext A ext)

/-- `Epoch::encoded_len [local#3]` (Block `478`) lifted to `epochEncLenStackSpecOf resStack A`
    (with `⌜VmPreserved s0 sf⌝`) on `spqrSendPlacedProg ext`. -/
theorem spqrSend_epochEncodedLen1_ok_placed {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    (A : RustAlloc) (ext : String → Option (State → State)) (s0 : State)
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 478)
      (withStepInv s0 (epochEncLenStackSpecOf resStack A)) := by
  have hep : subroutine_ok (spqrSendPlacedProg ext)
      (lsmpl.base 478) (withLsCodeLoaded lsmpl (epochEncodedLenPinnedSpec A)) :=
    ls_subroutine_ok_of_block
      (subroutine_ok_withLsCodeLoaded_of_plain
        (epochEncodedLen_local1_pinned_placed_ok_ext A ext))
      (by decide) (by decide) (by decide)
  apply subroutine_ok_withStepInv_lscl hcl0
  refine subroutine_ok_outcome_intro fun ⟨a, g, ep⟩ R s hpc hrun hpre hal => ?_
  obtain ⟨hcl_s, hpre⟩ := extract_withLsCodeLoaded hpre
  dsimp only [epochEncLenStackSpecOf] at hpre
  rw [stackAt_callee_eq_unchunkedEncodedLen hres s.sp] at hpre
  let F_rem := memRegion (s.sp - BitVec.ofNat 64 (encodeToVecCalleeStackOf resStack)) (160 + resStack)
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hfit⟩, hm⟩
  have hpre' : s.mem ⊨ (withLsCodeLoaded lsmpl (epochEncodedLenPinnedSpec A)).pre ⟨a, g, ep⟩ s ∗ (F_rem ∗ R) := by
    dsimp only [withLsCodeLoaded, epochEncodedLenPinnedSpec, withVmPreserved,
      CryptoVerification.SpqrV1.ProtoRepr.epochEncodedLenPinnedSpec, EpochEncodedLenFits]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl_s, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hfit⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by dsimp [F_rem, epochEncodedLenStack, unchunkedEncodedLenStack]; sep_ac_rfl)) hm
  refine hep.mono_outcome ⟨a, g, ep⟩ (F_rem ∗ R) s hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, epochEncodedLenPinnedSpec, withVmPreserved,
      CryptoVerification.SpqrV1.ProtoRepr.epochEncodedLenPinnedSpec, epochEncLenStackSpecOf] at hpost ⊢
    rw [stackAt_callee_eq_unchunkedEncodedLen hres s.sp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hvm, ⟨hx0f, htrf⟩, hpost⟩
    refine ⟨⟨hvm, hx0f, htrf⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by dsimp [F_rem, epochEncodedLenStack, unchunkedEncodedLenStack]; sep_ac_rfl)) hpost
  · exact (ProofLib.allowPanic_not_exited hpan).elim
  · exact (ProofLib.allowPanic_not_exited hex).elim
  · exact (ProofLib.allowPanic_not_exited hoom).elim

/-! ## 3. Budget-Threaded `s.sp = sp` Call Wrappers for `V1State` Encoding in `spqr::send::<Coins>` (Block `427`) -/

/-- Execute `bl encode_varint` at `s.sp = sp` on any `prog : Program`, threading `A.pool lim st`. -/
theorem step_send_encode_varint_call_placed {resStack : Nat} {M : AllocCostModel}
    {prog : Program} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {call_pc : BitVec 64} {s0 s : State}
    (henc : subroutine_ok prog call_pc
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (val v cap ptr sp ret_pc : BitVec 64) (bs : List (BitVec 8))
    (hfit : bs.length + (encodeVarint val).length ≤ cap.toNat)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = val)
    (hx1 : s.readReg64 .x1 = v)
    (hinv0 : StepInv s0 s)
    (hP : P = (vecU8At A.repAlloc v cap ptr bs ∗ A.pool lim st s ∗
      stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      StepInv s0 sm →
      SepWPp prog ret sm
        ((vecU8At A.repAlloc v cap ptr (bs ++ encodeVarint val) ∗ A.pool lim st sm ∗
          stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  have hsp' : s.sp = (sp + 144#64) - 144#64 := by rw [sp_add_144_sub_144, hsp]
  have hP' : P = (vecU8At A.repAlloc v cap ptr bs ∗ A.pool lim st s ∗
      stackAt ((sp + 144#64) - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F := by
    rw [sp_add_144_sub_144]; exact hP
  refine step_etv_encode_varint_call_prog A lim st henc val v cap ptr (sp + 144#64) ret_pc bs hfit
    hpc hrun hsp' (sp_add_144_aligned halign) htr hlr hx0 hx1 hinv0 hP' ?_
  intro sm hpcm hrunm hspm htrm hcsm hinvm
  rw [sp_add_144_sub_144] at hspm
  refine SepWPp.weaken_pre (by rw [sp_add_144_sub_144]; exact Entails.refl _)
    (hnext sm hpcm hrunm hspm htrm hcsm hinvm)

/-- Execute `bl V1State::encoded_len [local#3]` (Block `484`) at `s.sp = sp`, exposing `VmPreserved s sm`. -/
theorem step_send_v1State_encLen_call_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (A : RustAlloc) (ext : String → Option (State → State))
    {roV1 call_pc : BitVec 64} {s0 s : State}
    (hv1Len : subroutine_ok (spqrSendPlacedProg ext) call_pc
      (withStepInv s0 (v1StateEncodedLenRoPinnedSpec A roV1)))
    (v1A sp ret_pc : BitVec 64) (g : V1StatePBGhost) (v1 : V1State)
    (hfit : v1StatePBEncodedLen v1 < 2 ^ 64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = v1A) (hinv0 : StepInv s0 s)
    (hP : P = (v1StatePBPinnedAt A g v1A v1 ∗
      (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
      stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 (v1StatePBEncodedLen v1) →
      CalleeSavedPreserved s sm → StepInv s0 sm → VmPreserved s sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((v1StatePBPinnedAt A g v1A v1 ∗
          (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
          stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  have hsp' : s.sp = (sp + 144#64) - 144#64 := by rw [sp_add_144_sub_144, hsp]
  have hP' : P = (v1StatePBPinnedAt A g v1A v1 ∗
      (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
      stackAt ((sp + 144#64) - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F := by
    rw [sp_add_144_sub_144]; exact hP
  refine step_etv_v1State_encLen_call_placed hres A hv1Len v1A (sp + 144#64) ret_pc
    g v1 hfit hpc hrun hsp' (sp_add_144_aligned halign) htr hlr hx0 hinv0 hP' ?_
  intro sm hpcm hrunm hspm htrm hx0m hcsm hinvm hvmm
  rw [sp_add_144_sub_144] at hspm
  refine SepWPp.weaken_pre (by rw [sp_add_144_sub_144]; exact Entails.refl _)
    (hnext sm hpcm hrunm hspm htrm hx0m hcsm hinvm hvmm)

/-- Execute any 16-byte stack `encoded_len` leaf callee at `s.sp = sp`, exposing `VmPreserved s sm`. -/
theorem step_send_leaf_encLen16_call_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {G M_msg : Type} (ext : String → Option (State → State))
    (reprAt : G → BitVec 64 → M_msg → SepProp) (encLen : M_msg → Nat)
    {call_pc : BitVec 64} {s0 s : State}
    (hcallee : subroutine_ok (spqrSendPlacedProg ext) call_pc
      (withStepInv s0 (leafEncLen16Spec reprAt encLen)))
    (msgA sp ret_pc : BitVec 64) (g : G) (m : M_msg) (hfit : encLen m < 2 ^ 64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = msgA) (hinv0 : StepInv s0 s)
    (hP : P = (reprAt g msgA m ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 (encLen m) →
      CalleeSavedPreserved s sm → StepInv s0 sm → VmPreserved s sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((reprAt g msgA m ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  have hsp' : s.sp = (sp + 144#64) - 144#64 := by rw [sp_add_144_sub_144, hsp]
  have hP' : P = (reprAt g msgA m ∗
      stackAt ((sp + 144#64) - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F := by
    rw [sp_add_144_sub_144]; exact hP
  refine step_etv_leaf_encLen16_call_placed hres reprAt encLen hcallee msgA (sp + 144#64) ret_pc
    g m hfit hpc hrun hsp' (sp_add_144_aligned halign) htr hlr hx0 hinv0 hP' ?_
  intro sm hpcm hrunm hspm htrm hx0m hcsm hinvm hvmm
  rw [sp_add_144_sub_144] at hspm
  refine SepWPp.weaken_pre (by rw [sp_add_144_sub_144]; exact Entails.refl _)
    (hnext sm hpcm hrunm hspm htrm hx0m hcsm hinvm hvmm)

/-- Execute any 48-byte stack `encoded_len` chunked callee at `s.sp = sp`, exposing `VmPreserved s sm`. -/
theorem step_send_chunked_encLen48_call_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {G M_msg : Type} (ext : String → Option (State → State))
    (reprAt : G → BitVec 64 → M_msg → SepProp) (encLen : M_msg → Nat)
    {call_pc : BitVec 64} {s0 s : State}
    (hcallee : subroutine_ok (spqrSendPlacedProg ext) call_pc
      (withStepInv s0 (leafEncLen48Spec reprAt encLen)))
    (msgA sp ret_pc : BitVec 64) (g : G) (m : M_msg) (hfit : encLen m < 2 ^ 64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = msgA) (hinv0 : StepInv s0 s)
    (hP : P = (reprAt g msgA m ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 (encLen m) →
      CalleeSavedPreserved s sm → StepInv s0 sm → VmPreserved s sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((reprAt g msgA m ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  have hsp' : s.sp = (sp + 144#64) - 144#64 := by rw [sp_add_144_sub_144, hsp]
  have hP' : P = (reprAt g msgA m ∗
      stackAt ((sp + 144#64) - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F := by
    rw [sp_add_144_sub_144]; exact hP
  refine step_etv_chunked_encLen48_call_placed hres reprAt encLen hcallee msgA (sp + 144#64) ret_pc
    g m hfit hpc hrun hsp' (sp_add_144_aligned halign) htr hlr hx0 hinv0 hP' ?_
  intro sm hpcm hrunm hspm htrm hx0m hcsm hinvm hvmm
  rw [sp_add_144_sub_144] at hspm
  refine SepWPp.weaken_pre (by rw [sp_add_144_sub_144]; exact Entails.refl _)
    (hnext sm hpcm hrunm hspm htrm hx0m hcsm hinvm hvmm)

/-- Execute `bl encode<Authenticator> [local#3]` (Block `454`) at `s.sp = sp`, threading `A.pool lim st`. -/
theorem step_send_encode_auth_call_placed {resStack : Nat} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    {call_pc : BitVec 64} {s0 s : State}
    (hauth : subroutine_ok (spqrSendPlacedProg ext) call_pc
      (withStepInv s0 (authEncodeExactSpecOf resStack A lim)))
    (authA v cap ptr sp ret_pc : BitVec 64)
    (g : AuthenticatorPBGhost) (auth : AuthenticatorPB) (bs : List (BitVec 8))
    (hfit : bs.length + (encodeMessage ProtoAuthenticator.encodeRaw 2#32 auth).length ≤ cap.toNat)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = authA)
    (hx1 : s.readReg64 .x1 = v) (hinv0 : StepInv s0 s)
    (hP : P = (authenticatorPBPinnedAt A.repAlloc g authA auth ∗ vecU8At A.repAlloc v cap ptr bs ∗
      A.pool lim st s ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((authenticatorPBPinnedAt A.repAlloc g authA auth ∗
          vecU8At A.repAlloc v cap ptr (bs ++ encodeMessage ProtoAuthenticator.encodeRaw 2#32 auth) ∗
          A.pool lim st sm ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  have hsp' : s.sp = (sp + 144#64) - 144#64 := by rw [sp_add_144_sub_144, hsp]
  have hP' : P = (authenticatorPBPinnedAt A.repAlloc g authA auth ∗
      vecU8At A.repAlloc v cap ptr bs ∗ A.pool lim st s ∗
      stackAt ((sp + 144#64) - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F := by
    rw [sp_add_144_sub_144]; exact hP
  refine step_etv_encode_auth_call_prog A lim st hauth authA v cap ptr (sp + 144#64) ret_pc g auth bs
    hfit hpc hrun hsp' (sp_add_144_aligned halign) htr hlr hx0 hx1 hinv0 hP' ?_
  intro sm hpcm hrunm hspm htrm hcsm hinvm
  rw [sp_add_144_sub_144] at hspm
  refine SepWPp.weaken_pre (by rw [sp_add_144_sub_144]; exact Entails.refl _)
    (hnext sm hpcm hrunm hspm htrm hcsm hinvm)

/-- Execute `bl encode<PolynomialEncoder> [local#3]` (Block `456`) at `s.sp = sp` via
    `etvPolyEncoderExactSpecOf resStack A.repAlloc` (`VmPreserved`). -/
theorem step_send_encode_polyEncoder_call_placed {resStack : Nat} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    {call_pc : BitVec 64} {s0 s : State}
    (hpe : subroutine_ok (spqrSendPlacedProg ext) call_pc
      (withStepInv s0 (etvPolyEncoderExactSpecOf resStack A.repAlloc)))
    (encA v cap ptr sp ret_pc : BitVec 64)
    (g : PolynomialEncoderPBGhost) (enc : PolynomialEncoder) (bs : List (BitVec 8))
    (hfit : bs.length + (encodeMessage PolynomialEncoder.encodeRaw 2#32 enc).length ≤ cap.toNat)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = encA)
    (hx1 : s.readReg64 .x1 = v) (hinv0 : StepInv s0 s)
    (hP : P = (polynomialEncoderPBPinnedAt A.repAlloc g encA enc ∗
      vecU8At A.repAlloc v cap ptr bs ∗ A.pool lim st s ∗
      stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → StepInv s0 sm → VmPreserved s sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((polynomialEncoderPBPinnedAt A.repAlloc g encA enc ∗
          vecU8At A.repAlloc v cap ptr (bs ++ encodeMessage PolynomialEncoder.encodeRaw 2#32 enc) ∗
          A.pool lim st sm ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  have hsp' : s.sp = (sp + 144#64) - 144#64 := by rw [sp_add_144_sub_144, hsp]
  have hP' : P = (polynomialEncoderPBPinnedAt A.repAlloc g encA enc ∗
      vecU8At A.repAlloc v cap ptr bs ∗ A.pool lim st s ∗
      stackAt ((sp + 144#64) - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F := by
    rw [sp_add_144_sub_144]; exact hP
  refine step_etv_encode_polyEncoder_call_placed A lim st hpe encA v cap ptr (sp + 144#64) ret_pc g enc bs
    hfit hpc hrun hsp' (sp_add_144_aligned halign) htr hlr hx0 hx1 hinv0 hP' ?_
  intro sm hpcm hrunm hspm htrm hcsm hinvm hvmm
  rw [sp_add_144_sub_144] at hspm
  refine SepWPp.weaken_pre (by rw [sp_add_144_sub_144]; exact Entails.refl _)
    (hnext sm hpcm hrunm hspm htrm hcsm hinvm hvmm)

/-- Execute `bl encode<PolynomialEncoder> [local#3]` (Block `456`) at `s.sp = sp` via
    `etvPolyEncoderBudgetExactSpecOf resStack A lim`. -/
theorem step_send_encode_polyEncoder_budget_call_placed {resStack : Nat} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    {call_pc : BitVec 64} {s0 s : State}
    (hpe : subroutine_ok (spqrSendPlacedProg ext) call_pc
      (withStepInv s0 (etvPolyEncoderBudgetExactSpecOf resStack A lim)))
    (encA v cap ptr sp ret_pc : BitVec 64)
    (g : PolynomialEncoderPBGhost) (enc : PolynomialEncoder) (bs : List (BitVec 8))
    (hfit : bs.length + (encodeMessage PolynomialEncoder.encodeRaw 2#32 enc).length ≤ cap.toNat)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = encA)
    (hx1 : s.readReg64 .x1 = v) (hinv0 : StepInv s0 s)
    (hP : P = (polynomialEncoderPBPinnedAt A.repAlloc g encA enc ∗
      vecU8At A.repAlloc v cap ptr bs ∗ A.pool lim st s ∗
      stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((polynomialEncoderPBPinnedAt A.repAlloc g encA enc ∗
          vecU8At A.repAlloc v cap ptr (bs ++ encodeMessage PolynomialEncoder.encodeRaw 2#32 enc) ∗
          A.pool lim st sm ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  have hsp' : s.sp = (sp + 144#64) - 144#64 := by rw [sp_add_144_sub_144, hsp]
  have hP' : P = (polynomialEncoderPBPinnedAt A.repAlloc g encA enc ∗
      vecU8At A.repAlloc v cap ptr bs ∗ A.pool lim st s ∗
      stackAt ((sp + 144#64) - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F := by
    rw [sp_add_144_sub_144]; exact hP
  refine step_etv_encode_polyEncoder_budget_call_placed A lim st hpe encA v cap ptr (sp + 144#64) ret_pc g enc bs
    hfit hpc hrun hsp' (sp_add_144_aligned halign) htr hlr hx0 hx1 hinv0 hP' ?_
  intro sm hpcm hrunm hspm htrm hcsm hinvm
  rw [sp_add_144_sub_144] at hspm
  refine SepWPp.weaken_pre (by rw [sp_add_144_sub_144]; exact Entails.refl _)
    (hnext sm hpcm hrunm hspm htrm hcsm hinvm)

/-- Execute `bl encode<PolynomialDecoder> [local#3]` (Block `455`) at `s.sp = sp` via
    `etvPolyDecoderExactSpecOf resStack A.repAlloc` (`VmPreserved`). -/
theorem step_send_encode_polyDecoder_call_placed {resStack : Nat} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    {call_pc : BitVec 64} {s0 s : State}
    (hpd : subroutine_ok (spqrSendPlacedProg ext) call_pc
      (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A.repAlloc)))
    (tag : BitVec 32) (decA v cap ptr sp ret_pc : BitVec 64)
    (g : PolynomialDecoderPBGhost) (dec : PolynomialDecoder) (bs : List (BitVec 8))
    (hfit : bs.length + (encodeMessage PolynomialDecoder.encodeRaw tag dec).length ≤ cap.toNat)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc) (hw0 : s.readReg32 .x0 = tag)
    (hx1 : s.readReg64 .x1 = decA) (hx2 : s.readReg64 .x2 = v) (hinv0 : StepInv s0 s)
    (hP : P = (polynomialDecoderPBPinnedAt A.repAlloc g decA dec ∗
      vecU8At A.repAlloc v cap ptr bs ∗ A.pool lim st s ∗
      stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → StepInv s0 sm → VmPreserved s sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((polynomialDecoderPBPinnedAt A.repAlloc g decA dec ∗
          vecU8At A.repAlloc v cap ptr (bs ++ encodeMessage PolynomialDecoder.encodeRaw tag dec) ∗
          A.pool lim st sm ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  have hsp' : s.sp = (sp + 144#64) - 144#64 := by rw [sp_add_144_sub_144, hsp]
  have hP' : P = (polynomialDecoderPBPinnedAt A.repAlloc g decA dec ∗
      vecU8At A.repAlloc v cap ptr bs ∗ A.pool lim st s ∗
      stackAt ((sp + 144#64) - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F := by
    rw [sp_add_144_sub_144]; exact hP
  refine step_etv_encode_polyDecoder_call_placed A lim st hpd tag decA v cap ptr (sp + 144#64) ret_pc g dec bs
    hfit hpc hrun hsp' (sp_add_144_aligned halign) htr hlr hw0 hx1 hx2 hinv0 hP' ?_
  intro sm hpcm hrunm hspm htrm hcsm hinvm hvmm
  rw [sp_add_144_sub_144] at hspm
  refine SepWPp.weaken_pre (by rw [sp_add_144_sub_144]; exact Entails.refl _)
    (hnext sm hpcm hrunm hspm htrm hcsm hinvm hvmm)

/-- Execute `bl encode<PolynomialDecoder> [local#3]` (Block `455`) at `s.sp = sp` via
    `etvPolyDecoderBudgetExactSpecOf resStack A lim`. -/
theorem step_send_encode_polyDecoder_budget_call_placed {resStack : Nat} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    {call_pc : BitVec 64} {s0 s : State}
    (hpd : subroutine_ok (spqrSendPlacedProg ext) call_pc
      (withStepInv s0 (etvPolyDecoderBudgetExactSpecOf resStack A lim)))
    (tag : BitVec 32) (decA v cap ptr sp ret_pc : BitVec 64)
    (g : PolynomialDecoderPBGhost) (dec : PolynomialDecoder) (bs : List (BitVec 8))
    (hfit : bs.length + (encodeMessage PolynomialDecoder.encodeRaw tag dec).length ≤ cap.toNat)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc) (hw0 : s.readReg32 .x0 = tag)
    (hx1 : s.readReg64 .x1 = decA) (hx2 : s.readReg64 .x2 = v) (hinv0 : StepInv s0 s)
    (hP : P = (polynomialDecoderPBPinnedAt A.repAlloc g decA dec ∗
      vecU8At A.repAlloc v cap ptr bs ∗ A.pool lim st s ∗
      stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((polynomialDecoderPBPinnedAt A.repAlloc g decA dec ∗
          vecU8At A.repAlloc v cap ptr (bs ++ encodeMessage PolynomialDecoder.encodeRaw tag dec) ∗
          A.pool lim st sm ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  have hsp' : s.sp = (sp + 144#64) - 144#64 := by rw [sp_add_144_sub_144, hsp]
  have hP' : P = (polynomialDecoderPBPinnedAt A.repAlloc g decA dec ∗
      vecU8At A.repAlloc v cap ptr bs ∗ A.pool lim st s ∗
      stackAt ((sp + 144#64) - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F := by
    rw [sp_add_144_sub_144]; exact hP
  refine step_etv_encode_polyDecoder_budget_call_placed A lim st hpd tag decA v cap ptr (sp + 144#64) ret_pc g dec bs
    hfit hpc hrun hsp' (sp_add_144_aligned halign) htr hlr hw0 hx1 hx2 hinv0 hP' ?_
  intro sm hpcm hrunm hspm htrm hcsm hinvm
  rw [sp_add_144_sub_144] at hspm
  refine SepWPp.weaken_pre (by rw [sp_add_144_sub_144]; exact Entails.refl _)
    (hnext sm hpcm hrunm hspm htrm hcsm hinvm)

/-- Execute `bl encode<EkSentCt1Received> [local#3]` (Block `458`) at `s.sp = sp` via
    `etvEkSentCt1ReceivedEncodeSpecOf resStack A lim` (`VmPreserved`). -/
theorem step_send_encode_ekSentCt1Received_call_placed {resStack : Nat} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    {call_pc : BitVec 64} {s0 s : State}
    (hek : subroutine_ok (spqrSendPlacedProg ext) call_pc
      (withStepInv s0 (etvEkSentCt1ReceivedEncodeSpecOf resStack A lim)))
    (msgA v cap ptr sp ret_pc : BitVec 64)
    (g : Unchunked4PBGhost) (m : V1State.Unchunked.EkSentCt1Received) (bs : List (BitVec 8))
    (hfit : bs.length +
      (encodeMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 m).length ≤ cap.toNat)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = msgA)
    (hx1 : s.readReg64 .x1 = v) (hinv0 : StepInv s0 s)
    (hP : P = (ekSentCt1ReceivedPBPinnedAt A.repAlloc g msgA m ∗
      vecU8At A.repAlloc v cap ptr bs ∗ A.pool lim st s ∗
      stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → StepInv s0 sm → VmPreserved s sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((ekSentCt1ReceivedPBPinnedAt A.repAlloc g msgA m ∗
          vecU8At A.repAlloc v cap ptr
            (bs ++ encodeMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 m) ∗
          A.pool lim st sm ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  have hsp' : s.sp = (sp + 144#64) - 144#64 := by rw [sp_add_144_sub_144, hsp]
  have hP' : P = (ekSentCt1ReceivedPBPinnedAt A.repAlloc g msgA m ∗
      vecU8At A.repAlloc v cap ptr bs ∗ A.pool lim st s ∗
      stackAt ((sp + 144#64) - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F := by
    rw [sp_add_144_sub_144]; exact hP
  refine step_etv_encode_ekSentCt1Received_call_placed A lim st hek msgA v cap ptr (sp + 144#64) ret_pc g m bs
    hfit hpc hrun hsp' (sp_add_144_aligned halign) htr hlr hx0 hx1 hinv0 hP' ?_
  intro sm hpcm hrunm hspm htrm hcsm hinvm hvmm
  rw [sp_add_144_sub_144] at hspm
  refine SepWPp.weaken_pre (by rw [sp_add_144_sub_144]; exact Entails.refl _)
    (hnext sm hpcm hrunm hspm htrm hcsm hinvm hvmm)

/-- Execute `bl encode<EkSentCt1Received> [local#3]` (Block `458`) at `s.sp = sp` via
    `etvEkSentCt1ReceivedBudgetExactSpecOf resStack A lim`. -/
theorem step_send_encode_ekSentCt1Received_budget_call_placed {resStack : Nat} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    {call_pc : BitVec 64} {s0 s : State}
    (hek : subroutine_ok (spqrSendPlacedProg ext) call_pc
      (withStepInv s0 (etvEkSentCt1ReceivedBudgetExactSpecOf resStack A lim)))
    (msgA v cap ptr sp ret_pc : BitVec 64)
    (g : Unchunked4PBGhost) (m : V1State.Unchunked.EkSentCt1Received) (bs : List (BitVec 8))
    (hfit : bs.length +
      (encodeMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 m).length ≤ cap.toNat)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = msgA)
    (hx1 : s.readReg64 .x1 = v) (hinv0 : StepInv s0 s)
    (hP : P = (ekSentCt1ReceivedPBPinnedAt A.repAlloc g msgA m ∗
      vecU8At A.repAlloc v cap ptr bs ∗ A.pool lim st s ∗
      stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((ekSentCt1ReceivedPBPinnedAt A.repAlloc g msgA m ∗
          vecU8At A.repAlloc v cap ptr
            (bs ++ encodeMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 m) ∗
          A.pool lim st sm ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  have hsp' : s.sp = (sp + 144#64) - 144#64 := by rw [sp_add_144_sub_144, hsp]
  have hP' : P = (ekSentCt1ReceivedPBPinnedAt A.repAlloc g msgA m ∗
      vecU8At A.repAlloc v cap ptr bs ∗ A.pool lim st s ∗
      stackAt ((sp + 144#64) - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F := by
    rw [sp_add_144_sub_144]; exact hP
  refine step_etv_encode_ekSentCt1Received_budget_call_placed A lim st hek msgA v cap ptr (sp + 144#64) ret_pc g m bs
    hfit hpc hrun hsp' (sp_add_144_aligned halign) htr hlr hx0 hx1 hinv0 hP' ?_
  intro sm hpcm hrunm hspm htrm hcsm hinvm
  rw [sp_add_144_sub_144] at hspm
  refine SepWPp.weaken_pre (by rw [sp_add_144_sub_144]; exact Entails.refl _)
    (hnext sm hpcm hrunm hspm htrm hcsm hinvm)

/-- Execute `bl encode<Ct1Sent> [local#3]` (Block `459`) at `s.sp = sp` via
    `etvCt1SentEncodeSpecOf resStack A lim` (`VmPreserved`). -/
theorem step_send_encode_ct1Sent_call_placed {resStack : Nat} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    {call_pc : BitVec 64} {s0 s : State}
    (hct1 : subroutine_ok (spqrSendPlacedProg ext) call_pc
      (withStepInv s0 (etvCt1SentEncodeSpecOf resStack A lim)))
    (msgA v cap ptr sp ret_pc : BitVec 64)
    (g : Unchunked5PBGhost) (m : V1State.Unchunked.Ct1Sent) (bs : List (BitVec 8))
    (hfit : bs.length +
      (encodeMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 m).length ≤ cap.toNat)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = msgA)
    (hx1 : s.readReg64 .x1 = v) (hinv0 : StepInv s0 s)
    (hP : P = (ct1SentPBPinnedAt A.repAlloc g msgA m ∗
      vecU8At A.repAlloc v cap ptr bs ∗ A.pool lim st s ∗
      stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → StepInv s0 sm → VmPreserved s sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((ct1SentPBPinnedAt A.repAlloc g msgA m ∗
          vecU8At A.repAlloc v cap ptr
            (bs ++ encodeMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 m) ∗
          A.pool lim st sm ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  have hsp' : s.sp = (sp + 144#64) - 144#64 := by rw [sp_add_144_sub_144, hsp]
  have hP' : P = (ct1SentPBPinnedAt A.repAlloc g msgA m ∗
      vecU8At A.repAlloc v cap ptr bs ∗ A.pool lim st s ∗
      stackAt ((sp + 144#64) - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F := by
    rw [sp_add_144_sub_144]; exact hP
  refine step_etv_encode_ct1Sent_call_placed A lim st hct1 msgA v cap ptr (sp + 144#64) ret_pc g m bs
    hfit hpc hrun hsp' (sp_add_144_aligned halign) htr hlr hx0 hx1 hinv0 hP' ?_
  intro sm hpcm hrunm hspm htrm hcsm hinvm hvmm
  rw [sp_add_144_sub_144] at hspm
  refine SepWPp.weaken_pre (by rw [sp_add_144_sub_144]; exact Entails.refl _)
    (hnext sm hpcm hrunm hspm htrm hcsm hinvm hvmm)

/-- Execute `bl encode<Ct1Sent> [local#3]` (Block `459`) at `s.sp = sp` via
    `etvCt1SentBudgetExactSpecOf resStack A lim`. -/
theorem step_send_encode_ct1Sent_budget_call_placed {resStack : Nat} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    {call_pc : BitVec 64} {s0 s : State}
    (hct1 : subroutine_ok (spqrSendPlacedProg ext) call_pc
      (withStepInv s0 (etvCt1SentBudgetExactSpecOf resStack A lim)))
    (msgA v cap ptr sp ret_pc : BitVec 64)
    (g : Unchunked5PBGhost) (m : V1State.Unchunked.Ct1Sent) (bs : List (BitVec 8))
    (hfit : bs.length +
      (encodeMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 m).length ≤ cap.toNat)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = msgA)
    (hx1 : s.readReg64 .x1 = v) (hinv0 : StepInv s0 s)
    (hP : P = (ct1SentPBPinnedAt A.repAlloc g msgA m ∗
      vecU8At A.repAlloc v cap ptr bs ∗ A.pool lim st s ∗
      stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((ct1SentPBPinnedAt A.repAlloc g msgA m ∗
          vecU8At A.repAlloc v cap ptr
            (bs ++ encodeMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 m) ∗
          A.pool lim st sm ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  have hsp' : s.sp = (sp + 144#64) - 144#64 := by rw [sp_add_144_sub_144, hsp]
  have hP' : P = (ct1SentPBPinnedAt A.repAlloc g msgA m ∗
      vecU8At A.repAlloc v cap ptr bs ∗ A.pool lim st s ∗
      stackAt ((sp + 144#64) - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F := by
    rw [sp_add_144_sub_144]; exact hP
  refine step_etv_encode_ct1Sent_budget_call_placed A lim st hct1 msgA v cap ptr (sp + 144#64) ret_pc g m bs
    hfit hpc hrun hsp' (sp_add_144_aligned halign) htr hlr hx0 hx1 hinv0 hP' ?_
  intro sm hpcm hrunm hspm htrm hcsm hinvm
  rw [sp_add_144_sub_144] at hspm
  refine SepWPp.weaken_pre (by rw [sp_add_144_sub_144]; exact Entails.refl _)
    (hnext sm hpcm hrunm hspm htrm hcsm hinvm)

/-! ## 4. General `roV1` Version of `step_send_inner_len_31b48_ro_placed` (`+4844..+4920`) -/

/-- `spqrSendPlacedEntry + 4844#64 -> spqrSendPlacedEntry + 4920#64` parameterized over `roV1`,
    polymorphic in `Q`, `Qp`, `oom` and exposing `VmPreserved s2 s3`. -/
theorem step_send_inner_len_31b48_ro_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (A : RustAlloc) (ext : String → Option (State → State))
    {roV1 : BitVec 64} {s0 s2 : State}
    (hV1StateLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 484)
      (withStepInv s0 (v1StateEncodedLenRoPinnedSpec A roV1)))
    (sp : BitVec 64) (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63) (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s2.pc = spqrSendPlacedEntry + 4844#64) (hrun : s2.status = .Running)
    (hsp : s2.sp = sp) (htr : s2.trace = s0.trace)
    (hx22 : s2.readReg64 .x22 =
      BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen st.versionNegotiation +
        optChainPBFieldEncodedLen st.chain))
    (hx24 : s2.readReg64 .x24 = sp + 4704#64) (hinv2 : StepInv s0 s2)
    (hP : P = (pqRatchetStatePBPinnedAt A g (sp + 4704#64) st ∗
      (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
      stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ s3 : State,
      s3.pc = spqrSendPlacedEntry + 4920#64 → s3.status = .Running → s3.sp = sp → s3.trace = s0.trace →
      s3.readReg64 .x19 = s2.readReg64 .x19 →
      s3.readReg64 .x20 = optPqRatchetInnerCap g.inner st.inner →
      s3.readReg64 .x21 = s2.readReg64 .x21 → s3.readReg64 .x22 = s2.readReg64 .x22 →
      s3.readReg64 .x23 = s2.readReg64 .x23 →
      s3.readReg64 .x24 = BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st) →
      s3.readReg64 .x25 = s2.readReg64 .x25 → s3.readReg64 .x26 = s2.readReg64 .x26 →
      s3.readReg64 .x27 = s2.readReg64 .x27 → s3.readReg64 .x28 = s2.readReg64 .x28 →
      s3.readReg64 .fp = s2.readReg64 .fp → StepInv s0 s3 → VmPreserved s2 s3 →
      SepWPp (spqrSendPlacedProg ext) ret s3
        ((pqRatchetStatePBPinnedAt A g (sp + 4704#64) st ∗
          (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
          stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s2 P Q Qp oom := by
  subst hP
  refine sepWPp_extract_pure
    ((optPqRatchetInnerCap g.inner st.inner + 3#64 == 0#64) = !st.inner.isSome ∧
     (optPqRatchetInnerCap g.inner st.inner + 3#64 != 0#64) = st.inner.isSome)
    (fun R' hm => ?_) (fun hin_cap => ?_)
  · apply optPqRatchetInnerPBPinnedAt_cap_bounds (A := A) (p := (sp + 4704#64) + 0x80#64)
      (R := optVersionNegotiationPBPinnedAt A g.vn (sp + 4704#64) st.versionNegotiation ∗
        optChainPBPinnedAt A g.chain ((sp + 4704#64) + 0x30#64) st.chain ∗
        (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
        stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
    rw [pqRatchetStatePBPinnedAt] at hm
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  · rw [pqRatchetStatePBPinnedAt, optPqRatchetInnerPBPinnedAt_eq]
    cases hin : st.inner with
    | none =>
      rw [hin] at hin_cap
      simp only [Option.isSome_none, Bool.not_false] at hin_cap
      have ⟨hadd1, hadd2⟩ := adds_no_overflow_of_eq (a := 0)
        (b := optVersionNegotiationPBFieldEncodedLen st.versionNegotiation +
          optChainPBFieldEncodedLen st.chain)
        (c := pqRatchetStatePBEncodedLen st)
        (by unfold pqRatchetStatePBEncodedLen; rw [hin]; dsimp [optPqRatchetInnerPBFieldEncodedLen])
        (by omega)
      dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
      apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_427).base + 4920#64)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv
      refine SepWPp.weaken_pre ?_
        (hnext _
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by rw [hin]; simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (hinv2.trans hinv.1) hinv.2)
      rw [pqRatchetStatePBPinnedAt, optPqRatchetInnerPBPinnedAt_eq, hin]
      exact Entails.of_eq (by sep_ac_rfl)
    | some innerVal =>
      cases innerVal with
      | v1 v1s =>
        rw [hin] at hin_cap
        simp only [Option.isSome_some, Bool.not_true] at hin_cap
        have ⟨hfit, hopt_lt, hvar_lt⟩ := v1StatePBEncodedLen_lt_of_state hin hlen
        have hls := cmp_ls_false_of_lt hvar_lt hopt_lt
        have hopt_in := bv_optInner_some_eq v1s
        have ⟨hadd1, hadd2⟩ := adds_no_overflow_of_eq
          (a := optPqRatchetInnerPBFieldEncodedLen (some (.v1 v1s)))
          (b := optVersionNegotiationPBFieldEncodedLen st.versionNegotiation +
            optChainPBFieldEncodedLen st.chain)
          (c := pqRatchetStatePBEncodedLen st)
          (by unfold pqRatchetStatePBEncodedLen; rw [hin])
          (by omega)
        dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
        apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 484)
        wp_steps
        apply sepWP_done_vm
          (by simp only [arm64_norm, ls_resolve_rel_427_blk_484, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hinv_bl
        have hres176 : resStack + 176 < 2 ^ 64 := by omega
        refine sepWPp_call_cs_noPanic (x := PinnedEncLenGhost.mk ((sp + 4704#64) + 0x80#64) g.inner v1s)
          (F := optVersionNegotiationPBPinnedAt A g.vn (sp + 4704#64) st.versionNegotiation ∗
            optChainPBPinnedAt A g.chain ((sp + 4704#64) + 0x30#64) st.chain ∗
            memRegion (sp - BitVec.ofNat 64 (encodeToVecCalleeStackOf resStack)) (96 + resStack) ∗ F)
          hV1StateLen
          (by simp only [arm64_norm, ls_resolve_rel_427_blk_484])
          (by simp only [arm64_norm, *])
          (by simp only [State.spAligned, arm64_norm, hsp, beq_iff_eq]; exact halign)
          (ret_pc := (blkPl_427).base + 4872#64) (by simp only [arm64_norm]) ?_ ?_ ?_ ?_ ?_
        · intro R' hm
          rw [← optPqRatchetInnerPBPinnedAt_eq A g.inner ((sp + 4704#64) + 0x80#64) (some (.v1 v1s)),
            optPqRatchetInnerPBPinnedAt,
            stackAt_callee_eq_v1StateEncodedLen hres176 sp] at hm
          simp only [arm64_norm] at hm
          simp only [withStepInv, v1StateEncodedLenRoPinnedSpec, withVmPreserved,
            CryptoVerification.SpqrV1.ProtoRepr.v1StateEncodedLenRoPinnedSpec, arm64_norm, hsp, hx24,
            sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨⟨hinv2.trans hinv_bl.1, hfit⟩, ?_⟩
          exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
        · intro _ _ _ _ hm; exact (not_satisfies_false_sepConj hm).elim
        · intro _ _ _ hm; exact (not_satisfies_false_sepConj hm).elim
        · intro _ _ _ hm; exact (not_satisfies_false_sepConj hm).elim
        · intro sm hpcm hrunm hspm hcsm hinv_call
          simp only [arm64_norm, hsp] at hspm
          dsimp only [withStepInv, v1StateEncodedLenRoPinnedSpec, withVmPreserved,
            CryptoVerification.SpqrV1.ProtoRepr.v1StateEncodedLenRoPinnedSpec]
          simp only [sepConj_assoc]
          refine SepWPp.pure_elim fun hvm_call => SepWPp.pure_elim fun ⟨hx0m, htrm⟩ => ?_
          simp only [arm64_norm, htr] at htrm
          rcases hcsm with ⟨hx19m, hx20m, hx21m, hx22m, hx23m, hx24m, hx25m, hx26m, hx27m, hx28m, hfpm, _⟩
          simp only [arm64_norm, hx22, hx24] at hx19m hx20m hx21m hx22m hx23m hx24m hx25m hx26m hx27m hx28m hfpm
          apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_427).base + 4920#64)
          wp_steps
          apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, wp_norm, *])
          intro hinv_post
          refine SepWPp.weaken_pre ?_
            (hnext _
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by rw [hin]; simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *])
              (((hinv2.trans hinv_bl.1).trans hinv_call).trans hinv_post.1)
              ((hinv_bl.2.trans hvm_call).trans hinv_post.2))
          rw [pqRatchetStatePBPinnedAt, hin, optPqRatchetInnerPBPinnedAt,
            stackAt_callee_eq_v1StateEncodedLen hres176 sp]
          simp only [arm64_norm, hsp]
          exact Entails.of_eq (by sep_ac_rfl)

theorem step_send_inner_len_31b48_ro_pool_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (ext : String → Option (State → State))
    {roV1 : BitVec 64} {s0 s2 : State}
    (hV1StateLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 484)
      (withStepInv s0 (v1StateEncodedLenRoPinnedSpec A.repAlloc roV1)))
    (sp : BitVec 64) (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63) (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s2.pc = spqrSendPlacedEntry + 4844#64) (hrun : s2.status = .Running)
    (hsp : s2.sp = sp) (htr : s2.trace = s0.trace)
    (hx22 : s2.readReg64 .x22 =
      BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen st.versionNegotiation +
        optChainPBFieldEncodedLen st.chain))
    (hx24 : s2.readReg64 .x24 = sp + 4704#64) (hinv2 : StepInv s0 s2)
    (hP : P = (pqRatchetStatePBPinnedAt A.repAlloc g (sp + 4704#64) st ∗
      (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
      A.pool lim st0 s2 ∗
      stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ s3 : State,
      s3.pc = spqrSendPlacedEntry + 4920#64 → s3.status = .Running → s3.sp = sp → s3.trace = s0.trace →
      s3.readReg64 .x19 = s2.readReg64 .x19 →
      s3.readReg64 .x20 = optPqRatchetInnerCap g.inner st.inner →
      s3.readReg64 .x21 = s2.readReg64 .x21 → s3.readReg64 .x22 = s2.readReg64 .x22 →
      s3.readReg64 .x23 = s2.readReg64 .x23 →
      s3.readReg64 .x24 = BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st) →
      s3.readReg64 .x25 = s2.readReg64 .x25 → s3.readReg64 .x26 = s2.readReg64 .x26 →
      s3.readReg64 .x27 = s2.readReg64 .x27 → s3.readReg64 .x28 = s2.readReg64 .x28 →
      s3.readReg64 .fp = s2.readReg64 .fp → StepInv s0 s3 →
      SepWPp (spqrSendPlacedProg ext) ret s3
        ((pqRatchetStatePBPinnedAt A.repAlloc g (sp + 4704#64) st ∗
          (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
          A.pool lim st0 s3 ∗
          stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s2 P Q Qp oom := by
  refine step_send_inner_len_31b48_ro_placed hres A.repAlloc ext hV1StateLen sp g st hlen halign
    (F := A.pool lim st0 s2 ∗ F)
    hpc hrun hsp htr hx22 hx24 hinv2 (by rw [hP]; sep_ac_rfl) ?_
  intro s3 hpcs3 hruns3 hsps3 htrs3 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 hfp hinv3 hvm3
  have hpool : A.pool lim st0 s2 = A.pool lim st0 s3 := (A.pool_of_vmPreserved hvm3).symm
  refine SepWPp.weaken_pre (by rw [hpool]; exact Entails.of_eq (by sep_ac_rfl))
    (hnext s3 hpcs3 hruns3 hsps3 htrs3 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 hfp hinv3)

end LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerHeaderPlacedBudgetAux

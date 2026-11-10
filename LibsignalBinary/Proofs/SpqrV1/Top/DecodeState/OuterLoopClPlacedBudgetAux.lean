/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainLoopClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.OuterLoopPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.V1StateStepClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoopClPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainLoopPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.OuterLoopPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.V1StateStepPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiation
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoop
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoopPlaced
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Code-Loaded Post-Loop Exit & Tag Dispatch for `spqr::decode_state` (Block `325`)

Proves the budget-threaded code-loaded post-loop success exit (`+1676..+1724` to `+2500`) and
outer-loop tag dispatch (`+160`) for `spqr::decode_state`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.OuterLoopClPlacedBudgetAux

open Arm64 Arm64.Obj ProofLib SepProp
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open CryptoVerification (LibsignalPlacement lsmpl lsρ)
open CryptoVerification.SpqrV1.Top.DecodeState.Placed (blkPC_325 blkPl_325)
open scoped CryptoVerification.SpqrV1.Top.DecodeState.Placed
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalProtoCodec (WireType)
open CryptoVerification.LibsignalTripleRatchet (sessionMemcpySpec)
open CryptoVerification.LibsignalTripleRatchet.Prost (IsDropSuffix sliceCursorAfter)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (codecWireTypeToProto mergeLoopBin v1StateJumpTablesPlacedAt)
open CryptoVerification.LibsignalSpqrV1 (PqRatchetState spqrDecodeState)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost TraceVRegs V1InnerHeapPred decodeStatePlacedEntry decodeStatePlacedProg
   decodeStateResultAt frame_4chunks_to_1296 head16_tail336_entails_protoPqRatchetStateAt
   lower_352_fold none2Cap pqRatchetState_mergeField_other pqRatchetState_mergeField_tag1
   pqRatchetState_mergeField_tag2 protoPqRatchetStateAt_entails_head16_tail336
   protoPqRatchetStateCapOkAt relocProtoPqRatchetStateTailAt scratch_688_fold_48
   sp_sub_1392_aligned stackAt_of_callee stackAt_to_callee tag_cmp32_of_gt tag_setWidth32_ofNat)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefsBudget
  (V1StateMergeEnv V1StateMergePostEnv optInnerStatePolyCapBound
   optInnerStatePolyCapBound_mono_len v1StateMergePostEnv_imp_pre)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget.FitsEnv
  (decodeStateLoop_head decodeStateLoop_mono decodeStateLoop_split)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget
  (DecodeStateEnv DecodeStateIterEnv DecodeStateLoopEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsClPlacedBudget
  (DecodeStateCalleeContractsClPlaced DecodeStateCalleeContractsClPlacedX)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget
  (decodeStatePanicPostPlaced decodeStatePanicPostPlacedOfEnv decodeStatePostPlaced
   decodeStatePostPlacedOfEnv decodeState_epilogue_53e60_placed_ofEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubBudget (decodeStateErrFramePlaced)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubPlacedBudgetAux
  (fitsEnv_decodeErrorPush_of_loop)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget
  (SepWPpIPlaced decodeStateLoopCommonPlaced loopCommon_cursor_to_errFrame_placed)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.OuterLoopPlacedBudgetAux
  (decodeState_codecWireTypeToProto_eq optInnerStatePolyCapBound_of_v1State_merge
   pqRatchetState_tag3_some_inv skipField3Env_ok_nil spqrMergeLoopEnv_to_decodeStateLoopEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.V1StateStepClPlacedBudget
  (decodeState_outer_skip_53664_cl_placed_ofEnv decodeState_v1_entry_535d4_cl_placed_ofEnv
   pqRatchetStateV1OrDefault)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainLoopClPlacedBudget
  (decodeState_chain_entry_53590_cl_placed_ofEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoopClPlacedBudget
  (bytesMerge3Det_of_contractsClPlacedX decodeState_vn_entry_53554_cl_placed_ofEnv)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr Obj.lookup v1StateJumpTablesPlacedAt
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local irreducible] mergeMessage mergeLoopBin CryptoVerification.LibsignalSpqrV1.Proto.spqrDecodeState

/-! ## 1. Post-Loop Success Exit (`+1676..+1724`) -/

private theorem head_ne_none2Cap_branch {w : BitVec 64} (hne : w ≠ none2Cap) :
    (w + 2#64 == 0#64) = false ∧ (w + 2#64 != 0#64) = true := by
  have h0 : w + 2#64 ≠ 0#64 := by
    intro h
    apply hne
    change w = -2#64
    bv_omega
  exact ⟨beq_eq_false_iff_ne.mpr h0, bne_iff_ne.mpr h0⟩

private theorem state_1040_fold_352 (sp w0 w1 : BitVec 64) {bs336 : List (BitVec 8)}
    (hlen : bs336.length = 336) :
    ((sp - 1040#64) ↦₆₄ w0) ∗ ((sp - 1032#64) ↦₆₄ w1) ∗ ((sp - 1024#64) ↦ₛ bs336) ⊢
      memRegion (sp - 1040#64) 352 := by
  have h16 : ((sp - 1040#64) ↦₆₄ w0) ∗ ((sp - 1032#64) ↦₆₄ w1) ⊢ memRegion (sp - 1040#64) 16 := by
    rw [ProofLib.memRegion_split' (b := sp - 1040#64) (n := 8) (k := 8)
        (b' := sp - 1032#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono
      (ProofLib.pointsTo64_entails_memRegion _ w0)
      (ProofLib.pointsTo64_entails_memRegion _ w1)
  have h336 : ((sp - 1024#64) ↦ₛ bs336) ⊢ memRegion (sp - 1024#64) 336 := by
    rw [← hlen]; exact pointsToBytes_entails_memRegion (sp - 1024#64) bs336
  rw [ProofLib.memRegion_split' (b := sp - 1040#64) (n := 16) (k := 336)
      (b' := sp - 1024#64) rfl (by bv_omega) (by decide)]
  have hassoc :
      ((sp - 1040#64) ↦₆₄ w0) ∗ ((sp - 1032#64) ↦₆₄ w1) ∗ ((sp - 1024#64) ↦ₛ bs336) =
      (((sp - 1040#64) ↦₆₄ w0) ∗ ((sp - 1032#64) ↦₆₄ w1)) ∗ ((sp - 1024#64) ↦ₛ bs336) := by
    sep_ac_rfl
  rw [hassoc]
  exact sepConj_mono h16 h336

private theorem memRegion_352_split_head16_tail336 (outPtr : BitVec 64) :
    memRegion outPtr 352 ⊢
      memRegion (outPtr + 16#64) 336 ∗
      (∃∗ out1 : BitVec 64, ∃∗ out0 : BitVec 64,
        (outPtr ↦₆₄ out0) ∗ ((outPtr + 8#64) ↦₆₄ out1)) := by
  rw [ProofLib.memRegion_split' (b := outPtr) (n := 8) (k := 344)
      (b' := outPtr + 8#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := outPtr + 8#64) (n := 8) (k := 336)
      (b' := outPtr + 16#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_eight outPtr,
    ProofLib.memRegion_eight (outPtr + 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  exact Entails.of_eq (by sep_ac_rfl)

/-- Envelope-parameterized code-loaded post-loop success exit (`+1676..+1724`, 13 instructions) -> `+2500`. -/
theorem decodeState_ok_exit_53b28_cl_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (w0_scr : BitVec 64) (curSt : PqRatchetState)
    (hok : spqrDecodeState x.st.bytes = .ok curSt)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (henv : ∃ evs, PostEnv x evs ∧ M.stepEvents evs st0 = st)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 1676#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hP : P =
      ((s0.sp - 688#64) ↦₆₄ w0_scr) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes [] ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) 0 curSt ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s) :
    SepWP (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post := by
  have hmemcpy := hc.session_memcpy allocHookStack (Nat.le_refl _) (by decide)
  simp only [withVmPreserved, sessionMemcpySpec] at hmemcpy
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  refine SepWP.fold (loopCommon_cursor_to_errFrame_placed H_inner A lim st x [] 0 curSt s0 s)
    (by sep_focus) ?_
  refine SepWP.fold (scratch_688_fold_48 s0.sp w0_scr)
    (by dsimp only [decodeStateErrFramePlaced]; sep_focus) ?_
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateErrFramePlaced] at hpc hmemcpy ⊢
  refine SepWP.fold (protoPqRatchetStateAt_entails_head16_tail336 H_inner A.repAlloc
    (s0.sp - 1040#64) curSt) (by sep_focus) ?_
  wp_pull_exists
  rename_i w0 w1 bs336
  wp_focus_pure; rintro ⟨hw0_ne, hbs336_len⟩
  have ⟨hcmn_eq_f, hcmn_ne_t⟩ := head_ne_none2Cap_branch hw0_ne
  rw [ProofLib.memRegion_split' (b := s0.sp - 1392#64) (n := 336) (k := 16)
      (b' := s0.sp - 1056#64) rfl (by bv_omega) (by decide)]
  refine SepWP.fold (stackAt_to_callee (s0.sp - 1392#64) allocHookStack (by decide))
    (by sep_focus) ?_
  wp_steps_sync_pool (lsρ "memcpy")
  try simp only [State.setMem_setMem]
  wp_apply
  wp_conv_pre => simp only [*]
  refine ProofLib.SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
  refine SepWP.fold (state_1040_fold_352 s0.sp w0 w1 hbs336_len) (by sep_focus) ?_
  refine SepWP.fold (memRegion_352_split_head16_tail336 x.outPtr) (by sep_focus) ?_
  wp_pull_exists
  wp_steps_sync_pool (lsρ "memcpy")
  try simp only [State.setMem_setMem]
  wp_apply
  wp_conv_pre => simp only [*]
  refine ProofLib.SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
  refine SepWP.fold (stackAt_of_callee (s0.sp - 1392#64) allocHookStack (by decide))
    (by sep_focus) ?_
  have h336_sp : ((s0.sp - 1392#64) ↦ₛ bs336) ⊢ memRegion (s0.sp - 1392#64) 336 := by
    rw [← hbs336_len]; exact pointsToBytes_entails_memRegion (s0.sp - 1392#64) bs336
  refine SepWP.fold h336_sp (by sep_focus) ?_
  refine SepWP.fold (lower_352_fold s0.sp) (by sep_focus) ?_
  refine SepWP.fold (frame_4chunks_to_1296 s0.sp) (by sep_focus) ?_
  wp_steps_sync_pool ((blkPl_325).base + 2500#64)
  try simp only [State.setMem_setMem]
  have hfold_ok :
      (x.outPtr ↦₆₄ w0) ∗ ((x.outPtr + 8#64) ↦₆₄ w1) ∗ ((x.outPtr + 16#64) ↦ₛ bs336) ∗
        (relocProtoPqRatchetStateTailAt H_inner A.repAlloc w0 w1 curSt).1 bs336 ⊢
        decodeStateResultAt H_inner A.repAlloc x.outPtr (spqrDecodeState x.st.bytes) := by
    rw [hok]
    exact head16_tail336_entails_protoPqRatchetStateAt H_inner A.repAlloc
      x.outPtr w0 w1 bs336 curSt hbs336_len
  refine SepWP.fold hfold_ok (by sep_focus) ?_
  exact decodeState_epilogue_53e60_placed_ofEnv x st0 st s0 _ _ R post hpost henv
    (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    hs0A
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]; sep_ac_rfl)

theorem decodeState_ok_exit_53b28_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (w0_scr : BitVec 64) (curSt : PqRatchetState)
    (hok : spqrDecodeState x.st.bytes = .ok curSt)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (henv : ∃ evs, DecodeStateEnv x evs ∧ M.stepEvents evs st0 = st)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 1676#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hP : P =
      ((s0.sp - 688#64) ↦₆₄ w0_scr) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes [] ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) 0 curSt ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s) :
    SepWP (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post :=
  decodeState_ok_exit_53b28_cl_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st w0_scr curSt hok s0 s P R post hpost henv hs0A hpc hrun hsp htr hx19 hx22 hP

/-! ## 2. Outer Loop Tag Dispatch (`+160..+180`, Code-Loaded) -/

/-- Envelope-parameterized code-loaded outer loop tag dispatch at `+160` (6 instructions)
given `1 ≤ tag < 2 ^ 29`: dispatches `tag = 3` (`+312`), `tag = 2` (`+244`), `tag = 1` (`+184`),
and `tag ∉ {1, 2, 3}` (`+456`), reaching `entry + 1576` on success while maintaining
`hlinks`, `hpoly`, `hacc`, `hst`, and `hFit` (`8 * (rest1.length - rest2.length)` steps). -/
theorem decodeState_outer_dispatch_5353c_cl_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (evs_acc : List AllocEvent) (f rem : Nat)
    (w0 : BitVec 64) (curSt : PqRatchetState)
    (rest1 : List (BitVec 8)) (tag : Nat) (iwt : WireType)
    (htag1_le : 1 ≤ tag) (htag29 : tag < 2 ^ 29)
    (hrest1_le : rest1.length ≤ x.st.bytes.length) (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hlinks : (curSt.chain.getD default).links.length + rest1.length ≤ 2 * x.st.bytes.length + 4)
    (hpoly : optInnerStatePolyCapBound (pqRatchetStateV1OrDefault curSt).innerState rest1.length ≤
      2 * x.st.bytes.length + 16)
    (herr_of_none :
      (match (PqRatchetState.mergeField curSt (BitVec.ofNat 32 tag) (codecWireTypeToProto iwt) rest1 100).toOption with
       | none => none
       | some (st', rest2) => mergeLoopBin PqRatchetState.mergeField rest2.length st' rest2 0 100) = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (hacc : DecodeStateLoopEnv f x.st.bytes.length (2 * x.st.bytes.length + 16) evs_acc)
    (hst : M.stepEvents evs_acc st0 = st)
    (hFit : FitsEnv M lim st
      (DecodeStateLoopEnv rem x.st.bytes.length (2 * x.st.bytes.length + 16)))
    (hrem : 8 * rest1.length + 24 ≤ rem)
    (hf : f + 8 * rest1.length + 24 ≤ 16 * x.st.bytes.length + 32)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (hpost_env : ∀ evs, DecodeStateEnv x evs → PostEnv x evs)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 160#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 tag)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = 8#64) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest1.length curSt ∗
      memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hnext : ∀ (w0' : BitVec 64) (st' : PqRatchetState) (rest2 : List (BitVec 8))
        (evs_step : List AllocEvent) (sf : State) (P' : SepProp),
      rest2.length ≤ rest1.length → IsDropSuffix rest1 rest2 →
      (PqRatchetState.mergeField curSt (BitVec.ofNat 32 tag) (codecWireTypeToProto iwt) rest1 100).toOption =
        some (st', rest2) →
      (st'.chain.getD default).links.length + rest2.length ≤ 2 * x.st.bytes.length + 4 →
      optInnerStatePolyCapBound (pqRatchetStateV1OrDefault st').innerState rest2.length ≤
        2 * x.st.bytes.length + 16 →
      DecodeStateLoopEnv (f + 8 * (rest1.length - rest2.length)) x.st.bytes.length
        (2 * x.st.bytes.length + 16) (evs_acc ++ evs_step) →
      M.stepEvents (evs_acc ++ evs_step) st0 = M.stepEvents evs_step st →
      FitsEnv M lim (M.stepEvents evs_step st)
        (DecodeStateLoopEnv (rem - 8 * (rest1.length - rest2.length)) x.st.bytes.length
          (2 * x.st.bytes.length + 16)) →
      sf.pc = decodeStatePlacedEntry + 1576#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = BitVec.ofNat 64 rest2.length →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = 8#64 → sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0') ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length st' ∗
        memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_step st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry] at hpc ⊢
  by_cases htag3 : tag = 3
  · subst htag3
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 312#64)
    wp_steps 2
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
    refine decodeState_v1_entry_535d4_cl_placed_ofEnv
      (V1PreEnv := V1StateMergeEnv) (V1PostEnv := V1StateMergePostEnv)
      (PreEnv := PreEnv) (PostEnv := PostEnv) (v27 := 8#64)
      hc.toDecodeStateCalleeContractsClPlaced hc.v1StateMerge
      x st0 st w0 curSt rest1 iwt hrest1_le hrest1_suf hlen_bound
      (fun hnone => herr_of_none (by
        rw [show BitVec.ofNat 32 3 = 3#32 from rfl, hnone]))
      s0 _ _ R post hpost
      (fun _ => hFit.mono fun evs hevs => by
        dsimp only [V1StateMergeEnv] at hevs
        have hdl := spqrMergeLoopEnv_to_decodeStateLoopEnv hevs (by omega)
        exact hdl.mono (by omega) hrest1_le hpoly)
      (fun evs_v1 evs_drop n _ _ hv1 hdrop hn => by
        have hv1' := v1StateMergePostEnv_imp_pre hv1
        dsimp only [V1StateMergeEnv] at hv1'
        have hv1_pre := spqrMergeLoopEnv_to_decodeStateLoopEnv hv1' (by omega)
        have hv1_l : DecodeStateLoopEnv (8 * rest1.length + 16) x.st.bytes.length
            (2 * x.st.bytes.length + 16) evs_v1 :=
          hv1_pre.mono (Nat.le_refl _) hrest1_le hpoly
        have hdr_l : DecodeStateLoopEnv 1 x.st.bytes.length
            (2 * x.st.bytes.length + 16) evs_drop :=
          DecodeStateLoopEnv.single (fuel := 0) (.deallocs hdrop)
        have h12 := hv1_l.append hdr_l
        have hFit1 : FitsEnv M lim (M.stepEvents (evs_v1 ++ evs_drop) st)
            (DecodeStateLoopEnv 1 x.st.bytes.length (2 * x.st.bytes.length + 16)) :=
          decodeStateLoop_split h12
            (decodeStateLoop_mono (by omega) (Nat.le_refl _) (Nat.le_refl _) hFit)
        rw [M.stepEvents_append] at hFit1
        exact fitsEnv_decodeErrorPush_of_loop hn (by decide) hFit1)
      (fun evs_v1 evs_drop evs_p evs_f n _ _ hv1 hdrop hn hp hf_evs => by
        have hv1' := v1StateMergePostEnv_imp_pre hv1
        dsimp only [V1StateMergeEnv] at hv1'
        have hv1_pre := spqrMergeLoopEnv_to_decodeStateLoopEnv hv1' (by omega)
        have hv1_l : DecodeStateLoopEnv (8 * rest1.length + 16) x.st.bytes.length
            (2 * x.st.bytes.length + 16) evs_v1 :=
          hv1_pre.mono (Nat.le_refl _) hrest1_le hpoly
        have hdr_l : DecodeStateLoopEnv 1 x.st.bytes.length
            (2 * x.st.bytes.length + 16) evs_drop :=
          DecodeStateLoopEnv.single (fuel := 0) (.deallocs hdrop)
        have hp_l : DecodeStateLoopEnv 1 x.st.bytes.length
            (2 * x.st.bytes.length + 16) evs_p :=
          DecodeStateLoopEnv.single (fuel := 0) (.pushErr hn hp)
        have hf_l : DecodeStateLoopEnv 1 x.st.bytes.length
            (2 * x.st.bytes.length + 16) evs_f :=
          DecodeStateLoopEnv.single (fuel := 0) (.deallocs hf_evs)
        have htot := (((hacc.append hv1_l).append hdr_l).append hp_l).append hf_l
        refine ⟨((((evs_acc ++ evs_v1) ++ evs_drop) ++ evs_p) ++ evs_f),
          hpost_env _ (htot.mono_fuel (by omega)), ?_⟩
        rw [M.stepEvents_append, M.stepEvents_append, M.stepEvents_append, M.stepEvents_append, hst])
      hs0A
      (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun]) (by simp only [wp_norm, arm64_norm, hsp])
      (by simp only [wp_norm, arm64_norm, htr]) (by simp only [wp_norm, arm64_norm, hx0])
      (by simp only [wp_norm, arm64_norm, hx19]) (by simp only [wp_norm, arm64_norm, hx21])
      (by simp only [wp_norm, arm64_norm, hx22]) (by simp only [wp_norm, arm64_norm, hx23])
      (by simp only [wp_norm, arm64_norm, hx24]) (by simp only [wp_norm, arm64_norm, hx25])
      (by simp only [wp_norm, arm64_norm, hx26]) (by simp only [wp_norm, arm64_norm, hx27])
      (by simp only [wp_norm, arm64_norm, hx28]) (by simp only [wp_norm, arm64_norm, hx29])
      (by
        dsimp only [decodeStateLoopCommonPlaced, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23,
          Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
        try simp only [wp_norm, arm64_norm]
        try sep_ac_rfl) ?_
    intro w0' st' rest2 evs_v1 sf P' hmf _ hv1 hle2 hsuf2
    obtain ⟨v1', hv1_ok, hst'_eq⟩ := pqRatchetState_tag3_some_inv hmf
    have hv1_step : DecodeStateLoopEnv (8 * (rest1.length - rest2.length)) x.st.bytes.length
        (2 * x.st.bytes.length + 16) evs_v1 := by
      dsimp only [V1StateMergePostEnv] at hv1
      rw [hv1_ok] at hv1
      have hv1_pre := spqrMergeLoopEnv_to_decodeStateLoopEnv hv1 (by omega)
      exact hv1_pre.mono (Nat.le_refl _) hrest1_le hpoly
    have hlinks' : (st'.chain.getD default).links.length + rest2.length ≤
        2 * x.st.bytes.length + 4 := by
      rw [hst'_eq]; dsimp only; omega
    have hpoly' : optInnerStatePolyCapBound (pqRatchetStateV1OrDefault st').innerState rest2.length ≤
        2 * x.st.bytes.length + 16 := by
      rw [hst'_eq]; dsimp only [pqRatchetStateV1OrDefault]
      exact Nat.le_trans (optInnerStatePolyCapBound_of_v1State_merge hv1_ok) hpoly
    have hFit' : FitsEnv M lim (M.stepEvents evs_v1 st)
        (DecodeStateLoopEnv (rem - 8 * (rest1.length - rest2.length)) x.st.bytes.length
          (2 * x.st.bytes.length + 16)) :=
      decodeStateLoop_split hv1_step
        (decodeStateLoop_mono (by omega) (Nat.le_refl _) (Nat.le_refl _) hFit)
    exact hnext w0' st' rest2 evs_v1 sf P' hle2 hsuf2
      (by rw [show BitVec.ofNat 32 3 = 3#32 from rfl]; exact hmf)
      hlinks' hpoly' (hacc.append hv1_step) (by rw [M.stepEvents_append, hst]) hFit'
  · by_cases htag2 : tag = 2
    · subst htag2
      rcases curSt with ⟨optVn, optCh, inner⟩
      have htag2_eq := pqRatchetState_mergeField_tag2 ⟨optVn, optCh, inner⟩ iwt rest1 100
      rw [decodeState_codecWireTypeToProto_eq] at htag2_eq
      apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 244#64)
      wp_steps 4
      apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
      refine decodeState_chain_entry_53590_cl_placed_ofEnv
        (PreEnv := PreEnv) (PostEnv := PostEnv)
        hc x st0 st evs_acc f rem w0 optVn optCh inner rest1 iwt
        hrest1_le hrest1_suf hlen_bound hlinks
        (fun hnone => herr_of_none (by
          rw [show BitVec.ofNat 32 2 = 2#32 from rfl, htag2_eq]
          dsimp only; rw [hnone]; rfl))
        hacc hst hFit (by omega) (by omega) s0 _ _ R post hpost hpost_env hs0A
        (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm, hrun]) (by simp only [wp_norm, arm64_norm, hsp])
        (by simp only [wp_norm, arm64_norm, htr]) (by simp only [wp_norm, arm64_norm, hx0])
        (by simp only [wp_norm, arm64_norm, hx19]) (by simp only [wp_norm, arm64_norm, hx21])
        (by simp only [wp_norm, arm64_norm, hx22]) (by simp only [wp_norm, arm64_norm, hx23])
        (by simp only [wp_norm, arm64_norm, hx24]) (by simp only [wp_norm, arm64_norm, hx25])
        (by simp only [wp_norm, arm64_norm, hx26]) (by simp only [wp_norm, arm64_norm, hx27])
        (by simp only [wp_norm, arm64_norm, hx28]) (by simp only [wp_norm, arm64_norm, hx29])
        (by
          dsimp only [decodeStateLoopCommonPlaced, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23,
            Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
          try simp only [wp_norm, arm64_norm]
          try sep_ac_rfl) ?_
      intro w0' ch' rest2 evs_ch sf P' hmf hlinks2 hacc2 hst2 hFit2 hle2 hsuf2
      exact hnext w0' ⟨optVn, some ch', inner⟩ rest2 evs_ch sf P' hle2 hsuf2
        (by rw [show BitVec.ofNat 32 2 = 2#32 from rfl, htag2_eq]
            dsimp only; rw [hmf]; rfl)
        (by dsimp only; exact Nat.le_trans hlinks2 hlinks)
        (Nat.le_trans (optInnerStatePolyCapBound_mono_len hle2) hpoly)
        (hacc2.mono_fuel (by omega)) hst2
        (decodeStateLoop_mono (by omega) (Nat.le_refl _) (Nat.le_refl _) hFit2)
    · by_cases htag1 : tag = 1
      · subst htag1
        rcases curSt with ⟨optVn, optCh, inner⟩
        have htag1_eq := pqRatchetState_mergeField_tag1 ⟨optVn, optCh, inner⟩ iwt rest1 100
        rw [decodeState_codecWireTypeToProto_eq] at htag1_eq
        apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 184#64)
        wp_steps 6
        apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
        refine decodeState_vn_entry_53554_cl_placed_ofEnv
          (maxLen := x.st.bytes.length) (polyCapBound := 2 * x.st.bytes.length + 16)
          (PreEnv := PreEnv) (PostEnv := PostEnv) (v27 := 8#64)
          hc.toDecodeStateCalleeContractsClPlaced (bytesMerge3Det_of_contractsClPlacedX hc)
          x st0 st w0 optVn optCh inner rest1 iwt
          hrest1_le hrest1_suf hlen_bound (Nat.le_refl _) (by omega)
          (fun hnone => herr_of_none (by
            rw [show BitVec.ofNat 32 1 = 1#32 from rfl, htag1_eq]
            dsimp only; rw [hnone]; rfl))
          s0 _ _ R post hpost
          (decodeStateLoop_mono (by omega) (Nat.le_refl _) (Nat.le_refl _) hFit)
          (fun evs_err herr_loop => by
            have htot := hacc.append herr_loop
            refine ⟨evs_acc ++ evs_err,
              hpost_env _ (htot.mono_fuel (by omega)), ?_⟩
            rw [M.stepEvents_append, hst])
          hs0A
          (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm, hrun]) (by simp only [wp_norm, arm64_norm, hsp])
          (by simp only [wp_norm, arm64_norm, htr]) (by simp only [wp_norm, arm64_norm, hx0])
          (by simp only [wp_norm, arm64_norm, hx19]) (by simp only [wp_norm, arm64_norm, hx21])
          (by simp only [wp_norm, arm64_norm, hx22]) (by simp only [wp_norm, arm64_norm, hx23])
          (by simp only [wp_norm, arm64_norm, hx24]) (by simp only [wp_norm, arm64_norm, hx25])
          (by simp only [wp_norm, arm64_norm, hx26]) (by simp only [wp_norm, arm64_norm, hx27])
          (by simp only [wp_norm, arm64_norm, hx28]) (by simp only [wp_norm, arm64_norm, hx29])
          (by
            dsimp only [decodeStateLoopCommonPlaced, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23,
              Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
            try simp only [wp_norm, arm64_norm]
            try sep_ac_rfl) ?_
        intro vn' rest2 evs_vn sf P' hmf hvn_loop hle2 hsuf2
        have hvn_step : DecodeStateLoopEnv (8 * (rest1.length - rest2.length)) x.st.bytes.length
            (2 * x.st.bytes.length + 16) evs_vn :=
          hvn_loop.mono_fuel (by omega)
        have hFit' : FitsEnv M lim (M.stepEvents evs_vn st)
            (DecodeStateLoopEnv (rem - 8 * (rest1.length - rest2.length)) x.st.bytes.length
              (2 * x.st.bytes.length + 16)) :=
          decodeStateLoop_split hvn_step
            (decodeStateLoop_mono (by omega) (Nat.le_refl _) (Nat.le_refl _) hFit)
        exact hnext w0 ⟨some vn', optCh, inner⟩ rest2 evs_vn sf P' hle2 hsuf2
          (by rw [show BitVec.ofNat 32 1 = 1#32 from rfl, htag1_eq]
              dsimp only; rw [hmf]; rfl)
          (by dsimp only at hlinks ⊢; omega)
          (Nat.le_trans (optInnerStatePolyCapBound_mono_len hle2) hpoly)
          (hacc.append hvn_step) (by rw [M.stepEvents_append, hst]) hFit'
      · -- tag ≥ 4
        have ⟨_, _, _, _, hbeq3, hbne3⟩ := tag_cmp32_of_gt (c := 3) (by omega) htag29
        have ⟨_, _, _, _, hbeq2, hbne2⟩ := tag_cmp32_of_gt (c := 2) (by omega) htag29
        have ⟨_, _, _, _, hbeq1, hbne1⟩ := tag_cmp32_of_gt (c := 1) (by omega) htag29
        have htw32 := tag_setWidth32_ofNat tag
        apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 456#64)
        wp_steps 6
        apply SepWP.done
          (by simp only [wp_norm, arm64_norm, hx1, htw32, hbeq3, hbne3, hbeq2, hbne2, hbeq1, hbne1])
          (by simp only [wp_norm, arm64_norm, hrun])
        refine decodeState_outer_skip_53664_cl_placed_ofEnv
          (PreEnv := PreEnv) (PostEnv := PostEnv) (v27 := 8#64)
          hc.toDecodeStateCalleeContractsClPlaced x st0 st w0 curSt rest1 iwt tag
          (by omega) hrest1_le hrest1_suf hlen_bound
          (fun hnone => herr_of_none (by
            have ho := pqRatchetState_mergeField_other curSt tag htag1 htag2 htag3 (by omega) iwt rest1 100
            rw [decodeState_codecWireTypeToProto_eq] at ho
            rw [ho, hnone]; rfl))
          s0 _ _ R post hpost
          (decodeStateLoop_head (fuel := rem - 1)
            (fun _ h => DecodeStateIterEnv.of_skipField3 h)
            (decodeStateLoop_mono (by omega) (Nat.le_refl _) (Nat.le_refl _) hFit))
          (fun evs_sf evs_f _ hsf_env hf_evs => by
            have hsf_l : DecodeStateLoopEnv 1 x.st.bytes.length
                (2 * x.st.bytes.length + 16) evs_sf :=
              DecodeStateLoopEnv.single (fuel := 0) (DecodeStateIterEnv.of_skipField3 hsf_env)
            have hf_l : DecodeStateLoopEnv 1 x.st.bytes.length
                (2 * x.st.bytes.length + 16) evs_f :=
              DecodeStateLoopEnv.single (fuel := 0) (.deallocs hf_evs)
            have htot := (hacc.append hsf_l).append hf_l
            refine ⟨(evs_acc ++ evs_sf) ++ evs_f,
              hpost_env _ (htot.mono_fuel (by omega)), ?_⟩
            rw [M.stepEvents_append, M.stepEvents_append, hst])
          hs0A
          (by dsimp only [decodeStatePlacedEntry]
              simp only [wp_norm, arm64_norm, hx1, htw32, hbeq3, hbne3, hbeq2, hbne2, hbeq1, hbne1])
          (by simp only [wp_norm, arm64_norm, hrun]) (by simp only [wp_norm, arm64_norm, hsp])
          (by simp only [wp_norm, arm64_norm, htr]) (by simp only [wp_norm, arm64_norm, hx0])
          (by simp only [wp_norm, arm64_norm, hx1, htw32])
          (by simp only [wp_norm, arm64_norm, hx19]) (by simp only [wp_norm, arm64_norm, hx21])
          (by simp only [wp_norm, arm64_norm, hx22]) (by simp only [wp_norm, arm64_norm, hx23])
          (by simp only [wp_norm, arm64_norm, hx24]) (by simp only [wp_norm, arm64_norm, hx25])
          (by simp only [wp_norm, arm64_norm, hx26]) (by simp only [wp_norm, arm64_norm, hx27])
          (by simp only [wp_norm, arm64_norm, hx28]) (by simp only [wp_norm, arm64_norm, hx29])
          (by
            dsimp only [decodeStateLoopCommonPlaced, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23,
              Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
            try simp only [wp_norm, arm64_norm]
            try sep_ac_rfl) ?_
        intro rest2 evs_sf sf P' hsf hevs_sf hle2 hsuf2
        have hnil_sf : evs_sf = [] := skipField3Env_ok_nil hsf hevs_sf
        have hsf_step : DecodeStateLoopEnv (8 * (rest1.length - rest2.length)) x.st.bytes.length
            (2 * x.st.bytes.length + 16) evs_sf := by
          rw [hnil_sf]; exact .nil
        have hFit' : FitsEnv M lim (M.stepEvents evs_sf st)
            (DecodeStateLoopEnv (rem - 8 * (rest1.length - rest2.length)) x.st.bytes.length
              (2 * x.st.bytes.length + 16)) :=
          decodeStateLoop_split hsf_step
            (decodeStateLoop_mono (by omega) (Nat.le_refl _) (Nat.le_refl _) hFit)
        have ho := pqRatchetState_mergeField_other curSt tag htag1 htag2 htag3 (by omega) iwt rest1 100
        rw [decodeState_codecWireTypeToProto_eq] at ho
        exact hnext w0 curSt rest2 evs_sf sf P' hle2 hsuf2
          (by rw [ho, hsf]; rfl)
          (by omega)
          (Nat.le_trans (optInnerStatePolyCapBound_mono_len hle2) hpoly)
          (hacc.append hsf_step) (by rw [M.stepEvents_append, hst]) hFit'

theorem decodeState_outer_dispatch_5353c_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (evs_acc : List AllocEvent) (f rem : Nat)
    (w0 : BitVec 64) (curSt : PqRatchetState)
    (rest1 : List (BitVec 8)) (tag : Nat) (iwt : WireType)
    (htag1_le : 1 ≤ tag) (htag29 : tag < 2 ^ 29)
    (hrest1_le : rest1.length ≤ x.st.bytes.length) (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hlinks : (curSt.chain.getD default).links.length + rest1.length ≤ 2 * x.st.bytes.length + 4)
    (hpoly : optInnerStatePolyCapBound (pqRatchetStateV1OrDefault curSt).innerState rest1.length ≤
      2 * x.st.bytes.length + 16)
    (herr_of_none :
      (match (PqRatchetState.mergeField curSt (BitVec.ofNat 32 tag) (codecWireTypeToProto iwt) rest1 100).toOption with
       | none => none
       | some (st', rest2) => mergeLoopBin PqRatchetState.mergeField rest2.length st' rest2 0 100) = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (hacc : DecodeStateLoopEnv f x.st.bytes.length (2 * x.st.bytes.length + 16) evs_acc)
    (hst : M.stepEvents evs_acc st0 = st)
    (hFit : FitsEnv M lim st
      (DecodeStateLoopEnv rem x.st.bytes.length (2 * x.st.bytes.length + 16)))
    (hrem : 8 * rest1.length + 24 ≤ rem)
    (hf : f + 8 * rest1.length + 24 ≤ 16 * x.st.bytes.length + 32)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 160#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 tag)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = 8#64) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest1.length curSt ∗
      memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hnext : ∀ (w0' : BitVec 64) (st' : PqRatchetState) (rest2 : List (BitVec 8))
        (evs_step : List AllocEvent) (sf : State) (P' : SepProp),
      rest2.length ≤ rest1.length → IsDropSuffix rest1 rest2 →
      (PqRatchetState.mergeField curSt (BitVec.ofNat 32 tag) (codecWireTypeToProto iwt) rest1 100).toOption =
        some (st', rest2) →
      (st'.chain.getD default).links.length + rest2.length ≤ 2 * x.st.bytes.length + 4 →
      optInnerStatePolyCapBound (pqRatchetStateV1OrDefault st').innerState rest2.length ≤
        2 * x.st.bytes.length + 16 →
      DecodeStateLoopEnv (f + 8 * (rest1.length - rest2.length)) x.st.bytes.length
        (2 * x.st.bytes.length + 16) (evs_acc ++ evs_step) →
      M.stepEvents (evs_acc ++ evs_step) st0 = M.stepEvents evs_step st →
      FitsEnv M lim (M.stepEvents evs_step st)
        (DecodeStateLoopEnv (rem - 8 * (rest1.length - rest2.length)) x.st.bytes.length
          (2 * x.st.bytes.length + 16)) →
      sf.pc = decodeStatePlacedEntry + 1576#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = BitVec.ofNat 64 rest2.length →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = 8#64 → sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0') ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length st' ∗
        memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_step st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_outer_dispatch_5353c_cl_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st evs_acc f rem w0 curSt rest1 tag iwt htag1_le htag29 hrest1_le hrest1_suf
    hlen_bound hlinks hpoly herr_of_none hacc hst hFit hrem hf s0 s P R post hpost
    (fun _ h => h) hs0A hpc hrun hsp htr hx0 hx1 hx19 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29
    hP hnext

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.OuterLoopClPlacedBudgetAux

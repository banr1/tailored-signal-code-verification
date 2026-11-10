/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.MessageMergePart2CodeSym
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Outer `skip_field` & `PqRatchetState::v1` `some` Helpers (Block `325`)

Proves budget-threaded `V1State::merge` call wrappers, outer `skip_field(depth=100)` (`+456`),
224-byte `PqRatchetState::v1` spatial helpers, and in-place Tag 3 `some (.v1 v1)` merge (`+476`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.V1StateStepPlacedBudgetAux

open Arm64 Arm64.Obj ProofLib SepProp
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.SpqrV1.Top.DecodeState.Placed (blkLib_eq_325 blkPC_325 blkPl_325)
open scoped CryptoVerification.SpqrV1.Top.DecodeState.Placed
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalProtoCodec (WireType skipField)
open CryptoVerification.LibsignalTripleRatchet
  (decodeErrorAtStackLen withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (IsDropSuffix sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join sliceCursorAt)
open CryptoVerification.SpqrV1.ProtoRepr (optChainPBAt optVersionNegotiationPBAt)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (OptInnerStatePolyBound V1StateMergeGhost codecWireTypeToProto mergeLoopBin
   optProtoInnerStateCapAt v1StateJumpTablesPlacedAt v1StateMergeStack)
open CryptoVerification.LibsignalSpqrV1
  (ChainPB PqRatchetState V1State VersionNegotiationPB spqrDecodeState)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost Quads28 TraceVRegs V1InnerHeapPred decodeStatePlacedEntry decodeStatePlacedProg
   none2Cap none3Cap optChainPBCapOkAt optChainPBCapOkAt_entails_optChainPBAt
   optChainPBCapOkAt_mono optProtoInnerStateAt optProtoInnerStateCapOkAt
   optProtoInnerStateCapOkAt_entails_capAt optProtoInnerStateCapOkAt_entails_quads28
   optProtoInnerStateCapOkHeap optProtoPqRatchetInnerAt optProtoPqRatchetInnerCapOkAt
   optVersionNegotiationPBCapOkAt
   optVersionNegotiationPBCapOkAt_entails_optVersionNegotiationPBAt
   optVersionNegotiationPBCapOkAt_mono protoPqRatchetStateAt protoPqRatchetStateCapOkAt
   protoPqRatchetStateCapOkAt_mono proto_mergeMessage_suffix quads14At quads28At
   quads28_entails_head_and_memRegion_216 quads28_entails_optProtoInnerStateCapOkAt quads7At
   quads7At_split_head scratch_688_fold_48 scratch_688_split_48 sp_sub_1392_aligned
   memRegion_224_eq_quads28At)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (DecodeErrorPushEnv)
open LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget (SkipField3Env)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefsBudget
  (V1StateMergeEnv V1StateMergePostEnv v1StateMergePlacedSpec v1StateMergePlacedSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget (DecodeStateEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
  (DecodeStateCalleeContractsPlaced DecodeStateCalleeContractsPlacedX)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubBudget (decodeStateErrFramePlaced)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget
  (decodeStatePanicPostPlaced decodeStatePanicPostPlacedOfEnv decodeStatePostPlaced
   decodeStatePostPlacedOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget
  (SepWPpIPlaced decodeStateLoopCommonPlaced loopCommon_calleeErr_proto_to_errFrame_placed
   loopCommon_calleeErr_to_errFrame_placed)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubPlacedBudgetAux
  (decodeState_err_53b20_placed_ofEnv decodeState_err_push_53bc0_placed_ofEnv)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr Obj.lookup v1StateJumpTablesPlacedAt
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Budget-Threaded Call Wrappers for `V1State::merge` -/

/-- Envelope-parameterized call wrapper for `v1StateMergePlacedSpecOfEnv` (`lsmpl.base 298`). -/
theorem call_v1StateMerge_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {V1PreEnv V1PostEnv : V1StateMergeGhost → List AllocEvent → Prop}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl (v1StateMergePlacedSpecOfEnv A lim V1PreEnv V1PostEnv)))
    (hcap : ∀ (a : BitVec 64) (remLen : Nat) (opt : Option V1State.InnerState),
      OptInnerStatePolyBound remLen opt →
      optProtoInnerStateCapAt A.repAlloc a remLen opt ⊢
        optProtoInnerStateCapOkAt H_inner A.repAlloc a remLen opt)
    (hdrop : ∀ (a : BitVec 64) (opt : Option V1State.InnerState),
      CryptoVerification.SpqrV1.Drop.optProtoInnerStateAt A.repAlloc a opt ⊢
        optProtoInnerStateAt H_inner A.repAlloc a opt)
    (wt : WireType) (msgPtr : BitVec 64) (msg : V1State)
    (bufRef slot ptr : BitVec 64) (bs : List (BitVec 8)) (st : M.σ)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : TraceVRegs s s0)
    (hx0 : (s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 wt.toNat)
    (hx1 : s.readReg64 .x1 = msgPtr)
    (hx2 : s.readReg64 .x2 = bufRef)
    (hlen : bs.length < 2 ^ 32)
    (hfits : OptInnerStatePolyBound bs.length msg.innerState →
      FitsEnv M lim st (V1PreEnv ⟨wt, msgPtr, msg, bufRef, slot, ptr, bs⟩))
    (hP : P = (optProtoInnerStateCapOkAt H_inner A.repAlloc msgPtr bs.length msg.innerState ∗
      v1StateJumpTablesPlacedAt ∗ (bufRef ↦₆₄ slot) ∗
      sliceCursorAt slot ptr bs ∗ A.pool lim st s ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
    (hok : ∀ (sf : State) (m' : V1State) (rest : List (BitVec 8)) (evs : List AllocEvent),
      (mergeMessage V1State.mergeField (codecWireTypeToProto wt) msg bs 100).toOption =
        some (m', rest) →
      OptInnerStatePolyBound bs.length msg.innerState →
      V1PostEnv ⟨wt, msgPtr, msg, bufRef, slot, ptr, bs⟩ evs →
      rest.length ≤ bs.length → IsDropSuffix bs rest →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = 0#64 →
      SepWPpIPlaced prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          v1StateJumpTablesPlacedAt ∗
          optProtoInnerStateCapOkAt H_inner A.repAlloc msgPtr rest.length m'.innerState ∗
          sliceCursorAfter slot ptr bs rest) ∗ F)
        Q Qp)
    (herr : ∀ (sf : State) (n : Nat) (m' : Option V1State.InnerState) (evs : List AllocEvent),
      (mergeMessage V1State.mergeField (codecWireTypeToProto wt) msg bs 100).toOption = none →
      OptInnerStatePolyBound bs.length msg.innerState →
      V1PostEnv ⟨wt, msgPtr, msg, bufRef, slot, ptr, bs⟩ evs →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 ≠ 0#64 → n ≤ 4 →
      SepWPpIPlaced prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          v1StateJumpTablesPlacedAt ∗
          decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) n ∗
          optProtoInnerStateAt H_inner A.repAlloc msgPtr m' ∗
          memRegion slot 16 ∗ (ptr ↦ₛ bs)) ∗ F)
        Q Qp) :
    SepWPpIPlaced prog ret s P Q Qp := by
  intro hinv R' hm hL
  let x_v1 : V1StateMergeGhost := ⟨wt, msgPtr, msg, bufRef, slot, ptr, bs⟩
  rw [hP] at hm
  have hm_cap := Satisfies.mono (sepConj_mono_left (sepConj_mono_left (sepConj_mono_left
    (optProtoInnerStateCapOkAt_entails_capAt H_inner A.repAlloc msgPtr bs.length msg.innerState)))) hm
  have hm_pb : s.mem ⊨ ⌜OptInnerStatePolyBound bs.length msg.innerState⌝ ∗
      ((optProtoInnerStateCapAt A.repAlloc msgPtr bs.length msg.innerState ∗
        v1StateJumpTablesPlacedAt ∗ (bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot ptr bs ∗ A.pool lim st s ∗
        stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F ∗ R') := by
    refine Satisfies.mono (Entails.of_eq ?_) hm_cap
    sep_ac_rfl
  rw [satisfies_pure_sepConj] at hm_pb
  rcases hm_pb with ⟨hpb, hm'⟩
  have hpre : s.mem ⊨
      (withLsCodeRoLoaded lsmpl (v1StateMergePlacedSpecOfEnv A lim V1PreEnv V1PostEnv)).pre
        (x_v1, st) s ∗ (F ∗ R') := by
    dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hinv, ?_⟩
    dsimp only [v1StateMergePlacedSpecOfEnv, x_v1]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, by omega, hpb, hfits hpb⟩, ?_⟩
    refine Satisfies.mono (Entails.of_eq ?_) hm'
    sep_ac_rfl
  have halign : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome (x_v1, st) (F ∗ R') s hpc hrun hpre halign hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · change sm.mem ⊨ (v1StateMergePlacedSpecOfEnv A lim V1PreEnv V1PostEnv).post (x_v1, st) s sm ∗
      (F ∗ R') at hpost
    dsimp only [v1StateMergePlacedSpecOfEnv, x_v1] at hpost
    rw [hsp] at hpost
    rcases hv1 : (mergeMessage V1State.mergeField (codecWireTypeToProto wt) msg bs 100).toOption with _ | ⟨m', rest⟩
    · simp only [hv1, sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
      rcases hpost with ⟨m', n, evs, hpost⟩
      have hpost_pure : sm.mem ⊨ ⌜V1PostEnv x_v1 evs⌝ ∗
          (⌜sm.trace = s.trace⌝ ∗ (⌜sm.readReg64 .x0 ≠ 0#64⌝ ∗ (⌜n ≤ 4⌝ ∗
            (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sm ∗
              stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
              v1StateJumpTablesPlacedAt ∗
              decodeErrorAtStackLen A.repAlloc (sm.readReg64 .x0) n ∗
              CryptoVerification.SpqrV1.Drop.optProtoInnerStateAt A.repAlloc msgPtr m' ∗
              memRegion slot 16 ∗ (ptr ↦ₛ bs)) ∗ F) ∗ R'))) := by
        refine Satisfies.mono (Entails.of_eq ?_) hpost
        sep_ac_rfl
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj, satisfies_pure_sepConj,
        satisfies_pure_sepConj] at hpost_pure
      rcases hpost_pure with ⟨hevs, htrm, hx0_ne, hn, hpost1⟩
      have hpost2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_left (hdrop msgPtr m'))))))))) hpost1
      rw [hlr] at hpcm; rw [hsp] at hspm
      obtain ⟨sf, hsteps', hout'⟩ :=
        herr sm n m' evs hv1 hpb hevs hpcm hrunm hspm (htr.step htrm hcsm) hcsm hx0_ne hn
          (hinv.of_keepsFrozen hsteps.keepsFrozen) R' hpost2 (hsteps.codeLoaded hL)
      exact ⟨sf, hsteps.trans hsteps', hout'⟩
    · simp only [hv1, sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
      rcases hpost with ⟨evs, hpost⟩
      have hpost_pure : sm.mem ⊨ ⌜V1PostEnv x_v1 evs⌝ ∗
          (⌜sm.trace = s.trace⌝ ∗
            (⌜sm.readReg64 .x0 = 0#64 ∧ OptInnerStatePolyBound rest.length m'.innerState⌝ ∗
              (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sm ∗
                stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
                v1StateJumpTablesPlacedAt ∗
                optProtoInnerStateCapAt A.repAlloc msgPtr rest.length m'.innerState ∗
                sliceCursorAfter slot ptr bs rest) ∗ F) ∗ R')) := by
        refine Satisfies.mono (Entails.of_eq ?_) hpost
        sep_ac_rfl
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost_pure
      rcases hpost_pure with ⟨hevs, htrm, ⟨hx0_0, hpb'⟩, hpost1⟩
      have hpost2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (hcap msgPtr rest.length m'.innerState hpb')))))))) hpost1
      rw [hlr] at hpcm; rw [hsp] at hspm
      have ⟨hle, hsuf⟩ := proto_mergeMessage_suffix hv1
      obtain ⟨sf, hsteps', hout'⟩ :=
        hok sm m' rest evs hv1 hpb hevs hle hsuf hpcm hrunm hspm (htr.step htrm hcsm) hcsm hx0_0
          (hinv.of_keepsFrozen hsteps.keepsFrozen) R' hpost2 (hsteps.codeLoaded hL)
      exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [v1StateMergePlacedSpecOfEnv, withLsCodeRoLoaded] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)
  · dsimp only [v1StateMergePlacedSpecOfEnv, withLsCodeRoLoaded] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)
  · dsimp only [v1StateMergePlacedSpecOfEnv, withLsCodeRoLoaded] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)

theorem call_v1StateMerge [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl (v1StateMergePlacedSpec A lim)))
    (hcap : ∀ (a : BitVec 64) (remLen : Nat) (opt : Option V1State.InnerState),
      OptInnerStatePolyBound remLen opt →
      optProtoInnerStateCapAt A.repAlloc a remLen opt ⊢
        optProtoInnerStateCapOkAt H_inner A.repAlloc a remLen opt)
    (hdrop : ∀ (a : BitVec 64) (opt : Option V1State.InnerState),
      CryptoVerification.SpqrV1.Drop.optProtoInnerStateAt A.repAlloc a opt ⊢
        optProtoInnerStateAt H_inner A.repAlloc a opt)
    (wt : WireType) (msgPtr : BitVec 64) (msg : V1State)
    (bufRef slot ptr : BitVec 64) (bs : List (BitVec 8)) (st : M.σ)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : TraceVRegs s s0)
    (hx0 : (s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 wt.toNat)
    (hx1 : s.readReg64 .x1 = msgPtr)
    (hx2 : s.readReg64 .x2 = bufRef)
    (hlen : bs.length < 2 ^ 32)
    (hfits : OptInnerStatePolyBound bs.length msg.innerState →
      FitsEnv M lim st (V1StateMergeEnv ⟨wt, msgPtr, msg, bufRef, slot, ptr, bs⟩))
    (hP : P = (optProtoInnerStateCapOkAt H_inner A.repAlloc msgPtr bs.length msg.innerState ∗
      v1StateJumpTablesPlacedAt ∗ (bufRef ↦₆₄ slot) ∗
      sliceCursorAt slot ptr bs ∗ A.pool lim st s ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
    (hok : ∀ (sf : State) (m' : V1State) (rest : List (BitVec 8)) (evs : List AllocEvent),
      (mergeMessage V1State.mergeField (codecWireTypeToProto wt) msg bs 100).toOption =
        some (m', rest) →
      OptInnerStatePolyBound bs.length msg.innerState →
      V1StateMergePostEnv ⟨wt, msgPtr, msg, bufRef, slot, ptr, bs⟩ evs →
      rest.length ≤ bs.length → IsDropSuffix bs rest →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = 0#64 →
      SepWPpIPlaced prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          v1StateJumpTablesPlacedAt ∗
          optProtoInnerStateCapOkAt H_inner A.repAlloc msgPtr rest.length m'.innerState ∗
          sliceCursorAfter slot ptr bs rest) ∗ F)
        Q Qp)
    (herr : ∀ (sf : State) (n : Nat) (m' : Option V1State.InnerState) (evs : List AllocEvent),
      (mergeMessage V1State.mergeField (codecWireTypeToProto wt) msg bs 100).toOption = none →
      OptInnerStatePolyBound bs.length msg.innerState →
      V1StateMergePostEnv ⟨wt, msgPtr, msg, bufRef, slot, ptr, bs⟩ evs →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 ≠ 0#64 → n ≤ 4 →
      SepWPpIPlaced prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          v1StateJumpTablesPlacedAt ∗
          decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) n ∗
          optProtoInnerStateAt H_inner A.repAlloc msgPtr m' ∗
          memRegion slot 16 ∗ (ptr ↦ₛ bs)) ∗ F)
        Q Qp) :
    SepWPpIPlaced prog ret s P Q Qp :=
  call_v1StateMerge_ofEnv hcall hcap hdrop wt msgPtr msg bufRef slot ptr bs st
    hpc hrun hsp hs0A hlr htr hx0 hx1 hx2 hlen hfits hP hok herr

/-! ## 2. Outer `skip_field(depth=100)` (`+456` -> `+1576` / `+1668`) -/

attribute [local irreducible] mergeMessage mergeLoopBin

theorem setWidth8_ofNat64_wt (iwt : WireType) :
    BitVec.setWidth 8 (BitVec.ofNat 64 iwt.toNat) = BitVec.ofNat 8 iwt.toNat := by
  cases iwt <;> rfl

/-- Envelope-parameterized outer loop default `skip_field` at `+456` (`0x53664`), reaching
`entry + 1576` on success or `decodeState_err_53b20_placed_ofEnv` on failure. -/
theorem decodeState_outer_skip_53664_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {v27 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (w0 : BitVec 64)
    (curSt : PqRatchetState)
    (rest1 : List (BitVec 8)) (iwt : WireType) (itag : Nat)
    (hitag_lt : itag < 2 ^ 32)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none :
      skipField (2 * rest1.length + 2) 100 itag iwt rest1 = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (hfits_sf : FitsEnv M lim st
      (SkipField3Env ⟨iwt, itag, 100, s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩))
    (henv_err : ∀ evs_sf evs_f,
      skipField (2 * rest1.length + 2) 100 itag iwt rest1 = none →
      SkipField3Env ⟨iwt, itag, 100, s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩ evs_sf →
      FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 = M.stepEvents evs_f (M.stepEvents evs_sf st))
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 456#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : (s.readReg64 (Reg.gpr 1#5)).setWidth 32 = BitVec.ofNat 32 itag)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = v27)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest1.length curSt ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hdone : ∀ (rest2 : List (BitVec 8)) (evs_sf : List AllocEvent)
        (sf : State) (P' : SepProp),
      skipField (2 * rest1.length + 2) 100 itag iwt rest1 = some rest2 →
      SkipField3Env ⟨iwt, itag, 100, s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩ evs_sf →
      rest2.length ≤ rest1.length →
      IsDropSuffix rest1 rest2 →
      sf.pc = decodeStatePlacedEntry + 1576#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 rest2.length →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = v27 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0) ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length curSt ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_sf st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hsf_call := hc.skipField3
  subst hP
  rw [sliceCursorAfter_eq_split hrest1_le hrest1_suf]
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateLoopCommonPlaced] at hpc hsf_call ⊢
  apply SepWPpIPlaced.of_sepWP (mid := lsmpl.base 263)
  wp_steps_sync_pool (lsmpl.base 263)
  try simp only [State.setMem_setMem]
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  have hx29_f0 : s0.sp - 96#64 - 240#64 = s0.sp - 336#64 := by bv_omega
  have hsp1048 : s0.sp - 1056#64 + 8#64 = s0.sp - 1048#64 := by bv_omega
  refine SepWPpIPlaced.call_skipField3 hsf_call iwt itag 100
    (s0.sp - 336#64) (s0.sp - 1056#64)
    (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length)) rest1 st
    (ret_pc := (blkPl_325).base + 468#64)
    (hpc := by simp only [wp_norm, arm64_norm])
    (hrun := by simp only [wp_norm, arm64_norm, hrun])
    (hsp := by simp only [wp_norm, arm64_norm, hsp]) (hs0A := hs0A)
    (hlr := by simp only [wp_norm, arm64_norm])
    (htr := by simp only [wp_norm, arm64_norm, htr])
    (hx0 := by simp only [wp_norm, arm64_norm, hx0, setWidth8_ofNat64_wt])
    (hx1 := by simp only [wp_norm, arm64_norm, hx1]) (htag := hitag_lt)
    (hx2 := by simp only [wp_norm, arm64_norm, hx29, hx29_f0])
    (hx3 := by rfl) (hdepth := by decide) (hlen := by omega)
    (hfits := hfits_sf)
    (hP := by sep_focus) ?_ ?_
  · intro s1 rest2 evs_sf hsf hevs_sf hle2 hsuf2 hpc1 hrun1 hsp1 htr1 hcs1 hx0_0
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
    simp only [arm64_norm, wp_norm] at hx0_0 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    have hsp1A : s1.spAligned = true := by rw [State.spAligned, hsp1]; exact sp_sub_1392_aligned s0 hs0A
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1576#64)
    refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
      hrest1_le hrest1_suf hle2) (by sep_focus) ?_
    refine SepWP.fold (protoPqRatchetStateCapOkAt_mono (H_inner := H_inner) (A := A.repAlloc)
      (a := s0.sp - 1040#64) (rem1 := rest1.length) (rem2 := rest2.length)
      (st := curSt) hle2) (by sep_focus) ?_
    dsimp only [sliceCursorAfter]
    wp_steps_sync_pool ((blkPl_325).base + 1576#64)
    try simp only [State.setMem_setMem]
    apply SepWP.done (by simp only [wp_norm, arm64_norm, hx0_0]) (by simp only [wp_norm, arm64_norm, hrun1])
    exact hdone rest2 evs_sf _ _ hsf hevs_sf hle2 hsuf2
      (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm, hx0_0])
      (by simp only [wp_norm, arm64_norm, hrun1]) (by simp only [wp_norm, arm64_norm, hsp1])
      (by simp only [wp_norm, arm64_norm, htr1])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by
        dsimp only [decodeStateLoopCommonPlaced, sliceCursorAfter, Reg.x19, Reg.x20, Reg.x21,
          Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
        rw [hsp1048]
        sep_ac_rfl)
  · intro s1 evs_sf hsf hevs_sf hpc1 hrun1 hsp1 htr1 hcs1 hx0_ne
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
    simp only [arm64_norm, wp_norm] at hx0_ne hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    have hbeq0 : (s1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1668#64)
    wp_steps_sync_pool ((blkPl_325).base + 1668#64)
    try simp only [State.setMem_setMem]
    refine SepWP.fold (loopCommon_calleeErr_to_errFrame_placed H_inner A lim
      (M.stepEvents evs_sf st) x hrest1_le hrest1_suf rest1.length curSt s0 _)
      (by dsimp only [decodeStateLoopCommonPlaced]; sep_focus) ?_
    apply SepWP.done (by simp only [wp_norm, arm64_norm, hbeq0]) (by simp only [wp_norm, arm64_norm, hrun1])
    exact SepWPpIPlaced.of_sepWPp (decodeState_err_53b20_placed_ofEnv hc x st0
      (M.stepEvents evs_sf st) curSt w0 0 s0 _ _ R post hpost
      (fun evs_f hfree => henv_err evs_sf evs_f hsf hevs_sf hfree)
      (herr_of_none hsf)
      (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm, hbeq0])
      (by simp only [wp_norm, arm64_norm, hrun1]) (by simp only [wp_norm, arm64_norm, hsp1]) hs0A
      (by simp only [wp_norm, arm64_norm, htr1]) (by simp only [wp_norm, arm64_norm, *])
      (by
        dsimp only [decodeStateErrFramePlaced, Reg.x0, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23,
          Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
        simp only [wp_norm, arm64_norm]
        sep_ac_rfl))

theorem decodeState_outer_skip_53664_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {v27 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (w0 : BitVec 64)
    (curSt : PqRatchetState)
    (rest1 : List (BitVec 8)) (iwt : WireType) (itag : Nat)
    (hitag_lt : itag < 2 ^ 32)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none :
      skipField (2 * rest1.length + 2) 100 itag iwt rest1 = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (hfits_sf : FitsEnv M lim st
      (SkipField3Env ⟨iwt, itag, 100, s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩))
    (henv_err : ∀ evs_sf evs_f,
      skipField (2 * rest1.length + 2) 100 itag iwt rest1 = none →
      SkipField3Env ⟨iwt, itag, 100, s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩ evs_sf →
      FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 = M.stepEvents evs_f (M.stepEvents evs_sf st))
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 456#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : (s.readReg64 (Reg.gpr 1#5)).setWidth 32 = BitVec.ofNat 32 itag)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = v27)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest1.length curSt ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hdone : ∀ (rest2 : List (BitVec 8)) (evs_sf : List AllocEvent)
        (sf : State) (P' : SepProp),
      skipField (2 * rest1.length + 2) 100 itag iwt rest1 = some rest2 →
      SkipField3Env ⟨iwt, itag, 100, s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩ evs_sf →
      rest2.length ≤ rest1.length →
      IsDropSuffix rest1 rest2 →
      sf.pc = decodeStatePlacedEntry + 1576#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 rest2.length →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = v27 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0) ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length curSt ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_sf st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_outer_skip_53664_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st w0 curSt rest1 iwt itag hitag_lt hrest1_le hrest1_suf hlen_bound
    herr_of_none s0 s P R post hpost hfits_sf henv_err hs0A
    hpc hrun hsp htr hx0 hx1 hx19 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP hdone

/-! ## 3. Spatial & Framing Helpers for Outer Tag 3 (`PqRatchetState::v1`, `224`B) -/

theorem protoPqRatchetStateCapOkAt_v1_eq (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (sp : BitVec 64) (remLen : Nat) (optVn : Option VersionNegotiationPB)
    (optCh : Option ChainPB) (inner : Option PqRatchetState.Inner) :
    protoPqRatchetStateCapOkAt H_inner A (sp - 1040#64) remLen ⟨optVn, optCh, inner⟩ =
      optVersionNegotiationPBCapOkAt A (sp - 1040#64) remLen optVn ∗
      optChainPBCapOkAt A (sp - 992#64) remLen optCh ∗
      optProtoPqRatchetInnerCapOkAt H_inner A (sp - 912#64) remLen inner := by
  unfold protoPqRatchetStateCapOkAt
  dsimp only
  have ha1 : sp - 1040#64 + 48#64 = sp - 992#64 := by bv_omega
  have ha2 : sp - 1040#64 + 128#64 = sp - 912#64 := by bv_omega
  rw [ha1, ha2]

theorem optProtoInnerStateCapOkAt_expose_head (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (a : BitVec 64) (remLen : Nat) (opt : Option V1State.InnerState) :
    optProtoInnerStateCapOkAt H_inner A a remLen opt ⊢
      ∃∗ q : Quads28,
        ⌜q.head ≠ none3Cap⌝ ∗
        (a ↦₆₄ q.head) ∗
        (((a + 8#64) ↦₆₄ q.1.1.2.1) ∗ ((a + 16#64) ↦₆₄ q.1.1.2.2.1) ∗
         ((a + 24#64) ↦₆₄ q.1.1.2.2.2.1) ∗ ((a + 32#64) ↦₆₄ q.1.1.2.2.2.2.1) ∗
         ((a + 40#64) ↦₆₄ q.1.1.2.2.2.2.2.1) ∗ ((a + 48#64) ↦₆₄ q.1.1.2.2.2.2.2.2) ∗
         quads7At (a + 56#64) q.1.2 ∗ quads14At (a + 112#64) q.2 ∗
         optProtoInnerStateCapOkHeap H_inner A remLen q opt) := by
  refine Entails.trans (optProtoInnerStateCapOkAt_entails_quads28 H_inner A a remLen opt) ?_
  apply Entails.sepExists_elim; intro q
  refine Entails.sepExists_right q ?_
  cases opt with
  | none =>
    unfold optProtoInnerStateCapOkHeap quads28At
    dsimp only
    rw [quads14At, quads7At_split_head a q.1.1]
    rw [sepConj_comm _ ⌜_⌝]
    apply Entails.pure_left; intro hrh
    have hne : q.head ≠ none3Cap := by rw [hrh.2]; decide
    apply Entails.pure_right hne
    have htrue : (⌜remLen < 2 ^ 56 ∧ q.head = none2Cap⌝ : SepProp) = emp := by
      simp only [hrh, and_self, pure_true]
    rw [htrue, sepConj_emp]
    unfold Quads28.head
    exact Entails.of_eq (by sep_ac_rfl)
  | some is =>
    unfold optProtoInnerStateCapOkHeap
    dsimp only
    rw [sepConj_comm (quads28At a q), sepConj_assoc]
    apply Entails.pure_left; intro hph
    apply Entails.pure_right hph.2
    have htrue : (⌜OptInnerStatePolyBound remLen (some is) ∧ q.head ≠ none3Cap⌝ : SepProp) = emp := by
      rw [eq_true hph, pure_true]
    rw [quads28At, quads14At, quads7At_split_head a q.1.1, htrue, emp_sepConj]
    unfold Quads28.head
    exact Entails.of_eq (by sep_ac_rfl)

theorem optProtoInnerStateCapOkAt_fold_head (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (a : BitVec 64) (q : Quads28) (remLen : Nat) (opt : Option V1State.InnerState) :
    (a ↦₆₄ q.head) ∗
      (((a + 8#64) ↦₆₄ q.1.1.2.1) ∗ ((a + 16#64) ↦₆₄ q.1.1.2.2.1) ∗
       ((a + 24#64) ↦₆₄ q.1.1.2.2.2.1) ∗ ((a + 32#64) ↦₆₄ q.1.1.2.2.2.2.1) ∗
       ((a + 40#64) ↦₆₄ q.1.1.2.2.2.2.2.1) ∗ ((a + 48#64) ↦₆₄ q.1.1.2.2.2.2.2.2) ∗
       quads7At (a + 56#64) q.1.2 ∗ quads14At (a + 112#64) q.2 ∗
       optProtoInnerStateCapOkHeap H_inner A remLen q opt) ⊢
    optProtoInnerStateCapOkAt H_inner A a remLen opt := by
  have hq :
      (a ↦₆₄ q.head) ∗
        (((a + 8#64) ↦₆₄ q.1.1.2.1) ∗ ((a + 16#64) ↦₆₄ q.1.1.2.2.1) ∗
         ((a + 24#64) ↦₆₄ q.1.1.2.2.2.1) ∗ ((a + 32#64) ↦₆₄ q.1.1.2.2.2.2.1) ∗
         ((a + 40#64) ↦₆₄ q.1.1.2.2.2.2.2.1) ∗ ((a + 48#64) ↦₆₄ q.1.1.2.2.2.2.2.2) ∗
         quads7At (a + 56#64) q.1.2 ∗ quads14At (a + 112#64) q.2 ∗
         optProtoInnerStateCapOkHeap H_inner A remLen q opt) =
      quads28At a q ∗ optProtoInnerStateCapOkHeap H_inner A remLen q opt := by
    unfold quads28At quads14At Quads28.head
    rw [quads7At_split_head a q.1.1]
    sep_ac_rfl
  rw [hq]
  exact quads28_entails_optProtoInnerStateCapOkAt H_inner A a remLen q opt

theorem head_ne_none3Cap_branch {w : BitVec 64} (hne : w ≠ none3Cap) :
    (w + 3#64 != 0#64) = true ∧ (w + 3#64 == 0#64) = false := by
  have h0 : w + 3#64 ≠ 0#64 := by
    intro h
    apply hne
    change w = -3#64
    bv_omega
  exact ⟨bne_iff_ne.mpr h0, beq_eq_false_iff_ne.mpr h0⟩

theorem memRegion_224_split_head (a : BitVec 64) :
    memRegion a 224 ⊢
      memRegion (a + 8#64) 216 ∗ (∃∗ w : BitVec 64, a ↦₆₄ w) := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 216) (b' := a + 8#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_eight a]
  exact Entails.of_eq (by sep_ac_rfl)

theorem optProtoInnerStateCapOkAt_default_init (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (a : BitVec 64) (remLen : Nat) (hrem : remLen < 2 ^ 56) :
    (a ↦₆₄ (-2#64)) ∗ memRegion (a + 8#64) 216 ⊢
      optProtoInnerStateCapOkAt H_inner A a remLen (default : V1State).innerState := by
  have hd : (default : V1State).innerState = none := rfl
  rw [hd]
  unfold optProtoInnerStateCapOkAt none2Cap
  exact Entails.pure_right hrem (Entails.refl _)

theorem scratch_688_split_quads28_and_3a0 (sp w0 : BitVec 64) :
    ((sp - 688#64) ↦₆₄ w0) ∗ memRegion (sp - 680#64) 40 ∗ memRegion (sp - 640#64) 304 ⊢
      memRegion (sp - 456#64) 120 ∗
      (∃∗ w_3a0 : BitVec 64, ∃∗ q_dst : Quads28,
        quads28At (sp - 688#64) q_dst ∗ ((sp - 464#64) ↦₆₄ w_3a0)) := by
  refine Entails.trans (scratch_688_fold_48 sp w0) ?_
  rw [ProofLib.memRegion_split' (b := sp - 688#64) (n := 224) (k := 128)
      (b' := sp - 464#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 464#64) (n := 8) (k := 120)
      (b' := sp - 456#64) rfl (by bv_omega) (by decide),
    memRegion_224_eq_quads28At (sp - 688#64),
    ProofLib.memRegion_eight (sp - 464#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  exact Entails.of_eq (by sep_ac_rfl)

theorem scratch_688_restore_from_quads28 (sp w_3a0 : BitVec 64) (q : Quads28) :
    quads28At (sp - 688#64) q ∗ ((sp - 464#64) ↦₆₄ w_3a0) ∗ memRegion (sp - 456#64) 120 ⊢
      ((sp - 688#64) ↦₆₄ q.head) ∗ memRegion (sp - 680#64) 40 ∗ memRegion (sp - 640#64) 304 := by
  have h1 := quads28_entails_head_and_memRegion_216 (sp - 688#64) q
  have h2 : ((sp - 464#64) ↦₆₄ w_3a0) ⊢ memRegion (sp - 464#64) 8 :=
    ProofLib.pointsTo64_entails_memRegion _ _
  refine Entails.trans (sepConj_mono h1 (sepConj_mono_left h2)) ?_
  have ha680 : sp - 688#64 + 8#64 = sp - 680#64 := by bv_omega
  rw [ha680]
  have h344 : memRegion (sp - 680#64) 216 ∗ memRegion (sp - 464#64) 8 ∗ memRegion (sp - 456#64) 120 =
      memRegion (sp - 680#64) 40 ∗ memRegion (sp - 640#64) 304 := by
    rw [← ProofLib.memRegion_split' (b := sp - 464#64) (n := 8) (k := 120)
        (b' := sp - 456#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := sp - 680#64) (n := 216) (k := 128)
        (b' := sp - 464#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 680#64) (n := 40) (k := 304)
        (b' := sp - 640#64) rfl (by bv_omega) (by decide)]
  have hassoc :
      ((sp - 688#64) ↦₆₄ q.head ∗ memRegion (sp - 680#64) 216) ∗
        (memRegion (sp - 464#64) 8 ∗ memRegion (sp - 456#64) 120) =
      (sp - 688#64) ↦₆₄ q.head ∗
        (memRegion (sp - 680#64) 216 ∗ memRegion (sp - 464#64) 8 ∗ memRegion (sp - 456#64) 120) := by
    sep_ac_rfl
  rw [hassoc, h344]
  exact Entails.refl _

theorem scratch_688_dropped_split_48 (sp w_3a0 : BitVec 64) :
    memRegion (sp - 688#64) 224 ∗ ((sp - 464#64) ↦₆₄ w_3a0) ∗ memRegion (sp - 456#64) 120 ⊢
      memRegion (sp - 680#64) 40 ∗ memRegion (sp - 640#64) 304 ∗
      (∃∗ w0' : BitVec 64, (sp - 688#64) ↦₆₄ w0') := by
  have h352 : memRegion (sp - 688#64) 224 ∗ ((sp - 464#64) ↦₆₄ w_3a0) ∗ memRegion (sp - 456#64) 120 ⊢
      memRegion (sp - 688#64) 352 := by
    rw [ProofLib.memRegion_split' (b := sp - 688#64) (n := 224) (k := 128)
        (b' := sp - 464#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 464#64) (n := 8) (k := 120)
        (b' := sp - 456#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_right (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _))
  exact Entails.trans h352 (scratch_688_split_48 sp)

/-! ## 4. Outer Tag 3 `some (.v1 v1)` In-Place Merge (`+476..+492`) -/

/-- Envelope-parameterized outer tag 3 when `inner = some (.v1 v1)` (`+476..+492`):
merges in-place at `s0.sp - 912#64` (`x22 + 0x80`). -/
theorem decodeState_v1_some_53678_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {v27 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {V1PreEnv V1PostEnv : V1StateMergeGhost → List AllocEvent → Prop}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (hv1_call : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 298)
      (withLsCodeRoLoaded lsmpl (v1StateMergePlacedSpecOfEnv A lim V1PreEnv V1PostEnv)))
    (x : DecodeStateGhost) (st0 st : M.σ) (w0 : BitVec 64)
    (optVn : Option VersionNegotiationPB) (optCh : Option ChainPB) (v1 : V1State)
    (rest1 : List (BitVec 8)) (iwt : WireType)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none :
      (mergeMessage V1State.mergeField (codecWireTypeToProto iwt) v1 rest1 100).toOption = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (hfits_v1 : OptInnerStatePolyBound rest1.length v1.innerState →
      FitsEnv M lim st
        (V1PreEnv ⟨iwt, s0.sp - 912#64, v1, s0.sp - 336#64, s0.sp - 1056#64,
          x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩))
    (hfits_err : ∀ evs_v1 n,
      (mergeMessage V1State.mergeField (codecWireTypeToProto iwt) v1 rest1 100).toOption = none →
      OptInnerStatePolyBound rest1.length v1.innerState →
      V1PostEnv ⟨iwt, s0.sp - 912#64, v1, s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩ evs_v1 →
      n ≤ 4 →
      FitsEnv M lim (M.stepEvents evs_v1 st) (DecodeErrorPushEnv n))
    (henv_err : ∀ evs_v1 evs_p evs_f n,
      (mergeMessage V1State.mergeField (codecWireTypeToProto iwt) v1 rest1 100).toOption = none →
      OptInnerStatePolyBound rest1.length v1.innerState →
      V1PostEnv ⟨iwt, s0.sp - 912#64, v1, s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩ evs_v1 →
      n ≤ 4 →
      DecodeErrorPushEnv n evs_p → FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p (M.stepEvents evs_v1 st)))
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 476#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = v27)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest1.length
        ⟨optVn, optCh, some (.v1 v1)⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hdone : ∀ (w0' : BitVec 64) (v1' : V1State) (rest2 : List (BitVec 8))
        (evs_v1 : List AllocEvent) (sf : State) (P' : SepProp),
      (mergeMessage V1State.mergeField (codecWireTypeToProto iwt) v1 rest1 100).toOption =
        some (v1', rest2) →
      OptInnerStatePolyBound rest1.length v1.innerState →
      V1PostEnv ⟨iwt, s0.sp - 912#64, v1, s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩ evs_v1 →
      rest2.length ≤ rest1.length →
      IsDropSuffix rest1 rest2 →
      sf.pc = decodeStatePlacedEntry + 1576#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 rest2.length →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = v27 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0') ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length
          ⟨optVn, optCh, some (.v1 v1')⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_v1 st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  subst hP
  rw [sliceCursorAfter_eq_split hrest1_le hrest1_suf,
      protoPqRatchetStateCapOkAt_v1_eq]
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateLoopCommonPlaced, optProtoPqRatchetInnerCapOkAt] at hpc hv1_call ⊢
  apply SepWPpIPlaced.of_sepWP (mid := lsmpl.base 298)
  wp_steps_sync_pool (lsmpl.base 298)
  try simp only [State.setMem_setMem]
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  have hx22_80 : s0.sp - 1040#64 + 128#64 = s0.sp - 912#64 := by bv_omega
  have hx29_f0 : s0.sp - 96#64 - 240#64 = s0.sp - 336#64 := by bv_omega
  have hsp1048 : s0.sp - 1056#64 + 8#64 = s0.sp - 1048#64 := by bv_omega
  refine call_v1StateMerge_ofEnv hv1_call hc.of_cap_inner hc.of_drop_inner
    iwt (s0.sp - 912#64) v1
    (s0.sp - 336#64) (s0.sp - 1056#64)
    (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length)) rest1 st
    (ret_pc := (blkPl_325).base + 488#64)
    (hpc := by simp only [wp_norm, arm64_norm])
    (hrun := by simp only [wp_norm, arm64_norm, hrun])
    (hsp := by simp only [wp_norm, arm64_norm, hsp]) (hs0A := hs0A)
    (hlr := by simp only [wp_norm, arm64_norm])
    (htr := by simp only [wp_norm, arm64_norm, htr])
    (hx0 := by simp only [wp_norm, arm64_norm, hx0, setWidth8_ofNat64_wt])
    (hx1 := by simp only [wp_norm, arm64_norm, hx22, hx22_80])
    (hx2 := by simp only [wp_norm, arm64_norm, hx29, hx29_f0])
    (hlen := by omega)
    (hfits := hfits_v1)
    (hP := by sep_focus) ?_ ?_
  · intro s1 v1' rest2 evs_v1 hv1 hpb hevs_v1 hle2 hsuf2 hpc1 hrun1 hsp1 htr1 hcs1 hx0_0
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
    simp only [arm64_norm, wp_norm] at hx0_0 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    have hsp1A : s1.spAligned = true := by rw [State.spAligned, hsp1]; exact sp_sub_1392_aligned s0 hs0A
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1576#64)
    refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
      hrest1_le hrest1_suf hle2) (by sep_focus) ?_
    refine SepWP.fold (optVersionNegotiationPBCapOkAt_mono (A := A.repAlloc) (a := s0.sp - 1040#64)
      (rem1 := rest1.length) (rem2 := rest2.length) (opt := optVn) hle2) (by sep_focus) ?_
    refine SepWP.fold (optChainPBCapOkAt_mono (A := A.repAlloc) (a := s0.sp - 992#64)
      (rem1 := rest1.length) (rem2 := rest2.length) (opt := optCh) hle2) (by sep_focus) ?_
    dsimp only [sliceCursorAfter]
    wp_steps_sync_pool ((blkPl_325).base + 1576#64)
    try simp only [State.setMem_setMem]
    apply SepWP.done (by simp only [wp_norm, arm64_norm, hx0_0]) (by simp only [wp_norm, arm64_norm, hrun1])
    exact hdone w0 v1' rest2 evs_v1 _ _ hv1 hpb hevs_v1 hle2 hsuf2
      (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm, hx0_0])
      (by simp only [wp_norm, arm64_norm, hrun1]) (by simp only [wp_norm, arm64_norm, hsp1])
      (by simp only [wp_norm, arm64_norm, htr1])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by
        rw [protoPqRatchetStateCapOkAt_v1_eq]
        dsimp only [decodeStateLoopCommonPlaced, sliceCursorAfter, optProtoPqRatchetInnerCapOkAt,
          Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
          Reg.x28, Reg.x29, Reg.x30]
        rw [hsp1048]
        sep_ac_rfl)
  · intro s1 n m' evs_v1 hv1 hpb hevs_v1 hpc1 hrun1 hsp1 htr1 hcs1 hx0_ne hn
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
    simp only [arm64_norm, wp_norm] at hx0_ne hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    have hbeq0 : (s1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1828#64)
    wp_steps_sync_pool ((blkPl_325).base + 1828#64)
    try simp only [State.setMem_setMem]
    refine SepWP.fold (optVersionNegotiationPBCapOkAt_entails_optVersionNegotiationPBAt A.repAlloc
      (s0.sp - 1040#64) rest1.length optVn) (by sep_focus) ?_
    refine SepWP.fold (optChainPBCapOkAt_entails_optChainPBAt A.repAlloc
      (s0.sp - 992#64) rest1.length optCh) (by sep_focus) ?_
    have hproto_eq :
        optVersionNegotiationPBAt A.repAlloc (s0.sp - 1040#64) optVn ∗
          optChainPBAt A.repAlloc (s0.sp - 992#64) optCh ∗
          optProtoInnerStateAt H_inner A.repAlloc (s0.sp - 912#64) m' =
        protoPqRatchetStateAt H_inner A.repAlloc (s0.sp - 1040#64)
          ⟨optVn, optCh, some (.v1 ⟨m'⟩)⟩ := by
      unfold protoPqRatchetStateAt optProtoPqRatchetInnerAt
      dsimp only
      have ha992 : s0.sp - 1040#64 + 48#64 = s0.sp - 992#64 := by bv_omega
      rw [ha992, hx22_80]
    refine SepWP.fold (Entails.of_eq hproto_eq) (by sep_focus) ?_
    refine SepWP.fold (loopCommon_calleeErr_proto_to_errFrame_placed H_inner A lim
      (M.stepEvents evs_v1 st) x hrest1_le hrest1_suf ⟨optVn, optCh, some (.v1 ⟨m'⟩)⟩ s0 _)
      (by dsimp only [decodeStateLoopCommonPlaced]; sep_focus) ?_
    apply SepWP.done (by simp only [wp_norm, arm64_norm, hbeq0]) (by simp only [wp_norm, arm64_norm, hrun1])
    exact SepWPpIPlaced.of_sepWPp (decodeState_err_push_53bc0_placed_ofEnv hc x st0
      (M.stepEvents evs_v1 st) ⟨optVn, optCh, some (.v1 ⟨m'⟩)⟩ w0 n s0 _ _ R post hpost
      (herr_of_none hv1) (by omega)
      (hfits_err evs_v1 n hv1 hpb hevs_v1 hn)
      (fun evs_p evs_f hp hf => henv_err evs_v1 evs_p evs_f n hv1 hpb hevs_v1 hn hp hf)
      (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm, hbeq0])
      (by simp only [wp_norm, arm64_norm, hrun1]) (by simp only [wp_norm, arm64_norm, hsp1]) hs0A
      (by simp only [wp_norm, arm64_norm, htr1]) (by simp only [wp_norm, arm64_norm, *])
      (by
        dsimp only [decodeStateErrFramePlaced, Reg.x0, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23,
          Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
        simp only [wp_norm, arm64_norm]
        sep_ac_rfl))

theorem decodeState_v1_some_53678_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {v27 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (w0 : BitVec 64)
    (optVn : Option VersionNegotiationPB) (optCh : Option ChainPB) (v1 : V1State)
    (rest1 : List (BitVec 8)) (iwt : WireType)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none :
      (mergeMessage V1State.mergeField (codecWireTypeToProto iwt) v1 rest1 100).toOption = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (hfits_v1 : OptInnerStatePolyBound rest1.length v1.innerState →
      FitsEnv M lim st
        (V1StateMergeEnv ⟨iwt, s0.sp - 912#64, v1, s0.sp - 336#64, s0.sp - 1056#64,
          x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩))
    (hfits_err : ∀ evs_v1 n,
      (mergeMessage V1State.mergeField (codecWireTypeToProto iwt) v1 rest1 100).toOption = none →
      OptInnerStatePolyBound rest1.length v1.innerState →
      V1StateMergePostEnv ⟨iwt, s0.sp - 912#64, v1, s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩ evs_v1 →
      n ≤ 4 →
      FitsEnv M lim (M.stepEvents evs_v1 st) (DecodeErrorPushEnv n))
    (henv_err : ∀ evs_v1 evs_p evs_f n,
      (mergeMessage V1State.mergeField (codecWireTypeToProto iwt) v1 rest1 100).toOption = none →
      OptInnerStatePolyBound rest1.length v1.innerState →
      V1StateMergePostEnv ⟨iwt, s0.sp - 912#64, v1, s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩ evs_v1 →
      n ≤ 4 →
      DecodeErrorPushEnv n evs_p → FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p (M.stepEvents evs_v1 st)))
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 476#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = v27)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest1.length
        ⟨optVn, optCh, some (.v1 v1)⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hdone : ∀ (w0' : BitVec 64) (v1' : V1State) (rest2 : List (BitVec 8))
        (evs_v1 : List AllocEvent) (sf : State) (P' : SepProp),
      (mergeMessage V1State.mergeField (codecWireTypeToProto iwt) v1 rest1 100).toOption =
        some (v1', rest2) →
      OptInnerStatePolyBound rest1.length v1.innerState →
      V1StateMergePostEnv ⟨iwt, s0.sp - 912#64, v1, s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩ evs_v1 →
      rest2.length ≤ rest1.length →
      IsDropSuffix rest1 rest2 →
      sf.pc = decodeStatePlacedEntry + 1576#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 rest2.length →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = v27 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0') ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length
          ⟨optVn, optCh, some (.v1 v1')⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_v1 st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_v1_some_53678_placed_ofEnv
    (V1PreEnv := V1StateMergeEnv) (V1PostEnv := V1StateMergePostEnv)
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc.toDecodeStateCalleeContractsPlaced hc.v1StateMerge
    x st0 st w0 optVn optCh v1 rest1 iwt hrest1_le hrest1_suf hlen_bound
    herr_of_none s0 s P R post hpost hfits_v1 hfits_err henv_err hs0A
    hpc hrun hsp htr hx0 hx19 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP hdone

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.V1StateStepPlacedBudgetAux

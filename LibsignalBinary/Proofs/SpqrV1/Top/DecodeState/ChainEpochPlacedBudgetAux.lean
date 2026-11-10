/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErrPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoop
import ProofLib.SepLogic.WPp

/-!
# `spqr::decode_state` (Block `325`): Budget Relocatable `ChainEpochPB` Call & Framing Helpers

Budget-threaded relocatable `[LibsignalPlacement]` call wrappers, stack/heap framing lemmas,
and `DecodeStateLoopEnv` bridges for `ChainEpochPB::merge`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlacedBudgetAux

open Arm64 Arm64.Obj ProofLib SepProp
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.RustHeap (RustAlloc allocHookStack vecHeader vecU8At)
open CryptoVerification.LibsignalProtoCodec (WireType)
open CryptoVerification.LibsignalTripleRatchet (decodeErrorAtStackLen withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (BytesMergeCapOk IsDropSuffix SkipFieldGhost pointsToBytes_prefix_join sliceCursorAfter
   sliceCursorAt)
open CryptoVerification.SpqrV1.Alloc (GrowGhost)
open CryptoVerification.SpqrV1.ProtoRepr
  (chainEpochPBAt epochDirectionPBAt optEpochDirectionPBAt)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (codecWireTypeToProto v1StateJumpTablesPlacedAt v1StateMergeStack)
open CryptoVerification.LibsignalSpqrV1 (ChainEpochPB EpochDirectionPB PqRatchetState)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost EpochDirectionMergeGhost TraceVRegs V1InnerHeapPred chainEpochPBCapOkAt
   chainEpochPBCapOkAt_entails_chainEpochPBAt chainEpochPBCapOkAt_eq_placed decodeStateSavedAt
   epochDirectionMergeStack epochDirectionPBCapOkAt lower_352_fold optEpochDirectionPBCapOkAt
   protoPqRatchetStateAt protoPqRatchetStateCapOkAt
   protoPqRatchetStateCapOkAt_entails_protoPqRatchetStateAt proto_mergeMessage_suffix
   sliceCursorAfter_to_memRegion sp_sub_1392_aligned stackAt_of_callee stackAt_to_callee
   upper_240_fold vecArgRestAt vecArg_join_bytes vecU8At_eq_header_heap vecU8CapOkAt vecU8Heap
   vecU8Heap_cap_lt)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (DecodeErrorPushEnv)
open LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget (SkipField3Env)
open LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneBudget
  (GrowOneStrideEnv growOneStrideEvents growOneStrideFullSpec growOneStrideFullSpecWithStack)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget
  (DecodeStateEnv DecodeStateIterEnv DecodeStateLoopEnv EpochDirectionMergeEnv
   EpochDirectionMergePostEnv FitsEnv.decodeStateLoop_head FitsEnv.decodeStateLoop_mono
   FitsEnv.decodeStateLoop_split FitsEnv.decodeStateLoop_tail epochDirectionMergeSpec
   epochDirectionMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubPlacedBudgetAux
  (fitsEnv_decodeErrorPush_of_loop)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErrPlacedBudget
  (decodeStateEpochErrFramePlaced decodeStateEpochErrTailFramePlaced
   fitsEnv_epochDrop_push1_of_loop fitsEnv_epochDrop_push2_of_loop)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget
  (SepWPpIPlaced decodeStateLoopCommonPlaced)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr Obj.lookup
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Budget-Threaded Panic-Aware Call Wrapper for `EpochDirection::merge` -/

theorem SepWPpIPlaced.call_epochDirectionMerge_ofEnv [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : EpochDirectionMergeGhost → List AllocEvent → Prop}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl (epochDirectionMergeSpecOfEnv A lim PreEnv PostEnv)))
    (wt : WireType) (msgPtr : BitVec 64) (msg : EpochDirectionPB)
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
    (hlen : bs.length < 2 ^ 63)
    (hfits : FitsEnv M lim st (PreEnv ⟨wt, msgPtr, msg, bufRef, slot, ptr, bs⟩))
    (hP : P = (epochDirectionPBCapOkAt A.repAlloc msgPtr bs.length msg ∗ (bufRef ↦₆₄ slot) ∗
      sliceCursorAt slot ptr bs ∗ A.pool lim st s ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
    (hok : ∀ (sf : State) (m' : EpochDirectionPB) (rest : List (BitVec 8))
        (evs : List AllocEvent),
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto wt) msg bs 98).toOption =
        some (m', rest) →
      PostEnv ⟨wt, msgPtr, msg, bufRef, slot, ptr, bs⟩ evs →
      rest.length ≤ bs.length → IsDropSuffix bs rest →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = 0#64 →
      SepWPpIPlaced prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          epochDirectionPBCapOkAt A.repAlloc msgPtr rest.length m' ∗
          sliceCursorAfter slot ptr bs rest) ∗ F)
        Q Qp)
    (herr : ∀ (sf : State) (n : Nat) (m' : EpochDirectionPB) (evs : List AllocEvent),
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto wt) msg bs 98).toOption =
        none →
      PostEnv ⟨wt, msgPtr, msg, bufRef, slot, ptr, bs⟩ evs →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 ≠ 0#64 → n ≤ 1 →
      SepWPpIPlaced prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) n ∗
          epochDirectionPBAt A.repAlloc msgPtr m' ∗
          memRegion slot 16 ∗ (ptr ↦ₛ bs)) ∗ F)
        Q Qp) :
    SepWPpIPlaced prog ret s P Q Qp := by
  intro hinv R' hm hL
  let sp_cur := s0.sp - 1392#64
  let x_ed : EpochDirectionMergeGhost := ⟨wt, msgPtr, msg, bufRef, slot, ptr, bs⟩
  let F_ext := memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
    (v1StateMergeStack - epochDirectionMergeStack) ∗ F
  have hpre : s.mem ⊨
      (withLsCodeRoLoaded lsmpl (epochDirectionMergeSpecOfEnv A lim PreEnv PostEnv)).pre
        (x_ed, st) s ∗ (F_ext ∗ R') := by
    dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hinv, ?_⟩
    dsimp only [epochDirectionMergeSpecOfEnv, x_ed]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hlen, hfits⟩, ?_⟩
    rw [hP] at hm
    have hm1 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (stackAt_to_callee sp_cur epochDirectionMergeStack (by decide)))))))) hm
    refine Satisfies.mono (Entails.of_eq ?_) hm1
    dsimp only [sp_cur, F_ext]; sep_ac_rfl
  have halign : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome (x_ed, st) (F_ext ∗ R') s hpc hrun hpre halign hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · change sm.mem ⊨ (epochDirectionMergeSpecOfEnv A lim PreEnv PostEnv).post (x_ed, st) s sm ∗
      (F_ext ∗ R') at hpost
    dsimp only [epochDirectionMergeSpecOfEnv, x_ed] at hpost
    rw [hsp] at hpost
    rcases hed :
        (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto wt) msg bs 98).toOption
        with _ | ⟨m', rest⟩
    · simp only [hed, sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
      rcases hpost with ⟨m', n, evs, hpost⟩
      have hpost_pure : sm.mem ⊨ ⌜PostEnv x_ed evs⌝ ∗
          (⌜sm.trace = s.trace⌝ ∗ (⌜sm.readReg64 .x0 ≠ 0#64⌝ ∗ (⌜n ≤ 1⌝ ∗
            (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sm ∗
              (memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
                (v1StateMergeStack - epochDirectionMergeStack) ∗
                stackAt sp_cur epochDirectionMergeStack) ∗
              decodeErrorAtStackLen A.repAlloc (sm.readReg64 .x0) n ∗
              epochDirectionPBAt A.repAlloc msgPtr m' ∗
              memRegion slot 16 ∗ (ptr ↦ₛ bs)) ∗ F) ∗ R'))) := by
        refine Satisfies.mono (Entails.of_eq ?_) hpost
        dsimp only [sp_cur, F_ext]; sep_ac_rfl
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj, satisfies_pure_sepConj,
        satisfies_pure_sepConj] at hpost_pure
      rcases hpost_pure with ⟨hevs, htrm, hx0_ne, hn, hpost1⟩
      rw [hlr] at hpcm; rw [hsp] at hspm
      have hpost2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (stackAt_of_callee sp_cur epochDirectionMergeStack (by decide))))))) hpost1
      obtain ⟨sf, hsteps', hout'⟩ :=
        herr sm n m' evs hed hevs hpcm hrunm hspm (htr.step htrm hcsm) hcsm hx0_ne hn
          (hinv.of_keepsFrozen hsteps.keepsFrozen) R' hpost2 (hsteps.codeLoaded hL)
      exact ⟨sf, hsteps.trans hsteps', hout'⟩
    · simp only [hed, sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
      rcases hpost with ⟨evs, hpost⟩
      have hpost_pure : sm.mem ⊨ ⌜PostEnv x_ed evs⌝ ∗
          (⌜sm.trace = s.trace⌝ ∗ (⌜sm.readReg64 .x0 = 0#64⌝ ∗
            (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sm ∗
              (memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
                (v1StateMergeStack - epochDirectionMergeStack) ∗
                stackAt sp_cur epochDirectionMergeStack) ∗
              epochDirectionPBCapOkAt A.repAlloc msgPtr rest.length m' ∗
              sliceCursorAfter slot ptr bs rest) ∗ F) ∗ R')) := by
        refine Satisfies.mono (Entails.of_eq ?_) hpost
        dsimp only [sp_cur, F_ext]; sep_ac_rfl
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost_pure
      rcases hpost_pure with ⟨hevs, htrm, hx0_0, hpost1⟩
      rw [hlr] at hpcm; rw [hsp] at hspm
      have hpost2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (stackAt_of_callee sp_cur epochDirectionMergeStack (by decide))))))) hpost1
      have ⟨hle, hsuf⟩ := proto_mergeMessage_suffix hed
      obtain ⟨sf, hsteps', hout'⟩ :=
        hok sm m' rest evs hed hevs hle hsuf hpcm hrunm hspm (htr.step htrm hcsm) hcsm hx0_0
          (hinv.of_keepsFrozen hsteps.keepsFrozen) R' hpost2 (hsteps.codeLoaded hL)
      exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [epochDirectionMergeSpecOfEnv, withLsCodeRoLoaded] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)
  · dsimp only [epochDirectionMergeSpecOfEnv, withLsCodeRoLoaded] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)
  · dsimp only [epochDirectionMergeSpecOfEnv, withLsCodeRoLoaded] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)

theorem SepWPpIPlaced.call_epochDirectionMerge [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl (epochDirectionMergeSpec A lim)))
    (wt : WireType) (msgPtr : BitVec 64) (msg : EpochDirectionPB)
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
    (hlen : bs.length < 2 ^ 63)
    (hfits : FitsEnv M lim st (EpochDirectionMergeEnv ⟨wt, msgPtr, msg, bufRef, slot, ptr, bs⟩))
    (hP : P = (epochDirectionPBCapOkAt A.repAlloc msgPtr bs.length msg ∗ (bufRef ↦₆₄ slot) ∗
      sliceCursorAt slot ptr bs ∗ A.pool lim st s ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
    (hok : ∀ (sf : State) (m' : EpochDirectionPB) (rest : List (BitVec 8))
        (evs : List AllocEvent),
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto wt) msg bs 98).toOption =
        some (m', rest) →
      EpochDirectionMergePostEnv ⟨wt, msgPtr, msg, bufRef, slot, ptr, bs⟩ evs →
      rest.length ≤ bs.length → IsDropSuffix bs rest →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = 0#64 →
      SepWPpIPlaced prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          epochDirectionPBCapOkAt A.repAlloc msgPtr rest.length m' ∗
          sliceCursorAfter slot ptr bs rest) ∗ F)
        Q Qp)
    (herr : ∀ (sf : State) (n : Nat) (m' : EpochDirectionPB) (evs : List AllocEvent),
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto wt) msg bs 98).toOption =
        none →
      EpochDirectionMergePostEnv ⟨wt, msgPtr, msg, bufRef, slot, ptr, bs⟩ evs →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 ≠ 0#64 → n ≤ 1 →
      SepWPpIPlaced prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) n ∗
          epochDirectionPBAt A.repAlloc msgPtr m' ∗
          memRegion slot 16 ∗ (ptr ↦ₛ bs)) ∗ F)
        Q Qp) :
    SepWPpIPlaced prog ret s P Q Qp :=
  SepWPpIPlaced.call_epochDirectionMerge_ofEnv
    (PreEnv := EpochDirectionMergeEnv) (PostEnv := EpochDirectionMergePostEnv)
    hcall wt msgPtr msg bufRef slot ptr bs st hpc hrun hsp hs0A hlr htr hx0 hx1 hx2 hlen hfits
    hP hok herr

/-! ## `ChainEpochPB` Framing Helpers, `DecodeStateLoopEnv` Bridges, & `grow_one` Wrapper -/

theorem optEpochDirectionPB_none_split48 (a : BitVec 64) :
    memRegion (a + 8#64) 48 ⊢
      ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 32,
        ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
        ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₃₂ w6) ∗
        memRegion (a + 52#64) 4 := by
  have hs1 := ProofLib.memRegion_split (a + 8#64) 8 40 (by decide)
  have hs2 := ProofLib.memRegion_split ((a + 8#64) + 8#64) 8 32 (by decide)
  have hs3 := ProofLib.memRegion_split (((a + 8#64) + 8#64) + 8#64) 8 24 (by decide)
  have hs4 := ProofLib.memRegion_split ((((a + 8#64) + 8#64) + 8#64) + 8#64) 8 16 (by decide)
  have hs5 := ProofLib.memRegion_split (((((a + 8#64) + 8#64) + 8#64) + 8#64) + 8#64) 8 8 (by decide)
  have hs6 := ProofLib.memRegion_split
    ((((((a + 8#64) + 8#64) + 8#64) + 8#64) + 8#64) + 8#64) 4 4 (by decide)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hs1 hs2 hs3 hs4 hs5 hs6
  rw [hs1, hs2, hs3, hs4, hs5, hs6,
    ProofLib.memRegion_eight (a + 8#64),
    ProofLib.memRegion_eight (a + 16#64),
    ProofLib.memRegion_eight (a + 24#64),
    ProofLib.memRegion_eight (a + 32#64),
    ProofLib.memRegion_eight (a + 40#64),
    ProofLib.memRegion_four (a + 48#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w6
  apply Entails.sepExists_elim; intro w5
  apply Entails.sepExists_elim; intro w4
  apply Entails.sepExists_elim; intro w3
  apply Entails.sepExists_elim; intro w2
  apply Entails.sepExists_elim; intro w1
  refine Entails.sepExists_right w1 (Entails.sepExists_right w2
    (Entails.sepExists_right w3 (Entails.sepExists_right w4
      (Entails.sepExists_right w5 (Entails.sepExists_right w6 ?_)))))
  exact Entails.of_eq (by sep_ac_rfl)

theorem optEpochDirectionPBCapOkAt_some (A : RustAlloc) (a : BitVec 64) (remLen : Nat)
    (d : EpochDirectionPB) :
    optEpochDirectionPBCapOkAt A a remLen (some d) = epochDirectionPBCapOkAt A a remLen d := rfl

theorem optEpochDirectionPBCapOkAt_none (A : RustAlloc) (a : BitVec 64) (remLen : Nat) :
    optEpochDirectionPBCapOkAt A a remLen none = (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 48 := rfl

theorem optEpochDirectionPBAt_some_eq (A : RustAlloc) (a : BitVec 64) (d : EpochDirectionPB) :
    optEpochDirectionPBAt A a (some d) = epochDirectionPBAt A a d := rfl

def epochDirectionPBCapOkRestAt (A : RustAlloc) (a : BitVec 64) (remLen : Nat)
    (cap1 : BitVec 64) (d : EpochDirectionPB) : SepProp :=
  (∃∗ ptr1 : BitVec 64,
    ((a + 8#64) ↦₆₄ ptr1) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 d.next.length) ∗
    vecU8Heap A cap1 ptr1 d.next) ∗
  vecU8CapOkAt A (a + 0x18#64) remLen d.prev ∗
  ((a + 0x30#64) ↦₃₂ d.ctr) ∗
  memRegion (a + 0x34#64) 4

theorem epochDirectionPBCapOkAt_expose_cap (A : RustAlloc) (a : BitVec 64) (remLen : Nat)
    (d : EpochDirectionPB) :
    epochDirectionPBCapOkAt A a remLen d ⊢
      ∃∗ cap1 : BitVec 64,
        ⌜BytesMergeCapOk cap1 remLen ∧ cap1.toNat < 2 ^ 63⌝ ∗
        (a ↦₆₄ cap1) ∗
        epochDirectionPBCapOkRestAt A a remLen cap1 d := by
  unfold epochDirectionPBCapOkAt
  rw [show vecU8CapOkAt A a remLen d.next =
    ∃∗ cap1 : BitVec 64, ∃∗ ptr1 : BitVec 64,
      ⌜BytesMergeCapOk cap1 remLen⌝ ∗ vecU8At A a cap1 ptr1 d.next from rfl]
  simp only [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro cap1
  apply Entails.sepExists_elim; intro ptr1
  refine Entails.sepExists_right cap1 ?_
  simp only [sepConj_assoc, sepConj_pure_left_comm]
  apply Entails.pure_left; intro hcap
  rw [vecU8At_eq_header_heap]
  unfold vecHeader
  simp only [sepConj_assoc]
  have hlt_ent := vecU8Heap_cap_lt A cap1 ptr1 d.next
  have hreord1 :
      (a ↦₆₄ cap1) ∗ ((a + 8#64) ↦₆₄ ptr1) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 d.next.length) ∗
        vecU8Heap A cap1 ptr1 d.next ∗
        vecU8CapOkAt A (a + 0x18#64) remLen d.prev ∗
        ((a + 0x30#64) ↦₃₂ d.ctr) ∗ memRegion (a + 0x34#64) 4 =
      vecU8Heap A cap1 ptr1 d.next ∗
        ((a ↦₆₄ cap1) ∗ ((a + 8#64) ↦₆₄ ptr1) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 d.next.length) ∗
          vecU8CapOkAt A (a + 0x18#64) remLen d.prev ∗
          ((a + 0x30#64) ↦₃₂ d.ctr) ∗ memRegion (a + 0x34#64) 4) := by sep_ac_rfl
  rw [hreord1]
  refine Entails.trans (sepConj_mono_left hlt_ent) ?_
  rw [sepConj_assoc]
  apply Entails.pure_left; intro hcap_lt
  apply Entails.pure_right ⟨hcap, hcap_lt⟩
  unfold epochDirectionPBCapOkRestAt
  have hreord2 :
      vecU8Heap A cap1 ptr1 d.next ∗ ((a ↦₆₄ cap1) ∗ ((a + 8#64) ↦₆₄ ptr1) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 d.next.length) ∗
        vecU8CapOkAt A (a + 0x18#64) remLen d.prev ∗
        ((a + 0x30#64) ↦₃₂ d.ctr) ∗ memRegion (a + 0x34#64) 4) =
      (a ↦₆₄ cap1) ∗
        (((a + 8#64) ↦₆₄ ptr1) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 d.next.length) ∗
          vecU8Heap A cap1 ptr1 d.next) ∗
        vecU8CapOkAt A (a + 0x18#64) remLen d.prev ∗
        ((a + 0x30#64) ↦₃₂ d.ctr) ∗ memRegion (a + 0x34#64) 4 := by sep_ac_rfl
  rw [hreord2]
  exact sepConj_mono_right (sepConj_mono_left (Entails.sepExists_right ptr1 (Entails.refl _)))

theorem epochDirectionPBCapOkAt_fold_cap (A : RustAlloc) (a cap1 : BitVec 64) (remLen : Nat)
    (d : EpochDirectionPB) (hcap : BytesMergeCapOk cap1 remLen) :
    (a ↦₆₄ cap1) ∗ epochDirectionPBCapOkRestAt A a remLen cap1 d ⊢
      epochDirectionPBCapOkAt A a remLen d := by
  unfold epochDirectionPBCapOkAt epochDirectionPBCapOkRestAt
  rw [show vecU8CapOkAt A a remLen d.next =
    ∃∗ cap1 : BitVec 64, ∃∗ ptr1 : BitVec 64,
      ⌜BytesMergeCapOk cap1 remLen⌝ ∗ vecU8At A a cap1 ptr1 d.next from rfl]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro ptr1
  refine Entails.sepExists_right cap1 (Entails.sepExists_right ptr1 ?_)
  simp only [sepConj_assoc, sepConj_pure_left_comm]
  apply Entails.pure_right hcap
  rw [vecU8At_eq_header_heap]
  unfold vecHeader
  exact Entails.of_eq (by sep_ac_rfl)

abbrev chainEpochPBCapOkAt_eq := @chainEpochPBCapOkAt_eq_placed

theorem chainEpochPBAt_eq (A : RustAlloc) (sp : BitVec 64) (ep : ChainEpochPB) :
    chainEpochPBAt A (sp - 688#64) ep =
      optEpochDirectionPBAt A (sp - 688#64) ep.send ∗
      optEpochDirectionPBAt A (sp - 632#64) ep.recv := by
  unfold chainEpochPBAt
  have ha : sp - 688#64 + 0x38#64 = sp - 632#64 := by bv_omega
  rw [ha]

theorem epochLoop_cursor_to_epochErrFrame_placed [LibsignalPlacement] {M : AllocCostModel}
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (x : DecodeStateGhost) (cur : List (BitVec 8)) (remSt remEp : Nat)
    (curSt : PqRatchetState) (curEpoch : ChainEpochPB) (s0 s : State) :
    sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) remSt curSt ∗
      chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) remEp curEpoch ∗
      memRegion (s0.sp - 576#64) 240 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s ⊢
      decodeStateEpochErrFramePlaced H_inner A lim st x curSt curEpoch s0 s := by
  dsimp only [decodeStateLoopCommonPlaced, decodeStateEpochErrFramePlaced,
    decodeStateEpochErrTailFramePlaced]
  have h1 := sliceCursorAfter_to_memRegion s0.sp x.st.ptr x.st.bytes cur
  have h2 := protoPqRatchetStateCapOkAt_entails_protoPqRatchetStateAt H_inner A.repAlloc
    (s0.sp - 1040#64) remSt curSt
  have h3 := chainEpochPBCapOkAt_entails_chainEpochPBAt A.repAlloc (s0.sp - 688#64) remEp curEpoch
  have hst := vecArg_join_bytes A.repAlloc x.st
  have hlow := lower_352_fold s0.sp
  have hup := upper_240_fold s0.sp (s0.sp - 1056#64)
  refine Entails.trans (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono_left h3))) ?_
  have hreord :
      (memRegion (s0.sp - 1056#64) 16 ∗ (x.st.ptr ↦ₛ x.st.bytes)) ∗
        protoPqRatchetStateAt H_inner A.repAlloc (s0.sp - 1040#64) curSt ∗
        chainEpochPBAt A.repAlloc (s0.sp - 688#64) curEpoch ∗
        memRegion (s0.sp - 576#64) 240 ∗
        (v1StateJumpTablesPlacedAt ∗ vecArgRestAt A.repAlloc x.st ∗ memRegion x.outPtr 352 ∗
          A.pool lim st s ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          memRegion (s0.sp - 1392#64) 336 ∗ ((s0.sp - 336#64) ↦₆₄ (s0.sp - 1056#64)) ∗
          memRegion (s0.sp - 328#64) 224 ∗ memRegion (s0.sp - 104#64) 8 ∗
          decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
            (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
            (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
            (s0.readReg64 .x20) (s0.readReg64 .x19)) =
      chainEpochPBAt A.repAlloc (s0.sp - 688#64) curEpoch ∗
        v1StateJumpTablesPlacedAt ∗
        ((x.st.ptr ↦ₛ x.st.bytes) ∗ vecArgRestAt A.repAlloc x.st) ∗
        memRegion x.outPtr 352 ∗ A.pool lim st s ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
        (memRegion (s0.sp - 1392#64) 336 ∗ memRegion (s0.sp - 1056#64) 16) ∗
        protoPqRatchetStateAt H_inner A.repAlloc (s0.sp - 1040#64) curSt ∗
        memRegion (s0.sp - 576#64) 240 ∗
        (((s0.sp - 336#64) ↦₆₄ (s0.sp - 1056#64)) ∗ memRegion (s0.sp - 328#64) 224 ∗
          memRegion (s0.sp - 104#64) 8) ∗
        decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
          (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
          (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
          (s0.readReg64 .x20) (s0.readReg64 .x19) := by sep_ac_rfl
  rw [hreord]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono hst (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono hlow (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left hup)))))))))

theorem epochLoop_calleeErr_to_epochErrFrame_placed [LibsignalPlacement] {M : AllocCostModel}
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (x : DecodeStateGhost) {cur : List (BitVec 8)}
    (hcur_le : cur.length ≤ x.st.bytes.length) (hcur_suf : IsDropSuffix x.st.bytes cur)
    (remSt : Nat) (curSt : PqRatchetState) (curEpoch : ChainEpochPB) (s0 s : State) :
    memRegion (s0.sp - 1056#64) 16 ∗
      ((x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) ↦ₛ cur) ∗
      (x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) remSt curSt ∗
      chainEpochPBAt A.repAlloc (s0.sp - 688#64) curEpoch ∗
      memRegion (s0.sp - 576#64) 240 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s ⊢
      decodeStateEpochErrFramePlaced H_inner A lim st x curSt curEpoch s0 s := by
  dsimp only [decodeStateLoopCommonPlaced, decodeStateEpochErrFramePlaced,
    decodeStateEpochErrTailFramePlaced]
  have h1 := pointsToBytes_prefix_join (ptr := x.st.ptr) hcur_le hcur_suf
  have hst := Entails.trans (sepConj_mono_left h1) (vecArg_join_bytes A.repAlloc x.st)
  have h2 := protoPqRatchetStateCapOkAt_entails_protoPqRatchetStateAt H_inner A.repAlloc
    (s0.sp - 1040#64) remSt curSt
  have hlow := lower_352_fold s0.sp
  have hup := upper_240_fold s0.sp (s0.sp - 1056#64)
  have hreord :
      memRegion (s0.sp - 1056#64) 16 ∗
        ((x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) ↦ₛ cur) ∗
        (x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) remSt curSt ∗
        chainEpochPBAt A.repAlloc (s0.sp - 688#64) curEpoch ∗
        memRegion (s0.sp - 576#64) 240 ∗
        (v1StateJumpTablesPlacedAt ∗ vecArgRestAt A.repAlloc x.st ∗ memRegion x.outPtr 352 ∗
          A.pool lim st s ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          memRegion (s0.sp - 1392#64) 336 ∗ ((s0.sp - 336#64) ↦₆₄ (s0.sp - 1056#64)) ∗
          memRegion (s0.sp - 328#64) 224 ∗ memRegion (s0.sp - 104#64) 8 ∗
          decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
            (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
            (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
            (s0.readReg64 .x20) (s0.readReg64 .x19)) =
      chainEpochPBAt A.repAlloc (s0.sp - 688#64) curEpoch ∗
        v1StateJumpTablesPlacedAt ∗
        (((x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
            ((x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) ↦ₛ cur)) ∗
          vecArgRestAt A.repAlloc x.st) ∗
        memRegion x.outPtr 352 ∗ A.pool lim st s ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
        (memRegion (s0.sp - 1392#64) 336 ∗ memRegion (s0.sp - 1056#64) 16) ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) remSt curSt ∗
        memRegion (s0.sp - 576#64) 240 ∗
        (((s0.sp - 336#64) ↦₆₄ (s0.sp - 1056#64)) ∗ memRegion (s0.sp - 328#64) 224 ∗
          memRegion (s0.sp - 104#64) 8) ∗
        decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
          (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
          (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
          (s0.readReg64 .x20) (s0.readReg64 .x19) := by sep_ac_rfl
  rw [hreord]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono hst (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono hlow (sepConj_mono h2
      (sepConj_mono_right (sepConj_mono_left hup)))))))))

theorem fitsEnv_epochDirectionMerge_of_loop {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {rem maxLen polyCapBound : Nat} {x : EpochDirectionMergeGhost}
    (hlen : x.bs.length ≤ maxLen) (hf : 4 * x.bs.length + 8 ≤ rem)
    (hFit : FitsEnv M lim st (DecodeStateLoopEnv rem maxLen polyCapBound)) :
    FitsEnv M lim st (EpochDirectionMergeEnv x) :=
  FitsEnv.decodeStateLoop_mono hf hlen (Nat.zero_le _) hFit

theorem decodeStateLoopEnv_of_epochDirectionMergePost_ok {maxLen polyCapBound : Nat}
    {x : EpochDirectionMergeGhost} {m' : EpochDirectionPB} {rest : List (BitVec 8)}
    {evs : List AllocEvent}
    (hlen : x.bs.length ≤ maxLen)
    (hok :
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
        some (m', rest))
    (hevs : EpochDirectionMergePostEnv x evs) :
    DecodeStateLoopEnv (4 * (x.bs.length - rest.length)) maxLen polyCapBound evs := by
  dsimp only [EpochDirectionMergePostEnv] at hevs
  rw [hok] at hevs
  exact hevs.mono (Nat.le_refl _) hlen (Nat.zero_le _)

theorem decodeStateLoopEnv_of_epochDirectionMergePost_err {maxLen polyCapBound : Nat}
    {x : EpochDirectionMergeGhost} {evs : List AllocEvent}
    (hlen : x.bs.length ≤ maxLen)
    (herr :
      (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
        none)
    (hevs : EpochDirectionMergePostEnv x evs) :
    DecodeStateLoopEnv (4 * x.bs.length + 8) maxLen polyCapBound evs := by
  dsimp only [EpochDirectionMergePostEnv] at hevs
  rw [herr] at hevs
  exact hevs.mono (Nat.le_refl _) hlen (Nat.zero_le _)

theorem fitsEnv_epochMergeErr_push0_of_loop {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {rem maxLen polyCapBound n : Nat} (hn : n ≤ 4) (hrem : 1 ≤ rem)
    (hFit : FitsEnv M lim st (DecodeStateLoopEnv rem maxLen polyCapBound)) :
    FitsEnv M lim st (DecodeErrorPushEnv n) :=
  fitsEnv_decodeErrorPush_of_loop hn hrem hFit

theorem fitsEnv_epochMergeErr_push1_of_loop {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {rem maxLen polyCapBound n : Nat} (hn : n + 1 ≤ 4) (hrem : 3 ≤ rem)
    (hFit : FitsEnv M lim st (DecodeStateLoopEnv rem maxLen polyCapBound)) :
    ∀ evs_p0 evs_d, DecodeErrorPushEnv n evs_p0 → FreeOnlyEvs evs_d →
      FitsEnv M lim (M.stepEvents evs_d (M.stepEvents evs_p0 st)) (DecodeErrorPushEnv (n + 1)) := by
  intro evs_p0 evs_d hp0 hd
  have h1 : FitsEnv M lim st (DecodeStateLoopEnv ((rem - 1) + 1) maxLen polyCapBound) :=
    FitsEnv.decodeStateLoop_mono (by omega) (Nat.le_refl _) (Nat.le_refl _) hFit
  exact fitsEnv_epochDrop_push1_of_loop hn (by omega)
    (FitsEnv.decodeStateLoop_tail (.pushErr (by omega) hp0) h1) evs_d hd

theorem fitsEnv_epochMergeErr_push2_of_loop {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {rem maxLen polyCapBound n : Nat} (hn : n + 2 ≤ 4) (hrem : 4 ≤ rem)
    (hFit : FitsEnv M lim st (DecodeStateLoopEnv rem maxLen polyCapBound)) :
    ∀ evs_p0 evs_d evs_p1,
      DecodeErrorPushEnv n evs_p0 → FreeOnlyEvs evs_d → DecodeErrorPushEnv (n + 1) evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs_d (M.stepEvents evs_p0 st)))
        (DecodeErrorPushEnv (n + 2)) := by
  intro evs_p0 evs_d evs_p1 hp0 hd hp1
  have h1 : FitsEnv M lim st (DecodeStateLoopEnv ((rem - 1) + 1) maxLen polyCapBound) :=
    FitsEnv.decodeStateLoop_mono (by omega) (Nat.le_refl _) (Nat.le_refl _) hFit
  exact fitsEnv_epochDrop_push2_of_loop hn (by omega)
    (FitsEnv.decodeStateLoop_tail (.pushErr (by omega) hp0) h1) evs_d evs_p1 hd hp1

theorem fitsEnv_skipField3_of_loop {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {rem maxLen polyCapBound : Nat} {x : SkipFieldGhost}
    (hrem : 1 ≤ rem)
    (hFit : FitsEnv M lim st (DecodeStateLoopEnv rem maxLen polyCapBound)) :
    FitsEnv M lim st (SkipField3Env x) :=
  FitsEnv.decodeStateLoop_head (fuel := rem - 1)
    (fun _ he => DecodeStateIterEnv.of_skipField3 he)
    (FitsEnv.decodeStateLoop_mono (by omega) (Nat.le_refl _) (Nat.le_refl _) hFit)

theorem decodeStateLoopEnv_of_skipField3 {maxLen polyCapBound : Nat}
    {x : SkipFieldGhost} {evs : List AllocEvent}
    (hevs : SkipField3Env x evs) :
    DecodeStateLoopEnv 1 maxLen polyCapBound evs :=
  DecodeStateLoopEnv.single (fuel := 0) (DecodeStateIterEnv.of_skipField3 hevs)

theorem fitsEnv_growOneChainEpoch_of_loop {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {rem maxLen polyCapBound : Nat} {cap : BitVec 64}
    (hcap : cap.toNat ≤ 2 * maxLen + 4) (hrem : 1 ≤ rem)
    (hFit : FitsEnv M lim st (DecodeStateLoopEnv rem maxLen polyCapBound)) :
    FitsEnv M lim st (GrowOneStrideEnv cap 112 8) :=
  FitsEnv.decodeStateLoop_head (fuel := rem - 1)
    (fun _ he => DecodeStateIterEnv.growChainEpoch cap hcap he)
    (FitsEnv.decodeStateLoop_mono (by omega) (Nat.le_refl _) (Nat.le_refl _) hFit)

theorem decodeStateLoopEnv_of_growOneChainEpoch {maxLen polyCapBound : Nat}
    {cap : BitVec 64} {evs : List AllocEvent}
    (hcap : cap.toNat ≤ 2 * maxLen + 4)
    (hevs : GrowOneStrideEnv cap 112 8 evs) :
    DecodeStateLoopEnv 1 maxLen polyCapBound evs :=
  DecodeStateLoopEnv.single (fuel := 0) (.growChainEpoch cap hcap hevs)

theorem SepWPpIPlaced.call_growOneChainEpoch [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (growOneStrideFullSpec M A lim 112 8))
    (v cap ptr : BitVec 64) (bs : List (BitVec 8)) (st : M.σ)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = v)
    (hlen : bs.length = cap.toNat * 112)
    (hptr : ptr ≠ 0#64)
    (hbound : max (2 * cap.toNat) 4 * 112 + 8 ≤ 2 ^ 63)
    (hfits : FitsEnv M lim st (GrowOneStrideEnv cap 112 8))
    (hP : P = ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
      (if cap = 0#64 then emp else A.repAlloc.live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) ∗
      A.pool lim st s ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
    (hok : ∀ (sf : State) (p' : BitVec 64) (evs : List AllocEvent),
      p' ≠ 0#64 → p'.toNat % 8 = 0 →
      GrowOneStrideEnv cap 112 8 evs →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      SepWPpIPlaced prog ret sf
        (((v ↦₆₄ BitVec.ofNat 64 (max (2 * cap.toNat) 4)) ∗ ((v + 8#64) ↦₆₄ p') ∗
          A.repAlloc.live p' (max (2 * cap.toNat) 4 * 112) 8 ∗ (p' ↦ₛ bs) ∗
          memRegion (p' + BitVec.ofNat 64 bs.length) ((max (2 * cap.toNat) 4 - cap.toNat) * 112) ∗
          A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
        Q Qp) :
    SepWPpIPlaced prog ret s P Q Qp := by
  intro hinv R' hm hL
  let sp_cur := s0.sp - 1392#64
  let x_go : GrowGhost := (v, cap, ptr, bs)
  let callee_stk := (allocHookStack + 48) + 64
  let F_ext := memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
    (v1StateMergeStack - callee_stk) ∗ F
  have hpre : s.mem ⊨ (growOneStrideFullSpec M A lim 112 8).pre (x_go, st) s ∗ (F_ext ∗ R') := by
    dsimp only [growOneStrideFullSpec, growOneStrideFullSpecWithStack, x_go]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hlen, hptr, hbound, hfits⟩, ?_⟩
    rw [hP] at hm
    simp only [RustCliAllocBudget.repAlloc_live] at hm
    have hm1 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (stackAt_to_callee sp_cur callee_stk (by decide)))))))) hm
    refine Satisfies.mono (Entails.of_eq ?_) hm1
    dsimp only [sp_cur, callee_stk, F_ext]; sep_ac_rfl
  have halign : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome (x_go, st) (F_ext ∗ R') s hpc hrun hpre halign hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · dsimp only [growOneStrideFullSpec, growOneStrideFullSpecWithStack, x_go] at hpost
    rw [hsp] at hpost
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
    rcases hpost with ⟨p', hpost⟩
    have hpost_pure : sm.mem ⊨ ⌜sm.trace = s.trace⌝ ∗ (⌜p' ≠ 0#64 ∧ p'.toNat % 8 = 0⌝ ∗
        (((v ↦₆₄ BitVec.ofNat 64 (max (2 * cap.toNat) 4)) ∗ ((v + 8#64) ↦₆₄ p') ∗
          A.repAlloc.live p' (max (2 * cap.toNat) 4 * 112) 8 ∗ (p' ↦ₛ bs) ∗
          memRegion (p' + BitVec.ofNat 64 bs.length)
            ((max (2 * cap.toNat) 4 - cap.toNat) * 112) ∗
          A.pool lim (M.stepEvents (growOneStrideEvents cap 112 8) st) sm ∗
          (memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
            (v1StateMergeStack - callee_stk) ∗
            stackAt sp_cur callee_stk)) ∗ F) ∗ R') := by
      refine Satisfies.mono (Entails.of_eq ?_) hpost
      simp only [RustCliAllocBudget.repAlloc_live]
      dsimp only [sp_cur, callee_stk, F_ext]; sep_ac_rfl
    rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost_pure
    rcases hpost_pure with ⟨htrm, ⟨hp'_ne, hp'_al⟩, hpost1⟩
    rw [hlr] at hpcm; rw [hsp] at hspm
    have hpost2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right
          (stackAt_of_callee sp_cur callee_stk (by decide)))))))))) hpost1
    obtain ⟨sf, hsteps', hout'⟩ :=
      hok sm p' (growOneStrideEvents cap 112 8) hp'_ne hp'_al rfl hpcm hrunm hspm
        (htr.step htrm hcsm) hcsm (hinv.of_keepsFrozen hsteps.keepsFrozen) R' hpost2
        (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [growOneStrideFullSpec, growOneStrideFullSpecWithStack] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)
  · dsimp only [growOneStrideFullSpec, growOneStrideFullSpecWithStack] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)
  · dsimp only [growOneStrideFullSpec, growOneStrideFullSpecWithStack] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlacedBudgetAux

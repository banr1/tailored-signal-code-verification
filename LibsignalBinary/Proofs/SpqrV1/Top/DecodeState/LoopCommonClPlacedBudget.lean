/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErrClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationErrClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Code-Loaded Shared Call Wrappers for `spqr::decode_state` (Block `325`)

Proves budget-threaded panic-aware code-loaded call wrappers (`decode_varint`, `skip_field`,
and `ChainParams::merge`) for `spqr::decode_state` under `LibsignalPlacement`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonClPlacedBudget

open Arm64 Arm64.Obj ProofLib SepProp
open CryptoVerification (LibsignalPlacement lsmpl withLsCodeLoaded)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint decodeVarint_length skipField skip_length)
open CryptoVerification.LibsignalTripleRatchet (decodeErrorAtStackLen)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (DecodeVarintSlowGhost IsDropSuffix SkipFieldGhost decodeVarint_suffix skip_suffix
   sliceCursorAfter sliceCursorAt)
open CryptoVerification.SpqrV1.Varint (decodeVarint2Stack skipField3Stack)
open CryptoVerification.SpqrV1.ProtoRepr (chainParamsPBAt)
open CryptoVerification.SpqrV1.Prost.MessageMerge (codecWireTypeToProto v1StateMergeStack)
open CryptoVerification.LibsignalSpqrV1 (ChainParamsPB)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Top.DecodeState
  (ChainParamsMergeGhost TraceVRegs chainParamsMergeStack proto_mergeMessage_suffix
   sp_sub_1392_aligned stackAt_of_callee stackAt_to_callee)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget (SkipField3Env skipField3BudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
  (DecodeVarint2Env decodeVarint2Spec decodeVarint2SpecGen)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget
  (ChainParamsMergeEnv ChainParamsMergePostEnv chainParamsMergeSpec chainParamsMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget (SepWPpIPlaced)

/-! ## Code-Loaded Budget-Threaded Panic-Aware Call Wrappers (`decode_varint`, `skip_field`, `ChainParams::merge`) -/

theorem SepWPpIPlaced.call_decodeVarint2_cl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (bufRef slot ptr : BitVec 64) (bs : List (BitVec 8)) (st : M.σ)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = bufRef)
    (hlen : bs.length < 2 ^ 63)
    (hfits : FitsEnv M lim st (DecodeVarint2Env bs))
    (hP : P = ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr bs ∗ A.pool lim st s ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
    (hok : ∀ (sf : State) (v : BitVec 64) (rest : List (BitVec 8)) (evs : List AllocEvent),
      decodeVarint bs = some (v, rest) →
      DecodeVarint2Env bs evs →
      rest.length < bs.length → IsDropSuffix bs rest →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = 0#64 → sf.readReg64 .x1 = v →
      SepWPpIPlaced prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          sliceCursorAfter slot ptr bs rest) ∗ F)
        Q Qp)
    (herr : ∀ (sf : State) (evs : List AllocEvent),
      decodeVarint bs = none →
      DecodeVarint2Env bs evs →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = 1#64 → sf.readReg64 .x1 ≠ 0#64 →
      SepWPpIPlaced prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x1) 0 ∗
          memRegion slot 16 ∗ (ptr ↦ₛ bs)) ∗ F)
        Q Qp) :
    SepWPpIPlaced prog ret s P Q Qp := by
  intro hinv R' hm hL
  let sp_cur := s0.sp - 1392#64
  let x_dv : DecodeVarintSlowGhost := ⟨bufRef, slot, ptr, bs⟩
  let F_ext := memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
    (v1StateMergeStack - decodeVarint2Stack) ∗ F
  have hpre : s.mem ⊨
      (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)).pre (x_dv, st) s ∗ (F_ext ∗ R') := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hinv.1, ?_⟩
    dsimp only [decodeVarint2Spec, decodeVarint2SpecGen, x_dv]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hlen, hfits⟩, ?_⟩
    rw [hP] at hm
    have hm1 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (stackAt_to_callee sp_cur decodeVarint2Stack (by decide))))))) hm
    refine Satisfies.mono (Entails.of_eq ?_) hm1
    dsimp only [sp_cur, F_ext, decodeVarint2Stack]; sep_ac_rfl
  have halign : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome (x_dv, st) (F_ext ∗ R') s hpc hrun hpre halign hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · change sm.mem ⊨ (decodeVarint2Spec A lim).post (x_dv, st) s sm ∗ (F_ext ∗ R') at hpost
    dsimp only [decodeVarint2Spec, decodeVarint2SpecGen, x_dv] at hpost
    rw [hsp] at hpost
    rcases hdv : decodeVarint bs with _ | ⟨v, rest⟩
    · simp only [hdv, sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
      rcases hpost with ⟨evs, hpost⟩
      have hpost_pure : sm.mem ⊨ ⌜DecodeVarint2Env bs evs⌝ ∗
          (⌜sm.trace = s.trace⌝ ∗ (⌜sm.readReg64 .x0 = 1#64⌝ ∗ (⌜sm.readReg64 .x1 ≠ 0#64⌝ ∗
            (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sm ∗
              (memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
                (v1StateMergeStack - decodeVarint2Stack) ∗
                stackAt sp_cur decodeVarint2Stack) ∗
              decodeErrorAtStackLen A.repAlloc (sm.readReg64 .x1) 0 ∗
              memRegion slot 16 ∗ (ptr ↦ₛ bs)) ∗ F) ∗ R'))) := by
        refine Satisfies.mono (Entails.of_eq ?_) hpost
        dsimp only [sp_cur, F_ext, decodeVarint2Stack]; sep_ac_rfl
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj, satisfies_pure_sepConj,
        satisfies_pure_sepConj] at hpost_pure
      rcases hpost_pure with ⟨hevs, htrm, hx0_1, hx1_ne, hpost1⟩
      rw [hlr] at hpcm; rw [hsp] at hspm
      have hpost2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (stackAt_of_callee sp_cur decodeVarint2Stack (by decide))))))) hpost1
      obtain ⟨sf, hsteps', hout'⟩ :=
        herr sm evs hdv hevs hpcm hrunm hspm (htr.step htrm hcsm) hcsm hx0_1 hx1_ne
          (hinv.of_keepsFrozen hsteps.keepsFrozen) R' hpost2 (hsteps.codeLoaded hL)
      exact ⟨sf, hsteps.trans hsteps', hout'⟩
    · simp only [hdv, sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
      rcases hpost with ⟨evs, hpost⟩
      have hpost_pure : sm.mem ⊨ ⌜DecodeVarint2Env bs evs⌝ ∗
          (⌜sm.trace = s.trace⌝ ∗ (⌜sm.readReg64 .x0 = 0#64 ∧ sm.readReg64 .x1 = v⌝ ∗
            (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sm ∗
              (memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
                (v1StateMergeStack - decodeVarint2Stack) ∗
                stackAt sp_cur decodeVarint2Stack) ∗
              sliceCursorAfter slot ptr bs rest) ∗ F) ∗ R')) := by
        refine Satisfies.mono (Entails.of_eq ?_) hpost
        dsimp only [sp_cur, F_ext, decodeVarint2Stack]; sep_ac_rfl
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost_pure
      rcases hpost_pure with ⟨hevs, htrm, ⟨hx0_0, hx1_v⟩, hpost1⟩
      rw [hlr] at hpcm; rw [hsp] at hspm
      have hpost2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (stackAt_of_callee sp_cur decodeVarint2Stack (by decide))))))) hpost1
      obtain ⟨sf, hsteps', hout'⟩ :=
        hok sm v rest evs hdv hevs (decodeVarint_length hdv) (decodeVarint_suffix hdv)
          hpcm hrunm hspm (htr.step htrm hcsm) hcsm hx0_0 hx1_v
          (hinv.of_keepsFrozen hsteps.keepsFrozen) R' hpost2 (hsteps.codeLoaded hL)
      exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [withLsCodeLoaded, decodeVarint2Spec, decodeVarint2SpecGen] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)
  · dsimp only [withLsCodeLoaded, decodeVarint2Spec, decodeVarint2SpecGen] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)
  · dsimp only [withLsCodeLoaded, decodeVarint2Spec, decodeVarint2SpecGen] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)

theorem SepWPpIPlaced.call_skipField3_cl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl (skipField3BudgetSpec M A lim)))
    (wt : WireType) (tag depth : Nat) (bufRef slot ptr : BitVec 64) (bs : List (BitVec 8))
    (st : M.σ) {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : TraceVRegs s s0)
    (hx0 : (s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 wt.toNat)
    (hx1 : (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 tag)
    (htag : tag < 2 ^ 32)
    (hx2 : s.readReg64 .x2 = bufRef)
    (hx3 : (s.readReg64 .x3).setWidth 32 = BitVec.ofNat 32 depth)
    (hdepth : depth ≤ 100)
    (hlen : bs.length < 2 ^ 63)
    (hfits : FitsEnv M lim st (SkipField3Env ⟨wt, tag, depth, bufRef, slot, ptr, bs⟩))
    (hP : P = ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr bs ∗ A.pool lim st s ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
    (hok : ∀ (sf : State) (rest : List (BitVec 8)) (evs : List AllocEvent),
      skipField (2 * bs.length + 2) depth tag wt bs = some rest →
      SkipField3Env ⟨wt, tag, depth, bufRef, slot, ptr, bs⟩ evs →
      rest.length ≤ bs.length → IsDropSuffix bs rest →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = 0#64 →
      SepWPpIPlaced prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          sliceCursorAfter slot ptr bs rest) ∗ F)
        Q Qp)
    (herr : ∀ (sf : State) (evs : List AllocEvent),
      skipField (2 * bs.length + 2) depth tag wt bs = none →
      SkipField3Env ⟨wt, tag, depth, bufRef, slot, ptr, bs⟩ evs →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 ≠ 0#64 →
      SepWPpIPlaced prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) 0 ∗
          memRegion slot 16 ∗ (ptr ↦ₛ bs)) ∗ F)
        Q Qp) :
    SepWPpIPlaced prog ret s P Q Qp := by
  intro hinv R' hm hL
  let sp_cur := s0.sp - 1392#64
  let x_sf : SkipFieldGhost := ⟨wt, tag, depth, bufRef, slot, ptr, bs⟩
  have hM : skipField3Stack depth ≤ v1StateMergeStack := by
    have h100 : skipField3Stack 100 ≤ v1StateMergeStack := by decide
    have hmono : skipField3Stack depth ≤ skipField3Stack 100 := by unfold skipField3Stack; omega
    omega
  let F_ext := memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
    (v1StateMergeStack - skipField3Stack depth) ∗ F
  have hpre : s.mem ⊨
      (withLsCodeLoaded lsmpl (skipField3BudgetSpec M A lim)).pre (x_sf, st) s ∗ (F_ext ∗ R') := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hinv.1, ?_⟩
    dsimp only [skipField3BudgetSpec, x_sf]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, htag, hx2, hx3, by omega, hlen, hfits⟩, ?_⟩
    rw [hP] at hm
    have hm1 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (stackAt_to_callee sp_cur (skipField3Stack depth) hM)))))) hm
    refine Satisfies.mono (Entails.of_eq ?_) hm1
    dsimp only [sp_cur, F_ext]; sep_ac_rfl
  have halign : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome (x_sf, st) (F_ext ∗ R') s hpc hrun hpre halign hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · change sm.mem ⊨ (skipField3BudgetSpec M A lim).post (x_sf, st) s sm ∗ (F_ext ∗ R') at hpost
    dsimp only [skipField3BudgetSpec, x_sf] at hpost
    rw [hsp] at hpost
    rcases hsf : skipField (2 * bs.length + 2) depth tag wt bs with _ | rest
    · simp only [hsf, sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
      rcases hpost with ⟨evs, hpost⟩
      have hpost_pure : sm.mem ⊨ ⌜SkipField3Env x_sf evs⌝ ∗
          (⌜sm.trace = s.trace⌝ ∗ (⌜sm.readReg64 .x0 ≠ 0#64⌝ ∗
            (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sm ∗
              (memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
                (v1StateMergeStack - skipField3Stack depth) ∗
                stackAt sp_cur (skipField3Stack depth)) ∗
              decodeErrorAtStackLen A.repAlloc (sm.readReg64 .x0) 0 ∗
              memRegion slot 16 ∗ (ptr ↦ₛ bs)) ∗ F) ∗ R')) := by
        refine Satisfies.mono (Entails.of_eq ?_) hpost
        dsimp only [sp_cur, F_ext]; sep_ac_rfl
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost_pure
      rcases hpost_pure with ⟨hevs, htrm, hx0_ne, hpost1⟩
      rw [hlr] at hpcm; rw [hsp] at hspm
      have hpost2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (stackAt_of_callee sp_cur (skipField3Stack depth) hM)))))) hpost1
      obtain ⟨sf, hsteps', hout'⟩ :=
        herr sm evs hsf hevs hpcm hrunm hspm (htr.step htrm hcsm) hcsm hx0_ne
          (hinv.of_keepsFrozen hsteps.keepsFrozen) R' hpost2 (hsteps.codeLoaded hL)
      exact ⟨sf, hsteps.trans hsteps', hout'⟩
    · simp only [hsf, sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
      rcases hpost with ⟨evs, hpost⟩
      have hpost_pure : sm.mem ⊨ ⌜SkipField3Env x_sf evs⌝ ∗
          (⌜sm.trace = s.trace⌝ ∗ (⌜sm.readReg64 .x0 = 0#64⌝ ∗
            (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sm ∗
              (memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
                (v1StateMergeStack - skipField3Stack depth) ∗
                stackAt sp_cur (skipField3Stack depth)) ∗
              sliceCursorAfter slot ptr bs rest) ∗ F) ∗ R')) := by
        refine Satisfies.mono (Entails.of_eq ?_) hpost
        dsimp only [sp_cur, F_ext]; sep_ac_rfl
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost_pure
      rcases hpost_pure with ⟨hevs, htrm, hx0_0, hpost1⟩
      rw [hlr] at hpcm; rw [hsp] at hspm
      have hpost2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (stackAt_of_callee sp_cur (skipField3Stack depth) hM)))))) hpost1
      have hle := (skip_length (2 * bs.length + 2)).1 depth tag wt bs rest hsf
      have hsuf := (skip_suffix (2 * bs.length + 2)).1 depth tag wt bs rest hsf
      obtain ⟨sf, hsteps', hout'⟩ :=
        hok sm rest evs hsf hevs hle hsuf hpcm hrunm hspm (htr.step htrm hcsm) hcsm hx0_0
          (hinv.of_keepsFrozen hsteps.keepsFrozen) R' hpost2 (hsteps.codeLoaded hL)
      exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [withLsCodeLoaded, skipField3BudgetSpec] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)
  · dsimp only [withLsCodeLoaded, skipField3BudgetSpec] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)
  · dsimp only [withLsCodeLoaded, skipField3BudgetSpec] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)

theorem SepWPpIPlaced.call_chainParamsMerge_cl_ofEnv [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : ChainParamsMergeGhost → List AllocEvent → Prop}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (chainParamsMergeSpecOfEnv A lim PreEnv PostEnv)))
    (wt : WireType) (msgPtr : BitVec 64) (msg : ChainParamsPB)
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
    (hP : P = (chainParamsPBAt msgPtr msg ∗ (bufRef ↦₆₄ slot) ∗
      sliceCursorAt slot ptr bs ∗ A.pool lim st s ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
    (hok : ∀ (sf : State) (m' : ChainParamsPB) (rest : List (BitVec 8)) (evs : List AllocEvent),
      (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto wt) msg bs 99).toOption =
        some (m', rest) →
      PostEnv ⟨wt, msgPtr, msg, bufRef, slot, ptr, bs⟩ evs →
      rest.length ≤ bs.length → IsDropSuffix bs rest →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = 0#64 →
      SepWPpIPlaced prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          chainParamsPBAt msgPtr m' ∗
          sliceCursorAfter slot ptr bs rest) ∗ F)
        Q Qp)
    (herr : ∀ (sf : State) (n : Nat) (m' : ChainParamsPB) (evs : List AllocEvent),
      (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto wt) msg bs 99).toOption =
        none →
      PostEnv ⟨wt, msgPtr, msg, bufRef, slot, ptr, bs⟩ evs →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 ≠ 0#64 → n ≤ 1 →
      SepWPpIPlaced prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) n ∗
          chainParamsPBAt msgPtr m' ∗
          memRegion slot 16 ∗ (ptr ↦ₛ bs)) ∗ F)
        Q Qp) :
    SepWPpIPlaced prog ret s P Q Qp := by
  intro hinv R' hm hL
  let sp_cur := s0.sp - 1392#64
  let x_cp : ChainParamsMergeGhost := ⟨wt, msgPtr, msg, bufRef, slot, ptr, bs⟩
  let F_ext := memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
    (v1StateMergeStack - chainParamsMergeStack) ∗ F
  have hpre : s.mem ⊨
      (withLsCodeLoaded lsmpl (chainParamsMergeSpecOfEnv A lim PreEnv PostEnv)).pre (x_cp, st) s ∗
        (F_ext ∗ R') := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hinv.1, ?_⟩
    dsimp only [chainParamsMergeSpecOfEnv, x_cp]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hlen, hfits⟩, ?_⟩
    rw [hP] at hm
    have hm1 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (stackAt_to_callee sp_cur chainParamsMergeStack (by decide)))))))) hm
    refine Satisfies.mono (Entails.of_eq ?_) hm1
    dsimp only [sp_cur, F_ext]; sep_ac_rfl
  have halign : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome (x_cp, st) (F_ext ∗ R') s hpc hrun hpre halign hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · change sm.mem ⊨
        (chainParamsMergeSpecOfEnv A lim PreEnv PostEnv).post (x_cp, st) s sm ∗ (F_ext ∗ R')
        at hpost
    dsimp only [chainParamsMergeSpecOfEnv, x_cp] at hpost
    rw [hsp] at hpost
    rcases hcp :
        (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto wt) msg bs 99).toOption
        with _ | ⟨m', rest⟩
    · simp only [hcp, sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
      rcases hpost with ⟨m', n, evs, hpost⟩
      have hpost_pure : sm.mem ⊨ ⌜PostEnv x_cp evs⌝ ∗
          (⌜sm.trace = s.trace⌝ ∗ (⌜sm.readReg64 .x0 ≠ 0#64⌝ ∗ (⌜n ≤ 1⌝ ∗
            (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sm ∗
              (memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
                (v1StateMergeStack - chainParamsMergeStack) ∗
                stackAt sp_cur chainParamsMergeStack) ∗
              decodeErrorAtStackLen A.repAlloc (sm.readReg64 .x0) n ∗
              chainParamsPBAt msgPtr m' ∗
              memRegion slot 16 ∗ (ptr ↦ₛ bs)) ∗ F) ∗ R'))) := by
        refine Satisfies.mono (Entails.of_eq ?_) hpost
        dsimp only [sp_cur, F_ext]; sep_ac_rfl
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj, satisfies_pure_sepConj,
        satisfies_pure_sepConj] at hpost_pure
      rcases hpost_pure with ⟨hevs, htrm, hx0_ne, hn, hpost1⟩
      rw [hlr] at hpcm; rw [hsp] at hspm
      have hpost2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (stackAt_of_callee sp_cur chainParamsMergeStack (by decide))))))) hpost1
      obtain ⟨sf, hsteps', hout'⟩ :=
        herr sm n m' evs hcp hevs hpcm hrunm hspm (htr.step htrm hcsm) hcsm hx0_ne hn
          (hinv.of_keepsFrozen hsteps.keepsFrozen) R' hpost2 (hsteps.codeLoaded hL)
      exact ⟨sf, hsteps.trans hsteps', hout'⟩
    · simp only [hcp, sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
      rcases hpost with ⟨evs, hpost⟩
      have hpost_pure : sm.mem ⊨ ⌜PostEnv x_cp evs⌝ ∗
          (⌜sm.trace = s.trace⌝ ∗ (⌜sm.readReg64 .x0 = 0#64⌝ ∗
            (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sm ∗
              (memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
                (v1StateMergeStack - chainParamsMergeStack) ∗
                stackAt sp_cur chainParamsMergeStack) ∗
              chainParamsPBAt msgPtr m' ∗
              sliceCursorAfter slot ptr bs rest) ∗ F) ∗ R')) := by
        refine Satisfies.mono (Entails.of_eq ?_) hpost
        dsimp only [sp_cur, F_ext]; sep_ac_rfl
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost_pure
      rcases hpost_pure with ⟨hevs, htrm, hx0_0, hpost1⟩
      rw [hlr] at hpcm; rw [hsp] at hspm
      have hpost2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (stackAt_of_callee sp_cur chainParamsMergeStack (by decide))))))) hpost1
      have ⟨hle, hsuf⟩ := proto_mergeMessage_suffix hcp
      obtain ⟨sf, hsteps', hout'⟩ :=
        hok sm m' rest evs hcp hevs hle hsuf hpcm hrunm hspm (htr.step htrm hcsm) hcsm hx0_0
          (hinv.of_keepsFrozen hsteps.keepsFrozen) R' hpost2 (hsteps.codeLoaded hL)
      exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [withLsCodeLoaded, chainParamsMergeSpecOfEnv] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)
  · dsimp only [withLsCodeLoaded, chainParamsMergeSpecOfEnv] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)
  · dsimp only [withLsCodeLoaded, chainParamsMergeSpecOfEnv] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)

theorem SepWPpIPlaced.call_chainParamsMerge_cl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl (chainParamsMergeSpec A lim)))
    (wt : WireType) (msgPtr : BitVec 64) (msg : ChainParamsPB)
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
    (hfits : FitsEnv M lim st (ChainParamsMergeEnv ⟨wt, msgPtr, msg, bufRef, slot, ptr, bs⟩))
    (hP : P = (chainParamsPBAt msgPtr msg ∗ (bufRef ↦₆₄ slot) ∗
      sliceCursorAt slot ptr bs ∗ A.pool lim st s ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
    (hok : ∀ (sf : State) (m' : ChainParamsPB) (rest : List (BitVec 8)) (evs : List AllocEvent),
      (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto wt) msg bs 99).toOption =
        some (m', rest) →
      ChainParamsMergePostEnv ⟨wt, msgPtr, msg, bufRef, slot, ptr, bs⟩ evs →
      rest.length ≤ bs.length → IsDropSuffix bs rest →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = 0#64 →
      SepWPpIPlaced prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          chainParamsPBAt msgPtr m' ∗
          sliceCursorAfter slot ptr bs rest) ∗ F)
        Q Qp)
    (herr : ∀ (sf : State) (n : Nat) (m' : ChainParamsPB) (evs : List AllocEvent),
      (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto wt) msg bs 99).toOption =
        none →
      ChainParamsMergePostEnv ⟨wt, msgPtr, msg, bufRef, slot, ptr, bs⟩ evs →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 ≠ 0#64 → n ≤ 1 →
      SepWPpIPlaced prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) n ∗
          chainParamsPBAt msgPtr m' ∗
          memRegion slot 16 ∗ (ptr ↦ₛ bs)) ∗ F)
        Q Qp) :
    SepWPpIPlaced prog ret s P Q Qp :=
  SepWPpIPlaced.call_chainParamsMerge_cl_ofEnv
    (PreEnv := ChainParamsMergeEnv) (PostEnv := ChainParamsMergePostEnv)
    hcall wt msgPtr msg bufRef slot ptr bs st hpc hrun hsp hs0A hlr htr hx0 hx1 hx2 hlen hfits
    hP hok herr

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonClPlacedBudget

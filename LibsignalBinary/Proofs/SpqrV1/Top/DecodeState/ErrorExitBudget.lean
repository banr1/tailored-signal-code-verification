/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExit
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Panic-Aware Error Helpers for `spqr::decode_state`

Defines the budget-threaded `decodeStatePost` and `decodeStatePanicPost` postconditions along
with panic-aware `SepWPp.call_decodeErrorPush` and `SepWPp.call_decodeErrorFrom` wrappers.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitBudget

open Arm64 ProofLib SepProp
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap decodeErrorAtStackLen decodeErrorHookStack)
open CryptoVerification.SpqrV1.Prost.MessageMerge (v1StateMergeStack)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost TraceVRegs V1InnerHeapPred sp_sub_1392_aligned
   stackAt_of_callee stackAt_to_callee)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget
  (DecodeErrorFromEnv DecodeErrorPushEnv decodeErrorFromBudgetSpec decodeErrorPushBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget
  (decodeStateSpecX decodeStateSpecXOfEnv)

abbrev decodeStatePostOfEnv {M : AllocCostModel} (H_inner : V1InnerHeapPred) (b : BitVec 64)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop)
    (x : DecodeStateGhost × M.σ) (s0 : State) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨ (decodeStateSpecXOfEnv H_inner b A lim PreEnv PostEnv).post x s0 sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

abbrev decodeStatePanicPostOfEnv {M : AllocCostModel} (H_inner : V1InnerHeapPred) (b : BitVec 64)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop)
    (x : DecodeStateGhost × M.σ) (s0 : State) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    (sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨ (decodeStateSpecXOfEnv H_inner b A lim PreEnv PostEnv).onPanic x s0 sf ∗ R)

abbrev decodeStatePost {M : AllocCostModel} (H_inner : V1InnerHeapPred) (b : BitVec 64)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : DecodeStateGhost × M.σ) (s0 : State) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (decodeStateSpecX H_inner b A lim).post x s0 sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

abbrev decodeStatePanicPost {M : AllocCostModel} (H_inner : V1InnerHeapPred) (b : BitVec 64)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : DecodeStateGhost × M.σ) (s0 : State) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (decodeStateSpecX H_inner b A lim).onPanic x s0 sf ∗ R)

theorem SepWPp.call_decodeErrorPush_gen {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (decodeErrorPushBudgetSpec M A lim))
    (d e : BitVec 64) (n : Nat) (st : M.σ) {s0 s : State}
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = d)
    (hn : n < 2 ^ 32)
    (hfits : FitsEnv M lim st (DecodeErrorPushEnv n))
    (hP : P = ((d ↦₆₄ e) ∗ decodeErrorAtStackLen A.repAlloc e n ∗ A.pool lim st s ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      DecodeErrorPushEnv n evs →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      SepWPp prog ret sf
        (((d ↦₆₄ e) ∗ decodeErrorAtStackLen A.repAlloc e (n + 1) ∗
          A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
        Q Qp)
    (hQp : ∀ sm P_f, (∀ R', ¬ (sm.mem ⊨ P_f ∗ R')) → Qp sm P_f) :
    SepWPp prog ret s P Q Qp := by
  let sp_cur := s0.sp - 1392#64
  let F_ext := memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
    (v1StateMergeStack - decodeErrorHookStack) ∗ F
  have halign : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  refine SepWPp.call (x := (d, e, n, st)) (F := F_ext) hcall hpc hrun halign hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    dsimp only [decodeErrorPushBudgetSpec]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hn, hfits⟩, ?_⟩
    rw [hP] at hm
    have hm1 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (stackAt_to_callee sp_cur decodeErrorHookStack (by decide))))))) hm
    refine Satisfies.mono (Entails.of_eq ?_) hm1
    dsimp only [sp_cur, F_ext]; sep_ac_rfl
  · intro sm _ R' _ hpost
    dsimp only [decodeErrorPushBudgetSpec] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)
  · intro sm _
    refine hQp sm _ (fun R' hm' => ?_)
    dsimp only [decodeErrorPushBudgetSpec] at hm'
    rw [sepConj_assoc] at hm'
    exact not_satisfies_false_sepConj hm'
  · intro sm hpcm hrunm hspm hcsm R' hpost hL
    rw [sepConj_assoc] at hpost
    dsimp only [decodeErrorPushBudgetSpec] at hpost
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨htrm, hpost⟩
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hpost⟩
    have hpost_env : sm.mem ⊨ ⌜DecodeErrorPushEnv n evs⌝ ∗
        (((d ↦₆₄ e) ∗ decodeErrorAtStackLen A.repAlloc e (n + 1) ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          (memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
            (v1StateMergeStack - decodeErrorHookStack) ∗
            stackAt sp_cur decodeErrorHookStack)) ∗ F) ∗ R' := by
      refine Satisfies.mono (Entails.of_eq ?_) hpost
      dsimp only [sp_cur, F_ext]; sep_ac_rfl
    rw [satisfies_pure_sepConj] at hpost_env
    rcases hpost_env with ⟨hevs, hpost1⟩
    rw [hsp] at hspm
    have hpost2 : sm.mem ⊨
        (((d ↦₆₄ e) ∗ decodeErrorAtStackLen A.repAlloc e (n + 1) ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          stackAt sp_cur v1StateMergeStack) ∗ F) ∗ R' :=
      Satisfies.mono (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (stackAt_of_callee sp_cur decodeErrorHookStack (by decide))))))) hpost1
    exact hnext sm evs hevs hpcm hrunm hspm (htr.step htrm hcsm) hcsm R' hpost2 hL
  · intro sm R' _ hpost
    exact False.elim (not_satisfies_false_sepConj hpost)

theorem SepWPp.call_decodeErrorPush {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (decodeErrorPushBudgetSpec M A lim))
    (d e : BitVec 64) (n : Nat) (st : M.σ) {x_outer : DecodeStateGhost × M.σ} {s0 s : State}
    {P F R : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = d)
    (hn : n < 2 ^ 32)
    (hfits : FitsEnv M lim st (DecodeErrorPushEnv n))
    (hP : P = ((d ↦₆₄ e) ∗ decodeErrorAtStackLen A.repAlloc e n ∗ A.pool lim st s ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      DecodeErrorPushEnv n evs →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      SepWPp prog ret sf
        (((d ↦₆₄ e) ∗ decodeErrorAtStackLen A.repAlloc e (n + 1) ∗
          A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
        Q (decodeStatePanicPost H_inner b A lim x_outer s0 R)) :
    SepWPp prog ret s P Q (decodeStatePanicPost H_inner b A lim x_outer s0 R) :=
  SepWPp.call_decodeErrorPush_gen hcall d e n st hpc hrun hsp hs0A hlr htr hx0 hn hfits hP hnext
    (fun _ _ h hm => False.elim (h R hm))

theorem SepWPp.call_decodeErrorFrom_gen {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (decodeErrorFromBudgetSpec M A lim))
    (k w : BitVec 64) (st : M.σ) {s0 s : State}
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = k)
    (hw : KindNoHeap w)
    (hfits : FitsEnv M lim st DecodeErrorFromEnv)
    (hP : P = ((k ↦₆₄ w) ∗ memRegion (k + 8#64) 40 ∗ A.pool lim st s ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
    (hnext : ∀ (sf : State) (v_k : BitVec 64) (evs : List AllocEvent),
      DecodeErrorFromEnv evs →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 ≠ 0#64 →
      SepWPp prog ret sf
        ((decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) 0 ∗ (k ↦₆₄ v_k) ∗ memRegion (k + 8#64) 40 ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
        Q Qp)
    (hQp : ∀ sm P_f, (∀ R', ¬ (sm.mem ⊨ P_f ∗ R')) → Qp sm P_f) :
    SepWPp prog ret s P Q Qp := by
  let sp_cur := s0.sp - 1392#64
  let F_ext := memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
    (v1StateMergeStack - decodeErrorHookStack) ∗ F
  have halign : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  refine SepWPp.call (x := (k, w, st)) (F := F_ext) hcall hpc hrun halign hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    dsimp only [decodeErrorFromBudgetSpec]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hw, hfits⟩, ?_⟩
    rw [hP] at hm
    have hm1 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (stackAt_to_callee sp_cur decodeErrorHookStack (by decide))))))) hm
    refine Satisfies.mono (Entails.of_eq ?_) hm1
    dsimp only [sp_cur, F_ext]; sep_ac_rfl
  · intro sm _ R' _ hpost
    dsimp only [decodeErrorFromBudgetSpec] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)
  · intro sm _
    refine hQp sm _ (fun R' hm' => ?_)
    dsimp only [decodeErrorFromBudgetSpec] at hm'
    rw [sepConj_assoc] at hm'
    exact not_satisfies_false_sepConj hm'
  · intro sm hpcm hrunm hspm hcsm R' hpost hL
    rw [sepConj_assoc] at hpost
    dsimp only [decodeErrorFromBudgetSpec] at hpost
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨hx0_ne, htrm⟩, hpost⟩
    rw [hsp] at hspm
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hpost⟩
    rw [ProofLib.memRegion_split' (b := k) (n := 8) (k := 40)
        (b' := k + 8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight k] at hpost
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
    rcases hpost with ⟨v_k, hpost⟩
    have hpost_env : sm.mem ⊨ ⌜DecodeErrorFromEnv evs⌝ ∗
        ((decodeErrorAtStackLen A.repAlloc (sm.readReg64 .x0) 0 ∗ (k ↦₆₄ v_k) ∗ memRegion (k + 8#64) 40 ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          (memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
            (v1StateMergeStack - decodeErrorHookStack) ∗
            stackAt sp_cur decodeErrorHookStack)) ∗ F) ∗ R' := by
      refine Satisfies.mono (Entails.of_eq ?_) hpost
      dsimp only [sp_cur, F_ext]; sep_ac_rfl
    rw [satisfies_pure_sepConj] at hpost_env
    rcases hpost_env with ⟨hevs, hpost1⟩
    have hpost2 : sm.mem ⊨
        ((decodeErrorAtStackLen A.repAlloc (sm.readReg64 .x0) 0 ∗ (k ↦₆₄ v_k) ∗ memRegion (k + 8#64) 40 ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt sp_cur v1StateMergeStack) ∗ F) ∗ R' :=
      Satisfies.mono (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (stackAt_of_callee sp_cur decodeErrorHookStack (by decide)))))))) hpost1
    exact hnext sm v_k evs hevs hpcm hrunm hspm (htr.step htrm hcsm) hcsm hx0_ne R' hpost2 hL
  · intro sm R' _ hpost
    exact False.elim (not_satisfies_false_sepConj hpost)

theorem SepWPp.call_decodeErrorFrom {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (decodeErrorFromBudgetSpec M A lim))
    (k w : BitVec 64) (st : M.σ) {x_outer : DecodeStateGhost × M.σ} {s0 s : State}
    {P F R : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = k)
    (hw : KindNoHeap w)
    (hfits : FitsEnv M lim st DecodeErrorFromEnv)
    (hP : P = ((k ↦₆₄ w) ∗ memRegion (k + 8#64) 40 ∗ A.pool lim st s ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
    (hnext : ∀ (sf : State) (v_k : BitVec 64) (evs : List AllocEvent),
      DecodeErrorFromEnv evs →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 ≠ 0#64 →
      SepWPp prog ret sf
        ((decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) 0 ∗ (k ↦₆₄ v_k) ∗ memRegion (k + 8#64) 40 ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
        Q (decodeStatePanicPost H_inner b A lim x_outer s0 R)) :
    SepWPp prog ret s P Q (decodeStatePanicPost H_inner b A lim x_outer s0 R) :=
  SepWPp.call_decodeErrorFrom_gen hcall k w st hpc hrun hsp hs0A hlr htr hx0 hw hfits hP hnext
    (fun _ _ h hm => False.elim (h R hm))

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitBudget

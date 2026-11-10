/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserialize
public import LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserialize.DefsBudget
import ProofLib.SepLogic.WPp
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Budget-Threaded Call Helpers for `<Message>::deserialize`

Framed `SepWP` / `SepWPp` call wrappers for `format_inner` (`FormatInnerEnv`) and `__rust_dealloc`
used by `<spqr::v1::chunked::states::Message>::deserialize` under `RustCliAllocBudget`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserializeBudget

open Arm64 ProofLib
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
   rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Heap.SpecBudget
  (FormatInnerEnv formatInnerBudgetEnvSpec formatInnerBudgetSpec)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.RustHeap (vecHeader vecU8 vecU8At)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SpqrV1.Top.MessageDeserialize (stackAt_extHookStack_split_alloc)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)

/-- Envelope-parametric framed call rule for `formatInnerBudgetEnvSpec M A lim Env` inside
    `SepWP`. -/
theorem call_formatInnerEnv {prog : Program} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {Env : List AllocEvent → Prop}
    {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (formatInnerBudgetEnvSpec M A lim Env))
    (ret sp_cur : BitVec 64) (st : M.σ) {s0 s : State} {P F : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_cur)
    (hsp_align : (sp_cur &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : s.trace = s0.trace)
    (hx8 : s.readReg64 .x8 = ret)
    (hfit : FitsEnv M lim st Env)
    (hP : P = (memRegion ret 24 ∗ A.pool lim st s ∗ stackAt sp_cur extHookStack) ∗ F)
    (hnext : ∀ (sf : State) (evs : List AllocEvent) (bs : List (BitVec 8)) (cap ptr : BitVec 64),
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_cur → sf.trace = s0.trace → CalleeSavedPreserved s sf →
      Env evs → bs.length ≤ cap.toNat → cap.toNat < 2 ^ 63 → ptr ≠ 0#64 →
      SepWP prog target_pc sf
        (((ret ↦₆₄ cap) ∗ ((ret + 8#64) ↦₆₄ ptr) ∗ ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (if cap = 0#64 then emp
           else A.repAlloc.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
             memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp_cur extHookStack) ∗ F) post) :
    SepWP prog target_pc s P post := by
  have halign : s.spAligned = true := by dsimp only [State.spAligned]; rw [hsp]; exact hsp_align
  refine SepWP.call_subroutine_frame (x := (ret, st)) (F := F) hcall hpc hrun halign hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    dsimp only [formatInnerBudgetEnvSpec]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx8, hfit⟩, ?_⟩
    rwa [← sepConj_assoc, ← hP]
  · intro R' sm _ hpost
    dsimp only [formatInnerBudgetEnvSpec] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro R' code sm _ hpost
    dsimp only [formatInnerBudgetEnvSpec] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm
    unfold SepWP
    intro R' hpost hL
    rw [sepConj_assoc] at hpost
    dsimp only [formatInnerBudgetEnvSpec] at hpost
    rw [hsp] at hpost hspm
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hpost⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨htrm, hevs⟩, hpost⟩
    rw [htr] at htrm
    dsimp only [vecU8, vecU8At, vecHeader] at hpost
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨bs, cap, ptr, hpost⟩
    have hpost' : sm.mem ⊨
        ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        ((((ret ↦₆₄ cap) ∗ ((ret + 8#64) ↦₆₄ ptr) ∗ ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (if cap = 0#64 then emp
           else A.repAlloc.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
             memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt sp_cur extHookStack) ∗ F) ∗ R') := by
      refine Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
    rw [satisfies_pure_sepConj] at hpost'
    rcases hpost' with ⟨⟨hle, hlt, hptr⟩, hpost'⟩
    have hnext' := hnext sm evs bs cap ptr hpcm hrunm hspm htrm hcsm hevs hle hlt hptr
    unfold SepWP at hnext'
    exact hnext' R' hpost' hL
  · intro R' sm _ hpost
    dsimp only [formatInnerBudgetEnvSpec] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)

/-- Framed call rule for `formatInnerBudgetSpec M A lim` (`FormatInnerEnv` = `evs = []`) inside
    `SepWP`. -/
theorem call_formatInner {prog : Program} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (formatInnerBudgetSpec M A lim))
    (ret sp_cur : BitVec 64) (st : M.σ) {s0 s : State} {P F : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_cur)
    (hsp_align : (sp_cur &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : s.trace = s0.trace)
    (hx8 : s.readReg64 .x8 = ret)
    (hP : P = (memRegion ret 24 ∗ A.pool lim st s ∗ stackAt sp_cur extHookStack) ∗ F)
    (hnext : ∀ (sf : State) (bs : List (BitVec 8)) (cap ptr : BitVec 64),
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_cur → sf.trace = s0.trace → CalleeSavedPreserved s sf →
      bs.length ≤ cap.toNat → cap.toNat < 2 ^ 63 → ptr ≠ 0#64 →
      SepWP prog target_pc sf
        (((ret ↦₆₄ cap) ∗ ((ret + 8#64) ↦₆₄ ptr) ∗ ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (if cap = 0#64 then emp
           else A.repAlloc.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
             memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ∗
          A.pool lim st sf ∗ stackAt sp_cur extHookStack) ∗ F) post) :
    SepWP prog target_pc s P post := by
  have hfit : FitsEnv M lim st FormatInnerEnv := by
    intro evs hevs
    dsimp only [FormatInnerEnv] at hevs
    subst hevs
    trivial
  refine call_formatInnerEnv hcall ret sp_cur st hpc hrun hsp hsp_align hlr htr hx8 hfit hP ?_
  intro sf evs bs cap ptr hpc' hrun' hsp' htr' hcs' hevs hle hlt hptr
  dsimp only [FormatInnerEnv] at hevs
  subst hevs
  simpa only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil] using
    hnext sf bs cap ptr hpc' hrun' hsp' htr' hcs' hle hlt hptr

/-- `SepWPp` convenience wrapper for `call_formatInner` when the caller goal uses `SepWPp`. -/
theorem call_formatInner_then_sepWP {prog : Program} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (formatInnerBudgetSpec M A lim))
    (ret sp_cur : BitVec 64) (st : M.σ) {s0 s : State} {P F : SepProp}
    {post panicPost : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_cur)
    (hsp_align : (sp_cur &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : s.trace = s0.trace)
    (hx8 : s.readReg64 .x8 = ret)
    (hP : P = (memRegion ret 24 ∗ A.pool lim st s ∗ stackAt sp_cur extHookStack) ∗ F)
    (hnext : ∀ (sf : State) (bs : List (BitVec 8)) (cap ptr : BitVec 64),
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_cur → sf.trace = s0.trace → CalleeSavedPreserved s sf →
      bs.length ≤ cap.toNat → cap.toNat < 2 ^ 63 → ptr ≠ 0#64 →
      SepWP prog target_pc sf
        (((ret ↦₆₄ cap) ∗ ((ret + 8#64) ↦₆₄ ptr) ∗ ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (if cap = 0#64 then emp
           else A.repAlloc.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
             memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ∗
          A.pool lim st sf ∗ stackAt sp_cur extHookStack) ∗ F) post) :
    SepWPp prog target_pc s P post panicPost :=
  SepWPp.of_sepWP_ret
    (call_formatInner hcall ret sp_cur st hpc hrun hsp hsp_align hlr htr hx8 hP hnext)

/-- Framed call rule for `rustCliDeallocBudgetSpec M A lim` inside `SepWP` using `extHookStack`. -/
theorem call_dealloc [LibsignalPlacement] {prog : Program} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (rustCliDeallocBudgetSpec M A lim))
    (ptr sp_cur : BitVec 64) (size : Nat) (st : M.σ) {s0 s : State} {P F : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_cur)
    (hsp_align : (sp_cur &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hlr624 : LsRetAddr624 ret_pc)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = ptr)
    (hx1 : (s.readReg64 .x1).toNat = size)
    (hx2 : (s.readReg64 .x2).toNat = 1)
    (hP : P = (A.repAlloc.live ptr size 1 ∗ memRegion ptr size ∗
      A.pool lim st s ∗ stackAt sp_cur extHookStack) ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_cur → sf.trace = s0.trace →
      AllocCallPreserved s sf → CalleeSavedPreserved s sf →
      SepWP prog target_pc sf
        ((A.pool lim (M.stepEvents (rustDeallocEvents size 1) st) sf ∗
          stackAt sp_cur extHookStack) ∗ F) post) :
    SepWP prog target_pc s P post := by
  let F_ext := memRegion (sp_cur - 16384#64) 12288 ∗ F
  have halign : s.spAligned = true := by dsimp only [State.spAligned]; rw [hsp]; exact hsp_align
  refine SepWP.call_subroutine_frame (x := (ptr, size, 1, st)) (F := F_ext)
    hcall hpc hrun halign hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    dsimp only [rustCliDeallocBudgetSpec, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live] at hP ⊢
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, by rw [hlr]; exact hlr624⟩, ?_⟩
    rw [hP, stackAt_extHookStack_split_alloc sp_cur] at hm
    refine Satisfies.mono (Entails.of_eq ?_) hm
    dsimp only [F_ext]; sep_ac_rfl
  · intro R' sm _ hpost
    dsimp only [rustCliDeallocBudgetSpec] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro R' code sm _ hpost
    dsimp only [rustCliDeallocBudgetSpec] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm
    unfold SepWP
    intro R' hpost hL
    rw [sepConj_assoc] at hpost
    dsimp only [rustCliDeallocBudgetSpec] at hpost
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨hacp, _⟩, hpost⟩
    have htrm : sm.trace = s0.trace := hacp.2.1.trans htr
    rw [hsp] at hspm
    have hpost' : sm.mem ⊨
        ((A.pool lim (M.stepEvents (rustDeallocEvents size 1) st) sm ∗
          stackAt sp_cur extHookStack) ∗ F) ∗ R' := by
      rw [stackAt_extHookStack_split_alloc sp_cur]
      refine Satisfies.mono (Entails.of_eq ?_) hpost
      dsimp only [F_ext]; sep_ac_rfl
    have hnext' := hnext sm hpcm hrunm hspm htrm hacp hcsm
    unfold SepWP at hnext'
    exact hnext' R' hpost' hL
  · intro R' sm _ hpost
    dsimp only [rustCliDeallocBudgetSpec] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)

end LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserializeBudget

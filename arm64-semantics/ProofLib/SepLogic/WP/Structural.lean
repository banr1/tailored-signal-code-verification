/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Lean
public import Std.Tactic.BVDecide
public import Arm64
public import ProofLib.SimpAttrs
public import ProofLib.CoreLemmas
public import ProofLib.Lemmas
public import ProofLib.SepLogic.Frame
public import ProofLib.Abi.Aapcs
public import ProofLib.SepLogic
public import ProofLib.SepLogic.Bytes
import ProofLib.Hoare.Model
public import ProofLib.ObjectLoad
public import ProofLib.Hoare.Safety
public import ProofLib.VCGen
public import ProofLib.LitNorm
public import ProofLib.BV.WidthNorm
public import ProofLib.SepLogic.WP.Defs
public import ProofLib.SepLogic.CondClassify
public import ProofLib.BV.Arith
public import ProofLib.SepLogic.WP.StateNorm
public import ProofLib.SepLogic.WP.Access
public import ProofLib.SepLogic.WP.StepsCore
public import ProofLib.SepLogic.CodeLookup
import ProofLib.SepLogic.Model

/-!
# Structural Rules for `SepWP` and `SepWPp`

Control-flow, subroutine call, loop, sequential cut, spatial focus, and unconstrained-byte step
rules for `SepWP` and panic-aware `SepWPp`.
-/

@[expose] public section

namespace ProofLib

open Arm64

/-- Default tactic for discharging `h_oom` on `SepWP.call_*` / `SepWP.tailcall_*` rules:
    unfolds `ToBaseSpec.toSpec` and any `Arm64.Spec`-returning constants in the goal, then
    discharges `⌜False⌝` (unreachable OOM), `⌜True⌝` (`Spec.allowOom`), or frame-dropping OOM
    obligations automatically. -/
elab "wp_close_oom_default" : tactic => do
  let _ ← Lean.Elab.Tactic.tryTactic (Lean.Elab.Tactic.evalTactic (← `(tactic| (
    dsimp only [Program.relocSubroutineOk, Program.alignedSubroutineOk,
      Obj.LinkedImage.subroutineOk, Program.subroutineOk, fn_subroutine_ok,
      ToBaseSpec.toSpec, instToBaseSpecId, instToBaseSpecFn]))))
  for _ in [:3] do
    let mvarId ← Lean.Elab.Tactic.getMainGoal
    let ref ← IO.mkRef #[]
    mvarId.withContext do
      let collectFromExpr (e : Lean.Expr) : Lean.MetaM Unit := do
        e.forEach fun sub => do
          if sub.isConst then
            let nm := sub.constName!
            if nm != ``Arm64.Spec.mk then
              let ty ← Lean.Meta.inferType sub
              if ty.getForallBody.isAppOf ``Arm64.Spec then
                let arr ← ref.get
                if !arr.any (fun i => i.getId == nm) then
                  ref.set (arr.push (Lean.mkIdent nm))
      collectFromExpr (← Lean.instantiateMVars (← mvarId.getType))
    let ids ← ref.get
    if ids.isEmpty then break
    for id in ids do
      let _ ← Lean.Elab.Tactic.tryTactic (Lean.Elab.Tactic.evalTactic (← `(tactic| dsimp only [$id:ident])))
  Lean.Elab.Tactic.evalTactic (← `(tactic| (
    intro _ _ _ ho
    try simp only [wp_unfold, Spec.allowPanicWhen, Spec.allowOomWhen, Spec.allowOom] at ho ⊢
    try dsimp only at ho ⊢
    first
      | exact ho
      | exact False.elim (not_satisfies_false_sepConj ho)
      | exact satisfies_true_sepConj ho
      | exact satisfies_true_sepConj_frame ho
      | exact Satisfies.drop_mid ho)))

/-- Conditional branch splitting rule for `SepWP` when `s.pc = if c then pc1 else pc2`. -/
theorem SepWP.ite {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {c : Prop} {inst : Decidable c} {pc1 pc2 : BitVec 64}
    (hpc : s.pc = @_root_.ite (BitVec 64) c inst pc1 pc2)
    (hthen : c → SepWP prog target_pc (s.setPC pc1) P post oom)
    (helse : ¬ c → SepWP prog target_pc (s.setPC pc2) P post oom) :
    SepWP prog target_pc s P post oom := by
  letI := inst
  by_cases hc : c
  · have hpc1 : s.pc = pc1 := by simp [hpc, hc]
    have hs1 : s.setPC pc1 = s := by cases s; simp [State.setPC] at hpc1 ⊢; exact hpc1.symm
    exact hs1 ▸ hthen hc
  · have hpc2 : s.pc = pc2 := by simp [hpc, hc]
    have hs2 : s.setPC pc2 = s := by cases s; simp [State.setPC] at hpc2 ⊢; exact hpc2.symm
    exact hs2 ▸ helse hc

/-- Deterministic `then`-branch rule for `SepWP` when `c` holds. -/
theorem SepWP.ite_true {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {c : Prop} {inst : Decidable c} {pc1 pc2 : BitVec 64}
    (hpc : s.pc = @_root_.ite (BitVec 64) c inst pc1 pc2)
    (hc : c)
    (hthen : SepWP prog target_pc (s.setPC pc1) P post oom) :
    SepWP prog target_pc s P post oom := by
  letI := inst
  have hpc1 : s.pc = pc1 := by simp [hpc, hc]
  have hs1 : s.setPC pc1 = s := by cases s; simp [State.setPC] at hpc1 ⊢; exact hpc1.symm
  exact hs1 ▸ hthen

/-- Deterministic `else`-branch rule for `SepWP` when `¬ c` holds. -/
theorem SepWP.ite_false {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {c : Prop} {inst : Decidable c} {pc1 pc2 : BitVec 64}
    (hpc : s.pc = @_root_.ite (BitVec 64) c inst pc1 pc2)
    (hnc : ¬ c)
    (helse : SepWP prog target_pc (s.setPC pc2) P post oom) :
    SepWP prog target_pc s P post oom := by
  letI := inst
  have hpc2 : s.pc = pc2 := by simp [hpc, hnc]
  have hs2 : s.setPC pc2 = s := by cases s; simp [State.setPC] at hpc2 ⊢; exact hpc2.symm
  exact hs2 ▸ helse

/-- Compositional `Spec.split` subroutine invocation rule for `SepWP`:
    splits `P = preMem x ∗ Frame` via `SepFrame` and updates the spatial context to
    `P' = postMem x ∗ Frame`. -/
theorem SepWP.call_sep {α : Type} {prog : Program} {entry target_pc : BitVec 64}
    {preRegs : α → State → Prop} {preMem : α → SepProp}
    {postRegs : α → State → State → Prop} {postMem : α → SepProp}
    (hcall : subroutine_ok prog entry (Spec.split preRegs preMem postRegs postMem))
    {x : α} {s : State} {P Frame P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {ret_pc : BitVec 64}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpreR : preRegs x s)
    (hframe : SepFrame (preMem x) P Frame)
    (hp' : postMem x ∗ Frame = P')
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      (postRegs x s sf ∧ sf.sp = s.sp ∧ CalleeSavedPreserved s sf) →
      SepWP prog target_pc sf P' post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hm1 : s.mem ⊨ preMem x ∗ (Frame ∗ R) := by
    rw [← sepConj_assoc, ← hframe.eq]
    exact hm
  have hreach := Spec.split.apply hcall x (Frame ∗ R) hpc hrun hpreR hm1 hsp_align
  rw [hlr] at hreach
  refine reaches_pc_seq hreach ?_
  intro sf hpc_sf hrun_sf ⟨hpostR, hmem_sf, hsp, hcs⟩
  have hm2 : sf.mem ⊨ P' ∗ R := by
    rw [← hp', sepConj_assoc]
    exact hmem_sf
  exact hnext sf hpc_sf hrun_sf ⟨hpostR, hsp, hcs⟩ R hm2

/-- Compositional `subroutine_ok` invocation rule for `SepWP`. -/
theorem SepWP.call_subroutine {α : Type} {prog : Program} {entry target_pc : BitVec 64}
    {spec : Spec α}
    (hcall : subroutine_ok prog entry spec)
    {x : α} {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {ret_pc : BitVec 64}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ R') → (s.mem ⊨ spec.pre x s ∗ R'))
    (h_no_panic : ∀ R' sf, sf.status = .Panicked → ¬(sf.mem ⊨ spec.onPanic x s sf ∗ R'))
    (h_no_exit : ∀ R' code sf, sf.status = .Exited code → ¬(sf.mem ⊨ spec.onExit x code s sf ∗ R'))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      ((sf.mem ⊨ spec.post x s sf) ∧ sf.sp = s.sp ∧ CalleeSavedPreserved s sf) →
      SepWP prog target_pc sf P post oom)
    (h_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (P ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by
      wp_close_oom_default) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hpreR : s.mem ⊨ spec.pre x s ∗ (P ∗ R) := hpre (P ∗ R) hm
  have hreach := subroutine_ok_apply_full hcall x (P ∗ R) hpc hrun hpreR hsp_align
    (h_no_panic (P ∗ R)) (h_no_exit (P ∗ R)) (h_oom R)
  rw [hlr] at hreach
  refine reaches_pc_seq hreach ?_
  intro sf hpc_sf hrun_sf ⟨hpostM, hsp, hcs⟩
  exact hnext sf hpc_sf hrun_sf ⟨Satisfies.of_sep_left hpostM, hsp, hcs⟩ R (Satisfies.of_sep_right hpostM)

/-- Framed compositional `subroutine_ok` invocation rule for `SepWP`, for callees whose
    precondition owns memory: the caller's spatial context `P` is split into the callee's
    precondition `spec.pre x s` and a residual frame `F` kept by the caller (`hpre`); after the
    call, the spatial context is the callee's postcondition `spec.post x s sf ∗ F`. -/
theorem SepWP.call_subroutine_frame {α : Type} {prog : Program} {entry target_pc : BitVec 64}
    {spec : Spec α}
    (hcall : subroutine_ok prog entry spec)
    {x : α} {s : State} {P F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {ret_pc : BitVec 64}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (h_no_panic : ∀ R' sf, sf.status = .Panicked → ¬(sf.mem ⊨ spec.onPanic x s sf ∗ R'))
    (h_no_exit : ∀ R' code sf, sf.status = .Exited code → ¬(sf.mem ⊨ spec.onExit x code s sf ∗ R'))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWP prog target_pc sf (spec.post x s sf ∗ F) post oom)
    (h_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by
      wp_close_oom_default) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hreach := subroutine_ok_apply_full hcall x (F ∗ R) hpc hrun (hpre R hm) hsp_align
    (h_no_panic (F ∗ R)) (h_no_exit (F ∗ R)) (h_oom R)
  rw [hlr] at hreach
  refine reaches_pc_seq hreach ?_
  intro sf hpc_sf hrun_sf ⟨hpostM, hsp, hcs⟩
  rw [← sepConj_assoc] at hpostM
  exact hnext sf hpc_sf hrun_sf hsp hcs R hpostM

/-- Eliminate a pure conjunct `⌜φ⌝` at the head of the `SepWP` spatial context into a hypothesis. -/
theorem SepWP.pure_elim {prog : Program} {target_pc : BitVec 64}
    {s : State} {φ : Prop} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : φ → SepWP prog target_pc s P post oom) :
    SepWP prog target_pc s (⌜φ⌝ ∗ P) post oom := by
  intro R hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact h hm.1 R hm.2

/-- Eliminate a spatial context consisting only of a pure assertion `⌜φ⌝` into a hypothesis. -/
theorem SepWP.pure_elim_only {prog : Program} {target_pc : BitVec 64}
    {s : State} {φ : Prop} {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : φ → SepWP prog target_pc s emp post oom) :
    SepWP prog target_pc s ⌜φ⌝ post oom := by
  intro R hm
  rw [satisfies_pure_sepConj] at hm
  exact h hm.1 R (by rw [emp_sepConj]; exact hm.2)

/-- Eliminate an existential `∃∗ a, Q a` at the head of the `SepWP` spatial context into a fresh
    universally quantified variable. -/
theorem SepWP.exists_elim {α : Sort _} {prog : Program} {target_pc : BitVec 64}
    {s : State} {Q : α → SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ a, SepWP prog target_pc s (Q a) post oom) :
    SepWP prog target_pc s (∃∗ a, Q a) post oom := by
  intro R hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨a, ha⟩ := hm
  exact h a R ha

/-- Well-founded loop rule for `SepWP` at loop header `head_pc` with state invariant `inv`
    and termination measure `meas : State → Nat`.
    Automatically preserves `st.sp = s.sp`, `st.readReg64 .lr = s.readReg64 .lr`, and
    `CalleeSavedPreserved s st` across loop iterations. -/
theorem SepWP.loop {prog : Program} {head_pc target_pc : BitVec 64}
    (inv : State → Prop) (meas : State → Nat)
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = head_pc)
    (hrun : s.status = .Running)
    (hinv : inv s)
    (hbase : ∀ st : State, st.pc = head_pc → st.status = .Running →
      (inv st ∧ st.sp = s.sp ∧ st.readReg64 .lr = s.readReg64 .lr ∧ CalleeSavedPreserved s st) →
      meas st = 0 →
      SepWP prog target_pc st P post oom)
    (hstep : ∀ st : State, st.pc = head_pc → st.status = .Running →
      (inv st ∧ st.sp = s.sp ∧ st.readReg64 .lr = s.readReg64 .lr ∧ CalleeSavedPreserved s st) →
      0 < meas st →
      SepWP prog head_pc st P (fun st' P' =>
        (P' ⊢ P) ∧ inv st' ∧
        st'.sp = s.sp ∧ st'.readReg64 .lr = s.readReg64 .lr ∧ CalleeSavedPreserved s st' ∧
        meas st' < meas st) oom) :
    SepWP prog target_pc s P post oom := by
  suffices hmain : ∀ n : Nat, ∀ st : State, meas st = n →
      st.pc = head_pc → st.status = .Running →
      (inv st ∧ st.sp = s.sp ∧ st.readReg64 .lr = s.readReg64 .lr ∧ CalleeSavedPreserved s st) →
      SepWP prog target_pc st P post oom from
    hmain (meas s) s rfl hpc hrun ⟨hinv, rfl, rfl, CalleeSavedPreserved.rfl s⟩
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro st hmeas hpc_st hrun_st hinv_st
    by_cases hzero : n = 0
    · subst hzero
      exact hbase st hpc_st hrun_st hinv_st hmeas
    · have hpos : 0 < meas st := by omega
      intro R hm
      have hiter := hstep st hpc_st hrun_st hinv_st hpos R hm
      refine reaches_pc_seq hiter ?_
      intro st' hpc_st' hrun_st' ⟨P', hm', hent, hinv_st', hsp', hlr', hcs', hlt⟩
      have hm_P : st'.mem ⊨ P ∗ R :=
        Satisfies.mono (sepConj_mono_left hent) hm'
      have hlt_n : meas st' < n := by omega
      exact ih (meas st') hlt_n st' rfl hpc_st' hrun_st' ⟨hinv_st', hsp', hlr', hcs'⟩ R hm_P

/-- Well-founded loop rule for `SepWP` with a state-indexed spatial invariant `P_inv : State → SepProp`,
    pure state invariant `inv : State → Prop`, and termination measure `meas : State → Nat`. -/
theorem SepWP.loop_sep {prog : Program} {head_pc target_pc : BitVec 64}
    (P_inv : State → SepProp) (inv : State → Prop) (meas : State → Nat)
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = head_pc)
    (hrun : s.status = .Running)
    (hent0 : P ⊢ P_inv s)
    (hinv : inv s)
    (hbase : ∀ st : State, st.pc = head_pc → st.status = .Running →
      (inv st ∧ st.sp = s.sp ∧ st.readReg64 .lr = s.readReg64 .lr ∧ CalleeSavedPreserved s st) →
      meas st = 0 →
      SepWP prog target_pc st (P_inv st) post oom)
    (hstep : ∀ st : State, st.pc = head_pc → st.status = .Running →
      (inv st ∧ st.sp = s.sp ∧ st.readReg64 .lr = s.readReg64 .lr ∧ CalleeSavedPreserved s st) →
      0 < meas st →
      SepWP prog head_pc st (P_inv st) (fun st' P' =>
        (P' ⊢ P_inv st') ∧ inv st' ∧
        st'.sp = s.sp ∧ st'.readReg64 .lr = s.readReg64 .lr ∧ CalleeSavedPreserved s st' ∧
        meas st' < meas st) oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.weaken_pre hent0
  suffices hmain : ∀ n : Nat, ∀ st : State, meas st = n →
      st.pc = head_pc → st.status = .Running →
      (inv st ∧ st.sp = s.sp ∧ st.readReg64 .lr = s.readReg64 .lr ∧ CalleeSavedPreserved s st) →
      SepWP prog target_pc st (P_inv st) post oom from
    hmain (meas s) s rfl hpc hrun ⟨hinv, rfl, rfl, CalleeSavedPreserved.rfl s⟩
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro st hmeas hpc_st hrun_st hinv_st
    by_cases hzero : n = 0
    · subst hzero
      exact hbase st hpc_st hrun_st hinv_st hmeas
    · have hpos : 0 < meas st := by omega
      intro R hm
      have hiter := hstep st hpc_st hrun_st hinv_st hpos R hm
      refine reaches_pc_seq hiter ?_
      intro st' hpc_st' hrun_st' ⟨P', hm', hent, hinv_st', hsp', hlr', hcs', hlt⟩
      have hm_P : st'.mem ⊨ P_inv st' ∗ R :=
        Satisfies.mono (sepConj_mono_left hent) hm'
      have hlt_n : meas st' < n := by omega
      exact ih (meas st') hlt_n st' rfl hpc_st' hrun_st' ⟨hinv_st', hsp', hlr', hcs'⟩ R hm_P

/-! ## Bridge theorems from `SepWP` to `subroutine_ok` -/

/-- Prove a `subroutine_ok prog entry (Spec.split ...)` specification using `SepWP`. -/
theorem Spec.split_of_sepWP {α : Type} {prog : Program} {entry : BitVec 64}
    {preRegs : α → State → Prop} {preMem : α → SepProp}
    {postRegs : α → State → State → Prop} {postMem : α → SepProp}
    (h : ∀ (x : α) (s0 : State),
      s0.pc = entry →
      s0.status = .Running →
      preRegs x s0 →
      s0.spAligned = true →
      SepWP prog (s0.readReg64 Reg.lr) s0 (preMem x)
        (fun sf P_f =>
          (postRegs x s0 sf ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) ∧
          (P_f ⊢ postMem x))) :
    subroutine_ok prog entry (Spec.split preRegs preMem postRegs postMem) := by
  apply Spec.split.intro
  intro x R s0 hpc hrun hregs hmem hsp_align
  refine reaches_pc_mono (h x s0 hpc hrun hregs hsp_align R hmem) ?_
  intro sf _ _ ⟨P_f, hmf, ⟨hpostR, hsp, hcs⟩, hent⟩
  refine ⟨?_, hsp, hcs⟩
  rw [Spec.split, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hpostR, Satisfies.mono (sepConj_mono_left hent) hmf⟩

/-- Prove an `Arm64.subroutine_ok` contract using `SepWP` with initial spatial footprint `P_init`
    and residual frame `Frame_init`. -/
theorem subroutine_ok_of_sepWP {α : Type} {prog : Program} {entry_pc : BitVec 64}
    {spec : Spec α}
    (h : ∀ (x : α) (R : SepProp) (s0 : State),
      s0.pc = entry_pc →
      s0.status = .Running →
      (s0.mem ⊨ spec.pre x s0 ∗ R) →
      s0.spAligned = true →
      ∃ P_init Frame_init : SepProp,
        (s0.mem ⊨ P_init ∗ Frame_init) ∧
        SepWP prog (s0.readReg64 Reg.lr) s0 P_init (fun sf P_f =>
          (sf.mem ⊨ P_f ∗ Frame_init → sf.mem ⊨ spec.post x s0 sf ∗ R) ∧
          sf.sp = s0.sp ∧
          CalleeSavedPreserved s0 sf)) :
    subroutine_ok prog entry_pc spec := by
  apply subroutine_ok_intro
  intro x R s0 hpc hrun hpre hsp_align
  rcases h x R s0 hpc hrun hpre hsp_align with ⟨P_init, Frame_init, hm0, hwp⟩
  refine reaches_pc_mono (hwp Frame_init hm0) ?_
  intro sf _ _ ⟨P_f, hmf, hpost, hsp, hcs⟩
  exact ⟨hpost hmf, hsp, hcs⟩

/-- Prove an `Arm64.subroutine_ok` contract using `SepWP` with initial spatial footprint `P_init`
    and caller frame `R`, propagating `spec.onOom x s0`. -/
theorem subroutine_ok_of_sepWP_init {α : Type} {prog : Program} {entry_pc : BitVec 64}
    {spec : Spec α}
    (h : ∀ (x : α) (R : SepProp) (s0 : State),
      s0.pc = entry_pc →
      s0.status = .Running →
      (s0.mem ⊨ spec.pre x s0 ∗ R) →
      s0.spAligned = true →
      ∃ P_init : SepProp,
        (s0.mem ⊨ P_init ∗ R) ∧
        SepWP prog (s0.readReg64 Reg.lr) s0 P_init (fun sf P_f =>
          (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ spec.post x s0 sf ∗ R) ∧
          sf.sp = s0.sp ∧
          CalleeSavedPreserved s0 sf)
          (fun sf => spec.onOom x s0 sf)) :
    subroutine_ok prog entry_pc spec := by
  apply subroutine_ok_intro
  intro x R s0 hpc hrun hpre hsp_align
  rcases h x R s0 hpc hrun hpre hsp_align with ⟨P_init, hm0, hwp⟩
  refine reaches_pc_mono (hwp R hm0) ?_
  intro sf _ _ ⟨P_f, hmf, hpost, hsp, hcs⟩
  exact ⟨hpost hmf, hsp, hcs⟩

/-! ## Sequential composition, framed calls, focus, and unconstrained-byte step rules -/

/-- Sequential composition through an intermediate PC. -/
theorem SepWP.seq {prog : Program} {mid target : BitVec 64} {s : State} {P : SepProp}
    {post Mid : State → SepProp → Prop} {oom : State → SepProp}
    (h1 : SepWP prog mid s P Mid oom)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running → Mid sm Pm → SepWP prog target sm Pm post oom) :
    SepWP prog target s P post oom := by
  intro R hm
  refine reaches_pc_seq (h1 R hm) ?_
  intro sm hpc hrun ⟨Pm, hmm, hMid⟩
  exact h2 sm Pm hpc hrun hMid R hmm

/-- Sequential composition through `mid_pc` when the first segment's postcondition has
    `Q_regs sm ∧ (Pm ⊢ P_mid)` (entailment into `P_mid`). -/
theorem SepWP.seq_entails_emp {prog : Program} {mid_pc target_pc : BitVec 64}
    {s : State} {P P_mid : SepProp} {Q_regs : State → Prop}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (h1 : SepWP prog mid_pc s P (fun sm Pm => Q_regs sm ∧ (Pm ⊢ P_mid)) oom)
    (h2 : ∀ sm, sm.pc = mid_pc → sm.status = .Running → Q_regs sm →
      SepWP prog target_pc sm P_mid post oom) :
    SepWP prog target_pc s P post oom :=
  SepWP.seq h1 fun sm _ hpc hrun ⟨hQ, hent⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hQ)

/-- Single-goal CPS cut of a `SepWP` goal at an intermediate PC `mid` (analogous to `SepWPp.of_sepWP`):
    run a `SepWP` segment to `mid`, transition via `apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)`,
    and continue proving `SepWP prog target sm Pm post oom` from the reached state `sm` and spatial
    context `Pm`. -/
theorem SepWP.cut {prog : Program} {mid target : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWP prog mid s P (fun sm Pm => SepWP prog target sm Pm post oom) oom) :
    SepWP prog target s P post oom :=
  SepWP.seq h (fun _ _ _ _ hcont => hcont)

/-- Sequential cut of a `SepWP` goal at function-relative byte offset `off` from `entry`
    (`mid := entry + off`), for use with `reloc_call_off%`, `code_call_off%`, or `words_ret_off%`. -/
theorem SepWP.cut_at_off {prog : Program} (entry off : BitVec 64) {target : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWP prog (entry + off) s P (fun sm Pm => SepWP prog target sm Pm post oom) oom) :
    SepWP prog target s P post oom :=
  SepWP.cut h

/-- Run a `SepWP` segment to `mid`, then continue with `SepWPp` from the reached state. -/
theorem SepWPp.of_sepWP {prog : Program} {ret mid : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWP prog mid s P (fun sm Pm => SepWPp prog ret sm Pm Q Qp oom) oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | hoom⟩
  · obtain ⟨sf, hsteps', hout⟩ := hnext R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

/-- `SepWPp.of_sepWP` that also passes `sm.pc = mid` and `sm.status = .Running` to the `SepWPp`
    continuation, for continuations that step from `mid` (e.g. `SepWPp.panic` at a panicking
    extern). -/
theorem SepWPp.of_sepWP_at {prog : Program} {ret mid : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWP prog mid s P (fun sm Pm => sm.pc = mid → sm.status = .Running →
      SepWPp prog ret sm Pm Q Qp oom) oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨hpc, hrun, Pm, hmm, hnext⟩ | hoom⟩
  · obtain ⟨sf, hsteps', hout⟩ := hnext hpc hrun R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

/-- Sequence a read-only `SepWP` sub-proof `hwp` on a focused sub-heap `P_sub` (`P = P_sub ∗ F`)
    up to `mid_pc` before continuing with the full spatial assertion `P` to `target_pc`. -/
theorem SepWP.bind_seq_readOnly {prog : Program} {mid_pc target_pc : BitVec 64}
    {s : State} {P P_sub F : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    {oom : State → SepProp}
    (hwp : SepWP prog mid_pc s P_sub (fun sf P_f => P_f = P_sub ∧ Q sf) oom)
    (hsplit : P = P_sub ∗ F := by sep_focus)
    (hnext : ∀ sf, sf.pc = mid_pc → sf.status = .Running → Q sf →
      SepWP prog target_pc sf P post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  rw [hsplit, sepConj_assoc] at hm
  have hreach := hwp (F ∗ R) hm
  refine reaches_pc_seq hreach ?_ (fun _ _ ho => Satisfies.drop_mid ho)
  rintro sf hpc hrun ⟨P_f, hmf, rfl, hQ⟩
  rw [← sepConj_assoc, ← hsplit] at hmf
  exact hnext sf hpc hrun hQ R hmf

/-- Extract `∃ R, s.mem ⊨ P ∗ R` from the `SepWP` precondition `P` to derive pure non-aliasing
    or address-bound facts before continuing symbolic execution. -/
theorem SepWP.with_sat {prog : Program} {target_pc : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : (∃ R, s.mem ⊨ P ∗ R) → SepWP prog target_pc s P post oom) :
    SepWP prog target_pc s P post oom :=
  fun R hm => h ⟨R, hm⟩ R hm

/-- Calling a subroutine whose pre/post are `⌜φ⌝ ∗ A` / `A`, where `P = A ∗ F`. -/
theorem SepWP.call_framed {α : Type} {prog : Program} {entry target_pc ret_pc : BitVec 64}
    {spec : Spec α} (hcall : subroutine_ok prog entry spec) (x : α)
    {s : State} {P A F : SepProp} {φ : Prop} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hno : spec.onPanic x s = (fun _ => ⌜False⌝))
    (hpre_eq : spec.pre x s = (⌜φ⌝ ∗ A)) (hpost_eq : ∀ sf, spec.post x s sf = A)
    (hP : P = A ∗ F) (hφ : φ)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → SepWP prog target_pc sf P post oom)
    (h_no_exit : spec.onExit x = (fun _ _ _ => ⌜False⌝) := by rfl)
    (h_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by
      wp_close_oom_default) :
    SepWP prog target_pc s P post oom := by
  refine SepWP.call_subroutine_frame hcall (x := x) (F := F) hpc hrun hsp_align hlr ?_ ?_ ?_ ?_ h_oom
  · intro R hm
    rw [hpre_eq, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  · intro R' sf _ hp
    rw [hno] at hp
    exact not_satisfies_false_sepConj hp
  · intro R' code sf _ he
    rw [h_no_exit] at he
    exact not_satisfies_false_sepConj he
  · intro sf h1 h2 h3 h4
    rw [hpost_eq, ← hP]
    exact hnext sf h1 h2 h3 h4

/-- Framing helper for a subroutine call whose pre/post are `⌜φ⌝ ∗ A` / `⌜ψ sf⌝ ∗ A`, where `P = A ∗ F`. -/
theorem SepWP.call_framed_pure {α : Type} {prog : Program} {entry target_pc ret_pc : BitVec 64}
    {spec : Spec α} (hcall : subroutine_ok prog entry spec) (x : α)
    {s : State} {P A F : SepProp} {φ : Prop} {ψ : State → Prop} {post : State → SepProp → Prop}
    {oom : State → SepProp}
    (hpre_eq : spec.pre x s = (⌜φ⌝ ∗ A)) (hpost_eq : ∀ sf, spec.post x s sf = (⌜ψ sf⌝ ∗ A))
    (hP : P = A ∗ F) (hφ : φ)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → ψ sf → SepWP prog target_pc sf P post oom)
    (hno : spec.onPanic x s = (fun _ => ⌜False⌝) := by rfl)
    (h_no_exit : spec.onExit x = (fun _ _ _ => ⌜False⌝) := by rfl)
    (h_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by
      wp_close_oom_default) :
    SepWP prog target_pc s P post oom := by
  refine SepWP.call_subroutine_frame hcall (x := x) (F := F) hpc hrun hsp_align hlr ?_ ?_ ?_ ?_ h_oom
  · intro R hm
    rw [hpre_eq, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  · intro R' sf _ hp
    rw [hno] at hp
    exact not_satisfies_false_sepConj hp
  · intro R' code sf _ he
    rw [h_no_exit] at he
    exact not_satisfies_false_sepConj he
  · intro sf h1 h2 h3 h4
    rw [hpost_eq, sepConj_assoc, ← hP]
    exact SepWP.pure_elim (hnext sf h1 h2 h3 h4)

abbrev call_framed_pure := @SepWP.call_framed_pure

/-- Framing helper for a subroutine call whose postcondition has no pure part (`spec.post x s sf = A`). -/
theorem SepWP.call_framed_spatial {α : Type} {prog : Program} {entry target_pc ret_pc : BitVec 64}
    {spec : Spec α} (hcall : subroutine_ok prog entry spec) (x : α)
    {s : State} {P A F : SepProp} {φ : Prop} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpre_eq : spec.pre x s = (⌜φ⌝ ∗ A)) (hpost_eq : ∀ sf, spec.post x s sf = A)
    (hP : P = A ∗ F) (hφ : φ)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → SepWP prog target_pc sf P post oom)
    (hno : spec.onPanic x s = (fun _ => ⌜False⌝) := by rfl)
    (h_no_exit : spec.onExit x = (fun _ _ _ => ⌜False⌝) := by rfl)
    (h_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by
      wp_close_oom_default) :
    SepWP prog target_pc s P post oom := by
  refine SepWP.call_subroutine_frame hcall (x := x) (F := F) hpc hrun hsp_align hlr ?_ ?_ ?_ ?_ h_oom
  · intro R hm
    rw [hpre_eq, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  · intro R' sf _ hp
    rw [hno] at hp
    exact not_satisfies_false_sepConj hp
  · intro R' code sf _ he
    rw [h_no_exit] at he
    exact not_satisfies_false_sepConj he
  · intro sf h1 h2 h3 h4
    rw [hpost_eq, ← hP]
    exact hnext sf h1 h2 h3 h4

abbrev call_framed_spatial := @SepWP.call_framed_spatial

/-- Framing helper for a subroutine call whose pre/post are `⌜φ⌝ ∗ A` / `A' sf`, where `P = A ∗ F`. -/
theorem SepWP.call_framed_spatial_mut {α : Type} {prog : Program} {entry target_pc ret_pc : BitVec 64}
    {spec : Spec α} (hcall : subroutine_ok prog entry spec) (x : α)
    {s : State} {P A F : SepProp} {A' : State → SepProp} {φ : Prop}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpre_eq : spec.pre x s = (⌜φ⌝ ∗ A)) (hpost_eq : ∀ sf, spec.post x s sf = A' sf)
    (hP : P = A ∗ F) (hφ : φ)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → SepWP prog target_pc sf (A' sf ∗ F) post oom)
    (hno : spec.onPanic x s = (fun _ => ⌜False⌝) := by rfl)
    (h_no_exit : spec.onExit x = (fun _ _ _ => ⌜False⌝) := by rfl)
    (h_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by
      wp_close_oom_default) :
    SepWP prog target_pc s P post oom := by
  refine SepWP.call_subroutine_frame hcall (x := x) (F := F) hpc hrun hsp_align hlr ?_ ?_ ?_ ?_ h_oom
  · intro R hm
    rw [hpre_eq, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  · intro R' sf _ hp
    rw [hno] at hp
    exact not_satisfies_false_sepConj hp
  · intro R' code sf _ he
    rw [h_no_exit] at he
    exact not_satisfies_false_sepConj he
  · intro sf h1 h2 h3 h4
    rw [hpost_eq]
    exact hnext sf h1 h2 h3 h4

abbrev call_framed_spatial_mut := @SepWP.call_framed_spatial_mut

/-- Framing helper for a subroutine call whose pre/post are `⌜φ⌝ ∗ A` / `⌜ψ sf⌝ ∗ A'`, where `P = A ∗ F`. -/
theorem SepWP.call_framed_mut {α : Type} {prog : Program} {entry target_pc ret_pc : BitVec 64}
    {spec : Spec α} (hcall : subroutine_ok prog entry spec) (x : α)
    {s : State} {P A A' F : SepProp} {φ : Prop} {ψ : State → Prop} {post : State → SepProp → Prop}
    {oom : State → SepProp}
    (hpre_eq : spec.pre x s = (⌜φ⌝ ∗ A)) (hpost_eq : ∀ sf, spec.post x s sf = (⌜ψ sf⌝ ∗ A'))
    (hP : P = A ∗ F) (hφ : φ)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → ψ sf → SepWP prog target_pc sf (A' ∗ F) post oom)
    (hno : spec.onPanic x s = (fun _ => ⌜False⌝) := by rfl)
    (h_no_exit : spec.onExit x = (fun _ _ _ => ⌜False⌝) := by rfl)
    (h_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by
      wp_close_oom_default) :
    SepWP prog target_pc s P post oom := by
  refine SepWP.call_subroutine_frame hcall (x := x) (F := F) hpc hrun hsp_align hlr ?_ ?_ ?_ ?_ h_oom
  · intro R hm
    rw [hpre_eq, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  · intro R' sf _ hp
    rw [hno] at hp
    exact not_satisfies_false_sepConj hp
  · intro R' code sf _ he
    rw [h_no_exit] at he
    exact not_satisfies_false_sepConj he
  · intro sf h1 h2 h3 h4
    rw [hpost_eq, sepConj_assoc]
    exact SepWP.pure_elim (hnext sf h1 h2 h3 h4)

abbrev call_framed_mut := @SepWP.call_framed_mut

/-- Repack a focused sub-assertion `S` into `T` inside `P = S ∗ Rest` under `SepWP`. -/
theorem SepWP.repack_pre {prog : Program} {target_pc : BitVec 64}
    {s : State} {P S T Rest : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hST : S ⊢ T) (hP : P = S ∗ Rest)
    (h : SepWP prog target_pc s (T ∗ Rest) post oom) :
    SepWP prog target_pc s P post oom := by
  rw [hP]
  exact SepWP.weaken_pre (sepConj_mono_left hST) h

/-- Replace a focused sub-assertion `P` with `Q` (`P ⊢ Q`) inside `G = P ∗ F` under `SepWP`. -/
theorem SepWP.replace_pre {prog : Program} {target_pc : BitVec 64}
    {s : State} {P Q F G : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hG : G = P ∗ F) (hPQ : P ⊢ Q)
    (h : SepWP prog target_pc s (Q ∗ F) post oom) :
    SepWP prog target_pc s G post oom := by
  subst hG
  exact SepWP.weaken_pre (sepConj_mono_left hPQ) h

/-- Focused spatial equality rewrite under `SepWP` (`sep_focus` discharges `Full = T ∗ F`). -/
theorem SepWP.focus_rw {prog : Program} {ret : BitVec 64} {s : State}
    {Full T Q F : SepProp} {Rest : State → SepProp → Prop} {oom : State → SepProp}
    (hEq : T = Q) (hf : Full = T ∗ F := by sep_focus)
    (h : SepWP prog ret s (Q ∗ F) Rest oom) :
    SepWP prog ret s Full Rest oom := by
  rw [hf, hEq]
  exact h


/-- Focused spatial entailment weakening under `SepWP` (`sep_focus` discharges `Full = T ∗ F`). -/
theorem SepWP.focus_weaken {prog : Program} {ret : BitVec 64} {s : State}
    {Full T Q F : SepProp} {Rest : State → SepProp → Prop} {oom : State → SepProp}
    (hEnt : T ⊢ Q) (hf : Full = T ∗ F := by sep_focus)
    (h : SepWP prog ret s (Q ∗ F) Rest oom) :
    SepWP prog ret s Full Rest oom := by
  rw [hf]
  exact SepWP.weaken_pre (sepConj_mono_left hEnt) h


/-- Focus a pure assertion `⌜φ⌝` inside `Full = ⌜φ⌝ ∗ F` and introduce `φ` into the context. -/
theorem SepWP.focus_pure {prog : Program} {ret : BitVec 64} {s : State}
    {Full F : SepProp} {φ : Prop} {Rest : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = ⌜φ⌝ ∗ F := by sep_focus)
    (h : φ → SepWP prog ret s F Rest oom) :
    SepWP prog ret s Full Rest oom := by
  rw [hf]
  exact SepWP.pure_elim h


/-- Focus the first `⌜φ⌝` atom in the `SepWP` precondition and leave `φ → SepWP ...` as the goal. -/
macro "wp_focus_pure" : tactic =>
  `(tactic| refine SepWP.focus_pure (by sep_focus) ?_)

/-- Pull `∃∗` quantifiers to the top of the `SepWP` precondition and introduce them. -/
macro "wp_pull_exists" : tactic =>
  `(tactic| (
    try simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      emp_sepConj, sepConj_emp]
    repeat (apply SepWP.exists_elim; intro _)))

/-- Rewrite the `SepWP` spatial precondition along an equality `P1 = P2`. -/
theorem SepWP.congr_pre {prog : Program} {target_pc : BitVec 64} {s : State}
    {P1 P2 : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (heq : P1 = P2) (h : SepWP prog target_pc s P1 post oom) :
    SepWP prog target_pc s P2 post oom :=
  heq ▸ h

/-- Alias for `SepWP.exists_elim`. -/
theorem SepWP.exists_left {α : Sort _} {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : α → SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ x, SepWP prog target_pc s (P x) post oom) :
    SepWP prog target_pc s (∃∗ x, P x) post oom :=
  SepWP.exists_elim h


/-- Introduce a read-only 64-bit word `(a ↦₆₄ᵣ v)` into the `SepWP` spatial context `P`
    from `s.mem.RO a 8` and `s.mem.read64 a = v`. -/
theorem SepWP.rodata64_intro {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {a v : BitVec 64} (hro : s.mem.RO a 8) (hread : s.mem.read64 a = v)
    (h : SepWP prog target_pc s ((a ↦₆₄ᵣ v) ∗ P) post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  apply h R
  rw [sepConj_assoc]
  exact Satisfies.rodata64_intro hro hread hm

/-- Introduce a read-only byte `(a ↦₈ᵣ v)` into the `SepWP` spatial context `P`
    from `s.mem.RO a 1` and `s.mem.read8 a = v`. -/
theorem SepWP.rodata8_intro {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {a : BitVec 64} {v : BitVec 8} (hro : s.mem.RO a 1) (hread : s.mem.read8 a = v)
    (h : SepWP prog target_pc s ((a ↦₈ᵣ v) ∗ P) post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  apply h R
  rw [sepConj_assoc]
  exact Satisfies.rodata8_intro hro hread hm

/-- 32-bit `LDR Wt` from any readable address (value unconstrained). -/
theorem SepWP.step_ldr32_any {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldr .W32 .W32 false rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hcan : ∀ R, (s.mem ⊨ P ∗ R) → s.mem.canRead ea 4 = true)
    (hnext : ∀ v : BitVec 64, SepWP prog target_pc
      (((applyWriteback s wb).writeReg .W32 rt v).setPC (pc + 4#64)) P post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.ldr .W32 .W32 false rt addr) := hpc.symm ▸ hfetch
  have hcan' := hcan R hm
  apply reaches_pc_step hrun hfetch'
  obtain ⟨v, hstep⟩ : ∃ v, prog.evalInst (.ldr .W32 .W32 false rt addr) s =
      ((applyWriteback s wb).writeReg .W32 rt v).setPC (pc + 4#64) := by
    refine ⟨s.mem.readSized ((RegWidth.W32 : MemWidth)) false ea, ?_⟩
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execLdr, State.writeReg,
      applyWriteback, State.advancePC, State.setPC, hsp, haddr, hcan', MemWidth.bytes, hpc]
  rw [hstep]
  apply hnext v R
  have hmem : (((applyWriteback s wb).writeReg .W32 rt v).setPC
      (pc + 4#64)).mem = s.mem := by cases wb <;> rfl
  rwa [hmem]

/-- `LDRB` from any readable address (value unconstrained). -/
theorem SepWP.step_ldrb_any {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldr .W32 .B8 false rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hcan : ∀ R, (s.mem ⊨ P ∗ R) → s.mem.canRead ea 1 = true)
    (hnext : ∀ v : BitVec 8, SepWP prog target_pc
      (((applyWriteback s wb).writeReg .W32 rt (v.zeroExtend 64)).setPC (pc + 4#64)) P post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.ldr .W32 .B8 false rt addr) := hpc.symm ▸ hfetch
  have hcan' := hcan R hm
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.ldr .W32 .B8 false rt addr) s =
      ((applyWriteback s wb).writeReg .W32 rt ((s.mem.read8 ea).zeroExtend 64)).setPC
        (pc + 4#64) := by
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execLdr, Memory.readSized, State.writeReg,
      applyWriteback, State.advancePC, State.setPC, hsp, haddr, hcan', MemWidth.bytes, hpc]
  rw [hstep]
  apply hnext _ R
  have hmem : (((applyWriteback s wb).writeReg .W32 rt ((s.mem.read8 ea).zeroExtend 64)).setPC
      (pc + 4#64)).mem = s.mem := by cases wb <;> rfl
  rwa [hmem]

/-- `LDURB` from any readable address (value unconstrained). -/
theorem SepWP.step_ldurb_any {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea : BitVec 64}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldr .W32 .B8 false rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, none))
    (hcan : ∀ R, (s.mem ⊨ P ∗ R) → s.mem.canRead ea 1 = true)
    (hnext : ∀ v : BitVec 8, SepWP prog target_pc
      ((s.writeReg .W32 rt (v.zeroExtend 64)).setPC (pc + 4#64)) P post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.ldr .W32 .B8 false rt addr) := hpc.symm ▸ hfetch
  have hcan' := hcan R hm
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.ldr .W32 .B8 false rt addr) s =
      (s.writeReg .W32 rt ((s.mem.read8 ea).zeroExtend 64)).setPC (pc + 4#64) := by
    simp [Program.evalInst, execInstWithSvc, execLdr, Memory.readSized, State.writeReg,
      State.advancePC, State.setPC, hsp, haddr, hcan', MemWidth.bytes, hpc]
  rw [hstep]
  apply hnext _ R
  exact hm

/-- `STRB` to any writable address preserving `P`. -/
theorem SepWP.step_strb_any {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.str .B8 rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hcan : ∀ R, (s.mem ⊨ P ∗ R) → s.mem.canWrite ea 1 = true)
    (hpres : ∀ R v, (s.mem ⊨ P ∗ R) → (s.mem.write8 ea v ⊨ P ∗ R))
    (hnext : SepWP prog target_pc
      ((applyWriteback (s.setMem (s.mem.write8 ea ((s.readReg64 rt).truncate 8))) wb).setPC
        (pc + 4#64)) P post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.str .B8 rt addr) := hpc.symm ▸ hfetch
  have hcan' := hcan R hm
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.str .B8 rt addr) s =
      (applyWriteback (s.setMem (s.mem.write8 ea ((s.readReg64 rt).truncate 8))) wb).setPC
        (pc + 4#64) := by
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized,
      applyWriteback, State.advancePC, State.setPC, hsp, haddr, hcan', MemWidth.bytes, hpc]
  rw [hstep]
  apply hnext R
  have hmem : ((applyWriteback (s.setMem (s.mem.write8 ea ((s.readReg64 rt).truncate 8))) wb).setPC
      (pc + 4#64)).mem = s.mem.write8 ea ((s.readReg64 rt).truncate 8) := by
    cases wb <;> rfl
  rw [hmem]
  exact hpres R _ hm

/-- `STURB` to any writable address preserving `P`. -/
theorem SepWP.step_sturb_any {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea : BitVec 64}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.str .B8 rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, none))
    (hcan : ∀ R, (s.mem ⊨ P ∗ R) → s.mem.canWrite ea 1 = true)
    (hpres : ∀ R v, (s.mem ⊨ P ∗ R) → (s.mem.write8 ea v ⊨ P ∗ R))
    (hnext : SepWP prog target_pc
      ((s.setMem (s.mem.write8 ea ((s.readReg64 rt).truncate 8))).setPC (pc + 4#64)) P post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.str .B8 rt addr) := hpc.symm ▸ hfetch
  have hcan' := hcan R hm
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.str .B8 rt addr) s =
      (s.setMem (s.mem.write8 ea ((s.readReg64 rt).truncate 8))).setPC (pc + 4#64) := by
    simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized,
      State.advancePC, State.setPC, hsp, haddr, hcan', MemWidth.bytes, hpc]
  rw [hstep]
  exact hnext R (hpres R _ hm)

/-- `LDRSB` from any readable address (value unconstrained). -/
theorem SepWP.step_ldrsb_any {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {w : RegWidth} {rt : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldr w .B8 true rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hcan : ∀ R, (s.mem ⊨ P ∗ R) → s.mem.canRead ea 1 = true)
    (hnext : ∀ v : BitVec 8, SepWP prog target_pc
      (((applyWriteback s wb).writeReg w rt (v.signExtend 64)).setPC (pc + 4#64)) P post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.ldr w .B8 true rt addr) := hpc.symm ▸ hfetch
  have hcan' := hcan R hm
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.ldr w .B8 true rt addr) s =
      ((applyWriteback s wb).writeReg w rt ((s.mem.read8 ea).signExtend 64)).setPC
        (pc + 4#64) := by
    cases w <;> cases wb <;> simp [Program.evalInst, execInstWithSvc, execLdr, Memory.readSized, State.writeReg,
      applyWriteback, State.advancePC, State.setPC, hsp, haddr, hcan', MemWidth.bytes, hpc]
  rw [hstep]
  apply hnext _ R
  have hmem : (((applyWriteback s wb).writeReg w rt ((s.mem.read8 ea).signExtend 64)).setPC
      (pc + 4#64)).mem = s.mem := by cases w <;> cases wb <;> rfl
  rwa [hmem]

/-- Recombine two (possibly separated) 32-bit stack cells `(sp - off_lo) ↦₃₂ lo` and
    `(sp - off_hi) ↦₃₂ hi` in `P` into a single 64-bit cell `(sp - off_lo) ↦₆₄ (hi ++ lo) ∗ F`.
    Usage: `apply (SepWP.combine_pointsTo32_sub s0.sp 168#64 164#64)`. -/
theorem SepWP.combine_pointsTo32_sub (sp off_lo off_hi : BitVec 64)
    {prog : Program} {target_pc : BitVec 64} {s : Arm64.State} {P F : SepProp}
    {post : Arm64.State → SepProp → Prop} {oom : Arm64.State → SepProp} {lo hi : BitVec 32}
    (hoff : off_lo - 4#64 = off_hi := by rfl)
    (hf : P = (((sp - off_lo) ↦₃₂ lo) ∗ ((sp - off_hi) ↦₃₂ hi)) ∗ F := by sep_focus)
    (h : SepWP prog target_pc s (((sp - off_lo) ↦₆₄ (hi ++ lo)) ∗ F) post oom) :
    SepWP prog target_pc s P post oom := by
  rw [hf, sepConj_assoc, pointsTo32_combine64_sub sp off_lo off_hi lo hi F hoff]
  exact h

/-- Split a 64-bit stack cell `(sp - off_lo) ↦₆₄ v` anywhere in `P` into two 32-bit cells
    `(sp - off_lo) ↦₃₂ v.truncate 32 ∗ (sp - off_hi) ↦₃₂ v.extractLsb' 32 32 ∗ F`.
    Usage: `apply (SepWP.split_pointsTo64_sub s0.sp 168#64 164#64)`. -/
theorem SepWP.split_pointsTo64_sub (sp off_lo off_hi : BitVec 64)
    {prog : Program} {target_pc : BitVec 64} {s : Arm64.State} {P F : SepProp}
    {post : Arm64.State → SepProp → Prop} {oom : Arm64.State → SepProp} {v : BitVec 64}
    (hoff : off_lo - 4#64 = off_hi := by rfl)
    (hf : P = ((sp - off_lo) ↦₆₄ v) ∗ F := by sep_focus)
    (h : SepWP prog target_pc s (((sp - off_lo) ↦₃₂ v.truncate 32) ∗
      ((sp - off_hi) ↦₃₂ v.extractLsb' 32 32) ∗ F) post oom) :
    SepWP prog target_pc s P post oom := by
  rw [hf, pointsTo64_split32_sub sp off_lo off_hi v F hoff]
  exact h

/-- Pull an existential quantifier out of the left operand of a separating conjunction in a `SepWP` precondition. -/
theorem SepWP.of_sepExists_left {α : Sort _} {prog : Program} {target_pc : BitVec 64}
    {s : Arm64.State} {P : α → SepProp} {F : SepProp} {post : Arm64.State → SepProp → Prop}
    {oom : Arm64.State → SepProp}
    (h : ∀ v, SepWP prog target_pc s (P v ∗ F) post oom) :
    SepWP prog target_pc s ((∃∗ v, P v) ∗ F) post oom := by
  rw [sepExists_sepConj_left]
  exact SepWP.exists_elim h

/-- Introduce `SepWP` directly from its frame-quantified `reaches_pc` characterization without
    unsealing `SepWP`. -/
theorem SepWP.of_reaches_pc {prog : Program} {target_pc : BitVec 64} {s : Arm64.State}
    {P : SepProp} {post : Arm64.State → SepProp → Prop} {oom : Arm64.State → SepProp}
    (h : ∀ R : SepProp, s.mem ⊨ P ∗ R →
      reaches_pc prog target_pc s (fun sf => ∃ P_f, sf.mem ⊨ P_f ∗ R ∧ post sf P_f)
        (fun sf => sf.mem ⊨ oom sf ∗ R)) :
    SepWP prog target_pc s P post oom :=
  h

/-- Eliminate `SepWP` at a frame `R` with `s.mem ⊨ P ∗ R` into a `reaches_pc` execution guarantee. -/
theorem SepWP.to_reaches_pc {prog : Program} {target_pc : BitVec 64} {s : Arm64.State}
    {P R : SepProp} {post : Arm64.State → SepProp → Prop} {oom : Arm64.State → SepProp}
    (hwp : SepWP prog target_pc s P post oom) (hm : s.mem ⊨ P ∗ R) :
    reaches_pc prog target_pc s (fun sf => ∃ P_f, sf.mem ⊨ P_f ∗ R ∧ post sf P_f)
      (fun sf => sf.mem ⊨ oom sf ∗ R) :=
  hwp R hm

/-- Extract a fact from `s.mem ⊨ P ∗ R` before proving `SepWP` without unsealing `SepWP`. -/
theorem SepWP.with_pre {prog : Program} {target_pc : BitVec 64} {s : Arm64.State}
    {P : SepProp} {post : Arm64.State → SepProp → Prop} {oom : Arm64.State → SepProp}
    (h : ∀ R : SepProp, s.mem ⊨ P ∗ R → SepWP prog target_pc s P post oom) :
    SepWP prog target_pc s P post oom :=
  fun R hm => h R hm R hm

/-- Apply a frame-preserving update `P ⊢ |==> Q` to the precondition of `SepWP` (e.g. a ghost
    allocation or a freeze to read-only) before continuing from `Q`. -/
theorem SepWP.bupd_pre {prog : Program} {target_pc : BitVec 64} {s : Arm64.State}
    {P Q : SepProp} {post : Arm64.State → SepProp → Prop} {oom : Arm64.State → SepProp}
    (hb : P ⊢ |==> Q) (hwp : SepWP prog target_pc s Q post oom) :
    SepWP prog target_pc s P post oom :=
  SepWP.of_reaches_pc fun R hm => SepWP.to_reaches_pc hwp
    ((satisfies_bupd (Q ∗ R) s.mem).mp
      (Satisfies.mono (Entails.trans (sepConj_mono_left hb) (bupd_frame_r Q R)) hm))

/-! ## Panic-aware (`SepWPp`) and frozen-image (`FrozenLoaded` / `Spec.inImage`) rules -/

/-- Run a `SepWP` segment to `mid`, re-establishing `img.FrozenLoaded sm` and
    `sm.symtab = img.symtab` at `mid` before continuing with `SepWP` to `target_pc`. -/
theorem SepWP.of_sepWP_frozen {prog : Program} {mid target_pc : BitVec 64} {s : State}
    {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {img : Obj.Image} (hfz : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (h : SepWP prog mid s P (fun sm Pm =>
      img.FrozenLoaded sm → sm.symtab = img.symtab →
      SepWP prog target_pc sm Pm post oom) oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm hL
  rcases (h R hm) hL with ⟨sm, hsteps, ⟨_, _, Pm, hmm, hcont⟩ | hoom⟩
  · have hfz_m := hfz.of_keepsFrozen hsteps.keepsFrozen
    have hsym_m := hsteps.symtab_eq.trans hsym
    obtain ⟨sf, hsteps', hout'⟩ := hcont hfz_m hsym_m R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr hoom⟩

abbrev SepWP.of_sepWP_inv := @SepWP.of_sepWP_frozen

/-- Strengthen a state-indexed spatial postcondition entailment `Pm ⊢ Q₁ sm` to `Pm ⊢ Q₂ sm`
    in `SepWP`, preserving out-of-memory (`oom`) outcomes. -/
theorem SepWP.strengthen_entails {prog : Program} {target_pc : BitVec 64} {s : State}
    {P : SepProp} {Q₁ Q₂ : State → SepProp} {φ : State → Prop} {oom : State → SepProp}
    (himp : ∀ sm, Q₁ sm ⊢ Q₂ sm)
    (h : SepWP prog target_pc s P (fun sm Pm => (Pm ⊢ Q₁ sm) ∧ φ sm) oom) :
    SepWP prog target_pc s P (fun sm Pm => (Pm ⊢ Q₂ sm) ∧ φ sm) oom :=
  SepWP.mono h fun sm _ _ _ ⟨h1, h2⟩ => ⟨Entails.trans h1 (himp sm), h2⟩

/-- Constant-spatial specialization of `SepWP.strengthen_entails`. -/
theorem SepWP.strengthen_entails_const {prog : Program} {target_pc : BitVec 64} {s : State}
    {P P₁ P₂ : SepProp} {φ : State → Prop} {oom : State → SepProp}
    (himp : P₁ ⊢ P₂)
    (h : SepWP prog target_pc s P (fun sm Pm => (Pm ⊢ P₁) ∧ φ sm) oom) :
    SepWP prog target_pc s P (fun sm Pm => (Pm ⊢ P₂) ∧ φ sm) oom :=
  SepWP.strengthen_entails (fun _ => himp) h

/-- Framed `subroutine_ok` invocation rule for `SepWP` that also preserves `img.FrozenLoaded`
    and `symtab = img.symtab` across the call. -/
theorem SepWP.call_subroutine_frame_frozen {α : Type} {prog : Program} {entry target_pc : BitVec 64}
    {spec : Spec α}
    (hcall : subroutine_ok prog entry spec)
    {x : α} {s : State} {P F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {ret_pc : BitVec 64} {img : Obj.Image}
    (hfz : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (h_no_panic : ∀ R' sf, sf.status = .Panicked → ¬(sf.mem ⊨ spec.onPanic x s sf ∗ R'))
    (h_no_exit : ∀ R' code sf, sf.status = .Exited code → ¬(sf.mem ⊨ spec.onExit x code s sf ∗ R'))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWP prog target_pc sf (spec.post x s sf ∗ F) post oom)
    (h_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by
      wp_close_oom_default) :
    SepWP prog target_pc s P post oom := by
  intro R hm hL
  obtain ⟨sm, hsteps, hout⟩ :=
    reaches_outcome_iff.1 (subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun (hpre R hm) hsp_align) hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpostM⟩ | ⟨hpan, hpostM⟩ | ⟨code, hex, hpostM⟩ | ⟨hoom_st, hpostM⟩
  · rw [← sepConj_assoc] at hpostM
    rw [hlr] at hpcm
    have hfz_m := hfz.of_keepsFrozen hsteps.keepsFrozen
    have hsym_m := hsteps.symtab_eq.trans hsym
    obtain ⟨sf, hsteps', hout'⟩ :=
      (hnext sm hpcm hrunm hspm hcsm hfz_m hsym_m R hpostM) (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact (h_no_panic (F ∗ R) sm hpan hpostM).elim
  · exact (h_no_exit (F ∗ R) code sm hex hpostM).elim
  · exact ⟨sm, hsteps, Or.inr ⟨hoom_st, h_oom R sm hoom_st hpostM⟩⟩

theorem entails_anyHeap (P : SepProp) : P ⊢ anyHeap :=
  Entails.top_right fun _ => SepProp.holds_anyHeap_iff.mpr trivial

theorem allowPanic_panicked {φ : Prop} {P R : SepProp} {m : Memory}
    (hφ : φ) (h : m ⊨ P ∗ R) : m ⊨ (⌜φ⌝ ∗ anyHeap) ∗ R := by
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hφ, Satisfies.mono (sepConj_mono_left (entails_anyHeap P)) h⟩

theorem allowPanic_frame {φ ψ : Prop} {F R : SepProp} {m : Memory}
    (hφ : φ → ψ) (h : m ⊨ ((⌜φ⌝ ∗ anyHeap) ∗ F) ∗ R) : m ⊨ (⌜ψ⌝ ∗ anyHeap) ∗ R := by
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at h
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨hφ h.1, ?_⟩
  rw [← sepConj_assoc] at h
  exact Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) h.2

theorem allowPanic_not_exited {R : SepProp} {m : Memory}
    (h : m ⊨ (⌜False⌝ : SepProp) ∗ R) : False :=
  not_satisfies_false_sepConj h

namespace SepWPp

variable {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
  {Q Qp : State → SepProp → Prop} {oom : State → SepProp}

/-- Run a `SepWP` segment to `mid`, re-establishing `img.FrozenLoaded sm` and
    `sm.symtab = img.symtab` at `mid` before continuing with `SepWPp`. -/
theorem of_sepWP_frozen {mid : BitVec 64} {img : Obj.Image}
    (hfz : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (h : SepWP prog mid s P (fun sm Pm =>
      img.FrozenLoaded sm → sm.symtab = img.symtab →
      SepWPp prog ret sm Pm Q Qp oom) oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | hoom⟩
  · have hfz_m := hfz.of_keepsFrozen hsteps.keepsFrozen
    have hsym_m := hsteps.symtab_eq.trans hsym
    obtain ⟨sf, hsteps', hout⟩ := hnext hfz_m hsym_m R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

abbrev of_sepWP_inv := @of_sepWP_frozen

/-- A final `SepWP` segment that reaches `ret` (no panic on this path). -/
theorem of_sepWP_ret (h : SepWP prog ret s P Q oom) : SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hq⟩ | hoom⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, P_f, hmf, hq⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

abbrev of_sepWP_ret_panicsOr := @of_sepWP_ret

/-- Reached `ret`. -/
theorem done {Qp : State → SepProp → Prop} (hpc : s.pc = ret) (hrun : s.status = .Running)
    (hq : Q s P) : SepWPp prog ret s P Q Qp oom :=
  fun _ hm _ => ⟨s, Steps.refl s, Or.inl ⟨hpc, hrun, P, hm, hq⟩⟩

/-- Pure (non-memory) instruction step rule for `SepWPp` (e.g. stepping `BL` before `wpp_call`). -/
theorem step_pure {s' : State} {pc : BitVec 64} {inst : Instr}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some inst)
    (hexec : prog.evalInst inst (s.setPC pc) = s')
    (hmem : s'.mem = s.mem)
    (hnext : SepWPp prog ret s' P Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  have hs_pc : s.setPC pc = s := by
    cases s; simp [State.setPC] at hpc ⊢; exact hpc.symm
  have hfetch' : prog.fetch s.pc = some inst := hpc.symm ▸ hfetch
  have hexec' : prog.evalInst inst s = s' := by rw [← hs_pc, hexec]
  have hm' : s'.mem ⊨ P ∗ R := by rwa [hmem]
  have hL' : prog.CodeLoaded s'.mem := by rwa [hmem]
  obtain ⟨sf, hsteps, hout⟩ := hnext R hm' hL'
  exact ⟨sf, Steps.step (hexec' ▸ Step.exec hrun (prog.fetchMem_of_fetch hL hfetch')) hsteps, hout⟩

/-- Case split on a conditional PC. -/
theorem ite {c : Prop} {inst : Decidable c} {pc1 pc2 : BitVec 64}
    (hpc : s.pc = @_root_.ite (BitVec 64) c inst pc1 pc2)
    (hthen : c → SepWPp prog ret (s.setPC pc1) P Q Qp oom)
    (helse : ¬ c → SepWPp prog ret (s.setPC pc2) P Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  letI := inst
  by_cases hc : c
  · have hpc1 : s.pc = pc1 := by simp [hpc, hc]
    have hs1 : s.setPC pc1 = s := by cases s; simp [State.setPC] at hpc1 ⊢; exact hpc1.symm
    exact hs1 ▸ hthen hc
  · have hpc2 : s.pc = pc2 := by simp [hpc, hc]
    have hs2 : s.setPC pc2 = s := by cases s; simp [State.setPC] at hpc2 ⊢; exact hpc2.symm
    exact hs2 ▸ helse hc

/-- Precondition weakening. -/
theorem weaken_pre {P' : SepProp} (hent : P ⊢ P') (h : SepWPp prog ret s P' Q Qp oom) :
    SepWPp prog ret s P Q Qp oom :=
  fun R hm => h R (Satisfies.mono (sepConj_mono_left hent) hm)

/-- Fold part `T` of the spatial context into `T'` (`T` is found by `sep_focus`). -/
theorem fold {T T' F : SepProp} (hent : T ⊢ T') (hf : P = T ∗ F)
    (h : SepWPp prog ret s (T' ∗ F) Q Qp oom) : SepWPp prog ret s P Q Qp oom :=
  weaken_pre (hf ▸ sepConj_mono_left hent) h

/-- Move a pure conjunct into the context. -/
theorem pure_elim {φ : Prop} (h : φ → SepWPp prog ret s P Q Qp oom) :
    SepWPp prog ret s (⌜φ⌝ ∗ P) Q Qp oom := by
  intro R hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact h hm.1 R hm.2

/-- Eliminate a spatial context consisting only of a pure assertion `⌜φ⌝` into a hypothesis. -/
theorem pure_elim_only {φ : Prop} (h : φ → SepWPp prog ret s emp Q Qp oom) :
    SepWPp prog ret s ⌜φ⌝ Q Qp oom := by
  intro R hm
  rw [satisfies_pure_sepConj] at hm
  exact h hm.1 R (by rw [emp_sepConj]; exact hm.2)

/-- Eliminate an existential at the head of the spatial context. -/
theorem exists_elim {α : Sort _} {P : α → SepProp} (h : ∀ a, SepWPp prog ret s (P a) Q Qp oom) :
    SepWPp prog ret s (∃∗ a, P a) Q Qp oom := by
  intro R hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨a, ha⟩ := hm
  exact h a R ha

/-- Compositional `Spec.split` subroutine invocation rule for `SepWPp`. -/
theorem call_sep {α : Type} {entry ret_pc : BitVec 64}
    {preRegs : α → State → Prop} {preMem : α → SepProp}
    {postRegs : α → State → State → Prop} {postMem : α → SepProp}
    (hcall : subroutine_ok prog entry (Spec.split preRegs preMem postRegs postMem))
    {x : α} {Frame P' : SepProp}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpreR : preRegs x s)
    (hframe : SepFrame (preMem x) P Frame)
    (hp' : postMem x ∗ Frame = P')
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      (postRegs x s sf ∧ sf.sp = s.sp ∧ CalleeSavedPreserved s sf) →
      SepWPp prog ret sf P' Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  apply of_sepWP (mid := ret_pc)
  refine SepWP.call_sep hcall hpc hrun hsp_align hlr hpreR hframe hp' ?_
  intro sf hpc_sf hrun_sf hpost
  exact SepWP.done hpc_sf hrun_sf (hnext sf hpc_sf hrun_sf hpost)

/-- Unified `subroutine_ok` call rule for `SepWPp`: `hpanic` receives both `sf.status = .Panicked`
    and `(∃ R', sf.mem ⊨ spec.onPanic x s sf ∗ R')`, so it handles both non-panicking callees
    (`spec.onPanic = ⌜False⌝`, even when `Qp` is an abstract variable) and panicking callees
    (`spec.onPanic = ⌜φ⌝ ∗ anyHeap`). -/
theorem call_wpp {α : Type} {entry ret_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry spec)
    {x : α} {F : SepProp}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked →
      (∃ R', sf.mem ⊨ spec.onPanic x s sf ∗ R') → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp oom)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by
      wp_close_oom_default) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  obtain ⟨sm, hsteps, hout⟩ :=
    reaches_outcome_iff.1 (subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun (hpre R hm) hsp) hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom_st, hpost⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ := hnext sm hpcm hrunm hspm hcsm R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · have hpan_ex : ∃ R', sm.mem ⊨ spec.onPanic x s sm ∗ R' := ⟨F ∗ R, hpost⟩
    rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, _, hpost, hpanic sm hpan hpan_ex⟩)⟩
  · exact (hexit sm code _ hex hpost).elim
  · exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom_st, hoom sm R hoom_st hpost⟩)⟩

/-- Unified frozen-aware `subroutine_ok` call rule for `SepWPp`: preserves `img.FrozenLoaded`
    and `symtab = img.symtab` across the call and hands `img.FrozenLoaded sf` and
    `sf.symtab = img.symtab` to the continuation `hnext`. -/
theorem call_wpp_frozen {α : Type} {entry ret_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry spec)
    {x : α} {F : SepProp} {img : Obj.Image}
    (hfz : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked →
      (∃ R', sf.mem ⊨ spec.onPanic x s sf ∗ R') → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp oom)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by
      wp_close_oom_default) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  obtain ⟨sm, hsteps, hout⟩ :=
    reaches_outcome_iff.1 (subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun (hpre R hm) hsp) hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom_st, hpost⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hfz_m := hfz.of_keepsFrozen hsteps.keepsFrozen
    have hsym_m := hsteps.symtab_eq.trans hsym
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm hfz_m hsym_m R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · have hpan_ex : ∃ R', sm.mem ⊨ spec.onPanic x s sm ∗ R' := ⟨F ∗ R, hpost⟩
    rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, _, hpost, hpanic sm hpan hpan_ex⟩)⟩
  · exact (hexit sm code _ hex hpost).elim
  · exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom_st, hoom sm R hoom_st hpost⟩)⟩

/-- Call (`bl`) a callee with spec `spec` (which may panic), lending it `spec.pre x s` out of `P`
    and keeping the frame `F`. `hexit` excludes process exit by the callee. -/
theorem call {α : Type} {entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {F : SepProp}
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp oom)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by
      wp_close_oom_default) :
    SepWPp prog ret s P Q Qp oom :=
  call_wpp hcall hpc hrun hsp hlr hpre hexit (fun sf hpan _ => hpanic sf hpan) hnext hoom

/-- Framed `SepWPp.call`: lend the callee `⌜φ⌝ ∗ T` where `spec.pre x s = ⌜φ⌝ ∗ T` and
    `P = T ∗ F`. -/
theorem call_frame {α : Type} {entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {φ : Prop}
    {T F : SepProp}
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp oom)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by
      wp_close_oom_default) :
    SepWPp prog ret s P Q Qp oom := by
  refine call (x := x) (F := F) hcall hpc hrun hsp hlr ?_ hexit hpanic hnext hoom
  intro R hm
  rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
  exact ⟨hφ, hm⟩

/-- Framed `SepWPp.call` carrying `img.FrozenLoaded` and `symtab = img.symtab` across the call. -/
theorem call_frame_frozen {α : Type} {entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {φ : Prop}
    {T F : SepProp} {img : Obj.Image}
    (hcall : subroutine_ok prog entry spec)
    (hfz : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp oom)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by
      wp_close_oom_default) :
    SepWPp prog ret s P Q Qp oom := by
  refine call_wpp_frozen (x := x) (F := F) hcall hfz hsym hpc hrun hsp hlr ?_ hexit
    (fun sf hpan _ => hpanic sf hpan) hnext hoom
  intro R hm
  rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
  exact ⟨hφ, hm⟩

/-- Framed `SepWPp.call` for a `spec0.inImage img` callee, automatically discharging the
    `img.FrozenLoaded s ∧ s.symtab = img.symtab` precondition of `Spec.inImage` and preserving
    both facts on the post-call state `sf`. -/
theorem call_inImage_frame {α : Type} {entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {φ : Prop}
    {T F : SepProp} {img : Obj.Image}
    (hcall : subroutine_ok prog entry (spec.inImage img))
    (hfz : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp oom)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by
      wp_close_oom_default) :
    SepWPp prog ret s P Q Qp oom := by
  refine call_wpp_frozen (x := x) (F := F) hcall hfz hsym hpc hrun hsp hlr ?_ hexit
    (fun sf hpan _ => hpanic sf hpan) hnext hoom
  intro R hm
  dsimp [Spec.inImage]
  rw [hspec, sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj,
    ← sepConj_assoc, ← hP]
  exact ⟨⟨hfz, hsym⟩, hφ, hm⟩

/-- Tail call (`b`) to a callee with spec `spec` (which may panic): the callee returns to our
    caller (`ret` is the current return address). -/
theorem tailcall {α : Type} {entry : BitVec 64} {spec : Spec α} {x : α} {F : SepProp}
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hret : ∀ sf : State, sf.pc = ret → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → Q sf (spec.post x s sf ∗ F))
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by
      wp_close_oom_default) :
    SepWPp prog ret s P Q Qp oom :=
  call hcall hpc hrun hsp hlr hpre hexit hpanic (fun sf hpcf hrunf hspf hcsf =>
    done hpcf hrunf (hret sf hpcf hrunf hspf hcsf)) hoom

end SepWPp

abbrev call_frame_frozen := @SepWPp.call_frame_frozen

end ProofLib

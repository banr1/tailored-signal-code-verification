/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public meta import ProofLib.SepLogic.WP -- shake: keep
public meta import Lean -- shake: keep

/-!
# VM-Preserving Basic-Block `SepWP` Steppers

Provides `trapHooks`, `sepWP_rebase_vmPreserved`, and the `by_vm_steps` / `wp_steps_vm` tactics to
supply `VmPreserved s sm` across basic blocks containing `STR`/`STP` on `P.rebase b Hk` without
scanning block instructions or requiring `IsLsBlockProg`.

The `vmPreserved_*` and `tpidrEl0_applyWriteback` lemmas carry global `@[simp, arm64_norm, wp_norm]`
attributes so callers invoking `wp_steps_vm` (`wp_done` via `simp only [wp_norm, arm64_norm]`) reduce
`VmPreserved s (s'.op ..)` and `(applyWriteback s wb).tpidrEl0` directly without `scoped` simp
attributes.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Placed.BudgetVmSteps

open _root_.Arm64 ProofLib
open LibsignalBinary.Heap (FdsHiFrame VmPreserved)


theorem vmPreserved_right_congr {s s₁ s₂ : State} (h : VmPreserved s₁ s₂) :
    VmPreserved s s₂ ↔ VmPreserved s s₁ :=
  ⟨fun h02 => h02.trans h.symm, fun h01 => h01.trans h⟩

@[simp, arm64_norm, wp_norm]
theorem vmPreserved_refl_iff (s : State) : VmPreserved s s ↔ True :=
  ⟨fun _ => trivial, fun _ => VmPreserved.refl s⟩

@[simp, arm64_norm, wp_norm]
theorem vmPreserved_setPC (s s' : State) (pc : BitVec 64) :
    VmPreserved s (s'.setPC pc) ↔ VmPreserved s s' :=
  vmPreserved_right_congr
    ⟨⟨rfl, rfl, rfl⟩, by cases s'; rfl, fun _ => by cases s'; rfl, fun _ _ _ => by cases s'; rfl⟩

@[simp, arm64_norm, wp_norm]
theorem vmPreserved_advancePC (s s' : State) :
    VmPreserved s s'.advancePC ↔ VmPreserved s s' :=
  vmPreserved_right_congr
    ⟨⟨rfl, rfl, rfl⟩, by cases s'; rfl, fun _ => by cases s'; rfl, fun _ _ _ => by cases s'; rfl⟩

@[simp, arm64_norm, wp_norm]
theorem vmPreserved_setPState (s s' : State) (ps : PState) :
    VmPreserved s (s'.setPState ps) ↔ VmPreserved s s' :=
  vmPreserved_right_congr
    ⟨⟨rfl, rfl, rfl⟩, by cases s'; rfl, fun _ => by cases s'; rfl, fun _ _ _ => by cases s'; rfl⟩

@[simp, arm64_norm, wp_norm]
theorem vmPreserved_writeReg64 (s s' : State) (r : Reg) (v : BitVec 64) :
    VmPreserved s (s'.writeReg64 r v) ↔ VmPreserved s s' :=
  vmPreserved_right_congr
    ⟨⟨rfl, rfl, rfl⟩, by cases s'; cases r <;> rfl, fun _ => by cases s'; cases r <;> rfl,
      fun _ _ _ => by cases s'; cases r <;> rfl⟩

@[simp, arm64_norm, wp_norm]
theorem vmPreserved_writeReg32 (s s' : State) (r : Reg) (v : BitVec 32) :
    VmPreserved s (s'.writeReg32 r v) ↔ VmPreserved s s' :=
  vmPreserved_writeReg64 s s' r _

@[simp, arm64_norm, wp_norm]
theorem vmPreserved_writeReg (s s' : State) (w : Width) (r : Reg) (v : BitVec 64) :
    VmPreserved s (s'.writeReg w r v) ↔ VmPreserved s s' :=
  vmPreserved_writeReg64 s s' r _

@[simp, arm64_norm, wp_norm]
theorem vmPreserved_writeVReg128 (s s' : State) (i : BitVec 5) (v : BitVec 128) :
    VmPreserved s (s'.writeVReg128 i v) ↔ VmPreserved s s' :=
  vmPreserved_right_congr
    ⟨⟨rfl, rfl, rfl⟩, by cases s'; rfl, fun _ => by cases s'; rfl, fun _ _ _ => by cases s'; rfl⟩

@[simp, arm64_norm, wp_norm]
theorem vmPreserved_writeVReg64 (s s' : State) (i : BitVec 5) (v : BitVec 64) :
    VmPreserved s (s'.writeVReg64 i v) ↔ VmPreserved s s' :=
  vmPreserved_right_congr
    ⟨⟨rfl, rfl, rfl⟩, by cases s'; rfl, fun _ => by cases s'; rfl, fun _ _ _ => by cases s'; rfl⟩

@[simp, arm64_norm, wp_norm]
theorem vmPreserved_writeVReg32 (s s' : State) (i : BitVec 5) (v : BitVec 32) :
    VmPreserved s (s'.writeVReg32 i v) ↔ VmPreserved s s' :=
  vmPreserved_right_congr
    ⟨⟨rfl, rfl, rfl⟩, by cases s'; rfl, fun _ => by cases s'; rfl, fun _ _ _ => by cases s'; rfl⟩

@[simp, arm64_norm, wp_norm]
theorem vmPreserved_applyWriteback (s s' : State) (wb : Option (Reg × BitVec 64)) :
    VmPreserved s (applyWriteback s' wb) ↔ VmPreserved s s' := by
  cases wb with
  | none => rfl
  | some p => exact vmPreserved_writeReg64 s s' p.1 p.2

@[simp, arm64_norm, wp_norm]
theorem vmPreserved_setMem_writeBytes (s s' : State) (addr : BitVec 64) (bs : List (BitVec 8)) :
    VmPreserved s (s'.setMem (s'.mem.writeBytes addr bs)) ↔ VmPreserved s s' :=
  vmPreserved_right_congr ⟨⟨rfl, rfl, rfl⟩, by cases s'; rfl, fun a => by
    have hp := congrFun (Memory.perm_writeBytes s'.mem addr bs) a
    cases s'; exact hp, fun _ _ _ => by cases s'; rfl⟩

@[simp, arm64_norm, wp_norm]
theorem vmPreserved_setMem_write8 (s s' : State) (addr : BitVec 64) (v : BitVec 8) :
    VmPreserved s (s'.setMem (s'.mem.write8 addr v)) ↔ VmPreserved s s' :=
  vmPreserved_right_congr ⟨⟨rfl, rfl, rfl⟩, by cases s'; rfl, fun a => by
    have hp := congrFun (Memory.perm_write8 s'.mem addr v) a
    cases s'; exact hp, fun _ _ _ => by cases s'; rfl⟩

@[simp, arm64_norm, wp_norm]
theorem vmPreserved_setMem_write16 (s s' : State) (addr : BitVec 64) (v : BitVec 16) :
    VmPreserved s (s'.setMem (s'.mem.write16 addr v)) ↔ VmPreserved s s' :=
  vmPreserved_right_congr ⟨⟨rfl, rfl, rfl⟩, by cases s'; rfl, fun a => by
    have hp := congrFun (Memory.perm_write16 s'.mem addr v) a
    cases s'; exact hp, fun _ _ _ => by cases s'; rfl⟩

@[simp, arm64_norm, wp_norm]
theorem vmPreserved_setMem_write32 (s s' : State) (addr : BitVec 64) (v : BitVec 32) :
    VmPreserved s (s'.setMem (s'.mem.write32 addr v)) ↔ VmPreserved s s' :=
  vmPreserved_right_congr ⟨⟨rfl, rfl, rfl⟩, by cases s'; rfl, fun a => by
    have hp := congrFun (Memory.perm_write32 s'.mem addr v) a
    cases s'; exact hp, fun _ _ _ => by cases s'; rfl⟩

@[simp, arm64_norm, wp_norm]
theorem vmPreserved_setMem_write64 (s s' : State) (addr : BitVec 64) (v : BitVec 64) :
    VmPreserved s (s'.setMem (s'.mem.write64 addr v)) ↔ VmPreserved s s' :=
  vmPreserved_right_congr ⟨⟨rfl, rfl, rfl⟩, by cases s'; rfl, fun a => by
    have hp := congrFun (Memory.perm_write64 s'.mem addr v) a
    cases s'; exact hp, fun _ _ _ => by cases s'; rfl⟩

@[simp, arm64_norm, wp_norm]
theorem vmPreserved_setStatus (s s' : State) (es : ExecStatus) :
    VmPreserved s (s'.setStatus es) ↔ VmPreserved s s' :=
  vmPreserved_right_congr
    ⟨⟨rfl, rfl, rfl⟩, by cases s'; rfl, fun _ => by cases s'; rfl, fun _ _ _ => by cases s'; rfl⟩

@[simp, arm64_norm, wp_norm]
theorem vmPreserved_appendTrace (s s' : State) (evs : List TraceEvent) :
    VmPreserved s (s'.appendTrace evs) ↔ VmPreserved s s' :=
  vmPreserved_right_congr
    ⟨⟨rfl, rfl, rfl⟩, by cases s'; rfl, fun _ => by cases s'; rfl, fun _ _ _ => by cases s'; rfl⟩

theorem vmPreserved_setFs (s s' : State) (f : FsState) (hfds : FdsHiFrame s' (s'.setFs f)) :
    VmPreserved s (s'.setFs f) ↔ VmPreserved s s' :=
  vmPreserved_right_congr ⟨⟨rfl, rfl, rfl⟩, by cases s'; rfl, fun _ => by cases s'; rfl, hfds⟩

@[simp, arm64_norm, wp_norm]
theorem vmPreserved_setFs_setFile (s s' : State) (path : String) (e : Option FsEntry) :
    VmPreserved s (s'.setFs (s'.fs.setFile path e)) ↔ VmPreserved s s' :=
  vmPreserved_setFs s s' _ fun _ _ _ => by cases s'; rfl

@[simp, arm64_norm, wp_norm]
theorem vmPreserved_stepExclLoop (s s' : State) :
    VmPreserved s s'.stepExclLoop ↔ VmPreserved s s' :=
  vmPreserved_right_congr
    ⟨⟨rfl, rfl, rfl⟩, by cases s'; rfl, fun _ => by cases s'; rfl, fun _ _ _ => by cases s'; rfl⟩

@[simp, arm64_norm, wp_norm]
theorem tpidrEl0_applyWriteback (s : State) (wb : Option (Reg × BitVec 64)) :
    (applyWriteback s wb).tpidrEl0 = s.tpidrEl0 := by
  cases wb with
  | none => rfl
  | some p => exact State.tpidrEl0_writeReg64 s p.1 p.2

/-- Trap-all hook table used with `noSyscalls` in `sepWP_rebase_vmPreserved` so `wp_steps` can
    discharge `VmPreserved s sm` across basic blocks containing `STR`/`STP` (`SepWP.step_str*`
    quantifies over an abstract `m' : Memory` without `m'.perm = s.mem.perm`). -/
def trapHooks : String → Option (State → State) :=
  fun _ => some (fun s => s.setStatus (.Exception "extern"))

private theorem findSome?_override_none :
    ∀ (l : List (String × Nat)) (off : Nat),
      (l.findSome? fun (_n, o) => if o == off then (none : Option (State → State)) else none) = none
  | [], _ => rfl
  | (_n, _o) :: tl, off => by
    dsimp only [List.findSome?]
    rw [ite_self]
    exact findSome?_override_none tl off

private theorem findSome?_trapHooks_some :
    ∀ (l : List (String × Nat)) {off : Nat} {f : State → State},
      (l.findSome? fun (n, o) => if o == off then trapHooks n else none) = some f →
      f = fun s => s.setStatus (.Exception "extern")
  | [], _, _, h => by simp at h
  | (n, o) :: tl, off, f, h => by
    simp only [List.findSome?_cons, trapHooks] at h
    by_cases ho : (o == off) = true
    · simp only [ho, ↓reduceIte, Option.some.injEq] at h
      exact h.symm
    · simp only [ho, Bool.false_eq_true, ↓reduceIte] at h
      exact findSome?_trapHooks_some tl h

private theorem findSome?_stubs_eq_none_of_trapHooks (Hk : String → Option (State → State)) :
    ∀ (l : List (String × Nat)) {off : Nat},
      (l.findSome? fun (n, o) => if o == off then trapHooks n else none) = none →
      (l.findSome? fun (n, o) => if o == off then Hk n else none) = none
  | [], _, _ => rfl
  | (n, o) :: tl, off, h => by
    simp only [List.findSome?_cons, trapHooks] at h ⊢
    by_cases ho : (o == off) = true
    · simp only [ho, ↓reduceIte] at h
      cases h
    · simp only [ho, Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact findSome?_stubs_eq_none_of_trapHooks Hk tl h

private theorem externAt?_rebase_trapHooks_some {P : Program} {b pc : BitVec 64} {f : State → State}
    (h : ((P.rebase b trapHooks).withSvc noSyscalls).externAt? pc = some f) :
    f = fun s => s.setStatus (.Exception "extern") := by
  unfold Program.withSvc Program.externAt? Program.hookAtOff? Program.rebase at h
  dsimp only at h
  rw [findSome?_override_none] at h
  cases hm : (P.stubs.findSome? fun (n, o) =>
      if o == (pc - b).toNat then trapHooks n else none) with
  | none =>
    rw [hm] at h
    cases h
  | some g =>
    rw [hm] at h
    injection h with hgf
    subst hgf
    exact findSome?_trapHooks_some P.stubs hm

private theorem externAt?_rebase_eq_none_of_trapHooks {P : Program} {b pc : BitVec 64}
    {Hk : String → Option (State → State)}
    (h : (P.rebase b trapHooks).externAt? pc = none) :
    (P.rebase b Hk).externAt? pc = none := by
  unfold Program.externAt? Program.hookAtOff? Program.rebase at h ⊢
  dsimp only at h ⊢
  rw [findSome?_override_none] at h ⊢
  have h1 : (P.stubs.findSome? fun (n, o) =>
      if o == (pc - b).toNat then trapHooks n else none) = none := by
    cases hm : (P.stubs.findSome? fun (n, o) =>
        if o == (pc - b).toNat then trapHooks n else none) with
    | none => rfl
    | some g =>
      rw [hm] at h
      cases h
  rw [findSome?_stubs_eq_none_of_trapHooks Hk P.stubs h1]
  rfl

private theorem steps_rebase_trapHooks_noSyscalls {P : Program} {b : BitVec 64}
    {Hk : String → Option (State → State)} {s sm : State}
    (hsteps : Steps ((P.rebase b trapHooks).withSvc noSyscalls) s sm)
    (hrun_m : sm.status = .Running) :
    Steps (P.rebase b Hk) s sm ∧ ProofLib.StdStartup.VmFieldsPreserved s sm ∧ sm.fs = s.fs := by
  induction hsteps with
  | refl => exact ⟨Steps.refl _, ProofLib.StdStartup.VmFieldsPreserved.refl _, rfl⟩
  | @step s1 s2 _ h1 hrest ih =>
    have hr2 : s2.status = .Running := by
      cases hrest with
      | refl => exact hrun_m
      | step hs _ => cases hs <;> assumption
    rcases ih hrun_m with ⟨hsteps_rest, hvm_rest, hfs_rest⟩
    cases h1 with
    | halt_unmapped _ _ _ => cases s1; cases hr2
    | extern_fault _ _ _ => cases s1; cases hr2
    | extern _ hext _ _ =>
      rw [externAt?_rebase_trapHooks_some hext] at hr2
      cases s1; cases hr2
    | @exec inst hr1 hfe =>
      have hext_trap : (P.rebase b trapHooks).externAt? s1.pc = none := by
        cases he : (P.rebase b trapHooks).externAt? s1.pc with
        | none => rfl
        | some g =>
          unfold Program.fetchMem Program.withSvc at hfe
          change (if (Program.externAt? (P.rebase b trapHooks) s1.pc).isSome then none else _) =
              some inst at hfe
          rw [he] at hfe
          cases hfe
      have hfeH : (P.rebase b Hk).fetchMem s1.mem s1.pc = some inst := by
        have hext_hk := externAt?_rebase_eq_none_of_trapHooks (Hk := Hk) hext_trap
        unfold Program.fetchMem at hfe ⊢
        change (if (Program.externAt? (P.rebase b trapHooks) s1.pc).isSome then none else _) =
            some inst at hfe
        rw [hext_trap] at hfe
        rw [hext_hk]
        exact hfe
      have hnsvc0 : inst.isSvc0 = false := by
        cases ht : inst.isSvc0 with
        | false => rfl
        | true =>
          cases inst with
          | system isHalt imm =>
            cases isHalt with
            | true => simp [Instr.isSvc0] at ht
            | false =>
              simp only [Instr.isSvc0, Bool.not_false, Bool.true_and, beq_iff_eq] at ht
              subst ht
              cases s1; cases hr2
          | _ => simp [Instr.isSvc0] at ht
      have hev1 := ProofLib.StdStartup.evalInst_eq_execInst_of_not_isSvc0
        ((P.rebase b trapHooks).withSvc noSyscalls) hnsvc0 s1
      have hev2 := ProofLib.StdStartup.evalInst_eq_execInst_of_not_isSvc0
        (P.rebase b Hk) hnsvc0 s1
      have hfs_step : (execInst inst s1).fs = s1.fs :=
        (ProofLib.execInst_brk_oracle_of_not_isSvc0 hnsvc0 s1).2.2.2.2.2
      rw [hev1] at hsteps_rest hvm_rest hfs_rest
      exact ⟨Steps.step (hev2 ▸ Step.exec hr1 hfeH) hsteps_rest,
        ProofLib.StdStartup.VmFieldsPreserved.trans
          (ProofLib.StdStartup.execInst_vmFields_of_not_isSvc0 hnsvc0 s1) hvm_rest,
        hfs_rest.trans hfs_step⟩

/-- Lift a total-correctness `SepWP` on `((P.rebase b trapHooks).withSvc noSyscalls)` to
    `P.rebase b Hk` for any `Hk : String → Option (State → State)`, automatically supplying
    `VmPreserved s sm` (including across `SepWP.step_str*` / `SepWP.step_stp*` abstract
    `m' : Memory` transitions) from `sm.tpidrEl0 = s.tpidrEl0`. -/
theorem sepWP_rebase_vmPreserved {P : Program} {b : BitVec 64}
    {Hk : String → Option (State → State)}
    {target_pc : BitVec 64} {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    (hwp : SepWP ((P.rebase b trapHooks).withSvc noSyscalls) target_pc s Pre
      (fun sm Pm => sm.tpidrEl0 = s.tpidrEl0 ∧ post sm Pm)) :
    SepWP (P.rebase b Hk) target_pc s Pre (fun sm Pm => VmPreserved s sm ∧ post sm Pm) := by
  apply SepWP.of_reaches_pc
  intro R hm hL
  have hL' : ((P.rebase b trapHooks).withSvc noSyscalls).CodeLoaded s.mem :=
    hL.of_base_code rfl rfl
  obtain ⟨sm, hsteps, hout⟩ := SepWP.to_reaches_pc hwp hm hL'
  rcases hout with ⟨hpc, hrun, Pm, hPm, htp, hpost⟩ | ⟨_, hoom⟩
  · obtain ⟨hsteps_hk, hvm, hfs⟩ := steps_rebase_trapHooks_noSyscalls (Hk := Hk) hsteps hrun
    exact ⟨sm, hsteps_hk,
      Or.inl ⟨hpc, hrun, Pm, hPm, VmPreserved.of_vm_tpidr hvm htp (FdsHiFrame.of_fs_eq hfs), hpost⟩⟩
  · exact False.elim (not_satisfies_false_sepConj hoom)

/-- Run `tac` (typically `(wp_steps; wp_done)`) on `SepWP (P.rebase b trapHooks) ...` so
    `ProofLib.tryCloseFetchFromHasCode` and `SymWP` see the `Program.rebase` head directly,
    then transport the elaborated proof term to `((P.rebase b trapHooks).withSvc noSyscalls)`
    via `sepWP_rebase_vmPreserved` (`fetch` and non-`SVC` `evalInst` are definitionally equal). -/
syntax "by_vm_steps " tacticSeq : tactic
macro "wp_steps_vm" : tactic => `(tactic| by_vm_steps (wp_steps; wp_done))

elab_rules : tactic
  | `(tactic| by_vm_steps $tac:tacticSeq) => do
    Lean.Elab.Tactic.evalTactic
      (← `(tactic| apply LibsignalBinary.Proofs.Placed.BudgetVmSteps.sepWP_rebase_vmPreserved))
    let g ← Lean.Elab.Tactic.getMainGoal
    g.withContext do
      let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData
      unless ty.getAppFn.isConstOf ``ProofLib.SepWP && ty.getAppNumArgs == 6 do
        throwError "by_vm_steps: expected `SepWP ((P.rebase b trapHooks).withSvc noSyscalls) ...`, got{Lean.indentExpr ty}"
      let e2 := ty.getArg! 0
      unless e2.getAppFn.isConstOf ``Arm64.Program.withSvc && e2.getAppNumArgs == 2 do
        throwError "by_vm_steps: program is not `Program.withSvc`:{Lean.indentExpr e2}"
      let e1 := e2.getArg! 0
      let ty1 := Lean.mkAppN ty.getAppFn #[e1, ty.getArg! 1, ty.getArg! 2, ty.getArg! 3, ty.getArg! 4, ty.getArg! 5]
      let g1 ← Lean.Meta.mkFreshExprMVar ty1
      let savedGoals ← Lean.Elab.Tactic.getGoals
      Lean.Elab.Tactic.setGoals [g1.mvarId!]
      Lean.Elab.Tactic.evalTactic (← `(tactic| ($tac)))
      let rem ← Lean.Elab.Tactic.getGoals
      unless rem.isEmpty do
        throwError "by_vm_steps: inner tactic left {rem.length} unsolved goal(s)"
      Lean.Elab.Tactic.setGoals savedGoals.tail!
      let prf1 ← Lean.instantiateMVars g1
      let prf2 := prf1.replace fun sub => if sub.eqv e1 then some e2 else none
      g.assign prf2

end LibsignalBinary.Proofs.Placed.BudgetVmSteps

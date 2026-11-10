/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CommonPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import ProofLib.FsTrace

/-!
# `FdsGe3Closed`-Threaded VM-Stepping and Call Helpers for Arm `R1b`

Proves straight-line basic-block `State.fs` preservation (`by_vm_fs_open` via
`((P.rebase b trapHooks).withSvc noSyscalls)`) alongside `VmPreserved`, and provides the
`r1b_call_withFds_placed` call combinator on Block `579`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CommonPlacedBudgetFd

open Arm64 ProofLib SepProp
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalPublicApi.StoreKit (withLsCodeRoLoaded)
open CryptoVerification.SignalSession.Cli.MainHops (RunCall)
open CryptoVerification.SignalSession.Cli.RunCompose
  (PanicK r1b_CodeOk runPanicProp runProgPlaced)
open LibsignalBinary.Heap (FdsHiFrame VmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (trapHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CommonPlacedBudget
  (r1b_call_placed)

theorem fdsGe3Closed_of_fs_eq {s s' : State} (hfs : s'.fs = s.fs) (hfd : FdsGe3Closed s.fs) :
    FdsGe3Closed s'.fs :=
  hfs ▸ hfd

theorem execInst_fs_of_not_isSvc0 {inst : Instr} (h : inst.isSvc0 = false) (s : State) :
    (execInst inst s).fs = s.fs := by
  have hnf : inst.isNonFs s = true := by
    cases inst with
    | system isHalt imm =>
      cases isHalt with
      | true => rfl
      | false =>
        by_cases himm : imm = 0#16
        · subst himm; simp [Instr.isSvc0] at h
        · simp [Instr.isNonFs, himm]
    | _ => rfl
  have hset := Arm64.Process.execInst_setFs_of_isNonFs inst s s.fs hnf
  have hs : s.setFs s.fs = s := by cases s; rfl
  rw [hs] at hset
  simpa [State.setFs] using congrArg State.fs hset

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
    | some _ =>
      rw [hm] at h
      cases h
  rw [findSome?_stubs_eq_none_of_trapHooks Hk P.stubs h1]
  rfl

theorem steps_rebase_trapHooks_noSyscalls_fs {P : Program} {b : BitVec 64}
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
        | some _ =>
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
      rw [hev1] at hsteps_rest hvm_rest hfs_rest
      exact ⟨Steps.step (hev2 ▸ Step.exec hr1 hfeH) hsteps_rest,
        ProofLib.StdStartup.VmFieldsPreserved.trans
          (ProofLib.StdStartup.execInst_vmFields_of_not_isSvc0 hnsvc0 s1) hvm_rest,
        hfs_rest.trans (execInst_fs_of_not_isSvc0 hnsvc0 s1)⟩

theorem sepWP_rebase_vmPreserved_fs {P : Program} {b : BitVec 64}
    {Hk : String → Option (State → State)}
    {target_pc : BitVec 64} {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    (hwp : SepWP ((P.rebase b trapHooks).withSvc noSyscalls) target_pc s Pre
      (fun sm Pm => sm.tpidrEl0 = s.tpidrEl0 ∧ post sm Pm)) :
    SepWP (P.rebase b Hk) target_pc s Pre
      (fun sm Pm => VmPreserved s sm ∧ sm.fs = s.fs ∧ post sm Pm) := by
  apply SepWP.of_reaches_pc
  intro R hm hL
  have hL' : ((P.rebase b trapHooks).withSvc noSyscalls).CodeLoaded s.mem :=
    hL.of_base_code rfl rfl
  obtain ⟨sm, hsteps, hout⟩ := SepWP.to_reaches_pc hwp hm hL'
  rcases hout with ⟨hpc, hrun, Pm, hPm, htp, hpost⟩ | ⟨_, hoom⟩
  · obtain ⟨hsteps_hk, hvm, hfs⟩ := steps_rebase_trapHooks_noSyscalls_fs (Hk := Hk) hsteps hrun
    exact ⟨sm, hsteps_hk, Or.inl ⟨hpc, hrun, Pm, hPm,
      VmPreserved.of_vm_tpidr hvm htp (FdsHiFrame.of_fs_eq hfs), hfs, hpost⟩⟩
  · exact False.elim (not_satisfies_false_sepConj hoom)

theorem sepWP_with_vm_fs_oom {P : Program} {b : BitVec 64} {Hk : String → Option (State → State)}
    {mid : BitVec 64} {s : State} {Pre : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWP ((P.rebase b trapHooks).withSvc noSyscalls) mid s Pre
      (fun sm Pm => sm.tpidrEl0 = s.tpidrEl0 ∧ (VmPreserved s sm → sm.fs = s.fs → post sm Pm))) :
    SepWP (P.rebase b Hk) mid s Pre post oom := by
  refine SepWP.of_reaches_pc fun R hm hL => ?_
  obtain ⟨sm, hsteps, ⟨hpc, hrun, Pm, hPm, hvm, hfs, hp⟩ | ⟨_, hoom⟩⟩ :=
    SepWP.to_reaches_pc (sepWP_rebase_vmPreserved_fs (Hk := Hk) h) hm hL
  · exact ⟨sm, hsteps, Or.inl ⟨hpc, hrun, Pm, hPm, hp hvm hfs⟩⟩
  · exact False.elim (not_satisfies_false_sepConj hoom)

scoped syntax "by_vm_fs_open " tacticSeq : tactic
scoped elab_rules : tactic
  | `(tactic| by_vm_fs_open $tac:tacticSeq) => do
    Lean.Elab.Tactic.evalTactic (← `(tactic| apply sepWP_with_vm_fs_oom))
    let g ← Lean.Elab.Tactic.getMainGoal
    g.withContext do
      let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData
      let e2 := ty.getArg! 0
      let e1 := e2.getArg! 0
      let ty1 := Lean.mkAppN ty.getAppFn #[e1, ty.getArg! 1, ty.getArg! 2, ty.getArg! 3, ty.getArg! 4, ty.getArg! 5]
      let g1 ← Lean.Meta.mkFreshExprMVar ty1
      let savedGoals ← Lean.Elab.Tactic.getGoals
      Lean.Elab.Tactic.setGoals [g1.mvarId!]
      Lean.Elab.Tactic.evalTactic (← `(tactic| ($tac)))
      let rem ← Lean.Elab.Tactic.getGoals
      unless rem.isEmpty do
        throwError "by_vm_fs_open: inner tactic left {rem.length} unsolved goal(s)"
      Lean.Elab.Tactic.setGoals savedGoals.tail!
      let prf1 ← Lean.instantiateMVars g1
      let prf2 := prf1.replace fun sub =>
        if sub.eqv e2 then some e2 else if sub.eqv e1 then some e2 else none
      g.assign prf2

theorem r1b_call_withFds_placed [LibsignalPlacement] {α : Type} {H : LibsignalHooks}
    {callee ret_pc ret : BitVec 64} {spec : Spec α} {g : RunCall} {s0 s : State}
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    {oom : State → SepProp}
    (x : α)
    (hcall : subroutine_ok (runProgPlaced H) callee
      (withLsCodeRoLoaded lsmpl (withFdsGe3Closed spec)))
    (hfd : FdsGe3Closed s.fs)
    (hinv : r1b_CodeOk s.mem)
    (hpc : s.pc = callee)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpanicK : PanicK g s0 Qp)
    (hP : P ⊢ spec.pre x s ∗ (F ∗ emp))
    (hpanic : ∀ sf R', sf.status = .Panicked →
      (sf.mem ⊨ spec.onPanic x s sf ∗ R') →
      runPanicProp g s0 sf := by
      intro _ _ _ hp; exact (not_satisfies_false_sepConj hp).elim)
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False := by
      intro _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by
      intro _ _ _ ho; exact (not_satisfies_false_sepConj ho).elim)
    (hnext : ∀ sf : State,
      Steps (runProgPlaced H) s sf →
      r1b_CodeOk sf.mem →
      FdsGe3Closed sf.fs →
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s.sp →
      CalleeSavedPreserved s sf →
      SepWPp (runProgPlaced H) ret sf (spec.post x s sf ∗ F) Q Qp oom) :
    SepWPp (runProgPlaced H) ret s P Q Qp oom := by
  refine r1b_call_placed x hcall hinv hpc hrun hsp hlr hpanicK ?_ hpanic hexit hoom ?_
  · dsimp only [withFdsGe3Closed]
    rw [sepConj_assoc]
    exact Entails.pure_right hfd hP
  · intro sf hsteps hinv_f hpc_f hrun_f hsp_f hcs_f
    dsimp only [withFdsGe3Closed]
    rw [sepConj_assoc]
    exact SepWPp.pure_elim fun hfd_f =>
      hnext sf hsteps hinv_f hfd_f hpc_f hrun_f hsp_f hcs_f

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CommonPlacedBudgetFd

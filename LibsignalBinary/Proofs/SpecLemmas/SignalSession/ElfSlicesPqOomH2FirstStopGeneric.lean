/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.FsTracedPlaced

/-!
# Generic First-Stop, `CallerLrUnmapped`, `ExecFrozen`, and Scoped `Steps` Lifts

**Checked by Lean.**

Program- and spec-parametric first-stop and trajectory-lifting lemmas for per-hook ghost-to-real
replay:
1. `CallerLrUnmapped`, `lr ∉ keep`, and deterministic first-stop extraction (`h2fsgen_firstStop_*`).
2. `ExecFrozen`, `State.fs`, and `FsTraced IsFsC` preservation up to first stop.
3. `stripS` first-stop eliminators (`h2fsgen_stepsUntil_of_stripS_standard`,
   `h2fsgen_f3CallPre_real_firstStop_of_stripS*`, `h2fsgen_activeRealRun_of_f3CallPre`), supporting
   memory-writing extern hooks (`ProofLib.hookMemcpy`, `Rust.panicked`).
4. Region-scoped (`h2fsgen_StepsVisitedIn`) and region-free (`h2fsgen_HooksUnfetched`) `Steps`
   and `StepsUntil` program lifts.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric

open Arm64 ProofLib ProofLib.SepLogic
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  ActiveRealRun ExecFrozen SpecPreservesFsTrace SpecStripSInvariant
  lr_not_keep_of_caller_bl lr_not_keep_of_eq_entry
  real_subroutine_run_of_stripS satisfies_of_stripExecOutside
  satisfies_stripExecOutside standard_stripS
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks (ActiveF3CallPre)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (CallerLrUnmapped)

/-! ## `CallerLrUnmapped`, `lr ∉ keep`, and First-Stop Extraction -/

/-- Public alias for `ReadFileBudgetPlaced.CallerLrUnmapped`: for every `m` with
    `s0.mem.KeepsFrozen m`, `P_io.fetchMem m (s0.readReg64 .lr) = none` and
    `P_io.externAt? (s0.readReg64 .lr) = none`. -/
abbrev h2fsgen_CallerLrUnmapped (P_io : Program) (s0 : State) : Prop :=
  CallerLrUnmapped P_io s0

theorem h2fsgen_callerLrUnmapped_iff (P_io : Program) (s0 : State) :
    h2fsgen_CallerLrUnmapped P_io s0 ↔
      ∀ m : Memory, s0.mem.KeepsFrozen m →
        P_io.fetchMem m (s0.readReg64 .lr) = none ∧
        P_io.externAt? (s0.readReg64 .lr) = none :=
  Iff.rfl

private theorem h2fsgen_setPC_mem (s : State) (pc : BitVec 64) :
    (s.setPC pc).mem = s.mem := by
  cases s; rfl

private theorem h2fsgen_setPC_fs (s : State) (pc : BitVec 64) :
    (s.setPC pc).fs = s.fs := by
  cases s; rfl

private theorem h2fsgen_setPC_trace (s : State) (pc : BitVec 64) :
    (s.setPC pc).trace = s.trace := by
  cases s; rfl

private theorem h2fsgen_setPC_status (s : State) (pc : BitVec 64) :
    (s.setPC pc).status = s.status := by
  cases s; rfl

private theorem h2fsgen_setPC_spAligned (s : State) (pc : BitVec 64) :
    (s.setPC pc).spAligned = s.spAligned := by
  cases s; rfl

private theorem h2fsgen_setPC_pc (s : State) (pc : BitVec 64) :
    (s.setPC pc).pc = pc := by
  cases s; rfl

private theorem h2fsgen_step_status_running {P : Program} {s1 s2 : State}
    (h : Step P s1 s2) : s1.status = .Running := by
  cases h <;> assumption

private theorem h2fsgen_steps_eq_of_not_running {P : Program} {s1 s2 : State}
    (hnr : s1.status ≠ .Running) (h : Steps P s1 s2) : s1 = s2 := by
  cases h with
  | refl => rfl
  | step h1 _ => exact absurd (h2fsgen_step_status_running h1) hnr

private theorem h2fsgen_strip_perm_frozen {keep : BitVec 64 → Bool} {m : Memory}
    (hfr : ExecFrozen m) (a : BitVec 64) :
    ((stripExecOutside keep m).perm a).frozen = (m.perm a).frozen := by
  rw [strip_perm]
  have hfr_a := hfr a
  cases hp : m.perm a with
  | none => rfl
  | some p =>
    rw [hp] at hfr_a
    rcases p with ⟨r, w, x, lf, an⟩
    unfold stripPerm Option.frozen Perm.frozen
    cases keep a <;> cases r <;> cases w <;> cases x <;>
      simp_all [Option.map, Option.x, Option.r, Option.w]

/-- Establish `CallerLrUnmapped P_io s0` whenever `lr` is frozen and non-executable in `s0.mem`
    and not an extern entry of `P_io`. -/
theorem h2fsgen_callerLrUnmapped_of_frozen_not_exec {P_io : Program} {s0 : State}
    (hfr_lr : s0.mem.Frozen (s0.readReg64 .lr))
    (hnx_lr : (s0.mem.perm (s0.readReg64 .lr)).x = false)
    (hext_lr : P_io.externAt? (s0.readReg64 .lr) = none) :
    CallerLrUnmapped P_io s0 := by
  intro m hkf
  refine ⟨?_, hext_lr⟩
  have hperm : m.perm (s0.readReg64 .lr) = s0.mem.perm (s0.readReg64 .lr) :=
    (hkf (s0.readReg64 .lr) hfr_lr).2.1
  have hnx : (m.perm (s0.readReg64 .lr)).x = false := hperm ▸ hnx_lr
  have hce : m.canExec (s0.readReg64 .lr) 4 = false := by
    simp [Memory.canExec, Memory.allPerm, hnx]
  simp [Program.fetchMem, hext_lr, hce]

/-- Under `ExecFrozen s0.mem`, if `lr` is frozen in `s0.mem` (e.g. caller `.text`), `keep lr = false`,
    and `P_io.externAt? lr = none`, then `CallerLrUnmapped P_io (stripS keep s0)` holds. -/
theorem h2fsgen_callerLrUnmapped_stripS_of_frozen {keep : BitVec 64 → Bool}
    {P_io : Program} {s0 : State}
    (hFr : ExecFrozen s0.mem)
    (hfr_lr : s0.mem.Frozen (s0.readReg64 .lr))
    (hlr_out : keep (s0.readReg64 .lr) = false)
    (hext_lr : P_io.externAt? (s0.readReg64 .lr) = none) :
    CallerLrUnmapped P_io (stripS keep s0) := by
  have hlr_reg : (stripS keep s0).readReg64 .lr = s0.readReg64 .lr := by
    cases s0; rfl
  have hmem_eq : (stripS keep s0).mem = stripExecOutside keep s0.mem := by
    cases s0; rfl
  apply h2fsgen_callerLrUnmapped_of_frozen_not_exec
  · rw [hlr_reg, hmem_eq]
    unfold Memory.Frozen at hfr_lr ⊢
    rwa [h2fsgen_strip_perm_frozen hFr]
  · rw [hlr_reg, hmem_eq, strip_perm, hlr_out]
    cases s0.mem.perm (s0.readReg64 .lr) with
    | none => rfl
    | some p =>
      rcases p with ⟨r, w, x, lf, an⟩
      cases x <;> rfl
  · rwa [hlr_reg]

/-- Public re-export of `AllocGhostLinkTransfer.lr_not_keep_of_caller_bl`: at any `BL` call site
    whose next PC `s_call.pc + 4` lies outside `keep`, the callee entry state has `keep lr = false`. -/
theorem h2fsgen_lr_not_keep_of_caller_bl {keep : BitVec 64 → Bool}
    {s_call : State} {off : BitVec 64}
    (hNextOut : keep (s_call.pc + 4#64) = false) :
    keep ((execInst (.bl off) s_call).readReg64 .lr) = false :=
  lr_not_keep_of_caller_bl hNextOut

/-- Public re-export of `AllocGhostLinkTransfer.lr_not_keep_of_eq_entry`: tail calls preserving `lr`
    preserve `keep lr = false`. -/
theorem h2fsgen_lr_not_keep_of_eq_entry {keep : BitVec 64 → Bool} {s0 u : State}
    (hlr_eq : u.readReg64 .lr = s0.readReg64 .lr)
    (hlr0 : keep (s0.readReg64 .lr) = false) :
    keep (u.readReg64 .lr) = false :=
  lr_not_keep_of_eq_entry hlr_eq hlr0

/-- Extract the deterministic **first** state satisfying `stop` along any `Steps P s sf_end` run
    whose endpoint `sf_end` satisfies `stop`. -/
theorem h2fsgen_firstStop_of_steps {P : Program} {stop : State → Prop} {s sf_end : State}
    (hsteps : Steps P s sf_end) (hstop : stop sf_end) :
    ∃ sf, StepsUntil P stop s sf ∧ stop sf ∧ Steps P sf sf_end :=
  hsteps.toStepsUntil hstop

/-- Generalized public `firstStop_eq_of_callerLrUnmapped` accepting any `SubroutineStop s0 sf`
    endpoint (`Returned`, `.Panicked`, `.Exited`, or `.OutOfMemory`): under `CallerLrUnmapped P_io s0`,
    `sf` itself is the unique **first** `SubroutineStop s0` state along `hsteps`. -/
theorem h2fsgen_firstStop_eq_of_callerLrUnmapped_stop {P_io : Program} {entry_io : BitVec 64}
    {s0 sf : State}
    (hsteps : Steps P_io (s0.setPC entry_io) sf)
    (hstop : SubroutineStop s0 sf)
    (hLr : CallerLrUnmapped P_io s0) :
    StepsUntil P_io (SubroutineStop s0) (s0.setPC entry_io) sf ∧ SubroutineStop s0 sf := by
  obtain ⟨sm, huntil, hstop_m, hrest⟩ :=
    hsteps.toStepsUntil (stop := SubroutineStop s0) hstop
  have hkf_m : s0.mem.KeepsFrozen sm.mem := by
    simpa only [h2fsgen_setPC_mem] using huntil.toSteps.keepsFrozen
  have hsm_eq : sm = sf := by
    rcases hstop_m with hret_m | hpan_m | ⟨code, hex_m⟩ | hoom_m
    · cases hrest with
      | refl => rfl
      | @step _ s2 _ h1 h2 =>
        obtain ⟨hfetch_none, hext_none⟩ := hLr sm.mem hkf_m
        rw [← hret_m.1] at hfetch_none hext_none
        cases h1 with
        | exec _ hfetch => rw [hfetch_none] at hfetch; cases hfetch
        | halt_unmapped _ _ _ =>
          have hs2_eq : { sm with status := .Halted } = sf :=
            h2fsgen_steps_eq_of_not_running (by simp) h2
          have hsf_halt : sf.status = .Halted := hs2_eq ▸ rfl
          rcases hstop with ⟨_, _, hr_sf⟩ | hpan_sf | ⟨_, hex_sf⟩ | hoom_sf
          · rw [hr_sf] at hsf_halt; cases hsf_halt
          · rw [hpan_sf] at hsf_halt; cases hsf_halt
          · rw [hex_sf] at hsf_halt; cases hsf_halt
          · rw [hoom_sf] at hsf_halt; cases hsf_halt
        | extern _ hext => rw [hext_none] at hext; cases hext
        | extern_fault _ hext => rw [hext_none] at hext; cases hext
    · exact h2fsgen_steps_eq_of_not_running (by rw [hpan_m]; exact ExecStatus.noConfusion) hrest
    · exact h2fsgen_steps_eq_of_not_running (by rw [hex_m]; exact ExecStatus.noConfusion) hrest
    · exact h2fsgen_steps_eq_of_not_running (by rw [hoom_m]; exact ExecStatus.noConfusion) hrest
  subst hsm_eq
  exact ⟨huntil, hstop⟩

/-- Under `CallerLrUnmapped P_io s0`, a `Returned s0 sf` endpoint of
`Steps P_io (s0.setPC entry_io) sf` is the first `SubroutineStop s0` state. -/
theorem h2fsgen_firstStop_eq_of_callerLrUnmapped {P_io : Program} {entry_io : BitVec 64}
    {s0 sf : State}
    (hsteps : Steps P_io (s0.setPC entry_io) sf)
    (hret : Returned s0 sf)
    (hLr : CallerLrUnmapped P_io s0) :
    StepsUntil P_io (SubroutineStop s0) (s0.setPC entry_io) sf ∧ SubroutineStop s0 sf :=
  h2fsgen_firstStop_eq_of_callerLrUnmapped_stop hsteps (Or.inl hret) hLr

private theorem h2fsgen_subroutineOutcome_to_stop {α : Type} {spec : Spec α} {x : α} {R : SepProp}
    {s0 sf : State} (h : SubroutineOutcome spec x R s0 sf) : SubroutineStop s0 sf := by
  rcases h with ⟨hret, _, _⟩ | ⟨hp, _⟩ | ⟨c, he, _⟩ | ⟨ho, _⟩
  · exact Or.inl hret
  · exact Or.inr (Or.inl hp)
  · exact Or.inr (Or.inr (Or.inl ⟨c, he⟩))
  · exact Or.inr (Or.inr (Or.inr ho))

private theorem h2fsgen_subroutineOutcome_not_halted {α : Type} {spec : Spec α} {x : α} {R : SepProp}
    {s0 sf : State} (h : SubroutineOutcome spec x R s0 sf) : sf.status ≠ .Halted := by
  rcases h with ⟨⟨_, _, hr⟩, _, _⟩ | ⟨hp, _⟩ | ⟨_, he, _⟩ | ⟨ho, _⟩
  · rw [hr]; decide
  · rw [hp]; decide
  · rw [he]; nofun
  · rw [ho]; decide

/-- Generic first-stop extraction from a `subroutine_ok` run under `CallerLrUnmapped P s0`
    (eliminates `subroutine_ok` via `subroutine_ok_elim_steps_outcome` and upgrades `Steps` to
    `StepsUntil P (SubroutineStop s0)`). -/
theorem h2fsgen_subroutine_ok_elim_firstStop_of_callerLrUnmapped {α : Type}
    {P : Program} {entry : BitVec 64} {spec : Spec α}
    (hOk : subroutine_ok P entry spec)
    (hPrePC : ∀ x (s : State) (pc : BitVec 64), spec.pre x (s.setPC pc) = spec.pre x s)
    (hOutPC : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome spec x R (s0.setPC pc) sf → SubroutineOutcome spec x R s0 sf)
    {x : α} {R : SepProp} {s0 : State}
    (hRun : s0.status = .Running)
    (hSp : s0.spAligned = true)
    (hPre : s0.mem ⊨ spec.pre x s0 ∗ R)
    (hCode : P.CodeLoaded s0.mem)
    (hLr : CallerLrUnmapped P s0) :
    ∃ sf : State,
      StepsUntil P (SubroutineStop s0) (s0.setPC entry) sf ∧
      SubroutineStop s0 sf ∧
      SubroutineOutcome spec x R s0 sf := by
  let s1 := s0.setPC entry
  have hs1_pre : s1.mem ⊨ spec.pre x s1 ∗ R := by
    dsimp only [s1]
    rw [h2fsgen_setPC_mem, hPrePC x s0 entry]
    exact hPre
  obtain ⟨sf, hsteps, hout1⟩ :=
    subroutine_ok_elim_steps_outcome hOk x R s1
      (h2fsgen_setPC_pc s0 entry)
      (by simpa only [s1, h2fsgen_setPC_status] using hRun)
      hs1_pre
      (by simpa only [s1, h2fsgen_setPC_spAligned] using hSp)
      (by simpa only [s1, h2fsgen_setPC_mem] using hCode)
  have hout0 : SubroutineOutcome spec x R s0 sf := hOutPC x R s0 sf entry hout1
  have hstop0 : SubroutineStop s0 sf := h2fsgen_subroutineOutcome_to_stop hout0
  obtain ⟨huntil, _⟩ := h2fsgen_firstStop_eq_of_callerLrUnmapped_stop hsteps hstop0 hLr
  exact ⟨sf, huntil, hstop0, hout0⟩

/-! ## `ExecFrozen`, `State.fs`, and `FsTraced IsFsC` Invariance up to First Stop -/

/-- Single-step `ExecFrozen` preservation along `Step P s s'` when `P.svc = Syscall.standard`
    and every active extern hook of `P` preserves `ExecFrozen` on valid `Step.extern` transitions. -/
theorem h2fsgen_step_preserves_execFrozen {P : Program}
    (hsvc : P.svc = Syscall.standard)
    (hext : ∀ (pc : BitVec 64) (f : State → State),
      P.externAt? pc = some f →
      ∀ st : State, st.status = .Running → ExecFrozen st.mem →
        st.mem.KeepsFrozen (f st).mem → (f st).symtab = st.symtab →
        ExecFrozen (f st).mem)
    {s s' : State}
    (hstep : Step P s s')
    (hfr : ExecFrozen s.mem) :
    ExecFrozen s'.mem := by
  cases hstep with
  | @exec inst _ _ =>
    by_cases hsvc0 : inst.isSvc0 = true
    · have hinst : inst = .system false 0#16 := by
        cases inst <;> simp [Instr.isSvc0] at hsvc0
        rcases hsvc0 with ⟨rfl, rfl⟩; rfl
      subst hinst
      have hev : P.evalInst (.system false 0#16) s = Syscall.standard s := by
        simp [Program.evalInst, execInstWithSvc, hsvc]
      rw [hev]
      exact (standard_stripS (keep := fun _ => false) hfr).2
    · have hnsvc0 : inst.isSvc0 = false := Bool.eq_false_iff.mpr hsvc0
      rw [evalInst_eq_execInst_of_not_isSvc0 hnsvc0 s]
      have hpf := ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 s
      exact ExecFrozen.of_perm_eq hfr (congrFun hpf.2.1)
  | halt_unmapped _ _ _ =>
    exact hfr
  | extern hrun he hkf hsym =>
    exact hext _ _ he _ hrun hfr hkf hsym
  | extern_fault _ _ _ =>
    exact hfr

/-- Multi-step `ExecFrozen` preservation along `Steps P s0 sf`. -/
theorem h2fsgen_steps_preserves_execFrozen {P : Program}
    (hsvc : P.svc = Syscall.standard)
    (hext : ∀ (pc : BitVec 64) (f : State → State),
      P.externAt? pc = some f →
      ∀ st : State, st.status = .Running → ExecFrozen st.mem →
        st.mem.KeepsFrozen (f st).mem → (f st).symtab = st.symtab →
        ExecFrozen (f st).mem)
    {s0 sf : State}
    (hsteps : Steps P s0 sf)
    (hfr0 : ExecFrozen s0.mem) :
    ExecFrozen sf.mem := by
  induction hsteps with
  | refl _ => exact hfr0
  | step h1 _ ih => exact ih (h2fsgen_step_preserves_execFrozen hsvc hext h1 hfr0)

/-- First-stop `ExecFrozen` preservation along `StepsUntil P stop s0 sf`. -/
theorem h2fsgen_stepsUntil_preserves_execFrozen {P : Program} {stop : State → Prop}
    (hsvc : P.svc = Syscall.standard)
    (hext : ∀ (pc : BitVec 64) (f : State → State),
      P.externAt? pc = some f →
      ∀ st : State, st.status = .Running → ExecFrozen st.mem →
        st.mem.KeepsFrozen (f st).mem → (f st).symtab = st.symtab →
        ExecFrozen (f st).mem)
    {s0 sf : State}
    (huntil : StepsUntil P stop s0 sf)
    (hfr0 : ExecFrozen s0.mem) :
    ExecFrozen sf.mem :=
  h2fsgen_steps_preserves_execFrozen hsvc hext huntil.toSteps hfr0

/-- `FsTraced IsFsC s0 sf` along any `StepsUntil P stop (s0.setPC entry) sf` run when
    `P.svc = Syscall.standard` and every extern hook of `P` satisfies `HookFsTraced IsFsC`. -/
theorem h2fsgen_stepsUntil_fsTraced {P : Program} {stop : State → Prop}
    {entry : BitVec 64} {s0 sf : State}
    (hsvc : P.svc = Syscall.standard)
    (hext_fsT : ∀ pc f, P.externAt? pc = some f → HookFsTraced IsFsC f)
    (huntil : StepsUntil P stop (s0.setPC entry) sf) :
    FsTraced IsFsC s0 sf := by
  have h0 : FsTraced IsFsC s0 (s0.setPC entry) := by
    cases s0; exact FsTraced.of_eq rfl rfl
  have htr : FsTraced IsFsC (s0.setPC entry) sf :=
    huntil.toSteps.fsTraced (isFs := IsFsC) (fun _ he => he) hext_fsT hsvc
  exact h0.trans htr

/-- Combined direct-program `subroutine_ok` first-stop + `ExecFrozen` + `fs` / `FsTraced IsFsC`
    eliminator under `CallerLrUnmapped P s0` (usable directly for unstripped compiled subroutines
    such as `read_file` / `read_stdin`). -/
theorem h2fsgen_subroutine_ok_firstStop_execFrozen_fs {α : Type}
    {P : Program} {entry : BitVec 64} {spec : Spec α}
    (hsvc : P.svc = Syscall.standard)
    (hext_fr : ∀ (pc : BitVec 64) (f : State → State),
      P.externAt? pc = some f →
      ∀ st : State, st.status = .Running → ExecFrozen st.mem →
        st.mem.KeepsFrozen (f st).mem → (f st).symtab = st.symtab →
        ExecFrozen (f st).mem)
    (hOk : subroutine_ok P entry spec)
    (hFsT : SpecPreservesFsTrace spec)
    (hPrePC : ∀ x (s : State) (pc : BitVec 64), spec.pre x (s.setPC pc) = spec.pre x s)
    (hOutPC : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome spec x R (s0.setPC pc) sf → SubroutineOutcome spec x R s0 sf)
    {x : α} {R : SepProp} {s0 : State}
    (hRun : s0.status = .Running)
    (hSp : s0.spAligned = true)
    (hPre : s0.mem ⊨ spec.pre x s0 ∗ R)
    (hFr : ExecFrozen s0.mem)
    (hCode : P.CodeLoaded s0.mem)
    (hLr : CallerLrUnmapped P s0) :
    ∃ sf : State,
      StepsUntil P (SubroutineStop s0) (s0.setPC entry) sf ∧
      SubroutineStop s0 sf ∧
      SubroutineOutcome spec x R s0 sf ∧
      sf.fs = s0.fs ∧
      FsTraced IsFsC s0 sf ∧
      ExecFrozen sf.mem := by
  obtain ⟨sf, huntil, hstop, hout⟩ :=
    h2fsgen_subroutine_ok_elim_firstStop_of_callerLrUnmapped hOk hPrePC hOutPC
      hRun hSp hPre hCode hLr
  obtain ⟨hfs, hfst⟩ := hFsT x R s0 sf hout
  have hfr_sf : ExecFrozen sf.mem :=
    h2fsgen_stepsUntil_preserves_execFrozen hsvc hext_fr huntil
      (by simpa only [h2fsgen_setPC_mem] using hFr)
  exact ⟨sf, huntil, hstop, hout, hfs, hfst, hfr_sf⟩

/-! ## `stripS` First-Stop Lift and `hookMemcpy` / `Rust.panicked` Commutation -/

private theorem h2fsgen_perm_write8 (m : Memory) (addr : BitVec 64) (val : BitVec 8)
    (a : BitVec 64) :
    (m.write8 addr val).perm a = m.perm a := by
  unfold Memory.write8 Memory.perm Memory.rawPerm
  dsimp only
  by_cases ha : a = addr
  · subst ha
    simp only [↓reduceIte]
    cases m.cells a with
    | none => rfl
    | some cb =>
      rcases cb with ⟨_ | p, b⟩
      · rfl
      · rcases p with ⟨r, w, x, lf, an⟩; rfl
  · simp only [ha, ↓reduceIte]

private theorem h2fsgen_perm_writeBytes :
    ∀ (m : Memory) (base : BitVec 64) (bs : List (BitVec 8)) (a : BitVec 64),
      (m.writeBytes base bs).perm a = m.perm a
  | _, _, [], _ => rfl
  | m, base, b :: rest, a => by
    simp only [Memory.writeBytes]
    rw [h2fsgen_perm_writeBytes (m.write8 base b) (base + 1#64) rest a,
      h2fsgen_perm_write8 m base b a]

private theorem h2fsgen_execFrozen_writeBytes {m : Memory} (hfr : ExecFrozen m)
    (base : BitVec 64) (bs : List (BitVec 8)) :
    ExecFrozen (m.writeBytes base bs) :=
  ExecFrozen.of_perm_eq hfr (h2fsgen_perm_writeBytes m base bs)

private theorem h2fsgen_strip_readBytes (keep : BitVec 64 → Bool) (m : Memory) :
    ∀ (a : BitVec 64) (n : Nat),
      (stripExecOutside keep m).readBytes a n = m.readBytes a n
  | _, 0 => rfl
  | a, n + 1 => by
    simp only [Memory.readBytes, strip_read8, h2fsgen_strip_readBytes keep m (a + 1#64) n]

private theorem h2fsgen_strip_writeBytes (keep : BitVec 64 → Bool) :
    ∀ (m : Memory) (base : BitVec 64) (bs : List (BitVec 8)),
      (stripExecOutside keep m).writeBytes base bs = stripExecOutside keep (m.writeBytes base bs)
  | _, _, [] => rfl
  | m, base, b :: rest => by
    simp only [Memory.writeBytes, strip_write8,
      h2fsgen_strip_writeBytes keep (m.write8 base b) _ rest]

/-- Recover `m.KeepsFrozen m'` from `(stripExecOutside keep m).KeepsFrozen (stripExecOutside keep m')`
    under `ExecFrozen m` whenever `m'` preserves byte permissions (`∀ a, m'.perm a = m.perm a`). -/
theorem h2fsgen_keepsFrozen_of_stripExecOutside_perm_eq {keep : BitVec 64 → Bool}
    {m m' : Memory}
    (hfr : ExecFrozen m)
    (hkf_strip : (stripExecOutside keep m).KeepsFrozen (stripExecOutside keep m'))
    (hperm : ∀ a, m'.perm a = m.perm a) :
    m.KeepsFrozen m' := by
  intro a hfa
  have hfa_strip : (stripExecOutside keep m).Frozen a := by
    unfold Memory.Frozen at hfa ⊢
    rwa [h2fsgen_strip_perm_frozen hfr]
  obtain ⟨hr8, _, hlf, han⟩ := hkf_strip a hfa_strip
  simp only [strip_read8, strip_isLazyFree, strip_isAnon] at hr8 hlf han
  exact ⟨hr8, hperm a, hlf, han⟩

/-- `Arm64.Rust.panicked` commutes with `stripS keep` and preserves `ExecFrozen`, `KeepsFrozen`,
    `symtab`, `State.fs`, and `FsTraced IsFsC`. -/
theorem h2fsgen_rustPanicked_comm_stripS (keep : BitVec 64 → Bool) (st : State)
    (hfr : ExecFrozen st.mem) :
    Rust.panicked (stripS keep st) = stripS keep (Rust.panicked st) ∧
    ExecFrozen (Rust.panicked st).mem ∧
    st.mem.KeepsFrozen (Rust.panicked st).mem ∧
    (Rust.panicked st).symtab = st.symtab ∧
    (Rust.panicked st).fs = st.fs ∧
    FsTraced IsFsC st (Rust.panicked st) := by
  refine ⟨by cases st; rfl, hfr, fun _ _ => ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, ?_⟩
  exact FsTraced.of_eq rfl rfl

/-- `ProofLib.hookMemcpy` commutes with `stripS keep`, preserves `ExecFrozen`, `symtab`, `State.fs`,
    and `FsTraced IsFsC`, and lifts `KeepsFrozen` from `stripS keep st` to `st`. -/
theorem h2fsgen_hookMemcpy_comm_stripS (keep : BitVec 64 → Bool) (st : State)
    (hfr : ExecFrozen st.mem)
    (hkf_strip : (stripS keep st).mem.KeepsFrozen (ProofLib.hookMemcpy (stripS keep st)).mem) :
    ProofLib.hookMemcpy (stripS keep st) = stripS keep (ProofLib.hookMemcpy st) ∧
    ExecFrozen (ProofLib.hookMemcpy st).mem ∧
    st.mem.KeepsFrozen (ProofLib.hookMemcpy st).mem ∧
    (ProofLib.hookMemcpy st).symtab = st.symtab ∧
    (ProofLib.hookMemcpy st).fs = st.fs ∧
    FsTraced IsFsC st (ProofLib.hookMemcpy st) := by
  have hcomm : ProofLib.hookMemcpy (stripS keep st) = stripS keep (ProofLib.hookMemcpy st) := by
    cases st with
    | mk regs sp pc pstate status mem brkStart brk physMemAvail symtab trace fs oracle oracleIdx =>
      dsimp only [ProofLib.hookMemcpy, ProofLib.retHook, stripS,
        State.readReg64, State.setMem, State.setPC]
      rw [h2fsgen_strip_readBytes, h2fsgen_strip_writeBytes]
  have hmem_eq :
      (ProofLib.hookMemcpy st).mem =
        st.mem.writeBytes (st.readReg64 .x0)
          (st.mem.readBytes (st.readReg64 .x1) (st.readReg64 .x2).toNat) := by
    cases st; rfl
  have hfr' : ExecFrozen (ProofLib.hookMemcpy st).mem := by
    rw [hmem_eq]
    exact h2fsgen_execFrozen_writeBytes hfr _ _
  have hkf : st.mem.KeepsFrozen (ProofLib.hookMemcpy st).mem := by
    rw [hcomm] at hkf_strip
    have hsm1 : (stripS keep st).mem = stripExecOutside keep st.mem := by cases st; rfl
    have hsm2 : (stripS keep (ProofLib.hookMemcpy st)).mem =
        stripExecOutside keep (ProofLib.hookMemcpy st).mem := by
      cases st; rfl
    rw [hsm1, hsm2] at hkf_strip
    exact h2fsgen_keepsFrozen_of_stripExecOutside_perm_eq hfr hkf_strip fun a => by
      rw [hmem_eq]
      exact h2fsgen_perm_writeBytes _ _ _ a
  have hsym : (ProofLib.hookMemcpy st).symtab = st.symtab := by cases st; rfl
  have hfs : (ProofLib.hookMemcpy st).fs = st.fs := by cases st; rfl
  have hfst : FsTraced IsFsC st (ProofLib.hookMemcpy st) := by
    cases st; exact FsTraced.of_eq rfl rfl
  exact ⟨hcomm, hfr', hkf, hsym, hfs, hfst⟩

private theorem h2fsgen_stripS_mem (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).mem = stripExecOutside keep s.mem := by cases s; rfl
private theorem h2fsgen_stripS_pc (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).pc = s.pc := by cases s; rfl
private theorem h2fsgen_stripS_sp (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).sp = s.sp := by cases s; rfl
private theorem h2fsgen_stripS_status (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).status = s.status := by cases s; rfl
private theorem h2fsgen_strip_read32 (keep : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) :
    (stripExecOutside keep m).read32 a = m.read32 a := by
  simp [Memory.read32, strip_read8]

private theorem h2fsgen_subroutineStop_stripS_iff {keep : BitVec 64 → Bool} {s0 s : State} :
    SubroutineStop s0 (stripS keep s) ↔ SubroutineStop s0 s := by
  simp [SubroutineStop, Returned, h2fsgen_stripS_pc, h2fsgen_stripS_sp, h2fsgen_stripS_status]

private theorem h2fsgen_steps_preserves_halted {P : Program} {u v : State}
    (hs : Steps P u v) (hu : u.status = .Halted) : v.status = .Halted := by
  induction hs with
  | refl => exact hu
  | step hs1 _ ihs => cases hs1 <;> simp_all

private theorem h2fsgen_steps_preserves_exception {P : Program} {u v : State} {msg : String}
    (hs : Steps P u v) (hu : u.status = .Exception msg) : v.status = .Exception msg := by
  induction hs with
  | refl => exact hu
  | step hs1 _ ihs => cases hs1 <;> simp_all

/-- Strengthened `stepsUntil_of_stripS_standard`: lifts `Steps P_sub s1' sf'` from
    `s1' = stripS keep s1` to a first-stop `StepsUntil P_real (SubroutineStop s0) s1 sf` while
    passing `Step.extern`'s `(stripS keep st).mem.KeepsFrozen (f (stripS keep st)).mem` and
    `(f (stripS keep st)).symtab = (stripS keep st).symtab` witnesses into `hext_comm` (allowing
    memory-writing extern hooks such as `ProofLib.hookMemcpy`). -/
theorem h2fsgen_stepsUntil_of_stripS_standard
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {s0 : State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hext_comm : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f →
      P_real.externAt? pc = some f ∧
      pc ≠ s0.readReg64 .lr ∧
      (∀ st : State, ExecFrozen st.mem →
        (stripS keep st).mem.KeepsFrozen (f (stripS keep st)).mem →
        (f (stripS keep st)).symtab = (stripS keep st).symtab →
        f (stripS keep st) = stripS keep (f st) ∧
        ExecFrozen (f st).mem ∧
        st.mem.KeepsFrozen (f st).mem ∧
        (f st).symtab = st.symtab))
    (hlr_out : keep (s0.readReg64 .lr) = false)
    {s1' sf' : State}
    (hsteps : Steps P_sub s1' sf')
    (hstop' : SubroutineStop s0 sf')
    (hnhalt' : sf'.status ≠ .Halted) :
    ∀ s1 : State,
      s1' = stripS keep s1 →
      ExecFrozen s1.mem →
      ∃ sf : State,
        StepsUntil P_real (SubroutineStop s0) s1 sf ∧
        SubroutineStop s0 sf ∧
        sf' = stripS keep sf ∧
        ExecFrozen sf.mem := by
  induction hsteps with
  | refl s' =>
    intro s1 hs1 hfr1
    have hstop1 : SubroutineStop s0 s1 :=
      h2fsgen_subroutineStop_stripS_iff.mp (hs1 ▸ hstop')
    exact ⟨s1, StepsUntil.refl s1, hstop1, hs1, hfr1⟩
  | @step sa' sb' sc' h1 hrest ih =>
    intro sa hsa hfra
    by_cases hstop_sa : SubroutineStop s0 sa
    · rcases hstop_sa with ⟨hpc_lr, _⟩ | hpan | ⟨_, hex⟩ | hoom
      · cases h1 with
        | @exec inst hr' hfm' =>
          rw [hsa, h2fsgen_stripS_pc, h2fsgen_stripS_mem] at hfm'
          unfold Program.fetchMem at hfm'
          cases he : P_sub.externAt? sa.pc with
          | some f => simp [he] at hfm'
          | none =>
            simp only [he, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hfm'
            by_cases hal : sa.pc.toNat % 4 = 0
            · simp only [hal, ne_eq, not_true_eq_false, ↓reduceIte] at hfm'
              by_cases hce' : (stripExecOutside keep sa.mem).canExec sa.pc 4 = true
              · have hx0 : ((stripExecOutside keep sa.mem).perm sa.pc).x = true := by
                  have h4 :
                      ((stripExecOutside keep sa.mem).perm sa.pc).x = true ∧
                      ((stripExecOutside keep sa.mem).allPerm (·.x) (sa.pc + 1#64) 3) = true := by
                    simpa [Memory.canExec, Memory.allPerm, Bool.and_eq_true] using hce'
                  exact h4.1
                have hkp := (strip_perm_x_imp hx0).2
                rw [hpc_lr, hlr_out] at hkp
                cases hkp
              · simp [hce'] at hfm'
            · simp [hal] at hfm'
        | halt_unmapped _ _ _ =>
          exact False.elim (hnhalt' (h2fsgen_steps_preserves_halted hrest rfl))
        | extern _ he _ _ =>
          rw [hsa, h2fsgen_stripS_pc] at he
          exact False.elim ((hext_comm sa.pc _ he).2.1 hpc_lr)
        | extern_fault _ he _ =>
          rw [hsa, h2fsgen_stripS_pc] at he
          exact False.elim ((hext_comm sa.pc _ he).2.1 hpc_lr)
      · have hr_sa : sa.status = .Running := by
          have h := h2fsgen_step_status_running h1
          rwa [hsa, h2fsgen_stripS_status] at h
        rw [hpan] at hr_sa; cases hr_sa
      · have hr_sa : sa.status = .Running := by
          have h := h2fsgen_step_status_running h1
          rwa [hsa, h2fsgen_stripS_status] at h
        rw [hex] at hr_sa; cases hr_sa
      · have hr_sa : sa.status = .Running := by
          have h := h2fsgen_step_status_running h1
          rwa [hsa, h2fsgen_stripS_status] at h
        rw [hoom] at hr_sa; cases hr_sa
    · cases h1 with
      | halt_unmapped _ _ _ =>
        exact False.elim (hnhalt' (h2fsgen_steps_preserves_halted hrest rfl))
      | @extern f hr' he' hkf' hsym' =>
        have hra : sa.status = .Running := by
          rw [hsa, h2fsgen_stripS_status] at hr'; exact hr'
        rw [hsa, h2fsgen_stripS_pc] at he'
        rw [hsa] at hkf' hsym'
        obtain ⟨he_real, _, hf_comm⟩ := hext_comm sa.pc f he'
        obtain ⟨hf_eq, hfr_f, hkf_f, hsym_f⟩ := hf_comm sa hfra hkf' hsym'
        have hstep_real : Step P_real sa (f sa) := Step.extern hra he_real hkf_f hsym_f
        rw [hsa, hf_eq] at hrest ih
        obtain ⟨sf, huntil_rest, hstop_sf, hsf_eq, hfr_sf⟩ :=
          ih hstop' hnhalt' (f sa) rfl hfr_f
        exact ⟨sf, StepsUntil.step hstop_sa hstep_real huntil_rest,
          hstop_sf, hsf_eq, hfr_sf⟩
      | extern_fault _ _ _ =>
        have hsf_ex := h2fsgen_steps_preserves_exception hrest rfl
        rcases hstop' with ⟨_, _, hr_sf⟩ | hpan | ⟨_, hex⟩ | hoom
        · rw [hsf_ex] at hr_sf; cases hr_sf
        · rw [hsf_ex] at hpan; cases hpan
        · rw [hsf_ex] at hex; cases hex
        · rw [hsf_ex] at hoom; cases hoom
      | @exec inst hr' hfm' =>
        have hra : sa.status = .Running := by
          rw [hsa, h2fsgen_stripS_status] at hr'; exact hr'
        rw [hsa, h2fsgen_stripS_pc, h2fsgen_stripS_mem] at hfm'
        unfold Program.fetchMem at hfm'
        cases he_sub : P_sub.externAt? sa.pc with
        | some f => simp [he_sub] at hfm'
        | none =>
          simp only [he_sub, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hfm'
          by_cases hal_pc : sa.pc.toNat % 4 = 0
          · simp only [hal_pc, ne_eq, not_true_eq_false, ↓reduceIte] at hfm'
            by_cases hce' : (stripExecOutside keep sa.mem).canExec sa.pc 4 = true
            · simp only [hce', Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hfm'
              have hx4 :
                  ((stripExecOutside keep sa.mem).perm sa.pc).x = true ∧
                  ((stripExecOutside keep sa.mem).perm (sa.pc + 1#64)).x = true ∧
                  ((stripExecOutside keep sa.mem).perm (sa.pc + 2#64)).x = true ∧
                  ((stripExecOutside keep sa.mem).perm (sa.pc + 3#64)).x = true := by
                simpa [Memory.canExec, Memory.allPerm, Bool.and_eq_true, BitVec.add_assoc] using hce'
              obtain ⟨hx0, hkp0⟩ := strip_perm_x_imp hx4.1
              obtain ⟨hx1, _⟩ := strip_perm_x_imp hx4.2.1
              obtain ⟨hx2, _⟩ := strip_perm_x_imp hx4.2.2.1
              obtain ⟨hx3, _⟩ := strip_perm_x_imp hx4.2.2.2
              have hce : sa.mem.canExec sa.pc 4 = true := by
                simp [Memory.canExec, Memory.allPerm, BitVec.add_assoc, hx0, hx1, hx2, hx3]
              rw [h2fsgen_strip_read32] at hfm'
              have hext_real : P_real.externAt? sa.pc = none := hreal_no sa.pc hkp0
              have hfm_real : P_real.fetchMem sa.mem sa.pc = some inst := by
                unfold Program.fetchMem
                simp [hext_real, hal_pc, hce, hfm']
              by_cases hsvc0 : inst.isSvc0 = true
              · have hinst : inst = .system false 0#16 := by
                  cases inst <;> simp [Instr.isSvc0] at hsvc0
                  rcases hsvc0 with ⟨rfl, rfl⟩; rfl
                subst hinst
                obtain ⟨hcomm, hfr_sb⟩ := standard_stripS (keep := keep) hfra
                have hev_strip :
                    P_sub.evalInst (.system false 0#16) (stripS keep sa) =
                      stripS keep (Syscall.standard sa) := by
                  simp [Program.evalInst, execInstWithSvc, hsvc_sub, hcomm]
                have hev_real :
                    P_real.evalInst (.system false 0#16) sa = Syscall.standard sa := by
                  simp [Program.evalInst, execInstWithSvc, hsvc_real]
                have hstep_real : Step P_real sa (Syscall.standard sa) :=
                  hev_real ▸ Step.exec hra hfm_real
                rw [hsa, hev_strip] at hrest ih
                obtain ⟨sf, huntil_rest, hstop_sf, hsf_eq, hfr_sf⟩ :=
                  ih hstop' hnhalt' (Syscall.standard sa) rfl hfr_sb
                exact ⟨sf, StepsUntil.step hstop_sa hstep_real huntil_rest,
                  hstop_sf, hsf_eq, hfr_sf⟩
              · have hnsvc0 : inst.isSvc0 = false := Bool.eq_false_iff.mpr hsvc0
                have hev_strip :
                    P_sub.evalInst inst (stripS keep sa) =
                      stripS keep (execInst inst sa) := by
                  rw [evalInst_eq_execInst_of_not_isSvc0 hnsvc0, execInst_stripS hnsvc0]
                have hev_real : P_real.evalInst inst sa = execInst inst sa :=
                  evalInst_eq_execInst_of_not_isSvc0 hnsvc0 sa
                have hpf := ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 sa
                have hfr_sb : ExecFrozen (execInst inst sa).mem :=
                  ExecFrozen.of_perm_eq hfra (congrFun hpf.2.1)
                have hstep_real : Step P_real sa (execInst inst sa) :=
                  hev_real ▸ Step.exec hra hfm_real
                rw [hsa, hev_strip] at hrest ih
                obtain ⟨sf, huntil_rest, hstop_sf, hsf_eq, hfr_sf⟩ :=
                  ih hstop' hnhalt' (execInst inst sa) rfl hfr_sb
                exact ⟨sf, StepsUntil.step hstop_sa hstep_real huntil_rest,
                  hstop_sf, hsf_eq, hfr_sf⟩
            · simp [hce'] at hfm'
          · simp [hal_pc] at hfm'

/-- Extern-hook generalization of `AllocGhostLinkTransfer.real_subroutine_run_of_stripS`:
    eliminates `subroutine_ok P_sub entryTarget spec` via `subroutine_ok_elim_steps_outcome`
    and lifts across `stripS keep` to a first-stop real execution on `P_real` preserving
    `State.fs`, `FsTraced IsFsC`, and `ExecFrozen`. -/
theorem h2fsgen_real_subroutine_run_of_stripS_ext {α : Type}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64} {spec : Spec α}
    {s0 : State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hext_comm : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f →
      P_real.externAt? pc = some f ∧
      pc ≠ s0.readReg64 .lr ∧
      (∀ st : State, ExecFrozen st.mem →
        (stripS keep st).mem.KeepsFrozen (f (stripS keep st)).mem →
        (f (stripS keep st)).symtab = (stripS keep st).symtab →
        f (stripS keep st) = stripS keep (f st) ∧
        ExecFrozen (f st).mem ∧
        st.mem.KeepsFrozen (f st).mem ∧
        (f st).symtab = st.symtab))
    (hOk : subroutine_ok P_sub entryTarget spec)
    (hInv : SpecStripSInvariant keep spec)
    (hFsT : SpecPreservesFsTrace spec)
    (hPrePC : ∀ x (s : State) (pc : BitVec 64), spec.pre x (s.setPC pc) = spec.pre x s)
    (hOutPC : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome spec x R (s0.setPC pc) sf → SubroutineOutcome spec x R s0 sf)
    {x : α} {R : SepProp}
    (hRun : s0.status = .Running)
    (hSp : s0.spAligned = true)
    (hPre : s0.mem ⊨ spec.pre x s0 ∗ R)
    (hFr : ExecFrozen s0.mem)
    (hlr_out : keep (s0.readReg64 .lr) = false)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep s0.mem)) :
    ∃ sf : State,
      StepsUntil P_real (SubroutineStop s0) (s0.setPC entryTarget) sf ∧
      SubroutineStop s0 sf ∧
      SubroutineOutcome spec x R s0 sf ∧
      sf.fs = s0.fs ∧
      FsTraced IsFsC s0 sf ∧
      ExecFrozen sf.mem := by
  let s1 := s0.setPC entryTarget
  let s1' := stripS keep s1
  have hs1_pre : s1.mem ⊨ spec.pre x s1 ∗ R := by
    change s0.mem ⊨ spec.pre x (s0.setPC entryTarget) ∗ R
    rwa [hPrePC x s0 entryTarget]
  have hs1'_pre : s1'.mem ⊨ spec.pre x s1' ∗ R := by
    have hsat := satisfies_stripExecOutside keep hs1_pre
    rwa [← hInv.pre_eq x s1] at hsat
  have hs1'_sp : s1'.spAligned = true := hSp
  obtain ⟨sf', hsteps', hout'⟩ :=
    subroutine_ok_elim_steps_outcome hOk x R s1' rfl hRun hs1'_pre hs1'_sp hCodeSub
  have hstop1' : SubroutineStop s1' sf' := h2fsgen_subroutineOutcome_to_stop hout'
  have hstop0' : SubroutineStop s0 sf' := hstop1'
  have hnhalt' : sf'.status ≠ .Halted := h2fsgen_subroutineOutcome_not_halted hout'
  obtain ⟨sf, huntil, hstop_sf, hsf_eq, hfr_sf⟩ :=
    h2fsgen_stepsUntil_of_stripS_standard (s0 := s0)
      hsvc_real hsvc_sub hreal_no hext_comm
      hlr_out hsteps' hstop0' hnhalt' s1 rfl hFr
  have hout1 : SubroutineOutcome spec x R s1 sf := by
    rw [hsf_eq] at hout'
    rcases hout' with ⟨hret', hcc', hpost'⟩ | ⟨hp', hpan'⟩ | ⟨c, he', hex'⟩ | ⟨ho', hoom'⟩
    · refine Or.inl ⟨?_, ?_, ?_⟩
      · exact ⟨hret'.1, hret'.2.1, hret'.2.2⟩
      · cases s0; cases sf; exact hcc'
      · rw [hInv.post_eq x s1 sf] at hpost'
        exact satisfies_of_stripExecOutside hfr_sf hpost'
    · refine Or.inr (Or.inl ⟨hp', ?_⟩)
      rw [hInv.onPanic_eq x s1 sf] at hpan'
      exact satisfies_of_stripExecOutside hfr_sf hpan'
    · refine Or.inr (Or.inr (Or.inl ⟨c, he', ?_⟩))
      rw [hInv.onExit_eq x c s1 sf] at hex'
      exact satisfies_of_stripExecOutside hfr_sf hex'
    · refine Or.inr (Or.inr (Or.inr ⟨ho', ?_⟩))
      rw [hInv.onOom_eq x s1 sf] at hoom'
      exact satisfies_of_stripExecOutside hfr_sf hoom'
  have hout0 : SubroutineOutcome spec x R s0 sf := hOutPC x R s0 sf entryTarget hout1
  obtain ⟨hfs, hfst⟩ := hFsT x R s0 sf hout0
  exact ⟨sf, huntil, hstop_sf, hout0, hfs, hfst, hfr_sf⟩

/-- Hook-free `P_sub` first-stop eliminator: from `ActiveF3CallPre specOf s0`,
`keep (s0.readReg64 .lr) = false`, `ExecFrozen s0.mem`, and
`P_sub.CodeLoaded (stripExecOutside keep s0.mem)`, produces a first-stop `P_real` run preserving
`State.fs`, `FsTraced IsFsC`, and `ExecFrozen`. -/
theorem h2fsgen_f3CallPre_real_firstStop_of_stripS {α : Type}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    {specOf : GhostName → BitVec 64 → Spec α} {s0 : State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hOk : ∀ γ tp, subroutine_ok P_sub entryTarget (specOf γ tp))
    (hInv : ∀ γ tp, SpecStripSInvariant keep (specOf γ tp))
    (hFsT : ∀ γ tp, SpecPreservesFsTrace (specOf γ tp))
    (hPrePC : ∀ γ tp x (s : State) (pc : BitVec 64),
      (specOf γ tp).pre x (s.setPC pc) = (specOf γ tp).pre x s)
    (hOutPC : ∀ γ tp x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome (specOf γ tp) x R (s0.setPC pc) sf →
        SubroutineOutcome (specOf γ tp) x R s0 sf)
    (hCallPre : ActiveF3CallPre specOf s0)
    (hlr_out : keep (s0.readReg64 .lr) = false)
    (hFr : ExecFrozen s0.mem)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep s0.mem)) :
    ∃ sf : State,
      StepsUntil P_real (SubroutineStop s0) (s0.setPC entryTarget) sf ∧
      SubroutineStop s0 sf ∧
      sf.fs = s0.fs ∧
      FsTraced IsFsC s0 sf ∧
      ExecFrozen sf.mem := by
  rcases hCallPre with ⟨hRun, hSp, γ, tp, x, R, hPre⟩
  obtain ⟨sf, huntil, hstop, _, hfs, hfst, hfr_sf⟩ :=
    real_subroutine_run_of_stripS hsvc_real hsvc_sub hreal_no hsub_no
      (hOk γ tp) (hInv γ tp) (hFsT γ tp) (hPrePC γ tp) (hOutPC γ tp)
      hRun hSp hPre hFr hlr_out hCodeSub
  exact ⟨sf, huntil, hstop, hfs, hfst, hfr_sf⟩

/-- Direct `ActiveRealRun keep P_real P_sub entryTarget s0` witness from `ActiveF3CallPre specOf s0`
    and `keep (s0.readReg64 .lr) = false` (showing `f3LinkedCallHook`'s fallback branch is dead
    whenever `lr ∉ keep`). -/
theorem h2fsgen_activeRealRun_of_f3CallPre {α : Type}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    {specOf : GhostName → BitVec 64 → Spec α} {s0 : State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hOk : ∀ γ tp, subroutine_ok P_sub entryTarget (specOf γ tp))
    (hInv : ∀ γ tp, SpecStripSInvariant keep (specOf γ tp))
    (hFsT : ∀ γ tp, SpecPreservesFsTrace (specOf γ tp))
    (hPrePC : ∀ γ tp x (s : State) (pc : BitVec 64),
      (specOf γ tp).pre x (s.setPC pc) = (specOf γ tp).pre x s)
    (hOutPC : ∀ γ tp x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome (specOf γ tp) x R (s0.setPC pc) sf →
        SubroutineOutcome (specOf γ tp) x R s0 sf)
    (hCallPre : ActiveF3CallPre specOf s0)
    (hlr_out : keep (s0.readReg64 .lr) = false)
    (hFr : ExecFrozen s0.mem)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep s0.mem)) :
    ActiveRealRun keep P_real P_sub entryTarget s0 :=
  ⟨hFr, hlr_out, hCodeSub,
    h2fsgen_f3CallPre_real_firstStop_of_stripS hsvc_real hsvc_sub hreal_no hsub_no
      hOk hInv hFsT hPrePC hOutPC hCallPre hlr_out hFr hCodeSub⟩

/-- Extern-hook `P_sub` counterpart to `h2fsgen_f3CallPre_real_firstStop_of_stripS`. -/
theorem h2fsgen_f3CallPre_real_firstStop_of_stripS_ext {α : Type}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    {specOf : GhostName → BitVec 64 → Spec α} {s0 : State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hext_comm : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f →
      P_real.externAt? pc = some f ∧
      pc ≠ s0.readReg64 .lr ∧
      (∀ st : State, ExecFrozen st.mem →
        (stripS keep st).mem.KeepsFrozen (f (stripS keep st)).mem →
        (f (stripS keep st)).symtab = (stripS keep st).symtab →
        f (stripS keep st) = stripS keep (f st) ∧
        ExecFrozen (f st).mem ∧
        st.mem.KeepsFrozen (f st).mem ∧
        (f st).symtab = st.symtab))
    (hOk : ∀ γ tp, subroutine_ok P_sub entryTarget (specOf γ tp))
    (hInv : ∀ γ tp, SpecStripSInvariant keep (specOf γ tp))
    (hFsT : ∀ γ tp, SpecPreservesFsTrace (specOf γ tp))
    (hPrePC : ∀ γ tp x (s : State) (pc : BitVec 64),
      (specOf γ tp).pre x (s.setPC pc) = (specOf γ tp).pre x s)
    (hOutPC : ∀ γ tp x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome (specOf γ tp) x R (s0.setPC pc) sf →
        SubroutineOutcome (specOf γ tp) x R s0 sf)
    (hCallPre : ActiveF3CallPre specOf s0)
    (hlr_out : keep (s0.readReg64 .lr) = false)
    (hFr : ExecFrozen s0.mem)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep s0.mem)) :
    ∃ sf : State,
      StepsUntil P_real (SubroutineStop s0) (s0.setPC entryTarget) sf ∧
      SubroutineStop s0 sf ∧
      sf.fs = s0.fs ∧
      FsTraced IsFsC s0 sf ∧
      ExecFrozen sf.mem := by
  rcases hCallPre with ⟨hRun, hSp, γ, tp, x, R, hPre⟩
  obtain ⟨sf, huntil, hstop, _, hfs, hfst, hfr_sf⟩ :=
    h2fsgen_real_subroutine_run_of_stripS_ext hsvc_real hsvc_sub hreal_no hext_comm
      (hOk γ tp) (hInv γ tp) (hFsT γ tp) (hPrePC γ tp) (hOutPC γ tp)
      hRun hSp hPre hFr hlr_out hCodeSub
  exact ⟨sf, huntil, hstop, hfs, hfst, hfr_sf⟩

/-! ## Determinism and Scoped `Steps` Lifts -/

/-- Single-step operational determinism of `Arm64.Step`. -/
theorem h2fsgen_step_det {P : Program} {s s1 s2 : State}
    (h1 : Step P s s1) (h2 : Step P s s2) : s1 = s2 := by
  cases h1 with
  | exec _ hf1 =>
    cases h2 with
    | exec _ hf2 =>
      rw [hf1] at hf2
      injection hf2 with hi
      subst hi; rfl
    | halt_unmapped _ hf2 _ => rw [hf1] at hf2; cases hf2
    | extern _ he2 _ _ => unfold Program.fetchMem at hf1; simp [he2] at hf1
    | extern_fault _ he2 _ => unfold Program.fetchMem at hf1; simp [he2] at hf1
  | halt_unmapped _ hf1 he1 =>
    cases h2 with
    | exec _ hf2 => rw [hf1] at hf2; cases hf2
    | halt_unmapped _ _ _ => rfl
    | extern _ he2 _ _ => rw [he1] at he2; cases he2
    | extern_fault _ he2 _ => rw [he1] at he2; cases he2
  | extern _ he1 hk1 hs1 =>
    cases h2 with
    | exec _ hf2 => unfold Program.fetchMem at hf2; simp [he1] at hf2
    | halt_unmapped _ _ he2 => rw [he1] at he2; cases he2
    | extern _ he2 _ _ =>
      rw [he1] at he2
      injection he2 with hf
      subst hf; rfl
    | extern_fault _ he2 hnk2 =>
      rw [he1] at he2
      injection he2 with hf
      subst hf
      exact absurd ⟨hk1, hs1⟩ hnk2
  | extern_fault _ he1 hnk1 =>
    cases h2 with
    | exec _ hf2 => unfold Program.fetchMem at hf2; simp [he1] at hf2
    | halt_unmapped _ _ he2 => rw [he1] at he2; cases he2
    | extern _ he2 hk2 hs2 =>
      rw [he1] at he2
      injection he2 with hf
      subst hf
      exact absurd ⟨hk2, hs2⟩ hnk1
    | extern_fault _ _ _ => rfl

/-- First-stop determinism of `Arm64.StepsUntil`: two `StepsUntil P stop s` runs both ending in
    `stop` states produce the exact same endpoint (`sf1 = sf2`). -/
theorem h2fsgen_stepsUntil_det {P : Program} {stop : State → Prop} {s sf1 sf2 : State}
    (hu1 : StepsUntil P stop s sf1) (hs1 : stop sf1)
    (hu2 : StepsUntil P stop s sf2) (hs2 : stop sf2) :
    sf1 = sf2 := by
  induction hu1 with
  | refl _ =>
    cases hu2 with
    | refl _ => rfl
    | step hnot2 _ _ => exact absurd hs1 hnot2
  | step hnot1 hst1 _ ih =>
    cases hu2 with
    | refl _ => exact absurd hs2 hnot1
    | step _ hst2 hrest2 =>
      have heq := h2fsgen_step_det hst1 hst2
      subst heq
      exact ih hs1 hrest2

private theorem h2fsgen_evalInst_eq_of_svc_eq {P1 P2 : Program} (hsvc : P1.svc = P2.svc)
    (inst : Instr) (s : State) :
    P1.evalInst inst s = P2.evalInst inst s := by
  by_cases hsvc0 : inst.isSvc0 = true
  · have hinst : inst = .system false 0#16 := by
      cases inst <;> simp [Instr.isSvc0] at hsvc0
      rcases hsvc0 with ⟨rfl, rfl⟩; rfl
    subst hinst
    simp [Program.evalInst, execInstWithSvc, hsvc]
  · have hnsvc0 : inst.isSvc0 = false := Bool.eq_false_iff.mpr hsvc0
    rw [evalInst_eq_execInst_of_not_isSvc0 hnsvc0, evalInst_eq_execInst_of_not_isSvc0 hnsvc0]

/-- `Program.fetchMem` depends on the `Program` only through `externAt?`. -/
theorem h2fsgen_fetchMem_eq_of_externAt_eq {P1 P2 : Program} (m : Memory) (pc : BitVec 64)
    (hext : P2.externAt? pc = P1.externAt? pc) :
    P2.fetchMem m pc = P1.fetchMem m pc := by
  unfold Program.fetchMem
  rw [hext]

/-! ### Inductive `D`-Scoped `Steps` Lift -/

/-- Inductive multi-step execution `s →* sf` on `P1` in which every step actually taken starts at a
    PC with `D s1.pc = true`. Stopping at `.refl sf` places zero constraint on `sf.pc` (avoiding the
    post-`sf` loop bug when `sf.pc = lr ∉ D`, e.g. `D = hole2_keepSub` on `P1 = hole2_emptyProg`). -/
inductive h2fsgen_StepsVisitedIn (D : BitVec 64 → Bool) (P1 : Program) :
    State → State → Prop where
  | refl (s : State) : h2fsgen_StepsVisitedIn D P1 s s
  | step {s1 s2 s3 : State}
      (hd : D s1.pc = true)
      (h1 : Step P1 s1 s2)
      (h2 : h2fsgen_StepsVisitedIn D P1 s2 s3) :
      h2fsgen_StepsVisitedIn D P1 s1 s3

theorem h2fsgen_StepsVisitedIn.toSteps {D : BitVec 64 → Bool} {P1 : Program} {a b : State}
    (h : h2fsgen_StepsVisitedIn D P1 a b) : Steps P1 a b := by
  induction h with
  | refl s => exact .refl s
  | step _ h1 _ ih => exact .step h1 ih

theorem h2fsgen_StepsVisitedIn.trans {D : BitVec 64 → Bool} {P1 : Program} {a b c : State}
    (hab : h2fsgen_StepsVisitedIn D P1 a b) (hbc : h2fsgen_StepsVisitedIn D P1 b c) :
    h2fsgen_StepsVisitedIn D P1 a c := by
  induction hab with
  | refl _ => exact hbc
  | step hd h1 _ ih => exact .step hd h1 (ih hbc)

/-- Lifts `h2fsgen_StepsVisitedIn D P1 s sf` to `Steps P2 s sf` when `P1.svc = P2.svc`,
`P1.externAt? = none` and `P2.externAt? = none` on `D`, and `fetchMem` agrees on `D`. -/
theorem h2fsgen_steps_lift_of_visitedIn
    {D : BitVec 64 → Bool} {P1 P2 : Program} {s sf : State}
    (hsvc : P1.svc = P2.svc)
    (hext1 : ∀ pc : BitVec 64, D pc = true → P1.externAt? pc = none)
    (hext2 : ∀ pc : BitVec 64, D pc = true → P2.externAt? pc = none)
    (hfetch : ∀ (m : Memory) (pc : BitVec 64), D pc = true → P2.fetchMem m pc = P1.fetchMem m pc)
    (hvis : h2fsgen_StepsVisitedIn D P1 s sf) :
    Steps P2 s sf := by
  induction hvis with
  | refl u => exact .refl u
  | @step u v _ hDu h1 _ ih =>
    have he1 : P1.externAt? u.pc = none := hext1 u.pc hDu
    have he2 : P2.externAt? u.pc = none := hext2 u.pc hDu
    have hf12 : P2.fetchMem u.mem u.pc = P1.fetchMem u.mem u.pc := hfetch u.mem u.pc hDu
    have hstep2 : Step P2 u v := by
      cases h1 with
      | @exec inst hrun hfm1 =>
        rw [h2fsgen_evalInst_eq_of_svc_eq hsvc inst u]
        exact Step.exec hrun (hf12.trans hfm1)
      | halt_unmapped hrun hfm1 _ =>
        exact Step.halt_unmapped hrun (hf12.trans hfm1) he2
      | extern _ he _ _ => rw [he1] at he; cases he
      | extern_fault _ he _ => rw [he1] at he; cases he
    exact .step hstep2 ih

/-- Auto-`fetchMem` specialization of `h2fsgen_steps_lift_of_visitedIn`, deriving `fetchMem`
    agreement on `D` from `hext1` and `hext2`. -/
theorem h2fsgen_steps_lift_of_visitedIn_noExtern
    {D : BitVec 64 → Bool} {P1 P2 : Program} {s sf : State}
    (hsvc : P1.svc = P2.svc)
    (hext1 : ∀ pc : BitVec 64, D pc = true → P1.externAt? pc = none)
    (hext2 : ∀ pc : BitVec 64, D pc = true → P2.externAt? pc = none)
    (hvis : h2fsgen_StepsVisitedIn D P1 s sf) :
    Steps P2 s sf :=
  h2fsgen_steps_lift_of_visitedIn hsvc hext1 hext2
    (fun m pc hD => h2fsgen_fetchMem_eq_of_externAt_eq m pc ((hext2 pc hD).trans (hext1 pc hD).symm))
    hvis

/-- Prepend a single step `Step P1 u s1` (`D u.pc = true`) onto `h2fsgen_StepsVisitedIn D P1 s1 sf`. -/
theorem h2fsgen_stepsVisitedIn_step_prefix
    {D : BitVec 64 → Bool} {P1 : Program} {u s1 sf : State}
    (hu : D u.pc = true)
    (h1 : Step P1 u s1)
    (hvis : h2fsgen_StepsVisitedIn D P1 s1 sf) :
    h2fsgen_StepsVisitedIn D P1 u sf :=
  .step hu h1 hvis

/-- Produce `h2fsgen_StepsVisitedIn D P1 s sf` by induction on a `StepsUntil P1 stop s sf` run
    whenever every pre-stop step starts inside `D`. -/
theorem h2fsgen_stepsVisitedIn_of_stepsUntil
    {D : BitVec 64 → Bool} {P1 : Program} {stop : State → Prop} {s sf : State}
    (huntil : StepsUntil P1 stop s sf)
    (hvis : ∀ u v : State, Steps P1 s u → ¬ stop u → Step P1 u v → StepsUntil P1 stop v sf →
      D u.pc = true) :
    h2fsgen_StepsVisitedIn D P1 s sf := by
  induction huntil with
  | refl u => exact .refl u
  | @step s1 s2 _ hnot h1 hrest ih =>
    exact .step (hvis s1 s2 (.refl s1) hnot h1 hrest) h1
      (ih fun u v hpre => hvis u v (.step h1 hpre))

private theorem h2fsgen_stepsVisitedIn_of_stripS_standard_aux
    {keep : BitVec 64 → Bool} {P1 P_sub : Program} {s0 : State}
    (hsvc1 : P1.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hext1_no : ∀ pc, keep pc = true → P1.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hlr_out : keep (s0.readReg64 .lr) = false)
    {s1' sf' : State}
    (hsteps : Steps P_sub s1' sf')
    (hstop' : SubroutineStop s0 sf')
    (hnhalt' : sf'.status ≠ .Halted) :
    ∀ s1 : State,
      s1' = stripS keep s1 →
      ExecFrozen s1.mem →
      ∃ sf : State,
        StepsUntil P1 (SubroutineStop s0) s1 sf ∧
        SubroutineStop s0 sf ∧
        sf' = stripS keep sf ∧
        ExecFrozen sf.mem ∧
        h2fsgen_StepsVisitedIn keep P1 s1 sf := by
  induction hsteps with
  | refl s' =>
    intro s1 hs1 hfr1
    have hstop1 : SubroutineStop s0 s1 :=
      h2fsgen_subroutineStop_stripS_iff.mp (hs1 ▸ hstop')
    exact ⟨s1, .refl s1, hstop1, hs1, hfr1, .refl s1⟩
  | @step sa' sb' sc' h1 hrest ih =>
    intro sa hsa hfra
    by_cases hstop_sa : SubroutineStop s0 sa
    · rcases hstop_sa with ⟨hpc_lr, _⟩ | hpan | ⟨_, hex⟩ | hoom
      · cases h1 with
        | @exec inst hr' hfm' =>
          rw [hsa, h2fsgen_stripS_pc, h2fsgen_stripS_mem] at hfm'
          unfold Program.fetchMem at hfm'
          rw [hsub_no sa.pc] at hfm'
          simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hfm'
          by_cases hal : sa.pc.toNat % 4 = 0
          · simp only [hal, ne_eq, not_true_eq_false, ↓reduceIte] at hfm'
            by_cases hce' : (stripExecOutside keep sa.mem).canExec sa.pc 4 = true
            · have hx0 : ((stripExecOutside keep sa.mem).perm sa.pc).x = true := by
                have h4 :
                    ((stripExecOutside keep sa.mem).perm sa.pc).x = true ∧
                    ((stripExecOutside keep sa.mem).allPerm (·.x) (sa.pc + 1#64) 3) = true := by
                  simpa [Memory.canExec, Memory.allPerm, Bool.and_eq_true] using hce'
                exact h4.1
              have hkp := (strip_perm_x_imp hx0).2
              rw [hpc_lr, hlr_out] at hkp
              cases hkp
            · simp [hce'] at hfm'
          · simp [hal] at hfm'
        | halt_unmapped _ _ _ =>
          exact False.elim (hnhalt' (h2fsgen_steps_preserves_halted hrest rfl))
        | extern _ he _ _ =>
          rw [hsa, h2fsgen_stripS_pc, hsub_no sa.pc] at he; cases he
        | extern_fault _ he _ =>
          rw [hsa, h2fsgen_stripS_pc, hsub_no sa.pc] at he; cases he
      · have hr_sa : sa.status = .Running := by
          have h := h2fsgen_step_status_running h1
          rwa [hsa, h2fsgen_stripS_status] at h
        rw [hpan] at hr_sa; cases hr_sa
      · have hr_sa : sa.status = .Running := by
          have h := h2fsgen_step_status_running h1
          rwa [hsa, h2fsgen_stripS_status] at h
        rw [hex] at hr_sa; cases hr_sa
      · have hr_sa : sa.status = .Running := by
          have h := h2fsgen_step_status_running h1
          rwa [hsa, h2fsgen_stripS_status] at h
        rw [hoom] at hr_sa; cases hr_sa
    · cases h1 with
      | halt_unmapped _ _ _ =>
        exact False.elim (hnhalt' (h2fsgen_steps_preserves_halted hrest rfl))
      | extern _ he' _ _ =>
        rw [hsa, h2fsgen_stripS_pc, hsub_no sa.pc] at he'; cases he'
      | extern_fault _ he' _ =>
        rw [hsa, h2fsgen_stripS_pc, hsub_no sa.pc] at he'; cases he'
      | @exec inst hr' hfm' =>
        have hra : sa.status = .Running := by
          rw [hsa, h2fsgen_stripS_status] at hr'; exact hr'
        rw [hsa, h2fsgen_stripS_pc, h2fsgen_stripS_mem] at hfm'
        unfold Program.fetchMem at hfm'
        rw [hsub_no sa.pc] at hfm'
        simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hfm'
        by_cases hal_pc : sa.pc.toNat % 4 = 0
        · simp only [hal_pc, ne_eq, not_true_eq_false, ↓reduceIte] at hfm'
          by_cases hce' : (stripExecOutside keep sa.mem).canExec sa.pc 4 = true
          · simp only [hce', Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hfm'
            have hx4 :
                ((stripExecOutside keep sa.mem).perm sa.pc).x = true ∧
                ((stripExecOutside keep sa.mem).perm (sa.pc + 1#64)).x = true ∧
                ((stripExecOutside keep sa.mem).perm (sa.pc + 2#64)).x = true ∧
                ((stripExecOutside keep sa.mem).perm (sa.pc + 3#64)).x = true := by
              simpa [Memory.canExec, Memory.allPerm, Bool.and_eq_true, BitVec.add_assoc] using hce'
            obtain ⟨hx0, hkp0⟩ := strip_perm_x_imp hx4.1
            obtain ⟨hx1, _⟩ := strip_perm_x_imp hx4.2.1
            obtain ⟨hx2, _⟩ := strip_perm_x_imp hx4.2.2.1
            obtain ⟨hx3, _⟩ := strip_perm_x_imp hx4.2.2.2
            have hce : sa.mem.canExec sa.pc 4 = true := by
              simp [Memory.canExec, Memory.allPerm, BitVec.add_assoc, hx0, hx1, hx2, hx3]
            rw [h2fsgen_strip_read32] at hfm'
            have hext1 : P1.externAt? sa.pc = none := hext1_no sa.pc hkp0
            have hfm1 : P1.fetchMem sa.mem sa.pc = some inst := by
              unfold Program.fetchMem
              simp [hext1, hal_pc, hce, hfm']
            by_cases hsvc0 : inst.isSvc0 = true
            · have hinst : inst = .system false 0#16 := by
                cases inst <;> simp [Instr.isSvc0] at hsvc0
                rcases hsvc0 with ⟨rfl, rfl⟩; rfl
              subst hinst
              obtain ⟨hcomm, hfr_sb⟩ := standard_stripS (keep := keep) hfra
              have hev_strip :
                  P_sub.evalInst (.system false 0#16) (stripS keep sa) =
                    stripS keep (Syscall.standard sa) := by
                simp [Program.evalInst, execInstWithSvc, hsvc_sub, hcomm]
              have hev1 :
                  P1.evalInst (.system false 0#16) sa = Syscall.standard sa := by
                simp [Program.evalInst, execInstWithSvc, hsvc1]
              have hstep1 : Step P1 sa (Syscall.standard sa) :=
                hev1 ▸ Step.exec hra hfm1
              rw [hsa, hev_strip] at hrest ih
              obtain ⟨sf, huntil_rest, hstop_sf, hsf_eq, hfr_sf, hvis_rest⟩ :=
                ih hstop' hnhalt' (Syscall.standard sa) rfl hfr_sb
              exact ⟨sf, .step hstop_sa hstep1 huntil_rest,
                hstop_sf, hsf_eq, hfr_sf, .step hkp0 hstep1 hvis_rest⟩
            · have hnsvc0 : inst.isSvc0 = false := Bool.eq_false_iff.mpr hsvc0
              have hev_strip :
                  P_sub.evalInst inst (stripS keep sa) =
                    stripS keep (execInst inst sa) := by
                rw [evalInst_eq_execInst_of_not_isSvc0 hnsvc0, execInst_stripS hnsvc0]
              have hev1 : P1.evalInst inst sa = execInst inst sa :=
                evalInst_eq_execInst_of_not_isSvc0 hnsvc0 sa
              have hpf := ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 sa
              have hfr_sb : ExecFrozen (execInst inst sa).mem :=
                ExecFrozen.of_perm_eq hfra (congrFun hpf.2.1)
              have hstep1 : Step P1 sa (execInst inst sa) :=
                hev1 ▸ Step.exec hra hfm1
              rw [hsa, hev_strip] at hrest ih
              obtain ⟨sf, huntil_rest, hstop_sf, hsf_eq, hfr_sf, hvis_rest⟩ :=
                ih hstop' hnhalt' (execInst inst sa) rfl hfr_sb
              exact ⟨sf, .step hstop_sa hstep1 huntil_rest,
                hstop_sf, hsf_eq, hfr_sf, .step hkp0 hstep1 hvis_rest⟩
          · simp [hce'] at hfm'
        · simp [hal_pc] at hfm'

/-- Extracts `h2fsgen_StepsVisitedIn keep P1 s1 sf` from a hook-free subroutine run on
`stripS keep s1`, since `stripExecOutside keep` clears `.x` outside `keep`. -/
theorem h2fsgen_stepsVisitedIn_of_stripS_standard
    {keep : BitVec 64 → Bool} {P1 P_sub : Program} {s0 s1 sf' : State}
    (hsvc1 : P1.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hext1_no : ∀ pc, keep pc = true → P1.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hlr_out : keep (s0.readReg64 .lr) = false)
    (hsteps' : Steps P_sub (stripS keep s1) sf')
    (hstop' : SubroutineStop s0 sf')
    (hnhalt' : sf'.status ≠ .Halted)
    (hFr1 : ExecFrozen s1.mem) :
    ∃ sf : State,
      StepsUntil P1 (SubroutineStop s0) s1 sf ∧
      SubroutineStop s0 sf ∧
      sf' = stripS keep sf ∧
      ExecFrozen sf.mem ∧
      h2fsgen_StepsVisitedIn keep P1 s1 sf :=
  h2fsgen_stepsVisitedIn_of_stripS_standard_aux hsvc1 hsvc_sub hext1_no hsub_no
    hlr_out hsteps' hstop' hnhalt' s1 rfl hFr1

/-- One-shot eliminator combining `subroutine_ok` on `P_sub` (`hsub_no : ∀ pc, P_sub.externAt? pc = none`)
    with `h2fsgen_stepsVisitedIn_of_stripS_standard` to emit both the first-stop run on `P1` and
    `h2fsgen_StepsVisitedIn keep P1 (s0.setPC entryTarget) sf` in one step. -/
theorem h2fsgen_real_subroutine_run_visitedIn_of_stripS {α : Type}
    {keep : BitVec 64 → Bool}
    {P1 P_sub : Program} {entryTarget : BitVec 64}
    {spec : Spec α} {s0 : State}
    (hsvc1 : P1.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hext1_no : ∀ pc, keep pc = true → P1.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hOk : subroutine_ok P_sub entryTarget spec)
    (hInv : SpecStripSInvariant keep spec)
    (hFsT : SpecPreservesFsTrace spec)
    (hPrePC : ∀ x (s : State) (pc : BitVec 64), spec.pre x (s.setPC pc) = spec.pre x s)
    (hOutPC : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome spec x R (s0.setPC pc) sf → SubroutineOutcome spec x R s0 sf)
    {x : α} {R : SepProp}
    (hRun : s0.status = .Running)
    (hSp : s0.spAligned = true)
    (hPre : s0.mem ⊨ spec.pre x s0 ∗ R)
    (hFr : ExecFrozen s0.mem)
    (hlr_out : keep (s0.readReg64 .lr) = false)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep s0.mem)) :
    ∃ sf : State,
      StepsUntil P1 (SubroutineStop s0) (s0.setPC entryTarget) sf ∧
      SubroutineStop s0 sf ∧
      SubroutineOutcome spec x R s0 sf ∧
      sf.fs = s0.fs ∧
      FsTraced IsFsC s0 sf ∧
      ExecFrozen sf.mem ∧
      h2fsgen_StepsVisitedIn keep P1 (s0.setPC entryTarget) sf := by
  let s1 := s0.setPC entryTarget
  let s1' := stripS keep s1
  have hs1_pre : s1.mem ⊨ spec.pre x s1 ∗ R := by
    change s0.mem ⊨ spec.pre x (s0.setPC entryTarget) ∗ R
    rwa [hPrePC x s0 entryTarget]
  have hs1'_pre : s1'.mem ⊨ spec.pre x s1' ∗ R := by
    have hsat := satisfies_stripExecOutside keep hs1_pre
    rwa [← hInv.pre_eq x s1] at hsat
  have hs1'_sp : s1'.spAligned = true := hSp
  obtain ⟨sf', hsteps', hout'⟩ :=
    subroutine_ok_elim_steps_outcome hOk x R s1' rfl hRun hs1'_pre hs1'_sp hCodeSub
  have hstop1' : SubroutineStop s1' sf' := h2fsgen_subroutineOutcome_to_stop hout'
  have hstop0' : SubroutineStop s0 sf' := hstop1'
  have hnhalt' : sf'.status ≠ .Halted := h2fsgen_subroutineOutcome_not_halted hout'
  obtain ⟨sf, huntil, hstop_sf, hsf_eq, hfr_sf, hvis⟩ :=
    h2fsgen_stepsVisitedIn_of_stripS_standard hsvc1 hsvc_sub hext1_no hsub_no
      hlr_out hsteps' hstop0' hnhalt' hFr
  have hout1 : SubroutineOutcome spec x R s1 sf := by
    rw [hsf_eq] at hout'
    rcases hout' with ⟨hret', hcc', hpost'⟩ | ⟨hp', hpan'⟩ | ⟨c, he', hex'⟩ | ⟨ho', hoom'⟩
    · refine Or.inl ⟨?_, ?_, ?_⟩
      · exact ⟨hret'.1, hret'.2.1, hret'.2.2⟩
      · cases s0; cases sf; exact hcc'
      · rw [hInv.post_eq x s1 sf] at hpost'
        exact satisfies_of_stripExecOutside hfr_sf hpost'
    · refine Or.inr (Or.inl ⟨hp', ?_⟩)
      rw [hInv.onPanic_eq x s1 sf] at hpan'
      exact satisfies_of_stripExecOutside hfr_sf hpan'
    · refine Or.inr (Or.inr (Or.inl ⟨c, he', ?_⟩))
      rw [hInv.onExit_eq x c s1 sf] at hex'
      exact satisfies_of_stripExecOutside hfr_sf hex'
    · refine Or.inr (Or.inr (Or.inr ⟨ho', ?_⟩))
      rw [hInv.onOom_eq x s1 sf] at hoom'
      exact satisfies_of_stripExecOutside hfr_sf hoom'
  have hout0 : SubroutineOutcome spec x R s0 sf := hOutPC x R s0 sf entryTarget hout1
  obtain ⟨hfs, hfst⟩ := hFsT x R s0 sf hout0
  exact ⟨sf, huntil, hstop_sf, hout0, hfs, hfst, hfr_sf, hvis⟩

/-! ### Region-Free `HooksUnfetched` `Steps` / `StepsUntil` Lift -/

/-- Every `P2`-hooked address (`P2.externAt? pc ≠ none`) is non-fetchable in `Program.pureMem`
across all `KeepsFrozen` evolutions of `m`. -/
def h2fsgen_HooksUnfetched (P2 : Program) (m : Memory) : Prop :=
  ∀ (m' : Memory) (pc : BitVec 64),
    m.KeepsFrozen m' → P2.externAt? pc ≠ none → Program.pureMem.fetchMem m' pc = none

/-- Criterion establishing `h2fsgen_HooksUnfetched P2 m` whenever every `P2`-hooked PC holds 4
    frozen bytes reading as `0#32` (`Arm64.decode 0#32 = none`). -/
theorem h2fsgen_hooksUnfetched_of_frozenZeroWord {P2 : Program} {m : Memory}
    (hstub : ∀ pc : BitVec 64, P2.externAt? pc ≠ none →
      m.Frozen (pc + 0#64) ∧ m.Frozen (pc + 1#64) ∧
      m.Frozen (pc + 2#64) ∧ m.Frozen (pc + 3#64) ∧
      m.read32 pc = 0#32) :
    h2fsgen_HooksUnfetched P2 m := by
  intro m' pc hkf hne
  obtain ⟨hf0, hf1, hf2, hf3, hz⟩ := hstub pc hne
  have hr32 : m'.read32 pc = m.read32 pc := by
    simp only [Memory.read32, (hkf _ hf0).1, (hkf _ hf1).1, (hkf _ hf2).1, (hkf _ hf3).1]
  have hdec : Arm64.decode (m.read32 pc) = none := by
    rw [hz]; rfl
  unfold Program.fetchMem
  rw [hr32, hdec]
  simp only [ite_self]

/-- Region-free `Steps` lift via `h2fsgen_HooksUnfetched`: lifts any non-halting `Steps P1 sa sf`
run from a `KeepsFrozen` descendant of `m0` to `Steps P2 sa sf` without a visited-PC guard set. -/
theorem h2fsgen_steps_lift_of_hooksUnfetched
    {P1 P2 : Program} {m0 : Memory} {sa sf : State}
    (hsvc : P1.svc = P2.svc)
    (hext12 : ∀ (pc : BitVec 64) (f : State → State),
      P1.externAt? pc = some f → P2.externAt? pc = some f)
    (hunf : h2fsgen_HooksUnfetched P2 m0)
    (hkf : m0.KeepsFrozen sa.mem)
    (hsteps : Steps P1 sa sf)
    (hnhalt : sf.status ≠ .Halted) :
    Steps P2 sa sf := by
  induction hsteps with
  | refl s => exact .refl s
  | @step s1 s2 _ h1 hrest ih =>
    have hkf2 : m0.KeepsFrozen s2.mem := hkf.trans h1.keepsFrozen
    cases h1 with
    | @exec inst hrun hfetch =>
      have hpure : Program.pureMem.fetchMem s1.mem s1.pc = some inst := by
        unfold Program.fetchMem at hfetch ⊢
        split at hfetch
        · cases hfetch
        · simpa [Program.pureMem, Program.pureWithSvc, Program.ofSvc,
            Program.externAt?, Program.hookAtOff?] using hfetch
      have hext2 : P2.externAt? s1.pc = none := by
        by_contra hne
        have hnone := hunf s1.mem s1.pc hkf hne
        rw [hpure] at hnone
        cases hnone
      have hfetch2 : P2.fetchMem s1.mem s1.pc = some inst := by
        unfold Program.fetchMem
        rw [hext2]
        simpa [Program.fetchMem, Program.pureMem, Program.pureWithSvc,
          Program.ofSvc, Program.externAt?, Program.hookAtOff?] using hpure
      have heval : P1.evalInst inst s1 = P2.evalInst inst s1 :=
        h2fsgen_evalInst_eq_of_svc_eq hsvc inst s1
      have ih2 := ih hkf2 hnhalt
      rw [heval] at ih2
      exact .step (Step.exec hrun hfetch2) ih2
    | halt_unmapped _ _ _ =>
      exact False.elim (hnhalt (h2fsgen_steps_preserves_halted hrest rfl))
    | extern hrun hext hkeep hsym =>
      exact .step (Step.extern hrun (hext12 _ _ hext) hkeep hsym) (ih hkf2 hnhalt)
    | extern_fault hrun hext hnkeep =>
      exact .step (Step.extern_fault hrun (hext12 _ _ hext) hnkeep) (ih hkf2 hnhalt)

/-- First-stop `StepsUntil P1 (SubroutineStop u) sa sf` specialization of
`h2fsgen_steps_lift_of_hooksUnfetched`. -/
theorem h2fsgen_stepsUntil_lift_of_hooksUnfetched
    {P1 P2 : Program} {u sa sf : State}
    (hsvc : P1.svc = P2.svc)
    (hext12 : ∀ (pc : BitVec 64) (f : State → State),
      P1.externAt? pc = some f → P2.externAt? pc = some f)
    (hunf : h2fsgen_HooksUnfetched P2 u.mem)
    (hkf : u.mem.KeepsFrozen sa.mem)
    (huntil : StepsUntil P1 (SubroutineStop u) sa sf)
    (hstop : SubroutineStop u sf) :
    Steps P2 sa sf := by
  have hnhalt : sf.status ≠ .Halted := by
    intro hh
    rcases hstop with ⟨_, _, hr⟩ | hpan | ⟨_, hex⟩ | hoom
    · rw [hh] at hr; cases hr
    · rw [hh] at hpan; cases hpan
    · rw [hh] at hex; cases hex
    · rw [hh] at hoom; cases hoom
  exact h2fsgen_steps_lift_of_hooksUnfetched hsvc hext12 hunf hkf huntil.toSteps hnhalt

/-- Zero-`hext12` specialization of `h2fsgen_stepsUntil_lift_of_hooksUnfetched` for hook-free
    programs `P1` (`∀ pc, P1.externAt? pc = none`, e.g. `hole2_emptyProg`) starting at
    `u.setPC entryTarget`: lifts any per-hook first-stop run directly to `Steps P2 (u.setPC entryTarget) sf`
    with zero visited-PC premise. -/
theorem h2fsgen_stepsUntil_noExtern_lift_of_hooksUnfetched
    {P1 P2 : Program} {u sf : State} {entryTarget : BitVec 64}
    (hsvc : P1.svc = P2.svc)
    (hext1_none : ∀ pc : BitVec 64, P1.externAt? pc = none)
    (hunf : h2fsgen_HooksUnfetched P2 u.mem)
    (huntil : StepsUntil P1 (SubroutineStop u) (u.setPC entryTarget) sf)
    (hstop : SubroutineStop u sf) :
    Steps P2 (u.setPC entryTarget) sf :=
  h2fsgen_stepsUntil_lift_of_hooksUnfetched hsvc
    (fun pc _ he => nomatch hext1_none pc ▸ he)
    hunf (Memory.KeepsFrozen.refl u.mem) huntil hstop

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric

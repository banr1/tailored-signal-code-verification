/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookOn -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric -- proof-setup: allow-public-import
import ProofLib.MallocngBridge

/-!
# Real-Code `stripS` & `linkedCallHook` Replays Allowing Panic-Stub Externs (`HooksDehook.StripRunPanicExterns`)

**Not trusted (`Role::Proof`, Card `K4` / `hooks-prep/k4-panic-strip`).**

Generalizes `AllocGhostLinkTransfer.real_subroutine_run_of_stripS`, `linkedCallHook_ok`,
`linkedCallHook_active_steps`, and `LinkedCallHookOn.ghostExternReplaysOn_of_linkedCallHook` from
hook-free subroutine programs (`∀ pc, P_sub.externAt? pc = none`) to subroutine programs `P_sub`
whose extern stubs form a `stripS`-commuting subset of `P_real`'s extern stubs (in particular
`Rust.panicked` cold-panic stubs such as `<SystemTime as Add<Duration>>::add`'s
`core::option::expect_failed`, which IS reachable on `i64` overflow).

- **§2–§3** re-package `ElfSlicesPqOomH2FirstStopGeneric.h2fsgen_real_subroutine_run_of_stripS_ext`
  with the named `StripCommExtern` predicate and separate `hlr_ne`, preserving `.Panicked` outcomes
  through the shared extern on both sides and producing token-identical `HookOk (linkedCallHook ...)`
  and `GhostExternReplaysOn` Arm-2 conclusions.
- **§4** defines `W`-independent `externOnlyStdProg P_sub` together with a generic-`keep`
  with-externs `h2fsgen_StepsVisitedIn (keepOrSubExtern keep P_sub)` producer, an extern-tolerant
  `StepsVisitedIn → Steps` lift (`steps_externOnly_to_real_of_visitedIn`, taking
  `hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none` as a premise), and
  `W`-independent `GhostExternReplaysOn` packagers (`ghostExternReplaysOn_externOnly_visitedIn_*`,
  where `StubReachesTargetOn` runs on `P_real`, never on `externOnlyStdProg P_sub`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StripRunPanicExterns

open Arm64 ProofLib
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  ActiveRealPre ActiveRealRun ExecFrozen SpecPreservesFsTrace SpecStripSInvariant
  keepFsTrace linkedCallHook satisfies_of_stripExecOutside
  satisfies_stripExecOutside standard_stripS
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer (
  StubReachesTargetOn
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookOn (
  linkedCallHook_activeRealPre_of_noException
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric (
  h2fsgen_StepsVisitedIn h2fsgen_fetchMem_eq_of_externAt_eq
  h2fsgen_hookMemcpy_comm_stripS h2fsgen_real_subroutine_run_of_stripS_ext
  h2fsgen_rustPanicked_comm_stripS h2fsgen_stepsUntil_det
)

/-! ## 1. `StripCommExtern` Predicate & Standard Instances (`Rust.panicked`, `hookMemcpy`) -/

/-- State-commutation contract required by `h2fsgen_stepsUntil_of_stripS_standard` for an extern
    hook `f` present in both `P_sub` and `P_real`. -/
@[expose] def StripCommExtern (keep : BitVec 64 → Bool) (f : State → State) : Prop :=
  ∀ st : State, ExecFrozen st.mem →
    (stripS keep st).mem.KeepsFrozen (f (stripS keep st)).mem →
    (f (stripS keep st)).symtab = (stripS keep st).symtab →
    f (stripS keep st) = stripS keep (f st) ∧
    ExecFrozen (f st).mem ∧
    st.mem.KeepsFrozen (f st).mem ∧
    (f st).symtab = st.symtab

/-- `Arm64.Rust.panicked` (`{ s with status := .Panicked }`) commutes with `stripS keep` and
    preserves `ExecFrozen`, `KeepsFrozen`, and `symtab`. -/
theorem stripCommExtern_rustPanicked (keep : BitVec 64 → Bool) :
    StripCommExtern keep Rust.panicked := by
  intro st hfr _ _
  have h := h2fsgen_rustPanicked_comm_stripS keep st hfr
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- `ProofLib.hookMemcpy` commutes with `stripS keep` and preserves `ExecFrozen`, `KeepsFrozen`,
    and `symtab`. -/
theorem stripCommExtern_hookMemcpy (keep : BitVec 64 → Bool) :
    StripCommExtern keep ProofLib.hookMemcpy := by
  intro st hfr hkf _
  have h := h2fsgen_hookMemcpy_comm_stripS keep st hfr hkf
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-! ## 2. Generic `P_sub ⊆ P_real` Extern-Subset `stripS` & `linkedCallHook` Replay Suite -/

/-- Extern-subset generalization of `AllocGhostLinkTransfer.real_subroutine_run_of_stripS`
    (re-packaging `h2fsgen_real_subroutine_run_of_stripS_ext` with `StripCommExtern` and separate
    `hlr_ne`): replaces `hsub_no : ∀ pc, P_sub.externAt? pc = none` with `hext_sub` (every `P_sub`
    extern is present at the same PC in `P_real` and satisfies `StripCommExtern keep`) and `hlr_ne`
    (caller `lr` is not one of `P_sub`'s extern stubs, e.g. from `LsRetAddr624` via `withLsRet`). -/
theorem real_subroutine_run_of_stripS_with_externs {α : Type}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64} {spec : Spec α}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hext_sub : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f →
      P_real.externAt? pc = some f ∧ StripCommExtern keep f)
    (hOk : subroutine_ok P_sub entryTarget spec)
    (hInv : SpecStripSInvariant keep spec)
    (hFsT : SpecPreservesFsTrace spec)
    (hPrePC : ∀ x (s : State) (pc : BitVec 64), spec.pre x (s.setPC pc) = spec.pre x s)
    (hOutPC : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome spec x R (s0.setPC pc) sf → SubroutineOutcome spec x R s0 sf)
    {x : α} {R : SepProp} {s0 : State}
    (hRun : s0.status = .Running)
    (hSp : s0.spAligned = true)
    (hPre : s0.mem ⊨ spec.pre x s0 ∗ R)
    (hFr : ExecFrozen s0.mem)
    (hlr_out : keep (s0.readReg64 .lr) = false)
    (hlr_ne : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → pc ≠ s0.readReg64 .lr)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep s0.mem)) :
    ∃ sf : State,
      StepsUntil P_real (SubroutineStop s0) (s0.setPC entryTarget) sf ∧
      SubroutineStop s0 sf ∧
      SubroutineOutcome spec x R s0 sf ∧
      sf.fs = s0.fs ∧
      FsTraced IsFsC s0 sf ∧
      ExecFrozen sf.mem :=
  h2fsgen_real_subroutine_run_of_stripS_ext
    hsvc_real hsvc_sub hreal_no
    (fun pc f he => ⟨(hext_sub pc f he).1, hlr_ne pc f he, (hext_sub pc f he).2⟩)
    hOk hInv hFsT hPrePC hOutPC hRun hSp hPre hFr hlr_out hCodeSub

/-- Extern-subset generalization of `AllocGhostLinkTransfer.linkedCallHook_ok`:
    proves `HookOk (linkedCallHook keep P_real P_sub entryTarget spec fallback) spec` when `P_sub`'s
    externs are a `StripCommExtern` subset of `P_real`'s externs and `spec.pre` excludes caller
    `lr` from `P_sub`'s extern stubs (e.g. under β′ `withLsRet`). -/
theorem linkedCallHook_ok_with_externs {α : Type}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64} {spec : Spec α} {fallback : State → State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hext_sub : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f →
      P_real.externAt? pc = some f ∧ StripCommExtern keep f)
    (hlr_ne_pre : ∀ x (R : SepProp) (s0 : State),
      (s0.mem ⊨ spec.pre x s0 ∗ R) →
      ∀ (pc : BitVec 64) (f : State → State),
        P_sub.externAt? pc = some f → pc ≠ s0.readReg64 .lr)
    (hOk : subroutine_ok P_sub entryTarget spec)
    (hInv : SpecStripSInvariant keep spec)
    (hFsT : SpecPreservesFsTrace spec)
    (hPrePC : ∀ x (s : State) (pc : BitVec 64), spec.pre x (s.setPC pc) = spec.pre x s)
    (hOutPC : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome spec x R (s0.setPC pc) sf → SubroutineOutcome spec x R s0 sf)
    (hFallbackOk : HookOk (keepFsTrace fallback) spec) :
    HookOk (linkedCallHook keep P_real P_sub entryTarget spec fallback) spec := by
  classical
  intro x R s0 hrun hpre hsp
  have hActPre : ActiveRealPre spec s0 := ⟨hrun, hsp, x, R, hpre⟩
  unfold linkedCallHook
  simp only [hActPre, ↓reduceDIte]
  by_cases hReal : ActiveRealRun keep P_real P_sub entryTarget s0
  · simp only [hReal, ↓reduceDIte]
    obtain ⟨sf, huntil, hstop, hout, _, _, _⟩ :=
      real_subroutine_run_of_stripS_with_externs hsvc_real hsvc_sub hreal_no hext_sub
        hOk hInv hFsT hPrePC hOutPC hrun hsp hpre hReal.1 hReal.2.1
        (hlr_ne_pre x R s0 hpre) hReal.2.2.1
    have hchoose := Classical.choose_spec hReal.2.2.2
    have hdet : Classical.choose hReal.2.2.2 = sf :=
      StepsUntil.deterministic hchoose.1 hchoose.2.1 huntil hstop
    rw [hdet]
    exact ⟨huntil.toSteps.keepsFrozen, huntil.toSteps.symtab_eq, hout⟩
  · simp only [hReal, ↓reduceDIte]
    exact hFallbackOk x R s0 hrun hpre hsp

/-- Extern-subset generalization of `AllocGhostLinkTransfer.linkedCallHook_active_steps`:
    at any call site `s0` satisfying `ActiveRealPre spec s0`, `ExecFrozen s0.mem`,
    `keep (s0.readReg64 .lr) = false`, `hlr_ne`, and `P_sub.CodeLoaded (stripExecOutside keep s0.mem)`,
    `linkedCallHook` steps on `P_real` from `s0.setPC entryTarget` and preserves `ExecFrozen`. -/
theorem linkedCallHook_active_steps_with_externs {α : Type}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64} {spec : Spec α} {fallback : State → State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hext_sub : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f →
      P_real.externAt? pc = some f ∧ StripCommExtern keep f)
    (hOk : subroutine_ok P_sub entryTarget spec)
    (hInv : SpecStripSInvariant keep spec)
    (hFsT : SpecPreservesFsTrace spec)
    (hPrePC : ∀ x (s : State) (pc : BitVec 64), spec.pre x (s.setPC pc) = spec.pre x s)
    (hOutPC : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome spec x R (s0.setPC pc) sf → SubroutineOutcome spec x R s0 sf)
    {s0 : State}
    (hActPre : ActiveRealPre spec s0)
    (hFr : ExecFrozen s0.mem)
    (hlr_out : keep (s0.readReg64 .lr) = false)
    (hlr_ne : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → pc ≠ s0.readReg64 .lr)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep s0.mem)) :
    Steps P_real (s0.setPC entryTarget)
        (linkedCallHook keep P_real P_sub entryTarget spec fallback s0) ∧
      ExecFrozen (linkedCallHook keep P_real P_sub entryTarget spec fallback s0).mem := by
  classical
  have ⟨hrun, hsp, x, R, hpre⟩ := hActPre
  obtain ⟨sf, huntil, hstop, _, hfs, hfst, hfr_sf⟩ :=
    real_subroutine_run_of_stripS_with_externs hsvc_real hsvc_sub hreal_no hext_sub
      hOk hInv hFsT hPrePC hOutPC hrun hsp hpre hFr hlr_out hlr_ne hCodeSub
  have hReal : ActiveRealRun keep P_real P_sub entryTarget s0 :=
    ⟨hFr, hlr_out, hCodeSub, sf, huntil, hstop, hfs, hfst, hfr_sf⟩
  unfold linkedCallHook
  simp only [hActPre, hReal, ↓reduceDIte]
  have hchoose := Classical.choose_spec hReal.2.2.2
  exact ⟨hchoose.1.toSteps, hchoose.2.2.2.2⟩

/-- Extern-subset generalization of `LinkedCallHookOn.ghostExternReplaysOn_of_linkedCallHook`
    (`pc ≠ lr` supplied from `spec.pre`, e.g. β′ `withLsRet` + K3).
    Conclusion is token-identical to `LinkedCallHookOn.ghostExternReplaysOn_of_linkedCallHook`
    (`GhostRowReplayOn` Arm 2). -/
theorem ghostExternReplaysOn_of_linkedCallHook_with_externs {α : Type}
    {InvMem : Memory → Prop}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {stubPc entryTarget : BitVec 64} {spec : Spec α} {fallback : State → State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hext_sub : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f →
      P_real.externAt? pc = some f ∧ StripCommExtern keep f)
    (hlr_ne_pre : ∀ x (R : SepProp) (u : State),
      (u.mem ⊨ spec.pre x u ∗ R) →
      ∀ (pc : BitVec 64) (f : State → State),
        P_sub.externAt? pc = some f → pc ≠ u.readReg64 .lr)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      P_sub.CodeLoaded (stripExecOutside keep m))
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    (hOk : subroutine_ok P_sub entryTarget spec)
    (hInv : SpecStripSInvariant keep spec)
    (hFsT : SpecPreservesFsTrace spec)
    (hPrePC : ∀ x (s : State) (pc : BitVec 64), spec.pre x (s.setPC pc) = spec.pre x s)
    (hOutPC : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome spec x R (s0.setPC pc) sf → SubroutineOutcome spec x R s0 sf) :
    P_real.externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg,
        (linkedCallHook keep P_real P_sub entryTarget spec fallback u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      keep (u.readReg64 .lr) = false →
      InvMem u.mem →
      Steps P_real u (linkedCallHook keep P_real P_sub entryTarget spec fallback u) ∧
      ExecFrozen (linkedCallHook keep P_real P_sub entryTarget spec fallback u).mem ∧
      InvMem (linkedCallHook keep P_real P_sub entryTarget spec fallback u).mem := by
  refine ⟨hreal_stub_none, fun u hpc hrun hnoex hfr hlr hinv => ?_⟩
  have hActPre : ActiveRealPre spec u := linkedCallHook_activeRealPre_of_noException hnoex
  have ⟨_, _, x, R, hpre⟩ := hActPre
  have hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem) := hInvLoaded u.mem hfr hinv
  have hStubSteps : Steps P_real u (u.setPC entryTarget) := hStub u hpc hrun hfr hinv
  obtain ⟨hBodySteps, hfr_out⟩ :=
    linkedCallHook_active_steps_with_externs hsvc_real hsvc_sub hreal_no hext_sub
      hOk hInv hFsT hPrePC hOutPC hActPre hfr hlr (hlr_ne_pre x R u hpre) hCodeSub
  have hSteps : Steps P_real u (linkedCallHook keep P_real P_sub entryTarget spec fallback u) :=
    hStubSteps.trans hBodySteps
  exact ⟨hSteps, hfr_out, hInvKf u.mem _ hinv hSteps.keepsFrozen⟩

/-- Companion to `ghostExternReplaysOn_of_linkedCallHook_with_externs` where `pc ≠ u.readReg64 .lr`
    is supplied from the call-site/memory invariant `hInvLr` rather than `spec.pre`. -/
theorem ghostExternReplaysOn_of_linkedCallHook_with_externs_of_invLr {α : Type}
    {InvMem : Memory → Prop}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {stubPc entryTarget : BitVec 64} {spec : Spec α} {fallback : State → State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hext_sub : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f →
      P_real.externAt? pc = some f ∧ StripCommExtern keep f)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      P_sub.CodeLoaded (stripExecOutside keep m))
    (hInvLr : ∀ u : State,
      u.pc = stubPc → u.status = .Running → ExecFrozen u.mem →
      keep (u.readReg64 .lr) = false → InvMem u.mem →
      ∀ (pc : BitVec 64) (f : State → State),
        P_sub.externAt? pc = some f → pc ≠ u.readReg64 .lr)
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    (hOk : subroutine_ok P_sub entryTarget spec)
    (hInv : SpecStripSInvariant keep spec)
    (hFsT : SpecPreservesFsTrace spec)
    (hPrePC : ∀ x (s : State) (pc : BitVec 64), spec.pre x (s.setPC pc) = spec.pre x s)
    (hOutPC : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome spec x R (s0.setPC pc) sf → SubroutineOutcome spec x R s0 sf) :
    P_real.externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg,
        (linkedCallHook keep P_real P_sub entryTarget spec fallback u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      keep (u.readReg64 .lr) = false →
      InvMem u.mem →
      Steps P_real u (linkedCallHook keep P_real P_sub entryTarget spec fallback u) ∧
      ExecFrozen (linkedCallHook keep P_real P_sub entryTarget spec fallback u).mem ∧
      InvMem (linkedCallHook keep P_real P_sub entryTarget spec fallback u).mem := by
  refine ⟨hreal_stub_none, fun u hpc hrun hnoex hfr hlr hinv => ?_⟩
  have hActPre : ActiveRealPre spec u := linkedCallHook_activeRealPre_of_noException hnoex
  have hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem) := hInvLoaded u.mem hfr hinv
  have hStubSteps : Steps P_real u (u.setPC entryTarget) := hStub u hpc hrun hfr hinv
  obtain ⟨hBodySteps, hfr_out⟩ :=
    linkedCallHook_active_steps_with_externs hsvc_real hsvc_sub hreal_no hext_sub
      hOk hInv hFsT hPrePC hOutPC hActPre hfr hlr (hInvLr u hpc hrun hfr hlr hinv) hCodeSub
  have hSteps : Steps P_real u (linkedCallHook keep P_real P_sub entryTarget spec fallback u) :=
    hStubSteps.trans hBodySteps
  exact ⟨hSteps, hfr_out, hInvKf u.mem _ hinv hSteps.keepsFrozen⟩

/-! ## 3. `Rust.panicked`-Extern Specializations (Supporting `.Panicked` Outcomes) -/

/-- `Rust.panicked` specialization of `real_subroutine_run_of_stripS_with_externs`:
    every extern `e` of `P_sub` equals `Rust.panicked` and is matched at the same PC by `P_real`.
    Both normal `Returned` and `.Panicked` outcomes are preserved across `stripS keep`. -/
theorem real_subroutine_run_of_stripS_panicExterns {α : Type}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64} {spec : Spec α}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_pan : ∀ (pc : BitVec 64) (e : State → State),
      P_sub.externAt? pc = some e →
      e = Rust.panicked ∧ P_real.externAt? pc = some Rust.panicked)
    (hOk : subroutine_ok P_sub entryTarget spec)
    (hInv : SpecStripSInvariant keep spec)
    (hFsT : SpecPreservesFsTrace spec)
    (hPrePC : ∀ x (s : State) (pc : BitVec 64), spec.pre x (s.setPC pc) = spec.pre x s)
    (hOutPC : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome spec x R (s0.setPC pc) sf → SubroutineOutcome spec x R s0 sf)
    {x : α} {R : SepProp} {s0 : State}
    (hRun : s0.status = .Running)
    (hSp : s0.spAligned = true)
    (hPre : s0.mem ⊨ spec.pre x s0 ∗ R)
    (hFr : ExecFrozen s0.mem)
    (hlr_out : keep (s0.readReg64 .lr) = false)
    (hlr_ne : ∀ (pc : BitVec 64) (e : State → State),
      P_sub.externAt? pc = some e → pc ≠ s0.readReg64 .lr)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep s0.mem)) :
    ∃ sf : State,
      StepsUntil P_real (SubroutineStop s0) (s0.setPC entryTarget) sf ∧
      SubroutineStop s0 sf ∧
      SubroutineOutcome spec x R s0 sf ∧
      sf.fs = s0.fs ∧
      FsTraced IsFsC s0 sf ∧
      ExecFrozen sf.mem :=
  real_subroutine_run_of_stripS_with_externs hsvc_real hsvc_sub hreal_no
    (fun pc e he => by
      obtain ⟨rfl, hreal⟩ := hsub_pan pc e he
      exact ⟨hreal, stripCommExtern_rustPanicked keep⟩)
    hOk hInv hFsT hPrePC hOutPC hRun hSp hPre hFr hlr_out hlr_ne hCodeSub

/-- `Rust.panicked` specialization of `linkedCallHook_ok_with_externs`. -/
theorem linkedCallHook_ok_panicExterns {α : Type}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64} {spec : Spec α} {fallback : State → State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_pan : ∀ (pc : BitVec 64) (e : State → State),
      P_sub.externAt? pc = some e →
      e = Rust.panicked ∧ P_real.externAt? pc = some Rust.panicked)
    (hlr_ne_pre : ∀ x (R : SepProp) (s0 : State),
      (s0.mem ⊨ spec.pre x s0 ∗ R) →
      ∀ (pc : BitVec 64) (e : State → State),
        P_sub.externAt? pc = some e → pc ≠ s0.readReg64 .lr)
    (hOk : subroutine_ok P_sub entryTarget spec)
    (hInv : SpecStripSInvariant keep spec)
    (hFsT : SpecPreservesFsTrace spec)
    (hPrePC : ∀ x (s : State) (pc : BitVec 64), spec.pre x (s.setPC pc) = spec.pre x s)
    (hOutPC : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome spec x R (s0.setPC pc) sf → SubroutineOutcome spec x R s0 sf)
    (hFallbackOk : HookOk (keepFsTrace fallback) spec) :
    HookOk (linkedCallHook keep P_real P_sub entryTarget spec fallback) spec :=
  linkedCallHook_ok_with_externs hsvc_real hsvc_sub hreal_no
    (fun pc e he => by
      obtain ⟨rfl, hreal⟩ := hsub_pan pc e he
      exact ⟨hreal, stripCommExtern_rustPanicked keep⟩)
    hlr_ne_pre hOk hInv hFsT hPrePC hOutPC hFallbackOk

/-- `Rust.panicked` specialization of `linkedCallHook_active_steps_with_externs`. -/
theorem linkedCallHook_active_steps_panicExterns {α : Type}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64} {spec : Spec α} {fallback : State → State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_pan : ∀ (pc : BitVec 64) (e : State → State),
      P_sub.externAt? pc = some e →
      e = Rust.panicked ∧ P_real.externAt? pc = some Rust.panicked)
    (hOk : subroutine_ok P_sub entryTarget spec)
    (hInv : SpecStripSInvariant keep spec)
    (hFsT : SpecPreservesFsTrace spec)
    (hPrePC : ∀ x (s : State) (pc : BitVec 64), spec.pre x (s.setPC pc) = spec.pre x s)
    (hOutPC : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome spec x R (s0.setPC pc) sf → SubroutineOutcome spec x R s0 sf)
    {s0 : State}
    (hActPre : ActiveRealPre spec s0)
    (hFr : ExecFrozen s0.mem)
    (hlr_out : keep (s0.readReg64 .lr) = false)
    (hlr_ne : ∀ (pc : BitVec 64) (e : State → State),
      P_sub.externAt? pc = some e → pc ≠ s0.readReg64 .lr)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep s0.mem)) :
    Steps P_real (s0.setPC entryTarget)
        (linkedCallHook keep P_real P_sub entryTarget spec fallback s0) ∧
      ExecFrozen (linkedCallHook keep P_real P_sub entryTarget spec fallback s0).mem :=
  linkedCallHook_active_steps_with_externs hsvc_real hsvc_sub hreal_no
    (fun pc e he => by
      obtain ⟨rfl, hreal⟩ := hsub_pan pc e he
      exact ⟨hreal, stripCommExtern_rustPanicked keep⟩)
    hOk hInv hFsT hPrePC hOutPC hActPre hFr hlr_out hlr_ne hCodeSub

/-- `Rust.panicked` specialization of `ghostExternReplaysOn_of_linkedCallHook_with_externs`
    (`pc ≠ lr` supplied from `spec.pre`, e.g. β′ `withLsRet` + K3). -/
theorem ghostExternReplaysOn_of_linkedCallHook_panicExterns {α : Type}
    {InvMem : Memory → Prop}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {stubPc entryTarget : BitVec 64} {spec : Spec α} {fallback : State → State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_pan : ∀ (pc : BitVec 64) (e : State → State),
      P_sub.externAt? pc = some e →
      e = Rust.panicked ∧ P_real.externAt? pc = some Rust.panicked)
    (hlr_ne_pre : ∀ x (R : SepProp) (u : State),
      (u.mem ⊨ spec.pre x u ∗ R) →
      ∀ (pc : BitVec 64) (e : State → State),
        P_sub.externAt? pc = some e → pc ≠ u.readReg64 .lr)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      P_sub.CodeLoaded (stripExecOutside keep m))
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    (hOk : subroutine_ok P_sub entryTarget spec)
    (hInv : SpecStripSInvariant keep spec)
    (hFsT : SpecPreservesFsTrace spec)
    (hPrePC : ∀ x (s : State) (pc : BitVec 64), spec.pre x (s.setPC pc) = spec.pre x s)
    (hOutPC : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome spec x R (s0.setPC pc) sf → SubroutineOutcome spec x R s0 sf) :
    P_real.externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg,
        (linkedCallHook keep P_real P_sub entryTarget spec fallback u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      keep (u.readReg64 .lr) = false →
      InvMem u.mem →
      Steps P_real u (linkedCallHook keep P_real P_sub entryTarget spec fallback u) ∧
      ExecFrozen (linkedCallHook keep P_real P_sub entryTarget spec fallback u).mem ∧
      InvMem (linkedCallHook keep P_real P_sub entryTarget spec fallback u).mem :=
  ghostExternReplaysOn_of_linkedCallHook_with_externs hsvc_real hsvc_sub hreal_no
    (fun pc e he => by
      obtain ⟨rfl, hreal⟩ := hsub_pan pc e he
      exact ⟨hreal, stripCommExtern_rustPanicked keep⟩)
    hlr_ne_pre hreal_stub_none hStub hInvLoaded hInvKf hOk hInv hFsT hPrePC hOutPC

/-- `Rust.panicked` specialization of `ghostExternReplaysOn_of_linkedCallHook_with_externs_of_invLr`
    (`pc ≠ lr` supplied from call-site/memory invariant `hInvLr`). -/
theorem ghostExternReplaysOn_of_linkedCallHook_panicExterns_of_invLr {α : Type}
    {InvMem : Memory → Prop}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {stubPc entryTarget : BitVec 64} {spec : Spec α} {fallback : State → State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_pan : ∀ (pc : BitVec 64) (e : State → State),
      P_sub.externAt? pc = some e →
      e = Rust.panicked ∧ P_real.externAt? pc = some Rust.panicked)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      P_sub.CodeLoaded (stripExecOutside keep m))
    (hInvLr : ∀ u : State,
      u.pc = stubPc → u.status = .Running → ExecFrozen u.mem →
      keep (u.readReg64 .lr) = false → InvMem u.mem →
      ∀ (pc : BitVec 64) (e : State → State),
        P_sub.externAt? pc = some e → pc ≠ u.readReg64 .lr)
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    (hOk : subroutine_ok P_sub entryTarget spec)
    (hInv : SpecStripSInvariant keep spec)
    (hFsT : SpecPreservesFsTrace spec)
    (hPrePC : ∀ x (s : State) (pc : BitVec 64), spec.pre x (s.setPC pc) = spec.pre x s)
    (hOutPC : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome spec x R (s0.setPC pc) sf → SubroutineOutcome spec x R s0 sf) :
    P_real.externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg,
        (linkedCallHook keep P_real P_sub entryTarget spec fallback u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      keep (u.readReg64 .lr) = false →
      InvMem u.mem →
      Steps P_real u (linkedCallHook keep P_real P_sub entryTarget spec fallback u) ∧
      ExecFrozen (linkedCallHook keep P_real P_sub entryTarget spec fallback u).mem ∧
      InvMem (linkedCallHook keep P_real P_sub entryTarget spec fallback u).mem :=
  ghostExternReplaysOn_of_linkedCallHook_with_externs_of_invLr hsvc_real hsvc_sub hreal_no
    (fun pc e he => by
      obtain ⟨rfl, hreal⟩ := hsub_pan pc e he
      exact ⟨hreal, stripCommExtern_rustPanicked keep⟩)
    hreal_stub_none hStub hInvLoaded hInvLr hInvKf hOk hInv hFsT hPrePC hOutPC

/-! ## 4. `W`-Independent `externOnlyStdProg P_sub`, Generic `StepsVisitedIn` Producer & Extern-Tolerant Lift

Defines `externOnlyStdProg P_sub` (`{ P_sub with code := [], svc := Syscall.standard }`), which
retains only `P_sub`'s `W`-independent extern/override stub map (e.g. `Rust.panicked`), together with:
1. `keepOrSubExtern keep P_sub` (`keep ∪ {pc | (P_sub.externAt? pc).isSome}`),
2. `steps_lift_of_visitedIn_eq_externAt` & `steps_externOnly_to_real_of_visitedIn` (extern-tolerant
   `h2fsgen_StepsVisitedIn` lift generic in `keep`, taking `hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none` as a premise),
3. `stepsVisitedIn_of_stripS_with_externs`, `real_subroutine_run_visitedIn_of_stripS_with_externs`,
   & `linkedCallHook_externOnly_visitedIn_with_externs` (with-externs `stripS` induction producing
   `h2fsgen_StepsVisitedIn (keepOrSubExtern keep P_sub)`), and
4. `ghostExternReplaysOn_externOnly_visitedIn_with_externs` / `_panicExterns` / `_of_invLr`.
-/

/-- `W`-independent `Syscall.standard` program retaining only `P_sub`'s extern/override stub map
    (`code := []`), playing the role of `MemsetGhostK.emptyStdProg` when `P_sub` has cold panic
    externs (`Rust.panicked`). -/
@[expose] def externOnlyStdProg (P_sub : Program) : Program :=
  { P_sub with code := [], svc := Syscall.standard }

theorem externOnlyStdProg_svc (P_sub : Program) :
    (externOnlyStdProg P_sub).svc = Syscall.standard := rfl

theorem externOnlyStdProg_externAt (P_sub : Program) (pc : BitVec 64) :
    (externOnlyStdProg P_sub).externAt? pc = P_sub.externAt? pc := rfl

/-- Extended visitation domain `keep ∪ {pc | (P_sub.externAt? pc).isSome}`: every `exec` step under
    `stripExecOutside keep` starts at `keep pc = true`, while any `P_sub` extern step (such as
    `Rust.panicked`) starts at `(P_sub.externAt? pc).isSome = true`. -/
@[expose] def keepOrSubExtern (keep : BitVec 64 → Bool) (P_sub : Program) (pc : BitVec 64) : Bool :=
  keep pc || (P_sub.externAt? pc).isSome

theorem keepOrSubExtern_of_keep {keep : BitVec 64 → Bool} {P_sub : Program} {pc : BitVec 64}
    (h : keep pc = true) : keepOrSubExtern keep P_sub pc = true := by
  simp [keepOrSubExtern, h]

theorem keepOrSubExtern_of_extern {keep : BitVec 64 → Bool} {P_sub : Program}
    {pc : BitVec 64} {f : State → State}
    (h : P_sub.externAt? pc = some f) : keepOrSubExtern keep P_sub pc = true := by
  simp [keepOrSubExtern, h]

private theorem evalInst_eq_of_svc_eq {P1 P2 : Program} (hsvc : P1.svc = P2.svc)
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

/-- Extern-tolerant generalization of `h2fsgen_steps_lift_of_visitedIn_noExtern`: lifts
    `h2fsgen_StepsVisitedIn D P1 s sf` to `Steps P2 s sf` whenever `P1.svc = P2.svc` and
    `P2.externAt? pc = P1.externAt? pc` on `D` (supporting both `exec` steps where
    `externAt? = none` and shared `extern` steps such as `Rust.panicked` where `externAt? = some f`
    on both programs). -/
theorem steps_lift_of_visitedIn_eq_externAt
    {D : BitVec 64 → Bool} {P1 P2 : Program} {s sf : State}
    (hsvc : P1.svc = P2.svc)
    (hext : ∀ pc : BitVec 64, D pc = true → P2.externAt? pc = P1.externAt? pc)
    (hvis : h2fsgen_StepsVisitedIn D P1 s sf) :
    Steps P2 s sf := by
  induction hvis with
  | refl u => exact .refl u
  | @step u v _ hDu h1 _ ih =>
    have heq : P2.externAt? u.pc = P1.externAt? u.pc := hext u.pc hDu
    have hf12 : P2.fetchMem u.mem u.pc = P1.fetchMem u.mem u.pc :=
      h2fsgen_fetchMem_eq_of_externAt_eq u.mem u.pc heq
    have hstep2 : Step P2 u v := by
      cases h1 with
      | @exec inst hrun hfm1 =>
        rw [evalInst_eq_of_svc_eq hsvc inst u]
        exact Step.exec hrun (hf12.trans hfm1)
      | halt_unmapped hrun hfm1 he1 =>
        exact Step.halt_unmapped hrun (hf12.trans hfm1) (heq.trans he1)
      | extern hrun he1 hkf hsym =>
        exact Step.extern hrun (heq.trans he1) hkf hsym
      | extern_fault hrun he1 hnkf =>
        exact Step.extern_fault hrun (heq.trans he1) hnkf
    exact .step hstep2 ih

/-- Lifts `h2fsgen_StepsVisitedIn (keepOrSubExtern keep P_sub) (externOnlyStdProg P_sub) s sf`
    onto any real target program `P_real` from:
    - `hsvc_real : P_real.svc = Syscall.standard`,
    - `hsub_out_keep : ∀ pc, keep pc = true → P_sub.externAt? pc = none`,
    - `hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none`, and
    - `hext_sub_real : ∀ pc f, P_sub.externAt? pc = some f → P_real.externAt? pc = some f`. -/
theorem steps_externOnly_to_real_of_visitedIn
    {keep : BitVec 64 → Bool} {P_sub P_real : Program} {s sf : State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsub_out_keep : ∀ pc, keep pc = true → P_sub.externAt? pc = none)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hext_sub_real : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → P_real.externAt? pc = some f)
    (hvis : h2fsgen_StepsVisitedIn (keepOrSubExtern keep P_sub) (externOnlyStdProg P_sub) s sf) :
    Steps P_real s sf := by
  refine steps_lift_of_visitedIn_eq_externAt
    ((externOnlyStdProg_svc P_sub).trans hsvc_real.symm) (fun pc hD => ?_) hvis
  rw [externOnlyStdProg_externAt]
  by_cases hkp : keep pc = true
  · rw [hreal_no pc hkp, hsub_out_keep pc hkp]
  · simp only [keepOrSubExtern, hkp, Bool.false_or, Option.isSome_iff_exists] at hD
    rcases hD with ⟨f, hf⟩
    rw [hf, hext_sub_real pc f hf]

private theorem stripS_mem_eq (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).mem = stripExecOutside keep s.mem := by cases s; rfl
private theorem stripS_pc_eq (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).pc = s.pc := by cases s; rfl
private theorem stripS_sp_eq (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).sp = s.sp := by cases s; rfl
private theorem stripS_status_eq (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).status = s.status := by cases s; rfl
private theorem strip_read32_eq (keep : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) :
    (stripExecOutside keep m).read32 a = m.read32 a := by simp [Memory.read32, strip_read8]
private theorem subroutineStop_stripS_iff {keep : BitVec 64 → Bool} {s0 s : State} :
    SubroutineStop s0 (stripS keep s) ↔ SubroutineStop s0 s := by
  simp [SubroutineStop, Returned, stripS_pc_eq, stripS_sp_eq, stripS_status_eq]
private theorem step_status_running {P : Program} {u v : State} (h : Step P u v) :
    u.status = .Running := by cases h <;> assumption
private theorem steps_preserves_halted {P : Program} {u v : State}
    (hs : Steps P u v) (hu : u.status = .Halted) : v.status = .Halted := by
  induction hs with
  | refl => exact hu
  | step h1 _ ih => cases h1 <;> simp_all
private theorem steps_preserves_exception {P : Program} {u v : State} {msg : String}
    (hs : Steps P u v) (hu : u.status = .Exception msg) : v.status = .Exception msg := by
  induction hs with
  | refl => exact hu
  | step h1 _ ih => cases h1 <;> simp_all
private theorem subroutineOutcome_to_stop {α : Type} {spec : Spec α} {x : α} {R : SepProp}
    {s0 sf : State} (h : SubroutineOutcome spec x R s0 sf) : SubroutineStop s0 sf := by
  rcases h with ⟨h1, _, _⟩ | ⟨h2, _⟩ | ⟨c, h3, _⟩ | ⟨h4, _⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (Or.inl ⟨c, h3⟩))
  · exact Or.inr (Or.inr (Or.inr h4))
private theorem subroutineOutcome_not_halted {α : Type} {spec : Spec α} {x : α} {R : SepProp}
    {s0 sf : State} (h : SubroutineOutcome spec x R s0 sf) : sf.status ≠ .Halted := by
  rcases h with ⟨⟨_, _, hst⟩, _, _⟩ | ⟨hst, _⟩ | ⟨_, hst, _⟩ | ⟨hst, _⟩ <;>
    (rw [hst]; nofun)

private theorem stepsVisitedIn_of_stripS_with_externs_aux
    {keep : BitVec 64 → Bool} {P1 P_sub : Program} {s0 : State}
    (hsvc1 : P1.svc = Syscall.standard) (hsvc_sub : P_sub.svc = Syscall.standard)
    (hext1_no : ∀ pc, keep pc = true → P1.externAt? pc = none)
    (hext_sub : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → P1.externAt? pc = some f ∧ StripCommExtern keep f)
    (hlr_out : keep (s0.readReg64 .lr) = false)
    (hlr_ne : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → pc ≠ s0.readReg64 .lr)
    {s1' sf' : State} (hsteps : Steps P_sub s1' sf')
    (hstop' : SubroutineStop s0 sf') (hnhalt' : sf'.status ≠ .Halted) :
    ∀ s1 : State, s1' = stripS keep s1 → ExecFrozen s1.mem →
      ∃ sf : State,
        StepsUntil P1 (SubroutineStop s0) s1 sf ∧ SubroutineStop s0 sf ∧
        sf' = stripS keep sf ∧ ExecFrozen sf.mem ∧
        h2fsgen_StepsVisitedIn (keepOrSubExtern keep P_sub) P1 s1 sf := by
  induction hsteps with
  | refl _ =>
    intro s1 hs1 hfr1
    exact ⟨s1, .refl s1, subroutineStop_stripS_iff.mp (hs1 ▸ hstop'), hs1, hfr1, .refl s1⟩
  | @step sa' sb' sc' h1 hrest ih =>
    intro sa hsa hfra
    by_cases hstop_sa : SubroutineStop s0 sa
    · rcases hstop_sa with ⟨hpc_lr, _⟩ | hpan | ⟨_, hex⟩ | hoom
      · cases h1 with
        | @exec inst hr' hfm' =>
          rw [hsa, stripS_pc_eq, stripS_mem_eq] at hfm'
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
                rw [hpc_lr, hlr_out] at hkp; cases hkp
              · simp [hce'] at hfm'
            · simp [hal] at hfm'
        | halt_unmapped _ _ _ =>
          exact False.elim (hnhalt' (steps_preserves_halted hrest rfl))
        | extern _ he _ _ =>
          rw [hsa, stripS_pc_eq] at he; exact False.elim (hlr_ne sa.pc _ he hpc_lr)
        | extern_fault _ he _ =>
          rw [hsa, stripS_pc_eq] at he; exact False.elim (hlr_ne sa.pc _ he hpc_lr)
      · have hr_sa : sa.status = .Running := by
          have h := step_status_running h1; rwa [hsa, stripS_status_eq] at h
        rw [hpan] at hr_sa; cases hr_sa
      · have hr_sa : sa.status = .Running := by
          have h := step_status_running h1; rwa [hsa, stripS_status_eq] at h
        rw [hex] at hr_sa; cases hr_sa
      · have hr_sa : sa.status = .Running := by
          have h := step_status_running h1; rwa [hsa, stripS_status_eq] at h
        rw [hoom] at hr_sa; cases hr_sa
    · cases h1 with
      | halt_unmapped _ _ _ =>
        exact False.elim (hnhalt' (steps_preserves_halted hrest rfl))
      | extern_fault _ _ _ =>
        have hsf_ex := steps_preserves_exception hrest rfl
        rcases hstop' with ⟨_, _, hr_sf⟩ | hpan | ⟨_, hex⟩ | hoom
        · rw [hsf_ex] at hr_sf; cases hr_sf
        · rw [hsf_ex] at hpan; cases hpan
        · rw [hsf_ex] at hex; cases hex
        · rw [hsf_ex] at hoom; cases hoom
      | @extern f hr' he' hkf' hsym' =>
        have hra : sa.status = .Running := by
          rw [hsa, stripS_status_eq] at hr'; exact hr'
        rw [hsa, stripS_pc_eq] at he'
        rw [hsa] at hkf' hsym'
        obtain ⟨he1, hf_comm⟩ := hext_sub sa.pc f he'
        obtain ⟨hf_eq, hfr_f, hkf_f, hsym_f⟩ := hf_comm sa hfra hkf' hsym'
        have hstep1 : Step P1 sa (f sa) := Step.extern hra he1 hkf_f hsym_f
        have hd : keepOrSubExtern keep P_sub sa.pc = true := keepOrSubExtern_of_extern he'
        rw [hsa, hf_eq] at hrest ih
        obtain ⟨sf, huntil_rest, hstop_sf, hsf_eq, hfr_sf, hvis_rest⟩ :=
          ih hstop' hnhalt' (f sa) rfl hfr_f
        exact ⟨sf, .step hstop_sa hstep1 huntil_rest,
          hstop_sf, hsf_eq, hfr_sf, .step hd hstep1 hvis_rest⟩
      | @exec inst hr' hfm' =>
        have hra : sa.status = .Running := by
          rw [hsa, stripS_status_eq] at hr'; exact hr'
        rw [hsa, stripS_pc_eq, stripS_mem_eq] at hfm'
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
              rw [strip_read32_eq] at hfm'
              have hext1 : P1.externAt? sa.pc = none := hext1_no sa.pc hkp0
              have hfm1 : P1.fetchMem sa.mem sa.pc = some inst := by
                unfold Program.fetchMem; simp [hext1, hal_pc, hce, hfm']
              have hd : keepOrSubExtern keep P_sub sa.pc = true := keepOrSubExtern_of_keep hkp0
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
                have hev1 : P1.evalInst (.system false 0#16) sa = Syscall.standard sa := by
                  simp [Program.evalInst, execInstWithSvc, hsvc1]
                have hstep1 : Step P1 sa (Syscall.standard sa) := hev1 ▸ Step.exec hra hfm1
                rw [hsa, hev_strip] at hrest ih
                obtain ⟨sf, huntil_rest, hstop_sf, hsf_eq, hfr_sf, hvis_rest⟩ :=
                  ih hstop' hnhalt' (Syscall.standard sa) rfl hfr_sb
                exact ⟨sf, .step hstop_sa hstep1 huntil_rest,
                  hstop_sf, hsf_eq, hfr_sf, .step hd hstep1 hvis_rest⟩
              · have hnsvc0 : inst.isSvc0 = false := Bool.eq_false_iff.mpr hsvc0
                have hev_strip :
                    P_sub.evalInst inst (stripS keep sa) = stripS keep (execInst inst sa) := by
                  rw [evalInst_eq_execInst_of_not_isSvc0 hnsvc0, execInst_stripS hnsvc0]
                have hev1 : P1.evalInst inst sa = execInst inst sa :=
                  evalInst_eq_execInst_of_not_isSvc0 hnsvc0 sa
                have hpf := ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 sa
                have hfr_sb : ExecFrozen (execInst inst sa).mem :=
                  ExecFrozen.of_perm_eq hfra (congrFun hpf.2.1)
                have hstep1 : Step P1 sa (execInst inst sa) := hev1 ▸ Step.exec hra hfm1
                rw [hsa, hev_strip] at hrest ih
                obtain ⟨sf, huntil_rest, hstop_sf, hsf_eq, hfr_sf, hvis_rest⟩ :=
                  ih hstop' hnhalt' (execInst inst sa) rfl hfr_sb
                exact ⟨sf, .step hstop_sa hstep1 huntil_rest,
                  hstop_sf, hsf_eq, hfr_sf, .step hd hstep1 hvis_rest⟩
            · simp [hce'] at hfm'
          · simp [hal_pc] at hfm'

/-- With-externs generalization of `h2fsgen_stepsVisitedIn_of_stripS_standard`: lifts a stripped
    subroutine run `Steps P_sub (stripS keep s1) sf'` (`sf'.status ≠ .Halted`) to both a first-stop
    `StepsUntil P1 (SubroutineStop s0) s1 sf` run and an inductive
    `h2fsgen_StepsVisitedIn (keepOrSubExtern keep P_sub) P1 s1 sf` witness. -/
theorem stepsVisitedIn_of_stripS_with_externs
    {keep : BitVec 64 → Bool} {P1 P_sub : Program} {s0 s1 sf' : State}
    (hsvc1 : P1.svc = Syscall.standard) (hsvc_sub : P_sub.svc = Syscall.standard)
    (hext1_no : ∀ pc, keep pc = true → P1.externAt? pc = none)
    (hext_sub : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → P1.externAt? pc = some f ∧ StripCommExtern keep f)
    (hlr_out : keep (s0.readReg64 .lr) = false)
    (hlr_ne : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → pc ≠ s0.readReg64 .lr)
    (hsteps' : Steps P_sub (stripS keep s1) sf')
    (hstop' : SubroutineStop s0 sf') (hnhalt' : sf'.status ≠ .Halted) (hFr1 : ExecFrozen s1.mem) :
    ∃ sf : State,
      StepsUntil P1 (SubroutineStop s0) s1 sf ∧ SubroutineStop s0 sf ∧
      sf' = stripS keep sf ∧ ExecFrozen sf.mem ∧
      h2fsgen_StepsVisitedIn (keepOrSubExtern keep P_sub) P1 s1 sf :=
  stepsVisitedIn_of_stripS_with_externs_aux hsvc1 hsvc_sub hext1_no hext_sub
    hlr_out hlr_ne hsteps' hstop' hnhalt' s1 rfl hFr1

/-- With-externs generalization of `h2fsgen_real_subroutine_run_visitedIn_of_stripS`: combines
    `subroutine_ok P_sub entryTarget spec` with `stepsVisitedIn_of_stripS_with_externs`. -/
theorem real_subroutine_run_visitedIn_of_stripS_with_externs {α : Type}
    {keep : BitVec 64 → Bool} {P1 P_sub : Program} {entryTarget : BitVec 64} {spec : Spec α}
    {s0 : State} (hsvc1 : P1.svc = Syscall.standard) (hsvc_sub : P_sub.svc = Syscall.standard)
    (hext1_no : ∀ pc, keep pc = true → P1.externAt? pc = none)
    (hext_sub : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → P1.externAt? pc = some f ∧ StripCommExtern keep f)
    (hOk : subroutine_ok P_sub entryTarget spec) (hInv : SpecStripSInvariant keep spec)
    (hFsT : SpecPreservesFsTrace spec)
    (hPrePC : ∀ x (s : State) (pc : BitVec 64), spec.pre x (s.setPC pc) = spec.pre x s)
    (hOutPC : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome spec x R (s0.setPC pc) sf → SubroutineOutcome spec x R s0 sf)
    {x : α} {R : SepProp} (hRun : s0.status = .Running) (hSp : s0.spAligned = true)
    (hPre : s0.mem ⊨ spec.pre x s0 ∗ R) (hFr : ExecFrozen s0.mem)
    (hlr_out : keep (s0.readReg64 .lr) = false)
    (hlr_ne : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → pc ≠ s0.readReg64 .lr)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep s0.mem)) :
    ∃ sf : State,
      StepsUntil P1 (SubroutineStop s0) (s0.setPC entryTarget) sf ∧ SubroutineStop s0 sf ∧
      SubroutineOutcome spec x R s0 sf ∧ sf.fs = s0.fs ∧ FsTraced IsFsC s0 sf ∧
      ExecFrozen sf.mem ∧
      h2fsgen_StepsVisitedIn (keepOrSubExtern keep P_sub) P1 (s0.setPC entryTarget) sf := by
  let s1 := s0.setPC entryTarget
  let s1' := stripS keep s1
  have hs1_pre : s1.mem ⊨ spec.pre x s1 ∗ R := by
    change s0.mem ⊨ spec.pre x (s0.setPC entryTarget) ∗ R
    rwa [hPrePC x s0 entryTarget]
  have hs1'_pre : s1'.mem ⊨ spec.pre x s1' ∗ R := by
    have hsat := satisfies_stripExecOutside keep hs1_pre
    rwa [← hInv.pre_eq x s1] at hsat
  obtain ⟨sf', hsteps', hout'⟩ :=
    subroutine_ok_elim_steps_outcome hOk x R s1' rfl hRun hs1'_pre hSp hCodeSub
  have hstop1' : SubroutineStop s1' sf' := subroutineOutcome_to_stop hout'
  have hstop0' : SubroutineStop s0 sf' := hstop1'
  have hnhalt' : sf'.status ≠ .Halted := subroutineOutcome_not_halted hout'
  obtain ⟨sf, huntil, hstop_sf, hsf_eq, hfr_sf, hvis⟩ :=
    stepsVisitedIn_of_stripS_with_externs hsvc1 hsvc_sub hext1_no hext_sub
      hlr_out hlr_ne hsteps' hstop0' hnhalt' hFr
  have hout1 : SubroutineOutcome spec x R s1 sf := by
    rw [hsf_eq] at hout'
    rcases hout' with ⟨hret', hcc', hpost'⟩ | ⟨hp', hpan'⟩ | ⟨c, he', hex'⟩ | ⟨ho', hoom'⟩
    · refine Or.inl ⟨⟨hret'.1, hret'.2.1, hret'.2.2⟩, ?_, ?_⟩
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

/-- `W`-independent `StepsUntil (externOnlyStdProg P_sub) (SubroutineStop u)` first-stop witness
    for `linkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget spec fallback` when all
    `P_sub` externs lie outside `keep` and satisfy `StripCommExtern keep`. -/
theorem linkedCallHook_externOnly_stepsUntil_with_externs {α : Type}
    {keep : BitVec 64 → Bool} {P_sub : Program}
    {entryTarget : BitVec 64} {spec : Spec α} {fallback : State → State}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_out_keep : ∀ pc, keep pc = true → P_sub.externAt? pc = none)
    (hcomm : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → StripCommExtern keep f)
    (hOk : subroutine_ok P_sub entryTarget spec) (hInv : SpecStripSInvariant keep spec)
    (hFsT : SpecPreservesFsTrace spec)
    (hPrePC : ∀ x (s : State) (pc : BitVec 64), spec.pre x (s.setPC pc) = spec.pre x s)
    (hOutPC : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome spec x R (s0.setPC pc) sf → SubroutineOutcome spec x R s0 sf)
    {u : State}
    (hnoex : ∀ msg,
      (linkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget spec fallback u).status ≠
        .Exception msg)
    (hFr : ExecFrozen u.mem) (hlr_out : keep (u.readReg64 .lr) = false)
    (hlr_ne : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → pc ≠ u.readReg64 .lr)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem)) :
    StepsUntil (externOnlyStdProg P_sub) (SubroutineStop u) (u.setPC entryTarget)
        (linkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget spec fallback u) ∧
      SubroutineStop u
        (linkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget spec fallback u) ∧
      ExecFrozen
        (linkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget spec fallback u).mem ∧
      (linkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget spec fallback u).fs = u.fs := by
  classical
  have hActPre : ActiveRealPre spec u := linkedCallHook_activeRealPre_of_noException hnoex
  have ⟨hrun, hsp, x, R, hpre⟩ := hActPre
  obtain ⟨sf, huntil, hstop, _, hfs, hfst, hfr_sf⟩ :=
    real_subroutine_run_of_stripS_with_externs (P_real := externOnlyStdProg P_sub)
      rfl hsvc_sub hsub_out_keep (fun pc f he => ⟨he, hcomm pc f he⟩)
      hOk hInv hFsT hPrePC hOutPC hrun hsp hpre hFr hlr_out hlr_ne hCodeSub
  have hReal : ActiveRealRun keep (externOnlyStdProg P_sub) P_sub entryTarget u :=
    ⟨hFr, hlr_out, hCodeSub, sf, huntil, hstop, hfs, hfst, hfr_sf⟩
  unfold linkedCallHook
  simp only [hActPre, hReal, ↓reduceDIte]
  have hchoose := Classical.choose_spec hReal.2.2.2
  exact ⟨hchoose.1, hchoose.2.1, hchoose.2.2.2.2, hchoose.2.2.1⟩

/-- Pins `sf = linkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget spec fallback u` via
    `h2fsgen_stepsUntil_det` and emits
    `h2fsgen_StepsVisitedIn (keepOrSubExtern keep P_sub) (externOnlyStdProg P_sub) (u.setPC entryTarget) sf`. -/
theorem linkedCallHook_externOnly_visitedIn_with_externs {α : Type}
    {keep : BitVec 64 → Bool} {P_sub : Program}
    {entryTarget : BitVec 64} {spec : Spec α} {fallback : State → State}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_out_keep : ∀ pc, keep pc = true → P_sub.externAt? pc = none)
    (hcomm : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → StripCommExtern keep f)
    (hOk : subroutine_ok P_sub entryTarget spec) (hInv : SpecStripSInvariant keep spec)
    (hFsT : SpecPreservesFsTrace spec)
    (hPrePC : ∀ x (s : State) (pc : BitVec 64), spec.pre x (s.setPC pc) = spec.pre x s)
    (hOutPC : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome spec x R (s0.setPC pc) sf → SubroutineOutcome spec x R s0 sf)
    {u : State}
    (hnoex : ∀ msg,
      (linkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget spec fallback u).status ≠
        .Exception msg)
    (hFr : ExecFrozen u.mem) (hlr_out : keep (u.readReg64 .lr) = false)
    (hlr_ne : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → pc ≠ u.readReg64 .lr)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem)) :
    h2fsgen_StepsVisitedIn (keepOrSubExtern keep P_sub) (externOnlyStdProg P_sub)
        (u.setPC entryTarget)
        (linkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget spec fallback u) ∧
      ExecFrozen
        (linkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget spec fallback u).mem ∧
      (linkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget spec fallback u).fs = u.fs := by
  obtain ⟨huntil_hook, hstop_hook, hfr_hook, hfs_hook⟩ :=
    linkedCallHook_externOnly_stepsUntil_with_externs hsvc_sub hsub_out_keep hcomm
      hOk hInv hFsT hPrePC hOutPC hnoex hFr hlr_out hlr_ne hCodeSub
  have hActPre : ActiveRealPre spec u := linkedCallHook_activeRealPre_of_noException hnoex
  obtain ⟨hrun, hsp, x, R, hpre⟩ := hActPre
  obtain ⟨sf, huntil_sf, hstop_sf, _, _, _, _, hvis_sf⟩ :=
    real_subroutine_run_visitedIn_of_stripS_with_externs
      (P1 := externOnlyStdProg P_sub) rfl hsvc_sub hsub_out_keep
      (fun pc f he => ⟨he, hcomm pc f he⟩)
      hOk hInv hFsT hPrePC hOutPC hrun hsp hpre hFr hlr_out hlr_ne hCodeSub
  have hsf_eq := h2fsgen_stepsUntil_det huntil_sf hstop_sf huntil_hook hstop_hook
  subst hsf_eq
  exact ⟨hvis_sf, hfr_hook, hfs_hook⟩

/-- **Stock-safe `W`-independent `GhostExternReplaysOn` for `externOnlyStdProg P_sub` (`with_externs`):**
    Replays `linkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget spec fallback` (which
    does **not** mention `P_real` / `W`) onto any real target program `P_real` via
    `steps_externOnly_to_real_of_visitedIn`, taking `hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none`
    as a premise. -/
theorem ghostExternReplaysOn_externOnly_visitedIn_with_externs {α : Type}
    {InvMem : Memory → Prop}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {stubPc entryTarget : BitVec 64} {spec : Spec α} {fallback : State → State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_out_keep : ∀ pc, keep pc = true → P_sub.externAt? pc = none)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hext_sub : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f →
      P_real.externAt? pc = some f ∧ StripCommExtern keep f)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      P_sub.CodeLoaded (stripExecOutside keep m))
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    (hOk : subroutine_ok P_sub entryTarget spec)
    (hInv : SpecStripSInvariant keep spec)
    (hFsT : SpecPreservesFsTrace spec)
    (hPrePC : ∀ x (s : State) (pc : BitVec 64), spec.pre x (s.setPC pc) = spec.pre x s)
    (hOutPC : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome spec x R (s0.setPC pc) sf → SubroutineOutcome spec x R s0 sf)
    (hlr_ne_inv : ∀ u : State,
      u.pc = stubPc → u.status = .Running →
      (∀ msg,
        (linkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget spec fallback u).status ≠
          .Exception msg) →
      ExecFrozen u.mem → keep (u.readReg64 .lr) = false → InvMem u.mem →
      ∀ (pc : BitVec 64) (f : State → State),
        P_sub.externAt? pc = some f → pc ≠ u.readReg64 .lr) :
    P_real.externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg,
        (linkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget spec fallback u).status ≠
          .Exception msg) →
      ExecFrozen u.mem →
      keep (u.readReg64 .lr) = false →
      InvMem u.mem →
      Steps P_real u
        (linkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget spec fallback u) ∧
      ExecFrozen
        (linkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget spec fallback u).mem ∧
      InvMem
        (linkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget spec fallback u).mem ∧
      (linkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget spec fallback u).fs = u.fs := by
  refine ⟨hreal_stub_none, fun u hpc hrun hnoex hfr hlr_out hinv => ?_⟩
  have hlr_ne := hlr_ne_inv u hpc hrun hnoex hfr hlr_out hinv
  obtain ⟨hvis, hfr_sf, hfs_sf⟩ :=
    linkedCallHook_externOnly_visitedIn_with_externs hsvc_sub hsub_out_keep
      (fun pc f he => (hext_sub pc f he).2)
      hOk hInv hFsT hPrePC hOutPC hnoex hfr hlr_out hlr_ne
      (hInvLoaded u.mem hfr hinv)
  have hStubSteps : Steps P_real u (u.setPC entryTarget) := hStub u hpc hrun hfr hinv
  have hBodySteps : Steps P_real (u.setPC entryTarget)
      (linkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget spec fallback u) :=
    steps_externOnly_to_real_of_visitedIn hsvc_real hsub_out_keep hreal_no
      (fun pc f he => (hext_sub pc f he).1) hvis
  have hSteps : Steps P_real u
      (linkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget spec fallback u) :=
    hStubSteps.trans hBodySteps
  exact ⟨hSteps, hfr_sf, hInvKf u.mem _ hinv hSteps.keepsFrozen, hfs_sf⟩

/-- **`Rust.panicked` specialization of `ghostExternReplaysOn_externOnly_visitedIn_with_externs`:**
    Stock-safe `W`-independent replay for cold-panic subroutines (such as `SystemTime::add`). -/
theorem ghostExternReplaysOn_externOnly_visitedIn_panicExterns {α : Type}
    {InvMem : Memory → Prop}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {stubPc entryTarget : BitVec 64} {spec : Spec α} {fallback : State → State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_out_keep : ∀ pc, keep pc = true → P_sub.externAt? pc = none)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_pan : ∀ (pc : BitVec 64) (e : State → State),
      P_sub.externAt? pc = some e →
      e = Rust.panicked ∧ P_real.externAt? pc = some Rust.panicked)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      P_sub.CodeLoaded (stripExecOutside keep m))
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    (hOk : subroutine_ok P_sub entryTarget spec)
    (hInv : SpecStripSInvariant keep spec)
    (hFsT : SpecPreservesFsTrace spec)
    (hPrePC : ∀ x (s : State) (pc : BitVec 64), spec.pre x (s.setPC pc) = spec.pre x s)
    (hOutPC : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome spec x R (s0.setPC pc) sf → SubroutineOutcome spec x R s0 sf)
    (hlr_ne_inv : ∀ u : State,
      u.pc = stubPc → u.status = .Running →
      (∀ msg,
        (linkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget spec fallback u).status ≠
          .Exception msg) →
      ExecFrozen u.mem → keep (u.readReg64 .lr) = false → InvMem u.mem →
      ∀ (pc : BitVec 64) (e : State → State),
        P_sub.externAt? pc = some e → pc ≠ u.readReg64 .lr) :
    P_real.externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg,
        (linkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget spec fallback u).status ≠
          .Exception msg) →
      ExecFrozen u.mem →
      keep (u.readReg64 .lr) = false →
      InvMem u.mem →
      Steps P_real u
        (linkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget spec fallback u) ∧
      ExecFrozen
        (linkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget spec fallback u).mem ∧
      InvMem
        (linkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget spec fallback u).mem ∧
      (linkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget spec fallback u).fs = u.fs :=
  ghostExternReplaysOn_externOnly_visitedIn_with_externs hsvc_real hsvc_sub hsub_out_keep hreal_no
    (fun pc e he => by
      obtain ⟨rfl, hreal⟩ := hsub_pan pc e he
      exact ⟨hreal, stripCommExtern_rustPanicked keep⟩)
    hreal_stub_none hStub hInvLoaded hInvKf hOk hInv hFsT hPrePC hOutPC hlr_ne_inv

/-- Zero-`keep(u.lr)` variant of `ghostExternReplaysOn_externOnly_visitedIn_panicExterns`: discharges
    both `keep (u.readReg64 .lr) = false` and `pc ≠ u.readReg64 .lr` from `hnoex` (e.g. via
    `withLsRet` / `LsRetAddr624`). -/
theorem ghostExternReplaysOn_externOnly_visitedIn_panicExterns_of_invLr {α : Type}
    {InvMem : Memory → Prop}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {stubPc entryTarget : BitVec 64} {spec : Spec α} {fallback : State → State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_out_keep : ∀ pc, keep pc = true → P_sub.externAt? pc = none)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_pan : ∀ (pc : BitVec 64) (e : State → State),
      P_sub.externAt? pc = some e →
      e = Rust.panicked ∧ P_real.externAt? pc = some Rust.panicked)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      P_sub.CodeLoaded (stripExecOutside keep m))
    (hInvLr : ∀ u : State,
      u.pc = stubPc → u.status = .Running →
      (∀ msg,
        (linkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget spec fallback u).status ≠
          .Exception msg) →
      ExecFrozen u.mem → InvMem u.mem →
      keep (u.readReg64 .lr) = false ∧
      ∀ (pc : BitVec 64) (e : State → State),
        P_sub.externAt? pc = some e → pc ≠ u.readReg64 .lr)
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    (hOk : subroutine_ok P_sub entryTarget spec)
    (hInv : SpecStripSInvariant keep spec)
    (hFsT : SpecPreservesFsTrace spec)
    (hPrePC : ∀ x (s : State) (pc : BitVec 64), spec.pre x (s.setPC pc) = spec.pre x s)
    (hOutPC : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome spec x R (s0.setPC pc) sf → SubroutineOutcome spec x R s0 sf) :
    P_real.externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg,
        (linkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget spec fallback u).status ≠
          .Exception msg) →
      ExecFrozen u.mem →
      InvMem u.mem →
      Steps P_real u
        (linkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget spec fallback u) ∧
      ExecFrozen
        (linkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget spec fallback u).mem ∧
      InvMem
        (linkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget spec fallback u).mem ∧
      (linkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget spec fallback u).fs = u.fs := by
  have hRep := ghostExternReplaysOn_externOnly_visitedIn_panicExterns
    hsvc_real hsvc_sub hsub_out_keep hreal_no hsub_pan hreal_stub_none hStub hInvLoaded hInvKf
    hOk hInv hFsT hPrePC hOutPC
    (fun u hpc hrun hnoex hfr _ hinv => (hInvLr u hpc hrun hnoex hfr hinv).2)
  exact ⟨hRep.1, fun u hpc hrun hnoex hfr hinv =>
    hRep.2 u hpc hrun hnoex hfr (hInvLr u hpc hrun hnoex hfr hinv).1 hinv⟩

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StripRunPanicExterns

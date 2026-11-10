/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.RustStd.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookOn -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric -- proof-setup: allow-public-import

/-!
# State-Guarded `linkedCallHook` & `.rodata` Table Guards (`HooksDehook.LinkedCallHookG`)

Shared de-hook infrastructure (`DEHOOK-PLAN` §0.4, Card S1) for rows whose real machine code reads a
frozen `.rodata` constant table not owned in the consumer specs' spatial precondition (such as
`core::str::converts::from_utf8`'s 256-byte `corePlacedData1` width table and
`std::time::SystemTime::duration_since`'s 16-byte `timePlacedData0` constant):

1. **`withStateGuard` & `linkedCallHookG`:**
   `linkedCallHookG Guard keep P_real P_sub entryTarget spec fallback` refines `linkedCallHook` by
   requiring `Guard s0` on the active real-code branch:
   - when `Guard s0` holds, it coincides with `linkedCallHook keep P_real P_sub entryTarget spec fallback s0`;
   - when `¬ Guard s0` and `ActiveRealPre spec s0` holds, it delegates to `keepFsTrace fallback s0`;
   - when `¬ ActiveRealPre spec s0`, it returns `.Exception "ghost-hook precondition violated"`.
   Defining `linkedCallHookG` directly via an outer `if _ : Guard s0` keeps every `Guard s0` branch
   equal to `linkedCallHook` by `dif_pos` (`linkedCallHookG_eq_of_guard`) while matching the
   conjunctive `Guard s0 ∧ ActiveRealRun …` characterization (`linkedCallHookG_eq_conj`).
2. **`hookOk_linkedCallHookG`:**
   Establishes `HookOk (linkedCallHookG Guard …) spec` for every state, given `hGuardStrip`, the
   region-local real-code theorem `subroutine_ok P_sub entryTarget (withStateGuard Guard spec)`
   (only requiring real-code correctness under `Guard`), and `hFallbackOk : HookOk (keepFsTrace fallback) spec`
   (since `spec.pre` omits the table, `¬ Guard s0 ∧ ActiveRealPre spec s0` is non-vacuous and
   `hFallbackOk` at the master spec is a genuine obligation).
3. **`ghostExternReplaysOn_of_linkedCallHookG` (& `StepsVisitedIn` `P_run → P_real` lift):**
   Establishes the `GhostExternReplaysS` / `GhostExternReplaysOn` arm-2 replay under
   `hGuard : ∀ u, ExecFrozen u.mem → InvMem u.mem → Guard u`, plus single-stub packagers and the
   stock-safe `StepsVisitedIn` lift `ghostExternReplaysOn_of_linkedCallHookG_liftVis` (and
   `_roTable_liftVis`) for `W`-independent `emptyStdProg` / `hole2_emptyProg` ghost hooks
   (discharged via `h2sl_steps_realW_of_visitedIn_keepSub` + `stepsVisitedIn_mono`; the older
   `StepsUntil` conditional `_lift` / `_roTable_lift` is retained as a pure implication).
   - **C11 §8.2 row-author wiring:** C11's state invariant `InvS u := F3CodeInv' … u.mem ∧ FdsGe3Closed u.fs`
     splits into `InvMem := F3CodeInv' …` plus the `fs` half from `linkedCallHookG_fs`, while
     `hGuard` / `hRoInv` comes from C2 §3 `f3CodeInv_roDataAt_*`.
4. **`.rodata` table guard `roTableGuard tbl bytes`:**
   Wraps `HookDischarge.RustStd.Common.RoDataAt s.mem tbl bytes` (`m.RO tbl bytes.length ∧
   m.readBytes tbl bytes.length = bytes`), proving `withStateGuard (roTableGuard tbl bytes) spec =
   withRoData tbl bytes spec` (`rfl`), `KeepsFrozen`-preservation (`roDataAt_of_keepsFrozen`),
   unconditional `stripExecOutside`-invariance (`roDataAt_stripExecOutside`), separating `↦ᵣ`
   framing (`roTableGuard_intro_sep` / `roTableGuard_elim_sep`), and ready-to-call
   `hookOk_linkedCallHookG_roTable` / `ghostExternReplaysOn_of_linkedCallHookG_roTable_liftVis`
   corollaries.
5. **Smoke instance (`Guard := fun _ => True`):**
   `linkedCallHookG_true_eq` proves `linkedCallHookG (fun _ => True) … = linkedCallHook …` by
   `funext`, and `hookOk_linkedCallHook_via_G` recovers `linkedCallHook_ok`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookG

open Arm64 ProofLib
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (
  RoDataAt SpecSimulates withRoData withRoDataSep
)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  ActiveRealPre ActiveRealRun ExecFrozen SpecPreservesFsTrace SpecStripSInvariant
  keepFsTrace keepFsTrace_fs linkedCallHook linkedCallHook_fs linkedCallHook_fsT
  satisfies_of_stripExecOutside satisfies_stripExecOutside stepsUntil_of_stripS_standard
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer (
  GhostExternReplaysOn GhostExternReplaysS StubReachesTargetOn
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookOn (
  ghostExternReplaysOn_of_single_stub ghostExternReplaysS_of_single_stub
  linkedCallHook_activeRealPre_of_noException
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric (
  h2fsgen_StepsVisitedIn h2fsgen_stepsUntil_det h2fsgen_stepsVisitedIn_of_stripS_standard
)

/-! ## 1. `withStateGuard` & `linkedCallHookG` Core Definitions and Branch Equations -/

/-- Adjoin a pure entry-state guard `⌜Guard s0⌝` to `spec.pre`, keeping `spec`'s spatial
    separation-logic footprint and exit outcomes (`post`, `onPanic`, `onExit`, `onOom`) unchanged. -/
@[expose] def withStateGuard {α : Type} (Guard : State → Prop) (spec : Spec α) : Spec α :=
  { spec with pre := fun x s0 => ⌜Guard s0⌝ ∗ spec.pre x s0 }

open Classical in
/-- State-guarded `linkedCallHook`:
    - When `Guard s0` holds, delegates directly to `linkedCallHook` (running the deterministic
      real-code `StepsUntil` witness when `ActiveRealPre` and `ActiveRealRun` hold, `keepFsTrace fallback`
      when `ActiveRealPre` holds outside `ActiveRealRun`, and `.Exception` outside `ActiveRealPre`).
    - When `¬ Guard s0`, delegates to `keepFsTrace fallback s0` inside `ActiveRealPre spec s0` and
      returns `.Exception "ghost-hook precondition violated"` outside `ActiveRealPre spec s0`. -/
@[expose] noncomputable def linkedCallHookG {α : Type}
    (Guard : State → Prop)
    (keep : BitVec 64 → Bool) (P_real P_sub : Program)
    (entryTarget : BitVec 64) (spec : Spec α) (fallback : State → State) (s0 : State) : State :=
  if _ : Guard s0 then
    linkedCallHook keep P_real P_sub entryTarget spec fallback s0
  else if _ : ActiveRealPre spec s0 then
    keepFsTrace fallback s0
  else
    { s0 with status := .Exception "ghost-hook precondition violated" }

/-- Under `Guard s0`, `linkedCallHookG` reduces to `linkedCallHook`. -/
theorem linkedCallHookG_eq_of_guard {α : Type}
    {Guard : State → Prop} {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64} {spec : Spec α} {fallback : State → State} {s0 : State}
    (hG : Guard s0) :
    linkedCallHookG Guard keep P_real P_sub entryTarget spec fallback s0 =
      linkedCallHook keep P_real P_sub entryTarget spec fallback s0 := by
  unfold linkedCallHookG
  simp [hG]

open Classical in
/-- Outside `Guard s0`, `linkedCallHookG` takes `keepFsTrace fallback` under `ActiveRealPre` and
    `.Exception` otherwise. -/
theorem linkedCallHookG_eq_of_not_guard {α : Type}
    {Guard : State → Prop} {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64} {spec : Spec α} {fallback : State → State} {s0 : State}
    (hnG : ¬ Guard s0) :
    linkedCallHookG Guard keep P_real P_sub entryTarget spec fallback s0 =
      if _ : ActiveRealPre spec s0 then
        keepFsTrace fallback s0
      else
        { s0 with status := .Exception "ghost-hook precondition violated" } := by
  unfold linkedCallHookG
  simp [hnG]

open Classical in
/-- Equivalence with the conjunctive `Guard s0 ∧ ActiveRealRun …` inner-branch formulation. -/
theorem linkedCallHookG_eq_conj {α : Type}
    (Guard : State → Prop) (keep : BitVec 64 → Bool) (P_real P_sub : Program)
    (entryTarget : BitVec 64) (spec : Spec α) (fallback : State → State) (s0 : State) :
    linkedCallHookG Guard keep P_real P_sub entryTarget spec fallback s0 =
      if _ : ActiveRealPre spec s0 then
        if hReal : Guard s0 ∧ ActiveRealRun keep P_real P_sub entryTarget s0 then
          Classical.choose hReal.2.2.2.2
        else
          keepFsTrace fallback s0
      else
        { s0 with status := .Exception "ghost-hook precondition violated" } := by
  by_cases hG : Guard s0
  · rw [linkedCallHookG_eq_of_guard hG]
    unfold linkedCallHook
    by_cases hPre : ActiveRealPre spec s0
    · by_cases hRun : ActiveRealRun keep P_real P_sub entryTarget s0
      · simp [hPre, hG, hRun]
      · simp [hPre, hRun]
    · simp [hPre]
  · rw [linkedCallHookG_eq_of_not_guard hG]
    by_cases hPre : ActiveRealPre spec s0
    · simp [hPre, hG]
    · simp [hPre]

/-- Any non-`.Exception` evaluation of `linkedCallHookG` entered the `ActiveRealPre` branch. -/
theorem linkedCallHookG_activeRealPre_of_noException {α : Type}
    {Guard : State → Prop} {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64} {spec : Spec α} {fallback : State → State} {u : State}
    (hnoex : ∀ msg,
      (linkedCallHookG Guard keep P_real P_sub entryTarget spec fallback u).status ≠ .Exception msg) :
    ActiveRealPre spec u := by
  classical
  by_cases hG : Guard u
  · rw [linkedCallHookG_eq_of_guard hG] at hnoex
    exact linkedCallHook_activeRealPre_of_noException hnoex
  · by_contra hNotPre
    apply hnoex "ghost-hook precondition violated"
    rw [linkedCallHookG_eq_of_not_guard hG]
    simp only [hNotPre, ↓reduceDIte]

open Classical in
/-- When `keep (s0.readReg64 .lr) = true`, `ActiveRealRun` is refuted, so `linkedCallHookG` reduces
    to the fallback / `.Exception` split regardless of `Guard s0` (useful for syntactic `LrTrap`
    compatibility). -/
theorem linkedCallHookG_of_keepLr_true {α : Type}
    {Guard : State → Prop} {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64} {spec : Spec α} {fallback : State → State} {s0 : State}
    (hlr : keep (s0.readReg64 .lr) = true) :
    linkedCallHookG Guard keep P_real P_sub entryTarget spec fallback s0 =
      if _ : ActiveRealPre spec s0 then
        keepFsTrace fallback s0
      else
        { s0 with status := .Exception "ghost-hook precondition violated" } := by
  rw [linkedCallHookG_eq_conj]
  have hNotConj : ¬ (Guard s0 ∧ ActiveRealRun keep P_real P_sub entryTarget s0) := by
    intro ⟨_, _, hlr_f, _⟩
    rw [hlr] at hlr_f
    exact Bool.noConfusion hlr_f
  by_cases hPre : ActiveRealPre spec s0
  · simp only [hPre, hNotConj, ↓reduceDIte]
  · simp only [hPre, ↓reduceDIte]

/-- Unconditional `.fs` invariance of `linkedCallHookG`. -/
theorem linkedCallHookG_fs {α : Type}
    (Guard : State → Prop) (keep : BitVec 64 → Bool) (P_real P_sub : Program)
    (entryTarget : BitVec 64) (spec : Spec α) (fallback : State → State) (s0 : State) :
    (linkedCallHookG Guard keep P_real P_sub entryTarget spec fallback s0).fs = s0.fs := by
  classical
  by_cases hG : Guard s0
  · rw [linkedCallHookG_eq_of_guard hG]
    exact linkedCallHook_fs keep P_real P_sub entryTarget spec fallback s0
  · rw [linkedCallHookG_eq_of_not_guard hG]
    by_cases hPre : ActiveRealPre spec s0
    · simp only [hPre, ↓reduceDIte]
      exact keepFsTrace_fs fallback s0
    · simp only [hPre, ↓reduceDIte]

/-- Unconditional `HookFsTraced IsFsC` for `linkedCallHookG`. -/
theorem linkedCallHookG_fsT {α : Type}
    (Guard : State → Prop) (keep : BitVec 64 → Bool) (P_real P_sub : Program)
    (entryTarget : BitVec 64) (spec : Spec α) (fallback : State → State) :
    HookFsTraced IsFsC (linkedCallHookG Guard keep P_real P_sub entryTarget spec fallback) := by
  classical
  intro s0
  by_cases hG : Guard s0
  · rw [linkedCallHookG_eq_of_guard hG]
    exact linkedCallHook_fsT keep P_real P_sub entryTarget spec fallback s0
  · rw [linkedCallHookG_eq_of_not_guard hG]
    by_cases hPre : ActiveRealPre spec s0
    · simp only [hPre, ↓reduceDIte]
      exact FsTraced.of_eq rfl rfl
    · simp only [hPre, ↓reduceDIte]
      exact FsTraced.of_eq rfl rfl

/-! ## 2. Guarded Strip-Lift, `hookOk_linkedCallHookG`, & Active-Branch Execution -/

private theorem subroutineOutcome_not_halted {α : Type} {spec : Spec α} {x : α} {R : SepProp}
    {s0 sf : State} (h : SubroutineOutcome spec x R s0 sf) : sf.status ≠ .Halted := by
  rcases h with ⟨⟨_, _, hr⟩, _, _⟩ | ⟨hp, _⟩ | ⟨_, he, _⟩ | ⟨ho, _⟩
  · rw [hr]; decide
  · rw [hp]; decide
  · rw [he]; nofun
  · rw [ho]; decide

private theorem subroutineOutcome_to_stop {α : Type} {spec : Spec α} {x : α} {R : SepProp}
    {s0 sf : State} (h : SubroutineOutcome spec x R s0 sf) : SubroutineStop s0 sf := by
  rcases h with ⟨hret, _, _⟩ | ⟨hp, _⟩ | ⟨c, he, _⟩ | ⟨ho, _⟩
  · exact Or.inl hret
  · exact Or.inr (Or.inl hp)
  · exact Or.inr (Or.inr (Or.inl ⟨c, he⟩))
  · exact Or.inr (Or.inr (Or.inr ho))

/-- Lift `subroutine_ok P_sub entryTarget (withStateGuard Guard spec)` across `stripS keep` to a
    first-stop real execution `StepsUntil P_real (SubroutineStop s0) (s0.setPC entryTarget) sf`
    establishing `SubroutineOutcome spec x R s0 sf` whenever `Guard s0` holds. -/
theorem real_subroutine_run_of_stripS_guarded {α : Type}
    {Guard : State → Prop}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64} {spec : Spec α}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hGuardStrip : ∀ s0 : State, ExecFrozen s0.mem → Guard s0 →
      Guard (stripS keep (s0.setPC entryTarget)))
    (hOk : subroutine_ok P_sub entryTarget (withStateGuard Guard spec))
    (hInv : SpecStripSInvariant keep spec)
    (hFsT : SpecPreservesFsTrace spec)
    (hPrePC : ∀ x (s : State) (pc : BitVec 64), spec.pre x (s.setPC pc) = spec.pre x s)
    (hOutPC : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome spec x R (s0.setPC pc) sf → SubroutineOutcome spec x R s0 sf)
    {x : α} {R : SepProp} {s0 : State}
    (hG : Guard s0)
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
  have hs1'_G : Guard s1' := hGuardStrip s0 hFr hG
  have hs1'_preG : s1'.mem ⊨ (withStateGuard Guard spec).pre x s1' ∗ R := by
    dsimp only [withStateGuard]
    rw [sepConj_assoc, pure_sepConj_of_true hs1'_G]
    exact hs1'_pre
  have hs1'_sp : s1'.spAligned = true := hSp
  obtain ⟨sf', hsteps', hout'⟩ :=
    subroutine_ok_elim_steps_outcome hOk x R s1' rfl hRun hs1'_preG hs1'_sp hCodeSub
  have hstop1' : SubroutineStop s1' sf' := subroutineOutcome_to_stop hout'
  have hstop0' : SubroutineStop s0 sf' := hstop1'
  have hnhalt' : sf'.status ≠ .Halted := subroutineOutcome_not_halted hout'
  obtain ⟨sf, huntil, hstop_sf, hsf_eq, hfr_sf⟩ :=
    stepsUntil_of_stripS_standard (s0 := s0)
      hsvc_real hsvc_sub hreal_no
      (fun pc f he => nomatch hsub_no pc ▸ he)
      hlr_out hsteps' hstop0' hnhalt' s1 rfl hFr
  have hout1 : SubroutineOutcome spec x R s1 sf := by
    change SubroutineOutcome spec x R s1' sf' at hout'
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

/-- `StepsVisitedIn`-strengthened counterpart of `real_subroutine_run_of_stripS_guarded`:
    additionally emits `h2fsgen_StepsVisitedIn keep P_real (s0.setPC entryTarget) sf` via
    `h2fsgen_stepsVisitedIn_of_stripS_standard`, enabling stock-safe `W`-polymorphic replay from an
    auxiliary `P_run` (`emptyStdProg` / `hole2_emptyProg`) via `h2sl_steps_realW_of_visitedIn_keepSub`. -/
theorem real_subroutine_run_visitedIn_of_stripS_guarded {α : Type}
    {Guard : State → Prop}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64} {spec : Spec α}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hGuardStrip : ∀ s0 : State, ExecFrozen s0.mem → Guard s0 →
      Guard (stripS keep (s0.setPC entryTarget)))
    (hOk : subroutine_ok P_sub entryTarget (withStateGuard Guard spec))
    (hInv : SpecStripSInvariant keep spec)
    (hFsT : SpecPreservesFsTrace spec)
    (hPrePC : ∀ x (s : State) (pc : BitVec 64), spec.pre x (s.setPC pc) = spec.pre x s)
    (hOutPC : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome spec x R (s0.setPC pc) sf → SubroutineOutcome spec x R s0 sf)
    {x : α} {R : SepProp} {s0 : State}
    (hG : Guard s0)
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
      ExecFrozen sf.mem ∧
      h2fsgen_StepsVisitedIn keep P_real (s0.setPC entryTarget) sf := by
  let s1 := s0.setPC entryTarget
  let s1' := stripS keep s1
  have hs1_pre : s1.mem ⊨ spec.pre x s1 ∗ R := by
    change s0.mem ⊨ spec.pre x (s0.setPC entryTarget) ∗ R
    rwa [hPrePC x s0 entryTarget]
  have hs1'_pre : s1'.mem ⊨ spec.pre x s1' ∗ R := by
    have hsat := satisfies_stripExecOutside keep hs1_pre
    rwa [← hInv.pre_eq x s1] at hsat
  have hs1'_G : Guard s1' := hGuardStrip s0 hFr hG
  have hs1'_preG : s1'.mem ⊨ (withStateGuard Guard spec).pre x s1' ∗ R := by
    dsimp only [withStateGuard]
    rw [sepConj_assoc, pure_sepConj_of_true hs1'_G]
    exact hs1'_pre
  have hs1'_sp : s1'.spAligned = true := hSp
  obtain ⟨sf', hsteps', hout'⟩ :=
    subroutine_ok_elim_steps_outcome hOk x R s1' rfl hRun hs1'_preG hs1'_sp hCodeSub
  have hstop1' : SubroutineStop s1' sf' := subroutineOutcome_to_stop hout'
  have hstop0' : SubroutineStop s0 sf' := hstop1'
  have hnhalt' : sf'.status ≠ .Halted := subroutineOutcome_not_halted hout'
  have hFr1 : ExecFrozen s1.mem := hFr
  obtain ⟨sf, huntil, hstop_sf, hsf_eq, hfr_sf, hvis⟩ :=
    h2fsgen_stepsVisitedIn_of_stripS_standard hsvc_real hsvc_sub hreal_no hsub_no
      hlr_out hsteps' hstop0' hnhalt' hFr1
  have hout1 : SubroutineOutcome spec x R s1 sf := by
    change SubroutineOutcome spec x R s1' sf' at hout'
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

/-- **`HookOk` for `linkedCallHookG`:**
    Requires the region-local real-code proof only under `Guard` (`withStateGuard Guard spec`),
    using `real_subroutine_run_of_stripS_guarded` when `Guard s0 ∧ ActiveRealRun …` holds and
    `hFallbackOk` when either `¬ Guard s0` or `¬ ActiveRealRun …` (for every state, given
    `hGuardStrip` and `hFallbackOk`). -/
theorem hookOk_linkedCallHookG {α : Type}
    {Guard : State → Prop}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64} {spec : Spec α} {fallback : State → State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hGuardStrip : ∀ s0 : State, ExecFrozen s0.mem → Guard s0 →
      Guard (stripS keep (s0.setPC entryTarget)))
    (hOk : subroutine_ok P_sub entryTarget (withStateGuard Guard spec))
    (hInv : SpecStripSInvariant keep spec)
    (hFsT : SpecPreservesFsTrace spec)
    (hPrePC : ∀ x (s : State) (pc : BitVec 64), spec.pre x (s.setPC pc) = spec.pre x s)
    (hOutPC : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome spec x R (s0.setPC pc) sf → SubroutineOutcome spec x R s0 sf)
    (hFallbackOk : HookOk (keepFsTrace fallback) spec) :
    HookOk (linkedCallHookG Guard keep P_real P_sub entryTarget spec fallback) spec := by
  classical
  intro x R s0 hrun hpre hsp
  have hActPre : ActiveRealPre spec s0 := ⟨hrun, hsp, x, R, hpre⟩
  by_cases hG : Guard s0
  · rw [linkedCallHookG_eq_of_guard hG]
    unfold linkedCallHook
    simp only [hActPre, ↓reduceDIte]
    by_cases hReal : ActiveRealRun keep P_real P_sub entryTarget s0
    · simp only [hReal, ↓reduceDIte]
      obtain ⟨sf, huntil, hstop, hout, _, _, _⟩ :=
        real_subroutine_run_of_stripS_guarded hsvc_real hsvc_sub hreal_no hsub_no
          hGuardStrip hOk hInv hFsT hPrePC hOutPC hG hrun hsp hpre
          hReal.1 hReal.2.1 hReal.2.2.1
      have hchoose := Classical.choose_spec hReal.2.2.2
      have hdet : Classical.choose hReal.2.2.2 = sf :=
        StepsUntil.deterministic hchoose.1 hchoose.2.1 huntil hstop
      rw [hdet]
      exact ⟨huntil.toSteps.keepsFrozen, huntil.toSteps.symtab_eq, hout⟩
    · simp only [hReal, ↓reduceDIte]
      exact hFallbackOk x R s0 hrun hpre hsp
  · rw [linkedCallHookG_eq_of_not_guard hG]
    simp only [hActPre, ↓reduceDIte]
    exact hFallbackOk x R s0 hrun hpre hsp

/-- First-stop execution witness for `linkedCallHookG` on any active guarded call (`Guard s0`,
    `ActiveRealPre spec s0`, `ExecFrozen s0.mem`, `keep (s0.readReg64 .lr) = false`, and
    `P_sub.CodeLoaded (stripExecOutside keep s0.mem)`). -/
theorem linkedCallHookG_stepsUntil {α : Type}
    {Guard : State → Prop}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64} {spec : Spec α} {fallback : State → State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hGuardStrip : ∀ s0 : State, ExecFrozen s0.mem → Guard s0 →
      Guard (stripS keep (s0.setPC entryTarget)))
    (hOk : subroutine_ok P_sub entryTarget (withStateGuard Guard spec))
    (hInv : SpecStripSInvariant keep spec)
    (hFsT : SpecPreservesFsTrace spec)
    (hPrePC : ∀ x (s : State) (pc : BitVec 64), spec.pre x (s.setPC pc) = spec.pre x s)
    (hOutPC : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome spec x R (s0.setPC pc) sf → SubroutineOutcome spec x R s0 sf)
    {s0 : State}
    (hG : Guard s0)
    (hActPre : ActiveRealPre spec s0)
    (hFr : ExecFrozen s0.mem)
    (hlr_out : keep (s0.readReg64 .lr) = false)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep s0.mem)) :
    StepsUntil P_real (SubroutineStop s0) (s0.setPC entryTarget)
        (linkedCallHookG Guard keep P_real P_sub entryTarget spec fallback s0) ∧
      SubroutineStop s0 (linkedCallHookG Guard keep P_real P_sub entryTarget spec fallback s0) ∧
      ExecFrozen (linkedCallHookG Guard keep P_real P_sub entryTarget spec fallback s0).mem := by
  classical
  have ⟨hrun, hsp, x, R, hpre⟩ := hActPre
  obtain ⟨sf, huntil, hstop, _, hfs, hfst, hfr_sf⟩ :=
    real_subroutine_run_of_stripS_guarded hsvc_real hsvc_sub hreal_no hsub_no
      hGuardStrip hOk hInv hFsT hPrePC hOutPC hG hrun hsp hpre hFr hlr_out hCodeSub
  have hReal : ActiveRealRun keep P_real P_sub entryTarget s0 :=
    ⟨hFr, hlr_out, hCodeSub, sf, huntil, hstop, hfs, hfst, hfr_sf⟩
  rw [linkedCallHookG_eq_of_guard hG]
  unfold linkedCallHook
  simp only [hActPre, hReal, ↓reduceDIte]
  have hchoose := Classical.choose_spec hReal.2.2.2
  exact ⟨hchoose.1, hchoose.2.1, hchoose.2.2.2.2⟩

/-- Guarded counterpart of `AllocGhostLinkTransfer.linkedCallHook_active_steps`: under `Guard s0`
    and the active real-run conditions, `linkedCallHookG` executes `Steps P_real` from
    `s0.setPC entryTarget` and preserves `ExecFrozen`. -/
theorem linkedCallHookG_active_steps {α : Type}
    {Guard : State → Prop}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64} {spec : Spec α} {fallback : State → State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hGuardStrip : ∀ s0 : State, ExecFrozen s0.mem → Guard s0 →
      Guard (stripS keep (s0.setPC entryTarget)))
    (hOk : subroutine_ok P_sub entryTarget (withStateGuard Guard spec))
    (hInv : SpecStripSInvariant keep spec)
    (hFsT : SpecPreservesFsTrace spec)
    (hPrePC : ∀ x (s : State) (pc : BitVec 64), spec.pre x (s.setPC pc) = spec.pre x s)
    (hOutPC : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome spec x R (s0.setPC pc) sf → SubroutineOutcome spec x R s0 sf)
    {s0 : State}
    (hG : Guard s0)
    (hActPre : ActiveRealPre spec s0)
    (hFr : ExecFrozen s0.mem)
    (hlr_out : keep (s0.readReg64 .lr) = false)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep s0.mem)) :
    Steps P_real (s0.setPC entryTarget)
        (linkedCallHookG Guard keep P_real P_sub entryTarget spec fallback s0) ∧
      ExecFrozen (linkedCallHookG Guard keep P_real P_sub entryTarget spec fallback s0).mem := by
  obtain ⟨huntil, _, hfr⟩ :=
    linkedCallHookG_stepsUntil hsvc_real hsvc_sub hreal_no hsub_no hGuardStrip hOk
      hInv hFsT hPrePC hOutPC hG hActPre hFr hlr_out hCodeSub
  exact ⟨huntil.toSteps, hfr⟩

/-- Under `Guard s0` and the active real-run conditions, `linkedCallHookG` evaluates to a state
    reached along `h2fsgen_StepsVisitedIn keep P_run (s0.setPC entryTarget)` (pinned via
    `h2fsgen_stepsUntil_det`) while preserving `ExecFrozen`. -/
theorem linkedCallHookG_visitedIn {α : Type}
    {Guard : State → Prop}
    {keep : BitVec 64 → Bool} {P_run P_sub : Program}
    {entryTarget : BitVec 64} {spec : Spec α} {fallback : State → State}
    (hsvc_run : P_run.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hrun_no : ∀ pc, keep pc = true → P_run.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hGuardStrip : ∀ s0 : State, ExecFrozen s0.mem → Guard s0 →
      Guard (stripS keep (s0.setPC entryTarget)))
    (hOk : subroutine_ok P_sub entryTarget (withStateGuard Guard spec))
    (hInv : SpecStripSInvariant keep spec)
    (hFsT : SpecPreservesFsTrace spec)
    (hPrePC : ∀ x (s : State) (pc : BitVec 64), spec.pre x (s.setPC pc) = spec.pre x s)
    (hOutPC : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome spec x R (s0.setPC pc) sf → SubroutineOutcome spec x R s0 sf)
    {s0 : State}
    (hG : Guard s0)
    (hActPre : ActiveRealPre spec s0)
    (hFr : ExecFrozen s0.mem)
    (hlr_out : keep (s0.readReg64 .lr) = false)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep s0.mem)) :
    h2fsgen_StepsVisitedIn keep P_run (s0.setPC entryTarget)
        (linkedCallHookG Guard keep P_run P_sub entryTarget spec fallback s0) ∧
      ExecFrozen (linkedCallHookG Guard keep P_run P_sub entryTarget spec fallback s0).mem := by
  classical
  have ⟨hrun, hsp, x, R, hpre⟩ := hActPre
  obtain ⟨sf, huntil, hstop, _, hfs, hfst, hfr_sf, hvis⟩ :=
    real_subroutine_run_visitedIn_of_stripS_guarded hsvc_run hsvc_sub hrun_no hsub_no
      hGuardStrip hOk hInv hFsT hPrePC hOutPC hG hrun hsp hpre hFr hlr_out hCodeSub
  have hReal : ActiveRealRun keep P_run P_sub entryTarget s0 :=
    ⟨hFr, hlr_out, hCodeSub, sf, huntil, hstop, hfs, hfst, hfr_sf⟩
  have heq :
      linkedCallHookG Guard keep P_run P_sub entryTarget spec fallback s0 = sf := by
    rw [linkedCallHookG_eq_of_guard hG]
    unfold linkedCallHook
    simp only [hActPre, hReal, ↓reduceDIte]
    have hchoose := Classical.choose_spec hReal.2.2.2
    exact h2fsgen_stepsUntil_det hchoose.1 hchoose.2.1 huntil hstop
  rw [heq]
  exact ⟨hvis, hfr_sf⟩

/-! ## 3. Guarded `On` / `S` Replay Lemmas (`ghostExternReplaysOn_of_linkedCallHookG`) -/

/-- **Guarded `On`/`S` replay for `linkedCallHookG`:**
    Like `LinkedCallHookOn.ghostExternReplaysOn_of_linkedCallHook`, plus
    `hGuard : ∀ u : State, ExecFrozen u.mem → InvMem u.mem → Guard u` (discharging `Guard u` from
    the replay invariant `ExecFrozen u.mem ∧ InvMem u.mem` at every non-faulting call) and
    `hGuardStrip` / `hOk : subroutine_ok P_sub entryTarget (withStateGuard Guard spec)`. -/
theorem ghostExternReplaysOn_of_linkedCallHookG {α : Type}
    {InvMem : Memory → Prop} {Guard : State → Prop}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {stubPc entryTarget : BitVec 64} {spec : Spec α} {fallback : State → State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      P_sub.CodeLoaded (stripExecOutside keep m))
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    (hGuard : ∀ u : State, ExecFrozen u.mem → InvMem u.mem → Guard u)
    (hGuardStrip : ∀ s0 : State, ExecFrozen s0.mem → Guard s0 →
      Guard (stripS keep (s0.setPC entryTarget)))
    (hOk : subroutine_ok P_sub entryTarget (withStateGuard Guard spec))
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
        (linkedCallHookG Guard keep P_real P_sub entryTarget spec fallback u).status ≠
          .Exception msg) →
      ExecFrozen u.mem →
      keep (u.readReg64 .lr) = false →
      InvMem u.mem →
      Steps P_real u (linkedCallHookG Guard keep P_real P_sub entryTarget spec fallback u) ∧
      ExecFrozen (linkedCallHookG Guard keep P_real P_sub entryTarget spec fallback u).mem ∧
      InvMem (linkedCallHookG Guard keep P_real P_sub entryTarget spec fallback u).mem := by
  refine ⟨hreal_stub_none, fun u hpc hrun hnoex hfr hlr hinv => ?_⟩
  have hGu : Guard u := hGuard u hfr hinv
  have hActPre : ActiveRealPre spec u := linkedCallHookG_activeRealPre_of_noException hnoex
  have hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem) := hInvLoaded u.mem hfr hinv
  have hStubSteps : Steps P_real u (u.setPC entryTarget) := hStub u hpc hrun hfr hinv
  obtain ⟨hBodySteps, hfr_out⟩ :=
    linkedCallHookG_active_steps hsvc_real hsvc_sub hreal_no hsub_no hGuardStrip hOk
      hInv hFsT hPrePC hOutPC hGu hActPre hfr hlr hCodeSub
  have hSteps :
      Steps P_real u (linkedCallHookG Guard keep P_real P_sub entryTarget spec fallback u) :=
    hStubSteps.trans hBodySteps
  exact ⟨hSteps, hfr_out, hInvKf u.mem _ hinv hSteps.keepsFrozen⟩

/-- **Conditional `StepsUntil` `P_run → P_real` replay for `linkedCallHookG`:**
    Replays a `W`-independent ghost hook defined against an auxiliary program `P_run` onto `P_real`
    given a `StepsUntil` lift `hLift`. Note: for stock-ELF `W`-polymorphic row ghosts (`emptyStdProg` /
    `hole2_emptyProg`), prefer `ghostExternReplaysOn_of_linkedCallHookG_liftVis` below, whose
    `h2fsgen_StepsVisitedIn` premise discharges via `h2sl_steps_realW_of_visitedIn_keepSub`. -/
theorem ghostExternReplaysOn_of_linkedCallHookG_lift {α : Type}
    {InvMem : Memory → Prop} {Guard : State → Prop}
    {keep : BitVec 64 → Bool} {P_run P_real P_sub : Program}
    {stubPc entryTarget : BitVec 64} {spec : Spec α} {fallback : State → State}
    (hsvc_run : P_run.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hrun_no : ∀ pc, keep pc = true → P_run.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hLift : ∀ u sf : State,
      ExecFrozen u.mem → InvMem u.mem → keep (u.readReg64 .lr) = false →
      StepsUntil P_run (SubroutineStop u) (u.setPC entryTarget) sf →
      SubroutineStop u sf →
      Steps P_real (u.setPC entryTarget) sf)
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      P_sub.CodeLoaded (stripExecOutside keep m))
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    (hGuard : ∀ u : State, ExecFrozen u.mem → InvMem u.mem → Guard u)
    (hGuardStrip : ∀ s0 : State, ExecFrozen s0.mem → Guard s0 →
      Guard (stripS keep (s0.setPC entryTarget)))
    (hOk : subroutine_ok P_sub entryTarget (withStateGuard Guard spec))
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
        (linkedCallHookG Guard keep P_run P_sub entryTarget spec fallback u).status ≠
          .Exception msg) →
      ExecFrozen u.mem →
      keep (u.readReg64 .lr) = false →
      InvMem u.mem →
      Steps P_real u (linkedCallHookG Guard keep P_run P_sub entryTarget spec fallback u) ∧
      ExecFrozen (linkedCallHookG Guard keep P_run P_sub entryTarget spec fallback u).mem ∧
      InvMem (linkedCallHookG Guard keep P_run P_sub entryTarget spec fallback u).mem := by
  refine ⟨hreal_stub_none, fun u hpc hrun hnoex hfr hlr hinv => ?_⟩
  have hGu : Guard u := hGuard u hfr hinv
  have hActPre : ActiveRealPre spec u := linkedCallHookG_activeRealPre_of_noException hnoex
  have hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem) := hInvLoaded u.mem hfr hinv
  have hStubSteps : Steps P_real u (u.setPC entryTarget) := hStub u hpc hrun hfr hinv
  obtain ⟨huntil, hstop, hfr_out⟩ :=
    linkedCallHookG_stepsUntil hsvc_run hsvc_sub hrun_no hsub_no hGuardStrip hOk
      hInv hFsT hPrePC hOutPC hGu hActPre hfr hlr hCodeSub
  have hBodySteps :
      Steps P_real (u.setPC entryTarget)
        (linkedCallHookG Guard keep P_run P_sub entryTarget spec fallback u) :=
    hLift u _ hfr hinv hlr huntil hstop
  have hSteps :
      Steps P_real u (linkedCallHookG Guard keep P_run P_sub entryTarget spec fallback u) :=
    hStubSteps.trans hBodySteps
  exact ⟨hSteps, hfr_out, hInvKf u.mem _ hinv hSteps.keepsFrozen⟩

/-- **Stock-safe `StepsVisitedIn` `P_run → P_real` replay for `linkedCallHookG`:**
    Replays a `W`-independent ghost hook defined against an auxiliary program `P_run` (such as
    `emptyStdProg` / `hole2_emptyProg`) onto `P_real` via `hLiftVis` over
    `h2fsgen_StepsVisitedIn keep P_run (u.setPC entryTarget) sf` (discharged on stock via
    `h2sl_steps_realW_of_visitedIn_keepSub` + `stepsVisitedIn_mono`). -/
theorem ghostExternReplaysOn_of_linkedCallHookG_liftVis {α : Type}
    {InvMem : Memory → Prop} {Guard : State → Prop}
    {keep : BitVec 64 → Bool} {P_run P_real P_sub : Program}
    {stubPc entryTarget : BitVec 64} {spec : Spec α} {fallback : State → State}
    (hsvc_run : P_run.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hrun_no : ∀ pc, keep pc = true → P_run.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hLiftVis : ∀ u sf : State,
      u.status = .Running → ExecFrozen u.mem → InvMem u.mem →
      h2fsgen_StepsVisitedIn keep P_run (u.setPC entryTarget) sf →
      Steps P_real (u.setPC entryTarget) sf)
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      P_sub.CodeLoaded (stripExecOutside keep m))
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    (hGuard : ∀ u : State, ExecFrozen u.mem → InvMem u.mem → Guard u)
    (hGuardStrip : ∀ s0 : State, ExecFrozen s0.mem → Guard s0 →
      Guard (stripS keep (s0.setPC entryTarget)))
    (hOk : subroutine_ok P_sub entryTarget (withStateGuard Guard spec))
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
        (linkedCallHookG Guard keep P_run P_sub entryTarget spec fallback u).status ≠
          .Exception msg) →
      ExecFrozen u.mem →
      keep (u.readReg64 .lr) = false →
      InvMem u.mem →
      Steps P_real u (linkedCallHookG Guard keep P_run P_sub entryTarget spec fallback u) ∧
      ExecFrozen (linkedCallHookG Guard keep P_run P_sub entryTarget spec fallback u).mem ∧
      InvMem (linkedCallHookG Guard keep P_run P_sub entryTarget spec fallback u).mem := by
  refine ⟨hreal_stub_none, fun u hpc hrun hnoex hfr hlr hinv => ?_⟩
  have hGu : Guard u := hGuard u hfr hinv
  have hActPre : ActiveRealPre spec u := linkedCallHookG_activeRealPre_of_noException hnoex
  have hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem) := hInvLoaded u.mem hfr hinv
  have hStubSteps : Steps P_real u (u.setPC entryTarget) := hStub u hpc hrun hfr hinv
  obtain ⟨hvis, hfr_out⟩ :=
    linkedCallHookG_visitedIn hsvc_run hsvc_sub hrun_no hsub_no hGuardStrip hOk
      hInv hFsT hPrePC hOutPC hGu hActPre hfr hlr hCodeSub
  have hBodySteps :
      Steps P_real (u.setPC entryTarget)
        (linkedCallHookG Guard keep P_run P_sub entryTarget spec fallback u) :=
    hLiftVis u _ hrun hfr hinv hvis
  have hSteps :
      Steps P_real u (linkedCallHookG Guard keep P_run P_sub entryTarget spec fallback u) :=
    hStubSteps.trans hBodySteps
  exact ⟨hSteps, hfr_out, hInvKf u.mem _ hinv hSteps.keepsFrozen⟩

/-- Single-stub `GhostExternReplaysS` packager for `linkedCallHookG` (note:
    `LinkedCallHookOn.ghostExternReplaysS_of_single_stub` is polymorphic in `f_stub : State → State`
    and applies directly as well). -/
theorem ghostExternReplaysS_of_linkedCallHookG_single_stub {α : Type}
    {InvMem : Memory → Prop} {Guard : State → Prop}
    {keep : BitVec 64 → Bool} {P_ghost P_real P_sub : Program}
    {stubPc entryTarget : BitVec 64} {spec : Spec α} {fallback : State → State}
    (hghost_stub : P_ghost.externAt? stubPc =
      some (linkedCallHookG Guard keep P_real P_sub entryTarget spec fallback))
    (hother : ∀ pc, pc ≠ stubPc → P_ghost.externAt? pc = P_real.externAt? pc)
    (hreal_pres : ∀ pc f, P_real.externAt? pc = some f →
      ∀ u : State, u.status = .Running → u.mem.KeepsFrozen (f u).mem →
        ExecFrozen u.mem → InvMem u.mem → ExecFrozen (f u).mem ∧ InvMem (f u).mem)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      P_sub.CodeLoaded (stripExecOutside keep m))
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    (hGuard : ∀ u : State, ExecFrozen u.mem → InvMem u.mem → Guard u)
    (hGuardStrip : ∀ s0 : State, ExecFrozen s0.mem → Guard s0 →
      Guard (stripS keep (s0.setPC entryTarget)))
    (hOk : subroutine_ok P_sub entryTarget (withStateGuard Guard spec))
    (hInv : SpecStripSInvariant keep spec)
    (hFsT : SpecPreservesFsTrace spec)
    (hPrePC : ∀ x (s : State) (pc : BitVec 64), spec.pre x (s.setPC pc) = spec.pre x s)
    (hOutPC : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome spec x R (s0.setPC pc) sf → SubroutineOutcome spec x R s0 sf) :
    GhostExternReplaysS keep (fun u => InvMem u.mem) P_ghost P_real :=
  ghostExternReplaysS_of_single_stub hghost_stub hother hreal_pres
    (ghostExternReplaysOn_of_linkedCallHookG hsvc_real hsvc_sub hreal_no hsub_no
      hreal_stub_none hStub hInvLoaded hInvKf hGuard hGuardStrip hOk hInv hFsT hPrePC hOutPC)

/-- Trajectory-aware single-stub `GhostExternReplaysOn` packager for `linkedCallHookG`
    (`LinkedCallHookOn.ghostExternReplaysOn_of_single_stub` also applies directly). -/
theorem ghostExternReplaysOn_of_linkedCallHookG_single_stub {α : Type}
    {InvMem : Memory → Prop} {Guard : State → Prop}
    {keep : BitVec 64 → Bool} {P_ghost P_real P_sub : Program} {s0 sf : State}
    {stubPc entryTarget : BitVec 64} {spec : Spec α} {fallback : State → State}
    (hghost_stub : P_ghost.externAt? stubPc =
      some (linkedCallHookG Guard keep P_real P_sub entryTarget spec fallback))
    (hother : ∀ pc, pc ≠ stubPc → P_ghost.externAt? pc = P_real.externAt? pc)
    (hreal_pres : ∀ pc f, P_real.externAt? pc = some f →
      ∀ u : State,
        Steps P_ghost s0 u →
        Steps P_ghost (f u) sf →
        u.pc = pc →
        u.status = .Running →
        (∀ msg, (f u).status ≠ .Exception msg) →
        u.mem.KeepsFrozen (f u).mem →
        ExecFrozen u.mem →
        InvMem u.mem →
        ExecFrozen (f u).mem ∧ InvMem (f u).mem)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      P_sub.CodeLoaded (stripExecOutside keep m))
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    (hGuard : ∀ u : State, ExecFrozen u.mem → InvMem u.mem → Guard u)
    (hGuardStrip : ∀ s0 : State, ExecFrozen s0.mem → Guard s0 →
      Guard (stripS keep (s0.setPC entryTarget)))
    (hOk : subroutine_ok P_sub entryTarget (withStateGuard Guard spec))
    (hInv : SpecStripSInvariant keep spec)
    (hFsT : SpecPreservesFsTrace spec)
    (hPrePC : ∀ x (s : State) (pc : BitVec 64), spec.pre x (s.setPC pc) = spec.pre x s)
    (hOutPC : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome spec x R (s0.setPC pc) sf → SubroutineOutcome spec x R s0 sf) :
    GhostExternReplaysOn keep (fun u => InvMem u.mem) P_ghost P_real s0 sf := by
  have ⟨hnone, hrep⟩ :=
    ghostExternReplaysOn_of_linkedCallHookG (fallback := fallback) hsvc_real hsvc_sub hreal_no
      hsub_no hreal_stub_none hStub hInvLoaded hInvKf hGuard hGuardStrip hOk hInv hFsT hPrePC hOutPC
  exact ghostExternReplaysOn_of_single_stub hghost_stub hother hreal_pres
    ⟨hnone, fun u _ _ hpc hrun hnoex _ hfr hlr hinv => hrep u hpc hrun hnoex hfr hlr hinv⟩

/-! ## 4. Concrete `.rodata` Table Guard (`roTableGuard`) & `↦ᵣ` Framing Bridges -/

/-- State guard asserting that `[tbl, tbl + bytes.length)` is mapped read-only (`Perm.ro`, not
    `lazyFree`) and holds `bytes` in `s.mem` (`HookDischarge.RustStd.Common.RoDataAt`). -/
@[expose] def roTableGuard (tbl : BitVec 64) (bytes : List (BitVec 8)) (s : State) : Prop :=
  RoDataAt s.mem tbl bytes

/-- `withStateGuard (roTableGuard tbl bytes) spec` is definitionally equal (`rfl`) to
    `HookDischarge.RustStd.Common.withRoData tbl bytes spec` (used by `FromUtf8` and
    `TimeDurationSince` bridges). -/
theorem withStateGuard_roTableGuard_eq_withRoData {α : Type}
    (tbl : BitVec 64) (bytes : List (BitVec 8)) (spec : Spec α) :
    withStateGuard (roTableGuard tbl bytes) spec = withRoData tbl bytes spec := rfl

private theorem readBytes_eq_of_ro_keepsFrozen {m m' : Memory} (hkf : m.KeepsFrozen m') :
    ∀ (n : Nat) (base : BitVec 64), m.RO base n → m'.readBytes base n = m.readBytes base n
  | 0, _, _ => rfl
  | n + 1, base, hro => by
    have h0 : InRegion base (n + 1) base := by
      simp [InRegion]
    have hfr0 : m.Frozen base := by
      rw [Memory.Frozen, (hro base h0).1]; rfl
    have hr0 : m'.read8 base = m.read8 base := (hkf base hfr0).1
    have hro_tail : m.RO (base + 1#64) n := by
      apply hro.sub
      have hsub : (base + 1#64) - base = 1#64 := by bv_arith
      rw [hsub]
      change 1 + n ≤ n + 1
      omega
    simp only [Memory.readBytes, hr0, readBytes_eq_of_ro_keepsFrozen hkf n (base + 1#64) hro_tail]

/-- `RoDataAt` is preserved by any `Memory.KeepsFrozen` transition (every `Perm.ro` byte is
    `Frozen`, so both its `Perm.ro` / `isLazyFree` status and its byte value are preserved). -/
theorem roDataAt_of_keepsFrozen {m m' : Memory} {tbl : BitVec 64} {bytes : List (BitVec 8)}
    (h : RoDataAt m tbl bytes) (hkf : m.KeepsFrozen m') :
    RoDataAt m' tbl bytes := by
  refine ⟨fun a ha => ?_, ?_⟩
  · obtain ⟨hpa, hlfa⟩ := h.1 a ha
    have hfr : m.Frozen a := by
      rw [Memory.Frozen, hpa]; rfl
    obtain ⟨_, hpeq, hlfeq, _⟩ := hkf a hfr
    exact ⟨hpeq.trans hpa, hlfeq.trans hlfa⟩
  · exact (readBytes_eq_of_ro_keepsFrozen hkf bytes.length tbl h.1).trans h.2

/-- State-level `KeepsFrozen` preservation of `roTableGuard`. -/
theorem roTableGuard_of_keepsFrozen {tbl : BitVec 64} {bytes : List (BitVec 8)} {s0 s1 : State}
    (h : roTableGuard tbl bytes s0) (hkf : s0.mem.KeepsFrozen s1.mem) :
    roTableGuard tbl bytes s1 :=
  roDataAt_of_keepsFrozen h hkf

private theorem readBytes_stripExecOutside (keep : BitVec 64 → Bool) (m : Memory) :
    ∀ (n : Nat) (base : BitVec 64),
      (stripExecOutside keep m).readBytes base n = m.readBytes base n
  | 0, _ => rfl
  | n + 1, base => by
    simp only [Memory.readBytes, strip_read8, readBytes_stripExecOutside keep m n (base + 1#64)]

/-- `RoDataAt` is unconditionally preserved by `stripExecOutside keep` (`Perm.ro` has `x = false`,
    so `stripPerm` acts as the identity on every byte of the `.rodata` table). -/
theorem roDataAt_stripExecOutside (keep : BitVec 64 → Bool) {m : Memory}
    {tbl : BitVec 64} {bytes : List (BitVec 8)}
    (h : RoDataAt m tbl bytes) :
    RoDataAt (stripExecOutside keep m) tbl bytes := by
  refine ⟨fun a ha => ?_, ?_⟩
  · obtain ⟨hpa, hlfa⟩ := h.1 a ha
    refine ⟨?_, (strip_isLazyFree keep m a).trans hlfa⟩
    rw [strip_perm, hpa]
    simp [Option.map, stripPerm, Perm.ro]
  · exact (readBytes_stripExecOutside keep m bytes.length tbl).trans h.2

/-- Ready-to-pass `hGuardStrip` witness for `roTableGuard tbl bytes`. -/
theorem roTableGuard_stripS (keep : BitVec 64 → Bool) (entryTarget tbl : BitVec 64)
    (bytes : List (BitVec 8)) (s0 : State) (_hFr : ExecFrozen s0.mem)
    (hG : roTableGuard tbl bytes s0) :
    roTableGuard tbl bytes (stripS keep (s0.setPC entryTarget)) :=
  roDataAt_stripExecOutside keep hG

/-- Separating `.rodata` introduction (left-adjoined `(tbl ↦ᵣ bytes) ∗ P ∗ R`): in `Arm64`'s
    separation logic, `↦ᵣ` is duplicable over `Memory.RO` via `Satisfies.rodata_intro`, so
    `roTableGuard tbl bytes s0` introduces `(tbl ↦ᵣ bytes)` alongside `P ∗ R` with the **exact same**
    frame `R` and zero disjointness side conditions (for `bytes.length ≤ 2 ^ 64`). -/
theorem roTableGuard_intro_sep_left {tbl : BitVec 64} {bytes : List (BitVec 8)}
    {P R : SepProp} {s0 : State}
    (hG : roTableGuard tbl bytes s0)
    (hlen : bytes.length ≤ 2 ^ 64 := by decide)
    (hPR : s0.mem ⊨ P ∗ R) :
    s0.mem ⊨ (tbl ↦ᵣ bytes) ∗ P ∗ R :=
  Satisfies.rodata_intro hG.1 hG.2 hlen hPR

/-- Separating `.rodata` introduction (`P ∗ (tbl ↦ᵣ bytes) ∗ R`, directly matching engine specs
    whose precondition has the shape `(p ↦ₛ bs) ∗ (tbl ↦ᵣ bytes)` with unchanged frame `R`). -/
theorem roTableGuard_intro_sep {tbl : BitVec 64} {bytes : List (BitVec 8)}
    {P R : SepProp} {s0 : State}
    (hG : roTableGuard tbl bytes s0)
    (hlen : bytes.length ≤ 2 ^ 64 := by decide)
    (hPR : s0.mem ⊨ P ∗ R) :
    s0.mem ⊨ P ∗ (tbl ↦ᵣ bytes) ∗ R := by
  have h := roTableGuard_intro_sep_left hG hlen hPR
  rwa [sepConj_left_comm (tbl ↦ᵣ bytes) P] at h

/-- Separating `.rodata` elimination on return: drops `(tbl ↦ᵣ bytes)` from `Q ∗ (tbl ↦ᵣ bytes) ∗ R`
    leaving `Q ∗ R`. -/
theorem roTableGuard_elim_sep {tbl : BitVec 64} {bytes : List (BitVec 8)}
    {Q R : SepProp} {sf : State}
    (hQR : sf.mem ⊨ Q ∗ (tbl ↦ᵣ bytes) ∗ R) :
    sf.mem ⊨ Q ∗ R := by
  rw [sepConj_left_comm Q (tbl ↦ᵣ bytes)] at hQR
  exact Satisfies.of_sep_right hQR

/-- Lower any region-local `subroutine_ok` stated with separating `withRoDataSep tbl bytes spec`
    (for arbitrary `onPanic` / `onExit` / `onOom`) to `withStateGuard (roTableGuard tbl bytes) spec`. -/
theorem subroutine_ok_withStateGuard_roTableGuard_of_sep {α : Type}
    {P_sub : Program} {entryTarget tbl : BitVec 64} {bytes : List (BitVec 8)} {spec : Spec α}
    (hlen : bytes.length ≤ 2 ^ 64)
    (h : subroutine_ok P_sub entryTarget (withRoDataSep tbl bytes spec)) :
    subroutine_ok P_sub entryTarget (withStateGuard (roTableGuard tbl bytes) spec) :=
  (SpecSimulates.withRoData_of_sep hlen).subroutine_ok h

/-- Ready-to-call `HookOk` for `linkedCallHookG (roTableGuard tbl bytes) …` from a `withRoData`
    real-code proof (such as `coreFromUtf8_fromUtf8AsciiSpec_ok` or
    `timeDurationSince_boundedSpec_ok`), discharging `hGuardStrip` automatically. -/
theorem hookOk_linkedCallHookG_roTable {α : Type}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget tbl : BitVec 64} {bytes : List (BitVec 8)}
    {spec : Spec α} {fallback : State → State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hOk : subroutine_ok P_sub entryTarget (withRoData tbl bytes spec))
    (hInv : SpecStripSInvariant keep spec)
    (hFsT : SpecPreservesFsTrace spec)
    (hPrePC : ∀ x (s : State) (pc : BitVec 64), spec.pre x (s.setPC pc) = spec.pre x s)
    (hOutPC : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome spec x R (s0.setPC pc) sf → SubroutineOutcome spec x R s0 sf)
    (hFallbackOk : HookOk (keepFsTrace fallback) spec) :
    HookOk (linkedCallHookG (roTableGuard tbl bytes) keep P_real P_sub entryTarget spec fallback)
      spec :=
  hookOk_linkedCallHookG hsvc_real hsvc_sub hreal_no hsub_no
    (roTableGuard_stripS keep entryTarget tbl bytes) hOk hInv hFsT hPrePC hOutPC hFallbackOk

/-- Ready-to-call `On`/`S` replay for `linkedCallHookG (roTableGuard tbl bytes) …` from a
    `withRoData` real-code proof and `hRoInv : ∀ m, ExecFrozen m → InvMem m → RoDataAt m tbl bytes`. -/
theorem ghostExternReplaysOn_of_linkedCallHookG_roTable {α : Type}
    {InvMem : Memory → Prop}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {stubPc entryTarget tbl : BitVec 64} {bytes : List (BitVec 8)}
    {spec : Spec α} {fallback : State → State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      P_sub.CodeLoaded (stripExecOutside keep m))
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    (hRoInv : ∀ m : Memory, ExecFrozen m → InvMem m → RoDataAt m tbl bytes)
    (hOk : subroutine_ok P_sub entryTarget (withRoData tbl bytes spec))
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
        (linkedCallHookG (roTableGuard tbl bytes) keep P_real P_sub entryTarget spec fallback u).status ≠
          .Exception msg) →
      ExecFrozen u.mem →
      keep (u.readReg64 .lr) = false →
      InvMem u.mem →
      Steps P_real u
        (linkedCallHookG (roTableGuard tbl bytes) keep P_real P_sub entryTarget spec fallback u) ∧
      ExecFrozen
        (linkedCallHookG (roTableGuard tbl bytes) keep P_real P_sub entryTarget spec fallback u).mem ∧
      InvMem
        (linkedCallHookG (roTableGuard tbl bytes) keep P_real P_sub entryTarget spec fallback u).mem :=
  ghostExternReplaysOn_of_linkedCallHookG hsvc_real hsvc_sub hreal_no hsub_no hreal_stub_none
    hStub hInvLoaded hInvKf (fun u hfr hinv => hRoInv u.mem hfr hinv)
    (roTableGuard_stripS keep entryTarget tbl bytes) hOk hInv hFsT hPrePC hOutPC

/-- Conditional `StepsUntil` `P_run → P_real` replay specialized to `roTableGuard tbl bytes`
    (for stock-ELF `W`-polymorphic row ghosts, prefer
    `ghostExternReplaysOn_of_linkedCallHookG_roTable_liftVis` below). -/
theorem ghostExternReplaysOn_of_linkedCallHookG_roTable_lift {α : Type}
    {InvMem : Memory → Prop}
    {keep : BitVec 64 → Bool} {P_run P_real P_sub : Program}
    {stubPc entryTarget tbl : BitVec 64} {bytes : List (BitVec 8)}
    {spec : Spec α} {fallback : State → State}
    (hsvc_run : P_run.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hrun_no : ∀ pc, keep pc = true → P_run.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hLift : ∀ u sf : State,
      ExecFrozen u.mem → InvMem u.mem → keep (u.readReg64 .lr) = false →
      StepsUntil P_run (SubroutineStop u) (u.setPC entryTarget) sf →
      SubroutineStop u sf →
      Steps P_real (u.setPC entryTarget) sf)
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      P_sub.CodeLoaded (stripExecOutside keep m))
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    (hRoInv : ∀ m : Memory, ExecFrozen m → InvMem m → RoDataAt m tbl bytes)
    (hOk : subroutine_ok P_sub entryTarget (withRoData tbl bytes spec))
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
        (linkedCallHookG (roTableGuard tbl bytes) keep P_run P_sub entryTarget spec fallback u).status ≠
          .Exception msg) →
      ExecFrozen u.mem →
      keep (u.readReg64 .lr) = false →
      InvMem u.mem →
      Steps P_real u
        (linkedCallHookG (roTableGuard tbl bytes) keep P_run P_sub entryTarget spec fallback u) ∧
      ExecFrozen
        (linkedCallHookG (roTableGuard tbl bytes) keep P_run P_sub entryTarget spec fallback u).mem ∧
      InvMem
        (linkedCallHookG (roTableGuard tbl bytes) keep P_run P_sub entryTarget spec fallback u).mem :=
  ghostExternReplaysOn_of_linkedCallHookG_lift hsvc_run hsvc_sub hrun_no hsub_no hreal_stub_none
    hStub hLift hInvLoaded hInvKf (fun u hfr hinv => hRoInv u.mem hfr hinv)
    (roTableGuard_stripS keep entryTarget tbl bytes) hOk hInv hFsT hPrePC hOutPC

/-- **Stock-safe `StepsVisitedIn` `P_run → P_real` replay specialized to `roTableGuard tbl bytes`:**
    Replays a `W`-independent ghost hook defined against `P_run` (`emptyStdProg` / `hole2_emptyProg`)
    onto `P_real` from a `withRoData tbl bytes spec` real-code proof, `hRoInv`, and `hLiftVis`
    (discharged on stock via `h2sl_steps_realW_of_visitedIn_keepSub` + `stepsVisitedIn_mono`). -/
theorem ghostExternReplaysOn_of_linkedCallHookG_roTable_liftVis {α : Type}
    {InvMem : Memory → Prop}
    {keep : BitVec 64 → Bool} {P_run P_real P_sub : Program}
    {stubPc entryTarget tbl : BitVec 64} {bytes : List (BitVec 8)}
    {spec : Spec α} {fallback : State → State}
    (hsvc_run : P_run.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hrun_no : ∀ pc, keep pc = true → P_run.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hLiftVis : ∀ u sf : State,
      u.status = .Running → ExecFrozen u.mem → InvMem u.mem →
      h2fsgen_StepsVisitedIn keep P_run (u.setPC entryTarget) sf →
      Steps P_real (u.setPC entryTarget) sf)
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      P_sub.CodeLoaded (stripExecOutside keep m))
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    (hRoInv : ∀ m : Memory, ExecFrozen m → InvMem m → RoDataAt m tbl bytes)
    (hOk : subroutine_ok P_sub entryTarget (withRoData tbl bytes spec))
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
        (linkedCallHookG (roTableGuard tbl bytes) keep P_run P_sub entryTarget spec fallback u).status ≠
          .Exception msg) →
      ExecFrozen u.mem →
      keep (u.readReg64 .lr) = false →
      InvMem u.mem →
      Steps P_real u
        (linkedCallHookG (roTableGuard tbl bytes) keep P_run P_sub entryTarget spec fallback u) ∧
      ExecFrozen
        (linkedCallHookG (roTableGuard tbl bytes) keep P_run P_sub entryTarget spec fallback u).mem ∧
      InvMem
        (linkedCallHookG (roTableGuard tbl bytes) keep P_run P_sub entryTarget spec fallback u).mem :=
  ghostExternReplaysOn_of_linkedCallHookG_liftVis hsvc_run hsvc_sub hrun_no hsub_no hreal_stub_none
    hStub hLiftVis hInvLoaded hInvKf (fun u hfr hinv => hRoInv u.mem hfr hinv)
    (roTableGuard_stripS keep entryTarget tbl bytes) hOk hInv hFsT hPrePC hOutPC

/-! ## 5. Smoke Instance (`Guard := fun _ => True`) -/

/-- Any unguarded `subroutine_ok` immediately lifts to `withStateGuard (fun _ => True) spec`. -/
theorem subroutine_ok_withStateGuard_true {α : Type}
    {P_sub : Program} {entryTarget : BitVec 64} {spec : Spec α}
    (hOk : subroutine_ok P_sub entryTarget spec) :
    subroutine_ok P_sub entryTarget (withStateGuard (fun _ => True) spec) := by
  apply subroutine_ok.of_codeLoaded
  intro x R s0 hpc hrun hpre hsp _hL
  dsimp only [withStateGuard] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hOk.mono_outcome x R s0 hpc hrun hpre.2 hsp (fun _ hout => hout)

/-- **Smoke equality (`Guard := fun _ => True`):**
    `linkedCallHookG (fun _ => True)` is extensionally equal to `linkedCallHook`, so existing
    unguarded users (`memset`, `memcpy`) instantiate `linkedCallHookG` seamlessly. -/
theorem linkedCallHookG_true_eq {α : Type}
    (keep : BitVec 64 → Bool) (P_real P_sub : Program)
    (entryTarget : BitVec 64) (spec : Spec α) (fallback : State → State) :
    linkedCallHookG (fun _ => True) keep P_real P_sub entryTarget spec fallback =
      linkedCallHook keep P_real P_sub entryTarget spec fallback := by
  funext s0
  exact linkedCallHookG_eq_of_guard trivial

/-- Smoke instantiation of `hookOk_linkedCallHookG` at `Guard := fun _ => True`, recovering
    `AllocGhostLinkTransfer.linkedCallHook_ok` via `linkedCallHookG_true_eq`. -/
theorem hookOk_linkedCallHook_via_G {α : Type}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64} {spec : Spec α} {fallback : State → State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hOk : subroutine_ok P_sub entryTarget spec)
    (hInv : SpecStripSInvariant keep spec)
    (hFsT : SpecPreservesFsTrace spec)
    (hPrePC : ∀ x (s : State) (pc : BitVec 64), spec.pre x (s.setPC pc) = spec.pre x s)
    (hOutPC : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome spec x R (s0.setPC pc) sf → SubroutineOutcome spec x R s0 sf)
    (hFallbackOk : HookOk (keepFsTrace fallback) spec) :
    HookOk (linkedCallHook keep P_real P_sub entryTarget spec fallback) spec := by
  rw [← linkedCallHookG_true_eq]
  exact hookOk_linkedCallHookG hsvc_real hsvc_sub hreal_no hsub_no
    (fun _ _ _ => trivial) (subroutine_ok_withStateGuard_true hOk)
    hInv hFsT hPrePC hOutPC hFallbackOk

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookG

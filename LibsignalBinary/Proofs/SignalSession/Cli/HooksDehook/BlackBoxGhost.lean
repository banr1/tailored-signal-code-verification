/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BlackBoxCode -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric -- proof-setup: allow-public-import

/-!
# Ghost `black_box::<u8>` Hooks, `HookOk` Suite & Stock-Safe `StepsVisitedIn` Replays (`HooksDehook.BlackBoxGhost`)

Stage `b` (`Card D1-b`) per-row ghost hooks for `subtle::black_box::<u8>` (`lsBlackBoxSym` /
`lsBlackBoxU8Sym`, 5-word `blackBoxU8Words`, 16-byte stack frame), parallel to
`HooksDehook.MemsetGhost`, `HooksDehook.MemsetGhostK`, and `HooksDehook.ZeroizeGhost`:

1. **Ghost `black_box::<u8>` hooks (`blackBoxGhostHook{,K}`, `f3EmptyBlackBoxGhostHook{,K}`)**:
   - `blackBoxGhostHook keep P_real P_sub entryTarget`: wraps `masterBlackBoxSpec` via
     `linkedCallHook` with `W`-independent fallback `LibsignalSession.blackBoxHook`.
   - `blackBoxGhostHookK keep P_real P_sub entryTarget`: wraps `blackBoxSpecK keep masterBlackBoxSpec`.
   - `f3EmptyBlackBoxGhostHook{,K} keep P_sub entryTarget`: `W`-independent `f3LinkedCallHook` forms
     at `P_real := emptyStdProg`, bridged to `blackBoxGhostHook{,K}` via
     `f3LinkedCallHook_const_eq_linkedCallHook`.
2. **Pointwise C11 §8.1 bundle properties**:
   Proves `.fs = s.fs`, `HookFsTraced IsFsC`, `.trace = s.trace`, `VmPreserved` (via Stage `a1`
   `processBlackBoxSpec` + `ExecFrozen` + `KeepsFrozen`), `OomPreserved ∧ PoolPreserved`,
   `ExecFrozen`-preservation, `keep lr = false` extraction on `K`, and `keep lr = true` branch
   equations once under generic `hsub_proc : subroutine_ok P_sub entryTarget processBlackBoxSpec`,
   then specializes to `P_sub.hasWords entryTarget blackBoxU8Words`.
3. **Complete consumer `HookOk` suite (including C11 `withAlloc` pool-framed lifts)**:
   Lifts `masterBlackBoxSpec` + `VmPreserved` + `.fs` across every honest (`16 ≤ hookStack ≤ 2 ^ 64`)
   consumer contract in `HooksDehook.BlackBoxCode` (`withStack blackBoxSpec 16`,
   `withStack blackBoxSpec hookStack`, `withStack blackBoxU8Spec hookStack`,
   `cliBlackBoxSpec hookStack`, `CliExt.blackBoxSpec` / `CtEq.blackBoxSpec32`, `.keepsFs`,
   `withFsPred`, `withVmPreserved`, `withAlloc`, `withExecFrozen`, and `blackBoxSpecK`).
4. **Stock-safe `StepsVisitedIn` execution & replay bridges**:
   Uses `h2fsgen_StepsVisitedIn` pinned via `h2fsgen_stepsUntil_det` and `hLiftVis` premises ONLY
   (never legacy `StepsUntil` lifts or `h2fsgen_HooksUnfetched`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BlackBoxGhost

open Arm64 ProofLib SepProp
open Arm64.Process (pureWordsProg)
open CryptoVerification.LibsignalSession (blackBoxHook)
open CryptoVerification.LibsignalTripleRatchet (withStack extHookStack)
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC)
open CryptoVerification.SignalSession.Cli.MainHops (hookOk_withStack)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget FdsHiFrame VmPreserved OomPreserved PoolPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Heap.Fine (blackBoxHook_vmPreserved)
open LibsignalBinary.Proofs.HookDischarge.Generics.ZeroizeDrop (withFsPred)
open LibsignalBinary.Proofs.HookDischarge.Generics.BlackBoxU8 (blackBoxU8Words cliBlackBoxSpec blackBoxU8Spec)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc (
  withAlloc hookOk_withAlloc_of_withVmPreserved hookOk_withAlloc_withVmPreserved
)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget (hookOk_withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  ExecFrozen satisfies_stripExecOutside stepsUntil_of_stripS_standard
  SpecStripSInvariant SpecPreservesFsTrace keepFsTrace keepFsTrace_fs ActiveRealPre ActiveRealRun
  linkedCallHook linkedCallHook_fs linkedCallHook_fsT linkedCallHook_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks (
  ActiveF3CallPre f3LinkedCallHook f3LinkedCallHook_fs f3LinkedCallHook_fsT
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer (
  GhostExternReplaysOn GhostExternReplaysS StubReachesTargetOn
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookOn (
  ghostExternReplaysOn_of_single_stub ghostExternReplaysS_of_single_stub
  linkedCallHook_activeRealPre_of_noException
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode (
  memsetSpecK pureWordsProg_externAt_none hookOk_memsetSpecK_of_plain
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost (withExecFrozen hookOk_withExecFrozen_of_plain)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK (
  emptyStdProg emptyStdProg_svc emptyStdProg_externAt_none
  activeF3CallPre_const_iff f3LinkedCallHook_const_eq_linkedCallHook
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeCode (
  hookOk_zeroizeSpecK_withFsPred_of_keepsFs
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BlackBoxCode (
  BlackBoxStatePreserved masterBlackBoxSpec processBlackBoxSpec masterBlackBoxBudgetSpec blackBoxSpecK
  pureWordsProg_blackBoxU8_hasWords processBlackBox_pre_of_masterBlackBox_pre
  subroutine_ok_processBlackBox_of_hasWords
  blackBoxHook_masterBlackBox_ok blackBoxHook_masterBlackBoxK_ok
  hookOk_sessionBlackBox16_of_master hookOk_sessionBlackBox16K_of_master
  hookOk_sessionBlackBox_of_master hookOk_sessionBlackBoxK_of_master
  hookOk_sessionBlackBox_keepsFs_of_master
  hookOk_blackBoxU8_of_master hookOk_blackBoxU8K_of_master
  hookOk_cliBlackBox_of_master hookOk_cliBlackBoxK_of_master
  hookOk_extBlackBox_of_master hookOk_extBlackBoxK_of_master
  hookOk_extBlackBox_keepsFs_of_master hookOk_extBlackBox_withFsPred_of_master
  hookOk_sessionBlackBox16Budget_of_masterBudget hookOk_sessionBlackBox16Budget_of_master
  hookOk_sessionBlackBoxBudget_of_masterBudget hookOk_sessionBlackBoxBudget_of_master
  hookOk_vmSessionBlackBox_of_master
  hookOk_blackBoxU8Budget_of_masterBudget hookOk_blackBoxU8Budget_of_master
  hookOk_extBlackBoxBudget_of_master hookOk_extBlackBoxBudgetK_of_master
  hookOk_extBlackBoxBudget_keepsFs_of_master hookOk_extBlackBoxBudget_withFsPred_of_master
  blackBoxSpecK_keepsFs blackBoxSpecK_withVmPreserved
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric (
  h2fsgen_StepsVisitedIn h2fsgen_stepsUntil_det h2fsgen_real_subroutine_run_visitedIn_of_stripS
)

/-! ## 1. Ghost `black_box::<u8>` Hook Definitions & `f3Empty` Bridges -/

/-- Plain ghost `black_box::<u8>` hook wrapping `masterBlackBoxSpec` with fallback `blackBoxHook`. -/
@[expose] noncomputable def blackBoxGhostHook (keep : BitVec 64 → Bool) (P_real P_sub : Program)
    (entryTarget : BitVec 64) : State → State :=
  linkedCallHook keep P_real P_sub entryTarget masterBlackBoxSpec blackBoxHook

/-- `K`-narrowed ghost `black_box::<u8>` hook wrapping `blackBoxSpecK keep masterBlackBoxSpec`. -/
@[expose] noncomputable def blackBoxGhostHookK (keep : BitVec 64 → Bool) (P_real P_sub : Program)
    (entryTarget : BitVec 64) : State → State :=
  linkedCallHook keep P_real P_sub entryTarget (blackBoxSpecK keep masterBlackBoxSpec) blackBoxHook

/-- Plain `W`-independent K-convention `black_box::<u8>` ghost hook (`P_real := emptyStdProg`). -/
@[expose] noncomputable def f3EmptyBlackBoxGhostHook (keep : BitVec 64 → Bool) (P_sub : Program)
    (entryTarget : BitVec 64) : State → State :=
  f3LinkedCallHook keep emptyStdProg P_sub entryTarget (fun _ _ => masterBlackBoxSpec) blackBoxHook

/-- `K`-narrowed `W`-independent K-convention `black_box::<u8>` ghost hook (`P_real := emptyStdProg`). -/
@[expose] noncomputable def f3EmptyBlackBoxGhostHookK (keep : BitVec 64 → Bool) (P_sub : Program)
    (entryTarget : BitVec 64) : State → State :=
  f3LinkedCallHook keep emptyStdProg P_sub entryTarget (fun _ _ => blackBoxSpecK keep masterBlackBoxSpec) blackBoxHook

theorem f3EmptyBlackBoxGhostHook_eq (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) :
    f3EmptyBlackBoxGhostHook keep P_sub entryTarget = blackBoxGhostHook keep emptyStdProg P_sub entryTarget :=
  f3LinkedCallHook_const_eq_linkedCallHook keep emptyStdProg P_sub entryTarget masterBlackBoxSpec blackBoxHook

theorem f3EmptyBlackBoxGhostHookK_eq (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) :
    f3EmptyBlackBoxGhostHookK keep P_sub entryTarget = blackBoxGhostHookK keep emptyStdProg P_sub entryTarget :=
  f3LinkedCallHook_const_eq_linkedCallHook keep emptyStdProg P_sub entryTarget (blackBoxSpecK keep masterBlackBoxSpec) blackBoxHook

noncomputable abbrev blackBoxGhostHookPure5 (keep : BitVec 64 → Bool) (P_real : Program) (entry : BitVec 64) : State → State :=
  blackBoxGhostHook keep P_real (pureWordsProg entry blackBoxU8Words) entry

noncomputable abbrev blackBoxGhostHookPure5K (keep : BitVec 64 → Bool) (P_real : Program) (entry : BitVec 64) : State → State :=
  blackBoxGhostHookK keep P_real (pureWordsProg entry blackBoxU8Words) entry

/-! ## 2. `SpecStripSInvariant`, `SpecPreservesFsTrace`, PC Invariance & `processBlackBoxSpec` Lifts -/

theorem specStripSInvariant_masterBlackBox (keep : BitVec 64 → Bool) :
    SpecStripSInvariant keep masterBlackBoxSpec where
  pre_eq := fun _ s => by cases s; rfl
  post_eq := fun _ s0 sf => by cases s0; cases sf; rfl
  onPanic_eq := fun _ _ _ => rfl
  onExit_eq := fun _ _ _ _ => rfl
  onOom_eq := fun _ _ _ => rfl

theorem specStripSInvariant_masterBlackBoxK (keep : BitVec 64 → Bool) :
    SpecStripSInvariant keep (blackBoxSpecK keep masterBlackBoxSpec) where
  pre_eq := fun _ s => by cases s; rfl
  post_eq := fun _ s0 sf => by cases s0; cases sf; rfl
  onPanic_eq := fun _ _ _ => rfl
  onExit_eq := fun _ _ _ _ => rfl
  onOom_eq := fun _ _ _ => rfl

theorem specPreservesFsTrace_masterBlackBox : SpecPreservesFsTrace masterBlackBoxSpec := by
  intro v R s0 sf hout
  rcases hout with ⟨_, _, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · dsimp only [masterBlackBoxSpec] at hpost; rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact ⟨hpost.1.2.1, FsTraced.of_eq hpost.1.2.2.1 (congrArg FsState.files hpost.1.2.1)⟩
  · dsimp only [masterBlackBoxSpec] at hpan; rw [satisfies_pure_sepConj] at hpan; exact False.elim hpan.1
  · dsimp only [masterBlackBoxSpec] at hex; rw [satisfies_pure_sepConj] at hex; exact False.elim hex.1
  · dsimp only [masterBlackBoxSpec] at hoom; rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

theorem specPreservesFsTrace_masterBlackBoxK (keep : BitVec 64 → Bool) :
    SpecPreservesFsTrace (blackBoxSpecK keep masterBlackBoxSpec) := specPreservesFsTrace_masterBlackBox

theorem masterBlackBox_pre_setPC (v : BitVec 64) (s : State) (pc : BitVec 64) :
    masterBlackBoxSpec.pre v (s.setPC pc) = masterBlackBoxSpec.pre v s := by cases s; rfl

theorem masterBlackBoxK_pre_setPC (keep : BitVec 64 → Bool) (v : BitVec 64) (s : State) (pc : BitVec 64) :
    (blackBoxSpecK keep masterBlackBoxSpec).pre v (s.setPC pc) =
      (blackBoxSpecK keep masterBlackBoxSpec).pre v s := by cases s; rfl

theorem masterBlackBox_outcome_setPC (v : BitVec 64) (R : SepProp) (s0 sf : State) (pc : BitVec 64)
    (h : SubroutineOutcome masterBlackBoxSpec v R (s0.setPC pc) sf) :
    SubroutineOutcome masterBlackBoxSpec v R s0 sf := by cases s0; cases sf; exact h

theorem masterBlackBoxK_outcome_setPC (keep : BitVec 64 → Bool) (v : BitVec 64) (R : SepProp)
    (s0 sf : State) (pc : BitVec 64)
    (h : SubroutineOutcome (blackBoxSpecK keep masterBlackBoxSpec) v R (s0.setPC pc) sf) :
    SubroutineOutcome (blackBoxSpecK keep masterBlackBoxSpec) v R s0 sf := by cases s0; cases sf; exact h

theorem keepFsTrace_blackBoxHook_eq (s0 : State) :
    keepFsTrace blackBoxHook s0 = blackBoxHook s0 := by cases s0; rfl

theorem keepFsTrace_blackBoxHook_master_ok : HookOk (keepFsTrace blackBoxHook) masterBlackBoxSpec := by
  rw [funext keepFsTrace_blackBoxHook_eq]; exact blackBoxHook_masterBlackBox_ok

theorem keepFsTrace_blackBoxHook_masterK_ok (keep : BitVec 64 → Bool) :
    HookOk (keepFsTrace blackBoxHook) (blackBoxSpecK keep masterBlackBoxSpec) := by
  rw [funext keepFsTrace_blackBoxHook_eq]; exact blackBoxHook_masterBlackBoxK_ok keep

theorem blackBoxHook_preserves_oom_pool (s0 : State) :
    OomPreserved s0 (blackBoxHook s0) ∧ PoolPreserved s0 (blackBoxHook s0) := by
  unfold blackBoxHook retHook; exact ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

theorem blackBoxHook_preserves_execFrozen {s0 : State} (hfr : ExecFrozen s0.mem) :
    ExecFrozen (blackBoxHook s0).mem := hfr

theorem subroutine_ok_masterBlackBox_of_process {P_sub : Program} {entryTarget : BitVec 64}
    (hsub_proc : subroutine_ok P_sub entryTarget processBlackBoxSpec) :
    subroutine_ok P_sub entryTarget masterBlackBoxSpec := by
  refine subroutine_ok_mono hsub_proc (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [processBlackBoxSpec, masterBlackBoxSpec] at hq ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  exact ⟨⟨hq.1.1, BlackBoxStatePreserved.of_processFieldsPreserved hq.1.2⟩, hq.2⟩

theorem subroutine_ok_masterBlackBoxK_of_process (keep : BitVec 64 → Bool) {P_sub : Program} {entryTarget : BitVec 64}
    (hsub_proc : subroutine_ok P_sub entryTarget processBlackBoxSpec) :
    subroutine_ok P_sub entryTarget (blackBoxSpecK keep masterBlackBoxSpec) := by
  refine subroutine_ok_mono (subroutine_ok_masterBlackBox_of_process hsub_proc) (fun _ _ _ hp => ?_) (fun _ _ _ _ hq => hq)
  dsimp only [blackBoxSpecK, memsetSpecK] at hp; rw [sepConj_assoc, satisfies_pure_sepConj] at hp; exact hp.2

/-! ## 3. Master `HookOk` & Pointwise State Preservation (`VmPreserved`, `OomPreserved`, `fs`, `ExecFrozen`) -/

private theorem perm_eq_of_stripExecOutside_keepsFrozen {keep : BitVec 64 → Bool} {m0 mf : Memory}
    (hfr0 : ExecFrozen m0) (hfrf : ExecFrozen mf) (hkf : m0.KeepsFrozen mf)
    (hstrip : ∀ a : BitVec 64, (stripExecOutside keep mf).perm a = (stripExecOutside keep m0).perm a) :
    ∀ a : BitVec 64, mf.perm a = m0.perm a := by
  intro a
  have hst := hstrip a
  rw [strip_perm, strip_perm] at hst
  have hfr0_a := hfr0 a
  have hfrf_a := hfrf a
  by_cases hfrozen0 : m0.Frozen a
  · exact (hkf a hfrozen0).2.1
  · unfold Memory.Frozen Option.frozen Perm.frozen at hfrozen0
    cases hp0 : m0.perm a with
    | none =>
      cases hpf : mf.perm a with
      | none => rfl
      | some pf => rw [hp0, hpf] at hst; simp [Option.map] at hst
    | some p0 =>
      cases hpf : mf.perm a with
      | none => rw [hp0, hpf] at hst; simp [Option.map] at hst
      | some pf =>
        rw [hp0] at hfr0_a hfrozen0 hst; rw [hpf] at hfrf_a hst
        rcases p0 with ⟨r0, w0, x0, lf0, an0⟩; rcases pf with ⟨rf, wf, xf, lff, anf⟩
        unfold stripPerm at hst
        cases hk : keep a <;> cases r0 <;> cases w0 <;> cases x0 <;>
          cases rf <;> cases wf <;> cases xf <;> simp_all [Option.map, Option.x, Option.r, Option.w]

private theorem subroutineStop_of_processBlackBoxOutcome {v : BitVec 64} {R : SepProp} {s0 sf : State}
    (h : SubroutineOutcome processBlackBoxSpec v R s0 sf) :
    SubroutineStop s0 sf ∧ sf.status ≠ .Halted := by
  rcases h with ⟨hret, _, _⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine ⟨Or.inl hret, ?_⟩; rw [hret.2.2]; decide
  · dsimp only [processBlackBoxSpec] at hpan; rw [satisfies_pure_sepConj] at hpan; exact False.elim hpan.1
  · dsimp only [processBlackBoxSpec] at hex; rw [satisfies_pure_sepConj] at hex; exact False.elim hex.1
  · dsimp only [processBlackBoxSpec] at hoom; rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

private theorem activeRealRun_processBlackBox {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64} (hsvc_real : P_real.svc = Syscall.standard) (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none) (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hsub_proc : subroutine_ok P_sub entryTarget processBlackBoxSpec) {v : BitVec 64} {R : SepProp} {s0 : State}
    (hrun : s0.status = .Running) (hsp : s0.spAligned = true) (hpreM : s0.mem ⊨ masterBlackBoxSpec.pre v s0 ∗ R)
    (hReal : ActiveRealRun keep P_real P_sub entryTarget s0) :
    ProcessFieldsPreserved s0 (Classical.choose hReal.2.2.2) := by
  have hpre : s0.mem ⊨ processBlackBoxSpec.pre v s0 ∗ R := processBlackBox_pre_of_masterBlackBox_pre hpreM
  let s1 := s0.setPC entryTarget
  let s1' := stripS keep s1
  have hs1_pre : s1.mem ⊨ processBlackBoxSpec.pre v s1 ∗ R := by cases s0; exact hpre
  have hs1'_pre : s1'.mem ⊨ processBlackBoxSpec.pre v s1' ∗ R := by
    have hsat := satisfies_stripExecOutside keep hs1_pre
    have heq : processBlackBoxSpec.pre v s1' = processBlackBoxSpec.pre v s1 := by dsimp only [s1']; cases s1; rfl
    rwa [heq]
  obtain ⟨sf', hsteps', hout'⟩ :=
    subroutine_ok_elim_steps_outcome hsub_proc v R s1' rfl hrun hs1'_pre hsp hReal.2.2.1
  obtain ⟨hstop1', hnhalt'⟩ := subroutineStop_of_processBlackBoxOutcome hout'
  have hstop0' : SubroutineStop s0 sf' := hstop1'
  obtain ⟨sf, huntil, hstop_sf, hsf_eq, hfr_sf⟩ :=
    stepsUntil_of_stripS_standard (s0 := s0) hsvc_real hsvc_sub hreal_no
      (fun pc f he => nomatch hsub_no pc ▸ he) hReal.2.1 hsteps' hstop0' hnhalt' s1 rfl hReal.1
  have hchoose := Classical.choose_spec hReal.2.2.2
  have hdet : Classical.choose hReal.2.2.2 = sf :=
    StepsUntil.deterministic hchoose.1 hchoose.2.1 huntil hstop_sf
  rw [hdet]
  rcases hout' with ⟨_, _, hpost'⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · dsimp only [processBlackBoxSpec] at hpost'; rw [sepConj_assoc, satisfies_pure_sepConj] at hpost'
    have hproc' : ProcessFieldsPreserved s1' sf' := hpost'.1.2
    rw [hsf_eq] at hproc'
    have hperm : ∀ addr, sf.mem.perm addr = s0.mem.perm addr :=
      perm_eq_of_stripExecOutside_keepsFrozen hReal.1 hfr_sf huntil.toSteps.keepsFrozen hproc'.2.2.2.2.2.2.2
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hperm⟩
    · cases s0; cases sf; exact hproc'.1
    · cases s0; cases sf; exact hproc'.2.1
    · cases s0; cases sf; exact hproc'.2.2.1
    · cases s0; cases sf; exact hproc'.2.2.2.1
    · cases s0; cases sf; exact hproc'.2.2.2.2.1
    · cases s0; cases sf; exact hproc'.2.2.2.2.2.1
    · cases s0; cases sf; exact hproc'.2.2.2.2.2.2.1
  · dsimp only [processBlackBoxSpec] at hpan; rw [satisfies_pure_sepConj] at hpan; exact False.elim hpan.1
  · dsimp only [processBlackBoxSpec] at hex; rw [satisfies_pure_sepConj] at hex; exact False.elim hex.1
  · dsimp only [processBlackBoxSpec] at hoom; rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

private theorem vmPreserved_of_processFieldsPreserved {s0 sf : State} (h : ProcessFieldsPreserved s0 sf) :
    VmPreserved s0 sf :=
  ⟨⟨h.2.2.2.2.2.1, h.2.2.2.2.1, h.2.2.1⟩, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2, FdsHiFrame.of_fs_eq h.1⟩

private theorem oomPoolPreserved_of_processFieldsPreserved {s0 sf : State} (h : ProcessFieldsPreserved s0 sf) :
    OomPreserved s0 sf ∧ PoolPreserved s0 sf :=
  ⟨⟨h.1, h.2.1, h.2.2.2.1⟩, ⟨h.2.2.2.2.2.1, h.2.2.2.2.1, h.2.2.1⟩⟩

-- 3.1 Unconditional `.fs`, `HookFsTraced`, `ExecFrozen`, and `lr` branch properties:

theorem blackBoxGhostHook_fs (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entryTarget : BitVec 64) (s0 : State) :
    (blackBoxGhostHook keep P_real P_sub entryTarget s0).fs = s0.fs :=
  linkedCallHook_fs keep P_real P_sub entryTarget masterBlackBoxSpec blackBoxHook s0

theorem blackBoxGhostHookK_fs (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entryTarget : BitVec 64) (s0 : State) :
    (blackBoxGhostHookK keep P_real P_sub entryTarget s0).fs = s0.fs :=
  linkedCallHook_fs keep P_real P_sub entryTarget (blackBoxSpecK keep masterBlackBoxSpec) blackBoxHook s0

theorem f3EmptyBlackBoxGhostHook_fs (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) (s0 : State) :
    (f3EmptyBlackBoxGhostHook keep P_sub entryTarget s0).fs = s0.fs :=
  f3LinkedCallHook_fs keep emptyStdProg P_sub entryTarget (fun _ _ => masterBlackBoxSpec) blackBoxHook s0

theorem f3EmptyBlackBoxGhostHookK_fs (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) (s0 : State) :
    (f3EmptyBlackBoxGhostHookK keep P_sub entryTarget s0).fs = s0.fs :=
  f3LinkedCallHook_fs keep emptyStdProg P_sub entryTarget (fun _ _ => blackBoxSpecK keep masterBlackBoxSpec) blackBoxHook s0

theorem blackBoxGhostHook_fsT (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entryTarget : BitVec 64) :
    HookFsTraced IsFsC (blackBoxGhostHook keep P_real P_sub entryTarget) :=
  linkedCallHook_fsT keep P_real P_sub entryTarget masterBlackBoxSpec blackBoxHook

theorem blackBoxGhostHookK_fsT (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entryTarget : BitVec 64) :
    HookFsTraced IsFsC (blackBoxGhostHookK keep P_real P_sub entryTarget) :=
  linkedCallHook_fsT keep P_real P_sub entryTarget (blackBoxSpecK keep masterBlackBoxSpec) blackBoxHook

theorem f3EmptyBlackBoxGhostHook_fsT (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) :
    HookFsTraced IsFsC (f3EmptyBlackBoxGhostHook keep P_sub entryTarget) :=
  f3LinkedCallHook_fsT keep emptyStdProg P_sub entryTarget (fun _ _ => masterBlackBoxSpec) blackBoxHook

theorem f3EmptyBlackBoxGhostHookK_fsT (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) :
    HookFsTraced IsFsC (f3EmptyBlackBoxGhostHookK keep P_sub entryTarget) :=
  f3LinkedCallHook_fsT keep emptyStdProg P_sub entryTarget (fun _ _ => blackBoxSpecK keep masterBlackBoxSpec) blackBoxHook

theorem blackBoxGhostHook_preserves_execFrozen (keep : BitVec 64 → Bool) (P_real P_sub : Program)
    (entryTarget : BitVec 64) {s0 : State} (hfr : ExecFrozen s0.mem) :
    ExecFrozen (blackBoxGhostHook keep P_real P_sub entryTarget s0).mem := by
  classical
  unfold blackBoxGhostHook linkedCallHook; split
  · split
    · rename_i _ hReal; exact (Classical.choose_spec hReal.2.2.2).2.2.2.2
    · rw [keepFsTrace_blackBoxHook_eq]; exact blackBoxHook_preserves_execFrozen hfr
  · exact hfr

theorem blackBoxGhostHookK_preserves_execFrozen (keep : BitVec 64 → Bool) (P_real P_sub : Program)
    (entryTarget : BitVec 64) {s0 : State} (hfr : ExecFrozen s0.mem) :
    ExecFrozen (blackBoxGhostHookK keep P_real P_sub entryTarget s0).mem := by
  classical
  unfold blackBoxGhostHookK linkedCallHook; split
  · split
    · rename_i _ hReal; exact (Classical.choose_spec hReal.2.2.2).2.2.2.2
    · rw [keepFsTrace_blackBoxHook_eq]; exact blackBoxHook_preserves_execFrozen hfr
  · exact hfr

theorem f3EmptyBlackBoxGhostHook_preserves_execFrozen (keep : BitVec 64 → Bool) (P_sub : Program)
    (entryTarget : BitVec 64) {s0 : State} (hfr : ExecFrozen s0.mem) :
    ExecFrozen (f3EmptyBlackBoxGhostHook keep P_sub entryTarget s0).mem := by
  rw [f3EmptyBlackBoxGhostHook_eq]; exact blackBoxGhostHook_preserves_execFrozen keep emptyStdProg P_sub entryTarget hfr

theorem f3EmptyBlackBoxGhostHookK_preserves_execFrozen (keep : BitVec 64 → Bool) (P_sub : Program)
    (entryTarget : BitVec 64) {s0 : State} (hfr : ExecFrozen s0.mem) :
    ExecFrozen (f3EmptyBlackBoxGhostHookK keep P_sub entryTarget s0).mem := by
  rw [f3EmptyBlackBoxGhostHookK_eq]; exact blackBoxGhostHookK_preserves_execFrozen keep emptyStdProg P_sub entryTarget hfr

theorem blackBoxGhostHookK_keepLr_false_of_noException {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64} {u : State}
    (hnoex : ∀ msg, (blackBoxGhostHookK keep P_real P_sub entryTarget u).status ≠ .Exception msg) :
    keep (u.readReg64 .lr) = false := by
  rcases linkedCallHook_activeRealPre_of_noException hnoex with ⟨_, _, v, R, hpre⟩
  dsimp only [blackBoxSpecK, memsetSpecK] at hpre; rw [sepConj_assoc, satisfies_pure_sepConj] at hpre; exact hpre.1

theorem f3EmptyBlackBoxGhostHookK_keepLr_false_of_noException {keep : BitVec 64 → Bool} {P_sub : Program}
    {entryTarget : BitVec 64} {u : State}
    (hnoex : ∀ msg, (f3EmptyBlackBoxGhostHookK keep P_sub entryTarget u).status ≠ .Exception msg) :
    keep (u.readReg64 .lr) = false := by
  rw [f3EmptyBlackBoxGhostHookK_eq] at hnoex; exact blackBoxGhostHookK_keepLr_false_of_noException hnoex

theorem blackBoxGhostHook_of_keepLr_true {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64} {s0 : State} (hActPre : ActiveRealPre masterBlackBoxSpec s0)
    (hlr_in : keep (s0.readReg64 .lr) = true) :
    blackBoxGhostHook keep P_real P_sub entryTarget s0 = blackBoxHook s0 := by
  classical
  have hnReal : ¬ ActiveRealRun keep P_real P_sub entryTarget s0 := fun hR => by
    have hf := hR.2.1; rw [hlr_in] at hf; exact Bool.noConfusion hf
  unfold blackBoxGhostHook linkedCallHook; simp only [hActPre, hnReal, ↓reduceDIte]
  exact keepFsTrace_blackBoxHook_eq s0

theorem blackBoxGhostHookK_of_keepLr_true {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64} {s0 : State} (hlr_in : keep (s0.readReg64 .lr) = true) :
    blackBoxGhostHookK keep P_real P_sub entryTarget s0 =
      { s0 with status := .Exception "ghost-hook precondition violated" } := by
  classical
  have hnAct : ¬ ActiveRealPre (blackBoxSpecK keep masterBlackBoxSpec) s0 := by
    rintro ⟨_, _, v, R, hpre⟩; dsimp only [blackBoxSpecK, memsetSpecK] at hpre
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    have hf := hpre.1; rw [hlr_in] at hf; exact Bool.noConfusion hf
  unfold blackBoxGhostHookK linkedCallHook; simp only [hnAct, ↓reduceDIte]

theorem f3EmptyBlackBoxGhostHook_of_keepLr_true {keep : BitVec 64 → Bool} {P_sub : Program}
    {entryTarget : BitVec 64} {s0 : State} (hActPre : ActiveRealPre masterBlackBoxSpec s0)
    (hlr_in : keep (s0.readReg64 .lr) = true) :
    f3EmptyBlackBoxGhostHook keep P_sub entryTarget s0 = blackBoxHook s0 := by
  rw [f3EmptyBlackBoxGhostHook_eq]; exact blackBoxGhostHook_of_keepLr_true hActPre hlr_in

theorem f3EmptyBlackBoxGhostHookK_of_keepLr_true {keep : BitVec 64 → Bool} {P_sub : Program}
    {entryTarget : BitVec 64} {s0 : State} (hlr_in : keep (s0.readReg64 .lr) = true) :
    f3EmptyBlackBoxGhostHookK keep P_sub entryTarget s0 =
      { s0 with status := .Exception "ghost-hook precondition violated" } := by
  rw [f3EmptyBlackBoxGhostHookK_eq]; exact blackBoxGhostHookK_of_keepLr_true hlr_in

-- 3.2 Generic `hsub_proc` master `HookOk` & pointwise `VmPreserved` / `OomPoolPreserved` / `trace`:

section ProcessPointwiseSuite

variable {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
  (hsvc_real : P_real.svc = Syscall.standard) (hsvc_sub : P_sub.svc = Syscall.standard)
  (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none) (hsub_no : ∀ pc, P_sub.externAt? pc = none)
  (hsub_proc : subroutine_ok P_sub entryTarget processBlackBoxSpec)
include hsvc_real hsvc_sub hreal_no hsub_no hsub_proc

theorem blackBoxGhostHook_master_ok_of_process :
    HookOk (blackBoxGhostHook keep P_real P_sub entryTarget) masterBlackBoxSpec :=
  linkedCallHook_ok hsvc_real hsvc_sub hreal_no hsub_no
    (subroutine_ok_masterBlackBox_of_process hsub_proc)
    (specStripSInvariant_masterBlackBox keep) specPreservesFsTrace_masterBlackBox
    masterBlackBox_pre_setPC masterBlackBox_outcome_setPC keepFsTrace_blackBoxHook_master_ok

theorem blackBoxGhostHookK_masterK_ok_of_process :
    HookOk (blackBoxGhostHookK keep P_real P_sub entryTarget) (blackBoxSpecK keep masterBlackBoxSpec) :=
  linkedCallHook_ok hsvc_real hsvc_sub hreal_no hsub_no
    (subroutine_ok_masterBlackBoxK_of_process keep hsub_proc)
    (specStripSInvariant_masterBlackBoxK keep) (specPreservesFsTrace_masterBlackBoxK keep)
    (masterBlackBoxK_pre_setPC keep) (masterBlackBoxK_outcome_setPC keep)
    (keepFsTrace_blackBoxHook_masterK_ok keep)

theorem blackBoxGhostHook_vmPreserved_of_process (s0 : State) :
    VmPreserved s0 (blackBoxGhostHook keep P_real P_sub entryTarget s0) := by
  classical
  unfold blackBoxGhostHook linkedCallHook; split
  · rename_i hActPre; split
    · rename_i hReal; rcases hActPre with ⟨hrun, hsp, v, R, hpre⟩
      exact vmPreserved_of_processFieldsPreserved
        (activeRealRun_processBlackBox hsvc_real hsvc_sub hreal_no hsub_no hsub_proc hrun hsp hpre hReal)
    · rw [keepFsTrace_blackBoxHook_eq]; exact blackBoxHook_vmPreserved s0
  · exact VmPreserved.refl s0

theorem blackBoxGhostHookK_vmPreserved_of_process (s0 : State) :
    VmPreserved s0 (blackBoxGhostHookK keep P_real P_sub entryTarget s0) := by
  classical
  unfold blackBoxGhostHookK linkedCallHook; split
  · rename_i hActPre; split
    · rename_i hReal; rcases hActPre with ⟨hrun, hsp, v, R, hpre⟩
      dsimp only [blackBoxSpecK, memsetSpecK] at hpre; rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      exact vmPreserved_of_processFieldsPreserved
        (activeRealRun_processBlackBox hsvc_real hsvc_sub hreal_no hsub_no hsub_proc hrun hsp hpre.2 hReal)
    · rw [keepFsTrace_blackBoxHook_eq]; exact blackBoxHook_vmPreserved s0
  · exact VmPreserved.refl s0

theorem blackBoxGhostHook_oomPoolPreserved_of_process (s0 : State) :
    OomPreserved s0 (blackBoxGhostHook keep P_real P_sub entryTarget s0) ∧
      PoolPreserved s0 (blackBoxGhostHook keep P_real P_sub entryTarget s0) := by
  classical
  unfold blackBoxGhostHook linkedCallHook; split
  · rename_i hActPre; split
    · rename_i hReal; rcases hActPre with ⟨hrun, hsp, v, R, hpre⟩
      exact oomPoolPreserved_of_processFieldsPreserved
        (activeRealRun_processBlackBox hsvc_real hsvc_sub hreal_no hsub_no hsub_proc hrun hsp hpre hReal)
    · rw [keepFsTrace_blackBoxHook_eq]; exact blackBoxHook_preserves_oom_pool s0
  · exact ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

theorem blackBoxGhostHookK_oomPoolPreserved_of_process (s0 : State) :
    OomPreserved s0 (blackBoxGhostHookK keep P_real P_sub entryTarget s0) ∧
      PoolPreserved s0 (blackBoxGhostHookK keep P_real P_sub entryTarget s0) := by
  classical
  unfold blackBoxGhostHookK linkedCallHook; split
  · rename_i hActPre; split
    · rename_i hReal; rcases hActPre with ⟨hrun, hsp, v, R, hpre⟩
      dsimp only [blackBoxSpecK, memsetSpecK] at hpre; rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      exact oomPoolPreserved_of_processFieldsPreserved
        (activeRealRun_processBlackBox hsvc_real hsvc_sub hreal_no hsub_no hsub_proc hrun hsp hpre.2 hReal)
    · rw [keepFsTrace_blackBoxHook_eq]; exact blackBoxHook_preserves_oom_pool s0
  · exact ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

theorem blackBoxGhostHook_trace_of_process (s0 : State) :
    (blackBoxGhostHook keep P_real P_sub entryTarget s0).trace = s0.trace := by
  classical
  unfold blackBoxGhostHook linkedCallHook; split
  · rename_i hActPre; split
    · rename_i hReal; rcases hActPre with ⟨hrun, hsp, v, R, hpre⟩
      exact (activeRealRun_processBlackBox hsvc_real hsvc_sub hreal_no hsub_no hsub_proc hrun hsp hpre hReal).2.1
    · rfl
  · rfl

theorem blackBoxGhostHookK_trace_of_process (s0 : State) :
    (blackBoxGhostHookK keep P_real P_sub entryTarget s0).trace = s0.trace := by
  classical
  unfold blackBoxGhostHookK linkedCallHook; split
  · rename_i hActPre; split
    · rename_i hReal; rcases hActPre with ⟨hrun, hsp, v, R, hpre⟩
      dsimp only [blackBoxSpecK, memsetSpecK] at hpre; rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      exact (activeRealRun_processBlackBox hsvc_real hsvc_sub hreal_no hsub_no hsub_proc hrun hsp hpre.2 hReal).2.1
    · rfl
  · rfl

end ProcessPointwiseSuite

section F3EmptyProcessPointwise

variable {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
  (hsvc_sub : P_sub.svc = Syscall.standard) (hsub_no : ∀ pc, P_sub.externAt? pc = none)
  (hsub_proc : subroutine_ok P_sub entryTarget processBlackBoxSpec)
include hsvc_sub hsub_no hsub_proc

theorem f3EmptyBlackBoxGhostHook_master_ok_of_process :
    HookOk (f3EmptyBlackBoxGhostHook keep P_sub entryTarget) masterBlackBoxSpec := by
  rw [f3EmptyBlackBoxGhostHook_eq]
  exact blackBoxGhostHook_master_ok_of_process emptyStdProg_svc hsvc_sub (fun pc _ => emptyStdProg_externAt_none pc) hsub_no hsub_proc

theorem f3EmptyBlackBoxGhostHookK_masterK_ok_of_process :
    HookOk (f3EmptyBlackBoxGhostHookK keep P_sub entryTarget) (blackBoxSpecK keep masterBlackBoxSpec) := by
  rw [f3EmptyBlackBoxGhostHookK_eq]
  exact blackBoxGhostHookK_masterK_ok_of_process emptyStdProg_svc hsvc_sub (fun pc _ => emptyStdProg_externAt_none pc) hsub_no hsub_proc

theorem f3EmptyBlackBoxGhostHook_vmPreserved_of_process (s0 : State) :
    VmPreserved s0 (f3EmptyBlackBoxGhostHook keep P_sub entryTarget s0) := by
  rw [f3EmptyBlackBoxGhostHook_eq]
  exact blackBoxGhostHook_vmPreserved_of_process emptyStdProg_svc hsvc_sub (fun pc _ => emptyStdProg_externAt_none pc) hsub_no hsub_proc s0

theorem f3EmptyBlackBoxGhostHookK_vmPreserved_of_process (s0 : State) :
    VmPreserved s0 (f3EmptyBlackBoxGhostHookK keep P_sub entryTarget s0) := by
  rw [f3EmptyBlackBoxGhostHookK_eq]
  exact blackBoxGhostHookK_vmPreserved_of_process emptyStdProg_svc hsvc_sub (fun pc _ => emptyStdProg_externAt_none pc) hsub_no hsub_proc s0

theorem f3EmptyBlackBoxGhostHook_oomPoolPreserved_of_process (s0 : State) :
    OomPreserved s0 (f3EmptyBlackBoxGhostHook keep P_sub entryTarget s0) ∧
      PoolPreserved s0 (f3EmptyBlackBoxGhostHook keep P_sub entryTarget s0) := by
  rw [f3EmptyBlackBoxGhostHook_eq]
  exact blackBoxGhostHook_oomPoolPreserved_of_process emptyStdProg_svc hsvc_sub (fun pc _ => emptyStdProg_externAt_none pc) hsub_no hsub_proc s0

theorem f3EmptyBlackBoxGhostHookK_oomPoolPreserved_of_process (s0 : State) :
    OomPreserved s0 (f3EmptyBlackBoxGhostHookK keep P_sub entryTarget s0) ∧
      PoolPreserved s0 (f3EmptyBlackBoxGhostHookK keep P_sub entryTarget s0) := by
  rw [f3EmptyBlackBoxGhostHookK_eq]
  exact blackBoxGhostHookK_oomPoolPreserved_of_process emptyStdProg_svc hsvc_sub (fun pc _ => emptyStdProg_externAt_none pc) hsub_no hsub_proc s0

theorem f3EmptyBlackBoxGhostHook_trace_of_process (s0 : State) :
    (f3EmptyBlackBoxGhostHook keep P_sub entryTarget s0).trace = s0.trace := by
  rw [f3EmptyBlackBoxGhostHook_eq]
  exact blackBoxGhostHook_trace_of_process emptyStdProg_svc hsvc_sub (fun pc _ => emptyStdProg_externAt_none pc) hsub_no hsub_proc s0

theorem f3EmptyBlackBoxGhostHookK_trace_of_process (s0 : State) :
    (f3EmptyBlackBoxGhostHookK keep P_sub entryTarget s0).trace = s0.trace := by
  rw [f3EmptyBlackBoxGhostHookK_eq]
  exact blackBoxGhostHookK_trace_of_process emptyStdProg_svc hsvc_sub (fun pc _ => emptyStdProg_externAt_none pc) hsub_no hsub_proc s0

end F3EmptyProcessPointwise

section BlackBoxHasWords

variable {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
  (hsvc_real : P_real.svc = Syscall.standard) (hsvc_sub : P_sub.svc = Syscall.standard)
  (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none) (hsub_no : ∀ pc, P_sub.externAt? pc = none)
  (hwords : P_sub.hasWords entryTarget blackBoxU8Words)
include hsvc_real hsvc_sub hreal_no hsub_no hwords

theorem blackBoxGhostHook_master_ok : HookOk (blackBoxGhostHook keep P_real P_sub entryTarget) masterBlackBoxSpec :=
  blackBoxGhostHook_master_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no (subroutine_ok_processBlackBox_of_hasWords hsub_no hwords)

theorem blackBoxGhostHookK_masterK_ok : HookOk (blackBoxGhostHookK keep P_real P_sub entryTarget) (blackBoxSpecK keep masterBlackBoxSpec) :=
  blackBoxGhostHookK_masterK_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no (subroutine_ok_processBlackBox_of_hasWords hsub_no hwords)

theorem blackBoxGhostHook_vmPreserved (s0 : State) : VmPreserved s0 (blackBoxGhostHook keep P_real P_sub entryTarget s0) :=
  blackBoxGhostHook_vmPreserved_of_process hsvc_real hsvc_sub hreal_no hsub_no (subroutine_ok_processBlackBox_of_hasWords hsub_no hwords) s0

theorem blackBoxGhostHookK_vmPreserved (s0 : State) : VmPreserved s0 (blackBoxGhostHookK keep P_real P_sub entryTarget s0) :=
  blackBoxGhostHookK_vmPreserved_of_process hsvc_real hsvc_sub hreal_no hsub_no (subroutine_ok_processBlackBox_of_hasWords hsub_no hwords) s0

theorem blackBoxGhostHook_oomPoolPreserved (s0 : State) :
    OomPreserved s0 (blackBoxGhostHook keep P_real P_sub entryTarget s0) ∧ PoolPreserved s0 (blackBoxGhostHook keep P_real P_sub entryTarget s0) :=
  blackBoxGhostHook_oomPoolPreserved_of_process hsvc_real hsvc_sub hreal_no hsub_no (subroutine_ok_processBlackBox_of_hasWords hsub_no hwords) s0

theorem blackBoxGhostHookK_oomPoolPreserved (s0 : State) :
    OomPreserved s0 (blackBoxGhostHookK keep P_real P_sub entryTarget s0) ∧ PoolPreserved s0 (blackBoxGhostHookK keep P_real P_sub entryTarget s0) :=
  blackBoxGhostHookK_oomPoolPreserved_of_process hsvc_real hsvc_sub hreal_no hsub_no (subroutine_ok_processBlackBox_of_hasWords hsub_no hwords) s0

theorem blackBoxGhostHook_trace (s0 : State) : (blackBoxGhostHook keep P_real P_sub entryTarget s0).trace = s0.trace :=
  blackBoxGhostHook_trace_of_process hsvc_real hsvc_sub hreal_no hsub_no (subroutine_ok_processBlackBox_of_hasWords hsub_no hwords) s0

theorem blackBoxGhostHookK_trace (s0 : State) : (blackBoxGhostHookK keep P_real P_sub entryTarget s0).trace = s0.trace :=
  blackBoxGhostHookK_trace_of_process hsvc_real hsvc_sub hreal_no hsub_no (subroutine_ok_processBlackBox_of_hasWords hsub_no hwords) s0

end BlackBoxHasWords

/-! ## 4. Complete Consumer `HookOk` Suite -/

section GenericHookOkSuite

variable {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
  (hsvc_real : P_real.svc = Syscall.standard) (hsvc_sub : P_sub.svc = Syscall.standard)
  (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none) (hsub_no : ∀ pc, P_sub.externAt? pc = none)
  (hsub_proc : subroutine_ok P_sub entryTarget processBlackBoxSpec)
include hsvc_real hsvc_sub hreal_no hsub_no hsub_proc

-- 4.1 Plain contracts on `blackBoxGhostHook`:

theorem blackBoxGhostHook_sessionBlackBox16_ok_of_process :
    HookOk (blackBoxGhostHook keep P_real P_sub entryTarget)
      (withStack CryptoVerification.LibsignalTripleRatchet.blackBoxSpec 16) :=
  hookOk_sessionBlackBox16_of_master (blackBoxGhostHook_master_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)

theorem blackBoxGhostHook_sessionBlackBox_ok_of_process {hookStack : Nat}
    (hstk : 16 ≤ hookStack ∧ hookStack ≤ 2 ^ 64) :
    HookOk (blackBoxGhostHook keep P_real P_sub entryTarget)
      (withStack CryptoVerification.LibsignalTripleRatchet.blackBoxSpec hookStack) :=
  hookOk_sessionBlackBox_of_master hstk (blackBoxGhostHook_master_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)

theorem blackBoxGhostHook_sessionBlackBox_keepsFs_ok_of_process {hookStack : Nat}
    (hstk : 16 ≤ hookStack ∧ hookStack ≤ 2 ^ 64) :
    HookOk (blackBoxGhostHook keep P_real P_sub entryTarget)
      (withStack CryptoVerification.LibsignalTripleRatchet.blackBoxSpec hookStack).keepsFs :=
  hookOk_sessionBlackBox_keepsFs_of_master hstk
    (blackBoxGhostHook_master_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)

theorem blackBoxGhostHook_blackBoxU8_ok_of_process {hookStack : Nat}
    (hstk : 16 ≤ hookStack ∧ hookStack ≤ 2 ^ 64) :
    HookOk (blackBoxGhostHook keep P_real P_sub entryTarget) (withStack blackBoxU8Spec hookStack) :=
  hookOk_blackBoxU8_of_master hstk (blackBoxGhostHook_master_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)

theorem blackBoxGhostHook_cliBlackBox_ok_of_process {hookStack : Nat}
    (hstk : 16 ≤ hookStack ∧ hookStack ≤ 2 ^ 64) :
    HookOk (blackBoxGhostHook keep P_real P_sub entryTarget) (cliBlackBoxSpec hookStack) :=
  hookOk_cliBlackBox_of_master hstk (blackBoxGhostHook_master_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)

theorem blackBoxGhostHook_extBlackBox_ok_of_process :
    HookOk (blackBoxGhostHook keep P_real P_sub entryTarget)
      CryptoVerification.SignalSession.CliExt.blackBoxSpec :=
  hookOk_extBlackBox_of_master (blackBoxGhostHook_master_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)

theorem blackBoxGhostHook_extBlackBox_keepsFs_ok_of_process :
    HookOk (blackBoxGhostHook keep P_real P_sub entryTarget)
      CryptoVerification.SignalSession.CliExt.blackBoxSpec.keepsFs :=
  hookOk_extBlackBox_keepsFs_of_master (blackBoxGhostHook_master_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)

theorem blackBoxGhostHook_extBlackBox_withFsPred_ok_of_process (Pfs : FsState → Prop) :
    HookOk (blackBoxGhostHook keep P_real P_sub entryTarget)
      (withFsPred Pfs CryptoVerification.SignalSession.CliExt.blackBoxSpec) :=
  hookOk_extBlackBox_withFsPred_of_master Pfs
    (blackBoxGhostHook_master_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)

theorem blackBoxGhostHook_extBlackBox_execFrozen_ok_of_process :
    HookOk (blackBoxGhostHook keep P_real P_sub entryTarget)
      (withExecFrozen CryptoVerification.SignalSession.CliExt.blackBoxSpec) :=
  hookOk_withExecFrozen_of_plain
    (blackBoxGhostHook_extBlackBox_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)

-- 4.2 Budget / `withVmPreserved` variants on `blackBoxGhostHook`:

theorem blackBoxGhostHook_masterBudget_ok_of_process :
    HookOk (blackBoxGhostHook keep P_real P_sub entryTarget) masterBlackBoxBudgetSpec :=
  hookOk_withVmPreserved
    (blackBoxGhostHook_master_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)
    (blackBoxGhostHook_vmPreserved_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)

theorem blackBoxGhostHook_sessionBlackBox16Budget_ok_of_process :
    HookOk (blackBoxGhostHook keep P_real P_sub entryTarget)
      (withVmPreserved (withStack CryptoVerification.LibsignalTripleRatchet.blackBoxSpec 16)) :=
  hookOk_sessionBlackBox16Budget_of_master
    (blackBoxGhostHook_master_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)
    (blackBoxGhostHook_vmPreserved_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)

theorem blackBoxGhostHook_sessionBlackBoxBudget_ok_of_process {hookStack : Nat}
    (hstk : 16 ≤ hookStack ∧ hookStack ≤ 2 ^ 64) :
    HookOk (blackBoxGhostHook keep P_real P_sub entryTarget)
      (withStack (withVmPreserved CryptoVerification.LibsignalTripleRatchet.blackBoxSpec) hookStack) :=
  hookOk_sessionBlackBoxBudget_of_master hstk
    (blackBoxGhostHook_master_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)
    (blackBoxGhostHook_vmPreserved_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)

theorem blackBoxGhostHook_vmSessionBlackBox_ok_of_process {hookStack : Nat}
    (hstk : 16 ≤ hookStack ∧ hookStack ≤ 2 ^ 64) :
    HookOk (blackBoxGhostHook keep P_real P_sub entryTarget)
      (withVmPreserved (withStack CryptoVerification.LibsignalTripleRatchet.blackBoxSpec hookStack)) :=
  hookOk_vmSessionBlackBox_of_master hstk
    (blackBoxGhostHook_master_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)
    (blackBoxGhostHook_vmPreserved_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)

theorem blackBoxGhostHook_blackBoxU8Budget_ok_of_process {hookStack : Nat}
    (hstk : 16 ≤ hookStack ∧ hookStack ≤ 2 ^ 64) :
    HookOk (blackBoxGhostHook keep P_real P_sub entryTarget)
      (withStack (withVmPreserved blackBoxU8Spec) hookStack) :=
  hookOk_blackBoxU8Budget_of_master hstk
    (blackBoxGhostHook_master_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)
    (blackBoxGhostHook_vmPreserved_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)

theorem blackBoxGhostHook_vmBlackBoxU8_ok_of_process {hookStack : Nat}
    (hstk : 16 ≤ hookStack ∧ hookStack ≤ 2 ^ 64) :
    HookOk (blackBoxGhostHook keep P_real P_sub entryTarget)
      (withVmPreserved (withStack blackBoxU8Spec hookStack)) :=
  hookOk_withVmPreserved
    (blackBoxGhostHook_blackBoxU8_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc hstk)
    (blackBoxGhostHook_vmPreserved_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)

theorem blackBoxGhostHook_extBlackBoxBudget_ok_of_process :
    HookOk (blackBoxGhostHook keep P_real P_sub entryTarget)
      (withVmPreserved CryptoVerification.SignalSession.CliExt.blackBoxSpec) :=
  hookOk_extBlackBoxBudget_of_master
    (blackBoxGhostHook_master_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)
    (blackBoxGhostHook_vmPreserved_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)

theorem blackBoxGhostHook_extBlackBoxBudget_keepsFs_ok_of_process :
    HookOk (blackBoxGhostHook keep P_real P_sub entryTarget)
      (withVmPreserved CryptoVerification.SignalSession.CliExt.blackBoxSpec).keepsFs :=
  hookOk_extBlackBoxBudget_keepsFs_of_master
    (blackBoxGhostHook_master_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)
    (blackBoxGhostHook_vmPreserved_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)

theorem blackBoxGhostHook_extBlackBoxBudget_withFsPred_ok_of_process (Pfs : FsState → Prop) :
    HookOk (blackBoxGhostHook keep P_real P_sub entryTarget)
      (withFsPred Pfs (withVmPreserved CryptoVerification.SignalSession.CliExt.blackBoxSpec)) :=
  hookOk_extBlackBoxBudget_withFsPred_of_master Pfs
    (blackBoxGhostHook_master_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)
    (blackBoxGhostHook_vmPreserved_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)

-- 4.2b C11 `withAlloc` pool-framed contracts on `blackBoxGhostHook`:

theorem blackBoxGhostHook_sessionBlackBox16_withAlloc_ok_of_process {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk (blackBoxGhostHook keep P_real P_sub entryTarget)
      (withAlloc (M := M) A lim (withStack CryptoVerification.LibsignalTripleRatchet.blackBoxSpec 16)) :=
  hookOk_withAlloc_of_withVmPreserved A lim
    (blackBoxGhostHook_sessionBlackBox16Budget_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)

theorem blackBoxGhostHook_sessionBlackBox16Budget_withAlloc_ok_of_process {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk (blackBoxGhostHook keep P_real P_sub entryTarget)
      (withAlloc (M := M) A lim (withVmPreserved (withStack CryptoVerification.LibsignalTripleRatchet.blackBoxSpec 16))) :=
  hookOk_withAlloc_withVmPreserved A lim
    (blackBoxGhostHook_sessionBlackBox16Budget_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)

theorem blackBoxGhostHook_sessionBlackBox_withAlloc_ok_of_process {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {hookStack : Nat}
    (hstk : 16 ≤ hookStack ∧ hookStack ≤ 2 ^ 64) :
    HookOk (blackBoxGhostHook keep P_real P_sub entryTarget)
      (withAlloc (M := M) A lim (withStack CryptoVerification.LibsignalTripleRatchet.blackBoxSpec hookStack)) :=
  hookOk_withAlloc_of_withVmPreserved A lim
    (blackBoxGhostHook_vmSessionBlackBox_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc hstk)

theorem blackBoxGhostHook_vmSessionBlackBox_withAlloc_ok_of_process {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {hookStack : Nat}
    (hstk : 16 ≤ hookStack ∧ hookStack ≤ 2 ^ 64) :
    HookOk (blackBoxGhostHook keep P_real P_sub entryTarget)
      (withAlloc (M := M) A lim (withVmPreserved (withStack CryptoVerification.LibsignalTripleRatchet.blackBoxSpec hookStack))) :=
  hookOk_withAlloc_withVmPreserved A lim
    (blackBoxGhostHook_vmSessionBlackBox_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc hstk)

theorem blackBoxGhostHook_vmBlackBoxU8_withAlloc_ok_of_process {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {hookStack : Nat}
    (hstk : 16 ≤ hookStack ∧ hookStack ≤ 2 ^ 64) :
    HookOk (blackBoxGhostHook keep P_real P_sub entryTarget)
      (withAlloc (M := M) A lim (withVmPreserved (withStack blackBoxU8Spec hookStack))) :=
  hookOk_withAlloc_withVmPreserved A lim
    (blackBoxGhostHook_vmBlackBoxU8_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc hstk)

theorem blackBoxGhostHook_extBlackBox_withAlloc_ok_of_process {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk (blackBoxGhostHook keep P_real P_sub entryTarget)
      (withAlloc (M := M) A lim CryptoVerification.SignalSession.CliExt.blackBoxSpec) :=
  hookOk_withAlloc_of_withVmPreserved A lim
    (blackBoxGhostHook_extBlackBoxBudget_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)

theorem blackBoxGhostHook_extBlackBoxBudget_withAlloc_ok_of_process {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk (blackBoxGhostHook keep P_real P_sub entryTarget)
      (withAlloc (M := M) A lim (withVmPreserved CryptoVerification.SignalSession.CliExt.blackBoxSpec)) :=
  hookOk_withAlloc_withVmPreserved A lim
    (blackBoxGhostHook_extBlackBoxBudget_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)

-- 4.3 `blackBoxSpecK`-narrowed contracts on `blackBoxGhostHook` and `blackBoxGhostHookK`:

omit hsvc_real hsvc_sub hreal_no hsub_no hsub_proc in
theorem blackBoxGhostHook_any_blackBoxSpecK_ok {α : Type} {spec : Spec α} (keep' : BitVec 64 → Bool)
    (hh : HookOk (blackBoxGhostHook keep P_real P_sub entryTarget) spec) :
    HookOk (blackBoxGhostHook keep P_real P_sub entryTarget) (blackBoxSpecK keep' spec) :=
  hookOk_memsetSpecK_of_plain keep' hh

theorem blackBoxGhostHookK_sessionBlackBox16K_ok_of_process :
    HookOk (blackBoxGhostHookK keep P_real P_sub entryTarget)
      (blackBoxSpecK keep (withStack CryptoVerification.LibsignalTripleRatchet.blackBoxSpec 16)) :=
  hookOk_sessionBlackBox16K_of_master keep
    (blackBoxGhostHookK_masterK_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)

theorem blackBoxGhostHookK_sessionBlackBoxK_ok_of_process {hookStack : Nat}
    (hstk : 16 ≤ hookStack ∧ hookStack ≤ 2 ^ 64) :
    HookOk (blackBoxGhostHookK keep P_real P_sub entryTarget)
      (blackBoxSpecK keep (withStack CryptoVerification.LibsignalTripleRatchet.blackBoxSpec hookStack)) :=
  hookOk_sessionBlackBoxK_of_master keep hstk
    (blackBoxGhostHookK_masterK_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)

theorem blackBoxGhostHookK_sessionBlackBoxK_keepsFs_ok_of_process {hookStack : Nat}
    (hstk : 16 ≤ hookStack ∧ hookStack ≤ 2 ^ 64) :
    HookOk (blackBoxGhostHookK keep P_real P_sub entryTarget)
      (blackBoxSpecK keep (withStack CryptoVerification.LibsignalTripleRatchet.blackBoxSpec hookStack)).keepsFs :=
  (blackBoxGhostHookK_sessionBlackBoxK_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc hstk).keepsFs
    (blackBoxGhostHookK_fs keep P_real P_sub entryTarget)

theorem blackBoxGhostHookK_blackBoxU8K_ok_of_process {hookStack : Nat}
    (hstk : 16 ≤ hookStack ∧ hookStack ≤ 2 ^ 64) :
    HookOk (blackBoxGhostHookK keep P_real P_sub entryTarget)
      (blackBoxSpecK keep (withStack blackBoxU8Spec hookStack)) :=
  hookOk_blackBoxU8K_of_master keep hstk
    (blackBoxGhostHookK_masterK_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)

theorem blackBoxGhostHookK_cliBlackBoxK_ok_of_process {hookStack : Nat}
    (hstk : 16 ≤ hookStack ∧ hookStack ≤ 2 ^ 64) :
    HookOk (blackBoxGhostHookK keep P_real P_sub entryTarget)
      (blackBoxSpecK keep (cliBlackBoxSpec hookStack)) :=
  hookOk_cliBlackBoxK_of_master keep hstk
    (blackBoxGhostHookK_masterK_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)

theorem blackBoxGhostHookK_extBlackBoxK_ok_of_process :
    HookOk (blackBoxGhostHookK keep P_real P_sub entryTarget)
      (blackBoxSpecK keep CryptoVerification.SignalSession.CliExt.blackBoxSpec) :=
  hookOk_extBlackBoxK_of_master keep
    (blackBoxGhostHookK_masterK_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)

theorem blackBoxGhostHookK_extBlackBoxK_keepsFs_ok_of_process :
    HookOk (blackBoxGhostHookK keep P_real P_sub entryTarget)
      (blackBoxSpecK keep CryptoVerification.SignalSession.CliExt.blackBoxSpec).keepsFs :=
  (blackBoxGhostHookK_extBlackBoxK_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc).keepsFs
    (blackBoxGhostHookK_fs keep P_real P_sub entryTarget)

theorem blackBoxGhostHookK_extBlackBoxK_withFsPred_ok_of_process (Pfs : FsState → Prop) :
    HookOk (blackBoxGhostHookK keep P_real P_sub entryTarget)
      (blackBoxSpecK keep (withFsPred Pfs CryptoVerification.SignalSession.CliExt.blackBoxSpec)) :=
  hookOk_zeroizeSpecK_withFsPred_of_keepsFs keep Pfs
    (blackBoxGhostHookK_extBlackBoxK_keepsFs_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)

theorem blackBoxGhostHookK_sessionBlackBox16BudgetK_ok_of_process :
    HookOk (blackBoxGhostHookK keep P_real P_sub entryTarget)
      (blackBoxSpecK keep (withVmPreserved (withStack CryptoVerification.LibsignalTripleRatchet.blackBoxSpec 16))) := by
  rw [← blackBoxSpecK_withVmPreserved]
  exact hookOk_withVmPreserved
    (blackBoxGhostHookK_sessionBlackBox16K_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)
    (blackBoxGhostHookK_vmPreserved_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)

theorem blackBoxGhostHookK_vmSessionBlackBoxK_ok_of_process {hookStack : Nat}
    (hstk : 16 ≤ hookStack ∧ hookStack ≤ 2 ^ 64) :
    HookOk (blackBoxGhostHookK keep P_real P_sub entryTarget)
      (blackBoxSpecK keep (withVmPreserved (withStack CryptoVerification.LibsignalTripleRatchet.blackBoxSpec hookStack))) := by
  rw [← blackBoxSpecK_withVmPreserved]
  exact hookOk_withVmPreserved
    (blackBoxGhostHookK_sessionBlackBoxK_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc hstk)
    (blackBoxGhostHookK_vmPreserved_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)

theorem blackBoxGhostHookK_extBlackBoxBudgetK_ok_of_process :
    HookOk (blackBoxGhostHookK keep P_real P_sub entryTarget)
      (blackBoxSpecK keep (withVmPreserved CryptoVerification.SignalSession.CliExt.blackBoxSpec)) :=
  hookOk_extBlackBoxBudgetK_of_master keep
    (blackBoxGhostHookK_masterK_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)
    (blackBoxGhostHookK_vmPreserved_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)

theorem blackBoxGhostHookK_extBlackBoxBudgetK_keepsFs_ok_of_process :
    HookOk (blackBoxGhostHookK keep P_real P_sub entryTarget)
      (blackBoxSpecK keep (withVmPreserved CryptoVerification.SignalSession.CliExt.blackBoxSpec)).keepsFs :=
  (blackBoxGhostHookK_extBlackBoxBudgetK_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc).keepsFs
    (blackBoxGhostHookK_fs keep P_real P_sub entryTarget)

theorem blackBoxGhostHookK_extBlackBoxBudgetK_withFsPred_ok_of_process (Pfs : FsState → Prop) :
    HookOk (blackBoxGhostHookK keep P_real P_sub entryTarget)
      (blackBoxSpecK keep (withFsPred Pfs (withVmPreserved CryptoVerification.SignalSession.CliExt.blackBoxSpec))) :=
  hookOk_zeroizeSpecK_withFsPred_of_keepsFs keep Pfs
    (blackBoxGhostHookK_extBlackBoxBudgetK_keepsFs_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)
    (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)

end GenericHookOkSuite

-- 4.4 `hasWords`, `withAlloc`, & `f3Empty*` consumer `HookOk` specializations:

section HasWordsRealConsumerHookOk

variable {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
  (hsvc_real : P_real.svc = Syscall.standard) (hsvc_sub : P_sub.svc = Syscall.standard)
  (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none) (hsub_no : ∀ pc, P_sub.externAt? pc = none)
include hsvc_real hsvc_sub hreal_no hsub_no

theorem blackBoxGhostHook_vmSessionBlackBox_ok {hookStack : Nat}
    (hstk : 16 ≤ hookStack ∧ hookStack ≤ 2 ^ 64) (hwords : P_sub.hasWords entryTarget blackBoxU8Words) :
    HookOk (blackBoxGhostHook keep P_real P_sub entryTarget)
      (withVmPreserved (withStack CryptoVerification.LibsignalTripleRatchet.blackBoxSpec hookStack)) :=
  blackBoxGhostHook_vmSessionBlackBox_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no
    (subroutine_ok_processBlackBox_of_hasWords hsub_no hwords) hstk

theorem blackBoxGhostHook_vmSessionBlackBox_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {hookStack : Nat}
    (hstk : 16 ≤ hookStack ∧ hookStack ≤ 2 ^ 64) (hwords : P_sub.hasWords entryTarget blackBoxU8Words) :
    HookOk (blackBoxGhostHook keep P_real P_sub entryTarget)
      (withAlloc (M := M) A lim (withVmPreserved (withStack CryptoVerification.LibsignalTripleRatchet.blackBoxSpec hookStack))) :=
  blackBoxGhostHook_vmSessionBlackBox_withAlloc_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no
    (subroutine_ok_processBlackBox_of_hasWords hsub_no hwords) A lim hstk

theorem blackBoxGhostHook_extBlackBoxBudget_ok (hwords : P_sub.hasWords entryTarget blackBoxU8Words) :
    HookOk (blackBoxGhostHook keep P_real P_sub entryTarget)
      (withVmPreserved CryptoVerification.SignalSession.CliExt.blackBoxSpec) :=
  blackBoxGhostHook_extBlackBoxBudget_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no
    (subroutine_ok_processBlackBox_of_hasWords hsub_no hwords)

theorem blackBoxGhostHook_extBlackBoxBudget_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (hwords : P_sub.hasWords entryTarget blackBoxU8Words) :
    HookOk (blackBoxGhostHook keep P_real P_sub entryTarget)
      (withAlloc (M := M) A lim (withVmPreserved CryptoVerification.SignalSession.CliExt.blackBoxSpec)) :=
  blackBoxGhostHook_extBlackBoxBudget_withAlloc_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no
    (subroutine_ok_processBlackBox_of_hasWords hsub_no hwords) A lim

end HasWordsRealConsumerHookOk

section F3EmptyConsumerHookOk

variable {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
  (hsvc_sub : P_sub.svc = Syscall.standard) (hsub_no : ∀ pc, P_sub.externAt? pc = none)
include hsvc_sub hsub_no

theorem f3EmptyBlackBoxGhostHook_vmSessionBlackBox_ok_of_process {hookStack : Nat}
    (hstk : 16 ≤ hookStack ∧ hookStack ≤ 2 ^ 64) (hsub_proc : subroutine_ok P_sub entryTarget processBlackBoxSpec) :
    HookOk (f3EmptyBlackBoxGhostHook keep P_sub entryTarget)
      (withVmPreserved (withStack CryptoVerification.LibsignalTripleRatchet.blackBoxSpec hookStack)) := by
  rw [f3EmptyBlackBoxGhostHook_eq]
  exact blackBoxGhostHook_vmSessionBlackBox_ok_of_process emptyStdProg_svc hsvc_sub
    (fun pc _ => emptyStdProg_externAt_none pc) hsub_no hsub_proc hstk

theorem f3EmptyBlackBoxGhostHook_vmSessionBlackBox_withAlloc_ok_of_process {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {hookStack : Nat}
    (hstk : 16 ≤ hookStack ∧ hookStack ≤ 2 ^ 64) (hsub_proc : subroutine_ok P_sub entryTarget processBlackBoxSpec) :
    HookOk (f3EmptyBlackBoxGhostHook keep P_sub entryTarget)
      (withAlloc (M := M) A lim (withVmPreserved (withStack CryptoVerification.LibsignalTripleRatchet.blackBoxSpec hookStack))) :=
  hookOk_withAlloc_withVmPreserved A lim
    (f3EmptyBlackBoxGhostHook_vmSessionBlackBox_ok_of_process hsvc_sub hsub_no hstk hsub_proc)

theorem f3EmptyBlackBoxGhostHook_extBlackBoxBudget_ok_of_process
    (hsub_proc : subroutine_ok P_sub entryTarget processBlackBoxSpec) :
    HookOk (f3EmptyBlackBoxGhostHook keep P_sub entryTarget)
      (withVmPreserved CryptoVerification.SignalSession.CliExt.blackBoxSpec) := by
  rw [f3EmptyBlackBoxGhostHook_eq]
  exact blackBoxGhostHook_extBlackBoxBudget_ok_of_process emptyStdProg_svc hsvc_sub
    (fun pc _ => emptyStdProg_externAt_none pc) hsub_no hsub_proc

theorem f3EmptyBlackBoxGhostHook_extBlackBoxBudget_withAlloc_ok_of_process {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (hsub_proc : subroutine_ok P_sub entryTarget processBlackBoxSpec) :
    HookOk (f3EmptyBlackBoxGhostHook keep P_sub entryTarget)
      (withAlloc (M := M) A lim (withVmPreserved CryptoVerification.SignalSession.CliExt.blackBoxSpec)) :=
  hookOk_withAlloc_withVmPreserved A lim
    (f3EmptyBlackBoxGhostHook_extBlackBoxBudget_ok_of_process hsvc_sub hsub_no hsub_proc)

theorem f3EmptyBlackBoxGhostHook_vmSessionBlackBox_ok {hookStack : Nat}
    (hstk : 16 ≤ hookStack ∧ hookStack ≤ 2 ^ 64) (hwords : P_sub.hasWords entryTarget blackBoxU8Words) :
    HookOk (f3EmptyBlackBoxGhostHook keep P_sub entryTarget)
      (withVmPreserved (withStack CryptoVerification.LibsignalTripleRatchet.blackBoxSpec hookStack)) :=
  f3EmptyBlackBoxGhostHook_vmSessionBlackBox_ok_of_process hsvc_sub hsub_no hstk
    (subroutine_ok_processBlackBox_of_hasWords hsub_no hwords)

theorem f3EmptyBlackBoxGhostHook_vmSessionBlackBox_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {hookStack : Nat}
    (hstk : 16 ≤ hookStack ∧ hookStack ≤ 2 ^ 64) (hwords : P_sub.hasWords entryTarget blackBoxU8Words) :
    HookOk (f3EmptyBlackBoxGhostHook keep P_sub entryTarget)
      (withAlloc (M := M) A lim (withVmPreserved (withStack CryptoVerification.LibsignalTripleRatchet.blackBoxSpec hookStack))) :=
  hookOk_withAlloc_withVmPreserved A lim
    (f3EmptyBlackBoxGhostHook_vmSessionBlackBox_ok hsvc_sub hsub_no hstk hwords)

theorem f3EmptyBlackBoxGhostHook_extBlackBoxBudget_ok (hwords : P_sub.hasWords entryTarget blackBoxU8Words) :
    HookOk (f3EmptyBlackBoxGhostHook keep P_sub entryTarget)
      (withVmPreserved CryptoVerification.SignalSession.CliExt.blackBoxSpec) :=
  f3EmptyBlackBoxGhostHook_extBlackBoxBudget_ok_of_process hsvc_sub hsub_no
    (subroutine_ok_processBlackBox_of_hasWords hsub_no hwords)

theorem f3EmptyBlackBoxGhostHook_extBlackBoxBudget_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (hwords : P_sub.hasWords entryTarget blackBoxU8Words) :
    HookOk (f3EmptyBlackBoxGhostHook keep P_sub entryTarget)
      (withAlloc (M := M) A lim (withVmPreserved CryptoVerification.SignalSession.CliExt.blackBoxSpec)) :=
  hookOk_withAlloc_withVmPreserved A lim
    (f3EmptyBlackBoxGhostHook_extBlackBoxBudget_ok hsvc_sub hsub_no hwords)

end F3EmptyConsumerHookOk

/-! ## 5. Stock-Safe `StepsVisitedIn` Witnesses & `hLiftVis` Guarded Replays -/

/-- Stock-safe `h2fsgen_StepsVisitedIn` execution witness for `blackBoxGhostHook` on `P_run`. -/
theorem blackBoxGhostHook_visitedIn_of_process {keep : BitVec 64 → Bool} {P_run P_sub : Program}
    {entryTarget : BitVec 64} (hsvc_run : P_run.svc = Syscall.standard) (hsvc_sub : P_sub.svc = Syscall.standard)
    (hrun_no : ∀ pc, keep pc = true → P_run.externAt? pc = none) (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hsub_proc : subroutine_ok P_sub entryTarget processBlackBoxSpec) {u : State} (hrun : u.status = .Running)
    (hnoex : ∀ msg, (blackBoxGhostHook keep P_run P_sub entryTarget u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem) (hlr_out : keep (u.readReg64 .lr) = false)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem)) :
    let sf_g := blackBoxGhostHook keep P_run P_sub entryTarget u
    h2fsgen_StepsVisitedIn keep P_run (u.setPC entryTarget) sf_g ∧ ExecFrozen sf_g.mem ∧ sf_g.fs = u.fs := by
  classical
  have hActPre : ActiveRealPre masterBlackBoxSpec u := linkedCallHook_activeRealPre_of_noException hnoex
  have ⟨_, hsp, v, R, hpre⟩ := hActPre
  obtain ⟨sf, huntil, hstop, _, hfs, hfst, hfr_sf, hvis⟩ :=
    h2fsgen_real_subroutine_run_visitedIn_of_stripS hsvc_run hsvc_sub hrun_no hsub_no
      (subroutine_ok_masterBlackBox_of_process hsub_proc)
      (specStripSInvariant_masterBlackBox keep) specPreservesFsTrace_masterBlackBox
      masterBlackBox_pre_setPC masterBlackBox_outcome_setPC hrun hsp hpre hFr hlr_out hCodeSub
  have hReal : ActiveRealRun keep P_run P_sub entryTarget u := ⟨hFr, hlr_out, hCodeSub, sf, huntil, hstop, hfs, hfst, hfr_sf⟩
  have heq : blackBoxGhostHook keep P_run P_sub entryTarget u = sf := by
    unfold blackBoxGhostHook linkedCallHook; simp only [hActPre, hReal, ↓reduceDIte]
    have hchoose := Classical.choose_spec hReal.2.2.2
    exact h2fsgen_stepsUntil_det hchoose.1 hchoose.2.1 huntil hstop
  dsimp only; rw [heq]; exact ⟨hvis, hfr_sf, hfs⟩

/-- Stock-safe `h2fsgen_StepsVisitedIn` execution witness for `blackBoxGhostHookK` on `P_run`. -/
theorem blackBoxGhostHookK_visitedIn_of_process {keep : BitVec 64 → Bool} {P_run P_sub : Program}
    {entryTarget : BitVec 64} (hsvc_run : P_run.svc = Syscall.standard) (hsvc_sub : P_sub.svc = Syscall.standard)
    (hrun_no : ∀ pc, keep pc = true → P_run.externAt? pc = none) (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hsub_proc : subroutine_ok P_sub entryTarget processBlackBoxSpec) {u : State} (hrun : u.status = .Running)
    (hnoex : ∀ msg, (blackBoxGhostHookK keep P_run P_sub entryTarget u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem) (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem)) :
    let sf_g := blackBoxGhostHookK keep P_run P_sub entryTarget u
    h2fsgen_StepsVisitedIn keep P_run (u.setPC entryTarget) sf_g ∧ ExecFrozen sf_g.mem ∧ sf_g.fs = u.fs := by
  classical
  have hlr_out : keep (u.readReg64 .lr) = false := blackBoxGhostHookK_keepLr_false_of_noException hnoex
  have hActPre : ActiveRealPre (blackBoxSpecK keep masterBlackBoxSpec) u := linkedCallHook_activeRealPre_of_noException hnoex
  have ⟨_, hsp, v, R, hpre⟩ := hActPre
  obtain ⟨sf, huntil, hstop, _, hfs, hfst, hfr_sf, hvis⟩ :=
    h2fsgen_real_subroutine_run_visitedIn_of_stripS hsvc_run hsvc_sub hrun_no hsub_no
      (subroutine_ok_masterBlackBoxK_of_process keep hsub_proc)
      (specStripSInvariant_masterBlackBoxK keep) (specPreservesFsTrace_masterBlackBoxK keep)
      (masterBlackBoxK_pre_setPC keep) (masterBlackBoxK_outcome_setPC keep) hrun hsp hpre hFr hlr_out hCodeSub
  have hReal : ActiveRealRun keep P_run P_sub entryTarget u := ⟨hFr, hlr_out, hCodeSub, sf, huntil, hstop, hfs, hfst, hfr_sf⟩
  have heq : blackBoxGhostHookK keep P_run P_sub entryTarget u = sf := by
    unfold blackBoxGhostHookK linkedCallHook; simp only [hActPre, hReal, ↓reduceDIte]
    have hchoose := Classical.choose_spec hReal.2.2.2
    exact h2fsgen_stepsUntil_det hchoose.1 hchoose.2.1 huntil hstop
  dsimp only; rw [heq]; exact ⟨hvis, hfr_sf, hfs⟩

/-- `W`-independent `h2fsgen_StepsVisitedIn keep emptyStdProg` witness for `f3EmptyBlackBoxGhostHook`. -/
theorem f3EmptyBlackBoxGhostHook_visitedIn_of_process {keep : BitVec 64 → Bool} {P_sub : Program}
    {entryTarget : BitVec 64} (hsvc_sub : P_sub.svc = Syscall.standard) (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hsub_proc : subroutine_ok P_sub entryTarget processBlackBoxSpec) {u : State} (hrun : u.status = .Running)
    (hnoex : ∀ msg, (f3EmptyBlackBoxGhostHook keep P_sub entryTarget u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem) (hlr_out : keep (u.readReg64 .lr) = false)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem)) :
    let sf_g := f3EmptyBlackBoxGhostHook keep P_sub entryTarget u
    h2fsgen_StepsVisitedIn keep emptyStdProg (u.setPC entryTarget) sf_g ∧ ExecFrozen sf_g.mem ∧ sf_g.fs = u.fs := by
  dsimp only; rw [f3EmptyBlackBoxGhostHook_eq] at hnoex ⊢
  exact blackBoxGhostHook_visitedIn_of_process emptyStdProg_svc hsvc_sub
    (fun pc _ => emptyStdProg_externAt_none pc) hsub_no hsub_proc hrun hnoex hFr hlr_out hCodeSub

/-- `W`-independent `h2fsgen_StepsVisitedIn keep emptyStdProg` witness for `f3EmptyBlackBoxGhostHookK`. -/
theorem f3EmptyBlackBoxGhostHookK_visitedIn_of_process {keep : BitVec 64 → Bool} {P_sub : Program}
    {entryTarget : BitVec 64} (hsvc_sub : P_sub.svc = Syscall.standard) (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hsub_proc : subroutine_ok P_sub entryTarget processBlackBoxSpec) {u : State} (hrun : u.status = .Running)
    (hnoex : ∀ msg, (f3EmptyBlackBoxGhostHookK keep P_sub entryTarget u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem) (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem)) :
    let sf_g := f3EmptyBlackBoxGhostHookK keep P_sub entryTarget u
    h2fsgen_StepsVisitedIn keep emptyStdProg (u.setPC entryTarget) sf_g ∧ ExecFrozen sf_g.mem ∧ sf_g.fs = u.fs := by
  dsimp only; rw [f3EmptyBlackBoxGhostHookK_eq] at hnoex ⊢
  exact blackBoxGhostHookK_visitedIn_of_process emptyStdProg_svc hsvc_sub
    (fun pc _ => emptyStdProg_externAt_none pc) hsub_no hsub_proc hrun hnoex hFr hCodeSub

/-- `blackBoxU8Words` `StepsVisitedIn` corollary for `f3EmptyBlackBoxGhostHook`. -/
theorem f3EmptyBlackBoxGhostHook_visitedIn {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard) (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget blackBoxU8Words) {u : State} (hrun : u.status = .Running)
    (hnoex : ∀ msg, (f3EmptyBlackBoxGhostHook keep P_sub entryTarget u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem) (hlr_out : keep (u.readReg64 .lr) = false)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem)) :
    let sf_g := f3EmptyBlackBoxGhostHook keep P_sub entryTarget u
    h2fsgen_StepsVisitedIn keep emptyStdProg (u.setPC entryTarget) sf_g ∧ ExecFrozen sf_g.mem ∧ sf_g.fs = u.fs :=
  f3EmptyBlackBoxGhostHook_visitedIn_of_process hsvc_sub hsub_no
    (subroutine_ok_processBlackBox_of_hasWords hsub_no hwords) hrun hnoex hFr hlr_out hCodeSub

/-- `blackBoxU8Words` `StepsVisitedIn` corollary for `f3EmptyBlackBoxGhostHookK`. -/
theorem f3EmptyBlackBoxGhostHookK_visitedIn {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard) (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget blackBoxU8Words) {u : State} (hrun : u.status = .Running)
    (hnoex : ∀ msg, (f3EmptyBlackBoxGhostHookK keep P_sub entryTarget u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem) (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem)) :
    let sf_g := f3EmptyBlackBoxGhostHookK keep P_sub entryTarget u
    h2fsgen_StepsVisitedIn keep emptyStdProg (u.setPC entryTarget) sf_g ∧ ExecFrozen sf_g.mem ∧ sf_g.fs = u.fs :=
  f3EmptyBlackBoxGhostHookK_visitedIn_of_process hsvc_sub hsub_no
    (subroutine_ok_processBlackBox_of_hasWords hsub_no hwords) hrun hnoex hFr hCodeSub

section StockSafeVisitedInReplays

variable {InvMem : Memory → Prop} {keep : BitVec 64 → Bool} {P_real P_sub : Program}
  {stubPc entryTarget : BitVec 64}
  (hsvc_sub : P_sub.svc = Syscall.standard) (hsub_no : ∀ pc, P_sub.externAt? pc = none)
  (hsub_proc : subroutine_ok P_sub entryTarget processBlackBoxSpec)
  (hreal_stub_none : P_real.externAt? stubPc = none)
  (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
  (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m → P_sub.CodeLoaded (stripExecOutside keep m))
  (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
  (hLiftVis : ∀ u sf : State, u.status = .Running → ExecFrozen u.mem → InvMem u.mem →
    h2fsgen_StepsVisitedIn keep emptyStdProg (u.setPC entryTarget) sf → Steps P_real (u.setPC entryTarget) sf)
include hsvc_sub hsub_no hsub_proc hreal_stub_none hStub hInvLoaded hInvKf hLiftVis

/-- Stock-safe `emptyStdProg → P_real` replay for `f3EmptyBlackBoxGhostHook` via `hLiftVis`. -/
theorem f3EmptyBlackBoxGhostHook_replayOn_of_visitedIn_process :
    P_real.externAt? stubPc = none ∧
    ∀ u : State, u.pc = stubPc → u.status = .Running →
      (∀ msg, (f3EmptyBlackBoxGhostHook keep P_sub entryTarget u).status ≠ .Exception msg) →
      ExecFrozen u.mem → keep (u.readReg64 .lr) = false → InvMem u.mem →
      Steps P_real u (f3EmptyBlackBoxGhostHook keep P_sub entryTarget u) ∧
      ExecFrozen (f3EmptyBlackBoxGhostHook keep P_sub entryTarget u).mem ∧
      InvMem (f3EmptyBlackBoxGhostHook keep P_sub entryTarget u).mem ∧
      (f3EmptyBlackBoxGhostHook keep P_sub entryTarget u).fs = u.fs := by
  refine ⟨hreal_stub_none, fun u hpc hrun hnoex hfr hlr hinv => ?_⟩
  obtain ⟨hvis, hfr_sf, hfs_sf⟩ :=
    f3EmptyBlackBoxGhostHook_visitedIn_of_process hsvc_sub hsub_no hsub_proc hrun hnoex hfr hlr
      (hInvLoaded u.mem hfr hinv)
  have hSteps := (hStub u hpc hrun hfr hinv).trans (hLiftVis u _ hrun hfr hinv hvis)
  exact ⟨hSteps, hfr_sf, hInvKf u.mem _ hinv hSteps.keepsFrozen, hfs_sf⟩

/-- Stock-safe `emptyStdProg → P_real` replay for `f3EmptyBlackBoxGhostHookK` via `hLiftVis` (zero `lr` premise). -/
theorem f3EmptyBlackBoxGhostHookK_replayOn_of_visitedIn_process :
    P_real.externAt? stubPc = none ∧
    ∀ u : State, u.pc = stubPc → u.status = .Running →
      (∀ msg, (f3EmptyBlackBoxGhostHookK keep P_sub entryTarget u).status ≠ .Exception msg) →
      ExecFrozen u.mem → InvMem u.mem →
      Steps P_real u (f3EmptyBlackBoxGhostHookK keep P_sub entryTarget u) ∧
      ExecFrozen (f3EmptyBlackBoxGhostHookK keep P_sub entryTarget u).mem ∧
      InvMem (f3EmptyBlackBoxGhostHookK keep P_sub entryTarget u).mem ∧
      (f3EmptyBlackBoxGhostHookK keep P_sub entryTarget u).fs = u.fs := by
  refine ⟨hreal_stub_none, fun u hpc hrun hnoex hfr hinv => ?_⟩
  obtain ⟨hvis, hfr_sf, hfs_sf⟩ :=
    f3EmptyBlackBoxGhostHookK_visitedIn_of_process hsvc_sub hsub_no hsub_proc hrun hnoex hfr
      (hInvLoaded u.mem hfr hinv)
  have hSteps := (hStub u hpc hrun hfr hinv).trans (hLiftVis u _ hrun hfr hinv hvis)
  exact ⟨hSteps, hfr_sf, hInvKf u.mem _ hinv hSteps.keepsFrozen, hfs_sf⟩

/-- Single-row `GhostExternReplaysS` packager for `f3EmptyBlackBoxGhostHook` via `hLiftVis`. -/
theorem f3EmptyBlackBoxGhostHook_replaysS_of_visitedIn_process {P_ghost : Program}
    (hghost_stub : P_ghost.externAt? stubPc = some (f3EmptyBlackBoxGhostHook keep P_sub entryTarget))
    (hother : ∀ pc, pc ≠ stubPc → P_ghost.externAt? pc = P_real.externAt? pc)
    (hreal_pres : ∀ pc f, P_real.externAt? pc = some f →
      ∀ u : State, u.status = .Running → u.mem.KeepsFrozen (f u).mem →
        ExecFrozen u.mem → InvMem u.mem → ExecFrozen (f u).mem ∧ InvMem (f u).mem) :
    GhostExternReplaysS keep (fun u => InvMem u.mem) P_ghost P_real := by
  have ⟨hnone, hstep⟩ :=
    f3EmptyBlackBoxGhostHook_replayOn_of_visitedIn_process hsvc_sub hsub_no hsub_proc
      hreal_stub_none hStub hInvLoaded hInvKf hLiftVis
  exact ghostExternReplaysS_of_single_stub hghost_stub hother hreal_pres
    ⟨hnone, fun u hpc hrun hnoex hfr hlr hinv =>
      let ⟨hs, hfr', hinv', _⟩ := hstep u hpc hrun hnoex hfr hlr hinv; ⟨hs, hfr', hinv'⟩⟩

/-- Single-row `GhostExternReplaysS keep_any` packager for `f3EmptyBlackBoxGhostHookK` via `hLiftVis`. -/
theorem f3EmptyBlackBoxGhostHookK_replaysS_of_visitedIn_process {keep_any : BitVec 64 → Bool} {P_ghost : Program}
    (hghost_stub : P_ghost.externAt? stubPc = some (f3EmptyBlackBoxGhostHookK keep P_sub entryTarget))
    (hother : ∀ pc, pc ≠ stubPc → P_ghost.externAt? pc = P_real.externAt? pc)
    (hreal_pres : ∀ pc f, P_real.externAt? pc = some f →
      ∀ u : State, u.status = .Running → u.mem.KeepsFrozen (f u).mem →
        ExecFrozen u.mem → InvMem u.mem → ExecFrozen (f u).mem ∧ InvMem (f u).mem) :
    GhostExternReplaysS keep_any (fun u => InvMem u.mem) P_ghost P_real := by
  have ⟨hnone, hstep⟩ :=
    f3EmptyBlackBoxGhostHookK_replayOn_of_visitedIn_process hsvc_sub hsub_no hsub_proc
      hreal_stub_none hStub hInvLoaded hInvKf hLiftVis
  exact ghostExternReplaysS_of_single_stub hghost_stub hother hreal_pres
    ⟨hnone, fun u hpc hrun hnoex hfr _ hinv =>
      let ⟨hs, hfr', hinv', _⟩ := hstep u hpc hrun hnoex hfr hinv; ⟨hs, hfr', hinv'⟩⟩

end StockSafeVisitedInReplays

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BlackBoxGhost

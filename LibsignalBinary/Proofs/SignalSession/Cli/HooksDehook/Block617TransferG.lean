/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer -- proof-setup: allow-public-import

/-!
# Generalized Guarded Block-`617` Ghost-to-Real Seam (`HooksDehook.Block617TransferG`)

Untrusted (`Role::Proof`, `0` edits to `Ghost617Transfer.lean` or `Specifications/`) generalization
of `Ghost617Transfer.Block617TransferFixedHyp` and `block617TransferFixed_of_replaysOn` for
Variant A (`rev_q8.md` §1b–§1c) and multi-pass ghost-to-real transfers:

1. **`withEntryGuard` & `Block617TransferFixedHypG` (D1a):**
   Generalizes `Block617TransferFixedHyp` over arbitrary ghost and real extern-table families
   `EG ER : CliHooks → String → Option (State → State)` and a real-side entry-state guard
   `Guard : State → Prop` (`withEntryGuard Guard spec` prepends `⌜Guard s0⌝ ∗` to `pre` while
   keeping `post`, `onPanic`, `onExit`, and `onOom` definitionally unchanged, and keeps the ghost
   side on the exact `b2MainSpecTightNeedLocksFineAt` spec).
2. **`block617TransferFixedHyp_of_G` (D1b):**
   Instantiating `EG := fun W' => cliGhostExterns ghFixed (cliExternsPlaced mmpl W')`,
   `ER := cliExternsPlaced mmpl`, and `Guard := fun _ => True` recovers the exact existing
   `Block617TransferFixedHyp` (showing `Block617TransferFixedHypG` is a pure generalization).
   **Non-drop-in note (`rev_c8` T4):** With a non-trivial `Guard`, `Block617TransferFixedHypG` has
   a **weaker** real-side conclusion (`subroutine_ok` under `withEntryGuard Guard`, requiring
   `⌜Guard s0⌝` at entry) than the trusted `Block617TransferFixedHyp` (equivalent only at
   `Guard := fun _ => True`), so it is **not** a drop-in replacement for `Block617TransferFixedHyp`.
3. **`block617TransferFixedG_of_replaysOn` & `block617TransferFixedG_of_replaysOn_outcome` (D1c):**
   Mirrors `block617TransferFixed_of_replaysOn` via `subroutine_ok_transfer_ghostS` over generic
   `EG`/`ER`/`Guard` and a `hNoNewHooks` hypothesis, forwarding `Guard s0` together with
   `sf.status = .Running → sf.pc = s0.readReg64 .lr`, `∀ msg, sf.status ≠ .Exception msg`, and
   `sf.status ≠ .Halted` (or the full `SubroutineOutcome` in the `_outcome` variant) into `hTraj`
   instead of dropping the `Returned` PC equality.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Block617TransferG

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.SepLogic
open CryptoVerification.SignalSession
  (CliHooks Inputs cliExternsPlaced cliProcessInputs libsignalSessionLib)
open CryptoVerification.SignalSession.Cli (MainGhost RunAnswer)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (ExecFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2
  (b2MainSpecTightNeedLocksFineAt cliBudgetLimits)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
  (cliProgExtPlacedAt cliStaticsPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer
  (Block617TransferFixedHyp GhostExternReplaysOn subroutine_ok_transfer_ghostS)

/-! ## 1. Real-Side Entry-State Guard Wrapper (`withEntryGuard`) -/

/-- Prepend a pure entry-state guard `⌜Guard s⌝ ∗` to `spec.pre` while leaving `post`, `onPanic`,
    `onExit`, and `onOom` definitionally unchanged. -/
@[expose] def withEntryGuard {α : Type} (Guard : State → Prop) (spec : Spec α) : Spec α :=
  { spec with pre := fun x s => ⌜Guard s⌝ ∗ spec.pre x s }

theorem withEntryGuard_pre {α : Type} (Guard : State → Prop) (spec : Spec α)
    (x : α) (s : State) :
    (withEntryGuard Guard spec).pre x s = (⌜Guard s⌝ ∗ spec.pre x s) :=
  rfl

theorem withEntryGuard_outcome_eq {α : Type} (Guard : State → Prop) (spec : Spec α)
    (x : α) (R : SepProp) (s0 sf : State) :
    SubroutineOutcome (withEntryGuard Guard spec) x R s0 sf =
      SubroutineOutcome spec x R s0 sf :=
  rfl

/-- Contravariant weakening of `withEntryGuard` under `∀ s, Guard' s → Guard s`. -/
theorem subroutine_ok_withEntryGuard_mono {α : Type}
    {prog : Program} {entry : BitVec 64} {Guard Guard' : State → Prop} {spec : Spec α}
    (hImp : ∀ s : State, Guard' s → Guard s)
    (h : subroutine_ok prog entry (withEntryGuard Guard spec)) :
    subroutine_ok prog entry (withEntryGuard Guard' spec) := by
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hsp _ => ?_
  dsimp only [withEntryGuard] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  have hpre' : s0.mem ⊨ (withEntryGuard Guard spec).pre x s0 ∗ R := by
    dsimp only [withEntryGuard]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hImp s0 hpre.1, hpre.2⟩
  exact h.mono_outcome x R s0 hpc hrun hpre' hsp fun _ hout => hout

/-- Any unguarded `subroutine_ok prog entry spec` immediately satisfies `withEntryGuard Guard spec`. -/
theorem subroutine_ok_withEntryGuard_of_plain {α : Type}
    {prog : Program} {entry : BitVec 64} (Guard : State → Prop) {spec : Spec α}
    (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (withEntryGuard Guard spec) := by
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hsp _ => ?_
  dsimp only [withEntryGuard] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact h.mono_outcome x R s0 hpc hrun hpre.2 hsp fun _ hout => hout

/-! ## 2. Generalized Block-`617` Transfer Hypothesis (`Block617TransferFixedHypG`) & Pure Generalization Proof -/

/-- **D1(a): Generalized Block-`617` Ghost-to-Real Transfer Hypothesis (`Block617TransferFixedHypG`).**
    Parameterizes `Block617TransferFixedHyp` by:
    - ghost and real extern-table functions `EG ER : CliHooks → String → Option (State → State)`,
    - a real-side entry-state guard `Guard : State → Prop` (wrapped via `withEntryGuard Guard`,
      keeping `post`/`onPanic`/`onExit`/`onOom` and the ghost-side Tight spec unchanged).
    Note (`rev_c8` T4): with a non-trivial `Guard`, this conclusion is **weaker** than the trusted
    `Block617TransferFixedHyp` (equivalent only at `Guard := fun _ => True`), so it is not a drop-in. -/
@[expose] def Block617TransferFixedHypG
    (mpl mmpl : Obj.MultiPlacement)
    (EG ER : CliHooks → String → Option (State → State))
    (Guard : State → Prop)
    (CodeOk_ghost CodeOk_real : Memory → Prop)
    (libcAddr brkStart : BitVec 64) (stk : Nat) : Prop :=
  ∀ (W : CliHooks) (Run : Inputs → RunAnswer → Prop),
    (∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok
        (cliProgExtPlacedAt mpl EG 617 W)
        (mpl.base 617)
        (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk_ghost
          (fineHookRustCliAllocBudget γ mmpl tp brkStart)
          cliBudgetLimits fineCostModel.init stk (cliStaticsPlacedAt mpl) Run cliProcessInputs)) →
    ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok
        (cliProgExtPlacedAt mpl ER 617 W)
        (mpl.base 617)
        (withEntryGuard Guard
          (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk_real
            (fineHookRustCliAllocBudget γ mmpl tp brkStart)
            cliBudgetLimits fineCostModel.init stk (cliStaticsPlacedAt mpl) Run cliProcessInputs))

/-- Monotonicity of `Block617TransferFixedHypG` in the real-side entry guard `Guard`. -/
theorem Block617TransferFixedHypG.mono_guard
    {mpl mmpl : Obj.MultiPlacement}
    {EG ER : CliHooks → String → Option (State → State)}
    {Guard Guard' : State → Prop}
    {CodeOk_ghost CodeOk_real : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {stk : Nat}
    (hImp : ∀ s : State, Guard' s → Guard s)
    (hG : Block617TransferFixedHypG mpl mmpl EG ER Guard CodeOk_ghost CodeOk_real
      libcAddr brkStart stk) :
    Block617TransferFixedHypG mpl mmpl EG ER Guard' CodeOk_ghost CodeOk_real
      libcAddr brkStart stk :=
  fun W Run hGhostOk γ tp => subroutine_ok_withEntryGuard_mono hImp (hG W Run hGhostOk γ tp)

/-- **D1(b): Pure generalization check (`block617TransferFixedHyp_of_G`).**
    Instantiating `EG := fun W' => cliGhostExterns ghFixed (cliExternsPlaced mmpl W')`,
    `ER := cliExternsPlaced mmpl`, and `Guard := fun _ => True` recovers the exact existing
    `Block617TransferFixedHyp`. -/
theorem block617TransferFixedHyp_of_G
    {mpl mmpl : Obj.MultiPlacement} {ghFixed : CliGhostHooks}
    {CodeOk_ghost CodeOk_real : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {stk : Nat}
    (hG : Block617TransferFixedHypG mpl mmpl
      (fun W' => cliGhostExterns ghFixed (cliExternsPlaced mmpl W'))
      (cliExternsPlaced mmpl)
      (fun _ => True)
      CodeOk_ghost CodeOk_real libcAddr brkStart stk) :
    Block617TransferFixedHyp mpl mmpl ghFixed CodeOk_ghost CodeOk_real libcAddr brkStart stk := by
  intro W Run hGhostOk γ tp
  exact subroutine_ok_of_pure_true _ (hG W Run hGhostOk γ tp)

/-- Converse of `block617TransferFixedHyp_of_G`: `Block617TransferFixedHyp` implies
    `Block617TransferFixedHypG` for any `Guard` at the F3 extern tables. -/
theorem block617TransferFixedHypG_of_fixed
    {mpl mmpl : Obj.MultiPlacement} {ghFixed : CliGhostHooks}
    {CodeOk_ghost CodeOk_real : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {stk : Nat}
    (Guard : State → Prop)
    (hFixed : Block617TransferFixedHyp mpl mmpl ghFixed CodeOk_ghost CodeOk_real
      libcAddr brkStart stk) :
    Block617TransferFixedHypG mpl mmpl
      (fun W' => cliGhostExterns ghFixed (cliExternsPlaced mmpl W'))
      (cliExternsPlaced mmpl)
      Guard CodeOk_ghost CodeOk_real libcAddr brkStart stk :=
  fun W Run hGhostOk γ tp => subroutine_ok_withEntryGuard_of_plain Guard (hFixed W Run hGhostOk γ tp)

/-! ## 3. Outcome-Preserving `replaysOn` Discharge (`block617TransferFixedG_of_replaysOn`) -/

private theorem findSome?_const_none {α β : Type} (l : List α) :
    (l.findSome? fun _ => (none : Option β)) = none := by
  induction l with
  | nil => rfl
  | cons _ tl ih => exact ih

private theorem findSome?_none_mono (tbl : List (String × Nat))
    {ext1 ext2 : String → Option (State → State)}
    (hmono : ∀ n, ext1 n = none → ext2 n = none) (off : Nat)
    (h : (tbl.findSome? fun x => if x.2 == off then ext1 x.1 else none) = none) :
    (tbl.findSome? fun x => if x.2 == off then ext2 x.1 else none) = none := by
  induction tbl with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.findSome?_cons] at h ⊢
    cases hoo : (hd.2 == off) with
    | false =>
      simp only [hoo, Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact ih h
    | true =>
      simp only [hoo, ↓reduceIte] at h ⊢
      cases he1 : ext1 hd.1 with
      | some _ => rw [he1] at h; cases h
      | none =>
        rw [he1] at h
        rw [hmono hd.1 he1]
        exact ih h

/-- Lift symbol-level hook monotonicity (`EG W sym = none → ER W sym = none`) to PC-level
    `hNoNewHooks` on `cliProgExtPlacedAt mpl _ idx W`. -/
theorem noNewHooks_cliProgExtPlacedAt_of_ext_none_imp
    (mpl : Obj.MultiPlacement) (idx : Nat)
    {EG ER : CliHooks → String → Option (State → State)}
    (hmono : ∀ (W : CliHooks) (sym : String), EG W sym = none → ER W sym = none) :
    ∀ (W : CliHooks) (pc : BitVec 64),
      (cliProgExtPlacedAt mpl EG idx W).externAt? pc = none →
      (cliProgExtPlacedAt mpl ER idx W).externAt? pc = none := by
  intro W pc h
  unfold cliProgExtPlacedAt Obj.MultiPlacedLib.blockProgram Obj.PlacedLib.program
    Program.externAt? Program.hookAtOff? at h ⊢
  simp only [ite_self] at h ⊢
  rw [findSome?_const_none, Option.or_none] at h ⊢
  exact findSome?_none_mono _ (hmono W) _ h

/-- Extract the generic terminal facts needed by link-transfer and closed-trap arguments from any
    `SubroutineOutcome spec x R s0 sf`:
    1. `sf.status = .Running → sf.pc = s0.readReg64 .lr` (from the `Returned` branch),
    2. `∀ msg, sf.status ≠ .Exception msg`,
    3. `sf.status ≠ .Halted`. -/
theorem subroutineOutcome_running_pc_and_noFault
    {α : Type} {spec : Spec α} {x : α} {R : SepProp} {s0 sf : State}
    (hout : SubroutineOutcome spec x R s0 sf) :
    (sf.status = .Running → sf.pc = s0.readReg64 .lr) ∧
    (∀ msg, sf.status ≠ .Exception msg) ∧
    sf.status ≠ .Halted := by
  rcases hout with ⟨⟨hpc_lr, _, hrun_sf⟩, _, _⟩ | ⟨hp, _⟩ | ⟨_, he, _⟩ | ⟨ho, _⟩
  · refine ⟨fun _ => hpc_lr, ?_, ?_⟩
    · intro _ hex; rw [hrun_sf] at hex; cases hex
    · rw [hrun_sf]; nofun
  · refine ⟨fun hrun => ?_, ?_, ?_⟩
    · rw [hp] at hrun; cases hrun
    · intro _ hex; rw [hp] at hex; cases hex
    · rw [hp]; nofun
  · refine ⟨fun hrun => ?_, ?_, ?_⟩
    · rw [he] at hrun; cases hrun
    · intro _ hex; rw [he] at hex; cases hex
    · rw [he]; nofun
  · refine ⟨fun hrun => ?_, ?_, ?_⟩
    · rw [ho] at hrun; cases hrun
    · intro _ hex; rw [ho] at hex; cases hex
    · rw [ho]; nofun

/-- Full-`SubroutineOutcome` companion of `block617TransferFixedG_of_replaysOn`, forwarding both
    `Guard s0` and `hout : SubroutineOutcome (b2MainSpecTightNeedLocksFineAt …) g R s0 sf` to
    `hTraj`. -/
theorem block617TransferFixedG_of_replaysOn_outcome
    {mpl mmpl : Obj.MultiPlacement}
    {EG ER : CliHooks → String → Option (State → State)}
    {Guard : State → Prop}
    {CodeOk_ghost CodeOk_real : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {stk : Nat}
    (keep : BitVec 64 → Bool) (InvMem : Memory → Prop) (PredFs : FsState → Prop)
    (hNoNewHooks : ∀ (W : CliHooks) (pc : BitVec 64),
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none →
      (cliProgExtPlacedAt mpl ER 617 W).externAt? pc = none)
    (hCode : ∀ m : Memory, CodeOk_real m → CodeOk_ghost m)
    (hGhostCL : ∀ (W : CliHooks) (m : Memory), CodeOk_ghost m →
      (cliProgExtPlacedAt mpl EG 617 W).CodeLoaded m)
    (hFr0 : ∀ m : Memory, CodeOk_real m → ExecFrozen m)
    (hInv0 : ∀ m : Memory, CodeOk_real m → InvMem m)
    (hInvStable : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    (hFs0 : ∀ i : Inputs, PredFs (initFsState (cliProcessInputs i)))
    (hTraj : ∀ (W : CliHooks) (Run : Inputs → RunAnswer → Prop)
      (γ : GhostName) (tp : BitVec 64) (g : MainGhost) (R : SepProp) (s0 sf : State),
      let P_ghost := cliProgExtPlacedAt mpl EG 617 W
      let P_real := cliProgExtPlacedAt mpl ER 617 W
      let spec_ghost := b2MainSpecTightNeedLocksFineAt libcAddr CodeOk_ghost
        (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        cliBudgetLimits fineCostModel.init stk (cliStaticsPlacedAt mpl) Run cliProcessInputs
      Guard s0 →
      CodeOk_real s0.mem →
      s0.pc = mpl.base 617 →
      s0.fs = initFsState (cliProcessInputs g.i) →
      s0.trace = [] →
      Steps P_ghost s0 sf →
      SubroutineOutcome spec_ghost g R s0 sf →
      GhostExternReplaysOn keep (fun u => InvMem u.mem ∧ PredFs u.fs) P_ghost P_real s0 sf ∧
      (∀ z, Steps P_ghost s0 z → Steps P_ghost (Syscall.standard z) sf →
        z.status = .Running → P_ghost.externAt? z.pc = none →
        P_ghost.fetchMem z.mem z.pc = some (.system false 0#16) →
        ExecFrozen z.mem → InvMem z.mem → PredFs z.fs →
        PredFs (Syscall.standard z).fs) ∧
      (∀ z : State, Steps P_ghost s0 z → Steps P_ghost z sf →
        z.status = .Running → P_ghost.externAt? z.pc ≠ P_real.externAt? z.pc →
        keep (z.readReg64 .lr) = false)) :
    Block617TransferFixedHypG mpl mmpl EG ER Guard CodeOk_ghost CodeOk_real
      libcAddr brkStart stk := by
  intro W Run hGhostOk γ tp
  refine subroutine_ok_transfer_ghostS (keep := keep) (InvMem := InvMem) (PredFs := PredFs)
    rfl rfl (hNoNewHooks W) hInvStable ?_ ?_ (hGhostOk γ tp)
  · intro g R s0 hm hpc _ _
    dsimp only [withEntryGuard, b2MainSpecTightNeedLocksFineAt] at hm ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm
    obtain ⟨hGuard0, hm_real⟩ := hm
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm_real ⊢
    obtain ⟨⟨hReal0, hCase, hInpOk, hEntry, hStk⟩, hm_frame⟩ := hm_real
    have hGhost0 : CodeOk_ghost s0.mem := hCode s0.mem hReal0
    have hFsInit : PredFs s0.fs := hEntry.2.1 ▸ hFs0 g.i
    refine ⟨⟨⟨hGhost0, hCase, hInpOk, hEntry, hStk⟩, hm_frame⟩,
      hGhostCL W s0.mem hGhost0, hFr0 s0.mem hReal0, hInv0 s0.mem hReal0, hFsInit, ?_⟩
    intro sf hsteps hout
    exact hTraj W Run γ tp g R s0 sf hGuard0 hReal0 hpc hEntry.2.1 hEntry.2.2 hsteps hout
  · intro g R s0 sf _ _ _ hout
    exact hout

/-- **D1(c): Generalized `replaysOn` discharge of `Block617TransferFixedHypG`.**
    Mirrors `Ghost617Transfer.block617TransferFixed_of_replaysOn` via `subroutine_ok_transfer_ghostS`
    over generic `EG`/`ER`/`Guard` and `hNoNewHooks`, while passing `Guard s0` and
    `sf.status = .Running → sf.pc = s0.readReg64 .lr` alongside `hnoex`/`hnhalt` to `hTraj`
    (with zero `(Run, γ, tp, R)` clutter in `hTraj`). -/
theorem block617TransferFixedG_of_replaysOn
    {mpl mmpl : Obj.MultiPlacement}
    {EG ER : CliHooks → String → Option (State → State)}
    {Guard : State → Prop}
    {CodeOk_ghost CodeOk_real : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {stk : Nat}
    (keep : BitVec 64 → Bool) (InvMem : Memory → Prop) (PredFs : FsState → Prop)
    (hNoNewHooks : ∀ (W : CliHooks) (pc : BitVec 64),
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none →
      (cliProgExtPlacedAt mpl ER 617 W).externAt? pc = none)
    (hCode : ∀ m : Memory, CodeOk_real m → CodeOk_ghost m)
    (hGhostCL : ∀ (W : CliHooks) (m : Memory), CodeOk_ghost m →
      (cliProgExtPlacedAt mpl EG 617 W).CodeLoaded m)
    (hFr0 : ∀ m : Memory, CodeOk_real m → ExecFrozen m)
    (hInv0 : ∀ m : Memory, CodeOk_real m → InvMem m)
    (hInvStable : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    (hFs0 : ∀ i : Inputs, PredFs (initFsState (cliProcessInputs i)))
    (hTraj : ∀ (W : CliHooks) (i : Inputs) (s0 sf : State),
      let P_ghost := cliProgExtPlacedAt mpl EG 617 W
      let P_real := cliProgExtPlacedAt mpl ER 617 W
      Guard s0 →
      CodeOk_real s0.mem →
      s0.pc = mpl.base 617 →
      s0.fs = initFsState (cliProcessInputs i) →
      s0.trace = [] →
      Steps P_ghost s0 sf →
      (sf.status = .Running → sf.pc = s0.readReg64 .lr) →
      (∀ msg, sf.status ≠ .Exception msg) →
      sf.status ≠ .Halted →
      GhostExternReplaysOn keep (fun u => InvMem u.mem ∧ PredFs u.fs) P_ghost P_real s0 sf ∧
      (∀ z, Steps P_ghost s0 z → Steps P_ghost (Syscall.standard z) sf →
        z.status = .Running → P_ghost.externAt? z.pc = none →
        P_ghost.fetchMem z.mem z.pc = some (.system false 0#16) →
        ExecFrozen z.mem → InvMem z.mem → PredFs z.fs →
        PredFs (Syscall.standard z).fs) ∧
      (∀ z : State, Steps P_ghost s0 z → Steps P_ghost z sf →
        z.status = .Running → P_ghost.externAt? z.pc ≠ P_real.externAt? z.pc →
        keep (z.readReg64 .lr) = false)) :
    Block617TransferFixedHypG mpl mmpl EG ER Guard CodeOk_ghost CodeOk_real
      libcAddr brkStart stk := by
  refine block617TransferFixedG_of_replaysOn_outcome keep InvMem PredFs
    hNoNewHooks hCode hGhostCL hFr0 hInv0 hInvStable hFs0
    fun W _Run _γ _tp g _R s0 sf hGuard0 hReal0 hpc hfs0 htr0 hsteps hout => ?_
  obtain ⟨hret_pc, hnoex, hnhalt⟩ := subroutineOutcome_running_pc_and_noFault hout
  exact hTraj W g.i s0 sf hGuard0 hReal0 hpc hfs0 htr0 hsteps hret_pc hnoex hnhalt

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Block617TransferG

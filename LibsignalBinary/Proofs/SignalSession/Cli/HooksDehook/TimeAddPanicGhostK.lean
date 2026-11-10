/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TimeAddPanicGhost -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc -- proof-setup: allow-public-import

/-!
# `<SystemTime as Add<Duration>>::add` `WithLsRet` / `WithAlloc` Suite & `W`-Independent `StepsVisitedIn` Replay (`HooksDehook.TimeAddPanicGhostK`)

**Not trusted (`Role::Proof`, Card `K4` Commit 2 / `hooks-prep/k4-panic-strip`).**

Completes the `<SystemTime as Add<Duration>>::add` ghost-hook & stock-safe replay package on top of
`HooksDehook.TimeAddPanicGhost` and `HooksDehook.StripRunPanicExterns` (§4):

1. **`WithLsRet.withLsRet` & `WithAlloc.withAlloc` Consumer `HookOk` Suite (`§1`)**:
   Exposes `HookOk` for `timeAddGhostHook` (`withLrGuard lrOk`) and `timeAddGhostHookLsRet`
   (`[LibsignalPlacement]`, stated directly with `WithLsRet.withLsRet`) across all consumer specs
   (`masterTimeAddSpec`, `keepsFs timeAddSpec`, `LibsignalPublicApi.timeAddSpec`,
   `E2E.HooksE.timeAddSpec`, `Heap.SpecBudget.timeAddBudgetSpec`,
   `keepsFs Heap.SpecBudget.timeAddBudgetSpec`, and `WithAlloc.withAlloc` pool-threaded forms),
   plus fixed-`P_real` Arm-2 `GhostExternReplaysOn`.
2. **`W`-Independent `timeAddGhostHookExternOnly` & `timeAddGhostHookExternOnlyLsRet` (`§2`)**:
   Fixes `P_real := externOnlyStdProg (timeAddBlk2Prog timeMpl externs)` so the ghost hook `f`
   depends only on `(lrOk, keep, timeMpl, externs)` (independent of per-invocation `W`), and proves
   `W`-independent `fs`, `HookFsTraced`, `VmPreserved`, and the full `withLrGuard` /
   `WithLsRet.withLsRet` / `WithAlloc.withAlloc` `HookOk` suite.
3. **Stock-Safe `StepsVisitedIn` Replays onto Arbitrary `P_real` (`§3`)**:
   Instantiates `StripRunPanicExterns.ghostExternReplaysOn_externOnly_visitedIn_panicExterns` (and
   `_of_invLr` / `ghostExternReplaysS_of_single_stub`) to replay `timeAddGhostHookExternOnly` /
   `timeAddGhostHookExternOnlyLsRet` onto any linked program `P_real` (e.g. `cliLinkedProgram W`).
   Note (`REV-K4` disclosure c): `StubReachesTargetOn InvMem P_real stubPc entry` executes directly
   on `P_real` (`u →*[P_real] u.setPC entry`), never on the `code := []` carrier `externOnlyStdProg`,
   while `linkedCallHook_externOnly_visitedIn_with_externs` + `steps_externOnly_to_real_of_visitedIn`
   lift the subroutine body `u.setPC entry →* f u` onto `P_real`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TimeAddPanicGhostK

open Arm64 ProofLib
open Arm64.Obj (MultiPlacement)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (timeAddBudgetSpec withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  ExecFrozen linkedCallHook
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit (withPreGuard)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer (
  GhostExternReplaysS StubReachesTargetOn
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookOn (
  ghostExternReplaysS_of_single_stub
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StripRunPanicExterns (
  externOnlyStdProg externOnlyStdProg_externAt externOnlyStdProg_svc
  ghostExternReplaysOn_externOnly_visitedIn_panicExterns
  ghostExternReplaysOn_externOnly_visitedIn_panicExterns_of_invLr
  ghostExternReplaysOn_of_linkedCallHook_panicExterns
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TimeAddPanicGhost (
  masterTimeAddSpec specPreservesFsTrace_withLrGuard_masterTimeAdd
  specStripSInvariant_withLrGuard_masterTimeAdd timeAddBlk2Prog
  timeAddBlk2Prog_externAt_none_of_keep timeAddBlk2Prog_externAt_stub
  timeAddBlk2Prog_hlr_ne timeAddBlk2Prog_panicExterns
  timeAddBlk2Prog_svc timeAddBlk2Prog_withLrGuard_masterTimeAddSpec_ok
  timeAddExpectFailedStubPc timeAddGhostHook timeAddGhostHook_e2eTimeAddSpec_ok
  timeAddGhostHook_fs timeAddGhostHook_fsT timeAddGhostHook_lrOk_of_noException
  timeAddGhostHook_master_ok timeAddGhostHook_timeAddBudgetSpec_keepsFs_ok
  timeAddGhostHook_timeAddBudgetSpec_ok timeAddGhostHook_timeAddSpec_keepsFs_ok
  timeAddGhostHook_timeAddSpec_ok timeAddGhostHook_vmPreserved timeAddGhostHookLsRet
  withLrGuard withLrGuard_masterTimeAdd_outcome_setPC withLrGuard_masterTimeAdd_pre_setPC
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc (
  hookOk_withAlloc_of_withVmPreserved hookOk_withAlloc_withVmPreserved withAlloc
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (withLsRet)
open VerifiedLibraries.RustStd (rustTimeExpectFailedSym timeAddSym timeMultiLib)

/-! ## 0. Commutation of `withLrGuard` / `WithLsRet.withLsRet` with `WithAlloc.withAlloc` -/

/-- `withLrGuard lrOk` commutes with `withAlloc A lim` by `sepConj_assoc`. -/
theorem withLrGuard_withAlloc (lrOk : BitVec 64 → Prop) {α : Type} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (spec : Spec α) :
    withLrGuard lrOk (withAlloc (M := M) A lim spec) =
      withAlloc (M := M) A lim (withLrGuard lrOk spec) := by
  unfold withLrGuard withPreGuard withAlloc
  congr 1
  funext ⟨x, st⟩ s
  exact (sepConj_assoc _ _ _).symm

/-- `WithLsRet.withLsRet` commutes with `withAlloc A lim` by `sepConj_assoc`. -/
theorem withLsRet_withAlloc [LibsignalPlacement] {α : Type} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (spec : Spec α) :
    withLsRet (withAlloc (M := M) A lim spec) =
      withAlloc (M := M) A lim (withLsRet spec) :=
  withLrGuard_withAlloc LsRetAddr624 A lim spec

/-! ## 1. `WithLsRet.withLsRet` / `WithAlloc` Consumer `HookOk` Suite & Fixed-`P_real` Replays -/

section FixedRealSuite

variable {keep : BitVec 64 → Bool} {P_real : Program} {timeMpl : MultiPlacement}
variable {externs : String → Option (State → State)}
variable (hpl : timeMultiLib.Placeable timeMpl)
variable (hsvc_real : P_real.svc = Syscall.standard)
variable (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
variable (hpan_sub : externs rustTimeExpectFailedSym = some Rust.panicked)
variable (hpan_real : P_real.externAt? (timeAddExpectFailedStubPc timeMpl) = some Rust.panicked)

include hpl hsvc_real hreal_no hpan_sub hpan_real

theorem timeAddGhostHook_timeAddSpec_withAlloc_ok {lrOk : BitVec 64 → Prop}
    (hlr_ne_stub : ∀ lr : BitVec 64, lrOk lr → lr ≠ timeAddExpectFailedStubPc timeMpl)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk (timeAddGhostHook lrOk keep P_real timeMpl externs)
      (withLrGuard lrOk (withAlloc (M := M) A lim CryptoVerification.LibsignalPublicApi.timeAddSpec)) := by
  rw [withLrGuard_withAlloc]
  exact hookOk_withAlloc_of_withVmPreserved A lim
    (timeAddGhostHook_timeAddBudgetSpec_ok hpl hsvc_real hreal_no hpan_sub hpan_real hlr_ne_stub)

theorem timeAddGhostHook_timeAddBudgetSpec_withAlloc_ok {lrOk : BitVec 64 → Prop}
    (hlr_ne_stub : ∀ lr : BitVec 64, lrOk lr → lr ≠ timeAddExpectFailedStubPc timeMpl)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk (timeAddGhostHook lrOk keep P_real timeMpl externs)
      (withLrGuard lrOk (withAlloc (M := M) A lim timeAddBudgetSpec)) := by
  rw [withLrGuard_withAlloc]
  change HookOk (timeAddGhostHook lrOk keep P_real timeMpl externs)
    (withAlloc (M := M) A lim
      (withVmPreserved (withLrGuard lrOk CryptoVerification.LibsignalPublicApi.timeAddSpec)))
  exact hookOk_withAlloc_withVmPreserved A lim
    (timeAddGhostHook_timeAddBudgetSpec_ok hpl hsvc_real hreal_no hpan_sub hpan_real hlr_ne_stub)

section LsRetConsumerSuite

variable [LibsignalPlacement]
variable (hlr_ne_stub : ∀ lr : BitVec 64, LsRetAddr624 lr → lr ≠ timeAddExpectFailedStubPc timeMpl)

include hlr_ne_stub

theorem timeAddGhostHookLsRet_master_ok :
    HookOk (timeAddGhostHookLsRet keep P_real timeMpl externs)
      (withLsRet (masterTimeAddSpec extHookStack)) :=
  timeAddGhostHook_master_ok hpl hsvc_real hreal_no hpan_sub hpan_real hlr_ne_stub

theorem timeAddGhostHookLsRet_timeAddSpec_keepsFs_ok :
    HookOk (timeAddGhostHookLsRet keep P_real timeMpl externs)
      (withLsRet (keepsFs CryptoVerification.LibsignalPublicApi.timeAddSpec)) :=
  timeAddGhostHook_timeAddSpec_keepsFs_ok hpl hsvc_real hreal_no hpan_sub hpan_real hlr_ne_stub

theorem timeAddGhostHookLsRet_timeAddSpec_ok :
    HookOk (timeAddGhostHookLsRet keep P_real timeMpl externs)
      (withLsRet CryptoVerification.LibsignalPublicApi.timeAddSpec) :=
  timeAddGhostHook_timeAddSpec_ok hpl hsvc_real hreal_no hpan_sub hpan_real hlr_ne_stub

theorem timeAddGhostHookLsRet_e2eTimeAddSpec_ok :
    HookOk (timeAddGhostHookLsRet keep P_real timeMpl externs)
      (withLsRet CryptoVerification.E2E.HooksE.timeAddSpec) :=
  timeAddGhostHook_e2eTimeAddSpec_ok hpl hsvc_real hreal_no hpan_sub hpan_real hlr_ne_stub

theorem timeAddGhostHookLsRet_timeAddBudgetSpec_ok :
    HookOk (timeAddGhostHookLsRet keep P_real timeMpl externs)
      (withLsRet timeAddBudgetSpec) :=
  timeAddGhostHook_timeAddBudgetSpec_ok hpl hsvc_real hreal_no hpan_sub hpan_real hlr_ne_stub

theorem timeAddGhostHookLsRet_timeAddBudgetSpec_keepsFs_ok :
    HookOk (timeAddGhostHookLsRet keep P_real timeMpl externs)
      (withLsRet (keepsFs timeAddBudgetSpec)) :=
  timeAddGhostHook_timeAddBudgetSpec_keepsFs_ok hpl hsvc_real hreal_no hpan_sub hpan_real hlr_ne_stub

theorem timeAddGhostHookLsRet_timeAddSpec_withAlloc_ok
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk (timeAddGhostHookLsRet keep P_real timeMpl externs)
      (withLsRet (withAlloc (M := M) A lim CryptoVerification.LibsignalPublicApi.timeAddSpec)) :=
  timeAddGhostHook_timeAddSpec_withAlloc_ok hpl hsvc_real hreal_no hpan_sub hpan_real hlr_ne_stub A lim

theorem timeAddGhostHookLsRet_timeAddBudgetSpec_withAlloc_ok
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk (timeAddGhostHookLsRet keep P_real timeMpl externs)
      (withLsRet (withAlloc (M := M) A lim timeAddBudgetSpec)) :=
  timeAddGhostHook_timeAddBudgetSpec_withAlloc_ok
    hpl hsvc_real hreal_no hpan_sub hpan_real hlr_ne_stub A lim

end LsRetConsumerSuite

end FixedRealSuite

/-- Memory-guarded Arm-2 replay (`GhostExternReplaysOn` shape) for `timeAddGhostHook` via §3
    `ghostExternReplaysOn_of_linkedCallHook_panicExterns`. -/
theorem timeAddGhostHook_replaysOn
    {InvMem : Memory → Prop} {lrOk : BitVec 64 → Prop} {keep : BitVec 64 → Bool}
    {P_real : Program} {stubPc : BitVec 64} {timeMpl : MultiPlacement}
    {externs : String → Option (State → State)}
    (hpl : timeMultiLib.Placeable timeMpl)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hpan_sub : externs rustTimeExpectFailedSym = some Rust.panicked)
    (hpan_real : P_real.externAt? (timeAddExpectFailedStubPc timeMpl) = some Rust.panicked)
    (hlr_ne_stub : ∀ lr : BitVec 64, lrOk lr → lr ≠ timeAddExpectFailedStubPc timeMpl)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc (timeMultiLib.fnAddr timeMpl timeAddSym))
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      (timeAddBlk2Prog timeMpl externs).CodeLoaded (stripExecOutside keep m))
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m') :
    P_real.externAt? stubPc = none ∧
    ∀ u : State, u.pc = stubPc → u.status = .Running →
      (∀ msg, (timeAddGhostHook lrOk keep P_real timeMpl externs u).status ≠ .Exception msg) →
      ExecFrozen u.mem → keep (u.readReg64 .lr) = false → InvMem u.mem →
      Steps P_real u (timeAddGhostHook lrOk keep P_real timeMpl externs u) ∧
      ExecFrozen (timeAddGhostHook lrOk keep P_real timeMpl externs u).mem ∧
      InvMem (timeAddGhostHook lrOk keep P_real timeMpl externs u).mem :=
  ghostExternReplaysOn_of_linkedCallHook_panicExterns
    hsvc_real (timeAddBlk2Prog_svc timeMpl externs) hreal_no
    (timeAddBlk2Prog_panicExterns hpan_sub hpan_real)
    (fun _ _ s0 hpre pc e he => by
      dsimp only [withLrGuard, withPreGuard] at hpre
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      exact timeAddBlk2Prog_hlr_ne (hlr_ne_stub (s0.readReg64 .lr) hpre.1) pc e he)
    hreal_stub_none hStub hInvLoaded hInvKf
    (timeAddBlk2Prog_withLrGuard_masterTimeAddSpec_ok lrOk hpl hpan_sub)
    (specStripSInvariant_withLrGuard_masterTimeAdd keep lrOk extHookStack)
    (specPreservesFsTrace_withLrGuard_masterTimeAdd lrOk extHookStack)
    (withLrGuard_masterTimeAdd_pre_setPC lrOk extHookStack)
    (withLrGuard_masterTimeAdd_outcome_setPC lrOk extHookStack)

/-- Zero-`keep(u.lr)` Arm-2 replay for `timeAddGhostHook` deriving `keep (u.lr) = false` from `noException`. -/
theorem timeAddGhostHook_replaysOn_of_lrKeep
    {InvMem : Memory → Prop} {lrOk : BitVec 64 → Prop} {keep : BitVec 64 → Bool}
    {P_real : Program} {stubPc : BitVec 64} {timeMpl : MultiPlacement}
    {externs : String → Option (State → State)}
    (hpl : timeMultiLib.Placeable timeMpl)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hpan_sub : externs rustTimeExpectFailedSym = some Rust.panicked)
    (hpan_real : P_real.externAt? (timeAddExpectFailedStubPc timeMpl) = some Rust.panicked)
    (hlr_keep : ∀ lr : BitVec 64, lrOk lr → keep lr = false)
    (hlr_ne_stub : ∀ lr : BitVec 64, lrOk lr → lr ≠ timeAddExpectFailedStubPc timeMpl)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc (timeMultiLib.fnAddr timeMpl timeAddSym))
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      (timeAddBlk2Prog timeMpl externs).CodeLoaded (stripExecOutside keep m))
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m') :
    P_real.externAt? stubPc = none ∧
    ∀ u : State, u.pc = stubPc → u.status = .Running →
      (∀ msg, (timeAddGhostHook lrOk keep P_real timeMpl externs u).status ≠ .Exception msg) →
      ExecFrozen u.mem → InvMem u.mem →
      Steps P_real u (timeAddGhostHook lrOk keep P_real timeMpl externs u) ∧
      ExecFrozen (timeAddGhostHook lrOk keep P_real timeMpl externs u).mem ∧
      InvMem (timeAddGhostHook lrOk keep P_real timeMpl externs u).mem := by
  have hbase := timeAddGhostHook_replaysOn
    hpl hsvc_real hreal_no hpan_sub hpan_real hlr_ne_stub hreal_stub_none hStub hInvLoaded hInvKf
  exact ⟨hbase.1, fun u hpc hrun hnoex hfr hinv =>
    hbase.2 u hpc hrun hnoex hfr
      (hlr_keep (u.readReg64 .lr) (timeAddGhostHook_lrOk_of_noException hnoex)) hinv⟩

/-- `[LibsignalPlacement]` `LsRetAddr624` (`withLsRet`) specialization of
    `timeAddGhostHook_replaysOn_of_lrKeep`. -/
theorem timeAddGhostHookLsRet_replaysOn [LibsignalPlacement]
    {InvMem : Memory → Prop} {keep : BitVec 64 → Bool}
    {P_real : Program} {stubPc : BitVec 64} {timeMpl : MultiPlacement}
    {externs : String → Option (State → State)}
    (hpl : timeMultiLib.Placeable timeMpl)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hpan_sub : externs rustTimeExpectFailedSym = some Rust.panicked)
    (hpan_real : P_real.externAt? (timeAddExpectFailedStubPc timeMpl) = some Rust.panicked)
    (hlr_keep : ∀ lr : BitVec 64, LsRetAddr624 lr → keep lr = false)
    (hlr_ne_stub : ∀ lr : BitVec 64, LsRetAddr624 lr → lr ≠ timeAddExpectFailedStubPc timeMpl)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc (timeMultiLib.fnAddr timeMpl timeAddSym))
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      (timeAddBlk2Prog timeMpl externs).CodeLoaded (stripExecOutside keep m))
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m') :
    P_real.externAt? stubPc = none ∧
    ∀ u : State, u.pc = stubPc → u.status = .Running →
      (∀ msg, (timeAddGhostHookLsRet keep P_real timeMpl externs u).status ≠ .Exception msg) →
      ExecFrozen u.mem → InvMem u.mem →
      Steps P_real u (timeAddGhostHookLsRet keep P_real timeMpl externs u) ∧
      ExecFrozen (timeAddGhostHookLsRet keep P_real timeMpl externs u).mem ∧
      InvMem (timeAddGhostHookLsRet keep P_real timeMpl externs u).mem :=
  timeAddGhostHook_replaysOn_of_lrKeep
    hpl hsvc_real hreal_no hpan_sub hpan_real hlr_keep hlr_ne_stub hreal_stub_none hStub
    hInvLoaded hInvKf

/-! ## 2. `W`-Independent `timeAddGhostHookExternOnly` & `WithLsRet` / `WithAlloc` `HookOk` Suite -/

/-- `W`-independent ghost `<SystemTime as Add<Duration>>::add` hook fixing the `ActiveRealRun`
    carrier to `externOnlyStdProg (timeAddBlk2Prog timeMpl externs)`. -/
@[expose] noncomputable def timeAddGhostHookExternOnly
    (lrOk : BitVec 64 → Prop) (keep : BitVec 64 → Bool)
    (timeMpl : MultiPlacement)
    (externs : String → Option (State → State)) : State → State :=
  timeAddGhostHook lrOk keep (externOnlyStdProg (timeAddBlk2Prog timeMpl externs)) timeMpl externs

/-- `[LibsignalPlacement]` `WithLsRet.withLsRet` (`LsRetAddr624`) specialization of
    `timeAddGhostHookExternOnly`. -/
noncomputable abbrev timeAddGhostHookExternOnlyLsRet [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (timeMpl : MultiPlacement)
    (externs : String → Option (State → State)) : State → State :=
  timeAddGhostHookExternOnly LsRetAddr624 keep timeMpl externs

theorem timeAddGhostHookExternOnly_eq
    (lrOk : BitVec 64 → Prop) (keep : BitVec 64 → Bool)
    (timeMpl : MultiPlacement) (externs : String → Option (State → State)) :
    timeAddGhostHookExternOnly lrOk keep timeMpl externs =
      linkedCallHook keep (externOnlyStdProg (timeAddBlk2Prog timeMpl externs))
        (timeAddBlk2Prog timeMpl externs)
        (timeMultiLib.fnAddr timeMpl timeAddSym)
        (withLrGuard lrOk (masterTimeAddSpec extHookStack))
        CryptoVerification.E2E.timeAddHook := rfl

private theorem externOnly_timeAdd_hpan_real
    {timeMpl : MultiPlacement} {externs : String → Option (State → State)}
    (hpan_sub : externs rustTimeExpectFailedSym = some Rust.panicked) :
    (externOnlyStdProg (timeAddBlk2Prog timeMpl externs)).externAt?
      (timeAddExpectFailedStubPc timeMpl) = some Rust.panicked := by
  rw [externOnlyStdProg_externAt, timeAddBlk2Prog_externAt_stub]
  exact hpan_sub

theorem timeAddGhostHookExternOnly_fs
    (lrOk : BitVec 64 → Prop) (keep : BitVec 64 → Bool)
    (timeMpl : MultiPlacement) (externs : String → Option (State → State)) (s0 : State) :
    (timeAddGhostHookExternOnly lrOk keep timeMpl externs s0).fs = s0.fs :=
  timeAddGhostHook_fs lrOk keep _ timeMpl externs s0

theorem timeAddGhostHookExternOnly_fsT
    (lrOk : BitVec 64 → Prop) (keep : BitVec 64 → Bool)
    (timeMpl : MultiPlacement) (externs : String → Option (State → State)) :
    HookFsTraced IsFsC (timeAddGhostHookExternOnly lrOk keep timeMpl externs) :=
  timeAddGhostHook_fsT lrOk keep _ timeMpl externs

theorem timeAddGhostHookExternOnly_lrOk_of_noException
    {lrOk : BitVec 64 → Prop} {keep : BitVec 64 → Bool}
    {timeMpl : MultiPlacement} {externs : String → Option (State → State)} {u : State}
    (hnoex : ∀ msg,
      (timeAddGhostHookExternOnly lrOk keep timeMpl externs u).status ≠ .Exception msg) :
    lrOk (u.readReg64 .lr) :=
  timeAddGhostHook_lrOk_of_noException hnoex

section ExternOnlyHookOkSuite

variable {keep : BitVec 64 → Bool} {timeMpl : MultiPlacement}
variable {externs : String → Option (State → State)}
variable (hpl : timeMultiLib.Placeable timeMpl)
variable (hkeep_stub : keep (timeAddExpectFailedStubPc timeMpl) = false)
variable (hpan_sub : externs rustTimeExpectFailedSym = some Rust.panicked)

include hpl hkeep_stub hpan_sub

theorem timeAddGhostHookExternOnly_vmPreserved {lrOk : BitVec 64 → Prop}
    (hlr_ne_stub : ∀ lr : BitVec 64, lrOk lr → lr ≠ timeAddExpectFailedStubPc timeMpl)
    (s0 : State) :
    VmPreserved s0 (timeAddGhostHookExternOnly lrOk keep timeMpl externs s0) :=
  timeAddGhostHook_vmPreserved hpl (externOnlyStdProg_svc _)
    (fun pc hk => by
      rw [externOnlyStdProg_externAt]
      exact timeAddBlk2Prog_externAt_none_of_keep hkeep_stub pc hk)
    hpan_sub (externOnly_timeAdd_hpan_real hpan_sub) hlr_ne_stub s0

theorem timeAddGhostHookExternOnly_master_ok {lrOk : BitVec 64 → Prop}
    (hlr_ne_stub : ∀ lr : BitVec 64, lrOk lr → lr ≠ timeAddExpectFailedStubPc timeMpl) :
    HookOk (timeAddGhostHookExternOnly lrOk keep timeMpl externs)
      (withLrGuard lrOk (masterTimeAddSpec extHookStack)) :=
  timeAddGhostHook_master_ok hpl (externOnlyStdProg_svc _)
    (fun pc hk => by
      rw [externOnlyStdProg_externAt]
      exact timeAddBlk2Prog_externAt_none_of_keep hkeep_stub pc hk)
    hpan_sub (externOnly_timeAdd_hpan_real hpan_sub) hlr_ne_stub

theorem timeAddGhostHookExternOnly_timeAddSpec_keepsFs_ok {lrOk : BitVec 64 → Prop}
    (hlr_ne_stub : ∀ lr : BitVec 64, lrOk lr → lr ≠ timeAddExpectFailedStubPc timeMpl) :
    HookOk (timeAddGhostHookExternOnly lrOk keep timeMpl externs)
      (withLrGuard lrOk (keepsFs CryptoVerification.LibsignalPublicApi.timeAddSpec)) :=
  timeAddGhostHook_timeAddSpec_keepsFs_ok hpl (externOnlyStdProg_svc _)
    (fun pc hk => by
      rw [externOnlyStdProg_externAt]
      exact timeAddBlk2Prog_externAt_none_of_keep hkeep_stub pc hk)
    hpan_sub (externOnly_timeAdd_hpan_real hpan_sub) hlr_ne_stub

theorem timeAddGhostHookExternOnly_timeAddSpec_ok {lrOk : BitVec 64 → Prop}
    (hlr_ne_stub : ∀ lr : BitVec 64, lrOk lr → lr ≠ timeAddExpectFailedStubPc timeMpl) :
    HookOk (timeAddGhostHookExternOnly lrOk keep timeMpl externs)
      (withLrGuard lrOk CryptoVerification.LibsignalPublicApi.timeAddSpec) :=
  timeAddGhostHook_timeAddSpec_ok hpl (externOnlyStdProg_svc _)
    (fun pc hk => by
      rw [externOnlyStdProg_externAt]
      exact timeAddBlk2Prog_externAt_none_of_keep hkeep_stub pc hk)
    hpan_sub (externOnly_timeAdd_hpan_real hpan_sub) hlr_ne_stub

theorem timeAddGhostHookExternOnly_e2eTimeAddSpec_ok {lrOk : BitVec 64 → Prop}
    (hlr_ne_stub : ∀ lr : BitVec 64, lrOk lr → lr ≠ timeAddExpectFailedStubPc timeMpl) :
    HookOk (timeAddGhostHookExternOnly lrOk keep timeMpl externs)
      (withLrGuard lrOk CryptoVerification.E2E.HooksE.timeAddSpec) :=
  timeAddGhostHook_e2eTimeAddSpec_ok hpl (externOnlyStdProg_svc _)
    (fun pc hk => by
      rw [externOnlyStdProg_externAt]
      exact timeAddBlk2Prog_externAt_none_of_keep hkeep_stub pc hk)
    hpan_sub (externOnly_timeAdd_hpan_real hpan_sub) hlr_ne_stub

theorem timeAddGhostHookExternOnly_timeAddBudgetSpec_ok {lrOk : BitVec 64 → Prop}
    (hlr_ne_stub : ∀ lr : BitVec 64, lrOk lr → lr ≠ timeAddExpectFailedStubPc timeMpl) :
    HookOk (timeAddGhostHookExternOnly lrOk keep timeMpl externs)
      (withLrGuard lrOk timeAddBudgetSpec) :=
  timeAddGhostHook_timeAddBudgetSpec_ok hpl (externOnlyStdProg_svc _)
    (fun pc hk => by
      rw [externOnlyStdProg_externAt]
      exact timeAddBlk2Prog_externAt_none_of_keep hkeep_stub pc hk)
    hpan_sub (externOnly_timeAdd_hpan_real hpan_sub) hlr_ne_stub

theorem timeAddGhostHookExternOnly_timeAddBudgetSpec_keepsFs_ok {lrOk : BitVec 64 → Prop}
    (hlr_ne_stub : ∀ lr : BitVec 64, lrOk lr → lr ≠ timeAddExpectFailedStubPc timeMpl) :
    HookOk (timeAddGhostHookExternOnly lrOk keep timeMpl externs)
      (withLrGuard lrOk (keepsFs timeAddBudgetSpec)) :=
  timeAddGhostHook_timeAddBudgetSpec_keepsFs_ok hpl (externOnlyStdProg_svc _)
    (fun pc hk => by
      rw [externOnlyStdProg_externAt]
      exact timeAddBlk2Prog_externAt_none_of_keep hkeep_stub pc hk)
    hpan_sub (externOnly_timeAdd_hpan_real hpan_sub) hlr_ne_stub

theorem timeAddGhostHookExternOnly_timeAddSpec_withAlloc_ok {lrOk : BitVec 64 → Prop}
    (hlr_ne_stub : ∀ lr : BitVec 64, lrOk lr → lr ≠ timeAddExpectFailedStubPc timeMpl)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk (timeAddGhostHookExternOnly lrOk keep timeMpl externs)
      (withLrGuard lrOk (withAlloc (M := M) A lim CryptoVerification.LibsignalPublicApi.timeAddSpec)) :=
  timeAddGhostHook_timeAddSpec_withAlloc_ok hpl (externOnlyStdProg_svc _)
    (fun pc hk => by
      rw [externOnlyStdProg_externAt]
      exact timeAddBlk2Prog_externAt_none_of_keep hkeep_stub pc hk)
    hpan_sub (externOnly_timeAdd_hpan_real hpan_sub) hlr_ne_stub A lim

theorem timeAddGhostHookExternOnly_timeAddBudgetSpec_withAlloc_ok {lrOk : BitVec 64 → Prop}
    (hlr_ne_stub : ∀ lr : BitVec 64, lrOk lr → lr ≠ timeAddExpectFailedStubPc timeMpl)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk (timeAddGhostHookExternOnly lrOk keep timeMpl externs)
      (withLrGuard lrOk (withAlloc (M := M) A lim timeAddBudgetSpec)) :=
  timeAddGhostHook_timeAddBudgetSpec_withAlloc_ok hpl (externOnlyStdProg_svc _)
    (fun pc hk => by
      rw [externOnlyStdProg_externAt]
      exact timeAddBlk2Prog_externAt_none_of_keep hkeep_stub pc hk)
    hpan_sub (externOnly_timeAdd_hpan_real hpan_sub) hlr_ne_stub A lim

section ExternOnlyLsRetSuite

variable [LibsignalPlacement]
variable (hlr_ne_stub : ∀ lr : BitVec 64, LsRetAddr624 lr → lr ≠ timeAddExpectFailedStubPc timeMpl)

include hlr_ne_stub

theorem timeAddGhostHookExternOnlyLsRet_master_ok :
    HookOk (timeAddGhostHookExternOnlyLsRet keep timeMpl externs)
      (withLsRet (masterTimeAddSpec extHookStack)) :=
  timeAddGhostHookExternOnly_master_ok hpl hkeep_stub hpan_sub hlr_ne_stub

theorem timeAddGhostHookExternOnlyLsRet_timeAddSpec_keepsFs_ok :
    HookOk (timeAddGhostHookExternOnlyLsRet keep timeMpl externs)
      (withLsRet (keepsFs CryptoVerification.LibsignalPublicApi.timeAddSpec)) :=
  timeAddGhostHookExternOnly_timeAddSpec_keepsFs_ok hpl hkeep_stub hpan_sub hlr_ne_stub

theorem timeAddGhostHookExternOnlyLsRet_timeAddSpec_ok :
    HookOk (timeAddGhostHookExternOnlyLsRet keep timeMpl externs)
      (withLsRet CryptoVerification.LibsignalPublicApi.timeAddSpec) :=
  timeAddGhostHookExternOnly_timeAddSpec_ok hpl hkeep_stub hpan_sub hlr_ne_stub

theorem timeAddGhostHookExternOnlyLsRet_e2eTimeAddSpec_ok :
    HookOk (timeAddGhostHookExternOnlyLsRet keep timeMpl externs)
      (withLsRet CryptoVerification.E2E.HooksE.timeAddSpec) :=
  timeAddGhostHookExternOnly_e2eTimeAddSpec_ok hpl hkeep_stub hpan_sub hlr_ne_stub

theorem timeAddGhostHookExternOnlyLsRet_timeAddBudgetSpec_ok :
    HookOk (timeAddGhostHookExternOnlyLsRet keep timeMpl externs)
      (withLsRet timeAddBudgetSpec) :=
  timeAddGhostHookExternOnly_timeAddBudgetSpec_ok hpl hkeep_stub hpan_sub hlr_ne_stub

theorem timeAddGhostHookExternOnlyLsRet_timeAddBudgetSpec_keepsFs_ok :
    HookOk (timeAddGhostHookExternOnlyLsRet keep timeMpl externs)
      (withLsRet (keepsFs timeAddBudgetSpec)) :=
  timeAddGhostHookExternOnly_timeAddBudgetSpec_keepsFs_ok hpl hkeep_stub hpan_sub hlr_ne_stub

theorem timeAddGhostHookExternOnlyLsRet_timeAddSpec_withAlloc_ok
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk (timeAddGhostHookExternOnlyLsRet keep timeMpl externs)
      (withLsRet (withAlloc (M := M) A lim CryptoVerification.LibsignalPublicApi.timeAddSpec)) :=
  timeAddGhostHookExternOnly_timeAddSpec_withAlloc_ok hpl hkeep_stub hpan_sub hlr_ne_stub A lim

theorem timeAddGhostHookExternOnlyLsRet_timeAddBudgetSpec_withAlloc_ok
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk (timeAddGhostHookExternOnlyLsRet keep timeMpl externs)
      (withLsRet (withAlloc (M := M) A lim timeAddBudgetSpec)) :=
  timeAddGhostHookExternOnly_timeAddBudgetSpec_withAlloc_ok
    hpl hkeep_stub hpan_sub hlr_ne_stub A lim

end ExternOnlyLsRetSuite

end ExternOnlyHookOkSuite

/-! ## 3. Stock-Safe `StepsVisitedIn` Replays of `timeAddGhostHookExternOnly` onto `P_real` -/

/-- Stock-safe `StepsVisitedIn` replay of `timeAddGhostHookExternOnly` onto an arbitrary linked
    program `P_real` (fixing `f` before `∀ W`; `hStub` runs directly on `P_real`, never on the
    `code := []` carrier `externOnlyStdProg`). -/
theorem timeAddGhostHookExternOnly_replaysOn
    {InvMem : Memory → Prop} {lrOk : BitVec 64 → Prop} {keep : BitVec 64 → Bool}
    {P_real : Program} {stubPc : BitVec 64} {timeMpl : MultiPlacement}
    {externs : String → Option (State → State)}
    (hpl : timeMultiLib.Placeable timeMpl)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hpan_sub : externs rustTimeExpectFailedSym = some Rust.panicked)
    (hpan_real : P_real.externAt? (timeAddExpectFailedStubPc timeMpl) = some Rust.panicked)
    (hlr_ne_stub : ∀ lr : BitVec 64, lrOk lr → lr ≠ timeAddExpectFailedStubPc timeMpl)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc (timeMultiLib.fnAddr timeMpl timeAddSym))
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      (timeAddBlk2Prog timeMpl externs).CodeLoaded (stripExecOutside keep m))
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m') :
    P_real.externAt? stubPc = none ∧
    ∀ u : State, u.pc = stubPc → u.status = .Running →
      (∀ msg, (timeAddGhostHookExternOnly lrOk keep timeMpl externs u).status ≠ .Exception msg) →
      ExecFrozen u.mem → keep (u.readReg64 .lr) = false → InvMem u.mem →
      Steps P_real u (timeAddGhostHookExternOnly lrOk keep timeMpl externs u) ∧
      ExecFrozen (timeAddGhostHookExternOnly lrOk keep timeMpl externs u).mem ∧
      InvMem (timeAddGhostHookExternOnly lrOk keep timeMpl externs u).mem ∧
      (timeAddGhostHookExternOnly lrOk keep timeMpl externs u).fs = u.fs := by
  have hkeep_stub : keep (timeAddExpectFailedStubPc timeMpl) = false := by
    cases hk : keep (timeAddExpectFailedStubPc timeMpl)
    · rfl
    · have hnone := hreal_no _ hk
      rw [hpan_real] at hnone
      cases hnone
  exact ghostExternReplaysOn_externOnly_visitedIn_panicExterns
    hsvc_real (timeAddBlk2Prog_svc timeMpl externs)
    (timeAddBlk2Prog_externAt_none_of_keep hkeep_stub)
    hreal_no
    (timeAddBlk2Prog_panicExterns hpan_sub hpan_real)
    hreal_stub_none hStub hInvLoaded hInvKf
    (timeAddBlk2Prog_withLrGuard_masterTimeAddSpec_ok lrOk hpl hpan_sub)
    (specStripSInvariant_withLrGuard_masterTimeAdd keep lrOk extHookStack)
    (specPreservesFsTrace_withLrGuard_masterTimeAdd lrOk extHookStack)
    (withLrGuard_masterTimeAdd_pre_setPC lrOk extHookStack)
    (withLrGuard_masterTimeAdd_outcome_setPC lrOk extHookStack)
    (fun u _ _ hnoex _ _ _ pc e he =>
      timeAddBlk2Prog_hlr_ne
        (hlr_ne_stub (u.readReg64 .lr) (timeAddGhostHookExternOnly_lrOk_of_noException hnoex))
        pc e he)

/-- Zero-`keep(u.lr)` `StepsVisitedIn` replay of `timeAddGhostHookExternOnly` onto `P_real`,
    discharging `keep (u.readReg64 .lr) = false` via `hlr_keep` + `noException`. -/
theorem timeAddGhostHookExternOnly_replaysOn_of_lrKeep
    {InvMem : Memory → Prop} {lrOk : BitVec 64 → Prop} {keep : BitVec 64 → Bool}
    {P_real : Program} {stubPc : BitVec 64} {timeMpl : MultiPlacement}
    {externs : String → Option (State → State)}
    (hpl : timeMultiLib.Placeable timeMpl)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hpan_sub : externs rustTimeExpectFailedSym = some Rust.panicked)
    (hpan_real : P_real.externAt? (timeAddExpectFailedStubPc timeMpl) = some Rust.panicked)
    (hlr_keep : ∀ lr : BitVec 64, lrOk lr → keep lr = false)
    (hlr_ne_stub : ∀ lr : BitVec 64, lrOk lr → lr ≠ timeAddExpectFailedStubPc timeMpl)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc (timeMultiLib.fnAddr timeMpl timeAddSym))
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      (timeAddBlk2Prog timeMpl externs).CodeLoaded (stripExecOutside keep m))
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m') :
    P_real.externAt? stubPc = none ∧
    ∀ u : State, u.pc = stubPc → u.status = .Running →
      (∀ msg, (timeAddGhostHookExternOnly lrOk keep timeMpl externs u).status ≠ .Exception msg) →
      ExecFrozen u.mem → InvMem u.mem →
      Steps P_real u (timeAddGhostHookExternOnly lrOk keep timeMpl externs u) ∧
      ExecFrozen (timeAddGhostHookExternOnly lrOk keep timeMpl externs u).mem ∧
      InvMem (timeAddGhostHookExternOnly lrOk keep timeMpl externs u).mem ∧
      (timeAddGhostHookExternOnly lrOk keep timeMpl externs u).fs = u.fs := by
  have hkeep_stub : keep (timeAddExpectFailedStubPc timeMpl) = false := by
    cases hk : keep (timeAddExpectFailedStubPc timeMpl)
    · rfl
    · have hnone := hreal_no _ hk
      rw [hpan_real] at hnone
      cases hnone
  exact ghostExternReplaysOn_externOnly_visitedIn_panicExterns_of_invLr
    hsvc_real (timeAddBlk2Prog_svc timeMpl externs)
    (timeAddBlk2Prog_externAt_none_of_keep hkeep_stub)
    hreal_no
    (timeAddBlk2Prog_panicExterns hpan_sub hpan_real)
    hreal_stub_none hStub hInvLoaded
    (fun u _ _ hnoex _ _ =>
      have hlr := timeAddGhostHookExternOnly_lrOk_of_noException hnoex
      ⟨hlr_keep (u.readReg64 .lr) hlr,
        fun pc e he => timeAddBlk2Prog_hlr_ne (hlr_ne_stub (u.readReg64 .lr) hlr) pc e he⟩)
    hInvKf
    (timeAddBlk2Prog_withLrGuard_masterTimeAddSpec_ok lrOk hpl hpan_sub)
    (specStripSInvariant_withLrGuard_masterTimeAdd keep lrOk extHookStack)
    (specPreservesFsTrace_withLrGuard_masterTimeAdd lrOk extHookStack)
    (withLrGuard_masterTimeAdd_pre_setPC lrOk extHookStack)
    (withLrGuard_masterTimeAdd_outcome_setPC lrOk extHookStack)

/-- `[LibsignalPlacement]` `WithLsRet.withLsRet` (`LsRetAddr624`) specialization of
    `timeAddGhostHookExternOnly_replaysOn_of_lrKeep`. -/
theorem timeAddGhostHookExternOnlyLsRet_replaysOn [LibsignalPlacement]
    {InvMem : Memory → Prop} {keep : BitVec 64 → Bool}
    {P_real : Program} {stubPc : BitVec 64} {timeMpl : MultiPlacement}
    {externs : String → Option (State → State)}
    (hpl : timeMultiLib.Placeable timeMpl)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hpan_sub : externs rustTimeExpectFailedSym = some Rust.panicked)
    (hpan_real : P_real.externAt? (timeAddExpectFailedStubPc timeMpl) = some Rust.panicked)
    (hlr_keep : ∀ lr : BitVec 64, LsRetAddr624 lr → keep lr = false)
    (hlr_ne_stub : ∀ lr : BitVec 64, LsRetAddr624 lr → lr ≠ timeAddExpectFailedStubPc timeMpl)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc (timeMultiLib.fnAddr timeMpl timeAddSym))
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      (timeAddBlk2Prog timeMpl externs).CodeLoaded (stripExecOutside keep m))
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m') :
    P_real.externAt? stubPc = none ∧
    ∀ u : State, u.pc = stubPc → u.status = .Running →
      (∀ msg, (timeAddGhostHookExternOnlyLsRet keep timeMpl externs u).status ≠ .Exception msg) →
      ExecFrozen u.mem → InvMem u.mem →
      Steps P_real u (timeAddGhostHookExternOnlyLsRet keep timeMpl externs u) ∧
      ExecFrozen (timeAddGhostHookExternOnlyLsRet keep timeMpl externs u).mem ∧
      InvMem (timeAddGhostHookExternOnlyLsRet keep timeMpl externs u).mem ∧
      (timeAddGhostHookExternOnlyLsRet keep timeMpl externs u).fs = u.fs :=
  timeAddGhostHookExternOnly_replaysOn_of_lrKeep
    hpl hsvc_real hreal_no hpan_sub hpan_real hlr_keep hlr_ne_stub hreal_stub_none hStub
    hInvLoaded hInvKf

/-- Single-stub `GhostExternReplaysS keep_any (fun u => InvMem u.mem) P_ghost P_real` packager
    (polymorphic in outer `keep_any`) for `timeAddGhostHookExternOnlyLsRet`. -/
theorem timeAddGhostHookExternOnlyLsRet_replaysS [LibsignalPlacement]
    (keep_any : BitVec 64 → Bool)
    {InvMem : Memory → Prop} {keep : BitVec 64 → Bool}
    {P_ghost P_real : Program} {stubPc : BitVec 64} {timeMpl : MultiPlacement}
    {externs : String → Option (State → State)}
    (hghost_stub : P_ghost.externAt? stubPc =
      some (timeAddGhostHookExternOnlyLsRet keep timeMpl externs))
    (hother : ∀ pc, pc ≠ stubPc → P_ghost.externAt? pc = P_real.externAt? pc)
    (hreal_fr : ∀ pc f, P_real.externAt? pc = some f →
      ∀ u : State, u.status = .Running → ExecFrozen u.mem → ExecFrozen (f u).mem)
    (hpl : timeMultiLib.Placeable timeMpl)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hpan_sub : externs rustTimeExpectFailedSym = some Rust.panicked)
    (hpan_real : P_real.externAt? (timeAddExpectFailedStubPc timeMpl) = some Rust.panicked)
    (hlr_keep : ∀ lr : BitVec 64, LsRetAddr624 lr → keep lr = false)
    (hlr_ne_stub : ∀ lr : BitVec 64, LsRetAddr624 lr → lr ≠ timeAddExpectFailedStubPc timeMpl)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc (timeMultiLib.fnAddr timeMpl timeAddSym))
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      (timeAddBlk2Prog timeMpl externs).CodeLoaded (stripExecOutside keep m))
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m') :
    GhostExternReplaysS keep_any (fun u => InvMem u.mem) P_ghost P_real := by
  have hRep := timeAddGhostHookExternOnlyLsRet_replaysOn
    hpl hsvc_real hreal_no hpan_sub hpan_real hlr_keep hlr_ne_stub hreal_stub_none hStub
    hInvLoaded hInvKf
  exact ghostExternReplaysS_of_single_stub hghost_stub hother
    (fun pc f hr u hrun hkf hfr hinv => ⟨hreal_fr pc f hr u hrun hfr, hInvKf u.mem _ hinv hkf⟩)
    ⟨hRep.1, fun u hpc hrun hnoex hfr _ hinv =>
      let ⟨hs, hfr', hinv', _⟩ := hRep.2 u hpc hrun hnoex hfr hinv
      ⟨hs, hfr', hinv'⟩⟩

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TimeAddPanicGhostK

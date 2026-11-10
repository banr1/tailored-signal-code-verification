/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Block617TransferG
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfMemsetEntryGuard
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KHooks
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
import LibsignalBinary.Specifications.LibsignalE2E.HooksMallocng
import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowF3R1Witness
import ProofLib.Hoare.MultiCodeROHook
import ProofLib.MallocngBridge
meta import ProofLib.ProgramReflection

/-!
# Post-Hoc `ExecFrozen` Upgrade and `Block617TransferFixedHyp` Wiring

**Checked by Lean.**

Provides Route-2 trajectory-level `ExecFrozen` upgrade lemmas and `Block617TransferFixedHyp` reductions
over `hole2_ghFixed` and `h2k_ghFixedK`:
1. `h2ef_StepsAll`, per-PC / uniform-`keep` hook-entry predicates (`h2ef_HookEntryLr*`,
   `h2ef_HookEntryCfi*`), post-hoc `ExecFrozen` upgrade, and `Arm64.Step` determinism.
2. Per-hook `keepSet` (`hole2_keepSub` for the six allocator / I/O hooks, `hole2_keep` for
   `stringClone`) and Block-`617` exclusion of `lsStringCloneSym`.
3. `ExecFrozen` preservation across all active hooks of `hole2_ghFixed`, `h2k_ghFixedK`, and
   `cliExternsPlaced mmpl W`.
4. Trajectory, step-upgrade, and `replaysOn` (`keep := fun _ => false`, `PredFs := fun _ => True`)
   reductions for `Block617TransferFixedHyp`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2ExecFrozenWire

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.SepLogic
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification (LibsignalFrozen LibsignalPlacement libsignalSessionExterns)
open CryptoVerification.E2E
  (PqxdhPrims restoreCallerRegs stepRustAlloc1 stepRustDealloc1 writeVecHeader)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase (mallocngHook)
open CryptoVerification.LibsignalAesCbc (returnToLinkRegister)
open CryptoVerification.SignalSession
  (CliHooks Inputs cliElfBytes cliElfImage cliExternsPlaced cliProcessInputs libsignalSessionLib
   lsMemcpySym lsMemsetSym lsReadFileSym lsReadStdinSym lsRustAllocSymCli lsRustAllocZeroedSymCli
   lsRustDeallocSymCli lsRustNoAllocShimSymCli lsRustReallocSymCli lsStringCloneSym)
open CryptoVerification.SignalSession.Cli (RunAnswer)
open CryptoVerification.SignalSession.Cli.MainHops (cliMainStk)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget (stringCloneHookMallocng)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (ExecFrozen keepFsTrace standard_stripS)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook
  (f3ReadFileFallback f3ReadFileFallbackRaw f3ReadFileFixedGhostHook
   f3ReadFileFixedGhostHookFine f3ReadFileFixedGhostHookFineSub
   f3ReadFileFixedGhostHookSub f3ReadFileLinkedHook)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed fdsGe3Closed_initFsState)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadStdinBudgetPlaced (keepFilesTrace)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2
  (b2MainSpecTightNeedLocksFineAt cliBudgetLimits)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks
  (f3AllocFallback f3AllocFallbackRaw f3AllocGhostHookFine f3AllocZeroedGhostHookFine
   f3CliGhostHooksFixed f3DeallocFallback f3DeallocFallbackRaw f3DeallocGhostHookFine
   f3LinkedCallHook f3ReadStdinFallback f3ReadStdinFallbackRaw f3ReadStdinGhostHook
   f3ReadStdinGhostHookFine f3ReadStdinGhostHookFineSub f3ReadStdinGhostHookSub
   f3ReallocFallback f3ReallocFallbackRaw f3ReallocGhostHookFine f3StringCloneFallback)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
  (cliProgExtPlacedAt cliStaticsPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Block617TransferG
  (Block617TransferFixedHypG block617TransferFixedG_of_replaysOn
   subroutineOutcome_running_pc_and_noFault withEntryGuard)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhost (keepMemcpyBlk20)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyLrTrapRet
  (Blk20TrapHook blk20_lr_trap_after_hook_ret)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost (keepMemsetBlk21)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetLrTrapRet
  (Blk21TrapHook blk21_lr_trap_after_hook_ret)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowF3R1Witness
  (f3EmptyMemcpyGhostHookNarrow_execFrozen f3EmptyMemsetGhostHookNarrow_execFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer
  (Block617TransferFixedHyp GhostSymActive
   blockProgram_cliGhostExterns_no_new_hooks cliExternsPlaced_nonMallocng_preserves_fdsGe3Closed
   cliExternsPlaced_preserves_execFrozen cliGhostExterns_none_imp)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics
  (F3CodeInv F3CodeOk)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfMemsetEntryGuard
  (F3MemsetMemcpyEntryLrFalse)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KHooks
  (h2k_allocGhostHookFineK h2k_allocZeroedGhostHookFineK h2k_deallocGhostHookFineK h2k_ghFixedK
   h2k_readFileFixedGhostHookFineK h2k_readFileFixedGhostHookFineSubK h2k_readStdinGhostHookFineK
   h2k_readStdinGhostHookFineSubK h2k_reallocGhostHookFineK h2k_strCloneGhostHookK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
  (hole2_ActiveStrCloneRun hole2_emptyProg hole2_ghFixed hole2_hookStack hole2_keep
   hole2_keepSub hole2_strCloneGhostHook hole2_targets)
open VerifiedLibraries (mallocngLib)
open VerifiedLibraries.Mallocng (mallocngAddrsOfPlacement)

/-! ## `h2ef_StepsAll`, Hook-Entry Predicates, and `ExecFrozen` Upgrade -/

/-- Trajectory-carrying small-step closure: `Steps P s1 s3` where every `Step P s s'` along the
    path satisfies `Q P s`. -/
inductive h2ef_StepsAll (Q : Program → State → Prop) (P : Program) : State → State → Prop where
  | refl (s : State) : h2ef_StepsAll Q P s s
  | step {s1 s2 s3 : State} (hq : Q P s1) (h1 : Step P s1 s2) (h2 : h2ef_StepsAll Q P s2 s3) :
      h2ef_StepsAll Q P s1 s3

theorem h2ef_stepsAll_toSteps {Q : Program → State → Prop} {P : Program} {s1 s2 : State}
    (h : h2ef_StepsAll Q P s1 s2) : Steps P s1 s2 := by
  induction h with
  | refl s => exact Steps.refl s
  | step _ h1 _ ih => exact Steps.step h1 ih

theorem h2ef_stepsAll_trans {Q : Program → State → Prop} {P : Program} {s1 s2 s3 : State}
    (h12 : h2ef_StepsAll Q P s1 s2) (h23 : h2ef_StepsAll Q P s2 s3) :
    h2ef_StepsAll Q P s1 s3 := by
  induction h12 with
  | refl => exact h23
  | step hq h1 _ ih => exact h2ef_StepsAll.step hq h1 (ih h23)

theorem h2ef_stepsAll_codeLoaded {Q : Program → State → Prop} {P : Program} {s1 s2 : State}
    (h : h2ef_StepsAll Q P s1 s2) (hL : P.CodeLoaded s1.mem) : P.CodeLoaded s2.mem :=
  (h2ef_stepsAll_toSteps h).codeLoaded hL

theorem h2ef_stepsAll_keepsFrozen {Q : Program → State → Prop} {P : Program} {s1 s2 : State}
    (h : h2ef_StepsAll Q P s1 s2) : s1.mem.KeepsFrozen s2.mem :=
  (h2ef_stepsAll_toSteps h).keepsFrozen

theorem h2ef_stepsAll_mono {Q1 Q2 : Program → State → Prop} {P : Program} {s1 s2 : State}
    (himp : ∀ s, Q1 P s → Q2 P s) (h : h2ef_StepsAll Q1 P s1 s2) :
    h2ef_StepsAll Q2 P s1 s2 := by
  induction h with
  | refl s => exact h2ef_StepsAll.refl s
  | step hq h1 _ ih => exact h2ef_StepsAll.step (himp _ hq) h1 ih

/-- Per-PC / per-hook return-address predicate (`keepAt s.pc (s.readReg64 .lr) = false`). -/
def h2ef_HookEntryLrAt (keepAt : BitVec 64 → BitVec 64 → Bool) (P : Program) (s : State) : Prop :=
  P.externAt? s.pc ≠ none → keepAt s.pc (s.readReg64 .lr) = false

/-- Per-PC / per-hook CFI + `ExecFrozen` predicate on intermediate states. -/
def h2ef_HookEntryCfiAt (keepAt : BitVec 64 → BitVec 64 → Bool) (P : Program) (s : State) : Prop :=
  P.externAt? s.pc ≠ none → keepAt s.pc (s.readReg64 .lr) = false ∧ ExecFrozen s.mem

/-- Uniform-`keep` hook-entry return-address predicate (`lr` outside `keep`). -/
def h2ef_HookEntryLr (keep : BitVec 64 → Bool) (P : Program) (s : State) : Prop :=
  P.externAt? s.pc ≠ none → keep (s.readReg64 .lr) = false

/-- Uniform-`keep` hook-entry CFI + `ExecFrozen` predicate on intermediate states. -/
def h2ef_HookEntryCfi (keep : BitVec 64 → Bool) (P : Program) (s : State) : Prop :=
  P.externAt? s.pc ≠ none → keep (s.readReg64 .lr) = false ∧ ExecFrozen s.mem

private theorem evalInst_eq_execInst_of_not_isSvc0 (P : Program) {inst : Instr}
    (h : inst.isSvc0 = false) (s : State) :
    P.evalInst inst s = execInst inst s := by
  cases inst <;> simp [Instr.isSvc0] at h
  case system isMrs imm16 =>
    cases isMrs
    · simp at h
      simp [Program.evalInst, execInst, execInstWithSvc, h]
    · rfl
  all_goals rfl

private theorem execInst_preserves_execFrozen_and_fs {inst : Instr} (h : inst.isSvc0 = false)
    {s : State} (hfr : ExecFrozen s.mem) :
    ExecFrozen (execInst inst s).mem ∧ (execInst inst s).fs = s.fs := by
  have hpf := ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 h s
  exact ⟨ExecFrozen.of_perm_eq hfr (congrFun hpf.2.1), hpf.2.2.2.2.2.2⟩

private theorem steps_preserves_halted {P : Program} {s sf : State}
    (h : Steps P s sf) (hs : s.status = .Halted) : sf.status = .Halted := by
  cases h with
  | refl => exact hs
  | step h1 _ =>
    have hrun : s.status = .Running := by cases h1 <;> assumption
    rw [hs] at hrun; cases hrun

private theorem steps_preserves_exception {P : Program} {s sf : State} {msg : String}
    (h : Steps P s sf) (hs : s.status = .Exception msg) : sf.status = .Exception msg := by
  cases h with
  | refl => exact hs
  | step h1 _ =>
    have hrun : s.status = .Running := by cases h1 <;> assumption
    rw [hs] at hrun; cases hrun

private theorem steps_eq_of_not_running {P : Program} {s sf : State}
    (h : Steps P s sf) (hnr : s.status ≠ .Running) : sf = s := by
  cases h with
  | refl => rfl
  | step h1 _ =>
    have hrun : s.status = .Running := by cases h1 <;> assumption
    exact False.elim (hnr hrun)

/-- **Per-PC post-hoc `ExecFrozen` upgrade:** any `h2ef_StepsAll (h2ef_HookEntryLrAt keepAt) P s0 sf`
    to a non-faulting, non-halted outcome automatically upgrades to
    `h2ef_StepsAll (h2ef_HookEntryCfiAt keepAt) P s0 sf ∧ ExecFrozen sf.mem` once `ExecFrozen s0.mem`
    holds and hooks preserve `ExecFrozen` under `keepAt pc (u.readReg64 .lr) = false`. -/
theorem h2ef_stepsAll_upgrade_execFrozen_at {keepAt : BitVec 64 → BitVec 64 → Bool}
    {P : Program} {s0 sf : State}
    (hsvc : P.svc = Syscall.standard)
    (hHookFr : ∀ (pc : BitVec 64) (f : State → State) (u : State),
      P.externAt? pc = some f → u.status = .Running →
      (∀ msg, (f u).status ≠ .Exception msg) →
      u.mem.KeepsFrozen (f u).mem →
      keepAt pc (u.readReg64 .lr) = false →
      ExecFrozen u.mem → ExecFrozen (f u).mem)
    (hsteps : h2ef_StepsAll (h2ef_HookEntryLrAt keepAt) P s0 sf)
    (hnoex : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt : sf.status ≠ .Halted)
    (hfr0 : ExecFrozen s0.mem) :
    h2ef_StepsAll (h2ef_HookEntryCfiAt keepAt) P s0 sf ∧ ExecFrozen sf.mem := by
  induction hsteps with
  | refl s => exact ⟨h2ef_StepsAll.refl s, hfr0⟩
  | @step u v w hq h1 hrest ih =>
    have hcfi_u : h2ef_HookEntryCfiAt keepAt P u := fun hne => ⟨hq hne, hfr0⟩
    cases h1 with
    | halt_unmapped _ _ _ =>
      exact False.elim (hnhalt (steps_preserves_halted (h2ef_stepsAll_toSteps hrest) rfl))
    | extern_fault _ _ _ =>
      exact False.elim (hnoex _ (steps_preserves_exception (h2ef_stepsAll_toSteps hrest) rfl))
    | @exec inst hr hfm =>
      have h1' : Step P u (P.evalInst inst u) := Step.exec hr hfm
      by_cases hsvc0 : inst.isSvc0 = true
      · have hinst : inst = .system false 0#16 := by
          cases inst <;> simp [Instr.isSvc0] at hsvc0
          rcases hsvc0 with ⟨rfl, rfl⟩; rfl
        subst hinst
        have hev : P.evalInst (.system false 0#16) u = Syscall.standard u := by
          simp [Program.evalInst, execInstWithSvc, hsvc]
        obtain ⟨_, hfr_v⟩ := standard_stripS (keep := fun _ => false) hfr0
        rw [hev] at h1' hrest ih
        obtain ⟨hrest', hfr_w⟩ := ih hnoex hnhalt hfr_v
        exact ⟨h2ef_StepsAll.step hcfi_u h1' hrest', hfr_w⟩
      · have hnsvc0 : inst.isSvc0 = false := Bool.eq_false_iff.mpr hsvc0
        have hev : P.evalInst inst u = execInst inst u :=
          evalInst_eq_execInst_of_not_isSvc0 P hnsvc0 u
        have hfr_v : ExecFrozen (execInst inst u).mem :=
          (execInst_preserves_execFrozen_and_fs hnsvc0 hfr0).1
        rw [hev] at h1' hrest ih
        obtain ⟨hrest', hfr_w⟩ := ih hnoex hnhalt hfr_v
        exact ⟨h2ef_StepsAll.step hcfi_u h1' hrest', hfr_w⟩
    | @extern f hr heg hkf hsym =>
      have h1' : Step P u (f u) := Step.extern hr heg hkf hsym
      have hnoex_fu : ∀ msg, (f u).status ≠ .Exception msg := fun msg hex =>
        hnoex msg (steps_preserves_exception (h2ef_stepsAll_toSteps hrest) hex)
      have hlr_u : keepAt u.pc (u.readReg64 .lr) = false := hq (by rw [heg]; nofun)
      have hfr_v : ExecFrozen (f u).mem := hHookFr u.pc f u heg hr hnoex_fu hkf hlr_u hfr0
      obtain ⟨hrest', hfr_w⟩ := ih hnoex hnhalt hfr_v
      exact ⟨h2ef_StepsAll.step hcfi_u h1' hrest', hfr_w⟩

/-- Uniform-`keep` post-hoc `ExecFrozen` upgrade along `h2ef_StepsAll`. -/
theorem h2ef_stepsAll_upgrade_execFrozen {keep : BitVec 64 → Bool} {P : Program} {s0 sf : State}
    (hsvc : P.svc = Syscall.standard)
    (hHookFr : ∀ (pc : BitVec 64) (f : State → State) (u : State),
      P.externAt? pc = some f → u.status = .Running →
      (∀ msg, (f u).status ≠ .Exception msg) →
      u.mem.KeepsFrozen (f u).mem →
      keep (u.readReg64 .lr) = false →
      ExecFrozen u.mem → ExecFrozen (f u).mem)
    (hsteps : h2ef_StepsAll (h2ef_HookEntryLr keep) P s0 sf)
    (hnoex : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt : sf.status ≠ .Halted)
    (hfr0 : ExecFrozen s0.mem) :
    h2ef_StepsAll (h2ef_HookEntryCfi keep) P s0 sf ∧ ExecFrozen sf.mem :=
  h2ef_stepsAll_upgrade_execFrozen_at (keepAt := fun _ => keep) hsvc hHookFr hsteps hnoex hnhalt hfr0

/-- Small-step determinism of `Arm64.Step P`. -/
theorem h2ef_step_det {P : Program} {s s1 s2 : State}
    (h1 : Step P s s1) (h2 : Step P s s2) : s1 = s2 := by
  cases h1 with
  | @exec i1 _ hfm1 =>
    cases h2 with
    | @exec i2 _ hfm2 =>
      cases hfm1.symm.trans hfm2
      rfl
    | halt_unmapped _ hf2 _ =>
      rw [hfm1] at hf2; cases hf2
    | extern _ he2 _ _ =>
      unfold Program.fetchMem at hfm1
      rw [he2] at hfm1; simp at hfm1
    | extern_fault _ he2 _ =>
      unfold Program.fetchMem at hfm1
      rw [he2] at hfm1; simp at hfm1
  | halt_unmapped _ hf1 he1 =>
    cases h2 with
    | exec _ hfm2 =>
      rw [hfm2] at hf1; cases hf1
    | halt_unmapped _ _ _ => rfl
    | extern _ he2 _ _ =>
      rw [he1] at he2; cases he2
    | extern_fault _ he2 _ =>
      rw [he1] at he2; cases he2
  | @extern f1 _ he1 hkf1 hsym1 =>
    cases h2 with
    | exec _ hfm2 =>
      unfold Program.fetchMem at hfm2
      rw [he1] at hfm2; simp at hfm2
    | halt_unmapped _ _ he2 =>
      rw [he1] at he2; cases he2
    | @extern f2 _ he2 _ _ =>
      cases he1.symm.trans he2
      rfl
    | @extern_fault f2 _ he2 hnk2 =>
      cases he1.symm.trans he2
      exact False.elim (hnk2 ⟨hkf1, hsym1⟩)
  | @extern_fault f1 _ he1 hnk1 =>
    cases h2 with
    | exec _ hfm2 =>
      unfold Program.fetchMem at hfm2
      rw [he1] at hfm2; simp at hfm2
    | halt_unmapped _ _ he2 =>
      rw [he1] at he2; cases he2
    | @extern f2 _ he2 hkf2 hsym2 =>
      cases he1.symm.trans he2
      exact False.elim (hnk1 ⟨hkf2, hsym2⟩)
    | extern_fault _ _ _ => rfl

/-- Determinism bridge: if `hAll : h2ef_StepsAll Q P s0 sf` ends in a non-`Running` state `sf`
    (`.Exited`, `.Panicked`, `.OutOfMemory`, etc.), then EVERY `Running` state `u` with
    `Steps P s0 u` satisfies `Q P u` (provided `u` takes at least one step to `sf`, which is
    automatic from `u.status = .Running` and `sf.status ≠ .Running`). -/
theorem h2ef_steps_running_on_stepsAll_of_not_running
    {Q : Program → State → Prop} {P : Program} {s0 sf u : State}
    (hAll : h2ef_StepsAll Q P s0 sf)
    (hpre : Steps P s0 u)
    (hrun : u.status = .Running)
    (hnr_sf : sf.status ≠ .Running) :
    Q P u := by
  induction hAll generalizing u with
  | refl s =>
    have heq : u = s := steps_eq_of_not_running hpre hnr_sf
    subst heq
    exact False.elim (hnr_sf hrun)
  | @step s1 s2 s3 hq hstep _ ih =>
    cases hpre with
    | refl => exact hq
    | step hstep' hrest' =>
      cases h2ef_step_det hstep hstep'
      exact ih hrest' hrun hnr_sf

/-! ## Per-Hook `keepSet` and Block-`617` `stringClone` Exclusion -/

/-- Per-symbol `keepSet`: `hole2_keep` on `lsStringCloneSym` (Block `623`) and `hole2_keepSub`
(`[0x469000, 0x46f000)`) on the six allocator / I/O hooks. -/
def h2ef_keepForSym (sym : String) : BitVec 64 → Bool :=
  if sym == lsStringCloneSym then hole2_keep else hole2_keepSub

/-- Per-PC `keepSet` keyed at Block `623` (`mpl.base 623`): `hole2_keep` at `mpl.base 623`,
    `hole2_keepSub` elsewhere. -/
def h2ef_keepForPc (mpl : MultiPlacement) (pc lr : BitVec 64) : Bool :=
  if pc == mpl.base 623 then hole2_keep lr else hole2_keepSub lr

theorem h2ef_keepSub_false_of_keep_false {a : BitVec 64}
    (h : hole2_keep a = false) : hole2_keepSub a = false := by
  unfold hole2_keep hole2_keepSub at *
  cases hk : decide (0x469000 ≤ a.toNat ∧ a.toNat < 0x46f000)
  · rfl
  · have htrue : decide ((0x4686a0 ≤ a.toNat ∧ a.toNat < 0x468724) ∨
        (0x469000 ≤ a.toNat ∧ a.toNat < 0x46f000)) = true :=
      decide_eq_true (Or.inr (of_decide_eq_true hk))
    rw [htrue] at h
    cases h

theorem h2ef_keepForPc_false_of_keep_false (mpl : MultiPlacement) (pc lr : BitVec 64)
    (h : hole2_keep lr = false) : h2ef_keepForPc mpl pc lr = false := by
  unfold h2ef_keepForPc
  split
  · exact h
  · exact h2ef_keepSub_false_of_keep_false h

theorem h2ef_keepForSym_false_of_keep_false (sym : String) (lr : BitVec 64)
    (h : hole2_keep lr = false) : h2ef_keepForSym sym lr = false := by
  unfold h2ef_keepForSym
  split
  · exact h
  · exact h2ef_keepSub_false_of_keep_false h

open ProofLib.ProgramReflection in
set_option maxRecDepth 4000000 in
private theorem strClone_not_mem_lsNamesB :
    List.elem lsStringCloneSym
      LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData.lsInternedMultiLib.names = false := by
  rfl_kernel

/-- `lsStringCloneSym` is an internal `libsignalSessionLib` block (`623`), NOT in
    `(libsignalSessionLib.blockLib 617).text.externs`: therefore Block-`617` `P_ghost` extern
    dispatch (`hole2_hTrFrozen`) only ever invokes the 6 `hole2_keepSub` hooks + `shim`. -/
theorem h2ef_strClone_not_mem_ext617 :
    lsStringCloneSym ∉ (libsignalSessionLib.blockLib 617).text.externs := by
  intro hmem
  rw [LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData.ls_block617_externs_eq,
    List.mem_map] at hmem
  obtain ⟨idx, hidx_mem, hget⟩ := hmem
  have hlt : idx <
      LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData.lsInternedMultiLib.names.length :=
    Nat.blt_eq.mp (List.all_eq_true.mp
      LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData.ls_sharedExterns_lt idx hidx_mem)
  have hmem_names : lsStringCloneSym ∈
      LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData.lsInternedMultiLib.names := by
    rw [← hget, Arm64.Obj.Interned.getD_of_lt hlt]
    exact List.getElem_mem hlt
  have htrue :
      List.elem lsStringCloneSym
        LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData.lsInternedMultiLib.names = true :=
    List.elem_eq_true_of_mem hmem_names
  rw [strClone_not_mem_lsNamesB] at htrue
  cases htrue

/-! ## `ExecFrozen` Preservation Across `hole2_ghFixed` and `P_ghost` -/

private theorem execFrozen_write8 {m : Memory} (hfr : ExecFrozen m)
    (addr : BitVec 64) (val : BitVec 8) :
    ExecFrozen (m.write8 addr val) := by
  intro a hx
  unfold Memory.perm Memory.write8 Memory.rawPerm at hx ⊢
  dsimp only at hx ⊢
  by_cases ha : a = addr
  · subst ha
    simp only [↓reduceIte] at hx ⊢
    have hfr_a := hfr a
    unfold Memory.perm at hfr_a
    cases hc : m.cells a with
    | none => simp [hc, Option.x] at hx
    | some cb =>
      rw [hc] at hx hfr_a
      rcases cb with ⟨_ | p, _⟩
      · simp [Option.x] at hx
      · rcases p with ⟨r, w, x, lf, an⟩
        dsimp only [Perm.rwx, Option.x, Option.r, Option.w] at hx hfr_a ⊢
        exact hfr_a hx
  · simp only [ha, ↓reduceIte] at hx ⊢
    exact hfr a hx

private theorem execFrozen_write64 {m : Memory} (hfr : ExecFrozen m)
    (addr : BitVec 64) (val : BitVec 64) :
    ExecFrozen (m.write64 addr val) :=
  execFrozen_write8 (execFrozen_write8 (execFrozen_write8 (execFrozen_write8
    (execFrozen_write8 (execFrozen_write8 (execFrozen_write8 (execFrozen_write8 hfr _ _) _ _) _ _) _ _)
    _ _) _ _) _ _) _ _

private theorem execFrozen_writeBytes :
    ∀ {m : Memory}, ExecFrozen m → ∀ (base : BitVec 64) (bs : List (BitVec 8)),
      ExecFrozen (m.writeBytes base bs)
  | _, hfr, _, [] => hfr
  | _, hfr, base, b :: rest =>
    execFrozen_writeBytes (execFrozen_write8 hfr base b) (base + 1#64) rest

private theorem execFrozen_writeVecHeader {m : Memory} (hfr : ExecFrozen m)
    (v cap ptr len : BitVec 64) :
    ExecFrozen (writeVecHeader m v cap ptr len) :=
  execFrozen_write64 (execFrozen_write64 (execFrozen_write64 hfr _ _) _ _) _ _

private theorem execFrozen_loadMultiCodeMem (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement)
    {m : Memory} (hfr : ExecFrozen m) :
    ExecFrozen (loadMultiCodeMem lib mpl m) := by
  intro a
  have hc : (∃ b, (loadMultiCodeMem lib mpl m).cells a =
      some (some { Perm.rx with anon := m.isAnon a }, b)) ∨
      (loadMultiCodeMem lib mpl m).cells a = m.cells a := by
    unfold loadMultiCodeMem; dsimp only; split
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inr rfl
  rcases hc with ⟨b, hb⟩ | hb
  · have hp : (loadMultiCodeMem lib mpl m).perm a = some Perm.rx := by
      unfold Memory.perm; rw [hb]; rfl
    rw [hp]; intro _; exact ⟨rfl, rfl⟩
  · have hp : (loadMultiCodeMem lib mpl m).perm a = m.perm a := by
      unfold Memory.perm; rw [hb]
    rw [hp]; exact hfr a

private theorem execFrozen_restoreMultiCodeMem (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement)
    {m0 mf : Memory} (hfr0 : ExecFrozen m0) (hfrf : ExecFrozen mf) :
    ExecFrozen (restoreMultiCodeMem lib mpl m0 mf) := by
  intro a
  have hc : (restoreMultiCodeMem lib mpl m0 mf).cells a = m0.cells a ∨
      (restoreMultiCodeMem lib mpl m0 mf).cells a = mf.cells a := by
    unfold restoreMultiCodeMem; dsimp only; split
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hc with h | h
  · have hp : (restoreMultiCodeMem lib mpl m0 mf).perm a = m0.perm a := by
      unfold Memory.perm; rw [h]
    rw [hp]; exact hfr0 a
  · have hp : (restoreMultiCodeMem lib mpl m0 mf).perm a = mf.perm a := by
      unfold Memory.perm; rw [h]
    rw [hp]; exact hfrf a

private theorem findSome?_const_none {α β : Type} (xs : List α) (p : α → Bool) :
    (xs.findSome? fun x => if p x then (none : Option β) else none) = none := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.findSome?_cons]
    cases p hd <;> exact ih

private theorem step_none_preserves_execFrozen {prog : Program}
    (hsvc : prog.svc = Syscall.standard)
    (hext : prog.externs = fun _ => none)
    (hovr : prog.overrides = fun _ => none)
    {s s' : State}
    (hstep : Step prog s s')
    (hfr : ExecFrozen s.mem) :
    ExecFrozen s'.mem := by
  cases hstep with
  | @exec inst _ _ =>
    by_cases hsvc0 : inst.isSvc0 = true
    · have hinst : inst = .system false 0#16 := by
        cases inst <;> simp [Instr.isSvc0] at hsvc0
        rcases hsvc0 with ⟨rfl, rfl⟩; rfl
      subst hinst
      have hev : prog.evalInst (.system false 0#16) s = Syscall.standard s := by
        simp [Program.evalInst, execInstWithSvc, hsvc]
      rw [hev]
      exact (standard_stripS (keep := fun _ => false) hfr).2
    · have hnsvc0 : inst.isSvc0 = false := Bool.eq_false_iff.mpr hsvc0
      rw [evalInst_eq_execInst_of_not_isSvc0 prog hnsvc0 s]
      exact (execInst_preserves_execFrozen_and_fs hnsvc0 hfr).1
  | halt_unmapped _ _ _ => exact hfr
  | extern _ he _ _ =>
    unfold Program.externAt? Program.hookAtOff? at he
    rw [hext, hovr, findSome?_const_none, findSome?_const_none] at he
    cases he
  | extern_fault _ _ _ => exact hfr

private theorem steps_none_preserves_execFrozen {prog : Program}
    (hsvc : prog.svc = Syscall.standard)
    (hext : prog.externs = fun _ => none)
    (hovr : prog.overrides = fun _ => none)
    {s0 sf : State}
    (hsteps : Steps prog s0 sf)
    (hfr0 : ExecFrozen s0.mem) :
    ExecFrozen sf.mem := by
  induction hsteps with
  | refl _ => exact hfr0
  | step h1 _ ih => exact ih (step_none_preserves_execFrozen hsvc hext hovr h1 hfr0)

private theorem stepsUntil_toSteps {prog : Program} {stop : State → Prop} {s0 sf : State}
    (h : StepsUntil prog stop s0 sf) : Steps prog s0 sf := by
  induction h with
  | refl s => exact Steps.refl s
  | step _ hstep _ ih => exact Steps.step hstep ih

private theorem execFrozen_codeROSubroutineHook
    (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement) (fnName : String)
    (s0 : State) (hfr0 : ExecFrozen s0.mem) :
    ExecFrozen
      (lib.codeROSubroutineHook mpl fnName (fun _ => none) (fun _ => none) Syscall.standard s0).mem := by
  unfold Obj.MultiPlacedLib.codeROSubroutineHook
  cases Obj.lookupBlockSym fnName lib.blocks with
  | none => exact hfr0
  | some p =>
    rcases p with ⟨i, _⟩
    dsimp only
    split
    · next hex =>
      change ExecFrozen (restoreMultiCodeMem lib mpl s0.mem (Classical.choose hex).mem)
      refine execFrozen_restoreMultiCodeMem lib mpl hfr0 ?_
      have hfrEntry :
          ExecFrozen (multiCodeROHookEntry lib mpl i (lib.fnAddr mpl fnName) s0).mem :=
        execFrozen_loadMultiCodeMem lib mpl hfr0
      exact steps_none_preserves_execFrozen rfl rfl rfl
        (stepsUntil_toSteps (Classical.choose_spec hex).1) hfrEntry
    · exact hfr0

private theorem execFrozen_mallocngHook (mmpl : Obj.MultiPlacement) (fnName : String)
    (s0 : State) (hfr0 : ExecFrozen s0.mem) :
    ExecFrozen (mallocngHook mmpl fnName s0).mem :=
  execFrozen_codeROSubroutineHook mallocngLib mmpl fnName s0 hfr0

private theorem execFrozen_stepRustAlloc1
    (mpl : Obj.MultiPlacement) (zeroed : Bool) (frameBytes size : Nat)
    {k : State → BitVec 64 → State}
    (hk : ∀ s1 p, ExecFrozen s1.mem → ExecFrozen (k s1 p).mem)
    (s : State) (hfr : ExecFrozen s.mem) :
    ExecFrozen (stepRustAlloc1 mpl zeroed frameBytes size k s).mem := by
  cases zeroed <;> simp only [stepRustAlloc1, Bool.false_eq_true, ↓reduceIte]
  · let sCall :=
      (s.writeReg64 .sp (s.sp - BitVec.ofNat 64 frameBytes)).writeReg64 .x0 (BitVec.ofNat 64 size)
    have hfr1 : ExecFrozen
        (mallocngLib.codeROSubroutineHook mpl "malloc" (fun _ => none) (fun _ => none)
          Syscall.standard sCall).mem :=
      execFrozen_codeROSubroutineHook mallocngLib mpl "malloc" sCall hfr
    split
    · exact hfr1
    · split
      · exact hfr1
      · exact hk _ _ hfr1
  · let sCall :=
      (((s.writeReg64 .sp (s.sp - BitVec.ofNat 64 frameBytes)).writeReg64 .x0
        (BitVec.ofNat 64 size)).writeReg64 .x1 1#64)
    have hfr1 : ExecFrozen
        (mallocngLib.codeROSubroutineHook mpl "calloc" (fun _ => none) (fun _ => none)
          Syscall.standard sCall).mem :=
      execFrozen_codeROSubroutineHook mallocngLib mpl "calloc" sCall hfr
    split
    · exact hfr1
    · split
      · exact hfr1
      · exact hk _ _ hfr1

private theorem execFrozen_keepFsTrace {fb : State → State} {s0 : State}
    (h : ExecFrozen (fb s0).mem) : ExecFrozen (keepFsTrace fb s0).mem := h

private theorem execFrozen_keepFilesTrace {fb : State → State} {s0 : State}
    (h : ExecFrozen (fb s0).mem) : ExecFrozen (keepFilesTrace fb s0).mem := by
  classical
  unfold keepFilesTrace
  dsimp only
  split <;> exact h

private theorem execFrozen_f3AllocFallback (mmpl : Obj.MultiPlacement) (zeroed : Bool)
    (s0 : State) (hfr0 : ExecFrozen s0.mem) :
    ExecFrozen (f3AllocFallback mmpl zeroed s0).mem := by
  apply execFrozen_keepFsTrace
  unfold f3AllocFallbackRaw
  dsimp only
  split
  · cases zeroed
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hfr1 : ExecFrozen (mallocngHook mmpl "malloc" s0).mem :=
        execFrozen_mallocngHook mmpl "malloc" s0 hfr0
      split <;> exact hfr1
    · simp only [↓reduceIte]
      have hfr1 : ExecFrozen (mallocngHook mmpl "calloc" (s0.writeReg64 .x1 1#64)).mem :=
        execFrozen_mallocngHook mmpl "calloc" _ hfr0
      split <;> exact hfr1
  · have hfr1 : ExecFrozen
        (mallocngHook mmpl "aligned_alloc"
          ((s0.writeReg64 .x0 (BitVec.ofNat 64 (max (s0.readReg64 .x1).toNat 8))).writeReg64
            .x1 (s0.readReg64 .x0))).mem :=
      execFrozen_mallocngHook mmpl "aligned_alloc" _ hfr0
    split
    · exact hfr1
    · change ExecFrozen (if zeroed && (_ != 0#64) then Memory.writeBytes _ _ _ else _)
      split
      · exact execFrozen_writeBytes hfr1 _ _
      · exact hfr1

private theorem execFrozen_f3DeallocFallback (mmpl : Obj.MultiPlacement)
    (s0 : State) (hfr0 : ExecFrozen s0.mem) :
    ExecFrozen (f3DeallocFallback mmpl s0).mem := by
  apply execFrozen_keepFsTrace
  unfold f3DeallocFallbackRaw
  dsimp only
  have hfr1 : ExecFrozen (mallocngHook mmpl "free" s0).mem :=
    execFrozen_mallocngHook mmpl "free" s0 hfr0
  split <;> exact hfr1

private theorem execFrozen_f3ReallocFallback (mmpl : Obj.MultiPlacement)
    (s0 : State) (hfr0 : ExecFrozen s0.mem) :
    ExecFrozen (f3ReallocFallback mmpl s0).mem := by
  apply execFrozen_keepFsTrace
  unfold f3ReallocFallbackRaw
  dsimp only
  split
  · have hfr1 : ExecFrozen
        (mallocngHook mmpl "realloc" (s0.writeReg64 .x1 (s0.readReg64 .x3))).mem :=
      execFrozen_mallocngHook mmpl "realloc" _ hfr0
    split <;> exact hfr1
  · let sCall := (s0.writeReg64 .x0 (BitVec.ofNat 64 (max (s0.readReg64 .x2).toNat 8))).writeReg64
      .x1 (s0.readReg64 .x3)
    let s1 := mallocngHook mmpl "aligned_alloc" sCall
    have hfr1 : ExecFrozen s1.mem := execFrozen_mallocngHook mmpl "aligned_alloc" sCall hfr0
    split
    · exact hfr1
    · split
      · exact hfr1
      · let copyLen := min (s0.readReg64 .x1).toNat (s0.readReg64 .x3).toNat
        let mCopy :=
          s1.mem.writeBytes (s1.readReg64 .x0) (s1.mem.readBytes (s0.readReg64 .x0) copyLen)
        have hfrCopy : ExecFrozen mCopy := execFrozen_writeBytes hfr1 _ _
        let sFreeCall := ((restoreCallerRegs s0 s1).setMem mCopy).writeReg64 .x0 (s0.readReg64 .x0)
        have hfr2 : ExecFrozen (mallocngHook mmpl "free" sFreeCall).mem :=
          execFrozen_mallocngHook mmpl "free" sFreeCall hfrCopy
        split <;> exact hfr2

private theorem execFrozen_f3StringCloneFallback (mmpl : Obj.MultiPlacement)
    (s0 : State) (hfr0 : ExecFrozen s0.mem) :
    ExecFrozen (f3StringCloneFallback mmpl s0).mem := by
  apply execFrozen_keepFsTrace
  unfold stringCloneHookMallocng
  dsimp only
  split
  · exact execFrozen_writeVecHeader hfr0 _ _ _ _
  · refine execFrozen_stepRustAlloc1 mmpl false _ _ (fun s1 _ hfr1 => ?_) s0 hfr0
    exact execFrozen_writeVecHeader (execFrozen_writeBytes hfr1 _ _) _ _ _ _

private theorem execFrozen_f3ReadFileFallback (mmpl : Obj.MultiPlacement)
    (s0 : State) (hfr0 : ExecFrozen s0.mem) :
    ExecFrozen (f3ReadFileFallback mmpl s0).mem := by
  apply execFrozen_keepFsTrace
  unfold f3ReadFileFallbackRaw
  split
  · exact execFrozen_write64 hfr0 _ _
  · split
    · exact execFrozen_writeVecHeader hfr0 _ _ _ _
    · refine execFrozen_stepRustAlloc1 mmpl false 0 _ (fun s1 _ hfr1 => ?_) s0 hfr0
      exact execFrozen_writeVecHeader (execFrozen_writeBytes hfr1 _ _) _ _ _ _

private theorem execFrozen_f3ReadStdinFallback (mmpl : Obj.MultiPlacement)
    (s0 : State) (hfr0 : ExecFrozen s0.mem) :
    ExecFrozen (f3ReadStdinFallback mmpl s0).mem := by
  apply execFrozen_keepFsTrace
  unfold f3ReadStdinFallbackRaw
  split
  · exact hfr0
  · split
    · split
      · exact execFrozen_writeVecHeader hfr0 _ _ _ _
      · refine execFrozen_stepRustAlloc1 mmpl false 0 _ (fun s1 _ hfr1 => ?_) s0 hfr0
        exact execFrozen_writeVecHeader (execFrozen_writeBytes hfr1 _ _) _ _ _ _
    · exact execFrozen_write64 hfr0 _ _

private theorem execFrozen_f3LinkedCallHook {α : Type}
    (keep : BitVec 64 → Bool) (P_real P_sub : Program)
    (entryTarget : BitVec 64) (specOf : GhostName → BitVec 64 → Spec α)
    (fallback : State → State)
    (hfb : ∀ s : State, ExecFrozen s.mem → ExecFrozen (fallback s).mem)
    (u : State) (hfr : ExecFrozen u.mem) :
    ExecFrozen (f3LinkedCallHook keep P_real P_sub entryTarget specOf fallback u).mem := by
  classical
  unfold f3LinkedCallHook
  split
  · split
    · rename_i hReal
      exact (Classical.choose_spec hReal.2.2.2).2.2.2.2
    · exact execFrozen_keepFsTrace (hfb u hfr)
  · exact hfr

/-- Every active ghost hook `(sym, f)` of `hole2_ghFixed mpl mmpl` preserves `ExecFrozen`. -/
theorem h2ef_hole2_ghFixed_preserves_execFrozen [LibsignalPlacement]
    (mpl mmpl : MultiPlacement) {sym : String} {f : State → State}
    (hAct : GhostSymActive (hole2_ghFixed mpl mmpl) sym f) :
    ∀ u : State, ExecFrozen u.mem → ExecFrozen (f u).mem := by
  intro u hfr
  rcases hAct with
    ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ |
    ⟨_, hsc⟩ | ⟨_, _, hrf⟩ | ⟨_, _, hrs⟩ | ⟨_, hms⟩ | ⟨_, hmc⟩
  · exact execFrozen_f3LinkedCallHook _ _ _ _ _ _ (execFrozen_f3AllocFallback mmpl false) u hfr
  · exact execFrozen_f3LinkedCallHook _ _ _ _ _ _ (execFrozen_f3DeallocFallback mmpl) u hfr
  · exact execFrozen_f3LinkedCallHook _ _ _ _ _ _ (execFrozen_f3ReallocFallback mmpl) u hfr
  · exact execFrozen_f3LinkedCallHook _ _ _ _ _ _ (execFrozen_f3AllocFallback mmpl true) u hfr
  · exact hfr
  · dsimp only [hole2_ghFixed] at hsc
    injection hsc with hfeq; subst hfeq
    classical
    unfold hole2_strCloneGhostHook
    split
    · split
      · rename_i hReal
        exact (Classical.choose_spec hReal.2.2.2.2).2.2.2.2
      · exact execFrozen_keepFsTrace (execFrozen_f3StringCloneFallback mmpl u hfr)
    · exact hfr
  · dsimp only [hole2_ghFixed, f3CliGhostHooksFixed] at hrf
    injection hrf with hsubeq
    have hfeq := (congrArg Subtype.val hsubeq).symm
    subst hfeq
    classical
    dsimp only [f3ReadFileFixedGhostHookFineSub, f3ReadFileFixedGhostHookSub,
      f3ReadFileFixedGhostHook, f3ReadFileLinkedHook]
    split
    · split
      · rename_i hReal
        exact (Classical.choose_spec hReal.2.2.2.2).2.2.2.2
      · exact execFrozen_keepFsTrace (execFrozen_f3ReadFileFallback mmpl u hfr)
    · exact hfr
  · dsimp only [hole2_ghFixed, f3CliGhostHooksFixed] at hrs
    injection hrs with hsubeq
    have hfeq := (congrArg Subtype.val hsubeq).symm
    subst hfeq
    classical
    dsimp only [f3ReadStdinGhostHookFineSub, f3ReadStdinGhostHookSub, f3ReadStdinGhostHook]
    split
    · split
      · rename_i hReal
        exact (Classical.choose_spec hReal.2.2.2).2.2.2.2.2
      · exact execFrozen_keepFilesTrace (execFrozen_f3ReadStdinFallback mmpl u hfr)
    · exact hfr
  · dsimp only [hole2_ghFixed, f3CliGhostHooksFixed] at hms
    injection hms with hfeq; subst hfeq
    exact f3EmptyMemsetGhostHookNarrow_execFrozen mmpl u hfr
  · dsimp only [hole2_ghFixed, f3CliGhostHooksFixed] at hmc
    injection hmc with hfeq; subst hfeq
    exact f3EmptyMemcpyGhostHookNarrow_execFrozen mmpl u hfr

private theorem findSome?_table_exists (tbl : List (String × Nat))
    {ext : String → Option (State → State)} (off : Nat) {f : State → State}
    (h : (tbl.findSome? fun (n, o) => if o == off then ext n else none) = some f) :
    ∃ sym : String, ext sym = some f := by
  induction tbl with
  | nil => simp at h
  | cons hd tl ih =>
    rcases hd with ⟨n, o⟩
    simp only [List.findSome?_cons] at h
    cases hoo : (o == off) with
    | false =>
      simp only [hoo, Bool.false_eq_true, ↓reduceIte] at h
      exact ih h
    | true =>
      simp only [hoo, ↓reduceIte] at h
      cases he : ext n with
      | none => rw [he] at h; exact ih h
      | some g =>
        rw [he] at h
        injection h with hgf
        subst hgf
        exact ⟨n, he⟩

private theorem blockProgram_externAt?_some_exists
    {lib : Obj.MultiPlacedLib} {mpl : Obj.MultiPlacement} {idx : Nat}
    {ext : String → Option (State → State)} {pc : BitVec 64} {f : State → State}
    (h : (lib.blockProgram mpl idx ext).externAt? pc = some f) :
    ∃ sym : String, ext sym = some f := by
  unfold Obj.MultiPlacedLib.blockProgram Obj.PlacedLib.program Program.externAt? Program.hookAtOff? at h
  dsimp only at h
  rw [findSome?_const_none, Option.or_none] at h
  exact findSome?_table_exists _ _ h

private theorem cliGhostExterns_some_cases
    {ghFixed : CliGhostHooks} {baseExt : String → Option (State → State)}
    {sym : String} {f : State → State}
    (h : cliGhostExterns ghFixed baseExt sym = some f) :
    GhostSymActive ghFixed sym f ∨ baseExt sym = some f := by
  unfold cliGhostExterns at h
  cases hc1 : (sym == lsRustAllocSymCli) with
  | true =>
    simp only [hc1, ↓reduceIte] at h; injection h with h
    exact Or.inl (Or.inl ⟨beq_iff_eq.mp hc1, h.symm⟩)
  | false =>
    simp only [hc1, Bool.false_eq_true, ↓reduceIte] at h
    cases hc2 : (sym == lsRustDeallocSymCli) with
    | true =>
      simp only [hc2, ↓reduceIte] at h; injection h with h
      exact Or.inl (Or.inr (Or.inl ⟨beq_iff_eq.mp hc2, h.symm⟩))
    | false =>
      simp only [hc2, Bool.false_eq_true, ↓reduceIte] at h
      cases hc3 : (sym == lsRustReallocSymCli) with
      | true =>
        simp only [hc3, ↓reduceIte] at h; injection h with h
        exact Or.inl (Or.inr (Or.inr (Or.inl ⟨beq_iff_eq.mp hc3, h.symm⟩)))
      | false =>
        simp only [hc3, Bool.false_eq_true, ↓reduceIte] at h
        cases hc4 : (sym == lsRustAllocZeroedSymCli) with
        | true =>
          simp only [hc4, ↓reduceIte] at h; injection h with h
          exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨beq_iff_eq.mp hc4, h.symm⟩))))
        | false =>
          simp only [hc4, Bool.false_eq_true, ↓reduceIte] at h
          cases hc5 : (sym == lsRustNoAllocShimSymCli) with
          | true =>
            simp only [hc5, ↓reduceIte] at h; injection h with h
            exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨beq_iff_eq.mp hc5, h.symm⟩)))))
          | false =>
            simp only [hc5, Bool.false_eq_true, ↓reduceIte] at h
            cases hc6 : (sym == lsStringCloneSym) with
            | true =>
              simp only [hc6, ↓reduceIte] at h
              cases hsc : ghFixed.stringClone with
              | none => rw [hsc] at h; exact Or.inr h
              | some g =>
                rw [hsc] at h; injection h with h; subst h
                exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨beq_iff_eq.mp hc6, hsc⟩))))))
            | false =>
              simp only [hc6, Bool.false_eq_true, ↓reduceIte] at h
              cases hc7 : (sym == lsReadFileSym) with
              | true =>
                simp only [hc7, ↓reduceIte] at h
                cases hrf : ghFixed.readFile with
                | none => rw [hrf] at h; exact Or.inr h
                | some gh =>
                  rcases gh with ⟨g, hg⟩
                  rw [hrf] at h; injection h with h; subst h
                  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨beq_iff_eq.mp hc7, hg, hrf⟩)))))))
              | false =>
                simp only [hc7, Bool.false_eq_true, ↓reduceIte] at h
                cases hc8 : (sym == lsReadStdinSym) with
                | true =>
                  simp only [hc8, ↓reduceIte] at h
                  cases hrs : ghFixed.readStdin with
                  | none => rw [hrs] at h; exact Or.inr h
                  | some gh =>
                    rcases gh with ⟨g, hg⟩
                    rw [hrs] at h; injection h with h; subst h
                    exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨beq_iff_eq.mp hc8, hg, hrs⟩))))))))
                | false =>
                  simp only [hc8, Bool.false_eq_true, ↓reduceIte] at h
                  cases hc9 : (sym == CryptoVerification.SignalSession.lsMemsetSym) with
                  | true =>
                    simp only [hc9, ↓reduceIte] at h
                    cases hms : ghFixed.memset with
                    | none => rw [hms] at h; exact Or.inr h
                    | some g =>
                      rw [hms] at h; injection h with h; subst h
                      exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨beq_iff_eq.mp hc9, hms⟩)))))))))
                  | false =>
                    simp only [hc9, Bool.false_eq_true, ↓reduceIte] at h
                    cases hc10 : (sym == CryptoVerification.SignalSession.lsMemcpySym) with
                    | true =>
                      simp only [hc10, ↓reduceIte] at h
                      cases hmc : ghFixed.memcpy with
                      | none => rw [hmc] at h; exact Or.inr h
                      | some g =>
                        rw [hmc] at h; injection h with h; subst h
                        exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨beq_iff_eq.mp hc10, hmc⟩)))))))))
                    | false =>
                      simp only [hc10, Bool.false_eq_true, ↓reduceIte] at h
                      exact Or.inr h

/-- Every extern hook `f` in `P_ghost` (`hole2_ghFixed mpl mmpl` overlaid on
    `cliExternsPlaced mmpl W`) at any block `idx` preserves `ExecFrozen` unconditionally. -/
theorem h2ef_pGhost_extern_preserves_execFrozen [LibsignalPlacement]
    (mpl mmpl : MultiPlacement) (idx : Nat) (W : CliHooks)
    {pc : BitVec 64} {f : State → State}
    (heg : (cliProgExtPlacedAt mpl
      (fun W' => cliGhostExterns (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W'))
      idx W).externAt? pc = some f) :
    ∀ u : State, ExecFrozen u.mem → ExecFrozen (f u).mem := by
  obtain ⟨sym, hsym⟩ := blockProgram_externAt?_some_exists heg
  rcases cliGhostExterns_some_cases hsym with hAct | hBase
  · exact h2ef_hole2_ghFixed_preserves_execFrozen mpl mmpl hAct
  · exact cliExternsPlaced_preserves_execFrozen mmpl W hBase

/-- Single-step `ExecFrozen` preservation along `P_ghost`. -/
theorem h2ef_pGhost_step_preserves_execFrozen [LibsignalPlacement]
    (mpl mmpl : MultiPlacement) (idx : Nat) (W : CliHooks)
    {s s' : State}
    (hstep : Step (cliProgExtPlacedAt mpl
      (fun W' => cliGhostExterns (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W'))
      idx W) s s')
    (hfr : ExecFrozen s.mem) :
    ExecFrozen s'.mem := by
  let P_ghost := cliProgExtPlacedAt mpl
    (fun W' => cliGhostExterns (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W')) idx W
  cases hstep with
  | @exec inst _ _ =>
    by_cases hsvc0 : inst.isSvc0 = true
    · have hinst : inst = .system false 0#16 := by
        cases inst <;> simp [Instr.isSvc0] at hsvc0
        rcases hsvc0 with ⟨rfl, rfl⟩; rfl
      subst hinst
      have hsvc_g : (cliProgExtPlacedAt mpl
          (fun W' => cliGhostExterns (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W'))
          idx W).svc = Syscall.standard := rfl
      have hev : (cliProgExtPlacedAt mpl
          (fun W' => cliGhostExterns (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W'))
          idx W).evalInst (.system false 0#16) s = Syscall.standard s := by
        simp [Program.evalInst, execInstWithSvc, hsvc_g]
      rw [hev]
      exact (standard_stripS (keep := fun _ => false) hfr).2
    · have hnsvc0 : inst.isSvc0 = false := Bool.eq_false_iff.mpr hsvc0
      rw [evalInst_eq_execInst_of_not_isSvc0 _ hnsvc0 s]
      exact (execInst_preserves_execFrozen_and_fs hnsvc0 hfr).1
  | halt_unmapped _ _ _ => exact hfr
  | extern _ heg _ _ =>
    exact h2ef_pGhost_extern_preserves_execFrozen mpl mmpl idx W heg s hfr
  | extern_fault _ _ _ => exact hfr

/-- Multi-step `ExecFrozen` preservation along `Steps P_ghost s0 u`. -/
theorem h2ef_pGhost_steps_preserves_execFrozen [LibsignalPlacement]
    (mpl mmpl : MultiPlacement) (idx : Nat) (W : CliHooks)
    {s0 u : State}
    (hsteps : Steps (cliProgExtPlacedAt mpl
      (fun W' => cliGhostExterns (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W'))
      idx W) s0 u)
    (hfr0 : ExecFrozen s0.mem) :
    ExecFrozen u.mem := by
  induction hsteps with
  | refl _ => exact hfr0
  | step h1 _ ih =>
    exact ih (h2ef_pGhost_step_preserves_execFrozen mpl mmpl idx W h1 hfr0)

/-- Direct `hole2_hTrFrozen`-entry `ExecFrozen` corollary: from `F3CodeOk mpl mmpl s0.mem` and
    `Steps P_ghost s0 u` at Block `617`, `ExecFrozen u.mem` holds at every intermediate/final `u`. -/
theorem h2ef_pGhost617_steps_execFrozen_of_f3CodeOk [LibsignalPlacement]
    (mpl mmpl : MultiPlacement) (W : CliHooks) {s0 u : State}
    (hReal0 : F3CodeOk mpl mmpl s0.mem)
    (hsteps : Steps (cliProgExtPlacedAt mpl
      (fun W' => cliGhostExterns (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W'))
      617 W) s0 u) :
    ExecFrozen u.mem :=
  h2ef_pGhost_steps_preserves_execFrozen mpl mmpl 617 W hsteps hReal0.2

/-- Concrete per-PC `h2ef_StepsAll` `ExecFrozen` upgrade for `P_ghost` (`h2ef_HookEntryLrAt` →
    `h2ef_HookEntryCfiAt`, e.g. at `keepAt := h2ef_keepForPc mpl`). -/
theorem h2ef_pGhost_upgrade_execFrozen_at [LibsignalPlacement]
    (mpl mmpl : MultiPlacement) (idx : Nat) (W : CliHooks)
    {keepAt : BitVec 64 → BitVec 64 → Bool} {s0 sf : State}
    (hReal0 : F3CodeOk mpl mmpl s0.mem)
    (hsteps : h2ef_StepsAll (h2ef_HookEntryLrAt keepAt)
      (cliProgExtPlacedAt mpl
        (fun W' => cliGhostExterns (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W'))
        idx W) s0 sf)
    (hnoex : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt : sf.status ≠ .Halted) :
    h2ef_StepsAll (h2ef_HookEntryCfiAt keepAt)
      (cliProgExtPlacedAt mpl
        (fun W' => cliGhostExterns (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W'))
        idx W) s0 sf ∧ ExecFrozen sf.mem :=
  h2ef_stepsAll_upgrade_execFrozen_at rfl
    (fun _ _ u heg _ _ _ _ hfr =>
      h2ef_pGhost_extern_preserves_execFrozen mpl mmpl idx W heg u hfr)
    hsteps hnoex hnhalt hReal0.2

/-- Concrete uniform-`keep` `h2ef_StepsAll` `ExecFrozen` upgrade for `P_ghost`. -/
theorem h2ef_pGhost_upgrade_execFrozen [LibsignalPlacement]
    (mpl mmpl : MultiPlacement) (idx : Nat) (W : CliHooks)
    {keep : BitVec 64 → Bool} {s0 sf : State}
    (hReal0 : F3CodeOk mpl mmpl s0.mem)
    (hsteps : h2ef_StepsAll (h2ef_HookEntryLr keep)
      (cliProgExtPlacedAt mpl
        (fun W' => cliGhostExterns (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W'))
        idx W) s0 sf)
    (hnoex : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt : sf.status ≠ .Halted) :
    h2ef_StepsAll (h2ef_HookEntryCfi keep)
      (cliProgExtPlacedAt mpl
        (fun W' => cliGhostExterns (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W'))
        idx W) s0 sf ∧ ExecFrozen sf.mem :=
  h2ef_stepsAll_upgrade_execFrozen rfl
    (fun _ _ u heg _ _ _ _ hfr =>
      h2ef_pGhost_extern_preserves_execFrozen mpl mmpl idx W heg u hfr)
    hsteps hnoex hnhalt hReal0.2

/-! ## `Block617TransferFixedHyp` Wiring Over `hole2_ghFixed` -/

/-- Block-`617` `P_ghost.CodeLoaded` from `LibsignalFrozen mpl m` (`hFrz.2 617`). -/
theorem h2ef_pGhost617_codeLoaded_of_libsignalFrozen [LibsignalPlacement]
    (mpl mmpl : MultiPlacement) (W : CliHooks) (m : Memory)
    (hFrz : LibsignalFrozen mpl m) :
    (cliProgExtPlacedAt mpl
      (fun W' => cliGhostExterns (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W'))
      617 W).CodeLoaded m := by
  have h617 : 617 < libsignalSessionLib.blocks.length := by
    have hlen := Nat.beq_eq.mp
      LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData.libsignalBlocks_len
    have hge : 618 ≤
        LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData.f3LsBlocksLen := by decide
    omega
  have hc := hFrz.2 617 h617
  exact Arm64.Program.CodeLoaded.intro hc.aligned hc.no_wrap fun i hi =>
    ⟨hc.byte_eq i hi, hc.perm_eq i hi, hc.isLazyFree_eq i hi⟩

private theorem findSome?_stubs_cliGhostExterns_mem_cases
    (exts : List String) (ρ : String → BitVec 64) (base pc : BitVec 64)
    (ghFixed : CliGhostHooks) (baseExt : String → Option (State → State))
    {f : State → State}
    (h : ((exts.map fun e => (e, (ρ e - base).toNat)).findSome?
      fun (n, o) => if o == (pc - base).toNat then cliGhostExterns ghFixed baseExt n else none) = some f) :
    ((exts.map fun e => (e, (ρ e - base).toNat)).findSome?
      fun (n, o) => if o == (pc - base).toNat then baseExt n else none) = some f ∨
    ∃ sym : String, sym ∈ exts ∧ GhostSymActive ghFixed sym f ∧ pc = ρ sym := by
  induction exts with
  | nil => simp at h
  | cons e tl ih =>
    simp only [List.map_cons, List.findSome?_cons] at h ⊢
    cases hoo : ((ρ e - base).toNat == (pc - base).toNat) with
    | false =>
      simp only [hoo, Bool.false_eq_true, ↓reduceIte] at h ⊢
      rcases ih h with hL | ⟨sym, hmem, hAct, hpc⟩
      · exact Or.inl hL
      · exact Or.inr ⟨sym, List.mem_cons_of_mem _ hmem, hAct, hpc⟩
    | true =>
      simp only [hoo, ↓reduceIte] at h ⊢
      cases he : cliGhostExterns ghFixed baseExt e with
      | none =>
        rw [he] at h
        rw [cliGhostExterns_none_imp he]
        rcases ih h with hL | ⟨sym, hmem, hAct, hpc⟩
        · exact Or.inl hL
        · exact Or.inr ⟨sym, List.mem_cons_of_mem _ hmem, hAct, hpc⟩
      | some g =>
        rw [he] at h
        injection h with hgf
        subst hgf
        rcases cliGhostExterns_some_cases he with hAct | hBase
        · have heq : ρ e - base = pc - base := BitVec.eq_of_toNat_eq (beq_iff_eq.mp hoo)
          exact Or.inr ⟨e, List.Mem.head _, hAct, by bv_omega⟩
        · rw [hBase]
          exact Or.inl rfl

private theorem blockProgram_cliGhostExterns_externAt?_mem_cases
    {lib : Obj.MultiPlacedLib} {mpl : Obj.MultiPlacement} {idx : Nat}
    (ghFixed : CliGhostHooks) (baseExt : String → Option (State → State))
    {pc : BitVec 64} {f : State → State}
    (h : (lib.blockProgram mpl idx (cliGhostExterns ghFixed baseExt)).externAt? pc = some f) :
    (lib.blockProgram mpl idx baseExt).externAt? pc = some f ∨
      ∃ sym : String, sym ∈ (lib.blockLib idx).text.externs ∧
        GhostSymActive ghFixed sym f ∧ pc = lib.resolve mpl sym := by
  unfold Obj.MultiPlacedLib.blockProgram Obj.PlacedLib.program Program.externAt? Program.hookAtOff? at h ⊢
  dsimp only at h ⊢
  rw [findSome?_const_none, Option.or_none] at h ⊢
  exact findSome?_stubs_cliGhostExterns_mem_cases
    (lib.blockLib idx).text.externs (lib.blockPlacement mpl idx).ρ
    (lib.blockPlacement mpl idx).base pc ghFixed baseExt h

private theorem stepsAll_cfi_transfer_pGhost617_aux [LibsignalPlacement]
    (mpl mmpl : MultiPlacement) (W : CliHooks) (i : Inputs) (s0 : State)
    (hReal0 : F3CodeOk mpl mmpl s0.mem)
    (hpc0 : s0.pc = mpl.base 617)
    (hfs0 : s0.fs = initFsState (cliProcessInputs i))
    (htr0 : s0.trace = [])
    (hRealNone : ∀ (sym : String) (f : State → State),
      sym ∈ (libsignalSessionLib.blockLib 617).text.externs →
      GhostSymActive (hole2_ghFixed mpl mmpl) sym f →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl sym) = none)
    (hGhostReplay : ∀ (sym : String) (f : State → State),
      sym ∈ (libsignalSessionLib.blockLib 617).text.externs →
      sym ≠ lsStringCloneSym →
      GhostSymActive (hole2_ghFixed mpl mmpl) sym f →
      ∀ u : State,
        u.pc = libsignalSessionLib.resolve mpl sym →
        u.status = .Running →
        (∀ msg, (f u).status ≠ .Exception msg) →
        u.mem.KeepsFrozen (f u).mem →
        ExecFrozen u.mem →
        hole2_keepSub (u.readReg64 .lr) = false →
        F3CodeInv mpl mmpl u.mem →
        FdsGe3Closed u.fs →
        Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u (f u) ∧
        FdsGe3Closed (f u).fs)
    (hMallocngFds : ∀ (sf u : State) (f : State → State),
      let P_ghost := cliProgExtPlacedAt mpl
        (fun W' => cliGhostExterns (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W')) 617 W
      Steps P_ghost s0 u →
      Steps P_ghost (f u) sf →
      (∀ msg, sf.status ≠ .Exception msg) →
      sf.status ≠ .Halted →
      u.status = .Running →
      (f = CryptoVerification.E2E.aesEncHookMallocng mmpl W.C.E ∨
       f = CryptoVerification.E2E.aesDecHookMallocng mmpl W.C.D ∨
       f = CryptoVerification.E2E.libcruxHmacHookMallocng mmpl W.C.F) →
      ExecFrozen u.mem →
      F3CodeInv mpl mmpl u.mem →
      FdsGe3Closed u.fs →
      FdsGe3Closed (f u).fs)
    (hSvcFds : ∀ (sf z : State),
      let P_ghost := cliProgExtPlacedAt mpl
        (fun W' => cliGhostExterns (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W')) 617 W
      Steps P_ghost s0 z →
      Steps P_ghost (Syscall.standard z) sf →
      (∀ msg, sf.status ≠ .Exception msg) →
      sf.status ≠ .Halted →
      z.status = .Running →
      P_ghost.externAt? z.pc = none →
      P_ghost.fetchMem z.mem z.pc = some (.system false 0#16) →
      ExecFrozen z.mem →
      F3CodeInv mpl mmpl z.mem →
      FdsGe3Closed z.fs →
      FdsGe3Closed (Syscall.standard z).fs)
    {u sf : State}
    (hAll : h2ef_StepsAll (h2ef_HookEntryCfi hole2_keepSub)
      (cliProgExtPlacedAt mpl
        (fun W' => cliGhostExterns (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W')) 617 W)
      u sf)
    (hpre : Steps
      (cliProgExtPlacedAt mpl
        (fun W' => cliGhostExterns (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W')) 617 W)
      s0 u)
    (hnoex : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt : sf.status ≠ .Halted)
    (hfr_u : ExecFrozen u.mem)
    (hinv_u : F3CodeInv mpl mmpl u.mem)
    (hfs_u : FdsGe3Closed u.fs) :
    Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u sf ∧
      ExecFrozen sf.mem ∧ F3CodeInv mpl mmpl sf.mem ∧ FdsGe3Closed sf.fs := by
  let P_ghost := cliProgExtPlacedAt mpl
    (fun W' => cliGhostExterns (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W')) 617 W
  let P_real := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W
  have _ := hReal0; have _ := hpc0; have _ := hfs0; have _ := htr0; have _ := hRealNone
  induction hAll with
  | refl s => exact ⟨Steps.refl s, hfr_u, hinv_u, hfs_u⟩
  | @step a b c hcfi h1 hrest ih =>
    have hrest_steps : Steps P_ghost b c := h2ef_stepsAll_toSteps hrest
    cases h1 with
    | halt_unmapped _ _ _ =>
      exact False.elim (hnhalt (steps_preserves_halted hrest_steps rfl))
    | extern_fault _ _ _ =>
      exact False.elim (hnoex _ (steps_preserves_exception hrest_steps rfl))
    | @exec inst hrun hfm =>
      have hfm_orig := hfm
      unfold Program.fetchMem at hfm
      cases heg :
          (cliProgExtPlacedAt mpl
            (fun W' => cliGhostExterns (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W'))
            617 W).externAt? a.pc with
      | some _ => simp [heg] at hfm
      | none =>
        have her : P_real.externAt? a.pc = none :=
          blockProgram_cliGhostExterns_no_new_hooks libsignalSessionLib mpl 617
            (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W) a.pc heg
        have hfm_real : P_real.fetchMem a.mem a.pc = some inst := by
          unfold Program.fetchMem
          simpa [heg, her] using hfm
        by_cases hsvc0 : inst.isSvc0 = true
        · have hinst : inst = .system false 0#16 := by
            cases inst <;> simp [Instr.isSvc0] at hsvc0
            rcases hsvc0 with ⟨rfl, rfl⟩; rfl
          subst hinst
          have hsvc_g : (cliProgExtPlacedAt mpl
              (fun W' => cliGhostExterns (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W'))
              617 W).svc = Syscall.standard := rfl
          have hsvc_r : P_real.svc = Syscall.standard := rfl
          have hev_g : (cliProgExtPlacedAt mpl
              (fun W' => cliGhostExterns (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W'))
              617 W).evalInst (.system false 0#16) a = Syscall.standard a := by
            simp [Program.evalInst, execInstWithSvc, hsvc_g]
          have hev_r : P_real.evalInst (.system false 0#16) a = Syscall.standard a := by
            simp [Program.evalInst, execInstWithSvc, hsvc_r]
          have hstep1_g : Step P_ghost a (Syscall.standard a) := hev_g ▸ Step.exec hrun hfm_orig
          have hstep1_r : Step P_real a (Syscall.standard a) := hev_r ▸ Step.exec hrun hfm_real
          obtain ⟨_, hfr_b⟩ := standard_stripS (keep := fun _ => false) hfr_u
          rw [hev_g] at hrest hrest_steps ih
          have hinv_b : F3CodeInv mpl mmpl (Syscall.standard a).mem :=
            hinv_u.of_keepsFrozen hstep1_r.keepsFrozen
          have hfs_b : FdsGe3Closed (Syscall.standard a).fs :=
            hSvcFds c a hpre hrest_steps hnoex hnhalt hrun heg hfm_orig hfr_u hinv_u hfs_u
          have hpre_b : Steps P_ghost s0 (Syscall.standard a) :=
            hpre.trans (Steps.step hstep1_g (Steps.refl _))
          obtain ⟨hrest_r, hfr_c, hinv_c, hfs_c⟩ :=
            ih hpre_b hnoex hnhalt hfr_b hinv_b hfs_b
          exact ⟨Steps.step hstep1_r hrest_r, hfr_c, hinv_c, hfs_c⟩
        · have hnsvc0 : inst.isSvc0 = false := Bool.eq_false_iff.mpr hsvc0
          have hev_g : (cliProgExtPlacedAt mpl
              (fun W' => cliGhostExterns (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W'))
              617 W).evalInst inst a = execInst inst a :=
            evalInst_eq_execInst_of_not_isSvc0 _ hnsvc0 a
          have hev_r : P_real.evalInst inst a = execInst inst a :=
            evalInst_eq_execInst_of_not_isSvc0 P_real hnsvc0 a
          have hstep1_g : Step P_ghost a (execInst inst a) := hev_g ▸ Step.exec hrun hfm_orig
          have hstep1_r : Step P_real a (execInst inst a) := hev_r ▸ Step.exec hrun hfm_real
          obtain ⟨hfr_b, hfs_eq⟩ := execInst_preserves_execFrozen_and_fs hnsvc0 hfr_u
          rw [hev_g] at hrest hrest_steps ih
          have hinv_b : F3CodeInv mpl mmpl (execInst inst a).mem :=
            hinv_u.of_keepsFrozen hstep1_r.keepsFrozen
          have hpre_b : Steps P_ghost s0 (execInst inst a) :=
            hpre.trans (Steps.step hstep1_g (Steps.refl _))
          obtain ⟨hrest_r, hfr_c, hinv_c, hfs_c⟩ :=
            ih hpre_b hnoex hnhalt hfr_b hinv_b (hfs_eq ▸ hfs_u)
          exact ⟨Steps.step hstep1_r hrest_r, hfr_c, hinv_c, hfs_c⟩
    | @extern f hrun heg hkf hsym =>
      have hstep1_g : Step P_ghost a (f a) := Step.extern hrun heg hkf hsym
      have hnoex_fa : ∀ msg, (f a).status ≠ .Exception msg := fun msg hex =>
        hnoex msg (steps_preserves_exception hrest_steps hex)
      have hpre_b : Steps P_ghost s0 (f a) :=
        hpre.trans (Steps.step hstep1_g (Steps.refl _))
      have hinv_b : F3CodeInv mpl mmpl (f a).mem := hinv_u.of_keepsFrozen hkf
      rcases blockProgram_cliGhostExterns_externAt?_mem_cases
          (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W) heg with
        her | ⟨sym, hsym_ext, hAct, hpc_eq⟩
      · obtain ⟨sym, hsym_real⟩ := blockProgram_externAt?_some_exists her
        have hstep1_r : Step P_real a (f a) := Step.extern hrun her hkf hsym
        have hfr_b : ExecFrozen (f a).mem :=
          cliExternsPlaced_preserves_execFrozen mmpl W hsym_real a hfr_u
        have hfs_b : FdsGe3Closed (f a).fs := by
          rcases cliExternsPlaced_nonMallocng_preserves_fdsGe3Closed mmpl W hsym_real with
            hpres | hmal
          · exact hpres a hfs_u
          · exact hMallocngFds c a f hpre hrest_steps hnoex hnhalt hrun hmal hfr_u hinv_u hfs_u
        obtain ⟨hrest_r, hfr_c, hinv_c, hfs_c⟩ :=
          ih hpre_b hnoex hnhalt hfr_b hinv_b hfs_b
        exact ⟨Steps.step hstep1_r hrest_r, hfr_c, hinv_c, hfs_c⟩
      · have hne_sc : sym ≠ lsStringCloneSym := fun heq =>
          h2ef_strClone_not_mem_ext617 (heq ▸ hsym_ext)
        have hlr_sub : hole2_keepSub (a.readReg64 .lr) = false :=
          (hcfi (by rw [heg]; nofun)).1
        have hfr_b : ExecFrozen (f a).mem :=
          h2ef_hole2_ghFixed_preserves_execFrozen mpl mmpl hAct a hfr_u
        obtain ⟨hst_r, hfs_b⟩ :=
          hGhostReplay sym f hsym_ext hne_sc hAct a hpc_eq hrun hnoex_fa hkf hfr_u
            hlr_sub hinv_u hfs_u
        obtain ⟨hrest_r, hfr_c, hinv_c, hfs_c⟩ :=
          ih hpre_b hnoex hnhalt hfr_b hinv_b hfs_b
        exact ⟨hst_r.trans hrest_r, hfr_c, hinv_c, hfs_c⟩

/-- Trajectory transfer over `h2ef_StepsAll (h2ef_HookEntryLr hole2_keepSub)` at Block `617`,
upgrading `ExecFrozen` post-hoc and eliminating `lsStringCloneSym` via
`h2ef_strClone_not_mem_ext617`. -/
theorem h2ef_stepsAll_transfer_pGhost617_keepSub [LibsignalPlacement]
    (mpl mmpl : MultiPlacement) (W : CliHooks) (i : Inputs) {s0 sf : State}
    (hReal0 : F3CodeOk mpl mmpl s0.mem)
    (hpc0 : s0.pc = mpl.base 617)
    (hfs0 : s0.fs = initFsState (cliProcessInputs i))
    (htr0 : s0.trace = [])
    (hRealNone : ∀ (sym : String) (f : State → State),
      sym ∈ (libsignalSessionLib.blockLib 617).text.externs →
      GhostSymActive (hole2_ghFixed mpl mmpl) sym f →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl sym) = none)
    (hGhostReplay : ∀ (sym : String) (f : State → State),
      sym ∈ (libsignalSessionLib.blockLib 617).text.externs →
      sym ≠ lsStringCloneSym →
      GhostSymActive (hole2_ghFixed mpl mmpl) sym f →
      ∀ u : State,
        u.pc = libsignalSessionLib.resolve mpl sym →
        u.status = .Running →
        (∀ msg, (f u).status ≠ .Exception msg) →
        u.mem.KeepsFrozen (f u).mem →
        ExecFrozen u.mem →
        hole2_keepSub (u.readReg64 .lr) = false →
        F3CodeInv mpl mmpl u.mem →
        FdsGe3Closed u.fs →
        Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u (f u) ∧
        FdsGe3Closed (f u).fs)
    (hMallocngFds : ∀ (sf' u : State) (f : State → State),
      let P_ghost := cliProgExtPlacedAt mpl
        (fun W' => cliGhostExterns (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W')) 617 W
      Steps P_ghost s0 u →
      Steps P_ghost (f u) sf' →
      (∀ msg, sf'.status ≠ .Exception msg) →
      sf'.status ≠ .Halted →
      u.status = .Running →
      (f = CryptoVerification.E2E.aesEncHookMallocng mmpl W.C.E ∨
       f = CryptoVerification.E2E.aesDecHookMallocng mmpl W.C.D ∨
       f = CryptoVerification.E2E.libcruxHmacHookMallocng mmpl W.C.F) →
      ExecFrozen u.mem →
      F3CodeInv mpl mmpl u.mem →
      FdsGe3Closed u.fs →
      FdsGe3Closed (f u).fs)
    (hSvcFds : ∀ (sf' z : State),
      let P_ghost := cliProgExtPlacedAt mpl
        (fun W' => cliGhostExterns (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W')) 617 W
      Steps P_ghost s0 z →
      Steps P_ghost (Syscall.standard z) sf' →
      (∀ msg, sf'.status ≠ .Exception msg) →
      sf'.status ≠ .Halted →
      z.status = .Running →
      P_ghost.externAt? z.pc = none →
      P_ghost.fetchMem z.mem z.pc = some (.system false 0#16) →
      ExecFrozen z.mem →
      F3CodeInv mpl mmpl z.mem →
      FdsGe3Closed z.fs →
      FdsGe3Closed (Syscall.standard z).fs)
    (hAllLr : h2ef_StepsAll (h2ef_HookEntryLr hole2_keepSub)
      (cliProgExtPlacedAt mpl
        (fun W' => cliGhostExterns (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W')) 617 W)
      s0 sf)
    (hnoex : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt : sf.status ≠ .Halted) :
    Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) s0 sf ∧
      ExecFrozen sf.mem ∧ F3CodeInv mpl mmpl sf.mem ∧ FdsGe3Closed sf.fs := by
  obtain ⟨hAllCfi, _⟩ := h2ef_pGhost_upgrade_execFrozen mpl mmpl 617 W hReal0 hAllLr hnoex hnhalt
  exact stepsAll_cfi_transfer_pGhost617_aux mpl mmpl W i s0 hReal0 hpc0 hfs0 htr0
    hRealNone hGhostReplay hMallocngFds hSvcFds hAllCfi (Steps.refl s0) hnoex hnhalt
    hReal0.2 hReal0.1 (hfs0 ▸ fdsGe3Closed_initFsState (cliProcessInputs i))

private theorem subroutineOutcome_not_halted {α : Type} {spec : Spec α}
    {x : α} {R : SepProp} {s0 sf : State}
    (h : SubroutineOutcome spec x R s0 sf) : sf.status ≠ .Halted := by
  rcases h with ⟨⟨_, _, hr⟩, _, _⟩ | ⟨hp, _⟩ | ⟨_, he, _⟩ | ⟨ho, _⟩
  · rw [hr]; nofun
  · rw [hp]; nofun
  · rw [he]; nofun
  · rw [ho]; nofun

private theorem subroutineOutcome_not_exception {α : Type} {spec : Spec α}
    {x : α} {R : SepProp} {s0 sf : State}
    (hout : SubroutineOutcome spec x R s0 sf) :
    ∀ msg, sf.status ≠ .Exception msg := by
  intro msg hex
  rcases hout with ⟨⟨_, _, hr⟩, _, _⟩ | ⟨hp, _⟩ | ⟨_, he, _⟩ | ⟨ho, _⟩
  · rw [hex] at hr; cases hr
  · rw [hex] at hp; cases hp
  · rw [hex] at he; cases he
  · rw [hex] at ho; cases ho

/-- Reduces `Block617TransferFixedHyp` at `hole2_keepSub` to `CodeLoaded`, `P_real.externAt? = none`
on active Block-`617` ghost symbols, per-hook replay for the six `hole2_keepSub` hooks + `shim`,
`FdsGe3Closed` preservation across `mallocng` and `svc #0`, and a trajectory `h2ef_HookEntryLr`
witness. -/
theorem h2ef_block617TransferFixed_of_traj_keepSub [LibsignalPlacement]
    (mpl mmpl : MultiPlacement)
    {libcAddr brkStart : BitVec 64} {stk : Nat}
    (hF3Frozen : ∀ m : Memory, F3CodeOk mpl mmpl m → LibsignalFrozen mpl m)
    (hGhostCL : ∀ (W : CliHooks) (m : Memory), LibsignalFrozen mpl m →
      (cliProgExtPlacedAt mpl
        (fun W' => cliGhostExterns (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W'))
        617 W).CodeLoaded m)
    (hRealNone : ∀ (W : CliHooks) (sym : String) (f : State → State),
      sym ∈ (libsignalSessionLib.blockLib 617).text.externs →
      GhostSymActive (hole2_ghFixed mpl mmpl) sym f →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl sym) = none)
    (hGhostReplay : ∀ (W : CliHooks) (sym : String) (f : State → State),
      sym ∈ (libsignalSessionLib.blockLib 617).text.externs →
      sym ≠ lsStringCloneSym →
      GhostSymActive (hole2_ghFixed mpl mmpl) sym f →
      ∀ u : State,
        u.pc = libsignalSessionLib.resolve mpl sym →
        u.status = .Running →
        (∀ msg, (f u).status ≠ .Exception msg) →
        u.mem.KeepsFrozen (f u).mem →
        ExecFrozen u.mem →
        hole2_keepSub (u.readReg64 .lr) = false →
        F3CodeInv mpl mmpl u.mem →
        FdsGe3Closed u.fs →
        Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u (f u) ∧
        FdsGe3Closed (f u).fs)
    (hMallocngFds : ∀ (W : CliHooks) (i : Inputs) (s0 sf u : State) (f : State → State),
      let P_ghost := cliProgExtPlacedAt mpl
        (fun W' => cliGhostExterns (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W')) 617 W
      F3CodeOk mpl mmpl s0.mem →
      s0.pc = mpl.base 617 →
      s0.fs = initFsState (cliProcessInputs i) →
      s0.trace = [] →
      Steps P_ghost s0 u →
      Steps P_ghost (f u) sf →
      (∀ msg, sf.status ≠ .Exception msg) →
      sf.status ≠ .Halted →
      u.status = .Running →
      (f = CryptoVerification.E2E.aesEncHookMallocng mmpl W.C.E ∨
       f = CryptoVerification.E2E.aesDecHookMallocng mmpl W.C.D ∨
       f = CryptoVerification.E2E.libcruxHmacHookMallocng mmpl W.C.F) →
      ExecFrozen u.mem →
      F3CodeInv mpl mmpl u.mem →
      FdsGe3Closed u.fs →
      FdsGe3Closed (f u).fs)
    (hSvcFds : ∀ (W : CliHooks) (i : Inputs) (s0 sf z : State),
      let P_ghost := cliProgExtPlacedAt mpl
        (fun W' => cliGhostExterns (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W')) 617 W
      F3CodeOk mpl mmpl s0.mem →
      s0.pc = mpl.base 617 →
      s0.fs = initFsState (cliProcessInputs i) →
      s0.trace = [] →
      Steps P_ghost s0 z →
      Steps P_ghost (Syscall.standard z) sf →
      (∀ msg, sf.status ≠ .Exception msg) →
      sf.status ≠ .Halted →
      z.status = .Running →
      P_ghost.externAt? z.pc = none →
      P_ghost.fetchMem z.mem z.pc = some (.system false 0#16) →
      ExecFrozen z.mem →
      F3CodeInv mpl mmpl z.mem →
      FdsGe3Closed z.fs →
      FdsGe3Closed (Syscall.standard z).fs)
    (hTrajLr : ∀ (W : CliHooks) (Run : Inputs → RunAnswer → Prop) (γ : GhostName) (tp : BitVec 64),
      let P_ghost := cliProgExtPlacedAt mpl
        (fun W' => cliGhostExterns (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W')) 617 W
      let spec_ghost := b2MainSpecTightNeedLocksFineAt libcAddr (LibsignalFrozen mpl)
        (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        cliBudgetLimits fineCostModel.init stk (cliStaticsPlacedAt mpl) Run cliProcessInputs
      subroutine_ok P_ghost (mpl.base 617) spec_ghost →
      ∀ g R (s0 : State),
        F3CodeOk mpl mmpl s0.mem →
        s0.pc = mpl.base 617 →
        s0.status = .Running →
        s0.spAligned = true →
        (s0.mem ⊨ spec_ghost.pre g s0 ∗ R) →
        P_ghost.CodeLoaded s0.mem →
        ∃ sf : State,
          h2ef_StepsAll (h2ef_HookEntryLr hole2_keepSub) P_ghost s0 sf ∧
          SubroutineOutcome spec_ghost g R s0 sf) :
    Block617TransferFixedHyp mpl mmpl (hole2_ghFixed mpl mmpl)
      (LibsignalFrozen mpl) (F3CodeOk mpl mmpl) libcAddr brkStart stk := by
  intro W Run hGhostOk γ tp
  apply subroutine_ok_of_steps_outcome
  intro g R s0 hpc hrun hm hsp _
  have hm_unfold := hm
  dsimp only [b2MainSpecTightNeedLocksFineAt] at hm_unfold
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm_unfold
  obtain ⟨⟨hReal0, hCase, hInpOk, hEntry, hStk⟩, hm_frame⟩ := hm_unfold
  have hGhost0 : LibsignalFrozen mpl s0.mem := hF3Frozen s0.mem hReal0
  have hm_ghost : s0.mem ⊨ (b2MainSpecTightNeedLocksFineAt libcAddr (LibsignalFrozen mpl)
      (fineHookRustCliAllocBudget γ mmpl tp brkStart)
      cliBudgetLimits fineCostModel.init stk (cliStaticsPlacedAt mpl) Run cliProcessInputs).pre g s0 ∗ R := by
    dsimp only [b2MainSpecTightNeedLocksFineAt]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hGhost0, hCase, hInpOk, hEntry, hStk⟩, hm_frame⟩
  have hCL : (cliProgExtPlacedAt mpl
      (fun W' => cliGhostExterns (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W'))
      617 W).CodeLoaded s0.mem := hGhostCL W s0.mem hGhost0
  obtain ⟨sf, hAllLr, hout⟩ :=
    hTrajLr W Run γ tp (hGhostOk γ tp) g R s0 hReal0 hpc hrun hsp hm_ghost hCL
  have hnoex : ∀ msg, sf.status ≠ .Exception msg := subroutineOutcome_not_exception hout
  have hnhalt : sf.status ≠ .Halted := subroutineOutcome_not_halted hout
  obtain ⟨hsteps_real, _, _, _⟩ :=
    h2ef_stepsAll_transfer_pGhost617_keepSub mpl mmpl W g.i hReal0 hpc hEntry.2.1 hEntry.2.2
      (hRealNone W) (hGhostReplay W)
      (fun sf' u f => hMallocngFds W g.i s0 sf' u f hReal0 hpc hEntry.2.1 hEntry.2.2)
      (fun sf' z => hSvcFds W g.i s0 sf' z hReal0 hpc hEntry.2.1 hEntry.2.2)
      hAllLr hnoex hnhalt
  exact ⟨sf, hsteps_real, hout⟩

/-- Step-upgrade reduction for `Block617TransferFixedHyp` at `hole2_keepSub` from a
`Steps → h2ef_StepsAll (h2ef_HookEntryLr hole2_keepSub)` companion. -/
theorem h2ef_block617TransferFixed_of_steps_to_stepsAll_keepSub [LibsignalPlacement]
    (mpl mmpl : MultiPlacement)
    {libcAddr brkStart : BitVec 64} {stk : Nat}
    (hF3Frozen : ∀ m : Memory, F3CodeOk mpl mmpl m → LibsignalFrozen mpl m)
    (hRealNone : ∀ (W : CliHooks) (sym : String) (f : State → State),
      sym ∈ (libsignalSessionLib.blockLib 617).text.externs →
      GhostSymActive (hole2_ghFixed mpl mmpl) sym f →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl sym) = none)
    (hGhostReplay : ∀ (W : CliHooks) (sym : String) (f : State → State),
      sym ∈ (libsignalSessionLib.blockLib 617).text.externs →
      sym ≠ lsStringCloneSym →
      GhostSymActive (hole2_ghFixed mpl mmpl) sym f →
      ∀ u : State,
        u.pc = libsignalSessionLib.resolve mpl sym →
        u.status = .Running →
        (∀ msg, (f u).status ≠ .Exception msg) →
        u.mem.KeepsFrozen (f u).mem →
        ExecFrozen u.mem →
        hole2_keepSub (u.readReg64 .lr) = false →
        F3CodeInv mpl mmpl u.mem →
        FdsGe3Closed u.fs →
        Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u (f u) ∧
        FdsGe3Closed (f u).fs)
    (hMallocngFds : ∀ (W : CliHooks) (i : Inputs) (s0 sf u : State) (f : State → State),
      let P_ghost := cliProgExtPlacedAt mpl
        (fun W' => cliGhostExterns (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W')) 617 W
      F3CodeOk mpl mmpl s0.mem →
      s0.pc = mpl.base 617 →
      s0.fs = initFsState (cliProcessInputs i) →
      s0.trace = [] →
      Steps P_ghost s0 u →
      Steps P_ghost (f u) sf →
      (∀ msg, sf.status ≠ .Exception msg) →
      sf.status ≠ .Halted →
      u.status = .Running →
      (f = CryptoVerification.E2E.aesEncHookMallocng mmpl W.C.E ∨
       f = CryptoVerification.E2E.aesDecHookMallocng mmpl W.C.D ∨
       f = CryptoVerification.E2E.libcruxHmacHookMallocng mmpl W.C.F) →
      ExecFrozen u.mem →
      F3CodeInv mpl mmpl u.mem →
      FdsGe3Closed u.fs →
      FdsGe3Closed (f u).fs)
    (hSvcFds : ∀ (W : CliHooks) (i : Inputs) (s0 sf z : State),
      let P_ghost := cliProgExtPlacedAt mpl
        (fun W' => cliGhostExterns (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W')) 617 W
      F3CodeOk mpl mmpl s0.mem →
      s0.pc = mpl.base 617 →
      s0.fs = initFsState (cliProcessInputs i) →
      s0.trace = [] →
      Steps P_ghost s0 z →
      Steps P_ghost (Syscall.standard z) sf →
      (∀ msg, sf.status ≠ .Exception msg) →
      sf.status ≠ .Halted →
      z.status = .Running →
      P_ghost.externAt? z.pc = none →
      P_ghost.fetchMem z.mem z.pc = some (.system false 0#16) →
      ExecFrozen z.mem →
      F3CodeInv mpl mmpl z.mem →
      FdsGe3Closed z.fs →
      FdsGe3Closed (Syscall.standard z).fs)
    (hUpgradeLr : ∀ (W : CliHooks) (i : Inputs) (s0 sf : State),
      let P_ghost := cliProgExtPlacedAt mpl
        (fun W' => cliGhostExterns (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W')) 617 W
      F3CodeOk mpl mmpl s0.mem →
      s0.pc = mpl.base 617 →
      s0.fs = initFsState (cliProcessInputs i) →
      s0.trace = [] →
      s0.status = .Running →
      s0.spAligned = true →
      Steps P_ghost s0 sf →
      (∀ msg, sf.status ≠ .Exception msg) →
      sf.status ≠ .Halted →
      h2ef_StepsAll (h2ef_HookEntryLr hole2_keepSub) P_ghost s0 sf) :
    Block617TransferFixedHyp mpl mmpl (hole2_ghFixed mpl mmpl)
      (LibsignalFrozen mpl) (F3CodeOk mpl mmpl) libcAddr brkStart stk := by
  refine h2ef_block617TransferFixed_of_traj_keepSub mpl mmpl hF3Frozen
    (h2ef_pGhost617_codeLoaded_of_libsignalFrozen mpl mmpl)
    hRealNone hGhostReplay hMallocngFds hSvcFds ?_
  intro W Run γ tp
  dsimp only
  intro hGhostOk g R s0 hReal0 hpc hrun hsp hm_ghost hCL
  have hm_u : s0.mem ⊨ (b2MainSpecTightNeedLocksFineAt libcAddr (LibsignalFrozen mpl)
      (fineHookRustCliAllocBudget γ mmpl tp brkStart)
      cliBudgetLimits fineCostModel.init stk (cliStaticsPlacedAt mpl) Run cliProcessInputs).pre g s0 ∗ R :=
    hm_ghost
  dsimp only [b2MainSpecTightNeedLocksFineAt] at hm_u
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm_u
  obtain ⟨⟨_, _, _, hEntry, _⟩, _⟩ := hm_u
  obtain ⟨sf, hsteps, hout⟩ :=
    subroutine_ok_elim_steps_outcome hGhostOk g R s0 hpc hrun hm_ghost hsp hCL
  exact ⟨sf, hUpgradeLr W g.i s0 sf hReal0 hpc hEntry.2.1 hEntry.2.2 hrun hsp hsteps
    (subroutineOutcome_not_exception hout) (subroutineOutcome_not_halted hout), hout⟩

/-- Uniform-`hole2_keep` specialization of `h2ef_block617TransferFixed_of_steps_to_stepsAll_keepSub`. -/
theorem h2ef_block617TransferFixed_of_steps_to_stepsAll_keep [LibsignalPlacement]
    (mpl mmpl : MultiPlacement)
    {libcAddr brkStart : BitVec 64} {stk : Nat}
    (hF3Frozen : ∀ m : Memory, F3CodeOk mpl mmpl m → LibsignalFrozen mpl m)
    (hRealNone : ∀ (W : CliHooks) (sym : String) (f : State → State),
      sym ∈ (libsignalSessionLib.blockLib 617).text.externs →
      GhostSymActive (hole2_ghFixed mpl mmpl) sym f →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl sym) = none)
    (hGhostReplay : ∀ (W : CliHooks) (sym : String) (f : State → State),
      sym ∈ (libsignalSessionLib.blockLib 617).text.externs →
      sym ≠ lsStringCloneSym →
      GhostSymActive (hole2_ghFixed mpl mmpl) sym f →
      ∀ u : State,
        u.pc = libsignalSessionLib.resolve mpl sym →
        u.status = .Running →
        (∀ msg, (f u).status ≠ .Exception msg) →
        u.mem.KeepsFrozen (f u).mem →
        ExecFrozen u.mem →
        hole2_keepSub (u.readReg64 .lr) = false →
        F3CodeInv mpl mmpl u.mem →
        FdsGe3Closed u.fs →
        Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u (f u) ∧
        FdsGe3Closed (f u).fs)
    (hMallocngFds : ∀ (W : CliHooks) (i : Inputs) (s0 sf u : State) (f : State → State),
      let P_ghost := cliProgExtPlacedAt mpl
        (fun W' => cliGhostExterns (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W')) 617 W
      F3CodeOk mpl mmpl s0.mem →
      s0.pc = mpl.base 617 →
      s0.fs = initFsState (cliProcessInputs i) →
      s0.trace = [] →
      Steps P_ghost s0 u →
      Steps P_ghost (f u) sf →
      (∀ msg, sf.status ≠ .Exception msg) →
      sf.status ≠ .Halted →
      u.status = .Running →
      (f = CryptoVerification.E2E.aesEncHookMallocng mmpl W.C.E ∨
       f = CryptoVerification.E2E.aesDecHookMallocng mmpl W.C.D ∨
       f = CryptoVerification.E2E.libcruxHmacHookMallocng mmpl W.C.F) →
      ExecFrozen u.mem →
      F3CodeInv mpl mmpl u.mem →
      FdsGe3Closed u.fs →
      FdsGe3Closed (f u).fs)
    (hSvcFds : ∀ (W : CliHooks) (i : Inputs) (s0 sf z : State),
      let P_ghost := cliProgExtPlacedAt mpl
        (fun W' => cliGhostExterns (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W')) 617 W
      F3CodeOk mpl mmpl s0.mem →
      s0.pc = mpl.base 617 →
      s0.fs = initFsState (cliProcessInputs i) →
      s0.trace = [] →
      Steps P_ghost s0 z →
      Steps P_ghost (Syscall.standard z) sf →
      (∀ msg, sf.status ≠ .Exception msg) →
      sf.status ≠ .Halted →
      z.status = .Running →
      P_ghost.externAt? z.pc = none →
      P_ghost.fetchMem z.mem z.pc = some (.system false 0#16) →
      ExecFrozen z.mem →
      F3CodeInv mpl mmpl z.mem →
      FdsGe3Closed z.fs →
      FdsGe3Closed (Syscall.standard z).fs)
    (hUpgradeLr : ∀ (W : CliHooks) (i : Inputs) (s0 sf : State),
      let P_ghost := cliProgExtPlacedAt mpl
        (fun W' => cliGhostExterns (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W')) 617 W
      F3CodeOk mpl mmpl s0.mem →
      s0.pc = mpl.base 617 →
      s0.fs = initFsState (cliProcessInputs i) →
      s0.trace = [] →
      s0.status = .Running →
      s0.spAligned = true →
      Steps P_ghost s0 sf →
      (∀ msg, sf.status ≠ .Exception msg) →
      sf.status ≠ .Halted →
      h2ef_StepsAll (h2ef_HookEntryLr hole2_keep) P_ghost s0 sf) :
    Block617TransferFixedHyp mpl mmpl (hole2_ghFixed mpl mmpl)
      (LibsignalFrozen mpl) (F3CodeOk mpl mmpl) libcAddr brkStart stk :=
  h2ef_block617TransferFixed_of_steps_to_stepsAll_keepSub mpl mmpl hF3Frozen
    hRealNone hGhostReplay hMallocngFds hSvcFds
    (fun W i s0 sf hR hpc hfs htr hrun hsp hst hnoex hnhalt =>
      h2ef_stepsAll_mono
        (fun _ hq hne => h2ef_keepSub_false_of_keep_false (hq hne))
        (hUpgradeLr W i s0 sf hR hpc hfs htr hrun hsp hst hnoex hnhalt))

private theorem steps_to_stepsAll_of_lrCalls
    {keep : BitVec 64 → Bool} {P_ghost P_real : Program} {s0 u sf : State}
    (hno_new : ∀ pc, P_ghost.externAt? pc = none → P_real.externAt? pc = none)
    (hOnlyGhost : ∀ pc f, P_ghost.externAt? pc = some f →
      P_real.externAt? pc = some f ∨ P_real.externAt? pc = none)
    (hsteps : Steps P_ghost u sf)
    (hpre : Steps P_ghost s0 u)
    (hnoex : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt : sf.status ≠ .Halted)
    (hLrCalls : ∀ z : State, Steps P_ghost s0 z → Steps P_ghost z sf →
      z.status = .Running → P_ghost.externAt? z.pc ≠ P_real.externAt? z.pc →
      keep (z.readReg64 .lr) = false)
    (hRealLr : ∀ pc f z, P_real.externAt? pc = some f → P_ghost.externAt? pc = some f →
      Steps P_ghost s0 z → Steps P_ghost z sf → z.pc = pc → z.status = .Running →
      keep (z.readReg64 .lr) = false) :
    h2ef_StepsAll (h2ef_HookEntryLr keep) P_ghost u sf := by
  have _ := hno_new
  induction hsteps with
  | refl s => exact h2ef_StepsAll.refl s
  | @step a b c h1 hrest ih =>
    have hstep_ac : Steps P_ghost a c := Steps.step h1 hrest
    have hrun_a : a.status = .Running := by cases h1 <;> assumption
    have hq_a : h2ef_HookEntryLr keep P_ghost a := by
      intro hne
      cases heg : P_ghost.externAt? a.pc with
      | none => exact False.elim (hne heg)
      | some f =>
        rcases hOnlyGhost a.pc f heg with her | her_none
        · exact hRealLr a.pc f a her heg hpre hstep_ac rfl hrun_a
        · exact hLrCalls a hpre hstep_ac hrun_a (by rw [heg, her_none]; nofun)
    have hpre_b : Steps P_ghost s0 b := hpre.trans (Steps.step h1 (Steps.refl b))
    exact h2ef_StepsAll.step hq_a h1 (ih hpre_b hnoex hnhalt hLrCalls hRealLr)

/-- State-indexed `Steps s0 u → Steps u sf` reduction for `Block617TransferFixedHyp` at
`hole2_keepSub`. -/
theorem h2ef_block617TransferFixed_of_lrCalls_keepSub [LibsignalPlacement]
    (mpl mmpl : MultiPlacement)
    {libcAddr brkStart : BitVec 64} {stk : Nat}
    (hPl : libsignalSessionLib.Placeable mpl)
    (hF3Frozen : ∀ m : Memory, F3CodeOk mpl mmpl m → LibsignalFrozen mpl m)
    (hRealNone : ∀ (W : CliHooks) (sym : String) (f : State → State),
      sym ∈ (libsignalSessionLib.blockLib 617).text.externs →
      GhostSymActive (hole2_ghFixed mpl mmpl) sym f →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl sym) = none)
    (hGhostReplay : ∀ (W : CliHooks) (sym : String) (f : State → State),
      sym ∈ (libsignalSessionLib.blockLib 617).text.externs →
      sym ≠ lsStringCloneSym →
      GhostSymActive (hole2_ghFixed mpl mmpl) sym f →
      ∀ u : State,
        u.pc = libsignalSessionLib.resolve mpl sym →
        u.status = .Running →
        (∀ msg, (f u).status ≠ .Exception msg) →
        u.mem.KeepsFrozen (f u).mem →
        ExecFrozen u.mem →
        hole2_keepSub (u.readReg64 .lr) = false →
        F3CodeInv mpl mmpl u.mem →
        FdsGe3Closed u.fs →
        Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u (f u) ∧
        FdsGe3Closed (f u).fs)
    (hMallocngFds : ∀ (W : CliHooks) (i : Inputs) (s0 sf u : State) (f : State → State),
      let P_ghost := cliProgExtPlacedAt mpl
        (fun W' => cliGhostExterns (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W')) 617 W
      F3CodeOk mpl mmpl s0.mem →
      s0.pc = mpl.base 617 →
      s0.fs = initFsState (cliProcessInputs i) →
      s0.trace = [] →
      Steps P_ghost s0 u →
      Steps P_ghost (f u) sf →
      (∀ msg, sf.status ≠ .Exception msg) →
      sf.status ≠ .Halted →
      u.status = .Running →
      (f = CryptoVerification.E2E.aesEncHookMallocng mmpl W.C.E ∨
       f = CryptoVerification.E2E.aesDecHookMallocng mmpl W.C.D ∨
       f = CryptoVerification.E2E.libcruxHmacHookMallocng mmpl W.C.F) →
      ExecFrozen u.mem →
      F3CodeInv mpl mmpl u.mem →
      FdsGe3Closed u.fs →
      FdsGe3Closed (f u).fs)
    (hSvcFds : ∀ (W : CliHooks) (i : Inputs) (s0 sf z : State),
      let P_ghost := cliProgExtPlacedAt mpl
        (fun W' => cliGhostExterns (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W')) 617 W
      F3CodeOk mpl mmpl s0.mem →
      s0.pc = mpl.base 617 →
      s0.fs = initFsState (cliProcessInputs i) →
      s0.trace = [] →
      Steps P_ghost s0 z →
      Steps P_ghost (Syscall.standard z) sf →
      (∀ msg, sf.status ≠ .Exception msg) →
      sf.status ≠ .Halted →
      z.status = .Running →
      P_ghost.externAt? z.pc = none →
      P_ghost.fetchMem z.mem z.pc = some (.system false 0#16) →
      ExecFrozen z.mem →
      F3CodeInv mpl mmpl z.mem →
      FdsGe3Closed z.fs →
      FdsGe3Closed (Syscall.standard z).fs)
    (hLrCalls : ∀ (W : CliHooks) (i : Inputs) (s0 sf u : State),
      let P_ghost := cliProgExtPlacedAt mpl
        (fun W' => cliGhostExterns (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W')) 617 W
      let P_real := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W
      F3CodeOk mpl mmpl s0.mem →
      s0.pc = mpl.base 617 →
      s0.fs = initFsState (cliProcessInputs i) →
      s0.trace = [] →
      Steps P_ghost s0 u →
      Steps P_ghost u sf →
      (∀ msg, sf.status ≠ .Exception msg) →
      sf.status ≠ .Halted →
      u.status = .Running →
      ExecFrozen u.mem →
      P_ghost.externAt? u.pc ≠ P_real.externAt? u.pc →
      hole2_keepSub (u.readReg64 .lr) = false) :
    Block617TransferFixedHyp mpl mmpl (hole2_ghFixed mpl mmpl)
      (LibsignalFrozen mpl) (F3CodeOk mpl mmpl) libcAddr brkStart stk := by
  have _ := hPl
  refine LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer.block617TransferFixed_of_replaysOn
    hole2_keepSub (F3CodeInv mpl mmpl) FdsGe3Closed
    hF3Frozen (h2ef_pGhost617_codeLoaded_of_libsignalFrozen mpl mmpl)
    (fun _ h => h.2) (fun _ h => h.1) (fun _ _ h hkf => h.of_keepsFrozen hkf)
    (fun i => fdsGe3Closed_initFsState (cliProcessInputs i)) ?_
  intro W i s0 sf
  dsimp only
  intro hReal0 hpc0 hfs0 htr0 hsteps hnoex hnhalt
  refine ⟨?_, ?_, ?_⟩
  · intro pc f heg
    rcases blockProgram_cliGhostExterns_externAt?_mem_cases
        (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W) heg with
      her | ⟨sym, hsym_ext, hAct, hpc_eq⟩
    · obtain ⟨sym, hsym⟩ := blockProgram_externAt?_some_exists her
      refine Or.inl ⟨her, fun u hpre hpost _ hrun _ hkf hfr ⟨hinv, hfs⟩ => ?_⟩
      refine ⟨cliExternsPlaced_preserves_execFrozen mmpl W hsym u hfr,
        hinv.of_keepsFrozen hkf, ?_⟩
      rcases cliExternsPlaced_nonMallocng_preserves_fdsGe3Closed mmpl W hsym with hpres | hmal
      · exact hpres u hfs
      · exact hMallocngFds W i s0 sf u f hReal0 hpc0 hfs0 htr0 hpre hpost hnoex hnhalt hrun hmal hfr hinv hfs
    · refine Or.inr ⟨hpc_eq ▸ hRealNone W sym f hsym_ext hAct,
        fun u _ _ hpc hrun hnoex_fu hkf hfr hlr ⟨hinv, hfs⟩ => ?_⟩
      have hne_sc : sym ≠ lsStringCloneSym := fun heq =>
        h2ef_strClone_not_mem_ext617 (heq ▸ hsym_ext)
      obtain ⟨hst_r, hfs'⟩ :=
        hGhostReplay W sym f hsym_ext hne_sc hAct u (hpc.trans hpc_eq) hrun hnoex_fu hkf hfr hlr hinv hfs
      exact ⟨hst_r, h2ef_hole2_ghFixed_preserves_execFrozen mpl mmpl hAct u hfr,
        hinv.of_keepsFrozen hkf, hfs'⟩
  · intro z hpre hrest hrun heg hfm hfr hinv hfs
    exact hSvcFds W i s0 sf z hReal0 hpc0 hfs0 htr0 hpre hrest hnoex hnhalt hrun heg hfm hfr hinv hfs
  · intro z hpre hrest hrun hne
    have hfr_z : ExecFrozen z.mem :=
      h2ef_pGhost617_steps_execFrozen_of_f3CodeOk mpl mmpl W hReal0 hpre
    exact hLrCalls W i s0 sf z hReal0 hpc0 hfs0 htr0 hpre hrest hnoex hnhalt hrun hfr_z hne

/-! ## Code-Only `InvS` Wiring at `h2k_ghFixedK` -/

/-- Per-call `lr` + `readFile`-`FdsGe3Closed` predicate on intermediate states. -/
def h2ef_HookEntryLrReadFds (keep : BitVec 64 → Bool) (readPc : BitVec 64)
    (P : Program) (s : State) : Prop :=
  (P.externAt? s.pc ≠ none → keep (s.readReg64 .lr) = false) ∧
  (P.externAt? s.pc ≠ none → s.pc = readPc → FdsGe3Closed s.fs)

/-- General `baseExt` bridge: any `(sym, f)` active in `gh` (`GhostSymActive gh sym f`) resolves to
    `some f` in `cliGhostExterns gh baseExt`. -/
theorem h2ef_cliGhostExterns_of_ghostSymActive_base
    (gh : CliGhostHooks) (baseExt : String → Option (State → State))
    {sym : String} {f : State → State}
    (hAct : GhostSymActive gh sym f) :
    cliGhostExterns gh baseExt sym = some f := by
  rcases hAct with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, hsc⟩ | ⟨rfl, _, hrf⟩ | ⟨rfl, _, hrs⟩ | ⟨rfl, hms⟩ | ⟨rfl, hmc⟩
  · have h1 : (lsRustAllocSymCli == lsRustAllocSymCli) = true := by decide
    unfold cliGhostExterns; simp only [h1, ↓reduceIte]
  · have h1 : (lsRustDeallocSymCli == lsRustAllocSymCli) = false := by decide
    have h2 : (lsRustDeallocSymCli == lsRustDeallocSymCli) = true := by decide
    unfold cliGhostExterns; simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]
  · have h1 : (lsRustReallocSymCli == lsRustAllocSymCli) = false := by decide
    have h2 : (lsRustReallocSymCli == lsRustDeallocSymCli) = false := by decide
    have h3 : (lsRustReallocSymCli == lsRustReallocSymCli) = true := by decide
    unfold cliGhostExterns; simp only [h1, h2, h3, Bool.false_eq_true, ↓reduceIte]
  · have h1 : (lsRustAllocZeroedSymCli == lsRustAllocSymCli) = false := by decide
    have h2 : (lsRustAllocZeroedSymCli == lsRustDeallocSymCli) = false := by decide
    have h3 : (lsRustAllocZeroedSymCli == lsRustReallocSymCli) = false := by decide
    have h4 : (lsRustAllocZeroedSymCli == lsRustAllocZeroedSymCli) = true := by decide
    unfold cliGhostExterns; simp only [h1, h2, h3, h4, Bool.false_eq_true, ↓reduceIte]
  · have h1 : (lsRustNoAllocShimSymCli == lsRustAllocSymCli) = false := by decide
    have h2 : (lsRustNoAllocShimSymCli == lsRustDeallocSymCli) = false := by decide
    have h3 : (lsRustNoAllocShimSymCli == lsRustReallocSymCli) = false := by decide
    have h4 : (lsRustNoAllocShimSymCli == lsRustAllocZeroedSymCli) = false := by decide
    have h5 : (lsRustNoAllocShimSymCli == lsRustNoAllocShimSymCli) = true := by decide
    unfold cliGhostExterns; simp only [h1, h2, h3, h4, h5, Bool.false_eq_true, ↓reduceIte]
  · have h1 : (lsStringCloneSym == lsRustAllocSymCli) = false := by decide
    have h2 : (lsStringCloneSym == lsRustDeallocSymCli) = false := by decide
    have h3 : (lsStringCloneSym == lsRustReallocSymCli) = false := by decide
    have h4 : (lsStringCloneSym == lsRustAllocZeroedSymCli) = false := by decide
    have h5 : (lsStringCloneSym == lsRustNoAllocShimSymCli) = false := by decide
    have h6 : (lsStringCloneSym == lsStringCloneSym) = true := by decide
    unfold cliGhostExterns
    simp only [h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ↓reduceIte, hsc]
  · have h1 : (lsReadFileSym == lsRustAllocSymCli) = false := by decide
    have h2 : (lsReadFileSym == lsRustDeallocSymCli) = false := by decide
    have h3 : (lsReadFileSym == lsRustReallocSymCli) = false := by decide
    have h4 : (lsReadFileSym == lsRustAllocZeroedSymCli) = false := by decide
    have h5 : (lsReadFileSym == lsRustNoAllocShimSymCli) = false := by decide
    have h6 : (lsReadFileSym == lsStringCloneSym) = false := by decide
    have h7 : (lsReadFileSym == lsReadFileSym) = true := by decide
    unfold cliGhostExterns
    simp only [h1, h2, h3, h4, h5, h6, h7, Bool.false_eq_true, ↓reduceIte, hrf]
  · have h1 : (lsReadStdinSym == lsRustAllocSymCli) = false := by decide
    have h2 : (lsReadStdinSym == lsRustDeallocSymCli) = false := by decide
    have h3 : (lsReadStdinSym == lsRustReallocSymCli) = false := by decide
    have h4 : (lsReadStdinSym == lsRustAllocZeroedSymCli) = false := by decide
    have h5 : (lsReadStdinSym == lsRustNoAllocShimSymCli) = false := by decide
    have h6 : (lsReadStdinSym == lsStringCloneSym) = false := by decide
    have h7 : (lsReadStdinSym == lsReadFileSym) = false := by decide
    have h8 : (lsReadStdinSym == lsReadStdinSym) = true := by decide
    unfold cliGhostExterns
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, Bool.false_eq_true, ↓reduceIte, hrs]
  · exact CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns_memset_some gh baseExt hms
  · exact CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns_memcpy_some gh baseExt hmc

/-- Active ghost symbols resolve to `some f` in `cliGhostExterns gh (fun _ => none)`. -/
theorem h2ef_cliGhostExterns_of_ghostSymActive
    (gh : CliGhostHooks) {sym : String} {f : State → State}
    (hAct : GhostSymActive gh sym f) :
    cliGhostExterns gh (fun _ => none) sym = some f :=
  h2ef_cliGhostExterns_of_ghostSymActive_base gh (fun _ => none) hAct

/-- Unconditional `ExecFrozen` preservation for all 8 active ghost hooks of `h2k_ghFixedK`. -/
theorem h2ef_h2k_ghFixedK_preserves_execFrozen [LibsignalPlacement]
    (mpl mmpl : MultiPlacement) {sym : String} {f : State → State}
    (hAct : GhostSymActive (h2k_ghFixedK mpl mmpl) sym f) :
    ∀ u : State, ExecFrozen u.mem → ExecFrozen (f u).mem := by
  intro u hfr
  rcases hAct with
    ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ |
    ⟨_, hsc⟩ | ⟨_, _, hrf⟩ | ⟨_, _, hrs⟩ | ⟨_, hms⟩ | ⟨_, hmc⟩
  · dsimp only [h2k_ghFixedK, h2k_allocGhostHookFineK]
    exact execFrozen_f3LinkedCallHook _ _ _ _ _ _ (execFrozen_f3AllocFallback mmpl false) u hfr
  · dsimp only [h2k_ghFixedK, h2k_deallocGhostHookFineK]
    exact execFrozen_f3LinkedCallHook _ _ _ _ _ _ (execFrozen_f3DeallocFallback mmpl) u hfr
  · dsimp only [h2k_ghFixedK, h2k_reallocGhostHookFineK]
    exact execFrozen_f3LinkedCallHook _ _ _ _ _ _ (execFrozen_f3ReallocFallback mmpl) u hfr
  · dsimp only [h2k_ghFixedK, h2k_allocZeroedGhostHookFineK]
    exact execFrozen_f3LinkedCallHook _ _ _ _ _ _ (execFrozen_f3AllocFallback mmpl true) u hfr
  · exact hfr
  · dsimp only [h2k_ghFixedK] at hsc
    injection hsc with hfeq; subst hfeq
    classical
    unfold h2k_strCloneGhostHookK
    split
    · split
      · rename_i hReal
        exact (Classical.choose_spec hReal.2.2.2.2).2.2.2.2
      · exact execFrozen_keepFsTrace (execFrozen_f3StringCloneFallback mmpl u hfr)
    · exact hfr
  · dsimp only [h2k_ghFixedK] at hrf
    injection hrf with hsubeq
    have hfeq := (congrArg Subtype.val hsubeq).symm
    subst hfeq
    classical
    dsimp only [h2k_readFileFixedGhostHookFineSubK]
    unfold h2k_readFileFixedGhostHookFineK
    split
    · split
      · rename_i hReal
        exact (Classical.choose_spec hReal.2.2.2.2).2.2.2.2
      · exact execFrozen_keepFsTrace (execFrozen_f3ReadFileFallback mmpl u hfr)
    · exact hfr
  · dsimp only [h2k_ghFixedK] at hrs
    injection hrs with hsubeq
    have hfeq := (congrArg Subtype.val hsubeq).symm
    subst hfeq
    classical
    dsimp only [h2k_readStdinGhostHookFineSubK]
    unfold h2k_readStdinGhostHookFineK
    split
    · split
      · rename_i hReal
        exact (Classical.choose_spec hReal.2.2.2).2.2.2.2.2
      · exact execFrozen_keepFilesTrace (execFrozen_f3ReadStdinFallback mmpl u hfr)
    · exact hfr
  · dsimp only [h2k_ghFixedK] at hms
    injection hms with hfeq; subst hfeq
    exact f3EmptyMemsetGhostHookNarrow_execFrozen mmpl u hfr
  · dsimp only [h2k_ghFixedK] at hmc
    injection hmc with hfeq; subst hfeq
    exact f3EmptyMemcpyGhostHookNarrow_execFrozen mmpl u hfr

/-- Block-`617` `P_ghost.CodeLoaded` at `h2k_ghFixedK` from `LibsignalFrozen mpl m`. -/
theorem h2ef_pGhost617K_codeLoaded_of_libsignalFrozen [LibsignalPlacement]
    (mpl mmpl : MultiPlacement) (W : CliHooks) (m : Memory)
    (hFrz : LibsignalFrozen mpl m) :
    (cliProgExtPlacedAt mpl
      (fun W' => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W'))
      617 W).CodeLoaded m := by
  have h617 : 617 < libsignalSessionLib.blocks.length := by
    have hlen := Nat.beq_eq.mp
      LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData.libsignalBlocks_len
    have hge : 618 ≤
        LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData.f3LsBlocksLen := by decide
    omega
  have hc := hFrz.2 617 h617
  exact Arm64.Program.CodeLoaded.intro hc.aligned hc.no_wrap fun i hi =>
    ⟨hc.byte_eq i hi, hc.perm_eq i hi, hc.isLazyFree_eq i hi⟩

private theorem steps_codeOnly_transfer_pGhost617KG_aux [LibsignalPlacement]
    (mpl mmpl : MultiPlacement) (W : CliHooks)
    (hGhostReplay : ∀ (sym : String) (f : State → State),
      sym ∈ (libsignalSessionLib.blockLib 617).text.externs →
      sym ≠ lsStringCloneSym →
      GhostSymActive (h2k_ghFixedK mpl mmpl) sym f →
      ∀ u : State,
        u.pc = libsignalSessionLib.resolve mpl sym →
        u.status = .Running →
        (∀ msg, (f u).status ≠ .Exception msg) →
        u.mem.KeepsFrozen (f u).mem →
        ExecFrozen u.mem →
        (sym ≠ lsRustNoAllocShimSymCli → sym ≠ lsMemsetSym → sym ≠ lsMemcpySym →
          hole2_keepSub (u.readReg64 .lr) = false) →
        (sym = lsMemsetSym → keepMemsetBlk21 mmpl (u.readReg64 .lr) = false) →
        (sym = lsMemcpySym → keepMemcpyBlk20 mmpl (u.readReg64 .lr) = false) →
        F3CodeInv mpl mmpl u.mem →
        (sym = lsReadFileSym → FdsGe3Closed u.fs) →
        Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u (f u))
    (hNoExLr : ∀ {sym : String} {f : State → State} {a : State},
      cliGhostExterns (h2k_ghFixedK mpl mmpl) (fun _ => none) sym = some f →
      sym ≠ lsRustNoAllocShimSymCli →
      (∀ msg, (f a).status ≠ .Exception msg) →
      sym ≠ lsMemsetSym →
      sym ≠ lsMemcpySym →
      hole2_keepSub (a.readReg64 .lr) = false)
    (hNoExFds : ∀ {baseExt : String → Option (State → State)} {f : State → State} {a : State},
      cliGhostExterns (h2k_ghFixedK mpl mmpl) baseExt lsReadFileSym = some f →
      (∀ msg, (f a).status ≠ .Exception msg) →
      FdsGe3Closed a.fs)
    (hTrap21 : ∀ {sym : String} {f : State → State},
      cliGhostExterns (h2k_ghFixedK mpl mmpl) (fun _ => none) sym = some f →
      sym ≠ lsRustNoAllocShimSymCli →
      ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f)
    (hTrap20 : ∀ {sym : String} {f : State → State},
      cliGhostExterns (h2k_ghFixedK mpl mmpl) (fun _ => none) sym = some f →
      sym ≠ lsRustNoAllocShimSymCli →
      ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f)
    (hBlk21Ext : ∀ pc, keepMemsetBlk21 mmpl pc = true →
      (cliProgExtPlacedAt mpl
        (fun W' => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W'))
        617 W).externAt? pc = none ∨
        ∃ f, (cliProgExtPlacedAt mpl
          (fun W' => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W'))
          617 W).externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f)
    (hBlk20Ext : ∀ pc, keepMemcpyBlk20 mmpl pc = true →
      (cliProgExtPlacedAt mpl
        (fun W' => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W'))
        617 W).externAt? pc = none ∨
        ∃ f, (cliProgExtPlacedAt mpl
          (fun W' => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W'))
          617 W).externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f)
    {u sf : State}
    (hsteps : Steps
      (cliProgExtPlacedAt mpl
        (fun W' => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W')) 617 W)
      u sf)
    (hrun_sf21 : sf.status = .Running → keepMemsetBlk21 mmpl sf.pc = false)
    (hrun_sf20 : sf.status = .Running → keepMemcpyBlk20 mmpl sf.pc = false)
    (hnoex : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt : sf.status ≠ .Halted)
    (hfr_u : ExecFrozen u.mem)
    (hinv_u : F3CodeInv mpl mmpl u.mem) :
    Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u sf ∧
      ExecFrozen sf.mem ∧ F3CodeInv mpl mmpl sf.mem := by
  let P_real := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W
  have hmng20 : (20 : Nat) < mallocngLib.blocks.length := by decide
  have hmng21 : (21 : Nat) < mallocngLib.blocks.length := by decide
  induction hsteps with
  | refl s => exact ⟨Steps.refl s, hfr_u, hinv_u⟩
  | @step a b c h1 hrest ih =>
    cases h1 with
    | halt_unmapped _ _ _ =>
      exact False.elim (hnhalt (steps_preserves_halted hrest rfl))
    | extern_fault _ _ _ =>
      exact False.elim (hnoex _ (steps_preserves_exception hrest rfl))
    | @exec inst hrun hfm =>
      unfold Program.fetchMem at hfm
      cases heg :
          (cliProgExtPlacedAt mpl
            (fun W' => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W'))
            617 W).externAt? a.pc with
      | some _ => simp [heg] at hfm
      | none =>
        have her : P_real.externAt? a.pc = none :=
          blockProgram_cliGhostExterns_no_new_hooks libsignalSessionLib mpl 617
            (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W) a.pc heg
        have hfm_real : P_real.fetchMem a.mem a.pc = some inst := by
          unfold Program.fetchMem
          simpa [heg, her] using hfm
        by_cases hsvc0 : inst.isSvc0 = true
        · have hinst : inst = .system false 0#16 := by
            cases inst <;> simp [Instr.isSvc0] at hsvc0
            rcases hsvc0 with ⟨rfl, rfl⟩; rfl
          subst hinst
          have hsvc_g : (cliProgExtPlacedAt mpl
              (fun W' => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W'))
              617 W).svc = Syscall.standard := rfl
          have hsvc_r : P_real.svc = Syscall.standard := rfl
          have hev_g : (cliProgExtPlacedAt mpl
              (fun W' => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W'))
              617 W).evalInst (.system false 0#16) a = Syscall.standard a := by
            simp [Program.evalInst, execInstWithSvc, hsvc_g]
          have hev_r : P_real.evalInst (.system false 0#16) a = Syscall.standard a := by
            simp [Program.evalInst, execInstWithSvc, hsvc_r]
          have hstep1_r : Step P_real a (Syscall.standard a) := hev_r ▸ Step.exec hrun hfm_real
          obtain ⟨_, hfr_b⟩ := standard_stripS (keep := fun _ => false) hfr_u
          rw [hev_g] at hrest ih
          have hinv_b : F3CodeInv mpl mmpl (Syscall.standard a).mem :=
            hinv_u.of_keepsFrozen hstep1_r.keepsFrozen
          obtain ⟨hrest_r, hfr_c, hinv_c⟩ := ih hrun_sf21 hrun_sf20 hnoex hnhalt hfr_b hinv_b
          exact ⟨Steps.step hstep1_r hrest_r, hfr_c, hinv_c⟩
        · have hnsvc0 : inst.isSvc0 = false := Bool.eq_false_iff.mpr hsvc0
          have hev_g : (cliProgExtPlacedAt mpl
              (fun W' => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W'))
              617 W).evalInst inst a = execInst inst a :=
            evalInst_eq_execInst_of_not_isSvc0 _ hnsvc0 a
          have hev_r : P_real.evalInst inst a = execInst inst a :=
            evalInst_eq_execInst_of_not_isSvc0 P_real hnsvc0 a
          have hstep1_r : Step P_real a (execInst inst a) := hev_r ▸ Step.exec hrun hfm_real
          obtain ⟨hfr_b, _⟩ := execInst_preserves_execFrozen_and_fs hnsvc0 hfr_u
          rw [hev_g] at hrest ih
          have hinv_b : F3CodeInv mpl mmpl (execInst inst a).mem :=
            hinv_u.of_keepsFrozen hstep1_r.keepsFrozen
          obtain ⟨hrest_r, hfr_c, hinv_c⟩ := ih hrun_sf21 hrun_sf20 hnoex hnhalt hfr_b hinv_b
          exact ⟨Steps.step hstep1_r hrest_r, hfr_c, hinv_c⟩
    | @extern f hrun heg hkf hsym =>
      have hnoex_fa : ∀ msg, (f a).status ≠ .Exception msg := fun msg hex =>
        hnoex msg (steps_preserves_exception hrest hex)
      have hinv_b : F3CodeInv mpl mmpl (f a).mem := hinv_u.of_keepsFrozen hkf
      rcases blockProgram_cliGhostExterns_externAt?_mem_cases
          (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W) heg with
        her | ⟨sym, hsym_ext, hAct, hpc_eq⟩
      · obtain ⟨sym, hsym_real⟩ := blockProgram_externAt?_some_exists her
        have hstep1_r : Step P_real a (f a) := Step.extern hrun her hkf hsym
        have hfr_b : ExecFrozen (f a).mem :=
          cliExternsPlaced_preserves_execFrozen mmpl W hsym_real a hfr_u
        obtain ⟨hrest_r, hfr_c, hinv_c⟩ := ih hrun_sf21 hrun_sf20 hnoex hnhalt hfr_b hinv_b
        exact ⟨Steps.step hstep1_r hrest_r, hfr_c, hinv_c⟩
      · have hne_sc : sym ≠ lsStringCloneSym := fun heq =>
          h2ef_strClone_not_mem_ext617 (heq ▸ hsym_ext)
        have hext0 : cliGhostExterns (h2k_ghFixedK mpl mmpl) (fun _ => none) sym = some f :=
          h2ef_cliGhostExterns_of_ghostSymActive (h2k_ghFixedK mpl mmpl) hAct
        have hlr_sub : sym ≠ lsRustNoAllocShimSymCli → sym ≠ lsMemsetSym → sym ≠ lsMemcpySym →
            hole2_keepSub (a.readReg64 .lr) = false :=
          fun hnoShim hnoMs hnoMc => hNoExLr hext0 hnoShim hnoex_fa hnoMs hnoMc
        have hlr_blk21 : sym = lsMemsetSym → keepMemsetBlk21 mmpl (a.readReg64 .lr) = false :=
          fun hms => blk21_lr_trap_after_hook_ret
            (hTrap21 hext0 (by subst hms; decide)) hBlk21Ext
            (hinv_b.mngBlockCodeLoaded 21 hmng21 _ _ Syscall.standard)
            hrest hrun hrun_sf21 hnoex hnhalt
        have hlr_blk20 : sym = lsMemcpySym → keepMemcpyBlk20 mmpl (a.readReg64 .lr) = false :=
          fun hmc => blk20_lr_trap_after_hook_ret
            (hTrap20 hext0 (by subst hmc; decide)) hBlk20Ext
            (hinv_b.mngBlockCodeLoaded 20 hmng20 _ _ Syscall.standard)
            hrest hrun hrun_sf20 hnoex hnhalt
        have hread_fds : sym = lsReadFileSym → FdsGe3Closed a.fs :=
          fun hrd => hNoExFds (hrd ▸ hext0) hnoex_fa
        have hfr_b : ExecFrozen (f a).mem :=
          h2ef_h2k_ghFixedK_preserves_execFrozen mpl mmpl hAct a hfr_u
        have hst_r : Steps P_real a (f a) :=
          hGhostReplay sym f hsym_ext hne_sc hAct a hpc_eq hrun hnoex_fa hkf hfr_u
            hlr_sub hlr_blk21 hlr_blk20 hinv_u hread_fds
        obtain ⟨hrest_r, hfr_c, hinv_c⟩ := ih hrun_sf21 hrun_sf20 hnoex hnhalt hfr_b hinv_b
        exact ⟨hst_r.trans hrest_r, hfr_c, hinv_c⟩

/-- Code-only trajectory `Block617TransferFixedHypG` reduction at `h2k_ghFixedK` (`C3e-8G`), deriving
`hlr_sub` (`sym ∉ {shim, ms, mc}`), `FdsGe3Closed`, and `hlr_blk{21,20}` via `blk{21,20}_lr_trap_after_hook_ret` and `F3MemsetMemcpyEntryLrFalse`. -/
theorem h2ef_block617TransferFixedG_of_traj_codeOnly [LibsignalPlacement]
    (mpl mmpl : MultiPlacement)
    {libcAddr brkStart : BitVec 64} {stk : Nat}
    (hF3Frozen : ∀ m : Memory, F3CodeOk mpl mmpl m → LibsignalFrozen mpl m)
    (hGhostCL : ∀ (W : CliHooks) (m : Memory), LibsignalFrozen mpl m →
      (cliProgExtPlacedAt mpl
        (fun W' => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W'))
        617 W).CodeLoaded m)
    (hRealNone : ∀ (W : CliHooks) (sym : String) (f : State → State),
      sym ∈ (libsignalSessionLib.blockLib 617).text.externs →
      GhostSymActive (h2k_ghFixedK mpl mmpl) sym f →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl sym) = none)
    (hGhostReplay : ∀ (W : CliHooks) (sym : String) (f : State → State),
      sym ∈ (libsignalSessionLib.blockLib 617).text.externs →
      sym ≠ lsStringCloneSym →
      GhostSymActive (h2k_ghFixedK mpl mmpl) sym f →
      ∀ u : State,
        u.pc = libsignalSessionLib.resolve mpl sym →
        u.status = .Running →
        (∀ msg, (f u).status ≠ .Exception msg) →
        u.mem.KeepsFrozen (f u).mem →
        ExecFrozen u.mem →
        (sym ≠ lsRustNoAllocShimSymCli → sym ≠ lsMemsetSym → sym ≠ lsMemcpySym →
          hole2_keepSub (u.readReg64 .lr) = false) →
        (sym = lsMemsetSym → keepMemsetBlk21 mmpl (u.readReg64 .lr) = false) →
        (sym = lsMemcpySym → keepMemcpyBlk20 mmpl (u.readReg64 .lr) = false) →
        F3CodeInv mpl mmpl u.mem →
        (sym = lsReadFileSym → FdsGe3Closed u.fs) →
        Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u (f u))
    (hNoExLr : ∀ {sym : String} {f : State → State} {a : State},
      cliGhostExterns (h2k_ghFixedK mpl mmpl) (fun _ => none) sym = some f →
      sym ≠ lsRustNoAllocShimSymCli →
      (∀ msg, (f a).status ≠ .Exception msg) →
      sym ≠ lsMemsetSym →
      sym ≠ lsMemcpySym →
      hole2_keepSub (a.readReg64 .lr) = false)
    (hNoExFds : ∀ {baseExt : String → Option (State → State)} {f : State → State} {a : State},
      cliGhostExterns (h2k_ghFixedK mpl mmpl) baseExt lsReadFileSym = some f →
      (∀ msg, (f a).status ≠ .Exception msg) →
      FdsGe3Closed a.fs)
    (hTrap21 : ∀ {sym : String} {f : State → State},
      cliGhostExterns (h2k_ghFixedK mpl mmpl) (fun _ => none) sym = some f →
      sym ≠ lsRustNoAllocShimSymCli →
      ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f)
    (hTrap20 : ∀ {sym : String} {f : State → State},
      cliGhostExterns (h2k_ghFixedK mpl mmpl) (fun _ => none) sym = some f →
      sym ≠ lsRustNoAllocShimSymCli →
      ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f)
    (hBlk21Ext : ∀ (W : CliHooks) (pc : BitVec 64), keepMemsetBlk21 mmpl pc = true →
      (cliProgExtPlacedAt mpl
        (fun W' => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W'))
        617 W).externAt? pc = none ∨
        ∃ f, (cliProgExtPlacedAt mpl
          (fun W' => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W'))
          617 W).externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f)
    (hBlk20Ext : ∀ (W : CliHooks) (pc : BitVec 64), keepMemcpyBlk20 mmpl pc = true →
      (cliProgExtPlacedAt mpl
        (fun W' => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W'))
        617 W).externAt? pc = none ∨
        ∃ f, (cliProgExtPlacedAt mpl
          (fun W' => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W'))
          617 W).externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f) :
    Block617TransferFixedHypG mpl mmpl
      (fun W => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W))
      (cliExternsPlaced mmpl)
      (F3MemsetMemcpyEntryLrFalse mmpl)
      (LibsignalFrozen mpl) (F3CodeOk mpl mmpl) libcAddr brkStart stk := by
  have _ := hRealNone
  intro W Run hGhostOk γ tp
  apply subroutine_ok_of_steps_outcome
  intro g R s0 hpc hrun hm hsp _
  have hm_unfold := hm
  dsimp only [withEntryGuard, b2MainSpecTightNeedLocksFineAt] at hm_unfold
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm_unfold
  obtain ⟨hGuard0, hm_real⟩ := hm_unfold
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm_real
  obtain ⟨⟨hReal0, hCase, hInpOk, hEntry, hStk⟩, hm_frame⟩ := hm_real
  have hGhost0 : LibsignalFrozen mpl s0.mem := hF3Frozen s0.mem hReal0
  have hm_ghost : s0.mem ⊨ (b2MainSpecTightNeedLocksFineAt libcAddr (LibsignalFrozen mpl)
      (fineHookRustCliAllocBudget γ mmpl tp brkStart)
      cliBudgetLimits fineCostModel.init stk (cliStaticsPlacedAt mpl) Run cliProcessInputs).pre g s0 ∗ R := by
    dsimp only [b2MainSpecTightNeedLocksFineAt]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hGhost0, hCase, hInpOk, hEntry, hStk⟩, hm_frame⟩
  have hCL : (cliProgExtPlacedAt mpl
      (fun W' => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W'))
      617 W).CodeLoaded s0.mem := hGhostCL W s0.mem hGhost0
  obtain ⟨sf, hsteps, hout⟩ :=
    subroutine_ok_elim_steps_outcome (hGhostOk γ tp) g R s0 hpc hrun hm_ghost hsp hCL
  obtain ⟨hret_pc, hnoex, hnhalt⟩ := subroutineOutcome_running_pc_and_noFault hout
  have hrun_sf21 : sf.status = .Running → keepMemsetBlk21 mmpl sf.pc = false :=
    fun hrs => hret_pc hrs ▸ hGuard0.1
  have hrun_sf20 : sf.status = .Running → keepMemcpyBlk20 mmpl sf.pc = false :=
    fun hrs => hret_pc hrs ▸ hGuard0.2
  obtain ⟨hsteps_real, _, _⟩ :=
    steps_codeOnly_transfer_pGhost617KG_aux mpl mmpl W (hGhostReplay W)
      hNoExLr hNoExFds hTrap21 hTrap20 (hBlk21Ext W) (hBlk20Ext W)
      hsteps hrun_sf21 hrun_sf20 hnoex hnhalt hReal0.2 hReal0.1
  exact ⟨sf, hsteps_real, hout⟩

/-- Code-only `Steps → h2ef_StepsAll` `Block617TransferFixedHypG` reduction at `h2k_ghFixedK`. -/
theorem h2ef_block617TransferFixedG_of_steps_to_stepsAll_codeOnly [LibsignalPlacement]
    (mpl mmpl : MultiPlacement)
    {libcAddr brkStart : BitVec 64} {stk : Nat}
    (hF3Frozen : ∀ m : Memory, F3CodeOk mpl mmpl m → LibsignalFrozen mpl m)
    (hRealNone : ∀ (W : CliHooks) (sym : String) (f : State → State),
      sym ∈ (libsignalSessionLib.blockLib 617).text.externs →
      GhostSymActive (h2k_ghFixedK mpl mmpl) sym f →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl sym) = none)
    (hGhostReplay : ∀ (W : CliHooks) (sym : String) (f : State → State),
      sym ∈ (libsignalSessionLib.blockLib 617).text.externs →
      sym ≠ lsStringCloneSym →
      GhostSymActive (h2k_ghFixedK mpl mmpl) sym f →
      ∀ u : State,
        u.pc = libsignalSessionLib.resolve mpl sym →
        u.status = .Running →
        (∀ msg, (f u).status ≠ .Exception msg) →
        u.mem.KeepsFrozen (f u).mem →
        ExecFrozen u.mem →
        (sym ≠ lsRustNoAllocShimSymCli → sym ≠ lsMemsetSym → sym ≠ lsMemcpySym →
          hole2_keepSub (u.readReg64 .lr) = false) →
        (sym = lsMemsetSym → keepMemsetBlk21 mmpl (u.readReg64 .lr) = false) →
        (sym = lsMemcpySym → keepMemcpyBlk20 mmpl (u.readReg64 .lr) = false) →
        F3CodeInv mpl mmpl u.mem →
        (sym = lsReadFileSym → FdsGe3Closed u.fs) →
        Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u (f u))
    (hNoExLr : ∀ {sym : String} {f : State → State} {a : State},
      cliGhostExterns (h2k_ghFixedK mpl mmpl) (fun _ => none) sym = some f →
      sym ≠ lsRustNoAllocShimSymCli →
      (∀ msg, (f a).status ≠ .Exception msg) →
      sym ≠ lsMemsetSym →
      sym ≠ lsMemcpySym →
      hole2_keepSub (a.readReg64 .lr) = false)
    (hNoExFds : ∀ {baseExt : String → Option (State → State)} {f : State → State} {a : State},
      cliGhostExterns (h2k_ghFixedK mpl mmpl) baseExt lsReadFileSym = some f →
      (∀ msg, (f a).status ≠ .Exception msg) →
      FdsGe3Closed a.fs)
    (hTrap21 : ∀ {sym : String} {f : State → State},
      cliGhostExterns (h2k_ghFixedK mpl mmpl) (fun _ => none) sym = some f →
      sym ≠ lsRustNoAllocShimSymCli →
      ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f)
    (hTrap20 : ∀ {sym : String} {f : State → State},
      cliGhostExterns (h2k_ghFixedK mpl mmpl) (fun _ => none) sym = some f →
      sym ≠ lsRustNoAllocShimSymCli →
      ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f)
    (hBlk21Ext : ∀ (W : CliHooks) (pc : BitVec 64), keepMemsetBlk21 mmpl pc = true →
      (cliProgExtPlacedAt mpl
        (fun W' => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W'))
        617 W).externAt? pc = none ∨
        ∃ f, (cliProgExtPlacedAt mpl
          (fun W' => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W'))
          617 W).externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f)
    (hBlk20Ext : ∀ (W : CliHooks) (pc : BitVec 64), keepMemcpyBlk20 mmpl pc = true →
      (cliProgExtPlacedAt mpl
        (fun W' => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W'))
        617 W).externAt? pc = none ∨
        ∃ f, (cliProgExtPlacedAt mpl
          (fun W' => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W'))
          617 W).externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f) :
    Block617TransferFixedHypG mpl mmpl
      (fun W => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W))
      (cliExternsPlaced mmpl)
      (F3MemsetMemcpyEntryLrFalse mmpl)
      (LibsignalFrozen mpl) (F3CodeOk mpl mmpl) libcAddr brkStart stk :=
  h2ef_block617TransferFixedG_of_traj_codeOnly mpl mmpl hF3Frozen
    (h2ef_pGhost617K_codeLoaded_of_libsignalFrozen mpl mmpl)
    hRealNone hGhostReplay hNoExLr hNoExFds hTrap21 hTrap20 hBlk21Ext hBlk20Ext

/-- `Block617TransferFixedHypG` reduction at `h2k_ghFixedK` via
`Block617TransferG.block617TransferFixedG_of_replaysOn` with `keep := fun _ => false` and `PredFs := fun _ => True`. -/
theorem h2ef_block617TransferFixedG_replaysOn_false_codeOnly [LibsignalPlacement]
    (mpl mmpl : MultiPlacement)
    {libcAddr brkStart : BitVec 64} {stk : Nat}
    (hF3Frozen : ∀ m : Memory, F3CodeOk mpl mmpl m → LibsignalFrozen mpl m)
    (hRealNone : ∀ (W : CliHooks) (sym : String) (f : State → State),
      sym ∈ (libsignalSessionLib.blockLib 617).text.externs →
      GhostSymActive (h2k_ghFixedK mpl mmpl) sym f →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl sym) = none)
    (hGhostReplay : ∀ (W : CliHooks) (sym : String) (f : State → State),
      sym ∈ (libsignalSessionLib.blockLib 617).text.externs →
      sym ≠ lsStringCloneSym →
      GhostSymActive (h2k_ghFixedK mpl mmpl) sym f →
      ∀ u : State,
        u.pc = libsignalSessionLib.resolve mpl sym →
        u.status = .Running →
        (∀ msg, (f u).status ≠ .Exception msg) →
        u.mem.KeepsFrozen (f u).mem →
        ExecFrozen u.mem →
        (sym ≠ lsRustNoAllocShimSymCli → sym ≠ lsMemsetSym → sym ≠ lsMemcpySym →
          hole2_keepSub (u.readReg64 .lr) = false) →
        (sym = lsMemsetSym → keepMemsetBlk21 mmpl (u.readReg64 .lr) = false) →
        (sym = lsMemcpySym → keepMemcpyBlk20 mmpl (u.readReg64 .lr) = false) →
        F3CodeInv mpl mmpl u.mem →
        (sym = lsReadFileSym → FdsGe3Closed u.fs) →
        Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u (f u))
    (hNoExLr : ∀ {sym : String} {f : State → State} {a : State},
      cliGhostExterns (h2k_ghFixedK mpl mmpl) (fun _ => none) sym = some f →
      sym ≠ lsRustNoAllocShimSymCli →
      (∀ msg, (f a).status ≠ .Exception msg) →
      sym ≠ lsMemsetSym →
      sym ≠ lsMemcpySym →
      hole2_keepSub (a.readReg64 .lr) = false)
    (hNoExFds : ∀ {baseExt : String → Option (State → State)} {f : State → State} {a : State},
      cliGhostExterns (h2k_ghFixedK mpl mmpl) baseExt lsReadFileSym = some f →
      (∀ msg, (f a).status ≠ .Exception msg) →
      FdsGe3Closed a.fs)
    (hTrap21 : ∀ {sym : String} {f : State → State},
      cliGhostExterns (h2k_ghFixedK mpl mmpl) (fun _ => none) sym = some f →
      sym ≠ lsRustNoAllocShimSymCli →
      ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f)
    (hTrap20 : ∀ {sym : String} {f : State → State},
      cliGhostExterns (h2k_ghFixedK mpl mmpl) (fun _ => none) sym = some f →
      sym ≠ lsRustNoAllocShimSymCli →
      ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f)
    (hBlk21Ext : ∀ (W : CliHooks) (pc : BitVec 64), keepMemsetBlk21 mmpl pc = true →
      (cliProgExtPlacedAt mpl
        (fun W' => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W'))
        617 W).externAt? pc = none ∨
        ∃ f, (cliProgExtPlacedAt mpl
          (fun W' => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W'))
          617 W).externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f)
    (hBlk20Ext : ∀ (W : CliHooks) (pc : BitVec 64), keepMemcpyBlk20 mmpl pc = true →
      (cliProgExtPlacedAt mpl
        (fun W' => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W'))
        617 W).externAt? pc = none ∨
        ∃ f, (cliProgExtPlacedAt mpl
          (fun W' => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W'))
          617 W).externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f) :
    Block617TransferFixedHypG mpl mmpl
      (fun W => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W))
      (cliExternsPlaced mmpl)
      (F3MemsetMemcpyEntryLrFalse mmpl)
      (LibsignalFrozen mpl) (F3CodeOk mpl mmpl) libcAddr brkStart stk := by
  have hmng20 : (20 : Nat) < mallocngLib.blocks.length := by decide
  have hmng21 : (21 : Nat) < mallocngLib.blocks.length := by decide
  refine block617TransferFixedG_of_replaysOn
    (fun _ => false) (F3CodeInv mpl mmpl) (fun _ => True)
    (fun W pc heg =>
      blockProgram_cliGhostExterns_no_new_hooks libsignalSessionLib mpl 617
        (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W) pc heg)
    hF3Frozen (h2ef_pGhost617K_codeLoaded_of_libsignalFrozen mpl mmpl)
    (fun _ h => h.2) (fun _ h => h.1) (fun _ _ h hkf => h.of_keepsFrozen hkf)
    (fun _ => trivial) ?_
  intro W _i s0 sf
  dsimp only
  intro hGuard0 _hReal0 _hpc0 _hfs0 _htr0 _hsteps hret_pc hnoex hnhalt
  have hrun_sf21 : sf.status = .Running → keepMemsetBlk21 mmpl sf.pc = false :=
    fun hrs => hret_pc hrs ▸ hGuard0.1
  have hrun_sf20 : sf.status = .Running → keepMemcpyBlk20 mmpl sf.pc = false :=
    fun hrs => hret_pc hrs ▸ hGuard0.2
  refine ⟨?_, fun _ _ _ _ _ _ _ _ _ => trivial, fun _ _ _ _ _ => rfl⟩
  intro pc f heg
  rcases blockProgram_cliGhostExterns_externAt?_mem_cases
      (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W) heg with
    her | ⟨sym, hsym_ext, hAct, hpc_eq⟩
  · obtain ⟨sym, hsym⟩ := blockProgram_externAt?_some_exists her
    refine Or.inl ⟨her, fun u _ _ _ _ _ hkf hfr ⟨hinv, _⟩ => ?_⟩
    exact ⟨cliExternsPlaced_preserves_execFrozen mmpl W hsym u hfr,
      hinv.of_keepsFrozen hkf, trivial⟩
  · refine Or.inr ⟨hpc_eq ▸ hRealNone W sym f hsym_ext hAct,
      fun u _ hrest hpc hrun hnoex_fu hkf hfr _ ⟨hinv, _⟩ => ?_⟩
    have hne_sc : sym ≠ lsStringCloneSym := fun heq =>
      h2ef_strClone_not_mem_ext617 (heq ▸ hsym_ext)
    have hext0 : cliGhostExterns (h2k_ghFixedK mpl mmpl) (fun _ => none) sym = some f :=
      h2ef_cliGhostExterns_of_ghostSymActive (h2k_ghFixedK mpl mmpl) hAct
    have hinv_fu : F3CodeInv mpl mmpl (f u).mem := hinv.of_keepsFrozen hkf
    have hlr_sub : sym ≠ lsRustNoAllocShimSymCli → sym ≠ lsMemsetSym → sym ≠ lsMemcpySym →
        hole2_keepSub (u.readReg64 .lr) = false :=
      fun hnoShim hnoMs hnoMc => hNoExLr hext0 hnoShim hnoex_fu hnoMs hnoMc
    have hlr_blk21 : sym = lsMemsetSym → keepMemsetBlk21 mmpl (u.readReg64 .lr) = false :=
      fun hms => blk21_lr_trap_after_hook_ret
        (hTrap21 hext0 (by subst hms; decide)) (hBlk21Ext W)
        (hinv_fu.mngBlockCodeLoaded 21 hmng21 _ _ Syscall.standard)
        hrest hrun hrun_sf21 hnoex hnhalt
    have hlr_blk20 : sym = lsMemcpySym → keepMemcpyBlk20 mmpl (u.readReg64 .lr) = false :=
      fun hmc => blk20_lr_trap_after_hook_ret
        (hTrap20 hext0 (by subst hmc; decide)) (hBlk20Ext W)
        (hinv_fu.mngBlockCodeLoaded 20 hmng20 _ _ Syscall.standard)
        hrest hrun hrun_sf20 hnoex hnhalt
    have hread_fds : sym = lsReadFileSym → FdsGe3Closed u.fs :=
      fun hrd => hNoExFds (hrd ▸ hext0) hnoex_fu
    have hst_r : Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u (f u) :=
      hGhostReplay W sym f hsym_ext hne_sc hAct u (hpc.trans hpc_eq) hrun hnoex_fu hkf hfr
        hlr_sub hlr_blk21 hlr_blk20 hinv hread_fds
    exact ⟨hst_r, h2ef_h2k_ghFixedK_preserves_execFrozen mpl mmpl hAct u hfr,
      hinv_fu, trivial⟩

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2ExecFrozenWire

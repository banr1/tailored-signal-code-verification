/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
import LibsignalBinary.Proofs.SpecLemmas.SyscallReadWritev

/-!
# Block-`617` Ghost-to-Real Link Transfer and State-Indexed Transfer

State- and trajectory-indexed ghost-to-real `Steps` and `subroutine_ok` transfer
(`GhostExternReplaysOn`, `GhostExternReplaysS`), `cliGhostExterns` active-symbol classification
and `DirectOrBranchStub` reachability (`StubReachesTargetOn`), `ExecFrozen` / `FdsGe3Closed`
preservation across `cliExternsPlaced` and `Syscall.standard`, and the block-`617` transfer seam
`Block617TransferFixedHyp`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.SepLogic
open CryptoGames.CBC (AesKey Block)
open CryptoGames.HMAC (ShaState)
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification.E2E
  (PqxdhPrims aesDecHookMallocng aesEncHookMallocng compress512Hook compressHook dsmbHook edNegHook
   fmtWriteHook0 formatInnerHook0 kemDecapsHook kemEncapsHook libcruxHmacHookMallocng
   mlkemDecapsHook mlkemEncaps1Hook mlkemEncaps2Hook mlkemFromSeedHook mlkemPk1Hook mlkemPk2Hook
   mlkemValidatePkHook restoreCallerRegs scalarModHook scalarWideHook stepRustAlloc1
   stepRustDealloc1 timeAddHook toEdwardsHook torsionFreeHook writeVecHeader)
open CryptoVerification.LibsignalAesCbc (returnToLinkRegister)
open CryptoVerification.LibsignalHmac (compress256Hook)
open CryptoVerification.LibsignalSession (blackBoxHook)
open CryptoVerification.LibsignalTripleRatchet
  (diffieHellmanHook pubFromSecretHook zeroizeSecretHook)
open CryptoVerification.SignalSession
  (CliHooks Inputs cliBcmpHook cliExternsPlaced cliHookTablePlaced cliPqxdhHookTablePlaced
   cliProcessInputs durationSinceExactHook fromUtf8Hook isCliPanicSymbolPlaced libsignalSessionLib
   lsReadFileSym lsReadStdinSym lsRustAllocSymCli lsRustAllocZeroedSymCli lsRustDeallocSymCli
   lsRustNoAllocShimSymCli lsRustReallocSymCli lsStringCloneSym memrchrHook strlenHook unitResult
   unmodelled writeFileHook writeStdoutHook)
open CryptoVerification.SignalSession.Placed (DirectOrBranchStub)
open CryptoVerification.SignalSession.Cli (RunAnswer)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (ExecFrozen StubReachesTarget standard_stripS)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed fdsGe3Closed_initFsState fdsGe3Closed_setFd_lt3 fdsGe3Closed_setFile)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2
  (MainOkCliExtOverB2NeedLocksPlacedAt MainOkCliExtPqB2NeedLocksPlacedAt
   MainOkCliF3OverB2NeedLocksPlacedAt MainOkCliF3PqB2NeedLocksPlacedAt
   b2MainSpecTightNeedLocksFineAt cliBudgetLimits)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
  (cliProgExtPlacedAt cliStaticsPlacedAt)
open VerifiedLibraries (mallocngLib)

/-! ## Generic `(P_ghost, P_real)` State-Indexed Link Transfer -/

private theorem execInst_preserves_execFrozen_and_fs {inst : Instr} (h : inst.isSvc0 = false)
    {s : State} (hfr : ExecFrozen s.mem) :
    ExecFrozen (execInst inst s).mem ∧ (execInst inst s).fs = s.fs := by
  have hpf := ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 h s
  exact ⟨ExecFrozen.of_perm_eq hfr (congrFun hpf.2.1), hpf.2.2.2.2.2.2⟩

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

private theorem subroutineOutcome_not_halted {α : Type} {spec : Spec α} {x : α} {R : SepProp}
    {s0 sf : State} (h : SubroutineOutcome spec x R s0 sf) : sf.status ≠ .Halted := by
  rcases h with ⟨⟨_, _, hr⟩, _, _⟩ | ⟨hp, _⟩ | ⟨_, he, _⟩ | ⟨ho, _⟩
  · rw [hr]; nofun
  · rw [hp]; nofun
  · rw [he]; nofun
  · rw [ho]; nofun

/-- Trajectory- and state-indexed generalization of `AllocGhostLinkTransfer.GhostExternReplays`
    from `Inv : Memory → Prop` to `InvS : State → Prop` (e.g. `InvMem u.mem ∧ FdsGe3Closed u.fs`). -/
def GhostExternReplaysOn (keep : BitVec 64 → Bool) (InvS : State → Prop)
    (P_ghost P_real : Program) (s0 sf : State) : Prop :=
  ∀ (pc : BitVec 64) (f : State → State),
    P_ghost.externAt? pc = some f →
    (P_real.externAt? pc = some f ∧
      (∀ u : State,
        Steps P_ghost s0 u →
        Steps P_ghost (f u) sf →
        u.pc = pc →
        u.status = .Running →
        (∀ msg, (f u).status ≠ .Exception msg) →
        u.mem.KeepsFrozen (f u).mem →
        ExecFrozen u.mem →
        InvS u →
        ExecFrozen (f u).mem ∧ InvS (f u))) ∨
    (P_real.externAt? pc = none ∧
      ∀ u : State,
        Steps P_ghost s0 u →
        Steps P_ghost (f u) sf →
        u.pc = pc →
        u.status = .Running →
        (∀ msg, (f u).status ≠ .Exception msg) →
        u.mem.KeepsFrozen (f u).mem →
        ExecFrozen u.mem →
        keep (u.readReg64 .lr) = false →
        InvS u →
        Steps P_real u (f u) ∧ ExecFrozen (f u).mem ∧ InvS (f u))

def GhostExternReplaysS (keep : BitVec 64 → Bool) (InvS : State → Prop)
    (P_ghost P_real : Program) : Prop :=
  ∀ (pc : BitVec 64) (f : State → State),
    P_ghost.externAt? pc = some f →
    (P_real.externAt? pc = some f ∧
      (∀ u : State, u.status = .Running → u.mem.KeepsFrozen (f u).mem →
        ExecFrozen u.mem → InvS u → ExecFrozen (f u).mem ∧ InvS (f u))) ∨
    (P_real.externAt? pc = none ∧
      ∀ u : State,
        u.pc = pc →
        u.status = .Running →
        (∀ msg, (f u).status ≠ .Exception msg) →
        ExecFrozen u.mem →
        keep (u.readReg64 .lr) = false →
        InvS u →
        Steps P_real u (f u) ∧ ExecFrozen (f u).mem ∧ InvS (f u))

theorem GhostExternReplaysS.toOn {keep : BitVec 64 → Bool} {InvS : State → Prop}
    {P_ghost P_real : Program} (h : GhostExternReplaysS keep InvS P_ghost P_real)
    (s0 sf : State) :
    GhostExternReplaysOn keep InvS P_ghost P_real s0 sf := by
  intro pc f heg
  rcases h pc f heg with ⟨her, hpres⟩ | ⟨hnone, hrep⟩
  · exact Or.inl ⟨her, fun u _ _ _ hrun _ hkf hfr hinv => hpres u hrun hkf hfr hinv⟩
  · exact Or.inr ⟨hnone, fun u _ _ hpc hrun hnoex _ hfr hlr hinv =>
      hrep u hpc hrun hnoex hfr hlr hinv⟩

private theorem steps_transfer_ghostOn_aux
    {keep : BitVec 64 → Bool} {InvS : State → Prop}
    {P_ghost P_real : Program} {s0 : State}
    (hsvc_ghost : P_ghost.svc = Syscall.standard)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hno_new_hooks : ∀ pc, P_ghost.externAt? pc = none → P_real.externAt? pc = none)
    {u sf : State}
    (hsteps : Steps P_ghost u sf)
    (hpre : Steps P_ghost s0 u)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted)
    (hfr_u : ExecFrozen u.mem)
    (hinv_u : InvS u)
    (hReplays : GhostExternReplaysOn keep InvS P_ghost P_real s0 sf)
    (hExecInv : ∀ z inst, Steps P_ghost s0 z → Steps P_ghost (execInst inst z) sf →
      z.status = .Running → P_ghost.externAt? z.pc = none →
      P_ghost.fetchMem z.mem z.pc = some inst → inst.isSvc0 = false →
      z.mem.KeepsFrozen (execInst inst z).mem → ExecFrozen z.mem → InvS z →
      InvS (execInst inst z))
    (hSvcInv : ∀ z, Steps P_ghost s0 z → Steps P_ghost (Syscall.standard z) sf →
      z.status = .Running → P_ghost.externAt? z.pc = none →
      P_ghost.fetchMem z.mem z.pc = some (.system false 0#16) →
      z.mem.KeepsFrozen (Syscall.standard z).mem → ExecFrozen z.mem → InvS z →
      InvS (Syscall.standard z))
    (hlr_calls : ∀ z : State, Steps P_ghost s0 z → Steps P_ghost z sf →
      z.status = .Running → P_ghost.externAt? z.pc ≠ P_real.externAt? z.pc →
      keep (z.readReg64 .lr) = false) :
    Steps P_real u sf ∧ ExecFrozen sf.mem ∧ InvS sf := by
  induction hsteps with
  | refl s => exact ⟨Steps.refl s, hfr_u, hinv_u⟩
  | @step a b c h1 hrest ih =>
    have hstep_ac : Steps P_ghost a c := Steps.step h1 hrest
    cases h1 with
    | halt_unmapped _ _ _ =>
      exact False.elim (hnhalt_sf (steps_preserves_halted hrest rfl))
    | extern_fault _ _ _ =>
      exact False.elim (hnoex_sf _ (steps_preserves_exception hrest rfl))
    | @exec inst hrun hfm =>
      have hfm_orig := hfm
      unfold Program.fetchMem at hfm
      cases heg : P_ghost.externAt? a.pc with
      | some f => simp [heg] at hfm
      | none =>
        have her : P_real.externAt? a.pc = none := hno_new_hooks a.pc heg
        have hfm_real : P_real.fetchMem a.mem a.pc = some inst := by
          unfold Program.fetchMem
          simpa [heg, her] using hfm
        by_cases hsvc0 : inst.isSvc0 = true
        · have hinst : inst = .system false 0#16 := by
            cases inst <;> simp [Instr.isSvc0] at hsvc0
            rcases hsvc0 with ⟨rfl, rfl⟩; rfl
          subst hinst
          have hev_g : P_ghost.evalInst (.system false 0#16) a = Syscall.standard a := by
            simp [Program.evalInst, execInstWithSvc, hsvc_ghost]
          have hev_r : P_real.evalInst (.system false 0#16) a = Syscall.standard a := by
            simp [Program.evalInst, execInstWithSvc, hsvc_real]
          have hstep1_g : Step P_ghost a (Syscall.standard a) := hev_g ▸ Step.exec hrun hfm_orig
          have hstep1_r : Step P_real a (Syscall.standard a) := hev_r ▸ Step.exec hrun hfm_real
          obtain ⟨_, hfr_b⟩ := standard_stripS (keep := keep) hfr_u
          rw [hev_g] at hrest ih
          have hinv_b : InvS (Syscall.standard a) :=
            hSvcInv a hpre hrest hrun heg hfm_orig hstep1_r.keepsFrozen hfr_u hinv_u
          have hpre_b : Steps P_ghost s0 (Syscall.standard a) :=
            hpre.trans (Steps.step hstep1_g (Steps.refl _))
          obtain ⟨hrest_r, hfr_c, hinv_c⟩ :=
            ih hpre_b hnoex_sf hnhalt_sf hfr_b hinv_b hReplays hExecInv hSvcInv hlr_calls
          exact ⟨Steps.step hstep1_r hrest_r, hfr_c, hinv_c⟩
        · have hnsvc0 : inst.isSvc0 = false := Bool.eq_false_iff.mpr hsvc0
          have hev_g : P_ghost.evalInst inst a = execInst inst a :=
            evalInst_eq_execInst_of_not_isSvc0 _ hnsvc0 a
          have hev_r : P_real.evalInst inst a = execInst inst a :=
            evalInst_eq_execInst_of_not_isSvc0 _ hnsvc0 a
          have hstep1_g : Step P_ghost a (execInst inst a) := hev_g ▸ Step.exec hrun hfm_orig
          have hstep1_r : Step P_real a (execInst inst a) := hev_r ▸ Step.exec hrun hfm_real
          obtain ⟨hfr_b, _⟩ := execInst_preserves_execFrozen_and_fs hnsvc0 hfr_u
          rw [hev_g] at hrest ih
          have hinv_b : InvS (execInst inst a) :=
            hExecInv a inst hpre hrest hrun heg hfm_orig hnsvc0 hstep1_r.keepsFrozen hfr_u hinv_u
          have hpre_b : Steps P_ghost s0 (execInst inst a) :=
            hpre.trans (Steps.step hstep1_g (Steps.refl _))
          obtain ⟨hrest_r, hfr_c, hinv_c⟩ :=
            ih hpre_b hnoex_sf hnhalt_sf hfr_b hinv_b hReplays hExecInv hSvcInv hlr_calls
          exact ⟨Steps.step hstep1_r hrest_r, hfr_c, hinv_c⟩
    | @extern f hrun heg hkf hsym =>
      have hstep1_g : Step P_ghost a (f a) := Step.extern hrun heg hkf hsym
      have hnoex_fa : ∀ msg, (f a).status ≠ .Exception msg := fun msg hex =>
        hnoex_sf msg (steps_preserves_exception hrest hex)
      have hpre_b : Steps P_ghost s0 (f a) :=
        hpre.trans (Steps.step hstep1_g (Steps.refl _))
      rcases hReplays a.pc f heg with ⟨her, hfr_pres⟩ | ⟨her_none, hghost_run⟩
      · have hstep1_r : Step P_real a (f a) := Step.extern hrun her hkf hsym
        obtain ⟨hfr_b, hinv_b⟩ := hfr_pres a hpre hrest rfl hrun hnoex_fa hkf hfr_u hinv_u
        obtain ⟨hrest_r, hfr_c, hinv_c⟩ :=
          ih hpre_b hnoex_sf hnhalt_sf hfr_b hinv_b hReplays hExecInv hSvcInv hlr_calls
        exact ⟨Steps.step hstep1_r hrest_r, hfr_c, hinv_c⟩
      · have hne_ext : P_ghost.externAt? a.pc ≠ P_real.externAt? a.pc := by
          rw [heg, her_none]; nofun
        have hlr_a : keep (a.readReg64 .lr) = false :=
          hlr_calls a hpre hstep_ac hrun hne_ext
        obtain ⟨hsteps_fa, hfr_b, hinv_b⟩ :=
          hghost_run a hpre hrest rfl hrun hnoex_fa hkf hfr_u hlr_a hinv_u
        obtain ⟨hrest_r, hfr_c, hinv_c⟩ :=
          ih hpre_b hnoex_sf hnhalt_sf hfr_b hinv_b hReplays hExecInv hSvcInv hlr_calls
        exact ⟨hsteps_fa.trans hrest_r, hfr_c, hinv_c⟩

/-- Trajectory- and state-indexed `Steps` ghost-to-real transfer (`baseExt`-generic). -/
theorem steps_transfer_ghostOn
    {keep : BitVec 64 → Bool} {InvS : State → Prop}
    {P_ghost P_real : Program}
    (hsvc_ghost : P_ghost.svc = Syscall.standard)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hno_new_hooks : ∀ pc, P_ghost.externAt? pc = none → P_real.externAt? pc = none)
    {s0 sf : State}
    (hsteps : Steps P_ghost s0 sf)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted)
    (hfr0 : ExecFrozen s0.mem)
    (hinv0 : InvS s0)
    (hReplays : GhostExternReplaysOn keep InvS P_ghost P_real s0 sf)
    (hExecInv : ∀ z inst, Steps P_ghost s0 z → Steps P_ghost (execInst inst z) sf →
      z.status = .Running → P_ghost.externAt? z.pc = none →
      P_ghost.fetchMem z.mem z.pc = some inst → inst.isSvc0 = false →
      z.mem.KeepsFrozen (execInst inst z).mem → ExecFrozen z.mem → InvS z →
      InvS (execInst inst z))
    (hSvcInv : ∀ z, Steps P_ghost s0 z → Steps P_ghost (Syscall.standard z) sf →
      z.status = .Running → P_ghost.externAt? z.pc = none →
      P_ghost.fetchMem z.mem z.pc = some (.system false 0#16) →
      z.mem.KeepsFrozen (Syscall.standard z).mem → ExecFrozen z.mem → InvS z →
      InvS (Syscall.standard z))
    (hlr_calls : ∀ z : State, Steps P_ghost s0 z → Steps P_ghost z sf →
      z.status = .Running → P_ghost.externAt? z.pc ≠ P_real.externAt? z.pc →
      keep (z.readReg64 .lr) = false) :
    Steps P_real s0 sf ∧ ExecFrozen sf.mem ∧ InvS sf :=
  steps_transfer_ghostOn_aux hsvc_ghost hsvc_real hno_new_hooks hsteps (Steps.refl s0)
    hnoex_sf hnhalt_sf hfr0 hinv0 hReplays hExecInv hSvcInv hlr_calls

/-- State-indexed `Steps` transfer for `InvS u := InvMem u.mem ∧ PredFs u.fs`, discharging
    non-syscall `Step.exec` preservation automatically via `execInst_preserves_execFrozen_and_fs`. -/
theorem steps_transfer_ghostS
    {keep : BitVec 64 → Bool} {InvMem : Memory → Prop} {PredFs : FsState → Prop}
    {P_ghost P_real : Program}
    (hsvc_ghost : P_ghost.svc = Syscall.standard)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hno_new_hooks : ∀ pc, P_ghost.externAt? pc = none → P_real.externAt? pc = none)
    (hInvStable : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    {s0 sf : State}
    (hsteps : Steps P_ghost s0 sf)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted)
    (hfr0 : ExecFrozen s0.mem)
    (hinv0 : InvMem s0.mem)
    (hfs0 : PredFs s0.fs)
    (hReplays : GhostExternReplaysOn keep (fun u => InvMem u.mem ∧ PredFs u.fs) P_ghost P_real s0 sf)
    (hSvcFs : ∀ z, Steps P_ghost s0 z → Steps P_ghost (Syscall.standard z) sf →
      z.status = .Running → P_ghost.externAt? z.pc = none →
      P_ghost.fetchMem z.mem z.pc = some (.system false 0#16) →
      ExecFrozen z.mem → InvMem z.mem → PredFs z.fs →
      PredFs (Syscall.standard z).fs)
    (hlr_calls : ∀ z : State, Steps P_ghost s0 z → Steps P_ghost z sf →
      z.status = .Running → P_ghost.externAt? z.pc ≠ P_real.externAt? z.pc →
      keep (z.readReg64 .lr) = false) :
    Steps P_real s0 sf ∧ ExecFrozen sf.mem ∧ InvMem sf.mem ∧ PredFs sf.fs := by
  obtain ⟨hsteps_r, hfr_sf, hinv_sf, hfs_sf⟩ :=
    steps_transfer_ghostOn hsvc_ghost hsvc_real hno_new_hooks hsteps hnoex_sf hnhalt_sf hfr0
      ⟨hinv0, hfs0⟩ hReplays
      (fun z inst _ _ _ _ _ hnsvc0 hkf hfr ⟨hinv, hfs⟩ => by
        obtain ⟨_, hfs_eq⟩ := execInst_preserves_execFrozen_and_fs hnsvc0 hfr
        exact ⟨hInvStable z.mem _ hinv hkf, hfs_eq ▸ hfs⟩)
      (fun z hpre hrest hrun heg hfm hkf hfr ⟨hinv, hfs⟩ =>
        ⟨hInvStable z.mem _ hinv hkf, hSvcFs z hpre hrest hrun heg hfm hfr hinv hfs⟩)
      hlr_calls
  exact ⟨hsteps_r, hfr_sf, hinv_sf, hfs_sf⟩

/-- Generic `subroutine_ok` transfer from `(P_ghost, spec_ghost)` to `(P_real, spec_real)`. -/
theorem subroutine_ok_transfer_ghostOn {α : Type}
    {keep : BitVec 64 → Bool} {InvS : State → Prop}
    {P_ghost P_real : Program} {entry : BitVec 64}
    {spec_ghost spec_real : Spec α}
    (hsvc_ghost : P_ghost.svc = Syscall.standard)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hno_new_hooks : ∀ pc, P_ghost.externAt? pc = none → P_real.externAt? pc = none)
    (hPreImp : ∀ x R (s0 : State),
      (s0.mem ⊨ spec_real.pre x s0 ∗ R) →
      s0.pc = entry →
      s0.status = .Running →
      s0.spAligned = true →
      (s0.mem ⊨ spec_ghost.pre x s0 ∗ R) ∧
      P_ghost.CodeLoaded s0.mem ∧
      ExecFrozen s0.mem ∧
      InvS s0 ∧
      ∀ sf : State,
        Steps P_ghost s0 sf →
        SubroutineOutcome spec_ghost x R s0 sf →
        GhostExternReplaysOn keep InvS P_ghost P_real s0 sf ∧
        (∀ z inst, Steps P_ghost s0 z → Steps P_ghost (execInst inst z) sf →
          z.status = .Running → P_ghost.externAt? z.pc = none →
          P_ghost.fetchMem z.mem z.pc = some inst → inst.isSvc0 = false →
          z.mem.KeepsFrozen (execInst inst z).mem → ExecFrozen z.mem → InvS z →
          InvS (execInst inst z)) ∧
        (∀ z, Steps P_ghost s0 z → Steps P_ghost (Syscall.standard z) sf →
          z.status = .Running → P_ghost.externAt? z.pc = none →
          P_ghost.fetchMem z.mem z.pc = some (.system false 0#16) →
          z.mem.KeepsFrozen (Syscall.standard z).mem → ExecFrozen z.mem → InvS z →
          InvS (Syscall.standard z)) ∧
        (∀ z : State, Steps P_ghost s0 z → Steps P_ghost z sf →
          z.status = .Running → P_ghost.externAt? z.pc ≠ P_real.externAt? z.pc →
          keep (z.readReg64 .lr) = false))
    (hOutImp : ∀ x R (s0 sf : State),
      ExecFrozen sf.mem → InvS sf →
      SubroutineOutcome spec_ghost x R s0 sf →
      SubroutineOutcome spec_real x R s0 sf)
    (hGhostOk : subroutine_ok P_ghost entry spec_ghost) :
    subroutine_ok P_real entry spec_real := by
  apply subroutine_ok_of_steps_outcome
  intro x R s0 hpc hrun hm hsp _
  obtain ⟨hm_g, hCodeG, hFr0, hInv0, hTraj⟩ := hPreImp x R s0 hm hpc hrun hsp
  obtain ⟨sf, hsteps, hout⟩ :=
    subroutine_ok_elim_steps_outcome hGhostOk x R s0 hpc hrun hm_g hsp hCodeG
  have hnoex : ∀ msg, sf.status ≠ .Exception msg := by
    intro msg hex
    rcases hout with ⟨⟨_, _, hr⟩, _, _⟩ | ⟨hp, _⟩ | ⟨_, he, _⟩ | ⟨ho, _⟩
    · rw [hex] at hr; cases hr
    · rw [hex] at hp; cases hp
    · rw [hex] at he; cases he
    · rw [hex] at ho; cases ho
  have hnhalt : sf.status ≠ .Halted := subroutineOutcome_not_halted hout
  obtain ⟨hRep, hExec, hSvc, hLr⟩ := hTraj sf hsteps hout
  obtain ⟨hsteps_real, hFr_sf, hInv_sf⟩ :=
    steps_transfer_ghostOn hsvc_ghost hsvc_real hno_new_hooks hsteps hnoex hnhalt
      hFr0 hInv0 hRep hExec hSvc hLr
  exact ⟨sf, hsteps_real, hOutImp x R s0 sf hFr_sf hInv_sf hout⟩

theorem subroutine_ok_transfer_ghostS {α : Type}
    {keep : BitVec 64 → Bool} {InvMem : Memory → Prop} {PredFs : FsState → Prop}
    {P_ghost P_real : Program} {entry : BitVec 64}
    {spec_ghost spec_real : Spec α}
    (hsvc_ghost : P_ghost.svc = Syscall.standard)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hno_new_hooks : ∀ pc, P_ghost.externAt? pc = none → P_real.externAt? pc = none)
    (hInvStable : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    (hPreImp : ∀ x R (s0 : State),
      (s0.mem ⊨ spec_real.pre x s0 ∗ R) →
      s0.pc = entry →
      s0.status = .Running →
      s0.spAligned = true →
      (s0.mem ⊨ spec_ghost.pre x s0 ∗ R) ∧
      P_ghost.CodeLoaded s0.mem ∧
      ExecFrozen s0.mem ∧
      InvMem s0.mem ∧
      PredFs s0.fs ∧
      ∀ sf : State,
        Steps P_ghost s0 sf →
        SubroutineOutcome spec_ghost x R s0 sf →
        GhostExternReplaysOn keep (fun u => InvMem u.mem ∧ PredFs u.fs) P_ghost P_real s0 sf ∧
        (∀ z, Steps P_ghost s0 z → Steps P_ghost (Syscall.standard z) sf →
          z.status = .Running → P_ghost.externAt? z.pc = none →
          P_ghost.fetchMem z.mem z.pc = some (.system false 0#16) →
          ExecFrozen z.mem → InvMem z.mem → PredFs z.fs →
          PredFs (Syscall.standard z).fs) ∧
        (∀ z : State, Steps P_ghost s0 z → Steps P_ghost z sf →
          z.status = .Running → P_ghost.externAt? z.pc ≠ P_real.externAt? z.pc →
          keep (z.readReg64 .lr) = false))
    (hOutImp : ∀ x R (s0 sf : State),
      ExecFrozen sf.mem → InvMem sf.mem → PredFs sf.fs →
      SubroutineOutcome spec_ghost x R s0 sf →
      SubroutineOutcome spec_real x R s0 sf)
    (hGhostOk : subroutine_ok P_ghost entry spec_ghost) :
    subroutine_ok P_real entry spec_real := by
  refine subroutine_ok_transfer_ghostOn
    (keep := keep) (InvS := fun u => InvMem u.mem ∧ PredFs u.fs)
    hsvc_ghost hsvc_real hno_new_hooks ?_ ?_ hGhostOk
  · intro x R s0 hm hpc hrun hsp
    obtain ⟨hm_g, hCodeG, hFr0, hInv0, hFs0, hTraj⟩ := hPreImp x R s0 hm hpc hrun hsp
    refine ⟨hm_g, hCodeG, hFr0, ⟨hInv0, hFs0⟩, fun sf hsteps hout => ?_⟩
    obtain ⟨hRep, hSvc, hLr⟩ := hTraj sf hsteps hout
    refine ⟨hRep, ?_, ?_, hLr⟩
    · intro z inst _ _ _ _ _ hnsvc0 hkf hfr ⟨hinv, hfs⟩
      obtain ⟨_, hfs_eq⟩ := execInst_preserves_execFrozen_and_fs hnsvc0 hfr
      exact ⟨hInvStable z.mem _ hinv hkf, hfs_eq ▸ hfs⟩
    · intro z hpre hrest hr heg hfm hkf hfr ⟨hinv, hfs⟩
      exact ⟨hInvStable z.mem _ hinv hkf, hSvc z hpre hrest hr heg hfm hfr hinv hfs⟩
  · intro x R s0 sf hFr ⟨hInv, hFs⟩ hout
    exact hOutImp x R s0 sf hFr hInv hFs hout

/-! ## `cliGhostExterns` Overlay and `DirectOrBranchStub` Helpers -/

/-- `InvMem`-guarded counterpart of `StubReachesTarget` supporting 1-word `B` branch stubs loaded
    in `u.mem` (`DirectOrBranchStub`). -/
def StubReachesTargetOn (InvMem : Memory → Prop) (P_real : Program)
    (stubPc entryTarget : BitVec 64) : Prop :=
  ∀ u : State,
    u.pc = stubPc →
    u.status = .Running →
    ExecFrozen u.mem →
    InvMem u.mem →
    Steps P_real u (u.setPC entryTarget)

theorem StubReachesTarget.toOn {InvMem : Memory → Prop} {P_real : Program}
    {stubPc entryTarget : BitVec 64}
    (h : StubReachesTarget P_real stubPc entryTarget) :
    StubReachesTargetOn InvMem P_real stubPc entryTarget :=
  fun u hpc hrun hfr _ => h u hpc hrun hfr

private theorem concat_bytesOfWordLE (w : BitVec 32) :
    (Obj.bytesOfWordLE w)[3] ++ (Obj.bytesOfWordLE w)[2] ++
      (Obj.bytesOfWordLE w)[1] ++ (Obj.bytesOfWordLE w)[0] = w := by
  change BitVec.extractLsb' 24 8 (w.setWidth 64) ++
    BitVec.extractLsb' 16 8 (w.setWidth 64) ++
    BitVec.extractLsb' 8 8 (w.setWidth 64) ++
    BitVec.extractLsb' 0 8 (w.setWidth 64) = w
  bv_bits

private theorem holdsBytes_rx_keepsFrozen_4 {m0 m : Memory} {a : BitVec 64} {w : BitVec 32}
    (hhb : Obj.HoldsBytes m0 a (Obj.bytesOfWordLE w) (fun _ => Perm.rx))
    (hkf : m0.KeepsFrozen m) :
    m.canExec a 4 = true ∧ m.read32 a = w := by
  have h0 := hhb 0 (by simp)
  have h1 := hhb 1 (by simp)
  have h2 := hhb 2 (by simp)
  have h3 := hhb 3 (by simp)
  have hfz0 : m0.Frozen (a + 0#64) := by unfold Memory.Frozen; rw [h0.2.1]; rfl
  have hfz1 : m0.Frozen (a + 1#64) := by unfold Memory.Frozen; rw [h1.2.1]; rfl
  have hfz2 : m0.Frozen (a + 2#64) := by unfold Memory.Frozen; rw [h2.2.1]; rfl
  have hfz3 : m0.Frozen (a + 3#64) := by unfold Memory.Frozen; rw [h3.2.1]; rfl
  obtain ⟨hr0, hp0, _⟩ := hkf _ hfz0
  obtain ⟨hr1, hp1, _⟩ := hkf _ hfz1
  obtain ⟨hr2, hp2, _⟩ := hkf _ hfz2
  obtain ⟨hr3, hp3, _⟩ := hkf _ hfz3
  have ha0 : a = a + 0#64 := by bv_omega
  have ha2 : a + 1#64 + 1#64 = a + 2#64 := by bv_omega
  have ha3 : a + 1#64 + 1#64 + 1#64 = a + 3#64 := by bv_omega
  refine ⟨?_, ?_⟩
  · simp only [Memory.canExec, Memory.allPerm]
    rw [ha3, ha2]
    rw [show m.perm a = m.perm (a + 0#64) from congrArg m.perm ha0]
    rw [hp0, h0.2.1, hp1, h1.2.1, hp2, h2.2.1, hp3, h3.2.1]
    rfl
  · unfold Memory.read32
    rw [hr0, h0.1, hr1, h1.1, hr2, h2.1, hr3, h3.1]
    exact concat_bytesOfWordLE w

/-- Discharge `StubReachesTargetOn InvMem P_real stubVa targetVa` from `DirectOrBranchStub elf stubVa targetVa`
    whenever `InvMem m` implies `sLoad.mem.KeepsFrozen m` for some initial ELF load `sLoad`. -/
theorem stubReachesTargetOn_of_directOrBranchStub
    {InvMem : Memory → Prop} {elf : ElfImage} {P_real : Program}
    {stubVa targetVa : BitVec 64}
    (hNone : P_real.externAt? stubVa = none)
    (hStub : DirectOrBranchStub elf stubVa targetVa)
    (hLoaded : ∀ m : Memory, InvMem m →
      ∃ (inputs : ProcessInputs) (sLoad : State),
        elf.loadState inputs = .ok sLoad ∧ sLoad.mem.KeepsFrozen m) :
    StubReachesTargetOn InvMem P_real stubVa targetVa := by
  intro u hpc hrun hfr hinv
  let _ := hfr
  rcases hStub with rfl | ⟨hal, hrange, hmaps⟩
  · have heq : u.setPC stubVa = u := by
      cases u
      dsimp [State.setPC] at hpc ⊢
      subst hpc
      rfl
    rw [heq]
    exact Steps.refl u
  · obtain ⟨inputs, sLoad, hload, hkf⟩ := hLoaded u.mem hinv
    have hhb := Obj.ElfMaps.holdsBytes hload (p := Perm.rx) (fun q hq => beq_iff_eq.mp hq) hmaps
    obtain ⟨hce, hr32⟩ := holdsBytes_rx_keepsFrozen_4 hhb hkf
    have hdec := Obj.decode_branchWord_b (w := 0x14000000#32) (by decide) hrange
    have hfm : P_real.fetchMem u.mem u.pc = some (.b (targetVa - stubVa)) := by
      rw [hpc]
      unfold Program.fetchMem
      simp only [hNone, Option.isSome_none, Bool.false_eq_true, Bool.not_true, ↓reduceIte,
        hal, ne_eq, not_true_eq_false, hce, hr32, hdec]
    have hstep : Step P_real u (P_real.evalInst (.b (targetVa - stubVa)) u) :=
      Step.exec hrun hfm
    have hev : P_real.evalInst (.b (targetVa - stubVa)) u = u.setPC targetVa := by
      change u.setPC (u.pc + (targetVa - stubVa)) = u.setPC targetVa
      congr 1
      rw [hpc]
      bv_omega
    rw [hev] at hstep
    exact Steps.step hstep (Steps.refl _)

/-- Active symbol/hook pairs overridden by `ghFixed : CliGhostHooks` in `cliGhostExterns`. -/
def GhostSymActive (ghFixed : CliGhostHooks) (sym : String) (f : State → State) : Prop :=
  (sym = lsRustAllocSymCli ∧ f = ghFixed.alloc) ∨
  (sym = lsRustDeallocSymCli ∧ f = ghFixed.dealloc) ∨
  (sym = lsRustReallocSymCli ∧ f = ghFixed.realloc) ∨
  (sym = lsRustAllocZeroedSymCli ∧ f = ghFixed.allocZeroed) ∨
  (sym = lsRustNoAllocShimSymCli ∧ f = ghFixed.shim) ∨
  (sym = lsStringCloneSym ∧ ghFixed.stringClone = some f) ∨
  (sym = lsReadFileSym ∧ ∃ h, ghFixed.readFile = some ⟨f, h⟩) ∨
  (sym = lsReadStdinSym ∧ ∃ h, ghFixed.readStdin = some ⟨f, h⟩) ∨
  (sym = CryptoVerification.SignalSession.lsMemsetSym ∧ ghFixed.memset = some f) ∨
  (sym = CryptoVerification.SignalSession.lsMemcpySym ∧ ghFixed.memcpy = some f)

/-- `cliGhostExterns ghFixed baseExt` only adds hooks: if it maps `sym` to `none`, so does `baseExt`. -/
theorem cliGhostExterns_none_imp
    {ghFixed : CliGhostHooks} {baseExt : String → Option (State → State)} {sym : String}
    (h : cliGhostExterns ghFixed baseExt sym = none) :
    baseExt sym = none := by
  unfold cliGhostExterns at h
  split at h <;> try cases h
  split at h <;> try cases h
  split at h <;> try cases h
  split at h <;> try cases h
  split at h <;> try cases h
  split at h
  · split at h
    · cases h
    · exact h
  · split at h
    · split at h
      · cases h
      · exact h
    · split at h
      · split at h
        · cases h
        · exact h
      · split at h
        · split at h
          · cases h
          · exact h
        · split at h
          · split at h
            · cases h
            · exact h
          · exact h

private theorem findSome?_const_none {α β : Type} (xs : List α) (p : α → Bool) :
    (xs.findSome? fun x => if p x then (none : Option β) else none) = none := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.findSome?_cons]
    cases p hd <;> exact ih

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

/-- Every symbol mapped to `none` in `lib.blockProgram mpl idx (cliGhostExterns ghFixed baseExt)`
is mapped to `none` in `lib.blockProgram mpl idx baseExt`. -/
theorem blockProgram_cliGhostExterns_no_new_hooks
    (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement) (idx : Nat)
    (ghFixed : CliGhostHooks) (baseExt : String → Option (State → State)) :
    ∀ pc : BitVec 64,
      (lib.blockProgram mpl idx (cliGhostExterns ghFixed baseExt)).externAt? pc = none →
      (lib.blockProgram mpl idx baseExt).externAt? pc = none := by
  intro pc h
  unfold Obj.MultiPlacedLib.blockProgram Obj.PlacedLib.program Program.externAt? Program.hookAtOff? at h ⊢
  dsimp only at h ⊢
  rw [findSome?_const_none, Option.or_none] at h ⊢
  exact findSome?_none_mono _ (@cliGhostExterns_none_imp ghFixed baseExt) _ h

private theorem cliGhostExterns_some_cases
    {ghFixed : CliGhostHooks} {baseExt : String → Option (State → State)}
    {sym : String} {f : State → State}
    (h : cliGhostExterns ghFixed baseExt sym = some f) :
    GhostSymActive ghFixed sym f ∨ baseExt sym = some f := by
  unfold cliGhostExterns at h
  cases hc1 : (sym == lsRustAllocSymCli) with
  | true =>
    simp only [hc1, ↓reduceIte] at h
    injection h with h
    exact Or.inl (Or.inl ⟨beq_iff_eq.mp hc1, h.symm⟩)
  | false =>
    simp only [hc1, Bool.false_eq_true, ↓reduceIte] at h
    cases hc2 : (sym == lsRustDeallocSymCli) with
    | true =>
      simp only [hc2, ↓reduceIte] at h
      injection h with h
      exact Or.inl (Or.inr (Or.inl ⟨beq_iff_eq.mp hc2, h.symm⟩))
    | false =>
      simp only [hc2, Bool.false_eq_true, ↓reduceIte] at h
      cases hc3 : (sym == lsRustReallocSymCli) with
      | true =>
        simp only [hc3, ↓reduceIte] at h
        injection h with h
        exact Or.inl (Or.inr (Or.inr (Or.inl ⟨beq_iff_eq.mp hc3, h.symm⟩)))
      | false =>
        simp only [hc3, Bool.false_eq_true, ↓reduceIte] at h
        cases hc4 : (sym == lsRustAllocZeroedSymCli) with
        | true =>
          simp only [hc4, ↓reduceIte] at h
          injection h with h
          exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨beq_iff_eq.mp hc4, h.symm⟩))))
        | false =>
          simp only [hc4, Bool.false_eq_true, ↓reduceIte] at h
          cases hc5 : (sym == lsRustNoAllocShimSymCli) with
          | true =>
            simp only [hc5, ↓reduceIte] at h
            injection h with h
            exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨beq_iff_eq.mp hc5, h.symm⟩)))))
          | false =>
            simp only [hc5, Bool.false_eq_true, ↓reduceIte] at h
            cases hc6 : (sym == lsStringCloneSym) with
            | true =>
              simp only [hc6, ↓reduceIte] at h
              cases hsc : ghFixed.stringClone with
              | none =>
                rw [hsc] at h
                exact Or.inr h
              | some g =>
                rw [hsc] at h
                injection h with h
                subst h
                exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨beq_iff_eq.mp hc6, hsc⟩))))))
            | false =>
              simp only [hc6, Bool.false_eq_true, ↓reduceIte] at h
              cases hc7 : (sym == lsReadFileSym) with
              | true =>
                simp only [hc7, ↓reduceIte] at h
                cases hrf : ghFixed.readFile with
                | none =>
                  rw [hrf] at h
                  exact Or.inr h
                | some gh =>
                  rcases gh with ⟨g, hg⟩
                  rw [hrf] at h
                  injection h with h
                  subst h
                  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨beq_iff_eq.mp hc7, hg, hrf⟩)))))))
              | false =>
                simp only [hc7, Bool.false_eq_true, ↓reduceIte] at h
                cases hc8 : (sym == lsReadStdinSym) with
                | true =>
                  simp only [hc8, ↓reduceIte] at h
                  cases hrs : ghFixed.readStdin with
                  | none =>
                    rw [hrs] at h
                    exact Or.inr h
                  | some gh =>
                    rcases gh with ⟨g, hg⟩
                    rw [hrs] at h
                    injection h with h
                    subst h
                    exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨beq_iff_eq.mp hc8, hg, hrs⟩))))))))
                | false =>
                  simp only [hc8, Bool.false_eq_true, ↓reduceIte] at h
                  cases hc9 : (sym == CryptoVerification.SignalSession.lsMemsetSym) with
                  | true =>
                    simp only [hc9, ↓reduceIte] at h
                    cases hms : ghFixed.memset with
                    | none =>
                      rw [hms] at h
                      exact Or.inr h
                    | some g =>
                      rw [hms] at h
                      injection h with h
                      subst h
                      exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨beq_iff_eq.mp hc9, hms⟩)))))))))
                  | false =>
                    simp only [hc9, Bool.false_eq_true, ↓reduceIte] at h
                    cases hc10 : (sym == CryptoVerification.SignalSession.lsMemcpySym) with
                    | true =>
                      simp only [hc10, ↓reduceIte] at h
                      cases hmc : ghFixed.memcpy with
                      | none =>
                        rw [hmc] at h
                        exact Or.inr h
                      | some g =>
                        rw [hmc] at h
                        injection h with h
                        subst h
                        exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨beq_iff_eq.mp hc10, hmc⟩)))))))))
                    | false =>
                      simp only [hc10, Bool.false_eq_true, ↓reduceIte] at h
                      exact Or.inr h

private theorem findSome?_stubs_cliGhostExterns_cases
    (exts : List String) (ρ : String → BitVec 64) (base pc : BitVec 64)
    (ghFixed : CliGhostHooks) (baseExt : String → Option (State → State))
    {f : State → State}
    (h : ((exts.map fun e => (e, (ρ e - base).toNat)).findSome?
      fun (n, o) => if o == (pc - base).toNat then cliGhostExterns ghFixed baseExt n else none) = some f) :
    ((exts.map fun e => (e, (ρ e - base).toNat)).findSome?
      fun (n, o) => if o == (pc - base).toNat then baseExt n else none) = some f ∨
    ∃ sym : String, GhostSymActive ghFixed sym f ∧ pc = ρ sym := by
  induction exts with
  | nil => simp at h
  | cons e tl ih =>
    simp only [List.map_cons, List.findSome?_cons] at h ⊢
    cases hoo : ((ρ e - base).toNat == (pc - base).toNat) with
    | false =>
      simp only [hoo, Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact ih h
    | true =>
      simp only [hoo, ↓reduceIte] at h ⊢
      cases he : cliGhostExterns ghFixed baseExt e with
      | none =>
        rw [he] at h
        rw [cliGhostExterns_none_imp he]
        exact ih h
      | some g =>
        rw [he] at h
        injection h with hgf
        subst hgf
        rcases cliGhostExterns_some_cases he with hAct | hBase
        · have heq : ρ e - base = pc - base := BitVec.eq_of_toNat_eq (beq_iff_eq.mp hoo)
          exact Or.inr ⟨e, hAct, by bv_omega⟩
        · rw [hBase]
          exact Or.inl rfl

/-- Generic classification of every active hook `(pc, f)` of
    `lib.blockProgram mpl idx (cliGhostExterns ghFixed baseExt)`: either it is already an identical
    hook of `lib.blockProgram mpl idx baseExt`, or `(sym, f)` satisfies `GhostSymActive ghFixed sym f`
    at `pc = lib.resolve mpl sym`. -/
theorem blockProgram_cliGhostExterns_externAt?_cases
    {lib : Obj.MultiPlacedLib} {mpl : Obj.MultiPlacement} {idx : Nat}
    (hIdx : idx < lib.blocks.length)
    (hPl : lib.Placeable mpl)
    (ghFixed : CliGhostHooks) (baseExt : String → Option (State → State))
    {pc : BitVec 64} {f : State → State}
    (h : (lib.blockProgram mpl idx (cliGhostExterns ghFixed baseExt)).externAt? pc = some f) :
    (lib.blockProgram mpl idx baseExt).externAt? pc = some f ∨
      ∃ sym : String, GhostSymActive ghFixed sym f ∧ pc = lib.resolve mpl sym := by
  let _ := hIdx
  let _ := hPl
  unfold Obj.MultiPlacedLib.blockProgram Obj.PlacedLib.program Program.externAt? Program.hookAtOff? at h ⊢
  dsimp only at h ⊢
  rw [findSome?_const_none, Option.or_none] at h ⊢
  exact findSome?_stubs_cliGhostExterns_cases
    (lib.blockLib idx).text.externs (lib.blockPlacement mpl idx).ρ
    (lib.blockPlacement mpl idx).base pc ghFixed baseExt h

/-! ## Real-Row `cliExternsPlaced` and `Syscall.standard` Preservation -/

private theorem fdsGe3Closed_setFd_none {fs : FsState} (fd : BitVec 64)
    (h : FdsGe3Closed fs) : FdsGe3Closed (fs.setFd fd none) := by
  intro k hlo hhi
  simp only [FsState.setFd]
  split
  · rfl
  · exact h k hlo hhi

private theorem fd_lt3_of_some {fs : FsState} {rawFd : BitVec 32} {desc : FdEntry}
    (hClosed : FdsGe3Closed fs)
    (hnslt : ¬ rawFd.slt 0#32 = true)
    (hsome : fs.fds (rawFd.zeroExtend 64) = some desc) :
    (rawFd.zeroExtend 64).toNat < 3 := by
  have hlt32 : rawFd.toNat < 2 ^ 32 := rawFd.isLt
  have hlt64 : rawFd.toNat < 2 ^ 64 := Nat.lt_trans hlt32 (by decide)
  have hlt31 : rawFd.toNat < 2 ^ 31 := by
    rw [BitVec.slt_eq_decide] at hnslt
    simp only [decide_eq_true_eq, not_lt, BitVec.toInt_zero] at hnslt
    rw [BitVec.toInt_eq_toNat_cond] at hnslt
    split at hnslt <;> omega
  have hze : (rawFd.zeroExtend 64).toNat = rawFd.toNat := by
    change (rawFd.setWidth 64).toNat = rawFd.toNat
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hlt64]
  by_contra hge
  have h3 : 3 ≤ rawFd.toNat := by omega
  have heq : BitVec.ofNat 64 rawFd.toNat = rawFd.zeroExtend 64 := by
    apply BitVec.eq_of_toNat_eq
    rw [hze, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64]
  have hnone := hClosed rawFd.toNat h3 hlt31
  rw [heq, hsome] at hnone
  cases hnone

private theorem ite_preserve_fdsGe3Closed {c : Prop} [inst : Decidable c] {a b : State}
    (ha : FdsGe3Closed a.fs) (hb : FdsGe3Closed b.fs) :
    FdsGe3Closed (if c then a else b).fs := by
  cases inst with
  | isFalse _ => exact hb
  | isTrue _ => exact ha

private theorem ite_preserve_fdsGe3Closed_hyp {c : Prop} [inst : Decidable c] {a b : State}
    (ha : c → FdsGe3Closed a.fs) (hb : ¬ c → FdsGe3Closed b.fs) :
    FdsGe3Closed (if c then a else b).fs := by
  cases inst with
  | isFalse hnc => exact hb hnc
  | isTrue hc => exact ha hc

private theorem writeReg64_advancePC_fs (st : State) (r : Reg) (v : BitVec 64) :
    ((st.writeReg64 r v).advancePC).fs = st.fs := rfl

local macro "fs_state_norm" : tactic => `(tactic|
  dsimp (config := { zeta := true, zetaHave := true }) only
    [State.advancePC, State.setPC, State.writeReg64, State.writeReg32, State.setMem,
     State.setBrk, State.setPhysMemAvail, State.nextOracle, State.setStatus,
     State.appendTrace, State.setSigAction, State.setSigAltStack, State.setFs])

local macro "fs_unchanged_close" h:ident : tactic => `(tactic|
  (repeat' split
   all_goals
     fs_state_norm
     exact $h))

private theorem fdsGe3Closed_execReadCommon {s : State} (useExplicitPos : Bool)
    (hClosed : FdsGe3Closed s.fs) :
    FdsGe3Closed (execReadCommon s useExplicitPos).fs := by
  dsimp (config := { zeta := true }) only [execReadCommon]
  refine ite_preserve_fdsGe3Closed hClosed ?_
  refine ite_preserve_fdsGe3Closed_hyp (fun _ => hClosed) (fun hnslt => ?_)
  cases hfd : s.fs.fds ((s.readReg32 Reg.x0).zeroExtend 64) with
  | none =>
    dsimp only
    exact ite_preserve_fdsGe3Closed hClosed hClosed
  | some desc =>
    dsimp (config := { zeta := true }) only
    have hlt3 := fd_lt3_of_some hClosed hnslt hfd
    refine ite_preserve_fdsGe3Closed
      (ite_preserve_fdsGe3Closed hClosed (ite_preserve_fdsGe3Closed hClosed hClosed)) ?_
    refine ite_preserve_fdsGe3Closed hClosed ?_
    refine ite_preserve_fdsGe3Closed hClosed ?_
    refine ite_preserve_fdsGe3Closed hClosed ?_
    refine ite_preserve_fdsGe3Closed hClosed ?_
    refine ite_preserve_fdsGe3Closed ?_ (ite_preserve_fdsGe3Closed hClosed hClosed)
    rw [writeReg64_advancePC_fs]
    exact ite_preserve_fdsGe3Closed hClosed (fdsGe3Closed_setFd_lt3 hlt3 _ hClosed)

private theorem fdsGe3Closed_execRead {s : State} (hClosed : FdsGe3Closed s.fs) :
    FdsGe3Closed (execRead s).fs :=
  fdsGe3Closed_execReadCommon false hClosed

private theorem fdsGe3Closed_execPread64 {s : State} (hClosed : FdsGe3Closed s.fs) :
    FdsGe3Closed (execPread64 s).fs :=
  fdsGe3Closed_execReadCommon true hClosed

private theorem fdsGe3Closed_execWrite {s : State} (hClosed : FdsGe3Closed s.fs) :
    FdsGe3Closed (execWrite s).fs := by
  dsimp (config := { zeta := true }) only [execWrite]
  refine ite_preserve_fdsGe3Closed_hyp (fun _ => hClosed) (fun hnslt => ?_)
  refine ite_preserve_fdsGe3Closed
    (ite_preserve_fdsGe3Closed hClosed
      (ite_preserve_fdsGe3Closed hClosed
        (ite_preserve_fdsGe3Closed hClosed
          (ite_preserve_fdsGe3Closed hClosed (ite_preserve_fdsGe3Closed hClosed hClosed))))) ?_
  cases hfd : s.fs.fds ((s.readReg32 Reg.x0).zeroExtend 64) with
  | none =>
    dsimp only
    exact ite_preserve_fdsGe3Closed hClosed hClosed
  | some desc =>
    dsimp (config := { zeta := true }) only
    have hlt3 := fd_lt3_of_some hClosed hnslt hfd
    refine ite_preserve_fdsGe3Closed hClosed ?_
    refine ite_preserve_fdsGe3Closed hClosed ?_
    refine ite_preserve_fdsGe3Closed hClosed ?_
    refine ite_preserve_fdsGe3Closed hClosed ?_
    refine ite_preserve_fdsGe3Closed hClosed ?_
    refine ite_preserve_fdsGe3Closed hClosed ?_
    refine ite_preserve_fdsGe3Closed hClosed ?_
    refine ite_preserve_fdsGe3Closed hClosed ?_
    exact ite_preserve_fdsGe3Closed
      (fdsGe3Closed_setFd_lt3 hlt3 _ (fdsGe3Closed_setFile _ _ hClosed))
      (ite_preserve_fdsGe3Closed hClosed (ite_preserve_fdsGe3Closed hClosed hClosed))

private theorem fdsGe3Closed_execClose {s : State} (hClosed : FdsGe3Closed s.fs) :
    FdsGe3Closed (execClose s).fs := by
  unfold execClose
  dsimp only
  repeat' split
  all_goals
    fs_state_norm
    first
      | exact hClosed
      | exact fdsGe3Closed_setFd_none _ hClosed

private theorem fdsGe3Closed_execLseek {s : State} (hClosed : FdsGe3Closed s.fs) :
    FdsGe3Closed (execLseek s).fs := by
  unfold execLseek
  dsimp only
  split
  · fs_state_norm; exact hClosed
  · next hnslt =>
    cases hfd : s.fs.fds ((s.readReg32 Reg.x0).zeroExtend 64) with
    | none =>
      dsimp only
      split <;> (fs_state_norm; exact hClosed)
    | some desc =>
      dsimp only
      have hlt3 := fd_lt3_of_some hClosed hnslt hfd
      repeat' split
      repeat' split
      all_goals
        fs_state_norm
        first
          | exact hClosed
          | exact fdsGe3Closed_setFd_lt3 hlt3 _ hClosed

private theorem fdsGe3Closed_execExit {s : State} (h : FdsGe3Closed s.fs) :
    FdsGe3Closed (execExit s).fs := by
  dsimp (config := { zetaHave := true }) only [execExit]; fs_unchanged_close h

private theorem fdsGe3Closed_execIoctl {s : State} (hClosed : FdsGe3Closed s.fs) :
    FdsGe3Closed (execIoctl s).fs := by
  unfold execIoctl
  dsimp only
  split
  · fs_state_norm; exact hClosed
  · next hnslt =>
    cases hfd : s.fs.fds ((s.readReg32 Reg.x0).zeroExtend 64) with
    | none =>
      dsimp only
      split <;> (fs_state_norm; exact hClosed)
    | some desc =>
      dsimp only
      have hlt3 := fd_lt3_of_some hClosed hnslt hfd
      repeat' split
      repeat' split
      all_goals
        fs_state_norm
        first
          | exact hClosed
          | exact fdsGe3Closed_setFd_lt3 hlt3 _ hClosed

private theorem fdsGe3Closed_execFstat {s : State} (h : FdsGe3Closed s.fs) :
    FdsGe3Closed (execFstat s).fs := by
  dsimp (config := { zetaHave := true }) only [execFstat]; fs_unchanged_close h

private theorem fdsGe3Closed_execPpoll {s : State} (h : FdsGe3Closed s.fs) :
    FdsGe3Closed (execPpoll s).fs := by
  dsimp (config := { zeta := true }) only [execPpoll]
  refine ite_preserve_fdsGe3Closed h ?_
  refine ite_preserve_fdsGe3Closed h ?_
  refine ite_preserve_fdsGe3Closed h ?_
  refine ite_preserve_fdsGe3Closed h ?_
  refine ite_preserve_fdsGe3Closed h ?_
  refine ite_preserve_fdsGe3Closed h ?_
  refine ite_preserve_fdsGe3Closed h ?_
  refine ite_preserve_fdsGe3Closed h ?_
  refine ite_preserve_fdsGe3Closed h ?_
  refine ite_preserve_fdsGe3Closed h ?_
  refine ite_preserve_fdsGe3Closed h ?_
  cases evalPpollEntries s.fs s.mem (s.readReg64 Reg.x0) (s.readReg32 Reg.x1).toNat 0 0 with
  | none => exact h
  | some mc =>
    rcases mc with ⟨_, _⟩
    dsimp only
    exact ite_preserve_fdsGe3Closed h h

private theorem fdsGe3Closed_execBrk {s : State} (h : FdsGe3Closed s.fs) :
    FdsGe3Closed (execBrk s).fs := by
  dsimp (config := { zetaHave := true }) only [execBrk]; fs_unchanged_close h

private theorem fdsGe3Closed_execMunmap {s : State} (h : FdsGe3Closed s.fs) :
    FdsGe3Closed (execMunmap s).fs := by
  dsimp (config := { zetaHave := true }) only [execMunmap]; fs_unchanged_close h

private theorem fdsGe3Closed_execMremap {s : State} (h : FdsGe3Closed s.fs) :
    FdsGe3Closed (execMremap s).fs := by
  dsimp (config := { zetaHave := true }) only [execMremap]; fs_unchanged_close h

private theorem fdsGe3Closed_execMmap {s : State} (h : FdsGe3Closed s.fs) :
    FdsGe3Closed (execMmap s).fs := by
  dsimp (config := { zetaHave := true }) only [execMmap]; fs_unchanged_close h

private theorem fdsGe3Closed_execMprotect {s : State} (h : FdsGe3Closed s.fs) :
    FdsGe3Closed (execMprotect s).fs := by
  dsimp (config := { zetaHave := true }) only [execMprotect]; fs_unchanged_close h

private theorem fdsGe3Closed_execMadvise {s : State} (h : FdsGe3Closed s.fs) :
    FdsGe3Closed (execMadvise s).fs := by
  dsimp (config := { zetaHave := true }) only [execMadvise]; fs_unchanged_close h

private theorem fdsGe3Closed_execTkill {s : State} (h : FdsGe3Closed s.fs) :
    FdsGe3Closed (execTkill s).fs := by
  dsimp (config := { zetaHave := true }) only [execTkill]; fs_unchanged_close h

private theorem fdsGe3Closed_execTgkill {s : State} (h : FdsGe3Closed s.fs) :
    FdsGe3Closed (execTgkill s).fs := by
  dsimp (config := { zetaHave := true }) only [execTgkill]; fs_unchanged_close h

private theorem fdsGe3Closed_execSigaltstack {s : State} (h : FdsGe3Closed s.fs) :
    FdsGe3Closed (execSigaltstack s).fs := by
  dsimp (config := { zetaHave := true }) only [execSigaltstack]; fs_unchanged_close h

private theorem fdsGe3Closed_execRtSigaction {s : State} (h : FdsGe3Closed s.fs) :
    FdsGe3Closed (execRtSigaction s).fs := by
  dsimp (config := { zetaHave := true }) only [execRtSigaction]; fs_unchanged_close h

private theorem fdsGe3Closed_execRtSigprocmask {s : State} (h : FdsGe3Closed s.fs) :
    FdsGe3Closed (execRtSigprocmask s).fs := by
  dsimp (config := { zetaHave := true }) only [execRtSigprocmask]; fs_unchanged_close h

private theorem fdsGe3Closed_execClockGettime {s : State} (h : FdsGe3Closed s.fs) :
    FdsGe3Closed (execClockGettime s).fs := by
  dsimp (config := { zetaHave := true }) only [execClockGettime]; fs_unchanged_close h

private theorem fdsGe3Closed_execGetrandom {s : State} (h : FdsGe3Closed s.fs) :
    FdsGe3Closed (execGetrandom s).fs := by
  dsimp (config := { zetaHave := true }) only [execGetrandom]; fs_unchanged_close h

private theorem fdsGe3Closed_execSetTidAddress {s : State} (h : FdsGe3Closed s.fs) :
    FdsGe3Closed (execSetTidAddress s).fs := by
  dsimp (config := { zetaHave := true }) only [execSetTidAddress]; fs_unchanged_close h

private theorem fdsGe3Closed_execSchedGetaffinity {s : State} (h : FdsGe3Closed s.fs) :
    FdsGe3Closed (execSchedGetaffinity s).fs := by
  dsimp (config := { zetaHave := true }) only [execSchedGetaffinity]; fs_unchanged_close h

private theorem fdsGe3Closed_execGetpid {s : State} (h : FdsGe3Closed s.fs) :
    FdsGe3Closed (execGetpid s).fs := by
  dsimp (config := { zetaHave := true }) only [execGetpid]; fs_unchanged_close h

/-- Every syscall in `Syscall.standard` except `fcntl` (`25`) and `openat` (`56`) preserves
    `FdsGe3Closed u.fs`. -/
theorem fdsGe3Closed_syscallStandard_of_not_open_fcntl {u : State}
    (hNotFcntl : (u.readReg64 .x8).toNat ≠ 25)
    (hNotOpenat : (u.readReg64 .x8).toNat ≠ 56)
    (hClosed : FdsGe3Closed u.fs) :
    FdsGe3Closed (Syscall.standard u).fs := by
  unfold Syscall.standard Syscall.dispatch
  split
  · rename_i nr fn hfind
    have hmem := List.mem_of_find?_eq_some hfind
    have hbeq : (nr == u.readReg64 Reg.x8) = true :=
      List.find?_some (p := fun (x : BitVec 64 × (State → State)) => x.1 == u.readReg64 Reg.x8) hfind
    have hnr : nr = u.readReg64 Reg.x8 := beq_iff_eq.mp hbeq
    simp only [Syscall.standardTable, Syscall.stdioTable, Syscall.fileIoOnlyTable,
      Syscall.pollTable, Syscall.allocTable, Syscall.signalsTable, Syscall.timeTable,
      Syscall.randomTable, Syscall.miscTable,
      List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
      Prod.mk.injEq] at hmem
    rcases hmem with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact fdsGe3Closed_execRead hClosed
    · exact fdsGe3Closed_execWrite hClosed
    · exact LibsignalBinary.Proofs.SpecLemmas.SyscallReadWritev.execReadv_fs_preserves
        (fun _ h => fdsGe3Closed_execRead h) hClosed
    · exact LibsignalBinary.Proofs.SpecLemmas.SyscallReadWritev.execWritev_fs_preserves
        (fun _ h => fdsGe3Closed_execWrite h) hClosed
    · exact fdsGe3Closed_execExit hClosed
    · exact fdsGe3Closed_execExit hClosed
    · exfalso; apply hNotFcntl; rw [← hnr]; decide
    · exact fdsGe3Closed_execIoctl hClosed
    · exfalso; apply hNotOpenat; rw [← hnr]; decide
    · exact fdsGe3Closed_execClose hClosed
    · exact fdsGe3Closed_execLseek hClosed
    · exact fdsGe3Closed_execPread64 hClosed
    · exact fdsGe3Closed_execFstat hClosed
    · exact fdsGe3Closed_execPpoll hClosed
    · exact fdsGe3Closed_execBrk hClosed
    · exact fdsGe3Closed_execMunmap hClosed
    · exact fdsGe3Closed_execMremap hClosed
    · exact fdsGe3Closed_execMmap hClosed
    · exact fdsGe3Closed_execMprotect hClosed
    · exact fdsGe3Closed_execMadvise hClosed
    · exact fdsGe3Closed_execTkill hClosed
    · exact fdsGe3Closed_execTgkill hClosed
    · exact fdsGe3Closed_execSigaltstack hClosed
    · exact fdsGe3Closed_execRtSigaction hClosed
    · exact fdsGe3Closed_execRtSigprocmask hClosed
    · exact fdsGe3Closed_execClockGettime hClosed
    · exact fdsGe3Closed_execGetrandom hClosed
    · exact fdsGe3Closed_execSetTidAddress hClosed
    · exact fdsGe3Closed_execSchedGetaffinity hClosed
    · exact fdsGe3Closed_execGetpid hClosed
    · exact fdsGe3Closed_execGetpid hClosed
  · exact hClosed

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

private theorem execFrozen_write16 {m : Memory} (hfr : ExecFrozen m)
    (addr : BitVec 64) (val : BitVec 16) :
    ExecFrozen (m.write16 addr val) :=
  execFrozen_write8 (execFrozen_write8 hfr _ _) _ _

private theorem execFrozen_write32 {m : Memory} (hfr : ExecFrozen m)
    (addr : BitVec 64) (val : BitVec 32) :
    ExecFrozen (m.write32 addr val) :=
  execFrozen_write8 (execFrozen_write8 (execFrozen_write8 (execFrozen_write8 hfr _ _) _ _) _ _) _ _

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
    rw [hp]
    intro _
    exact ⟨rfl, rfl⟩
  · have hp : (loadMultiCodeMem lib mpl m).perm a = m.perm a := by
      unfold Memory.perm; rw [hb]
    rw [hp]
    exact hfr a

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
    rw [hp]
    exact hfr0 a
  · have hp : (restoreMultiCodeMem lib mpl m0 mf).perm a = mf.perm a := by
      unfold Memory.perm; rw [h]
    rw [hp]
    exact hfrf a

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
  | halt_unmapped _ _ _ =>
    exact hfr
  | extern _ he _ _ =>
    unfold Program.externAt? Program.hookAtOff? at he
    rw [hext, hovr, findSome?_const_none, findSome?_const_none] at he
    cases he
  | extern_fault _ _ _ =>
    exact hfr

private theorem stepsUntil_toSteps {prog : Program} {stop : State → Prop} {s0 sf : State}
    (h : StepsUntil prog stop s0 sf) :
    Steps prog s0 sf := by
  induction h with
  | refl s => exact Steps.refl s
  | step _ hstep _ ih => exact Steps.step hstep ih

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

private theorem multiCodeROHookEntry_mem (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement)
    (i : Nat) (entryPc : BitVec 64) (s0 : State) :
    (multiCodeROHookEntry lib mpl i entryPc s0).mem = loadMultiCodeMem lib mpl s0.mem := rfl

private theorem multiCodeROHookExit_mem (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement)
    (i : Nat) (s0 sf' : State) :
    (multiCodeROHookExit lib mpl i s0 sf').mem = restoreMultiCodeMem lib mpl s0.mem sf'.mem := rfl

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
      rw [multiCodeROHookExit_mem]
      refine execFrozen_restoreMultiCodeMem lib mpl hfr0 ?_
      have hfrEntry :
          ExecFrozen (multiCodeROHookEntry lib mpl i (lib.fnAddr mpl fnName) s0).mem := by
        rw [multiCodeROHookEntry_mem]
        exact execFrozen_loadMultiCodeMem lib mpl hfr0
      exact steps_none_preserves_execFrozen rfl rfl rfl
        (stepsUntil_toSteps (Classical.choose_spec hex).1) hfrEntry
    · exact hfr0

private theorem retHook_mem (f : State → State) (s : State) :
    (retHook f s).mem = (f s).mem := rfl
private theorem returnToLinkRegister_mem (s : State) :
    (returnToLinkRegister s).mem = s.mem := rfl
private theorem restoreCallerRegs_mem (sCaller sCallee : State) :
    (restoreCallerRegs sCaller sCallee).mem = sCallee.mem := rfl
private theorem rustPanicked_mem (s : State) :
    (Rust.panicked s).mem = s.mem := rfl

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
      · rw [rustPanicked_mem, restoreCallerRegs_mem]; exact hfr1
      · refine hk _ _ ?_; rw [restoreCallerRegs_mem]; exact hfr1
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
      · rw [rustPanicked_mem, restoreCallerRegs_mem]; exact hfr1
      · refine hk _ _ ?_; rw [restoreCallerRegs_mem]; exact hfr1

private theorem execFrozen_stepRustDealloc1
    (mpl : Obj.MultiPlacement) (frameBytes : Nat) (ptr : BitVec 64)
    {k : State → State}
    (hk : ∀ s1, ExecFrozen s1.mem → ExecFrozen (k s1).mem)
    (s : State) (hfr : ExecFrozen s.mem) :
    ExecFrozen (stepRustDealloc1 mpl frameBytes ptr k s).mem := by
  unfold stepRustDealloc1
  dsimp only
  let sCall := (s.writeReg64 .sp (s.sp - BitVec.ofNat 64 frameBytes)).writeReg64 .x0 ptr
  have hfr1 : ExecFrozen
      (mallocngLib.codeROSubroutineHook mpl "free" (fun _ => none) (fun _ => none)
        Syscall.standard sCall).mem :=
    execFrozen_codeROSubroutineHook mallocngLib mpl "free" sCall hfr
  split
  · exact hfr1
  · refine hk _ ?_; rw [restoreCallerRegs_mem]; exact hfr1

private theorem execFrozen_aesEncHookMallocng
    (mpl : Obj.MultiPlacement) (E : AesKey → Block → Block)
    (s0 : State) (hfr0 : ExecFrozen s0.mem) :
    ExecFrozen (aesEncHookMallocng mpl E s0).mem := by
  unfold aesEncHookMallocng
  split
  · exact hfr0
  · dsimp only
    split
    · exact hfr0
    · refine execFrozen_stepRustAlloc1 mpl true _ _ (fun s1 _ hfr1 => ?_) s0 hfr0
      rw [retHook_mem]
      exact execFrozen_writeVecHeader (execFrozen_writeBytes hfr1 _ _) _ _ _ _

private theorem execFrozen_aesDecHookMallocng
    (mpl : Obj.MultiPlacement) (D : AesKey → Block → Block)
    (s0 : State) (hfr0 : ExecFrozen s0.mem) :
    ExecFrozen (aesDecHookMallocng mpl D s0).mem := by
  unfold aesDecHookMallocng
  split
  · exact hfr0
  · dsimp only
    split
    · rw [retHook_mem]
      exact execFrozen_write64 (execFrozen_write64 hfr0 _ _) _ _
    · refine execFrozen_stepRustAlloc1 mpl true _ _ (fun s1 p hfr1 => ?_) s0 hfr0
      split
      · rw [retHook_mem]
        exact execFrozen_writeVecHeader (execFrozen_writeBytes hfr1 _ _) _ _ _ _
      · refine execFrozen_stepRustDealloc1 mpl _ p (fun s2 hfr2 => ?_) s1 hfr1
        rw [retHook_mem]
        exact execFrozen_write64 (execFrozen_write64 hfr2 _ _) _ _

private theorem execFrozen_libcruxHmacHookMallocng
    (mpl : Obj.MultiPlacement) (F : ShaState → List (BitVec 8) → ShaState)
    (s0 : State) (hfr0 : ExecFrozen s0.mem) :
    ExecFrozen (libcruxHmacHookMallocng mpl F s0).mem := by
  unfold libcruxHmacHookMallocng
  split
  · exact hfr0
  · dsimp only
    split
    · exact hfr0
    · refine execFrozen_stepRustAlloc1 mpl true _ 64 (fun s1 pKey hfr1 => ?_) s0 hfr0
      refine execFrozen_stepRustAlloc1 mpl false _ 64 (fun s2 pIpad hfr2 => ?_) s1 hfr1
      refine execFrozen_stepRustAlloc1 mpl false _ 64 (fun s3 pOpad hfr3 => ?_) s2 hfr2
      refine execFrozen_stepRustDealloc1 mpl _ pOpad (fun s4 hfr4 => ?_) s3 hfr3
      refine execFrozen_stepRustDealloc1 mpl _ pIpad (fun s5 hfr5 => ?_) s4 hfr4
      refine execFrozen_stepRustDealloc1 mpl _ pKey (fun s6 hfr6 => ?_) s5 hfr5
      refine execFrozen_stepRustAlloc1 mpl false _ 32 (fun s7 _ hfr7 => ?_) s6 hfr6
      rw [retHook_mem]
      exact execFrozen_writeVecHeader (execFrozen_writeBytes hfr7 _ _) _ _ _ _

private theorem tableLookup_mem {tbl : List (String × (State → State))} {sym : String}
    {f : State → State} (h : tbl.lookup sym = some f) :
    (sym, f) ∈ tbl := by
  induction tbl with
  | nil => simp at h
  | cons hd tl ih =>
    rcases hd with ⟨k, g⟩
    simp only [List.lookup] at h
    cases hbeq : (sym == k) with
    | true =>
      rw [hbeq] at h
      injection h with hgf
      subst hgf
      have hsk : sym = k := beq_iff_eq.mp hbeq
      subst hsk
      exact List.Mem.head tl
    | false =>
      rw [hbeq] at h
      exact List.Mem.tail _ (ih h)

private theorem table_cliPqxdhPlaced_execFrozen (mmpl : Obj.MultiPlacement)
    (C : Crypto) (Q : PqxdhPrims) :
    ∀ p ∈ cliPqxdhHookTablePlaced mmpl C Q, ∀ u : State, ExecFrozen u.mem → ExecFrozen (p.2 u).mem := by
  simp only [cliPqxdhHookTablePlaced, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) u hfr
  · unfold compress512Hook; rw [returnToLinkRegister_mem]; exact execFrozen_writeBytes hfr _ _
  · unfold toEdwardsHook; rw [returnToLinkRegister_mem]
    split
    · exact execFrozen_writeBytes (execFrozen_write64 hfr _ _) _ _
    · exact execFrozen_write64 hfr _ _
  · unfold compressHook; rw [returnToLinkRegister_mem]; exact execFrozen_writeBytes hfr _ _
  · unfold edNegHook; rw [returnToLinkRegister_mem]; exact execFrozen_writeBytes hfr _ _
  · unfold torsionFreeHook; exact hfr
  · unfold dsmbHook; rw [returnToLinkRegister_mem]; exact execFrozen_writeBytes hfr _ _
  · unfold scalarModHook; rw [returnToLinkRegister_mem]; exact execFrozen_writeBytes hfr _ _
  · unfold scalarWideHook; rw [returnToLinkRegister_mem]; exact execFrozen_writeBytes hfr _ _
  · unfold kemEncapsHook; rw [returnToLinkRegister_mem]
    exact execFrozen_writeBytes (execFrozen_writeBytes hfr _ _) _ _
  · unfold kemDecapsHook; rw [returnToLinkRegister_mem]; exact execFrozen_writeBytes hfr _ _
  · unfold mlkemFromSeedHook; rw [retHook_mem]; exact execFrozen_writeBytes hfr _ _
  · unfold mlkemPk1Hook; exact hfr
  · unfold mlkemPk2Hook; exact hfr
  · unfold mlkemEncaps1Hook; rw [retHook_mem]; dsimp only
    split
    · exact execFrozen_writeBytes hfr _ _
    · split
      · exact execFrozen_writeBytes (execFrozen_writeBytes (execFrozen_writeBytes hfr _ _) _ _) _ _
      · exact execFrozen_writeBytes hfr _ _
  · unfold mlkemEncaps2Hook; rw [retHook_mem]; exact execFrozen_writeBytes hfr _ _
  · unfold mlkemDecapsHook; rw [retHook_mem]; exact execFrozen_writeBytes hfr _ _
  · unfold mlkemValidatePkHook; exact hfr
  · exact execFrozen_libcruxHmacHookMallocng mmpl C.F u hfr

private theorem table_cliHookTablePlaced_execFrozen (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    ∀ p ∈ cliHookTablePlaced mmpl W, ∀ u : State, ExecFrozen u.mem → ExecFrozen (p.2 u).mem := by
  intro p hp
  unfold cliHookTablePlaced at hp
  rw [List.mem_append] at hp
  rcases hp with hpq | hcli
  · exact table_cliPqxdhPlaced_execFrozen mmpl W.C W.Q p hpq
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hcli
    rcases hcli with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro u hfr; unfold hookMemmove hookMemcpy; rw [retHook_mem]; exact execFrozen_writeBytes hfr _ _
    · intro _ hfr; exact hfr
    · intro u hfr; unfold strlenHook; dsimp only; split <;> exact hfr
    · intro u hfr
      unfold writeFileHook; dsimp only
      split
      · exact hfr
      · split
        · exact hfr
        · split
          · exact hfr
          · split <;> exact hfr
    · intro u hfr; unfold writeStdoutHook; dsimp only; split <;> exact hfr
    · intro u hfr
      unfold memrchrHook; dsimp only
      split
      · exact hfr
      · split <;> exact hfr
    · intro u hfr
      unfold fromUtf8Hook; dsimp only
      split
      · exact hfr
      · split
        · rw [retHook_mem]
          exact execFrozen_write64 (execFrozen_write64 (execFrozen_write64 hfr _ _) _ _) _ _
        · rw [retHook_mem]
          exact execFrozen_write16 (execFrozen_write64 (execFrozen_write64 hfr _ _) _ _) _ _
    · intro _ hfr; exact hfr
    · intro u hfr; unfold formatInnerHook0; rw [retHook_mem]; exact execFrozen_writeVecHeader hfr _ _ _ _
    · intro u hfr
      unfold durationSinceExactHook; dsimp only
      split
      · exact hfr
      · split
        · rw [retHook_mem]
          exact execFrozen_write32 (execFrozen_write64 (execFrozen_write64 hfr _ _) _ _) _ _
        · exact hfr
    · intro u hfr; unfold timeAddHook; dsimp only; split <;> split <;> exact hfr
    · intro _ hfr; exact hfr
    · intro u hfr; unfold compress256Hook; rw [returnToLinkRegister_mem]; exact execFrozen_writeBytes hfr _ _
    · exact execFrozen_aesEncHookMallocng mmpl W.C.E
    · exact execFrozen_aesDecHookMallocng mmpl W.C.D
    · intro u hfr; unfold pubFromSecretHook; rw [retHook_mem]; exact execFrozen_writeBytes hfr _ _
    · intro u hfr; unfold diffieHellmanHook; rw [retHook_mem]; exact execFrozen_writeBytes hfr _ _
    · intro u hfr; unfold zeroizeSecretHook; rw [retHook_mem]; exact execFrozen_writeBytes hfr _ _
    · intro u hfr; unfold zeroizeSecretHook; rw [retHook_mem]; exact execFrozen_writeBytes hfr _ _

/-- Every hook `f` in `cliExternsPlaced mmpl W` (`39` rows + `Rust.panicked`) preserves
    `ExecFrozen` unconditionally. -/
theorem cliExternsPlaced_preserves_execFrozen
    (mmpl : Obj.MultiPlacement) (W : CliHooks)
    {sym : String} {f : State → State}
    (h : cliExternsPlaced mmpl W sym = some f) :
    ∀ u : State, ExecFrozen u.mem → ExecFrozen (f u).mem := by
  unfold cliExternsPlaced at h
  split at h
  · injection h with hrf
    subst hrf
    intro _ hfr; exact hfr
  · exact table_cliHookTablePlaced_execFrozen mmpl W (sym, f) (tableLookup_mem h)

private theorem table_cliPqxdhPlaced_fdsGe3Closed (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    ∀ p ∈ cliPqxdhHookTablePlaced mmpl W.C W.Q,
      (∀ u : State, FdsGe3Closed u.fs → FdsGe3Closed (p.2 u).fs) ∨
        (p.2 = aesEncHookMallocng mmpl W.C.E ∨
         p.2 = aesDecHookMallocng mmpl W.C.D ∨
         p.2 = libcruxHmacHookMallocng mmpl W.C.F) := by
  simp only [cliPqxdhHookTablePlaced, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · exact Or.inl (fun _ hfs => hfs)
  · exact Or.inl (fun _ hfs => hfs)
  · exact Or.inl (fun _ hfs => hfs)
  · exact Or.inl (fun _ hfs => hfs)
  · exact Or.inl (fun _ hfs => hfs)
  · exact Or.inl (fun _ hfs => hfs)
  · exact Or.inl (fun _ hfs => hfs)
  · exact Or.inl (fun _ hfs => hfs)
  · exact Or.inl (fun _ hfs => hfs)
  · exact Or.inl (fun _ hfs => hfs)
  · exact Or.inl (fun _ hfs => hfs)
  · exact Or.inl (fun _ hfs => hfs)
  · exact Or.inl (fun _ hfs => hfs)
  · refine Or.inl (fun u hfs => ?_)
    unfold mlkemEncaps1Hook retHook; dsimp only
    split <;> exact hfs
  · exact Or.inl (fun _ hfs => hfs)
  · exact Or.inl (fun _ hfs => hfs)
  · exact Or.inl (fun _ hfs => hfs)
  · exact Or.inr (Or.inr (Or.inr rfl))

private theorem table_cliHookTablePlaced_fdsGe3Closed (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    ∀ p ∈ cliHookTablePlaced mmpl W,
      (∀ u : State, FdsGe3Closed u.fs → FdsGe3Closed (p.2 u).fs) ∨
        (p.2 = aesEncHookMallocng mmpl W.C.E ∨
         p.2 = aesDecHookMallocng mmpl W.C.D ∨
         p.2 = libcruxHmacHookMallocng mmpl W.C.F) := by
  intro p hp
  unfold cliHookTablePlaced at hp
  rw [List.mem_append] at hp
  rcases hp with hpq | hcli
  · exact table_cliPqxdhPlaced_fdsGe3Closed mmpl W p hpq
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hcli
    rcases hcli with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (fun _ hfs => hfs)
    · exact Or.inl (fun _ hfs => hfs)
    · exact Or.inl (fun u hfs => by unfold strlenHook; dsimp only; split <;> exact hfs)
    · refine Or.inl (fun u hfs => ?_)
      unfold writeFileHook; dsimp only
      split
      · exact hfs
      · split
        · exact hfs
        · split
          · exact hfs
          · split
            · exact hfs
            · exact hfs
            · exact fdsGe3Closed_setFile _ _ hfs
    · exact Or.inl (fun u hfs => by unfold writeStdoutHook; dsimp only; split <;> exact hfs)
    · exact Or.inl (fun u hfs => by
        unfold memrchrHook; dsimp only
        split
        · exact hfs
        · split <;> exact hfs)
    · exact Or.inl (fun u hfs => by
        unfold fromUtf8Hook; dsimp only
        split
        · exact hfs
        · split <;> exact hfs)
    · exact Or.inl (fun _ hfs => hfs)
    · exact Or.inl (fun _ hfs => hfs)
    · exact Or.inl (fun u hfs => by
        unfold durationSinceExactHook; dsimp only
        split
        · exact hfs
        · split <;> exact hfs)
    · exact Or.inl (fun u hfs => by unfold timeAddHook; dsimp only; split <;> split <;> exact hfs)
    · exact Or.inl (fun _ hfs => hfs)
    · exact Or.inl (fun _ hfs => hfs)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inl (fun _ hfs => hfs)
    · exact Or.inl (fun _ hfs => hfs)
    · exact Or.inl (fun _ hfs => hfs)
    · exact Or.inl (fun _ hfs => hfs)

/-- Every hook `f` in `cliExternsPlaced mmpl W` except the `3` `mallocng`-backed crypto hooks
    (`aesEncHookMallocng`, `aesDecHookMallocng`, `libcruxHmacHookMallocng`) preserves `FdsGe3Closed`
    unconditionally. -/
theorem cliExternsPlaced_nonMallocng_preserves_fdsGe3Closed
    (mmpl : Obj.MultiPlacement) (W : CliHooks)
    {sym : String} {f : State → State}
    (h : cliExternsPlaced mmpl W sym = some f) :
    (∀ u : State, FdsGe3Closed u.fs → FdsGe3Closed (f u).fs) ∨
      (f = aesEncHookMallocng mmpl W.C.E ∨
       f = aesDecHookMallocng mmpl W.C.D ∨
       f = libcruxHmacHookMallocng mmpl W.C.F) := by
  unfold cliExternsPlaced at h
  split at h
  · injection h with hrf
    subst hrf
    exact Or.inl (fun _ hfs => hfs)
  · exact table_cliHookTablePlaced_fdsGe3Closed mmpl W (sym, f) (tableLookup_mem h)

/-! ## Block-`617` Seam and Concrete Real-Externs Discharges -/

def Block617TransferFixedHyp
    (mpl mmpl : Obj.MultiPlacement) (ghFixed : CliGhostHooks)
    (CodeOk_ghost CodeOk_real : Memory → Prop)
    (libcAddr brkStart : BitVec 64) (stk : Nat) : Prop :=
  ∀ (W : CliHooks) (Run : Inputs → RunAnswer → Prop),
    (∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok
        (cliProgExtPlacedAt mpl (fun W' => cliGhostExterns ghFixed (cliExternsPlaced mmpl W')) 617 W)
        (mpl.base 617)
        (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk_ghost
          (fineHookRustCliAllocBudget γ mmpl tp brkStart)
          cliBudgetLimits fineCostModel.init stk (cliStaticsPlacedAt mpl) Run cliProcessInputs)) →
    ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok
        (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (mpl.base 617)
        (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk_real
          (fineHookRustCliAllocBudget γ mmpl tp brkStart)
          cliBudgetLimits fineCostModel.init stk (cliStaticsPlacedAt mpl) Run cliProcessInputs)

theorem mainOkCliF3Pq_of_block617TransferFixed
    {mpl mmpl : Obj.MultiPlacement} {ghFixed : CliGhostHooks}
    {CodeOk_ghost CodeOk_real : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {stk : Nat}
    (hTr : Block617TransferFixedHyp mpl mmpl ghFixed CodeOk_ghost CodeOk_real libcAddr brkStart stk)
    (hGhost : MainOkCliExtPqB2NeedLocksPlacedAt mpl mmpl
      (fun W => cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) 617 cliProcessInputs
      CodeOk_ghost libcAddr brkStart stk cliBudgetLimits) :
    MainOkCliF3PqB2NeedLocksPlacedAt mpl mmpl CodeOk_real libcAddr brkStart stk := by
  intro hDropNz X W
  obtain ⟨Run, hmainW, hclauses⟩ := hGhost hDropNz X W
  exact ⟨Run, hTr W Run hmainW, hclauses⟩

theorem mainOkCliF3Over_of_block617TransferFixed
    {mpl mmpl : Obj.MultiPlacement} {ghFixed : CliGhostHooks}
    {CodeOk_ghost CodeOk_real : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {stk : Nat}
    (hTr : Block617TransferFixedHyp mpl mmpl ghFixed CodeOk_ghost CodeOk_real libcAddr brkStart stk)
    (hGhost : MainOkCliExtOverB2NeedLocksPlacedAt mpl mmpl
      (fun W => cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) 617 cliProcessInputs
      CodeOk_ghost libcAddr brkStart stk cliBudgetLimits) :
    MainOkCliF3OverB2NeedLocksPlacedAt mpl mmpl CodeOk_real libcAddr brkStart stk := by
  intro hDropNz X W
  obtain ⟨Run, hmainW, hclauses⟩ := hGhost hDropNz X W
  exact ⟨Run, hTr W Run hmainW, hclauses⟩

/-- Discharge `Block617TransferFixedHyp` from `GhostExternReplaysOn` (`InvMem` + `PredFs` form)
under `CodeOk_real → CodeOk_ghost`. -/
theorem block617TransferFixed_of_replaysOn
    {mpl mmpl : Obj.MultiPlacement} {ghFixed : CliGhostHooks}
    {CodeOk_ghost CodeOk_real : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {stk : Nat}
    (keep : BitVec 64 → Bool) (InvMem : Memory → Prop) (PredFs : FsState → Prop)
    (hCode : ∀ m : Memory, CodeOk_real m → CodeOk_ghost m)
    (hGhostCL : ∀ (W : CliHooks) (m : Memory), CodeOk_ghost m →
      (cliProgExtPlacedAt mpl (fun W' => cliGhostExterns ghFixed (cliExternsPlaced mmpl W')) 617 W).CodeLoaded m)
    (hFr0 : ∀ m : Memory, CodeOk_real m → ExecFrozen m)
    (hInv0 : ∀ m : Memory, CodeOk_real m → InvMem m)
    (hInvStable : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    (hFs0 : ∀ i : Inputs, PredFs (initFsState (cliProcessInputs i)))
    (hTraj : ∀ (W : CliHooks) (i : Inputs) (s0 sf : State),
      let P_ghost := cliProgExtPlacedAt mpl (fun W' => cliGhostExterns ghFixed (cliExternsPlaced mmpl W')) 617 W
      let P_real := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W
      CodeOk_real s0.mem →
      s0.pc = mpl.base 617 →
      s0.fs = initFsState (cliProcessInputs i) →
      s0.trace = [] →
      Steps P_ghost s0 sf →
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
    Block617TransferFixedHyp mpl mmpl ghFixed CodeOk_ghost CodeOk_real libcAddr brkStart stk := by
  intro W Run hGhostOk γ tp
  refine subroutine_ok_transfer_ghostS (keep := keep) (InvMem := InvMem) (PredFs := PredFs)
    rfl rfl
    (blockProgram_cliGhostExterns_no_new_hooks libsignalSessionLib mpl 617 ghFixed (cliExternsPlaced mmpl W))
    hInvStable ?_ ?_ (hGhostOk γ tp)
  · intro g R s0 hm hpc _ _
    dsimp only [b2MainSpecTightNeedLocksFineAt] at hm ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    obtain ⟨⟨hReal0, hCase, hInpOk, hEntry, hStk⟩, hm_frame⟩ := hm
    have hGhost0 : CodeOk_ghost s0.mem := hCode s0.mem hReal0
    have hFsInit : PredFs s0.fs := hEntry.2.1 ▸ hFs0 g.i
    refine ⟨⟨⟨hGhost0, hCase, hInpOk, hEntry, hStk⟩, hm_frame⟩,
      hGhostCL W s0.mem hGhost0, hFr0 s0.mem hReal0, hInv0 s0.mem hReal0, hFsInit, ?_⟩
    intro sf hsteps hout
    have hnoex : ∀ msg, sf.status ≠ .Exception msg := by
      intro msg hex
      rcases hout with ⟨⟨_, _, hr⟩, _, _⟩ | ⟨hp, _⟩ | ⟨_, he, _⟩ | ⟨ho, _⟩
      · rw [hex] at hr; cases hr
      · rw [hex] at hp; cases hp
      · rw [hex] at he; cases he
      · rw [hex] at ho; cases ho
    have hnhalt : sf.status ≠ .Halted := subroutineOutcome_not_halted hout
    exact hTraj W g.i s0 sf hReal0 hpc hEntry.2.1 hEntry.2.2 hsteps hnoex hnhalt
  · intro g R s0 sf _ _ _ hout
    exact hout

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

/-- `FdsGe3Closed`-specialized discharge of `Block617TransferFixedHyp`, reducing real-row
obligations on `cliExternsPlaced mmpl W` to the active `ghFixed` per-symbol replay obligations and
trajectory `lr`, `mallocng`-`fs`, and `svc` guards. -/
theorem block617TransferFixed_of_ghostHooks
    {mpl mmpl : Obj.MultiPlacement} {ghFixed : CliGhostHooks}
    {CodeOk_ghost CodeOk_real : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {stk : Nat}
    (keep : BitVec 64 → Bool) (InvMem : Memory → Prop)
    (hPl : libsignalSessionLib.Placeable mpl)
    (hCode : ∀ m : Memory, CodeOk_real m → CodeOk_ghost m)
    (hGhostCL : ∀ (W : CliHooks) (m : Memory), CodeOk_ghost m →
      (cliProgExtPlacedAt mpl (fun W' => cliGhostExterns ghFixed (cliExternsPlaced mmpl W')) 617 W).CodeLoaded m)
    (hFr0 : ∀ m : Memory, CodeOk_real m → ExecFrozen m)
    (hInv0 : ∀ m : Memory, CodeOk_real m → InvMem m)
    (hInvStable : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    (hRealNone : ∀ (W : CliHooks) (sym : String) (f : State → State),
      GhostSymActive ghFixed sym f →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl sym) = none)
    (hGhostReplay : ∀ (W : CliHooks) (sym : String) (f : State → State),
      GhostSymActive ghFixed sym f →
      ∀ u : State,
        u.pc = libsignalSessionLib.resolve mpl sym →
        u.status = .Running →
        (∀ msg, (f u).status ≠ .Exception msg) →
        u.mem.KeepsFrozen (f u).mem →
        ExecFrozen u.mem →
        keep (u.readReg64 .lr) = false →
        InvMem u.mem →
        FdsGe3Closed u.fs →
        Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u (f u) ∧
        ExecFrozen (f u).mem ∧
        FdsGe3Closed (f u).fs)
    (hMallocngFds : ∀ (W : CliHooks) (i : Inputs) (s0 sf u : State) (f : State → State),
      let P_ghost := cliProgExtPlacedAt mpl (fun W' => cliGhostExterns ghFixed (cliExternsPlaced mmpl W')) 617 W
      CodeOk_real s0.mem →
      s0.pc = mpl.base 617 →
      s0.fs = initFsState (cliProcessInputs i) →
      s0.trace = [] →
      Steps P_ghost s0 u →
      Steps P_ghost (f u) sf →
      (∀ msg, sf.status ≠ .Exception msg) →
      sf.status ≠ .Halted →
      u.status = .Running →
      (f = aesEncHookMallocng mmpl W.C.E ∨
       f = aesDecHookMallocng mmpl W.C.D ∨
       f = libcruxHmacHookMallocng mmpl W.C.F) →
      ExecFrozen u.mem →
      InvMem u.mem →
      FdsGe3Closed u.fs →
      FdsGe3Closed (f u).fs)
    (hSvcFds : ∀ (W : CliHooks) (i : Inputs) (s0 sf u : State),
      let P_ghost := cliProgExtPlacedAt mpl (fun W' => cliGhostExterns ghFixed (cliExternsPlaced mmpl W')) 617 W
      CodeOk_real s0.mem →
      s0.pc = mpl.base 617 →
      s0.fs = initFsState (cliProcessInputs i) →
      s0.trace = [] →
      Steps P_ghost s0 u →
      Steps P_ghost (Syscall.standard u) sf →
      (∀ msg, sf.status ≠ .Exception msg) →
      sf.status ≠ .Halted →
      u.status = .Running →
      P_ghost.externAt? u.pc = none →
      P_ghost.fetchMem u.mem u.pc = some (.system false 0#16) →
      ExecFrozen u.mem →
      InvMem u.mem →
      FdsGe3Closed u.fs →
      FdsGe3Closed (Syscall.standard u).fs)
    (hLrCalls : ∀ (W : CliHooks) (i : Inputs) (s0 sf u : State),
      let P_ghost := cliProgExtPlacedAt mpl (fun W' => cliGhostExterns ghFixed (cliExternsPlaced mmpl W')) 617 W
      let P_real := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W
      CodeOk_real s0.mem →
      s0.pc = mpl.base 617 →
      s0.fs = initFsState (cliProcessInputs i) →
      s0.trace = [] →
      Steps P_ghost s0 u →
      Steps P_ghost u sf →
      (∀ msg, sf.status ≠ .Exception msg) →
      sf.status ≠ .Halted →
      u.status = .Running →
      P_ghost.externAt? u.pc ≠ P_real.externAt? u.pc →
      keep (u.readReg64 .lr) = false) :
    Block617TransferFixedHyp mpl mmpl ghFixed CodeOk_ghost CodeOk_real libcAddr brkStart stk := by
  refine block617TransferFixed_of_replaysOn keep InvMem FdsGe3Closed
    hCode hGhostCL hFr0 hInv0 hInvStable
    (fun i => fdsGe3Closed_initFsState (cliProcessInputs i)) ?_
  intro W i s0 sf
  dsimp only
  intro hReal0 hpc0 hfs0 htr0 hsteps hnoex hnhalt
  refine ⟨?_, ?_, ?_⟩
  · intro pc f heg
    have h617 : 617 < libsignalSessionLib.blocks.length := by decide
    rcases blockProgram_cliGhostExterns_externAt?_cases h617 hPl ghFixed (cliExternsPlaced mmpl W) heg with
      her | ⟨sym, hAct, hpc_eq⟩
    · obtain ⟨sym, hsym⟩ := blockProgram_externAt?_some_exists her
      refine Or.inl ⟨her, fun u hpre hpost _ hrun _ hkf hfr ⟨hinv, hfs⟩ => ?_⟩
      refine ⟨cliExternsPlaced_preserves_execFrozen mmpl W hsym u hfr,
        hInvStable u.mem _ hinv hkf, ?_⟩
      rcases cliExternsPlaced_nonMallocng_preserves_fdsGe3Closed mmpl W hsym with hpres | hmal
      · exact hpres u hfs
      · exact hMallocngFds W i s0 sf u f hReal0 hpc0 hfs0 htr0 hpre hpost hnoex hnhalt hrun hmal hfr hinv hfs
    · refine Or.inr ⟨hpc_eq ▸ hRealNone W sym f hAct,
        fun u _ _ hpc hrun hnoex_fu hkf hfr hlr ⟨hinv, hfs⟩ => ?_⟩
      obtain ⟨hst_r, hfr', hfs'⟩ :=
        hGhostReplay W sym f hAct u (hpc.trans hpc_eq) hrun hnoex_fu hkf hfr hlr hinv hfs
      exact ⟨hst_r, hfr', hInvStable u.mem _ hinv hkf, hfs'⟩
  · intro z hpre hrest hrun heg hfm hfr hinv hfs
    exact hSvcFds W i s0 sf z hReal0 hpc0 hfs0 htr0 hpre hrest hnoex hnhalt hrun heg hfm hfr hinv hfs
  · intro z hpre hrest hrun hne
    exact hLrCalls W i s0 sf z hReal0 hpc0 hfs0 htr0 hpre hrest hnoex hnhalt hrun hne

end LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer

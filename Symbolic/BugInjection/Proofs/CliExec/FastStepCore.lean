/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.Invariant
public import LibsignalBinary.Specifications.SignalSession.CliProcess
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliProcessFixed
public import Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable
public import Symbolic.BugInjection.Proofs.CliExec.RadixMemAux
public import Symbolic.BugInjection.Proofs.CliExec.TreePatch
public import Symbolic.BugInjection.Proofs.CliExec.RadixMem
public import Symbolic.BugInjection.Proofs.CliExec.FastHooksAux
public import Symbolic.BugInjection.Proofs.CliExec.FastHooksRows
public import Symbolic.BugInjection.Proofs.CliExec.FastHooks
public import Symbolic.BugInjection.Proofs.CliExec.CliRunBridge
public import Symbolic.BugInjection.Proofs.CliExec.FastStepInit

/-!
# Fuel-Bounded Fast Stepper and `cliRunAbortOnPanic` Soundness Bridge

Defines single-step, fuel-bounded, and binary-doubling (`2 ^ k`) execution over `FastProg`,
parameterized by an instruction evaluator `evalF` satisfying `EvalSound`. Chains multi-chunk runs
via `FastReachableCoreW` (including the per-chunk decoded-instruction cache `fastRunChunkCachedW`)
and connects computable outcome checks (`checkFastExited`, `checkFastAborted`) to
`cliRunAbortOnPanic`.
-/

@[expose] public section

namespace Symbolic.BugInjection.Proofs.CliExec.FastStepCore

set_option autoImplicit false

open Arm64 Arm64.Memory Arm64.Obj Arm64.Process ProofLib
open CryptoVerification.SignalSession (CliHooks Inputs Outcome OutcomeMatchesProcess cliBase
  cliExternsAbortOnPanic cliProcessInputs cliProgAbortOnPanic cliRunAbortOnPanic cliTokenPatch
  filesOf sigAbrt)
open Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable (compHooks0)
open Symbolic.BugInjection.Proofs.CliExec.RadixMemAux (BinTree Line64 btGet btSet
  btGet_empty btGet_btSet_same' btGet_btSet_ne withForcedBinTree withForcedBinTree_eq)
open Symbolic.BugInjection.Proofs.CliExec.TreePatch (TreePatch applyTreePatch applyLineUpdates)
open Symbolic.BugInjection.Proofs.CliExec.RadixMem (FastMem)
open Symbolic.BugInjection.Proofs.CliExec.FastHooksAux (FastFs fastFsMatchesFilesOf
  fastFsMatchesFilesOf_sound)
open Symbolic.BugInjection.Proofs.CliExec.FastHooksRows (FastState)
open Symbolic.BugInjection.Proofs.CliExec.FastHooks (fastExecExtern fastExecExtern0
  fastExecExtern_exists_sound)
open Symbolic.BugInjection.Proofs.CliExec.CliRunBridge (cliRunAbortOnPanic_eq_some_of_signaled
  cliRunAbortOnPanic_eq_some_of_steps)
open Symbolic.BugInjection.Proofs.CliExec.FastStepInit

export Symbolic.BugInjection.Proofs.CliExec.TreePatch (TreePatch applyTreePatch applyLineUpdates)
export Symbolic.BugInjection.Proofs.CliExec.FastStepInit (progDepth progWordBound progByteBound
  StepEntry FastProg PrebuiltElf buildFastProg buildFastProg0 prebuildElfBaseLines prebuildElf
  prebuildElf0 initFastStateFromBaseProcess initFastStateFromBase FastProgSound
  initFastStateFromBaseProcess_sound initFastStateFromBase_sound)

/-- Agreement preservation of `evalF` against `Program.evalInst` under `Arm64.Syscall.standard`. -/
def EvalSound (evalF : Arm64.Instr → FastState → Option FastState) : Prop :=
  ∀ {prog : Arm64.Program}, prog.svc = Arm64.Syscall.standard →
    ∀ {inst : Arm64.Instr} {fs fs' : FastState} {s : Arm64.State},
      fs.Agrees s → evalF inst fs = some fs' → fs'.Agrees (prog.evalInst inst s)

/-- Execute one step from `fs` by looking up `(fs.pc - cliBase) / 4` in `fp` and dispatching to
`evalF` or `fastExecExtern W`. -/
def fastStepCoreW (W : CliHooks) (evalF : Arm64.Instr → FastState → Option FastState)
    (fp : FastProg) (fs : FastState) : Option FastState :=
  match fs.status with
  | .Running =>
    let off := (fs.pc - cliBase).toNat
    if Nat.beq (Nat.mod off 4) 0 && Nat.blt (Nat.div off 4) progWordBound then
      match lookupStepEntry fp (Nat.div off 4) with
      | .instr inst => evalF inst fs
      | .hook name  => fastExecExtern W name fs
      | .unmapped   => none
    else
      none
  | _ => none

abbrev fastStepCore :
    (Arm64.Instr → FastState → Option FastState) → FastProg → FastState → Option FastState :=
  fastStepCoreW compHooks0

/-- `fastStepCoreW` simulates one `Arm64.Step` and preserves `FastState.Agrees` and
`m0.KeepsFrozen`. -/
theorem fastStepCoreW_sound
    {W : CliHooks} {li : LinkedImage} {evalF : Arm64.Instr → FastState → Option FastState}
    {fp : FastProg} {m0 : Memory} {fs fs' : FastState} {s : State}
    (heval : EvalSound evalF)
    (hfp : FastProgSound W li fp m0)
    (hag : fs.Agrees s)
    (hkf : m0.KeepsFrozen s.mem)
    (hstep : fastStepCoreW W evalF fp fs = some fs') :
    ∃ s' : State,
      Step (li.toProgram.rebase cliBase (cliExternsAbortOnPanic W)) s s' ∧
      fs'.Agrees s' ∧
      m0.KeepsFrozen s'.mem := by
  unfold fastStepCoreW at hstep
  cases hst : fs.status <;> rw [hst] at hstep
  · dsimp only at hstep
    have hmod_eq : ∀ x, Nat.mod x 4 = x % 4 := fun _ => rfl
    have hdiv_eq : ∀ x, Nat.div x 4 = x / 4 := fun _ => rfl
    rw [hag.pc, hmod_eq, hdiv_eq] at hstep
    have h_run : s.status = .Running := hag.status.symm.trans hst
    split at hstep; swap; · nomatch hstep
    rename_i hcond
    simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at hcond
    rcases hcond with ⟨hmod4, hlt⟩
    have hspec := hfp s.pc s.mem hkf hmod4 hlt
    cases hget : lookupStepEntry fp ((s.pc - cliBase).toNat / 4) with
    | unmapped => rw [hget] at hstep; nomatch hstep
    | instr inst =>
      rw [hget] at hstep hspec
      set prog := li.toProgram.rebase cliBase (cliExternsAbortOnPanic W)
      have hsem : Step prog s (prog.evalInst inst s) := Step.exec h_run hspec
      have hsvc : prog.svc = Arm64.Syscall.standard := rfl
      exact ⟨prog.evalInst inst s, hsem, heval hsvc hag hstep, hkf.trans hsem.keepsFrozen⟩
    | hook name =>
      rw [hget] at hstep hspec
      obtain ⟨h, hext, hag', hkeep, hsym⟩ := fastExecExtern_exists_sound hag hstep
      have hsem : Step (li.toProgram.rebase cliBase (cliExternsAbortOnPanic W)) s (h s) :=
        Step.extern h_run (hspec h hext) hkeep hsym
      exact ⟨h s, hsem, hag', hkf.trans hkeep⟩
  all_goals nomatch hstep

theorem fastStepCore_sound
    {li : LinkedImage} {evalF : Arm64.Instr → FastState → Option FastState}
    {fp : FastProg} {m0 : Memory} {fs fs' : FastState} {s : State}
    (heval : EvalSound evalF)
    (hfp : FastProgSound compHooks0 li fp m0)
    (hag : fs.Agrees s)
    (hkf : m0.KeepsFrozen s.mem)
    (hstep : fastStepCore evalF fp fs = some fs') :
    ∃ s' : State,
      Step (li.toProgram.rebase cliBase (cliExternsAbortOnPanic compHooks0)) s s' ∧
      fs'.Agrees s' ∧
      m0.KeepsFrozen s'.mem :=
  fastStepCoreW_sound heval hfp hag hkf hstep

/-- Run up to `fuel` steps under hooks `W`; returns `some fs` immediately once
`fs.status ≠ .Running`. -/
def fastRunStepsCoreW (W : CliHooks) (evalF : Arm64.Instr → FastState → Option FastState) :
    Nat → FastProg → FastState → Option FastState
  | 0, _, fs => some fs
  | fuel + 1, fp, fs =>
    match fs.status with
    | .Running =>
      match fastStepCoreW W evalF fp fs with
      | some fs' => fastRunStepsCoreW W evalF fuel fp fs'
      | none => none
    | _ => some fs

abbrev fastRunStepsCore :
    (Arm64.Instr → FastState → Option FastState) → Nat → FastProg → FastState → Option FastState :=
  fastRunStepsCoreW compHooks0

theorem fastRunStepsCoreW_sound
    {W : CliHooks} {li : LinkedImage} {evalF : Arm64.Instr → FastState → Option FastState}
    {fuel : Nat} {fp : FastProg} {m0 : Memory} {fs fsf : FastState} {s : State}
    (heval : EvalSound evalF)
    (hfp : FastProgSound W li fp m0)
    (hag : fs.Agrees s)
    (hkf : m0.KeepsFrozen s.mem)
    (hrun : fastRunStepsCoreW W evalF fuel fp fs = some fsf) :
    ∃ sf : State,
      Steps (li.toProgram.rebase cliBase (cliExternsAbortOnPanic W)) s sf ∧
      fsf.Agrees sf ∧
      m0.KeepsFrozen sf.mem := by
  induction fuel generalizing fs s with
  | zero =>
    injection hrun with hrun
    subst hrun
    exact ⟨s, .refl s, hag, hkf⟩
  | succ n ih =>
    unfold fastRunStepsCoreW at hrun
    cases hst : fs.status <;> rw [hst] at hrun
    ·
      dsimp only at hrun
      cases hstep : fastStepCoreW W evalF fp fs with
      | none => rw [hstep] at hrun; nomatch hrun
      | some fs' =>
        rw [hstep] at hrun
        obtain ⟨s', hsem1, hag', hkf'⟩ := fastStepCoreW_sound heval hfp hag hkf hstep
        obtain ⟨sf, hsems, hagf, hkff⟩ := ih hag' hkf' hrun
        exact ⟨sf, .step hsem1 hsems, hagf, hkff⟩
    all_goals
      injection hrun with hrun
      subst hrun
      exact ⟨s, .refl s, hag, hkf⟩

theorem fastRunStepsCore_sound
    {li : LinkedImage} {evalF : Arm64.Instr → FastState → Option FastState}
    {fuel : Nat} {fp : FastProg} {m0 : Memory} {fs fsf : FastState} {s : State}
    (heval : EvalSound evalF)
    (hfp : FastProgSound compHooks0 li fp m0)
    (hag : fs.Agrees s)
    (hkf : m0.KeepsFrozen s.mem)
    (hrun : fastRunStepsCore evalF fuel fp fs = some fsf) :
    ∃ sf : State,
      Steps (li.toProgram.rebase cliBase (cliExternsAbortOnPanic compHooks0)) s sf ∧
      fsf.Agrees sf ∧
      m0.KeepsFrozen sf.mem :=
  fastRunStepsCoreW_sound heval hfp hag hkf hrun

private theorem steps_trans {prog : Program} {s1 s2 s3 : State}
    (h1 : Steps prog s1 s2) (h2 : Steps prog s2 s3) : Steps prog s1 s3 := by
  induction h1 with
  | refl _ => exact h2
  | step hs _ ih => exact .step hs (ih h2)

/-- Run up to `2 ^ k` steps at recursion depth `k` under hooks `W`; subtrees short-circuit once
`fs.status ≠ .Running`. -/
def fastRunPow2CoreW (W : CliHooks) (evalF : Arm64.Instr → FastState → Option FastState)
    (fp : FastProg) : Nat → FastState → Option FastState
  | 0, fs =>
    match fs.status with
    | .Running => fastStepCoreW W evalF fp fs
    | _ => some fs
  | k + 1, fs =>
    match fs.status with
    | .Running =>
      match fastRunPow2CoreW W evalF fp k fs with
      | some fs' => fastRunPow2CoreW W evalF fp k fs'
      | none => none
    | _ => some fs

abbrev fastRunPow2Core :
    (Arm64.Instr → FastState → Option FastState) → FastProg → Nat → FastState → Option FastState :=
  fastRunPow2CoreW compHooks0

theorem fastRunPow2CoreW_sound
    {W : CliHooks} {li : LinkedImage} {evalF : Arm64.Instr → FastState → Option FastState}
    {fp : FastProg} {k : Nat} {m0 : Memory} {fs fsf : FastState} {s : State}
    (heval : EvalSound evalF)
    (hfp : FastProgSound W li fp m0)
    (hag : fs.Agrees s)
    (hkf : m0.KeepsFrozen s.mem)
    (hrun : fastRunPow2CoreW W evalF fp k fs = some fsf) :
    ∃ sf : State,
      Steps (li.toProgram.rebase cliBase (cliExternsAbortOnPanic W)) s sf ∧
      fsf.Agrees sf ∧
      m0.KeepsFrozen sf.mem := by
  induction k generalizing fs fsf s with
  | zero =>
    unfold fastRunPow2CoreW at hrun
    cases hst : fs.status <;> rw [hst] at hrun
    · obtain ⟨s', hsem1, hag', hkf'⟩ := fastStepCoreW_sound heval hfp hag hkf hrun
      exact ⟨s', .step hsem1 (.refl s'), hag', hkf'⟩
    all_goals
      injection hrun with hrun
      subst hrun
      exact ⟨s, .refl s, hag, hkf⟩
  | succ n ih =>
    unfold fastRunPow2CoreW at hrun
    cases hst : fs.status <;> rw [hst] at hrun
    · dsimp only at hrun
      cases hmid : fastRunPow2CoreW W evalF fp n fs with
      | none => rw [hmid] at hrun; nomatch hrun
      | some fs' =>
        rw [hmid] at hrun
        obtain ⟨s', hst1, hag', hkf'⟩ := ih hag hkf hmid
        obtain ⟨sf, hst2, hagf, hkff⟩ := ih hag' hkf' hrun
        exact ⟨sf, steps_trans hst1 hst2, hagf, hkff⟩
    all_goals
      injection hrun with hrun
      subst hrun
      exact ⟨s, .refl s, hag, hkf⟩

/-- Multi-chunk reachability relation generated by `fastRunStepsCoreW` and `fastRunPow2CoreW` runs. -/
inductive FastReachableCoreW (W : CliHooks)
    (evalF : Arm64.Instr → FastState → Option FastState) (fp : FastProg) :
    FastState → FastState → Prop where
  | refl (fs : FastState) : FastReachableCoreW W evalF fp fs fs
  | chunk {fs1 fs2 : FastState} (fuel : Nat)
      (h : fastRunStepsCoreW W evalF fuel fp fs1 = some fs2) :
      FastReachableCoreW W evalF fp fs1 fs2
  | pow2 {fs1 fs2 : FastState} (k : Nat)
      (h : fastRunPow2CoreW W evalF fp k fs1 = some fs2) :
      FastReachableCoreW W evalF fp fs1 fs2
  | trans {fs1 fs2 fs3 : FastState}
      (h1 : FastReachableCoreW W evalF fp fs1 fs2)
      (h2 : FastReachableCoreW W evalF fp fs2 fs3) :
      FastReachableCoreW W evalF fp fs1 fs3

abbrev FastReachableCore :
    (Arm64.Instr → FastState → Option FastState) → FastProg → FastState → FastState → Prop :=
  FastReachableCoreW compHooks0

theorem FastReachableCoreW.sound
    {W : CliHooks} {li : LinkedImage} {evalF : Arm64.Instr → FastState → Option FastState}
    {fp : FastProg} {m0 : Memory} {fs0 fsf : FastState} {s0 : State}
    (hreach : FastReachableCoreW W evalF fp fs0 fsf)
    (heval : EvalSound evalF)
    (hfp : FastProgSound W li fp m0)
    (hag : fs0.Agrees s0)
    (hkf : m0.KeepsFrozen s0.mem) :
    ∃ sf : State,
      Steps (li.toProgram.rebase cliBase (cliExternsAbortOnPanic W)) s0 sf ∧
      fsf.Agrees sf ∧
      m0.KeepsFrozen sf.mem := by
  induction hreach generalizing s0 with
  | refl _ => exact ⟨s0, .refl s0, hag, hkf⟩
  | chunk fuel hrun => exact fastRunStepsCoreW_sound heval hfp hag hkf hrun
  | pow2 k hrun => exact fastRunPow2CoreW_sound heval hfp hag hkf hrun
  | trans _ _ ih1 ih2 =>
    obtain ⟨sm, hst1, hagm, hkfm⟩ := ih1 hag hkf
    obtain ⟨sf, hst2, hagf, hkff⟩ := ih2 hagm hkfm
    exact ⟨sf, steps_trans hst1 hst2, hagf, hkff⟩

def isExitedWith (st : ExecStatus) (code : BitVec 64) : Bool :=
  match st with
  | .Exited c => c == code
  | _ => false

def isSignaledWith (st : ExecStatus) (sig : BitVec 7) : Bool :=
  match st with
  | .Signaled s => s == sig
  | _ => false

/-- Check that `fs` terminated with `.Exited expectedCode`, `expectedStdout`, and
`filesOf expectedFiles`. -/
def checkFastExited (fs : FastState) (expectedCode : BitVec 64)
    (expectedStdout : List (BitVec 8))
    (expectedFiles : List (String × List (BitVec 8))) : Bool :=
  isExitedWith fs.status expectedCode &&
  ProcessOutcome.traceStreamBytes .stdout fs.trace == expectedStdout &&
  fastFsMatchesFilesOf fs.fs expectedFiles

def checkFastExited0 (fs : FastState) (expectedStdout : List (BitVec 8))
    (expectedFiles : List (String × List (BitVec 8))) : Bool :=
  checkFastExited fs 0#64 expectedStdout expectedFiles

def checkFastAborted (fs : FastState) : Bool :=
  isSignaledWith fs.status sigAbrt

theorem checkFastExited_sound
    {fs : FastState} {sf : State} {code : BitVec 64}
    {expectedStdout : List (BitVec 8)} {expectedFiles : List (String × List (BitVec 8))}
    (hag : fs.Agrees sf)
    (hchk : checkFastExited fs code expectedStdout expectedFiles = true) :
    sf.status = .Exited code ∧
      OutcomeMatchesProcess
        (.exited (code.toNat % 256) expectedStdout (filesOf expectedFiles))
        (ProcessOutcome.ofState code sf) := by
  unfold checkFastExited at hchk
  simp only [Bool.and_eq_true] at hchk
  rcases hchk with ⟨⟨hexit, hstdout⟩, hfiles⟩
  have hst : sf.status = .Exited code := by
    rw [← hag.status]
    cases h : fs.status <;> simp [isExitedWith, h] at hexit
    exact congrArg ExecStatus.Exited hexit
  have hout_eq : ProcessOutcome.traceStreamBytes .stdout sf.trace = expectedStdout := by
    rw [← hag.trace]
    exact eq_of_beq hstdout
  have hfs_eq : CryptoVerification.SignalSession.fsView sf.fs = filesOf expectedFiles :=
    fastFsMatchesFilesOf_sound hag.fs hfiles
  exact ⟨hst, rfl, rfl, hout_eq, hfs_eq⟩

theorem checkFastExited0_sound
    {fs : FastState} {sf : State}
    {expectedStdout : List (BitVec 8)} {expectedFiles : List (String × List (BitVec 8))}
    (hag : fs.Agrees sf)
    (hchk : checkFastExited0 fs expectedStdout expectedFiles = true) :
    sf.status = .Exited 0#64 ∧
      OutcomeMatchesProcess
        (.exited 0 expectedStdout (filesOf expectedFiles))
        (ProcessOutcome.ofState 0#64 sf) :=
  checkFastExited_sound hag hchk

theorem checkFastAborted_sound
    {fs : FastState} {sf : State}
    (hag : fs.Agrees sf)
    (hchk : checkFastAborted fs = true) :
    sf.status = .Signaled sigAbrt ∧
      OutcomeMatchesProcess .aborted (ProcessOutcome.ofSignal sigAbrt sf) := by
  unfold checkFastAborted at hchk
  have hst : sf.status = .Signaled sigAbrt := by
    rw [← hag.status]
    cases h : fs.status <;> simp [isSignaledWith, h] at hchk
    exact congrArg ExecStatus.Signaled hchk
  exact ⟨hst, rfl, rfl⟩

/-- End-to-end `.exited` soundness of `FastReachableCoreW` for any `elf` validated by `prebuildElf`. -/
theorem cliRunAbortOnPanic_of_fastReachableCoreW_exited
    {W : CliHooks} {evalF : Arm64.Instr → FastState → Option FastState}
    {elf : ElfImage} {pb : PrebuiltElf} {inp : Inputs} {fs0 fsf : FastState}
    {code : BitVec 64} {outStdout : List (BitVec 8)} {outFiles : List (String × List (BitVec 8))}
    (heval : EvalSound evalF)
    (hpb : prebuildElf W CryptoVerification.libsignalSessionImage elf = some pb)
    (hinit : initFastStateFromBase elf pb inp = some fs0)
    (hreach : FastReachableCoreW W evalF pb.prog fs0 fsf)
    (hchk : checkFastExited fsf code outStdout outFiles = true) :
    cliRunAbortOnPanic elf W inp =
      some (.exited (code.toNat % 256) outStdout (filesOf outFiles)) := by
  obtain ⟨s0, hload, hag0, hfp⟩ := initFastStateFromBase_sound hpb hinit
  obtain ⟨sf, hsteps, hagf, _⟩ :=
    hreach.sound heval hfp hag0 (Memory.KeepsFrozen.refl (cliTokenPatch s0).mem)
  obtain ⟨hst, hout⟩ := checkFastExited_sound hagf hchk
  exact cliRunAbortOnPanic_eq_some_of_steps hload hsteps hst hout

/-- End-to-end `.aborted` (`SIGABRT`) soundness of `FastReachableCoreW` for any `elf` validated by
`prebuildElf`. -/
theorem cliRunAbortOnPanic_of_fastReachableCoreW_aborted
    {W : CliHooks} {evalF : Arm64.Instr → FastState → Option FastState}
    {elf : ElfImage} {pb : PrebuiltElf} {inp : Inputs} {fs0 fsf : FastState}
    (heval : EvalSound evalF)
    (hpb : prebuildElf W CryptoVerification.libsignalSessionImage elf = some pb)
    (hinit : initFastStateFromBase elf pb inp = some fs0)
    (hreach : FastReachableCoreW W evalF pb.prog fs0 fsf)
    (hchk : checkFastAborted fsf = true) :
    cliRunAbortOnPanic elf W inp = some .aborted := by
  obtain ⟨s0, hload, hag0, hfp⟩ := initFastStateFromBase_sound hpb hinit
  obtain ⟨sf, hsteps, hagf, _⟩ :=
    hreach.sound heval hfp hag0 (Memory.KeepsFrozen.refl (cliTokenPatch s0).mem)
  obtain ⟨hst, hout⟩ := checkFastAborted_sound hagf hchk
  exact cliRunAbortOnPanic_eq_some_of_signaled hload hsteps hst hout

theorem cliRunAbortOnPanic_of_fastReachableCore_anyElf
    {evalF : Arm64.Instr → FastState → Option FastState}
    {elf : ElfImage} {pb : PrebuiltElf} {inp : Inputs} {fs0 fsf : FastState}
    {outStdout : List (BitVec 8)} {outFiles : List (String × List (BitVec 8))}
    (heval : EvalSound evalF)
    (hpb : prebuildElf compHooks0 CryptoVerification.libsignalSessionImage elf = some pb)
    (hinit : initFastStateFromBase elf pb inp = some fs0)
    (hreach : FastReachableCore evalF pb.prog fs0 fsf)
    (hchk : checkFastExited0 fsf outStdout outFiles = true) :
    cliRunAbortOnPanic elf compHooks0 inp = some (.exited 0 outStdout (filesOf outFiles)) :=
  cliRunAbortOnPanic_of_fastReachableCoreW_exited heval hpb hinit hreach hchk

/-- Insert `e : StepEntry` into `ic` after forcing `e` to constructor WHNF. -/
def btSetStep (ic : BinTree StepEntry) (idx : Nat) (e : StepEntry) : BinTree StepEntry :=
  match e with
  | .instr i => btSet progDepth ic idx (.instr i)
  | .hook nm => btSet progDepth ic idx (.hook nm)
  | .unmapped => btSet progDepth ic idx .unmapped

private theorem btSetStep_eq (ic : BinTree StepEntry) (idx : Nat) (e : StepEntry) :
    btSetStep ic idx e = btSet progDepth ic idx e := by
  cases e <;> rfl

/-- Every entry present in `ic` agrees with `lookupStepEntry fp`. -/
def ICacheSound (fp : FastProg) (ic : BinTree StepEntry) : Prop :=
  ∀ idx < progWordBound, ∀ e, btGet progDepth ic idx = some e → lookupStepEntry fp idx = e

theorem icacheSound_empty (fp : FastProg) : ICacheSound fp .empty := by
  intro _ _ _ h
  rw [btGet_empty] at h
  nomatch h

/-- Execute one step using `ic` as an on-demand `StepEntry` cache so repeated PCs within a chunk are
decoded only once. -/
def fastStepCachedCoreW (W : CliHooks) (evalF : Arm64.Instr → FastState → Option FastState)
    (fp : FastProg) (ic : BinTree StepEntry) (fs : FastState) :
    Option (BinTree StepEntry × FastState) :=
  match fs.status with
  | .Running =>
    let off := (fs.pc - cliBase).toNat
    if Nat.beq (Nat.mod off 4) 0 && Nat.blt (Nat.div off 4) progWordBound then
      let idx := Nat.div off 4
      match btGet progDepth ic idx with
      | some (.instr inst) =>
        match evalF inst fs with
        | some fs' => some (ic, fs')
        | none => none
      | some (.hook name) =>
        match fastExecExtern W name fs with
        | some fs' => some (ic, fs')
        | none => none
      | some .unmapped => none
      | none =>
        let e := lookupStepEntry fp idx
        withForcedBinTree (btSetStep ic idx e) fun ic' =>
          match e with
          | .instr inst =>
            match evalF inst fs with
            | some fs' => some (ic', fs')
            | none => none
          | .hook name =>
            match fastExecExtern W name fs with
            | some fs' => some (ic', fs')
            | none => none
          | .unmapped => none
    else
      none
  | _ => none

theorem fastStepCachedCoreW_eq
    {W : CliHooks} {evalF : Arm64.Instr → FastState → Option FastState}
    {fp : FastProg} {ic ic' : BinTree StepEntry} {fs fs' : FastState}
    (hic : ICacheSound fp ic)
    (h : fastStepCachedCoreW W evalF fp ic fs = some (ic', fs')) :
    ICacheSound fp ic' ∧ fastStepCoreW W evalF fp fs = some fs' := by
  unfold fastStepCachedCoreW at h
  unfold fastStepCoreW
  revert h; cases fs.status <;> intro h
  · dsimp only at h ⊢
    split at h; swap; · nomatch h
    rename_i hcond
    simp only [hcond, ↓reduceIte]
    have hlt : Nat.div (fs.pc - cliBase).toNat 4 < progWordBound := by
      simp only [Bool.and_eq_true, Nat.blt_eq] at hcond; exact hcond.2
    cases hget : btGet progDepth ic (Nat.div (fs.pc - cliBase).toNat 4) with
    | some e =>
      rw [hget] at h
      rw [hic _ hlt e hget]
      cases e with
      | instr inst =>
        dsimp only at h ⊢
        cases hev : evalF inst fs <;> rw [hev] at h
        · nomatch h
        · injection h with hp; injection hp with h1 h2; subst h1 h2; exact ⟨hic, rfl⟩
      | hook name =>
        dsimp only at h ⊢
        cases hev : fastExecExtern W name fs <;> rw [hev] at h
        · nomatch h
        · injection h with hp; injection hp with h1 h2; subst h1 h2; exact ⟨hic, rfl⟩
      | unmapped => nomatch h
    | none =>
      rw [hget] at h
      simp only [withForcedBinTree_eq] at h
      have hic_new : ICacheSound fp (btSetStep ic (Nat.div (fs.pc - cliBase).toNat 4)
          (lookupStepEntry fp (Nat.div (fs.pc - cliBase).toNat 4))) := by
        intro j hj e' hgj
        rw [btSetStep_eq] at hgj
        by_cases hjeq : Nat.div (fs.pc - cliBase).toNat 4 = j
        · subst hjeq
          rw [btGet_btSet_same'] at hgj
          injection hgj
        · rw [btGet_btSet_ne progDepth _ j ic _ hlt hj hjeq] at hgj
          exact hic j hj e' hgj
      cases he : lookupStepEntry fp (Nat.div (fs.pc - cliBase).toNat 4) with
      | instr inst =>
        rw [he] at h hic_new
        dsimp only at h ⊢
        cases hev : evalF inst fs <;> rw [hev] at h
        · nomatch h
        · injection h with hp; injection hp with h1 h2; subst h1 h2; exact ⟨hic_new, rfl⟩
      | hook name =>
        rw [he] at h hic_new
        dsimp only at h ⊢
        cases hev : fastExecExtern W name fs <;> rw [hev] at h
        · nomatch h
        · injection h with hp; injection hp with h1 h2; subst h1 h2; exact ⟨hic_new, rfl⟩
      | unmapped =>
        rw [he] at h; nomatch h
  all_goals nomatch h

def fastRunPow2CachedCoreW (W : CliHooks) (evalF : Arm64.Instr → FastState → Option FastState)
    (fp : FastProg) : Nat → BinTree StepEntry → FastState → Option (BinTree StepEntry × FastState)
  | 0, ic, fs =>
    match fs.status with
    | .Running => fastStepCachedCoreW W evalF fp ic fs
    | _ => some (ic, fs)
  | k + 1, ic, fs =>
    match fs.status with
    | .Running =>
      match fastRunPow2CachedCoreW W evalF fp k ic fs with
      | some (ic1, fs1) => fastRunPow2CachedCoreW W evalF fp k ic1 fs1
      | none => none
    | _ => some (ic, fs)

theorem fastRunPow2CachedCoreW_eq
    {W : CliHooks} {evalF : Arm64.Instr → FastState → Option FastState}
    {fp : FastProg} {k : Nat} {ic ic' : BinTree StepEntry} {fs fsf : FastState}
    (hic : ICacheSound fp ic)
    (h : fastRunPow2CachedCoreW W evalF fp k ic fs = some (ic', fsf)) :
    ICacheSound fp ic' ∧ fastRunPow2CoreW W evalF fp k fs = some fsf := by
  induction k generalizing ic ic' fs fsf with
  | zero =>
    unfold fastRunPow2CachedCoreW at h
    unfold fastRunPow2CoreW
    revert h; cases fs.status <;> intro h
    · exact fastStepCachedCoreW_eq hic h
    all_goals
      dsimp only at h ⊢
      injection h with hp; injection hp with h1 h2; subst h1 h2; exact ⟨hic, rfl⟩
  | succ n ih =>
    unfold fastRunPow2CachedCoreW at h
    unfold fastRunPow2CoreW
    revert h; cases fs.status <;> intro h
    · dsimp only at h ⊢
      cases hmid : fastRunPow2CachedCoreW W evalF fp n ic fs with
      | none => rw [hmid] at h; nomatch h
      | some p =>
        rcases p with ⟨ic1, fs1⟩
        rw [hmid] at h
        obtain ⟨hic1, hr1⟩ := ih hic hmid
        obtain ⟨hic2, hr2⟩ := ih hic1 h
        rw [hr1]; exact ⟨hic2, hr2⟩
    all_goals
      dsimp only at h ⊢
      injection h with hp; injection hp with h1 h2; subst h1 h2; exact ⟨hic, rfl⟩

/-- Run one `2 ^ k`-step chunk with a fresh instruction cache and discard the cache at the chunk
boundary so checkpoints do not retain decoded instructions. -/
def fastRunChunkCachedW (W : CliHooks) (evalF : Arm64.Instr → FastState → Option FastState)
    (fp : FastProg) (k : Nat) (fs : FastState) : Option FastState :=
  match fastRunPow2CachedCoreW W evalF fp k .empty fs with
  | some (_, fs') => some fs'
  | none => none

theorem fastRunChunkCachedW_eq
    {W : CliHooks} {evalF : Arm64.Instr → FastState → Option FastState}
    {fp : FastProg} {k : Nat} {fs fsf : FastState}
    (h : fastRunChunkCachedW W evalF fp k fs = some fsf) :
    fastRunPow2CoreW W evalF fp k fs = some fsf := by
  unfold fastRunChunkCachedW at h
  cases hm : fastRunPow2CachedCoreW W evalF fp k .empty fs with
  | none => rw [hm] at h; nomatch h
  | some p =>
    rcases p with ⟨ic', fs'⟩
    rw [hm] at h; injection h with heq; subst heq
    exact (fastRunPow2CachedCoreW_eq (icacheSound_empty fp) hm).2

end Symbolic.BugInjection.Proofs.CliExec.FastStepCore

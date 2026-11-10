/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import LibsignalBinary.Specifications.SignalSession.CliProcess
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliProcessFixed
public import Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable
public import Symbolic.BugInjection.Proofs.CliExec.RadixMemAux
public import Symbolic.BugInjection.Proofs.CliExec.TreePatch
public import Symbolic.BugInjection.Proofs.CliExec.RadixMem
public import Symbolic.BugInjection.Proofs.CliExec.RadixMemLine
public import Symbolic.BugInjection.Proofs.CliExec.FastHooksAux
public import Symbolic.BugInjection.Proofs.CliExec.FastHooksRows
public import Symbolic.BugInjection.Proofs.CliExec.FastHooks
public import Symbolic.BugInjection.Proofs.CliExec.FastEval
public import Symbolic.BugInjection.Proofs.CliExec.FastStepInit
public import Symbolic.BugInjection.Proofs.CliExec.FastStepCore

/-!
# Concrete CLI Fast Stepper and Single-Call Checkers

Specializes `FastStepCore` to the concrete instruction evaluator `fastEvalInst` and hook
configuration `compHooks0`. Provides fuel-bounded, binary-doubling (`2 ^ k`), and cached chunk
runners, single-call boolean outcome checkers (`checkSingleCallExited0`, `checkSingleCallExited`,
`checkSingleCallAborted`), and `cliRunAbortOnPanic` soundness theorems, along with depth-3
`BinTree` splitting helpers for checkpoint serialization.
-/

@[expose] public section

namespace Symbolic.BugInjection.Proofs.CliExec.FastStep

set_option autoImplicit false

open Arm64 Arm64.Obj Arm64.Process
open CryptoVerification.SignalSession (CliElfCodeMatches CliHooks Inputs Outcome cliBase
  cliExternsAbortOnPanic cliProcessInputs cliRunAbortOnPanic cliTokenPatch filesOf sigAbrt)
open Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable (compHooks0)
open Symbolic.BugInjection.Proofs.CliExec.RadixMemAux (BinTree Line64 loadRegionFast regionToCells
  setCellsAt withForcedBinTree withForcedBinTree_eq)
open Symbolic.BugInjection.Proofs.CliExec.RadixMem (FastMem)
open Symbolic.BugInjection.Proofs.CliExec.RadixMemLine (loadRegionsLines)
open Symbolic.BugInjection.Proofs.CliExec.FastHooksRows (FastState)
open Symbolic.BugInjection.Proofs.CliExec.FastEval (fastEvalInst fastEvalInst_sound)
open Symbolic.BugInjection.Proofs.CliExec.FastStepInit (progDepth progWordBound progByteBound
  StepEntry FastProg PrebuiltElf PrebuildSpec buildFastProg buildFastProg0 buildFastProgWithLens
  checkElfPrebuildOk loadMutantSegments overlayHooks patchTokenFastMem prebuildElfBaseLines
  prebuildMutantElf prebuildMutantElf_sound prebuildElfWithLens prebuildElf
  prebuildElfWithLens_eq_prebuildElf initFastStateFromBaseProcess initFastStateFromBase
  FastProgSound initFastStateFromBaseProcess_sound initFastStateFromBase_sound
  initFastStateFromBase_sound_of_spec)
open Symbolic.BugInjection.Proofs.CliExec.TreePatch (TreePatch applyTreePatch applyLineUpdates)
open Symbolic.BugInjection.Proofs.CliExec.FastStepCore (EvalSound fastStepCoreW fastStepCore
  fastStepCoreW_sound fastStepCore_sound fastRunStepsCoreW fastRunStepsCore
  fastRunStepsCoreW_sound fastRunStepsCore_sound fastRunPow2CoreW fastRunPow2Core
  fastRunPow2CoreW_sound FastReachableCoreW FastReachableCore
  isExitedWith isSignaledWith checkFastExited checkFastExited0 checkFastAborted
  checkFastExited_sound checkFastExited0_sound checkFastAborted_sound
  cliRunAbortOnPanic_of_fastReachableCoreW_exited
  cliRunAbortOnPanic_of_fastReachableCoreW_aborted
  cliRunAbortOnPanic_of_fastReachableCore_anyElf
  fastRunChunkCachedW fastRunChunkCachedW_eq)

export Symbolic.BugInjection.Proofs.CliExec.TreePatch (TreePatch applyTreePatch applyLineUpdates)
export Symbolic.BugInjection.Proofs.CliExec.FastStepInit (progDepth progWordBound progByteBound
  StepEntry FastProg PrebuiltElf buildFastProg buildFastProg0 prebuildElfBaseLines prebuildElf
  initFastStateFromBaseProcess initFastStateFromBase FastProgSound
  initFastStateFromBaseProcess_sound initFastStateFromBase_sound)
export Symbolic.BugInjection.Proofs.CliExec.FastStepCore (EvalSound isExitedWith isSignaledWith
  checkFastExited checkFastExited0 checkFastAborted checkFastExited_sound checkFastExited0_sound
  checkFastAborted_sound)

theorem fastEvalInst_evalSound : EvalSound fastEvalInst := by
  intro _ hsvc _ _ _ _ hag hev
  exact fastEvalInst_sound hsvc hag hev

abbrev prebuildElf0 (li : LinkedImage) (elf : ElfImage) : Option PrebuiltElf :=
  prebuildElf compHooks0 li elf

abbrev fastStep (fp : FastProg) (fs : FastState) : Option FastState :=
  fastStepCore fastEvalInst fp fs

abbrev fastStepW (W : CliHooks) (fp : FastProg) (fs : FastState) : Option FastState :=
  fastStepCoreW W fastEvalInst fp fs

abbrev fastRunSteps (fuel : Nat) (fp : FastProg) (fs : FastState) : Option FastState :=
  fastRunStepsCore fastEvalInst fuel fp fs

abbrev fastRunStepsW (W : CliHooks) (fuel : Nat) (fp : FastProg) (fs : FastState) :
    Option FastState :=
  fastRunStepsCoreW W fastEvalInst fuel fp fs

abbrev FastReachable (fp : FastProg) (fs0 fsf : FastState) : Prop :=
  FastReachableCore fastEvalInst fp fs0 fsf

abbrev FastReachableW (W : CliHooks) (fp : FastProg) (fs0 fsf : FastState) : Prop :=
  FastReachableCoreW W fastEvalInst fp fs0 fsf

theorem FastReachable.refl {fp : FastProg} (fs : FastState) : FastReachable fp fs fs :=
  FastReachableCoreW.refl fs

theorem FastReachable.of_run {fp : FastProg} {fs0 fsf : FastState}
    (fuel : Nat) (h : fastRunSteps fuel fp fs0 = some fsf) :
    FastReachable fp fs0 fsf :=
  FastReachableCoreW.chunk fuel h

theorem FastReachable.trans {fp : FastProg} {fs0 fs1 fsf : FastState}
    (h1 : FastReachable fp fs0 fs1) (h2 : FastReachable fp fs1 fsf) :
    FastReachable fp fs0 fsf :=
  FastReachableCoreW.trans h1 h2

theorem FastReachable.step_chunk {fp : FastProg} {fs0 fs1 fsf : FastState}
    (fuel : Nat) (h1 : fastRunSteps fuel fp fs0 = some fs1)
    (h2 : FastReachable fp fs1 fsf) :
    FastReachable fp fs0 fsf :=
  FastReachableCoreW.trans (FastReachableCoreW.chunk fuel h1) h2

/-- Soundness of `FastReachable` for `.exited 0` outcomes under `compHooks0`. -/
theorem cliRunAbortOnPanic_of_fastReachable
    {elf : ElfImage} {pb : PrebuiltElf} {inp : Inputs} {fs0 fsf : FastState}
    {outStdout : List (BitVec 8)} {outFiles : List (String × List (BitVec 8))}
    (hpb : prebuildElf0 CryptoVerification.libsignalSessionImage elf = some pb)
    (hinit : initFastStateFromBase elf pb inp = some fs0)
    (hreach : FastReachable pb.prog fs0 fsf)
    (hchk : checkFastExited0 fsf outStdout outFiles = true) :
    cliRunAbortOnPanic elf compHooks0 inp = some (.exited 0 outStdout (filesOf outFiles)) :=
  cliRunAbortOnPanic_of_fastReachableCore_anyElf
    fastEvalInst_evalSound hpb hinit hreach hchk

theorem cliRunAbortOnPanic_of_fastReachableW_exited
    {W : CliHooks} {elf : ElfImage} {pb : PrebuiltElf} {inp : Inputs} {fs0 fsf : FastState}
    {code : BitVec 64} {outStdout : List (BitVec 8)} {outFiles : List (String × List (BitVec 8))}
    (hpb : prebuildElf W CryptoVerification.libsignalSessionImage elf = some pb)
    (hinit : initFastStateFromBase elf pb inp = some fs0)
    (hreach : FastReachableW W pb.prog fs0 fsf)
    (hchk : checkFastExited fsf code outStdout outFiles = true) :
    cliRunAbortOnPanic elf W inp =
      some (.exited (code.toNat % 256) outStdout (filesOf outFiles)) :=
  cliRunAbortOnPanic_of_fastReachableCoreW_exited
    fastEvalInst_evalSound hpb hinit hreach hchk

theorem cliRunAbortOnPanic_of_fastReachableW_aborted
    {W : CliHooks} {elf : ElfImage} {pb : PrebuiltElf} {inp : Inputs} {fs0 fsf : FastState}
    (hpb : prebuildElf W CryptoVerification.libsignalSessionImage elf = some pb)
    (hinit : initFastStateFromBase elf pb inp = some fs0)
    (hreach : FastReachableW W pb.prog fs0 fsf)
    (hchk : checkFastAborted fsf = true) :
    cliRunAbortOnPanic elf W inp = some .aborted :=
  cliRunAbortOnPanic_of_fastReachableCoreW_aborted
    fastEvalInst_evalSound hpb hinit hreach hchk

/-- Initialize `FastState` from `pb`, run up to `fuel` steps, and check for `.Exited 0#64` with
`outStdout` and `outFiles`. -/
def checkSingleCallExited0 (elf : ElfImage) (pb : PrebuiltElf) (inp : Inputs)
    (fuel : Nat) (outStdout : List (BitVec 8))
    (outFiles : List (String × List (BitVec 8))) : Bool :=
  match initFastStateFromBase elf pb inp with
  | none => false
  | some fs0 =>
    match fastRunSteps fuel pb.prog fs0 with
    | none => false
    | some fsf => checkFastExited0 fsf outStdout outFiles

/-- Soundness of `checkSingleCallExited0`: a `true` check implies `cliRunAbortOnPanic` returns
`.exited 0 outStdout (filesOf outFiles)`. -/
theorem cliRunAbortOnPanic_of_singleCall
    {elf : ElfImage} {pb : PrebuiltElf} {inp : Inputs} {fuel : Nat}
    {outStdout : List (BitVec 8)} {outFiles : List (String × List (BitVec 8))}
    (hpb : prebuildElf0 CryptoVerification.libsignalSessionImage elf = some pb)
    (hok : checkSingleCallExited0 elf pb inp fuel outStdout outFiles = true) :
    cliRunAbortOnPanic elf compHooks0 inp = some (.exited 0 outStdout (filesOf outFiles)) := by
  unfold checkSingleCallExited0 at hok
  cases hinit : initFastStateFromBase elf pb inp with
  | none => rw [hinit] at hok; nomatch hok
  | some fs0 =>
    rw [hinit] at hok
    dsimp only at hok
    cases hrun : fastRunSteps fuel pb.prog fs0 with
    | none => rw [hrun] at hok; nomatch hok
    | some fsf =>
      rw [hrun] at hok
      exact cliRunAbortOnPanic_of_fastReachable hpb hinit
        (FastReachable.of_run fuel hrun) hok

def checkSingleCallExited (elf : ElfImage) (pb : PrebuiltElf) (inp : Inputs)
    (fuel : Nat) (code : BitVec 64) (outStdout : List (BitVec 8))
    (outFiles : List (String × List (BitVec 8))) : Bool :=
  match initFastStateFromBase elf pb inp with
  | none => false
  | some fs0 =>
    match fastRunSteps fuel pb.prog fs0 with
    | none => false
    | some fsf => checkFastExited fsf code outStdout outFiles

theorem cliRunAbortOnPanic_of_singleCall_exited
    {elf : ElfImage} {pb : PrebuiltElf} {inp : Inputs} {fuel : Nat} {code : BitVec 64}
    {outStdout : List (BitVec 8)} {outFiles : List (String × List (BitVec 8))}
    (hpb : prebuildElf0 CryptoVerification.libsignalSessionImage elf = some pb)
    (hok : checkSingleCallExited elf pb inp fuel code outStdout outFiles = true) :
    cliRunAbortOnPanic elf compHooks0 inp =
      some (.exited (code.toNat % 256) outStdout (filesOf outFiles)) := by
  unfold checkSingleCallExited at hok
  cases hinit : initFastStateFromBase elf pb inp with
  | none => rw [hinit] at hok; nomatch hok
  | some fs0 =>
    rw [hinit] at hok
    dsimp only at hok
    cases hrun : fastRunSteps fuel pb.prog fs0 with
    | none => rw [hrun] at hok; nomatch hok
    | some fsf =>
      rw [hrun] at hok
      exact cliRunAbortOnPanic_of_fastReachableW_exited hpb hinit
        (FastReachable.of_run fuel hrun) hok

def checkSingleCallAborted (elf : ElfImage) (pb : PrebuiltElf) (inp : Inputs)
    (fuel : Nat) : Bool :=
  match initFastStateFromBase elf pb inp with
  | none => false
  | some fs0 =>
    match fastRunSteps fuel pb.prog fs0 with
    | none => false
    | some fsf => checkFastAborted fsf

theorem cliRunAbortOnPanic_of_singleCall_aborted
    {elf : ElfImage} {pb : PrebuiltElf} {inp : Inputs} {fuel : Nat}
    (hpb : prebuildElf0 CryptoVerification.libsignalSessionImage elf = some pb)
    (hok : checkSingleCallAborted elf pb inp fuel = true) :
    cliRunAbortOnPanic elf compHooks0 inp = some .aborted := by
  unfold checkSingleCallAborted at hok
  cases hinit : initFastStateFromBase elf pb inp with
  | none => rw [hinit] at hok; nomatch hok
  | some fs0 =>
    rw [hinit] at hok
    dsimp only at hok
    cases hrun : fastRunSteps fuel pb.prog fs0 with
    | none => rw [hrun] at hok; nomatch hok
    | some fsf =>
      rw [hrun] at hok
      exact cliRunAbortOnPanic_of_fastReachableW_aborted hpb hinit
        (FastReachable.of_run fuel hrun) hok

abbrev fastRunPow2 (fp : FastProg) (k : Nat) (fs : FastState) : Option FastState :=
  fastRunPow2Core fastEvalInst fp k fs

theorem FastReachable.of_pow2 {fp : FastProg} {fs0 fsf : FastState}
    (k : Nat) (h : fastRunPow2 fp k fs0 = some fsf) :
    FastReachable fp fs0 fsf :=
  FastReachableCoreW.pow2 k h

/-- Variant of `checkSingleCallExited0` using `fastRunPow2` (`2 ^ k` step budget). -/
def checkSingleCallPow2Exited0 (elf : ElfImage) (pb : PrebuiltElf) (inp : Inputs)
    (k : Nat) (outStdout : List (BitVec 8))
    (outFiles : List (String × List (BitVec 8))) : Bool :=
  match initFastStateFromBase elf pb inp with
  | none => false
  | some fs0 =>
    match fastRunPow2 pb.prog k fs0 with
    | none => false
    | some fsf => checkFastExited0 fsf outStdout outFiles

theorem cliRunAbortOnPanic_of_singleCallPow2
    {elf : ElfImage} {pb : PrebuiltElf} {inp : Inputs} {k : Nat}
    {outStdout : List (BitVec 8)} {outFiles : List (String × List (BitVec 8))}
    (hpb : prebuildElf0 CryptoVerification.libsignalSessionImage elf = some pb)
    (hok : checkSingleCallPow2Exited0 elf pb inp k outStdout outFiles = true) :
    cliRunAbortOnPanic elf compHooks0 inp = some (.exited 0 outStdout (filesOf outFiles)) := by
  unfold checkSingleCallPow2Exited0 at hok
  cases hinit : initFastStateFromBase elf pb inp with
  | none => rw [hinit] at hok; nomatch hok
  | some fs0 =>
    rw [hinit] at hok
    dsimp only at hok
    cases hrun : fastRunPow2 pb.prog k fs0 with
    | none => rw [hrun] at hok; nomatch hok
    | some fsf =>
      rw [hrun] at hok
      exact cliRunAbortOnPanic_of_fastReachable hpb hinit
        (FastReachable.of_pow2 k hrun) hok

abbrev fastRunChunkCached (fp : FastProg) (k : Nat) (fs : FastState) : Option FastState :=
  fastRunChunkCachedW compHooks0 fastEvalInst fp k fs

theorem FastReachable.of_cachedPow2 {fp : FastProg} {fs0 fsf : FastState}
    (k : Nat) (h : fastRunChunkCached fp k fs0 = some fsf) :
    FastReachable fp fs0 fsf :=
  FastReachable.of_pow2 k (fastRunChunkCachedW_eq h)

/-- Checkpoint constructor parameterized by `(pb, fs0)` so untouched `pb.baseLines`,
`fs0.fs`, `fs0.oracle`, and `fs0.mem.{stackBase,stackTop}` remain unforced. -/
abbrev MkCkpt := PrebuiltElf → FastState → FastState

def ckptInit : MkCkpt := fun _ fs0 => fs0

def extractMutantHooks (li : LinkedImage) : BinTree String :=
  overlayHooks compHooks0 li.stubs .empty

def treeL {α : Type} : BinTree α → BinTree α
  | .branch l _ => l
  | _ => .empty

def treeR {α : Type} : BinTree α → BinTree α
  | .branch _ r => r
  | _ => .empty

def isFullDepth3 {α : Type} : BinTree α → Bool
  | .branch (.branch (.branch _ _) (.branch _ _)) (.branch (.branch _ _) (.branch _ _)) => true
  | _ => false

/-- Extract the depth-3 subtree at index `m < 8` for LSB-first residue `hi % 8 = m`. -/
def treeSub3 {α : Type} (m : Nat) (t : BinTree α) : BinTree α :=
  match m with
  | 0 => treeL (treeL (treeL t))
  | 1 => treeL (treeL (treeR t))
  | 2 => treeL (treeR (treeL t))
  | 3 => treeL (treeR (treeR t))
  | 4 => treeR (treeL (treeL t))
  | 5 => treeR (treeL (treeR t))
  | 6 => treeR (treeR (treeL t))
  | _ => treeR (treeR (treeR t))

/-- Reassemble a depth-3 `BinTree` from its 8 LSB-first residue subtrees `b0..b7` (`hi % 8 = m`). -/
def mkDepth3 {α : Type} (b0 b1 b2 b3 b4 b5 b6 b7 : BinTree α) : BinTree α :=
  .branch
    (.branch (.branch b0 b4) (.branch b2 b6))
    (.branch (.branch b1 b5) (.branch b3 b7))

theorem eq_mkDepth3 {α : Type} {t b0 b1 b2 b3 b4 b5 b6 b7 : BinTree α}
    (hf : isFullDepth3 t = true)
    (h0 : treeSub3 0 t = b0) (h1 : treeSub3 1 t = b1)
    (h2 : treeSub3 2 t = b2) (h3 : treeSub3 3 t = b3)
    (h4 : treeSub3 4 t = b4) (h5 : treeSub3 5 t = b5)
    (h6 : treeSub3 6 t = b6) (h7 : treeSub3 7 t = b7) :
    t = mkDepth3 b0 b1 b2 b3 b4 b5 b6 b7 := by
  cases t with
  | empty => nomatch hf
  | twig _ _ => nomatch hf
  | branch l r =>
    cases l with
    | empty => nomatch hf
    | twig _ _ => nomatch hf
    | branch ll lr =>
      cases ll with
      | empty => nomatch hf
      | twig _ _ => nomatch hf
      | branch _ _ =>
        cases lr with
        | empty => nomatch hf
        | twig _ _ => nomatch hf
        | branch _ _ =>
          cases r with
          | empty => nomatch hf
          | twig _ _ => nomatch hf
          | branch rl rr =>
            cases rl with
            | empty => nomatch hf
            | twig _ _ => nomatch hf
            | branch _ _ =>
              cases rr with
              | empty => nomatch hf
              | twig _ _ => nomatch hf
              | branch _ _ =>
                dsimp only [treeSub3, treeL, treeR] at h0 h1 h2 h3 h4 h5 h6 h7
                subst h0 h1 h2 h3 h4 h5 h6 h7
                rfl

end Symbolic.BugInjection.Proofs.CliExec.FastStep

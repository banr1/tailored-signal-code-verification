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
public import Symbolic.BugInjection.Proofs.CliExec.FastHooksRows
public import Symbolic.BugInjection.Proofs.CliExec.FastStepInit
public import Symbolic.BugInjection.Proofs.CliExec.FastStep

/-!
# Pre-Elaborated ELF Specification and Chunk Execution Bridge

Bridges a parsed `elf : ElfImage` to `cliRunAbortOnPanic elf compHooks0 realInp` through an
image-free pre-elaborated `ElfFullSpec` checkpoint chain (`ElfCkptReachable`). Initial state setup
depends on `elf` only through its five scalar header fields (`initFastStateFromBase_congr`), while
per-chunk execution steps from `headerElfOfFull fs` over `prebuiltOfFull fs`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.CliExec.ElfFullSpec

open Arm64 Arm64.Obj Arm64.Process
open CryptoVerification.SignalSession (Inputs Outcome cliRunAbortOnPanic filesOf)
open Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable (compHooks0)
open Symbolic.BugInjection.Proofs.CliExec.RadixMemAux (BinTree Line64)
open Symbolic.BugInjection.Proofs.CliExec.FastHooksRows (FastState)
open Symbolic.BugInjection.Proofs.CliExec.FastStepInit (PrebuiltElf initFastStateFromBase
  initFastStateFromBaseProcess prebuildElf)
open Symbolic.BugInjection.Proofs.CliExec.FastStep (MkCkpt ckptInit FastReachable fastRunChunkCached
  checkFastExited0 checkFastExited checkFastAborted
  cliRunAbortOnPanic_of_fastReachable cliRunAbortOnPanic_of_fastReachableW_exited
  cliRunAbortOnPanic_of_fastReachableW_aborted treeL treeR isFullDepth3 treeSub3 mkDepth3
  eq_mkDepth3)

export Symbolic.BugInjection.Proofs.CliExec.FastStep (MkCkpt ckptInit treeL treeR isFullDepth3
  treeSub3 mkDepth3 eq_mkDepth3)

set_option linter.dupNamespace false in
/-- Pre-elaborated specification of a parsed `ElfImage` (`entry`, `phdrVaddr`, `phnum`, `brkStart`,
`hooks`, and token-patched `baseLines`) with no `ElfImage` segment byte lists. -/
structure ElfFullSpec where
  entry     : BitVec 64
  phdrVaddr : BitVec 64
  phnum     : Nat
  brkStart  : BitVec 64
  hooks     : BinTree String
  baseLines : BinTree Line64

/-- Header-only `ElfImage` agreeing with `fs` on `(entry, phdrVaddr, phent = 56, phnum, brkStart)`
with empty `segments` and `symbols`. -/
def headerElfOfFull (fs : ElfFullSpec) : ElfImage :=
  { entry := fs.entry
    phdrVaddr := fs.phdrVaddr
    phent := 56
    phnum := fs.phnum
    segments := []
    brkStart := fs.brkStart
    symbols := [] }

def prebuiltOfFull (fs : ElfFullSpec) : PrebuiltElf :=
  { baseLines := fs.baseLines
    prog := { hooks := fs.hooks, rxLines := fs.baseLines } }

/-- Validity of `fs : ElfFullSpec` against `(li, elf)`. -/
def ElfFullValidFor (li : LinkedImage) (elf : ElfImage) (fs : ElfFullSpec) : Prop :=
  prebuildElf compHooks0 li elf = some (prebuiltOfFull fs) ∧
  elf.entry = fs.entry ∧
  elf.phdrVaddr = fs.phdrVaddr ∧
  elf.phent = 56 ∧
  elf.phnum = fs.phnum ∧
  elf.brkStart = fs.brkStart

/-- Validity of `fs : ElfFullSpec` against `elf` and `CryptoVerification.libsignalSessionImage`. -/
def ElfFullValid (elf : ElfImage) (fs : ElfFullSpec) : Prop :=
  prebuildElf compHooks0 CryptoVerification.libsignalSessionImage elf = some (prebuiltOfFull fs) ∧
  elf.entry = fs.entry ∧
  elf.phdrVaddr = fs.phdrVaddr ∧
  elf.phent = 56 ∧
  elf.phnum = fs.phnum ∧
  elf.brkStart = fs.brkStart

private theorem buildInitialStack_congr {e1 e2 : ElfImage} (pinputs : ProcessInputs)
    (hentry : e1.entry = e2.entry) (hphdr : e1.phdrVaddr = e2.phdrVaddr)
    (hphent : e1.phent = e2.phent) (hphnum : e1.phnum = e2.phnum)
    (hbrk : e1.brkStart = e2.brkStart) :
    buildInitialStack e1 pinputs = buildInitialStack e2 pinputs := by
  unfold buildInitialStack
  simp only [hentry, hphdr, hphent, hphnum, hbrk]

/-- `initFastStateFromBase` depends on `elf` only through `(entry, phdrVaddr, phent, phnum, brkStart)`. -/
theorem initFastStateFromBase_congr {e1 e2 : ElfImage} (pb : PrebuiltElf) (inp : Inputs)
    (hentry : e1.entry = e2.entry) (hphdr : e1.phdrVaddr = e2.phdrVaddr)
    (hphent : e1.phent = e2.phent) (hphnum : e1.phnum = e2.phnum)
    (hbrk : e1.brkStart = e2.brkStart) :
    initFastStateFromBase e1 pb inp = initFastStateFromBase e2 pb inp := by
  unfold initFastStateFromBase initFastStateFromBaseProcess
  rw [buildInitialStack_congr _ hentry hphdr hphent hphnum hbrk, hentry, hbrk]

def runElfChunkLHS (fs : ElfFullSpec) (inp : Inputs) (k : Nat) (src : MkCkpt) : Option FastState :=
  let pb := prebuiltOfFull fs
  match initFastStateFromBase (headerElfOfFull fs) pb inp with
  | none => none
  | some fs0 => fastRunChunkCached pb.prog k (src pb fs0)

def runElfChunkRHS (fs : ElfFullSpec) (inp : Inputs) (dst : MkCkpt) : Option FastState :=
  let pb := prebuiltOfFull fs
  match initFastStateFromBase (headerElfOfFull fs) pb inp with
  | none => none
  | some fs0 => some (dst pb fs0)

def checkElfFinalChunkExited0 (fs : ElfFullSpec) (inp : Inputs) (k : Nat) (src : MkCkpt)
    (outStdout : List (BitVec 8)) (outFiles : List (String × List (BitVec 8))) : Bool :=
  let pb := prebuiltOfFull fs
  match initFastStateFromBase (headerElfOfFull fs) pb inp with
  | none => false
  | some fs0 =>
    match fastRunChunkCached pb.prog k (src pb fs0) with
    | none => false
    | some fsf => checkFastExited0 fsf outStdout outFiles

def checkElfFinalChunkExited (fs : ElfFullSpec) (inp : Inputs) (k : Nat) (src : MkCkpt)
    (code : BitVec 64) (outStdout : List (BitVec 8))
    (outFiles : List (String × List (BitVec 8))) : Bool :=
  let pb := prebuiltOfFull fs
  match initFastStateFromBase (headerElfOfFull fs) pb inp with
  | none => false
  | some fs0 =>
    match fastRunChunkCached pb.prog k (src pb fs0) with
    | none => false
    | some fsf => checkFastExited fsf code outStdout outFiles

def checkElfFinalChunkAborted (fs : ElfFullSpec) (inp : Inputs) (k : Nat) (src : MkCkpt) : Bool :=
  let pb := prebuiltOfFull fs
  match initFastStateFromBase (headerElfOfFull fs) pb inp with
  | none => false
  | some fs0 =>
    match fastRunChunkCached pb.prog k (src pb fs0) with
    | none => false
    | some fsf => checkFastAborted fsf

/-- Reachability from the initial fast state `fs0` to `dst (prebuiltOfFull fs) fs0`. -/
def ElfCkptReachable (fs : ElfFullSpec) (inp : Inputs) (dst : MkCkpt) : Prop :=
  ∀ fs0 : FastState,
    initFastStateFromBase (headerElfOfFull fs) (prebuiltOfFull fs) inp = some fs0 →
    FastReachable (prebuiltOfFull fs).prog fs0 (dst (prebuiltOfFull fs) fs0)

theorem ElfCkptReachable.init {fs : ElfFullSpec} {inp : Inputs} :
    ElfCkptReachable fs inp ckptInit :=
  fun fs0 _ => FastReachable.refl fs0

theorem ElfCkptReachable.step {fs : ElfFullSpec} {inp : Inputs} {k : Nat}
    {src dst : MkCkpt}
    (hr : ElfCkptReachable fs inp src)
    (hchunk : runElfChunkLHS fs inp k src = runElfChunkRHS fs inp dst) :
    ElfCkptReachable fs inp dst := by
  intro fs0 hinit
  unfold runElfChunkLHS runElfChunkRHS at hchunk
  dsimp only at hchunk
  rw [hinit] at hchunk; dsimp only at hchunk
  exact FastReachable.trans (hr fs0 hinit) (FastReachable.of_cachedPow2 k hchunk)

private theorem reach_of_elfFinalChunk_aux
    {li : LinkedImage} {elf : ElfImage} {fs : ElfFullSpec} {inp : Inputs}
    {k : Nat} {src : MkCkpt} {checkF : FastState → Bool}
    (hv : ElfFullValidFor li elf fs)
    (hreach : ElfCkptReachable fs inp src)
    (hok : (let pb := prebuiltOfFull fs
            match initFastStateFromBase (headerElfOfFull fs) pb inp with
            | none => false
            | some fs0 =>
              match fastRunChunkCached pb.prog k (src pb fs0) with
              | none => false
              | some fsf => checkF fsf) = true) :
    ∃ (fs0 fsf : FastState),
      prebuildElf compHooks0 li elf = some (prebuiltOfFull fs) ∧
      initFastStateFromBase elf (prebuiltOfFull fs) inp = some fs0 ∧
      FastReachable (prebuiltOfFull fs).prog fs0 fsf ∧
      checkF fsf = true := by
  rcases hv with ⟨hpb, hentry, hphdr, hphent, hphnum, hbrk⟩
  dsimp only at hok
  cases hinit_h : initFastStateFromBase (headerElfOfFull fs) (prebuiltOfFull fs) inp with
  | none => rw [hinit_h] at hok; nomatch hok
  | some fs0 =>
    rw [hinit_h] at hok; dsimp only at hok
    have hinit_e : initFastStateFromBase elf (prebuiltOfFull fs) inp = some fs0 := by
      rw [initFastStateFromBase_congr (e2 := headerElfOfFull fs) _ _
        hentry hphdr hphent hphnum hbrk, hinit_h]
    cases hrun : fastRunChunkCached (prebuiltOfFull fs).prog k (src (prebuiltOfFull fs) fs0) with
    | none => rw [hrun] at hok; nomatch hok
    | some fsf =>
      rw [hrun] at hok
      exact ⟨fs0, fsf, hpb, hinit_e,
        FastReachable.trans (hreach fs0 hinit_h) (FastReachable.of_cachedPow2 k hrun), hok⟩

/-- Transfers an `ElfCkptReachable` chain and final `.exited 0` chunk check onto `cliRunAbortOnPanic`
via `ElfFullValid elf fs`. -/
theorem cliRunAbortOnPanic_of_elfFinalChunk
    {elf : ElfImage} {fs : ElfFullSpec} {realInp fastInp : Inputs} {k : Nat} {src : MkCkpt}
    {realStdout fastStdout : List (BitVec 8)} {outFiles : List (String × List (BitVec 8))}
    (hv : ElfFullValid elf fs)
    (hinp : realInp = fastInp)
    (hstd : realStdout = fastStdout)
    (hreach : ElfCkptReachable fs fastInp src)
    (hok : checkElfFinalChunkExited0 fs fastInp k src fastStdout outFiles = true) :
    cliRunAbortOnPanic elf compHooks0 realInp =
      some (.exited 0 realStdout (filesOf outFiles)) := by
  subst hinp hstd
  obtain ⟨fs0, fsf, hpb, hinit, htot, hchk⟩ := reach_of_elfFinalChunk_aux hv hreach hok
  exact cliRunAbortOnPanic_of_fastReachable hpb hinit htot hchk

theorem cliRunAbortOnPanic_of_elfFinalChunk_exited
    {elf : ElfImage} {fs : ElfFullSpec} {realInp fastInp : Inputs} {k : Nat} {src : MkCkpt}
    {code : BitVec 64} {realStdout fastStdout : List (BitVec 8)}
    {outFiles : List (String × List (BitVec 8))}
    (hv : ElfFullValid elf fs)
    (hinp : realInp = fastInp)
    (hstd : realStdout = fastStdout)
    (hreach : ElfCkptReachable fs fastInp src)
    (hok : checkElfFinalChunkExited fs fastInp k src code fastStdout outFiles = true) :
    cliRunAbortOnPanic elf compHooks0 realInp =
      some (.exited (code.toNat % 256) realStdout (filesOf outFiles)) := by
  subst hinp hstd
  obtain ⟨fs0, fsf, hpb, hinit, htot, hchk⟩ := reach_of_elfFinalChunk_aux hv hreach hok
  exact cliRunAbortOnPanic_of_fastReachableW_exited hpb hinit htot hchk

theorem cliRunAbortOnPanic_of_elfFinalChunk_aborted
    {elf : ElfImage} {fs : ElfFullSpec} {realInp fastInp : Inputs} {k : Nat} {src : MkCkpt}
    (hv : ElfFullValid elf fs)
    (hinp : realInp = fastInp)
    (hreach : ElfCkptReachable fs fastInp src)
    (hok : checkElfFinalChunkAborted fs fastInp k src = true) :
    cliRunAbortOnPanic elf compHooks0 realInp = some .aborted := by
  subst hinp
  obtain ⟨fs0, fsf, hpb, hinit, htot, hchk⟩ := reach_of_elfFinalChunk_aux hv hreach hok
  exact cliRunAbortOnPanic_of_fastReachableW_aborted hpb hinit htot hchk

theorem forall_parse_of_ok
    {bytes : List (BitVec 8)} {elf₀ : ElfImage} {P : ElfImage → Prop}
    (hparse₀ : ElfImage.parse bytes = .ok elf₀)
    (hp : P elf₀) :
    ∀ elf : ElfImage, ElfImage.parse bytes = .ok elf → P elf := by
  intro elf hparse
  cases hparse₀.symm.trans hparse
  exact hp

/-- Direct parse-to-execution bridge from `ElfImage.parse bytes = .ok elf₀` and `ElfFullValid elf₀ fs`
to `cliRunAbortOnPanic elf compHooks0 realInp` for any `elf` parsed from `bytes`. -/
theorem cliRunAbortOnPanic_of_parse_and_elfFinalChunk
    {bytes : List (BitVec 8)} {elf₀ elf : ElfImage} {fs : ElfFullSpec}
    {realInp fastInp : Inputs} {k : Nat} {src : MkCkpt}
    {realStdout fastStdout : List (BitVec 8)} {outFiles : List (String × List (BitVec 8))}
    (hparse₀ : ElfImage.parse bytes = .ok elf₀)
    (hv : ElfFullValid elf₀ fs)
    (hparse : ElfImage.parse bytes = .ok elf)
    (hinp : realInp = fastInp)
    (hstd : realStdout = fastStdout)
    (hreach : ElfCkptReachable fs fastInp src)
    (hok : checkElfFinalChunkExited0 fs fastInp k src fastStdout outFiles = true) :
    cliRunAbortOnPanic elf compHooks0 realInp =
      some (.exited 0 realStdout (filesOf outFiles)) := by
  cases hparse₀.symm.trans hparse
  exact cliRunAbortOnPanic_of_elfFinalChunk hv hinp hstd hreach hok

abbrev ParsedFullSpec := ElfFullSpec
abbrev headerElfOfParsed := headerElfOfFull
abbrev prebuiltOfParsed := prebuiltOfFull
abbrev ParsedFullValidFor := ElfFullValidFor
abbrev ParsedFullValid := ElfFullValid
abbrev runParsedChunkLHS := runElfChunkLHS
abbrev runParsedChunkRHS := runElfChunkRHS
abbrev checkParsedFinalChunkExited0 := checkElfFinalChunkExited0
abbrev checkParsedFinalChunkExited := checkElfFinalChunkExited
abbrev checkParsedFinalChunkAborted := checkElfFinalChunkAborted
abbrev ParsedCkptReachable := ElfCkptReachable
abbrev cliRunAbortOnPanic_of_parsedFinalChunk := @cliRunAbortOnPanic_of_elfFinalChunk
abbrev cliRunAbortOnPanic_of_parse_and_parsedFinalChunk :=
  @cliRunAbortOnPanic_of_parse_and_elfFinalChunk

end Symbolic.BugInjection.Proofs.CliExec.ElfFullSpec

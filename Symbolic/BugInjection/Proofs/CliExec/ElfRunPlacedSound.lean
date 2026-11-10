/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import VerifiedLibraries.Mallocng.Spec
public import LibsignalBinary.Specifications.SignalSession.CliProcess
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import Symbolic.BugInjection.Proofs.CliExec.CompHooks0Placed
public import Symbolic.BugInjection.Proofs.CliExec.FastHooksRows
public import Symbolic.BugInjection.Proofs.CliExec.PlacedExecCore
public import Symbolic.BugInjection.Proofs.CliExec.PrebuildPlaced
public import Symbolic.BugInjection.Proofs.CliExec.ElfFullSpecPlacedCore
public import Symbolic.BugInjection.Proofs.CliExec.ElfFullSpecPlaced
public import Symbolic.BugInjection.Proofs.CliExec.PlacedExecSound
public import Symbolic.BugInjection.Proofs.CliExec.InitPlacedSound

/-!
# Placed ELF Checkpoint-to-`cliRunPlacedSig` Soundness Bridges

Transfers an image-free `ElfCkptReachablePlaced` checkpoint chain and `ElfFullValidPlaced mpl mmpl elf fs`
onto `CryptoVerification.SignalSession.Placed.cliRunPlacedSig mpl mmpl elf W` for generic
`W : CliHooks` and `mpl mmpl : Arm64.Obj.MultiPlacement`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.CliExec.ElfRunPlacedSound

open Arm64 (Memory)
open Arm64.Obj (MultiPlacement)
open Arm64.Process (ElfImage)
open CryptoVerification.SignalSession (CliHooks Inputs cliExternsPlacedSig filesOf)
open CryptoVerification.SignalSession.Placed (cliRunPlacedSig)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0Placed (compHooks0)
open Symbolic.BugInjection.Proofs.CliExec.FastHooksRows (FastState)
open Symbolic.BugInjection.Proofs.CliExec.PlacedExecCore (FastReachablePlaced
  fastRunChunkCachedPlaced fastRunChunkCachedPlaced_eq initFastStateFromBasePlaced)
open Symbolic.BugInjection.Proofs.CliExec.PrebuildPlaced (prebuildElfPlaced)
open Symbolic.BugInjection.Proofs.CliExec.ElfFullSpecPlacedCore (ElfCkptReachablePlaced
  ElfFullSpecPlaced MkCkpt checkElfFinalChunkPlacedAborted checkElfFinalChunkPlacedExited
  checkElfFinalChunkPlacedExited0 headerElfOfFullPlaced initFastStateFromBasePlaced_congr
  prebuiltOfFullPlaced)
open Symbolic.BugInjection.Proofs.CliExec.ElfFullSpecPlaced (ElfFullValidPlaced
  mallocngCallAddrsPlaced stubsOfMpl tokOnceAddrPlaced tokStorageAddrPlaced)
open Symbolic.BugInjection.Proofs.CliExec.PlacedExecSound (
  cliRunPlacedSig_of_fastReachablePlaced
  cliRunPlacedSig_of_fastReachablePlaced_aborted
  cliRunPlacedSig_of_fastReachablePlaced_exited)
open Symbolic.BugInjection.Proofs.CliExec.InitPlacedSound (
  initFastStateFromBasePlaced_sound_of_valid)

private theorem reach_of_elfFinalChunkPlaced_aux
    {mpl mmpl : MultiPlacement} {elf : ElfImage} {fs : ElfFullSpecPlaced} {inp : Inputs}
    {k : Nat} {src : MkCkpt} {checkF : FastState → Bool}
    (hv : ElfFullValidPlaced mpl mmpl elf fs)
    (hreach : ElfCkptReachablePlaced fs inp src)
    (hok : (let pb := prebuiltOfFullPlaced fs
            match initFastStateFromBasePlaced (headerElfOfFullPlaced fs) pb inp with
            | none => false
            | some fs0 =>
              match fastRunChunkCachedPlaced pb.prog k (src pb fs0) with
              | none => false
              | some fsf => checkF fsf) = true) :
    ∃ (fs0 fsf : FastState),
      prebuildElfPlaced compHooks0 elf
        (tokStorageAddrPlaced mpl) (tokOnceAddrPlaced mpl)
        (mallocngCallAddrsPlaced mmpl) (stubsOfMpl mpl) = some (prebuiltOfFullPlaced fs) ∧
      initFastStateFromBasePlaced elf (prebuiltOfFullPlaced fs) inp = some fs0 ∧
      FastReachablePlaced (prebuiltOfFullPlaced fs).prog fs0 fsf ∧
      checkF fsf = true := by
  dsimp only at hok
  cases hinit_h : initFastStateFromBasePlaced (headerElfOfFullPlaced fs) (prebuiltOfFullPlaced fs) inp with
  | none => rw [hinit_h] at hok; nomatch hok
  | some fs0 =>
    rw [hinit_h] at hok
    dsimp only at hok
    have hinit_e : initFastStateFromBasePlaced elf (prebuiltOfFullPlaced fs) inp = some fs0 := by
      rw [initFastStateFromBasePlaced_congr (e1 := elf) (e2 := headerElfOfFullPlaced fs)
        (prebuiltOfFullPlaced fs) inp
        hv.entry_eq hv.phdrVaddr_eq hv.phent_eq hv.phnum_eq hv.brkStart_eq,
        hinit_h]
    cases hrun : fastRunChunkCachedPlaced (prebuiltOfFullPlaced fs).prog k
        (src (prebuiltOfFullPlaced fs) fs0) with
    | none => rw [hrun] at hok; nomatch hok
    | some fsf =>
      rw [hrun] at hok
      exact ⟨fs0, fsf, hv.prebuild_eq, hinit_e,
        .trans (hreach fs0 hinit_h) (.pow2 k (fastRunChunkCachedPlaced_eq hrun)), hok⟩

/-- Transfers an `ElfCkptReachablePlaced` chain and final `.exited 0` chunk check onto
`Placed.cliRunPlacedSig mpl mmpl elf W` via `ElfFullValidPlaced mpl mmpl elf fs`. -/
theorem cliRunPlacedSig_of_elfFinalChunk
    {mpl mmpl : MultiPlacement} {elf : ElfImage} {W : CliHooks}
    {fs : ElfFullSpecPlaced} {realInp fastInp : Inputs} {k : Nat} {src : MkCkpt}
    {realStdout fastStdout : List (BitVec 8)} {outFiles : List (String × List (BitVec 8))}
    (hv : ElfFullValidPlaced mpl mmpl elf fs)
    (hW : ∀ name, cliExternsPlacedSig mmpl compHooks0 name = cliExternsPlacedSig mmpl W name)
    (hinp : realInp = fastInp)
    (hstd : realStdout = fastStdout)
    (hreach : ElfCkptReachablePlaced fs fastInp src)
    (hok : checkElfFinalChunkPlacedExited0 fs fastInp k src fastStdout outFiles = true) :
    cliRunPlacedSig mpl mmpl elf W realInp =
      some (.exited 0 realStdout (filesOf outFiles)) := by
  subst hinp hstd
  obtain ⟨fs0, fsf, _, hinit, htot, hchk⟩ := reach_of_elfFinalChunkPlaced_aux hv hreach hok
  obtain ⟨s0, hload, hag0, hfp, hcl0⟩ :=
    initFastStateFromBasePlaced_sound_of_valid (W := W) hv hW hinit
  exact cliRunPlacedSig_of_fastReachablePlaced
    hload hcl0 hfp hW hag0 (Memory.KeepsFrozen.refl _) htot hchk

theorem cliRunPlacedSig_of_elfFinalChunk_exited
    {mpl mmpl : MultiPlacement} {elf : ElfImage} {W : CliHooks}
    {fs : ElfFullSpecPlaced} {realInp fastInp : Inputs} {k : Nat} {src : MkCkpt}
    {code : BitVec 64} {realStdout fastStdout : List (BitVec 8)}
    {outFiles : List (String × List (BitVec 8))}
    (hv : ElfFullValidPlaced mpl mmpl elf fs)
    (hW : ∀ name, cliExternsPlacedSig mmpl compHooks0 name = cliExternsPlacedSig mmpl W name)
    (hinp : realInp = fastInp)
    (hstd : realStdout = fastStdout)
    (hreach : ElfCkptReachablePlaced fs fastInp src)
    (hok : checkElfFinalChunkPlacedExited fs fastInp k src code fastStdout outFiles = true) :
    cliRunPlacedSig mpl mmpl elf W realInp =
      some (.exited (code.toNat % 256) realStdout (filesOf outFiles)) := by
  subst hinp hstd
  obtain ⟨fs0, fsf, _, hinit, htot, hchk⟩ := reach_of_elfFinalChunkPlaced_aux hv hreach hok
  obtain ⟨s0, hload, hag0, hfp, hcl0⟩ :=
    initFastStateFromBasePlaced_sound_of_valid (W := W) hv hW hinit
  exact cliRunPlacedSig_of_fastReachablePlaced_exited
    hload hcl0 hfp hW hag0 (Memory.KeepsFrozen.refl _) htot hchk

theorem cliRunPlacedSig_of_elfFinalChunk_aborted
    {mpl mmpl : MultiPlacement} {elf : ElfImage} {W : CliHooks}
    {fs : ElfFullSpecPlaced} {realInp fastInp : Inputs} {k : Nat} {src : MkCkpt}
    (hv : ElfFullValidPlaced mpl mmpl elf fs)
    (hW : ∀ name, cliExternsPlacedSig mmpl compHooks0 name = cliExternsPlacedSig mmpl W name)
    (hinp : realInp = fastInp)
    (hreach : ElfCkptReachablePlaced fs fastInp src)
    (hok : checkElfFinalChunkPlacedAborted fs fastInp k src = true) :
    cliRunPlacedSig mpl mmpl elf W realInp = some .aborted := by
  subst hinp
  obtain ⟨fs0, fsf, _, hinit, htot, hchk⟩ := reach_of_elfFinalChunkPlaced_aux hv hreach hok
  obtain ⟨s0, hload, hag0, hfp, hcl0⟩ :=
    initFastStateFromBasePlaced_sound_of_valid (W := W) hv hW hinit
  exact cliRunPlacedSig_of_fastReachablePlaced_aborted
    hload hcl0 hfp hW hag0 (Memory.KeepsFrozen.refl _) htot hchk

theorem forall_parse_of_ok_placed
    {bytes : List (BitVec 8)} {elf₀ : ElfImage} {P : ElfImage → Prop}
    (hparse₀ : ElfImage.parse bytes = .ok elf₀)
    (hp : P elf₀) :
    ∀ elf : ElfImage, ElfImage.parse bytes = .ok elf → P elf := by
  intro elf hparse
  cases hparse₀.symm.trans hparse
  exact hp

/-- Direct parse-to-execution bridge from `ElfImage.parse bytes = .ok elf₀` and
`ElfFullValidPlaced mpl mmpl elf₀ fs` to `Placed.cliRunPlacedSig mpl mmpl elf W realInp`
for any `elf` parsed from `bytes`. -/
theorem cliRunPlacedSig_of_parse_and_elfFinalChunk
    {mpl mmpl : MultiPlacement} {bytes : List (BitVec 8)} {elf₀ elf : ElfImage} {W : CliHooks}
    {fs : ElfFullSpecPlaced} {realInp fastInp : Inputs} {k : Nat} {src : MkCkpt}
    {realStdout fastStdout : List (BitVec 8)} {outFiles : List (String × List (BitVec 8))}
    (hparse₀ : ElfImage.parse bytes = .ok elf₀)
    (hv : ElfFullValidPlaced mpl mmpl elf₀ fs)
    (hW : ∀ name, cliExternsPlacedSig mmpl compHooks0 name = cliExternsPlacedSig mmpl W name)
    (hparse : ElfImage.parse bytes = .ok elf)
    (hinp : realInp = fastInp)
    (hstd : realStdout = fastStdout)
    (hreach : ElfCkptReachablePlaced fs fastInp src)
    (hok : checkElfFinalChunkPlacedExited0 fs fastInp k src fastStdout outFiles = true) :
    cliRunPlacedSig mpl mmpl elf W realInp =
      some (.exited 0 realStdout (filesOf outFiles)) := by
  cases hparse₀.symm.trans hparse
  exact cliRunPlacedSig_of_elfFinalChunk hv hW hinp hstd hreach hok

end Symbolic.BugInjection.Proofs.CliExec.ElfRunPlacedSound

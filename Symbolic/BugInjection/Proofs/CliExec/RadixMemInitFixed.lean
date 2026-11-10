/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.Process.FastParse
public import LibsignalBinary.Specifications.SignalSession.CliProcess
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliProcessFixed
public import Symbolic.BugInjection.Proofs.CliExec.RadixMem
public import Symbolic.BugInjection.Proofs.CliExec.RadixMemLine

/-!
# Fixed-Offset Initial `FastMem` Loader

Constructs the initial stack pointer and `FastMem` for the fixed-offset CLI process image
(`initFastMemAndSp`, `initFastMem`) with the `cliTokenPatch` byte writes at
`cliBase + tokenStorageOff` and `cliBase + tokenOnceOff`, and proves extensional agreement with
`(cliTokenPatch (elf.rawState pinputs)).mem`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.CliExec.RadixMemInitFixed

open Arm64
open Arm64.Process (ElfImage ProcessInputs buildInitialStack)
open CryptoVerification.SignalSession (cliBase cliTokenPatch)
open CryptoVerification.LibsignalSpqrV1 (tokenStorageOff tokenOnceOff)
open Symbolic.BugInjection.Proofs.CliExec.RadixMem (FastMem baseRegions_mapZero_cells_eq
  loadRegionsLines)

/-- Initial `(sp, FastMem)` for `elf` and `pinputs` with `cliTokenPatch` applied, or `none` on address wrap. -/
def initFastMemAndSp (elf : ElfImage) (pinputs : ProcessInputs) : Option (BitVec 64 × FastMem) :=
  match buildInitialStack elf pinputs with
  | .error _ => none
  | .ok (sp, stackRegion) =>
    let regions := elf.segments ++ [stackRegion]
    let top := pinputs.init.stackTop.toNat; let sz := pinputs.init.stackSize
    if sz ≤ top && top ≤ 2 ^ 64 &&
        regions.all (fun r => decide (r.start.toNat + r.bytes.length ≤ 2 ^ 64)) then
      let fm0 : FastMem := { lines := loadRegionsLines regions, stackBase := top - sz, stackTop := top }
      let fm1 := (fm0.writeBytes (cliBase + tokenStorageOff) [0#8]).writeBytes
        (cliBase + tokenOnceOff) [0#8, 0#8, 0#8, 0#8]
      some (sp, fm1)
    else none

def initFastMem (elf : ElfImage) (pinputs : ProcessInputs) : Option FastMem :=
  (initFastMemAndSp elf pinputs).map Prod.snd

theorem initFastMemAndSp_agrees {elf : ElfImage} {pinputs : ProcessInputs}
    {sp : BitVec 64} {fm : FastMem}
    (hinit : initFastMemAndSp elf pinputs = some (sp, fm)) :
    (elf.rawState pinputs).sp = sp ∧
      fm.Agrees (cliTokenPatch (elf.rawState pinputs)).mem := by
  unfold initFastMemAndSp at hinit
  generalize hstk : buildInitialStack elf pinputs = stkRes at hinit
  cases stkRes with
  | error _ => nomatch hinit
  | ok pair =>
    rcases pair with ⟨sp0, stackRegion⟩; dsimp only at hinit
    split at hinit
    · rename_i hcond; injection hinit with hinit; rcases Prod.mk.inj hinit with ⟨rfl, rfl⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      rcases hcond with ⟨⟨hsz_le, htop_le⟩, hreg_wrap⟩
      have hsp : (elf.rawState pinputs).sp = sp0 := by simp [ElfImage.rawState, hstk]
      have hmem : (cliTokenPatch (elf.rawState pinputs)).mem =
          (((Memory.mapZero ⟨Snapshot.loadCellAt (elf.segments ++ [stackRegion])⟩
              (BitVec.ofNat 64 (pinputs.init.stackTop.toNat - pinputs.init.stackSize))
              pinputs.init.stackSize).writeBytes (cliBase + tokenStorageOff) [0#8]).writeBytes
            (cliBase + tokenOnceOff) [0#8, 0#8, 0#8, 0#8]) := by
        simp [ElfImage.rawState, hstk, cliTokenPatch, State.setMem]
      refine ⟨hsp, ?_⟩; rw [hmem]
      apply FastMem.writeBytes_agrees; apply FastMem.writeBytes_agrees
      intro a; dsimp only [FastMem.cellAt]
      exact baseRegions_mapZero_cells_eq (elf.segments ++ [stackRegion])
        pinputs.init.stackTop.toNat pinputs.init.stackSize hsz_le htop_le hreg_wrap a
    · nomatch hinit

theorem initFastMem_agrees {elf : ElfImage} {pinputs : ProcessInputs} {fm : FastMem}
    (hinit : initFastMem elf pinputs = some fm) :
    fm.Agrees (cliTokenPatch (elf.rawState pinputs)).mem := by
  unfold initFastMem at hinit
  cases h : initFastMemAndSp elf pinputs with
  | none => rw [h] at hinit; nomatch hinit
  | some pair => rw [h] at hinit; injection hinit with hinit; subst hinit; exact (initFastMemAndSp_agrees h).2

end Symbolic.BugInjection.Proofs.CliExec.RadixMemInitFixed

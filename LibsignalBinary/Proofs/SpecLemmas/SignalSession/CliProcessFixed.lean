/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionObj
public import LibsignalBinary.Specifications.SignalSession.CliProcess
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliRunFixed

@[expose] public section

set_option autoImplicit false

/-!
# Fixed-Image Whole-Process CLI Execution

**Checked by Lean.** Fixed-image process execution definitions for the `signal-session` CLI at
`cliBase`: panic-aborting externs `cliExternsAbortOnPanic` and program `cliProgAbortOnPanic`, the
post-CPU-probe state patch `cliTokenPatch` (DEV-CLI10, DEV-M17), and whole-process run semantics
`CliRunsTo` and `cliRunAbortOnPanic`.
-/

namespace CryptoVerification.SignalSession

open Arm64 Arm64.Process

/-- Wraps every hook in `cliExterns W` with `abortOnPanic`. -/
noncomputable def cliExternsAbortOnPanic (W : CliHooks) : String → Option (State → State) :=
  fun name => (cliExterns W name).map abortOnPanic

/-- Fixed-image CLI `Program` rebasing `libsignalSessionImage.toProgram` at `cliBase` under
`cliExternsAbortOnPanic W`. -/
noncomputable def cliProgAbortOnPanic (W : CliHooks) : Program :=
  libsignalSessionImage.toProgram.rebase cliBase (cliExternsAbortOnPanic W)

/-- Writes SPQR's post-CPU-probe state ("no AES/PMULL", DEV-CLI10, DEV-M17) into loaded state `s`:
`STORAGE.0 := 0` at `cliBase + tokenStorageOff` and `TOKEN`'s 4-byte LE `futex::Once` state `:= 0`
(`COMPLETE`) at `cliBase + tokenOnceOff`, matching what `use_accelerated::init` stores under the
engine's default `AT_HWCAP = 0x3` (FP + ASIMD, without AES or PMULL). -/
def cliTokenPatch (s : State) : State :=
  s.setMem ((s.mem.writeBytes (cliBase + LibsignalSpqrV1.tokenStorageOff) [0#8]).writeBytes
    (cliBase + LibsignalSpqrV1.tokenOnceOff) [0#8, 0#8, 0#8, 0#8])


/-- Whole-process execution predicate: `elf.loadState (cliProcessInputs i)` yields `s0`, and from
`cliTokenPatch s0` (DEV-CLI10) `cliProgAbortOnPanic W` terminates matching `o` with no reachable
fault, halt, panic, or `.OutOfMemory` (`ProcessRunsTo` with `oom := False`). -/
def CliRunsTo (elf : ElfImage) (W : CliHooks) (i : Inputs) (o : Outcome) : Prop :=
  ∃ s0, elf.loadState (cliProcessInputs i) = .ok s0 ∧
    _root_.Arm64.Process.ProcessRunsTo (cliProgAbortOnPanic W) (cliTokenPatch s0) (OutcomeMatchesProcess o)

open Classical in
/-- Partial run function returning the unique `Outcome` satisfying `CliRunsTo elf W i`, or `none`
if none exists. -/
noncomputable def cliRunAbortOnPanic (elf : ElfImage) (W : CliHooks) : CliRun := fun i =>
  if h : ∃ o, CliRunsTo elf W i o then some (Classical.choose h) else none

end CryptoVerification.SignalSession

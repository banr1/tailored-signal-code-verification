/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.ElfBinding
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliProcessFixed
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliBinaryFixed

/-!
# Fixed-image CLI refinement predicates

**Checked by Lean.** Proof-side fixed-image ELF run relation (`elfRel`), termination predicate
(`CliElfProgress`), and refinement statements (`CompRefinesCliElf`, `CompRefinesCliBinary`).
-/

@[expose] public section

set_option autoImplicit false

namespace DY.Libsignal.Composed.Refinement.Cli

open Arm64 Arm64.Process
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.Composed.Refinement
open CryptoVerification.SignalSession (CliElfCodeMatches CliHooks cliRunAbortOnPanic)

/-- Run relation of the fixed ELF image `elf` under hooks `W` induced by `cliRunAbortOnPanic`. -/
noncomputable def elfRel (elf : ElfImage) (_interp : ExternInterpretation)
    (W : CliHooks) : CryptoVerification.SignalSession.Inputs →
    Option CryptoVerification.SignalSession.Outcome → Prop :=
  runFnToRelation (cliRunAbortOnPanic elf W)

/-- Termination without fault or trap on every guarded CLI call reachable from `initDirs`. -/
def CliElfProgress (elf : ElfImage) : Prop :=
  ∀ interp : ExternInterpretation, ExternContractsHoldCli interp →
  ∀ W : CliHooks, HooksMatchInterpretation interp W →
  ∀ r : ProtocolSetup, ProtocolSetupWF r →
  ∀ t : CliTurn, CliReachable (elfRel elf interp W) interp r (CliTurn.init (initDirs interp r)) t →
  ∀ (c : CliCall) (i : CryptoVerification.SignalSession.Inputs),
    ValidCall interp r t c → InputsFor c (t.dirs c.party) i →
    cliRunAbortOnPanic elf W i ≠ none

/-- Whole-protocol trace refinement over runs of the fixed ELF image `elf`. -/
def CompRefinesCliElf (elf : ElfImage) : Prop :=
  CompRefinesCli HooksMatchInterpretation (elfRel elf)

/-- Fixed-image refinement and progress statement for ELF binary `bytes`. -/
def CompRefinesCliBinary (bytes : List (BitVec 8)) : Prop :=
  ∃ elf : ElfImage, ElfImage.parse bytes = .ok elf ∧ CliElfCodeMatches elf ∧
    CliElfProgress elf ∧ CompRefinesCliElf elf

end DY.Libsignal.Composed.Refinement.Cli

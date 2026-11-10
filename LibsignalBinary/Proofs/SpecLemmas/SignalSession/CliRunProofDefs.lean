/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.CliRun
public import LibsignalBinary.Specifications.SignalSession.Process
public import LibsignalBinary.Specifications.SignalSession.Run
public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhHooksCommon
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliRunFixed
public import GeneratedLean.LibsignalSessionObj

/-!
# Proof-Side CLI Program and Outcome Projection

Defines the non-aborting fixed-image CLI program `cliProg` and the `ProcessResult → Outcome`
projection `toOutcome`.
-/

@[expose] public section

set_option autoImplicit false
namespace CryptoVerification.SignalSession
open Arm64 Arm64.Process ProofLib
/-- Fixed-image CLI `Program` rebasing `libsignalSessionImage.toProgram` at `cliBase` with externs
`cliExterns W`. -/
noncomputable def cliProg (W : CliHooks) : Program :=
  libsignalSessionImage.toProgram.rebase cliBase (cliExterns W)

/-- Projects an engine `ProcessResult` to a CLI `Outcome`, reducing the 64-bit `exit_group` status
modulo 256 (matching Linux `WEXITSTATUS`) and restricting the file system via `fsView`. -/
def toOutcome : ProcessResult → Outcome
  | .exited code out fs => .exited (code.toNat % 256) out (fsView fs)
  | .aborted => .aborted

end CryptoVerification.SignalSession

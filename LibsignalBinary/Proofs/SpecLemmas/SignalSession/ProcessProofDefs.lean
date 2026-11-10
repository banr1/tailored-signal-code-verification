/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.Process
public import Arm64.Trusted.Process.Semantics

/-!
# Proof-Side Process Outcome Definitions

Defines `ProcessResult.ofState?`, `ProcessSafe`, `ProcessRunsTo`, `ElfRunsTo`, and
`outcomeOf` over `LibsignalBinary.Specifications.SignalSession.Process`.
-/

@[expose] public section

set_option autoImplicit false
namespace CryptoVerification.SignalSession
open Arm64 Arm64.Process
namespace ProcessResult

/-- Extracts a `ProcessResult` from a terminal machine state: `.Exited code` yields
`.exited code stdout s.fs`, `.Panicked` yields `.aborted`, and all other statuses yield `none`. -/
def ofState? (s : State) : Option ProcessResult :=
  match s.status with
  | .Exited code => some (.exited code (ProcessOutcome.traceStreamBytes .stdout s.trace) s.fs)
  | .Panicked => some .aborted
  | _ => none

end ProcessResult

/-- Every state reachable from `s0` either has a `ProcessResult` or is `.Running` and can step. -/
def ProcessSafe (prog : Program) (s0 : State) : Prop :=
  ∀ s', Steps prog s0 s' →
    (ProcessResult.ofState? s').isSome ∨ (s'.status = .Running ∧ ∃ s'', Step prog s' s'')

/-- `prog` is `ProcessSafe` from `s0` and reaches a state with result `r`. -/
def ProcessRunsTo (prog : Program) (s0 : State) (r : ProcessResult) : Prop :=
  ProcessSafe prog s0 ∧ ∃ sf, Steps prog s0 sf ∧ ProcessResult.ofState? sf = some r

/-- `img.loadState inputs` succeeds and `ProcessRunsTo prog s0 r` holds from the loaded state. -/
def ElfRunsTo (img : ElfImage) (prog : Program) (inputs : ProcessInputs)
    (r : ProcessResult) : Prop :=
  ∃ s0, img.loadState inputs = .ok s0 ∧ ProcessRunsTo prog s0 r

open Classical in
/-- Partial function selecting the unique `r` satisfying `ElfRunsTo img prog inputs r`, or `none` if none exists. -/
noncomputable def outcomeOf (img : ElfImage) (prog : Program) (inputs : ProcessInputs) :
    Option ProcessResult :=
  if h : ∃ r, ElfRunsTo img prog inputs r then some (Classical.choose h) else none

end CryptoVerification.SignalSession

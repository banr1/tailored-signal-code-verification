/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.CliLabels
public import ProofLib.Placed.LabelsInterned
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliLabelsLfoCert
import ProofLib.ProgramReflection
meta import ProofLib.ProgramReflection

@[expose] public section

set_option autoImplicit false

/-!
# `ExtractedObj` Interning and Symbol-Table Certificate Checks

**Checked by Lean.** Proves `cliLabelsLfo_objs_eq` and `cliLabelsLfo_objs_ok` over `cliLinkObjs`
against the interned `IdxTree` certificate in `CliLabelsLfoCert`.
-/

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliLabelsLfoObjsEq

open ProofLib.ProgramReflection
open CryptoVerification.SignalSession (cliLinkObjs)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliLabelsLfoCert
  (cliLabelsLfo_N cliLabelsLfo_namesTree cliLabelsLfo_charsTree cliLabelsLfo_objsTree
   cliLabelsLfo_rawSummary cliLabelsLfo_rawClaimed)

set_option maxRecDepth 2000000 in
theorem cliLabelsLfo_objs_eq :
    (cliLinkObjs : List Arm64.Obj.ExtractedObj) =
      cliLabelsLfo_objsTree.toList.map
        (Arm64.Obj.LabelsInterned.IObj.toExtractedObj cliLabelsLfo_namesTree) := by
  rfl_kernel

set_option maxRecDepth 2000000 in
theorem cliLabelsLfo_objs_ok :
    Arm64.Obj.LabelsInterned.checkObjSymsB cliLabelsLfo_N cliLabelsLfo_charsTree
      cliLabelsLfo_objsTree cliLabelsLfo_rawSummary cliLabelsLfo_rawClaimed = true := by
  rfl_kernel

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliLabelsLfoObjsEq

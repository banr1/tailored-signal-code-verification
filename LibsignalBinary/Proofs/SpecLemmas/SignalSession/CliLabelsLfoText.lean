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
# Code-Slice Byte, Metadata, and Relocation Certificate Checks

**Checked by Lean.** Proves `cliLabelsLfo_lib_eq`, `cliLabelsLfo_tbytes_ok`,
`cliLabelsLfo_tmeta_ok`, and `cliLabelsLfo_brelocs_ok` over `libsignalSessionLib` against the
interned `IdxTree` certificate in `CliLabelsLfoCert`.
-/

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliLabelsLfoText

open ProofLib.ProgramReflection
open CryptoVerification.SignalSession (libsignalSessionLib)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliLabelsLfoCert
  (cliLabelsLfo_N cliLabelsLfo_namesTree cliLabelsLfo_objsTree cliLabelsLfo_iLib
   cliLabelsLfo_bOTree cliLabelsLfo_dOTree cliLabelsLfo_symRole cliLabelsLfo_rawSummary
   cliLabelsLfo_rawClaimed cliLabelsLfo_textGroups)

theorem cliLabelsLfo_lib_eq :
    (libsignalSessionLib : Arm64.Obj.MultiPlacedLib) =
      cliLabelsLfo_iLib.toMultiPlacedLib cliLabelsLfo_namesTree := by
  rfl_kernel

theorem cliLabelsLfo_tbytes_ok :
    Arm64.Obj.LabelsInterned.checkTextGroupsBytesB cliLabelsLfo_objsTree
      cliLabelsLfo_iLib.blocks cliLabelsLfo_bOTree cliLabelsLfo_textGroups = true := by
  rfl_kernel

theorem cliLabelsLfo_tmeta_ok :
    Arm64.Obj.LabelsInterned.checkTextSlicesMetaB cliLabelsLfo_N cliLabelsLfo_objsTree
      cliLabelsLfo_iLib.blocks cliLabelsLfo_bOTree cliLabelsLfo_rawClaimed = true := by
  rfl_kernel

theorem cliLabelsLfo_brelocs_ok :
    Arm64.Obj.LabelsInterned.checkAllBlockRelocsB cliLabelsLfo_N cliLabelsLfo_objsTree
      cliLabelsLfo_iLib cliLabelsLfo_bOTree cliLabelsLfo_dOTree cliLabelsLfo_symRole
      cliLabelsLfo_rawSummary = true := by
  rfl_kernel

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliLabelsLfoText

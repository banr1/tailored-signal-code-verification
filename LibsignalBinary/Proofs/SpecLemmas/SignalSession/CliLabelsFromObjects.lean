/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.CliLabels
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliLabelsLfo
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliProbeLabels
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternLabels
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliPanicLabels

@[expose] public section

set_option autoImplicit false

/-!
# Label Provenance Assembly (`CliLabelsFromObjects`)

**Checked by Lean.** Combines `Obj.LabelsFromObjects cliLinkObjs libsignalSessionLib`,
`CliProbeLabelsAnchored`, `CliExternLabelsUndefined`, and `CliPanicLabelsSound` into the unified
label provenance certificate `cliLabelsFromObjects : CliLabelsFromObjects`.
-/

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliLabelsFromObjects

open Arm64
open CryptoVerification.SignalSession (
  cliLinkObjs libsignalSessionLib CliProbeLabelsAnchored
  CliExternLabelsUndefined CliPanicLabelsSound CliLabelsFromObjects
)

/-- Combines `(bO, dO)` witnesses for `Obj.LabelsFromObjects` and `CliProbeLabelsAnchored` with
`CliExternLabelsUndefined` and `CliPanicLabelsSound` into `CliLabelsFromObjects`. -/
theorem cliLabelsFromObjects_of_parts
    (bO : Fin libsignalSessionLib.blocks.length → Obj.SliceOrigin)
    (dO : Fin libsignalSessionLib.data.length → Obj.SliceOrigin)
    (h_lfo : Obj.LabelsFromObjects cliLinkObjs libsignalSessionLib bO dO)
    (h_probe : CliProbeLabelsAnchored dO)
    (h_ext : CliExternLabelsUndefined)
    (h_panic : CliPanicLabelsSound) :
    CliLabelsFromObjects :=
  ⟨⟨bO, dO, h_lfo, h_probe⟩, h_ext, h_panic⟩

/-- Existential-witness variant of `cliLabelsFromObjects_of_parts`. -/
theorem cliLabelsFromObjects_of_exists
    (h_lfo_probe : ∃ bO dO,
      Obj.LabelsFromObjects cliLinkObjs libsignalSessionLib bO dO ∧
        CliProbeLabelsAnchored dO)
    (h_ext : CliExternLabelsUndefined)
    (h_panic : CliPanicLabelsSound) :
    CliLabelsFromObjects :=
  ⟨h_lfo_probe, h_ext, h_panic⟩

/-- Concrete label provenance certificate for `cliLinkObjs` and `libsignalSessionLib`. -/
theorem cliLabelsFromObjects : CliLabelsFromObjects :=
  cliLabelsFromObjects_of_parts
    CliLabelsLfo.cliLabelsLfo_bO
    CliLabelsLfo.cliLabelsLfo_dO
    CliLabelsLfo.cliLabelsLfo_spec
    CliProbeLabels.cliProbeLabelsAnchored
    CliExternLabels.cliExternLabelsUndefined
    CliPanicLabels.cliPanicLabelsSound

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliLabelsFromObjects

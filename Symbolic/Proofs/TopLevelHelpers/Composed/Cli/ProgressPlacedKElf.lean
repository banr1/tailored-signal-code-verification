/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.CliElfProof
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KGhostArms
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedG
public import LibsignalBinary.Specifications.SignalSession.CliElf
public import Symbolic.Proofs.TopLevelHelpers.Composed.Cli.ProgressElfPlacedG
public import Symbolic.Specifications.Refinement.ElfBinding
public import VerifiedLibraries.Mallocng.Spec

/-!
# Relocatable Progress for `cliElfBytes` from `H2KGhostArms`

**Checked by Lean.**

Instantiates `cliElfProgressPlaced_of_strictG` at `cliElfBytes` from `H2KGhostArms`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.TopLevelHelpers.Composed.Cli.ProgressPlacedKElf

open Arm64.Obj (MultiPlacement)
open Arm64.Process (ElfImage)
open CryptoVerification.SignalSession (cliElfBytes cliElfImage cliElf_parse libsignalSessionLib)
open DY.Libsignal.Composed.Refinement.Cli (CliElfProgressPlaced)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KGhostArms
  (H2KGhostArms
   h2kg_hinitSem_cliElfG
   h2kg_hmain_cliElfG
   h2kg_hoverD3_cliElfG
   h2kg_hpathB_cliElfG
   h2kg_huntyped_cliElfG
   h2kg_hvalidMatch_cliElfG)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedG
  (cliElf_f3B2NeedLocksAssumptionsG)
open Symbolic.Proofs.TopLevelHelpers.Composed.Cli.ProgressElfPlacedG
  (cliElfProgressPlaced_of_strictG)

/-- Relocatable two-placement progress for `cliElfBytes` from `H2KGhostArms`. -/
theorem cliElfProgressPlaced_cliElfK (hG : H2KGhostArms) :
    ∀ mpl mmpl : MultiPlacement,
      libsignalSessionLib.LinkedAt cliElfBytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl →
      ∀ elf : ElfImage, ElfImage.parse cliElfBytes = .ok elf →
        CliElfProgressPlaced mpl mmpl elf := by
  intro mpl mmpl hLs hMm elf hparse
  have helf : cliElfImage = elf := Except.ok.inj (cliElf_parse.symm.trans hparse)
  subst helf
  exact cliElfProgressPlaced_of_strictG
    (cliElf_f3B2NeedLocksAssumptionsG hLs hMm)
    (h2kg_hmain_cliElfG hG mpl mmpl hLs hMm)
    (h2kg_hoverD3_cliElfG hG mpl mmpl hLs hMm)
    (h2kg_huntyped_cliElfG hG mpl mmpl hLs hMm)
    (h2kg_hpathB_cliElfG hG mpl mmpl hLs hMm)
    (h2kg_hvalidMatch_cliElfG hG mpl mmpl hLs hMm)
    (h2kg_hinitSem_cliElfG hG mpl mmpl hLs hMm)

end Symbolic.Proofs.TopLevelHelpers.Composed.Cli.ProgressPlacedKElf

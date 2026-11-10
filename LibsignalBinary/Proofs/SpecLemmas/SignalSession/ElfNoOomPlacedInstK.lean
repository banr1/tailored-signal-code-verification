/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.CliElfProof
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomProofF3G
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4A.T2Strict2Bridge
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2G
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KGhostArms
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedG
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import LibsignalBinary.Specifications.SignalSession.CliElf
public import VerifiedLibraries.Mallocng.Spec

/-!
# Ghost-Arm Pointwise `¬ CliReachesOOMPlaced` Instantiation for `cliElfImage`

**Checked by Lean.** Counterpart of `ElfNoOomPlacedInst` parameterized by `(hG : H2KGhostArms)` via
`h2kg_hmain_cliElfG` and `h2kg_hoverD3_cliElfG`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfNoOomPlacedInstK

open Arm64
open Arm64.Process (ElfImage)
open CryptoVerification.SignalSession
  (CliHooks CliPqxdhInputs CliReachesOOMPlaced Inputs cliElfBytes cliElfImage cliElf_parse
    libsignalSessionLib)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomProofF3G
  (mainOkCliF3OverG_of_mainOkOverD3F3G)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4A.T2Strict2Bridge
  (hAlloc_of_cliPqxdhElfCorrectStrictPlaced2)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2G
  (cliPqxdhElfCorrectStrictPlaced2_of_f3B2NeedLocksG')
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KGhostArms
  (H2KGhostArms h2kg_hmain_cliElfG h2kg_hoverD3_cliElfG)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedG
  (cliElf_f3B2NeedLocksAssumptionsG)

/-- Under `H2KGhostArms`, `¬ CliReachesOOMPlaced mpl mmpl cliElfImage W i` holds across
`CliPqxdhInputs ⟨W.C, W.Q⟩` for any `LinkedAt cliElfBytes` placements `(mpl, mmpl)`. -/
theorem cliElf_noOOMK (hG : H2KGhostArms) :
    ∀ (mpl mmpl : Obj.MultiPlacement),
      libsignalSessionLib.LinkedAt cliElfBytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl →
      ∀ (W : CliHooks),
        ∀ i : Inputs, CliPqxdhInputs ⟨W.C, W.Q⟩ i → ¬ CliReachesOOMPlaced mpl mmpl cliElfImage W i :=
  fun mpl mmpl hLs hMm W =>
    hAlloc_of_cliPqxdhElfCorrectStrictPlaced2
      (cliPqxdhElfCorrectStrictPlaced2_of_f3B2NeedLocksG'
        (cliElf_f3B2NeedLocksAssumptionsG hLs hMm)
        (h2kg_hmain_cliElfG hG mpl mmpl hLs hMm)
        (mainOkCliF3OverG_of_mainOkOverD3F3G (h2kg_hoverD3_cliElfG hG mpl mmpl hLs hMm)))
      W

/-- `ElfImage.parse` form of `cliElf_noOOMK`. -/
theorem cliElf_noOOM_of_parseK (hG : H2KGhostArms) :
    ∀ (mpl mmpl : Obj.MultiPlacement), libsignalSessionLib.LinkedAt cliElfBytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl →
      ∀ elf : ElfImage, ElfImage.parse cliElfBytes = .ok elf →
      ∀ (W : CliHooks) (i : Inputs), CliPqxdhInputs ⟨W.C, W.Q⟩ i →
        ¬ CliReachesOOMPlaced mpl mmpl elf W i := by
  intro mpl mmpl hLs hMm elf hParse
  have h : cliElfImage = elf := Except.ok.inj (cliElf_parse.symm.trans hParse)
  subst h
  exact cliElf_noOOMK hG mpl mmpl hLs hMm

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfNoOomPlacedInstK

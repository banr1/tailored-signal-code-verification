/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.CliElfProof
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3NonCanonF3
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4A.T2Strict2Bridge
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import LibsignalBinary.Specifications.SignalSession.CliElf
public import VerifiedLibraries.Mallocng.Spec

/-!
# Pointwise `¬ CliReachesOOMPlaced` Instantiation for `cliElfImage`

**Checked by Lean.** Composes `cliElf_f3B2NeedLocksAssumptions`, `hmain_cliElf`, and `hoverD3_cliElf`
through `cliPqxdhElfCorrectStrictPlaced2_of_f3B2NeedLocks'` and
`hAlloc_of_cliPqxdhElfCorrectStrictPlaced2` to prove `¬ CliReachesOOMPlaced` across `CliPqxdhInputs`
on `cliElfImage` under `CliElfHole2Assumption` (retiring DEV-CLI12).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfNoOomPlacedInst

open Arm64
open Arm64.Process (ElfImage)
open CryptoVerification.SignalSession
  (CliHooks CliPqxdhInputs CliReachesOOMPlaced Inputs cliElfBytes cliElfImage cliElf_parse
    libsignalSessionLib)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3NonCanonF3
  (mainOkCliF3Over_of_mainOkOverD3F3)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4A.T2Strict2Bridge
  (hAlloc_of_cliPqxdhElfCorrectStrictPlaced2)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2
  (cliPqxdhElfCorrectStrictPlaced2_of_f3B2NeedLocks')
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics
  (cliElf_f3B2NeedLocksAssumptions)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
  (CliElfHole2Assumption hmain_cliElf hoverD3_cliElf)

/-- Under `CliElfHole2Assumption`, `¬ CliReachesOOMPlaced mpl mmpl cliElfImage W i` holds on every
`CliPqxdhInputs ⟨W.C, W.Q⟩ i` for any `LinkedAt cliElfBytes` placements `(mpl, mmpl)` (discharging
the no-OOM premise replacing DEV-CLI12). -/
theorem cliElf_noOOM (hA : CliElfHole2Assumption) :
    ∀ (mpl mmpl : Obj.MultiPlacement),
      libsignalSessionLib.LinkedAt cliElfBytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl →
      ∀ (W : CliHooks),
        ∀ i : Inputs, CliPqxdhInputs ⟨W.C, W.Q⟩ i → ¬ CliReachesOOMPlaced mpl mmpl cliElfImage W i :=
  fun mpl mmpl hLs hMm W =>
    hAlloc_of_cliPqxdhElfCorrectStrictPlaced2
      (cliPqxdhElfCorrectStrictPlaced2_of_f3B2NeedLocks'
        (cliElf_f3B2NeedLocksAssumptions hLs hMm)
        (hmain_cliElf hA mpl mmpl hLs hMm)
        (mainOkCliF3Over_of_mainOkOverD3F3 (hoverD3_cliElf hA mpl mmpl hLs hMm)))
      W

/-- `ElfImage.parse` form of `cliElf_noOOM` matching `main_of_lemmas_placed`. -/
theorem cliElf_noOOM_of_parse (hA : CliElfHole2Assumption) :
    ∀ (mpl mmpl : Obj.MultiPlacement), libsignalSessionLib.LinkedAt cliElfBytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl →
      ∀ elf : ElfImage, ElfImage.parse cliElfBytes = .ok elf →
      ∀ (W : CliHooks) (i : Inputs), CliPqxdhInputs ⟨W.C, W.Q⟩ i →
        ¬ CliReachesOOMPlaced mpl mmpl elf W i := by
  intro mpl mmpl hLs hMm elf hParse
  have h : cliElfImage = elf := Except.ok.inj (cliElf_parse.symm.trans hParse)
  subst h
  exact cliElf_noOOM hA mpl mmpl hLs hMm

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfNoOomPlacedInst

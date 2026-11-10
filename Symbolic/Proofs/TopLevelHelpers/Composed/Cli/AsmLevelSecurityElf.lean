/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced
public import Symbolic.Proofs.TopLevelHelpers.Composed.Cli.RefinementElf
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst -- rooting-only, no decl used
public import Symbolic.Proofs.TopLevelHelpers.Composed.Cli.AsmLevelSecurity
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliLabelsFromObjects
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KM1
import Symbolic.Proofs.TopLevelHelpers.Composed.Cli.AsmLevelSecurityKElf

/-!
# Concrete `cliElfBytes` Relocatable Assembly-Level Security

Lifts `comp_refines_cli_placed_of_v2`, `comp_refines_cli_placed_of_main`, and
`AsmLevelSecurityKElf.signal_session_secure_placed_proofK` to `SignalSessionSecurePlaced cliElfBytes`,
and re-exports the `LinkedIn cliElfBytes` non-vacuity witnesses for `libsignalSessionLib` and
`VerifiedLibraries.mallocngLib` together with `CliLabelsFromObjects`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.TopLevelHelpers.Composed.Cli

open Arm64 (Memory)
open Arm64.Obj (MultiPlacement)
open Arm64.Process (ElfImage)
open VerifiedLibraries.Mallocng (mallocngAddrsOfPlacement)
open CryptoVerification.SignalSession (cliElfBytes libsignalSessionLib CliLabelsFromObjects)
open DY.Libsignal.Composed.Security (SignalSessionSecurePlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MatchingPathBF3 (MainOkPathBD3F3)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3NonCanonF3
  (MainOkOverD3F3 MainOkValidMatchD3F3)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3UntypedElfF3 (MainOkUntypedD3F3)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2
  (CliElfF3B2NeedLocksAssumptions MainOkCliF3PqB2NeedLocksPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.Parity.F3.BundleInitElfF3 (MainInitSemF3)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlaced
  (CliPqBinaryV2OomF3BytesPlaced)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KM1
  (h2k_ghostArms_closed)

/-- Relocatable two-placement `cliElfBytes` assembly-level CLI security from
`hv2 : CliPqBinaryV2OomF3BytesPlaced cliElfBytes`. -/
theorem signal_session_secure_placed_of_v2
    (hv2 : CliPqBinaryV2OomF3BytesPlaced cliElfBytes)
    (hprog : ∀ mpl mmpl : MultiPlacement,
      libsignalSessionLib.LinkedAt cliElfBytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl →
      ∀ elf' : ElfImage, ElfImage.parse cliElfBytes = .ok elf' →
        DY.Libsignal.Composed.Refinement.Cli.CliElfProgressPlaced mpl mmpl elf') :
    SignalSessionSecurePlaced cliElfBytes :=
  signal_session_secure_placed_of_binary_refines (comp_refines_cli_placed_of_v2 hv2 hprog)

/-- Composes `cliPqBinaryV2OomF3BytesPlaced_cliElf_of_main` with
`signal_session_secure_placed_of_v2` to obtain `SignalSessionSecurePlaced cliElfBytes`. -/
theorem signal_session_secure_placed_of_main
    {elf : ElfImage} {exitStk : Nat} {stk : Nat}
    {CodeOk : MultiPlacement → MultiPlacement → Memory → Prop}
    (hparse : ElfImage.parse cliElfBytes = .ok elf)
    (hAssump : ∀ (mpl mmpl : MultiPlacement),
      libsignalSessionLib.LinkedAt cliElfBytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl →
      CliElfF3B2NeedLocksAssumptions mpl mmpl exitStk
        (mallocngAddrsOfPlacement mmpl).libc stk (CodeOk mpl mmpl) elf)
    (hmain : ∀ mpl mmpl, libsignalSessionLib.LinkedAt cliElfBytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl →
      MainOkCliF3PqB2NeedLocksPlacedAt mpl mmpl (CodeOk mpl mmpl)
        (mallocngAddrsOfPlacement mmpl).libc elf.brkStart stk)
    (hoverD3 : ∀ mpl mmpl, libsignalSessionLib.LinkedAt cliElfBytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl →
      MainOkOverD3F3 mpl mmpl (CodeOk mpl mmpl)
        (mallocngAddrsOfPlacement mmpl).libc elf.brkStart stk)
    (huntyped : ∀ mpl mmpl, libsignalSessionLib.LinkedAt cliElfBytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl →
      MainOkUntypedD3F3 mpl mmpl (CodeOk mpl mmpl)
        (mallocngAddrsOfPlacement mmpl).libc elf.brkStart stk)
    (hpathB : ∀ mpl mmpl, libsignalSessionLib.LinkedAt cliElfBytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl →
      MainOkPathBD3F3 mpl mmpl (CodeOk mpl mmpl)
        (mallocngAddrsOfPlacement mmpl).libc elf.brkStart stk)
    (hvalidMatch : ∀ mpl mmpl, libsignalSessionLib.LinkedAt cliElfBytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl →
      MainOkValidMatchD3F3 mpl mmpl (CodeOk mpl mmpl)
        (mallocngAddrsOfPlacement mmpl).libc elf.brkStart stk)
    (hinitSem : ∀ mpl mmpl, libsignalSessionLib.LinkedAt cliElfBytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl →
      MainInitSemF3 mpl mmpl (CodeOk mpl mmpl)
        (mallocngAddrsOfPlacement mmpl).libc elf.brkStart stk)
    (hprog : ∀ mpl mmpl : MultiPlacement,
      libsignalSessionLib.LinkedAt cliElfBytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl →
      ∀ elf' : ElfImage, ElfImage.parse cliElfBytes = .ok elf' →
        DY.Libsignal.Composed.Refinement.Cli.CliElfProgressPlaced mpl mmpl elf') :
    SignalSessionSecurePlaced cliElfBytes :=
  signal_session_secure_placed_of_binary_refines
    (comp_refines_cli_placed_of_main
      hparse hAssump hmain hoverD3 huntyped hpathB hvalidMatch hinitSem hprog)

/-- Relocatable two-placement assembly-level CLI security for `cliElfBytes`. -/
theorem signal_session_secure_placed_proof :
    SignalSessionSecurePlaced cliElfBytes :=
  AsmLevelSecurityKElf.signal_session_secure_placed_proofK h2k_ghostArms_closed

/-- Non-vacuity witness that `libsignalSessionLib` links into `cliElfBytes`. -/
theorem libsignal_cli_elf_linked_in_proof :
    libsignalSessionLib.LinkedIn cliElfBytes :=
  LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced.cliElf_linkedIn

/-- Non-vacuity witness that `VerifiedLibraries.mallocngLib` links into `cliElfBytes`. -/
theorem libsignal_cli_elf_mallocng_linked_in_proof :
    VerifiedLibraries.mallocngLib.LinkedIn cliElfBytes :=
  LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced.cliElf_mallocng_linkedIn

/--
info: 'Symbolic.Proofs.TopLevelHelpers.Composed.Cli.signal_session_secure_placed_of_v2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms signal_session_secure_placed_of_v2

/--
info: 'Symbolic.Proofs.TopLevelHelpers.Composed.Cli.signal_session_secure_placed_of_main' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms signal_session_secure_placed_of_main


/--
info: 'Symbolic.Proofs.TopLevelHelpers.Composed.Cli.libsignal_cli_elf_linked_in_proof' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms libsignal_cli_elf_linked_in_proof

/--
info: 'Symbolic.Proofs.TopLevelHelpers.Composed.Cli.libsignal_cli_elf_mallocng_linked_in_proof' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms libsignal_cli_elf_mallocng_linked_in_proof

/-- Pre-link object label witness `CliLabelsFromObjects`. -/
theorem libsignal_cli_labels_from_objects_proof : CliLabelsFromObjects :=
  LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliLabelsFromObjects.cliLabelsFromObjects

end Symbolic.Proofs.TopLevelHelpers.Composed.Cli

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.LibsignalCli.StatementPqElf
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import LibsignalBinary.Specifications.SignalSession.CliElf
public import Computational.Proofs.LibsignalCli.MainOfLemmas
public import Computational.Proofs.SignalPqxdh.Delta.Statements
public import Computational.Proofs.LibsignalCli.HeadlineSession
public import Computational.Proofs.LibsignalCli.HeadlineModel
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlaced
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst -- rooting-only, no decl used
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfNoOomPlacedInst -- rooting-only, no decl used
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliLabelsFromObjects
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomG5aReach -- rooting-only, no decl used
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole2FitsEnvParts -- rooting-only, no decl used
import Computational.Proofs.LibsignalCli.MainHaltedGame
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KGhostArms
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KM1
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfNoOomPlacedInstK

@[expose] public section

set_option autoImplicit false

/-!
# PQXDH + SPQR correctness and security of the concrete `signal-session` ELF

**Checked by Lean.**

Composes the relocatable binary correctness bundle, the 1 GiB no-OOM proof, the link-completeness
witnesses, and the pre-link object label witness with `main_of_lemmas_placed` to prove
`CliPqxdhBinaryCorrectAndSecurePlaced cliElfBytes`.
-/

namespace CryptoVerification.SignalSession

open Arm64 (Memory)
open Arm64.Obj (MultiPlacement)
open Arm64.Process (ElfImage)
open VerifiedLibraries.Mallocng (mallocngAddrsOfPlacement)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomSpecF3 (
  LibsignalCliPqBinaryV2OomF3Placed LibsignalCliPqBinaryV2OomF3PlacedAt
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MatchingPathBF3 (MainOkPathBD3F3)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3NonCanonF3 (
  MainOkOverD3F3 MainOkValidMatchD3F3
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3UntypedElfF3 (MainOkUntypedD3F3)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2 (
  CliElfF3B2NeedLocksAssumptions MainOkCliF3PqB2NeedLocksPlacedAt
)
open LibsignalBinary.Proofs.SignalSession.Cli.Parity.F3.BundleInitElfF3 (MainInitSemF3)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlaced (
  CliPqBinaryV2OomF3BytesPlaced
  cliPqBinaryV2OomF3BytesPlaced_cliElf_of_main
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KGhostArms (
  H2KGhostArms h2kg_cliPqBinaryV2OomF3BytesPlaced_cliElf
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KM1 (
  h2k_ghostArms_closed
)

/-! ## Relocatable binary correctness and link witnesses -/

theorem cliPqxdhBinaryCorrectPlacedAt_of_v2OomF3 {mpl mmpl : MultiPlacement}
    {bytes : List (BitVec 8)}
    (hv2 : LibsignalCliPqBinaryV2OomF3PlacedAt mpl mmpl bytes) :
    CliPqxdhBinaryCorrectPlacedAt mpl mmpl bytes :=
  let ⟨elf, hparse, h⟩ := hv2
  ⟨elf, hparse, h.base⟩

theorem cliPqxdhBinaryCorrectPlaced_of_v2OomF3 {bytes : List (BitVec 8)}
    (hv2 : LibsignalCliPqBinaryV2OomF3Placed bytes) :
    CliPqxdhBinaryCorrectPlaced bytes :=
  fun mpl mmpl hLs hMm => cliPqxdhBinaryCorrectPlacedAt_of_v2OomF3 (hv2 mpl mmpl hLs hMm)

theorem libsignal_cli_pq_binary_correct_placed_of_v2
    (hv2 : CliPqBinaryV2OomF3BytesPlaced cliElfBytes) :
    CliPqxdhBinaryCorrectPlaced cliElfBytes :=
  cliPqxdhBinaryCorrectPlaced_of_v2OomF3 hv2

theorem libsignal_cli_pq_binary_correct_placed_of_main
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
        (mallocngAddrsOfPlacement mmpl).libc elf.brkStart stk) :
    CliPqxdhBinaryCorrectPlaced cliElfBytes :=
  libsignal_cli_pq_binary_correct_placed_of_v2
    (cliPqBinaryV2OomF3BytesPlaced_cliElf_of_main
      hparse hAssump hmain hoverD3 huntyped hpathB hvalidMatch hinitSem)

theorem libsignal_cli_pq_binary_correct_placed_proofK :
    H2KGhostArms → CliPqxdhBinaryCorrectPlaced cliElfBytes :=
  fun hG => libsignal_cli_pq_binary_correct_placed_of_v2 (h2kg_cliPqBinaryV2OomF3BytesPlaced_cliElf hG)

/-- Relocatable binary correctness of `cliElfBytes`. -/
theorem libsignal_cli_pq_binary_correct_placed_proof :
    CliPqxdhBinaryCorrectPlaced cliElfBytes :=
  libsignal_cli_pq_binary_correct_placed_proofK h2k_ghostArms_closed

/-- Link-completeness witness for `libsignalSessionLib` in `cliElfBytes`. -/
theorem libsignal_cli_elf_linked_in_proof : libsignalSessionLib.LinkedIn cliElfBytes :=
  LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced.cliElf_linkedIn

/-- Pre-link object label witness `CliLabelsFromObjects`. -/
theorem libsignal_cli_labels_from_objects_proof : CliLabelsFromObjects :=
  LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliLabelsFromObjects.cliLabelsFromObjects

/-- Link-completeness witness for `mallocngLib` in `cliElfBytes`. -/
theorem libsignal_cli_elf_mallocng_linked_in_proof :
    VerifiedLibraries.mallocngLib.LinkedIn cliElfBytes :=
  LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced.cliElf_mallocng_linkedIn

end CryptoVerification.SignalSession

namespace CryptoVerification.LibsignalCli

open Arm64 (Memory)
open Arm64.Obj (MultiPlacement)
open Arm64.Process (ElfImage)
open VerifiedLibraries.Mallocng (mallocngAddrsOfPlacement)
open CryptoVerification.E2E (model_secure_costed_proof session_secure_proof)
open CryptoVerification.SignalSession (
  CliHooks CliPqxdhInputs CliReachesOOMPlaced Inputs
  cliElfBytes libsignalSessionLib
  libsignal_cli_pq_binary_correct_placed_of_main
  libsignal_cli_pq_binary_correct_placed_of_v2
  libsignal_cli_pq_binary_correct_placed_proof
)
open _root_.SignalPqxdh.Security (headlineδ_proof)
open Computational.Proofs.LibsignalCli.MainHaltedGame (cliHaltedBoundProp_holds)
open Computational.Proofs.LibsignalCli.MainOfLemmas (main_of_lemmas_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MatchingPathBF3 (MainOkPathBD3F3)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3NonCanonF3 (
  MainOkOverD3F3 MainOkValidMatchD3F3
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3UntypedElfF3 (MainOkUntypedD3F3)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2 (
  CliElfF3B2NeedLocksAssumptions MainOkCliF3PqB2NeedLocksPlacedAt
)
open LibsignalBinary.Proofs.SignalSession.Cli.Parity.F3.BundleInitElfF3 (MainInitSemF3)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfNoOomPlacedInstK (cliElf_noOOM_of_parseK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KM1 (h2k_ghostArms_closed)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlaced (
  CliPqBinaryV2OomF3BytesPlaced
)

/-! ## Relocatable main theorem -/

theorem libsignal_cli_pq_secure_elf_binary_placed_of_v2
    (hv2 : CliPqBinaryV2OomF3BytesPlaced cliElfBytes)
    (hNoOOM : ∀ (mpl mmpl : MultiPlacement), libsignalSessionLib.LinkedAt cliElfBytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl →
      ∀ elf : ElfImage, ElfImage.parse cliElfBytes = .ok elf →
      ∀ (W : CliHooks) (i : Inputs), CliPqxdhInputs ⟨W.C, W.Q⟩ i →
        ¬ CliReachesOOMPlaced mpl mmpl elf W i) :
    CliPqxdhBinaryCorrectAndSecurePlaced cliElfBytes :=
  main_of_lemmas_placed headlineδ_proof session_secure_proof model_secure_costed_proof
    (libsignal_cli_pq_binary_correct_placed_of_v2 hv2) hNoOOM
    (fun {Pt} _ _ _ S ℓ => cliHaltedBoundProp_holds (Pt := Pt) S ℓ)

theorem libsignal_cli_pq_secure_elf_binary_placed_of_main
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
    (hNoOOM : ∀ (mpl mmpl : MultiPlacement), libsignalSessionLib.LinkedAt cliElfBytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl →
      ∀ elf' : ElfImage, ElfImage.parse cliElfBytes = .ok elf' →
      ∀ (W : CliHooks) (i : Inputs), CliPqxdhInputs ⟨W.C, W.Q⟩ i →
        ¬ CliReachesOOMPlaced mpl mmpl elf' W i) :
    CliPqxdhBinaryCorrectAndSecurePlaced cliElfBytes :=
  main_of_lemmas_placed headlineδ_proof session_secure_proof model_secure_costed_proof
    (libsignal_cli_pq_binary_correct_placed_of_main
      hparse hAssump hmain hoverD3 huntyped hpathB hvalidMatch hinitSem)
    hNoOOM
    (fun {Pt} _ _ _ S ℓ => cliHaltedBoundProp_holds (Pt := Pt) S ℓ)

/-- Relocatable PQXDH + SPQR binary correctness and security of `cliElfBytes`. -/
theorem libsignal_cli_pq_secure_elf_binary_placed_proof :
    CliPqxdhBinaryCorrectAndSecurePlaced cliElfBytes :=
  main_of_lemmas_placed headlineδ_proof session_secure_proof model_secure_costed_proof
    libsignal_cli_pq_binary_correct_placed_proof
    (cliElf_noOOM_of_parseK h2k_ghostArms_closed)
    (fun {Pt} _ _ _ S ℓ => cliHaltedBoundProp_holds (Pt := Pt) S ℓ)

end CryptoVerification.LibsignalCli

/-! ## `H2KGhostArms`-parameterized main theorem -/

namespace CryptoVerification.LibsignalCli

open CryptoVerification.E2E (model_secure_costed_proof session_secure_proof)
open CryptoVerification.SignalSession (
  cliElfBytes libsignal_cli_pq_binary_correct_placed_proofK
)
open _root_.SignalPqxdh.Security (headlineδ_proof)
open Computational.Proofs.LibsignalCli.MainHaltedGame (cliHaltedBoundProp_holds)
open Computational.Proofs.LibsignalCli.MainOfLemmas (main_of_lemmas_placed)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfNoOomPlacedInstK (cliElf_noOOM_of_parseK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KGhostArms (H2KGhostArms)

theorem libsignal_cli_pq_secure_elf_binary_placed_proofK :
    H2KGhostArms → CliPqxdhBinaryCorrectAndSecurePlaced cliElfBytes :=
  fun hG =>
    main_of_lemmas_placed headlineδ_proof session_secure_proof model_secure_costed_proof
      (libsignal_cli_pq_binary_correct_placed_proofK hG) (cliElf_noOOM_of_parseK hG)
      (fun {Pt} _ _ _ S ℓ => cliHaltedBoundProp_holds (Pt := Pt) S ℓ)

end CryptoVerification.LibsignalCli

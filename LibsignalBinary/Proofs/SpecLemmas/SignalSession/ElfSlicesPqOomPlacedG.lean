/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomProofF3G -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2G -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.SignalSession.CliElf
public import VerifiedLibraries.Mallocng.Spec
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfMemsetEntryGuard

/-!
# Concrete `cliElfBytes` Guarded Route-2 Constructors (`ElfSlicesPqOomPlacedG`)

- **Role**: `Role::Proof` (outside the TCB, `CliElfLib`-only).
- **Overview**:
  Hosts the two concrete `cliElfBytes` / `cliElfImage` Route-2 declarations (`R2-G7`
  `cliElf_f3B2NeedLocksAssumptionsG` and `R2-D4` `cliPqBinaryV2OomF3BytesPlaced_cliElf_of_mainG`,
  `HOOKS-LEAD` / `H-REV` Option A) in `SpecLemmas/SignalSession/Elf*.lean` so that
  `CliStrictPlaced2G`, `D3BinaryOomProofF3G`, and `ProgressElfPlacedG` remain `CliElf`-free in the
  default library (`scripts/check_lib_roots.py` L4/L10 `rc=0` with `0` trusted-file edits).
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedG

open Arm64 Arm64.Obj Arm64.Process
open CryptoVerification.SignalSession (cliElfBytes cliElfImage libsignalSessionLib)
open CryptoVerification.SignalSession.Cli.MainHops (cliMainStk)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomProofF3G
  (MainInitSemF3G MainOkOverD3F3G MainOkPathBD3F3G MainOkUntypedD3F3G MainOkValidMatchD3F3G
   libsignalCliPqBinaryV2OomF3PlacedAt_of_f3B2NeedLocksG)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2G
  (CliElfF3B2NeedLocksAssumptionsG MainOkCliF3PqB2NeedLocksPlacedAtG)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics
  (F3CodeOk cliElf_f3B2NeedLocksAssumptions)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfMemsetEntryGuard
  (cliElf_f3MuslHarness_memsetMemcpyLrFalse_of_linkedAt)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlaced
  (CliPqBinaryV2OomF3BytesPlaced)
open VerifiedLibraries.Mallocng (mallocngAddrsOfPlacement)

/-- Closed guarded F3 assumption bundle on `cliElfImage` for arbitrary `LinkedAt cliElfBytes`
placements `(mpl, mmpl)`, discharging `harnessG` internally via
`ElfMemsetEntryGuard.cliElf_f3MuslHarness_memsetMemcpyLrFalse_of_linkedAt` (`R2-G7`). -/
theorem cliElf_f3B2NeedLocksAssumptionsG {mpl mmpl : Obj.MultiPlacement}
    (hls : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hmng : VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl) :
    CliElfF3B2NeedLocksAssumptionsG mpl mmpl 80
      (mallocngAddrsOfPlacement mmpl).libc cliMainStk (F3CodeOk mpl mmpl) cliElfImage :=
  { toCliElfExtB2NeedLocksAssumptions2 := cliElf_f3B2NeedLocksAssumptions hls hmng
    harnessG := cliElf_f3MuslHarness_memsetMemcpyLrFalse_of_linkedAt hls hmng }

/-- Guarded twin of `ElfSlicesPqOomPlaced.cliPqBinaryV2OomF3BytesPlaced_cliElf_of_main` concluding
the unchanged `CliPqBinaryV2OomF3BytesPlaced cliElfBytes` (`R2-D4`). -/
theorem cliPqBinaryV2OomF3BytesPlaced_cliElf_of_mainG
    {elf : ElfImage} {exitStk : Nat} {stk : Nat}
    {CodeOk : MultiPlacement → MultiPlacement → Memory → Prop}
    (hparse : ElfImage.parse cliElfBytes = .ok elf)
    (hAssump : ∀ (mpl mmpl : MultiPlacement),
      libsignalSessionLib.LinkedAt cliElfBytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl →
      CliElfF3B2NeedLocksAssumptionsG mpl mmpl exitStk
        (mallocngAddrsOfPlacement mmpl).libc stk (CodeOk mpl mmpl) elf)
    (hmain : ∀ mpl mmpl, libsignalSessionLib.LinkedAt cliElfBytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl →
      MainOkCliF3PqB2NeedLocksPlacedAtG mpl mmpl (CodeOk mpl mmpl)
        (mallocngAddrsOfPlacement mmpl).libc elf.brkStart stk)
    (hoverD3 : ∀ mpl mmpl, libsignalSessionLib.LinkedAt cliElfBytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl →
      MainOkOverD3F3G mpl mmpl (CodeOk mpl mmpl)
        (mallocngAddrsOfPlacement mmpl).libc elf.brkStart stk)
    (huntyped : ∀ mpl mmpl, libsignalSessionLib.LinkedAt cliElfBytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl →
      MainOkUntypedD3F3G mpl mmpl (CodeOk mpl mmpl)
        (mallocngAddrsOfPlacement mmpl).libc elf.brkStart stk)
    (hpathB : ∀ mpl mmpl, libsignalSessionLib.LinkedAt cliElfBytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl →
      MainOkPathBD3F3G mpl mmpl (CodeOk mpl mmpl)
        (mallocngAddrsOfPlacement mmpl).libc elf.brkStart stk)
    (hvalidMatch : ∀ mpl mmpl, libsignalSessionLib.LinkedAt cliElfBytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl →
      MainOkValidMatchD3F3G mpl mmpl (CodeOk mpl mmpl)
        (mallocngAddrsOfPlacement mmpl).libc elf.brkStart stk)
    (hinitSem : ∀ mpl mmpl, libsignalSessionLib.LinkedAt cliElfBytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl →
      MainInitSemF3G mpl mmpl (CodeOk mpl mmpl)
        (mallocngAddrsOfPlacement mmpl).libc elf.brkStart stk) :
    CliPqBinaryV2OomF3BytesPlaced cliElfBytes :=
  fun mpl mmpl hLs hMm =>
    libsignalCliPqBinaryV2OomF3PlacedAt_of_f3B2NeedLocksG hparse
      (hAssump mpl mmpl hLs hMm)
      (hmain mpl mmpl hLs hMm)
      (hoverD3 mpl mmpl hLs hMm)
      (huntyped mpl mmpl hLs hMm)
      (hpathB mpl mmpl hLs hMm)
      (hvalidMatch mpl mmpl hLs hMm)
      (hinitSem mpl mmpl hLs hMm)

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedG

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Spec
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomProofF3
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomSpecF3
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MatchingPathBF3
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3NonCanonF3
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3UntypedElfF3
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3ExternNoAllocFail
public import LibsignalBinary.Proofs.SignalSession.Cli.Parity.F3.BundleInitElfF3
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import LibsignalBinary.Specifications.SignalSession.CliElf
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Inst
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics

/-!
# Two-Placement ELF-Byte V2-OOM Constructors

Provides two-placement raw ELF-byte V2-OOM constructors (`CliPqBinaryV2OomF3BytesPlacedAt`
and `CliPqBinaryV2OomF3BytesPlaced`) from `CliElfF3B2NeedLocksAssumptions` and the six
`main`-level arm witnesses (`hmain`, `hoverD3`, `huntyped`, `hpathB`, `hvalidMatch`,
and `hinitSem`), discharging `externPreservesNoAllocFailed_cliExternsPlaced` internally.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlaced

open Arm64 (Memory)
open Arm64.Obj (MultiPlacement)
open Arm64.Process (ElfImage)
open VerifiedLibraries.Mallocng (mallocngAddrsOfPlacement)
open CryptoVerification.SignalSession (
  cliElfBytes libsignalSessionLib
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomProofF3 (
  cliPqBinaryV2OomF3Placed_of_f3B2NeedLocks
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomSpecF3 (
  CliPqBinaryV2OomF3Placed LibsignalCliPqBinaryV2OomF3Placed LibsignalCliPqBinaryV2OomF3PlacedAt
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MatchingPathBF3 (
  MainOkPathBD3F3
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3NonCanonF3 (
  MainOkOverD3F3 MainOkValidMatchD3F3
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3UntypedElfF3 (
  MainOkUntypedD3F3
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2 (
  CliElfF3B2NeedLocksAssumptions MainOkCliF3PqB2NeedLocksPlacedAt
)
open LibsignalBinary.Proofs.SignalSession.Cli.Parity.F3.BundleInitElfF3 (
  MainInitSemF3
)

/-- Placement-pinned `(mpl, mmpl)` raw ELF-byte V2-OOM predicate. -/
abbrev CliPqBinaryV2OomF3BytesPlacedAt
    (mpl mmpl : MultiPlacement) (bytes : List (BitVec 8)) : Prop :=
  LibsignalCliPqBinaryV2OomF3PlacedAt mpl mmpl bytes

/-- Universal two-placement `LinkedAt` V2-OOM predicate on raw ELF `bytes`. -/
abbrev CliPqBinaryV2OomF3BytesPlaced (bytes : List (BitVec 8)) : Prop :=
  LibsignalCliPqBinaryV2OomF3Placed bytes

/-- Constructs `CliPqBinaryV2OomF3BytesPlacedAt` from `CliElfF3B2NeedLocksAssumptions` and the six `main`-level arm obligations. -/
theorem cliPqBinaryV2OomF3BytesPlacedAt_of_f3B2NeedLocks
    {mpl mmpl : MultiPlacement} {bytes : List (BitVec 8)} {elf : ElfImage}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    (hparse : ElfImage.parse bytes = .ok elf)
    (H : CliElfF3B2NeedLocksAssumptions mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hmain : MainOkCliF3PqB2NeedLocksPlacedAt mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hoverD3 : MainOkOverD3F3 mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (huntyped : MainOkUntypedD3F3 mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hpathB : MainOkPathBD3F3 mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hvalidMatch : MainOkValidMatchD3F3 mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hinitSem : MainInitSemF3 mpl mmpl CodeOk libcAddr elf.brkStart stk) :
    LibsignalCliPqBinaryV2OomF3PlacedAt mpl mmpl bytes :=
  ⟨elf, hparse,
    cliPqBinaryV2OomF3Placed_of_f3B2NeedLocks H hmain hoverD3 huntyped hpathB hvalidMatch hinitSem⟩

/-- Constructs `CliPqBinaryV2OomF3BytesPlaced` universally quantified over `(mpl, mmpl)` placements. -/
theorem cliPqBinaryV2OomF3BytesPlaced_of_f3B2NeedLocks
    {bytes : List (BitVec 8)} {elf : ElfImage}
    (hparse : ElfImage.parse bytes = .ok elf)
    (hAt : ∀ (mpl mmpl : MultiPlacement),
      libsignalSessionLib.LinkedAt bytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt bytes mmpl →
      ∃ (exitStk : Nat) (libcAddr : BitVec 64) (stk : Nat) (CodeOk : Memory → Prop),
        CliElfF3B2NeedLocksAssumptions mpl mmpl exitStk libcAddr stk CodeOk elf ∧
        MainOkCliF3PqB2NeedLocksPlacedAt mpl mmpl CodeOk libcAddr elf.brkStart stk ∧
        MainOkOverD3F3 mpl mmpl CodeOk libcAddr elf.brkStart stk ∧
        MainOkUntypedD3F3 mpl mmpl CodeOk libcAddr elf.brkStart stk ∧
        MainOkPathBD3F3 mpl mmpl CodeOk libcAddr elf.brkStart stk ∧
        MainOkValidMatchD3F3 mpl mmpl CodeOk libcAddr elf.brkStart stk ∧
        MainInitSemF3 mpl mmpl CodeOk libcAddr elf.brkStart stk) :
    CliPqBinaryV2OomF3BytesPlaced bytes := by
  intro mpl mmpl hLs hMm
  obtain ⟨exitStk, libcAddr, stk, CodeOk, H, hmain, hoverD3, huntyped, hpathB, hvalidMatch, hinitSem⟩ :=
    hAt mpl mmpl hLs hMm
  exact cliPqBinaryV2OomF3BytesPlacedAt_of_f3B2NeedLocks hparse H
    hmain hoverD3 huntyped hpathB hvalidMatch hinitSem

/-- Specializes `cliPqBinaryV2OomF3BytesPlaced_of_f3B2NeedLocks` to `cliElfBytes`. -/
theorem cliPqBinaryV2OomF3BytesPlaced_cliElf_of_main
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
    CliPqBinaryV2OomF3BytesPlaced cliElfBytes :=
  cliPqBinaryV2OomF3BytesPlaced_of_f3B2NeedLocks hparse fun mpl mmpl hLs hMm =>
    ⟨exitStk, (mallocngAddrsOfPlacement mmpl).libc, stk, CodeOk mpl mmpl,
      hAssump mpl mmpl hLs hMm,
      hmain mpl mmpl hLs hMm,
      hoverD3 mpl mmpl hLs hMm,
      huntyped mpl mmpl hLs hMm,
      hpathB mpl mmpl hLs hMm,
      hvalidMatch mpl mmpl hLs hMm,
      hinitSem mpl mmpl hLs hMm⟩

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlaced

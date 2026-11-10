/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.CliElfProof
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomProofF3G
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2G
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2Asm
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KAssembly
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlaced
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
public import LibsignalBinary.Specifications.SignalSession.CliElf
public import VerifiedLibraries.Mallocng.Spec

/-!
# `H2KGhostArms` Bundle and 6-Arm `MainOk*G` Corollaries (`ElfSlicesPqOomH2KGhostArms`)

**Checked by Lean.**

Packages the 6-arm ghost bundle `H2KGhostArms` across all valid `(mpl, mmpl)` placements of
`cliElfBytes` and projects the six guarded `MainOk*G` corollaries (`h2kg_hmain_cliElfG` ..
`h2kg_hinitSem_cliElfG`, Route 2 `#1255` `A2`, which discharge `h2asm_h*_cliElfKG` via `hG`) plus
`h2kg_cliPqBinaryV2OomF3BytesPlaced_cliElf`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KGhostArms

open Arm64.Obj (MultiPlacement)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.SignalSession (cliElfBytes cliElfImage libsignalSessionLib)
open CryptoVerification.SignalSession.Cli.MainHops (cliMainStk)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomProofF3G
  (MainInitSemF3G MainOkOverD3F3G MainOkPathBD3F3G MainOkUntypedD3F3G MainOkValidMatchD3F3G)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2G
  (MainOkCliF3PqB2NeedLocksPlacedAtG)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics (F3CodeOk)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2Asm
  (h2asm_GhostMainArmsK
   h2asm_hinitSem_cliElfKG
   h2asm_hmain_cliElfKG
   h2asm_hoverD3_cliElfKG
   h2asm_hpathB_cliElfKG
   h2asm_huntyped_cliElfKG
   h2asm_hvalidMatch_cliElfKG)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KAssembly
  (h2ka_branch2HookReplaysK h2ka_cliPqBinaryV2OomF3BytesPlaced_cliElf_of_ghostArms)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlaced
  (CliPqBinaryV2OomF3BytesPlaced)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
  (hole2_hblk hole2_hext_nodup)
open VerifiedLibraries (mallocngLib)
open VerifiedLibraries.Mallocng (mallocngAddrsOfPlacement)

/-- 6-arm ghost witness bundle across all valid `(mpl, mmpl)` placements of `cliElfBytes`. -/
def H2KGhostArms : Prop :=
  ∀ mpl mmpl (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl),
    mallocngLib.LinkedAt cliElfBytes mmpl →
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    h2asm_GhostMainArmsK mpl mmpl

/-- Guarded K-route twin (`R2-K1`) of `ElfSlicesPqOomPlacedInst.hmain_cliElf`. -/
theorem h2kg_hmain_cliElfG
    (hG : H2KGhostArms)
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    MainOkCliF3PqB2NeedLocksPlacedAtG mpl mmpl (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  h2asm_hmain_cliElfKG mpl mmpl hLs hMm
    (h2ka_branch2HookReplaysK mpl mmpl hLs hMm)
    (hG mpl mmpl hLs hMm).hmain

/-- Guarded K-route twin (`R2-K1`) of `ElfSlicesPqOomPlacedInst.hoverD3_cliElf`. -/
theorem h2kg_hoverD3_cliElfG
    (hG : H2KGhostArms)
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    MainOkOverD3F3G mpl mmpl (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  h2asm_hoverD3_cliElfKG mpl mmpl hLs hMm
    (h2ka_branch2HookReplaysK mpl mmpl hLs hMm)
    (hG mpl mmpl hLs hMm).hoverD3

/-- Guarded K-route twin (`R2-K1`) of `ElfSlicesPqOomPlacedInst.huntyped_cliElf`. -/
theorem h2kg_huntyped_cliElfG
    (hG : H2KGhostArms)
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    MainOkUntypedD3F3G mpl mmpl (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  h2asm_huntyped_cliElfKG mpl mmpl hLs hMm
    (h2ka_branch2HookReplaysK mpl mmpl hLs hMm)
    (hG mpl mmpl hLs hMm).huntyped

/-- Guarded K-route twin (`R2-K1`) of `ElfSlicesPqOomPlacedInst.hpathB_cliElf`. -/
theorem h2kg_hpathB_cliElfG
    (hG : H2KGhostArms)
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    MainOkPathBD3F3G mpl mmpl (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  h2asm_hpathB_cliElfKG mpl mmpl hLs hMm
    (h2ka_branch2HookReplaysK mpl mmpl hLs hMm)
    (hG mpl mmpl hLs hMm).hpathB

/-- Guarded K-route twin (`R2-K1`) of `ElfSlicesPqOomPlacedInst.hvalidMatch_cliElf`. -/
theorem h2kg_hvalidMatch_cliElfG
    (hG : H2KGhostArms)
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    MainOkValidMatchD3F3G mpl mmpl (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  h2asm_hvalidMatch_cliElfKG mpl mmpl hLs hMm
    (h2ka_branch2HookReplaysK mpl mmpl hLs hMm)
    (hG mpl mmpl hLs hMm).hvalidMatch

/-- Guarded K-route twin (`R2-K1`) of `ElfSlicesPqOomPlacedInst.hinitSem_cliElf`. -/
theorem h2kg_hinitSem_cliElfG
    (hG : H2KGhostArms)
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    MainInitSemF3G mpl mmpl (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  h2asm_hinitSem_cliElfKG mpl mmpl hLs hMm
    (h2ka_branch2HookReplaysK mpl mmpl hLs hMm)
    (hG mpl mmpl hLs hMm).hinitSem

/-- Assembles `CliPqBinaryV2OomF3BytesPlaced cliElfBytes` from `H2KGhostArms`. -/
theorem h2kg_cliPqBinaryV2OomF3BytesPlaced_cliElf
    (hG : H2KGhostArms) :
    CliPqBinaryV2OomF3BytesPlaced cliElfBytes :=
  h2ka_cliPqBinaryV2OomF3BytesPlaced_cliElf_of_ghostArms hG

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KGhostArms

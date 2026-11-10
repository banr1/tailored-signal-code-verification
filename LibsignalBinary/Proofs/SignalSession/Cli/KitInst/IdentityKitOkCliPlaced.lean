/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.ReadFileHookPlaced

/-!
# Placed CLI Instantiation of `IdentityStoreKitPlacedOkI`

Specializes `IdKit.cliIdKitRoClOkIE_placed` and `IdKit.cliIdKitOkIE_placed` to
`cliExternsPlaced mmpl W` (`37`-row `cliHookTablePlaced`), `E2E.HooksE.A0`, `cliIo.rd`, and `cliWrOk`.
-/

@[expose] public section
set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.KitInst.IdKit

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding withLsCodeRoLoaded LibsignalCodeRoLoaded
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunGlue

theorem blackBox_row_placed (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    (lsBlackBoxU8Sym, CryptoVerification.LibsignalSession.blackBoxHook) ∈
      cliHookTablePlaced mmpl W :=
  List.mem_append_right _ (List.mem_of_getElem? (i := 11) rfl)

theorem cliExternsPlaced_blackBox (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliExternsPlaced mmpl W lsBlackBoxU8Sym =
      some CryptoVerification.LibsignalSession.blackBoxHook :=
  cliExternsPlaced_row mmpl W (blackBox_row_placed mmpl W)

theorem cliGhostExterns_blackBox (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) :
    cliGhostExterns g (cliExternsPlaced mmpl W) lsBlackBoxU8Sym =
      some CryptoVerification.LibsignalSession.blackBoxHook :=
  (cliGhostExterns_other g _ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)).trans (cliExternsPlaced_blackBox mmpl W)

theorem cliIdentityVtablesCli_placed [LibsignalPlacement] {F0 : FsFiles} {peer : AddrGhost}
    {s1 s2 s3 s4 : Nat} (hDropNz : lsmpl.base 547 ≠ 0#64) :
    IdentityVtablesPlacedOk
      (cliIdentityKitSpecPlaced E2E.HooksE.A0 cliIo.rd F0 cliWrOk peer s1 s2 s3 s4
        cliIdentityVtRoSym) :=
  cliIdentityKitSpecPlaced_vtables hDropNz

/-- `IdentityStoreKitPlacedRoClOkI` for CLI `IdentityFiles` at
`cliGhostExterns g (cliExternsPlaced mmpl W)`. -/
theorem cliIdKitRoClOkIE_cli_placed [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) {F0 : FsFiles}
    {peer : AddrGhost} {readStk s1 s2 s3 s4 : Nat}
    {vtSym : String} {readProg : Program} {jRead : Nat}
    [IsLsBlockProg readProg jRead (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : RunSkeleton.RunHooksPlaced E2E.HooksE.A0
      (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok readProg (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 readStk))
    (hs1 : trustShimNeedPlaced ≤ s1) (hs2 : trustPollNeedPlaced readStk ≤ s2)
    (hs3 : saveShimNeedPlaced ≤ s3) (hs4 : savePollNeedPlaced readStk ≤ s4)
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide) :
    IdentityStoreKitPlacedRoClOkI
      (cliIdentityKitSpecPlaced E2E.HooksE.A0 cliIo.rd F0 cliWrOk peer s1 s2 s3 s4 vtSym)
      (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  cliIdKitRoClOkIE_placed
    (readProg := readProg)
    (jRead := jRead)
    hDropNz
    (fun _ hp => hp.2)
    hh
    (RunSkeleton.cliReadFilePlaced_rocl_ok mmpl g W readStk hRead)
    (cliGhostExterns_blackBox mmpl g W)
    hs1 hs2 hs3 hs4
    hjRead hjRead_unmut

/-- `IdentityStoreKitPlacedOkI` for CLI `IdentityFiles` at
`cliGhostExterns g (cliExternsPlaced mmpl W)`. -/
theorem cliIdKitOkIE_cli_placed [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) {F0 : FsFiles}
    {peer : AddrGhost} {readStk s1 s2 s3 s4 : Nat}
    {vtSym : String} {readProg : Program} {jRead : Nat}
    [IsLsBlockProg readProg jRead (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : RunSkeleton.RunHooksPlaced E2E.HooksE.A0
      (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok readProg (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 readStk))
    (hs1 : trustShimNeedPlaced ≤ s1) (hs2 : trustPollNeedPlaced readStk ≤ s2)
    (hs3 : saveShimNeedPlaced ≤ s3) (hs4 : savePollNeedPlaced readStk ≤ s4)
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide) :
    IdentityStoreKitPlacedOkI
      (cliIdentityKitSpecPlaced E2E.HooksE.A0 cliIo.rd F0 cliWrOk peer s1 s2 s3 s4 vtSym)
      (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  cliIdKitOkIE_placed
    (readProg := readProg)
    (jRead := jRead)
    hDropNz
    (fun _ hp => hp.2)
    hh
    (RunSkeleton.cliReadFilePlaced_rocl_ok mmpl g W readStk hRead)
    (cliGhostExterns_blackBox mmpl g W)
    hs1 hs2 hs3 hs4
    hjRead hjRead_unmut

end CryptoVerification.SignalSession.Cli.KitInst.IdKit

namespace CryptoVerification.SignalSession.Cli.KitInst

export IdKit (cliExternsPlaced_blackBox cliGhostExterns_blackBox cliIdentityVtablesCli_placed
  cliIdKitRoClOkIE_cli_placed cliIdKitOkIE_cli_placed)

end CryptoVerification.SignalSession.Cli.KitInst

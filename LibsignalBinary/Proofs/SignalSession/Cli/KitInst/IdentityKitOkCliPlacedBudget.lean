/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkCliPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.ReadFileHookPlacedBudget
import Arm64.Trusted.Spec.Hoare

/-!
# Placed Budgeted CLI Instantiation of `IdentityStoreKitPlacedOkI`

Budget-threaded `IdentityStoreKitPlacedOkI` and `IdentityStoreKitPlacedRoClOkI` instances for
CLI `IdentityFiles` under `SessKitHooksPlaced` and `cliExternsPlaced mmpl W`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkCliPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement libsignalMutatedBlocks lsBlackBoxU8Sym
   ls_hook_ok_ultra_of_mem lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles IdentityVtablesPlacedOk subroutine_ok_withLsCodeRoLoaded_of_plain withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced lsReadFileSym)
open CryptoVerification.SignalSession.Cli (ReadRule)
open CryptoVerification.SignalSession.Cli.KitInst (cliGhostExterns_blackBox cliIdentityVtRoSym)
open CryptoVerification.SignalSession.Cli.KitInst.IdKit
  (cliIdentityKitSpecPlaced cliIdentityKitSpecPlaced_vtables dirPutStrNeedPlaced
   savePollNeedPlaced saveShimNeedPlaced trustPollNeedPlaced trustShimNeedPlaced)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliWrOk)
open CryptoVerification.SignalSession.Cli.Placed
  (blkPC_565 blkPl_565 lsProg_543 lsProg_565 lsProg_589)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks IsFsC cliGhostExterns)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon
  (ls_transfer_cl_to_lscro ls_transfer_lscro)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (IdentityStoreKitPlacedOkI)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a (DirGetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudget (dirPutStr_placed_ok_of_deps)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux (DirPutStrEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
  (IdentityStoreKitPlacedRoClOkI cliGrowOneDir_placed_ok cliIdKitOkIE_placed_of_polls
   cliIdentityKitDefaultBudgetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
  (SessKitHooksPlaced cliDirGet_placed_ok_of_sessHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.ReadFileHookPlacedBudget
  (cliReadFilePlaced_rocl_ok cliReadFilePlaced_rocl_ok_of_hookSat)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (CliGhostAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (dirPutStrSpecPlaced idSavePollSpecPlaced readFileSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.BranchesPlacedBudget
  (CliIdSavePollEnv publicKeySerialize_lscro_of_cli)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.SymPlacedBudget
  (idSavePoll_placed_ok_of_deps_core)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPollPlacedBudget
  (idTrustPoll_placed_ok_of_deps identityKey_decode_placed_ok publicKeyEq_placed_ok_of_bb)

theorem cliDirPutStr_placed_ok_of_sessHooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hh : SessKitHooksPlaced A lim H) :
    subroutine_ok (lsProg_543 H) (lsmpl.base 543)
      (dirPutStrSpecPlaced A lim DirPutStrEnv dirPutStrNeedPlaced) :=
  dirPutStr_placed_ok_of_deps hh.alloc hh.panics hh.memcpyRO hh.bcmp
    (jGrow := 586) (by decide) (by decide)
    (cliGrowOneDir_placed_ok hh.alloc hh.panics)
    (Nat.le_refl dirPutStrNeedPlaced)

/-- Assemble `IdentityStoreKitPlacedOkI` from `SessKitHooksPlaced`. -/
theorem cliIdKitOkIE_placed_of_sessHooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {readStk s1 s2 s3 s4 : Nat} {vtSym : String}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {readProg : Program} {jRead : Nat} [IsLsBlockProg readProg jRead H]
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hpathLen : ∀ p, pathOk p → p.length < 2 ^ 32)
    (hh : SessKitHooksPlaced A lim H)
    (hRead : subroutine_ok readProg (lsρ lsReadFileSym)
      (withLsCodeRoLoaded lsmpl (readFileSpecPlaced rd pathOk A lim readStk ReadEnv)))
    (h_bb : H lsBlackBoxU8Sym = some CryptoVerification.LibsignalSession.blackBoxHook)
    (hs1 : trustShimNeedPlaced ≤ s1) (hs2 : trustPollNeedPlaced readStk ≤ s2)
    (hs3 : saveShimNeedPlaced ≤ s3) (hs4 : savePollNeedPlaced readStk ≤ s4)
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide) :
    IdentityStoreKitPlacedOkI A lim
      (cliIdentityKitSpecPlaced A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 vtSym)
      (cliIdentityKitDefaultBudgetEnv A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 vtSym ReadEnv)
      H := by
  have hGet := cliDirGet_placed_ok_of_sessHooks hpathLen hh hRead hjRead hjRead_unmut
  have hPut := cliDirPutStr_placed_ok_of_sessHooks hh
  have hEq := publicKeyEq_placed_ok_of_bb h_bb
  have h566 := idTrustPoll_placed_ok_of_deps hh.alloc hGet
    (identityKey_decode_placed_ok (A := A) H) hEq hs2
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hSer := publicKeySerialize_lscro_of_cli
    (callerProg := (blkPC_565).rebase (blkPl_565).base H) hh.alloc (by decide)
  have hGet' := ls_transfer_lscro (callerProg := (blkPC_565).rebase (blkPl_565).base H)
    hGet (by decide) (by decide) (by decide)
  have hPut' := ls_transfer_lscro (callerProg := (blkPC_565).rebase (blkPl_565).base H)
    hPut (by decide) (by decide) (by decide)
  have hDec' := ls_transfer_cl_to_lscro (callerProg := (blkPC_565).rebase (blkPl_565).base H)
    (identityKey_decode_placed_ok (A := A) H) (by decide) (by decide) (by decide)
  have hEq' := ls_transfer_cl_to_lscro (callerProg := (blkPC_565).rebase (blkPl_565).base H)
    hEq (by decide) (by decide) (by decide)
  have h565 : subroutine_ok (lsProg_565 H) (lsmpl.base 565)
      (idSavePollSpecPlaced rd pathOk A lim
        (CliIdSavePollEnv rd (DirGetEnv PathEnv ReadEnv rd) DirPutStrEnv) s4) :=
    idSavePoll_placed_ok_of_deps_core hh.alloc hSer hGet' hPut' hDec' hEq' hs4
  exact cliIdKitOkIE_placed_of_polls hDropNz hh.alloc h566 h565 hs1 hs3

theorem cliIdKitRoClOkIE_placed_of_sessHooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {readStk s1 s2 s3 s4 : Nat} {vtSym : String}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {readProg : Program} {jRead : Nat} [IsLsBlockProg readProg jRead H]
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hpathLen : ∀ p, pathOk p → p.length < 2 ^ 32)
    (hh : SessKitHooksPlaced A lim H)
    (hRead : subroutine_ok readProg (lsρ lsReadFileSym)
      (withLsCodeRoLoaded lsmpl (readFileSpecPlaced rd pathOk A lim readStk ReadEnv)))
    (h_bb : H lsBlackBoxU8Sym = some CryptoVerification.LibsignalSession.blackBoxHook)
    (hs1 : trustShimNeedPlaced ≤ s1) (hs2 : trustPollNeedPlaced readStk ≤ s2)
    (hs3 : saveShimNeedPlaced ≤ s3) (hs4 : savePollNeedPlaced readStk ≤ s4)
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide) :
    IdentityStoreKitPlacedRoClOkI A lim
      (cliIdentityKitSpecPlaced A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 vtSym)
      (cliIdentityKitDefaultBudgetEnv A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 vtSym ReadEnv)
      H :=
  cliIdKitOkIE_placed_of_sessHooks hDropNz hpathLen hh hRead h_bb hs1 hs2 hs3 hs4
    hjRead hjRead_unmut

theorem cliIdentityVtablesCli_placed [LibsignalPlacement] {A : RustAlloc} {F0 : FsFiles}
    {peer : AddrGhost} {s1 s2 s3 s4 : Nat} (hDropNz : lsmpl.base 547 ≠ 0#64) :
    IdentityVtablesPlacedOk
      (cliIdentityKitSpecPlaced A cliIo.rd F0 cliWrOk peer s1 s2 s3 s4
        cliIdentityVtRoSym) :=
  cliIdentityKitSpecPlaced_vtables hDropNz

/-- Budget-threaded `IdentityStoreKitPlacedOkI` at
`cliGhostExterns g (cliExternsPlaced mmpl W)`. -/
theorem cliIdKitOkIE_cli_placed [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F0 : FsFiles}
    {peer : AddrGhost}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {readStk s1 s2 s3 s4 : Nat} {vtSym : String}
    {readProg : Program} {jRead : Nat}
    [IsLsBlockProg readProg jRead (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim g)
    (hAzFsT : HookFsTraced IsFsC g.allocZeroed)
    (hStrFsT : ∀ f, g.stringClone = some f → HookFsTraced IsFsC f)
    (hRead : subroutine_ok readProg (lsρ lsReadFileSym)
      (withLsCodeRoLoaded lsmpl (readFileSpecPlaced cliIo.rd cliWrOk A lim readStk ReadEnv)))
    (hs1 : trustShimNeedPlaced ≤ s1) (hs2 : trustPollNeedPlaced readStk ≤ s2)
    (hs3 : saveShimNeedPlaced ≤ s3) (hs4 : savePollNeedPlaced readStk ≤ s4)
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide) :
    IdentityStoreKitPlacedOkI A lim
      (cliIdentityKitSpecPlaced A.repAlloc cliIo.rd F0 cliWrOk peer s1 s2 s3 s4 vtSym)
      (cliIdentityKitDefaultBudgetEnv A.repAlloc cliIo.rd F0 cliWrOk peer s1 s2 s3 s4 vtSym ReadEnv)
      (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  cliIdKitOkIE_placed_of_sessHooks hDropNz (fun _ hp => hp.2)
    (SessKitHooksPlaced.cli mmpl g W hG hAzFsT hStrFsT)
    hRead (cliGhostExterns_blackBox mmpl g W) hs1 hs2 hs3 hs4 hjRead hjRead_unmut

theorem cliIdKitRoClOkIE_cli_placed [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F0 : FsFiles}
    {peer : AddrGhost}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {readStk s1 s2 s3 s4 : Nat} {vtSym : String}
    {readProg : Program} {jRead : Nat}
    [IsLsBlockProg readProg jRead (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim g)
    (hAzFsT : HookFsTraced IsFsC g.allocZeroed)
    (hStrFsT : ∀ f, g.stringClone = some f → HookFsTraced IsFsC f)
    (hRead : subroutine_ok readProg (lsρ lsReadFileSym)
      (withLsCodeRoLoaded lsmpl (readFileSpecPlaced cliIo.rd cliWrOk A lim readStk ReadEnv)))
    (hs1 : trustShimNeedPlaced ≤ s1) (hs2 : trustPollNeedPlaced readStk ≤ s2)
    (hs3 : saveShimNeedPlaced ≤ s3) (hs4 : savePollNeedPlaced readStk ≤ s4)
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide) :
    IdentityStoreKitPlacedRoClOkI A lim
      (cliIdentityKitSpecPlaced A.repAlloc cliIo.rd F0 cliWrOk peer s1 s2 s3 s4 vtSym)
      (cliIdentityKitDefaultBudgetEnv A.repAlloc cliIo.rd F0 cliWrOk peer s1 s2 s3 s4 vtSym ReadEnv)
      (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  cliIdKitOkIE_cli_placed mmpl g W hDropNz hG hAzFsT hStrFsT hRead hs1 hs2 hs3 hs4
    hjRead hjRead_unmut

theorem cliIdKitOkIE_cli_placed_of_read [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F0 : FsFiles}
    {peer : AddrGhost}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {readStk s1 s2 s3 s4 : Nat} {vtSym : String}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim g)
    (hAzFsT : HookFsTraced IsFsC g.allocZeroed)
    (hStrFsT : ∀ f, g.stringClone = some f → HookFsTraced IsFsC f)
    (hRead : subroutine_ok (lsProg_589 (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym) (readFileSpecPlaced cliIo.rd cliWrOk A lim readStk ReadEnv))
    (hs1 : trustShimNeedPlaced ≤ s1) (hs2 : trustPollNeedPlaced readStk ≤ s2)
    (hs3 : saveShimNeedPlaced ≤ s3) (hs4 : savePollNeedPlaced readStk ≤ s4) :
    IdentityStoreKitPlacedOkI A lim
      (cliIdentityKitSpecPlaced A.repAlloc cliIo.rd F0 cliWrOk peer s1 s2 s3 s4 vtSym)
      (cliIdentityKitDefaultBudgetEnv A.repAlloc cliIo.rd F0 cliWrOk peer s1 s2 s3 s4 vtSym ReadEnv)
      (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  cliIdKitOkIE_cli_placed mmpl g W
    (readProg := lsProg_589 (cliGhostExterns g (cliExternsPlaced mmpl W))) (jRead := 589)
    hDropNz hG hAzFsT hStrFsT
    (cliReadFilePlaced_rocl_ok mmpl g W readStk (i := 589) hRead)
    hs1 hs2 hs3 hs4 (by decide) (by decide)

theorem cliIdKitRoClOkIE_cli_placed_of_read [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F0 : FsFiles}
    {peer : AddrGhost}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {readStk s1 s2 s3 s4 : Nat} {vtSym : String}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim g)
    (hAzFsT : HookFsTraced IsFsC g.allocZeroed)
    (hStrFsT : ∀ f, g.stringClone = some f → HookFsTraced IsFsC f)
    (hRead : subroutine_ok (lsProg_589 (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym) (readFileSpecPlaced cliIo.rd cliWrOk A lim readStk ReadEnv))
    (hs1 : trustShimNeedPlaced ≤ s1) (hs2 : trustPollNeedPlaced readStk ≤ s2)
    (hs3 : saveShimNeedPlaced ≤ s3) (hs4 : savePollNeedPlaced readStk ≤ s4) :
    IdentityStoreKitPlacedRoClOkI A lim
      (cliIdentityKitSpecPlaced A.repAlloc cliIo.rd F0 cliWrOk peer s1 s2 s3 s4 vtSym)
      (cliIdentityKitDefaultBudgetEnv A.repAlloc cliIo.rd F0 cliWrOk peer s1 s2 s3 s4 vtSym ReadEnv)
      (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  cliIdKitOkIE_cli_placed_of_read mmpl g W hDropNz hG hAzFsT hStrFsT hRead hs1 hs2 hs3 hs4

theorem cliIdKitOkIE_cli_placed_of_readHookSat [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F0 : FsFiles}
    {peer : AddrGhost}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {readStk s1 s2 s3 s4 : Nat} {vtSym : String}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim g)
    (hAzFsT : HookFsTraced IsFsC g.allocZeroed)
    (hStrFsT : ∀ f, g.stringClone = some f → HookFsTraced IsFsC f)
    (hReadHook : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk A lim readStk ReadEnv))
    (hs1 : trustShimNeedPlaced ≤ s1) (hs2 : trustPollNeedPlaced readStk ≤ s2)
    (hs3 : saveShimNeedPlaced ≤ s3) (hs4 : savePollNeedPlaced readStk ≤ s4) :
    IdentityStoreKitPlacedOkI A lim
      (cliIdentityKitSpecPlaced A.repAlloc cliIo.rd F0 cliWrOk peer s1 s2 s3 s4 vtSym)
      (cliIdentityKitDefaultBudgetEnv A.repAlloc cliIo.rd F0 cliWrOk peer s1 s2 s3 s4 vtSym ReadEnv)
      (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  cliIdKitOkIE_cli_placed mmpl g W
    (readProg := lsProg_589 (cliGhostExterns g (cliExternsPlaced mmpl W))) (jRead := 589)
    hDropNz hG hAzFsT hStrFsT
    (cliReadFilePlaced_rocl_ok_of_hookSat readStk (i := 589) hReadHook)
    hs1 hs2 hs3 hs4 (by decide) (by decide)

theorem cliIdKitRoClOkIE_cli_placed_of_readHookSat [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F0 : FsFiles}
    {peer : AddrGhost}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {readStk s1 s2 s3 s4 : Nat} {vtSym : String}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim g)
    (hAzFsT : HookFsTraced IsFsC g.allocZeroed)
    (hStrFsT : ∀ f, g.stringClone = some f → HookFsTraced IsFsC f)
    (hReadHook : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk A lim readStk ReadEnv))
    (hs1 : trustShimNeedPlaced ≤ s1) (hs2 : trustPollNeedPlaced readStk ≤ s2)
    (hs3 : saveShimNeedPlaced ≤ s3) (hs4 : savePollNeedPlaced readStk ≤ s4) :
    IdentityStoreKitPlacedRoClOkI A lim
      (cliIdentityKitSpecPlaced A.repAlloc cliIo.rd F0 cliWrOk peer s1 s2 s3 s4 vtSym)
      (cliIdentityKitDefaultBudgetEnv A.repAlloc cliIo.rd F0 cliWrOk peer s1 s2 s3 s4 vtSym ReadEnv)
      (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  cliIdKitOkIE_cli_placed_of_readHookSat mmpl g W hDropNz hG hAzFsT hStrFsT hReadHook
    hs1 hs2 hs3 hs4

end LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkCliPlacedBudget

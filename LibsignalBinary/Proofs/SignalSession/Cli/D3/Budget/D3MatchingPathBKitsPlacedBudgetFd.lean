/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
import LibsignalBinary.Proofs.PeakBudget.CliDpPollTrustedWideBridge
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3MatchingPathBAuxPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MatchingPathBF3 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureEntryPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage1InstPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.InnerInstPlacedBudgetFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget -- proof-setup: allow-public-import
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Store.SerSeqFreePlacedBudget

/-!
# `FdsGe3Closed`-Threaded Poll Store Kits and Slot-`520` Adapters for Matching-Session Path B

Assembles the `SessionOnlyKitPlacedOkSE` and `IdentityStoreKitPlacedOkI` poll kits directly from a
block-`589` `dirGetSpecPlaced` contract, and adapts block-`520` `subroutine_ok` / `.OkPlaced`
contracts at `AllocWithFds.withFds A` to `withPreFdsGe3Closed` / `slotWithPreFdsGe3Closed` at `A`.
-/

public section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3MatchingPathBKitsPlacedBudgetFd

open Arm64 Arm64.Obj ProofLib SepProp
open CryptoGames.LibsignalSession (IdentityKey)
open CryptoGames.LibsignalSessionApi (ApiError SessionRecord)
open CryptoVerification (
  LibsignalFrozen LibsignalHooks LibsignalPlacement lsmpl lsρ withLsCodeLoaded
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (loadCallStack stageP1CallStack)
open CryptoVerification.CliHandshake.RespClosurePlaced (lsProg_518)
open scoped CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.E2E (UnreachedPqxdhPrimitives)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.E2E.Record.Placed (lsProg_52)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  FsAt FsFiles LibsignalCodeRoLoaded withLsCodeRoLoaded
)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal preKeyMsgAt)
open CryptoVerification.LibsignalTripleRatchet (extHookStack extract_withLsFrozen withLsFrozen)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost protocolAddressAt)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli (
  ReadRule StoresGhost cliIdentityVtSym cliKyberPreKeyVtSym cliPreKeyVtSym cliSessionVtSym
  cliSignedPreKeyVtSym
)
open CryptoVerification.SignalSession.Cli.KitInst (cliSessionStoreSpec)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliWrOk coinsInstalledPlaced storesAt)
open CryptoVerification.SignalSession.Cli.Placed (lsProg_589)
open CryptoVerification.SignalSession.Cli.RunCompose (
  DecPkGhost RunNeeds RunSem decResAt dpSlotArgsPlaced mkSlot slotOut slotTrace
)
open CryptoVerification.SignalSession.Cli.RunGlue (
  CliGhostHooks cliExternsPlaced_row cliGhostExterns cliGhostExterns_other
)
open CryptoVerification.SignalSession.Cli.RunProofs (dpCxAt dpFutStartAt)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (
  LsTokenInit cliKitStk cliPollIdKitPlaced cliPollSessKit cliPollSessKitPlaced
  dpCxAt_entails_memRegion32 dpPollEntryPlaced dpPollProgPlaced
)
open CryptoVerification.SignalSession.Cli.RunSkeleton (CalleeSlot.OkPlaced RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (
  FilesOkPeer blackBox_row_placed scopeIn scopeKit
)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.PeakBudget.CliDpPollTrustedWideBridge (not_fitsEnv_top)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift (PeerSpqrStateTight640)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0 (
  realCliDecPkBinaryWideSlotEnvCmkDom0Fixed' realCliDecPkBinaryWideSlotEnvCmkDom0GuardedFixed'
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3 (DecPkOkPathB)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MatchingPathBF3 (cliRunSemPathB)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a (DirGetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (
  FdsGe3Closed withFdsGe3Closed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds (
  withFds withFds_pool_enforced withFds_repAlloc
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget (
  RunSlotEnvs slotsOfSigPkFrozenPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureEntryPlacedBudget (
  dpPollEntrySpatialPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageDefsPlacedBudget (
  StageP1OkEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget (
  RunHooksPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget (
  cliIdKitPlacedOkI_full serContractsX_of_runHooks
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage1InstPlacedBudget (
  stageP1OkPostAt stageP1OkPreAt stageP1_ok_placed_of_kits
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget (
  cliPollIdBudgetEnv cliPollSessBudgetEnv cliPollSessSeqFreeBudgetEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.InnerInstPlacedBudgetFd (
  cliIdKitOkIE_of_dirGet cliSessKitOkSE_of_dirGet cliSessKitOkSE_seqFree_of_dirGet
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudgetFd (
  slotFramePlaced_withFds_enforced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd (
  extract_withPreFdsGe3Closed slotWithPreFdsGe3Closed
  subroutine_ok_withPreFdsGe3Closed_of_withFdsGe3Closed withPreFdsGe3Closed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget (
  DpPollGhostStateBudget decPkSlotSpecBasePlaced decPkSlotSpecFrozenPlaced decPkSlotSpecPlaced
  decPkSlotSpecPlacedOf dpPollSpecStateBudget dpSlotPollKStatePlaced slotFramePlaced
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (
  IdentityStoreKitPlacedOkI SessionOnlyKitPlacedOkSE
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (
  dirGetSpecPlaced readFileSpecPlaced sessDeserializeSpecPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXPlacedBudget (
  serializeCanonX_placed_ok_of_serContractsX
)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SerSeqFreePlacedBudget (
  serializeCanonSeqFree_placed_ok_of_serContractsX
)

/-! ## 1. `RunHooksPlaced` Bridge & `blackBox` Row Lookup -/

theorem toSkeletonRunHooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hh : RunHooksPlaced A lim ext) :
    LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced A lim ext :=
  { alloc := hh.alloc, allocFs := hh.allocFs, panics := hh.panics, memcpyRO := hh.memcpyRO,
    bcmp := hh.bcmp, fs := hh.fs, utf8 := hh.utf8, memrchr := hh.memrchr,
    codecHooks := hh.codecHooks, allocZeroed := hh.allocZeroed, stringClone := hh.stringClone,
    formatInner := hh.formatInner }

private theorem cliGhostExterns_blackBox_row (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks) :
    cliGhostExterns gh (cliExternsPlaced mmpl W) CryptoVerification.lsBlackBoxU8Sym =
      some CryptoVerification.LibsignalSession.blackBoxHook :=
  (cliGhostExterns_other gh (cliExternsPlaced mmpl W)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)).trans
    (cliExternsPlaced_row mmpl W (blackBox_row_placed mmpl W))

/-- Discharges the unused `_hread` hypothesis in `StageP2MatchedFramedCliPlacedStmt` (where
`StageP2Matched` performs zero `read_file` calls and `ReadEnv` appears nowhere else in the
statement) by instantiating `ReadEnv := fun _ _ _ => True` via `not_fitsEnv_top`. -/
theorem subroutine_ok_readFile_top_unused {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64}
    (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat) :
    subroutine_ok prog entry
      (readFileSpecPlaced rd pathOk A lim stk (fun _ _ _ => True)) := by
  refine subroutine_ok.of_codeLoaded fun (x, st) R s0 _ _ hpre _ _ => ?_
  dsimp only [readFileSpecPlaced] at hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact False.elim (not_fitsEnv_top M lim st hpre.1.2.2.2.2.2)

/-! ## 2. Poll Store Kits from Block-`589` `dirGetSpecPlaced` -/

theorem cliPollSess_kitPlacedOkSE_untrusted_of_dirGet [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F0 : FsFiles} {peer : AddrGhost} {B : RunBudgets}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGet : subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 589)
      (dirGetSpecPlaced cliIo.rd cliWrOk A lim (DirGetEnv PathEnv ReadEnv cliIo.rd) B.dirGetNeed))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv)) :
    SessionOnlyKitPlacedOkSE A lim
      (cliPollSessKitPlaced A.repAlloc F0 scopeKit peer (cliKitStk B))
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget.cliPollSessBudgetEnv
        A.repAlloc F0 peer B ReadEnv DeserEnv)
      scopeKit encodeRecord (cliGhostExterns gh (cliExternsPlaced mmpl W)) := by
  have : CryptoVerification.IsLsBlockProg
      (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) 518
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) := inferInstance
  exact cliSessKitOkSE_of_dirGet
    (deserProg := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (deserBlk := 518)
    (serProg := lsProg_52 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (serBlk := 52)
    hDropNz (LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget.SessKitHooksPlaced.of_runHooks hh)
    hGet hDeser
    (serializeCanonX_placed_ok_of_serContractsX (serContractsX_of_runHooks mmpl gh W hh))
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    (by decide) (by decide) (by decide) (by decide)

theorem cliPollId_kitPlacedOkI_untrusted_of_dirGet [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F0 : FsFiles} {peer : AddrGhost} {B : RunBudgets}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGet : subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 589)
      (dirGetSpecPlaced cliIo.rd cliWrOk A lim (DirGetEnv PathEnv ReadEnv cliIo.rd) B.dirGetNeed)) :
    IdentityStoreKitPlacedOkI A lim
      (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B))
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget.cliPollIdBudgetEnv
        A.repAlloc F0 peer B ReadEnv)
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  cliIdKitPlacedOkI_full
    (cliIdKitOkIE_of_dirGet hDropNz hh hGet (cliGhostExterns_blackBox_row mmpl gh W)
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))

theorem cliPollSess_kitPlacedOkSE_of_dirGet [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGet : subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 589)
      (dirGetSpecPlaced cliIo.rd cliWrOk A lim (DirGetEnv PathEnv ReadEnv cliIo.rd) B.dirGetNeed))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv)) :
    SessionOnlyKitPlacedOkSE A lim
      (cliPollSessKitPlaced A.repAlloc F0 scopeKit peer (cliKitStk B))
      (cliPollSessBudgetEnv A.repAlloc F0 peer (cliKitStk B) DeserEnv ReadEnv)
      scopeKit encodeRecord (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  cliPollSess_kitPlacedOkSE_untrusted_of_dirGet mmpl gh W hDropNz (toSkeletonRunHooks hh) hGet hDeser

theorem cliPollSess_seqFreeKitPlacedOkSE_of_dirGet [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGet : subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 589)
      (dirGetSpecPlaced cliIo.rd cliWrOk A lim (DirGetEnv PathEnv ReadEnv cliIo.rd) B.dirGetNeed))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv)) :
    SessionOnlyKitPlacedOkSE A lim
      (cliPollSessKitPlaced A.repAlloc F0 scopeKit peer (cliKitStk B))
      (cliPollSessSeqFreeBudgetEnv A.repAlloc F0 peer (cliKitStk B) DeserEnv ReadEnv)
      scopeKit encodeRecord (cliGhostExterns gh (cliExternsPlaced mmpl W)) := by
  have hhSk := toSkeletonRunHooks hh
  have : CryptoVerification.IsLsBlockProg
      (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) 518
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) := inferInstance
  exact cliSessKitOkSE_seqFree_of_dirGet
    (deserProg := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (deserBlk := 518)
    (serProg := lsProg_52 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (serBlk := 52)
    hDropNz hhSk hGet hDeser
    (serializeCanonSeqFree_placed_ok_of_serContractsX (serContractsX_of_runHooks mmpl gh W hhSk))
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    (by decide) (by decide) (by decide) (by decide)

theorem cliPollId_kitPlacedOkI_of_dirGet [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGet : subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 589)
      (dirGetSpecPlaced cliIo.rd cliWrOk A lim (DirGetEnv PathEnv ReadEnv cliIo.rd) B.dirGetNeed)) :
    IdentityStoreKitPlacedOkI A lim
      (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B))
      (cliPollIdBudgetEnv A.repAlloc F0 peer (cliKitStk B) ReadEnv)
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  cliPollId_kitPlacedOkI_untrusted_of_dirGet mmpl gh W hDropNz (toSkeletonRunHooks hh) hGet

theorem stageP1_ok_placed_inst_of_dirGet [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost) (remoteIdKey : IdentityKey)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGet : subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 589)
      (dirGetSpecPlaced cliIo.rd cliWrOk A lim (DirGetEnv PathEnv ReadEnv cliIo.rd) B.dirGetNeed))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv)) :
    let σ := cliKitStk B
    let kit := cliPollSessKitPlaced A.repAlloc F0 scopeKit peer σ
    let ikit := cliPollIdKitPlaced A.repAlloc F0 peer σ
    let kitEnv := cliPollSessBudgetEnv A.repAlloc F0 peer σ DeserEnv ReadEnv
    let ikitEnv := cliPollIdBudgetEnv A.repAlloc F0 peer σ ReadEnv
    ∀ (st_b : M.σ) (st : kit.StoreState) (ist : ikit.IdState),
      stageP1CallStack kit ikit ≤ 2 ^ 64 →
      kit.addrOk peer.val →
      ikit.addrOk peer.val →
      (∀ ans, kit.loadRel st peer.val ans → ans.isOk = true) →
      (∀ ans, ikit.trustRel ist peer.val remoteIdKey .receiving ans → ans = .ok true) →
      FitsEnv M lim st_b (StageP1OkEnv kit kitEnv st ikit ikitEnv ist peer.val remoteIdKey) →
      ∀ (s0 : State)
        (sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
         sessStorePtr idStorePtr
         preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
         kyberStorePtr kyberStoreVt rngPtr
         v_sp0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 : BitVec 64)
        (b_390 b_4f2 : BitVec 8),
        CryptoVerification.LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem →
        FsAt
          (fun F => kit.envOk F ∧ ikit.envOk F) (kit.Quiet ∧ ikit.Quiet)
          (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s0 →
        s0.pc = dpPollEntryPlaced →
        s0.status = .Running →
        (s0.sp &&& 15#64 == 0#64) = true →
        s0.sp - 0xcd0#64 = sp →
        s0.readReg64 .x0 = outPtr →
        s0.readReg64 .x1 = coroPtr →
        s0.readReg64 .x2 = ctxPtr →
        SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
          (dpPollEntryPlaced + 0x868#64) s0
          (stageP1OkPreAt A lim st_b kit ikit st ist peer remoteIdKey s0
            sp coroPtr msgPtr remoteAddrPtr localAddrPtr
            sessStorePtr idStorePtr
            preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
            kyberStorePtr kyberStoreVt rngPtr
            v_sp0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 b_390 b_4f2)
          (stageP1OkPostAt A lim st_b scopeKit encodeRecord kit kitEnv ikit ikitEnv st ist
            peer remoteIdKey s0
            sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
            sessStorePtr idStorePtr
            preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
            kyberStorePtr kyberStoreVt rngPtr)
          (fun _ _ => False) :=
  stageP1_ok_placed_of_kits mmpl gh W B F0 peer remoteIdKey hDropNz hh
    (cliPollSess_kitPlacedOkSE_of_dirGet mmpl gh W B F0 peer hDropNz hh hGet hDeser)
    (cliPollId_kitPlacedOkI_of_dirGet mmpl gh W B F0 peer hDropNz hh hGet)

/-! ## 3. Slot-`520` `decPkSlotSpecFrozenPlaced (withFds A)` → `withPreFdsGe3Closed` Adapters -/

/-- Convert a Slot-`520` `subroutine_ok` proved at `AllocWithFds.withFds A` (when
`lim.enforced = true`) into the `withFdsGe3Closed`-wrapped `decPkSlotSpecFrozenPlaced` at `A`. -/
theorem decPkSlotSpecFrozenPlaced_withFds_to_withFds [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true)
    {prog : Program} {entry : BitVec 64}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {S : RunSem} {stk : Nat}
    (h : subroutine_ok prog entry (decPkSlotSpecFrozenPlaced (withFds A) lim DecPkEnv S stk)) :
    subroutine_ok prog entry
      (withFdsGe3Closed (decPkSlotSpecFrozenPlaced A lim DecPkEnv S stk)) := by
  refine subroutine_ok_mono h (fun (x, st) R s0 hpre => ?_) (fun (x, st) R s0 sf hpost => ?_)
  · dsimp only [withFdsGe3Closed, decPkSlotSpecFrozenPlaced, decPkSlotSpecPlacedOf,
      decPkSlotSpecBasePlaced, withFds_repAlloc] at hpre ⊢
    rw [slotFramePlaced_withFds_enforced A henf]
    refine Eq.mp (congrArg (s0.mem ⊨ ·) ?_) hpre; sep_ac_rfl
  · dsimp only [withFdsGe3Closed, decPkSlotSpecFrozenPlaced, decPkSlotSpecPlacedOf,
      decPkSlotSpecBasePlaced, decPkSlotSpecPlaced, withLsCodeRoLoaded,
      withFds_repAlloc] at hpost ⊢
    simp only [sepConj_assoc, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨evs, g', e, hpost⟩
    rw [withFds_pool_enforced A henf (M.stepEvents evs st) sf] at hpost
    exact ⟨evs, g', e, Satisfies.of_eq hpost (by sep_ac_rfl)⟩

/-- Pre-side cutoff form (`SkeletonPlacedBudgetFd.withPreFdsGe3Closed`): drops post-side
`FdsGe3Closed` at the Slot-`520` boundary (`0` reads after `decrypt_prekey`). -/
theorem decPkSlotSpecFrozenPlaced_withFds_to_preFd [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true)
    {prog : Program} {entry : BitVec 64}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {S : RunSem} {stk : Nat}
    (h : subroutine_ok prog entry (decPkSlotSpecFrozenPlaced (withFds A) lim DecPkEnv S stk)) :
    subroutine_ok prog entry
      (withPreFdsGe3Closed (decPkSlotSpecFrozenPlaced A lim DecPkEnv S stk)) :=
  subroutine_ok_withPreFdsGe3Closed_of_withFdsGe3Closed
    (decPkSlotSpecFrozenPlaced_withFds_to_withFds henf h)

/-- Slot-level lift from `(slotsOfSigPkFrozenPlaced (withFds A) …).decryptPrekey.OkPlaced` to
`(slotWithPreFdsGe3Closed (slotsOfSigPkFrozenPlaced A …).decryptPrekey).OkPlaced`. -/
theorem slotOk_decPkFrozenPlaced_withFds_to_preFd [LibsignalPlacement]
    {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true)
    {sEnvs : RunSlotEnvs} {S : RunSem} {needs : RunNeeds}
    (h : (slotsOfSigPkFrozenPlaced (withFds A) lim sEnvs S needs).decryptPrekey.OkPlaced
      prog entry) :
    (slotWithPreFdsGe3Closed
      (slotsOfSigPkFrozenPlaced A lim sEnvs S needs).decryptPrekey).OkPlaced prog entry :=
  fun stk h1 h2 => decPkSlotSpecFrozenPlaced_withFds_to_preFd henf (h stk h1 h2)

/-- Lifts an unguarded `DecPkEnv₀` block-`520` `slotWithPreFdsGe3Closed` `.OkPlaced` contract to
`realCliDecPkBinaryWideSlotEnvCmkDom0GuardedFixed' X W`, discharging `¬ PeerSpqrStateTight640` via
`not_fitsEnv_top`. -/
theorem slotOk_preFd_guarded_of_unguarded [LibsignalPlacement]
    {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    {DecPkEnv₀ : DecPkGhost → List AllocEvent → Prop}
    {sEnvs : RunSlotEnvs} {needs : RunNeeds}
    (hsEnv : sEnvs.decryptPrekey = realCliDecPkBinaryWideSlotEnvCmkDom0GuardedFixed' X W)
    (hUnguarded :
      (slotWithPreFdsGe3Closed
        (slotsOfSigPkFrozenPlaced A lim { sEnvs with decryptPrekey := DecPkEnv₀ }
          (cliRunSemPathB X W) needs).decryptPrekey).OkPlaced prog entry)
    (hBridge : ∀ x evs,
      FilesOkPeer scopeIn x.F x.peer.val →
      DecPkOkPathB ⟨W.C, W.Q⟩ scopeIn x.F x.peer.val x.me.val x.msg →
      PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val →
      DecPkEnv₀ x evs →
      realCliDecPkBinaryWideSlotEnvCmkDom0Fixed' X W x evs) :
    (slotWithPreFdsGe3Closed
      (slotsOfSigPkFrozenPlaced A lim sEnvs (cliRunSemPathB X W) needs).decryptPrekey).OkPlaced
      prog entry := by
  intro stk hstk1 hstk2
  have hSub0 := hUnguarded stk hstk1 hstk2
  dsimp only [slotWithPreFdsGe3Closed, slotsOfSigPkFrozenPlaced, mkSlot] at hSub0 ⊢
  rw [hsEnv]
  refine subroutine_ok.of_codeLoaded fun (x, st) R s0 hpc hrun hpre0 hsp _ => ?_
  obtain ⟨hfds, hpre⟩ := extract_withPreFdsGe3Closed hpre0
  dsimp only [
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.decPkSlotSpecFrozenPlaced,
    decPkSlotSpecFrozenPlaced, decPkSlotSpecPlacedOf, decPkSlotSpecBasePlaced] at hpre
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hF0, hfOk, hdOk, hsp_le, hfit⟩,
    hrest⟩ := hpre
  by_cases hTight : PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val
  · have hdOk' : DecPkOkPathB ⟨W.C, W.Q⟩ scopeIn x.F x.peer.val x.me.val x.msg :=
      ⟨hdOk.party, hdOk.loadedMatch, hdOk.keyPairLt, hdOk.preKeysWf, hdOk.baseKeysLt⟩
    have hImp : ∀ evs, DecPkEnv₀ x evs →
        realCliDecPkBinaryWideSlotEnvCmkDom0GuardedFixed' X W x evs :=
      fun evs hevs0 _ => hBridge x evs hfOk.1 hdOk' hTight hevs0
    have hfit0 : FitsEnv M lim st (DecPkEnv₀ x) :=
      fun evs hevs0 => hfit evs (hImp evs hevs0)
    have hpre1 :
        s0.mem ⊨
          (withPreFdsGe3Closed
            (LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.decPkSlotSpecFrozenPlaced
              A lim DecPkEnv₀ (cliRunSemPathB X W) stk)).pre (x, st) s0 ∗ R := by
      dsimp only [withPreFdsGe3Closed]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hfds, ?_⟩
      dsimp only [
        LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.decPkSlotSpecFrozenPlaced,
        decPkSlotSpecFrozenPlaced, decPkSlotSpecPlacedOf, decPkSlotSpecBasePlaced]
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hF0, hfOk, hdOk, hsp_le, hfit0⟩,
        hrest⟩
    refine hSub0.mono_outcome (x, st) R s0 hpc hrun hpre1 hsp fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hpost⟩ | hp | hex | ho
    · refine Or.inl ⟨hret, hcc, Satisfies.mono (sepConj_mono_left ?_) hpost⟩
      dsimp only [withPreFdsGe3Closed,
        LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.decPkSlotSpecFrozenPlaced,
        decPkSlotSpecFrozenPlaced, decPkSlotSpecPlacedOf, decPkSlotSpecBasePlaced,
        decPkSlotSpecPlaced, withLsCodeRoLoaded]
      refine Entails.sepExists_elim fun evs => Entails.sepExists_right evs ?_
      refine Entails.sepExists_elim fun g' => Entails.sepExists_right g' ?_
      refine Entails.sepExists_elim fun e => Entails.sepExists_right e ?_
      refine Entails.pure_left fun ⟨hevs0, htr, hout_e⟩ => ?_
      have hPure :
          (realCliDecPkBinaryWideSlotEnvCmkDom0GuardedFixed' X W x evs ∧ slotTrace s0 sf ∧
            slotOut ((cliRunSemPathB X W).decryptPrekey x.F x.peer.val x.me.val x.msg x.coins)
              g' e s0 sf) = True :=
        propext ⟨fun _ => trivial, fun _ => ⟨hImp evs hevs0, htr, hout_e⟩⟩
      rw [hPure, pure_true, emp_sepConj]
      exact Entails.refl _
    · exact Or.inr (Or.inl hp)
    · exact Or.inr (Or.inr (Or.inl hex))
    · exact Or.inr (Or.inr (Or.inr ho))
  · exfalso
    refine not_fitsEnv_top M lim st (fun evs _ => ?_)
    exact hfit evs (fun h => False.elim (hTight h))

/-! ## 4. Poll-Entry Unpack & Stack Helpers for D3 `PathB` -/

structure DpPollEntryPurePathBFrozenPlacedBudget [LibsignalPlacement]
    {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S : RunSem} (stk' : Nat)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (s0 : State) : Prop where
  fr : LibsignalFrozen lsmpl s0.mem
  ro : LibsignalCodeRoLoaded lsmpl s0.mem
  x0 : s0.readReg64 .x0 = y.out
  x1 : s0.readReg64 .x1 = y.fut
  x2 : s0.readReg64 .x2 = y.cx
  stk_le_sp : stk' ≤ s0.sp.toNat
  files_eq : s0.fs.files = y.g.F
  coins_lt : y.g.coins.length < 2 ^ 63
  filesOkPeer : FilesOkPeer Scope y.g.F y.g.peer.val
  decPkOk : DecPkOkPathB ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg
  fits : FitsEnv M lim y.st (DecPkEnv y.g)

theorem dpPollPre_unpack_pathB_frozen_placedBudget [LibsignalPlacement]
    {W : CliHooks} {X : UnreachedPqxdhPrimitives}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S : RunSem}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hSemOk : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      FilesOkPeer Scope F peer ∧ DecPkOkPathB ⟨W.C, W.Q⟩ Scope F peer me pm)
    (stk' : Nat) (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (R : SepProp) (s0 : State) (hpre : s0.mem ⊨
      (withLsFrozen lsmpl
        (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk')).pre y s0 ∗ R) :
    DpPollEntryPurePathBFrozenPlacedBudget (X := X) (W := W) (Scope := Scope) stk' y s0 ∧
      (s0.mem ⊨ dpPollEntrySpatialPlaced stk' y s0 R) := by
  obtain ⟨hfr, hpre0⟩ := extract_withLsFrozen hpre
  have hro : LibsignalCodeRoLoaded lsmpl s0.mem :=
    CryptoVerification.LibsignalTripleRatchet.Record.LibsignalCodeRoLoaded.of_libsignalFrozen hfr
  have h2 : s0.mem ⊨
      ⌜s0.readReg64 .x0 = y.out ∧ s0.readReg64 .x1 = y.fut ∧ s0.readReg64 .x2 = y.cx ∧
        (dpSlotArgsPlaced y.g).length = 13 ∧ stk' ≤ s0.sp.toNat⌝ ∗ (memRegion y.out 48 ∗
        dpFutStartAt y.fut (dpSlotArgsPlaced y.g) ∗ dpCxAt y.cx ∗
        (⌜s0.fs.files = y.g.F ∧ S.filesOk y.g.F y.g.peer.val y.g.me.val ∧
            S.decPkOk y.g.F y.g.peer.val y.g.me.val y.g.msg ∧ FitsEnv M lim y.st (DecPkEnv y.g)⌝ ∗
          (⌜y.g.coins.length < 2 ^ 63⌝ ∗
            (storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
              protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
              protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
              coinsInstalledPlaced y.g.coinsP y.g.coins ∗ LsTokenInit ∗
              lsLogOff ∗
              A.pool lim y.st s0 ∗ preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
              stackAt s0.sp stk' ∗ R)))) := by
    simpa only [dpPollSpecStateBudget, dpSlotPollKStatePlaced, slotFramePlaced,
      sepConj_assoc] using hpre0
  rw [satisfies_pure_sepConj] at h2
  rcases h2 with ⟨⟨hx0, hx1, hx2, _, hstk_sp⟩, h3⟩
  have h3' : s0.mem ⊨
      ⌜s0.fs.files = y.g.F ∧ S.filesOk y.g.F y.g.peer.val y.g.me.val ∧
          S.decPkOk y.g.F y.g.peer.val y.g.me.val y.g.msg ∧ FitsEnv M lim y.st (DecPkEnv y.g)⌝ ∗
        (⌜y.g.coins.length < 2 ^ 63⌝ ∗ (dpCxAt y.cx ∗ (memRegion y.out 48 ∗
              dpFutStartAt y.fut (dpSlotArgsPlaced y.g) ∗
              storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
              protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
              protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
              coinsInstalledPlaced y.g.coinsP y.g.coins ∗ LsTokenInit ∗
              lsLogOff ∗
              A.pool lim y.st s0 ∗ preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
              stackAt s0.sp stk' ∗ R))) := by
    convert h3 using 1
    sep_ac_rfl
  rw [satisfies_pure_sepConj] at h3'
  rcases h3' with ⟨⟨hfiles, hfOk, hdOk, hfits⟩, h4⟩
  rw [satisfies_pure_sepConj] at h4
  rcases h4 with ⟨hcoins_lt, h5⟩
  obtain ⟨hfPeer, hdecOk⟩ := hSemOk y.g.F y.g.peer.val y.g.me.val y.g.msg hfOk hdOk
  have h5_cx := Satisfies.mono (sepConj_mono_left (dpCxAt_entails_memRegion32 y.cx)) h5
  refine ⟨⟨hfr, hro, hx0, hx1, hx2, hstk_sp, hfiles, hcoins_lt, hfPeer, hdecOk, hfits⟩, ?_⟩
  dsimp only [dpPollEntrySpatialPlaced]
  convert h5_cx using 1
  sep_ac_rfl

theorem extHookStack_le_cliPollSess_loadCallStack [LibsignalPlacement]
    (A : RustAlloc) (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost) :
    extHookStack ≤ loadCallStack (cliPollSessKitPlaced A F0 scopeKit peer (cliKitStk B)) := by
  dsimp only [extHookStack, loadCallStack, cliPollSessKitPlaced, cliPollSessKit,
    cliSessionStoreSpec, cliKitStk,
    CryptoVerification.SignalSession.Cli.KitInst.SessKit.loadShimNeed,
    CryptoVerification.SignalSession.Cli.KitInst.SessKit.loadPollNeed,
    CryptoVerification.RustHeap.allocHookStack]
  omega

end LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3MatchingPathBKitsPlacedBudgetFd

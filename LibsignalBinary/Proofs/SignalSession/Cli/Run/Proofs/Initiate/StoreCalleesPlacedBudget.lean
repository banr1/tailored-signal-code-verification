/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCalleesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdKeyPairPollPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdRegIdPollPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.ShimsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.StorePollCliPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded `[LibsignalPlacement]` CLI Store Vtable and Callback Contracts

Allocation-budget (`RustCliAllocBudget M`) bundle of all 12 CLI store functions, `futDrop`
(`futDropBudgetSpec` and `futDropSpec`), and the 6 trait-vtable `.rodata` slot dispatch facts
transferred onto `initProgPlaced mmpl gh W`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCalleesPlacedBudget

noncomputable section

open Arm64 Arm64.Obj ProofLib SepProp
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement LibsignalRoLoaded libsignalMutatedBlocks lsmpl
   lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles subroutine_ok_withLsCodeRoLoaded_of_plain withLsCodeRoLoaded)
open CryptoVerification.LibsignalPublicApi.StoreSession (futDropSpec)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli
  (DirGhost IdPollGhost SessLoadPollGhost cliIdentityVtSym cliSessionVtSym idKeyPairFutVtSym
   idRegIdFutVtSym)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliWrOk)
open CryptoVerification.SignalSession.Cli.Placed
  (lsProg_542 lsProg_565 lsProg_566 lsProg_569 lsProg_589 lsProg_594 lsProg_600 lsProg_601
   lsProg_604 lsProg_605)
open CryptoVerification.SignalSession.Cli.RunProofs (cliInitiateFrame cliInitiateNeed)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
  (cliAddrTextStk cliDirPutStk initProgPlaced transfer_withLsCodeRoLoaded)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.StoreCalleesProofs
  (futDrop_block_placed_ok)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (futDropBudgetSpec)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (SerializeEnvX)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
  (futDropBudget_block_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdKeyPairPollPlacedBudget
  (CliIdKeyPairPollEnv idKeyPairPoll_cli_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdRegIdPollPlacedBudget
  (CliIdRegIdPollEnv idRegIdPoll_cli_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.ShimsPlacedBudget
  (idKeyPairShim_cli_placed_ok idRegIdShim_cli_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.StorePollCliPlacedBudget
  (sessStorePoll_cli_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (addrTextSpecPlaced dirGetSpecPlaced dirPutSpecPlaced idKeyPairPollSpecPlaced idOwnShimSpecPlaced
   idRegIdPollSpecPlaced idSavePollSpecPlaced idSaveShimSpecPlaced idTrustPollSpecPlaced
   idTrustShimSpecPlaced sessLoadPollSpecPlaced sessLoadShimSpecPlaced sessStorePollSpecPlaced
   sessStoreShimSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePoll.LayoutBudget (CliStorePollEnv)
open Arm64.Obj (MultiPlacement)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

export CryptoVerification.SignalSession.Cli.RunProofs.Initiate (transfer_withLsCodeRoLoaded)
export LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdKeyPairPollPlacedBudget
  (CliIdKeyPairPollEnv)
export LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdRegIdPollPlacedBudget
  (CliIdRegIdPollEnv)
export LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePoll.LayoutBudget (CliStorePollEnv)

/-! ## 1. Allocation-Event Envelopes and External Store Leaf Contracts -/

/-- Allocation-event envelopes for the `Cli/Dir/*` and `Cli/Store/*` callees bundled in
`ExistingStoreCalleesPlaced`. -/
structure ExistingStoreCalleesEnvs where
  dirGet : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop
  addressText : AddrGhost → List AllocEvent → Prop
  dirPut : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop
  idTrustPoll : FsFiles → IdPollGhost → List AllocEvent → Prop
  sessLoadPoll : FsFiles → SessLoadPollGhost → List AllocEvent → Prop
  idSavePoll : FsFiles → IdPollGhost → List AllocEvent → Prop

/-- Budget-threaded `[LibsignalPlacement]` bundle of the `Cli/Dir/*`, `Cli/Store/*`, and
`.rodata` trait-vtable leaf contracts consumed by `InitStoreCalleesPlaced`. -/
structure ExistingStoreCalleesPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (eEnvs : ExistingStoreCalleesEnvs)
    (H : LibsignalHooks) (B : RunBudgets) : Prop where
  dirGet : subroutine_ok (lsProg_589 H) (lsmpl.base 589)
    (dirGetSpecPlaced cliIo.rd cliWrOk A lim eEnvs.dirGet B.dirGetNeed)
  addressText : subroutine_ok (lsProg_594 H) (lsmpl.base 594)
    (addrTextSpecPlaced A lim eEnvs.addressText cliAddrTextStk)
  dirPut : subroutine_ok (lsProg_542 H) (lsmpl.base 542)
    (dirPutSpecPlaced A lim eEnvs.dirPut cliDirPutStk)
  idTrustShim : ∀ {stk : Nat}, cliInitiateNeed B ≤ stk →
    subroutine_ok (lsProg_601 H) (lsmpl.base 601)
      (idTrustShimSpecPlaced A lim (stk - cliInitiateFrame))
  idTrustPoll : ∀ {stk : Nat}, cliInitiateNeed B ≤ stk →
    subroutine_ok (lsProg_566 H) (lsmpl.base 566)
      (idTrustPollSpecPlaced cliIo.rd cliWrOk A lim eEnvs.idTrustPoll
        (stk - cliInitiateFrame))
  sessLoadShim : ∀ {stk : Nat}, cliInitiateNeed B ≤ stk →
    subroutine_ok (lsProg_604 H) (lsmpl.base 604)
      (sessLoadShimSpecPlaced A lim (stk - cliInitiateFrame))
  sessLoadPoll : ∀ {stk : Nat}, cliInitiateNeed B ≤ stk →
    subroutine_ok (lsProg_569 H) (lsmpl.base 569)
      (sessLoadPollSpecPlaced cliIo.rd cliWrOk (fun _ => False) A lim
        eEnvs.sessLoadPoll (stk - cliInitiateFrame))
  idSaveShim : ∀ {stk : Nat}, cliInitiateNeed B ≤ stk →
    subroutine_ok (lsProg_600 H) (lsmpl.base 600)
      (idSaveShimSpecPlaced A lim (stk - cliInitiateFrame))
  idSavePoll : ∀ {stk : Nat}, cliInitiateNeed B ≤ stk →
    subroutine_ok (lsProg_565 H) (lsmpl.base 565)
      (idSavePollSpecPlaced cliIo.rd cliWrOk A lim eEnvs.idSavePoll
        (stk - cliInitiateFrame))
  sessStoreShim : ∀ {stk : Nat}, cliInitiateNeed B ≤ stk →
    subroutine_ok (lsProg_605 H) (lsmpl.base 605)
      (sessStoreShimSpecPlaced A lim (stk - cliInitiateFrame))
  rodata_idVt_keyPairSlot : ∀ {m : Memory} {P : SepProp},
    LibsignalRoLoaded lsmpl m → (m ⊨ P) →
      (m ⊨ ((lsρ cliIdentityVtSym + 24#64) ↦₆₄ᵣ lsmpl.base 602) ∗ P)
  rodata_idVt_regIdSlot : ∀ {m : Memory} {P : SepProp},
    LibsignalRoLoaded lsmpl m → (m ⊨ P) →
      (m ⊨ ((lsρ cliIdentityVtSym + 32#64) ↦₆₄ᵣ lsmpl.base 603) ∗ P)
  rodata_idVt_saveSlot : ∀ {m : Memory} {P : SepProp},
    LibsignalRoLoaded lsmpl m → (m ⊨ P) →
      (m ⊨ ((lsρ cliIdentityVtSym + 40#64) ↦₆₄ᵣ lsmpl.base 600) ∗ P)
  rodata_idVt_trustSlot : ∀ {m : Memory} {P : SepProp},
    LibsignalRoLoaded lsmpl m → (m ⊨ P) →
      (m ⊨ ((lsρ cliIdentityVtSym + 48#64) ↦₆₄ᵣ lsmpl.base 601) ∗ P)
  rodata_sessVt_loadSlot : ∀ {m : Memory} {P : SepProp},
    LibsignalRoLoaded lsmpl m → (m ⊨ P) →
      (m ⊨ ((lsρ cliSessionVtSym + 24#64) ↦₆₄ᵣ lsmpl.base 604) ∗ P)
  rodata_sessVt_storeSlot : ∀ {m : Memory} {P : SepProp},
    LibsignalRoLoaded lsmpl m → (m ⊨ P) →
      (m ⊨ ((lsρ cliSessionVtSym + 32#64) ↦₆₄ᵣ lsmpl.base 605) ∗ P)

/-! ## 2. Bundled Budget-Threaded CLI Store Contracts on `initProgPlaced mmpl gh W` at `stk - cliInitiateFrame` -/

/-- Budget-threaded `[LibsignalPlacement]` counterpart of `InitStoreCalleesPlaced`, bundling all 12
CLI store functions, `futDrop` (`futDropBudgetSpec` + plain `futDropSpec`), and the 6 trait-slot
`.rodata` vtable dispatch facts on `initProgPlaced mmpl gh W`. -/
structure InitStoreCalleesPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (eEnvs : ExistingStoreCalleesEnvs)
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (B : RunBudgets) (stk : Nat) : Prop where
  futDrop : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 547)
    (withLsCodeRoLoaded lsmpl futDropBudgetSpec)
  futDropPlain : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 547)
    (withLsCodeRoLoaded lsmpl futDropSpec)
  idTrustShim : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 601)
    (idTrustShimSpecPlaced A lim (stk - cliInitiateFrame))
  idTrustPoll : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 566)
    (idTrustPollSpecPlaced cliIo.rd cliWrOk A lim eEnvs.idTrustPoll
      (stk - cliInitiateFrame))
  sessLoadShim : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 604)
    (sessLoadShimSpecPlaced A lim (stk - cliInitiateFrame))
  sessLoadPoll : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 569)
    (sessLoadPollSpecPlaced cliIo.rd cliWrOk (fun _ => False) A lim
      eEnvs.sessLoadPoll (stk - cliInitiateFrame))
  idKeyPairShim : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 602)
    (idOwnShimSpecPlaced idKeyPairFutVtSym A lim (stk - cliInitiateFrame))
  idKeyPairPoll : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 567)
    (idKeyPairPollSpecPlaced cliIo.rd cliWrOk A lim
      (CliIdKeyPairPollEnv eEnvs.dirGet cliIo.rd) (stk - cliInitiateFrame))
  idRegIdShim : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 603)
    (idOwnShimSpecPlaced idRegIdFutVtSym A lim (stk - cliInitiateFrame))
  idRegIdPoll : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 568)
    (idRegIdPollSpecPlaced cliIo.rd cliWrOk A lim
      (CliIdRegIdPollEnv eEnvs.dirGet cliIo.rd) (stk - cliInitiateFrame))
  idSaveShim : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 600)
    (idSaveShimSpecPlaced A lim (stk - cliInitiateFrame))
  idSavePoll : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 565)
    (idSavePollSpecPlaced cliIo.rd cliWrOk A lim eEnvs.idSavePoll
      (stk - cliInitiateFrame))
  sessStoreShim : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 605)
    (sessStoreShimSpecPlaced A lim (stk - cliInitiateFrame))
  sessStorePoll : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 570)
    (sessStorePollSpecPlaced A lim
      (CliStorePollEnv eEnvs.addressText SerializeEnvX eEnvs.dirPut) (stk - cliInitiateFrame))
  rodata_idVt_keyPairSlot : ∀ {m : Memory} {P : SepProp},
    LibsignalRoLoaded lsmpl m → (m ⊨ P) →
      (m ⊨ ((lsρ cliIdentityVtSym + 24#64) ↦₆₄ᵣ lsmpl.base 602) ∗ P)
  rodata_idVt_regIdSlot : ∀ {m : Memory} {P : SepProp},
    LibsignalRoLoaded lsmpl m → (m ⊨ P) →
      (m ⊨ ((lsρ cliIdentityVtSym + 32#64) ↦₆₄ᵣ lsmpl.base 603) ∗ P)
  rodata_idVt_saveSlot : ∀ {m : Memory} {P : SepProp},
    LibsignalRoLoaded lsmpl m → (m ⊨ P) →
      (m ⊨ ((lsρ cliIdentityVtSym + 40#64) ↦₆₄ᵣ lsmpl.base 600) ∗ P)
  rodata_idVt_trustSlot : ∀ {m : Memory} {P : SepProp},
    LibsignalRoLoaded lsmpl m → (m ⊨ P) →
      (m ⊨ ((lsρ cliIdentityVtSym + 48#64) ↦₆₄ᵣ lsmpl.base 601) ∗ P)
  rodata_sessVt_loadSlot : ∀ {m : Memory} {P : SepProp},
    LibsignalRoLoaded lsmpl m → (m ⊨ P) →
      (m ⊨ ((lsρ cliSessionVtSym + 24#64) ↦₆₄ᵣ lsmpl.base 604) ∗ P)
  rodata_sessVt_storeSlot : ∀ {m : Memory} {P : SepProp},
    LibsignalRoLoaded lsmpl m → (m ⊨ P) →
      (m ⊨ ((lsρ cliSessionVtSym + 32#64) ↦₆₄ᵣ lsmpl.base 605) ∗ P)

/-- Budget-threaded relocatable `[LibsignalPlacement]` counterpart of
`Initiate.initStoreCallees_placed_ok`. -/
theorem initStoreCallees_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {eEnvs : ExistingStoreCalleesEnvs}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (B : RunBudgets)
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hExist : ExistingStoreCalleesPlaced A lim eEnvs (cliGhostExterns gh (cliExternsPlaced mmpl W)) B)
    (stk : Nat) (hstk : cliInitiateNeed B ≤ stk) (_hstk64 : stk ≤ 2 ^ 63) :
    InitStoreCalleesPlaced A lim eEnvs mmpl gh W B stk :=
  { futDrop := transfer_withLsCodeRoLoaded (callerProg := initProgPlaced mmpl gh W)
      (subroutine_ok_withLsCodeRoLoaded_of_plain
        (futDropBudget_block_placed_ok (cliGhostExterns gh (cliExternsPlaced mmpl W))))
    futDropPlain := transfer_withLsCodeRoLoaded (callerProg := initProgPlaced mmpl gh W)
      (subroutine_ok_withLsCodeRoLoaded_of_plain
        (futDrop_block_placed_ok (cliGhostExterns gh (cliExternsPlaced mmpl W))))
    idTrustShim := transfer_withLsCodeRoLoaded (callerProg := initProgPlaced mmpl gh W)
      (hExist.idTrustShim hstk)
    idTrustPoll := transfer_withLsCodeRoLoaded (callerProg := initProgPlaced mmpl gh W)
      (hExist.idTrustPoll hstk)
    sessLoadShim := transfer_withLsCodeRoLoaded (callerProg := initProgPlaced mmpl gh W)
      (hExist.sessLoadShim hstk)
    sessLoadPoll := transfer_withLsCodeRoLoaded (callerProg := initProgPlaced mmpl gh W)
      (hExist.sessLoadPoll hstk)
    idKeyPairShim := idKeyPairShim_cli_placed_ok (callerProg := initProgPlaced mmpl gh W) B hh hstk
    idKeyPairPoll := idKeyPairPoll_cli_placed_ok (prog := initProgPlaced mmpl gh W)
      B hh hExist.dirGet (by decide) (by decide) (by decide) hstk
    idRegIdShim := idRegIdShim_cli_placed_ok (callerProg := initProgPlaced mmpl gh W) B hh hstk
    idRegIdPoll := idRegIdPoll_cli_placed_ok (prog := initProgPlaced mmpl gh W)
      B hh hExist.dirGet (by decide) (by decide) (by decide) hstk
    idSaveShim := transfer_withLsCodeRoLoaded (callerProg := initProgPlaced mmpl gh W)
      (hExist.idSaveShim hstk)
    idSavePoll := transfer_withLsCodeRoLoaded (callerProg := initProgPlaced mmpl gh W)
      (hExist.idSavePoll hstk)
    sessStoreShim := transfer_withLsCodeRoLoaded (callerProg := initProgPlaced mmpl gh W)
      (hExist.sessStoreShim hstk)
    sessStorePoll := sessStorePoll_cli_placed_ok (prog := initProgPlaced mmpl gh W)
      B hh hExist.addressText hExist.dirPut (by decide) hstk
    rodata_idVt_keyPairSlot := hExist.rodata_idVt_keyPairSlot
    rodata_idVt_regIdSlot := hExist.rodata_idVt_regIdSlot
    rodata_idVt_saveSlot := hExist.rodata_idVt_saveSlot
    rodata_idVt_trustSlot := hExist.rodata_idVt_trustSlot
    rodata_sessVt_loadSlot := hExist.rodata_sessVt_loadSlot
    rodata_sessVt_storeSlot := hExist.rodata_sessVt_storeSlot }

end

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCalleesPlacedBudget

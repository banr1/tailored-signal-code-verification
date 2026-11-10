/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.CliSessionCodeSym
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.Existing
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.ShimsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdKeyPairPollPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdRegIdPollPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.StorePollCliPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `[LibsignalPlacement]` CLI Store Vtable and Callback Contracts

Packages all 12 CLI store functions, `futDrop`, and the 6 trait-vtable `.rodata` slot dispatch
facts transferred onto `initProgPlaced W` (`lsProg_521 (cliExternsPlaced W)`).
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option maxRecDepth 200000

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate

open Arm64 Arm64.Obj Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open Arm64.Obj (MultiPlacement)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

/-! ## 1. Cross-Block Transfer Helper (`withLsCodeRoLoaded lsmpl`) -/

theorem transfer_withLsCodeRoLoaded [LibsignalPlacement] {α : Type}
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] [IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok calleeProg entry
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl spec))
    (hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl spec) := by
  have hrocl := ls_subroutine_ok_rocl_of_block (callerProg := callerProg) hcallee hi hj hj_unmut
  exact subroutine_ok_mono hrocl (fun _ _ _ hp => hp)
    (fun _ _ _ _ hq => by
      dsimp only [LibsignalPublicApi.StoreKit.withLsRoCl,
        LibsignalPublicApi.StoreKit.withLsCodeRoLoaded] at hq ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq
      exact hq.2)

/-- Typeclass packaging `TraceFsSound (initProgPlaced mmpl gh W)` so sub-lemmas without explicit
`hh : RunHooksPlaced ...` thread `TraceFsSound` with zero positional-argument churn. -/
class InitTraceFsSound [LibsignalPlacement] (mmpl : MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) : Prop where
  out : TraceFsSound (initProgPlaced mmpl gh W)

theorem traceFsSound_initPlaced [LibsignalPlacement] (mmpl : MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks) [h : InitTraceFsSound mmpl gh W] :
    TraceFsSound (initProgPlaced mmpl gh W) :=
  h.out

/-! ## 2. External Store Leaf Contracts (`ExistingStoreCalleesPlaced`) -/

/-- `[LibsignalPlacement]` bundle of the `Cli/Dir/*`, `Cli/Store/*`, and `.rodata` trait-vtable
leaf contracts consumed by `InitStoreCalleesPlaced`. -/
structure ExistingStoreCalleesPlaced [LibsignalPlacement] (A : RustAlloc)
    (H : LibsignalHooks) (B : RunBudgets) : Prop where
  dirGet : subroutine_ok (lsProg_589 H) (lsmpl.base 589)
    (dirGetSpecPlaced cliIo.rd cliWrOk A B.dirGetNeed)
  addressText : subroutine_ok (lsProg_594 H) (lsmpl.base 594)
    (addrTextSpecPlaced A cliAddrTextStk)
  dirPut : subroutine_ok (lsProg_542 H) (lsmpl.base 542)
    (dirPutSpecPlaced A cliDirPutStk)
  idTrustShim : ∀ {stk : Nat}, cliInitiateNeed B ≤ stk →
    subroutine_ok (lsProg_601 H) (lsmpl.base 601)
      (idTrustShimSpecPlaced A (stk - cliInitiateFrame))
  idTrustPoll : ∀ {stk : Nat}, cliInitiateNeed B ≤ stk →
    subroutine_ok (lsProg_566 H) (lsmpl.base 566)
      (idTrustPollSpecPlaced cliIo.rd cliWrOk A (stk - cliInitiateFrame))
  sessLoadShim : ∀ {stk : Nat}, cliInitiateNeed B ≤ stk →
    subroutine_ok (lsProg_604 H) (lsmpl.base 604)
      (sessLoadShimSpecPlaced A (stk - cliInitiateFrame))
  sessLoadPoll : ∀ {stk : Nat}, cliInitiateNeed B ≤ stk →
    subroutine_ok (lsProg_569 H) (lsmpl.base 569)
      (sessLoadPollSpecPlaced cliIo.rd cliWrOk (fun _ => False) A (stk - cliInitiateFrame))
  idSaveShim : ∀ {stk : Nat}, cliInitiateNeed B ≤ stk →
    subroutine_ok (lsProg_600 H) (lsmpl.base 600)
      (idSaveShimSpecPlaced A (stk - cliInitiateFrame))
  idSavePoll : ∀ {stk : Nat}, cliInitiateNeed B ≤ stk →
    subroutine_ok (lsProg_565 H) (lsmpl.base 565)
      (idSavePollSpecPlaced cliIo.rd cliWrOk A (stk - cliInitiateFrame))
  sessStoreShim : ∀ {stk : Nat}, cliInitiateNeed B ≤ stk →
    subroutine_ok (lsProg_605 H) (lsmpl.base 605)
      (sessStoreShimSpecPlaced A (stk - cliInitiateFrame))
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

/-! ## 3. Bundled CLI Store Contracts on `initProgPlaced W` at `stk - cliInitiateFrame` -/

/-- `[LibsignalPlacement]` counterpart of `InitStoreCallees`, bundling all 12 CLI store functions,
`futDrop`, and the 6 trait-slot `.rodata` vtable dispatch facts on `initProgPlaced W`. -/
structure InitStoreCalleesPlaced [LibsignalPlacement] (A : RustAlloc) (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (stk : Nat) : Prop where
  futDrop : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 547)
    (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl futDropSpec)
  idTrustShim : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 601)
    (idTrustShimSpecPlaced A (stk - cliInitiateFrame))
  idTrustPoll : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 566)
    (idTrustPollSpecPlaced cliIo.rd cliWrOk A (stk - cliInitiateFrame))
  sessLoadShim : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 604)
    (sessLoadShimSpecPlaced A (stk - cliInitiateFrame))
  sessLoadPoll : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 569)
    (sessLoadPollSpecPlaced cliIo.rd cliWrOk (fun _ => False) A (stk - cliInitiateFrame))
  idKeyPairShim : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 602)
    (idOwnShimSpecPlaced idKeyPairFutVtSym A (stk - cliInitiateFrame))
  idKeyPairPoll : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 567)
    (idKeyPairPollSpecPlaced cliIo.rd cliWrOk A (stk - cliInitiateFrame))
  idRegIdShim : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 603)
    (idOwnShimSpecPlaced idRegIdFutVtSym A (stk - cliInitiateFrame))
  idRegIdPoll : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 568)
    (idRegIdPollSpecPlaced cliIo.rd cliWrOk A (stk - cliInitiateFrame))
  idSaveShim : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 600)
    (idSaveShimSpecPlaced A (stk - cliInitiateFrame))
  idSavePoll : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 565)
    (idSavePollSpecPlaced cliIo.rd cliWrOk A (stk - cliInitiateFrame))
  sessStoreShim : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 605)
    (sessStoreShimSpecPlaced A (stk - cliInitiateFrame))
  sessStorePoll : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 570)
    (sessStorePollSpecPlaced A (stk - cliInitiateFrame))
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

/-- Relocatable `[LibsignalPlacement]` counterpart of `initStoreCallees_ok`. -/
theorem initStoreCallees_placed_ok [LibsignalPlacement] {A : RustAlloc} (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets)
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hExist : ExistingStoreCalleesPlaced A (cliGhostExterns gh (cliExternsPlaced mmpl W)) B)
    (stk : Nat) (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    InitStoreCalleesPlaced A mmpl gh W B stk := by
  have hShimStk : 32 + extHookStack ≤ stk - cliInitiateFrame := by
    have := stk_sub_ge_base hstk
    dsimp only [extHookStack]
    omega
  have hShimHi : stk - cliInitiateFrame ≤ 2 ^ 64 := by omega
  have hKpShim602 : subroutine_ok (lsProg_602 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 602)
      (idOwnShimSpecPlaced idKeyPairFutVtSym A (stk - cliInitiateFrame)) :=
    StoreCalleesProofs.idOwnShim_lift_stk_placed
      (StoreCalleesProofs.idKeyPairShim_fixed_placed_ok hh.alloc hh.panic_alloc)
      hShimStk hShimHi
  have hRegShim603 : subroutine_ok (lsProg_603 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 603)
      (idOwnShimSpecPlaced idRegIdFutVtSym A (stk - cliInitiateFrame)) :=
    StoreCalleesProofs.idOwnShim_lift_stk_placed
      (StoreCalleesProofs.idRegIdShim_fixed_placed_ok hh.alloc hh.panic_alloc)
      hShimStk hShimHi
  exact
    { futDrop := transfer_withLsCodeRoLoaded (callerProg := initProgPlaced mmpl gh W)
        (LibsignalPublicApi.StoreKit.subroutine_ok_withLsCodeRoLoaded_of_plain
          (StoreCalleesProofs.futDrop_block_placed_ok (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      idTrustShim := transfer_withLsCodeRoLoaded (callerProg := initProgPlaced mmpl gh W)
        (hExist.idTrustShim hstk)
      idTrustPoll := transfer_withLsCodeRoLoaded (callerProg := initProgPlaced mmpl gh W)
        (hExist.idTrustPoll hstk)
      sessLoadShim := transfer_withLsCodeRoLoaded (callerProg := initProgPlaced mmpl gh W)
        (hExist.sessLoadShim hstk)
      sessLoadPoll := transfer_withLsCodeRoLoaded (callerProg := initProgPlaced mmpl gh W)
        (hExist.sessLoadPoll hstk)
      idKeyPairShim := transfer_withLsCodeRoLoaded (callerProg := initProgPlaced mmpl gh W) hKpShim602
      idKeyPairPoll := IdKeyPairPoll.idKeyPairPoll_cli_placed_ok (prog := initProgPlaced mmpl gh W)
        B hh hExist.dirGet (by decide) hstk
      idRegIdShim := transfer_withLsCodeRoLoaded (callerProg := initProgPlaced mmpl gh W) hRegShim603
      idRegIdPoll := IdRegIdPoll.idRegIdPoll_cli_placed_ok (prog := initProgPlaced mmpl gh W)
        B hh hExist.dirGet (by decide) hstk
      idSaveShim := transfer_withLsCodeRoLoaded (callerProg := initProgPlaced mmpl gh W)
        (hExist.idSaveShim hstk)
      idSavePoll := transfer_withLsCodeRoLoaded (callerProg := initProgPlaced mmpl gh W)
        (hExist.idSavePoll hstk)
      sessStoreShim := transfer_withLsCodeRoLoaded (callerProg := initProgPlaced mmpl gh W)
        (hExist.sessStoreShim hstk)
      sessStorePoll := StorePollCli.sessStorePoll_cli_placed_ok (prog := initProgPlaced mmpl gh W)
        B hh hExist.addressText hExist.dirPut (by decide) hstk
      rodata_idVt_keyPairSlot := hExist.rodata_idVt_keyPairSlot
      rodata_idVt_regIdSlot := hExist.rodata_idVt_regIdSlot
      rodata_idVt_saveSlot := hExist.rodata_idVt_saveSlot
      rodata_idVt_trustSlot := hExist.rodata_idVt_trustSlot
      rodata_sessVt_loadSlot := hExist.rodata_sessVt_loadSlot
      rodata_sessVt_storeSlot := hExist.rodata_sessVt_storeSlot }

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate

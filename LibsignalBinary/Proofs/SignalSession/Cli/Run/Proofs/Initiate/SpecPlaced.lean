/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.RunCodeSym
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.AssemblyPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Spec
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.S0Proofs

/-!
# Relocatable Top-Level Contract for `signal_session_handshake::initiate`

Exports `cliInitiate_placed_ok` on block `521` (`initProgPlaced mmpl gh W`), caller-block transfer
`cliInitiate_caller_placed_ok` (`i < 619`), `RunCalleesPlaced.initiate` packaging
`cliInitiate_slotOk_placed` on block `579`, and pure `S₀` re-exports under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.RunProofs

open Arm64 Arm64.Obj Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  LibsignalCodeRoLoaded withLsCodeRoLoaded extract_withLsCodeRoLoaded
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.Run.Placed
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.CliHandshake.InitiatePlaced
open Arm64.Obj (MultiPlacement)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

/-- Block `521` (`signal_session_handshake::initiate`) satisfies `initSlotSpecPlaced A S stk` for `cliInitiateNeed B ≤ stk ≤ 2 ^ 63`. -/
theorem cliInitiate_placed_ok [LibsignalPlacement] {A : RustAlloc} (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    (B : RunBudgets) (S : RunSem)
    (hh : Initiate.RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hExist : Initiate.ExistingStoreCalleesPlaced A (cliGhostExterns gh (cliExternsPlaced mmpl W)) B)
    (ha4 : Initiate.SubsetA4InitCalleesPlaced A mmpl gh W)
    (hStage2 : Initiate.Stage2PlacedOk A mmpl gh W X B S)
    (hStage3 : Initiate.Stage3PlacedOk A mmpl gh W X B S)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hok : ∀ F peer me, S.filesOk F peer me → S.initOk F peer me → InitOk₀ ⟨W.C, W.Q⟩ F peer me)
    (stk : Nat) (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (Initiate.initProgPlaced mmpl gh W) (lsmpl.base 521)
      (RunCompose.initSlotSpecPlaced A S stk) :=
  Initiate.cliInitiate_placed_ok_proof mmpl gh W X B S hh hExist ha4 hStage2 hStage3 hS hok stk hstk hstk64

/-- Transfers `cliInitiate_placed_ok` to any caller block `i < 619`. -/
theorem cliInitiate_caller_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {i : Nat}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) [IsLsBlockProg callerProg i (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (hh : Initiate.RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hExist : Initiate.ExistingStoreCalleesPlaced A (cliGhostExterns gh (cliExternsPlaced mmpl W)) B)
    (ha4 : Initiate.SubsetA4InitCalleesPlaced A mmpl gh W)
    (hStage2 : Initiate.Stage2PlacedOk A mmpl gh W X B S)
    (hStage3 : Initiate.Stage3PlacedOk A mmpl gh W X B S)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hok : ∀ F peer me, S.filesOk F peer me → S.initOk F peer me → InitOk₀ ⟨W.C, W.Q⟩ F peer me)
    (stk : Nat) (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 521)
      (RunCompose.initSlotSpecPlaced A S stk) :=
  Initiate.transfer_withLsCodeRoLoaded (callerProg := callerProg) (hi := hi)
    (cliInitiate_placed_ok mmpl gh W X B S hh hExist ha4 hStage2 hStage3 hS hok stk hstk hstk64)

/-- Packages `cliInitiate_caller_placed_ok` into `RunCalleesPlaced.initiate` on block `579` when `needs.initiate = cliInitiateNeed B`. -/
theorem cliInitiate_slotOk_placed [LibsignalPlacement] {A : RustAlloc} (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem) (needs : RunNeeds)
    (hh : Initiate.RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hExist : Initiate.ExistingStoreCalleesPlaced A (cliGhostExterns gh (cliExternsPlaced mmpl W)) B)
    (ha4 : Initiate.SubsetA4InitCalleesPlaced A mmpl gh W)
    (hStage2 : Initiate.Stage2PlacedOk A mmpl gh W X B S)
    (hStage3 : Initiate.Stage3PlacedOk A mmpl gh W X B S)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hok : ∀ F peer me, S.filesOk F peer me → S.initOk F peer me → InitOk₀ ⟨W.C, W.Q⟩ F peer me)
    (hneed : needs.initiate = cliInitiateNeed B) :
    ∀ stk, (slotsOfPlaced A S needs).initiate.need ≤ stk → stk ≤ 2 ^ 63 →
      subroutine_ok (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 521)
        ((slotsOfPlaced A S needs).initiate.spec stk) :=
  fun stk h1 h2 =>
    cliInitiate_caller_placed_ok (i := 579) mmpl gh W X B S hh hExist ha4 hStage2 hStage3 hS hok stk
      (hneed ▸ h1) h2

theorem initOk₀_pqInit_placed (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) (hwf : PqxdhPartyInSpecDomain W st) (hs : st.session = none) :
    InitOk₀ W (runFiles (pqInitInputs W st b t)) (RunRefine.addrValE st.party.other)
      (RunRefine.addrValE st.party) :=
  initOk₀_pqInit W st b t hwf hs

theorem pqInitiateAgrees_initDef_placed (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (hS : S.initiate = initDef X W) : RunRefine.PqInitiateAgrees S X W :=
  pqInitiateAgrees_initDef S X W hS

end CryptoVerification.SignalSession.Cli.RunProofs

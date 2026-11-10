/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RunInstPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.JProofPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0ProofPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1bProofPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cProofPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2ProofPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bProofPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bBadPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

@[expose] public section

set_option autoImplicit false

/-!
# Relocatable `RunArmsPlaced` and `CliPubCalleesPlaced` Aggregator

Assembles the relocatable arm hop contracts on Block `579` (`signal_session::run`) into
`RunArmsPlaced` and `CliPubCalleesPlaced`.
-/

namespace CryptoVerification.SignalSession.Cli.RunCompose

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.SignalSession.Cli.Run.Placed
open CryptoVerification.SignalSession.Cli.Slots
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunRefine
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.MainHops
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (CliGhostHooks cliGhostExterns)

theorem runArmsPlaced_of_send_recvP_recvBad [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat}
    (hsend : RunHopSendPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
      A H B S needs resStack)
    (hrecvP : RunHopRecvPPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
      A H B S needs resStack)
    (hrecvBad : RunHopRecvBadPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
      A H B S needs resStack) :
    RunArmsPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
      A H B S needs resStack :=
  { join := run_hop_join_placed_ok
    pre := run_hop_pre_placed_ok
    init1 := run_hop_init1_placed_ok
    init2 := run_hop_init2_placed_ok
    init3 := run_hop_init3_placed_ok
    send := hsend
    recvW := run_hop_recvW_placed_ok
    recvP := hrecvP
    recvBad := hrecvBad }

theorem cliPubCallees_placed_of_send_recvP_recvBad [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hRunA0 : CliA0RunHooks mmpl g W)
    (hsend : ∀ (S : RunSem) (decPkNeed : Nat),
      RunHopSendPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
        E2E.HooksE.A0 (cliGhostExterns g (cliExternsPlaced mmpl W)) cliRunBudgets_placed S
        (cliRunNeeds_placed decPkNeed) cliResStack)
    (hrecvP : ∀ (S : RunSem) (decPkNeed : Nat),
      RunHopRecvPPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
        E2E.HooksE.A0 (cliGhostExterns g (cliExternsPlaced mmpl W)) cliRunBudgets_placed S
        (cliRunNeeds_placed decPkNeed) cliResStack)
    (hrecvBad : ∀ (S : RunSem) (decPkNeed : Nat),
      RunHopRecvBadPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
        E2E.HooksE.A0 (cliGhostExterns g (cliExternsPlaced mmpl W)) cliRunBudgets_placed S
        (cliRunNeeds_placed decPkNeed) cliResStack) :
    CliPubCalleesPlaced mmpl g W :=
  cliPubCallees_of_arms_placed mmpl g W hRunA0 fun S decPkNeed =>
    runArmsPlaced_of_send_recvP_recvBad (hsend S decPkNeed) (hrecvP S decPkNeed)
      (hrecvBad S decPkNeed)

theorem runArmsPlaced_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat} :
    RunArmsPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
      A H B S needs resStack :=
  runArmsPlaced_of_send_recvP_recvBad
    run_hop_send_placed_ok run_hop_recvP_placed_ok run_hop_recvBad_placed_ok

theorem cliPubCallees_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hRunA0 : CliA0RunHooks mmpl g W) :
    CliPubCalleesPlaced mmpl g W :=
  cliPubCallees_of_arms_placed mmpl g W hRunA0 fun _ _ => runArmsPlaced_ok

theorem runArmsFrozenPlaced_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat} :
    RunArmsFrozenPlaced A H B S needs resStack :=
  { join := run_hop_join_placed_ok
    joinRo := run_hop_join_placed_ok
    pre := run_hop_pre_of_slots (slots := slotsOfSigPkFrozenPlaced A S needs) (needs := needs) rfl
    init1 := run_hop_init1_of_slots (slots := slotsOfSigPkFrozenPlaced A S needs) (needs := needs) rfl
    init2 := run_hop_init2_of_slots (slots := slotsOfSigPkFrozenPlaced A S needs) (needs := needs) rfl rfl
    init3 := run_hop_init3_of_slots (slots := slotsOfSigPkFrozenPlaced A S needs) (needs := needs) rfl rfl
    send := run_hop_send_of_slots (slots := slotsOfSigPkFrozenPlaced A S needs) (needs := needs) rfl rfl
    recvW := run_hop_recvW_of_codeOk (CodeOk := LibsignalFrozen lsmpl)
      (slots := slotsOfSigPkFrozenPlaced A S needs) (needs := needs) rfl rfl
    recvP := run_hop_recvP_of_codeOk (CodeOk := LibsignalFrozen lsmpl)
      (slots := slotsOfSigPkFrozenPlaced A S needs) (needs := needs) rfl rfl
    recvBad := run_hop_recvBad_placed_ok }

theorem cliPubCallees_frozen_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hRunA0 : CliA0RunHooks mmpl g W) :
    CliPubCalleesFrozenPlaced mmpl g W :=
  cliPubCallees_frozen_of_arms_placed mmpl g W hRunA0 fun _ _ => runArmsFrozenPlaced_ok

end CryptoVerification.SignalSession.Cli.RunCompose

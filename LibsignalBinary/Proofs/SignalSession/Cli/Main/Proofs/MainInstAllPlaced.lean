/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RunInstNoMatchPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.AllPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromInstPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.RootTrapPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverInstPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsInst

/-!
# Relocatable Top-Level CLI `main` Assembly (`[LibsignalPlacement]` & `[LibsignalFullPlacement]`)

Assembles relocatable `[LibsignalPlacement]` (`MainOk*Placed`) and closed `[LibsignalFullPlacement]`
(`MainOk*FrozenPlaced`) theorems for `main` over `cliGhostExterns gh (cliExternsPlaced mmpl W)`,
covering both SM and 6-clause PQXDH + `NoMatch` specifications.
-/

@[expose] public section
set_option autoImplicit false

namespace CryptoVerification.SignalSession

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Poll
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.SignalSession.Cli.Run.Placed
open CryptoVerification.LibsignalSpqrV1 (libcruxHmacSpec)
open CryptoVerification.SignalSession.Cli.Slots (CliGhostA0Hooks lsLibcruxHmacSymCli)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.KitInst hiding
  cliPreKeyStoreSpecPlaced cliSignedPreKeyStoreSpecPlaced cliKyberPreKeyStoreSpecPlaced
  cliPreKeyStoreSpecPlaced_quiet cliSignedPreKeyStoreSpecPlaced_quiet
open CryptoVerification.E2E.Pqxdh CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
open CryptoVerification.CliHandshake.Placed
open CryptoVerification.CliHandshake.RespClosurePlaced

/-! ## 1. Placed `PksmSlotOkPlaced` & `CliDecPkSlotExistsPlaced` Bridges -/

/-- Discharges `RunProofs.PksmSlotOkPlaced mmpl gh W` under `[LibsignalPlacement]` and
`CliGhostA0Hooks E2E.HooksE.A0 gh` from `RunProofs.subsetA4PksmTryFromPlaced_cli` and
`RunProofs.cliPksmTryFrom_placed_at_block`. -/
theorem pksmSlotOkPlaced_cli [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostA0Hooks E2E.HooksE.A0 gh) :
    RunProofs.PksmSlotOkPlaced mmpl gh W :=
  fun _ hS =>
    RunProofs.cliPksmTryFrom_placed_at_block
      (callerProg := lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 579)
      (RunProofs.subsetA4PksmTryFromPlaced_cli mmpl gh W hG)
      (fun b => congrFun hS b)

/-- Discharges `RunProofs.Poll.CliTryDecryptPqV1PlacedStmt mmpl gh W` from `CliGhostA0Hooks`,
`hAesDec`, and `SpqrV1PlacedSeams mmpl gh W` via
`DecryptPq.tryDecryptPqV1_placed_ok_PTight_cli_at_block`. -/
theorem cliTryDecryptPqV1_placed_of_spqr [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hAesDec : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesDecSym
      (aesDecSpec W.C.D E2E.HooksE.A0))
    (hSpqr : SpqrV1PlacedSeams mmpl gh W) :
    RunProofs.Poll.CliTryDecryptPqV1PlacedStmt mmpl gh W :=
  fun ctl =>
    CryptoVerification.LibsignalTripleRatchet.DecryptPq.tryDecryptPqV1_placed_ok_PTight_cli_at_block
      (callerProg := Poll.dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 518)
      mmpl gh W ctl hG hAesDec hSpqr (by decide)

/-- Assembles `RunProofs.DecPkD2cSlotOkPlaced mmpl gh W` from
`RunProofs.Poll.decPkD2cSlotOk_placed_of_seams` and `cliTryDecryptPqV1_placed_of_spqr`. -/
theorem decPkD2cSlotOk_placed_of_seams [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hRunA0 : CliA0RunHooks mmpl gh W)
    (hRead518 : subroutine_ok (Poll.dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 cliRunBudgets_placed.readFile))
    (hAesDec : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesDecSym
      (aesDecSpec W.C.D E2E.HooksE.A0))
    (hSpqr : SpqrV1PlacedSeams mmpl gh W)
    (h_accept : ∀ X : UnreachedPqxdhPrimitives,
      subroutine_ok (lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 79)
        (pqxdhAcceptOptFieldsPlacedSpec
          (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) E2E.HooksE.A0))
    (h_accept_err : ∀ X : UnreachedPqxdhPrimitives,
      subroutine_ok (lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 79)
        (pqxdhAcceptErrOwnedPlacedSpec
          (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) E2E.HooksE.A0))
    (hLog519 : ∀ (mmpl' : Obj.MultiPlacement) (gh' : CliGhostHooks) (W' : CliHooks),
      subroutine_ok (lsProg_518 (cliGhostExterns gh' (cliExternsPlaced mmpl' W')))
        (lsmpl.base 519) (withLsCodeLoaded lsmpl pqxdhLogClosurePlacedSpec)) :
    RunProofs.DecPkD2cSlotOkPlaced mmpl gh W :=
  RunProofs.Poll.decPkD2cSlotOk_placed_of_seams mmpl gh W
    hRunA0.runHooks hRead518 (Slots.stage2ContractsMinPlaced_cli mmpl gh W hG)
    hDropNz hSpqr h_accept h_accept_err hLog519
    (cliTryDecryptPqV1_placed_of_spqr mmpl gh W hG hAesDec hSpqr)

/-- Specializes `RunProofs.DecPkD2cSlotOkPlaced mmpl gh W` at `X := defaultModelExtras_placed` to
witness `MainHops.CliDecPkSlotExistsPlaced mmpl gh W`
(`cliDecryptPrekeyNeed cliRunBudgets_placed ≤ 4194304`). -/
theorem cliDecPkSlotExistsPlaced_of_d2c [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (h : RunProofs.DecPkD2cSlotOkPlaced mmpl gh W) :
    MainHops.CliDecPkSlotExistsPlaced mmpl gh W :=
  ⟨decPkDefD2c defaultModelExtras_placed ⟨W.C, W.Q⟩ Slots.scopeIn,
   DecPkOkD2c ⟨W.C, W.Q⟩ Slots.scopeIn,
   cliDecryptPrekeyNeed cliRunBudgets_placed,
   by decide,
   fun S needs hfiles hdec hok hneed =>
     h defaultModelExtras_placed S needs hfiles hdec hok hneed⟩

/-! ## 2. Top-Level `MainOk*Placed` Theorems Parameterized Over Pre-Key & SPQR/Log Seams -/

-- A2'' D1: A0 island, hMs/hMc discharged at a0Ghost
/-- Assembles `MainOkPqAllTightPlaced mmpl gh` (all 5 `CliSpecPqxdh` clauses + Clause 6 `NoMatch`
under `mainSpecTightPlaced`) from `hDecPk`, `hSpqr`, and `hLog462`. -/
theorem main_ok_cli_pq_all_tight_placed_of_w4 [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (hG : CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hMs : gh.memset = some CryptoVerification.LibsignalAesCbc.memsetHook)
    (hMc : gh.memcpy = some CryptoVerification.LibsignalAesCbc.memcpyHook)
    (hMainHooks : ∀ W : CliHooks, CliA0MainHooks mmpl gh W)
    (hRunHooks : ∀ W : CliHooks, CliA0RunHooks mmpl gh W)
    (hRead589 : ∀ W : CliHooks,
      subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 cliRunBudgets_placed.readFile))
    (hAesEnc : ∀ W : CliHooks,
      HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesEncSym
        (aesEncSpec W.C.E E2E.HooksE.A0))
    (hAesDec : ∀ W : CliHooks,
      HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesDecSym
        (aesDecSpec W.C.D E2E.HooksE.A0))
    (hDecPk : lsmpl.base 547 ≠ 0#64 → ∀ W : CliHooks, RunProofs.DecPkD2cSlotOkPlaced mmpl gh W)
    (hSpqr : ∀ W : CliHooks, SpqrV1PlacedSeams mmpl gh W)
    (hLog462 : ∀ W : CliHooks,
      subroutine_ok
        (CryptoVerification.CliRatchet.DecPlaced.lsProg_463
          (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsmpl.base 462)
        (withLsCodeLoaded lsmpl
          CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.logClosurePlacedSpec)) :
    MainOkPqAllTightPlaced mmpl gh :=
  fun hDropNz =>
    main_ok_cli_pq_all_tight_placed mmpl gh
      hMainHooks
      (fun W => RunCompose.cliPubCallees_placed_ok mmpl gh W (hRunHooks W))
      (fun X W =>
        MainHops.cliSlotCallees_placed_of_seams mmpl gh X W hDropNz hG hMs hMc
          (hRunHooks W).runHooks (hRead589 W) (hAesEnc W) (hAesDec W) (hSpqr W) (hLog462 W))
      (hDecPk hDropNz)
      (fun W => pksmSlotOkPlaced_cli mmpl gh W hG)
      hDropNz

-- A2'' D1: A0 island, hMs/hMc discharged at a0Ghost
theorem main_ok_cli_pq_all_placed_of_w4 [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (hG : CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hMs : gh.memset = some CryptoVerification.LibsignalAesCbc.memsetHook)
    (hMc : gh.memcpy = some CryptoVerification.LibsignalAesCbc.memcpyHook)
    (hMainHooks : ∀ W : CliHooks, CliA0MainHooks mmpl gh W)
    (hRunHooks : ∀ W : CliHooks, CliA0RunHooks mmpl gh W)
    (hRead589 : ∀ W : CliHooks,
      subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 cliRunBudgets_placed.readFile))
    (hAesEnc : ∀ W : CliHooks,
      HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesEncSym
        (aesEncSpec W.C.E E2E.HooksE.A0))
    (hAesDec : ∀ W : CliHooks,
      HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesDecSym
        (aesDecSpec W.C.D E2E.HooksE.A0))
    (hDecPk : lsmpl.base 547 ≠ 0#64 → ∀ W : CliHooks, RunProofs.DecPkD2cSlotOkPlaced mmpl gh W)
    (hSpqr : ∀ W : CliHooks, SpqrV1PlacedSeams mmpl gh W)
    (hLog462 : ∀ W : CliHooks,
      subroutine_ok
        (CryptoVerification.CliRatchet.DecPlaced.lsProg_463
          (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsmpl.base 462)
        (withLsCodeLoaded lsmpl
          CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.logClosurePlacedSpec)) :
    MainOkPqAllPlaced mmpl gh :=
  (main_ok_cli_pq_all_tight_placed_of_w4 mmpl gh hG hMs hMc hMainHooks hRunHooks hRead589 hAesEnc hAesDec
    hDecPk hSpqr hLog462).toMainOkPqAllPlaced

-- A2'' D1: A0 island, hMs/hMc discharged at a0Ghost
theorem main_ok_cli_pq_tight_placed_of_w4 [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (hG : CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hMs : gh.memset = some CryptoVerification.LibsignalAesCbc.memsetHook)
    (hMc : gh.memcpy = some CryptoVerification.LibsignalAesCbc.memcpyHook)
    (hMainHooks : ∀ W : CliHooks, CliA0MainHooks mmpl gh W)
    (hRunHooks : ∀ W : CliHooks, CliA0RunHooks mmpl gh W)
    (hRead589 : ∀ W : CliHooks,
      subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 cliRunBudgets_placed.readFile))
    (hAesEnc : ∀ W : CliHooks,
      HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesEncSym
        (aesEncSpec W.C.E E2E.HooksE.A0))
    (hAesDec : ∀ W : CliHooks,
      HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesDecSym
        (aesDecSpec W.C.D E2E.HooksE.A0))
    (hDecPk : lsmpl.base 547 ≠ 0#64 → ∀ W : CliHooks, RunProofs.DecPkD2cSlotOkPlaced mmpl gh W)
    (hSpqr : ∀ W : CliHooks, SpqrV1PlacedSeams mmpl gh W)
    (hLog462 : ∀ W : CliHooks,
      subroutine_ok
        (CryptoVerification.CliRatchet.DecPlaced.lsProg_463
          (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsmpl.base 462)
        (withLsCodeLoaded lsmpl
          CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.logClosurePlacedSpec)) :
    MainOkCliPqTightPlaced mmpl gh :=
  (main_ok_cli_pq_all_tight_placed_of_w4 mmpl gh hG hMs hMc hMainHooks hRunHooks hRead589 hAesEnc hAesDec
    hDecPk hSpqr hLog462).toMainOkCliPqTightPlaced

-- A2'' D1: A0 island, hMs/hMc discharged at a0Ghost
theorem main_ok_cli_pq_placed_of_w4 [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (hG : CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hMs : gh.memset = some CryptoVerification.LibsignalAesCbc.memsetHook)
    (hMc : gh.memcpy = some CryptoVerification.LibsignalAesCbc.memcpyHook)
    (hMainHooks : ∀ W : CliHooks, CliA0MainHooks mmpl gh W)
    (hRunHooks : ∀ W : CliHooks, CliA0RunHooks mmpl gh W)
    (hRead589 : ∀ W : CliHooks,
      subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 cliRunBudgets_placed.readFile))
    (hAesEnc : ∀ W : CliHooks,
      HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesEncSym
        (aesEncSpec W.C.E E2E.HooksE.A0))
    (hAesDec : ∀ W : CliHooks,
      HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesDecSym
        (aesDecSpec W.C.D E2E.HooksE.A0))
    (hDecPk : lsmpl.base 547 ≠ 0#64 → ∀ W : CliHooks, RunProofs.DecPkD2cSlotOkPlaced mmpl gh W)
    (hSpqr : ∀ W : CliHooks, SpqrV1PlacedSeams mmpl gh W)
    (hLog462 : ∀ W : CliHooks,
      subroutine_ok
        (CryptoVerification.CliRatchet.DecPlaced.lsProg_463
          (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsmpl.base 462)
        (withLsCodeLoaded lsmpl
          CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.logClosurePlacedSpec)) :
    MainOkCliPqPlaced mmpl gh :=
  (main_ok_cli_pq_all_placed_of_w4 mmpl gh hG hMs hMc hMainHooks hRunHooks hRead589 hAesEnc hAesDec
    hDecPk hSpqr hLog462).toMainOkCliPqPlaced

-- A2'' D1: A0 island, hMs/hMc discharged at a0Ghost
theorem main_ok_over_tight_placed_of_w4 [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (hG : CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hMs : gh.memset = some CryptoVerification.LibsignalAesCbc.memsetHook)
    (hMc : gh.memcpy = some CryptoVerification.LibsignalAesCbc.memcpyHook)
    (hMainHooks : ∀ W : CliHooks, CliA0MainHooks mmpl gh W)
    (hRunHooks : ∀ W : CliHooks, CliA0RunHooks mmpl gh W)
    (hRead589 : ∀ W : CliHooks,
      subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 cliRunBudgets_placed.readFile))
    (hAesEnc : ∀ W : CliHooks,
      HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesEncSym
        (aesEncSpec W.C.E E2E.HooksE.A0))
    (hAesDec : ∀ W : CliHooks,
      HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesDecSym
        (aesDecSpec W.C.D E2E.HooksE.A0))
    (hDecPk : lsmpl.base 547 ≠ 0#64 → ∀ W : CliHooks, RunProofs.DecPkD2cSlotOkPlaced mmpl gh W)
    (hSpqr : ∀ W : CliHooks, SpqrV1PlacedSeams mmpl gh W)
    (hLog462 : ∀ W : CliHooks,
      subroutine_ok
        (CryptoVerification.CliRatchet.DecPlaced.lsProg_463
          (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsmpl.base 462)
        (withLsCodeLoaded lsmpl
          CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.logClosurePlacedSpec)) :
    MainOkOverTightPlaced mmpl gh :=
  (main_ok_cli_pq_all_tight_placed_of_w4 mmpl gh hG hMs hMc hMainHooks hRunHooks hRead589 hAesEnc hAesDec
    hDecPk hSpqr hLog462).toMainOkOverNormTightPlaced

-- A2'' D1: A0 island, hMs/hMc discharged at a0Ghost
theorem main_ok_over_placed_of_w4 [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (hG : CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hMs : gh.memset = some CryptoVerification.LibsignalAesCbc.memsetHook)
    (hMc : gh.memcpy = some CryptoVerification.LibsignalAesCbc.memcpyHook)
    (hMainHooks : ∀ W : CliHooks, CliA0MainHooks mmpl gh W)
    (hRunHooks : ∀ W : CliHooks, CliA0RunHooks mmpl gh W)
    (hRead589 : ∀ W : CliHooks,
      subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 cliRunBudgets_placed.readFile))
    (hAesEnc : ∀ W : CliHooks,
      HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesEncSym
        (aesEncSpec W.C.E E2E.HooksE.A0))
    (hAesDec : ∀ W : CliHooks,
      HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesDecSym
        (aesDecSpec W.C.D E2E.HooksE.A0))
    (hDecPk : lsmpl.base 547 ≠ 0#64 → ∀ W : CliHooks, RunProofs.DecPkD2cSlotOkPlaced mmpl gh W)
    (hSpqr : ∀ W : CliHooks, SpqrV1PlacedSeams mmpl gh W)
    (hLog462 : ∀ W : CliHooks,
      subroutine_ok
        (CryptoVerification.CliRatchet.DecPlaced.lsProg_463
          (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsmpl.base 462)
        (withLsCodeLoaded lsmpl
          CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.logClosurePlacedSpec)) :
    MainOkOverPlaced mmpl gh :=
  (main_ok_over_tight_placed_of_w4 mmpl gh hG hMs hMc hMainHooks hRunHooks hRead589 hAesEnc hAesDec
    hDecPk hSpqr hLog462).toMainOkOverPlaced

-- A2'' D1: A0 island, hMs/hMc discharged at a0Ghost
theorem main_ok_no_match_tight_placed_of_w4 [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (hG : CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hMs : gh.memset = some CryptoVerification.LibsignalAesCbc.memsetHook)
    (hMc : gh.memcpy = some CryptoVerification.LibsignalAesCbc.memcpyHook)
    (hMainHooks : ∀ W : CliHooks, CliA0MainHooks mmpl gh W)
    (hRunHooks : ∀ W : CliHooks, CliA0RunHooks mmpl gh W)
    (hRead589 : ∀ W : CliHooks,
      subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 cliRunBudgets_placed.readFile))
    (hAesEnc : ∀ W : CliHooks,
      HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesEncSym
        (aesEncSpec W.C.E E2E.HooksE.A0))
    (hAesDec : ∀ W : CliHooks,
      HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesDecSym
        (aesDecSpec W.C.D E2E.HooksE.A0))
    (hDecPk : lsmpl.base 547 ≠ 0#64 → ∀ W : CliHooks, RunProofs.DecPkD2cSlotOkPlaced mmpl gh W)
    (hSpqr : ∀ W : CliHooks, SpqrV1PlacedSeams mmpl gh W)
    (hLog462 : ∀ W : CliHooks,
      subroutine_ok
        (CryptoVerification.CliRatchet.DecPlaced.lsProg_463
          (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsmpl.base 462)
        (withLsCodeLoaded lsmpl
          CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.logClosurePlacedSpec)) :
    MainOkNoMatchTightPlaced mmpl gh :=
  (main_ok_cli_pq_all_tight_placed_of_w4 mmpl gh hG hMs hMc hMainHooks hRunHooks hRead589 hAesEnc hAesDec
    hDecPk hSpqr hLog462).toMainOkNoMatchTightPlaced

-- A2'' D1: A0 island, hMs/hMc discharged at a0Ghost
theorem main_ok_no_match_placed_of_w4 [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (hG : CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hMs : gh.memset = some CryptoVerification.LibsignalAesCbc.memsetHook)
    (hMc : gh.memcpy = some CryptoVerification.LibsignalAesCbc.memcpyHook)
    (hMainHooks : ∀ W : CliHooks, CliA0MainHooks mmpl gh W)
    (hRunHooks : ∀ W : CliHooks, CliA0RunHooks mmpl gh W)
    (hRead589 : ∀ W : CliHooks,
      subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 cliRunBudgets_placed.readFile))
    (hAesEnc : ∀ W : CliHooks,
      HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesEncSym
        (aesEncSpec W.C.E E2E.HooksE.A0))
    (hAesDec : ∀ W : CliHooks,
      HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesDecSym
        (aesDecSpec W.C.D E2E.HooksE.A0))
    (hDecPk : lsmpl.base 547 ≠ 0#64 → ∀ W : CliHooks, RunProofs.DecPkD2cSlotOkPlaced mmpl gh W)
    (hSpqr : ∀ W : CliHooks, SpqrV1PlacedSeams mmpl gh W)
    (hLog462 : ∀ W : CliHooks,
      subroutine_ok
        (CryptoVerification.CliRatchet.DecPlaced.lsProg_463
          (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsmpl.base 462)
        (withLsCodeLoaded lsmpl
          CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.logClosurePlacedSpec)) :
    MainOkNoMatchPlaced mmpl gh :=
  (main_ok_cli_pq_all_placed_of_w4 mmpl gh hG hMs hMc hMainHooks hRunHooks hRead589 hAesEnc hAesDec
    hDecPk hSpqr hLog462).toMainOkNoMatchPlaced

-- A2'' D1: A0 island, hMs/hMc discharged at a0Ghost
/-- Tightened SM-domain `MainOkCliSmTightPlaced mmpl gh` assembled via `main_ok_cli_sm_tight_placed`. -/
theorem main_ok_cli_sm_tight_placed_of_w4 [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (hG : CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hMs : gh.memset = some CryptoVerification.LibsignalAesCbc.memsetHook)
    (hMc : gh.memcpy = some CryptoVerification.LibsignalAesCbc.memcpyHook)
    (hMainHooks : ∀ W : CliHooks, CliA0MainHooks mmpl gh W)
    (hRunHooks : ∀ W : CliHooks, CliA0RunHooks mmpl gh W)
    (hRead589 : ∀ W : CliHooks,
      subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 cliRunBudgets_placed.readFile))
    (hAesEnc : ∀ W : CliHooks,
      HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesEncSym
        (aesEncSpec W.C.E E2E.HooksE.A0))
    (hAesDec : ∀ W : CliHooks,
      HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesDecSym
        (aesDecSpec W.C.D E2E.HooksE.A0))
    (hDecPk : lsmpl.base 547 ≠ 0#64 → ∀ W : CliHooks, RunProofs.DecPkD2cSlotOkPlaced mmpl gh W)
    (hSpqr : ∀ W : CliHooks, SpqrV1PlacedSeams mmpl gh W)
    (hLog462 : ∀ W : CliHooks,
      subroutine_ok
        (CryptoVerification.CliRatchet.DecPlaced.lsProg_463
          (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsmpl.base 462)
        (withLsCodeLoaded lsmpl
          CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.logClosurePlacedSpec)) :
    MainOkCliSmTightPlaced mmpl gh :=
  fun hDropNz W =>
    main_ok_cli_sm_tight_placed mmpl gh W
      (hMainHooks W)
      (RunCompose.cliPubCallees_placed_ok mmpl gh W (hRunHooks W))
      (MainHops.cliSlotCallees_placed_of_seams mmpl gh defaultModelExtras_placed W hDropNz hG hMs hMc
        (hRunHooks W).runHooks (hRead589 W) (hAesEnc W) (hAesDec W) (hSpqr W) (hLog462 W))
      (MainHops.cliPksmSlotExistsPlaced mmpl gh W hG)
      (cliDecPkSlotExistsPlaced_of_d2c mmpl gh W (hDecPk hDropNz W))

-- A2'' D1: A0 island, hMs/hMc discharged at a0Ghost
/-- Non-tight SM-domain `MainOkCliSmPlaced mmpl gh` assembled via `main_ok_cli_sm_placed`. -/
theorem main_ok_cli_sm_placed_of_w4 [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (hG : CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hMs : gh.memset = some CryptoVerification.LibsignalAesCbc.memsetHook)
    (hMc : gh.memcpy = some CryptoVerification.LibsignalAesCbc.memcpyHook)
    (hMainHooks : ∀ W : CliHooks, CliA0MainHooks mmpl gh W)
    (hRunHooks : ∀ W : CliHooks, CliA0RunHooks mmpl gh W)
    (hRead589 : ∀ W : CliHooks,
      subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 cliRunBudgets_placed.readFile))
    (hAesEnc : ∀ W : CliHooks,
      HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesEncSym
        (aesEncSpec W.C.E E2E.HooksE.A0))
    (hAesDec : ∀ W : CliHooks,
      HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesDecSym
        (aesDecSpec W.C.D E2E.HooksE.A0))
    (hDecPk : lsmpl.base 547 ≠ 0#64 → ∀ W : CliHooks, RunProofs.DecPkD2cSlotOkPlaced mmpl gh W)
    (hSpqr : ∀ W : CliHooks, SpqrV1PlacedSeams mmpl gh W)
    (hLog462 : ∀ W : CliHooks,
      subroutine_ok
        (CryptoVerification.CliRatchet.DecPlaced.lsProg_463
          (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsmpl.base 462)
        (withLsCodeLoaded lsmpl
          CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.logClosurePlacedSpec)) :
    MainOkCliSmPlaced mmpl gh :=
  fun hDropNz W =>
    main_ok_cli_sm_placed mmpl gh W
      (hMainHooks W)
      (RunCompose.cliPubCallees_placed_ok mmpl gh W (hRunHooks W))
      (MainHops.cliSlotCallees_placed_of_seams mmpl gh defaultModelExtras_placed W hDropNz hG hMs hMc
        (hRunHooks W).runHooks (hRead589 W) (hAesEnc W) (hAesDec W) (hSpqr W) (hLog462 W))
      (MainHops.cliPksmSlotExistsPlaced mmpl gh W hG)
      (cliDecPkSlotExistsPlaced_of_d2c mmpl gh W (hDecPk hDropNz W))

-- A2'' D1: A0 island, hMs/hMc discharged at a0Ghost
/-- Assembles `MainOkPqAllTightPlaced mmpl gh` with `hDecPk` discharged via
`decPkD2cSlotOk_placed_of_seams`. -/
theorem main_ok_cli_pq_all_tight_placed_of_poll_seams [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (hG : CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hMs : gh.memset = some CryptoVerification.LibsignalAesCbc.memsetHook)
    (hMc : gh.memcpy = some CryptoVerification.LibsignalAesCbc.memcpyHook)
    (hMainHooks : ∀ W : CliHooks, CliA0MainHooks mmpl gh W)
    (hRunHooks : ∀ W : CliHooks, CliA0RunHooks mmpl gh W)
    (hRead518 : ∀ W : CliHooks,
      subroutine_ok (Poll.dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 cliRunBudgets_placed.readFile))
    (hRead589 : ∀ W : CliHooks,
      subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 cliRunBudgets_placed.readFile))
    (hAesEnc : ∀ W : CliHooks,
      HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesEncSym
        (aesEncSpec W.C.E E2E.HooksE.A0))
    (hAesDec : ∀ W : CliHooks,
      HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesDecSym
        (aesDecSpec W.C.D E2E.HooksE.A0))
    (h_accept : ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
      subroutine_ok (lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 79)
        (pqxdhAcceptOptFieldsPlacedSpec
          (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) E2E.HooksE.A0))
    (h_accept_err : ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
      subroutine_ok (lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 79)
        (pqxdhAcceptErrOwnedPlacedSpec
          (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) E2E.HooksE.A0))
    (hLog519 : ∀ (mmpl' : Obj.MultiPlacement) (gh' : CliGhostHooks) (W' : CliHooks),
      subroutine_ok (lsProg_518 (cliGhostExterns gh' (cliExternsPlaced mmpl' W'))) (lsmpl.base 519)
        (withLsCodeLoaded lsmpl pqxdhLogClosurePlacedSpec))
    (hSpqr : ∀ W : CliHooks, SpqrV1PlacedSeams mmpl gh W)
    (hLog462 : ∀ W : CliHooks,
      subroutine_ok
        (CryptoVerification.CliRatchet.DecPlaced.lsProg_463
          (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsmpl.base 462)
        (withLsCodeLoaded lsmpl
          CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.logClosurePlacedSpec)) :
    MainOkPqAllTightPlaced mmpl gh :=
  main_ok_cli_pq_all_tight_placed_of_w4 mmpl gh hG hMs hMc hMainHooks hRunHooks hRead589 hAesEnc hAesDec
    (fun hDropNz W =>
      SignalSession.decPkD2cSlotOk_placed_of_seams mmpl gh W hDropNz hG (hRunHooks W) (hRead518 W)
        (hAesDec W) (hSpqr W) (fun X => h_accept X W) (fun X => h_accept_err X W) hLog519)
    hSpqr hLog462

-- A2'' D1: A0 island, hMs/hMc discharged at a0Ghost
/-- Assembles `MainOkCliSmTightPlaced mmpl gh` with `hDecPk` discharged via
`decPkD2cSlotOk_placed_of_seams`. -/
theorem main_ok_cli_sm_tight_placed_of_poll_seams [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (hG : CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hMs : gh.memset = some CryptoVerification.LibsignalAesCbc.memsetHook)
    (hMc : gh.memcpy = some CryptoVerification.LibsignalAesCbc.memcpyHook)
    (hMainHooks : ∀ W : CliHooks, CliA0MainHooks mmpl gh W)
    (hRunHooks : ∀ W : CliHooks, CliA0RunHooks mmpl gh W)
    (hRead518 : ∀ W : CliHooks,
      subroutine_ok (Poll.dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 cliRunBudgets_placed.readFile))
    (hRead589 : ∀ W : CliHooks,
      subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 cliRunBudgets_placed.readFile))
    (hAesEnc : ∀ W : CliHooks,
      HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesEncSym
        (aesEncSpec W.C.E E2E.HooksE.A0))
    (hAesDec : ∀ W : CliHooks,
      HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesDecSym
        (aesDecSpec W.C.D E2E.HooksE.A0))
    (h_accept : ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
      subroutine_ok (lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 79)
        (pqxdhAcceptOptFieldsPlacedSpec
          (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) E2E.HooksE.A0))
    (h_accept_err : ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
      subroutine_ok (lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 79)
        (pqxdhAcceptErrOwnedPlacedSpec
          (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) E2E.HooksE.A0))
    (hLog519 : ∀ (mmpl' : Obj.MultiPlacement) (gh' : CliGhostHooks) (W' : CliHooks),
      subroutine_ok (lsProg_518 (cliGhostExterns gh' (cliExternsPlaced mmpl' W'))) (lsmpl.base 519)
        (withLsCodeLoaded lsmpl pqxdhLogClosurePlacedSpec))
    (hSpqr : ∀ W : CliHooks, SpqrV1PlacedSeams mmpl gh W)
    (hLog462 : ∀ W : CliHooks,
      subroutine_ok
        (CryptoVerification.CliRatchet.DecPlaced.lsProg_463
          (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsmpl.base 462)
        (withLsCodeLoaded lsmpl
          CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.logClosurePlacedSpec)) :
    MainOkCliSmTightPlaced mmpl gh :=
  main_ok_cli_sm_tight_placed_of_w4 mmpl gh hG hMs hMc hMainHooks hRunHooks hRead589 hAesEnc hAesDec
    (fun hDropNz W =>
      SignalSession.decPkD2cSlotOk_placed_of_seams mmpl gh W hDropNz hG (hRunHooks W) (hRead518 W)
        (hAesDec W) (hSpqr W) (fun X => h_accept X W) (fun X => h_accept_err X W) hLog519)
    hSpqr hLog462

/-! ## 3. Closed `[LibsignalFullPlacement]` `main`-Level Theorems (`0` Mutated-Callee Seam Premises) -/

-- A2'' D1: A0 island, hMs/hMc discharged at a0Ghost
/-- Closed `[LibsignalFullPlacement]` assembly of `RunProofs.DecPkD2cSlotOkFrozenPlaced mmpl gh W`
(`SpqrV1PlacedSeams` is discharged via `spqrV1PlacedSeams_ok` and `h_accept` / `h_accept_err` /
`hLog519` are discharged inside `decPkD2cSlotOk_full_placed_of_seams`). -/
theorem decPkD2cSlotOk_frozen_placed [LibsignalFullPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hMs : gh.memset = some CryptoVerification.LibsignalAesCbc.memsetHook)
    (hMc : gh.memcpy = some CryptoVerification.LibsignalAesCbc.memcpyHook)
    (hRunA0 : CliA0RunHooks mmpl gh W)
    (hRead518 : subroutine_ok (Poll.dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 cliRunBudgets_placed.readFile))
    (hAesDec : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesDecSym
      (aesDecSpec W.C.D E2E.HooksE.A0))
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsLibcruxHmacSymCli
      (libcruxHmacSpec W.C.F E2E.HooksE.A0)) :
    RunProofs.DecPkD2cSlotOkFrozenPlaced mmpl gh W :=
  let hSpqr :=
    LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsInst.spqrV1PlacedSeams_ok
      mmpl gh W hG hMs hMc hHmac
  RunProofs.Poll.decPkD2cSlotOk_full_placed_of_seams mmpl gh W
    hRunA0.runHooks hRead518 (Slots.stage2ContractsMinPlaced_cli mmpl gh W hG)
    hDropNz hG hSpqr
    (cliTryDecryptPqV1_placed_of_spqr mmpl gh W hG hAesDec hSpqr)

/-- Specializes `RunProofs.DecPkD2cSlotOkFrozenPlaced mmpl gh W` at `X := defaultModelExtras_placed`
to witness `MainHops.CliDecPkSlotExistsFrozenPlaced mmpl gh W`. -/
theorem cliDecPkSlotExistsFrozenPlaced_of_d2c [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (h : RunProofs.DecPkD2cSlotOkFrozenPlaced mmpl gh W) :
    MainHops.CliDecPkSlotExistsFrozenPlaced mmpl gh W :=
  ⟨decPkDefD2c defaultModelExtras_placed ⟨W.C, W.Q⟩ Slots.scopeIn,
   DecPkOkD2c ⟨W.C, W.Q⟩ Slots.scopeIn,
   cliDecryptPrekeyNeed cliRunBudgets_placed,
   by decide,
   fun S needs hfiles hdec hok hneed =>
     h defaultModelExtras_placed S needs hfiles hdec hok hneed⟩

-- A2'' D1: A0 island, hMs/hMc discharged at a0Ghost
/-- Closed `[LibsignalFullPlacement]` 6-clause PQXDH + `NoMatch` `main` theorem with zero
mutated-callee seam premises. -/
theorem main_ok_cli_pq_all_tight_frozen_placed [LibsignalFullPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (hG : CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hMs : gh.memset = some CryptoVerification.LibsignalAesCbc.memsetHook)
    (hMc : gh.memcpy = some CryptoVerification.LibsignalAesCbc.memcpyHook)
    (hMainHooks : ∀ W : CliHooks, CliA0MainHooks mmpl gh W)
    (hRunHooks : ∀ W : CliHooks, CliA0RunHooks mmpl gh W)
    (hRead518 : ∀ W : CliHooks,
      subroutine_ok (Poll.dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 cliRunBudgets_placed.readFile))
    (hRead589 : ∀ W : CliHooks,
      subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 cliRunBudgets_placed.readFile))
    (hAesEnc : ∀ W : CliHooks,
      HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesEncSym
        (aesEncSpec W.C.E E2E.HooksE.A0))
    (hAesDec : ∀ W : CliHooks,
      HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesDecSym
        (aesDecSpec W.C.D E2E.HooksE.A0))
    (hHmac : ∀ W : CliHooks, HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W))
      lsLibcruxHmacSymCli (libcruxHmacSpec W.C.F E2E.HooksE.A0)) :
    MainOkPqAllTightFrozenPlaced mmpl gh :=
  fun hDropNz =>
    main_ok_cli_pq_all_tight_full_placed mmpl gh
      hMainHooks
      (fun W => RunCompose.cliPubCallees_frozen_placed_ok mmpl gh W (hRunHooks W))
      (fun X W =>
        MainHops.cliSlotCallees_full_placed_of_seams mmpl gh X W hDropNz hG hMs hMc
          (hRunHooks W).runHooks (hRead589 W) (hAesEnc W) (hAesDec W)
          (LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsInst.spqrV1PlacedSeams_ok
            mmpl gh W hG hMs hMc (hHmac W)))
      (fun W =>
        decPkD2cSlotOk_frozen_placed mmpl gh W hDropNz hG hMs hMc (hRunHooks W) (hRead518 W) (hAesDec W)
          (hHmac W))
      (fun W => pksmSlotOkPlaced_cli mmpl gh W hG)
      hDropNz

-- A2'' D1: A0 island, hMs/hMc discharged at a0Ghost
/-- Closed `[LibsignalFullPlacement]` 5-clause PQXDH `main` theorem with zero mutated-callee
seam premises. -/
theorem main_ok_cli_pq_tight_frozen_placed [LibsignalFullPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (hG : CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hMs : gh.memset = some CryptoVerification.LibsignalAesCbc.memsetHook)
    (hMc : gh.memcpy = some CryptoVerification.LibsignalAesCbc.memcpyHook)
    (hMainHooks : ∀ W : CliHooks, CliA0MainHooks mmpl gh W)
    (hRunHooks : ∀ W : CliHooks, CliA0RunHooks mmpl gh W)
    (hRead518 : ∀ W : CliHooks,
      subroutine_ok (Poll.dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 cliRunBudgets_placed.readFile))
    (hRead589 : ∀ W : CliHooks,
      subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 cliRunBudgets_placed.readFile))
    (hAesEnc : ∀ W : CliHooks,
      HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesEncSym
        (aesEncSpec W.C.E E2E.HooksE.A0))
    (hAesDec : ∀ W : CliHooks,
      HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesDecSym
        (aesDecSpec W.C.D E2E.HooksE.A0))
    (hHmac : ∀ W : CliHooks, HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W))
      lsLibcruxHmacSymCli (libcruxHmacSpec W.C.F E2E.HooksE.A0)) :
    MainOkCliPqTightFrozenPlaced mmpl gh :=
  (main_ok_cli_pq_all_tight_frozen_placed mmpl gh hG hMs hMc hMainHooks hRunHooks hRead518 hRead589 hAesEnc
    hAesDec hHmac).toMainOkCliPqTightFrozenPlaced

-- A2'' D1: A0 island, hMs/hMc discharged at a0Ghost
/-- Closed `[LibsignalFullPlacement]` `MainOkOverTightFrozenPlaced` theorem with zero mutated-callee
seam premises. -/
theorem main_ok_over_tight_frozen_placed [LibsignalFullPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (hG : CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hMs : gh.memset = some CryptoVerification.LibsignalAesCbc.memsetHook)
    (hMc : gh.memcpy = some CryptoVerification.LibsignalAesCbc.memcpyHook)
    (hMainHooks : ∀ W : CliHooks, CliA0MainHooks mmpl gh W)
    (hRunHooks : ∀ W : CliHooks, CliA0RunHooks mmpl gh W)
    (hRead518 : ∀ W : CliHooks,
      subroutine_ok (Poll.dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 cliRunBudgets_placed.readFile))
    (hRead589 : ∀ W : CliHooks,
      subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 cliRunBudgets_placed.readFile))
    (hAesEnc : ∀ W : CliHooks,
      HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesEncSym
        (aesEncSpec W.C.E E2E.HooksE.A0))
    (hAesDec : ∀ W : CliHooks,
      HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesDecSym
        (aesDecSpec W.C.D E2E.HooksE.A0))
    (hHmac : ∀ W : CliHooks, HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W))
      lsLibcruxHmacSymCli (libcruxHmacSpec W.C.F E2E.HooksE.A0)) :
    MainOkOverTightFrozenPlaced mmpl gh :=
  (main_ok_cli_pq_all_tight_frozen_placed mmpl gh hG hMs hMc hMainHooks hRunHooks hRead518 hRead589 hAesEnc
    hAesDec hHmac).toMainOkOverTightFrozenPlaced

-- A2'' D1: A0 island, hMs/hMc discharged at a0Ghost
/-- Closed `[LibsignalFullPlacement]` standalone `NoMatch` `main` theorem with zero mutated-callee
seam premises. -/
theorem main_ok_no_match_tight_frozen_placed [LibsignalFullPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (hG : CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hMs : gh.memset = some CryptoVerification.LibsignalAesCbc.memsetHook)
    (hMc : gh.memcpy = some CryptoVerification.LibsignalAesCbc.memcpyHook)
    (hMainHooks : ∀ W : CliHooks, CliA0MainHooks mmpl gh W)
    (hRunHooks : ∀ W : CliHooks, CliA0RunHooks mmpl gh W)
    (hRead518 : ∀ W : CliHooks,
      subroutine_ok (Poll.dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 cliRunBudgets_placed.readFile))
    (hRead589 : ∀ W : CliHooks,
      subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 cliRunBudgets_placed.readFile))
    (hAesEnc : ∀ W : CliHooks,
      HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesEncSym
        (aesEncSpec W.C.E E2E.HooksE.A0))
    (hAesDec : ∀ W : CliHooks,
      HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesDecSym
        (aesDecSpec W.C.D E2E.HooksE.A0))
    (hHmac : ∀ W : CliHooks, HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W))
      lsLibcruxHmacSymCli (libcruxHmacSpec W.C.F E2E.HooksE.A0)) :
    MainOkNoMatchTightFrozenPlaced mmpl gh :=
  (main_ok_cli_pq_all_tight_frozen_placed mmpl gh hG hMs hMc hMainHooks hRunHooks hRead518 hRead589 hAesEnc
    hAesDec hHmac).toMainOkNoMatchTightFrozenPlaced

end CryptoVerification.SignalSession

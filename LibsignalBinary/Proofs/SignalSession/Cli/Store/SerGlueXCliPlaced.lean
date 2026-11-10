/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsA1
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Hooks

/-!
# Relocatable `SessionRecord::serialize` Glue at `cliGhostExterns`

Instantiates `SerContractsXPlaced` and `serializeCanonSpecX` on Block `52` at
`cliGhostExterns g (cliExternsPlaced mmpl W)` under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Store.SerGlueX

open Arm64 Arm64.Obj ProofLib
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.Slots
  (CliGhostA0Hooks a0Ghost cliGhostA0Hooks_a0Ghost
   cliExternsPlaced_alloc_sat cliExternsPlaced_dealloc_sat cliExternsPlaced_realloc_sat
   cliExternsPlaced_shim_sat cliExternsPlaced_sessionMemmove_sat cliExternsPlaced_sessionMemcpy_sat
   cliGhostExterns_sat_of_cliExternsPlaced
   cliGhostExterns_panic_handle_error cliGhostExterns_panic_handle_alloc_error)

section Placed

/-- `SerContractsXPlaced A (cliGhostExterns g (cliExternsPlaced mmpl W))` from
`CliGhostA0Hooks A g`. -/
theorem serContractsX_placed_of_cliHooks [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) {A : RustAlloc}
    (hG : CliGhostA0Hooks A g) :
    Proofs.libsignal.Hooks2.SerContractsXPlaced A
      (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  Proofs.libsignal.Hooks2.SerContractsXPlaced.of_hooks
    (cliExternsPlaced_alloc_sat mmpl g W hG)
    (cliExternsPlaced_dealloc_sat mmpl g W hG)
    (cliExternsPlaced_realloc_sat mmpl g W hG)
    (cliExternsPlaced_shim_sat mmpl g W hG.shim_eq)
    (cliGhostExterns_sat_of_cliExternsPlaced mmpl g W
      (cliExternsPlaced_sessionMemmove_sat mmpl W _))
    (cliExternsPlaced_sessionMemcpy_sat mmpl g W hG _)
    (cliGhostExterns_panic_handle_error mmpl g W)
    (cliGhostExterns_panic_handle_alloc_error mmpl g W)

/-- `SerContractsXPlaced` at `E2E.HooksE.A0` and `cliGhostExterns g (cliExternsPlaced mmpl W)`. -/
theorem serContractsX_cli_placed [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostA0Hooks E2E.HooksE.A0 g) :
    Proofs.libsignal.Hooks2.SerContractsXPlaced E2E.HooksE.A0
      (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  serContractsX_placed_of_cliHooks mmpl g W hG

/-- Closed `a0Ghost` instantiation of `serContractsX_cli_placed`. -/
theorem serContractsX_cli_a0Ghost [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (W : CliHooks) :
    Proofs.libsignal.Hooks2.SerContractsXPlaced E2E.HooksE.A0
      (cliGhostExterns a0Ghost (cliExternsPlaced mmpl W)) :=
  serContractsX_cli_placed mmpl a0Ghost W cliGhostA0Hooks_a0Ghost

/-- `serializeCanonSpecX E2E.HooksE.A0` on Block `52` at
`cliGhostExterns g (cliExternsPlaced mmpl W)` (`withLsCodeLoaded`). -/
theorem serializeCanonX_cli_placed [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostA0Hooks E2E.HooksE.A0 g) :
    subroutine_ok
      (CryptoVerification.E2E.Record.Placed.lsProg_52
        (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (Proofs.libsignal.Hooks2.serializeCanonSpecX E2E.HooksE.A0)) :=
  serializeCanonX_placed_ok_of_serContractsX (serContractsX_cli_placed mmpl g W hG)

/-- Caller-block-polymorphic `StoreKit.withLsCodeRoLoaded` form of `serializeCanonX_cli_placed`. -/
theorem serializeCanonX_cli_placed_lscro [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hG : CliGhostA0Hooks E2E.HooksE.A0 g)
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 52)
      (StoreKit.withLsCodeRoLoaded lsmpl
        (Proofs.libsignal.Hooks2.serializeCanonSpecX E2E.HooksE.A0)) :=
  serializeCanonX_placed_lscro_of_serContractsX (serContractsX_cli_placed mmpl g W hG) hblk

end Placed

end CryptoVerification.SignalSession.Cli.Store.SerGlueX

namespace CryptoVerification.SignalSession.Cli.Store.SerGlueXCli
export CryptoVerification.SignalSession.Cli.Store.SerGlueX
  (serContractsX_cli_placed serContractsX_cli_a0Ghost
   serializeCanonX_cli_placed serializeCanonX_cli_placed_lscro)
end CryptoVerification.SignalSession.Cli.Store.SerGlueXCli

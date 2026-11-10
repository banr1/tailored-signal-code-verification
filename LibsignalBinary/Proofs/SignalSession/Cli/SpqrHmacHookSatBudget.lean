/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlaced
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedSegs

/-!
# Budget-Threaded `libcrux_hmac::hmac` `HookSat` Witnesses

Proves `HookSat` witnesses for `spqrLibcruxHmacSym` (`libcrux_hmac::hmac`) on `cliExternsPlaced`
and `cliGhostExterns` from `VerifiedLibraries.mallocngLib.Placeable mmpl`, for both generic
`mallocngHookRustCliAllocBudget` and concrete `fineHookRustCliAllocBudget`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.SpqrHmacHookSatBudget

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic
open CryptoVerification.E2E (libcruxHmacHookMallocng)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliExternsPlaced_row cliGhostExterns)
open CryptoVerification.SignalSession.Cli.Slots
  (cliGhostExterns_sat_of_cliExternsPlaced libcruxHmac_row_placed lsLibcruxHmacSymCli)
open CryptoVerification.SpqrV1.Unchunked (spqrLibcruxHmacSym)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits MallocngCostModelIface MallocngCostModelSound)
open LibsignalBinary.Heap.Fine (fineCostModel)
open LibsignalBinary.Heap.SpecBudget (libcruxHmacBudgetSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget
  (fineHookRustCliAllocBudget fineLibcruxHmac_budget_hookSat
   libcruxHmacHookMallocng_budget_ok mallocngHookRustCliAllocBudget)

/-- Direct `cliExternsPlaced` lookup equation for `spqrLibcruxHmacSym` (`libcrux_hmac::hmac`). -/
theorem hpo_cliExternsPlaced_libcruxHmac_eq (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliExternsPlaced mmpl W spqrLibcruxHmacSym = some (libcruxHmacHookMallocng mmpl W.C.F) :=
  cliExternsPlaced_row mmpl W (libcruxHmac_row_placed mmpl W)

/-- `HookSat (cliExternsPlaced mmpl W) spqrLibcruxHmacSym` over any `(M, I)` satisfying
    `MallocngCostModelSound M I`. -/
theorem hpo_cliExternsPlaced_libcruxHmac_mallocngHook_sat
    {M : AllocCostModel} {I : MallocngCostModelIface M} (hS : MallocngCostModelSound M I)
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (W : CliHooks)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl) :
    HookSat (cliExternsPlaced mmpl W) spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec W.C.F M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim) :=
  ⟨libcruxHmacHookMallocng mmpl W.C.F, hpo_cliExternsPlaced_libcruxHmac_eq mmpl W,
    libcruxHmacHookMallocng_budget_ok hS γ tp brkStart lim hPl W.C.F⟩

/-- `HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym` over any `(M, I)`
    satisfying `MallocngCostModelSound M I`. -/
theorem hpo_cliLibcruxHmac_mallocngHook_budget_hookSat
    {M : AllocCostModel} {I : MallocngCostModelIface M} (hS : MallocngCostModelSound M I)
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (gh : CliGhostHooks) (W : CliHooks)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl) :
    HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec W.C.F M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim) :=
  cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
    (hpo_cliExternsPlaced_libcruxHmac_mallocngHook_sat hS γ mmpl tp brkStart lim W hPl)

/-- Concrete `(fineCostModel, fineHookRustCliAllocBudget γ mmpl tp brkStart)` `HookSat` witness for
    `spqrLibcruxHmacSym` on `cliExternsPlaced mmpl W`. -/
theorem hpo_cliExternsPlaced_libcruxHmac_budget_sat
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (W : CliHooks)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl) :
    HookSat (cliExternsPlaced mmpl W) spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec W.C.F fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim) :=
  fineLibcruxHmac_budget_hookSat γ tp brkStart lim hPl W.C.F
    (hpo_cliExternsPlaced_libcruxHmac_eq mmpl W)

/-- Concrete `(fineCostModel, fineHookRustCliAllocBudget γ mmpl tp brkStart)` `HookSat` witness for
    `spqrLibcruxHmacSym` on `cliGhostExterns gh (cliExternsPlaced mmpl W)`, matching the `hHmac`
    hypothesis of `spqrV1PlacedSeamsOfEnv_of_sendCoins` and `cliSpqrSendCoins_placed_ok_*`. -/
theorem hpo_cliLibcruxHmac_budget_hookSat
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (gh : CliGhostHooks) (W : CliHooks)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl) :
    HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec W.C.F fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim) :=
  cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
    (hpo_cliExternsPlaced_libcruxHmac_budget_sat γ mmpl tp brkStart lim W hPl)

/-- Direct `cliGhostExterns` lookup equation for `spqrLibcruxHmacSym`. -/
theorem hpo_cliGhostExterns_libcruxHmac_eq
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) :
    cliGhostExterns gh (cliExternsPlaced mmpl W) spqrLibcruxHmacSym =
      some (libcruxHmacHookMallocng mmpl W.C.F) := by
  have hother :=
    CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns_other gh
      (cliExternsPlaced mmpl W) (sym := spqrLibcruxHmacSym)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  exact hother.trans (hpo_cliExternsPlaced_libcruxHmac_eq mmpl W)

end LibsignalBinary.Proofs.SignalSession.Cli.SpqrHmacHookSatBudget

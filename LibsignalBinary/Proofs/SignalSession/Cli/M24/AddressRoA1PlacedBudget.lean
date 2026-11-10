/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.M24.AddressRoPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Placed Budgeted Read-Only `signal_session::address` and `MainCalleesROBlk617` Discharge

Discharges the `memrchrSpecRO` external-hook premise of `address_ro_placed_ok` against
`memrchrHook` and derives `MainCalleesROBlk617` from `MainCalleesBlk617`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.M24.AddressRoA1PlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalPublicApi.StoreKit (withLsRoCl)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.SignalSession
  (CliHooks cliExternsPlaced fromUtf8Hook lsFromUtf8Sym lsMemrchrSym memrchrHook strlenHook)
open CryptoVerification.SignalSession.Cli.Main.Placed (lsProg_617)
open CryptoVerification.SignalSession.Cli.MainHops
  (cliExternsPlaced_fromUtf8 cliExternsPlaced_memrchr cliExternsPlaced_strlen)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.AddressRoPlacedBudget
  (address_ro_placed_ok address_ro_placed_ok_rocl)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO
  (MainCalleesROBlk617 addressSpecRO mainCalleesROBlk617_of_mainCalleesBlk617_and_addr
   memrchr_ro_blk580_ok_of_hooks)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget (MainCalleesBlk617)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (AllocContractsFsPlaced)

/-- Budget-threaded `signal_session::address` contract for read-only `argv` slices under
`AllocContractsFsPlaced` and `memrchrHook`. -/
theorem address_ro_placed_ok_a1_of_hooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {resStack : Nat}
    (hFs : AllocContractsFsPlaced A lim H)
    (hext : H lsMemrchrSym = some memrchrHook)
    (hres : 0xB0 + extHookStack ≤ resStack) (hres64 : resStack ≤ 2 ^ 63) :
    subroutine_ok (lsProg_617 H) (lsmpl.base 580)
      (withLsRoCl lsmpl (addressSpecRO A lim uuidTryParse resStack)) :=
  address_ro_placed_ok hFs (memrchr_ro_blk580_ok_of_hooks hext) hres hres64

theorem address_ro_placed_ok_a1_rocl_of_hooks [LibsignalPlacement] {prog : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} [IsLsBlockProg prog i H] {resStack : Nat}
    (hFs : AllocContractsFsPlaced A lim H)
    (hext : H lsMemrchrSym = some memrchrHook)
    (hres : 0xB0 + extHookStack ≤ resStack) (hres64 : resStack ≤ 2 ^ 63)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsmpl.base 580)
      (withLsRoCl lsmpl (addressSpecRO A lim uuidTryParse resStack)) :=
  address_ro_placed_ok_rocl (prog := prog) (i := i)
    hFs (memrchr_ro_blk580_ok_of_hooks hext) hres hres64 hi

theorem address_ro_placed_ok_a1 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (W : CliHooks)
    (hFs : AllocContractsFsPlaced A lim (cliExternsPlaced mmpl W))
    {resStack : Nat}
    (hres : 0xB0 + extHookStack ≤ resStack) (hres64 : resStack ≤ 2 ^ 63) :
    subroutine_ok (lsProg_617 (cliExternsPlaced mmpl W)) (lsmpl.base 580)
      (withLsRoCl lsmpl (addressSpecRO A lim uuidTryParse resStack)) :=
  address_ro_placed_ok_a1_of_hooks hFs (cliExternsPlaced_memrchr mmpl W) hres hres64

/-- Derive `MainCalleesROBlk617` from `MainCalleesBlk617` and the `strlen`, `from_utf8`, and
`memrchr` hook entries. -/
theorem mainCalleesROBlk617_of_mainCalleesBlk617_and_hooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {hookStack resStack : Nat}
    {err : List (BitVec 8) → BitVec 64 × BitVec 16}
    (hc : MainCalleesBlk617 A lim H uuidTryParse hookStack resStack)
    (hstrlen : H "strlen" = some strlenHook)
    (hutf8 : H lsFromUtf8Sym = some (fromUtf8Hook err))
    (hmemrchr : H lsMemrchrSym = some memrchrHook)
    (hres : 0xB0 + extHookStack ≤ resStack) (hres64 : resStack ≤ 2 ^ 63) :
    MainCalleesROBlk617 A lim H uuidTryParse hookStack resStack :=
  mainCalleesROBlk617_of_mainCalleesBlk617_and_addr hc hstrlen hutf8
    (address_ro_placed_ok_a1_of_hooks hc.allocFs hmemrchr hres hres64)

theorem mainCalleesROBlk617_of_mainCalleesBlk617_cliExterns [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (W : CliHooks) {hookStack resStack : Nat}
    (hc : MainCalleesBlk617 A lim (cliExternsPlaced mmpl W) uuidTryParse hookStack resStack)
    (hres : 0xB0 + extHookStack ≤ resStack) (hres64 : resStack ≤ 2 ^ 63) :
    MainCalleesROBlk617 A lim (cliExternsPlaced mmpl W) uuidTryParse hookStack resStack :=
  mainCalleesROBlk617_of_mainCalleesBlk617_and_hooks hc
    (cliExternsPlaced_strlen mmpl W) (cliExternsPlaced_fromUtf8 mmpl W)
    (cliExternsPlaced_memrchr mmpl W)
    hres hres64

end LibsignalBinary.Proofs.SignalSession.Cli.M24.AddressRoA1PlacedBudget

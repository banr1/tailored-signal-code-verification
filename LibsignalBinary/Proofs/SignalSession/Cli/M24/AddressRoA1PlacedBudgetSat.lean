/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.M24.AddressRoA1PlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesROSat -- proof-setup: allow-public-import

/-!
# `HookSat` Sibling of `AddressRoA1PlacedBudget` (`AddressRoA1PlacedBudgetSat`)

Replaces both `H lsFromUtf8Sym = some (fromUtf8Hook err)` (dropping `err`) and
`H lsMemrchrSym = some memrchrHook` with `HookSat` contracts
(`withVmPreserved (fromUtf8AsciiSpecRO hookStack)` and
`withVmPreserved (memrchrSpecRO extHookStack)`) across
`address_ro_placed_ok_a1_of_hooks_sat`, `address_ro_placed_ok_a1_rocl_of_hooks_sat`, and
`mainCalleesROBlk617_of_mainCalleesBlk617_and_hooks_sat`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.M24.AddressRoA1PlacedBudgetSat

open Arm64 ProofLib
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalPublicApi.StoreKit (withLsRoCl)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.SignalSession (lsFromUtf8Sym lsMemrchrSym strlenHook)
open CryptoVerification.SignalSession.Cli.Main.Placed (lsProg_617)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (withLsRet)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.AddressRoPlacedBudget
  (address_ro_placed_ok_ls address_ro_placed_ok_rocl_ls)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO
  (MainCalleesROBlk617 addressSpecRO fromUtf8AsciiSpecRO memrchrSpecRO)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesROSat
  (mainCalleesROBlk617_of_mainCalleesBlk617_and_addr_sat memrchr_ro_blk580_ok_of_hooks_sat)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget (MainCalleesBlk617)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (AllocContractsFsPlaced)

/-- `HookSat` sibling of `address_ro_placed_ok_a1_of_hooks` (`AddressRoA1PlacedBudget.lean:61`). -/
theorem address_ro_placed_ok_a1_of_hooks_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {resStack : Nat}
    (hFs : AllocContractsFsPlaced A lim H)
    (hext : HookSat H lsMemrchrSym (withLsRet (withVmPreserved (memrchrSpecRO extHookStack))))
    (hres : 0xB0 + extHookStack ≤ resStack) (hres64 : resStack ≤ 2 ^ 63) :
    subroutine_ok (lsProg_617 H) (lsmpl.base 580)
      (withLsRoCl lsmpl (addressSpecRO A lim uuidTryParse resStack)) :=
  address_ro_placed_ok_ls hFs (memrchr_ro_blk580_ok_of_hooks_sat hext) hres hres64

/-- `HookSat` sibling of `address_ro_placed_ok_a1_rocl_of_hooks` (`AddressRoA1PlacedBudget.lean:73`). -/
theorem address_ro_placed_ok_a1_rocl_of_hooks_sat [LibsignalPlacement] {prog : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} [IsLsBlockProg prog i H] {resStack : Nat}
    (hFs : AllocContractsFsPlaced A lim H)
    (hext : HookSat H lsMemrchrSym (withLsRet (withVmPreserved (memrchrSpecRO extHookStack))))
    (hres : 0xB0 + extHookStack ≤ resStack) (hres64 : resStack ≤ 2 ^ 63)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsmpl.base 580)
      (withLsRoCl lsmpl (addressSpecRO A lim uuidTryParse resStack)) :=
  address_ro_placed_ok_rocl_ls (prog := prog) (i := i)
    hFs (memrchr_ro_blk580_ok_of_hooks_sat hext) hres hres64 hi

/-- `HookSat` sibling of `mainCalleesROBlk617_of_mainCalleesBlk617_and_hooks`
    (`AddressRoA1PlacedBudget.lean:98`), weakening both `hutf8` and `hmemrchr` to `HookSat` and
    dropping `err`. -/
theorem mainCalleesROBlk617_of_mainCalleesBlk617_and_hooks_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {hookStack resStack : Nat}
    (hc : MainCalleesBlk617 A lim H uuidTryParse hookStack resStack)
    (hstrlen : H "strlen" = some strlenHook)
    (hutf8 : HookSat H lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpecRO hookStack)))
    (hmemrchr : HookSat H lsMemrchrSym (withLsRet (withVmPreserved (memrchrSpecRO extHookStack))))
    (hres : 0xB0 + extHookStack ≤ resStack) (hres64 : resStack ≤ 2 ^ 63) :
    MainCalleesROBlk617 A lim H uuidTryParse hookStack resStack :=
  mainCalleesROBlk617_of_mainCalleesBlk617_and_addr_sat hc hstrlen hutf8
    (address_ro_placed_ok_a1_of_hooks_sat hc.allocFs hmemrchr hres hres64)

end LibsignalBinary.Proofs.SignalSession.Cli.M24.AddressRoA1PlacedBudgetSat

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSitesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.HelpersPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Call Helpers for `main_m2` Dispatch

Provides budget-threaded `.keepsFs` callee corollaries (`address`, `dealloc`, `memcpy`) from
`HopsPlacedBudget.MainCalleesBlk617` on Block `617`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

open Arm64 ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit (withLsRoCl)
open CryptoVerification.LibsignalTripleRatchet (extHookStack memcpyName)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli.Main.Placed (blkPC_617 blkPl_617)

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.HelpersPlacedBudget

open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.CalleesBudget (addressSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget (MainCalleesBlk617)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSitesPlacedBudget
  (main_dealloc_fs_placed_ok main_memcpy2_fs_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (session2MemcpyBudgetSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustDeallocExternSpecWithStack)

/-! ## `.keepsFs` callee corollaries from `MainCalleesBlk617` -/

theorem address_keepsFs_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {uuidParse : UuidParser}
    {hookStack resStack : Nat}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsmpl.base 580)
      (withLsRoCl lsmpl (addressSpec A lim uuidParse resStack).keepsFs) := by
  refine subroutine_ok_mono hc.address (fun _ _ _ hp => hp) (fun (x, st) R s1 sm hpost => ?_)
  dsimp only [withLsRoCl, Spec.keepsFs, addressSpec] at hpost ⊢
  refine Satisfies.mono (sepConj_mono_left (sepConj_mono_right ?_)) hpost
  refine Entails.sepExists_elim fun evs => ?_
  refine Entails.pure_left fun hpure => ?_
  refine Entails.pure_right hpure.2.1 ?_
  refine Entails.sepExists_right evs ?_
  exact Entails.pure_right hpure (Entails.refl _)

theorem dealloc_keepsFs_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {uuidParse : UuidParser}
    {hookStack resStack : Nat}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsRustDeallocSymCli)
      (withLsRoCl lsmpl (rustDeallocExternSpecWithStack M A lim extHookStack).keepsFs) :=
  main_dealloc_fs_placed_ok hc.allocFs

theorem memcpy_keepsFs_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {uuidParse : UuidParser}
    {hookStack resStack : Nat}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ memcpyName)
      (withLsRoCl lsmpl session2MemcpyBudgetSpecX.keepsFs) :=
  main_memcpy2_fs_placed_ok hc.allocFs

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.HelpersPlacedBudget

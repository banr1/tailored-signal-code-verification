/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityFutDropExt
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.ShimsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Placed `cliIdFutDrop` Contract

Relocatable `[LibsignalPlacement]` `futDropSpec` contracts for Block `547` (`cliIdFutDropName`).
-/

@[expose] public section
set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.KitInst

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.StoreCalleesProofs

/-- `futDrop` (Block `547`, `lsmpl.base 547`) meets `futDropSpec` on `lsProg_547 H`. -/
theorem cliIdFutDrop_block_placed_ok [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok (lsProg_547 H) (lsmpl.base 547) futDropSpec :=
  futDrop_block_placed_ok H

/-- `futDrop` (Block `547`, `lsmpl.base 547`) meets `withLsCodeRoLoaded lsmpl futDropSpec` on any
caller block `i < 619` (`[IsLsBlockProg callerProg i H]`). -/
theorem cliIdFutDrop_caller_placed_ok [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {H : LibsignalHooks} [IsLsBlockProg callerProg i H] (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 547)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl futDropSpec) := by
  have hrocl := ls_subroutine_ok_rocl_of_block (callerProg := callerProg)
    (LibsignalPublicApi.StoreKit.subroutine_ok_withLsCodeRoLoaded_of_plain
      (futDrop_block_placed_ok H))
    hi (by decide) (by decide)
  exact subroutine_ok_mono hrocl (fun _ _ _ hp => hp)
    (fun _ _ _ _ hq => by
      dsimp only [LibsignalPublicApi.StoreKit.withLsRoCl,
        LibsignalPublicApi.StoreKit.withLsCodeRoLoaded] at hq ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq
      exact hq.2)

end CryptoVerification.SignalSession.Cli.KitInst

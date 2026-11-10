/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Proofs.RecordCodecs.AssemblyBudget
public import LibsignalBinary.Proofs.RecordCodecs.SignedAssemblyBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.KitCodecsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable `[LibsignalPlacement]` CLI Record Decoders

Instantiates budget-threaded `[LibsignalPlacement]` record decoders at `cliExternsPlaced mmpl W`
from `SkeletonPlacedBudget.RunHooksPlaced A lim`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.KitCodecsPlacedBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.RecordCodecs.Placed
  (blkPl_18 blkPl_65 blkPl_84 blkPl_595 lsProg_18 lsProg_65 lsProg_84 lsProg_595)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli (CliGhostHooks cliGhostExterns)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.RecordCodecs.AssemblyBudget
  (identityKey_decode_placed_ok_of_hooks identityKeyPair_tryFrom_placed_ok_of_hooks
   preKeyRecord_deserialize_placed_ok_of_hooks)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget
  (identityKeyDecodePlacedSpec identityKeyPairTryFromPlacedSpec preKeyDeserializePlacedSpec)
open LibsignalBinary.Proofs.RecordCodecs.SignedAssemblyBudget
  (decodeKyberPreKey_placed_ok decodeSignedPreKey_placed_ok)
open LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget
  (SignedHooksPlaced SignedPortDepsPlaced decodeKyberPreKeyPlacedSpec decodeSignedPreKeyPlacedSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)

/-! ## 1. Budget-Threaded Record Decoders at `cliGhostExterns g (cliExternsPlaced mmpl W)` -/

theorem cliPreKeyDeserialize_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W))) :
    subroutine_ok (lsProg_65 (cliGhostExterns g (cliExternsPlaced mmpl W))) (blkPl_65).base
      (preKeyDeserializePlacedSpec A lim) :=
  preKeyRecord_deserialize_placed_ok_of_hooks hh.codecHooks

theorem cliIdentityKeyPairTryFrom_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W))) :
    subroutine_ok (lsProg_84 (cliGhostExterns g (cliExternsPlaced mmpl W))) (blkPl_84).base
      (identityKeyPairTryFromPlacedSpec A lim) :=
  identityKeyPair_tryFrom_placed_ok_of_hooks hh.codecHooks

theorem cliIdentityKeyDecode_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M)
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) :
    subroutine_ok (lsProg_18 (cliGhostExterns g (cliExternsPlaced mmpl W))) (blkPl_18).base
      (identityKeyDecodePlacedSpec A) :=
  identityKey_decode_placed_ok_of_hooks (cliGhostExterns g (cliExternsPlaced mmpl W))

theorem cliDecodeKyberPreKey_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hH : SignedHooksPlaced M A lim (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (d : SignedPortDepsPlaced M A lim (cliGhostExterns g (cliExternsPlaced mmpl W))) :
    subroutine_ok (lsProg_595 (cliGhostExterns g (cliExternsPlaced mmpl W))) (blkPl_595).base
      (decodeKyberPreKeyPlacedSpec A lim) :=
  decodeKyberPreKey_placed_ok hH d

theorem cliDecodeSignedPreKey_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hH : SignedHooksPlaced M A lim (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (d : SignedPortDepsPlaced M A lim (cliGhostExterns g (cliExternsPlaced mmpl W))) :
    subroutine_ok (lsProg_595 (cliGhostExterns g (cliExternsPlaced mmpl W))) (blkPl_595).base
      (decodeSignedPreKeyPlacedSpec A lim) :=
  decodeSignedPreKey_placed_ok hH d

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.KitCodecsPlacedBudget

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Sem
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.KemDeserializePlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `kem::Key<Public>::deserialize` Slot Adapter

Defines `CalleeSlotPlaced` and `kemDeserializeSlotPlaced` under `[LibsignalPlacement]`, and proves
that Block `590` (`kem::Key<Public>::deserialize`) satisfies `kemDeserializeSlotPlaced` on any
caller block `i < 619`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunCompose

open Arm64 ProofLib CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunProofs

/-- Relocatable `[LibsignalPlacement]` callee slot packaging a ghost type, stack-indexed `Spec`, and minimum stack `need`. -/
structure CalleeSlotPlaced where
  Ghost : Type
  spec : Nat → Spec Ghost
  need : Nat

/-- `σ`'s specification holds on `callerProg` at `entry` for every stack budget `σ.need ≤ stk ≤ 2^63`. -/
def CalleeSlotPlaced.OkAtBlock [LibsignalPlacement] (callerProg : Program)
    (entry : BitVec 64) (σ : CalleeSlotPlaced) : Prop :=
  ∀ stk, σ.need ≤ stk → stk ≤ 2 ^ 63 →
    subroutine_ok callerProg entry (σ.spec stk)

/-- Relocatable `[LibsignalPlacement]` slot for `kem::Key<Public>::deserialize` (Block `590`). -/
def kemDeserializeSlotPlaced [LibsignalPlacement] (A : RustAlloc) : CalleeSlotPlaced where
  Ghost := KemDeserializeGhost
  spec := fun stk => cliKemDeserializeSpecPlaced A stk
  need := 48 + extHookStack

/-- Block `590` (`kem::Key<Public>::deserialize`) satisfies `kemDeserializeSlotPlaced A` on any caller block `i < 619`. -/
theorem hc_kemDeserialize_placed [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {A : RustAlloc} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H]
    (hA : AllocContractsXCliPlaced A H)
    (hRO : HookSat H memcpyName SpqrV1.Alloc.sessionMemcpyRegionROSpec)
    (hpanic : H lsHandleAllocErrorSymCli = some Rust.panicked)
    (hi : i < 619 := by decide) :
    (kemDeserializeSlotPlaced A).OkAtBlock callerProg (blkPl_590).base :=
  fun stk hstk hstk63 =>
    cliKemDeserialize_placed_at_block (callerProg := callerProg) (i := i)
      hA hRO hpanic stk hstk (Nat.le_trans hstk63 (by decide)) hi

end CryptoVerification.SignalSession.Cli.RunCompose

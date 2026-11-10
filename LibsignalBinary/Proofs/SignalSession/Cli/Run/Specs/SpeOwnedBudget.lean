/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SignalSession.Cli.Pub.DropSpe.ProofBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Specs.SpeOwned

/-!
# Budget-Threaded `dropSpeOwnedSpec`

Defines the budget-threaded `dropSpeOwnedSpec` over `RustCliAllocBudget M` and `FreeOnlyEvs` (with
no `FitsEnv` precondition) and proves agreement with `DropSpe.ProofBudget.dropSpeSpecStk` on
`.proto`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Specs.SpeOwnedBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (SignalProtocolError)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.SignalSession.Cli.RunDrop (DropSpeOwnedGhost speOwnedAt)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget FreeOnlyEvs)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SignalSession.Cli.Pub.DropSpe.ProofBudget (dropSpeSpecStk)

/-- Budget-threaded `core::ptr::drop_glue::<SignalProtocolError>` specification on `SpeOwned` at
stack budget `stk` (`FreeOnlyEvs`). -/
def dropSpeOwnedSpec [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) : Spec (DropSpeOwnedGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.a ∧ LsRetAddr624 (s.readReg64 .x30)⌝ ∗
      speOwnedAt A.repAlloc x.a x.k ∗ A.pool lim st s ∗ stackAt s.sp stk
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ FreeOnlyEvs evs⌝ ∗
        memRegion x.a 48 ∗ A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp stk

theorem dropSpeOwnedSpec_proto_pre [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat) (a : BitVec 64)
    (fnName : List (BitVec 8)) (e : SignalProtocolError) (st : M.σ) :
    (dropSpeOwnedSpec A lim stk).pre (⟨a, .proto fnName e⟩, st) =
      (dropSpeSpecStk A lim stk).pre (⟨a, fnName, e⟩, st) := rfl

theorem dropSpeOwnedSpec_proto_post [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat) (a : BitVec 64)
    (fnName : List (BitVec 8)) (e : SignalProtocolError) (st : M.σ) :
    (dropSpeOwnedSpec A lim stk).post (⟨a, .proto fnName e⟩, st) =
      (dropSpeSpecStk A lim stk).post (⟨a, fnName, e⟩, st) := rfl

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Specs.SpeOwnedBudget

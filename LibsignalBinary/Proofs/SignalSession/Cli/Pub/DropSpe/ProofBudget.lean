/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SignalSession.Cli.Pub.DropSpe.Proof

/-!
# Budget-Threaded `dropSpeSpecStk`

Defines the budget-threaded stack-parameterized `dropSpeSpecStk` contract over `FreeOnlyEvs`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Pub.DropSpe.ProofBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget FreeOnlyEvs)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open CryptoVerification.LibsignalTripleRatchetRepr (speAt)
open CryptoVerification.LibsignalTripleRatchet.Getters (DropSpeGhost)

def dropSpeSpecStk [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) : Spec (DropSpeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.a ∧ LsRetAddr624 (s.readReg64 .x30)⌝ ∗
      speAt A.repAlloc x.fnName x.a x.e ∗ A.pool lim st s ∗ stackAt s.sp stk
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ FreeOnlyEvs evs⌝ ∗
        memRegion x.a 48 ∗ A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp stk

end LibsignalBinary.Proofs.SignalSession.Cli.Pub.DropSpe.ProofBudget

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Callees

/-!
# Budget-Threaded `kpkConcat2PosSpec` for `KpkMarkPoll`

Defines `kpkConcat2PosEvents`, `KpkConcat2PosEnv`, and budget-threaded `kpkConcat2PosSpec` for
`concat [local#3]` on two non-empty slices.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.CalleesBudget

open Arm64 ProofLib
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget FitsEnv rustAllocEvents)
open CryptoVerification.RustHeap (vecU8)
open CryptoVerification.SignalSession.Cli.Store.KpkMarkPoll.Helpers (Concat2PosCall)

/-- Deterministic `AllocEvent` list emitted by `concat [local#3]` on two non-empty slices. -/
def kpkConcat2PosEvents (x : Concat2PosCall) : List AllocEvent :=
  rustAllocEvents (x.bs0.length + x.bs1.length) 1

/-- Event envelope of `kpkConcat2PosSpec`. -/
def KpkConcat2PosEnv (x : Concat2PosCall) (evs : List AllocEvent) : Prop :=
  evs = kpkConcat2PosEvents x

/-- Budget-threaded `kpkConcat2PosSpec` (`onPanic = ⌜False⌝` under `FitsEnv`). -/
def kpkConcat2PosSpec {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat) : Spec (Concat2PosCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.outVec ∧ s.readReg64 .x1 = x.slicesA ∧ s.readReg64 .x2 = 2#64 ∧
      0 < x.bs0.length ∧ 0 < x.bs1.length ∧ x.bs0.length + x.bs1.length < 2 ^ 63 ∧
      FitsEnv M lim st (KpkConcat2PosEnv x)⌝ ∗
      memRegion x.outVec 24 ∗
      (x.slicesA ↦₆₄ x.p0) ∗ ((x.slicesA + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs0.length) ∗
      ((x.slicesA + 16#64) ↦₆₄ x.p1) ∗ ((x.slicesA + 24#64) ↦₆₄ BitVec.ofNat 64 x.bs1.length) ∗
      (x.p0 ↦ₛ x.bs0) ∗ (x.p1 ↦ₛ x.bs1) ∗
      A.pool lim st s ∗ stackAt s.sp stk
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ KpkConcat2PosEnv x evs⌝ ∗
        vecU8 A.repAlloc x.outVec (x.bs0 ++ x.bs1) ∗
        (x.slicesA ↦₆₄ x.p0) ∗ ((x.slicesA + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs0.length) ∗
        ((x.slicesA + 16#64) ↦₆₄ x.p1) ∗ ((x.slicesA + 24#64) ↦₆₄ BitVec.ofNat 64 x.bs1.length) ∗
        (x.p0 ↦ₛ x.bs0) ∗ (x.p1 ↦ₛ x.bs1) ∗
        A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp stk

end LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.CalleesBudget

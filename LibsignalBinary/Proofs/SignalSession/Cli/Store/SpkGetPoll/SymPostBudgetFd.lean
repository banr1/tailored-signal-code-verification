/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.SymPostBudget

/-!
# `FdsGe3Closed`-Threaded Postcondition and Panic Predicates for `SpkGetPoll`

Defines `spkPostQ_fd` and `spkPanicQp_fd` over `CalleesBudgetFd.spkGetPollInnerSpec_fd`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.SymPostBudgetFd

open Arm64 ProofLib
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open CryptoVerification.SignalSession.Cli (DirGhost ReadRule PkPollGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudgetFd
  (spkGetPollInnerSpec_fd)

def spkPostQ_fd {M : AllocCostModel} (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecEnv : BitVec 32 → List AllocEvent → Prop)
    (GetEnv : DirGhost → BitVec 32 → List AllocEvent → Prop)
    (DecodeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (calleeStk : Nat) (x : PkPollGhost) (st : M.σ) (R : SepProp) (s0 : State) :
    State → SepProp → Prop :=
  fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨
        (spkGetPollInnerSpec_fd rd pathOk A lim DecEnv GetEnv DecodeEnv calleeStk).post
          (x, st) s0 sf ∗ R)) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

def spkPanicQp_fd {M : AllocCostModel} (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecEnv : BitVec 32 → List AllocEvent → Prop)
    (GetEnv : DirGhost → BitVec 32 → List AllocEvent → Prop)
    (DecodeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (calleeStk : Nat) (x : PkPollGhost) (st : M.σ) (R : SepProp) (s0 : State) :
    State → SepProp → Prop :=
  fun sf P_f =>
    (sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨
        (spkGetPollInnerSpec_fd rd pathOk A lim DecEnv GetEnv DecodeEnv calleeStk).onPanic
          (x, st) s0 sf ∗ R)

end LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.SymPostBudgetFd

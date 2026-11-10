/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.LayoutBudget

/-!
# `FdsGe3Closed`-Threaded Cell and Inner Specifications for `PkGetPoll`

`withFdsGe3Closed`-wrapped cell and inner specifications (`*_fd`) for `get_pre_key::{closure#0}`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.LayoutBudgetFd

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.SignalSession.Cli (DirGhost PkPollGhost ReadRule)
open CryptoVerification.SignalSession.Cli.Store.PkGetPoll.Helpers
  (DeallocCellsGhost DecimalCellsGhost DirGetCellsGhost DropSpeCellsGhost PkDecCellsGhost)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.LayoutBudget
  (deallocBufCellsSpec decimalCellsSpec dirGetCellsSpec dropSpeWordCellsSpec pkDecCellsSpec
   pkGetPollInnerSpec)

def deallocBufCellsSpec_fd [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (calleeStk : Nat) : Spec (DeallocCellsGhost × M.σ) :=
  withFdsGe3Closed (deallocBufCellsSpec A lim calleeStk)

def decimalCellsSpec_fd {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecEnv : BitVec 32 → List AllocEvent → Prop)
    (calleeStk : Nat) : Spec (DecimalCellsGhost × M.σ) :=
  withFdsGe3Closed (decimalCellsSpec A lim DecEnv calleeStk)

def dirGetCellsSpec_fd {M : AllocCostModel} (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (GetEnv : DirGhost → List (BitVec 8) → List AllocEvent → Prop)
    (calleeStk : Nat) : Spec (DirGetCellsGhost × M.σ) :=
  withFdsGe3Closed (dirGetCellsSpec rd pathOk A lim GetEnv calleeStk)

def pkDecCellsSpec_fd {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PkDecEnv : List (BitVec 8) → List AllocEvent → Prop)
    (calleeStk : Nat) : Spec (PkDecCellsGhost × M.σ) :=
  withFdsGe3Closed (pkDecCellsSpec A lim PkDecEnv calleeStk)

def dropSpeWordCellsSpec_fd {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (calleeStk : Nat) : Spec (DropSpeCellsGhost × M.σ) :=
  withFdsGe3Closed (dropSpeWordCellsSpec A lim calleeStk)

def pkGetPollInnerSpec_fd {M : AllocCostModel} (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecEnv : BitVec 32 → List AllocEvent → Prop)
    (GetEnv : DirGhost → List (BitVec 8) → List AllocEvent → Prop)
    (PkDecEnv : List (BitVec 8) → List AllocEvent → Prop)
    (calleeStk : Nat) : Spec (PkPollGhost × M.σ) :=
  withFdsGe3Closed (pkGetPollInnerSpec rd pathOk A lim DecEnv GetEnv PkDecEnv calleeStk)

end LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.LayoutBudgetFd

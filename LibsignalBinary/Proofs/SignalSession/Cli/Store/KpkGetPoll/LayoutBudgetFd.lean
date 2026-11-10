/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutBudget

/-!
# `FdsGe3Closed`-Threaded Cell & Inner Specifications for `KpkGetPoll`

Wraps the five `KpkGetPoll.LayoutBudget` cell and inner `Spec` definitions with `withFdsGe3Closed`
(`withFsInv (withFdsGe3Closed spec) F0 T0` at `FsInv` call sites).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutBudgetFd

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.SignalSession.Cli (DirGhost KpkPollGhost ReadRule)
open CryptoVerification.SignalSession.Cli.Store.KpkGetPoll.Helpers
  (DeallocBufGhost DecimalCellsGhost DecodeCellsGhost DirGetCellsGhost)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutBudget
  (cliKpkGetPollInnerSpec deallocVecBufCellsSpec decimalFsCellsSpec decodeFsCellsSpec
   dirGetFsCellsSpec)

def deallocVecBufCellsSpec_fd [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F0 : FsFiles) (T0 : List TraceEvent) (calleeStk : Nat) :
    Spec (DeallocBufGhost × M.σ) :=
  withFdsGe3Closed (deallocVecBufCellsSpec A lim F0 T0 calleeStk)

def decimalFsCellsSpec_fd {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecEnv : BitVec 32 → List AllocEvent → Prop)
    (F0 : FsFiles) (T0 : List TraceEvent) (calleeStk : Nat) :
    Spec (DecimalCellsGhost × M.σ) :=
  withFdsGe3Closed (decimalFsCellsSpec A lim DecEnv F0 T0 calleeStk)

def dirGetFsCellsSpec_fd {M : AllocCostModel} (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (GetEnv : DirGhost → BitVec 32 → List AllocEvent → Prop)
    (F0 : FsFiles) (T0 : List TraceEvent) (calleeStk : Nat) :
    Spec (DirGetCellsGhost × M.σ) :=
  withFdsGe3Closed (dirGetFsCellsSpec rd pathOk A lim GetEnv F0 T0 calleeStk)

def decodeFsCellsSpec_fd {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecodeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (F0 : FsFiles) (T0 : List TraceEvent) (calleeStk : Nat) :
    Spec (DecodeCellsGhost × M.σ) :=
  withFdsGe3Closed (decodeFsCellsSpec A lim DecodeEnv F0 T0 calleeStk)

def cliKpkGetPollInnerSpec_fd {M : AllocCostModel} (rd : ReadRule)
    (pathOk : List (BitVec 8) → Prop)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecEnv : BitVec 32 → List AllocEvent → Prop)
    (GetEnv : DirGhost → BitVec 32 → List AllocEvent → Prop)
    (DecodeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (calleeStk : Nat) : Spec (KpkPollGhost × M.σ) :=
  withFdsGe3Closed (cliKpkGetPollInnerSpec rd pathOk A lim DecEnv GetEnv DecodeEnv calleeStk)

end LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutBudgetFd

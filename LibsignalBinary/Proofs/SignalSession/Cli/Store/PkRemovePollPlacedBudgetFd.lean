/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePollPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.SymPlacedBudgetFd
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# `FdsGe3Closed`-Threaded Relocatable `<OneTimePreKeyFiles as PreKeyStore>::remove_pre_key::{closure#0}`

`FdsGe3Closed` and budget-threaded `[LibsignalPlacement]` contract
`pkRemovePoll_placed_ok_of_deps_fd` on Block `575` (`lsProg_575 H`) and caller-block-polymorphic
transfer.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePollPlacedBudgetFd

open Arm64 ProofLib
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement libsignalMutatedBlocks lsmpl)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles TraceFsSound)
open CryptoVerification.SignalSession.Cli (DirGhost ReadRule)
open CryptoVerification.SignalSession.Cli.Placed (lsProg_575)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
  (ls_transfer_withFdsGe3Closed_lscro)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced decimalSpecPlaced dirGetSpecPlaced dirPutSpecPlaced
   pkRemovePollSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.LayoutPlacedBudget
  (CliPkRemovePollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.SymPlacedBudgetFd
  (pkRemovePoll_placed_ok_fd)

section Placed

/-- Block `575` (`remove_pre_key::{closure#0}`) meets two-sided
`withFdsGe3Closed (pkRemovePollSpecPlaced rd pathOk A lim (CliPkRemovePollEnv rd DecEnv GetEnv PutEnv) stk)`
given `AllocContractsFsPlaced`, `withFdsGe3Closed (decimalSpecPlaced …)` (block `597`),
`withFdsGe3Closed (dirGetSpecPlaced …)` (block `589`),
`withFdsGe3Closed (dirPutSpecPlaced …)` (block `542`), and `TraceFsSound (lsProg_575 H)`. -/
theorem pkRemovePoll_placed_ok_of_deps_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {decProg getProg putProg : Program} {decBlk getBlk putBlk : Nat}
    [IsLsBlockProg decProg decBlk H]
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg putProg putBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {decStk getStk putStk stk : Nat}
    (hFsAlloc : AllocContractsFsPlaced A lim H)
    (hDecimal : subroutine_ok decProg (lsmpl.base 597)
      (withFdsGe3Closed (decimalSpecPlaced A lim DecEnv decStk)))
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)))
    (hPut : subroutine_ok putProg (lsmpl.base 542)
      (withFdsGe3Closed (dirPutSpecPlaced A lim PutEnv putStk)))
    (hFs : TraceFsSound (lsProg_575 H))
    (hstk : 0xc0 + max (max decStk getStk) (max putStk extHookStack) ≤ stk)
    (hDecBlk : decBlk < 619 := by decide)
    (hDecUnmut : (decBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hPutBlk : putBlk < 619 := by decide)
    (hPutUnmut : (putBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (lsProg_575 H) (lsmpl.base 575)
      (withFdsGe3Closed
        (pkRemovePollSpecPlaced rd pathOk A lim
          (CliPkRemovePollEnv rd DecEnv GetEnv PutEnv) stk)) := by
  have hDecimal' := ls_transfer_withFdsGe3Closed_lscro
    (callerProg := lsProg_575 H) hDecimal (by decide) hDecBlk hDecUnmut
  have hGet' := ls_transfer_withFdsGe3Closed_lscro
    (callerProg := lsProg_575 H) hGet (by decide) hGetBlk hGetUnmut
  have hPut' := ls_transfer_withFdsGe3Closed_lscro
    (callerProg := lsProg_575 H) hPut (by decide) hPutBlk hPutUnmut
  exact pkRemovePoll_placed_ok_fd hFsAlloc hDecimal' hGet' hPut' hFs hstk

/-- Caller-block-polymorphic form of `pkRemovePoll_placed_ok_of_deps_fd`. -/
theorem pkRemovePoll_placed_caller_ok_of_deps_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {callerProg decProg getProg putProg : Program}
    {callerBlk decBlk getBlk putBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H]
    [IsLsBlockProg decProg decBlk H]
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg putProg putBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {decStk getStk putStk stk : Nat}
    (hFsAlloc : AllocContractsFsPlaced A lim H)
    (hDecimal : subroutine_ok decProg (lsmpl.base 597)
      (withFdsGe3Closed (decimalSpecPlaced A lim DecEnv decStk)))
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)))
    (hPut : subroutine_ok putProg (lsmpl.base 542)
      (withFdsGe3Closed (dirPutSpecPlaced A lim PutEnv putStk)))
    (hFs : TraceFsSound (lsProg_575 H))
    (hstk : 0xc0 + max (max decStk getStk) (max putStk extHookStack) ≤ stk)
    (hCallerBlk : callerBlk < 619 := by decide)
    (hDecBlk : decBlk < 619 := by decide)
    (hDecUnmut : (decBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hPutBlk : putBlk < 619 := by decide)
    (hPutUnmut : (putBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsmpl.base 575)
      (withFdsGe3Closed
        (pkRemovePollSpecPlaced rd pathOk A lim
          (CliPkRemovePollEnv rd DecEnv GetEnv PutEnv) stk)) :=
  ls_transfer_withFdsGe3Closed_lscro (callerProg := callerProg) (j := 575)
    (pkRemovePoll_placed_ok_of_deps_fd hFsAlloc hDecimal hGet hPut hFs hstk
      hDecBlk hDecUnmut hGetBlk hGetUnmut hPutBlk hPutUnmut) hCallerBlk

end Placed

end LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePollPlacedBudgetFd

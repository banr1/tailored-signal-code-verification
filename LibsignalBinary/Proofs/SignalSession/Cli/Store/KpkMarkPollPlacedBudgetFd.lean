/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPollPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPollPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.SymPlacedBudgetFd
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# `FdsGe3Closed`-Threaded Relocatable `<KyberPreKeyFiles as KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}`

Proves `withFdsGe3Closed (kpkMarkPollSpecPlaced …)` on Block `578` (`lsProg_578 H`) in both
generic-envelope (`KpkMarkEnvSpec`) and canonical `CliKpkMarkPollEnv` forms.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPollPlacedBudgetFd

open Arm64 Arm64.Obj ProofLib
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement libsignalMutatedBlocks lsmpl)
open CryptoVerification.LibsignalTripleRatchet (doReserveStackX)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles TraceFsSound)
open CryptoVerification.SignalSession.Cli
  (DirGhost KpkMarkPollGhost ReadRule cliBcmpName cliBcmpSpec)
open CryptoVerification.SignalSession.Cli.Placed (lsProg_578)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (CliPanicHooksPlaced)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
  (ls_transfer_withFdsGe3Closed_lscro)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced decimalSpecPlaced dirGetSpecPlaced dirPutSpecPlaced
   kpkMarkPollSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.SymPlacedBudgetAux
  (CliKpkMarkPollEnv KpkMarkEnvSpec cliKpkMarkPollEnv_spec)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.SymPlacedBudgetFd
  (kpkMarkPoll_placed_ok_fd kpkMarkPoll_placed_ok_of_envSpec_fd)

export LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.SymPlacedBudgetAux
  (CliKpkMarkPollEnv KpkMarkEnvSpec cliKpkMarkPollEnv_spec)

section Placed

theorem kpkMarkPoll_placed_ok_of_deps_gen_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {MarkEnv : FsFiles → KpkMarkPollGhost → List AllocEvent → Prop}
    {decProg getProg putProg : Program} {decBlk getBlk putBlk : Nat}
    [IsLsBlockProg decProg decBlk H]
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg putProg putBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {decStk getStk putStk stk : Nat}
    (hFsAlloc : AllocContractsFsPlaced A lim H)
    (hP : CliPanicHooksPlaced H)
    (hBcmp : HookSat H cliBcmpName (withVmPreserved cliBcmpSpec).keepsFs)
    (hDecimal : subroutine_ok decProg (lsmpl.base 597)
      (withFdsGe3Closed (decimalSpecPlaced A lim DecEnv decStk)))
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)))
    (hPut : subroutine_ok putProg (lsmpl.base 542)
      (withFdsGe3Closed (dirPutSpecPlaced A lim PutEnv putStk)))
    (hFs : TraceFsSound (lsProg_578 H))
    (hEnv : ∀ (F0 : FsFiles) (x : KpkMarkPollGhost) (st0 : M.σ),
      KpkMarkEnvSpec M lim rd DecEnv GetEnv PutEnv MarkEnv F0 x st0)
    (hstk : 0xf0 + max (max decStk getStk) (max putStk doReserveStackX) ≤ stk)
    (hDecBlk : decBlk < 619 := by decide)
    (hDecUnmut : (decBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hPutBlk : putBlk < 619 := by decide)
    (hPutUnmut : (putBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (lsProg_578 H) (lsmpl.base 578)
      (withFdsGe3Closed (kpkMarkPollSpecPlaced rd pathOk A lim MarkEnv stk)) := by
  have hDecimal' := ls_transfer_withFdsGe3Closed_lscro (callerProg := lsProg_578 H)
    hDecimal (by decide) hDecBlk hDecUnmut
  have hGet' := ls_transfer_withFdsGe3Closed_lscro (callerProg := lsProg_578 H)
    hGet (by decide) hGetBlk hGetUnmut
  have hPut' := ls_transfer_withFdsGe3Closed_lscro (callerProg := lsProg_578 H)
    hPut (by decide) hPutBlk hPutUnmut
  exact kpkMarkPoll_placed_ok_of_envSpec_fd hFsAlloc hP hBcmp hDecimal' hGet' hPut' hFs hEnv hstk

/-- Block `578` (`mark_kyber_pre_key_used::{closure#0}`) meets two-sided
`withFdsGe3Closed (kpkMarkPollSpecPlaced rd pathOk A lim (CliKpkMarkPollEnv rd DecEnv GetEnv PutEnv) stk)`
given `AllocContractsFsPlaced`, `CliPanicHooksPlaced`, `.keepsFs` `bcmp`,
`withFdsGe3Closed (decimalSpecPlaced …)` (block `597`),
`withFdsGe3Closed (dirGetSpecPlaced …)` (block `589`),
`withFdsGe3Closed (dirPutSpecPlaced …)` (block `542`), and `TraceFsSound (lsProg_578 H)`. -/
theorem kpkMarkPoll_placed_ok_of_deps_fd [LibsignalPlacement] {M : AllocCostModel}
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
    (hP : CliPanicHooksPlaced H)
    (hBcmp : HookSat H cliBcmpName (withVmPreserved cliBcmpSpec).keepsFs)
    (hDecimal : subroutine_ok decProg (lsmpl.base 597)
      (withFdsGe3Closed (decimalSpecPlaced A lim DecEnv decStk)))
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)))
    (hPut : subroutine_ok putProg (lsmpl.base 542)
      (withFdsGe3Closed (dirPutSpecPlaced A lim PutEnv putStk)))
    (hFs : TraceFsSound (lsProg_578 H))
    (hstk : 0xf0 + max (max decStk getStk) (max putStk doReserveStackX) ≤ stk)
    (hDecBlk : decBlk < 619 := by decide)
    (hDecUnmut : (decBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hPutBlk : putBlk < 619 := by decide)
    (hPutUnmut : (putBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (lsProg_578 H) (lsmpl.base 578)
      (withFdsGe3Closed
        (kpkMarkPollSpecPlaced rd pathOk A lim
          (CliKpkMarkPollEnv rd DecEnv GetEnv PutEnv) stk)) := by
  have hDecimal' := ls_transfer_withFdsGe3Closed_lscro (callerProg := lsProg_578 H)
    hDecimal (by decide) hDecBlk hDecUnmut
  have hGet' := ls_transfer_withFdsGe3Closed_lscro (callerProg := lsProg_578 H)
    hGet (by decide) hGetBlk hGetUnmut
  have hPut' := ls_transfer_withFdsGe3Closed_lscro (callerProg := lsProg_578 H)
    hPut (by decide) hPutBlk hPutUnmut
  exact kpkMarkPoll_placed_ok_fd hFsAlloc hP hBcmp hDecimal' hGet' hPut' hFs hstk

theorem kpkMarkPoll_placed_caller_ok_of_deps_gen_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {MarkEnv : FsFiles → KpkMarkPollGhost → List AllocEvent → Prop}
    {callerProg decProg getProg putProg : Program}
    {callerBlk decBlk getBlk putBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H]
    [IsLsBlockProg decProg decBlk H]
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg putProg putBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {decStk getStk putStk stk : Nat}
    (hFsAlloc : AllocContractsFsPlaced A lim H)
    (hP : CliPanicHooksPlaced H)
    (hBcmp : HookSat H cliBcmpName (withVmPreserved cliBcmpSpec).keepsFs)
    (hDecimal : subroutine_ok decProg (lsmpl.base 597)
      (withFdsGe3Closed (decimalSpecPlaced A lim DecEnv decStk)))
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)))
    (hPut : subroutine_ok putProg (lsmpl.base 542)
      (withFdsGe3Closed (dirPutSpecPlaced A lim PutEnv putStk)))
    (hFs : TraceFsSound (lsProg_578 H))
    (hEnv : ∀ (F0 : FsFiles) (x : KpkMarkPollGhost) (st0 : M.σ),
      KpkMarkEnvSpec M lim rd DecEnv GetEnv PutEnv MarkEnv F0 x st0)
    (hstk : 0xf0 + max (max decStk getStk) (max putStk doReserveStackX) ≤ stk)
    (hCallerBlk : callerBlk < 619 := by decide)
    (hDecBlk : decBlk < 619 := by decide)
    (hDecUnmut : (decBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hPutBlk : putBlk < 619 := by decide)
    (hPutUnmut : (putBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsmpl.base 578)
      (withFdsGe3Closed (kpkMarkPollSpecPlaced rd pathOk A lim MarkEnv stk)) :=
  ls_transfer_withFdsGe3Closed_lscro (callerProg := callerProg) (j := 578)
    (kpkMarkPoll_placed_ok_of_deps_gen_fd hFsAlloc hP hBcmp hDecimal hGet hPut hFs hEnv hstk
      hDecBlk hDecUnmut hGetBlk hGetUnmut hPutBlk hPutUnmut) hCallerBlk

theorem kpkMarkPoll_placed_caller_ok_of_deps_fd [LibsignalPlacement] {M : AllocCostModel}
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
    (hP : CliPanicHooksPlaced H)
    (hBcmp : HookSat H cliBcmpName (withVmPreserved cliBcmpSpec).keepsFs)
    (hDecimal : subroutine_ok decProg (lsmpl.base 597)
      (withFdsGe3Closed (decimalSpecPlaced A lim DecEnv decStk)))
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)))
    (hPut : subroutine_ok putProg (lsmpl.base 542)
      (withFdsGe3Closed (dirPutSpecPlaced A lim PutEnv putStk)))
    (hFs : TraceFsSound (lsProg_578 H))
    (hstk : 0xf0 + max (max decStk getStk) (max putStk doReserveStackX) ≤ stk)
    (hCallerBlk : callerBlk < 619 := by decide)
    (hDecBlk : decBlk < 619 := by decide)
    (hDecUnmut : (decBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hPutBlk : putBlk < 619 := by decide)
    (hPutUnmut : (putBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsmpl.base 578)
      (withFdsGe3Closed
        (kpkMarkPollSpecPlaced rd pathOk A lim
          (CliKpkMarkPollEnv rd DecEnv GetEnv PutEnv) stk)) :=
  ls_transfer_withFdsGe3Closed_lscro (callerProg := callerProg) (j := 578)
    (kpkMarkPoll_placed_ok_of_deps_fd hFsAlloc hP hBcmp hDecimal hGet hPut hFs hstk
      hDecBlk hDecUnmut hGetBlk hGetUnmut hPutBlk hPutUnmut) hCallerBlk

end Placed

end LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPollPlacedBudgetFd

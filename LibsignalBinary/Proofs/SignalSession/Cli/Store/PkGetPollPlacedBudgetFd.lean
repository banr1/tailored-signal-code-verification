/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPollPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.BlocksPlacedBudgetAuxFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.LayoutBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.SymPlacedBudgetFd
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# `FdsGe3Closed`-Threaded Relocatable `<OneTimePreKeyFiles as PreKeyStore>::get_pre_key::{closure#0}`

`FdsGe3Closed` and budget-threaded `[LibsignalPlacement]` contracts for `get_pre_key::{closure#0}`
on Block `573` (`lsProg_573 H`), with `withFsInv (withFdsGe3Closed spec) F0 T0` at `FsInv` call
sites and `withFdsGe3Closed` wrapping top-level poll and callee specs.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPollPlacedBudgetFd

open Arm64 ProofLib
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement libsignalMutatedBlocks lsmpl)
open CryptoVerification.LibsignalTripleRatchet (extHookStack smallRootStack)
open CryptoVerification.LibsignalTripleRatchet.Getters (dropSpeStackX)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles TraceFsSound)
open CryptoVerification.SignalSession.Cli (DirGhost ReadRule)
open CryptoVerification.SignalSession.Cli.Placed (lsProg_573)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget
  (PreKeyDeserializeEnv RecordCodecLoopEnv preKeyDeserializePlacedSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
  (ls_transfer_withFdsGe3Closed_lscro)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced decimalSpecPlaced dirGetSpecPlaced dropSpeWordSpecPlaced
   pkGetPollSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.LayoutBudget (CliPkGetPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.SymPlacedBudgetFd
  (pkGetPoll_placed_fs_ok_fd pkGetPoll_placed_ok_fd)

section Placed

/-- Block `573` (`get_pre_key::{closure#0}`) meets two-sided `withFdsGe3Closed` +
budget-threaded `pkGetPollSpecPlaced` on `lsProg_573 H`. -/
theorem pkGetPoll_placed_ok_of_deps_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv : DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {PkDecEnv : List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks}
    {decProg getProg pkDecProg dropProg : Program}
    {decBlk getBlk pkDecBlk dropBlk : Nat}
    [IsLsBlockProg decProg decBlk H]
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg pkDecProg pkDecBlk H]
    [IsLsBlockProg dropProg dropBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {decStk getStk stk : Nat}
    (hC : AllocContractsFsPlaced A lim H)
    (hDecimal : subroutine_ok decProg (lsmpl.base 597)
      (withFdsGe3Closed (decimalSpecPlaced A lim DecEnv decStk)))
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim (fun _ => GetEnv) getStk)))
    (hDec : subroutine_ok pkDecProg (lsmpl.base 65)
      (withFdsGe3Closed (preKeyDeserializePlacedSpec A lim)))
    (hDrop : subroutine_ok dropProg (lsmpl.base 553)
      (withFdsGe3Closed (dropSpeWordSpecPlaced A lim)))
    (hFs : TraceFsSound (lsProg_573 H))
    (hstk : 0x100 + max (max decStk getStk) (max smallRootStack (max dropSpeStackX extHookStack))
      ≤ stk)
    (hSub : ∀ bs evs, RecordCodecLoopEnv (2 * bs.length + 3) bs.length evs → PkDecEnv bs evs)
    (hSup : ∀ bs evs, PreKeyDeserializeEnv bs.length evs → PkDecEnv bs evs)
    (hDecBlk : decBlk < 619 := by decide)
    (hDecUnmut : (decBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hPkDecBlk : pkDecBlk < 619 := by decide)
    (hPkDecUnmut : (pkDecBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hDropBlk : dropBlk < 619 := by decide)
    (hDropUnmut : (dropBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (lsProg_573 H) (lsmpl.base 573)
      (withFdsGe3Closed
        (pkGetPollSpecPlaced rd pathOk A lim
          (CliPkGetPollEnv DecEnv GetEnv PkDecEnv rd) stk)) := by
  have hDecimal' : subroutine_ok (lsProg_573 H) (lsmpl.base 597)
      (withFdsGe3Closed (decimalSpecPlaced A lim DecEnv decStk)) :=
    ls_transfer_withFdsGe3Closed_lscro (callerProg := lsProg_573 H) hDecimal (by decide) hDecBlk hDecUnmut
  have hGet' : subroutine_ok (lsProg_573 H) (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim (fun _ => GetEnv) getStk)) :=
    ls_transfer_withFdsGe3Closed_lscro (callerProg := lsProg_573 H) hGet (by decide) hGetBlk hGetUnmut
  have hDec' : subroutine_ok (lsProg_573 H) (lsmpl.base 65)
      (withFdsGe3Closed (preKeyDeserializePlacedSpec A lim)) :=
    ls_transfer_withFdsGe3Closed_lscro (callerProg := lsProg_573 H) hDec (by decide) hPkDecBlk hPkDecUnmut
  have hDrop' : subroutine_ok (lsProg_573 H) (lsmpl.base 553)
      (withFdsGe3Closed (dropSpeWordSpecPlaced A lim)) :=
    ls_transfer_withFdsGe3Closed_lscro (callerProg := lsProg_573 H) hDrop (by decide) hDropBlk hDropUnmut
  exact pkGetPoll_placed_ok_fd hC hDecimal' hGet' hDec' hDrop' hFs hstk hSub hSup

/-- Caller-block-polymorphic `withFdsGe3Closed` `get_pre_key::{closure#0}` contract at
`lsmpl.base 573`. -/
theorem pkGetPoll_placed_caller_ok_of_deps_fd [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv : DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {PkDecEnv : List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    {decProg getProg pkDecProg dropProg : Program}
    {decBlk getBlk pkDecBlk dropBlk : Nat}
    [IsLsBlockProg decProg decBlk H]
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg pkDecProg pkDecBlk H]
    [IsLsBlockProg dropProg dropBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {decStk getStk stk : Nat}
    (hC : AllocContractsFsPlaced A lim H)
    (hDecimal : subroutine_ok decProg (lsmpl.base 597)
      (withFdsGe3Closed (decimalSpecPlaced A lim DecEnv decStk)))
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim (fun _ => GetEnv) getStk)))
    (hDec : subroutine_ok pkDecProg (lsmpl.base 65)
      (withFdsGe3Closed (preKeyDeserializePlacedSpec A lim)))
    (hDrop : subroutine_ok dropProg (lsmpl.base 553)
      (withFdsGe3Closed (dropSpeWordSpecPlaced A lim)))
    (hFs : TraceFsSound (lsProg_573 H))
    (hstk : 0x100 + max (max decStk getStk) (max smallRootStack (max dropSpeStackX extHookStack))
      ≤ stk)
    (hSub : ∀ bs evs, RecordCodecLoopEnv (2 * bs.length + 3) bs.length evs → PkDecEnv bs evs)
    (hSup : ∀ bs evs, PreKeyDeserializeEnv bs.length evs → PkDecEnv bs evs)
    (hi : i < 619 := by decide)
    (hDecBlk : decBlk < 619 := by decide)
    (hDecUnmut : (decBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hPkDecBlk : pkDecBlk < 619 := by decide)
    (hPkDecUnmut : (pkDecBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hDropBlk : dropBlk < 619 := by decide)
    (hDropUnmut : (dropBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsmpl.base 573)
      (withFdsGe3Closed
        (pkGetPollSpecPlaced rd pathOk A lim
          (CliPkGetPollEnv DecEnv GetEnv PkDecEnv rd) stk)) :=
  ls_transfer_withFdsGe3Closed_lscro (callerProg := callerProg) (j := 573)
    (pkGetPoll_placed_ok_of_deps_fd hC hDecimal hGet hDec hDrop hFs hstk hSub hSup
      hDecBlk hDecUnmut hGetBlk hGetUnmut hPkDecBlk hPkDecUnmut hDropBlk hDropUnmut) hi

/-- `FsFiles`-indexed `GetEnv` variant of `pkGetPoll_placed_ok_of_deps_fd` on `lsProg_573 H`. -/
theorem pkGetPoll_placed_fs_ok_of_deps_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {PkDecEnv : List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks}
    {decProg getProg pkDecProg dropProg : Program}
    {decBlk getBlk pkDecBlk dropBlk : Nat}
    [IsLsBlockProg decProg decBlk H]
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg pkDecProg pkDecBlk H]
    [IsLsBlockProg dropProg dropBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {decStk getStk stk : Nat}
    (hC : AllocContractsFsPlaced A lim H)
    (hDecimal : subroutine_ok decProg (lsmpl.base 597)
      (withFdsGe3Closed (decimalSpecPlaced A lim DecEnv decStk)))
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)))
    (hDec : subroutine_ok pkDecProg (lsmpl.base 65)
      (withFdsGe3Closed (preKeyDeserializePlacedSpec A lim)))
    (hDrop : subroutine_ok dropProg (lsmpl.base 553)
      (withFdsGe3Closed (dropSpeWordSpecPlaced A lim)))
    (hFs : TraceFsSound (lsProg_573 H))
    (hstk : 0x100 + max (max decStk getStk) (max smallRootStack (max dropSpeStackX extHookStack))
      ≤ stk)
    (hSub : ∀ bs evs, RecordCodecLoopEnv (2 * bs.length + 3) bs.length evs → PkDecEnv bs evs)
    (hSup : ∀ bs evs, PreKeyDeserializeEnv bs.length evs → PkDecEnv bs evs)
    (hDecBlk : decBlk < 619 := by decide)
    (hDecUnmut : (decBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hPkDecBlk : pkDecBlk < 619 := by decide)
    (hPkDecUnmut : (pkDecBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hDropBlk : dropBlk < 619 := by decide)
    (hDropUnmut : (dropBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (lsProg_573 H) (lsmpl.base 573)
      (withFdsGe3Closed
        (pkGetPollSpecPlaced rd pathOk A lim
          (fun F0 x => CliPkGetPollEnv DecEnv (GetEnv F0) PkDecEnv rd F0 x) stk)) := by
  have hDecimal' : subroutine_ok (lsProg_573 H) (lsmpl.base 597)
      (withFdsGe3Closed (decimalSpecPlaced A lim DecEnv decStk)) :=
    ls_transfer_withFdsGe3Closed_lscro (callerProg := lsProg_573 H) hDecimal (by decide) hDecBlk hDecUnmut
  have hGet' : subroutine_ok (lsProg_573 H) (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)) :=
    ls_transfer_withFdsGe3Closed_lscro (callerProg := lsProg_573 H) hGet (by decide) hGetBlk hGetUnmut
  have hDec' : subroutine_ok (lsProg_573 H) (lsmpl.base 65)
      (withFdsGe3Closed (preKeyDeserializePlacedSpec A lim)) :=
    ls_transfer_withFdsGe3Closed_lscro (callerProg := lsProg_573 H) hDec (by decide) hPkDecBlk hPkDecUnmut
  have hDrop' : subroutine_ok (lsProg_573 H) (lsmpl.base 553)
      (withFdsGe3Closed (dropSpeWordSpecPlaced A lim)) :=
    ls_transfer_withFdsGe3Closed_lscro (callerProg := lsProg_573 H) hDrop (by decide) hDropBlk hDropUnmut
  exact pkGetPoll_placed_fs_ok_fd hC hDecimal' hGet' hDec' hDrop' hFs hstk hSub hSup

/-- Caller-block-polymorphic `FsFiles`-indexed `GetEnv` variant of
`pkGetPoll_placed_caller_ok_of_deps_fd` at `lsmpl.base 573`. -/
theorem pkGetPoll_placed_fs_caller_ok_of_deps_fd [LibsignalPlacement] {callerProg : Program}
    {i : Nat} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {PkDecEnv : List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    {decProg getProg pkDecProg dropProg : Program}
    {decBlk getBlk pkDecBlk dropBlk : Nat}
    [IsLsBlockProg decProg decBlk H]
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg pkDecProg pkDecBlk H]
    [IsLsBlockProg dropProg dropBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {decStk getStk stk : Nat}
    (hC : AllocContractsFsPlaced A lim H)
    (hDecimal : subroutine_ok decProg (lsmpl.base 597)
      (withFdsGe3Closed (decimalSpecPlaced A lim DecEnv decStk)))
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)))
    (hDec : subroutine_ok pkDecProg (lsmpl.base 65)
      (withFdsGe3Closed (preKeyDeserializePlacedSpec A lim)))
    (hDrop : subroutine_ok dropProg (lsmpl.base 553)
      (withFdsGe3Closed (dropSpeWordSpecPlaced A lim)))
    (hFs : TraceFsSound (lsProg_573 H))
    (hstk : 0x100 + max (max decStk getStk) (max smallRootStack (max dropSpeStackX extHookStack))
      ≤ stk)
    (hSub : ∀ bs evs, RecordCodecLoopEnv (2 * bs.length + 3) bs.length evs → PkDecEnv bs evs)
    (hSup : ∀ bs evs, PreKeyDeserializeEnv bs.length evs → PkDecEnv bs evs)
    (hi : i < 619 := by decide)
    (hDecBlk : decBlk < 619 := by decide)
    (hDecUnmut : (decBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hPkDecBlk : pkDecBlk < 619 := by decide)
    (hPkDecUnmut : (pkDecBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hDropBlk : dropBlk < 619 := by decide)
    (hDropUnmut : (dropBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsmpl.base 573)
      (withFdsGe3Closed
        (pkGetPollSpecPlaced rd pathOk A lim
          (fun F0 x => CliPkGetPollEnv DecEnv (GetEnv F0) PkDecEnv rd F0 x) stk)) :=
  ls_transfer_withFdsGe3Closed_lscro (callerProg := callerProg) (j := 573)
    (pkGetPoll_placed_fs_ok_of_deps_fd hC hDecimal hGet hDec hDrop hFs hstk hSub hSup
      hDecBlk hDecUnmut hGetBlk hGetUnmut hPkDecBlk hPkDecUnmut hDropBlk hDropUnmut) hi

end Placed

end LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPollPlacedBudgetFd

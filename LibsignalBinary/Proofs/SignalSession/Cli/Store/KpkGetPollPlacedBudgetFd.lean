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
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPollPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.SymPlacedBudgetFd
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# `FdsGe3Closed`-Threaded Relocatable `<KyberPreKeyFiles as KyberPreKeyStore>::get_kyber_pre_key::{closure#0}`

Proves `withFdsGe3Closed (kpkGetPollSpecPlaced …)` on Block `576` (`lsProg_576 H`) under
`[LibsignalPlacement]`, including caller-polymorphic and `FsFiles`-indexed `GetEnv` variants.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPollPlacedBudgetFd

open Arm64 ProofLib
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement libsignalMutatedBlocks lsmpl)
open CryptoVerification.LibsignalTripleRatchet (extHookStack smallRootStack)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles TraceFsSound)
open CryptoVerification.SignalSession.Cli (DirGhost ReadRule keyName)
open CryptoVerification.SignalSession.Cli.Placed (lsProg_576)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget
  (KyberDecodeEnv SpkLoopEnv decodeKyberPreKeyPlacedSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
  (ls_transfer_withFdsGe3Closed_lscro)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced decimalSpecPlaced dirGetSpecPlaced kpkGetPollSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutBudget (CliKpkGetPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.SymPlacedBudgetFd
  (kpkGetPoll_placed_fs_ok_fd kpkGetPoll_placed_ok_fd)

section Placed

/-- Block `576` (`get_kyber_pre_key::{closure#0}`) meets two-sided `withFdsGe3Closed` +
budget-threaded `kpkGetPollSpecPlaced` on `lsProg_576 H`. -/
theorem kpkGetPoll_placed_ok_of_deps_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv : DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {DecodeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks}
    {decProg getProg decodeProg : Program}
    {decBlk getBlk decodeBlk : Nat}
    [IsLsBlockProg decProg decBlk H]
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg decodeProg decodeBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {decStk getStk stk : Nat}
    (hC : AllocContractsFsPlaced A lim H)
    (hDecimal : subroutine_ok decProg (lsmpl.base 597)
      (withFdsGe3Closed (decimalSpecPlaced A lim DecEnv decStk)))
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim (fun _ => GetEnv) getStk)))
    (hDec : subroutine_ok decodeProg (lsmpl.base 595)
      (withFdsGe3Closed (decodeKyberPreKeyPlacedSpec A lim)))
    (hFs : TraceFsSound (lsProg_576 H))
    (hstk : 0x1b0 + max (max decStk getStk) (max smallRootStack extHookStack) ≤ stk)
    (hSub : ∀ bs evs, SpkLoopEnv (2 * bs.length + 3) bs.length evs → DecodeEnv bs evs)
    (hSup : ∀ bs evs, KyberDecodeEnv bs.length evs → DecodeEnv bs evs)
    (hDecBlk : decBlk < 619 := by decide)
    (hDecUnmut : (decBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hDecodeBlk : decodeBlk < 619 := by decide)
    (hDecodeUnmut : (decodeBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (lsProg_576 H) (lsmpl.base 576)
      (withFdsGe3Closed
        (kpkGetPollSpecPlaced rd pathOk A lim
          (CliKpkGetPollEnv DecEnv (fun dir id => GetEnv dir (keyName id)) DecodeEnv rd) stk)) := by
  have hDecimal' : subroutine_ok (lsProg_576 H) (lsmpl.base 597)
      (withFdsGe3Closed (decimalSpecPlaced A lim DecEnv decStk)) :=
    ls_transfer_withFdsGe3Closed_lscro (callerProg := lsProg_576 H) hDecimal (by decide) hDecBlk hDecUnmut
  have hGet' : subroutine_ok (lsProg_576 H) (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim (fun _ => GetEnv) getStk)) :=
    ls_transfer_withFdsGe3Closed_lscro (callerProg := lsProg_576 H) hGet (by decide) hGetBlk hGetUnmut
  have hDec' : subroutine_ok (lsProg_576 H) (lsmpl.base 595)
      (withFdsGe3Closed (decodeKyberPreKeyPlacedSpec A lim)) :=
    ls_transfer_withFdsGe3Closed_lscro (callerProg := lsProg_576 H) hDec (by decide) hDecodeBlk hDecodeUnmut
  exact kpkGetPoll_placed_ok_fd hC hDecimal' hGet' hDec' hFs hstk hSub hSup

theorem kpkGetPoll_placed_caller_ok_of_deps_fd [LibsignalPlacement] {callerProg : Program}
    {i : Nat} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv : DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {DecodeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    {decProg getProg decodeProg : Program}
    {decBlk getBlk decodeBlk : Nat}
    [IsLsBlockProg decProg decBlk H]
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg decodeProg decodeBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {decStk getStk stk : Nat}
    (hC : AllocContractsFsPlaced A lim H)
    (hDecimal : subroutine_ok decProg (lsmpl.base 597)
      (withFdsGe3Closed (decimalSpecPlaced A lim DecEnv decStk)))
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim (fun _ => GetEnv) getStk)))
    (hDec : subroutine_ok decodeProg (lsmpl.base 595)
      (withFdsGe3Closed (decodeKyberPreKeyPlacedSpec A lim)))
    (hFs : TraceFsSound (lsProg_576 H))
    (hstk : 0x1b0 + max (max decStk getStk) (max smallRootStack extHookStack) ≤ stk)
    (hSub : ∀ bs evs, SpkLoopEnv (2 * bs.length + 3) bs.length evs → DecodeEnv bs evs)
    (hSup : ∀ bs evs, KyberDecodeEnv bs.length evs → DecodeEnv bs evs)
    (hi : i < 619 := by decide)
    (hDecBlk : decBlk < 619 := by decide)
    (hDecUnmut : (decBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hDecodeBlk : decodeBlk < 619 := by decide)
    (hDecodeUnmut : (decodeBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsmpl.base 576)
      (withFdsGe3Closed
        (kpkGetPollSpecPlaced rd pathOk A lim
          (CliKpkGetPollEnv DecEnv (fun dir id => GetEnv dir (keyName id)) DecodeEnv rd) stk)) :=
  ls_transfer_withFdsGe3Closed_lscro (callerProg := callerProg) (j := 576)
    (kpkGetPoll_placed_ok_of_deps_fd hC hDecimal hGet hDec hFs hstk hSub hSup
      hDecBlk hDecUnmut hGetBlk hGetUnmut hDecodeBlk hDecodeUnmut) hi

/-- `FsFiles`-indexed `GetEnv` variant of `kpkGetPoll_placed_ok_of_deps_fd` on `lsProg_576 H`. -/
theorem kpkGetPoll_placed_fs_ok_of_deps_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {DecodeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks}
    {decProg getProg decodeProg : Program}
    {decBlk getBlk decodeBlk : Nat}
    [IsLsBlockProg decProg decBlk H]
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg decodeProg decodeBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {decStk getStk stk : Nat}
    (hC : AllocContractsFsPlaced A lim H)
    (hDecimal : subroutine_ok decProg (lsmpl.base 597)
      (withFdsGe3Closed (decimalSpecPlaced A lim DecEnv decStk)))
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)))
    (hDec : subroutine_ok decodeProg (lsmpl.base 595)
      (withFdsGe3Closed (decodeKyberPreKeyPlacedSpec A lim)))
    (hFs : TraceFsSound (lsProg_576 H))
    (hstk : 0x1b0 + max (max decStk getStk) (max smallRootStack extHookStack) ≤ stk)
    (hSub : ∀ bs evs, SpkLoopEnv (2 * bs.length + 3) bs.length evs → DecodeEnv bs evs)
    (hSup : ∀ bs evs, KyberDecodeEnv bs.length evs → DecodeEnv bs evs)
    (hDecBlk : decBlk < 619 := by decide)
    (hDecUnmut : (decBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hDecodeBlk : decodeBlk < 619 := by decide)
    (hDecodeUnmut : (decodeBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (lsProg_576 H) (lsmpl.base 576)
      (withFdsGe3Closed
        (kpkGetPollSpecPlaced rd pathOk A lim
          (fun F0 x =>
            CliKpkGetPollEnv DecEnv (fun dir id => GetEnv F0 dir (keyName id)) DecodeEnv rd F0 x)
          stk)) := by
  have hDecimal' : subroutine_ok (lsProg_576 H) (lsmpl.base 597)
      (withFdsGe3Closed (decimalSpecPlaced A lim DecEnv decStk)) :=
    ls_transfer_withFdsGe3Closed_lscro (callerProg := lsProg_576 H) hDecimal (by decide) hDecBlk hDecUnmut
  have hGet' : subroutine_ok (lsProg_576 H) (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)) :=
    ls_transfer_withFdsGe3Closed_lscro (callerProg := lsProg_576 H) hGet (by decide) hGetBlk hGetUnmut
  have hDec' : subroutine_ok (lsProg_576 H) (lsmpl.base 595)
      (withFdsGe3Closed (decodeKyberPreKeyPlacedSpec A lim)) :=
    ls_transfer_withFdsGe3Closed_lscro (callerProg := lsProg_576 H) hDec (by decide) hDecodeBlk hDecodeUnmut
  exact kpkGetPoll_placed_fs_ok_fd hC hDecimal' hGet' hDec' hFs hstk hSub hSup

theorem kpkGetPoll_placed_fs_caller_ok_of_deps_fd [LibsignalPlacement] {callerProg : Program}
    {i : Nat} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {DecodeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    {decProg getProg decodeProg : Program}
    {decBlk getBlk decodeBlk : Nat}
    [IsLsBlockProg decProg decBlk H]
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg decodeProg decodeBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {decStk getStk stk : Nat}
    (hC : AllocContractsFsPlaced A lim H)
    (hDecimal : subroutine_ok decProg (lsmpl.base 597)
      (withFdsGe3Closed (decimalSpecPlaced A lim DecEnv decStk)))
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)))
    (hDec : subroutine_ok decodeProg (lsmpl.base 595)
      (withFdsGe3Closed (decodeKyberPreKeyPlacedSpec A lim)))
    (hFs : TraceFsSound (lsProg_576 H))
    (hstk : 0x1b0 + max (max decStk getStk) (max smallRootStack extHookStack) ≤ stk)
    (hSub : ∀ bs evs, SpkLoopEnv (2 * bs.length + 3) bs.length evs → DecodeEnv bs evs)
    (hSup : ∀ bs evs, KyberDecodeEnv bs.length evs → DecodeEnv bs evs)
    (hi : i < 619 := by decide)
    (hDecBlk : decBlk < 619 := by decide)
    (hDecUnmut : (decBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hDecodeBlk : decodeBlk < 619 := by decide)
    (hDecodeUnmut : (decodeBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsmpl.base 576)
      (withFdsGe3Closed
        (kpkGetPollSpecPlaced rd pathOk A lim
          (fun F0 x =>
            CliKpkGetPollEnv DecEnv (fun dir id => GetEnv F0 dir (keyName id)) DecodeEnv rd F0 x)
          stk)) :=
  ls_transfer_withFdsGe3Closed_lscro (callerProg := callerProg) (j := 576)
    (kpkGetPoll_placed_fs_ok_of_deps_fd hC hDecimal hGet hDec hFs hstk hSub hSup
      hDecBlk hDecUnmut hGetBlk hGetUnmut hDecodeBlk hDecodeUnmut) hi

end Placed

end LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPollPlacedBudgetFd

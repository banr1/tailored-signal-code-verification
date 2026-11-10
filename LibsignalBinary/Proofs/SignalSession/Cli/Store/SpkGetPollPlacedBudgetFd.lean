/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPollPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.SymPlacedBudgetFd
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# `FdsGe3Closed`-Threaded Relocatable `<SignedPreKeyFiles as SignedPreKeyStore>::get_signed_pre_key::{closure#0}`

`FdsGe3Closed` and budget-threaded `[LibsignalPlacement]` contracts for
`get_signed_pre_key::{closure#0}` on Block `571` (`lsProg_571 H`), plus caller-block-polymorphic
transfers.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPollPlacedBudgetFd

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement libsignalMutatedBlocks lsmpl)
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit CryptoVerification.RecordCodecsBinary
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget
  (KyberDecodeEnv SpkLoopEnv decodeSignedPreKeyPlacedSpec decodeSignedPreKeyRawSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
  (ls_transfer_withFdsGe3Closed_lscro)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced decimalSpecPlaced dirGetSpecPlaced dropSpeWordSpecPlaced
   spkGetPollSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget
  (CliSpkGetPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesPlacedBudgetFd
  (spkGetPoll_placed_of_inner_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.SymPlacedBudgetFd
  (spkGetPollInner_placed_ok_fd spkGetPoll_placed_fs_ok_fd)

section Placed

/-- Block `571` (`get_signed_pre_key::{closure#0}`) meets
`withFdsGe3Closed (spkGetPollSpecPlaced rd pathOk A lim (CliSpkGetPollEnv DecEnv (fun dir id => GetEnv dir (keyName id)) DecodeEnv rd) stk)`
on `lsProg_571 H`. -/
theorem spkGetPoll_placed_ok_of_deps_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv : DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {DecodeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks}
    {decProg getProg spkDecProg dropProg : Program}
    {decBlk getBlk spkDecBlk dropBlk : Nat}
    [IsLsBlockProg decProg decBlk H]
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg spkDecProg spkDecBlk H]
    [IsLsBlockProg dropProg dropBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {decStk getStk stk : Nat}
    (hC : AllocContractsFsPlaced A lim H)
    (hDecimal : subroutine_ok decProg (lsmpl.base 597)
      (withFdsGe3Closed (decimalSpecPlaced A lim DecEnv decStk)))
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim (fun _ => GetEnv) getStk)))
    (hDec : subroutine_ok spkDecProg (lsmpl.base 595)
      (withFdsGe3Closed (decodeSignedPreKeyPlacedSpec A lim)))
    (hDrop : subroutine_ok dropProg (lsmpl.base 553)
      (withFdsGe3Closed (dropSpeWordSpecPlaced A lim)))
    (hFs : TraceFsSound (lsProg_571 H))
    (hstk : 0x180 + max (max decStk getStk) (max smallRootStack (max dropSpeStackX extHookStack))
      ≤ stk)
    (hSub : ∀ bs evs, SpkLoopEnv (2 * bs.length + 3) bs.length evs → DecodeEnv bs evs)
    (hSup : ∀ bs evs, KyberDecodeEnv bs.length evs → DecodeEnv bs evs)
    (hDecBlk : decBlk < 619 := by decide)
    (hDecUnmut : (decBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hSpkDecBlk : spkDecBlk < 619 := by decide)
    (hSpkDecUnmut : (spkDecBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hDropBlk : dropBlk < 619 := by decide)
    (hDropUnmut : (dropBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (lsProg_571 H) (lsmpl.base 571)
      (withFdsGe3Closed
        (spkGetPollSpecPlaced rd pathOk A lim
          (CliSpkGetPollEnv DecEnv (fun dir id => GetEnv dir (keyName id)) DecodeEnv rd) stk)) := by
  have hDecimal' : subroutine_ok (lsProg_571 H) (lsmpl.base 597)
      (withFdsGe3Closed (decimalSpecPlaced A lim DecEnv decStk)) :=
    ls_transfer_withFdsGe3Closed_lscro (callerProg := lsProg_571 H) hDecimal
      (by decide) hDecBlk hDecUnmut
  have hGet' : subroutine_ok (lsProg_571 H) (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim (fun _ => GetEnv) getStk)) :=
    ls_transfer_withFdsGe3Closed_lscro (callerProg := lsProg_571 H) hGet
      (by decide) hGetBlk hGetUnmut
  have hDec' : subroutine_ok (lsProg_571 H) (lsmpl.base 595)
      (withFdsGe3Closed (decodeSignedPreKeyPlacedSpec A lim)) :=
    ls_transfer_withFdsGe3Closed_lscro (callerProg := lsProg_571 H)
      (spec := decodeSignedPreKeyRawSpec A lim) hDec
      (by decide) hSpkDecBlk hSpkDecUnmut
  have hDrop' : subroutine_ok (lsProg_571 H) (lsmpl.base 553)
      (withFdsGe3Closed (dropSpeWordSpecPlaced A lim)) :=
    ls_transfer_withFdsGe3Closed_lscro (callerProg := lsProg_571 H) hDrop
      (by decide) hDropBlk hDropUnmut
  exact spkGetPoll_placed_of_inner_fd
    (calleeStk := max (max decStk getStk) (max smallRootStack (max dropSpeStackX extHookStack)))
    (fun hhi => spkGetPollInner_placed_ok_fd hC hDecimal' hGet' hDec' hDrop' hFs hhi hSub hSup)
    hstk

/-- Caller-block-polymorphic `FdsGe3Closed` `get_signed_pre_key::{closure#0}` contract at
`lsmpl.base 571`. -/
theorem spkGetPoll_placed_caller_ok_of_deps_fd [LibsignalPlacement] {callerProg : Program}
    {i : Nat} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv : DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {DecodeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    {decProg getProg spkDecProg dropProg : Program}
    {decBlk getBlk spkDecBlk dropBlk : Nat}
    [IsLsBlockProg decProg decBlk H]
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg spkDecProg spkDecBlk H]
    [IsLsBlockProg dropProg dropBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {decStk getStk stk : Nat}
    (hC : AllocContractsFsPlaced A lim H)
    (hDecimal : subroutine_ok decProg (lsmpl.base 597)
      (withFdsGe3Closed (decimalSpecPlaced A lim DecEnv decStk)))
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim (fun _ => GetEnv) getStk)))
    (hDec : subroutine_ok spkDecProg (lsmpl.base 595)
      (withFdsGe3Closed (decodeSignedPreKeyPlacedSpec A lim)))
    (hDrop : subroutine_ok dropProg (lsmpl.base 553)
      (withFdsGe3Closed (dropSpeWordSpecPlaced A lim)))
    (hFs : TraceFsSound (lsProg_571 H))
    (hstk : 0x180 + max (max decStk getStk) (max smallRootStack (max dropSpeStackX extHookStack))
      ≤ stk)
    (hSub : ∀ bs evs, SpkLoopEnv (2 * bs.length + 3) bs.length evs → DecodeEnv bs evs)
    (hSup : ∀ bs evs, KyberDecodeEnv bs.length evs → DecodeEnv bs evs)
    (hi : i < 619 := by decide)
    (hDecBlk : decBlk < 619 := by decide)
    (hDecUnmut : (decBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hSpkDecBlk : spkDecBlk < 619 := by decide)
    (hSpkDecUnmut : (spkDecBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hDropBlk : dropBlk < 619 := by decide)
    (hDropUnmut : (dropBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsmpl.base 571)
      (withFdsGe3Closed
        (spkGetPollSpecPlaced rd pathOk A lim
          (CliSpkGetPollEnv DecEnv (fun dir id => GetEnv dir (keyName id)) DecodeEnv rd) stk)) :=
  ls_transfer_withFdsGe3Closed_lscro (callerProg := callerProg) (j := 571)
    (spkGetPoll_placed_ok_of_deps_fd hC hDecimal hGet hDec hDrop hFs hstk hSub hSup
      hDecBlk hDecUnmut hGetBlk hGetUnmut hSpkDecBlk hSpkDecUnmut hDropBlk hDropUnmut) hi

/-- `FsFiles`-indexed `GetEnv` variant of `spkGetPoll_placed_ok_of_deps_fd` on `lsProg_571 H`. -/
theorem spkGetPoll_placed_fs_ok_of_deps_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {DecodeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks}
    {decProg getProg spkDecProg dropProg : Program}
    {decBlk getBlk spkDecBlk dropBlk : Nat}
    [IsLsBlockProg decProg decBlk H]
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg spkDecProg spkDecBlk H]
    [IsLsBlockProg dropProg dropBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {decStk getStk stk : Nat}
    (hC : AllocContractsFsPlaced A lim H)
    (hDecimal : subroutine_ok decProg (lsmpl.base 597)
      (withFdsGe3Closed (decimalSpecPlaced A lim DecEnv decStk)))
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)))
    (hDec : subroutine_ok spkDecProg (lsmpl.base 595)
      (withFdsGe3Closed (decodeSignedPreKeyPlacedSpec A lim)))
    (hDrop : subroutine_ok dropProg (lsmpl.base 553)
      (withFdsGe3Closed (dropSpeWordSpecPlaced A lim)))
    (hFs : TraceFsSound (lsProg_571 H))
    (hstk : 0x180 + max (max decStk getStk) (max smallRootStack (max dropSpeStackX extHookStack))
      ≤ stk)
    (hSub : ∀ bs evs, SpkLoopEnv (2 * bs.length + 3) bs.length evs → DecodeEnv bs evs)
    (hSup : ∀ bs evs, KyberDecodeEnv bs.length evs → DecodeEnv bs evs)
    (hDecBlk : decBlk < 619 := by decide)
    (hDecUnmut : (decBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hSpkDecBlk : spkDecBlk < 619 := by decide)
    (hSpkDecUnmut : (spkDecBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hDropBlk : dropBlk < 619 := by decide)
    (hDropUnmut : (dropBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (lsProg_571 H) (lsmpl.base 571)
      (withFdsGe3Closed
        (spkGetPollSpecPlaced rd pathOk A lim
          (fun F0 x =>
            CliSpkGetPollEnv DecEnv (fun dir id => GetEnv F0 dir (keyName id)) DecodeEnv rd F0 x)
          stk)) := by
  have hDecimal' : subroutine_ok (lsProg_571 H) (lsmpl.base 597)
      (withFdsGe3Closed (decimalSpecPlaced A lim DecEnv decStk)) :=
    ls_transfer_withFdsGe3Closed_lscro (callerProg := lsProg_571 H) hDecimal
      (by decide) hDecBlk hDecUnmut
  have hGet' : subroutine_ok (lsProg_571 H) (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)) :=
    ls_transfer_withFdsGe3Closed_lscro (callerProg := lsProg_571 H) hGet
      (by decide) hGetBlk hGetUnmut
  have hDec' : subroutine_ok (lsProg_571 H) (lsmpl.base 595)
      (withFdsGe3Closed (decodeSignedPreKeyPlacedSpec A lim)) :=
    ls_transfer_withFdsGe3Closed_lscro (callerProg := lsProg_571 H)
      (spec := decodeSignedPreKeyRawSpec A lim) hDec
      (by decide) hSpkDecBlk hSpkDecUnmut
  have hDrop' : subroutine_ok (lsProg_571 H) (lsmpl.base 553)
      (withFdsGe3Closed (dropSpeWordSpecPlaced A lim)) :=
    ls_transfer_withFdsGe3Closed_lscro (callerProg := lsProg_571 H) hDrop
      (by decide) hDropBlk hDropUnmut
  exact spkGetPoll_placed_fs_ok_fd hC hDecimal' hGet' hDec' hDrop' hFs hstk hSub hSup

/-- Caller-block-polymorphic `FsFiles`-indexed `GetEnv` variant of
`spkGetPoll_placed_caller_ok_of_deps_fd` at `lsmpl.base 571`. -/
theorem spkGetPoll_placed_fs_caller_ok_of_deps_fd [LibsignalPlacement] {callerProg : Program}
    {i : Nat} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {DecodeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    {decProg getProg spkDecProg dropProg : Program}
    {decBlk getBlk spkDecBlk dropBlk : Nat}
    [IsLsBlockProg decProg decBlk H]
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg spkDecProg spkDecBlk H]
    [IsLsBlockProg dropProg dropBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {decStk getStk stk : Nat}
    (hC : AllocContractsFsPlaced A lim H)
    (hDecimal : subroutine_ok decProg (lsmpl.base 597)
      (withFdsGe3Closed (decimalSpecPlaced A lim DecEnv decStk)))
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)))
    (hDec : subroutine_ok spkDecProg (lsmpl.base 595)
      (withFdsGe3Closed (decodeSignedPreKeyPlacedSpec A lim)))
    (hDrop : subroutine_ok dropProg (lsmpl.base 553)
      (withFdsGe3Closed (dropSpeWordSpecPlaced A lim)))
    (hFs : TraceFsSound (lsProg_571 H))
    (hstk : 0x180 + max (max decStk getStk) (max smallRootStack (max dropSpeStackX extHookStack))
      ≤ stk)
    (hSub : ∀ bs evs, SpkLoopEnv (2 * bs.length + 3) bs.length evs → DecodeEnv bs evs)
    (hSup : ∀ bs evs, KyberDecodeEnv bs.length evs → DecodeEnv bs evs)
    (hi : i < 619 := by decide)
    (hDecBlk : decBlk < 619 := by decide)
    (hDecUnmut : (decBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hSpkDecBlk : spkDecBlk < 619 := by decide)
    (hSpkDecUnmut : (spkDecBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hDropBlk : dropBlk < 619 := by decide)
    (hDropUnmut : (dropBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsmpl.base 571)
      (withFdsGe3Closed
        (spkGetPollSpecPlaced rd pathOk A lim
          (fun F0 x =>
            CliSpkGetPollEnv DecEnv (fun dir id => GetEnv F0 dir (keyName id)) DecodeEnv rd F0 x)
          stk)) :=
  ls_transfer_withFdsGe3Closed_lscro (callerProg := callerProg) (j := 571)
    (spkGetPoll_placed_fs_ok_of_deps_fd hC hDecimal hGet hDec hDrop hFs hstk hSub hSup
      hDecBlk hDecUnmut hGetBlk hGetUnmut hSpkDecBlk hSpkDecUnmut hDropBlk hDropUnmut) hi

end Placed

end LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPollPlacedBudgetFd

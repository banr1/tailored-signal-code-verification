/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll.SymPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# `FdsGe3Closed`-Threaded Relocatable `<SessionFiles as SessionStore>::load_session::{closure#0}`

Proves `withFdsGe3Closed (sessLoadPollSpecPlaced …)` on Block `569` (`lsProg_569 H`) under
`[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollPlacedBudgetFd

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement libsignalMutatedBlocks lsmpl)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles TraceFsSound)
open CryptoVerification.E2E.Record (recDeserializeStack)
open CryptoVerification.SignalSession.Cli (DirGhost ReadRule)
open CryptoVerification.SignalSession.Cli.Placed (lsProg_569)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
  (ls_transfer_withFdsGe3Closed_lscro)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced addrTextSpecPlaced dirGetSpecPlaced sessDeserializeSpecPlaced
   sessLoadPollSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll.LayoutPlacedBudget
  (CliLoadPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll.SymPlacedBudgetFd
  (sessLoadPoll_placed_ok_fd)

section Placed

/-- Block `569` (`load_session::{closure#0}`) meets `withFdsGe3Closed (sessLoadPollSpecPlaced …)`
given `AllocContractsFsPlaced`, `withFdsGe3Closed` on `address_text` (block `594`), `Dir::get`
(block `589`), and `SessionRecord::deserialize` (block `46`), plus `TraceFsSound (lsProg_569 H)`. -/
theorem sessLoadPoll_placed_ok_of_deps_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {AddrEnv : AddrGhost → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {addrProg getProg deserProg : Program} {addrBlk getBlk deserBlk : Nat}
    [IsLsBlockProg addrProg addrBlk H]
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg deserProg deserBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {addrStk getStk stk : Nat}
    (hC : AllocContractsFsPlaced A lim H)
    (hAddr : subroutine_ok addrProg (lsmpl.base 594)
      (withFdsGe3Closed (addrTextSpecPlaced A lim AddrEnv addrStk)))
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)))
    (hDeser : subroutine_ok deserProg (lsmpl.base 46)
      (withFdsGe3Closed (sessDeserializeSpecPlaced Scope A lim DeserEnv)))
    (hFs : TraceFsSound (lsProg_569 H))
    (hstk : 0x350 + max (max addrStk getStk) (max recDeserializeStack extHookStack) ≤ stk)
    (hAddrBlk : addrBlk < 619 := by decide)
    (hAddrUnmut : (addrBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hDeserBlk : deserBlk < 619 := by decide)
    (hDeserUnmut : (deserBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (lsProg_569 H) (lsmpl.base 569)
      (withFdsGe3Closed
        (sessLoadPollSpecPlaced rd pathOk Scope A lim
          (CliLoadPollEnv rd Scope AddrEnv GetEnv DeserEnv) stk)) := by
  have hAddr' :=
    ls_transfer_withFdsGe3Closed_lscro
      (callerProg := lsProg_569 H) hAddr (by decide) hAddrBlk hAddrUnmut
  have hGet' :=
    ls_transfer_withFdsGe3Closed_lscro
      (callerProg := lsProg_569 H) hGet (by decide) hGetBlk hGetUnmut
  have hDeser' :=
    ls_transfer_withFdsGe3Closed_lscro
      (callerProg := lsProg_569 H) hDeser (by decide) hDeserBlk hDeserUnmut
  exact sessLoadPoll_placed_ok_fd hC hAddr' hGet' hDeser' hFs hstk

theorem sessLoadPoll_placed_caller_ok_of_deps_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {AddrEnv : AddrGhost → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {callerProg addrProg getProg deserProg : Program}
    {callerBlk addrBlk getBlk deserBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H]
    [IsLsBlockProg addrProg addrBlk H]
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg deserProg deserBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {addrStk getStk stk : Nat}
    (hC : AllocContractsFsPlaced A lim H)
    (hAddr : subroutine_ok addrProg (lsmpl.base 594)
      (withFdsGe3Closed (addrTextSpecPlaced A lim AddrEnv addrStk)))
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)))
    (hDeser : subroutine_ok deserProg (lsmpl.base 46)
      (withFdsGe3Closed (sessDeserializeSpecPlaced Scope A lim DeserEnv)))
    (hFs : TraceFsSound (lsProg_569 H))
    (hstk : 0x350 + max (max addrStk getStk) (max recDeserializeStack extHookStack) ≤ stk)
    (hCallerBlk : callerBlk < 619 := by decide)
    (hAddrBlk : addrBlk < 619 := by decide)
    (hAddrUnmut : (addrBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hDeserBlk : deserBlk < 619 := by decide)
    (hDeserUnmut : (deserBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsmpl.base 569)
      (withFdsGe3Closed
        (sessLoadPollSpecPlaced rd pathOk Scope A lim
          (CliLoadPollEnv rd Scope AddrEnv GetEnv DeserEnv) stk)) :=
  ls_transfer_withFdsGe3Closed_lscro (callerProg := callerProg) (j := 569)
    (sessLoadPoll_placed_ok_of_deps_fd hC hAddr hGet hDeser hFs hstk
      hAddrBlk hAddrUnmut hGetBlk hGetUnmut hDeserBlk hDeserUnmut) hCallerBlk

end Placed

end LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollPlacedBudgetFd

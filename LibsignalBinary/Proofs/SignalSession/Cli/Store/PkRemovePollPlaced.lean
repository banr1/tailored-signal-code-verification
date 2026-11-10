/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.SymPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `<OneTimePreKeyFiles as PreKeyStore>::remove_pre_key::{closure#0}`

Top-level `[LibsignalPlacement]` contract `pkRemovePoll_placed_ok_of_deps` on Block `575`
(`lsProg_575 H`) and caller-block-polymorphic transfer.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Store.PkRemovePoll

open Arm64 Arm64.Obj ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon

section Placed

/-- Block `575` (`remove_pre_key::{closure#0}`) meets `pkRemovePollSpecPlaced rd pathOk A stk`
given `AllocContractsXCliPlaced`, `decimal` (block `597`), `Dir::get` (block `589`),
`Dir::put::<String>` (block `542`), and `TraceFsSound (lsProg_575 H)`. -/
theorem pkRemovePoll_placed_ok_of_deps [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {decProg getProg putProg : Program} {decBlk getBlk putBlk : Nat}
    [IsLsBlockProg decProg decBlk H]
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg putProg putBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {decStk getStk putStk stk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hDecimal : subroutine_ok decProg (lsmpl.base 597) (decimalSpecPlaced A decStk))
    (hGet : subroutine_ok getProg (lsmpl.base 589) (dirGetSpecPlaced rd pathOk A getStk))
    (hPut : subroutine_ok putProg (lsmpl.base 542) (dirPutSpecPlaced A putStk))
    (hFs : TraceFsSound (lsProg_575 H))
    (hstk : 0xc0 + max (max decStk getStk) (max putStk extHookStack) ≤ stk)
    (hDecBlk : decBlk < 619 := by decide)
    (hDecUnmut : (decBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hPutBlk : putBlk < 619 := by decide)
    (hPutUnmut : (putBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (lsProg_575 H) (lsmpl.base 575)
      (pkRemovePollSpecPlaced rd pathOk A stk) := by
  have hDecimal' := ls_transfer_lscro (callerProg := lsProg_575 H) hDecimal (by decide) hDecBlk hDecUnmut
  have hGet' := ls_transfer_lscro (callerProg := lsProg_575 H) hGet (by decide) hGetBlk hGetUnmut
  have hPut' := ls_transfer_lscro (callerProg := lsProg_575 H) hPut (by decide) hPutBlk hPutUnmut
  exact Helpers.pkRemovePoll_placed_ok hC hDecimal' hGet' hPut' hFs hstk

/-- Caller-block-polymorphic form of `pkRemovePoll_placed_ok_of_deps`. -/
theorem pkRemovePoll_placed_caller_ok_of_deps [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {callerProg decProg getProg putProg : Program}
    {callerBlk decBlk getBlk putBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H]
    [IsLsBlockProg decProg decBlk H]
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg putProg putBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {decStk getStk putStk stk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hDecimal : subroutine_ok decProg (lsmpl.base 597) (decimalSpecPlaced A decStk))
    (hGet : subroutine_ok getProg (lsmpl.base 589) (dirGetSpecPlaced rd pathOk A getStk))
    (hPut : subroutine_ok putProg (lsmpl.base 542) (dirPutSpecPlaced A putStk))
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
      (pkRemovePollSpecPlaced rd pathOk A stk) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 575)
    (pkRemovePoll_placed_ok_of_deps hC hDecimal hGet hPut hFs hstk
      hDecBlk hDecUnmut hGetBlk hGetUnmut hPutBlk hPutUnmut) hCallerBlk

end Placed

end CryptoVerification.SignalSession.Cli.Store.PkRemovePoll

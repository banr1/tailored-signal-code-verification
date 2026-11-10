/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll.SymPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `<SessionFiles as SessionStore>::load_session::{closure#0}`

Proves `sessLoadPollSpecPlaced` on Block `569` (`lsProg_569 H`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Store.LoadPoll

open Arm64 Arm64.Obj ProofLib CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon

section Placed

/-- Block `569` (`load_session::{closure#0}`) meets `sessLoadPollSpecPlaced rd pathOk Scope A stk`
given `AllocContractsXCliPlaced`, `address_text` (block `594`), `Dir::get` (block `589`),
`SessionRecord::deserialize` (block `46`), and `TraceFsSound (lsProg_569 H)`. -/
theorem sessLoadPoll_placed_ok_of_deps [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {addrProg getProg deserProg : Program} {addrBlk getBlk deserBlk : Nat}
    [IsLsBlockProg addrProg addrBlk H]
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg deserProg deserBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {addrStk getStk stk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hAddr : subroutine_ok addrProg (lsmpl.base 594) (addrTextSpecPlaced A addrStk))
    (hGet : subroutine_ok getProg (lsmpl.base 589) (dirGetSpecPlaced rd pathOk A getStk))
    (hDeser : subroutine_ok deserProg (lsmpl.base 46) (sessDeserializeSpecPlaced Scope A))
    (hFs : TraceFsSound (lsProg_569 H))
    (hstk : 0x350 + max (max addrStk getStk) (max E2E.Record.recDeserializeStack extHookStack) ≤
      stk)
    (hAddrBlk : addrBlk < 619 := by decide)
    (hAddrUnmut : (addrBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hDeserBlk : deserBlk < 619 := by decide)
    (hDeserUnmut : (deserBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (lsProg_569 H) (lsmpl.base 569)
      (sessLoadPollSpecPlaced rd pathOk Scope A stk) := by
  have hAddr' := ls_transfer_lscro (callerProg := lsProg_569 H) hAddr (by decide) hAddrBlk hAddrUnmut
  have hGet' := ls_transfer_lscro (callerProg := lsProg_569 H) hGet (by decide) hGetBlk hGetUnmut
  have hDeser' := ls_transfer_lscro (callerProg := lsProg_569 H) hDeser (by decide) hDeserBlk hDeserUnmut
  exact Helpers.sessLoadPoll_placed_ok hC hAddr' hGet' hDeser' hFs hstk

theorem sessLoadPoll_placed_caller_ok_of_deps [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {callerProg addrProg getProg deserProg : Program}
    {callerBlk addrBlk getBlk deserBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H]
    [IsLsBlockProg addrProg addrBlk H]
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg deserProg deserBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {addrStk getStk stk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hAddr : subroutine_ok addrProg (lsmpl.base 594) (addrTextSpecPlaced A addrStk))
    (hGet : subroutine_ok getProg (lsmpl.base 589) (dirGetSpecPlaced rd pathOk A getStk))
    (hDeser : subroutine_ok deserProg (lsmpl.base 46) (sessDeserializeSpecPlaced Scope A))
    (hFs : TraceFsSound (lsProg_569 H))
    (hstk : 0x350 + max (max addrStk getStk) (max E2E.Record.recDeserializeStack extHookStack) ≤
      stk)
    (hCallerBlk : callerBlk < 619 := by decide)
    (hAddrBlk : addrBlk < 619 := by decide)
    (hAddrUnmut : (addrBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hDeserBlk : deserBlk < 619 := by decide)
    (hDeserUnmut : (deserBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsmpl.base 569)
      (sessLoadPollSpecPlaced rd pathOk Scope A stk) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 569)
    (sessLoadPoll_placed_ok_of_deps hC hAddr hGet hDeser hFs hstk
      hAddrBlk hAddrUnmut hGetBlk hGetUnmut hDeserBlk hDeserUnmut) hCallerBlk

end Placed

end CryptoVerification.SignalSession.Cli.Store.LoadPoll

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.SymPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `<SignedPreKeyFiles as SignedPreKeyStore>::get_signed_pre_key::{closure#0}`

Top-level `[LibsignalPlacement]` contract `spkGetPoll_placed_ok_of_deps` on Block `571`
(`lsProg_571 H`) and caller-block-polymorphic transfer `spkGetPoll_placed_caller_ok_of_deps`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Store.SpkGetPoll

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit CryptoVerification.RecordCodecsBinary
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon

section Placed

/-- Block `571` (`get_signed_pre_key::{closure#0}`) meets `spkGetPollSpecPlaced rd pathOk A stk`
on `lsProg_571 H`. -/
theorem spkGetPoll_placed_ok_of_deps [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {decProg getProg spkDecProg dropProg : Program}
    {decBlk getBlk spkDecBlk dropBlk : Nat}
    [IsLsBlockProg decProg decBlk H]
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg spkDecProg spkDecBlk H]
    [IsLsBlockProg dropProg dropBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {decStk getStk stk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hDecimal : subroutine_ok decProg (lsmpl.base 597) (decimalSpecPlaced A decStk))
    (hGet : subroutine_ok getProg (lsmpl.base 589) (dirGetSpecPlaced rd pathOk A getStk))
    (hDec : subroutine_ok spkDecProg (lsmpl.base 595) (decodeSignedPreKeyPlacedSpec A))
    (hDrop : subroutine_ok dropProg (lsmpl.base 553) (dropSpeWordSpecPlaced A))
    (hFs : TraceFsSound (lsProg_571 H))
    (hstk : 0x180 + max (max decStk getStk) (max smallRootStack (max dropSpeStackX extHookStack))
      ≤ stk)
    (hDecBlk : decBlk < 619 := by decide)
    (hDecUnmut : (decBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hSpkDecBlk : spkDecBlk < 619 := by decide)
    (hSpkDecUnmut : (spkDecBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hDropBlk : dropBlk < 619 := by decide)
    (hDropUnmut : (dropBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (lsProg_571 H) (lsmpl.base 571) (spkGetPollSpecPlaced rd pathOk A stk) := by
  have hDecimal' : subroutine_ok (lsProg_571 H) (lsmpl.base 597) (decimalSpecPlaced A decStk) :=
    ls_transfer_lscro (callerProg := lsProg_571 H) hDecimal (by decide) hDecBlk hDecUnmut
  have hGet' : subroutine_ok (lsProg_571 H) (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A getStk) :=
    ls_transfer_lscro (callerProg := lsProg_571 H) hGet (by decide) hGetBlk hGetUnmut
  have hDec' : subroutine_ok (lsProg_571 H) (lsmpl.base 595) (decodeSignedPreKeyPlacedSpec A) :=
    ls_transfer_lscro (callerProg := lsProg_571 H) hDec (by decide) hSpkDecBlk hSpkDecUnmut
  have hDrop' : subroutine_ok (lsProg_571 H) (lsmpl.base 553) (dropSpeWordSpecPlaced A) :=
    ls_transfer_lscro (callerProg := lsProg_571 H) hDrop (by decide) hDropBlk hDropUnmut
  exact Helpers.spkGetPoll_placed_of_inner
    (calleeStk := max (max decStk getStk) (max smallRootStack (max dropSpeStackX extHookStack)))
    (fun hhi => Helpers.spkGetPollInner_placed_ok hC hDecimal' hGet' hDec' hDrop' hFs hhi)
    hstk

/-- Caller-block-polymorphic `get_signed_pre_key::{closure#0}` contract at `lsmpl.base 571`. -/
theorem spkGetPoll_placed_caller_ok_of_deps [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {A : RustAlloc} {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    {decProg getProg spkDecProg dropProg : Program}
    {decBlk getBlk spkDecBlk dropBlk : Nat}
    [IsLsBlockProg decProg decBlk H]
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg spkDecProg spkDecBlk H]
    [IsLsBlockProg dropProg dropBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {decStk getStk stk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hDecimal : subroutine_ok decProg (lsmpl.base 597) (decimalSpecPlaced A decStk))
    (hGet : subroutine_ok getProg (lsmpl.base 589) (dirGetSpecPlaced rd pathOk A getStk))
    (hDec : subroutine_ok spkDecProg (lsmpl.base 595) (decodeSignedPreKeyPlacedSpec A))
    (hDrop : subroutine_ok dropProg (lsmpl.base 553) (dropSpeWordSpecPlaced A))
    (hFs : TraceFsSound (lsProg_571 H))
    (hstk : 0x180 + max (max decStk getStk) (max smallRootStack (max dropSpeStackX extHookStack))
      ≤ stk)
    (hi : i < 619 := by decide)
    (hDecBlk : decBlk < 619 := by decide)
    (hDecUnmut : (decBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hSpkDecBlk : spkDecBlk < 619 := by decide)
    (hSpkDecUnmut : (spkDecBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hDropBlk : dropBlk < 619 := by decide)
    (hDropUnmut : (dropBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsmpl.base 571) (spkGetPollSpecPlaced rd pathOk A stk) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 571)
    (spkGetPoll_placed_ok_of_deps hC hDecimal hGet hDec hDrop hFs hstk
      hDecBlk hDecUnmut hGetBlk hGetUnmut hSpkDecBlk hSpkDecUnmut hDropBlk hDropUnmut) hi

end Placed

end CryptoVerification.SignalSession.Cli.Store.SpkGetPoll

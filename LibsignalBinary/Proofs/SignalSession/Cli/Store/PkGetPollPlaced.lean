/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.SymPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `<OneTimePreKeyFiles as PreKeyStore>::get_pre_key::{closure#0}`

Top-level `[LibsignalPlacement]` contract `pkGetPoll_placed_ok_of_deps` on Block `573`
(`lsProg_573 H`) and caller-block-polymorphic transfer `pkGetPoll_placed_caller_ok_of_deps`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Store.PkGetPoll

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit CryptoVerification.RecordCodecsBinary
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon

section Placed

/-- Block `573` (`get_pre_key::{closure#0}`) meets `pkGetPollSpecPlaced rd pathOk A stk`
on `lsProg_573 H`. -/
theorem pkGetPoll_placed_ok_of_deps [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {decProg getProg pkDecProg dropProg : Program}
    {decBlk getBlk pkDecBlk dropBlk : Nat}
    [IsLsBlockProg decProg decBlk H]
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg pkDecProg pkDecBlk H]
    [IsLsBlockProg dropProg dropBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {decStk getStk stk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hDecimal : subroutine_ok decProg (lsmpl.base 597) (decimalSpecPlaced A decStk))
    (hGet : subroutine_ok getProg (lsmpl.base 589) (dirGetSpecPlaced rd pathOk A getStk))
    (hDec : subroutine_ok pkDecProg (lsmpl.base 65) (preKeyDeserializePlacedSpec A))
    (hDrop : subroutine_ok dropProg (lsmpl.base 553) (dropSpeWordSpecPlaced A))
    (hFs : TraceFsSound (lsProg_573 H))
    (hstk : 0x100 + max (max decStk getStk) (max smallRootStack (max dropSpeStackX extHookStack))
      ≤ stk)
    (hDecBlk : decBlk < 619 := by decide)
    (hDecUnmut : (decBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hPkDecBlk : pkDecBlk < 619 := by decide)
    (hPkDecUnmut : (pkDecBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hDropBlk : dropBlk < 619 := by decide)
    (hDropUnmut : (dropBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (lsProg_573 H) (lsmpl.base 573) (pkGetPollSpecPlaced rd pathOk A stk) := by
  have hDecimal' : subroutine_ok (lsProg_573 H) (lsmpl.base 597) (decimalSpecPlaced A decStk) :=
    ls_transfer_lscro (callerProg := lsProg_573 H) hDecimal (by decide) hDecBlk hDecUnmut
  have hGet' : subroutine_ok (lsProg_573 H) (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A getStk) :=
    ls_transfer_lscro (callerProg := lsProg_573 H) hGet (by decide) hGetBlk hGetUnmut
  have hDec' : subroutine_ok (lsProg_573 H) (lsmpl.base 65) (preKeyDeserializePlacedSpec A) :=
    ls_transfer_lscro (callerProg := lsProg_573 H) hDec (by decide) hPkDecBlk hPkDecUnmut
  have hDrop' : subroutine_ok (lsProg_573 H) (lsmpl.base 553) (dropSpeWordSpecPlaced A) :=
    ls_transfer_lscro (callerProg := lsProg_573 H) hDrop (by decide) hDropBlk hDropUnmut
  exact Helpers.pkGetPoll_placed_of_inner
    (calleeStk := max (max decStk getStk) (max smallRootStack (max dropSpeStackX extHookStack)))
    (fun hhi => Helpers.pkGetPollInner_placed_ok hC hDecimal' hGet' hDec' hDrop' hFs hhi)
    hstk

/-- Caller-block-polymorphic `get_pre_key::{closure#0}` contract at `lsmpl.base 573`. -/
theorem pkGetPoll_placed_caller_ok_of_deps [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {A : RustAlloc} {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    {decProg getProg pkDecProg dropProg : Program}
    {decBlk getBlk pkDecBlk dropBlk : Nat}
    [IsLsBlockProg decProg decBlk H]
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg pkDecProg pkDecBlk H]
    [IsLsBlockProg dropProg dropBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {decStk getStk stk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hDecimal : subroutine_ok decProg (lsmpl.base 597) (decimalSpecPlaced A decStk))
    (hGet : subroutine_ok getProg (lsmpl.base 589) (dirGetSpecPlaced rd pathOk A getStk))
    (hDec : subroutine_ok pkDecProg (lsmpl.base 65) (preKeyDeserializePlacedSpec A))
    (hDrop : subroutine_ok dropProg (lsmpl.base 553) (dropSpeWordSpecPlaced A))
    (hFs : TraceFsSound (lsProg_573 H))
    (hstk : 0x100 + max (max decStk getStk) (max smallRootStack (max dropSpeStackX extHookStack))
      ≤ stk)
    (hi : i < 619 := by decide)
    (hDecBlk : decBlk < 619 := by decide)
    (hDecUnmut : (decBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hPkDecBlk : pkDecBlk < 619 := by decide)
    (hPkDecUnmut : (pkDecBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hDropBlk : dropBlk < 619 := by decide)
    (hDropUnmut : (dropBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsmpl.base 573) (pkGetPollSpecPlaced rd pathOk A stk) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 573)
    (pkGetPoll_placed_ok_of_deps hC hDecimal hGet hDec hDrop hFs hstk
      hDecBlk hDecUnmut hGetBlk hGetUnmut hPkDecBlk hPkDecUnmut hDropBlk hDropUnmut) hi

end Placed

end CryptoVerification.SignalSession.Cli.Store.PkGetPoll

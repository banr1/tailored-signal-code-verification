/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.SymPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `<KyberPreKeyFiles as KyberPreKeyStore>::get_kyber_pre_key::{closure#0}`

Proves `kpkGetPollSpecPlaced` on Block `576` (`lsProg_576 H`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Store.KpkGetPoll

open Arm64 Arm64.Obj ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon

section Placed

/-- Block `576` (`get_kyber_pre_key::{closure#0}`) meets `kpkGetPollSpecPlaced rd pathOk A stk`
given `AllocContractsXCliPlaced`, `decimal` (block `597`), `Dir::get` (block `589`),
`decode_kyber_pre_key` (block `595`), and `TraceFsSound (lsProg_576 H)`. -/
theorem kpkGetPoll_placed_ok_of_deps [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {decProg getProg decodeProg : Program} {decBlk getBlk decodeBlk : Nat}
    [IsLsBlockProg decProg decBlk H]
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg decodeProg decodeBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {decStk getStk stk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hDecimal : subroutine_ok decProg (lsmpl.base 597) (decimalSpecPlaced A decStk))
    (hGet : subroutine_ok getProg (lsmpl.base 589) (dirGetSpecPlaced rd pathOk A getStk))
    (hDec : subroutine_ok decodeProg (lsmpl.base 595) (decodeKyberPreKeyPlacedSpec A))
    (hFs : TraceFsSound (lsProg_576 H))
    (hstk : 0x1b0 + max (max decStk getStk) (max smallRootStack extHookStack) ≤ stk)
    (hDecBlk : decBlk < 619 := by decide)
    (hDecUnmut : (decBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hDecodeBlk : decodeBlk < 619 := by decide)
    (hDecodeUnmut : (decodeBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (lsProg_576 H) (lsmpl.base 576)
      (kpkGetPollSpecPlaced rd pathOk A stk) := by
  have hDecimal' := ls_transfer_lscro (callerProg := lsProg_576 H) hDecimal (by decide) hDecBlk hDecUnmut
  have hGet' := ls_transfer_lscro (callerProg := lsProg_576 H) hGet (by decide) hGetBlk hGetUnmut
  have hDec' := ls_transfer_lscro (callerProg := lsProg_576 H) hDec (by decide) hDecodeBlk hDecodeUnmut
  exact Helpers.kpkGetPoll_placed_of_inner
    (fun hhi => Helpers.kpkGetPollInner_placed_ok hC hDecimal' hGet' hDec'
      (by omega) (by omega) (by omega) (by omega) hFs hhi)
    hstk

theorem kpkGetPoll_placed_caller_ok_of_deps [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {callerProg decProg getProg decodeProg : Program}
    {callerBlk decBlk getBlk decodeBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H]
    [IsLsBlockProg decProg decBlk H]
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg decodeProg decodeBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {decStk getStk stk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hDecimal : subroutine_ok decProg (lsmpl.base 597) (decimalSpecPlaced A decStk))
    (hGet : subroutine_ok getProg (lsmpl.base 589) (dirGetSpecPlaced rd pathOk A getStk))
    (hDec : subroutine_ok decodeProg (lsmpl.base 595) (decodeKyberPreKeyPlacedSpec A))
    (hFs : TraceFsSound (lsProg_576 H))
    (hstk : 0x1b0 + max (max decStk getStk) (max smallRootStack extHookStack) ≤ stk)
    (hCallerBlk : callerBlk < 619 := by decide)
    (hDecBlk : decBlk < 619 := by decide)
    (hDecUnmut : (decBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hDecodeBlk : decodeBlk < 619 := by decide)
    (hDecodeUnmut : (decodeBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsmpl.base 576)
      (kpkGetPollSpecPlaced rd pathOk A stk) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 576)
    (kpkGetPoll_placed_ok_of_deps hC hDecimal hGet hDec hFs hstk
      hDecBlk hDecUnmut hGetBlk hGetUnmut hDecodeBlk hDecodeUnmut) hCallerBlk

end Placed

end CryptoVerification.SignalSession.Cli.Store.KpkGetPoll

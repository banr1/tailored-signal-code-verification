/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPoll
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPoll.SymPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `<IdentityFiles as IdentityKeyStore>::is_trusted_identity::{closure#0}`

Proves `idTrustPollSpecPlaced` on Block `566` (`lsProg_566 H`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Store.IdTrustPoll

open Arm64 Arm64.Obj ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoGames.LibsignalSessionApi CryptoVerification.LibsignalSession
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon

section Placed

/-- Bridge from `FindReceiverChainIndex.publicKey_eq_placed_ok` (Block `212`) to
`Getters.publicKeyEqSpec`. -/
theorem publicKeyEq_placed_ok_of_bb [LibsignalPlacement] {H : LibsignalHooks}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    subroutine_ok ((blkPC_212).rebase (blkPl_212).base H)
      (lsmpl.base 212)
      (withLsCodeLoaded lsmpl Getters.publicKeyEqSpec) := by
  have h := FindReceiverChainIndex.publicKey_eq_placed_ok (H := H) h_bb
  have hspec : FindReceiverChainIndex.publicKeyEqSpec = Getters.publicKeyEqSpec := rfl
  rwa [hspec] at h

/-- Block `566` (`is_trusted_identity::{closure#0}`) meets `idTrustPollSpecPlaced rd pathOk A stk`
given `AllocContractsXCliPlaced`, `Dir::get` (block `589`), `IdentityKey::decode` (block `18`),
and `<PublicKey as PartialEq>::eq` (block `212`). -/
theorem idTrustPoll_placed_ok_of_deps [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {getProg decProg eqProg : Program} {getBlk decBlk eqBlk : Nat}
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg decProg decBlk H]
    [IsLsBlockProg eqProg eqBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk stk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hGet : subroutine_ok getProg (lsmpl.base 589) (dirGetSpecPlaced rd pathOk A getStk))
    (hDec : subroutine_ok decProg (lsmpl.base 18)
      (RecordCodecsBinary.identityKeyDecodePlacedSpec A))
    (hEq : subroutine_ok eqProg (lsmpl.base 212)
      (withLsCodeLoaded lsmpl Getters.publicKeyEqSpec))
    (hstk : 0xc0 + max (max getStk 0x60) (max 64 extHookStack) ≤ stk)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hDecBlk : decBlk < 619 := by decide)
    (hDecUnmut : (decBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hEqBlk : eqBlk < 619 := by decide)
    (hEqUnmut : (eqBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (lsProg_566 H) (lsmpl.base 566)
      (idTrustPollSpecPlaced rd pathOk A stk) := by
  have hGet' := ls_transfer_lscro (callerProg := (blkPC_566).rebase (blkPl_566).base H)
    hGet (by decide) hGetBlk hGetUnmut
  have hDec' := ls_transfer_cl_to_lscro (callerProg := (blkPC_566).rebase (blkPl_566).base H)
    hDec (by decide) hDecBlk hDecUnmut
  have hEq' := ls_transfer_cl_to_lscro (callerProg := (blkPC_566).rebase (blkPl_566).base H)
    hEq (by decide) hEqBlk hEqUnmut
  exact Helpers.idTrustPoll_placed_of_inner
    (fun hhi => Helpers.idTrustPollInner_placed_ok hC hGet' hDec' hEq' hhi) hstk

/-- Convenience specialization discharging `IdentityKey::decode` via
`RecordCodecsBinary.IdentityKeyDecode.identityKey_decode_placed_ok` and `<PublicKey as PartialEq>::eq`
via `publicKeyEq_placed_ok_of_bb`. -/
theorem idTrustPoll_placed_ok_of_get_bb [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {getProg : Program} {getBlk : Nat} [IsLsBlockProg getProg getBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk stk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hGet : subroutine_ok getProg (lsmpl.base 589) (dirGetSpecPlaced rd pathOk A getStk))
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (hstk : 0xc0 + max (max getStk 0x60) (max 64 extHookStack) ≤ stk)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (lsProg_566 H) (lsmpl.base 566)
      (idTrustPollSpecPlaced rd pathOk A stk) :=
  idTrustPoll_placed_ok_of_deps hC hGet
    (RecordCodecsBinary.IdentityKeyDecode.identityKey_decode_placed_ok H)
    (publicKeyEq_placed_ok_of_bb h_bb) hstk hGetBlk hGetUnmut

theorem idTrustPoll_placed_caller_ok_of_deps [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {callerProg getProg decProg eqProg : Program}
    {callerBlk getBlk decBlk eqBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H]
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg decProg decBlk H]
    [IsLsBlockProg eqProg eqBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk stk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hGet : subroutine_ok getProg (lsmpl.base 589) (dirGetSpecPlaced rd pathOk A getStk))
    (hDec : subroutine_ok decProg (lsmpl.base 18)
      (RecordCodecsBinary.identityKeyDecodePlacedSpec A))
    (hEq : subroutine_ok eqProg (lsmpl.base 212)
      (withLsCodeLoaded lsmpl Getters.publicKeyEqSpec))
    (hstk : 0xc0 + max (max getStk 0x60) (max 64 extHookStack) ≤ stk)
    (hCallerBlk : callerBlk < 619 := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hDecBlk : decBlk < 619 := by decide)
    (hDecUnmut : (decBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hEqBlk : eqBlk < 619 := by decide)
    (hEqUnmut : (eqBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsmpl.base 566)
      (idTrustPollSpecPlaced rd pathOk A stk) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 566)
    (idTrustPoll_placed_ok_of_deps hC hGet hDec hEq hstk
      hGetBlk hGetUnmut hDecBlk hDecUnmut hEqBlk hEqUnmut) hCallerBlk

end Placed

end CryptoVerification.SignalSession.Cli.Store.IdTrustPoll

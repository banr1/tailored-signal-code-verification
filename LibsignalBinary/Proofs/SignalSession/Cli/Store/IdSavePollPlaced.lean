/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.SymPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEq
public import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyDecode

/-!
# Relocatable `<IdentityFiles as IdentityKeyStore>::save_identity::{closure#0}`

Proves `idSavePollSpecPlaced` on Block `565` (`lsProg_565 H`) under `[LibsignalPlacement]`, with
caller-polymorphic transfer and specializations discharging `IdentityKey::decode` and
`PublicKey::eq`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Store.IdSavePoll

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
  have h2 := FindReceiverChainIndex.publicKey_eq_placed_ok (H := H) h_bb
  have hspec : FindReceiverChainIndex.publicKeyEqSpec = Getters.publicKeyEqSpec := rfl
  rwa [hspec] at h2

/-- Block `565` (`save_identity::{closure#0}`) meets `idSavePollSpecPlaced rd pathOk A stk`
given `AllocContractsXCliPlaced`, `CliPanicHooksPlaced`, `Dir::get` (block `589`),
`Dir::put::<&str>` (block `543`), `IdentityKey::decode` (block `18`), and
`<PublicKey as PartialEq>::eq` (block `212`). -/
theorem idSavePoll_placed_ok_of_deps [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {getProg putProg decProg eqProg : Program} {getBlk putBlk decBlk eqBlk : Nat}
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg putProg putBlk H]
    [IsLsBlockProg decProg decBlk H]
    [IsLsBlockProg eqProg eqBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk putStk stk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hpan : CliPanicHooksPlaced H)
    (hGet : subroutine_ok getProg (lsmpl.base 589) (dirGetSpecPlaced rd pathOk A getStk))
    (hPut : subroutine_ok putProg (lsmpl.base 543) (dirPutStrSpecPlaced A putStk))
    (hDec : subroutine_ok decProg (lsmpl.base 18)
      (RecordCodecsBinary.identityKeyDecodePlacedSpec A))
    (hEq : subroutine_ok eqProg (lsmpl.base 212)
      (withLsCodeLoaded lsmpl Getters.publicKeyEqSpec))
    (hstk : 0xd0 + max (max (max getStk putStk) (max 0x60 64))
      (max publicKeySerializeStackX extHookStack) ≤ stk)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hPutBlk : putBlk < 619 := by decide)
    (hPutUnmut : (putBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hDecBlk : decBlk < 619 := by decide)
    (hDecUnmut : (decBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hEqBlk : eqBlk < 619 := by decide)
    (hEqUnmut : (eqBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (lsProg_565 H) (lsmpl.base 565)
      (idSavePollSpecPlaced rd pathOk A stk) := by
  have hSer := Helpers.publicKeySerialize_lscro_of_cli
    (callerProg := (blkPC_565).rebase (blkPl_565).base H) hC hpan (by decide)
  have hGet' := ls_transfer_lscro (callerProg := (blkPC_565).rebase (blkPl_565).base H)
    hGet (by decide) hGetBlk hGetUnmut
  have hPut' := ls_transfer_lscro (callerProg := (blkPC_565).rebase (blkPl_565).base H)
    hPut (by decide) hPutBlk hPutUnmut
  have hDec' := ls_transfer_cl_to_lscro (callerProg := (blkPC_565).rebase (blkPl_565).base H)
    hDec (by decide) hDecBlk hDecUnmut
  have hEq' := ls_transfer_cl_to_lscro (callerProg := (blkPC_565).rebase (blkPl_565).base H)
    hEq (by decide) hEqBlk hEqUnmut
  exact Helpers.idSavePoll_placed_ok_of_deps_core hC hSer hGet' hPut' hDec' hEq' hstk

/-- Convenience specialization discharging `IdentityKey::decode` and `<PublicKey as PartialEq>::eq`. -/
theorem idSavePoll_placed_ok_of_get_put_bb [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {getProg putProg : Program} {getBlk putBlk : Nat}
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg putProg putBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk putStk stk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hpan : CliPanicHooksPlaced H)
    (hGet : subroutine_ok getProg (lsmpl.base 589) (dirGetSpecPlaced rd pathOk A getStk))
    (hPut : subroutine_ok putProg (lsmpl.base 543) (dirPutStrSpecPlaced A putStk))
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (hstk : 0xd0 + max (max (max getStk putStk) (max 0x60 64))
      (max publicKeySerializeStackX extHookStack) ≤ stk)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hPutBlk : putBlk < 619 := by decide)
    (hPutUnmut : (putBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (lsProg_565 H) (lsmpl.base 565)
      (idSavePollSpecPlaced rd pathOk A stk) :=
  idSavePoll_placed_ok_of_deps hC hpan hGet hPut
    (RecordCodecsBinary.IdentityKeyDecode.identityKey_decode_placed_ok H)
    (publicKeyEq_placed_ok_of_bb h_bb) hstk hGetBlk hGetUnmut hPutBlk hPutUnmut

theorem idSavePoll_placed_caller_ok_of_deps [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {callerProg getProg putProg decProg eqProg : Program}
    {callerBlk getBlk putBlk decBlk eqBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H]
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg putProg putBlk H]
    [IsLsBlockProg decProg decBlk H]
    [IsLsBlockProg eqProg eqBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk putStk stk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hpan : CliPanicHooksPlaced H)
    (hGet : subroutine_ok getProg (lsmpl.base 589) (dirGetSpecPlaced rd pathOk A getStk))
    (hPut : subroutine_ok putProg (lsmpl.base 543) (dirPutStrSpecPlaced A putStk))
    (hDec : subroutine_ok decProg (lsmpl.base 18)
      (RecordCodecsBinary.identityKeyDecodePlacedSpec A))
    (hEq : subroutine_ok eqProg (lsmpl.base 212)
      (withLsCodeLoaded lsmpl Getters.publicKeyEqSpec))
    (hstk : 0xd0 + max (max (max getStk putStk) (max 0x60 64))
      (max publicKeySerializeStackX extHookStack) ≤ stk)
    (hCallerBlk : callerBlk < 619 := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hPutBlk : putBlk < 619 := by decide)
    (hPutUnmut : (putBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hDecBlk : decBlk < 619 := by decide)
    (hDecUnmut : (decBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hEqBlk : eqBlk < 619 := by decide)
    (hEqUnmut : (eqBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsmpl.base 565)
      (idSavePollSpecPlaced rd pathOk A stk) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 565)
    (idSavePoll_placed_ok_of_deps hC hpan hGet hPut hDec hEq hstk
      hGetBlk hGetUnmut hPutBlk hPutUnmut hDecBlk hDecUnmut hEqBlk hEqUnmut) hCallerBlk

end Placed

end CryptoVerification.SignalSession.Cli.Store.IdSavePoll

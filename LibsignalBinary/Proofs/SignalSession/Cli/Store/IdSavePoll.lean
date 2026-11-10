/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.StoreSpecs.Identity
public import LibsignalBinary.Proofs.TripleRatchet.Getters.Defs
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.Sym

/-!
# Poll of `<IdentityFiles as IdentityKeyStore>::save_identity`

Verifies `save_identity::{closure#0}` (`idSavePoll_fnOff`, `0xd0`-byte frame) against
`idSavePollSpec`: reads any existing peer identity key via `Dir::get`, decodes and compares it via
`IdentityKey::decode` and `<PublicKey as PartialEq>::eq` to compute `replaced`, serializes the new
key via `PublicKey::serialize`, and writes it via `Dir::put::<&str>`.
-/

@[expose] public section


namespace CryptoVerification.SignalSession.Cli.Store.IdSavePoll

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit CryptoGames.LibsignalSessionApi

/-- The `save_identity` poll meets `idSavePollSpec rd pathOk A img stk` at any 4 KiB-aligned
image base, given the hook contracts, `Dir::get` (budget `getStk`), `Dir::put::<&str>` (budget
`putStk`), `IdentityKey::decode` and `<PublicKey as PartialEq>::eq`. -/
theorem idSavePoll_ok_of_deps {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {getStk putStk stk : Nat}
    (hC : AllocContractsX img A ext)
    (hGet : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirGetName)
      (dirGetSpec rd pathOk A img getStk))
    (hPut : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutStrName)
      (dirPutStrSpec A img putStk))
    (hDec : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr RecordCodecsBinary.identityKeyDecodeName)
      (RecordCodecsBinary.identityKeyDecodeSpec A img))
    (hEq : Getters.PublicKeyEqOkExt img.base ext)
    (hstk : 0xd0 + max (max (max getStk putStk) (max 0x60 64))
      (max publicKeySerializeStackX extHookStack) ≤ stk)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr idSavePollName)
      (idSavePollSpec rd pathOk A img stk) := by
  exact Helpers.idSavePoll_ok_of_deps_core hC hGet hPut hDec hEq hstk hb

/-- Stacked 32-bit `black_box` variant (`PublicKeyEqOkExt32`) of `idSavePoll_ok_of_deps`:
`<PublicKey as PartialEq>::eq` meets `publicKeyEqSpecExt` (`64 + extHookStack = 16448` B). -/
theorem idSavePoll_ok_of_deps_ext32 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {getStk putStk stk : Nat}
    (hC : AllocContractsX img A ext)
    (hGet : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirGetName)
      (dirGetSpec rd pathOk A img getStk))
    (hPut : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutStrName)
      (dirPutStrSpec A img putStk))
    (hDec : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr RecordCodecsBinary.identityKeyDecodeName)
      (RecordCodecsBinary.identityKeyDecodeSpec A img))
    (hEq : Getters.PublicKeyEqOkExt32 img.base ext)
    (hstk : 0xd0 + max (max (max getStk putStk) 0x60)
      (max publicKeySerializeStackX Getters.publicKeyEqStackExt) ≤ stk)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr idSavePollName)
      (idSavePollSpec rd pathOk A img stk) :=
  Helpers.idSavePoll_ok_of_deps_core_ext32 hC hGet hPut hDec hEq hstk hb

end CryptoVerification.SignalSession.Cli.Store.IdSavePoll

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.StoreSpecs.Identity
public import LibsignalBinary.Proofs.TripleRatchet.Getters.Defs
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPoll.Callees
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPoll.Sym

/-!
# Poll of `<IdentityFiles as IdentityKeyStore>::is_trusted_identity`

Verifies `is_trusted_identity::{closure#0}` (`0xc0`-byte frame) against `idTrustPollSpec`: reads
the stored peer key bytes via `Dir::get`, returns `true` when absent, or decodes via
`IdentityKey::decode`, frees any heap buffer, and compares keys via `<PublicKey as PartialEq>::eq`
(ignoring the direction byte at box `+0x19`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Store.IdTrustPoll

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit CryptoGames.LibsignalSessionApi

/-- The `is_trusted_identity` poll meets `idTrustPollSpec rd pathOk A img stk` at any 4
KiB-aligned image base, given the hook contracts, `Dir::get` (budget `getStk`, read rule `rd`
on the `pathOk` paths), `IdentityKey::decode` and `<PublicKey as PartialEq>::eq`. -/
theorem idTrustPoll_ok_of_deps {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {getStk stk : Nat}
    (hC : AllocContractsX img A ext)
    (hGet : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirGetName)
      (dirGetSpec rd pathOk A img getStk))
    (hDec : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr RecordCodecsBinary.identityKeyDecodeName)
      (RecordCodecsBinary.identityKeyDecodeSpec A img))
    (hEq : Getters.PublicKeyEqOkExt img.base ext)
    (hstk : 0xc0 + max (max getStk 0x60) (max 64 extHookStack) ≤ stk)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr idTrustPollName)
      (idTrustPollSpec rd pathOk A img stk) := by
  let _ := hb
  exact Helpers.idTrustPoll_of_inner
    (fun hhi => Helpers.idTrustPollInner_ok hC hGet hDec hEq hhi) hstk

/-- Stacked 32-bit `black_box` variant (`PublicKeyEqOkExt32`) of `idTrustPoll_ok_of_deps`:
`<PublicKey as PartialEq>::eq` meets `publicKeyEqSpecExt` (`64 + extHookStack = 16448` B). -/
theorem idTrustPoll_ok_of_deps_ext32 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {getStk stk : Nat}
    (hC : AllocContractsX img A ext)
    (hGet : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirGetName)
      (dirGetSpec rd pathOk A img getStk))
    (hDec : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr RecordCodecsBinary.identityKeyDecodeName)
      (RecordCodecsBinary.identityKeyDecodeSpec A img))
    (hEq : Getters.PublicKeyEqOkExt32 img.base ext)
    (hstk : 0xc0 + max (max getStk 0x60) Getters.publicKeyEqStackExt ≤ stk)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr idTrustPollName)
      (idTrustPollSpec rd pathOk A img stk) := by
  let _ := hb
  exact Helpers.idTrustPoll_of_inner
    (fun hhi => Helpers.idTrustPollInner_ok_ext32 hC hGet hDec hEq hhi) hstk

end CryptoVerification.SignalSession.Cli.Store.IdTrustPoll

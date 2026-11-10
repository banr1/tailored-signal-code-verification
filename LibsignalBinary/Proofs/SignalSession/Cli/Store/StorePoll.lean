/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.StoreSpecs.Session
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePoll.Sym

/-!
# `<SessionFiles as SessionStore>::store_session` Future Poll

Proves that `store_session::{closure#0}` (`0xd0`-byte frame, 48-byte sret) formats the peer address
via `address_text`, serializes the canonical `SessionRecord` via `SessionRecord::serialize`
(`serializeCanonSpec`), stores the resulting key/value pair in memory via `Dir::put::<String>`,
sets the future state byte to `1`, and satisfies `sessStorePollSpec`.
-/

@[expose] public section

namespace CryptoVerification.SignalSession.Cli.Store.StorePoll

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit

/-- The `store_session` poll meets `sessStorePollSpec A img stk` at any 4 KiB-aligned image
base, given the hook contracts, `address_text` (budget `addrStk`), `SessionRecord::serialize`,
and `Dir::put::<String>` (budget `putStk`). -/
theorem sessStorePoll_ok_of_deps {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {addrStk putStk stk : Nat}
    (hC : AllocContractsX img A ext)
    (hAddr : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr addressTextName)
      (addrTextSpec A img addrStk))
    (hSer : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recordSerializeName)
      ((E2E.Record.Serialization.serializeCanonSpec A).inImage img))
    (hPut : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutName)
      (dirPutSpec A img putStk))
    (hstk : 0xd0 + max (max addrStk E2E.Record.Serialization.serializeStack)
      (max putStk extHookStack) ≤ stk)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr sessStorePollName)
      (sessStorePollSpec A img stk) := by
  let _ := hC
  let _ := hb
  exact Helpers.sessStorePoll_of_inner
    (fun hhi => Helpers.sessStorePollInner_ok hAddr hSer hPut hhi) hstk

end CryptoVerification.SignalSession.Cli.Store.StorePoll

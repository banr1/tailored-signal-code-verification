/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.StoreSpecs.Session
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll.Sym

/-!
# Poll of `<SessionFiles as SessionStore>::load_session`

Verifies `load_session::{closure#0}` (`0x350`-byte frame, 368-byte `sret`) against
`sessLoadPollSpec`: formats the peer address via `address_text`, reads the session file via
`Dir::get`, returns `Err` (`speWord 1`) on I/O failure or `Ok none` on an empty file, and on
non-empty bytes invokes `SessionRecord::deserialize` and copies the 368-byte `Option<SessionRecord>`
into `out`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Store.LoadPoll

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit CryptoGames.LibsignalSessionApi

/-- The `load_session` poll meets `sessLoadPollSpec rd pathOk Scope A img stk` at any 4
KiB-aligned image base, given the hook contracts, `address_text` (budget `addrStk`), `Dir::get`
(budget `getStk`, read rule `rd` on the `pathOk` paths), `SessionRecord::deserialize` on
`Scope`, and trace soundness. -/
theorem sessLoadPoll_ok_of_deps {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {addrStk getStk stk : Nat}
    (hC : AllocContractsX img A ext)
    (hAddr : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr addressTextName)
      (addrTextSpec A img addrStk))
    (hGet : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirGetName)
      (dirGetSpec rd pathOk A img getStk))
    (hDeser : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recordDeserializeName)
      (sessDeserializeSpec Scope A img))
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (hstk : 0x350 + max (max addrStk getStk) (max E2E.Record.recDeserializeStack extHookStack) ≤
      stk)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr sessLoadPollName)
      (sessLoadPollSpec rd pathOk Scope A img stk) := by
  let _ := hb
  exact Helpers.sessLoadPoll_ok hC hAddr hGet hDeser hFs hstk

/-- The `load_session` poll meets `sessLoadPollSpec rd pathOk Scope A img stk` from
`sessDeserializeExtSpec Scope A img` (carrying `A.pool` across `SessionRecord::deserialize`). -/
theorem sessLoadPoll_ok_of_deps_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {addrStk getStk stk : Nat}
    (hC : AllocContractsX img A ext)
    (hAddr : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr addressTextName)
      (addrTextSpec A img addrStk))
    (hGet : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirGetName)
      (dirGetSpec rd pathOk A img getStk))
    (hDeser : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recordDeserializeName)
      (sessDeserializeExtSpec Scope A img))
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (hstk : 0x350 + max (max addrStk getStk) (max E2E.Record.recDeserializeStack extHookStack) ≤
      stk)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr sessLoadPollName)
      (sessLoadPollSpec rd pathOk Scope A img stk) := by
  let _ := hb
  exact Helpers.sessLoadPoll_ok_ext hC hAddr hGet hDeser hFs hstk

end CryptoVerification.SignalSession.Cli.Store.LoadPoll

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.StoreSpecs.PreKey
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.Sym

/-!
# `<OneTimePreKeyFiles as PreKeyStore>::remove_pre_key` Future Poll

Proves that `remove_pre_key::{closure#0}` (`pkRemovePoll_fnOff`, `0xc0`-byte frame, 48-byte sret)
formats the decimal key ID, reads the existing entry via `Dir::get`, writes an empty byte vector via
`Dir::put::<String>` when the entry was nonempty, frees temporary buffers, sets the future state
byte to `1`, and satisfies `pkRemovePollSpec`.
-/

@[expose] public section

namespace CryptoVerification.SignalSession.Cli.Store.PkRemovePoll

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit

/-- The `remove_pre_key` poll meets `pkRemovePollSpec rd pathOk A img stk` at any 4
KiB-aligned image base, given the hook contracts, `decimal`, `Dir::get` and `Dir::put::<String>`. -/
theorem pkRemovePoll_ok_of_deps {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {decStk getStk putStk stk : Nat}
    (hC : AllocContractsX img A ext)
    (hDecimal : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decimalName)
      (decimalSpec A img decStk))
    (hGet : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirGetName)
      (dirGetSpec rd pathOk A img getStk))
    (hPut : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutName)
      (dirPutSpec A img putStk))
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (hstk : 0xc0 + max (max decStk getStk) (max putStk extHookStack) ≤ stk)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pkRemovePollName)
      (pkRemovePollSpec rd pathOk A img stk) := by
  let _ := hb
  exact Helpers.pkRemovePoll_ok hC hDecimal hGet hPut hFs hstk

end CryptoVerification.SignalSession.Cli.Store.PkRemovePoll

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.StoreSpecs.KpkMark
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Sym

/-!
# Poll of `<KyberPreKeyFiles as KyberPreKeyStore>::mark_kyber_pre_key_used`

Verifies `mark_kyber_pre_key_used::{closure#0}` (`kpkMarkPoll_fnOff`, `0xf0`-byte frame, 48-byte
`sret`) against `kpkMarkPollSpec`: looks up `keyName id` in `one_time` (`self`) via `Dir::get`,
truncating non-empty entries via `Dir::put::<String>` or falling back on empty entries to
`baseKeysName id` in `last_resort` (`self + 0x28`), where it checks 37-byte chunks via `bcmp` for
reuse or malformation and otherwise appends `le32 signedId ++ baseKey.serialize`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Store.KpkMarkPoll

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit CryptoVerification.CodeLayout

/-- The `mark_kyber_pre_key_used` poll meets `kpkMarkPollSpec rd pathOk A img stk` at any
4 KiB-aligned loaded image, given the allocator/hook contracts, `decimal`, `Dir::get`,
`Dir::put::<String>`, and `TraceFsSound`. -/
theorem kpkMarkPoll_ok_of_deps {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {decStk getStk putStk stk : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hC : AllocContractsX img A ext)
    (hBcmp : HookSat ext cliBcmpName cliBcmpSpec)
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
    (hstk : 0xf0 + max (max decStk getStk) (max putStk doReserveStackX) ≤ stk)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr kpkMarkPollName)
      (kpkMarkPollSpec rd pathOk A img stk) :=
  Helpers.kpkMarkPoll_ok himg hb hC hBcmp hDecimal hGet hPut hFs hstk

end CryptoVerification.SignalSession.Cli.Store.KpkMarkPoll

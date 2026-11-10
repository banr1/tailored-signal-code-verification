/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.StoreSpecs.PreKey
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.Sym

/-!
# Poll of `<KyberPreKeyFiles as KyberPreKeyStore>::get_kyber_pre_key`

Verifies `get_kyber_pre_key::{closure#0}` (`kpkGetPoll_fnOff`, `0x1b0`-byte frame, 88-byte `sret`)
against `kpkGetPollSpec`: formats the key ID via `decimal`, looks up the `one_time` directory at
`self` via `Dir::get` and decodes non-empty records via `decode_kyber_pre_key`, falling back on an
empty `one_time` lookup to the `last_resort` directory at `self + 0x28` and returning
`InvalidKyberPreKeyId` (`speWord 15`) if both are absent.
-/

@[expose] public section

namespace CryptoVerification.SignalSession.Cli.Store.KpkGetPoll

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit CryptoVerification.RecordCodecsBinary

/-- The `get_kyber_pre_key` poll meets `kpkGetPollSpec rd pathOk A img stk` at any 4
KiB-aligned image base, given the hook contracts, `decimal`, `Dir::get` and
`decode_kyber_pre_key`. -/
theorem kpkGetPoll_ok_of_deps {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {decStk getStk stk : Nat}
    (hC : AllocContractsX img A ext)
    (hDecimal : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decimalName)
      (decimalSpec A img decStk))
    (hGet : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirGetName)
      (dirGetSpec rd pathOk A img getStk))
    (hDec : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodeKyberPreKeyName)
      (decodeKyberPreKeySpec A img))
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (hstk : 0x1b0 + max (max decStk getStk) (max smallRootStack extHookStack) ≤ stk)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr kpkGetPollName)
      (kpkGetPollSpec rd pathOk A img stk) := by
  let _ := hb
  exact Helpers.kpkGetPoll_of_inner
    (fun hhi => Helpers.kpkGetPollInner_ok hC hDecimal hGet hDec
      (by omega) (by omega) (by omega) (by omega) hFs hhi)
    hstk

end CryptoVerification.SignalSession.Cli.Store.KpkGetPoll

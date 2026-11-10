/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.StoreSpecs.PreKey
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkShims.Shim16A
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkShims.Shim16B
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkShims.MarkShim

/-!
# Pre-Key Store `async_trait` Shims

Proves the `async_trait` future-boxing shims for the pre-key stores:
- 16-byte `pkBoxAt` shims (`0x20`-byte frame): `get_signed_pre_key`, `get_pre_key`,
  `remove_pre_key`, and `get_kyber_pre_key` (`pkShimSpec`);
- 32-byte `kpkMarkBoxAt` shim (`0x30`-byte frame): `mark_kyber_pre_key_used` (`kpkMarkShimSpec`).
-/

@[expose] public section

namespace CryptoVerification.SignalSession.Cli.Store.PkShims

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

/-- The `get_signed_pre_key` shim meets `pkShimSpec spkGetFutVtOff A img stk`. -/
theorem spkGetShim_ok_of_deps {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {stk : Nat}
    (hC : AllocContractsX img A ext)
    (hstk : 0x20 + extHookStack ≤ stk)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spkGetShimName)
      (pkShimSpec spkGetFutVtOff A img stk) := by
  exact Helpers.pkShim_lift_stk (Helpers.spkGetShim_fixed_ok hC hb) hstk

/-- The `get_pre_key` shim meets `pkShimSpec pkGetFutVtOff A img stk`. -/
theorem pkGetShim_ok_of_deps {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {stk : Nat}
    (hC : AllocContractsX img A ext)
    (hstk : 0x20 + extHookStack ≤ stk)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pkGetShimName)
      (pkShimSpec pkGetFutVtOff A img stk) := by
  exact Helpers.pkShim_lift_stk (Helpers.pkGetShim_fixed_ok hC hb) hstk

/-- The `remove_pre_key` shim meets `pkShimSpec pkRemoveFutVtOff A img stk`. -/
theorem pkRemoveShim_ok_of_deps {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {stk : Nat}
    (hC : AllocContractsX img A ext)
    (hstk : 0x20 + extHookStack ≤ stk)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pkRemoveShimName)
      (pkShimSpec pkRemoveFutVtOff A img stk) := by
  exact Helpers.pkShim_lift_stk (Helpers.pkRemoveShim_fixed_ok hC hb) hstk

/-- The `get_kyber_pre_key` shim meets `pkShimSpec kpkGetFutVtOff A img stk`. -/
theorem kpkGetShim_ok_of_deps {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {stk : Nat}
    (hC : AllocContractsX img A ext)
    (hstk : 0x20 + extHookStack ≤ stk)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr kpkGetShimName)
      (pkShimSpec kpkGetFutVtOff A img stk) := by
  exact Helpers.pkShim_lift_stk (Helpers.kpkGetShim_fixed_ok hC hb) hstk

/-- The `mark_kyber_pre_key_used` shim meets `kpkMarkShimSpec A img stk`. -/
theorem kpkMarkShim_ok_of_deps {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {stk : Nat}
    (hC : AllocContractsX img A ext)
    (hstk : 0x30 + extHookStack ≤ stk)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr kpkMarkShimName)
      (kpkMarkShimSpec A img stk) := by
  exact Helpers.kpkMarkShim_ok_main hC hstk hb

end CryptoVerification.SignalSession.Cli.Store.PkShims

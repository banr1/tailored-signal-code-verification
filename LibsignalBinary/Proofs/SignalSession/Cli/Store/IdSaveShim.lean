/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.StoreSpecs.Identity
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSaveShim.Sym

/-!
# `<IdentityFiles as IdentityKeyStore>::save_identity` Async-Trait Shim

Verifies `save_identity` (`idSaveShim_fnOff`, `0x30`-byte frame) against `idSaveShimSpec`:
allocates a 32-byte future box `[self, address, key, state = 0]` via `__rust_alloc(32, 8)` and
returns `(box, img.base + idSaveFutVtOff)`.
-/

@[expose] public section

namespace CryptoVerification.SignalSession.Cli.Store.IdSaveShim

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit

/-- The `save_identity` shim meets `idSaveShimSpec A img stk` at any 4 KiB-aligned image
base, given the hook contracts. -/
theorem idSaveShim_ok_of_deps {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {stk : Nat}
    (hC : AllocContractsX img A ext)
    (hstk : 0x30 + extHookStack ≤ stk)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr idSaveShimName)
      (idSaveShimSpec A img stk) := by
  exact Helpers.idSaveShim_ok_main hC hstk hb

end CryptoVerification.SignalSession.Cli.Store.IdSaveShim

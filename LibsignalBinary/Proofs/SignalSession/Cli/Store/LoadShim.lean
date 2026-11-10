/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.StoreSpecs.Session
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadShim.Sym

/-!
# `<SessionFiles as SessionStore>::load_session` Shim

Proves that the `async_trait` shim for `SessionFiles::load_session` (`sessLoadShim_fnOff`,
`0x20`-byte frame) allocates a 24-byte `sessLoadBoxAt` future box via `__rust_alloc(24, 8)`,
returns the box pointer in `x0` and `img.base + sessLoadFutVtOff` in `x1`, and panics via
`handle_alloc_error` on allocation failure (`sessLoadShimSpec`).
-/

@[expose] public section

namespace CryptoVerification.SignalSession.Cli.Store.LoadShim

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit

/-- The `load_session` shim meets `sessLoadShimSpec A img stk` at any 4 KiB-aligned image
base, given the hook contracts. -/
theorem sessLoadShim_ok_of_deps {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {stk : Nat}
    (hC : AllocContractsX img A ext)
    (hstk : 0x20 + extHookStack ≤ stk)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr sessLoadShimName)
      (sessLoadShimSpec A img stk) := by
  exact Helpers.sessLoadShim_ok_main hC hstk hb

end CryptoVerification.SignalSession.Cli.Store.LoadShim

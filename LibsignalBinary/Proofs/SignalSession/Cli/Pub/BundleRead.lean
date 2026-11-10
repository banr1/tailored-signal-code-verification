/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.PublicSpecs
public import LibsignalBinary.Proofs.SignalSession.Cli.Pub.BundleRead.Proof
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliRunFixed

/-!
# Subroutine Contract for `signal_session::public::read_bundle::{closure#0}`

Verifies `bundleReadSpec` for `|name| io::read_file(&path(dir, name)).map_err(unreadable)` (`0x50`-byte
stack frame): constructs `path(dir, name)`, calls `read_file`, writes either the returned `Vec<u8>`
or a 22-byte `"file could not be read"` `SignalProtocolError` (`"read"`) to `sret`, and tail-calls
`__rust_dealloc` on `path` when `path.cap ≠ 0`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.BundleRead

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit

/-- `read_bundle::{closure#0}` satisfies `bundleReadSpec` from its callee contracts. -/
theorem bundleRead_ok_of_deps {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {pathStk readStk stk : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hpLen : ∀ p, pathOk p → p.length < 2 ^ 32)
    (hC : AllocContractsX img A ext)
    (hPath : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pathName)
      (pathSpec A img pathStk))
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr readFileName)
      (readFileSpec rd pathOk A img readStk))
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (hstk : 0x50 + max (max pathStk readStk) extHookStack ≤ stk)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr bundleReadName)
      (bundleReadSpec rd pathOk A img stk) := by
  exact Helpers.bundleRead_ok_of_loads himg hpLen hC hPath hRead hFs hstk hb

end CryptoVerification.SignalSession.Cli.BundleRead

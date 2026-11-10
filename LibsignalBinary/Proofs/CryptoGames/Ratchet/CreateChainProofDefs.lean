/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.Ratchet.CreateChainDefs
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.RootKdfDefs

/-!
# Proof-Side Definitions for `CreateChainDefs`

Byte-list X25519 wrapper and 64-byte `(RootKey, ChainKey)` tuple encoding for `create_chain` proofs.
-/

@[expose] public section

namespace CryptoGames
namespace Ratchet
open HMAC HKDF

/-- An `X25519Fn` on byte lists (the argument type of `CKA.X25519Model`): `X` on 32-byte inputs,
`[]` otherwise. -/
def X25519Fn.toListFn (X : X25519Fn) : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) :=
  fun k u =>
    if hk : k.length = 32 then
      if hu : u.length = 32 then (X ⟨k, hk⟩ ⟨u, hu⟩).toList else []
    else []

/-- The 64 bytes `root_key ‖ chain_key` of a `(RootKey, ChainKey)` pair, as the binary returns
them (the tuple `([u8; 32], [u8; 32])`, root key first). -/
def keysToBytes (p : RootKey × ChainKey) : List (BitVec 8) :=
  keyToBytes32 p.1 ++ keyToBytes32 p.2

end Ratchet
end CryptoGames

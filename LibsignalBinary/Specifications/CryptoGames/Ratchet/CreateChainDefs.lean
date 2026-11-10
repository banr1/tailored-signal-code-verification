/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.Ratchet.RootKdfDefs

/-!
# `RootKey::create_chain` with the X25519 agreement, over abstract SHA-256 and X25519

**Trusted: definitions used by the statement.** The theorems of `Computational/Theorems/` use every
definition in this file: read them. The theorems here are checked by Lean. See
`Computational/docs/TRUSTED_BASE.md`.

Models the X25519 key-agreement half of libsignal v0.105.4 `RootKey::create_chain`
(`rust/protocol/src/ratchet/keys.rs:199–218`): RFC 7748 scalar clamping (`clampScalar`), abstract
X25519 evaluation (`X25519Fn`), all-zero shared-secret rejection, and HKDF root derivation via
`rootKdf`.
-/

@[expose] public section

namespace CryptoGames
namespace Ratchet

open HMAC HKDF

/-- Abstract X25519 function mapping 32 clamped scalar bytes and 32 u-coordinate bytes to 32
u-coordinate bytes (all LE). -/
abbrev X25519Fn := List.Vector (BitVec 8) 32 → List.Vector (BitVec 8) 32 → List.Vector (BitVec 8) 32

/-- `curve25519_dalek::scalar::clamp_integer` (v5.0.0): `k[0] &= 0xf8; k[31] &= 0x7f; k[31] |= 0x40`. -/
def clampScalar (k : List.Vector (BitVec 8) 32) : List.Vector (BitVec 8) 32 :=
  ((k.set 0 (k.get 0 &&& 0xf8#8)).set 31 ((k.get 31 &&& 0x7f#8) ||| 0x40#8))

/-- 32 LE bytes of a 256-bit key as a `List.Vector`. -/
def keyToBytesVec32 (k : BitVec 256) : List.Vector (BitVec 8) 32 :=
  ⟨keyToBytes32 k, by simp [keyToBytes32]⟩

/-- `RootKey::create_chain` over abstract SHA-256 `F` and X25519 `X`: computes
`ss = X (clampScalar priv) pub`, returning `none` if `ss` is all zero and `rootKdf F rk ss.toList`
otherwise. -/
def createChain (F : ShaState → List (BitVec 8) → ShaState) (X : X25519Fn) (rk : RootKey)
    (pub priv : List.Vector (BitVec 8) 32) : Option (RootKey × ChainKey) :=
  let ss := X (clampScalar priv) pub
  if ss.toList = List.replicate 32 0#8 then none else some (rootKdf F rk ss.toList)

end Ratchet
end CryptoGames

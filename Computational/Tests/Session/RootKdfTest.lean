/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Tests.AEAD.HKDFTest -- shake: keep
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.RootKdfDefs -- shake: keep
public import Computational.Tests.AEAD.HMACTest -- shake: keep
public meta import Computational.Tests.AEAD.HKDFTest -- shake: keep
public meta import LibsignalBinary.Specifications.CryptoGames.Ratchet.RootKdfDefs -- shake: keep
public meta import Computational.Tests.AEAD.HMACTest -- shake: keep
public meta import LibsignalBinary.Specifications.CryptoGames.AEAD.HKDFDefs -- shake: keep

/-!
# Test Vectors for the Root KDF (`RootKey::create_chain`)

Interpreter `#guard` tests for `rootKdf` and `rootPRNG` (`RootKdfDefs.lean`) instantiated with
`sha256Compress`. Each vector checks `okm = HKDF-SHA256(salt = rk, ikm = ss, info = "WhisperRatchet", L = 64)`
against RFC 5869 reference outputs, splitting `okm[0..32]` as the new root key and `okm[32..64]` as
the new chain key.
-/

@[expose] public section

namespace CryptoGames.Ratchet.Tests

open CryptoGames.HMAC CryptoGames.HMAC.Tests CryptoGames.HKDF CryptoGames.HKDF.Tests
  CryptoGames.Ratchet

/-- Concatenates the 32-byte little-endian encodings of `(rootKey, chainKey)` from `rootKdf`. -/
def rootOkm (p : RootKey × ChainKey) : List (BitVec 8) :=
  keyToBytes32 p.1 ++ keyToBytes32 p.2

#guard whisperRatchetInfo == ascii "WhisperRatchet"
#guard whisperRatchetInfo.length == 14

def rk1 : RootKey := bytesToKey32 (bs (List.range 32))
def ss1 : List (BitVec 8) := bs (List.range' 0x20 32)

#guard hkdfExtract sha256Compress (rootSalt rk1) ss1 ==
  hex 32 0x62215de7bddcea7e2c4047ff6bb94f8d18262fc8b3f3648134bb7d44158ff84d
#guard rootOkm (rootKdf sha256Compress rk1 ss1) == hex 64
  0x62ffc77945c7aae74572869ac8a9522d96bc75a79cf3863ae7335004186255b32de7be8dc5a58c68bcb5db2e71cb88157ed10ab4f7ea97ba5606e49733da2b94
#guard (rootKdf sha256Compress rk1 ss1).1 ==
  bytesToKey32 (hex 32 0x62ffc77945c7aae74572869ac8a9522d96bc75a79cf3863ae7335004186255b3)
#guard (rootKdf sha256Compress rk1 ss1).2 ==
  bytesToKey32 (hex 32 0x2de7be8dc5a58c68bcb5db2e71cb88157ed10ab4f7ea97ba5606e49733da2b94)
#guard rootOkm (rootKdf sha256Compress rk1 ss1) ==
  hkdf sha256Compress (salt32 (bs (List.range 32))) ss1 whisperRatchetInfo 64
#guard (rootPRNG sha256Compress (fun l : List (BitVec 8) => l)).up rk1 ss1 ==
  rootKdf sha256Compress rk1 ss1

def rk2 : RootKey := bytesToKey32 (bs (List.range' 0x40 32))
def ss2 : List (BitVec 8) := bs (List.replicate 32 0xa0)

#guard hkdfExtract sha256Compress (rootSalt rk2) ss2 ==
  hex 32 0x73b688fe6f8b48aa0681b1bc6abb9b019c3ead3d6ee25adec2835b07bbf183da
#guard rootOkm (rootKdf sha256Compress rk2 ss2) == hex 64
  0x1deba315ba484d7636a2dd6bb33680bb856d5e0232978ed090b95b89898bf0439ab9a844d460464b631412b013633d8e986de150fe83907af99810007f9edea2

end CryptoGames.Ratchet.Tests

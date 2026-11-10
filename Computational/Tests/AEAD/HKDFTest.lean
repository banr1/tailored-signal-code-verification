/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Tests.AEAD.HMACTest
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.ChainDefs
public meta import Computational.Tests.AEAD.HMACTest -- shake: keep
public meta import LibsignalBinary.Specifications.CryptoGames.Ratchet.ChainDefs -- shake: keep
public meta import LibsignalBinary.Specifications.CryptoGames.AEAD.HKDFDefs -- shake: keep
public import LibsignalBinary.Specifications.CryptoGames.AEAD.LibsignalAead
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Construction
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Security
public import Computational.Proofs.CryptoGames.AEAD.HKDFProofDefs
public meta import Computational.Proofs.CryptoGames.AEAD.HKDFProofDefs -- shake: keep
public import LibsignalTestVectors.ChainKeyDerivation
public meta import LibsignalTestVectors.ChainKeyDerivation -- shake: keep

/-!
# HKDF-SHA256 and Ratchet Key-Derivation Tests

Interpreter `#guard` known-answer tests for `CryptoGames.HKDF` (`HKDFDefs.lean`) and
`CryptoGames.Ratchet` (`ChainDefs.lean`), instantiated with `sha256Compress` from `HMACTest.lean`.
Checks RFC 5869 Appendix A.1 and A.3 vectors, libsignal v0.105.4's `test_chain_key_derivation`
(`rust/protocol/src/ratchet/keys.rs`; the vectors are in
`third_party/libsignal/test-vectors/LibsignalTestVectors/ChainKeyDerivation.lean`), and
salted/unsalted `deriveMessageKeys` vectors.
-/

@[expose] public section

namespace CryptoGames.HKDF.Tests

open CryptoGames.HMAC CryptoGames.HMAC.Tests CryptoGames.HKDF CryptoGames.CBC CryptoGames.Ratchet

def salt32 (l : List (BitVec 8)) : Salt :=
  if h : l.length = 32 then some ⟨l, h⟩ else none

-- RFC 5869 Appendix A.1 (13-byte salt computed via `hmacWith`, L = 42).
def a1ikm : List (BitVec 8) := bs (List.replicate 22 0x0b)
def a1salt : List (BitVec 8) := bs (List.range 13)
def a1info : List (BitVec 8) := bs (List.range' 0xf0 10)
def a1prk : List (BitVec 8) := hmacWith sha256Compress a1salt a1ikm

#guard a1prk == hex 32 0x077709362c2e32df0ddc3f0dc47bba6390b6c73bb50f9c3122ec844ad7c2b3e5
#guard hkdfExpand sha256Compress a1prk a1info 42 ==
  hex 42 0x3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf34007208d5b887185865

-- RFC 5869 Appendix A.3 (absent salt defaults to 32 zero bytes, empty info, L = 42).
#guard hkdfExtract sha256Compress none a1ikm ==
  hex 32 0x19ef24a32c717b167f33a91d6f648bdf96596776afdb6377ac434c1c293ccb04
#guard hkdf sha256Compress none a1ikm [] 42 ==
  hex 42 0x8da4e775a563c18f715f802a063c5a31b8a11f5c5ee1879ec3454e5f3c738d2d9d201395faa4b61a96c8
#guard hkdfExtract sha256Compress (salt32 (bs (List.replicate 32 0))) a1ikm ==
  hkdfExtract sha256Compress none a1ikm

#guard whisperMessageKeys.length == 18
#guard whisperMessageKeys == ascii "WhisperMessageKeys"
#guard (hkdfBlocks sha256Compress a1prk a1info 3).length == 3
#guard (hkdf sha256Compress none a1ikm whisperMessageKeys 80).length == 80

-- libsignal `test_chain_key_derivation` (`ratchet/keys.rs:231-277`); the vectors are in
-- `LibsignalTestVectors.ChainKeyDerivation` (`third_party/libsignal/test-vectors/`).
def ck0 : ChainKey := bytesToKey32 (hex 32 LibsignalTestVectors.ChainKeyDerivation.seed)

#guard chainHmac sha256Compress ck0 chainKeySeed ==
  hex 32 LibsignalTestVectors.ChainKeyDerivation.nextChainKey
#guard (deriveMessageKeys sha256Compress none (chainHmac sha256Compress ck0 messageKeySeed)).1.1 ==
  bytesToKey32 (hex 32 LibsignalTestVectors.ChainKeyDerivation.cipherKey)
#guard (deriveMessageKeys sha256Compress none (chainHmac sha256Compress ck0 messageKeySeed)).2 ==
  bytesToKey32 (hex 32 LibsignalTestVectors.ChainKeyDerivation.macKey)
#guard (chainPRG sha256Compress (fun _ => none) 0).gen ck0 ==
  (bytesToKey32 (hex 32 LibsignalTestVectors.ChainKeyDerivation.nextChainKey),
    deriveMessageKeys sha256Compress none (chainHmac sha256Compress ck0 messageKeySeed))

/-- Reassembles the 80-byte HKDF output `cipherKey ‖ macKey ‖ iv` (little-endian) from `k`. -/
def okmOf (k : DerivedMessageKeys) : List (BitVec 8) :=
  keyToBytes32 k.1.1 ++ keyToBytes32 k.2 ++ (List.ofFn fun j : Fin 16 => k.1.2.extractLsb' (8 * j.val) 8)

#guard okmOf (deriveMessageKeys sha256Compress none (bs (List.range 32))) == hex 80
  0xb818cf662a1eaf9ded79df503b322cd36850a2f61db0703882cd0c5a73b4103e81f29940c87867fc2eb7f29f1719c398ea89c3dab6f7749b2e070cb3751001a224d3cb64e9b5119c24f1e7aee85280e9
#guard okmOf (deriveMessageKeys sha256Compress (salt32 (bs (List.range' 0x40 32))) (bs (List.range 32))) == hex 80
  0xafe50506aab1d909a8829051bcd5f12c8a88962b3ac0b5a538869844d4fb6d71ca00903c2d4d8a290377b379237e4aa7894d7ac0d9cd496f80319c52e7305428fa7e2e9479adaff22274dd696b0ac1e5
#guard okmOf (deriveMessageKeys sha256Compress (salt32 (bs (List.range' 0x40 32)))
    (hex 32 LibsignalTestVectors.ChainKeyDerivation.seed)) == hex 80
  0x55a03644f0555a89fe05a96a43a3f77d14d114a70deada67581d6f059d8f1081d062e13bc25af2c2d00082705953c5921de3200450492d949da35272addeba62ed26f2e25a1a8ef7781ffbc7deb0d06f
#guard chainHmac sha256Compress (bytesToKey32 (bs (List.range 32))) messageKeySeed ==
  hex 32 0x9b4c8120a4823a95f47cde17a244f4507244ee6e3957d1fab9fa29b44d3829b7
#guard chainHmac sha256Compress (bytesToKey32 (bs (List.range 32))) chainKeySeed ==
  hex 32 0x4304c22c84a53755ab08ead8d97a8d429be5efa480682d7ad1da27f73e1fbe1d

end CryptoGames.HKDF.Tests

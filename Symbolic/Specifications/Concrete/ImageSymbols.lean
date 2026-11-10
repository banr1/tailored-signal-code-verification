/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

/-!
# External Stub Symbols and Wire Constants

ELF symbol names for hooked cryptographic primitives in `signal-session` and wire-framing tag and
length constants.
-/

@[expose] public section

namespace DY.Libsignal.Refinement

abbrev StubSymbol := String

/-- Single-block SHA-256 compression `[state, block] ↦ state'` (`sha2::sha256::compress256`). -/
abbrev sha256CompressSymbol : StubSymbol := "sha2::sha256::compress256"

/-- AES-256-CBC encryption with PKCS#7 padding `[plaintext, key, iv] ↦ ciphertext`. -/
abbrev aesCbcEncryptSymbol : StubSymbol := "signal_crypto::aes_cbc::aes_256_cbc_encrypt"

/-- AES-256-CBC decryption with PKCS#7 unpadding `[ciphertext, key, iv] ↦ Option plaintext`. -/
abbrev aesCbcDecryptSymbol : StubSymbol := "signal_crypto::aes_cbc::aes_256_cbc_decrypt"

abbrev x25519AgreementSymbol : StubSymbol := "<x25519_dalek::x25519::StaticSecret>::diffie_hellman"

abbrev x25519PublicKeySymbol : StubSymbol :=
  "<x25519_dalek::x25519::PublicKey as core::convert::From<&x25519_dalek::x25519::StaticSecret>>::from"

end DY.Libsignal.Refinement

namespace DY.Libsignal.PQXDH.Refinement

open DY.Libsignal.Refinement (StubSymbol)

abbrev libcruxHmacSymbol : StubSymbol := "libcrux_hmac::hmac"

abbrev kyberEncapsSymbol : StubSymbol := "libcrux_ml_kem::mlkem1024::kyber::encapsulate"

abbrev kyberDecapsSymbol : StubSymbol := "libcrux_ml_kem::mlkem1024::kyber::decapsulate"

abbrev toEdwardsSymbol : StubSymbol := "<curve25519_dalek::montgomery::MontgomeryPoint>::to_edwards"

abbrev torsionFreeSymbol : StubSymbol :=
  "<curve25519_dalek::edwards::EdwardsPoint>::is_torsion_free"

/-- Leading wire tag byte for `PreKeySignalMessage`. -/
abbrev wirePrekeyTag : BitVec 8 := 3#8

/-- Byte length of the serialized `PublicBundle` blob read by `session_initiate`. -/
abbrev preKeyBundleByteLength : Nat := 1813

end DY.Libsignal.PQXDH.Refinement

namespace DY.Libsignal.TripleRatchet.Refinement

/-- Leading wire tag byte for `SignalMessage`. -/
abbrev wireWhisperTag : BitVec 8 := 2#8

end DY.Libsignal.TripleRatchet.Refinement

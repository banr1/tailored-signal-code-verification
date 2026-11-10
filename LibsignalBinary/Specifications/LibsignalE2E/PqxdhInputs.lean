/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalE2E.SchemeModel
public import LibsignalBinary.Specifications.LibsignalSpqrV1.MlKem
public import LibsignalBinary.Specifications.LibsignalAesCbc
public import LibsignalBinary.Specifications.LibsignalTripleRatchet

/-!
# PQXDH Parameters and Typed Inputs

**Trusted: the statement.** Abstract PQXDH cryptographic primitives (`PqxdhPrims`, `PEParams`),
initiator coin-tape layout (`initiateTapeLen`, `initiateKemCoins`), typed local identity and
pre-key bundle formats (`LocalIdentity`, `PreKeyBundleFields`), and `BitVec 8` / `UInt8`
conversions for `SignalPqxdh.Model`. See `Computational/docs/TRUSTED_BASE.md` and
`Computational/docs/DEVIATIONS.md` (DEV-PQ1, DEV-PQ2, DEV-PQ6).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalAesCbc (toLEBytes)
open CryptoVerification.LibsignalSpqrV1 (MlKem)

/-! ## The free primitives -/

/-- A SHA-512 chaining state: eight 64-bit words. -/
abbrev Sha512State := List.Vector (BitVec 64) 8

/-- **The PQXDH primitives, all abstract** (universally quantified in the statement).

**DEV-PQ1 (machine model): the machine code of SHA-512 compression, the Ed25519 curve core and Kyber
is not verified.** The extension of DEV-E8. `compress512`, the seven `curve25519_dalek` functions of
`pqxdhHookTable` and `kyber::{encapsulate, decapsulate}` are hooks over these free functions. Byte
strings are fixed-length vectors, so each hook is total and reads exactly its argument bytes. Why:
primitives are verified or assumed separately. Effect: out of scope: their compiled code is trusted
to match.

**DEV-PQ2 (libsignal): the KEM is Kyber1024 round 3, not FIPS 203 ML-KEM-1024.** libsignal v0.105.4's
`kem::KeyType::Kyber1024` calls `libcrux_ml_kem::mlkem1024::kyber` (the pre-standard round-3 variant,
`TAG_KYBER_1024 = 0x08`). `encaps` / `decaps` are abstract, so nothing here depends on which; the
security layer's KEM assumptions must be read as about Kyber1024 round 3. Effect: none here; a
disclosure for the security conjunct.

`decaps` is total: Kyber decapsulation never fails (implicit rejection returns a pseudorandom
secret), as libcrux's `decapsulate` returns `[u8; 32]`. -/
structure PqxdhPrims where
  /-- SHA-512 compression of one 128-byte block (FIPS 180-4 §6.4.2 on the big-endian words of the
  block; the state as eight words). As SHA-256's `F` (`CryptoGames/AEAD/HMACDefs.lean`), the
  block is a byte list; the hook and the model's `sha512Ref` (at `modelPrims`) pass only 128-byte
  blocks. -/
  F512 : Sha512State → List (BitVec 8) → Sha512State
  /-- `MontgomeryPoint::to_edwards`: u-coordinate and sign bit (0 or 1) to an `EdwardsPoint`, `none`
  if `u` is not the u-coordinate of a curve point. -/
  montToEd : List.Vector (BitVec 8) 32 → BitVec 8 → Option (List.Vector (BitVec 8) 160)
  /-- `EdwardsPoint::compress`. -/
  compress : List.Vector (BitVec 8) 160 → List.Vector (BitVec 8) 32
  /-- `<EdwardsPoint as Neg>::neg`. -/
  edNeg : List.Vector (BitVec 8) 160 → List.Vector (BitVec 8) 160
  /-- `EdwardsPoint::is_torsion_free`. -/
  isTorsionFree : List.Vector (BitVec 8) 160 → Bool
  /-- `vartime_double_scalar_mul_basepoint a A b = [a]A + [b]B`. -/
  dsmb : List.Vector (BitVec 8) 32 → List.Vector (BitVec 8) 160 → List.Vector (BitVec 8) 32 →
    List.Vector (BitVec 8) 160
  /-- `Scalar::from_bytes_mod_order` (32 bytes, reduced mod ℓ). -/
  scalarMod : List.Vector (BitVec 8) 32 → List.Vector (BitVec 8) 32
  /-- `Scalar::from_bytes_mod_order_wide` (64 bytes, reduced mod ℓ). -/
  scalarWide : List.Vector (BitVec 8) 64 → List.Vector (BitVec 8) 32
  /-- Kyber1024 encapsulation on the 1568-byte public key and 32 coin bytes: (ciphertext, shared
  secret). -/
  encaps : List.Vector (BitVec 8) 1568 → List.Vector (BitVec 8) 32 →
    List.Vector (BitVec 8) 1568 × List.Vector (BitVec 8) 32
  /-- Kyber1024 decapsulation on the 3168-byte secret key and the ciphertext: the shared secret. -/
  decaps : List.Vector (BitVec 8) 3168 → List.Vector (BitVec 8) 1568 → List.Vector (BitVec 8) 32
  /-- SPQR V1 ML-KEM-768 incremental primitives. -/
  K : MlKem

/-! ## Parameters -/

/-- **The parameters of the PQXDH statement**: the session layer's primitives (`C : Crypto`, the
primitives `absE` already uses) and the PQXDH primitives. All are universally quantified. -/
structure PEParams where
  /-- The session layer's primitives (SHA-256, AES-256, X25519). -/
  C : Crypto
  /-- The PQXDH primitives (SHA-512, the Ed25519 curve core, Kyber1024). -/
  Q : PqxdhPrims

/-! ## The coins of `init` -/

/-- **The coin length of `init`**: 192 bytes.

**DEV-PQ6 (machine model): the handshake's randomness is a tape of fixed shape.** The CLI draws its
randomness from the call's `coins` file, in order (`signal_session_coins_fill`, `cli/src/coins.rs`,
in-image code). Alice's `init` makes 34 draws: Alice's base key (one 32-byte fill), the Kyber
encapsulation coins (32 `next_u32` calls, 4 bytes each, of which `initialize_alice_session` keeps
the low byte, so coin `i` is byte `4 i` of those 128 bytes; `initiateKemCoins`), and Alice's first
ratchet key (one 32-byte fill): 192 bytes. Bob's pre-key `recv` takes 32 (his first ratchet key).
Why: an RNG is a source of fresh bytes, and the game fills the tape. Effect: none; the security
layer must draw the Kyber coins as `initiateKemCoins` of a uniform tape, which is uniform. -/
abbrev initiateTapeLen : Nat := 192

/-- The 32 Kyber coins `init` passes to `kyber::encapsulate` for the tape `t`: byte
`32 + 4 i` for `i < 32` (DEV-PQ6). -/
def initiateKemCoins (t : List.Vector (BitVec 8) initiateTapeLen) : List.Vector (BitVec 8) 32 :=
  List.Vector.ofFn fun i : Fin 32 => t.get ⟨32 + 4 * i.val, by unfold initiateTapeLen; omega⟩

/-! ## Inputs -/

/-- A Curve25519 public key as libsignal serializes it: type byte `0x05` and the 32 bytes. -/
def djbKey (k : List.Vector (BitVec 8) 32) : List (BitVec 8) := 0x05#8 :: k.toList

/-- A Kyber1024 public key as libsignal serializes it: type byte `0x08` (`kem::KeyType::Kyber1024`)
and the 1568 bytes. -/
def kyberKey (k : List.Vector (BitVec 8) 1568) : List (BitVec 8) := 0x08#8 :: k.toList

/-- **The caller's identity** (`me`). -/
structure LocalIdentity where
  /-- The identity private key (any 32 bytes: `PrivateKey::deserialize` clamps). -/
  idPriv : List.Vector (BitVec 8) 32
  /-- The registration id. -/
  regId : BitVec 32

/-- **A pre-key bundle**, typed so that its encoding `PreKeyBundleFields.bytes` is always well-formed: key
type bytes are `djbKey` / `kyberKey`'s, lengths are fixed, and `has_opk` is 0 or 1. -/
structure PreKeyBundleFields where
  /-- The peer's registration id. -/
  regId : BitVec 32
  /-- The one-time pre-key (id, X25519 public key), if any. -/
  opk : Option (BitVec 32 × List.Vector (BitVec 8) 32)
  /-- The signed pre-key id. -/
  spkId : BitVec 32
  /-- The signed pre-key (X25519 public key). -/
  spkPub : List.Vector (BitVec 8) 32
  /-- Its XEdDSA signature under the identity key. -/
  spkSig : List.Vector (BitVec 8) 64
  /-- The Kyber pre-key id. -/
  kpkId : BitVec 32
  /-- The Kyber1024 pre-key. -/
  kpkPub : List.Vector (BitVec 8) 1568
  /-- Its XEdDSA signature under the identity key. -/
  kpkSig : List.Vector (BitVec 8) 64
  /-- The peer's identity key (X25519 public key). -/
  idPub : List.Vector (BitVec 8) 32

/-- The 1813-byte serialization of a bundle: `reg_id has_opk opk_id opk_pub[33]
spk_id spk_pub[33] spk_sig[64] kpk_id kpk_pub[1569] kpk_sig[64] id_pub[33]`, integers LE; with no
one-time pre-key, `has_opk = 0` and its fields are zero. -/
def PreKeyBundleFields.bytes (b : PreKeyBundleFields) : List (BitVec 8) :=
  let opk : List (BitVec 8) := match b.opk with
    | some (i, k) => 1#8 :: toLEBytes 4 i ++ djbKey k
    | none => 0#8 :: List.replicate 37 0#8
  toLEBytes 4 b.regId ++ opk ++ toLEBytes 4 b.spkId ++ djbKey b.spkPub ++ b.spkSig.toList ++
    toLEBytes 4 b.kpkId ++ kyberKey b.kpkPub ++ b.kpkSig.toList ++ djbKey b.idPub

/-! ## Bytes as `UInt8` (for the link to the PQXDH model) -/

/-- A byte string of the PQXDH model (`Bytes := List UInt8`,
`LibsignalBinary/Specifications/SignalPqxdh/Model.lean`) as machine bytes (as
`Symbolic/Specifications/Refinement/Concretization.lean`: `.map UInt8.toBitVec`). -/
def ofU8 (bs : List UInt8) : List (BitVec 8) := bs.map UInt8.toBitVec

/-- Machine bytes as a byte string of the PQXDH model. Inverse of `ofU8` (`ofU8_toU8`, `toU8_ofU8`
in `LibsignalBinary/Proofs/E2E/PqxdhSpecTestsPure.lean`). -/
def toU8 (bs : List (BitVec 8)) : List UInt8 := bs.map UInt8.ofBitVec

/-- The first `n` bytes of `bs`, zero-padded, as a vector. -/
def fitVec (n : Nat) (bs : List (BitVec 8)) : List.Vector (BitVec 8) n :=
  ⟨(bs ++ List.replicate n 0#8).take n, by simp⟩

end CryptoVerification.E2E

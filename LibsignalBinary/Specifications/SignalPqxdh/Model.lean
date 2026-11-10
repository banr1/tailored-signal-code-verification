/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

/-!
# Pure Byte-Level Specification of the Signal PQXDH Handshake and First Message

**Trusted: the statement.** Machine-free functional model of the PQXDH key agreement
(`Model.initiateKeys`, `Model.acceptKeys`) and first-message key schedule (`Model.initiate`,
`Model.accept`) of `libsignal-protocol` v0.105.4 over byte lists (`Bytes := List UInt8`),
parameterized by `Primitives`, together with reference cryptographic constructions, the structural
and algebraic well-formedness bundle `WellFormedPrimitivesδ` (without perfect KEM decapsulation
correctness, DEV-PQ21), and functional correctness `PqxdhCorrect`. See
`Computational/docs/TRUSTED_BASE.md`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh

/-- Byte string representation used across `SignalPqxdh`. -/
abbrev Bytes := List UInt8

/-- 96-byte PQXDH handshake output (`HandshakeKeys`, `pqxdh.rs:51-68`). -/
structure DRKey where
  rootKey  : Bytes -- 32 bytes (okm[0..32])
  chainKey : Bytes -- 32 bytes (okm[32..64])
  pqrKey   : Bytes -- 32 bytes (okm[64..96])
  deriving DecidableEq, Repr, Inhabited

/-- 80-byte per-message keys (`MessageKeys`, `ratchet/keys.rs:91-97`). -/
structure MessageKeys where
  cipherKey : Bytes -- 32 bytes (okm[0..32], AES-256-CBC key)
  macKey    : Bytes -- 32 bytes (okm[32..64], HMAC-SHA256 key)
  iv        : Bytes -- 16 bytes (okm[64..80], AES-256-CBC IV)
  deriving DecidableEq, Repr, Inhabited

/-- Key-type tag byte `0x05` of serialized Curve25519 (DJB) public keys in `libsignal-core`. -/
def TAG_EC_DJB     : UInt8 := 0x05
/-- Key-type tag byte `0x08` of serialized Kyber1024 public keys in `libsignal-protocol`. -/
def TAG_KYBER_1024 : UInt8 := 0x08

/-- 32-byte `0xFF` domain separator prefix for X25519 in X3DH/PQXDH (`pqxdh.rs:200, 337`). -/
def F_X25519 : Bytes := List.replicate 32 0xFF

/-- 46-byte ASCII HKDF info string (`pqxdh.rs:28-30, 74, 82`). -/
def INFO_PQXDH : Bytes :=
  "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024".toUTF8.toList

/-- 14-byte ASCII HKDF info string (`ratchet/keys.rs:207`). -/
def INFO_RATCHET : Bytes :=
  "WhisperRatchet".toUTF8.toList

/-- 18-byte ASCII HKDF info string (`ratchet/keys.rs:108`). -/
def INFO_MSG_KEYS : Bytes :=
  "WhisperMessageKeys".toUTF8.toList

/-- Serializes a 32-byte X25519 public key into 33 bytes: `0x05 ‖ pk`. -/
def encodeEC (pk : Bytes) : Bytes := TAG_EC_DJB :: pk

/-- Byte length of a Kyber1024 public key (`rust/protocol/src/kem.rs`). -/
def kyberPkLen : Nat := 1568

/-- Byte length of a Kyber1024 ciphertext (`rust/protocol/src/kem.rs`). -/
def kyberCtLen : Nat := 1568

/-- Serializes a `kyberPkLen`-byte Kyber1024 public key into 1569 bytes: `0x08 ‖ pk`. -/
def encodeKEM (pk : Bytes) : Bytes := TAG_KYBER_1024 :: pk

/-- The abstract cryptographic primitives that parameterize the `Model.*` protocol functions: one
    field per operation used by the handshake and the 5-step first-message key schedule, plus the
    block functions and curve arithmetic used by the reference constructions below. -/
structure Primitives where
  /-- RFC 7748 X25519 scalar multiplication `x25519(sk, pk)` (32B → 32B → 32B). -/
  x25519          : Bytes → Bytes → Bytes
  /-- RFC 7748 X25519 basepoint multiplication `x25519Base(sk)` (32B → 32B). -/
  x25519Base      : Bytes → Bytes
  /-- Canonical Curve25519 ephemeral public-key check (`PublicKey::is_canonical`, `pqxdh.rs:328`). -/
  isCanonical     : Bytes → Bool
  /-- XEdDSA public-key derivation `sigPkGen(sk32)` (equals `x25519Base` in real single-key setup). -/
  sigPkGen        : Bytes → Bytes
  /-- XEdDSA deterministic/randomized signing `sigSign(sk32, msg, rand64) = sig64`. -/
  sigSign         : Bytes → Bytes → Bytes → Bytes
  /-- XEdDSA signature verification `sigVerify(ikPk32, msg, sig64)`. -/
  sigVerify       : Bytes → Bytes → Bytes → Bool
  /-- SHA-512 hash / compression primitive (`sha2::sha512::compress512`, 64-byte digest). -/
  sha512          : Bytes → Bytes
  /-- Curve25519 scalar multiplication mod ℓ (`<Scalar as Mul>::mul`: 32B × 32B → 32B). -/
  scalarMul       : Bytes → Bytes → Bytes
  /-- Curve25519 scalar addition mod ℓ (`<Scalar as Add>::add`: 32B × 32B → 32B). -/
  scalarAdd       : Bytes → Bytes → Bytes
  /-- Curve25519 scalar reduction mod ℓ (`Scalar::from_bytes_mod_order`: 32B → 32B). -/
  scalarFromBytesModOrder : Bytes → Bytes
  /-- Curve25519 wide scalar reduction mod ℓ (`Scalar::from_bytes_mod_order_wide`: 64B → 32B). -/
  scalarFromWide  : Bytes → Bytes
  /-- Birational map from Montgomery u-coordinate (32B) and sign bit (`0` or `1`) to 160B `EdwardsPoint`
      (`MontgomeryPoint::to_edwards`: `32B → UInt8 → Option Bytes`). -/
  montToEd        : Bytes → UInt8 → Option Bytes
  /-- Edwards point small-subgroup torsion check (`EdwardsPoint::is_torsion_free`: 160B → Bool). -/
  isTorsionFree   : Bytes → Bool
  /-- Edwards point negation (`<EdwardsPoint as Neg>::neg`: 160B → 160B). -/
  edNeg           : Bytes → Bytes
  /-- Edwards double-scalar basepoint multiplication `[h](-A) + [s]B`
      (`EdwardsPoint::vartime_double_scalar_mul_basepoint`: 32B × 160B × 32B → 160B). -/
  doubleScalarMulBasepoint : Bytes → Bytes → Bytes → Bytes
  /-- Edwards point compression to 32-byte `CompressedEdwardsY`
      (`EdwardsPoint::compress`: 160B → 32B). -/
  compress        : Bytes → Bytes
  /-- Kyber1024 key generation from 64-byte seed `kemKeyGen(seed64) = (pk1568, sk3168)`. -/
  kemKeyGen       : Bytes → (Bytes × Bytes)
  /-- Kyber1024 deterministic encapsulation `kemEncaps(pqPk1568, coins32) = some (ss32, ct1568)`. -/
  kemEncaps       : Bytes → Bytes → Option (Bytes × Bytes)
  /-- Kyber1024 decapsulation `kemDecaps(pqSk3168, ct1568) = some ss32`. -/
  kemDecaps       : Bytes → Bytes → Option Bytes
  /-- PQXDH handshake KDF: `HKDF-SHA256(salt = None, ikm = secrets).expand(INFO_PQXDH, 96)`. -/
  hkdfDerive96    : Bytes → DRKey
  /-- Epoch-1 Root KDF (`RootKey::create_chain`, `ratchet/keys.rs:199-218`):
      `HKDF-SHA256(salt = Some rk0, ikm = dhRatchet, info = "WhisperRatchet", 64) = (rk1, ck1_0)`. -/
  rootCreateChain : Bytes → Bytes → (Bytes × Bytes)
  /-- Epoch-1 Chain KDF seed (`ChainKey::message_keys`, `ratchet/keys.rs:172-182`):
      `HMAC-SHA256(key = ck, [0x01])` (32B message-key seed `mk_seed`). -/
  chainKdfSeed    : Bytes → Bytes
  /-- Epoch-1 Chain KDF advance (`ChainKey::next_chain_key`, `ratchet/keys.rs:165-170`):
      `HMAC-SHA256(key = ck, [0x02])` (32B next chain key `ck1_1`). -/
  chainKdfNext    : Bytes → Bytes
  /-- SPQR initiator bootstrap + first-message step (`spqr::initial_state(A2B, pqr0)` + `spqr::send`):
      `spqrInitSend(pqr0, spqrCoins) = some (pqrStateA, spqrSalt?, pqRatchetMsg)`. -/
  spqrInitSend    : Bytes → Bytes → Option (Bytes × Option Bytes × Bytes)
  /-- SPQR recipient bootstrap + first-message step (`spqr::initial_state(B2A, pqr0)` + `spqr::recv`):
      `spqrInitRecv(pqr0, pqRatchetMsg) = some (pqrStateB, spqrSalt?)`. -/
  spqrInitRecv    : Bytes → Bytes → Option (Bytes × Option Bytes)
  /-- Message keys KDF (`MessageKeys::derive_keys`, `ratchet/keys.rs:100-118`):
      `HKDF-SHA256(salt = spqrSalt?, ikm = mkSeed, info = "WhisperMessageKeys", 80)` split 32/32/16. -/
  deriveMsgKeys   : Bytes → Option Bytes → MessageKeys
  /-- First-message AEAD encryption (`AES-256-CBC` + 8-byte truncated `HMAC-SHA256` over `ad`). -/
  aeadEnc         : MessageKeys → Bytes → Bytes → Bytes
  /-- First-message AEAD decryption (`AES-256-CBC` + 8-byte truncated `HMAC-SHA256` over `ad`). -/
  aeadDec         : MessageKeys → Bytes → Bytes → Option Bytes
  /-- Prime-order subgroup cofactor projection `pow8` (`gexp_div_8` in `PQXDH.m4.ocv:268`). -/
  pow8            : Bytes → Bytes
  /-- Decisional Diffie-Hellman predicate on `(X, Y, Z)` in the prime-order subgroup. -/
  isValidDhTriple : Bytes → Bytes → Bytes → Bool
  /-- SHA-256 64-byte compression block function (`sha2::sha256::compress256`: 32B × 64B → 32B). -/
  sha256Compress  : Bytes → Bytes → Bytes
  /-- SHA-512 128-byte compression block function
      (`sha2::sha512::compress512`: 64B × 128B → 64B). -/
  sha512Compress  : Bytes → Bytes → Bytes
  /-- AES-256 16-byte single-block encryption
      (`aes::soft::fixslice64::aes256_encrypt8`: 32B × 16B → 16B). -/
  aesEncBlock     : Bytes → Bytes → Bytes
  /-- AES-256 16-byte single-block decryption
      (`aes::soft::fixslice64::aes256_decrypt8`: 32B × 16B → 16B). -/
  aesDecBlock     : Bytes → Bytes → Bytes

/-- Assembles the 160-byte (no OPK) or 192-byte (with OPK) `secrets` buffer (`pqxdh.rs:202-231`). -/
def buildSecrets (dh1 dh2 dh3 : Bytes) (dh4? : Option Bytes) (ss : Bytes) : Bytes :=
  match dh4? with
  | none     => F_X25519 ++ dh1 ++ dh2 ++ dh3 ++ ss
  | some dh4 => F_X25519 ++ dh1 ++ dh2 ++ dh3 ++ dh4 ++ ss

/-- Protobuf base-128 varint (`prost::encoding::encode_varint`): 7 bits per byte, least significant
    group first, high bit set on every byte but the last. -/
def pbVarint (n : Nat) : Bytes :=
  go n n
where
  /-- Structural on the fuel `f` (so the kernel reduces it); `f = n` is always enough. -/
  go : Nat → Nat → Bytes
    | 0, n => [n.toUInt8]
    | f + 1, n => if n < 128 then [n.toUInt8] else (n % 128 + 128).toUInt8 :: go f (n / 128)

/-- Protobuf `bytes` field `tag` (wire type 2): key byte `8·tag + 2`, length varint, contents. -/
def pbBytesField (tag : Nat) (b : Bytes) : Bytes :=
  (8 * tag + 2).toUInt8 :: (pbVarint b.length ++ b)

/-- First-message associated data authenticated by the 8-byte MAC in `SignalMessage::compute_mac`
    (`protocol.rs:214-235`): `ser(ikA) ‖ ser(ikB)`, then the version byte `0x44` and the prost
    encoding of the inner `SignalMessage` header fields: `ratchet_key = 1` (`encodeEC ephAPk`),
    `counter = 2` and `previous_counter = 3` (both `0` for the first message) and, if non-empty,
    `pq_ratchet = 5`. The first `firstMsgHdrLen` bytes are the fields that precede the ciphertext;
    `aeadMacInput` inserts the ciphertext field (`ciphertext = 4`) there, so the MAC input has
    prost's tag order `1, 2, 3, 4, 5`. `addresses = 6` is omitted (DEV-PQ31). -/
def firstMsgAD (ikA ikB ephAPk pqRatchetMsg : Bytes) : Bytes :=
  encodeEC ikA ++ encodeEC ikB ++ [0x44] ++ pbBytesField 1 (encodeEC ephAPk) ++
    [0x10, 0x00, 0x18, 0x00] ++
    (if pqRatchetMsg.isEmpty then [] else pbBytesField 5 pqRatchetMsg)

/-- Bob's prekey bundle as received on the wire by Alice (`PreKeyBundle`).
    Only the single wire identity public key `ikB` (32B) exists on the wire. -/
structure PreKeyBundleInput where
  ikB      : Bytes                  -- 32B Bob wire identity public key (used for both sigVerify and DH2)
  spkId    : UInt32
  spkB     : Bytes                  -- 32B signed EC prekey public key
  spkSig   : Bytes                  -- 64B XEdDSA signature over `encodeEC spkB`
  opkB?    : Option (UInt32 × Bytes) -- optional (opkId, 32B one-time EC prekey public key)
  pqspkId  : UInt32
  pqspkB   : Bytes                  -- `kyberPkLen`-byte Kyber1024 public key
  pqspkSig : Bytes                  -- 64B XEdDSA signature over `encodeKEM pqspkB`
  deriving DecidableEq, Repr, Inhabited

/-- Handshake-only wire header output by `Model.initiateKeys` (also the header type used by the
    PQXDH games in `Computational/Specifications/Pqxdh/Game.lean`). -/
structure HandshakeHdr where
  ikAPk   : Bytes        -- 32B Alice wire identity public key
  ekAPk   : Bytes        -- 32B Alice ephemeral `base_key`
  spkId   : UInt32
  opkId?  : Option UInt32
  pqspkId : UInt32
  kemCt   : Bytes        -- `kyberCtLen`-byte `kyber_ciphertext`
  deriving DecidableEq, Repr, Inhabited

/-- Full first-message wire packet output by `Model.initiate` (`PreKeySignalMessage`). -/
structure PreKeyMsg where
  hdr          : HandshakeHdr
  ephAPk       : Bytes -- 32B Alice Epoch-1 sending ratchet public key (`SignalMessage.ratchet_key`)
  pqRatchetMsg : Bytes -- SPQR initial token (`SignalMessage.pq_ratchet`)
  aeadCt       : Bytes -- encrypted inner `SignalMessage` body + 8-byte MAC tag
  deriving DecidableEq, Repr, Inhabited

/-- Alice's inputs to handshake-only `Model.initiateKeys` (and full `Model.initiate`).
    Only Alice's single wire identity key `(ikASk, ikAPk)` is present. -/
structure InitiateKeysInput where
  ikASk       : Bytes -- 32B Alice identity secret scalar
  ikAPk       : Bytes -- 32B Alice wire identity public key
  ekASk       : Bytes -- 32B freshly sampled PQXDH ephemeral scalar (`base_key`)
  kemCoins    : Bytes -- 32B freshly sampled Kyber1024 encapsulation randomness
  trustedPeer : Bool  -- result of `is_trusted_identity` store hook
  bundle      : PreKeyBundleInput
  deriving DecidableEq, Repr, Inhabited

/-- Alice's inputs to full first-message `Model.initiate` (`process_prekey_bundle` + first send). -/
structure InitiateInput extends InitiateKeysInput where
  ephASk    : Bytes -- 32B freshly sampled Epoch-1 sending ratchet scalar (`ratchet.rs:77`)
  spqrCoins : Bytes -- 32B freshly sampled SPQR send randomness (`triple_ratchet.rs:97`)
  plaintext : Bytes -- initial message payload
  deriving DecidableEq, Repr, Inhabited

/-- Bob's inputs to handshake-only `Model.acceptKeys` (`<Pqxdh as Handshake>::accept`). -/
structure AcceptKeysInput where
  ikBSk       : Bytes        -- 32B Bob identity secret scalar
  ikBPk       : Bytes        -- 32B Bob wire identity public key
  spkBSk      : Bytes        -- 32B Bob signed EC prekey secret scalar
  spkBPk      : Bytes        -- 32B Bob signed EC prekey public key
  opkBSk?     : Option Bytes -- 32B Bob one-time EC prekey secret scalar (if `hdr.opkId? = some id`)
  pqspkBSk    : Bytes        -- 3168B Bob Kyber1024 secret key
  pqspkBPk    : Bytes        -- `kyberPkLen`-byte Bob Kyber1024 public key
  trustedPeer : Bool         -- result of `is_trusted_identity` store hook
  replayOk    : Bool         -- result of `mark_kyber_pre_key_used(pqspkId, spkId, ekAPk)`
  hdr         : HandshakeHdr
  deriving DecidableEq, Repr, Inhabited

/-- Bob's inputs to full first-message `Model.accept` (`process_prekey` + `message_decrypt_prekey`). -/
structure AcceptInput where
  keysInp : AcceptKeysInput
  msg     : PreKeyMsg
  deriving DecidableEq, Repr, Inhabited

/-- Check that an optional 32-byte X25519 shared secret (`dh4?`) is non-zero when present
    (`PrivateKey::calculate_agreement` in `rust/core/src/curve.rs`). -/
def dhOptNonZero (dh? : Option Bytes) : Bool :=
  match dh? with
  | none => true
  | some dh => dh != List.replicate 32 0

/-- Core PQXDH handshake initiation (`<Pqxdh as Handshake>::initiate` / `pqxdh_initiate`,
    `pqxdh.rs:97-205, 194-237`):
    verifies bundle signatures against the single wire key `bundle.ikB`, encapsulates against
    `pqspkB`, computes the 3 or 4 X25519 legs, and derives the 96-byte `DRKey`. -/
def Model.initiateKeys (P : Primitives) (inp : InitiateKeysInput) :
    Option (DRKey × HandshakeHdr) := do
  guard inp.trustedPeer
  -- 1. Verify XEdDSA signature on `SPK_B.serialize()` (`0x05 ‖ spkB`) under wire key `bundle.ikB`
  guard (P.sigVerify inp.bundle.ikB (encodeEC inp.bundle.spkB) inp.bundle.spkSig)
  -- 2. Verify XEdDSA signature on `PQSPK_B.serialize()` (`0x08 ‖ pqspkB`) under wire key `bundle.ikB`
  guard (P.sigVerify inp.bundle.ikB (encodeKEM inp.bundle.pqspkB) inp.bundle.pqspkSig)
  -- 3. Encapsulate against `PQSPK_B` (`pqxdh.rs:226-231`)
  let (ss, kemCt) ← P.kemEncaps inp.bundle.pqspkB inp.kemCoins
  -- 4. Ephemeral public key and 3 or 4 X25519 DH legs (`pqxdh.rs:198-224`);
  --    each `PrivateKey::calculate_agreement` (`rust/core/src/curve.rs`) rejects all-zero shared secrets.
  let ekAPk := P.x25519Base inp.ekASk
  let dh1   := P.x25519 inp.ikASk inp.bundle.spkB
  guard (dh1 != List.replicate 32 0)
  let dh2   := P.x25519 inp.ekASk inp.bundle.ikB
  guard (dh2 != List.replicate 32 0)
  let dh3   := P.x25519 inp.ekASk inp.bundle.spkB
  guard (dh3 != List.replicate 32 0)
  let dh4?  := inp.bundle.opkB?.map (fun (_, opkPk) => P.x25519 inp.ekASk opkPk)
  guard (dhOptNonZero dh4?)
  -- 5. Derive 96-byte `DRKey = (rootKey, chainKey, pqrKey)` (`pqxdh.rs:233-236`)
  let secrets := buildSecrets dh1 dh2 dh3 dh4? ss
  let drKey   := P.hkdfDerive96 secrets
  let hdr : HandshakeHdr := {
    ikAPk   := inp.ikAPk
    ekAPk   := ekAPk
    spkId   := inp.bundle.spkId
    opkId?  := inp.bundle.opkB?.map Prod.fst
    pqspkId := inp.bundle.pqspkId
    kemCt   := kemCt
  }
  some (drKey, hdr)

/-- Core PQXDH handshake acceptance (`<Pqxdh as Handshake>::accept` / `pqxdh_accept`,
    `pqxdh.rs:208-291, 326-376`, with `mark_kyber_pre_key_used` at `pqxdh.rs:246-254` and
    `storage/inmem.rs:247-265`):
    checks `is_canonical(ekAPk)`, computes 3 or 4 DH legs, decapsulates `kemCt`, and derives `DRKey`. -/
def Model.acceptKeys (P : Primitives) (inp : AcceptKeysInput) : Option DRKey := do
  guard inp.trustedPeer
  guard inp.replayOk
  -- 0. Wire EC public key 32-byte length checks (`curve.rs:95-115`)
  guard (inp.hdr.ikAPk.length == 32)
  guard (inp.hdr.ekAPk.length == 32)
  -- 1. Check `their_ephemeral_key.is_canonical()` first (`pqxdh.rs:328-333`)
  guard (P.isCanonical inp.hdr.ekAPk)
  -- 2. Compute 3 or 4 X25519 DH legs (`pqxdh.rs:339-366`);
  --    each `PrivateKey::calculate_agreement` (`rust/core/src/curve.rs`) rejects all-zero shared secrets.
  let dh1  := P.x25519 inp.spkBSk inp.hdr.ikAPk
  guard (dh1 != List.replicate 32 0)
  let dh2  := P.x25519 inp.ikBSk  inp.hdr.ekAPk
  guard (dh2 != List.replicate 32 0)
  let dh3  := P.x25519 inp.spkBSk inp.hdr.ekAPk
  guard (dh3 != List.replicate 32 0)
  let dh4? ← match inp.hdr.opkId?, inp.opkBSk? with
    | none,   none       => some none
    | some _, some opkSk => some (some (P.x25519 opkSk inp.hdr.ekAPk))
    | _,      _          => none
  guard (dhOptNonZero dh4?)
  -- 3. Check `Ciphertext` wire length (`rust/protocol/src/kem.rs`, which rejects any slice whose
  --    length differs from `kyberCtLen`) and decapsulate under `PQSPK_B.sk` (`pqxdh.rs:368-373`)
  guard (inp.hdr.kemCt.length == kyberCtLen)
  let ss ← P.kemDecaps inp.pqspkBSk inp.hdr.kemCt
  -- 4. Assemble `[0xFFu8; 32]` (`pqxdh.rs:337`) + DH legs + `ss` and derive 96-byte `DRKey` (`pqxdh.rs:374-376`)
  let secrets := buildSecrets dh1 dh2 dh3 dh4? ss
  some (P.hkdfDerive96 secrets)

/-- Faithful first-message initiation (5-step key schedule; `session.rs:200-285`,
    `ratchet.rs:67-112`, `triple_ratchet.rs:86-135`): runs `Model.initiateKeys` to obtain
    `drKey = (rk0, ck0, pqr0)`, then executes
    `rootCreateChain(rk0, DH(ephA, spkB)) → chainKdf → spqrInitSend → deriveMsgKeys → aeadEnc`. -/
def Model.initiate (P : Primitives) (inp : InitiateInput) :
    Option (DRKey × Bytes × Bytes × PreKeyMsg) := do
  let (drKey, hdr) ← Model.initiateKeys P inp.toInitiateKeysInput
  -- 6. Epoch-1 Root KDF: `root_key.create_chain(SPK_B.pk, eph_A¹.sk)` (`ratchet.rs:77-81`, `curve.rs`)
  let ephAPk    := P.x25519Base inp.ephASk
  let dhRatchet := P.x25519 inp.ephASk inp.bundle.spkB
  guard (dhRatchet != List.replicate 32 0)
  let (rk1, ck1_0) := P.rootCreateChain drKey.rootKey dhRatchet
  -- 7. Epoch-1 Chain KDF: `ChainKey::message_keys` & `next_chain_key` (`ratchet/keys.rs:165-182`)
  let mkSeed := P.chainKdfSeed ck1_0
  let ck1_1  := P.chainKdfNext ck1_0
  -- 8. SPQR initial state & first send (`ratchet.rs:83-89`, `triple_ratchet.rs:97`)
  let (_pqrStA, spqrSalt?, pqRatchetMsg) ← P.spqrInitSend drKey.pqrKey inp.spqrCoins
  -- 9. Derive 80B `MessageKeys` with `optional_salt = spqrSalt?` (`ratchet/keys.rs:100-118`)
  let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
  -- 10. Encrypt inner `SignalMessage` under `deriveMessageKeys` and `firstMsgAD`
  let ad     := firstMsgAD inp.ikAPk inp.bundle.ikB ephAPk pqRatchetMsg
  let aeadCt := P.aeadEnc deriveMessageKeys ad inp.plaintext
  let msg : PreKeyMsg := {
    hdr          := hdr
    ephAPk       := ephAPk
    pqRatchetMsg := pqRatchetMsg
    aeadCt       := aeadCt
  }
  some (drKey, rk1, ck1_1, msg)

/-- Faithful first-message acceptance (5-step key schedule; `session.rs:39-198`,
    `ratchet.rs:118-172`, `triple_ratchet.rs:215-298`, `session_management.rs:207-285`):
    runs `Model.acceptKeys` to obtain `drKey = (rk0, ck0, pqr0)`, then executes
    `rootCreateChain(rk0, DH(spkB, ephA)) → chainKdf → spqrInitRecv → deriveMsgKeys → aeadDec`. -/
def Model.accept (P : Primitives) (inp : AcceptInput) :
    Option (DRKey × Bytes × Bytes × Bytes) := do
  guard (inp.keysInp.hdr == inp.msg.hdr)
  let drKey ← Model.acceptKeys P inp.keysInp
  guard (inp.msg.ephAPk.length == 32)
  -- 5. Epoch-1 Root KDF receiving half-step: `create_chain(eph_A¹.pk, SPK_B.sk)` (`double_ratchet.rs:285`, `curve.rs`)
  let dhRatchet := P.x25519 inp.keysInp.spkBSk inp.msg.ephAPk
  guard (dhRatchet != List.replicate 32 0)
  let (rk1, ck1_0) := P.rootCreateChain drKey.rootKey dhRatchet
  -- 6. Epoch-1 Chain KDF: `ChainKey::message_keys` & `next_chain_key`
  let mkSeed := P.chainKdfSeed ck1_0
  let ck1_1  := P.chainKdfNext ck1_0
  -- 7. SPQR initial state & first receive (`ratchet.rs:146-152`, `triple_ratchet.rs:241-251`)
  let (_pqrStB, spqrSalt?) ← P.spqrInitRecv drKey.pqrKey inp.msg.pqRatchetMsg
  -- 8. Derive 80B `MessageKeys` with `optional_salt = spqrSalt?`
  let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
  -- 9. Verify 8-byte MAC and decrypt inner `SignalMessage`
  let ad := firstMsgAD inp.msg.hdr.ikAPk inp.keysInp.ikBPk inp.msg.ephAPk inp.msg.pqRatchetMsg
  let pt ← P.aeadDec deriveMessageKeys ad inp.msg.aeadCt
  some (drKey, rk1, ck1_1, pt)

/-- Functional reference specification of Signal's XEdDSA signature verification
    (`curve25519::verify_signature_for_multipart_message`,
    `rust/core/src/curve/curve25519.rs:119-160`). The range check is on
    `sig[63] &&& 0x60` because the sign bit (bit 7) is extracted and cleared before
    `(s[31] & 0xE0) == 0` is tested. -/
def xeddsaVerifyRef (P : Primitives) (pk m sig : Bytes) : Bool :=
  if pk.length == 32 && sig.length == 64 && ((sig.getD 63 0 &&& 0x60) == 0) then
    let signBit : UInt8 := (sig.getD 63 0 &&& 0x80) >>> 7
    match P.montToEd pk signBit with
    | none => false
    | some edPk =>
      let capA := P.compress edPk
      let minusCapA := P.edNeg edPk
      let capR := sig.take 32
      let sRaw := sig.drop 32
      let sClamped := sRaw.take 31 ++ [sRaw.getD 31 0 &&& 0x7F]
      let h := P.scalarFromWide (P.sha512 (capR ++ capA ++ m))
      let sScalar := P.scalarFromBytesModOrder sClamped
      let capRCheck := P.compress (P.doubleScalarMulBasepoint h minusCapA sScalar)
      capRCheck == capR
  else
    false

/-- Constant-time little-endian range check `scalar_is_in_range` from
    `rust/core/src/curve.rs:176-186`:
    returns `true` iff bit 7 of byte 31 is `0` (`(pk.getD 31 0 &&& 0x80) == 0`) and the
    little-endian 255-bit integer `pk` is strictly less than `2^255 - 19`, i.e., not
    `pk[0] >= 0xED ∧ pk[1..31] == [0xFF; 30] ∧ (pk[31] & 0x7F) == 0x7F`. -/
def scalarIsInRange (pk : Bytes) : Bool :=
  ((pk.getD 31 0 &&& 0x80) == 0) &&
    !(pk.getD 0 0 >= 0xED &&
      (pk.drop 1).take 30 == List.replicate 30 0xFF &&
      (pk.getD 31 0 &&& 0x7F) == 0x7F)

/-- Functional reference specification of `<libsignal_core::curve::PublicKey>::is_canonical`
    (`rust/core/src/curve.rs:156-191`). -/
def isCanonicalRef (P : Primitives) (pk : Bytes) : Bool :=
  if pk.length == 32 && ((pk.getD 31 0 &&& 0x80) == 0) && scalarIsInRange pk then
    match P.montToEd pk 0 with
    | some edPt => P.isTorsionFree edPt
    | none => false
  else
    false

/-- Pad or truncate a `Bytes` list to `n` bytes (reference helper). -/
def fitBytesRef (n : Nat) (bs : Bytes) : Bytes :=
  bs.take n ++ List.replicate (n - bs.length) 0

@[simp]
theorem fitBytesRef_length (n : Nat) (bs : Bytes) : (fitBytesRef n bs).length = n := by
  simp [fitBytesRef]
  omega

/-- RFC 7748 32-byte scalar clamping (`x25519_dalek::StaticSecret::from` / `clamp_integer`):
    clears the low 3 bits of byte 0 (`&&& 0xF8`),
    clears bit 7 and sets bit 6 of byte 31 (`(b &&& 0x7F) ||| 0x40`), and preserves bytes 1..30. -/
def clampScalar25519 (sk : Bytes) : Bytes :=
  let s := fitBytesRef 32 sk
  (s.take 1).map (fun b => b &&& 0xF8) ++
    (s.drop 1).take 30 ++
    ((s.drop 31).take 1).map (fun b => (b &&& 0x7F) ||| 0x40)

/-- FIPS 180-4 §5.3.3 SHA-256 initial 32-byte chaining state (`H^(0)`). -/
def sha256InitState : Bytes :=
  [ 0x6a, 0x09, 0xe6, 0x67, 0xbb, 0x67, 0xae, 0x85,
    0x3c, 0x6e, 0xf3, 0x72, 0xa5, 0x4f, 0xf5, 0x3a,
    0x51, 0x0e, 0x52, 0x7f, 0x9b, 0x05, 0x68, 0x8c,
    0x1f, 0x83, 0xd9, 0xab, 0x5b, 0xe0, 0xcd, 0x19 ]

/-- FIPS 180-4 §5.3.5 SHA-512 initial 64-byte chaining state (`H^(0)`). -/
def sha512InitState : Bytes :=
  [ 0x6a, 0x09, 0xe6, 0x67, 0xf3, 0xbc, 0xc9, 0x08,
    0xbb, 0x67, 0xae, 0x85, 0x84, 0xca, 0xa7, 0x3b,
    0x3c, 0x6e, 0xf3, 0x72, 0xfe, 0x94, 0xf8, 0x2b,
    0xa5, 0x4f, 0xf5, 0x3a, 0x5f, 0x1d, 0x36, 0xf1,
    0x51, 0x0e, 0x52, 0x7f, 0xad, 0xe6, 0x82, 0xd1,
    0x9b, 0x05, 0x68, 0x8c, 0x2b, 0x3e, 0x6c, 0x1f,
    0x1f, 0x83, 0xd9, 0xab, 0xfb, 0x41, 0xbd, 0x6b,
    0x5b, 0xe0, 0xcd, 0x19, 0x13, 0x7e, 0x21, 0x79 ]

/-- Big-endian 64-bit bit-length encoding (`8 * byteLen`). -/
def encodeBitLen64BE (byteLen : Nat) : Bytes :=
  let bitLen : UInt64 := byteLen.toUInt64 * 8
  [ ((bitLen >>> 56) &&& 0xFF).toUInt8,
    ((bitLen >>> 48) &&& 0xFF).toUInt8,
    ((bitLen >>> 40) &&& 0xFF).toUInt8,
    ((bitLen >>> 32) &&& 0xFF).toUInt8,
    ((bitLen >>> 24) &&& 0xFF).toUInt8,
    ((bitLen >>> 16) &&& 0xFF).toUInt8,
    ((bitLen >>>  8) &&& 0xFF).toUInt8,
    ( bitLen         &&& 0xFF).toUInt8 ]

/-- Big-endian 128-bit bit-length encoding (`8 * byteLen`) for SHA-512. -/
def encodeBitLen128BE (byteLen : Nat) : Bytes :=
  List.replicate 8 0 ++ encodeBitLen64BE byteLen

/-- FIPS 180-4 §5.1.1 SHA-256 message padding to a multiple of 64 bytes. -/
def sha256Pad (msg : Bytes) : Bytes :=
  let rem := (msg.length + 9) % 64
  let zeroPadLen := if rem == 0 then 0 else 64 - rem
  msg ++ [0x80] ++ List.replicate zeroPadLen 0 ++ encodeBitLen64BE msg.length

/-- FIPS 180-4 §5.1.2 SHA-512 message padding to a multiple of 128 bytes. -/
def sha512Pad (msg : Bytes) : Bytes :=
  let rem := (msg.length + 17) % 128
  let zeroPadLen := if rem == 0 then 0 else 128 - rem
  msg ++ [0x80] ++ List.replicate zeroPadLen 0 ++ encodeBitLen128BE msg.length

/-- Splits `bs` into fixed-size chunks of `blockSize` bytes. -/
def chunkBlocks (blockSize : Nat) (bs : Bytes) : List Bytes :=
  let numBlocks := bs.length / blockSize
  (List.range numBlocks).map (fun i => (bs.drop (i * blockSize)).take blockSize)

/-- Single 64-byte block SHA-256 compression step (normalizing state to 32 bytes). -/
def sha256Step (P : Primitives) (state32 block64 : Bytes) : Bytes :=
  fitBytesRef 32 (P.sha256Compress (fitBytesRef 32 state32) block64)

/-- Single 128-byte block SHA-512 compression step (normalizing state to 64 bytes). -/
def sha512Step (P : Primitives) (state64 block128 : Bytes) : Bytes :=
  fitBytesRef 64 (P.sha512Compress (fitBytesRef 64 state64) block128)

/-- Merkle-Damgård SHA-256 reference construction over `P.sha256Compress` (`sha2::Sha256`). -/
def sha256Ref (P : Primitives) (msg : Bytes) : Bytes :=
  let blocks := chunkBlocks 64 (sha256Pad msg)
  fitBytesRef 32 (blocks.foldl (sha256Step P) sha256InitState)

/-- Merkle-Damgård SHA-512 reference construction over `P.sha512Compress` (`sha2::Sha512`). -/
def sha512Ref (P : Primitives) (msg : Bytes) : Bytes :=
  let blocks := chunkBlocks 128 (sha512Pad msg)
  fitBytesRef 64 (blocks.foldl (sha512Step P) sha512InitState)

/-- Bytewise XOR of two byte lists (`List.zipWith (· ^^^ ·)`). -/
def xorBytes (a b : Bytes) : Bytes :=
  List.zipWith (· ^^^ ·) a b

/-- RFC 2104 HMAC-SHA256 reference construction built from `sha256Ref P`. -/
def hmacSha256Ref (P : Primitives) (key msg : Bytes) : Bytes :=
  let key' := if key.length > 64 then sha256Ref P key else key
  let kPad := fitBytesRef 64 key'
  let ipad := xorBytes kPad (List.replicate 64 0x36)
  let opad := xorBytes kPad (List.replicate 64 0x5c)
  sha256Ref P (opad ++ sha256Ref P (ipad ++ msg))

/-- RFC 5869 `HKDF-Extract(salt?, ikm)` using `hmacSha256Ref P` (`hkdf::Hkdf::<Sha256>::new`). -/
def hkdfExtractRef (P : Primitives) (salt? : Option Bytes) (ikm : Bytes) : Bytes :=
  let salt := match salt? with
    | some s => s
    | none   => List.replicate 32 0
  hmacSha256Ref P salt ikm

/-- RFC 5869 `HKDF-Expand(prk, info, 96)` into three 32-byte blocks (`T(1), T(2), T(3)`). -/
def hkdfExpand96Ref (P : Primitives) (prk info : Bytes) : DRKey :=
  let t1 := hmacSha256Ref P prk (info ++ [0x01])
  let t2 := hmacSha256Ref P prk (t1 ++ info ++ [0x02])
  let t3 := hmacSha256Ref P prk (t2 ++ info ++ [0x03])
  { rootKey := t1, chainKey := t2, pqrKey := t3 }

/-- Reference PQXDH handshake KDF (`pqxdh.rs:70-92`):
    `HKDF-SHA256(salt = None, ikm = secrets).expand(INFO_PQXDH, 96)`. -/
def hkdfDerive96Ref (P : Primitives) (secrets : Bytes) : DRKey :=
  hkdfExpand96Ref P (hkdfExtractRef P none secrets) INFO_PQXDH

/-- Reference Epoch-1 Root KDF (`RootKey::create_chain`, `ratchet/keys.rs:199-218`):
    `HKDF-SHA256(salt = Some rk0, ikm = dhRatchet).expand(INFO_RATCHET, 64)`. -/
def rootCreateChainRef (P : Primitives) (rk dhRatchet : Bytes) : (Bytes × Bytes) :=
  let prk := hkdfExtractRef P (some rk) dhRatchet
  let t1  := hmacSha256Ref P prk (INFO_RATCHET ++ [0x01])
  let t2  := hmacSha256Ref P prk (t1 ++ INFO_RATCHET ++ [0x02])
  (t1, t2)

/-- Reference Epoch-1 Chain KDF seed (`ChainKey::message_keys`, `ratchet/keys.rs:172-182`):
    `HMAC-SHA256(key = ck, [0x01])`. -/
def chainKdfSeedRef (P : Primitives) (ck : Bytes) : Bytes :=
  hmacSha256Ref P ck [0x01]

/-- Reference Epoch-1 Chain KDF step (`ChainKey::next_chain_key`, `ratchet/keys.rs:165-170`):
    `HMAC-SHA256(key = ck, [0x02])`. -/
def chainKdfNextRef (P : Primitives) (ck : Bytes) : Bytes :=
  hmacSha256Ref P ck [0x02]

/-- Reference `MessageKeys::derive_keys` (`ratchet/keys.rs:100-118`):
    `HKDF-SHA256(salt = spqrSalt?, ikm = mkSeed).expand(INFO_MSG_KEYS, 80)` split `32 / 32 / 16`. -/
def deriveMsgKeysRef (P : Primitives) (mkSeed : Bytes) (spqrSalt? : Option Bytes) : MessageKeys :=
  let prk := hkdfExtractRef P spqrSalt? mkSeed
  let t1  := hmacSha256Ref P prk (INFO_MSG_KEYS ++ [0x01])
  let t2  := hmacSha256Ref P prk (t1 ++ INFO_MSG_KEYS ++ [0x02])
  let t3  := hmacSha256Ref P prk (t2 ++ INFO_MSG_KEYS ++ [0x03])
  { cipherKey := t1, macKey := t2, iv := t3.take 16 }

/-- PKCS#7 padding to a 16-byte block boundary (`block_padding::Pkcs7`, `crypto.rs:14-35`). -/
def pkcs7Pad16 (pt : Bytes) : Bytes :=
  let padM1 := 15 - (pt.length % 16)
  let padLen := padM1 + 1
  pt ++ List.replicate padLen padLen.toUInt8

/-- PKCS#7 unpadding on 16-byte blocks (`block_padding::Pkcs7`, `crypto.rs:37-61`). -/
def pkcs7Unpad16 (padded : Bytes) : Option Bytes :=
  match padded.reverse with
  | [] => none
  | padByte :: revRest =>
    let padLen := padByte.toNat
    if padLen >= 1 && padLen <= 16 && padded.length % 16 == 0 &&
       revRest.take (padLen - 1) == List.replicate (padLen - 1) padByte then
      some (revRest.drop (padLen - 1)).reverse
    else
      none

/-- Splits a byte list into 16-byte blocks. -/
def toBlocks16 (bs : Bytes) : List Bytes :=
  if bs.length >= 16 then
    bs.take 16 :: toBlocks16 (bs.drop 16)
  else
    []
termination_by bs.length
decreasing_by
  simp_wf
  omega

/-- Concatenates 16-byte blocks back into a flat byte list. -/
def fromBlocks16 (blks : List Bytes) : Bytes :=
  blks.foldr (· ++ ·) []

/-- Encrypts 16-byte blocks in AES-256-CBC mode using an AES block encryptor. -/
def cbcEncBlocksWith (aesEnc : Bytes → Bytes → Bytes) (key iv : Bytes) : List Bytes → List Bytes
  | [] => []
  | blk :: rest =>
    let ctBlk := fitBytesRef 16 (aesEnc (fitBytesRef 32 key) (xorBytes (fitBytesRef 16 blk) (fitBytesRef 16 iv)))
    ctBlk :: cbcEncBlocksWith aesEnc key ctBlk rest

/-- Decrypts 16-byte blocks in AES-256-CBC mode using an AES block decryptor. -/
def cbcDecBlocksWith (aesDec : Bytes → Bytes → Bytes) (key iv : Bytes) : List Bytes → List Bytes
  | [] => []
  | ctBlk :: rest =>
    let ptBlk := xorBytes (fitBytesRef 16 (aesDec (fitBytesRef 32 key) (fitBytesRef 16 ctBlk))) (fitBytesRef 16 iv)
    ptBlk :: cbcDecBlocksWith aesDec key (fitBytesRef 16 ctBlk) rest

/-- Encrypts 16-byte blocks in AES-256-CBC mode using `P.aesEncBlock`. -/
abbrev cbcEncBlocks (P : Primitives) (key iv : Bytes) (blks : List Bytes) : List Bytes :=
  cbcEncBlocksWith P.aesEncBlock key iv blks

/-- Decrypts 16-byte blocks in AES-256-CBC mode using `P.aesDecBlock`. -/
abbrev cbcDecBlocks (P : Primitives) (key iv : Bytes) (blks : List Bytes) : List Bytes :=
  cbcDecBlocksWith P.aesDecBlock key iv blks

/-- Reference AES-256-CBC encryption with PKCS#7 padding (`libsignal_protocol::crypto::aes_256_cbc_encrypt`,
    `crypto.rs:14-35`, backed by `P.aesEncBlock`). -/
def aes256CbcEncRef (P : Primitives) (key iv pt : Bytes) : Bytes :=
  fromBlocks16 (cbcEncBlocks P key iv (toBlocks16 (pkcs7Pad16 pt)))

/-- Reference AES-256-CBC decryption with PKCS#7 unpadding (`libsignal_protocol::crypto::aes_256_cbc_decrypt`,
    `crypto.rs:37-61`, backed by `P.aesDecBlock`). -/
def aes256CbcDecRef (P : Primitives) (key iv ct : Bytes) : Option Bytes :=
  if ct.length >= 16 && ct.length % 16 == 0 then
    pkcs7Unpad16 (fromBlocks16 (cbcDecBlocks P key iv (toBlocks16 ct)))
  else
    none

/-- Length of the part of `firstMsgAD` before `pq_ratchet` when the three EC keys have 32 bytes:
    `ser(ikA)` and `ser(ikB)` (33 each), `0x44` (1), `ratchet_key` (`0x0a 0x21` and 33 bytes),
    `counter` and `previous_counter` (`0x10 0x00 0x18 0x00`). `Model.acceptKeys` and `Model.accept`
    reject received EC keys of any other length. -/
def firstMsgHdrLen : Nat := 106

/-- HMAC input of the first-message AEAD: the prost-serialized `SignalMessage` that `compute_mac`
    authenticates (DEV-PQ31). The ciphertext, as the length-delimited field `ciphertext = 4`
    (`0x22 ‖ varint |ct| ‖ ct`), is placed after the first `firstMsgHdrLen` bytes of `ad`
    (`ser(ikA) ‖ ser(ikB) ‖ 0x44 ‖` fields 1-3) and before the rest of `ad` (field 5 if present). -/
def aeadMacInput (ad ct : Bytes) : Bytes :=
  ad.take firstMsgHdrLen ++ pbBytesField 4 ct ++ ad.drop firstMsgHdrLen

/-- Reference first-message AEAD encryption (`session_cipher.rs:125-175`, `protocol.rs:78-125`):
    AES-256-CBC-PKCS#7 ciphertext followed by the 8-byte truncated
    `HMAC-SHA256(macKey, aeadMacInput ad ct)` tag. -/
def aes256CbcHmacEncRef (P : Primitives) (mk : MessageKeys) (ad pt : Bytes) : Bytes :=
  let ct  := aes256CbcEncRef P mk.cipherKey mk.iv pt
  let mac := (hmacSha256Ref P mk.macKey (aeadMacInput ad ct)).take 8
  ct ++ mac

/-- Reference first-message AEAD decryption (`session_cipher.rs:290-360`, `protocol.rs:236-250`):
    verifies the 8-byte trailing `HMAC-SHA256(macKey, aeadMacInput ad ct)` tag and runs
    `aes256CbcDecRef`. -/
def aes256CbcHmacDecRef (P : Primitives) (mk : MessageKeys) (ad ctAndTag : Bytes) : Option Bytes :=
  if ctAndTag.length >= 24 then
    let ctLen := ctAndTag.length - 8
    let ct    := ctAndTag.take ctLen
    let tag   := ctAndTag.drop ctLen
    let expectedTag := (hmacSha256Ref P mk.macKey (aeadMacInput ad ct)).take 8
    if tag == expectedTag then
      aes256CbcDecRef P mk.cipherKey mk.iv ct
    else
      none
  else
    none

/-- `pk` is an X25519 input on which scalar multiplication is determined by the
    scalar's residue modulo `±ℓ`: either a canonical key (`isCanonicalRef`: 32 bytes, high bit
    clear, `u < p`, `montToEd` succeeds and torsion-free, hence a curve point of order exactly `ℓ`)
    or a point whose `pow8` projection agrees with that of an honest base-point output (so, by
    `x25519_pow8_congr`, X25519 on `pk` behaves like X25519 on a prime-subgroup curve point).
    Twist points are excluded: they satisfy neither disjunct. -/
def onCurveKey (P : Primitives) (pk : Bytes) : Prop :=
  P.isCanonical pk = true ∨ ∃ e, e.length = 32 ∧ P.pow8 pk = P.pow8 (P.x25519Base e)

/-- Reference DDH predicate, gated on `onCurveKey`: `(X, Y, Z)` is a DH triple iff both `X` and
    `Y` satisfy `onCurveKey P` and some scalar `a` with `X = x25519Base a` has
    `pow8 Z = pow8 (x25519 a Y)`, or the same holds with `X` and `Y` swapped. Requiring
    `onCurveKey P X` and `onCurveKey P Y` rejects quadratic-twist and small-order points in either
    key slot, so the DDH oracle in `GapDH`, `GapDhWithSign` and `GapSigEufCma` never answers
    cross-curve queries on `8k₀ mod ℓ'` (on `onCurveKey` inputs, `x25519_congr_of_base_eq` makes
    `x25519 a Y` independent of the choice of scalar `a` with `x25519Base a = X`). Law
    `isValidDhTriple_eq_ref` pins `P.isValidDhTriple` to this predicate. -/
def isValidDhTripleRef (P : Primitives) (X Y Z : Bytes) : Prop :=
  onCurveKey P X ∧ onCurveKey P Y ∧
    ((∃ a, X = P.x25519Base a ∧ P.pow8 Z = P.pow8 (P.x25519 a Y)) ∨
      (∃ b, Y = P.x25519Base b ∧ P.pow8 Z = P.pow8 (P.x25519 b X)))

/-- Kyber-1024 structural well-formedness laws on `P : Primitives` without perfect decapsulation
    correctness (`kem_corr`, DEV-PQ21): encapsulation/decapsulation totality on well-sized inputs
    and output byte lengths. -/
structure WellFormedKemδ (P : Primitives) : Prop where
  kemDecaps_isSome       : ∀ sk ct, sk.length = 3168 → ct.length = 1568 →
                             (P.kemDecaps sk ct).isSome = true
  /-- ML-KEM-1024 encapsulation is total on well-sized inputs: `process_prekey_bundle` checks
      only `pqspkB.len == 1568` and then calls `libcrux_ml_kem::mlkem1024::kyber::encapsulate`
      with 32 coin bytes and no failure branch. -/
  kemEncaps_isSome       : ∀ pk r, pk.length = 1568 → r.length = 32 →
                             (P.kemEncaps pk r).isSome = true
  kemKeyGen_valid        : ∀ seed,
                             (P.kemKeyGen seed).1.length = kyberPkLen ∧
                             (P.kemKeyGen seed).2.length = 3168
  kemEncaps_len          : ∀ pk r ss ct,
                             P.kemEncaps pk r = some (ss, ct) →
                             ss.length = 32 ∧ ct.length = 1568
  kemDecaps_len          : ∀ sk ct ss,
                             P.kemDecaps sk ct = some ss →
                             ss.length = 32

/-- SPQR initial-step well-formedness laws on `P : Primitives`: initiator totality, initiator/responder
    salt agreement, and received salt length bound. -/
structure WellFormedSpqr (P : Primitives) : Prop where
  spqrInitSend_some      : ∀ k r, (P.spqrInitSend k r).isSome = true
  spqr_corr              : ∀ pqrKey coins stA salt? pqMsg,
                             P.spqrInitSend pqrKey coins = some (stA, salt?, pqMsg) →
                             ∃ stB, P.spqrInitRecv pqrKey pqMsg = some (stB, salt?)
  /-- `spqr::recv` yields a salt of at most 32 bytes when present (DEV-LS25). `spqr` 1.6.0:
      `MessageKey = Option<Vec<u8>>` (`src/lib.rs:42`); keys are `[u8; 32]` (`src/chain.rs:229`),
      except `recv_key(0, 0) = Ok(vec![])` (`src/chain.rs:416-418`), returned unfiltered as
      `Some([])` on `recv`'s `Ordering::Greater` path (`src/lib.rs:406`); so lengths are 0 or 32.
      With HMAC's key zero-padding, `deriveMsgKeysRef` then depends only on the 32-byte effective
      salt (`effectiveHkdfSaltBytes`, `Computational/Proofs/SignalPqxdh/TwoKeyAndAuthStatements.lean`).
      The send side follows by `spqr_corr`. A hypothesis of `CryptoWellFormedPrimitivesδ`: it narrows
      the `P` covered; real `spqr` (0 / 32) and SPQR off (`none`) satisfy it. -/
  spqrInitRecv_salt_len  : ∀ pqrKey pqMsg stB salt,
                             P.spqrInitRecv pqrKey pqMsg = some (stB, some salt) →
                             salt.length ≤ 32

/-- RFC 7748 X25519, canonicality, cofactor-8 subgroup projection (`pow8`), and DDH-oracle
    consistency laws on `P : Primitives`.

    **Satisfiability requirement.** Every law below is required to hold for real
    RFC 7748 X25519 on ALL 32-byte inputs, including twist points and small-order points (an
    adversary may supply any 32 bytes as a public key). A real-X25519 witness: let `pow8 Q := [c]Q`
    where `c` is the CRT idempotent with `c ≡ 1 (mod ℓ)`, `c ≡ 0 (mod 8)` on the curve and
    `c' ≡ 1 (mod ℓ')`, `c' ≡ 0 (mod 4)` on the twist, all torsion points mapping to `0^32`
    (encoded as a 32-byte u-coordinate); let `isValidDhTriple X Y Z` hold iff
    `isValidDhTripleRef X Y Z` (law `isValidDhTriple_eq_ref`). `canon_x25519` and
    `ddh_consistent_left` carry hypotheses (canonical input, `onCurveKey`) because their
    unrestricted forms do not hold for this witness (and for real X25519 under any choice of
    `pow8`/`isValidDhTriple`). -/
structure WellFormedDh (P : Primitives) : Prop where
  x25519_clamp           : ∀ sk pk, P.x25519 (clampScalar25519 sk) pk = P.x25519 sk pk
  x25519Base_clamp       : ∀ sk, P.x25519Base (clampScalar25519 sk) = P.x25519Base sk
  /-- Clamped X25519 scalars are non-zero mod ℓ (`2^252 + 27742317777372353535851937790883648493`),
      and `x25519Base b` lies in the prime-order subgroup of Curve25519 (order ℓ), so scalar
      multiplication by a clamped scalar `a` never yields the identity / order-2 point `u = 0`
      (all-zero 32-byte shared secret in `rust/core/src/curve.rs` `PrivateKey::calculate_agreement`). -/
  x25519_base_ne_zero    : ∀ a b, a.length = 32 → b.length = 32 →
                             P.x25519 a (P.x25519Base b) ≠ List.replicate 32 0
  /-- On Curve25519, every clamped 32-byte scalar `s = clampScalar25519 a` is a multiple of 8
      (`s = 8 * k` with `2^251 ≤ s < 2^255 < 8 * ℓ`, so `gcd(k, ℓ) = 1`), which annihilates the
      cofactor-8 torsion subgroup (`ℤ/8ℤ` on the curve, `ℤ/4ℤ` on the twist) and is invertible on
      the prime-order-`ℓ` subgroup; hence `[s] pk` produces the all-zero `u = 0` output iff `[8] pk`
      is the identity, independently of the clamped scalar `a`. -/
  x25519_zero_iff        : ∀ a1 a2 pk, a1.length = 32 → a2.length = 32 → pk.length = 32 →
                             (P.x25519 a1 pk = List.replicate 32 0 ↔
                              P.x25519 a2 pk = List.replicate 32 0)
  x25519_comm            : ∀ a b, P.x25519 a (P.x25519Base b) = P.x25519 b (P.x25519Base a)
  canon_base             : ∀ e, P.isCanonical (P.x25519Base e) = true
  /-- Scalar multiplication preserves canonicity of canonical inputs. The unconditional form
      `∀ a pk, P.isCanonical (P.x25519 a pk) = true` fails for real X25519: `pk = 0^32` (and any
      small-order point) gives output `0^32`, which is not torsion-free, and twist points give
      twist outputs, which fail `montToEd`/`isTorsionFree`. Holds for real X25519: a canonical `pk`
      has order exactly `ℓ`; the clamped scalar is `s = 8k` with `0 < k < 2^252 < ℓ`, so `[s]pk` has
      order `ℓ` and is again canonical. -/
  canon_x25519           : ∀ a pk, a.length = 32 → P.isCanonical pk = true →
                             P.isCanonical (P.x25519 a pk) = true
  pow8_idemp             : ∀ p, P.pow8 (P.pow8 p) = P.pow8 p
  pow8_x25519_comm       : ∀ a b, P.pow8 (P.x25519 a (P.x25519Base b)) = P.pow8 (P.x25519 b (P.x25519Base a))
  ddh_consistent         : ∀ a b z,
                             P.isValidDhTriple (P.x25519Base a) (P.x25519Base b) z = true ↔
                               P.pow8 z = P.pow8 (P.x25519 a (P.x25519Base b))
  /-- Restricted to `onCurveKey P pk`. The unrestricted
      form over ALL `pk` contradicts `x25519_pow8_congr` at real X25519: take clamped
      `s1 = 2^254`, `s2 = 2^254 + 8δ` with `δ = ℓ - 2^252`, so `s1 + s2 = 8ℓ`. Then
      `x25519Base s1 = x25519Base s2` (since `s2 ≡ -s1 (mod ℓ)`), so the left-hand side
      `isValidDhTriple (x25519Base s1) pk z` is the same for both scalars, while on the twist point
      `u = 2` (order divisible by the large twist prime `ℓ'`) `x25519 s1 pk ≠ x25519 s2 pk` and
      `pow8` separates them, so the right-hand sides differ. On `onCurveKey` inputs both scalars
      agree (`x25519_congr_of_base_eq`), and the law holds for the witness in the structure
      docstring. -/
  ddh_consistent_left    : ∀ a pk z, onCurveKey P pk →
                             (P.isValidDhTriple (P.x25519Base a) pk z = true ↔
                               P.pow8 z = P.pow8 (P.x25519 a pk))
  ddh_symm               : ∀ pk1 pk2 z,
                             P.isValidDhTriple pk1 pk2 z = P.isValidDhTriple pk2 pk1 z
  /-- The DDH oracle is the reference predicate `isValidDhTripleRef` on every input (including
      rejecting non-`onCurveKey` inputs such as twist and small-order points). Without this law the
      oracle is constrained only on `(base, base)` and `(base, onCurveKey)` inputs and by symmetry,
      so a `P` whose oracle answers `(x25519Base a, Y, Z)` for twist points `Y` with bits of
      `8k₀ mod ℓ'` would satisfy the other laws and make `GapDH` / `GapDhWithSign` easy. `ddh_symm`
      follows from this law, and `ddh_consistent` from it and `x25519_comm`. -/
  isValidDhTriple_eq_ref : ∀ X Y Z, P.isValidDhTriple X Y Z = true ↔ isValidDhTripleRef P X Y Z
  /-- Restricted to 32-byte public keys. The unrestricted form fails for `pqxdhModelPrims`:
      `x25519 a pk` fits `pk` to 32 bytes (`u8Vec 32`), so a 33-byte `p' = x25519Base 0 ++ [0]`
      has `x25519 a p' = x25519 a (x25519Base 0) ≠ x25519 a 0^32`, preventing `pow8 p'` from
      mapping either to `pow8 0^32` (by `x25519_pow8_congr` + `x25519_inj_pow8`) or to
      `pow8 (x25519Base 0)` (by `pow8_base_len`). For 32-byte `pk1, pk2`, equal `pow8` projections
      mean `pk1` and `pk2` differ only by cofactor torsion, which clamping (`8k`) annihilates. -/
  x25519_pow8_congr      : ∀ a pk1 pk2, pk1.length = 32 → pk2.length = 32 →
                             P.pow8 pk1 = P.pow8 pk2 → P.x25519 a pk1 = P.x25519 a pk2
  /-- (True for real X25519.) Scalars with
      equal base-point outputs agree on every `onCurveKey` input. Equal `x25519Base` outputs give
      `s1 ≡ ±s2 (mod ℓ)`. For a canonical `pk` (order `ℓ`), `u([s]Q) = u([-s]Q)`, so the outputs
      agree. For the torsion disjunct `pow8 pk = pow8 (x25519Base e)`, `x25519_pow8_congr` reduces
      both sides to `x25519 sᵢ (x25519Base e) = x25519 e (x25519Base sᵢ)`, which agree. The
      `onCurveKey` hypothesis is necessary: on the twist point `u = 2` the pair `s1 = 2^254`,
      `s2 = 2^254 + 8(ℓ - 2^252)` has equal base outputs but different outputs (the twist subgroup
      has order `ℓ' ≠ ℓ`). -/
  x25519_congr_of_base_eq : ∀ a1 a2 pk, a1.length = 32 → a2.length = 32 → onCurveKey P pk →
                             P.x25519Base a1 = P.x25519Base a2 → P.x25519 a1 pk = P.x25519 a2 pk
  canon_pow8_inj         : ∀ pk1 pk2,
                             P.isCanonical pk1 = true →
                             P.isCanonical pk2 = true →
                             P.pow8 pk1 = P.pow8 pk2 →
                             pk1 = pk2
  x25519_len             : ∀ k p, (P.x25519 k p).length = 32
  x25519Base_len         : ∀ k, (P.x25519Base k).length = 32
  pow8_len               : ∀ p, (P.pow8 p).length = 32
  isCanonical_eq_isCanonicalRef : ∀ pk, P.isCanonical pk = isCanonicalRef P pk

/-- XEdDSA signing/verification, single-key public-key identity (`sigPkGen = x25519Base`),
    SHA-512 reference link, and Curve25519 scalar and Edwards-point byte lengths on `P : Primitives`. -/
structure WellFormedSig (P : Primitives) : Prop where
  sha512Compress_len           : ∀ st blk, (P.sha512Compress st blk).length = 64
  sha512_eq_ref                : ∀ m, P.sha512 m = sha512Ref P m
  sha512_len                   : ∀ m, (P.sha512 m).length = 64
  sigPkGen_eq_x25519Base       : P.sigPkGen = P.x25519Base
  scalarMul_len                : ∀ a b, (P.scalarMul a b).length = 32
  scalarAdd_len                : ∀ a b, (P.scalarAdd a b).length = 32
  scalarFromBytesModOrder_len  : ∀ b, (P.scalarFromBytesModOrder b).length = 32
  scalarFromWide_len           : ∀ b, (P.scalarFromWide b).length = 32
  montToEd_len                 : ∀ u s pt, P.montToEd u s = some pt → pt.length = 160
  edNeg_len                    : ∀ pt, (P.edNeg pt).length = 160
  doubleScalarMulBasepoint_len : ∀ h a s, (P.doubleScalarMulBasepoint h a s).length = 160
  compress_len                 : ∀ pt, (P.compress pt).length = 32
  sigVerify_eq_xeddsaVerifyRef : ∀ pk m sig, P.sigVerify pk m sig = xeddsaVerifyRef P pk m sig
  sig_corr                     : ∀ sk msg r, P.sigVerify (P.sigPkGen sk) msg (P.sigSign sk msg r) = true

/-- SHA-256 compression block length and reference-construction equations for the handshake,
    Epoch-1 root, chain, and message-key HKDF/HMAC derivations on `P : Primitives`. -/
structure WellFormedKdf (P : Primitives) : Prop where
  sha256Compress_len     : ∀ st blk, (P.sha256Compress st blk).length = 32
  hkdfDerive96_eq_ref    : ∀ secrets, P.hkdfDerive96 secrets = hkdfDerive96Ref P secrets
  rootCreateChain_eq_ref : ∀ rk dh, P.rootCreateChain rk dh = rootCreateChainRef P rk dh
  chainKdfSeed_eq_ref    : ∀ ck, P.chainKdfSeed ck = chainKdfSeedRef P ck
  chainKdfNext_eq_ref    : ∀ ck, P.chainKdfNext ck = chainKdfNextRef P ck
  deriveMsgKeys_eq_ref   : ∀ mkSeed salt?, P.deriveMsgKeys mkSeed salt? = deriveMsgKeysRef P mkSeed salt?

/-- AES-256 block-cipher lengths/roundtrip and first-message CBC-HMAC AEAD reference links and
    decryption roundtrip on `P : Primitives`. -/
structure WellFormedAead (P : Primitives) : Prop where
  aesEncBlock_len        : ∀ k blk, (P.aesEncBlock k blk).length = 16
  aesDecBlock_len        : ∀ k blk, (P.aesDecBlock k blk).length = 16
  aesBlock_corr          : ∀ k blk, k.length = 32 → blk.length = 16 →
                             P.aesDecBlock k (P.aesEncBlock k blk) = blk
  aeadEnc_eq_ref         : ∀ mk ad pt, P.aeadEnc mk ad pt = aes256CbcHmacEncRef P mk ad pt
  aeadDec_eq_ref         : ∀ mk ad ct, P.aeadDec mk ad ct = aes256CbcHmacDecRef P mk ad ct
  aead_corr              : ∀ mk ad pt, P.aeadDec mk ad (P.aeadEnc mk ad pt) = some pt

/-- Structural and algebraic well-formedness of `P : Primitives` without the perfect KEM
    decapsulation correctness law `kem_corr` (DEV-PQ21), assembled from the six component bundles
    `WellFormedKemδ`, `WellFormedSpqr`, `WellFormedDh`, `WellFormedSig`, `WellFormedKdf`, and
    `WellFormedAead`. KEM correctness is assumed separately via `KemDeltaCorrect P δ`
    (`Computational/Specifications/Assumptions/KemCorrect.lean`), while proof-side
    `WellFormedPrimitives` (`LibsignalBinary/Proofs/SpecLemmas/SignalPqxdh/ModelProofDefs.lean`)
    extends `WellFormedPrimitivesδ` with `kem_corr`. -/
structure WellFormedPrimitivesδ (P : Primitives) : Prop
    extends WellFormedKemδ P, WellFormedSpqr P, WellFormedDh P,
      WellFormedSig P, WellFormedKdf P, WellFormedAead P

/-- Functional correctness of PQXDH: for every honest run (authentic bundle and signatures,
    trusted peers, no replay, KEM and SPQR succeed), `Model.initiateKeys`/`Model.acceptKeys` and
    `Model.initiate`/`Model.accept` all succeed with identical `(drKey, rk1, ck1_1)` and Bob
    recovers Alice's plaintext. The correctness conjunct of the PQXDH headline statement
    (`Computational/Specifications/Pqxdh/Security/Headline.lean`). -/
def PqxdhCorrect (P : Primitives) : Prop :=
  ∀ (initInp : InitiateInput) (accKeysInp : AcceptKeysInput) (ss kemCt : Bytes),
    initInp.trustedPeer = true →
    accKeysInp.trustedPeer = true →
    accKeysInp.replayOk = true →
    P.sigVerify initInp.bundle.ikB (encodeEC initInp.bundle.spkB) initInp.bundle.spkSig = true →
    P.sigVerify initInp.bundle.ikB (encodeKEM initInp.bundle.pqspkB) initInp.bundle.pqspkSig = true →
    initInp.ikAPk = P.x25519Base initInp.ikASk →
    (initInp.bundle.ikB = P.x25519Base accKeysInp.ikBSk ∧ accKeysInp.ikBPk = initInp.bundle.ikB) →
    (initInp.bundle.spkB = P.x25519Base accKeysInp.spkBSk ∧ accKeysInp.spkBPk = initInp.bundle.spkB) →
    (initInp.bundle.opkB?.map Prod.snd = accKeysInp.opkBSk?.map P.x25519Base ∧
     initInp.bundle.opkB?.isSome = accKeysInp.opkBSk?.isSome) →
    P.kemEncaps initInp.bundle.pqspkB initInp.kemCoins = some (ss, kemCt) →
    P.kemDecaps accKeysInp.pqspkBSk kemCt = some ss →
    (P.spqrInitSend (P.hkdfDerive96 (buildSecrets
      (P.x25519 initInp.ikASk initInp.bundle.spkB)
      (P.x25519 initInp.ekASk initInp.bundle.ikB)
      (P.x25519 initInp.ekASk initInp.bundle.spkB)
      (initInp.bundle.opkB?.map (fun (_, opkPk) => P.x25519 initInp.ekASk opkPk))
      ss)).pqrKey initInp.spqrCoins).isSome = true →
    ∃ drKey hdr rk1 ck1_1 msg,
      Model.initiateKeys P initInp.toInitiateKeysInput = some (drKey, hdr) ∧
      Model.acceptKeys P { accKeysInp with hdr := hdr } = some drKey ∧
      Model.initiate P initInp = some (drKey, rk1, ck1_1, msg) ∧
      Model.accept P { keysInp := { accKeysInp with hdr := hdr }, msg := msg } =
        some (drKey, rk1, ck1_1, initInp.plaintext)

end SignalPqxdh

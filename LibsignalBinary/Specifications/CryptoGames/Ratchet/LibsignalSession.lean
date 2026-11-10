/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.Ratchet.CreateChainDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.WireAeadDefs
public import LibsignalBinary.Specifications.LibsignalSignalMessage

/-!
# libsignal's double-ratchet session as a pure functional model

**Trusted: definitions used by the statement.** The theorems of `Computational/Theorems/` use every
definition in this file: read them. The theorems here are checked by Lean. See
`Computational/docs/TRUSTED_BASE.md`.

Method-for-method pure functional transcription of a single libsignal v0.105.4 double-ratchet /
triple-ratchet session (`rust/protocol/src/{ratchet,double_ratchet,triple_ratchet,session_management,protocol}.rs`,
with wire and error types imported from `LibsignalSignalMessage.lean`). Inner `&mut self` methods run
in `Mut σ α := ExceptT SignalProtocolError (StateM σ) α` (retaining partial mutations on error),
while session-level `tryDecryptFromRecord` and `messageEncrypt` preserve the input record on error by
operating on a clone (DEV-LS16); panics (`overflow-checks = true`, `panic = "abort"`) surface as
`SignalProtocolError.panic` (DEV-LS19).

Primitives (`Crypto`), protobuf encoding (`SignalMessageProtoCodec`, fixed to `protoSignalCodec` by
the headline theorem, DEV-LS21), and SPQR (`Spqr`, an untrusted per-message HKDF salt source,
DEV-LS24, DEV-LS25) are parameterized; X25519 is byte-level (`X25519Fn`, linked to an abstract group
via `X25519RealizesDh`, DEV-LS29). Relative to ACD19 Fig. 9, libsignal initializes from PQXDH with
Bob's signed pre-key (DEV-LS22, DEV-LS26), steps the DH ratchet eagerly on receive (DEV-LS1,
DEV-LS2), derives message keys via chain HMAC plus salted HKDF (DEV-LS14), identifies epochs by
ratchet key rather than epoch number with clear-text headers and 8-byte truncated MACs over identity
keys and raw wire bytes (DEV-LS8, DEV-LS12, DEV-LS13, DEV-LS15, DEV-LS20, DEV-LS23), and bounds
skipped keys and receiver chains (DEV-LS6, DEV-LS9, DEV-LS10, DEV-LS11, DEV-LS31).

**DEV-LS28 (libsignal): scope of the model.** Covers one non-self session (`self_session = false`,
distinct identity keys) started from abstract initial keys: Sesame archived-session loops, PQXDH,
`PreKeySignalMessage` wrapping, stores, identity trust checks, registration IDs, and the 30-day
staleness check are out of scope here (`LibsignalSessionApi.lean` adds `PreKeySignalMessage`, stores,
trust checks, and staleness for the public API). Session records use typed keys and `Seed`-form
skipped keys, excluding malformed-protobuf `InvalidSessionStructure` branches.
-/

@[expose] public section

namespace CryptoGames
namespace LibsignalSession

open HMAC HKDF CBC LibsignalAead

/-! ### Constants (`consts.rs`) -/

/-- `consts::MAX_FORWARD_JUMPS` (`consts.rs:8`).

**DEV-LS10 (libsignal): bounded receiver state.** ACD19 Fig. 6 and Fig. 8 keep every skipped key
and every epoch. libsignal rejects a jump of more than `maxForwardJumps = 25000` messages, keeps at
most `maxMessageKeys = 2000` skipped keys per chain and at most `maxReceiverChains = 5` receiver
chains. The model's Fig. 6 instance uses `maxSkip = 25000`; the reductions answer the other
rejections themselves. Effect: constants (`maxForwardJumps + 1 = 25001` lookahead slots in
`fsSlotCount qR = 2·qR + 25001`) and restricts the correctness game (DEV-LS6). -/
def maxForwardJumps : ℕ := 25000

/-- `consts::MAX_MESSAGE_KEYS` (`consts.rs:9`): stored skipped keys per receiver chain. -/
def maxMessageKeys : ℕ := 2000

/-- `consts::MAX_RECEIVER_CHAINS` (`consts.rs:10`). -/
def maxReceiverChains : ℕ := 5

/-! ### Keys (`core/curve.rs`, `core/curve/curve25519.rs`, `identity_key.rs`) -/

/-- The SHA-256 compression function (abstract `F`). -/
abbrev ShaCompress := ShaState → List (BitVec 8) → ShaState

/-- Public-key derivation on 32 secret bytes (`PrivateKey::derive_public_key_bytes`,
`core/curve/curve25519.rs:161–163`: `x25519_dalek::PublicKey::from(&StaticSecret)`, i.e.
`EdwardsPoint::mul_base_clamped(x).to_montgomery()`). -/
abbrev PubKeyFn := List.Vector (BitVec 8) 32 → List.Vector (BitVec 8) 32

/-- **The primitives** the session model is parameterized by (all abstract). -/
structure Crypto where
  /-- `F`: the SHA-256 compression function (HMAC, HKDF). -/
  F : ShaCompress
  /-- `E`: the AES-256 block encryption (CBC encryption). -/
  E : AesKey → Block → Block
  /-- `D`: the AES-256 block decryption (CBC decryption). -/
  D : AesKey → Block → Block
  /-- `X`: X25519 on 32-byte strings (`StaticSecret::diffie_hellman`, an abstract hook). -/
  X : Ratchet.X25519Fn
  /-- `pubKey`: X25519 public-key derivation (`PubKeyFn`). -/
  pubKey : PubKeyFn

/-- `PublicKey::serialize` (`core/curve.rs:122–132`): `0x05 ‖ key` (33 bytes). -/
def PublicKey.serialize (k : PublicKey) : List (BitVec 8) := djbType :: k.bytes.toList

/-- Curve25519 private key: 32 clamped key bytes (`core/curve/curve25519.rs:27–38`). -/
structure PrivateKey where
  bytes : List.Vector (BitVec 8) 32
  deriving DecidableEq

/-- `KeyPair` (`core/curve.rs:320–324`). -/
structure KeyPair where
  publicKey : PublicKey
  privateKey : PrivateKey
  deriving DecidableEq

/-- `KeyPair::generate` (`core/curve.rs:327–341`): clamp 32 LE bytes from `coins` and derive the
public key. -/
def KeyPair.generate (C : Crypto) (coins : BitVec 256) : KeyPair :=
  let sk := Ratchet.clampScalar (Ratchet.keyToBytesVec32 coins)
  ⟨⟨C.pubKey sk⟩, ⟨sk⟩⟩

/-- Identity public key (`IdentityKey`, `identity_key.rs`). -/
structure IdentityKey where
  publicKey : PublicKey
  deriving DecidableEq

/-- The 33-byte serialization `0x05 ‖ key` of an identity key (`IdentityKey::serialize`). -/
def IdentityKey.serialize (k : IdentityKey) : List (BitVec 8) := k.publicKey.serialize

/-- `sender.serialize() ‖ receiver.serialize()` as the wire AEAD's 66-byte `SerializedIdentityKeys`, the first two
`update`s of `compute_mac` (`protocol.rs:226–227`). -/
def macIds (sender receiver : IdentityKey) : SerializedIdentityKeys :=
  ⟨sender.serialize ++ receiver.serialize, by
    simp [IdentityKey.serialize, PublicKey.serialize]⟩

/-! ### Chain keys, message keys, root keys (`ratchet/keys.rs`) -/

/-- A root key (`RootKey { key: [u8; 32] }`, `ratchet/keys.rs:186–188`): its 32 LE bytes as a
`BitVec 256`, as `Ratchet.RootKey`. -/
abbrev RootKey := BitVec 256

/-- `ChainKey { key: [u8; 32], index: u32 }` (`ratchet/keys.rs:142–145`). -/
structure ChainKey where
  key : BitVec 256
  index : BitVec 32
  deriving DecidableEq

/-- `MessageKeyGenerator::Seed((seed, counter))` (`ratchet/keys.rs:13–17, 29–31, 54–60`): 32-byte
seed `HMAC(chain key, 0x01)` and `u32` counter. -/
structure MessageKeyGenerator where
  seed : List (BitVec 8)
  counter : BitVec 32
  deriving DecidableEq

/-- `MessageKeys { cipher_key, mac_key, iv, counter }` (`ratchet/keys.rs:91–97`). -/
structure MessageKeys where
  cipherKey : AesKey
  macKey : BitVec 256
  iv : Block
  counter : BitVec 32
  deriving DecidableEq

/-- `MessageKeyGenerator::generate_keys(pqr_key)` on a `Seed` (`ratchet/keys.rs:32–36`) =
`MessageKeys::derive_keys(seed, pqr_key, counter)` (`:100–118`): `HKDF(salt = pqr_key, ikm = seed,
"WhisperMessageKeys", 80)` split 32/32/16, exactly `HKDF.deriveMessageKeys`. -/
def MessageKeyGenerator.generateKeys (F : ShaCompress) (g : MessageKeyGenerator) (pqrKey : Salt) :
    MessageKeys :=
  let k := deriveMessageKeys F pqrKey g.seed
  ⟨k.1.1, k.2, k.1.2, g.counter⟩

/-- `ChainKey::next_chain_key` (`ratchet/keys.rs:165–170`): `key' = HMAC(key, 0x02)` (the chain
step `Ratchet.chainHmac`), `index + 1`. The `u32` addition panics at `index = u32::MAX` (overflow
checks are on in libsignal's release profile, `Cargo.toml:250–251`).

**DEV-LS19 (libsignal): `u32` counter, 0-based on the wire, panic at `u32::MAX`.** ACD19's message
indices are 1-based and unbounded. libsignal's counter is a `u32`, the wire carries `i − 1`, and
`next_chain_key` panics at `u32::MAX`. The reductions treat an index `≥ 2³²` as a structural
rejection, and the theorem assumes `2(q + 1) + 25002 < 2³²` (`hq32`). Effect: none for realistic
sessions (the bound is vacuous long before, DEV-LS31). -/
def ChainKey.nextChainKey (F : ShaCompress) (ck : ChainKey) :
    Except SignalProtocolError ChainKey :=
  if ck.index = BitVec.allOnes 32 then .error .panic
  else .ok ⟨bytesToKey32 (Ratchet.chainHmac F ck.key Ratchet.chainKeySeed), ck.index + 1⟩

/-- `ChainKey::message_keys` (`ratchet/keys.rs:172–177`): the generator with seed
`HMAC(key, 0x01)` and the chain's index. -/
def ChainKey.messageKeys (F : ShaCompress) (ck : ChainKey) : MessageKeyGenerator :=
  ⟨Ratchet.chainHmac F ck.key Ratchet.messageKeySeed, ck.index⟩

/-- `RootKey::create_chain(self, their_ratchet_key, our_ratchet_key)` (`ratchet/keys.rs:199–218`):
the X25519 agreement (`InvalidKeyAgreement` if all zero, `core/curve.rs:296–309`) and the root KDF,
via `Ratchet.createChain`; the new chain key has index 0. -/
def rootCreateChain (C : Crypto) (rk : RootKey) (their : PublicKey) (our : PrivateKey) :
    Except SignalProtocolError (RootKey × ChainKey) :=
  match Ratchet.createChain C.F C.X rk their.bytes our.bytes with
  | none => .error .invalidKeyAgreement
  | some (rk', ck) => .ok (rk', ⟨ck, 0⟩)

/-! ### SPQR (abstract) -/

/-- `spqr::Direction` (`A2B` for the initiator, `B2A` for the recipient, `ratchet.rs:86, 149`). -/
inductive SpqrDirection where
  | a2b
  | b2a
  deriving DecidableEq, Repr

/-- **The SPQR interface** (crate `spqr` 1.6.0, `src/lib.rs`): state `PQ` (upstream the serialized
bytes `SerializedState = Vec<u8>`, `:43`; here abstract, so a game can plug in any state machine),
`pq_ratchet` messages as bytes (`SerializedMessage = Vec<u8>`, `:44`, they go on the wire), coins
`PQC`:

* `init dir pqrKey` (`spqr::initial_state`, `:211`): the initial state from PQXDH's `pqr_key`;
  both parties use the same key (directions `A2B` / `B2A`).
* `send state coins` (`spqr::send`, `:264`): the new state, the message key (the HKDF salt of the
  message keys; `none` = no salt) and the `pq_ratchet` bytes; `none` = `Err`.
* `recv state msg` (`spqr::recv`, `:355`): the new state and the message key; `.error true` =
  `Error::StateDecode` (mapped to `InvalidState`), `.error false` = any other error (mapped to
  `InvalidMessage`, `triple_ratchet.rs:242–251`).
* `sendPanics state coins` / `recvPanics state msg`: `spqr::send` / `spqr::recv` panics on these
  inputs. libsignal is built with `panic = "abort"`, so the session operations abort
  (`SignalProtocolError.panic`) at the call site; the values of `send` / `recv` on such inputs are
  never used.

No property is assumed. Upstream moves the state out of the session with `mem::take`
(`state/session.rs:677–679`), leaving an empty `Vec`; the model leaves `default : PQ`
(`[Inhabited PQ]`; for `PQ = List (BitVec 8)` it is `[]`, exactly upstream). -/
structure Spqr (PQ PQC : Type) where
  /-- `spqr::initial_state(Params { auth_key = pqr_key, version: V1, direction, min_version: V1,
  chain_params })` (`spqr/src/lib.rs:211–233`; infallible for `V1`; `pqr_key` is PQXDH's 32-byte
  output, `ratchet.rs:83–96, 146–159`). -/
  init : SpqrDirection → BitVec 256 → PQ
  /-- `spqr::send`. -/
  send : PQ → PQC → Option (PQ × Salt × List (BitVec 8))
  /-- `spqr::recv`; the `Bool` of an error is "is `StateDecode`". -/
  recv : PQ → List (BitVec 8) → Except Bool (PQ × Salt)
  /-- `spqr::send` panics. -/
  sendPanics : PQ → PQC → Bool
  /-- `spqr::recv` panics. -/
  recvPanics : PQ → List (BitVec 8) → Bool

/-! ### `SignalMessage` (`protocol.rs:62–308`) -/

/-- The version byte `((message_version & 0xF) << 4) | CIPHERTEXT_MESSAGE_CURRENT_VERSION`
(`protocol.rs:106`). -/
def versionByte (v : BitVec 8) : BitVec 8 := ((v &&& 0x0F) <<< 4) ||| currentVersion

/-- The bytes before the MAC (`serialized` of `SignalMessage::new` before `extend_from_slice(&mac)`,
`protocol.rs:93–109`): `versionByte ‖ protobuf { ratchet_key = Some(serialize),
counter = Some, previous_counter = Some, ciphertext = Some, pq_ratchet = None if empty,
addresses }`. -/
def serializeContent (codec : SignalMessageProtoCodec) (v : BitVec 8) (ratchetKey : PublicKey)
    (counter previousCounter : BitVec 32) (ciphertext pqRatchet : List (BitVec 8))
    (addresses : Option (List (BitVec 8))) : List (BitVec 8) :=
  versionByte v :: codec.encode
    { ratchetKey := some ratchetKey.serialize, counter := some counter,
      previousCounter := some previousCounter, ciphertext := some ciphertext,
      pqRatchet := if pqRatchet.isEmpty then none else some pqRatchet, addresses := addresses }

/-- `SignalMessage::compute_mac` (`protocol.rs:214–235`): the first 8 bytes of
`HMAC-SHA256(mac_key, sender.serialize ‖ receiver.serialize ‖ message)`. The `mac_key.len() != 32`
error (`:220–222`) cannot occur (fixed-size key). Equals the wire AEAD's tag:
`bytesToWord64LE (computeMac …) = (hmacScheme F).tag macKey (macIds s r ‖ message)`.

**DEV-LS15 (libsignal): identity keys and addresses inside the MAC.** ACD19 Fig. 8 authenticates
only the header `h` as AD. libsignal MACs both identity keys (sender first) with the wire bytes,
and Alice's messages carry the serialized addresses until her first successful receive, which the
receiver checks. The Fig. 8 instance orders the identity keys by epoch parity (`lIds`). Effect:
none (the theorem assumes the instance uses libsignal's identity keys, `hid`). -/
def computeMac (F : ShaCompress) (sender receiver : IdentityKey) (macKey : BitVec 256)
    (message : List (BitVec 8)) : List (BitVec 8) :=
  hmacSha256Trunc8 F (keyToBytes32 macKey) ((macIds sender receiver).toList ++ message)

/-- `SignalMessage::new` (`protocol.rs:79–128`). `addresses` is the already serialized
`serialize_addresses(sender, recipient)` (`:91–92, 237–252`): `none` if no addresses are passed or
they are not valid service ids.

**DEV-LS20 (libsignal): the wire format.** ACD19 Fig. 8 sends `(h, e)` with `e ← Enc(K, h, m)`.
libsignal sends `version ‖ protobuf{ratchet_key, counter, previous_counter, ciphertext,
pq_ratchet?, addresses?} ‖ 8-byte MAC`: AES-256-CBC with PKCS#7, then HMAC-SHA256 truncated to 8
bytes over the raw bytes. The receiver parses the counter before it checks the MAC. The proof models
this as a per-message AEAD on the wire AEAD (`lAead`). Effect: constants (the 8-byte tag gives the
forgery term `macForgeryProb ≥ 2⁻⁶⁴`, DEV-LS23). -/
def SignalMessage.new (F : ShaCompress) (codec : SignalMessageProtoCodec) (messageVersion : BitVec 8)
    (macKey : BitVec 256) (addresses : Option (List (BitVec 8))) (senderRatchetKey : PublicKey)
    (counter previousCounter : BitVec 32) (ciphertext : List (BitVec 8))
    (senderIdentity receiverIdentity : IdentityKey) (pqRatchet : List (BitVec 8)) :
    SignalMessage :=
  let content := serializeContent codec messageVersion senderRatchetKey counter previousCounter
    ciphertext pqRatchet addresses
  { messageVersion, senderRatchetKey, counter, previousCounter, ciphertext, pqRatchet, addresses,
    serialized := content ++ computeMac F senderIdentity receiverIdentity macKey content }

/-- `SignalMessage::verify_mac` (`protocol.rs:160–173`): split off the last 8 bytes and compare
them with `compute_mac` of the rest (`ct_eq`). `serialized.len() ≥ 9` holds for every message
built by `new` / `try_from`. -/
def SignalMessage.verifyMac (F : ShaCompress) (m : SignalMessage)
    (senderIdentity receiverIdentity : IdentityKey) (macKey : BitVec 256) : Bool :=
  let content := m.serialized.take (m.serialized.length - macLength)
  let theirMac := m.serialized.drop (m.serialized.length - macLength)
  computeMac F senderIdentity receiverIdentity macKey content == theirMac

/-- `SignalMessage::verify_mac_with_addresses` (`protocol.rs:175–212`): the MAC, then, if the
message carries addresses, they must equal `expected = serialize_addresses(sender, recipient)`
(`none` = not serializable ⇒ reject). The wire AEAD's `addressCheckPasses`. The `Result` error of `compute_mac`
cannot occur. -/
def SignalMessage.verifyMacWithAddresses (F : ShaCompress) (m : SignalMessage)
    (expected : Option (List (BitVec 8))) (senderIdentity receiverIdentity : IdentityKey)
    (macKey : BitVec 256) : Bool :=
  m.verifyMac F senderIdentity receiverIdentity macKey && addressCheckPasses m.addresses expected

/-! ### AES-256-CBC (`crypto/aes_cbc.rs`) -/

/-- `aes_256_cbc_encrypt` (`crypto/aes_cbc.rs:26–35`) on any-length plaintext:
`cbcPkcs7EncryptOnly E ℓ` (PKCS#7, CBC) at `ℓ = |ptext|`, as bytes (LE blocks). The `BadKeyOrIv` error cannot
occur (fixed-size key and IV). -/
def aesCbcEncrypt (E : AesKey → Block → Block) (key : AesKey) (iv : Block)
    (ptext : List (BitVec 8)) : List (BitVec 8) :=
  ((cbcPkcs7EncryptOnly E ptext.length).enc (key, iv) ⟨ptext, rfl⟩).toList.flatMap blockToBytesLE

/-- `aes_256_cbc_decrypt` (`crypto/aes_cbc.rs:37–53`): `cbcDecRaw` (`none` =
`BadCiphertext`; `BadKeyOrIv` cannot occur). -/
def aesCbcDecrypt (D : AesKey → Block → Block) (key : AesKey) (iv : Block)
    (ctext : List (BitVec 8)) : Option (List (BitVec 8)) :=
  cbcDecRaw D key iv ctext

/-! ### The ratchet state (`double_ratchet.rs:24–55`) -/

/-- `SenderChain { ratchet_key, chain_key }` (`double_ratchet.rs:46–50`). -/
structure SenderChain where
  ratchetKey : KeyPair
  chainKey : ChainKey
  deriving DecidableEq

/-- Receiver chain (`session_structure::Chain`, `proto/storage.proto:11–33`,
`double_ratchet.rs:304–309`): peer ratchet public key, chain key, and stored skipped keys (newest
first).

**DEV-LS9 (libsignal): per-chain skipped-key stores instead of FS-AEAD instances.** libsignal keeps
a sender chain and up to 5 receiver chains, each storing up to 2000 skipped keys as 32-byte seeds
expanded with the receiving message's SPQR salt (bounds in DEV-LS10). -/
structure ReceiverChain where
  senderRatchetKey : PublicKey
  chainKey : Option ChainKey
  /-- Skipped keys in `Seed` form, newest first (at most 2000). -/
  messageKeys : List MessageKeyGenerator
  deriving DecidableEq

/-- `RatchetState` (`double_ratchet.rs:31–42`), with `receiverChains` ordered oldest first. -/
structure RatchetState where
  rootKey : RootKey
  senderChain : Option SenderChain
  receiverChains : List ReceiverChain
  previousCounter : BitVec 32
  /-- `max_forward_jumps` (`25000` for non-self sessions). -/
  maxForwardJumps : ℕ
  deriving DecidableEq

/-! ### Effects -/

/-- A Rust method `fn(&mut σ, …) -> Result<α, SignalProtocolError>`: the state after the call is
returned on success **and** on error (what upstream leaves in `*self`). -/
abbrev Mut (σ α : Type) := ExceptT SignalProtocolError (StateM σ) α

/-- Run a `Mut` action: (result, final state). -/
def Mut.exec {σ α : Type} (m : Mut σ α) (s : σ) : Except SignalProtocolError α × σ :=
  (m.run).run s

/-- Lift a pure `Result` (no state change). -/
def liftE {σ α : Type} : Except SignalProtocolError α → Mut σ α
  | .ok a => pure a
  | .error e => throw e

/-- Run a `Mut` action on a field of the state (`self.ratchet.m(…)` from a method of the outer
struct). -/
def zoom {σ τ α : Type} (proj : σ → τ) (inj : σ → τ → σ) (m : Mut τ α) : Mut σ α := do
  let s ← get
  let (r, t) := Mut.exec m (proj s)
  set (inj s t)
  liftE r

/-! ### Double ratchet methods (`double_ratchet.rs:171–381`) -/

namespace RatchetState

/-- `find_receiver_chain_index` (`double_ratchet.rs:370–380`): the first receiver chain whose
`sender_ratchet_key` equals `their`. -/
def findReceiverChainIndex (s : RatchetState) (their : PublicKey) : Option ℕ :=
  s.receiverChains.findIdx? (fun c => c.senderRatchetKey == their)

/-- `find_receiver_chain_key` (`double_ratchet.rs:257–269`): the chain key of that chain;
`Err(missing receiver chain key)` if it is `None`. -/
def findReceiverChainKey (s : RatchetState) (their : PublicKey) :
    Except SignalProtocolError (Option ChainKey) :=
  match s.findReceiverChainIndex their with
  | none => .ok none
  | some idx =>
    match s.receiverChains[idx]? with
    | none => .error .panic
    | some c =>
      match c.chainKey with
      | none => .error (.invalidSessionStructure .missingReceiverChainKey)
      | some ck => .ok (some ck)

/-- `take_root_key` (`double_ratchet.rs:174–176`): replace the root key by 32 zero bytes. -/
def takeRootKey : Mut RatchetState RootKey :=
  modifyGet fun s => (s.rootKey, { s with rootKey := 0 })

/-- Keep the last `maxReceiverChains` chains: the `while len > 5 { remove(0) }` loop
(`double_ratchet.rs:310–312`). -/
def evictReceiverChains (cs : List ReceiverChain) : List ReceiverChain :=
  cs.drop (cs.length - maxReceiverChains)

/-- **`dh_ratchet_step`** (`double_ratchet.rs:271–320`), both half-steps, with `coins` the 32 bytes
of `KeyPair::generate(csprng)`:
1. `missing sender chain` if none (no change);
2. take the root key (now zero in `self`);
3. receiving half-step `create_chain(their, our sender private key)` (may fail:
   `InvalidKeyAgreement`, root key left zero);
4. fresh key pair; sending half-step `create_chain(their, new private key)` (may fail likewise);
5. `previous_counter = sender index saturating_sub 1`, root key, push the receiver chain
   `(their, receiver chain key, [])`, evict to 5, new sender chain. Returns the receiver chain
   key. -/
def dhRatchetStep (C : Crypto) (their : PublicKey) (coins : BitVec 256) :
    Mut RatchetState ChainKey := do
  let some sc := (← get).senderChain
    | throw (.invalidSessionStructure .missingSenderChain)
  let senderPrivateKey := sc.ratchetKey.privateKey
  let currentRootKey ← takeRootKey
  let (newRootKey, receiverChainKey) ← liftE (rootCreateChain C currentRootKey their senderPrivateKey)
  let newSenderKey := KeyPair.generate C coins
  let (finalRootKey, senderChainKey) ←
    liftE (rootCreateChain C newRootKey their newSenderKey.privateKey)
  let currentIndex := sc.chainKey.index
  modify fun s =>
    { s with
      previousCounter := if currentIndex = 0 then 0 else currentIndex - 1
      rootKey := finalRootKey
      receiverChains := evictReceiverChains
        (s.receiverChains ++ [⟨their, some receiverChainKey, []⟩])
      senderChain := some ⟨newSenderKey, senderChainKey⟩ }
  return receiverChainKey

/-- **`take_skipped_key`** (`double_ratchet.rs:322–344`): in the chain for `their` (if any), find
the first stored key with `index = counter` (`position`), **remove** it and return it; `none` if
there is no such chain or key. (`from_pb` cannot fail on a `Seed`-form key.) -/
def takeSkippedKey (their : PublicKey) (counter : BitVec 32) :
    Mut RatchetState (Option MessageKeyGenerator) := do
  let s ← get
  let some chainIdx := s.findReceiverChainIndex their | return none
  let some c := s.receiverChains[chainIdx]? | throw .panic
  let some pos := c.messageKeys.findIdx? (fun mk => mk.counter == counter) | return none
  let some key := c.messageKeys[pos]? | throw .panic
  set { s with receiverChains :=
    s.receiverChains.set chainIdx { c with messageKeys := c.messageKeys.eraseIdx pos } }
  return some key

/-- **`store_skipped_key`** (`double_ratchet.rs:346–361`): `insert(0, key)` into the chain for
`their` (panics if there is none), then `pop()` the oldest if more than 2000. -/
def storeSkippedKey (their : PublicKey) (key : MessageKeyGenerator) : Mut RatchetState Unit := do
  let s ← get
  let some chainIdx := s.findReceiverChainIndex their | throw .panic
  let some c := s.receiverChains[chainIdx]? | throw .panic
  let keys := key :: c.messageKeys
  let keys := if maxMessageKeys < keys.length then keys.dropLast else keys
  set { s with receiverChains := s.receiverChains.set chainIdx { c with messageKeys := keys } }

/-- **`set_receiver_chain_key`** (`double_ratchet.rs:363–368`): set the chain key of the chain
for `their` (panics if there is none). -/
def setReceiverChainKey (their : PublicKey) (ck : ChainKey) : Mut RatchetState Unit := do
  let s ← get
  let some chainIdx := s.findReceiverChainIndex their | throw .panic
  let some c := s.receiverChains[chainIdx]? | throw .panic
  set { s with receiverChains := s.receiverChains.set chainIdx { c with chainKey := some ck } }

/-- The loop `while chain_key.index() < counter { store_skipped_key(their,
chain_key.message_keys()); chain_key = chain_key.next_chain_key(); }` (`double_ratchet.rs:244–247`)
with `fuel` bounding the iterations (`consumeMessageKey` passes `counter − index`, which is exactly
the number of iterations; with `fuel = 0` the loop stops). -/
def advanceChain (F : ShaCompress) (their : PublicKey) (counter : BitVec 32) :
    ℕ → ChainKey → Mut RatchetState ChainKey
  | 0, ck => pure ck
  | fuel + 1, ck => do
    if ck.index < counter then
      storeSkippedKey their (ck.messageKeys F)
      let ck' ← liftE (ck.nextChainKey F)
      advanceChain F their counter fuel ck'
    else pure ck

/-- **`consume_message_key`** (`double_ratchet.rs:203–253`) for the receiver chain of `their` with
chain key `chainKey` and message `counter`:
* `counter < index`: `take_skipped_key`, or `DuplicatedMessage(index, counter)` (no change);
* `counter − index > max_forward_jumps`: `InvalidMessage(too far into the future)` (no change);
* otherwise store the skipped keys `index … counter − 1` (newest first, at most 2000), set the
  receiver chain key to the key after `counter`, return the key at `counter`. -/
def consumeMessageKey (F : ShaCompress) (their : PublicKey) (chainKey : ChainKey)
    (counter : BitVec 32) (msgType : MessageType) : Mut RatchetState MessageKeyGenerator := do
  let chainIndex := chainKey.index
  if counter < chainIndex then
    match ← takeSkippedKey their counter with
    | some k => return k
    | none => throw (.duplicatedMessage chainIndex counter)
  let jump := (counter - chainIndex).toNat
  if (← get).maxForwardJumps < jump then
    throw (.invalidMessage msgType .tooFarInFuture)
  let chainKey ← advanceChain F their counter jump chainKey
  setReceiverChainKey their (← liftE (chainKey.nextChainKey F))
  return chainKey.messageKeys F

/-- **`ensure_receiver_chain`** (`double_ratchet.rs:185–195`): the chain key of the chain for
`their` if there is one, else `dh_ratchet_step` (which consumes `coins`). -/
def ensureReceiverChain (C : Crypto) (their : PublicKey) (coins : BitVec 256) :
    Mut RatchetState ChainKey := do
  match ← liftE ((← get).findReceiverChainKey their) with
  | some ck => return ck
  | none => dhRatchetStep C their coins

end RatchetState

/-! ### Triple ratchet (`triple_ratchet.rs`) -/

/-- `TripleRatchet` (`triple_ratchet.rs:160–165`). -/
structure TripleRatchet (PQ : Type) where
  ratchet : RatchetState
  pqrState : PQ
  localIdentityKey : IdentityKey
  remoteIdentityKey : IdentityKey
  deriving DecidableEq

/-- Lift a `RatchetState` mutation onto `TripleRatchet.ratchet`. -/
def TripleRatchet.onRatchet {PQ α : Type} (m : Mut RatchetState α) : Mut (TripleRatchet PQ) α :=
  zoom TripleRatchet.ratchet (fun t r => { t with ratchet := r }) m

/-- `TripleRatchet::decrypt` (`triple_ratchet.rs:215–298`): advances/consumes the receiver chain key
(persisting on later failure), steps `spqr.recv`, verifies the MAC and address blob over raw bytes,
AES-CBC decrypts, and commits `newPqrState`. -/
def TripleRatchet.decrypt {PQ PQC : Type} (C : Crypto) (spqr : Spqr PQ PQC)
    (expected : Option (List (BitVec 8))) (ciphertext : SignalMessage) (msgType : MessageType)
    (coins : BitVec 256) : Mut (TripleRatchet PQ) (List (BitVec 8)) := do
  let their := ciphertext.senderRatchetKey
  let counter := ciphertext.counter
  let chainKey ← TripleRatchet.onRatchet (RatchetState.ensureReceiverChain C their coins)
  let messageKeyGen ←
    TripleRatchet.onRatchet (RatchetState.consumeMessageKey C.F their chainKey counter msgType)
  let t ← get
  if spqr.recvPanics t.pqrState ciphertext.pqRatchet then throw .panic
  let (newPqrState, pqrKey) ← match spqr.recv t.pqrState ciphertext.pqRatchet with
    | .ok r => pure r
    | .error true => throw .invalidState
    | .error false => throw (.invalidMessage msgType .pqRatchet)
  let messageKeys := messageKeyGen.generateKeys C.F pqrKey
  let macValid := ciphertext.verifyMacWithAddresses C.F expected t.remoteIdentityKey
    t.localIdentityKey messageKeys.macKey
  if !macValid then throw (.invalidMessage msgType .macFailed)
  let some ptext := aesCbcDecrypt C.D messageKeys.cipherKey messageKeys.iv ciphertext.ciphertext
    | throw (.invalidMessage msgType .badCiphertext)
  modify fun t => { t with pqrState := newPqrState }
  return ptext

/-- `OutgoingTripleRatchet` (`triple_ratchet.rs:41–49`). -/
structure OutgoingTripleRatchet (PQ : Type) where
  senderRatchetKey : KeyPair
  senderChainKey : ChainKey
  previousCounter : BitVec 32
  pqrState : PQ
  sessionVersion : BitVec 8
  localIdentityKey : IdentityKey
  remoteIdentityKey : IdentityKey
  deriving DecidableEq

/-- `OutgoingTripleRatchet::encrypt` (`triple_ratchet.rs:86–135`): steps `spqr.send`, derives
salted message keys, AES-CBC encrypts and MACs via `SignalMessage.new`, and advances the sender
chain key (panicking at `u32::MAX`). -/
def OutgoingTripleRatchet.encrypt {PQ PQC : Type} (C : Crypto) (codec : SignalMessageProtoCodec)
    (spqr : Spqr PQ PQC)
    (ptext : List (BitVec 8)) (addresses : Option (List (BitVec 8))) (coins : PQC) :
    Mut (OutgoingTripleRatchet PQ) SignalMessage := do
  let o ← get
  if spqr.sendPanics o.pqrState coins then throw .panic
  let some (newPqrState, pqrKey, pqrMsg) := spqr.send o.pqrState coins | throw .invalidState
  let messageKeys := (o.senderChainKey.messageKeys C.F).generateKeys C.F pqrKey
  let ctext := aesCbcEncrypt C.E messageKeys.cipherKey messageKeys.iv ptext
  let message := SignalMessage.new C.F codec o.sessionVersion messageKeys.macKey addresses
    o.senderRatchetKey.publicKey o.senderChainKey.index o.previousCounter ctext
    o.localIdentityKey o.remoteIdentityKey pqrMsg
  let next ← liftE (o.senderChainKey.nextChainKey C.F)
  set { o with senderChainKey := next, pqrState := newPqrState }
  return message

/-! ### The session state and the session-level operations -/

/-- Ratchet-relevant fields of `SessionState` / `SessionStructure` (`state/session.rs:141–171`,
`proto/storage.proto:10–68`). -/
structure SessionState (PQ : Type) where
  /-- `session_version` (`0` reads as `2`, `state/session.rs:178–183`). -/
  sessionVersion : BitVec 32
  localIdentity : IdentityKey
  remoteIdentity : Option IdentityKey
  rootKey : RootKey
  previousCounter : BitVec 32
  senderChain : Option SenderChain
  /-- Stored receiver chains, oldest first. -/
  receiverChains : List ReceiverChain
  /-- Whether `pending_pre_key.is_some()` (unacknowledged session). -/
  pendingPreKey : Bool
  pqRatchetState : PQ
  deriving DecidableEq

namespace SessionState

/-- `SessionState::session_version` (`state/session.rs:178–183`): `0` means `2`. -/
def version {PQ : Type} (s : SessionState PQ) : BitVec 32 := if s.sessionVersion = 0 then 2 else s.sessionVersion

/-- `take_ratchet_state(self_session = false)` (`state/session.rs:625–635`) with `RatchetState::from_pb`
(`double_ratchet.rs:71–99`): move the receiver chains out (left empty), copy root key, sender
chain, previous counter; `max_forward_jumps = MAX_FORWARD_JUMPS`. (`from_pb`'s errors are about
malformed bytes, not representable here.) -/
def takeRatchetState {PQ : Type} : Mut (SessionState PQ) RatchetState :=
  modifyGet fun s =>
    (⟨s.rootKey, s.senderChain, s.receiverChains, s.previousCounter, maxForwardJumps⟩,
      { s with receiverChains := [] })

/-- `take_pq_ratchet_state` (`state/session.rs:677–679`): move the SPQR state out (left empty). -/
def takePqRatchetState {PQ : Type} [Inhabited PQ] : Mut (SessionState PQ) PQ :=
  modifyGet fun s => (s.pqRatchetState, { s with pqRatchetState := default })

/-- `clear_unacknowledged_pre_key_message` (`state/session.rs:566–598`). -/
def clearUnacknowledgedPreKeyMessage {PQ : Type} (s : SessionState PQ) : SessionState PQ :=
  { s with pendingPreKey := false }

end SessionState

/-- `TripleRatchet::from_session_state` (`triple_ratchet.rs:176–193`): take the ratchet and SPQR
states (mutating `state`), read the identity keys (`missing remote identity key` if absent). -/
def TripleRatchet.fromSessionState {PQ : Type} [Inhabited PQ] :
    Mut (SessionState PQ) (TripleRatchet PQ) := do
  let ratchet ← SessionState.takeRatchetState
  let pqrState ← SessionState.takePqRatchetState
  let s ← get
  let some remote := s.remoteIdentity
    | throw (.invalidSessionStructure .missingRemoteIdentity)
  return ⟨ratchet, pqrState, s.localIdentity, remote⟩

/-- `TripleRatchet::apply_to_session_state` (`triple_ratchet.rs:199–202`) with
`RatchetState::apply_to_pb` (`double_ratchet.rs:105–117`): write root key, previous counter, sender
chain, receiver chains and the SPQR state back. -/
def TripleRatchet.applyToSessionState {PQ : Type} (t : TripleRatchet PQ) (s : SessionState PQ) :
    SessionState PQ :=
  { s with rootKey := t.ratchet.rootKey, previousCounter := t.ratchet.previousCounter,
           senderChain := t.ratchet.senderChain, receiverChains := t.ratchet.receiverChains,
           pqRatchetState := t.pqrState }

namespace SessionState

/-- **`try_decrypt_with_state`** (`session_management.rs:566–606`, `self_session = false`): build a
`TripleRatchet` from `state` (which moves fields out of it), decrypt, and on success write the
ratchet back and clear the unacknowledged pre-key flag. On error, `state` is left as
`from_session_state` / the failed decrypt left it (the caller discards it). -/
def tryDecryptWithState {PQ PQC : Type} [Inhabited PQ] (C : Crypto) (spqr : Spqr PQ PQC)
    (expected : Option (List (BitVec 8))) (ciphertext : SignalMessage) (msgType : MessageType)
    (coins : BitVec 256) : Mut (SessionState PQ) (List (BitVec 8)) := do
  let session ← TripleRatchet.fromSessionState
  let (r, session) :=
    Mut.exec (TripleRatchet.decrypt C spqr expected ciphertext msgType coins) session
  let ptext ← liftE r
  modify fun s => (session.applyToSessionState s).clearUnacknowledgedPreKeyMessage
  return ptext

/-- The error `try_decrypt_from_record` returns for a failed `try_decrypt_with_state` with a single
session: `DuplicatedMessage` as is (`session_management.rs:432`); a panic is never collected (it
aborts / unwinds); every other error is collected and becomes `InvalidMessage(msg_type, "decryption
failed")` (`:436–455` for `PreKey`, `:527–554` for `Whisper` after the empty previous-session
loop). -/
def recordError (msgType : MessageType) : SignalProtocolError → SignalProtocolError
  | .duplicatedMessage i c => .duplicatedMessage i c
  | .panic => .panic
  | _ => .invalidMessage msgType .decryptionFailed

/-- **`try_decrypt_from_record`** (`session_management.rs:368–556`) for a record with a current
session `record` and no previous sessions: on a clone, check the version
(`UnrecognizedMessageVersion`, collected), run `try_decrypt_with_state`; store the clone only on
success. A version mismatch is collected (`InvalidMessage(msg_type, "decryption failed")`); other
errors are mapped by `recordError`. **On error the record is unchanged.**

**DEV-LS16 (libsignal): reject leaves the state unchanged only through the caller's clone.** ACD19
Def. 7 (A) asks that a rejected ciphertext leaves the state unchanged. libsignal's inner methods do
not: on error they leave a zeroed root key or a removed skipped key. `try_decrypt_from_record` works
on a clone and stores it only on success, so Def. 7 (A) holds at this level. Effect: none. -/
def tryDecryptFromRecord {PQ PQC : Type} [Inhabited PQ] (C : Crypto) (spqr : Spqr PQ PQC)
    (expected : Option (List (BitVec 8))) (ciphertext : SignalMessage) (msgType : MessageType)
    (coins : BitVec 256) (record : SessionState PQ) :
    Except SignalProtocolError (List (BitVec 8)) × SessionState PQ :=
  if record.version.toNat ≠ ciphertext.messageVersion.toNat then
    (.error (.invalidMessage msgType .decryptionFailed), record)
  else
    match Mut.exec (tryDecryptWithState C spqr expected ciphertext msgType coins) record with
    | (.ok ptext, updated) => (.ok ptext, updated)
    | (.error e, _) => (.error (recordError msgType e), record)

end SessionState

/-- `OutgoingTripleRatchet::from_session_state` (`triple_ratchet.rs:52–79`): read the sender key
pair and chain key (`missing sender chain`), **take** the SPQR state, check the version fits in a
`u8`, read the identity keys (`missing remote identity key`). -/
def OutgoingTripleRatchet.fromSessionState {PQ : Type} [Inhabited PQ] :
    Mut (SessionState PQ) (OutgoingTripleRatchet PQ) := do
  let some sc := (← get).senderChain
    | throw (.invalidSessionStructure .missingSenderChain)
  let pqrState ← SessionState.takePqRatchetState
  let s ← get
  if 256 ≤ s.version.toNat then throw (.invalidSessionStructure .versionTooLarge)
  let some remote := s.remoteIdentity
    | throw (.invalidSessionStructure .missingRemoteIdentity)
  return ⟨sc.ratchetKey, sc.chainKey, s.previousCounter, pqrState,
    BitVec.ofNat 8 s.version.toNat, s.localIdentity, remote⟩

/-- `OutgoingTripleRatchet::apply_to_session_state` (`triple_ratchet.rs:81–84`):
`set_sender_chain_key` (`state/session.rs:417–440`; keeps the sender key pair) and the SPQR state.
(`set_sender_chain_key` with no sender chain would create one with empty keys; it is called only
after `from_session_state` found a sender chain.) -/
def OutgoingTripleRatchet.applyToSessionState {PQ : Type} (o : OutgoingTripleRatchet PQ)
    (s : SessionState PQ) : SessionState PQ :=
  { s with senderChain := s.senderChain.map fun sc => { sc with chainKey := o.senderChainKey },
           pqRatchetState := o.pqrState }

namespace SessionState

/-- The addresses `message_encrypt` passes to `encrypt`: `serialize_addresses(local, remote)` iff
the session is unacknowledged (`Some(local_address)` at `session_management.rs:104`, `None` at
`:117`). -/
def encryptAddresses {PQ : Type} (record : SessionState PQ) (addresses : Option (List (BitVec 8))) :
    Option (List (BitVec 8)) :=
  if record.pendingPreKey then addresses else none

/-- **`message_encrypt`'s ratchet part** (`session_management.rs:43–151`): on the loaded record,
`OutgoingTripleRatchet::from_session_state`, `encrypt` (with `encryptAddresses`), then
`apply_to_session_state` and store. On error nothing is stored: **the record is unchanged.**
For an unacknowledged session upstream wraps the result in a `PreKeySignalMessage` (out of scope:
the inner `SignalMessage` is returned); the staleness check, identity trust and store calls are out
of scope. -/
def messageEncrypt {PQ PQC : Type} [Inhabited PQ] (C : Crypto) (codec : SignalMessageProtoCodec)
    (spqr : Spqr PQ PQC)
    (addresses : Option (List (BitVec 8))) (ptext : List (BitVec 8)) (coins : PQC)
    (record : SessionState PQ) : Except SignalProtocolError SignalMessage × SessionState PQ :=
  match Mut.exec OutgoingTripleRatchet.fromSessionState record with
  | (.error e, _) => (.error e, record)
  | (.ok session, taken) =>
    match Mut.exec (OutgoingTripleRatchet.encrypt C codec spqr ptext
        (record.encryptAddresses addresses) coins) session with
    | (.error e, _) => (.error e, record)
    | (.ok message, session) => (.ok message, session.applyToSessionState taken)

/-! ### Session initialization (`ratchet.rs`, `state/session.rs`) -/

/-- `SessionState::new` (`state/session.rs:146–171`) without `alice_base_key` and registration
ids: no chains, `previous_counter = 0`, no pending pre-key. -/
def new {PQ : Type} (version : BitVec 8) (ourIdentity theirIdentity : IdentityKey)
    (rootKey : RootKey) (pqRatchetState : PQ) : SessionState PQ :=
  { sessionVersion := BitVec.ofNat 32 version.toNat, localIdentity := ourIdentity,
    remoteIdentity := some theirIdentity, rootKey, previousCounter := 0, senderChain := none,
    receiverChains := [], pendingPreKey := false, pqRatchetState }

/-- `add_receiver_chain` (`state/session.rs:342–366`): push, then remove index 0 if more than 5. -/
def addReceiverChain {PQ : Type} (s : SessionState PQ) (sender : PublicKey) (ck : ChainKey) :
    SessionState PQ :=
  let cs := s.receiverChains ++ [⟨sender, some ck, []⟩]
  { s with receiverChains := if maxReceiverChains < cs.length then cs.drop 1 else cs }

/-- `set_sender_chain` (`state/session.rs:373–387`). -/
def setSenderChain {PQ : Type} (s : SessionState PQ) (sender : KeyPair) (ck : ChainKey) :
    SessionState PQ :=
  { s with senderChain := some ⟨sender, ck⟩ }

/-- `set_unacknowledged_pre_key_message` (`state/session.rs:509–547`), as called by
`process_prekey_bundle` right after `initialize_alice_session` (`session.rs:270–275`). -/
def setUnacknowledgedPreKeyMessage {PQ : Type} (s : SessionState PQ) : SessionState PQ :=
  { s with pendingPreKey := true }

end SessionState

/-- **`initialize_initiator_session`** (`ratchet.rs:67–112`) from abstract PQXDH outputs (root key
`rootKey`, chain key `chainKey` with index 0, `pqrKey`): generate the first sending key pair from
`coins` **eagerly**, `create_chain(root key, their ratchet key = Bob's signed pre-key, new private
key)`, the SPQR state `spqr.init A2B pqrKey`; the session has a receiver chain for
`theirRatchetKey` with `chainKey`, and the new sender chain. -/
def initializeInitiatorSession {PQ PQC : Type} (C : Crypto) (spqr : Spqr PQ PQC)
    (ourIdentity theirIdentity : IdentityKey) (theirRatchetKey : PublicKey) (rootKey : RootKey)
    (chainKey pqrKey : BitVec 256) (coins : BitVec 256) :
    Except SignalProtocolError (SessionState PQ) := do
  let sendingRatchetKey := KeyPair.generate C coins
  let (sendingChainRootKey, sendingChainChainKey) ←
    rootCreateChain C rootKey theirRatchetKey sendingRatchetKey.privateKey
  let pqrState := spqr.init .a2b pqrKey
  return ((SessionState.new currentVersion ourIdentity theirIdentity sendingChainRootKey
      pqrState).addReceiverChain theirRatchetKey ⟨chainKey, 0⟩).setSenderChain
    sendingRatchetKey sendingChainChainKey

/-- **`initialize_recipient_session`** (`ratchet.rs:137–172`) from abstract PQXDH outputs (root key,
chain key, `pqrKey`; SPQR state `spqr.init B2A pqrKey`): the session's sender chain is our ratchet key pair (Bob's signed pre-key) with `chainKey` (index 0);
no receiver chain. Upstream private keys are always clamped (`PrivateKey::new`, `From<[u8; 32]>`,
`PrivateKey::deserialize`, `core/curve/curve25519.rs:34, 170–175`, `core/curve.rs:242–248`); the
caller passes a clamped key pair (e.g. `KeyPair.generate`). -/
def initializeRecipientSession {PQ PQC : Type} (spqr : Spqr PQ PQC)
    (ourIdentity theirIdentity : IdentityKey) (ourRatchetKeyPair : KeyPair) (rootKey : RootKey)
    (chainKey pqrKey : BitVec 256) : SessionState PQ :=
  (SessionState.new currentVersion ourIdentity theirIdentity rootKey
    (spqr.init .b2a pqrKey)).setSenderChain ourRatchetKeyPair ⟨chainKey, 0⟩

/-! ### Bridge to the wire AEAD's `WireCodec` -/

/-- Header fields of a `SignalMessage` (everything in the MACed bytes except the ciphertext body). -/
structure SignalHeader where
  messageVersion : BitVec 8
  senderRatchetKey : PublicKey
  counter : BitVec 32
  previousCounter : BitVec 32
  pqRatchet : List (BitVec 8)
  addresses : Option (List (BitVec 8))
  deriving DecidableEq

/-- Extract the `SignalHeader` of a `SignalMessage`. -/
def SignalMessage.header (m : SignalMessage) : SignalHeader :=
  ⟨m.messageVersion, m.senderRatchetKey, m.counter, m.previousCounter, m.pqRatchet, m.addresses⟩

/-- **libsignal's `SignalMessage` as the wire AEAD's `WireCodec`**: `encode` = the bytes before the MAC
of `SignalMessage::new`; `parse ser` = `SignalMessage::try_from (ser ‖ 8 bytes)` (the MAC bytes are
not read by `try_from`). -/
def signalWireCodec (codec : SignalMessageProtoCodec) : WireCodec SignalHeader where
  encode h body := serializeContent codec h.messageVersion h.senderRatchetKey h.counter
    h.previousCounter body h.pqRatchet h.addresses
  parse ser :=
    match SignalMessage.tryFrom codec (ser ++ List.replicate macLength 0) with
    | .ok m => some (m.header, m.ciphertext)
    | .error _ => none

end LibsignalSession
end CryptoGames

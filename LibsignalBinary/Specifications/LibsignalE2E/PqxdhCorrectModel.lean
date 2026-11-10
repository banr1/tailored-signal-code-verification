/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhModelLink
public import LibsignalBinary.Specifications.LibsignalE2E.StateXModel
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Init
public import LibsignalBinary.Specifications.LibsignalE2E.SchemeModel

/-!
# PQXDH Handshake Session Models (`initiateState`, `recvPrekeyState`)

**Trusted: the statement.** Composes the pure PQXDH key-agreement specification
(`SignalPqxdh.Model.initiateKeys` / `acceptKeys`) with `initializeInitiatorSession` /
`initializeRecipientSession` and V1 SPQR (`pqxdhSpqrSession`) to model Alice's `init` and Bob's
pre-key `recv` (`process_prekey_bundle` / `process_prekey`). See `Computational/docs/TRUSTED_BASE.md`
and `Computational/docs/DEVIATIONS.md` (DEV-PQ5, DEV-PQ6, DEV-PQ8).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalAesCbc (toLEBytes)

/-! ## Keys -/

/-- **The key pair of 32 private-key bytes** as libsignal makes it (`PrivateKey::deserialize`
clamps; `KeyPair::try_from` / `IdentityKeyPair::try_from` derive the public key from the clamped
scalar). This is the body of the session model's `KeyPair.generate` (`LibsignalSession.lean`), which
takes its 32 bytes as `BitVec 256` coins (`keyToBytesVec32 coins`) rather than as a byte vector; it is
restated here on bytes so that no byte/word round trip enters the statement. -/
def keyPairOf (C : Crypto) (sk : List.Vector (BitVec 8) 32) : KeyPair :=
  let c := Ratchet.clampScalar sk
  ⟨⟨C.pubKey c⟩, ⟨c⟩⟩

/-- A model `UInt32` from a 32-bit word. -/
def u32 (b : BitVec 32) : UInt32 := UInt32.ofBitVec b

/-! ## SPQR V1 session parameters (`pqxdhSpqrSession`, `pqxdhSessionParams`) -/

/-- **The V1 `Spqr Bytes Bytes` session instance for `W`**:
`LibsignalSpqrV1.spqrV1Session W.C.F W.Q.K`
(`= (LibsignalSpqrV1.spqrV1 W.C.F W.Q.K).spqrWith (spqrV1Init W.C.F W.Q.K)` by `rfl`). -/
def pqxdhSpqrSession (W : PEParams) : Spqr Bytes Bytes :=
  LibsignalSpqrV1.spqrV1Session W.C.F W.Q.K

/-- **The session-model parameters for PQXDH sessions** (`spqrOffSessionParams W.C` with V1 SPQR `pqxdhSpqrSession W`
replacing `spqrOffB`; `spqrOffSessionParams W.C` stays untouched for the SPQR-off statements, `SmDir.lean`). -/
def pqxdhSessionParams (W : PEParams) : Params Bytes Bytes :=
  ⟨W.C, protoSignalCodec, pqxdhSpqrSession W, partyIdentityKey .A, partyIdentityKey .B,
   serializedPartyAddresses LibsignalTripleRatchetRepr.uuidTryParse .A .B,
   serializedPartyAddresses LibsignalTripleRatchetRepr.uuidTryParse .B .A⟩

/-! ## Alice's `init` -/

/-- **Alice's record extras after `init`** (`process_prekey_bundle`):
* `pending`: one-time pre-key id (if any), signed pre-key id, Alice's base key `base`, timestamp 0
  (DEV-PQ8);
* `kyber`: the Kyber pre-key id and the serialized ciphertext `0x08 ‖ ct`
  (`set_kyber_ciphertext`, `set_unacknowledged_kyber_pre_key_id`);
* the registration ids: `me`'s local id and the bundle's remote id;
* `alice_base_key`: Alice's own base key, serialized. -/
def initiatorRecordExtras (me : LocalIdentity) (b : PreKeyBundleFields) (base : PublicKey) (ct : List.Vector (BitVec 8) 1568) :
    RecordExtras :=
  { pending := { preKeyId := b.opk.map Prod.fst, signedPreKeyId := b.spkId, baseKey := base,
                 timestamp := 0#64 }
    kyber := some { preKeyId := b.kpkId, ciphertext := kyberKey ct }
    remoteRegistrationId := b.regId
    localRegistrationId := me.regId
    aliceBaseKey := base.serialize }

/-- **The model's input to `Model.initiateKeys`** for `me`, bundle `b` and tape `t`:
* Alice's identity key pair is `me.idPriv`'s;
* the base key's scalar is tape bytes `0..32` (`KeyPair::generate`, which clamps; so does
  `x25519`);
* the Kyber coins are `initiateKemCoins t` (DEV-PQ6);
* the peer is trusted (DEV-PQ5).

Kyber keys are raw (1568 bytes, no type byte), as in the model. -/
def initiateInput (W : PEParams) (me : LocalIdentity) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) : SignalPqxdh.InitiateKeysInput :=
  let idA := keyPairOf W.C me.idPriv
  { ikASk := vecU8 idA.privateKey.bytes
    ikAPk := vecU8 idA.publicKey.bytes
    ekASk := toU8 (t.toList.take 32)
    kemCoins := vecU8 (initiateKemCoins t)
    trustedPeer := true
    bundle :=
      { ikB := vecU8 b.idPub
        spkId := u32 b.spkId
        spkB := vecU8 b.spkPub
        spkSig := vecU8 b.spkSig
        opkB? := b.opk.map fun (i, k) => (u32 i, vecU8 k)
        pqspkId := u32 b.kpkId
        pqspkB := vecU8 b.kpkPub
        pqspkSig := vecU8 b.kpkSig } }

/-- **Alice's state after `init`** in the model, for party `P`, identity `me`, bundle
`b` and tape `t`, with the record extras it is encoded under (`none`: null):
1. `Model.initiateKeys` gives the handshake keys `(rk, ck, pqr)` and header (else null);
2. `initializeInitiatorSession` uses V1 SPQR (`pqxdhSpqrSession W`), Alice's and the peer's identity keys,
   the peer's signed pre-key as their ratchet key, and the ratchet key from tape bytes `160..192`
   (else null: all-zero DH);
3. `setUnacknowledgedPreKeyMessage`.

The ghost epochs are those of `Params.initA` (epoch 0, one receiver chain of epoch 0); they are not
encoded. -/
def initiateState (X : UnreachedPqxdhPrimitives) (W : PEParams) (P : Party) (me : LocalIdentity) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) : Option (RecordExtras × GhostState Bytes) :=
  match SignalPqxdh.Model.initiateKeys (modelPrims X W) (initiateInput W me b t) with
  | none => none
  | some (dk, hdr) =>
    let idA := keyPairOf W.C me.idPriv
    match initializeInitiatorSession W.C (pqxdhSpqrSession W) ⟨idA.publicKey⟩ ⟨⟨b.idPub⟩⟩ ⟨b.spkPub⟩
        (HKDF.bytesToKey32 (ofU8 dk.rootKey)) (HKDF.bytesToKey32 (ofU8 dk.chainKey))
        (HKDF.bytesToKey32 (ofU8 dk.pqrKey)) (HKDF.bytesToKey32 ((t.toList.drop 160).take 32)) with
    | .error _ => none
    | .ok st =>
      some (initiatorRecordExtras me b ⟨u8Vec 32 hdr.ekAPk⟩ (u8Vec 1568 hdr.kemCt),
        ⟨P, st.setUnacknowledgedPreKeyMessage, 0, [0]⟩)

/-! ## Bob's pre-key `recv` -/

/-- **Bob's pre-key material**: the pre-keys a pre-key message names, from Bob's stores
(`preKeysNamedBy`, `SignalSession/PqDir.lean`). -/
structure ResponderPreKeySecrets where
  /-- The signed pre-key id. -/
  spkId : BitVec 32
  /-- The signed pre-key's private key (any 32 bytes: deserialization clamps). -/
  spkPriv : List.Vector (BitVec 8) 32
  /-- The Kyber pre-key id. -/
  kpkId : BitVec 32
  /-- The Kyber1024 public key. -/
  kpkPub : List.Vector (BitVec 8) 1568
  /-- The Kyber1024 secret key. -/
  kpkSec : List.Vector (BitVec 8) 3168
  /-- The one-time pre-key (id, private key), if any. -/
  opk : Option (BitVec 32 × List.Vector (BitVec 8) 32)

/-- **A PQXDH pre-key message** (message version 4, with a Kyber payload). The inner `SignalMessage`
is arbitrary bytes. -/
structure PreKeyMessageFields where
  /-- The sender's registration id. -/
  regId : BitVec 32
  /-- The one-time pre-key id, if any. -/
  opkId : Option (BitVec 32)
  /-- The signed pre-key id. -/
  spkId : BitVec 32
  /-- The Kyber pre-key id. -/
  kpkId : BitVec 32
  /-- The Kyber1024 ciphertext (serialized behind type byte `0x08`). -/
  kyberCt : List.Vector (BitVec 8) 1568
  /-- The sender's base key (X25519 public key). -/
  baseKey : List.Vector (BitVec 8) 32
  /-- The sender's identity key (X25519 public key). -/
  idPub : List.Vector (BitVec 8) 32
  /-- The serialized inner `SignalMessage`. -/
  inner : List (BitVec 8)

/-- **The wire bytes of a pre-key message**, as `PreKeySignalMessage::new` writes them:
`versionByte 4 ‖ protobuf { pre_key_id?, base_key, identity_key, message, registration_id,
signed_pre_key_id, kyber_pre_key_id, kyber_ciphertext }`. -/
def PreKeyMessageFields.bytes (m : PreKeyMessageFields) : List (BitVec 8) :=
  versionByte currentVersion ::
    ProtoPreKeySignalMessage.encode
      { registrationId := some m.regId, preKeyId := m.opkId, signedPreKeyId := some m.spkId,
        kyberPreKeyId := some m.kpkId, kyberCiphertext := some (kyberKey m.kyberCt),
        baseKey := some (djbKey m.baseKey), identityKey := some (djbKey m.idPub),
        message := some m.inner }

/-- **Bob's record extras after his pre-key `recv`** (`process_prekey`): no pending pre-key (the
session model's flag is clear after the successful decryption, so `pending` / `kyber` are not
written), local registration id `me`'s, remote id the message's, `alice_base_key` the message's
base key, serialized. -/
def responderRecordExtras (me : LocalIdentity) (m : PreKeyMessageFields) : RecordExtras :=
  { pending := { preKeyId := none, signedPreKeyId := 0#32, baseKey := ⟨m.baseKey⟩,
                 timestamp := 0#64 }
    kyber := none
    remoteRegistrationId := m.regId
    localRegistrationId := me.regId
    aliceBaseKey := djbKey m.baseKey }

/-- **The model's input to `Model.acceptKeys`** for `me`, keys `k` and message `m`. Bob's identity
and pre-key pairs are derived as libsignal derives them (`keyPairOf`). The one-time pre-key is
`k`'s iff `m` names its id (otherwise `none`, and `acceptKeys` rejects a named but missing key).
Trusted peer (DEV-PQ5), no replay refusal (DEV-PQ8). -/
def acceptInput (W : PEParams) (me : LocalIdentity) (k : ResponderPreKeySecrets) (m : PreKeyMessageFields) :
    SignalPqxdh.AcceptKeysInput :=
  let idB := keyPairOf W.C me.idPriv
  let spk := keyPairOf W.C k.spkPriv
  { ikBSk := vecU8 idB.privateKey.bytes
    ikBPk := vecU8 idB.publicKey.bytes
    spkBSk := vecU8 spk.privateKey.bytes
    spkBPk := vecU8 spk.publicKey.bytes
    opkBSk? := match k.opk, m.opkId with
      | some (i, sk), some j => if i = j then some (vecU8 (keyPairOf W.C sk).privateKey.bytes)
                                else none
      | _, _ => none
    pqspkBSk := vecU8 k.kpkSec
    pqspkBPk := vecU8 k.kpkPub
    trustedPeer := true
    replayOk := true
    hdr :=
      { ikAPk := vecU8 m.idPub
        ekAPk := vecU8 m.baseKey
        spkId := u32 m.spkId
        opkId? := m.opkId.map u32
        pqspkId := u32 m.kpkId
        kemCt := vecU8 m.kyberCt } }

/-- **Bob's state after his pre-key `recv`** in the model, for party `P`, identity `me`, keys
`k`, message `m`, an empty record, and Bob's ratchet coins `rc`, with its record extras and the
plaintext (`none`: abort; `some none`: null). Each step's failure gives null:
1. the inner message parses (`SignalMessage.tryFrom`);
2. `m`'s signed and Kyber pre-key ids are `k`'s (`get_signed_pre_key`, `get_kyber_pre_key`);
3. `Model.acceptKeys` gives `(rk, ck, pqr)`;
4. `initializeRecipientSession` with V1 SPQR (`pqxdhSpqrSession W`) and the signed pre-key pair as Bob's
   ratchet key;
5. `tryDecryptFromRecord` (type `PreKey`, the addresses `P` expects, coins `rc`) gives the
   plaintext. A panic aborts.

The ghost epochs are those `Params.receive` gives from `Params.initB` on a first message (epoch 1,
one receiver chain of epoch 1); they are not encoded. -/
def recvPrekeyState (X : UnreachedPqxdhPrimitives) (W : PEParams) (P : Party) (me : LocalIdentity) (k : ResponderPreKeySecrets)
    (m : PreKeyMessageFields) (rc : BitVec 256) :
    Option (Option (RecordExtras × GhostState Bytes × Bytes)) :=
  match SignalMessage.tryFrom protoSignalCodec m.inner with
  | .error _ => some none
  | .ok inner =>
    if m.spkId ≠ k.spkId ∨ m.kpkId ≠ k.kpkId then some none
    else
      match SignalPqxdh.Model.acceptKeys (modelPrims X W) (acceptInput W me k m) with
      | none => some none
      | some dk =>
        let st0 : SessionState Bytes :=
          initializeRecipientSession (pqxdhSpqrSession W) ⟨(keyPairOf W.C me.idPriv).publicKey⟩
            ⟨⟨m.idPub⟩⟩ (keyPairOf W.C k.spkPriv) (HKDF.bytesToKey32 (ofU8 dk.rootKey))
            (HKDF.bytesToKey32 (ofU8 dk.chainKey)) (HKDF.bytesToKey32 (ofU8 dk.pqrKey))
        match SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W) ((pqxdhSessionParams W).expectedAddrs P) inner
            .preKey rc st0 with
        | (.ok pt, st) => some (some (responderRecordExtras me m, ⟨P, st, 1, [1]⟩, pt))
        | (.error .panic, _) => none
        | (.error _, _) => some none

/-! ## The bundle's signatures -/

/-- **The bundle's two signatures verify**, exactly as `Model.initiateKeys` checks them (the
model's `sigVerify`, i.e. `xeddsaVerifyRef` at `modelPrims`): the signed pre-key's signature on
`0x05 ‖ spk_pub` and the Kyber pre-key's on `0x08 ‖ kpk_pub`, both under `id_pub`
(`process_prekey_bundle`, `rust/protocol/src/session.rs`). -/
def PreKeyBundleFields.signaturesVerify (X : UnreachedPqxdhPrimitives) (W : PEParams) (b : PreKeyBundleFields) : Bool :=
  let i := initiateInput W ⟨List.Vector.replicate 32 0#8, 0⟩ b
    (List.Vector.replicate initiateTapeLen 0#8)
  (modelPrims X W).sigVerify i.bundle.ikB (SignalPqxdh.encodeEC i.bundle.spkB) i.bundle.spkSig &&
    (modelPrims X W).sigVerify i.bundle.ikB (SignalPqxdh.encodeKEM i.bundle.pqspkB)
      i.bundle.pqspkSig

end CryptoVerification.E2E

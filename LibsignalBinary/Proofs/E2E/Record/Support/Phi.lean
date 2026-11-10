/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionApi
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionSM
public import LibsignalBinary.Specifications.LibsignalProtoCodec
public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDecDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.EffSalt
public import LibsignalBinary.Specifications.CryptoGames.AEAD.EtMDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HKDFDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HMACDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.LibsignalAead
public import LibsignalBinary.Specifications.CryptoGames.AEAD.MacPrecompDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.WireAeadDefs
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Construction
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Defs
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Security
public import LibsignalBinary.Specifications.CryptoGames.PRNG.Defs
public import LibsignalBinary.Specifications.CryptoGames.Party
public import LibsignalBinary.Specifications.CryptoGames.Primitives
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.ChainDefs
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.CreateChainDefs
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSession
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.RootKdfDefs
public import LibsignalBinary.Specifications.HkdfSalt
public import LibsignalBinary.Specifications.LibsignalSignalMessage

/-!
# Protobuf `storage.proto` encoders, `SessionExtras`, and `encodeRecord`

Defines the functional `storage.proto` wire-format encoders (`encodeRecord`, `encSession`,
`encSenderChain`, `encReceiverChain`), `GhostState.afterRecv`, and `toRecord`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E.Record

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalProtoCodec
abbrev Bytes := List (BitVec 8)

/-- Post-receive `GhostState` bookkeeping (`Params.receive` success branch): returns the updated
`GhostState`, chain epoch (`epoch + 1` on a new ratchet key), evicted receiver-chain epochs, and
message index `counter + 1`. -/
def _root_.CryptoGames.LibsignalSession.GhostState.afterRecv {PQ : Type} (g : GhostState PQ)
    (rk : PublicKey) (counter : BitVec 32) (s : SessionState PQ) (m : Bytes) :
    GhostState PQ × ℕ × ℕ × Bytes :=
  let idx := g.session.receiverChains.findIdx? (·.senderRatchetKey == rk)
  let (t, epochs, cur) := match idx with
    | some i => (g.chainEpochs.getD i 0, g.chainEpochs, g.epoch)
    | none => (g.epoch + 1, g.chainEpochs ++ [g.epoch + 1], g.epoch + 1)
  let epochs := epochs.drop (epochs.length - s.receiverChains.length)
  ({ g with session := s, epoch := cur, chainEpochs := epochs }, t, counter.toNat + 1, m)

/-- `Params.receive` unfolds to `GhostState.afterRecv` on `SignalMessage.tryFrom` and `SessionState.tryDecryptFromRecord`. -/
theorem receive_eq_afterRecv {PQ PQC : Type} [Inhabited PQ] (P : Params PQ PQC)
    (g : GhostState PQ) (c : Bytes) (rc : BitVec 256) :
    P.receive g c rc =
      match SignalMessage.tryFrom P.codec c with
      | .error _ => none
      | .ok msg =>
        match SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party) msg .whisper
            rc g.session with
        | (.error _, _) => none
        | (.ok m, s) => some (g.afterRecv msg.senderRatchetKey msg.counter s m) := by
  unfold Params.receive GhostState.afterRecv
  cases SignalMessage.tryFrom P.codec c with
  | error _ => rfl
  | ok msg =>
    rcases SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party) msg .whisper
        rc g.session with ⟨res, s⟩
    cases res <;> rfl

/-- A length-delimited field: key, length, payload. -/
def lenField (tag : ℕ) (payload : List (BitVec 8)) : List (BitVec 8) :=
  encodeKey tag .lengthDelimited ++ encodeVarint (BitVec.ofNat 64 payload.length) ++ payload

/-- proto3 `bytes`: omitted when empty. -/
def bytesField (tag : ℕ) (v : List (BitVec 8)) : List (BitVec 8) :=
  if v = [] then [] else lenField tag v

/-- proto3 `uint32`: omitted when 0. -/
def uint32Field (tag : ℕ) (v : BitVec 32) : List (BitVec 8) :=
  if v = 0 then [] else encodeKey tag .varint ++ encodeVarint (v.setWidth 64)

/-- proto3 `uint64`: omitted when 0. -/
def uint64Field (tag : ℕ) (v : BitVec 64) : List (BitVec 8) :=
  if v = 0 then [] else encodeKey tag .varint ++ encodeVarint v

/-- proto3 `int32`: omitted when 0; a negative value is sign-extended to 64 bits. -/
def int32Field (tag : ℕ) (v : BitVec 32) : List (BitVec 8) :=
  if v = 0 then [] else encodeKey tag .varint ++ encodeVarint (v.signExtend 64)

/-- `optional uint32` (explicit presence): written whenever `some`. -/
def optUint32Field (tag : ℕ) : Option (BitVec 32) → List (BitVec 8)
  | none => []
  | some v => encodeKey tag .varint ++ encodeVarint (v.setWidth 64)

/-- A sub-message: written whenever present (even if its encoding is empty). -/
def msgField (tag : ℕ) : Option (List (BitVec 8)) → List (BitVec 8)
  | none => []
  | some body => lenField tag body

/-! ## Messages of `storage.proto` -/

/-- `Chain.ChainKey { uint32 index = 1; bytes key = 2; }` (the key's 32 little-endian bytes). -/
def encChainKey (ck : ChainKey) : List (BitVec 8) :=
  uint32Field 1 ck.index ++ bytesField 2 (HMAC.keyToBytes32 ck.key)

/-- `Chain.MessageKey` in its `Seed` form: `index = 1`, `seed = 5`. -/
def encMessageKey (mk : MessageKeyGenerator) : List (BitVec 8) :=
  uint32Field 1 mk.counter ++ bytesField 5 mk.seed

/-- `Chain` for the sending chain: public key, private key, chain key, no message keys. -/
def encSenderChain (c : SenderChain) : List (BitVec 8) :=
  bytesField 1 c.ratchetKey.publicKey.serialize ++ bytesField 2 c.ratchetKey.privateKey.bytes.toList ++
    msgField 3 (some (encChainKey c.chainKey))

/-- `Chain` for a receiving chain: public key, chain key, skipped message keys (oldest first). -/
def encReceiverChain (c : ReceiverChain) : List (BitVec 8) :=
  bytesField 1 c.senderRatchetKey.serialize ++ msgField 3 (c.chainKey.map encChainKey) ++
    (c.messageKeys.map fun mk => lenField 4 (encMessageKey mk)).flatten

/-- `PendingPreKey { optional uint32 pre_key_id = 1; bytes base_key = 2; int32 signed_pre_key_id = 3;
uint64 timestamp = 4; }`. -/
def encPendingPreKey (p : PendingPreKey) : List (BitVec 8) :=
  optUint32Field 1 p.preKeyId ++ bytesField 2 p.baseKey.serialize ++ int32Field 3 p.signedPreKeyId ++
    uint64Field 4 p.timestamp

/-- `PendingKyberPreKey { uint32 pre_key_id = 1; bytes ciphertext = 2; }`. -/
def encPendingKyber (p : PendingKyberPreKey) : List (BitVec 8) :=
  uint32Field 1 p.preKeyId ++ bytesField 2 p.ciphertext

/-- `SessionStructure`, fields in tag order 1–7, 9, 10, 11, 13, 14, 15. -/
def encSession (s : Session (List (BitVec 8))) : List (BitVec 8) :=
  let st := s.state
  uint32Field 1 st.sessionVersion ++
  bytesField 2 st.localIdentity.serialize ++
  bytesField 3 ((st.remoteIdentity.map IdentityKey.serialize).getD []) ++
  bytesField 4 (HMAC.keyToBytes32 st.rootKey) ++
  uint32Field 5 st.previousCounter ++
  msgField 6 (st.senderChain.map encSenderChain) ++
  (st.receiverChains.map fun c => lenField 7 (encReceiverChain c)).flatten ++
  msgField 9 (s.pendingPreKey.map encPendingPreKey) ++
  uint32Field 10 s.remoteRegistrationId ++
  uint32Field 11 s.localRegistrationId ++
  bytesField 13 s.aliceBaseKey ++
  msgField 14 (s.pendingKyberPreKey.map encPendingKyber) ++
  bytesField 15 st.pqRatchetState

/-- Encodes a `SessionRecord` as `RecordStructure { current_session = 1; }` (with no `previous_sessions`). -/
def encodeRecord (r : SessionRecord (List (BitVec 8))) : List (BitVec 8) :=
  msgField 1 (r.currentSession.map encSession)


/-! ## `SessionExtras` and `toRecord` -/

section MoveCompat
def spqrOffB : Spqr Bytes Unit :=
  ⟨fun _ _ => [], fun _ _ => some ([], none, []), fun _ _ => .ok ([], none), fun _ _ => false,
    fun _ _ => false⟩

structure SessionExtras where
  /-- `pending_pre_key` while the session is unacknowledged. -/
  pending : PendingPreKey
  /-- `pending_kyber_pre_key` while the session is unacknowledged (`none` = no Kyber payload). -/
  kyber : Option PendingKyberPreKey
  localRegistrationId : BitVec 32
  remoteRegistrationId : BitVec 32
  aliceBaseKey : Bytes

def toRecord (E : Party → SessionExtras) (g : GhostState Bytes) : SessionRecord Bytes :=
  { currentSession := some
      { state := g.session
        pendingPreKey := if g.session.pendingPreKey then some (E g.party).pending else none
        pendingKyberPreKey := if g.session.pendingPreKey then (E g.party).kyber else none
        localRegistrationId := (E g.party).localRegistrationId
        remoteRegistrationId := (E g.party).remoteRegistrationId
        aliceBaseKey := (E g.party).aliceBaseKey } }

def _root_.CryptoGames.LibsignalSession.GhostState.afterSend {PQ : Type} (g : GhostState PQ)
    (s : SessionState PQ) : GhostState PQ :=
  { g with session := s, epoch := if g.party.sendsIn g.epoch then g.epoch else g.epoch + 1 }

theorem send_eq_afterSend {PQ PQC : Type} [Inhabited PQ] (P : Params PQ PQC) (g : GhostState PQ)
    (m : Bytes) (r : PQC) :
    P.send g m r =
      match SessionState.messageEncrypt P.C P.codec P.spqr (P.sendAddrs g.party) m r g.session with
      | (.ok msg, s) => (g.afterSend s, msg.serialized)
      | (.error _, _) => (g, []) := rfl

def extrasM : Party → SessionExtras := fun _ =>
  { pending := { preKeyId := none, signedPreKeyId := 0#32,
                 baseKey := ⟨List.Vector.replicate 32 0#8⟩, timestamp := 0#64 }
    kyber := none
    localRegistrationId := 0#32
    remoteRegistrationId := 0#32
    aliceBaseKey := [] }

end MoveCompat

end CryptoVerification.E2E.Record

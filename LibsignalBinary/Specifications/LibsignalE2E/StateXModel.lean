/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionApi
public import LibsignalBinary.Specifications.LibsignalE2E.State
public import ProofLib.Lemmas

/-!
# Session-Record Encoding with PQXDH Extras (`encodeRecordUnderExtras`)

**Trusted: definitions used by the statement.** Generalizes `encodeRecord` (`State.lean`, DEV-M9)
from constant placeholder fields to the per-session public transcript fields `RecordExtras`
produced by a PQXDH handshake (`pending_pre_key`, `pending_kyber_pre_key` with Kyber1024 round-3
ciphertext per DEV-PQ2, registration IDs, and `alice_base_key`). Both pending sub-messages are
emitted iff `st.pendingPreKey` holds. See `Computational/docs/TRUSTED_BASE.md`.
-/

@[expose] public section

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.LibsignalSession CryptoVerification.LibsignalProtoCodec

/-! ## The record extras -/

/-- **The `SessionStructure` fields of one party's record that the session model does not
track**, constant over one session: the pending pre-key and pending Kyber pre-key (written only
while the session model's `pendingPreKey` flag is set), the registration ids and
`alice_base_key`. Field numbers: libsignal v0.105.4 `rust/protocol/src/proto/storage.proto`. -/
structure RecordExtras where
  /-- `pending_pre_key` (tag 9) while unacknowledged. -/
  pending : LibsignalSessionApi.PendingPreKey
  /-- `pending_kyber_pre_key` (tag 14) while unacknowledged (`none`: no Kyber payload). -/
  kyber : Option LibsignalSessionApi.PendingKyberPreKey
  /-- `remote_registration_id` (tag 10). -/
  remoteRegistrationId : BitVec 32
  /-- `local_registration_id` (tag 11). -/
  localRegistrationId : BitVec 32
  /-- `alice_base_key` (tag 13). -/
  aliceBaseKey : Bytes

/-! ## Field writers not needed by `State.lean` -/

/-- proto3 `uint64`: omitted when 0. -/
def uint64FieldX (tag : ℕ) (v : BitVec 64) : Bytes :=
  if v = 0 then [] else encodeKey tag .varint ++ encodeVarint v

/-- proto3 `int32`: omitted when 0; a negative value is sign-extended to 64 bits (prost). -/
def int32FieldX (tag : ℕ) (v : BitVec 32) : Bytes :=
  if v = 0 then [] else encodeKey tag .varint ++ encodeVarint (v.signExtend 64)

/-- `optional uint32` (explicit presence): written whenever `some`. -/
def optUint32FieldX (tag : ℕ) : Option (BitVec 32) → Bytes
  | none => []
  | some v => encodeKey tag .varint ++ encodeVarint (v.setWidth 64)

/-! ## Messages -/

/-- `PendingPreKey { optional uint32 pre_key_id = 1; bytes base_key = 2; int32 signed_pre_key_id = 3;
uint64 timestamp = 4; }`. -/
def encPendingPreKeyX (p : LibsignalSessionApi.PendingPreKey) : Bytes :=
  optUint32FieldX 1 p.preKeyId ++ bytesField 2 p.baseKey.serialize ++
    int32FieldX 3 p.signedPreKeyId ++ uint64FieldX 4 p.timestamp

/-- `PendingKyberPreKey { uint32 pre_key_id = 1; bytes ciphertext = 2; }`. -/
def encPendingKyberX (p : LibsignalSessionApi.PendingKyberPreKey) : Bytes :=
  uint32Field 1 p.preKeyId ++ bytesField 2 p.ciphertext

/-- **`SessionStructure` of a session-model state with extras `x`**, fields in tag order 1–7, 9,
10, 11, 13, 14, 15. The pending items (9, 14) are written exactly while the session model's
`pendingPreKey` flag is set. -/
def encStateUnderExtras (x : RecordExtras) (st : SessionState Bytes) : Bytes :=
  uint32Field 1 st.sessionVersion ++
  bytesField 2 st.localIdentity.serialize ++
  bytesField 3 ((st.remoteIdentity.map IdentityKey.serialize).getD []) ++
  bytesField 4 (HMAC.keyToBytes32 st.rootKey) ++
  uint32Field 5 st.previousCounter ++
  msgField 6 (st.senderChain.map encSenderChain) ++
  (st.receiverChains.map fun c => lenField 7 (encReceiverChain c)).flatten ++
  msgField 9 (if st.pendingPreKey then some (encPendingPreKeyX x.pending) else none) ++
  uint32Field 10 x.remoteRegistrationId ++
  uint32Field 11 x.localRegistrationId ++
  bytesField 13 x.aliceBaseKey ++
  msgField 14 (if st.pendingPreKey then x.kyber.map encPendingKyberX else none) ++
  bytesField 15 st.pqRatchetState

/-- **`SessionRecord::serialize` of a session-model state under extras `E`**:
`RecordStructure { current_session = 1; }` (no previous sessions). -/
def encodeRecordUnderExtras (E : Party → RecordExtras) (g : GhostState Bytes) : Bytes :=
  msgField 1 (some (encStateUnderExtras (E g.party) g.session))

/-- **The binary state of a session-model state under extras `E`**: the party, the record bytes
`encodeRecordUnderExtras E g`, and the epoch ghost `EpochGhost.ofGhost g`. -/
def binStateOfUnderExtras (E : Party → RecordExtras) (g : GhostState Bytes) : BinState :=
  ⟨g.party, encodeRecordUnderExtras E g, EpochGhost.ofGhost g⟩

end CryptoVerification.E2E

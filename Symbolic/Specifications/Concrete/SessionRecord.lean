/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.WireFormat

/-!
# Persisted Session Record Mirrors and Protobuf Codecs

Plain-data mirrors and proto3 serializers for `libsignal` persisted session records
(`SessionRecord`, `SessionStructure`, `Chain`), together with stored-secret membership
(`KeyInRecord`) and single-session promotion eligibility (`EligibleForSessionPromotion`).
-/

@[expose] public section

namespace DY.Libsignal.Rust

open DY.Libsignal (HwBytes)
open DY.Libsignal.Refinement (encodeField)
open DY.Libsignal.PQXDH.Refinement (parsePreKeyWire)

/-- Mirror of `session_structure::Chain`, with `messageKeys` in `(index, seed)` form. -/
structure ChainRec where
  senderRatchetKey : List (BitVec 8)
  senderRatchetKeyPrivate : List (BitVec 8)
  chainKey : Option (BitVec 32 × List (BitVec 8))
  messageKeys : List (BitVec 32 × List (BitVec 8))

/-- Mirror of `proto::storage::SessionStructure`. Pending pre-key submessages (`pendingPreKey`
field 9 and `pendingKyberPreKey` field 14) split into their leading byte vector and remaining raw
bytes. -/
structure SessionRec where
  sessionVersion : BitVec 32
  localIdentityPublic : List (BitVec 8)
  remoteIdentityPublic : List (BitVec 8)
  rootKey : List (BitVec 8)
  previousCounter : BitVec 32
  senderChain : Option ChainRec
  receiverChains : List ChainRec
  pendingPreKey : Option (List (BitVec 8) × List (BitVec 8))
  pendingKyberPreKey : Option (List (BitVec 8) × List (BitVec 8))
  remoteRegistrationId : BitVec 32
  localRegistrationId : BitVec 32
  aliceBaseKey : List (BitVec 8)
  pqRatchetState : List (BitVec 8)

/-- Mirror of `SessionRecord`: current session and serialized previous sessions (newest first). -/
structure RecordRec where
  current : SessionRec
  previous : List (List (BitVec 8))

/-- Encodes a proto3 `bytes` field (omitted when empty). -/
def bytesField (tag : Nat) (b : HwBytes) : HwBytes :=
  if b = [] then [] else encodeField tag 0 0 (.bytes b)

/-- Encodes a proto3 `uint32` field (omitted when zero). -/
def u32Field (tag : Nat) (v : BitVec 32) : HwBytes :=
  if v = 0 then [] else encodeField tag 0 0 (.varint v.toNat)

/-- Encodes a length-delimited submessage or repeated `bytes` element. -/
def msgField (tag : Nat) (body : HwBytes) : HwBytes := encodeField tag 0 0 (.bytes body)

def chainBytes (c : ChainRec) : HwBytes :=
  bytesField 1 c.senderRatchetKey ++ bytesField 2 c.senderRatchetKeyPrivate ++
    ((c.chainKey.map fun k => msgField 3 (u32Field 1 k.1 ++ bytesField 2 k.2)).getD []) ++
    c.messageKeys.flatMap fun k => msgField 4 (u32Field 1 k.1 ++ bytesField 5 k.2)

/-- Proto3 encoding of `rec`, writing pending pre-key submessages (fields 9 and 14) as raw payloads
`p.1 ++ p.2`. -/
def recordBytes (rec : RecordRec) : HwBytes :=
  let s := rec.current
  msgField 1 (u32Field 1 s.sessionVersion ++ bytesField 2 s.localIdentityPublic ++
    bytesField 3 s.remoteIdentityPublic ++ bytesField 4 s.rootKey ++
    u32Field 5 s.previousCounter ++ ((s.senderChain.map (msgField 6 ∘ chainBytes)).getD []) ++
    s.receiverChains.flatMap (msgField 7 ∘ chainBytes) ++
    ((s.pendingPreKey.map fun p => msgField 9 (p.1 ++ p.2)).getD []) ++
    u32Field 10 s.remoteRegistrationId ++ u32Field 11 s.localRegistrationId ++
    bytesField 13 s.aliceBaseKey ++
    ((s.pendingKyberPreKey.map fun p => msgField 14 (p.1 ++ p.2)).getD []) ++
    bytesField 15 s.pqRatchetState) ++
  rec.previous.flatMap (msgField 2)

/-- Whether `k` is a secret stored in `rec.current` (root key, chain key, ratchet private key,
cached skipped seed, or SPQR state). -/
def KeyInRecord (rec : RecordRec) (k : HwBytes) : Prop :=
  k = rec.current.rootKey ∨
  (∃ sc, rec.current.senderChain = some sc ∧
    (k = sc.senderRatchetKeyPrivate ∨ ∃ ck, sc.chainKey = some ck ∧ k = ck.2)) ∨
  (∃ rc ∈ rec.current.receiverChains,
    (rc.senderRatchetKeyPrivate ≠ [] ∧ k = rc.senderRatchetKeyPrivate) ∨
    (∃ ck, rc.chainKey = some ck ∧ k = ck.2) ∨ (∃ mk ∈ rc.messageKeys, k = mk.2)) ∨
  k = rec.current.pqRatchetState

/-- Whether `rec` encodes a single session (no archived previous sessions) whose `aliceBaseKey`
matches the outer base key of pre-key message `b`. -/
def EligibleForSessionPromotion (rec b : HwBytes) : Prop :=
  ∃ rr p, rec = recordBytes rr ∧ rr.previous = [] ∧ parsePreKeyWire b = some p ∧
    rr.current.aliceBaseKey = p.baseKey.take 33

end DY.Libsignal.Rust

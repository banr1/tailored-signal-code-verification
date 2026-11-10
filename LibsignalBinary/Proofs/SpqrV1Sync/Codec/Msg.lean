/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1Sync.Codec.VarintPure
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Assemble
public import Batteries.Tactic.OpenPrivate
public meta import LibsignalBinary.Proofs.SpqrV1Sync.Codec.VarintPure
public meta import LibsignalBinary.Specifications.LibsignalSpqrV1.Assemble
public import ProofLib

set_option autoImplicit false

/-!
# SPQR V1 Wire-Message Serialization Round-Trip

`Message.serialize m index` writes `[1] ++ varint epoch ++ varint index ++ [typeByte] ++ chunk`,
where the optional chunk (`encode_chunk`) is `varint chunk.index ++ chunk.data` (32 bytes) and is
absent for `.none` and `.ct1Ack _`. On reception, `msg_preamble` parses the version byte, nonzero
epoch, and 32-bit index, and `Message.deserialize` parses the payload type byte and chunk.

For every message with `m.epoch ≠ 0#64` and `m.payload ≠ .ct1Ack false` (epochs start at `1`, and
the `ct1Ack` wire tag always deserializes to `.ct1Ack true`), `msg_preamble` followed by
`Message.deserialize` recovers `(1, m.epoch, index)` and `m`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1Sync.Codec

open CryptoVerification.LibsignalSpqrV1 hiding WireType DecodeErr decodeVarint encodeVarint
open CryptoGames.LibsignalSession (ShaCompress)
/-- Trailing chunk bytes written after the message-type tag by `Message.serialize`. -/
def payloadBytes {P : PolyApi} : MessagePayload P → Bytes
  | .hdr c | .ek c | .ekCt1Ack c | .ct1 c | .ct2 c => encode_chunk c
  | .none | .ct1Ack _ => []

/-! ## Chunks -/

theorem decode_chunk_varint_data (P : PolyApi) (i : BitVec 16) (d : Bytes) (hd : d.length = 32)
    (rest : Bytes) :
    decode_chunk P (encode_varint (i.zeroExtend 64) [] ++ (d ++ rest)) =
      .ok (P.mkChunk i ⟨d, hd⟩, rest) := by
  unfold decode_chunk
  rw [decode_varint_encode_varint]
  simp only [bind, Except.bind]
  have hlen_lt : ¬ ((d ++ rest).length < 32) := by
    rw [List.length_append]
    omega
  have hi_gt : ¬ ((i.zeroExtend 64).toNat > 65535) := by
    rw [BitVec.zeroExtend, BitVec.toNat_setWidth]
    have := i.isLt
    omega
  have htake : (d ++ rest).take 32 = d := by
    rw [← hd]
    simp
  have hdrop : (d ++ rest).drop 32 = rest := by
    rw [← hd]
    simp
  have htrunc : (i.zeroExtend 64).truncate 16 = i := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.truncate, BitVec.zeroExtend, BitVec.toNat_setWidth, BitVec.toNat_setWidth]
    have := i.isLt
    omega
  simp only [hlen_lt, hi_gt, decide_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
    htake, hdrop, bytesToVector?, hd, ↓reduceDIte, htrunc]

theorem decode_chunk_encode_chunk (P : PolyApi)
    (hmk : ∀ c, P.mkChunk (P.chunkIndex c) (P.chunkData c) = c) (c : P.Chunk) (rest : Bytes) :
    decode_chunk P (encode_chunk c ++ rest) = .ok (c, rest) := by
  unfold encode_chunk
  rw [List.append_assoc]
  rw [decode_chunk_varint_data P (P.chunkIndex c) (P.chunkData c).toList
    (P.chunkData c).toList_length rest]
  have hvec :
      (⟨(P.chunkData c).toList, (P.chunkData c).toList_length⟩ : List.Vector (BitVec 8) 32) =
        P.chunkData c :=
    Subtype.ext rfl
  rw [hvec, hmk c]

theorem decode_chunk_encode_chunk_nil (P : PolyApi)
    (hmk : ∀ c, P.mkChunk (P.chunkIndex c) (P.chunkData c) = c) (c : P.Chunk) :
    decode_chunk P (encode_chunk c) = .ok (c, []) := by
  simpa using decode_chunk_encode_chunk P hmk c []

theorem spqrPolyApi_mkChunk (c : spqrPolyApi.Chunk) :
    spqrPolyApi.mkChunk (spqrPolyApi.chunkIndex c) (spqrPolyApi.chunkData c) = c := by
  cases c
  rfl

theorem serialize_eq {P : PolyApi} (m : Message P) (index : BitVec 32) :
    m.serialize index =
      1#8 :: (encode_varint m.epoch [] ++ (encode_varint (index.zeroExtend 64) [] ++
        ((MessageType.from_payload m.payload).toU8 :: payloadBytes m.payload))) := by
  unfold Message.serialize payloadBytes encode_chunk encode_varint
  cases m.payload <;> simp [List.append_assoc]

theorem msg_preamble_serialize {P : PolyApi} (m : Message P) (index : BitVec 32)
    (he : m.epoch ≠ 0#64) :
    msg_preamble (m.serialize index) =
      .ok { version := 1#8, epoch := m.epoch, index := index,
            remaining := (MessageType.from_payload m.payload).toU8 :: payloadBytes m.payload } := by
  rw [serialize_eq]
  unfold msg_preamble
  dsimp only
  rw [decode_varint_encode_varint]
  simp only [bind, Except.bind, he, ↓reduceIte]
  rw [decode_varint_encode_varint]
  dsimp only
  have hlt : (index.zeroExtend 64).toNat < 2 ^ 32 := by
    rw [BitVec.zeroExtend, BitVec.toNat_setWidth]
    have := index.isLt
    omega
  have hset : (index.zeroExtend 64).setWidth 32 = index := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.zeroExtend, BitVec.toNat_setWidth, BitVec.toNat_setWidth]
    have := index.isLt
    omega
  simp only [hlt, ↓reduceIte, hset]

theorem deserialize_payload (P : PolyApi)
    (hmk : ∀ c, P.mkChunk (P.chunkIndex c) (P.chunkData c) = c) (epoch : Epoch)
    (p : MessagePayload P) (hp : p ≠ .ct1Ack false) :
    Message.deserialize P epoch ((MessageType.from_payload p).toU8 :: payloadBytes p) =
      .ok { epoch := epoch, payload := p } := by
  cases p with
  | none =>
    simp [Message.deserialize, MessageType.from_payload, MessageType.toU8, MessageType.tryFromU8,
      bind, Except.bind]
  | ct1Ack b =>
    cases b with
    | false => exact False.elim (hp rfl)
    | true =>
      simp [Message.deserialize, MessageType.from_payload, MessageType.toU8, MessageType.tryFromU8,
        bind, Except.bind]
  | hdr c | ek c | ekCt1Ack c | ct1 c | ct2 c =>
    simp [Message.deserialize, MessageType.from_payload, MessageType.toU8, MessageType.tryFromU8,
      payloadBytes, decode_chunk_encode_chunk_nil P hmk c, bind, Except.bind]

/-- `msg_preamble` followed by `Message.deserialize` inverts `Message.serialize` whenever
`m.epoch ≠ 0#64` and `m.payload ≠ .ct1Ack false`. -/
theorem preamble_deserialize_serialize (P : PolyApi)
    (hmk : ∀ c, P.mkChunk (P.chunkIndex c) (P.chunkData c) = c) (m : Message P) (index : BitVec 32)
    (he : m.epoch ≠ 0#64) (hp : m.payload ≠ .ct1Ack false) :
    ∃ rem, msg_preamble (m.serialize index) =
        .ok { version := 1#8, epoch := m.epoch, index := index, remaining := rem } ∧
      Message.deserialize P m.epoch rem = .ok m := by
  refine ⟨(MessageType.from_payload m.payload).toU8 :: payloadBytes m.payload,
    msg_preamble_serialize m index he, ?_⟩
  have hdes := deserialize_payload P hmk m.epoch m.payload hp
  cases m
  exact hdes

/-- Specialization of `preamble_deserialize_serialize` to the concrete `spqrDeps F K` bundle. -/
theorem spqrDeps_preamble_msgDeserialize_serialize (F : ShaCompress) (K : MlKem)
    (m : Message spqrPolyApi) (index : BitVec 32) (he : m.epoch ≠ 0#64)
    (hp : m.payload ≠ .ct1Ack false) :
    ∃ rem, msgPreamble ((spqrDeps F K).msgSerialize m index) =
        .ok { version := 1#8, epoch := m.epoch, index := index, remaining := rem } ∧
      (spqrDeps F K).msgDeserialize m.epoch rem = .ok m := by
  obtain ⟨rem, hpre, hdes⟩ :=
    preamble_deserialize_serialize spqrPolyApi spqrPolyApi_mkChunk m index he hp
  refine ⟨rem, hpre, ?_⟩
  unfold spqrDeps
  dsimp only
  rw [hdes]

end CryptoVerification.SpqrV1Sync.Codec

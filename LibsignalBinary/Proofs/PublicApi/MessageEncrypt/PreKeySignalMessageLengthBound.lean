/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Callees

/-!
# Serialized Length Bound for `PreKeySignalMessage::new`

Pure upper bound `< 2 ^ 42` on the protobuf-serialized byte length produced by
`PreKeySignalMessage.new`, derived from the caller bounds `< 2 ^ 40` on the inner
`SignalMessage` and `< 2 ^ 32` on the optional Kyber ciphertext.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi

theorem varint_length_le (n : ℕ) : (Prost.varint n).length ≤ n / 128 + 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [Prost.varint]
    split
    · simp
    · have h := ih (n / 128) (by omega)
      simp only [List.length_cons]
      have : n / 128 / 128 + 1 ≤ n / 128 := by omega
      omega

theorem key_length (tag wt : ℕ) (ht : tag ≤ 15) (hw : wt ≤ 7) :
    (Prost.key tag wt).length = 1 := by
  unfold Prost.key
  rw [Prost.varint]
  split
  · rfl
  · omega

theorem uint32Field_length_le (tag : ℕ) (ht : tag ≤ 15) (v : Option (BitVec 32)) :
    (Prost.uint32Field tag v).length ≤ 2 ^ 25 + 2 := by
  cases v with
  | none => simp [Prost.uint32Field]
  | some v =>
    simp only [Prost.uint32Field, List.length_append, key_length tag 0 ht (by omega)]
    have h1 := varint_length_le v.toNat
    have h2 := v.isLt
    omega

theorem bytesField_length_le (tag : ℕ) (ht : tag ≤ 15) (b : List (BitVec 8)) :
    (Prost.bytesField tag (some b)).length ≤ 2 * b.length + 2 := by
  simp only [Prost.bytesField, List.length_append, key_length tag 2 ht (by omega)]
  have := varint_length_le b.length
  omega

/-- With the inner `SignalMessage` under `2 ^ 40` bytes and any Kyber ciphertext under `2 ^ 32`
bytes, `PreKeySignalMessage.new` serializes to fewer than `2 ^ 42` bytes. -/
theorem preKeySignalMessage_new_serialized_length_lt (ver : BitVec 8) (regId : BitVec 32)
    (preKeyId : Option (BitVec 32)) (spk : BitVec 32) (kp : Option KyberPayload)
    (baseKey : PublicKey) (ik : IdentityKey) (msg : SignalMessage)
    (hmsg : msg.serialized.length < 2 ^ 40)
    (hkp : ∀ k, kp = some k → k.ciphertext.length < 2 ^ 32) :
    (PreKeySignalMessage.new ver regId preKeyId spk kp baseKey ik msg).serialized.length <
      2 ^ 42 := by
  have hbk : baseKey.serialize.length = 33 := by
    simp [PublicKey.serialize, List.Vector.toList_length]
  have hik : ik.serialize.length = 33 := by
    simp [IdentityKey.serialize, PublicKey.serialize, List.Vector.toList_length]
  have f1 := uint32Field_length_le 1 (by omega) preKeyId
  have f2 := bytesField_length_le 2 (by omega) baseKey.serialize
  have f3 := bytesField_length_le 3 (by omega) ik.serialize
  have f4 := bytesField_length_le 4 (by omega) msg.serialized
  have f5 := uint32Field_length_le 5 (by omega) (some regId)
  have f6 := uint32Field_length_le 6 (by omega) (some spk)
  have f7 := uint32Field_length_le 7 (by omega) (kp.map (·.preKeyId))
  have f8 : (Prost.bytesField 8 (kp.map (·.ciphertext))).length ≤ 2 * 2 ^ 32 + 2 := by
    cases kp with
    | none => simp [Prost.bytesField]
    | some k =>
      have := bytesField_length_le 8 (by omega) k.ciphertext
      have := hkp k rfl
      simp only [Option.map_some]
      omega
  simp only [PreKeySignalMessage.new, ProtoPreKeySignalMessage.encode, List.length_cons,
    List.length_append]
  omega

theorem PreKeyMsgNewCall.model_serialized_length_lt (x : PreKeyMsgNewCall)
    (hmsg : x.msg.serialized.length < 2 ^ 40)
    (hkp : ∀ k, x.kp = some k → k.ciphertext.length < 2 ^ 32) :
    x.model.serialized.length < 2 ^ 42 :=
  preKeySignalMessage_new_serialized_length_lt _ _ _ _ _ _ _ _ hmsg hkp

end CryptoVerification.LibsignalPublicApi.MessageEncrypt

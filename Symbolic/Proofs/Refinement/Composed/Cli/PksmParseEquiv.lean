/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Model
public import Symbolic.Proofs.Refinement.EncodeWithCovered
public import Symbolic.Specifications.Refinement.TraceExplanation
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0Lemmas.Ok -- shake: keep

/-!
# Equivalence of `Pksm.pksmParse` and `parsePreKey`

Proves that `decodePreKey` equals `(Pksm.decodeProto ·).map protoToPreKeyMsg` and characterizes
the joint behavior of `Pksm.pksmParse` and `parsePreKey` on every byte list via
`PreKeyFieldsAgree`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Refinement.Composed.Cli

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.SignalSession.Cli.RunProofs
open DY.Libsignal.PQXDH.Refinement (PreKeyProto wirePrekeyTag)
open DY.Libsignal.Composed.Refinement
  (PreKeyFields emptyPreKeyMsg mergePreKeyField decodePreKeyLoop decodePreKey
   ecKeyParses parsePreKey parsePreKeyWire EligibleForSessionPromotion
   bytesField u32Field msgField chainBytes recordBytes)

/-! ## Protobuf decoder equivalence -/

/-- Converts `ProtoPreKeySignalMessage` to `PreKeyProto`. -/
def protoToPreKeyMsg (m : ProtoPreKeySignalMessage) : PreKeyProto where
  registrationId := m.registrationId
  preKeyId := m.preKeyId
  signedPreKeyId := m.signedPreKeyId
  kyberPreKeyId := m.kyberPreKeyId
  kyberCiphertext := m.kyberCiphertext
  baseKey := m.baseKey
  identityKey := m.identityKey
  message := m.message

@[simp]
theorem protoToPreKeyMsg_emptyProto :
    protoToPreKeyMsg Pksm.emptyProto = emptyPreKeyMsg := rfl

theorem mergePreKeyField_protoToPreKeyMsg (m : ProtoPreKeySignalMessage)
    (tag : Nat) (wt : WireType) (bs : List (BitVec 8)) :
    mergePreKeyField (protoToPreKeyMsg m) tag wt bs =
      (Pksm.mergeProtoField m tag wt bs).map (fun (m', r) => (protoToPreKeyMsg m', r)) := by
  rcases tag with _ | _ | _ | _ | _ | _ | _ | _ | _ | tag <;>
    simp [mergePreKeyField, Pksm.mergeProtoField, Option.map_map, Function.comp_def,
      protoToPreKeyMsg]

theorem decodePreKeyLoop_protoToPreKeyMsg :
    ∀ (fuel : Nat) (m : ProtoPreKeySignalMessage) (bs : List (BitVec 8)),
      decodePreKeyLoop fuel (protoToPreKeyMsg m) bs =
        (Pksm.decodeProtoLoop fuel m bs).map protoToPreKeyMsg
  | _, _, [] => by simp [decodePreKeyLoop, Pksm.decodeProtoLoop]
  | 0, _, _ :: _ => by simp [decodePreKeyLoop, Pksm.decodeProtoLoop]
  | fuel + 1, m, b :: bs => by
    simp only [decodePreKeyLoop, Pksm.decodeProtoLoop]
    cases decodeKey (b :: bs) with
    | none => rfl
    | some kr =>
      rcases kr with ⟨⟨tag, wt⟩, rest⟩
      simp only [mergePreKeyField_protoToPreKeyMsg]
      cases Pksm.mergeProtoField m tag wt rest with
      | none => rfl
      | some mr =>
        rcases mr with ⟨m', rest'⟩
        simp only [Option.map_some]
        exact decodePreKeyLoop_protoToPreKeyMsg fuel m' rest'

theorem decodePreKey_eq_map_decodeProto (body : List (BitVec 8)) :
    decodePreKey body = (Pksm.decodeProto body).map protoToPreKeyMsg := by
  unfold decodePreKey Pksm.decodeProto
  rw [← protoToPreKeyMsg_emptyProto]
  exact decodePreKeyLoop_protoToPreKeyMsg body.length Pksm.emptyProto body

/-! ## Version, Kyber, and Curve25519 key helpers -/

private theorem version_out_of_range_iff (ver : BitVec 8) :
    (ver < preKyberVersion ∨ currentVersion < ver) ↔ (ver.toNat < 3 ∨ 4 < ver.toNat) := by
  simp [preKyberVersion, currentVersion, BitVec.lt_def]

private theorem kyberOk_eq_bool (ver : BitVec 8) (m : ProtoPreKeySignalMessage) :
    Pksm.kyberOk ver m =
      (((protoToPreKeyMsg m).kyberPreKeyId.isSome &&
          (protoToPreKeyMsg m).kyberCiphertext.isSome) ||
        ((protoToPreKeyMsg m).kyberPreKeyId.isNone &&
          (protoToPreKeyMsg m).kyberCiphertext.isNone &&
          decide (ver.toNat ≤ 3))) := by
  have hle : decide (ver ≤ preKyberVersion) = decide (ver.toNat ≤ 3) := by
    simp [preKyberVersion, BitVec.le_def]
  simp [Pksm.kyberOk, protoToPreKeyMsg, hle]

private theorem kyberPayloadOf_projections {ver : BitVec 8} {m : ProtoPreKeySignalMessage}
    (hk : Pksm.kyberOk ver m = true) :
    m.kyberPreKeyId = (Pksm.kyberPayloadOf m.kyberPreKeyId m.kyberCiphertext).map (·.preKeyId) ∧
      m.kyberCiphertext =
        (Pksm.kyberPayloadOf m.kyberPreKeyId m.kyberCiphertext).map (·.ciphertext) := by
  rcases hkid : m.kyberPreKeyId with _ | kid <;> rcases hct : m.kyberCiphertext with _ | ct
  · exact ⟨rfl, rfl⟩
  · simp [Pksm.kyberOk, hkid, hct] at hk
  · simp [Pksm.kyberOk, hkid, hct] at hk
  · exact ⟨rfl, rfl⟩

private theorem ecKeyParses_of_deserialize_ok {b : List (BitVec 8)} {k : PublicKey}
    (h : PublicKey.deserialize b = .ok k) :
    ecKeyParses b = true ∧ b.take 33 = k.serialize ∧ b.take 33 = 5#8 :: k.bytes.toList := by
  cases b with
  | nil => simp [PublicKey.deserialize] at h
  | cons t rest =>
    dsimp only [PublicKey.deserialize] at h
    by_cases ht : t = djbType
    · subst ht
      by_cases hl : 32 ≤ rest.length
      · simp only [ne_eq, not_true_eq_false, ↓reduceIte, hl, ↓reduceDIte, Except.ok.injEq] at h
        subst h
        refine ⟨?_, rfl, rfl⟩
        simp [ecKeyParses, djbType]
        omega
      · simp [hl] at h
    · simp [ht] at h

private theorem ecKeyParses_false_of_deserialize_err {b : List (BitVec 8)}
    {e : SignalProtocolError} (h : PublicKey.deserialize b = .error e) :
    ecKeyParses b = false := by
  cases b with
  | nil => rfl
  | cons t rest =>
    unfold PublicKey.deserialize at h
    by_cases ht : t = djbType
    · subst ht
      by_cases hl : 32 ≤ rest.length
      · simp [hl] at h
      · simp [ecKeyParses, djbType]
        omega
    · have ht' : t ≠ 5#8 := ht
      simp [ecKeyParses, ht']

/-! ## Joint parse equivalence -/

/-- Fieldwise correspondence between `pm : PreKeySignalMessage` from `Pksm.pksmParse body`
and `q : PreKeyFields` from `parsePreKey body`. -/
structure PreKeyFieldsAgree (body : List (BitVec 8))
    (pm : PreKeySignalMessage) (q : PreKeyFields) : Prop where
  version_eq : q.version = pm.messageVersion.toNat
  preKeyId_eq : q.preKeyId = pm.preKeyId
  signedPreKeyId_eq : q.signedPreKeyId = pm.signedPreKeyId
  kyberPreKeyId_eq : q.kyberPreKeyId = pm.kyberPayload.map (·.preKeyId)
  kyberCiphertext_eq : q.kyberCiphertext = pm.kyberPayload.map (·.ciphertext)
  baseKey_take33_eq : q.baseKey.take 33 = pm.baseKey.serialize
  identityKey_take33_eq : q.identityKey.take 33 = 5#8 :: pm.identityKey.publicKey.bytes.toList
  inner_eq : q.inner = pm.message
  tryFrom_message_eq : SignalMessage.tryFrom protoSignalCodec q.message = .ok pm.message
  message_serialized_eq : pm.message.serialized = q.message
  serialized_eq : pm.serialized = body

/-- Joint outcome characterization of `Pksm.pksmParse body` and `parsePreKey body` on every byte
string `body`. -/
theorem pksmParse_parsePreKey_cases (body : List (BitVec 8)) :
    (Pksm.pksmParse body = none ∧ parsePreKey body = none) ∨
      ∃ (pm : PreKeySignalMessage) (q : PreKeyFields),
        Pksm.pksmParse body = some pm ∧
          parsePreKey body = some q ∧
          PreKeyFieldsAgree body pm q := by
  cases body with
  | nil => exact Or.inl ⟨rfl, rfl⟩
  | cons vb rest =>
    unfold Pksm.pksmParse parsePreKey
    dsimp only
    by_cases hver : (vb >>> 4) < preKyberVersion ∨ currentVersion < (vb >>> 4)
    · have hver' : (vb >>> 4).toNat < 3 ∨ 4 < (vb >>> 4).toNat :=
        (version_out_of_range_iff (vb >>> 4)).mp hver
      exact Or.inl ⟨by simp only [hver, ↓reduceIte], by simp only [hver', ↓reduceIte]⟩
    · have hver' : ¬ ((vb >>> 4).toNat < 3 ∨ 4 < (vb >>> 4).toNat) :=
        fun h => hver ((version_out_of_range_iff (vb >>> 4)).mpr h)
      simp only [hver, hver', ↓reduceIte, decodePreKey_eq_map_decodeProto]
      cases hdec : Pksm.decodeProto rest with
      | none => exact Or.inl ⟨rfl, rfl⟩
      | some m =>
        dsimp only [Option.map_some, protoToPreKeyMsg]
        cases hbk : m.baseKey with
        | none => exact Or.inl ⟨rfl, rfl⟩
        | some bk =>
          cases hik : m.identityKey with
          | none => exact Or.inl ⟨rfl, rfl⟩
          | some ik =>
            cases hmsg : m.message with
            | none => exact Or.inl ⟨rfl, rfl⟩
            | some msg =>
              cases hsid : m.signedPreKeyId with
              | none => exact Or.inl ⟨rfl, rfl⟩
              | some sid =>
                dsimp only
                have hkyb_eq := kyberOk_eq_bool (vb >>> 4) m
                dsimp only [protoToPreKeyMsg] at hkyb_eq
                cases hkyb : Pksm.kyberOk (vb >>> 4) m
                · rw [hkyb] at hkyb_eq
                  refine Or.inl ⟨by simp only [Bool.false_eq_true, ↓reduceIte], ?_⟩
                  rw [← hkyb_eq]
                  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
                · have hkyb' := hkyb_eq.symm.trans hkyb
                  simp only [↓reduceIte, hkyb', Bool.true_and]
                  cases hbk_d : PublicKey.deserialize bk with
                  | error e =>
                    have hec := ecKeyParses_false_of_deserialize_err hbk_d
                    exact Or.inl ⟨rfl, by simp [hec]⟩
                  | ok baseKey =>
                    obtain ⟨hec_bk, hbk33, _⟩ := ecKeyParses_of_deserialize_ok hbk_d
                    cases hik_d : PublicKey.deserialize ik with
                    | error e =>
                      have hec := ecKeyParses_false_of_deserialize_err hik_d
                      exact Or.inl ⟨rfl, by simp [hec_bk, hec]⟩
                    | ok idKey =>
                      obtain ⟨hec_ik, _, hik33⟩ := ecKeyParses_of_deserialize_ok hik_d
                      simp only [hec_bk, hec_ik, Bool.and_self, ↓reduceIte]
                      cases htry : SignalMessage.tryFrom protoSignalCodec msg with
                      | error e => exact Or.inl ⟨rfl, rfl⟩
                      | ok inner =>
                        obtain ⟨hkid_eq, hkct_eq⟩ := kyberPayloadOf_projections hkyb
                        refine Or.inr ⟨_, _, rfl, rfl, ?_⟩
                        exact
                          { version_eq := rfl
                            preKeyId_eq := rfl
                            signedPreKeyId_eq := rfl
                            kyberPreKeyId_eq := hkid_eq
                            kyberCiphertext_eq := hkct_eq
                            baseKey_take33_eq := hbk33
                            identityKey_take33_eq := hik33
                            inner_eq := rfl
                            tryFrom_message_eq := htry
                            message_serialized_eq := DecPkS0.tryFrom_serialized htry
                            serialized_eq := rfl }

section RecordAliceBaseKey

end RecordAliceBaseKey

end Symbolic.Proofs.Refinement.Composed.Cli

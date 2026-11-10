/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Refinement.Composed.Cli.Model
import Symbolic.Proofs.Refinement.Composed.Cli.ParD3ProtoCodec

/-!
# Pre-Key Parser Round-Trips and Overlap Consistency Lemmas

Proves inversion and canonical `m.bytes` evaluation lemmas for `parsePreKey`, `decodePreKey`, and
`preKeyOfBody?`, and establishes equivalence between `PqFieldsMatch` and `PqSessionMatches` and
between `pqRecvMatchingFieldsModel` and `pqRecvPrekeyModel` on typed pre-key messages.
-/

@[expose] public section

set_option autoImplicit false

namespace DY.Libsignal.Composed.Refinement.Cli

open DY.Libsignal (HwBytes)
open DY.Libsignal.PQXDH.Refinement (PreKeyProto wirePrekeyTag)
open DY.Libsignal.Composed.Refinement
  (PreKeyFields ecKeyParses parsePreKey parsePreKeyWire decodePreKey preKeyWire ecKey vec32)
open CryptoGames.LibsignalSession (GhostState SessionState SignalMessage)
open CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E
  (PreKeyMessageFields UnreachedPqxdhPrimitives PEParams RecordExtras wireWhisper wirePrekey djbKey pqxdhSpqrSession pqxdhSessionParams)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.SignalSession
  (Inputs Outcome Address PqParty filesOf sessionFile pqRecvInputs pqxdhExpectedOutcome pqRecvPrekeyModel
   PqSessionMatches PqxdhPartyInSpecDomain OutcomeMatchesModelExceptPath partyAddress preKeysNamedBy markKyberUsed removeOpk)

/-! ## Parser inversions -/

theorem wirePrekey_eq_wirePrekeyTag : wirePrekey = wirePrekeyTag := by decide

@[simp]
theorem parsePreKeyWire_wirePrekey_cons (body : HwBytes) :
    parsePreKeyWire (wirePrekey :: body) = parsePreKey body := by
  unfold parsePreKeyWire; rw [wirePrekey_eq_wirePrekeyTag]; simp

theorem ecKeyParses_take33 {b : HwBytes} (h : ecKeyParses b = true) :
    b.take 33 = 5#8 :: (vec32 (b.drop 1)).toList := by
  unfold ecKeyParses at h
  cases b with
  | nil => simp at h
  | cons hd tl =>
    simp only [List.head?_cons, Bool.and_eq_true, beq_iff_eq, Option.some.injEq,
      decide_eq_true_eq, List.length_cons] at h
    rcases h with ⟨rfl, hlen⟩
    have hvec : (vec32 tl).toList = tl.take 32 := by
      change (tl ++ List.replicate 32 0#8).take 32 = tl.take 32
      exact List.take_append_of_le_length (by omega)
    dsimp only [List.drop_succ_cons, List.drop_zero, List.take_succ_cons]
    exact congrArg (5#8 :: ·) hvec.symm

theorem parsePreKey_some_inv {body : HwBytes} {q : PreKeyFields}
    (hq : parsePreKey body = some q) :
    ecKeyParses q.baseKey = true ∧ ecKeyParses q.identityKey = true ∧
      SignalMessage.tryFrom protoSignalCodec q.message = .ok q.inner ∧
      (q.version = 3 ∨ q.version = 4) := by
  cases body with
  | nil => simp [parsePreKey] at hq
  | cons vb rest =>
    unfold parsePreKey at hq; dsimp only at hq
    split_ifs at hq with hver
    cases hdec : decodePreKey rest with
    | none => rw [hdec] at hq; cases hq
    | some raw =>
      rw [hdec] at hq
      rcases hbk : raw.baseKey with _ | bk; · simp [hbk] at hq
      rcases hik : raw.identityKey with _ | ik; · simp [hbk, hik] at hq
      rcases hmsg : raw.message with _ | msg; · simp [hbk, hik, hmsg] at hq
      rcases hsid : raw.signedPreKeyId with _ | sid; · simp [hbk, hik, hmsg, hsid] at hq
      simp only [hbk, hik, hmsg, hsid] at hq
      split_ifs at hq with hok
      cases htry : SignalMessage.tryFrom protoSignalCodec msg with
      | error _ => rw [htry] at hq; cases hq
      | ok inner =>
        rw [htry] at hq; injection hq with hq_eq; subst hq_eq
        simp only [Bool.and_eq_true] at hok
        exact ⟨hok.1.2, hok.2, htry, by dsimp; omega⟩

theorem preKeyOfBody?_some_inv {body : HwBytes} {m : PreKeyMessageFields}
    (hm : preKeyOfBody? body = some m) :
    ∃ q : PreKeyFields,
      parsePreKey body = some q ∧ q.version = 4 ∧ m.inner = q.message ∧
      m.idPub = vec32 (q.identityKey.drop 1) ∧ q.baseKey.take 33 = djbKey m.baseKey ∧
      SignalMessage.tryFrom protoSignalCodec m.inner = .ok q.inner := by
  unfold preKeyOfBody? at hm
  rcases hq : parsePreKey body with _ | q; · rw [hq] at hm; cases hm
  rcases hraw : decodePreKey (body.drop 1) with _ | raw; · rw [hq, hraw] at hm; cases hm
  rw [hq, hraw] at hm; dsimp only at hm
  split_ifs at hm with hv4
  rcases hkid : q.kyberPreKeyId with _ | kid; · rw [hkid] at hm; cases hm
  rcases hct : q.kyberCiphertext with _ | (_ | ⟨t, ct⟩) <;> try (rw [hkid, hct] at hm; cases hm)
  rw [hkid, hct] at hm; dsimp only at hm
  split at hm
  · injection hm with hm_eq; subst hm_eq
    obtain ⟨hbk_ok, _, htry, _⟩ := parsePreKey_some_inv hq
    exact ⟨q, rfl, hv4, rfl, rfl, ecKeyParses_take33 hbk_ok, htry⟩
  · cases hm

/-! ## Canonical `m.bytes` evaluations and matching equivalence -/

private theorem vec32_toList (v : List.Vector (BitVec 8) 32) : vec32 v.toList = v := by
  apply Subtype.ext
  change (v.toList ++ List.replicate 32 0#8).take 32 = v.toList
  have hlen : v.toList.length = 32 := v.2
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]

private theorem vec32_djbKey_drop1 (v : List.Vector (BitVec 8) 32) :
    vec32 ((djbKey v).drop 1) = v := vec32_toList v

theorem parsePreKey_bytes_eq (m : PreKeyMessageFields) (hlen : m.inner.length < 2 ^ 64) :
    parsePreKey m.bytes =
      match SignalMessage.tryFrom protoSignalCodec m.inner with
      | .ok inner =>
        some { version := 4, preKeyId := m.opkId, signedPreKeyId := m.spkId,
               kyberPreKeyId := some m.kpkId,
               kyberCiphertext := some (CryptoVerification.E2E.kyberKey m.kyberCt),
               baseKey := djbKey m.baseKey, identityKey := djbKey m.idPub,
               message := m.inner, inner }
      | .error _ => none := by
  rw [← parsePreKeyWire_wirePrekey_cons]
  exact parsePreKeyWire_preKeyMsgE m hlen

theorem decodePreKey_bytes_drop1 (m : PreKeyMessageFields) (hlen : m.inner.length < 2 ^ 64) :
    decodePreKey (m.bytes.drop 1) =
      some { registrationId := some m.regId, preKeyId := m.opkId, signedPreKeyId := some m.spkId,
             kyberPreKeyId := some m.kpkId,
             kyberCiphertext := some (DY.Libsignal.Composed.Refinement.kyberKey m.kyberCt.toList),
             baseKey := some (ecKey m.baseKey.toList),
             identityKey := some (ecKey m.idPub.toList),
             message := some m.inner } := by
  have hwire := preKeyWire_eq_preKeyMsgE_bytes m hlen
  have hdrop : m.bytes.drop 1 = PreKeyProto.encode
      { registrationId := some m.regId, preKeyId := m.opkId, signedPreKeyId := some m.spkId,
        kyberPreKeyId := some m.kpkId,
        kyberCiphertext := some (DY.Libsignal.Composed.Refinement.kyberKey m.kyberCt.toList),
        baseKey := some (ecKey m.baseKey.toList),
        identityKey := some (ecKey m.idPub.toList),
        message := some m.inner } := by
    have h2 := congrArg (fun l => (l.drop 1).drop 1) hwire
    simpa [preKeyWire, ecKey, DY.Libsignal.Composed.Refinement.kyberKey] using h2
  rw [hdrop]
  exact decodePreKey_encode _
    (by rintro _ ⟨⟩; have := m.baseKey.2; simp [ecKey])
    (by rintro _ ⟨⟩; have := m.idPub.2; simp [ecKey])
    (by rintro _ ⟨⟩; exact hlen)
    (by rintro _ ⟨⟩; have := m.kyberCt.2; simp [DY.Libsignal.Composed.Refinement.kyberKey])

theorem preKeyOfBody?_bytes_eq (m : PreKeyMessageFields) (hlen : m.inner.length < 2 ^ 64) :
    preKeyOfBody? m.bytes =
      match SignalMessage.tryFrom protoSignalCodec m.inner with
      | .ok _ => some m
      | .error _ => none := by
  unfold preKeyOfBody?
  rw [parsePreKey_bytes_eq m hlen, decodePreKey_bytes_drop1 m hlen]
  cases SignalMessage.tryFrom protoSignalCodec m.inner with
  | error _ => rfl
  | ok inner =>
    dsimp only [CryptoVerification.E2E.kyberKey]
    split
    · split
      · congr 1
        cases m with | mk regId opkId spkId kpkId kyberCt baseKey idPub msg =>
        rw [Option.getD_some, vec32_djbKey_drop1, vec32_djbKey_drop1]
        exact congrArg (fun k => PreKeyMessageFields.mk regId opkId spkId kpkId k baseKey idPub msg)
          (Subtype.ext rfl)
      · rename_i hnc; exact absurd ⟨rfl, m.kyberCt.2⟩ hnc
    · rename_i hne; exact absurd rfl hne

theorem preKeyOfBody?_bytes_of_parsePreKey_some {m : PreKeyMessageFields} {q : PreKeyFields}
    (hm : m.inner.length + 2048 < 2 ^ 32) (hq : parsePreKey m.bytes = some q) :
    preKeyOfBody? m.bytes = some m := by
  rw [parsePreKey_bytes_eq m (by omega)] at hq
  rw [preKeyOfBody?_bytes_eq m (by omega)]
  cases htry : SignalMessage.tryFrom protoSignalCodec m.inner with
  | ok _ => rfl
  | error _ => rw [htry] at hq; cases hq

theorem eq_of_preKeyOfBody?_bytes_some {m m' : PreKeyMessageFields}
    (hm : m.inner.length + 2048 < 2 ^ 32) (h : preKeyOfBody? m.bytes = some m') : m' = m := by
  rw [preKeyOfBody?_bytes_eq m (by omega)] at h
  cases htry : SignalMessage.tryFrom protoSignalCodec m.inner with
  | ok _ => rw [htry] at h; exact (Option.some.inj h).symm
  | error _ => rw [htry] at h; cases h

private theorem bv32_toNat_eq_four_iff (v : BitVec 32) : v.toNat = 4 ↔ v = 4#32 :=
  ⟨fun h => BitVec.eq_of_toNat_eq (by simpa using h), fun h => by rw [h]; rfl⟩

theorem pqFieldsMatch_iff_pqSessionMatches (x : RecordExtras) (g : GhostState HwBytes)
    {body : HwBytes} {q : PreKeyFields} {m : PreKeyMessageFields}
    (hq : parsePreKey body = some q) (hm : preKeyOfBody? body = some m) :
    PqFieldsMatch x g q ↔ PqSessionMatches x g m := by
  obtain ⟨q', hq', hv4, _, _, hbk, _⟩ := preKeyOfBody?_some_inv hm
  cases Option.some.inj (hq.symm.trans hq')
  unfold PqFieldsMatch PqSessionMatches
  rw [hbk, hv4]
  exact and_congr_right' (bv32_toNat_eq_four_iff g.session.sessionVersion)

theorem pqRecvMatchingFieldsModel_eq_pqRecvPrekeyModel (X : UnreachedPqxdhPrimitives) (P : PEParams)
    (st : PqParty) (x : RecordExtras) (g : GhostState HwBytes)
    {body : HwBytes} {q : PreKeyFields} {m : PreKeyMessageFields} (rc : BitVec 256)
    (_hwf : PqxdhPartyInSpecDomain P st) (hsess : st.session = some (x, g))
    (hq : parsePreKey body = some q) (hm : preKeyOfBody? body = some m)
    (hmatch : PqFieldsMatch x g q) :
    pqRecvMatchingFieldsModel P st x g q rc = pqRecvPrekeyModel X P st m rc := by
  have hpq : PqSessionMatches x g m := (pqFieldsMatch_iff_pqSessionMatches x g hq hm).mp hmatch
  obtain ⟨q', hq', _, _, hid, _, htry⟩ := preKeyOfBody?_some_inv hm
  cases Option.some.inj (hq.symm.trans hq')
  unfold pqRecvMatchingFieldsModel pqRecvPrekeyModel
  rw [htry, hid]; dsimp only
  cases st.trusts ⟨⟨vec32 (q.identityKey.drop 1)⟩⟩
  · rfl
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hsess, hpq]
    split_ifs
    · rfl
    · rcases SessionState.tryDecryptFromRecord P.C (pqxdhSpqrSession P)
          ((pqxdhSessionParams P).expectedAddrs g.party) q.inner .preKey rc g.session with ⟨_ | err, _⟩
      · rfl
      · cases err <;> rfl

local instance instDecidablePqFieldsMatch (x : RecordExtras) (g : GhostState HwBytes)
    (q : PreKeyFields) : Decidable (PqFieldsMatch x g q) := by
  unfold PqFieldsMatch; infer_instance

theorem pqRecvPrekeyModel_eq_some_none_of_parsePreKey_bytes_none (X : UnreachedPqxdhPrimitives) (P : PEParams)
    (st : PqParty) (m : PreKeyMessageFields) (rc : BitVec 256)
    (hm : m.inner.length + 2048 < 2 ^ 32) (hnone : parsePreKey m.bytes = none) :
    pqRecvPrekeyModel X P st m rc = some none := by
  rw [parsePreKey_bytes_eq m (by omega)] at hnone
  unfold pqRecvPrekeyModel
  cases htry : SignalMessage.tryFrom protoSignalCodec m.inner with
  | ok _ => rw [htry] at hnone; cases hnone
  | error _ => rfl

theorem a2_untyped_vacuous_on_bytes (m : PreKeyMessageFields) (q : PreKeyFields)
    (hm : m.inner.length + 2048 < 2 ^ 32) (hq : parsePreKey m.bytes = some q) :
    preKeyOfBody? m.bytes ≠ none := by
  rw [preKeyOfBody?_bytes_of_parsePreKey_some hm hq]; exact Option.some_ne_none _

end DY.Libsignal.Composed.Refinement.Cli

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Model

/-!
# Auxiliary `PreKeySignalMessage` Lemmas for `decrypt_prekey`

Characterizes outputs `pm` of `Pksm.pksmParse`: invariance of `SessMatchesPm`, `pkToE?`, and
`decPkDef` under changes to `pm.serialized`, and the version-3/version-4 Kyber-payload trichotomy.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.E2E
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs

/-- Reconstructs the `Session (List (BitVec 8))` stored on disk for a PQXDH domain session
`(x, g)` (`Record.toRecord (RecordX.extrasOf fun _ => x) g`'s `currentSession`). -/
def pqSessionOf (x : RecordExtras) (g : GhostState (List (BitVec 8))) :
    Session (List (BitVec 8)) where
  state := g.session
  pendingPreKey := if g.session.pendingPreKey then some x.pending else none
  pendingKyberPreKey := if g.session.pendingPreKey then x.kyber else none
  localRegistrationId := x.localRegistrationId
  remoteRegistrationId := x.remoteRegistrationId
  aliceBaseKey := x.aliceBaseKey

private theorem eq_cons_of_pkVecTag?_eq_some {tag : BitVec 8} {n : Nat} {l : List (BitVec 8)}
    {v : List.Vector (BitVec 8) n} (hv : pkVecTag? tag n l = some v) :
    l = tag :: v.toList := by
  cases l with
  | nil => cases hv
  | cons t rest =>
    dsimp only [pkVecTag?] at hv
    split at hv
    · next h =>
      injection hv with hv'
      exact congrArg₂ List.cons h.1 (congrArg List.Vector.toList hv')
    · cases hv

/-- Any `pm : PreKeySignalMessage` with `pkToE? pm = some m` is identical to `pmOfE m pm.message`
except possibly in `pm.serialized`. -/
theorem pm_eq_pmOfE_with_serialized {pm : PreKeySignalMessage} {m : PreKeyMessageFields}
    (h : pkToE? pm = some m) :
    pm = { pmOfE m pm.message with serialized := pm.serialized } := by
  rcases pm with ⟨ver, regId, opkId, spkId, kpay, ⟨bk⟩, ⟨⟨ik⟩⟩, msg, ser⟩
  have hver : ver = 4#8 := by
    have h' := h
    simp [pkToE?] at h'
    exact h'.1
  subst hver
  rcases kpay with _ | ⟨kpkId, ctBytes⟩
  · simp [pkToE?] at h
  have h2 :
      (match pkVecTag? 8#8 1568 ctBytes with
       | none => none
       | some ct =>
         some { regId := regId, opkId := opkId, spkId := spkId, kpkId := kpkId,
                kyberCt := ct, baseKey := bk, idPub := ik, inner := msg.serialized }) =
        some m := h
  cases hct : pkVecTag? 8#8 1568 ctBytes with
  | none => rw [hct] at h2; cases h2
  | some ct =>
    rw [hct] at h2
    injection h2 with hm
    subst hm
    have hct_eq : ctBytes = 8#8 :: ct.toList := eq_cons_of_pkVecTag?_eq_some hct
    subst hct_eq
    rfl

@[simp]
theorem sessMatchesPm_with_serialized (s : Session (List (BitVec 8)))
    (pm : PreKeySignalMessage) (ser : List (BitVec 8)) :
    SessMatchesPm s { pm with serialized := ser } ↔ SessMatchesPm s pm := by
  cases pm; rfl

@[simp]
theorem pkToE?_with_serialized (pm : PreKeySignalMessage) (ser : List (BitVec 8)) :
    pkToE? { pm with serialized := ser } = pkToE? pm := by
  cases pm; rfl

@[simp]
theorem decPkDef_with_serialized (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (F : _) (peer me : AddrVal)
    (pm : PreKeySignalMessage) (ser : List (BitVec 8)) (coins : List (BitVec 8)) :
    decPkDef X W Scope F peer me { pm with serialized := ser } coins =
      decPkDef X W Scope F peer me pm coins := by
  cases pm; rfl

/-- Whenever `pkToE? pm = some m`, `decPkDef` at `pm` equals `decPkDef` at the canonical
`pmOfE m pm.message`. -/
theorem decPkDef_eq_pmOfE_of_pkToE?_some {pm : PreKeySignalMessage} {m : PreKeyMessageFields}
    (h : pkToE? pm = some m) (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (F : _) (peer me : AddrVal)
    (coins : List (BitVec 8)) :
    decPkDef X W Scope F peer me pm coins =
      decPkDef X W Scope F peer me (pmOfE m pm.message) coins := by
  conv => lhs; rw [pm_eq_pmOfE_with_serialized h]
  exact decPkDef_with_serialized X W Scope F peer me (pmOfE m pm.message) pm.serialized coins

private theorem unpack_pksmParse_some {body : List (BitVec 8)} {pm : PreKeySignalMessage}
    (h : Pksm.pksmParse body = some pm) :
    ∃ (vb : BitVec 8) (rest : List (BitVec 8)) (m : ProtoPreKeySignalMessage),
      body = vb :: rest ∧
        ¬ ((vb >>> 4) < preKyberVersion ∨ currentVersion < (vb >>> 4)) ∧
        Pksm.decodeProto rest = some m ∧
        Pksm.kyberOk (vb >>> 4) m = true ∧
        pm.messageVersion = vb >>> 4 ∧
        pm.kyberPayload = Pksm.kyberPayloadOf m.kyberPreKeyId m.kyberCiphertext := by
  cases body with
  | nil => simp [Pksm.pksmParse] at h
  | cons vb rest =>
    unfold Pksm.pksmParse at h
    dsimp only at h
    by_cases hver : (vb >>> 4) < preKyberVersion ∨ currentVersion < (vb >>> 4)
    · simp [hver] at h
    · simp only [hver, ↓reduceIte] at h
      rcases hdec : Pksm.decodeProto rest with _ | m
      · simp [hdec] at h
      rw [hdec] at h
      rcases hbk : m.baseKey with _ | bk
      · simp [hbk] at h
      rcases hik : m.identityKey with _ | ik
      · simp [hbk, hik] at h
      rcases hmsg : m.message with _ | msg
      · simp [hbk, hik, hmsg] at h
      rcases hsid : m.signedPreKeyId with _ | sid
      · simp [hbk, hik, hmsg, hsid] at h
      simp only [hbk, hik, hmsg, hsid] at h
      cases hkyb : Pksm.kyberOk (vb >>> 4) m
      · simp [hkyb] at h
      simp only [hkyb, ↓reduceIte] at h
      rcases h1 : PublicKey.deserialize bk with _ | baseKey
      · simp [h1] at h
      rcases h2 : PublicKey.deserialize ik with _ | idKey
      · simp [h1, h2] at h
      rcases h3 : SignalMessage.tryFrom protoSignalCodec msg with _ | inner
      · simp [h1, h2, h3] at h
      simp only [h1, h2, h3, Option.some.injEq] at h
      subst h
      exact ⟨vb, rest, m, rfl, hver, hdec, hkyb, rfl, rfl⟩

/-- Every `PreKeySignalMessage` accepted by `Pksm.pksmParse` has `messageVersion` equal to `3#8`
or `4#8`. -/
theorem version_three_or_four_of_pksmParse_some {body : List (BitVec 8)} {pm : PreKeySignalMessage}
    (h : Pksm.pksmParse body = some pm) :
    pm.messageVersion = 3#8 ∨ pm.messageVersion = 4#8 := by
  obtain ⟨vb, _, _, _, hver, _, _, hpmv, _⟩ := unpack_pksmParse_some h
  have hbounds : 3 ≤ (vb >>> 4).toNat ∧ (vb >>> 4).toNat ≤ 4 := by
    simp only [preKyberVersion, currentVersion, BitVec.lt_def, not_or, Nat.not_lt] at hver
    exact ⟨hver.1, hver.2⟩
  have h34 : (vb >>> 4).toNat = 3 ∨ (vb >>> 4).toNat = 4 := by omega
  rw [hpmv]
  rcases h34 with h3 | h4
  · exact Or.inl (BitVec.eq_of_toNat_eq (by simpa using h3))
  · exact Or.inr (BitVec.eq_of_toNat_eq (by simpa using h4))

/-- Every version-4 `PreKeySignalMessage` accepted by `Pksm.pksmParse` has `pm.kyberPayload =
some kp` (`pm.kyberPayload = none` is unreachable on v4 outputs of `Pksm.pksmParse`). -/
theorem kyberPayload_isSome_of_pksmParse_v4 {body : List (BitVec 8)} {pm : PreKeySignalMessage}
    (h : Pksm.pksmParse body = some pm) (hv4 : pm.messageVersion = 4#8) :
    ∃ kp : KyberPayload, pm.kyberPayload = some kp := by
  obtain ⟨vb, _, m, _, _, _, hkyb, hpmv, hkpay⟩ := unpack_pksmParse_some h
  have hvb4 : vb >>> 4 = 4#8 := hpmv.symm.trans hv4
  rw [hvb4] at hkyb
  rw [hkpay]
  rcases hkid : m.kyberPreKeyId with _ | kid <;>
    rcases hct : m.kyberCiphertext with _ | ct
  · simp [Pksm.kyberOk, preKyberVersion, hkid, hct] at hkyb
  · simp [Pksm.kyberOk, hkid, hct] at hkyb
  · simp [Pksm.kyberOk, hkid, hct] at hkyb
  · exact ⟨⟨kid, ct⟩, rfl⟩

/-- On a version-4 output of `Pksm.pksmParse`, `pkToE? pm = none` iff its (necessarily present)
Kyber payload fails `pkVecTag? 8#8 1568` (wrong key-type byte or length `≠ 1569`). -/
theorem pkToE?_eq_none_iff_of_pksmParse_v4 {body : List (BitVec 8)} {pm : PreKeySignalMessage}
    (h : Pksm.pksmParse body = some pm) (hv4 : pm.messageVersion = 4#8) :
    pkToE? pm = none ↔
      ∃ kp : KyberPayload,
        pm.kyberPayload = some kp ∧ pkVecTag? 8#8 1568 kp.ciphertext = none := by
  obtain ⟨kp, hkp⟩ := kyberPayload_isSome_of_pksmParse_v4 h hv4
  have hlhs :
      pkToE? pm =
        match pkVecTag? 8#8 1568 kp.ciphertext with
        | none => none
        | some ct =>
          some { regId := pm.registrationId, opkId := pm.preKeyId, spkId := pm.signedPreKeyId,
                 kpkId := kp.preKeyId, kyberCt := ct, baseKey := pm.baseKey.bytes,
                 idPub := pm.identityKey.publicKey.bytes, inner := pm.message.serialized } := by
    unfold pkToE?
    rw [hv4, hkp]
    rfl
  rw [hlhs]
  simp only [hkp, Option.some.injEq]
  constructor
  · intro hnone
    refine ⟨kp, rfl, ?_⟩
    cases htag : pkVecTag? 8#8 1568 kp.ciphertext with
    | none => rfl
    | some ct => rw [htag] at hnone; cases hnone
  · rintro ⟨kp', rfl, htag⟩
    rw [htag]

end LibsignalBinary.Proofs.SignalSession.Cli.D3

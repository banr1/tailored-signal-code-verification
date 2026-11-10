/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.Statement
public import LibsignalBinary.Proofs.ProtoCodecRoundTrip

@[expose] public section
set_option autoImplicit false
namespace Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.PQXDH.Refinement (PreKeyProto versionByte)
open CryptoVerification.LibsignalProtoCodec (WireType decodeKey mergeBytes mergeUint32 encodeKey encodeVarint encodeBytesField encodeUint32Field decodeKey_encodeKey mergeBytes_encode mergeUint32_encode encodeVarint_ne_nil protoSignalCodec)
theorem length_le_preKeyWire (preKeyId : Option (BitVec 32)) (spkId kpkId regId : BitVec 32) (ik ek ct msg : HwBytes) : ik.length ≤ (preKeyWire preKeyId spkId kpkId regId ik ek ct msg).length ∧ ek.length ≤ (preKeyWire preKeyId spkId kpkId regId ik ek ct msg).length ∧ ct.length ≤ (preKeyWire preKeyId spkId kpkId regId ik ek ct msg).length ∧ msg.length ≤ (preKeyWire preKeyId spkId kpkId regId ik ek ct msg).length := by simp only [preKeyWire, DY.Libsignal.PQXDH.Refinement.PreKeyProto.encode, encodeBytesField, List.length_cons, List.length_append]; refine ⟨by omega, by omega, by omega, by omega⟩
private def pLoopsTo (m : PreKeyProto) (bs : HwBytes) (r : PreKeyProto) : Prop := ∀ n, bs.length ≤ n → decodePreKeyLoop n m bs = some r
private theorem pLoopsTo_nil (m : PreKeyProto) : pLoopsTo m [] m := by
  intro n _
  cases n <;> simp [decodePreKeyLoop]
private theorem pLoopsTo_field (t : Nat) (wt : WireType) (h1 : 1 ≤ t) (h2 : t < 2 ^ 28) (m m' r : PreKeyProto) (body rest : HwBytes) (hmerge : mergePreKeyField m t wt (body ++ rest) = some (m', rest)) (h : pLoopsTo m' rest r) : pLoopsTo m (encodeKey t wt ++ (body ++ rest)) r := by
  intro n hn; have hkey := decodeKey_encodeKey t wt (body ++ rest) h1 h2; have hpos : 0 < (encodeKey t wt).length := List.length_pos_iff.mpr (encodeVarint_ne_nil _); simp only [List.length_append] at hn
  obtain ⟨b, bs, hk⟩ := List.exists_cons_of_ne_nil
    (List.length_pos_iff.mp (by simp only [List.length_append]; omega) : encodeKey t wt ++ (body ++ rest) ≠ [])
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩; rw [hk] at hkey ⊢; simp only [decodePreKeyLoop, hkey, hmerge]; exact h n' (by omega)
private theorem fieldBytes_split (t : Nat) (v rest : HwBytes) : encodeBytesField t (some v) ++ rest = encodeKey t .lengthDelimited ++ ((encodeVarint (BitVec.ofNat 64 v.length) ++ v) ++ rest) := by simp [encodeBytesField]
private theorem fieldUint32_split (t : Nat) (x : BitVec 32) (rest : HwBytes) : encodeUint32Field t (some x) ++ rest = encodeKey t .varint ++ (encodeVarint (x.zeroExtend 64) ++ rest) := by simp [encodeUint32Field]
private theorem pLoopsTo_bytes (t : Nat) (h1 : 1 ≤ t) (h2 : t < 2 ^ 28) (o : Option HwBytes) (upd : Option HwBytes → PreKeyProto) (rest : HwBytes) (r : PreKeyProto) (hl : ∀ v, o = some v → v.length < 2 ^ 64) (hm : ∀ bs, mergePreKeyField (upd none) t .lengthDelimited bs = (mergeBytes .lengthDelimited bs).map fun (v, r) => (upd (some v), r)) (h : pLoopsTo (upd o) rest r) : pLoopsTo (upd none) (encodeBytesField t o ++ rest) r := by
  cases o with
  | none => simpa [encodeBytesField] using h
  | some v =>
    rw [fieldBytes_split]; refine pLoopsTo_field t _ h1 h2 _ _ _ _ _ ?_ h; rw [hm, List.append_assoc, mergeBytes_encode v rest (hl v rfl)]; rfl
private theorem pLoopsTo_uint32 (t : Nat) (h1 : 1 ≤ t) (h2 : t < 2 ^ 28) (o : Option (BitVec 32)) (upd : Option (BitVec 32) → PreKeyProto) (rest : HwBytes) (r : PreKeyProto) (hm : ∀ bs, mergePreKeyField (upd none) t .varint bs = (mergeUint32 .varint bs).map fun (v, r) => (upd (some v), r)) (h : pLoopsTo (upd o) rest r) : pLoopsTo (upd none) (encodeUint32Field t o ++ rest) r := by
  cases o with
  | none => simpa [encodeUint32Field] using h
  | some x =>
    rw [fieldUint32_split]; refine pLoopsTo_field t _ h1 h2 _ _ _ _ _ ?_ h; rw [hm, mergeUint32_encode x rest]; rfl
def PreKeyLengthsFit (p : PreKeyProto) : Prop := ∀ v, p.baseKey = some v ∨ p.identityKey = some v ∨ p.message = some v ∨ p.kyberCiphertext = some v → v.length < 2 ^ 64
theorem decodePreKey_encode (p : PreKeyProto) (h : PreKeyLengthsFit p) : decodePreKey (PreKeyProto.encode p) = some p := by
  obtain ⟨reg, pk, spk, kpk, kct, bk, ik, msg⟩ := p
  have hbk : ∀ v, bk = some v → v.length < 2 ^ 64 := fun v hv => h v (Or.inl hv)
  have hik : ∀ v, ik = some v → v.length < 2 ^ 64 := fun v hv => h v (Or.inr (Or.inl hv))
  have hmsg : ∀ v, msg = some v → v.length < 2 ^ 64 :=
    fun v hv => h v (Or.inr (Or.inr (Or.inl hv)))
  have hkct : ∀ v, kct = some v → v.length < 2 ^ 64 :=
    fun v hv => h v (Or.inr (Or.inr (Or.inr hv)))
  have hloop : pLoopsTo emptyPreKeyMsg
      (encodeUint32Field 1 pk ++ (encodeBytesField 2 bk ++ (encodeBytesField 3 ik ++ (encodeBytesField 4 msg ++ (encodeUint32Field 5 reg ++ (encodeUint32Field 6 spk ++ (encodeUint32Field 7 kpk ++ (encodeBytesField 8 kct ++ []))))))))
      ⟨reg, pk, spk, kpk, kct, bk, ik, msg⟩ :=
    pLoopsTo_uint32 1 (by omega) (by omega) pk
      (fun o => ⟨none, o, none, none, none, none, none, none⟩) _ _ (fun _ => rfl) <|
    pLoopsTo_bytes 2 (by omega) (by omega) bk
      (fun o => ⟨none, pk, none, none, none, o, none, none⟩) _ _ hbk (fun _ => rfl) <|
    pLoopsTo_bytes 3 (by omega) (by omega) ik
      (fun o => ⟨none, pk, none, none, none, bk, o, none⟩) _ _ hik (fun _ => rfl) <|
    pLoopsTo_bytes 4 (by omega) (by omega) msg
      (fun o => ⟨none, pk, none, none, none, bk, ik, o⟩) _ _ hmsg (fun _ => rfl) <|
    pLoopsTo_uint32 5 (by omega) (by omega) reg
      (fun o => ⟨o, pk, none, none, none, bk, ik, msg⟩) _ _ (fun _ => rfl) <|
    pLoopsTo_uint32 6 (by omega) (by omega) spk
      (fun o => ⟨reg, pk, o, none, none, bk, ik, msg⟩) _ _ (fun _ => rfl) <|
    pLoopsTo_uint32 7 (by omega) (by omega) kpk
      (fun o => ⟨reg, pk, spk, o, none, bk, ik, msg⟩) _ _ (fun _ => rfl) <|
    pLoopsTo_bytes 8 (by omega) (by omega) kct
      (fun o => ⟨reg, pk, spk, kpk, o, bk, ik, msg⟩) _ _ hkct (fun _ => rfl) <|
    pLoopsTo_nil _
  have henc : PreKeyProto.encode ⟨reg, pk, spk, kpk, kct, bk, ik, msg⟩ = encodeUint32Field 1 pk ++ (encodeBytesField 2 bk ++ (encodeBytesField 3 ik ++ (encodeBytesField 4 msg ++ (encodeUint32Field 5 reg ++ (encodeUint32Field 6 spk ++
          (encodeUint32Field 7 kpk ++ (encodeBytesField 8 kct ++ []))))))) := by
    simp only [PreKeyProto.encode, List.append_assoc, List.append_nil]
  rw [decodePreKey, henc]; exact hloop _ (Nat.le_refl _)
theorem parsePreKeyWire_preKeyWire_inv {preKeyId : Option (BitVec 32)} {spkId kpkId regId : BitVec 32} {ik ek ct msg b : HwBytes} {p : PreKeyFields} (hb : b = preKeyWire preKeyId spkId kpkId regId ik ek ct msg) (hlen : b.length < 2 ^ 63) (hp : parsePreKeyWire b = some p) : p.preKeyId = preKeyId ∧ p.kyberCiphertext = some (kyberKey ct) ∧ p.baseKey = ecKey ek ∧ p.message = msg := by
  have ⟨hik_le, hek_le, hct_le, hmsg_le⟩ := length_le_preKeyWire preKeyId spkId kpkId regId ik ek ct msg; rw [← hb] at hik_le hek_le hct_le hmsg_le
  have hfit : PreKeyLengthsFit
      { registrationId := some regId, preKeyId, signedPreKeyId := some spkId, kyberPreKeyId := some kpkId, kyberCiphertext := some (kyberKey ct),
        baseKey := some (ecKey ek), identityKey := some ik, message := some msg } := by
    intro v hv; simp only [Option.some.injEq] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · simp only [ecKey, List.length_cons]; omega
    · omega
    · omega
    · simp only [kyberKey, List.length_cons]; omega
  dsimp only [ecKey, kyberKey] at hfit
  subst hb; simp only [parsePreKeyWire, preKeyWire, ↓reduceIte, parsePreKey, decodePreKey_encode _ hfit] at hp
  split at hp
  · cases hp
  · split at hp
    · split at hp
      · injection hp with hp'
        subst hp'; exact ⟨rfl, rfl, rfl, rfl⟩
      · cases hp
    · cases hp

abbrev SendMatchesMoves (interpretation : CryptoProofLib.Refinement.ExternInterpretation)
    (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (b : HwBytes) (ts : List DY.Bytes) : Prop :=
  ∃ ids, SendMatches interpretation r S g (some ids) b ts

abbrev PreKeyOuterMatches (i : CryptoProofLib.Refinement.ExternInterpretation)
    (r : ProtocolSetup) (b : HwBytes) (q : PreKeyFields) : Prop :=
  q.version = 4 ∧ q.signedPreKeyId = r.spkId ∧ q.kyberPreKeyId = some r.kpkId ∧
    q.identityKey.take 33 = ecKey (pubBytes i (secretBytes r 0)) ∧ (∃ used, OpkNamed r b used)

end Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire

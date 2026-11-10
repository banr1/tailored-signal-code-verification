/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Model

@[expose] public section

set_option autoImplicit false

/-!
# `AllocCostModel`-Free Prost Wire Field Length Bounds

Pure `Prop` byte-length bounds on parsed fields of `SignalMessage.tryFrom` and `Pksm.pksmParse`,
with zero dependency on `AllocCostModel` or `AllocNeverFails/`.
-/

namespace LibsignalBinary.Proofs.PeakBudget.WireFieldDomainCaps

open CryptoGames.LibsignalSession
  (ProtoSignalMessage PublicKey SignalMessage macLength)
open CryptoGames.LibsignalSessionApi
  (KyberPayload PreKeySignalMessage ProtoPreKeySignalMessage)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeKey decodeLoop decodeVarint decodeVarintAux emptyProtoSignalMessage
   mergeBytes mergeField mergeUint32 protoSignalCodec skipBytes skipField skipGroup skipScalar)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm
  (decodeProto decodeProtoLoop emptyProto mergeProtoField pksmParse)

private theorem decodeVarintAux_length_le :
    ∀ (bs : List (BitVec 8)) (i : Nat) (acc v : BitVec 64) (rest : List (BitVec 8)),
      decodeVarintAux i acc bs = some (v, rest) → rest.length ≤ bs.length
  | [], _, _, _, _, h => by cases h
  | b :: tl, i, acc, v, rest, h => by
    unfold decodeVarintAux at h
    dsimp only at h
    split_ifs at h
    · injection h with h'
      obtain ⟨_, rfl⟩ := Prod.mk.inj h'
      exact Nat.le_succ _
    · exact Nat.le_trans (decodeVarintAux_length_le tl (i + 1) _ v rest h) (Nat.le_succ _)

private theorem decodeVarint_length_le {bs rest : List (BitVec 8)} {v : BitVec 64}
    (h : decodeVarint bs = some (v, rest)) :
    rest.length ≤ bs.length :=
  decodeVarintAux_length_le bs 0 0 v rest h

private theorem decodeKey_length_le {bs rest : List (BitVec 8)} {tw : Nat × WireType}
    (h : decodeKey bs = some (tw, rest)) :
    rest.length ≤ bs.length := by
  unfold decodeKey at h
  rcases hd : decodeVarint bs with _ | ⟨key, r⟩ <;> rw [hd] at h
  · cases h
  · dsimp only at h
    by_cases hk : 2 ^ 32 ≤ key.toNat
    · simp only [hk, ↓reduceIte] at h; cases h
    · simp only [hk, ↓reduceIte] at h
      rcases hw : WireType.ofNat? (key.toNat % 8) with _ | wt <;> rw [hw] at h
      · cases h
      · dsimp only at h
        split_ifs at h
        injection h with h'
        obtain ⟨_, rfl⟩ := Prod.mk.inj h'
        exact decodeVarint_length_le hd

private theorem skipBytes_length_le {n : Nat} {bs r : List (BitVec 8)}
    (h : skipBytes n bs = some r) :
    r.length ≤ bs.length := by
  unfold skipBytes at h
  split_ifs at h
  injection h with hr
  rw [← hr, List.length_drop]
  omega

private theorem skipScalar_length_le {wt : WireType} {bs r : List (BitVec 8)}
    (h : skipScalar wt bs = some r) :
    r.length ≤ bs.length := by
  cases wt with
  | varint =>
    unfold skipScalar at h
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨v, rest⟩, hd, rfl⟩ := h
    exact decodeVarint_length_le hd
  | thirtyTwoBit => exact skipBytes_length_le h
  | sixtyFourBit => exact skipBytes_length_le h
  | lengthDelimited =>
    unfold skipScalar at h
    rcases hd : decodeVarint bs with _ | ⟨len, rest⟩ <;> rw [hd] at h
    · cases h
    · exact Nat.le_trans (skipBytes_length_le h) (decodeVarint_length_le hd)
  | startGroup => cases h
  | endGroup => cases h

private theorem skipField_skipGroup_length_le :
    ∀ fuel : Nat,
      (∀ depth tag wt bs r, skipField fuel depth tag wt bs = some r → r.length ≤ bs.length) ∧
      (∀ depth tag bs r, skipGroup fuel depth tag bs = some r → r.length ≤ bs.length)
  | 0 => ⟨(fun _ _ _ _ _ h => by cases h), (fun _ _ _ _ h => by cases h)⟩
  | fuel + 1 => by
    obtain ⟨ihF, ihG⟩ := skipField_skipGroup_length_le fuel
    refine ⟨?_, ?_⟩
    · intro depth tag wt bs r h
      unfold skipField at h
      split_ifs at h
      cases wt with
      | endGroup => cases h
      | startGroup => exact ihG depth tag bs r h
      | varint => exact skipScalar_length_le h
      | sixtyFourBit => exact skipScalar_length_le h
      | lengthDelimited => exact skipScalar_length_le h
      | thirtyTwoBit => exact skipScalar_length_le h
    · intro depth tag bs r h
      unfold skipGroup at h
      rcases hk : decodeKey bs with _ | ⟨⟨itag, iwt⟩, rest⟩ <;> rw [hk] at h
      · cases h
      · have hrest := decodeKey_length_le hk
        cases iwt <;> dsimp only at h
        case endGroup =>
          split_ifs at h
          injection h with hr
          rwa [← hr]
        all_goals
          rcases hs : skipField fuel (depth - 1) itag _ rest with _ | rest' <;> rw [hs] at h
          · cases h
          · exact Nat.le_trans (ihG depth tag rest' r h)
              (Nat.le_trans (ihF _ _ _ rest rest' hs) hrest)

private theorem mergeBytes_lengths_le {wt : WireType} {bs v r : List (BitVec 8)}
    (h : mergeBytes wt bs = some (v, r)) :
    v.length ≤ bs.length ∧ r.length ≤ bs.length := by
  unfold mergeBytes at h
  split_ifs at h
  rcases hd : decodeVarint bs with _ | ⟨len, rest⟩ <;> rw [hd] at h
  · cases h
  · dsimp only at h
    split_ifs at h
    injection h with h'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h'
    have hrest := decodeVarint_length_le hd
    rw [List.length_take, List.length_drop]
    omega

private theorem mergeUint32_length_le {wt : WireType} {bs r : List (BitVec 8)} {v : BitVec 32}
    (h : mergeUint32 wt bs = some (v, r)) :
    r.length ≤ bs.length := by
  unfold mergeUint32 at h
  split_ifs at h
  rcases hd : decodeVarint bs with _ | ⟨val, rest⟩ <;> rw [hd] at h
  · cases h
  · injection h with h'
    obtain ⟨_, rfl⟩ := Prod.mk.inj h'
    exact decodeVarint_length_le hd

private def protoSigFieldsBounded (N : Nat) (m : ProtoSignalMessage) : Prop :=
  (∀ v, m.ciphertext = some v → v.length ≤ N) ∧
    (∀ v, m.pqRatchet = some v → v.length ≤ N)

private theorem decodeLoop_fields_le (N : Nat) :
    ∀ (fuel : Nat) (m m' : ProtoSignalMessage) (bs : List (BitVec 8)),
      bs.length ≤ N →
      protoSigFieldsBounded N m →
      decodeLoop fuel m bs = some m' →
      protoSigFieldsBounded N m'
  | _, m, m', [], _, hm, h => by
    unfold decodeLoop at h
    injection h with hm'
    rwa [← hm']
  | 0, _, _, _ :: _, _, _, h => by cases h
  | fuel + 1, m, m', b :: tl, hbs, hm, h => by
    unfold decodeLoop at h
    rcases hk : decodeKey (b :: tl) with _ | ⟨⟨tag, wt⟩, rest⟩ <;> rw [hk] at h
    · cases h
    · have hrest : rest.length ≤ N := Nat.le_trans (decodeKey_length_le hk) hbs
      dsimp only at h
      rcases hmF : mergeField m tag wt rest with _ | ⟨m1, rest1⟩ <;> rw [hmF] at h
      · cases h
      · have hstep : rest1.length ≤ N ∧ protoSigFieldsBounded N m1 := by
          unfold mergeField at hmF
          split at hmF <;> simp only [Option.map_eq_some_iff] at hmF
          · obtain ⟨⟨v, r⟩, hmb, hmr⟩ := hmF
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmr
            exact ⟨Nat.le_trans (mergeBytes_lengths_le hmb).2 hrest, hm⟩
          · obtain ⟨⟨v, r⟩, hmu, hmr⟩ := hmF
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmr
            exact ⟨Nat.le_trans (mergeUint32_length_le hmu) hrest, hm⟩
          · obtain ⟨⟨v, r⟩, hmu, hmr⟩ := hmF
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmr
            exact ⟨Nat.le_trans (mergeUint32_length_le hmu) hrest, hm⟩
          · obtain ⟨⟨v, r⟩, hmb, hmr⟩ := hmF
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmr
            have ⟨hv, hr⟩ := mergeBytes_lengths_le hmb
            refine ⟨Nat.le_trans hr hrest, ?_, hm.2⟩
            intro w hw; injection hw with hw'; rw [← hw']; exact Nat.le_trans hv hrest
          · obtain ⟨⟨v, r⟩, hmb, hmr⟩ := hmF
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmr
            have ⟨hv, hr⟩ := mergeBytes_lengths_le hmb
            refine ⟨Nat.le_trans hr hrest, hm.1, ?_⟩
            intro w hw; injection hw with hw'; rw [← hw']; exact Nat.le_trans hv hrest
          · obtain ⟨⟨v, r⟩, hmb, hmr⟩ := hmF
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmr
            exact ⟨Nat.le_trans (mergeBytes_lengths_le hmb).2 hrest, hm⟩
          · obtain ⟨r, hsk, hmr⟩ := hmF
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmr
            exact ⟨Nat.le_trans ((skipField_skipGroup_length_le _).1 _ _ _ _ _ hsk) hrest, hm⟩
        exact decodeLoop_fields_le N fuel m1 m' rest1 hstep.1 hstep.2 h

/-- Every `SignalMessage.tryFrom protoSignalCodec rest = .ok sm` yields `sm.serialized = rest`,
`sm.ciphertext.length ≤ rest.length`, and `sm.pqRatchet.length ≤ rest.length`. -/
theorem signalMessage_tryFrom_lengths_le {rest : List (BitVec 8)} {sm : SignalMessage}
    (h : SignalMessage.tryFrom protoSignalCodec rest = .ok sm) :
    sm.serialized = rest ∧ sm.ciphertext.length ≤ rest.length ∧
      sm.pqRatchet.length ≤ rest.length := by
  unfold SignalMessage.tryFrom at h
  dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  split_ifs at h
  have hsub_len : ((rest.take (rest.length - macLength)).drop 1).length ≤ rest.length := by
    rw [List.length_drop, List.length_take]
    omega
  rcases hp : protoSignalCodec.decode ((rest.take (rest.length - macLength)).drop 1) with _ | p <;>
    rw [hp] at h
  · cases h
  · dsimp only at h
    rcases hrk : p.ratchetKey with _ | rk <;> rw [hrk] at h
    · cases h
    · dsimp only at h
      rcases hpk : PublicKey.deserialize rk with _ | srk <;> rw [hpk] at h
      · cases h
      · dsimp only at h
        rcases hcnt : p.counter with _ | cnt <;> rw [hcnt] at h
        · cases h
        · dsimp only at h
          rcases hct : p.ciphertext with _ | ct <;> rw [hct] at h
          · cases h
          · dsimp only at h
            injection h with hsm
            rw [← hsm]
            have hfb := decodeLoop_fields_le rest.length _ emptyProtoSignalMessage p _ hsub_len
              ⟨(fun _ hv => by cases hv), (fun _ hv => by cases hv)⟩ hp
            refine ⟨rfl, hfb.1 ct hct, ?_⟩
            rcases hpq : p.pqRatchet with _ | pq
            · simp
            · exact hfb.2 pq hpq

private def protoPksmFieldsBounded (N : Nat) (m : ProtoPreKeySignalMessage) : Prop :=
  (∀ v, m.message = some v → v.length ≤ N) ∧
    (∀ v, m.kyberCiphertext = some v → v.length ≤ N)

private theorem decodeProtoLoop_fields_le (N : Nat) :
    ∀ (fuel : Nat) (m m' : ProtoPreKeySignalMessage) (bs : List (BitVec 8)),
      bs.length ≤ N →
      protoPksmFieldsBounded N m →
      decodeProtoLoop fuel m bs = some m' →
      protoPksmFieldsBounded N m'
  | _, m, m', [], _, hm, h => by
    unfold decodeProtoLoop at h
    injection h with hm'
    rwa [← hm']
  | 0, _, _, _ :: _, _, _, h => by cases h
  | fuel + 1, m, m', b :: tl, hbs, hm, h => by
    unfold decodeProtoLoop at h
    rcases hk : decodeKey (b :: tl) with _ | ⟨⟨tag, wt⟩, rest⟩ <;> rw [hk] at h
    · cases h
    · have hrest : rest.length ≤ N := Nat.le_trans (decodeKey_length_le hk) hbs
      dsimp only at h
      rcases hmF : mergeProtoField m tag wt rest with _ | ⟨m1, rest1⟩ <;> rw [hmF] at h
      · cases h
      · have hstep : rest1.length ≤ N ∧ protoPksmFieldsBounded N m1 := by
          unfold mergeProtoField at hmF
          split at hmF <;> simp only [Option.map_eq_some_iff] at hmF
          · obtain ⟨⟨v, r⟩, hmu, hmr⟩ := hmF
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmr
            exact ⟨Nat.le_trans (mergeUint32_length_le hmu) hrest, hm⟩
          · obtain ⟨⟨v, r⟩, hmb, hmr⟩ := hmF
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmr
            exact ⟨Nat.le_trans (mergeBytes_lengths_le hmb).2 hrest, hm⟩
          · obtain ⟨⟨v, r⟩, hmb, hmr⟩ := hmF
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmr
            exact ⟨Nat.le_trans (mergeBytes_lengths_le hmb).2 hrest, hm⟩
          · obtain ⟨⟨v, r⟩, hmb, hmr⟩ := hmF
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmr
            have ⟨hv, hr⟩ := mergeBytes_lengths_le hmb
            refine ⟨Nat.le_trans hr hrest, ?_, hm.2⟩
            intro w hw; injection hw with hw'; rw [← hw']; exact Nat.le_trans hv hrest
          · obtain ⟨⟨v, r⟩, hmu, hmr⟩ := hmF
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmr
            exact ⟨Nat.le_trans (mergeUint32_length_le hmu) hrest, hm⟩
          · obtain ⟨⟨v, r⟩, hmu, hmr⟩ := hmF
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmr
            exact ⟨Nat.le_trans (mergeUint32_length_le hmu) hrest, hm⟩
          · obtain ⟨⟨v, r⟩, hmu, hmr⟩ := hmF
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmr
            exact ⟨Nat.le_trans (mergeUint32_length_le hmu) hrest, hm⟩
          · obtain ⟨⟨v, r⟩, hmb, hmr⟩ := hmF
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmr
            have ⟨hv, hr⟩ := mergeBytes_lengths_le hmb
            refine ⟨Nat.le_trans hr hrest, hm.1, ?_⟩
            intro w hw; injection hw with hw'; rw [← hw']; exact Nat.le_trans hv hrest
          · obtain ⟨r, hsk, hmr⟩ := hmF
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmr
            exact ⟨Nat.le_trans ((skipField_skipGroup_length_le _).1 _ _ _ _ _ hsk) hrest, hm⟩
        exact decodeProtoLoop_fields_le N fuel m1 m' rest1 hstep.1 hstep.2 h

/-- Every `pksmParse rest = some pm` bounds `pm.message.serialized`, `pm.message.ciphertext`,
`pm.message.pqRatchet`, and any `kyberPayload.ciphertext` by `rest.length`. -/
theorem pksmParse_lengths_le {rest : List (BitVec 8)} {pm : PreKeySignalMessage}
    (h : pksmParse rest = some pm) :
    pm.serialized = rest ∧
      pm.message.serialized.length ≤ rest.length ∧
      pm.message.ciphertext.length ≤ rest.length ∧
      pm.message.pqRatchet.length ≤ rest.length ∧
      ∀ ky : KyberPayload, pm.kyberPayload = some ky → ky.ciphertext.length ≤ rest.length := by
  rcases rest with _ | ⟨vb, body⟩
  · cases h
  · unfold pksmParse at h
    dsimp only at h
    split_ifs at h
    rcases hd : decodeProto body with _ | m <;> rw [hd] at h
    · cases h
    · dsimp only at h
      rcases hbk : m.baseKey with _ | bk <;> rw [hbk] at h
      · cases h
      · rcases hik : m.identityKey with _ | ik <;> rw [hik] at h
        · cases h
        · rcases hmsg : m.message with _ | msg <;> rw [hmsg] at h
          · cases h
          · rcases hsid : m.signedPreKeyId with _ | sid <;> rw [hsid] at h
            · cases h
            · dsimp only at h
              split_ifs at h
              rcases hpk1 : PublicKey.deserialize bk with _ | bKey <;> rw [hpk1] at h
              · cases h
              · rcases hpk2 : PublicKey.deserialize ik with _ | iKey <;> rw [hpk2] at h
                · cases h
                · rcases hsm : SignalMessage.tryFrom protoSignalCodec msg with _ | inner <;>
                    rw [hsm] at h
                  · cases h
                  · dsimp only at h
                    injection h with hpm
                    rw [← hpm]
                    have hbody_le : body.length ≤ (vb :: body).length := Nat.le_succ _
                    have hfb := decodeProtoLoop_fields_le (vb :: body).length body.length
                      emptyProto m body hbody_le
                      ⟨(fun _ hv => by cases hv), (fun _ hv => by cases hv)⟩ hd
                    have hmsg_le : msg.length ≤ (vb :: body).length := hfb.1 msg hmsg
                    obtain ⟨hser, hct, hpq⟩ := signalMessage_tryFrom_lengths_le hsm
                    refine ⟨rfl, hser ▸ hmsg_le, Nat.le_trans hct hmsg_le,
                      Nat.le_trans hpq hmsg_le, ?_⟩
                    intro ky hky
                    dsimp only at hky
                    rcases hkpid : m.kyberPreKeyId with _ | kpid <;>
                      rcases hkpct : m.kyberCiphertext with _ | kpct <;>
                      rw [hkpid, hkpct] at hky
                    · cases hky
                    · cases hky
                    · cases hky
                    · injection hky with hky'
                      rw [← hky']
                      exact hfb.2 kpct hkpct

end LibsignalBinary.Proofs.PeakBudget.WireFieldDomainCaps

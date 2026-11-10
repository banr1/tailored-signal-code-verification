/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Model
import LibsignalBinary.Proofs.ProtoCodecRoundTrip

/-!
# Pure `pksmParse` Dispatch and Field-Slice Length Lemmas

Proves `Option`/`Bool` dispatch equations for `Pksm.pksmParse`, `decodeProto`, and `kyberOk`,
together with length bounds showing every decoded field slice is strictly shorter than the
protobuf body.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalProtoCodec
open RunProofs.Pksm

/-! ## Version Nibble Arithmetic (`toNat`) -/

private theorem toNat_ver (vb : BitVec 8) : (vb >>> 4).toNat = vb.toNat / 16 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem pksmParse_nil : pksmParse [] = none := rfl

theorem pksmParse_legacy {vb : BitVec 8} {body} (h : vb < 0x30#8) :
    pksmParse (vb :: body) = none := by
  have hv : (vb >>> 4) < preKyberVersion := by
    rw [BitVec.lt_def] at h ⊢
    rw [toNat_ver]
    change vb.toNat / 16 < 3
    change vb.toNat < 48 at h
    omega
  simp [pksmParse, hv]

theorem pksmParse_unrec {vb : BitVec 8} {body} (h : 0x4f#8 < vb) :
    pksmParse (vb :: body) = none := by
  have hv : currentVersion < (vb >>> 4) := by
    rw [BitVec.lt_def] at h ⊢
    rw [toNat_ver]
    change 4 < vb.toNat / 16
    change 79 < vb.toNat at h
    omega
  simp [pksmParse, hv]

-- the accepted version range (prologue +0x038): exactly 0x30 ≤ vb ≤ 0x4f
theorem pksmParse_ver_ok_iff (vb : BitVec 8) :
    ¬ ((vb >>> 4) < preKyberVersion ∨ currentVersion < (vb >>> 4)) ↔
      (0x30#8 ≤ vb ∧ vb ≤ 0x4f#8) := by
  have hlt : vb.toNat < 256 := vb.isLt
  simp only [BitVec.lt_def, BitVec.le_def, toNat_ver]
  change ¬ (vb.toNat / 16 < 3 ∨ 4 < vb.toNat / 16) ↔ 48 ≤ vb.toNat ∧ vb.toNat ≤ 79
  omega

/-! ## `pksmParse` `Err` (`none`) & `Ok` (`some`) Dispatch Lemmas -/

theorem pksmParse_decodeNone {vb body} (hv : 0x30#8 ≤ vb ∧ vb ≤ 0x4f#8)
    (h : decodeProto body = none) : pksmParse (vb :: body) = none := by
  have hv' := (pksmParse_ver_ok_iff vb).mpr hv
  simp [pksmParse, hv', h]

theorem decodeProto_nil : decodeProto [] = some emptyProto := rfl

theorem pksmParse_bkNone {vb body m} (hd : decodeProto body = some m) (h : m.baseKey = none) :
    pksmParse (vb :: body) = none := by
  simp only [pksmParse]
  split
  · rfl
  · simp [hd, h]

theorem pksmParse_ikNone {vb body m} (hd : decodeProto body = some m)
    (h : m.identityKey = none) : pksmParse (vb :: body) = none := by
  simp only [pksmParse]
  split
  · rfl
  · simp only [hd]
    cases m.baseKey with
    | none => rfl
    | some _ => simp [h]

theorem pksmParse_msgNone {vb body m} (hd : decodeProto body = some m)
    (h : m.message = none) : pksmParse (vb :: body) = none := by
  simp only [pksmParse]
  split
  · rfl
  · simp only [hd]
    cases m.baseKey with
    | none => rfl
    | some _ =>
      cases m.identityKey with
      | none => rfl
      | some _ => simp [h]

theorem pksmParse_spkNone {vb body m} (hd : decodeProto body = some m)
    (h : m.signedPreKeyId = none) : pksmParse (vb :: body) = none := by
  simp only [pksmParse]
  split
  · rfl
  · simp only [hd]
    cases m.baseKey with
    | none => rfl
    | some _ =>
      cases m.identityKey with
      | none => rfl
      | some _ =>
        cases m.message with
        | none => rfl
        | some _ => simp [h]

theorem pksmParse_kyberBad {vb : BitVec 8} {body m} (hd : decodeProto body = some m)
    (h : kyberOk (vb >>> 4) m = false) : pksmParse (vb :: body) = none := by
  simp only [pksmParse]
  split
  · rfl
  · simp only [hd]
    cases m.baseKey with
    | none => rfl
    | some _ =>
      cases m.identityKey with
      | none => rfl
      | some _ =>
        cases m.message with
        | none => rfl
        | some _ =>
          cases m.signedPreKeyId with
          | none => rfl
          | some _ => simp [h]

-- the two machine-level shapes of `kyberOk = false`
theorem kyberOk_false_of_half {ver m} (h : m.kyberPreKeyId.isSome ≠ m.kyberCiphertext.isSome) :
    kyberOk ver m = false := by
  rcases m with ⟨_, _, _, kpk, kct, _, _, _⟩
  cases kpk <;> cases kct
  · exact absurd rfl h
  · rfl
  · rfl
  · exact absurd rfl h

theorem kyberOk_false_of_neither_v4 {vb : BitVec 8} {m} (hv : 0x40#8 ≤ vb) (hv' : vb ≤ 0x4f#8)
    (h1 : m.kyberPreKeyId = none) (h2 : m.kyberCiphertext = none) :
    kyberOk (vb >>> 4) m = false := by
  have hnot : ¬ ((vb >>> 4) ≤ preKyberVersion) := by
    rw [BitVec.le_def] at hv hv' ⊢
    rw [toNat_ver]
    change ¬ (vb.toNat / 16 ≤ 3)
    change 64 ≤ vb.toNat at hv
    change vb.toNat ≤ 79 at hv'
    omega
  simp [kyberOk, h1, h2, hnot]

theorem pksmParse_bkErr {vb body m bk e} (hd : decodeProto body = some m)
    (hb : m.baseKey = some bk) (h : PublicKey.deserialize bk = .error e) :
    pksmParse (vb :: body) = none := by
  simp only [pksmParse]
  split
  · rfl
  · simp only [hd, hb]
    cases m.identityKey with
    | none => rfl
    | some _ =>
      cases m.message with
      | none => rfl
      | some _ =>
        cases m.signedPreKeyId with
        | none => rfl
        | some _ =>
          dsimp only
          split
          · simp [h]
          · rfl

theorem pksmParse_ikErr {vb body m ik e} (hd : decodeProto body = some m)
    (hi : m.identityKey = some ik) (h : PublicKey.deserialize ik = .error e) :
    pksmParse (vb :: body) = none := by
  simp only [pksmParse]
  split
  · rfl
  · simp only [hd, hi]
    cases m.baseKey with
    | none => rfl
    | some bk =>
      cases m.message with
      | none => rfl
      | some _ =>
        cases m.signedPreKeyId with
        | none => rfl
        | some _ =>
          dsimp only
          split
          · cases PublicKey.deserialize bk with
            | error _ => rfl
            | ok _ => simp [h]
          · rfl

theorem pksmParse_msgErr {vb body m msg e} (hd : decodeProto body = some m)
    (hm : m.message = some msg)
    (h : SignalMessage.tryFrom protoSignalCodec msg = .error e) :
    pksmParse (vb :: body) = none := by
  simp only [pksmParse]
  split
  · rfl
  · simp only [hd, hm]
    cases m.baseKey with
    | none => rfl
    | some bk =>
      cases m.identityKey with
      | none => rfl
      | some ik =>
        cases m.signedPreKeyId with
        | none => rfl
        | some _ =>
          dsimp only
          split
          · cases PublicKey.deserialize bk with
            | error _ => rfl
            | ok _ =>
              cases PublicKey.deserialize ik with
              | error _ => rfl
              | ok _ => simp [h]
          · rfl

theorem pksmParse_eq_some {vb body m bk ik msg sid baseKey idKey inner}
    (hv : 0x30#8 ≤ vb ∧ vb ≤ 0x4f#8) (hd : decodeProto body = some m)
    (hb : m.baseKey = some bk) (hi : m.identityKey = some ik) (hm : m.message = some msg)
    (hs : m.signedPreKeyId = some sid) (hk : kyberOk (vb >>> 4) m = true)
    (hbk : PublicKey.deserialize bk = .ok baseKey) (hik : PublicKey.deserialize ik = .ok idKey)
    (hin : SignalMessage.tryFrom protoSignalCodec msg = .ok inner) :
    pksmParse (vb :: body) = some
      { messageVersion := vb >>> 4, registrationId := m.registrationId.getD 0#32,
        preKeyId := m.preKeyId, signedPreKeyId := sid,
        kyberPayload := kyberPayloadOf m.kyberPreKeyId m.kyberCiphertext,
        baseKey := baseKey, identityKey := ⟨idKey⟩, message := inner, serialized := vb :: body } := by
  have hv' := (pksmParse_ver_ok_iff vb).mpr hv
  simp [pksmParse, hv', hd, hb, hi, hm, hs, hk, hbk, hik, hin]

/-! ## Field-Slice Length Bounds (`decodeProtoLoop` / `decodeProto`) -/

private theorem mergeBytes_lengths {wt : WireType} {bs v r : List (BitVec 8)}
    (h : mergeBytes wt bs = some (v, r)) :
    v.length < bs.length ∧ r.length ≤ bs.length := by
  simp only [mergeBytes] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i len rest hv
      split at h
      · simp at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hlen := decodeVarint_length hv
        simp only [List.length_take, List.length_drop]
        omega

private theorem mergeUint32_length {wt : WireType} {bs r : List (BitVec 8)} {v : BitVec 32}
    (h : mergeUint32 wt bs = some (v, r)) :
    r.length ≤ bs.length := by
  simp only [mergeUint32] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i _ rest hv
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact Nat.le_of_lt (decodeVarint_length hv)

private theorem mergeProtoField_lengths {m m' : ProtoPreKeySignalMessage} {tag : ℕ}
    {wt : WireType} {bs r : List (BitVec 8)} {n : ℕ}
    (h0 : (∀ v, m.baseKey = some v → v.length < n) ∧
          (∀ v, m.identityKey = some v → v.length < n) ∧
          (∀ v, m.message = some v → v.length < n) ∧
          (∀ v, m.kyberCiphertext = some v → v.length < n))
    (hbs : bs.length < n)
    (h : mergeProtoField m tag wt bs = some (m', r)) :
    ((∀ v, m'.baseKey = some v → v.length < n) ∧
     (∀ v, m'.identityKey = some v → v.length < n) ∧
     (∀ v, m'.message = some v → v.length < n) ∧
     (∀ v, m'.kyberCiphertext = some v → v.length < n)) ∧
    r.length ≤ bs.length := by
  rcases h0 with ⟨hbk, hik, hmsg, hkyb⟩
  unfold mergeProtoField at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨v, r'⟩, hv, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨⟨hbk, hik, hmsg, hkyb⟩, mergeUint32_length hv⟩
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨v, r'⟩, hv, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have ⟨hvlen, hrlen⟩ := mergeBytes_lengths hv
    exact ⟨⟨by rintro _ ⟨rfl⟩; omega, hik, hmsg, hkyb⟩, hrlen⟩
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨v, r'⟩, hv, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have ⟨hvlen, hrlen⟩ := mergeBytes_lengths hv
    exact ⟨⟨hbk, by rintro _ ⟨rfl⟩; omega, hmsg, hkyb⟩, hrlen⟩
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨v, r'⟩, hv, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have ⟨hvlen, hrlen⟩ := mergeBytes_lengths hv
    exact ⟨⟨hbk, hik, by rintro _ ⟨rfl⟩; omega, hkyb⟩, hrlen⟩
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨v, r'⟩, hv, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨⟨hbk, hik, hmsg, hkyb⟩, mergeUint32_length hv⟩
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨v, r'⟩, hv, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨⟨hbk, hik, hmsg, hkyb⟩, mergeUint32_length hv⟩
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨v, r'⟩, hv, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨⟨hbk, hik, hmsg, hkyb⟩, mergeUint32_length hv⟩
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨v, r'⟩, hv, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have ⟨hvlen, hrlen⟩ := mergeBytes_lengths hv
    exact ⟨⟨hbk, hik, hmsg, by rintro _ ⟨rfl⟩; omega⟩, hrlen⟩
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨r', hv, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨⟨hbk, hik, hmsg, hkyb⟩, (skip_length _).1 _ _ _ _ _ hv⟩

theorem decodeProtoLoop_field_length_lt {fuel n : ℕ} {m0 m : ProtoPreKeySignalMessage}
    {bs : List (BitVec 8)}
    (h0 : (∀ v, m0.baseKey = some v → v.length < n) ∧
          (∀ v, m0.identityKey = some v → v.length < n) ∧
          (∀ v, m0.message = some v → v.length < n) ∧
          (∀ v, m0.kyberCiphertext = some v → v.length < n))
    (hbs : bs.length ≤ n)
    (hd : decodeProtoLoop fuel m0 bs = some m) :
    (∀ v, m.baseKey = some v → v.length < n) ∧
    (∀ v, m.identityKey = some v → v.length < n) ∧
    (∀ v, m.message = some v → v.length < n) ∧
    (∀ v, m.kyberCiphertext = some v → v.length < n) := by
  induction fuel generalizing m0 bs with
  | zero =>
    cases bs with
    | nil =>
      simp only [decodeProtoLoop, Option.some.injEq] at hd
      subst hd
      exact h0
    | cons _ _ => simp [decodeProtoLoop] at hd
  | succ fuel ih =>
    cases bs with
    | nil =>
      simp only [decodeProtoLoop, Option.some.injEq] at hd
      subst hd
      exact h0
    | cons b bs' =>
      simp only [decodeProtoLoop] at hd
      cases hk : decodeKey (b :: bs') with
      | none => simp [hk] at hd
      | some p =>
        obtain ⟨⟨tag, wt⟩, rest⟩ := p
        simp only [hk] at hd
        have hrest : rest.length < (b :: bs').length := decodeKey_length hk
        cases hm : mergeProtoField m0 tag wt rest with
        | none => simp [hm] at hd
        | some q =>
          obtain ⟨m', rest'⟩ := q
          simp only [hm] at hd
          have ⟨h0', hrest'⟩ := mergeProtoField_lengths h0 (Nat.lt_of_lt_of_le hrest hbs) hm
          exact ih h0' (by omega) hd

theorem decodeProtoLoop_field_length_le {fuel n : ℕ} {m0 m : ProtoPreKeySignalMessage}
    {bs : List (BitVec 8)}
    (h0 : (∀ v, m0.baseKey = some v → v.length ≤ n) ∧
          (∀ v, m0.identityKey = some v → v.length ≤ n) ∧
          (∀ v, m0.message = some v → v.length ≤ n) ∧
          (∀ v, m0.kyberCiphertext = some v → v.length ≤ n))
    (hbs : bs.length ≤ n)
    (hd : decodeProtoLoop fuel m0 bs = some m) :
    (∀ v, m.baseKey = some v → v.length ≤ n) ∧
    (∀ v, m.identityKey = some v → v.length ≤ n) ∧
    (∀ v, m.message = some v → v.length ≤ n) ∧
    (∀ v, m.kyberCiphertext = some v → v.length ≤ n) := by
  have hlt := decodeProtoLoop_field_length_lt (n := n + 1)
    ⟨fun v hv => Nat.lt_succ_of_le (h0.1 v hv),
     fun v hv => Nat.lt_succ_of_le (h0.2.1 v hv),
     fun v hv => Nat.lt_succ_of_le (h0.2.2.1 v hv),
     fun v hv => Nat.lt_succ_of_le (h0.2.2.2 v hv)⟩
    (Nat.le_succ_of_le hbs) hd
  exact ⟨fun v hv => Nat.le_of_lt_succ (hlt.1 v hv),
         fun v hv => Nat.le_of_lt_succ (hlt.2.1 v hv),
         fun v hv => Nat.le_of_lt_succ (hlt.2.2.1 v hv),
         fun v hv => Nat.le_of_lt_succ (hlt.2.2.2 v hv)⟩

theorem decodeProto_field_length_lt {body m} (hd : decodeProto body = some m) :
    (∀ v, m.baseKey = some v → v.length < body.length) ∧
    (∀ v, m.identityKey = some v → v.length < body.length) ∧
    (∀ v, m.message = some v → v.length < body.length) ∧
    (∀ v, m.kyberCiphertext = some v → v.length < body.length) :=
  decodeProtoLoop_field_length_lt
    ⟨by simp [emptyProto], by simp [emptyProto], by simp [emptyProto], by simp [emptyProto]⟩
    (Nat.le_refl _) hd

-- field slices are shorter than the input (callee bounds `< 2^32`); also for `decodeProtoLoop`
theorem decodeProto_field_length_le {body m} (hd : decodeProto body = some m) :
    (∀ v, m.baseKey = some v → v.length ≤ body.length) ∧
    (∀ v, m.identityKey = some v → v.length ≤ body.length) ∧
    (∀ v, m.message = some v → v.length ≤ body.length) ∧
    (∀ v, m.kyberCiphertext = some v → v.length ≤ body.length) := by
  have hlt := decodeProto_field_length_lt hd
  exact ⟨fun v hv => Nat.le_of_lt (hlt.1 v hv),
         fun v hv => Nat.le_of_lt (hlt.2.1 v hv),
         fun v hv => Nat.le_of_lt (hlt.2.2.1 v hv),
         fun v hv => Nat.le_of_lt (hlt.2.2.2 v hv)⟩

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.PureRecvEval
public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhSessionModel
import LibsignalBinary.Proofs.ProtoCodecRoundTrip

/-!
# Whisper Receive Codec and 32-Byte Coin Helpers

Proves 32-byte roundtrip lemmas between `HMAC.keyToBytes32` and `pureCoinsOf`
(`HKDF.bytesToKey32`), address serialization agreement, and the protobuf ciphertext length bound
`tryFrom_protoSignalCodec_ciphertext_length_le`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.Cli.Slots
open Symbolic.Swarm.CREF.CliPure

open DY.Libsignal (HwBytes)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.E2E
open CryptoVerification.E2E.Bin (Role)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.SignalSession
open Symbolic.Swarm.CREF.CliPure.TR.PureRecvEval (pureCoinsOf pureSerializeRole)

/-! ## Coin Roundtrips and Role Serialization -/

theorem keyToBytes32_length (rc : BitVec 256) : (HMAC.keyToBytes32 rc).length = 32 := by
  simp [HMAC.keyToBytes32]

theorem keyToBytes32_ne_nil (rc : BitVec 256) : HMAC.keyToBytes32 rc ≠ [] := by
  intro h
  have hlen := keyToBytes32_length rc
  rw [h] at hlen
  cases hlen

private theorem extractLsb'_zero_bytesToKey32_cons (b : BitVec 8) (acc : BitVec 256) :
    ((acc <<< 8) ||| b.zeroExtend 256).extractLsb' 0 8 = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', Nat.zero_add, hi, decide_true, Bool.true_and,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  have h256 : i < 256 := by omega
  simp [hi, h256]

private theorem extractLsb'_succ_bytesToKey32_cons (b : BitVec 8) (acc : BitVec 256) (j : Nat)
    (hj : j + 1 < 32) :
    ((acc <<< 8) ||| b.zeroExtend 256).extractLsb' (8 * (j + 1)) 8 =
      acc.extractLsb' (8 * j) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  have h1 : ¬ (8 * (j + 1) + i < 8) := by omega
  have h2 : 8 * (j + 1) + i < 256 := by omega
  have h3 : 8 * (j + 1) + i - 8 = 8 * j + i := by omega
  have hb : b.getLsbD (8 * (j + 1) + i) = false := by
    unfold BitVec.getLsbD
    exact Nat.testBit_lt_two_pow
      (lt_of_lt_of_le b.isLt (Nat.pow_le_pow_right (Nat.zero_lt_succ 1) (by omega)))
  simp [h1, h2, h3, hb]

private theorem extractLsb'_bytesToKey32 (bs : List (BitVec 8)) (j : Nat)
    (hj : j < bs.length) (h32 : j < 32) :
    (HKDF.bytesToKey32 bs).extractLsb' (8 * j) 8 = bs[j] := by
  induction bs generalizing j with
  | nil => simp at hj
  | cons b rest ih =>
    cases j with
    | zero =>
      simpa [HKDF.bytesToKey32] using
        extractLsb'_zero_bytesToKey32_cons b (HKDF.bytesToKey32 rest)
    | succ j =>
      have hcons : HKDF.bytesToKey32 (b :: rest) =
          (HKDF.bytesToKey32 rest <<< 8) ||| b.zeroExtend 256 := rfl
      rw [hcons, extractLsb'_succ_bytesToKey32_cons b (HKDF.bytesToKey32 rest) j h32,
        List.getElem_cons_succ]
      exact ih j (by simpa using hj) (by omega)

theorem bytesToKey32_keyToBytes32 (k : BitVec 256) :
    HKDF.bytesToKey32 (HMAC.keyToBytes32 k) = k := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hj : i / 8 < 32 := by omega
  have hr : i % 8 < 8 := by omega
  have hbyte := congrArg (fun b : BitVec 8 => b.getLsbD (i % 8))
    (extractLsb'_bytesToKey32 (HMAC.keyToBytes32 k) (i / 8)
      (by simp [HMAC.keyToBytes32, hj]) hj)
  simp only [HMAC.keyToBytes32, List.getElem_ofFn, BitVec.getLsbD_extractLsb', hr, decide_true,
    Bool.true_and, Nat.div_add_mod] at hbyte
  exact hbyte

theorem coinsOf_keyToBytes32 (rc : BitVec 256) :
    pureCoinsOf (HMAC.keyToBytes32 rc) = rc := by
  unfold pureCoinsOf
  have hlen1 : 32 ≤ (HMAC.keyToBytes32 rc).length := by simp [HMAC.keyToBytes32]
  have hlen2 : (HMAC.keyToBytes32 rc).length ≤ 32 := by simp [HMAC.keyToBytes32]
  rw [List.take_append_of_le_length hlen1, List.take_of_length_le hlen2,
    bytesToKey32_keyToBytes32]

theorem serializeAddrVal_role_expectedAddrs_pq (W : PEParams) (P : Party) :
    pureSerializeRole (Role.ofParty P).peer (Role.ofParty P) =
      (pqxdhSessionParams W).expectedAddrs P := by
  cases P <;> rfl

/-! ## Protobuf Ciphertext Length Bound -/

section ProtoCiphertextLen

open CryptoVerification.LibsignalProtoCodec

private theorem decodeVarintAux_rest_le (i : Nat) (acc : BitVec 64) (bs : List (BitVec 8))
    {v : BitVec 64} {rest : List (BitVec 8)}
    (h : decodeVarintAux i acc bs = some (v, rest)) : rest.length ≤ bs.length := by
  induction bs generalizing i acc with
  | nil => simp [decodeVarintAux] at h
  | cons b tail ih =>
    unfold decodeVarintAux at h
    dsimp only at h
    split at h
    · split at h
      · cases h
      · injection h with h'; injection h' with _ hr; subst hr; simp
    · split at h
      · cases h
      · exact Nat.le_trans (ih (i + 1) _ h) (Nat.le_succ _)

private theorem decodeVarint_rest_le {bs : List (BitVec 8)} {v : BitVec 64} {rest : List (BitVec 8)}
    (h : decodeVarint bs = some (v, rest)) : rest.length ≤ bs.length :=
  decodeVarintAux_rest_le 0 0 bs h

private theorem decodeKey_rest_le {bs : List (BitVec 8)} {kw : Nat × WireType} {rest : List (BitVec 8)}
    (h : decodeKey bs = some (kw, rest)) : rest.length ≤ bs.length := by
  unfold decodeKey at h
  rcases hv : decodeVarint bs with _ | ⟨key, r0⟩
  · simp [hv] at h
  · rw [hv] at h; dsimp only at h
    split at h
    · cases h
    · rcases hw : WireType.ofNat? (key.toNat % 8) with _ | wt
      · simp [hw] at h
      · rw [hw] at h; dsimp only at h
        split at h
        · cases h
        · injection h with h'; injection h' with _ hr; subst hr
          exact decodeVarint_rest_le hv

private theorem skipScalar_rest_le {wt : WireType} {bs rest : List (BitVec 8)}
    (h : skipScalar wt bs = some rest) : rest.length ≤ bs.length := by
  cases wt with
  | varint =>
    simp only [skipScalar, Option.map_eq_some_iff] at h
    obtain ⟨⟨_, r0⟩, hv, rfl⟩ := h
    exact decodeVarint_rest_le hv
  | thirtyTwoBit =>
    simp only [skipScalar, skipBytes] at h
    split at h
    · cases h
    · injection h with hr; subst hr; simp
  | sixtyFourBit =>
    simp only [skipScalar, skipBytes] at h
    split at h
    · cases h
    · injection h with hr; subst hr; simp
  | lengthDelimited =>
    simp only [skipScalar] at h
    rcases hv : decodeVarint bs with _ | ⟨len, r0⟩
    · simp [hv] at h
    · rw [hv] at h; simp only [skipBytes] at h
      split at h
      · cases h
      · injection h with hr; subst hr
        have hr0 := decodeVarint_rest_le hv
        simp; omega
  | startGroup => simp [skipScalar] at h
  | endGroup => simp [skipScalar] at h

private theorem skipField_and_Group_rest_le (fuel : Nat) :
    (∀ depth tag wt bs rest, skipField fuel depth tag wt bs = some rest → rest.length ≤ bs.length) ∧
    (∀ depth tag bs rest, skipGroup fuel depth tag bs = some rest → rest.length ≤ bs.length) := by
  induction fuel with
  | zero =>
    exact ⟨fun _ _ _ _ _ h => by simp [skipField] at h,
           fun _ _ _ _ h => by simp [skipGroup] at h⟩
  | succ f ih =>
    refine ⟨fun depth tag wt bs rest h => ?_, fun depth tag bs rest h => ?_⟩
    · unfold skipField at h
      split at h
      · cases h
      · cases wt with
        | endGroup => cases h
        | startGroup => exact ih.2 depth tag bs rest h
        | varint | sixtyFourBit | lengthDelimited | thirtyTwoBit => exact skipScalar_rest_le h
    · unfold skipGroup at h
      rcases hk : decodeKey bs with _ | ⟨⟨itag, iwt⟩, r0⟩
      · simp [hk] at h
      · rw [hk] at h
        have hr0 := decodeKey_rest_le hk
        cases iwt <;> dsimp only at h
        case endGroup =>
          split at h
          · injection h with hr; subst hr; exact hr0
          · cases h
        all_goals
          split at h
          · cases h
          · rename_i r1 hs
            exact Nat.le_trans (ih.2 depth tag r1 rest h) (Nat.le_trans (ih.1 _ _ _ _ _ hs) hr0)

private theorem mergeBytes_len_le {wt : WireType} {bs v rest : List (BitVec 8)}
    (h : mergeBytes wt bs = some (v, rest)) : v.length ≤ bs.length ∧ rest.length ≤ bs.length := by
  unfold mergeBytes at h
  split at h
  · cases h
  · rcases hv : decodeVarint bs with _ | ⟨len, r0⟩
    · simp [hv] at h
    · rw [hv] at h; dsimp only at h
      split at h
      · cases h
      · injection h with h'; injection h' with hv_eq hr_eq; subst hv_eq hr_eq
        have hr0 := decodeVarint_rest_le hv
        exact ⟨by simp; omega, by simp; omega⟩

private theorem mergeUint32_rest_le {wt : WireType} {bs : List (BitVec 8)}
    {v : BitVec 32} {rest : List (BitVec 8)}
    (h : mergeUint32 wt bs = some (v, rest)) : rest.length ≤ bs.length := by
  unfold mergeUint32 at h
  split at h
  · cases h
  · rcases hv : decodeVarint bs with _ | ⟨_, r0⟩
    · simp [hv] at h
    · rw [hv] at h; dsimp only at h
      injection h with h'; injection h' with _ hr; subst hr
      exact decodeVarint_rest_le hv

private theorem mergeField_ct_le {m m' : ProtoSignalMessage} {tag : Nat} {wt : WireType}
    {bs rest : List (BitVec 8)} (h : mergeField m tag wt bs = some (m', rest)) :
    rest.length ≤ bs.length ∧
    (∀ ct, m'.ciphertext = some ct → m.ciphertext = some ct ∨ ct.length ≤ bs.length) := by
  unfold mergeField at h
  match tag with
  | 1 =>
    rcases hm : mergeBytes wt bs with _ | ⟨v, r0⟩
    · simp [hm] at h
    · rw [hm] at h; injection h with h'; injection h' with hm' hr'; subst hm' hr'
      exact ⟨(mergeBytes_len_le hm).2, fun ct hct => Or.inl hct⟩
  | 2 =>
    rcases hm : mergeUint32 wt bs with _ | ⟨v, r0⟩
    · simp [hm] at h
    · rw [hm] at h; injection h with h'; injection h' with hm' hr'; subst hm' hr'
      exact ⟨mergeUint32_rest_le hm, fun ct hct => Or.inl hct⟩
  | 3 =>
    rcases hm : mergeUint32 wt bs with _ | ⟨v, r0⟩
    · simp [hm] at h
    · rw [hm] at h; injection h with h'; injection h' with hm' hr'; subst hm' hr'
      exact ⟨mergeUint32_rest_le hm, fun ct hct => Or.inl hct⟩
  | 4 =>
    rcases hm : mergeBytes wt bs with _ | ⟨v, r0⟩
    · simp [hm] at h
    · rw [hm] at h; injection h with h'; injection h' with hm' hr'; subst hm' hr'
      obtain ⟨hv, hr0⟩ := mergeBytes_len_le hm
      refine ⟨hr0, fun ct hct => Or.inr ?_⟩
      injection hct with hct'; subst hct'; exact hv
  | 5 =>
    rcases hm : mergeBytes wt bs with _ | ⟨v, r0⟩
    · simp [hm] at h
    · rw [hm] at h; injection h with h'; injection h' with hm' hr'; subst hm' hr'
      exact ⟨(mergeBytes_len_le hm).2, fun ct hct => Or.inl hct⟩
  | 6 =>
    rcases hm : mergeBytes wt bs with _ | ⟨v, r0⟩
    · simp [hm] at h
    · rw [hm] at h; injection h with h'; injection h' with hm' hr'; subst hm' hr'
      exact ⟨(mergeBytes_len_le hm).2, fun ct hct => Or.inl hct⟩
  | n + 7 =>
    change (skipField (2 * bs.length + 2) recursionLimit (n + 7) wt bs).map (fun r => (m, r)) =
      some (m', rest) at h
    rcases hs : skipField (2 * bs.length + 2) recursionLimit (n + 7) wt bs with _ | r0
    · simp [hs] at h
    · rw [hs] at h; injection h with h'; injection h' with hm' hr'; subst hm' hr'
      exact ⟨(skipField_and_Group_rest_le _).1 _ _ _ _ _ hs, fun ct hct => Or.inl hct⟩
  | 0 =>
    change (skipField (2 * bs.length + 2) recursionLimit 0 wt bs).map (fun r => (m, r)) =
      some (m', rest) at h
    rcases hs : skipField (2 * bs.length + 2) recursionLimit 0 wt bs with _ | r0
    · simp [hs] at h
    · rw [hs] at h; injection h with h'; injection h' with hm' hr'; subst hm' hr'
      exact ⟨(skipField_and_Group_rest_le _).1 _ _ _ _ _ hs, fun ct hct => Or.inl hct⟩

private theorem decodeLoop_ct_le (fuel : Nat) (m m_out : ProtoSignalMessage) (bs : List (BitVec 8))
    (h : decodeLoop fuel m bs = some m_out) :
    ∀ ct, m_out.ciphertext = some ct → m.ciphertext = some ct ∨ ct.length ≤ bs.length := by
  induction fuel generalizing m bs with
  | zero =>
    cases bs with
    | nil => injection h with hm; subst hm; exact fun ct hct => Or.inl hct
    | cons _ _ => simp [decodeLoop] at h
  | succ f ih =>
    cases bs with
    | nil => injection h with hm; subst hm; exact fun ct hct => Or.inl hct
    | cons b tail =>
      unfold decodeLoop at h
      rcases hk : decodeKey (b :: tail) with _ | ⟨⟨tag, wt⟩, rest⟩
      · simp [hk] at h
      · rw [hk] at h; dsimp only at h
        rcases hm : mergeField m tag wt rest with _ | ⟨m', rest'⟩
        · simp [hm] at h
        · rw [hm] at h
          have hk_le := decodeKey_rest_le hk
          obtain ⟨hm_le, hm_ct⟩ := mergeField_ct_le hm
          intro ct hct
          rcases ih m' rest' h ct hct with hm'ct | hlen
          · rcases hm_ct ct hm'ct with hmct | hlen
            · exact Or.inl hmct
            · exact Or.inr (Nat.le_trans hlen hk_le)
          · exact Or.inr (Nat.le_trans hlen (Nat.le_trans hm_le hk_le))

theorem tryFrom_protoSignalCodec_ciphertext_length_le {body : HwBytes} {msg : SignalMessage}
    (h : SignalMessage.tryFrom protoSignalCodec body = .ok msg) :
    msg.ciphertext.length ≤ body.length := by
  unfold SignalMessage.tryFrom at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rcases hd : protoSignalCodec.decode ((body.take (body.length - macLength)).drop 1) with _ | p
        · rw [hd] at h; cases h
        · rw [hd] at h; dsimp only at h
          rcases hrk : p.ratchetKey with _ | rk
          · rw [hrk] at h; cases h
          · rw [hrk] at h; dsimp only at h
            rcases hpk : PublicKey.deserialize rk with _ | spk
            · rw [hpk] at h; cases h
            · rw [hpk] at h; dsimp only at h
              rcases hctr : p.counter with _ | ctr
              · rw [hctr] at h; cases h
              · rw [hctr] at h; dsimp only at h
                rcases hct : p.ciphertext with _ | ct
                · rw [hct] at h; cases h
                · rw [hct] at h
                  injection h with hmsg; subst hmsg
                  have hd' : decodeLoop ((body.take (body.length - macLength)).drop 1).length emptyProtoSignalMessage
                      ((body.take (body.length - macLength)).drop 1) = some p := hd
                  rcases decodeLoop_ct_le _ _ _ _ hd' ct hct with hemp | hle
                  · cases hemp
                  · have hdrop : ((body.take (body.length - macLength)).drop 1).length ≤ body.length := by
                      simp; omega
                    exact Nat.le_trans hle hdrop

end ProtoCiphertextLen

end Symbolic.Swarm.CREF.Cli.Slots

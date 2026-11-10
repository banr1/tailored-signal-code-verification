/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalProtoCodec
public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDecDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.EffSalt
public import LibsignalBinary.Specifications.CryptoGames.AEAD.EtMDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HKDFDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HMACDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.LibsignalAead
public import LibsignalBinary.Specifications.CryptoGames.AEAD.MacPrecompDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.WireAeadDefs
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Construction
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Defs
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Security
public import LibsignalBinary.Specifications.CryptoGames.PRNG.Defs
public import LibsignalBinary.Specifications.CryptoGames.Primitives
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.ChainDefs
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.CreateChainDefs
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSession
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.RootKdfDefs
public import LibsignalBinary.Specifications.HkdfSalt
public import LibsignalBinary.Specifications.LibsignalSignalMessage

set_option autoImplicit false

/-!
# Round-Trip Correctness of `protoSignalCodec`

**Checked by Lean.** Proves `protoSignalCodec_roundTrip`: `protoSignalCodec.decode` left-inverts
`protoSignalCodec.encode` on every `ProtoSignalMessage` satisfying `LengthsFit` (all byte-slice
fields strictly shorter than `2^64`).

The `LengthsFit` bound is necessary because `encodeBytesField` truncates `v.length` to a 64-bit
Rust `usize` (`BitVec.ofNat 64 v.length`), so a field of length `2^64` encodes with length varint `0`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalProtoCodec

open CryptoGames.LibsignalSession

private theorem testBit_127_of_lt {m : ℕ} (hm : m < 7) : (127 : ℕ).testBit m = true := by
  match m, hm with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ => decide

private theorem testBit_127_of_ge {m : ℕ} (hm : 7 ≤ m) : (127 : ℕ).testBit m = false :=
  Nat.testBit_lt_two_pow
    (Nat.lt_of_lt_of_le (by decide : 127 < 2 ^ 7) (Nat.pow_le_pow_right (by omega) hm))

private theorem testBit_128_of_lt {m : ℕ} (hm : m < 7) : (128 : ℕ).testBit m = false := by
  match m, hm with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ => decide

private theorem getLsbD_false_of_toNat_lt {w : ℕ} (x : BitVec w) {k m : ℕ}
    (hx : x.toNat < 2 ^ k) (hm : k ≤ m) : x.getLsbD m = false := by
  change x.toNat.testBit m = false
  exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hm))

private theorem getLsbD_0x7f_8 {m : ℕ} : (0x7F : BitVec 8).getLsbD m = decide (m < 7) := by
  change ((0x7F : BitVec 8).toNat).testBit m = decide (m < 7)
  have h127 : (0x7F : BitVec 8).toNat = 127 := rfl
  rw [h127]
  by_cases hm : m < 7
  · simp [hm, testBit_127_of_lt hm]
  · have hm' : 7 ≤ m := by omega
    simp [hm, testBit_127_of_ge hm']

private theorem getLsbD_0x7f_64 {m : ℕ} : (0x7F : BitVec 64).getLsbD m = decide (m < 7) := by
  change ((0x7F : BitVec 64).toNat).testBit m = decide (m < 7)
  have h127 : (0x7F : BitVec 64).toNat = 127 := rfl
  rw [h127]
  by_cases hm : m < 7
  · simp [hm, testBit_127_of_lt hm]
  · have hm' : 7 ≤ m := by omega
    simp [hm, testBit_127_of_ge hm']

private theorem getLsbD_0x80_64_of_lt {m : ℕ} (hm : m < 7) :
    (0x80 : BitVec 64).getLsbD m = false := by
  change ((0x80 : BitVec 64).toNat).testBit m = false
  exact testBit_128_of_lt hm

private theorem ushiftRight_63_toNat_lt_two (v : BitVec 64) : (v >>> 63).toNat < 2 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hv : v.toNat < 2 ^ 64 := v.isLt
  omega

private theorem cont_byte_gt_0x7f (w : BitVec 64) :
    ¬ (((w &&& 0x7F) ||| 0x80).setWidth 8).toNat ≤ 0x7F := by
  intro hle
  have hlt : (((w &&& 0x7F) ||| 0x80).setWidth 8).toNat < 2 ^ 7 := by omega
  have hf := getLsbD_false_of_toNat_lt (((w &&& 0x7F) ||| 0x80).setWidth 8) hlt (le_refl 7)
  have ht : (((w &&& 0x7F) ||| 0x80).setWidth 8).getLsbD 7 = true := by
    rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_or]
    simp
  rw [ht] at hf
  exact Bool.noConfusion hf

private theorem ushiftRight_ushiftRight_seven (v : BitVec 64) (i : ℕ) :
    (v >>> (7 * i)) >>> 7 = v >>> (7 * (i + 1)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j _
  rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ushiftRight]
  congr 1
  omega

private theorem decodeVarintAux_encodeVarintAux :
    ∀ (k i : ℕ) (v acc : BitVec 64) (rest : List (BitVec 8)),
      i + k = 10 →
      1 ≤ k →
      (∀ j < 64, acc.getLsbD j = (decide (j < 7 * i) && v.getLsbD j)) →
      decodeVarintAux i acc (encodeVarintAux k (v >>> (7 * i)) ++ rest) = some (v, rest)
  | 0, _, _, _, _, _, hk, _ => by omega
  | k + 1, i, v, acc, rest, hik, _, hacc => by
    unfold encodeVarintAux
    by_cases hw : (v >>> (7 * i)).toNat < 0x80
    · simp only [hw, ↓reduceIte, List.singleton_append]
      unfold decodeVarintAux
      have hb_le : ((v >>> (7 * i)).setWidth 8).toNat ≤ 0x7F := by
        rw [BitVec.toNat_setWidth]
        omega
      have hb_i9 : ¬ (i = 9 ∧ 0x02 ≤ ((v >>> (7 * i)).setWidth 8).toNat) := by
        rintro ⟨rfl, h2⟩
        rw [BitVec.toNat_setWidth] at h2
        have hlt2 := ushiftRight_63_toNat_lt_two v
        have h63 : 7 * 9 = 63 := rfl
        rw [h63] at h2
        omega
      simp only [hb_le, ↓reduceIte, hb_i9]
      congr 2
      apply BitVec.eq_of_getLsbD_eq
      intro j hj
      rw [BitVec.getLsbD_or, hacc j hj, BitVec.getLsbD_shiftLeft, BitVec.zeroExtend,
        BitVec.getLsbD_setWidth, BitVec.getLsbD_and, BitVec.getLsbD_setWidth, getLsbD_0x7f_8,
        BitVec.getLsbD_ushiftRight]
      by_cases h1 : j < 7 * i
      · simp [hj, h1]
      · by_cases h2 : j < 7 * i + 7
        · have hm7 : j - 7 * i < 7 := by omega
          have hm8 : j - 7 * i < 8 := by omega
          have hm64 : j - 7 * i < 64 := by omega
          have hadd : 7 * i + (j - 7 * i) = j := by omega
          simp [hj, h1, hm7, hm8, hm64, hadd]
        · have hm7 : ¬ (j - 7 * i < 7) := by omega
          have hvj : v.getLsbD j = false := by
            have hadd : j = 7 * i + (j - 7 * i) := by omega
            rw [hadd, ← BitVec.getLsbD_ushiftRight]
            exact getLsbD_false_of_toNat_lt (k := 7) (v >>> (7 * i)) hw (by omega)
          rw [hvj]
          simp [hj, h1, hm7]
    · simp only [hw, ↓reduceIte, List.cons_append]
      have hk1 : 1 ≤ k := by
        by_cases hk0 : k = 0
        · subst hk0
          have hi9 : i = 9 := by omega
          subst hi9
          have hlt2 := ushiftRight_63_toNat_lt_two v
          have h63 : 7 * 9 = 63 := rfl
          rw [h63] at hw
          omega
        · omega
      have hi9 : i ≠ 9 := by omega
      unfold decodeVarintAux
      have hb_gt := cont_byte_gt_0x7f (v >>> (7 * i))
      simp only [hb_gt, ↓reduceIte, hi9]
      rw [ushiftRight_ushiftRight_seven]
      apply decodeVarintAux_encodeVarintAux k (i + 1) v _ rest (by omega) hk1
      intro j hj
      rw [BitVec.getLsbD_or, hacc j hj, BitVec.getLsbD_shiftLeft, BitVec.zeroExtend,
        BitVec.getLsbD_setWidth, BitVec.getLsbD_and, BitVec.getLsbD_setWidth, BitVec.getLsbD_or,
        BitVec.getLsbD_and, getLsbD_0x7f_8, getLsbD_0x7f_64, BitVec.getLsbD_ushiftRight]
      by_cases h1 : j < 7 * i
      · have h1' : j < 7 * (i + 1) := by omega
        simp [hj, h1, h1']
      · by_cases h2 : j < 7 * (i + 1)
        · have hm7 : j - 7 * i < 7 := by omega
          have hm8 : j - 7 * i < 8 := by omega
          have hm64 : j - 7 * i < 64 := by omega
          have h80 := getLsbD_0x80_64_of_lt hm7
          have hadd : 7 * i + (j - 7 * i) = j := by omega
          rw [h80]
          simp [hj, h1, h2, hm7, hm8, hm64, hadd]
        · have hm7 : ¬ (j - 7 * i < 7) := by omega
          simp [hj, h1, h2, hm7]

/-- `decodeVarint` left-inverts `encodeVarint` for any trailing byte suffix `rest`. -/
theorem decodeVarint_encodeVarint (v : BitVec 64) (rest : List (BitVec 8)) :
    decodeVarint (encodeVarint v ++ rest) = some (v, rest) := by
  unfold decodeVarint encodeVarint
  have hv0 : v = v >>> (7 * 0) := by simp
  conv_lhs => rw [hv0]
  apply decodeVarintAux_encodeVarintAux 10 0 v 0 rest rfl (by omega)
  intro j _
  simp

theorem encodeVarint_ne_nil (v : BitVec 64) : encodeVarint v ≠ [] := by
  unfold encodeVarint encodeVarintAux
  split <;> simp

private theorem wireType_toNat_lt_eight (wt : WireType) : wt.toNat < 8 := by
  cases wt <;> decide

private theorem wireType_ofNat_toNat (wt : WireType) : WireType.ofNat? wt.toNat = some wt := by
  cases wt <;> rfl

theorem decodeKey_encodeKey (t : ℕ) (wt : WireType) (rest : List (BitVec 8)) (h1 : 1 ≤ t)
    (h2 : t < 2 ^ 28) : decodeKey (encodeKey t wt ++ rest) = some ((t, wt), rest) := by
  unfold decodeKey encodeKey
  rw [decodeVarint_encodeVarint]
  dsimp only
  have hwt : wt.toNat < 8 := wireType_toNat_lt_eight wt
  have hkey_toNat : (BitVec.ofNat 64 (t * 8 + wt.toNat)).toNat = t * 8 + wt.toNat := by
    rw [BitVec.toNat_ofNat]
    omega
  rw [hkey_toNat]
  have hlt32 : ¬ (2 ^ 32 ≤ t * 8 + wt.toNat) := by omega
  have hmod : (t * 8 + wt.toNat) % 8 = wt.toNat := by omega
  have hdiv : (t * 8 + wt.toNat) / 8 = t := by omega
  have htag : ¬ (t < 1) := by omega
  simp only [hlt32, ↓reduceIte, hmod, wireType_ofNat_toNat, hdiv, htag]

theorem mergeBytes_encode (v rest : List (BitVec 8)) (h : v.length < 2 ^ 64) :
    mergeBytes .lengthDelimited (encodeVarint (BitVec.ofNat 64 v.length) ++ (v ++ rest)) =
      some (v, rest) := by
  unfold mergeBytes
  simp only [ne_eq, not_true_eq_false, ↓reduceIte, decodeVarint_encodeVarint]
  have hlen : (BitVec.ofNat 64 v.length).toNat = v.length := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt h
  rw [hlen]
  simp

theorem mergeUint32_encode (x : BitVec 32) (rest : List (BitVec 8)) :
    mergeUint32 .varint (encodeVarint (x.zeroExtend 64) ++ rest) = some (x, rest) := by
  unfold mergeUint32
  simp only [ne_eq, not_true_eq_false, ↓reduceIte, decodeVarint_encodeVarint]
  congr 2
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.zeroExtend, BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  have hx : x.toNat < 2 ^ 32 := x.isLt
  omega

/-- `decodeLoop` reaches `r` from `m` on `bs` with any fuel that covers the input. -/
def LoopsTo (m : ProtoSignalMessage) (bs : List (BitVec 8)) (r : ProtoSignalMessage) : Prop :=
  ∀ n, bs.length ≤ n → decodeLoop n m bs = some r

theorem loopsTo_nil (m : ProtoSignalMessage) : LoopsTo m [] m := by
  intro n _
  cases n <;> rfl

/-- Peel one encoded `(tag, wireType)` field off `decodeLoop` via `mergeField`. -/
theorem loopsTo_field (t : ℕ) (wt : WireType) (h1 : 1 ≤ t) (h2 : t < 2 ^ 28)
    (m m' r : ProtoSignalMessage) (body rest : List (BitVec 8))
    (hmerge : mergeField m t wt (body ++ rest) = some (m', rest)) (h : LoopsTo m' rest r) :
    LoopsTo m (encodeKey t wt ++ (body ++ rest)) r := by
  intro n hn
  have hne : encodeKey t wt ≠ [] := encodeVarint_ne_nil _
  have hpos : 1 ≤ (encodeKey t wt).length := List.length_pos_iff.mpr hne
  have hlen : 1 + rest.length ≤ (encodeKey t wt ++ (body ++ rest)).length := by
    simp only [List.length_append]
    omega
  cases n with
  | zero => omega
  | succ fuel =>
    cases h_bs : encodeKey t wt ++ (body ++ rest) with
    | nil =>
      rw [h_bs] at hlen
      simp at hlen
    | cons b bs_tail =>
      unfold decodeLoop
      rw [← h_bs, decodeKey_encodeKey t wt (body ++ rest) h1 h2]
      dsimp only
      rw [hmerge]
      exact h fuel (by omega)

/-- Every `bytes` field of `m` has length strictly less than `2^64`. -/
def LengthsFit (m : ProtoSignalMessage) : Prop :=
  ∀ v, m.ratchetKey = some v ∨ m.ciphertext = some v ∨ m.pqRatchet = some v ∨ m.addresses = some v →
    v.length < 2 ^ 64

private theorem loopsTo_opt_bytes (t : ℕ) (h1 : 1 ≤ t) (h2 : t < 2 ^ 28)
    (opt : Option (List (BitVec 8))) (m m' r : ProtoSignalMessage) (rest : List (BitVec 8))
    (hnone : opt = none → m = m')
    (hsome : ∀ v, opt = some v →
      mergeField m t .lengthDelimited
        (encodeVarint (BitVec.ofNat 64 v.length) ++ (v ++ rest)) = some (m', rest))
    (h : LoopsTo m' rest r) :
    LoopsTo m (encodeBytesField t opt ++ rest) r := by
  cases opt with
  | none =>
    have hm := hnone rfl
    subst hm
    simpa [encodeBytesField] using h
  | some v =>
    have hmf := hsome v rfl
    simpa only [encodeBytesField, List.append_assoc] using
      loopsTo_field t .lengthDelimited h1 h2 m m' r
        (encodeVarint (BitVec.ofNat 64 v.length) ++ v) rest
        (by simpa only [List.append_assoc] using hmf) h

private theorem loopsTo_opt_uint32 (t : ℕ) (h1 : 1 ≤ t) (h2 : t < 2 ^ 28)
    (opt : Option (BitVec 32)) (m m' r : ProtoSignalMessage) (rest : List (BitVec 8))
    (hnone : opt = none → m = m')
    (hsome : ∀ x, opt = some x →
      mergeField m t .varint (encodeVarint (x.zeroExtend 64) ++ rest) = some (m', rest))
    (h : LoopsTo m' rest r) :
    LoopsTo m (encodeUint32Field t opt ++ rest) r := by
  cases opt with
  | none =>
    have hm := hnone rfl
    subst hm
    simpa [encodeUint32Field] using h
  | some x =>
    simpa only [encodeUint32Field, List.append_assoc] using
      loopsTo_field t .varint h1 h2 m m' r
        (encodeVarint (x.zeroExtend 64)) rest (hsome x rfl) h

/-- `protoSignalCodec.decode` left-inverts `protoSignalCodec.encode` whenever `LengthsFit m` holds. -/
theorem protoSignalCodec_roundTrip (m : ProtoSignalMessage) (h : LengthsFit m) :
    protoSignalCodec.decode (protoSignalCodec.encode m) = some m := by
  change decodeLoop (encode m).length emptyProtoSignalMessage (encode m) = some m
  suffices hloop : LoopsTo emptyProtoSignalMessage (encode m) m from
    hloop (encode m).length (le_refl _)
  unfold encode
  simp only [List.append_assoc]
  let s0 := emptyProtoSignalMessage
  let s1 : ProtoSignalMessage := { s0 with ratchetKey := m.ratchetKey }
  let s2 : ProtoSignalMessage := { s1 with counter := m.counter }
  let s3 : ProtoSignalMessage := { s2 with previousCounter := m.previousCounter }
  let s4 : ProtoSignalMessage := { s3 with ciphertext := m.ciphertext }
  let s5 : ProtoSignalMessage := { s4 with pqRatchet := m.pqRatchet }
  let s6 : ProtoSignalMessage := { s5 with addresses := m.addresses }
  have hs6 : s6 = m := by cases m; rfl
  rw [← List.append_nil (encodeBytesField 6 m.addresses)]
  refine loopsTo_opt_bytes 1 (by omega) (by omega) m.ratchetKey s0 s1 m _
    (fun hn => by simp [s0, s1, emptyProtoSignalMessage, hn])
    (fun v hv => ?_) ?_
  · unfold mergeField
    rw [mergeBytes_encode v _ (h v (Or.inl hv))]
    simp [s1, hv]
  refine loopsTo_opt_uint32 2 (by omega) (by omega) m.counter s1 s2 m _
    (fun hn => by simp [s0, s1, s2, emptyProtoSignalMessage, hn])
    (fun x hx => ?_) ?_
  · unfold mergeField
    rw [mergeUint32_encode]
    simp [s2, hx]
  refine loopsTo_opt_uint32 3 (by omega) (by omega) m.previousCounter s2 s3 m _
    (fun hn => by simp [s0, s1, s2, s3, emptyProtoSignalMessage, hn])
    (fun x hx => ?_) ?_
  · unfold mergeField
    rw [mergeUint32_encode]
    simp [s3, hx]
  refine loopsTo_opt_bytes 4 (by omega) (by omega) m.ciphertext s3 s4 m _
    (fun hn => by simp [s0, s1, s2, s3, s4, emptyProtoSignalMessage, hn])
    (fun v hv => ?_) ?_
  · unfold mergeField
    rw [mergeBytes_encode v _ (h v (Or.inr (Or.inl hv)))]
    simp [s4, hv]
  refine loopsTo_opt_bytes 5 (by omega) (by omega) m.pqRatchet s4 s5 m _
    (fun hn => by simp [s0, s1, s2, s3, s4, s5, emptyProtoSignalMessage, hn])
    (fun v hv => ?_) ?_
  · unfold mergeField
    rw [mergeBytes_encode v _ (h v (Or.inr (Or.inr (Or.inl hv))))]
    simp [s5, hv]
  refine loopsTo_opt_bytes 6 (by omega) (by omega) m.addresses s5 s6 m []
    (fun hn => by simp [s0, s1, s2, s3, s4, s5, s6, emptyProtoSignalMessage, hn])
    (fun v hv => ?_) ?_
  · unfold mergeField
    rw [mergeBytes_encode v [] (h v (Or.inr (Or.inr (Or.inr hv))))]
    simp [s6, hv]
  · rw [hs6]
    exact loopsTo_nil m

/-! ## Fuel Sufficiency

Any fuel `n ≥ bs.length` for `decodeLoop` (and `n ≥ 2 * bs.length + 2` for `skipField` /
`skipGroup`) yields the same result, since each step consumes at least one input byte. -/

theorem decodeVarintAux_length (i : ℕ) (acc : BitVec 64) (bs : List (BitVec 8))
    (v : BitVec 64) (rest : List (BitVec 8)) (h : decodeVarintAux i acc bs = some (v, rest)) :
    rest.length < bs.length := by
  induction bs generalizing i acc with
  | nil => simp [decodeVarintAux] at h
  | cons b bs ih =>
    simp only [decodeVarintAux] at h
    split at h
    · split at h
      · simp at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        simp
    · split at h
      · simp at h
      · have := ih _ _ h
        simp only [List.length_cons]
        omega

theorem decodeVarint_length {bs rest : List (BitVec 8)} {v : BitVec 64}
    (h : decodeVarint bs = some (v, rest)) : rest.length < bs.length :=
  decodeVarintAux_length 0 0 bs v rest h

theorem decodeKey_length {bs rest : List (BitVec 8)} {k : ℕ × WireType}
    (h : decodeKey bs = some (k, rest)) : rest.length < bs.length := by
  unfold decodeKey at h
  split at h
  · simp at h
  · rename_i key r hv
    split at h
    · simp at h
    · split at h
      · simp at h
      · dsimp only at h
        split at h
        · simp at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          exact decodeVarint_length hv

theorem skipScalar_length {wt : WireType} {bs r : List (BitVec 8)}
    (h : skipScalar wt bs = some r) : r.length ≤ bs.length := by
  cases wt with
  | varint =>
    simp only [skipScalar, Option.map_eq_some_iff] at h
    obtain ⟨⟨v, r'⟩, hv, rfl⟩ := h
    exact Nat.le_of_lt (decodeVarint_length hv)
  | thirtyTwoBit =>
    simp only [skipScalar, skipBytes] at h
    split at h
    · simp at h
    · simp only [Option.some.injEq] at h; subst h; simp
  | sixtyFourBit =>
    simp only [skipScalar, skipBytes] at h
    split at h
    · simp at h
    · simp only [Option.some.injEq] at h; subst h; simp
  | lengthDelimited =>
    simp only [skipScalar] at h
    split at h
    · simp at h
    · rename_i len r' hv
      simp only [skipBytes] at h
      split at h
      · simp at h
      · simp only [Option.some.injEq] at h
        subst h
        have := decodeVarint_length hv
        simp only [List.length_drop]
        omega
  | startGroup => simp [skipScalar] at h
  | endGroup => simp [skipScalar] at h

theorem skip_length (fuel : ℕ) :
    (∀ d t wt (bs r : List (BitVec 8)), skipField fuel d t wt bs = some r →
      r.length ≤ bs.length) ∧
    (∀ d t (bs r : List (BitVec 8)), skipGroup fuel d t bs = some r → r.length ≤ bs.length) := by
  induction fuel with
  | zero => exact ⟨fun _ _ _ _ _ h => by simp [skipField] at h,
      fun _ _ _ _ h => by simp [skipGroup] at h⟩
  | succ f ih =>
    refine ⟨fun d t wt bs r h => ?_, fun d t bs r h => ?_⟩
    · simp only [skipField] at h
      split at h
      · simp at h
      · cases wt with
        | endGroup => simp at h
        | startGroup => exact ih.2 _ _ _ _ h
        | varint => exact skipScalar_length h
        | thirtyTwoBit => exact skipScalar_length h
        | sixtyFourBit => exact skipScalar_length h
        | lengthDelimited => exact skipScalar_length h
    · simp only [skipGroup] at h
      split at h
      · simp at h
      · rename_i itag rest hk
        split at h
        · simp only [Option.some.injEq] at h
          subst h
          exact Nat.le_of_lt (decodeKey_length hk)
        · simp at h
      · rename_i itag iwt rest _ hk
        split at h
        · simp at h
        · rename_i rest' hs
          have h1 := ih.1 _ _ _ _ _ hs
          have h2 := ih.2 _ _ _ _ h
          have h3 := decodeKey_length hk
          omega


theorem skip_fuel (n₁ : ℕ) :
    (∀ n₂ d t wt (bs : List (BitVec 8)), 2 * bs.length + 2 ≤ n₁ → 2 * bs.length + 2 ≤ n₂ →
      skipField n₁ d t wt bs = skipField n₂ d t wt bs) ∧
    (∀ n₂ d t (bs : List (BitVec 8)), 2 * bs.length + 1 ≤ n₁ → 2 * bs.length + 1 ≤ n₂ →
      skipGroup n₁ d t bs = skipGroup n₂ d t bs) := by
  induction n₁ with
  | zero => exact ⟨fun _ _ _ _ _ h => by omega, fun _ _ _ _ h => by omega⟩
  | succ f ih =>
    refine ⟨fun n₂ d t wt bs h₁ h₂ => ?_, fun n₂ d t bs h₁ h₂ => ?_⟩
    · obtain ⟨g, rfl⟩ : ∃ g, n₂ = g + 1 := ⟨n₂ - 1, by omega⟩
      simp only [skipField]
      by_cases hd : d = 0
      · simp [hd]
      · simp only [hd, ↓reduceIte]
        cases wt with
        | startGroup => exact ih.2 g d t bs (by omega) (by omega)
        | endGroup => rfl
        | varint => rfl
        | thirtyTwoBit => rfl
        | sixtyFourBit => rfl
        | lengthDelimited => rfl
    · obtain ⟨g, rfl⟩ : ∃ g, n₂ = g + 1 := ⟨n₂ - 1, by omega⟩
      simp only [skipGroup]
      cases hk : decodeKey bs with
      | none => rfl
      | some p =>
        obtain ⟨⟨itag, iwt⟩, rest⟩ := p
        have hr := decodeKey_length hk
        cases iwt
        case endGroup => rfl
        all_goals
          dsimp only
          rw [ih.1 g _ _ _ rest (by omega) (by omega)]
          cases hs : skipField g (d - 1) itag _ rest with
          | none => rfl
          | some rest' =>
            have := (skip_length g).1 _ _ _ _ _ hs
            exact ih.2 g d t rest' (by omega) (by omega)

/-- Any fuel `n ≥ 2 * bs.length + 2` suffices for `skipField`. -/
theorem skipField_fuel (n d t : ℕ) (wt : WireType) (bs : List (BitVec 8))
    (h : 2 * bs.length + 2 ≤ n) :
    skipField n d t wt bs = skipField (2 * bs.length + 2) d t wt bs :=
  (skip_fuel n).1 _ d t wt bs h (Nat.le_refl _)

end CryptoVerification.LibsignalProtoCodec

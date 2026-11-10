/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ProtoCodecRoundTrip
public import Symbolic.Specifications.Refinement.WireFormat
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import VCVio.EvalDist.ProbabilityNotation

/-!
# Soundness of `encodeWith` for `SignalMessage.tryFrom`

Defines `HonestWF` on `(EncodingVariation, WireFields)` and proves `tryFrom_encodeWith`:
`SignalMessage.tryFrom protoSignalCodec (encodeWith v f ++ mac)` succeeds and returns `f` whenever
`mac.length = macLength` and `HonestWF v f` holds.
-/

@[expose] public section

set_option autoImplicit false

namespace DY.Libsignal.Refinement

open DY DY.TrWire
open CryptoGames.LibsignalSession CryptoVerification.LibsignalProtoCodec

/-! ## Padded varints -/

private theorem toNat_and7F (x : BitVec 64) : (x &&& 0x7F).toNat = x.toNat % 128 := by
  rw [BitVec.toNat_and, show (0x7F : BitVec 64).toNat = 127 from rfl]
  exact Nat.and_two_pow_sub_one_eq_mod x.toNat 7

private theorem toNat_and7F_8 (x : BitVec 8) : (x &&& 0x7F).toNat = x.toNat % 128 := by
  rw [BitVec.toNat_and, show (0x7F : BitVec 8).toNat = 127 from rfl]
  exact Nat.and_two_pow_sub_one_eq_mod x.toNat 7

private theorem low_or_high (w : BitVec 64) :
    (w &&& (0x7F : BitVec 64)) ||| (w >>> 7) <<< 7 = w := by
  apply BitVec.eq_of_toNat_eq
  have hor := Nat.two_pow_add_eq_or_of_lt (i := 7) (b := w.toNat % 128) (by omega)
    (w.toNat / 128)
  have hlt := w.isLt
  simp only [Nat.reducePow] at hor hlt
  rw [BitVec.toNat_or, toNat_and7F, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  simp only [Nat.reducePow]
  rw [show w.toNat / 128 * 128 % 18446744073709551616 = 128 * (w.toNat / 128) by omega,
    Nat.or_comm, ← hor]
  omega

private theorem ofNat_group (n : ℕ) :
    BitVec.ofNat 64 (n % 128) ||| BitVec.ofNat 64 (n / 128) <<< 7 = BitVec.ofNat 64 n := by
  have h1 : BitVec.ofNat 64 (n % 128) = BitVec.ofNat 64 n &&& 0x7F := by
    apply BitVec.eq_of_toNat_eq
    rw [toNat_and7F, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  have h2 : BitVec.ofNat 64 (n / 128) <<< 7 = (BitVec.ofNat 64 n >>> 7) <<< 7 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftLeft_eq,
      Nat.shiftRight_eq_div_pow]
    simp only [Nat.reducePow]
    omega
  rw [h1, h2, low_or_high]

theorem paddedVarint_ne_nil (n pad : ℕ) : paddedVarint n pad ≠ [] := by
  rw [paddedVarint]; split <;> simp

theorem decodeVarintAux_paddedVarint : ∀ (s n pad : ℕ), n + pad < s →
    ∀ (i : ℕ) (acc : BitVec 64) (rest : HwBytes), i + (paddedVarint n pad).length ≤ 10 →
      n < 2 ^ (64 - 7 * i) →
      decodeVarintAux i acc (paddedVarint n pad ++ rest) =
        some (acc ||| BitVec.ofNat 64 n <<< (7 * i), rest)
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | s + 1, n, pad, hs => by
    intro i acc rest hlen hn
    by_cases hlt : n < 128 ∧ pad = 0
    · have hpv : paddedVarint n pad = [BitVec.ofNat 8 n] := by
        rw [paddedVarint]; simp [hlt]
      rw [hpv] at hlen ⊢
      have h8 : (BitVec.ofNat 8 n).toNat = n := by rw [BitVec.toNat_ofNat]; omega
      have hbyte : (BitVec.ofNat 8 n &&& 0x7F).setWidth 64 = BitVec.ofNat 64 n := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_setWidth, toNat_and7F_8, h8, BitVec.toNat_ofNat]
        omega
      have hov : ¬ (i = 9 ∧ 2 ≤ n) := by
        rintro ⟨rfl, h2⟩
        simp at hn
        omega
      simp only [List.cons_append, List.nil_append, decodeVarintAux, h8, hov, ↓reduceIte,
        show n ≤ 0x7F by omega, BitVec.zeroExtend_eq_setWidth, hbyte]
    · have hpv : paddedVarint n pad = BitVec.ofNat 8 (n % 128 + 128) ::
          paddedVarint (n / 128) (if n < 128 then pad - 1 else pad) := by
        rw [paddedVarint]; simp [hlt]
      rw [hpv] at hlen ⊢
      simp only [List.length_cons] at hlen
      have hi : i ≠ 9 := by
        have := List.length_pos_iff.mpr (paddedVarint_ne_nil (n / 128)
          (if n < 128 then pad - 1 else pad))
        omega
      have h8 : (BitVec.ofNat 8 (n % 128 + 128)).toNat = n % 128 + 128 := by
        rw [BitVec.toNat_ofNat]; omega
      have hbyte : (BitVec.ofNat 8 (n % 128 + 128) &&& 0x7F).setWidth 64 =
          BitVec.ofNat 64 (n % 128) := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_setWidth, toNat_and7F_8, h8, BitVec.toNat_ofNat]
        omega
      have hs' : n / 128 + (if n < 128 then pad - 1 else pad) < s := by
        split <;> omega
      have hn' : n / 128 < 2 ^ (64 - 7 * (i + 1)) := by
        apply Nat.div_lt_of_lt_mul
        have he : 64 - 7 * i = 7 + (64 - 7 * (i + 1)) := by omega
        rw [he, Nat.pow_add] at hn
        simpa [Nat.mul_comm] using hn
      simp only [List.cons_append, decodeVarintAux, h8, hi, ↓reduceIte,
        show ¬ n % 128 + 128 ≤ 0x7F by omega, BitVec.zeroExtend_eq_setWidth, hbyte]
      rw [decodeVarintAux_paddedVarint s _ _ hs' (i + 1) _ rest (by omega) hn']
      congr 2
      have h7 : 7 * (i + 1) = 7 + 7 * i := by omega
      rw [BitVec.or_assoc, h7, BitVec.shiftLeft_add, ← BitVec.shiftLeft_or_distrib,
        ofNat_group]

theorem decodeVarint_paddedVarint (n pad : ℕ) (rest : HwBytes) (hn : n < 2 ^ 64)
    (hlen : (paddedVarint n pad).length ≤ 10) :
    decodeVarint (paddedVarint n pad ++ rest) = some (BitVec.ofNat 64 n, rest) := by
  have h := decodeVarintAux_paddedVarint (n + pad + 1) n pad (by omega) 0 0 rest (by omega)
    (by simpa using hn)
  simpa [decodeVarint] using h

/-! ## Single-field encoding and well-formedness -/

def _root_.DY.TrWire.PbValue.wireType : PbValue → WireType
  | .varint _ => .varint
  | .bytes _ => .lengthDelimited
  | .unknown wt _ => (WireType.ofNat? wt).getD .endGroup

def _root_.DY.TrWire.PbValue.wireNat : PbValue → ℕ
  | .varint _ => 0
  | .bytes _ => 2
  | .unknown wt _ => wt

def _root_.DY.TrWire.PbValue.body (valuePad : ℕ) : PbValue → HwBytes
  | .varint n => paddedVarint n valuePad
  | .bytes b => paddedVarint b.length valuePad ++ b
  | .unknown _ p => p

def _root_.DY.TrWire.PbValue.head : PbValue → ℕ
  | .varint n => n
  | .bytes b => b.length
  | .unknown _ _ => 0

theorem encodeField_eq (tag kp vp : ℕ) (x : PbValue) :
    encodeField tag kp vp x = paddedVarint (tag * 8 + x.wireNat) kp ++ x.body vp := by
  cases x <;> simp [encodeField, PbValue.wireNat, PbValue.body]

/-- Field update performed by `mergeField` for field `tag` and value `x`. -/
def setField (m : ProtoSignalMessage) : ℕ → PbValue → ProtoSignalMessage
  | 1, .bytes b => { m with ratchetKey := some b }
  | 2, .varint n => { m with counter := some (BitVec.ofNat 32 n) }
  | 3, .varint n => { m with previousCounter := some (BitVec.ofNat 32 n) }
  | 4, .bytes b => { m with ciphertext := some b }
  | 5, .bytes b => { m with pqRatchet := some b }
  | 6, .bytes b => { m with addresses := some b }
  | _, _ => m

/-- Wire-type compatibility for field `tag`: matching `signal.proto` wire types on tags `1..6`,
and a valid wire type with a skipped payload on tags above `6`. -/
def WireTypeOk (tag : ℕ) : PbValue → Prop
  | .varint _ => tag = 2 ∨ tag = 3 ∨ 6 < tag
  | .bytes _ => tag = 1 ∨ tag = 4 ∨ tag = 5 ∨ tag = 6 ∨ 6 < tag
  | .unknown wt p => 6 < tag ∧ ∃ w, WireType.ofNat? wt = some w ∧
      skipField (2 * p.length + 2) recursionLimit tag w p = some []

theorem WireType.toNat_of_ofNat? {n : ℕ} {w : WireType} (h : WireType.ofNat? n = some w) :
    w.toNat = n := by
  unfold WireType.ofNat? at h; split at h <;> cases h <;> rfl

theorem _root_.DY.TrWire.PbValue.wireType_toNat {tag : ℕ} {x : PbValue} (h : WireTypeOk tag x) :
    x.wireType.toNat = x.wireNat := by
  cases x with
  | varint => rfl
  | bytes => rfl
  | unknown wt p =>
    obtain ⟨_, w, hw, _⟩ := h
    simp only [PbValue.wireType, PbValue.wireNat, hw, Option.getD_some]
    exact WireType.toNat_of_ofNat? hw

/-- Well-formedness of an encoded protobuf field: valid tag in `1..(2^29 - 1)`, key and head
varints of at most 10 bytes, `x.head < 2 ^ 64`, and `WireTypeOk tag x`. -/
structure FieldWF (tag keyPad valuePad : ℕ) (x : PbValue) : Prop where
  tag_pos : 1 ≤ tag
  tag_lt : tag < 2 ^ 29
  key_len : (paddedVarint (tag * 8 + x.wireType.toNat) keyPad).length ≤ 10
  head_lt : x.head < 2 ^ 64
  head_len : (paddedVarint x.head valuePad).length ≤ 10
  wireType : WireTypeOk tag x

theorem decodeKey_paddedVarint (t : ℕ) (wt : WireType) (kp : ℕ) (rest : HwBytes) (h1 : 1 ≤ t)
    (h2 : t < 2 ^ 29) (hl : (paddedVarint (t * 8 + wt.toNat) kp).length ≤ 10) :
    decodeKey (paddedVarint (t * 8 + wt.toNat) kp ++ rest) = some ((t, wt), rest) := by
  have hw : wt.toNat < 8 := by cases wt <;> decide
  have hn : (BitVec.ofNat 64 (t * 8 + wt.toNat)).toNat = t * 8 + wt.toNat := by
    rw [BitVec.toNat_ofNat]; omega
  have hmod : (t * 8 + wt.toNat) % 8 = wt.toNat := by omega
  have hdiv : (t * 8 + wt.toNat) / 8 = t := by omega
  have hof : WireType.ofNat? wt.toNat = some wt := by cases wt <;> rfl
  simp only [decodeKey, decodeVarint_paddedVarint _ _ rest (by omega) hl, hn, hmod, hdiv, hof]
  simp only [show ¬ 2 ^ 32 ≤ t * 8 + wt.toNat by omega, show ¬ t < 1 by omega, ↓reduceIte]

theorem mergeBytes_body (b rest : HwBytes) (vp : ℕ) (hb : b.length < 2 ^ 64)
    (hl : (paddedVarint b.length vp).length ≤ 10) :
    mergeBytes .lengthDelimited ((PbValue.bytes b).body vp ++ rest) = some (b, rest) := by
  have hv : (BitVec.ofNat 64 b.length).toNat = b.length := by rw [BitVec.toNat_ofNat]; omega
  simp [PbValue.body, mergeBytes, List.append_assoc, decodeVarint_paddedVarint _ _ _ hb hl, hv]

theorem mergeUint32_body (n vp : ℕ) (rest : HwBytes) (hn : n < 2 ^ 64)
    (hl : (paddedVarint n vp).length ≤ 10) :
    mergeUint32 .varint ((PbValue.varint n).body vp ++ rest) =
      some (BitVec.ofNat 32 n, rest) := by
  have hx : (BitVec.ofNat 64 n).setWidth 32 = BitVec.ofNat 32 n := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    simp only [Nat.reducePow]
    omega
  simp [PbValue.body, mergeUint32, decodeVarint_paddedVarint _ _ _ hn hl, hx]

/-! ## Decoder prefix consumption -/

theorem decodeVarintAux_inv : ∀ (bs : HwBytes) (i : ℕ) (acc r : BitVec 64) (rest : HwBytes), i ≤ 9 →
    decodeVarintAux i acc bs = some (r, rest) →
      ∃ n pad, bs = paddedVarint n pad ++ rest ∧ i + (paddedVarint n pad).length ≤ 10 ∧
        n < 2 ^ (64 - 7 * i)
  | [], _, _, _, _, _, h => by simp [decodeVarintAux] at h
  | b :: bs, i, acc, r, rest, hi, h => by
    have hb : b.toNat < 256 := b.isLt
    simp only [decodeVarintAux] at h
    by_cases hlo : b.toNat ≤ 0x7F
    · by_cases hov : i = 9 ∧ 2 ≤ b.toNat
      · simp [hlo, hov] at h
      · simp only [hlo, hov, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        have hpv : paddedVarint b.toNat 0 = [b] := by
          rw [paddedVarint]
          simp only [show b.toNat < 128 by omega, and_self, ↓reduceIte, List.cons.injEq,
            and_true]
          exact BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat]; omega)
        refine ⟨b.toNat, 0, by rw [hpv]; rfl, by rw [hpv]; simp; omega, ?_⟩
        rcases Nat.lt_or_ge i 9 with h9 | h9
        · have : 2 ^ 8 ≤ 2 ^ (64 - 7 * i) := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        · obtain rfl : i = 9 := by omega
          have : b.toNat < 2 := by
            by_contra hc
            exact hov ⟨rfl, by omega⟩
          simp only [Nat.reduceMul, Nat.reduceSub, pow_one]
          omega
    · by_cases h9 : i = 9
      · simp [hlo, h9] at h
      · simp only [hlo, h9, ↓reduceIte] at h
        obtain ⟨n', pad', hbs, hlen, hn'⟩ := decodeVarintAux_inv bs (i + 1) _ r rest (by omega) h
        have hpv : paddedVarint (b.toNat - 128 + 128 * n') (if n' = 0 then pad' + 1 else pad') =
            b :: paddedVarint n' pad' := by
          rw [paddedVarint]
          have hc : ¬ (b.toNat - 128 + 128 * n' < 128 ∧
              (if n' = 0 then pad' + 1 else pad') = 0) := by
            split <;> omega
          have h3 : (if b.toNat - 128 + 128 * n' < 128 then
              (if n' = 0 then pad' + 1 else pad') - 1 else (if n' = 0 then pad' + 1 else pad')) =
              pad' := by
            split_ifs <;> omega
          rw [ite_eq_right_iff.mpr (fun h => absurd h hc), h3, show (b.toNat - 128 + 128 * n') / 128 = n' by omega]
          congr 1
          exact BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat]; omega)
        refine ⟨_, _, by rw [hpv, hbs]; rfl, by rw [hpv]; simp only [List.length_cons]; omega, ?_⟩
        have hpow : 2 ^ (64 - 7 * i) = 128 * 2 ^ (64 - 7 * (i + 1)) := by
          rw [show 64 - 7 * i = 7 + (64 - 7 * (i + 1)) by omega, Nat.pow_add]
        rw [hpow]
        generalize 2 ^ (64 - 7 * (i + 1)) = X at hn'
        omega

theorem decodeVarint_inv {bs rest : HwBytes} {r : BitVec 64} (h : decodeVarint bs = some (r, rest)) :
    ∃ pad, bs = paddedVarint r.toNat pad ++ rest ∧ (paddedVarint r.toNat pad).length ≤ 10 := by
  obtain ⟨n, pad, hbs, hlen, hn⟩ := decodeVarintAux_inv bs 0 0 r rest (by omega) h
  simp only [Nat.mul_zero, Nat.sub_zero, Nat.zero_add] at hlen hn
  have hd := decodeVarint_paddedVarint n pad rest hn hlen
  rw [← hbs, h] at hd
  have hr : r = BitVec.ofNat 64 n := by simpa using hd
  have hrn : r.toNat = n := by rw [hr, BitVec.toNat_ofNat]; omega
  exact ⟨pad, hrn ▸ hbs, hrn ▸ hlen⟩

theorem decodeVarint_prefix {bs rest : HwBytes} {r : BitVec 64} (h : decodeVarint bs = some (r, rest)) :
    ∃ c, bs = c ++ rest ∧ c ≠ [] ∧ ∀ r', decodeVarint (c ++ r') = some (r, r') := by
  obtain ⟨pad, hbs, hlen⟩ := decodeVarint_inv h
  refine ⟨_, hbs, paddedVarint_ne_nil _ _, fun r' => ?_⟩
  rw [decodeVarint_paddedVarint _ _ _ r.isLt hlen, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem decodeKey_inv {bs rest : HwBytes} {t : ℕ} {wt : WireType}
    (h : decodeKey bs = some ((t, wt), rest)) :
    ∃ kp, bs = paddedVarint (t * 8 + wt.toNat) kp ++ rest ∧
      (paddedVarint (t * 8 + wt.toNat) kp).length ≤ 10 ∧ 1 ≤ t ∧ t < 2 ^ 29 := by
  unfold decodeKey at h
  split at h
  · cases h
  · next key rest0 hdec =>
    split at h
    · cases h
    · next hk =>
      split at h
      · cases h
      · next w hw =>
        dsimp only at h
        split at h
        · cases h
        · next ht =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
          obtain ⟨pad, hbs, hlen⟩ := decodeVarint_inv hdec
          have hwn := WireType.toNat_of_ofNat? hw
          have hkey : key.toNat / 8 * 8 + w.toNat = key.toNat := by omega
          exact ⟨pad, by rw [hkey]; exact hbs, by rw [hkey]; exact hlen, by omega, by omega⟩

theorem decodeKey_prefix {bs rest : HwBytes} {t : ℕ} {wt : WireType}
    (h : decodeKey bs = some ((t, wt), rest)) :
    ∃ c, bs = c ++ rest ∧ c ≠ [] ∧ ∀ r', decodeKey (c ++ r') = some ((t, wt), r') := by
  obtain ⟨kp, hbs, hlen, h1, h2⟩ := decodeKey_inv h
  exact ⟨_, hbs, paddedVarint_ne_nil _ _, fun r' => decodeKey_paddedVarint t wt kp r' h1 h2 hlen⟩

theorem skipBytes_prefix {n : ℕ} {bs r : HwBytes} (h : skipBytes n bs = some r) :
    ∃ c, bs = c ++ r ∧ ∀ r', skipBytes n (c ++ r') = some r' := by
  unfold skipBytes at h
  split at h
  · cases h
  · next hl =>
    cases h
    have hc : (bs.take n).length = n := by simp only [List.length_take]; omega
    refine ⟨bs.take n, (List.take_append_drop n bs).symm, fun r' => ?_⟩
    simp only [skipBytes, List.length_append, hc, show ¬ n + r'.length < n by omega, ↓reduceIte,
      List.drop_left' hc]

theorem skipScalar_prefix {wt : WireType} {bs r : HwBytes} (h : skipScalar wt bs = some r) :
    ∃ c, bs = c ++ r ∧ ∀ r', skipScalar wt (c ++ r') = some r' := by
  cases wt with
  | varint =>
    simp only [skipScalar, Option.map_eq_some_iff] at h
    obtain ⟨⟨v, r0⟩, hd, rfl⟩ := h
    obtain ⟨c, hbs, -, hc⟩ := decodeVarint_prefix hd
    exact ⟨c, hbs, fun r' => by simp [skipScalar, hc]⟩
  | sixtyFourBit =>
    obtain ⟨c, hbs, hc⟩ := skipBytes_prefix h
    exact ⟨c, hbs, fun r' => hc r'⟩
  | thirtyTwoBit =>
    obtain ⟨c, hbs, hc⟩ := skipBytes_prefix h
    exact ⟨c, hbs, fun r' => hc r'⟩
  | lengthDelimited =>
    simp only [skipScalar] at h
    split at h
    · cases h
    · next len rest hd =>
      obtain ⟨c1, hbs, -, hc1⟩ := decodeVarint_prefix hd
      obtain ⟨c2, hrest, hc2⟩ := skipBytes_prefix h
      refine ⟨c1 ++ c2, by rw [hbs, hrest, List.append_assoc], fun r' => ?_⟩
      simp only [skipScalar, List.append_assoc, hc1, hc2]
  | startGroup => simp [skipScalar] at h
  | endGroup => simp [skipScalar] at h

theorem skip_prefix : ∀ fuel : ℕ,
    (∀ d t wt bs r, skipField fuel d t wt bs = some r →
      ∃ c, bs = c ++ r ∧ ∀ f', c.length + 1 ≤ f' → ∀ r', skipField f' d t wt (c ++ r') = some r') ∧
    (∀ d t bs r, skipGroup fuel d t bs = some r →
      ∃ c, bs = c ++ r ∧ c ≠ [] ∧ ∀ f', c.length ≤ f' → ∀ r', skipGroup f' d t (c ++ r') = some r')
  | 0 => ⟨fun _ _ _ _ _ h => by simp [skipField] at h, fun _ _ _ _ h => by simp [skipGroup] at h⟩
  | fuel + 1 => by
    obtain ⟨ihF, ihG⟩ := skip_prefix fuel
    constructor
    · intro d t wt bs r h
      simp only [skipField] at h
      split at h
      · cases h
      · next hd =>
        cases wt with
        | endGroup => cases h
        | startGroup =>
          obtain ⟨c, hbs, hne, hc⟩ := ihG d t bs r h
          refine ⟨c, hbs, fun f' hf' r' => ?_⟩
          obtain ⟨g, rfl⟩ : ∃ g, f' = g + 1 := ⟨f' - 1, by omega⟩
          simp only [skipField, hd, ↓reduceIte]
          exact hc g (by omega) r'
        | _ =>
          obtain ⟨c, hbs, hc⟩ := skipScalar_prefix h
          refine ⟨c, hbs, fun f' hf' r' => ?_⟩
          obtain ⟨g, rfl⟩ : ∃ g, f' = g + 1 := ⟨f' - 1, by omega⟩
          simp only [skipField, hd, ↓reduceIte]
          exact hc r'
    · intro d t bs r h
      simp only [skipGroup] at h
      split at h
      · cases h
      · next itag rest hkey =>
        obtain ⟨kc, hbs, hkne, hk⟩ := decodeKey_prefix hkey
        have hkl : 1 ≤ kc.length := List.length_pos_iff.mpr hkne
        split at h
        · next ht =>
          cases h
          refine ⟨kc, hbs, hkne, fun f' hf' r' => ?_⟩
          obtain ⟨g, rfl⟩ : ∃ g, f' = g + 1 := ⟨f' - 1, by omega⟩
          simp only [skipGroup, hk, ht, ↓reduceIte]
        · cases h
      · next itag iwt rest hne hkey =>
        obtain ⟨kc, hbs, hkne, hk⟩ := decodeKey_prefix hkey
        have hkl : 1 ≤ kc.length := List.length_pos_iff.mpr hkne
        split at h
        · cases h
        · next rest' hf =>
          obtain ⟨c1, hrest, hc1⟩ := ihF _ _ _ _ _ hf
          obtain ⟨c2, hrest', hne2, hc2⟩ := ihG _ _ _ _ h
          have hl2 : 1 ≤ c2.length := List.length_pos_iff.mpr hne2
          refine ⟨kc ++ c1 ++ c2, by rw [hbs, hrest, hrest']; simp, by simp [hkne], ?_⟩
          intro f' hf' r'
          simp only [List.length_append] at hf'
          obtain ⟨g, rfl⟩ : ∃ g, f' = g + 1 := ⟨f' - 1, by omega⟩
          have e : kc ++ c1 ++ c2 ++ r' = kc ++ (c1 ++ (c2 ++ r')) := by simp
          rw [e]
          cases iwt with
          | endGroup => exact absurd rfl hne
          | _ =>
            simp only [skipGroup, hk, hc1 g (by omega) (c2 ++ r'), hc2 g (by omega) r']

theorem skipField_exact {t : ℕ} {w : WireType} {p : HwBytes} (rest : HwBytes) {f : ℕ}
    (hf : p.length + 1 ≤ f) (h : skipField (2 * p.length + 2) recursionLimit t w p = some []) :
    skipField f recursionLimit t w (p ++ rest) = some rest := by
  obtain ⟨c, hp, hc⟩ := (skip_prefix _).1 _ _ _ _ _ h
  rw [List.append_nil] at hp
  subst hp
  exact hc f hf rest

theorem skipField_body (t vp : ℕ) (x : PbValue) (rest : HwBytes) (fuel : ℕ)
    (hx : x.head < 2 ^ 64) (hl : (paddedVarint x.head vp).length ≤ 10)
    (hwt : ∀ wt p, x ≠ .unknown wt p) :
    skipField (fuel + 1) recursionLimit t x.wireType (x.body vp ++ rest) = some rest := by
  cases x with
  | varint n =>
    simp only [PbValue.head] at hx hl
    simp [skipField, recursionLimit, PbValue.wireType, skipScalar, PbValue.body,
      decodeVarint_paddedVarint _ _ _ hx hl]
  | bytes b =>
    simp only [PbValue.head] at hx hl
    have hv : (BitVec.ofNat 64 b.length).toNat = b.length := by rw [BitVec.toNat_ofNat]; omega
    simp [skipField, recursionLimit, PbValue.wireType, skipScalar, PbValue.body, List.append_assoc,
      decodeVarint_paddedVarint _ _ _ hx hl, hv, skipBytes]
  | unknown wt p => exact absurd rfl (hwt wt p)

theorem mergeField_body (m : ProtoSignalMessage) (tag vp : ℕ) (x : PbValue) (rest : HwBytes)
    (hpos : 1 ≤ tag) (hx : x.head < 2 ^ 64) (hl : (paddedVarint x.head vp).length ≤ 10)
    (hwt : WireTypeOk tag x) :
    mergeField m tag x.wireType (x.body vp ++ rest) = some (setField m tag x, rest) := by
  rcases tag with _ | _ | _ | _ | _ | _ | _ | t
  · omega
  all_goals cases x
  all_goals simp only [WireTypeOk] at hwt
  all_goals first
    | omega
    | (simp only [PbValue.head] at hx hl
       first
        | (simp [mergeField, setField, PbValue.wireType, mergeBytes_body _ _ _ hx hl]; done)
        | (simp [mergeField, setField, PbValue.wireType, mergeUint32_body _ _ _ hx hl]; done)
        | (simp [mergeField, setField, PbValue.wireType]
           first
            | exact skipField_body _ vp (.varint _) rest _ hx hl (by simp)
            | exact skipField_body _ vp (.bytes _) rest _ hx hl (by simp)))
    | (obtain ⟨-, w, hw, hskip⟩ := hwt
       simp only [mergeField, setField, PbValue.wireType, PbValue.body, hw, Option.getD_some]
       rw [skipField_exact rest (by simp only [List.length_append]; omega) hskip]
       rfl)

theorem loopsTo_encodeField (m r : ProtoSignalMessage) (tag kp vp : ℕ) (x : PbValue) (rest : HwBytes)
    (hwf : FieldWF tag kp vp x) (h : LoopsTo (setField m tag x) rest r) :
    LoopsTo m (encodeField tag kp vp x ++ rest) r := by
  intro n hn
  rw [encodeField_eq, ← PbValue.wireType_toNat hwf.wireType, List.append_assoc] at hn ⊢
  have hkey := decodeKey_paddedVarint tag x.wireType kp (x.body vp ++ rest) hwf.tag_pos hwf.tag_lt
    hwf.key_len
  have hmerge := mergeField_body m tag vp x rest hwf.tag_pos hwf.head_lt hwf.head_len hwf.wireType
  have hpos : 0 < (paddedVarint (tag * 8 + x.wireType.toNat) kp).length :=
    List.length_pos_iff.mpr (paddedVarint_ne_nil _ _)
  simp only [List.length_append] at hn
  obtain ⟨b, bs, hk⟩ := List.exists_cons_of_ne_nil
    (List.length_pos_iff.mp (by simp only [List.length_append]; omega) :
      paddedVarint (tag * 8 + x.wireType.toNat) kp ++ (x.body vp ++ rest) ≠ [])
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  rw [hk] at hkey ⊢
  simp only [decodeLoop, hkey, hmerge]
  exact h n' (by omega)

/-! ## Variation item lists -/

def _root_.DY.TrWire.FieldItem.tag : FieldItem → ℕ
  | .known t .. => t
  | .extra t .. => t

/-- Well-formedness of a `FieldItem`: `.known` items resolve via `knownValue? v f` (tags `1..4`),
and every item satisfies `FieldWF`. -/
def ItemWF (v : EncodingVariation) (f : WireFields) : FieldItem → Prop
  | .known t kp vp => ∃ x, knownValue? v f t = some x ∧ FieldWF t kp vp x
  | .extra t x kp vp => FieldWF t kp vp x

def stepItem (v : EncodingVariation) (f : WireFields) (m : ProtoSignalMessage) :
    FieldItem → ProtoSignalMessage
  | .known t _ _ => ((knownValue? v f t).map (setField m t)).getD m
  | .extra t x _ _ => setField m t x

theorem loopsTo_items (v : EncodingVariation) (f : WireFields) :
    ∀ (items : List FieldItem) (m : ProtoSignalMessage), (∀ it ∈ items, ItemWF v f it) →
      LoopsTo m (items.flatMap (FieldItem.encode v f)) (items.foldl (stepItem v f) m)
  | [], m, _ => loopsTo_nil m
  | it :: items, m, hwf => by
    have ih := loopsTo_items v f items
    simp only [List.flatMap_cons, List.foldl_cons]
    have hit := hwf it (by simp)
    cases it with
    | known t kp vp =>
      obtain ⟨x, hx, hf⟩ := hit
      have he : FieldItem.encode v f (.known t kp vp) = encodeField t kp vp x := by
        simp [FieldItem.encode, hx]
      have hs : stepItem v f m (.known t kp vp) = setField m t x := by simp [stepItem, hx]
      rw [he, hs]
      exact loopsTo_encodeField _ _ _ _ _ _ _ hf (ih _ fun it h => hwf it (by simp [h]))
    | extra t x kp vp =>
      exact loopsTo_encodeField _ _ _ _ _ _ _ hit (ih _ fun it h => hwf it (by simp [h]))

/-! ## Last occurrence of a tag -/

/-- Last item in `items` with tag `t`. -/
def lastWithTag (t : ℕ) (items : List FieldItem) : Option FieldItem :=
  (items.filter (·.tag == t)).getLast?

theorem proj_foldl_stepItem {β : Type} (v : EncodingVariation) (f : WireFields)
    (proj : ProtoSignalMessage → β) (t : ℕ)
    (hkeep : ∀ m it, it.tag ≠ t → proj (stepItem v f m it) = proj m) :
    ∀ (items : List FieldItem) (m : ProtoSignalMessage),
      (∀ it ∈ items, it.tag = t → ∀ m, proj (stepItem v f m it) = proj (stepItem v f emptyProtoSignalMessage it)) →
      proj (items.foldl (stepItem v f) m) =
        ((lastWithTag t items).map fun it => proj (stepItem v f emptyProtoSignalMessage it)).getD (proj m)
  | [], _, _ => rfl
  | it :: items, m, hset => by
    have ih := proj_foldl_stepItem v f proj t hkeep items (stepItem v f m it)
      fun it' h => hset it' (by simp [h])
    simp only [List.foldl_cons, ih, lastWithTag, List.filter_cons]
    by_cases ht : it.tag = t
    · simp only [ht, beq_self_eq_true, ↓reduceIte, List.getLast?_cons]
      cases (items.filter (·.tag == t)).getLast? <;>
        simp [hset it (by simp) ht m]
    · simp only [show (it.tag == t) = false by simpa using ht]
      simp [hkeep m it ht]

theorem stepItem_keep {β : Type} (v : EncodingVariation) (f : WireFields)
    (proj : ProtoSignalMessage → β) (t : ℕ)
    (hs : ∀ m u x, u ≠ t → proj (setField m u x) = proj m) :
    ∀ m it, it.tag ≠ t → proj (stepItem v f m it) = proj m := by
  intro m it ht
  cases it with
  | known u kp vp =>
    simp only [stepItem]
    cases knownValue? v f u <;> simp [hs m u _ ht]
  | extra u x kp vp => exact hs m u x ht

theorem stepItem_set {β : Type} (v : EncodingVariation) (f : WireFields)
    (proj : ProtoSignalMessage → β) (t : ℕ)
    (hs : ∀ m x, WireTypeOk t x → proj (setField m t x) = proj (setField emptyProtoSignalMessage t x))
    (it : FieldItem) (hwf : ItemWF v f it) (ht : it.tag = t) (m : ProtoSignalMessage) :
    proj (stepItem v f m it) = proj (stepItem v f emptyProtoSignalMessage it) := by
  cases it with
  | known u kp vp =>
    obtain ⟨x, hx, hf⟩ := hwf
    simp only [FieldItem.tag] at ht; subst ht
    simp only [stepItem, hx, Option.map_some, Option.getD_some]
    exact hs m x hf.wireType
  | extra u x kp vp =>
    simp only [FieldItem.tag] at ht; subst ht
    exact hs m x hwf.wireType

private theorem proj_decoded {β : Type} (v : EncodingVariation) (f : WireFields)
    (proj : ProtoSignalMessage → β) (t : ℕ) (hwf : ∀ it ∈ v.fields, ItemWF v f it)
    (hkeep : ∀ m u x, u ≠ t → proj (setField m u x) = proj m)
    (hset : ∀ m x, WireTypeOk t x → proj (setField m t x) = proj (setField emptyProtoSignalMessage t x)) :
    proj (v.fields.foldl (stepItem v f) emptyProtoSignalMessage) =
      ((lastWithTag t v.fields).map fun it => proj (stepItem v f emptyProtoSignalMessage it)).getD
        (proj emptyProtoSignalMessage) :=
  proj_foldl_stepItem v f proj t (stepItem_keep v f proj t hkeep) v.fields emptyProtoSignalMessage
    fun it hit ht m => stepItem_set v f proj t hset it (hwf it hit) ht m

/-! ## `tryFrom` round-trip -/

/-- Well-formedness of variation `v` for fields `f` guaranteeing that `SignalMessage.tryFrom`
decodes `encodeWith v f ++ mac` back to `f`. -/
structure HonestWF (v : EncodingVariation) (f : WireFields) : Prop where
  version : 3 ≤ f.version ∧ f.version ≤ 4
  ratchetKey : f.ratchetKey.length = 32
  counter : f.counter < 2 ^ 32
  previousCounter : f.previousCounter < 2 ^ 32
  items : ∀ it ∈ v.fields, ItemWF v f it
  lastRatchetKey : ∃ kp vp, lastWithTag 1 v.fields = some (.known 1 kp vp)
  lastCounter : ∃ kp vp, lastWithTag 2 v.fields = some (.known 2 kp vp)
  lastPreviousCounter : (∃ kp vp, lastWithTag 3 v.fields = some (.known 3 kp vp)) ∨
    (lastWithTag 3 v.fields = none ∧ f.previousCounter = 0)
  lastCiphertext : ∃ kp vp, lastWithTag 4 v.fields = some (.known 4 kp vp)

theorem ofNat32_add_high (a h : ℕ) : BitVec.ofNat 32 (a + 2 ^ 32 * h) = BitVec.ofNat 32 a := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, Nat.reducePow]
  omega

theorem deserialize_ratchetKey (rk tr : HwBytes) (h : rk.length = 32) :
    ∃ k, PublicKey.deserialize (0x05#8 :: rk ++ tr) = .ok k ∧ k.bytes.toList = rk := by
  have h32 : 32 ≤ (rk ++ tr).length := by simp [h]
  refine ⟨⟨⟨(rk ++ tr).take 32, by rw [List.length_take]; omega⟩⟩, ?_, ?_⟩
  · simp only [List.cons_append, PublicKey.deserialize, djbType, h32, ↓reduceDIte]
    split
    · next hne => exact absurd rfl hne
    · rfl
  · show (rk ++ tr).take 32 = rk
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]

/-- `SignalMessage.tryFrom protoSignalCodec` on `encodeWith v f ++ mac` with `mac.length = macLength`
and `HonestWF v f` succeeds and returns the fields `f`. -/
theorem tryFrom_encodeWith (v : EncodingVariation) (f : WireFields) (mac : HwBytes)
    (hmac : mac.length = macLength) (h : HonestWF v f) :
    ∃ m, SignalMessage.tryFrom protoSignalCodec (encodeWith v f ++ mac) = .ok m ∧
      m.messageVersion.toNat = f.version ∧ m.senderRatchetKey.bytes.toList = f.ratchetKey ∧
      m.counter.toNat = f.counter ∧ m.previousCounter.toNat = f.previousCounter ∧
      m.ciphertext = f.ciphertext := by
  have hdec : protoSignalCodec.decode (v.fields.flatMap (FieldItem.encode v f)) =
      some (v.fields.foldl (stepItem v f) emptyProtoSignalMessage) :=
    loopsTo_items v f v.fields emptyProtoSignalMessage h.items _ le_rfl
  have hrk : (v.fields.foldl (stepItem v f) emptyProtoSignalMessage).ratchetKey =
      some (0x05#8 :: f.ratchetKey ++ v.ratchetKeyTrailingBytes) := by
    obtain ⟨kp, vp, hl⟩ := h.lastRatchetKey
    rw [proj_decoded v f (·.ratchetKey) 1 h.items
      (by intro m u x hu; rcases u with _|_|_|_|_|_|_|u <;> cases x <;> first | omega | rfl)
      (by intro m x hx; cases x <;> simp only [WireTypeOk] at hx <;> first | omega | rfl), hl]
    rfl
  have hctr : (v.fields.foldl (stepItem v f) emptyProtoSignalMessage).counter =
      some (BitVec.ofNat 32 f.counter) := by
    obtain ⟨kp, vp, hl⟩ := h.lastCounter
    rw [proj_decoded v f (·.counter) 2 h.items
      (by intro m u x hu; rcases u with _|_|_|_|_|_|_|u <;> cases x <;> first | omega | rfl)
      (by intro m x hx; cases x <;> simp only [WireTypeOk] at hx <;> first | omega | rfl), hl]
    show some (BitVec.ofNat 32 (f.counter + 2 ^ 32 * v.counterHigh)) = _
    rw [ofNat32_add_high]
  have hpc : ((v.fields.foldl (stepItem v f) emptyProtoSignalMessage).previousCounter.getD 0).toNat =
      f.previousCounter := by
    rw [proj_decoded v f (·.previousCounter) 3 h.items
      (by intro m u x hu; rcases u with _|_|_|_|_|_|_|u <;> cases x <;> first | omega | rfl)
      (by intro m x hx; cases x <;> simp only [WireTypeOk] at hx <;> first | omega | rfl)]
    rcases h.lastPreviousCounter with ⟨kp, vp, hl⟩ | ⟨hl, h0⟩
    · rw [hl]
      show (BitVec.ofNat 32 (f.previousCounter + 2 ^ 32 * v.previousCounterHigh)).toNat =
        f.previousCounter
      rw [ofNat32_add_high, BitVec.toNat_ofNat]; have := h.previousCounter; omega
    · rw [hl, h0]; rfl
  have hct : (v.fields.foldl (stepItem v f) emptyProtoSignalMessage).ciphertext = some f.ciphertext := by
    obtain ⟨kp, vp, hl⟩ := h.lastCiphertext
    rw [proj_decoded v f (·.ciphertext) 4 h.items
      (by intro m u x hu; rcases u with _|_|_|_|_|_|_|u <;> cases x <;> first | omega | rfl)
      (by intro m x hx; cases x <;> simp only [WireTypeOk] at hx <;> first | omega | rfl), hl]
    rfl
  obtain ⟨k, hk, hkb⟩ := deserialize_ratchetKey f.ratchetKey v.ratchetKeyTrailingBytes
    h.ratchetKey
  have hbyte : (BitVec.ofNat 8 (f.version * 16 + v.versionLowNibble % 16)).toNat =
      f.version * 16 + v.versionLowNibble % 16 := by
    rw [BitVec.toNat_ofNat]; have := h.version; omega
  have hv : BitVec.ofNat 8 (f.version * 16 + v.versionLowNibble % 16) >>> 4 =
      BitVec.ofNat 8 f.version := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, hbyte, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
    have := h.version; omega
  have hsplit : ((encodeWith v f ++ mac).take ((encodeWith v f ++ mac).length - macLength)).drop 1 =
      v.fields.flatMap (FieldItem.encode v f) := by
    simp only [encodeWith]
    generalize v.fields.flatMap (FieldItem.encode v f) = body
    rw [List.cons_append, List.length_cons, List.length_append, hmac,
      show body.length + macLength + 1 - macLength = body.length + 1 by omega, List.take_succ_cons,
      List.drop_one, List.tail_cons, List.take_left' rfl]
  have hlen : ¬ (encodeWith v f ++ mac).length < macLength + 1 := by
    simp [encodeWith, hmac]
  have hhead : (encodeWith v f ++ mac).headD 0 =
      BitVec.ofNat 8 (f.version * 16 + v.versionLowNibble % 16) := rfl
  have hver : f.version = 3 ∨ f.version = 4 := by have := h.version; omega
  have htry : SignalMessage.tryFrom protoSignalCodec (encodeWith v f ++ mac) = .ok
      { messageVersion := BitVec.ofNat 8 f.version, senderRatchetKey := k,
        counter := BitVec.ofNat 32 f.counter,
        previousCounter := (v.fields.foldl (stepItem v f) emptyProtoSignalMessage).previousCounter.getD 0,
        ciphertext := f.ciphertext,
        pqRatchet := (v.fields.foldl (stepItem v f) emptyProtoSignalMessage).pqRatchet.getD [],
        addresses := (v.fields.foldl (stepItem v f) emptyProtoSignalMessage).addresses,
        serialized := encodeWith v f ++ mac } := by
    simp only [SignalMessage.tryFrom, hlen, hhead, hv, hsplit, hdec, hrk, hctr, hct, hk]
    rcases hver with h3 | h4 <;> simp [*, preKyberVersion, currentVersion]
  refine ⟨_, htry, ?_, hkb, ?_, hpc, rfl⟩
  · show (BitVec.ofNat 8 f.version).toNat = f.version
    rw [BitVec.toNat_ofNat]; have := h.version; omega
  · show (BitVec.ofNat 32 f.counter).toNat = f.counter
    rw [BitVec.toNat_ofNat]; have := h.counter; omega

end DY.Libsignal.Refinement

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import VerifiedLibraries.RustStd.Proofs.Wave1.CoreMemrchrLemmas
public import VerifiedLibraries.RustStd.Spec.CoreFromUtf8
public import VerifiedLibraries.RustStd.Proofs.Wave2.FromUtf8Model

/-!
# Arithmetic, Table, SWAR, and `sret` Lemmas for `from_utf8`

Separation-logic byte/word focusing, 16-byte SWAR ASCII equivalences, `UTF8_CHAR_WIDTH`
(`corePlacedData1`) table classification, ARM64 32-bit byte condition-code characterizations, and
`runUtf8ValidationLoop` unfolding lemmas on `bs.drop idx`.
-/

@[expose] public section

set_option autoImplicit false

namespace VerifiedLibraries.RustStd

open Arm64 ProofLib

/-! ## Separation-Logic Helpers -/

theorem pointsToBytesRO_focus8 (base : BitVec 64) (bs : List (BitVec 8)) (off : Nat)
    (h : off < bs.length) :
    (base ↦ᵣ bs) =
      ((base + BitVec.ofNat 64 off) ↦₈ᵣ bs.getD off 0#8) ∗
      ((base ↦ᵣ bs.take off) ∗
       ((base + BitVec.ofNat 64 (off + 1)) ↦ᵣ bs.drop (off + 1))) := by
  rw [pointsToBytesRO_split3 base bs off 1 (by omega),
      pointsToBytesRO_take1_eq_pointsTo8RO (base + BitVec.ofNat 64 off) bs off (by omega)]

theorem memRegion18_eq (ret : BitVec 64) :
    memRegion ret 18 =
      (∃∗ s0 : BitVec 64, ret ↦₆₄ s0) ∗
      (∃∗ s8 : BitVec 64, (ret + 8#64) ↦₆₄ s8) ∗
      (∃∗ s16 : BitVec 8, (ret + 16#64) ↦₈ s16) ∗
      (∃∗ s17 : BitVec 8, (ret + 17#64) ↦₈ s17) := by
  have h18 : memRegion ret 18 = memRegion ret 8 ∗ memRegion (ret + 8#64) 10 :=
    memRegion_split' (n := 8) (k := 10) rfl rfl (by decide)
  have h10 : memRegion (ret + 8#64) 10 = memRegion (ret + 8#64) 8 ∗ memRegion (ret + 16#64) 2 :=
    memRegion_split' (n := 8) (k := 2) rfl (by bv_lin) (by decide)
  have h2 : memRegion (ret + 16#64) 2 = memRegion (ret + 16#64) 1 ∗ memRegion (ret + 17#64) 1 :=
    memRegion_split' (n := 1) (k := 1) rfl (by bv_lin) (by decide)
  rw [h18, h10, h2, memRegion_eight, memRegion_eight, memRegion_one, memRegion_one]

/-- Combine bytes `16..24` (`1 + 1 + 2 + 4 = 8` bytes) of `sret` into a single 64-bit cell at
    `ret + 16#64` for `stp x0, x1, [x8, #8]`. -/
theorem sret_tail8_merge (ret : BitVec 64) (s16 s17 : BitVec 8)
    (b18 : BitVec 16) (b20 : BitVec 32) :
    (((ret + 16#64) ↦₈ s16) ∗
     ((ret + 17#64) ↦₈ s17) ∗
     ((ret + 18#64) ↦₁₆ b18) ∗
     ((ret + 20#64) ↦₃₂ b20)) =
      ((ret + 16#64) ↦₆₄ (b20 ++ (b18 ++ (s17 ++ s16)))) := by
  have ha1 : ret + 17#64 = (ret + 16#64) + 1#64 := by bv_lin
  have ha2 : ret + 18#64 = (ret + 16#64) + 2#64 := by bv_lin
  have ha4 : ret + 20#64 = (ret + 16#64) + 4#64 := by bv_lin
  rw [ha1, ha2, ha4,
      ← sepConj_assoc, pointsTo8_pair (ret + 16#64) s16 s17,
      ← sepConj_assoc, pointsTo16_pair (ret + 16#64) (s17 ++ s16) b18,
      pointsTo32_pair (ret + 16#64) (b18 ++ (s17 ++ s16)) b20]

theorem memRegion24_eq_fromUtf8Pre (ret : BitVec 64) :
    memRegion ret 24 =
      memRegion ret 18 ∗
      (∃∗ b18 : BitVec 16, (ret + 18#64) ↦₁₆ b18) ∗
      (∃∗ b20 : BitVec 32, (ret + 20#64) ↦₃₂ b20) := by
  have h24 : memRegion ret 24 = memRegion ret 18 ∗ memRegion (ret + 18#64) 6 :=
    memRegion_split' (n := 18) (k := 6) rfl rfl (by decide)
  have h6 : memRegion (ret + 18#64) 6 = memRegion (ret + 18#64) 2 ∗ memRegion (ret + 20#64) 4 :=
    memRegion_split' (n := 2) (k := 4) rfl (by bv_lin) (by decide)
  rw [h24, h6, memRegion_two, memRegion_four]

theorem pointsToBytes_focus16_at (p : BitVec 64) (bs : List (BitVec 8)) {idx : Nat}
    (h16 : idx + 16 ≤ bs.length) :
    ∃ w0 w1 : BitVec 64,
      (bs.drop idx).take 16 = unpack64 w0 ++ unpack64 w1 ∧
      (p ↦ₛ bs) =
        ((p + BitVec.ofNat 64 idx) ↦₆₄ w0) ∗
        (((p + BitVec.ofNat 64 idx) + 8#64) ↦₆₄ w1) ∗
        ((p ↦ₛ bs.take idx) ∗
         ((p + BitVec.ofNat 64 (idx + 16)) ↦ₛ bs.drop (idx + 16))) := by
  have h := pointsToBytes_focus16_words p bs (cur := idx + 16) (by omega) h16
  have hsub : idx + 16 - 16 = idx := by omega
  simpa only [hsub] using h

/-! ## SWAR 16-Byte ASCII Lemmas -/

private theorem byte_lt_0x80_iff_and_eq_zero (b : BitVec 8) :
    (b < 0x80#8) ↔ (b &&& 0x80#8 = 0#8) := by
  revert b; decide

theorem utf8SwarAscii_word_eq_zero_iff (w : BitVec 64) :
    (w &&& 0x8080808080808080#64 = 0#64) ↔ (∀ b ∈ unpack64 w, b < 0x80#8) := by
  simp only [unpack64, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    byte_lt_0x80_iff_and_eq_zero]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_robdd
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
    bv_robdd

theorem utf8SwarAscii_pair_iff (w0 w1 : BitVec 64) :
    ((w1 ||| w0) &&& 0x8080808080808080#64 = 0#64) ↔
      ((∀ b ∈ unpack64 w0, b < 0x80#8) ∧ (∀ b ∈ unpack64 w1, b < 0x80#8)) := by
  have hor : ((w1 ||| w0) &&& 0x8080808080808080#64 = 0#64) ↔
      (w0 &&& 0x8080808080808080#64 = 0#64 ∧ w1 &&& 0x8080808080808080#64 = 0#64) := by
    constructor
    · intro h; exact ⟨by bv_robdd, by bv_robdd⟩
    · rintro ⟨h0, h1⟩; bv_robdd
  rw [hor, utf8SwarAscii_word_eq_zero_iff, utf8SwarAscii_word_eq_zero_iff]

theorem runUtf8ValidationLoop_swar16 {bs : List (BitVec 8)} {idx : Nat} {w0 w1 : BitVec 64}
    (h16 : idx + 16 ≤ bs.length)
    (hchunk : (bs.drop idx).take 16 = unpack64 w0 ++ unpack64 w1)
    (hswar : (w1 ||| w0) &&& 0x8080808080808080#64 = 0#64) :
    runUtf8ValidationLoop idx (bs.drop idx) =
      runUtf8ValidationLoop (idx + 16) (bs.drop (idx + 16)) := by
  obtain ⟨hw0, hw1⟩ := (utf8SwarAscii_pair_iff w0 w1).mp hswar
  have hall : ∀ b ∈ (bs.drop idx).take 16, b < 0x80#8 := by
    rw [hchunk]
    intro b hb
    rcases List.mem_append.mp hb with hb0 | hb1
    · exact hw0 b hb0
    · exact hw1 b hb1
  have hsplit : bs.drop idx = (bs.drop idx).take 16 ++ bs.drop (idx + 16) := by
    conv => lhs; rw [← List.take_append_drop 16 (bs.drop idx), List.drop_drop]
  have hlen : ((bs.drop idx).take 16).length = 16 := by simp; omega
  rw [hsplit, runUtf8ValidationLoop_ascii_append ((bs.drop idx).take 16) idx hall, hlen]

/-! ## `corePlacedData1` (`UTF8_CHAR_WIDTH`) Lookup Lemmas -/

set_option maxRecDepth 2000 in
theorem corePlacedData1_length : corePlacedData1.length = 256 := rfl

private def utf8CharWidthRowOk (w : BitVec 8) (i : Nat) : Bool :=
  let b := BitVec.ofNat 8 i
  ((w == 4#8) == (0xf0#8 ≤ b && b ≤ 0xf4#8)) &&
  ((w == 3#8) == (0xe0#8 ≤ b && b ≤ 0xef#8)) &&
  ((w == 2#8) == (0xc2#8 ≤ b && b ≤ 0xdf#8))

private def utf8CharWidthCheck : Nat → List (BitVec 8) → Bool
  | _, [] => true
  | i, w :: ws => utf8CharWidthRowOk w i && utf8CharWidthCheck (i + 1) ws

set_option maxRecDepth 2000 in
private theorem utf8CharWidth_table_ok :
    utf8CharWidthCheck 0 corePlacedData1 = true := rfl

private theorem utf8CharWidthCheck_getD :
    ∀ (ws : List (BitVec 8)) (i k : Nat),
      k < ws.length →
      utf8CharWidthCheck i ws = true →
      utf8CharWidthRowOk (ws.getD k 0#8) (i + k) = true
  | [], _, _, hk, _ => by simp at hk
  | w :: _, i, 0, _, h => by
    simp only [utf8CharWidthCheck, Bool.and_eq_true] at h
    simpa only [Nat.add_zero, List.getD_cons_zero] using h.1
  | _ :: ws, i, k + 1, hk, h => by
    simp only [utf8CharWidthCheck, Bool.and_eq_true] at h
    have ih := utf8CharWidthCheck_getD ws (i + 1) k (by simp at hk; omega) h.2
    have heq : i + 1 + k = i + (k + 1) := by omega
    simpa only [heq, List.getD_cons_succ] using ih

private theorem utf8CharWidth_row_of_byte (b0 : BitVec 8) :
    utf8CharWidthRowOk (corePlacedData1.getD b0.toNat 0#8) b0.toNat = true := by
  have hk : b0.toNat < corePlacedData1.length := by
    rw [corePlacedData1_length]; exact b0.isLt
  simpa only [Nat.zero_add] using
    utf8CharWidthCheck_getD corePlacedData1 0 b0.toNat hk utf8CharWidth_table_ok

private theorem bvec8_beq_bool_iff {w c : BitVec 8} {y : Bool}
    (h : ((w == c) == y) = true) : (w = c) ↔ y = true := by
  cases hy : y <;> rw [hy] at h
  · have hne : (w == c) = false := by revert h; cases (w == c) <;> decide
    exact ⟨fun heq => by subst heq; simp at hne, fun hf => False.elim (Bool.noConfusion hf)⟩
  · have heq : (w == c) = true := by revert h; cases (w == c) <;> decide
    exact ⟨fun _ => rfl, fun _ => beq_iff_eq.mp heq⟩

theorem utf8CharWidth_eq_4_iff (b0 : BitVec 8) :
    (corePlacedData1.getD b0.toNat 0#8 = 4#8) ↔ (0xf0#8 ≤ b0 && b0 ≤ 0xf4#8) = true := by
  have h := utf8CharWidth_row_of_byte b0
  unfold utf8CharWidthRowOk at h
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq, Bool.and_eq_true] at h
  exact bvec8_beq_bool_iff h.1.1

theorem utf8CharWidth_eq_3_iff (b0 : BitVec 8) :
    (corePlacedData1.getD b0.toNat 0#8 = 3#8) ↔ (0xe0#8 ≤ b0 && b0 ≤ 0xef#8) = true := by
  have h := utf8CharWidth_row_of_byte b0
  unfold utf8CharWidthRowOk at h
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq, Bool.and_eq_true] at h
  exact bvec8_beq_bool_iff h.1.2

theorem utf8CharWidth_eq_2_iff (b0 : BitVec 8) :
    (corePlacedData1.getD b0.toNat 0#8 = 2#8) ↔ (0xc2#8 ≤ b0 && b0 ≤ 0xdf#8) = true := by
  have h := utf8CharWidth_row_of_byte b0
  unfold utf8CharWidthRowOk at h
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq, Bool.and_eq_true] at h
  exact bvec8_beq_bool_iff h.2

theorem utf8CharWidth_zeroExtend32_eq (w : BitVec 8) (k : BitVec 32)
    (hk : k.toNat < 256) :
    (BitVec.setWidth 32 w == k) = (w == BitVec.setWidth 8 k) := by
  by_cases h : w = BitVec.setWidth 8 k
  · subst h
    have h1 : BitVec.setWidth 32 (BitVec.setWidth 8 k) = k := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hk,
        Nat.mod_eq_of_lt (show k.toNat < 4294967296 by omega)]
    simp [h1]
  · have hne : BitVec.setWidth 32 w ≠ k := by
      intro heq; apply h
      simpa using congrArg (BitVec.setWidth 8) heq
    simp [beq_false_of_ne h, beq_false_of_ne hne]

/-! ## Index and Length Arithmetic Lemmas -/

def utf8AlignOff (p : BitVec 64) : BitVec 64 :=
  ((p + 7#64) &&& ~~~7#64) - p

/-- `subs x9, x1, #0xf; csel x10, xzr, x9, cc` computes `BitVec.ofNat 64 (n - 15)` for all
    `n < 2 ^ 64` (saturating at `0` when `n < 15`). -/
theorem utf8_saturating_sub15 {n : Nat} (hn : n < 2 ^ 64) :
    (if !(AddWithCarry64 (BitVec.ofNat 64 n) (~~~15#64) true).2.c then 0#64
     else (AddWithCarry64 (BitVec.ofNat 64 n) (~~~15#64) true).1) =
      BitVec.ofNat 64 (n - 15) := by
  have hc : (AddWithCarry64 (BitVec.ofNat 64 n) (~~~15#64) true).2.c =
      decide (15 ≤ n) := by
    have h1 : ∀ x : BitVec 64,
        (AddWithCarry64 x (~~~15#64) true).2.c = !(x.ult 15#64) := by
      intro x; unfold AddWithCarry64; bv_robdd
    rw [h1]
    simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, show (15#64).toNat = 15 from rfl]
    by_cases h15 : 15 ≤ n
    · have hlt : ¬ (n < 15) := by omega
      simp [h15, hlt]
    · have hlt : n < 15 := by omega
      simp [h15, hlt]
  have hv : (AddWithCarry64 (BitVec.ofNat 64 n) (~~~15#64) true).1 =
      BitVec.ofNat 64 n - 15#64 := by
    have h2 : ∀ x : BitVec 64,
        (AddWithCarry64 x (~~~15#64) true).1 = x - 15#64 := by
      intro x; unfold AddWithCarry64; bv_robdd
    exact h2 _
  rw [hc, hv]
  by_cases h15 : 15 ≤ n
  · simp only [decide_eq_true h15, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_sub, Nat.mod_eq_of_lt hn]
    omega
  · have hsub0 : n - 15 = 0 := by omega
    simp [decide_eq_false h15, hsub0]

theorem addWithCarry64_sub_c (a b : BitVec 64) :
    (AddWithCarry64 a (~~~b) true).2.c = !(a.ult b) := by
  unfold AddWithCarry64; bv_robdd

theorem addWithCarry64_sub_z (a b : BitVec 64) :
    (AddWithCarry64 a (~~~b) true).2.z = (a == b) := by
  unfold AddWithCarry64; bv_robdd

theorem utf8_cmp_cs_of_eq {n : Nat} :
    (AddWithCarry64 (BitVec.ofNat 64 n) (~~~BitVec.ofNat 64 n) true).2.c = true := by
  rw [addWithCarry64_sub_c]; simp [BitVec.ult]

theorem utf8_cmp_cs_of_lt {idx n : Nat} (hlt : idx < n) (hn : n < 2 ^ 64) :
    (AddWithCarry64 (BitVec.ofNat 64 idx) (~~~BitVec.ofNat 64 n) true).2.c = false := by
  rw [addWithCarry64_sub_c]
  simp [BitVec.ult, Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (show idx < 2 ^ 64 by omega), hlt]

theorem utf8_cmp_sub15_cs {idx n : Nat} (hle : idx ≤ n) (hn : n < 2 ^ 64) :
    (AddWithCarry64 (BitVec.ofNat 64 idx) (~~~BitVec.ofNat 64 (n - 15)) true).2.c =
      decide (¬ (idx + 16 ≤ n)) := by
  rw [addWithCarry64_sub_c]
  simp only [BitVec.ult, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show idx < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show n - 15 < 2 ^ 64 by omega)]
  by_cases h : idx + 16 ≤ n
  · have hlt : idx < n - 15 := by omega
    simp [h, hlt]
  · have hge : ¬ (idx < n - 15) := by omega
    simp [h, hge]

theorem utf8_cmp_ne_len {idx n : Nat} (hle : idx ≤ n) (hn : n < 2 ^ 64) :
    (!(AddWithCarry64 (BitVec.ofNat 64 n) (~~~BitVec.ofNat 64 idx) true).2.z) =
      decide (idx < n) := by
  rw [addWithCarry64_sub_z]
  by_cases hlt : idx < n
  · have hne : BitVec.ofNat 64 n ≠ BitVec.ofNat 64 idx := by
      intro heq
      have htn := congrArg BitVec.toNat heq
      simp [Nat.mod_eq_of_lt hn,
        Nat.mod_eq_of_lt (show idx < 2 ^ 64 by omega)] at htn
      omega
    simp [beq_false_of_ne hne, hlt]
  · have heq : idx = n := by omega
    subst heq; simp

/-! ## Byte Sign-Extension and 32-Bit Condition-Code Lemmas -/

theorem ldrsb32_bit31_eq_nonAscii (b : BitVec 8) :
    ((BitVec.signExtend 32 b).zeroExtend 64).getLsbD 31 = decide (¬ (b < 0x80#8)) := by
  revert b; decide

theorem signExtend32_and_ff64 (b : BitVec 8) :
    (BitVec.signExtend 32 b).zeroExtend 64 &&& 0xff#64 = BitVec.ofNat 64 b.toNat ∧
    BitVec.zeroExtend 64 b = BitVec.ofNat 64 b.toNat := by
  have hb : b.toNat < 256 := b.isLt
  refine ⟨?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq
    have h1 : (BitVec.signExtend 32 b).zeroExtend 64 &&& 0xff#64 = b.zeroExtend 64 := by
      revert b; decide
    rw [h1]
    simp [Nat.mod_eq_of_lt (show b.toNat < 2 ^ 64 by omega)]
  · apply BitVec.eq_of_toNat_eq
    simp [Nat.mod_eq_of_lt (show b.toNat < 2 ^ 64 by omega)]

theorem signExtend32_and_ff32 (b : BitVec 8) :
    BitVec.setWidth 32 ((BitVec.signExtend 32 b).zeroExtend 64) &&& 0xff#32 =
      BitVec.setWidth 32 b := by
  revert b; decide

theorem evalBitfield_sxtb32 (dst : BitVec 64) (b : BitVec 8) :
    evalBitfield .W32 .SBFM dst (b.zeroExtend 64) 0 7 = (b.signExtend 32).zeroExtend 64 := by
  have h : evalBitfield .W32 .SBFM dst (b.zeroExtend 64) 0 7 =
      evalBitfield .W32 .SBFM 0#64 (b.zeroExtend 64) 0 7 := rfl
  rw [h]; clear h dst
  revert b; decide

/-- For `cmn w, #0x41` (`adds wzr, b.signExtend 32, 0x41#32`), `CondCode.LE` (`Z || (N != V)`)
    equals `isUtf8ContByte b` and `CondCode.GT` (`!Z && (N == V)`) equals `!isUtf8ContByte b`. -/
theorem cmn_0x41_le_iff_cont (b : BitVec 8) :
    let flags := (AddWithCarry32 (b.signExtend 32) 0x41#32 false).2
    (flags.z || (flags.n != flags.v)) = isUtf8ContByte b ∧
    (!flags.z && (flags.n == flags.v)) = !isUtf8ContByte b := by
  revert b; decide

/-- For `cmn w, #0x40` (`adds wzr, b.signExtend 32, 0x40#32`), `CondCode.LT` (`N != V`) equals
    `isUtf8ContByte b` and `CondCode.GE` (`N == V`) equals `!isUtf8ContByte b`. -/
theorem cmn_0x40_lt_iff_cont (b : BitVec 8) :
    let flags := (AddWithCarry32 (b.signExtend 32) 0x40#32 false).2
    (flags.n != flags.v) = isUtf8ContByte b ∧
    (flags.n == flags.v) = !isUtf8ContByte b := by
  revert b; decide

/-- Surrogate check (`b0 = 0xED`): `cmn w14, #0x61` (`CondCode.LE`) equals
    `0x80#8 ≤ b1 && b1 ≤ 0x9f#8`. -/
theorem cmn_0x61_le_iff_ed_ok (b1 : BitVec 8) :
    let flags := (AddWithCarry32 (b1.signExtend 32) 0x61#32 false).2
    (flags.z || (flags.n != flags.v)) = (0x80#8 ≤ b1 && b1 ≤ 0x9f#8) := by
  revert b1; decide

/-- Upper codepoint bound (`b0 = 0xF4`): `cmn w14, #0x71` (`CondCode.LE`) equals
    `0x80#8 ≤ b1 && b1 ≤ 0x8f#8`. -/
theorem cmn_0x71_le_iff_f4_ok (b1 : BitVec 8) :
    let flags := (AddWithCarry32 (b1.signExtend 32) 0x71#32 false).2
    (flags.z || (flags.n != flags.v)) = (0x80#8 ≤ b1 && b1 ≤ 0x8f#8) := by
  revert b1; decide

theorem and_0xe0_eq_0xa0_iff_e0_ok (b1 : BitVec 8) :
    let flags := (AddWithCarry32 (BitVec.setWidth 32 b1 &&& 0xe0#32) (~~~0xa0#32) true).2
    flags.z = (0xa0#8 ≤ b1 && b1 ≤ 0xbf#8) := by
  revert b1; decide

theorem sub_0x90_ult_0x30_iff_f0_ok (b1 : BitVec 8) :
    let flags := (AddWithCarry32 (BitVec.setWidth 32 b1 - 0x90#32) (~~~0x30#32) true).2
    (!flags.c) = (0x90#8 ≤ b1 && b1 ≤ 0xbf#8) := by
  revert b1; decide

theorem e_range_ee_ef_eq_true (b0 : BitVec 8)
    (he : (0xe0#8 ≤ b0 && b0 ≤ 0xef#8) = true)
    (hne0 : b0 ≠ 0xe0#8) (hned : b0 ≠ 0xed#8)
    (hcs : (AddWithCarry32 (BitVec.setWidth 32 b0 - 0xe1#32) (~~~0x0c#32) true).2.c = true) :
    (!(AddWithCarry32 (BitVec.setWidth 32 b0 &&& 0xfe#32) (~~~0xee#32) true).2.z) = false := by
  revert b0; decide

theorem f_range_f1_f3_hi_false (b0 : BitVec 8)
    (hf : (0xf0#8 ≤ b0 && b0 ≤ 0xf4#8) = true)
    (hne0 : b0 ≠ 0xf0#8) (hne4 : b0 ≠ 0xf4#8) :
    let flags := (AddWithCarry32 (BitVec.setWidth 32 b0 - 0xf1#32) (~~~0x02#32) true).2
    (flags.c && !flags.z) = false := by
  revert b0; decide

theorem addWithCarry32_sub_z (a b : BitVec 32) :
    (AddWithCarry32 a (~~~b) true).2.z = (a == b) := by
  unfold AddWithCarry32; bv_robdd

theorem cmp32_byte_imm_z (b imm : BitVec 8) :
    (AddWithCarry32 (BitVec.setWidth 32 b) (~~~BitVec.setWidth 32 imm) true).2.z = (b == imm) := by
  rw [addWithCarry32_sub_z]
  simpa using utf8CharWidth_zeroExtend32_eq b (BitVec.setWidth 32 imm)
    (by simp only [BitVec.toNat_setWidth]; have := imm.isLt; omega)

/-! ## `runUtf8ValidationLoop` Multi-Byte Unfolding Lemmas -/

theorem drop_eq_nil_of_eq_len {bs : List (BitVec 8)} {idx : Nat} (h : idx = bs.length) :
    bs.drop idx = [] := by
  subst h; exact List.drop_length

theorem runUtf8ValidationLoop_step_ascii {bs : List (BitVec 8)} {idx : Nat}
    (hidx : idx < bs.length) (hb0 : bs.getD idx 0#8 < 0x80#8) :
    runUtf8ValidationLoop idx (bs.drop idx) =
      runUtf8ValidationLoop (idx + 1) (bs.drop (idx + 1)) := by
  rw [List.drop_eq_getD_cons bs idx 0#8 hidx]
  exact runUtf8ValidationLoop_ascii_cons hb0

theorem runUtf8ValidationLoop_err_lead {bs : List (BitVec 8)} {idx : Nat}
    (hidx : idx < bs.length)
    (hnonAscii : ¬ (bs.getD idx 0#8 < 0x80#8))
    (hnot2 : (0xc2#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xdf#8) = false)
    (hnot3 : (0xe0#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xef#8) = false)
    (hnot4 : (0xf0#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xf4#8) = false) :
    runUtf8ValidationLoop idx (bs.drop idx) =
      .error { valid_up_to := idx, error_len := some 1#8 } := by
  rw [List.drop_eq_getD_cons bs idx 0#8 hidx]
  conv => lhs; unfold runUtf8ValidationLoop
  simp only [hnonAscii, hnot2, hnot3, hnot4, Bool.false_eq_true, ↓reduceIte]

theorem runUtf8ValidationLoop_width2_eof {bs : List (BitVec 8)} {idx : Nat}
    (hidx : idx < bs.length) (heof : idx + 1 = bs.length)
    (hw2 : (0xc2#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xdf#8) = true) :
    runUtf8ValidationLoop idx (bs.drop idx) =
      .error { valid_up_to := idx, error_len := none } := by
  have hna : ¬ (bs.getD idx 0#8 < 0x80#8) := by
    revert hw2; generalize bs.getD idx 0#8 = b0; revert b0; decide
  rw [List.drop_eq_getD_cons bs idx 0#8 hidx, drop_eq_nil_of_eq_len heof]
  conv => lhs; unfold runUtf8ValidationLoop
  simp only [hna, hw2, ↓reduceIte]

theorem runUtf8ValidationLoop_width2_step {bs : List (BitVec 8)} {idx : Nat}
    (hidx1 : idx + 1 < bs.length)
    (hw2 : (0xc2#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xdf#8) = true) :
    runUtf8ValidationLoop idx (bs.drop idx) =
      if isUtf8ContByte (bs.getD (idx + 1) 0#8) then
        runUtf8ValidationLoop (idx + 2) (bs.drop (idx + 2))
      else
        .error { valid_up_to := idx, error_len := some 1#8 } := by
  have hna : ¬ (bs.getD idx 0#8 < 0x80#8) := by
    revert hw2; generalize bs.getD idx 0#8 = b0; revert b0; decide
  rw [List.drop_eq_getD_cons bs idx 0#8 (by omega),
      List.drop_eq_getD_cons bs (idx + 1) 0#8 hidx1]
  conv => lhs; unfold runUtf8ValidationLoop
  simp only [hna, hw2, ↓reduceIte, show idx + 1 + 1 = idx + 2 by omega]

def utf8Width3Ok2 (b0 b1 : BitVec 8) : Bool :=
  if b0 == 0xe0#8 then 0xa0#8 ≤ b1 && b1 ≤ 0xbf#8
  else if b0 == 0xed#8 then 0x80#8 ≤ b1 && b1 ≤ 0x9f#8
  else isUtf8ContByte b1

theorem runUtf8ValidationLoop_width3_eof1 {bs : List (BitVec 8)} {idx : Nat}
    (hidx : idx < bs.length) (heof : idx + 1 = bs.length)
    (hw3 : (0xe0#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xef#8) = true) :
    runUtf8ValidationLoop idx (bs.drop idx) =
      .error { valid_up_to := idx, error_len := none } := by
  have h1 : ¬ (bs.getD idx 0#8 < 0x80#8) ∧
      (0xc2#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xdf#8) = false := by
    revert hw3; generalize bs.getD idx 0#8 = b0; revert b0; decide
  rw [List.drop_eq_getD_cons bs idx 0#8 hidx, drop_eq_nil_of_eq_len heof]
  conv => lhs; unfold runUtf8ValidationLoop
  simp only [h1.1, h1.2, hw3, Bool.false_eq_true, ↓reduceIte]

theorem runUtf8ValidationLoop_width3_err1 {bs : List (BitVec 8)} {idx : Nat}
    (hidx1 : idx + 1 < bs.length)
    (hw3 : (0xe0#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xef#8) = true)
    (hok2 : utf8Width3Ok2 (bs.getD idx 0#8) (bs.getD (idx + 1) 0#8) = false) :
    runUtf8ValidationLoop idx (bs.drop idx) =
      .error { valid_up_to := idx, error_len := some 1#8 } := by
  have h1 : ¬ (bs.getD idx 0#8 < 0x80#8) ∧
      (0xc2#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xdf#8) = false := by
    revert hw3; generalize bs.getD idx 0#8 = b0; revert b0; decide
  rw [List.drop_eq_getD_cons bs idx 0#8 (by omega),
      List.drop_eq_getD_cons bs (idx + 1) 0#8 hidx1]
  conv => lhs; unfold runUtf8ValidationLoop
  simp only [h1.1, h1.2, hw3, Bool.false_eq_true, ↓reduceIte]
  change (if (!utf8Width3Ok2 (bs.getD idx 0#8) (bs.getD (idx + 1) 0#8)) = true then _ else _) = _
  simp only [hok2, Bool.not_false, ↓reduceIte]

theorem runUtf8ValidationLoop_width3_eof2 {bs : List (BitVec 8)} {idx : Nat}
    (hidx1 : idx + 1 < bs.length) (heof2 : idx + 2 = bs.length)
    (hw3 : (0xe0#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xef#8) = true)
    (hok2 : utf8Width3Ok2 (bs.getD idx 0#8) (bs.getD (idx + 1) 0#8) = true) :
    runUtf8ValidationLoop idx (bs.drop idx) =
      .error { valid_up_to := idx, error_len := none } := by
  have h1 : ¬ (bs.getD idx 0#8 < 0x80#8) ∧
      (0xc2#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xdf#8) = false := by
    revert hw3; generalize bs.getD idx 0#8 = b0; revert b0; decide
  rw [List.drop_eq_getD_cons bs idx 0#8 (by omega),
      List.drop_eq_getD_cons bs (idx + 1) 0#8 hidx1,
      show idx + 1 + 1 = idx + 2 by omega, drop_eq_nil_of_eq_len heof2]
  conv => lhs; unfold runUtf8ValidationLoop
  simp only [h1.1, h1.2, hw3, Bool.false_eq_true, ↓reduceIte]
  change (if (!utf8Width3Ok2 (bs.getD idx 0#8) (bs.getD (idx + 1) 0#8)) = true then _ else _) = _
  simp only [hok2, Bool.not_true, Bool.false_eq_true, ↓reduceIte]

theorem runUtf8ValidationLoop_width3_step {bs : List (BitVec 8)} {idx : Nat}
    (hidx2 : idx + 2 < bs.length)
    (hw3 : (0xe0#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xef#8) = true)
    (hok2 : utf8Width3Ok2 (bs.getD idx 0#8) (bs.getD (idx + 1) 0#8) = true) :
    runUtf8ValidationLoop idx (bs.drop idx) =
      if isUtf8ContByte (bs.getD (idx + 2) 0#8) then
        runUtf8ValidationLoop (idx + 3) (bs.drop (idx + 3))
      else
        .error { valid_up_to := idx, error_len := some 2#8 } := by
  have h1 : ¬ (bs.getD idx 0#8 < 0x80#8) ∧
      (0xc2#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xdf#8) = false := by
    revert hw3; generalize bs.getD idx 0#8 = b0; revert b0; decide
  rw [List.drop_eq_getD_cons bs idx 0#8 (by omega),
      List.drop_eq_getD_cons bs (idx + 1) 0#8 (by omega),
      show idx + 1 + 1 = idx + 2 by omega,
      List.drop_eq_getD_cons bs (idx + 2) 0#8 hidx2]
  conv => lhs; unfold runUtf8ValidationLoop
  simp only [h1.1, h1.2, hw3, Bool.false_eq_true, ↓reduceIte]
  change (if (!utf8Width3Ok2 (bs.getD idx 0#8) (bs.getD (idx + 1) 0#8)) = true then _ else _) = _
  simp only [hok2, Bool.not_true, Bool.false_eq_true, ↓reduceIte, show idx + 2 + 1 = idx + 3 by omega]

def utf8Width4Ok2 (b0 b1 : BitVec 8) : Bool :=
  if b0 == 0xf0#8 then 0x90#8 ≤ b1 && b1 ≤ 0xbf#8
  else if b0 == 0xf4#8 then 0x80#8 ≤ b1 && b1 ≤ 0x8f#8
  else isUtf8ContByte b1

theorem runUtf8ValidationLoop_width4_eof1 {bs : List (BitVec 8)} {idx : Nat}
    (hidx : idx < bs.length) (heof : idx + 1 = bs.length)
    (hw4 : (0xf0#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xf4#8) = true) :
    runUtf8ValidationLoop idx (bs.drop idx) =
      .error { valid_up_to := idx, error_len := none } := by
  have h1 : ¬ (bs.getD idx 0#8 < 0x80#8) ∧
      (0xc2#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xdf#8) = false ∧
      (0xe0#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xef#8) = false := by
    revert hw4; generalize bs.getD idx 0#8 = b0; revert b0; decide
  rw [List.drop_eq_getD_cons bs idx 0#8 hidx, drop_eq_nil_of_eq_len heof]
  conv => lhs; unfold runUtf8ValidationLoop
  simp only [h1.1, h1.2.1, h1.2.2, hw4, Bool.false_eq_true, ↓reduceIte]

theorem runUtf8ValidationLoop_width4_err1 {bs : List (BitVec 8)} {idx : Nat}
    (hidx1 : idx + 1 < bs.length)
    (hw4 : (0xf0#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xf4#8) = true)
    (hok2 : utf8Width4Ok2 (bs.getD idx 0#8) (bs.getD (idx + 1) 0#8) = false) :
    runUtf8ValidationLoop idx (bs.drop idx) =
      .error { valid_up_to := idx, error_len := some 1#8 } := by
  have h1 : ¬ (bs.getD idx 0#8 < 0x80#8) ∧
      (0xc2#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xdf#8) = false ∧
      (0xe0#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xef#8) = false := by
    revert hw4; generalize bs.getD idx 0#8 = b0; revert b0; decide
  rw [List.drop_eq_getD_cons bs idx 0#8 (by omega),
      List.drop_eq_getD_cons bs (idx + 1) 0#8 hidx1]
  conv => lhs; unfold runUtf8ValidationLoop
  simp only [h1.1, h1.2.1, h1.2.2, hw4, Bool.false_eq_true, ↓reduceIte]
  change (if (!utf8Width4Ok2 (bs.getD idx 0#8) (bs.getD (idx + 1) 0#8)) = true then _ else _) = _
  simp only [hok2, Bool.not_false, ↓reduceIte]

theorem runUtf8ValidationLoop_width4_eof2 {bs : List (BitVec 8)} {idx : Nat}
    (hidx1 : idx + 1 < bs.length) (heof2 : idx + 2 = bs.length)
    (hw4 : (0xf0#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xf4#8) = true)
    (hok2 : utf8Width4Ok2 (bs.getD idx 0#8) (bs.getD (idx + 1) 0#8) = true) :
    runUtf8ValidationLoop idx (bs.drop idx) =
      .error { valid_up_to := idx, error_len := none } := by
  have h1 : ¬ (bs.getD idx 0#8 < 0x80#8) ∧
      (0xc2#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xdf#8) = false ∧
      (0xe0#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xef#8) = false := by
    revert hw4; generalize bs.getD idx 0#8 = b0; revert b0; decide
  rw [List.drop_eq_getD_cons bs idx 0#8 (by omega),
      List.drop_eq_getD_cons bs (idx + 1) 0#8 hidx1,
      show idx + 1 + 1 = idx + 2 by omega, drop_eq_nil_of_eq_len heof2]
  conv => lhs; unfold runUtf8ValidationLoop
  simp only [h1.1, h1.2.1, h1.2.2, hw4, Bool.false_eq_true, ↓reduceIte]
  change (if (!utf8Width4Ok2 (bs.getD idx 0#8) (bs.getD (idx + 1) 0#8)) = true then _ else _) = _
  simp only [hok2, Bool.not_true, Bool.false_eq_true, ↓reduceIte]

theorem runUtf8ValidationLoop_width4_err2 {bs : List (BitVec 8)} {idx : Nat}
    (hidx2 : idx + 2 < bs.length)
    (hw4 : (0xf0#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xf4#8) = true)
    (hok2 : utf8Width4Ok2 (bs.getD idx 0#8) (bs.getD (idx + 1) 0#8) = true)
    (hc2 : isUtf8ContByte (bs.getD (idx + 2) 0#8) = false) :
    runUtf8ValidationLoop idx (bs.drop idx) =
      .error { valid_up_to := idx, error_len := some 2#8 } := by
  have h1 : ¬ (bs.getD idx 0#8 < 0x80#8) ∧
      (0xc2#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xdf#8) = false ∧
      (0xe0#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xef#8) = false := by
    revert hw4; generalize bs.getD idx 0#8 = b0; revert b0; decide
  rw [List.drop_eq_getD_cons bs idx 0#8 (by omega),
      List.drop_eq_getD_cons bs (idx + 1) 0#8 (by omega),
      show idx + 1 + 1 = idx + 2 by omega,
      List.drop_eq_getD_cons bs (idx + 2) 0#8 hidx2]
  conv => lhs; unfold runUtf8ValidationLoop
  simp only [h1.1, h1.2.1, h1.2.2, hw4, Bool.false_eq_true, ↓reduceIte]
  change (if (!utf8Width4Ok2 (bs.getD idx 0#8) (bs.getD (idx + 1) 0#8)) = true then _ else _) = _
  simp only [hok2, hc2, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte]

theorem runUtf8ValidationLoop_width4_eof3 {bs : List (BitVec 8)} {idx : Nat}
    (hidx2 : idx + 2 < bs.length) (heof3 : idx + 3 = bs.length)
    (hw4 : (0xf0#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xf4#8) = true)
    (hok2 : utf8Width4Ok2 (bs.getD idx 0#8) (bs.getD (idx + 1) 0#8) = true)
    (hc2 : isUtf8ContByte (bs.getD (idx + 2) 0#8) = true) :
    runUtf8ValidationLoop idx (bs.drop idx) =
      .error { valid_up_to := idx, error_len := none } := by
  have h1 : ¬ (bs.getD idx 0#8 < 0x80#8) ∧
      (0xc2#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xdf#8) = false ∧
      (0xe0#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xef#8) = false := by
    revert hw4; generalize bs.getD idx 0#8 = b0; revert b0; decide
  rw [List.drop_eq_getD_cons bs idx 0#8 (by omega),
      List.drop_eq_getD_cons bs (idx + 1) 0#8 (by omega),
      show idx + 1 + 1 = idx + 2 by omega,
      List.drop_eq_getD_cons bs (idx + 2) 0#8 hidx2,
      show idx + 2 + 1 = idx + 3 by omega, drop_eq_nil_of_eq_len heof3]
  conv => lhs; unfold runUtf8ValidationLoop
  simp only [h1.1, h1.2.1, h1.2.2, hw4, Bool.false_eq_true, ↓reduceIte]
  change (if (!utf8Width4Ok2 (bs.getD idx 0#8) (bs.getD (idx + 1) 0#8)) = true then _ else _) = _
  simp only [hok2, hc2, Bool.not_true, Bool.false_eq_true, ↓reduceIte]

theorem runUtf8ValidationLoop_width4_step {bs : List (BitVec 8)} {idx : Nat}
    (hidx3 : idx + 3 < bs.length)
    (hw4 : (0xf0#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xf4#8) = true)
    (hok2 : utf8Width4Ok2 (bs.getD idx 0#8) (bs.getD (idx + 1) 0#8) = true)
    (hc2 : isUtf8ContByte (bs.getD (idx + 2) 0#8) = true) :
    runUtf8ValidationLoop idx (bs.drop idx) =
      if isUtf8ContByte (bs.getD (idx + 3) 0#8) then
        runUtf8ValidationLoop (idx + 4) (bs.drop (idx + 4))
      else
        .error { valid_up_to := idx, error_len := some 3#8 } := by
  have h1 : ¬ (bs.getD idx 0#8 < 0x80#8) ∧
      (0xc2#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xdf#8) = false ∧
      (0xe0#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xef#8) = false := by
    revert hw4; generalize bs.getD idx 0#8 = b0; revert b0; decide
  rw [List.drop_eq_getD_cons bs idx 0#8 (by omega),
      List.drop_eq_getD_cons bs (idx + 1) 0#8 (by omega),
      show idx + 1 + 1 = idx + 2 by omega,
      List.drop_eq_getD_cons bs (idx + 2) 0#8 (by omega),
      show idx + 2 + 1 = idx + 3 by omega,
      List.drop_eq_getD_cons bs (idx + 3) 0#8 hidx3]
  conv => lhs; unfold runUtf8ValidationLoop
  simp only [h1.1, h1.2.1, h1.2.2, hw4, Bool.false_eq_true, ↓reduceIte]
  change (if (!utf8Width4Ok2 (bs.getD idx 0#8) (bs.getD (idx + 1) 0#8)) = true then _ else _) = _
  simp only [hok2, hc2, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    show idx + 3 + 1 = idx + 4 by omega]

end VerifiedLibraries.RustStd

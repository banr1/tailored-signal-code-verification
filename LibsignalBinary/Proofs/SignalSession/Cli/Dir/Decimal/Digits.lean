/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import all Init.Data.String.Defs
import all Init.Data.Repr
public import LibsignalBinary.Proofs.SignalSession.Cli.Kits
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeatedCommon

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Decimal.Helpers

open Arm64 ProofLib CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet

private theorem byteArray_toList_loop (l : List UInt8) :
    ∀ k i r, l.length - i = k →
      ByteArray.toList.loop ⟨⟨l⟩⟩ i r = r.reverse ++ l.drop i := by
  intro k
  induction k with
  | zero =>
    intro i r hk
    rw [ByteArray.toList.loop.eq_1]
    have hni : ¬ i < (⟨⟨l⟩⟩ : ByteArray).size := by
      change ¬ i < l.length
      omega
    simp only [hni, ↓reduceIte]
    rw [List.drop_eq_nil_of_le (by omega), List.append_nil]
  | succ k ih =>
    intro i r hk
    rw [ByteArray.toList.loop.eq_1]
    have hi : i < (⟨⟨l⟩⟩ : ByteArray).size := by
      change i < l.length
      omega
    have hget : (⟨⟨l⟩⟩ : ByteArray).get! i = l[i]'hi :=
      getElem!_pos (⟨l⟩ : Array UInt8) i hi
    simp only [hi, ↓reduceIte]
    rw [ih (i + 1) ((⟨⟨l⟩⟩ : ByteArray).get! i :: r) (by omega),
      List.reverse_cons, List.append_assoc, List.singleton_append, hget,
      ← List.drop_eq_getElem_cons]

private theorem byteArray_toList_eq_data_toList (bs : ByteArray) :
    bs.toList = bs.data.toList := by
  rcases bs with ⟨⟨l⟩⟩
  unfold ByteArray.toList
  rw [byteArray_toList_loop l l.length 0 [] (Nat.sub_zero _), List.reverse_nil, List.nil_append,
    List.drop_zero]

theorem utf8_append (s₁ s₂ : String) : utf8 (s₁ ++ s₂) = utf8 s₁ ++ utf8 s₂ := by
  simp only [utf8, String.toUTF8, String.toByteArray_append, byteArray_toList_eq_data_toList,
    ByteArray.toList_data_append, List.map_append]

private theorem toByteArray_singleton_toList (x : UInt8) :
    ([x] : List UInt8).toByteArray.toList = [x] := by
  rw [byteArray_toList_eq_data_toList, List.data_toByteArray]

private theorem utf8_digitChar (r : Nat) (hr : r < 10) :
    utf8 (String.ofList [Nat.digitChar r]) = [BitVec.ofNat 8 (0x30 + r)] := by
  have hchar : String.utf8EncodeChar (Nat.digitChar r) = [UInt8.ofNat (0x30 + r)] := by
    match r, hr with
    | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl
    | 5, _ => rfl | 6, _ => rfl | 7, _ => rfl | 8, _ => rfl | 9, _ => rfl
  have hmod : (UInt8.ofNat (0x30 + r)).toNat = 0x30 + r := by
    rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  simp only [utf8, String.toUTF8, String.toByteArray_ofList, List.utf8Encode_singleton,
    hchar, toByteArray_singleton_toList, List.map_cons, List.map_nil, hmod]

theorem decimalText_digit (n : Nat) (hn : n < 10) :
    decimalText n = [BitVec.ofNat 8 (0x30 + n)] := by
  have hd : Nat.toDigits 10 n = [Nat.digitChar n] := by
    match n, hn with
    | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl
    | 5, _ => rfl | 6, _ => rfl | 7, _ => rfl | 8, _ => rfl | 9, _ => rfl
  change utf8 (String.ofList (Nat.toDigits 10 n)) = _
  rw [hd]
  exact utf8_digitChar n hn

private theorem toDigitsCore10_eq (fuel : Nat) :
    ∀ n cs, n < fuel → Nat.toDigitsCore 10 fuel n cs = Nat.toDigits 10 n ++ cs := by
  refine Nat.strongRecOn fuel fun fuel ih n cs hf => ?_
  rcases fuel with _ | fuel
  · omega
  · unfold Nat.toDigitsCore
    by_cases hq : n / 10 = 0
    · simp only [Nat.toDigits, Nat.toDigitsCore, hq, ↓reduceIte, List.singleton_append]
    · simp only [hq, ↓reduceIte]
      rw [ih fuel (by omega) (n / 10) _ (by omega)]
      conv => rhs; arg 1; unfold Nat.toDigits Nat.toDigitsCore
      simp only [hq, ↓reduceIte]
      rw [ih n (by omega) (n / 10) [Nat.digitChar (n % 10)] (by omega),
        List.append_assoc, List.singleton_append]

theorem decimalText_ge10 (n : Nat) (hn : 10 ≤ n) :
    decimalText n = decimalText (n / 10) ++ [BitVec.ofNat 8 (0x30 + n % 10)] := by
  have htd : Nat.toDigits 10 n = Nat.toDigits 10 (n / 10) ++ [Nat.digitChar (n % 10)] := by
    have hq : n / 10 ≠ 0 := by omega
    unfold Nat.toDigits
    unfold Nat.toDigitsCore
    simp only [hq, ↓reduceIte]
    exact toDigitsCore10_eq n (n / 10) [Nat.digitChar (n % 10)] (by omega)
  have hstr : toString n = String.ofList (Nat.toDigits 10 (n / 10)) ++
      String.ofList [Nat.digitChar (n % 10)] := by
    change String.ofList (Nat.toDigits 10 n) = _
    rw [htd, String.ofList_append]
  change utf8 (toString n) = utf8 (String.ofList (Nat.toDigits 10 (n / 10))) ++ _
  rw [hstr, utf8_append, utf8_digitChar (n % 10) (Nat.mod_lt _ (by omega))]

theorem decimalText_length_le (k n : Nat) (hk : 1 ≤ k) (hn : n < 10 ^ k) :
    (decimalText n).length ≤ k := by
  induction k generalizing n with
  | zero => omega
  | succ k ih =>
    by_cases h10 : n < 10
    · rw [decimalText_digit n h10, List.length_singleton]
      omega
    · have hk1 : 1 ≤ k := by
        rcases k with _ | k
        · exfalso; omega
        · omega
      have hdiv : n / 10 < 10 ^ k := by
        have hp : 10 ^ (k + 1) = 10 ^ k * 10 := rfl
        omega
      rw [decimalText_ge10 n (by omega), List.length_append, List.length_singleton]
      have := ih (n / 10) hk1 hdiv
      omega

theorem ule_nine_true {n : BitVec 32} (h : n.toNat ≤ 9) :
    n.ule 9#32 = true := by
  rw [BitVec.ule_eq_decide, decide_eq_true_eq]
  exact h

theorem ule_nine_false {n : BitVec 32} (h : 10 ≤ n.toNat) :
    n.ule 9#32 = false := by
  rw [BitVec.ule_eq_decide, decide_eq_false_iff_not]
  change ¬ n.toNat ≤ 9
  omega

theorem div10_magic_nat (m : Nat) (hm : m < 2 ^ 32) :
    (m * 3435973837) / 2 ^ 35 = m / 10 := by
  omega

theorem div10_shift_toNat (n : BitVec 32) :
    ((BitVec.zeroExtend 64 n * 3435973837#64) >>> 35).toNat = n.toNat / 10 := by
  have hn : n.toNat < 2 ^ 32 := n.isLt
  have hext : (BitVec.zeroExtend 64 n).toNat = n.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
  have hc : (3435973837#64).toNat = 3435973837 := rfl
  have hmul : (BitVec.zeroExtend 64 n * 3435973837#64).toNat = n.toNat * 3435973837 := by
    rw [BitVec.toNat_mul, hext, hc, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_ushiftRight, hmul, Nat.shiftRight_eq_div_pow]
  exact div10_magic_nat n.toNat hn

theorem div10_trunc32 (n : BitVec 32) :
    BitVec.truncate 32 ((BitVec.zeroExtend 64 n * 3435973837#64) >>> 35) =
      BitVec.ofNat 32 (n.toNat / 10) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, div10_shift_toNat, BitVec.toNat_ofNat]

theorem div10_trunc32_toNat (n : BitVec 32) :
    (BitVec.truncate 32 ((BitVec.zeroExtend 64 n * 3435973837#64) >>> 35)).toNat =
      n.toNat / 10 := by
  have hn : n.toNat < 2 ^ 32 := n.isLt
  rw [div10_trunc32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

private theorem digit_orr_of_lt10 (r : Nat) (hr : r < 10) :
    BitVec.zeroExtend 8 (BitVec.zeroExtend 64 (BitVec.ofNat 32 r) ||| 206158430256#64) =
      BitVec.ofNat 8 (0x30 + r) := by
  match r, hr with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl
  | 9, _ => rfl

theorem digit_byte_eq (n : BitVec 32) :
    BitVec.zeroExtend 8
      (BitVec.zeroExtend 64
          (n - BitVec.truncate 32 ((BitVec.zeroExtend 64 n * 3435973837#64) >>> 35) * 10#32) |||
        206158430256#64) =
      BitVec.ofNat 8 (0x30 + n.toNat % 10) := by
  have hn : n.toNat < 2 ^ 32 := n.isLt
  have hprod : BitVec.ofNat 32 (n.toNat / 10) * 10#32 = BitVec.ofNat 32 (n.toNat / 10 * 10) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  have hle : BitVec.ofNat 32 (n.toNat / 10 * 10) ≤ n := by
    rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  have hrem : n - BitVec.ofNat 32 (n.toNat / 10 * 10) = BitVec.ofNat 32 (n.toNat % 10) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le hle, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  rw [div10_trunc32, hprod, hrem]
  exact digit_orr_of_lt10 (n.toNat % 10) (Nat.mod_lt _ (by omega))

theorem cap_beq_len_true {cap : BitVec 64} {len : Nat} (h : cap.toNat = len) :
    (cap == BitVec.ofNat 64 len) = true := by
  rw [beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (h ▸ cap.isLt)]

theorem cap_beq_len_false {cap : BitVec 64} {len : Nat} (h : len < cap.toNat) :
    (cap == BitVec.ofNat 64 len) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans h cap.isLt)] at ht
  omega

theorem memRegion_24_cells (a : BitVec 64) :
    memRegion a 24 =
      ∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) := by
  rw [memRegion_split' (b := a) (b' := a + 8#64) (n := 8) (k := 16) (by omega) rfl (by omega),
    memRegion_split' (b := a + 8#64) (b' := a + 16#64) (n := 8) (k := 8)
      (by omega) (by bv_omega) (by omega),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

theorem stack_slot_memRegion24 (sp v1 v2 v3 : BitVec 64) :
    ((sp - 72#64) ↦₆₄ v1 ∗ (sp - 64#64) ↦₆₄ v2 ∗ (sp - 56#64) ↦₆₄ v3) ⊢
      memRegion (sp - 72#64) 24 := by
  have hv8 : sp - 72#64 + 8#64 = sp - 64#64 := by bv_omega
  have hv16 : sp - 72#64 + 16#64 = sp - 56#64 := by bv_omega
  rw [memRegion_24_cells (sp - 72#64), hv8, hv16]
  exact Entails.sepExists_right v3 (Entails.sepExists_right v2 (Entails.sepExists_right v1 (Entails.refl _)))

theorem stack_slot_empty_vecU8At (A : RustAlloc) (sp : BitVec 64) :
    (((sp - 72#64) ↦₆₄ 0#64) ∗ ((sp - 64#64) ↦₆₄ 1#64) ∗ ((sp - 56#64) ↦₆₄ 0#64)) =
      vecU8At A (sp - 72#64) 0#64 1#64 [] := by
  have hv8 : sp - 72#64 + 8#64 = sp - 64#64 := by bv_omega
  have hv16 : sp - 72#64 + 16#64 = sp - 56#64 := by bv_omega
  have hpure : (([] : List (BitVec 8)).length ≤ (0#64 : BitVec 64).toNat ∧
      (0#64 : BitVec 64).toNat < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0) = True :=
    eq_true ⟨by decide, by decide, by decide⟩
  rw [SpqrV1.Varint.vecU8At_expose_header A (sp - 72#64) 0#64 1#64 [], hv8, hv16,
    hpure, pure_true, emp_sepConj]
  simp only [List.length_nil]
  change ((sp - 72#64) ↦₆₄ 0#64) ∗ ((sp - 64#64) ↦₆₄ 1#64) ∗ ((sp - 56#64) ↦₆₄ 0#64) =
    ((sp - 72#64) ↦₆₄ 0#64) ∗ ((sp - 64#64) ↦₆₄ 1#64) ∗ ((sp - 56#64) ↦₆₄ 0#64) ∗ emp
  ac_rfl

theorem stack_slot_eq_header_rest (A : RustAlloc) (sp cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A (sp - 72#64) cap ptr bs =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        ((sp - 72#64) ↦₆₄ cap) ∗ ((sp - 64#64) ↦₆₄ ptr) ∗
        ((sp - 56#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        SpqrV1.Varint.vecU8RestAt A cap ptr bs := by
  have hv8 : sp - 72#64 + 8#64 = sp - 64#64 := by bv_omega
  have hv16 : sp - 72#64 + 16#64 = sp - 56#64 := by bv_omega
  rw [SpqrV1.Varint.vecU8At_eq_header_rest A (sp - 72#64) cap ptr bs, hv8, hv16]

theorem stack_slot_of_header_rest (A : RustAlloc) (sp cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hle : bs.length ≤ cap.toNat) (hcap : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0) :
    (((sp - 72#64) ↦₆₄ cap) ∗ ((sp - 64#64) ↦₆₄ ptr) ∗
      ((sp - 56#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      SpqrV1.Varint.vecU8RestAt A cap ptr bs) =
      vecU8At A (sp - 72#64) cap ptr bs := by
  have hv8 : sp - 72#64 + 8#64 = sp - 64#64 := by bv_omega
  have hv16 : sp - 72#64 + 16#64 = sp - 56#64 := by bv_omega
  rw [← SpqrV1.Varint.vecU8At_of_header_rest A (sp - 72#64) cap ptr bs hle hcap hptr, hv8, hv16]

theorem stack_slot_open_one (A : RustAlloc) (sp cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hlt : bs.length < cap.toNat) (hcap : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0) :
    vecU8At A (sp - 72#64) cap ptr bs =
      ∃∗ b0 : BitVec 8,
        ((sp - 72#64) ↦₆₄ cap) ∗ ((sp - 64#64) ↦₆₄ ptr) ∗
        ((sp - 56#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
          ((ptr + BitVec.ofNat 64 bs.length) ↦₈ b0) ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length + 1#64) (cap.toNat - bs.length - 1) := by
  have hv8 : sp - 72#64 + 8#64 = sp - 64#64 := by bv_omega
  have hv16 : sp - 72#64 + 16#64 = sp - 56#64 := by bv_omega
  rw [SpqrV1.Varint.vecU8At_expose_slice A (sp - 72#64) cap ptr bs 1 (by omega) hcap hptr (by omega),
    hv8, hv16, ProofLib.memRegion_one]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

theorem vecU8At_snoc_sret (A : RustAlloc) (ret cap ptr : BitVec 64)
    (bs : List (BitVec 8)) (d : BitVec 8)
    (hlt : bs.length < cap.toNat) (hcap : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0) :
    ((ret ↦₆₄ cap) ∗ ((ret + 8#64) ↦₆₄ ptr) ∗
      ((ret + 16#64) ↦₆₄ (BitVec.ofNat 64 bs.length + 1#64)) ∗
      A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
      ((ptr + BitVec.ofNat 64 bs.length) ↦₈ d) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length + 1#64) (cap.toNat - bs.length - 1)) =
      vecU8At A ret cap ptr (bs ++ [d]) := by
  have h1 := SpqrV1.Varint.vecU8At_pack_slice A ret cap ptr bs [d]
    (by simp only [List.length_singleton]; omega) hcap hptr (List.cons_ne_nil _ _)
  simpa only [List.length_singleton, BitVec.ofNat_eq_ofNat, pointsToBytes_cons,
    pointsToBytes_nil, sepConj_emp, sepConj_assoc] using h1

theorem stk_le_pow64_of_pre {m : Memory} {ret sp : BitVec 64} {stk : Nat} {R : SepProp}
    (hm : m ⊨ memRegion ret 24 ∗ stackAt sp stk ∗ R) :
    stk ≤ 2 ^ 64 := by
  by_cases hpos : 0 < stk
  · have hd := (IsBlock.memRegion ret 24).disjoint (IsBlock.memRegion (sp - BitVec.ofNat 64 stk) stk)
      (by omega) hpos hm
    exact Nat.le_of_lt (Nat.lt_of_le_of_lt hd.2 (BitVec.isLt _))
  · omega

end CryptoVerification.SignalSession.Cli.Decimal.Helpers

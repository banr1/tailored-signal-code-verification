/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Mathlib.NumberTheory.LucasPrimality
public import LibsignalBinary.Specifications.SignalPqxdh.Model
import LibsignalBinary.Proofs.SpecLemmas.SignalPqxdh.Model
import Mathlib.Tactic.NormNum.Prime

/-!
# Curve25519 subgroup order primality, byte encodings, and clamping arithmetic

**Checked by Lean.** Certifies `Nat.Prime l25519` via a Lucas-Pratt primality certificate and proves
little-endian scalar encoding, XEdDSA `H_1` prefix domain separation, and RFC 7748 clamped-scalar
`±` recovery in `ZMod l25519`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Computational.Proofs.SignalPqxdh.XeddsaRom.PrimeL25519

open _root_.SignalPqxdh (Bytes clampScalar25519 fitBytesRef fitBytesRef_length scalarIsInRange)

/-- Field characteristic `2 ^ 255 - 19` of Curve25519 and Ed25519. -/
abbrev p25519 : ℕ := 2 ^ 255 - 19

/-- Prime order `2 ^ 252 + 27742317777372353535851937790883648493` of the Curve25519/Ed25519
subgroup. -/
abbrev l25519 : ℕ := 2 ^ 252 + 27742317777372353535851937790883648493

theorem two_pow_252_lt_l25519 : 2 ^ 252 < l25519 := by
  unfold l25519; omega

theorem l25519_lt_two_pow_253 : l25519 < 2 ^ 253 := by
  unfold l25519; omega

theorem l25519_lt_p25519 : l25519 < p25519 := by
  unfold l25519 p25519; omega

theorem l25519_pos : 0 < l25519 := by
  unfold l25519; omega

/-! ## Lucas-Pratt primality certificate for `l25519` -/

private def powStepMod (half a : ℕ) (isOdd : Bool) (p : ℕ) : ℕ :=
  let sq := (half * half) % p
  if isOdd then (sq * a) % p else sq

private def fastPowModFuel : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, p => 1 % p
  | fuel + 1, a, e, p =>
      if e = 0 then 1 % p
      else powStepMod (fastPowModFuel fuel a (e / 2) p) a (e % 2 == 1) p

private def fastPowMod (a e p : ℕ) : ℕ :=
  fastPowModFuel 255 a e p

private theorem powStepMod_lt (half a : ℕ) (isOdd : Bool) {p : ℕ} (hp : 0 < p) :
    powStepMod half a isOdd p < p := by
  unfold powStepMod
  cases isOdd <;> simp [Nat.mod_lt _ hp]

private theorem fastPowModFuel_lt (fuel a e : ℕ) {p : ℕ} (hp : 0 < p) :
    fastPowModFuel fuel a e p < p := by
  cases fuel with
  | zero => exact Nat.mod_lt _ hp
  | succ fuel =>
    unfold fastPowModFuel
    split
    · exact Nat.mod_lt _ hp
    · exact powStepMod_lt _ _ _ hp

private theorem fastPowModFuel_eq_zmod_pow :
    ∀ (fuel a e p : ℕ), e < 2 ^ fuel →
      ((fastPowModFuel fuel a e p : ℕ) : ZMod p) = (a : ZMod p) ^ e
  | 0, a, e, p, he => by
      have he0 : e = 0 := by omega
      subst he0
      simp [fastPowModFuel]
  | fuel + 1, a, e, p, he => by
      unfold fastPowModFuel
      split
      · rename_i he0
        subst he0
        simp
      · rename_i hne0
        have he_div : e / 2 < 2 ^ fuel := by
          rw [Nat.pow_succ] at he
          omega
        have hrec := fastPowModFuel_eq_zmod_pow fuel a (e / 2) p he_div
        unfold powStepMod
        rcases Nat.mod_two_eq_zero_or_one e with hmod0 | hmod1
        · have hodd : (e % 2 == 1) = false := by simp [hmod0]
          rw [hodd]
          simp only [Bool.false_eq_true, ↓reduceIte]
          have he2 : e = 2 * (e / 2) := by omega
          calc
            (((fastPowModFuel fuel a (e / 2) p * fastPowModFuel fuel a (e / 2) p) % p : ℕ) :
                ZMod p)
                = ((fastPowModFuel fuel a (e / 2) p : ZMod p) *
                    (fastPowModFuel fuel a (e / 2) p : ZMod p)) := by
                    rw [ZMod.natCast_mod, Nat.cast_mul]
            _ = ((a : ZMod p) ^ (e / 2)) * ((a : ZMod p) ^ (e / 2)) := by rw [hrec]
            _ = (a : ZMod p) ^ e := by
                  conv_rhs => rw [he2, pow_mul', sq]
        · have hodd : (e % 2 == 1) = true := by simp [hmod1]
          rw [hodd]
          simp only [↓reduceIte]
          have he2 : e = 2 * (e / 2) + 1 := by omega
          calc
            ((((fastPowModFuel fuel a (e / 2) p *
                fastPowModFuel fuel a (e / 2) p) % p * a) % p : ℕ) : ZMod p)
                = (((fastPowModFuel fuel a (e / 2) p *
                    fastPowModFuel fuel a (e / 2) p) % p : ℕ) : ZMod p) * (a : ZMod p) := by
                    rw [ZMod.natCast_mod, Nat.cast_mul]
            _ = ((fastPowModFuel fuel a (e / 2) p : ZMod p) *
                  (fastPowModFuel fuel a (e / 2) p : ZMod p)) * (a : ZMod p) := by
                  rw [ZMod.natCast_mod, Nat.cast_mul]
            _ = ((a : ZMod p) ^ (e / 2) * (a : ZMod p) ^ (e / 2)) * (a : ZMod p) := by rw [hrec]
            _ = (a : ZMod p) ^ e := by
                  conv_rhs => rw [he2, pow_add, pow_one, pow_mul', sq]

private theorem mem_of_prime_dvd_prod {q : ℕ} (hq : q.Prime) :
    ∀ {qs : List (ℕ × ℕ)}, (∀ qe ∈ qs, Nat.Prime qe.1) →
      q ∣ (qs.map (fun qe => qe.1 ^ qe.2)).prod → ∃ qe ∈ qs, q = qe.1
  | [], _, hdvd => by
      simp only [List.map_nil, List.prod_nil] at hdvd
      exact absurd (Nat.eq_one_of_dvd_one hdvd) hq.ne_one
  | qe :: rest, hprimes, hdvd => by
      simp only [List.map_cons, List.prod_cons] at hdvd
      rcases hq.dvd_mul.mp hdvd with hhead | htail
      · have hq_dvd_qe : q ∣ qe.1 := hq.dvd_of_dvd_pow hhead
        have hqe_prime : Nat.Prime qe.1 := hprimes qe List.mem_cons_self
        have heq : q = qe.1 := (Nat.prime_dvd_prime_iff_eq hq hqe_prime).mp hq_dvd_qe
        exact ⟨qe, List.mem_cons_self, heq⟩
      · obtain ⟨qe', hmem, heq⟩ :=
          mem_of_prime_dvd_prod hq (fun x hx => hprimes x (List.mem_cons_of_mem qe hx)) htail
        exact ⟨qe', List.mem_cons_of_mem qe hmem, heq⟩

private theorem lucas_step (p a : ℕ) (qs : List (ℕ × ℕ))
    (hp : 1 < p) (hbound : p < 2 ^ 255)
    (hprod : (qs.map (fun qe => qe.1 ^ qe.2)).prod = p - 1)
    (hqprime : ∀ qe ∈ qs, Nat.Prime qe.1)
    (hf : fastPowMod a (p - 1) p = 1)
    (hord : ∀ qe ∈ qs, fastPowMod a ((p - 1) / qe.1) p ≠ 1) :
    Nat.Prime p := by
  have : Fact (1 < p) := ⟨hp⟩
  refine lucas_primality p (a : ZMod p) ?_ ?_
  · rw [← fastPowModFuel_eq_zmod_pow 255 a (p - 1) p (by omega)]
    change ((fastPowMod a (p - 1) p : ℕ) : ZMod p) = 1
    rw [hf, Nat.cast_one]
  · intro q hq hqdvd
    rw [← hprod] at hqdvd
    obtain ⟨qe, hmem, rfl⟩ := mem_of_prime_dvd_prod hq hqprime hqdvd
    have hdiv_lt : (p - 1) / qe.1 < 2 ^ 255 :=
      lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
    rw [← fastPowModFuel_eq_zmod_pow 255 a ((p - 1) / qe.1) p hdiv_lt]
    intro heq
    have hval := congrArg ZMod.val heq
    have hlt : fastPowMod a ((p - 1) / qe.1) p < p := fastPowModFuel_lt 255 a _ (by omega)
    change ((fastPowMod a ((p - 1) / qe.1) p : ℕ) : ZMod p).val = (1 : ZMod p).val at hval
    rw [ZMod.val_natCast_of_lt hlt, ZMod.val_one] at hval
    exact hord qe hmem hval

private theorem prime_leaf_primes :
    Nat.Prime 2 ∧ Nat.Prime 3 ∧ Nat.Prime 5 ∧ Nat.Prime 7 ∧ Nat.Prime 11 ∧
    Nat.Prime 23 ∧ Nat.Prime 41 ∧ Nat.Prime 43 ∧ Nat.Prime 73 ∧ Nat.Prime 269 ∧
    Nat.Prime 307 ∧ Nat.Prime 1361 ∧ Nat.Prime 2551 ∧ Nat.Prime 2851 ∧ Nat.Prime 5879 ∧
    Nat.Prime 30703 ∧ Nat.Prime 82163 ∧ Nat.Prime 132667 ∧ Nat.Prime 137849 ∧
    Nat.Prime 409477 ∧ Nat.Prime 531581 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num

private theorem prime_14741173 : Nat.Prime 14741173 := by
  have h := prime_leaf_primes
  refine lucas_step 14741173 2 [(2, 2), (3, 2), (409477, 1)]
    (by decide) (by decide) (by decide) ?_ (by decide) (by decide)
  intro qe hmem; simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem prime_58964693 : Nat.Prime 58964693 := by
  refine lucas_step 58964693 2 [(2, 2), (14741173, 1)]
    (by decide) (by decide) (by decide) ?_ (by decide) (by decide)
  intro qe hmem; simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl
  · exact prime_leaf_primes.1
  · exact prime_14741173

private theorem prime_3044861653679985063343 : Nat.Prime 3044861653679985063343 := by
  have h := prime_leaf_primes
  refine lucas_step 3044861653679985063343 5
    [(2, 1), (3, 1), (11, 1), (30703, 1), (82163, 1), (132667, 1), (137849, 1)]
    (by decide) (by decide) (by decide) ?_ (by decide) (by decide)
  intro qe hmem; simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem prime_198211423230930754013084525763697 :
    Nat.Prime 198211423230930754013084525763697 := by
  have h := prime_leaf_primes
  refine lucas_step 198211423230930754013084525763697 5
    [(2, 4), (3, 1), (23, 1), (58964693, 1), (3044861653679985063343, 1)]
    (by decide) (by decide) (by decide) ?_ (by decide) (by decide)
  intro qe hmem; simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2.2.2.2.1
  · exact prime_58964693
  · exact prime_3044861653679985063343

private theorem prime_292386187 : Nat.Prime 292386187 := by
  have h := prime_leaf_primes
  refine lucas_step 292386187 2 [(2, 1), (3, 4), (307, 1), (5879, 1)]
    (by decide) (by decide) (by decide) ?_ (by decide) (by decide)
  intro qe hmem; simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem prime_213441916511 : Nat.Prime 213441916511 := by
  have h := prime_leaf_primes
  refine lucas_step 213441916511 13 [(2, 1), (5, 1), (73, 1), (292386187, 1)]
    (by decide) (by decide) (by decide) ?_ (by decide) (by decide)
  intro qe hmem; simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl
  · exact h.1
  · exact h.2.2.1
  · exact h.2.2.2.2.2.2.2.2.1
  · exact prime_292386187

private theorem prime_1224481 : Nat.Prime 1224481 := by
  have h := prime_leaf_primes
  refine lucas_step 1224481 13 [(2, 5), (3, 1), (5, 1), (2551, 1)]
    (by decide) (by decide) (by decide) ?_ (by decide) (by decide)
  intro qe hmem; simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem prime_1257559732178653 : Nat.Prime 1257559732178653 := by
  have h := prime_leaf_primes
  refine lucas_step 1257559732178653 2
    [(2, 2), (3, 1), (7, 1), (23, 1), (531581, 1), (1224481, 1)]
    (by decide) (by decide) (by decide) ?_ (by decide) (by decide)
  intro qe hmem; simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2.2.1
  · exact h.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  · exact prime_1224481

private theorem prime_4434155615661930479 : Nat.Prime 4434155615661930479 := by
  have h := prime_leaf_primes
  refine lucas_step 4434155615661930479 17
    [(2, 1), (41, 1), (43, 1), (1257559732178653, 1)]
    (by decide) (by decide) (by decide) ?_ (by decide) (by decide)
  intro qe hmem; simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl
  · exact h.1
  · exact h.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.1
  · exact prime_1257559732178653

private theorem prime_172054593956031949258510691 :
    Nat.Prime 172054593956031949258510691 := by
  have h := prime_leaf_primes
  refine lucas_step 172054593956031949258510691 2
    [(2, 1), (5, 1), (1361, 1), (2851, 1), (4434155615661930479, 1)]
    (by decide) (by decide) (by decide) ?_ (by decide) (by decide)
  intro qe hmem; simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl
  · exact h.1
  · exact h.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact prime_4434155615661930479

private theorem prime_19757330305831588566944191468367130476339 :
    Nat.Prime 19757330305831588566944191468367130476339 := by
  have h := prime_leaf_primes
  refine lucas_step 19757330305831588566944191468367130476339 2
    [(2, 1), (269, 1), (213441916511, 1), (172054593956031949258510691, 1)]
    (by decide) (by decide) (by decide) ?_ (by decide) (by decide)
  intro qe hmem; simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl
  · exact h.1
  · exact h.2.2.2.2.2.2.2.2.2.1
  · exact prime_213441916511
  · exact prime_172054593956031949258510691

private theorem prime_276602624281642239937218680557139826668747 :
    Nat.Prime 276602624281642239937218680557139826668747 := by
  have h := prime_leaf_primes
  refine lucas_step 276602624281642239937218680557139826668747 2
    [(2, 1), (7, 1), (19757330305831588566944191468367130476339, 1)]
    (by decide) (by decide) (by decide) ?_ (by decide) (by decide)
  intro qe hmem; simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl
  · exact h.1
  · exact h.2.2.2.1
  · exact prime_19757330305831588566944191468367130476339

/-- Primality of the Curve25519/Ed25519 subgroup order `l25519`. -/
theorem prime_l25519 : Nat.Prime l25519 := by
  have h := prime_leaf_primes
  refine lucas_step l25519 2
    [(2, 2), (3, 1), (11, 1),
     (198211423230930754013084525763697, 1),
     (276602624281642239937218680557139826668747, 1)]
    (by decide) (by decide) (by decide) ?_ (by decide) (by decide)
  intro qe hmem; simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2.2.2.1
  · exact prime_198211423230930754013084525763697
  · exact prime_276602624281642239937218680557139826668747

instance instFactPrimeL25519 : Fact (Nat.Prime l25519) := ⟨prime_l25519⟩

theorem eight_ne_zero_zmod_l25519 : (8 : ZMod l25519) ≠ 0 := by
  intro h
  have hval := congrArg ZMod.val h
  have hlt : 8 < l25519 := by unfold l25519; omega
  rw [show (8 : ZMod l25519) = ((8 : ℕ) : ZMod l25519) from rfl,
    ZMod.val_natCast_of_lt hlt, ZMod.val_zero] at hval
  omega

/-! ## Little-endian scalar encodings -/

/-- Little-endian natural number decoded from a byte list. -/
def natOfBytesLE : Bytes → ℕ
  | [] => 0
  | b :: bs => b.toNat + 256 * natOfBytesLE bs

/-- `k`-byte little-endian encoding of `n mod 256 ^ k`. -/
def bytesOfNatLE : ℕ → ℕ → Bytes
  | 0, _ => []
  | k + 1, n => UInt8.ofNat (n % 256) :: bytesOfNatLE k (n / 256)

@[simp]
theorem bytesOfNatLE_length (k n : ℕ) : (bytesOfNatLE k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [bytesOfNatLE, ih]

theorem natOfBytesLE_lt (bs : Bytes) : natOfBytesLE bs < 256 ^ bs.length := by
  induction bs with
  | nil => simp [natOfBytesLE]
  | cons b bs ih =>
    have hb : b.toNat < 256 := b.toBitVec.isLt
    simp only [natOfBytesLE, List.length_cons, Nat.pow_succ]
    omega

theorem natOfBytesLE_append (xs ys : Bytes) :
    natOfBytesLE (xs ++ ys) = natOfBytesLE xs + 256 ^ xs.length * natOfBytesLE ys := by
  induction xs with
  | nil => simp [natOfBytesLE]
  | cons x xs ih =>
    simp only [List.cons_append, natOfBytesLE, List.length_cons, ih, Nat.pow_succ]
    ring

@[simp]
theorem natOfBytesLE_replicate_zero (k : ℕ) : natOfBytesLE (List.replicate k 0) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, natOfBytesLE, ih]

@[simp]
theorem bytesOfNatLE_zero (k : ℕ) : bytesOfNatLE k 0 = List.replicate k 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [bytesOfNatLE, Nat.zero_mod, Nat.zero_div, ih, List.replicate_succ]
    rfl

theorem natOfBytesLE_bytesOfNatLE (k n : ℕ) :
    natOfBytesLE (bytesOfNatLE k n) = n % 256 ^ k := by
  induction k generalizing n with
  | zero => simp [bytesOfNatLE, natOfBytesLE, Nat.mod_one]
  | succ k ih =>
    simp only [bytesOfNatLE, natOfBytesLE, ih]
    have hlt : n % 256 < UInt8.size := Nat.mod_lt n (by decide)
    have hu8 : (UInt8.ofNat (n % 256)).toNat = n % 256 := UInt8.toNat_ofNat_of_lt' hlt
    rw [hu8]
    have h1 : n % 256 + 256 * ((n / 256) % 256 ^ k) = (n % 256 + 256 * (n / 256)) % (256 * 256 ^ k) := by
      have hdiv := Nat.div_add_mod (n / 256) (256 ^ k)
      have hmod_lt : n % 256 + 256 * ((n / 256) % 256 ^ k) < 256 * 256 ^ k := by
        have := Nat.mod_lt (n / 256) (Nat.pow_pos (by decide : 0 < 256) (n := k))
        have := Nat.mod_lt n (by decide : 0 < 256)
        omega
      have heq : n % 256 + 256 * (n / 256) =
          (256 * 256 ^ k) * ((n / 256) / 256 ^ k) + (n % 256 + 256 * ((n / 256) % 256 ^ k)) := by
        linarith
      rw [heq, Nat.mul_add_mod, Nat.mod_eq_of_lt hmod_lt]
    rw [h1, Nat.mod_add_div, Nat.pow_succ']

theorem bytesOfNatLE_natOfBytesLE (bs : Bytes) :
    bytesOfNatLE bs.length (natOfBytesLE bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    have hb : b.toNat < 256 := b.toBitVec.isLt
    simp only [List.length_cons, natOfBytesLE, bytesOfNatLE]
    have hmod : (b.toNat + 256 * natOfBytesLE bs) % 256 = b.toNat := by omega
    have hdiv : (b.toNat + 256 * natOfBytesLE bs) / 256 = natOfBytesLE bs := by omega
    rw [hmod, hdiv, ih]
    congr 1
    exact UInt8.toNat_inj.mp (UInt8.toNat_ofNat_of_lt' hb)

theorem getD_toNat_eq_div_mod (bs : Bytes) (i : ℕ) :
    (bs.getD i 0).toNat = (natOfBytesLE bs / 256 ^ i) % 256 := by
  induction bs generalizing i with
  | nil => simp [natOfBytesLE]
  | cons b bs ih =>
    have hb : b.toNat < 256 := b.toBitVec.isLt
    cases i with
    | zero =>
      simp only [List.getD_cons_zero, natOfBytesLE, Nat.pow_zero, Nat.div_one]
      omega
    | succ i =>
      simp only [List.getD_cons_succ, natOfBytesLE, ih i, Nat.pow_succ']
      have hdiv : (b.toNat + 256 * natOfBytesLE bs) / (256 * 256 ^ i) =
          natOfBytesLE bs / 256 ^ i := by
        rw [← Nat.div_div_eq_div_mul]
        have : (b.toNat + 256 * natOfBytesLE bs) / 256 = natOfBytesLE bs := by omega
        rw [this]
      rw [hdiv]

/-- Canonical 32-byte little-endian encoding of a scalar in `ZMod l25519`. -/
def encodeScalarBytes (x : ZMod l25519) : Bytes :=
  bytesOfNatLE 32 x.val

/-- Decode a byte list into `ZMod l25519` as a little-endian natural number modulo `l25519`. -/
def decodeScalarBytes (bs : Bytes) : ZMod l25519 :=
  (natOfBytesLE bs : ZMod l25519)

@[simp]
theorem encodeScalarBytes_length (x : ZMod l25519) : (encodeScalarBytes x).length = 32 :=
  bytesOfNatLE_length 32 x.val

@[simp]
theorem encodeScalarBytes_zero : encodeScalarBytes 0 = List.replicate 32 0 := by
  simp [encodeScalarBytes]

theorem natOfBytesLE_encodeScalarBytes (x : ZMod l25519) :
    natOfBytesLE (encodeScalarBytes x) = x.val := by
  unfold encodeScalarBytes
  rw [natOfBytesLE_bytesOfNatLE]
  have hlt : x.val < 256 ^ 32 := by
    have hx : x.val < l25519 := x.val_lt
    have hl : l25519 < 256 ^ 32 := by unfold l25519; omega
    omega
  exact Nat.mod_eq_of_lt hlt

@[simp]
theorem decodeScalarBytes_encodeScalarBytes (x : ZMod l25519) :
    decodeScalarBytes (encodeScalarBytes x) = x := by
  unfold decodeScalarBytes
  rw [natOfBytesLE_encodeScalarBytes, ZMod.natCast_zmod_val]

theorem encodeScalarBytes_injective : Function.Injective encodeScalarBytes := by
  intro x y h
  have := congrArg decodeScalarBytes h
  simpa using this

theorem encodeScalarBytes_byte31_lt_32 (x : ZMod l25519) :
    ((encodeScalarBytes x).getD 31 0).toNat < 32 := by
  rw [getD_toNat_eq_div_mod, natOfBytesLE_encodeScalarBytes]
  have hx : x.val < l25519 := x.val_lt
  have hl : l25519 < 32 * 256 ^ 31 := by
    have := l25519_lt_two_pow_253
    omega
  have hdiv : x.val / 256 ^ 31 < 32 := Nat.div_lt_of_lt_mul (by omega)
  omega

private theorem uint8_ofNat_toNat_eq (b : UInt8) : UInt8.ofNat b.toNat = b :=
  UInt8.toNat_inj.mp (UInt8.toNat_ofNat_of_lt' b.toBitVec.isLt)

theorem encodeScalarBytes_byte31_and_e0 (x : ZMod l25519) :
    ((encodeScalarBytes x).getD 31 0 &&& 0xE0) = 0 := by
  have hlt := encodeScalarBytes_byte31_lt_32 x
  have hcheck : ∀ i : Fin 256, i.val < 32 → UInt8.ofNat i.val &&& 0xE0 = 0 := by decide
  set b := (encodeScalarBytes x).getD 31 0
  simpa [uint8_ofNat_toNat_eq b] using hcheck ⟨b.toNat, b.toBitVec.isLt⟩ hlt

theorem encodeScalarBytes_byte31_and_60 (x : ZMod l25519) :
    ((encodeScalarBytes x).getD 31 0 &&& 0x60) = 0 := by
  have hlt := encodeScalarBytes_byte31_lt_32 x
  have hcheck : ∀ i : Fin 256, i.val < 32 → UInt8.ofNat i.val &&& 0x60 = 0 := by decide
  set b := (encodeScalarBytes x).getD 31 0
  simpa [uint8_ofNat_toNat_eq b] using hcheck ⟨b.toNat, b.toBitVec.isLt⟩ hlt

theorem encodeScalarBytes_byte31_and_7f (x : ZMod l25519) :
    ((encodeScalarBytes x).getD 31 0 &&& 0x7F) = (encodeScalarBytes x).getD 31 0 := by
  have hlt := encodeScalarBytes_byte31_lt_32 x
  have hcheck : ∀ i : Fin 256, i.val < 32 → UInt8.ofNat i.val &&& 0x7F = UInt8.ofNat i.val := by
    decide
  set b := (encodeScalarBytes x).getD 31 0
  simpa [uint8_ofNat_toNat_eq b] using hcheck ⟨b.toNat, b.toBitVec.isLt⟩ hlt

/-! ## XEdDSA hash-prefix domain separation -/

/-- 32-byte domain-separation prefix `0xFE || 0xFF^31` of XEdDSA's nonce hash `H_1`. -/
def xeddsaHashPrefix : Bytes :=
  [0xFE] ++ List.replicate 31 0xFF

@[simp]
theorem xeddsaHashPrefix_length : xeddsaHashPrefix.length = 32 := by
  simp [xeddsaHashPrefix]

/-- Clears bit 7 of byte 31 of a 32-byte buffer. -/
def clearSignBit32 (bs : Bytes) : Bytes :=
  bs.take 31 ++ [bs.getD 31 0 &&& 0x7F]

@[simp]
theorem clearSignBit32_length {bs : Bytes} (h : bs.length = 32) :
    (clearSignBit32 bs).length = 32 := by
  simp [clearSignBit32, h]

theorem scalarIsInRange_clearSignBit32_xeddsaHashPrefix :
    scalarIsInRange (clearSignBit32 xeddsaHashPrefix) = false := by
  decide

theorem natOfBytesLE_clearSignBit32_xeddsaHashPrefix :
    natOfBytesLE (clearSignBit32 xeddsaHashPrefix) = 2 ^ 255 - 2 := by
  decide

theorem ne_xeddsaHashPrefix_of_lt_p25519 {capR : Bytes}
    (hy : natOfBytesLE (clearSignBit32 capR) < p25519) :
    capR ≠ xeddsaHashPrefix := by
  intro heq
  subst heq
  rw [natOfBytesLE_clearSignBit32_xeddsaHashPrefix] at hy
  unfold p25519 at hy
  omega

/-- Compressed Edwards points in canonical range cannot collide with `xeddsaHashPrefix`-prefixed
inputs. -/
theorem append_ne_xeddsaHashPrefix_append {capR rest1 rest2 : Bytes}
    (hlen : capR.length = 32)
    (hrange : scalarIsInRange (clearSignBit32 capR) = true) :
    capR ++ rest1 ≠ xeddsaHashPrefix ++ rest2 := by
  intro heq
  have htake := congrArg (List.take 32) heq
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
    List.take_append_of_le_length (by simp), List.take_of_length_le (by simp)] at htake
  rw [htake, scalarIsInRange_clearSignBit32_xeddsaHashPrefix] at hrange
  exact Bool.false_ne_true hrange

/-! ## Clamped scalar arithmetic and `±` recovery -/

@[simp]
theorem clampScalar25519_length (sk : Bytes) : (clampScalar25519 sk).length = 32 := by
  have hfit : (fitBytesRef 32 sk).length = 32 := fitBytesRef_length 32 sk
  unfold clampScalar25519
  simp only [List.length_append, List.length_map, List.length_take, List.length_drop, hfit]
  omega

private theorem fitBytesRef_of_length_eq {n : ℕ} {s : Bytes} (hs : s.length = n) :
    fitBytesRef n s = s := by
  simp [fitBytesRef, hs]

private theorem clampScalar25519_unfold_of_length_32 {s : Bytes} (hs : s.length = 32) :
    clampScalar25519 s =
      [s.getD 0 0 &&& 0xF8] ++ (s.drop 1).take 30 ++ [(s.getD 31 0 &&& 0x7F) ||| 0x40] := by
  have hfit : fitBytesRef 32 s = s := fitBytesRef_of_length_eq hs
  unfold clampScalar25519
  dsimp only
  rw [hfit]
  rcases s with _ | ⟨b0, rest⟩
  · simp at hs
  have hrest_len : rest.length = 31 := by simpa using hs
  have hlt30 : 30 < rest.length := by omega
  have hdrop30 : (rest.drop 30).take 1 = [rest.getD 30 0] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt30, Option.getD_some,
      List.drop_eq_getElem_cons hlt30]
    rfl
  change [b0 &&& 0xF8] ++ rest.take 30 ++ List.map (fun b => (b &&& 0x7F) ||| 0x40)
    ((rest.drop 30).take 1) = [b0 &&& 0xF8] ++ rest.take 30 ++ [(rest.getD 30 0 &&& 0x7F) ||| 0x40]
  rw [hdrop30]
  rfl

private theorem clampScalar25519_eq_clamp_fit (sk : Bytes) :
    clampScalar25519 sk = clampScalar25519 (fitBytesRef 32 sk) := by
  have hfit : fitBytesRef 32 (fitBytesRef 32 sk) = fitBytesRef 32 sk :=
    fitBytesRef_of_length_eq (fitBytesRef_length 32 sk)
  unfold clampScalar25519
  dsimp only
  rw [hfit]

private theorem uint8_and_f8_mod_8 (b : UInt8) : (b &&& 0xF8).toNat % 8 = 0 := by
  have hcheck : ∀ i : Fin 256, (UInt8.ofNat i.val &&& 0xF8).toNat % 8 = 0 := by decide
  simpa [uint8_ofNat_toNat_eq b] using hcheck ⟨b.toNat, b.toBitVec.isLt⟩

private theorem uint8_clamp_hi_lo (b : UInt8) : 64 ≤ ((b &&& 0x7F) ||| 0x40).toNat := by
  have hcheck : ∀ i : Fin 256, 64 ≤ ((UInt8.ofNat i.val &&& 0x7F) ||| 0x40).toNat := by decide
  simpa [uint8_ofNat_toNat_eq b] using hcheck ⟨b.toNat, b.toBitVec.isLt⟩

private theorem uint8_clamp_hi_hi (b : UInt8) : ((b &&& 0x7F) ||| 0x40).toNat < 128 := by
  have hcheck : ∀ i : Fin 256, ((UInt8.ofNat i.val &&& 0x7F) ||| 0x40).toNat < 128 := by decide
  simpa [uint8_ofNat_toNat_eq b] using hcheck ⟨b.toNat, b.toBitVec.isLt⟩

theorem natOfBytesLE_clampScalar25519_bounds (sk : Bytes) :
    ∃ k : ℕ, natOfBytesLE (clampScalar25519 sk) = 8 * k ∧ 2 ^ 251 ≤ k ∧ k < 2 ^ 252 := by
  rw [clampScalar25519_eq_clamp_fit sk,
    clampScalar25519_unfold_of_length_32 (fitBytesRef_length 32 sk)]
  set s := fitBytesRef 32 sk
  have hs : s.length = 32 := fitBytesRef_length 32 sk
  have hmid_len : ((s.drop 1).take 30).length = 30 := by simp [hs]
  set b0 := s.getD 0 0
  set b31 := s.getD 31 0
  rw [List.append_assoc, List.singleton_append, natOfBytesLE, natOfBytesLE_append, hmid_len]
  have hb0_mod : (b0 &&& 0xF8).toNat % 8 = 0 := uint8_and_f8_mod_8 b0
  have hb0_lt : (b0 &&& 0xF8).toNat < 256 := (b0 &&& 0xF8).toBitVec.isLt
  have hb31_lo : 64 ≤ ((b31 &&& 0x7F) ||| 0x40).toNat := uint8_clamp_hi_lo b31
  have hb31_hi : ((b31 &&& 0x7F) ||| 0x40).toNat < 128 := uint8_clamp_hi_hi b31
  have hmid_lt : natOfBytesLE ((s.drop 1).take 30) < 256 ^ 30 := by
    have hlt := natOfBytesLE_lt ((s.drop 1).take 30)
    rwa [hmid_len] at hlt
  have hlast_nat : natOfBytesLE [((b31 &&& 0x7F) ||| 0x40)] = ((b31 &&& 0x7F) ||| 0x40).toNat := by
    simp [natOfBytesLE]
  rw [hlast_nat]
  let val := (b0 &&& 0xF8).toNat + 256 * (natOfBytesLE ((s.drop 1).take 30) +
    256 ^ 30 * ((b31 &&& 0x7F) ||| 0x40).toNat)
  refine ⟨val / 8, ?_, ?_, ?_⟩ <;> dsimp only [val] <;> omega

private theorem clampScalar25519_bytesOfNatLE_eight_mul {k : ℕ}
    (hk_lo : 2 ^ 251 ≤ k) (hk_hi : k < 2 ^ 252) :
    clampScalar25519 (bytesOfNatLE 32 (8 * k)) = bytesOfNatLE 32 (8 * k) := by
  set bs := bytesOfNatLE 32 (8 * k)
  have hbs_len : bs.length = 32 := bytesOfNatLE_length 32 (8 * k)
  have hbs_nat : natOfBytesLE bs = 8 * k := by
    dsimp only [bs]
    rw [natOfBytesLE_bytesOfNatLE]
    exact Nat.mod_eq_of_lt (by omega)
  rw [clampScalar25519_unfold_of_length_32 hbs_len]
  have hb0_nat : (bs.getD 0 0).toNat = (8 * k) % 256 := by
    rw [getD_toNat_eq_div_mod, hbs_nat]; simp
  have hb31_nat : (bs.getD 31 0).toNat = (8 * k) / 256 ^ 31 := by
    rw [getD_toNat_eq_div_mod, hbs_nat]
    exact Nat.mod_eq_of_lt (by omega)
  have hb0_fix : bs.getD 0 0 &&& 0xF8 = bs.getD 0 0 := by
    have hmod8 : (bs.getD 0 0).toNat % 8 = 0 := by omega
    have hcheck : ∀ i : Fin 256, i.val % 8 = 0 → UInt8.ofNat i.val &&& 0xF8 = UInt8.ofNat i.val := by
      decide
    set b := bs.getD 0 0
    simpa [uint8_ofNat_toNat_eq b] using hcheck ⟨b.toNat, b.toBitVec.isLt⟩ hmod8
  have hb31_fix : ((bs.getD 31 0 &&& 0x7F) ||| 0x40) = bs.getD 31 0 := by
    have hlo : 64 ≤ (bs.getD 31 0).toNat := by omega
    have hhi : (bs.getD 31 0).toNat < 128 := by omega
    have hcheck : ∀ i : Fin 256, 64 ≤ i.val → i.val < 128 →
        ((UInt8.ofNat i.val &&& 0x7F) ||| 0x40) = UInt8.ofNat i.val := by
      decide
    set b := bs.getD 31 0
    simpa [uint8_ofNat_toNat_eq b] using hcheck ⟨b.toNat, b.toBitVec.isLt⟩ hlo hhi
  rw [hb0_fix, hb31_fix]
  rcases bs with _ | ⟨b0, rest⟩
  · simp at hbs_len
  have hrest_len : rest.length = 31 := by simpa using hbs_len
  have hlt30 : 30 < rest.length := by omega
  have hrest_split : rest.take 30 ++ [rest.getD 30 0] = rest := by
    have hdrop_all : rest.drop 30 = [rest.getD 30 0] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt30, Option.getD_some,
        List.drop_eq_getElem_cons hlt30, List.drop_eq_nil_of_le (by omega)]
    conv_rhs => rw [← List.take_append_drop 30 rest, hdrop_all]
  change [b0] ++ rest.take 30 ++ [rest.getD 30 0] = b0 :: rest
  rw [List.append_assoc, List.singleton_append, hrest_split]

theorem clampScalar25519_idem (sk : Bytes) :
    clampScalar25519 (clampScalar25519 sk) = clampScalar25519 sk := by
  obtain ⟨k, hk_eq, hk_lo, hk_hi⟩ := natOfBytesLE_clampScalar25519_bounds sk
  have hbytes : clampScalar25519 sk = bytesOfNatLE 32 (8 * k) := by
    rw [← bytesOfNatLE_natOfBytesLE (clampScalar25519 sk), clampScalar25519_length, hk_eq]
  rw [hbytes]
  exact clampScalar25519_bytesOfNatLE_eight_mul hk_lo hk_hi

/-- Clamped X25519 private key `sk` decoded into `ZMod l25519`. -/
def clampedScalarZMod (sk : Bytes) : ZMod l25519 :=
  decodeScalarBytes (clampScalar25519 sk)

theorem clampedScalarZMod_clamp (sk : Bytes) :
    clampedScalarZMod (clampScalar25519 sk) = clampedScalarZMod sk := by
  simp [clampedScalarZMod, clampScalar25519_idem]

theorem clampedScalarZMod_ne_zero (sk : Bytes) : clampedScalarZMod sk ≠ 0 := by
  obtain ⟨k, hk_eq, hk_lo, hk_hi⟩ := natOfBytesLE_clampScalar25519_bounds sk
  unfold clampedScalarZMod decodeScalarBytes
  rw [hk_eq, Nat.cast_mul, show ((8 : ℕ) : ZMod l25519) = (8 : ZMod l25519) from rfl]
  refine mul_ne_zero eight_ne_zero_zmod_l25519 ?_
  intro hk0
  have hval := congrArg ZMod.val hk0
  have hk_lt : k < l25519 := lt_trans hk_hi two_pow_252_lt_l25519
  rw [ZMod.val_natCast_of_lt hk_lt, ZMod.val_zero] at hval
  omega

/-- Recovers the unique 32-byte RFC 7748 clamped scalar matching `±aExt` in `ZMod l25519`. -/
noncomputable def recoverClampedScalar (aExt : ZMod l25519) : Bytes :=
  let k0 : ℕ := ((8 : ZMod l25519)⁻¹ * aExt).val
  let kCand : ℕ := if 2 ^ 251 ≤ k0 ∧ k0 < 2 ^ 252 then k0 else (l25519 - k0) % l25519
  bytesOfNatLE 32 (8 * kCand)

@[simp]
theorem recoverClampedScalar_length (aExt : ZMod l25519) :
    (recoverClampedScalar aExt).length = 32 := by
  unfold recoverClampedScalar
  exact bytesOfNatLE_length 32 _

/-- When `aExt = ±clampedScalarZMod sk`, `recoverClampedScalar aExt` is clamped and equals
`±clampedScalarZMod sk`. -/
theorem recoverClampedScalar_spec {sk : Bytes} {aExt : ZMod l25519}
    (ha : aExt = clampedScalarZMod sk ∨ aExt = -clampedScalarZMod sk) :
    clampScalar25519 (recoverClampedScalar aExt) = recoverClampedScalar aExt ∧
      (clampedScalarZMod (recoverClampedScalar aExt) = clampedScalarZMod sk ∨
        clampedScalarZMod (recoverClampedScalar aExt) = -clampedScalarZMod sk) := by
  obtain ⟨k, hk_eq, hk_lo, hk_hi⟩ := natOfBytesLE_clampScalar25519_bounds sk
  have hk_lt_l : k < l25519 := lt_trans hk_hi two_pow_252_lt_l25519
  have ha_sk : clampedScalarZMod sk = (8 : ZMod l25519) * (k : ZMod l25519) := by
    unfold clampedScalarZMod decodeScalarBytes
    rw [hk_eq, Nat.cast_mul]; rfl
  have h8 : (8 : ZMod l25519) ≠ 0 := eight_ne_zero_zmod_l25519
  have hk_pos : 0 < k := by omega
  rcases ha with rfl | rfl
  · have hk0_eq : ((8 : ZMod l25519)⁻¹ * clampedScalarZMod sk).val = k := by
      rw [ha_sk, inv_mul_cancel_left₀ h8, ZMod.val_natCast_of_lt hk_lt_l]
    have hrec : recoverClampedScalar (clampedScalarZMod sk) = bytesOfNatLE 32 (8 * k) := by
      unfold recoverClampedScalar
      simp only [hk0_eq, hk_lo, hk_hi, and_self, ↓reduceIte]
    have hclamp := clampScalar25519_bytesOfNatLE_eight_mul hk_lo hk_hi
    rw [hrec]
    refine ⟨hclamp, Or.inl ?_⟩
    unfold clampedScalarZMod decodeScalarBytes
    rw [hclamp, natOfBytesLE_bytesOfNatLE, Nat.mod_eq_of_lt (by omega), hk_eq]
  · have hk0_eq : ((8 : ZMod l25519)⁻¹ * (-clampedScalarZMod sk)).val = l25519 - k := by
      rw [ha_sk, mul_neg, inv_mul_cancel_left₀ h8]
      have hk_ne0 : (k : ZMod l25519) ≠ 0 := by
        intro h0
        have := congrArg ZMod.val h0
        rw [ZMod.val_natCast_of_lt hk_lt_l, ZMod.val_zero] at this
        omega
      rw [ZMod.neg_val]
      simp [hk_ne0, ZMod.val_natCast_of_lt hk_lt_l]
    have hnot_in_or_in : (2 ^ 251 ≤ l25519 - k ∧ l25519 - k < 2 ^ 252) ∨
        ¬ (2 ^ 251 ≤ l25519 - k ∧ l25519 - k < 2 ^ 252) := Classical.em _
    rcases hnot_in_or_in with hin | hnot_in
    · have hrec : recoverClampedScalar (-clampedScalarZMod sk) =
          bytesOfNatLE 32 (8 * (l25519 - k)) := by
        unfold recoverClampedScalar
        simp only [hk0_eq, hin.1, hin.2, and_self, ↓reduceIte]
      have hclamp := clampScalar25519_bytesOfNatLE_eight_mul hin.1 hin.2
      rw [hrec]
      refine ⟨hclamp, Or.inr ?_⟩
      unfold clampedScalarZMod decodeScalarBytes
      rw [hclamp, natOfBytesLE_bytesOfNatLE, Nat.mod_eq_of_lt (by omega),
        Nat.cast_mul, Nat.cast_sub (le_of_lt hk_lt_l), ZMod.natCast_self, zero_sub,
        mul_neg, hk_eq, Nat.cast_mul]
    · have hsub_mod : (l25519 - (l25519 - k)) % l25519 = k := by
        have : l25519 - (l25519 - k) = k := by omega
        rw [this, Nat.mod_eq_of_lt hk_lt_l]
      have hrec : recoverClampedScalar (-clampedScalarZMod sk) = bytesOfNatLE 32 (8 * k) := by
        unfold recoverClampedScalar
        simp only [hk0_eq, hnot_in, ↓reduceIte, hsub_mod]
      have hclamp := clampScalar25519_bytesOfNatLE_eight_mul hk_lo hk_hi
      rw [hrec]
      refine ⟨hclamp, Or.inl ?_⟩
      unfold clampedScalarZMod decodeScalarBytes
      rw [hclamp, natOfBytesLE_bytesOfNatLE, Nat.mod_eq_of_lt (by omega), hk_eq]

end Computational.Proofs.SignalPqxdh.XeddsaRom.PrimeL25519

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Getters.Defs
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import ProofLib.SepLogic.WPp

/-!
# `memRegion` and Receiver-Chain Eviction Helpers for `S3CommitSpec`

Arithmetic, multi-cell `memRegion` splitting, and `vecBuf` eviction helper lemmas supporting the
`receiver_chains` eviction loop of `S3CommitSpec`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegBH

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.DecryptPq
open CryptoVerification.LibsignalSession

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace BS10

theorem len_lt_of_cons_le {α : Type} {x : α} {xs : List α} (hle : (x :: xs).length ≤ 2 ^ 32) :
    xs.length < 2 ^ 32 := by
  simp only [List.length_cons] at hle
  omega

theorem ult_five_of_ge_six {n : Nat} (hge : 6 ≤ n) (hlt : n < 2 ^ 32) :
    BitVec.ult 5#64 (BitVec.ofNat 64 n) = true := by
  rw [BitVec.ult_iff_lt, BitVec.lt_def, show (5#64).toNat = 5 from rfl,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem le_five_of_not_ge_six {n : Nat} (h : ¬ 6 ≤ n) : n ≤ 5 := by omega

theorem ult_five_eq_false_of_le_five {n : Nat} (hle : n ≤ 5) :
    BitVec.ult 5#64 (BitVec.ofNat 64 n) = false := by
  rw [Bool.eq_false_iff, ne_eq, BitVec.ult_iff_lt, BitVec.lt_def,
      show (5#64).toNat = 5 from rfl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem ult_six_of_lt_six {n : Nat} (hlt : n < 6) :
    BitVec.ult (BitVec.ofNat 64 n) 6#64 = true := by
  rw [BitVec.ult_iff_lt, BitVec.lt_def, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
  exact hlt

theorem le_five_of_lt_six {n : Nat} (hlt : n < 6) : n ≤ 5 := by omega

theorem ge_six_of_not_lt_six {n : Nat} (h : ¬ n < 6) : 6 ≤ n := by omega

theorem ult_six_eq_false_of_not_lt_six {n : Nat} (h : ¬ n < 6) (hle : n ≤ 2 ^ 32) :
    BitVec.ult (BitVec.ofNat 64 n) 6#64 = false := by
  rw [Bool.eq_false_iff, ne_eq, BitVec.ult_iff_lt, BitVec.lt_def,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact h

theorem memmove_bounds {n : Nat} :
    0 + n * 104 ≤ 104 + n * 104 ∧ 104 + n * 104 ≤ 104 + n * 104 := by omega

end BS10

/-! ## Multi-Cell `memRegion` and Eviction Helpers -/

theorem add_assoc_const (sp c d cd : BitVec 64) (h : c + d = cd := by rfl) :
    sp + c + d = sp + cd := by
  rw [BitVec.add_assoc, h]

theorem cell_to_memRegion_8 (a : BitVec 64) (v : BitVec 64) :
    (a ↦₆₄ v) ⊢ memRegion a 8 := by
  rw [memRegion_eight]
  exact Entails.sepExists_right v (Entails.refl _)

theorem elim_memRegion_8 {m : Memory} {a : BitVec 64} {R : SepProp}
    (h : m ⊨ memRegion a 8 ∗ R) :
    ∃ v : BitVec 64, m ⊨ (a ↦₆₄ v) ∗ R := by
  rw [memRegion_eight, sepExists_sepConj_left, satisfies_sepExists] at h
  exact h

theorem cells_2_to_memRegion_16 (a : BitVec 64) (v0 v1 : BitVec 64) :
    ((a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1)) ⊢ memRegion a 16 := by
  have hsplit := memRegion_split a 8 8 (by decide)
  rw [show (8 + 8 : Nat) = 16 from rfl] at hsplit
  rw [hsplit]
  exact sepConj_mono (cell_to_memRegion_8 a v0) (cell_to_memRegion_8 (a + 8#64) v1)

theorem elim_memRegion_16 {m : Memory} {a : BitVec 64} {R : SepProp}
    (h : m ⊨ memRegion a 16 ∗ R) :
    ∃ v0 v1 : BitVec 64, m ⊨ ((a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1)) ∗ R := by
  have hsplit := memRegion_split a 8 8 (by decide)
  rw [show (8 + 8 : Nat) = 16 from rfl] at hsplit
  rw [hsplit, sepConj_assoc] at h
  obtain ⟨v0, h⟩ := elim_memRegion_8 h
  have h' : m ⊨ memRegion (a + 8#64) 8 ∗ ((a ↦₆₄ v0) ∗ R) := by
    refine Satisfies.mono (Entails.of_eq ?_) h
    ac_rfl
  obtain ⟨v1, h''⟩ := elim_memRegion_8 h'
  refine ⟨v0, v1, ?_⟩
  refine Satisfies.mono (Entails.of_eq ?_) h''
  ac_rfl

theorem cells_4_to_memRegion_32 (a : BitVec 64) (v0 v1 v2 v3 : BitVec 64) :
    ((a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3)) ⊢
      memRegion a 32 := by
  have hsplit := memRegion_split a 16 16 (by decide)
  rw [show (16 + 16 : Nat) = 32 from rfl] at hsplit
  rw [hsplit]
  have h0 := cells_2_to_memRegion_16 a v0 v1
  have h1 := cells_2_to_memRegion_16 (a + 16#64) v2 v3
  have h16_8 := add_assoc_const a 16#64 8#64 24#64
  rw [h16_8] at h1
  refine Entails.trans (Entails.of_eq ?_) (sepConj_mono h0 h1)
  ac_rfl

theorem elim_memRegion_32 {m : Memory} {a : BitVec 64} {R : SepProp}
    (h : m ⊨ memRegion a 32 ∗ R) :
    ∃ v0 v1 v2 v3 : BitVec 64,
      m ⊨ ((a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3)) ∗ R := by
  have hsplit := memRegion_split a 16 16 (by decide)
  rw [show (16 + 16 : Nat) = 32 from rfl] at hsplit
  rw [hsplit, sepConj_assoc] at h
  obtain ⟨v0, v1, h⟩ := elim_memRegion_16 h
  have h' : m ⊨ memRegion (a + 16#64) 16 ∗ (((a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1)) ∗ R) := by
    refine Satisfies.mono (Entails.of_eq ?_) h
    ac_rfl
  obtain ⟨v2, v3, h''⟩ := elim_memRegion_16 h'
  have h16_8 := add_assoc_const a 16#64 8#64 24#64
  rw [h16_8] at h''
  refine ⟨v0, v1, v2, v3, ?_⟩
  refine Satisfies.mono (Entails.of_eq ?_) h''
  ac_rfl

theorem elim_memRegion_96 {m : Memory} {a : BitVec 64} {R : SepProp}
    (h : m ⊨ memRegion a 96 ∗ R) :
    ∃ v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : BitVec 64,
      m ⊨ ((a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3) ∗
           ((a + 32#64) ↦₆₄ v4) ∗ ((a + 40#64) ↦₆₄ v5) ∗ ((a + 48#64) ↦₆₄ v6) ∗
             ((a + 56#64) ↦₆₄ v7) ∗
           ((a + 64#64) ↦₆₄ v8) ∗ ((a + 72#64) ↦₆₄ v9) ∗ ((a + 80#64) ↦₆₄ v10) ∗
             ((a + 88#64) ↦₆₄ v11)) ∗ R := by
  have hsplit96 := memRegion_split a 32 64 (by decide)
  rw [show (32 + 64 : Nat) = 96 from rfl] at hsplit96
  have hsplit64 := memRegion_split (a + 32#64) 32 32 (by decide)
  rw [show (32 + 32 : Nat) = 64 from rfl] at hsplit64
  rw [hsplit96, hsplit64, sepConj_assoc, sepConj_assoc] at h
  obtain ⟨v0, v1, v2, v3, h⟩ := elim_memRegion_32 h
  have h1 : m ⊨ memRegion (a + 32#64) 32 ∗
      (memRegion (a + 32#64 + BitVec.ofNat 64 32) 32 ∗
       ((a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3)) ∗ R) := by
    refine Satisfies.mono (Entails.of_eq ?_) h
    ac_rfl
  obtain ⟨v4, v5, v6, v7, h1⟩ := elim_memRegion_32 h1
  have h32_32 := add_assoc_const a 32#64 (BitVec.ofNat 64 32) 64#64
  rw [h32_32] at h1
  have h2 : m ⊨ memRegion (a + 64#64) 32 ∗
      (((a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3)) ∗
       (((a + 32#64) ↦₆₄ v4) ∗ ((a + 32#64 + 8#64) ↦₆₄ v5) ∗ ((a + 32#64 + 16#64) ↦₆₄ v6) ∗
         ((a + 32#64 + 24#64) ↦₆₄ v7)) ∗ R) := by
    refine Satisfies.mono (Entails.of_eq ?_) h1
    ac_rfl
  obtain ⟨v8, v9, v10, v11, h2⟩ := elim_memRegion_32 h2
  refine ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, ?_⟩
  have h32_8 := add_assoc_const a 32#64 8#64 40#64
  have h32_16 := add_assoc_const a 32#64 16#64 48#64
  have h32_24 := add_assoc_const a 32#64 24#64 56#64
  have h64_8 := add_assoc_const a 64#64 8#64 72#64
  have h64_16 := add_assoc_const a 64#64 16#64 80#64
  have h64_24 := add_assoc_const a 64#64 24#64 88#64
  rw [h32_8, h32_16, h32_24, h64_8, h64_16, h64_24] at h2
  refine Satisfies.mono (Entails.of_eq ?_) h2
  ac_rfl

theorem cells_12_to_memRegion_96 (a : BitVec 64)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : BitVec 64) :
    ((a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3) ∗
     ((a + 32#64) ↦₆₄ v4) ∗ ((a + 40#64) ↦₆₄ v5) ∗ ((a + 48#64) ↦₆₄ v6) ∗ ((a + 56#64) ↦₆₄ v7) ∗
     ((a + 64#64) ↦₆₄ v8) ∗ ((a + 72#64) ↦₆₄ v9) ∗ ((a + 80#64) ↦₆₄ v10) ∗ ((a + 88#64) ↦₆₄ v11)) ⊢
      memRegion a 96 := by
  have hsplit96 := memRegion_split a 32 64 (by decide)
  rw [show (32 + 64 : Nat) = 96 from rfl] at hsplit96
  have hsplit64 := memRegion_split (a + 32#64) 32 32 (by decide)
  rw [show (32 + 32 : Nat) = 64 from rfl] at hsplit64
  rw [hsplit96, hsplit64]
  have h32_8 := add_assoc_const a 32#64 8#64 40#64
  have h32_16 := add_assoc_const a 32#64 16#64 48#64
  have h32_24 := add_assoc_const a 32#64 24#64 56#64
  have h32_32 := add_assoc_const a 32#64 (BitVec.ofNat 64 32) 64#64
  have h64_8 := add_assoc_const a 64#64 8#64 72#64
  have h64_16 := add_assoc_const a 64#64 16#64 80#64
  have h64_24 := add_assoc_const a 64#64 24#64 88#64
  rw [h32_32]
  have h0 := cells_4_to_memRegion_32 a v0 v1 v2 v3
  have h1 := cells_4_to_memRegion_32 (a + 32#64) v4 v5 v6 v7
  have h2 := cells_4_to_memRegion_32 (a + 64#64) v8 v9 v10 v11
  rw [h32_8, h32_16, h32_24] at h1
  rw [h64_8, h64_16, h64_24] at h2
  refine Entails.trans (Entails.of_eq ?_) (sepConj_mono h0 (sepConj_mono h1 h2))
  ac_rfl

theorem elim_memRegion_104 {m : Memory} {a : BitVec 64} {R : SepProp}
    (h : m ⊨ memRegion a 104 ∗ R) :
    ∃ v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 : BitVec 64,
      m ⊨ ((a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3) ∗
           ((a + 32#64) ↦₆₄ v4) ∗ ((a + 40#64) ↦₆₄ v5) ∗ ((a + 48#64) ↦₆₄ v6) ∗
             ((a + 56#64) ↦₆₄ v7) ∗
           ((a + 64#64) ↦₆₄ v8) ∗ ((a + 72#64) ↦₆₄ v9) ∗ ((a + 80#64) ↦₆₄ v10) ∗
             ((a + 88#64) ↦₆₄ v11) ∗
           ((a + 96#64) ↦₆₄ v12)) ∗ R := by
  have hsplit := memRegion_split a 96 8 (by decide)
  rw [show (96 + 8 : Nat) = 104 from rfl] at hsplit
  rw [hsplit, sepConj_assoc] at h
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, h⟩ := elim_memRegion_96 h
  have h1 : m ⊨ memRegion (a + 96#64) 8 ∗
      (((a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3) ∗
        ((a + 32#64) ↦₆₄ v4) ∗ ((a + 40#64) ↦₆₄ v5) ∗ ((a + 48#64) ↦₆₄ v6) ∗ ((a + 56#64) ↦₆₄ v7) ∗
        ((a + 64#64) ↦₆₄ v8) ∗ ((a + 72#64) ↦₆₄ v9) ∗ ((a + 80#64) ↦₆₄ v10) ∗
          ((a + 88#64) ↦₆₄ v11)) ∗ R) := by
    refine Satisfies.mono (Entails.of_eq ?_) h
    ac_rfl
  obtain ⟨v12, h1⟩ := elim_memRegion_8 h1
  refine ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, ?_⟩
  refine Satisfies.mono (Entails.of_eq ?_) h1
  ac_rfl

def evictList {α : Type} (xs : List α) : List α :=
  xs.drop (xs.length - maxReceiverChains)

theorem evictList_cons_of_ge_six {α : Type} (x : α) (xs : List α) (h : 6 ≤ (x :: xs).length) :
    evictList (x :: xs) = evictList xs := by
  unfold evictList
  simp only [List.length_cons] at h ⊢
  have hsub : xs.length + 1 - maxReceiverChains = (xs.length - maxReceiverChains) + 1 := by
    unfold maxReceiverChains at *; omega
  rw [hsub, List.drop_succ_cons]

theorem evictList_of_le_five {α : Type} (xs : List α) (h : xs.length ≤ 5) :
    evictList xs = xs := by
  unfold evictList
  have hsub : xs.length - maxReceiverChains = 0 := by
    unfold maxReceiverChains; omega
  rw [hsub, List.drop_zero]

theorem evictList_length_le_five {α : Type} (xs : List α) :
    (evictList xs).length ≤ 5 := by
  unfold evictList maxReceiverChains
  rw [List.length_drop]
  omega

theorem drop_zip_eq {α β : Type} :
    ∀ (k : Nat) (xs : List α) (ys : List β),
      (xs.drop k).zip (ys.drop k) = (xs.zip ys).drop k
  | 0, _, _ => rfl
  | _ + 1, [], _ => by simp
  | _ + 1, _ :: _, [] => by simp
  | k + 1, _ :: xs, _ :: ys => drop_zip_eq k xs ys

theorem evictList_zip {α β : Type} (xs : List α) (ys : List β) (h : xs.length = ys.length) :
    (evictList xs).zip (evictList ys) = evictList (xs.zip ys) := by
  unfold evictList
  rw [List.length_zip, h, Nat.min_self, drop_zip_eq]

def evictActive (A : RustAlloc) (sp chainsCap chainsPtr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain)) : SepProp :=
  ((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
  ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
  vecBuf A 104 8 (chainAt A) chainsCap chainsPtr gcs ∗
  memRegion (sp + 0x190#64) 104 ∗
  memRegion (sp + 0x500#64) 96 ∗
  A.pool ∗
  stackAt sp dropChainStack

theorem memmove_len_toNat {n : Nat} (hn : n < 2 ^ 32) :
    (0xffffffffffffff98#64 + BitVec.ofNat 64 (n + 1) * 104#64).toNat = n * 104 := by
  have h1 : 0xffffffffffffff98#64 + BitVec.ofNat 64 (n + 1) * 104#64 =
      BitVec.ofNat 64 (n * 104) := by
    rw [BitVec.ofNat_add, BitVec.ofNat_mul]
    bv_omega
  rw [h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem sub_one_ofNat_succ (n : Nat) :
    BitVec.ofNat 64 (n + 1) - 1#64 = BitVec.ofNat 64 n := by
  rw [BitVec.ofNat_add]
  bv_omega

end CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegBH

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Defs
import ProofLib.VCGen

/-!
# Position-Independence and Raw-Byte Move Lemmas

Proves the 128-bit quadword chunk equivalences, inline-byte / detached-heap decompositions, and
raw-byte move corollaries for `chainAt`, `optSenderChainAt`, and `sessionStateAt` declared in
`RawByteMove/Defs.lean`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.RawByteMove

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr

/-! ## General `SepProp` equality and existential helpers -/

theorem sepProp_eq_of_entails {P Q : SepProp} (hPQ : P ⊢ Q) (hQP : Q ⊢ P) : P = Q :=
  Entails.antisymm hPQ hQP

theorem sepExists_congr {α : Sort u} {P Q : α → SepProp} (h : ∀ x, P x = Q x) :
    (∃∗ x, P x) = (∃∗ x, Q x) := by
  congr 1
  funext x
  exact h x

theorem sepExists_comm {α : Sort u} {β : Sort v} (P : α → β → SepProp) :
    (∃∗ x, ∃∗ y, P x y) = (∃∗ y, ∃∗ x, P x y) := by
  apply sepProp_eq_of_entails
  · apply Entails.sepExists_elim; intro x
    apply Entails.sepExists_elim; intro y
    exact Entails.sepExists_right y (Entails.sepExists_right x (Entails.refl _))
  · apply Entails.sepExists_elim; intro y
    apply Entails.sepExists_elim; intro x
    exact Entails.sepExists_right x (Entails.sepExists_right y (Entails.refl _))

theorem pure_and_eq_sepConj (φ ψ : Prop) : (⌜φ ∧ ψ⌝ : SepProp) = (⌜φ⌝ ∗ ⌜ψ⌝) :=
  (pure_sepConj_pure φ ψ).symm

/-! ## 128-bit quadword (`↦₁₂₈`) and 104-byte chunk bridges -/

@[scoped simp]
theorem unpack128_length (v : BitVec 128) : (unpack128 v).length = 16 := by
  simp [unpack128]

theorem unpack128_append64 (lo hi : BitVec 64) :
    unpack128 (hi ++ lo) = unpack64 lo ++ unpack64 hi := by
  unfold unpack128
  have hlo : (hi ++ lo).extractLsb' 0 64 = lo := by bv_kernel
  have hhi : (hi ++ lo).extractLsb' 64 64 = hi := by bv_kernel
  rw [hlo, hhi]

/-- `a ↦₁₂₈ v` equals the 16-byte slice `a ↦ₛ unpack128 v`. -/
theorem pointsTo128_eq_pointsToBytes (a : BitVec 64) (v : BitVec 128) :
    (a ↦₁₂₈ v) = (a ↦ₛ unpack128 v) := by
  unfold pointsTo128 unpack128
  rw [pointsToBytes_append, unpack64_length,
      ← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes]

/-- Combine two adjacent 64-bit cells into one 128-bit cell. -/
protected theorem pointsTo64_pair (a : BitVec 64) (lo hi : BitVec 64) :
    ((a ↦₆₄ lo) ∗ ((a + 8#64) ↦₆₄ hi)) = (a ↦₁₂₈ (hi ++ lo)) := by
  rw [pointsTo64_eq_pointsToBytes, pointsTo64_eq_pointsToBytes,
      pointsTo128_eq_pointsToBytes, unpack128_append64,
      pointsToBytes_append, unpack64_length]

/-- Any 16-byte list `bs` is `unpack128 q` for some `q : BitVec 128`. -/
theorem exists_unpack128_of_length_16 {bs : List (BitVec 8)} (h : bs.length = 16) :
    ∃ q : BitVec 128,
      bs = unpack128 q ∧
      ∀ a : BitVec 64, (a ↦ₛ bs) = (a ↦₁₂₈ q) := by
  obtain ⟨w0, w1, hbs, hp⟩ := exists_unpack64_of_length_16 h
  refine ⟨w1 ++ w0, ?_, fun a => ?_⟩
  · rw [hbs, unpack128_append64]
  · rw [hp a, pointsTo64_pair]

/-- A 16-byte `memRegion` is an existential 128-bit cell `∃∗ q, a ↦₁₂₈ q`. -/
theorem memRegion_16_eq_exists_pointsTo128 (a : BitVec 64) :
    memRegion a 16 = ∃∗ q : BitVec 128, a ↦₁₂₈ q := by
  rw [memRegion_eq_exists_bytes a 16 (by decide)]
  apply sepProp_eq_of_entails
  · apply Entails.sepExists_elim; intro bs
    apply Entails.pure_left; intro h16
    obtain ⟨q, _, hq⟩ := exists_unpack128_of_length_16 h16
    rw [hq a]
    exact Entails.sepExists_right q (Entails.refl _)
  · apply Entails.sepExists_elim; intro q
    rw [pointsTo128_eq_pointsToBytes]
    exact Entails.sepExists_right (unpack128 q)
      (Entails.pure_right (unpack128_length q) (Entails.refl _))

@[scoped simp]
theorem bytes104OfW6Q_length (w0 : BitVec 64) (q0 q1 q2 q3 q4 q5 : BitVec 128) :
    (bytes104OfW6Q w0 q0 q1 q2 q3 q4 q5).length = 104 := by
  simp [bytes104OfW6Q]

@[scoped simp]
theorem bytes96Of6Q_length (q0 q1 q2 q3 q4 q5 : BitVec 128) :
    (bytes96Of6Q q0 q1 q2 q3 q4 q5).length = 96 := by
  simp [bytes96Of6Q]

/-- `chunks96_6QAt` equals the 96-byte contiguous slice `base ↦ₛ bytes96Of6Q q0..q5`. -/
theorem chunks96_6QAt_eq_pointsToBytes (base : BitVec 64) (q0 q1 q2 q3 q4 q5 : BitVec 128) :
    Chunks96_6QStmt base q0 q1 q2 q3 q4 q5 := by
  unfold Chunks96_6QStmt chunks96_6QAt bytes96Of6Q
  simp only [List.append_assoc, pointsToBytes_append, unpack128_length,
    ← pointsTo128_eq_pointsToBytes]
  have h10 : base + BitVec.ofNat 64 16 = base + 16#64 := rfl
  have h20 : base + 16#64 + BitVec.ofNat 64 16 = base + 32#64 := by bv_arith
  have h30 : base + 32#64 + BitVec.ofNat 64 16 = base + 48#64 := by bv_arith
  have h40 : base + 48#64 + BitVec.ofNat 64 16 = base + 64#64 := by bv_arith
  have h50 : base + 64#64 + BitVec.ofNat 64 16 = base + 80#64 := by bv_arith
  rw [h10, h20, h30, h40, h50]

/-- `chunks104W6QAt a` splits into `(a ↦₆₄ w0)` at `+0x00` and `chunks96_6QAt (a + 0x8#64)`. -/
theorem chunks104W6QAt_eq_word_sep_chunks96 (a : BitVec 64) (w0 : BitVec 64)
    (q0 q1 q2 q3 q4 q5 : BitVec 128) :
    chunks104W6QAt a w0 q0 q1 q2 q3 q4 q5 =
      (a ↦₆₄ w0) ∗ chunks96_6QAt (a + 0x8#64) q0 q1 q2 q3 q4 q5 := by
  unfold chunks104W6QAt chunks96_6QAt
  have h18 : a + 0x8#64 + 0x10#64 = a + 0x18#64 := by bv_arith
  have h28 : a + 0x8#64 + 0x20#64 = a + 0x28#64 := by bv_arith
  have h38 : a + 0x8#64 + 0x30#64 = a + 0x38#64 := by bv_arith
  have h48 : a + 0x8#64 + 0x40#64 = a + 0x48#64 := by bv_arith
  have h58 : a + 0x8#64 + 0x50#64 = a + 0x58#64 := by bv_arith
  rw [h18, h28, h38, h48, h58]

/-- `chunks104W6QAt a w0 q0..q5` equals `a ↦ₛ bytes104OfW6Q w0 q0..q5`. -/
theorem chunks104W6QAt_eq_pointsToBytes (a : BitVec 64) (w0 : BitVec 64)
    (q0 q1 q2 q3 q4 q5 : BitVec 128) :
    Chunks104W6QStmt a w0 q0 q1 q2 q3 q4 q5 := by
  unfold Chunks104W6QStmt
  rw [chunks104W6QAt_eq_word_sep_chunks96, chunks96_6QAt_eq_pointsToBytes,
      pointsTo64_eq_pointsToBytes]
  unfold bytes104OfW6Q bytes96Of6Q
  simp only [List.append_assoc]
  have h8 : a + 0x8#64 = a + BitVec.ofNat 64 (unpack64 w0).length := rfl
  rw [h8, ← pointsToBytes_append]

/-- Any 96-byte list `bs` decomposes into six 128-bit quadwords `q0..q5`. -/
theorem exists_chunks96_of_length_96 {bs : List (BitVec 8)} (h : bs.length = 96) :
    ∃ q0 q1 q2 q3 q4 q5 : BitVec 128,
      bs = bytes96Of6Q q0 q1 q2 q3 q4 q5 ∧
      ∀ base : BitVec 64, (base ↦ₛ bs) = chunks96_6QAt base q0 q1 q2 q3 q4 q5 := by
  have h0 : (bs.take 16).length = 16 := by simp [h]
  have h1 : ((bs.drop 16).take 16).length = 16 := by simp [h]
  have h2 : ((bs.drop 32).take 16).length = 16 := by simp [h]
  have h3 : ((bs.drop 48).take 16).length = 16 := by simp [h]
  have h4 : ((bs.drop 64).take 16).length = 16 := by simp [h]
  have h5 : (bs.drop 80).length = 16 := by simp [h]
  obtain ⟨q0, hq0, _⟩ := exists_unpack128_of_length_16 h0
  obtain ⟨q1, hq1, _⟩ := exists_unpack128_of_length_16 h1
  obtain ⟨q2, hq2, _⟩ := exists_unpack128_of_length_16 h2
  obtain ⟨q3, hq3, _⟩ := exists_unpack128_of_length_16 h3
  obtain ⟨q4, hq4, _⟩ := exists_unpack128_of_length_16 h4
  obtain ⟨q5, hq5, _⟩ := exists_unpack128_of_length_16 h5
  have hbs : bs = bytes96Of6Q q0 q1 q2 q3 q4 q5 := by
    unfold bytes96Of6Q
    rw [← hq0, ← hq1, ← hq2, ← hq3, ← hq4, ← hq5]
    simp only [List.append_assoc]
    have s4 : (bs.drop 64).take 16 ++ bs.drop 80 = bs.drop 64 := by
      have := List.take_append_drop 16 (bs.drop 64)
      rwa [List.drop_drop] at this
    have s3 : (bs.drop 48).take 16 ++ bs.drop 64 = bs.drop 48 := by
      have := List.take_append_drop 16 (bs.drop 48)
      rwa [List.drop_drop] at this
    have s2 : (bs.drop 32).take 16 ++ bs.drop 48 = bs.drop 32 := by
      have := List.take_append_drop 16 (bs.drop 32)
      rwa [List.drop_drop] at this
    have s1 : (bs.drop 16).take 16 ++ bs.drop 32 = bs.drop 16 := by
      have := List.take_append_drop 16 (bs.drop 16)
      rwa [List.drop_drop] at this
    rw [s4, s3, s2, s1, List.take_append_drop]
  refine ⟨q0, q1, q2, q3, q4, q5, hbs, fun base => ?_⟩
  rw [chunks96_6QAt_eq_pointsToBytes, ← hbs]

theorem split96_6Q (bs : List (BitVec 8)) : Split96_6QStmt bs := by
  intro h
  obtain ⟨q0, q1, q2, q3, q4, q5, hbs, _⟩ := exists_chunks96_of_length_96 h
  exact ⟨q0, q1, q2, q3, q4, q5, hbs⟩

/-- Any 104-byte list `bs` decomposes as `bytes104OfW6Q w0 q0 q1 q2 q3 q4 q5`. -/
theorem exists_bytes104OfW6Q {bs : List (BitVec 8)} (h : bs.length = 104) :
    ∃ (w0 : BitVec 64) (q0 q1 q2 q3 q4 q5 : BitVec 128),
      bs = bytes104OfW6Q w0 q0 q1 q2 q3 q4 q5 ∧
      ∀ a : BitVec 64, (a ↦ₛ bs) = chunks104W6QAt a w0 q0 q1 q2 q3 q4 q5 := by
  have hw0 : (bs.take 8).length = 8 := by simp [h]
  have hrest : (bs.drop 8).length = 96 := by simp [h]
  obtain ⟨w0, hw0_eq⟩ := exists_unpack64_of_length_8 hw0
  obtain ⟨q0, q1, q2, q3, q4, q5, hq_eq, _⟩ := exists_chunks96_of_length_96 hrest
  have hbs : bs = bytes104OfW6Q w0 q0 q1 q2 q3 q4 q5 := by
    unfold bytes104OfW6Q
    unfold bytes96Of6Q at hq_eq
    simp only [List.append_assoc] at hq_eq ⊢
    rw [← hw0_eq, ← hq_eq, List.take_append_drop]
  refine ⟨w0, q0, q1, q2, q3, q4, q5, hbs, fun a => ?_⟩
  rw [chunks104W6QAt_eq_pointsToBytes, ← hbs]

theorem split104W6Q (bs : List (BitVec 8)) : Split104W6QStmt bs := by
  intro h
  obtain ⟨w0, q0, q1, q2, q3, q4, q5, hbs, _⟩ := exists_bytes104OfW6Q h
  exact ⟨w0, q0, q1, q2, q3, q4, q5, hbs⟩

/-- A 96-byte `memRegion` is an existential `chunks96_6QAt`. -/
theorem memRegion_96_eq_exists_chunks96_6QAt (base : BitVec 64) :
    memRegion base 96 =
      ∃∗ q0 : BitVec 128, ∃∗ q1 : BitVec 128, ∃∗ q2 : BitVec 128,
      ∃∗ q3 : BitVec 128, ∃∗ q4 : BitVec 128, ∃∗ q5 : BitVec 128,
        chunks96_6QAt base q0 q1 q2 q3 q4 q5 := by
  rw [memRegion_eq_exists_bytes base 96 (by decide)]
  apply sepProp_eq_of_entails
  · apply Entails.sepExists_elim; intro bs
    apply Entails.pure_left; intro h96
    obtain ⟨q0, q1, q2, q3, q4, q5, _, hchunks⟩ := exists_chunks96_of_length_96 h96
    rw [hchunks base]
    exact Entails.sepExists_right q0 (Entails.sepExists_right q1
      (Entails.sepExists_right q2 (Entails.sepExists_right q3
        (Entails.sepExists_right q4 (Entails.sepExists_right q5 (Entails.refl _))))))
  · apply Entails.sepExists_elim; intro q0
    apply Entails.sepExists_elim; intro q1
    apply Entails.sepExists_elim; intro q2
    apply Entails.sepExists_elim; intro q3
    apply Entails.sepExists_elim; intro q4
    apply Entails.sepExists_elim; intro q5
    rw [chunks96_6QAt_eq_pointsToBytes]
    exact Entails.sepExists_right _
      (Entails.pure_right (bytes96Of6Q_length q0 q1 q2 q3 q4 q5) (Entails.refl _))

@[scoped simp]
theorem bytes104Of6QW_length (q0 q1 q2 q3 q4 q5 : BitVec 128) (w6 : BitVec 64) :
    (bytes104Of6QW q0 q1 q2 q3 q4 q5 w6).length = 104 := by
  simp [bytes104Of6QW]

/-- `chunks104_6QWAt a q0..q5 w6` equals `a ↦ₛ bytes104Of6QW q0..q5 w6`. -/
theorem chunks104_6QWAt_eq_pointsToBytes (a : BitVec 64)
    (q0 q1 q2 q3 q4 q5 : BitVec 128) (w6 : BitVec 64) :
    Chunks104_6QWStmt a q0 q1 q2 q3 q4 q5 w6 := by
  unfold Chunks104_6QWStmt chunks104_6QWAt bytes104Of6QW
  simp only [List.append_assoc, pointsToBytes_append, unpack128_length,
    ← pointsTo128_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes]
  have h10 : a + BitVec.ofNat 64 16 = a + 0x10#64 := rfl
  have h20 : a + 0x10#64 + BitVec.ofNat 64 16 = a + 0x20#64 := by bv_arith
  have h30 : a + 0x20#64 + BitVec.ofNat 64 16 = a + 0x30#64 := by bv_arith
  have h40 : a + 0x30#64 + BitVec.ofNat 64 16 = a + 0x40#64 := by bv_arith
  have h50 : a + 0x40#64 + BitVec.ofNat 64 16 = a + 0x50#64 := by bv_arith
  have h60 : a + 0x50#64 + BitVec.ofNat 64 16 = a + 0x60#64 := by bv_arith
  rw [h10, h20, h30, h40, h50, h60]

/-- Any 104-byte list `bs` decomposes as `bytes104Of6QW q0 q1 q2 q3 q4 q5 w6`. -/
theorem exists_bytes104Of6QW {bs : List (BitVec 8)} (h : bs.length = 104) :
    ∃ (q0 q1 q2 q3 q4 q5 : BitVec 128) (w6 : BitVec 64),
      bs = bytes104Of6QW q0 q1 q2 q3 q4 q5 w6 ∧
      ∀ a : BitVec 64, (a ↦ₛ bs) = chunks104_6QWAt a q0 q1 q2 q3 q4 q5 w6 := by
  have h96 : (bs.take 96).length = 96 := by simp [h]
  have h8 : (bs.drop 96).length = 8 := by simp [h]
  obtain ⟨q0, q1, q2, q3, q4, q5, hq_eq, _⟩ := exists_chunks96_of_length_96 h96
  obtain ⟨w6, hw6_eq⟩ := exists_unpack64_of_length_8 h8
  have hbs : bs = bytes104Of6QW q0 q1 q2 q3 q4 q5 w6 := by
    unfold bytes104Of6QW
    unfold bytes96Of6Q at hq_eq
    rw [← hq_eq, ← hw6_eq, List.take_append_drop]
  refine ⟨q0, q1, q2, q3, q4, q5, w6, hbs, fun a => ?_⟩
  rw [chunks104_6QWAt_eq_pointsToBytes, ← hbs]

theorem split104_6QW (bs : List (BitVec 8)) : Split104_6QWStmt bs := by
  intro h
  obtain ⟨q0, q1, q2, q3, q4, q5, w6, hbs, _⟩ := exists_bytes104Of6QW h
  exact ⟨q0, q1, q2, q3, q4, q5, w6, hbs⟩

/-! ## `vecGhostAt`, `vecAt`, `optChainKeyAt`, and `optTailVecAt` decompositions -/

@[scoped simp]
theorem vecGhostHeaderBytes_length (g : VecGhost) :
    (vecGhostHeaderBytes g).length = 24 := by
  simp [vecGhostHeaderBytes, vecHeaderBytes]

/-- `vecGhostAt A g a` decomposes into `(a ↦ₛ vecGhostHeaderBytes g) ∗ vecGhostHeap A g`. -/
theorem vecGhostAt_eq_bytes_sep_heap (A : RustAlloc) (g : VecGhost) (a : BitVec 64) :
    vecGhostAt A g a = (a ↦ₛ vecGhostHeaderBytes g) ∗ vecGhostHeap A g := by
  unfold vecGhostAt vecGhostHeaderBytes vecGhostHeap
  rw [vecU8At_eq_header_sep_buf, vecHeader_eq_pointsToBytes]

/-- `vecU8At A a cap ptr bs` decomposes into `(a ↦ₛ vecHeaderBytes cap ptr (BitVec.ofNat 64 bs.length)) ∗ vecU8Buf A cap ptr bs`. -/
theorem vecU8At_eq_bytes_sep_buf (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A a cap ptr bs =
      (a ↦ₛ vecHeaderBytes cap ptr (BitVec.ofNat 64 bs.length)) ∗ vecU8Buf A cap ptr bs := by
  rw [vecU8At_eq_header_sep_buf, vecHeader_eq_pointsToBytes]

/-- `vecAt` decomposes into its 24-byte header slice `(v ↦ₛ vecHeaderBytes cap ptr (BitVec.ofNat 64 xs.length))`
and its address-independent `vecBuf`. -/
theorem vecAt_eq_bytes_sep_buf {α : Type} (A : RustAlloc) (stride align : Nat)
    (elem : α → BitVec 64 → SepProp) (v cap ptr : BitVec 64) (xs : List α) :
    vecAt A stride align elem v cap ptr xs =
      (v ↦ₛ vecHeaderBytes cap ptr (BitVec.ofNat 64 xs.length)) ∗
        vecBuf A stride align elem cap ptr xs := by
  unfold vecAt
  rw [vecHeader_eq_pointsToBytes]

theorem OptChainKeyInline.length_eq {pin : VecPin} {o : Option ChainKey} {bs : List (BitVec 8)}
    (h : OptChainKeyInline pin o bs) : bs.length = 32 := by
  cases o with
  | none =>
    rcases h with ⟨pad, hpad, rfl⟩
    simp [hpad]
  | some ck =>
    rcases h with ⟨pad, hpad, rfl⟩
    simp [vecHeaderBytes, hpad]

/-- `optChainKeyAt A pin o a` decomposes into 32 inline bytes `a ↦ₛ bs` (`OptChainKeyInline pin o bs`)
and `optChainKeyHeap A pin o`. -/
theorem optChainKeyAt_eq_inline_sep_heap (A : RustAlloc) (pin : VecPin) (o : Option ChainKey)
    (a : BitVec 64) :
    optChainKeyAt A pin o a =
      ∃∗ bs : List (BitVec 8),
        ⌜bs.length = 32 ∧ OptChainKeyInline pin o bs⌝ ∗ (a ↦ₛ bs) ∗ optChainKeyHeap A pin o := by
  apply sepProp_eq_of_entails
  · cases o with
    | none =>
      dsimp only [optChainKeyAt, optChainKeyHeap]
      rw [pointsTo64_eq_pointsToBytes, memRegion_eq_exists_bytes (a + 8#64) 24 (by decide),
          sepExists_sepConj_right]
      apply Entails.sepExists_elim; intro pad
      rw [sepConj_pure_left_comm]
      apply Entails.pure_left; intro hpad
      have h8 : a + 8#64 = a + BitVec.ofNat 64 (unpack64 optChainKeyNone).length := rfl
      rw [h8, ← pointsToBytes_append]
      have hinl : OptChainKeyInline pin none (unpack64 optChainKeyNone ++ pad) := ⟨pad, hpad, rfl⟩
      refine Entails.sepExists_right (unpack64 optChainKeyNone ++ pad) ?_
      rw [sepConj_emp]
      exact Entails.pure_right ⟨hinl.length_eq, hinl⟩ (Entails.refl _)
    | some ck =>
      dsimp only [optChainKeyAt, optChainKeyHeap]
      rw [vecU8At_eq_bytes_sep_buf, pointsTo32_eq_pointsToBytes,
          memRegion_eq_exists_bytes (a + 28#64) 4 (by decide)]
      have hlen32 : BitVec.ofNat 64 (keyToBytes32 ck.key).length = 32#64 := by
        simp [keyToBytes32]
      rw [hlen32]
      have hpull :
          (((a ↦ₛ vecHeaderBytes pin.cap pin.ptr 32#64) ∗
              vecU8Buf A pin.cap pin.ptr (keyToBytes32 ck.key)) ∗
            ((a + 24#64) ↦ₛ unpack32 ck.index) ∗
            (∃∗ bs, ⌜bs.length = 4⌝ ∗ ((a + 28#64) ↦ₛ bs))) =
          ((∃∗ bs, ⌜bs.length = 4⌝ ∗
              ((a ↦ₛ vecHeaderBytes pin.cap pin.ptr 32#64) ∗
                ((a + 24#64) ↦ₛ unpack32 ck.index) ∗
                ((a + 28#64) ↦ₛ bs))) ∗
            vecU8Buf A pin.cap pin.ptr (keyToBytes32 ck.key)) := by
        simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        apply sepExists_congr; intro pad
        ac_rfl
      rw [hpull, sepExists_sepConj_left]
      apply Entails.sepExists_elim; intro pad
      rw [sepConj_assoc]
      apply Entails.pure_left; intro hpad
      have h24 : a + 24#64 = a + BitVec.ofNat 64 (vecHeaderBytes pin.cap pin.ptr 32#64).length := by
        simp [vecHeaderBytes]
      have h28 : a + 28#64 =
          a + BitVec.ofNat 64 (vecHeaderBytes pin.cap pin.ptr 32#64 ++ unpack32 ck.index).length := by
        simp [vecHeaderBytes]
      rw [← sepConj_assoc (a ↦ₛ _), h24, ← pointsToBytes_append, h28, ← pointsToBytes_append]
      set bs := vecHeaderBytes pin.cap pin.ptr 32#64 ++ unpack32 ck.index ++ pad
      have hinl : OptChainKeyInline pin (some ck) bs := ⟨pad, hpad, rfl⟩
      refine Entails.sepExists_right bs ?_
      exact Entails.pure_right ⟨hinl.length_eq, hinl⟩ (Entails.refl _)
  · apply Entails.sepExists_elim; intro bs
    apply Entails.pure_left; rintro ⟨_, hinl⟩
    cases o with
    | none =>
      rcases hinl with ⟨pad, hpad, rfl⟩
      dsimp only [optChainKeyAt, optChainKeyHeap]
      rw [sepConj_emp, pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes]
      apply sepConj_mono_right
      have h := pointsToBytes_entails_memRegion (a + 8#64) pad
      rwa [hpad] at h
    | some ck =>
      rcases hinl with ⟨pad, hpad, rfl⟩
      dsimp only [optChainKeyAt, optChainKeyHeap]
      rw [pointsToBytes_append, pointsToBytes_append]
      have hhdr_len : (vecHeaderBytes pin.cap pin.ptr 32#64).length = 24 := by
        simp [vecHeaderBytes]
      have hhdr_idx_len :
          (vecHeaderBytes pin.cap pin.ptr 32#64 ++ unpack32 ck.index).length = 28 := by
        simp [vecHeaderBytes]
      rw [hhdr_len, hhdr_idx_len, ← pointsTo32_eq_pointsToBytes, vecU8At_eq_bytes_sep_buf]
      have hlen32 : BitVec.ofNat 64 (keyToBytes32 ck.key).length = 32#64 := by
        simp [keyToBytes32]
      rw [hlen32]
      have hpull :
          ((((a ↦ₛ vecHeaderBytes pin.cap pin.ptr 32#64) ∗
              ((a + 24#64) ↦₃₂ ck.index)) ∗
              ((a + 28#64) ↦ₛ pad)) ∗
            vecU8Buf A pin.cap pin.ptr (keyToBytes32 ck.key)) =
          (((a ↦ₛ vecHeaderBytes pin.cap pin.ptr 32#64) ∗
              vecU8Buf A pin.cap pin.ptr (keyToBytes32 ck.key)) ∗
            ((a + 24#64) ↦₃₂ ck.index) ∗
            ((a + 28#64) ↦ₛ pad)) := by
        ac_rfl
      rw [hpull]
      apply sepConj_mono_right
      apply sepConj_mono_right
      have h := pointsToBytes_entails_memRegion (a + 28#64) pad
      rwa [hpad] at h

/-- Reassemble `optChainKeyAt` from its 32 inline bytes and detached heap. -/
theorem optChainKeyAt_of_bytes (A : RustAlloc) (pin : VecPin) (o : Option ChainKey)
    (a : BitVec 64) {bs : List (BitVec 8)} (h : OptChainKeyInline pin o bs) :
    ((a ↦ₛ bs) ∗ optChainKeyHeap A pin o) ⊢ optChainKeyAt A pin o a := by
  rw [optChainKeyAt_eq_inline_sep_heap]
  refine Entails.sepExists_right bs ?_
  exact Entails.pure_right ⟨h.length_eq, h⟩ (Entails.refl _)

theorem OptTailVecInline.length_eq {size : Nat} (hsize : 24 ≤ size)
    {o : Option TailVecGhost} {bs : List (BitVec 8)}
    (h : OptTailVecInline size o bs) : bs.length = size := by
  cases o with
  | none =>
    rcases h with ⟨pad, hpad, rfl⟩
    simp [hpad]
    omega
  | some g =>
    rcases h with ⟨htail, rfl⟩
    simp [htail]
    omega

/-- `optTailVecAt A size a o` decomposes into `size` inline bytes `a ↦ₛ bs`
(`OptTailVecInline size o bs`) and `optTailVecHeap A o`. -/
theorem optTailVecAt_eq_inline_sep_heap (A : RustAlloc) {size : Nat}
    (hsize : 24 ≤ size) (hbound : size - 8 ≤ 2 ^ 64)
    (a : BitVec 64) (o : Option TailVecGhost) :
    optTailVecAt A size a o =
      ∃∗ bs : List (BitVec 8),
        ⌜bs.length = size ∧ OptTailVecInline size o bs⌝ ∗ (a ↦ₛ bs) ∗ optTailVecHeap A o := by
  apply sepProp_eq_of_entails
  · cases o with
    | none =>
      dsimp only [optTailVecAt, optTailVecHeap]
      rw [pointsTo64_eq_pointsToBytes, memRegion_eq_exists_bytes (a + 8#64) (size - 8) hbound,
          sepExists_sepConj_right]
      apply Entails.sepExists_elim; intro pad
      rw [sepConj_pure_left_comm]
      apply Entails.pure_left; intro hpad
      have h8 : a + 8#64 = a + BitVec.ofNat 64 (unpack64 noneCap).length := rfl
      rw [h8, ← pointsToBytes_append]
      have hinl : OptTailVecInline size none (unpack64 noneCap ++ pad) := ⟨pad, hpad, rfl⟩
      refine Entails.sepExists_right (unpack64 noneCap ++ pad) ?_
      rw [sepConj_emp]
      exact Entails.pure_right ⟨hinl.length_eq hsize, hinl⟩ (Entails.refl _)
    | some g =>
      dsimp only [optTailVecAt, optTailVecHeap]
      apply Entails.pure_left; intro htail
      rw [vecGhostAt_eq_bytes_sep_heap]
      have hpull :
          (((a ↦ₛ vecGhostHeaderBytes g.vec) ∗ vecGhostHeap A g.vec) ∗ ((a + 24#64) ↦ₛ g.tail)) =
          (((a ↦ₛ vecGhostHeaderBytes g.vec) ∗ ((a + 24#64) ↦ₛ g.tail)) ∗ vecGhostHeap A g.vec) := by
        ac_rfl
      rw [hpull]
      have h24 : a + 24#64 = a + BitVec.ofNat 64 (vecGhostHeaderBytes g.vec).length := by
        simp [vecGhostHeaderBytes_length]
      rw [h24, ← pointsToBytes_append]
      set bs := vecGhostHeaderBytes g.vec ++ g.tail
      have hinl : OptTailVecInline size (some g) bs := ⟨htail, rfl⟩
      refine Entails.sepExists_right bs ?_
      exact Entails.pure_right ⟨hinl.length_eq hsize, hinl⟩ (Entails.refl _)
  · apply Entails.sepExists_elim; intro bs
    apply Entails.pure_left; rintro ⟨_, hinl⟩
    cases o with
    | none =>
      rcases hinl with ⟨pad, hpad, rfl⟩
      dsimp only [optTailVecAt, optTailVecHeap]
      rw [sepConj_emp, pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes]
      apply sepConj_mono_right
      have h := pointsToBytes_entails_memRegion (a + 8#64) pad
      rwa [hpad] at h
    | some g =>
      rcases hinl with ⟨htail, rfl⟩
      dsimp only [optTailVecAt, optTailVecHeap]
      apply Entails.pure_right htail
      rw [pointsToBytes_append, vecGhostHeaderBytes_length, vecGhostAt_eq_bytes_sep_heap]
      exact Entails.of_eq (by ac_rfl)

/-! ## `chainAt` (104 bytes): decomposition and move corollaries -/

@[scoped simp]
theorem chainPrefixBytes_length (gc : ChainGhost × ReceiverChain) :
    (chainPrefixBytes gc).length = 72 := by
  simp [chainPrefixBytes, vecHeaderBytes]

theorem ChainInline.length_eq {gc : ChainGhost × ReceiverChain} {bs : List (BitVec 8)}
    (h : ChainInline gc bs) : bs.length = 104 := by
  rcases h with ⟨ckBs, hck_len, _, rfl⟩
  simp [hck_len]

/-- The first 72 bytes of `chainAt` (`srk`, `priv`, `message_keys` headers) equal
`a ↦ₛ chainPrefixBytes gc`. -/
theorem pointsToBytes_chainPrefixBytes (gc : ChainGhost × ReceiverChain) (a : BitVec 64) :
    (a ↦ₛ chainPrefixBytes gc) =
      (a ↦ₛ vecGhostHeaderBytes gc.1.srk) ∗
        ((a + 24#64) ↦ₛ vecGhostHeaderBytes gc.1.priv) ∗
        ((a + 48#64) ↦ₛ
          vecHeaderBytes gc.1.mkCap gc.1.mkPtr
            (BitVec.ofNat 64 (gc.1.keys.zip gc.2.messageKeys).length)) := by
  unfold chainPrefixBytes
  rw [List.append_assoc, pointsToBytes_append, pointsToBytes_append]
  simp only [vecGhostHeaderBytes_length]
  have h24 : a + BitVec.ofNat 64 24 = a + 24#64 := rfl
  have h48 : a + 24#64 + BitVec.ofNat 64 24 = a + 48#64 := by bv_arith
  rw [h24, h48]

/-- Decomposes `protoChainAt A gc a` into 104 inline bytes (`ChainInline gc bs`) and `protoChainHeap A gc`. -/
theorem protoChainAt_eq_inline_sep_heap (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64) :
    ProtoChainAtDecompStmt A gc a := by
  unfold ProtoChainAtDecompStmt protoChainAt protoChainHeap
  rw [vecGhostAt_eq_bytes_sep_heap A gc.1.srk a,
      vecGhostAt_eq_bytes_sep_heap A gc.1.priv (a + 24#64),
      vecAt_eq_bytes_sep_buf A 104 8 (messageKeyAt A) (a + 48#64),
      optChainKeyAt_eq_inline_sep_heap A gc.1.ck gc.2.chainKey (a + 72#64)]
  apply sepProp_eq_of_entails
  · have hpull :
        (⌜ProtoChainPure gc⌝ ∗
          ((a ↦ₛ vecGhostHeaderBytes gc.1.srk) ∗ vecGhostHeap A gc.1.srk) ∗
          (((a + 24#64) ↦ₛ vecGhostHeaderBytes gc.1.priv) ∗ vecGhostHeap A gc.1.priv) ∗
          (((a + 48#64) ↦ₛ
              vecHeaderBytes gc.1.mkCap gc.1.mkPtr
                (BitVec.ofNat 64 (gc.1.keys.zip gc.2.messageKeys).length)) ∗
            vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr
              (gc.1.keys.zip gc.2.messageKeys)) ∗
          (∃∗ bs, ⌜bs.length = 32 ∧ OptChainKeyInline gc.1.ck gc.2.chainKey bs⌝ ∗
            ((a + 72#64) ↦ₛ bs) ∗ optChainKeyHeap A gc.1.ck gc.2.chainKey)) =
        ((∃∗ bs, ⌜bs.length = 32 ∧ OptChainKeyInline gc.1.ck gc.2.chainKey bs⌝ ∗
            (((a ↦ₛ vecGhostHeaderBytes gc.1.srk) ∗
              ((a + 24#64) ↦ₛ vecGhostHeaderBytes gc.1.priv) ∗
              ((a + 48#64) ↦ₛ
                vecHeaderBytes gc.1.mkCap gc.1.mkPtr
                  (BitVec.ofNat 64 (gc.1.keys.zip gc.2.messageKeys).length))) ∗
             ((a + 72#64) ↦ₛ bs))) ∗
          (⌜ProtoChainPure gc⌝ ∗
            vecGhostHeap A gc.1.srk ∗
            vecGhostHeap A gc.1.priv ∗
            vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr
              (gc.1.keys.zip gc.2.messageKeys) ∗
            optChainKeyHeap A gc.1.ck gc.2.chainKey)) := by
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply sepExists_congr; intro ckBs
      ac_rfl
    rw [hpull, sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro ckBs
    rw [← pointsToBytes_chainPrefixBytes gc a, sepConj_assoc]
    apply Entails.pure_left; rintro ⟨hck_len, hck_inl⟩
    have h72 : a + 72#64 = a + BitVec.ofNat 64 (chainPrefixBytes gc).length := by
      rw [chainPrefixBytes_length]
    rw [h72, ← pointsToBytes_append]
    set bs := chainPrefixBytes gc ++ ckBs
    have hinl : ChainInline gc bs := ⟨ckBs, hck_len, hck_inl, rfl⟩
    refine Entails.sepExists_right bs ?_
    exact Entails.pure_right ⟨hinl.length_eq, hinl⟩ (Entails.refl _)
  · apply Entails.sepExists_elim; intro bs
    apply Entails.pure_left; rintro ⟨_, ckBs, hck_len, hck_inl, rfl⟩
    rw [pointsToBytes_append, chainPrefixBytes_length, pointsToBytes_chainPrefixBytes]
    have h72 : a + BitVec.ofNat 64 72 = a + 72#64 := rfl
    rw [h72]
    have hpull :
        ((((a ↦ₛ vecGhostHeaderBytes gc.1.srk) ∗
            ((a + 24#64) ↦ₛ vecGhostHeaderBytes gc.1.priv) ∗
            ((a + 48#64) ↦ₛ
              vecHeaderBytes gc.1.mkCap gc.1.mkPtr
                (BitVec.ofNat 64 (gc.1.keys.zip gc.2.messageKeys).length))) ∗
           ((a + 72#64) ↦ₛ ckBs)) ∗
          (⌜ProtoChainPure gc⌝ ∗
            vecGhostHeap A gc.1.srk ∗
            vecGhostHeap A gc.1.priv ∗
            vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr
              (gc.1.keys.zip gc.2.messageKeys) ∗
            optChainKeyHeap A gc.1.ck gc.2.chainKey)) =
        (⌜ProtoChainPure gc⌝ ∗
          ((a ↦ₛ vecGhostHeaderBytes gc.1.srk) ∗ vecGhostHeap A gc.1.srk) ∗
          (((a + 24#64) ↦ₛ vecGhostHeaderBytes gc.1.priv) ∗ vecGhostHeap A gc.1.priv) ∗
          (((a + 48#64) ↦ₛ
              vecHeaderBytes gc.1.mkCap gc.1.mkPtr
                (BitVec.ofNat 64 (gc.1.keys.zip gc.2.messageKeys).length)) ∗
            vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr
              (gc.1.keys.zip gc.2.messageKeys)) ∗
          (((a + 72#64) ↦ₛ ckBs) ∗ optChainKeyHeap A gc.1.ck gc.2.chainKey)) := by
      ac_rfl
    rw [hpull]
    apply sepConj_mono_right
    apply sepConj_mono_right
    apply sepConj_mono_right
    apply sepConj_mono_right
    refine Entails.sepExists_right ckBs ?_
    exact Entails.pure_right ⟨hck_len, hck_inl⟩ (Entails.refl _)

/-- Decomposes `chainAt A gc a` into 104 inline bytes (`ChainInline gc bs`) and `chainHeap A gc`. -/
theorem chainAt_eq_inline_sep_heap (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64) :
    ChainAtDecompStmt A gc a := by
  unfold ChainAtDecompStmt chainAt chainHeap
  rw [vecGhostAt_eq_bytes_sep_heap A gc.1.srk a,
      vecGhostAt_eq_bytes_sep_heap A gc.1.priv (a + 24#64),
      vecAt_eq_bytes_sep_buf A 104 8 (messageKeyAt A) (a + 48#64),
      optChainKeyAt_eq_inline_sep_heap A gc.1.ck gc.2.chainKey (a + 72#64)]
  change (⌜ChainPure gc⌝ ∗ _) = _
  apply sepProp_eq_of_entails
  · have hpull :
        (⌜ChainPure gc⌝ ∗
          ((a ↦ₛ vecGhostHeaderBytes gc.1.srk) ∗ vecGhostHeap A gc.1.srk) ∗
          (((a + 24#64) ↦ₛ vecGhostHeaderBytes gc.1.priv) ∗ vecGhostHeap A gc.1.priv) ∗
          (((a + 48#64) ↦ₛ
              vecHeaderBytes gc.1.mkCap gc.1.mkPtr
                (BitVec.ofNat 64 (gc.1.keys.zip gc.2.messageKeys).length)) ∗
            vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr
              (gc.1.keys.zip gc.2.messageKeys)) ∗
          (∃∗ bs, ⌜bs.length = 32 ∧ OptChainKeyInline gc.1.ck gc.2.chainKey bs⌝ ∗
            ((a + 72#64) ↦ₛ bs) ∗ optChainKeyHeap A gc.1.ck gc.2.chainKey)) =
        ((∃∗ bs, ⌜bs.length = 32 ∧ OptChainKeyInline gc.1.ck gc.2.chainKey bs⌝ ∗
            (((a ↦ₛ vecGhostHeaderBytes gc.1.srk) ∗
              ((a + 24#64) ↦ₛ vecGhostHeaderBytes gc.1.priv) ∗
              ((a + 48#64) ↦ₛ
                vecHeaderBytes gc.1.mkCap gc.1.mkPtr
                  (BitVec.ofNat 64 (gc.1.keys.zip gc.2.messageKeys).length))) ∗
             ((a + 72#64) ↦ₛ bs))) ∗
          (⌜ChainPure gc⌝ ∗
            vecGhostHeap A gc.1.srk ∗
            vecGhostHeap A gc.1.priv ∗
            vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr
              (gc.1.keys.zip gc.2.messageKeys) ∗
            optChainKeyHeap A gc.1.ck gc.2.chainKey)) := by
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply sepExists_congr; intro ckBs
      ac_rfl
    rw [hpull, sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro ckBs
    rw [← pointsToBytes_chainPrefixBytes gc a, sepConj_assoc]
    apply Entails.pure_left; rintro ⟨hck_len, hck_inl⟩
    have h72 : a + 72#64 = a + BitVec.ofNat 64 (chainPrefixBytes gc).length := by
      rw [chainPrefixBytes_length]
    rw [h72, ← pointsToBytes_append]
    set bs := chainPrefixBytes gc ++ ckBs
    have hinl : ChainInline gc bs := ⟨ckBs, hck_len, hck_inl, rfl⟩
    refine Entails.sepExists_right bs ?_
    exact Entails.pure_right ⟨hinl.length_eq, hinl⟩ (Entails.refl _)
  · apply Entails.sepExists_elim; intro bs
    apply Entails.pure_left; rintro ⟨_, ckBs, hck_len, hck_inl, rfl⟩
    rw [pointsToBytes_append, chainPrefixBytes_length, pointsToBytes_chainPrefixBytes]
    have h72 : a + BitVec.ofNat 64 72 = a + 72#64 := rfl
    rw [h72]
    have hpull :
        ((((a ↦ₛ vecGhostHeaderBytes gc.1.srk) ∗
            ((a + 24#64) ↦ₛ vecGhostHeaderBytes gc.1.priv) ∗
            ((a + 48#64) ↦ₛ
              vecHeaderBytes gc.1.mkCap gc.1.mkPtr
                (BitVec.ofNat 64 (gc.1.keys.zip gc.2.messageKeys).length))) ∗
           ((a + 72#64) ↦ₛ ckBs)) ∗
          (⌜ChainPure gc⌝ ∗
            vecGhostHeap A gc.1.srk ∗
            vecGhostHeap A gc.1.priv ∗
            vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr
              (gc.1.keys.zip gc.2.messageKeys) ∗
            optChainKeyHeap A gc.1.ck gc.2.chainKey)) =
        (⌜ChainPure gc⌝ ∗
          ((a ↦ₛ vecGhostHeaderBytes gc.1.srk) ∗ vecGhostHeap A gc.1.srk) ∗
          (((a + 24#64) ↦ₛ vecGhostHeaderBytes gc.1.priv) ∗ vecGhostHeap A gc.1.priv) ∗
          (((a + 48#64) ↦ₛ
              vecHeaderBytes gc.1.mkCap gc.1.mkPtr
                (BitVec.ofNat 64 (gc.1.keys.zip gc.2.messageKeys).length)) ∗
            vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr
              (gc.1.keys.zip gc.2.messageKeys)) ∗
          (((a + 72#64) ↦ₛ ckBs) ∗ optChainKeyHeap A gc.1.ck gc.2.chainKey)) := by
      ac_rfl
    rw [hpull]
    apply sepConj_mono_right
    apply sepConj_mono_right
    apply sepConj_mono_right
    apply sepConj_mono_right
    refine Entails.sepExists_right ckBs ?_
    exact Entails.pure_right ⟨hck_len, hck_inl⟩ (Entails.refl _)

theorem chainAt_entails_inline_sep_heap (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64) :
    chainAt A gc a ⊢
      ∃∗ bs : List (BitVec 8),
        ⌜bs.length = 104 ∧ ChainInline gc bs⌝ ∗ (a ↦ₛ bs) ∗ chainHeap A gc :=
  Entails.of_eq (chainAt_eq_inline_sep_heap A gc a)

/-- Reassemble `chainAt A gc dst` from `(dst ↦ₛ bs) ∗ chainHeap A gc` given `ChainInline gc bs`. -/
theorem chainAt_of_bytes (A : RustAlloc) (gc : ChainGhost × ReceiverChain) (dst : BitVec 64)
    {bs : List (BitVec 8)} (h : ChainInline gc bs) :
    ((dst ↦ₛ bs) ∗ chainHeap A gc) ⊢ chainAt A gc dst := by
  rw [chainAt_eq_inline_sep_heap A gc dst]
  refine Entails.sepExists_right bs ?_
  exact Entails.pure_right ⟨h.length_eq, h⟩ (Entails.refl _)

/-- Forgetting the 104 inline bytes of `chainAt` yields `memRegion a 104 ∗ chainHeap A gc`. -/
theorem chainAt_entails_memRegion_sep_heap (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64) :
    chainAt A gc a ⊢ memRegion a 104 ∗ chainHeap A gc := by
  rw [chainAt_eq_inline_sep_heap A gc a]
  apply Entails.sepExists_elim; intro bs
  apply Entails.pure_left; rintro ⟨hlen, _⟩
  apply sepConj_mono_left
  have h := pointsToBytes_entails_memRegion a bs
  rwa [hlen] at h

/-- Move `chainAt` from `src` to `dst` after copying the 104 inline bytes `bs` to `dst`,
leaving `src ↦ₛ bs`. -/
theorem chainAt_move_bytes (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (src dst : BitVec 64) {bs : List (BitVec 8)} (h : ChainInline gc bs) :
    ((dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ chainHeap A gc) ⊢
      chainAt A gc dst ∗ (src ↦ₛ bs) := by
  have hpull :
      ((dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ chainHeap A gc) =
      (((dst ↦ₛ bs) ∗ chainHeap A gc) ∗ (src ↦ₛ bs)) := by
    ac_rfl
  rw [hpull]
  exact sepConj_mono_left (chainAt_of_bytes A gc dst h)

/-- Move `chainAt` from `src` to `dst` after copying `bs`, collapsing `src ↦ₛ bs` to
`memRegion src 104`. -/
theorem chainAt_move_to_memRegion (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (src dst : BitVec 64) {bs : List (BitVec 8)} (h : ChainInline gc bs) :
    ((dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ chainHeap A gc) ⊢
      chainAt A gc dst ∗ memRegion src 104 := by
  refine Entails.trans (chainAt_move_bytes A gc src dst h) ?_
  apply sepConj_mono_right
  have hregion := pointsToBytes_entails_memRegion src bs
  rwa [h.length_eq] at hregion

/-- Exposes `chainAt A gc a` as six 128-bit quadwords at `+0x00..+0x60` and one 64-bit word at `+0x60`. -/
theorem chainAt_entails_chunks104_6QW (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64) :
    chainAt A gc a ⊢
      ∃∗ q0 : BitVec 128, ∃∗ q1 : BitVec 128, ∃∗ q2 : BitVec 128,
      ∃∗ q3 : BitVec 128, ∃∗ q4 : BitVec 128, ∃∗ q5 : BitVec 128,
      ∃∗ w6 : BitVec 64,
        ⌜ChainInline gc (bytes104Of6QW q0 q1 q2 q3 q4 q5 w6)⌝ ∗
          chunks104_6QWAt a q0 q1 q2 q3 q4 q5 w6 ∗ chainHeap A gc := by
  rw [chainAt_eq_inline_sep_heap A gc a]
  apply Entails.sepExists_elim; intro bs
  apply Entails.pure_left; rintro ⟨hlen, hinl⟩
  obtain ⟨q0, q1, q2, q3, q4, q5, w6, hbs_eq, hchunks⟩ := exists_bytes104Of6QW hlen
  rw [hchunks a]
  rw [hbs_eq] at hinl
  refine Entails.sepExists_right q0 (Entails.sepExists_right q1
    (Entails.sepExists_right q2 (Entails.sepExists_right q3
      (Entails.sepExists_right q4 (Entails.sepExists_right q5
        (Entails.sepExists_right w6 ?_))))))
  exact Entails.pure_right hinl (Entails.refl _)

/-- Reassemble `chainAt A gc dst` from `chunks104_6QWAt dst q0 q1 q2 q3 q4 q5 w6` and
`chainHeap A gc`. -/
theorem chainAt_of_chunks104_6QW (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (dst : BitVec 64) {q0 q1 q2 q3 q4 q5 : BitVec 128} {w6 : BitVec 64}
    (h : ChainInline gc (bytes104Of6QW q0 q1 q2 q3 q4 q5 w6)) :
    (chunks104_6QWAt dst q0 q1 q2 q3 q4 q5 w6 ∗ chainHeap A gc) ⊢
      chainAt A gc dst := by
  rw [chunks104_6QWAt_eq_pointsToBytes]
  exact chainAt_of_bytes A gc dst h

/-! ## `optSenderChainAt` (104 bytes): bridge, decomposition, and move corollaries -/

/-- Relates `optSenderChainAt A a (some g) (some sc)` to `protoChainAt` and `SenderChainPrivPure`. -/
theorem optSenderChainAt_some_eq_chainAt (A : RustAlloc) (a : BitVec 64)
    (g : SenderChainGhost) (sc : SenderChain) :
    OptSenderChainSomeBridgeStmt A a g sc := by
  dsimp only [OptSenderChainSomeBridgeStmt, optSenderChainAt, protoChainAt, ProtoChainPure,
    SenderChainPrivPure, SenderChainGhost.toChainGhost, SenderChain.toReceiverChain,
    List.length_nil, List.zip_nil_left]
  rw [pure_sepConj_pure_assoc]
  congr 2
  apply propext
  have hmax : 0 ≤ maxMessageKeys := Nat.zero_le _
  tauto

theorem OptSenderChainInline.length_eq {g : Option SenderChainGhost} {sc : Option SenderChain}
    {bs : List (BitVec 8)} (h : OptSenderChainInline g sc bs) : bs.length = 104 := by
  cases g <;> cases sc
  · rcases h with ⟨pad, hpad, rfl⟩
    simp [hpad]
  · cases h
  · cases h
  · exact ChainInline.length_eq h

/-- Any 6 quadwords after `noneCap` satisfy `OptSenderChainInline none none`. -/
theorem OptSenderChainInline.none_of_chunks96 (q0 q1 q2 q3 q4 q5 : BitVec 128) :
    OptSenderChainInline none none (bytes104OfW6Q noneCap q0 q1 q2 q3 q4 q5) := by
  refine ⟨unpack128 q0 ++ unpack128 q1 ++ unpack128 q2 ++
    unpack128 q3 ++ unpack128 q4 ++ unpack128 q5, by simp, ?_⟩
  simp [bytes104OfW6Q, List.append_assoc]

/-- Decomposes `optSenderChainAt A a g sc` into 104 inline bytes (`OptSenderChainInline g sc bs`) and `optSenderChainHeap A g sc`. -/
theorem optSenderChainAt_eq_inline_sep_heap (A : RustAlloc) (a : BitVec 64)
    (g : Option SenderChainGhost) (sc : Option SenderChain) :
    OptSenderChainAtDecompStmt A a g sc := by
  unfold OptSenderChainAtDecompStmt
  cases g with
  | none =>
    cases sc with
    | none =>
      dsimp only [optSenderChainAt, optSenderChainHeap]
      apply sepProp_eq_of_entails
      · rw [pointsTo64_eq_pointsToBytes, memRegion_eq_exists_bytes (a + 8#64) 96 (by decide),
            sepExists_sepConj_right]
        apply Entails.sepExists_elim; intro pad
        rw [sepConj_pure_left_comm]
        apply Entails.pure_left; intro hpad
        have h8 : a + 8#64 = a + BitVec.ofNat 64 (unpack64 noneCap).length := rfl
        rw [h8, ← pointsToBytes_append]
        have hinl : OptSenderChainInline none none (unpack64 noneCap ++ pad) := ⟨pad, hpad, rfl⟩
        refine Entails.sepExists_right (unpack64 noneCap ++ pad) ?_
        rw [sepConj_emp]
        exact Entails.pure_right ⟨hinl.length_eq, hinl⟩ (Entails.refl _)
      · apply Entails.sepExists_elim; intro bs
        rw [sepConj_emp]
        apply Entails.pure_left; rintro ⟨_, pad, hpad, rfl⟩
        rw [pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes]
        apply sepConj_mono_right
        have h := pointsToBytes_entails_memRegion (a + 8#64) pad
        rwa [hpad] at h
    | some sc =>
      dsimp only [optSenderChainAt, optSenderChainHeap, OptSenderChainInline]
      apply sepProp_eq_of_entails
      · apply Entails.pure_left_only; intro h; exact False.elim h
      · apply Entails.sepExists_elim; intro bs
        apply Entails.pure_left; rintro ⟨_, h⟩; exact False.elim h
  | some g =>
    cases sc with
    | none =>
      dsimp only [optSenderChainAt, optSenderChainHeap, OptSenderChainInline]
      apply sepProp_eq_of_entails
      · apply Entails.pure_left_only; intro h; exact False.elim h
      · apply Entails.sepExists_elim; intro bs
        apply Entails.pure_left; rintro ⟨_, h⟩; exact False.elim h
    | some sc =>
      rw [optSenderChainAt_some_eq_chainAt A a g sc,
          protoChainAt_eq_inline_sep_heap A (g.toChainGhost, sc.toReceiverChain) a,
          sepExists_sepConj_right]
      apply sepExists_congr; intro bs
      dsimp only [OptSenderChainInline, optSenderChainHeap]
      ac_rfl

theorem optSenderChainAt_entails_inline_sep_heap (A : RustAlloc) (a : BitVec 64)
    (g : Option SenderChainGhost) (sc : Option SenderChain) :
    optSenderChainAt A a g sc ⊢
      ∃∗ bs : List (BitVec 8),
        ⌜bs.length = 104 ∧ OptSenderChainInline g sc bs⌝ ∗ (a ↦ₛ bs) ∗ optSenderChainHeap A g sc :=
  Entails.of_eq (optSenderChainAt_eq_inline_sep_heap A a g sc)

/-- Reassemble `optSenderChainAt A dst g sc` from `(dst ↦ₛ bs) ∗ optSenderChainHeap A g sc`
given `OptSenderChainInline g sc bs`. -/
theorem optSenderChainAt_of_bytes (A : RustAlloc) (dst : BitVec 64)
    (g : Option SenderChainGhost) (sc : Option SenderChain)
    {bs : List (BitVec 8)} (h : OptSenderChainInline g sc bs) :
    ((dst ↦ₛ bs) ∗ optSenderChainHeap A g sc) ⊢ optSenderChainAt A dst g sc := by
  rw [optSenderChainAt_eq_inline_sep_heap A dst g sc]
  refine Entails.sepExists_right bs ?_
  exact Entails.pure_right ⟨h.length_eq, h⟩ (Entails.refl _)

/-- Forgetting the 104 inline bytes of `optSenderChainAt` yields
`memRegion a 104 ∗ optSenderChainHeap A g sc`. -/
theorem optSenderChainAt_entails_memRegion_sep_heap (A : RustAlloc) (a : BitVec 64)
    (g : Option SenderChainGhost) (sc : Option SenderChain) :
    optSenderChainAt A a g sc ⊢ memRegion a 104 ∗ optSenderChainHeap A g sc := by
  rw [optSenderChainAt_eq_inline_sep_heap A a g sc]
  apply Entails.sepExists_elim; intro bs
  apply Entails.pure_left; rintro ⟨hlen, _⟩
  apply sepConj_mono_left
  have h := pointsToBytes_entails_memRegion a bs
  rwa [hlen] at h

/-- Move `optSenderChainAt` from `src` to `dst` after copying the 104 inline bytes `bs` to `dst`,
leaving `src ↦ₛ bs`. -/
theorem optSenderChainAt_move_bytes (A : RustAlloc) (src dst : BitVec 64)
    (g : Option SenderChainGhost) (sc : Option SenderChain)
    {bs : List (BitVec 8)} (h : OptSenderChainInline g sc bs) :
    ((dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ optSenderChainHeap A g sc) ⊢
      optSenderChainAt A dst g sc ∗ (src ↦ₛ bs) := by
  have hpull :
      ((dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ optSenderChainHeap A g sc) =
      (((dst ↦ₛ bs) ∗ optSenderChainHeap A g sc) ∗ (src ↦ₛ bs)) := by
    ac_rfl
  rw [hpull]
  exact sepConj_mono_left (optSenderChainAt_of_bytes A dst g sc h)

/-- Move `optSenderChainAt` from `src` to `dst` after copying `bs`, collapsing `src ↦ₛ bs` to
`memRegion src 104`. -/
theorem optSenderChainAt_move_to_memRegion (A : RustAlloc) (src dst : BitVec 64)
    (g : Option SenderChainGhost) (sc : Option SenderChain)
    {bs : List (BitVec 8)} (h : OptSenderChainInline g sc bs) :
    ((dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ optSenderChainHeap A g sc) ⊢
      optSenderChainAt A dst g sc ∗ memRegion src 104 := by
  refine Entails.trans (optSenderChainAt_move_bytes A src dst g sc h) ?_
  apply sepConj_mono_right
  have hregion := pointsToBytes_entails_memRegion src bs
  rwa [h.length_eq] at hregion

/-- Exposes `optSenderChainAt A a g sc` as a 64-bit word at `+0x00` and six 128-bit quadwords at `+0x08..+0x68`. -/
theorem optSenderChainAt_entails_chunks104W6Q (A : RustAlloc) (a : BitVec 64)
    (g : Option SenderChainGhost) (sc : Option SenderChain) :
    optSenderChainAt A a g sc ⊢
      ∃∗ w0 : BitVec 64,
      ∃∗ q0 : BitVec 128, ∃∗ q1 : BitVec 128, ∃∗ q2 : BitVec 128,
      ∃∗ q3 : BitVec 128, ∃∗ q4 : BitVec 128, ∃∗ q5 : BitVec 128,
        ⌜OptSenderChainInline g sc (bytes104OfW6Q w0 q0 q1 q2 q3 q4 q5)⌝ ∗
          chunks104W6QAt a w0 q0 q1 q2 q3 q4 q5 ∗ optSenderChainHeap A g sc := by
  rw [optSenderChainAt_eq_inline_sep_heap A a g sc]
  apply Entails.sepExists_elim; intro bs
  apply Entails.pure_left; rintro ⟨hlen, hinl⟩
  obtain ⟨w0, q0, q1, q2, q3, q4, q5, hbs_eq, hchunks⟩ := exists_bytes104OfW6Q hlen
  rw [hchunks a]
  rw [hbs_eq] at hinl
  refine Entails.sepExists_right w0 (Entails.sepExists_right q0
    (Entails.sepExists_right q1 (Entails.sepExists_right q2
      (Entails.sepExists_right q3 (Entails.sepExists_right q4
        (Entails.sepExists_right q5 ?_))))))
  exact Entails.pure_right hinl (Entails.refl _)

/-- Reassembles `optSenderChainAt A dst g sc` from `chunks104W6QAt` and `optSenderChainHeap`. -/
theorem optSenderChainAt_of_chunks104W6Q (A : RustAlloc) (dst : BitVec 64)
    (g : Option SenderChainGhost) (sc : Option SenderChain)
    {w0 : BitVec 64} {q0 q1 q2 q3 q4 q5 : BitVec 128}
    (h : OptSenderChainInline g sc (bytes104OfW6Q w0 q0 q1 q2 q3 q4 q5)) :
    (chunks104W6QAt dst w0 q0 q1 q2 q3 q4 q5 ∗ optSenderChainHeap A g sc) ⊢
      optSenderChainAt A dst g sc := by
  rw [chunks104W6QAt_eq_pointsToBytes]
  exact optSenderChainAt_of_bytes A dst g sc h

/-- In the `None` sender-chain case, writing `noneCap` at `dst` and any 6 quadwords `q0..q5` at
`dst + 0x8..dst + 0x68` directly entails `optSenderChainAt A dst none none`. -/
theorem optSenderChainAt_none_of_chunks104W6Q (A : RustAlloc) (dst : BitVec 64)
    (q0 q1 q2 q3 q4 q5 : BitVec 128) :
    chunks104W6QAt dst noneCap q0 q1 q2 q3 q4 q5 ⊢
      optSenderChainAt A dst none none := by
  have h := optSenderChainAt_of_chunks104W6Q A dst none none
    (OptSenderChainInline.none_of_chunks96 q0 q1 q2 q3 q4 q5)
  simpa [optSenderChainHeap] using h

/-! ## `sessionStateAt` (344 bytes): decomposition and move corollaries -/

@[scoped simp]
theorem sessionPrefixBytes_length (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    (sessionPrefixBytes G st).length = 144 := by
  simp [sessionPrefixBytes, vecHeaderBytes]

theorem sessionSuffixBytes_length {G : SessionGhost} (st : SessionState (List (BitVec 8)))
    (hreg : G.regIds.length = 8) :
    (sessionSuffixBytes G st).length = 16 := by
  simp [sessionSuffixBytes, hreg]

theorem SessionInline.length_eq {G : SessionGhost} {st : SessionState (List (BitVec 8))}
    {bs : List (BitVec 8)} (h : SessionInline G st bs) : bs.length = 344 := by
  rcases h with ⟨hreg, scBs, pendBs, kybBs, hsc_len, _, hpend_len, _, hkyb_len, _, rfl⟩
  simp [sessionSuffixBytes_length st hreg, hsc_len, hpend_len, hkyb_len]

/-- The first 144 (`0x90`) bytes of `sessionStateAt` equal `ss ↦ₛ sessionPrefixBytes G st`. -/
theorem pointsToBytes_sessionPrefixBytes (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) (ss : BitVec 64) :
    (ss ↦ₛ sessionPrefixBytes G st) =
      (ss ↦ₛ vecGhostHeaderBytes G.localIk) ∗
        ((ss + 0x18#64) ↦ₛ vecGhostHeaderBytes G.remoteIk) ∗
        ((ss + 0x30#64) ↦ₛ vecHeaderBytes G.root.cap G.root.ptr 32#64) ∗
        ((ss + 0x48#64) ↦ₛ
          vecHeaderBytes G.chainsCap G.chainsPtr
            (BitVec.ofNat 64 (G.chains.zip st.receiverChains).length)) ∗
        ((ss + 0x60#64) ↦ₛ vecGhostHeaderBytes G.alice) ∗
        ((ss + 0x78#64) ↦ₛ
          vecHeaderBytes G.pq.cap G.pq.ptr (BitVec.ofNat 64 st.pqRatchetState.length)) := by
  unfold sessionPrefixBytes
  simp only [List.append_assoc, pointsToBytes_append,
    vecGhostHeaderBytes_length, vecHeaderBytes_length]
  have h18 : ss + BitVec.ofNat 64 24 = ss + 0x18#64 := rfl
  have h30 : ss + 0x18#64 + BitVec.ofNat 64 24 = ss + 0x30#64 := by bv_arith
  have h48 : ss + 0x30#64 + BitVec.ofNat 64 24 = ss + 0x48#64 := by bv_arith
  have h60 : ss + 0x48#64 + BitVec.ofNat 64 24 = ss + 0x60#64 := by bv_arith
  have h78 : ss + 0x60#64 + BitVec.ofNat 64 24 = ss + 0x78#64 := by bv_arith
  rw [h18, h30, h48, h60, h78]

/-- The last 16 (`0x10`) bytes of `sessionStateAt` at `ss + 0x148` equal
`(ss + 0x148#64) ↦ₛ sessionSuffixBytes G st`. -/
theorem pointsToBytes_sessionSuffixBytes (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) (ss : BitVec 64) :
    ((ss + 0x148#64) ↦ₛ sessionSuffixBytes G st) =
      ((ss + 0x148#64) ↦₃₂ st.sessionVersion) ∗
        ((ss + 0x14c#64) ↦₃₂ st.previousCounter) ∗
        ((ss + 0x150#64) ↦ₛ G.regIds) := by
  unfold sessionSuffixBytes
  rw [List.append_assoc, pointsToBytes_append, pointsToBytes_append,
      unpack32_length, unpack32_length,
      ← pointsTo32_eq_pointsToBytes, ← pointsTo32_eq_pointsToBytes]
  have h14c : ss + 0x148#64 + BitVec.ofNat 64 4 = ss + 0x14c#64 := by bv_arith
  have h150 : ss + 0x14c#64 + BitVec.ofNat 64 4 = ss + 0x150#64 := by bv_arith
  rw [h14c, h150]

/-- Combine the five contiguous inline byte segments of `sessionStateAt` (`144 + 104 + 48 + 32 + 16`)
into a single 344-byte slice at `ss`. -/
theorem pointsToBytes_sessionInline_segments (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) (ss : BitVec 64)
    {scBs pendBs kybBs : List (BitVec 8)}
    (hsc_len : scBs.length = 104)
    (hpend_len : pendBs.length = 48)
    (hkyb_len : kybBs.length = 32) :
    (ss ↦ₛ (sessionPrefixBytes G st ++ scBs ++ pendBs ++ kybBs ++ sessionSuffixBytes G st)) =
      (ss ↦ₛ sessionPrefixBytes G st) ∗
        ((ss + 0x90#64) ↦ₛ scBs) ∗
        ((ss + 0xf8#64) ↦ₛ pendBs) ∗
        ((ss + 0x128#64) ↦ₛ kybBs) ∗
        ((ss + 0x148#64) ↦ₛ sessionSuffixBytes G st) := by
  simp only [List.append_assoc, pointsToBytes_append,
    sessionPrefixBytes_length, hsc_len, hpend_len, hkyb_len]
  have h90 : ss + BitVec.ofNat 64 144 = ss + 0x90#64 := rfl
  have hf8 : ss + 0x90#64 + BitVec.ofNat 64 104 = ss + 0xf8#64 := by bv_arith
  have h128 : ss + 0xf8#64 + BitVec.ofNat 64 48 = ss + 0x128#64 := by bv_arith
  have h148 : ss + 0x128#64 + BitVec.ofNat 64 32 = ss + 0x148#64 := by bv_arith
  rw [h90, hf8, h128, h148]

/-- Decomposes `sessionStateAt A ss G st` into 344 inline bytes (`SessionInline G st bs`) and `sessionHeap A G st`. -/
theorem sessionStateAt_eq_inline_sep_heap (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) :
    SessionStateAtDecompStmt A ss G st := by
  unfold SessionStateAtDecompStmt sessionStateAt sessionHeap
  rw [vecGhostAt_eq_bytes_sep_heap A G.localIk ss,
      vecGhostAt_eq_bytes_sep_heap A G.remoteIk (ss + 0x18#64),
      vecU8At_eq_bytes_sep_buf A (ss + 0x30#64) G.root.cap G.root.ptr (keyToBytes32 st.rootKey),
      vecAt_eq_bytes_sep_buf A 104 8 (chainAt A) (ss + 0x48#64),
      vecGhostAt_eq_bytes_sep_heap A G.alice (ss + 0x60#64),
      vecU8At_eq_bytes_sep_buf A (ss + 0x78#64) G.pq.cap G.pq.ptr st.pqRatchetState,
      optSenderChainAt_eq_inline_sep_heap A (ss + 0x90#64) G.sender st.senderChain,
      optTailVecAt_eq_inline_sep_heap A (by decide) (by decide) (ss + 0xf8#64) G.pending,
      optTailVecAt_eq_inline_sep_heap A (by decide) (by decide) (ss + 0x128#64) G.kyber,
      ← pointsToBytes_sessionSuffixBytes G st ss]
  have hroot_len : BitVec.ofNat 64 (keyToBytes32 st.rootKey).length = 32#64 := by
    simp [keyToBytes32]
  rw [hroot_len]
  change (⌜SessionPure G st⌝ ∗ _) = _
  apply sepProp_eq_of_entails
  · apply Entails.pure_left; intro hpure
    have hreg : G.regIds.length = 8 := hpure.2.2.2.2.1
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro kybBs
    apply Entails.sepExists_elim; intro pendBs
    apply Entails.sepExists_elim; intro scBs
    have hpull :
        (((ss ↦ₛ vecGhostHeaderBytes G.localIk) ∗ vecGhostHeap A G.localIk) ∗
          (((ss + 0x18#64) ↦ₛ vecGhostHeaderBytes G.remoteIk) ∗ vecGhostHeap A G.remoteIk) ∗
          (((ss + 0x30#64) ↦ₛ vecHeaderBytes G.root.cap G.root.ptr 32#64) ∗
            vecU8Buf A G.root.cap G.root.ptr (keyToBytes32 st.rootKey)) ∗
          (((ss + 0x48#64) ↦ₛ
              vecHeaderBytes G.chainsCap G.chainsPtr
                (BitVec.ofNat 64 (G.chains.zip st.receiverChains).length)) ∗
            vecBuf A 104 8 (chainAt A) G.chainsCap G.chainsPtr
              (G.chains.zip st.receiverChains)) ∗
          (((ss + 0x60#64) ↦ₛ vecGhostHeaderBytes G.alice) ∗ vecGhostHeap A G.alice) ∗
          (((ss + 0x78#64) ↦ₛ
              vecHeaderBytes G.pq.cap G.pq.ptr (BitVec.ofNat 64 st.pqRatchetState.length)) ∗
            vecU8Buf A G.pq.cap G.pq.ptr st.pqRatchetState) ∗
          (⌜scBs.length = 104 ∧ OptSenderChainInline G.sender st.senderChain scBs⌝ ∗
            ((ss + 0x90#64) ↦ₛ scBs) ∗ optSenderChainHeap A G.sender st.senderChain) ∗
          (⌜pendBs.length = 48 ∧ OptTailVecInline 48 G.pending pendBs⌝ ∗
            ((ss + 0xf8#64) ↦ₛ pendBs) ∗ optTailVecHeap A G.pending) ∗
          (⌜kybBs.length = 32 ∧ OptTailVecInline 32 G.kyber kybBs⌝ ∗
            ((ss + 0x128#64) ↦ₛ kybBs) ∗ optTailVecHeap A G.kyber) ∗
          ((ss + 0x148#64) ↦ₛ sessionSuffixBytes G st)) =
        (⌜scBs.length = 104 ∧ OptSenderChainInline G.sender st.senderChain scBs⌝ ∗
          ⌜pendBs.length = 48 ∧ OptTailVecInline 48 G.pending pendBs⌝ ∗
          ⌜kybBs.length = 32 ∧ OptTailVecInline 32 G.kyber kybBs⌝ ∗
          (((ss ↦ₛ vecGhostHeaderBytes G.localIk) ∗
            ((ss + 0x18#64) ↦ₛ vecGhostHeaderBytes G.remoteIk) ∗
            ((ss + 0x30#64) ↦ₛ vecHeaderBytes G.root.cap G.root.ptr 32#64) ∗
            ((ss + 0x48#64) ↦ₛ
              vecHeaderBytes G.chainsCap G.chainsPtr
                (BitVec.ofNat 64 (G.chains.zip st.receiverChains).length)) ∗
            ((ss + 0x60#64) ↦ₛ vecGhostHeaderBytes G.alice) ∗
            ((ss + 0x78#64) ↦ₛ
              vecHeaderBytes G.pq.cap G.pq.ptr (BitVec.ofNat 64 st.pqRatchetState.length))) ∗
           ((ss + 0x90#64) ↦ₛ scBs) ∗
           ((ss + 0xf8#64) ↦ₛ pendBs) ∗
           ((ss + 0x128#64) ↦ₛ kybBs) ∗
           ((ss + 0x148#64) ↦ₛ sessionSuffixBytes G st)) ∗
          (vecGhostHeap A G.localIk ∗
            vecGhostHeap A G.remoteIk ∗
            vecU8Buf A G.root.cap G.root.ptr (keyToBytes32 st.rootKey) ∗
            vecBuf A 104 8 (chainAt A) G.chainsCap G.chainsPtr
              (G.chains.zip st.receiverChains) ∗
            vecGhostHeap A G.alice ∗
            vecU8Buf A G.pq.cap G.pq.ptr st.pqRatchetState ∗
            optSenderChainHeap A G.sender st.senderChain ∗
            optTailVecHeap A G.pending ∗
            optTailVecHeap A G.kyber)) := by
      ac_rfl
    rw [hpull, ← pointsToBytes_sessionPrefixBytes G st ss]
    apply Entails.pure_left; rintro ⟨hsc_len, hsc_inl⟩
    apply Entails.pure_left; rintro ⟨hpend_len, hpend_inl⟩
    apply Entails.pure_left; rintro ⟨hkyb_len, hkyb_inl⟩
    rw [← pointsToBytes_sessionInline_segments G st ss hsc_len hpend_len hkyb_len]
    set bs := sessionPrefixBytes G st ++ scBs ++ pendBs ++ kybBs ++ sessionSuffixBytes G st
    have hinl : SessionInline G st bs :=
      ⟨hreg, scBs, pendBs, kybBs, hsc_len, hsc_inl, hpend_len, hpend_inl, hkyb_len, hkyb_inl, rfl⟩
    refine Entails.sepExists_right bs ?_
    apply Entails.pure_right ⟨hinl.length_eq, hinl⟩
    apply sepConj_mono_right
    exact Entails.pure_right hpure (Entails.refl _)
  · apply Entails.sepExists_elim; intro bs
    apply Entails.pure_left
    rintro ⟨_, _, scBs, pendBs, kybBs, hsc_len, hsc_inl, hpend_len, hpend_inl, hkyb_len, hkyb_inl, rfl⟩
    rw [pointsToBytes_sessionInline_segments G st ss hsc_len hpend_len hkyb_len,
        pointsToBytes_sessionPrefixBytes G st ss]
    have hpull :
        ((((ss ↦ₛ vecGhostHeaderBytes G.localIk) ∗
            ((ss + 0x18#64) ↦ₛ vecGhostHeaderBytes G.remoteIk) ∗
            ((ss + 0x30#64) ↦ₛ vecHeaderBytes G.root.cap G.root.ptr 32#64) ∗
            ((ss + 0x48#64) ↦ₛ
              vecHeaderBytes G.chainsCap G.chainsPtr
                (BitVec.ofNat 64 (G.chains.zip st.receiverChains).length)) ∗
            ((ss + 0x60#64) ↦ₛ vecGhostHeaderBytes G.alice) ∗
            ((ss + 0x78#64) ↦ₛ
              vecHeaderBytes G.pq.cap G.pq.ptr (BitVec.ofNat 64 st.pqRatchetState.length))) ∗
          ((ss + 0x90#64) ↦ₛ scBs) ∗
          ((ss + 0xf8#64) ↦ₛ pendBs) ∗
          ((ss + 0x128#64) ↦ₛ kybBs) ∗
          ((ss + 0x148#64) ↦ₛ sessionSuffixBytes G st)) ∗
         (⌜SessionPure G st⌝ ∗
           vecGhostHeap A G.localIk ∗
           vecGhostHeap A G.remoteIk ∗
           vecU8Buf A G.root.cap G.root.ptr (keyToBytes32 st.rootKey) ∗
           vecBuf A 104 8 (chainAt A) G.chainsCap G.chainsPtr
             (G.chains.zip st.receiverChains) ∗
           vecGhostHeap A G.alice ∗
           vecU8Buf A G.pq.cap G.pq.ptr st.pqRatchetState ∗
           optSenderChainHeap A G.sender st.senderChain ∗
           optTailVecHeap A G.pending ∗
           optTailVecHeap A G.kyber)) =
        (⌜SessionPure G st⌝ ∗
          ((ss ↦ₛ vecGhostHeaderBytes G.localIk) ∗ vecGhostHeap A G.localIk) ∗
          (((ss + 0x18#64) ↦ₛ vecGhostHeaderBytes G.remoteIk) ∗ vecGhostHeap A G.remoteIk) ∗
          (((ss + 0x30#64) ↦ₛ vecHeaderBytes G.root.cap G.root.ptr 32#64) ∗
            vecU8Buf A G.root.cap G.root.ptr (keyToBytes32 st.rootKey)) ∗
          (((ss + 0x48#64) ↦ₛ
              vecHeaderBytes G.chainsCap G.chainsPtr
                (BitVec.ofNat 64 (G.chains.zip st.receiverChains).length)) ∗
            vecBuf A 104 8 (chainAt A) G.chainsCap G.chainsPtr
              (G.chains.zip st.receiverChains)) ∗
          (((ss + 0x60#64) ↦ₛ vecGhostHeaderBytes G.alice) ∗ vecGhostHeap A G.alice) ∗
          (((ss + 0x78#64) ↦ₛ
              vecHeaderBytes G.pq.cap G.pq.ptr (BitVec.ofNat 64 st.pqRatchetState.length)) ∗
            vecU8Buf A G.pq.cap G.pq.ptr st.pqRatchetState) ∗
          (((ss + 0x90#64) ↦ₛ scBs) ∗ optSenderChainHeap A G.sender st.senderChain) ∗
          (((ss + 0xf8#64) ↦ₛ pendBs) ∗ optTailVecHeap A G.pending) ∗
          (((ss + 0x128#64) ↦ₛ kybBs) ∗ optTailVecHeap A G.kyber) ∗
          ((ss + 0x148#64) ↦ₛ sessionSuffixBytes G st)) := by
      ac_rfl
    rw [hpull]
    apply sepConj_mono_right
    apply sepConj_mono_right
    apply sepConj_mono_right
    apply sepConj_mono_right
    apply sepConj_mono_right
    apply sepConj_mono_right
    apply sepConj_mono_right
    refine sepConj_mono ?_ (sepConj_mono ?_ (sepConj_mono ?_ (Entails.refl _)))
    · refine Entails.sepExists_right scBs ?_
      exact Entails.pure_right ⟨hsc_len, hsc_inl⟩ (Entails.refl _)
    · refine Entails.sepExists_right pendBs ?_
      exact Entails.pure_right ⟨hpend_len, hpend_inl⟩ (Entails.refl _)
    · refine Entails.sepExists_right kybBs ?_
      exact Entails.pure_right ⟨hkyb_len, hkyb_inl⟩ (Entails.refl _)

theorem sessionStateAt_entails_inline_sep_heap (A : RustAlloc) (ss : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    sessionStateAt A ss G st ⊢
      ∃∗ bs : List (BitVec 8),
        ⌜bs.length = 344 ∧ SessionInline G st bs⌝ ∗ (ss ↦ₛ bs) ∗ sessionHeap A G st :=
  Entails.of_eq (sessionStateAt_eq_inline_sep_heap A ss G st)

/-- Reassemble `sessionStateAt A dst G st` from `(dst ↦ₛ bs) ∗ sessionHeap A G st`
given `SessionInline G st bs`. -/
theorem sessionStateAt_of_bytes (A : RustAlloc) (dst : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    {bs : List (BitVec 8)} (h : SessionInline G st bs) :
    ((dst ↦ₛ bs) ∗ sessionHeap A G st) ⊢ sessionStateAt A dst G st := by
  rw [sessionStateAt_eq_inline_sep_heap A dst G st]
  refine Entails.sepExists_right bs ?_
  exact Entails.pure_right ⟨h.length_eq, h⟩ (Entails.refl _)

/-- Forgetting the 344 inline bytes of `sessionStateAt` yields
`memRegion ss 344 ∗ sessionHeap A G st`. -/
theorem sessionStateAt_entails_memRegion_sep_heap (A : RustAlloc) (ss : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    sessionStateAt A ss G st ⊢ memRegion ss 344 ∗ sessionHeap A G st := by
  rw [sessionStateAt_eq_inline_sep_heap A ss G st]
  apply Entails.sepExists_elim; intro bs
  apply Entails.pure_left; rintro ⟨hlen, _⟩
  apply sepConj_mono_left
  have h := pointsToBytes_entails_memRegion ss bs
  rwa [hlen] at h

/-- Transfers `sessionStateAt A src G st` to `dst` given a copy `dst ↦ₛ bs` of its 344 inline bytes. -/
theorem sessionStateAt_move_bytes (A : RustAlloc) (src dst : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (bs : List (BitVec 8)) :
    SessionStateMoveStmt A src dst G st bs := by
  intro h
  have hpull :
      ((dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ sessionHeap A G st) =
      (((dst ↦ₛ bs) ∗ sessionHeap A G st) ∗ (src ↦ₛ bs)) := by
    ac_rfl
  rw [hpull]
  exact sepConj_mono_left (sessionStateAt_of_bytes A dst G st h)

/-- Move `sessionStateAt` from `src` to `dst` after copying `bs`, collapsing `src ↦ₛ bs` to
`memRegion src 344`. -/
theorem sessionStateAt_move_to_memRegion (A : RustAlloc) (src dst : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    {bs : List (BitVec 8)} (h : SessionInline G st bs) :
    ((dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ sessionHeap A G st) ⊢
      sessionStateAt A dst G st ∗ memRegion src 344 := by
  refine Entails.trans (sessionStateAt_move_bytes A src dst G st bs h) ?_
  apply sepConj_mono_right
  have hregion := pointsToBytes_entails_memRegion src bs
  rwa [h.length_eq] at hregion

/-- Two-hop raw-byte move `src → mid → dst` of `sessionStateAt`, collapsing `src` and `mid` to 344-byte `memRegion`s. -/
theorem sessionStateAt_move_bytes_twice (A : RustAlloc) (src mid dst : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    {bs : List (BitVec 8)} (h : SessionInline G st bs) :
    ((dst ↦ₛ bs) ∗ (mid ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ sessionHeap A G st) ⊢
      sessionStateAt A dst G st ∗ memRegion mid 344 ∗ memRegion src 344 := by
  have hpull :
      ((dst ↦ₛ bs) ∗ (mid ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ sessionHeap A G st) =
      (((dst ↦ₛ bs) ∗ (mid ↦ₛ bs) ∗ sessionHeap A G st) ∗ (src ↦ₛ bs)) := by
    ac_rfl
  rw [hpull]
  refine Entails.trans (sepConj_mono (sessionStateAt_move_to_memRegion A mid dst G st h) ?_)
    (Entails.of_eq (sepConj_assoc _ _ _))
  have hsrc := pointsToBytes_entails_memRegion src bs
  rwa [h.length_eq] at hsrc

/-- Splits a 344-byte list into two leading 128-bit quadwords and a 312-byte remainder. -/
theorem exists_split_344_as_2Q_312 {bs : List (BitVec 8)} (h : bs.length = 344) :
    ∃ (q0 q1 : BitVec 128) (rest : List (BitVec 8)),
      rest.length = 312 ∧
      bs = unpack128 q0 ++ unpack128 q1 ++ rest ∧
      ∀ a : BitVec 64,
        (a ↦ₛ bs) = (a ↦₁₂₈ q0) ∗ ((a + 0x10#64) ↦₁₂₈ q1) ∗ ((a + 0x20#64) ↦ₛ rest) := by
  have h0 : (bs.take 16).length = 16 := by simp [h]
  have h1 : ((bs.drop 16).take 16).length = 16 := by simp [h]
  have hrest : (bs.drop 32).length = 312 := by simp [h]
  obtain ⟨q0, hq0, _⟩ := exists_unpack128_of_length_16 h0
  obtain ⟨q1, hq1, _⟩ := exists_unpack128_of_length_16 h1
  have hbs : bs = unpack128 q0 ++ unpack128 q1 ++ bs.drop 32 := by
    rw [← hq0, ← hq1, List.append_assoc]
    have s1 : (bs.drop 16).take 16 ++ bs.drop 32 = bs.drop 16 := by
      have := List.take_append_drop 16 (bs.drop 16)
      rwa [List.drop_drop] at this
    rw [s1, List.take_append_drop]
  refine ⟨q0, q1, bs.drop 32, hrest, hbs, fun a => ?_⟩
  conv => lhs; rw [hbs]
  simp only [List.append_assoc, pointsToBytes_append, unpack128_length,
    ← pointsTo128_eq_pointsToBytes]
  have h10 : a + BitVec.ofNat 64 16 = a + 0x10#64 := rfl
  have h20 : a + 0x10#64 + BitVec.ofNat 64 16 = a + 0x20#64 := by bv_arith
  rw [h10, h20]

end CryptoVerification.LibsignalTripleRatchet.RawByteMove

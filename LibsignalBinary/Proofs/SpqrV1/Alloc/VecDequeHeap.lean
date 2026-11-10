/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Chain.Repr
public import ProofLib.SepLogic.Bytes

/-!
# Separation-Logic Byte Layout for `VecDeque<ChainEpoch>`

Splits `chainEpochAt A gce a` into its 112-byte flat struct representation
(`IsChainEpochBytes gce bs`) and detached `Vec<u8>` heap buffers (`chainEpochHeap A gce`),
connecting `vecDequeSlotsAt (chainEpochAt A) 112` to `arrayAt` and `memRegion` for
`VecDeque<ChainEpoch>::grow`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Alloc

open Arm64 ProofLib
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.ChainProofs

/-! ## `Vec` Header and Buffer Helpers -/

/-- 24 little-endian bytes of a `Vec` header `{cap, ptr, len}`. -/
def vecHeaderBytes (cap ptr len : BitVec 64) : List (BitVec 8) :=
  unpack64 cap ++ unpack64 ptr ++ unpack64 len

@[local simp]
theorem vecHeaderBytes_length (cap ptr len : BitVec 64) :
    (vecHeaderBytes cap ptr len).length = 24 := by
  simp [vecHeaderBytes]

theorem vecHeader_eq_pointsToBytes (v cap ptr len : BitVec 64) :
    vecHeader v cap ptr len = (v ↦ₛ vecHeaderBytes cap ptr len) := by
  unfold vecHeader vecHeaderBytes
  rw [List.append_assoc, pointsToBytes_append, pointsToBytes_append]
  simp only [unpack64_length]
  rw [← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes]
  have h16 : v + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 = v + 16#64 := by bv_arith
  rw [h16]

/-- Detached heap buffer of a `Vec<u8>`. -/
def vecU8Buf (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

theorem vecU8At_eq_header_sep_buf (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs = vecHeader v cap ptr (BitVec.ofNat 64 bs.length) ∗ vecU8Buf A cap ptr bs := by
  unfold vecU8At vecU8Buf
  ac_rfl

@[local simp]
theorem arrayAt_nil {α : Type} (elem : α → BitVec 64 → SepProp) (stride : Nat) (base : BitVec 64) :
    arrayAt elem stride base [] = emp := rfl

@[local simp]
theorem arrayAt_cons {α : Type} (elem : α → BitVec 64 → SepProp) (stride : Nat)
    (base : BitVec 64) (x : α) (xs : List α) :
    arrayAt elem stride base (x :: xs) =
      elem x base ∗ arrayAt elem stride (base + BitVec.ofNat 64 stride) xs := rfl

/-! ## `ChainEpoch` Flat 112-Byte Slice and Detached Heap Buffers -/

/-- 52-byte prefix of `ChainEpochDirection` (two 24-byte `Vec<u8>` headers plus 4-byte `ctr`). -/
def chainEpochDirHeaderBytes (g : ChainEpochDirectionGhost) (ced : ChainEpochDirection) :
    List (BitVec 8) :=
  vecHeaderBytes g.next.cap g.next.ptr (BitVec.ofNat 64 ced.next.length) ++
    (vecHeaderBytes g.prev.cap g.prev.ptr (BitVec.ofNat 64 ced.prev.data.length) ++
      unpack32 ced.ctr)

@[local simp]
theorem chainEpochDirHeaderBytes_length (g : ChainEpochDirectionGhost)
    (ced : ChainEpochDirection) :
    (chainEpochDirHeaderBytes g ced).length = 52 := by
  simp [chainEpochDirHeaderBytes]

/-- 56-byte in-struct representation of `ChainEpochDirection` with 4-byte tail padding `pad`. -/
def chainEpochDirBytes (g : ChainEpochDirectionGhost) (ced : ChainEpochDirection)
    (pad : List (BitVec 8)) : List (BitVec 8) :=
  chainEpochDirHeaderBytes g ced ++ pad

theorem chainEpochDirBytes_length (g : ChainEpochDirectionGhost) (ced : ChainEpochDirection)
    {pad : List (BitVec 8)} (hpad : pad.length = 4) :
    (chainEpochDirBytes g ced pad).length = 56 := by
  simp [chainEpochDirBytes, hpad]

/-- Detached heap buffers owned by a `ChainEpochDirection`. -/
def chainEpochDirHeap (A : RustAlloc) (g : ChainEpochDirectionGhost)
    (ced : ChainEpochDirection) : SepProp :=
  vecU8Buf A g.next.cap g.next.ptr ced.next ∗
    vecU8Buf A g.prev.cap g.prev.ptr ced.prev.data

theorem pointsToBytes_chainEpochDirHeaderBytes (g : ChainEpochDirectionGhost)
    (ced : ChainEpochDirection) (a : BitVec 64) :
    (a ↦ₛ chainEpochDirHeaderBytes g ced) =
      vecHeader a g.next.cap g.next.ptr (BitVec.ofNat 64 ced.next.length) ∗
        vecHeader (a + 0x18#64) g.prev.cap g.prev.ptr (BitVec.ofNat 64 ced.prev.data.length) ∗
        ((a + 0x30#64) ↦₃₂ ced.ctr) := by
  unfold chainEpochDirHeaderBytes
  rw [pointsToBytes_append, pointsToBytes_append]
  simp only [vecHeaderBytes_length]
  rw [← vecHeader_eq_pointsToBytes, ← vecHeader_eq_pointsToBytes, ← pointsTo32_eq_pointsToBytes]
  have h24 : a + BitVec.ofNat 64 24 = a + 0x18#64 := rfl
  have h48 : a + BitVec.ofNat 64 24 + BitVec.ofNat 64 24 = a + 0x30#64 := by bv_arith
  rw [h48, h24]

theorem chainEpochDirectionAt_eq_exists_bytes (A : RustAlloc) (a : BitVec 64)
    (g : ChainEpochDirectionGhost) (ced : ChainEpochDirection) :
    chainEpochDirectionAt A a g ced =
      (∃∗ pad : List (BitVec 8),
        ⌜pad.length = 4⌝ ∗ (a ↦ₛ chainEpochDirBytes g ced pad)) ∗
      chainEpochDirHeap A g ced := by
  unfold chainEpochDirectionAt keyHistoryAt chainEpochDirHeap
  rw [vecU8At_eq_header_sep_buf A a, vecU8At_eq_header_sep_buf A (a + 0x18#64),
      memRegion_eq_exists_bytes (a + 0x34#64) 4 (by decide)]
  have hpull :
      ((vecHeader a g.next.cap g.next.ptr (BitVec.ofNat 64 ced.next.length) ∗
          vecU8Buf A g.next.cap g.next.ptr ced.next) ∗
        (vecHeader (a + 0x18#64) g.prev.cap g.prev.ptr (BitVec.ofNat 64 ced.prev.data.length) ∗
          vecU8Buf A g.prev.cap g.prev.ptr ced.prev.data) ∗
        ((a + 0x30#64) ↦₃₂ ced.ctr) ∗
        (∃∗ pad : List (BitVec 8), ⌜pad.length = 4⌝ ∗ ((a + 0x34#64) ↦ₛ pad))) =
      ((vecHeader a g.next.cap g.next.ptr (BitVec.ofNat 64 ced.next.length) ∗
          vecHeader (a + 0x18#64) g.prev.cap g.prev.ptr (BitVec.ofNat 64 ced.prev.data.length) ∗
          ((a + 0x30#64) ↦₃₂ ced.ctr)) ∗
        (∃∗ pad : List (BitVec 8), ⌜pad.length = 4⌝ ∗ ((a + 0x34#64) ↦ₛ pad))) ∗
      (vecU8Buf A g.next.cap g.next.ptr ced.next ∗
        vecU8Buf A g.prev.cap g.prev.ptr ced.prev.data) := by
    ac_rfl
  rw [hpull, ← pointsToBytes_chainEpochDirHeaderBytes]
  congr 1
  rw [sepExists_sepConj_right]
  apply congrArg SepProp.sepExists
  funext pad
  have h52 : a + 0x34#64 = a + BitVec.ofNat 64 (chainEpochDirHeaderBytes g ced).length := by
    rw [chainEpochDirHeaderBytes_length]
  rw [sepConj_pure_left_comm, h52, ← pointsToBytes_append]
  rfl

/-- 112-byte in-buffer byte representation of a `ChainEpoch`. -/
inductive IsChainEpochBytes (gce : ChainEpochGhost × ChainEpoch) : List (BitVec 8) → Prop
  | mk {pad1 pad2 : List (BitVec 8)} (h1 : pad1.length = 4) (h2 : pad2.length = 4) :
      IsChainEpochBytes gce
        (chainEpochDirBytes gce.1.send gce.2.send pad1 ++
          chainEpochDirBytes gce.1.recv gce.2.recv pad2)

theorem IsChainEpochBytes.length_eq {gce : ChainEpochGhost × ChainEpoch} {bs : List (BitVec 8)}
    (h : IsChainEpochBytes gce bs) :
    bs.length = 112 := by
  cases h with
  | mk h1 h2 =>
    rw [List.length_append, chainEpochDirBytes_length _ _ h1, chainEpochDirBytes_length _ _ h2]

/-- Detached heap buffers owned by a `ChainEpoch`. -/
def chainEpochHeap (A : RustAlloc) (gce : ChainEpochGhost × ChainEpoch) : SepProp :=
  chainEpochDirHeap A gce.1.send gce.2.send ∗
    chainEpochDirHeap A gce.1.recv gce.2.recv

theorem chainEpochAt_entails_bytes (A : RustAlloc) (gce : ChainEpochGhost × ChainEpoch)
    (a : BitVec 64) :
    chainEpochAt A gce a ⊢
      (∃∗ bs : List (BitVec 8), ⌜IsChainEpochBytes gce bs⌝ ∗ (a ↦ₛ bs)) ∗
      chainEpochHeap A gce := by
  unfold chainEpochAt chainEpochHeap
  rw [chainEpochDirectionAt_eq_exists_bytes A a,
      chainEpochDirectionAt_eq_exists_bytes A (a + 0x38#64)]
  have hpull :
      (((∃∗ pad : List (BitVec 8),
          ⌜pad.length = 4⌝ ∗ (a ↦ₛ chainEpochDirBytes gce.1.send gce.2.send pad)) ∗
         chainEpochDirHeap A gce.1.send gce.2.send) ∗
       ((∃∗ pad : List (BitVec 8),
          ⌜pad.length = 4⌝ ∗ ((a + 0x38#64) ↦ₛ chainEpochDirBytes gce.1.recv gce.2.recv pad)) ∗
         chainEpochDirHeap A gce.1.recv gce.2.recv)) =
      (((∃∗ pad : List (BitVec 8),
          ⌜pad.length = 4⌝ ∗ (a ↦ₛ chainEpochDirBytes gce.1.send gce.2.send pad)) ∗
        (∃∗ pad : List (BitVec 8),
          ⌜pad.length = 4⌝ ∗ ((a + 0x38#64) ↦ₛ chainEpochDirBytes gce.1.recv gce.2.recv pad))) ∗
       (chainEpochDirHeap A gce.1.send gce.2.send ∗
         chainEpochDirHeap A gce.1.recv gce.2.recv)) := by
    ac_rfl
  rw [hpull]
  apply sepConj_mono_left
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim
  intro pad1
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim
  intro pad2
  have hpull2 :
      ((⌜pad1.length = 4⌝ ∗ (a ↦ₛ chainEpochDirBytes gce.1.send gce.2.send pad1)) ∗
        (⌜pad2.length = 4⌝ ∗ ((a + 0x38#64) ↦ₛ chainEpochDirBytes gce.1.recv gce.2.recv pad2))) =
      (⌜pad1.length = 4⌝ ∗
        (⌜pad2.length = 4⌝ ∗
          ((a ↦ₛ chainEpochDirBytes gce.1.send gce.2.send pad1) ∗
            ((a + 0x38#64) ↦ₛ chainEpochDirBytes gce.1.recv gce.2.recv pad2)))) := by
    ac_rfl
  rw [hpull2]
  apply Entails.pure_left
  intro h1
  apply Entails.pure_left
  intro h2
  apply Entails.sepExists_right
    (chainEpochDirBytes gce.1.send gce.2.send pad1 ++
      chainEpochDirBytes gce.1.recv gce.2.recv pad2)
  apply Entails.pure_right (IsChainEpochBytes.mk h1 h2)
  rw [pointsToBytes_append, chainEpochDirBytes_length _ _ h1]
  exact Entails.refl _

theorem chainEpochAt_of_bytes (A : RustAlloc) (gce : ChainEpochGhost × ChainEpoch)
    (a : BitVec 64) {bs : List (BitVec 8)} (hbs : IsChainEpochBytes gce bs) :
    ((a ↦ₛ bs) ∗ chainEpochHeap A gce) ⊢ chainEpochAt A gce a := by
  cases hbs with
  | @mk pad1 pad2 h1 h2 =>
    unfold chainEpochAt chainEpochHeap
    rw [chainEpochDirectionAt_eq_exists_bytes A a,
        chainEpochDirectionAt_eq_exists_bytes A (a + 0x38#64),
        pointsToBytes_append, chainEpochDirBytes_length _ _ h1]
    have h56 : a + BitVec.ofNat 64 56 = a + 0x38#64 := rfl
    rw [h56]
    have hpull :
        (((a ↦ₛ chainEpochDirBytes gce.1.send gce.2.send pad1) ∗
          ((a + 0x38#64) ↦ₛ chainEpochDirBytes gce.1.recv gce.2.recv pad2)) ∗
         (chainEpochDirHeap A gce.1.send gce.2.send ∗
          chainEpochDirHeap A gce.1.recv gce.2.recv)) =
        (((a ↦ₛ chainEpochDirBytes gce.1.send gce.2.send pad1) ∗
          chainEpochDirHeap A gce.1.send gce.2.send) ∗
         (((a + 0x38#64) ↦ₛ chainEpochDirBytes gce.1.recv gce.2.recv pad2) ∗
          chainEpochDirHeap A gce.1.recv gce.2.recv)) := by
      ac_rfl
    rw [hpull]
    exact sepConj_mono
      (sepConj_mono_left (Entails.sepExists_right pad1 (Entails.pure_right h1 (Entails.refl _))))
      (sepConj_mono_left (Entails.sepExists_right pad2 (Entails.pure_right h2 (Entails.refl _))))

def chainEpochHeaps (A : RustAlloc) : List (ChainEpochGhost × ChainEpoch) → SepProp
  | [] => emp
  | gce :: gces => chainEpochHeap A gce ∗ chainEpochHeaps A gces

@[local simp]
theorem chainEpochHeaps_nil (A : RustAlloc) : chainEpochHeaps A [] = emp := rfl

@[local simp]
theorem chainEpochHeaps_cons (A : RustAlloc) (gce : ChainEpochGhost × ChainEpoch)
    (gces : List (ChainEpochGhost × ChainEpoch)) :
    chainEpochHeaps A (gce :: gces) = chainEpochHeap A gce ∗ chainEpochHeaps A gces := rfl

theorem chainEpochHeaps_append (A : RustAlloc)
    (xs ys : List (ChainEpochGhost × ChainEpoch)) :
    chainEpochHeaps A (xs ++ ys) = chainEpochHeaps A xs ∗ chainEpochHeaps A ys := by
  induction xs with
  | nil => simp [chainEpochHeaps]
  | cons x xs ih => simp [chainEpochHeaps, ih, sepConj_assoc]

/-- Relates a list of `ChainEpoch` values to their flat `112 * length`-byte slice. -/
inductive ChainEpochArrayBytes : List (ChainEpochGhost × ChainEpoch) → List (BitVec 8) → Prop
  | nil : ChainEpochArrayBytes [] []
  | cons {gce : ChainEpochGhost × ChainEpoch} {gces : List (ChainEpochGhost × ChainEpoch)}
      {bs1 bs : List (BitVec 8)}
      (h1 : IsChainEpochBytes gce bs1)
      (hrest : ChainEpochArrayBytes gces bs) :
      ChainEpochArrayBytes (gce :: gces) (bs1 ++ bs)

namespace ChainEpochArrayBytes

theorem length_eq {gces : List (ChainEpochGhost × ChainEpoch)} {bs : List (BitVec 8)}
    (h : ChainEpochArrayBytes gces bs) :
    bs.length = gces.length * 112 := by
  induction h with
  | nil => rfl
  | @cons gce gces bs1 bs h1 _ ih =>
    rw [List.length_append, h1.length_eq, ih, List.length_cons, Nat.succ_mul]
    omega

theorem append {xs ys : List (ChainEpochGhost × ChainEpoch)} {bs1 bs2 : List (BitVec 8)}
    (h1 : ChainEpochArrayBytes xs bs1) (h2 : ChainEpochArrayBytes ys bs2) :
    ChainEpochArrayBytes (xs ++ ys) (bs1 ++ bs2) := by
  induction h1 with
  | nil => simpa using h2
  | @cons gce gces b1 bs hce _ ih =>
    rw [List.cons_append, List.append_assoc]
    exact .cons hce ih

end ChainEpochArrayBytes

theorem arrayAt_chainEpochAt_entails_bytes (A : RustAlloc) (base : BitVec 64)
    (gces : List (ChainEpochGhost × ChainEpoch)) :
    arrayAt (chainEpochAt A) 112 base gces ⊢
      (∃∗ bs : List (BitVec 8), ⌜ChainEpochArrayBytes gces bs⌝ ∗ (base ↦ₛ bs)) ∗
        chainEpochHeaps A gces := by
  induction gces generalizing base with
  | nil =>
    simp only [arrayAt_nil, chainEpochHeaps_nil, sepConj_emp]
    apply Entails.sepExists_right []
    apply Entails.pure_right ChainEpochArrayBytes.nil
    rw [pointsToBytes_nil]
    exact Entails.refl _
  | cons gce gces ih =>
    rw [arrayAt_cons, chainEpochHeaps_cons]
    refine Entails.trans
      (sepConj_mono (chainEpochAt_entails_bytes A gce base)
        (ih (base + BitVec.ofNat 64 112))) ?_
    have hpull :
        (((∃∗ bs1 : List (BitVec 8),
            ⌜IsChainEpochBytes gce bs1⌝ ∗ (base ↦ₛ bs1)) ∗
           chainEpochHeap A gce) ∗
         ((∃∗ bs : List (BitVec 8), ⌜ChainEpochArrayBytes gces bs⌝ ∗
            ((base + BitVec.ofNat 64 112) ↦ₛ bs)) ∗
          chainEpochHeaps A gces)) =
        (((∃∗ bs1 : List (BitVec 8),
            ⌜IsChainEpochBytes gce bs1⌝ ∗ (base ↦ₛ bs1)) ∗
          (∃∗ bs : List (BitVec 8), ⌜ChainEpochArrayBytes gces bs⌝ ∗
            ((base + BitVec.ofNat 64 112) ↦ₛ bs))) ∗
         (chainEpochHeap A gce ∗ chainEpochHeaps A gces)) := by
      ac_rfl
    rw [hpull]
    apply sepConj_mono_left
    rw [sepExists_sepConj_left]
    apply Entails.sepExists_elim
    intro bs1
    rw [sepExists_sepConj_right]
    apply Entails.sepExists_elim
    intro bs
    have hpull2 :
        ((⌜IsChainEpochBytes gce bs1⌝ ∗ (base ↦ₛ bs1)) ∗
          (⌜ChainEpochArrayBytes gces bs⌝ ∗ ((base + BitVec.ofNat 64 112) ↦ₛ bs))) =
        (⌜IsChainEpochBytes gce bs1⌝ ∗
          (⌜ChainEpochArrayBytes gces bs⌝ ∗
            ((base ↦ₛ bs1) ∗ ((base + BitVec.ofNat 64 112) ↦ₛ bs)))) := by
      ac_rfl
    rw [hpull2]
    apply Entails.pure_left
    intro h1
    apply Entails.pure_left
    intro hrest
    apply Entails.sepExists_right (bs1 ++ bs)
    apply Entails.pure_right (.cons h1 hrest)
    rw [pointsToBytes_append, h1.length_eq]
    exact Entails.refl _

theorem arrayAt_chainEpochAt_of_bytes (A : RustAlloc) (base : BitVec 64)
    {gces : List (ChainEpochGhost × ChainEpoch)} {bs : List (BitVec 8)}
    (hbs : ChainEpochArrayBytes gces bs) :
    ((base ↦ₛ bs) ∗ chainEpochHeaps A gces) ⊢ arrayAt (chainEpochAt A) 112 base gces := by
  induction hbs generalizing base with
  | nil =>
    simp only [pointsToBytes_nil, chainEpochHeaps_nil, arrayAt_nil, emp_sepConj]
    exact Entails.refl _
  | @cons gce gces bs1 bs' h1 _ ih =>
    rw [pointsToBytes_append, h1.length_eq, chainEpochHeaps_cons, arrayAt_cons]
    have hpull :
        (((base ↦ₛ bs1) ∗ ((base + BitVec.ofNat 64 112) ↦ₛ bs')) ∗
          (chainEpochHeap A gce ∗ chainEpochHeaps A gces)) =
        (((base ↦ₛ bs1) ∗ chainEpochHeap A gce) ∗
          (((base + BitVec.ofNat 64 112) ↦ₛ bs') ∗ chainEpochHeaps A gces)) := by
      ac_rfl
    rw [hpull]
    exact sepConj_mono (chainEpochAt_of_bytes A gce base h1) (ih (base + BitVec.ofNat 64 112))

/-! ## `vecDequeSlotsAt` Range Splitting -/

theorem vecDequeSlotsAt_add {α : Type} (elem : α → BitVec 64 → SepProp) (stride cap head : Nat)
    (ptr : BitVec 64) (xs : List α) (s m n : Nat) :
    vecDequeSlotsAt elem stride cap head ptr xs s (m + n) =
      vecDequeSlotsAt elem stride cap head ptr xs s m ∗
        vecDequeSlotsAt elem stride cap head ptr xs (s + m) n := by
  induction m generalizing s with
  | zero =>
    simp [vecDequeSlotsAt]
  | succ m ih =>
    rw [Nat.succ_add, vecDequeSlotsAt, vecDequeSlotsAt, ih (s + 1), sepConj_assoc]
    have hsm : s + 1 + m = s + (m + 1) := by omega
    rw [hsm]

theorem vecDequeSlotsAt_occupied_eq_arrayAt {α : Type} (elem : α → BitVec 64 → SepProp)
    (stride cap head : Nat) (ptr : BitVec 64) (xs : List α) (s i0 n : Nat)
    (hi : i0 + n ≤ xs.length)
    (hidx : ∀ k < n, vecDequeLogIdx head cap (s + k) = i0 + k) :
    vecDequeSlotsAt elem stride cap head ptr xs s n =
      arrayAt elem stride (ptr + BitVec.ofNat 64 (s * stride)) ((xs.drop i0).take n) := by
  induction n generalizing s i0 with
  | zero =>
    simp [vecDequeSlotsAt]
  | succ n ih =>
    have h0 : vecDequeLogIdx head cap s = i0 := by
      have := hidx 0 (Nat.zero_lt_succ n)
      omega
    have hi0 : i0 < xs.length := by omega
    have hdrop : xs.drop i0 = xs[i0] :: xs.drop (i0 + 1) := List.drop_eq_getElem_cons hi0
    rw [vecDequeSlotsAt, hdrop, List.take_succ_cons, arrayAt_cons]
    simp only [h0, hi0, ↓reduceDIte]
    have hadj : ptr + BitVec.ofNat 64 (s * stride) + BitVec.ofNat 64 stride =
        ptr + BitVec.ofNat 64 ((s + 1) * stride) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.succ_mul]
    rw [hadj, ih (s + 1) (i0 + 1) (by omega)]
    intro k hk
    have hk' := hidx (k + 1) (by omega)
    have hsk : s + 1 + k = s + (k + 1) := by omega
    have hik : i0 + 1 + k = i0 + (k + 1) := by omega
    rw [hsk, hik, hk']

theorem memRegion_entails_vecDequeSlotsAt_uninit {α : Type}
    (elem : α → BitVec 64 → SepProp) (stride cap head : Nat)
    (ptr : BitVec 64) (xs : List α) (s n : Nat)
    (hbound : n * stride ≤ 2 ^ 64)
    (huninit : ∀ k < n, ¬ vecDequeLogIdx head cap (s + k) < xs.length) :
    memRegion (ptr + BitVec.ofNat 64 (s * stride)) (n * stride) ⊢
      vecDequeSlotsAt elem stride cap head ptr xs s n := by
  induction n generalizing s with
  | zero =>
    simp only [Nat.zero_mul, memRegion_zero, vecDequeSlotsAt]
    exact Entails.refl _
  | succ n ih =>
    have h0 : ¬ vecDequeLogIdx head cap s < xs.length := by
      have := huninit 0 (Nat.zero_lt_succ n)
      simpa using this
    have hsucc : (n + 1) * stride = stride + n * stride := by
      rw [Nat.succ_mul, Nat.add_comm]
    rw [hsucc]
    have hsplit := memRegion_split (ptr + BitVec.ofNat 64 (s * stride)) stride (n * stride)
      (by omega)
    rw [hsplit, vecDequeSlotsAt]
    simp only [h0, ↓reduceDIte]
    have hadj : ptr + BitVec.ofNat 64 (s * stride) + BitVec.ofNat 64 stride =
        ptr + BitVec.ofNat 64 ((s + 1) * stride) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.succ_mul]
    rw [hadj]
    refine sepConj_mono_right (ih (s + 1) (by omega) ?_)
    intro k hk
    have hk' := huninit (k + 1) (by omega)
    have hsk : s + 1 + k = s + (k + 1) := by omega
    rwa [hsk]

/-! ## `vecDequeAt` Decomposition and Reassembly for `grow` -/

/-- Non-wrapping (`head = 0#64`) precondition decomposition of a full `VecDeque<ChainEpoch>`. -/
theorem vecDequeAt_head_zero_entails_bytes (A : RustAlloc)
    (v cap ptr : BitVec 64) (xs : List (ChainEpochGhost × ChainEpoch))
    (hlen : xs.length = cap.toNat) :
    vecDequeAt A chainEpochSize chainEpochAlign (chainEpochAt A) v cap ptr 0#64 xs ⊢
      ∃∗ bs : List (BitVec 8),
        ⌜ChainEpochArrayBytes xs bs ∧ bs.length = cap.toNat * 112 ∧ ptr ≠ 0#64⌝ ∗
        (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ 0#64) ∗ ((v + 24#64) ↦₆₄ cap) ∗
        (if cap = 0#64 then emp
         else A.live ptr (cap.toNat * 112) 8 ∗ (ptr ↦ₛ bs) ∗
           memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat * 112 - bs.length)) ∗
        chainEpochHeaps A xs := by
  unfold vecDequeAt vecDequeHeader vecDequeRingBuf chainEpochSize chainEpochAlign
  have hlen_bv : BitVec.ofNat 64 xs.length = cap := by
    rw [hlen, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [hlen_bv, sepConj_pure_left_comm]
  apply Entails.pure_left
  rintro ⟨_, _, hptr, _⟩
  by_cases hcap : cap = 0
  · subst hcap
    have hxs : xs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    subst hxs
    simp only [↓reduceIte, chainEpochHeaps_nil, sepConj_emp]
    apply Entails.sepExists_right []
    exact Entails.pure_right ⟨ChainEpochArrayBytes.nil, rfl, hptr⟩
      (Entails.of_eq (by ac_rfl))
  · have hcap' : cap ≠ 0#64 := hcap
    simp only [hcap, hcap', ↓reduceIte]
    have hslots :
        vecDequeSlotsAt (chainEpochAt A) 112 cap.toNat (0#64).toNat ptr xs 0 cap.toNat =
          arrayAt (chainEpochAt A) 112 ptr xs := by
      change vecDequeSlotsAt (chainEpochAt A) 112 cap.toNat 0 ptr xs 0 cap.toNat =
        arrayAt (chainEpochAt A) 112 ptr xs
      rw [vecDequeSlotsAt_occupied_eq_arrayAt (chainEpochAt A) 112 cap.toNat 0 ptr xs 0 0 cap.toNat
        (by omega)]
      · simp [← hlen]
      · intro k _
        simp [vecDequeLogIdx]
    rw [hslots]
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_right (arrayAt_chainEpochAt_entails_bytes A ptr xs))) ?_
    rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right]
    apply Entails.sepExists_elim
    intro bs
    have hpull :
        ((v ↦₆₄ cap ∗ (v + 8#64) ↦₆₄ ptr ∗ (v + 16#64) ↦₆₄ 0#64 ∗ (v + 24#64) ↦₆₄ cap) ∗
          (A.live ptr (cap.toNat * 112) 8 ∗
            ((⌜ChainEpochArrayBytes xs bs⌝ ∗ (ptr ↦ₛ bs)) ∗ chainEpochHeaps A xs))) =
        (⌜ChainEpochArrayBytes xs bs⌝ ∗
          ((v ↦₆₄ cap ∗ (v + 8#64) ↦₆₄ ptr ∗ (v + 16#64) ↦₆₄ 0#64 ∗ (v + 24#64) ↦₆₄ cap) ∗
            (A.live ptr (cap.toNat * 112) 8 ∗ (ptr ↦ₛ bs)) ∗ chainEpochHeaps A xs)) := by
      ac_rfl
    rw [hpull]
    apply Entails.pure_left
    intro hbs
    have hbs_len : bs.length = cap.toNat * 112 := by rw [hbs.length_eq, hlen]
    apply Entails.sepExists_right bs
    apply Entails.pure_right ⟨hbs, hbs_len, hptr⟩
    have hsub : cap.toNat * 112 - bs.length = 0 := by omega
    rw [hsub, memRegion_zero, sepConj_emp]
    exact Entails.of_eq (by ac_rfl)

/-- Non-wrapping (`head = 0#64`) postcondition reassembly after `grow`. -/
theorem vecDequeAt_head_zero_of_post (A : RustAlloc)
    (v cap p' : BitVec 64) (xs : List (ChainEpochGhost × ChainEpoch))
    {bs : List (BitVec 8)}
    (hlen : xs.length = cap.toNat)
    (hbs : ChainEpochArrayBytes xs bs)
    (hmax_lt : max (2 * cap.toNat) 4 * 112 < 2 ^ 63)
    (hp' : p' ≠ 0#64) :
    ((v ↦₆₄ BitVec.ofNat 64 (max (2 * cap.toNat) 4)) ∗ ((v + 8#64) ↦₆₄ p') ∗
      ((v + 16#64) ↦₆₄ 0#64) ∗ ((v + 24#64) ↦₆₄ cap) ∗
      A.live p' (max (2 * cap.toNat) 4 * 112) 8 ∗
      (p' ↦ₛ bs) ∗
      memRegion (p' + BitVec.ofNat 64 bs.length) (max (2 * cap.toNat) 4 * 112 - bs.length) ∗
      chainEpochHeaps A xs) ⊢
    vecDequeAt A chainEpochSize chainEpochAlign (chainEpochAt A)
      v (BitVec.ofNat 64 (max (2 * cap.toNat) 4)) p' 0#64 xs := by
  let newCap := max (2 * cap.toNat) 4
  have hnc_def : newCap = max (2 * cap.toNat) 4 := rfl
  have hnc_toNat : (BitVec.ofNat 64 newCap).toNat = newCap := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hnc_ne : BitVec.ofNat 64 newCap ≠ 0 := by
    intro h0
    have := congrArg BitVec.toNat h0
    rw [hnc_toNat] at this
    change newCap = 0 at this
    omega
  have hlen_bv : BitVec.ofNat 64 xs.length = cap := by
    rw [hlen, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  unfold vecDequeAt vecDequeHeader vecDequeRingBuf chainEpochSize chainEpochAlign
  rw [hlen_bv, sepConj_pure_left_comm]
  simp only [← hnc_def, hnc_ne, ↓reduceIte, hnc_toNat]
  apply Entails.pure_right ⟨by omega, hmax_lt, hp', by change 0 < newCap; omega⟩
  have hslots_split :
      vecDequeSlotsAt (chainEpochAt A) 112 newCap (0#64).toNat p' xs 0 newCap =
        vecDequeSlotsAt (chainEpochAt A) 112 newCap (0#64).toNat p' xs 0 cap.toNat ∗
          vecDequeSlotsAt (chainEpochAt A) 112 newCap (0#64).toNat p' xs (0 + cap.toNat)
            (newCap - cap.toNat) := by
    rw [← vecDequeSlotsAt_add]
    congr 1
    omega
  have hslots1 :
      vecDequeSlotsAt (chainEpochAt A) 112 newCap (0#64).toNat p' xs 0 cap.toNat =
        arrayAt (chainEpochAt A) 112 p' xs := by
    change vecDequeSlotsAt (chainEpochAt A) 112 newCap 0 p' xs 0 cap.toNat =
      arrayAt (chainEpochAt A) 112 p' xs
    rw [vecDequeSlotsAt_occupied_eq_arrayAt (chainEpochAt A) 112 newCap 0 p' xs 0 0 cap.toNat
      (by omega)]
    · simp [← hlen]
    · intro k _
      simp [vecDequeLogIdx]
  have hslots2 :
      memRegion (p' + BitVec.ofNat 64 bs.length) (newCap * 112 - bs.length) ⊢
        vecDequeSlotsAt (chainEpochAt A) 112 newCap (0#64).toNat p' xs (0 + cap.toNat)
          (newCap - cap.toNat) := by
    have hbs_len : bs.length = (0 + cap.toNat) * 112 := by
      rw [Nat.zero_add, hbs.length_eq, hlen]
    have hrem : newCap * 112 - bs.length = (newCap - cap.toNat) * 112 := by
      rw [hbs.length_eq, hlen, Nat.sub_mul]
    rw [hrem, hbs_len]
    refine memRegion_entails_vecDequeSlotsAt_uninit (chainEpochAt A) 112 newCap 0 p' xs
      (0 + cap.toNat) (newCap - cap.toNat) (by omega) ?_
    intro k _
    simp only [vecDequeLogIdx, Nat.zero_le, ↓reduceIte, Nat.sub_zero, hlen]
    omega
  rw [hslots_split, hslots1]
  have h1 := arrayAt_chainEpochAt_of_bytes A p' hbs
  have hpull :
      ((v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
        ((v + 16#64) ↦₆₄ 0#64) ∗ ((v + 24#64) ↦₆₄ cap) ∗
        A.live p' (newCap * 112) 8 ∗
        (p' ↦ₛ bs) ∗
        memRegion (p' + BitVec.ofNat 64 bs.length) (newCap * 112 - bs.length) ∗
        chainEpochHeaps A xs) =
      (((v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
        ((v + 16#64) ↦₆₄ 0#64) ∗ ((v + 24#64) ↦₆₄ cap)) ∗
       (A.live p' (newCap * 112) 8 ∗
         (((p' ↦ₛ bs) ∗ chainEpochHeaps A xs) ∗
          memRegion (p' + BitVec.ofNat 64 bs.length) (newCap * 112 - bs.length)))) := by
    ac_rfl
  rw [hpull]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono h1 hslots2))

/-- Wrapping (`0 < head.toNat`) precondition decomposition of a full `VecDeque<ChainEpoch>`. -/
theorem vecDequeAt_wrap_entails_bytes (A : RustAlloc)
    (v cap ptr head : BitVec 64) (xs : List (ChainEpochGhost × ChainEpoch))
    (hlen : xs.length = cap.toNat) (hhead_pos : 0 < head.toNat) :
    vecDequeAt A chainEpochSize chainEpochAlign (chainEpochAt A) v cap ptr head xs ⊢
      ∃∗ bs_back : List (BitVec 8), ∃∗ bs_front : List (BitVec 8),
        ⌜head.toNat < cap.toNat ∧ ptr ≠ 0#64 ∧
          ChainEpochArrayBytes (xs.drop (cap.toNat - head.toNat)) bs_back ∧
          ChainEpochArrayBytes (xs.take (cap.toNat - head.toNat)) bs_front ∧
          bs_back.length = head.toNat * 112 ∧
          bs_front.length = (cap.toNat - head.toNat) * 112⌝ ∗
        (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ head) ∗ ((v + 24#64) ↦₆₄ cap) ∗
        A.live ptr (cap.toNat * 112) 8 ∗
        (ptr ↦ₛ (bs_back ++ bs_front)) ∗
        chainEpochHeaps A (xs.drop (cap.toNat - head.toNat)) ∗
        chainEpochHeaps A (xs.take (cap.toNat - head.toNat)) := by
  unfold vecDequeAt vecDequeHeader vecDequeRingBuf chainEpochSize chainEpochAlign
  have hlen_bv : BitVec.ofNat 64 xs.length = cap := by
    rw [hlen, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [hlen_bv, sepConj_pure_left_comm]
  apply Entails.pure_left
  rintro ⟨_, _, hptr, hhead_if⟩
  have hcap : cap ≠ 0 := by
    intro h0
    simp only [h0, ↓reduceIte] at hhead_if
    rw [hhead_if] at hhead_pos
    change 0 < 0 at hhead_pos
    omega
  simp only [hcap, ↓reduceIte] at hhead_if ⊢
  have hslots_split :
      vecDequeSlotsAt (chainEpochAt A) 112 cap.toNat head.toNat ptr xs 0 cap.toNat =
        vecDequeSlotsAt (chainEpochAt A) 112 cap.toNat head.toNat ptr xs 0 head.toNat ∗
          vecDequeSlotsAt (chainEpochAt A) 112 cap.toNat head.toNat ptr xs (0 + head.toNat)
            (cap.toNat - head.toNat) := by
    rw [← vecDequeSlotsAt_add]
    congr 1
    omega
  have hslots_back :
      vecDequeSlotsAt (chainEpochAt A) 112 cap.toNat head.toNat ptr xs 0 head.toNat =
        arrayAt (chainEpochAt A) 112 ptr (xs.drop (cap.toNat - head.toNat)) := by
    rw [vecDequeSlotsAt_occupied_eq_arrayAt (chainEpochAt A) 112 cap.toNat head.toNat ptr xs
      0 (cap.toNat - head.toNat) head.toNat (by omega)]
    · have htake : (xs.drop (cap.toNat - head.toNat)).take head.toNat =
          xs.drop (cap.toNat - head.toNat) :=
        List.take_of_length_le (by rw [List.length_drop, hlen]; omega)
      simp [htake]
    · intro k hk
      have hnot : ¬ head.toNat ≤ 0 + k := by omega
      simp only [vecDequeLogIdx, hnot, ↓reduceIte]
      omega
  have hslots_front :
      vecDequeSlotsAt (chainEpochAt A) 112 cap.toNat head.toNat ptr xs (0 + head.toNat)
        (cap.toNat - head.toNat) =
        arrayAt (chainEpochAt A) 112 (ptr + BitVec.ofNat 64 (head.toNat * 112))
          (xs.take (cap.toNat - head.toNat)) := by
    rw [Nat.zero_add,
      vecDequeSlotsAt_occupied_eq_arrayAt (chainEpochAt A) 112 cap.toNat head.toNat ptr xs
        head.toNat 0 (cap.toNat - head.toNat) (by omega)]
    · simp
    · intro k _
      have hle : head.toNat ≤ head.toNat + k := by omega
      simp only [vecDequeLogIdx, hle, ↓reduceIte]
      omega
  rw [hslots_split, hslots_back, hslots_front]
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono
        (arrayAt_chainEpochAt_entails_bytes A ptr (xs.drop (cap.toNat - head.toNat)))
        (arrayAt_chainEpochAt_entails_bytes A (ptr + BitVec.ofNat 64 (head.toNat * 112))
          (xs.take (cap.toNat - head.toNat)))))) ?_
  rw [sepExists_sepConj_left, sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim
  intro bs_back
  rw [sepExists_sepConj_left, sepExists_sepConj_right,
      sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim
  intro bs_front
  have hpull :
      ((v ↦₆₄ cap ∗ (v + 8#64) ↦₆₄ ptr ∗ (v + 16#64) ↦₆₄ head ∗ (v + 24#64) ↦₆₄ cap) ∗
        (A.live ptr (cap.toNat * 112) 8 ∗
          (((⌜ChainEpochArrayBytes (xs.drop (cap.toNat - head.toNat)) bs_back⌝ ∗ (ptr ↦ₛ bs_back)) ∗
            chainEpochHeaps A (xs.drop (cap.toNat - head.toNat))) ∗
           ((⌜ChainEpochArrayBytes (xs.take (cap.toNat - head.toNat)) bs_front⌝ ∗
             ((ptr + BitVec.ofNat 64 (head.toNat * 112)) ↦ₛ bs_front)) ∗
            chainEpochHeaps A (xs.take (cap.toNat - head.toNat)))))) =
      (⌜ChainEpochArrayBytes (xs.drop (cap.toNat - head.toNat)) bs_back⌝ ∗
        (⌜ChainEpochArrayBytes (xs.take (cap.toNat - head.toNat)) bs_front⌝ ∗
          ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ head) ∗ ((v + 24#64) ↦₆₄ cap) ∗
           A.live ptr (cap.toNat * 112) 8 ∗
           ((ptr ↦ₛ bs_back) ∗ ((ptr + BitVec.ofNat 64 (head.toNat * 112)) ↦ₛ bs_front)) ∗
           chainEpochHeaps A (xs.drop (cap.toNat - head.toNat)) ∗
           chainEpochHeaps A (xs.take (cap.toNat - head.toNat))))) := by
    ac_rfl
  rw [hpull]
  apply Entails.pure_left
  intro hbs_back
  apply Entails.pure_left
  intro hbs_front
  have hlen_back : bs_back.length = head.toNat * 112 := by
    rw [hbs_back.length_eq, List.length_drop, hlen]
    have : cap.toNat - (cap.toNat - head.toNat) = head.toNat := by omega
    rw [this]
  have hlen_front : bs_front.length = (cap.toNat - head.toNat) * 112 := by
    rw [hbs_front.length_eq, List.length_take_of_le (by omega)]
  apply Entails.sepExists_right bs_back
  apply Entails.sepExists_right bs_front
  apply Entails.pure_right ⟨hhead_if, hptr, hbs_back, hbs_front, hlen_back, hlen_front⟩
  rw [pointsToBytes_append, hlen_back]
  exact Entails.of_eq (by ac_rfl)

/-- Wrapping `memcpy` (`head < cap - head`) postcondition reassembly. -/
theorem vecDequeAt_wrap_memcpy_of_post (A : RustAlloc)
    (v cap p' head : BitVec 64) (xs : List (ChainEpochGhost × ChainEpoch))
    {bs_back bs_front : List (BitVec 8)}
    (hlen : xs.length = cap.toNat)
    (hhead_pos : 0 < head.toNat)
    (hhead_lt : head.toNat < cap.toNat - head.toNat)
    (hbs_back : ChainEpochArrayBytes (xs.drop (cap.toNat - head.toNat)) bs_back)
    (hbs_front : ChainEpochArrayBytes (xs.take (cap.toNat - head.toNat)) bs_front)
    (hmax_lt : max (2 * cap.toNat) 4 * 112 < 2 ^ 63)
    (hp' : p' ≠ 0#64) :
    ((v ↦₆₄ BitVec.ofNat 64 (max (2 * cap.toNat) 4)) ∗ ((v + 8#64) ↦₆₄ p') ∗
      ((v + 16#64) ↦₆₄ head) ∗ ((v + 24#64) ↦₆₄ cap) ∗
      A.live p' (max (2 * cap.toNat) 4 * 112) 8 ∗
      memRegion p' (head.toNat * 112) ∗
      ((p' + BitVec.ofNat 64 (head.toNat * 112)) ↦ₛ (bs_front ++ bs_back)) ∗
      memRegion (p' + BitVec.ofNat 64 ((cap.toNat + head.toNat) * 112))
        ((max (2 * cap.toNat) 4 - (cap.toNat + head.toNat)) * 112) ∗
      chainEpochHeaps A (xs.drop (cap.toNat - head.toNat)) ∗
      chainEpochHeaps A (xs.take (cap.toNat - head.toNat))) ⊢
    vecDequeAt A chainEpochSize chainEpochAlign (chainEpochAt A)
      v (BitVec.ofNat 64 (max (2 * cap.toNat) 4)) p' head xs := by
  let newCap := max (2 * cap.toNat) 4
  have hnc_def : newCap = max (2 * cap.toNat) 4 := rfl
  have hnc_toNat : (BitVec.ofNat 64 newCap).toNat = newCap := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hnc_ne : BitVec.ofNat 64 newCap ≠ 0 := by
    intro h0
    have := congrArg BitVec.toNat h0
    rw [hnc_toNat] at this
    change newCap = 0 at this
    omega
  have hlen_bv : BitVec.ofNat 64 xs.length = cap := by
    rw [hlen, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  unfold vecDequeAt vecDequeHeader vecDequeRingBuf chainEpochSize chainEpochAlign
  rw [hlen_bv, sepConj_pure_left_comm]
  simp only [← hnc_def, hnc_ne, ↓reduceIte, hnc_toNat]
  apply Entails.pure_right ⟨by omega, hmax_lt, hp', by omega⟩
  have hslots_split :
      vecDequeSlotsAt (chainEpochAt A) 112 newCap head.toNat p' xs 0 newCap =
        vecDequeSlotsAt (chainEpochAt A) 112 newCap head.toNat p' xs 0 head.toNat ∗
          (vecDequeSlotsAt (chainEpochAt A) 112 newCap head.toNat p' xs (0 + head.toNat) cap.toNat ∗
            vecDequeSlotsAt (chainEpochAt A) 112 newCap head.toNat p' xs
              (0 + head.toNat + cap.toNat) (newCap - (cap.toNat + head.toNat))) := by
    rw [← vecDequeSlotsAt_add, ← vecDequeSlotsAt_add]
    congr 1
    omega
  have hslots1 :
      memRegion p' (head.toNat * 112) ⊢
        vecDequeSlotsAt (chainEpochAt A) 112 newCap head.toNat p' xs 0 head.toNat := by
    have hp0 : p' = p' + BitVec.ofNat 64 (0 * 112) := by simp
    conv => lhs; rw [hp0]
    refine memRegion_entails_vecDequeSlotsAt_uninit (chainEpochAt A) 112 newCap head.toNat p' xs
      0 head.toNat (by omega) ?_
    intro k hk
    have hnot : ¬ head.toNat ≤ 0 + k := by omega
    simp only [vecDequeLogIdx, hnot, ↓reduceIte, hlen]
    omega
  have hslots2 :
      vecDequeSlotsAt (chainEpochAt A) 112 newCap head.toNat p' xs (0 + head.toNat) cap.toNat =
        arrayAt (chainEpochAt A) 112 (p' + BitVec.ofNat 64 (head.toNat * 112)) xs := by
    rw [Nat.zero_add,
      vecDequeSlotsAt_occupied_eq_arrayAt (chainEpochAt A) 112 newCap head.toNat p' xs
        head.toNat 0 cap.toNat (by omega)]
    · simp [← hlen]
    · intro k _
      have hle : head.toNat ≤ head.toNat + k := by omega
      simp only [vecDequeLogIdx, hle, ↓reduceIte]
      omega
  have hslots3 :
      memRegion (p' + BitVec.ofNat 64 ((cap.toNat + head.toNat) * 112))
        ((newCap - (cap.toNat + head.toNat)) * 112) ⊢
        vecDequeSlotsAt (chainEpochAt A) 112 newCap head.toNat p' xs
          (0 + head.toNat + cap.toNat) (newCap - (cap.toNat + head.toNat)) := by
    have hadd : 0 + head.toNat + cap.toNat = cap.toNat + head.toNat := by omega
    rw [hadd]
    refine memRegion_entails_vecDequeSlotsAt_uninit (chainEpochAt A) 112 newCap head.toNat p' xs
      (cap.toNat + head.toNat) (newCap - (cap.toNat + head.toNat)) (by omega) ?_
    intro k _
    have hle : head.toNat ≤ cap.toNat + head.toNat + k := by omega
    simp only [vecDequeLogIdx, hle, ↓reduceIte, hlen]
    omega
  rw [hslots_split, hslots2]
  have hbs_all : ChainEpochArrayBytes xs (bs_front ++ bs_back) := by
    have h := hbs_front.append hbs_back
    rwa [List.take_append_drop] at h
  have hheaps_all :
      chainEpochHeaps A (xs.drop (cap.toNat - head.toNat)) ∗
        chainEpochHeaps A (xs.take (cap.toNat - head.toNat)) =
      chainEpochHeaps A xs := by
    conv => rhs; rw [← List.take_append_drop (cap.toNat - head.toNat) xs, chainEpochHeaps_append]
    ac_rfl
  have h2 := arrayAt_chainEpochAt_of_bytes A (p' + BitVec.ofNat 64 (head.toNat * 112)) hbs_all
  have hpull :
      ((v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
        ((v + 16#64) ↦₆₄ head) ∗ ((v + 24#64) ↦₆₄ cap) ∗
        A.live p' (newCap * 112) 8 ∗
        memRegion p' (head.toNat * 112) ∗
        ((p' + BitVec.ofNat 64 (head.toNat * 112)) ↦ₛ (bs_front ++ bs_back)) ∗
        memRegion (p' + BitVec.ofNat 64 ((cap.toNat + head.toNat) * 112))
          ((newCap - (cap.toNat + head.toNat)) * 112) ∗
        chainEpochHeaps A (xs.drop (cap.toNat - head.toNat)) ∗
        chainEpochHeaps A (xs.take (cap.toNat - head.toNat))) =
      (((v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
        ((v + 16#64) ↦₆₄ head) ∗ ((v + 24#64) ↦₆₄ cap)) ∗
       (A.live p' (newCap * 112) 8 ∗
         (memRegion p' (head.toNat * 112) ∗
          ((((p' + BitVec.ofNat 64 (head.toNat * 112)) ↦ₛ (bs_front ++ bs_back)) ∗
            (chainEpochHeaps A (xs.drop (cap.toNat - head.toNat)) ∗
             chainEpochHeaps A (xs.take (cap.toNat - head.toNat)))) ∗
           memRegion (p' + BitVec.ofNat 64 ((cap.toNat + head.toNat) * 112))
             ((newCap - (cap.toNat + head.toNat)) * 112))))) := by
    ac_rfl
  rw [hpull, hheaps_all]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono hslots1 (sepConj_mono h2 hslots3)))

/-- Wrapping `memmove` (`cap - head ≤ head`) postcondition reassembly. -/
theorem vecDequeAt_wrap_memmove_of_post (A : RustAlloc)
    (v cap p' head : BitVec 64) (xs : List (ChainEpochGhost × ChainEpoch))
    {bs_back bs_front : List (BitVec 8)}
    (hlen : xs.length = cap.toNat)
    (hhead_pos : 0 < head.toNat)
    (hhead_lt : head.toNat < cap.toNat)
    (hhead_ge : cap.toNat - head.toNat ≤ head.toNat)
    (hbs_back : ChainEpochArrayBytes (xs.drop (cap.toNat - head.toNat)) bs_back)
    (hbs_front : ChainEpochArrayBytes (xs.take (cap.toNat - head.toNat)) bs_front)
    (hmax_lt : max (2 * cap.toNat) 4 * 112 < 2 ^ 63)
    (hp' : p' ≠ 0#64) :
    ((v ↦₆₄ BitVec.ofNat 64 (max (2 * cap.toNat) 4)) ∗ ((v + 8#64) ↦₆₄ p') ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (max (2 * cap.toNat) 4 - (cap.toNat - head.toNat))) ∗
      ((v + 24#64) ↦₆₄ cap) ∗
      A.live p' (max (2 * cap.toNat) 4 * 112) 8 ∗
      (p' ↦ₛ bs_back) ∗
      memRegion (p' + BitVec.ofNat 64 (head.toNat * 112))
        ((max (2 * cap.toNat) 4 - cap.toNat) * 112) ∗
      ((p' + BitVec.ofNat 64 ((max (2 * cap.toNat) 4 - (cap.toNat - head.toNat)) * 112)) ↦ₛ bs_front) ∗
      chainEpochHeaps A (xs.drop (cap.toNat - head.toNat)) ∗
      chainEpochHeaps A (xs.take (cap.toNat - head.toNat))) ⊢
    vecDequeAt A chainEpochSize chainEpochAlign (chainEpochAt A)
      v (BitVec.ofNat 64 (max (2 * cap.toNat) 4)) p'
      (BitVec.ofNat 64 (max (2 * cap.toNat) 4 - (cap.toNat - head.toNat))) xs := by
  let newCap := max (2 * cap.toNat) 4
  let newHead := newCap - (cap.toNat - head.toNat)
  have hnc_def : newCap = max (2 * cap.toNat) 4 := rfl
  have hnh_def : newHead = newCap - (cap.toNat - head.toNat) := rfl
  have hnc_toNat : (BitVec.ofNat 64 newCap).toNat = newCap := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hnh_toNat : (BitVec.ofNat 64 newHead).toNat = newHead := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hnc_ne : BitVec.ofNat 64 newCap ≠ 0 := by
    intro h0
    have := congrArg BitVec.toNat h0
    rw [hnc_toNat] at this
    change newCap = 0 at this
    omega
  have hlen_bv : BitVec.ofNat 64 xs.length = cap := by
    rw [hlen, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  unfold vecDequeAt vecDequeHeader vecDequeRingBuf chainEpochSize chainEpochAlign
  rw [hlen_bv, sepConj_pure_left_comm]
  simp only [← hnc_def, ← hnh_def, hnc_ne, ↓reduceIte, hnc_toNat, hnh_toNat]
  apply Entails.pure_right ⟨by omega, hmax_lt, hp', by omega⟩
  have hslots_split :
      vecDequeSlotsAt (chainEpochAt A) 112 newCap newHead p' xs 0 newCap =
        vecDequeSlotsAt (chainEpochAt A) 112 newCap newHead p' xs 0 head.toNat ∗
          (vecDequeSlotsAt (chainEpochAt A) 112 newCap newHead p' xs (0 + head.toNat)
              (newCap - cap.toNat) ∗
            vecDequeSlotsAt (chainEpochAt A) 112 newCap newHead p' xs
              (0 + head.toNat + (newCap - cap.toNat)) (cap.toNat - head.toNat)) := by
    rw [← vecDequeSlotsAt_add, ← vecDequeSlotsAt_add]
    congr 1
    omega
  have hslots1 :
      vecDequeSlotsAt (chainEpochAt A) 112 newCap newHead p' xs 0 head.toNat =
        arrayAt (chainEpochAt A) 112 p' (xs.drop (cap.toNat - head.toNat)) := by
    rw [vecDequeSlotsAt_occupied_eq_arrayAt (chainEpochAt A) 112 newCap newHead p' xs
      0 (cap.toNat - head.toNat) head.toNat (by omega)]
    · have htake : (xs.drop (cap.toNat - head.toNat)).take head.toNat =
          xs.drop (cap.toNat - head.toNat) :=
        List.take_of_length_le (by rw [List.length_drop, hlen]; omega)
      simp [htake]
    · intro k hk
      have hnot : ¬ newHead ≤ 0 + k := by omega
      simp only [vecDequeLogIdx, hnot, ↓reduceIte]
      omega
  have hslots2 :
      memRegion (p' + BitVec.ofNat 64 (head.toNat * 112)) ((newCap - cap.toNat) * 112) ⊢
        vecDequeSlotsAt (chainEpochAt A) 112 newCap newHead p' xs
          (0 + head.toNat) (newCap - cap.toNat) := by
    rw [Nat.zero_add]
    refine memRegion_entails_vecDequeSlotsAt_uninit (chainEpochAt A) 112 newCap newHead p' xs
      head.toNat (newCap - cap.toNat) (by omega) ?_
    intro k hk
    have hnot : ¬ newHead ≤ head.toNat + k := by omega
    simp only [vecDequeLogIdx, hnot, ↓reduceIte, hlen]
    omega
  have hslots3 :
      vecDequeSlotsAt (chainEpochAt A) 112 newCap newHead p' xs
        (0 + head.toNat + (newCap - cap.toNat)) (cap.toNat - head.toNat) =
        arrayAt (chainEpochAt A) 112 (p' + BitVec.ofNat 64 (newHead * 112))
          (xs.take (cap.toNat - head.toNat)) := by
    have hadd : 0 + head.toNat + (newCap - cap.toNat) = newHead := by omega
    rw [hadd,
      vecDequeSlotsAt_occupied_eq_arrayAt (chainEpochAt A) 112 newCap newHead p' xs
        newHead 0 (cap.toNat - head.toNat) (by omega)]
    · simp
    · intro k _
      have hle : newHead ≤ newHead + k := by omega
      simp only [vecDequeLogIdx, hle, ↓reduceIte]
      omega
  rw [hslots_split, hslots1, hslots3]
  have h1 := arrayAt_chainEpochAt_of_bytes A p' hbs_back
  have h3 := arrayAt_chainEpochAt_of_bytes A (p' + BitVec.ofNat 64 (newHead * 112)) hbs_front
  have hpull :
      ((v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 newHead) ∗ ((v + 24#64) ↦₆₄ cap) ∗
        A.live p' (newCap * 112) 8 ∗
        (p' ↦ₛ bs_back) ∗
        memRegion (p' + BitVec.ofNat 64 (head.toNat * 112)) ((newCap - cap.toNat) * 112) ∗
        ((p' + BitVec.ofNat 64 (newHead * 112)) ↦ₛ bs_front) ∗
        chainEpochHeaps A (xs.drop (cap.toNat - head.toNat)) ∗
        chainEpochHeaps A (xs.take (cap.toNat - head.toNat))) =
      (((v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 newHead) ∗ ((v + 24#64) ↦₆₄ cap)) ∗
       (A.live p' (newCap * 112) 8 ∗
         (((p' ↦ₛ bs_back) ∗ chainEpochHeaps A (xs.drop (cap.toNat - head.toNat))) ∗
          (memRegion (p' + BitVec.ofNat 64 (head.toNat * 112)) ((newCap - cap.toNat) * 112) ∗
           (((p' + BitVec.ofNat 64 (newHead * 112)) ↦ₛ bs_front) ∗
            chainEpochHeaps A (xs.take (cap.toNat - head.toNat))))))) := by
    ac_rfl
  rw [hpull]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono h1 (sepConj_mono hslots2 h3)))

end CryptoVerification.SpqrV1.Alloc

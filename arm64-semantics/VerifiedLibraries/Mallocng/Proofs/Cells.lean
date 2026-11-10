/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import ProofLib.SepLogic.Fresh
public import VerifiedLibraries.Mallocng.Spec

/-!
# Flat Byte-Level Separation-Logic Maps

Finite separating conjunctions (`BigSep`, `SetSep`) over address lists and decidable subsets,
contiguous address ranges (`rangeAddrs`), and flat byte-granular maps (`ByteMap`, `ProtNoneByteMap`,
`MappedSet`) with slice extraction, slice absorption, and `BoundedFootprint` lemmas.
-/

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 ProofLib

/-! ## Finite Separating Conjunctions -/

/-- Separating conjunction of `f x` across `xs : List α`. -/
def BigSep {α : Type} (f : α → SepProp) : List α → SepProp
  | [] => emp
  | x :: xs => f x ∗ BigSep f xs

@[simp] theorem BigSep_nil {α : Type} (f : α → SepProp) :
    BigSep f [] = emp := rfl

@[simp] theorem BigSep_cons {α : Type} (f : α → SepProp) (x : α) (xs : List α) :
    BigSep f (x :: xs) = (f x ∗ BigSep f xs) := rfl

theorem BigSep_congr {α : Type} {f g : α → SepProp} {xs : List α}
    (h : ∀ x ∈ xs, f x = g x) :
    BigSep f xs = BigSep g xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [BigSep_cons]
    rw [h x (List.Mem.head xs), ih (fun y hy => h y (List.Mem.tail x hy))]

theorem BigSep_append {α : Type} (f : α → SepProp) (xs ys : List α) :
    BigSep f (xs ++ ys) = (BigSep f xs ∗ BigSep f ys) := by
  induction xs with
  | nil =>
    simp only [List.nil_append, BigSep_nil]
    exact (emp_sepConj _).symm
  | cons x xs ih =>
    simp only [List.cons_append, BigSep_cons, ih, sepConj_assoc]

theorem BigSep_emp {α : Type} {f : α → SepProp} {xs : List α}
    (h : ∀ x ∈ xs, f x = emp) :
    BigSep f xs = emp := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [BigSep_cons, h x (List.Mem.head xs),
      ih (fun y hy => h y (List.Mem.tail x hy)), emp_sepConj]

theorem BigSep_noRO {α : Type} {f : α → SepProp} {xs : List α}
    (h : ∀ x ∈ xs, SepProp.NoRO (f x)) :
    SepProp.NoRO (BigSep f xs) := by
  induction xs with
  | nil => exact SepProp.NoRO.emp
  | cons x xs ih =>
    exact SepProp.NoRO.sepConj (h x (List.Mem.head xs))
      (ih (fun y hy => h y (List.Mem.tail x hy)))

theorem BigSep_footprintIn {α : Type} {f : α → SepProp} {xs : List α} {S : BitVec 64 → Prop}
    (h : ∀ x ∈ xs, SepProp.FootprintIn (f x) S) :
    SepProp.FootprintIn (BigSep f xs) S := by
  induction xs with
  | nil => exact SepProp.FootprintIn.emp
  | cons x xs ih =>
    exact SepProp.FootprintIn.sepConj (h x (List.Mem.head xs))
      (ih (fun y hy => h y (List.Mem.tail x hy)))

/-- Separating conjunction of `f x` over elements `x ∈ dom` satisfying `keep x`. -/
def SetSep {α : Type} (dom : List α) (keep : α → Prop) [DecidablePred keep]
    (f : α → SepProp) : SepProp :=
  BigSep (fun x => if keep x then f x else emp) dom

theorem SetSep_congr {α : Type} {dom : List α}
    {keep₁ keep₂ : α → Prop} [DecidablePred keep₁] [DecidablePred keep₂]
    {f₁ f₂ : α → SepProp}
    (hKeep : ∀ x ∈ dom, keep₁ x ↔ keep₂ x)
    (hVal : ∀ x ∈ dom, keep₁ x → f₁ x = f₂ x) :
    SetSep dom keep₁ f₁ = SetSep dom keep₂ f₂ := by
  apply BigSep_congr
  intro x hx
  by_cases hk : keep₁ x
  · have hk2 : keep₂ x := (hKeep x hx).mp hk
    simp [hk, hk2, hVal x hx hk]
  · have hk2 : ¬ keep₂ x := fun h => hk ((hKeep x hx).mpr h)
    simp [hk, hk2]

theorem SetSep_empty {α : Type} {dom : List α}
    {keep : α → Prop} [DecidablePred keep] (f : α → SepProp)
    (hEmpty : ∀ x ∈ dom, ¬ keep x) :
    SetSep dom keep f = emp := by
  apply BigSep_emp
  intro x hx
  simp [hEmpty x hx]

theorem SetSep_append {α : Type} (dom₁ dom₂ : List α)
    (keep : α → Prop) [DecidablePred keep] (f : α → SepProp) :
    SetSep (dom₁ ++ dom₂) keep f = (SetSep dom₁ keep f ∗ SetSep dom₂ keep f) :=
  BigSep_append _ dom₁ dom₂

theorem SetSep_append_right_empty {α : Type} {dom₁ dom₂ : List α}
    {keep : α → Prop} [DecidablePred keep] (f : α → SepProp)
    (hEmpty : ∀ x ∈ dom₂, ¬ keep x) :
    SetSep (dom₁ ++ dom₂) keep f = SetSep dom₁ keep f := by
  rw [SetSep_append, SetSep_empty f hEmpty, sepConj_emp]

theorem SetSep_filter_of_imp {α : Type} {dom : List α}
    {keep : α → Prop} [DecidablePred keep] (p : α → Bool) (f : α → SepProp)
    (hImp : ∀ x ∈ dom, keep x → p x = true) :
    SetSep (dom.filter p) keep f = SetSep dom keep f := by
  induction dom with
  | nil => rfl
  | cons x xs ih =>
    have ih' := ih (fun y hy hk => hImp y (List.Mem.tail x hy) hk)
    by_cases hp : p x = true
    · simp only [List.filter_cons_of_pos hp, SetSep, BigSep_cons]
      simp only [SetSep] at ih'
      rw [ih']
    · have hnk : ¬ keep x := fun hk => hp (hImp x (List.Mem.head xs) hk)
      simp only [List.filter_cons_of_neg hp, SetSep, BigSep_cons, hnk, ↓reduceIte, emp_sepConj]
      exact ih'

theorem SetSep_noRO {α : Type} {dom : List α}
    {keep : α → Prop} [DecidablePred keep] {f : α → SepProp}
    (h : ∀ x ∈ dom, keep x → SepProp.NoRO (f x)) :
    SepProp.NoRO (SetSep dom keep f) := by
  apply BigSep_noRO
  intro x hx
  by_cases hk : keep x
  · simp [hk, h x hx hk]
  · simp [hk]

theorem SetSep_split {α : Type} (dom : List α)
    (keep : α → Prop) [DecidablePred keep]
    (P : α → Prop) [DecidablePred P] (f : α → SepProp) :
    SetSep dom keep f =
      (SetSep dom (fun x => keep x ∧ P x) f ∗ SetSep dom (fun x => keep x ∧ ¬ P x) f) := by
  induction dom with
  | nil =>
    simp [SetSep]
  | cons x xs ih =>
    simp only [SetSep, BigSep_cons] at ih ⊢
    rw [ih]
    by_cases hk : keep x
    · by_cases hp : P x
      · simp only [hk, hp, and_self, not_true_eq_false, and_false, ↓reduceIte]
        exact Entails.antisymm (by sep_entail) (by sep_entail)
      · simp only [hk, hp, and_false, not_false_eq_true, and_self, ↓reduceIte]
        exact Entails.antisymm (by sep_entail) (by sep_entail)
    · simp only [hk, false_and, ↓reduceIte]
      exact Entails.antisymm (by sep_entail) (by sep_entail)

theorem SetSep_merge {α : Type} {dom : List α}
    {keep₁ keep₂ : α → Prop} [DecidablePred keep₁] [DecidablePred keep₂]
    (f : α → SepProp)
    (hDisj : ∀ x ∈ dom, ¬ (keep₁ x ∧ keep₂ x)) :
    (SetSep dom keep₁ f ∗ SetSep dom keep₂ f) =
      SetSep dom (fun x => keep₁ x ∨ keep₂ x) f := by
  rw [SetSep_split dom (fun x => keep₁ x ∨ keep₂ x) keep₁ f]
  have h1 : SetSep dom (fun x => (keep₁ x ∨ keep₂ x) ∧ keep₁ x) f = SetSep dom keep₁ f := by
    refine SetSep_congr (fun x _ => ?_) (fun _ _ _ => rfl)
    exact ⟨fun h => h.2, fun h => ⟨Or.inl h, h⟩⟩
  have h2 : SetSep dom (fun x => (keep₁ x ∨ keep₂ x) ∧ ¬ keep₁ x) f = SetSep dom keep₂ f := by
    refine SetSep_congr (fun x hx => ?_) (fun _ _ _ => rfl)
    constructor
    · rintro ⟨h12 | h2, hn1⟩
      · exact False.elim (hn1 h12)
      · exact h2
    · intro h2
      exact ⟨Or.inr h2, fun h1 => hDisj x hx ⟨h1, h2⟩⟩
  rw [h1, h2]

theorem SetSep_focus {α : Type} [DecidableEq α] {dom : List α}
    (hNodup : dom.Nodup) {keep : α → Prop} [DecidablePred keep]
    (f : α → SepProp) {x₀ : α} (hMem : x₀ ∈ dom) (hKeep : keep x₀) :
    SetSep dom keep f = (f x₀ ∗ SetSep dom (fun x => keep x ∧ x ≠ x₀) f) := by
  induction dom with
  | nil => cases hMem
  | cons x xs ih =>
    have ⟨hxNotMem, hxsNodup⟩ := List.nodup_cons.mp hNodup
    by_cases hxx : x = x₀
    · subst hxx
      simp only [SetSep, BigSep_cons, hKeep, ne_eq, not_true_eq_false, and_false, ↓reduceIte,
        emp_sepConj]
      congr 1
      refine SetSep_congr (fun y hy => ?_) (fun _ _ _ => rfl)
      have hyNe : y ≠ x := fun h => hxNotMem (h ▸ hy)
      exact ⟨fun hk => ⟨hk, hyNe⟩, fun h => h.1⟩
    · have hMemTail : x₀ ∈ xs := by
        cases hMem with
        | head => exact False.elim (hxx rfl)
        | tail _ hm => exact hm
      simp only [SetSep, BigSep_cons]
      have ih' := ih hxsNodup hMemTail
      simp only [SetSep] at ih'
      rw [ih']
      by_cases hk : keep x
      · simp only [hk, ne_eq, hxx, not_false_eq_true, and_self, ↓reduceIte]
        exact Entails.antisymm (by sep_entail) (by sep_entail)
      · simp only [hk, false_and, ↓reduceIte]
        exact Entails.antisymm (by sep_entail) (by sep_entail)

theorem SetSep_eq_BigSep_of_sub {α : Type} [DecidableEq α] {dom sub : List α}
    (hNodup : dom.Nodup) (hSubNodup : sub.Nodup)
    (hSub : ∀ x ∈ sub, x ∈ dom)
    {keep : α → Prop} [DecidablePred keep]
    (hKeep : ∀ x ∈ dom, keep x ↔ x ∈ sub) (f : α → SepProp) :
    SetSep dom keep f = BigSep f sub := by
  induction sub generalizing keep with
  | nil =>
    rw [BigSep_nil]
    exact SetSep_empty f (fun x hx hk => by simpa using (hKeep x hx).mp hk)
  | cons x₀ rest ih =>
    have ⟨hxNotRest, hRestNodup⟩ := List.nodup_cons.mp hSubNodup
    have hxDom : x₀ ∈ dom := hSub x₀ (List.Mem.head rest)
    have hxKeep : keep x₀ := (hKeep x₀ hxDom).mpr (List.Mem.head rest)
    rw [SetSep_focus hNodup f hxDom hxKeep, BigSep_cons]
    congr 1
    apply ih hRestNodup (fun y hy => hSub y (List.Mem.tail x₀ hy))
    intro y hyDom
    constructor
    · rintro ⟨hyk, hyNe⟩
      rcases List.mem_cons.mp ((hKeep y hyDom).mp hyk) with rfl | hyRest
      · exact False.elim (hyNe rfl)
      · exact hyRest
    · intro hyRest
      exact ⟨(hKeep y hyDom).mpr (List.Mem.tail x₀ hyRest),
        fun hEq => hxNotRest (hEq ▸ hyRest)⟩

/-! ## Contiguous Address Ranges -/

/-- List of `n` consecutive 64-bit addresses `[base, base + 1, ..., base + (n - 1)]`. -/
def rangeAddrs (base : BitVec 64) (n : Nat) : List (BitVec 64) :=
  (List.range n).map (fun i => base + BitVec.ofNat 64 i)

@[simp] theorem rangeAddrs_zero (base : BitVec 64) :
    rangeAddrs base 0 = [] := rfl

@[simp] theorem rangeAddrs_length (base : BitVec 64) (n : Nat) :
    (rangeAddrs base n).length = n := by
  simp [rangeAddrs]

theorem rangeAddrs_succ (base : BitVec 64) (n : Nat) :
    rangeAddrs base (n + 1) = base :: rangeAddrs (base + 1#64) n := by
  unfold rangeAddrs
  rw [List.range_succ_eq_map]
  simp only [List.map_cons, BitVec.add_zero, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  show base + BitVec.ofNat 64 (i + 1) = base + 1#64 + BitVec.ofNat 64 i
  bv_omega

theorem mem_rangeAddrs_iff_inRegion (base : BitVec 64) {n : Nat} (hn : n ≤ 2 ^ 64) (a : BitVec 64) :
    a ∈ rangeAddrs base n ↔ InRegion base n a := by
  unfold rangeAddrs InRegion
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hi64 : i < 2 ^ 64 := Nat.lt_of_lt_of_le hi hn
    have hsub : base + BitVec.ofNat 64 i - base = BitVec.ofNat 64 i := by bv_omega
    rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64]
    exact hi
  · intro ha
    refine ⟨(a - base).toNat, ha, ?_⟩
    bv_omega

theorem nodup_rangeAddrs (base : BitVec 64) {n : Nat} (hn : n ≤ 2 ^ 64) :
    (rangeAddrs base n).Nodup := by
  induction n generalizing base with
  | zero => simp [rangeAddrs_zero]
  | succ k ih =>
    have hk : k + 1 ≤ 2 ^ 64 := hn
    rw [rangeAddrs_succ, List.nodup_cons]
    refine ⟨?_, ih (base + 1#64) (by omega)⟩
    rw [mem_rangeAddrs_iff_inRegion (base + 1#64) (by omega)]
    unfold InRegion
    bv_omega

/-! ## Range Bridges to Contiguous Slice Predicates -/

/-- Extract the `n`-byte list `[val base, val (base + 1), ..., val (base + n - 1)]` from `val`. -/
def readBytesFromMap (val : BitVec 64 → BitVec 8) (base : BitVec 64) (n : Nat) : List (BitVec 8) :=
  (rangeAddrs base n).map val

@[simp] theorem readBytesFromMap_length (val : BitVec 64 → BitVec 8) (base : BitVec 64) (n : Nat) :
    (readBytesFromMap val base n).length = n := by
  simp [readBytesFromMap]

@[simp] theorem readBytesFromMap_zero (val : BitVec 64 → BitVec 8) (base : BitVec 64) :
    readBytesFromMap val base 0 = [] := rfl

theorem readBytesFromMap_succ (val : BitVec 64 → BitVec 8) (base : BitVec 64) (n : Nat) :
    readBytesFromMap val base (n + 1) = val base :: readBytesFromMap val (base + 1#64) n := by
  simp [readBytesFromMap, rangeAddrs_succ]

theorem readBytesFromMap_getElem (val : BitVec 64 → BitVec 8) (base : BitVec 64) (n i : Nat)
    (hi : i < (readBytesFromMap val base n).length) :
    (readBytesFromMap val base n)[i] = val (base + BitVec.ofNat 64 i) := by
  simp [readBytesFromMap, rangeAddrs]

/-- Update `val` on `[base, base + bs.length)` with bytes from `bs`. -/
def writeBytesToMap (val : BitVec 64 → BitVec 8) (base : BitVec 64) (bs : List (BitVec 8)) :
    BitVec 64 → BitVec 8 :=
  fun a =>
    if h : InRegion base bs.length a then bs[(a - base).toNat]'h
    else val a

theorem writeBytesToMap_in (val : BitVec 64 → BitVec 8) (base : BitVec 64) (bs : List (BitVec 8))
    {i : Nat} (hi : i < bs.length) (hlen : bs.length ≤ 2 ^ 64) :
    writeBytesToMap val base bs (base + BitVec.ofNat 64 i) = bs[i] := by
  unfold writeBytesToMap
  have hi64 : i < 2 ^ 64 := Nat.lt_of_lt_of_le hi hlen
  have hsub : base + BitVec.ofNat 64 i - base = BitVec.ofNat 64 i := by bv_omega
  have hnat : (base + BitVec.ofNat 64 i - base).toNat = i := by
    rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64]
  have hin : InRegion base bs.length (base + BitVec.ofNat 64 i) := by
    simpa [InRegion, hnat] using hi
  simp only [hin, ↓reduceDIte]
  congr 1

theorem writeBytesToMap_out (val : BitVec 64 → BitVec 8) (base : BitVec 64) (bs : List (BitVec 8))
    {a : BitVec 64} (hout : ¬ InRegion base bs.length a) :
    writeBytesToMap val base bs a = val a := by
  simp [writeBytesToMap, hout]

theorem readBytesFromMap_writeBytesToMap (val : BitVec 64 → BitVec 8) (base : BitVec 64)
    (bs : List (BitVec 8)) (hlen : bs.length ≤ 2 ^ 64) :
    readBytesFromMap (writeBytesToMap val base bs) base bs.length = bs := by
  apply List.ext_getElem (by simp)
  intro i hi1 hi2
  rw [readBytesFromMap_getElem _ _ _ _ hi1]
  exact writeBytesToMap_in val base bs hi2 hlen

theorem BigSep_pointsTo8_rangeAddrs (val : BitVec 64 → BitVec 8) (base : BitVec 64) (n : Nat) :
    BigSep (fun a => a ↦₈ val a) (rangeAddrs base n) =
      (base ↦ₛ readBytesFromMap val base n) := by
  induction n generalizing base with
  | zero =>
    simp [rangeAddrs_zero, readBytesFromMap_zero, pointsToBytes_nil]
  | succ k ih =>
    rw [rangeAddrs_succ, readBytesFromMap_succ, BigSep_cons, pointsToBytes_cons, ih (base + 1#64)]

theorem BigSep_pointsTo8ProtNone_rangeAddrs (val : BitVec 64 → BitVec 8) (base : BitVec 64) (n : Nat) :
    BigSep (fun a => a ↦₈ₙ val a) (rangeAddrs base n) =
      (base ↦ₙ readBytesFromMap val base n) := by
  induction n generalizing base with
  | zero =>
    simp [rangeAddrs_zero, readBytesFromMap_zero, pointsToBytesProtNone_nil]
  | succ k ih =>
    rw [rangeAddrs_succ, readBytesFromMap_succ, BigSep_cons, pointsToBytesProtNone_cons,
      ih (base + 1#64)]

theorem BigSep_memMapped1_rangeAddrs (base : BitVec 64) {n : Nat} (hn : n ≤ 2 ^ 64) :
    BigSep (fun a => memMapped a 1) (rangeAddrs base n) = memMapped base n := by
  induction n generalizing base with
  | zero =>
    simp [rangeAddrs_zero, memMapped_zero]
  | succ k ih =>
    have hk : k ≤ 2 ^ 64 := by omega
    have hsplit : memMapped base (1 + k) = (memMapped base 1 ∗ memMapped (base + 1#64) k) := by
      simpa using memMapped_split base 1 k (by omega)
    rw [Nat.add_comm 1 k] at hsplit
    rw [rangeAddrs_succ, BigSep_cons, ih (base + 1#64) hk, hsplit]

/-! ## Flat Byte Maps and Slice Extraction -/

/-- Flat read-write (`↦₈`) byte map over `dom` gated by `keep`. -/
def ByteMap (dom : List (BitVec 64)) (keep : BitVec 64 → Prop) [DecidablePred keep]
    (val : BitVec 64 → BitVec 8) : SepProp :=
  SetSep dom keep (fun a => a ↦₈ val a)

/-- Flat `PROT_NONE` (`↦₈ₙ`) byte map over `dom` gated by `keep`. -/
def ProtNoneByteMap (dom : List (BitVec 64)) (keep : BitVec 64 → Prop) [DecidablePred keep]
    (val : BitVec 64 → BitVec 8) : SepProp :=
  SetSep dom keep (fun a => a ↦₈ₙ val a)

/-- Flat `memMapped · 1` virtual-address reservation set over `dom` gated by `keep`. -/
def MappedSet (dom : List (BitVec 64)) (keep : BitVec 64 → Prop) [DecidablePred keep] : SepProp :=
  SetSep dom keep (fun a => memMapped a 1)

theorem ByteMap_noRO (dom : List (BitVec 64)) (keep : BitVec 64 → Prop) [DecidablePred keep]
    (val : BitVec 64 → BitVec 8) :
    SepProp.NoRO (ByteMap dom keep val) :=
  SetSep_noRO (fun a _ _ => SepProp.NoRO.pointsTo8 a (val a))

theorem ProtNoneByteMap_noRO (dom : List (BitVec 64)) (keep : BitVec 64 → Prop) [DecidablePred keep]
    (val : BitVec 64 → BitVec 8) :
    SepProp.NoRO (ProtNoneByteMap dom keep val) :=
  SetSep_noRO (fun a _ _ => SepProp.NoRO.pointsTo8ProtNone a (val a))

theorem MappedSet_noRO (dom : List (BitVec 64)) (keep : BitVec 64 → Prop) [DecidablePred keep] :
    SepProp.NoRO (MappedSet dom keep) :=
  SetSep_noRO (fun a _ _ => SepProp.NoRO.memMapped a 1)

theorem SetSep_footprintIn {α : Type} {dom : List α}
    {keep : α → Prop} [DecidablePred keep] {f : α → SepProp} {S : BitVec 64 → Prop}
    (h : ∀ x ∈ dom, keep x → SepProp.FootprintIn (f x) S) :
    SepProp.FootprintIn (SetSep dom keep f) S := by
  apply BigSep_footprintIn
  intro x hx
  by_cases hk : keep x
  · simpa [hk] using h x hx hk
  · simpa [hk] using (SepProp.FootprintIn.emp (S := S))

theorem ByteMap_footprintIn (dom : List (BitVec 64)) (keep : BitVec 64 → Prop) [DecidablePred keep]
    (val : BitVec 64 → BitVec 8) :
    SepProp.FootprintIn (ByteMap dom keep val) (· ∈ dom) :=
  SetSep_footprintIn (fun _ ha _ => SepProp.FootprintIn.pointsTo8 ha)

theorem ProtNoneByteMap_footprintIn (dom : List (BitVec 64)) (keep : BitVec 64 → Prop) [DecidablePred keep]
    (val : BitVec 64 → BitVec 8) :
    SepProp.FootprintIn (ProtNoneByteMap dom keep val) (· ∈ dom) :=
  SetSep_footprintIn (fun _ ha _ => SepProp.FootprintIn.pointsTo8ProtNone ha)

theorem MappedSet_footprintIn (dom : List (BitVec 64)) (keep : BitVec 64 → Prop) [DecidablePred keep] :
    SepProp.FootprintIn (MappedSet dom keep) (· ∈ dom) := by
  refine SetSep_footprintIn (fun a ha _ => SepProp.FootprintIn.memMapped fun x hx => ?_)
  have hxa : x = a := by
    unfold InRegion at hx
    bv_omega
  exact hxa ▸ ha

theorem ByteMap_extract_slice {dom : List (BitVec 64)} (hNodup : dom.Nodup)
    {keep : BitVec 64 → Prop} [DecidablePred keep]
    (val : BitVec 64 → BitVec 8) (base : BitVec 64) {n : Nat} (hn : n ≤ 2 ^ 64)
    (hSubDom : ∀ a, InRegion base n a → a ∈ dom)
    (hSubKeep : ∀ a, InRegion base n a → keep a) :
    ByteMap dom keep val =
      ((base ↦ₛ readBytesFromMap val base n) ∗
        ByteMap dom (fun a => keep a ∧ ¬ InRegion base n a) val) := by
  unfold ByteMap
  rw [SetSep_split dom keep (InRegion base n)]
  congr 1
  rw [SetSep_eq_BigSep_of_sub hNodup (nodup_rangeAddrs base hn)
    (fun a ha => hSubDom a ((mem_rangeAddrs_iff_inRegion base hn a).mp ha))
    (fun a _ => by
      rw [mem_rangeAddrs_iff_inRegion base hn a]
      exact ⟨fun h => h.2, fun h => ⟨hSubKeep a h, h⟩⟩),
    BigSep_pointsTo8_rangeAddrs]

theorem ByteMap_absorb_slice {dom : List (BitVec 64)} (hNodup : dom.Nodup)
    {keep : BitVec 64 → Prop} [DecidablePred keep]
    (val : BitVec 64 → BitVec 8) (base : BitVec 64) (bs : List (BitVec 8))
    (hn : bs.length ≤ 2 ^ 64)
    (hSubDom : ∀ a, InRegion base bs.length a → a ∈ dom)
    (hDisjKeep : ∀ a, InRegion base bs.length a → ¬ keep a) :
    ((base ↦ₛ bs) ∗ ByteMap dom keep val) =
      ByteMap dom (fun a => keep a ∨ InRegion base bs.length a)
        (writeBytesToMap val base bs) := by
  let val' := writeBytesToMap val base bs
  have hbs : bs = readBytesFromMap val' base bs.length :=
    (readBytesFromMap_writeBytesToMap val base bs hn).symm
  have hRest : ByteMap dom keep val =
      ByteMap dom (fun a => (keep a ∨ InRegion base bs.length a) ∧ ¬ InRegion base bs.length a) val' := by
    unfold ByteMap
    refine SetSep_congr (fun a _ => ?_) (fun a _ hk => ?_)
    · exact ⟨fun hk => ⟨Or.inl hk, fun hin => hDisjKeep a hin hk⟩,
        fun ⟨h12, hnin⟩ => h12.elim id (fun hin => False.elim (hnin hin))⟩
    · have hnin : ¬ InRegion base bs.length a := fun hin => hDisjKeep a hin hk
      simp [val', writeBytesToMap_out val base bs hnin]
  have hExtract := ByteMap_extract_slice hNodup (keep := fun a => keep a ∨ InRegion base bs.length a)
    val' base hn hSubDom (fun a hin => Or.inr hin)
  rw [← hbs, ← hRest] at hExtract
  exact hExtract.symm

theorem ProtNoneByteMap_extract_slice {dom : List (BitVec 64)} (hNodup : dom.Nodup)
    {keep : BitVec 64 → Prop} [DecidablePred keep]
    (val : BitVec 64 → BitVec 8) (base : BitVec 64) {n : Nat} (hn : n ≤ 2 ^ 64)
    (hSubDom : ∀ a, InRegion base n a → a ∈ dom)
    (hSubKeep : ∀ a, InRegion base n a → keep a) :
    ProtNoneByteMap dom keep val =
      ((base ↦ₙ readBytesFromMap val base n) ∗
        ProtNoneByteMap dom (fun a => keep a ∧ ¬ InRegion base n a) val) := by
  unfold ProtNoneByteMap
  rw [SetSep_split dom keep (InRegion base n)]
  congr 1
  rw [SetSep_eq_BigSep_of_sub hNodup (nodup_rangeAddrs base hn)
    (fun a ha => hSubDom a ((mem_rangeAddrs_iff_inRegion base hn a).mp ha))
    (fun a _ => by
      rw [mem_rangeAddrs_iff_inRegion base hn a]
      exact ⟨fun h => h.2, fun h => ⟨hSubKeep a h, h⟩⟩),
    BigSep_pointsTo8ProtNone_rangeAddrs]

theorem ProtNoneByteMap_absorb_slice {dom : List (BitVec 64)} (hNodup : dom.Nodup)
    {keep : BitVec 64 → Prop} [DecidablePred keep]
    (val : BitVec 64 → BitVec 8) (base : BitVec 64) (bs : List (BitVec 8))
    (hn : bs.length ≤ 2 ^ 64)
    (hSubDom : ∀ a, InRegion base bs.length a → a ∈ dom)
    (hDisjKeep : ∀ a, InRegion base bs.length a → ¬ keep a) :
    ((base ↦ₙ bs) ∗ ProtNoneByteMap dom keep val) =
      ProtNoneByteMap dom (fun a => keep a ∨ InRegion base bs.length a)
        (writeBytesToMap val base bs) := by
  let val' := writeBytesToMap val base bs
  have hbs : bs = readBytesFromMap val' base bs.length :=
    (readBytesFromMap_writeBytesToMap val base bs hn).symm
  have hRest : ProtNoneByteMap dom keep val =
      ProtNoneByteMap dom (fun a => (keep a ∨ InRegion base bs.length a) ∧ ¬ InRegion base bs.length a) val' := by
    unfold ProtNoneByteMap
    refine SetSep_congr (fun a _ => ?_) (fun a _ hk => ?_)
    · exact ⟨fun hk => ⟨Or.inl hk, fun hin => hDisjKeep a hin hk⟩,
        fun ⟨h12, hnin⟩ => h12.elim id (fun hin => False.elim (hnin hin))⟩
    · have hnin : ¬ InRegion base bs.length a := fun hin => hDisjKeep a hin hk
      simp [val', writeBytesToMap_out val base bs hnin]
  have hExtract := ProtNoneByteMap_extract_slice hNodup
    (keep := fun a => keep a ∨ InRegion base bs.length a)
    val' base hn hSubDom (fun a hin => Or.inr hin)
  rw [← hbs, ← hRest] at hExtract
  exact hExtract.symm

theorem MappedSet_extract_slice {dom : List (BitVec 64)} (hNodup : dom.Nodup)
    {keep : BitVec 64 → Prop} [DecidablePred keep]
    (base : BitVec 64) {n : Nat} (hn : n ≤ 2 ^ 64)
    (hSubDom : ∀ a, InRegion base n a → a ∈ dom)
    (hSubKeep : ∀ a, InRegion base n a → keep a) :
    MappedSet dom keep =
      (memMapped base n ∗ MappedSet dom (fun a => keep a ∧ ¬ InRegion base n a)) := by
  unfold MappedSet
  rw [SetSep_split dom keep (InRegion base n)]
  congr 1
  rw [SetSep_eq_BigSep_of_sub hNodup (nodup_rangeAddrs base hn)
    (fun a ha => hSubDom a ((mem_rangeAddrs_iff_inRegion base hn a).mp ha))
    (fun a _ => by
      rw [mem_rangeAddrs_iff_inRegion base hn a]
      exact ⟨fun h => h.2, fun h => ⟨hSubKeep a h, h⟩⟩),
    BigSep_memMapped1_rangeAddrs base hn]

theorem MappedSet_absorb_slice {dom : List (BitVec 64)} (hNodup : dom.Nodup)
    {keep : BitVec 64 → Prop} [DecidablePred keep]
    (base : BitVec 64) {n : Nat} (hn : n ≤ 2 ^ 64)
    (hSubDom : ∀ a, InRegion base n a → a ∈ dom)
    (hDisjKeep : ∀ a, InRegion base n a → ¬ keep a) :
    (memMapped base n ∗ MappedSet dom keep) =
      MappedSet dom (fun a => keep a ∨ InRegion base n a) := by
  have hRest : MappedSet dom keep =
      MappedSet dom (fun a => (keep a ∨ InRegion base n a) ∧ ¬ InRegion base n a) := by
    unfold MappedSet
    refine SetSep_congr (fun a _ => ?_) (fun _ _ _ => rfl)
    exact ⟨fun hk => ⟨Or.inl hk, fun hin => hDisjKeep a hin hk⟩,
      fun ⟨h12, hnin⟩ => h12.elim id (fun hin => False.elim (hnin hin))⟩
  have hExtract := MappedSet_extract_slice hNodup (keep := fun a => keep a ∨ InRegion base n a)
    base hn hSubDom (fun a hin => Or.inr hin)
  rw [← hRest] at hExtract
  exact hExtract.symm

/-! ## `SepProp.BoundedFootprint` Bridges -/

theorem BoundedFootprint_ghostMapAuth (γ : GhostName) (L : BitVec 64 → Option Nat) :
    SepProp.BoundedFootprint (ghostMapAuth γ L) 0 :=
  SepProp.BoundedFootprint.of_footprintIn (dom := [])
    (SepProp.FootprintIn.ghostMapAuth γ L) (Nat.le_refl 0)

theorem BoundedFootprint_pointsTo8 (a : BitVec 64) (v : BitVec 8) :
    SepProp.BoundedFootprint (a ↦₈ v) 1 :=
  SepProp.BoundedFootprint.of_footprintIn (dom := [a])
    (SepProp.FootprintIn.pointsTo8 (List.Mem.head [])) (Nat.le_refl 1)

theorem BoundedFootprint_pointsTo32 (a : BitVec 64) (v : BitVec 32) :
    SepProp.BoundedFootprint (a ↦₃₂ v) 4 :=
  SepProp.BoundedFootprint.of_footprintIn (dom := rangeAddrs a 4)
    (SepProp.FootprintIn.pointsTo32 fun x hx =>
      (mem_rangeAddrs_iff_inRegion a (by decide) x).mpr hx)
    (by simp)

theorem BoundedFootprint_pointsTo64 (a : BitVec 64) (v : BitVec 64) :
    SepProp.BoundedFootprint (a ↦₆₄ v) 8 :=
  SepProp.BoundedFootprint.of_footprintIn (dom := rangeAddrs a 8)
    (SepProp.FootprintIn.pointsTo64 fun x hx =>
      (mem_rangeAddrs_iff_inRegion a (by decide) x).mpr hx)
    (by simp)

theorem BoundedFootprint_pointsToBytes (a : BitVec 64) (bs : List (BitVec 8))
    (hlen : bs.length ≤ 2 ^ 64) :
    SepProp.BoundedFootprint (a ↦ₛ bs) bs.length :=
  SepProp.BoundedFootprint.of_footprintIn (dom := rangeAddrs a bs.length)
    (SepProp.FootprintIn.pointsToBytes hlen fun x hx =>
      (mem_rangeAddrs_iff_inRegion a hlen x).mpr hx)
    (by simp)

theorem BoundedFootprint_pointsToBytesRO (a : BitVec 64) (bs : List (BitVec 8))
    (hlen : bs.length ≤ 2 ^ 64) :
    SepProp.BoundedFootprint (a ↦ᵣ bs) bs.length :=
  SepProp.BoundedFootprint.of_footprintIn (dom := rangeAddrs a bs.length)
    (SepProp.FootprintIn.pointsToBytesRO hlen fun x hx =>
      (mem_rangeAddrs_iff_inRegion a hlen x).mpr hx)
    (by simp)

theorem BoundedFootprint_pointsToWords64 (a : BitVec 64) (ws : List (BitVec 64))
    (hlen : 8 * ws.length ≤ 2 ^ 64) :
    SepProp.BoundedFootprint (a ↦₆₄* ws) (8 * ws.length) := by
  induction ws generalizing a with
  | nil =>
    simpa [pointsToWords64_nil] using SepProp.BoundedFootprint.emp
  | cons w rest ih =>
    simp only [List.length_cons] at hlen ⊢
    rw [pointsToWords64_cons]
    exact SepProp.BoundedFootprint.mono
      (SepProp.BoundedFootprint.sepConj (BoundedFootprint_pointsTo64 a w)
        (ih (a + 8#64) (by omega)))
      (by omega)

theorem BoundedFootprint_dynamicMaps (dom : List (BitVec 64))
    (keepRw : BitVec 64 → Prop) [DecidablePred keepRw]
    (keepPn : BitVec 64 → Prop) [DecidablePred keepPn]
    (keepMp : BitVec 64 → Prop) [DecidablePred keepMp]
    (val : BitVec 64 → BitVec 8) :
    SepProp.BoundedFootprint
      (ByteMap dom keepRw val ∗ ProtNoneByteMap dom keepPn val ∗ MappedSet dom keepMp)
      dom.length :=
  SepProp.BoundedFootprint.of_footprintIn (dom := dom)
    (SepProp.FootprintIn.sepConj (ByteMap_footprintIn dom keepRw val)
      (SepProp.FootprintIn.sepConj (ProtNoneByteMap_footprintIn dom keepPn val)
        (MappedSet_footprintIn dom keepMp)))
    (Nat.le_refl dom.length)

end VerifiedLibraries.Mallocng.Proofs

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.ProgramReflection
public meta import Lean

/-!
# Balanced Random-Access Trees and Symbol Search Trees

Provides `O(log N)` kernel-verified random-access trees (`IdxTree α`) and string-keyed binary
search trees (`SymBST α`) for proof-by-reflection over large code-block and symbol tables.

- `IdxTree α` caches left-subtree leaf counts (`leftSize : Nat`). The `idx_tree_of% xs` elaborator
  constructs a balanced `IdxTree α` sharing the exact element `Expr` subterms of `xs`, so
  `t.toList = xs` closes by pointer equality in the kernel (`rfl_kernel`).
- `SymBST α`, `charListBeq`, `charListCmp`, and `hashChars1024` provide primitive-`Nat`
  character comparison, hashing, and balanced search trees for `O(log S)` symbol lookup and
  linear-time `Nodup` verification (`nodup_of_symBST_ranks`, `nodup_flatMap_of_symBST_blockRanks`).
-/

set_option autoImplicit false

namespace ProofLib.ProgramReflection

@[expose] public section

universe u

/-! ## Balanced Random-Access Tree `IdxTree` -/

/-- Balanced binary random-access tree over elements of type `α`.
    Each `.node leftSize left right` stores the exact leaf count `leftSize` of `left`. -/
inductive IdxTree (α : Type u) where
  | empty : IdxTree α
  | leaf : α → IdxTree α
  | node : Nat → IdxTree α → IdxTree α → IdxTree α

/-- Flatten an `IdxTree` onto an accumulator list in `O(N)` steps with `O(log N)` call depth. -/
def IdxTree.toListAux {α : Type u} : IdxTree α → List α → List α
  | .empty, acc => acc
  | .leaf x, acc => x :: acc
  | .node _ l r, acc => l.toListAux (r.toListAux acc)

/-- Flatten an `IdxTree` to its underlying list of elements. -/
def IdxTree.toList {α : Type u} (t : IdxTree α) : List α :=
  t.toListAux []

@[simp] theorem IdxTree.toList_empty {α : Type u} :
    (IdxTree.empty : IdxTree α).toList = [] := rfl

@[simp] theorem IdxTree.toList_leaf {α : Type u} (x : α) :
    (IdxTree.leaf x).toList = [x] := rfl

theorem IdxTree.toListAux_eq {α : Type u} (t : IdxTree α) (acc : List α) :
    t.toListAux acc = t.toListAux [] ++ acc := by
  induction t generalizing acc with
  | empty => simp [toListAux]
  | leaf x => simp [toListAux]
  | node _ l r ihl ihr =>
    simp only [toListAux]
    rw [ihr acc, ihl (r.toListAux [] ++ acc), ihl (r.toListAux []), List.append_assoc]

@[simp] theorem IdxTree.toList_node {α : Type u} (n : Nat) (l r : IdxTree α) :
    (IdxTree.node n l r).toList = l.toList ++ r.toList := by
  simp only [toList, toListAux]
  exact toListAux_eq l (r.toListAux [])

/-- Validated leaf count: returns `some sz` iff every internal node stores `l.size? = some ls`. -/
def IdxTree.size? {α : Type u} : IdxTree α → Option Nat
  | .empty => some 0
  | .leaf _ => some 1
  | .node leftSize l r =>
    match l.size?, r.size? with
    | some ls, some rs => if Nat.beq ls leftSize then some (ls + rs) else none
    | _, _ => none

theorem IdxTree.length_toList_of_size? {α : Type u} {t : IdxTree α} {sz : Nat}
    (h : t.size? = some sz) : t.toList.length = sz := by
  induction t generalizing sz with
  | empty =>
    simp only [size?, Option.some.injEq] at h
    subst h; rfl
  | leaf x =>
    simp only [size?, Option.some.injEq] at h
    subst h; rfl
  | node leftSize l r ihl ihr =>
    simp only [size?] at h
    cases hls : l.size? with
    | none => simp [hls] at h
    | some ls =>
      cases hrs : r.size? with
      | none => simp [hls, hrs] at h
      | some rs =>
        simp only [hls, hrs] at h
        cases hbeq : Nat.beq ls leftSize with
        | false => simp [hbeq] at h
        | true =>
          simp only [hbeq, ↓reduceIte, Option.some.injEq] at h
          subst h
          rw [toList_node, List.length_append, ihl hls, ihr hrs]

/-- Look up element `idx` in `O(log N)` steps using cached `leftSize` bounds. -/
def IdxTree.get? {α : Type u} : IdxTree α → Nat → Option α
  | .empty, _ => none
  | .leaf x, 0 => some x
  | .leaf _, _ + 1 => none
  | .node leftSize l r, idx =>
    if idx < leftSize then l.get? idx else r.get? (idx - leftSize)

/-- Unconditional membership soundness: any element returned by `get?` belongs to `toList`,
    even without a `size?` certificate. -/
theorem IdxTree.mem_toList_of_get? {α : Type u} {t : IdxTree α} {i : Nat} {x : α}
    (h : t.get? i = some x) : x ∈ t.toList := by
  induction t generalizing i with
  | empty => simp [get?] at h
  | leaf y =>
    cases i with
    | zero =>
      simp only [get?, Option.some.injEq] at h
      subst h; simp [toList_leaf]
    | succ _ => simp [get?] at h
  | node leftSize l r ihl ihr =>
    simp only [get?] at h
    rw [toList_node, List.mem_append]
    split at h
    · exact Or.inl (ihl h)
    · exact Or.inr (ihr h)

/-- Under a valid `size?` certificate, `t.get? i` agrees exactly with list indexing `t.toList[i]?`. -/
theorem IdxTree.get?_eq_getElem? {α : Type u} {t : IdxTree α} {sz : Nat}
    (hsz : t.size? = some sz) (i : Nat) : t.get? i = t.toList[i]? := by
  induction t generalizing sz i with
  | empty => simp [get?]
  | leaf x =>
    cases i with
    | zero => rfl
    | succ k => simp [get?]
  | node leftSize l r ihl ihr =>
    simp only [size?] at hsz
    cases hls : l.size? with
    | none => simp [hls] at hsz
    | some ls =>
      cases hrs : r.size? with
      | none => simp [hls, hrs] at hsz
      | some rs =>
        simp only [hls, hrs] at hsz
        cases hbeq : Nat.beq ls leftSize with
        | false => simp [hbeq] at hsz
        | true =>
          have hls_eq : ls = leftSize := Nat.eq_of_beq_eq_true hbeq
          subst hls_eq
          have hllen : l.toList.length = ls := l.length_toList_of_size? hls
          simp only [get?, toList_node]
          by_cases hi : i < ls
          · simp only [hi, ↓reduceIte]
            rw [ihl hls i, List.getElem?_append_left (by omega)]
          · simp only [hi, ↓reduceIte]
            rw [ihr hrs (i - ls), List.getElem?_append_right (by omega), hllen]

/-! ## Tree-Wide Boolean Folds (`all`, `allIdx`) -/

/-- Check `p` on every leaf of `t` with `O(log N)` recursion depth. -/
def IdxTree.all {α : Type u} (p : α → Bool) : IdxTree α → Bool
  | .empty => true
  | .leaf x => p x
  | .node _ l r => l.all p && r.all p

theorem IdxTree.all_eq_toList_all {α : Type u} (p : α → Bool) (t : IdxTree α) :
    t.all p = t.toList.all p := by
  induction t with
  | empty => rfl
  | leaf x => simp [all]
  | node _ l r ihl ihr =>
    simp only [all, toList_node, List.all_append, ihl, ihr]

/-- Indexed boolean fold over a list starting at index `base`. -/
def checkListIdx {α : Type u} (p : Nat → α → Bool) : Nat → List α → Bool
  | _, [] => true
  | base, x :: rest => p base x && checkListIdx p (base + 1) rest

theorem checkListIdx_eq_true_iff {α : Type u} (p : Nat → α → Bool) (base : Nat) (xs : List α) :
    checkListIdx p base xs = true ↔ ∀ k (hk : k < xs.length), p (base + k) xs[k] = true := by
  induction xs generalizing base with
  | nil => simp [checkListIdx]
  | cons x rest ih =>
    simp only [checkListIdx, Bool.and_eq_true, ih, List.length_cons]
    constructor
    · rintro ⟨h0, hrest⟩ k hk
      cases k with
      | zero => simpa using h0
      | succ k' =>
        have hk' : k' < rest.length := by omega
        have := hrest k' hk'
        have hadd : base + 1 + k' = base + (k' + 1) := by omega
        rw [hadd] at this
        simpa using this
    · intro hall
      refine ⟨by simpa using hall 0 (by omega), fun k' hk' => ?_⟩
      have := hall (k' + 1) (by omega)
      have hadd : base + (k' + 1) = base + 1 + k' := by omega
      rw [← hadd]
      simpa using this

/-- Check `p (base + k) x` on every leaf `k` of `t` with `O(log N)` recursion depth. -/
def IdxTree.allIdx {α : Type u} (p : Nat → α → Bool) : Nat → IdxTree α → Bool
  | _, .empty => true
  | base, .leaf x => p base x
  | base, .node leftSize l r => l.allIdx p base && r.allIdx p (base + leftSize)

private theorem checkListIdx_append {α : Type u} (p : Nat → α → Bool) (base : Nat)
    (xs ys : List α) :
    checkListIdx p base (xs ++ ys) =
      (checkListIdx p base xs && checkListIdx p (base + xs.length) ys) := by
  induction xs generalizing base with
  | nil => simp [checkListIdx]
  | cons x rest ih =>
    simp only [List.cons_append, checkListIdx, ih, List.length_cons, Bool.and_assoc]
    have hadd : base + 1 + rest.length = base + (rest.length + 1) := by omega
    rw [hadd]

theorem IdxTree.allIdx_eq_checkListIdx {α : Type u} (p : Nat → α → Bool) {t : IdxTree α}
    {sz : Nat} (hsz : t.size? = some sz) (base : Nat) :
    t.allIdx p base = checkListIdx p base t.toList := by
  induction t generalizing sz base with
  | empty => rfl
  | leaf x => simp [allIdx, checkListIdx]
  | node leftSize l r ihl ihr =>
    simp only [size?] at hsz
    cases hls : l.size? with
    | none => simp [hls] at hsz
    | some ls =>
      cases hrs : r.size? with
      | none => simp [hls, hrs] at hsz
      | some rs =>
        simp only [hls, hrs] at hsz
        cases hbeq : Nat.beq ls leftSize with
        | false => simp [hbeq] at hsz
        | true =>
          have hls_eq : ls = leftSize := Nat.eq_of_beq_eq_true hbeq
          subst hls_eq
          have hllen : l.toList.length = ls := l.length_toList_of_size? hls
          simp only [allIdx, toList_node, checkListIdx_append, ihl hls base,
            ihr hrs (base + ls), hllen]

theorem IdxTree.allIdx_eq_true_iff {α : Type u} (p : Nat → α → Bool) {t : IdxTree α}
    {sz : Nat} (hsz : t.size? = some sz) (base : Nat) :
    t.allIdx p base = true ↔ ∀ k (hk : k < t.toList.length), p (base + k) t.toList[k] = true := by
  rw [t.allIdx_eq_checkListIdx p hsz base, checkListIdx_eq_true_iff]

/-! ## Computable Balanced Builders (`ofArray`, `ofList`) -/

/-- Build a balanced `IdxTree` over slice `[start, start + len)` of `arr`. -/
def IdxTree.ofArraySlice {α : Type u} (arr : Array α) : Nat → Nat → IdxTree α
  | _, 0 => .empty
  | start, 1 =>
    if h : start < arr.size then .leaf arr[start] else .empty
  | start, len + 2 =>
    let n := len + 2
    let half := n / 2
    .node half (ofArraySlice arr start half) (ofArraySlice arr (start + half) (n - half))
termination_by _ len => len
decreasing_by all_goals omega

/-- Build a balanced `IdxTree` from an `Array`. -/
def IdxTree.ofArray {α : Type u} (arr : Array α) : IdxTree α :=
  IdxTree.ofArraySlice arr 0 arr.size

/-- Build a balanced `IdxTree` from a `List`. -/
def IdxTree.ofList {α : Type u} (xs : List α) : IdxTree α :=
  IdxTree.ofArray xs.toArray

/-- Map `f` over every leaf of an `IdxTree`, preserving tree shape and cached sizes. -/
def IdxTree.map {α β : Type u} (f : α → β) : IdxTree α → IdxTree β
  | .empty => .empty
  | .leaf x => .leaf (f x)
  | .node sz l r => .node sz (l.map f) (r.map f)

theorem IdxTree.toList_map {α β : Type u} (f : α → β) :
    ∀ (t : IdxTree α), (t.map f).toList = t.toList.map f
  | .empty => rfl
  | .leaf _ => rfl
  | .node _ l r => by
    simp [IdxTree.map, IdxTree.toList_node, IdxTree.toList_map f l, IdxTree.toList_map f r]

theorem IdxTree.get?_map {α β : Type u} (f : α → β) :
    ∀ (t : IdxTree α) (i : Nat), (t.map f).get? i = (t.get? i).map f
  | .empty, _ => rfl
  | .leaf _, 0 => rfl
  | .leaf _, _ + 1 => rfl
  | .node leftSize l r, i => by
    simp only [IdxTree.map, IdxTree.get?, IdxTree.get?_map f l i, IdxTree.get?_map f r (i - leftSize)]
    by_cases hi : i < leftSize <;> simp [hi]

/-! ## `List Char` Comparison, Hashing, and `SymBST` -/

/-- Structural `Bool` equality on `List Char` via primitive kernel `Nat.beq` on scalar values,
    short-circuiting on first mismatch and avoiding `Decidable` proof-term allocation. -/
def charListBeq : List Char → List Char → Bool
  | [], [] => true
  | a :: as, b :: bs => if Nat.beq a.val.toNat b.val.toNat then charListBeq as bs else false
  | _, _ => false

theorem charListBeq_refl (cs : List Char) : charListBeq cs cs = true := by
  induction cs with
  | nil => rfl
  | cons c rest ih => simp [charListBeq, ih]

private theorem char_eq_of_val_toNat_eq {a b : Char} (h : a.val.toNat = b.val.toNat) : a = b :=
  Char.ext (UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h))

theorem charListBeq_iff_eq {xs ys : List Char} : charListBeq xs ys = true ↔ xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [charListBeq]
  | cons a as ih =>
    cases ys with
    | nil => simp [charListBeq]
    | cons b bs =>
      simp only [charListBeq, List.cons.injEq]
      cases h : Nat.beq a.val.toNat b.val.toNat with
      | false =>
        have hne : a ≠ b := fun heq => by subst heq; simp at h
        simp [hne]
      | true =>
        have heq : a = b := char_eq_of_val_toNat_eq (Nat.eq_of_beq_eq_true h)
        subst heq
        simpa using ih

/-- Total 1024-bucket hash on `List Char` (`0 ≤ hashChars1024 cs < 1024`) built strictly from
    primitive kernel `Nat.mul` / `Nat.add` / `Nat.land` operations over every character.
    Used strictly as an untrusted bucket selector; collisions are resolved by exact `charListBeq`. -/
def hashChars1024 (cs : List Char) : Nat :=
  let rec go (h : Nat) : List Char → Nat
    | [] => Nat.land h 1023
    | c :: rest => go (Nat.land (Nat.add (Nat.mul h 131) c.val.toNat) 1073741823) rest
  go 5381 cs

/-- Kernel-fast lexicographic comparison on `List Char` consistent with `charListLt`. -/
def charListCmp : List Char → List Char → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs =>
    if Nat.beq a.val.toNat b.val.toNat then charListCmp as bs
    else if Nat.blt a.val.toNat b.val.toNat then .lt else .gt

theorem charListCmp_eq_iff {xs ys : List Char} : charListCmp xs ys = .eq ↔ xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [charListCmp]
  | cons a as ih =>
    cases ys with
    | nil => simp [charListCmp]
    | cons b bs =>
      simp only [charListCmp, List.cons.injEq]
      cases h : Nat.beq a.val.toNat b.val.toNat with
      | true =>
        have heq : a = b := char_eq_of_val_toNat_eq (Nat.eq_of_beq_eq_true h)
        subst heq; simpa using ih
      | false =>
        have hne : a ≠ b := fun heq => by subst heq; simp at h
        cases Nat.blt a.val.toNat b.val.toNat <;> simp [hne]

theorem charListCmp_lt_iff {xs ys : List Char} : charListCmp xs ys = .lt ↔ charListLt xs ys = true := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [charListCmp, charListLt]
  | cons a as ih =>
    cases ys with
    | nil => simp [charListCmp, charListLt]
    | cons b bs =>
      simp only [charListCmp, charListLt]
      cases Nat.beq a.val.toNat b.val.toNat with
      | true => simpa using ih
      | false => cases Nat.blt a.val.toNat b.val.toNat <;> simp

theorem charListCmp_gt_iff {xs ys : List Char} : charListCmp xs ys = .gt ↔ charListLt ys xs = true := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [charListCmp, charListLt]
  | cons a as ih =>
    cases ys with
    | nil => simp [charListCmp, charListLt]
    | cons b bs =>
      simp only [charListCmp, charListLt, Nat.beq_eq, Nat.blt_eq, Char.toNat_val]
      by_cases hab : a.toNat = b.toNat
      · simp [hab, ih]
      · have hba : b.toNat ≠ a.toNat := Ne.symm hab
        by_cases hlt : a.toNat < b.toNat
        · have hnot : ¬ b.toNat < a.toNat := by omega
          simp [hab, hba, hlt, hnot]
        · have hbgt : b.toNat < a.toNat := by omega
          simp [hab, hba, hlt, hbgt]

/-- Balanced binary search tree keyed by `List Char` with cached left-subtree size `leftSize`
    for `O(log S)` key search (`find?`) and in-order rank projection (`get?`). -/
inductive SymBST (α : Type) where
  | empty : SymBST α
  | node : Nat → List Char → α → SymBST α → SymBST α → SymBST α

def SymBST.toListAux {α : Type} : SymBST α → List (List Char × α) → List (List Char × α)
  | .empty, acc => acc
  | .node _ k v l r, acc => l.toListAux ((k, v) :: r.toListAux acc)

def SymBST.toList {α : Type} (t : SymBST α) : List (List Char × α) :=
  t.toListAux []

theorem SymBST.toListAux_eq {α : Type} (t : SymBST α) (acc : List (List Char × α)) :
    t.toListAux acc = t.toListAux [] ++ acc := by
  induction t generalizing acc with
  | empty => rfl
  | node sz k v l r ihl ihr =>
    simp only [toListAux]
    rw [ihl ((k, v) :: r.toListAux acc), ihl ((k, v) :: r.toListAux []), ihr acc]
    simp [List.append_assoc]

@[simp] theorem SymBST.toList_empty {α : Type} : (SymBST.empty : SymBST α).toList = [] := rfl

@[simp] theorem SymBST.toList_node {α : Type} (sz : Nat) (k : List Char) (v : α)
    (l r : SymBST α) :
    (SymBST.node sz k v l r).toList = l.toList ++ (k, v) :: r.toList := by
  simp only [toList, toListAux]
  exact SymBST.toListAux_eq l ((k, v) :: r.toListAux [])

/-- Look up the entry at in-order rank `idx` in `O(log S)` steps using cached `leftSize`. -/
def SymBST.get? {α : Type} : SymBST α → Nat → Option (List Char × α)
  | .empty, _ => none
  | .node leftSize k v l r, idx =>
    if Nat.blt idx leftSize then l.get? idx
    else if Nat.beq idx leftSize then some (k, v)
    else r.get? (idx - leftSize - 1)

theorem SymBST.mem_toList_of_get? {α : Type} {t : SymBST α} {idx : Nat} {p : List Char × α}
    (h : t.get? idx = some p) : p ∈ t.toList := by
  induction t generalizing idx with
  | empty => simp [get?] at h
  | node leftSize k v l r ihl ihr =>
    simp only [get?] at h
    rw [toList_node, List.mem_append, List.mem_cons]
    cases hlt : Nat.blt idx leftSize with
    | true => simp only [hlt, ↓reduceIte] at h; exact Or.inl (ihl h)
    | false =>
      simp only [hlt, Bool.false_eq_true, ↓reduceIte] at h
      cases heq : Nat.beq idx leftSize with
      | true =>
        simp only [heq, ↓reduceIte, Option.some.injEq] at h
        exact Or.inr (Or.inl h.symm)
      | false =>
        simp only [heq, Bool.false_eq_true, ↓reduceIte] at h
        exact Or.inr (Or.inr (ihr h))

/-- Look up key `cs` in `O(log S)` comparisons via `charListCmp`. -/
def SymBST.find? {α : Type} : SymBST α → List Char → Option α
  | .empty, _ => none
  | .node _ k v l r, cs =>
    match charListCmp cs k with
    | .eq => some v
    | .lt => l.find? cs
    | .gt => r.find? cs

theorem SymBST.mem_toList_of_find? {α : Type} {t : SymBST α} {cs : List Char} {v : α}
    (h : t.find? cs = some v) : (cs, v) ∈ t.toList := by
  induction t with
  | empty => simp [find?] at h
  | node sz k val l r ihl ihr =>
    simp only [find?] at h
    rw [toList_node, List.mem_append, List.mem_cons]
    cases hc : charListCmp cs k with
    | eq =>
      simp only [hc, Option.some.injEq] at h
      subst h
      exact Or.inr (Or.inl (Prod.ext (charListCmp_eq_iff.mp hc) rfl))
    | lt => simp only [hc] at h; exact Or.inl (ihl h)
    | gt => simp only [hc] at h; exact Or.inr (Or.inr (ihr h))

theorem SymBST.find?_eq_some_of_pairwise {α : Type} {t : SymBST α}
    (hpw : t.toList.Pairwise (fun a b => charListLt a.1 b.1 = true))
    {cs : List Char} {v : α} (hmem : (cs, v) ∈ t.toList) :
    t.find? cs = some v := by
  induction t with
  | empty => simp at hmem
  | node sz k val l r ihl ihr =>
    rw [toList_node, List.pairwise_append] at hpw
    obtain ⟨hpw_l, hpw_cr, hcross⟩ := hpw
    rw [List.pairwise_cons] at hpw_cr
    obtain ⟨hk_lt_r, hpw_r⟩ := hpw_cr
    rw [toList_node, List.mem_append, List.mem_cons] at hmem
    simp only [find?]
    rcases hmem with hl | heq | hr
    · have hlt : charListLt cs k = true := hcross (cs, v) hl (k, val) List.mem_cons_self
      rw [charListCmp_lt_iff.mpr hlt]; exact ihl hpw_l hl
    · rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
      rw [charListCmp_eq_iff.mpr rfl]
    · have hgt : charListLt k cs = true := hk_lt_r (cs, v) hr
      rw [charListCmp_gt_iff.mpr hgt]; exact ihr hpw_r hr

theorem SymBST.find?_eq_some_of_mem {α : Type} {t : SymBST α}
    (hsort : isStrictSorted t.toList = true) {cs : List Char} {v : α}
    (hmem : (cs, v) ∈ t.toList) : t.find? cs = some v :=
  t.find?_eq_some_of_pairwise
    (strictChain_pairwise (fun (a b : List Char × α) => charListLt a.1 b.1)
      (fun h₁ h₂ => charListLt_trans h₁ h₂) _ hsort) hmem

theorem SymBST.not_mem_of_find?_eq_none {α : Type} {t : SymBST α}
    (hsort : isStrictSorted t.toList = true) {cs : List Char}
    (hnone : t.find? cs = none) (v : α) : (cs, v) ∉ t.toList := by
  intro hmem
  have hs := t.find?_eq_some_of_mem hsort hmem
  rw [hnone] at hs; cases hs

private theorem pairwise_key_inj {α : Type} {l : List (List Char × α)}
    (hpw : l.Pairwise (fun a b => a.1 ≠ b.1))
    {cs : List Char} {v₁ v₂ : α} (h₁ : (cs, v₁) ∈ l) (h₂ : (cs, v₂) ∈ l) : v₁ = v₂ := by
  induction l with
  | nil => cases h₁
  | cons hd tl ih =>
    rw [List.pairwise_cons] at hpw
    rcases List.mem_cons.mp h₁ with rfl | h₁' <;> rcases List.mem_cons.mp h₂ with h₂_eq | h₂'
    · exact (Prod.mk.inj h₂_eq).2.symm
    · exact absurd rfl (hpw.1 (cs, v₂) h₂')
    · exact absurd (Prod.mk.inj h₂_eq).1.symm (hpw.1 (cs, v₁) h₁')
    · exact ih hpw.2 h₁' h₂'

/-- Project `ranks` through `t.get?` onto `Option (String × Nat)` via `String.ofList`. -/
def mapSymRanks (t : SymBST Nat) : List Nat → List (Option (String × Nat))
  | [] => []
  | r :: rs =>
    (match t.get? r with
     | some (cs, idx) => some (String.ofList cs, idx)
     | none => none) :: mapSymRanks t rs

/-- Pair each symbol in `ss` with its index starting from `base`. -/
def mapSomeZipIdx : List String → Nat → List (Option (String × Nat))
  | [], _ => []
  | s :: ss, i => some (s, i) :: mapSomeZipIdx ss (Nat.add i 1)

theorem mem_symBST_of_mapSymRanks {t : SymBST Nat} {ranks : List Nat} {syms : List String}
    {base : Nat} (h : mapSymRanks t ranks = mapSomeZipIdx syms base)
    {k : Nat} {s : String} (hk : syms[k]? = some s) :
    ∃ cs, String.ofList cs = s ∧ (cs, base + k) ∈ t.toList := by
  induction syms generalizing ranks base k with
  | nil => simp at hk
  | cons s0 rest ih =>
    cases ranks with
    | nil => simp [mapSymRanks, mapSomeZipIdx] at h
    | cons r rs =>
      simp only [mapSymRanks, mapSomeZipIdx, List.cons.injEq] at h
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
        subst hk
        cases hg : t.get? r with
        | none => simp [hg] at h
        | some p =>
          rcases p with ⟨cs, idx⟩
          simp only [hg, Option.some.injEq, Prod.mk.injEq] at h
          rcases h.1 with ⟨hcs, rfl⟩
          exact ⟨cs, hcs, Nat.add_zero idx ▸ SymBST.mem_toList_of_get? hg⟩
      | succ k' =>
        simp only [List.getElem?_cons_succ] at hk
        obtain ⟨cs, hcs, hmem⟩ := ih h.2 hk
        exact ⟨cs, hcs, by simpa [Nat.add_eq, Nat.add_assoc, Nat.add_comm 1 k'] using hmem⟩

/-- Prove `syms.Nodup` in linear kernel time from a strictly sorted `SymBST Nat` and rank table. -/
theorem nodup_of_symBST_ranks {t : SymBST Nat} {ranks : List Nat} {syms : List String}
    (hsort : isStrictSorted t.toList = true)
    (hranks : mapSymRanks t ranks = mapSomeZipIdx syms 0) : syms.Nodup := by
  have hpw := pairwise_ne_of_strictSorted hsort
  rw [List.Nodup, List.pairwise_iff_getElem]
  intro i j hi hj hlt heq
  obtain ⟨cs₁, hs₁, hm₁⟩ := mem_symBST_of_mapSymRanks hranks (List.getElem?_eq_getElem hi)
  obtain ⟨cs₂, hs₂, hm₂⟩ := mem_symBST_of_mapSymRanks hranks (List.getElem?_eq_getElem hj)
  have hcs : cs₁ = cs₂ := String.ofList_inj.mp (hs₁.trans (heq.trans hs₂.symm))
  subst hcs
  have hidx := pairwise_key_inj hpw hm₁ hm₂
  omega

/-- Project within-block symbol ranks through `t.get?`, checking `(blkIdx, symIdx)` positions. -/
def mapInnerSymRanks (t : SymBST (Nat × Nat × Nat)) (blkIdx : Nat) :
    Nat → List Nat → Option (List (String × Nat))
  | _, [] => some []
  | j, r :: rs =>
    match t.get? r, mapInnerSymRanks t blkIdx (Nat.add j 1) rs with
    | some (cs, (bi, sj, off)), some tail =>
      if Nat.beq bi blkIdx && Nat.beq sj j then some ((String.ofList cs, off) :: tail) else none
    | _, _ => none

/-- Project nested block symbol rank lists through `t.get?`. -/
def mapBlockSymRanks (t : SymBST (Nat × Nat × Nat)) :
    Nat → List (List Nat) → Option (List (List (String × Nat)))
  | _, [] => some []
  | blkIdx, rs :: rest =>
    match mapInnerSymRanks t blkIdx 0 rs, mapBlockSymRanks t (Nat.add blkIdx 1) rest with
    | some syms, some tail => some (syms :: tail)
    | _, _ => none

theorem mem_symBST_of_mapInnerSymRanks {t : SymBST (Nat × Nat × Nat)} {blkIdx base : Nat}
    {rs : List Nat} {syms : List (String × Nat)}
    (h : mapInnerSymRanks t blkIdx base rs = some syms)
    {k : Nat} {s : String} {off : Nat} (hk : syms[k]? = some (s, off)) :
    ∃ cs, String.ofList cs = s ∧ (cs, (blkIdx, base + k, off)) ∈ t.toList := by
  induction rs generalizing base syms k with
  | nil =>
    simp only [mapInnerSymRanks, Option.some.injEq] at h
    subst h; simp at hk
  | cons r rs' ih =>
    simp only [mapInnerSymRanks] at h
    cases hg : t.get? r with
    | none => simp [hg] at h
    | some p =>
      rcases p with ⟨cs, bi, sj, o⟩
      cases htl : mapInnerSymRanks t blkIdx (Nat.add base 1) rs' with
      | none => simp [hg, htl] at h
      | some tail =>
        simp only [hg, htl] at h
        cases hchk : (Nat.beq bi blkIdx && Nat.beq sj base) with
        | false => simp [hchk] at h
        | true =>
          simp only [hchk, ↓reduceIte, Option.some.injEq] at h
          subst h
          simp only [Bool.and_eq_true, Nat.beq_eq] at hchk
          rcases hchk with ⟨rfl, rfl⟩
          cases k with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hk
            rcases hk with ⟨hcs, rfl⟩
            exact ⟨cs, hcs, Nat.add_zero sj ▸ SymBST.mem_toList_of_get? hg⟩
          | succ k' =>
            simp only [List.getElem?_cons_succ] at hk
            obtain ⟨cs', hcs', hm'⟩ := ih htl hk
            exact ⟨cs', hcs', by simpa [Nat.add_eq, Nat.add_assoc, Nat.add_comm 1 k'] using hm'⟩

theorem mem_symBST_of_mapBlockSymRanks {t : SymBST (Nat × Nat × Nat)} {base : Nat}
    {blkRanks : List (List Nat)} {symLists : List (List (String × Nat))}
    (h : mapBlockSymRanks t base blkRanks = some symLists)
    {i : Nat} {syms : List (String × Nat)} (hi : symLists[i]? = some syms)
    {k : Nat} {s : String} {off : Nat} (hk : syms[k]? = some (s, off)) :
    ∃ cs, String.ofList cs = s ∧ (cs, (base + i, k, off)) ∈ t.toList := by
  induction blkRanks generalizing base symLists i with
  | nil =>
    simp only [mapBlockSymRanks, Option.some.injEq] at h
    subst h; simp at hi
  | cons rs rest ih =>
    simp only [mapBlockSymRanks] at h
    cases hin : mapInnerSymRanks t base 0 rs with
    | none => simp [hin] at h
    | some s0 =>
      cases htl : mapBlockSymRanks t (Nat.add base 1) rest with
      | none => simp [hin, htl] at h
      | some tail =>
        simp only [hin, htl, Option.some.injEq] at h
        subst h
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
          subst hi
          obtain ⟨cs, hcs, hm⟩ := mem_symBST_of_mapInnerSymRanks hin hk
          exact ⟨cs, hcs, by simpa using hm⟩
        | succ i' =>
          simp only [List.getElem?_cons_succ] at hi
          obtain ⟨cs, hcs, hm⟩ := ih htl hi
          exact ⟨cs, hcs, by simpa [Nat.add_eq, Nat.add_assoc, Nat.add_comm 1 i'] using hm⟩

private theorem getElem?_of_mem {α : Type} {x : α} {l : List α} (h : x ∈ l) :
    ∃ k : Nat, l[k]? = some x := by
  induction l with
  | nil => cases h
  | cons hd tl ih =>
    rcases List.mem_cons.mp h with rfl | htl
    · exact ⟨0, rfl⟩
    · obtain ⟨k, hk⟩ := ih htl; exact ⟨k + 1, hk⟩

theorem nodup_flatMap_of_symBST_blockRanks {t : SymBST (Nat × Nat × Nat)}
    {blkRanks : List (List Nat)} {symLists : List (List (String × Nat))}
    (hsort : isStrictSorted t.toList = true)
    (hranks : mapBlockSymRanks t 0 blkRanks = some symLists) :
    ((symLists.flatMap id).map Prod.fst).Nodup := by
  have hpw := pairwise_ne_of_strictSorted hsort
  have keyInj {i₁ k₁ o₁ i₂ k₂ o₂ : Nat} {cs₁ cs₂ : List Char} {s : String}
      (hs₁ : String.ofList cs₁ = s) (hm₁ : (cs₁, (i₁, k₁, o₁)) ∈ t.toList)
      (hs₂ : String.ofList cs₂ = s) (hm₂ : (cs₂, (i₂, k₂, o₂)) ∈ t.toList) :
      i₁ = i₂ ∧ k₁ = k₂ := by
    have hcs : cs₁ = cs₂ := String.ofList_inj.mp (hs₁.trans hs₂.symm)
    subst hcs
    have heq := pairwise_key_inj hpw hm₁ hm₂
    simp only [Prod.mk.injEq] at heq
    exact ⟨heq.1, heq.2.1⟩
  suffices hgen : ∀ (lists : List (List (String × Nat))) (base : Nat),
      (∀ i syms k s off, lists[i]? = some syms → syms[k]? = some (s, off) →
        ∃ cs, String.ofList cs = s ∧ (cs, (base + i, k, off)) ∈ t.toList) →
      ((lists.flatMap id).map Prod.fst).Nodup by
    exact hgen symLists 0 fun i syms k s off hi hk =>
      mem_symBST_of_mapBlockSymRanks hranks hi hk
  intro lists base hmem
  induction lists generalizing base with
  | nil => exact .nil
  | cons syms rest ih =>
    simp only [List.flatMap_cons, id_eq, List.map_append, List.nodup_append]
    refine ⟨?_, ih (base + 1) fun i s2 k s o hi hk => ?_, ?_⟩
    · rw [List.Nodup, List.pairwise_iff_getElem]
      intro k₁ k₂ hk₁ hk₂ hlt heq
      simp only [List.length_map] at hk₁ hk₂
      simp only [List.getElem_map] at heq
      obtain ⟨cs₁, hs₁, hm₁⟩ := hmem 0 syms k₁ syms[k₁].1 syms[k₁].2 rfl (List.getElem?_eq_getElem hk₁)
      obtain ⟨cs₂, hs₂, hm₂⟩ := hmem 0 syms k₂ syms[k₂].1 syms[k₂].2 rfl (List.getElem?_eq_getElem hk₂)
      have := (keyInj hs₁ hm₁ (hs₂.trans heq.symm) hm₂).2
      omega
    · obtain ⟨cs, hcs, hm⟩ := hmem (i + 1) s2 k s o (by simpa using hi) hk
      exact ⟨cs, hcs, by simpa [Nat.add_assoc, Nat.add_comm 1 i] using hm⟩
    · intro name₁ hn₁ name₂ hn₂ hname
      subst hname
      obtain ⟨p₁, hp₁, hp₁_eq⟩ := List.mem_map.mp hn₁
      obtain ⟨k₁, hk₁⟩ := getElem?_of_mem hp₁
      obtain ⟨p₂, hp₂, hp₂_eq⟩ := List.mem_map.mp hn₂
      obtain ⟨syms₂, hs2_mem, hp₂'⟩ := List.mem_flatMap.mp hp₂
      obtain ⟨i₂, hi₂⟩ := getElem?_of_mem hs2_mem
      obtain ⟨k₂, hk₂⟩ := getElem?_of_mem hp₂'
      obtain ⟨cs₁, hs₁, hm₁⟩ := hmem 0 syms k₁ p₁.1 p₁.2 rfl hk₁
      obtain ⟨cs₂, hs₂, hm₂⟩ := hmem (i₂ + 1) syms₂ k₂ p₂.1 p₂.2 (by simpa using hi₂) hk₂
      have := (keyInj (hs₁.trans hp₁_eq) hm₁ (hs₂.trans hp₂_eq) hm₂).1
      omega

end

/-! ## Subterm-Sharing Elaborators (`mkIdxTreeExpr`, `idx_tree_of%`) -/

public meta section

open Lean Elab Term Meta in
/-- Construct a balanced `IdxTree elemTy` expression from `elems`, reusing every element `Expr`
    verbatim so `tree.toList = list` reduces by pointer equality in the kernel. -/
protected def mkIdxTreeExpr (u : Level) (elemTy : Expr) (elems : Array Expr) : Expr :=
  let emptyE := mkApp (Lean.mkConst ``IdxTree.empty [u]) elemTy
  let leafFn := mkApp (Lean.mkConst ``IdxTree.leaf [u]) elemTy
  let nodeFn := mkApp (Lean.mkConst ``IdxTree.node [u]) elemTy
  let rec go (lo hi : Nat) : Expr :=
    if _h0 : hi - lo = 0 then
      emptyE
    else if _h1 : hi - lo = 1 then
      mkApp leafFn elems[lo]!
    else
      let half := (hi - lo) / 2
      let mid := lo + half
      mkApp3 nodeFn (mkRawNatLit half) (go lo mid) (go mid hi)
  termination_by hi - lo
  decreasing_by all_goals omega
  go 0 elems.size

open Lean Elab Term Meta in
/-- Build a balanced `IdxTree α` at elaboration time from a concrete `List α` expression `e`,
    preserving element `Expr` sharing for `O(N)` `rfl_kernel` flattening proofs. -/
scoped elab "idx_tree_of% " e:term : term => do
  let listExpr ← elabTerm e none
  let listTy ← whnf (← inferType (← instantiateMVars listExpr))
  let .app (.const ``List [u]) elemTy := listTy
    | throwError "idx_tree_of%: expected `List α`, got type {listTy}"
  let elems ← listElemsWhnf (← instantiateMVars listExpr)
  return ProofLib.ProgramReflection.mkIdxTreeExpr u elemTy elems

open Lean Elab Term Meta in
/-- Construct a `List Char` expression for `s` using direct `Char` constructor values so both
    `String.ofList cs = s` and `c.val.toNat` projections reduce directly in the kernel. -/
protected def mkCharListExpr (s : String) : Expr :=
  let charTy := Lean.mkConst ``Char
  let nilE := mkApp (Lean.mkConst ``List.nil [.zero]) charTy
  let consFn := mkApp (Lean.mkConst ``List.cons [.zero]) charTy
  s.toList.foldr (fun c acc => mkApp2 consFn (toExpr c) acc) nilE

open Lean Elab Term Meta in
/-- Build a balanced `SymBST valTy` expression from pre-sorted `(charListExpr, valExpr)` pairs,
    caching exact `leftSize` raw natural literals at each node. -/
protected partial def mkSymBSTExpr (valTy : Expr) (sorted : Array (Expr × Expr)) : Expr :=
  let emptyE := mkApp (Lean.mkConst ``SymBST.empty) valTy
  let nodeFn := mkApp (Lean.mkConst ``SymBST.node) valTy
  let rec go (lo hi : Nat) : Expr :=
    if lo < hi then
      let mid := (lo + hi) / 2
      let (ke, ve) := sorted[mid]!
      mkApp5 nodeFn (mkRawNatLit (mid - lo)) ke ve (go lo mid) (go (mid + 1) hi)
    else
      emptyE
  go 0 sorted.size

open Lean Elab Term Meta in
/-- Elaborate a concrete string literal or constant into its kernel-fast `List Char` term. -/
scoped elab "char_lit% " s:term:arg : term => do
  let strVal ← match s.raw.isStrLit? with
    | some str => pure str
    | none =>
      let e ← instantiateMVars (← elabTerm s (some (Lean.mkConst ``String)))
      if let .lit (.strVal str) := e then pure str
      else if let .lit (.strVal str) := (← withTransparency .all (whnf e)) then pure str
      else throwError "char_lit%: expected string literal or constant, got {e}"
  return ProofLib.ProgramReflection.mkCharListExpr strVal

end

end ProofLib.ProgramReflection

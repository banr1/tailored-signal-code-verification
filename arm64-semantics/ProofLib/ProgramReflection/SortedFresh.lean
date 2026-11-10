/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.ProgramReflection
import Arm64.Trusted.Spec.SepLogic

/-!
# Kernel Key-Freshness Check via Merge Sort

Decides pairwise distinctness of pre-encoded `(length, codepoints)` symbol keys in $O(n \log n)$
comparisons by sorting with a fuel-bounded merge sort (`mergeSortFuel`) and checking `strictChain keyLt`.
Soundness (`allFreshEntries_of_sortedFresh`) uses only that `mergeSortFuel` returns a permutation and
`keyLt` is irreflexive and transitive, avoiding quadratic term caching during `rfl_kernel` replay on
large symbol tables.
-/

namespace ProofLib.ProgramReflection

@[expose] public section

/-- Strict order on pre-encoded `(length, codepoints)` keys: length first, then lexicographic. -/
def keyLt (e₁ e₂ : Nat × List Nat) : Bool :=
  if Nat.beq e₁.1 e₂.1 then natListLt e₁.2 e₂.2 else Nat.blt e₁.1 e₂.1

private theorem beq_eq_false_of_ne {a b : Nat} (h : a ≠ b) : a.beq b = false := by
  cases hb : a.beq b with
  | true => exact absurd (Nat.eq_of_beq_eq_true hb) h
  | false => rfl

theorem keyLt_irrefl (e : Nat × List Nat) : keyLt e e = false := by
  simp only [keyLt, Nat.beq_refl, ↓reduceIte, natListLt_irrefl]

theorem keyLt_trans {e₁ e₂ e₃ : Nat × List Nat}
    (h₁ : keyLt e₁ e₂ = true) (h₂ : keyLt e₂ e₃ = true) : keyLt e₁ e₃ = true := by
  simp only [keyLt] at h₁ h₂ ⊢
  cases hab : Nat.beq e₁.1 e₂.1 <;> cases hbc : Nat.beq e₂.1 e₃.1 <;>
    simp only [hab, hbc, Bool.false_eq_true, ↓reduceIte] at h₁ h₂
  · rw [Nat.blt_eq] at h₁ h₂
    have hlt : e₁.1 < e₃.1 := Nat.lt_trans h₁ h₂
    have hac : e₁.1.beq e₃.1 = false := beq_eq_false_of_ne (Nat.ne_of_lt hlt)
    simp only [hac, Bool.false_eq_true, ↓reduceIte, Nat.blt_eq]
    exact hlt
  · have hab' : e₁.1 ≠ e₂.1 := Nat.ne_of_beq_eq_false hab
    have hac : e₁.1.beq e₃.1 = false :=
      beq_eq_false_of_ne ((Nat.eq_of_beq_eq_true hbc) ▸ hab')
    simp only [hac, Bool.false_eq_true, ↓reduceIte, Nat.blt_eq] at h₁ ⊢
    exact (Nat.eq_of_beq_eq_true hbc) ▸ h₁
  · have hbc' : e₂.1 ≠ e₃.1 := Nat.ne_of_beq_eq_false hbc
    have hac : e₁.1.beq e₃.1 = false :=
      beq_eq_false_of_ne ((Nat.eq_of_beq_eq_true hab) ▸ hbc')
    simp only [hac, Bool.false_eq_true, ↓reduceIte, Nat.blt_eq] at h₂ ⊢
    exact (Nat.eq_of_beq_eq_true hab) ▸ h₂
  · have hac : e₁.1 = e₃.1 := (Nat.eq_of_beq_eq_true hab).trans (Nat.eq_of_beq_eq_true hbc)
    simp only [hac, Nat.beq_refl, ↓reduceIte]
    exact natListLt_trans h₁ h₂

/-- Fuel-bounded merge of two lists; appends the remaining suffixes when fuel reaches zero, so the
    output is a permutation of `xs ++ ys` for every fuel value. -/
def mergeFuel {α : Type} (lt : α → α → Bool) : Nat → List α → List α → List α
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, x :: xs, [] => x :: xs
  | n + 1, x :: xs, y :: ys =>
    if lt y x then y :: mergeFuel lt n (x :: xs) ys else x :: mergeFuel lt n xs (y :: ys)

/-- Split a list into two sublists by alternating elements. -/
def splitAlt {α : Type} : List α → List α × List α
  | [] => ([], [])
  | a :: rest => (a :: (splitAlt rest).2, (splitAlt rest).1)

/-- Structurally recursive merge sort with recursion depth bounded by `fuel` (`l.length` suffices). -/
def mergeSortFuel {α : Type} (lt : α → α → Bool) : Nat → List α → List α
  | 0, l => l
  | _ + 1, [] => []
  | _ + 1, [a] => [a]
  | n + 1, a :: b :: rest =>
    let l := a :: b :: rest
    mergeFuel lt l.length (mergeSortFuel lt n (splitAlt l).1) (mergeSortFuel lt n (splitAlt l).2)

theorem mergeFuel_perm {α : Type} (lt : α → α → Bool) :
    ∀ (n : Nat) (xs ys : List α), (mergeFuel lt n xs ys).Perm (xs ++ ys)
  | 0, _, _ => List.Perm.refl _
  | _ + 1, [], _ => List.Perm.refl _
  | _ + 1, _ :: _, [] => by simp only [mergeFuel, List.append_nil]; exact List.Perm.refl _
  | n + 1, x :: xs, y :: ys => by
    simp only [mergeFuel]
    cases hxy : lt y x with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact (mergeFuel_perm lt n xs (y :: ys)).cons x
    | true =>
      simp only [↓reduceIte]
      exact ((mergeFuel_perm lt n (x :: xs) ys).cons y).trans List.perm_middle.symm

theorem splitAlt_perm {α : Type} : ∀ l : List α, ((splitAlt l).1 ++ (splitAlt l).2).Perm l
  | [] => List.Perm.refl _
  | a :: rest => by
    simp only [splitAlt, List.cons_append]
    exact (List.perm_append_comm.trans (splitAlt_perm rest)).cons a

theorem mergeSortFuel_perm {α : Type} (lt : α → α → Bool) :
    ∀ (n : Nat) (l : List α), (mergeSortFuel lt n l).Perm l
  | 0, _ => List.Perm.refl _
  | _ + 1, [] => List.Perm.refl _
  | _ + 1, [_] => List.Perm.refl _
  | n + 1, a :: b :: rest => by
    simp only [mergeSortFuel]
    exact (mergeFuel_perm lt _ _ _).trans
      (((mergeSortFuel_perm lt n _).append (mergeSortFuel_perm lt n _)).trans
        (splitAlt_perm (a :: b :: rest)))

/-- Sort pre-encoded keys and check that adjacent keys satisfy `keyLt`. -/
def sortedFreshEntries (l : List (Nat × List Nat)) : Bool :=
  strictChain keyLt (mergeSortFuel keyLt l.length l)

/-- Soundness of `sortedFreshEntries` with respect to `allFreshEntries`. -/
theorem allFreshEntries_of_sortedFresh {l : List (Nat × List Nat)}
    (h : sortedFreshEntries l = true) : allFreshEntries l = true :=
  allFreshEntries_of_pairwise l
    (((mergeSortFuel_perm keyLt l.length l).pairwise_iff (fun h => h.symm)).mp
      ((strictChain_pairwise keyLt keyLt_trans _ h).imp
        fun {a b} (hlt : keyLt a b = true) (heq : a = b) => by
          subst heq; rw [keyLt_irrefl] at hlt; exact Bool.false_ne_true hlt))

/-- Derive `allFreshCharSymbols` from `sortedFreshEntries`. -/
theorem allFreshCharSymbols_of_sorted {syms : List (List Char × Nat)}
    (h : sortedFreshEntries (prepareCharSymbols syms) = true) : allFreshCharSymbols syms = true :=
  allFreshEntries_of_sortedFresh h

/-- Derive `allFreshCharAssoc` from `sortedFreshEntries`. -/
theorem allFreshCharAssoc_of_sorted {α : Type} {syms : List (List Char × α)}
    (h : sortedFreshEntries (prepareCharAssoc syms) = true) : allFreshCharAssoc syms = true :=
  allFreshEntries_of_sortedFresh h

end

end ProofLib.ProgramReflection

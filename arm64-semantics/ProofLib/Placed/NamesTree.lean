/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Placed.Split

/-!
# Names-Tree Projection of an Interned Library

`Lib.toLib` resolves each name index through `L.names.getD i ""`, which takes time quadratic in
the library size on large symbol tables. `Lib.toLibT` computes the same projection through a
balanced `VecTree String` (`nameT`), and `Lib.toLibT_eq` equates it to `L.toLib` from bounded-size
chunk equalities (`NamesTreeOkChunks`) checkable by `rfl`.
-/

@[expose] public section

set_option autoImplicit false

namespace Arm64.Obj.Interned
open Arm64 ProofLib.Placed.Split

/-- `Reloc.toEntry` with the symbol name given by `nm`. -/
def Reloc.toEntryWith (nm : Nat → String) (r : Reloc) : RelocEntry :=
  { off := r.off, kind := r.kind, sym := nm r.sym, addend := r.addend, localSym := r.localSym }

/-- `Data.toInfo` with every name given by `nm`. -/
def Data.toInfoWith (nm : Nat → String) (d : Data) : SymDataInfo :=
  { sym := nm d.sym, align := d.align, readOnly := d.readOnly, bytes := d.bytes,
    zeroTail := d.zeroTail, relocs := d.relocs.map (Reloc.toEntryWith nm) }

/-- `Lib.toLib` with every name given by `nm`. -/
def Lib.toLibWith (L : Lib) (nm : Nat → String) : PlacedLib :=
  { name := L.name,
    text :=
      { code := L.code, align := L.align, symbols := L.symbols.map fun s => (nm s.1, s.2)
        relocs := L.relocs.map (Reloc.toEntryWith nm), externs := L.externs.map nm
        weakRefs := L.weakRefs.map nm },
    data := L.data.map (Data.toInfoWith nm), exports := L.exports.map nm }

theorem Lib.toLibWith_getD (L : Lib) : L.toLibWith (fun i => L.names.getD i "") = L.toLib := rfl

/-- Name `i` of the tree `t` holding a names table of length `n`: `""` when `i ≥ n`. -/
def nameT (n : Nat) (t : VecTree String) (i : Nat) : String :=
  match Nat.blt i n with
  | true => t.getD "" i
  | false => ""

/-- `L.toLib` with names resolved through the tree `t` holding a names table of length `n`. -/
def Lib.toLibT (L : Lib) (n : Nat) (t : VecTree String) : PlacedLib := L.toLibWith (nameT n t)

/-- The names of `t` at indices `i, i + 1, ..., i + n - 1`. -/
def namesFrom (t : VecTree String) : Nat → Nat → List String
  | 0, _ => []
  | n + 1, i => t.getD "" i :: namesFrom t n (i + 1)

theorem length_namesFrom (t : VecTree String) : ∀ n i, (namesFrom t n i).length = n
  | 0, _ => rfl
  | n + 1, i => by simp [namesFrom, length_namesFrom t n (i + 1)]

theorem getD_namesFrom (t : VecTree String) :
    ∀ n i j, j < n → (namesFrom t n i).getD j "" = t.getD "" (i + j)
  | 0, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | n + 1, i, 0, _ => rfl
  | n + 1, i, j + 1, hj => by
    simp only [namesFrom, List.getD_cons_succ]
    rw [getD_namesFrom t n (i + 1) j (by omega), show i + 1 + j = i + (j + 1) by omega]

/-- Names `[i, j)` of `t` match `L.names`. -/
def namesTreeOkChunk (L : Lib) (t : VecTree String) (i j : Nat) : Prop :=
  namesFrom t (j - i) i = rTake (j - i) (rDrop i L.names)

/-- Names `[i, n)` of `t` match `L.names` from index `i` onward. -/
def namesTreeOkTail (L : Lib) (n : Nat) (t : VecTree String) (i : Nat) : Prop :=
  namesFrom t (n - i) i = rDrop i L.names

/-- The name chunks `[i, j₁), [j₁, j₂), ..., [jₖ, n)` of `t` match `L.names`. -/
def NamesTreeOkChunks (L : Lib) (n : Nat) (t : VecTree String) : Nat → List Nat → Prop
  | i, [] => namesTreeOkTail L n t i
  | i, j :: js => namesTreeOkChunk L t i j ∧ NamesTreeOkChunks L n t j js

theorem namesTreeOkChunks_nil {L : Lib} {n : Nat} {t : VecTree String} {i : Nat}
    (h : namesFrom t (n - i) i = rDrop i L.names) : NamesTreeOkChunks L n t i [] := h

theorem namesTreeOkChunks_cons {L : Lib} {n : Nat} {t : VecTree String} {i j : Nat}
    {js : List Nat} (h : namesFrom t (j - i) i = rTake (j - i) (rDrop i L.names))
    (hr : NamesTreeOkChunks L n t j js) : NamesTreeOkChunks L n t i (j :: js) := ⟨h, hr⟩

theorem getD_drop_eq {α : Type} (l : List α) (i j : Nat) (d : α) :
    (l.drop i).getD j d = l.getD (i + j) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem getD_take_eq {α : Type} (l : List α) (k j : Nat) (d : α) (h : j < k) :
    (l.take k).getD j d = l.getD j d := by
  simp [List.getD_eq_getElem?_getD, h]

theorem namesTreeOk_of_chunks_from {L : Lib} {n : Nat} {t : VecTree String} :
    ∀ (i : Nat) (js : List Nat), NamesTreeOkChunks L n t i js →
      ∀ x, i ≤ x → x < n → t.getD "" x = L.names.getD x ""
  | i, [], h, x, hix, hx => by
    have := congrArg (·.getD (x - i) "") (show namesFrom t (n - i) i = rDrop i L.names from h)
    simp only [getD_namesFrom t _ i _ (show x - i < n - i by omega), rDrop_eq, getD_drop_eq,
      show i + (x - i) = x by omega] at this
    exact this
  | i, j :: js, h, x, hix, hx => by
    obtain ⟨h1, h2⟩ := h
    by_cases hxj : x < j
    · have := congrArg (·.getD (x - i) "")
        (show namesFrom t (j - i) i = rTake (j - i) (rDrop i L.names) from h1)
      simp only [getD_namesFrom t _ i _ (show x - i < j - i by omega), rTake_eq, rDrop_eq,
        getD_take_eq _ _ _ _ (show x - i < j - i by omega), getD_drop_eq,
        show i + (x - i) = x by omega] at this
      exact this
    · exact namesTreeOk_of_chunks_from j js h2 x (by omega) hx

theorem nameT_eq {L : Lib} {n : Nat} {t : VecTree String} {js : List Nat}
    (hn : rLen L.names = n) (h : NamesTreeOkChunks L n t 0 js) (i : Nat) :
    nameT n t i = L.names.getD i "" := by
  rw [rLen_eq] at hn
  unfold nameT
  cases hb : Nat.blt i n with
  | true =>
    exact namesTreeOk_of_chunks_from 0 js h i (Nat.zero_le _) (Nat.blt_eq.mp hb)
  | false =>
    have hi : ¬ i < n := fun hlt => by simp [Nat.blt_eq.mpr hlt] at hb
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

/-- `L.toLibT n t = L.toLib` when `n` is the length of the names table and the chunk facts hold. -/
theorem Lib.toLibT_eq {L : Lib} {n : Nat} {t : VecTree String} {js : List Nat}
    (hn : rLen L.names = n) (h : NamesTreeOkChunks L n t 0 js) : L.toLibT n t = L.toLib := by
  rw [Lib.toLibT, show nameT n t = fun i => L.names.getD i "" from funext (nameT_eq hn h),
    Lib.toLibWith_getD]

end Arm64.Obj.Interned

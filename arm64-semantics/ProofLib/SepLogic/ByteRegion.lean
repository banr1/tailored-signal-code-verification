/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.SliceArray
import Arm64.Trusted.Spec.SepLogic

/-!
# Byte-Region Loop Invariants

Functional models of partially filled (`ByteSlice.fillSet`, `fillPrefix`) and partially copied
(`ByteSlice.copySet`, `copyPrefix`, `copySuffix`) byte buffers, together with write-collapse lemmas
and closing tactics (`byte_region_len`, `byte_region_eq`, `byte_region_entails`) for spatial loop
invariants over `base ↦ₛ bs` and `base ↦ᵣ bs`.

## Which lemma for which goal

| Goal shape | Use |
|---|---|
| `off + w ≤ (ByteSlice.write* (fillSet bs b p) ...).length` | `byte_region_len` |
| `ByteSlice.write8 (fillPrefix bs b k) k b = fillPrefix bs b (k + 1)` | `write8_fillPrefix` (or `byte_region_eq`) |
| `ByteSlice.write64 (copyPrefix old src k) k (readLE src k 8) = copyPrefix old src (k + 8)` | `write64_copyPrefix_readLE` |
| `ByteSlice.write16/32 (copyPrefix old src k) k (pack16/32 (src.getD k 0) ...) = copyPrefix old src (k + 2/4)` (16/32-bit loads come out as `pack16` / `pack32`) | `write16_copyPrefix_pack16` / `write32_copyPrefix_pack32` |
| `ByteSlice.write* (fillSet bs b p) off v = fillSet bs b p'` with `p'` adding `[off, off + w)` | `write8_fillSet` / `writeLE_fillSet` / `write16/32/64_fillSet_bcast64` |
| `ByteSlice.write16/32/64 (fillPrefix bs b k) k ((bcast64 b).truncate 16/32 / bcast64 b) = fillPrefix bs b (k + 2/4/8)` (`strh` / `str w` / `str x` of a broadcast) | `write16/32/64_fillPrefix_bcast64` |
| `ByteSlice.write16/32/64 bs off (truncated bcast64 b) = fillSet bs b [off, off + w)` | `write16/32/64_bcast64` |
| `((bcast64 b).truncate w).extractLsb' (8 * j) 8 = b`, `(bcast64 b).truncate 8 = b` | `extractLsb'_bcast64_trunc` / `bcast64_truncate8` (`@[simp]`) |
| `ByteSlice.write* (copySet old src p) off v = copySet old src p'` (`v` = bytes of `src` at `off`) | `write8_copySet` / `writeLE_copySet` / `write16_copySet_pack16` / `write32_copySet_pack32` / `write64_copySet_readLE` |
| any equality of byte lists built from the above, offsets differing by `omega` | `byte_region_eq` |
| `fillPrefix bs b n = List.replicate n b` / `copyPrefix old src n = src` | `fillPrefix_full` / `copyPrefix_full` |
| `P ⊢ Q` where `P`, `Q` differ only in `↦ₛ` / `↦ᵣ` byte lists | `byte_region_entails` |

Typical invariants for `wp_loop_measure frame m Inv P_inv` (with `k` iterations remaining):

- forward byte fill of `n` bytes: `fun k _ => dst ↦ₛ ByteSlice.fillPrefix bs0 b (n - k)`;
- forward 8-byte copy of `8 * n` bytes:
  `fun k _ => (dst ↦ₛ ByteSlice.copyPrefix old src (8 * (n - k))) ∗ (srcPtr ↦ᵣ src)`.

The last iteration produces a goal that `byte_region_eq` closes against the final
`dst ↦ₛ List.replicate n b` or `dst ↦ₛ src`; `fillPrefix_full` and `copyPrefix_full` restate
the invariant at `k = 0` directly.
-/

@[expose] public section

namespace ProofLib

open Arm64

namespace ByteSlice

/-! ## Models -/

/-- `bs` with byte `i` replaced by `b` wherever `p i` holds. -/
def fillSet (bs : List (BitVec 8)) (b : BitVec 8) (p : Nat → Bool) : List (BitVec 8) :=
  bs.mapIdx fun i x => if p i then b else x

/-- `old` with byte `i` replaced by `src.getD i 0#8` wherever `p i` holds. -/
def copySet (old src : List (BitVec 8)) (p : Nat → Bool) : List (BitVec 8) :=
  old.mapIdx fun i x => if p i then src.getD i 0#8 else x

/-- `bs` with bytes `[0, k)` set to `b`. -/
abbrev fillPrefix (bs : List (BitVec 8)) (b : BitVec 8) (k : Nat) : List (BitVec 8) :=
  fillSet bs b fun i => decide (i < k)

/-- `old` with bytes `[0, k)` copied from `src`. -/
abbrev copyPrefix (old src : List (BitVec 8)) (k : Nat) : List (BitVec 8) :=
  copySet old src fun i => decide (i < k)

/-- `old` with bytes `[k, old.length)` copied from `src` (a backward copy that has done the
    top `old.length - k` bytes). -/
abbrev copySuffix (old src : List (BitVec 8)) (k : Nat) : List (BitVec 8) :=
  copySet old src fun i => decide (k ≤ i)

/-- The 64-bit value whose eight little-endian bytes are all `b`. -/
def bcast64 (b : BitVec 8) : BitVec 64 :=
  BitVec.replicate 8 b

/-! ## Lengths and Pointwise Reads -/

@[simp] theorem fillSet_length (bs : List (BitVec 8)) (b : BitVec 8) (p : Nat → Bool) :
    (fillSet bs b p).length = bs.length := by
  simp [fillSet]

@[simp] theorem copySet_length (old src : List (BitVec 8)) (p : Nat → Bool) :
    (copySet old src p).length = old.length := by
  simp [copySet]

theorem getD_fillSet (bs : List (BitVec 8)) (b : BitVec 8) (p : Nat → Bool) (i : Nat)
    (d : BitVec 8) :
    (fillSet bs b p).getD i d = if p i && decide (i < bs.length) then b else bs.getD i d := by
  unfold fillSet
  by_cases hi : i < bs.length
  · simp [List.getD_eq_getElem?_getD, hi]
  · simp [List.getD_eq_getElem?_getD, hi]

theorem getD_copySet (old src : List (BitVec 8)) (p : Nat → Bool) (i : Nat) (d : BitVec 8) :
    (copySet old src p).getD i d =
      if p i && decide (i < old.length) then src.getD i 0#8 else old.getD i d := by
  unfold copySet
  by_cases hi : i < old.length
  · simp [List.getD_eq_getElem?_getD, hi]
  · simp [List.getD_eq_getElem?_getD, hi]

theorem getD_replicate' (n : Nat) (b : BitVec 8) (i : Nat) (d : BitVec 8) :
    (List.replicate n b).getD i d = if i < n then b else d := by
  by_cases hi : i < n
  · simp [List.getD_eq_getElem?_getD, hi]
  · simp [List.getD_eq_getElem?_getD, hi]

/-- Two byte lists of equal length are equal when they agree at every in-range index. -/
theorem ext_getD {xs ys : List (BitVec 8)} (hlen : xs.length = ys.length)
    (h : ∀ i, i < xs.length → xs.getD i 0#8 = ys.getD i 0#8) : xs = ys := by
  apply List.ext_getElem hlen
  intro i h1 h2
  have := h i h1
  simpa [List.getD_eq_getElem?_getD, h1, h2] using this

theorem getD_write (buf src : List (BitVec 8)) (off i : Nat) (d : BitVec 8)
    (h : off ≤ buf.length) :
    (write buf off src).getD i d =
      if off ≤ i ∧ i < off + src.length then src.getD (i - off) d else buf.getD i d := by
  unfold write
  have hmin : min off buf.length = off := by omega
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append, List.getElem?_take,
    List.getElem?_drop, List.length_append, List.length_take, hmin]
  by_cases h1 : i < off
  · simp [h1, show i < off + src.length by omega, show ¬(off ≤ i) by omega]
  · by_cases h2 : i < off + src.length
    · simp [h1, h2, show off ≤ i by omega]
    · simp only [h2, ↓reduceIte, and_false]
      congr 2
      omega

theorem getD_write8 (bs : List (BitVec 8)) (off : Nat) (v : BitVec 8) (i : Nat) (d : BitVec 8)
    (h : off ≤ bs.length) :
    (write8 bs off v).getD i d = if i = off then v else bs.getD i d := by
  unfold write8
  rw [getD_write bs [v] off i d h]
  by_cases hi : i = off
  · subst hi; simp
  · have : ¬(off ≤ i ∧ i < off + [v].length) := by simp only [List.length_singleton]; omega
    simp only [hi, this, ↓reduceIte]

theorem getD_writeLE {w : Nat} (n : Nat) (bs : List (BitVec 8)) (off : Nat) (v : BitVec w)
    (i : Nat) (d : BitVec 8) (h : off ≤ bs.length) :
    (writeLE n bs off v).getD i d =
      if off ≤ i ∧ i < off + n then v.extractLsb' (8 * (i - off)) 8 else bs.getD i d := by
  unfold writeLE
  rw [getD_write bs _ off i d h, unpackLE_length]
  split
  · rw [getD_unpackLE n v (i - off) d (by omega)]
  · rfl

theorem getD_write16 (bs : List (BitVec 8)) (off : Nat) (v : BitVec 16) (i : Nat)
    (d : BitVec 8) (h : off ≤ bs.length) :
    (write16 bs off v).getD i d =
      if off ≤ i ∧ i < off + 2 then v.extractLsb' (8 * (i - off)) 8 else bs.getD i d :=
  getD_writeLE 2 bs off v i d h

theorem getD_write32 (bs : List (BitVec 8)) (off : Nat) (v : BitVec 32) (i : Nat)
    (d : BitVec 8) (h : off ≤ bs.length) :
    (write32 bs off v).getD i d =
      if off ≤ i ∧ i < off + 4 then v.extractLsb' (8 * (i - off)) 8 else bs.getD i d :=
  getD_writeLE 4 bs off v i d h

theorem getD_write64 (bs : List (BitVec 8)) (off : Nat) (v : BitVec 64) (i : Nat)
    (d : BitVec 8) (h : off ≤ bs.length) :
    (write64 bs off v).getD i d =
      if off ≤ i ∧ i < off + 8 then v.extractLsb' (8 * (i - off)) 8 else bs.getD i d :=
  getD_writeLE 8 bs off v i d h

/-- Byte `j` of an `n`-byte little-endian read (`n ≤ 8`). -/
theorem extractLsb'_readLE (bs : List (BitVec 8)) (off n j : Nat) (hn : n ≤ 8 := by omega) :
    (readLE bs off n).extractLsb' (8 * j) 8 = if j < n then bs.getD (off + j) 0#8 else 0#8 := by
  ext k hk
  rw [BitVec.getElem_extractLsb']
  by_cases hj : j < n
  · have hbit : 8 * j + k < 64 := by omega
    rw [BitVec.getLsbD_eq_getElem hbit, getElem_readLE bs off n (8 * j + k) hbit]
    simp only [show 8 * j + k < 8 * n by omega, ↓reduceIte, hj,
      show (8 * j + k) / 8 = j by omega, show (8 * j + k) % 8 = k by omega]
  · simp only [hj, ↓reduceIte, BitVec.getElem_zero]
    by_cases hbit : 8 * j + k < 64
    · rw [BitVec.getLsbD_eq_getElem hbit, getElem_readLE bs off n (8 * j + k) hbit]
      simp [show ¬(8 * j + k < 8 * n) by omega]
    · exact BitVec.getLsbD_of_ge _ _ (by omega)

/-- Byte `j` of the byte broadcast `bcast64 b`. -/
theorem extractLsb'_bcast64 (b : BitVec 8) (j : Nat) :
    (bcast64 b).extractLsb' (8 * j) 8 = if j < 8 then b else 0#8 := by
  ext k hk
  rw [BitVec.getElem_extractLsb']
  unfold bcast64
  split
  · rw [BitVec.getLsbD_replicate (n := 8) (w := 8) (x := b)]
    simp [show 8 * j + k < 8 * 8 by omega, show (8 * j + k) % 8 = k by omega,
      BitVec.getLsbD_eq_getElem hk]
  · simp only [BitVec.getElem_zero]
    exact BitVec.getLsbD_of_ge _ _ (by omega)

/-- Byte `j` of the halfword `pack16 b0 b1` (the value of a 16-bit load from a byte list). -/
theorem extractLsb'_pack16 (b0 b1 : BitVec 8) (j : Nat) :
    (pack16 b0 b1).extractLsb' (8 * j) 8 = if j = 0 then b0 else if j = 1 then b1 else 0#8 := by
  ext k hk
  rw [BitVec.getElem_extractLsb']
  unfold pack16
  rcases j with _ | _ | j
  · simp only [BitVec.getLsbD_append]; simp [hk, BitVec.getLsbD_eq_getElem]
  · simp only [BitVec.getLsbD_append]; simp [hk, BitVec.getLsbD_eq_getElem]
  · simp only [show j + 1 + 1 ≠ 0 by omega, show j + 1 + 1 ≠ 1 by omega, ↓reduceIte,
      BitVec.getElem_zero]
    exact BitVec.getLsbD_of_ge _ _ (by omega)

/-- Byte `j` of the word `pack32 b0 b1 b2 b3` (the value of a 32-bit load from a byte list). -/
theorem extractLsb'_pack32 (b0 b1 b2 b3 : BitVec 8) (j : Nat) :
    (pack32 b0 b1 b2 b3).extractLsb' (8 * j) 8 =
      if j = 0 then b0 else if j = 1 then b1 else if j = 2 then b2 else if j = 3 then b3
      else 0#8 := by
  ext k hk
  rw [BitVec.getElem_extractLsb']
  unfold pack32
  simp only [BitVec.getLsbD_append]
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ 4 ≤ j := by omega
  rcases hj with rfl | rfl | rfl | rfl | hj
  all_goals
    repeat' split
    all_goals first
      | omega
      | (rw [← BitVec.getLsbD_eq_getElem hk]; congr 1; omega)
      | (rw [BitVec.getElem_zero]; exact BitVec.getLsbD_of_ge _ _ (by omega))

/-- Byte `j` of a byte broadcast truncated to `w` bits, for a byte below `w`. -/
theorem extractLsb'_bcast64_trunc (b : BitVec 8) (w j : Nat) (hj : 8 * j + 8 ≤ w)
    (hw : w ≤ 64) : ((bcast64 b).setWidth w).extractLsb' (8 * j) 8 = b := by
  have h1 : ((bcast64 b).setWidth w).extractLsb' (8 * j) 8 = (bcast64 b).extractLsb' (8 * j) 8 := by
    ext k hk
    simp [BitVec.getElem_extractLsb', show 8 * j + k < w by omega]
  rw [h1, extractLsb'_bcast64]
  simp [show j < 8 by omega]

/-- Byte `j` of the low 16 bits of a byte broadcast (the value of `strh` of a broadcast). -/
theorem extractLsb'_bcast64_trunc16 (b : BitVec 8) (j : Nat) :
    ((bcast64 b).setWidth 16).extractLsb' (8 * j) 8 = if j < 2 then b else 0#8 := by
  split
  · exact extractLsb'_bcast64_trunc b 16 j (by omega) (by omega)
  · ext k hk
    simp [BitVec.getElem_extractLsb', show ¬(8 * j + k < 16) by omega]

/-- Byte `j` of the low 32 bits of a byte broadcast (the value of `str w` of a broadcast). -/
theorem extractLsb'_bcast64_trunc32 (b : BitVec 8) (j : Nat) :
    ((bcast64 b).setWidth 32).extractLsb' (8 * j) 8 = if j < 4 then b else 0#8 := by
  split
  · exact extractLsb'_bcast64_trunc b 32 j (by omega) (by omega)
  · ext k hk
    simp [BitVec.getElem_extractLsb', show ¬(8 * j + k < 32) by omega]

/-- The low byte of a byte broadcast (the value of `strb` of a broadcast). -/
@[simp] theorem bcast64_truncate8 (b : BitVec 8) : (bcast64 b).setWidth 8 = b := by
  simpa using extractLsb'_bcast64_trunc b 8 0 (by omega) (by omega)

/-! ## Closing Tactics -/

/-- Close `off + w ≤ L.length` (or any `omega` goal mentioning lengths) where `L` is built from
    `fillSet` / `copySet` / `write*` / `List.replicate`, using the length facts in context. -/
syntax "byte_region_len" : tactic
macro_rules
  | `(tactic| byte_region_len) =>
    `(tactic| first
      | omega
      | (simp (disch := byte_region_len) only [ProofLib.ByteSlice.fillSet_length,
          ProofLib.ByteSlice.copySet_length, ProofLib.ByteSlice.write8_length,
          ProofLib.ByteSlice.write16_length, ProofLib.ByteSlice.write32_length,
          ProofLib.ByteSlice.write64_length, ProofLib.ByteSlice.writeLE_length,
          ProofLib.ByteSlice.write_length, List.length_replicate, ProofLib.ByteSlice.unpackLE_length,
          List.length_cons, List.length_nil] <;> omega))

/-- Close an equality of byte lists built from `fillSet` / `copySet` (and their prefix / suffix
    abbreviations), `write*`, `List.replicate` and `readLE`, by extensionality on `getD` and
    `omega` over the offsets (length facts and offset bounds must be in context). -/
syntax "byte_region_eq" : tactic
macro_rules
  | `(tactic| byte_region_eq) =>
    `(tactic| first
      | with_reducible rfl
      | (apply ProofLib.ByteSlice.ext_getD
         · byte_region_len
         · intro i hi
           try simp (disch := byte_region_len) only [ProofLib.ByteSlice.fillSet_length,
             ProofLib.ByteSlice.copySet_length, ProofLib.ByteSlice.write8_length,
             ProofLib.ByteSlice.write16_length, ProofLib.ByteSlice.write32_length,
             ProofLib.ByteSlice.write64_length, ProofLib.ByteSlice.writeLE_length,
             List.length_replicate] at hi
           simp (disch := byte_region_len) only [ProofLib.ByteSlice.getD_fillSet,
             ProofLib.ByteSlice.getD_copySet, ProofLib.ByteSlice.getD_write8,
             ProofLib.ByteSlice.getD_write16, ProofLib.ByteSlice.getD_write32,
             ProofLib.ByteSlice.getD_write64, ProofLib.ByteSlice.getD_writeLE,
             ProofLib.ByteSlice.getD_replicate', ProofLib.ByteSlice.extractLsb'_readLE,
             ProofLib.ByteSlice.extractLsb'_bcast64, ProofLib.ByteSlice.extractLsb'_pack16,
             ProofLib.ByteSlice.extractLsb'_pack32,
             ProofLib.ByteSlice.extractLsb'_bcast64_trunc16,
             ProofLib.ByteSlice.extractLsb'_bcast64_trunc32, ProofLib.ByteSlice.bcast64_truncate8,
             BitVec.extractLsb'_zero, BitVec.setWidth_setWidth_of_le,
             ProofLib.ByteSlice.fillSet_length, ProofLib.ByteSlice.copySet_length,
             ProofLib.ByteSlice.write8_length, ProofLib.ByteSlice.write64_length,
             List.length_replicate,
             Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
             decide_eq_false_iff_not]
           repeat' split
           all_goals first
             | rfl
             | omega
             | (congr 1; omega)
             | (simp_all; done)
             | (simp_all <;> omega)))

end ByteSlice

/-! ## Write-Collapse Lemmas -/

namespace ByteSlice

theorem write8_fillSet (bs : List (BitVec 8)) (b : BitVec 8) (p : Nat → Bool) (off : Nat)
    (h : off + 1 ≤ bs.length) :
    write8 (fillSet bs b p) off b = fillSet bs b (fun i => p i || decide (i = off)) := by
  byte_region_eq

theorem writeLE_fillSet {w : Nat} (n : Nat) (bs : List (BitVec 8)) (b : BitVec 8)
    (p : Nat → Bool) (off : Nat) (v : BitVec w) (h : off + n ≤ bs.length)
    (hv : ∀ j, j < n → v.extractLsb' (8 * j) 8 = b) :
    writeLE n (fillSet bs b p) off v =
      fillSet bs b (fun i => p i || (decide (off ≤ i) && decide (i < off + n))) := by
  have hlen : (writeLE n (fillSet bs b p) off v).length = bs.length := by
    rw [writeLE_length n _ off v (by simp only [fillSet_length]; omega), fillSet_length]
  apply ext_getD (by rw [hlen, fillSet_length])
  intro i hi
  rw [hlen] at hi
  rw [getD_writeLE n _ off v i _ (by simp only [fillSet_length]; omega), getD_fillSet,
    getD_fillSet]
  by_cases hin : off ≤ i ∧ i < off + n
  · simp only [hin]
    rw [hv (i - off) (by omega)]
    simp [hi]
  · have hw : (decide (off ≤ i) && decide (i < off + n)) = false := by simp; omega
    simp only [hin, ↓reduceIte, hw, Bool.or_false]

theorem write64_fillSet_bcast64 (bs : List (BitVec 8)) (b : BitVec 8) (p : Nat → Bool)
    (off : Nat) (h : off + 8 ≤ bs.length) :
    write64 (fillSet bs b p) off (bcast64 b) =
      fillSet bs b (fun i => p i || (decide (off ≤ i) && decide (i < off + 8))) :=
  writeLE_fillSet 8 bs b p off (bcast64 b) h fun j hj => by
    simp only [extractLsb'_bcast64, hj, ↓reduceIte]

/-- A broadcast store into a plain byte list starts a `fillSet` over the stored interval. -/
theorem write64_bcast64 (bs : List (BitVec 8)) (b : BitVec 8) (off : Nat)
    (h : off + 8 ≤ bs.length) :
    write64 bs off (bcast64 b) =
      fillSet bs b (fun i => decide (off ≤ i) && decide (i < off + 8)) := by
  byte_region_eq

theorem write32_bcast64 (bs : List (BitVec 8)) (b : BitVec 8) (off : Nat)
    (h : off + 4 ≤ bs.length) :
    write32 bs off ((bcast64 b).setWidth 32) =
      fillSet bs b (fun i => decide (off ≤ i) && decide (i < off + 4)) := by
  byte_region_eq

theorem write16_bcast64 (bs : List (BitVec 8)) (b : BitVec 8) (off : Nat)
    (h : off + 2 ≤ bs.length) :
    write16 bs off ((bcast64 b).setWidth 16) =
      fillSet bs b (fun i => decide (off ≤ i) && decide (i < off + 2)) := by
  byte_region_eq

theorem write8_copySet (old src : List (BitVec 8)) (p : Nat → Bool) (off : Nat)
    (h : off + 1 ≤ old.length) :
    write8 (copySet old src p) off (src.getD off 0#8) =
      copySet old src (fun i => p i || decide (i = off)) := by
  byte_region_eq

theorem writeLE_copySet {w : Nat} (n : Nat) (old src : List (BitVec 8)) (p : Nat → Bool)
    (off : Nat) (v : BitVec w) (h : off + n ≤ old.length)
    (hv : ∀ j, j < n → v.extractLsb' (8 * j) 8 = src.getD (off + j) 0#8) :
    writeLE n (copySet old src p) off v =
      copySet old src (fun i => p i || (decide (off ≤ i) && decide (i < off + n))) := by
  have hlen : (writeLE n (copySet old src p) off v).length = old.length := by
    rw [writeLE_length n _ off v (by simp only [copySet_length]; omega), copySet_length]
  apply ext_getD (by rw [hlen, copySet_length])
  intro i hi
  rw [hlen] at hi
  rw [getD_writeLE n _ off v i _ (by simp only [copySet_length]; omega), getD_copySet,
    getD_copySet]
  by_cases hin : off ≤ i ∧ i < off + n
  · simp only [hin]
    rw [hv (i - off) (by omega), show off + (i - off) = i by omega]
    simp [hi]
  · have hw : (decide (off ≤ i) && decide (i < off + n)) = false := by simp; omega
    simp only [hin, ↓reduceIte, hw, Bool.or_false]

theorem write64_copySet_readLE (old src : List (BitVec 8)) (p : Nat → Bool) (off : Nat)
    (h : off + 8 ≤ old.length) :
    write64 (copySet old src p) off (readLE src off 8) =
      copySet old src (fun i => p i || (decide (off ≤ i) && decide (i < off + 8))) :=
  writeLE_copySet 8 old src p off (readLE src off 8) h fun j hj => by
    simp only [extractLsb'_readLE src off 8 j, hj, ↓reduceIte]

theorem write16_copySet_pack16 (old src : List (BitVec 8)) (p : Nat → Bool) (off : Nat)
    (h : off + 2 ≤ old.length) :
    write16 (copySet old src p) off (pack16 (src.getD off 0#8) (src.getD (off + 1) 0#8)) =
      copySet old src (fun i => p i || (decide (off ≤ i) && decide (i < off + 2))) :=
  writeLE_copySet 2 old src p off _ h fun j hj => by
    rw [extractLsb'_pack16]
    rcases j with _ | _ | j <;> simp_all <;> omega

theorem write32_copySet_pack32 (old src : List (BitVec 8)) (p : Nat → Bool) (off : Nat)
    (h : off + 4 ≤ old.length) :
    write32 (copySet old src p) off (pack32 (src.getD off 0#8) (src.getD (off + 1) 0#8)
      (src.getD (off + 2) 0#8) (src.getD (off + 3) 0#8)) =
      copySet old src (fun i => p i || (decide (off ≤ i) && decide (i < off + 4))) :=
  writeLE_copySet 4 old src p off _ h fun j hj => by
    rw [extractLsb'_pack32]
    rcases j with _ | _ | _ | _ | j <;> simp_all <;> omega

theorem write8_fillPrefix (bs : List (BitVec 8)) (b : BitVec 8) (k : Nat)
    (h : k + 1 ≤ bs.length) :
    write8 (fillPrefix bs b k) k b = fillPrefix bs b (k + 1) := by
  byte_region_eq

@[simp] theorem fillSet_fillSet (bs : List (BitVec 8)) (b : BitVec 8) (p q : Nat → Bool) :
    fillSet (fillSet bs b p) b q = fillSet bs b (fun i => p i || q i) := by
  byte_region_eq

@[simp] theorem fillSet_fillPrefix_range (bs : List (BitVec 8)) (b : BitVec 8) (k n : Nat) :
    fillSet (fillPrefix bs b k) b (fun i => decide (k ≤ i) && decide (i < k + n)) =
      fillPrefix bs b (k + n) := by
  byte_region_eq

theorem write64_zero (bs : List (BitVec 8)) (off : Nat) (h : off + 8 ≤ bs.length) :
    write64 bs off 0#64 =
      fillSet bs 0#8 (fun i => decide (off ≤ i) && decide (i < off + 8)) := by
  byte_region_eq

theorem write64_fillSet_range_zero (bs : List (BitVec 8)) (lo hi : Nat)
    (hlo : lo ≤ hi) (hhi : hi + 8 ≤ bs.length) :
    write64 (fillSet bs 0#8 (fun i => decide (lo ≤ i) && decide (i < hi))) hi 0#64 =
      fillSet bs 0#8 (fun i => decide (lo ≤ i) && decide (i < hi + 8)) := by
  byte_region_eq

/-- Eight adjacent 64-bit zero writes at `off, off + 8, ..., off + 56` collapse into a single
    64-byte `fillSet` with `0#8` over `[off, off + 64)`. -/
theorem write64_zero_8_eq_fillSet (bs : List (BitVec 8)) (off : Nat)
    (h : off + 64 ≤ bs.length) :
    write64 (write64 (write64 (write64 (write64 (write64 (write64 (write64 bs
      off 0#64)
      (off + 8) 0#64)
      (off + 16) 0#64)
      (off + 24) 0#64)
      (off + 32) 0#64)
      (off + 40) 0#64)
      (off + 48) 0#64)
      (off + 56) 0#64 =
      fillSet bs 0#8 (fun i => decide (off ≤ i) && decide (i < off + 64)) := by
  rw [write64_zero bs off (by omega),
      write64_fillSet_range_zero bs off (off + 8) (by omega) (by omega),
      show off + 8 + 8 = off + 16 by omega,
      write64_fillSet_range_zero bs off (off + 16) (by omega) (by omega),
      show off + 16 + 8 = off + 24 by omega,
      write64_fillSet_range_zero bs off (off + 24) (by omega) (by omega),
      show off + 24 + 8 = off + 32 by omega,
      write64_fillSet_range_zero bs off (off + 32) (by omega) (by omega),
      show off + 32 + 8 = off + 40 by omega,
      write64_fillSet_range_zero bs off (off + 40) (by omega) (by omega),
      show off + 40 + 8 = off + 48 by omega,
      write64_fillSet_range_zero bs off (off + 48) (by omega) (by omega),
      show off + 48 + 8 = off + 56 by omega,
      write64_fillSet_range_zero bs off (off + 56) (by omega) (by omega),
      show off + 56 + 8 = off + 64 by omega]

theorem write8_copyPrefix (old src : List (BitVec 8)) (k : Nat) (h : k + 1 ≤ old.length) :
    write8 (copyPrefix old src k) k (src.getD k 0#8) = copyPrefix old src (k + 1) := by
  byte_region_eq

theorem write64_copyPrefix_readLE (old src : List (BitVec 8)) (k : Nat)
    (h : k + 8 ≤ old.length) :
    write64 (copyPrefix old src k) k (readLE src k 8) = copyPrefix old src (k + 8) := by
  byte_region_eq

theorem write16_copyPrefix_pack16 (old src : List (BitVec 8)) (k : Nat)
    (h : k + 2 ≤ old.length) :
    write16 (copyPrefix old src k) k (pack16 (src.getD k 0#8) (src.getD (k + 1) 0#8)) =
      copyPrefix old src (k + 2) := by
  byte_region_eq

theorem write32_copyPrefix_pack32 (old src : List (BitVec 8)) (k : Nat)
    (h : k + 4 ≤ old.length) :
    write32 (copyPrefix old src k) k (pack32 (src.getD k 0#8) (src.getD (k + 1) 0#8)
      (src.getD (k + 2) 0#8) (src.getD (k + 3) 0#8)) = copyPrefix old src (k + 4) := by
  byte_region_eq

/-! ## End-of-Loop Lemmas, Identities, and Congruence -/

theorem fillSet_congr {bs : List (BitVec 8)} {b : BitVec 8} {p q : Nat → Bool}
    (h : ∀ i, i < bs.length → p i = q i) : fillSet bs b p = fillSet bs b q := by
  apply ext_getD (by simp)
  intro i hi
  simp only [fillSet_length] at hi
  rw [getD_fillSet, getD_fillSet, h i hi]

theorem copySet_congr {old src : List (BitVec 8)} {p q : Nat → Bool}
    (h : ∀ i, i < old.length → p i = q i) : copySet old src p = copySet old src q := by
  apply ext_getD (by simp)
  intro i hi
  simp only [copySet_length] at hi
  rw [getD_copySet, getD_copySet, h i hi]

theorem fillSet_all {bs : List (BitVec 8)} {b : BitVec 8} {p : Nat → Bool} {n : Nat}
    (hlen : bs.length = n) (h : ∀ i, i < n → p i = true) :
    fillSet bs b p = List.replicate n b := by
  apply ext_getD (by simp [hlen])
  intro i hi
  simp only [fillSet_length] at hi
  rw [getD_fillSet, getD_replicate', h i (by omega)]
  simp [hi, show i < n by omega]

theorem copySet_all {old src : List (BitVec 8)} {p : Nat → Bool}
    (hlen : old.length = src.length) (h : ∀ i, i < old.length → p i = true) :
    copySet old src p = src := by
  apply ext_getD (by simp [hlen])
  intro i hi
  simp only [copySet_length] at hi
  rw [getD_copySet, h i hi]
  simp [hi]

theorem fillSet_false (bs : List (BitVec 8)) (b : BitVec 8) :
    fillSet bs b (fun _ => false) = bs := by
  apply ext_getD (by simp)
  intro i _
  rw [getD_fillSet]
  simp

theorem copySet_false (old src : List (BitVec 8)) :
    copySet old src (fun _ => false) = old := by
  apply ext_getD (by simp)
  intro i _
  rw [getD_copySet]
  simp

@[simp] theorem fillPrefix_zero (bs : List (BitVec 8)) (b : BitVec 8) :
    fillPrefix bs b 0 = bs :=
  (fillSet_congr fun _ _ => by simp).trans (fillSet_false bs b)

@[simp] theorem copyPrefix_zero (old src : List (BitVec 8)) : copyPrefix old src 0 = old :=
  (copySet_congr fun _ _ => by simp).trans (copySet_false old src)

theorem copySuffix_len {old src : List (BitVec 8)} {n : Nat} (hlen : old.length = n) :
    copySuffix old src n = old :=
  (copySet_congr fun i hi => by simp; omega).trans (copySet_false old src)

theorem fillPrefix_full {bs : List (BitVec 8)} {b : BitVec 8} {n : Nat} (hlen : bs.length = n) :
    fillPrefix bs b n = List.replicate n b :=
  fillSet_all hlen fun i hi => by simpa using hi

theorem copyPrefix_full {old src : List (BitVec 8)} {n : Nat} (hlen : old.length = n)
    (hsrc : src.length = n) : copyPrefix old src n = src :=
  copySet_all (by omega) fun i hi => by simp; omega

theorem copySuffix_zero {old src : List (BitVec 8)} (hlen : old.length = src.length) :
    copySuffix old src 0 = src :=
  copySet_all hlen fun _ _ => by simp

/-! ## Additional `readLE`, `write8`, and `copySet` Helpers -/

theorem write8_chain8 (bs : List (BitVec 8)) (h : bs.length = 8)
    (x0 x1 x2 x3 x4 x5 x6 x7 : BitVec 8) :
    write8 (write8 (write8 (write8 (write8
      (write8 (write8 (write8 bs 0 x0) 1 x1) 2 x2) 3 x3) 4 x4)
      5 x5) 6 x6) 7 x7 = [x0, x1, x2, x3, x4, x5, x6, x7] := by
  rcases bs with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try (simp at h; done)
  rfl

theorem readLE_congr (bs bs' : List (BitVec 8)) (off n : Nat)
    (h : ∀ i, i < n → bs.getD (off + i) 0#8 = bs'.getD (off + i) 0#8) :
    readLE bs off n = readLE bs' off n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [readLE_succ, readLE_succ, ih (fun i hi => h i (by omega)),
      h n (by omega)]

/-- A byte write outside `[off, off + n)` does not change a little-endian read there. -/
theorem readLE_write8_of_disjoint (bs : List (BitVec 8)) (off n i : Nat) (x : BitVec 8)
    (hi : i < off ∨ off + n ≤ i) (hlen : i ≤ bs.length) :
    readLE (write8 bs i x) off n = readLE bs off n := by
  apply readLE_congr
  intro j hj
  rw [getD_write8 bs i x _ _ hlen]
  have : ¬ (off + j = i) := by omega
  simp only [this, ↓reduceIte]

theorem readLE_write64_self (bs : List (BitVec 8)) (off : Nat) (v : BitVec 64)
    (h : off ≤ bs.length) :
    readLE (write64 bs off v) off 8 = v := by
  ext i hi
  rw [getElem_readLE _ off 8 i hi]
  simp only [show i < 8 * 8 by omega, ↓reduceIte,
    getD_write64 bs off v (off + i / 8) 0#8 h,
    show off ≤ off + i / 8 ∧ off + i / 8 < off + 8 by omega, and_self,
    Nat.add_sub_cancel_left]
  rw [BitVec.getElem_extractLsb' (by omega), BitVec.getLsbD_eq_getElem (by omega)]
  congr 1
  omega

theorem readLE8_lowByte (bs : List (BitVec 8)) :
    (readLE bs 0 8).extractLsb' 0 8 = bs.getD 0 0#8 := by
  have := extractLsb'_readLE bs 0 8 0
  simpa using this

theorem write8_append_cons (xs ys : List (BitVec 8)) (y v : BitVec 8) :
    write8 (xs ++ y :: ys) xs.length v = xs ++ v :: ys := by
  simp [write8, write, List.drop_append]

theorem write8_append_cons' (xs ys : List (BitVec 8)) (y v : BitVec 8) (n : Nat)
    (h : n = xs.length) :
    write8 (xs ++ y :: ys) n v = xs ++ v :: ys := by
  subst h; exact write8_append_cons xs ys y v

abbrev write8_mid := @write8_append_cons

theorem copySet_empty_range (L S : List (BitVec 8)) (i : Nat) :
    copySet L S (fun idx => decide (i ≤ idx ∧ idx < i + 0)) = L := by
  rw [copySet_congr (q := fun _ => false) (fun idx _ => by simp)]
  exact copySet_false L S

theorem copySet_shift_getD (L : List (BitVec 8)) (i j : Nat) :
    (copySet L (L.drop 1) (fun idx => decide (i ≤ idx ∧ idx < i + j))).getD
      (i + j + 1) 0#8 = (L.drop 1).getD (i + j) 0#8 := by
  rw [getD_copySet, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]
  have : decide (i ≤ i + j + 1 ∧ i + j + 1 < i + j) = false := by simp
  simp [this]

theorem write8_shift (L : List (BitVec 8)) (i j : Nat) (h : i + j + 1 ≤ L.length) :
    write8 (copySet L (L.drop 1) (fun idx => decide (i ≤ idx ∧ idx < i + j)))
      (i + j) ((copySet L (L.drop 1) (fun idx => decide (i ≤ idx ∧ idx < i + j))).getD
        (i + j + 1) 0#8) =
      copySet L (L.drop 1) (fun idx => decide (i ≤ idx ∧ idx < i + (j + 1))) := by
  rw [copySet_shift_getD, write8_copySet _ _ _ _ h]
  apply copySet_congr
  intro idx _
  by_cases h1 : idx = i + j
  · subst h1; simp
  · by_cases h2 : i ≤ idx ∧ idx < i + j
    · have h3 : i ≤ idx ∧ idx < i + (j + 1) := by omega
      simp [h2, h3]
    · have h3 : ¬(i ≤ idx ∧ idx < i + (j + 1)) := by omega
      simp only [h1, h2, h3, decide_false, Bool.or_false]

end ByteSlice

export ByteSlice (
  write8_chain8 readLE_congr readLE_write8_of_disjoint readLE_write64_self readLE8_lowByte
  write8_append_cons write8_append_cons' write8_mid copySet_empty_range copySet_shift_getD
  write8_shift
)

/-- An 8-byte slice is an aligned 64-bit cell holding its little-endian value. -/
theorem pointsToBytes8_eq_cell (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 8) :
    (a ↦ₛ bs) = (a ↦₆₄ ByteSlice.readLE bs 0 8) := by
  have := pointsToBytes_slice_eq_pointsTo64 a bs 0 (by omega)
  rwa [ByteSlice.slice, List.drop_zero, List.take_of_length_le (by omega)] at this

/-! ## Spatial Bridges and `byte_region_entails` -/

theorem pointsToBytes_congr_bytes {a : BitVec 64} {bs1 bs2 : List (BitVec 8)} (h : bs1 = bs2) :
    (a ↦ₛ bs1) = (a ↦ₛ bs2) := h ▸ rfl

theorem pointsToBytesRO_congr_bytes {a : BitVec 64} {bs1 bs2 : List (BitVec 8)}
    (h : bs1 = bs2) : (a ↦ᵣ bs1) = (a ↦ᵣ bs2) := h ▸ rfl

theorem ByteSlice.sepConj_congr_eq {P1 P2 Q1 Q2 : SepProp} (hP : P1 = P2) (hQ : Q1 = Q2) :
    (P1 ∗ Q1) = (P2 ∗ Q2) := hP ▸ hQ ▸ rfl

theorem ByteSlice.entails_of_eq {P Q : SepProp} (h : P = Q) : P ⊢ Q := h ▸ Entails.refl P

/-- Close `P ⊢ Q` where `P` and `Q` have the same `∗` structure (after reassociation) and differ
    only in the byte lists of `↦ₛ` / `↦ᵣ` atoms, which `byte_region_eq` proves equal. -/
macro "byte_region_entails" : tactic =>
  `(tactic| (
    try simp only [ProofLib.sepConj_assoc, ProofLib.emp_sepConj, ProofLib.sepConj_emp]
    apply ProofLib.ByteSlice.entails_of_eq
    repeat' (first
      | with_reducible rfl
      | apply ProofLib.ByteSlice.sepConj_congr_eq
      | apply ProofLib.pointsToBytes_congr_bytes
      | apply ProofLib.pointsToBytesRO_congr_bytes)
    all_goals byte_region_eq))

end ProofLib

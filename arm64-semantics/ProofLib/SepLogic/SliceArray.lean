/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.Bytes
public import ProofLib.SepLogic.ByteSliceAttr
import Arm64.Trusted.Spec.SepLogic

/-!
# Byte-Slice Windows, Little-Endian Accumulation, and Fixed-Stride Arrays

Defines `ByteSlice` windowing and functional updates (`slice`, `write`, `[byteslice]`,
`byteslice_simp`), little-endian accumulation and unpacking (`readLE`, `unpackLE`, `writeLE`),
function-indexed separating ranges (`sepRange`), and fixed-stride typed element arrays
(`pointsToArray`) indexed via `List.getD`.
-/

@[expose] public section

namespace ProofLib

open Arm64

/-- Simplify `ByteSlice` window, write, and little-endian unpacking expressions. -/
macro "byteslice_simp" : tactic =>
  `(tactic| simp (disch := first | exact BitVec.isLt _ | decide | omega) only [byteslice])

/-! ## Sub-Slice Windows and Functional Byte Writes -/

namespace ByteSlice

/-- Extract the contiguous `n`-byte window `[off, off + n)` from `buf`. -/
def slice (buf : List (BitVec 8)) (off n : Nat) : List (BitVec 8) :=
  (buf.drop off).take n

/-- Overwrite `[off, off + src.length)` in `buf` with `src`, leaving surrounding bytes intact. -/
def write (buf : List (BitVec 8)) (off : Nat) (src : List (BitVec 8)) : List (BitVec 8) :=
  buf.take off ++ src ++ buf.drop (off + src.length)

@[simp, byteslice]
theorem slice_zero (buf : List (BitVec 8)) (off : Nat) :
    slice buf off 0 = [] := by
  simp [slice]

@[simp, byteslice]
theorem slice_nil (off n : Nat) :
    slice [] off n = [] := by
  simp [slice]


@[simp, byteslice]
theorem slice_length (buf : List (BitVec 8)) (off n : Nat) (h : off + n ≤ buf.length) :
    (slice buf off n).length = n := by
  simp only [slice, List.length_take, List.length_drop]
  omega

@[byteslice]
theorem slice_slice (buf : List (BitVec 8)) (off m k n : Nat) (h : k + n ≤ m) :
    slice (slice buf off m) k n = slice buf (off + k) n := by
  unfold slice
  rw [List.drop_take, List.take_take, List.drop_drop, Nat.min_eq_left (by omega)]

@[byteslice]
theorem slice_append_slice (buf : List (BitVec 8)) (off m n : Nat) :
    slice buf off m ++ slice buf (off + m) n = slice buf off (m + n) := by
  unfold slice
  rw [List.take_add, List.drop_drop]

@[simp, byteslice]
theorem write_nil (buf : List (BitVec 8)) (off : Nat) :
    write buf off [] = buf := by
  simp [write]

@[simp, byteslice]
theorem write_length (buf src : List (BitVec 8)) (off : Nat)
    (h : off + src.length ≤ buf.length) :
    (write buf off src).length = buf.length :=
  List.splice_length buf src off h

@[simp, byteslice]
theorem write_slice_self (buf : List (BitVec 8)) (off n : Nat)
    (h : off + n ≤ buf.length) :
    write buf off (slice buf off n) = buf := by
  unfold write
  rw [slice_length buf off n h]
  exact List.splice_drop_take_eq buf off n

@[simp, byteslice]
theorem slice_write_self (buf src : List (BitVec 8)) (off : Nat)
    (h : off + src.length ≤ buf.length) :
    slice (write buf off src) off src.length = src := by
  unfold slice write
  have htake : (buf.take off).length = off := by simp [List.length_take]; omega
  rw [List.append_assoc,
      List.drop_append_of_le_length (Nat.le_of_eq htake.symm),
      List.drop_eq_nil_of_le (List.length_take_le off buf),
      List.nil_append,
      List.take_append_of_le_length (Nat.le_refl _), List.take_length]

@[byteslice]
theorem slice_write_disjoint (buf src : List (BitVec 8)) (off k n : Nat)
    (hb : off + src.length ≤ buf.length)
    (hdisj : off + src.length ≤ k ∨ k + n ≤ off) :
    slice (write buf off src) k n = slice buf k n := by
  unfold slice write
  rcases hdisj with hle | hge
  · have hlen1 : (buf.take off ++ src).length = off + src.length := by
      simp [List.length_take]; omega
    rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append, hlen1,
        List.drop_drop, show off + src.length + (k - (off + src.length)) = k by omega]
  · rw [List.append_assoc, List.drop_append, List.take_append]
    have hlen_take : (buf.take off).length = off := by simp [List.length_take]; omega
    have hlen_drop : ((buf.take off).drop k).length = off - k := by
      simp [List.length_drop, hlen_take]
    have hsub : n - (off - k) = 0 := by omega
    rw [hlen_drop, hsub, List.take_zero, List.append_nil, List.drop_take, List.take_take,
        Nat.min_eq_left (by omega)]

@[byteslice]
theorem slice_write_inside (buf src : List (BitVec 8)) (off k n : Nat)
    (h1 : off ≤ k) (h2 : k + n ≤ off + src.length) (hb : off + src.length ≤ buf.length) :
    slice (write buf off src) k n = slice src (k - off) n := by
  unfold slice write
  have htake : (buf.take off).length = off := by simp [List.length_take]; omega
  rw [List.append_assoc, List.drop_append, htake,
      List.drop_eq_nil_of_le (by simp [List.length_take]; omega), List.nil_append,
      List.drop_append, List.take_append_of_le_length (by simp [List.length_drop]; omega)]

@[byteslice]
theorem getD_slice (buf : List (BitVec 8)) (off n i : Nat) (d : BitVec 8) (h : i < n) :
    (slice buf off n).getD i d = buf.getD (off + i) d := by
  unfold slice
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_take_of_lt h, List.getElem?_drop]

@[byteslice]
theorem set_eq_write (buf : List (BitVec 8)) (i : Nat) (v : BitVec 8) (h : i < buf.length) :
    buf.set i v = write buf i [v] := by
  rw [List.set_eq_take_cons_drop buf i v h]
  simp [write]

@[byteslice]
theorem listMove_eq_write (buf : List (BitVec 8)) (dst src len : Nat)
    (h : src + len ≤ buf.length) :
    ProofLib.listMove buf dst src len = write buf dst (slice buf src len) := by
  unfold ProofLib.listMove write
  rw [slice_length buf src len h]
  rfl

end ByteSlice

/-- Partition a byte slice `base ↦ₛ bs` at offset `k ≤ bs.length` into prefix
    `base ↦ₛ bs.take k` and suffix `(base + BitVec.ofNat 64 k) ↦ₛ bs.drop k`. -/
theorem pointsToBytes_partition (base : BitVec 64) (bs : List (BitVec 8)) (k : Nat)
    (hk : k ≤ bs.length) :
    (base ↦ₛ bs) = ((base ↦ₛ bs.take k) ∗ ((base + BitVec.ofNat 64 k) ↦ₛ bs.drop k)) :=
  pointsToBytes_take_drop base k bs hk

/-- Focus a contiguous `n`-byte window `[off, off + n)` in window-first order matching
    `pointsToBytes_split3` and `wp_sep_access`:
    `((base + off) ↦ₛ ByteSlice.slice buf off n) ∗ ((base ↦ₛ buf.take off) ∗ ((base + (off + n)) ↦ₛ buf.drop (off + n)))`. -/
theorem pointsToBytes_focus (base : BitVec 64) (buf : List (BitVec 8)) (off n : Nat)
    (h : off + n ≤ buf.length) :
    (base ↦ₛ buf) =
      ((base + BitVec.ofNat 64 off) ↦ₛ ByteSlice.slice buf off n) ∗
      ((base ↦ₛ buf.take off) ∗
       ((base + BitVec.ofNat 64 (off + n)) ↦ₛ buf.drop (off + n))) :=
  pointsToBytes_split3 base buf off n h


/-- Reassemble a window-first split byte slice after replacing its active window at `base + off` with `src`. -/
theorem pointsToBytes_write (base : BitVec 64) (buf src : List (BitVec 8)) (off : Nat)
    (h : off + src.length ≤ buf.length) :
    (((base + BitVec.ofNat 64 off) ↦ₛ src) ∗
      ((base ↦ₛ buf.take off) ∗
       ((base + BitVec.ofNat 64 (off + src.length)) ↦ₛ buf.drop (off + src.length)))) =
    (base ↦ₛ ByteSlice.write buf off src) := by
  unfold ByteSlice.write
  rw [← sepConj_assoc, sepConj_comm ((base + BitVec.ofNat 64 off) ↦ₛ src) (base ↦ₛ buf.take off)]
  rw [pointsToBytes_append, pointsToBytes_append]
  have htl : (buf.take off).length = off := by simp [List.length_take]; omega
  have htl2 : (buf.take off ++ src).length = off + src.length := by
    simp [List.length_append, htl]
  rw [htl, htl2]

/-- Variant of `pointsToBytes_write` when the suffix address uses an explicit length `n`
    with `hn : src.length = n`. -/
theorem pointsToBytes_write_len (base : BitVec 64) (buf src : List (BitVec 8))
    (off n : Nat) (hn : src.length = n) (h : off + n ≤ buf.length) :
    (((base + BitVec.ofNat 64 off) ↦ₛ src) ∗
      ((base ↦ₛ buf.take off) ∗
       ((base + BitVec.ofNat 64 (off + n)) ↦ₛ buf.drop (off + n)))) =
    (base ↦ₛ ByteSlice.write buf off src) := by
  subst hn
  exact pointsToBytes_write base buf src off h

/-! ## Little-Endian Accumulation and Typed Word Updates -/

namespace ByteSlice

/-- Little-endian value of `bs[off .. off + n)` zero-extended into 64 bits (LSB-first accumulation). -/
def readLE (bs : List (BitVec 8)) (off : Nat) : Nat → BitVec 64
  | 0 => 0#64
  | n + 1 => readLE bs off n ||| (((bs.getD (off + n) 0#8).zeroExtend 64) <<< (8 * n))

@[simp]
theorem readLE_zero (bs : List (BitVec 8)) (off : Nat) :
    readLE bs off 0 = 0#64 := rfl

theorem readLE_succ (bs : List (BitVec 8)) (off n : Nat) :
    readLE bs off (n + 1) =
      readLE bs off n ||| (((bs.getD (off + n) 0#8).zeroExtend 64) <<< (8 * n)) := rfl

private theorem shiftLeft_or_shiftLeft_64 (a b : BitVec 64) (m n : Nat) :
    (a ||| (b <<< m)) <<< n = (a <<< n) ||| (b <<< (m + n)) := by
  ext i hi
  simp only [BitVec.getElem_shiftLeft, BitVec.getElem_or]
  by_cases h1 : i < n
  · simp [h1, show i < m + n by omega]
  · by_cases h2 : i - n < m
    · simp [h1, h2, show i < m + n by omega]
    · simp [h1, h2, show ¬(i < m + n) by omega, show i - n - m = i - (m + n) by omega]

/-- Single compositional tail lemma splitting any `(k + j)`-byte little-endian read into
    a `k`-byte prefix and a shifted `j`-byte suffix:
    `readLE bs off (k + j) = readLE bs off k ||| (readLE bs (off + k) j <<< (8 * k))`. -/
theorem readLE_add (bs : List (BitVec 8)) (off k : Nat) :
    ∀ (j : Nat), readLE bs off (k + j) =
      readLE bs off k ||| (readLE bs (off + k) j <<< (8 * k))
  | 0 => by simp [readLE]
  | j + 1 => by
    rw [Nat.add_succ, readLE_succ, readLE_add bs off k j, readLE_succ, shiftLeft_or_shiftLeft_64,
        show 8 * j + 8 * k = 8 * (k + j) by omega,
        show off + k + j = off + (k + j) by omega,
        ← BitVec.or_assoc]

theorem readLE_one (bs : List (BitVec 8)) (off : Nat) :
    readLE bs off 1 = (bs.getD off 0#8).zeroExtend 64 := by
  simp [readLE]

theorem readLE_two (bs : List (BitVec 8)) (off : Nat) :
    readLE bs off 2 =
      (pack16 (bs.getD off 0#8) (bs.getD (off + 1) 0#8)).zeroExtend 64 := by
  rw [show (2 : Nat) = 1 + 1 from rfl, readLE_succ, readLE_one, ← pack16_zeroExtend64]

theorem readLE_four (bs : List (BitVec 8)) (off : Nat) :
    readLE bs off 4 =
      (pack32 (bs.getD off 0#8) (bs.getD (off + 1) 0#8)
        (bs.getD (off + 2) 0#8) (bs.getD (off + 3) 0#8)).zeroExtend 64 := by
  rw [show (4 : Nat) = 3 + 1 from rfl, readLE_succ,
      show (3 : Nat) = 2 + 1 from rfl, readLE_succ,
      readLE_two, pack16_zeroExtend64, ← pack32_zeroExtend64]

private theorem append32_32_eq_or (hi lo : BitVec 32) :
    hi ++ lo = lo.zeroExtend 64 ||| ((hi.zeroExtend 64) <<< 32) := by
  bv_bits

private theorem pack64_eq_append_pack32 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    pack64 b0 b1 b2 b3 b4 b5 b6 b7 =
      (pack32 b4 b5 b6 b7) ++ (pack32 b0 b1 b2 b3) := by
  simp only [pack64, pack32]
  bv_bits

theorem pack64_eq_readLE_8 (bs : List (BitVec 8)) (off : Nat) :
    pack64 (bs.getD off 0#8) (bs.getD (off + 1) 0#8)
      (bs.getD (off + 2) 0#8) (bs.getD (off + 3) 0#8)
      (bs.getD (off + 4) 0#8) (bs.getD (off + 5) 0#8)
      (bs.getD (off + 6) 0#8) (bs.getD (off + 7) 0#8) =
      readLE bs off 8 := by
  rw [pack64_eq_append_pack32, append32_32_eq_or,
      show readLE bs off 8 = readLE bs off (4 + 4) from rfl,
      readLE_add bs off 4 4,
      readLE_four bs off, readLE_four bs (off + 4),
      show (off + 4) + 1 = off + 5 by omega,
      show (off + 4) + 2 = off + 6 by omega,
      show (off + 4) + 3 = off + 7 by omega]

theorem getElem_readLE (bs : List (BitVec 8)) (off n i : Nat) (hi : i < 64) :
    (readLE bs off n)[i] =
      if i < 8 * n then (bs.getD (off + i / 8) 0#8)[i % 8]'(Nat.mod_lt _ (by omega))
      else false := by
  induction n with
  | zero => simp [readLE]
  | succ k ih =>
    simp only [readLE, BitVec.getElem_or, BitVec.getElem_shiftLeft,
      BitVec.zeroExtend_eq_setWidth, BitVec.getElem_setWidth, ih]
    by_cases h1 : i < 8 * k
    · have h2 : i < 8 * (k + 1) := by omega
      simp [h1, h2]
    · by_cases h2 : i < 8 * (k + 1)
      · have hdiv : i / 8 = k := by omega
        have hsub : i - 8 * k = i % 8 := by omega
        have hmod : i % 8 < 8 := Nat.mod_lt _ (by omega)
        simp only [h1, h2, ↓reduceIte, hdiv, hsub, Bool.false_or]
        exact BitVec.getLsbD_eq_getElem hmod
      · have hge8 : 8 ≤ i - 8 * k := by omega
        simp only [h1, h2, ↓reduceIte, Bool.false_or]
        exact BitVec.getLsbD_of_ge _ _ hge8

private theorem setWidth_setWidth_self {w : Nat} (x : BitVec w) (hw : w ≤ 64 := by decide) :
    (x.setWidth 64).setWidth w = x := by
  ext i hi
  simp [BitVec.getElem_setWidth, BitVec.getLsbD_eq_getElem (Nat.lt_of_lt_of_le hi hw),
    BitVec.getLsbD_eq_getElem hi]

@[simp, byteslice]
theorem setWidth8_readLE_one (bs : List (BitVec 8)) (off : Nat) :
    (readLE bs off 1).setWidth 8 = bs.getD off 0#8 := by
  rw [readLE_one, BitVec.zeroExtend_eq_setWidth, setWidth_setWidth_self]

@[simp, byteslice]
theorem zeroExtend_setWidth_readLE (bs : List (BitVec 8)) (off n : Nat) :
    ((readLE bs off n).setWidth (8 * n)).zeroExtend 64 = readLE bs off n := by
  ext i hi
  simp only [BitVec.zeroExtend_eq_setWidth, BitVec.getElem_setWidth]
  by_cases h : i < 8 * n
  · simp [h, BitVec.getLsbD_eq_getElem hi]
  · simp [h, getElem_readLE bs off n i hi]

/-- `n` little-endian bytes of `v` (`= Arm64.Obj.bytesLE n v` at width 64). -/
def unpackLE {w : Nat} (n : Nat) (v : BitVec w) : List (BitVec 8) :=
  (List.range n).map fun i => v.extractLsb' (8 * i) 8


@[simp, byteslice]
theorem unpackLE_length {w : Nat} (n : Nat) (v : BitVec w) :
    (unpackLE n v).length = n := by
  simp [unpackLE]

theorem getD_unpackLE {w : Nat} (n : Nat) (v : BitVec w) (i : Nat) (d : BitVec 8)
    (hi : i < n) :
    (unpackLE n v).getD i d = v.extractLsb' (8 * i) 8 := by
  unfold unpackLE
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hi),
      List.getElem_map, List.getElem_range, Option.getD_some]


/-- Round-trip: reading `n` little-endian bytes unpacked from `v` recovers `v.setWidth 64`
    whenever `v.toNat < 2 ^ (8 * n)`. -/
theorem readLE_unpackLE {w : Nat} (n : Nat) (v : BitVec w)
    (hv : v.toNat < 2 ^ (8 * n) := by first | exact v.isLt | omega) :
    readLE (unpackLE n v) 0 n = v.setWidth 64 := by
  ext i hi
  rw [getElem_readLE (unpackLE n v) 0 n i hi]
  by_cases h : i < 8 * n
  · simp only [h, ↓reduceIte, ← BitVec.getLsbD_eq_getElem]
    rw [Nat.zero_add, getD_unpackLE n v (i / 8) 0#8 (by omega),
        BitVec.getLsbD_eq_getElem (Nat.mod_lt _ (by omega)), BitVec.getElem_extractLsb',
        BitVec.getLsbD_eq_getElem hi, BitVec.getElem_setWidth]
    congr 1; omega
  · simp only [h, ↓reduceIte, BitVec.getElem_setWidth]
    symm
    exact Nat.testBit_lt_two_pow
      (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) (by omega)))

@[simp, byteslice]
theorem readLE_unpackLE_64 (n : Nat) (v : BitVec 64)
    (hv : v.toNat < 2 ^ (8 * n) := by first | exact v.isLt | omega) :
    readLE (unpackLE n v) 0 n = v := by
  rw [readLE_unpackLE n v hv, BitVec.setWidth_eq]

@[simp, byteslice]
theorem setWidth_readLE_unpackLE {w : Nat} (n : Nat) (v : BitVec w)
    (hw : w ≤ 8 * n := by omega) (hw64 : w ≤ 64 := by omega) :
    (readLE (unpackLE n v) 0 n).setWidth w = v := by
  have hv : v.toNat < 2 ^ (8 * n) :=
    Nat.lt_of_lt_of_le v.isLt (Nat.pow_le_pow_right (by decide) hw)
  rw [readLE_unpackLE n v hv, setWidth_setWidth_self v hw64]

@[simp, byteslice]
theorem unpackLE_readLE (bs : List (BitVec 8)) (off n : Nat)
    (h : off + n ≤ bs.length) (hn : n ≤ 8 := by omega) :
    unpackLE n (readLE bs off n) = slice bs off n := by
  apply List.ext_getElem (by rw [unpackLE_length, slice_length bs off n h])
  intro j h1 h2
  have hj : j < n := by simpa using h1
  have hget : (slice bs off n)[j] = bs.getD (off + j) 0#8 := by
    rw [← getD_slice bs off n j 0#8 hj, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem h2, Option.getD_some]
  rw [hget]
  ext k hk
  simp only [unpackLE, List.getElem_map, List.getElem_range, BitVec.getElem_extractLsb']
  have hbit : 8 * j + k < 64 := by omega
  have hlt8n : 8 * j + k < 8 * n := by omega
  rw [BitVec.getLsbD_eq_getElem hbit, getElem_readLE bs off n (8 * j + k) hbit]
  simp only [hlt8n, ↓reduceIte]
  have hdiv : (8 * j + k) / 8 = j := by omega
  have hmod : (8 * j + k) % 8 = k := by omega
  simp [hdiv, hmod]

/-- Overwrite `[off, off + n)` in `bs` with the `n`-byte little-endian encoding of `v`. -/
def writeLE {w : Nat} (n : Nat) (bs : List (BitVec 8)) (off : Nat) (v : BitVec w) :
    List (BitVec 8) :=
  write bs off (unpackLE n v)

@[simp, byteslice]
theorem writeLE_length {w : Nat} (n : Nat) (bs : List (BitVec 8)) (off : Nat) (v : BitVec w)
    (h : off + n ≤ bs.length) :
    (writeLE n bs off v).length = bs.length := by
  unfold writeLE
  exact write_length bs (unpackLE n v) off (by simpa using h)

def write8 (bs : List (BitVec 8)) (off : Nat) (v : BitVec 8) : List (BitVec 8) :=
  write bs off [v]

def write16 : List (BitVec 8) → Nat → BitVec 16 → List (BitVec 8) :=
  writeLE 2

def write32 : List (BitVec 8) → Nat → BitVec 32 → List (BitVec 8) :=
  writeLE 4

def write64 : List (BitVec 8) → Nat → BitVec 64 → List (BitVec 8) :=
  writeLE 8

theorem write32_eq_writeLE : write32 = writeLE (w := 32) 4 := rfl

theorem write64_eq_writeLE : write64 = writeLE (w := 64) 8 := rfl

@[simp, byteslice]
theorem write8_length (bs : List (BitVec 8)) (off : Nat) (v : BitVec 8)
    (h : off + 1 ≤ bs.length) :
    (write8 bs off v).length = bs.length :=
  write_length bs [v] off h

@[simp, byteslice]
theorem write16_length (bs : List (BitVec 8)) (off : Nat) (v : BitVec 16)
    (h : off + 2 ≤ bs.length) :
    (write16 bs off v).length = bs.length :=
  writeLE_length 2 bs off v h

@[simp, byteslice]
theorem write32_length (bs : List (BitVec 8)) (off : Nat) (v : BitVec 32)
    (h : off + 4 ≤ bs.length) :
    (write32 bs off v).length = bs.length :=
  writeLE_length 4 bs off v h

@[simp, byteslice]
theorem write64_length (bs : List (BitVec 8)) (off : Nat) (v : BitVec 64)
    (h : off + 8 ≤ bs.length) :
    (write64 bs off v).length = bs.length :=
  writeLE_length 8 bs off v h

end ByteSlice

/-- Reassemble `(base ↦ₛ bs)` after updating the focused byte at `base + off` (companion to
    `pointsToBytes_focus8`). -/
theorem pointsToBytes_update8 (base : BitVec 64) (bs : List (BitVec 8)) (off : Nat)
    (v : BitVec 8) (h : off + 1 ≤ bs.length) :
    (((base + BitVec.ofNat 64 off) ↦₈ v) ∗
      ((base ↦ₛ bs.take off) ∗
       ((base + BitVec.ofNat 64 (off + 1)) ↦ₛ bs.drop (off + 1)))) =
    (base ↦ₛ ByteSlice.write8 bs off v) := by
  unfold ByteSlice.write8
  rw [← pointsToBytes_singleton _ v]
  exact pointsToBytes_write_len base bs [v] off 1 rfl h

/-- Reassemble `(base ↦ₛ bs)` after updating the focused 16-bit halfword at `base + off`
    (companion to `pointsToBytes_focus16`). -/
theorem pointsToBytes_update16 (base : BitVec 64) (bs : List (BitVec 8)) (off : Nat)
    (v : BitVec 16) (h : off + 2 ≤ bs.length) :
    (((base + BitVec.ofNat 64 off) ↦₁₆ v) ∗
      ((base ↦ₛ bs.take off) ∗
       ((base + BitVec.ofNat 64 (off + 2)) ↦ₛ bs.drop (off + 2)))) =
    (base ↦ₛ ByteSlice.write16 bs off v) := by
  unfold ByteSlice.write16
  have hp16 : ((base + BitVec.ofNat 64 off) ↦₁₆ v) =
      ((base + BitVec.ofNat 64 off) ↦ₛ [BitVec.extractLsb' 0 8 v, BitVec.extractLsb' 8 8 v]) := by
    rw [pointsTo16_split8]
    simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
  rw [hp16]
  exact pointsToBytes_write_len base bs [BitVec.extractLsb' 0 8 v, BitVec.extractLsb' 8 8 v] off 2 rfl h

/-- Reassemble `(base ↦ₛ bs)` after updating the focused 32-bit word at `base + off`
    (companion to `pointsToBytes_focus32`). -/
theorem pointsToBytes_update32 (base : BitVec 64) (bs : List (BitVec 8)) (off : Nat)
    (v : BitVec 32) (h : off + 4 ≤ bs.length) :
    (((base + BitVec.ofNat 64 off) ↦₃₂ v) ∗
      ((base ↦ₛ bs.take off) ∗
       ((base + BitVec.ofNat 64 (off + 4)) ↦ₛ bs.drop (off + 4)))) =
    (base ↦ₛ ByteSlice.write32 bs off v) := by
  unfold ByteSlice.write32
  rw [pointsTo32_eq_pointsToBytes]
  exact pointsToBytes_write_len base bs (unpack32 v) off 4 rfl h

/-- Reassemble `(base ↦ₛ bs)` after updating the focused 64-bit word at `base + off`
    (companion to `pointsToBytes_focus64`). -/
theorem pointsToBytes_update64 (base : BitVec 64) (bs : List (BitVec 8)) (off : Nat)
    (v : BitVec 64) (h : off + 8 ≤ bs.length) :
    (((base + BitVec.ofNat 64 off) ↦₆₄ v) ∗
      ((base ↦ₛ bs.take off) ∗
       ((base + BitVec.ofNat 64 (off + 8)) ↦ₛ bs.drop (off + 8)))) =
    (base ↦ₛ ByteSlice.write64 bs off v) := by
  unfold ByteSlice.write64
  rw [pointsTo64_eq_pointsToBytes]
  exact pointsToBytes_write_len base bs (unpack64 v) off 8 rfl h

theorem pointsToBytes_slice_eq_pointsTo8 (a : BitVec 64) (bs : List (BitVec 8)) (off : Nat)
    (h : off + 1 ≤ bs.length) :
    (a ↦ₛ ByteSlice.slice bs off 1) = (a ↦₈ (ByteSlice.readLE bs off 1).setWidth 8) := by
  rw [ByteSlice.slice, pointsToBytes_take1_eq_pointsTo8 a bs off h, ByteSlice.readLE_one,
      BitVec.zeroExtend_eq_setWidth, ByteSlice.setWidth_setWidth_self]

theorem pointsToBytes_slice_eq_pointsTo16 (a : BitVec 64) (bs : List (BitVec 8)) (off : Nat)
    (h : off + 2 ≤ bs.length) :
    (a ↦ₛ ByteSlice.slice bs off 2) = (a ↦₁₆ (ByteSlice.readLE bs off 2).setWidth 16) := by
  rw [ByteSlice.slice, pointsToBytes_take2_eq_pointsTo16 a bs off h, ByteSlice.readLE_two,
      BitVec.zeroExtend_eq_setWidth, ByteSlice.setWidth_setWidth_self]

theorem pointsToBytes_slice_eq_pointsTo32 (a : BitVec 64) (bs : List (BitVec 8)) (off : Nat)
    (h : off + 4 ≤ bs.length) :
    (a ↦ₛ ByteSlice.slice bs off 4) = (a ↦₃₂ (ByteSlice.readLE bs off 4).setWidth 32) := by
  rw [ByteSlice.slice, pointsToBytes_take4_eq_pointsTo32 a bs off h, ByteSlice.readLE_four,
      BitVec.zeroExtend_eq_setWidth, ByteSlice.setWidth_setWidth_self]

theorem pointsToBytes_slice_eq_pointsTo64 (a : BitVec 64) (bs : List (BitVec 8)) (off : Nat)
    (h : off + 8 ≤ bs.length) :
    (a ↦ₛ ByteSlice.slice bs off 8) = (a ↦₆₄ ByteSlice.readLE bs off 8) := by
  rw [ByteSlice.slice, pointsToBytes_take8_eq_pointsTo64 a bs off h, ByteSlice.pack64_eq_readLE_8]

/-- Focus an 8-byte little-endian word from `(base ↦ₛ bs)` as `ByteSlice.readLE bs off 8`. -/
theorem pointsToBytes_focus64_le (base : BitVec 64) (bs : List (BitVec 8)) (off : Nat)
    (h : off + 8 ≤ bs.length) :
    (base ↦ₛ bs) =
      ((base + BitVec.ofNat 64 off) ↦₆₄ ByteSlice.readLE bs off 8) ∗
      ((base ↦ₛ bs.take off) ∗
       ((base + BitVec.ofNat 64 (off + 8)) ↦ₛ bs.drop (off + 8))) := by
  rw [pointsToBytes_focus base bs off 8 h, pointsToBytes_slice_eq_pointsTo64 _ _ _ h]

/-- Read `n` little-endian bytes starting at `addr` into a zero-extended 64-bit value. -/
def _root_.Arm64.Memory.readLE (m : Memory) (addr : BitVec 64) : Nat → BitVec 64
  | 0 => 0#64
  | n + 1 => m.readLE addr n ||| (((m.read8 (addr + BitVec.ofNat 64 n)).zeroExtend 64) <<< (8 * n))

theorem _root_.Arm64.Memory.readLE_of_readBytes (m : Memory) (a : BitVec 64)
    (bs : List (BitVec 8)) (n : Nat) (h : m.readBytes a n = bs) :
    m.readLE a n = ByteSlice.readLE bs 0 n := by
  subst h
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [Memory.readLE, ByteSlice.readLE, ih, Nat.zero_add]
    have hpre : ByteSlice.readLE (m.readBytes a k) 0 k =
        ByteSlice.readLE (m.readBytes a (k + 1)) 0 k := by
      rw [Memory.readBytes_add m a k 1]
      ext i hi
      simp only [ByteSlice.getElem_readLE _ _ k i hi]
      by_cases hlt : i < 8 * k
      · simp only [hlt, ↓reduceIte, ← BitVec.getLsbD_eq_getElem]
        rw [Nat.zero_add, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_append_left (by rw [Memory.readBytes_length]; omega)]
      · simp [hlt]
    have hk : m.read8 (a + BitVec.ofNat 64 k) = (m.readBytes a (k + 1)).getD k 0#8 :=
      Memory.read8_of_readBytes m a (m.readBytes a (k + 1)) (by rw [Memory.readBytes_length]) k
        (by rw [Memory.readBytes_length]; omega)
    rw [hpre, hk]

/-! ## Function-Indexed Separating Ranges -/

/-- Separating conjunction of `f i` for `i` ranging over `[lo, lo + n)`. -/
def sepRange (lo n : Nat) (f : Nat → SepProp) : SepProp :=
  match n with
  | 0 => emp
  | k + 1 => f lo ∗ sepRange (lo + 1) k f

@[simp]
theorem sepRange_zero (lo : Nat) (f : Nat → SepProp) :
    sepRange lo 0 f = emp := rfl

theorem sepRange_succ (lo n : Nat) (f : Nat → SepProp) :
    sepRange lo (n + 1) f = f lo ∗ sepRange (lo + 1) n f := rfl

theorem sepRange_add (lo m n : Nat) (f : Nat → SepProp) :
    sepRange lo (m + n) f = (sepRange lo m f ∗ sepRange (lo + m) n f) := by
  induction m generalizing lo with
  | zero => simp only [Nat.zero_add, sepRange_zero, emp_sepConj, Nat.add_zero]
  | succ m ih =>
    simp only [Nat.succ_add, sepRange_succ, ih (lo + 1), sepConj_assoc, Nat.add_succ]

theorem sepRange_snoc (lo n : Nat) (f : Nat → SepProp) :
    sepRange lo (n + 1) f = (sepRange lo n f ∗ f (lo + n)) := by
  rw [sepRange_add lo n 1 f, sepRange_succ (lo + n) 0 f, sepRange_zero, sepConj_emp]


theorem sepRange_focus (lo n i : Nat) (f : Nat → SepProp) (hi : i < n) :
    sepRange lo n f = (f (lo + i) ∗ (sepRange lo i f ∗ sepRange (lo + i + 1) (n - i - 1) f)) := by
  have hn : i + ((n - i - 1) + 1) = n := by omega
  have h1 := sepRange_add lo i ((n - i - 1) + 1) f
  rw [hn] at h1
  rw [h1, sepRange_succ, ← sepConj_assoc, sepConj_comm (sepRange lo i f) (f (lo + i)), sepConj_assoc]

theorem sepRange_congr {lo n : Nat} {f g : Nat → SepProp}
    (h : ∀ i, lo ≤ i → i < lo + n → f i = g i) :
    sepRange lo n f = sepRange lo n g := by
  induction n generalizing lo with
  | zero => rfl
  | succ n ih =>
    simp only [sepRange_succ]
    rw [h lo (Nat.le_refl lo) (by omega), ih fun i hlo hhi => h i (by omega) (by omega)]

theorem sepRange_update (lo n i : Nat) (f : Nat → SepProp) (P : SepProp) (hi : i < n) :
    (P ∗ (sepRange lo i f ∗ sepRange (lo + i + 1) (n - i - 1) f)) =
      sepRange lo n (fun j => if j = lo + i then P else f j) := by
  rw [sepRange_focus lo n i (fun j => if j = lo + i then P else f j) hi]
  simp only [↓reduceIte]
  have hpre : sepRange lo i (fun j => if j = lo + i then P else f j) = sepRange lo i f :=
    sepRange_congr fun j _ hj => by simp [show j ≠ lo + i by omega]
  have hsuf :
      sepRange (lo + i + 1) (n - i - 1) (fun j => if j = lo + i then P else f j) =
        sepRange (lo + i + 1) (n - i - 1) f :=
    sepRange_congr fun j hj _ => by simp [show j ≠ lo + i by omega]
  rw [hpre, hsuf]

theorem sepRange_shift (lo k n : Nat) (f : Nat → SepProp) :
    sepRange (lo + k) n f = sepRange lo n (fun i => f (i + k)) := by
  induction n generalizing lo with
  | zero => rfl
  | succ n ih =>
    simp only [sepRange_succ, show lo + k + 1 = (lo + 1) + k by omega, ih (lo + 1)]

/-! ## Fixed-Stride Typed Element Arrays -/

/-- Contiguous array of elements starting at `ptr` separated by fixed byte offset `stride`. -/
def pointsToArray {α : Type _} (stride : Nat) (elemAt : BitVec 64 → α → SepProp)
    (ptr : BitVec 64) : List α → SepProp
  | [] => emp
  | x :: xs => elemAt ptr x ∗ pointsToArray stride elemAt (ptr + BitVec.ofNat 64 stride) xs

@[simp]
theorem pointsToArray_nil {α : Type _} (stride : Nat) (elemAt : BitVec 64 → α → SepProp)
    (ptr : BitVec 64) :
    pointsToArray stride elemAt ptr [] = emp := rfl

@[simp]
theorem pointsToArray_cons {α : Type _} (stride : Nat) (elemAt : BitVec 64 → α → SepProp)
    (ptr : BitVec 64) (x : α) (xs : List α) :
    pointsToArray stride elemAt ptr (x :: xs) =
      elemAt ptr x ∗ pointsToArray stride elemAt (ptr + BitVec.ofNat 64 stride) xs := rfl

theorem pointsToArray_append {α : Type _} (stride : Nat) (elemAt : BitVec 64 → α → SepProp) :
    ∀ (xs ys : List α) (ptr : BitVec 64),
      pointsToArray stride elemAt ptr (xs ++ ys) =
        pointsToArray stride elemAt ptr xs ∗
          pointsToArray stride elemAt (ptr + BitVec.ofNat 64 (stride * xs.length)) ys
  | [], ys, ptr => by
    simp only [List.nil_append, pointsToArray_nil, emp_sepConj, List.length_nil, Nat.mul_zero,
      BitVec.add_zero]
  | x :: xs, ys, ptr => by
    simp only [List.cons_append, pointsToArray_cons, pointsToArray_append stride elemAt xs ys,
      sepConj_assoc, List.length_cons]
    have hmul : ptr + BitVec.ofNat 64 stride + BitVec.ofNat 64 (stride * xs.length) =
        ptr + BitVec.ofNat 64 (stride * (xs.length + 1)) := by
      have hdist : stride + stride * xs.length = stride * (xs.length + 1) := by
        rw [Nat.mul_succ, Nat.add_comm]
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, hdist]
    rw [hmul]

theorem pointsToArray_split_at {α : Type _} (stride : Nat) (elemAt : BitVec 64 → α → SepProp)
    (ptr : BitVec 64) (xs : List α) (i : Nat) (hi : i ≤ xs.length) :
    pointsToArray stride elemAt ptr xs =
      pointsToArray stride elemAt ptr (xs.take i) ∗
        pointsToArray stride elemAt (ptr + BitVec.ofNat 64 (stride * i)) (xs.drop i) := by
  have h1 := pointsToArray_append stride elemAt (xs.take i) (xs.drop i) ptr
  rw [List.take_append_drop i xs, List.length_take_of_le hi] at h1
  exact h1

/-- Focus element `i` of a fixed-stride array using proof-free `List.getD xs i default`. -/
theorem pointsToArray_focus {α : Type _} [Inhabited α] (stride : Nat)
    (elemAt : BitVec 64 → α → SepProp)
    (ptr : BitVec 64) (xs : List α) (i : Nat) (hi : i < xs.length) :
    pointsToArray stride elemAt ptr xs =
      elemAt (ptr + BitVec.ofNat 64 (stride * i)) (xs.getD i default) ∗
        (pointsToArray stride elemAt ptr (xs.take i) ∗
         pointsToArray stride elemAt (ptr + BitVec.ofNat 64 (stride * (i + 1))) (xs.drop (i + 1))) := by
  rw [pointsToArray_split_at stride elemAt ptr xs i (Nat.le_of_lt hi)]
  have hdrop : xs.drop i = xs.getD i default :: xs.drop (i + 1) :=
    List.drop_eq_getD_cons xs i default hi
  rw [hdrop, pointsToArray_cons]
  have hadd : ptr + BitVec.ofNat 64 (stride * i) + BitVec.ofNat 64 stride =
      ptr + BitVec.ofNat 64 (stride * (i + 1)) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_succ]
  rw [hadd, ← sepConj_assoc,
      sepConj_comm (pointsToArray stride elemAt ptr (xs.take i)) (elemAt _ _),
      sepConj_assoc]

/-- Reassemble a fixed-stride array after updating element `i` with `x'`. -/
theorem pointsToArray_update {α : Type _} [Inhabited α] (stride : Nat)
    (elemAt : BitVec 64 → α → SepProp)
    (ptr : BitVec 64) (xs : List α) (i : Nat) (x' : α) (hi : i < xs.length) :
    (elemAt (ptr + BitVec.ofNat 64 (stride * i)) x' ∗
      (pointsToArray stride elemAt ptr (xs.take i) ∗
       pointsToArray stride elemAt (ptr + BitVec.ofNat 64 (stride * (i + 1))) (xs.drop (i + 1)))) =
    pointsToArray stride elemAt ptr (xs.set i x') := by
  have hi' : i < (xs.set i x').length := by simpa using hi
  rw [pointsToArray_focus stride elemAt ptr (xs.set i x') i hi']
  have hget : (xs.set i x').getD i default = x' := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_set_self hi]
  have hdrop : (xs.set i x').drop (i + 1) = xs.drop (i + 1) :=
    List.drop_set_of_lt (by omega)
  simp only [hget, List.take_set_of_le (Nat.le_refl i), hdrop]


/-- Hardware shift-indexed element update (`stride = 2 ^ shift`, matching `ptr + (idx <<< shift)`). -/
theorem pointsToArray_update_shift {α : Type _} [Inhabited α] (shift : Nat)
    (elemAt : BitVec 64 → α → SepProp)
    (ptr : BitVec 64) (xs : List α) (idx : BitVec 64) (x' : α)
    (hi : idx.toNat < xs.length)
    (hshift : (2 ^ shift) * idx.toNat < 2 ^ 64 := by first | decide | omega) :
    (elemAt (ptr + (idx <<< shift)) x' ∗
      (pointsToArray (2 ^ shift) elemAt ptr (xs.take idx.toNat) ∗
       pointsToArray (2 ^ shift) elemAt
         (ptr + BitVec.ofNat 64 ((2 ^ shift) * (idx.toNat + 1)))
         (xs.drop (idx.toNat + 1)))) =
    pointsToArray (2 ^ shift) elemAt ptr (xs.set idx.toNat x') := by
  have hm : idx.toNat * (2 ^ shift) < 2 ^ 64 := by rw [Nat.mul_comm]; exact hshift
  have hsh : idx <<< shift = BitVec.ofNat 64 ((2 ^ shift) * idx.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hm,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt hshift, Nat.mul_comm]
  rw [hsh, pointsToArray_update (2 ^ shift) elemAt ptr xs idx.toNat x' hi]



/-- Bridge between list-indexed `pointsToArray` and function-indexed `sepRange` over `getD`. -/
theorem pointsToArray_eq_sepRange {α : Type _} [Inhabited α] (stride : Nat)
    (elem : BitVec 64 → α → SepProp) (ptr : BitVec 64) (xs : List α) :
    pointsToArray stride elem ptr xs =
      sepRange 0 xs.length (fun i => elem (ptr + BitVec.ofNat 64 (stride * i)) (xs.getD i default)) := by
  induction xs generalizing ptr with
  | nil => simp [pointsToArray_nil, sepRange_zero]
  | cons x xs ih =>
    simp only [pointsToArray_cons, List.length_cons, sepRange_succ, Nat.zero_add,
      List.getD_cons_zero, Nat.mul_zero, BitVec.add_zero]
    rw [ih (ptr + BitVec.ofNat 64 stride)]
    have hshift :
        sepRange 1 xs.length (fun i => elem (ptr + BitVec.ofNat 64 (stride * i)) ((x :: xs).getD i default)) =
          sepRange 0 xs.length
            (fun i => elem (ptr + BitVec.ofNat 64 stride + BitVec.ofNat 64 (stride * i)) (xs.getD i default)) := by
      rw [show (1 : Nat) = 0 + 1 from rfl, sepRange_shift]
      refine sepRange_congr fun i _ _ => ?_
      simp only [List.getD_cons_succ]
      congr 1
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_succ, Nat.add_comm]
    rw [hshift]

theorem pointsToWords64_eq_pointsToArray (ptr : BitVec 64) (ws : List (BitVec 64)) :
    (ptr ↦₆₄* ws) = pointsToArray 8 (· ↦₆₄ ·) ptr ws := by
  induction ws generalizing ptr with
  | nil => rw [pointsToWords64_nil, pointsToArray_nil]
  | cons w ws ih =>
    rw [pointsToWords64_cons, pointsToArray_cons, ih (ptr + 8#64)]

theorem pointsToBytes_eq_pointsToArray (ptr : BitVec 64) (bs : List (BitVec 8)) :
    (ptr ↦ₛ bs) = pointsToArray 1 (· ↦₈ ·) ptr bs := by
  induction bs generalizing ptr with
  | nil => rw [pointsToBytes_nil, pointsToArray_nil]
  | cons b bs ih =>
    rw [pointsToBytes_cons, pointsToArray_cons, ih (ptr + 1#64)]

/-- Hardware multiply-indexed element focus (`madd`/`umaddl`, matching `ptr + BitVec.ofNat 64 stride * idx`). -/
theorem pointsToArray_focus_mul {α : Type _} [Inhabited α] (stride : Nat)
    (elem : BitVec 64 → α → SepProp) (ptr : BitVec 64) (xs : List α) (idx : BitVec 64)
    (hi : idx.toNat < xs.length) :
    pointsToArray stride elem ptr xs =
      (elem (ptr + BitVec.ofNat 64 stride * idx) (xs.getD idx.toNat default) ∗
        (pointsToArray stride elem ptr (xs.take idx.toNat) ∗
         pointsToArray stride elem (ptr + BitVec.ofNat 64 (stride * (idx.toNat + 1)))
           (xs.drop (idx.toNat + 1)))) := by
  have hidx : BitVec.ofNat 64 idx.toNat = idx := by
    apply BitVec.eq_of_toNat_eq
    simp
  have hmul : BitVec.ofNat 64 stride * idx = BitVec.ofNat 64 (stride * idx.toNat) := by
    rw [BitVec.ofNat_mul, hidx]
  rw [pointsToArray_focus stride elem ptr xs idx.toNat hi, ← hmul]

theorem pointsToWords64_eq_pointsToBytes (ptr : BitVec 64) (ws : List (BitVec 64)) :
    (ptr ↦₆₄* ws) = (ptr ↦ₛ unpackL ws) := by
  induction ws generalizing ptr with
  | nil => simp [pointsToWords64_nil, unpackL, pointsToBytes_nil]
  | cons w ws ih =>
    simp only [pointsToWords64_cons, unpackL, List.flatMap_cons, pointsToBytes_append,
      pointsTo64_eq_pointsToBytes ptr w, ih (ptr + 8#64)]
    have hlen : (unpack64 w).length = 8 := rfl
    rw [hlen]

end ProofLib

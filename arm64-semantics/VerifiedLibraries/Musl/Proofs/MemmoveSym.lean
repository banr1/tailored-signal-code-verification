/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import ProofLib.SepLogic.LoopTactics
public meta import ProofLib.SepLogic.LoopTactics

/-!
# Symbolic Execution of `musl` `memmove`

Proves `SepWP` block contracts (`memmove_fwd_entry`, `memmove_bwd_entry`, `memmove_ret`) for all
in-place forward and backward paths of `musl` `memmove` (`MemmoveCode`) inside a single buffer
`base ↦ₛ buf`, tracking partially copied bytes via `mmSet`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Musl

open Arm64 ProofLib

/-- Words `0..25` of `memmove` (up to, excluding, `b memcpy` at `+0x68` = word 26). -/
def memmoveWordsA : List (BitVec 32) := [
  0xaa0003e7#32, 0xaa0103e4#32, 0xeb01001f#32, 0xaa0203e3#32, 0x54000880#32, 0xcb020025#32,
  0xcb0207e6#32, 0xcb0000a8#32, 0xeb06011f#32, 0x54000229#32, 0xca000021#32, 0xeb04001f#32,
  0x92400821#32, 0x54000442#32, 0xb5000321#32, 0x8b0204a2#32, 0x8b030083#32, 0xaa0003e1#32,
  0xcb040040#32, 0xf2400825#32, 0x540000e0#32, 0xeb03009f#32, 0x54000640#32, 0x38401485#32,
  0x38001425#32, 0x17fffff9#32]

/-- Words `27..73` of `memmove` (from `+0x6c` = byte offset 108 to `ret` at `+0x124`). -/
def memmoveWordsB : List (BitVec 32) := [
  0xd343fc03#32, 0x927df006#32, 0x14000004#32,
  0xf8656882#32, 0xf8256822#32, 0x910020a5#32, 0xeb0600bf#32, 0x54ffff81#32, 0xcb030c03#32,
  0x8b050022#32, 0x8b050084#32, 0x14000002#32, 0xaa0003e2#32, 0xd2800001#32, 0xeb01007f#32,
  0x540003c0#32, 0x38616885#32, 0x38216845#32, 0x91000421#32, 0x17fffffb#32, 0xb40000c1#32,
  0xb4000303#32, 0xd1000463#32, 0x38636881#32, 0x382368e1#32, 0x17fffffc#32, 0x8b0300e1#32,
  0xd1000462#32, 0xf240083f#32, 0x540000c0#32, 0xb40001e3#32, 0x38626881#32, 0xaa0203e3#32,
  0x382268e1#32, 0x17fffff8#32, 0x92400862#32, 0xaa0303e1#32, 0x14000003#32, 0xf8616880#32,
  0xf82168e0#32, 0xeb02003f#32, 0xd1002021#32, 0x54ffff81#32, 0x92400863#32, 0x17ffffe9#32,
  0xaa0703e0#32, 0xd65f03c0#32]

/-- The code of `memmove` at `a`, except the `b memcpy` word at `a + 0x68`. -/
def MemmoveCode (prog : Program) (a : BitVec 64) : Prop :=
  prog.hasCode a memmoveWordsA ∧ prog.hasCode (a + 0x6c#64) memmoveWordsB

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-! ## Partial-Move Model -/

private theorem mm_getD_listMove {buf : List (BitVec 8)} {d o len : Nat}
    (hd : d + len ≤ buf.length) (ho : o + len ≤ buf.length) (i : Nat) :
    (listMove buf d o len).getD i 0#8 =
      if d ≤ i ∧ i < d + len then buf.getD (o + (i - d)) 0#8 else buf.getD i 0#8 := by
  simp only [listMove, List.getD_eq_getElem?_getD, List.getElem?_append, List.getElem?_take,
    List.getElem?_drop, List.length_append, List.length_take, List.length_drop,
    show min d buf.length = d by omega, show min len (buf.length - o) = len by omega]
  repeat' split
  all_goals first | rfl | omega | (congr 2; omega)

/-- `buf` with bytes `[lo, hi)` replaced by their `memmove(d, o, len)` values. -/
abbrev mmSet (buf : List (BitVec 8)) (d o len lo hi : Nat) : List (BitVec 8) :=
  ByteSlice.copySet buf (listMove buf d o len) fun i => decide (lo ≤ i) && decide (i < hi)

private theorem mm_getD_mmSet_out {buf : List (BitVec 8)} {d o len lo hi i : Nat}
    (h : i < lo ∨ hi ≤ i) : (mmSet buf d o len lo hi).getD i 0#8 = buf.getD i 0#8 := by
  rw [ByteSlice.getD_copySet]
  have : (decide (lo ≤ i) && decide (i < hi)) = false := by
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
  simp [this]

theorem mmSet_full {buf : List (BitVec 8)} {d o len : Nat}
    (hd : d + len ≤ buf.length) (ho : o + len ≤ buf.length) :
    mmSet buf d o len d (d + len) = listMove buf d o len := by
  apply ByteSlice.ext_getD (by simp [listMove]; omega)
  intro i hi
  simp only [ByteSlice.copySet_length] at hi
  rw [ByteSlice.getD_copySet, mm_getD_listMove hd ho]
  by_cases h : d ≤ i ∧ i < d + len
  · simp [h, hi]
  · simp only [h, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq]; split <;> rfl

theorem mm_mmSet_empty (buf : List (BitVec 8)) (d o len lo : Nat) :
    mmSet buf d o len lo lo = buf := by
  have h : (fun i => decide (lo ≤ i) && decide (i < lo)) = fun _ => false := by
    funext i; simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
  simp only [mmSet, h, ByteSlice.copySet_false]

theorem mm_listMove_self {buf : List (BitVec 8)} {d len : Nat} (hd : d + len ≤ buf.length) :
    listMove buf d d len = buf := by
  apply ByteSlice.ext_getD (by simp [listMove]; omega)
  intro i _
  rw [mm_getD_listMove hd hd]
  split
  · rw [show d + (i - d) = i by omega]
  · rfl

theorem mmSet_write8 {buf : List (BitVec 8)} {d o len lo hi lo' hi' p q : Nat}
    (hd : d + len ≤ buf.length) (ho : o + len ≤ buf.length) (hp : d ≤ p ∧ p < d + len)
    (hq : q = o + (p - d)) (hsrc : q < lo ∨ hi ≤ q) (hle : lo ≤ hi)
    (hgrow : (lo' = lo ∧ p = hi ∧ hi' = hi + 1) ∨ (hi' = hi ∧ p + 1 = lo ∧ lo' = p)) :
    ByteSlice.write8 (mmSet buf d o len lo hi) p ((mmSet buf d o len lo hi).getD q 0#8) =
      mmSet buf d o len lo' hi' := by
  subst hq
  rw [mm_getD_mmSet_out hsrc]
  have hv : buf.getD (o + (p - d)) 0#8 = (listMove buf d o len).getD p 0#8 := by
    rw [mm_getD_listMove hd ho]; simp only [hp, and_self, ↓reduceIte]
  rw [hv]
  refine (ByteSlice.write8_copySet _ _ _ _ (by omega)).trans (ByteSlice.copySet_congr ?_)
  intro i _
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  omega

private theorem mm_mmSet_write64 {buf : List (BitVec 8)} {d o len lo hi lo' hi' p q : Nat}
    (hd : d + len ≤ buf.length) (ho : o + len ≤ buf.length) (hp : d ≤ p ∧ p + 8 ≤ d + len)
    (hq : q = o + (p - d)) (hsrc : q + 8 ≤ lo ∨ hi ≤ q) (hle : lo ≤ hi)
    (hgrow : (lo' = lo ∧ p = hi ∧ hi' = hi + 8) ∨ (hi' = hi ∧ p + 8 = lo ∧ lo' = p)) :
    ByteSlice.write64 (mmSet buf d o len lo hi) p
        (ByteSlice.readLE (mmSet buf d o len lo hi) q 8) =
      mmSet buf d o len lo' hi' := by
  subst hq
  refine (ByteSlice.writeLE_copySet 8 _ _ _ _ _ (by omega) ?_).trans
    (ByteSlice.copySet_congr ?_)
  · intro j hj
    rw [ByteSlice.extractLsb'_readLE _ _ 8 j]
    simp only [hj, ↓reduceIte]
    rw [mm_getD_mmSet_out (by omega), mm_getD_listMove hd ho]
    simp only [show d ≤ p + j by omega, show p + j < d + len by omega, and_self, ↓reduceIte]
    rw [show p + j - d = p - d + j by omega, Nat.add_assoc]
  · intro i _
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    omega

/-! ## Pointer and Counter Arithmetic -/

theorem mm_add_ofNat_add_one {p : BitVec 64} {j k : Nat} (h : j + 1 = k) :
    p + BitVec.ofNat 64 j + 1#64 = p + BitVec.ofNat 64 k := by
  subst h; bv_omega

theorem mm_ofNat_add_one_sub_one (k : Nat) :
    BitVec.ofNat 64 (k + 1) - 1#64 = BitVec.ofNat 64 k := by
  bv_omega

theorem mm_ofNat_succ_ne_zero {k : Nat} (h : k + 1 < 2 ^ 64) :
    ¬(BitVec.ofNat 64 (k + 1) == 0#64) = true := by
  simp only [beq_iff_eq]; bv_omega

private theorem mm_add_ofNat_add_lit {p : BitVec 64} {j k : Nat} (n : Nat) (h : j + n = k) :
    p + BitVec.ofNat 64 j + BitVec.ofNat 64 n = p + BitVec.ofNat 64 k := by
  subst h; bv_omega

private theorem mm_ofNat_sub_ofNat {j k : Nat} (h : k ≤ j) :
    BitVec.ofNat 64 j - BitVec.ofNat 64 k = BitVec.ofNat 64 (j - k) := by
  bv_omega

private theorem mm_lsr3 {r : Nat} (hr : r < 2 ^ 64) :
    (BitVec.ofNat 64 r) >>> (3 : Nat) = BitVec.ofNat 64 (r / 8) := by
  apply BitVec.eq_of_toNat_eq
  simp [Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hr]
  omega

private theorem mm_shl3 (q : Nat) :
    (BitVec.ofNat 64 q) <<< (3 : Nat) = BitVec.ofNat 64 (8 * q) := by
  apply BitVec.eq_of_toNat_eq
  simp [Nat.shiftLeft_eq]
  omega

private theorem mm_and_not7 {r : Nat} (hr : r < 2 ^ 64) :
    (BitVec.ofNat 64 r) &&& 0xfffffffffffffff8#64 = BitVec.ofNat 64 (8 * (r / 8)) := by
  have hbits : ∀ x : BitVec 64, x &&& 0xfffffffffffffff8#64 = (x >>> (3 : Nat)) <<< (3 : Nat) := by
    bv_bits
  rw [hbits, mm_lsr3 hr, mm_shl3]

private theorem mm_and_7 {r : Nat} (hr : r < 2 ^ 64) :
    (BitVec.ofNat 64 r) &&& 7#64 = BitVec.ofNat 64 (r % 8) := by
  have hbits : ∀ x : BitVec 64, x &&& 7#64 = x - (x &&& 0xfffffffffffffff8#64) := by bv_bits
  rw [hbits, mm_and_not7 hr, mm_ofNat_sub_ofNat (Nat.mul_div_le r 8)]
  congr 1; omega

private theorem mm_sub_shl3 {r : Nat} (hr : r < 2 ^ 64) :
    BitVec.ofNat 64 r - ((BitVec.ofNat 64 r >>> (3 : Nat)) <<< (3 : Nat)) =
      BitVec.ofNat 64 (r % 8) := by
  rw [mm_lsr3 hr, mm_shl3, mm_ofNat_sub_ofNat (Nat.mul_div_le r 8)]
  congr 1; omega

private theorem mm_ptr_sub_ptr {base : BitVec 64} {a1 a2 r : Nat} (h : a2 + r = a1) :
    (base + BitVec.ofNat 64 a1) - (base + BitVec.ofNat 64 a2) = BitVec.ofNat 64 r := by
  subst h; bv_omega

private theorem mm_sub_add_shl1 (base : BitVec 64) (o len : Nat) :
    (base + BitVec.ofNat 64 o - BitVec.ofNat 64 len) + (BitVec.ofNat 64 len <<< (1 : Nat)) =
      base + BitVec.ofNat 64 (o + len) := by
  have hbits : ∀ x y : BitVec 64, (x - y) + (y <<< (1 : Nat)) = x + y := by bv_bits
  rw [hbits]; bv_omega

private theorem mm_ofNat_ne {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (hne : x ≠ y) :
    ¬(BitVec.ofNat 64 x == BitVec.ofNat 64 y) = true := by
  simp only [beq_iff_eq]; bv_omega

private theorem mm_ofNat_add_lit {x y z : Nat} (h : x + y = z) :
    BitVec.ofNat 64 x + BitVec.ofNat 64 y = BitVec.ofNat 64 z := by
  subst h; bv_omega

private theorem mm_ofNat_beq_add_lit {z x y : Nat} (h : x + y = z) :
    (BitVec.ofNat 64 z == BitVec.ofNat 64 x + BitVec.ofNat 64 y) = true := by
  subst h; simp only [beq_iff_eq]; bv_omega

private theorem mm_add_lit_beq_ofNat {x y z : Nat} (h : x + y = z) :
    (BitVec.ofNat 64 x + BitVec.ofNat 64 y == BitVec.ofNat 64 z) = true := by
  subst h; simp only [beq_iff_eq]; bv_omega

private theorem mm_add_lit_ne_ofNat {x y z : Nat} (hxy : x + y < 2 ^ 64) (hz : z < 2 ^ 64)
    (hne : x + y ≠ z) :
    ¬(BitVec.ofNat 64 x + BitVec.ofNat 64 y == BitVec.ofNat 64 z) = true := by
  simp only [beq_iff_eq]; bv_omega

private theorem mm_ptr_ne_ptr {base : BitVec 64} {x y : Nat}
    (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (hne : x ≠ y) :
    ¬(base + BitVec.ofNat 64 x == base + BitVec.ofNat 64 y) = true := by
  simp only [beq_iff_eq]; bv_omega

/-! ## Return and Loop Setup -/

/-- Frame facts at every return of `memmove`, relative to the entry state `s0`. -/
abbrev MmExit (s0 : State) (dst : BitVec 64) (sf : State) : Prop :=
  sf.readReg64 .x0 = dst ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

theorem memmove_ret (prog : Program) (a : BitVec 64) (hc : MemmoveCode prog a)
    (s0 s : State) (base : BitVec 64) (bs bs' : List (BitVec 8)) (dst : BitVec 64)
    (heq : bs = bs')
    (hpc : s.pc = a + 0x120#64) (hrun : s.status = .Running)
    (hx7 : s.readReg64 .x7 = dst)
    (hsp : s.sp = s0.sp) (hlr : s.readReg64 .lr = s0.readReg64 .lr)
    (hcs : CalleeSavedPreserved s0 s) :
    SepWP prog (s0.readReg64 .lr) s (base ↦ₛ bs) (sepPost (MmExit s0 dst) (base ↦ₛ bs')) := by
  subst heq
  obtain ⟨hc1, hc2⟩ := hc
  rw [← hlr]
  wp_sym_steps
  wp_done

local macro "mm_side" : tactic => `(tactic|
  first
  | assumption
  | omega
  | simp (config := { decide := true }) [CalleeSavedPreserved.iff_regs, arm64_norm, *])

set_option hygiene false in
local notation "MM[" s ", " lo ", " hi "]" =>
  SepWP prog (State.readReg64 s0 .lr) s (base ↦ₛ mmSet buf d o len lo hi)
    (sepPost (MmExit s0 (base + BitVec.ofNat 64 d)) (base ↦ₛ listMove buf d o len))

variable {prog : Program} {a : BitVec 64} (hc : MemmoveCode prog a)
  {s0 : State} {base : BitVec 64} {buf : List (BitVec 8)} {d o len : Nat}
  (hd : d + len ≤ buf.length) (ho : o + len ≤ buf.length) (hbuf : buf.length < 2 ^ 63)
  {s : State} (hrun : s.status = .Running) (hx7 : s.readReg64 .x7 = base + BitVec.ofNat 64 d)
  (hsp : s.sp = s0.sp) (hlr : s.readReg64 .lr = s0.readReg64 .lr)
  (hcs : CalleeSavedPreserved s0 s)

/-! ## Forward Blocks (`dst < src`) -/

section Forward

variable (hfwd : d ≤ o ∨ o + len ≤ d)

include hc hd ho hbuf hfwd hrun hx7 hsp hlr hcs

theorem memmove_fwd_bytes {j r : Nat} (hjr : j + r = len) (hpc : s.pc = a + 0xa0#64)
    (hx2 : s.readReg64 .x2 = base + BitVec.ofNat 64 (d + j))
    (hx4 : s.readReg64 .x4 = base + BitVec.ofNat 64 (o + j))
    (hx3 : s.readReg64 .x3 = BitVec.ofNat 64 r) :
    MM[s, d, d + j] := by
  obtain ⟨hc1, hc2⟩ := hc
  rw [← hlr]
  rcases r with _ | m
  · obtain rfl : j = len := by omega
    rw [mmSet_full hd ho]
    wp_sym_steps
    wp_done
  rw [show d + j = d + j + (m - m) by omega]
  wp_step
  wp_loop_measure frame m (fun k st =>
    k ≤ m ∧ st.readReg64 .x7 = base + BitVec.ofNat 64 d ∧
      st.readReg64 .x2 = base + BitVec.ofNat 64 (d + j) ∧
      st.readReg64 .x4 = base + BitVec.ofNat 64 (o + j) ∧
      st.readReg64 .x3 = BitVec.ofNat 64 (m + 1) ∧
      st.readReg64 .x1 = BitVec.ofNat 64 (m - k))
    (fun k _ => base ↦ₛ mmSet buf d o len d (d + j + (m - k)))
  case base =>
    simp only [Nat.sub_zero]
    have hne := mm_ofNat_ne (x := m + 1) (y := m) (by omega) (by omega) (by omega)
    have heq := mm_ofNat_beq_add_lit (z := m + 1) (x := m) (y := 1) rfl
    have hsrc_p := mm_add_ofNat_add_lit (p := base) (j := o + j) (k := o + j + m) m rfl
    have hdst_p := mm_add_ofNat_add_lit (p := base) (j := d + j) (k := d + j + m) m rfl
    wp_sym_steps
    wp_conv_pre => rw [mmSet_write8 (lo' := d) (hi' := d + len) hd ho (by omega) (by omega)
      (by omega) (by omega) (by omega), mmSet_full hd ho]
    wp_done
  case step =>
    right
    have hne := mm_ofNat_ne (x := m + 1) (y := m - (m' + 1)) (by omega) (by omega) (by omega)
    have hsrc_p := mm_add_ofNat_add_lit (p := base) (j := o + j)
      (k := o + j + (m - (m' + 1))) (m - (m' + 1)) rfl
    have hdst_p := mm_add_ofNat_add_lit (p := base) (j := d + j)
      (k := d + j + (m - (m' + 1))) (m - (m' + 1)) rfl
    have hx1' := mm_ofNat_add_lit (x := m - (m' + 1)) (y := 1) (z := m - m') (by omega)
    wp_sym_steps
    wp_conv_pre => rw [mmSet_write8 (lo' := d) (hi' := d + j + (m - m')) hd ho (by omega)
      (by omega) (by omega) (by omega) (by omega)]
    wp_done

theorem memmove_fwd_words {j r : Nat} (hjr : j + r = len) (hpc : s.pc = a + 0x6c#64)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 r)
    (hx1 : s.readReg64 .x1 = base + BitVec.ofNat 64 (d + j))
    (hx4 : s.readReg64 .x4 = base + BitVec.ofNat 64 (o + j))
    (hx5 : s.readReg64 .x5 = 0#64) :
    MM[s, d, d + j] := by
  have ⟨hc1, hc2⟩ := hc
  by_cases hr8 : r < 8
  · have hnot7 := mm_and_not7 (r := r) (by omega)
    have hrem := mm_sub_shl3 (r := r) (by omega)
    rw [show r / 8 = 0 by omega, Nat.mul_zero] at hnot7
    rw [show r % 8 = r by omega] at hrem
    wp_sym_steps 9
    apply memmove_fwd_bytes (hc := hc) (hfwd := hfwd) (j := j) (r := r) <;> mm_side
  obtain ⟨q, t, rfl, ht⟩ : ∃ q t, r = 8 * (q + 1) + t ∧ t < 8 :=
    ⟨r / 8 - 1, r % 8, by omega, by omega⟩
  have hdiv : (8 * (q + 1) + t) / 8 = q + 1 := by omega
  have hmod : (8 * (q + 1) + t) % 8 = t := by omega
  have hlsr := mm_lsr3 (r := 8 * (q + 1) + t) (by omega)
  have hnot7 := mm_and_not7 (r := 8 * (q + 1) + t) (by omega)
  rw [hdiv] at hlsr hnot7
  have hne0 := mm_ofNat_ne (x := 0) (y := 8 * (q + 1)) (by omega) (by omega) (by omega)
  wp_sym_steps 5
  rw [show d + j = d + j + 8 * (q - q) by omega]
  wp_join_sep (a + 0xa0#64)
    (fun st => st.readReg64 .x7 = base + BitVec.ofNat 64 d ∧
      st.readReg64 .x2 = base + BitVec.ofNat 64 (d + (j + 8 * (q + 1))) ∧
      st.readReg64 .x4 = base + BitVec.ofNat 64 (o + (j + 8 * (q + 1))) ∧
      st.readReg64 .x3 = BitVec.ofNat 64 t ∧
      st.sp = s.sp ∧ st.readReg64 .lr = s.readReg64 .lr ∧ CalleeSavedPreserved s st)
    (base ↦ₛ mmSet buf d o len d (d + (j + 8 * (q + 1))))
  · wp_loop_measure frame q (fun k st =>
      k ≤ q ∧ st.readReg64 .x7 = base + BitVec.ofNat 64 d ∧
        st.readReg64 .x0 = BitVec.ofNat 64 (8 * (q + 1) + t) ∧
        st.readReg64 .x1 = base + BitVec.ofNat 64 (d + j) ∧
        st.readReg64 .x4 = base + BitVec.ofNat 64 (o + j) ∧
        st.readReg64 .x3 = BitVec.ofNat 64 (q + 1) ∧
        st.readReg64 .x6 = BitVec.ofNat 64 (8 * (q + 1)) ∧
        st.readReg64 .x5 = BitVec.ofNat 64 (8 * (q - k)))
      (fun k _ => base ↦ₛ mmSet buf d o len d (d + j + 8 * (q - k)))
    case base =>
      simp only [Nat.sub_zero]
      have hsrc_p := mm_add_ofNat_add_lit (p := base) (j := o + j) (k := o + j + 8 * q) (8 * q) rfl
      have hdst_p := mm_add_ofNat_add_lit (p := base) (j := d + j) (k := d + j + 8 * q) (8 * q) rfl
      have heq := mm_add_lit_beq_ofNat (x := 8 * q) (y := 8) (z := 8 * (q + 1)) (by omega)
      have hx5' := mm_ofNat_add_lit (x := 8 * q) (y := 8) (z := 8 * (q + 1)) (by omega)
      have hx3' : BitVec.ofNat 64 (8 * (q + 1) + t) - (BitVec.ofNat 64 (q + 1) <<< (3 : Nat)) =
          BitVec.ofNat 64 t := by
        rw [mm_shl3, mm_ofNat_sub_ofNat (by omega)]
        congr 1; omega
      have hx2' := mm_add_ofNat_add_lit (p := base) (j := d + j)
        (k := d + (j + 8 * (q + 1))) (8 * (q + 1)) (by omega)
      have hx4' := mm_add_ofNat_add_lit (p := base) (j := o + j)
        (k := o + (j + 8 * (q + 1))) (8 * (q + 1)) (by omega)
      wp_sym_steps
      wp_conv_pre => rw [mm_mmSet_write64 (lo' := d) (hi' := d + (j + 8 * (q + 1))) hd ho
        (by omega) (by omega) (by omega) (by omega) (by omega)]
      wp_done
    case step =>
      right
      have hsrc_p := mm_add_ofNat_add_lit (p := base) (j := o + j)
        (k := o + j + 8 * (q - (m' + 1))) (8 * (q - (m' + 1))) rfl
      have hdst_p := mm_add_ofNat_add_lit (p := base) (j := d + j)
        (k := d + j + 8 * (q - (m' + 1))) (8 * (q - (m' + 1))) rfl
      have hne := mm_add_lit_ne_ofNat (x := 8 * (q - (m' + 1))) (y := 8) (z := 8 * (q + 1))
        (by omega) (by omega) (by omega)
      have hx5' := mm_ofNat_add_lit (x := 8 * (q - (m' + 1))) (y := 8)
        (z := 8 * (q - m')) (by omega)
      wp_sym_steps
      wp_conv_pre => rw [mm_mmSet_write64 (lo' := d) (hi' := d + j + 8 * (q - m')) hd ho
        (by omega) (by omega) (by omega) (by omega) (by omega)]
      wp_done
  · intro sj hpcj hrunj ⟨hj7, hj2, hj4, hj3, hjsp, hjlr, hjcs⟩
    apply memmove_fwd_bytes (hc := hc) (hfwd := hfwd) (s := sj) (j := j + 8 * (q + 1)) (r := t)
      (hcs := hcs.trans hjcs) <;> mm_side

theorem memmove_fwd_align (hpc : s.pc = a + 0x48#64)
    (hx1 : s.readReg64 .x1 = base + BitVec.ofNat 64 d)
    (hx4 : s.readReg64 .x4 = base + BitVec.ofNat 64 o)
    (hx2 : s.readReg64 .x2 = base + BitVec.ofNat 64 (o + len))
    (hx3 : s.readReg64 .x3 = base + BitVec.ofNat 64 (o + len)) :
    MM[s, d, d] := by
  have ⟨hc1, hc2⟩ := hc
  rw [show mmSet buf d o len d d = mmSet buf d o len d (d + (len - len)) by congr 1; omega]
  have hx1_0 : s.readReg64 .x1 = base + BitVec.ofNat 64 (d + (len - len)) := by simpa using hx1
  have hx4_0 : s.readReg64 .x4 = base + BitVec.ofNat 64 (o + (len - len)) := by simpa using hx4
  wp_loop_measure frame len (fun k st =>
    k ≤ len ∧ st.readReg64 .x7 = base + BitVec.ofNat 64 d ∧
      st.readReg64 .x1 = base + BitVec.ofNat 64 (d + (len - k)) ∧
      st.readReg64 .x4 = base + BitVec.ofNat 64 (o + (len - k)) ∧
      st.readReg64 .x2 = base + BitVec.ofNat 64 (o + len) ∧
      st.readReg64 .x3 = base + BitVec.ofNat 64 (o + len))
    (fun k _ => base ↦ₛ mmSet buf d o len d (d + (len - k)))
  case base =>
    simp only [Nat.sub_zero] at *
    have hx0' := mm_ptr_sub_ptr (base := base) (a1 := o + len) (a2 := o + len) (r := 0) (by omega)
    wp_sym_steps
    wp_if hal
    · have hal_eq : (base + BitVec.ofNat 64 (d + len)) &&& 7#64 = 0#64 := by
        first | exact hal | exact beq_iff_eq.mp hal
      apply memmove_fwd_words (hc := hc) (hfwd := hfwd) (j := len) (r := 0)
        (hcs := hcs.trans (by mm_side)) <;> mm_side
    wp_sym_steps 2
    refine memmove_ret prog a hc s0 _ base _ _ _ (mmSet_full hd ho) ?_ ?_ ?_ ?_ ?_
      (hcs.trans (by mm_side)) <;> mm_side
  case step =>
    have hx0' := mm_ptr_sub_ptr (base := base) (a1 := o + len) (a2 := o + (len - (m' + 1)))
      (r := m' + 1) (by omega)
    by_cases hal : ((base + BitVec.ofNat 64 (d + (len - (m' + 1)))) &&& 7#64 == 0#64) = true
    · left
      have hal_eq : (base + BitVec.ofNat 64 (d + (len - (m' + 1)))) &&& 7#64 = 0#64 :=
        beq_iff_eq.mp hal
      wp_sym_steps 3
      apply memmove_fwd_words (hc := hc) (hfwd := hfwd) (j := len - (m' + 1)) (r := m' + 1)
        (hcs := hcs.trans (by mm_side)) <;> mm_side
    · right
      have hne_end := mm_ptr_ne_ptr (base := base) (x := o + (len - (m' + 1))) (y := o + len)
        (by omega) (by omega) (by omega)
      have hx1' := mm_add_ofNat_add_one (p := base) (j := d + (len - (m' + 1)))
        (k := d + (len - m')) (by omega)
      have hx4' := mm_add_ofNat_add_one (p := base) (j := o + (len - (m' + 1)))
        (k := o + (len - m')) (by omega)
      wp_sym_steps
      wp_conv_pre => rw [mmSet_write8 (lo' := d) (hi' := d + (len - m')) hd ho (by omega)
        (by omega) (by omega) (by omega) (by omega)]
      wp_done

/-- Forward entry at `+0x38` (`cbnz x1, +0x9c`, `x1 = (src ^ dst) & 7`): non-co-aligned pointers
    jump to `memmove_fwd_bytes` via `+0x9c`; co-aligned pointers compute `src + len` and enter
    `memmove_fwd_align` at `+0x48`. -/
theorem memmove_fwd_entry (hpc : s.pc = a + 0x38#64)
    (hx0 : s.readReg64 .x0 = base + BitVec.ofNat 64 d)
    (hx4 : s.readReg64 .x4 = base + BitVec.ofNat 64 o)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 len)
    (hx3 : s.readReg64 .x3 = BitVec.ofNat 64 len)
    (hx5 : s.readReg64 .x5 = base + BitVec.ofNat 64 o - BitVec.ofNat 64 len) :
    MM[s, d, d] := by
  have ⟨hc1, hc2⟩ := hc
  have hx2_end := mm_sub_add_shl1 base o len
  have hx3_end := mm_add_ofNat_add_lit (p := base) (j := o) (k := o + len) len rfl
  wp_sym_steps
  wp_if hnz
  · wp_sym_steps 1
    apply memmove_fwd_bytes (hc := hc) (hfwd := hfwd) (j := 0) (r := len) <;> mm_side
  wp_sym_steps 3
  apply memmove_fwd_align (hc := hc) (hfwd := hfwd) <;> mm_side

end Forward


/-! ## Backward Blocks (`src < dst`) -/

private theorem mm_mmSet_full_of {buf : List (BitVec 8)} {d o len lo : Nat}
    (hd : d + len ≤ buf.length) (ho : o + len ≤ buf.length) (hlo : lo = d) :
    mmSet buf d o len lo (d + len) = listMove buf d o len := by
  subst hlo; exact mmSet_full hd ho

section Backward

variable (hbwd : o ≤ d ∨ d + len ≤ o) (hx4 : s.readReg64 .x4 = base + BitVec.ofNat 64 o)

include hc hd ho hbuf hbwd hrun hx7 hx4 hsp hlr hcs

theorem memmove_bwd_bytes {r : Nat} (hr : r ≤ len) (hpc : s.pc = a + 0xc0#64)
    (hx3 : s.readReg64 .x3 = BitVec.ofNat 64 r) :
    MM[s, d + r, d + len] := by
  obtain ⟨hc1, hc2⟩ := hc
  rw [← hlr]
  rcases r with _ | m
  · rw [mm_mmSet_full_of hd ho (Nat.add_zero d)]
    wp_sym_steps
    wp_done
  wp_loop_measure frame m (fun k st =>
    k < len ∧ st.readReg64 .x7 = base + BitVec.ofNat 64 d ∧
      st.readReg64 .x4 = base + BitVec.ofNat 64 o ∧
      st.readReg64 .x3 = BitVec.ofNat 64 (k + 1))
    (fun k _ => base ↦ₛ mmSet buf d o len (d + (k + 1)) (d + len))
  case base =>
    have hcbz := mm_ofNat_succ_ne_zero (k := 0) (by omega)
    have hx3' := mm_ofNat_add_one_sub_one 0
    simp only [Nat.zero_add] at *
    wp_sym_steps
    wp_conv_pre => rw [mmSet_write8 (lo' := d) (hi' := d + len) hd ho (by omega) (by omega)
      (by omega) (by omega) (by omega), mmSet_full hd ho]
    wp_done
  case step =>
    right
    have hcbz := mm_ofNat_succ_ne_zero (k := m' + 1) (by omega)
    have hx3' := mm_ofNat_add_one_sub_one (m' + 1)
    have hsrc_p := mm_add_ofNat_add_lit (p := base) (j := o) (k := o + (m' + 1)) (m' + 1) rfl
    have hdst_p := mm_add_ofNat_add_lit (p := base) (j := d) (k := d + (m' + 1)) (m' + 1) rfl
    wp_sym_steps
    wp_conv_pre => rw [mmSet_write8 (lo' := d + (m' + 1)) (hi' := d + len) hd ho (by omega)
      (by omega) (by omega) (by omega) (by omega)]
    wp_done

theorem memmove_bwd_words {r : Nat} (hr : r ≤ len) (hpc : s.pc = a + 0xf8#64)
    (hx3 : s.readReg64 .x3 = BitVec.ofNat 64 r) :
    MM[s, d + r, d + len] := by
  have ⟨hc1, hc2⟩ := hc
  by_cases hr8 : r < 8
  · have hand := mm_and_7 (r := r) (by omega)
    rw [show r % 8 = r by omega] at hand
    wp_sym_steps 8
    apply memmove_bwd_bytes (hc := hc) (hbwd := hbwd) (r := r) <;> mm_side
  obtain ⟨q, t, rfl, ht⟩ : ∃ q t, r = 8 * (q + 1) + t ∧ t < 8 :=
    ⟨r / 8 - 1, r % 8, by omega, by omega⟩
  have hand := mm_and_7 (r := 8 * (q + 1) + t) (by omega)
  rw [show (8 * (q + 1) + t) % 8 = t by omega] at hand
  have hne0 := mm_ofNat_ne (x := 8 * (q + 1) + t) (y := t) (by omega) (by omega) (by omega)
  have hx1_init := mm_ofNat_sub_ofNat (j := 8 * (q + 1) + t) (k := 8) (by omega)
  rw [show 8 * (q + 1) + t - 8 = 8 * q + t by omega] at hx1_init
  wp_sym_steps 6
  wp_join_sep (a + 0xc0#64)
    (fun st => st.readReg64 .x7 = base + BitVec.ofNat 64 d ∧
      st.readReg64 .x4 = base + BitVec.ofNat 64 o ∧
      st.readReg64 .x3 = BitVec.ofNat 64 t ∧
      st.sp = s.sp ∧ st.readReg64 .lr = s.readReg64 .lr ∧ CalleeSavedPreserved s st)
    (base ↦ₛ mmSet buf d o len (d + t) (d + len))
  · wp_loop_measure frame q (fun k st =>
      k ≤ q ∧ st.readReg64 .x7 = base + BitVec.ofNat 64 d ∧
        st.readReg64 .x4 = base + BitVec.ofNat 64 o ∧
        st.readReg64 .x3 = BitVec.ofNat 64 (8 * (q + 1) + t) ∧
        st.readReg64 .x2 = BitVec.ofNat 64 t ∧
        st.readReg64 .x1 = BitVec.ofNat 64 (8 * k + t))
      (fun k _ => base ↦ₛ mmSet buf d o len (d + (8 * (k + 1) + t)) (d + len))
    case base =>
      simp only [Nat.zero_add, Nat.mul_one] at *
      have hsrc_p := mm_add_ofNat_add_lit (p := base) (j := o) (k := o + t) t rfl
      have hdst_p := mm_add_ofNat_add_lit (p := base) (j := d) (k := d + t) t rfl
      wp_sym_steps
      wp_conv_pre => rw [mm_mmSet_write64 (lo' := d + t) (hi' := d + len) hd ho (by omega)
        (by omega) (by omega) (by omega) (by omega)]
      wp_done
    case step =>
      right
      have hsrc_p := mm_add_ofNat_add_lit (p := base) (j := o)
        (k := o + (8 * (m' + 1) + t)) (8 * (m' + 1) + t) rfl
      have hdst_p := mm_add_ofNat_add_lit (p := base) (j := d)
        (k := d + (8 * (m' + 1) + t)) (8 * (m' + 1) + t) rfl
      have hne := mm_ofNat_ne (x := 8 * (m' + 1) + t) (y := t) (by omega) (by omega) (by omega)
      have hx1' := mm_ofNat_sub_ofNat (j := 8 * (m' + 1) + t) (k := 8) (by omega)
      rw [show 8 * (m' + 1) + t - 8 = 8 * m' + t by omega] at hx1'
      wp_sym_steps
      wp_conv_pre => rw [mm_mmSet_write64 (lo' := d + (8 * (m' + 1) + t)) (hi' := d + len) hd ho
        (by omega) (by omega) (by omega) (by omega) (by omega)]
      wp_done
  · intro sj hpcj hrunj ⟨hj7, hj4, hj3, hjsp, hjlr, hjcs⟩
    apply memmove_bwd_bytes (hc := hc) (hbwd := hbwd) (s := sj) (r := t)
      (hcs := hcs.trans hjcs) <;> mm_side

theorem memmove_bwd_align (hpc : s.pc = a + 0xd4#64)
    (hx3 : s.readReg64 .x3 = BitVec.ofNat 64 len) :
    MM[s, d + len, d + len] := by
  have ⟨hc1, hc2⟩ := hc
  wp_loop_measure frame len (fun k st =>
    k ≤ len ∧ st.readReg64 .x7 = base + BitVec.ofNat 64 d ∧
      st.readReg64 .x4 = base + BitVec.ofNat 64 o ∧
      st.readReg64 .x3 = BitVec.ofNat 64 k)
    (fun k _ => base ↦ₛ mmSet buf d o len (d + k) (d + len))
  case base =>
    wp_sym_steps
    wp_if hal
    · apply memmove_bwd_words (hc := hc) (hbwd := hbwd) (r := 0)
        (hcs := hcs.trans (by mm_side)) <;> mm_side
    wp_sym_steps 1
    refine memmove_ret prog a hc s0 _ base _ _ _ (mm_mmSet_full_of hd ho (Nat.add_zero d))
      ?_ ?_ ?_ ?_ ?_ (hcs.trans (by mm_side)) <;> mm_side
  case step =>
    have hx1_end := mm_add_ofNat_add_lit (p := base) (j := d) (k := d + (m' + 1)) (m' + 1) rfl
    have hx2' := mm_ofNat_add_one_sub_one m'
    by_cases hal : ((base + BitVec.ofNat 64 (d + (m' + 1))) &&& 7#64 == 0#64) = true
    · left
      wp_sym_steps 4
      apply memmove_bwd_words (hc := hc) (hbwd := hbwd) (r := m' + 1)
        (hcs := hcs.trans (by mm_side)) <;> mm_side
    · right
      have hcbz := mm_ofNat_succ_ne_zero (k := m') (by omega)
      have hsrc_p := mm_add_ofNat_add_lit (p := base) (j := o) (k := o + m') m' rfl
      have hdst_p := mm_add_ofNat_add_lit (p := base) (j := d) (k := d + m') m' rfl
      wp_sym_steps
      wp_conv_pre => rw [mmSet_write8 (lo' := d + m') (hi' := d + len) hd ho (by omega)
        (by omega) (by omega) (by omega) (by omega)]
      wp_done

/-- Backward entry at `+0xbc` (`cbz x1, +0xd4`, `x1 = (src ^ dst) & 7`): co-aligned pointers take
    `memmove_bwd_align` at `+0xd4`, otherwise `memmove_bwd_bytes` at `+0xc0`. -/
theorem memmove_bwd_entry (hpc : s.pc = a + 0xbc#64)
    (hx3 : s.readReg64 .x3 = BitVec.ofNat 64 len) :
    MM[s, d + len, d + len] := by
  have ⟨hc1, hc2⟩ := hc
  wp_sym_steps
  wp_if hz
  · apply memmove_bwd_align (hc := hc) (hbwd := hbwd) <;> mm_side
  apply memmove_bwd_bytes (hc := hc) (hbwd := hbwd) (r := len) <;> mm_side

end Backward

end VerifiedLibraries.Musl

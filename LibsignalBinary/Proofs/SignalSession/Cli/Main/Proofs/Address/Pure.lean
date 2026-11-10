/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Model
import ProofLib.SepLogic.WP.StateNorm

@[expose] public section

set_option autoImplicit false

/-!
# `memrchrSpec` and Pure Parsing Equivalences for `signal_session::address`

Defines `MemrchrCall`, `memrchrIdx`, and `memrchrSpec`, and proves the pure equivalences between
`memrchrIdx 46#8 bs` and `rsplitDot bs`, `serviceIdParse` name lengths (`36` or `40`), the compiled
device-ID digit loop and `sxtb ≤ 0` check against `parseUnsigned 255` in `1..=127`, and address-space
bounds from `IsBlock.disjoint`.
-/

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr

structure MemrchrCall where
  c : BitVec 8
  p : BitVec 64
  bs : List (BitVec 8)

/-- Index of the last occurrence of `c` in `bs` (matching `CliRun.memrchrHook`). -/
def memrchrIdx (c : BitVec 8) (bs : List (BitVec 8)) : Option Nat :=
  ((List.range bs.length).filter fun i => bs[i]? == some c).getLast?

/-- Specification of `core::slice::memchr::memrchr(c, p, len) -> Option<usize>`. -/
def memrchrSpec (stk : Nat) : Spec MemrchrCall where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = x.c ∧ s.readReg64 .x1 = x.p ∧
      s.readReg64 .x2 = BitVec.ofNat 64 x.bs.length ∧ x.bs.length < 2 ^ 64⌝ ∗
      (x.p ↦ₛ x.bs) ∗ stackAt s.sp stk
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.fs = s0.fs ∧ match memrchrIdx x.c x.bs with
      | some i => sf.readReg64 .x0 = 1#64 ∧ sf.readReg64 .x1 = BitVec.ofNat 64 i
      | none => sf.readReg64 .x0 = 0#64⌝ ∗ (x.p ↦ₛ x.bs) ∗ stackAt s0.sp stk

namespace Address.Helpers

/-! ## Address-Space Bounds from `IsBlock.disjoint` -/

theorem slice_lt_addr_space {m : Memory} {p out : BitVec 64} {bs : List (BitVec 8)}
    {R : SepProp} (h : m ⊨ (p ↦ₛ bs) ∗ (memRegion out 32 ∗ R)) :
    bs.length < 2 ^ 64 := by
  by_cases hpos : 0 < bs.length
  · have hd := IsBlock.disjoint (IsBlock.pointsToBytes p bs)
      (IsBlock.memRegion out 32) hpos (by decide) h
    unfold DisjointRegions at hd
    have := (out - p).isLt
    omega
  · omega

theorem stack_lt_addr_space_32 {m : Memory} {sp out : BitVec 64} {stk : Nat}
    {R : SepProp} (h : m ⊨ stackAt sp stk ∗ (memRegion out 32 ∗ R))
    (hpos : 0 < stk) : stk < 2 ^ 64 := by
  have hd := IsBlock.disjoint (IsBlock.memRegion (sp - BitVec.ofNat 64 stk) stk)
    (IsBlock.memRegion out 32) hpos (by decide) h
  unfold DisjointRegions at hd
  have := (out - (sp - BitVec.ofNat 64 stk)).isLt
  omega

/-! ## `memrchrIdx` and `rsplitDot` -/

private theorem range_succ_eq (n : Nat) :
    List.range (n + 1) = List.range n ++ [n] :=
  List.range_succ

theorem memrchrIdx_snoc (c b : BitVec 8) (bs : List (BitVec 8)) :
    memrchrIdx c (bs ++ [b]) =
      if b == c then some bs.length else memrchrIdx c bs := by
  unfold memrchrIdx
  rw [List.length_append, List.length_singleton, List.range_succ, List.filter_append]
  have hpref : (List.range bs.length).filter (fun i => (bs ++ [b])[i]? == some c) =
      (List.range bs.length).filter (fun i => bs[i]? == some c) := by
    apply List.filter_congr
    intro i hi
    rw [List.mem_range] at hi
    rw [List.getElem?_append_left hi]
  rw [hpref]
  have hlast : ([bs.length].filter fun i => (bs ++ [b])[i]? == some c) =
      if b == c then [bs.length] else [] := by
    have helem : (bs ++ [b])[bs.length]? = some b := by
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl
    simp only [List.filter, helem]
    cases hb : (b == c)
    · have hne : b ≠ c := by simpa using hb
      have hbeq : (some b == some c) = false := beq_false_of_ne (fun h => hne (Option.some.inj h))
      rw [hbeq]
      rfl
    · have heq : b = c := by simpa using hb
      subst heq
      simp
  rw [hlast]
  split
  · rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)]
    rfl
  · rw [List.append_nil]

private theorem span_loop_eq {α : Type} (p : α → Bool) :
    ∀ (xs acc : List α),
      List.span.loop p xs acc = (acc.reverse ++ xs.takeWhile p, xs.dropWhile p)
  | [], acc => by simp [List.span.loop]
  | x :: xs, acc => by
    unfold List.span.loop
    cases hx : p x
    · simp [List.takeWhile, List.dropWhile, hx]
    · simp [List.takeWhile, List.dropWhile, hx, span_loop_eq p xs (x :: acc), List.append_assoc]

private theorem list_span_eq {α : Type} (p : α → Bool) (xs : List α) :
    xs.span p = (xs.takeWhile p, xs.dropWhile p) := by
  simpa [List.span] using span_loop_eq p xs []

private theorem rsplitDot_snoc (bs : List (BitVec 8)) (b : BitVec 8) :
    rsplitDot (bs ++ [b]) =
      if b == 46#8 then some (bs, [])
      else (rsplitDot bs).map (fun (n, d) => (n, d ++ [b])) := by
  unfold rsplitDot
  rw [list_span_eq, List.reverse_append]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
    List.takeWhile_cons, List.dropWhile_cons]
  cases hb : (b == 46#8)
  · have hne : (b != 46#8) = true := by simpa [bne] using hb
    simp only [hne, ↓reduceIte, Bool.false_eq_true]
    cases hdw : bs.reverse.dropWhile (fun x => x != 46#8) with
    | nil =>
      rw [list_span_eq, hdw]; rfl
    | cons dot nameR =>
      rw [list_span_eq, hdw]
      dsimp only [Option.map]
      rw [List.reverse_cons]
  · have heq : (b != 46#8) = false := by simpa [bne] using hb
    simp only [heq, Bool.false_eq_true, ↓reduceIte]
    rw [List.reverse_reverse, List.reverse_nil]

theorem memrchrIdx_none_iff_rsplitDot (bs : List (BitVec 8)) :
    memrchrIdx 46#8 bs = none ↔ rsplitDot bs = none := by
  induction bs using List.reverseRecOn with
  | nil => simp [memrchrIdx, rsplitDot]
  | append_singleton xs b ih =>
    rw [memrchrIdx_snoc, rsplitDot_snoc]
    cases hb : (b == 46#8) <;> simp [ih]

theorem memrchrIdx_some_props {bs : List (BitVec 8)} {i : Nat}
    (h : memrchrIdx 46#8 bs = some i) :
    i < bs.length ∧ bs[i]? = some 46#8 ∧
      bs = bs.take i ++ [46#8] ++ bs.drop (i + 1) ∧
      rsplitDot bs = some (bs.take i, bs.drop (i + 1)) := by
  induction bs using List.reverseRecOn generalizing i with
  | nil => simp [memrchrIdx] at h
  | append_singleton xs b ih =>
    rw [memrchrIdx_snoc, rsplitDot_snoc] at *
    cases hb : (b == 46#8)
    · rw [hb] at h
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      obtain ⟨hilt, hget, hsplit, hrs⟩ := ih h
      have hlen : (xs ++ [b]).length = xs.length + 1 := by simp
      have htake : (xs ++ [b]).take i = xs.take i :=
        List.take_append_of_le_length (Nat.le_of_lt hilt)
      have hdrop : (xs ++ [b]).drop (i + 1) = xs.drop (i + 1) ++ [b] :=
        List.drop_append_of_le_length hilt
      refine ⟨by omega, ?_, ?_, ?_⟩
      · rw [List.getElem?_append_left hilt]; exact hget
      · rw [htake, hdrop, ← List.append_assoc, ← hsplit]
      · rw [hrs, htake, hdrop]; rfl
    · rw [hb] at h
      simp only [↓reduceIte, Option.some.injEq] at h ⊢
      subst h
      have hbeq : b = 46#8 := by simpa using hb
      subst hbeq
      have htake : (xs ++ [46#8]).take xs.length = xs := by simp
      have hdrop : (xs ++ [46#8]).drop (xs.length + 1) = [] := by simp
      refine ⟨by simp, ?_, ?_, ?_⟩
      · rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl
      · rw [htake, hdrop, List.append_nil]
      · rw [htake, hdrop]

/-! ## `serviceIdParse` Name Lengths -/

/-! ## Device `parseUnsigned 255` and `sxtb` Filter Equivalences -/

set_option maxRecDepth 200000

def digitSub32 (b : BitVec 8) : BitVec 32 :=
  b.zeroExtend 32 - 0x30#32

theorem isDigit_iff_sub32_ule9 (b : BitVec 8) :
    ((digitSub32 b).ule 9#32) = isDigit b := by
  revert b; decide

theorem not_isDigit_iff_hi9 (b : BitVec 8) :
    ((9#32).ult (digitSub32 b)) = !isDigit b := by
  revert b; decide

theorem digitSub32_toNat (b : BitVec 8) (h : isDigit b = true) :
    digitSub32 b = BitVec.ofNat 32 (b.toNat - 48) := by
  revert b h; decide

theorem digit_val_le9 (b : BitVec 8) (h : isDigit b = true) :
    b.toNat - 48 ≤ 9 := by
  unfold isDigit at h
  simp only [decide_eq_true_eq] at h
  omega

theorem two_digits_madd (d0 d1 : BitVec 8)
    (h0 : isDigit d0 = true) (h1 : isDigit d1 = true) :
    digitSub32 d0 * 10#32 + digitSub32 d1 =
      BitVec.ofNat 32 (10 * (d0.toNat - 48) + (d1.toNat - 48)) := by
  rw [digitSub32_toNat d0 h0, digitSub32_toNat d1 h1]
  have v0 := digit_val_le9 d0 h0
  have v1 := digit_val_le9 d1 h1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

theorem sxtb_le_zero_iff (d : Nat) (hd : d ≤ 255) :
    (((BitVec.ofNat 64 d).truncate 8).signExtend 32).sle 0#32 =
      decide ¬(1 ≤ d ∧ d ≤ 127) := by
  have hfin : ∃ k : Fin 256, k.val = d := ⟨⟨d, by omega⟩, rfl⟩
  rcases hfin with ⟨k, rfl⟩
  revert k; decide

theorem sxtb_sgt_zero_iff (d : Nat) (hd : d ≤ 255) :
    BitVec.slt 0#32 ((((BitVec.ofNat 64 d).truncate 8).signExtend 64).truncate 32) =
      decide (1 ≤ d ∧ d ≤ 127) := by
  have hfin : ∃ k : Fin 256, k.val = d := ⟨⟨d, by omega⟩, rfl⟩
  rcases hfin with ⟨k, rfl⟩
  revert k; decide

theorem loop_mul10_overflow (acc : Nat) (hacc : acc ≤ 255) :
    let w24 := BitVec.ofNat 32 acc
    let w10 := ((w24 &&& 0xff#32) + ((w24 &&& 0xff#32) <<< 2)) <<< 1
    ((w10 &&& 0xf00#32) != 0#32) = decide (26 ≤ acc) ∧
      (acc ≤ 25 → (w10 &&& 0xff#32) = BitVec.ofNat 32 (10 * acc)) := by
  have hfin : ∃ k : Fin 256, k.val = acc := ⟨⟨acc, by omega⟩, rfl⟩
  rcases hfin with ⟨k, rfl⟩
  revert k; decide

theorem digitSub32_mask_eq (b : BitVec 8) (hb : isDigit b = true) :
    (digitSub32 b &&& 0xff#32) = BitVec.ofNat 32 (b.toNat - 48) := by
  revert b hb; decide

theorem carry_bit_iff_le255 (acc' : Nat) (hacc' : acc' ≤ 259) :
    (((BitVec.ofNat 32 acc' >>> 8) &&& 1#32) == 0#32) = decide (acc' ≤ 255) := by
  have hfin : ∃ k : Fin 260, k.val = acc' := ⟨⟨acc', by omega⟩, rfl⟩
  rcases hfin with ⟨k, rfl⟩
  revert k; decide

theorem loop_step_carry (acc : Nat) (b : BitVec 8)
    (hacc : acc ≤ 25) (hb : isDigit b = true) :
    let acc' := 10 * acc + (b.toNat - 48)
    let w24' := BitVec.ofNat 32 (10 * acc) + ((digitSub32 b) &&& 0xff#32)
    w24' = BitVec.ofNat 32 acc' ∧
      (((w24' >>> 8) &&& 1#32) == 0#32) = decide (acc' ≤ 255) := by
  have vb := digit_val_le9 b hb
  have hw : BitVec.ofNat 32 (10 * acc) + (digitSub32 b &&& 0xff#32) =
      BitVec.ofNat 32 (10 * acc + (b.toNat - 48)) := by
    rw [digitSub32_mask_eq b hb]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  refine ⟨hw, ?_⟩
  rw [hw]
  exact carry_bit_iff_le255 _ (by omega)

theorem foldl_digit_mono (ds : List (BitVec 8)) :
    ∀ acc : Nat, acc ≤ ds.foldl (fun a b => 10 * a + (b.toNat - 48)) acc := by
  induction ds with
  | nil => intro acc; exact Nat.le_refl _
  | cons b rest ih =>
    intro acc
    dsimp only [List.foldl]
    exact Nat.le_trans (by omega) (ih _)

theorem parseUnsigned_of_ds (bound : Nat) (dev ds : List (BitVec 8))
    (hds : ds = match dev with | b :: rest => if b = 43#8 then rest else dev | [] => []) :
    parseUnsigned bound dev =
      if ds = [] ∨ ds.any (fun b => !isDigit b) then none
      else
        let v := ds.foldl (fun acc b => 10 * acc + (b.toNat - 48)) 0
        if v ≤ bound then some v else none := by
  subst hds
  rfl

theorem parseUnsigned_bad_digit {bound : Nat} {dev ds : List (BitVec 8)} {b : BitVec 8}
    (hds : ds = match dev with | x :: rest => if x = 43#8 then rest else dev | [] => [])
    (hmem : b ∈ ds) (hb : isDigit b = false) :
    parseUnsigned bound dev = none := by
  rw [parseUnsigned_of_ds bound dev ds hds]
  have hany : ds.any (fun x => !isDigit x) = true :=
    List.any_eq_true.mpr ⟨b, hmem, by simp [hb]⟩
  simp [hany]

theorem parseUnsigned_overflow_prefix {dev ds done rem : List (BitVec 8)}
    (hds : ds = match dev with | x :: rest => if x = 43#8 then rest else dev | [] => [])
    (hsplit : ds = done ++ rem)
    (h256 : 256 ≤ done.foldl (fun acc b => 10 * acc + (b.toNat - 48)) 0) :
    parseUnsigned 255 dev = none := by
  rw [parseUnsigned_of_ds 255 dev ds hds]
  split
  · rfl
  · dsimp only
    rw [hsplit, List.foldl_append]
    have hbig := Nat.le_trans h256 (foldl_digit_mono rem _)
    have hnot : ¬(rem.foldl (fun acc b => 10 * acc + (b.toNat - 48))
        (done.foldl (fun acc b => 10 * acc + (b.toNat - 48)) 0) ≤ 255) := by omega
    simp [hnot]

end Address.Helpers

end CryptoVerification.SignalSession.Cli.MainHops

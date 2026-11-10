/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.Repr
public import LibsignalBinary.Proofs.SpqrV1.GF.DivImpl
import GeneratedLean.LibsignalSessionCode -- shake: keep

/-!
# `<Poly>::lagrange_interpolate_complete`: Definitions and Specifications

Pure totality characterizations for `Poly.lagrangeInterpolateComplete`, separation-logic slice
focus/update lemmas for `gf16SliceAt` and `ptSliceAt`, and subroutine contracts
(`lagrangeCompleteSpec`, `lagrangeCompletePlacedSpec`) for
`<spqr::encoding::polynomial::Poly>::lagrange_interpolate_complete` (`0x61ec4`, Block `373`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Poly.LagrangeComplete

open Arm64 ProofLib
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.GF.DivImpl
open CryptoVerification.SpqrV1.Poly

abbrev lagrangeCompleteName : String :=
  "<spqr::encoding::polynomial::Poly>::lagrange_interpolate_complete"

theorem lagrangeComplete_fnOff : libsignalSessionCode.fnOff lagrangeCompleteName = 0x5cacc :=
  ls_lemma% fnOff "<spqr::encoding::polynomial::Poly>::lagrange_interpolate_complete"

/-- Own stack frame of `lagrange_interpolate_complete` (`sub sp, sp, #0x80` = 128 B) plus
`divImplStack` (`0x70` = 112 B) for the `<GF16>::div_impl` call at `0x61fdc`. -/
abbrev lagrangeCompleteStack : Nat := 0x80 + divImplStack

/-! ## Pure model characterizations (`Poly.lagrangeDenominator`, `Poly.lagrangeCompleteDivLoop`) -/

/-- Step function of `Poly.lagrangeDenominator` (`src/encoding/polynomial.rs:206–212`). -/
def denomStep (pix : GF16) (denominator : GF16) (pj : Pt) : GF16 :=
  if pix == pj.x then
    denominator
  else
    GF16.mul denominator (GF16.sub pix pj.x)

theorem lagrangeDenominator_eq_foldl (pix : GF16) (pts : List Pt) :
    Poly.lagrangeDenominator pix pts = pts.foldl (denomStep pix) GF16.ONE := rfl

/-- Total pure version of `Poly.lagrangeCompleteDivLoop` (`src/encoding/polynomial.rs:219–225`),
stepping `idx` down from `rem` to `1`. -/
def divLoopPure (pix scale : GF16) : Nat → List GF16 → List GF16
  | 0, coeffs => coeffs
  | idx + 1, coeffs =>
    let cIdx := coeffs[idx + 1]?.getD GF16.ZERO
    let cPrev := coeffs[idx]?.getD GF16.ZERO
    let negativeDelta := GF16.mul cIdx pix
    let coeffs1 := coeffs.set (idx + 1) (GF16.mul cIdx scale)
    let coeffs2 := coeffs1.set idx (GF16.add cPrev negativeDelta)
    divLoopPure pix scale idx coeffs2

@[simp]
theorem divLoopPure_length (pix scale : GF16) (rem : Nat) (coeffs : List GF16) :
    (divLoopPure pix scale rem coeffs).length = coeffs.length := by
  induction rem generalizing coeffs with
  | zero => rfl
  | succ idx ih =>
    simp only [divLoopPure]
    rw [ih]
    simp [List.length_set]

theorem lagrangeCompleteDivLoop_eq_ok (pix scale : GF16) (len j rem : Nat) (coeffs : List GF16)
    (hj : 1 ≤ j) (hsum : j + rem = len) (hlen : coeffs.length = len) :
    Poly.lagrangeCompleteDivLoop pix scale len j rem coeffs =
      .ok (divLoopPure pix scale rem coeffs) := by
  induction rem generalizing j coeffs with
  | zero =>
    simp [Poly.lagrangeCompleteDivLoop, divLoopPure]
  | succ rem' ih =>
    unfold Poly.lagrangeCompleteDivLoop divLoopPure
    have hj_le : ¬ (j > len) := by omega
    have hidx : len - j = rem' + 1 := by omega
    have hidx_ne : (rem' + 1 == 0) = false := rfl
    have hlt1 : rem' + 1 < coeffs.length := by omega
    have hlt0 : rem' < coeffs.length := by omega
    have hget1 : coeffs[rem' + 1]? = some (coeffs[rem' + 1]'hlt1) := List.getElem?_eq_getElem hlt1
    have hget0 : coeffs[rem']? = some (coeffs[rem']'hlt0) := List.getElem?_eq_getElem hlt0
    simp only [hj_le, ↓reduceIte, hidx, hidx_ne, Bool.false_eq_true, hget1, hget0, Option.getD_some,
      Nat.add_sub_cancel]
    apply ih (j + 1)
    · omega
    · omega
    · simp [List.length_set, hlen]

/-- Total pure result of `Poly.lagrangeInterpolateComplete self pts i` when `i < pts.length`. -/
def lagrangeCompletePure (self : Poly) (pts : List Pt) (i : Nat) : Poly :=
  match pts[i]? with
  | none => self
  | some pi =>
    let denominator := Poly.lagrangeDenominator pi.x pts
    let scale := GF16.div pi.y denominator
    let len := self.coefficients.length
    if len ≤ 1 then
      self
    else
      { coefficients := divLoopPure pi.x scale (len - 1) self.coefficients }

@[simp]
theorem lagrangeCompletePure_length (self : Poly) (pts : List Pt) (i : Nat) :
    (lagrangeCompletePure self pts i).coefficients.length = self.coefficients.length := by
  unfold lagrangeCompletePure
  cases pts[i]? with
  | none => rfl
  | some pi =>
    dsimp only
    split_ifs with hle
    · rfl
    · simp

theorem lagrangeInterpolateComplete_eq_ok {self : Poly} {pts : List Pt} {i : Nat}
    (hi : i < pts.length) :
    Poly.lagrangeInterpolateComplete self pts i = .ok (lagrangeCompletePure self pts i) := by
  unfold Poly.lagrangeInterpolateComplete lagrangeCompletePure
  have hpi : pts[i]? = some (pts[i]'hi) := List.getElem?_eq_getElem hi
  rw [hpi]
  dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
  split_ifs with hle
  · rfl
  · rw [lagrangeCompleteDivLoop_eq_ok _ _ self.coefficients.length 1
        (self.coefficients.length - 1) self.coefficients (by omega) (by omega) rfl]

/-! ## Separation-logic slice focus and update lemmas (`gf16SliceAt`, `ptSliceAt`) -/

/-- Context of `gf16SliceAt ptr cs` with the `k`-th element removed. -/
def gf16SliceRest (ptr : BitVec 64) : List GF16 → Nat → SepProp
  | [], _ => emp
  | _ :: cs, 0 => gf16SliceAt (ptr + 2#64) cs
  | c :: cs, k + 1 => gf16At c ptr ∗ gf16SliceRest (ptr + 2#64) cs k

/-- Focus the `k`-th `GF16` element of `gf16SliceAt ptr cs`. -/
theorem gf16SliceAt_focus {cs : List GF16} {k : Nat} (hk : k < cs.length) (ptr : BitVec 64) :
    gf16SliceAt ptr cs =
      ((ptr + BitVec.ofNat 64 (2 * k)) ↦₁₆ (cs[k]'hk).value) ∗
      gf16SliceRest ptr cs k := by
  induction cs generalizing k ptr with
  | nil => contradiction
  | cons c cs ih =>
    cases k with
    | zero =>
      simp only [gf16SliceAt, arrayAt, gf16At, gf16Stride, gf16SliceRest, Nat.mul_zero,
        BitVec.add_zero, List.getElem_cons_zero]
    | succ k' =>
      have hk' : k' < cs.length := Nat.lt_of_succ_lt_succ hk
      simp only [gf16SliceAt, arrayAt, gf16Stride, gf16SliceRest, List.getElem_cons_succ]
      have hih := ih hk' (ptr + 2#64)
      simp only [gf16SliceAt, gf16Stride] at hih
      rw [hih]
      have haddr : ptr + 2#64 + BitVec.ofNat 64 (2 * k') = ptr + BitVec.ofNat 64 (2 * (k' + 1)) := by
        rw [BitVec.add_assoc, show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl,
          ← BitVec.ofNat_add]
        congr 2
        omega
      rw [haddr]
      ac_rfl

theorem gf16SliceRest_set (ptr : BitVec 64) (cs : List GF16) (k : Nat) (v : GF16) :
    gf16SliceRest ptr (cs.set k v) k = gf16SliceRest ptr cs k := by
  induction cs generalizing k ptr with
  | nil => rfl
  | cons c cs ih =>
    cases k with
    | zero => rfl
    | succ k' =>
      simp only [List.set_cons_succ, gf16SliceRest, ih]

/-- Unfocus and update the `k`-th `GF16` element of `gf16SliceAt ptr cs` after storing `v`. -/
theorem gf16SliceAt_update {cs : List GF16} {k : Nat} (hk : k < cs.length) (ptr : BitVec 64)
    (v : BitVec 16) :
    ((ptr + BitVec.ofNat 64 (2 * k)) ↦₁₆ v) ∗ gf16SliceRest ptr cs k =
      gf16SliceAt ptr (cs.set k ⟨v⟩) := by
  have hk_set : k < (cs.set k ⟨v⟩).length := by simp [hk]
  rw [gf16SliceAt_focus hk_set ptr, gf16SliceRest_set]
  simp [List.getElem_set_self]

/-- Context of `ptSliceAt ptr pts` with the `k`-th `Pt.x` field removed. -/
def ptSliceRestX (ptr : BitVec 64) : List Pt → Nat → SepProp
  | [], _ => emp
  | pt :: pts, 0 => ((ptr + 2#64) ↦₁₆ pt.y.value) ∗ ptSliceAt (ptr + 4#64) pts
  | pt :: pts, k + 1 => ptAt pt ptr ∗ ptSliceRestX (ptr + 4#64) pts k

/-- Focus the `x` coordinate (`+0`) of the `k`-th `Pt` in `ptSliceAt ptr pts`. -/
theorem ptSliceAt_focus_x {pts : List Pt} {k : Nat} (hk : k < pts.length) (ptr : BitVec 64) :
    ptSliceAt ptr pts =
      ((ptr + BitVec.ofNat 64 (4 * k)) ↦₁₆ (pts[k]'hk).x.value) ∗
      ptSliceRestX ptr pts k := by
  induction pts generalizing k ptr with
  | nil => contradiction
  | cons pt pts ih =>
    cases k with
    | zero =>
      simp only [ptSliceAt, arrayAt, ptAt, ptStride, ptSliceRestX, Nat.mul_zero,
        BitVec.add_zero, List.getElem_cons_zero, sepConj_assoc]
    | succ k' =>
      have hk' : k' < pts.length := Nat.lt_of_succ_lt_succ hk
      simp only [ptSliceAt, arrayAt, ptStride, ptSliceRestX, List.getElem_cons_succ]
      have hih := ih hk' (ptr + 4#64)
      simp only [ptSliceAt, ptStride] at hih
      rw [hih]
      have haddr : ptr + 4#64 + BitVec.ofNat 64 (4 * k') = ptr + BitVec.ofNat 64 (4 * (k' + 1)) := by
        rw [BitVec.add_assoc, show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
          ← BitVec.ofNat_add]
        congr 2
        omega
      rw [haddr]
      ac_rfl

/-- Context of `ptSliceAt ptr pts` with the `k`-th `Pt.y` field removed. -/
def ptSliceRestY (ptr : BitVec 64) : List Pt → Nat → SepProp
  | [], _ => emp
  | pt :: pts, 0 => (ptr ↦₁₆ pt.x.value) ∗ ptSliceAt (ptr + 4#64) pts
  | pt :: pts, k + 1 => ptAt pt ptr ∗ ptSliceRestY (ptr + 4#64) pts k

/-- Focus the `y` coordinate (`+2`) of the `k`-th `Pt` in `ptSliceAt ptr pts`. -/
theorem ptSliceAt_focus_y {pts : List Pt} {k : Nat} (hk : k < pts.length) (ptr : BitVec 64) :
    ptSliceAt ptr pts =
      ((ptr + BitVec.ofNat 64 (4 * k) + 2#64) ↦₁₆ (pts[k]'hk).y.value) ∗
      ptSliceRestY ptr pts k := by
  induction pts generalizing k ptr with
  | nil => contradiction
  | cons pt pts ih =>
    cases k with
    | zero =>
      simp only [ptSliceAt, arrayAt, ptAt, ptStride, ptSliceRestY, Nat.mul_zero,
        BitVec.add_zero, List.getElem_cons_zero]
      ac_rfl
    | succ k' =>
      have hk' : k' < pts.length := Nat.lt_of_succ_lt_succ hk
      simp only [ptSliceAt, arrayAt, ptStride, ptSliceRestY, List.getElem_cons_succ]
      have hih := ih hk' (ptr + 4#64)
      simp only [ptSliceAt, ptStride] at hih
      rw [hih]
      have haddr : ptr + 4#64 + BitVec.ofNat 64 (4 * k') = ptr + BitVec.ofNat 64 (4 * (k' + 1)) := by
        rw [BitVec.add_assoc, show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
          ← BitVec.ofNat_add]
        congr 2
        omega
      rw [haddr]
      ac_rfl

/-! ## Subroutine specification (`lagrangeCompleteSpec`) -/

/-- Ghost arguments to `<spqr::encoding::polynomial::Poly>::lagrange_interpolate_complete` (`0x61ec4`). -/
structure LagrangeCompleteArgs where
  /-- Pointer `x0` to `self.coefficients` (`&mut [GF16]`). -/
  coeffsPtr : BitVec 64
  /-- Pointer `x2` to `pts` (`&[Pt]`). -/
  ptsPtr : BitVec 64
  /-- Input polynomial `self` (`x1 = self.coefficients.length`). -/
  self : Poly
  /-- Input point slice `pts` (`x3 = pts.length`). -/
  pts : List Pt
  /-- Point index `i` (`x4 = i`, with `i < pts.length`). -/
  i : Nat

/-- Specification of `<spqr::encoding::polynomial::Poly>::lagrange_interpolate_complete` (`0x61ec4`)
under `tokenInitAt b`.
Given `self.coefficients` at `(x0 = coeffsPtr, x1 = self.coefficients.length)`, `pts` at
`(x2 = ptsPtr, x3 = pts.length)`, and `x4 = i` with `i < pts.length`, mutates `self.coefficients`
in-place to `(lagrangeCompletePure self pts i).coefficients` (which equals the `.ok` result of
`Poly.lagrangeInterpolateComplete self pts i` by `lagrangeInterpolateComplete_eq_ok`). -/
def lagrangeCompleteSpec (b : BitVec 64) : Spec LagrangeCompleteArgs where
  pre := fun x s =>
    ⌜b &&& 0xfff#64 = 0#64 ∧
      s.readReg64 .x0 = x.coeffsPtr ∧
      s.readReg64 .x1 = BitVec.ofNat 64 x.self.coefficients.length ∧
      s.readReg64 .x2 = x.ptsPtr ∧
      s.readReg64 .x3 = BitVec.ofNat 64 x.pts.length ∧
      s.readReg64 .x4 = BitVec.ofNat 64 x.i ∧
      x.i < x.pts.length ∧
      2 * x.self.coefficients.length < 2 ^ 64 ∧
      4 * x.pts.length < 2 ^ 64⌝ ∗
      gf16SliceAt x.coeffsPtr x.self.coefficients ∗
      ptSliceAt x.ptsPtr x.pts ∗
      tokenInitAt b ∗
      reduceTableAt b ∗
      stackAt s.sp lagrangeCompleteStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      gf16SliceAt x.coeffsPtr (lagrangeCompletePure x.self x.pts x.i).coefficients ∗
      ptSliceAt x.ptsPtr x.pts ∗
      tokenInitAt b ∗
      reduceTableAt b ∗
      stackAt s0.sp lagrangeCompleteStack

/-- Relocatable (`[LibsignalPlacement]`) specification of
`<spqr::encoding::polynomial::Poly>::lagrange_interpolate_complete` (Block `373`). -/
def lagrangeCompletePlacedSpec [LibsignalPlacement] : Spec LagrangeCompleteArgs where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.coeffsPtr ∧
      s.readReg64 .x1 = BitVec.ofNat 64 x.self.coefficients.length ∧
      s.readReg64 .x2 = x.ptsPtr ∧
      s.readReg64 .x3 = BitVec.ofNat 64 x.pts.length ∧
      s.readReg64 .x4 = BitVec.ofNat 64 x.i ∧
      x.i < x.pts.length ∧
      2 * x.self.coefficients.length < 2 ^ 64 ∧
      4 * x.pts.length < 2 ^ 64⌝ ∗
      gf16SliceAt x.coeffsPtr x.self.coefficients ∗
      ptSliceAt x.ptsPtr x.pts ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      stackAt s.sp lagrangeCompleteStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      gf16SliceAt x.coeffsPtr (lagrangeCompletePure x.self x.pts x.i).coefficients ∗
      ptSliceAt x.ptsPtr x.pts ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      stackAt s0.sp lagrangeCompleteStack

/-! ## Pure arithmetic, bitvector, and stack helpers -/

theorem aligned_86bd8 (b : BitVec 64) (hb : b &&& 0xfff#64 = 0#64) :
    MemWidth.isAligned .W32 (b + bv% (ls_xref% 0x5e628 0x5e62c)) = true := by
  simp only [MemWidth.isAligned, beq_iff_eq]
  revert hb; bv_bits

theorem ptr_add_four_mul_ne (ptr : BitVec 64) {j n : Nat} (hjn : j < n) (hn : n < 2 ^ 62) :
    ptr + BitVec.ofNat 64 (4 * j) ≠ ptr + BitVec.ofNat 64 (4 * n) := by
  intro h
  have h1 : BitVec.ofNat 64 (4 * j) = BitVec.ofNat 64 (4 * n) := by
    have := congrArg (fun x => x - ptr) h
    simpa [BitVec.add_sub_cancel] using this
  have h2 := congrArg BitVec.toNat h1
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 4 * j < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 4 * n < 2 ^ 64)] at h2
  omega

theorem ptr_add_four_step (ptr : BitVec 64) (j : Nat) :
    ptr + BitVec.ofNat 64 (4 * j) + 4#64 = ptr + BitVec.ofNat 64 (4 * (j + 1)) := by
  rw [BitVec.add_assoc, show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_add]
  congr 2

theorem ptr_sub_two_step (ptr : BitVec 64) (rem : Nat) :
    ptr + BitVec.ofNat 64 (2 * (rem + 1)) + 0xfffffffffffffffe#64 =
      ptr + BitVec.ofNat 64 (2 * rem) := by
  have h1 : BitVec.ofNat 64 (2 * (rem + 1)) = BitVec.ofNat 64 (2 * rem) + 2#64 := by
    rw [show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, ← BitVec.ofNat_add]
    congr 1
  rw [h1, BitVec.add_assoc ptr, BitVec.add_assoc (BitVec.ofNat 64 (2 * rem)),
    show (2#64 : BitVec 64) + 0xfffffffffffffffe#64 = 0#64 from rfl, BitVec.add_zero]

theorem lsl_two_eq_four_mul (n : Nat) :
    (BitVec.ofNat 64 n) <<< 2#64 = BitVec.ofNat 64 (4 * n) := by
  change (BitVec.ofNat 64 n) <<< 2 = BitVec.ofNat 64 (4 * n)
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_mul_mod, Nat.mul_comm n]

theorem lsl_one_eq_two_mul (n : Nat) :
    (BitVec.ofNat 64 n) <<< 1#64 = BitVec.ofNat 64 (2 * n) := by
  change (BitVec.ofNat 64 n) <<< 1 = BitVec.ofNat 64 (2 * n)
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_mul_mod, Nat.mul_comm n]

theorem gf16_beq_iff (x y : GF16) :
    (x == y) = (x.value == y.value) := by
  cases x; cases y; simp

theorem zext32_64_eq_iff (u v : BitVec 16) :
    (BitVec.zeroExtend 32 (BitVec.zeroExtend 64 u) ==
     BitVec.zeroExtend 32 (BitVec.zeroExtend 64 v)) = (u == v) := by
  cases h : u == v <;> simp_all [beq_iff_eq]
  · intro heq; apply h; bv_bits

theorem eor_zext_eq_gf16_add (u v : BitVec 16) :
    BitVec.zeroExtend 64
      (BitVec.zeroExtend 32 (BitVec.zeroExtend 64 u) ^^^
       BitVec.zeroExtend 32 (BitVec.zeroExtend 64 v)) =
      BitVec.zeroExtend 64 (GF16.add ⟨u⟩ ⟨v⟩).value := by
  change BitVec.zeroExtend 64
      (BitVec.zeroExtend 32 (BitVec.zeroExtend 64 u) ^^^
       BitVec.zeroExtend 32 (BitVec.zeroExtend 64 v)) =
      BitVec.zeroExtend 64 (u ^^^ v)
  bv_bits

theorem truncate16_eor_zext_eq (u v : BitVec 16) :
    BitVec.truncate 16
      (BitVec.zeroExtend 64
        (BitVec.zeroExtend 32 (BitVec.zeroExtend 64 u) ^^^
         BitVec.zeroExtend 32 (BitVec.zeroExtend 64 v))) = u ^^^ v := by
  bv_bits

theorem truncate16_zext64 (u : BitVec 16) :
    BitVec.truncate 16 (BitVec.zeroExtend 64 u) = u := by
  bv_bits

theorem zext64_zext32_zext64 (u : BitVec 16) :
    BitVec.zeroExtend 64 (BitVec.zeroExtend 32 (BitVec.zeroExtend 64 u)) =
      BitVec.zeroExtend 64 u := by
  bv_bits

/-- Split `stackAt sp lagrangeCompleteStack` into the callee frame `stackAt (sp - 128#64) divImplStack`
and the 128-byte own frame of `lagrange_interpolate_complete`. -/
theorem stackAt_lagrangeComplete_split (sp : BitVec 64) :
    stackAt sp lagrangeCompleteStack =
      stackAt (sp - 128#64) divImplStack ∗ memRegion (sp - 128#64) 16 ∗
      (∃∗ s112 : BitVec 16, (sp - 112#64) ↦₁₆ s112) ∗ memRegion (sp - 110#64) 6 ∗
      (∃∗ s104 : BitVec 16, (sp - 104#64) ↦₁₆ s104) ∗ memRegion (sp - 102#64) 6 ∗
      (∃∗ s29 : BitVec 64, (sp - 96#64) ↦₆₄ s29) ∗ (∃∗ s30 : BitVec 64, (sp - 88#64) ↦₆₄ s30) ∗
      (∃∗ s28 : BitVec 64, (sp - 80#64) ↦₆₄ s28) ∗ (∃∗ s27 : BitVec 64, (sp - 72#64) ↦₆₄ s27) ∗
      (∃∗ s26 : BitVec 64, (sp - 64#64) ↦₆₄ s26) ∗ (∃∗ s25 : BitVec 64, (sp - 56#64) ↦₆₄ s25) ∗
      (∃∗ s24 : BitVec 64, (sp - 48#64) ↦₆₄ s24) ∗ (∃∗ s23 : BitVec 64, (sp - 40#64) ↦₆₄ s23) ∗
      (∃∗ s22 : BitVec 64, (sp - 32#64) ↦₆₄ s22) ∗ (∃∗ s21 : BitVec 64, (sp - 24#64) ↦₆₄ s21) ∗
      (∃∗ s20 : BitVec 64, (sp - 16#64) ↦₆₄ s20) ∗ (∃∗ s19 : BitVec 64, (sp - 8#64) ↦₆₄ s19) := by
  have hbot : sp - BitVec.ofNat 64 (0x80 + divImplStack) = sp - 128#64 - BitVec.ofNat 64 divImplStack := by
    rw [BitVec.sub_sub, ← BitVec.ofNat_add]
  show stackAt sp (0x80 + divImplStack) = _
  rw [ProofLib.stackAt_split_bottom sp 0x80 divImplStack (by decide), hbot]
  simp only [stackAt]
  rw [show BitVec.ofNat 64 0x80 = 128#64 from rfl,
      ProofLib.memRegion_split' (b := sp - 128#64) (n := 16) (k := 112) (b' := sp - 112#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 112#64) (n := 2) (k := 110) (b' := sp - 110#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 110#64) (n := 6) (k := 104) (b' := sp - 104#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 104#64) (n := 2) (k := 102) (b' := sp - 102#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 102#64) (n := 6) (k := 96) (b' := sp - 96#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 96#64) (n := 8) (k := 88) (b' := sp - 88#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 88#64) (n := 8) (k := 80) (b' := sp - 80#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 80#64) (n := 8) (k := 72) (b' := sp - 72#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 72#64) (n := 8) (k := 64) (b' := sp - 64#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 64#64) (n := 8) (k := 56) (b' := sp - 56#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 56#64) (n := 8) (k := 48) (b' := sp - 48#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 48#64) (n := 8) (k := 40) (b' := sp - 40#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 40#64) (n := 8) (k := 32) (b' := sp - 32#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 32#64) (n := 8) (k := 24) (b' := sp - 24#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 24#64) (n := 8) (k := 16) (b' := sp - 16#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 16#64) (n := 8) (k := 8) (b' := sp - 8#64) rfl (by bv_arith) (by decide),
      memRegion_two (sp - 112#64), memRegion_two (sp - 104#64),
      memRegion_eight (sp - 96#64), memRegion_eight (sp - 88#64),
      memRegion_eight (sp - 80#64), memRegion_eight (sp - 72#64),
      memRegion_eight (sp - 64#64), memRegion_eight (sp - 56#64),
      memRegion_eight (sp - 48#64), memRegion_eight (sp - 40#64),
      memRegion_eight (sp - 32#64), memRegion_eight (sp - 24#64),
      memRegion_eight (sp - 16#64), memRegion_eight (sp - 8#64)]

theorem stackAt_lagrangeComplete_merge
    (sp sp' : BitVec 64) (s112 s104 : BitVec 16)
    (s29 s30 s28 s27 s26 s25 s24 s23 s22 s21 s20 s19 : BitVec 64)
    (hsp : sp' = sp - 128#64) :
    stackAt sp' divImplStack ∗ memRegion (sp - 128#64) 16 ∗
      ((sp - 112#64) ↦₁₆ s112) ∗ memRegion (sp - 110#64) 6 ∗
      ((sp - 104#64) ↦₁₆ s104) ∗ memRegion (sp - 102#64) 6 ∗
      ((sp - 96#64) ↦₆₄ s29) ∗ ((sp - 88#64) ↦₆₄ s30) ∗
      ((sp - 80#64) ↦₆₄ s28) ∗ ((sp - 72#64) ↦₆₄ s27) ∗
      ((sp - 64#64) ↦₆₄ s26) ∗ ((sp - 56#64) ↦₆₄ s25) ∗
      ((sp - 48#64) ↦₆₄ s24) ∗ ((sp - 40#64) ↦₆₄ s23) ∗
      ((sp - 32#64) ↦₆₄ s22) ∗ ((sp - 24#64) ↦₆₄ s21) ∗
      ((sp - 16#64) ↦₆₄ s20) ∗ ((sp - 8#64) ↦₆₄ s19) ⊢
      stackAt sp lagrangeCompleteStack := by
  subst hsp; rw [stackAt_lagrangeComplete_split sp]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono (Entails.sepExists_intro s112) (sepConj_mono_right ?_)))
  refine sepConj_mono (Entails.sepExists_intro s104) (sepConj_mono_right ?_)
  refine sepConj_mono (Entails.sepExists_intro s29) (sepConj_mono (Entails.sepExists_intro s30) ?_)
  refine sepConj_mono (Entails.sepExists_intro s28) (sepConj_mono (Entails.sepExists_intro s27) ?_)
  refine sepConj_mono (Entails.sepExists_intro s26) (sepConj_mono (Entails.sepExists_intro s25) ?_)
  refine sepConj_mono (Entails.sepExists_intro s24) (sepConj_mono (Entails.sepExists_intro s23) ?_)
  refine sepConj_mono (Entails.sepExists_intro s22) (sepConj_mono (Entails.sepExists_intro s21) ?_)
  exact sepConj_mono (Entails.sepExists_intro s20) (Entails.sepExists_intro s19)

theorem ptr_sub_four_mul_ne_zero (ptr : BitVec 64) {j n : Nat} (hjn : j < n) (hn : 4 * n < 2 ^ 64) :
    (ptr + BitVec.ofNat 64 (4 * j) - (ptr + BitVec.ofNat 64 (4 * n)) == 0#64) = false ∧
    (ptr + BitVec.ofNat 64 (4 * j) == ptr + BitVec.ofNat 64 (4 * n)) = false := by
  have hne := ptr_add_four_mul_ne ptr hjn (by omega)
  have hsub : ptr + BitVec.ofNat 64 (4 * j) - (ptr + BitVec.ofNat 64 (4 * n)) ≠ 0#64 := by
    intro h0; apply hne
    have := congrArg (· + (ptr + BitVec.ofNat 64 (4 * n))) h0
    simpa [BitVec.sub_add_cancel] using this
  simp [hne, hsub]

theorem cmp32_zext16_eq_zero (u v : BitVec 16) (h : u = v) :
    (BitVec.zeroExtend 32 (BitVec.zeroExtend 64 u) -
     BitVec.zeroExtend 32 (BitVec.zeroExtend 64 v) == 0#32) = true ∧
    (BitVec.zeroExtend 32 u - BitVec.zeroExtend 32 v == 0#32) = true ∧
    (BitVec.zeroExtend 32 (BitVec.zeroExtend 64 u) ==
     BitVec.zeroExtend 32 (BitVec.zeroExtend 64 v)) = true ∧
    (BitVec.zeroExtend 32 u == BitVec.zeroExtend 32 v) = true := by
  subst h; simp

theorem cmp32_zext16_ne_zero (u v : BitVec 16) (h : u ≠ v) :
    (BitVec.zeroExtend 32 (BitVec.zeroExtend 64 u) -
     BitVec.zeroExtend 32 (BitVec.zeroExtend 64 v) == 0#32) = false ∧
    (BitVec.zeroExtend 32 u - BitVec.zeroExtend 32 v == 0#32) = false ∧
    (BitVec.zeroExtend 32 (BitVec.zeroExtend 64 u) ==
     BitVec.zeroExtend 32 (BitVec.zeroExtend 64 v)) = false ∧
    (BitVec.zeroExtend 32 u == BitVec.zeroExtend 32 v) = false := by
  have h1 : BitVec.zeroExtend 32 u ≠ BitVec.zeroExtend 32 v := by
    intro heq; apply h; revert heq; bv_bits
  have h2 : BitVec.zeroExtend 32 u - BitVec.zeroExtend 32 v ≠ 0#32 := by
    intro hsub; apply h1
    have := congrArg (· + BitVec.zeroExtend 32 v) hsub
    simpa [BitVec.sub_add_cancel] using this
  have h3 : BitVec.zeroExtend 32 (BitVec.zeroExtend 64 u) = BitVec.zeroExtend 32 u := by bv_bits
  have h4 : BitVec.zeroExtend 32 (BitVec.zeroExtend 64 v) = BitVec.zeroExtend 32 v := by bv_bits
  simp [h1, h2, h3, h4]

theorem perm_denom_pre (P T R F : SepProp) :
    R ∗ T ∗ P ∗ F = P ∗ T ∗ R ∗ F := by
  rw [← sepConj_assoc R, sepConj_comm R T, sepConj_assoc T,
      ← sepConj_assoc R, sepConj_comm R P, sepConj_assoc P,
      ← sepConj_assoc T, sepConj_comm T P, sepConj_assoc P]

theorem bv_sub_one_succ (rem : Nat) (hrem : rem + 2 < 2 ^ 64) :
    BitVec.ofNat 64 (rem + 1 + 1) - 1#64 = BitVec.ofNat 64 (rem + 1) ∧
    (BitVec.ofNat 64 (rem + 1 + 1) - 1#64 == 0#64) = false ∧
    (BitVec.ofNat 64 (rem + 1 + 1) == 1#64) = false := by
  have h1 : BitVec.ofNat 64 (rem + 1 + 1) - 1#64 = BitVec.ofNat 64 (rem + 1) := by
    rw [show (rem + 1 + 1 : Nat) = (rem + 1) + 1 from rfl,
      BitVec.ofNat_add, show BitVec.ofNat 64 1 = 1#64 from rfl, BitVec.add_sub_cancel]
  have h2 : BitVec.ofNat 64 (rem + 1) ≠ 0#64 := by
    intro h0; have := congrArg BitVec.toNat h0
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : rem + 1 < 2 ^ 64)] at this; omega
  have h3 : BitVec.ofNat 64 (rem + 1 + 1) ≠ 1#64 := by
    intro h1'; have := congrArg (· - 1#64) h1'; rw [h1, BitVec.sub_self] at this; exact h2 this
  rw [h1]; simp [h2, h3]

theorem divLoop_step_eq (pix scale : GF16) (rem : Nat) (cs : List GF16)
    (hrem : rem + 1 < cs.length) :
    (let cs1 := cs.set (rem + 1) ⟨unaccelerated.mul (cs[rem + 1]'hrem).value scale.value⟩
     have hrem0 : rem < cs1.length := by simp [cs1, List.length_set]; omega
     cs1.set rem ⟨(cs1[rem]'hrem0).value ^^^ unaccelerated.mul (cs[rem + 1]'hrem).value pix.value⟩) =
    (let cIdx := cs[rem + 1]?.getD GF16.ZERO
     let cPrev := cs[rem]?.getD GF16.ZERO
     let negativeDelta := GF16.mul cIdx pix
     let coeffs1 := cs.set (rem + 1) (GF16.mul cIdx scale)
     coeffs1.set rem (GF16.add cPrev negativeDelta)) := by
  have hrem0' : rem < cs.length := by omega
  have hget1 : cs[rem + 1]? = some (cs[rem + 1]'hrem) := List.getElem?_eq_getElem hrem
  have hget0 : cs[rem]? = some (cs[rem]'hrem0') := List.getElem?_eq_getElem hrem0'
  dsimp only
  simp only [hget1, hget0, Option.getD_some, List.getElem_set_ne (by omega : rem + 1 ≠ rem)]
  rfl

theorem perm_div_pre (P T R F : SepProp) :
    R ∗ T ∗ P ∗ F = P ∗ T ∗ R ∗ F :=
  perm_denom_pre P T R F

theorem gf16SliceAt_focus_assoc {cs : List GF16} {k : Nat} (hk : k < cs.length)
    (ptr : BitVec 64) (R : SepProp) :
    gf16SliceAt ptr cs ∗ R =
      ((ptr + BitVec.ofNat 64 (2 * k)) ↦₁₆ (cs[k]'hk).value) ∗ gf16SliceRest ptr cs k ∗ R := by
  rw [gf16SliceAt_focus hk ptr, sepConj_assoc]

theorem gf16SliceAt_update_assoc {cs : List GF16} {k : Nat} (hk : k < cs.length)
    (ptr : BitVec 64) (v : BitVec 16) (R : SepProp) :
    ((ptr + BitVec.ofNat 64 (2 * k)) ↦₁₆ v) ∗ gf16SliceRest ptr cs k ∗ R =
      gf16SliceAt ptr (cs.set k ⟨v⟩) ∗ R := by
  rw [← sepConj_assoc, gf16SliceAt_update hk ptr]

theorem gf16SliceAt_update_one_assoc {cs : List GF16} (hk : 1 < cs.length)
    (ptr : BitVec 64) (v : BitVec 16) (R : SepProp) :
    ((ptr + 2#64) ↦₁₆ v) ∗ gf16SliceRest ptr cs 1 ∗ R =
      gf16SliceAt ptr (cs.set 1 ⟨v⟩) ∗ R :=
  gf16SliceAt_update_assoc hk ptr v R

end CryptoVerification.SpqrV1.Poly.LagrangeComplete

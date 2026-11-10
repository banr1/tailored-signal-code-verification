/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOne
public import LibsignalBinary.Proofs.SpqrV1.GF.Mul2U16
public import LibsignalBinary.Proofs.SpqrV1.Poly.Repr
import GeneratedLean.LibsignalSessionCode -- shake: keep

/-!
# `<spqr::encoding::polynomial::Poly>::compute_at`: Definitions and Specifications

Pure totality (`computeAtPure`), binary and `[LibsignalPlacement]` specifications (`computeAtSpec`,
`computeAtPlacedSpec`), and specialized `RawVec<GF16>::grow_one` contracts for `Poly::compute_at`
(`0x61914`, Block `371`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Poly.ComputeAt

open Arm64 ProofLib
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.GF.UnacceleratedMul

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

abbrev computeAtName : String :=
  "<spqr::encoding::polynomial::Poly>::compute_at"

theorem computeAt_fnOff : libsignalSessionCode.fnOff computeAtName = 0x5c51c :=
  ls_lemma% fnOff "<spqr::encoding::polynomial::Poly>::compute_at"

/-! ## Pure Totality & Loop Characterization -/

/-- Pure total version of `Poly.computeAtPowersLoop`. -/
def powersLoopPure : Nat → Nat → List GF16 → List GF16
  | _, 0, xs => xs
  | i, rem + 1, xs =>
    let a := xs[i / 2]?.getD GF16.ZERO
    let b := xs[(i / 2) + (i % 2)]?.getD GF16.ZERO
    powersLoopPure (i + 1) rem (xs ++ [GF16.mul a b])

@[simp]
theorem powersLoopPure_length (i rem : Nat) (xs : List GF16) :
    (powersLoopPure i rem xs).length = xs.length + rem := by
  induction rem generalizing i xs with
  | zero => simp [powersLoopPure]
  | succ rem ih =>
    simp only [powersLoopPure, ih, List.length_append, List.length_singleton]
    omega

theorem computeAtPowersLoop_eq_ok :
    ∀ (rem i : Nat) (xs : List GF16),
      2 ≤ i → xs.length = i →
      Poly.computeAtPowersLoop i rem xs = .ok (powersLoopPure i rem xs)
  | 0, _, _, _, _ => rfl
  | rem + 1, i, xs, hi, hlen => by
    have h1 : i / 2 < xs.length := by omega
    have h2 : (i / 2) + (i % 2) < xs.length := by omega
    have ha : xs[i / 2]? = some (xs[i / 2]'h1) := List.getElem?_eq_getElem h1
    have hb : xs[(i / 2) + (i % 2)]? = some (xs[(i / 2) + (i % 2)]'h2) := List.getElem?_eq_getElem h2
    simp only [Poly.computeAtPowersLoop, powersLoopPure, ha, hb, Option.getD_some]
    apply computeAtPowersLoop_eq_ok rem (i + 1) _ (by omega)
    simp [hlen]

/-- Pure power table `[1, x, x^2, ..., x^(max 1 (len - 1))]` built by `Poly.computeAt`. -/
def computeAtPowersPure (len : Nat) (x : GF16) : List GF16 :=
  let xs0 : List GF16 := [GF16.ONE, x]
  if len ≤ 2 then xs0 else powersLoopPure 2 (len - 2) xs0

@[simp]
theorem computeAtPowersPure_length (len : Nat) (x : GF16) :
    (computeAtPowersPure len x).length = max 2 len := by
  dsimp [computeAtPowersPure]
  split <;> simp <;> omega

theorem computeAtPowersPure_of_le_two {len : Nat} (h : len ≤ 2) (x : GF16) :
    computeAtPowersPure len x = [GF16.ONE, x] := by
  simp [computeAtPowersPure, h]

theorem computeAtPowersPure_of_gt_two {len : Nat} (h : 2 < len) (x : GF16) :
    computeAtPowersPure len x = powersLoopPure 2 (len - 2) [GF16.ONE, x] := by
  have hle : ¬ len ≤ 2 := by omega
  simp [computeAtPowersPure, hle]

/-- Pure total version of `Poly.computeAt`. -/
def computeAtPure (self : Poly) (x : GF16) : GF16 :=
  let xs := computeAtPowersPure self.coefficients.length x
  (self.coefficients.zip xs).foldl (fun out (a, b) => GF16.add out (GF16.mul a b)) GF16.ZERO

theorem computeAt_eq_ok (self : Poly) (x : GF16) :
    self.computeAt x = .ok (computeAtPure self x) := by
  unfold Poly.computeAt computeAtPure computeAtPowersPure
  dsimp only
  split
  · rfl
  · rw [computeAtPowersLoop_eq_ok (self.coefficients.length - 2) 2 [GF16.ONE, x] (by decide) rfl]
    rfl

/-- Indexed tail-recursive version of the dot-product loop in `Poly.computeAt`. -/
def dotLoopPure : Nat → Nat → List GF16 → List GF16 → GF16 → GF16
  | _, 0, _, _, acc => acc
  | k, r + 1, coeffs, xs, acc =>
    let a := coeffs[k]?.getD GF16.ZERO
    let b := xs[k]?.getD GF16.ZERO
    dotLoopPure (k + 1) r coeffs xs (GF16.add acc (GF16.mul a b))

theorem powersLoopPure_succ (i rem : Nat) (xs : List GF16)
    (h1 : i / 2 < xs.length) (h2 : (i / 2) + (i % 2) < xs.length) :
    powersLoopPure i (rem + 1) xs =
      powersLoopPure (i + 1) rem (xs ++ [GF16.mul (xs[i / 2]'h1) (xs[(i / 2) + (i % 2)]'h2)]) := by
  have ha : xs[i / 2]? = some (xs[i / 2]'h1) := List.getElem?_eq_getElem h1
  have hb : xs[(i / 2) + (i % 2)]? = some (xs[(i / 2) + (i % 2)]'h2) := List.getElem?_eq_getElem h2
  simp only [powersLoopPure, ha, hb, Option.getD_some]

theorem dotLoopPure_succ (k rem : Nat) (coeffs xs : List GF16) (acc : GF16)
    (hkc : k < coeffs.length) (hkx : k < xs.length) :
    dotLoopPure k (rem + 1) coeffs xs acc =
      dotLoopPure (k + 1) rem coeffs xs (GF16.add acc (GF16.mul (coeffs[k]'hkc) (xs[k]'hkx))) := by
  have hc : coeffs[k]? = some (coeffs[k]'hkc) := List.getElem?_eq_getElem hkc
  have hx : xs[k]? = some (xs[k]'hkx) := List.getElem?_eq_getElem hkx
  simp only [dotLoopPure, hc, hx, Option.getD_some]

theorem dotLoopPure_eq_foldl_zip_drop :
    ∀ (rem k : Nat) (coeffs xs : List GF16) (acc : GF16),
      k + rem = coeffs.length → coeffs.length ≤ xs.length →
      dotLoopPure k rem coeffs xs acc =
        ((coeffs.drop k).zip (xs.drop k)).foldl
          (fun out (a, b) => GF16.add out (GF16.mul a b)) acc
  | 0, k, coeffs, xs, acc, hk, _ => by
    have hk_eq : k = coeffs.length := by omega
    subst hk_eq
    simp [dotLoopPure]
  | r + 1, k, coeffs, xs, acc, hk, hle => by
    have hkc : k < coeffs.length := by omega
    have hkx : k < xs.length := by omega
    have hc : coeffs[k]? = some (coeffs[k]'hkc) := List.getElem?_eq_getElem hkc
    have hx : xs[k]? = some (xs[k]'hkx) := List.getElem?_eq_getElem hkx
    have hdrop_c : coeffs.drop k = (coeffs[k]'hkc) :: coeffs.drop (k + 1) :=
      List.drop_eq_getElem_cons hkc
    have hdrop_x : xs.drop k = (xs[k]'hkx) :: xs.drop (k + 1) :=
      List.drop_eq_getElem_cons hkx
    simp only [dotLoopPure, hc, hx, Option.getD_some, hdrop_c, hdrop_x,
      List.zip_cons_cons, List.foldl_cons]
    exact dotLoopPure_eq_foldl_zip_drop r (k + 1) coeffs xs _ (by omega) hle

theorem computeAtPure_eq_dotLoopPure (self : Poly) (x : GF16) :
    computeAtPure self x =
      dotLoopPure 0 self.coefficients.length self.coefficients
        (computeAtPowersPure self.coefficients.length x) GF16.ZERO := by
  have hle : self.coefficients.length ≤ (computeAtPowersPure self.coefficients.length x).length := by
    rw [computeAtPowersPure_length]; omega
  rw [dotLoopPure_eq_foldl_zip_drop self.coefficients.length 0 _ _ _ (by omega) hle]
  simp [computeAtPure]

theorem computeAtPure_nil (x : GF16) :
    computeAtPure ⟨[]⟩ x = GF16.ZERO := by
  rfl

/-! ## Binary Contract (`0x61914`) -/

/-- Stack requirement for `Poly::compute_at`:
144 bytes local frame + `growOneStack` (`4208` bytes for `RawVec<GF16>::grow_one`) = `4352` bytes. -/
abbrev computeAtStack : Nat := 144 + growOneStack

/-- Ghost arguments for `<spqr::encoding::polynomial::Poly>::compute_at` (`0x61914`).
In the compiled binary, `&Poly` is passed by its data pointer (`x0 = p_coeffs`) and length
(`x1 = poly.coefficients.length`), and `x : GF16` is passed in `w2`. -/
structure ComputeAtArgs where
  p_coeffs : BitVec 64
  poly : Poly
  x : GF16
  deriving DecidableEq, Repr

def computeAtSpec (A : RustAlloc) (b : BitVec 64) : Spec ComputeAtArgs where
  pre := fun args s =>
    ⌜s.readReg64 .x0 = args.p_coeffs ∧
      s.readReg64 .x1 = BitVec.ofNat 64 args.poly.coefficients.length ∧
      BitVec.truncate 16 (s.readReg64 .x2) = args.x.value ∧
      2 * args.poly.coefficients.length + 2 ≤ 2 ^ 63⌝ ∗
    gf16SliceAt args.p_coeffs args.poly.coefficients ∗
    tokenInitAt b ∗
    reduceTableAt b ∗
    A.pool ∗
    stackAt s.sp computeAtStack
  post := fun args s0 sf =>
    ⌜sf.trace = s0.trace ∧
      BitVec.truncate 16 (sf.readReg64 .x0) = (computeAtPure args.poly args.x).value⌝ ∗
    gf16SliceAt args.p_coeffs args.poly.coefficients ∗
    tokenInitAt b ∗
    reduceTableAt b ∗
    A.pool ∗
    stackAt s0.sp computeAtStack
  onPanic := fun _ s0 sf =>
    ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def computeAtPlacedSpec [LibsignalPlacement] (A : RustAlloc) : Spec ComputeAtArgs where
  pre := fun args s =>
    ⌜s.readReg64 .x0 = args.p_coeffs ∧
      s.readReg64 .x1 = BitVec.ofNat 64 args.poly.coefficients.length ∧
      BitVec.truncate 16 (s.readReg64 .x2) = args.x.value ∧
      2 * args.poly.coefficients.length + 2 ≤ 2 ^ 63⌝ ∗
    gf16SliceAt args.p_coeffs args.poly.coefficients ∗
    tokenInitPlacedAt ∗
    reduceTablePlacedAt ∗
    A.pool ∗
    stackAt s.sp computeAtStack
  post := fun args s0 sf =>
    ⌜sf.trace = s0.trace ∧
      BitVec.truncate 16 (sf.readReg64 .x0) = (computeAtPure args.poly args.x).value⌝ ∗
    gf16SliceAt args.p_coeffs args.poly.coefficients ∗
    tokenInitPlacedAt ∗
    reduceTablePlacedAt ∗
    A.pool ∗
    stackAt s0.sp computeAtStack
  onPanic := fun _ s0 sf =>
    ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-! ## Pure Arithmetic, Bitvector, & Stack Frame Helpers -/

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_pre (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg32 r = s.readReg32 r := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_pre (s : State) (m : Memory) (w : Width) (r : Reg) :
    (s.setMem m).readReg w r = s.readReg w r := by cases s; rfl

@[local arm64_norm, local wp_norm]
theorem ofNat_shl_one (k : Nat) :
    BitVec.ofNat 64 k <<< 1 = BitVec.ofNat 64 (2 * k) := by
  bv_omega

@[local arm64_norm, local wp_norm]
theorem ofNat_shl_one_bv (k : Nat) :
    BitVec.ofNat 64 k <<< 1#64 = BitVec.ofNat 64 (2 * k) := by
  change BitVec.ofNat 64 k <<< 1 = BitVec.ofNat 64 (2 * k)
  bv_omega

theorem ofNat_ushr_one {i : Nat} (hi : i < 2 ^ 64) :
    BitVec.ofNat 64 i >>> 1 = BitVec.ofNat 64 (i / 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hi, Nat.shiftRight_eq_div_pow, Nat.pow_one,
      Nat.mod_eq_of_lt (by omega)]

theorem ofNat_ushr_one_bv {i : Nat} (hi : i < 2 ^ 64) :
    BitVec.ofNat 64 i >>> 1#64 = BitVec.ofNat 64 (i / 2) :=
  ofNat_ushr_one hi

theorem ofNat_and_one (i : Nat) :
    BitVec.ofNat 64 i &&& 1#64 = BitVec.ofNat 64 (i % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  change (i % 2 ^ 64) &&& 1 = (i % 2) % 2 ^ 64
  rw [Nat.and_one_is_mod]
  omega

theorem ofNat_add_ofNat (a b : Nat) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  rw [BitVec.ofNat_add]

theorem ofNat_add_one (a : Nat) :
    BitVec.ofNat 64 a + 1#64 = BitVec.ofNat 64 (a + 1) := by
  rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]

theorem ofNat_sub_one_succ (r : Nat) :
    BitVec.ofNat 64 (r + 1) - 1#64 = BitVec.ofNat 64 r := by
  rw [BitVec.ofNat_add]
  bv_omega

theorem ofNat_ule_false_of_lt {m n : Nat} (hlt : m < n) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n).ule (BitVec.ofNat 64 m) = false := by
  rw [BitVec.ule_eq_decide, decide_eq_false_iff_not]
  simp only [BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (by omega : m < 2 ^ 64)]
  omega

theorem ofNat_ule_true_of_le {m n : Nat} (hle : m ≤ n) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 m).ule (BitVec.ofNat 64 n) = true := by
  rw [BitVec.ule_iff_toNat_le]
  simp only [BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (by omega : m < 2 ^ 64)]
  exact hle

theorem ofNat_beq_false_of_lt {a b : Nat} (hlt : a < b) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a == BitVec.ofNat 64 b) = false ∧
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b == 0#64) = false ∧
    (BitVec.ofNat 64 b == BitVec.ofNat 64 a) = false ∧
    (BitVec.ofNat 64 b - BitVec.ofNat 64 a == 0#64) = false := by
  have hne : BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := by
    intro h
    have ht := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt (by omega : a < 2 ^ 64)] at ht
    omega
  have hsub1 : BitVec.ofNat 64 a - BitVec.ofNat 64 b ≠ 0#64 := by
    intro h0; apply hne
    have := congrArg (· + BitVec.ofNat 64 b) h0
    simpa [BitVec.sub_add_cancel] using this
  have hsub2 : BitVec.ofNat 64 b - BitVec.ofNat 64 a ≠ 0#64 := by
    intro h0; apply hne.symm
    have := congrArg (· + BitVec.ofNat 64 a) h0
    simpa [BitVec.sub_add_cancel] using this
  simp [hne, hne.symm, hsub1, hsub2]

theorem subs_succ_one_ne_zero {r : Nat} (hr : r + 2 < 2 ^ 64) :
    (BitVec.ofNat 64 (r + 1 + 1) - 1#64 == 0#64) = false ∧
    (BitVec.ofNat 64 (r + 1 + 1) == 1#64) = false := by
  rw [ofNat_sub_one_succ (r + 1)]
  rcases ofNat_beq_false_of_lt (a := 0) (b := r + 1) (by omega) (by omega) with ⟨_, _, h1, _⟩
  rcases ofNat_beq_false_of_lt (a := 1) (b := r + 2) (by omega) hr with ⟨_, _, h2, _⟩
  exact ⟨h1, h2⟩

theorem ptr_add_two_step (ptr : BitVec 64) (k : Nat) :
    ptr + BitVec.ofNat 64 (2 * k) + 2#64 = ptr + BitVec.ofNat 64 (2 * (k + 1)) := by
  rw [BitVec.add_assoc, show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, ← BitVec.ofNat_add,
      Nat.mul_add]

@[local arm64_norm, local wp_norm]
theorem truncate16_zext64_trunc32 (x : BitVec 64) :
    BitVec.truncate 16 (BitVec.zeroExtend 64 (BitVec.truncate 32 x)) = BitVec.truncate 16 x := by
  bv_bits

@[local arm64_norm, local wp_norm]
theorem zext16_xor_trunc32 (x y : BitVec 64) :
    BitVec.zeroExtend 16 (BitVec.truncate 32 x ^^^ BitVec.truncate 32 y) =
      BitVec.truncate 16 x ^^^ BitVec.truncate 16 y := by
  ext i hi
  simp

theorem eor_gf16_add_comm (acc prod : GF16) :
    prod.value ^^^ acc.value = (GF16.add acc prod).value := by
  change prod.value ^^^ acc.value = acc.value ^^^ prod.value
  exact BitVec.xor_comm prod.value acc.value

theorem gf16SliceAt_append_singleton (ptr : BitVec 64) (xs : List GF16) (y : GF16) :
    gf16SliceAt ptr xs ∗ ((ptr + BitVec.ofNat 64 (2 * xs.length)) ↦₁₆ y.value) =
      gf16SliceAt ptr (xs ++ [y]) := by
  induction xs generalizing ptr with
  | nil =>
    simp [gf16SliceAt, arrayAt, gf16At, gf16Stride, sepConj_emp]
  | cons c cs ih =>
    simp only [gf16SliceAt, arrayAt, gf16At, gf16Stride, List.length_cons, List.cons_append]
    have haddr : ptr + BitVec.ofNat 64 (2 * (cs.length + 1)) =
        (ptr + 2#64) + BitVec.ofNat 64 (2 * cs.length) := by
      rw [BitVec.add_assoc, show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl,
          ← BitVec.ofNat_add]
      congr 2; omega
    rw [haddr, sepConj_assoc]
    have hih := ih (ptr + 2#64)
    simp only [gf16SliceAt, gf16Stride] at hih
    rw [hih]

theorem gf16SliceAt_append_singleton_assoc (ptr : BitVec 64) (xs : List GF16) (y : GF16)
    (R : SepProp) :
    gf16SliceAt ptr xs ∗ ((ptr + BitVec.ofNat 64 (2 * xs.length)) ↦₁₆ y.value) ∗ R =
      gf16SliceAt ptr (xs ++ [y]) ∗ R := by
  rw [← sepConj_assoc, gf16SliceAt_append_singleton]

theorem memRegion_two_succ (a : BitVec 64) (r : Nat) (hr : 2 * (r + 1) ≤ 2 ^ 64) :
    memRegion a (2 * (r + 1)) =
      (∃∗ v : BitVec 16, a ↦₁₆ v) ∗ memRegion (a + 2#64) (2 * r) := by
  rw [show 2 * (r + 1) = 2 + 2 * r by omega,
      memRegion_split a 2 (2 * r) (by omega),
      ProofLib.memRegion_two]

theorem pointsTo16_entails_memRegion_two (a : BitVec 64) (v : BitVec 16) :
    (a ↦₁₆ v) ⊢ memRegion a 2 := by
  rw [ProofLib.memRegion_two]
  exact Entails.sepExists_intro v

theorem gf16SliceAt_entails_memRegion (ptr : BitVec 64) (cs : List GF16)
    (h : 2 * cs.length ≤ 2 ^ 64) :
    gf16SliceAt ptr cs ⊢ memRegion ptr (2 * cs.length) := by
  induction cs generalizing ptr with
  | nil =>
    simp [gf16SliceAt, arrayAt, memRegion_zero]
    exact Entails.refl _
  | cons c cs ih =>
    simp only [gf16SliceAt, arrayAt, gf16At, gf16Stride, List.length_cons] at h ⊢
    rw [show 2 * (cs.length + 1) = 2 + 2 * cs.length by omega,
        memRegion_split ptr 2 (2 * cs.length) (by omega)]
    exact sepConj_mono (pointsTo16_entails_memRegion_two ptr c.value) (ih (ptr + 2#64) (by omega))

theorem gf16Slice2_rest4_entails_memRegion8 (p' : BitVec 64) (xs : List GF16) (hxs : xs.length = 2) :
    gf16SliceAt p' xs ∗ memRegion (p' + 4#64) 4 ⊢ memRegion p' 8 := by
  rw [show (8 : Nat) = 4 + 4 by rfl, memRegion_split p' 4 4 (by decide)]
  refine sepConj_mono ?_ (Entails.refl _)
  have h2 : 2 * xs.length = 4 := by omega
  rw [← h2]
  exact gf16SliceAt_entails_memRegion p' xs (by omega)

theorem stackAt_growOne_eq_allocHook (sp' : BitVec 64) :
    stackAt sp' growOneStack =
      stackAt (sp' - 4096#64) 112 ∗ stackAt sp' allocHookStack := by
  have hbot : sp' - BitVec.ofNat 64 (4096 + 112) =
      sp' - 4096#64 - BitVec.ofNat 64 112 := by
    rw [BitVec.sub_sub, ← BitVec.ofNat_add]
  show stackAt sp' (4096 + 112) = _
  rw [ProofLib.stackAt_split_bottom sp' 4096 112 (by decide), hbot]

theorem stackAt_computeAt_split (sp : BitVec 64) :
    stackAt sp computeAtStack =
      stackAt (sp - 144#64) growOneStack ∗
      memRegion (sp - 144#64) 8 ∗
      (∃∗ v136 : BitVec 64, (sp - 136#64) ↦₆₄ v136) ∗
      (∃∗ v128 : BitVec 64, (sp - 128#64) ↦₆₄ v128) ∗
      (∃∗ v120 : BitVec 64, (sp - 120#64) ↦₆₄ v120) ∗
      memRegion (sp - 112#64) 16 ∗
      (∃∗ s29 : BitVec 64, (sp - 96#64) ↦₆₄ s29) ∗
      (∃∗ s30 : BitVec 64, (sp - 88#64) ↦₆₄ s30) ∗
      (∃∗ s28 : BitVec 64, (sp - 80#64) ↦₆₄ s28) ∗
      (∃∗ s27 : BitVec 64, (sp - 72#64) ↦₆₄ s27) ∗
      (∃∗ s26 : BitVec 64, (sp - 64#64) ↦₆₄ s26) ∗
      (∃∗ s25 : BitVec 64, (sp - 56#64) ↦₆₄ s25) ∗
      (∃∗ s24 : BitVec 64, (sp - 48#64) ↦₆₄ s24) ∗
      (∃∗ s23 : BitVec 64, (sp - 40#64) ↦₆₄ s23) ∗
      (∃∗ s22 : BitVec 64, (sp - 32#64) ↦₆₄ s22) ∗
      (∃∗ s21 : BitVec 64, (sp - 24#64) ↦₆₄ s21) ∗
      (∃∗ s20 : BitVec 64, (sp - 16#64) ↦₆₄ s20) ∗
      (∃∗ s19 : BitVec 64, (sp - 8#64) ↦₆₄ s19) := by
  have hbot : sp - BitVec.ofNat 64 (0x90 + growOneStack) =
      sp - 144#64 - BitVec.ofNat 64 growOneStack := by
    rw [BitVec.sub_sub, ← BitVec.ofNat_add]
  show stackAt sp (0x90 + growOneStack) = _
  rw [ProofLib.stackAt_split_bottom sp 0x90 growOneStack (by decide), hbot]
  simp only [stackAt]
  rw [show BitVec.ofNat 64 0x90 = 144#64 from rfl,
      ProofLib.memRegion_split' (b := sp - 144#64) (n := 8) (k := 136)
        (b' := sp - 136#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 136#64) (n := 8) (k := 128)
        (b' := sp - 128#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 128#64) (n := 8) (k := 120)
        (b' := sp - 120#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 120#64) (n := 8) (k := 112)
        (b' := sp - 112#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 112#64) (n := 16) (k := 96)
        (b' := sp - 96#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 96#64) (n := 8) (k := 88)
        (b' := sp - 88#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 88#64) (n := 8) (k := 80)
        (b' := sp - 80#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 80#64) (n := 8) (k := 72)
        (b' := sp - 72#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 72#64) (n := 8) (k := 64)
        (b' := sp - 64#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 64#64) (n := 8) (k := 56)
        (b' := sp - 56#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 56#64) (n := 8) (k := 48)
        (b' := sp - 48#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 48#64) (n := 8) (k := 40)
        (b' := sp - 40#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 40#64) (n := 8) (k := 32)
        (b' := sp - 32#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 32#64) (n := 8) (k := 24)
        (b' := sp - 24#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 24#64) (n := 8) (k := 16)
        (b' := sp - 16#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 16#64) (n := 8) (k := 8)
        (b' := sp - 8#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_eight (sp - 136#64),
      ProofLib.memRegion_eight (sp - 128#64),
      ProofLib.memRegion_eight (sp - 120#64),
      ProofLib.memRegion_eight (sp - 96#64), ProofLib.memRegion_eight (sp - 88#64),
      ProofLib.memRegion_eight (sp - 80#64), ProofLib.memRegion_eight (sp - 72#64),
      ProofLib.memRegion_eight (sp - 64#64), ProofLib.memRegion_eight (sp - 56#64),
      ProofLib.memRegion_eight (sp - 48#64), ProofLib.memRegion_eight (sp - 40#64),
      ProofLib.memRegion_eight (sp - 32#64), ProofLib.memRegion_eight (sp - 24#64),
      ProofLib.memRegion_eight (sp - 16#64), ProofLib.memRegion_eight (sp - 8#64)]

theorem stackAt_computeAt_merge
    (sp sp' : BitVec 64)
    (v136 v128 v120 : BitVec 64)
    (s29 s30 s28 s27 s26 s25 s24 s23 s22 s21 s20 s19 : BitVec 64)
    (hsp : sp' = sp - 144#64) :
    stackAt sp' growOneStack ∗
      memRegion (sp - 144#64) 8 ∗
      ((sp - 136#64) ↦₆₄ v136) ∗
      ((sp - 128#64) ↦₆₄ v128) ∗
      ((sp - 120#64) ↦₆₄ v120) ∗
      memRegion (sp - 112#64) 16 ∗
      ((sp - 96#64) ↦₆₄ s29) ∗
      ((sp - 88#64) ↦₆₄ s30) ∗
      ((sp - 80#64) ↦₆₄ s28) ∗
      ((sp - 72#64) ↦₆₄ s27) ∗
      ((sp - 64#64) ↦₆₄ s26) ∗
      ((sp - 56#64) ↦₆₄ s25) ∗
      ((sp - 48#64) ↦₆₄ s24) ∗
      ((sp - 40#64) ↦₆₄ s23) ∗
      ((sp - 32#64) ↦₆₄ s22) ∗
      ((sp - 24#64) ↦₆₄ s21) ∗
      ((sp - 16#64) ↦₆₄ s20) ∗
      ((sp - 8#64) ↦₆₄ s19) ⊢
      stackAt sp computeAtStack := by
  subst hsp
  rw [stackAt_computeAt_split sp]
  refine sepConj_mono_right (sepConj_mono_right ?_)
  refine sepConj_mono (Entails.sepExists_intro v136) ?_
  refine sepConj_mono (Entails.sepExists_intro v128) ?_
  refine sepConj_mono (Entails.sepExists_intro v120) (sepConj_mono_right ?_)
  refine sepConj_mono (Entails.sepExists_intro s29) ?_
  refine sepConj_mono (Entails.sepExists_intro s30) ?_
  refine sepConj_mono (Entails.sepExists_intro s28) ?_
  refine sepConj_mono (Entails.sepExists_intro s27) ?_
  refine sepConj_mono (Entails.sepExists_intro s26) ?_
  refine sepConj_mono (Entails.sepExists_intro s25) ?_
  refine sepConj_mono (Entails.sepExists_intro s24) ?_
  refine sepConj_mono (Entails.sepExists_intro s23) ?_
  refine sepConj_mono (Entails.sepExists_intro s22) ?_
  refine sepConj_mono (Entails.sepExists_intro s21) ?_
  refine sepConj_mono (Entails.sepExists_intro s20) ?_
  exact Entails.sepExists_intro s19

/-! ## Callee Specs (`unaccelerated::mul` and `RawVec<GF16>::grow_one`) -/

theorem unacceleratedMul_at_computeAt (b : BitVec 64) (ext : String → Option (State → State)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr computeAtName + BitVec.ofNat 64 9104)
      (unacceleratedMulSpec b) :=
  sub_ok_at_of_fnAddr (unacceleratedMul_ok b ext) computeAtName 9104
    (by rw [computeAt_fnOff, unacceleratedMul_fnOff])

theorem fnAddr_growOneGF16_eq_computeAt (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr growOneGF16Name =
      (tripleRatchetProgAtExt b ext).fnAddr computeAtName + 18446744073709544188#64 := by
  dsimp only [tripleRatchetProgAtExt]
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      libsignalSessionCode_fnOff_0x5a818, computeAt_fnOff]
  bv_omega

/-- Specialized contract for `RawVec<GF16>::grow_one` called with `cap = 0` (`ptr = 2`). -/
def growOneGF16ZeroSpec (A : RustAlloc) : Spec (BitVec 64) where
  pre := fun v s =>
    ⌜s.readReg64 .x0 = v⌝ ∗
    (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 2#64) ∗
    A.pool ∗ stackAt s.sp growOneStack
  post := fun v s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64, ∃∗ w1 : BitVec 16, ∃∗ w0 : BitVec 16,
      ⌜p' ≠ 0#64 ∧ p'.toNat % 2 = 0⌝ ∗
      (v ↦₆₄ 4#64) ∗ ((v + 8#64) ↦₆₄ p') ∗
      A.live p' 8 2 ∗ (p' ↦₁₆ w0) ∗ ((p' + 2#64) ↦₁₆ w1) ∗
      memRegion (p' + 4#64) 4) ∗
    A.pool ∗ stackAt s0.sp growOneStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem memRegion8_split_16_16_4 (p' : BitVec 64) :
    memRegion p' 8 =
      (∃∗ w1 : BitVec 16, ∃∗ w0 : BitVec 16,
        (p' ↦₁₆ w0) ∗ ((p' + 2#64) ↦₁₆ w1) ∗ memRegion (p' + 4#64) 4) := by
  rw [show (8 : Nat) = 2 + (2 + 4) by rfl,
      memRegion_split p' 2 (2 + 4) (by decide),
      memRegion_split (p' + 2#64) 2 4 (by decide),
      ProofLib.memRegion_two p', ProofLib.memRegion_two (p' + 2#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

theorem grow_one_gf16_zero_ok_at {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr computeAtName + 18446744073709544188#64)
      (growOneGF16ZeroSpec A) := by
  rw [← fnAddr_growOneGF16_eq_computeAt b ext]
  refine subroutine_ok_outcome_intro fun v R s0 hpc hrun hpre hsp => ?_
  simp only [growOneGF16ZeroSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hx0, hmem⟩
  have hpre' : s0.mem ⊨ (growOneGF16FullSpec A).pre (v, 0#64, 2#64, []) s0 ∗ R := by
    simp only [growOneGF16FullSpec, growOneStrideFullSpec, ite_true, emp_sepConj,
      sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, rfl, by decide, by decide⟩, hmem⟩
  refine (grow_one_gf16_full_ok_ext hA).mono_outcome (v, 0#64, 2#64, []) R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    change sf.mem ⊨ (growOneGF16FullSpec A).post (v, 0#64, 2#64, []) s0 sf ∗ R at hq
    dsimp only [growOneGF16FullSpec, growOneStrideFullSpec, growOneGF16ZeroSpec] at hq ⊢
    have h4 : BitVec.ofNat 64 (max (2 * (0#64 : BitVec 64).toNat) 4) = 4#64 := rfl
    have h8 : max (2 * (0#64 : BitVec 64).toNat) 4 * 2 = 8 := rfl
    have h8' : (max (2 * (0#64 : BitVec 64).toNat) 4 - (0#64 : BitVec 64).toNat) * 2 = 8 := rfl
    have h0_2 : BitVec.ofNat 64 ([] : List (BitVec 8)).length = 0#64 := rfl
    simp only [h4, h8, h8', h0_2, pointsToBytes_nil, BitVec.add_zero, emp_sepConj,
      memRegion8_split_16_16_4, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      satisfies_pure_sepConj, satisfies_sepExists] at hq ⊢
    exact hq
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact (not_satisfies_false_sepConj hq).elim

/-- Specialized contract for `RawVec<GF16>::grow_one` called with `cap = 1` and `p0 ↦₁₆ 1#16`. -/
def growOneGF16OneSpec (A : RustAlloc) : Spec (BitVec 64 × BitVec 64) where
  pre := fun (v, p0) s =>
    ⌜s.readReg64 .x0 = v ∧ p0 ≠ 0#64⌝ ∗
    (v ↦₆₄ 1#64) ∗ ((v + 8#64) ↦₆₄ p0) ∗
    A.live p0 2 2 ∗ (p0 ↦₁₆ 1#16) ∗
    A.pool ∗ stackAt s.sp growOneStack
  post := fun (v, _) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64, ∃∗ w1 : BitVec 16,
      ⌜p' ≠ 0#64 ∧ p'.toNat % 2 = 0⌝ ∗
      (v ↦₆₄ 4#64) ∗ ((v + 8#64) ↦₆₄ p') ∗
      A.live p' 8 2 ∗ (p' ↦₁₆ 1#16) ∗ ((p' + 2#64) ↦₁₆ w1) ∗
      memRegion (p' + 4#64) 4) ∗
    A.pool ∗ stackAt s0.sp growOneStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem pointsTo16_one_eq_bytes (a : BitVec 64) :
    (a ↦₁₆ 1#16) = (a ↦ₛ [1#8, 0#8]) := by
  simp only [pointsTo16, pointsToBytes_cons, pointsToBytes_nil, sepConj_emp, BitVec.add_zero]
  rfl

theorem memRegion6_split_16_4 (p' : BitVec 64) :
    memRegion (p' + 2#64) 6 =
      (∃∗ w1 : BitVec 16, ((p' + 2#64) ↦₁₆ w1) ∗ memRegion (p' + 4#64) 4) := by
  rw [show (6 : Nat) = 2 + 4 by rfl,
      memRegion_split (p' + 2#64) 2 4 (by decide),
      ProofLib.memRegion_two (p' + 2#64)]
  simp only [sepExists_sepConj_left, BitVec.add_assoc, BitVec.reduceAdd]

theorem grow_one_gf16_one_ok_at {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr computeAtName + 18446744073709544188#64)
      (growOneGF16OneSpec A) := by
  rw [← fnAddr_growOneGF16_eq_computeAt b ext]
  refine subroutine_ok_outcome_intro fun ⟨v, p0⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [growOneGF16OneSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hp0⟩, hmem⟩
  have hpre' : s0.mem ⊨ (growOneGF16FullSpec A).pre (v, 1#64, p0, [1#8, 0#8]) s0 ∗ R := by
    simp only [growOneGF16FullSpec, growOneStrideFullSpec,
      show (1#64 : BitVec 64) = 0#64 ↔ False by decide, ite_false,
      List.length_cons, List.length_nil, ← pointsTo16_one_eq_bytes,
      sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, rfl, hp0, by decide⟩, hmem⟩
  refine (grow_one_gf16_full_ok_ext hA).mono_outcome (v, 1#64, p0, [1#8, 0#8]) R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    change sf.mem ⊨ (growOneGF16FullSpec A).post (v, 1#64, p0, [1#8, 0#8]) s0 sf ∗ R at hq
    dsimp only [growOneGF16FullSpec, growOneStrideFullSpec, growOneGF16OneSpec] at hq ⊢
    have h4 : BitVec.ofNat 64 (max (2 * (1#64 : BitVec 64).toNat) 4) = 4#64 := rfl
    have h8 : max (2 * (1#64 : BitVec 64).toNat) 4 * 2 = 8 := rfl
    have h6 : (max (2 * (1#64 : BitVec 64).toNat) 4 - (1#64 : BitVec 64).toNat) * 2 = 6 := rfl
    have hlen2 : BitVec.ofNat 64 ([1#8, 0#8] : List (BitVec 8)).length = 2#64 := rfl
    simp only [h4, h8, h6, hlen2, ← pointsTo16_one_eq_bytes,
      memRegion6_split_16_4, sepExists_sepConj_left, sepExists_sepConj_right,
      sepConj_assoc, satisfies_pure_sepConj, satisfies_sepExists] at hq ⊢
    exact hq
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact (not_satisfies_false_sepConj hq).elim

theorem grow_one_gf16_zero_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_359).rebase (blkPl_359).base H)
      (blkPl_359).base
      (withLsCodeLoaded lsmpl (growOneGF16ZeroSpec A)) := by
  refine subroutine_ok_outcome_intro fun v R s0 hpc hrun hpre hsp => ?_
  simp only [growOneGF16ZeroSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hx0, hmem⟩
  have hpre' : s0.mem ⊨ (withLsCodeLoaded lsmpl (growOneGF16FullSpec A)).pre (v, 0#64, 2#64, []) s0 ∗ R := by
    simp only [growOneGF16FullSpec, growOneStrideFullSpec, ite_true, emp_sepConj,
      sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, rfl, by decide, by decide⟩, hmem⟩
  refine (grow_one_gf16_full_placed_ok h_panic hshim halloc hrealloc).mono_outcome (v, 0#64, 2#64, []) R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    change sf.mem ⊨ (growOneGF16FullSpec A).post (v, 0#64, 2#64, []) s0 sf ∗ R at hq
    dsimp only [withLsCodeLoaded, growOneGF16FullSpec, growOneStrideFullSpec, growOneGF16ZeroSpec] at hq ⊢
    have h4 : BitVec.ofNat 64 (max (2 * (0#64 : BitVec 64).toNat) 4) = 4#64 := rfl
    have h8 : max (2 * (0#64 : BitVec 64).toNat) 4 * 2 = 8 := rfl
    have h8' : (max (2 * (0#64 : BitVec 64).toNat) 4 - (0#64 : BitVec 64).toNat) * 2 = 8 := rfl
    have h0_2 : BitVec.ofNat 64 ([] : List (BitVec 8)).length = 0#64 := rfl
    simp only [h4, h8, h8', h0_2, pointsToBytes_nil, BitVec.add_zero, emp_sepConj,
      memRegion8_split_16_16_4, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      satisfies_pure_sepConj, satisfies_sepExists] at hq ⊢
    exact hq
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact (not_satisfies_false_sepConj hq).elim

theorem grow_one_gf16_one_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_359).rebase (blkPl_359).base H)
      (blkPl_359).base
      (withLsCodeLoaded lsmpl (growOneGF16OneSpec A)) := by
  refine subroutine_ok_outcome_intro fun ⟨v, p0⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [growOneGF16OneSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hp0⟩, hmem⟩
  have hpre' : s0.mem ⊨ (withLsCodeLoaded lsmpl (growOneGF16FullSpec A)).pre (v, 1#64, p0, [1#8, 0#8]) s0 ∗ R := by
    simp only [growOneGF16FullSpec, growOneStrideFullSpec,
      show (1#64 : BitVec 64) = 0#64 ↔ False by decide, ite_false,
      List.length_cons, List.length_nil, ← pointsTo16_one_eq_bytes,
      sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, rfl, hp0, by decide⟩, hmem⟩
  refine (grow_one_gf16_full_placed_ok h_panic hshim halloc hrealloc).mono_outcome (v, 1#64, p0, [1#8, 0#8]) R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    change sf.mem ⊨ (growOneGF16FullSpec A).post (v, 1#64, p0, [1#8, 0#8]) s0 sf ∗ R at hq
    dsimp only [withLsCodeLoaded, growOneGF16FullSpec, growOneStrideFullSpec, growOneGF16OneSpec] at hq ⊢
    have h4 : BitVec.ofNat 64 (max (2 * (1#64 : BitVec 64).toNat) 4) = 4#64 := rfl
    have h8 : max (2 * (1#64 : BitVec 64).toNat) 4 * 2 = 8 := rfl
    have h6 : (max (2 * (1#64 : BitVec 64).toNat) 4 - (1#64 : BitVec 64).toNat) * 2 = 6 := rfl
    have hlen2 : BitVec.ofNat 64 ([1#8, 0#8] : List (BitVec 8)).length = 2#64 := rfl
    simp only [h4, h8, h6, hlen2, ← pointsTo16_one_eq_bytes,
      memRegion6_split_16_4, sepExists_sepConj_left, sepExists_sepConj_right,
      sepConj_assoc, satisfies_pure_sepConj, satisfies_sepExists] at hq ⊢
    exact hq
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact (not_satisfies_false_sepConj hq).elim

/-! ## Additional Pure Bitvector, Panic-Aware Call, & Frame Helpers -/

theorem len_bit62_false (n : Nat) (h : 2 * n < 2 ^ 63) :
    ((BitVec.ofNat 64 n &&& 4611686018427387904#64) != 0#64) = false := by
  rw [bne_eq_false_iff_eq]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  have h62 : n < 2 ^ 62 := by omega
  have h64 : n < 2 ^ 64 := by omega
  have hlt : (BitVec.ofNat 64 n).toNat < 2 ^ 62 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64]
    exact h62
  have hpow : (4611686018427387904#64).toNat = 2 ^ 62 := rfl
  rw [hpow]
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_and, Nat.testBit_two_pow]
  by_cases hk : 62 = k
  · subst hk
    rw [Nat.testBit_lt_two_pow hlt]
    rfl
  · simp [hk]

theorem ofNat_two_mul_toNat (n : Nat) (h : 2 * n < 2 ^ 63) :
    (BitVec.ofNat 64 (2 * n)).toNat = 2 * n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem allocFailedIn_of_trace_eq {s0 sf : State}
    (ht : sf.trace = s0.trace ++ [allocFailedEvent]) :
    allocFailedIn s0 sf := by
  unfold allocFailedIn
  rw [ht, List.drop_left]
  exact List.Mem.head []

theorem pull_pure_after_two (P1 P2 : SepProp) (φ : Prop) (Rest : SepProp) :
    P1 ∗ P2 ∗ ⌜φ⌝ ∗ Rest = ⌜φ⌝ ∗ P1 ∗ P2 ∗ Rest := by
  ac_rfl

theorem alloc_post_pos {P1 P2 Rest : SepProp} {x0 : BitVec 64} {φ : Prop} {Q : SepProp}
    (h0 : x0 = 0#64) :
    P1 ∗ P2 ∗ (if x0 = 0 then ⌜φ⌝ else Q) ∗ Rest = ⌜φ⌝ ∗ P1 ∗ P2 ∗ Rest := by
  have h0' : x0 = 0 := h0
  simp only [h0', ↓reduceIte]
  exact pull_pure_after_two P1 P2 φ Rest

theorem alloc_post_neg {P1 P2 Rest : SepProp} {x0 : BitVec 64} {φ ψ : Prop} {Q : SepProp}
    (h0 : x0 ≠ 0#64) :
    P1 ∗ P2 ∗ (if x0 = 0 then ⌜φ⌝ else ⌜ψ⌝ ∗ Q) ∗ Rest = ⌜ψ⌝ ∗ P1 ∗ P2 ∗ Q ∗ Rest := by
  have h0' : x0 ≠ 0 := h0
  simp only [h0', ↓reduceIte]
  rw [sepConj_assoc ⌜ψ⌝ Q Rest]
  exact pull_pure_after_two P1 P2 ψ (Q ∗ Rest)

theorem stackAt_growOne_merge_allocHook (sp' : BitVec 64) (P1 P2 P3 Rest : SepProp) :
    stackAt sp' allocHookStack ∗ P1 ∗ P2 ∗ P3 ∗ stackAt (sp' - 4096#64) 112 ∗ Rest =
      stackAt sp' growOneStack ∗ P1 ∗ P2 ∗ P3 ∗ Rest := by
  rw [stackAt_growOne_eq_allocHook sp']
  ac_rfl

theorem SepWPp.call_panic_to_sepWP {α : Type} {prog : Program} {entry ret_pc ret : BitVec 64}
    {s0 s : State} {spec : Spec α} {x : α} {φ : Prop} {T F P R : SepProp}
    {Q : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : s.trace = s0.trace)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_eq : ∀ sf, spec.onPanic x s sf = (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap))
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → False)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWP prog ret sf (spec.post x s sf ∗ F) Q) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R)) := by
  refine SepWPp.call_frame hcall hpc hrun hsp hlr hspec hφ hP hexit
    (fun sf _ hm => ?_)
    (fun sf hpcf hrunf hspf hcsf => SepWPp.of_sepWP_ret (hnext sf hpcf hrunf hspf hcsf))
    (fun sf R' ho hm => (hoom sf R' ho hm).elim)
  have hpan_tr : allocFailedIn s sf = allocFailedIn s0 sf := by
    unfold allocFailedIn; rw [htr]
  rw [hpan_eq sf, hpan_tr, htr, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨hpan, hm2⟩
  rw [← sepConj_assoc] at hm2
  rw [← sepConj_assoc]
  exact allowPanic_panicked (φ := allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) hpan hm2

theorem ult_max_two_false (n : Nat) (h : 2 * n + 2 ≤ 2 ^ 63) :
    (BitVec.ofNat 64 (max 2 n)).ult (BitVec.ofNat 64 n) = false := by
  have h1 : (BitVec.ofNat 64 (max 2 n)).toNat = max 2 n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h2 : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp only [BitVec.ult, h1, h2, decide_eq_false_iff_not]
  omega

theorem combine_two_gf16 (p_xs : BitVec 64) (x : GF16) (Rest : SepProp) :
    (p_xs ↦₁₆ 1#16) ∗ ((p_xs + 2#64) ↦₁₆ x.value) ∗ Rest =
      gf16SliceAt p_xs [GF16.ONE, x] ∗ Rest := by
  simp [gf16SliceAt, arrayAt, gf16At, gf16Stride, GF16.ONE, sepConj_emp, sepConj_assoc]

theorem ult_three_of_lt (n : Nat) (h : n < 3) :
    (BitVec.ofNat 64 n).ult 3#64 = true := by
  have h1 : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp only [BitVec.ult, h1, BitVec.toNat_ofNat, decide_eq_true_eq]
  omega

theorem ult_three_false_of_ge (n : Nat) (hge : 3 ≤ n) (hb : 2 * n + 2 ≤ 2 ^ 63) :
    (BitVec.ofNat 64 n).ult 3#64 = false := by
  have h1 : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp only [BitVec.ult, h1, BitVec.toNat_ofNat, decide_eq_false_iff_not]
  omega

theorem insert_emp_memRegion_after_w1 (p_xs : BitVec 64) (w1 : BitVec 16) (n : Nat)
    (hn : n ≤ 2) (Rest : SepProp) :
    ((p_xs + 2#64) ↦₁₆ w1) ∗ Rest =
      ((p_xs + 2#64) ↦₁₆ w1) ∗ memRegion (p_xs + 4#64) (2 * (n - 2)) ∗ Rest := by
  have h0 : n - 2 = 0 := by omega
  rw [h0, Nat.mul_zero, memRegion_zero, emp_sepConj]

theorem powers_to_dot_frame
    (P_pow P_136 P_128 P_120 P_tok P_red P_coeffs P_rest4 P_live P_pool P_stk P_m144 Tail : SepProp) :
    P_pow ∗ P_136 ∗ P_128 ∗ P_120 ∗ P_tok ∗ P_red ∗ P_coeffs ∗ P_rest4 ∗
      P_live ∗ P_pool ∗ P_stk ∗ P_m144 ∗ Tail =
    P_coeffs ∗ P_pow ∗ P_tok ∗ P_red ∗ P_rest4 ∗
      P_live ∗ P_pool ∗ P_stk ∗ P_m144 ∗ P_136 ∗ P_128 ∗ P_120 ∗ Tail := by
  ac_rfl

theorem powers_to_dot_ge2_frame
    (P_pow P_136 P_128 P_120 P_tok P_red P_coeffs P_live P_pool P_stk P_m144 Tail : SepProp) :
    P_pow ∗ P_136 ∗ P_128 ∗ P_120 ∗ P_tok ∗ P_red ∗ P_coeffs ∗
      P_live ∗ P_pool ∗ P_stk ∗ P_m144 ∗ Tail =
    P_coeffs ∗ P_pow ∗ P_tok ∗ P_red ∗
      P_live ∗ P_pool ∗ P_stk ∗ P_m144 ∗ P_136 ∗ P_128 ∗ P_120 ∗ Tail := by
  ac_rfl

theorem grow0_pre_split (sp0 : BitVec 64) (A : RustAlloc)
    (P_coeffs P_tok P_red P_m144 P_120 Tail : SepProp) :
    P_coeffs ∗ P_tok ∗ P_red ∗ A.pool ∗
      stackAt (sp0 - 144#64) growOneStack ∗
      P_m144 ∗
      ((sp0 - 136#64) ↦₆₄ 0#64) ∗
      ((sp0 - 128#64) ↦₆₄ 2#64) ∗
      P_120 ∗ Tail =
    (((sp0 - 136#64) ↦₆₄ 0#64) ∗
     ((sp0 - 136#64 + 8#64) ↦₆₄ 2#64) ∗
     A.pool ∗
     stackAt (sp0 - 144#64) growOneStack) ∗
    (P_coeffs ∗ P_tok ∗ P_red ∗ P_m144 ∗ P_120 ∗ Tail) := by
  have h128 : sp0 - 136#64 + 8#64 = sp0 - 128#64 := by bv_omega
  rw [h128]
  ac_rfl

theorem grow0_post_rearrange
    (P_136 P_128 P_live P_p0 P_p2 P_rest4 P_pool P_stk
     P_coeffs P_tok P_red P_m144 P_120 Tail : SepProp) :
    P_136 ∗ P_128 ∗ P_live ∗ P_p0 ∗ P_p2 ∗ P_rest4 ∗
      P_pool ∗ P_stk ∗ P_coeffs ∗ P_tok ∗ P_red ∗ P_m144 ∗ P_120 ∗ Tail =
    P_p0 ∗ P_p2 ∗ P_136 ∗ P_128 ∗ P_120 ∗
      P_tok ∗ P_red ∗ P_coeffs ∗ P_rest4 ∗
      P_live ∗ P_pool ∗ P_stk ∗ P_m144 ∗ Tail := by
  ac_rfl

theorem merge_allocHook_after_alloc (sp0 : BitVec 64)
    (P_pool P_live P_mem P_coeffs P_tok P_red Tail : SepProp) :
    P_pool ∗
      stackAt (sp0 - 144#64) allocHookStack ∗
      (P_live ∗ P_mem) ∗
      P_coeffs ∗ P_tok ∗ P_red ∗
      stackAt (sp0 - 4240#64) 112 ∗ Tail =
    P_pool ∗
      stackAt (sp0 - 144#64) growOneStack ∗
      P_live ∗ P_mem ∗
      P_coeffs ∗ P_tok ∗ P_red ∗ Tail := by
  have h4240 : sp0 - 4240#64 = sp0 - 144#64 - 4096#64 := by bv_omega
  rw [h4240, stackAt_growOne_eq_allocHook (sp0 - 144#64)]
  ac_rfl

theorem grow1_pre_split (sp0 p0 : BitVec 64) (A : RustAlloc)
    (P_stk P_live P_p0 P_coeffs P_tok P_red P_m144 P_120 Tail : SepProp) :
    A.pool ∗ P_stk ∗ P_live ∗ P_p0 ∗ P_coeffs ∗ P_tok ∗ P_red ∗ P_m144 ∗
      ((sp0 - 136#64) ↦₆₄ 1#64) ∗
      ((sp0 - 128#64) ↦₆₄ p0) ∗
      P_120 ∗ Tail =
    (((sp0 - 136#64) ↦₆₄ 1#64) ∗
     ((sp0 - 136#64 + 8#64) ↦₆₄ p0) ∗
     P_live ∗ P_p0 ∗ A.pool ∗ P_stk) ∗
    (P_coeffs ∗ P_tok ∗ P_red ∗ P_m144 ∗ P_120 ∗ Tail) := by
  have h128 : sp0 - 136#64 + 8#64 = sp0 - 128#64 := by bv_omega
  rw [h128]
  ac_rfl

theorem ge2_to_61974_rearrange
    (P_pool P_stk P_live P_p0 P_p2 P_rest P_coeffs P_tok P_red P_m144 P_136 P_128 P_120 Tail : SepProp) :
    P_pool ∗ P_stk ∗ P_live ∗ P_p0 ∗ P_p2 ∗ P_rest ∗
      P_coeffs ∗ P_tok ∗ P_red ∗ P_m144 ∗ P_136 ∗ P_128 ∗ P_120 ∗ Tail =
    P_p0 ∗ P_p2 ∗ P_rest ∗ P_136 ∗ P_128 ∗ P_120 ∗
      P_tok ∗ P_red ∗ P_coeffs ∗ P_live ∗ P_pool ∗ P_stk ∗ P_m144 ∗ Tail := by
  ac_rfl

theorem memRegion_ge2_split (p0 : BitVec 64) (n : Nat) (hge2 : 2 ≤ n)
    (hb : 2 * n + 2 ≤ 2 ^ 63) :
    memRegion p0 (2 * n) =
      (∃∗ w0 : BitVec 16, p0 ↦₁₆ w0) ∗
      (∃∗ w1 : BitVec 16, (p0 + 2#64) ↦₁₆ w1) ∗
      memRegion (p0 + 4#64) (2 * (n - 2)) := by
  rw [show 2 * n = 2 + (2 + 2 * (n - 2)) by omega,
      memRegion_split p0 2 (2 + 2 * (n - 2)) (by omega),
      memRegion_split (p0 + 2#64) 2 (2 * (n - 2)) (by omega),
      ProofLib.memRegion_two p0, ProofLib.memRegion_two (p0 + 2#64),
      BitVec.add_assoc, show (2#64 : BitVec 64) + 2#64 = 4#64 from rfl]

end CryptoVerification.SpqrV1.Poly.ComputeAt

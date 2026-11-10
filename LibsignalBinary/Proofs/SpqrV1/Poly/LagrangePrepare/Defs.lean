/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.Repr
public import LibsignalBinary.Proofs.SpqrV1.GF.Mul2U16
import GeneratedLean.LibsignalSessionCode -- shake: keep

/-!
# `<Poly>::lagrange_interpolate_prepare`: Definitions and Specifications

Pure totality characterizations, slice focus/update helpers, and subroutine specifications
(`lagrangePrepareSpec`, `lagrangePreparePlacedSpec`) for
`<spqr::encoding::polynomial::Poly>::lagrange_interpolate_prepare` (`0x61c1c`, Block `372`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Poly.LagrangePrepare

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly

abbrev lagrangePrepareName : String :=
  "<spqr::encoding::polynomial::Poly>::lagrange_interpolate_prepare"

theorem lagrangePrepare_fnOff : libsignalSessionCode.fnOff lagrangePrepareName = 0x5c824 :=
  ls_lemma% fnOff "<spqr::encoding::polynomial::Poly>::lagrange_interpolate_prepare"

gen_decodes libsignalSessionCode_tree lagrangePrepareBin [0x5c824 → 0x5cacc]

/-- Stack budget of `lagrange_interpolate_prepare` (`0x61c1c`):
`0xd0` (`208` bytes own frame) + `allocHookStack` (`4096` bytes for `__rust_alloc` / `memset`). -/
abbrev lagrangePrepareStack : Nat := 0xd0 + allocHookStack

/-! ## Pure Totality & Loop Characterization -/

/-- Pure total version of `Poly.multXdiffAssignTrailingLoop`. -/
def multXdiffLoopPure (diff : GF16) : Nat → Nat → List GF16 → List GF16
  | _, 0, coeffs => coeffs
  | i, rem + 1, coeffs =>
    let ci := coeffs[i]?.getD GF16.ZERO
    let ciPrev := coeffs[i - 1]?.getD GF16.ZERO
    let delta := GF16.mul ci diff
    let coeffs' := coeffs.set (i - 1) (GF16.sub ciPrev delta)
    multXdiffLoopPure diff (i + 1) rem coeffs'

@[simp]
theorem multXdiffLoopPure_length (diff : GF16) (i rem : Nat) (coeffs : List GF16) :
    (multXdiffLoopPure diff i rem coeffs).length = coeffs.length := by
  induction rem generalizing i coeffs with
  | zero => rfl
  | succ rem ih =>
    simp only [multXdiffLoopPure]
    rw [ih]
    exact List.length_set

theorem multXdiffAssignTrailingLoop_eq_ok (diff : GF16) :
    ∀ (rem i : Nat) (coeffs : List GF16),
      1 ≤ i → i + rem ≤ coeffs.length →
      Poly.multXdiffAssignTrailingLoop diff i rem coeffs =
        .ok (multXdiffLoopPure diff i rem coeffs)
  | 0, _, _, _, _ => rfl
  | rem + 1, i, coeffs, hi, hlen => by
    have hi0 : (i == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
    have hi_lt : i < coeffs.length := by omega
    have hiprev_lt : i - 1 < coeffs.length := by omega
    have hci : coeffs[i]? = some (coeffs[i]'hi_lt) := List.getElem?_eq_getElem hi_lt
    have hciprev : coeffs[i - 1]? = some (coeffs[i - 1]'hiprev_lt) := List.getElem?_eq_getElem hiprev_lt
    simp only [Poly.multXdiffAssignTrailingLoop, multXdiffLoopPure, hi0, Bool.false_eq_true,
      ↓reduceIte, hci, hciprev, Option.getD_some]
    apply multXdiffAssignTrailingLoop_eq_ok diff rem (i + 1) _ (by omega)
    rw [List.length_set]
    omega

/-- Pure total version of `Poly.multXdiffAssignTrailing`. -/
def multXdiffPure (self : Poly) (start : Nat) (diff : GF16) : Poly :=
  let l := self.coefficients.length
  if start ≥ l then self
  else ⟨multXdiffLoopPure diff start (l - start) self.coefficients⟩

@[simp]
theorem multXdiffPure_length (self : Poly) (start : Nat) (diff : GF16) :
    (multXdiffPure self start diff).coefficients.length = self.coefficients.length := by
  dsimp [multXdiffPure]
  split <;> simp

theorem multXdiffAssignTrailing_eq_ok (self : Poly) (start : Nat) (diff : GF16)
    (hstart : 1 ≤ start) :
    self.multXdiffAssignTrailing start diff = .ok (multXdiffPure self start diff) := by
  unfold Poly.multXdiffAssignTrailing multXdiffPure
  dsimp only
  split
  · rfl
  · rename_i hlt
    rw [multXdiffAssignTrailingLoop_eq_ok diff (self.coefficients.length - start) start
      self.coefficients hstart (by omega)]
    rfl

/-- Pure total version of `Poly.lagrangeInterpolatePrepareLoop`. -/
def prepareLoopPure (pts : List Pt) (offset : Nat) : Nat → Nat → Poly → Poly
  | _, 0, p => p
  | i, rem + 1, p =>
    let pi := pts[i]?.getD { x := GF16.ZERO, y := GF16.ZERO }
    let p' := multXdiffPure p (offset - i) pi.x
    prepareLoopPure pts offset (i + 1) rem p'

@[simp]
theorem prepareLoopPure_length (pts : List Pt) (offset i rem : Nat) (p : Poly) :
    (prepareLoopPure pts offset i rem p).coefficients.length = p.coefficients.length := by
  induction rem generalizing i p with
  | zero => rfl
  | succ rem ih =>
    simp only [prepareLoopPure]
    rw [ih, multXdiffPure_length]

theorem lagrangeInterpolatePrepareLoop_eq_ok (pts : List Pt) (offset : Nat)
    (hoff : offset = pts.length) :
    ∀ (rem i : Nat) (p : Poly),
      i + rem ≤ offset →
      Poly.lagrangeInterpolatePrepareLoop pts offset i rem p =
        .ok (prepareLoopPure pts offset i rem p)
  | 0, _, _, _ => rfl
  | rem + 1, i, p, hle => by
    have hi_lt : i < pts.length := by omega
    have hpi : pts[i]? = some (pts[i]'hi_lt) := List.getElem?_eq_getElem hi_lt
    have hgt : ¬ (i > offset) := by omega
    have hstart : 1 ≤ offset - i := by omega
    simp only [Poly.lagrangeInterpolatePrepareLoop, prepareLoopPure, hpi, Option.getD_some,
      hgt, ↓reduceIte]
    change (do
      let p' ← p.multXdiffAssignTrailing (offset - i) (pts[i]'hi_lt).x
      Poly.lagrangeInterpolatePrepareLoop pts offset (i + 1) rem p') = _
    rw [multXdiffAssignTrailing_eq_ok p (offset - i) (pts[i]'hi_lt).x hstart]
    exact lagrangeInterpolatePrepareLoop_eq_ok pts offset hoff rem (i + 1) _ (by omega)

/-- Pure total version of `Poly.lagrangeInterpolatePrepare`. -/
def lagrangePreparePure (pts : List Pt) : Poly :=
  let offset := pts.length
  let p0 : Poly := { coefficients := List.replicate offset GF16.ZERO ++ [GF16.ONE] }
  prepareLoopPure pts offset 0 offset p0

@[simp]
theorem lagrangePreparePure_length (pts : List Pt) :
    (lagrangePreparePure pts).coefficients.length = pts.length + 1 := by
  simp [lagrangePreparePure]

theorem lagrangeInterpolatePrepare_eq_ok (pts : List Pt)
    (hlen : pts.length + 1 ≤ USIZE_MAX) :
    Poly.lagrangeInterpolatePrepare pts = .ok (lagrangePreparePure pts) := by
  unfold Poly.lagrangeInterpolatePrepare lagrangePreparePure
  have hgt : ¬ (pts.length + 1 > USIZE_MAX) := by omega
  simp only [hgt, ↓reduceIte]
  exact lagrangeInterpolatePrepareLoop_eq_ok pts pts.length rfl pts.length 0 _ (by omega)

/-! ## Separation-logic slice construction helpers -/

theorem gf16SliceAt_replicate_zero :
    ∀ (n : Nat) (ptr : BitVec 64),
      gf16SliceAt ptr (List.replicate n GF16.ZERO) =
        (ptr ↦ₛ List.replicate (2 * n) 0#8)
  | 0, ptr => by
    simp [gf16SliceAt, arrayAt, pointsToBytes_nil]
  | n + 1, ptr => by
    have hmul : 2 * (n + 1) = (2 * n) + 1 + 1 := by omega
    rw [List.replicate_succ, hmul, List.replicate_succ, List.replicate_succ,
      pointsToBytes_cons, pointsToBytes_cons]
    change gf16At GF16.ZERO ptr ∗ gf16SliceAt (ptr + 2#64) (List.replicate n GF16.ZERO) =
      (ptr ↦₈ 0#8) ∗ (((ptr + 1#64) ↦₈ 0#8) ∗ ((ptr + 1#64 + 1#64) ↦ₛ List.replicate (2 * n) 0#8))
    have h0 : gf16At GF16.ZERO ptr = (ptr ↦₈ 0#8) ∗ ((ptr + 1#64) ↦₈ 0#8) := by
      dsimp [gf16At, GF16.ZERO]
      rw [pointsTo16_split8 ptr 0#16]
      rfl
    have hptr : ptr + 1#64 + 1#64 = ptr + 2#64 := by
      rw [BitVec.add_assoc]; rfl
    rw [h0, hptr, gf16SliceAt_replicate_zero n (ptr + 2#64), sepConj_assoc]

theorem gf16SliceAt_append_singleton :
    ∀ (cs : List GF16) (g : GF16) (ptr : BitVec 64),
      gf16SliceAt ptr (cs ++ [g]) =
        gf16SliceAt ptr cs ∗ ((ptr + BitVec.ofNat 64 (2 * cs.length)) ↦₁₆ g.value)
  | [], g, ptr => by
    simp [gf16SliceAt, arrayAt, gf16At]
  | c :: cs, g, ptr => by
    change gf16At c ptr ∗ gf16SliceAt (ptr + 2#64) (cs ++ [g]) =
      (gf16At c ptr ∗ gf16SliceAt (ptr + 2#64) cs) ∗
        ((ptr + BitVec.ofNat 64 (2 * (cs.length + 1))) ↦₁₆ g.value)
    rw [gf16SliceAt_append_singleton cs g (ptr + 2#64), ← sepConj_assoc]
    have haddr : ptr + 2#64 + BitVec.ofNat 64 (2 * cs.length) =
        ptr + BitVec.ofNat 64 (2 * (cs.length + 1)) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      congr 2
      omega
    rw [haddr]

/-! ## Subroutine specification -/

/-- Arguments and preconditions for `<spqr::encoding::polynomial::Poly>::lagrange_interpolate_prepare` (`0x61c1c`). -/
structure LagrangePrepareArgs where
  out : BitVec 64
  ptsPtr : BitVec 64
  pts : List Pt
  hlen_bound : 4 * (pts.length + 1) < 2 ^ 63

/-- Subroutine specification for `<spqr::encoding::polynomial::Poly>::lagrange_interpolate_prepare` (`0x61c1c`). -/
def lagrangePrepareSpec (A : RustAlloc) (b : BitVec 64) : Spec LagrangePrepareArgs where
  pre := fun a s =>
    ⌜s.readReg64 .x0 = a.out ∧
      s.readReg64 .x1 = a.ptsPtr ∧
      s.readReg64 .x2 = BitVec.ofNat 64 a.pts.length⌝ ∗
    memRegion a.out 24 ∗
    ptSliceAt a.ptsPtr a.pts ∗
    reduceTableAt b ∗
    tokenInitAt b ∗
    A.pool ∗
    stackAt s.sp lagrangePrepareStack
  post := fun a s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    polyOf A a.out (lagrangePreparePure a.pts) ∗
    ptSliceAt a.ptsPtr a.pts ∗
    reduceTableAt b ∗
    tokenInitAt b ∗
    A.pool ∗
    stackAt s0.sp lagrangePrepareStack
  onPanic := fun _ s0 sf =>
    ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Relocatable (`[LibsignalPlacement]`) subroutine specification for
`<spqr::encoding::polynomial::Poly>::lagrange_interpolate_prepare` (Block `372`). -/
def lagrangePreparePlacedSpec [LibsignalPlacement] (A : RustAlloc) : Spec LagrangePrepareArgs where
  pre := fun a s =>
    ⌜s.readReg64 .x0 = a.out ∧
      s.readReg64 .x1 = a.ptsPtr ∧
      s.readReg64 .x2 = BitVec.ofNat 64 a.pts.length⌝ ∗
    memRegion a.out 24 ∗
    ptSliceAt a.ptsPtr a.pts ∗
    reduceTablePlacedAt ∗
    tokenInitPlacedAt ∗
    A.pool ∗
    stackAt s.sp lagrangePrepareStack
  post := fun a s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    polyOf A a.out (lagrangePreparePure a.pts) ∗
    ptSliceAt a.ptsPtr a.pts ∗
    reduceTablePlacedAt ∗
    tokenInitPlacedAt ∗
    A.pool ∗
    stackAt s0.sp lagrangePrepareStack
  onPanic := fun _ s0 sf =>
    ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem gf16SliceAt_zero (ptr : BitVec 64) :
    gf16SliceAt ptr [] = emp := rfl

theorem gf16SliceAt_cons (ptr : BitVec 64) (c : GF16) (cs : List GF16) :
    gf16SliceAt ptr (c :: cs) = (ptr ↦₁₆ c.value) ∗ gf16SliceAt (ptr + 2#64) cs := rfl

theorem ptSliceAt_zero (ptr : BitVec 64) :
    ptSliceAt ptr [] = emp := rfl

theorem ptSliceAt_cons (ptr : BitVec 64) (p : Pt) (ps : List Pt) :
    ptSliceAt ptr (p :: ps) =
      ((ptr ↦₁₆ p.x.value) ∗ ((ptr + 2#64) ↦₁₆ p.y.value)) ∗ ptSliceAt (ptr + 4#64) ps := rfl

theorem polyOf_eq (A : RustAlloc) (v : BitVec 64) (p : Poly) :
    polyOf A v p =
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 p.coefficients.length) ∗
        ⌜p.coefficients.length ≤ cap.toNat ∧ cap.toNat * 2 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (if cap = 0 then emp
         else A.live ptr (cap.toNat * 2) 2 ∗ gf16SliceAt ptr p.coefficients ∗
           memRegion (ptr + BitVec.ofNat 64 (p.coefficients.length * 2)) ((cap.toNat - p.coefficients.length) * 2)) := by
  unfold polyOf vecOf vecAt vecHeader vecBuf gf16SliceAt gf16Stride gf16Align
  simp only [sepConj_assoc]

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
        congr 2; omega
      rw [haddr]; ac_rfl

theorem gf16SliceRest_set (ptr : BitVec 64) (cs : List GF16) (k : Nat) (v : GF16) :
  gf16SliceRest ptr (cs.set k v) k = gf16SliceRest ptr cs k := by
  induction cs generalizing k ptr with
  | nil => rfl
  | cons c cs ih =>
    cases k with
    | zero => rfl
    | succ k' => simp only [List.set_cons_succ, gf16SliceRest, ih]

theorem gf16SliceAt_update {cs : List GF16} {k : Nat} (hk : k < cs.length) (ptr : BitVec 64)
    (v : BitVec 16) :
    ((ptr + BitVec.ofNat 64 (2 * k)) ↦₁₆ v) ∗ gf16SliceRest ptr cs k =
      gf16SliceAt ptr (cs.set k ⟨v⟩) := by
  have hk_set : k < (cs.set k ⟨v⟩).length := by simp [hk]
  rw [gf16SliceAt_focus hk_set ptr, gf16SliceRest_set]
  simp [List.getElem_set_self]

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
        congr 2; omega
      rw [haddr]; ac_rfl

theorem ptSliceAt_focus_x_assoc {pts : List Pt} {k : Nat} (hk : k < pts.length)
    (ptr : BitVec 64) (R : SepProp) :
    ptSliceAt ptr pts ∗ R =
      ((ptr + BitVec.ofNat 64 (4 * k)) ↦₁₆ (pts[k]'hk).x.value) ∗ ptSliceRestX ptr pts k ∗ R := by
  rw [ptSliceAt_focus_x hk ptr, sepConj_assoc]

theorem memRegion_four (a : BitVec 64) :
    memRegion a 4 = ∃∗ v : BitVec 32, a ↦₃₂ v :=
  IsBlock.eq (IsBlock.memRegion a 4)
    (IsBlock.sepExists fun v => IsBlock.pointsTo32 a v)
    fun _ => ⟨fun _ => ⟨_, rfl⟩, fun _ => trivial⟩

theorem stackAt_lagrangePrepare_split (sp : BitVec 64) :
    stackAt sp lagrangePrepareStack =
      stackAt (sp - 208#64) allocHookStack ∗
      memRegion (sp - 208#64) 16 ∗
      (∃∗ v192 : BitVec 64, (sp - 192#64) ↦₆₄ v192) ∗
      (∃∗ v184 : BitVec 64, (sp - 184#64) ↦₆₄ v184) ∗
      (∃∗ v176 : BitVec 64, (sp - 176#64) ↦₆₄ v176) ∗
      (∃∗ v168 : BitVec 64, (sp - 168#64) ↦₆₄ v168) ∗
      (∃∗ v160 : BitVec 64, (sp - 160#64) ↦₆₄ v160) ∗
      (∃∗ v152 : BitVec 64, (sp - 152#64) ↦₆₄ v152) ∗
      (∃∗ v144 : BitVec 64, (sp - 144#64) ↦₆₄ v144) ∗
      memRegion (sp - 136#64) 4 ∗
      (∃∗ w132 : BitVec 32, (sp - 132#64) ↦₃₂ w132) ∗
      (∃∗ w128 : BitVec 32, (sp - 128#64) ↦₃₂ w128) ∗
      (∃∗ w124 : BitVec 32, (sp - 124#64) ↦₃₂ w124) ∗
      (∃∗ w120 : BitVec 32, (sp - 120#64) ↦₃₂ w120) ∗
      (∃∗ w116 : BitVec 32, (sp - 116#64) ↦₃₂ w116) ∗
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
  have hbot : sp - BitVec.ofNat 64 (0xd0 + allocHookStack) =
      sp - 208#64 - BitVec.ofNat 64 allocHookStack := by
    rw [BitVec.sub_sub, ← BitVec.ofNat_add]
  show stackAt sp (0xd0 + allocHookStack) = _
  rw [ProofLib.stackAt_split_bottom sp 0xd0 allocHookStack (by decide), hbot]
  simp only [stackAt]
  rw [show BitVec.ofNat 64 0xd0 = 208#64 from rfl,
      ProofLib.memRegion_split' (b := sp - 208#64) (n := 16) (k := 192) (b' := sp - 192#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 192#64) (n := 8) (k := 184) (b' := sp - 184#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 184#64) (n := 8) (k := 176) (b' := sp - 176#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 176#64) (n := 8) (k := 168) (b' := sp - 168#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 168#64) (n := 8) (k := 160) (b' := sp - 160#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 160#64) (n := 8) (k := 152) (b' := sp - 152#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 152#64) (n := 8) (k := 144) (b' := sp - 144#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 144#64) (n := 8) (k := 136) (b' := sp - 136#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 136#64) (n := 4) (k := 132) (b' := sp - 132#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 132#64) (n := 4) (k := 128) (b' := sp - 128#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 128#64) (n := 4) (k := 124) (b' := sp - 124#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 124#64) (n := 4) (k := 120) (b' := sp - 120#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 120#64) (n := 4) (k := 116) (b' := sp - 116#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 116#64) (n := 4) (k := 112) (b' := sp - 112#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 112#64) (n := 16) (k := 96) (b' := sp - 96#64) rfl (by bv_arith) (by decide),
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
      ProofLib.memRegion_eight (sp - 192#64), ProofLib.memRegion_eight (sp - 184#64),
      ProofLib.memRegion_eight (sp - 176#64), ProofLib.memRegion_eight (sp - 168#64),
      ProofLib.memRegion_eight (sp - 160#64), ProofLib.memRegion_eight (sp - 152#64),
      ProofLib.memRegion_eight (sp - 144#64),
      memRegion_four (sp - 132#64), memRegion_four (sp - 128#64),
      memRegion_four (sp - 124#64), memRegion_four (sp - 120#64),
      memRegion_four (sp - 116#64),
      ProofLib.memRegion_eight (sp - 96#64), ProofLib.memRegion_eight (sp - 88#64),
      ProofLib.memRegion_eight (sp - 80#64), ProofLib.memRegion_eight (sp - 72#64),
      ProofLib.memRegion_eight (sp - 64#64), ProofLib.memRegion_eight (sp - 56#64),
      ProofLib.memRegion_eight (sp - 48#64), ProofLib.memRegion_eight (sp - 40#64),
      ProofLib.memRegion_eight (sp - 32#64), ProofLib.memRegion_eight (sp - 24#64),
      ProofLib.memRegion_eight (sp - 16#64), ProofLib.memRegion_eight (sp - 8#64)]

theorem stackAt_lagrangePrepare_merge
    (sp sp' : BitVec 64)
    (v192 v184 v176 v168 v160 v152 v144 : BitVec 64)
    (w132 w128 w124 w120 w116 : BitVec 32)
    (s29 s30 s28 s27 s26 s25 s24 s23 s22 s21 s20 s19 : BitVec 64)
    (hsp : sp' = sp - 208#64) :
    stackAt sp' allocHookStack ∗
      memRegion (sp - 208#64) 16 ∗
      ((sp - 192#64) ↦₆₄ v192) ∗ ((sp - 184#64) ↦₆₄ v184) ∗ ((sp - 176#64) ↦₆₄ v176) ∗
      ((sp - 168#64) ↦₆₄ v168) ∗ ((sp - 160#64) ↦₆₄ v160) ∗ ((sp - 152#64) ↦₆₄ v152) ∗
      ((sp - 144#64) ↦₆₄ v144) ∗ memRegion (sp - 136#64) 4 ∗
      ((sp - 132#64) ↦₃₂ w132) ∗ ((sp - 128#64) ↦₃₂ w128) ∗ ((sp - 124#64) ↦₃₂ w124) ∗
      ((sp - 120#64) ↦₃₂ w120) ∗ ((sp - 116#64) ↦₃₂ w116) ∗ memRegion (sp - 112#64) 16 ∗
      ((sp - 96#64) ↦₆₄ s29) ∗ ((sp - 88#64) ↦₆₄ s30) ∗ ((sp - 80#64) ↦₆₄ s28) ∗
      ((sp - 72#64) ↦₆₄ s27) ∗ ((sp - 64#64) ↦₆₄ s26) ∗ ((sp - 56#64) ↦₆₄ s25) ∗
      ((sp - 48#64) ↦₆₄ s24) ∗ ((sp - 40#64) ↦₆₄ s23) ∗ ((sp - 32#64) ↦₆₄ s22) ∗
      ((sp - 24#64) ↦₆₄ s21) ∗ ((sp - 16#64) ↦₆₄ s20) ∗ ((sp - 8#64) ↦₆₄ s19) ⊢
      stackAt sp lagrangePrepareStack := by
  subst hsp; rw [stackAt_lagrangePrepare_split sp]
  refine sepConj_mono_right (sepConj_mono_right ?_)
  refine sepConj_mono (Entails.sepExists_intro v192) (sepConj_mono (Entails.sepExists_intro v184) ?_)
  refine sepConj_mono (Entails.sepExists_intro v176) (sepConj_mono (Entails.sepExists_intro v168) ?_)
  refine sepConj_mono (Entails.sepExists_intro v160) (sepConj_mono (Entails.sepExists_intro v152) ?_)
  refine sepConj_mono (Entails.sepExists_intro v144) (sepConj_mono_right ?_)
  refine sepConj_mono (Entails.sepExists_intro w132) (sepConj_mono (Entails.sepExists_intro w128) ?_)
  refine sepConj_mono (Entails.sepExists_intro w124) (sepConj_mono (Entails.sepExists_intro w120) ?_)
  refine sepConj_mono (Entails.sepExists_intro w116) (sepConj_mono_right ?_)
  refine sepConj_mono (Entails.sepExists_intro s29) (sepConj_mono (Entails.sepExists_intro s30) ?_)
  refine sepConj_mono (Entails.sepExists_intro s28) (sepConj_mono (Entails.sepExists_intro s27) ?_)
  refine sepConj_mono (Entails.sepExists_intro s26) (sepConj_mono (Entails.sepExists_intro s25) ?_)
  refine sepConj_mono (Entails.sepExists_intro s24) (sepConj_mono (Entails.sepExists_intro s23) ?_)
  refine sepConj_mono (Entails.sepExists_intro s22) (sepConj_mono (Entails.sepExists_intro s21) ?_)
  exact sepConj_mono (Entails.sepExists_intro s20) (Entails.sepExists_intro s19)

theorem polyOf_of_exact_cap (A : RustAlloc) (out ptr : BitVec 64) (p : Poly) (n : Nat)
    (hn0 : 1 ≤ n)
    (hlen : p.coefficients.length = n)
    (hbound : 2 * n < 2 ^ 63)
    (hptr_ne : ptr ≠ 0#64) :
    (out ↦₆₄ BitVec.ofNat 64 n) ∗
      ((out + 8#64) ↦₆₄ ptr) ∗
      ((out + 16#64) ↦₆₄ BitVec.ofNat 64 n) ∗
      A.live ptr (2 * n) 2 ∗
      gf16SliceAt ptr p.coefficients ⊢
      polyOf A out p := by
  have htoNat : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hne0 : BitVec.ofNat 64 n ≠ 0 := by
    intro h; have ht := congrArg BitVec.toNat h; rw [htoNat] at ht; change n = 0 at ht; omega
  have hmul : n * 2 = 2 * n := Nat.mul_comm n 2
  have hp : (n ≤ n ∧ 2 * n < 2 ^ 63 ∧ ptr ≠ 0) = True :=
    eq_true ⟨Nat.le_refl n, hbound, hptr_ne⟩
  have hpure : (⌜n ≤ n ∧ 2 * n < 2 ^ 63 ∧ ptr ≠ 0⌝ : SepProp) = emp := by
    rw [hp]; simp
  rw [polyOf_eq]
  refine Entails.trans ?_ (Entails.sepExists_intro (BitVec.ofNat 64 n))
  refine Entails.trans ?_ (Entails.sepExists_intro ptr)
  simp only [hlen, htoNat, Nat.sub_self, Nat.zero_mul, memRegion_zero, sepConj_emp,
    ite_eq_right_iff.mpr (fun h => False.elim (hne0 h)), hmul, hpure, emp_sepConj]
  exact Entails.refl _

theorem len_succ_bit62_false (n : Nat) (h : 4 * (n + 1) < 2 ^ 63) :
    (((BitVec.ofNat 64 n + 1#64) &&& 4611686018427387904#64) != 0#64) = false := by
  have h1 : BitVec.ofNat 64 n + 1#64 = BitVec.ofNat 64 (n + 1) := by
    rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
  rw [h1, bne_eq_false_iff_eq]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  have h62 : n + 1 < 2 ^ 62 := by omega
  have h64 : n + 1 < 2 ^ 64 := by omega
  have hlt : (BitVec.ofNat 64 (n + 1)).toNat < 2 ^ 62 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64]; exact h62
  have hpow : (4611686018427387904#64).toNat = 2 ^ 62 := rfl
  rw [hpow]
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_and, Nat.testBit_two_pow]
  by_cases hk : 62 = k
  · subst hk; rw [Nat.testBit_lt_two_pow hlt]; rfl
  · simp [hk]

theorem ofNat_shl_one_nat (n : Nat) :
    BitVec.ofNat 64 n <<< (1 : Nat) = BitVec.ofNat 64 (2 * n) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow, show BitVec.twoPow 64 1 = BitVec.ofNat 64 2 from rfl,
    ← BitVec.ofNat_mul, Nat.mul_comm]

theorem ofNat_shl_one (n : Nat) :
    BitVec.ofNat 64 n <<< 1#64 = BitVec.ofNat 64 (2 * n) :=
  ofNat_shl_one_nat n

theorem ofNat_add_one_shl_one (n : Nat) :
    (BitVec.ofNat 64 n + 1#64) <<< 1#64 = BitVec.ofNat 64 (2 * (n + 1)) := by
  rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
  exact ofNat_shl_one (n + 1)

theorem ofNat_add_one_shl_one_nat (n : Nat) :
    (BitVec.ofNat 64 n + 1#64) <<< (1 : Nat) = BitVec.ofNat 64 (2 * (n + 1)) := by
  rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
  exact ofNat_shl_one_nat (n + 1)

theorem ofNat_succ_sub_one_shl_one (r : Nat) :
    (BitVec.ofNat 64 (r + 1) + 0xffffffff_ffffffff#64) <<< (1 : Nat) = BitVec.ofNat 64 (2 * r) := by
  have hsub : BitVec.ofNat 64 (r + 1) + 0xffffffff_ffffffff#64 = BitVec.ofNat 64 r := by
    rw [BitVec.ofNat_add, BitVec.add_assoc]; exact BitVec.add_zero _
  rw [hsub]; exact ofNat_shl_one_nat r

theorem ofNat_two_mul_succ_toNat (n : Nat) (h : 4 * (n + 1) < 2 ^ 63) :
    (BitVec.ofNat 64 (2 * (n + 1))).toNat = 2 * (n + 1) := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem ofNat_two_mul_toNat (n : Nat) (h : 4 * (n + 1) < 2 ^ 63) :
    (BitVec.ofNat 64 (2 * n)).toNat = 2 * n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem allocFailedIn_of_trace_eq {s0 sf : State}
    (ht : sf.trace = s0.trace ++ [allocFailedEvent]) :
    allocFailedIn s0 sf := by
  unfold allocFailedIn; rw [ht, List.drop_left]; exact List.Mem.head []

theorem pull_pure_after_two (P1 P2 : SepProp) (φ : Prop) (Rest : SepProp) :
    P1 ∗ P2 ∗ ⌜φ⌝ ∗ Rest = ⌜φ⌝ ∗ P1 ∗ P2 ∗ Rest := by ac_rfl

theorem alloc_post_pos {P1 P2 Rest : SepProp} {x0 : BitVec 64} {φ : Prop} {Q : SepProp}
    (h0 : x0 = 0#64) :
    P1 ∗ P2 ∗ (if x0 = 0 then ⌜φ⌝ else Q) ∗ Rest = ⌜φ⌝ ∗ P1 ∗ P2 ∗ Rest := by
  have h0' : x0 = 0 := h0; simp only [h0', ↓reduceIte]; exact pull_pure_after_two P1 P2 φ Rest

theorem alloc_post_neg {P1 P2 Rest : SepProp} {x0 : BitVec 64} {φ ψ : Prop} {Q : SepProp}
    (h0 : x0 ≠ 0#64) :
    P1 ∗ P2 ∗ (if x0 = 0 then ⌜φ⌝ else ⌜ψ⌝ ∗ Q) ∗ Rest = ⌜ψ⌝ ∗ P1 ∗ P2 ∗ Q ∗ Rest := by
  have h0' : x0 ≠ 0 := h0; simp only [h0', ↓reduceIte]
  rw [sepConj_assoc ⌜ψ⌝ Q Rest]; exact pull_pure_after_two P1 P2 ψ (Q ∗ Rest)

theorem sub_two_toNat_eq (n : Nat) (h : 4 * (n + 1) < 2 ^ 63) :
    (BitVec.ofNat 64 (2 * (n + 1)) - 2#64).toNat = 2 * n := by
  have h1 : BitVec.ofNat 64 (2 * (n + 1)) - 2#64 = BitVec.ofNat 64 (2 * n) := by
    rw [show 2 * (n + 1) = 2 * n + 2 by omega, BitVec.ofNat_add]; exact BitVec.add_sub_cancel _ _
  rw [h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem combine_init_slice (ptr : BitVec 64) (n : Nat) (P1 P2 P3 Rest : SepProp) :
    gf16SliceAt ptr (List.replicate n GF16.ZERO) ∗ P1 ∗ P2 ∗ P3 ∗
      ((ptr + BitVec.ofNat 64 (2 * n)) ↦₁₆ 1#16) ∗ Rest =
      P1 ∗ P2 ∗ P3 ∗ gf16SliceAt ptr (List.replicate n GF16.ZERO ++ [GF16.ONE]) ∗ Rest := by
  have h1 : gf16SliceAt ptr (List.replicate n GF16.ZERO) ∗
      ((ptr + BitVec.ofNat 64 (2 * n)) ↦₁₆ 1#16) =
      gf16SliceAt ptr (List.replicate n GF16.ZERO ++ [GF16.ONE]) := by
    have hlen : (List.replicate n GF16.ZERO).length = n := List.length_replicate
    have h := gf16SliceAt_append_singleton (List.replicate n GF16.ZERO) GF16.ONE ptr
    rw [hlen] at h; exact h.symm
  rw [← h1]; ac_rfl

theorem outerLoop_frame_eq
    (P_pool P_stk P_live P_slice P_o0 P_o1 P_o2 P_pts P_red P_tok
     P_m208 P_192 P_184 P_176 P_168 P_160 P_152 P_144
     P_m136 P_132 P_128 P_124 P_120 P_116 Tail : SepProp) :
    P_pool ∗ P_stk ∗ P_live ∗ P_slice ∗ P_o0 ∗ P_o1 ∗ P_o2 ∗
      P_pts ∗ P_red ∗ P_tok ∗
      P_m208 ∗ P_192 ∗ P_184 ∗ P_176 ∗ P_168 ∗ P_160 ∗ P_152 ∗ P_144 ∗
      P_m136 ∗ P_132 ∗ P_128 ∗ P_124 ∗ P_120 ∗ P_116 ∗ Tail =
    P_tok ∗ P_132 ∗ P_128 ∗ P_124 ∗ P_120 ∗ P_116 ∗ P_slice ∗ P_red ∗
      P_168 ∗ P_160 ∗ P_152 ∗ P_144 ∗ P_pts ∗
      (P_pool ∗ P_stk ∗ P_live ∗ P_o0 ∗ P_o1 ∗ P_o2 ∗
       P_m208 ∗ P_192 ∗ P_184 ∗ P_176 ∗ P_m136 ∗ Tail) := by ac_rfl

end CryptoVerification.SpqrV1.Poly.LagrangePrepare

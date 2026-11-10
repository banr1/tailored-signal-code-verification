/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Epilogue
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Rodata
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysDefs
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysFallbackLoop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysInit
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysSumMult1
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<PolyEncoder as Encoder>::next_chunk`: `Poly::add_assign` and `lagrange_sum` Iteration Helpers

**Checked by Lean.**

Pure fold characterizations of `Poly.lagrangeSum` and `Poly.addAssignCoeffs`, together with
verification of the `Poly::add_assign` push/XOR loops and per-iteration `Poly::clone` / deallocation
blocks for `Poly::lagrange_sum`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Poly.NextChunk

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.ComputeAt
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly.LagrangePrepare
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  exists_pow_two_eq_two_sm exists_pow_two_eq_eight_sm
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre
  LagrangePrepare.sp_setPC_pre LagrangePrepare.sp_setMem_setPC_pre
  LagrangePrepare.readReg64_setPC_pre LagrangePrepare.readReg64_setMem_setPC_pre
  LagrangePrepare.readReg32_setPC_pre LagrangePrepare.readReg32_setMem_setPC_pre
  LagrangePrepare.readReg_setPC_pre LagrangePrepare.readReg_setMem_setPC_pre

/-! ## 1. Pure Lemmas for `Poly.addAssignCoeffs` and `Poly.lagrangeSum` -/

@[simp]
theorem addAssignCoeffs_nil_left (cs : List GF16) :
    Poly.addAssignCoeffs [] cs = cs := by
  cases cs <;> rfl

@[simp]
theorem addAssignCoeffs_nil_right (cs : List GF16) :
    Poly.addAssignCoeffs cs [] = cs := by
  cases cs <;> rfl

@[simp]
theorem addAssignCoeffs_cons (a : GF16) (as_ : List GF16) (b : GF16) (bs : List GF16) :
    Poly.addAssignCoeffs (a :: as_) (b :: bs) = GF16.add a b :: Poly.addAssignCoeffs as_ bs := rfl

theorem addAssignCoeffs_length_eq :
    ∀ {as_ bs : List GF16}, as_.length = bs.length →
      (Poly.addAssignCoeffs as_ bs).length = as_.length
  | [], [], _ => rfl
  | _ :: _, [], h => by simp at h
  | [], _ :: _, h => by simp at h
  | _ :: as_, _ :: bs, h => by
    have h' : as_.length = bs.length := by simp at h; omega
    simp [addAssignCoeffs_cons, addAssignCoeffs_length_eq h']

@[simp]
theorem multAssign_length (p : Poly) (c : GF16) :
    (p.multAssign c).coefficients.length = p.coefficients.length := by
  unfold Poly.multAssign
  exact parallelMult_length c p.coefficients

/-- Recursive fold for `Poly::lagrange_sum` over `pts` and `polys`. -/
def lagrangeSumFoldPoly (acc : Poly) : List Pt → List Poly → Poly
  | pt :: ptsRest, poly :: polysRest =>
    lagrangeSumFoldPoly (acc.addAssign (poly.multAssign pt.y)) ptsRest polysRest
  | _, _ => acc

@[simp]
theorem lagrangeSumFoldPoly_nil_left (acc : Poly) (polys : List Poly) :
    lagrangeSumFoldPoly acc [] polys = acc := rfl

@[simp]
theorem lagrangeSumFoldPoly_cons (acc : Poly) (pt : Pt) (ptsRest : List Pt)
    (poly : Poly) (polysRest : List Poly) :
    lagrangeSumFoldPoly acc (pt :: ptsRest) (poly :: polysRest) =
      lagrangeSumFoldPoly (acc.addAssign (poly.multAssign pt.y)) ptsRest polysRest := rfl

theorem lagrangeSum_eq_foldPoly (pts : List Pt) (polys : List Poly) :
    Poly.lagrangeSum pts polys = lagrangeSumFoldPoly Poly.zero pts polys := by
  unfold Poly.lagrangeSum
  have h : ∀ (pts : List Pt) (polys : List Poly) (acc : Poly),
      (pts.zip polys).foldl (fun (out : Poly) (pair : Pt × Poly) =>
        let p := pair.2.multAssign pair.1.y
        out.addAssign p) acc =
      lagrangeSumFoldPoly acc pts polys := by
    intro pts
    induction pts with
    | nil => intro polys acc; rfl
    | cons pt ptsRest ih =>
      intro polys acc
      cases polys with
      | nil => rfl
      | cons poly polysRest =>
        simp only [List.zip_cons_cons, List.foldl_cons, lagrangeSumFoldPoly_cons]
        exact ih polysRest _
  exact h pts polys Poly.zero

theorem gf16SliceAt_cons (ptr : BitVec 64) (c : GF16) (cs : List GF16) :
    gf16SliceAt ptr (c :: cs) = (gf16At c ptr ∗ gf16SliceAt (ptr + 2#64) cs) := rfl

/-! ## 2. `Poly::add_assign` Loops (`0x6b24c..0x6b2b4`, `+3784 -> +2640`) -/

@[local arm64_norm, local wp_norm]
theorem shl1_ofNat_sum (j : Nat) :
    BitVec.ofNat 64 j <<< 1 = BitVec.ofNat 64 (2 * j) :=
  shl_one_ofNat_eq_nat j

@[local arm64_norm, local wp_norm]
theorem add1_ofNat_sum (j : Nat) :
    BitVec.ofNat 64 j + 1#64 = BitVec.ofNat 64 (j + 1) := by
  rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]

@[local arm64_norm, local wp_norm]
theorem sub2_ofNat_sum (m : Nat) :
    BitVec.ofNat 64 (2 * (m + 1)) - 2#64 = BitVec.ofNat 64 (2 * m) := by
  have h2 : BitVec.ofNat 64 (2 * (m + 1)) = BitVec.ofNat 64 (2 * m) + 2#64 := by
    rw [show 2 * (m + 1) = 2 * m + 2 by omega, BitVec.ofNat_add]
  rw [h2]; bv_omega

@[local arm64_norm, local wp_norm]
theorem sub2_ofNat_sum_add (m : Nat) :
    BitVec.ofNat 64 (2 * (m + 1)) + 18446744073709551614#64 = BitVec.ofNat 64 (2 * m) := by
  have h1 : (18446744073709551614#64 : BitVec 64) = -2#64 := rfl
  have h2 : BitVec.ofNat 64 (2 * (m + 1)) = BitVec.ofNat 64 (2 * m) + 2#64 := by
    rw [show 2 * (m + 1) = 2 * m + 2 by omega, BitVec.ofNat_add]
  rw [h1, h2]; bv_omega

@[local arm64_norm, local wp_norm]
theorem xor_zext64_gf16_sum (a b : GF16) :
    BitVec.truncate 16
      (BitVec.truncate 32
        (BitVec.zeroExtend 64 a.value ^^^ BitVec.zeroExtend 64 b.value)) =
      (GF16.add a b).value := by
  cases a; cases b; unfold GF16.add; dsimp only; bv_bits

@[local arm64_norm, local wp_norm]
theorem zext16_trunc32_xor_zext64_gf16_sum (a b : GF16) :
    BitVec.zeroExtend 16
      (BitVec.truncate 32
        (BitVec.zeroExtend 64 a.value ^^^ BitVec.zeroExtend 64 b.value)) =
      (GF16.add a b).value := by
  cases a; cases b; unfold GF16.add; dsimp only; bv_bits

theorem ult_self_false_sum (j : Nat) :
    (BitVec.ofNat 64 j).ult (BitVec.ofNat 64 j) = false := by
  simp [BitVec.ult]

theorem beq_lt_false_sum {j n : Nat} (hj : j < n) (hn : n ≤ 0x0555555555555555) :
    (BitVec.ofNat 64 j == BitVec.ofNat 64 n) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have hto := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hto
  omega

theorem bne_2m1_two_sum {m : Nat} (hm : m ≤ 0x0555555555555555) :
    (BitVec.ofNat 64 (2 * (m + 1)) != 2#64) = decide (m ≠ 0) := by
  by_cases h : m = 0
  · subst h; rfl
  · rw [decide_eq_true_eq.mpr h, bne_iff_ne]; intro heq
    have hto := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hto
    change 2 * (m + 1) = 2 at hto; omega

theorem beq_2m1_two_sum {m : Nat} (hm : m ≤ 0x0555555555555555) :
    (BitVec.ofNat 64 (2 * (m + 1)) == 2#64) = decide (m = 0) := by
  by_cases h : m = 0
  · subst h; rfl
  · rw [decide_eq_false_iff_not.mpr h, beq_eq_false_iff_ne]; intro heq
    have hto := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hto
    change 2 * (m + 1) = 2 at hto; omega

/-- `Poly::add_assign` push loop (`0x6b280..0x6b2b4`, `+3836 -> +3888 -> +2640`)
    when `out` starts with `out_len = j` and `self_index = j` (the `i = 0` iteration of `lagrange_sum`). -/
theorem addAssignPushLoop_sepWP {b : BitVec 64} {ext : String → Option (State → State)}
    {ret : BitVec 64} {post : State → SepProp → Prop} :
    ∀ (pRest : List GF16) (j n : Nat)
      (hne : pRest ≠ []) (hjn : j + pRest.length = n) (hn : n ≤ 0x0555555555555555)
      (s : State) (fsp accPtr clonePtr : BitVec 64)
      (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame : SepProp)
      (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 3836#64)
      (hrun : s.status = .Running) (hsp : s.sp = fsp)
      (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 (2 * n))
      (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 j)
      (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 j)
      (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 (2 * pRest.length))
      (hx22 : s.readReg64 .x22 = clonePtr)
      (hcont : ∀ s1 : State,
        s1.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 2640#64 →
        s1.status = .Running → s1.sp = fsp → s1.trace = s.trace →
        calleeSavedVRegs s1 = calleeSavedVRegs s →
        s1.readReg64 .x1 = BitVec.ofNat 64 (2 * n) →
        s1.readReg64 .x22 = clonePtr →
        s1.readReg64 .x24 = s.readReg64 .x24 →
        s1.readReg64 .x25 = s.readReg64 .x25 →
        s1.readReg64 .x26 = s.readReg64 .x26 →
        s1.readReg64 .x27 = s.readReg64 .x27 →
        s1.readReg64 .x28 = s.readReg64 .x28 →
        s1.readReg64 .x29 = s.readReg64 .x29 →
        SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s1
          (gf16SliceAt (accPtr + BitVec.ofNat 64 (2 * j)) pRest ∗
           gf16SliceAt (clonePtr + BitVec.ofNat 64 (2 * j)) pRest ∗
           ((fsp + 656#64) ↦₆₄ BitVec.ofNat 64 n) ∗
           ((fsp + 664#64) ↦₆₄ accPtr) ∗
           ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 n) ∗ Frame) post),
      SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s
        (memRegion (accPtr + BitVec.ofNat 64 (2 * j)) (2 * pRest.length) ∗
         gf16SliceAt (clonePtr + BitVec.ofNat 64 (2 * j)) pRest ∗
         ((fsp + 656#64) ↦₆₄ BitVec.ofNat 64 n) ∗
         ((fsp + 664#64) ↦₆₄ accPtr) ∗
         ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 j) ∗ Frame) post
  | [], _, _, hne, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => absurd rfl hne
  | p :: pTail, j, n, _, hjn, hn, s, fsp, accPtr, clonePtr, hfsp_align, Frame,
    hpc, hrun, hsp, hx1, hx19, hx20, hx21, hx22, hcont => by
    have hj_lt : j < n := by simp at hjn; omega
    have hult := ult_self_false_sum j
    have hbeq := beq_lt_false_sum hj_lt hn
    have hsub2 := sub2_ofNat_sum pTail.length
    have hsub2_add := sub2_ofNat_sum_add pTail.length
    have hbne2 := bne_2m1_two_sum (m := pTail.length) (by simp at hjn; omega)
    have hacc_add : (accPtr + BitVec.ofNat 64 (2 * j)) + 2#64 =
        accPtr + BitVec.ofNat 64 (2 * (j + 1)) := by
      rw [show 2 * (j + 1) = 2 * j + 2 by omega, BitVec.ofNat_add]; bv_omega
    have hclone_add : (clonePtr + BitVec.ofNat 64 (2 * j)) + 2#64 =
        clonePtr + BitVec.ofNat 64 (2 * (j + 1)) := by
      rw [show 2 * (j + 1) = 2 * j + 2 by omega, BitVec.ofNat_add]; bv_omega
    rw [List.length_cons] at hx21
    rw [show 2 * (p :: pTail).length = 2 + 2 * pTail.length by simp; omega,
        ProofLib.memRegion_split' (b := accPtr + BitVec.ofNat 64 (2 * j))
          (n := 2) (k := 2 * pTail.length) (b' := accPtr + BitVec.ofNat 64 (2 * (j + 1)))
          rfl hacc_add.symm (by simp at hjn; omega),
        ProofLib.memRegion_two (accPtr + BitVec.ofNat 64 (2 * j)),
        gf16SliceAt_cons (clonePtr + BitVec.ofNat 64 (2 * j)) p pTail, hclone_add]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_elim; intro u_acc
    poly_next_chunk_fetches_range b (Rust.withPanics ext) 0xefc 56
    dsimp only [tripleRatchetProgAtExt, polyNextChunkName, BitVec.ofNat_eq_ofNat] at hpc hcont ⊢
    generalize_entry hentry :
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName = entry
    examples_hide_fetches
    unfold gf16At
    wp_steps
    cases pTail with
    | nil =>
      wp_steps
      subst hentry
      have hj1 : j + 1 = n := by simp at hjn; omega
      rw [hj1]
      simp only [gf16SliceAt_cons, gf16SliceAt, arrayAt, gf16At, List.length_nil,
        Nat.mul_zero, Nat.zero_mul, ProofLib.memRegion_zero, sepConj_emp] at hcont ⊢
      refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
        (hcont _ (by simp only [wp_norm, hult, hbeq, hsub2, hsub2_add, ↓reduceIte])
          (by wp_norm_lhs) (by simp only [wp_norm, hsp]) (by simp only [arm64_norm, wp_norm]) rfl
          (by simp only [wp_norm, hx1]) (by simp only [wp_norm, hx22])
          (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
          (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs))
    | cons p2 pTail' =>
      subst hentry
      have hne' : p2 :: pTail' ≠ [] := List.cons_ne_nil _ _
      have hjn' : (j + 1) + (p2 :: pTail').length = n := by simp at hjn ⊢; omega
      refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
        (addAssignPushLoop_sepWP (p2 :: pTail') (j + 1) n hne' hjn' hn _ fsp accPtr clonePtr hfsp_align
          (((accPtr + BitVec.ofNat 64 (2 * j)) ↦₁₆ p.value) ∗
           ((clonePtr + BitVec.ofNat 64 (2 * j)) ↦₁₆ p.value) ∗ Frame)
          (by simp only [wp_norm, hult, hbeq, hsub2, hsub2_add, hbne2, List.length_cons, ne_eq, Nat.succ_ne_zero, Nat.add_one_ne_zero, not_false_eq_true, decide_true, ↓reduceIte])
          (by wp_norm_lhs) (by simp only [wp_norm, hsp])
          (by simp only [wp_norm, hx1]) (by simp only [wp_norm]) (by simp only [wp_norm])
          (by simp only [wp_norm, hsub2, hsub2_add, List.length_cons]) (by simp only [wp_norm, hx22]) ?_)
      intro s1 hpc1 hrun1 hsp1 htr1 hvregs1 hx1_1 hx22_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
      have hacc_cons :
          gf16SliceAt (accPtr + BitVec.ofNat 64 (2 * j)) (p :: p2 :: pTail') =
          (((accPtr + BitVec.ofNat 64 (2 * j)) ↦₁₆ p.value) ∗
           gf16SliceAt (accPtr + BitVec.ofNat 64 (2 * (j + 1))) (p2 :: pTail')) := by
        rw [gf16SliceAt_cons, gf16At, hacc_add]
      have hclone_cons :
          gf16SliceAt (clonePtr + BitVec.ofNat 64 (2 * j)) (p :: p2 :: pTail') =
          (((clonePtr + BitVec.ofNat 64 (2 * j)) ↦₁₆ p.value) ∗
           gf16SliceAt (clonePtr + BitVec.ofNat 64 (2 * (j + 1))) (p2 :: pTail')) := by
        rw [gf16SliceAt_cons, gf16At, hclone_add]
      refine SepWP.weaken_pre
        (Entails.of_eq (by rw [hacc_cons, hclone_cons]; ac_rfl))
        (hcont s1 hpc1 hrun1 hsp1
          (by rw [htr1]; simp only [arm64_norm, wp_norm])
          (by rw [hvregs1]; rfl)
          hx1_1 hx22_1
          (by rw [hx24_1]; wp_norm_lhs)
          (by rw [hx25_1]; wp_norm_lhs)
          (by rw [hx26_1]; wp_norm_lhs)
          (by rw [hx27_1]; wp_norm_lhs)
          (by rw [hx28_1]; wp_norm_lhs)
          (by rw [hx29_1]; wp_norm_lhs))

/-- `Poly::add_assign` XOR loop (`0x6b260..0x6b284`, `+3804 -> +2640`)
    when `out` already has length `n` (iterations `i > 0` of `lagrange_sum`). -/
theorem addAssignXorLoop_sepWP {b : BitVec 64} {ext : String → Option (State → State)}
    {ret : BitVec 64} {post : State → SepProp → Prop} :
    ∀ (outRest pRest : List GF16) (j n : Nat)
      (hne : pRest ≠ []) (hlen_eq : outRest.length = pRest.length)
      (hjn : j + pRest.length = n) (hn : n ≤ 0x0555555555555555)
      (s : State) (fsp accPtr clonePtr : BitVec 64)
      (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame : SepProp)
      (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 3804#64)
      (hrun : s.status = .Running) (hsp : s.sp = fsp)
      (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 (2 * n))
      (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 j)
      (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 n)
      (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 (2 * pRest.length))
      (hx22 : s.readReg64 .x22 = clonePtr)
      (hcont : ∀ s1 : State,
        s1.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 2640#64 →
        s1.status = .Running → s1.sp = fsp → s1.trace = s.trace →
        calleeSavedVRegs s1 = calleeSavedVRegs s →
        s1.readReg64 .x1 = BitVec.ofNat 64 (2 * n) →
        s1.readReg64 .x22 = clonePtr →
        s1.readReg64 .x24 = s.readReg64 .x24 →
        s1.readReg64 .x25 = s.readReg64 .x25 →
        s1.readReg64 .x26 = s.readReg64 .x26 →
        s1.readReg64 .x27 = s.readReg64 .x27 →
        s1.readReg64 .x28 = s.readReg64 .x28 →
        s1.readReg64 .x29 = s.readReg64 .x29 →
        SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s1
          (gf16SliceAt (accPtr + BitVec.ofNat 64 (2 * j)) (Poly.addAssignCoeffs outRest pRest) ∗
           gf16SliceAt (clonePtr + BitVec.ofNat 64 (2 * j)) pRest ∗
           ((fsp + 664#64) ↦₆₄ accPtr) ∗ Frame) post),
      SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s
        (gf16SliceAt (accPtr + BitVec.ofNat 64 (2 * j)) outRest ∗
         gf16SliceAt (clonePtr + BitVec.ofNat 64 (2 * j)) pRest ∗
         ((fsp + 664#64) ↦₆₄ accPtr) ∗ Frame) post
  | _, [], _, _, hne, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => absurd rfl hne
  | [], _ :: _, _, _, _, hlen, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp at hlen
  | o :: oTail, p :: pTail, j, n, _, hlen_eq, hjn, hn, s, fsp, accPtr, clonePtr,
    hfsp_align, Frame, hpc, hrun, hsp, hx1, hx19, hx20, hx21, hx22, hcont => by
    have hj_lt : j < n := by simp at hjn; omega
    have hult : (BitVec.ofNat 64 j).ult (BitVec.ofNat 64 n) = true := by
      simp only [BitVec.ult, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : j < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : n < 2 ^ 64), decide_eq_true_eq]
      omega
    have hsub2 := sub2_ofNat_sum pTail.length
    have hsub2_add := sub2_ofNat_sum_add pTail.length
    have hbeq2 := beq_2m1_two_sum (m := pTail.length) (by simp at hjn; omega)
    have hacc_add : (accPtr + BitVec.ofNat 64 (2 * j)) + 2#64 =
        accPtr + BitVec.ofNat 64 (2 * (j + 1)) := by
      rw [show 2 * (j + 1) = 2 * j + 2 by omega, BitVec.ofNat_add]; bv_omega
    have hclone_add : (clonePtr + BitVec.ofNat 64 (2 * j)) + 2#64 =
        clonePtr + BitVec.ofNat 64 (2 * (j + 1)) := by
      rw [show 2 * (j + 1) = 2 * j + 2 by omega, BitVec.ofNat_add]; bv_omega
    rw [List.length_cons] at hx21
    rw [gf16SliceAt_cons (accPtr + BitVec.ofNat 64 (2 * j)) o oTail, hacc_add,
        gf16SliceAt_cons (clonePtr + BitVec.ofNat 64 (2 * j)) p pTail, hclone_add]
    poly_next_chunk_fetches_range b (Rust.withPanics ext) 0xedc 40
    dsimp only [tripleRatchetProgAtExt, polyNextChunkName, BitVec.ofNat_eq_ofNat] at hpc hcont ⊢
    generalize_entry hentry :
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName = entry
    examples_hide_fetches
    unfold gf16At
    wp_steps
    cases pTail with
    | nil =>
      cases oTail with
      | nil =>
        subst hentry
        simp only [addAssignCoeffs_cons, addAssignCoeffs_nil_left,
          gf16SliceAt_cons, gf16SliceAt, arrayAt, gf16At, sepConj_emp] at hcont ⊢
        refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
          (hcont _ (by simp only [wp_norm, hsub2, hsub2_add, hbeq2, List.length_nil, decide_true, ↓reduceIte])
            (by wp_norm_lhs) (by simp only [wp_norm, hsp]) (by simp only [arm64_norm, wp_norm]) rfl
            (by simp only [wp_norm, hx1]) (by simp only [wp_norm, hx22])
            (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
            (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs))
      | cons _ _ => simp at hlen_eq
    | cons p2 pTail' =>
      cases oTail with
      | nil => simp at hlen_eq
      | cons o2 oTail' =>
        conv => arg 3; simp only [wp_norm, hsub2, hsub2_add, hbeq2, List.length_cons, Nat.succ_ne_zero, decide_false, Bool.false_eq_true, ↓reduceIte]
        wp_steps
        subst hentry
        have hne' : p2 :: pTail' ≠ [] := List.cons_ne_nil _ _
        have hlen_eq' : (o2 :: oTail').length = (p2 :: pTail').length := by
          simp at hlen_eq ⊢; omega
        have hjn' : (j + 1) + (p2 :: pTail').length = n := by simp at hjn ⊢; omega
        have hj1_lt : j + 1 < n := by simp at hjn'; omega
        have hult1 : (BitVec.ofNat 64 (j + 1)).ult (BitVec.ofNat 64 n) = true := by
          simp only [BitVec.ult, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega : j + 1 < 2 ^ 64),
            Nat.mod_eq_of_lt (by omega : n < 2 ^ 64), decide_eq_true_eq]
          omega
        refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
          (addAssignXorLoop_sepWP (o2 :: oTail') (p2 :: pTail') (j + 1) n
            hne' hlen_eq' hjn' hn _ fsp accPtr clonePtr hfsp_align
            (((accPtr + BitVec.ofNat 64 (2 * j)) ↦₁₆ (GF16.add o p).value) ∗
             ((clonePtr + BitVec.ofNat 64 (2 * j)) ↦₁₆ p.value) ∗ Frame)
            (by simp only [wp_norm, hult1, ↓reduceIte])
            (by wp_norm_lhs) (by simp only [wp_norm, hsp])
            (by simp only [wp_norm, hx1]) (by simp only [wp_norm])
            (by simp only [wp_norm, hx20]) (by simp only [wp_norm, hsub2, hsub2_add, List.length_cons])
            (by simp only [wp_norm, hx22]) ?_)
        intro s1 hpc1 hrun1 hsp1 htr1 hvregs1 hx1_1 hx22_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
        have hacc_cons :
            gf16SliceAt (accPtr + BitVec.ofNat 64 (2 * j))
              (Poly.addAssignCoeffs (o :: o2 :: oTail') (p :: p2 :: pTail')) =
            (((accPtr + BitVec.ofNat 64 (2 * j)) ↦₁₆ (GF16.add o p).value) ∗
             gf16SliceAt (accPtr + BitVec.ofNat 64 (2 * (j + 1)))
               (Poly.addAssignCoeffs (o2 :: oTail') (p2 :: pTail'))) := by
          rw [addAssignCoeffs_cons, gf16SliceAt_cons, gf16At, hacc_add]
        have hclone_cons :
            gf16SliceAt (clonePtr + BitVec.ofNat 64 (2 * j)) (p :: p2 :: pTail') =
            (((clonePtr + BitVec.ofNat 64 (2 * j)) ↦₁₆ p.value) ∗
             gf16SliceAt (clonePtr + BitVec.ofNat 64 (2 * (j + 1))) (p2 :: pTail')) := by
          rw [gf16SliceAt_cons, gf16At, hclone_add]
        refine SepWP.weaken_pre
          (Entails.of_eq (by rw [hacc_cons, hclone_cons]; ac_rfl))
          (hcont s1 hpc1 hrun1 hsp1
            (by rw [htr1]; simp only [arm64_norm, wp_norm])
            (by rw [hvregs1]; rfl)
            hx1_1 hx22_1
            (by rw [hx24_1]; wp_norm_lhs)
            (by rw [hx25_1]; wp_norm_lhs)
            (by rw [hx26_1]; wp_norm_lhs)
            (by rw [hx27_1]; wp_norm_lhs)
            (by rw [hx28_1]; wp_norm_lhs)
            (by rw [hx29_1]; wp_norm_lhs))

/-- Entry to `Poly::add_assign` at `0x6b24c` (`+3784 -> +2640`) on iteration `i = 0`
    (when `[fsp + 672] = 0#64` and `accPtr` is an uninitialized `memRegion accPtr (2 * n)`). -/
theorem addAssignFirst_sepWP {b : BitVec 64} {ext : String → Option (State → State)}
    {ret : BitVec 64} {post : State → SepProp → Prop}
    (pCs : List GF16) (n : Nat)
    (hne : pCs ≠ []) (hlen : pCs.length = n) (hn : n ≤ 0x0555555555555555)
    (s : State) (fsp accPtr clonePtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 3784#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx22 : s.readReg64 .x22 = clonePtr)
    (hcont : ∀ s1 : State,
      s1.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 2640#64 →
      s1.status = .Running → s1.sp = fsp → s1.trace = s.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x1 = BitVec.ofNat 64 (2 * n) →
      s1.readReg64 .x22 = clonePtr →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s1
        (gf16SliceAt accPtr (Poly.addAssignCoeffs [] pCs) ∗
         gf16SliceAt clonePtr pCs ∗
         ((fsp + 128#64) ↦₆₄ BitVec.ofNat 64 (2 * n)) ∗
         ((fsp + 656#64) ↦₆₄ BitVec.ofNat 64 n) ∗
         ((fsp + 664#64) ↦₆₄ accPtr) ∗
         ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 n) ∗ Frame) post) :
    SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s
      (memRegion accPtr (2 * n) ∗
       gf16SliceAt clonePtr pCs ∗
       ((fsp + 128#64) ↦₆₄ BitVec.ofNat 64 (2 * n)) ∗
       ((fsp + 656#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       ((fsp + 664#64) ↦₆₄ accPtr) ∗
       ((fsp + 672#64) ↦₆₄ 0#64) ∗ Frame) post := by
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0xec8 20
  dsimp only [tripleRatchetProgAtExt, polyNextChunkName, BitVec.ofNat_eq_ofNat] at hpc hcont ⊢
  generalize_entry hentry :
    (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName = entry
  examples_hide_fetches
  wp_steps
  subst hentry
  have hacc0 : accPtr + BitVec.ofNat 64 (2 * 0) = accPtr := by bv_omega
  have hclone0 : clonePtr + BitVec.ofNat 64 (2 * 0) = clonePtr := by bv_omega
  refine SepWP.weaken_pre
    (by rw [← hlen, ← hacc0, ← hclone0]; exact Entails.of_eq (by ac_rfl))
    (addAssignPushLoop_sepWP pCs 0 n hne (by omega) hn _ fsp accPtr clonePtr hfsp_align
      (((fsp + 128#64) ↦₆₄ BitVec.ofNat 64 (2 * pCs.length)) ∗ Frame)
      (by wp_norm_goal) (by wp_norm_lhs) (by simp only [wp_norm, hsp])
      (by simp only [wp_norm, hlen]) (by wp_norm_lhs) (by wp_norm_lhs)
      (by simp only [wp_norm, hlen]) (by simp only [wp_norm, hx22]) ?_)
  intro s1 hpc1 hrun1 hsp1 htr1 hvregs1 hx1_1 hx22_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  rw [hacc0, hclone0, hlen]
  simp only [addAssignCoeffs_nil_left] at hcont
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (hcont s1 hpc1 hrun1 hsp1
      (by rw [htr1]; simp only [arm64_norm, wp_norm])
      (by rw [hvregs1]; rfl)
      hx1_1 hx22_1
      (by rw [hx24_1]; wp_norm_lhs)
      (by rw [hx25_1]; wp_norm_lhs)
      (by rw [hx26_1]; wp_norm_lhs)
      (by rw [hx27_1]; wp_norm_lhs)
      (by rw [hx28_1]; wp_norm_lhs)
      (by rw [hx29_1]; wp_norm_lhs))

/-- Entry to `Poly::add_assign` at `0x6b24c` (`+3784 -> +2640`) on iterations `i > 0`
    (when `[fsp + 672] = n` and `accPtr` holds `gf16SliceAt accPtr outCs`). -/
theorem addAssignNext_sepWP {b : BitVec 64} {ext : String → Option (State → State)}
    {ret : BitVec 64} {post : State → SepProp → Prop}
    (outCs pCs : List GF16) (n : Nat)
    (hne : pCs ≠ []) (hout_len : outCs.length = n) (hp_len : pCs.length = n)
    (hn : n ≤ 0x0555555555555555)
    (s : State) (fsp accPtr clonePtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 3784#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx22 : s.readReg64 .x22 = clonePtr)
    (hcont : ∀ s1 : State,
      s1.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 2640#64 →
      s1.status = .Running → s1.sp = fsp → s1.trace = s.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x1 = BitVec.ofNat 64 (2 * n) →
      s1.readReg64 .x22 = clonePtr →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s1
        (gf16SliceAt accPtr (Poly.addAssignCoeffs outCs pCs) ∗
         gf16SliceAt clonePtr pCs ∗
         ((fsp + 128#64) ↦₆₄ BitVec.ofNat 64 (2 * n)) ∗
         ((fsp + 656#64) ↦₆₄ BitVec.ofNat 64 n) ∗
         ((fsp + 664#64) ↦₆₄ accPtr) ∗
         ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 n) ∗ Frame) post) :
    SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s
      (gf16SliceAt accPtr outCs ∗
       gf16SliceAt clonePtr pCs ∗
       ((fsp + 128#64) ↦₆₄ BitVec.ofNat 64 (2 * n)) ∗
       ((fsp + 656#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       ((fsp + 664#64) ↦₆₄ accPtr) ∗
       ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 n) ∗ Frame) post := by
  have hn_pos : 0 < n := by have := List.length_pos_iff.mpr hne; omega
  have hult0 : (BitVec.ofNat 64 0).ult (BitVec.ofNat 64 n) = true := by
    simp only [BitVec.ult, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 0 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : n < 2 ^ 64), decide_eq_true_eq]
    omega
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0xec8 20
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0xefc 8
  dsimp only [tripleRatchetProgAtExt, polyNextChunkName, BitVec.ofNat_eq_ofNat] at hpc hcont ⊢
  generalize_entry hentry :
    (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName = entry
  examples_hide_fetches
  wp_steps
  subst hentry
  have hacc0 : accPtr + BitVec.ofNat 64 (2 * 0) = accPtr := by bv_omega
  have hclone0 : clonePtr + BitVec.ofNat 64 (2 * 0) = clonePtr := by bv_omega
  refine SepWP.weaken_pre
    (by rw [← hacc0, ← hclone0]; exact Entails.of_eq (by ac_rfl))
    (addAssignXorLoop_sepWP outCs pCs 0 n hne (by omega) (by omega) hn
      _ fsp accPtr clonePtr hfsp_align
      (((fsp + 128#64) ↦₆₄ BitVec.ofNat 64 (2 * n)) ∗
       ((fsp + 656#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 n) ∗ Frame)
      (by simp only [wp_norm, hult0, ↓reduceIte])
      (by wp_norm_lhs) (by simp only [wp_norm, hsp])
      (by simp only [wp_norm]) (by wp_norm_lhs) (by simp only [wp_norm])
      (by simp only [wp_norm, hp_len]) (by simp only [wp_norm, hx22]) ?_)
  intro s1 hpc1 hrun1 hsp1 htr1 hvregs1 hx1_1 hx22_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  rw [hacc0, hclone0]
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (hcont s1 hpc1 hrun1 hsp1
      (by rw [htr1]; simp only [arm64_norm, wp_norm])
      (by rw [hvregs1]; rfl)
      hx1_1 hx22_1
      (by rw [hx24_1]; wp_norm_lhs)
      (by rw [hx25_1]; wp_norm_lhs)
      (by rw [hx26_1]; wp_norm_lhs)
      (by rw [hx27_1]; wp_norm_lhs)
      (by rw [hx28_1]; wp_norm_lhs)
      (by rw [hx29_1]; wp_norm_lhs))

/-! ## 3. `Poly::lagrange_sum` Setup, Clone, and Dealloc Helpers -/

theorem next_chunk_panic_4688 {b : BitVec 64} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop} (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 4688#64)
    (hrun : s.status = .Running) (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0x1250 12
  dsimp only [tripleRatchetProgAtExt, polyNextChunkName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry hentry :
    (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName = entry
  examples_hide_fetches
  refine sepWPp_panic_of_sepWP_59096 s0 s P R ?_
  rw [hentry]; wp_steps
  exact SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
    ⟨Entails.refl _, by simpa [wp_norm] using htrace⟩

theorem sepWPp_panic_of_sepWP_4688 {b : BitVec 64} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop} (s0 s : State) (P R : SepProp)
    (hwp : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext))
      ((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 4688#64) s P
      (fun sm Pm => (Pm ⊢ P) ∧ sm.trace = s0.trace ++ [allocFailedEvent])) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) :=
  SepWPp.of_sepWP (SepWP.mono hwp fun sm Pm hpcm hrunm ⟨hPm, htrm⟩ =>
    SepWPp.weaken_pre hPm (next_chunk_panic_4688 s0 sm P R hpcm hrunm htrm))

theorem polyOf_expose_sum (A : RustAlloc) (addr : BitVec 64) (p : Poly) (n : Nat)
    (hn_pos : 0 < n) (hlen : p.coefficients.length = n) :
    polyOf A addr p ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜n ≤ cap.toNat ∧ cap.toNat * 2 < 2 ^ 63 ∧ ptr ≠ 0#64 ∧ cap ≠ 0#64⌝ ∗
        (addr ↦₆₄ cap) ∗ ((addr + 8#64) ↦₆₄ ptr) ∗
        ((addr + 16#64) ↦₆₄ BitVec.ofNat 64 n) ∗
        A.live ptr (cap.toNat * 2) 2 ∗
        (ptr ↦ₛ gf16SliceBytes p.coefficients) ∗
        memRegion (ptr + BitVec.ofNat 64 (n * 2)) ((cap.toNat - n) * 2) := by
  unfold polyOf vecOf vecAt vecHeader vecBuf gf16Stride gf16Align
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have h0_eq : (0#64 : BitVec 64) = 0 := rfl
    simp only [h0_eq, ↓reduceIte, sepConj_pure_left_comm]
    apply Entails.pure_left; intro ⟨h0, _⟩
    have h0_nat : (0 : BitVec 64).toNat = 0 := rfl
    omega
  · have hcap0' : cap ≠ 0 := hcap0
    simp only [hcap0, hcap0', ↓reduceIte, hlen, sepConj_pure_left_comm]
    apply Entails.pure_left; intro ⟨hle, hcap_lt, hptr⟩
    have hbytes : arrayAt gf16At 2 ptr p.coefficients = (ptr ↦ₛ gf16SliceBytes p.coefficients) :=
      gf16SliceAt_eq_pointsToBytes ptr p.coefficients
    rw [hbytes]
    refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
    exact Entails.pure_right ⟨hle, hcap_lt, hptr, hcap0⟩ (Entails.of_eq (by ac_rfl))

theorem polyOf_fold_sum (A : RustAlloc) (addr cap ptr : BitVec 64) (p : Poly) (n : Nat)
    (hlen : p.coefficients.length = n)
    (hle : n ≤ cap.toNat) (hcap_lt : cap.toNat * 2 < 2 ^ 63) (hptr : ptr ≠ 0#64) (hcap : cap ≠ 0#64) :
    (addr ↦₆₄ cap) ∗ ((addr + 8#64) ↦₆₄ ptr) ∗
    ((addr + 16#64) ↦₆₄ BitVec.ofNat 64 n) ∗
    A.live ptr (cap.toNat * 2) 2 ∗
    (ptr ↦ₛ gf16SliceBytes p.coefficients) ∗
    memRegion (ptr + BitVec.ofNat 64 (n * 2)) ((cap.toNat - n) * 2) ⊢
    polyOf A addr p := by
  unfold polyOf vecOf vecAt vecHeader vecBuf gf16Stride gf16Align
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  have hbytes : arrayAt gf16At 2 ptr p.coefficients = (ptr ↦ₛ gf16SliceBytes p.coefficients) :=
    gf16SliceAt_eq_pointsToBytes ptr p.coefficients
  have hcap' : cap ≠ 0 := hcap
  simp only [hcap, hcap', ↓reduceIte, hlen, hbytes, sepConj_pure_left_comm]
  exact Entails.pure_right ⟨hle, hcap_lt, hptr⟩ (Entails.of_eq (by ac_rfl))

theorem polyOf_entails_dealloc_sum (A : RustAlloc) (addr : BitVec 64) (p : Poly) (n : Nat)
    (hn_pos : 0 < n) (hlen : p.coefficients.length = n) :
    polyOf A addr p ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜cap.toNat * 2 < 2 ^ 63 ∧ ptr ≠ 0#64 ∧ cap ≠ 0#64⌝ ∗
        (addr ↦₆₄ cap) ∗ ((addr + 8#64) ↦₆₄ ptr) ∗
        ((addr + 16#64) ↦₆₄ BitVec.ofNat 64 n) ∗
        A.live ptr (cap.toNat * 2) 2 ∗
        memRegion ptr (cap.toNat * 2) := by
  refine Entails.trans (polyOf_expose_sum A addr p n hn_pos hlen) ?_
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  apply Entails.pure_left; intro ⟨hle, hcap_lt, hptr, hcap⟩
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  refine Entails.pure_right ⟨hcap_lt, hptr, hcap⟩ ?_
  have hlen_bs : (gf16SliceBytes p.coefficients).length = n * 2 := by
    rw [gf16SliceBytes_length, hlen, Nat.mul_comm]
  have hm := ProofLib.memRegion_split' (b := ptr) (N := cap.toNat * 2)
    (n := n * 2) (k := (cap.toNat - n) * 2) (b' := ptr + BitVec.ofNat 64 (n * 2))
    (by omega) rfl (by omega)
  have h1 : (ptr ↦ₛ gf16SliceBytes p.coefficients) ∗
      memRegion (ptr + BitVec.ofNat 64 (n * 2)) ((cap.toNat - n) * 2) ⊢
      memRegion ptr (cap.toNat * 2) := by
    refine Entails.trans (sepConj_mono_left (pointsToBytes_entails_memRegion ptr _)) ?_
    rw [hlen_bs, ← hm]
    exact Entails.refl _
  refine Entails.trans (Entails.of_eq (show
    ((addr ↦₆₄ cap) ∗ ((addr + 8#64) ↦₆₄ ptr) ∗ ((addr + 16#64) ↦₆₄ BitVec.ofNat 64 n) ∗
     A.live ptr (cap.toNat * 2) 2 ∗ (ptr ↦ₛ gf16SliceBytes p.coefficients) ∗
     memRegion (ptr + BitVec.ofNat 64 (n * 2)) ((cap.toNat - n) * 2)) =
    ((addr ↦₆₄ cap) ∗ ((addr + 8#64) ↦₆₄ ptr) ∗ ((addr + 16#64) ↦₆₄ BitVec.ofNat 64 n) ∗
     A.live ptr (cap.toNat * 2) 2 ∗
     ((ptr ↦ₛ gf16SliceBytes p.coefficients) ∗
      memRegion (ptr + BitVec.ofNat 64 (n * 2)) ((cap.toNat - n) * 2))) by ac_rfl)) ?_
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right h1)))

@[local arm64_norm, local wp_norm]
theorem madd_basis_addr_sum (basisPtr : BitVec 64) (i : Nat) :
    basisPtr + BitVec.ofNat 64 i * 24#64 = basisPtr + BitVec.ofNat 64 (24 * i) := by
  have h : BitVec.ofNat 64 i * 24#64 = BitVec.ofNat 64 (24 * i) := by
    rw [Nat.mul_comm 24 i, BitVec.ofNat_mul]
  rw [h]

@[local arm64_norm, local wp_norm]
theorem shl2_ofNat_sum (i : Nat) :
    BitVec.ofNat 64 i <<< 2#64 = BitVec.ofNat 64 (4 * i) := by
  have h1 : BitVec.ofNat 64 i <<< 2#64 = 4#64 * BitVec.ofNat 64 i := by bv_bits
  have h2 : BitVec.ofNat 64 (4 * i) = 4#64 * BitVec.ofNat 64 i := by
    rw [BitVec.ofNat_mul]
  rw [h1, h2]

@[local arm64_norm, local wp_norm]
theorem shl2_ofNat_sum_nat (i : Nat) :
    BitVec.ofNat 64 i <<< 2 = BitVec.ofNat 64 (4 * i) :=
  shl2_ofNat_sum i

@[local arm64_norm, local wp_norm]
theorem extractLsb_lo_concat_sum (lo hi : BitVec 64) :
    (hi ++ lo).extractLsb' 0 64 = lo := by bv_bits

@[local arm64_norm, local wp_norm]
theorem extractLsb_hi_concat_sum (lo hi : BitVec 64) :
    (hi ++ lo).extractLsb' 64 64 = hi := by bv_bits

theorem beq_i1_n_sum {i m n : Nat} (him : (i + 1) + m = n) (hn : n ≤ 0x0555555555555555) :
    (BitVec.ofNat 64 (i + 1) == BitVec.ofNat 64 n) = decide (m = 0) := by
  by_cases hm : m = 0
  · subst hm
    have hi : i + 1 = n := by omega
    rw [hi, beq_self_eq_true]; rfl
  · rw [decide_eq_false hm, beq_eq_false_iff_ne]
    intro heq
    have hto := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hto
    omega

/-- Setup block of `Poly::lagrange_sum` (`0x6adb4..0x6add0`, `+2608 -> +2668`). -/
theorem lagrangeSumSetup_sepWP {b : BitVec 64} {ext : String → Option (State → State)}
    {ret : BitVec 64} {post : State → SepProp → Prop}
    (n : Nat)
    (s : State) (fsp accPtr basisPtr ptVecPtr cIdx v27 : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (u16 u64 u72 u80 u656 u664 u672 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 2608#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = accPtr)
    (hx20 : s.readReg64 .x20 = cIdx)
    (hx24 : s.readReg64 .x24 = basisPtr)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 n)
    (hx26 : s.readReg64 .x26 = ptVecPtr)
    (hx27 : s.readReg64 .x27 = v27)
    (hx28 : s.readReg64 .x28 = 24#64)
    (hx29 : s.readReg64 .x29 = fsp + 1104#64)
    (hcont : ∀ s1 : State,
      s1.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 2668#64 →
      s1.status = .Running → s1.sp = fsp → s1.trace = s.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x21 = BitVec.ofNat 64 0 →
      s1.readReg64 .x24 = basisPtr →
      s1.readReg64 .x25 = BitVec.ofNat 64 n →
      s1.readReg64 .x26 = ptVecPtr →
      s1.readReg64 .x27 = v27 →
      s1.readReg64 .x28 = 24#64 →
      s1.readReg64 .x29 = fsp + 1104#64 →
      SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s1
        (((fsp + 16#64) ↦₆₄ cIdx) ∗
         ((fsp + 64#64) ↦₆₄ v27) ∗
         ((fsp + 72#64) ↦₆₄ basisPtr) ∗
         ((fsp + 80#64) ↦₆₄ ptVecPtr) ∗
         ((fsp + 656#64) ↦₆₄ BitVec.ofNat 64 n) ∗
         ((fsp + 664#64) ↦₆₄ accPtr) ∗
         ((fsp + 672#64) ↦₆₄ 0#64) ∗ Frame) post) :
    SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s
      (((fsp + 16#64) ↦₆₄ u16) ∗
       ((fsp + 64#64) ↦₆₄ u64) ∗
       ((fsp + 72#64) ↦₆₄ u72) ∗
       ((fsp + 80#64) ↦₆₄ u80) ∗
       ((fsp + 656#64) ↦₆₄ u656) ∗
       ((fsp + 664#64) ↦₆₄ u664) ∗
       ((fsp + 672#64) ↦₆₄ u672) ∗ Frame) post := by
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0xa30 32
  dsimp only [tripleRatchetProgAtExt, polyNextChunkName, BitVec.ofNat_eq_ofNat] at hpc hcont ⊢
  generalize_entry hentry :
    (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName = entry
  examples_hide_fetches
  wp_steps
  subst hentry
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (hcont _ (by wp_norm_goal) (by wp_norm_lhs) (by simp only [wp_norm, hsp])
      (by simp only [arm64_norm, wp_norm]) rfl
      (by wp_norm_lhs)
      (by simp only [wp_norm, hx24])
      (by simp only [wp_norm, hx25])
      (by simp only [wp_norm, hx26])
      (by simp only [wp_norm, hx27])
      (by simp only [wp_norm, hx28])
      (by simp only [wp_norm, hx29]))

/-- Per-iteration clone and `pt.y` load (`0x6adf0..0x6ae34`, `+2668 -> +2736`).
    Clones `poly.coefficients` into a freshly allocated buffer `clonePtr` (`2 * n` bytes, align `2`)
    and loads `pt.y.value` into `w21`. -/
theorem lagrangeSumClone_sepWPp {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {Q : State → SepProp → Prop}
    (hA : AllocContracts b A ext)
    (i n : Nat) (pt : Pt) (poly : Poly)
    (hn_pos : 0 < n) (hn : n ≤ 0x0555555555555555) (hplen : poly.coefficients.length = n)
    (s0 s : State) (fsp basisPtr ptVecPtr v27 u120 u128 : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame R : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 2668#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (htrace : s.trace = s0.trace)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 i)
    (hx24 : s.readReg64 .x24 = basisPtr)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 n)
    (hx26 : s.readReg64 .x26 = ptVecPtr)
    (hx27 : s.readReg64 .x27 = v27)
    (hx28 : s.readReg64 .x28 = 24#64)
    (hx29 : s.readReg64 .x29 = fsp + 1104#64)
    (hcont : ∀ s1 clonePtr,
      clonePtr ≠ 0#64 →
      s1.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 2736#64 →
      s1.status = .Running → s1.sp = fsp → s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x20 = BitVec.ofNat 64 n →
      s1.readReg64 .x21 = BitVec.zeroExtend 64 pt.y.value →
      s1.readReg64 .x22 = clonePtr →
      s1.readReg64 .x24 = basisPtr →
      s1.readReg64 .x25 = BitVec.ofNat 64 n →
      s1.readReg64 .x26 = ptVecPtr →
      s1.readReg64 .x27 = v27 →
      s1.readReg64 .x28 = 24#64 →
      s1.readReg64 .x29 = fsp + 1104#64 →
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s1
        (A.pool ∗
         A.live clonePtr (2 * n) 2 ∗
         gf16SliceAt clonePtr poly.coefficients ∗
         polyOf A (basisPtr + BitVec.ofNat 64 (24 * i)) poly ∗
         ptAt pt (ptVecPtr + BitVec.ofNat 64 (4 * i)) ∗
         ((fsp + 120#64) ↦₆₄ BitVec.ofNat 64 i) ∗
         ((fsp + 128#64) ↦₆₄ BitVec.ofNat 64 (2 * n)) ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗
       polyOf A (basisPtr + BitVec.ofNat 64 (24 * i)) poly ∗
       ptAt pt (ptVecPtr + BitVec.ofNat 64 (4 * i)) ∗
       ((fsp + 120#64) ↦₆₄ u120) ∗
       ((fsp + 128#64) ↦₆₄ u128) ∗
       stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  have hshim := hA.shim_ok_at polyNextChunkName
    (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
      ls_off% "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk"))
    (by rw [polyNextChunk_fnOff, (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
  simp only [sessionShimSpec] at hshim
  have halloc := hA.alloc_ok_at polyNextChunkName
    (num% (ls_off% "__rustc::__rust_alloc" -
      ls_off% "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk"))
    (by rw [polyNextChunk_fnOff, (ls_stub% "__rustc::__rust_alloc")])
  simp only [rustAllocSpec] at halloc
  have hmemcpy := hA.session_memcpy_ok_at polyNextChunkName
    (num% (ls_off% "memcpy" -
      ls_off% "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk"))
  simp only [sessionMemcpySpec] at hmemcpy
  have hpanic4688 := fun (s : State) (P : SepProp) =>
    @sepWPp_panic_of_sepWP_4688 b ext Q s0 s P R
  obtain ⟨hn_ne0, h2n_ne0⟩ := ofNat_pos_ne_zero hn_pos hn
  have hn_bne0 : ¬(BitVec.ofNat 64 n == 0#64) = true := by simpa [beq_iff_eq] using hn_ne0
  have hlayout2n : LayoutOk (2 * n) 2 := ⟨by omega, ⟨1, rfl⟩, by omega⟩
  have h2n_toNat : (BitVec.ofNat 64 (2 * n)).toNat = 2 * n := Nat.mod_eq_of_lt (by omega)
  have hlen_bytes : (gf16SliceBytes poly.coefficients).length = 2 * n := by
    rw [gf16SliceBytes_length, hplen]
  refine SepWPp.weaken_pre
    (sepConj_mono_right (sepConj_mono_left (polyOf_expose_sum A (basisPtr + BitVec.ofNat 64 (24 * i)) poly n hn_pos hplen))) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_pure_left_comm, sepConj_assoc]
  apply SepWPp.exists_elim; intro cap
  apply SepWPp.exists_elim; intro ptr
  apply SepWPp.pure_left; rintro ⟨hle, hcap_lt, hptr, hcap⟩
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0xa6c 68
  dsimp only [tripleRatchetProgAtExt, polyNextChunkName, BitVec.ofNat_eq_ofNat] at hpc hshim halloc hmemcpy hpanic4688 hcont ⊢
  generalize_entry hentry :
    (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 2704#64)
  wp_steps; wp_apply; wp_steps; wp_apply
  refine SepWP.done hpc_sf_1 hrun_sf_1 ?_
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · conv => arg 4; simp only [hoom, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; intro htr_oom
    refine hpanic4688 _ _ ?_
    wp_steps
    exact SepWP.done (by simp only [wp_norm, hoom, beq_self_eq_true, ↓reduceIte]) (by wp_norm_lhs)
      ⟨Entails.refl _, by rw [‹sf.trace = s.trace›, htrace] at htr_oom; exact htr_oom⟩
  · conv => arg 4; simp only [hoom, ↓reduceIte, sepConj_assoc, h2n_toNat]
    apply sepWPp_pure_mid; intro ⟨_, htr_alloc⟩
    have hcond_oom : ¬(sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = true := by
      simpa [beq_iff_eq] using hoom
    have hsp_sf1 : sf_1.sp = fsp := by rw [‹sf_1.sp = sf.sp›, ‹sf.sp = s.sp›, hsp]
    have hx19_sf1 : sf_1.readReg64 (Reg.gpr 19#5) = ptr := by
      rw [h_12, h_2]
    have hx20_sf1 : sf_1.readReg64 (Reg.gpr 20#5) = BitVec.ofNat 64 n := by
      rw [h_13, h_3]
    have hx21_sf1 : sf_1.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 i := by
      rw [h_14, h_4, hx21]
    have hx23_sf1 : sf_1.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 (2 * n) := by
      rw [h_16, h_6]
    have hx24_sf1 : sf_1.readReg64 (Reg.gpr 24#5) = basisPtr := by
      rw [h_17, h_7, hx24]
    have hx25_sf1 : sf_1.readReg64 (Reg.gpr 25#5) = BitVec.ofNat 64 n := by
      rw [h_18, h_8, hx25]
    have hx26_sf1 : sf_1.readReg64 (Reg.gpr 26#5) = ptVecPtr := by
      rw [h_19, h_9, hx26]
    have hx27_sf1 : sf_1.readReg64 (Reg.gpr 27#5) = v27 := by
      rw [h_20, h_10, hx27]
    have hx28_sf1 : sf_1.readReg64 (Reg.gpr 28#5) = 24#64 := by
      rw [h_21, h_11, hx28]
    have hx29_sf1 : sf_1.readReg64 (Reg.gpr 29#5) = fsp + 1104#64 := by
      rw [hcs_sf, hpost_sf, hx29]
    apply SepWPp.of_sepWP (mid := entry + 2736#64)
    unfold ptAt
    rw [← hlen_bytes]
    wp_steps; wp_apply; wp_steps
    refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
    subst hentry
    rw [hlen_bytes, ← gf16SliceAt_eq_pointsToBytes (sf_1.readReg64 (Reg.gpr 0#5)) poly.coefficients]
    have hfold_poly := polyOf_fold_sum A (basisPtr + BitVec.ofNat 64 (24 * i)) cap ptr poly n
      hplen hle hcap_lt hptr hcap
    have hfold_pt :
        (((ptVecPtr + BitVec.ofNat 64 (4 * i)) ↦₁₆ pt.x.value) ∗
         ((ptVecPtr + BitVec.ofNat 64 (4 * i) + 2#64) ↦₁₆ pt.y.value)) =
        ptAt pt (ptVecPtr + BitVec.ofNat 64 (4 * i)) := rfl
    refine SepWPp.weaken_pre ?_
      (hcont _ (sf_1.readReg64 (Reg.gpr 0#5)) hoom
        (by wp_norm_goal) (by wp_norm_lhs)
        (by simp only [wp_norm, hsp_sf_1, hsp_sf1])
        (by simp only [arm64_norm, wp_norm]; rw [hpost, htr_alloc, ‹sf.trace = s.trace›, htrace])
        (by simp only [arm64_norm, wp_norm]; rw [hvregs_2, hvregs_1, hvregs])
        (by simp only [wp_norm, h_23, hx20_sf1])
        (by wp_norm_lhs)
        (by simp only [wp_norm, h_25])
        (by simp only [wp_norm, h_27, hx24_sf1])
        (by simp only [wp_norm, h_28, hx25_sf1])
        (by simp only [wp_norm, h_29, hx26_sf1])
        (by simp only [wp_norm, h_30, hx27_sf1])
        (by simp only [wp_norm, h_31, hx28_sf1])
        (by simp only [wp_norm, hcs_sf_1, hx29_sf1]))
    rw [hsp_sf1]
    refine Entails.trans (Entails.of_eq (show _ =
      (((basisPtr + BitVec.ofNat 64 (24 * i)) ↦₆₄ cap) ∗
       ((basisPtr + BitVec.ofNat 64 (24 * i) + 8#64) ↦₆₄ ptr) ∗
       ((basisPtr + BitVec.ofNat 64 (24 * i) + 16#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       A.live ptr (cap.toNat * 2) 2 ∗
       (ptr ↦ₛ gf16SliceBytes poly.coefficients) ∗
       memRegion (ptr + BitVec.ofNat 64 (n * 2)) ((cap.toNat - n) * 2)) ∗
      (A.pool ∗
       A.live (sf_1.readReg64 (Reg.gpr 0#5)) (2 * n) 2 ∗
       gf16SliceAt (sf_1.readReg64 (Reg.gpr 0#5)) poly.coefficients ∗
       (((ptVecPtr + BitVec.ofNat 64 (4 * i)) ↦₁₆ pt.x.value) ∗
        ((ptVecPtr + BitVec.ofNat 64 (4 * i) + 2#64) ↦₁₆ pt.y.value)) ∗
       ((fsp + 120#64) ↦₆₄ BitVec.ofNat 64 i) ∗
       ((fsp + 128#64) ↦₆₄ BitVec.ofNat 64 (2 * n)) ∗
       stackAt fsp allocHookStack ∗ Frame) by ac_rfl)) ?_
    rw [hfold_pt]
    refine Entails.trans (sepConj_mono_left hfold_poly) ?_
    exact Entails.of_eq (by ac_rfl)

/-- Per-iteration deallocation of `clonePtr` and loop counter step (`0x6add4..0x6adec`, `+2640 -> +2668 / +3908`). -/
theorem lagrangeSumDeallocNext_sepWP {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {ret : BitVec 64} {post : State → SepProp → Prop}
    (hA : AllocContracts b A ext)
    (cs : List GF16) (i m n : Nat)
    (hn_pos : 0 < n) (hn : n ≤ 0x0555555555555555)
    (hcs_len : cs.length = n) (him : (i + 1) + m = n)
    (s : State) (fsp clonePtr : BitVec 64)
    (hclone_ne : clonePtr ≠ 0#64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 2640#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 (2 * n))
    (hx22 : s.readReg64 .x22 = clonePtr)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 n)
    (hcont : ∀ s1 : State,
      s1.pc = (if m = 0 then
          (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 3908#64
        else
          (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 2668#64) →
      s1.status = .Running → s1.sp = fsp → s1.trace = s.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x21 = BitVec.ofNat 64 (i + 1) →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = BitVec.ofNat 64 n →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s1
        (A.pool ∗
         ((fsp + 120#64) ↦₆₄ BitVec.ofNat 64 i) ∗
         stackAt fsp allocHookStack ∗ Frame) post) :
    SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s
      (A.pool ∗
       A.live clonePtr (2 * n) 2 ∗
       gf16SliceAt clonePtr cs ∗
       ((fsp + 120#64) ↦₆₄ BitVec.ofNat 64 i) ∗
       stackAt fsp allocHookStack ∗ Frame) post := by
  subst hsp
  have hdealloc := hA.dealloc_ok_at polyNextChunkName
    (num% (ls_off% "__rustc::__rust_dealloc" -
      ls_off% "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk"))
    (by rw [polyNextChunk_fnOff, (ls_stub% "__rustc::__rust_dealloc")])
  simp only [rustDeallocSpec] at hdealloc
  have h2n_toNat : (BitVec.ofNat 64 (2 * n)).toNat = 2 * n := Nat.mod_eq_of_lt (by omega)
  have hmem : gf16SliceAt clonePtr cs ⊢ memRegion clonePtr (2 * n) := by
    rw [gf16SliceAt_eq_pointsToBytes]
    have hlen : (gf16SliceBytes cs).length = 2 * n := by rw [gf16SliceBytes_length, hcs_len]
    rw [← hlen]
    exact pointsToBytes_entails_memRegion clonePtr _
  have hbeq := beq_i1_n_sum him hn
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hmem))) ?_
  rw [← h2n_toNat]
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0xa50 28
  dsimp only [tripleRatchetProgAtExt, polyNextChunkName, BitVec.ofNat_eq_ofNat] at hpc hdealloc hcont ⊢
  generalize_entry hentry :
    (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName = entry
  examples_hide_fetches
  wp_steps; wp_apply; wp_steps
  subst hentry
  by_cases hm0 : m = 0
  · subst hm0
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (hcont _ (by simp only [wp_norm, h_6, hx25, hbeq, decide_true, ↓reduceIte])
        (by wp_norm_lhs) (by simp only [wp_norm, ‹sf.sp = s.sp›])
        (by simp only [arm64_norm, wp_norm]; exact hpost)
        hvregs
        (by simp only [wp_norm, add1_ofNat_sum])
        (by simp only [wp_norm, h_5])
        (by simp only [wp_norm, h_6, hx25])
        (by simp only [wp_norm, h_7])
        (by simp only [wp_norm, h_8])
        (by simp only [wp_norm, h_9])
        (by simp only [wp_norm, hcs_sf]))
  · refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (hcont _ (by simp only [wp_norm, h_6, hx25, hbeq, hm0, decide_false, Bool.false_eq_true, ↓reduceIte])
        (by wp_norm_lhs) (by simp only [wp_norm, ‹sf.sp = s.sp›])
        (by simp only [arm64_norm, wp_norm]; exact hpost)
        hvregs
        (by simp only [wp_norm, add1_ofNat_sum])
        (by simp only [wp_norm, h_5])
        (by simp only [wp_norm, h_6, hx25])
        (by simp only [wp_norm, h_7])
        (by simp only [wp_norm, h_8])
        (by simp only [wp_norm, h_9])
        (by simp only [wp_norm, hcs_sf]))

end CryptoVerification.SpqrV1.Poly.NextChunk

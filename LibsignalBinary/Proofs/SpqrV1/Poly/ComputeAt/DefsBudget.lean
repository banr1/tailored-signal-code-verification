/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.Defs
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Budget-Threaded Specifications for `<spqr::encoding::polynomial::Poly>::compute_at`

Allocator event envelopes (`computeAtEvents`, `ComputeAtEnv`), `RustCliAllocBudget`-threaded
specifications (`computeAtSpec`, `computeAtPlacedSpec`), and `cap ∈ {0, 1}` `RawVec<GF16>::grow_one`
wrappers for Block `371`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.DefsBudget

open Arm64 ProofLib SepProp
open CryptoVerification
  (LibsignalPlacement blkPC_359 blkPl_359 lsmpl withLsCodeLoaded)
open CryptoVerification.SpqrV1.Alloc
  (growOneStack spqrHandleErrorSym spqrRustAllocSym spqrRustNoAllocShimSym
   spqrRustReallocSym)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (noAllocShimSpec)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitAt tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTableAt reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Poly (gf16SliceAt)
open CryptoVerification.SpqrV1.Poly.ComputeAt
  (ComputeAtArgs computeAtPure computeAtStack memRegion6_split_16_4 memRegion8_split_16_16_4
   pointsTo16_one_eq_bytes)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget
   rustAllocEvents rustCliAllocBudgetSpec rustCliReallocBudgetSpec rustDeallocEvents
   rustReallocEvents)
open LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneBudget
  (GrowOneStrideEnv fitsEnv_growOneStride_iff growOneGF16FullSpec growOneStrideEvents
   growOneStrideFullSpec growOneStrideFullSpecWithStack grow_one_gf16_full_placed_ok)

/-! ## Allocator Event Envelopes for `<Poly>::compute_at` -/

/-- Scratch `GF16` capacity allocated (and deallocated in the epilogue) by `<Poly>::compute_at`
    for a polynomial with `len` coefficients: `4` when `len ≤ 1`, and `len` when `2 ≤ len`. -/
def computeAtScratchCap (len : Nat) : Nat :=
  if len ≤ 1 then 4 else len

/-- Allocation/reallocation events emitted by `<Poly>::compute_at` before its epilogue
    `__rust_dealloc`:
    - `len = 0`: `grow_one` from `0 → 4` `GF16`s (`8` bytes, align `2`);
    - `len = 1`: `with_capacity(1)` (`2` bytes, align `2`) then `grow_one` (`2 → 8` bytes, align `2`);
    - `2 ≤ len`: `with_capacity(len)` (`2 * len` bytes, align `2`). -/
def computeAtAllocEvents (len : Nat) : List AllocEvent :=
  if len = 0 then
    rustAllocEvents 8 2
  else if len = 1 then
    rustAllocEvents 2 2 ++ rustReallocEvents 2 8 2
  else
    rustAllocEvents (2 * len) 2

/-- Full deterministic allocator event sequence of `<Poly>::compute_at` on `len` coefficients,
    including the epilogue `__rust_dealloc` of `2 * computeAtScratchCap len` bytes at alignment `2`. -/
def computeAtEvents (len : Nat) : List AllocEvent :=
  computeAtAllocEvents len ++ rustDeallocEvents (2 * computeAtScratchCap len) 2

def ComputeAtEnv (len : Nat) (evs : List AllocEvent) : Prop :=
  evs = computeAtEvents len

theorem fitsEnv_computeAt_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} (len : Nat) :
    FitsEnv M lim st (ComputeAtEnv len) ↔ FitsEvents M lim st (computeAtEvents len) :=
  FitsEnv.eq_iff

/-! ## Budget-Threaded `<Poly>::compute_at` Specifications -/

def computeAtSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (b : BitVec 64) : Spec (ComputeAtArgs × M.σ) where
  pre := fun (args, st) s =>
    ⌜s.readReg64 .x0 = args.p_coeffs ∧
      s.readReg64 .x1 = BitVec.ofNat 64 args.poly.coefficients.length ∧
      BitVec.truncate 16 (s.readReg64 .x2) = args.x.value ∧
      2 * args.poly.coefficients.length + 2 ≤ 2 ^ 63 ∧
      FitsEvents M lim st (computeAtAllocEvents args.poly.coefficients.length)⌝ ∗
    gf16SliceAt args.p_coeffs args.poly.coefficients ∗
    tokenInitAt b ∗
    reduceTableAt b ∗
    A.pool lim st s ∗
    stackAt s.sp computeAtStack
  post := fun (args, st) s0 sf =>
    ⌜sf.trace = s0.trace ∧
      BitVec.truncate 16 (sf.readReg64 .x0) = (computeAtPure args.poly args.x).value⌝ ∗
    gf16SliceAt args.p_coeffs args.poly.coefficients ∗
    tokenInitAt b ∗
    reduceTableAt b ∗
    A.pool lim (M.stepEvents (computeAtEvents args.poly.coefficients.length) st) sf ∗
    stackAt s0.sp computeAtStack
  onPanic := fun _ _ _ => ⌜False⌝

def computeAtPlacedSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (ComputeAtArgs × M.σ) where
  pre := fun (args, st) s =>
    ⌜s.readReg64 .x0 = args.p_coeffs ∧
      s.readReg64 .x1 = BitVec.ofNat 64 args.poly.coefficients.length ∧
      BitVec.truncate 16 (s.readReg64 .x2) = args.x.value ∧
      2 * args.poly.coefficients.length + 2 ≤ 2 ^ 63 ∧
      FitsEvents M lim st (computeAtAllocEvents args.poly.coefficients.length)⌝ ∗
    gf16SliceAt args.p_coeffs args.poly.coefficients ∗
    tokenInitPlacedAt ∗
    reduceTablePlacedAt ∗
    A.pool lim st s ∗
    stackAt s.sp computeAtStack
  post := fun (args, st) s0 sf =>
    ⌜sf.trace = s0.trace ∧
      BitVec.truncate 16 (sf.readReg64 .x0) = (computeAtPure args.poly args.x).value⌝ ∗
    gf16SliceAt args.p_coeffs args.poly.coefficients ∗
    tokenInitPlacedAt ∗
    reduceTablePlacedAt ∗
    A.pool lim (M.stepEvents (computeAtEvents args.poly.coefficients.length) st) sf ∗
    stackAt s0.sp computeAtStack
  onPanic := fun _ _ _ => ⌜False⌝

/-! ## Specialized `RawVec<GF16>::grow_one` Wrappers (`cap = 0` and `cap = 1`, Block `359`) -/

/-- Budget-threaded contract for `RawVec<GF16>::grow_one` called with `cap = 0` (`ptr = 2`). -/
def growOneGF16ZeroSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (BitVec 64 × M.σ) where
  pre := fun (v, st) s =>
    ⌜s.readReg64 .x0 = v ∧ FitsEvents M lim st (rustAllocEvents 8 2)⌝ ∗
    (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 2#64) ∗
    A.pool lim st s ∗ stackAt s.sp growOneStack
  post := fun (v, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64, ∃∗ w1 : BitVec 16, ∃∗ w0 : BitVec 16,
      ⌜p' ≠ 0#64 ∧ p'.toNat % 2 = 0⌝ ∗
      (v ↦₆₄ 4#64) ∗ ((v + 8#64) ↦₆₄ p') ∗
      A.live p' 8 2 ∗ (p' ↦₁₆ w0) ∗ ((p' + 2#64) ↦₁₆ w1) ∗
      memRegion (p' + 4#64) 4) ∗
    A.pool lim (M.stepEvents (rustAllocEvents 8 2) st) sf ∗ stackAt s0.sp growOneStack
  onPanic := fun _ _ _ => ⌜False⌝

/-- Budget-threaded contract for `RawVec<GF16>::grow_one` called with `cap = 1` and `p0 ↦₁₆ 1#16`. -/
def growOneGF16OneSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec ((BitVec 64 × BitVec 64) × M.σ) where
  pre := fun ((v, p0), st) s =>
    ⌜s.readReg64 .x0 = v ∧ p0 ≠ 0#64 ∧ FitsEvents M lim st (rustReallocEvents 2 8 2)⌝ ∗
    (v ↦₆₄ 1#64) ∗ ((v + 8#64) ↦₆₄ p0) ∗
    A.live p0 2 2 ∗ (p0 ↦₁₆ 1#16) ∗
    A.pool lim st s ∗ stackAt s.sp growOneStack
  post := fun ((v, _), st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64, ∃∗ w1 : BitVec 16,
      ⌜p' ≠ 0#64 ∧ p'.toNat % 2 = 0⌝ ∗
      (v ↦₆₄ 4#64) ∗ ((v + 8#64) ↦₆₄ p') ∗
      A.live p' 8 2 ∗ (p' ↦₁₆ 1#16) ∗ ((p' + 2#64) ↦₁₆ w1) ∗
      memRegion (p' + 4#64) 4) ∗
    A.pool lim (M.stepEvents (rustReallocEvents 2 8 2) st) sf ∗ stackAt s0.sp growOneStack
  onPanic := fun _ _ _ => ⌜False⌝

theorem grow_one_gf16_zero_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_359).rebase (blkPl_359).base H)
      (blkPl_359).base
      (withLsCodeLoaded lsmpl (growOneGF16ZeroSpec M A lim)) := by
  refine subroutine_ok_outcome_intro fun (v, st) R s0 hpc hrun hpre hsp => ?_
  dsimp only [withLsCodeLoaded] at hpre
  simp only [growOneGF16ZeroSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hfits⟩, hmem⟩
  have hfits_env : FitsEnv M lim st (GrowOneStrideEnv 0#64 2 2) := by
    rw [fitsEnv_growOneStride_iff]
    simpa [growOneStrideEvents] using hfits
  have hpre' :
      s0.mem ⊨ (withLsCodeLoaded lsmpl (growOneGF16FullSpec M A lim)).pre
        ((v, 0#64, 2#64, []), st) s0 ∗ R := by
    dsimp only [withLsCodeLoaded, growOneGF16FullSpec, growOneStrideFullSpec,
      growOneStrideFullSpecWithStack]
    simp only [ite_true, emp_sepConj, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, rfl, by decide, by decide, hfits_env⟩, hmem⟩
  refine (grow_one_gf16_full_placed_ok h_panic hshim halloc hrealloc).mono_outcome
    ((v, 0#64, 2#64, []), st) R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    change sf.mem ⊨ (growOneGF16FullSpec M A lim).post ((v, 0#64, 2#64, []), st) s0 sf ∗ R at hq
    dsimp only [withLsCodeLoaded, growOneGF16FullSpec, growOneStrideFullSpec,
      growOneStrideFullSpecWithStack, growOneGF16ZeroSpec] at hq ⊢
    have h4 : BitVec.ofNat 64 (max (2 * (0#64 : BitVec 64).toNat) 4) = 4#64 := rfl
    have h8 : max (2 * (0#64 : BitVec 64).toNat) 4 * 2 = 8 := rfl
    have h8' : (max (2 * (0#64 : BitVec 64).toNat) 4 - (0#64 : BitVec 64).toNat) * 2 = 8 := rfl
    have h0_2 : BitVec.ofNat 64 ([] : List (BitVec 8)).length = 0#64 := rfl
    have hevs : growOneStrideEvents 0#64 2 2 = rustAllocEvents 8 2 := rfl
    simp only [h4, h8, h8', h0_2, hevs, pointsToBytes_nil, BitVec.add_zero, emp_sepConj,
      memRegion8_split_16_16_4, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      satisfies_pure_sepConj, satisfies_sepExists] at hq ⊢
    exact hq
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact (not_satisfies_false_sepConj hq).elim

theorem grow_one_gf16_one_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_359).rebase (blkPl_359).base H)
      (blkPl_359).base
      (withLsCodeLoaded lsmpl (growOneGF16OneSpec M A lim)) := by
  refine subroutine_ok_outcome_intro fun ((v, p0), st) R s0 hpc hrun hpre hsp => ?_
  dsimp only [withLsCodeLoaded] at hpre
  simp only [growOneGF16OneSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hp0, hfits⟩, hmem⟩
  have hfits_env : FitsEnv M lim st (GrowOneStrideEnv 1#64 2 2) := by
    rw [fitsEnv_growOneStride_iff]
    simpa [growOneStrideEvents] using hfits
  have hpre' :
      s0.mem ⊨ (withLsCodeLoaded lsmpl (growOneGF16FullSpec M A lim)).pre
        ((v, 1#64, p0, [1#8, 0#8]), st) s0 ∗ R := by
    dsimp only [withLsCodeLoaded, growOneGF16FullSpec, growOneStrideFullSpec,
      growOneStrideFullSpecWithStack]
    simp only [show (1#64 : BitVec 64) = 0#64 ↔ False by decide, ite_false,
      List.length_cons, List.length_nil, ← pointsTo16_one_eq_bytes,
      sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, rfl, hp0, by decide, hfits_env⟩, hmem⟩
  refine (grow_one_gf16_full_placed_ok h_panic hshim halloc hrealloc).mono_outcome
    ((v, 1#64, p0, [1#8, 0#8]), st) R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    change sf.mem ⊨ (growOneGF16FullSpec M A lim).post ((v, 1#64, p0, [1#8, 0#8]), st) s0 sf ∗ R
      at hq
    dsimp only [withLsCodeLoaded, growOneGF16FullSpec, growOneStrideFullSpec,
      growOneStrideFullSpecWithStack, growOneGF16OneSpec] at hq ⊢
    have h4 : BitVec.ofNat 64 (max (2 * (1#64 : BitVec 64).toNat) 4) = 4#64 := rfl
    have h8 : max (2 * (1#64 : BitVec 64).toNat) 4 * 2 = 8 := rfl
    have h6 : (max (2 * (1#64 : BitVec 64).toNat) 4 - (1#64 : BitVec 64).toNat) * 2 = 6 := rfl
    have hlen2 : BitVec.ofNat 64 ([1#8, 0#8] : List (BitVec 8)).length = 2#64 := rfl
    have hevs : growOneStrideEvents 1#64 2 2 = rustReallocEvents 2 8 2 := rfl
    simp only [h4, h8, h6, hlen2, hevs, ← pointsTo16_one_eq_bytes,
      memRegion6_split_16_4, sepExists_sepConj_left, sepExists_sepConj_right,
      sepConj_assoc, satisfies_pure_sepConj, satisfies_sepExists] at hq ⊢
    exact hq
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact (not_satisfies_false_sepConj hq).elim

/-! ## Pool-Generic Frame Rearrangement Helpers for `compute_at` -/

theorem grow0_pre_split (sp0 : BitVec 64)
    (P_pool P_coeffs P_tok P_red P_m144 P_120 Tail : SepProp) :
    P_coeffs ∗ P_tok ∗ P_red ∗ P_pool ∗
      stackAt (sp0 - 144#64) growOneStack ∗
      P_m144 ∗
      ((sp0 - 136#64) ↦₆₄ 0#64) ∗
      ((sp0 - 128#64) ↦₆₄ 2#64) ∗
      P_120 ∗ Tail =
    (((sp0 - 136#64) ↦₆₄ 0#64) ∗
     ((sp0 - 136#64 + 8#64) ↦₆₄ 2#64) ∗
     P_pool ∗
     stackAt (sp0 - 144#64) growOneStack) ∗
    (P_coeffs ∗ P_tok ∗ P_red ∗ P_m144 ∗ P_120 ∗ Tail) := by
  have h128 : sp0 - 136#64 + 8#64 = sp0 - 128#64 := by bv_omega
  rw [h128]
  sep_ac_rfl

theorem grow1_pre_split (sp0 p0 : BitVec 64)
    (P_pool P_stk P_live P_p0 P_coeffs P_tok P_red P_m144 P_120 Tail : SepProp) :
    P_pool ∗ P_stk ∗ P_live ∗ P_p0 ∗ P_coeffs ∗ P_tok ∗ P_red ∗ P_m144 ∗
      ((sp0 - 136#64) ↦₆₄ 1#64) ∗
      ((sp0 - 128#64) ↦₆₄ p0) ∗
      P_120 ∗ Tail =
    (((sp0 - 136#64) ↦₆₄ 1#64) ∗
     ((sp0 - 136#64 + 8#64) ↦₆₄ p0) ∗
     P_live ∗ P_p0 ∗ P_pool ∗ P_stk) ∗
    (P_coeffs ∗ P_tok ∗ P_red ∗ P_m144 ∗ P_120 ∗ Tail) := by
  have h128 : sp0 - 136#64 + 8#64 = sp0 - 128#64 := by bv_omega
  rw [h128]
  sep_ac_rfl

end LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.DefsBudget

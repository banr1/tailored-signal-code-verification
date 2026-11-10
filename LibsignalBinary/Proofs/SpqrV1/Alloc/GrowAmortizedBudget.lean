/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Placed.GenLsBlock
public import LibsignalBinary.Proofs.SpqrV1.Alloc.FinishGrowBudget
public import LibsignalBinary.Proofs.SpqrV1.Alloc.GrowAmortized
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Alloc.Fetch
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable `grow_amortized` and `RawVec<(&str, &str)>::grow_one`

Proves `RustCliAllocBudget M` `[LibsignalPlacement]` contracts for block 260
(`<alloc::raw_vec::RawVecInner>::grow_amortized`) and block 258
(`<alloc::raw_vec::RawVec<(&str, &str)>>::grow_one`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Alloc.GrowAmortizedBudget

open Arm64 ProofLib
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement blkPC_258 blkPC_259 blkPC_260
  blkPl_258 blkPl_259 blkPl_260 lscall_blk lscall_blk_cl lsmpl sepWP_seq_lscl withLsCodeLoaded
)
open CryptoVerification.RustHeap (RustAlloc allocHookStack)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SpqrV1.Alloc (
  GrowAmortizedCall growAmortizedName growAmortizedStack
  growOneStrPairName growOneStrPairStack grow_amortized_new_eq
  newCap32 newCap32_toNat spqrHandleErrorSym spqrRustAllocSym
  spqrRustNoAllocShimSym spqrRustReallocSym
)
open CryptoVerification.SpqrV1.Alloc.GrowAmortizedNorm (
  readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre
  readReg64_setPC_pre readReg_setMem_setPC_pre readReg_setPC_pre
  sp_setMem_setPC_pre sp_setPC_pre
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents
  RustCliAllocBudget rustAllocEvents rustCliAllocBudgetSpec
  rustCliReallocBudgetSpec rustReallocEvents
)
open LibsignalBinary.Heap.SpecBudget (DecodeErrorPushEnv)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (noAllocShimSpec)
open LibsignalBinary.Proofs.SpqrV1.Alloc.FinishGrowBudget (
  FinishGrow1Call FinishGrow7Env finishGrow32Stack finishGrow7Events
  finishGrow7Spec finishGrow7SpecWithStack finishGrow7SpecX
  finish_grow_7_placed_ok finish_grow_7_placed_ok_x
  fitsEnv_finishGrow7_iff memRegion_24
)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg_setPC_pre readReg_setMem_setPC_pre

/-! ## Stack Helpers and Allocator Event Envelope -/

private theorem stackAt_growAmortized_gen (sp : BitVec 64) {hookStack : Nat}
    (hhook : (hookStack + 32) + 8 * 8 ≤ 2 ^ 64) :
    stackAt sp ((hookStack + 32) + 64) =
      stackAt (sp - 64#64) (hookStack + 32) ∗ cells (sp - 64#64) 8 :=
  ProofLib.stackAt_split_cells sp (hookStack + 32) 8 hhook

private theorem stackAt_growOneStrPair_gen (sp : BitVec 64) {hookStack : Nat}
    (hhook : ((hookStack + 32) + 64) + 2 * 8 ≤ 2 ^ 64) :
    stackAt sp (((hookStack + 32) + 64) + 16) =
      stackAt (sp - 16#64) ((hookStack + 32) + 64) ∗ cells (sp - 16#64) 2 :=
  ProofLib.stackAt_split_cells sp ((hookStack + 32) + 64) 2 hhook

/-- Deterministic allocator events of `grow_amortized` (`stride = 32, align = 8`). -/
def growAmortizedEvents (cap : BitVec 64) : List AllocEvent :=
  if cap = 0#64 then rustAllocEvents ((newCap32 cap).toNat * 32) 8
  else rustReallocEvents (cap.toNat * 32) ((newCap32 cap).toNat * 32) 8

def GrowAmortizedEnv (cap : BitVec 64) (evs : List AllocEvent) : Prop :=
  evs = growAmortizedEvents cap

theorem fitsEnv_growAmortized_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (cap : BitVec 64) :
    FitsEnv M lim st (GrowAmortizedEnv cap) ↔ FitsEvents M lim st (growAmortizedEvents cap) :=
  FitsEnv.eq_iff

/-- Embeds `growAmortizedEvents (BitVec.ofNat 64 n)` (`n < 2 ^ 32`) into `DecodeErrorPushEnv n`. -/
theorem decodeErrorPushEnv_growAmortizedEvents {n : Nat} (hn : n < 2 ^ 32) :
    DecodeErrorPushEnv n (growAmortizedEvents (BitVec.ofNat 64 n)) := by
  by_cases hn0 : n = 0
  · subst hn0
    refine Or.inr (Or.inl ⟨rfl, 4, by decide, by decide, ?_⟩)
    simp only [growAmortizedEvents, ↓reduceIte, (by decide : (newCap32 0#64).toNat = 4)]
  · have htoNat : (BitVec.ofNat 64 n).toNat = n := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hne0 : BitVec.ofNat 64 n ≠ 0#64 := fun h =>
      hn0 (by simpa [htoNat] using congrArg BitVec.toNat h)
    have hnew : (newCap32 (BitVec.ofNat 64 n)).toNat = max (2 * n) 4 := by
      rw [newCap32_toNat (by omega), htoNat]
    refine Or.inr (Or.inr ⟨n, (newCap32 (BitVec.ofNat 64 n)).toNat,
      by omega, Nat.le_refl _, by omega, by omega, ?_⟩)
    simp only [growAmortizedEvents, hne0, ↓reduceIte, htoNat]

theorem fitsEnv_growAmortized_of_decodeErrorPush {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {n : Nat} (hn : n < 2 ^ 32)
    (hfits : FitsEnv M lim st (DecodeErrorPushEnv n)) :
    FitsEnv M lim st (GrowAmortizedEnv (BitVec.ofNat 64 n)) := by
  rw [fitsEnv_growAmortized_iff]
  exact hfits _ (decodeErrorPushEnv_growAmortizedEvents hn)

/-! ## Cell-Unfolded `finishGrow7` Wrappers -/

abbrev FG7Ghost (σ : Type) :=
  BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) ×
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × σ

def finishGrow7ZeroCellsSpecG (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hookStack : Nat) : Spec (FG7Ghost M.σ) where
  pre := fun (out, cap, ptr, new, bs, o0, o1, o2, fsp, st) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.sp = fsp ∧ cap = 0#64 ∧ bs = [] ∧
      cap.toNat ≤ new.toNat ∧ 0 < new.toNat ∧ new.toNat * 32 + 8 ≤ 2 ^ 63 ∧
      FitsEvents M lim st (rustAllocEvents (new.toNat * 32) 8)⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.pool lim st s ∗ stackAt fsp (hookStack + 32)
  post := fun (out, _cap, _ptr, new, _bs, _o0, _o1, _o2, fsp, st) s0 sf =>
    ∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ p'.toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
      (out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ p') ∗
      ((out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * 32)) ∗
      A.live p' (new.toNat * 32) 8 ∗ memRegion p' (new.toNat * 32) ∗
      A.pool lim (M.stepEvents (rustAllocEvents (new.toNat * 32) 8) st) sf ∗
      stackAt fsp (hookStack + 32)

theorem finish_grow_7_zero_cells_of_spec {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {addr : BitVec 64} {hookStack : Nat}
    (hfg : subroutine_ok P addr (finishGrow7SpecWithStack M A lim hookStack)) :
    subroutine_ok P addr (finishGrow7ZeroCellsSpecG M A lim hookStack) := by
  refine subroutine_ok_outcome_intro
    fun ⟨out, cap, ptr, new, bs, o0, o1, o2, fsp, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [finishGrow7ZeroCellsSpecG, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hfsp, hcap0, hbs, hle, hpos, hbound, hfits⟩, hmem⟩
  subst hfsp; subst hcap0; subst hbs
  let hcall : FinishGrow1Call := ⟨out, 0#64, ptr, new, []⟩
  have hfits_env : FitsEnv M lim st (FinishGrow7Env hcall) := by
    rw [fitsEnv_finishGrow7_iff]
    simpa only [finishGrow7Events, hcall, ↓reduceIte] using hfits
  have hpre' : s0.mem ⊨ (finishGrow7SpecWithStack M A lim hookStack).pre (hcall, st) s0 ∗ R := by
    simp only [finishGrow7SpecWithStack, hcall,
      CryptoVerification.SpqrV1.Alloc.FinishGrow1Call.oldBuf32, ite_true,
      memRegion_24, emp_sepConj, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, fun _ => trivial, Nat.zero_le _, hle, hpos, hbound, hfits_env⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  refine hfg.mono_outcome (hcall, st) R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | hfail)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simpa only [finishGrow7SpecWithStack, finishGrow7ZeroCellsSpecG, hcall,
      finishGrow7Events, ↓reduceIte,
      pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj] using hq
  · exact Or.inr hfail

def finishGrow7NeCellsSpecG (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hookStack : Nat) : Spec (FG7Ghost M.σ) where
  pre := fun (out, cap, ptr, new, bs, o0, o1, o2, fsp, st) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.sp = fsp ∧ cap ≠ 0#64 ∧
      bs.length ≤ cap.toNat * 32 ∧ cap.toNat ≤ new.toNat ∧
      0 < new.toNat ∧ new.toNat * 32 + 8 ≤ 2 ^ 63 ∧
      FitsEvents M lim st (rustReallocEvents (cap.toNat * 32) (new.toNat * 32) 8)⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.live ptr (cap.toNat * 32) 8 ∗ (ptr ↦ₛ bs) ∗
    memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat * 32 - bs.length) ∗
    A.pool lim st s ∗ stackAt fsp (hookStack + 32)
  post := fun (out, cap, _ptr, new, bs, _o0, _o1, _o2, fsp, st) s0 sf =>
    ∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ p'.toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
      (out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ p') ∗
      ((out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * 32)) ∗
      A.live p' (new.toNat * 32) 8 ∗ (p' ↦ₛ bs) ∗
      memRegion (p' + BitVec.ofNat 64 bs.length) (new.toNat * 32 - bs.length) ∗
      A.pool lim (M.stepEvents (rustReallocEvents (cap.toNat * 32) (new.toNat * 32) 8) st) sf ∗
      stackAt fsp (hookStack + 32)

theorem finish_grow_7_ne_cells_of_spec {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {addr : BitVec 64} {hookStack : Nat}
    (hfg : subroutine_ok P addr (finishGrow7SpecWithStack M A lim hookStack)) :
    subroutine_ok P addr (finishGrow7NeCellsSpecG M A lim hookStack) := by
  refine subroutine_ok_outcome_intro
    fun ⟨out, cap, ptr, new, bs, o0, o1, o2, fsp, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [finishGrow7NeCellsSpecG, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hfsp, hcap, hbs, hle, hpos, hbound, hfits⟩, hmem⟩
  subst hfsp
  let hcall : FinishGrow1Call := ⟨out, cap, ptr, new, bs⟩
  have hfits_env : FitsEnv M lim st (FinishGrow7Env hcall) := by
    rw [fitsEnv_finishGrow7_iff]
    simpa only [finishGrow7Events, hcall, hcap, ↓reduceIte] using hfits
  have hpre' : s0.mem ⊨ (finishGrow7SpecWithStack M A lim hookStack).pre (hcall, st) s0 ∗ R := by
    simp only [finishGrow7SpecWithStack, hcall,
      CryptoVerification.SpqrV1.Alloc.FinishGrow1Call.oldBuf32, hcap, ite_false,
      RustCliAllocBudget.repAlloc_live_norm,
      memRegion_24, sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, False.elim, hbs, hle, hpos, hbound, hfits_env⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  refine hfg.mono_outcome (hcall, st) R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | hfail)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simpa only [finishGrow7SpecWithStack, finishGrow7NeCellsSpecG, hcall,
      finishGrow7Events, hcap, ↓reduceIte] using hq
  · exact Or.inr hfail

/-! ## Budget Contracts -/

/-- Budget contract of `grow_amortized` preserving an initialized byte prefix `x.bs`. -/
def growAmortizedBsSpecWithStack (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hookStack : Nat) : Spec (GrowAmortizedCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.v ∧ s.readReg64 .x1 = x.cap ∧
      x.bs.length ≤ x.cap.toNat * 32 ∧ x.cap.toNat < 2 ^ 32 ∧ x.ptr ≠ 0#64 ∧
      FitsEnv M lim st (GrowAmortizedEnv x.cap)⌝ ∗
    (x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
    x.oldBuf A.repAlloc ∗ A.pool lim st s ∗ stackAt s.sp ((hookStack + 32) + 64)
  post := fun (x, st) s0 sf =>
    ∃∗ p' : BitVec 64,
      ⌜sf.readReg64 .x0 = 0xffffffffffffffff#64 ∧ p' ≠ 0#64 ∧ p'.toNat % 8 = 0 ∧
        sf.trace = s0.trace⌝ ∗
      (x.v ↦₆₄ newCap32 x.cap) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
      A.live p' ((newCap32 x.cap).toNat * 32) 8 ∗ (p' ↦ₛ x.bs) ∗
      memRegion (p' + BitVec.ofNat 64 x.bs.length) ((newCap32 x.cap).toNat * 32 - x.bs.length) ∗
      A.pool lim (M.stepEvents (growAmortizedEvents x.cap) st) sf ∗
      stackAt s0.sp ((hookStack + 32) + 64)

abbrev growAmortizedBsSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (GrowAmortizedCall × M.σ) :=
  growAmortizedBsSpecWithStack M A lim allocHookStack

abbrev growAmortizedBsSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (GrowAmortizedCall × M.σ) :=
  growAmortizedBsSpecWithStack M A lim extHookStack

/-- Budget contract of `grow_amortized` on an uninitialized buffer (`bs = []`). -/
def growAmortizedSpecWithStack (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hookStack : Nat) :
    Spec ((BitVec 64 × BitVec 64 × BitVec 64) × M.σ) where
  pre := fun ((v, cap, ptr), st) s =>
    ⌜s.readReg64 .x0 = v ∧ s.readReg64 .x1 = cap ∧
      cap.toNat < 2 ^ 32 ∧ ptr ≠ 0#64 ∧
      FitsEnv M lim st (GrowAmortizedEnv cap)⌝ ∗
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
    (if cap = 0#64 then emp
     else A.live ptr (cap.toNat * 32) 8 ∗ memRegion ptr (cap.toNat * 32)) ∗
    A.pool lim st s ∗ stackAt s.sp ((hookStack + 32) + 64)
  post := fun ((v, cap, _ptr), st) s0 sf =>
    ∃∗ p' : BitVec 64,
      ⌜sf.readReg64 .x0 = 0xffffffffffffffff#64 ∧ p' ≠ 0#64 ∧ p'.toNat % 8 = 0 ∧
        sf.trace = s0.trace⌝ ∗
      (v ↦₆₄ newCap32 cap) ∗ ((v + 8#64) ↦₆₄ p') ∗
      A.live p' ((newCap32 cap).toNat * 32) 8 ∗ memRegion p' ((newCap32 cap).toNat * 32) ∗
      A.pool lim (M.stepEvents (growAmortizedEvents cap) st) sf ∗
      stackAt s0.sp ((hookStack + 32) + 64)

abbrev growAmortizedSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec ((BitVec 64 × BitVec 64 × BitVec 64) × M.σ) :=
  growAmortizedSpecWithStack M A lim allocHookStack

abbrev growAmortizedSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec ((BitVec 64 × BitVec 64 × BitVec 64) × M.σ) :=
  growAmortizedSpecWithStack M A lim extHookStack

/-- Budget contract of `RawVec<(&str, &str)>::grow_one` preserving an initialized byte prefix `x.bs`. -/
def growOneStrPairBsSpecWithStack (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hookStack : Nat) : Spec (GrowAmortizedCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.v ∧ x.bs.length ≤ x.cap.toNat * 32 ∧
      x.cap.toNat < 2 ^ 32 ∧ x.ptr ≠ 0#64 ∧
      FitsEnv M lim st (GrowAmortizedEnv x.cap)⌝ ∗
    (x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
    x.oldBuf A.repAlloc ∗ A.pool lim st s ∗ stackAt s.sp (((hookStack + 32) + 64) + 16)
  post := fun (x, st) s0 sf =>
    ∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ p'.toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
      (x.v ↦₆₄ newCap32 x.cap) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
      A.live p' ((newCap32 x.cap).toNat * 32) 8 ∗ (p' ↦ₛ x.bs) ∗
      memRegion (p' + BitVec.ofNat 64 x.bs.length) ((newCap32 x.cap).toNat * 32 - x.bs.length) ∗
      A.pool lim (M.stepEvents (growAmortizedEvents x.cap) st) sf ∗
      stackAt s0.sp (((hookStack + 32) + 64) + 16)

abbrev growOneStrPairBsSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (GrowAmortizedCall × M.σ) :=
  growOneStrPairBsSpecWithStack M A lim allocHookStack

abbrev growOneStrPairBsSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (GrowAmortizedCall × M.σ) :=
  growOneStrPairBsSpecWithStack M A lim extHookStack

/-- Budget contract of `RawVec<(&str, &str)>::grow_one` on an uninitialized buffer (`bs = []`). -/
def growOneStrPairSpecWithStack (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hookStack : Nat) :
    Spec ((BitVec 64 × BitVec 64 × BitVec 64) × M.σ) where
  pre := fun ((v, cap, ptr), st) s =>
    ⌜s.readReg64 .x0 = v ∧ cap.toNat < 2 ^ 32 ∧ ptr ≠ 0#64 ∧
      FitsEnv M lim st (GrowAmortizedEnv cap)⌝ ∗
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
    (if cap = 0#64 then emp
     else A.live ptr (cap.toNat * 32) 8 ∗ memRegion ptr (cap.toNat * 32)) ∗
    A.pool lim st s ∗ stackAt s.sp (((hookStack + 32) + 64) + 16)
  post := fun ((v, cap, _ptr), st) s0 sf =>
    ∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ p'.toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
      (v ↦₆₄ newCap32 cap) ∗ ((v + 8#64) ↦₆₄ p') ∗
      A.live p' ((newCap32 cap).toNat * 32) 8 ∗ memRegion p' ((newCap32 cap).toNat * 32) ∗
      A.pool lim (M.stepEvents (growAmortizedEvents cap) st) sf ∗
      stackAt s0.sp (((hookStack + 32) + 64) + 16)

abbrev growOneStrPairSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec ((BitVec 64 × BitVec 64 × BitVec 64) × M.σ) :=
  growOneStrPairSpecWithStack M A lim allocHookStack

abbrev growOneStrPairSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec ((BitVec 64 × BitVec 64 × BitVec 64) × M.σ) :=
  growOneStrPairSpecWithStack M A lim extHookStack

/-! ## Relocatable Proofs (Blocks 260 and 258) -/

section PlacedProofs
attribute [local irreducible] FitsEvents

theorem grow_amortized_bs_placed_ok_of_fg [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : (hookStack + 32) + 8 * 8 ≤ 2 ^ 64)
    (hfg : subroutine_ok ((blkPC_259).rebase (blkPl_259).base H)
      (blkPl_259).base (finishGrow7SpecWithStack M A lim hookStack)) :
    subroutine_ok ((blkPC_260).rebase (blkPl_260).base H)
      (blkPl_260).base
      (withLsCodeLoaded lsmpl (growAmortizedBsSpecWithStack M A lim hookStack)) := by
  unfold withLsCodeLoaded growAmortizedBsSpecWithStack GrowAmortizedCall.oldBuf
  simp only [stackAt_growAmortized_gen _ hhook]
  cells_unfold
  wp_init x s0
  rcases x with ⟨⟨v, cap, ptr, bs⟩, st⟩
  dsimp only at *
  have hcl : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hbs_le : bs.length ≤ cap.toNat * 32 := by assumption
  have hcap_lt : cap.toNat < 2 ^ 32 := by assumption
  have hfits_env : FitsEnv M lim st (GrowAmortizedEnv cap) := by assumption
  have hnew_eq := grow_amortized_new_eq hcap_lt
  have hnew_toNat : (newCap32 cap).toNat = max (2 * cap.toNat) 4 := newCap32_toNat hcap_lt
  have hcap_le_new : cap.toNat ≤ (newCap32 cap).toNat := by omega
  have hnew_pos : 0 < (newCap32 cap).toNat := by omega
  have hnew_bound : (newCap32 cap).toNat * 32 + 8 ≤ 2 ^ 63 := by omega
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hbs_le)
    subst hbs
    have hfits : FitsEvents M lim st (rustAllocEvents ((newCap32 0#64).toNat * 32) 8) := by
      rw [fitsEnv_growAmortized_iff] at hfits_env
      simpa only [growAmortizedEvents, ↓reduceIte] using hfits_env
    simp only [ite_true, emp_sepConj, pointsToBytes_nil, List.length_nil,
      BitVec.add_zero, Nat.sub_zero, growAmortizedEvents]
    apply sepWP_seq_lscl hcl (mid := lsmpl.base 259)
    wp_steps_sync_pool (lsmpl.base 259)
    simp only [State.setMem_setMem]
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) ?_
    intro hcl_m
    have hfg0 := lscall_blk (callerProg := (blkPC_260).rebase (blkPl_260).base H)
      (finish_grow_7_zero_cells_of_spec hfg) hcl_m
    wp_call hfg0 (s0.sp - 56#64, 0#64, ptr, newCap32 0#64, [], v_stk_1, v_stk_2, v_stk_3,
      s0.sp - 64#64, st)
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem, (by decide : newCap32 0#64 = 4#64)]
    wp_done
  · have hfits : FitsEvents M lim st
        (rustReallocEvents (cap.toNat * 32) ((newCap32 cap).toNat * 32) 8) := by
      rw [fitsEnv_growAmortized_iff] at hfits_env
      simpa only [growAmortizedEvents, hcap0, ↓reduceIte] using hfits_env
    simp only [hcap0, ite_false, growAmortizedEvents, sepConj_assoc]
    apply sepWP_seq_lscl hcl (mid := lsmpl.base 259)
    wp_steps_sync_pool (lsmpl.base 259)
    simp only [State.setMem_setMem]
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) ?_
    intro hcl_m
    have hfg1 := lscall_blk (callerProg := (blkPC_260).rebase (blkPl_260).base H)
      (finish_grow_7_ne_cells_of_spec hfg) hcl_m
    wp_call hfg1 (s0.sp - 56#64, cap, ptr, newCap32 cap, bs, v_stk_1, v_stk_2, v_stk_3,
      s0.sp - 64#64, st)
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    wp_done

end PlacedProofs

theorem grow_amortized_spec_placed_of_bs [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {P : Program} {addr : BitVec 64}
    {hookStack : Nat}
    (hbs : subroutine_ok P addr
      (withLsCodeLoaded lsmpl (growAmortizedBsSpecWithStack M A lim hookStack))) :
    subroutine_ok P addr
      (withLsCodeLoaded lsmpl (growAmortizedSpecWithStack M A lim hookStack)) := by
  refine subroutine_ok_outcome_intro fun ⟨⟨v, cap, ptr⟩, st⟩ R s0 hpc hrun hpre hsp => ?_
  let x : GrowAmortizedCall := ⟨v, cap, ptr, []⟩
  have hpre' : s0.mem ⊨
      (withLsCodeLoaded lsmpl (growAmortizedBsSpecWithStack M A lim hookStack)).pre (x, st) s0 ∗ R := by
    simp only [growAmortizedSpecWithStack, growAmortizedBsSpecWithStack,
      GrowAmortizedCall.oldBuf, x, RustCliAllocBudget.repAlloc_live_norm,
      pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj,
      sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hcap, hptr, hfits⟩, hmem⟩
    exact ⟨⟨hx0, hx1, Nat.zero_le _, hcap, hptr, hfits⟩, hmem⟩
  refine hbs.mono_outcome (x, st) R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | hfail)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simpa only [growAmortizedSpecWithStack, growAmortizedBsSpecWithStack,
      GrowAmortizedCall.oldBuf, x,
      pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj] using hq
  · exact Or.inr hfail

private def growAmortizedCallSpecG (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hookStack : Nat) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64 × M.σ) where
  pre := fun (v, cap, ptr, bs, gsp, st) s =>
    ⌜s.readReg64 .x0 = v ∧ s.readReg64 .x1 = cap ∧ s.sp = gsp ∧
      bs.length ≤ cap.toNat * 32 ∧ cap.toNat < 2 ^ 32 ∧ ptr ≠ 0#64 ∧
      FitsEnv M lim st (GrowAmortizedEnv cap)⌝ ∗
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
    (GrowAmortizedCall.mk v cap ptr bs).oldBuf A.repAlloc ∗
    A.pool lim st s ∗ stackAt gsp ((hookStack + 32) + 64)
  post := fun (v, cap, _ptr, bs, gsp, st) s0 sf =>
    ∃∗ p' : BitVec 64,
      ⌜sf.readReg64 .x0 = 0xffffffffffffffff#64 ∧ p' ≠ 0#64 ∧ p'.toNat % 8 = 0 ∧
        sf.trace = s0.trace⌝ ∗
      (v ↦₆₄ newCap32 cap) ∗ ((v + 8#64) ↦₆₄ p') ∗
      A.live p' ((newCap32 cap).toNat * 32) 8 ∗ (p' ↦ₛ bs) ∗
      memRegion (p' + BitVec.ofNat 64 bs.length) ((newCap32 cap).toNat * 32 - bs.length) ∗
      A.pool lim (M.stepEvents (growAmortizedEvents cap) st) sf ∗
      stackAt gsp ((hookStack + 32) + 64)

private theorem grow_amortized_call_placed_ok_of_bs [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {P : Program} {addr : BitVec 64}
    {hookStack : Nat}
    (hbs : subroutine_ok P addr
      (withLsCodeLoaded lsmpl (growAmortizedBsSpecWithStack M A lim hookStack))) :
    subroutine_ok P addr
      (withLsCodeLoaded lsmpl (growAmortizedCallSpecG M A lim hookStack)) := by
  refine subroutine_ok_outcome_intro fun ⟨v, cap, ptr, bs, gsp, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [growAmortizedCallSpecG, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hgsp, hbs_le, hcap, hptr, hfits⟩, hmem⟩
  subst hgsp
  let x : GrowAmortizedCall := ⟨v, cap, ptr, bs⟩
  have hpre' : s0.mem ⊨
      (withLsCodeLoaded lsmpl (growAmortizedBsSpecWithStack M A lim hookStack)).pre (x, st) s0 ∗ R := by
    simp only [growAmortizedBsSpecWithStack, x, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hbs_le, hcap, hptr, hfits⟩, hmem⟩
  exact hbs.mono_outcome (x, st) R s0 hpc hrun hpre' hsp fun _ hout => hout

theorem grow_one_str_pair_bs_placed_ok_of_ga [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : ((hookStack + 32) + 64) + 2 * 8 ≤ 2 ^ 64)
    (_h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hga_bs : subroutine_ok ((blkPC_260).rebase (blkPl_260).base H)
      (blkPl_260).base
      (withLsCodeLoaded lsmpl (growAmortizedBsSpecWithStack M A lim hookStack))) :
    subroutine_ok ((blkPC_258).rebase (blkPl_258).base H)
      (blkPl_258).base
      (withLsCodeLoaded lsmpl (growOneStrPairBsSpecWithStack M A lim hookStack)) := by
  unfold withLsCodeLoaded growOneStrPairBsSpecWithStack
  simp only [stackAt_growOneStrPair_gen _ hhook]
  cells_unfold
  wp_init x s0
  rcases x with ⟨⟨v, cap, ptr, bs⟩, st⟩
  dsimp only at *
  have hcl : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  apply sepWP_seq_lscl hcl (mid := lsmpl.base 260)
  wp_steps_sync_pool (lsmpl.base 260)
  simp only [State.setMem_setMem]
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) ?_
  intro hcl_m
  have hga := lscall_blk_cl (callerProg := (blkPC_258).rebase (blkPl_258).base H)
    (grow_amortized_call_placed_ok_of_bs hga_bs) hcl_m
  wp_call hga (v, cap, ptr, bs, s0.sp - 16#64, st)
  wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
  simp only [State.setMem_setMem]
  wp_done

theorem grow_one_str_pair_spec_placed_of_bs [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {P : Program} {addr : BitVec 64}
    {hookStack : Nat}
    (hbs : subroutine_ok P addr
      (withLsCodeLoaded lsmpl (growOneStrPairBsSpecWithStack M A lim hookStack))) :
    subroutine_ok P addr
      (withLsCodeLoaded lsmpl (growOneStrPairSpecWithStack M A lim hookStack)) := by
  refine subroutine_ok_outcome_intro fun ⟨⟨v, cap, ptr⟩, st⟩ R s0 hpc hrun hpre hsp => ?_
  let x : GrowAmortizedCall := ⟨v, cap, ptr, []⟩
  have hpre' : s0.mem ⊨
      (withLsCodeLoaded lsmpl (growOneStrPairBsSpecWithStack M A lim hookStack)).pre (x, st) s0 ∗ R := by
    simp only [growOneStrPairSpecWithStack, growOneStrPairBsSpecWithStack,
      GrowAmortizedCall.oldBuf, x, RustCliAllocBudget.repAlloc_live_norm,
      pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj,
      sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hcap, hptr, hfits⟩, hmem⟩
    exact ⟨⟨hx0, Nat.zero_le _, hcap, hptr, hfits⟩, hmem⟩
  refine hbs.mono_outcome (x, st) R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | hfail)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simpa only [growOneStrPairSpecWithStack, growOneStrPairBsSpecWithStack,
      GrowAmortizedCall.oldBuf, x,
      pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj] using hq
  · exact Or.inr hfail

/-! ## `HookSat` Corollaries -/

theorem grow_amortized_bs_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_260).rebase (blkPl_260).base H)
      (blkPl_260).base (withLsCodeLoaded lsmpl (growAmortizedBsSpec M A lim)) :=
  grow_amortized_bs_placed_ok_of_fg (by decide) (finish_grow_7_placed_ok hshim halloc hrealloc)

theorem grow_amortized_bs_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_260).rebase (blkPl_260).base H)
      (blkPl_260).base (withLsCodeLoaded lsmpl (growAmortizedBsSpecX M A lim)) :=
  grow_amortized_bs_placed_ok_of_fg (by decide) (finish_grow_7_placed_ok_x hshim halloc hrealloc)

theorem grow_amortized_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_260).rebase (blkPl_260).base H)
      (blkPl_260).base (withLsCodeLoaded lsmpl (growAmortizedSpec M A lim)) :=
  grow_amortized_spec_placed_of_bs (grow_amortized_bs_placed_ok hshim halloc hrealloc)

theorem grow_amortized_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_260).rebase (blkPl_260).base H)
      (blkPl_260).base (withLsCodeLoaded lsmpl (growAmortizedSpecX M A lim)) :=
  grow_amortized_spec_placed_of_bs (grow_amortized_bs_placed_ok_x hshim halloc hrealloc)

theorem grow_one_str_pair_bs_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_258).rebase (blkPl_258).base H)
      (blkPl_258).base (withLsCodeLoaded lsmpl (growOneStrPairBsSpec M A lim)) :=
  grow_one_str_pair_bs_placed_ok_of_ga (by decide) h_panic
    (grow_amortized_bs_placed_ok hshim halloc hrealloc)

theorem grow_one_str_pair_bs_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_258).rebase (blkPl_258).base H)
      (blkPl_258).base (withLsCodeLoaded lsmpl (growOneStrPairBsSpecX M A lim)) :=
  grow_one_str_pair_bs_placed_ok_of_ga (by decide) h_panic
    (grow_amortized_bs_placed_ok_x hshim halloc hrealloc)

theorem grow_one_str_pair_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_258).rebase (blkPl_258).base H)
      (blkPl_258).base (withLsCodeLoaded lsmpl (growOneStrPairSpec M A lim)) :=
  grow_one_str_pair_spec_placed_of_bs (grow_one_str_pair_bs_placed_ok h_panic hshim halloc hrealloc)

theorem grow_one_str_pair_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_258).rebase (blkPl_258).base H)
      (blkPl_258).base (withLsCodeLoaded lsmpl (growOneStrPairSpecX M A lim)) :=
  grow_one_str_pair_spec_placed_of_bs
    (grow_one_str_pair_bs_placed_ok_x h_panic hshim halloc hrealloc)

end LibsignalBinary.Proofs.SpqrV1.Alloc.GrowAmortizedBudget

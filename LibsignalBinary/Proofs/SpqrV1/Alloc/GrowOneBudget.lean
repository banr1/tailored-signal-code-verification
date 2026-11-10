/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Placed.GenLsBlock
public import LibsignalBinary.Proofs.SpqrV1.Alloc.FinishGrowBudget
public import LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOne
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Alloc.Fetch
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable `RawVec<{ChainEpoch, Pt, Poly, GF16, &[Pt]}>::grow_one`

Proves `RustCliAllocBudget M` / `AllocCallPreserved` `[LibsignalPlacement]` contracts
for blocks 356..360 calling block 361 (`finish_grow [local#8]`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneBudget

open Arm64 ProofLib
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement
  blkPC_356 blkPC_357 blkPC_358 blkPC_359 blkPC_360 blkPC_361
  blkPl_356 blkPl_357 blkPl_358 blkPl_359 blkPl_360 blkPl_361
  lscall_blk lsmpl lsρ sepWP_seq_lscl withLsCodeLoaded
)
open CryptoVerification.RustHeap (RustAlloc allocHookStack)
open CryptoVerification.LibsignalTripleRatchet (FinishGrowCall extHookStack finishGrowStack)
open CryptoVerification.SpqrV1.Alloc (
  GrowGhost growOneChainEpochName growOneGF16Name growOnePolyName
  growOnePtName growOnePtSliceName growOneStack
  spqrHandleErrorSym spqrRustAllocSym spqrRustNoAllocShimSym spqrRustReallocSym
  spqr_externAt?_of_mem spqr_hook_ok_of_mem
)
open CryptoVerification.SpqrV1.Alloc.GrowOneNorm (
  readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre
  readReg64_setPC_pre readReg_setMem_setPC_pre readReg_setPC_pre
  sp_setMem_setPC_pre sp_setPC_pre
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents
  RustCliAllocBudget RustLayoutOk
  rustAllocEvents rustCliAllocBudgetSpec rustCliReallocBudgetSpec rustReallocEvents
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  rustCliAllocNoOomExternSpecWithStack rustCliReallocNoOomExternSpecWithStack
  subroutine_ok_allocNoOom_externWithStack_of_hookSat
  subroutine_ok_reallocNoOom_externWithStack_of_hookSat
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  FinishGrowEnv finishGrowEvents finishGrowSpecWithStack fitsEnv_finishGrow_iff noAllocShimSpec
)
open LibsignalBinary.Proofs.SpqrV1.Alloc.FinishGrowBudget (
  finishGrow8AllocSpecG finishGrow8ReallocSpecG
  finish_grow_8_ne_placed_ok_of_hooks finish_grow_8_zero_placed_ok_of_hooks
  memRegion_24 session2ShimSpecWithStack session2ShimWithStack_of_noAllocShim
)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg_setPC_pre readReg_setMem_setPC_pre

/-! ## Stack and Arithmetic Helpers -/

private theorem stackAt_growOne_gen (sp : BitVec 64) {hookStack : Nat}
    (hhook : (hookStack + 48) + 8 * 8 ≤ 2 ^ 64) :
    stackAt sp ((hookStack + 48) + 64) =
      stackAt (sp - 64#64) (hookStack + 48) ∗ cells (sp - 64#64) 8 :=
  ProofLib.stackAt_split_cells sp (hookStack + 48) 8 hhook

private theorem grow_new_cap_eq {cap : BitVec 64} (h : max (2 * cap.toNat) 4 < 2 ^ 63) :
    (if (4#64).ult (cap <<< 1) = true then cap <<< 1 else 4#64) =
      BitVec.ofNat 64 (max (2 * cap.toNat) 4) := by
  have hsh : (cap <<< 1).toNat = 2 * cap.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    change (cap.toNat * 2) % 2 ^ 64 = 2 * cap.toNat
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  have h4 : (4#64 : BitVec 64).toNat = 4 := rfl
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  by_cases hc : (4#64).ult (cap <<< 1) = true
  · simp only [hc, ite_true, hsh]
    rw [BitVec.ult_eq_decide, decide_eq_true_eq, h4, hsh] at hc; omega
  · simp only [hc, Bool.false_eq_true, ite_false]
    rw [BitVec.ult_eq_decide, decide_eq_true_eq, h4, hsh] at hc
    change 4 = max (2 * cap.toNat) 4; omega

/-! ## Cell-Unfolded `finish_grow [local#8]` (Block 361) -/

abbrev FG8CellsGhost (σ : Type) :=
  BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) ×
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × σ

def finishGrow8ZeroCellsSpecG (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hookStack : Nat) : Spec (FG8CellsGhost M.σ) where
  pre := fun (out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp, st) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.readReg64 .x4 = align ∧ s.readReg64 .x5 = stride ∧
      s.sp = fsp ∧ cap = 0#64 ∧ bs = [] ∧ cap.toNat ≤ new.toNat ∧
      0 < new.toNat ∧ 0 < stride.toNat ∧
      RustLayoutOk (new.toNat * stride.toNat) align.toNat ∧
      FitsEvents M lim st (rustAllocEvents (new.toNat * stride.toNat) align.toNat)⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.pool lim st s ∗ stackAt fsp (hookStack + 48)
  post := fun (out, _cap, _ptr, new, align, stride, _bs, _o0, _o1, _o2, fsp, st) s0 sf =>
    ∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ p'.toNat % align.toNat = 0 ∧ sf.trace = s0.trace⌝ ∗
      (out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ p') ∗
      ((out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * stride.toNat)) ∗
      A.live p' (new.toNat * stride.toNat) align.toNat ∗
      memRegion p' (new.toNat * stride.toNat) ∗
      A.pool lim (M.stepEvents (rustAllocEvents (new.toNat * stride.toNat) align.toNat) st) sf ∗
      stackAt fsp (hookStack + 48)

def finishGrow8NeCellsSpecG (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hookStack : Nat) : Spec (FG8CellsGhost M.σ) where
  pre := fun (out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp, st) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.readReg64 .x4 = align ∧ s.readReg64 .x5 = stride ∧
      s.sp = fsp ∧ cap ≠ 0#64 ∧ bs.length ≤ cap.toNat * stride.toNat ∧ cap.toNat ≤ new.toNat ∧
      0 < new.toNat ∧ 0 < stride.toNat ∧
      RustLayoutOk (new.toNat * stride.toNat) align.toNat ∧
      FitsEvents M lim st
        (rustReallocEvents (cap.toNat * stride.toNat) (new.toNat * stride.toNat) align.toNat)⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.live ptr (cap.toNat * stride.toNat) align.toNat ∗ (ptr ↦ₛ bs) ∗
    memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat * stride.toNat - bs.length) ∗
    A.pool lim st s ∗ stackAt fsp (hookStack + 48)
  post := fun (out, cap, _ptr, new, align, stride, bs, _o0, _o1, _o2, fsp, st) s0 sf =>
    ∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ p'.toNat % align.toNat = 0 ∧ sf.trace = s0.trace⌝ ∗
      (out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ p') ∗
      ((out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * stride.toNat)) ∗
      A.live p' (new.toNat * stride.toNat) align.toNat ∗ (p' ↦ₛ bs) ∗
      memRegion (p' + BitVec.ofNat 64 bs.length) (new.toNat * stride.toNat - bs.length) ∗
      A.pool lim
        (M.stepEvents
          (rustReallocEvents (cap.toNat * stride.toNat) (new.toNat * stride.toNat) align.toNat) st)
        sf ∗
      stackAt fsp (hookStack + 48)

theorem finish_grow_8_zero_cells_of_alloc {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {hookStack : Nat} {P : Program} {addr : BitVec 64}
    (hfg : subroutine_ok P addr (finishGrow8AllocSpecG M A lim hookStack)) :
    subroutine_ok P addr (finishGrow8ZeroCellsSpecG M A lim hookStack) := by
  refine subroutine_ok_outcome_intro
    fun ⟨out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [finishGrow8ZeroCellsSpecG, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap0, hbs, hle, hpos, hstr, hlay, hfits⟩,
    hmem⟩
  subst hfsp; subst hcap0; subst hbs
  let hcall : FinishGrowCall := ⟨out, 0#64, ptr, new, align, stride, []⟩
  have hfits_env : FitsEnv M lim st (FinishGrowEnv hcall) := by
    simp only [fitsEnv_finishGrow_iff, finishGrowEvents, hcall, BitVec.toNat_zero, ↓reduceIte]
    exact hfits
  have hpre' : s0.mem ⊨ (finishGrow8AllocSpecG M A lim hookStack).pre (hcall, st) s0 ∗ R := by
    simp only [finishGrow8AllocSpecG, hcall, memRegion_24,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, trivial, trivial, hle, hpos, hstr, hlay, hfits_env⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  refine hfg.mono_outcome (hcall, st) R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | hfail
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [finishGrow8AllocSpecG, finishGrowSpecWithStack, finishGrow8ZeroCellsSpecG, hcall,
      finishGrowEvents, BitVec.toNat_zero, ↓reduceIte, pointsToBytes_nil, List.length_nil,
      BitVec.add_zero, Nat.sub_zero, emp_sepConj,
      sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨p', hq⟩
    exact ⟨p', by simpa only [sepConj_assoc] using hq⟩
  · exact Or.inr hfail

theorem finish_grow_8_ne_cells_of_realloc {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {hookStack : Nat} {P : Program} {addr : BitVec 64}
    (hfg : subroutine_ok P addr (finishGrow8ReallocSpecG M A lim hookStack)) :
    subroutine_ok P addr (finishGrow8NeCellsSpecG M A lim hookStack) := by
  refine subroutine_ok_outcome_intro
    fun ⟨out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [finishGrow8NeCellsSpecG, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap, hbs, hle, hpos, hstr, hlay, hfits⟩,
    hmem⟩
  subst hfsp
  have hcap_nat : cap.toNat ≠ 0 := fun hc => hcap (BitVec.eq_of_toNat_eq hc)
  let hcall : FinishGrowCall := ⟨out, cap, ptr, new, align, stride, bs⟩
  have hfits_env : FitsEnv M lim st (FinishGrowEnv hcall) := by
    simp only [fitsEnv_finishGrow_iff, finishGrowEvents, hcall, hcap_nat, ↓reduceIte]
    exact hfits
  have hpre' : s0.mem ⊨ (finishGrow8ReallocSpecG M A lim hookStack).pre (hcall, st) s0 ∗ R := by
    simp only [finishGrow8ReallocSpecG, hcall, memRegion_24,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hcap, hbs, hle, hpos, hstr, hlay, hfits_env⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  refine hfg.mono_outcome (hcall, st) R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | hfail
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [finishGrow8ReallocSpecG, finishGrowSpecWithStack, finishGrow8NeCellsSpecG, hcall,
      finishGrowEvents, hcap_nat, ↓reduceIte,
      sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨p', hq⟩
    exact ⟨p', by simpa only [sepConj_assoc] using hq⟩
  · exact Or.inr hfail

theorem finish_grow_8_zero_cells_of_fg8 {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {hookStack : Nat} {P : Program} {addr : BitVec 64}
    (hfg : subroutine_ok P addr (finishGrowSpecWithStack M A lim hookStack)) :
    subroutine_ok P addr (finishGrow8ZeroCellsSpecG M A lim hookStack) := by
  refine finish_grow_8_zero_cells_of_alloc ?_
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [finishGrow8AllocSpecG, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hcap0, hbs, hle, hpos, hstr, hlay, hfits⟩, hmem⟩
  rw [hcap0] at hx1 hle
  have hpre' : s0.mem ⊨ (finishGrowSpecWithStack M A lim hookStack).pre (x, st) s0 ∗ R := by
    simp only [finishGrowSpecWithStack, FinishGrowCall.oldBuf, hcap0, ite_true, emp_sepConj,
      sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, fun _ => hbs, hbs ▸ Nat.zero_le _,
      hle, hpos, hstr, hlay, hfits⟩, hmem⟩
  exact hfg.mono_outcome (x, st) R s0 hpc hrun hpre' hsp fun _ hout => hout

theorem finish_grow_8_ne_cells_of_fg8 {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {hookStack : Nat} {P : Program} {addr : BitVec 64}
    (hfg : subroutine_ok P addr (finishGrowSpecWithStack M A lim hookStack)) :
    subroutine_ok P addr (finishGrow8NeCellsSpecG M A lim hookStack) := by
  refine finish_grow_8_ne_cells_of_realloc ?_
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [finishGrow8ReallocSpecG, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hcap, hbs, hle, hpos, hstr, hlay, hfits⟩, hmem⟩
  have hpre' : s0.mem ⊨ (finishGrowSpecWithStack M A lim hookStack).pre (x, st) s0 ∗ R := by
    simp only [finishGrowSpecWithStack, FinishGrowCall.oldBuf, hcap, ite_false,
      RustCliAllocBudget.repAlloc_live_norm, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, False.elim, hbs,
      hle, hpos, hstr, hlay, hfits⟩, hmem⟩
  exact hfg.mono_outcome (x, st) R s0 hpc hrun hpre' hsp fun _ hout => hout

theorem finish_grow_8_zero_cells_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : hookStack + 6 * 8 ≤ 2 ^ 64)
    (hshim : subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (lsρ spqrRustNoAllocShimSym) (session2ShimSpecWithStack hookStack))
    (halloc : subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (lsρ spqrRustAllocSym) (rustCliAllocNoOomExternSpecWithStack M A lim false hookStack)) :
    subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (blkPl_361).base (finishGrow8ZeroCellsSpecG M A lim hookStack) :=
  finish_grow_8_zero_cells_of_alloc (finish_grow_8_zero_placed_ok_of_hooks hhook hshim halloc)

theorem finish_grow_8_ne_cells_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : hookStack + 6 * 8 ≤ 2 ^ 64)
    (hrealloc : subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (lsρ spqrRustReallocSym) (rustCliReallocNoOomExternSpecWithStack M A lim hookStack)) :
    subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (blkPl_361).base (finishGrow8NeCellsSpecG M A lim hookStack) :=
  finish_grow_8_ne_cells_of_realloc (finish_grow_8_ne_placed_ok_of_hooks hhook hrealloc)

theorem finish_grow_8_zero_cells_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hge : hookStack ≥ allocHookStack) (hhook : hookStack + 6 * 8 ≤ 2 ^ 64)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (blkPl_361).base (finishGrow8ZeroCellsSpecG M A lim hookStack) :=
  finish_grow_8_zero_cells_placed_ok_of_hooks hhook
    (session2ShimWithStack_of_noAllocShim hookStack (spqr_hook_ok_of_mem hshim))
    (subroutine_ok_allocNoOom_externWithStack_of_hookSat halloc spqr_externAt?_of_mem hge (by omega))

theorem finish_grow_8_ne_cells_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hge : hookStack ≥ allocHookStack) (hhook : hookStack + 6 * 8 ≤ 2 ^ 64)
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (blkPl_361).base (finishGrow8NeCellsSpecG M A lim hookStack) :=
  finish_grow_8_ne_cells_placed_ok_of_hooks hhook
    (subroutine_ok_reallocNoOom_externWithStack_of_hookSat hrealloc spqr_externAt?_of_mem hge
      (by omega))

/-! ## Generic `(stride, align)` Budget Specifications -/

/-- Deterministic allocator events of `RawVec<T>::grow_one` (`stride > 1`). -/
def growOneStrideEvents (cap : BitVec 64) (stride align : Nat) : List AllocEvent :=
  if cap = 0#64 then rustAllocEvents (4 * stride) align
  else rustReallocEvents (cap.toNat * stride) (max (2 * cap.toNat) 4 * stride) align

def GrowOneStrideEnv (cap : BitVec 64) (stride align : Nat) (evs : List AllocEvent) : Prop :=
  evs = growOneStrideEvents cap stride align

theorem fitsEnv_growOneStride_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (cap : BitVec 64) (stride align : Nat) :
    FitsEnv M lim st (GrowOneStrideEnv cap stride align) ↔
      FitsEvents M lim st (growOneStrideEvents cap stride align) :=
  FitsEnv.eq_iff

/-- Prefix-preserving budget contract for `RawVec<T>::grow_one` (`stride > 1`). -/
def growOneStrideBsSpecWithStack (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stride align hookStack : Nat) : Spec (GrowGhost × M.σ) where
  pre := fun ((v, cap, ptr, bs), st) s =>
    ⌜s.readReg64 .x0 = v ∧ bs.length ≤ cap.toNat * stride ∧ ptr ≠ 0#64 ∧
      max (2 * cap.toNat) 4 * stride + align ≤ 2 ^ 63 ∧
      FitsEnv M lim st (GrowOneStrideEnv cap stride align)⌝ ∗
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
    (if cap = 0#64 then emp
     else A.live ptr (cap.toNat * stride) align ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat * stride - bs.length)) ∗
    A.pool lim st s ∗ stackAt s.sp ((hookStack + 48) + 64)
  post := fun ((v, cap, _, bs), st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ p'.toNat % align = 0⌝ ∗
      (v ↦₆₄ BitVec.ofNat 64 (max (2 * cap.toNat) 4)) ∗ ((v + 8#64) ↦₆₄ p') ∗
      A.live p' (max (2 * cap.toNat) 4 * stride) align ∗ (p' ↦ₛ bs) ∗
      memRegion (p' + BitVec.ofNat 64 bs.length) (max (2 * cap.toNat) 4 * stride - bs.length)) ∗
    A.pool lim (M.stepEvents (growOneStrideEvents cap stride align) st) sf ∗
    stackAt s0.sp ((hookStack + 48) + 64)

/-- Full-buffer budget contract for `RawVec<T>::grow_one` (`bs.length = cap.toNat * stride`). -/
def growOneStrideFullSpecWithStack (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stride align hookStack : Nat) : Spec (GrowGhost × M.σ) where
  pre := fun ((v, cap, ptr, bs), st) s =>
    ⌜s.readReg64 .x0 = v ∧ bs.length = cap.toNat * stride ∧ ptr ≠ 0#64 ∧
      max (2 * cap.toNat) 4 * stride + align ≤ 2 ^ 63 ∧
      FitsEnv M lim st (GrowOneStrideEnv cap stride align)⌝ ∗
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
    (if cap = 0#64 then emp else A.live ptr bs.length align ∗ (ptr ↦ₛ bs)) ∗
    A.pool lim st s ∗ stackAt s.sp ((hookStack + 48) + 64)
  post := fun ((v, cap, _, bs), st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ p'.toNat % align = 0⌝ ∗
      (v ↦₆₄ BitVec.ofNat 64 (max (2 * cap.toNat) 4)) ∗ ((v + 8#64) ↦₆₄ p') ∗
      A.live p' (max (2 * cap.toNat) 4 * stride) align ∗ (p' ↦ₛ bs) ∗
      memRegion (p' + BitVec.ofNat 64 bs.length) ((max (2 * cap.toNat) 4 - cap.toNat) * stride)) ∗
    A.pool lim (M.stepEvents (growOneStrideEvents cap stride align) st) sf ∗
    stackAt s0.sp ((hookStack + 48) + 64)

/-- Uninitialized (`memRegion`) budget contract for `RawVec<T>::grow_one` (`bs = []`). -/
def growOneStrideEmptySpecWithStack (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stride align hookStack : Nat) :
    Spec ((BitVec 64 × BitVec 64 × BitVec 64) × M.σ) where
  pre := fun ((v, cap, ptr), st) s =>
    ⌜s.readReg64 .x0 = v ∧ ptr ≠ 0#64 ∧
      max (2 * cap.toNat) 4 * stride + align ≤ 2 ^ 63 ∧
      FitsEnv M lim st (GrowOneStrideEnv cap stride align)⌝ ∗
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
    (if cap = 0#64 then emp
     else A.live ptr (cap.toNat * stride) align ∗ memRegion ptr (cap.toNat * stride)) ∗
    A.pool lim st s ∗ stackAt s.sp ((hookStack + 48) + 64)
  post := fun ((v, cap, _ptr), st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ p'.toNat % align = 0⌝ ∗
      (v ↦₆₄ BitVec.ofNat 64 (max (2 * cap.toNat) 4)) ∗ ((v + 8#64) ↦₆₄ p') ∗
      A.live p' (max (2 * cap.toNat) 4 * stride) align ∗
      memRegion p' (max (2 * cap.toNat) 4 * stride)) ∗
    A.pool lim (M.stepEvents (growOneStrideEvents cap stride align) st) sf ∗
    stackAt s0.sp ((hookStack + 48) + 64)

abbrev growOneStrideBsSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stride align : Nat) :=
  growOneStrideBsSpecWithStack M A lim stride align allocHookStack

abbrev growOneStrideFullSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stride align : Nat) :=
  growOneStrideFullSpecWithStack M A lim stride align allocHookStack

abbrev growOneStrideEmptySpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stride align : Nat) :=
  growOneStrideEmptySpecWithStack M A lim stride align allocHookStack

abbrev growOneStrideBsSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stride align : Nat) :=
  growOneStrideBsSpecWithStack M A lim stride align extHookStack

abbrev growOneStrideFullSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stride align : Nat) :=
  growOneStrideFullSpecWithStack M A lim stride align extHookStack

abbrev growOneStrideEmptySpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stride align : Nat) :=
  growOneStrideEmptySpecWithStack M A lim stride align extHookStack

abbrev growOneChainEpochBsSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :=
  growOneStrideBsSpec M A lim 112 8
abbrev growOneChainEpochFullSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :=
  growOneStrideFullSpec M A lim 112 8
abbrev growOneChainEpochSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :=
  growOneStrideEmptySpec M A lim 112 8

abbrev growOnePtBsSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :=
  growOneStrideBsSpec M A lim 4 2
abbrev growOnePtFullSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :=
  growOneStrideFullSpec M A lim 4 2
abbrev growOnePtSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :=
  growOneStrideEmptySpec M A lim 4 2

abbrev growOnePolyBsSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :=
  growOneStrideBsSpec M A lim 24 8
abbrev growOnePolyFullSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :=
  growOneStrideFullSpec M A lim 24 8
abbrev growOnePolySpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :=
  growOneStrideEmptySpec M A lim 24 8

abbrev growOneGF16BsSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :=
  growOneStrideBsSpec M A lim 2 2
abbrev growOneGF16FullSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :=
  growOneStrideFullSpec M A lim 2 2
abbrev growOneGF16Spec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :=
  growOneStrideEmptySpec M A lim 2 2

abbrev growOnePtSliceBsSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :=
  growOneStrideBsSpec M A lim 16 8
abbrev growOnePtSliceFullSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :=
  growOneStrideFullSpec M A lim 16 8
abbrev growOnePtSliceSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :=
  growOneStrideEmptySpec M A lim 16 8

theorem grow_one_stride_full_placed_of_bs [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {addr : BitVec 64} {stride align hookStack : Nat}
    (hbs : subroutine_ok P addr
      (withLsCodeLoaded lsmpl (growOneStrideBsSpecWithStack M A lim stride align hookStack))) :
    subroutine_ok P addr
      (withLsCodeLoaded lsmpl (growOneStrideFullSpecWithStack M A lim stride align hookStack)) := by
  refine subroutine_ok_outcome_intro fun ⟨⟨v, cap, ptr, bs⟩, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [growOneStrideFullSpecWithStack, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hlen, hptr, hbound, hfits⟩, hmem⟩
  have hpre' : s0.mem ⊨
      (withLsCodeLoaded lsmpl (growOneStrideBsSpecWithStack M A lim stride align hookStack)).pre
        ((v, cap, ptr, bs), st) s0 ∗ R := by
    simp only [growOneStrideBsSpecWithStack, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, Nat.le_of_eq hlen, hptr, hbound, hfits⟩, ?_⟩
    by_cases hcap0 : cap = 0#64
    · simpa only [hcap0, ite_true] using hmem
    · simpa only [hcap0, ite_false, ← hlen, Nat.sub_self, memRegion_zero, sepConj_emp,
        sepConj_assoc] using hmem
  refine hbs.mono_outcome ((v, cap, ptr, bs), st) R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | hfail
  · refine Or.inl ⟨hret, hcc, ?_⟩
    have hsub_mul : (max (2 * cap.toNat) 4 - cap.toNat) * stride =
        max (2 * cap.toNat) 4 * stride - bs.length := by rw [Nat.sub_mul, hlen]
    simpa only [growOneStrideBsSpecWithStack, growOneStrideFullSpecWithStack, hsub_mul] using hq
  · exact Or.inr hfail

theorem grow_one_stride_empty_placed_of_bs [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {addr : BitVec 64} {stride align hookStack : Nat}
    (hbs : subroutine_ok P addr
      (withLsCodeLoaded lsmpl (growOneStrideBsSpecWithStack M A lim stride align hookStack))) :
    subroutine_ok P addr
      (withLsCodeLoaded lsmpl (growOneStrideEmptySpecWithStack M A lim stride align hookStack)) := by
  refine subroutine_ok_outcome_intro fun ⟨⟨v, cap, ptr⟩, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [growOneStrideEmptySpecWithStack, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hptr, hbound, hfits⟩, hmem⟩
  have hpre' : s0.mem ⊨
      (withLsCodeLoaded lsmpl (growOneStrideBsSpecWithStack M A lim stride align hookStack)).pre
        ((v, cap, ptr, []), st) s0 ∗ R := by
    simp only [growOneStrideBsSpecWithStack, List.length_nil, pointsToBytes_nil,
      BitVec.add_zero, Nat.sub_zero, emp_sepConj, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, Nat.zero_le _, hptr, hbound, hfits⟩, hmem⟩
  refine hbs.mono_outcome ((v, cap, ptr, []), st) R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | hfail
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simpa only [growOneStrideBsSpecWithStack, growOneStrideEmptySpecWithStack, List.length_nil,
      pointsToBytes_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj] using hq
  · exact Or.inr hfail

/-! ## Relocatable Proofs (Blocks 356..360) -/

section PlacedGrowOneProofs
attribute [local irreducible] FitsEvents

/-- Block 356 (`RawVec<ChainEpoch>::grow_one`, `stride = 112, align = 8`). -/
theorem grow_one_chain_epoch_bs_placed_ok_of_fg [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : (hookStack + 48) + 8 * 8 ≤ 2 ^ 64)
    (_h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hfg0_blk : subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (blkPl_361).base (finishGrow8ZeroCellsSpecG M A lim hookStack))
    (hfg1_blk : subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (blkPl_361).base (finishGrow8NeCellsSpecG M A lim hookStack)) :
    subroutine_ok ((blkPC_356).rebase (blkPl_356).base H)
      (blkPl_356).base
      (withLsCodeLoaded lsmpl (growOneStrideBsSpecWithStack M A lim 112 8 hookStack)) := by
  unfold withLsCodeLoaded growOneStrideBsSpecWithStack
  simp only [stackAt_growOne_gen _ hhook]
  cells_unfold
  wp_init x s0
  rcases x with ⟨⟨v, cap, ptr, bs⟩, st⟩
  dsimp only at *
  have hcl : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hbs_le : bs.length ≤ cap.toNat * 112 := by assumption
  have hbound : max (2 * cap.toNat) 4 * 112 + 8 ≤ 2 ^ 63 := by omega
  have hfits_env : FitsEnv M lim st (GrowOneStrideEnv cap 112 8) := by assumption
  have hnew_lt63 : max (2 * cap.toNat) 4 < 2 ^ 63 := by omega
  have hnew_eq := grow_new_cap_eq hnew_lt63
  let new := BitVec.ofNat 64 (max (2 * cap.toNat) 4)
  have hnew_toNat : new.toNat = max (2 * cap.toNat) 4 := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by omega
  have hnew_pos : 0 < new.toNat := by omega
  have hpow : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have hc0 : (0#64 : BitVec 64).toNat = 0 := rfl
    have hm4 : max (2 * 0) 4 = 4 := rfl
    rw [hc0] at hbs_le hnew_toNat
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hbs
    have hfits : FitsEvents M lim st (rustAllocEvents (new.toNat * 112) 8) := by
      rw [fitsEnv_growOneStride_iff] at hfits_env
      simpa only [growOneStrideEvents, ↓reduceIte, hnew_toNat, hm4] using hfits_env
    have hnew_eq0 : (if (4#64).ult (0#64 <<< 1) = true then 0#64 <<< 1 else 4#64) = new := hnew_eq
    have hmul_eq : max (2 * 0) 4 * 112 = new.toNat * 112 := by rw [hnew_toNat]
    simp only [ite_true, emp_sepConj, pointsToBytes_nil, List.length_nil,
      BitVec.add_zero, BitVec.toNat_ofNat, Nat.zero_mod, Nat.sub_zero,
      growOneStrideEvents, hmul_eq]
    apply sepWP_seq_lscl hcl (mid := lsmpl.base 361)
    wp_steps_sync_pool (lsmpl.base 361)
    simp only [State.setMem_setMem]
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) ?_
    intro hcl_m
    have hfg0 := lscall_blk (callerProg := (blkPC_356).rebase (blkPl_356).base H) hfg0_blk hcl_m
    wp_call hfg0 (s0.sp - 56#64, 0#64, ptr, new, 8#64, 112#64, [],
      v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64, st)
    have htr : sf.trace = s0.trace := ‹sf.trace = _›.trans (by simp [wp_norm, arm64_norm])
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    wp_done
  · have hfits : FitsEvents M lim st (rustReallocEvents (cap.toNat * 112) (new.toNat * 112) 8) := by
      rw [fitsEnv_growOneStride_iff] at hfits_env
      simpa only [growOneStrideEvents, hcap0, ↓reduceIte, hnew_toNat] using hfits_env
    simp only [hcap0, ite_false, growOneStrideEvents, sepConj_assoc]
    rw [← hnew_toNat]
    apply sepWP_seq_lscl hcl (mid := lsmpl.base 361)
    wp_steps_sync_pool (lsmpl.base 361)
    simp only [State.setMem_setMem]
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) ?_
    intro hcl_m
    have hfg1 := lscall_blk (callerProg := (blkPC_356).rebase (blkPl_356).base H) hfg1_blk hcl_m
    wp_call hfg1 (s0.sp - 56#64, cap, ptr, new, 8#64, 112#64, bs,
      v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64, st)
    have htr : sf.trace = s0.trace := ‹sf.trace = _›.trans (by simp [wp_norm, arm64_norm])
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    wp_done

/-- Block 357 (`RawVec<Pt>::grow_one`, `stride = 4, align = 2`). -/
theorem grow_one_pt_bs_placed_ok_of_fg [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : (hookStack + 48) + 8 * 8 ≤ 2 ^ 64)
    (_h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hfg0_blk : subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (blkPl_361).base (finishGrow8ZeroCellsSpecG M A lim hookStack))
    (hfg1_blk : subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (blkPl_361).base (finishGrow8NeCellsSpecG M A lim hookStack)) :
    subroutine_ok ((blkPC_357).rebase (blkPl_357).base H)
      (blkPl_357).base
      (withLsCodeLoaded lsmpl (growOneStrideBsSpecWithStack M A lim 4 2 hookStack)) := by
  unfold withLsCodeLoaded growOneStrideBsSpecWithStack
  simp only [stackAt_growOne_gen _ hhook]
  cells_unfold
  wp_init x s0
  rcases x with ⟨⟨v, cap, ptr, bs⟩, st⟩
  dsimp only at *
  have hcl : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hbs_le : bs.length ≤ cap.toNat * 4 := by assumption
  have hbound : max (2 * cap.toNat) 4 * 4 + 2 ≤ 2 ^ 63 := by omega
  have hfits_env : FitsEnv M lim st (GrowOneStrideEnv cap 4 2) := by assumption
  have hnew_lt63 : max (2 * cap.toNat) 4 < 2 ^ 63 := by omega
  have hnew_eq := grow_new_cap_eq hnew_lt63
  let new := BitVec.ofNat 64 (max (2 * cap.toNat) 4)
  have hnew_toNat : new.toNat = max (2 * cap.toNat) 4 := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by omega
  have hnew_pos : 0 < new.toNat := by omega
  have hpow : ∃ k, 2 = 2 ^ k := ⟨1, rfl⟩
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have hc0 : (0#64 : BitVec 64).toNat = 0 := rfl
    have hm4 : max (2 * 0) 4 = 4 := rfl
    rw [hc0] at hbs_le hnew_toNat
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hbs
    have hfits : FitsEvents M lim st (rustAllocEvents (new.toNat * 4) 2) := by
      rw [fitsEnv_growOneStride_iff] at hfits_env
      simpa only [growOneStrideEvents, ↓reduceIte, hnew_toNat, hm4] using hfits_env
    have hnew_eq0 : (if (4#64).ult (0#64 <<< 1) = true then 0#64 <<< 1 else 4#64) = new := hnew_eq
    have hmul_eq : max (2 * 0) 4 * 4 = new.toNat * 4 := by rw [hnew_toNat]
    simp only [ite_true, emp_sepConj, pointsToBytes_nil, List.length_nil,
      BitVec.add_zero, BitVec.toNat_ofNat, Nat.zero_mod, Nat.sub_zero,
      growOneStrideEvents, hmul_eq]
    apply sepWP_seq_lscl hcl (mid := lsmpl.base 361)
    wp_steps_sync_pool (lsmpl.base 361)
    simp only [State.setMem_setMem]
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) ?_
    intro hcl_m
    have hfg0 := lscall_blk (callerProg := (blkPC_357).rebase (blkPl_357).base H) hfg0_blk hcl_m
    wp_call hfg0 (s0.sp - 56#64, 0#64, ptr, new, 2#64, 4#64, [],
      v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64, st)
    have htr : sf.trace = s0.trace := ‹sf.trace = _›.trans (by simp [wp_norm, arm64_norm])
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    wp_done
  · have hfits : FitsEvents M lim st (rustReallocEvents (cap.toNat * 4) (new.toNat * 4) 2) := by
      rw [fitsEnv_growOneStride_iff] at hfits_env
      simpa only [growOneStrideEvents, hcap0, ↓reduceIte, hnew_toNat] using hfits_env
    simp only [hcap0, ite_false, growOneStrideEvents, sepConj_assoc]
    rw [← hnew_toNat]
    apply sepWP_seq_lscl hcl (mid := lsmpl.base 361)
    wp_steps_sync_pool (lsmpl.base 361)
    simp only [State.setMem_setMem]
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) ?_
    intro hcl_m
    have hfg1 := lscall_blk (callerProg := (blkPC_357).rebase (blkPl_357).base H) hfg1_blk hcl_m
    wp_call hfg1 (s0.sp - 56#64, cap, ptr, new, 2#64, 4#64, bs,
      v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64, st)
    have htr : sf.trace = s0.trace := ‹sf.trace = _›.trans (by simp [wp_norm, arm64_norm])
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    wp_done

/-- Block 358 (`RawVec<Poly>::grow_one`, `stride = 24, align = 8`). -/
theorem grow_one_poly_bs_placed_ok_of_fg [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : (hookStack + 48) + 8 * 8 ≤ 2 ^ 64)
    (_h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hfg0_blk : subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (blkPl_361).base (finishGrow8ZeroCellsSpecG M A lim hookStack))
    (hfg1_blk : subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (blkPl_361).base (finishGrow8NeCellsSpecG M A lim hookStack)) :
    subroutine_ok ((blkPC_358).rebase (blkPl_358).base H)
      (blkPl_358).base
      (withLsCodeLoaded lsmpl (growOneStrideBsSpecWithStack M A lim 24 8 hookStack)) := by
  unfold withLsCodeLoaded growOneStrideBsSpecWithStack
  simp only [stackAt_growOne_gen _ hhook]
  cells_unfold
  wp_init x s0
  rcases x with ⟨⟨v, cap, ptr, bs⟩, st⟩
  dsimp only at *
  have hcl : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hbs_le : bs.length ≤ cap.toNat * 24 := by assumption
  have hbound : max (2 * cap.toNat) 4 * 24 + 8 ≤ 2 ^ 63 := by omega
  have hfits_env : FitsEnv M lim st (GrowOneStrideEnv cap 24 8) := by assumption
  have hnew_lt63 : max (2 * cap.toNat) 4 < 2 ^ 63 := by omega
  have hnew_eq := grow_new_cap_eq hnew_lt63
  let new := BitVec.ofNat 64 (max (2 * cap.toNat) 4)
  have hnew_toNat : new.toNat = max (2 * cap.toNat) 4 := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by omega
  have hnew_pos : 0 < new.toNat := by omega
  have hpow : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have hc0 : (0#64 : BitVec 64).toNat = 0 := rfl
    have hm4 : max (2 * 0) 4 = 4 := rfl
    rw [hc0] at hbs_le hnew_toNat
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hbs
    have hfits : FitsEvents M lim st (rustAllocEvents (new.toNat * 24) 8) := by
      rw [fitsEnv_growOneStride_iff] at hfits_env
      simpa only [growOneStrideEvents, ↓reduceIte, hnew_toNat, hm4] using hfits_env
    have hnew_eq0 : (if (4#64).ult (0#64 <<< 1) = true then 0#64 <<< 1 else 4#64) = new := hnew_eq
    have hmul_eq : max (2 * 0) 4 * 24 = new.toNat * 24 := by rw [hnew_toNat]
    simp only [ite_true, emp_sepConj, pointsToBytes_nil, List.length_nil,
      BitVec.add_zero, BitVec.toNat_ofNat, Nat.zero_mod, Nat.sub_zero,
      growOneStrideEvents, hmul_eq]
    apply sepWP_seq_lscl hcl (mid := lsmpl.base 361)
    wp_steps_sync_pool (lsmpl.base 361)
    simp only [State.setMem_setMem]
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) ?_
    intro hcl_m
    have hfg0 := lscall_blk (callerProg := (blkPC_358).rebase (blkPl_358).base H) hfg0_blk hcl_m
    wp_call hfg0 (s0.sp - 56#64, 0#64, ptr, new, 8#64, 24#64, [],
      v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64, st)
    have htr : sf.trace = s0.trace := ‹sf.trace = _›.trans (by simp [wp_norm, arm64_norm])
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    wp_done
  · have hfits : FitsEvents M lim st (rustReallocEvents (cap.toNat * 24) (new.toNat * 24) 8) := by
      rw [fitsEnv_growOneStride_iff] at hfits_env
      simpa only [growOneStrideEvents, hcap0, ↓reduceIte, hnew_toNat] using hfits_env
    simp only [hcap0, ite_false, growOneStrideEvents, sepConj_assoc]
    rw [← hnew_toNat]
    apply sepWP_seq_lscl hcl (mid := lsmpl.base 361)
    wp_steps_sync_pool (lsmpl.base 361)
    simp only [State.setMem_setMem]
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) ?_
    intro hcl_m
    have hfg1 := lscall_blk (callerProg := (blkPC_358).rebase (blkPl_358).base H) hfg1_blk hcl_m
    wp_call hfg1 (s0.sp - 56#64, cap, ptr, new, 8#64, 24#64, bs,
      v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64, st)
    have htr : sf.trace = s0.trace := ‹sf.trace = _›.trans (by simp [wp_norm, arm64_norm])
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    wp_done

/-- Block 359 (`RawVec<GF16>::grow_one`, `stride = 2, align = 2`). -/
theorem grow_one_gf16_bs_placed_ok_of_fg [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : (hookStack + 48) + 8 * 8 ≤ 2 ^ 64)
    (_h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hfg0_blk : subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (blkPl_361).base (finishGrow8ZeroCellsSpecG M A lim hookStack))
    (hfg1_blk : subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (blkPl_361).base (finishGrow8NeCellsSpecG M A lim hookStack)) :
    subroutine_ok ((blkPC_359).rebase (blkPl_359).base H)
      (blkPl_359).base
      (withLsCodeLoaded lsmpl (growOneStrideBsSpecWithStack M A lim 2 2 hookStack)) := by
  unfold withLsCodeLoaded growOneStrideBsSpecWithStack
  simp only [stackAt_growOne_gen _ hhook]
  cells_unfold
  wp_init x s0
  rcases x with ⟨⟨v, cap, ptr, bs⟩, st⟩
  dsimp only at *
  have hcl : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hbs_le : bs.length ≤ cap.toNat * 2 := by assumption
  have hbound : max (2 * cap.toNat) 4 * 2 + 2 ≤ 2 ^ 63 := by omega
  have hfits_env : FitsEnv M lim st (GrowOneStrideEnv cap 2 2) := by assumption
  have hnew_lt63 : max (2 * cap.toNat) 4 < 2 ^ 63 := by omega
  have hnew_eq := grow_new_cap_eq hnew_lt63
  let new := BitVec.ofNat 64 (max (2 * cap.toNat) 4)
  have hnew_toNat : new.toNat = max (2 * cap.toNat) 4 := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by omega
  have hnew_pos : 0 < new.toNat := by omega
  have hpow : ∃ k, 2 = 2 ^ k := ⟨1, rfl⟩
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have hc0 : (0#64 : BitVec 64).toNat = 0 := rfl
    have hm4 : max (2 * 0) 4 = 4 := rfl
    rw [hc0] at hbs_le hnew_toNat
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hbs
    have hfits : FitsEvents M lim st (rustAllocEvents (new.toNat * 2) 2) := by
      rw [fitsEnv_growOneStride_iff] at hfits_env
      simpa only [growOneStrideEvents, ↓reduceIte, hnew_toNat, hm4] using hfits_env
    have hnew_eq0 : (if (4#64).ult (0#64 <<< 1) = true then 0#64 <<< 1 else 4#64) = new := hnew_eq
    have hmul_eq : max (2 * 0) 4 * 2 = new.toNat * 2 := by rw [hnew_toNat]
    simp only [ite_true, emp_sepConj, pointsToBytes_nil, List.length_nil,
      BitVec.add_zero, BitVec.toNat_ofNat, Nat.zero_mod, Nat.sub_zero,
      growOneStrideEvents, hmul_eq]
    apply sepWP_seq_lscl hcl (mid := lsmpl.base 361)
    wp_steps_sync_pool (lsmpl.base 361)
    simp only [State.setMem_setMem]
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) ?_
    intro hcl_m
    have hfg0 := lscall_blk (callerProg := (blkPC_359).rebase (blkPl_359).base H) hfg0_blk hcl_m
    wp_call hfg0 (s0.sp - 56#64, 0#64, ptr, new, 2#64, 2#64, [],
      v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64, st)
    have htr : sf.trace = s0.trace := ‹sf.trace = _›.trans (by simp [wp_norm, arm64_norm])
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    wp_done
  · have hfits : FitsEvents M lim st (rustReallocEvents (cap.toNat * 2) (new.toNat * 2) 2) := by
      rw [fitsEnv_growOneStride_iff] at hfits_env
      simpa only [growOneStrideEvents, hcap0, ↓reduceIte, hnew_toNat] using hfits_env
    simp only [hcap0, ite_false, growOneStrideEvents, sepConj_assoc]
    rw [← hnew_toNat]
    apply sepWP_seq_lscl hcl (mid := lsmpl.base 361)
    wp_steps_sync_pool (lsmpl.base 361)
    simp only [State.setMem_setMem]
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) ?_
    intro hcl_m
    have hfg1 := lscall_blk (callerProg := (blkPC_359).rebase (blkPl_359).base H) hfg1_blk hcl_m
    wp_call hfg1 (s0.sp - 56#64, cap, ptr, new, 2#64, 2#64, bs,
      v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64, st)
    have htr : sf.trace = s0.trace := ‹sf.trace = _›.trans (by simp [wp_norm, arm64_norm])
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    wp_done

/-- Block 360 (`RawVec<&[Pt]>::grow_one`, `stride = 16, align = 8`). -/
theorem grow_one_pt_slice_bs_placed_ok_of_fg [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : (hookStack + 48) + 8 * 8 ≤ 2 ^ 64)
    (_h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hfg0_blk : subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (blkPl_361).base (finishGrow8ZeroCellsSpecG M A lim hookStack))
    (hfg1_blk : subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (blkPl_361).base (finishGrow8NeCellsSpecG M A lim hookStack)) :
    subroutine_ok ((blkPC_360).rebase (blkPl_360).base H)
      (blkPl_360).base
      (withLsCodeLoaded lsmpl (growOneStrideBsSpecWithStack M A lim 16 8 hookStack)) := by
  unfold withLsCodeLoaded growOneStrideBsSpecWithStack
  simp only [stackAt_growOne_gen _ hhook]
  cells_unfold
  wp_init x s0
  rcases x with ⟨⟨v, cap, ptr, bs⟩, st⟩
  dsimp only at *
  have hcl : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hbs_le : bs.length ≤ cap.toNat * 16 := by assumption
  have hbound : max (2 * cap.toNat) 4 * 16 + 8 ≤ 2 ^ 63 := by omega
  have hfits_env : FitsEnv M lim st (GrowOneStrideEnv cap 16 8) := by assumption
  have hnew_lt63 : max (2 * cap.toNat) 4 < 2 ^ 63 := by omega
  have hnew_eq := grow_new_cap_eq hnew_lt63
  let new := BitVec.ofNat 64 (max (2 * cap.toNat) 4)
  have hnew_toNat : new.toNat = max (2 * cap.toNat) 4 := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by omega
  have hnew_pos : 0 < new.toNat := by omega
  have hpow : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have hc0 : (0#64 : BitVec 64).toNat = 0 := rfl
    have hm4 : max (2 * 0) 4 = 4 := rfl
    rw [hc0] at hbs_le hnew_toNat
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hbs
    have hfits : FitsEvents M lim st (rustAllocEvents (new.toNat * 16) 8) := by
      rw [fitsEnv_growOneStride_iff] at hfits_env
      simpa only [growOneStrideEvents, ↓reduceIte, hnew_toNat, hm4] using hfits_env
    have hnew_eq0 : (if (4#64).ult (0#64 <<< 1) = true then 0#64 <<< 1 else 4#64) = new := hnew_eq
    have hmul_eq : max (2 * 0) 4 * 16 = new.toNat * 16 := by rw [hnew_toNat]
    simp only [ite_true, emp_sepConj, pointsToBytes_nil, List.length_nil,
      BitVec.add_zero, BitVec.toNat_ofNat, Nat.zero_mod, Nat.sub_zero,
      growOneStrideEvents, hmul_eq]
    apply sepWP_seq_lscl hcl (mid := lsmpl.base 361)
    wp_steps_sync_pool (lsmpl.base 361)
    simp only [State.setMem_setMem]
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) ?_
    intro hcl_m
    have hfg0 := lscall_blk (callerProg := (blkPC_360).rebase (blkPl_360).base H) hfg0_blk hcl_m
    wp_call hfg0 (s0.sp - 56#64, 0#64, ptr, new, 8#64, 16#64, [],
      v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64, st)
    have htr : sf.trace = s0.trace := ‹sf.trace = _›.trans (by simp [wp_norm, arm64_norm])
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    wp_done
  · have hfits : FitsEvents M lim st (rustReallocEvents (cap.toNat * 16) (new.toNat * 16) 8) := by
      rw [fitsEnv_growOneStride_iff] at hfits_env
      simpa only [growOneStrideEvents, hcap0, ↓reduceIte, hnew_toNat] using hfits_env
    simp only [hcap0, ite_false, growOneStrideEvents, sepConj_assoc]
    rw [← hnew_toNat]
    apply sepWP_seq_lscl hcl (mid := lsmpl.base 361)
    wp_steps_sync_pool (lsmpl.base 361)
    simp only [State.setMem_setMem]
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) ?_
    intro hcl_m
    have hfg1 := lscall_blk (callerProg := (blkPC_360).rebase (blkPl_360).base H) hfg1_blk hcl_m
    wp_call hfg1 (s0.sp - 56#64, cap, ptr, new, 8#64, 16#64, bs,
      v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64, st)
    have htr : sf.trace = s0.trace := ‹sf.trace = _›.trans (by simp [wp_norm, arm64_norm])
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    wp_done

end PlacedGrowOneProofs

/-! ## `HookSat` Corollaries -/

theorem grow_one_chain_epoch_bs_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_356).rebase (blkPl_356).base H)
      (blkPl_356).base (withLsCodeLoaded lsmpl (growOneChainEpochBsSpec M A lim)) :=
  grow_one_chain_epoch_bs_placed_ok_of_fg (by decide) h_panic
    (finish_grow_8_zero_cells_placed_ok (by decide) (by decide) hshim halloc)
    (finish_grow_8_ne_cells_placed_ok (by decide) (by decide) hrealloc)

theorem grow_one_chain_epoch_full_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_356).rebase (blkPl_356).base H)
      (blkPl_356).base (withLsCodeLoaded lsmpl (growOneChainEpochFullSpec M A lim)) :=
  grow_one_stride_full_placed_of_bs
    (grow_one_chain_epoch_bs_placed_ok h_panic hshim halloc hrealloc)

theorem grow_one_chain_epoch_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_356).rebase (blkPl_356).base H)
      (blkPl_356).base (withLsCodeLoaded lsmpl (growOneChainEpochSpec M A lim)) :=
  grow_one_stride_empty_placed_of_bs
    (grow_one_chain_epoch_bs_placed_ok h_panic hshim halloc hrealloc)

theorem grow_one_pt_bs_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_357).rebase (blkPl_357).base H)
      (blkPl_357).base (withLsCodeLoaded lsmpl (growOnePtBsSpec M A lim)) :=
  grow_one_pt_bs_placed_ok_of_fg (by decide) h_panic
    (finish_grow_8_zero_cells_placed_ok (by decide) (by decide) hshim halloc)
    (finish_grow_8_ne_cells_placed_ok (by decide) (by decide) hrealloc)

theorem grow_one_pt_full_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_357).rebase (blkPl_357).base H)
      (blkPl_357).base (withLsCodeLoaded lsmpl (growOnePtFullSpec M A lim)) :=
  grow_one_stride_full_placed_of_bs (grow_one_pt_bs_placed_ok h_panic hshim halloc hrealloc)

theorem grow_one_pt_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_357).rebase (blkPl_357).base H)
      (blkPl_357).base (withLsCodeLoaded lsmpl (growOnePtSpec M A lim)) :=
  grow_one_stride_empty_placed_of_bs (grow_one_pt_bs_placed_ok h_panic hshim halloc hrealloc)

theorem grow_one_poly_bs_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_358).rebase (blkPl_358).base H)
      (blkPl_358).base (withLsCodeLoaded lsmpl (growOnePolyBsSpec M A lim)) :=
  grow_one_poly_bs_placed_ok_of_fg (by decide) h_panic
    (finish_grow_8_zero_cells_placed_ok (by decide) (by decide) hshim halloc)
    (finish_grow_8_ne_cells_placed_ok (by decide) (by decide) hrealloc)

theorem grow_one_poly_full_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_358).rebase (blkPl_358).base H)
      (blkPl_358).base (withLsCodeLoaded lsmpl (growOnePolyFullSpec M A lim)) :=
  grow_one_stride_full_placed_of_bs (grow_one_poly_bs_placed_ok h_panic hshim halloc hrealloc)

theorem grow_one_poly_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_358).rebase (blkPl_358).base H)
      (blkPl_358).base (withLsCodeLoaded lsmpl (growOnePolySpec M A lim)) :=
  grow_one_stride_empty_placed_of_bs (grow_one_poly_bs_placed_ok h_panic hshim halloc hrealloc)

theorem grow_one_gf16_bs_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_359).rebase (blkPl_359).base H)
      (blkPl_359).base (withLsCodeLoaded lsmpl (growOneGF16BsSpec M A lim)) :=
  grow_one_gf16_bs_placed_ok_of_fg (by decide) h_panic
    (finish_grow_8_zero_cells_placed_ok (by decide) (by decide) hshim halloc)
    (finish_grow_8_ne_cells_placed_ok (by decide) (by decide) hrealloc)

theorem grow_one_gf16_full_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_359).rebase (blkPl_359).base H)
      (blkPl_359).base (withLsCodeLoaded lsmpl (growOneGF16FullSpec M A lim)) :=
  grow_one_stride_full_placed_of_bs (grow_one_gf16_bs_placed_ok h_panic hshim halloc hrealloc)

theorem grow_one_gf16_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_359).rebase (blkPl_359).base H)
      (blkPl_359).base (withLsCodeLoaded lsmpl (growOneGF16Spec M A lim)) :=
  grow_one_stride_empty_placed_of_bs (grow_one_gf16_bs_placed_ok h_panic hshim halloc hrealloc)

theorem grow_one_pt_slice_bs_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_360).rebase (blkPl_360).base H)
      (blkPl_360).base (withLsCodeLoaded lsmpl (growOnePtSliceBsSpec M A lim)) :=
  grow_one_pt_slice_bs_placed_ok_of_fg (by decide) h_panic
    (finish_grow_8_zero_cells_placed_ok (by decide) (by decide) hshim halloc)
    (finish_grow_8_ne_cells_placed_ok (by decide) (by decide) hrealloc)

theorem grow_one_pt_slice_full_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_360).rebase (blkPl_360).base H)
      (blkPl_360).base (withLsCodeLoaded lsmpl (growOnePtSliceFullSpec M A lim)) :=
  grow_one_stride_full_placed_of_bs (grow_one_pt_slice_bs_placed_ok h_panic hshim halloc hrealloc)

theorem grow_one_pt_slice_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_360).rebase (blkPl_360).base H)
      (blkPl_360).base (withLsCodeLoaded lsmpl (growOnePtSliceSpec M A lim)) :=
  grow_one_stride_empty_placed_of_bs (grow_one_pt_slice_bs_placed_ok h_panic hshim halloc hrealloc)

end LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneBudget

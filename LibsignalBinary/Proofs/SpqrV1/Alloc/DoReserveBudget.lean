/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserve
public import LibsignalBinary.Proofs.SpqrV1.Alloc.FinishGrowBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Alloc.Fetch
import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable `do_reserve_and_handle` (`[local#2, 4, 7]`)

Proves `RustCliAllocBudget M` / `VmPreserved` `[LibsignalPlacement]` contracts for
blocks 320 (`[local#7]`, generic `(stride, align)`), 157 (`[local#2]`, `stride = 1`), and
218 (`[local#4]`, `stride = 1`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget

open Arm64 ProofLib
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement blkPC_157 blkPC_160 blkPC_218 blkPC_221
  blkPC_320 blkPC_361 blkPl_157 blkPl_160 blkPl_218 blkPl_221 blkPl_320 blkPl_361
  lscall_blk lsmpl sepWP_seq_lscl withLsCodeLoaded withMemEq
)
open CryptoVerification.RustHeap (RustAlloc allocHookStack vecHeader vecU8At)
open CryptoVerification.LibsignalTripleRatchet (
  DoReserveCall FinishGrowCall doReserveStack doReserveStackX extHookStack
  finishGrowStack finishGrowStackX reserveCap
)
open CryptoVerification.SpqrV1.Alloc (
  DoReserveStrideCall FinishGrow1Call adds_cs_eq_false
  reserveCapStride reserveCapStride_one reserveMinCap
  reserve_new_cap_eq reserve_new_cap_stride_eq
  spqrHandleErrorSym spqrRustAllocSym spqrRustNoAllocShimSym spqrRustReallocSym
  stackAt_doReserve32_gen stackAt_doReserve_gen
)
open CryptoVerification.SpqrV1.Alloc.DoReserveNorm (
  readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre
  readReg64_setPC_pre readReg_setMem_setPC_pre readReg_setPC_pre
  sp_setMem_setPC_pre sp_setPC_pre
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents
  RustCliAllocBudget RustLayoutOk
  rustAllocEvents rustCliAllocBudgetSpec rustCliReallocBudgetSpec rustReallocEvents
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  DoReserveEnv FinishGrowEnv doReserveEvents finishGrowEvents finishGrowSpecWithStack
  fitsEnv_doReserve_iff fitsEnv_finishGrow_iff noAllocShimSpec
)
open LibsignalBinary.Proofs.SpqrV1.Alloc.FinishGrowBudget (
  FinishGrow1Env finishGrow1Events finishGrow1SpecWithStack
  finish_grow_2_placed_ok finish_grow_2_placed_ok_x
  finish_grow_4_placed_ok finish_grow_4_placed_ok_x
  finish_grow_8_placed_ok finish_grow_8_placed_ok_x
  fitsEnv_finishGrow1_iff memRegion_24
)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg_setPC_pre readReg_setMem_setPC_pre

/-! ## Re-Exported Symbols and Shared Budget Contracts -/

abbrev doReserve2Name : String := CryptoVerification.SpqrV1.Alloc.doReserve2Name
abbrev doReserve4Name : String := CryptoVerification.SpqrV1.Alloc.doReserve4Name
abbrev doReserve7Name : String := CryptoVerification.SpqrV1.Alloc.doReserve7Name
abbrev doReserve32Stack : Nat := CryptoVerification.SpqrV1.Alloc.doReserve32Stack
abbrev doReserve32StackX : Nat := CryptoVerification.SpqrV1.Alloc.doReserve32StackX

abbrev doReserveRawSpecWithStack (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hookStack : Nat) : Spec (DoReserveCall × M.σ) :=
  LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpecWithStack
    M A lim (hookStack + 48)

abbrev doReserveSpecWithStack (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hookStack : Nat) : Spec (DoReserveCall × M.σ) :=
  LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpecWithStack
    M A lim (hookStack + 48)

abbrev doReserveRawSpec := @LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpec
abbrev doReserveRawSpecX := @LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpecX
abbrev doReserveSpec := @LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpec
abbrev doReserveSpecX := @LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpecX

/-! ## Stride-Generic and 32B-Frame Budget Specs -/

/-- Deterministic allocator events of `do_reserve_and_handle` for `(stride, align)`. -/
def doReserveStrideEvents (x : DoReserveStrideCall) : List AllocEvent :=
  let newCap := reserveCapStride x.stride.toNat x.cap.toNat x.len x.additional
  if x.cap = 0#64 then rustAllocEvents (newCap * x.stride.toNat) x.align.toNat
  else rustReallocEvents (x.cap.toNat * x.stride.toNat) (newCap * x.stride.toNat) x.align.toNat

def DoReserveStrideEnv (x : DoReserveStrideCall) (evs : List AllocEvent) : Prop :=
  evs = doReserveStrideEvents x

theorem fitsEnv_doReserveStride_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (x : DoReserveStrideCall) :
    FitsEnv M lim st (DoReserveStrideEnv x) ↔ FitsEvents M lim st (doReserveStrideEvents x) :=
  FitsEnv.eq_iff

theorem doReserveStrideEvents_eq_finishGrowEvents (x : DoReserveStrideCall) :
    doReserveStrideEvents x =
      finishGrowEvents x.cap.toNat
        (reserveCapStride x.stride.toNat x.cap.toNat x.len x.additional)
        x.align.toNat x.stride.toNat := by
  unfold doReserveStrideEvents finishGrowEvents
  by_cases hcap : x.cap = 0#64
  · rw [hcap]; rfl
  · have hcap_nat : x.cap.toNat ≠ 0 := fun h0 => hcap (BitVec.eq_of_toNat_eq h0)
    simp only [hcap, hcap_nat, ↓reduceIte]

/-- Budget contract of `do_reserve_and_handle [local#7]` parameterized by callee `hookStack`. -/
def doReserveStrideRawSpecWithStack (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hookStack : Nat) : Spec (DoReserveStrideCall × M.σ) where
  pre := fun (x, st) s =>
    let newCap := reserveCapStride x.stride.toNat x.cap.toNat x.len x.additional
    ⌜s.readReg64 .x0 = x.v ∧ (s.readReg64 .x1).toNat = x.len ∧
      (s.readReg64 .x2).toNat = x.additional ∧ s.readReg64 .x3 = x.align ∧
      s.readReg64 .x4 = x.stride ∧
      x.len ≤ x.cap.toNat ∧ x.bs.length ≤ x.cap.toNat * x.stride.toNat ∧
      x.ptr ≠ 0#64 ∧ 0 < x.stride.toNat ∧
      RustLayoutOk (newCap * x.stride.toNat) x.align.toNat ∧
      FitsEnv M lim st (DoReserveStrideEnv x)⌝ ∗
    (x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
    (if x.cap = 0#64 then emp
     else A.live x.ptr (x.cap.toNat * x.stride.toNat) x.align.toNat ∗ (x.ptr ↦ₛ x.bs) ∗
       memRegion (x.ptr + BitVec.ofNat 64 x.bs.length)
         (x.cap.toNat * x.stride.toNat - x.bs.length)) ∗
    A.pool lim st s ∗ stackAt s.sp ((hookStack + 48) + 64)
  post := fun (x, st) s0 sf =>
    let newCap := reserveCapStride x.stride.toNat x.cap.toNat x.len x.additional
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ p'.toNat % x.align.toNat = 0⌝ ∗
      (x.v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
      A.live p' (newCap * x.stride.toNat) x.align.toNat ∗ (p' ↦ₛ x.bs) ∗
      memRegion (p' + BitVec.ofNat 64 x.bs.length)
        (newCap * x.stride.toNat - x.bs.length)) ∗
    A.pool lim (M.stepEvents (doReserveStrideEvents x) st) sf ∗
    stackAt s0.sp ((hookStack + 48) + 64)

abbrev doReserveStrideRawSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (DoReserveStrideCall × M.σ) :=
  doReserveStrideRawSpecWithStack M A lim allocHookStack

abbrev doReserveStrideRawSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (DoReserveStrideCall × M.σ) :=
  doReserveStrideRawSpecWithStack M A lim extHookStack

/-- Budget contract of `do_reserve_and_handle [local#2, 4]` (`stride = 1, align = 1`, 32B callee frame). -/
def doReserve1Raw32SpecWithStack (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hookStack : Nat) : Spec (DoReserveCall × M.σ) where
  pre := fun (x, st) s =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜s.readReg64 .x0 = x.v ∧ (s.readReg64 .x1).toNat = x.bs.length ∧
      (s.readReg64 .x2).toNat = x.additional ∧
      x.bs.length ≤ x.cap.toNat ∧ x.ptr ≠ 0#64 ∧ newCap + 1 ≤ 2 ^ 63 ∧
      FitsEnv M lim st (DoReserveEnv x)⌝ ∗
    (x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
    (if x.cap = 0#64 then emp
     else A.live x.ptr x.cap.toNat 1 ∗ (x.ptr ↦ₛ x.bs) ∗
       memRegion (x.ptr + BitVec.ofNat 64 x.bs.length) (x.cap.toNat - x.bs.length)) ∗
    A.pool lim st s ∗ stackAt s.sp ((hookStack + 32) + 64)
  post := fun (x, st) s0 sf =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64⌝ ∗ (x.v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
      A.live p' newCap 1 ∗ (p' ↦ₛ x.bs) ∗
      memRegion (p' + BitVec.ofNat 64 x.bs.length) (newCap - x.bs.length)) ∗
    A.pool lim (M.stepEvents (doReserveEvents x) st) sf ∗
    stackAt s0.sp ((hookStack + 32) + 64)

/-- Budget contract of `do_reserve_and_handle [local#2, 4]` framed to `(hookStack + 48) + 64`. -/
def doReserve1RawSpecWithStack (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hookStack : Nat) : Spec (DoReserveCall × M.σ) where
  pre := fun (x, st) s =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜s.readReg64 .x0 = x.v ∧ (s.readReg64 .x1).toNat = x.bs.length ∧
      (s.readReg64 .x2).toNat = x.additional ∧
      x.bs.length ≤ x.cap.toNat ∧ x.ptr ≠ 0#64 ∧ newCap + 1 ≤ 2 ^ 63 ∧
      FitsEnv M lim st (DoReserveEnv x)⌝ ∗
    (x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
    (if x.cap = 0#64 then emp
     else A.live x.ptr x.cap.toNat 1 ∗ (x.ptr ↦ₛ x.bs) ∗
       memRegion (x.ptr + BitVec.ofNat 64 x.bs.length) (x.cap.toNat - x.bs.length)) ∗
    A.pool lim st s ∗ stackAt s.sp ((hookStack + 48) + 64)
  post := fun (x, st) s0 sf =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64⌝ ∗ (x.v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
      A.live p' newCap 1 ∗ (p' ↦ₛ x.bs) ∗
      memRegion (p' + BitVec.ofNat 64 x.bs.length) (newCap - x.bs.length)) ∗
    A.pool lim (M.stepEvents (doReserveEvents x) st) sf ∗
    stackAt s0.sp ((hookStack + 48) + 64)

abbrev doReserve1Raw32Spec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (DoReserveCall × M.σ) :=
  doReserve1Raw32SpecWithStack M A lim allocHookStack

abbrev doReserve1Raw32SpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (DoReserveCall × M.σ) :=
  doReserve1Raw32SpecWithStack M A lim extHookStack

abbrev doReserve1RawSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (DoReserveCall × M.σ) :=
  doReserve1RawSpecWithStack M A lim allocHookStack

abbrev doReserve1RawSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (DoReserveCall × M.σ) :=
  doReserve1RawSpecWithStack M A lim extHookStack

/-! ## Cell-Unfolded `finish_grow` Budget Wrappers -/

abbrev FG8Ghost (σ : Type) :=
  BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) ×
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × σ

def finishGrow8ZeroCellsSpecG (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hookStack : Nat) : Spec (FG8Ghost M.σ) where
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

theorem finish_grow_8_zero_cells_of_spec {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {addr : BitVec 64} {hookStack : Nat}
    (hfg : subroutine_ok P addr (finishGrowSpecWithStack M A lim hookStack)) :
    subroutine_ok P addr (finishGrow8ZeroCellsSpecG M A lim hookStack) := by
  refine subroutine_ok_outcome_intro
    fun ⟨out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [finishGrow8ZeroCellsSpecG, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with
    ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap0, hbs, hle, hpos, hstr, hlay, hfits⟩, hmem⟩
  subst hfsp; subst hcap0; subst hbs
  let hcall : FinishGrowCall := ⟨out, 0#64, ptr, new, align, stride, []⟩
  have hfits_env : FitsEnv M lim st (FinishGrowEnv hcall) := by
    rw [fitsEnv_finishGrow_iff]
    simpa only [finishGrowEvents, hcall, BitVec.toNat_zero, ↓reduceIte] using hfits
  have hpre' : s0.mem ⊨ (finishGrowSpecWithStack M A lim hookStack).pre (hcall, st) s0 ∗ R := by
    simp only [finishGrowSpecWithStack, hcall, FinishGrowCall.oldBuf, ite_true,
      memRegion_24, emp_sepConj, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, fun _ => trivial, Nat.zero_le _,
      hle, hpos, hstr, hlay, hfits_env⟩, by simpa only [sepConj_assoc] using hmem⟩
  refine hfg.mono_outcome (hcall, st) R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | hfail)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simpa only [finishGrowSpecWithStack, finishGrow8ZeroCellsSpecG, hcall,
      finishGrowEvents, BitVec.toNat_zero, ↓reduceIte,
      pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj] using hq
  · exact Or.inr hfail

def finishGrow8NeCellsSpecG (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hookStack : Nat) : Spec (FG8Ghost M.σ) where
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

theorem finish_grow_8_ne_cells_of_spec {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {addr : BitVec 64} {hookStack : Nat}
    (hfg : subroutine_ok P addr (finishGrowSpecWithStack M A lim hookStack)) :
    subroutine_ok P addr (finishGrow8NeCellsSpecG M A lim hookStack) := by
  refine subroutine_ok_outcome_intro
    fun ⟨out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [finishGrow8NeCellsSpecG, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with
    ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap, hbs, hle, hpos, hstr, hlay, hfits⟩, hmem⟩
  subst hfsp
  have hcap_nat : cap.toNat ≠ 0 := fun h0 => hcap (BitVec.eq_of_toNat_eq h0)
  let hcall : FinishGrowCall := ⟨out, cap, ptr, new, align, stride, bs⟩
  have hfits_env : FitsEnv M lim st (FinishGrowEnv hcall) := by
    rw [fitsEnv_finishGrow_iff]
    simpa only [finishGrowEvents, hcall, hcap_nat, ↓reduceIte] using hfits
  have hpre' : s0.mem ⊨ (finishGrowSpecWithStack M A lim hookStack).pre (hcall, st) s0 ∗ R := by
    simp only [finishGrowSpecWithStack, hcall, FinishGrowCall.oldBuf, hcap, ite_false,
      RustCliAllocBudget.repAlloc_live_norm,
      memRegion_24, sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, False.elim, hbs, hle, hpos, hstr, hlay, hfits_env⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  refine hfg.mono_outcome (hcall, st) R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | hfail)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simpa only [finishGrowSpecWithStack, finishGrow8NeCellsSpecG, hcall,
      finishGrowEvents, hcap_nat, ↓reduceIte] using hq
  · exact Or.inr hfail

abbrev FG24Ghost (σ : Type) :=
  BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) ×
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × σ

def finishGrow24ZeroCellsSpecG (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hookStack : Nat) : Spec (FG24Ghost M.σ) where
  pre := fun (out, cap, ptr, new, bs, o0, o1, o2, fsp, st) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.sp = fsp ∧ cap = 0#64 ∧ bs = [] ∧
      cap.toNat ≤ new.toNat ∧ 0 < new.toNat ∧ new.toNat + 1 ≤ 2 ^ 63 ∧
      FitsEvents M lim st (rustAllocEvents new.toNat 1)⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.pool lim st s ∗ stackAt fsp (hookStack + 32)
  post := fun (out, _cap, _ptr, new, _bs, _o0, _o1, _o2, fsp, st) s0 sf =>
    ∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
      (out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ new) ∗
      A.live p' new.toNat 1 ∗ memRegion p' new.toNat ∗
      A.pool lim (M.stepEvents (rustAllocEvents new.toNat 1) st) sf ∗
      stackAt fsp (hookStack + 32)

theorem finish_grow_24_zero_cells_of_spec {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {addr : BitVec 64} {hookStack : Nat}
    (hfg : subroutine_ok P addr (finishGrow1SpecWithStack M A lim hookStack)) :
    subroutine_ok P addr (finishGrow24ZeroCellsSpecG M A lim hookStack) := by
  refine subroutine_ok_outcome_intro
    fun ⟨out, cap, ptr, new, bs, o0, o1, o2, fsp, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [finishGrow24ZeroCellsSpecG, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hfsp, hcap0, hbs, hle, hpos, hbound, hfits⟩, hmem⟩
  subst hfsp; subst hcap0; subst hbs
  let hcall : FinishGrow1Call := ⟨out, 0#64, ptr, new, []⟩
  have hfits_env : FitsEnv M lim st (FinishGrow1Env hcall) := by
    rw [fitsEnv_finishGrow1_iff]
    simpa only [finishGrow1Events, hcall, ↓reduceIte] using hfits
  have hpre' : s0.mem ⊨ (finishGrow1SpecWithStack M A lim hookStack).pre (hcall, st) s0 ∗ R := by
    simp only [finishGrow1SpecWithStack, hcall,
      CryptoVerification.SpqrV1.Alloc.FinishGrow1Call.oldBuf, ite_true,
      memRegion_24, emp_sepConj, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, fun _ => trivial, Nat.zero_le _, hle, hpos, hbound, hfits_env⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  refine hfg.mono_outcome (hcall, st) R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | hfail)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simpa only [finishGrow1SpecWithStack, finishGrow24ZeroCellsSpecG, hcall,
      finishGrow1Events, ↓reduceIte,
      pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj] using hq
  · exact Or.inr hfail

def finishGrow24NeCellsSpecG (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hookStack : Nat) : Spec (FG24Ghost M.σ) where
  pre := fun (out, cap, ptr, new, bs, o0, o1, o2, fsp, st) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.sp = fsp ∧ cap ≠ 0#64 ∧
      bs.length ≤ cap.toNat ∧ cap.toNat ≤ new.toNat ∧
      0 < new.toNat ∧ new.toNat + 1 ≤ 2 ^ 63 ∧
      FitsEvents M lim st (rustReallocEvents cap.toNat new.toNat 1)⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
    memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
    A.pool lim st s ∗ stackAt fsp (hookStack + 32)
  post := fun (out, cap, _ptr, new, bs, _o0, _o1, _o2, fsp, st) s0 sf =>
    ∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
      (out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ new) ∗
      A.live p' new.toNat 1 ∗ (p' ↦ₛ bs) ∗
      memRegion (p' + BitVec.ofNat 64 bs.length) (new.toNat - bs.length) ∗
      A.pool lim (M.stepEvents (rustReallocEvents cap.toNat new.toNat 1) st) sf ∗
      stackAt fsp (hookStack + 32)

theorem finish_grow_24_ne_cells_of_spec {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {addr : BitVec 64} {hookStack : Nat}
    (hfg : subroutine_ok P addr (finishGrow1SpecWithStack M A lim hookStack)) :
    subroutine_ok P addr (finishGrow24NeCellsSpecG M A lim hookStack) := by
  refine subroutine_ok_outcome_intro
    fun ⟨out, cap, ptr, new, bs, o0, o1, o2, fsp, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [finishGrow24NeCellsSpecG, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hfsp, hcap, hbs, hle, hpos, hbound, hfits⟩, hmem⟩
  subst hfsp
  let hcall : FinishGrow1Call := ⟨out, cap, ptr, new, bs⟩
  have hfits_env : FitsEnv M lim st (FinishGrow1Env hcall) := by
    rw [fitsEnv_finishGrow1_iff]
    simpa only [finishGrow1Events, hcall, hcap, ↓reduceIte] using hfits
  have hpre' : s0.mem ⊨ (finishGrow1SpecWithStack M A lim hookStack).pre (hcall, st) s0 ∗ R := by
    simp only [finishGrow1SpecWithStack, hcall,
      CryptoVerification.SpqrV1.Alloc.FinishGrow1Call.oldBuf, hcap, ite_false,
      RustCliAllocBudget.repAlloc_live_norm,
      memRegion_24, sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, False.elim, hbs, hle, hpos, hbound, hfits_env⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  refine hfg.mono_outcome (hcall, st) R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | hfail)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simpa only [finishGrow1SpecWithStack, finishGrow24NeCellsSpecG, hcall,
      finishGrow1Events, hcap, ↓reduceIte] using hq
  · exact Or.inr hfail

/-! ## Relocatable Proofs (Blocks 320, 157, and 218) -/

theorem do_reserve_7_stride_raw_placed_ok_of_fg [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : (hookStack + 48) + 8 * 8 ≤ 2 ^ 64)
    (_h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hfg : subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (blkPl_361).base
      (finishGrowSpecWithStack M A lim hookStack)) :
    subroutine_ok ((blkPC_320).rebase (blkPl_320).base H)
      (blkPl_320).base
      (withLsCodeLoaded lsmpl (doReserveStrideRawSpecWithStack M A lim hookStack)) := by
  unfold withLsCodeLoaded doReserveStrideRawSpecWithStack
  simp only [stackAt_doReserve_gen _ hhook, sepExists_sepConj_right]
  wp_init x s0
  rcases x with ⟨⟨v, cap, ptr, bs, len, additional, align, stride⟩, st⟩
  dsimp only at *
  have hcl : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hx1_eq : (s0.readReg64 .x1).toNat = len := by assumption
  have hx2_eq : (s0.readReg64 .x2).toNat = additional := by assumption
  have hlen_le_cap : len ≤ cap.toNat := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat * stride.toNat := by assumption
  have hptr_ne : ptr ≠ 0#64 := by assumption
  have hstr_pos : 0 < stride.toNat := by assumption
  have hrlay : RustLayoutOk
      (reserveCapStride stride.toNat cap.toNat len additional * stride.toNat) align.toNat := by
    assumption
  have hfits_env : FitsEnv M lim st
      (DoReserveStrideEnv ⟨v, cap, ptr, bs, len, additional, align, stride⟩) := by
    assumption
  have hlay := hrlay.1
  have hal_le := hrlay.2
  have halign_pos : 1 ≤ align.toNat := by
    rcases hlay.2.1 with ⟨k, hk⟩; rw [hk]; exact Nat.one_le_two_pow
  have hmin_ge : 4 ≤ reserveMinCap stride.toNat := by
    unfold reserveMinCap; split <;> omega
  have hbound :
      reserveCapStride stride.toNat cap.toNat len additional * stride.toNat + align.toNat ≤
        2 ^ 63 := hlay.2.2
  have hnew_lt63 : reserveCapStride stride.toNat cap.toNat len additional < 2 ^ 63 := by
    have : reserveCapStride stride.toNat cap.toNat len additional * 1 ≤
        reserveCapStride stride.toNat cap.toNat len additional * stride.toNat :=
      Nat.mul_le_mul_left _ hstr_pos
    omega
  have hmax : max (max (len + additional) (2 * cap.toNat)) (reserveMinCap stride.toNat) < 2 ^ 63 :=
    hnew_lt63
  have hcs := adds_cs_eq_false (x2 := s0.readReg64 .x2) (x1 := s0.readReg64 .x1) (by
    rw [hx2_eq, hx1_eq]; omega)
  have hnew_eq := reserve_new_cap_stride_eq (stride := stride) (cap := cap) hx1_eq hx2_eq hnew_lt63
  let new := BitVec.ofNat 64 (reserveCapStride stride.toNat cap.toNat len additional)
  have hnew_toNat : new.toNat = reserveCapStride stride.toNat cap.toNat len additional := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by
    rw [hnew_toNat]; dsimp [reserveCapStride]; omega
  have hnew_pos : 0 < new.toNat := by
    rw [hnew_toNat]; dsimp [reserveCapStride]; omega
  have hnew_rlay : RustLayoutOk (new.toNat * stride.toNat) align.toNat := by
    rw [hnew_toNat]; exact hrlay
  have hmul_pos : 0 < new.toNat * stride.toNat := hnew_rlay.1.1
  have hpow_al : ∃ k, align.toNat = 2 ^ k := hnew_rlay.1.2.1
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have h0_mul : (0#64 : BitVec 64).toNat * stride.toNat = 0 := Nat.zero_mul stride.toNat
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hbs
    have hfits : FitsEvents M lim st (rustAllocEvents (new.toNat * stride.toNat) align.toNat) := by
      rw [fitsEnv_doReserveStride_iff] at hfits_env
      simpa only [doReserveStrideEvents, ↓reduceIte, hnew_toNat] using hfits_env
    have hnew_eq0 :
        (if (if (stride == 1#64) = true then 8#64 else 4#64).ult
              (if (0#64).ult (s0.readReg64 .x2 + s0.readReg64 .x1) = true then
                s0.readReg64 .x2 + s0.readReg64 .x1
               else 0#64) = true then
          if (0#64).ult (s0.readReg64 .x2 + s0.readReg64 .x1) = true then
            s0.readReg64 .x2 + s0.readReg64 .x1
          else 0#64
         else if (stride == 1#64) = true then 8#64 else 4#64) = new := hnew_eq
    have hmul_eq : reserveCapStride stride.toNat 0 len additional * stride.toNat =
        new.toNat * stride.toNat := by
      rw [hnew_toNat]; rfl
    simp only [emp_sepConj, pointsToBytes_nil,
      List.length_nil, BitVec.add_zero, Nat.sub_zero, BitVec.toNat_ofNat, Nat.zero_mod,
      doReserveStrideEvents, ↓reduceIte, hmul_eq]
    apply sepWP_seq_lscl hcl (mid := lsmpl.base 361)
    wp_steps_sync_pool (lsmpl.base 361)
    simp only [State.setMem_setMem]
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) ?_
    intro hcl_m
    have hfg0 := lscall_blk (callerProg := (blkPC_320).rebase (blkPl_320).base H)
      (finish_grow_8_zero_cells_of_spec hfg) hcl_m
    wp_call hfg0
      (s0.sp - 56#64, 0#64, ptr, new, align, stride, [], v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64, st)
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    wp_done
  · have hfits : FitsEvents M lim st
        (rustReallocEvents (cap.toNat * stride.toNat) (new.toNat * stride.toNat) align.toNat) := by
      rw [fitsEnv_doReserveStride_iff] at hfits_env
      simpa only [doReserveStrideEvents, hcap0, ↓reduceIte, hnew_toNat] using hfits_env
    simp only [hcap0, doReserveStrideEvents, ↓reduceIte, sepConj_assoc]
    have hsub_eq :
        reserveCapStride stride.toNat cap.toNat len additional * stride.toNat - bs.length =
          new.toNat * stride.toNat - bs.length := by rw [hnew_toNat]
    have hmul_eq :
        reserveCapStride stride.toNat cap.toNat len additional * stride.toNat =
          new.toNat * stride.toNat := by rw [hnew_toNat]
    rw [hsub_eq, hmul_eq]
    apply sepWP_seq_lscl hcl (mid := lsmpl.base 361)
    wp_steps_sync_pool (lsmpl.base 361)
    simp only [State.setMem_setMem]
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) ?_
    intro hcl_m
    have hfg1 := lscall_blk (callerProg := (blkPC_320).rebase (blkPl_320).base H)
      (finish_grow_8_ne_cells_of_spec hfg) hcl_m
    wp_call hfg1
      (s0.sp - 56#64, cap, ptr, new, align, stride, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64, st)
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    wp_done

theorem do_reserve_2_raw32_placed_ok_of_fg [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : (hookStack + 32) + 8 * 8 ≤ 2 ^ 64)
    (_h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hfg : subroutine_ok ((blkPC_160).rebase (blkPl_160).base H)
      (blkPl_160).base
      (finishGrow1SpecWithStack M A lim hookStack)) :
    subroutine_ok ((blkPC_157).rebase (blkPl_157).base H)
      (blkPl_157).base
      (withLsCodeLoaded lsmpl (doReserve1Raw32SpecWithStack M A lim hookStack)) := by
  unfold withLsCodeLoaded doReserve1Raw32SpecWithStack
  simp only [stackAt_doReserve32_gen _ hhook, sepExists_sepConj_right]
  wp_init x s0
  rcases x with ⟨⟨v, cap, ptr, bs, additional⟩, st⟩
  dsimp only at *
  have hcl : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hx1_eq : (s0.readReg64 .x1).toNat = bs.length := by assumption
  have hx2_eq : (s0.readReg64 .x2).toNat = additional := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat := by assumption
  have hbound : reserveCap cap.toNat bs.length additional + 1 ≤ 2 ^ 63 := by omega
  have hfits_env : FitsEnv M lim st (DoReserveEnv ⟨v, cap, ptr, bs, additional⟩) := by assumption
  have hcs := adds_cs_eq_false (x2 := s0.readReg64 .x2) (x1 := s0.readReg64 .x1) (by
    dsimp [reserveCap] at hbound; rw [hx2_eq, hx1_eq]; omega)
  have hnew_eq := reserve_new_cap_eq (cap := cap) hx1_eq hx2_eq hbound
  let new := BitVec.ofNat 64 (reserveCap cap.toNat bs.length additional)
  have hnew_toNat : new.toNat = reserveCap cap.toNat bs.length additional := by
    dsimp [new, reserveCap] at hbound ⊢; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by dsimp [reserveCap] at hnew_toNat; omega
  have hnew_pos : 0 < new.toNat := by dsimp [reserveCap] at hnew_toNat; omega
  have hnew_bound : new.toNat + 1 ≤ 2 ^ 63 := by omega
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hbs_le_cap)
    subst hbs
    have hfits : FitsEvents M lim st (rustAllocEvents new.toNat 1) := by
      rw [fitsEnv_doReserve_iff] at hfits_env
      simpa only [doReserveEvents, ↓reduceIte, hnew_toNat] using hfits_env
    have hnew_eq0 :
        (if (8#64).ult
              (if (0#64).ult (s0.readReg64 .x2 + s0.readReg64 .x1) = true then
                s0.readReg64 .x2 + s0.readReg64 .x1
               else 0#64) = true then
          if (0#64).ult (s0.readReg64 .x2 + s0.readReg64 .x1) = true then
            s0.readReg64 .x2 + s0.readReg64 .x1
          else 0#64
         else 8#64) = new := hnew_eq
    simp only [emp_sepConj, pointsToBytes_nil,
      List.length_nil, BitVec.add_zero, Nat.sub_zero, doReserveEvents, ↓reduceIte]
    rw [show reserveCap (0#64 : BitVec 64).toNat 0 additional = new.toNat from hnew_toNat.symm]
    apply sepWP_seq_lscl hcl (mid := lsmpl.base 160)
    wp_steps_sync_pool (lsmpl.base 160)
    simp only [State.setMem_setMem]
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) ?_
    intro hcl_m
    have hfg0 := lscall_blk (callerProg := (blkPC_157).rebase (blkPl_157).base H)
      (finish_grow_24_zero_cells_of_spec hfg) hcl_m
    wp_call hfg0 (s0.sp - 56#64, 0#64, ptr, new, [], v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64, st)
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    wp_done
  · have hfits : FitsEvents M lim st (rustReallocEvents cap.toNat new.toNat 1) := by
      rw [fitsEnv_doReserve_iff] at hfits_env
      simpa only [doReserveEvents, hcap0, ↓reduceIte, hnew_toNat] using hfits_env
    simp only [hcap0, doReserveEvents, ↓reduceIte, sepConj_assoc]
    rw [← hnew_toNat]
    apply sepWP_seq_lscl hcl (mid := lsmpl.base 160)
    wp_steps_sync_pool (lsmpl.base 160)
    simp only [State.setMem_setMem]
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) ?_
    intro hcl_m
    have hfg1 := lscall_blk (callerProg := (blkPC_157).rebase (blkPl_157).base H)
      (finish_grow_24_ne_cells_of_spec hfg) hcl_m
    wp_call hfg1 (s0.sp - 56#64, cap, ptr, new, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64, st)
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    wp_done

theorem do_reserve_4_raw32_placed_ok_of_fg [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : (hookStack + 32) + 8 * 8 ≤ 2 ^ 64)
    (_h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hfg : subroutine_ok ((blkPC_221).rebase (blkPl_221).base H)
      (blkPl_221).base
      (finishGrow1SpecWithStack M A lim hookStack)) :
    subroutine_ok ((blkPC_218).rebase (blkPl_218).base H)
      (blkPl_218).base
      (withLsCodeLoaded lsmpl (doReserve1Raw32SpecWithStack M A lim hookStack)) := by
  unfold withLsCodeLoaded doReserve1Raw32SpecWithStack
  simp only [stackAt_doReserve32_gen _ hhook, sepExists_sepConj_right]
  wp_init x s0
  rcases x with ⟨⟨v, cap, ptr, bs, additional⟩, st⟩
  dsimp only at *
  have hcl : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hx1_eq : (s0.readReg64 .x1).toNat = bs.length := by assumption
  have hx2_eq : (s0.readReg64 .x2).toNat = additional := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat := by assumption
  have hbound : reserveCap cap.toNat bs.length additional + 1 ≤ 2 ^ 63 := by omega
  have hfits_env : FitsEnv M lim st (DoReserveEnv ⟨v, cap, ptr, bs, additional⟩) := by assumption
  have hcs := adds_cs_eq_false (x2 := s0.readReg64 .x2) (x1 := s0.readReg64 .x1) (by
    dsimp [reserveCap] at hbound; rw [hx2_eq, hx1_eq]; omega)
  have hnew_eq := reserve_new_cap_eq (cap := cap) hx1_eq hx2_eq hbound
  let new := BitVec.ofNat 64 (reserveCap cap.toNat bs.length additional)
  have hnew_toNat : new.toNat = reserveCap cap.toNat bs.length additional := by
    dsimp [new, reserveCap] at hbound ⊢; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by dsimp [reserveCap] at hnew_toNat; omega
  have hnew_pos : 0 < new.toNat := by dsimp [reserveCap] at hnew_toNat; omega
  have hnew_bound : new.toNat + 1 ≤ 2 ^ 63 := by omega
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hbs_le_cap)
    subst hbs
    have hfits : FitsEvents M lim st (rustAllocEvents new.toNat 1) := by
      rw [fitsEnv_doReserve_iff] at hfits_env
      simpa only [doReserveEvents, ↓reduceIte, hnew_toNat] using hfits_env
    have hnew_eq0 :
        (if (8#64).ult
              (if (0#64).ult (s0.readReg64 .x2 + s0.readReg64 .x1) = true then
                s0.readReg64 .x2 + s0.readReg64 .x1
               else 0#64) = true then
          if (0#64).ult (s0.readReg64 .x2 + s0.readReg64 .x1) = true then
            s0.readReg64 .x2 + s0.readReg64 .x1
          else 0#64
         else 8#64) = new := hnew_eq
    simp only [emp_sepConj, pointsToBytes_nil,
      List.length_nil, BitVec.add_zero, Nat.sub_zero, doReserveEvents, ↓reduceIte]
    rw [show reserveCap (0#64 : BitVec 64).toNat 0 additional = new.toNat from hnew_toNat.symm]
    apply sepWP_seq_lscl hcl (mid := lsmpl.base 221)
    wp_steps_sync_pool (lsmpl.base 221)
    simp only [State.setMem_setMem]
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) ?_
    intro hcl_m
    have hfg0 := lscall_blk (callerProg := (blkPC_218).rebase (blkPl_218).base H)
      (finish_grow_24_zero_cells_of_spec hfg) hcl_m
    wp_call hfg0 (s0.sp - 56#64, 0#64, ptr, new, [], v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64, st)
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    wp_done
  · have hfits : FitsEvents M lim st (rustReallocEvents cap.toNat new.toNat 1) := by
      rw [fitsEnv_doReserve_iff] at hfits_env
      simpa only [doReserveEvents, hcap0, ↓reduceIte, hnew_toNat] using hfits_env
    simp only [hcap0, doReserveEvents, ↓reduceIte, sepConj_assoc]
    rw [← hnew_toNat]
    apply sepWP_seq_lscl hcl (mid := lsmpl.base 221)
    wp_steps_sync_pool (lsmpl.base 221)
    simp only [State.setMem_setMem]
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) ?_
    intro hcl_m
    have hfg1 := lscall_blk (callerProg := (blkPC_218).rebase (blkPl_218).base H)
      (finish_grow_24_ne_cells_of_spec hfg) hcl_m
    wp_call hfg1 (s0.sp - 56#64, cap, ptr, new, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64, st)
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    wp_done

/-! ## Representation and Stack-Framing Reductions -/

private theorem do_reserve_7_raw_placed_of_stride [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {addr : BitVec 64} {hookStack : Nat}
    (hs : subroutine_ok P addr
      (withLsCodeLoaded lsmpl (doReserveStrideRawSpecWithStack M A lim hookStack))) :
    subroutine_ok P addr
      (withLsCodeLoaded lsmpl (doReserveRawSpecWithStack M A lim hookStack)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [doReserveRawSpecWithStack,
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpecWithStack,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hlen, hptr, hbound, hfits⟩, hmem⟩
  let xs : DoReserveStrideCall := ⟨x.v, x.cap, x.ptr, x.bs, x.bs.length, x.additional, 1#64, 1#64⟩
  have hrlay : RustLayoutOk (reserveCap x.cap.toNat x.bs.length x.additional) 1 :=
    ⟨⟨by dsimp [reserveCap]; omega, ⟨0, rfl⟩, by omega⟩, by decide⟩
  have hevs : doReserveStrideEvents xs = doReserveEvents x := by
    unfold doReserveStrideEvents doReserveEvents
    simp only [xs, BitVec.toNat_ofNat, Nat.one_mod, reserveCapStride_one, Nat.mul_one]
  have hfits_s : FitsEnv M lim st (DoReserveStrideEnv xs) := by
    rw [fitsEnv_doReserveStride_iff, hevs, ← fitsEnv_doReserve_iff]
    exact hfits
  have hpre' : s0.mem ⊨
      (withLsCodeLoaded lsmpl (doReserveStrideRawSpecWithStack M A lim hookStack)).pre (xs, st) s0 ∗
        R := by
    simp only [doReserveStrideRawSpecWithStack, xs, BitVec.toNat_ofNat, Nat.one_mod,
      reserveCapStride_one, Nat.mul_one, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hlen, hlen, hptr, by decide, hrlay, hfits_s⟩, hmem⟩
  refine hs.mono_outcome (xs, st) R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | hfail)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simpa only [doReserveStrideRawSpecWithStack, doReserveRawSpecWithStack,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpecWithStack, xs,
      hevs, BitVec.toNat_ofNat, Nat.one_mod, reserveCapStride_one, Nat.mul_one, Nat.mod_one,
      and_true] using hq
  · exact Or.inr hfail

private theorem vecU8At_eq (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (if cap = 0#64 then emp
       else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
         memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) := by
  simp only [vecU8At, vecHeader, BitVec.ofNat_eq_ofNat]
  sep_ac_rfl

private theorem do_reserve_vec_placed_of_raw [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {addr : BitVec 64} {hookStack : Nat}
    (hraw : subroutine_ok P addr
      (withLsCodeLoaded lsmpl (doReserveRawSpecWithStack M A lim hookStack))) :
    subroutine_ok P addr
      (withLsCodeLoaded lsmpl (doReserveSpecWithStack M A lim hookStack)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [doReserveSpecWithStack,
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpecWithStack,
    vecU8At_eq, RustCliAllocBudget.repAlloc_live_norm, sepConj_assoc, satisfies_pure_sepConj]
    at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hbound, hfits⟩, ⟨hlen, _hcap63, hptr⟩, hmem⟩
  have hpre' : s0.mem ⊨
      (withLsCodeLoaded lsmpl (doReserveRawSpecWithStack M A lim hookStack)).pre (x, st) s0 ∗
        (((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R) := by
    simp only [doReserveRawSpecWithStack,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpecWithStack,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hx4, hlen, hptr, hbound, hfits⟩, ?_⟩
    have heq :
        (x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
          ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
          ((if x.cap = 0#64 then emp
            else A.live x.ptr x.cap.toNat 1 ∗ (x.ptr ↦ₛ x.bs) ∗
              memRegion (x.ptr + BitVec.ofNat 64 x.bs.length) (x.cap.toNat - x.bs.length)) ∗
            A.pool lim st s0 ∗ stackAt s0.sp (hookStack + 48 + 64) ∗
            ⌜LibsignalCodeLoaded lsmpl s0.mem⌝ ∗ R) =
        (x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
          ((if x.cap = 0#64 then emp
            else A.live x.ptr x.cap.toNat 1 ∗ (x.ptr ↦ₛ x.bs) ∗
              memRegion (x.ptr + BitVec.ofNat 64 x.bs.length) (x.cap.toNat - x.bs.length)) ∗
            A.pool lim st s0 ∗ stackAt s0.sp (hookStack + 48 + 64) ∗
            ⌜LibsignalCodeLoaded lsmpl s0.mem⌝ ∗
            ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R) := by sep_ac_rfl
    simpa only [sepConj_assoc] using heq ▸ hmem
  refine hraw.mono_outcome (x, st) (((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R)
    s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    change reserveCap x.cap.toNat x.bs.length x.additional + 1 ≤ 2 ^ 63 at hbound
    simp only [doReserveRawSpecWithStack, doReserveSpecWithStack,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpecWithStack,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpecWithStack,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.reserveCap,
      vecU8At_eq, RustCliAllocBudget.repAlloc_live_norm] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htrace, hq⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq
    rcases hq with ⟨p', hq⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨hp', hmem_f⟩
    have hlt : reserveCap x.cap.toNat x.bs.length x.additional < 2 ^ 64 := by
      dsimp [reserveCap] at hbound ⊢; omega
    have htoNat : (BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional)).toNat =
        reserveCap x.cap.toNat x.bs.length x.additional := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    have hlen_le : x.bs.length ≤ reserveCap x.cap.toNat x.bs.length x.additional := by
      dsimp [reserveCap]; omega
    have hcap63' : reserveCap x.cap.toNat x.bs.length x.additional < 2 ^ 63 := by omega
    have hcap_ne : BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional) ≠ 0#64 := by
      intro heq
      have := congrArg BitVec.toNat heq
      rw [htoNat] at this
      change reserveCap x.cap.toNat x.bs.length x.additional = 0 at this
      dsimp [reserveCap] at this; omega
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htrace, ?_⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨p', ?_⟩
    simp only [hcap_ne, ite_false, htoNat]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hlen_le, hcap63', hp'⟩, ?_⟩
    simp only [sepConj_assoc] at hmem_f ⊢
    have hpost_eq :
        (x.v ↦₆₄ BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional)) ∗
          ((x.v + 8#64) ↦₆₄ p') ∗
          A.live p' (reserveCap x.cap.toNat x.bs.length x.additional) 1 ∗ (p' ↦ₛ x.bs) ∗
          memRegion (p' + BitVec.ofNat 64 x.bs.length)
            (reserveCap x.cap.toNat x.bs.length x.additional - x.bs.length) ∗
          A.pool lim (M.stepEvents (doReserveEvents x) st) sf ∗
          stackAt s0.sp (hookStack + 48 + 64) ∗
          ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R =
        (x.v ↦₆₄ BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional)) ∗
          ((x.v + 8#64) ↦₆₄ p') ∗
          ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
          A.live p' (reserveCap x.cap.toNat x.bs.length x.additional) 1 ∗ (p' ↦ₛ x.bs) ∗
          memRegion (p' + BitVec.ofNat 64 x.bs.length)
            (reserveCap x.cap.toNat x.bs.length x.additional - x.bs.length) ∗
          A.pool lim (M.stepEvents (doReserveEvents x) st) sf ∗
          stackAt s0.sp (hookStack + 48 + 64) ∗ R := by sep_ac_rfl
    exact hpost_eq ▸ hmem_f
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

private theorem stackAt_doReserve_eq_32_gen (sp : BitVec 64) {hookStack : Nat}
    (hhook : (hookStack + 48) + 64 ≤ 2 ^ 64) :
    stackAt sp ((hookStack + 48) + 64) =
      stackAt sp ((hookStack + 32) + 64) ∗
        memRegion (sp - BitVec.ofNat 64 ((hookStack + 48) + 64)) 16 := by
  have hsplit := ProofLib.stackAt_split_bottom sp ((hookStack + 32) + 64) 16
    (by omega : ((hookStack + 32) + 64) + 16 ≤ 2 ^ 64)
  rw [sepConj_comm]
  simpa only [show ((hookStack + 32) + 64) + 16 = (hookStack + 48) + 64 by omega] using hsplit

private theorem do_reserve_raw1_placed_of_raw32 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {addr : BitVec 64} {hookStack : Nat}
    (hhook : (hookStack + 48) + 64 ≤ 2 ^ 64)
    (h32 : subroutine_ok P addr
      (withLsCodeLoaded lsmpl (doReserve1Raw32SpecWithStack M A lim hookStack))) :
    subroutine_ok P addr
      (withLsCodeLoaded lsmpl (doReserve1RawSpecWithStack M A lim hookStack)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [doReserve1RawSpecWithStack, stackAt_doReserve_eq_32_gen _ hhook, sepConj_assoc]
    at hpre
  let btm := memRegion (s0.sp - BitVec.ofNat 64 ((hookStack + 48) + 64)) 16
  have hpre' : s0.mem ⊨
      (withLsCodeLoaded lsmpl (doReserve1Raw32SpecWithStack M A lim hookStack)).pre (x, st) s0 ∗
        (btm ∗ R) := by
    simp only [doReserve1Raw32SpecWithStack, btm, sepConj_assoc]
    have heq :
        ∀ (Q1 Q2 Q3 Q4 Q5 Q6 : SepProp),
          Q1 ∗ Q2 ∗ Q3 ∗ Q4 ∗ Q5 ∗ Q6 ∗ btm ∗ ⌜LibsignalCodeLoaded lsmpl s0.mem⌝ ∗ R =
            Q1 ∗ Q2 ∗ Q3 ∗ Q4 ∗ Q5 ∗ Q6 ∗ ⌜LibsignalCodeLoaded lsmpl s0.mem⌝ ∗ btm ∗ R := by
      intro _ _ _ _ _ _; sep_ac_rfl
    simpa only [sepConj_assoc] using (heq _ _ _ _ _ _) ▸ hpre
  refine h32.mono_outcome (x, st) (btm ∗ R) s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simpa only [doReserve1Raw32SpecWithStack, doReserve1RawSpecWithStack,
      stackAt_doReserve_eq_32_gen _ hhook, btm, sepConj_assoc] using hq
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

private theorem do_reserve_raw_placed_of_raw1 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {addr : BitVec 64} {hookStack : Nat}
    (h1 : subroutine_ok P addr
      (withLsCodeLoaded lsmpl (doReserve1RawSpecWithStack M A lim hookStack))) :
    subroutine_ok P addr
      (withLsCodeLoaded lsmpl (doReserveRawSpecWithStack M A lim hookStack)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [doReserveRawSpecWithStack,
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpecWithStack,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, _, _, hlen, hptr, hbound, hfits⟩, hmem⟩
  have hpre' : s0.mem ⊨
      (withLsCodeLoaded lsmpl (doReserve1RawSpecWithStack M A lim hookStack)).pre (x, st) s0 ∗
        R := by
    simp only [doReserve1RawSpecWithStack, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hlen, hptr, hbound, hfits⟩, hmem⟩
  exact h1.mono_outcome (x, st) R s0 hpc hrun hpre' hsp fun _ hout => hout

/-! ## `HookSat` Corollaries -/

theorem do_reserve_7_stride_raw_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_320).rebase (blkPl_320).base H) (blkPl_320).base
      (withLsCodeLoaded lsmpl (doReserveStrideRawSpec M A lim)) :=
  do_reserve_7_stride_raw_placed_ok_of_fg (hookStack := allocHookStack) (by decide) h_panic
    (finish_grow_8_placed_ok hshim halloc hrealloc)

theorem do_reserve_7_stride_raw_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_320).rebase (blkPl_320).base H) (blkPl_320).base
      (withLsCodeLoaded lsmpl (doReserveStrideRawSpecX M A lim)) :=
  do_reserve_7_stride_raw_placed_ok_of_fg (hookStack := extHookStack) (by decide) h_panic
    (finish_grow_8_placed_ok_x hshim halloc hrealloc)

theorem do_reserve_7_raw_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_320).rebase (blkPl_320).base H) (blkPl_320).base
      (withLsCodeLoaded lsmpl (doReserveRawSpec M A lim)) :=
  do_reserve_7_raw_placed_of_stride
    (do_reserve_7_stride_raw_placed_ok h_panic hshim halloc hrealloc)

theorem do_reserve_7_raw_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_320).rebase (blkPl_320).base H) (blkPl_320).base
      (withLsCodeLoaded lsmpl (doReserveRawSpecX M A lim)) :=
  do_reserve_7_raw_placed_of_stride (hookStack := extHookStack)
    (do_reserve_7_stride_raw_placed_ok_x h_panic hshim halloc hrealloc)

theorem do_reserve_7_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_320).rebase (blkPl_320).base H) (blkPl_320).base
      (withLsCodeLoaded lsmpl (doReserveSpec M A lim)) :=
  do_reserve_vec_placed_of_raw (do_reserve_7_raw_placed_ok h_panic hshim halloc hrealloc)

theorem do_reserve_7_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_320).rebase (blkPl_320).base H) (blkPl_320).base
      (withLsCodeLoaded lsmpl (doReserveSpecX M A lim)) :=
  do_reserve_vec_placed_of_raw (hookStack := extHookStack)
    (do_reserve_7_raw_placed_ok_x h_panic hshim halloc hrealloc)

theorem do_reserve_2_raw32_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_157).rebase (blkPl_157).base H) (blkPl_157).base
      (withLsCodeLoaded lsmpl (doReserve1Raw32Spec M A lim)) :=
  do_reserve_2_raw32_placed_ok_of_fg (hookStack := allocHookStack) (by decide) h_panic
    (finish_grow_2_placed_ok hshim halloc hrealloc)

theorem do_reserve_2_raw32_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_157).rebase (blkPl_157).base H) (blkPl_157).base
      (withLsCodeLoaded lsmpl (doReserve1Raw32SpecX M A lim)) :=
  do_reserve_2_raw32_placed_ok_of_fg (hookStack := extHookStack) (by decide) h_panic
    (finish_grow_2_placed_ok_x hshim halloc hrealloc)

theorem do_reserve_4_raw32_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_218).rebase (blkPl_218).base H) (blkPl_218).base
      (withLsCodeLoaded lsmpl (doReserve1Raw32Spec M A lim)) :=
  do_reserve_4_raw32_placed_ok_of_fg (hookStack := allocHookStack) (by decide) h_panic
    (finish_grow_4_placed_ok hshim halloc hrealloc)

theorem do_reserve_4_raw32_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_218).rebase (blkPl_218).base H) (blkPl_218).base
      (withLsCodeLoaded lsmpl (doReserve1Raw32SpecX M A lim)) :=
  do_reserve_4_raw32_placed_ok_of_fg (hookStack := extHookStack) (by decide) h_panic
    (finish_grow_4_placed_ok_x hshim halloc hrealloc)

theorem do_reserve_2_raw1_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_157).rebase (blkPl_157).base H) (blkPl_157).base
      (withLsCodeLoaded lsmpl (doReserve1RawSpec M A lim)) :=
  do_reserve_raw1_placed_of_raw32 (hookStack := allocHookStack) (by decide)
    (do_reserve_2_raw32_placed_ok h_panic hshim halloc hrealloc)

theorem do_reserve_2_raw1_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_157).rebase (blkPl_157).base H) (blkPl_157).base
      (withLsCodeLoaded lsmpl (doReserve1RawSpecX M A lim)) :=
  do_reserve_raw1_placed_of_raw32 (hookStack := extHookStack) (by decide)
    (do_reserve_2_raw32_placed_ok_x h_panic hshim halloc hrealloc)

theorem do_reserve_2_raw_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_157).rebase (blkPl_157).base H) (blkPl_157).base
      (withLsCodeLoaded lsmpl (doReserveRawSpec M A lim)) :=
  do_reserve_raw_placed_of_raw1 (do_reserve_2_raw1_placed_ok h_panic hshim halloc hrealloc)

theorem do_reserve_2_raw_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_157).rebase (blkPl_157).base H) (blkPl_157).base
      (withLsCodeLoaded lsmpl (doReserveRawSpecX M A lim)) :=
  do_reserve_raw_placed_of_raw1 (hookStack := extHookStack)
    (do_reserve_2_raw1_placed_ok_x h_panic hshim halloc hrealloc)

theorem do_reserve_2_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_157).rebase (blkPl_157).base H) (blkPl_157).base
      (withLsCodeLoaded lsmpl (doReserveSpec M A lim)) :=
  do_reserve_vec_placed_of_raw (do_reserve_2_raw_placed_ok h_panic hshim halloc hrealloc)

theorem do_reserve_2_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_157).rebase (blkPl_157).base H) (blkPl_157).base
      (withLsCodeLoaded lsmpl (doReserveSpecX M A lim)) :=
  do_reserve_vec_placed_of_raw (hookStack := extHookStack)
    (do_reserve_2_raw_placed_ok_x h_panic hshim halloc hrealloc)

theorem do_reserve_4_raw1_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_218).rebase (blkPl_218).base H) (blkPl_218).base
      (withLsCodeLoaded lsmpl (doReserve1RawSpec M A lim)) :=
  do_reserve_raw1_placed_of_raw32 (hookStack := allocHookStack) (by decide)
    (do_reserve_4_raw32_placed_ok h_panic hshim halloc hrealloc)

theorem do_reserve_4_raw1_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_218).rebase (blkPl_218).base H) (blkPl_218).base
      (withLsCodeLoaded lsmpl (doReserve1RawSpecX M A lim)) :=
  do_reserve_raw1_placed_of_raw32 (hookStack := extHookStack) (by decide)
    (do_reserve_4_raw32_placed_ok_x h_panic hshim halloc hrealloc)

theorem do_reserve_4_raw_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_218).rebase (blkPl_218).base H) (blkPl_218).base
      (withLsCodeLoaded lsmpl (doReserveRawSpec M A lim)) :=
  do_reserve_raw_placed_of_raw1 (do_reserve_4_raw1_placed_ok h_panic hshim halloc hrealloc)

theorem do_reserve_4_raw_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_218).rebase (blkPl_218).base H) (blkPl_218).base
      (withLsCodeLoaded lsmpl (doReserveRawSpecX M A lim)) :=
  do_reserve_raw_placed_of_raw1 (hookStack := extHookStack)
    (do_reserve_4_raw1_placed_ok_x h_panic hshim halloc hrealloc)

theorem do_reserve_4_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_218).rebase (blkPl_218).base H) (blkPl_218).base
      (withLsCodeLoaded lsmpl (doReserveSpec M A lim)) :=
  do_reserve_vec_placed_of_raw (do_reserve_4_raw_placed_ok h_panic hshim halloc hrealloc)

theorem do_reserve_4_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_218).rebase (blkPl_218).base H) (blkPl_218).base
      (withLsCodeLoaded lsmpl (doReserveSpecX M A lim)) :=
  do_reserve_vec_placed_of_raw (hookStack := extHookStack)
    (do_reserve_4_raw_placed_ok_x h_panic hshim halloc hrealloc)

end LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Alloc.FinishGrowBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DoReserve
public import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.GrowOneCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym
public meta import LibsignalBinary.Proofs.TripleRatchet.Alloc.FinishGrowBudget -- shake: keep
public meta import LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContractsBudget -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry -- shake: keep
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Placed.GenLsBlock
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `RawVecInner::reserve::do_reserve_and_handle` (`0x4cac`, Block `13`)

Verifies `<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]`
(`0x4cac`, Block `13`, calling Block `45`) against `doReserveRawSpecWithStack M A lim fgStack`
(16-byte `RawVecInner`) and `doReserveSpecWithStack M A lim fgStack` (24-byte `Vec<u8>`), with
`onPanic = ⌜False⌝` and `onOom = ⌜False⌝` under `FitsEnv M lim st (DoReserveEnv x)`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Alloc.DoReserveBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement blkPC_13 blkPC_45 blkPl_13 blkPl_45
  extract_withLsCodeLoaded libsignalSessionCode ls_subroutine_ok_of_block lsmpl
  lsRustAllocSym lsRustNoAllocShimSym lsRustReallocSym
  sepWP_seq_lscl subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded
)
open CryptoVerification.RustHeap (
  LayoutOk allocHookStack vecU8At
)
open CryptoVerification.InImageLift (OptCallInv)
open CryptoVerification.LibsignalTripleRatchet (
  DoReserveCall FinishGrowCall
  doReserveName extHookStack finishGrowName specWithOptInv
  subroutine_ok_kit_of_trTrap subroutine_ok_of_optNone subroutine_ok_to_optNone
  trTrapProgAt trTrapProgAt_fnAddr_eq tripleRatchetProgAt tripleRatchetProgAtExt
  vecU8At_eq_shared_lb
)
open CryptoVerification.LibsignalTripleRatchet.DoReserveFacts (
  doReserve_fnOff finishGrow_fnOff
)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits FitsEvents RustCliAllocBudget RustLayoutOk
  rustAllocEvents rustCliAllocBudgetSpec rustCliAllocNoOomSpec
  rustCliReallocBudgetSpec rustCliReallocNoOomSpec rustReallocEvents
)
open LibsignalBinary.Heap.SpecBudget (AllocHooksBudgetBase)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (trapHooks)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  AllocContractsBudget AllocContractsXBudget
  DoReserveEnv FinishGrowEnv doReserveEvents doReserveRawSpec doReserveRawSpecX
  doReserveSpec doReserveSpecX finishGrowEvents fitsEnv_doReserve_iff fitsEnv_finishGrow_iff
  noAllocShimBudgetSpec reserveCap
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContractsBudget (
  doReserveRawSpecWithStack doReserveSpecWithStack finishGrowSpecWithStack
  rebase_trapHooks_fnAddr
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.FinishGrowBudget (
  finish_grow_ok_ext finish_grow_ok_ext_x
  finish_grow_placed_ok finish_grow_placed_ok_noOom
  finish_grow_placed_ok_x finish_grow_placed_ok_x_noOom
)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Local State-Normalization & Separation-Logic Repack Helpers -/

@[local arm64_norm ↓, local wp_norm ↓]
private theorem doReserve_sp_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem doReserve_sp_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem doReserve_readReg64_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
private theorem doReserve_readReg64_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory)
    (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem doReserve_readReg32_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem doReserve_readReg32_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory)
    (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem doReserve_readReg_setPC_pre (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem doReserve_readReg_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory)
    (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

private theorem fg0_post_repack (C0 C1 C2 L1 L2 P S R : SepProp) :
    (C0 ∗ C1 ∗ C2 ∗ L1 ∗ L2 ∗ P ∗ S) ∗ R =
      (L1 ∗ L2 ∗ P ∗ S ∗ C0 ∗ C1 ∗ C2) ∗ R := by
  sep_ac_rfl

private theorem fg1_post_repack (C0 C1 C2 L1 L2 L3 P S R : SepProp) :
    (C0 ∗ C1 ∗ C2 ∗ L1 ∗ L2 ∗ L3 ∗ P ∗ S) ∗ R =
      (L1 ∗ L2 ∗ L3 ∗ P ∗ S ∗ C0 ∗ C1 ∗ C2) ∗ R := by
  sep_ac_rfl

private theorem doReserve_pre_repack (P1 P2 P3 P4 P5 P6 R : SepProp) :
    P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ (P6 ∗ R) =
      P1 ∗ P2 ∗ P6 ∗ P3 ∗ P4 ∗ P5 ∗ R := by
  sep_ac_rfl

private theorem doReserve_post_repack (P1 P2 P6 P3 P4 P5 P7 R : SepProp) :
    (P1 ∗ P2 ∗ P6 ∗ P3 ∗ P4 ∗ P5) ∗ P7 ∗ R =
      (P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5) ∗ P7 ∗ (P6 ∗ R) := by
  sep_ac_rfl

private abbrev vecU8At_eq := @vecU8At_eq_shared_lb

private theorem optCallInv_none (s : State) : OptCallInv none s := trivial

/-! ## Arithmetic & Stack Helpers for `do_reserve_and_handle` -/

private theorem adds_cs_eq_false {x2 x1 : BitVec 64}
    (h : x2.toNat + x1.toNat < 2 ^ 64) :
    (x2 + x1).ult x2 = false := by
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, BitVec.toNat_add, Nat.mod_eq_of_lt h]
  omega

private theorem reserve_new_cap_eq {cap x1 x2 : BitVec 64} {len additional : Nat}
    (hx1 : x1.toNat = len) (hx2 : x2.toNat = additional)
    (h : reserveCap cap.toNat len additional + 1 ≤ 2 ^ 63) :
    (if (8#64).ult (if (cap <<< 1).ult (x2 + x1) = true then x2 + x1 else cap <<< 1) = true then
      if (cap <<< 1).ult (x2 + x1) = true then x2 + x1 else cap <<< 1
     else 8#64) =
      BitVec.ofNat 64 (reserveCap cap.toNat len additional) := by
  have hmax : max (max (len + additional) (2 * cap.toNat)) 8 + 1 ≤ 2 ^ 63 := h
  have hadd : (x2 + x1).toNat = len + additional := by
    rw [BitVec.toNat_add, hx2, hx1, Nat.mod_eq_of_lt (by omega)]
    omega
  have hsh : (cap <<< 1).toNat = 2 * cap.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    change (cap.toNat * 2) % 2 ^ 64 = 2 * cap.toNat
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hm1 : (if (cap <<< 1).ult (x2 + x1) = true then x2 + x1 else cap <<< 1).toNat =
      max (len + additional) (2 * cap.toNat) := by
    by_cases hc : (cap <<< 1).ult (x2 + x1) = true
    · simp only [hc, ite_true, hadd]
      rw [BitVec.ult_eq_decide, decide_eq_true_eq, hsh, hadd] at hc
      omega
    · simp only [hc, Bool.false_eq_true, ite_false, hsh]
      rw [BitVec.ult_eq_decide, decide_eq_true_eq, hsh, hadd] at hc
      omega
  apply BitVec.eq_of_toNat_eq
  dsimp [reserveCap, CryptoVerification.LibsignalTripleRatchet.reserveCap]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  generalize (if (cap <<< 1).ult (x2 + x1) = true then x2 + x1 else cap <<< 1) = m1 at hm1 ⊢
  by_cases hc2 : (8#64).ult m1 = true
  · simp only [hc2, ite_true, hm1]
    rw [BitVec.ult_eq_decide, decide_eq_true_eq, hm1] at hc2
    change 8 < max (len + additional) (2 * cap.toNat) at hc2
    omega
  · simp only [hc2, Bool.false_eq_true, ite_false]
    rw [BitVec.ult_eq_decide, decide_eq_true_eq, hm1] at hc2
    change ¬ 8 < max (len + additional) (2 * cap.toNat) at hc2
    change 8 = max (max (len + additional) (2 * cap.toNat)) 8
    omega

private theorem memRegion_24_cells (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v2) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v0)) := by
  rw [show (24 : Nat) = 8 + (8 + 8) by rfl, memRegion_split a 8 (8 + 8) (by decide),
    memRegion_split (a + 8#64) 8 8 (by decide), memRegion_eight, memRegion_eight, memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem stackAt_doReserve_opt {fgStack : Nat}
    (hstack : fgStack + 64 ≤ 2 ^ 64) (sp : BitVec 64) :
    stackAt sp (fgStack + 64) =
      stackAt (sp - 64#64) fgStack ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
         ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
          ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
          ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
          ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
  have h1 := stackAt_split_cells sp fgStack 8 hstack
  have hc8 : cells (sp - 64#64) 8 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
        ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
        ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
    cells_unfold
  rw [h1, hc8]

/-! ## Cell-Unfolded `finish_grow` Budget Specs for `stride = 1, align = 1` -/

private abbrev FG1BudgetGhost (M : AllocCostModel) :=
  BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) ×
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × M.σ

private def finishGrow1ZeroSpecWithStack (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (fgStack : Nat) : Spec (FG1BudgetGhost M) where
  pre := fun (out, cap, ptr, new, bs, o0, o1, o2, fsp, st) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.readReg64 .x4 = 1#64 ∧ s.readReg64 .x5 = 1#64 ∧
      s.sp = fsp ∧ cap = 0#64 ∧ bs = [] ∧ cap.toNat ≤ new.toNat ∧
      0 < new.toNat ∧ new.toNat + 1 ≤ 2 ^ 63 ∧
      FitsEvents M lim st (rustAllocEvents new.toNat 1)⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.pool lim st s ∗ stackAt fsp fgStack
  post := fun (out, _cap, _ptr, new, _bs, _o0, _o1, _o2, fsp, st) s0 sf =>
    ∃∗ p' : BitVec 64, ∃∗ o2' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
      A.live p' new.toNat 1 ∗ memRegion p' new.toNat ∗
      A.pool lim (M.stepEvents (rustAllocEvents new.toNat 1) st) sf ∗
      stackAt fsp fgStack ∗
      (out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')

private theorem finish_grow_1_zero_ok_of_fg_opt {oimg : Option Obj.Image} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)} {hookStack : Nat}
    (hfg : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowName)
      (specWithOptInv oimg (finishGrowSpecWithStack M A lim hookStack))) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowName)
      (specWithOptInv oimg (finishGrow1ZeroSpecWithStack M A lim (hookStack + 48))) := by
  refine subroutine_ok_outcome_intro ?_
  intro ⟨out, cap, ptr, new, bs, o0, o1, o2, fsp, st⟩ R s0 hpc hrun hpre hsp
  dsimp only [specWithOptInv] at hpre
  simp only [finishGrow1ZeroSpecWithStack, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap0, hbs, hle, hpos, hbound, hfit⟩, hmem⟩
  subst hfsp; subst hcap0; subst hbs
  let hcall : FinishGrowCall := ⟨out, 0#64, ptr, new, 1#64, 1#64, []⟩
  have hrlay : RustLayoutOk (new.toNat * (1#64 : BitVec 64).toNat) (1#64 : BitVec 64).toNat := by
    refine ⟨⟨by change 0 < new.toNat * 1; omega, ⟨0, rfl⟩, ?_⟩, by decide⟩
    change new.toNat * 1 + 1 ≤ 2 ^ 63; omega
  have hfit_env : LibsignalBinary.Heap.FitsEnv M lim st (FinishGrowEnv hcall) := by
    rw [fitsEnv_finishGrow_iff]
    have ha1 : (1#64 : BitVec 64).toNat = 1 := rfl
    simpa only [finishGrowEvents, hcall, BitVec.toNat_zero, ↓reduceIte, ha1, Nat.mul_one] using hfit
  have hpre' : s0.mem ⊨
      (specWithOptInv oimg (finishGrowSpecWithStack M A lim hookStack)).pre (hcall, st) s0 ∗ R := by
    dsimp only [specWithOptInv]
    simp only [finishGrowSpecWithStack,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowSpecWithStack,
      hcall, FinishGrowCall.oldBuf, ite_true, memRegion_24_cells, emp_sepConj,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, fun _ => trivial, Nat.zero_le _, hle, hpos,
      by decide, hrlay, hfit_env⟩, by simpa only [sepConj_assoc] using hmem⟩
  refine hfg.mono_outcome (hcall, st) R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [specWithOptInv] at hq ⊢
    simp only [finishGrowSpecWithStack,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowSpecWithStack,
      finishGrow1ZeroSpecWithStack, hcall, finishGrowEvents, BitVec.toNat_zero, ↓reduceIte,
      pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj,
      sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨p', hq⟩
    have hm1 : new.toNat * (1#64 : BitVec 64).toNat = new.toNat := Nat.mul_one _
    have ha1 : (1#64 : BitVec 64).toNat = 1 := rfl
    rw [hm1] at hq
    rw [ha1] at hq
    refine ⟨p', BitVec.ofNat 64 new.toNat, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨⟨hp', _, htrace⟩, hrest⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hp', htrace⟩, ?_⟩
    have hrest' : sf.mem ⊨
        ((out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ BitVec.ofNat 64 new.toNat) ∗
          A.live p' new.toNat 1 ∗ memRegion p' new.toNat ∗
          A.pool lim (M.stepEvents (rustAllocEvents new.toNat 1) st) sf ∗
          stackAt s0.sp (hookStack + 48)) ∗ R := by
      simpa only [sepConj_assoc] using hrest
    rw [fg0_post_repack] at hrest'
    simpa only [sepConj_assoc] using hrest'
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hq⟩))

private def finishGrow1NeSpecWithStack (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (fgStack : Nat) : Spec (FG1BudgetGhost M) where
  pre := fun (out, cap, ptr, new, bs, o0, o1, o2, fsp, st) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.readReg64 .x4 = 1#64 ∧ s.readReg64 .x5 = 1#64 ∧
      s.sp = fsp ∧ cap ≠ 0#64 ∧ bs.length ≤ cap.toNat ∧ cap.toNat ≤ new.toNat ∧
      0 < new.toNat ∧ new.toNat + 1 ≤ 2 ^ 63 ∧
      FitsEvents M lim st (rustReallocEvents cap.toNat new.toNat 1)⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
    memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
    A.pool lim st s ∗ stackAt fsp fgStack
  post := fun (out, cap, _ptr, new, bs, _o0, _o1, _o2, fsp, st) s0 sf =>
    ∃∗ p' : BitVec 64, ∃∗ o2' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
      A.live p' new.toNat 1 ∗ (p' ↦ₛ bs) ∗
      memRegion (p' + BitVec.ofNat 64 bs.length) (new.toNat - bs.length) ∗
      A.pool lim (M.stepEvents (rustReallocEvents cap.toNat new.toNat 1) st) sf ∗
      stackAt fsp fgStack ∗
      (out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')

private theorem finish_grow_1_ne_ok_of_fg_opt {oimg : Option Obj.Image} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)} {hookStack : Nat}
    (hfg : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowName)
      (specWithOptInv oimg (finishGrowSpecWithStack M A lim hookStack))) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowName)
      (specWithOptInv oimg (finishGrow1NeSpecWithStack M A lim (hookStack + 48))) := by
  refine subroutine_ok_outcome_intro ?_
  intro ⟨out, cap, ptr, new, bs, o0, o1, o2, fsp, st⟩ R s0 hpc hrun hpre hsp
  dsimp only [specWithOptInv] at hpre
  simp only [finishGrow1NeSpecWithStack, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap, hbs, hle, hpos, hbound, hfit⟩, hmem⟩
  subst hfsp
  let hcall : FinishGrowCall := ⟨out, cap, ptr, new, 1#64, 1#64, bs⟩
  have hcap_nat_ne : cap.toNat ≠ 0 := fun hc => hcap (BitVec.eq_of_toNat_eq hc)
  have hrlay : RustLayoutOk (new.toNat * (1#64 : BitVec 64).toNat) (1#64 : BitVec 64).toNat := by
    refine ⟨⟨by change 0 < new.toNat * 1; omega, ⟨0, rfl⟩, ?_⟩, by decide⟩
    change new.toNat * 1 + 1 ≤ 2 ^ 63; omega
  have hfit_env : LibsignalBinary.Heap.FitsEnv M lim st (FinishGrowEnv hcall) := by
    rw [fitsEnv_finishGrow_iff]
    have ha1 : (1#64 : BitVec 64).toNat = 1 := rfl
    simpa only [finishGrowEvents, hcall, hcap_nat_ne, ↓reduceIte, ha1, Nat.mul_one] using hfit
  have hpre' : s0.mem ⊨
      (specWithOptInv oimg (finishGrowSpecWithStack M A lim hookStack)).pre (hcall, st) s0 ∗ R := by
    dsimp only [specWithOptInv]
    simp only [finishGrowSpecWithStack,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowSpecWithStack,
      hcall, FinishGrowCall.oldBuf, RustCliAllocBudget.repAlloc_live, hcap, ite_false,
      memRegion_24_cells, sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    have hm_cap : cap.toNat * (1#64 : BitVec 64).toNat = cap.toNat := Nat.mul_one _
    have ha1 : (1#64 : BitVec 64).toNat = 1 := rfl
    rw [hm_cap, ha1]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, False.elim, hbs, hle, hpos,
      by decide, hrlay, hfit_env⟩, by simpa only [sepConj_assoc] using hmem⟩
  refine hfg.mono_outcome (hcall, st) R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [specWithOptInv] at hq ⊢
    simp only [finishGrowSpecWithStack,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowSpecWithStack,
      finishGrow1NeSpecWithStack, hcall, finishGrowEvents, hcap_nat_ne, ↓reduceIte,
      sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨p', hq⟩
    have hm_new : new.toNat * (1#64 : BitVec 64).toNat = new.toNat := Nat.mul_one _
    have hm_cap : cap.toNat * (1#64 : BitVec 64).toNat = cap.toNat := Nat.mul_one _
    have ha1 : (1#64 : BitVec 64).toNat = 1 := rfl
    rw [hm_new, hm_cap, ha1] at hq
    refine ⟨p', BitVec.ofNat 64 new.toNat, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨⟨hp', _, htrace⟩, hrest⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hp', htrace⟩, ?_⟩
    have hrest' : sf.mem ⊨
        ((out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ BitVec.ofNat 64 new.toNat) ∗
          A.live p' new.toNat 1 ∗ (p' ↦ₛ bs) ∗
          memRegion (p' + BitVec.ofNat 64 bs.length) (new.toNat - bs.length) ∗
          A.pool lim (M.stepEvents (rustReallocEvents cap.toNat new.toNat 1) st) sf ∗
          stackAt s0.sp (hookStack + 48)) ∗ R := by
      simpa only [sepConj_assoc] using hrest
    rw [fg1_post_repack] at hrest'
    simpa only [sepConj_assoc] using hrest'
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hq⟩))

/-! ## Fixed-Base Verification of `do_reserve_and_handle` (`doReserveRawSpec` and `doReserveSpec`) -/

section FixedBaseSteps

attribute [local irreducible] Program.fnOff

theorem do_reserve_raw_ok_of_fg_opt {oimg : Option Obj.Image} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)} {hookStack : Nat}
    (hstack : (hookStack + 48) + 64 ≤ 2 ^ 64 := by decide)
    (hfg : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowName)
      (specWithOptInv oimg (finishGrowSpecWithStack M A lim hookStack))) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr doReserveName)
      (specWithOptInv oimg (doReserveRawSpecWithStack M A lim (hookStack + 48))) := by
  have hfn : libsignalSessionCode.fnOff doReserveName =
      num% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]") :=
    doReserve_fnOff
  have hfg0 := finish_grow_1_zero_ok_of_fg_opt hfg
  have hfg1 := finish_grow_1_ne_ok_of_fg_opt hfg
  rw [Program.fnAddr_rel (name := doReserveName)
    hfn finishGrow_fnOff
    (k := num% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]" -
      ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]"))
    (by decide)] at hfg0 hfg1
  clear hfg
  unfold specWithOptInv tripleRatchetProgAtExt at hfg0 hfg1 ⊢
  unfold doReserveRawSpecWithStack
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpecWithStack
  simp only [stackAt_doReserve_opt hstack, sepExists_sepConj_right]
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin b
    trapHooks hfn
    (num% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]")) 140
  rw [← rebase_trapHooks_fnAddr libsignalSessionCode b (Rust.withPanics ext) doReserveName]
    at hfg0 hfg1 ⊢
  generalize_entry (libsignalSessionCode.rebase b trapHooks).fnAddr doReserveName = entry
  examples_hide_fetches
  wp_init x s0
  obtain ⟨⟨v, cap, ptr, bs, additional⟩, st⟩ := x
  dsimp only at *
  have hinv0 : OptCallInv oimg s0 := by assumption
  have hx1_eq : (s0.readReg64 .x1).toNat = bs.length := by assumption
  have hx2_eq : (s0.readReg64 .x2).toNat = additional := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat := by assumption
  have hfit0 : LibsignalBinary.Heap.FitsEnv M lim st
      (DoReserveEnv ⟨v, cap, ptr, bs, additional⟩) := by assumption
  have hbound : reserveCap cap.toNat bs.length additional + 1 ≤ 2 ^ 63 := by
    dsimp [reserveCap, CryptoVerification.LibsignalTripleRatchet.reserveCap] at *; omega
  have hmax : max (max (bs.length + additional) (2 * cap.toNat)) 8 + 1 ≤ 2 ^ 63 := hbound
  have hcs := adds_cs_eq_false (x2 := s0.readReg64 .x2) (x1 := s0.readReg64 .x1) (by
    rw [hx2_eq, hx1_eq]; omega)
  have hnew_eq := reserve_new_cap_eq (cap := cap) hx1_eq hx2_eq hbound
  let new := BitVec.ofNat 64 (reserveCap cap.toNat bs.length additional)
  have hnew_toNat : new.toNat = reserveCap cap.toNat bs.length additional := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by
    rw [hnew_toNat]; dsimp [reserveCap, CryptoVerification.LibsignalTripleRatchet.reserveCap]; omega
  have hnew_pos : 0 < new.toNat := by
    rw [hnew_toNat]; dsimp [reserveCap, CryptoVerification.LibsignalTripleRatchet.reserveCap]; omega
  have hnew_bound : new.toNat + 1 ≤ 2 ^ 63 := by omega
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hbs_le_cap)
    subst hbs
    have hfit_ev : FitsEvents M lim st (rustAllocEvents new.toNat 1) := by
      simpa only [fitsEnv_doReserve_iff, doReserveEvents, ↓reduceIte, ← hnew_toNat] using hfit0
    have hnew_eq0 :
        (if (8#64).ult
              (if (0#64).ult (s0.readReg64 .x2 + s0.readReg64 .x1) = true then
                s0.readReg64 .x2 + s0.readReg64 .x1
               else 0#64) = true then
          if (0#64).ult (s0.readReg64 .x2 + s0.readReg64 .x1) = true then
            s0.readReg64 .x2 + s0.readReg64 .x1
          else 0#64
         else 8#64) = new := hnew_eq
    simp only [ite_true, emp_sepConj, pointsToBytes_nil,
      List.length_nil, BitVec.add_zero, Nat.sub_zero]
    wp_steps_opt_vm
      (entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]" -
        ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]"))
      hinv0 =>
      wp_call hfg0 (s0.sp - 56#64, 0#64, ptr, new, [], v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64, st)
      wp_steps_opt_vm (s0.readReg64 .lr) (optCallInv_none _) =>
        simp only [doReserveEvents, ↓reduceIte, ← hnew_toNat]
        wp_done
  · have hcap0' : cap ≠ 0 := hcap0
    have hfit_ev : FitsEvents M lim st (rustReallocEvents cap.toNat new.toNat 1) := by
      simpa only [fitsEnv_doReserve_iff, doReserveEvents, hcap0, ↓reduceIte, ← hnew_toNat] using hfit0
    simp only [hcap0, ite_false, sepConj_assoc]
    have hsub_eq : reserveCap cap.toNat bs.length additional - bs.length = new.toNat - bs.length := by
      rw [hnew_toNat]
    rw [hsub_eq]
    wp_steps_opt_vm
      (entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]" -
        ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]"))
      hinv0 =>
      wp_call hfg1 (s0.sp - 56#64, cap, ptr, new, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64, st)
      wp_steps_opt_vm (s0.readReg64 .lr) (optCallInv_none _) =>
        simp only [doReserveEvents, hcap0, ↓reduceIte, ← hnew_toNat]
        wp_done

end FixedBaseSteps

theorem do_reserve_raw_ok_ext {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContractsBudget b M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr doReserveName)
      (doReserveRawSpec M A lim) :=
  subroutine_ok_of_optNone <|
    do_reserve_raw_ok_of_fg_opt (by decide)
      (subroutine_ok_to_optNone (finish_grow_ok_ext hA))

theorem do_reserve_raw_ok_trap {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {C : Crypto} {abs : String → Option (State → State)}
    (hA : AllocHooksBudgetBase M A lim abs) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr doReserveName)
      (doReserveRawSpec M A lim) :=
  do_reserve_raw_ok_ext (AllocContractsBudget.of_tripleRatchetProgAt_trap b C M A lim abs hA)

/-- `<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]`
(`0x4cac`) meets `doReserveRawSpec M A lim` on `tripleRatchetProgAt`. -/
theorem do_reserve_raw_ok {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {C : Crypto} {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hA : AllocHooksBudgetBase M A lim abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr doReserveName)
      (doReserveRawSpec M A lim) :=
  (trTrapProgAt_fnAddr_eq b C ctl abs doReserveName).rec
    (motive := fun addr _ =>
      subroutine_ok (tripleRatchetProgAt b C ctl abs) addr (doReserveRawSpec M A lim))
    (subroutine_ok_kit_of_trTrap (do_reserve_raw_ok_trap hA))

theorem do_reserve_ok_of_raw_opt {oimg : Option Obj.Image} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)} {fgStack : Nat}
    (hraw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr doReserveName)
      (specWithOptInv oimg (doReserveRawSpecWithStack M A lim fgStack))) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr doReserveName)
      (specWithOptInv oimg (doReserveSpecWithStack M A lim fgStack)) := by
  refine subroutine_ok_outcome_intro ?_
  intro ⟨x, st⟩ R s0 hpc hrun hpre hsp
  dsimp only [specWithOptInv] at hpre
  simp only [doReserveSpecWithStack,
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpecWithStack,
    vecU8At_eq, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hbound, hfit⟩, ⟨hlen, hcap63, hptr⟩, hmem⟩
  have hpre' : s0.mem ⊨
      (specWithOptInv oimg (doReserveRawSpecWithStack M A lim fgStack)).pre (x, st) s0 ∗
      (((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R) := by
    dsimp only [specWithOptInv]
    simp only [doReserveRawSpecWithStack,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpecWithStack,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hlen, hptr, hbound, hfit⟩, ?_⟩
    rwa [doReserve_pre_repack]
  refine hraw.mono_outcome (x, st)
      (((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R) s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [specWithOptInv] at hq ⊢
    simp only [doReserveRawSpecWithStack, doReserveSpecWithStack,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpecWithStack,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpecWithStack,
      vecU8At_eq] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htrace, hq⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq
    rcases hq with ⟨p', hq⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨hp', hmem⟩
    have hlt : reserveCap x.cap.toNat x.bs.length x.additional < 2 ^ 64 := by omega
    have htoNat : (BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional)).toNat =
        reserveCap x.cap.toNat x.bs.length x.additional := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    have hlen_le : x.bs.length ≤ reserveCap x.cap.toNat x.bs.length x.additional := by
      dsimp [reserveCap, CryptoVerification.LibsignalTripleRatchet.reserveCap]; omega
    have hcap63' : reserveCap x.cap.toNat x.bs.length x.additional < 2 ^ 63 := by
      omega
    have hcap_ne : BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional) ≠ 0#64 := by
      intro heq
      have := congrArg BitVec.toNat heq
      rw [htoNat] at this
      change reserveCap x.cap.toNat x.bs.length x.additional = 0 at this
      dsimp [reserveCap, CryptoVerification.LibsignalTripleRatchet.reserveCap] at this; omega
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htrace, ?_⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨p', ?_⟩
    simp only [hcap_ne, ite_false, htoNat]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hlen_le, hcap63', hp'⟩, ?_⟩
    rwa [doReserve_post_repack]
  · dsimp only [specWithOptInv, doReserveRawSpecWithStack,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpecWithStack] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [specWithOptInv, doReserveRawSpecWithStack,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpecWithStack] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [specWithOptInv, doReserveRawSpecWithStack,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpecWithStack] at hq
    exact (not_satisfies_false_sepConj hq).elim

theorem do_reserve_ok_of_fg_opt {oimg : Option Obj.Image} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)} {hookStack : Nat}
    (hstack : (hookStack + 48) + 64 ≤ 2 ^ 64 := by decide)
    (hfg : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowName)
      (specWithOptInv oimg (finishGrowSpecWithStack M A lim hookStack))) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr doReserveName)
      (specWithOptInv oimg (doReserveSpecWithStack M A lim (hookStack + 48))) :=
  do_reserve_ok_of_raw_opt (do_reserve_raw_ok_of_fg_opt hstack hfg)

theorem do_reserve_ok_ext {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContractsBudget b M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr doReserveName)
      (doReserveSpec M A lim) :=
  subroutine_ok_of_optNone <|
    do_reserve_ok_of_raw_opt (subroutine_ok_to_optNone (do_reserve_raw_ok_ext hA))

theorem do_reserve_ok_trap {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {C : Crypto} {abs : String → Option (State → State)}
    (hA : AllocHooksBudgetBase M A lim abs) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr doReserveName)
      (doReserveSpec M A lim) :=
  do_reserve_ok_ext (AllocContractsBudget.of_tripleRatchetProgAt_trap b C M A lim abs hA)

/-- `<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]`
(`0x4cac`) meets `doReserveSpec M A lim` on `tripleRatchetProgAt`. -/
theorem do_reserve_ok {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {C : Crypto} {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hA : AllocHooksBudgetBase M A lim abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr doReserveName)
      (doReserveSpec M A lim) :=
  (trTrapProgAt_fnAddr_eq b C ctl abs doReserveName).rec
    (motive := fun addr _ =>
      subroutine_ok (tripleRatchetProgAt b C ctl abs) addr (doReserveSpec M A lim))
    (subroutine_ok_kit_of_trTrap (do_reserve_ok_trap hA))

theorem do_reserve_raw_ok_ext_x {img : Obj.Image} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContractsXBudget img M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr doReserveName)
      ((doReserveRawSpecX M A lim).inImage img) :=
  do_reserve_raw_ok_of_fg_opt (oimg := some img) (by decide)
    (finish_grow_ok_ext_x hA)

theorem do_reserve_ok_ext_x {img : Obj.Image} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContractsXBudget img M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr doReserveName)
      ((doReserveSpecX M A lim).inImage img) :=
  do_reserve_ok_of_raw_opt (oimg := some img) (do_reserve_raw_ok_ext_x hA)

/-! ## Relocatable Per-Block Proofs (`[LibsignalPlacement]`, Block `13`, Calling Block `45`) -/

private theorem finish_grow_1_zero_placed_ok_of_fg_opt [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hfg : subroutine_ok ((blkPC_45).rebase (blkPl_45).base H)
      (blkPl_45).base
      (finishGrowSpecWithStack M A lim hookStack)) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H)
      (blkPl_45).base
      (finishGrow1ZeroSpecWithStack M A lim (hookStack + 48)) := by
  refine subroutine_ok_outcome_intro ?_
  intro ⟨out, cap, ptr, new, bs, o0, o1, o2, fsp, st⟩ R s0 hpc hrun hpre hsp
  simp only [finishGrow1ZeroSpecWithStack, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap0, hbs, hle, hpos, hbound, hfit⟩, hmem⟩
  subst hfsp; subst hcap0; subst hbs
  let hcall : FinishGrowCall := ⟨out, 0#64, ptr, new, 1#64, 1#64, []⟩
  have hrlay : RustLayoutOk (new.toNat * (1#64 : BitVec 64).toNat) (1#64 : BitVec 64).toNat := by
    refine ⟨⟨by change 0 < new.toNat * 1; omega, ⟨0, rfl⟩, ?_⟩, by decide⟩
    change new.toNat * 1 + 1 ≤ 2 ^ 63; omega
  have hfit_env : LibsignalBinary.Heap.FitsEnv M lim st (FinishGrowEnv hcall) := by
    rw [fitsEnv_finishGrow_iff]
    have ha1 : (1#64 : BitVec 64).toNat = 1 := rfl
    simpa only [finishGrowEvents, hcall, BitVec.toNat_zero, ↓reduceIte, ha1, Nat.mul_one] using hfit
  have hpre' : s0.mem ⊨
      (finishGrowSpecWithStack M A lim hookStack).pre (hcall, st) s0 ∗ R := by
    simp only [finishGrowSpecWithStack,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowSpecWithStack,
      hcall, FinishGrowCall.oldBuf, ite_true, memRegion_24_cells, emp_sepConj,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, fun _ => trivial, Nat.zero_le _, hle, hpos,
      by decide, hrlay, hfit_env⟩, by simpa only [sepConj_assoc] using hmem⟩
  refine hfg.mono_outcome (hcall, st) R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [finishGrowSpecWithStack,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowSpecWithStack,
      finishGrow1ZeroSpecWithStack, hcall, finishGrowEvents, BitVec.toNat_zero, ↓reduceIte,
      pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj,
      sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨p', hq⟩
    have hm1 : new.toNat * (1#64 : BitVec 64).toNat = new.toNat := Nat.mul_one _
    have ha1 : (1#64 : BitVec 64).toNat = 1 := rfl
    rw [hm1] at hq
    rw [ha1] at hq
    refine ⟨p', BitVec.ofNat 64 new.toNat, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨⟨hp', _, htrace⟩, hrest⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hp', htrace⟩, ?_⟩
    have hrest' : sf.mem ⊨
        ((out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ BitVec.ofNat 64 new.toNat) ∗
          A.live p' new.toNat 1 ∗ memRegion p' new.toNat ∗
          A.pool lim (M.stepEvents (rustAllocEvents new.toNat 1) st) sf ∗
          stackAt s0.sp (hookStack + 48)) ∗ R := by
      simpa only [sepConj_assoc] using hrest
    rw [fg0_post_repack] at hrest'
    simpa only [sepConj_assoc] using hrest'
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hq⟩))

private theorem finish_grow_1_ne_placed_ok_of_fg_opt [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hfg : subroutine_ok ((blkPC_45).rebase (blkPl_45).base H)
      (blkPl_45).base
      (finishGrowSpecWithStack M A lim hookStack)) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H)
      (blkPl_45).base
      (finishGrow1NeSpecWithStack M A lim (hookStack + 48)) := by
  refine subroutine_ok_outcome_intro ?_
  intro ⟨out, cap, ptr, new, bs, o0, o1, o2, fsp, st⟩ R s0 hpc hrun hpre hsp
  simp only [finishGrow1NeSpecWithStack, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap, hbs, hle, hpos, hbound, hfit⟩, hmem⟩
  subst hfsp
  let hcall : FinishGrowCall := ⟨out, cap, ptr, new, 1#64, 1#64, bs⟩
  have hcap_nat_ne : cap.toNat ≠ 0 := fun hc => hcap (BitVec.eq_of_toNat_eq hc)
  have hrlay : RustLayoutOk (new.toNat * (1#64 : BitVec 64).toNat) (1#64 : BitVec 64).toNat := by
    refine ⟨⟨by change 0 < new.toNat * 1; omega, ⟨0, rfl⟩, ?_⟩, by decide⟩
    change new.toNat * 1 + 1 ≤ 2 ^ 63; omega
  have hfit_env : LibsignalBinary.Heap.FitsEnv M lim st (FinishGrowEnv hcall) := by
    rw [fitsEnv_finishGrow_iff]
    have ha1 : (1#64 : BitVec 64).toNat = 1 := rfl
    simpa only [finishGrowEvents, hcall, hcap_nat_ne, ↓reduceIte, ha1, Nat.mul_one] using hfit
  have hpre' : s0.mem ⊨
      (finishGrowSpecWithStack M A lim hookStack).pre (hcall, st) s0 ∗ R := by
    simp only [finishGrowSpecWithStack,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowSpecWithStack,
      hcall, FinishGrowCall.oldBuf, RustCliAllocBudget.repAlloc_live, hcap, ite_false,
      memRegion_24_cells, sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    have hm_cap : cap.toNat * (1#64 : BitVec 64).toNat = cap.toNat := Nat.mul_one _
    have ha1 : (1#64 : BitVec 64).toNat = 1 := rfl
    rw [hm_cap, ha1]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, False.elim, hbs, hle, hpos,
      by decide, hrlay, hfit_env⟩, by simpa only [sepConj_assoc] using hmem⟩
  refine hfg.mono_outcome (hcall, st) R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [finishGrowSpecWithStack,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowSpecWithStack,
      finishGrow1NeSpecWithStack, hcall, finishGrowEvents, hcap_nat_ne, ↓reduceIte,
      sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨p', hq⟩
    have hm_new : new.toNat * (1#64 : BitVec 64).toNat = new.toNat := Nat.mul_one _
    have hm_cap : cap.toNat * (1#64 : BitVec 64).toNat = cap.toNat := Nat.mul_one _
    have ha1 : (1#64 : BitVec 64).toNat = 1 := rfl
    rw [hm_new, hm_cap, ha1] at hq
    refine ⟨p', BitVec.ofNat 64 new.toNat, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨⟨hp', _, htrace⟩, hrest⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hp', htrace⟩, ?_⟩
    have hrest' : sf.mem ⊨
        ((out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ BitVec.ofNat 64 new.toNat) ∗
          A.live p' new.toNat 1 ∗ (p' ↦ₛ bs) ∗
          memRegion (p' + BitVec.ofNat 64 bs.length) (new.toNat - bs.length) ∗
          A.pool lim (M.stepEvents (rustReallocEvents cap.toNat new.toNat 1) st) sf ∗
          stackAt s0.sp (hookStack + 48)) ∗ R := by
      simpa only [sepConj_assoc] using hrest
    rw [fg1_post_repack] at hrest'
    simpa only [sepConj_assoc] using hrest'
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hq⟩))

theorem do_reserve_raw_placed_ok_of_fg_opt [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hstack : (hookStack + 48) + 64 ≤ 2 ^ 64 := by decide)
    (hfg : subroutine_ok ((blkPC_45).rebase (blkPl_45).base H)
      (blkPl_45).base
      (finishGrowSpecWithStack M A lim hookStack)) :
    subroutine_ok ((blkPC_13).rebase (blkPl_13).base H)
      (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveRawSpecWithStack M A lim (hookStack + 48))) := by
  unfold withLsCodeLoaded doReserveRawSpecWithStack
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpecWithStack
  simp only [stackAt_doReserve_opt hstack, sepExists_sepConj_right]
  have hfg0 := ls_subroutine_ok_of_block (callerProg := (blkPC_13).rebase (blkPl_13).base H)
    (subroutine_ok_withLsCodeLoaded_of_plain (finish_grow_1_zero_placed_ok_of_fg_opt hfg))
  have hfg1 := ls_subroutine_ok_of_block (callerProg := (blkPC_13).rebase (blkPl_13).base H)
    (subroutine_ok_withLsCodeLoaded_of_plain (finish_grow_1_ne_placed_ok_of_fg_opt hfg))
  change subroutine_ok _ (lsmpl.base 45) _ at hfg0 hfg1
  dsimp only [withLsCodeLoaded,
    finishGrow1ZeroSpecWithStack, finishGrow1NeSpecWithStack] at hfg0 hfg1
  clear hfg
  wp_init x s0
  obtain ⟨⟨v, cap, ptr, bs, additional⟩, st⟩ := x
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hx1_eq : (s0.readReg64 .x1).toNat = bs.length := by assumption
  have hx2_eq : (s0.readReg64 .x2).toNat = additional := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat := by assumption
  have hfit0 : LibsignalBinary.Heap.FitsEnv M lim st
      (DoReserveEnv ⟨v, cap, ptr, bs, additional⟩) := by assumption
  have hbound : reserveCap cap.toNat bs.length additional + 1 ≤ 2 ^ 63 := by
    dsimp [reserveCap, CryptoVerification.LibsignalTripleRatchet.reserveCap] at *; omega
  have hmax : max (max (bs.length + additional) (2 * cap.toNat)) 8 + 1 ≤ 2 ^ 63 := hbound
  have hcs := adds_cs_eq_false (x2 := s0.readReg64 .x2) (x1 := s0.readReg64 .x1) (by
    rw [hx2_eq, hx1_eq]; omega)
  have hnew_eq := reserve_new_cap_eq (cap := cap) hx1_eq hx2_eq hbound
  let new := BitVec.ofNat 64 (reserveCap cap.toNat bs.length additional)
  have hnew_toNat : new.toNat = reserveCap cap.toNat bs.length additional := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by
    rw [hnew_toNat]; dsimp [reserveCap, CryptoVerification.LibsignalTripleRatchet.reserveCap]; omega
  have hnew_pos : 0 < new.toNat := by
    rw [hnew_toNat]; dsimp [reserveCap, CryptoVerification.LibsignalTripleRatchet.reserveCap]; omega
  have hnew_bound : new.toNat + 1 ≤ 2 ^ 63 := by omega
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hbs_le_cap)
    subst hbs
    have hfit_ev : FitsEvents M lim st (rustAllocEvents new.toNat 1) := by
      simpa only [fitsEnv_doReserve_iff, doReserveEvents, ↓reduceIte, ← hnew_toNat] using hfit0
    have hnew_eq0 :
        (if (8#64).ult
              (if (0#64).ult (s0.readReg64 .x2 + s0.readReg64 .x1) = true then
                s0.readReg64 .x2 + s0.readReg64 .x1
               else 0#64) = true then
          if (0#64).ult (s0.readReg64 .x2 + s0.readReg64 .x1) = true then
            s0.readReg64 .x2 + s0.readReg64 .x1
          else 0#64
         else 8#64) = new := hnew_eq
    simp only [ite_true, emp_sepConj, pointsToBytes_nil,
      List.length_nil, BitVec.add_zero, Nat.sub_zero]
    apply sepWP_seq_lscl hcl0 (mid := lsmpl.base 45)
    wp_steps_sync_pool (lsmpl.base 45)
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    intro hcl1
    wp_call hfg0 (s0.sp - 56#64, 0#64, ptr, new, [], v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64, st)
    wp_steps_sync_pool (s0.readReg64 .lr)
    simp only [doReserveEvents, ↓reduceIte, ← hnew_toNat]
    wp_done
  · have hcap0' : cap ≠ 0 := hcap0
    have hfit_ev : FitsEvents M lim st (rustReallocEvents cap.toNat new.toNat 1) := by
      simpa only [fitsEnv_doReserve_iff, doReserveEvents, hcap0, ↓reduceIte, ← hnew_toNat] using hfit0
    simp only [hcap0, ite_false, sepConj_assoc]
    have hsub_eq : reserveCap cap.toNat bs.length additional - bs.length = new.toNat - bs.length := by
      rw [hnew_toNat]
    rw [hsub_eq]
    apply sepWP_seq_lscl hcl0 (mid := lsmpl.base 45)
    wp_steps_sync_pool (lsmpl.base 45)
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    intro hcl1
    wp_call hfg1 (s0.sp - 56#64, cap, ptr, new, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64, st)
    wp_steps_sync_pool (s0.readReg64 .lr)
    simp only [doReserveEvents, hcap0, ↓reduceIte, ← hnew_toNat]
    wp_done

theorem do_reserve_placed_ok_of_raw_opt [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {fgStack : Nat}
    (hraw : subroutine_ok ((blkPC_13).rebase (blkPl_13).base H)
      (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveRawSpecWithStack M A lim fgStack))) :
    subroutine_ok ((blkPC_13).rebase (blkPl_13).base H)
      (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveSpecWithStack M A lim fgStack)) := by
  refine subroutine_ok_outcome_intro ?_
  intro ⟨x, st⟩ R s0 hpc hrun hpre hsp
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  simp only [doReserveSpecWithStack,
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpecWithStack,
    vecU8At_eq, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hbound, hfit⟩, ⟨hlen, hcap63, hptr⟩, hmem⟩
  have hpre' : s0.mem ⊨
      (withLsCodeLoaded lsmpl (doReserveRawSpecWithStack M A lim fgStack)).pre (x, st) s0 ∗
      (((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R) := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl0, ?_⟩
    simp only [doReserveRawSpecWithStack,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpecWithStack,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hx4, hlen, hptr, hbound, hfit⟩, ?_⟩
    rwa [doReserve_pre_repack]
  refine hraw.mono_outcome (x, st)
      (((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R) s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded] at hq ⊢
    simp only [doReserveRawSpecWithStack, doReserveSpecWithStack,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpecWithStack,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpecWithStack,
      vecU8At_eq] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htrace, hq⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq
    rcases hq with ⟨p', hq⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨hp', hmem⟩
    have hlt : reserveCap x.cap.toNat x.bs.length x.additional < 2 ^ 64 := by omega
    have htoNat : (BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional)).toNat =
        reserveCap x.cap.toNat x.bs.length x.additional := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    have hlen_le : x.bs.length ≤ reserveCap x.cap.toNat x.bs.length x.additional := by
      dsimp [reserveCap, CryptoVerification.LibsignalTripleRatchet.reserveCap]; omega
    have hcap63' : reserveCap x.cap.toNat x.bs.length x.additional < 2 ^ 63 := by
      omega
    have hcap_ne : BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional) ≠ 0#64 := by
      intro heq
      have := congrArg BitVec.toNat heq
      rw [htoNat] at this
      change reserveCap x.cap.toNat x.bs.length x.additional = 0 at this
      dsimp [reserveCap, CryptoVerification.LibsignalTripleRatchet.reserveCap] at this; omega
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htrace, ?_⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨p', ?_⟩
    simp only [hcap_ne, ite_false, htoNat]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hlen_le, hcap63', hp'⟩, ?_⟩
    rwa [doReserve_post_repack]
  · dsimp only [withLsCodeLoaded, doReserveRawSpecWithStack,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpecWithStack] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeLoaded, doReserveRawSpecWithStack,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpecWithStack] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeLoaded, doReserveRawSpecWithStack,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpecWithStack] at hq
    exact (not_satisfies_false_sepConj hq).elim

/-- Relocatable `<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]`
(Block `13`) meets `withLsCodeLoaded lsmpl (doReserveRawSpec M A lim)`. -/
theorem do_reserve_raw_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_13).rebase (blkPl_13).base H)
      (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveRawSpec M A lim)) :=
  do_reserve_raw_placed_ok_of_fg_opt (hookStack := allocHookStack) (by decide)
    (finish_grow_placed_ok hshim halloc hrealloc)

/-- Relocatable `<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]`
(Block `13`) meets `withLsCodeLoaded lsmpl (doReserveSpec M A lim)`. -/
theorem do_reserve_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_13).rebase (blkPl_13).base H)
      (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveSpec M A lim)) :=
  do_reserve_placed_ok_of_raw_opt (do_reserve_raw_placed_ok hshim halloc hrealloc)

theorem do_reserve_raw_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_13).rebase (blkPl_13).base H)
      (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveRawSpecX M A lim)) :=
  do_reserve_raw_placed_ok_of_fg_opt (hookStack := extHookStack) (by decide)
    (finish_grow_placed_ok_x hshim halloc hrealloc)

theorem do_reserve_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_13).rebase (blkPl_13).base H)
      (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveSpecX M A lim)) :=
  do_reserve_placed_ok_of_raw_opt (do_reserve_raw_placed_ok_x hshim halloc hrealloc)

theorem do_reserve_raw_placed_ok_noOom [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocNoOomSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocNoOomSpec M A lim)) :
    subroutine_ok ((blkPC_13).rebase (blkPl_13).base H)
      (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveRawSpec M A lim)) :=
  do_reserve_raw_placed_ok_of_fg_opt (hookStack := allocHookStack) (by decide)
    (finish_grow_placed_ok_noOom hshim halloc hrealloc)

theorem do_reserve_placed_ok_noOom [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocNoOomSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocNoOomSpec M A lim)) :
    subroutine_ok ((blkPC_13).rebase (blkPl_13).base H)
      (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveSpec M A lim)) :=
  do_reserve_placed_ok_of_raw_opt (do_reserve_raw_placed_ok_noOom hshim halloc hrealloc)

theorem do_reserve_raw_placed_ok_x_noOom [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocNoOomSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocNoOomSpec M A lim)) :
    subroutine_ok ((blkPC_13).rebase (blkPl_13).base H)
      (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveRawSpecX M A lim)) :=
  do_reserve_raw_placed_ok_of_fg_opt (hookStack := extHookStack) (by decide)
    (finish_grow_placed_ok_x_noOom hshim halloc hrealloc)

theorem do_reserve_placed_ok_x_noOom [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocNoOomSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocNoOomSpec M A lim)) :
    subroutine_ok ((blkPC_13).rebase (blkPl_13).base H)
      (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveSpecX M A lim)) :=
  do_reserve_placed_ok_of_raw_opt (do_reserve_raw_placed_ok_x_noOom hshim halloc hrealloc)

end LibsignalBinary.Proofs.TripleRatchet.Alloc.DoReserveBudget

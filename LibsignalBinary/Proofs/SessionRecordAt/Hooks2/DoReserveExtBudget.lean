/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.AdaptersBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DoReserveBudget
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `RawVecInner::reserve::do_reserve_and_handle` (Block `13`)

Verifies relocatable `<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle`
(Block `13`, calling `finish_grow` in Block `45`) against the budget-threaded specifications
`doReserveRawSpecX M A lim` and `doReserveSpecX M A lim` under `AllocContractsPlaced M A lim H`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DoReserveExtBudget

open Arm64 ProofLib SepProp
open CryptoVerification (
  LibsignalPlacement LibsignalHooks LibsignalCodeLoaded IsLsBlockProg
  lsmpl withLsCodeLoaded withLsCl extract_withLsCodeLoaded
  lsρ lsRustAllocSym lsRustDeallocSym lsRustReallocSym lsRustNoAllocShimSym
  blkPC_13 blkPl_13 blkPC_45 blkPl_45 sepWP_seq_lscl ls_subroutine_ok_of_block
)
open CryptoVerification.RustHeap (allocHookStack vecU8At)
open CryptoVerification.LibsignalTripleRatchet (
  DoReserveCall FinishGrowCall extHookStack ls_subroutine_ok_cl_of_callee
)
open Proofs.libsignal.Hooks2 (subroutine_ok_withLsCl_map')
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel BudgetLimits FitsEnv FitsEvents NullAllowed
  RustCliAllocBudget RustLayoutOk VmPreserved
  rustAllocEvents rustDeallocEvents rustReallocEvents
  rustCliAllocBudgetSpec rustCliDeallocBudgetSpec rustCliReallocBudgetSpec
)
open LibsignalBinary.Heap.IfaceLemmas (withExternStackFromAllocOom')
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  rustCliAllocBudgetSpecWithStack rustCliDeallocBudgetExternSpecWithStack
  rustCliReallocBudgetExternSpecWithStack
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionShimBudgetSpec sessionMemmoveBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  FinishGrowEnv finishGrowEvents fitsEnv_finishGrow_iff reserveCap session2ShimBudgetSpecX
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DefsBudget (
  subroutine_ok_withLsCl_map_oom' subroutine_ok_withLsCodeLoaded_map_oom'
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.AdaptersBudget (
  Stage2ContractsPlaced rustDeallocLayoutBudgetSpec'
)
open LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget (
  finish_grow_placed_ok_ext_x
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Re-exported envelopes, specs, and contract bundle -/

abbrev doReserveStackX : Nat := (extHookStack + 48) + 64
abbrev DoReserveEnv := LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.DoReserveEnv
abbrev doReserveEvents := LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveEvents
abbrev fitsEnv_doReserve_iff :=
  @LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.fitsEnv_doReserve_iff
abbrev doReserveRawSpecX :=
  @LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpecX
abbrev doReserveSpecX :=
  @LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpecX
abbrev AllocContractsPlaced :=
  @LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget.AllocContractsPlaced

/-! ## Bridge from `Stage2ContractsPlaced` to `AllocContractsPlaced` -/

private theorem stackAt_extHookStack_eq (sp : BitVec 64) :
    stackAt sp extHookStack =
      stackAt sp allocHookStack ∗ memRegion (sp - 16384#64) 12288 := by
  have hs := ProofLib.stackAt_split_bottom sp 4096 12288 (by decide)
  dsimp only [extHookStack, allocHookStack]
  rw [sepConj_comm] at hs
  exact hs

/-- Bridges `Stage2ContractsPlaced A lim H` (`withExternStackFromAllocOom'`) to
`Stage1X.GrowOneXBudget.AllocContractsPlaced M A lim H` (`extHookStack = 16384`). -/
theorem allocContractsPlaced_of_stage2ContractsPlaced [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : Stage2ContractsPlaced A lim H) :
    AllocContractsPlaced M A lim H where
  alloc := fun {callerProg callerBlk _} => by
    refine subroutine_ok_withLsCl_map_oom' (hC.alloc (callerProg := callerProg))
      fun ⟨size, align, st⟩ R s0 hpre => ⟨(size, align, st), R, ?_, fun sf hpost => ?_, fun _ ho => ho⟩
    · dsimp only [rustCliAllocBudgetSpecWithStack, withExternStackFromAllocOom',
        Arm64.Spec.withExternStackFromAllocOom', rustCliAllocBudgetSpec] at hpre ⊢
      rw [stackAt_extHookStack_eq s0.sp] at hpre
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
    · dsimp only [rustCliAllocBudgetSpecWithStack, withExternStackFromAllocOom',
        Arm64.Spec.withExternStackFromAllocOom', rustCliAllocBudgetSpec] at hpost ⊢
      rw [stackAt_extHookStack_eq s0.sp]
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
  dealloc := fun {callerProg callerBlk _} => by
    refine subroutine_ok_withLsCl_map' (hC.deallocLayout (callerProg := callerProg))
      fun ⟨p, size, align, st⟩ R s0 hpre => ⟨(p, size, align, st), R, ?_, fun sf hpost => ?_⟩
    · dsimp only [rustCliDeallocBudgetExternSpecWithStack,
        LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack,
        withExternStackFromAllocOom', Arm64.Spec.withExternStackFromAllocOom',
        rustDeallocLayoutBudgetSpec', rustCliDeallocBudgetSpec] at hpre ⊢
      rw [stackAt_extHookStack_eq s0.sp] at hpre
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
      rcases hpre with ⟨⟨hx0, hx1, hx2, hlay, hlr⟩, hrest⟩
      exact ⟨hlay, ⟨hx0, hx1, hx2, hlr⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hrest⟩
    · dsimp only [rustCliDeallocBudgetExternSpecWithStack,
        LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack,
        withExternStackFromAllocOom', Arm64.Spec.withExternStackFromAllocOom',
        rustDeallocLayoutBudgetSpec', rustCliDeallocBudgetSpec] at hpost ⊢
      rw [stackAt_extHookStack_eq s0.sp]
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      rcases hpost with ⟨⟨hacp, _⟩, hrest⟩
      exact ⟨hacp.2.1, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hrest⟩
  realloc := fun {callerProg callerBlk _} => by
    refine subroutine_ok_withLsCl_map_oom' (hC.realloc (callerProg := callerProg))
      fun ⟨p, old, align, new, bs, st⟩ R s0 hpre =>
        ⟨(p, old, align, new, bs, st), R, ?_, fun sf hpost => ?_, fun _ ho => ho⟩
    · dsimp only [rustCliReallocBudgetExternSpecWithStack,
        LibsignalBinary.Heap.rustCliReallocBudgetExternSpecWithStack,
        withExternStackFromAllocOom', Arm64.Spec.withExternStackFromAllocOom',
        rustCliReallocBudgetSpec] at hpre ⊢
      rw [stackAt_extHookStack_eq s0.sp] at hpre
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
      rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, _hold, hnew, hbs1, hbs2⟩, hrest⟩
      exact ⟨⟨hx0, hx1, hx2, hx3, hnew, hbs1, hbs2⟩,
        Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hrest⟩
    · dsimp only [rustCliReallocBudgetExternSpecWithStack,
        LibsignalBinary.Heap.rustCliReallocBudgetExternSpecWithStack,
        withExternStackFromAllocOom', Arm64.Spec.withExternStackFromAllocOom',
        rustCliReallocBudgetSpec] at hpost ⊢
      rw [stackAt_extHookStack_eq s0.sp]
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost
      rcases hpost with ⟨hacp, hrest⟩
      by_cases h0 : sf.readReg64 .x0 = 0
      · simp only [h0, ↓reduceIte] at hrest ⊢
        have hrest' : sf.mem ⊨ ⌜NullAllowed new align⌝ ∗
            (A.pool lim st sf ∗ (stackAt s0.sp allocHookStack ∗ memRegion (s0.sp - 16384#64) 12288) ∗
              A.live p old align ∗ (p ↦ₛ bs) ∗
              memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗ R) :=
          Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hrest
        rw [satisfies_pure_sepConj] at hrest'
        refine Satisfies.mono (Entails.of_eq (by sep_ac_rfl))
          (P := ⌜sf.trace = s0.trace ∧ NullAllowed new align⌝ ∗
            (A.pool lim st sf ∗ (stackAt s0.sp allocHookStack ∗ memRegion (s0.sp - 16384#64) 12288) ∗
              A.live p old align ∗ (p ↦ₛ bs) ∗
              memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗ R)) ?_
        rw [satisfies_pure_sepConj]
        exact ⟨⟨hacp.2.1, hrest'.1⟩, hrest'.2⟩
      · simp only [h0, ↓reduceIte] at hrest ⊢
        have hrest' : sf.mem ⊨ ⌜(sf.readReg64 .x0).toNat % align = 0⌝ ∗
            (A.pool lim (M.stepEvents (rustReallocEvents old new align) st) sf ∗
              (stackAt s0.sp allocHookStack ∗ memRegion (s0.sp - 16384#64) 12288) ∗
              A.live (sf.readReg64 .x0) new align ∗ (sf.readReg64 .x0 ↦ₛ bs) ∗
              memRegion (sf.readReg64 .x0 + BitVec.ofNat 64 bs.length) (new - bs.length) ∗ R) :=
          Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hrest
        rw [satisfies_pure_sepConj] at hrest'
        refine Satisfies.mono (Entails.of_eq (by sep_ac_rfl))
          (P := ⌜(sf.readReg64 .x0).toNat % align = 0 ∧ sf.trace = s0.trace⌝ ∗
            (A.pool lim (M.stepEvents (rustReallocEvents old new align) st) sf ∗
              (stackAt s0.sp allocHookStack ∗ memRegion (s0.sp - 16384#64) 12288) ∗
              A.live (sf.readReg64 .x0) new align ∗ (sf.readReg64 .x0 ↦ₛ bs) ∗
              memRegion (sf.readReg64 .x0 + BitVec.ofNat 64 bs.length) (new - bs.length) ∗ R)) ?_
        rw [satisfies_pure_sepConj]
        exact ⟨⟨hrest'.1, hacp.2.1⟩, hrest'.2⟩
  shim := fun {callerProg callerBlk _} => by
    refine subroutine_ok_withLsCl_map' (hC.shim_vm (callerProg := callerProg))
      fun _ R s0 hpre => ⟨(), R, ?_, fun sf hpost => ?_⟩
    · dsimp only [withVmPreserved, Spec.withHookStack,
        CryptoVerification.LibsignalTripleRatchet.sessionShimSpec,
        session2ShimBudgetSpecX] at hpre ⊢
      simpa only [emp_sepConj, sepConj_assoc] using hpre
    · dsimp only [withVmPreserved, Spec.withHookStack,
        CryptoVerification.LibsignalTripleRatchet.sessionShimSpec,
        session2ShimBudgetSpecX] at hpost ⊢
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hpost.2.1, hpost.1⟩, hpost.2.2⟩
  session_memmove := hC.memmove

/-! ## Block `13` (`do_reserve_and_handle`) verification -/

private abbrev FG1BudgetGhost (M : AllocCostModel) :=
  BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) ×
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × M.σ

private def finishGrow1ZeroSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (FG1BudgetGhost M) where
  pre := fun (out, cap, ptr, new, bs, o0, o1, o2, fsp, st) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.readReg64 .x4 = 1#64 ∧ s.readReg64 .x5 = 1#64 ∧
      s.sp = fsp ∧ cap = 0#64 ∧ bs = [] ∧ cap.toNat ≤ new.toNat ∧
      0 < new.toNat ∧ new.toNat + 1 ≤ 2 ^ 63 ∧
      FitsEvents M lim st (rustAllocEvents new.toNat 1)⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.pool lim st s ∗ stackAt fsp (extHookStack + 48)
  post := fun (out, _cap, _ptr, new, _bs, _o0, _o1, _o2, fsp, st) s0 sf =>
    ∃∗ p' : BitVec 64, ∃∗ o2' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
      A.live p' new.toNat 1 ∗ memRegion p' new.toNat ∗
      A.pool lim (M.stepEvents (rustAllocEvents new.toNat 1) st) sf ∗
      stackAt fsp (extHookStack + 48) ∗
      (out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')

private def finishGrow1NeSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (FG1BudgetGhost M) where
  pre := fun (out, cap, ptr, new, bs, o0, o1, o2, fsp, st) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.readReg64 .x4 = 1#64 ∧ s.readReg64 .x5 = 1#64 ∧
      s.sp = fsp ∧ cap ≠ 0#64 ∧ bs.length ≤ cap.toNat ∧ cap.toNat ≤ new.toNat ∧
      0 < new.toNat ∧ new.toNat + 1 ≤ 2 ^ 63 ∧
      FitsEvents M lim st (rustReallocEvents cap.toNat new.toNat 1)⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
    memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
    A.pool lim st s ∗ stackAt fsp (extHookStack + 48)
  post := fun (out, cap, _ptr, new, bs, _o0, _o1, _o2, fsp, st) s0 sf =>
    ∃∗ p' : BitVec 64, ∃∗ o2' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
      A.live p' new.toNat 1 ∗ (p' ↦ₛ bs) ∗
      memRegion (p' + BitVec.ofNat 64 bs.length) (new.toNat - bs.length) ∗
      A.pool lim (M.stepEvents (rustReallocEvents cap.toNat new.toNat 1) st) sf ∗
      stackAt fsp (extHookStack + 48) ∗
      (out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')

private theorem fg0_post_repack (C0 C1 C2 L1 L2 P S R : SepProp) :
    (C0 ∗ C1 ∗ C2 ∗ L1 ∗ L2 ∗ P ∗ S) ∗ R =
      (L1 ∗ L2 ∗ P ∗ S ∗ C0 ∗ C1 ∗ C2) ∗ R := by
  sep_ac_rfl

private theorem fg1_post_repack (C0 C1 C2 L1 L2 L3 P S R : SepProp) :
    (C0 ∗ C1 ∗ C2 ∗ L1 ∗ L2 ∗ L3 ∗ P ∗ S) ∗ R =
      (L1 ∗ L2 ∗ L3 ∗ P ∗ S ∗ C0 ∗ C1 ∗ C2) ∗ R := by
  sep_ac_rfl

private theorem memRegion_24_cells (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v2) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v0)) := by
  rw [show (24 : Nat) = 8 + (8 + 8) by rfl, memRegion_split a 8 (8 + 8) (by decide),
    memRegion_split (a + 8#64) 8 8 (by decide), memRegion_eight, memRegion_eight, memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem stackAt_doReserve_x (sp : BitVec 64) :
    stackAt sp ((extHookStack + 48) + 64) =
      stackAt (sp - 64#64) (extHookStack + 48) ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
         ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
          ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
          ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
          ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
  have h1 := CryptoVerification.LibsignalTripleRatchet.stackAt_split_cells sp (extHookStack + 48) 8
    (by decide)
  have hc8 : cells (sp - 64#64) 8 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
        ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
        ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
    cells_unfold
  rw [h1, hc8]

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

private theorem finish_grow_1_zero_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hfg : subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base
      (withLsCodeLoaded lsmpl
        (LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowSpecX M A lim))) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base
      (withLsCodeLoaded lsmpl (finishGrow1ZeroSpecX M A lim)) := by
  refine subroutine_ok_withLsCodeLoaded_map_oom' hfg
    fun ⟨out, cap, ptr, new, bs, o0, o1, o2, fsp, st⟩ R s0 hpre => ?_
  simp only [finishGrow1ZeroSpecX, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap0, hbs, hle, hpos, hbound, hfit⟩, hmem⟩
  subst hfsp; subst hcap0; subst hbs
  let hcall : FinishGrowCall := ⟨out, 0#64, ptr, new, 1#64, 1#64, []⟩
  have hrlay : RustLayoutOk (new.toNat * (1#64 : BitVec 64).toNat) (1#64 : BitVec 64).toNat := by
    refine ⟨⟨by change 0 < new.toNat * 1; omega, ⟨0, rfl⟩, ?_⟩, by decide⟩
    change new.toNat * 1 + 1 ≤ 2 ^ 63; omega
  have hfit_env : FitsEnv M lim st (FinishGrowEnv hcall) := by
    rw [fitsEnv_finishGrow_iff]
    have ha1 : (1#64 : BitVec 64).toNat = 1 := rfl
    simpa only [finishGrowEvents, hcall, BitVec.toNat_zero, ↓reduceIte, ha1, Nat.mul_one] using hfit
  refine ⟨(hcall, st), R, ?_, fun sf hq => ?_, fun _ ho => ho⟩
  · simp only [LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowSpecX,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowSpecWithStack,
      hcall, FinishGrowCall.oldBuf, ite_true, memRegion_24_cells, emp_sepConj,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, fun _ => trivial, Nat.zero_le _, hle, hpos,
      by decide, hrlay, hfit_env⟩, by simpa only [sepConj_assoc] using hmem⟩
  · simp only [LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowSpecX,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowSpecWithStack,
      finishGrow1ZeroSpecX, hcall, finishGrowEvents, BitVec.toNat_zero, ↓reduceIte,
      pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj,
      sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨p', hq⟩
    have hm1 : new.toNat * (1#64 : BitVec 64).toNat = new.toNat := Nat.mul_one _
    have ha1 : (1#64 : BitVec 64).toNat = 1 := rfl
    rw [hm1, ha1] at hq
    refine ⟨p', BitVec.ofNat 64 new.toNat, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨⟨hp', _, htrace⟩, hrest⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hp', htrace⟩, ?_⟩
    have hrest' : sf.mem ⊨
        ((out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ BitVec.ofNat 64 new.toNat) ∗
          A.live p' new.toNat 1 ∗ memRegion p' new.toNat ∗
          A.pool lim (M.stepEvents (rustAllocEvents new.toNat 1) st) sf ∗
          stackAt s0.sp (extHookStack + 48)) ∗ R := by
      simpa only [sepConj_assoc] using hrest
    rw [fg0_post_repack] at hrest'
    simpa only [sepConj_assoc] using hrest'

private theorem finish_grow_1_ne_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hfg : subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base
      (withLsCodeLoaded lsmpl
        (LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowSpecX M A lim))) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base
      (withLsCodeLoaded lsmpl (finishGrow1NeSpecX M A lim)) := by
  refine subroutine_ok_withLsCodeLoaded_map_oom' hfg
    fun ⟨out, cap, ptr, new, bs, o0, o1, o2, fsp, st⟩ R s0 hpre => ?_
  simp only [finishGrow1NeSpecX, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap, hbs, hle, hpos, hbound, hfit⟩, hmem⟩
  subst hfsp
  let hcall : FinishGrowCall := ⟨out, cap, ptr, new, 1#64, 1#64, bs⟩
  have hcap_nat_ne : cap.toNat ≠ 0 := fun hc => hcap (BitVec.eq_of_toNat_eq hc)
  have hrlay : RustLayoutOk (new.toNat * (1#64 : BitVec 64).toNat) (1#64 : BitVec 64).toNat := by
    refine ⟨⟨by change 0 < new.toNat * 1; omega, ⟨0, rfl⟩, ?_⟩, by decide⟩
    change new.toNat * 1 + 1 ≤ 2 ^ 63; omega
  have hfit_env : FitsEnv M lim st (FinishGrowEnv hcall) := by
    rw [fitsEnv_finishGrow_iff]
    have ha1 : (1#64 : BitVec 64).toNat = 1 := rfl
    simpa only [finishGrowEvents, hcall, hcap_nat_ne, ↓reduceIte, ha1, Nat.mul_one] using hfit
  refine ⟨(hcall, st), R, ?_, fun sf hq => ?_, fun _ ho => ho⟩
  · simp only [LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowSpecX,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowSpecWithStack,
      hcall, FinishGrowCall.oldBuf, RustCliAllocBudget.repAlloc_live_norm, hcap, ite_false,
      memRegion_24_cells, sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    have hm_cap : cap.toNat * (1#64 : BitVec 64).toNat = cap.toNat := Nat.mul_one _
    have ha1 : (1#64 : BitVec 64).toNat = 1 := rfl
    rw [hm_cap, ha1]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, False.elim, hbs, hle, hpos,
      by decide, hrlay, hfit_env⟩, by simpa only [sepConj_assoc] using hmem⟩
  · simp only [LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowSpecX,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowSpecWithStack,
      finishGrow1NeSpecX, hcall, finishGrowEvents, hcap_nat_ne, ↓reduceIte,
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
          stackAt s0.sp (extHookStack + 48)) ∗ R := by
      simpa only [sepConj_assoc] using hrest
    rw [fg1_post_repack] at hrest'
    simpa only [sepConj_assoc] using hrest'

/-- Relocatable `RawVecInner::reserve::do_reserve_and_handle` (Block `13`) satisfies
`withLsCodeLoaded lsmpl (doReserveRawSpecX M A lim)` under `AllocContractsPlaced M A lim H`. -/
theorem do_reserve_raw_placed_ok_ext_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsPlaced M A lim H) :
    subroutine_ok ((blkPC_13).rebase (blkPl_13).base H)
      (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveRawSpecX M A lim)) := by
  have hfg := finish_grow_placed_ok_ext_x hA
  have hfg0 := ls_subroutine_ok_of_block (callerProg := (blkPC_13).rebase (blkPl_13).base H)
    (finish_grow_1_zero_placed_ok_x hfg)
  have hfg1 := ls_subroutine_ok_of_block (callerProg := (blkPC_13).rebase (blkPl_13).base H)
    (finish_grow_1_ne_placed_ok_x hfg)
  change subroutine_ok _ (lsmpl.base 45) _ at hfg0 hfg1
  dsimp only [withLsCodeLoaded, finishGrow1ZeroSpecX, finishGrow1NeSpecX] at hfg0 hfg1
  clear hfg
  unfold withLsCodeLoaded doReserveRawSpecX
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpecX
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpecWithStack
  dsimp only [LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowStackX]
  simp only [stackAt_doReserve_x, sepExists_sepConj_right, sepExists_sepConj_left]
  wp_init x s0
  obtain ⟨⟨v, cap, ptr, bs, additional⟩, st⟩ := x
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hx1_eq : (s0.readReg64 .x1).toNat = bs.length := by assumption
  have hx2_eq : (s0.readReg64 .x2).toNat = additional := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat := by assumption
  have hfit0 : FitsEnv M lim st (DoReserveEnv ⟨v, cap, ptr, bs, additional⟩) := by assumption
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
      simpa only [fitsEnv_doReserve_iff, doReserveEvents,
        LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveEvents,
        ↓reduceIte, ← hnew_toNat] using hfit0
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
    simp only [LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveEvents,
      ↓reduceIte, ← hnew_toNat]
    wp_done
  · have hcap0' : cap ≠ 0 := hcap0
    have hfit_ev : FitsEvents M lim st (rustReallocEvents cap.toNat new.toNat 1) := by
      simpa only [fitsEnv_doReserve_iff, doReserveEvents,
        LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveEvents,
        hcap0, ↓reduceIte, ← hnew_toNat] using hfit0
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
    simp only [LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveEvents,
      hcap0, ↓reduceIte, ← hnew_toNat]
    wp_done

/-- Relocatable `RawVecInner::reserve::do_reserve_and_handle` (Block `13`) satisfies
`withLsCodeLoaded lsmpl (doReserveSpecX M A lim)` under `AllocContractsPlaced M A lim H`. -/
theorem do_reserve_placed_ok_ext_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsPlaced M A lim H) :
    subroutine_ok ((blkPC_13).rebase (blkPl_13).base H)
      (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveSpecX M A lim)) :=
  LibsignalBinary.Proofs.TripleRatchet.Alloc.DoReserveBudget.do_reserve_placed_ok_of_raw_opt
    (fgStack := extHookStack + 48)
    (do_reserve_raw_placed_ok_ext_x hA)

theorem do_reserve_placed_ok_cl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hA : AllocContractsPlaced M A lim H) :
    subroutine_ok callerProg (lsmpl.base 13)
      (withLsCl lsmpl (doReserveSpecX M A lim)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg) (do_reserve_placed_ok_ext_x hA)

theorem do_reserve_placed_ok_of_stage2 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : Stage2ContractsPlaced A lim H) :
    subroutine_ok ((blkPC_13).rebase (blkPl_13).base H)
      (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveSpecX M A lim)) :=
  do_reserve_placed_ok_ext_x (allocContractsPlaced_of_stage2ContractsPlaced hC)

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DoReserveExtBudget

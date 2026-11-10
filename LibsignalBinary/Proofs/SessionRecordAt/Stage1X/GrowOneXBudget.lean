/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DefsBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.DefsBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneX
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.Core
import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.Fetch
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.HooksX
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `<alloc::raw_vec::RawVec<Chain>>::grow_one` (Blocks `45` and `43`)

Defines the budget-threaded `[LibsignalPlacement]` allocator bundle `AllocContractsPlaced M A lim H`
at `extHookStack = 16384` and verifies `<alloc::raw_vec::RawVecInner>::finish_grow [local#1]`
(Block `45`) and `<alloc::raw_vec::RawVec<Chain>>::grow_one` (Block `43`) with total correctness
under `FitsEnv M lim st (GrowOne104Env cap)`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget

open Arm64 ProofLib SepProp
open CryptoVerification (
  LibsignalPlacement LibsignalHooks LibsignalCodeLoaded IsLsBlockProg
  lsmpl withLsCodeLoaded withLsCl withMemEq extract_withLsCodeLoaded extract_withMemEq
  lsρ lsRustAllocSym lsRustDeallocSym lsRustReallocSym lsRustNoAllocShimSym
  lsProg_43 blkPC_43 blkPl_43 blkPC_45 blkPl_45 sepWP_seq_lscl
)
open CryptoVerification.RustHeap (LayoutOk)
open CryptoVerification.LibsignalSession (GrowGhost)
open CryptoVerification.LibsignalTripleRatchet (
  FinishGrowCall extHookStack ls_hook_ok_of_caller
  ls_subroutine_ok_cl_of_plain_prog ls_subroutine_ok_cl_of_callee
  SepWP.instantiate_post_exists
)
open Proofs.libsignal.Stage1X (lscall_of_withLsCl)
open Proofs.libsignal.Hooks2 (subroutine_ok_withLsCodeLoaded_map' subroutine_ok_withLsCl_map')
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget RustLayoutOk NullAllowed
  AllocCallPreserved FitsEvents FitsEnv VmPreserved
  rustAllocEvents rustReallocEvents
  not_nullAllowed_of_fitsAllocEvents not_nullAllowed_of_fitsReallocEvents
  rustCliAllocBudgetSpec rustCliDeallocBudgetSpec rustCliReallocBudgetSpec
  rustCliAllocNoOomSpec rustCliReallocNoOomSpec
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  rustCliAllocBudgetSpecWithStack rustCliDeallocBudgetExternSpecWithStack
  rustCliReallocBudgetExternSpecWithStack
  rustCliAllocNoOomSpecWithStack rustCliDeallocNoOomExternSpecWithStack
  rustCliReallocNoOomExternSpecWithStack
  subroutine_ok_rustCliAllocBudget_withStack
  subroutine_ok_rustCliDeallocBudget_externWithStack
  subroutine_ok_rustCliReallocBudget_externWithStack
)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionShimBudgetSpec sessionMemmoveBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  finishGrowEvents FinishGrowEnv fitsEnv_finishGrow_iff
  session2ShimBudgetSpecX
)
abbrev finishGrowSpecXB :=
  LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowSpecX

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Re-exported stack constants and symbol names -/

abbrev finishGrowStackX : Nat := Proofs.libsignal.Stage1X.finishGrowStackX
abbrev growOneChainStackX : Nat := Proofs.libsignal.Stage1X.growOneChainStackX
abbrev cmkStackX : Nat := Proofs.libsignal.Stage1X.cmkStackX
abbrev growOneChainName : String := Proofs.libsignal.Stage1X.growOneChainName

/-! ## Budget-threaded `[LibsignalPlacement]` allocator contract bundle -/

/-- Relocatable budget-threaded allocator + `shim` + `memmove` bundle at `extHookStack = 16384`. -/
structure AllocContractsPlaced [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop where
  alloc : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ lsRustAllocSym)
      (withLsCl lsmpl (rustCliAllocBudgetSpecWithStack M A lim false extHookStack))
  dealloc : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ lsRustDeallocSym)
      (withLsCl lsmpl (rustCliDeallocBudgetExternSpecWithStack M A lim extHookStack))
  realloc : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ lsRustReallocSym)
      (withLsCl lsmpl (rustCliReallocBudgetExternSpecWithStack M A lim extHookStack))
  shim : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ lsRustNoAllocShimSym)
      (withLsCl lsmpl session2ShimBudgetSpecX)
  session_memmove : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ "memmove")
      (withLsCl lsmpl (sessionMemmoveBudgetSpec extHookStack))

/-- Construct `AllocContractsPlaced M A lim H` from block-0 `withLsCodeLoaded` contracts. -/
theorem AllocContractsPlaced.of_block0 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {blk0Prog : Program} [IsLsBlockProg blk0Prog 0 H]
    (halloc : subroutine_ok blk0Prog (lsρ lsRustAllocSym)
      (withLsCodeLoaded lsmpl (rustCliAllocBudgetSpecWithStack M A lim false extHookStack)))
    (hdealloc : subroutine_ok blk0Prog (lsρ lsRustDeallocSym)
      (withLsCodeLoaded lsmpl (rustCliDeallocBudgetExternSpecWithStack M A lim extHookStack)))
    (hrealloc : subroutine_ok blk0Prog (lsρ lsRustReallocSym)
      (withLsCodeLoaded lsmpl (rustCliReallocBudgetExternSpecWithStack M A lim extHookStack)))
    (hshim : subroutine_ok blk0Prog (lsρ lsRustNoAllocShimSym)
      (withLsCodeLoaded lsmpl session2ShimBudgetSpecX))
    (hmemmove : subroutine_ok blk0Prog (lsρ "memmove")
      (withLsCodeLoaded lsmpl (sessionMemmoveBudgetSpec extHookStack))) :
    AllocContractsPlaced M A lim H :=
  ⟨ls_subroutine_ok_cl_of_callee (j := 0) halloc,
   ls_subroutine_ok_cl_of_callee (j := 0) hdealloc,
   ls_subroutine_ok_cl_of_callee (j := 0) hrealloc,
   ls_subroutine_ok_cl_of_callee (j := 0) hshim,
   ls_subroutine_ok_cl_of_callee (j := 0) hmemmove⟩

/-- Construct `AllocContractsPlaced M A lim H` from `HookSat H` single-step hooks. -/
theorem AllocContractsPlaced.of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (hmemmove : HookSat H "memmove" (sessionMemmoveBudgetSpec extHookStack)) :
    AllocContractsPlaced M A lim H where
  alloc := ls_subroutine_ok_cl_of_plain_prog
    (subroutine_ok_rustCliAllocBudget_withStack (by decide) (by decide) (ls_hook_ok_of_caller halloc))
  dealloc := ls_subroutine_ok_cl_of_plain_prog
    (subroutine_ok_rustCliDeallocBudget_externWithStack (by decide) (by decide) (ls_hook_ok_of_caller hdealloc))
  realloc := ls_subroutine_ok_cl_of_plain_prog
    (subroutine_ok_rustCliReallocBudget_externWithStack (by decide) (by decide) (ls_hook_ok_of_caller hrealloc))
  shim := by
    intro callerProg callerBlk hprog
    refine ls_subroutine_ok_cl_of_plain_prog ?_
    have h0 := LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget.subroutine_ok_withStack_of_subroutine_ok
      (ls_hook_ok_of_caller (prog := callerProg) (i := callerBlk) hshim) extHookStack
    refine subroutine_ok_mono h0 (fun _ _ _ hpre => ?_) (fun _ _ _ _ hpost => ?_)
    · dsimp only [LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget.withStack,
        CryptoVerification.LibsignalTripleRatchet.withStack, sessionShimBudgetSpec,
        CryptoVerification.LibsignalTripleRatchet.sessionShimSpec, session2ShimBudgetSpecX] at hpre ⊢
      simpa only [emp_sepConj, sepConj_assoc] using hpre
    · dsimp only [LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget.withStack,
        CryptoVerification.LibsignalTripleRatchet.withStack, sessionShimBudgetSpec,
        CryptoVerification.LibsignalTripleRatchet.sessionShimSpec, session2ShimBudgetSpecX] at hpost ⊢
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hpost.2.1, hpost.1⟩, hpost.2.2⟩
  session_memmove := ls_subroutine_ok_cl_of_plain_prog (ls_hook_ok_of_caller hmemmove)

/-- `NoOom` specialization of `AllocContractsPlaced.alloc` at memory `m` with `LibsignalCodeLoaded`. -/
theorem AllocContractsPlaced.allocNoOom_call [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsPlaced M A lim H)
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    {m : Memory} (hcl : LibsignalCodeLoaded lsmpl m) :
    subroutine_ok callerProg (lsρ lsRustAllocSym)
      (withMemEq m (rustCliAllocNoOomSpecWithStack M A lim false extHookStack)) := by
  have h0 := lscall_of_withLsCl (hA.alloc (callerProg := callerProg)) hcl
  exact subroutine_ok_outcome_intro fun ⟨size, align, st⟩ R s0 hpc hrun hpre hsp => by
    have ⟨hm, hpre0⟩ := extract_withMemEq hpre
    dsimp only [rustCliAllocNoOomSpecWithStack] at hpre0
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
    rcases hpre0 with ⟨⟨hx0, hx1, hlay, hfits, hlr⟩, hrest⟩
    have hpre_b : s0.mem ⊨
        (withMemEq m (rustCliAllocBudgetSpecWithStack M A lim false extHookStack)).pre
          (size, align, st) s0 ∗ R := by
      dsimp only [withMemEq, rustCliAllocBudgetSpecWithStack]
      refine Satisfies.mono (Entails.of_eq (by sep_ac_rfl))
        (P := ⌜s0.mem = m⌝ ∗
          (⌜(s0.readReg64 .x0).toNat = size ∧ (s0.readReg64 .x1).toNat = align ∧
            RustLayoutOk size align ∧ LsRetAddr624 (s0.readReg64 .lr)⌝ ∗
            ((A.pool lim st s0 ∗ stackAt s0.sp extHookStack) ∗ R))) ?_
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj]
      exact ⟨hm, ⟨hx0, hx1, hlay, hlr⟩, hrest⟩
    refine h0.mono_outcome (size, align, st) R s0 hpc hrun hpre_b hsp fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [withMemEq, rustCliAllocBudgetSpecWithStack,
        rustCliAllocNoOomSpecWithStack] at hpost ⊢
      by_cases hnull : sf.readReg64 .x0 = 0
      · simp only [hnull, ↓reduceIte] at hpost
        have hpost' : sf.mem ⊨ ⌜NullAllowed size align⌝ ∗
            (⌜AllocCallPreserved s0 sf⌝ ∗ A.pool lim st sf ∗ stackAt s0.sp extHookStack ∗ R) :=
          Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
        rw [satisfies_pure_sepConj] at hpost'
        exact False.elim (not_nullAllowed_of_fitsAllocEvents hlay hfits hpost'.1)
      · simp only [hnull, Bool.false_eq_true, ↓reduceIte] at hpost ⊢
        have hpost' : sf.mem ⊨ ⌜AllocCallPreserved s0 sf⌝ ∗
            (⌜(sf.readReg64 .x0).toNat % align = 0⌝ ∗
              (A.pool lim (M.stepEvents (rustAllocEvents size align) st) sf ∗
                stackAt s0.sp extHookStack ∗ A.live (sf.readReg64 .x0) size align ∗
                memRegion (sf.readReg64 .x0) size ∗ R)) :=
          Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
        rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost'
        refine Satisfies.mono (Entails.of_eq (by sep_ac_rfl))
          (P := ⌜AllocCallPreserved s0 sf ∧ sf.readReg64 .x0 ≠ 0#64 ∧
            (sf.readReg64 .x0).toNat % align = 0⌝ ∗
            (A.pool lim (M.stepEvents (rustAllocEvents size align) st) sf ∗
              stackAt s0.sp extHookStack ∗ A.live (sf.readReg64 .x0) size align ∗
              memRegion (sf.readReg64 .x0) size ∗ R)) ?_
        rw [satisfies_pure_sepConj]
        exact ⟨⟨hpost'.1, hnull, hpost'.2.1⟩, hpost'.2.2⟩
    · exact Or.inr (Or.inl ⟨hp, hpan⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
    · dsimp only [withMemEq, rustCliAllocBudgetSpecWithStack, rustCliAllocBudgetSpec] at hoom
      rw [satisfies_pure_sepConj] at hoom
      exact False.elim (hoom.1.1 hfits)

/-- `NoOom` specialization of `AllocContractsPlaced.realloc` at memory `m` with `LibsignalCodeLoaded`. -/
theorem AllocContractsPlaced.reallocNoOom_call [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsPlaced M A lim H)
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    {m : Memory} (hcl : LibsignalCodeLoaded lsmpl m) :
    subroutine_ok callerProg (lsρ lsRustReallocSym)
      (withMemEq m (rustCliReallocNoOomExternSpecWithStack M A lim extHookStack)) := by
  have h0 := lscall_of_withLsCl (hA.realloc (callerProg := callerProg)) hcl
  exact subroutine_ok_outcome_intro fun ⟨p, old_size, align, new_size, bs, st⟩ R s0 hpc hrun hpre hsp => by
    have ⟨hm, hpre0⟩ := extract_withMemEq hpre
    dsimp only [rustCliReallocNoOomExternSpecWithStack,
      LibsignalBinary.Heap.rustCliReallocNoOomExternSpecWithStack] at hpre0
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
    rcases hpre0 with ⟨⟨hx0, hx1, hx2, hx3, hlay_old, hlay_new, hbs1, hbs2, hfits, hlr⟩, hrest⟩
    have hpre_b : s0.mem ⊨
        (withMemEq m (rustCliReallocBudgetExternSpecWithStack M A lim extHookStack)).pre
          (p, old_size, align, new_size, bs, st) s0 ∗ R := by
      dsimp only [withMemEq, rustCliReallocBudgetExternSpecWithStack,
        LibsignalBinary.Heap.rustCliReallocBudgetExternSpecWithStack]
      refine Satisfies.mono (Entails.of_eq (by sep_ac_rfl))
        (P := ⌜s0.mem = m⌝ ∗
          (⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = old_size ∧
            (s0.readReg64 .x2).toNat = align ∧ (s0.readReg64 .x3).toNat = new_size ∧
            RustLayoutOk old_size align ∧ RustLayoutOk new_size align ∧
            bs.length ≤ old_size ∧ bs.length ≤ new_size ∧
            LsRetAddr624 (s0.readReg64 .lr)⌝ ∗
            ((A.pool lim st s0 ∗ A.live p old_size align ∗ (p ↦ₛ bs) ∗
              memRegion (p + BitVec.ofNat 64 bs.length) (old_size - bs.length) ∗
              stackAt s0.sp extHookStack) ∗ R))) ?_
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj]
      exact ⟨hm, ⟨hx0, hx1, hx2, hx3, hlay_old, hlay_new, hbs1, hbs2, hlr⟩, hrest⟩
    refine h0.mono_outcome (p, old_size, align, new_size, bs, st) R s0 hpc hrun hpre_b hsp fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [withMemEq, rustCliReallocBudgetExternSpecWithStack,
        LibsignalBinary.Heap.rustCliReallocBudgetExternSpecWithStack,
        rustCliReallocNoOomExternSpecWithStack,
        LibsignalBinary.Heap.rustCliReallocNoOomExternSpecWithStack] at hpost ⊢
      by_cases hnull : sf.readReg64 .x0 = 0
      · simp only [hnull, ↓reduceIte] at hpost
        have hpost' : sf.mem ⊨ ⌜sf.trace = s0.trace ∧ NullAllowed new_size align⌝ ∗
            (A.pool lim st sf ∗ stackAt s0.sp extHookStack ∗ A.live p old_size align ∗
              (p ↦ₛ bs) ∗ memRegion (p + BitVec.ofNat 64 bs.length) (old_size - bs.length) ∗ R) :=
          Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
        rw [satisfies_pure_sepConj] at hpost'
        exact False.elim (not_nullAllowed_of_fitsReallocEvents hlay_new hfits hpost'.1.2)
      · simp only [hnull, ↓reduceIte] at hpost
        have hpost' : sf.mem ⊨ ⌜(sf.readReg64 .x0).toNat % align = 0 ∧ sf.trace = s0.trace⌝ ∗
            (A.pool lim (M.stepEvents (rustReallocEvents old_size new_size align) st) sf ∗
              stackAt s0.sp extHookStack ∗ A.live (sf.readReg64 .x0) new_size align ∗
              (sf.readReg64 .x0 ↦ₛ bs) ∗
              memRegion (sf.readReg64 .x0 + BitVec.ofNat 64 bs.length) (new_size - bs.length) ∗ R) :=
          Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
        rw [satisfies_pure_sepConj] at hpost'
        refine Satisfies.mono (Entails.of_eq (by sep_ac_rfl))
          (P := ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 ≠ 0#64 ∧
            (sf.readReg64 .x0).toNat % align = 0⌝ ∗
            (A.pool lim (M.stepEvents (rustReallocEvents old_size new_size align) st) sf ∗
              stackAt s0.sp extHookStack ∗ A.live (sf.readReg64 .x0) new_size align ∗
              (sf.readReg64 .x0 ↦ₛ bs) ∗
              memRegion (sf.readReg64 .x0 + BitVec.ofNat 64 bs.length) (new_size - bs.length) ∗ R)) ?_
        rw [satisfies_pure_sepConj]
        exact ⟨⟨hpost'.1.2, hnull, hpost'.1.1⟩, hpost'.2⟩
    · exact Or.inr (Or.inl ⟨hp, hpan⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
    · dsimp only [withMemEq, rustCliReallocBudgetExternSpecWithStack,
        LibsignalBinary.Heap.rustCliReallocBudgetExternSpecWithStack, rustCliReallocBudgetSpec] at hoom
      rw [satisfies_pure_sepConj] at hoom
      exact False.elim (hoom.1.1 hfits)

/-! ## Arithmetic and memory helpers -/

private theorem umulh_stride_eq_zero {new stride : BitVec 64}
    (h : new.toNat * stride.toNat < 2 ^ 64) :
    BitVec.truncate 64 ((BitVec.zeroExtend 128 stride * BitVec.zeroExtend 128 new) >>> 64) = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_mul,
    BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  have h1 : stride.toNat < 2 ^ 128 := by omega
  have h2 : new.toNat < 2 ^ 128 := by omega
  have hcomm : stride.toNat * new.toNat = new.toNat * stride.toNat := Nat.mul_comm _ _
  have h3 : stride.toNat * new.toNat < 2 ^ 128 := by omega
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3, Nat.shiftRight_eq_div_pow]
  have hdiv : stride.toNat * new.toNat / 2 ^ 64 = 0 := Nat.div_eq_of_lt (by omega)
  rw [hdiv]
  rfl

private theorem mul_stride_toNat {new stride : BitVec 64}
    (h : new.toNat * stride.toNat < 2 ^ 64) :
    (stride * new).toNat = new.toNat * stride.toNat := by
  rw [BitVec.toNat_mul, Nat.mul_comm, Nat.mod_eq_of_lt h]

private theorem mul_stride_eq_ofNat {new stride : BitVec 64}
    (h : new.toNat * stride.toNat < 2 ^ 64) :
    stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [mul_stride_toNat h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

private theorem mul_stride_ne_zero {new stride : BitVec 64}
    (h0 : 0 < new.toNat * stride.toNat) (h : new.toNat * stride.toNat < 2 ^ 64) :
    stride * new ≠ 0#64 := by
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [mul_stride_toNat h] at ht
  change new.toNat * stride.toNat = 0 at ht
  omega

private theorem beq_mul_stride_zero_eq_false {new stride : BitVec 64}
    (h0 : 0 < new.toNat * stride.toNat) (h : new.toNat * stride.toNat < 2 ^ 64) :
    (stride * new == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  exact mul_stride_ne_zero h0 h

private theorem hi_stride_eq_false {new stride align : BitVec 64}
    (h : new.toNat * stride.toNat + align.toNat ≤ 2 ^ 63) :
    (9223372036854775808#64 - align).ult (stride * new) = false := by
  have hsub : (9223372036854775808#64 - align).toNat = 2 ^ 63 - align.toNat := by
    rw [BitVec.toNat_sub_of_le]
    · simp
    · rw [BitVec.le_def]
      change align.toNat ≤ 2 ^ 63
      omega
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, hsub, mul_stride_toNat (by omega)]
  omega

private theorem memRegion_24 (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v2) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v0)) := by
  rw [show (24 : Nat) = 8 + (8 + 8) by rfl, memRegion_split a 8 (8 + 8) (by decide),
    memRegion_split (a + 8#64) 8 8 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem stackAt_finishGrowX (sp : BitVec 64) :
    stackAt sp (extHookStack + 48) =
      stackAt (sp - 48#64) extHookStack ∗ cells (sp - 48#64) 6 :=
  stackAt_split_cells sp 16384 6 (by decide)

private abbrev FG48Ghost :=
  BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) ×
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64

private def growPad104X (sp : BitVec 64) : SepProp :=
  memRegion (sp - 16896#64) 400

private theorem stackAt_grow_one_104_x (sp : BitVec 64) :
    stackAt sp (464 + finishGrowStackX) =
      growPad104X sp ∗
      (stackAt (sp - 64#64) finishGrowStackX ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
         ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
          ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
          ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
          ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7))) := by
  have h1 := stackAt_split_bottom sp 16496 400 (by decide)
  have h2 := stackAt_split_cells sp 16432 8 (by decide)
  change stackAt sp (464 + finishGrowStackX) = growPad104X sp ∗ stackAt sp 16496 at h1
  change stackAt sp 16496 = stackAt (sp - 64#64) finishGrowStackX ∗ cells (sp - 64#64) 8 at h2
  have hc8 : cells (sp - 64#64) 8 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
        ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
        ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
    cells_unfold
  rw [h1, h2, hc8]

private theorem grow_104_new_cap_eq {cap : BitVec 64}
    (h : max (2 * cap.toNat) 4 * 104 ≤ 9223372036854775800) :
    (if (4#64).ult (cap <<< 1) = true then cap <<< 1 else 4#64) =
      BitVec.ofNat 64 (max (2 * cap.toNat) 4) := by
  have hsh : (cap <<< 1).toNat = 2 * cap.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    change (cap.toNat * 2) % 2 ^ 64 = 2 * cap.toNat
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  by_cases hc : (4#64).ult (cap <<< 1) = true
  · simp only [hc, ite_true, hsh]
    have hlt : 4 < 2 * cap.toNat := by
      rw [BitVec.ult_eq_decide, decide_eq_true_eq, hsh] at hc
      exact hc
    omega
  · simp only [hc, Bool.false_eq_true, ite_false]
    have hle : ¬ 4 < 2 * cap.toNat := by
      rw [BitVec.ult_eq_decide, decide_eq_true_eq, hsh] at hc
      exact hc
    change 4 = max (2 * cap.toNat) 4
    omega

/-! ## Block `45`: `<alloc::raw_vec::RawVecInner>::finish_grow [local#1]` -/

private def finishGrowZeroSpec2X (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (FinishGrowCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
      s.readReg64 .x3 = x.new ∧ s.readReg64 .x4 = x.align ∧ s.readReg64 .x5 = x.stride ∧
      x.cap = 0#64 ∧ x.bs = [] ∧ x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧
      0 < x.stride.toNat ∧ RustLayoutOk (x.new.toNat * x.stride.toNat) x.align.toNat ∧
      FitsEvents M lim st (rustAllocEvents (x.new.toNat * x.stride.toNat) x.align.toNat)⌝ ∗
    memRegion x.out 24 ∗ A.pool lim st s ∗ stackAt s.sp (extHookStack + 48)
  post := (finishGrowSpecXB M A lim).post

private def finishGrowNeSpec2X (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (FinishGrowCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
      s.readReg64 .x3 = x.new ∧ s.readReg64 .x4 = x.align ∧ s.readReg64 .x5 = x.stride ∧
      x.cap ≠ 0#64 ∧ x.bs.length ≤ x.cap.toNat * x.stride.toNat ∧
      x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ 0 < x.stride.toNat ∧
      RustLayoutOk (x.new.toNat * x.stride.toNat) x.align.toNat ∧
      FitsEvents M lim st
        (rustReallocEvents (x.cap.toNat * x.stride.toNat)
          (x.new.toNat * x.stride.toNat) x.align.toNat)⌝ ∗
    memRegion x.out 24 ∗
    A.live x.ptr (x.cap.toNat * x.stride.toNat) x.align.toNat ∗ (x.ptr ↦ₛ x.bs) ∗
    memRegion (x.ptr + BitVec.ofNat 64 x.bs.length)
      (x.cap.toNat * x.stride.toNat - x.bs.length) ∗
    A.pool lim st s ∗ stackAt s.sp (extHookStack + 48)
  post := (finishGrowSpecXB M A lim).post

set_option maxHeartbeats 800000 in
private theorem finish_grow_zero_placed_ok_ext_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsPlaced M A lim H) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base
      (withLsCodeLoaded lsmpl (finishGrowZeroSpec2X M A lim)) := by
  unfold withLsCodeLoaded finishGrowZeroSpec2X finishGrowSpecXB
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowSpecX
  dsimp only [LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowSpecWithStack]
  simp only [memRegion_24, stackAt_finishGrowX, sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  wp_init xst s0
  obtain ⟨⟨out, cap, ptr, new, align, stride, bs⟩, st⟩ := xst
  dsimp only at *
  rcases ‹RustLayoutOk (new.toNat * stride.toNat) align.toNat› with ⟨⟨hsz_pos, hpow, hbound⟩, hal31⟩
  subst cap; subst bs
  have hlt64 : new.toNat * stride.toNat < 2 ^ 64 := by omega
  have humulh := umulh_stride_eq_zero hlt64
  have hhi := hi_stride_eq_false hbound
  have hcbz := beq_mul_stride_zero_eq_false hsz_pos hlt64
  have hmul := mul_stride_toNat hlt64
  have hlay : RustLayoutOk (new.toNat * stride.toNat) align.toNat := ⟨⟨hsz_pos, hpow, hbound⟩, hal31⟩
  apply sepWP_seq_lscl (mid := lsρ lsRustNoAllocShimSym) ‹_›
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl1
  apply sepWP_seq_lscl (mid := lsρ lsRustAllocSym) hcl1
  have hshim_call := lscall_of_withLsCl
    (hA.shim (callerProg := (blkPC_45).rebase (blkPl_45).base H)) hcl1
  wp_call hshim_call ()
  have htr1 : sf.trace = s0.trace := by simpa only [wp_norm] using ‹sf.trace = _›
  refine ProofLib.SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl2
  have halloc_call := hA.allocNoOom_call (callerProg := (blkPC_45).rebase (blkPl_45).base H) hcl2
  wp_call halloc_call (new.toNat * stride.toNat, align.toNat, st)
  have htr2 : sf_1.trace = s0.trace := ‹AllocCallPreserved sf sf_1›.2.1.trans htr1
  have hoom_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false :=
    beq_eq_false_iff_ne.mpr ‹sf_1.readReg64 Reg.x0 ≠ 0#64›
  have hmul_bv := mul_stride_eq_ofNat hlt64
  wp_steps_sync_pool (s0.readReg64 .lr)
  apply SepWP.instantiate_post_exists (sf_1.readReg64 Reg.x0)
  rw [‹s0.readReg64 (Reg.gpr 1#5) = 0#64›]
  dsimp only [finishGrowEvents]
  simp only [pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj]
  wp_done

set_option maxHeartbeats 800000 in
private theorem finish_grow_ne_placed_ok_ext_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsPlaced M A lim H) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base
      (withLsCodeLoaded lsmpl (finishGrowNeSpec2X M A lim)) := by
  unfold withLsCodeLoaded finishGrowNeSpec2X finishGrowSpecXB
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowSpecX
  dsimp only [LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowSpecWithStack]
  simp only [memRegion_24, stackAt_finishGrowX, sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  wp_init xst s0
  obtain ⟨⟨out, cap, ptr, new, align, stride, bs⟩, st⟩ := xst
  dsimp only at *
  rcases ‹RustLayoutOk (new.toNat * stride.toNat) align.toNat› with ⟨⟨hsz_pos, hpow, hbound⟩, hal31⟩
  have hcap_ne : cap ≠ 0#64 := ‹_›
  have hstr_pos : 0 < stride.toNat := ‹_›
  have hcap_le_new : cap.toNat ≤ new.toNat := ‹_›
  have hbs_le_cap : bs.length ≤ cap.toNat * stride.toNat := ‹_›
  have hlt64 : new.toNat * stride.toNat < 2 ^ 64 := by omega
  have hcap_le : cap.toNat * stride.toNat ≤ new.toNat * stride.toNat :=
    Nat.mul_le_mul_right stride.toNat hcap_le_new
  have hcap_lt64 : cap.toNat * stride.toNat < 2 ^ 64 := by omega
  have hcap_pos : 0 < cap.toNat := Nat.pos_of_ne_zero (fun hc => hcap_ne (BitVec.eq_of_toNat_eq hc))
  have hold_pos : 0 < cap.toNat * stride.toNat := Nat.mul_pos hcap_pos hstr_pos
  have humulh := umulh_stride_eq_zero hlt64
  have hhi := hi_stride_eq_false hbound
  have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap_ne
  have hmul := mul_stride_toNat hlt64
  have hmul_cap := mul_stride_toNat hcap_lt64
  have hle_new : bs.length ≤ new.toNat * stride.toNat := by omega
  have hlay_old : RustLayoutOk (cap.toNat * stride.toNat) align.toNat := ⟨⟨hold_pos, hpow, by omega⟩, hal31⟩
  have hlay : RustLayoutOk (new.toNat * stride.toNat) align.toNat := ⟨⟨hsz_pos, hpow, hbound⟩, hal31⟩
  apply sepWP_seq_lscl (mid := lsρ lsRustReallocSym) ‹_›
  wp_steps_sync_pool (lsρ lsRustReallocSym)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl1
  have hrealloc_call := hA.reallocNoOom_call (callerProg := (blkPC_45).rebase (blkPl_45).base H) hcl1
  wp_call hrealloc_call (ptr, cap.toNat * stride.toNat, align.toNat, new.toNat * stride.toNat, bs, st)
  have hoom_beq : (sf.readReg64 Reg.x0 == 0#64) = false :=
    beq_eq_false_iff_ne.mpr ‹sf.readReg64 Reg.x0 ≠ 0#64›
  have hmul_bv := mul_stride_eq_ofNat hlt64
  wp_steps_sync_pool (s0.readReg64 .lr)
  apply SepWP.instantiate_post_exists (sf.readReg64 Reg.x0)
  have hcap_nat_ne : cap.toNat ≠ 0 := Nat.ne_of_gt hcap_pos
  simp only [finishGrowEvents, hcap_nat_ne, ite_false]
  wp_done

/-- Relocatable `<alloc::raw_vec::RawVecInner>::finish_grow [local#1]` (Block `45`) meets
`withLsCodeLoaded lsmpl (finishGrowSpecX M A lim)` under `AllocContractsPlaced M A lim H`. -/
theorem finish_grow_placed_ok_ext_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsPlaced M A lim H) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base
      (withLsCodeLoaded lsmpl (finishGrowSpecXB M A lim)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  have ⟨hcl0, hpre0⟩ := extract_withLsCodeLoaded hpre
  by_cases hcap0 : x.cap = 0#64
  · refine (finish_grow_zero_placed_ok_ext_x hA).mono_outcome (x, st) R s0 hpc hrun ?_ hsp
      fun _ hout => hout
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl0, ?_⟩
    simp only [finishGrowSpecXB,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowSpecX,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowSpecWithStack,
      finishGrowZeroSpec2X, FinishGrowCall.oldBuf, hcap0, ite_true, emp_sepConj,
      sepConj_assoc, satisfies_pure_sepConj] at hpre0 ⊢
    rcases hpre0 with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hbs0, _, hle, hnew, hstr, hlay, hfits⟩, hmem⟩
    have hfits0 : FitsEvents M lim st (rustAllocEvents (x.new.toNat * x.stride.toNat) x.align.toNat) := by
      have hf := (fitsEnv_finishGrow_iff x).mp hfits
      simp only [hcap0, BitVec.toNat_zero, finishGrowEvents, ite_true] at hf
      exact hf
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, trivial, hbs0 trivial, hle, hnew, hstr, hlay, hfits0⟩, hmem⟩
  · refine (finish_grow_ne_placed_ok_ext_x hA).mono_outcome (x, st) R s0 hpc hrun ?_ hsp
      fun _ hout => hout
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl0, ?_⟩
    simp only [finishGrowSpecXB,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowSpecX,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowSpecWithStack,
      finishGrowNeSpec2X, FinishGrowCall.oldBuf, RustCliAllocBudget.repAlloc_live_norm,
      hcap0, ite_false, sepConj_assoc, satisfies_pure_sepConj] at hpre0 ⊢
    rcases hpre0 with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, _, hbs, hle, hnew, hstr, hlay, hfits⟩, hmem⟩
    have hcap_nat_ne : x.cap.toNat ≠ 0 := fun hc => hcap0 (BitVec.eq_of_toNat_eq hc)
    have hfits1 : FitsEvents M lim st
        (rustReallocEvents (x.cap.toNat * x.stride.toNat)
          (x.new.toNat * x.stride.toNat) x.align.toNat) := by
      have hf := (fitsEnv_finishGrow_iff x).mp hfits
      simp only [finishGrowEvents, hcap_nat_ne, ite_false] at hf
      exact hf
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hcap0, hbs, hle, hnew, hstr, hlay, hfits1⟩, hmem⟩

/-! ## Block `43`: `<alloc::raw_vec::RawVec<Chain>>::grow_one` -/

/-- Deterministic `AllocEvent` list for `<RawVec<Chain>>::grow_one` at capacity `cap`
(`stride = 104`, `align = 8`, `new = max (2 * cap.toNat) 4`). -/
def growOne104Events (cap : BitVec 64) : List AllocEvent :=
  finishGrowEvents cap.toNat (max (2 * cap.toNat) 4) 8 104

/-- Allocation envelope for `<RawVec<Chain>>::grow_one` at capacity `cap`. -/
def GrowOne104Env (cap : BitVec 64) (evs : List AllocEvent) : Prop :=
  evs = growOne104Events cap

abbrev growOneChainEvents := growOne104Events
abbrev GrowOneChainEnv := GrowOne104Env

theorem fitsEnv_growOne104_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} {cap : BitVec 64} :
    FitsEnv M lim st (GrowOne104Env cap) ↔ FitsEvents M lim st (growOne104Events cap) :=
  ⟨fun h => h _ rfl, fun h _ he => he ▸ h⟩

/-- Budget-threaded `growOne104SpecX` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝` under
`FitsEnv M lim st (GrowOne104Env cap)`). -/
def growOne104SpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (GrowGhost × M.σ) where
  pre := fun ((v, cap, ptr, bs), st) s =>
    ⌜s.readReg64 .x0 = v ∧ bs.length = cap.toNat * 104 ∧ ptr ≠ 0 ∧
      max (2 * cap.toNat) 4 * 104 + 8 ≤ 2 ^ 63 ∧
      FitsEnv M lim st (GrowOne104Env cap)⌝ ∗
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
    (if cap = 0 then emp else A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) ∗
    A.pool lim st s ∗ stackAt s.sp (464 + finishGrowStackX)
  post := fun ((v, cap, _, bs), st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    ∃∗ p' : BitVec 64,
      ⌜p' ≠ 0⌝ ∗ (v ↦₆₄ BitVec.ofNat 64 (max (2 * cap.toNat) 4)) ∗ ((v + 8#64) ↦₆₄ p') ∗
      A.live p' (max (2 * cap.toNat) 4 * 104) 8 ∗ (p' ↦ₛ bs) ∗
      memRegion (p' + BitVec.ofNat 64 bs.length) ((max (2 * cap.toNat) 4 - cap.toNat) * 104) ∗
      A.pool lim (M.stepEvents (growOne104Events cap) st) sf ∗
      stackAt s0.sp (464 + finishGrowStackX)

abbrev growOneChainSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (GrowGhost × M.σ) :=
  growOne104SpecX M A lim

private def finishGrow104ZeroSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (FG48Ghost × M.σ) where
  pre := fun ((out, cap, ptr, new, bs, o0, o1, o2, fsp), st) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.readReg64 .x4 = 8#64 ∧ s.readReg64 .x5 = 104#64 ∧
      s.sp = fsp ∧ cap = 0#64 ∧ bs = [] ∧ cap.toNat ≤ new.toNat ∧ 0 < new.toNat ∧
      new.toNat * 104 + 8 ≤ 2 ^ 63 ∧
      FitsEnv M lim st (FinishGrowEnv ⟨out, 0#64, ptr, new, 8#64, 104#64, []⟩)⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.pool lim st s ∗ stackAt fsp finishGrowStackX
  post := fun ((out, _, _, new, _, _, _, _, fsp), st) s0 sf =>
    ∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
      (out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ p') ∗
      ((out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * 104)) ∗
      A.live p' (new.toNat * 104) 8 ∗ memRegion p' (new.toNat * 104) ∗
      A.pool lim (M.stepEvents (finishGrowEvents 0 new.toNat 8 104) st) sf ∗
      stackAt fsp finishGrowStackX

private def finishGrow104NeSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (FG48Ghost × M.σ) where
  pre := fun ((out, cap, ptr, new, bs, o0, o1, o2, fsp), st) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.readReg64 .x4 = 8#64 ∧ s.readReg64 .x5 = 104#64 ∧
      s.sp = fsp ∧ cap ≠ 0#64 ∧ bs.length = cap.toNat * 104 ∧
      cap.toNat ≤ new.toNat ∧ 0 < new.toNat ∧ new.toNat * 104 + 8 ≤ 2 ^ 63 ∧
      FitsEvents M lim st (finishGrowEvents cap.toNat new.toNat 8 104)⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs) ∗
    A.pool lim st s ∗ stackAt fsp finishGrowStackX
  post := fun ((out, cap, _, new, bs, _, _, _, fsp), st) s0 sf =>
    ∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
      (out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ p') ∗
      ((out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * 104)) ∗
      A.live p' (new.toNat * 104) 8 ∗ (p' ↦ₛ bs) ∗
      memRegion (p' + BitVec.ofNat 64 bs.length) (new.toNat * 104 - bs.length) ∗
      A.pool lim (M.stepEvents (finishGrowEvents cap.toNat new.toNat 8 104) st) sf ∗
      stackAt fsp finishGrowStackX

private theorem finish_grow_104_zero_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hfg : subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base
      (withLsCodeLoaded lsmpl (finishGrowSpecXB M A lim))) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base
      (withLsCodeLoaded lsmpl (finishGrow104ZeroSpecX M A lim)) := by
  refine subroutine_ok_withLsCodeLoaded_map' hfg
    (fun ⟨⟨out, cap, ptr, new, bs, o0, o1, o2, fsp⟩, st⟩ R s0 hpre => ?_)
  simp only [finishGrow104ZeroSpecX, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap0, hbs, hle, hpos, hbound, hfits_env⟩, hmem⟩
  subst hfsp; subst hcap0; subst hbs
  let hcall : FinishGrowCall := ⟨out, 0#64, ptr, new, 8#64, 104#64, []⟩
  have hlay : RustLayoutOk (new.toNat * (104#64 : BitVec 64).toNat) (8#64 : BitVec 64).toNat :=
    ⟨⟨by change 0 < new.toNat * 104; omega, ⟨3, rfl⟩, by change new.toNat * 104 + 8 ≤ 2 ^ 63; omega⟩,
      by decide⟩
  refine ⟨(hcall, st), R, ?_, fun sf hq => ?_⟩
  · simp only [finishGrowSpecXB,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowSpecX,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowSpecWithStack,
      hcall, FinishGrowCall.oldBuf, ite_true, memRegion_24, emp_sepConj,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, fun _ => trivial, Nat.zero_le _, hle, hpos,
      by decide, hlay, hfits_env⟩, ?_⟩
    dsimp only [finishGrowStackX, Proofs.libsignal.Stage1X.finishGrowStackX,
      Proofs.libsignal.Stage1X.extHookStack, extHookStack] at hmem ⊢
    simpa only [sepConj_assoc] using hmem
  · simp only [finishGrowSpecXB,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowSpecX,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowSpecWithStack,
      finishGrow104ZeroSpecX, hcall, pointsToBytes_nil, List.length_nil, BitVec.add_zero,
      Nat.sub_zero, emp_sepConj, sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨p', hq⟩
    refine ⟨p', ?_⟩
    dsimp only [finishGrowStackX, Proofs.libsignal.Stage1X.finishGrowStackX,
      Proofs.libsignal.Stage1X.extHookStack, extHookStack] at hq ⊢
    simp only [BitVec.toNat_ofNat] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    exact ⟨⟨hq.1.1, hq.1.2.2⟩, by simpa only [sepConj_assoc] using hq.2⟩

private theorem finish_grow_104_ne_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hfg : subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base
      (withLsCodeLoaded lsmpl (finishGrowSpecXB M A lim))) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base
      (withLsCodeLoaded lsmpl (finishGrow104NeSpecX M A lim)) := by
  refine subroutine_ok_withLsCodeLoaded_map' hfg
    (fun ⟨⟨out, cap, ptr, new, bs, o0, o1, o2, fsp⟩, st⟩ R s0 hpre => ?_)
  simp only [finishGrow104NeSpecX, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap, hbs, hle, hpos, hbound, hfits⟩, hmem⟩
  subst hfsp
  let hcall : FinishGrowCall := ⟨out, cap, ptr, new, 8#64, 104#64, bs⟩
  have hlay : RustLayoutOk (new.toNat * (104#64 : BitVec 64).toNat) (8#64 : BitVec 64).toNat :=
    ⟨⟨by change 0 < new.toNat * 104; omega, ⟨3, rfl⟩, by change new.toNat * 104 + 8 ≤ 2 ^ 63; omega⟩,
      by decide⟩
  have hm104 : (104#64 : BitVec 64).toNat = 104 := rfl
  have ha8 : (8#64 : BitVec 64).toNat = 8 := rfl
  have hfits_env : FitsEnv M lim st (FinishGrowEnv hcall) :=
    (fitsEnv_finishGrow_iff hcall).mpr hfits
  refine ⟨(hcall, st), R, ?_, fun sf hq => ?_⟩
  · simp only [finishGrowSpecXB,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowSpecX,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowSpecWithStack,
      hcall, FinishGrowCall.oldBuf, RustCliAllocBudget.repAlloc_live_norm,
      hcap, ite_false, memRegion_24,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    rw [hm104, ha8, ← hbs, Nat.sub_self, memRegion_zero, sepConj_emp,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, False.elim, Nat.le_refl _, hle, hpos,
      by decide, hlay, hfits_env⟩, ?_⟩
    dsimp only [finishGrowStackX, Proofs.libsignal.Stage1X.finishGrowStackX,
      Proofs.libsignal.Stage1X.extHookStack, extHookStack] at hmem ⊢
    simpa only [sepConj_assoc] using hmem
  · simp only [finishGrowSpecXB,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowSpecX,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowSpecWithStack,
      finishGrow104NeSpecX, hcall, sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨p', hq⟩
    refine ⟨p', ?_⟩
    dsimp only [finishGrowStackX, Proofs.libsignal.Stage1X.finishGrowStackX,
      Proofs.libsignal.Stage1X.extHookStack, extHookStack] at hq ⊢
    rw [hm104, ha8] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    exact ⟨⟨hq.1.1, hq.1.2.2⟩, by simpa only [sepConj_assoc] using hq.2⟩

/-- Relocatable `<alloc::raw_vec::RawVec<Chain>>::grow_one` contract on Block `43` at
`growOneChainStackX` (`16896` B). -/
def GrowOneChainPlacedOkX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_43).rebase (blkPl_43).base H) (blkPl_43).base
    (withLsCodeLoaded lsmpl (growOneChainSpecX M A lim))

set_option maxHeartbeats 800000 in
/-- Relocatable `<alloc::raw_vec::RawVec<Chain>>::grow_one` (Block `43`) meets
`withLsCodeLoaded lsmpl (growOne104SpecX M A lim)` under `AllocContractsPlaced M A lim H`. -/
theorem grow_one_104_placed_ok_ext_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsPlaced M A lim H) :
    subroutine_ok ((blkPC_43).rebase (blkPl_43).base H) (blkPl_43).base
      (withLsCodeLoaded lsmpl (growOne104SpecX M A lim)) := by
  simp only [withLsCodeLoaded, growOne104SpecX, stackAt_grow_one_104_x,
    sepExists_sepConj_left, sepExists_sepConj_right]
  wp_init xst s0
  obtain ⟨⟨v, cap, ptr, bs⟩, st⟩ := xst
  dsimp only at *
  have hfg := finish_grow_placed_ok_ext_x hA
  have hfg0_cl : subroutine_ok ((blkPC_43).rebase (blkPl_43).base H) (lsmpl.base 45)
      (withLsCl lsmpl (finishGrow104ZeroSpecX M A lim)) :=
    ls_subroutine_ok_cl_of_callee (j := 45) (finish_grow_104_zero_placed_ok_x hfg)
  have hfg1_cl : subroutine_ok ((blkPC_43).rebase (blkPl_43).base H) (lsmpl.base 45)
      (withLsCl lsmpl (finishGrow104NeSpecX M A lim)) :=
    ls_subroutine_ok_cl_of_callee (j := 45) (finish_grow_104_ne_placed_ok_x hfg)
  have hnew_eq : (if (4#64).ult (cap <<< 1) = true then cap <<< 1 else 4#64) =
      BitVec.ofNat 64 (max (2 * cap.toNat) 4) :=
    grow_104_new_cap_eq (by omega)
  let new := BitVec.ofNat 64 (max (2 * cap.toNat) 4)
  have hnew_toNat : new.toNat = max (2 * cap.toNat) 4 := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by omega
  have hnew_pos : 0 < new.toNat := by omega
  have hnew_bound : new.toNat * 104 + 8 ≤ 2 ^ 63 := by omega
  have hfits_ev : FitsEvents M lim st (finishGrowEvents cap.toNat new.toNat 8 104) := by
    rw [hnew_toNat]
    exact fitsEnv_growOne104_iff.mp ‹FitsEnv M lim st (GrowOne104Env cap)›
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have hbs := List.eq_nil_of_length_eq_zero ‹bs.length = (0#64 : BitVec 64).toNat * 104›
    subst hbs
    simp only [BitVec.ofNat_eq_ofNat, ite_true, emp_sepConj, pointsToBytes_nil, List.length_nil,
      BitVec.add_zero, BitVec.toNat_zero, Nat.mul_zero, Nat.sub_zero] at hfits_ev ⊢
    have hfits0_env :
        FitsEnv M lim st (FinishGrowEnv ⟨s0.sp - 56#64, 0#64, ptr, new, 8#64, 104#64, []⟩) :=
      (fitsEnv_finishGrow_iff ⟨s0.sp - 56#64, 0#64, ptr, new, 8#64, 104#64, []⟩).mpr hfits_ev
    apply sepWP_seq_lscl (mid := lsmpl.base 45) ‹_›
    wp_steps_sync_pool (lsmpl.base 45)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcl1
    have hfg0_call := lscall_of_withLsCl hfg0_cl hcl1
    wp_call hfg0_call
      ((s0.sp - 56#64, 0#64, ptr, new, [], v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64), st)
    wp_steps_sync_pool (s0.readReg64 .lr)
    simp only [growOne104Events, BitVec.toNat_zero, hnew_toNat]
    wp_done
  · have hcap0' : cap ≠ 0 := hcap0
    simp only [hcap0', ite_false, sepConj_assoc]
    have hsub_mul : (max (2 * cap.toNat) 4 - cap.toNat) * 104 = new.toNat * 104 - bs.length := by
      rw [Nat.sub_mul, hnew_toNat, ‹bs.length = cap.toNat * 104›]
    rw [hsub_mul]
    apply sepWP_seq_lscl (mid := lsmpl.base 45) ‹_›
    wp_steps_sync_pool (lsmpl.base 45)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcl1
    have hfg1_call := lscall_of_withLsCl hfg1_cl hcl1
    wp_call hfg1_call
      ((s0.sp - 56#64, cap, ptr, new, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64), st)
    wp_steps_sync_pool (s0.readReg64 .lr)
    simp only [growOne104Events, hnew_toNat]
    wp_done

/-- `<alloc::raw_vec::RawVec<Chain>>::grow_one` meets `GrowOneChainPlacedOkX A lim H` under
`AllocContractsPlaced M A lim H`. -/
theorem growOneChain_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsPlaced M A lim H) :
    GrowOneChainPlacedOkX A lim H :=
  grow_one_104_placed_ok_ext_x hA

theorem growOneChain_placed_ok_cl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (h : GrowOneChainPlacedOkX A lim H) :
    subroutine_ok callerProg (lsmpl.base 43) (withLsCl lsmpl (growOneChainSpecX M A lim)) :=
  ls_subroutine_ok_cl_of_callee (j := 43) h

end LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget

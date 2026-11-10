/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr

/-!
# Budget-Threaded `[LibsignalPlacement]` Infrastructure for CLI Store Proofs

Stack-frame lifting for total budget specs under `LibsignalCodeRoLoaded`, `.keepsFs` forgetting and
`Budget → NoOom` hook lifts, and cross-block `AllocContractsXCliPlaced` transfers.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoVerification (IsLsBlockProg LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalTripleRatchet
  (extHookStack memcpyName memmoveName memsetName withStack)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (LibsignalCodeRoLoaded extract_withLsCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.SignalSession
  (lsRustAllocSymCli lsRustDeallocSymCli lsRustNoAllocShimSymCli lsRustReallocSymCli)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon
  (ls_transfer_lscro stk_le_pow64_of_roLoaded)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel BudgetLimits NullAllowed RustCliAllocBudget RustLayoutOk
   not_nullAllowed_of_fitsAllocEvents not_nullAllowed_of_fitsReallocEvents
   rustAllocEvents rustCliAllocNoOomExternSpecWithStack rustCliReallocBudgetExternSpecWithStack
   rustCliReallocNoOomExternSpecWithStack rustReallocEvents)
open LibsignalBinary.Heap.IfaceBudgetLemmas
  (rustCliAllocBudgetSpecWithStack rustCliAllocNoOomSpecWithStack)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyBudgetSpec sessionMemcpyRegionBudgetSpec sessionMemmoveBudgetSpec
   sessionMemsetBudgetSpec sessionMemsetRegionBudgetSpec sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
  (rustAllocNoOomExternSpecWithStack rustAllocNoOomSpecWithStack rustAllocSpecWithStack
   rustDeallocExternSpecWithStack rustReallocExternSpecWithStack
   rustReallocNoOomExternSpecWithStack)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced AllocContractsXCliPlaced)

/-! ## 1. Stack Lifting for Total Budget Specs (`onPanic = ⌜False⌝`) -/

theorem lift_stk_lscro_budget {α : Type} {prog : Program} {entry : BitVec 64} {pl : MultiPlacement}
    {F : Nat → Spec α} {P : α → State → SepProp} {Q : α → State → State → SepProp}
    {stk0 stk : Nat}
    (hInner : subroutine_ok prog entry (F stk0))
    (hstk : stk0 ≤ stk)
    (hpre_eq : ∀ x s k, (F k).pre x s =
      ⌜LibsignalCodeRoLoaded pl s.mem⌝ ∗ P x s ∗ stackAt s.sp k)
    (hpost_eq : ∀ x s0 sf k, (F k).post x s0 sf = Q x s0 sf ∗ stackAt s0.sp k)
    (hpan_eq0 : (F stk0).onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (hexit_eq : (F stk0).onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (hoom_eq : (F stk0).onOom = fun _ _ _ => ⌜False⌝ := by rfl) :
    subroutine_ok prog entry (F stk) := by
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre halign _ => ?_
  have hpre0 := hpre
  rw [hpre_eq x s0 stk] at hpre0
  have hcrl : LibsignalCodeRoLoaded pl s0.mem := by
    have h1 : s0.mem ⊨ ⌜LibsignalCodeRoLoaded pl s0.mem⌝ ∗
        (P x s0 ∗ stackAt s0.sp stk ∗ R) := by
      convert hpre0 using 1; sep_ac_rfl
    rw [satisfies_pure_sepConj] at h1
    exact h1.1
  have hstk64 : stk ≤ 2 ^ 64 := by
    have hm_stk : s0.mem ⊨ stackAt s0.sp stk ∗
        (⌜LibsignalCodeRoLoaded pl s0.mem⌝ ∗ P x s0 ∗ R) := by
      convert hpre0 using 1; sep_ac_rfl
    exact stk_le_pow64_of_roLoaded hcrl.2 hm_stk
  have hsplit : stackAt s0.sp stk =
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - stk0) ∗ stackAt s0.sp stk0 := by
    have h1 := ProofLib.stackAt_split_bottom s0.sp stk0 (stk - stk0) (by omega)
    rwa [Nat.add_sub_of_le hstk] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - stk0) ∗ R
  have hpre' : s0.mem ⊨ (F stk0).pre x s0 ∗ R' := by
    rw [hpre_eq x s0 stk0]
    rw [hsplit] at hpre0
    dsimp only [R']
    convert hpre0 using 1; sep_ac_rfl
  refine hInner.mono_outcome x R' s0 hpc hrun hpre' halign fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    rw [hpost_eq x s0 sf stk0] at hpost
    rw [hpost_eq x s0 sf stk, hsplit]
    dsimp only [R'] at hpost
    convert hpost using 1; sep_ac_rfl
  · rw [hpan_eq0] at hpan
    exact (not_satisfies_false_sepConj hpan).elim
  · rw [hexit_eq] at hex
    exact (not_satisfies_false_sepConj hex).elim
  · rw [hoom_eq] at hoom
    exact (not_satisfies_false_sepConj hoom).elim

/-! ## 2. `.keepsFs` Forgetting & `Budget → NoOom` Lifts under `withLsCodeRoLoaded` -/

theorem subroutine_ok_withLsCodeRoLoaded_of_keepsFs {α : Type} {P : Program} {entry : BitVec 64}
    {pl : MultiPlacement} {spec : Spec α}
    (h : subroutine_ok P entry (withLsCodeRoLoaded pl spec.keepsFs)) :
    subroutine_ok P entry (withLsCodeRoLoaded pl spec) :=
  subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => by
    dsimp only [withLsCodeRoLoaded, Spec.keepsFs] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact hq.2)

theorem AllocContractsFsPlaced.toAllocContractsX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsFsPlaced A lim H) : AllocContractsXCliPlaced A lim H where
  alloc := subroutine_ok_withLsCodeRoLoaded_of_keepsFs hA.alloc
  dealloc := subroutine_ok_withLsCodeRoLoaded_of_keepsFs hA.dealloc
  realloc := subroutine_ok_withLsCodeRoLoaded_of_keepsFs hA.realloc
  shim stk h1 h2 := subroutine_ok_withLsCodeRoLoaded_of_keepsFs (hA.shim stk h1 h2)
  memcpy stk h1 h2 := subroutine_ok_withLsCodeRoLoaded_of_keepsFs (hA.memcpy stk h1 h2)
  session_memcpy stk h1 h2 := subroutine_ok_withLsCodeRoLoaded_of_keepsFs (hA.session_memcpy stk h1 h2)
  memcpy_region stk h1 h2 := subroutine_ok_withLsCodeRoLoaded_of_keepsFs (hA.memcpy_region stk h1 h2)
  session_memcpy_region stk h1 h2 :=
    subroutine_ok_withLsCodeRoLoaded_of_keepsFs (hA.session_memcpy_region stk h1 h2)
  memmove stk h1 h2 := subroutine_ok_withLsCodeRoLoaded_of_keepsFs (hA.memmove stk h1 h2)
  session_memmove stk h1 h2 :=
    subroutine_ok_withLsCodeRoLoaded_of_keepsFs (hA.session_memmove stk h1 h2)
  memset stk h1 h2 := subroutine_ok_withLsCodeRoLoaded_of_keepsFs (hA.memset stk h1 h2)
  session_memset stk h1 h2 := subroutine_ok_withLsCodeRoLoaded_of_keepsFs (hA.session_memset stk h1 h2)
  memset_region stk h1 h2 := subroutine_ok_withLsCodeRoLoaded_of_keepsFs (hA.memset_region stk h1 h2)
  session_memset_region stk h1 h2 :=
    subroutine_ok_withLsCodeRoLoaded_of_keepsFs (hA.session_memset_region stk h1 h2)

theorem allocNoOomWithStack_lscro_of_budget [LibsignalPlacement] {pl : MultiPlacement} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {zeroed : Bool} {stk : Nat}
    {P : Program} {addr : BitVec 64}
    (h : subroutine_ok P addr
      (withLsCodeRoLoaded pl (rustAllocSpecWithStack M A lim zeroed stk))) :
    subroutine_ok P addr
      (withLsCodeRoLoaded pl (rustAllocNoOomSpecWithStack M A lim zeroed stk)) := by
  refine subroutine_ok_outcome_intro fun ⟨size, align, st⟩ R s0 hpc hrun hpre hal => ?_
  obtain ⟨hinv, hpre_rest⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [rustAllocNoOomSpecWithStack, rustCliAllocNoOomSpecWithStack] at hpre_rest
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_rest
  rcases hpre_rest with ⟨⟨hx0, hx1, hlay, hfit, hlr⟩, hmem⟩
  have hpre' : s0.mem ⊨
      (withLsCodeRoLoaded pl (rustAllocSpecWithStack M A lim zeroed stk)).pre
        (size, align, st) s0 ∗ R := by
    dsimp only [withLsCodeRoLoaded, rustAllocSpecWithStack, rustCliAllocBudgetSpecWithStack]
    have h1 : s0.mem ⊨ ⌜(s0.readReg64 .x0).toNat = size ∧
        (s0.readReg64 .x1).toNat = align ∧ RustLayoutOk size align ∧
        LsRetAddr624 (s0.readReg64 .lr)⌝ ∗
        (⌜LibsignalCodeRoLoaded pl s0.mem⌝ ∗
          ((A.pool lim st s0 ∗ stackAt s0.sp stk) ∗ R)) := by
      rw [satisfies_pure_sepConj]
      refine ⟨⟨hx0, hx1, hlay, hlr⟩, ?_⟩
      rw [satisfies_pure_sepConj]
      exact ⟨hinv, hmem⟩
    convert h1 using 1; sep_ac_rfl
  refine h.mono_outcome (size, align, st) R s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, rustAllocSpecWithStack, rustCliAllocBudgetSpecWithStack,
      rustAllocNoOomSpecWithStack, rustCliAllocNoOomSpecWithStack] at hpost ⊢
    by_cases h0 : sf.readReg64 .x0 = 0
    · simp only [h0, ↓reduceIte] at hpost
      have hnull_abs : sf.mem ⊨ ⌜NullAllowed size align⌝ ∗
          (⌜AllocCallPreserved s0 sf⌝ ∗ A.pool lim st sf ∗ stackAt s0.sp stk ∗ R) := by
        convert hpost using 1; sep_ac_rfl
      rw [satisfies_pure_sepConj] at hnull_abs
      exact False.elim (not_nullAllowed_of_fitsAllocEvents hlay hfit hnull_abs.1)
    · simp only [h0, ↓reduceIte] at hpost
      have hpost' : sf.mem ⊨ ⌜AllocCallPreserved s0 sf⌝ ∗
          (⌜(sf.readReg64 .x0).toNat % align = 0⌝ ∗
            (A.pool lim (M.stepEvents (rustAllocEvents size align) st) sf ∗
              stackAt s0.sp stk ∗ A.live (sf.readReg64 .x0) size align ∗
              (if zeroed then (sf.readReg64 .x0 ↦ₛ List.replicate size 0#8)
               else memRegion (sf.readReg64 .x0) size) ∗ R)) := by
        convert hpost using 1; sep_ac_rfl
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost'
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hpost'.1, h0, hpost'.2.1⟩, ?_⟩
      simpa only [sepConj_assoc] using hpost'.2.2
  · dsimp only [withLsCodeRoLoaded, rustAllocSpecWithStack,
      rustCliAllocBudgetSpecWithStack] at hpan
    exact (not_satisfies_false_sepConj hpan).elim
  · dsimp only [withLsCodeRoLoaded, rustAllocSpecWithStack,
      rustCliAllocBudgetSpecWithStack] at hex
    exact (not_satisfies_false_sepConj hex).elim
  · dsimp only [withLsCodeRoLoaded, rustAllocSpecWithStack,
      rustCliAllocBudgetSpecWithStack] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim (hoom.1.1 hfit)

theorem allocNoOomExternWithStack_lscro_of_budget [LibsignalPlacement] {pl : MultiPlacement} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {zeroed : Bool} {stk : Nat}
    {P : Program} {addr : BitVec 64}
    (h : subroutine_ok P addr
      (withLsCodeRoLoaded pl (rustAllocSpecWithStack M A lim zeroed stk))) :
    subroutine_ok P addr
      (withLsCodeRoLoaded pl (rustAllocNoOomExternSpecWithStack M A lim zeroed stk)) := by
  have hno := allocNoOomWithStack_lscro_of_budget h
  refine subroutine_ok_mono hno (fun _ _ _ hpre => hpre) (fun ⟨size, align, st⟩ R s0 sf hpost => ?_)
  dsimp only [withLsCodeRoLoaded, rustAllocNoOomSpecWithStack, rustCliAllocNoOomSpecWithStack,
    rustAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomExternSpecWithStack,
    rustCliAllocNoOomExternSpecWithStack] at hpost ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨⟨hpost.1.1.2.1, hpost.1.2.1, hpost.1.2.2⟩, hpost.2⟩

theorem reallocNoOomExternWithStack_lscro_of_budget [LibsignalPlacement] {pl : MultiPlacement} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {P : Program} {addr : BitVec 64}
    (h : subroutine_ok P addr
      (withLsCodeRoLoaded pl (rustReallocExternSpecWithStack M A lim stk))) :
    subroutine_ok P addr
      (withLsCodeRoLoaded pl (rustReallocNoOomExternSpecWithStack M A lim stk)) := by
  refine subroutine_ok_outcome_intro fun ⟨p, old, align, new, bs, st⟩ R s0 hpc hrun hpre hal => ?_
  obtain ⟨hinv, hpre_rest⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [rustReallocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliReallocNoOomExternSpecWithStack,
    rustCliReallocNoOomExternSpecWithStack] at hpre_rest
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_rest
  rcases hpre_rest with ⟨⟨hx0, hx1, hx2, hx3, hold, hnew, hblo, hbln, hfit, hlr⟩, hmem⟩
  have hpre' : s0.mem ⊨
      (withLsCodeRoLoaded pl (rustReallocExternSpecWithStack M A lim stk)).pre
        (p, old, align, new, bs, st) s0 ∗ R := by
    dsimp only [withLsCodeRoLoaded, rustReallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliReallocBudgetExternSpecWithStack,
      rustCliReallocBudgetExternSpecWithStack]
    have h1 : s0.mem ⊨ ⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = old ∧
        (s0.readReg64 .x2).toNat = align ∧ (s0.readReg64 .x3).toNat = new ∧
        RustLayoutOk old align ∧ RustLayoutOk new align ∧ bs.length ≤ old ∧ bs.length ≤ new ∧
        LsRetAddr624 (s0.readReg64 .lr)⌝ ∗
        (⌜LibsignalCodeRoLoaded pl s0.mem⌝ ∗
          ((A.pool lim st s0 ∗ A.live p old align ∗ (p ↦ₛ bs) ∗
            memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗ stackAt s0.sp stk) ∗ R)) := by
      rw [satisfies_pure_sepConj]
      refine ⟨⟨hx0, hx1, hx2, hx3, hold, hnew, hblo, hbln, hlr⟩, ?_⟩
      rw [satisfies_pure_sepConj]
      exact ⟨hinv, hmem⟩
    convert h1 using 1; sep_ac_rfl
  refine h.mono_outcome (p, old, align, new, bs, st) R s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, rustReallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliReallocBudgetExternSpecWithStack,
      rustCliReallocBudgetExternSpecWithStack,
      rustReallocNoOomExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliReallocNoOomExternSpecWithStack,
      rustCliReallocNoOomExternSpecWithStack] at hpost ⊢
    by_cases h0 : sf.readReg64 .x0 = 0
    · simp only [h0, ↓reduceIte] at hpost
      have hnull_abs : sf.mem ⊨ ⌜sf.trace = s0.trace ∧ NullAllowed new align⌝ ∗
          (A.pool lim st sf ∗ stackAt s0.sp stk ∗ A.live p old align ∗ (p ↦ₛ bs) ∗
            memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗ R) := by
        convert hpost using 1; sep_ac_rfl
      rw [satisfies_pure_sepConj] at hnull_abs
      exact False.elim (not_nullAllowed_of_fitsReallocEvents hnew hfit hnull_abs.1.2)
    · simp only [h0, ↓reduceIte] at hpost
      have hpost' : sf.mem ⊨ ⌜(sf.readReg64 .x0).toNat % align = 0 ∧ sf.trace = s0.trace⌝ ∗
          (A.pool lim (M.stepEvents (rustReallocEvents old new align) st) sf ∗
            stackAt s0.sp stk ∗ A.live (sf.readReg64 .x0) new align ∗
            (sf.readReg64 .x0 ↦ₛ bs) ∗
            memRegion (sf.readReg64 .x0 + BitVec.ofNat 64 bs.length) (new - bs.length) ∗ R) := by
        convert hpost using 1; sep_ac_rfl
      rw [satisfies_pure_sepConj] at hpost'
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hpost'.1.2, h0, hpost'.1.1⟩, ?_⟩
      simpa only [sepConj_assoc] using hpost'.2
  · dsimp only [withLsCodeRoLoaded, rustReallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliReallocBudgetExternSpecWithStack,
      rustCliReallocBudgetExternSpecWithStack] at hpan
    exact (not_satisfies_false_sepConj hpan).elim
  · dsimp only [withLsCodeRoLoaded, rustReallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliReallocBudgetExternSpecWithStack,
      rustCliReallocBudgetExternSpecWithStack] at hex
    exact (not_satisfies_false_sepConj hex).elim
  · dsimp only [withLsCodeRoLoaded, rustReallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliReallocBudgetExternSpecWithStack,
      rustCliReallocBudgetExternSpecWithStack] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim (hoom.1.1 hfit)

/-! ## 3. Cross-Block Transfer for `AllocContractsXCliPlaced` -/

theorem alloc_lscro_of_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i H]
    (hC : AllocContractsXCliPlaced A lim H) (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsρ lsRustAllocSymCli)
      (withLsCodeRoLoaded lsmpl (rustAllocSpecWithStack M A lim false extHookStack)) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 617) hC.alloc hi

theorem allocNoOom_lscro_of_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i H]
    (hC : AllocContractsXCliPlaced A lim H) (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsρ lsRustAllocSymCli)
      (withLsCodeRoLoaded lsmpl (rustAllocNoOomSpecWithStack M A lim false extHookStack)) :=
  allocNoOomWithStack_lscro_of_budget (alloc_lscro_of_cli hC hi)

theorem allocNoOomExtern_lscro_of_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i H]
    (hC : AllocContractsXCliPlaced A lim H) (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsρ lsRustAllocSymCli)
      (withLsCodeRoLoaded lsmpl (rustAllocNoOomExternSpecWithStack M A lim false extHookStack)) :=
  allocNoOomExternWithStack_lscro_of_budget (alloc_lscro_of_cli hC hi)

theorem dealloc_lscro_of_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i H]
    (hC : AllocContractsXCliPlaced A lim H) (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsρ lsRustDeallocSymCli)
      (withLsCodeRoLoaded lsmpl (rustDeallocExternSpecWithStack M A lim extHookStack)) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 617) hC.dealloc hi

theorem realloc_lscro_of_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i H]
    (hC : AllocContractsXCliPlaced A lim H) (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsρ lsRustReallocSymCli)
      (withLsCodeRoLoaded lsmpl (rustReallocExternSpecWithStack M A lim extHookStack)) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 617) hC.realloc hi

theorem reallocNoOom_lscro_of_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i H]
    (hC : AllocContractsXCliPlaced A lim H) (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsρ lsRustReallocSymCli)
      (withLsCodeRoLoaded lsmpl (rustReallocNoOomExternSpecWithStack M A lim extHookStack)) :=
  reallocNoOomExternWithStack_lscro_of_budget (realloc_lscro_of_cli hC hi)

theorem shim_lscro_of_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i H]
    (hC : AllocContractsXCliPlaced A lim H)
    {stk : Nat} (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsρ lsRustNoAllocShimSymCli)
      (withLsCodeRoLoaded lsmpl (withStack sessionShimBudgetSpec stk)) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 617) (hC.shim stk h1 h2) hi

theorem memcpy_lscro_of_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i H]
    (hC : AllocContractsXCliPlaced A lim H)
    {stk : Nat} (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsρ memcpyName)
      (withLsCodeRoLoaded lsmpl (withVmPreserved (libcMemcpySpec stk))) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 617) (hC.memcpy stk h1 h2) hi

theorem session_memcpy_lscro_of_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i H]
    (hC : AllocContractsXCliPlaced A lim H)
    {stk : Nat} (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsρ memcpyName)
      (withLsCodeRoLoaded lsmpl (sessionMemcpyBudgetSpec stk)) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 617) (hC.session_memcpy stk h1 h2) hi

theorem memcpy_region_lscro_of_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i H]
    (hC : AllocContractsXCliPlaced A lim H)
    {stk : Nat} (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsρ memcpyName)
      (withLsCodeRoLoaded lsmpl (withStack (withVmPreserved memcpyRegionSpec) stk)) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 617) (hC.memcpy_region stk h1 h2) hi

theorem session_memcpy_region_lscro_of_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i H]
    (hC : AllocContractsXCliPlaced A lim H)
    {stk : Nat} (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsρ memcpyName)
      (withLsCodeRoLoaded lsmpl (withStack sessionMemcpyRegionBudgetSpec stk)) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 617) (hC.session_memcpy_region stk h1 h2) hi

theorem memmove_lscro_of_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i H]
    (hC : AllocContractsXCliPlaced A lim H)
    {stk : Nat} (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsρ memmoveName)
      (withLsCodeRoLoaded lsmpl (withVmPreserved (libcMemmoveSpec stk))) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 617) (hC.memmove stk h1 h2) hi

theorem session_memmove_lscro_of_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i H]
    (hC : AllocContractsXCliPlaced A lim H)
    {stk : Nat} (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsρ memmoveName)
      (withLsCodeRoLoaded lsmpl (sessionMemmoveBudgetSpec stk)) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 617) (hC.session_memmove stk h1 h2) hi

theorem memset_lscro_of_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i H]
    (hC : AllocContractsXCliPlaced A lim H)
    {stk : Nat} (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsρ memsetName)
      (withLsCodeRoLoaded lsmpl (withVmPreserved (libcMemsetSpec stk))) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 617) (hC.memset stk h1 h2) hi

theorem session_memset_lscro_of_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i H]
    (hC : AllocContractsXCliPlaced A lim H)
    {stk : Nat} (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsρ memsetName)
      (withLsCodeRoLoaded lsmpl (sessionMemsetBudgetSpec stk)) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 617) (hC.session_memset stk h1 h2) hi

theorem memset_region_lscro_of_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i H]
    (hC : AllocContractsXCliPlaced A lim H)
    {stk : Nat} (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsρ memsetName)
      (withLsCodeRoLoaded lsmpl (withStack (withVmPreserved memsetRegionSpec) stk)) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 617) (hC.memset_region stk h1 h2) hi

theorem session_memset_region_lscro_of_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i H]
    (hC : AllocContractsXCliPlaced A lim H)
    {stk : Nat} (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsρ memsetName)
      (withLsCodeRoLoaded lsmpl (withStack sessionMemsetRegionBudgetSpec stk)) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 617) (hC.session_memset_region stk h1 h2) hi

end LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget

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
public import LibsignalBinary.Proofs.SignalSession.Cli.CliSessionCodeSymA
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.CalleesBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsSitesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.FinishGrowFsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Reserve11Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-!
# Budget-Threaded Relocatable `do_reserve_and_handle [local#9]` (Block `561`)

Budget-threaded `[LibsignalPlacement]` contracts for `do_reserve_and_handle [local#9]` on Block `561`
under `RustCliAllocBudget M`, proving `doReserveStrideRawSpecX`, `reserve1`, `cliDoReserve`, and
`reserve16` variants and lifting them to caller blocks via `StoreKit.withLsRoCl`.
-/

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Reserve11PlacedBudget

open Arm64 Arm64.Obj ProofLib SepProp
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.RustHeap (LayoutOk RustAlloc vecHeader vecU8At)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (LibsignalCodeRoLoaded extract_withLsCodeRoLoaded ls_subroutine_ok_rocl_of_block
   sepWP_seq_lscro withLsCodeRoLoaded withLsRoCl)
open CryptoVerification.LibsignalTripleRatchet
  (doReserveStackX extHookStack finishGrowStackX reserveCap)
open CryptoVerification.SignalSession
  (cliExternsPlaced cliPanicSymbolsPlaced isCliPanicSymbolPlaced
   lsRustAllocSymCli lsRustNoAllocShimSymCli lsRustReallocSymCli)
open CryptoVerification.SignalSession.Cli.Placed
  (blkPC_561 blkPl_561 lsProg_561 lsProg_587)
open CryptoVerification.SignalSession.Cli.Main.Placed (lsProg_617)
open CryptoVerification.SignalSession.Cli.GrowOne.Helpers
  (memRegion_bound_of_pointsTo64 stackAt_cliGrowOne stackAt_split_stk)
open CryptoVerification.SignalSession.Cli.MainHops
  (Reserve16Call SpecRefines handleErrorSymCli vec16At)
open CryptoVerification.SignalSession.Cli.MainHops.Reserve11Norm
  (readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre
   readReg64_setPC_pre readReg_setMem_setPC_pre readReg_setPC_pre
   repack_raw_post repack_raw_pre repack_stack_bound
   sp_setMem_setPC_pre sp_setPC_pre)
open CryptoVerification.SpqrV1.Alloc
  (DoReserveStrideCall reserveCapStride reserveCapStride_one reserveMinCap)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents NullAllowed
   RustCliAllocBudget RustLayoutOk
   not_nullAllowed_of_fitsAllocEvents not_nullAllowed_of_fitsReallocEvents
   rustAllocEvents rustReallocEvents)
open LibsignalBinary.Heap.IfaceBudgetLemmas
  (rustCliAllocBudgetExternSpecWithStack rustCliAllocBudgetSpecWithStack
   rustCliAllocNoOomExternSpecWithStack rustCliAllocNoOomSpecWithStack
   rustCliReallocBudgetExternSpecWithStack rustCliReallocNoOomExternSpecWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (DoReserveEnv doReserveEvents fitsEnv_doReserve_iff)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContractsBudget (shimSpecWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
  (rustAllocSpecWithStack rustReallocExternSpecWithStack)
open LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget
  (DoReserveStrideEnv doReserveStrideEvents doReserveStrideRawSpecX fitsEnv_doReserveStride_iff)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget (doReserveSpecOf)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.GrowOne.LayoutBudget
  (FinishGrowNeEnv FinishGrowZeroEnv finishGrowNeCellsSpec finishGrowZeroCellsSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced AllocContractsXCliPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.CalleesBudget
  (Reserve16Env reserve16Events reserve16Spec)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsSitesPlacedBudget
  (AllocContractsFsPlaced.shim2_rocl AllocContractsXCliPlaced.shim2_rocl)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.FinishGrowFsPlacedBudget
  (finishGrowNeCellsRustSpec finishGrowZeroCellsRustSpec
   finish_grow_ne_cells_fs_placed_ok_of_hooks_at finish_grow_ne_cells_placed_ok_of_hooks_at
   finish_grow_zero_cells_fs_placed_ok_of_hooks_at finish_grow_zero_cells_placed_ok_of_hooks_at)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
attribute [local wp_norm]
  State.fs_writeReg64 State.fs_writeReg32 State.fs_writeVReg128
  State.fs_advancePC State.fs_setPC State.fs_setPState
  State.fs_setMem State.fs_setStatus State.fs_appendTrace

/-! ## 1. Arithmetic, Post-Condition, and `NoOom` Cross-Block Helpers -/

private theorem drop_rocl_post {α : Type} {P : Program} {e : BitVec 64}
    {pl : MultiPlacement} {spec : Spec α}
    (h : subroutine_ok P e (withLsRoCl pl spec)) :
    subroutine_ok P e (withLsCodeRoLoaded pl spec) :=
  subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => by
    dsimp only [withLsRoCl, withLsCodeRoLoaded] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact hq.2)

private theorem adds_cs_eq_false_p {x2 x1 : BitVec 64}
    (h : x2.toNat + x1.toNat < 2 ^ 64) :
    (x2 + x1).ult x2 = false := by
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, BitVec.toNat_add, Nat.mod_eq_of_lt h]
  omega

private theorem reserve_new_cap_stride_eq_p {stride cap x1 x2 : BitVec 64} {len additional : Nat}
    (hx1 : x1.toNat = len) (hx2 : x2.toNat = additional)
    (h : reserveCapStride stride.toNat cap.toNat len additional < 2 ^ 63) :
    (if (if (stride == 1#64) = true then 8#64 else 4#64).ult
          (if (cap <<< 1).ult (x2 + x1) = true then x2 + x1 else cap <<< 1) = true then
      if (cap <<< 1).ult (x2 + x1) = true then x2 + x1 else cap <<< 1
     else if (stride == 1#64) = true then 8#64 else 4#64) =
      BitVec.ofNat 64 (reserveCapStride stride.toNat cap.toNat len additional) := by
  have hmin_ge : 4 ≤ reserveMinCap stride.toNat := by
    unfold reserveMinCap; split <;> omega
  have hmax : max (max (len + additional) (2 * cap.toNat))
      (reserveMinCap stride.toNat) < 2 ^ 63 := h
  have hadd : (x2 + x1).toNat = len + additional := by
    rw [BitVec.toNat_add, hx2, hx1, Nat.mod_eq_of_lt (by omega)]
    omega
  have hsh : (cap <<< 1).toNat = 2 * cap.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    change (cap.toNat * 2) % 2 ^ 64 = 2 * cap.toNat
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hm0 : (if (stride == 1#64) = true then 8#64 else 4#64).toNat =
      reserveMinCap stride.toNat := by
    by_cases hs : (stride == 1#64) = true
    · have hs' : stride = 1#64 := beq_iff_eq.mp hs
      subst hs'
      rfl
    · have hs' : stride.toNat ≠ 1 := by
        intro h1
        apply hs
        exact beq_iff_eq.mpr (BitVec.eq_of_toNat_eq h1)
      simp only [hs, Bool.false_eq_true, ite_false, reserveMinCap, hs']
      rfl
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
  dsimp only [reserveCapStride]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  generalize (if (stride == 1#64) = true then 8#64 else 4#64) = m0 at hm0 ⊢
  generalize (if (cap <<< 1).ult (x2 + x1) = true then x2 + x1 else cap <<< 1) = m1 at hm1 ⊢
  by_cases hc2 : m0.ult m1 = true
  · simp only [hc2, ite_true, hm1]
    rw [BitVec.ult_eq_decide, decide_eq_true_eq, hm0, hm1] at hc2
    omega
  · simp only [hc2, Bool.false_eq_true, ite_false, hm0]
    rw [BitVec.ult_eq_decide, decide_eq_true_eq, hm0, hm1] at hc2
    omega

/-- `SpecRefines` lift from `rustAllocSpecWithStack` to `rustCliAllocNoOomExternSpecWithStack`
(supports both `apply_withLsCodeRoLoaded` and `apply_keepsFs_withLsCodeRoLoaded`). -/
theorem rustAllocSpecWithStack_refines_noOomExtern [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (zeroed : Bool) (stk : Nat) :
    SpecRefines
      (rustAllocSpecWithStack M A lim zeroed stk)
      (rustCliAllocNoOomExternSpecWithStack M A lim zeroed stk) := by
  intro ⟨size, align, st⟩ R s0 hpre
  dsimp only [rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack,
    rustCliAllocNoOomSpecWithStack] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hlay, hfit, hlr⟩, hmem⟩
  have hpre1 : s0.mem ⊨
      (rustAllocSpecWithStack M A lim zeroed stk).pre (size, align, st) s0 ∗ R := by
    dsimp only [rustAllocSpecWithStack, rustCliAllocBudgetSpecWithStack]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hlay, hlr⟩, hmem⟩
  refine ⟨(size, align, st), R, hpre1, ?_, ?_, ?_, ?_⟩
  · intro sf hpost
    dsimp only [rustAllocSpecWithStack, rustCliAllocBudgetSpecWithStack,
      rustCliAllocNoOomExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomExternSpecWithStack,
      LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack] at hpost ⊢
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
      refine ⟨⟨hpost'.1.2.1, h0, hpost'.2.1⟩, ?_⟩
      simpa only [sepConj_assoc] using hpost'.2.2
  · intro _ hpan
    dsimp only [rustAllocSpecWithStack, rustCliAllocBudgetSpecWithStack] at hpan
    exact (not_satisfies_false_sepConj hpan).elim
  · intro _ _ hex
    dsimp only [rustAllocSpecWithStack, rustCliAllocBudgetSpecWithStack] at hex
    exact (not_satisfies_false_sepConj hex).elim
  · intro _ hoom
    dsimp only [rustAllocSpecWithStack, rustCliAllocBudgetSpecWithStack] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim (hoom.1.1 hfit)

/-- `SpecRefines` lift from `rustReallocExternSpecWithStack` to
`rustCliReallocNoOomExternSpecWithStack`. -/
theorem rustReallocExternSpecWithStack_refines_noOomExtern [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat) :
    SpecRefines
      (rustReallocExternSpecWithStack M A lim stk)
      (rustCliReallocNoOomExternSpecWithStack M A lim stk) := by
  intro ⟨p, old, align, new, bs, st⟩ R s0 hpre
  dsimp only [rustCliReallocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliReallocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.rustCliReallocNoOomExternSpecWithStack] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hold, hnew, hblo, hbln, hfit, hlr⟩, hmem⟩
  have hpre1 : s0.mem ⊨
      (rustReallocExternSpecWithStack M A lim stk).pre (p, old, align, new, bs, st) s0 ∗ R := by
    dsimp only [rustReallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliReallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliReallocBudgetExternSpecWithStack]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hold, hnew, hblo, hbln, hlr⟩, hmem⟩
  refine ⟨(p, old, align, new, bs, st), R, hpre1, ?_, ?_, ?_, ?_⟩
  · intro sf hpost
    dsimp only [rustReallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliReallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliReallocBudgetExternSpecWithStack,
      rustCliReallocNoOomExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliReallocNoOomExternSpecWithStack,
      LibsignalBinary.Heap.rustCliReallocNoOomExternSpecWithStack] at hpost ⊢
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
  · intro _ hpan
    dsimp only [rustReallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliReallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliReallocBudgetExternSpecWithStack] at hpan
    exact (not_satisfies_false_sepConj hpan).elim
  · intro _ _ hex
    dsimp only [rustReallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliReallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliReallocBudgetExternSpecWithStack] at hex
    exact (not_satisfies_false_sepConj hex).elim
  · intro _ hoom
    dsimp only [rustReallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliReallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliReallocBudgetExternSpecWithStack] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim (hoom.1.1 hfit)

theorem allocNoOomExtern_rocl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {prog : Program} {i : Nat} [IsLsBlockProg prog i H]
    (hA : AllocContractsXCliPlaced A lim H) (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ lsRustAllocSymCli)
      (withLsRoCl lsmpl (rustCliAllocNoOomExternSpecWithStack M A lim false extHookStack)) :=
  ls_subroutine_ok_rocl_of_block (i := i) (j := 617)
    ((rustAllocSpecWithStack_refines_noOomExtern A lim false extHookStack).apply_withLsCodeRoLoaded
      hA.alloc)
    hi

theorem allocNoOomExtern_fs_rocl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {prog : Program} {i : Nat} [IsLsBlockProg prog i H]
    (hFs : AllocContractsFsPlaced A lim H) (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ lsRustAllocSymCli)
      (withLsRoCl lsmpl
        (rustCliAllocNoOomExternSpecWithStack M A lim false extHookStack).keepsFs) :=
  ls_subroutine_ok_rocl_of_block (i := i) (j := 617)
    ((rustAllocSpecWithStack_refines_noOomExtern A lim false
        extHookStack).apply_keepsFs_withLsCodeRoLoaded hFs.alloc)
    hi

theorem reallocNoOomExtern_rocl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {prog : Program} {i : Nat} [IsLsBlockProg prog i H]
    (hA : AllocContractsXCliPlaced A lim H) (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ lsRustReallocSymCli)
      (withLsRoCl lsmpl (rustCliReallocNoOomExternSpecWithStack M A lim extHookStack)) :=
  ls_subroutine_ok_rocl_of_block (i := i) (j := 617)
    ((rustReallocExternSpecWithStack_refines_noOomExtern A lim
        extHookStack).apply_withLsCodeRoLoaded hA.realloc)
    hi

theorem reallocNoOomExtern_fs_rocl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {prog : Program} {i : Nat} [IsLsBlockProg prog i H]
    (hFs : AllocContractsFsPlaced A lim H) (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ lsRustReallocSymCli)
      (withLsRoCl lsmpl
        (rustCliReallocNoOomExternSpecWithStack M A lim extHookStack).keepsFs) :=
  ls_subroutine_ok_rocl_of_block (i := i) (j := 617)
    ((rustReallocExternSpecWithStack_refines_noOomExtern A lim
        extHookStack).apply_keepsFs_withLsCodeRoLoaded hFs.realloc)
    hi

/-! ## 2. Block `561` General `(stride, align)` Raw Contracts (`reserve11_raw_blk561_ok`, `reserve11_raw_fs_blk561_ok`) -/

theorem reserve11_raw_blk561_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hA : AllocContractsXCliPlaced A lim H)
    (_hpan : H handleErrorSymCli = some Rust.panicked := by
      simp [handleErrorSymCli, cliExternsPlaced, isCliPanicSymbolPlaced, cliPanicSymbolsPlaced,
        Rust.withPanics, Rust.isPanicSymbol]) :
    subroutine_ok (lsProg_561 H) (lsmpl.base 561)
      (withLsCodeRoLoaded lsmpl (doReserveStrideRawSpecX M A lim)) := by
  have hshim587 := AllocContractsXCliPlaced.shim2_rocl (prog := lsProg_587 H) (i := 587) hA
  have halloc587 := allocNoOomExtern_rocl (prog := lsProg_587 H) (i := 587) hA
  have hrealloc587 := reallocNoOomExtern_rocl (prog := lsProg_587 H) (i := 587) hA
  have hfg0 := drop_rocl_post
    (finish_grow_zero_cells_placed_ok_of_hooks_at (prog := lsProg_561 H) (i := 561)
      hshim587 halloc587 hrealloc587)
  have hfg1 := drop_rocl_post
    (finish_grow_ne_cells_placed_ok_of_hooks_at (prog := lsProg_561 H) (i := 561)
      hshim587 halloc587 hrealloc587)
  dsimp only [lsProg_561] at hfg0 hfg1
  unfold withLsCodeRoLoaded
  simp only [doReserveStrideRawSpecX,
    LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget.doReserveStrideRawSpecWithStack,
    stackAt_cliGrowOne, sepExists_sepConj_right]
  change subroutine_ok ((blkPC_561).rebase (blkPl_561).base H) (blkPl_561).base _
  wp_init x s0
  rcases x with ⟨⟨v, cap, ptr, bs, len, additional, align, stride⟩, st⟩
  dsimp only at *
  have hcrl0 : LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  have hx1_eq : (s0.readReg64 .x1).toNat = len := by assumption
  have hx2_eq : (s0.readReg64 .x2).toNat = additional := by assumption
  have hlen_le_cap : len ≤ cap.toNat := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat * stride.toNat := by assumption
  have hptr_ne : ptr ≠ 0#64 := by assumption
  have hstr_pos : 0 < stride.toNat := by assumption
  have hrlay : RustLayoutOk
      (reserveCapStride stride.toNat cap.toNat len additional * stride.toNat)
      align.toNat := by assumption
  have hfits_env : FitsEnv M lim st
      (DoReserveStrideEnv ⟨v, cap, ptr, bs, len, additional, align, stride⟩) := by assumption
  have hlay0 := hrlay.1
  have hal_le := hrlay.2
  have hsz_pos : 0 < reserveCapStride stride.toNat cap.toNat len additional * stride.toNat :=
    hlay0.1
  have hpow : ∃ k, align.toNat = 2 ^ k := hlay0.2.1
  have hbound :
      reserveCapStride stride.toNat cap.toNat len additional * stride.toNat +
        align.toNat ≤ 2 ^ 63 := hlay0.2.2
  have halign_pos : 1 ≤ align.toNat := by
    rcases hpow with ⟨k, hk⟩; rw [hk]; exact Nat.one_le_two_pow
  have hmin_ge : 4 ≤ reserveMinCap stride.toNat := by
    unfold reserveMinCap; split <;> omega
  have hnew_lt63 : reserveCapStride stride.toNat cap.toNat len additional < 2 ^ 63 := by
    have : reserveCapStride stride.toNat cap.toNat len additional * 1 ≤
        reserveCapStride stride.toNat cap.toNat len additional * stride.toNat :=
      Nat.mul_le_mul_left _ hstr_pos
    omega
  have hmax : max (max (len + additional) (2 * cap.toNat))
      (reserveMinCap stride.toNat) < 2 ^ 63 := hnew_lt63
  have hcs := adds_cs_eq_false_p (x2 := s0.readReg64 .x2) (x1 := s0.readReg64 .x1) (by
    rw [hx2_eq, hx1_eq]; omega)
  have hnew_eq := reserve_new_cap_stride_eq_p (stride := stride) (cap := cap) hx1_eq hx2_eq hnew_lt63
  let new := BitVec.ofNat 64 (reserveCapStride stride.toNat cap.toNat len additional)
  have hnew_toNat : new.toNat = reserveCapStride stride.toNat cap.toNat len additional := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by
    rw [hnew_toNat]; dsimp [reserveCapStride]; omega
  have hnew_pos : 0 < new.toNat := by
    rw [hnew_toNat]; dsimp [reserveCapStride]; omega
  have hnew_rlay : RustLayoutOk (new.toNat * stride.toNat) align.toNat := by
    rw [hnew_toNat]; exact hrlay
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have h0_mul : (0#64 : BitVec 64).toNat * stride.toNat = 0 := Nat.zero_mul stride.toNat
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hbs
    have hfits0 : FitsEnv M lim st (FinishGrowZeroEnv new stride align) := by
      intro evs hevs
      rw [fitsEnv_doReserveStride_iff] at hfits_env
      dsimp only [FinishGrowZeroEnv] at hevs
      subst hevs
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
    simp only [pointsToBytes_nil,
      List.length_nil, BitVec.add_zero, Nat.sub_zero, BitVec.toNat_ofNat, Nat.zero_mod,
      doReserveStrideEvents, ↓reduceIte, hmul_eq]
    apply sepWP_seq_lscro (mid := lsmpl.base 587) hcrl0
    wp_steps_sync_pool (lsmpl.base 587)
    simp only [State.setMem_setMem]
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    intro hcrl1
    simp only [wp_norm] at hcrl1
    have ⟨hcl1, hro1⟩ := hcrl1
    wp_call hfg0
      ((s0.sp - 56#64, 0#64, ptr, new, align, stride, [], v_stk_1, v_stk_2, v_stk_3,
        s0.sp - 64#64), st)
    dsimp only [FinishGrowZeroEnv] at hpost
    subst hpost
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    wp_done
  · have hfits1 : FitsEnv M lim st (FinishGrowNeEnv cap new stride align) := by
      intro evs hevs
      rw [fitsEnv_doReserveStride_iff] at hfits_env
      dsimp only [FinishGrowNeEnv] at hevs
      subst hevs
      simpa only [doReserveStrideEvents, hcap0, ↓reduceIte, hnew_toNat] using hfits_env
    simp only [hcap0, doReserveStrideEvents, ↓reduceIte, sepConj_assoc]
    have hsub_eq :
        reserveCapStride stride.toNat cap.toNat len additional * stride.toNat - bs.length =
          new.toNat * stride.toNat - bs.length := by rw [hnew_toNat]
    have hmul_eq :
        reserveCapStride stride.toNat cap.toNat len additional * stride.toNat =
          new.toNat * stride.toNat := by rw [hnew_toNat]
    rw [hsub_eq, hmul_eq]
    apply sepWP_seq_lscro (mid := lsmpl.base 587) hcrl0
    wp_steps_sync_pool (lsmpl.base 587)
    simp only [State.setMem_setMem]
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    intro hcrl1
    simp only [wp_norm] at hcrl1
    have ⟨hcl1, hro1⟩ := hcrl1
    wp_call hfg1
      ((s0.sp - 56#64, cap, ptr, new, align, stride, bs, v_stk_1, v_stk_2, v_stk_3,
        s0.sp - 64#64), st)
    dsimp only [FinishGrowNeEnv] at hpost
    subst hpost
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    wp_done

theorem reserve11_raw_fs_blk561_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hFs : AllocContractsFsPlaced A lim H)
    (_hpan : H handleErrorSymCli = some Rust.panicked := by
      simp [handleErrorSymCli, cliExternsPlaced, isCliPanicSymbolPlaced, cliPanicSymbolsPlaced,
        Rust.withPanics, Rust.isPanicSymbol]) :
    subroutine_ok (lsProg_561 H) (lsmpl.base 561)
      (withLsCodeRoLoaded lsmpl (doReserveStrideRawSpecX M A lim).keepsFs) := by
  have hshim587 := AllocContractsFsPlaced.shim2_rocl (prog := lsProg_587 H) (i := 587) hFs
  have halloc587 := allocNoOomExtern_fs_rocl (prog := lsProg_587 H) (i := 587) hFs
  have hrealloc587 := reallocNoOomExtern_fs_rocl (prog := lsProg_587 H) (i := 587) hFs
  have hfg0 := drop_rocl_post
    (finish_grow_zero_cells_fs_placed_ok_of_hooks_at (prog := lsProg_561 H) (i := 561)
      hshim587 halloc587 hrealloc587)
  have hfg1 := drop_rocl_post
    (finish_grow_ne_cells_fs_placed_ok_of_hooks_at (prog := lsProg_561 H) (i := 561)
      hshim587 halloc587 hrealloc587)
  dsimp only [lsProg_561] at hfg0 hfg1
  unfold withLsCodeRoLoaded
  simp only [Spec.keepsFs, doReserveStrideRawSpecX,
    LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget.doReserveStrideRawSpecWithStack,
    stackAt_cliGrowOne, sepExists_sepConj_right]
  change subroutine_ok ((blkPC_561).rebase (blkPl_561).base H) (blkPl_561).base _
  wp_init x s0
  rcases x with ⟨⟨v, cap, ptr, bs, len, additional, align, stride⟩, st⟩
  dsimp only at *
  have hcrl0 : LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  have hx1_eq : (s0.readReg64 .x1).toNat = len := by assumption
  have hx2_eq : (s0.readReg64 .x2).toNat = additional := by assumption
  have hlen_le_cap : len ≤ cap.toNat := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat * stride.toNat := by assumption
  have hptr_ne : ptr ≠ 0#64 := by assumption
  have hstr_pos : 0 < stride.toNat := by assumption
  have hrlay : RustLayoutOk
      (reserveCapStride stride.toNat cap.toNat len additional * stride.toNat)
      align.toNat := by assumption
  have hfits_env : FitsEnv M lim st
      (DoReserveStrideEnv ⟨v, cap, ptr, bs, len, additional, align, stride⟩) := by assumption
  have hlay0 := hrlay.1
  have hal_le := hrlay.2
  have hsz_pos : 0 < reserveCapStride stride.toNat cap.toNat len additional * stride.toNat :=
    hlay0.1
  have hpow : ∃ k, align.toNat = 2 ^ k := hlay0.2.1
  have hbound :
      reserveCapStride stride.toNat cap.toNat len additional * stride.toNat +
        align.toNat ≤ 2 ^ 63 := hlay0.2.2
  have halign_pos : 1 ≤ align.toNat := by
    rcases hpow with ⟨k, hk⟩; rw [hk]; exact Nat.one_le_two_pow
  have hmin_ge : 4 ≤ reserveMinCap stride.toNat := by
    unfold reserveMinCap; split <;> omega
  have hnew_lt63 : reserveCapStride stride.toNat cap.toNat len additional < 2 ^ 63 := by
    have : reserveCapStride stride.toNat cap.toNat len additional * 1 ≤
        reserveCapStride stride.toNat cap.toNat len additional * stride.toNat :=
      Nat.mul_le_mul_left _ hstr_pos
    omega
  have hmax : max (max (len + additional) (2 * cap.toNat))
      (reserveMinCap stride.toNat) < 2 ^ 63 := hnew_lt63
  have hcs := adds_cs_eq_false_p (x2 := s0.readReg64 .x2) (x1 := s0.readReg64 .x1) (by
    rw [hx2_eq, hx1_eq]; omega)
  have hnew_eq := reserve_new_cap_stride_eq_p (stride := stride) (cap := cap) hx1_eq hx2_eq hnew_lt63
  let new := BitVec.ofNat 64 (reserveCapStride stride.toNat cap.toNat len additional)
  have hnew_toNat : new.toNat = reserveCapStride stride.toNat cap.toNat len additional := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by
    rw [hnew_toNat]; dsimp [reserveCapStride]; omega
  have hnew_pos : 0 < new.toNat := by
    rw [hnew_toNat]; dsimp [reserveCapStride]; omega
  have hnew_rlay : RustLayoutOk (new.toNat * stride.toNat) align.toNat := by
    rw [hnew_toNat]; exact hrlay
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have h0_mul : (0#64 : BitVec 64).toNat * stride.toNat = 0 := Nat.zero_mul stride.toNat
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hbs
    have hfits0 : FitsEnv M lim st (FinishGrowZeroEnv new stride align) := by
      intro evs hevs
      rw [fitsEnv_doReserveStride_iff] at hfits_env
      dsimp only [FinishGrowZeroEnv] at hevs
      subst hevs
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
    simp only [pointsToBytes_nil,
      List.length_nil, BitVec.add_zero, Nat.sub_zero, BitVec.toNat_ofNat, Nat.zero_mod,
      doReserveStrideEvents, ↓reduceIte, hmul_eq]
    apply sepWP_seq_lscro (mid := lsmpl.base 587) hcrl0
    wp_steps_sync_pool (lsmpl.base 587)
    simp only [State.setMem_setMem]
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    intro hcrl1
    simp only [wp_norm] at hcrl1
    have ⟨hcl1, hro1⟩ := hcrl1
    wp_call hfg0
      ((s0.sp - 56#64, 0#64, ptr, new, align, stride, [], v_stk_1, v_stk_2, v_stk_3,
        s0.sp - 64#64), st)
    dsimp only [FinishGrowZeroEnv] at hpost
    subst hpost
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    wp_done
  · have hfits1 : FitsEnv M lim st (FinishGrowNeEnv cap new stride align) := by
      intro evs hevs
      rw [fitsEnv_doReserveStride_iff] at hfits_env
      dsimp only [FinishGrowNeEnv] at hevs
      subst hevs
      simpa only [doReserveStrideEvents, hcap0, ↓reduceIte, hnew_toNat] using hfits_env
    simp only [hcap0, doReserveStrideEvents, ↓reduceIte, sepConj_assoc]
    have hsub_eq :
        reserveCapStride stride.toNat cap.toNat len additional * stride.toNat - bs.length =
          new.toNat * stride.toNat - bs.length := by rw [hnew_toNat]
    have hmul_eq :
        reserveCapStride stride.toNat cap.toNat len additional * stride.toNat =
          new.toNat * stride.toNat := by rw [hnew_toNat]
    rw [hsub_eq, hmul_eq]
    apply sepWP_seq_lscro (mid := lsmpl.base 587) hcrl0
    wp_steps_sync_pool (lsmpl.base 587)
    simp only [State.setMem_setMem]
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    intro hcrl1
    simp only [wp_norm] at hcrl1
    have ⟨hcl1, hro1⟩ := hcrl1
    wp_call hfg1
      ((s0.sp - 56#64, cap, ptr, new, align, stride, bs, v_stk_1, v_stk_2, v_stk_3,
        s0.sp - 64#64), st)
    dsimp only [FinishGrowNeEnv] at hpost
    subst hpost
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    wp_done

/-! ## 3. Pure `doReserveSpecOf` & `reserve16` Refinements -/

private theorem vecU8At_eq_p (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (if cap = 0#64 then emp
       else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
         memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) := by
  simp only [vecU8At, vecHeader, BitVec.ofNat_eq_ofNat]
  sep_ac_rfl

theorem doReserveStrideRaw_refines_doReserveSpecOf_pure {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {resStack : Nat} (hstk : doReserveStackX ≤ resStack) :
    SpecRefines
      (doReserveStrideRawSpecX M A lim)
      (doReserveSpecOf resStack A lim) := by
  intro ⟨x, st⟩ R s0 hpre
  simp only [doReserveSpecOf, vecU8At_eq_p, RustCliAllocBudget.repAlloc_live_norm,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hbound, hfits⟩, ⟨hlen, _hcap63, hptr⟩, hmem⟩
  have hhi : resStack ≤ 2 ^ 64 := by
    have hm := hmem
    rw [stackAt, repack_stack_bound] at hm
    exact memRegion_bound_of_pointsTo64 hm
  have hlo : 64 + finishGrowStackX ≤ resStack := by
    have : 64 + finishGrowStackX = doReserveStackX := by decide
    omega
  have hsplit : stackAt s0.sp resStack =
      memRegion (s0.sp - BitVec.ofNat 64 resStack) (resStack - doReserveStackX) ∗
        stackAt s0.sp doReserveStackX :=
    stackAt_split_stk s0.sp hlo hhi
  have hstk_eq : (extHookStack + 48) + 64 = doReserveStackX := by decide
  rw [hsplit, repack_raw_pre] at hmem
  let xs : DoReserveStrideCall :=
    ⟨x.v, x.cap, x.ptr, x.bs, x.bs.length, x.additional, 1#64, 1#64⟩
  have hrlay : RustLayoutOk (reserveCap x.cap.toNat x.bs.length x.additional) 1 :=
    ⟨⟨by dsimp [reserveCap]; omega, ⟨0, rfl⟩, by omega⟩, by decide⟩
  have hevs : doReserveStrideEvents xs = doReserveEvents x := by
    unfold doReserveStrideEvents doReserveEvents
    simp only [xs, BitVec.toNat_ofNat, Nat.one_mod, reserveCapStride_one, Nat.mul_one]
  have hfits_s : FitsEnv M lim st (DoReserveStrideEnv xs) := by
    rw [fitsEnv_doReserveStride_iff, hevs, ← fitsEnv_doReserve_iff]
    exact hfits
  let F : SepProp :=
    ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
      memRegion (s0.sp - BitVec.ofNat 64 resStack) (resStack - doReserveStackX) ∗ R
  have hpre' : s0.mem ⊨ (doReserveStrideRawSpecX M A lim).pre (xs, st) s0 ∗ F := by
    simp only [doReserveStrideRawSpecX,
      LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget.doReserveStrideRawSpecWithStack,
      hstk_eq, xs, BitVec.toNat_ofNat, Nat.one_mod, reserveCapStride_one, Nat.mul_one,
      sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hlen, hlen, hptr, by decide, hrlay, hfits_s⟩, hmem⟩
  refine ⟨(xs, st), F, hpre', ?_,
    fun _ hq => (not_satisfies_false_sepConj hq).elim,
    fun _ _ hq => (not_satisfies_false_sepConj hq).elim,
    fun _ hq => (not_satisfies_false_sepConj hq).elim⟩
  intro sf hq
  simp only [doReserveStrideRawSpecX,
    LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget.doReserveStrideRawSpecWithStack,
    doReserveSpecOf, vecU8At_eq_p, RustCliAllocBudget.repAlloc_live_norm, hstk_eq, hevs,
    xs, BitVec.toNat_ofNat, Nat.one_mod, reserveCapStride_one, Nat.mul_one,
    Nat.mod_one, and_true] at hq ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq
  rcases hq with ⟨htrace, hq⟩
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hq
  rcases hq with ⟨p', hq⟩
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq
  rcases hq with ⟨hp', hpost_mem⟩
  have hlt : reserveCap x.cap.toNat x.bs.length x.additional < 2 ^ 64 := by
    dsimp [reserveCap] at hbound ⊢; omega
  have hlen_le : x.bs.length ≤ reserveCap x.cap.toNat x.bs.length x.additional := by
    dsimp [reserveCap]; omega
  have hcap63' : reserveCap x.cap.toNat x.bs.length x.additional < 2 ^ 63 := by omega
  have hcap_ne : BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional) ≠ 0#64 := by
    intro heq
    have ht := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at ht
    change reserveCap x.cap.toNat x.bs.length x.additional = 0 at ht
    dsimp [reserveCap] at ht; omega
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htrace, ?_⟩
  simp only [sepExists_sepConj_left, satisfies_sepExists]
  refine ⟨p', ?_⟩
  simp only [hcap_ne, ite_false, Nat.mod_eq_of_lt hlt, hsplit]
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨hlen_le, hcap63', hp'⟩, ?_⟩
  rw [← repack_raw_post]
  dsimp only [F] at hpost_mem
  exact hpost_mem

theorem reserve1_blk561_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {resStack : Nat}
    (hCF : AllocContractsFsPlaced A lim H)
    (hres : doReserveStackX ≤ resStack)
    (hpan : H handleErrorSymCli = some Rust.panicked := by
      simp [handleErrorSymCli, cliExternsPlaced, isCliPanicSymbolPlaced, cliPanicSymbolsPlaced,
        Rust.withPanics, Rust.isPanicSymbol]) :
    subroutine_ok (lsProg_561 H) (lsmpl.base 561)
      (withLsCodeRoLoaded lsmpl (doReserveSpecOf resStack A lim).keepsFs) :=
  SpecRefines.apply_keepsFs_withLsCodeRoLoaded
    (doReserveStrideRaw_refines_doReserveSpecOf_pure hres)
    (reserve11_raw_fs_blk561_ok hCF hpan)

theorem cliDoReserve_blk561_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {resStack : Nat}
    (hA : AllocContractsXCliPlaced A lim H)
    (hstk : doReserveStackX ≤ resStack)
    (hpan : H handleErrorSymCli = some Rust.panicked := by
      simp [handleErrorSymCli, cliExternsPlaced, isCliPanicSymbolPlaced, cliPanicSymbolsPlaced,
        Rust.withPanics, Rust.isPanicSymbol]) :
    subroutine_ok (lsProg_561 H) (lsmpl.base 561)
      (withLsCodeRoLoaded lsmpl (doReserveSpecOf resStack A lim)) :=
  SpecRefines.apply_withLsCodeRoLoaded
    (doReserveStrideRaw_refines_doReserveSpecOf_pure hstk)
    (reserve11_raw_blk561_ok hA hpan)

abbrev reserve16CapSpec {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (resStack : Nat) : Spec (Reserve16Call × M.σ) :=
  reserve16Spec A lim resStack

/-- Equality-guarded (`x.cap = BitVec.ofNat 64 (x.bs.length / 16)`) variant of `reserve16Spec`. -/
def reserve16EqSpec {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (resStack : Nat) : Spec (Reserve16Call × M.σ) where
  pre := fun (x, st) s0 =>
    ⌜s0.readReg64 .x0 = x.v ∧ s0.readReg64 .x1 = BitVec.ofNat 64 (x.bs.length / 16) ∧
      s0.readReg64 .x2 = 1#64 ∧ s0.readReg64 .x3 = 8#64 ∧ s0.readReg64 .x4 = 16#64 ∧
      16 * (x.bs.length / 16 + 1) < 2 ^ 62 ∧
      x.cap = BitVec.ofNat 64 (x.bs.length / 16) ∧
      FitsEnv M lim st (Reserve16Env x)⌝ ∗
      vec16At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s0 ∗ stackAt s0.sp resStack
  post := (reserve16Spec A lim resStack).post

private theorem vec16At_eq_p (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vec16At A v cap ptr bs =
      ⌜bs.length % 16 = 0 ∧ bs.length ≤ 16 * cap.toNat ∧ 16 * cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (bs.length / 16)) ∗
      (if cap = 0#64 then emp
       else A.live ptr (16 * cap.toNat) 8 ∗ (ptr ↦ₛ bs) ∗
         memRegion (ptr + BitVec.ofNat 64 bs.length) (16 * cap.toNat - bs.length)) := by
  simp only [vec16At, vecHeader, BitVec.ofNat_eq_ofNat]
  sep_ac_rfl

theorem reserve16Cap_blk561_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {resStack : Nat}
    (hCF : AllocContractsFsPlaced A lim H)
    (hres : doReserveStackX ≤ resStack)
    (hpan : H handleErrorSymCli = some Rust.panicked := by
      simp [handleErrorSymCli, cliExternsPlaced, isCliPanicSymbolPlaced, cliPanicSymbolsPlaced,
        Rust.withPanics, Rust.isPanicSymbol]) :
    subroutine_ok (lsProg_561 H) (lsmpl.base 561)
      (withLsCodeRoLoaded lsmpl (reserve16CapSpec A lim resStack)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  obtain ⟨hcrl, hpre0⟩ := extract_withLsCodeRoLoaded hpre
  simp only [reserve16CapSpec, reserve16Spec, vec16At_eq_p, RustCliAllocBudget.repAlloc_live_norm,
    sepConj_assoc, satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨⟨hx0, hx1, hx2, hx3, hx4, hlen62, hcap62, hfits⟩,
    ⟨hmod16, hbs_le, _hcap63, hptr⟩, hmem⟩
  have hhi : resStack ≤ 2 ^ 64 := by
    have hm := hmem
    rw [stackAt, repack_stack_bound] at hm
    exact memRegion_bound_of_pointsTo64 hm
  have hlo : 64 + finishGrowStackX ≤ resStack := by
    have : 64 + finishGrowStackX = doReserveStackX := by decide
    omega
  have hsplit : stackAt s0.sp resStack =
      memRegion (s0.sp - BitVec.ofNat 64 resStack) (resStack - doReserveStackX) ∗
        stackAt s0.sp doReserveStackX :=
    stackAt_split_stk s0.sp hlo hhi
  have hstk_eq : (extHookStack + 48) + 64 = doReserveStackX := by decide
  rw [hsplit, repack_raw_pre] at hmem
  let len := x.bs.length / 16
  let newCap := reserveCapStride 16 x.cap.toNat len 1
  have hx1_nat : (s0.readReg64 .x1).toNat = len := by
    rw [hx1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by dsimp [len]; omega)]
  have hx2_nat : (s0.readReg64 .x2).toNat = 1 := by rw [hx2]; rfl
  have hlen_le_cap : len ≤ x.cap.toNat := by dsimp [len]; omega
  have hnew_mul : newCap * 16 + 8 ≤ 2 ^ 63 := by
    dsimp [newCap, reserveCapStride, reserveMinCap, len]
    omega
  have hrlay : RustLayoutOk (newCap * 16) 8 :=
    ⟨⟨by dsimp [newCap, reserveCapStride, reserveMinCap]; omega,
      ⟨3, rfl⟩, hnew_mul⟩, by decide⟩
  let xs : DoReserveStrideCall :=
    ⟨x.v, x.cap, x.ptr, x.bs, len, 1, 8#64, 16#64⟩
  have hevs : doReserveStrideEvents xs = reserve16Events x := by
    unfold doReserveStrideEvents reserve16Events
    simp only [xs, len,
      show (8#64 : BitVec 64).toNat = 8 from rfl,
      show (16#64 : BitVec 64).toNat = 16 from rfl,
      Nat.mul_comm]
  have hfits_s : FitsEnv M lim st (DoReserveStrideEnv xs) := by
    rw [fitsEnv_doReserveStride_iff, hevs]
    exact hfits (reserve16Events x) rfl
  let F : SepProp :=
    ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 len) ∗
      memRegion (s0.sp - BitVec.ofNat 64 resStack) (resStack - doReserveStackX) ∗ R
  have hcap_comm : x.cap.toNat * 16 = 16 * x.cap.toNat := Nat.mul_comm _ _
  have hpre' : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl (doReserveStrideRawSpecX M A lim).keepsFs).pre (xs, st) s0 ∗ F := by
    dsimp only [withLsCodeRoLoaded, Spec.keepsFs]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl, ?_⟩
    simp only [doReserveStrideRawSpecX,
      LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget.doReserveStrideRawSpecWithStack,
      hstk_eq, xs,
      show (8#64 : BitVec 64).toNat = 8 from rfl,
      show (16#64 : BitVec 64).toNat = 16 from rfl,
      hcap_comm, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1_nat, hx2_nat, hx3, hx4, hlen_le_cap, hbs_le, hptr, by decide, hrlay,
      hfits_s⟩, hmem⟩
  refine (reserve11_raw_fs_blk561_ok hCF hpan).mono_outcome (xs, st) F s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [Spec.keepsFs, doReserveStrideRawSpecX,
      LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget.doReserveStrideRawSpecWithStack,
      reserve16CapSpec, reserve16Spec, vec16At_eq_p, RustCliAllocBudget.repAlloc_live_norm,
      hstk_eq, hevs, xs,
      show (8#64 : BitVec 64).toNat = 8 from rfl,
      show (16#64 : BitVec 64).toNat = 16 from rfl] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨hfs, hq⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htrace, hq⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq
    rcases hq with ⟨p', hq⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨⟨hp'_ne, _⟩, hpost_mem⟩
    have hnew_lt64 : newCap < 2 ^ 64 := by omega
    have htoNat : (BitVec.ofNat 64 newCap).toNat = newCap := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnew_lt64]
    have hgrow : len + 1 ≤ newCap := by
      dsimp [newCap, reserveCapStride]; omega
    have hbs_le' : x.bs.length ≤ 16 * newCap := by dsimp [len] at hgrow; omega
    have hcap63' : 16 * newCap < 2 ^ 63 := by omega
    have hcap_ne : BitVec.ofNat 64 newCap ≠ 0#64 := by
      intro heq
      have ht := congrArg BitVec.toNat heq
      rw [htoNat] at ht
      change newCap = 0 at ht
      omega
    have hnew_comm : newCap * 16 = 16 * newCap := Nat.mul_comm _ _
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨reserve16Events x, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨htrace, hfs, rfl⟩, ?_⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨BitVec.ofNat 64 newCap, p', ?_⟩
    simp only [hcap_ne, ite_false, htoNat, hsplit]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hgrow, ?_⟩
    rw [satisfies_pure_sepConj]
    refine ⟨⟨hmod16, hbs_le', hcap63', hp'_ne⟩, ?_⟩
    rw [hnew_comm] at hpost_mem
    rw [← repack_raw_post]
    dsimp only [F] at hpost_mem
    exact hpost_mem
  · dsimp only [withLsCodeRoLoaded, Spec.keepsFs, doReserveStrideRawSpecX,
      LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget.doReserveStrideRawSpecWithStack] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeRoLoaded, Spec.keepsFs, doReserveStrideRawSpecX,
      LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget.doReserveStrideRawSpecWithStack] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeRoLoaded, Spec.keepsFs, doReserveStrideRawSpecX,
      LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget.doReserveStrideRawSpecWithStack] at hq
    exact (not_satisfies_false_sepConj hq).elim

theorem reserve16Eq_blk561_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {resStack : Nat}
    (hCF : AllocContractsFsPlaced A lim H)
    (hres : doReserveStackX ≤ resStack)
    (hpan : H handleErrorSymCli = some Rust.panicked := by
      simp [handleErrorSymCli, cliExternsPlaced, isCliPanicSymbolPlaced, cliPanicSymbolsPlaced,
        Rust.withPanics, Rust.isPanicSymbol]) :
    subroutine_ok (lsProg_561 H) (lsmpl.base 561)
      (withLsCodeRoLoaded lsmpl (reserve16EqSpec A lim resStack)) := by
  refine subroutine_ok_mono (reserve16Cap_blk561_ok hCF hres hpan) ?_ (fun _ _ _ _ h => h)
  rintro ⟨x, st⟩ R s0 hpre
  obtain ⟨hcrl, hpre0⟩ := extract_withLsCodeRoLoaded hpre
  simp only [reserve16EqSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨⟨hx0, hx1, hx2, hx3, hx4, hlen62, hcap_eq, hfits⟩, hmem⟩
  have hcap62 : 16 * x.cap.toNat < 2 ^ 62 := by
    rw [hcap_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  dsimp only [withLsCodeRoLoaded]
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  refine ⟨hcrl, ?_⟩
  simp only [reserve16CapSpec, reserve16Spec, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hlen62, hcap62, hfits⟩, hmem⟩

theorem reserve16_blk561_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {resStack : Nat}
    (hCF : AllocContractsFsPlaced A lim H)
    (hres : doReserveStackX ≤ resStack)
    (hpan : H handleErrorSymCli = some Rust.panicked := by
      simp [handleErrorSymCli, cliExternsPlaced, isCliPanicSymbolPlaced, cliPanicSymbolsPlaced,
        Rust.withPanics, Rust.isPanicSymbol]) :
    subroutine_ok (lsProg_561 H) (lsmpl.base 561)
      (withLsCodeRoLoaded lsmpl (reserve16Spec A lim resStack)) :=
  reserve16Cap_blk561_ok hCF hres hpan

/-! ## 4. Cross-Block Lifted Contracts (`withLsRoCl lsmpl`, Block `561` → Any Caller Block & Block `617`) -/

section CallerBlock
variable [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
  {lim : BudgetLimits} {H : LibsignalHooks}
  {prog : Program} {i : Nat} [IsLsBlockProg prog i H]

theorem reserve1_placed_ok_at {resStack : Nat}
    (hCF : AllocContractsFsPlaced A lim H)
    (hres : doReserveStackX ≤ resStack)
    (hpan : H handleErrorSymCli = some Rust.panicked := by
      simp [handleErrorSymCli, cliExternsPlaced, isCliPanicSymbolPlaced, cliPanicSymbolsPlaced,
        Rust.withPanics, Rust.isPanicSymbol])
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsmpl.base 561)
      (withLsRoCl lsmpl (doReserveSpecOf resStack A lim).keepsFs) :=
  ls_subroutine_ok_rocl_of_block (i := i) (j := 561)
    (reserve1_blk561_ok hCF hres hpan) hi

theorem cliDoReserve_placed_ok_at {resStack : Nat}
    (hA : AllocContractsXCliPlaced A lim H)
    (hstk : doReserveStackX ≤ resStack)
    (hpan : H handleErrorSymCli = some Rust.panicked := by
      simp [handleErrorSymCli, cliExternsPlaced, isCliPanicSymbolPlaced, cliPanicSymbolsPlaced,
        Rust.withPanics, Rust.isPanicSymbol])
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsmpl.base 561)
      (withLsRoCl lsmpl (doReserveSpecOf resStack A lim)) :=
  ls_subroutine_ok_rocl_of_block (i := i) (j := 561)
    (cliDoReserve_blk561_ok hA hstk hpan) hi

theorem reserve16Cap_placed_ok_at {resStack : Nat}
    (hCF : AllocContractsFsPlaced A lim H)
    (hres : doReserveStackX ≤ resStack)
    (hpan : H handleErrorSymCli = some Rust.panicked := by
      simp [handleErrorSymCli, cliExternsPlaced, isCliPanicSymbolPlaced, cliPanicSymbolsPlaced,
        Rust.withPanics, Rust.isPanicSymbol])
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsmpl.base 561)
      (withLsRoCl lsmpl (reserve16CapSpec A lim resStack)) :=
  ls_subroutine_ok_rocl_of_block (i := i) (j := 561)
    (reserve16Cap_blk561_ok hCF hres hpan) hi

theorem reserve16Eq_placed_ok_at {resStack : Nat}
    (hCF : AllocContractsFsPlaced A lim H)
    (hres : doReserveStackX ≤ resStack)
    (hpan : H handleErrorSymCli = some Rust.panicked := by
      simp [handleErrorSymCli, cliExternsPlaced, isCliPanicSymbolPlaced, cliPanicSymbolsPlaced,
        Rust.withPanics, Rust.isPanicSymbol])
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsmpl.base 561)
      (withLsRoCl lsmpl (reserve16EqSpec A lim resStack)) :=
  ls_subroutine_ok_rocl_of_block (i := i) (j := 561)
    (reserve16Eq_blk561_ok hCF hres hpan) hi

theorem reserve16_placed_ok_at {resStack : Nat}
    (hCF : AllocContractsFsPlaced A lim H)
    (hres : doReserveStackX ≤ resStack)
    (hpan : H handleErrorSymCli = some Rust.panicked := by
      simp [handleErrorSymCli, cliExternsPlaced, isCliPanicSymbolPlaced, cliPanicSymbolsPlaced,
        Rust.withPanics, Rust.isPanicSymbol])
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsmpl.base 561)
      (withLsRoCl lsmpl (reserve16Spec A lim resStack)) :=
  ls_subroutine_ok_rocl_of_block (i := i) (j := 561)
    (reserve16_blk561_ok hCF hres hpan) hi

end CallerBlock

theorem reserve1_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {resStack : Nat}
    (hCF : AllocContractsFsPlaced A lim H)
    (hres : doReserveStackX ≤ resStack)
    (hpan : H handleErrorSymCli = some Rust.panicked := by
      simp [handleErrorSymCli, cliExternsPlaced, isCliPanicSymbolPlaced, cliPanicSymbolsPlaced,
        Rust.withPanics, Rust.isPanicSymbol]) :
    subroutine_ok (lsProg_617 H) (lsmpl.base 561)
      (withLsRoCl lsmpl (doReserveSpecOf resStack A lim).keepsFs) :=
  reserve1_placed_ok_at (prog := lsProg_617 H) (i := 617) hCF hres hpan

theorem cliDoReserve_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {resStack : Nat}
    (hA : AllocContractsXCliPlaced A lim H)
    (hstk : doReserveStackX ≤ resStack)
    (hpan : H handleErrorSymCli = some Rust.panicked := by
      simp [handleErrorSymCli, cliExternsPlaced, isCliPanicSymbolPlaced, cliPanicSymbolsPlaced,
        Rust.withPanics, Rust.isPanicSymbol]) :
    subroutine_ok (lsProg_617 H) (lsmpl.base 561)
      (withLsRoCl lsmpl (doReserveSpecOf resStack A lim)) :=
  cliDoReserve_placed_ok_at (prog := lsProg_617 H) (i := 617) hA hstk hpan

theorem reserve16Cap_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {resStack : Nat}
    (hCF : AllocContractsFsPlaced A lim H)
    (hres : doReserveStackX ≤ resStack)
    (hpan : H handleErrorSymCli = some Rust.panicked := by
      simp [handleErrorSymCli, cliExternsPlaced, isCliPanicSymbolPlaced, cliPanicSymbolsPlaced,
        Rust.withPanics, Rust.isPanicSymbol]) :
    subroutine_ok (lsProg_617 H) (lsmpl.base 561)
      (withLsRoCl lsmpl (reserve16CapSpec A lim resStack)) :=
  reserve16Cap_placed_ok_at (prog := lsProg_617 H) (i := 617) hCF hres hpan

theorem reserve16Eq_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {resStack : Nat}
    (hCF : AllocContractsFsPlaced A lim H)
    (hres : doReserveStackX ≤ resStack)
    (hpan : H handleErrorSymCli = some Rust.panicked := by
      simp [handleErrorSymCli, cliExternsPlaced, isCliPanicSymbolPlaced, cliPanicSymbolsPlaced,
        Rust.withPanics, Rust.isPanicSymbol]) :
    subroutine_ok (lsProg_617 H) (lsmpl.base 561)
      (withLsRoCl lsmpl (reserve16EqSpec A lim resStack)) :=
  reserve16Eq_placed_ok_at (prog := lsProg_617 H) (i := 617) hCF hres hpan

theorem reserve16_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {resStack : Nat}
    (hCF : AllocContractsFsPlaced A lim H)
    (hres : doReserveStackX ≤ resStack)
    (hpan : H handleErrorSymCli = some Rust.panicked := by
      simp [handleErrorSymCli, cliExternsPlaced, isCliPanicSymbolPlaced, cliPanicSymbolsPlaced,
        Rust.withPanics, Rust.isPanicSymbol]) :
    subroutine_ok (lsProg_617 H) (lsmpl.base 561)
      (withLsRoCl lsmpl (reserve16Spec A lim resStack)) :=
  reserve16_placed_ok_at (prog := lsProg_617 H) (i := 617) hCF hres hpan

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Reserve11PlacedBudget

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
public import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget
public import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExtBudgetAux
public meta import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExtBudgetAux -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4KBudget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserve
import LibsignalBinary.Proofs.SpqrV1.Alloc.Fetch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
meta import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry -- shake: keep
import ProofLib.SepLogic.WPp
meta import ProofLib.SepLogic.WPp -- shake: keep

/-!
# Budget-Threaded `AllocContracts4K` Contracts for `finish_grow` and `do_reserve_and_handle`

Re-exports `finish_grow_{8,2,4}_ok_ext_4k` from `DoReserveExtBudgetAux` and proves
`do_reserve_{7,2,4}_*ok_ext_4k` under `Hooks4KBudget.AllocContracts4K b A lim ext`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExtBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification (libsignalSessionCode)
open CryptoVerification.RustHeap (RustAlloc allocHookStack vecHeader vecU8At)
open CryptoVerification.LibsignalTripleRatchet (
  DoReserveCall doReserveStack doReserveStackX extHookStack
  finishGrowStack finishGrowStackX reserveCap subroutine_ok_inImage_of_subroutine_ok
  tripleRatchetProgAtExt
)
open CryptoVerification.SpqrV1.Alloc (
  DoReserveStrideCall adds_cs_eq_false
  doReserve2Name doReserve4Name doReserve7Name
  finishGrow2Name finishGrow4Name finishGrow8Name
  reserveCapStride reserveCapStride_one reserveMinCap
  reserve_new_cap_eq reserve_new_cap_stride_eq
  stackAt_doReserve32_gen stackAt_doReserve_gen
)
open CryptoVerification.SpqrV1.Alloc.DoReserveNorm (
  readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre
  readReg64_setPC_pre readReg_setMem_setPC_pre readReg_setPC_pre
  sp_setMem_setPC_pre sp_setPC_pre
)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits FitsEnv FitsEvents
  RustCliAllocBudget RustLayoutOk
  rustAllocEvents rustReallocEvents
)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (trapHooks)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  DoReserveEnv doReserveEvents finishGrowSpec finishGrowSpecWithStack fitsEnv_doReserve_iff
)
open LibsignalBinary.Proofs.SpqrV1.Alloc.FinishGrowBudget (
  finishGrow1Spec finishGrow1SpecWithStack
)
open LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget (
  DoReserveStrideEnv doReserve1Raw32Spec doReserve1Raw32SpecWithStack
  doReserve1RawSpec doReserve1RawSpecWithStack
  doReserveRawSpec doReserveRawSpecWithStack
  doReserveSpec doReserveSpecWithStack doReserveSpecX
  doReserveStrideEvents doReserveStrideRawSpec doReserveStrideRawSpecWithStack
  finish_grow_24_ne_cells_of_spec finish_grow_24_zero_cells_of_spec
  finish_grow_8_ne_cells_of_spec finish_grow_8_zero_cells_of_spec
  fitsEnv_doReserveStride_iff
)
open LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4KBudget (AllocContracts4K)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg_setPC_pre readReg_setMem_setPC_pre

/-! ## Re-Exported `finish_grow` Contracts -/

theorem finish_grow_8_ok_ext_4k {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow8Name)
      (finishGrowSpec M A lim) :=
  DoReserveExtBudgetAux.finish_grow_8_ok_ext_4k hA

theorem finish_grow_2_ok_ext_4k {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow2Name)
      (finishGrow1Spec M A lim) :=
  DoReserveExtBudgetAux.finish_grow_2_ok_ext_4k hA

theorem finish_grow_4_ok_ext_4k {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow4Name)
      (finishGrow1Spec M A lim) :=
  DoReserveExtBudgetAux.finish_grow_4_ok_ext_4k hA

/-! ## `do_reserve_and_handle` (`[local#7, 2, 4]`) -/

set_option maxHeartbeats 400000 in
private theorem do_reserve_7_stride_raw_ok_gen {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    {hookStack : Nat} (hhook : (hookStack + 48) + 8 * 8 ≤ 2 ^ 64)
    (hfg : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow8Name)
      (finishGrowSpecWithStack M A lim hookStack)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr doReserve7Name)
      (doReserveStrideRawSpecWithStack M A lim hookStack) := by
  have hfg0 := finish_grow_8_zero_cells_of_spec hfg
  have hfg1 := finish_grow_8_ne_cells_of_spec hfg
  have hfn := (ls_lemma% fnOff doReserve7Name)
  rw [Program.fnAddr_rel (name := doReserve7Name)
    hfn (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::finish_grow [local#7]")
    (k := num% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#7]" - ls_off% doReserve7Name))
    (by decide)] at hfg0 hfg1
  unfold doReserveStrideRawSpecWithStack
  simp only [stackAt_doReserve_gen _ hhook, sepExists_sepConj_right]
  code_fetches CryptoVerification.libsignalSessionCode CryptoVerification.SpqrV1.Alloc.spqrAllocBin
    b trapHooks hfn (ls_off% doReserve7Name) 140
  dsimp only [tripleRatchetProgAtExt, doReserve7Name] at *
  simp +singlePass only [Program.fnAddr_rebase,
    LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExtBudgetAux.fetch_withSvc _ noSyscalls] at *
  clear hfn hfg
  generalize_entry (libsignalSessionCode.fnOff
    "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#6]") = fnOffVal
    reverting [Program.fetch, subroutine_ok]
  generalize b + BitVec.ofNat 64 fnOffVal = fnBase at *
  clear fnOffVal
  generalize_entry libsignalSessionCode = codeProg
    reverting [Program.fetch, subroutine_ok]
  examples_hide_fetches
  wp_init x s0
  rcases x with ⟨⟨v, cap, ptr, bs, len, additional, align, stride⟩, st⟩
  dsimp only at *
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
    wp_steps_rebase_pool
      (fnBase + bv% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#7]" - ls_off% doReserve7Name))
    wp_call hfg0
      (s0.sp - 56#64, 0#64, ptr, new, align, stride, [], v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64, st)
    wp_steps_rebase_pool (s0.readReg64 (Reg.gpr 30#5))
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
    wp_steps_rebase_pool
      (fnBase + bv% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#7]" - ls_off% doReserve7Name))
    wp_call hfg1
      (s0.sp - 56#64, cap, ptr, new, align, stride, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64, st)
    wp_steps_rebase_pool (s0.readReg64 (Reg.gpr 30#5))
    wp_done

/-- `do_reserve_and_handle [local#7]` meets `doReserveStrideRawSpec M A lim` under `AllocContracts4K`. -/
theorem do_reserve_7_stride_raw_ok_ext_4k {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr doReserve7Name)
      (doReserveStrideRawSpec M A lim) :=
  do_reserve_7_stride_raw_ok_gen (by decide) (finish_grow_8_ok_ext_4k hA)

private theorem do_reserve_2_raw32_ok_gen {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    {hookStack : Nat} (hhook : (hookStack + 32) + 8 * 8 ≤ 2 ^ 64)
    (hfg : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow2Name)
      (finishGrow1SpecWithStack M A lim hookStack)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr doReserve2Name)
      (doReserve1Raw32SpecWithStack M A lim hookStack) := by
  have hfg0 := finish_grow_24_zero_cells_of_spec hfg
  have hfg1 := finish_grow_24_ne_cells_of_spec hfg
  have hfn := (ls_lemma% fnOff doReserve2Name)
  rw [Program.fnAddr_rel (name := doReserve2Name)
    hfn (ls_lemma% fnOff finishGrow2Name)
    (k := num% (ls_off% finishGrow2Name - ls_off% doReserve2Name))
    (by decide)] at hfg0 hfg1
  unfold doReserve1Raw32SpecWithStack
  simp only [stackAt_doReserve32_gen _ hhook, sepExists_sepConj_right]
  code_fetches CryptoVerification.libsignalSessionCode CryptoVerification.SpqrV1.Alloc.spqrAllocBin
    b trapHooks hfn (ls_off% doReserve2Name) 120
  dsimp only [tripleRatchetProgAtExt, doReserve2Name] at *
  simp +singlePass only [Program.fnAddr_rebase,
    LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExtBudgetAux.fetch_withSvc _ noSyscalls] at *
  clear hfn hfg
  generalize_entry (libsignalSessionCode.fnOff
    "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#2]") = fnOffVal
    reverting [Program.fetch, subroutine_ok]
  generalize b + BitVec.ofNat 64 fnOffVal = fnBase at *
  clear fnOffVal
  generalize_entry libsignalSessionCode = codeProg
    reverting [Program.fetch, subroutine_ok]
  examples_hide_fetches
  wp_init x s0
  rcases x with ⟨⟨v, cap, ptr, bs, additional⟩, st⟩
  dsimp only at *
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
      simpa only [doReserveEvents, BitVec.toNat_zero, ↓reduceIte, hnew_toNat] using hfits_env
    have hnew_eq0 :
        (if (8#64).ult (if (0#64).ult (s0.readReg64 .x2 + s0.readReg64 .x1) = true then
              s0.readReg64 .x2 + s0.readReg64 .x1 else 0#64) = true then
          if (0#64).ult (s0.readReg64 .x2 + s0.readReg64 .x1) = true then
            s0.readReg64 .x2 + s0.readReg64 .x1 else 0#64
         else 8#64) = new := hnew_eq
    have hcap_eq : reserveCap 0 0 additional = new.toNat := by rw [hnew_toNat]; rfl
    simp only [emp_sepConj, pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero,
      BitVec.toNat_zero, doReserveEvents, ↓reduceIte, hcap_eq]
    wp_steps_rebase_pool (fnBase + bv% (ls_off% finishGrow2Name - ls_off% doReserve2Name))
    wp_call hfg0 (s0.sp - 56#64, 0#64, ptr, new, [], v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64, st)
    wp_steps_rebase_pool (s0.readReg64 (Reg.gpr 30#5))
    wp_done
  · have hfits : FitsEvents M lim st (rustReallocEvents cap.toNat new.toNat 1) := by
      rw [fitsEnv_doReserve_iff] at hfits_env
      simpa only [doReserveEvents, hcap0, ↓reduceIte, hnew_toNat] using hfits_env
    simp only [hcap0, doReserveEvents, ↓reduceIte, sepConj_assoc]
    rw [← hnew_toNat]
    wp_steps_rebase_pool (fnBase + bv% (ls_off% finishGrow2Name - ls_off% doReserve2Name))
    wp_call hfg1 (s0.sp - 56#64, cap, ptr, new, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64, st)
    wp_steps_rebase_pool (s0.readReg64 (Reg.gpr 30#5))
    wp_done

theorem do_reserve_2_raw32_ok_ext_4k {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr doReserve2Name)
      (doReserve1Raw32Spec M A lim) :=
  do_reserve_2_raw32_ok_gen (by decide) (finish_grow_2_ok_ext_4k hA)

private theorem do_reserve_4_raw32_ok_gen {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    {hookStack : Nat} (hhook : (hookStack + 32) + 8 * 8 ≤ 2 ^ 64)
    (hfg : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow4Name)
      (finishGrow1SpecWithStack M A lim hookStack)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr doReserve4Name)
      (doReserve1Raw32SpecWithStack M A lim hookStack) := by
  have hfg0 := finish_grow_24_zero_cells_of_spec hfg
  have hfg1 := finish_grow_24_ne_cells_of_spec hfg
  have hfn := (ls_lemma% fnOff doReserve4Name)
  rw [Program.fnAddr_rel (name := doReserve4Name)
    hfn (ls_lemma% fnOff finishGrow4Name)
    (k := num% (ls_off% finishGrow4Name - ls_off% doReserve4Name))
    (by decide)] at hfg0 hfg1
  unfold doReserve1Raw32SpecWithStack
  simp only [stackAt_doReserve32_gen _ hhook, sepExists_sepConj_right]
  code_fetches CryptoVerification.libsignalSessionCode CryptoVerification.SpqrV1.Alloc.spqrAllocBin
    b trapHooks hfn (ls_off% doReserve4Name) 120
  dsimp only [tripleRatchetProgAtExt, doReserve4Name] at *
  simp +singlePass only [Program.fnAddr_rebase,
    LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExtBudgetAux.fetch_withSvc _ noSyscalls] at *
  clear hfn hfg
  generalize_entry (libsignalSessionCode.fnOff
    "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#4]") = fnOffVal
    reverting [Program.fetch, subroutine_ok]
  generalize b + BitVec.ofNat 64 fnOffVal = fnBase at *
  clear fnOffVal
  generalize_entry libsignalSessionCode = codeProg
    reverting [Program.fetch, subroutine_ok]
  examples_hide_fetches
  wp_init x s0
  rcases x with ⟨⟨v, cap, ptr, bs, additional⟩, st⟩
  dsimp only at *
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
      simpa only [doReserveEvents, BitVec.toNat_zero, ↓reduceIte, hnew_toNat] using hfits_env
    have hnew_eq0 :
        (if (8#64).ult (if (0#64).ult (s0.readReg64 .x2 + s0.readReg64 .x1) = true then
              s0.readReg64 .x2 + s0.readReg64 .x1 else 0#64) = true then
          if (0#64).ult (s0.readReg64 .x2 + s0.readReg64 .x1) = true then
            s0.readReg64 .x2 + s0.readReg64 .x1 else 0#64
         else 8#64) = new := hnew_eq
    have hcap_eq : reserveCap 0 0 additional = new.toNat := by rw [hnew_toNat]; rfl
    simp only [emp_sepConj, pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero,
      BitVec.toNat_zero, doReserveEvents, ↓reduceIte, hcap_eq]
    wp_steps_rebase_pool (fnBase + bv% (ls_off% finishGrow4Name - ls_off% doReserve4Name))
    wp_call hfg0 (s0.sp - 56#64, 0#64, ptr, new, [], v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64, st)
    wp_steps_rebase_pool (s0.readReg64 (Reg.gpr 30#5))
    wp_done
  · have hfits : FitsEvents M lim st (rustReallocEvents cap.toNat new.toNat 1) := by
      rw [fitsEnv_doReserve_iff] at hfits_env
      simpa only [doReserveEvents, hcap0, ↓reduceIte, hnew_toNat] using hfits_env
    simp only [hcap0, doReserveEvents, ↓reduceIte, sepConj_assoc]
    rw [← hnew_toNat]
    wp_steps_rebase_pool (fnBase + bv% (ls_off% finishGrow4Name - ls_off% doReserve4Name))
    wp_call hfg1 (s0.sp - 56#64, cap, ptr, new, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64, st)
    wp_steps_rebase_pool (s0.readReg64 (Reg.gpr 30#5))
    wp_done

theorem do_reserve_4_raw32_ok_ext_4k {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr doReserve4Name)
      (doReserve1Raw32Spec M A lim) :=
  do_reserve_4_raw32_ok_gen (by decide) (finish_grow_4_ok_ext_4k hA)

/-! ## Representation, Stack-Framing, and `.inImage` Corollaries -/

private theorem do_reserve_7_raw_of_stride {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {addr : BitVec 64} {hookStack : Nat}
    (hs : subroutine_ok P addr (doReserveStrideRawSpecWithStack M A lim hookStack)) :
    subroutine_ok P addr (doReserveRawSpecWithStack M A lim hookStack) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [doReserveRawSpecWithStack,
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpecWithStack,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hlen, hptr, hbound, hfits⟩, hmem⟩
  let xs : DoReserveStrideCall := ⟨x.v, x.cap, x.ptr, x.bs, x.bs.length, x.additional, 1#64, 1#64⟩
  have hrlay : RustLayoutOk (reserveCap x.cap.toNat x.bs.length x.additional) 1 :=
    ⟨⟨by dsimp [reserveCap]; omega, ⟨0, rfl⟩, by omega⟩, by decide⟩
  have hfits' : FitsEnv M lim st (DoReserveStrideEnv xs) := by
    rw [fitsEnv_doReserve_iff] at hfits
    rw [fitsEnv_doReserveStride_iff]
    by_cases hc : x.cap = 0#64
    · simpa only [doReserveStrideEvents, doReserveEvents, xs, hc, BitVec.toNat_zero,
        BitVec.toNat_ofNat, Nat.one_mod, reserveCapStride_one, Nat.mul_one, ↓reduceIte] using hfits
    · have hc_nat : x.cap.toNat ≠ 0 :=
        Nat.ne_of_gt (Nat.pos_of_ne_zero (fun h0 => hc (BitVec.eq_of_toNat_eq h0)))
      simpa only [doReserveStrideEvents, doReserveEvents, xs, hc, hc_nat,
        BitVec.toNat_ofNat, Nat.one_mod, reserveCapStride_one, Nat.mul_one, ↓reduceIte] using hfits
  have hpre' : s0.mem ⊨ (doReserveStrideRawSpecWithStack M A lim hookStack).pre (xs, st) s0 ∗ R := by
    simp only [doReserveStrideRawSpecWithStack, xs, BitVec.toNat_ofNat, Nat.one_mod,
      reserveCapStride_one, Nat.mul_one, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hlen, hlen, hptr, by decide, hrlay, hfits'⟩, hmem⟩
  refine hs.mono_outcome (xs, st) R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | hfail
  · refine Or.inl ⟨hret, hcc, ?_⟩
    have hevs : doReserveStrideEvents xs = doReserveEvents x := by
      by_cases hc : x.cap = 0#64
      · simp [doReserveStrideEvents, doReserveEvents, xs, hc, reserveCapStride_one]
      · simp [doReserveStrideEvents, doReserveEvents, xs, hc, reserveCapStride_one]
    simpa only [doReserveStrideRawSpecWithStack, doReserveRawSpecWithStack,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpecWithStack,
      xs, hevs, BitVec.toNat_ofNat, Nat.one_mod, reserveCapStride_one, Nat.mul_one, Nat.mod_one,
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

private theorem do_reserve_vec_of_raw {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {addr : BitVec 64} {hookStack : Nat}
    (hraw : subroutine_ok P addr (doReserveRawSpecWithStack M A lim hookStack)) :
    subroutine_ok P addr (doReserveSpecWithStack M A lim hookStack) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [doReserveSpecWithStack,
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpecWithStack,
    vecU8At_eq, RustCliAllocBudget.repAlloc_live_norm, sepConj_assoc, satisfies_pure_sepConj]
    at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hbound, hfits⟩, ⟨hlen, _hcap63, hptr⟩, hmem⟩
  have hpre' : s0.mem ⊨ (doReserveRawSpecWithStack M A lim hookStack).pre (x, st) s0 ∗
      (((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R) := by
    simp only [doReserveRawSpecWithStack,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpecWithStack,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hx4, hlen, hptr, hbound, hfits⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  refine hraw.mono_outcome (x, st) (((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R)
    s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    change reserveCap x.cap.toNat x.bs.length x.additional + 1 ≤ 2 ^ 63 at hbound
    simp only [doReserveRawSpecWithStack,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpecWithStack,
      doReserveSpecWithStack,
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
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem_f
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

private theorem stackAt_doReserve_eq_32 (sp : BitVec 64) {hookStack : Nat}
    (hhook : (hookStack + 48) + 64 ≤ 2 ^ 64) :
    stackAt sp ((hookStack + 48) + 64) =
      stackAt sp ((hookStack + 32) + 64) ∗
        memRegion (sp - BitVec.ofNat 64 ((hookStack + 48) + 64)) 16 := by
  have hsplit := ProofLib.stackAt_split_bottom sp ((hookStack + 32) + 64) 16
    (by omega : ((hookStack + 32) + 64) + 16 ≤ 2 ^ 64)
  rw [sepConj_comm]
  simpa only [show ((hookStack + 32) + 64) + 16 = (hookStack + 48) + 64 by omega] using hsplit

private theorem do_reserve_raw1_of_raw32 {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {addr : BitVec 64} {hookStack : Nat}
    (hhook : (hookStack + 48) + 64 ≤ 2 ^ 64)
    (h32 : subroutine_ok P addr (doReserve1Raw32SpecWithStack M A lim hookStack)) :
    subroutine_ok P addr (doReserve1RawSpecWithStack M A lim hookStack) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [doReserve1RawSpecWithStack, stackAt_doReserve_eq_32 _ hhook, sepConj_assoc] at hpre
  let btm := memRegion (s0.sp - BitVec.ofNat 64 ((hookStack + 48) + 64)) 16
  have hpre' : s0.mem ⊨
      (doReserve1Raw32SpecWithStack M A lim hookStack).pre (x, st) s0 ∗ (btm ∗ R) := by
    simp only [doReserve1Raw32SpecWithStack, btm, sepConj_assoc]
    exact hpre
  refine h32.mono_outcome (x, st) (btm ∗ R) s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simpa only [doReserve1Raw32SpecWithStack, doReserve1RawSpecWithStack,
      stackAt_doReserve_eq_32 _ hhook, btm, sepConj_assoc] using hq
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

private theorem do_reserve_raw_of_raw1 {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {addr : BitVec 64} {hookStack : Nat}
    (h1 : subroutine_ok P addr (doReserve1RawSpecWithStack M A lim hookStack)) :
    subroutine_ok P addr (doReserveRawSpecWithStack M A lim hookStack) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [doReserveRawSpecWithStack,
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveRawSpecWithStack,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, _, _, hlen, hptr, hbound, hfits⟩, hmem⟩
  have hpre' : s0.mem ⊨ (doReserve1RawSpecWithStack M A lim hookStack).pre (x, st) s0 ∗ R := by
    simp only [doReserve1RawSpecWithStack, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hlen, hptr, hbound, hfits⟩, hmem⟩
  exact h1.mono_outcome (x, st) R s0 hpc hrun hpre' hsp fun _ hout => hout

private theorem doReserveSpecX_of_doReserveSpec_budget {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {P : Program} {addr : BitVec 64}
    (h4k : subroutine_ok P addr (doReserveSpec M A lim)) :
    subroutine_ok P addr (doReserveSpecX M A lim) := by
  have hstk : ∀ sp : BitVec 64,
      stackAt sp ((extHookStack + 48) + 64) =
        stackAt sp ((allocHookStack + 48) + 64) ∗
          memRegion (sp - BitVec.ofNat 64 ((extHookStack + 48) + 64))
            (((extHookStack + 48) + 64) - ((allocHookStack + 48) + 64)) := by
    intro sp
    have hsplit := ProofLib.stackAt_split_bottom sp ((allocHookStack + 48) + 64)
      (((extHookStack + 48) + 64) - ((allocHookStack + 48) + 64)) (by decide)
    rw [sepConj_comm]
    simpa only [show ((allocHookStack + 48) + 64) +
        (((extHookStack + 48) + 64) - ((allocHookStack + 48) + 64)) =
      (extHookStack + 48) + 64 by decide] using hsplit
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [doReserveSpecX,
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpecX,
    doReserveSpecWithStack,
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpecWithStack,
    doReserveStackX, finishGrowStackX] at hpre
  rw [hstk s0.sp] at hpre
  simp only [sepConj_assoc] at hpre
  let btm := memRegion (s0.sp - BitVec.ofNat 64 ((extHookStack + 48) + 64))
    (((extHookStack + 48) + 64) - ((allocHookStack + 48) + 64))
  have hpre' : s0.mem ⊨ (doReserveSpec M A lim).pre (x, st) s0 ∗ (btm ∗ R) := by
    dsimp only [doReserveSpec,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpec,
      doReserveSpecWithStack,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpecWithStack,
      doReserveStack, finishGrowStack, btm]
    simpa only [sepConj_assoc] using hpre
  refine h4k.mono_outcome (x, st) (btm ∗ R) s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [doReserveSpec, doReserveSpecX,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpec,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpecX,
      doReserveSpecWithStack,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpecWithStack,
      doReserveStack, doReserveStackX, finishGrowStack, finishGrowStackX, btm] at hq ⊢
    rw [hstk s0.sp]
    simpa only [sepConj_assoc] using hq
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

theorem do_reserve_7_raw_ok_ext_4k {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr doReserve7Name)
      (doReserveRawSpec M A lim) :=
  do_reserve_7_raw_of_stride (do_reserve_7_stride_raw_ok_ext_4k hA)

theorem do_reserve_7_ok_ext_4k {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr doReserve7Name)
      (doReserveSpec M A lim) :=
  do_reserve_vec_of_raw (do_reserve_7_raw_ok_ext_4k hA)

theorem do_reserve_2_raw1_ok_ext_4k {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr doReserve2Name)
      (doReserve1RawSpec M A lim) :=
  do_reserve_raw1_of_raw32 (hookStack := allocHookStack) (by decide) (do_reserve_2_raw32_ok_ext_4k hA)

theorem do_reserve_2_raw_ok_ext_4k {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr doReserve2Name)
      (doReserveRawSpec M A lim) :=
  do_reserve_raw_of_raw1 (do_reserve_2_raw1_ok_ext_4k hA)

theorem do_reserve_2_ok_ext_4k {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr doReserve2Name)
      (doReserveSpec M A lim) :=
  do_reserve_vec_of_raw (do_reserve_2_raw_ok_ext_4k hA)

theorem do_reserve_4_raw1_ok_ext_4k {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr doReserve4Name)
      (doReserve1RawSpec M A lim) :=
  do_reserve_raw1_of_raw32 (hookStack := allocHookStack) (by decide) (do_reserve_4_raw32_ok_ext_4k hA)

theorem do_reserve_4_raw_ok_ext_4k {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr doReserve4Name)
      (doReserveRawSpec M A lim) :=
  do_reserve_raw_of_raw1 (do_reserve_4_raw1_ok_ext_4k hA)

theorem do_reserve_4_ok_ext_4k {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr doReserve4Name)
      (doReserveSpec M A lim) :=
  do_reserve_vec_of_raw (do_reserve_4_raw_ok_ext_4k hA)

theorem do_reserve_7_ok_inImage_4k {img : Obj.Image} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContracts4K img.base A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr doReserve7Name)
      ((doReserveSpec M A lim).inImage img) :=
  subroutine_ok_inImage_of_subroutine_ok img (do_reserve_7_ok_ext_4k hA)

theorem do_reserve_2_ok_inImage_4k {img : Obj.Image} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContracts4K img.base A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr doReserve2Name)
      ((doReserveSpec M A lim).inImage img) :=
  subroutine_ok_inImage_of_subroutine_ok img (do_reserve_2_ok_ext_4k hA)

theorem do_reserve_4_ok_inImage_4k {img : Obj.Image} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContracts4K img.base A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr doReserve4Name)
      ((doReserveSpec M A lim).inImage img) :=
  subroutine_ok_inImage_of_subroutine_ok img (do_reserve_4_ok_ext_4k hA)

theorem do_reserve_7_ok_ext_x_4k {img : Obj.Image} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContracts4K img.base A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr doReserve7Name)
      ((doReserveSpecX M A lim).inImage img) :=
  subroutine_ok_inImage_of_subroutine_ok img
    (doReserveSpecX_of_doReserveSpec_budget (do_reserve_7_ok_ext_4k hA))

theorem do_reserve_2_ok_ext_x_4k {img : Obj.Image} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContracts4K img.base A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr doReserve2Name)
      ((doReserveSpecX M A lim).inImage img) :=
  subroutine_ok_inImage_of_subroutine_ok img
    (doReserveSpecX_of_doReserveSpec_budget (do_reserve_2_ok_ext_4k hA))

theorem do_reserve_4_ok_ext_x_4k {img : Obj.Image} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContracts4K img.base A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr doReserve4Name)
      ((doReserveSpecX M A lim).inImage img) :=
  subroutine_ok_inImage_of_subroutine_ok img
    (doReserveSpecX_of_doReserveSpec_budget (do_reserve_4_ok_ext_4k hA))

end LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExtBudget

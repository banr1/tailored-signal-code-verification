/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.CliC.SpqrV1.Alloc.DoReserve
public import LibsignalBinary.Proofs.CliC.SpqrV1.Alloc.DoReservePlaced
public import LibsignalBinary.Proofs.CliC.SpqrV1.Alloc.FinishGrowPlacedBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Placed.GenLsBlock
public import LibsignalBinary.Proofs.SignalSession.Cli.CliSessionCodeSym
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable `RawVecInner::do_reserve_and_handle` Proofs for `CliC`

Threads `RustCliAllocBudget M`, `BudgetLimits`, `FitsEnv`, and `VmPreserved` across `CliC`
`RawVecInner::reserve::do_reserve_and_handle` (Block `561`, calling Block `587`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.CliC.SpqrV1.Alloc.DoReservePlacedBudget

open Arm64 ProofLib
open CryptoVerification (
  LibsignalCodeLoaded LibsignalHooks LibsignalPlacement
  lscall_blk lsmpl sepWP_seq_lscl withLsCodeLoaded
)
open CryptoVerification.RustHeap (RustAlloc allocHookStack vecHeader vecU8At)
open CryptoVerification.LibsignalTripleRatchet (extHookStack reserveCap)
open CryptoVerification.SignalSession (
  lsRustAllocSymCli lsRustNoAllocShimSymCli lsRustReallocSymCli
)
open CryptoVerification.SignalSession.Cli.Placed (
  blkPC_561 blkPl_561 blkPl_587 lsProg_561 lsProg_587
)
open CryptoVerification.SpqrV1.Alloc (
  DoReserveStrideCall adds_cs_eq_false
  reserveCapStride reserveCapStride_one reserveMinCap
  reserve_new_cap_stride_eq spqrHandleErrorSym stackAt_doReserve_gen
)
open CryptoVerification.SpqrV1.Alloc.DoReserveNorm (
  readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre
  readReg64_setPC_pre readReg_setMem_setPC_pre readReg_setPC_pre
  sp_setMem_setPC_pre sp_setPC_pre
)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits FitsEnv FitsEvents RustCliAllocBudget RustLayoutOk
  rustAllocEvents rustCliAllocBudgetSpec rustCliReallocBudgetSpec rustReallocEvents
)
open LibsignalBinary.Proofs.CliC.SpqrV1.Alloc.FinishGrowPlacedBudget (
  finish_grow_8_placed_ok finish_grow_8_placed_ok_x
)
open LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget (
  DoReserveStrideEnv doReserveRawSpec doReserveRawSpecWithStack doReserveRawSpecX
  doReserveSpec doReserveSpecWithStack doReserveSpecX
  doReserveStrideEvents doReserveStrideRawSpec doReserveStrideRawSpecWithStack
  doReserveStrideRawSpecX
  finish_grow_8_ne_cells_of_spec finish_grow_8_zero_cells_of_spec
  fitsEnv_doReserveStride_iff
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  doReserveEvents finishGrowSpecWithStack fitsEnv_doReserve_iff noAllocShimSpec
)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg_setPC_pre readReg_setMem_setPC_pre

theorem do_reserve_7_stride_raw_placed_ok_of_fg_core [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {hookStack : Nat}
    (hhook : (hookStack + 48) + 8 * 8 ≤ 2 ^ 64 := by decide)
    (hfg : subroutine_ok (lsProg_587 H) (blkPl_587).base
      (finishGrowSpecWithStack M A lim hookStack)) :
    subroutine_ok (lsProg_561 H) (blkPl_561).base
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
    apply sepWP_seq_lscl hcl (mid := lsmpl.base 587)
    wp_steps_sync_pool (lsmpl.base 587)
    simp only [State.setMem_setMem]
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) ?_
    intro hcl_m
    have hfg0 := lscall_blk (callerProg := lsProg_561 H)
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
    apply sepWP_seq_lscl hcl (mid := lsmpl.base 587)
    wp_steps_sync_pool (lsmpl.base 587)
    simp only [State.setMem_setMem]
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) ?_
    intro hcl_m
    have hfg1 := lscall_blk (callerProg := lsProg_561 H)
      (finish_grow_8_ne_cells_of_spec hfg) hcl_m
    wp_call hfg1
      (s0.sp - 56#64, cap, ptr, new, align, stride, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64, st)
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    wp_done

theorem do_reserve_7_stride_raw_placed_ok_of_fg [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {hookStack : Nat}
    (hhook : (hookStack + 48) + 8 * 8 ≤ 2 ^ 64 := by decide)
    (_h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hfg : subroutine_ok (lsProg_587 H) (blkPl_587).base
      (finishGrowSpecWithStack M A lim hookStack)) :
    subroutine_ok (lsProg_561 H) (blkPl_561).base
      (withLsCodeLoaded lsmpl (doReserveStrideRawSpecWithStack M A lim hookStack)) :=
  do_reserve_7_stride_raw_placed_ok_of_fg_core hhook hfg

private theorem do_reserve_7_raw_placed_of_stride_cli [LibsignalPlacement] {M : AllocCostModel}
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

private theorem vecU8At_eq_cli (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (if cap = 0#64 then emp
       else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
         memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) := by
  simp only [vecU8At, vecHeader, BitVec.ofNat_eq_ofNat]
  sep_ac_rfl

private theorem do_reserve_vec_placed_of_raw_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {addr : BitVec 64} {hookStack : Nat}
    (hraw : subroutine_ok P addr
      (withLsCodeLoaded lsmpl (doReserveRawSpecWithStack M A lim hookStack))) :
    subroutine_ok P addr
      (withLsCodeLoaded lsmpl (doReserveSpecWithStack M A lim hookStack)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [doReserveSpecWithStack,
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpecWithStack,
    vecU8At_eq_cli, RustCliAllocBudget.repAlloc_live_norm, sepConj_assoc, satisfies_pure_sepConj]
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
      vecU8At_eq_cli, RustCliAllocBudget.repAlloc_live_norm] at hq ⊢
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

theorem do_reserve_7_stride_raw_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H lsRustNoAllocShimSymCli noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSymCli (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSymCli (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_561 H) (blkPl_561).base
      (withLsCodeLoaded lsmpl (doReserveStrideRawSpec M A lim)) :=
  do_reserve_7_stride_raw_placed_ok_of_fg (hookStack := allocHookStack) (by decide) h_panic
    (finish_grow_8_placed_ok hshim halloc hrealloc)

theorem do_reserve_7_stride_raw_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H lsRustNoAllocShimSymCli noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSymCli (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSymCli (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_561 H) (blkPl_561).base
      (withLsCodeLoaded lsmpl (doReserveStrideRawSpecX M A lim)) :=
  do_reserve_7_stride_raw_placed_ok_of_fg (hookStack := extHookStack) (by decide) h_panic
    (finish_grow_8_placed_ok_x hshim halloc hrealloc)

theorem do_reserve_7_raw_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H lsRustNoAllocShimSymCli noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSymCli (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSymCli (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_561 H) (blkPl_561).base
      (withLsCodeLoaded lsmpl (doReserveRawSpec M A lim)) :=
  do_reserve_7_raw_placed_of_stride_cli
    (do_reserve_7_stride_raw_placed_ok h_panic hshim halloc hrealloc)

theorem do_reserve_7_raw_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H lsRustNoAllocShimSymCli noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSymCli (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSymCli (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_561 H) (blkPl_561).base
      (withLsCodeLoaded lsmpl (doReserveRawSpecX M A lim)) :=
  do_reserve_7_raw_placed_of_stride_cli (hookStack := extHookStack)
    (do_reserve_7_stride_raw_placed_ok_x h_panic hshim halloc hrealloc)

theorem do_reserve_7_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H lsRustNoAllocShimSymCli noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSymCli (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSymCli (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_561 H) (blkPl_561).base
      (withLsCodeLoaded lsmpl (doReserveSpec M A lim)) :=
  do_reserve_vec_placed_of_raw_cli
    (do_reserve_7_raw_placed_ok h_panic hshim halloc hrealloc)

theorem do_reserve_7_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H lsRustNoAllocShimSymCli noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSymCli (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSymCli (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_561 H) (blkPl_561).base
      (withLsCodeLoaded lsmpl (doReserveSpecX M A lim)) :=
  do_reserve_vec_placed_of_raw_cli (hookStack := extHookStack)
    (do_reserve_7_raw_placed_ok_x h_panic hshim halloc hrealloc)

end LibsignalBinary.Proofs.CliC.SpqrV1.Alloc.DoReservePlacedBudget

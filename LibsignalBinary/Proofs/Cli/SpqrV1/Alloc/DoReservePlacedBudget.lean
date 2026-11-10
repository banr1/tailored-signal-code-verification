/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Alloc.DoReservePlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.Alloc.FinishGrowPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable `RawVecInner::do_reserve_and_handle [local#7]` (Block `460`)

Proves `do_reserve_2_raw32_placed_ok`, `do_reserve_2_raw1_placed_ok`,
`do_reserve_2_raw_placed_ok`, and `do_reserve_2_placed_ok` (plus `_x` variants) on Block `460`
under `RustCliAllocBudget M` and `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Alloc.DoReservePlacedBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalCodeLoaded LibsignalPlacement lscall_blk lsmpl sepWP_seq_lscl withLsCodeLoaded)
open CryptoVerification.RustHeap (RustAlloc allocHookStack vecHeader vecU8At)
open CryptoVerification.LibsignalTripleRatchet (DoReserveCall extHookStack reserveCap)
open CryptoVerification.SpqrV1.Alloc (
  adds_cs_eq_false reserve_new_cap_eq
  spqrHandleErrorSym spqrRustAllocSym spqrRustNoAllocShimSym spqrRustReallocSym
  stackAt_doReserve32_gen
)
open CryptoVerification.SpqrV1.Alloc.DoReserveNorm (
  readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre
  readReg64_setPC_pre readReg_setMem_setPC_pre readReg_setPC_pre
  sp_setMem_setPC_pre sp_setPC_pre
)
open CryptoVerification.Cli.SpqrV1.Alloc.Placed (blkPC_460 blkPC_465 blkPl_460 blkPl_465)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits FitsEnv FitsEvents RustCliAllocBudget
  rustAllocEvents rustCliAllocBudgetSpec rustCliReallocBudgetSpec rustReallocEvents
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  DoReserveEnv doReserveEvents fitsEnv_doReserve_iff noAllocShimSpec
)
open LibsignalBinary.Proofs.SpqrV1.Alloc.FinishGrowBudget (finishGrow1SpecWithStack)
open LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget (
  doReserve1Raw32Spec doReserve1Raw32SpecWithStack doReserve1Raw32SpecX
  doReserve1RawSpec doReserve1RawSpecWithStack doReserve1RawSpecX
  doReserveRawSpec doReserveRawSpecWithStack doReserveRawSpecX
  doReserveSpec doReserveSpecWithStack doReserveSpecX
  finish_grow_24_ne_cells_of_spec finish_grow_24_zero_cells_of_spec
)
open LibsignalBinary.Proofs.Cli.SpqrV1.Alloc.FinishGrowPlacedBudget (
  finish_grow_2_placed_ok finish_grow_2_placed_ok_x
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg_setPC_pre readReg_setMem_setPC_pre

theorem do_reserve_2_raw32_placed_ok_of_fg [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : (hookStack + 32) + 8 * 8 ≤ 2 ^ 64)
    (_h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hfg : subroutine_ok ((blkPC_465).rebase (blkPl_465).base H)
      (blkPl_465).base
      (finishGrow1SpecWithStack M A lim hookStack)) :
    subroutine_ok ((blkPC_460).rebase (blkPl_460).base H)
      (blkPl_460).base
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
    apply sepWP_seq_lscl hcl (mid := lsmpl.base 465)
    wp_steps_sync_pool (lsmpl.base 465)
    simp only [State.setMem_setMem]
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) ?_
    intro hcl_m
    have hfg0 := lscall_blk (callerProg := (blkPC_460).rebase (blkPl_460).base H)
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
    apply sepWP_seq_lscl hcl (mid := lsmpl.base 465)
    wp_steps_sync_pool (lsmpl.base 465)
    simp only [State.setMem_setMem]
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) ?_
    intro hcl_m
    have hfg1 := lscall_blk (callerProg := (blkPC_460).rebase (blkPl_460).base H)
      (finish_grow_24_ne_cells_of_spec hfg) hcl_m
    wp_call hfg1 (s0.sp - 56#64, cap, ptr, new, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64, st)
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    wp_done

/-- Relocatable `do_reserve_and_handle [local#7]` (Block `460`) meets
`withLsCodeLoaded lsmpl (doReserve1Raw32Spec M A lim)`. -/
theorem do_reserve_2_raw32_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_460).rebase (blkPl_460).base H) (blkPl_460).base
      (withLsCodeLoaded lsmpl (doReserve1Raw32Spec M A lim)) :=
  do_reserve_2_raw32_placed_ok_of_fg (hookStack := allocHookStack) (by decide) h_panic
    (finish_grow_2_placed_ok hshim halloc hrealloc)

theorem do_reserve_2_raw32_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_460).rebase (blkPl_460).base H) (blkPl_460).base
      (withLsCodeLoaded lsmpl (doReserve1Raw32SpecX M A lim)) :=
  do_reserve_2_raw32_placed_ok_of_fg (hookStack := extHookStack) (by decide) h_panic
    (finish_grow_2_placed_ok_x hshim halloc hrealloc)

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

/-- Relocatable `do_reserve_and_handle [local#7]` (Block `460`) meets
`withLsCodeLoaded lsmpl (doReserve1RawSpec M A lim)`. -/
theorem do_reserve_2_raw1_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_460).rebase (blkPl_460).base H) (blkPl_460).base
      (withLsCodeLoaded lsmpl (doReserve1RawSpec M A lim)) :=
  do_reserve_raw1_placed_of_raw32 (hookStack := allocHookStack) (by decide)
    (do_reserve_2_raw32_placed_ok h_panic hshim halloc hrealloc)

theorem do_reserve_2_raw1_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_460).rebase (blkPl_460).base H) (blkPl_460).base
      (withLsCodeLoaded lsmpl (doReserve1RawSpecX M A lim)) :=
  do_reserve_raw1_placed_of_raw32 (hookStack := extHookStack) (by decide)
    (do_reserve_2_raw32_placed_ok_x h_panic hshim halloc hrealloc)

/-- Relocatable `do_reserve_and_handle [local#7]` (Block `460`) meets
`withLsCodeLoaded lsmpl (doReserveRawSpec M A lim)`. -/
theorem do_reserve_2_raw_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_460).rebase (blkPl_460).base H) (blkPl_460).base
      (withLsCodeLoaded lsmpl (doReserveRawSpec M A lim)) :=
  do_reserve_raw_placed_of_raw1 (do_reserve_2_raw1_placed_ok h_panic hshim halloc hrealloc)

theorem do_reserve_2_raw_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_460).rebase (blkPl_460).base H) (blkPl_460).base
      (withLsCodeLoaded lsmpl (doReserveRawSpecX M A lim)) :=
  do_reserve_raw_placed_of_raw1 (hookStack := extHookStack)
    (do_reserve_2_raw1_placed_ok_x h_panic hshim halloc hrealloc)

/-- Relocatable `do_reserve_and_handle [local#7]` (Block `460`) meets
`withLsCodeLoaded lsmpl (doReserveSpec M A lim)`. -/
theorem do_reserve_2_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_460).rebase (blkPl_460).base H) (blkPl_460).base
      (withLsCodeLoaded lsmpl (doReserveSpec M A lim)) :=
  do_reserve_vec_placed_of_raw (do_reserve_2_raw_placed_ok h_panic hshim halloc hrealloc)

theorem do_reserve_2_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_460).rebase (blkPl_460).base H) (blkPl_460).base
      (withLsCodeLoaded lsmpl (doReserveSpecX M A lim)) :=
  do_reserve_vec_placed_of_raw (hookStack := extHookStack)
    (do_reserve_2_raw_placed_ok_x h_panic hshim halloc hrealloc)

abbrev doReserve2_raw32_placed_ok_of_fg := @do_reserve_2_raw32_placed_ok_of_fg
abbrev doReserve2_raw32_placed_ok := @do_reserve_2_raw32_placed_ok
abbrev doReserve2_raw32_placed_ok_x := @do_reserve_2_raw32_placed_ok_x
abbrev doReserve2_raw1_placed_ok := @do_reserve_2_raw1_placed_ok
abbrev doReserve2_raw1_placed_ok_x := @do_reserve_2_raw1_placed_ok_x
abbrev doReserve2_raw_placed_ok := @do_reserve_2_raw_placed_ok
abbrev doReserve2_raw_placed_ok_x := @do_reserve_2_raw_placed_ok_x
abbrev doReserve2_placed_ok := @do_reserve_2_placed_ok
abbrev doReserve2_placed_ok_x := @do_reserve_2_placed_ok_x

end LibsignalBinary.Proofs.Cli.SpqrV1.Alloc.DoReservePlacedBudget

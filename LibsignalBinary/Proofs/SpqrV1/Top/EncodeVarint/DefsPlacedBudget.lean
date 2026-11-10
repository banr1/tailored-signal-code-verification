/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.Alloc.FinishGrowBudget
public import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Specification for `spqr::encode_varint` (Block `326`)

Verifies `<alloc::raw_vec::RawVecInner>::finish_grow` (Block `620`) and
`<alloc::raw_vec::RawVec<u8>>::grow_one` (Block `619`) against `growOneU8BudgetSpec`,
and defines the relocatable budget contracts for `spqr::encode_varint` (Block `326`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.DefsPlacedBudget

open Arm64 ProofLib SepProp
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkPC_619 blkPC_620 blkPl_619 blkPl_620
   extract_withLsCodeLoaded libsignalSessionLib ls_subroutine_ok_of_block lscall_blk
   lsmpl lsρ sepWP_seq_lscl withLsCodeLoaded)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalSpqrV1 (GrowOneCall newCapU8)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SpqrV1.Alloc
  (GrowGhost growOneU8SmallStack spqrHandleErrorSym spqrRustAllocSym
   spqrRustNoAllocShimSym spqrRustReallocSym spqr_externAt?_of_mem_623
   spqr_hook_ok_of_mem_623 stackAt_doReserve32_gen)
open CryptoVerification.SpqrV1.Alloc.GrowOneNorm
  (readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre
   readReg64_setPC_pre readReg_setMem_setPC_pre readReg_setPC_pre
   sp_setMem_setPC_pre sp_setPC_pre)
open CryptoVerification.SpqrV1.Top.EncodeVarint
  (subroutine_ok_withEncStepInvPlaced_of_lscl withEncStepInvPlaced)
open CryptoVerification.SpqrV1.Top.Placed (blkPC_326 blkPl_326)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget RustLayoutOk
   rustAllocEvents rustCliAllocBudgetSpec rustCliReallocBudgetSpec rustReallocEvents)
open LibsignalBinary.Heap.IfaceBudgetLemmas
  (rustCliAllocNoOomExternSpecWithStack rustCliReallocNoOomExternSpecWithStack
   subroutine_ok_allocNoOom_externWithStack_of_hookSat
   subroutine_ok_reallocNoOom_externWithStack_of_hookSat)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge
  (fitsEvents_growOneU8_of_fitsEnv growOneU8BudgetSpec growOneU8Env_events growOneU8Events)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (noAllocShimSpec)
open LibsignalBinary.Proofs.SpqrV1.Alloc.FinishGrowBudget
  (FinishGrow1Env finishGrow1AllocSpecG finishGrow1Events finishGrow1ReallocSpecG
   finishGrow1Spec finishGrow1SpecWithStack fitsEnv_finishGrow1_iff memRegion_24
   session2ShimSpecWithStack session2ShimWithStack_of_noAllocShim)
open LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget
  (finish_grow_24_ne_cells_of_spec finish_grow_24_zero_cells_of_spec)
open LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.DefsBudget (spqrEncodeVarintSpecX)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Budget Proofs of In-Image Block `620` (`finish_grow`) and Block `619` (`grow_one`) -/

private theorem getLsbD_63_eq_false {new : BitVec 64} (h : new.toNat < 2 ^ 63) :
    new.getLsbD 63 = false := by
  rw [BitVec.getLsbD_eq_getElem (by decide), BitVec.getElem_eq_testBit_toNat]
  exact Nat.testBit_lt_two_pow h

private theorem getElem_63_eq_false {new : BitVec 64} (h : new.toNat < 2 ^ 63) :
    new[63] = false := by
  rw [BitVec.getElem_eq_testBit_toNat]
  exact Nat.testBit_lt_two_pow h

private theorem beq_zero_eq_false {new : BitVec 64} (h0 : 0 < new.toNat) :
    (new == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  change new.toNat = 0 at ht
  omega

private theorem stackAt_finishGrow32_gen (sp : BitVec 64) {hookStack : Nat}
    (hhook : hookStack + 32 ≤ 2 ^ 64) :
    stackAt sp (hookStack + 32) =
      stackAt (sp - 32#64) hookStack ∗ cells (sp - 32#64) 4 :=
  ProofLib.stackAt_split_cells sp hookStack 4 hhook

private theorem grow_new_cap_u8_eq_local {cap : BitVec 64}
    (h : max (2 * cap.toNat) 8 < 2 ^ 63) :
    (if (8#64).ult (cap <<< 1) = true then cap <<< 1 else 8#64) =
      BitVec.ofNat 64 (max (2 * cap.toNat) 8) := by
  have hsh : (cap <<< 1).toNat = 2 * cap.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    change (cap.toNat * 2) % 2 ^ 64 = 2 * cap.toNat
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  by_cases hc : (8#64).ult (cap <<< 1) = true
  · simp only [hc, ite_true, hsh]
    rw [BitVec.ult_eq_decide, decide_eq_true_eq, hsh] at hc
    change 8 < 2 * cap.toNat at hc
    omega
  · simp only [hc, Bool.false_eq_true, ite_false]
    rw [BitVec.ult_eq_decide, decide_eq_true_eq, hsh] at hc
    change ¬ 8 < 2 * cap.toNat at hc
    change 8 = max (2 * cap.toNat) 8
    omega

private theorem finish_grow_1_placed_of_zero_ne {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {addr : BitVec 64} {hookStack : Nat}
    (hz : subroutine_ok P addr (finishGrow1AllocSpecG M A lim hookStack))
    (hne : subroutine_ok P addr (finishGrow1ReallocSpecG M A lim hookStack)) :
    subroutine_ok P addr (finishGrow1SpecWithStack M A lim hookStack) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  by_cases hcap0 : x.cap = 0#64
  · refine hz.mono_outcome (x, st) R s0 hpc hrun ?_ hsp fun _ hout => hout
    simp only [finishGrow1SpecWithStack, finishGrow1AllocSpecG,
      CryptoVerification.SpqrV1.Alloc.FinishGrow1Call.oldBuf, hcap0, ite_true, emp_sepConj,
      sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hbs0, _, hle, hnew, hlay, hfits⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, trivial, hbs0 trivial, hle, hnew, hlay, hfits⟩, hmem⟩
  · refine hne.mono_outcome (x, st) R s0 hpc hrun ?_ hsp fun _ hout => hout
    simp only [finishGrow1SpecWithStack, finishGrow1ReallocSpecG,
      CryptoVerification.SpqrV1.Alloc.FinishGrow1Call.oldBuf, hcap0, ite_false, sepConj_assoc,
      satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, _, hbs, hle, hnew, hlay, hfits⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, hcap0, hbs, hle, hnew, hlay, hfits⟩, hmem⟩

theorem finish_grow_620_zero_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : hookStack + 32 ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok ((blkPC_620).rebase (blkPl_620).base H)
      (lsρ spqrRustNoAllocShimSym) (session2ShimSpecWithStack hookStack))
    (halloc : subroutine_ok ((blkPC_620).rebase (blkPl_620).base H)
      (lsρ spqrRustAllocSym) (rustCliAllocNoOomExternSpecWithStack M A lim false hookStack)) :
    subroutine_ok ((blkPC_620).rebase (blkPl_620).base H)
      (blkPl_620).base
      (finishGrow1AllocSpecG M A lim hookStack) := by
  unfold finishGrow1AllocSpecG finishGrow1SpecWithStack
  simp only [memRegion_24, stackAt_finishGrow32_gen _ hhook,
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  wp_init x s0
  rcases x with ⟨⟨out, cap, ptr, new, bs⟩, st⟩
  dsimp only at *
  rcases ‹cap = 0#64› with rfl
  rcases ‹bs = []› with rfl
  have hnew_pos : 0 < new.toNat := by assumption
  have hnew_bound : new.toNat + 1 ≤ 2 ^ 63 := by omega
  have hfits_env : FitsEnv M lim st (FinishGrow1Env ⟨out, 0#64, ptr, new, []⟩) := by assumption
  have hfits : FitsEvents M lim st (rustAllocEvents new.toNat 1) := by
    simp only [fitsEnv_finishGrow1_iff, finishGrow1Events, ↓reduceIte] at hfits_env
    exact hfits_env
  have hmsb := getLsbD_63_eq_false (new := new) (by omega)
  have hmsb' := getElem_63_eq_false (new := new) (by omega)
  have hcbz := beq_zero_eq_false hnew_pos
  have hpow : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : RustLayoutOk new.toNat 1 := ⟨⟨hnew_pos, hpow, hnew_bound⟩, by decide⟩
  wp_steps_sync_pool (lsρ spqrRustNoAllocShimSym)
  simp only [State.setMem_setMem]
  wp_call hshim ()
  rw [← A.pool_of_vmPreserved hpost]
  wp_steps_sync_pool (lsρ spqrRustAllocSym)
  simp only [State.setMem_setMem]
  simp only [Bool.false_eq_true, ↓reduceIte] at halloc
  wp_call halloc (new.toNat, 1, st)
  wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
  simp only [State.setMem_setMem]
  apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists (sf_1.readReg64 Reg.x0)
  simp only [finishGrow1Events, ↓reduceIte,
    pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj]
  wp_done

theorem finish_grow_620_ne_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : hookStack + 32 ≤ 2 ^ 64 := by decide)
    (hrealloc : subroutine_ok ((blkPC_620).rebase (blkPl_620).base H)
      (lsρ spqrRustReallocSym) (rustCliReallocNoOomExternSpecWithStack M A lim hookStack)) :
    subroutine_ok ((blkPC_620).rebase (blkPl_620).base H)
      (blkPl_620).base
      (finishGrow1ReallocSpecG M A lim hookStack) := by
  unfold finishGrow1ReallocSpecG finishGrow1SpecWithStack
  simp only [memRegion_24, stackAt_finishGrow32_gen _ hhook,
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  wp_init x s0
  rcases x with ⟨⟨out, cap, ptr, new, bs⟩, st⟩
  dsimp only at *
  have hcap_ne : cap ≠ 0#64 := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat := by assumption
  have hcap_le_new : cap.toNat ≤ new.toNat := by assumption
  have hnew_pos : 0 < new.toNat := by assumption
  have hnew_bound : new.toNat + 1 ≤ 2 ^ 63 := by omega
  have hfits_env : FitsEnv M lim st (FinishGrow1Env ⟨out, cap, ptr, new, bs⟩) := by assumption
  have hfits : FitsEvents M lim st (rustReallocEvents cap.toNat new.toNat 1) := by
    simp only [fitsEnv_finishGrow1_iff, finishGrow1Events, hcap_ne, ↓reduceIte] at hfits_env
    exact hfits_env
  have hcap_pos : 0 < cap.toNat :=
    Nat.pos_of_ne_zero (fun hc => hcap_ne (BitVec.eq_of_toNat_eq hc))
  have hmsb := getLsbD_63_eq_false (new := new) (by omega)
  have hmsb' := getElem_63_eq_false (new := new) (by omega)
  have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap_ne
  have hle_new : bs.length ≤ new.toNat := by omega
  have hpow : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay_old : RustLayoutOk cap.toNat 1 := ⟨⟨hcap_pos, hpow, by omega⟩, by decide⟩
  have hlay : RustLayoutOk new.toNat 1 := ⟨⟨hnew_pos, hpow, hnew_bound⟩, by decide⟩
  wp_steps_sync_pool (lsρ spqrRustReallocSym)
  simp only [State.setMem_setMem]
  wp_call hrealloc (ptr, cap.toNat, 1, new.toNat, bs, st)
  wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
  simp only [State.setMem_setMem]
  apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists (sf.readReg64 Reg.x0)
  simp only [finishGrow1Events, hcap_ne, ↓reduceIte]
  wp_done

theorem finish_grow_620_budget_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_620).rebase (blkPl_620).base H)
      (blkPl_620).base
      (finishGrow1Spec M A lim) :=
  finish_grow_1_placed_of_zero_ne
    (finish_grow_620_zero_placed_ok_of_hooks (hookStack := allocHookStack) (by decide)
      (session2ShimWithStack_of_noAllocShim allocHookStack (spqr_hook_ok_of_mem_623 hshim))
      (subroutine_ok_allocNoOom_externWithStack_of_hookSat halloc spqr_externAt?_of_mem_623))
    (finish_grow_620_ne_placed_ok_of_hooks (hookStack := allocHookStack) (by decide)
      (subroutine_ok_reallocNoOom_externWithStack_of_hookSat hrealloc spqr_externAt?_of_mem_623))

/-- Tight `4192`-byte stack budget contract of `<alloc::raw_vec::RawVec<u8>>::grow_one` (Block `619`). -/
def growOneU8BsBudgetSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (GrowGhost × M.σ) where
  pre := fun ((v, cap, ptr, bs), st) s =>
    ⌜s.readReg64 .x0 = v ∧ bs.length ≤ cap.toNat ∧ ptr ≠ 0#64 ∧
      max (2 * cap.toNat) 8 < 2 ^ 63 ∧
      FitsEvents M lim st (growOneU8Events cap)⌝ ∗
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
    (if cap = 0#64 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ∗
    A.pool lim st s ∗ stackAt s.sp growOneU8SmallStack
  post := fun ((v, cap, _, bs), st) s0 sf =>
    ∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
      (v ↦₆₄ newCapU8 cap) ∗ ((v + 8#64) ↦₆₄ p') ∗
      A.live p' (max (2 * cap.toNat) 8) 1 ∗ (p' ↦ₛ bs) ∗
      memRegion (p' + BitVec.ofNat 64 bs.length) (max (2 * cap.toNat) 8 - bs.length) ∗
      A.pool lim (M.stepEvents (growOneU8Events cap) st) sf ∗
      stackAt s0.sp growOneU8SmallStack

theorem growOneU8_bs_budget_placed_ok_of_fg [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (_h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hfg : subroutine_ok ((blkPC_620).rebase (blkPl_620).base H)
      (blkPl_620).base (finishGrow1Spec M A lim)) :
    subroutine_ok ((blkPC_619).rebase (blkPl_619).base H)
      (blkPl_619).base
      (withLsCodeLoaded lsmpl (growOneU8BsBudgetSpec M A lim)) := by
  unfold withLsCodeLoaded growOneU8BsBudgetSpec growOneU8SmallStack newCapU8
  simp only [stackAt_doReserve32_gen _ (hookStack := allocHookStack) (by decide), sepExists_sepConj_right]
  wp_init x s0
  rcases x with ⟨⟨v, cap, ptr, bs⟩, st⟩
  dsimp only at *
  have hcl : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat := by assumption
  have hnew_lt63 : max (2 * cap.toNat) 8 < 2 ^ 63 := by assumption
  have hfits_ev : FitsEvents M lim st (growOneU8Events cap) := by assumption
  have hnew_eq := grow_new_cap_u8_eq_local hnew_lt63
  let new := BitVec.ofNat 64 (max (2 * cap.toNat) 8)
  have hnew_toNat : new.toNat = max (2 * cap.toNat) 8 := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by omega
  have hnew_pos : 0 < new.toNat := by omega
  have hnew_bound : new.toNat + 1 ≤ 2 ^ 63 := by omega
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hbs_le_cap)
    subst hbs
    have hnew_nat0 : new.toNat = 8 := by simpa using hnew_toNat
    have hfits0 : FitsEvents M lim st (rustAllocEvents 8 1) := by
      simpa only [growOneU8Events, ↓reduceIte] using hfits_ev
    have hfits : FitsEvents M lim st (rustAllocEvents new.toNat 1) := by
      simpa only [hnew_nat0] using hfits0
    rcases hfits0 with ⟨⟨_, henf, hram0, hva0⟩, ⟨_, _, hram1, hva1⟩, _⟩
    have hnew_eq0 : (if (8#64).ult (0#64 <<< 1) = true then 0#64 <<< 1 else 8#64) = new := hnew_eq
    have hmax_eq : max (2 * 0) 8 = new.toNat := by rw [hnew_toNat]; rfl
    simp only [emp_sepConj, pointsToBytes_nil, List.length_nil,
      BitVec.add_zero, BitVec.toNat_ofNat, Nat.zero_mod, Nat.sub_zero,
      growOneU8Events, ↓reduceIte, hmax_eq]
    rw [show rustAllocEvents 8 1 = rustAllocEvents new.toNat 1 from by rw [hnew_nat0]]
    clear hmax_eq
    apply sepWP_seq_lscl hcl (mid := lsmpl.base 620)
    wp_steps_sync_pool (lsmpl.base 620)
    simp only [State.setMem_setMem]
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) ?_
    intro hcl_m
    have hfg0 := lscall_blk (callerProg := (blkPC_619).rebase (blkPl_619).base H)
      (finish_grow_24_zero_cells_of_spec hfg) hcl_m
    wp_call hfg0 (s0.sp - 56#64, 0#64, ptr, new, [], v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64, st)
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    wp_done
  · have hfits : FitsEvents M lim st (rustReallocEvents cap.toNat new.toNat 1) := by
      simpa only [growOneU8Events, hcap0, ↓reduceIte, ← hnew_toNat] using hfits_ev
    simp only [hcap0, growOneU8Events, ↓reduceIte, sepConj_assoc, ← hnew_toNat]
    apply sepWP_seq_lscl hcl (mid := lsmpl.base 620)
    wp_steps_sync_pool (lsmpl.base 620)
    simp only [State.setMem_setMem]
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) ?_
    intro hcl_m
    have hfg1 := lscall_blk (callerProg := (blkPC_619).rebase (blkPl_619).base H)
      (finish_grow_24_ne_cells_of_spec hfg) hcl_m
    wp_call hfg1 (s0.sp - 56#64, cap, ptr, new, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64, st)
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    wp_done

theorem growOneU8_budget_placed_cl_ok_of_bs [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {P : Program} {addr : BitVec 64}
    (hbs : subroutine_ok P addr (withLsCodeLoaded lsmpl (growOneU8BsBudgetSpec M A lim))) :
    subroutine_ok P addr (withLsCodeLoaded lsmpl (growOneU8BudgetSpec M A lim)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  let Frame : SepProp := memRegion (s0.sp - 16384#64) 12192
  have hstack : stackAt s0.sp extHookStack = Frame ∗ stackAt s0.sp growOneU8SmallStack :=
    ProofLib.stackAt_split_bottom s0.sp growOneU8SmallStack 12192 (by decide)
  obtain ⟨hcl, hpre0⟩ := extract_withLsCodeLoaded hpre
  simp only [growOneU8BudgetSpec, BitVec.ofNat_eq_ofNat, sepConj_assoc, satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨⟨hx0, hlen, hptr, hbound, hEnv⟩, hmem⟩
  have hfits : FitsEvents M lim st (growOneU8Events x.cap) :=
    fitsEvents_growOneU8_of_fitsEnv M lim st x hEnv
  have hpre' : s0.mem ⊨ (withLsCodeLoaded lsmpl (growOneU8BsBudgetSpec M A lim)).pre
      ((x.v, x.cap, x.ptr, x.bs), st) s0 ∗ (Frame ∗ R) := by
    dsimp only [withLsCodeLoaded, growOneU8BsBudgetSpec]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, Nat.le_of_eq hlen, hptr, hbound, hfits⟩, ?_⟩
    rw [hstack] at hmem
    by_cases hcap0 : x.cap = 0#64
    · simp only [hcap0, ite_true] at hmem ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
    · simp only [hcap0, ite_false, ← hlen, Nat.sub_self, memRegion_zero, sepConj_emp,
        sepConj_assoc] at hmem ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
  refine hbs.mono_outcome ((x.v, x.cap, x.ptr, x.bs), st) (Frame ∗ R) s0 hpc hrun hpre' hsp
    fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, growOneU8BsBudgetSpec, growOneU8BudgetSpec] at hq ⊢
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨p', ⟨hp', htr⟩, hmem'⟩
    refine ⟨growOneU8Events x.cap, p', ⟨htr, growOneU8Env_events x⟩, hp', ?_⟩
    rw [hstack]
    simp only [hlen] at hmem' ⊢
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem'
  · exact False.elim (not_satisfies_false_sepConj hq)
  · exact False.elim (not_satisfies_false_sepConj hq)
  · exact False.elim (not_satisfies_false_sepConj hq)

theorem growOneU8_budget_placed_cl_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_619).rebase (blkPl_619).base H)
      (blkPl_619).base
      (withLsCodeLoaded lsmpl (growOneU8BudgetSpec M A lim)) :=
  growOneU8_budget_placed_cl_ok_of_bs
    (growOneU8_bs_budget_placed_ok_of_fg h_panic (finish_grow_620_budget_placed_ok hshim halloc hrealloc))

/-! ## 2. Block `326` Caller Contracts -/

/-- `<alloc::raw_vec::RawVec<u8>>::grow_one` (Block `619`) meets
`withLsCodeLoaded lsmpl (growOneU8BudgetSpec M A lim)` on `(blkPC_326).rebase (blkPl_326).base (Rust.withPanics ext)`. -/
def GrowOneU8PlacedOkExt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics ext))
    (lsmpl.base 619)
    (withLsCodeLoaded lsmpl (growOneU8BudgetSpec M A lim))

/-- Step-invariant-wrapped `<alloc::raw_vec::RawVec<u8>>::grow_one` (Block `619`) budget contract anchored at `s0`. -/
def GrowOneU8StepOkExt [LibsignalPlacement] (s0 : State) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics ext))
    (lsmpl.base 619)
    (withEncStepInvPlaced s0 (growOneU8BudgetSpec M A lim))

theorem growOneU8StepOkExt_of_lscl [LibsignalPlacement] {s0 : State} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (h : GrowOneU8PlacedOkExt A lim ext) :
    GrowOneU8StepOkExt s0 A lim ext :=
  subroutine_ok_withEncStepInvPlaced_of_lscl hcl0 h

theorem growOneU8_placed_ok_ext [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    GrowOneU8PlacedOkExt A lim ext :=
  ls_subroutine_ok_of_block
    (callerProg := (blkPC_326).rebase (blkPl_326).base (Rust.withPanics ext))
    (growOneU8_budget_placed_cl_ok h_panic hshim halloc hrealloc)
    (bi := 624) (bj := 624) (by decide) (by decide) (by decide)

/-- `spqr::encode_varint` (Block `326`) meets `withLsCodeLoaded lsmpl (spqrEncodeVarintSpecX A lim)` on
`(blkPC_326).rebase (blkPl_326).base (Rust.withPanics ext)`. -/
def SpqrEncodeVarintPlacedOkExt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics ext))
    (blkPl_326).base
    (withLsCodeLoaded lsmpl (spqrEncodeVarintSpecX A lim))

/-- `spqr::encode_varint` (Block `326`) meets `withLsCodeLoaded lsmpl (spqrEncodeVarintSpecX A lim)`
on `libsignalSessionLib.blockProgram lsmpl 326 (Rust.withPanics ext)`. -/
def SpqrEncodeVarintPlacedOkX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 326 (Rust.withPanics ext))
    (lsmpl.base 326)
    (withLsCodeLoaded lsmpl (spqrEncodeVarintSpecX A lim))

abbrev EncodeVarintPlacedOkX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  SpqrEncodeVarintPlacedOkX A lim ext

end LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.DefsPlacedBudget

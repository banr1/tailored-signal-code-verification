/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneRustAllocPlaced
public import LibsignalBinary.Proofs.SpqrV1.Alloc.FinishGrowBudget
public import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget
public import LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Sysroot `RawVec::grow_one` (Blocks 619..622)

Proves `RustCliAllocBudget M` `[LibsignalPlacement]` contracts for blocks 620
(`finish_grow [liballoc]`), 622 (`finish_grow [libstd]`), 619 (`RawVec<u8>::grow_one`),
and 621 (`RawVec<Vec<u8>>::grow_one`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneRustAllocPlacedBudget

open Arm64 ProofLib SepProp
open CryptoVerification (
  IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement LsBlockBound
  blkPC_619 blkPC_620 blkPC_621 blkPC_622
  blkPl_619 blkPl_620 blkPl_621 blkPl_622
  extract_withLsCodeLoaded instIsLsBlockProg_619 instIsLsBlockProg_621
  libsignalSessionLib ls_subroutine_ok_cl_of_block ls_subroutine_ok_of_block
  lscall_blk lscall_blk_cl lsmpl lsρ sepWP_seq_lscl withLsCl withLsCodeLoaded withMemEq
)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalSpqrV1 (GrowOneCall newCapU8)
open CryptoVerification.LibsignalTripleRatchet (FinishGrowCall extHookStack withLsCodeRoLoaded)
open CryptoVerification.SpqrV1.Alloc (
  FinishGrow1Call GrowGhost
  spqrHandleErrorSym spqrRustAllocSym spqrRustNoAllocShimSym spqrRustReallocSym
  spqr_externAt?_of_mem_623 spqr_hook_ok_of_mem_623
  stackAt_doReserve32_gen subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded_alloc
)
open CryptoVerification.SpqrV1.Alloc.GrowOneNorm (
  readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre
  readReg64_setPC_pre readReg_setMem_setPC_pre readReg_setPC_pre
  sp_setMem_setPC_pre sp_setPC_pre
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents
  RustCliAllocBudget RustLayoutOk
  rustAllocEvents rustCliAllocBudgetSpec rustCliReallocBudgetSpec rustReallocEvents
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  rustCliAllocNoOomExternSpecWithStack rustCliReallocNoOomExternSpecWithStack
  subroutine_ok_allocNoOom_externWithStack_of_hookSat
  subroutine_ok_reallocNoOom_externWithStack_of_hookSat
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (
   fitsEvents_growOneU8_of_fitsEnv fitsEvents_rawVecGrow_of_fitsEnv
  growOneU8BudgetSpec growOneU8Env_events growOneU8Events
  growOneVecU8BudgetSpec rawVecGrowEnv_events rawVecGrowEvents
  rawVecGrowBudgetSpec rawVecNewCap
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  FinishGrowEnv finishGrowEvents finishGrowSpec finishGrowSpecWithStack finishGrowSpecX
  fitsEnv_finishGrow_iff noAllocShimSpec
)
open LibsignalBinary.Proofs.SpqrV1.Alloc.FinishGrowBudget (
  FinishGrow1Env finishGrow1AllocSpecG finishGrow1Events finishGrow1ReallocSpecG
  finishGrow1Spec finishGrow1SpecWithStack finishGrow1SpecX fitsEnv_finishGrow1_iff
  finishGrow8AllocSpecG finishGrow8ReallocSpecG
  memRegion_24 session2ShimSpecWithStack session2ShimWithStack_of_noAllocShim
)
open LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget (
  finish_grow_24_ne_cells_of_spec finish_grow_24_zero_cells_of_spec
)
open LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneBudget (
  GrowOneStrideEnv finishGrow8NeCellsSpecG finishGrow8ZeroCellsSpecG
  finish_grow_8_ne_cells_of_fg8 finish_grow_8_zero_cells_of_fg8
  fitsEnv_growOneStride_iff growOneStrideBsSpec growOneStrideBsSpecWithStack
  growOneStrideEvents growOneStrideFullSpec growOneStrideFullSpecWithStack
  grow_one_stride_full_placed_of_bs
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Arithmetic and Stack Helpers -/

private theorem umulh_stride_eq_zero {new stride : BitVec 64}
    (h : new.toNat * stride.toNat < 2 ^ 64) :
    BitVec.truncate 64 ((BitVec.zeroExtend 128 stride * BitVec.zeroExtend 128 new) >>> 64) =
      0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_mul,
    BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  have hs : stride.toNat < 2 ^ 128 := lt_trans stride.isLt (by decide)
  have hn : new.toNat < 2 ^ 128 := lt_trans new.isLt (by decide)
  rw [Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hn]
  have hprod : stride.toNat * new.toNat < 2 ^ 64 := by rw [Nat.mul_comm]; exact h
  rw [Nat.mod_eq_of_lt (lt_trans hprod (by decide)), Nat.shiftRight_eq_div_pow,
    Nat.div_eq_of_lt hprod]
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

private theorem beq_mul_stride_zero_eq_false {new stride : BitVec 64}
    (h0 : 0 < new.toNat * stride.toNat) (hlt : new.toNat * stride.toNat < 2 ^ 64) :
    (stride * new == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [mul_stride_toNat hlt] at ht
  change new.toNat * stride.toNat = 0 at ht
  omega

private theorem hi_stride_eq_false {new stride align : BitVec 64}
    (h : new.toNat * stride.toNat + align.toNat ≤ 2 ^ 63) :
    (9223372036854775808#64 - align).ult (stride * new) = false := by
  have hlt : new.toNat * stride.toNat < 2 ^ 64 := by omega
  have hal : align.toNat ≤ 2 ^ 63 := by omega
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, not_lt]
  rw [mul_stride_toNat hlt, BitVec.toNat_sub_of_le]
  · change new.toNat * stride.toNat ≤ 2 ^ 63 - align.toNat
    omega
  · rw [BitVec.le_def]
    exact hal

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

private theorem stackAt_finishGrow_gen (sp : BitVec 64) {hookStack : Nat}
    (hhook : hookStack + 48 ≤ 2 ^ 64) :
    stackAt sp (hookStack + 48) =
      stackAt (sp - 48#64) hookStack ∗ cells (sp - 48#64) 6 :=
  ProofLib.stackAt_split_cells sp hookStack 6 hhook

private theorem stackAt_finishGrow32_gen (sp : BitVec 64) {hookStack : Nat}
    (hhook : hookStack + 32 ≤ 2 ^ 64) :
    stackAt sp (hookStack + 32) =
      stackAt (sp - 32#64) hookStack ∗ cells (sp - 32#64) 4 :=
  ProofLib.stackAt_split_cells sp hookStack 4 hhook

private theorem stackAt_growOne_gen (sp : BitVec 64) {hookStack : Nat}
    (hhook : (hookStack + 48) + 8 * 8 ≤ 2 ^ 64) :
    stackAt sp ((hookStack + 48) + 64) =
      stackAt (sp - 64#64) (hookStack + 48) ∗ cells (sp - 64#64) 8 :=
  ProofLib.stackAt_split_cells sp (hookStack + 48) 8 hhook

private theorem grow_new_cap_eq_local {cap : BitVec 64}
    (h : max (2 * cap.toNat) 4 < 2 ^ 63) :
    (if (4#64).ult (cap <<< 1) = true then cap <<< 1 else 4#64) =
      BitVec.ofNat 64 (max (2 * cap.toNat) 4) := by
  have hsh : (cap <<< 1).toNat = 2 * cap.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    change (cap.toNat * 2) % 2 ^ 64 = 2 * cap.toNat
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have h4 : (4#64 : BitVec 64).toNat = 4 := rfl
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  by_cases hc : (4#64).ult (cap <<< 1) = true
  · simp only [hc, ite_true, hsh]
    rw [BitVec.ult_eq_decide, decide_eq_true_eq, h4, hsh] at hc
    omega
  · simp only [hc, Bool.false_eq_true, ite_false]
    rw [BitVec.ult_eq_decide, decide_eq_true_eq, h4, hsh] at hc
    change 4 = max (2 * cap.toNat) 4
    omega

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

/-! ## Block 620: `finish_grow [liballoc]` (`stride = 1, align = 1`) -/

private theorem finish_grow_1_placed_of_zero_ne {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {addr : BitVec 64} {hookStack : Nat}
    (hz : subroutine_ok P addr (finishGrow1AllocSpecG M A lim hookStack))
    (hne : subroutine_ok P addr (finishGrow1ReallocSpecG M A lim hookStack)) :
    subroutine_ok P addr (finishGrow1SpecWithStack M A lim hookStack) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  by_cases hcap0 : x.cap = 0#64
  · refine hz.mono_outcome (x, st) R s0 hpc hrun ?_ hsp fun _ hout => hout
    simp only [finishGrow1SpecWithStack, finishGrow1AllocSpecG,
      FinishGrow1Call.oldBuf, hcap0, ite_true, emp_sepConj,
      sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hbs0, _, hle, hnew, hlay, hfits⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, trivial, hbs0 trivial, hle, hnew, hlay, hfits⟩, hmem⟩
  · refine hne.mono_outcome (x, st) R s0 hpc hrun ?_ hsp fun _ hout => hout
    simp only [finishGrow1SpecWithStack, finishGrow1ReallocSpecG,
      FinishGrow1Call.oldBuf, hcap0, ite_false, sepConj_assoc,
      satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, _, hbs, hle, hnew, hlay, hfits⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, hcap0, hbs, hle, hnew, hlay, hfits⟩, hmem⟩

private theorem finish_grow_620_zero_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
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

private theorem finish_grow_620_ne_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
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

theorem finish_grow_620_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : hookStack + 32 ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok ((blkPC_620).rebase (blkPl_620).base H)
      (lsρ spqrRustNoAllocShimSym) (session2ShimSpecWithStack hookStack))
    (halloc : subroutine_ok ((blkPC_620).rebase (blkPl_620).base H)
      (lsρ spqrRustAllocSym) (rustCliAllocNoOomExternSpecWithStack M A lim false hookStack))
    (hrealloc : subroutine_ok ((blkPC_620).rebase (blkPl_620).base H)
      (lsρ spqrRustReallocSym) (rustCliReallocNoOomExternSpecWithStack M A lim hookStack)) :
    subroutine_ok ((blkPC_620).rebase (blkPl_620).base H)
      (blkPl_620).base
      (finishGrow1SpecWithStack M A lim hookStack) :=
  finish_grow_1_placed_of_zero_ne
    (finish_grow_620_zero_placed_ok_of_hooks hhook hshim halloc)
    (finish_grow_620_ne_placed_ok_of_hooks hhook hrealloc)

/-- Block 620 (`finish_grow [liballoc]`) meets `finishGrow1Spec M A lim`. -/
theorem finish_grow_620_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_620).rebase (blkPl_620).base H)
      (blkPl_620).base
      (finishGrow1Spec M A lim) :=
  finish_grow_620_placed_ok_of_hooks (hookStack := allocHookStack) (by decide)
    (session2ShimWithStack_of_noAllocShim allocHookStack (spqr_hook_ok_of_mem_623 hshim))
    (subroutine_ok_allocNoOom_externWithStack_of_hookSat halloc spqr_externAt?_of_mem_623)
    (subroutine_ok_reallocNoOom_externWithStack_of_hookSat hrealloc spqr_externAt?_of_mem_623)

theorem finish_grow_620_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_620).rebase (blkPl_620).base H)
      (blkPl_620).base
      (finishGrow1SpecX M A lim) :=
  finish_grow_620_placed_ok_of_hooks (hookStack := extHookStack) (by decide)
    (session2ShimWithStack_of_noAllocShim extHookStack (spqr_hook_ok_of_mem_623 hshim))
    (subroutine_ok_allocNoOom_externWithStack_of_hookSat halloc spqr_externAt?_of_mem_623)
    (subroutine_ok_reallocNoOom_externWithStack_of_hookSat hrealloc spqr_externAt?_of_mem_623)

/-! ## Block 622: `finish_grow [libstd]` (Generic `stride` and `align`) -/

private theorem finish_grow_622_zero_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : hookStack + 48 ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok ((blkPC_622).rebase (blkPl_622).base H)
      (lsρ spqrRustNoAllocShimSym) (session2ShimSpecWithStack hookStack))
    (halloc : subroutine_ok ((blkPC_622).rebase (blkPl_622).base H)
      (lsρ spqrRustAllocSym) (rustCliAllocNoOomExternSpecWithStack M A lim false hookStack)) :
    subroutine_ok ((blkPC_622).rebase (blkPl_622).base H)
      (blkPl_622).base
      (finishGrow8AllocSpecG M A lim hookStack) := by
  unfold finishGrow8AllocSpecG finishGrowSpecWithStack
  simp only [memRegion_24, stackAt_finishGrow_gen _ hhook,
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  wp_init x s0
  rcases x with ⟨⟨out, cap, ptr, new, align, stride, bs⟩, st⟩
  dsimp only at *
  rcases ‹cap = 0#64› with rfl
  rcases ‹bs = []› with rfl
  have hrlay : RustLayoutOk (new.toNat * stride.toNat) align.toNat := by assumption
  rcases hrlay with ⟨⟨hsz_pos, hpow, hbound⟩, hal_le⟩
  have hfits_env : FitsEnv M lim st (FinishGrowEnv ⟨out, 0#64, ptr, new, align, stride, []⟩) := by
    assumption
  have hfits : FitsEvents M lim st (rustAllocEvents (new.toNat * stride.toNat) align.toNat) := by
    simp only [fitsEnv_finishGrow_iff, finishGrowEvents, BitVec.toNat_zero, ↓reduceIte] at hfits_env
    exact hfits_env
  have hlt64 : new.toNat * stride.toNat < 2 ^ 64 := by omega
  have humulh := umulh_stride_eq_zero hlt64
  have hhi := hi_stride_eq_false hbound
  have hcbz := beq_mul_stride_zero_eq_false hsz_pos hlt64
  have hmul : (stride * new).toNat = new.toNat * stride.toNat := mul_stride_toNat hlt64
  have hlay : RustLayoutOk (new.toNat * stride.toNat) align.toNat :=
    ⟨⟨hsz_pos, hpow, hbound⟩, hal_le⟩
  wp_steps_sync_pool (lsρ spqrRustNoAllocShimSym)
  simp only [State.setMem_setMem]
  wp_call hshim ()
  rw [← A.pool_of_vmPreserved hpost]
  wp_steps_sync_pool (lsρ spqrRustAllocSym)
  simp only [State.setMem_setMem]
  simp only [Bool.false_eq_true, ↓reduceIte] at halloc
  wp_call halloc (new.toNat * stride.toNat, align.toNat, st)
  have hmul_bv : stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) :=
    mul_stride_eq_ofNat hlt64
  wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
  simp only [State.setMem_setMem]
  apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists (sf_1.readReg64 Reg.x0)
  simp only [finishGrowEvents, BitVec.toNat_zero, ↓reduceIte,
    pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj]
  wp_done

private theorem finish_grow_622_ne_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : hookStack + 48 ≤ 2 ^ 64 := by decide)
    (hrealloc : subroutine_ok ((blkPC_622).rebase (blkPl_622).base H)
      (lsρ spqrRustReallocSym) (rustCliReallocNoOomExternSpecWithStack M A lim hookStack)) :
    subroutine_ok ((blkPC_622).rebase (blkPl_622).base H)
      (blkPl_622).base
      (finishGrow8ReallocSpecG M A lim hookStack) := by
  unfold finishGrow8ReallocSpecG finishGrowSpecWithStack
  simp only [memRegion_24, stackAt_finishGrow_gen _ hhook,
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  wp_init x s0
  rcases x with ⟨⟨out, cap, ptr, new, align, stride, bs⟩, st⟩
  dsimp only at *
  have hrlay : RustLayoutOk (new.toNat * stride.toNat) align.toNat := by assumption
  rcases hrlay with ⟨⟨hsz_pos, hpow, hbound⟩, hal_le⟩
  have hcap_ne : cap ≠ 0#64 := by assumption
  have hstr_pos : 0 < stride.toNat := by assumption
  have hcap_le_new : cap.toNat ≤ new.toNat := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat * stride.toNat := by assumption
  have hcap_pos : 0 < cap.toNat :=
    Nat.pos_of_ne_zero (fun hc => hcap_ne (BitVec.eq_of_toNat_eq hc))
  have hcap_nat_ne : cap.toNat ≠ 0 := Nat.ne_of_gt hcap_pos
  have hfits_env : FitsEnv M lim st (FinishGrowEnv ⟨out, cap, ptr, new, align, stride, bs⟩) := by
    assumption
  have hfits : FitsEvents M lim st
      (rustReallocEvents (cap.toNat * stride.toNat) (new.toNat * stride.toNat) align.toNat) := by
    simp only [fitsEnv_finishGrow_iff, finishGrowEvents, hcap_nat_ne, ↓reduceIte] at hfits_env
    exact hfits_env
  have hlt64 : new.toNat * stride.toNat < 2 ^ 64 := by omega
  have hcap_le : cap.toNat * stride.toNat ≤ new.toNat * stride.toNat :=
    Nat.mul_le_mul_right stride.toNat hcap_le_new
  have hcap_lt64 : cap.toNat * stride.toNat < 2 ^ 64 := by omega
  have hold_pos : 0 < cap.toNat * stride.toNat := Nat.mul_pos hcap_pos hstr_pos
  have humulh := umulh_stride_eq_zero hlt64
  have hhi := hi_stride_eq_false hbound
  have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap_ne
  have hmul : (stride * new).toNat = new.toNat * stride.toNat := mul_stride_toNat hlt64
  have hmul_cap : (stride * cap).toNat = cap.toNat * stride.toNat := mul_stride_toNat hcap_lt64
  have hle_new : bs.length ≤ new.toNat * stride.toNat := by omega
  have hlay_old : RustLayoutOk (cap.toNat * stride.toNat) align.toNat :=
    ⟨⟨hold_pos, hpow, by omega⟩, hal_le⟩
  have hlay : RustLayoutOk (new.toNat * stride.toNat) align.toNat :=
    ⟨⟨hsz_pos, hpow, hbound⟩, hal_le⟩
  wp_steps_sync_pool (lsρ spqrRustReallocSym)
  simp only [State.setMem_setMem]
  wp_call hrealloc (ptr, cap.toNat * stride.toNat, align.toNat, new.toNat * stride.toNat, bs, st)
  have hmul_bv : stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) :=
    mul_stride_eq_ofNat hlt64
  wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
  simp only [State.setMem_setMem]
  apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists (sf.readReg64 Reg.x0)
  simp only [finishGrowEvents, hcap_nat_ne, ↓reduceIte]
  wp_done

theorem finish_grow_622_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : hookStack + 48 ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok ((blkPC_622).rebase (blkPl_622).base H)
      (lsρ spqrRustNoAllocShimSym) (session2ShimSpecWithStack hookStack))
    (halloc : subroutine_ok ((blkPC_622).rebase (blkPl_622).base H)
      (lsρ spqrRustAllocSym) (rustCliAllocNoOomExternSpecWithStack M A lim false hookStack))
    (hrealloc : subroutine_ok ((blkPC_622).rebase (blkPl_622).base H)
      (lsρ spqrRustReallocSym) (rustCliReallocNoOomExternSpecWithStack M A lim hookStack)) :
    subroutine_ok ((blkPC_622).rebase (blkPl_622).base H)
      (blkPl_622).base
      (finishGrowSpecWithStack M A lim hookStack) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  by_cases hcap0 : x.cap = 0#64
  · refine (finish_grow_622_zero_placed_ok_of_hooks hhook hshim halloc).mono_outcome
      (x, st) R s0 hpc hrun ?_ hsp fun _ hout => hout
    simp only [finishGrowSpecWithStack, finishGrow8AllocSpecG,
      FinishGrowCall.oldBuf, hcap0, ite_true, emp_sepConj, sepConj_assoc,
      satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hbs0, _, hle, hnew, hstr, hlay, hfits⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, trivial, hbs0 trivial, hle, hnew, hstr, hlay, hfits⟩,
      hmem⟩
  · refine (finish_grow_622_ne_placed_ok_of_hooks hhook hrealloc).mono_outcome
      (x, st) R s0 hpc hrun ?_ hsp fun _ hout => hout
    simp only [finishGrowSpecWithStack, finishGrow8ReallocSpecG,
      FinishGrowCall.oldBuf, hcap0, ite_false, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, _, hbs, hle, hnew, hstr, hlay, hfits⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hcap0, hbs, hle, hnew, hstr, hlay, hfits⟩, hmem⟩

/-- Block 622 (`finish_grow [libstd]`) meets `finishGrowSpec M A lim`. -/
theorem finish_grow_622_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_622).rebase (blkPl_622).base H)
      (blkPl_622).base
      (finishGrowSpec M A lim) :=
  finish_grow_622_placed_ok_of_hooks (hookStack := allocHookStack) (by decide)
    (session2ShimWithStack_of_noAllocShim allocHookStack (spqr_hook_ok_of_mem_623 hshim))
    (subroutine_ok_allocNoOom_externWithStack_of_hookSat halloc spqr_externAt?_of_mem_623)
    (subroutine_ok_reallocNoOom_externWithStack_of_hookSat hrealloc spqr_externAt?_of_mem_623)

theorem finish_grow_622_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_622).rebase (blkPl_622).base H)
      (blkPl_622).base
      (finishGrowSpecX M A lim) :=
  finish_grow_622_placed_ok_of_hooks (hookStack := extHookStack) (by decide)
    (session2ShimWithStack_of_noAllocShim extHookStack (spqr_hook_ok_of_mem_623 hshim))
    (subroutine_ok_allocNoOom_externWithStack_of_hookSat halloc spqr_externAt?_of_mem_623)
    (subroutine_ok_reallocNoOom_externWithStack_of_hookSat hrealloc spqr_externAt?_of_mem_623)

/-! ## Block 619: `RawVec<u8>::grow_one` -/

/-- Stack budget `(allocHookStack + 32) + 64` (`4192` B) for `RawVec<u8>::grow_one`. -/
abbrev growOneU8SmallStack : Nat := (allocHookStack + 32) + 64

/-- Prefix-preserving budget contract (`bs.length ≤ cap.toNat`) for `RawVec<u8>::grow_one` at `growOneU8SmallStack`. -/
def growOneU8BsSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
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
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64⌝ ∗
      (v ↦₆₄ newCapU8 cap) ∗ ((v + 8#64) ↦₆₄ p') ∗
      A.live p' (max (2 * cap.toNat) 8) 1 ∗ (p' ↦ₛ bs) ∗
      memRegion (p' + BitVec.ofNat 64 bs.length) (max (2 * cap.toNat) 8 - bs.length)) ∗
    A.pool lim (M.stepEvents (growOneU8Events cap) st) sf ∗
    stackAt s0.sp growOneU8SmallStack

section Block619Proof

attribute [local irreducible] FitsEvents
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg_setPC_pre readReg_setMem_setPC_pre

/-- Block 619 (`RawVec<u8>::grow_one`) meets `withLsCodeLoaded lsmpl (growOneU8BsSpec M A lim)`. -/
theorem growOneU8_bs_placed_ok_of_fg [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (_h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hfg : subroutine_ok ((blkPC_620).rebase (blkPl_620).base H)
      (blkPl_620).base (finishGrow1Spec M A lim)) :
    subroutine_ok ((blkPC_619).rebase (blkPl_619).base H)
      (blkPl_619).base
      (withLsCodeLoaded lsmpl (growOneU8BsSpec M A lim)) := by
  unfold withLsCodeLoaded growOneU8BsSpec growOneU8SmallStack newCapU8
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
    have hfits : FitsEvents M lim st (rustAllocEvents new.toNat 1) := by
      simpa only [growOneU8Events, ↓reduceIte, hnew_nat0] using hfits_ev
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
    have htr : sf.trace = s0.trace := ‹sf.trace = _›.trans (by simp [wp_norm, arm64_norm])
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    wp_done
  · have hfits : FitsEvents M lim st (rustReallocEvents cap.toNat new.toNat 1) := by
      simpa only [growOneU8Events, hcap0, ↓reduceIte, ← hnew_toNat] using hfits_ev
    simp only [hcap0, growOneU8Events, ↓reduceIte, sepConj_assoc]
    have hsub_eq : max (2 * cap.toNat) 8 - bs.length = new.toNat - bs.length := by
      rw [hnew_toNat]
    have hmax_eq : max (2 * cap.toNat) 8 = new.toNat := by
      rw [hnew_toNat]
    rw [hsub_eq, hmax_eq]
    clear hsub_eq hmax_eq
    apply sepWP_seq_lscl hcl (mid := lsmpl.base 620)
    wp_steps_sync_pool (lsmpl.base 620)
    simp only [State.setMem_setMem]
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) ?_
    intro hcl_m
    have hfg1 := lscall_blk (callerProg := (blkPC_619).rebase (blkPl_619).base H)
      (finish_grow_24_ne_cells_of_spec hfg) hcl_m
    wp_call hfg1 (s0.sp - 56#64, cap, ptr, new, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64, st)
    have htr : sf.trace = s0.trace := ‹sf.trace = _›.trans (by simp [wp_norm, arm64_norm])
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    wp_done

end Block619Proof

theorem growOneU8_placed_cl_ok_of_bs [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {P : Program} {addr : BitVec 64}
    (hbs : subroutine_ok P addr (withLsCodeLoaded lsmpl (growOneU8BsSpec M A lim))) :
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
  have hpre' : s0.mem ⊨ (withLsCodeLoaded lsmpl (growOneU8BsSpec M A lim)).pre
      ((x.v, x.cap, x.ptr, x.bs), st) s0 ∗ (Frame ∗ R) := by
    dsimp only [withLsCodeLoaded, growOneU8BsSpec]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, Nat.le_of_eq hlen, hptr, hbound, hfits⟩, ?_⟩
    rw [hstack] at hmem
    by_cases hcap0 : x.cap = 0#64
    · simp only [hcap0, ite_true] at hmem ⊢
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
    · simp only [hcap0, ite_false, ← hlen, Nat.sub_self, memRegion_zero, sepConj_emp,
        sepConj_assoc] at hmem ⊢
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  refine hbs.mono_outcome ((x.v, x.cap, x.ptr, x.bs), st) (Frame ∗ R) s0 hpc hrun hpre' hsp
    fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, growOneU8BsSpec, growOneU8BudgetSpec] at hq ⊢
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨p', htr, hp', hmem'⟩
    refine ⟨growOneU8Events x.cap, p', ⟨htr, growOneU8Env_events x⟩, hp', ?_⟩
    rw [hstack]
    simp only [hlen] at hmem' ⊢
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem'
  · exact False.elim (not_satisfies_false_sepConj hq)
  · exact False.elim (not_satisfies_false_sepConj hq)
  · exact False.elim (not_satisfies_false_sepConj hq)

theorem growOneU8_placed_cl_ok_of_fg [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hfg : subroutine_ok ((blkPC_620).rebase (blkPl_620).base H)
      (blkPl_620).base (finishGrow1Spec M A lim)) :
    subroutine_ok ((blkPC_619).rebase (blkPl_619).base H)
      (blkPl_619).base
      (withLsCodeLoaded lsmpl (growOneU8BudgetSpec M A lim)) :=
  growOneU8_placed_cl_ok_of_bs (growOneU8_bs_placed_ok_of_fg h_panic hfg)

/-- Block 619 (`RawVec<u8>::grow_one`) meets `withLsCodeLoaded lsmpl (growOneU8BudgetSpec M A lim)`. -/
theorem growOneU8_placed_cl_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_619).rebase (blkPl_619).base H)
      (blkPl_619).base
      (withLsCodeLoaded lsmpl (growOneU8BudgetSpec M A lim)) :=
  growOneU8_placed_cl_ok_of_fg h_panic (finish_grow_620_placed_ok hshim halloc hrealloc)

/-- Own-block `blockProgram` contract for block 619 (`growOneU8BudgetSpec M A lim`). -/
theorem growOneU8_blockProgram_cl_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 619 H)
      (lsmpl.base 619)
      (withLsCodeLoaded lsmpl (growOneU8BudgetSpec M A lim)) := by
  rw [← (instIsLsBlockProg_619 H).eq_blockProgram]
  exact growOneU8_placed_cl_ok h_panic hshim halloc hrealloc

/-! ## Block 621: `RawVec<Vec<u8>>::grow_one` -/

section Block621Proof

attribute [local irreducible] FitsEvents
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg_setPC_pre readReg_setMem_setPC_pre

/-- Block 621 (`RawVec<Vec<u8>>::grow_one`) meets `withLsCodeLoaded lsmpl (growOneStrideBsSpec M A lim 24 8)`. -/
theorem growOneVecU8_bs_placed_ok_of_fg [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (_h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hfg : subroutine_ok ((blkPC_622).rebase (blkPl_622).base H)
      (blkPl_622).base (finishGrowSpec M A lim)) :
    subroutine_ok ((blkPC_621).rebase (blkPl_621).base H)
      (blkPl_621).base
      (withLsCodeLoaded lsmpl (growOneStrideBsSpec M A lim 24 8)) := by
  have hfg0_blk : subroutine_ok ((blkPC_622).rebase (blkPl_622).base H)
      (blkPl_622).base (finishGrow8ZeroCellsSpecG M A lim allocHookStack) :=
    finish_grow_8_zero_cells_of_fg8 (hookStack := allocHookStack) hfg
  have hfg1_blk : subroutine_ok ((blkPC_622).rebase (blkPl_622).base H)
      (blkPl_622).base (finishGrow8NeCellsSpecG M A lim allocHookStack) :=
    finish_grow_8_ne_cells_of_fg8 (hookStack := allocHookStack) hfg
  unfold withLsCodeLoaded growOneStrideBsSpec growOneStrideBsSpecWithStack
  simp only [stackAt_growOne_gen _ (by decide : (allocHookStack + 48) + 8 * 8 ≤ 2 ^ 64)]
  cells_unfold
  wp_init x s0
  rcases x with ⟨⟨v, cap, ptr, bs⟩, st⟩
  dsimp only at *
  have hcl : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hbs_le : bs.length ≤ cap.toNat * 24 := by assumption
  have hbound : max (2 * cap.toNat) 4 * 24 + 8 ≤ 2 ^ 63 := by omega
  have hfits_env : FitsEnv M lim st (GrowOneStrideEnv cap 24 8) := by assumption
  have hnew_lt63 : max (2 * cap.toNat) 4 < 2 ^ 63 := by omega
  have hnew_eq := grow_new_cap_eq_local hnew_lt63
  let new := BitVec.ofNat 64 (max (2 * cap.toNat) 4)
  have hnew_toNat : new.toNat = max (2 * cap.toNat) 4 := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by omega
  have hnew_pos : 0 < new.toNat := by omega
  have hpow : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have hc0 : (0#64 : BitVec 64).toNat = 0 := rfl
    have hm4 : max (2 * 0) 4 = 4 := rfl
    rw [hc0] at hbs_le hnew_toNat
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hbs
    have hfits : FitsEvents M lim st (rustAllocEvents (new.toNat * 24) 8) := by
      rw [fitsEnv_growOneStride_iff] at hfits_env
      simpa only [growOneStrideEvents, ↓reduceIte, hnew_toNat, hm4] using hfits_env
    have hnew_eq0 : (if (4#64).ult (0#64 <<< 1) = true then 0#64 <<< 1 else 4#64) = new := hnew_eq
    have hmul_eq : max (2 * 0) 4 * 24 = new.toNat * 24 := by rw [hnew_toNat]
    simp only [ite_true, emp_sepConj, pointsToBytes_nil, List.length_nil,
      BitVec.add_zero, BitVec.toNat_ofNat, Nat.zero_mod, Nat.sub_zero,
      growOneStrideEvents, hmul_eq]
    apply sepWP_seq_lscl hcl (mid := lsmpl.base 622)
    wp_steps_sync_pool (lsmpl.base 622)
    simp only [State.setMem_setMem]
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) ?_
    intro hcl_m
    have hfg0 := lscall_blk (callerProg := (blkPC_621).rebase (blkPl_621).base H) hfg0_blk hcl_m
    wp_call hfg0 (s0.sp - 56#64, 0#64, ptr, new, 8#64, 24#64, [],
      v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64, st)
    have htr : sf.trace = s0.trace := ‹sf.trace = _›.trans (by simp [wp_norm, arm64_norm])
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    wp_done
  · have hfits : FitsEvents M lim st (rustReallocEvents (cap.toNat * 24) (new.toNat * 24) 8) := by
      rw [fitsEnv_growOneStride_iff] at hfits_env
      simpa only [growOneStrideEvents, hcap0, ↓reduceIte, hnew_toNat] using hfits_env
    simp only [hcap0, ite_false, growOneStrideEvents, sepConj_assoc]
    rw [← hnew_toNat]
    apply sepWP_seq_lscl hcl (mid := lsmpl.base 622)
    wp_steps_sync_pool (lsmpl.base 622)
    simp only [State.setMem_setMem]
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) ?_
    intro hcl_m
    have hfg1 := lscall_blk (callerProg := (blkPC_621).rebase (blkPl_621).base H) hfg1_blk hcl_m
    wp_call hfg1 (s0.sp - 56#64, cap, ptr, new, 8#64, 24#64, bs,
      v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64, st)
    have htr : sf.trace = s0.trace := ‹sf.trace = _›.trans (by simp [wp_norm, arm64_norm])
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    wp_done

end Block621Proof

private theorem growOneStrideEvents_24_8_eq (cap : BitVec 64) :
    growOneStrideEvents cap 24 8 = rawVecGrowEvents 24 4 8 cap := rfl

theorem growOneVecU8_placed_cl_ok_of_full [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {addr : BitVec 64}
    (hfull : subroutine_ok P addr (withLsCodeLoaded lsmpl (growOneStrideFullSpec M A lim 24 8))) :
    subroutine_ok P addr (withLsCodeLoaded lsmpl (growOneVecU8BudgetSpec M A lim)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  let Frame : SepProp := memRegion (s0.sp - 16384#64) 12176
  have hstack : stackAt s0.sp extHookStack = Frame ∗ stackAt s0.sp ((allocHookStack + 48) + 64) :=
    ProofLib.stackAt_split_bottom s0.sp ((allocHookStack + 48) + 64) 12176 (by decide)
  obtain ⟨hcl, hpre0⟩ := extract_withLsCodeLoaded hpre
  simp only [growOneVecU8BudgetSpec, rawVecGrowBudgetSpec, rawVecNewCap,
    BitVec.ofNat_eq_ofNat, sepConj_assoc, satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨⟨hx0, hlen, hptr, hbound, hEnv⟩, hmem⟩
  have hfits_ev : FitsEvents M lim st (rawVecGrowEvents 24 4 8 x.cap) :=
    fitsEvents_rawVecGrow_of_fitsEnv 24 4 8 M lim st x hEnv
  have hfits_str : FitsEnv M lim st (GrowOneStrideEnv x.cap 24 8) :=
    (fitsEnv_growOneStride_iff x.cap 24 8).mpr (growOneStrideEvents_24_8_eq x.cap ▸ hfits_ev)
  have hpre' : s0.mem ⊨
      (withLsCodeLoaded lsmpl (growOneStrideFullSpec M A lim 24 8)).pre
        ((x.v, x.cap, x.ptr, x.bs), st) s0 ∗ (Frame ∗ R) := by
    dsimp only [withLsCodeLoaded, growOneStrideFullSpec, growOneStrideFullSpecWithStack]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hlen, hptr, hbound, hfits_str⟩, ?_⟩
    rw [hstack] at hmem
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  refine hfull.mono_outcome ((x.v, x.cap, x.ptr, x.bs), st) (Frame ∗ R) s0 hpc hrun hpre' hsp
    fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, growOneStrideFullSpec, growOneStrideFullSpecWithStack,
      growOneVecU8BudgetSpec, rawVecGrowBudgetSpec, rawVecNewCap] at hq ⊢
    simp only [BitVec.ofNat_eq_ofNat, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨p', htr, ⟨hp', halign⟩, hmem'⟩
    refine ⟨rawVecGrowEvents 24 4 8 x.cap, p', ⟨htr, rawVecGrowEnv_events 24 4 8 x⟩,
      ⟨hp', halign⟩, ?_⟩
    rw [hstack]
    rw [growOneStrideEvents_24_8_eq] at hmem'
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem'
  · exact False.elim (not_satisfies_false_sepConj hq)
  · exact False.elim (not_satisfies_false_sepConj hq)
  · exact False.elim (not_satisfies_false_sepConj hq)

theorem growOneVecU8_placed_cl_ok_of_fg [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hfg : subroutine_ok ((blkPC_622).rebase (blkPl_622).base H)
      (blkPl_622).base (finishGrowSpec M A lim)) :
    subroutine_ok ((blkPC_621).rebase (blkPl_621).base H)
      (blkPl_621).base
      (withLsCodeLoaded lsmpl (growOneVecU8BudgetSpec M A lim)) :=
  growOneVecU8_placed_cl_ok_of_full
    (grow_one_stride_full_placed_of_bs (growOneVecU8_bs_placed_ok_of_fg h_panic hfg))

/-- Block 621 (`RawVec<Vec<u8>>::grow_one`) meets `withLsCodeLoaded lsmpl (growOneVecU8BudgetSpec M A lim)`. -/
theorem growOneVecU8_placed_cl_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_621).rebase (blkPl_621).base H)
      (blkPl_621).base
      (withLsCodeLoaded lsmpl (growOneVecU8BudgetSpec M A lim)) :=
  growOneVecU8_placed_cl_ok_of_fg h_panic (finish_grow_622_placed_ok hshim halloc hrealloc)

/-- Own-block `blockProgram` contract for block 621 (`growOneVecU8BudgetSpec M A lim`). -/
theorem growOneVecU8_blockProgram_cl_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 621 H)
      (lsmpl.base 621)
      (withLsCodeLoaded lsmpl (growOneVecU8BudgetSpec M A lim)) := by
  rw [← (instIsLsBlockProg_621 H).eq_blockProgram]
  exact growOneVecU8_placed_cl_ok h_panic hshim halloc hrealloc

/-! ## Cross-Block Caller Transfer Lemmas -/

theorem growOneU8_caller_cl_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    {bi : Nat} [LsBlockBound bi]
    (hi : i < bi := by decide) :
    subroutine_ok callerProg (lsmpl.base 619)
      (withLsCodeLoaded lsmpl (growOneU8BudgetSpec M A lim)) :=
  ls_subroutine_ok_of_block (callerProg := callerProg)
    (growOneU8_placed_cl_ok h_panic hshim halloc hrealloc) hi (by decide) (by decide)

theorem growOneU8_caller_withLsCl_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    {bi : Nat} [LsBlockBound bi]
    (hi : i < bi := by decide) :
    subroutine_ok callerProg (lsmpl.base 619)
      (withLsCl lsmpl (growOneU8BudgetSpec M A lim)) :=
  ls_subroutine_ok_cl_of_block (callerProg := callerProg)
    (growOneU8_placed_cl_ok h_panic hshim halloc hrealloc) hi (by decide) (by decide)

theorem growOneU8_caller_cro_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    {bi : Nat} [LsBlockBound bi]
    (hi : i < bi := by decide) :
    subroutine_ok callerProg (lsmpl.base 619)
      (withLsCodeRoLoaded lsmpl (growOneU8BudgetSpec M A lim)) :=
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded_alloc
    (growOneU8_caller_cl_ok h_panic hshim halloc hrealloc hi)

theorem growOneU8_lscall_blk [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] {m : Memory}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hcl : LibsignalCodeLoaded lsmpl m)
    {bi : Nat} [LsBlockBound bi]
    (hi : i < bi := by decide) :
    subroutine_ok callerProg (lsmpl.base 619)
      (withMemEq m (growOneU8BudgetSpec M A lim)) :=
  lscall_blk_cl (callerProg := callerProg)
    (growOneU8_placed_cl_ok h_panic hshim halloc hrealloc) hcl hi (by decide) (by decide)

theorem growOneVecU8_caller_cl_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    {bi : Nat} [LsBlockBound bi]
    (hi : i < bi := by decide) :
    subroutine_ok callerProg (lsmpl.base 621)
      (withLsCodeLoaded lsmpl (growOneVecU8BudgetSpec M A lim)) :=
  ls_subroutine_ok_of_block (callerProg := callerProg)
    (growOneVecU8_placed_cl_ok h_panic hshim halloc hrealloc) hi (by decide) (by decide)

theorem growOneVecU8_caller_withLsCl_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    {bi : Nat} [LsBlockBound bi]
    (hi : i < bi := by decide) :
    subroutine_ok callerProg (lsmpl.base 621)
      (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)) :=
  ls_subroutine_ok_cl_of_block (callerProg := callerProg)
    (growOneVecU8_placed_cl_ok h_panic hshim halloc hrealloc) hi (by decide) (by decide)

theorem growOneVecU8_caller_cro_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    {bi : Nat} [LsBlockBound bi]
    (hi : i < bi := by decide) :
    subroutine_ok callerProg (lsmpl.base 621)
      (withLsCodeRoLoaded lsmpl (growOneVecU8BudgetSpec M A lim)) :=
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded_alloc
    (growOneVecU8_caller_cl_ok h_panic hshim halloc hrealloc hi)

theorem growOneVecU8_lscall_blk [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] {m : Memory}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hcl : LibsignalCodeLoaded lsmpl m)
    {bi : Nat} [LsBlockBound bi]
    (hi : i < bi := by decide) :
    subroutine_ok callerProg (lsmpl.base 621)
      (withMemEq m (growOneVecU8BudgetSpec M A lim)) :=
  lscall_blk_cl (callerProg := callerProg)
    (growOneVecU8_placed_cl_ok h_panic hshim halloc hrealloc) hcl hi (by decide) (by decide)

end LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneRustAllocPlacedBudget

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.DropDecodeError
import ProofLib.SepLogic.WP.Apply

/-!
# Budget-Threaded Verification of `core::ptr::drop_glue::<prost::error::DecodeError>`

Relocatable per-block verification of `drop_glue::<prost::error::DecodeError>` (block 5) against
`DefsBudget.dropDecodeErrorSpecGen`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Prost.DropDecodeErrorBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget RustLayoutOk
   rustCliDeallocBudgetSpec rustDeallocEvents)
open CryptoVerification
  (LibsignalHooks LibsignalPlacement lsmpl blkPC_4 blkPl_4
   lsRustDeallocSym ls_hook_ok_of_mem lsρ subroutine_ok_withLsCodeLoaded_of_plain)
open CryptoVerification.RustHeap
  (LayoutOk allocHookStack vecAt vecBuf vecHeader vecOf)
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap decodeErrorAt decodeErrorAtStackLen extHookStack)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (box72_entails_memRegion kindNoHeap_branch_false layoutOk_72_8 layoutOk_mul32_8 shl5_toNat
   stackAt_dropDecodeErrorGen stackAt_dropDecodeErrorGen_post
   stackAt_dropDecodeErrorGen_tail stackVec_buf_memRegion)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
  (rustDeallocExternSpecWithStack rustDeallocExternWithStack_of_rustDealloc)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
  (DropDecodeErrorEnv DropDecodeErrorPlacedOk DropDecodeErrorPlacedOkX
   dropDecodeErrorSpec dropDecodeErrorSpecGen dropDecodeErrorSpecX)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem drop_decode_error_placed_ok_gen [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {dStack : Nat} (hd : 0x20 + dStack ≤ 2 ^ 64 := by decide)
    (hdealloc : subroutine_ok ((blkPC_4).rebase (blkPl_4).base H) (lsρ lsRustDeallocSym)
      (rustDeallocExternSpecWithStack M A lim dStack)) :
    subroutine_ok ((blkPC_4).rebase (blkPl_4).base H) (blkPl_4).base
      (dropDecodeErrorSpecGen A lim dStack) := by
  simp only [dropDecodeErrorSpecGen, decodeErrorAt, decodeErrorAtStackLen, vecOf, vecAt,
    vecHeader, vecBuf, stackAt_dropDecodeErrorGen hd, sepExists_sepConj_left,
    sepExists_sepConj_right, List.length_replicate, RustCliAllocBudget.repAlloc_live]
  simp only [rustDeallocExternSpecWithStack,
    _root_.LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack] at hdealloc
  wp_init x s0
  rcases x with ⟨e, st⟩
  dsimp only at *
  have hkv : KindNoHeap v_stk_5 := by assumption
  have hbr := kindNoHeap_branch_false hkv
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hlay72 : RustLayoutOk 72 8 := ⟨layoutOk_72_8, by decide⟩
  have h_len_le : v_stk_4 ≤ v_stk_6.toNat := by assumption
  have h_cap_lt : v_stk_6.toNat * 32 < 2 ^ 63 := by omega
  by_cases hcap0 : v_stk_6 = 0
  · subst hcap0
    simp only [ite_true, emp_sepConj]
    wp_steps_sync_pool (lsρ lsRustDeallocSym)
    simp only [State.setMem_setMem]
    apply SepWP.fold (box72_entails_memRegion e 0 v_stk_7 (BitVec.ofNat 64 v_stk_4) v_stk_5)
      (by sep_focus)
    apply SepWP.fold (stackAt_dropDecodeErrorGen_tail hd s0.sp _ _ _ _) (by sep_focus)
    wp_call hdealloc (e, 72, 8, st)
    apply SepWP.fold (Entails.of_eq (stackAt_dropDecodeErrorGen_post hd s0.sp)) (by sep_focus)
    have henv72 : DropDecodeErrorEnv (rustDeallocEvents 72 8) := Or.inl rfl
    wp_done
  · have hcap_beq : (v_stk_6 == 0#64) = false := beq_eq_false_iff_ne.mpr hcap0
    have hshl : (v_stk_6 <<< 5).toNat = v_stk_6.toNat * 32 := shl5_toNat h_cap_lt
    have hlay_vec : LayoutOk (v_stk_6.toNat * 32) 8 := layoutOk_mul32_8 hcap0 h_cap_lt
    rcases hlay_vec with ⟨hvec_pos, _, hvec_max⟩
    have hrlay_vec : RustLayoutOk (v_stk_6.toNat * 32) 8 := ⟨⟨hvec_pos, hpow8, hvec_max⟩, by decide⟩
    have hpos_vec : 0 < v_stk_6.toNat := Nat.pos_of_ne_zero fun h0 =>
      hcap0 (BitVec.eq_of_toNat_eq (by simpa using h0))
    simp only [hcap0, ite_false, stackVec_buf_memRegion h_len_le h_cap_lt]
    wp_steps_sync_pool (lsρ lsRustDeallocSym)
    simp only [State.setMem_setMem]
    wp_call hdealloc (v_stk_7, v_stk_6.toNat * 32, 8, st)
    wp_steps_sync_pool (lsρ lsRustDeallocSym)
    simp only [State.setMem_setMem]
    apply SepWP.fold (box72_entails_memRegion e v_stk_6 v_stk_7 (BitVec.ofNat 64 v_stk_4) v_stk_5)
      (by sep_focus)
    apply SepWP.fold (stackAt_dropDecodeErrorGen_tail hd s0.sp _ _ _ _) (by sep_focus)
    wp_call hdealloc (e, 72, 8, M.stepEvents (rustDeallocEvents (v_stk_6.toNat * 32) 8) st)
    apply SepWP.fold (Entails.of_eq (stackAt_dropDecodeErrorGen_post hd s0.sp)) (by sep_focus)
    rw [← M.stepEvents_append]
    have henv2 : DropDecodeErrorEnv
        (rustDeallocEvents (v_stk_6.toNat * 32) 8 ++ rustDeallocEvents 72 8) :=
      Or.inr ⟨v_stk_6.toNat, hpos_vec, h_cap_lt, rfl⟩
    wp_done

theorem drop_decode_error_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_4).rebase (blkPl_4).base H) (blkPl_4).base
      (dropDecodeErrorSpec A lim) :=
  drop_decode_error_placed_ok_gen (dStack := allocHookStack) (by decide)
    (rustDeallocExternWithStack_of_rustDealloc (by decide) (by decide)
      (ls_hook_ok_of_mem hdealloc))

theorem drop_decode_error_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_4).rebase (blkPl_4).base H) (blkPl_4).base
      (dropDecodeErrorSpecX A lim) :=
  drop_decode_error_placed_ok_gen (dStack := extHookStack) (by decide)
    (rustDeallocExternWithStack_of_rustDealloc (by decide) (by decide)
      (ls_hook_ok_of_mem hdealloc))

theorem dropDecodeError_placedOk [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    DropDecodeErrorPlacedOk A lim H :=
  subroutine_ok_withLsCodeLoaded_of_plain (drop_decode_error_placed_ok hdealloc)

theorem dropDecodeError_placedOkX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    DropDecodeErrorPlacedOkX A lim H :=
  subroutine_ok_withLsCodeLoaded_of_plain (drop_decode_error_placed_ok_x hdealloc)

end LibsignalBinary.Proofs.TripleRatchet.Prost.DropDecodeErrorBudget

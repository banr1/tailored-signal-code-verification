/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.FinishGrowBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Alloc.FetchPlaced
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable `RawVecInner::finish_grow [local#8]` (Block `465`)

Proves `finish_grow_2_placed_ok` and `finish_grow_2_placed_ok_x` on Block `465` under
`RustCliAllocBudget M` and `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Alloc.FinishGrowPlacedBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement lsρ)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SpqrV1.Alloc (
  spqrRustAllocSym spqrRustNoAllocShimSym spqrRustReallocSym
  spqr_externAt?_of_mem spqr_hook_ok_of_mem
)
open CryptoVerification.Cli.SpqrV1.Alloc.Placed (blkPC_465 blkPl_465)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits FitsEnv FitsEvents
  RustCliAllocBudget RustLayoutOk
  rustAllocEvents rustCliAllocBudgetSpec rustCliReallocBudgetSpec rustReallocEvents
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  rustCliAllocNoOomExternSpecWithStack rustCliReallocNoOomExternSpecWithStack
  subroutine_ok_allocNoOom_externWithStack_of_hookSat
  subroutine_ok_reallocNoOom_externWithStack_of_hookSat
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  noAllocShimSpec
)
open LibsignalBinary.Proofs.SpqrV1.Alloc.FinishGrowBudget (
  FinishGrow1Env finishGrow1AllocSpecG finishGrow1Events finishGrow1ReallocSpecG
  finishGrow1Spec finishGrow1SpecWithStack finishGrow1SpecX
  fitsEnv_finishGrow1_iff memRegion_24 session2ShimSpecWithStack
  session2ShimWithStack_of_noAllocShim
)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

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

theorem finish_grow_2_zero_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : hookStack + 32 ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok ((blkPC_465).rebase (blkPl_465).base H)
      (lsρ spqrRustNoAllocShimSym) (session2ShimSpecWithStack hookStack))
    (halloc : subroutine_ok ((blkPC_465).rebase (blkPl_465).base H)
      (lsρ spqrRustAllocSym) (rustCliAllocNoOomExternSpecWithStack M A lim false hookStack)) :
    subroutine_ok ((blkPC_465).rebase (blkPl_465).base H)
      (blkPl_465).base
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

theorem finish_grow_2_ne_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : hookStack + 32 ≤ 2 ^ 64 := by decide)
    (hrealloc : subroutine_ok ((blkPC_465).rebase (blkPl_465).base H)
      (lsρ spqrRustReallocSym) (rustCliReallocNoOomExternSpecWithStack M A lim hookStack)) :
    subroutine_ok ((blkPC_465).rebase (blkPl_465).base H)
      (blkPl_465).base
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

theorem finish_grow_2_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : hookStack + 32 ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok ((blkPC_465).rebase (blkPl_465).base H)
      (lsρ spqrRustNoAllocShimSym) (session2ShimSpecWithStack hookStack))
    (halloc : subroutine_ok ((blkPC_465).rebase (blkPl_465).base H)
      (lsρ spqrRustAllocSym) (rustCliAllocNoOomExternSpecWithStack M A lim false hookStack))
    (hrealloc : subroutine_ok ((blkPC_465).rebase (blkPl_465).base H)
      (lsρ spqrRustReallocSym) (rustCliReallocNoOomExternSpecWithStack M A lim hookStack)) :
    subroutine_ok ((blkPC_465).rebase (blkPl_465).base H)
      (blkPl_465).base
      (finishGrow1SpecWithStack M A lim hookStack) :=
  finish_grow_1_placed_of_zero_ne
    (finish_grow_2_zero_placed_ok_of_hooks hhook hshim halloc)
    (finish_grow_2_ne_placed_ok_of_hooks hhook hrealloc)

theorem finish_grow_2_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_465).rebase (blkPl_465).base H)
      (blkPl_465).base
      (finishGrow1Spec M A lim) :=
  finish_grow_2_placed_ok_of_hooks (hookStack := allocHookStack) (by decide)
    (session2ShimWithStack_of_noAllocShim allocHookStack (spqr_hook_ok_of_mem hshim))
    (subroutine_ok_allocNoOom_externWithStack_of_hookSat halloc spqr_externAt?_of_mem)
    (subroutine_ok_reallocNoOom_externWithStack_of_hookSat hrealloc spqr_externAt?_of_mem)

theorem finish_grow_2_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_465).rebase (blkPl_465).base H)
      (blkPl_465).base
      (finishGrow1SpecX M A lim) :=
  finish_grow_2_placed_ok_of_hooks (hookStack := extHookStack) (by decide)
    (session2ShimWithStack_of_noAllocShim extHookStack (spqr_hook_ok_of_mem hshim))
    (subroutine_ok_allocNoOom_externWithStack_of_hookSat halloc spqr_externAt?_of_mem)
    (subroutine_ok_reallocNoOom_externWithStack_of_hookSat hrealloc spqr_externAt?_of_mem)

abbrev finishGrow2_placed_ok_of_hooks := @finish_grow_2_placed_ok_of_hooks
abbrev finishGrow2_placed_ok := @finish_grow_2_placed_ok
abbrev finishGrow2_placed_ok_x := @finish_grow_2_placed_ok_x

end LibsignalBinary.Proofs.Cli.SpqrV1.Alloc.FinishGrowPlacedBudget

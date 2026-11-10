/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.FinishGrow
public import LibsignalBinary.Proofs.Cli.SpqrV1.Alloc.FetchPlaced
import ProofLib.SepLogic.WPp

/-!
# Relocatable `RawVecInner::finish_grow [local#8]` (Block `465`)

Proves `finish_grow_2_placed_ok` and `finish_grow_2_placed_ok_x` on Block `465` under
`[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.Cli.SpqrV1.Alloc

open Arm64 ProofLib CryptoVerification.RustHeap
  CryptoGames.LibsignalSession CryptoVerification.LibsignalTripleRatchetRepr
  CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
  CryptoVerification.SpqrV1.Alloc
  CryptoVerification.Cli.SpqrV1.Alloc.Placed

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

def finishGrow1AllocSpecG (A : RustAlloc) (hookStack : Nat) : Spec FinishGrow1Call :=
  { finishGrow1SpecWithStack A hookStack with
    pre := fun x s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
        s.readReg64 .x3 = x.new ∧ x.cap = 0#64 ∧ x.bs = [] ∧
        x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ x.new.toNat + 1 ≤ 2 ^ 63⌝ ∗
      memRegion x.out 24 ∗ A.pool ∗ stackAt s.sp (hookStack + 32) }

def finishGrow1ReallocSpecG (A : RustAlloc) (hookStack : Nat) : Spec FinishGrow1Call :=
  { finishGrow1SpecWithStack A hookStack with
    pre := fun x s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
        s.readReg64 .x3 = x.new ∧ x.cap ≠ 0#64 ∧ x.bs.length ≤ x.cap.toNat ∧
        x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ x.new.toNat + 1 ≤ 2 ^ 63⌝ ∗
      memRegion x.out 24 ∗
      A.live x.ptr x.cap.toNat 1 ∗ (x.ptr ↦ₛ x.bs) ∗
      memRegion (x.ptr + BitVec.ofNat 64 x.bs.length) (x.cap.toNat - x.bs.length) ∗
      A.pool ∗ stackAt s.sp (hookStack + 32) }

private theorem finish_grow_1_placed_of_zero_ne {A : RustAlloc} {P : Program} {addr : BitVec 64}
    {hookStack : Nat}
    (hz : subroutine_ok P addr (finishGrow1AllocSpecG A hookStack))
    (hne : subroutine_ok P addr (finishGrow1ReallocSpecG A hookStack)) :
    subroutine_ok P addr (finishGrow1SpecWithStack A hookStack) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  by_cases hcap0 : x.cap = 0#64
  · refine hz.mono_outcome x R s0 hpc hrun ?_ hsp fun _ hout => hout
    simp only [finishGrow1SpecWithStack, finishGrow1AllocSpecG,
      FinishGrow1Call.oldBuf, hcap0, ite_true, emp_sepConj, sepConj_assoc,
      satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hbs0, _, hle, hnew, hlay⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, trivial, hbs0 trivial, hle, hnew, hlay⟩, hmem⟩
  · refine hne.mono_outcome x R s0 hpc hrun ?_ hsp fun _ hout => hout
    simp only [finishGrow1SpecWithStack, finishGrow1ReallocSpecG,
      FinishGrow1Call.oldBuf, hcap0, ite_false, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, _, hbs, hle, hnew, hlay⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, hcap0, hbs, hle, hnew, hlay⟩, hmem⟩

theorem finish_grow_2_zero_placed_ok_of_hooks [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : hookStack + 32 ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok ((blkPC_465).rebase (blkPl_465).base H)
      (lsρ spqrRustNoAllocShimSym) (session2ShimSpecWithStack hookStack))
    (halloc : subroutine_ok ((blkPC_465).rebase (blkPl_465).base H)
      (lsρ spqrRustAllocSym) (rustAllocSpecWithStack A hookStack)) :
    subroutine_ok ((blkPC_465).rebase (blkPl_465).base H)
      (blkPl_465).base
      (finishGrow1AllocSpecG A hookStack) := by
  unfold finishGrow1AllocSpecG finishGrow1SpecWithStack
  simp only [memRegion_24, stackAt_finishGrow32_gen _ hhook,
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  wp_init x s0
  obtain ⟨out, cap, ptr, new, bs⟩ := x
  dsimp only at *
  subst cap
  subst bs
  have hnew_pos : 0 < new.toNat := by assumption
  have hnew_bound : new.toNat + 1 ≤ 2 ^ 63 := by omega
  have hmsb := getLsbD_63_eq_false (new := new) (by omega)
  have hmsb' := getElem_63_eq_false (new := new) (by omega)
  have hcbz := beq_zero_eq_false hnew_pos
  have hpow : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk new.toNat 1 := ⟨hnew_pos, hpow, hnew_bound⟩
  wp_steps
  wp_call hshim ()
  wp_steps
  wp_call halloc (new.toNat, 1)
  wp_steps
  wp_if hoom
  · have hoom' : sf_1.readReg64 Reg.x0 ≠ 0 := hoom
    simp only [hoom', ite_false]
    wp_steps
    apply SepWP.instantiate_post_exists 0#64
    apply SepWP.instantiate_post_exists (sf_1.readReg64 Reg.x0)
    simp only [(by decide : (0#64 : BitVec 64) = 1#64 ↔ False), ite_false,
      pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj]
    wp_done
  · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]
    wp_steps
    apply SepWP.instantiate_post_exists 1#64
    apply SepWP.instantiate_post_exists 1#64
    simp only [ite_true, FinishGrow1Call.oldBuf]
    wp_done

theorem finish_grow_2_ne_placed_ok_of_hooks [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : hookStack + 32 ≤ 2 ^ 64 := by decide)
    (hrealloc : subroutine_ok ((blkPC_465).rebase (blkPl_465).base H)
      (lsρ spqrRustReallocSym) (rustReallocExternSpecWithStack A hookStack)) :
    subroutine_ok ((blkPC_465).rebase (blkPl_465).base H)
      (blkPl_465).base
      (finishGrow1ReallocSpecG A hookStack) := by
  unfold finishGrow1ReallocSpecG finishGrow1SpecWithStack
  simp only [memRegion_24, stackAt_finishGrow32_gen _ hhook,
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  wp_init x s0
  obtain ⟨out, cap, ptr, new, bs⟩ := x
  dsimp only at *
  have hcap_ne : cap ≠ 0#64 := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat := by assumption
  have hcap_le_new : cap.toNat ≤ new.toNat := by assumption
  have hnew_pos : 0 < new.toNat := by assumption
  have hnew_bound : new.toNat + 1 ≤ 2 ^ 63 := by omega
  have hcap_pos : 0 < cap.toNat :=
    Nat.pos_of_ne_zero (fun hc => hcap_ne (BitVec.eq_of_toNat_eq hc))
  have hmsb := getLsbD_63_eq_false (new := new) (by omega)
  have hmsb' := getElem_63_eq_false (new := new) (by omega)
  have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap_ne
  have hle_new : bs.length ≤ new.toNat := by omega
  have hpow : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay_old : LayoutOk cap.toNat 1 := ⟨hcap_pos, hpow, by omega⟩
  have hlay : LayoutOk new.toNat 1 := ⟨hnew_pos, hpow, hnew_bound⟩
  wp_steps
  wp_call hrealloc (ptr, cap.toNat, 1, new.toNat, bs)
  wp_steps
  wp_if hoom
  · have hoom' : sf.readReg64 Reg.x0 ≠ 0 := hoom
    simp only [hoom', ite_false]
    wp_steps
    apply SepWP.instantiate_post_exists 0#64
    apply SepWP.instantiate_post_exists (sf.readReg64 Reg.x0)
    simp only [(by decide : (0#64 : BitVec 64) = 1#64 ↔ False), ite_false]
    wp_done
  · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]
    wp_steps
    apply SepWP.instantiate_post_exists 1#64
    apply SepWP.instantiate_post_exists 1#64
    simp only [ite_true, FinishGrow1Call.oldBuf, hcap_ne, ite_false]
    wp_done

theorem finish_grow_2_placed_ok_of_hooks [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : hookStack + 32 ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok ((blkPC_465).rebase (blkPl_465).base H)
      (lsρ spqrRustNoAllocShimSym) (session2ShimSpecWithStack hookStack))
    (halloc : subroutine_ok ((blkPC_465).rebase (blkPl_465).base H)
      (lsρ spqrRustAllocSym) (rustAllocSpecWithStack A hookStack))
    (hrealloc : subroutine_ok ((blkPC_465).rebase (blkPl_465).base H)
      (lsρ spqrRustReallocSym) (rustReallocExternSpecWithStack A hookStack)) :
    subroutine_ok ((blkPC_465).rebase (blkPl_465).base H)
      (blkPl_465).base
      (finishGrow1SpecWithStack A hookStack) :=
  finish_grow_1_placed_of_zero_ne
    (finish_grow_2_zero_placed_ok_of_hooks hhook hshim halloc)
    (finish_grow_2_ne_placed_ok_of_hooks hhook hrealloc)

/-- Relocatable `<alloc::raw_vec::RawVecInner>::finish_grow [local#8]` (Block `465`) meets
`finishGrow1Spec A`. -/
theorem finish_grow_2_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_465).rebase (blkPl_465).base H)
      (blkPl_465).base
      (finishGrow1Spec A) :=
  finish_grow_2_placed_ok_of_hooks (hookStack := allocHookStack) (by decide)
    (session2ShimWithStack_of_noAllocShim allocHookStack (spqr_hook_ok_of_mem hshim))
    (spqr_hook_ok_of_mem halloc)
    (rustReallocExternWithStack_of_rustRealloc (spqr_hook_ok_of_mem hrealloc) (by decide) (by decide))

/-- Relocatable `<alloc::raw_vec::RawVecInner>::finish_grow [local#8]` (Block `465`) meets
`finishGrow1SpecX A`. -/
theorem finish_grow_2_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_465).rebase (blkPl_465).base H)
      (blkPl_465).base
      (finishGrow1SpecX A) :=
  finish_grow_2_placed_ok_of_hooks (hookStack := extHookStack) (by decide)
    (session2ShimWithStack_of_noAllocShim extHookStack (spqr_hook_ok_of_mem hshim))
    (rustAllocWithStack_of_rustAlloc (spqr_hook_ok_of_mem halloc) (by decide) (by decide))
    (rustReallocExternWithStack_of_rustRealloc (spqr_hook_ok_of_mem hrealloc) (by decide) (by decide))

abbrev finishGrow2_placed_ok_of_hooks := @finish_grow_2_placed_ok_of_hooks
abbrev finishGrow2_placed_ok := @finish_grow_2_placed_ok
abbrev finishGrow2_placed_ok_x := @finish_grow_2_placed_ok_x

end CryptoVerification.Cli.SpqrV1.Alloc

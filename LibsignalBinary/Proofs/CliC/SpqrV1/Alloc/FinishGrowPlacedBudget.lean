/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.CliC.SpqrV1.Alloc.FinishGrow
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.CliSessionCodeSym
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Alloc.FinishGrowBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable `RawVecInner::finish_grow` Proofs for `CliC`

Threads `RustCliAllocBudget M`, `BudgetLimits`, `FitsEnv`, and `VmPreserved` across `CliC`
`RawVecInner::finish_grow [local#10]` (Block `587`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.CliC.SpqrV1.Alloc.FinishGrowPlacedBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement lsρ)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchet (
  FinishGrowCall SepWP.instantiate_post_exists extHookStack
)
open CryptoVerification.SignalSession (
  lsRustAllocSymCli lsRustNoAllocShimSymCli lsRustReallocSymCli
)
open CryptoVerification.SignalSession.Cli.Placed (blkPC_587 blkPl_587 lsProg_587)
open CryptoVerification.SpqrV1.Alloc (
  spqr_externAt?_of_mem spqr_hook_ok_of_mem
)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits FitsEnv FitsEvents RustCliAllocBudget RustLayoutOk
  rustAllocEvents rustCliAllocBudgetSpec rustCliReallocBudgetSpec rustReallocEvents
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  rustCliAllocNoOomExternSpecWithStack rustCliReallocNoOomExternSpecWithStack
  subroutine_ok_allocNoOom_externWithStack_of_hookSat
  subroutine_ok_reallocNoOom_externWithStack_of_hookSat
)
open LibsignalBinary.Proofs.SpqrV1.Alloc.FinishGrowBudget (
  finishGrow8AllocSpecG finishGrow8ReallocSpecG memRegion_24
  session2ShimSpecWithStack session2ShimWithStack_of_noAllocShim
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  FinishGrowEnv finishGrowEvents finishGrowSpec finishGrowSpecWithStack
  finishGrowSpecX fitsEnv_finishGrow_iff noAllocShimSpec
)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

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

private theorem stackAt_finishGrow_gen (sp : BitVec 64) {hookStack : Nat}
    (hhook : hookStack + 48 ≤ 2 ^ 64) :
    stackAt sp (hookStack + 48) =
      stackAt (sp - 48#64) hookStack ∗ cells (sp - 48#64) 6 :=
  ProofLib.stackAt_split_cells sp hookStack 6 hhook

theorem finish_grow_8_zero_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {hookStack : Nat}
    (hhook : hookStack + 48 ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok (lsProg_587 H)
      (lsρ lsRustNoAllocShimSymCli) (session2ShimSpecWithStack hookStack))
    (halloc : subroutine_ok (lsProg_587 H)
      (lsρ lsRustAllocSymCli) (rustCliAllocNoOomExternSpecWithStack M A lim false hookStack)) :
    subroutine_ok (lsProg_587 H)
      (blkPl_587).base
      (finishGrow8AllocSpecG M A lim hookStack) := by
  unfold finishGrow8AllocSpecG finishGrowSpecWithStack lsProg_587
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
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSymCli)
  simp only [State.setMem_setMem]
  wp_call hshim ()
  rw [← A.pool_of_vmPreserved hpost]
  wp_steps_sync_pool (lsρ lsRustAllocSymCli)
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

theorem finish_grow_8_ne_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {hookStack : Nat}
    (hhook : hookStack + 48 ≤ 2 ^ 64 := by decide)
    (hrealloc : subroutine_ok (lsProg_587 H)
      (lsρ lsRustReallocSymCli) (rustCliReallocNoOomExternSpecWithStack M A lim hookStack)) :
    subroutine_ok (lsProg_587 H)
      (blkPl_587).base
      (finishGrow8ReallocSpecG M A lim hookStack) := by
  unfold finishGrow8ReallocSpecG finishGrowSpecWithStack lsProg_587
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
  wp_steps_sync_pool (lsρ lsRustReallocSymCli)
  simp only [State.setMem_setMem]
  wp_call hrealloc (ptr, cap.toNat * stride.toNat, align.toNat, new.toNat * stride.toNat, bs, st)
  have hmul_bv : stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) :=
    mul_stride_eq_ofNat hlt64
  wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
  simp only [State.setMem_setMem]
  apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists (sf.readReg64 Reg.x0)
  simp only [finishGrowEvents, hcap_nat_ne, ↓reduceIte]
  wp_done

theorem finish_grow_8_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {hookStack : Nat}
    (hhook : hookStack + 48 ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok (lsProg_587 H)
      (lsρ lsRustNoAllocShimSymCli) (session2ShimSpecWithStack hookStack))
    (halloc : subroutine_ok (lsProg_587 H)
      (lsρ lsRustAllocSymCli) (rustCliAllocNoOomExternSpecWithStack M A lim false hookStack))
    (hrealloc : subroutine_ok (lsProg_587 H)
      (lsρ lsRustReallocSymCli) (rustCliReallocNoOomExternSpecWithStack M A lim hookStack)) :
    subroutine_ok (lsProg_587 H)
      (blkPl_587).base
      (finishGrowSpecWithStack M A lim hookStack) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  by_cases hcap0 : x.cap = 0#64
  · refine (finish_grow_8_zero_placed_ok_of_hooks hhook hshim halloc).mono_outcome
      (x, st) R s0 hpc hrun ?_ hsp fun _ hout => hout
    simp only [finishGrowSpecWithStack, finishGrow8AllocSpecG,
      FinishGrowCall.oldBuf, hcap0, ite_true, emp_sepConj, sepConj_assoc,
      satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hbs0, _, hle, hnew, hstr, hlay, hfits⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, trivial, hbs0 trivial, hle, hnew, hstr, hlay, hfits⟩,
      hmem⟩
  · refine (finish_grow_8_ne_placed_ok_of_hooks hhook hrealloc).mono_outcome
      (x, st) R s0 hpc hrun ?_ hsp fun _ hout => hout
    simp only [finishGrowSpecWithStack, finishGrow8ReallocSpecG,
      FinishGrowCall.oldBuf, hcap0, ite_false, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, _, hbs, hle, hnew, hstr, hlay, hfits⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hcap0, hbs, hle, hnew, hstr, hlay, hfits⟩, hmem⟩

theorem finish_grow_8_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSymCli noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSymCli (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSymCli (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_587 H)
      (blkPl_587).base
      (finishGrowSpec M A lim) :=
  finish_grow_8_placed_ok_of_hooks (hookStack := allocHookStack) (by decide)
    (session2ShimWithStack_of_noAllocShim allocHookStack (spqr_hook_ok_of_mem hshim))
    (subroutine_ok_allocNoOom_externWithStack_of_hookSat halloc spqr_externAt?_of_mem)
    (subroutine_ok_reallocNoOom_externWithStack_of_hookSat hrealloc spqr_externAt?_of_mem)

theorem finish_grow_8_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSymCli noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSymCli (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSymCli (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_587 H)
      (blkPl_587).base
      (finishGrowSpecX M A lim) :=
  finish_grow_8_placed_ok_of_hooks (hookStack := extHookStack) (by decide)
    (session2ShimWithStack_of_noAllocShim extHookStack (spqr_hook_ok_of_mem hshim))
    (subroutine_ok_allocNoOom_externWithStack_of_hookSat halloc spqr_externAt?_of_mem)
    (subroutine_ok_reallocNoOom_externWithStack_of_hookSat hrealloc spqr_externAt?_of_mem)

end LibsignalBinary.Proofs.CliC.SpqrV1.Alloc.FinishGrowPlacedBudget

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.SignalSession.Cli.CliSessionCodeSymD
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.GrowOne.LayoutBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.FinishGrowFsPlaced
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContractsBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Budget-Threaded Relocatable `finish_grow [local#10]` (Block `587`)

Budget-threaded `[LibsignalPlacement]` contracts for `finish_grow [local#10]` (`finishGrowSpecX M A lim`
and `.keepsFs`) on Block `587`, `RustLayoutOk` cell-form corollaries, and cross-block lifts via
`StoreKit.withLsRoCl`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.FinishGrowFsPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoVerification (IsLsBlockProg LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.RustHeap (LayoutOk)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (LibsignalCodeRoLoaded extract_withLsCodeRoLoaded ls_subroutine_ok_rocl_of_block
   sepWP_seq_lscro withLsCodeRoLoaded withLsRoCl)
open CryptoVerification.LibsignalTripleRatchet (FinishGrowCall extHookStack finishGrowStackX)
open CryptoVerification.SignalSession
  (lsRustAllocSymCli lsRustNoAllocShimSymCli lsRustReallocSymCli)
open CryptoVerification.SignalSession.Cli.Placed (blkPC_587 blkPl_587 lsProg_587)
open CryptoVerification.SignalSession.Cli.GrowOne.Helpers (FGCellsGhost)
open CryptoVerification.SignalSession.Cli.MainHops (SpecRefines keepsFs_withLsCodeRoLoaded)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget
   RustLayoutOk VmPreserved rustAllocEvents rustReallocEvents
   rustCliAllocNoOomExternSpecWithStack rustCliReallocNoOomExternSpecWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (FinishGrowEnv finishGrowEvents finishGrowSpecWithStack finishGrowSpecX fitsEnv_finishGrow_iff)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContractsBudget (shimSpecWithStack)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.GrowOne.LayoutBudget
  (FinishGrowNeEnv FinishGrowZeroEnv finishGrowNeCellsSpec finishGrowZeroCellsSpec)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local wp_norm]
  State.fs_writeReg64 State.fs_writeReg32 State.fs_writeVReg128
  State.fs_advancePC State.fs_setPC State.fs_setPState
  State.fs_setMem State.fs_setStatus State.fs_appendTrace

/-! ## 1. Arithmetic & Memory Helpers -/

private theorem umulh_stride_eq_zero_p {new stride : BitVec 64}
    (h : new.toNat * stride.toNat < 2 ^ 64) :
    BitVec.truncate 64
      ((BitVec.zeroExtend 128 stride * BitVec.zeroExtend 128 new) >>> 64) = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_mul,
    BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  have h1 : stride.toNat < 2 ^ 128 := by omega
  have h2 : new.toNat < 2 ^ 128 := by omega
  have hcomm : stride.toNat * new.toNat = new.toNat * stride.toNat := Nat.mul_comm _ _
  have h3 : stride.toNat * new.toNat < 2 ^ 128 := by omega
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3, Nat.shiftRight_eq_div_pow]
  have hdiv : stride.toNat * new.toNat / 2 ^ 64 = 0 := Nat.div_eq_of_lt (by omega)
  rw [hdiv]
  rfl

private theorem mul_stride_toNat_p {new stride : BitVec 64}
    (h : new.toNat * stride.toNat < 2 ^ 64) :
    (stride * new).toNat = new.toNat * stride.toNat := by
  rw [BitVec.toNat_mul, Nat.mul_comm, Nat.mod_eq_of_lt h]

private theorem mul_stride_eq_ofNat_p {new stride : BitVec 64}
    (h : new.toNat * stride.toNat < 2 ^ 64) :
    stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [mul_stride_toNat_p h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

private theorem mul_stride_ne_zero_p {new stride : BitVec 64}
    (h0 : 0 < new.toNat * stride.toNat) (h : new.toNat * stride.toNat < 2 ^ 64) :
    stride * new ≠ 0#64 := by
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [mul_stride_toNat_p h] at ht
  change new.toNat * stride.toNat = 0 at ht
  omega

private theorem beq_mul_stride_zero_eq_false_p {new stride : BitVec 64}
    (h0 : 0 < new.toNat * stride.toNat) (h : new.toNat * stride.toNat < 2 ^ 64) :
    (stride * new == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  exact mul_stride_ne_zero_p h0 h

private theorem hi_stride_eq_false_p {new stride align : BitVec 64}
    (h : new.toNat * stride.toNat + align.toNat ≤ 2 ^ 63) :
    (9223372036854775808#64 - align).ult (stride * new) = false := by
  have hsub : (9223372036854775808#64 - align).toNat = 2 ^ 63 - align.toNat := by
    rw [BitVec.toNat_sub_of_le]
    · simp
    · rw [BitVec.le_def]
      change align.toNat ≤ 2 ^ 63
      omega
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, hsub, mul_stride_toNat_p (by omega)]
  omega

private theorem memRegion_24_p (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v2) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v0)) := by
  rw [show (24 : Nat) = 8 + (8 + 8) by rfl, memRegion_split a 8 (8 + 8) (by decide),
    memRegion_split (a + 8#64) 8 8 (by decide), ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem stackAt_finishGrowX_p (sp : BitVec 64) :
    stackAt sp (extHookStack + 48) =
      stackAt (sp - 48#64) extHookStack ∗ cells (sp - 48#64) 6 :=
  ProofLib.stackAt_split_cells sp 16384 6 (by decide)

private theorem instantiate_post_exists {α : Sort _} {prog : Program} {target_pc : BitVec 64}
    {s0 s : State} {P R : SepProp} {Q : α → State → SepProp} {oom : State → SepProp}
    (w : α)
    (h : SepWP prog target_pc s P (fun sf P_f =>
      ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Q w sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) oom) :
    SepWP prog target_pc s P (fun sf P_f =>
      ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (∃∗ a, Q a sf) ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) oom := by
  refine SepWP.mono h fun sf P_f _ _ ⟨hq, hsp, hcs⟩ => ⟨fun hm => ?_, hsp, hcs⟩
  rw [sepExists_sepConj_left, satisfies_sepExists]
  exact ⟨w, hq hm⟩

/-! ## 2. Block `587` Zero-Cap & Nonzero-Cap Symbolic Execution -/

def finishGrowZeroSpec2X {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (FinishGrowCall × M.σ) :=
  { finishGrowSpecX M A lim with
      pre := fun (x, st) s =>
        ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
          s.readReg64 .x3 = x.new ∧ s.readReg64 .x4 = x.align ∧ s.readReg64 .x5 = x.stride ∧
          x.cap = 0#64 ∧ x.bs = [] ∧
          x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ 0 < x.stride.toNat ∧
          RustLayoutOk (x.new.toNat * x.stride.toNat) x.align.toNat ∧
          FitsEvents M lim st
            (rustAllocEvents (x.new.toNat * x.stride.toNat) x.align.toNat)⌝ ∗
        memRegion x.out 24 ∗ A.pool lim st s ∗ stackAt s.sp (extHookStack + 48) }

def finishGrowNeSpec2X {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (FinishGrowCall × M.σ) :=
  { finishGrowSpecX M A lim with
      pre := fun (x, st) s =>
        ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
          s.readReg64 .x3 = x.new ∧ s.readReg64 .x4 = x.align ∧ s.readReg64 .x5 = x.stride ∧
          x.cap ≠ 0#64 ∧ x.bs.length ≤ x.cap.toNat * x.stride.toNat ∧
          x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ 0 < x.stride.toNat ∧
          RustLayoutOk (x.new.toNat * x.stride.toNat) x.align.toNat ∧
          FitsEvents M lim st
            (rustReallocEvents (x.cap.toNat * x.stride.toNat)
              (x.new.toNat * x.stride.toNat) x.align.toNat)⌝ ∗
        memRegion x.out 24 ∗
        A.live x.ptr (x.cap.toNat * x.stride.toNat) x.align.toNat ∗ (x.ptr ↦ₛ x.bs) ∗
        memRegion (x.ptr + BitVec.ofNat 64 x.bs.length)
          (x.cap.toNat * x.stride.toNat - x.bs.length) ∗
        A.pool lim st s ∗ stackAt s.sp (extHookStack + 48) }

set_option maxHeartbeats 1000000 in
theorem finish_grow_zero_blk587_ok_x_of_hooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hshim : subroutine_ok (lsProg_587 H) (lsρ lsRustNoAllocShimSymCli)
      (withLsRoCl lsmpl (shimSpecWithStack extHookStack)))
    (halloc : subroutine_ok (lsProg_587 H) (lsρ lsRustAllocSymCli)
      (withLsRoCl lsmpl (rustCliAllocNoOomExternSpecWithStack M A lim false extHookStack))) :
    subroutine_ok (lsProg_587 H) (lsmpl.base 587)
      (withLsCodeRoLoaded lsmpl (finishGrowZeroSpec2X A lim)) := by
  dsimp only [withLsRoCl, shimSpecWithStack, lsProg_587] at hshim
  simp only [withLsRoCl, rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomSpecWithStack,
    Bool.false_eq_true, ↓reduceIte, lsProg_587] at halloc
  unfold withLsCodeRoLoaded finishGrowZeroSpec2X finishGrowSpecX finishGrowSpecWithStack
  simp only [memRegion_24_p, stackAt_finishGrowX_p, sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  change subroutine_ok ((blkPC_587).rebase (blkPl_587).base H) (blkPl_587).base _
  wp_init x s0
  obtain ⟨⟨out, cap, ptr, new, align, stride, bs⟩, st⟩ := x
  dsimp only at *
  have hcrl0 : LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  have hrlay : RustLayoutOk (new.toNat * stride.toNat) align.toNat := by assumption
  rcases hrlay with ⟨⟨hsz_pos, hpow, hbound⟩, hal31⟩
  have hcap_eq : cap = 0#64 := by assumption
  have hbs_eq : bs = [] := by assumption
  subst hcap_eq
  subst hbs_eq
  have hlt64 : new.toNat * stride.toNat < 2 ^ 64 := by omega
  have humulh := umulh_stride_eq_zero_p hlt64
  have hhi := hi_stride_eq_false_p hbound
  have hcbz := beq_mul_stride_zero_eq_false_p hsz_pos hlt64
  have hmul : (stride * new).toNat = new.toNat * stride.toNat := mul_stride_toNat_p hlt64
  have hrlay : RustLayoutOk (new.toNat * stride.toNat) align.toNat :=
    ⟨⟨hsz_pos, hpow, hbound⟩, hal31⟩
  change SepWP (lsProg_587 H) _ _ _ _ _
  apply sepWP_seq_lscro (mid := lsρ lsRustNoAllocShimSymCli) hcrl0
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSymCli)
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hcrl1
  simp only [wp_norm] at hcrl1
  have ⟨hcl1, hro1⟩ := hcrl1
  apply sepWP_seq_lscro (mid := lsρ lsRustAllocSymCli) hcrl1
  change SepWP ((blkPC_587).rebase (blkPl_587).base H) _ _ _ _ _
  wp_call hshim ()
  apply ProofLib.SepWP.transport_budgetPool (by assumption)
  change SepWP (lsProg_587 H) _ _ _ _ _
  wp_steps_sync_pool (lsρ lsRustAllocSymCli)
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hcrl2
  simp only [wp_norm] at hcrl2
  have ⟨hcl2, hro2⟩ := hcrl2
  change SepWP ((blkPC_587).rebase (blkPl_587).base H) _ _ _ _ _
  wp_call halloc (new.toNat * stride.toNat, align.toNat, st)
  have hret_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false :=
    beq_eq_false_iff_ne.mpr (by tauto)
  have hmul_bv : stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) :=
    mul_stride_eq_ofNat_p hlt64
  change SepWP (lsProg_587 H) _ _ _ _ _
  wp_steps_sync_pool (s0.readReg64 Reg.x30)
  simp only [finishGrowEvents]
  apply instantiate_post_exists (sf_1.readReg64 Reg.x0)
  simp only [pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj]
  wp_done

set_option maxHeartbeats 1000000 in
theorem finish_grow_zero_fs_blk587_ok_x_of_hooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hshim : subroutine_ok (lsProg_587 H) (lsρ lsRustNoAllocShimSymCli)
      (withLsRoCl lsmpl (shimSpecWithStack extHookStack).keepsFs))
    (halloc : subroutine_ok (lsProg_587 H) (lsρ lsRustAllocSymCli)
      (withLsRoCl lsmpl (rustCliAllocNoOomExternSpecWithStack M A lim false extHookStack).keepsFs)) :
    subroutine_ok (lsProg_587 H) (lsmpl.base 587)
      (withLsCodeRoLoaded lsmpl (finishGrowZeroSpec2X A lim).keepsFs) := by
  dsimp only [withLsRoCl, Spec.keepsFs, shimSpecWithStack, lsProg_587] at hshim
  simp only [withLsRoCl, Spec.keepsFs, rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomSpecWithStack,
    Bool.false_eq_true, ↓reduceIte, lsProg_587] at halloc
  unfold withLsCodeRoLoaded Spec.keepsFs finishGrowZeroSpec2X finishGrowSpecX finishGrowSpecWithStack
  simp only [memRegion_24_p, stackAt_finishGrowX_p, sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  change subroutine_ok ((blkPC_587).rebase (blkPl_587).base H) (blkPl_587).base _
  wp_init x s0
  obtain ⟨⟨out, cap, ptr, new, align, stride, bs⟩, st⟩ := x
  dsimp only at *
  have hcrl0 : LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  have hrlay : RustLayoutOk (new.toNat * stride.toNat) align.toNat := by assumption
  rcases hrlay with ⟨⟨hsz_pos, hpow, hbound⟩, hal31⟩
  have hcap_eq : cap = 0#64 := by assumption
  have hbs_eq : bs = [] := by assumption
  subst hcap_eq
  subst hbs_eq
  have hlt64 : new.toNat * stride.toNat < 2 ^ 64 := by omega
  have humulh := umulh_stride_eq_zero_p hlt64
  have hhi := hi_stride_eq_false_p hbound
  have hcbz := beq_mul_stride_zero_eq_false_p hsz_pos hlt64
  have hmul : (stride * new).toNat = new.toNat * stride.toNat := mul_stride_toNat_p hlt64
  have hrlay : RustLayoutOk (new.toNat * stride.toNat) align.toNat :=
    ⟨⟨hsz_pos, hpow, hbound⟩, hal31⟩
  change SepWP (lsProg_587 H) _ _ _ _ _
  apply sepWP_seq_lscro (mid := lsρ lsRustNoAllocShimSymCli) hcrl0
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSymCli)
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hcrl1
  simp only [wp_norm] at hcrl1
  have ⟨hcl1, hro1⟩ := hcrl1
  apply sepWP_seq_lscro (mid := lsρ lsRustAllocSymCli) hcrl1
  change SepWP ((blkPC_587).rebase (blkPl_587).base H) _ _ _ _ _
  wp_call hshim ()
  apply ProofLib.SepWP.transport_budgetPool (by assumption)
  change SepWP (lsProg_587 H) _ _ _ _ _
  wp_steps_sync_pool (lsρ lsRustAllocSymCli)
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hcrl2
  simp only [wp_norm] at hcrl2
  have ⟨hcl2, hro2⟩ := hcrl2
  change SepWP ((blkPC_587).rebase (blkPl_587).base H) _ _ _ _ _
  wp_call halloc (new.toNat * stride.toNat, align.toNat, st)
  have hret_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false :=
    beq_eq_false_iff_ne.mpr (by tauto)
  have hmul_bv : stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) :=
    mul_stride_eq_ofNat_p hlt64
  change SepWP (lsProg_587 H) _ _ _ _ _
  wp_steps_sync_pool (s0.readReg64 Reg.x30)
  simp only [finishGrowEvents]
  apply instantiate_post_exists (sf_1.readReg64 Reg.x0)
  simp only [pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj]
  wp_done

set_option maxHeartbeats 1000000 in
theorem finish_grow_ne_blk587_ok_x_of_hooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hrealloc : subroutine_ok (lsProg_587 H) (lsρ lsRustReallocSymCli)
      (withLsRoCl lsmpl (rustCliReallocNoOomExternSpecWithStack M A lim extHookStack))) :
    subroutine_ok (lsProg_587 H) (lsmpl.base 587)
      (withLsCodeRoLoaded lsmpl (finishGrowNeSpec2X A lim)) := by
  dsimp only [withLsRoCl, rustCliReallocNoOomExternSpecWithStack, lsProg_587] at hrealloc
  unfold withLsCodeRoLoaded finishGrowNeSpec2X finishGrowSpecX finishGrowSpecWithStack
  simp only [memRegion_24_p, stackAt_finishGrowX_p, sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  change subroutine_ok ((blkPC_587).rebase (blkPl_587).base H) (blkPl_587).base _
  wp_init x s0
  obtain ⟨⟨out, cap, ptr, new, align, stride, bs⟩, st⟩ := x
  dsimp only at *
  have hcrl0 : LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  have hrlay : RustLayoutOk (new.toNat * stride.toNat) align.toNat := by assumption
  rcases hrlay with ⟨⟨hsz_pos, hpow, hbound⟩, hal31⟩
  have hcap_ne : cap ≠ 0#64 := by assumption
  have hstr_pos : 0 < stride.toNat := by assumption
  have hcap_le_new : cap.toNat ≤ new.toNat := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat * stride.toNat := by assumption
  have hlt64 : new.toNat * stride.toNat < 2 ^ 64 := by omega
  have hcap_le : cap.toNat * stride.toNat ≤ new.toNat * stride.toNat :=
    Nat.mul_le_mul_right stride.toNat hcap_le_new
  have hcap_lt64 : cap.toNat * stride.toNat < 2 ^ 64 := by omega
  have hcap_pos : 0 < cap.toNat :=
    Nat.pos_of_ne_zero (fun hc => hcap_ne (BitVec.eq_of_toNat_eq hc))
  have hold_pos : 0 < cap.toNat * stride.toNat := Nat.mul_pos hcap_pos hstr_pos
  have humulh := umulh_stride_eq_zero_p hlt64
  have hhi := hi_stride_eq_false_p hbound
  have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap_ne
  have hmul : (stride * new).toNat = new.toNat * stride.toNat := mul_stride_toNat_p hlt64
  have hmul_cap : (stride * cap).toNat = cap.toNat * stride.toNat := mul_stride_toNat_p hcap_lt64
  have hle_new : bs.length ≤ new.toNat * stride.toNat := by omega
  have hrlay_old : RustLayoutOk (cap.toNat * stride.toNat) align.toNat :=
    ⟨⟨hold_pos, hpow, by omega⟩, hal31⟩
  have hrlay : RustLayoutOk (new.toNat * stride.toNat) align.toNat :=
    ⟨⟨hsz_pos, hpow, hbound⟩, hal31⟩
  change SepWP (lsProg_587 H) _ _ _ _ _
  apply sepWP_seq_lscro (mid := lsρ lsRustReallocSymCli) hcrl0
  wp_steps_sync_pool (lsρ lsRustReallocSymCli)
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hcrl1
  simp only [wp_norm] at hcrl1
  have ⟨hcl1, hro1⟩ := hcrl1
  change SepWP ((blkPC_587).rebase (blkPl_587).base H) _ _ _ _ _
  wp_call hrealloc (ptr, cap.toNat * stride.toNat, align.toNat, new.toNat * stride.toNat, bs, st)
  have hret_beq : (sf.readReg64 Reg.x0 == 0#64) = false :=
    beq_eq_false_iff_ne.mpr (by tauto)
  have hmul_bv : stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) :=
    mul_stride_eq_ofNat_p hlt64
  have hcap_nat_ne : cap.toNat ≠ 0 := Nat.ne_of_gt hcap_pos
  change SepWP (lsProg_587 H) _ _ _ _ _
  wp_steps_sync_pool (s0.readReg64 Reg.x30)
  simp only [finishGrowEvents, hcap_nat_ne, ↓reduceIte]
  apply instantiate_post_exists (sf.readReg64 Reg.x0)
  wp_done

set_option maxHeartbeats 1000000 in
theorem finish_grow_ne_fs_blk587_ok_x_of_hooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hrealloc : subroutine_ok (lsProg_587 H) (lsρ lsRustReallocSymCli)
      (withLsRoCl lsmpl (rustCliReallocNoOomExternSpecWithStack M A lim extHookStack).keepsFs)) :
    subroutine_ok (lsProg_587 H) (lsmpl.base 587)
      (withLsCodeRoLoaded lsmpl (finishGrowNeSpec2X A lim).keepsFs) := by
  dsimp only [withLsRoCl, Spec.keepsFs, rustCliReallocNoOomExternSpecWithStack, lsProg_587] at hrealloc
  unfold withLsCodeRoLoaded Spec.keepsFs finishGrowNeSpec2X finishGrowSpecX finishGrowSpecWithStack
  simp only [memRegion_24_p, stackAt_finishGrowX_p, sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  change subroutine_ok ((blkPC_587).rebase (blkPl_587).base H) (blkPl_587).base _
  wp_init x s0
  obtain ⟨⟨out, cap, ptr, new, align, stride, bs⟩, st⟩ := x
  dsimp only at *
  have hcrl0 : LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  have hrlay : RustLayoutOk (new.toNat * stride.toNat) align.toNat := by assumption
  rcases hrlay with ⟨⟨hsz_pos, hpow, hbound⟩, hal31⟩
  have hcap_ne : cap ≠ 0#64 := by assumption
  have hstr_pos : 0 < stride.toNat := by assumption
  have hcap_le_new : cap.toNat ≤ new.toNat := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat * stride.toNat := by assumption
  have hlt64 : new.toNat * stride.toNat < 2 ^ 64 := by omega
  have hcap_le : cap.toNat * stride.toNat ≤ new.toNat * stride.toNat :=
    Nat.mul_le_mul_right stride.toNat hcap_le_new
  have hcap_lt64 : cap.toNat * stride.toNat < 2 ^ 64 := by omega
  have hcap_pos : 0 < cap.toNat :=
    Nat.pos_of_ne_zero (fun hc => hcap_ne (BitVec.eq_of_toNat_eq hc))
  have hold_pos : 0 < cap.toNat * stride.toNat := Nat.mul_pos hcap_pos hstr_pos
  have humulh := umulh_stride_eq_zero_p hlt64
  have hhi := hi_stride_eq_false_p hbound
  have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap_ne
  have hmul : (stride * new).toNat = new.toNat * stride.toNat := mul_stride_toNat_p hlt64
  have hmul_cap : (stride * cap).toNat = cap.toNat * stride.toNat := mul_stride_toNat_p hcap_lt64
  have hle_new : bs.length ≤ new.toNat * stride.toNat := by omega
  have hrlay_old : RustLayoutOk (cap.toNat * stride.toNat) align.toNat :=
    ⟨⟨hold_pos, hpow, by omega⟩, hal31⟩
  have hrlay : RustLayoutOk (new.toNat * stride.toNat) align.toNat :=
    ⟨⟨hsz_pos, hpow, hbound⟩, hal31⟩
  change SepWP (lsProg_587 H) _ _ _ _ _
  apply sepWP_seq_lscro (mid := lsρ lsRustReallocSymCli) hcrl0
  wp_steps_sync_pool (lsρ lsRustReallocSymCli)
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hcrl1
  simp only [wp_norm] at hcrl1
  have ⟨hcl1, hro1⟩ := hcrl1
  change SepWP ((blkPC_587).rebase (blkPl_587).base H) _ _ _ _ _
  wp_call hrealloc (ptr, cap.toNat * stride.toNat, align.toNat, new.toNat * stride.toNat, bs, st)
  have hret_beq : (sf.readReg64 Reg.x0 == 0#64) = false :=
    beq_eq_false_iff_ne.mpr (by tauto)
  have hmul_bv : stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) :=
    mul_stride_eq_ofNat_p hlt64
  have hcap_nat_ne : cap.toNat ≠ 0 := Nat.ne_of_gt hcap_pos
  change SepWP (lsProg_587 H) _ _ _ _ _
  wp_steps_sync_pool (s0.readReg64 Reg.x30)
  simp only [finishGrowEvents, hcap_nat_ne, ↓reduceIte]
  apply instantiate_post_exists (sf.readReg64 Reg.x0)
  wp_done

/-! ## 3. Block `587` Full `finishGrowSpecX` Contracts -/

theorem cliFinishGrow_blk587_ok_of_hooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hshim : subroutine_ok (lsProg_587 H) (lsρ lsRustNoAllocShimSymCli)
      (withLsRoCl lsmpl (shimSpecWithStack extHookStack)))
    (halloc : subroutine_ok (lsProg_587 H) (lsρ lsRustAllocSymCli)
      (withLsRoCl lsmpl (rustCliAllocNoOomExternSpecWithStack M A lim false extHookStack)))
    (hrealloc : subroutine_ok (lsProg_587 H) (lsρ lsRustReallocSymCli)
      (withLsRoCl lsmpl (rustCliReallocNoOomExternSpecWithStack M A lim extHookStack))) :
    subroutine_ok (lsProg_587 H) (lsmpl.base 587)
      (withLsCodeRoLoaded lsmpl (finishGrowSpecX M A lim)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  obtain ⟨hcrl, hpre0⟩ := extract_withLsCodeRoLoaded hpre
  by_cases hcap0 : x.cap = 0#64
  · refine (finish_grow_zero_blk587_ok_x_of_hooks hshim halloc).mono_outcome
      (x, st) R s0 hpc hrun ?_ hsp fun _ hout => hout
    dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl, ?_⟩
    simp only [finishGrowSpecX, finishGrowSpecWithStack, finishGrowZeroSpec2X,
      fitsEnv_finishGrow_iff, finishGrowEvents,
      FinishGrowCall.oldBuf, hcap0, ↓reduceIte, BitVec.toNat_ofNat, Nat.zero_mod,
      emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre0 ⊢
    rcases hpre0 with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hbs0, _, hle, hnew, hstr, hlay, hfit⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, trivial, hbs0 trivial, hle, hnew, hstr, hlay, hfit⟩, hmem⟩
  · refine (finish_grow_ne_blk587_ok_x_of_hooks hrealloc).mono_outcome
      (x, st) R s0 hpc hrun ?_ hsp fun _ hout => hout
    have hcap_nat_ne : x.cap.toNat ≠ 0 := fun hc => hcap0 (BitVec.eq_of_toNat_eq hc)
    dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl, ?_⟩
    simp only [finishGrowSpecX, finishGrowSpecWithStack, finishGrowNeSpec2X,
      fitsEnv_finishGrow_iff, finishGrowEvents,
      FinishGrowCall.oldBuf, hcap0, hcap_nat_ne, ↓reduceIte,
      LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live,
      sepConj_assoc, satisfies_pure_sepConj] at hpre0 ⊢
    rcases hpre0 with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, _, hbs, hle, hnew, hstr, hlay, hfit⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hcap0, hbs, hle, hnew, hstr, hlay, hfit⟩, hmem⟩

theorem cliFinishGrow_blk587_okFs_of_hooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hshim : subroutine_ok (lsProg_587 H) (lsρ lsRustNoAllocShimSymCli)
      (withLsRoCl lsmpl (shimSpecWithStack extHookStack).keepsFs))
    (halloc : subroutine_ok (lsProg_587 H) (lsρ lsRustAllocSymCli)
      (withLsRoCl lsmpl (rustCliAllocNoOomExternSpecWithStack M A lim false extHookStack).keepsFs))
    (hrealloc : subroutine_ok (lsProg_587 H) (lsρ lsRustReallocSymCli)
      (withLsRoCl lsmpl (rustCliReallocNoOomExternSpecWithStack M A lim extHookStack).keepsFs)) :
    subroutine_ok (lsProg_587 H) (lsmpl.base 587)
      (withLsCodeRoLoaded lsmpl (finishGrowSpecX M A lim).keepsFs) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  obtain ⟨hcrl, hpre0⟩ := extract_withLsCodeRoLoaded hpre
  by_cases hcap0 : x.cap = 0#64
  · refine (finish_grow_zero_fs_blk587_ok_x_of_hooks hshim halloc).mono_outcome
      (x, st) R s0 hpc hrun ?_ hsp fun _ hout => hout
    dsimp only [withLsCodeRoLoaded, Spec.keepsFs]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl, ?_⟩
    simp only [finishGrowSpecX, finishGrowSpecWithStack, finishGrowZeroSpec2X, Spec.keepsFs,
      fitsEnv_finishGrow_iff, finishGrowEvents,
      FinishGrowCall.oldBuf, hcap0, ↓reduceIte, BitVec.toNat_ofNat, Nat.zero_mod,
      emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre0 ⊢
    rcases hpre0 with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hbs0, _, hle, hnew, hstr, hlay, hfit⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, trivial, hbs0 trivial, hle, hnew, hstr, hlay, hfit⟩, hmem⟩
  · refine (finish_grow_ne_fs_blk587_ok_x_of_hooks hrealloc).mono_outcome
      (x, st) R s0 hpc hrun ?_ hsp fun _ hout => hout
    have hcap_nat_ne : x.cap.toNat ≠ 0 := fun hc => hcap0 (BitVec.eq_of_toNat_eq hc)
    dsimp only [withLsCodeRoLoaded, Spec.keepsFs]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl, ?_⟩
    simp only [finishGrowSpecX, finishGrowSpecWithStack, finishGrowNeSpec2X, Spec.keepsFs,
      fitsEnv_finishGrow_iff, finishGrowEvents,
      FinishGrowCall.oldBuf, hcap0, hcap_nat_ne, ↓reduceIte,
      LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live,
      sepConj_assoc, satisfies_pure_sepConj] at hpre0 ⊢
    rcases hpre0 with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, _, hbs, hle, hnew, hstr, hlay, hfit⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hcap0, hbs, hle, hnew, hstr, hlay, hfit⟩, hmem⟩

/-! ## 4. `SpecRefines` Cell-Form Corollaries (`finishGrowZeroCellsRustSpec`, `finishGrowNeCellsRustSpec`) -/

/-- `RustLayoutOk` counterpart of `LayoutBudget.finishGrowZeroCellsSpec`. -/
def finishGrowZeroCellsRustSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (FGCellsGhost × M.σ) :=
  { finishGrowZeroCellsSpec A lim with
    pre := fun ((out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp), st) s =>
      ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
        s.readReg64 .x3 = new ∧ s.readReg64 .x4 = align ∧ s.readReg64 .x5 = stride ∧
        s.sp = fsp ∧ cap = 0#64 ∧ bs = [] ∧ cap.toNat ≤ new.toNat ∧
        0 < new.toNat ∧ 0 < stride.toNat ∧ RustLayoutOk (new.toNat * stride.toNat) align.toNat ∧
        FitsEnv M lim st (FinishGrowZeroEnv new stride align)⌝ ∗
      (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
      A.pool lim st s ∗ stackAt fsp finishGrowStackX }

/-- `RustLayoutOk` counterpart of `LayoutBudget.finishGrowNeCellsSpec`. -/
def finishGrowNeCellsRustSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (FGCellsGhost × M.σ) :=
  { finishGrowNeCellsSpec A lim with
    pre := fun ((out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp), st) s =>
      ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
        s.readReg64 .x3 = new ∧ s.readReg64 .x4 = align ∧ s.readReg64 .x5 = stride ∧
        s.sp = fsp ∧ cap ≠ 0#64 ∧ bs.length ≤ cap.toNat * stride.toNat ∧ cap.toNat ≤ new.toNat ∧
        0 < new.toNat ∧ 0 < stride.toNat ∧ RustLayoutOk (new.toNat * stride.toNat) align.toNat ∧
        FitsEnv M lim st (FinishGrowNeEnv cap new stride align)⌝ ∗
      (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
      A.live ptr (cap.toNat * stride.toNat) align.toNat ∗ (ptr ↦ₛ bs) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat * stride.toNat - bs.length) ∗
      A.pool lim st s ∗ stackAt fsp finishGrowStackX }

theorem finishGrowSpecX_refines_zeroCells {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    SpecRefines (finishGrowSpecX M A lim) (finishGrowZeroCellsRustSpec A lim) := by
  intro ⟨(out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp), st⟩ R s0 hpre
  simp only [finishGrowZeroCellsRustSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with
    ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap0, hbs, hle, hpos, hstr, hlay, hfit0⟩, hmem⟩
  subst hfsp; subst hcap0; subst hbs
  let hcall : FinishGrowCall := ⟨out, 0#64, ptr, new, align, stride, []⟩
  have hfit : FitsEnv M lim st (FinishGrowEnv hcall) := by
    intro evs hevs
    apply hfit0 evs
    simpa only [FinishGrowEnv, FinishGrowZeroEnv, hcall, finishGrowEvents,
      BitVec.toNat_ofNat, Nat.zero_mod, ↓reduceIte] using hevs
  have hpre0 : s0.mem ⊨ (finishGrowSpecX M A lim).pre (hcall, st) s0 ∗ R := by
    simp only [finishGrowSpecX, finishGrowSpecWithStack, hcall, FinishGrowCall.oldBuf, ↓reduceIte,
      memRegion_24_p, emp_sepConj, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, fun _ => trivial, Nat.zero_le _, hle, hpos, hstr,
      hlay, hfit⟩, by simpa only [sepConj_assoc] using hmem⟩
  refine ⟨(hcall, st), R, hpre0, ?_, fun _ h => h, fun _ _ h => h, fun _ h => h⟩
  intro sf hq
  simp only [finishGrowSpecX, finishGrowSpecWithStack, finishGrowZeroCellsRustSpec,
    finishGrowZeroCellsSpec, hcall, FinishGrowCall.oldBuf, ↓reduceIte,
    pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj,
    finishGrowEvents, BitVec.toNat_ofNat, Nat.zero_mod,
    sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
  rcases hq with ⟨p', hq⟩
  refine ⟨rustAllocEvents (new.toNat * stride.toNat) align.toNat, p',
    BitVec.ofNat 64 (new.toNat * stride.toNat), ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq
  rw [sepConj_assoc, satisfies_pure_sepConj]
  rcases hq with ⟨⟨hpne, hmod, htr⟩, hrest⟩
  refine ⟨⟨hpne, hmod, htr, rfl⟩, ?_⟩
  exact Satisfies.mono (ByteSlice.entails_of_eq (by sep_ac_rfl)) hrest

theorem finishGrowSpecX_refines_neCells {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    SpecRefines (finishGrowSpecX M A lim) (finishGrowNeCellsRustSpec A lim) := by
  intro ⟨(out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp), st⟩ R s0 hpre
  simp only [finishGrowNeCellsRustSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with
    ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap, hbs, hle, hpos, hstr, hlay, hfit0⟩, hmem⟩
  subst hfsp
  have hcap_nat_ne : cap.toNat ≠ 0 := fun hc => hcap (BitVec.eq_of_toNat_eq hc)
  let hcall : FinishGrowCall := ⟨out, cap, ptr, new, align, stride, bs⟩
  have hfit : FitsEnv M lim st (FinishGrowEnv hcall) := by
    intro evs hevs
    apply hfit0 evs
    simpa only [FinishGrowEnv, FinishGrowNeEnv, hcall, finishGrowEvents,
      hcap_nat_ne, ↓reduceIte] using hevs
  have hpre0 : s0.mem ⊨ (finishGrowSpecX M A lim).pre (hcall, st) s0 ∗ R := by
    simp only [finishGrowSpecX, finishGrowSpecWithStack, hcall, FinishGrowCall.oldBuf,
      hcap, ↓reduceIte, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live,
      memRegion_24_p, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, False.elim, hbs, hle, hpos, hstr, hlay, hfit⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  refine ⟨(hcall, st), R, hpre0, ?_, fun _ h => h, fun _ _ h => h, fun _ h => h⟩
  intro sf hq
  simp only [finishGrowSpecX, finishGrowSpecWithStack, finishGrowNeCellsRustSpec,
    finishGrowNeCellsSpec, hcall, FinishGrowCall.oldBuf, ↓reduceIte,
    finishGrowEvents, hcap_nat_ne,
    sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
  rcases hq with ⟨p', hq⟩
  refine ⟨rustReallocEvents (cap.toNat * stride.toNat) (new.toNat * stride.toNat) align.toNat,
    p', BitVec.ofNat 64 (new.toNat * stride.toNat), ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq
  rw [sepConj_assoc, satisfies_pure_sepConj]
  rcases hq with ⟨⟨hpne, hmod, htr⟩, hrest⟩
  refine ⟨⟨hpne, hmod, htr, rfl⟩, ?_⟩
  exact Satisfies.mono (ByteSlice.entails_of_eq (by sep_ac_rfl)) hrest

theorem finish_grow_zero_cells_blk587_ok_x_of_hooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hshim : subroutine_ok (lsProg_587 H) (lsρ lsRustNoAllocShimSymCli)
      (withLsRoCl lsmpl (shimSpecWithStack extHookStack)))
    (halloc : subroutine_ok (lsProg_587 H) (lsρ lsRustAllocSymCli)
      (withLsRoCl lsmpl (rustCliAllocNoOomExternSpecWithStack M A lim false extHookStack)))
    (hrealloc : subroutine_ok (lsProg_587 H) (lsρ lsRustReallocSymCli)
      (withLsRoCl lsmpl (rustCliReallocNoOomExternSpecWithStack M A lim extHookStack))) :
    subroutine_ok (lsProg_587 H) (lsmpl.base 587)
      (withLsCodeRoLoaded lsmpl (finishGrowZeroCellsRustSpec A lim)) :=
  CryptoVerification.SignalSession.Cli.MainHops.SpecRefines.apply_withLsCodeRoLoaded
    (finishGrowSpecX_refines_zeroCells A lim)
    (cliFinishGrow_blk587_ok_of_hooks hshim halloc hrealloc)

theorem finish_grow_zero_cells_fs_blk587_ok_x_of_hooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hshim : subroutine_ok (lsProg_587 H) (lsρ lsRustNoAllocShimSymCli)
      (withLsRoCl lsmpl (shimSpecWithStack extHookStack).keepsFs))
    (halloc : subroutine_ok (lsProg_587 H) (lsρ lsRustAllocSymCli)
      (withLsRoCl lsmpl (rustCliAllocNoOomExternSpecWithStack M A lim false extHookStack).keepsFs))
    (hrealloc : subroutine_ok (lsProg_587 H) (lsρ lsRustReallocSymCli)
      (withLsRoCl lsmpl (rustCliReallocNoOomExternSpecWithStack M A lim extHookStack).keepsFs)) :
    subroutine_ok (lsProg_587 H) (lsmpl.base 587)
      (withLsCodeRoLoaded lsmpl (finishGrowZeroCellsRustSpec A lim).keepsFs) :=
  CryptoVerification.SignalSession.Cli.MainHops.SpecRefines.apply_keepsFs_withLsCodeRoLoaded
    (finishGrowSpecX_refines_zeroCells A lim)
    (cliFinishGrow_blk587_okFs_of_hooks hshim halloc hrealloc)

theorem finish_grow_ne_cells_blk587_ok_x_of_hooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hshim : subroutine_ok (lsProg_587 H) (lsρ lsRustNoAllocShimSymCli)
      (withLsRoCl lsmpl (shimSpecWithStack extHookStack)))
    (halloc : subroutine_ok (lsProg_587 H) (lsρ lsRustAllocSymCli)
      (withLsRoCl lsmpl (rustCliAllocNoOomExternSpecWithStack M A lim false extHookStack)))
    (hrealloc : subroutine_ok (lsProg_587 H) (lsρ lsRustReallocSymCli)
      (withLsRoCl lsmpl (rustCliReallocNoOomExternSpecWithStack M A lim extHookStack))) :
    subroutine_ok (lsProg_587 H) (lsmpl.base 587)
      (withLsCodeRoLoaded lsmpl (finishGrowNeCellsRustSpec A lim)) :=
  CryptoVerification.SignalSession.Cli.MainHops.SpecRefines.apply_withLsCodeRoLoaded
    (finishGrowSpecX_refines_neCells A lim)
    (cliFinishGrow_blk587_ok_of_hooks hshim halloc hrealloc)

theorem finish_grow_ne_cells_fs_blk587_ok_x_of_hooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hshim : subroutine_ok (lsProg_587 H) (lsρ lsRustNoAllocShimSymCli)
      (withLsRoCl lsmpl (shimSpecWithStack extHookStack).keepsFs))
    (halloc : subroutine_ok (lsProg_587 H) (lsρ lsRustAllocSymCli)
      (withLsRoCl lsmpl (rustCliAllocNoOomExternSpecWithStack M A lim false extHookStack).keepsFs))
    (hrealloc : subroutine_ok (lsProg_587 H) (lsρ lsRustReallocSymCli)
      (withLsRoCl lsmpl (rustCliReallocNoOomExternSpecWithStack M A lim extHookStack).keepsFs)) :
    subroutine_ok (lsProg_587 H) (lsmpl.base 587)
      (withLsCodeRoLoaded lsmpl (finishGrowNeCellsRustSpec A lim).keepsFs) :=
  CryptoVerification.SignalSession.Cli.MainHops.SpecRefines.apply_keepsFs_withLsCodeRoLoaded
    (finishGrowSpecX_refines_neCells A lim)
    (cliFinishGrow_blk587_okFs_of_hooks hshim halloc hrealloc)

/-! ## 5. Cross-Block Lifted Contracts (`withLsRoCl lsmpl`) -/

section CallerBlock

variable [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
  {lim : BudgetLimits} {H : LibsignalHooks}
  {prog : Program} {i : Nat} [IsLsBlockProg prog i H]

theorem cliFinishGrow_placed_ok_of_hooks_at
    (hshim : subroutine_ok (lsProg_587 H) (lsρ lsRustNoAllocShimSymCli)
      (withLsRoCl lsmpl (shimSpecWithStack extHookStack)))
    (halloc : subroutine_ok (lsProg_587 H) (lsρ lsRustAllocSymCli)
      (withLsRoCl lsmpl (rustCliAllocNoOomExternSpecWithStack M A lim false extHookStack)))
    (hrealloc : subroutine_ok (lsProg_587 H) (lsρ lsRustReallocSymCli)
      (withLsRoCl lsmpl (rustCliReallocNoOomExternSpecWithStack M A lim extHookStack)))
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsmpl.base 587)
      (withLsRoCl lsmpl (finishGrowSpecX M A lim)) :=
  ls_subroutine_ok_rocl_of_block (i := i) (j := 587)
    (cliFinishGrow_blk587_ok_of_hooks hshim halloc hrealloc) hi

theorem cliFinishGrow_placed_okFs_of_hooks_at
    (hshim : subroutine_ok (lsProg_587 H) (lsρ lsRustNoAllocShimSymCli)
      (withLsRoCl lsmpl (shimSpecWithStack extHookStack).keepsFs))
    (halloc : subroutine_ok (lsProg_587 H) (lsρ lsRustAllocSymCli)
      (withLsRoCl lsmpl (rustCliAllocNoOomExternSpecWithStack M A lim false extHookStack).keepsFs))
    (hrealloc : subroutine_ok (lsProg_587 H) (lsρ lsRustReallocSymCli)
      (withLsRoCl lsmpl (rustCliReallocNoOomExternSpecWithStack M A lim extHookStack).keepsFs))
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsmpl.base 587)
      (withLsRoCl lsmpl (finishGrowSpecX M A lim).keepsFs) :=
  ls_subroutine_ok_rocl_of_block (i := i) (j := 587)
    (cliFinishGrow_blk587_okFs_of_hooks hshim halloc hrealloc) hi

theorem finish_grow_zero_cells_placed_ok_of_hooks_at
    (hshim : subroutine_ok (lsProg_587 H) (lsρ lsRustNoAllocShimSymCli)
      (withLsRoCl lsmpl (shimSpecWithStack extHookStack)))
    (halloc : subroutine_ok (lsProg_587 H) (lsρ lsRustAllocSymCli)
      (withLsRoCl lsmpl (rustCliAllocNoOomExternSpecWithStack M A lim false extHookStack)))
    (hrealloc : subroutine_ok (lsProg_587 H) (lsρ lsRustReallocSymCli)
      (withLsRoCl lsmpl (rustCliReallocNoOomExternSpecWithStack M A lim extHookStack)))
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsmpl.base 587)
      (withLsRoCl lsmpl (finishGrowZeroCellsRustSpec A lim)) :=
  ls_subroutine_ok_rocl_of_block (i := i) (j := 587)
    (finish_grow_zero_cells_blk587_ok_x_of_hooks hshim halloc hrealloc) hi

theorem finish_grow_zero_cells_fs_placed_ok_of_hooks_at
    (hshim : subroutine_ok (lsProg_587 H) (lsρ lsRustNoAllocShimSymCli)
      (withLsRoCl lsmpl (shimSpecWithStack extHookStack).keepsFs))
    (halloc : subroutine_ok (lsProg_587 H) (lsρ lsRustAllocSymCli)
      (withLsRoCl lsmpl (rustCliAllocNoOomExternSpecWithStack M A lim false extHookStack).keepsFs))
    (hrealloc : subroutine_ok (lsProg_587 H) (lsρ lsRustReallocSymCli)
      (withLsRoCl lsmpl (rustCliReallocNoOomExternSpecWithStack M A lim extHookStack).keepsFs))
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsmpl.base 587)
      (withLsRoCl lsmpl (finishGrowZeroCellsRustSpec A lim).keepsFs) :=
  ls_subroutine_ok_rocl_of_block (i := i) (j := 587)
    (finish_grow_zero_cells_fs_blk587_ok_x_of_hooks hshim halloc hrealloc) hi

theorem finish_grow_ne_cells_placed_ok_of_hooks_at
    (hshim : subroutine_ok (lsProg_587 H) (lsρ lsRustNoAllocShimSymCli)
      (withLsRoCl lsmpl (shimSpecWithStack extHookStack)))
    (halloc : subroutine_ok (lsProg_587 H) (lsρ lsRustAllocSymCli)
      (withLsRoCl lsmpl (rustCliAllocNoOomExternSpecWithStack M A lim false extHookStack)))
    (hrealloc : subroutine_ok (lsProg_587 H) (lsρ lsRustReallocSymCli)
      (withLsRoCl lsmpl (rustCliReallocNoOomExternSpecWithStack M A lim extHookStack)))
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsmpl.base 587)
      (withLsRoCl lsmpl (finishGrowNeCellsRustSpec A lim)) :=
  ls_subroutine_ok_rocl_of_block (i := i) (j := 587)
    (finish_grow_ne_cells_blk587_ok_x_of_hooks hshim halloc hrealloc) hi

theorem finish_grow_ne_cells_fs_placed_ok_of_hooks_at
    (hshim : subroutine_ok (lsProg_587 H) (lsρ lsRustNoAllocShimSymCli)
      (withLsRoCl lsmpl (shimSpecWithStack extHookStack).keepsFs))
    (halloc : subroutine_ok (lsProg_587 H) (lsρ lsRustAllocSymCli)
      (withLsRoCl lsmpl (rustCliAllocNoOomExternSpecWithStack M A lim false extHookStack).keepsFs))
    (hrealloc : subroutine_ok (lsProg_587 H) (lsρ lsRustReallocSymCli)
      (withLsRoCl lsmpl (rustCliReallocNoOomExternSpecWithStack M A lim extHookStack).keepsFs))
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsmpl.base 587)
      (withLsRoCl lsmpl (finishGrowNeCellsRustSpec A lim).keepsFs) :=
  ls_subroutine_ok_rocl_of_block (i := i) (j := 587)
    (finish_grow_ne_cells_fs_blk587_ok_x_of_hooks hshim halloc hrealloc) hi

end CallerBlock

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.FinishGrowFsPlacedBudget

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.VecDequeGrowBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.LoopPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.ProofPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.AddChunkCl1Placed
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Alloc.Fetch
import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPFrozen
import ProofLib.SepLogic.WPp

/-!
# `<PolyDecoder as Decoder>::add_chunk` (Block `419`): `RustCliAllocBudget` Inner Loop & `grow_one` Helpers

Verifies `AllocCallPreserved`-strengthened relocatable `RawVec<Pt>::grow_one` (Block `357`,
`stride = 4, align = 2`) under `RustCliAllocBudget M` and `withLsCodeLoaded lsmpl`, together with
the inner binary-search helpers `bsearchReplace_cl_placed_wpp` (`+236 -> +64`) and
`bsearchPush_cl_placed_wpp` (`+128 -> +64`) on Block `419`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.Leaves.AddChunkCl1PlacedBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open scoped CryptoVerification.CodeLayout
open scoped CryptoVerification.SpqrV1.Poly.AddChunk.AddChunkNorm
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement
  blkPC_357 blkPC_361 blkPC_419
  blkPl_357 blkPl_361 blkPl_419
  lscall_blk lsmpl sepWP_seq_lscl withLsCodeLoaded
)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalSpqrV1 (Pt SortedSetPt)
open CryptoVerification.LibsignalTripleRatchet (sessionMemmoveSpec)
open CryptoVerification.SpqrV1.Alloc (
  GrowGhost growOneStack
  spqrHandleErrorSym spqrMemmoveSym spqrRustAllocSym spqrRustNoAllocShimSym spqrRustReallocSym
  spqr_externAt?_of_mem spqr_hook_ok_of_mem
)
open CryptoVerification.SpqrV1.Poly (ptAt ptSliceAt sortedSetPtOf)
open CryptoVerification.SpqrV1.Poly.AddChunk (
  bsearchLoop bsearchLoop_bounds bsearchPush bsearchReplace
  bv32_bne_zeroExtend16 bv32_ule_zeroExtend16 bv64_beq_cap_ofNat
  bv64_lsl2_ofNat bv64_ne_zero_of_pos bv64_ule_succ cinc_insertIdx_eq
  dropLast_append_singleton_eq_set growOnePtFull_post_entails_grown
  memRegion_spare_split_one ptListBytes ptListBytes_length
  ptSliceAt_eq_pointsToBytes ptSliceAt_focus
  ptr_add_len_sub2 ptr_add_len_sub4
  reassemble_sortedSetPtOf_set reassemble_sortedSetPtOf_snoc
  sortedSetPtGrownAt sortedSetPtOf_expose
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv
  FitsEvents RustCliAllocBudget VmPreserved
  rustAllocEvents rustCliAllocBudgetSpec rustCliReallocBudgetSpec rustReallocEvents
)
open LibsignalBinary.Heap.IfaceSimp (allocCallPreserved_self)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  subroutine_ok_allocNoOom_withStack_of_hookSat
  subroutine_ok_reallocNoOom_withStack_of_hookSat
)
open LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux (
  acp_chain_acp session2ShimAcpWithStack_of_rustAllocShimVm
)
open LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneBudget (
  GrowOneStrideEnv fitsEnv_growOneStride_iff growOnePtFullSpec growOnePtSpec
  growOneStrideEmptySpec growOneStrideEmptySpecWithStack
  growOneStrideEvents growOneStrideFullSpec growOneStrideFullSpecWithStack
)
open LibsignalBinary.Proofs.SpqrV1.Alloc.VecDequeGrowBudgetAux (
  finishGrow8NeCellsAcpSpecG finishGrow8ZeroCellsAcpSpecG
  finish_grow_8_ne_cells_acp_placed_ok_of_hooks
  finish_grow_8_zero_cells_acp_placed_ok_of_hooks
)
open LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget (
  allocCallPreserved_trans withAllocVmPreserved
)
open LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget (
  AddChunkSlotEnv growOnePtEvents
)
open LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.LoopPlacedBudget (
  bsearch_insert_at_336_acp_placed_sepWP bsearch_insert_at_452_acp_placed_sepWP
  bsearch_push_empty_at_216_placed_sepWP bsearch_to_296_placed_sepWP
  withAllocCallPreserved
)
open LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.ProofPlacedBudgetAux (
  bsearch_push_grown_at_412_placed_sepWP sepWP_with_vm
)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget (of_sepWP_lscl)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. `AllocCallPreserved` Block `357` (`RawVec<Pt>::grow_one`, `stride = 4, align = 2`) -/

private theorem pc_setMem_pre (s : State) (m : Memory) : (s.setMem m).pc = s.pc := rfl
private theorem status_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).status = s.status := rfl
private theorem pstate_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).pstate = s.pstate := rfl
private theorem trace_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).trace = s.trace := rfl
private theorem calleeSavedVRegs_setMem_pre (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := rfl

private theorem stackAt_growOne_gen (sp : BitVec 64) {hookStack : Nat}
    (hhook : (hookStack + 48) + 8 * 8 ≤ 2 ^ 64) :
    stackAt sp ((hookStack + 48) + 64) =
      stackAt (sp - 64#64) (hookStack + 48) ∗ cells (sp - 64#64) 8 :=
  ProofLib.stackAt_split_cells sp (hookStack + 48) 8 hhook

private theorem grow_new_cap_eq {cap : BitVec 64} (h : max (2 * cap.toNat) 4 < 2 ^ 63) :
    (if (4#64).ult (cap <<< 1) = true then cap <<< 1 else 4#64) =
      BitVec.ofNat 64 (max (2 * cap.toNat) 4) := by
  have hsh : (cap <<< 1).toNat = 2 * cap.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    change (cap.toNat * 2) % 2 ^ 64 = 2 * cap.toNat
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  have h4 : (4#64 : BitVec 64).toNat = 4 := rfl
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  by_cases hc : (4#64).ult (cap <<< 1) = true
  · simp only [hc, ite_true, hsh]
    rw [BitVec.ult_eq_decide, decide_eq_true_eq, h4, hsh] at hc; omega
  · simp only [hc, Bool.false_eq_true, ite_false]
    rw [BitVec.ult_eq_decide, decide_eq_true_eq, h4, hsh] at hc
    change 4 = max (2 * cap.toNat) 4; omega

/-- `AllocCallPreserved`-strengthened budget contract for `RawVec<Pt>::grow_one`
    (`stride = 4, align = 2`). -/
def growOnePtBsAcpSpecWithStack (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hookStack : Nat) : Spec (GrowGhost × M.σ) where
  pre := fun ((v, cap, ptr, bs), st) s =>
    ⌜s.readReg64 .x0 = v ∧ bs.length ≤ cap.toNat * 4 ∧ ptr ≠ 0#64 ∧
      max (2 * cap.toNat) 4 * 4 + 2 ≤ 2 ^ 63 ∧
      FitsEnv M lim st (GrowOneStrideEnv cap 4 2)⌝ ∗
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
    (if cap = 0#64 then emp
     else A.live ptr (cap.toNat * 4) 2 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat * 4 - bs.length)) ∗
    A.pool lim st s ∗ stackAt s.sp ((hookStack + 48) + 64)
  post := fun ((v, cap, _, bs), st) s0 sf =>
    ⌜AllocCallPreserved s0 sf⌝ ∗
    (∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ p'.toNat % 2 = 0⌝ ∗
      (v ↦₆₄ BitVec.ofNat 64 (max (2 * cap.toNat) 4)) ∗ ((v + 8#64) ↦₆₄ p') ∗
      A.live p' (max (2 * cap.toNat) 4 * 4) 2 ∗ (p' ↦ₛ bs) ∗
      memRegion (p' + BitVec.ofNat 64 bs.length) (max (2 * cap.toNat) 4 * 4 - bs.length)) ∗
    A.pool lim (M.stepEvents (growOneStrideEvents cap 4 2) st) sf ∗
    stackAt s0.sp ((hookStack + 48) + 64)

abbrev growOnePtBsAcpSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (GrowGhost × M.σ) :=
  growOnePtBsAcpSpecWithStack M A lim allocHookStack

section SymbolicExecGrowOnePt

attribute [local irreducible] FitsEvents AllocCallPreserved
attribute [local arm64_norm ↓, local wp_norm ↓]
  CryptoVerification.SpqrV1.Alloc.GrowOneNorm.sp_setPC_pre
  CryptoVerification.SpqrV1.Alloc.GrowOneNorm.sp_setMem_setPC_pre
  CryptoVerification.SpqrV1.Alloc.GrowOneNorm.readReg64_setPC_pre
  CryptoVerification.SpqrV1.Alloc.GrowOneNorm.readReg64_setMem_setPC_pre
  CryptoVerification.SpqrV1.Alloc.GrowOneNorm.readReg32_setPC_pre
  CryptoVerification.SpqrV1.Alloc.GrowOneNorm.readReg32_setMem_setPC_pre
  CryptoVerification.SpqrV1.Alloc.GrowOneNorm.readReg_setPC_pre
  CryptoVerification.SpqrV1.Alloc.GrowOneNorm.readReg_setMem_setPC_pre
  pc_setMem_pre status_setMem_pre pstate_setMem_pre trace_setMem_pre
  calleeSavedVRegs_setMem_pre

theorem grow_one_pt_bs_acp_placed_ok_of_fg [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : (hookStack + 48) + 8 * 8 ≤ 2 ^ 64)
    (_h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hfg0_blk : subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (blkPl_361).base (finishGrow8ZeroCellsAcpSpecG M A lim hookStack))
    (hfg1_blk : subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (blkPl_361).base (finishGrow8NeCellsAcpSpecG M A lim hookStack)) :
    subroutine_ok ((blkPC_357).rebase (blkPl_357).base H)
      (blkPl_357).base
      (withLsCodeLoaded lsmpl (growOnePtBsAcpSpecWithStack M A lim hookStack)) := by
  unfold withLsCodeLoaded growOnePtBsAcpSpecWithStack
  simp only [stackAt_growOne_gen _ hhook]
  cells_unfold
  wp_init x s0
  rcases x with ⟨⟨v, cap, ptr, bs⟩, st⟩
  dsimp only at *
  have hcl : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hbs_le : bs.length ≤ cap.toNat * 4 := by assumption
  have hbound : max (2 * cap.toNat) 4 * 4 + 2 ≤ 2 ^ 63 := by omega
  have hfits_env : FitsEnv M lim st (GrowOneStrideEnv cap 4 2) := by assumption
  have hnew_lt63 : max (2 * cap.toNat) 4 < 2 ^ 63 := by omega
  have hnew_eq := grow_new_cap_eq hnew_lt63
  let new := BitVec.ofNat 64 (max (2 * cap.toNat) 4)
  have hnew_toNat : new.toNat = max (2 * cap.toNat) 4 := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by omega
  have hnew_pos : 0 < new.toNat := by omega
  have hpow : ∃ k, 2 = 2 ^ k := ⟨1, rfl⟩
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have hc0 : (0#64 : BitVec 64).toNat = 0 := rfl
    have hm4 : max (2 * 0) 4 = 4 := rfl
    rw [hc0] at hbs_le hnew_toNat
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hbs
    have hfits : FitsEvents M lim st (rustAllocEvents (new.toNat * 4) 2) := by
      rw [fitsEnv_growOneStride_iff] at hfits_env
      simpa only [growOneStrideEvents, ↓reduceIte, hnew_toNat, hm4] using hfits_env
    have hnew_eq0 : (if (4#64).ult (0#64 <<< 1) = true then 0#64 <<< 1 else 4#64) = new := hnew_eq
    have hmul_eq : max (2 * 0) 4 * 4 = new.toNat * 4 := by rw [hnew_toNat]
    simp only [ite_true, emp_sepConj, pointsToBytes_nil, List.length_nil,
      BitVec.add_zero, BitVec.toNat_ofNat, Nat.zero_mod, Nat.sub_zero,
      growOneStrideEvents, hmul_eq]
    apply sepWP_seq_lscl hcl (mid := lsmpl.base 361)
    wp_steps_sync_pool (lsmpl.base 361)
    simp only [State.setMem_setMem]
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) ?_
    intro hcl_m
    have hfg0 := lscall_blk (callerProg := (blkPC_357).rebase (blkPl_357).base H) hfg0_blk hcl_m
    wp_call hfg0 (s0.sp - 56#64, 0#64, ptr, new, 2#64, 4#64, [],
      v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64, st)
    have hacp : AllocCallPreserved s0 sf :=
      acp_chain_acp ‹AllocCallPreserved _ sf›
        (by simp only [arm64_norm, wp_norm, allocCallPreserved_self])
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    wp_done
  · have hfits : FitsEvents M lim st (rustReallocEvents (cap.toNat * 4) (new.toNat * 4) 2) := by
      rw [fitsEnv_growOneStride_iff] at hfits_env
      simpa only [growOneStrideEvents, hcap0, ↓reduceIte, hnew_toNat] using hfits_env
    simp only [hcap0, ite_false, growOneStrideEvents, sepConj_assoc]
    rw [← hnew_toNat]
    apply sepWP_seq_lscl hcl (mid := lsmpl.base 361)
    wp_steps_sync_pool (lsmpl.base 361)
    simp only [State.setMem_setMem]
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) ?_
    intro hcl_m
    have hfg1 := lscall_blk (callerProg := (blkPC_357).rebase (blkPl_357).base H) hfg1_blk hcl_m
    wp_call hfg1 (s0.sp - 56#64, cap, ptr, new, 2#64, 4#64, bs,
      v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64, st)
    have hacp : AllocCallPreserved s0 sf :=
      acp_chain_acp ‹AllocCallPreserved _ sf›
        (by simp only [arm64_norm, wp_norm, allocCallPreserved_self])
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    wp_done

end SymbolicExecGrowOnePt

theorem grow_one_pt_bs_acp_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_357).rebase (blkPl_357).base H)
      (blkPl_357).base
      (withLsCodeLoaded lsmpl (growOnePtBsAcpSpec M A lim)) :=
  grow_one_pt_bs_acp_placed_ok_of_fg (hookStack := allocHookStack) (by decide) h_panic
    (finish_grow_8_zero_cells_acp_placed_ok_of_hooks (by decide)
      (session2ShimAcpWithStack_of_rustAllocShimVm allocHookStack (spqr_hook_ok_of_mem hshim))
      (subroutine_ok_allocNoOom_withStack_of_hookSat halloc spqr_externAt?_of_mem))
    (finish_grow_8_ne_cells_acp_placed_ok_of_hooks (by decide)
      (subroutine_ok_reallocNoOom_withStack_of_hookSat hrealloc spqr_externAt?_of_mem))

theorem grow_one_pt_full_acp_placed_of_bs [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {addr : BitVec 64}
    (hbs : subroutine_ok P addr
      (withLsCodeLoaded lsmpl (growOnePtBsAcpSpec M A lim))) :
    subroutine_ok P addr
      (withLsCodeLoaded lsmpl (withAllocCallPreserved (growOnePtFullSpec M A lim))) := by
  refine subroutine_ok_outcome_intro fun ⟨⟨v, cap, ptr, bs⟩, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [withAllocCallPreserved, growOnePtFullSpec, growOneStrideFullSpec,
    growOneStrideFullSpecWithStack, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hlen, hptr, hbound, hfits⟩, hmem⟩
  have hpre' : s0.mem ⊨
      (withLsCodeLoaded lsmpl (growOnePtBsAcpSpec M A lim)).pre ((v, cap, ptr, bs), st) s0 ∗ R := by
    simp only [growOnePtBsAcpSpec, growOnePtBsAcpSpecWithStack, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, Nat.le_of_eq hlen, hptr, hbound, hfits⟩, ?_⟩
    by_cases hcap0 : cap = 0#64
    · simpa only [hcap0, ite_true] using hmem
    · simpa only [hcap0, ite_false, ← hlen, Nat.sub_self, memRegion_zero, sepConj_emp,
        sepConj_assoc] using hmem
  refine hbs.mono_outcome ((v, cap, ptr, bs), st) R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | hfail
  · refine Or.inl ⟨hret, hcc, ?_⟩
    have hsub_mul : (max (2 * cap.toNat) 4 - cap.toNat) * 4 =
        max (2 * cap.toNat) 4 * 4 - bs.length := by rw [Nat.sub_mul, hlen]
    simp only [withLsCodeLoaded, withAllocCallPreserved, growOnePtFullSpec, growOneStrideFullSpec,
      growOneStrideFullSpecWithStack, growOnePtBsAcpSpec, growOnePtBsAcpSpecWithStack,
      hsub_mul, sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    exact ⟨hq.1, hq.1.2.1, hq.2⟩
  · exact Or.inr hfail

theorem grow_one_pt_empty_acp_placed_of_bs [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {addr : BitVec 64}
    (hbs : subroutine_ok P addr
      (withLsCodeLoaded lsmpl (growOnePtBsAcpSpec M A lim))) :
    subroutine_ok P addr
      (withLsCodeLoaded lsmpl (withAllocCallPreserved (growOnePtSpec M A lim))) := by
  refine subroutine_ok_outcome_intro fun ⟨⟨v, cap, ptr⟩, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [withAllocCallPreserved, growOnePtSpec, growOneStrideEmptySpec,
    growOneStrideEmptySpecWithStack, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hptr, hbound, hfits⟩, hmem⟩
  have hpre' : s0.mem ⊨
      (withLsCodeLoaded lsmpl (growOnePtBsAcpSpec M A lim)).pre ((v, cap, ptr, []), st) s0 ∗ R := by
    simp only [growOnePtBsAcpSpec, growOnePtBsAcpSpecWithStack, List.length_nil,
      BitVec.ofNat_eq_ofNat, pointsToBytes_nil, BitVec.add_zero, Nat.sub_zero,
      emp_sepConj, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, Nat.zero_le _, hptr, hbound, hfits⟩, hmem⟩
  refine hbs.mono_outcome ((v, cap, ptr, []), st) R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | hfail
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [withLsCodeLoaded, withAllocCallPreserved, growOnePtSpec, growOneStrideEmptySpec,
      growOneStrideEmptySpecWithStack, growOnePtBsAcpSpec, growOnePtBsAcpSpecWithStack,
      List.length_nil, BitVec.ofNat_eq_ofNat, pointsToBytes_nil, BitVec.add_zero, Nat.sub_zero,
      emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    exact ⟨hq.1, hq.1.2.1, hq.2⟩
  · exact Or.inr hfail

theorem grow_one_pt_full_acp_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_357).rebase (blkPl_357).base H)
      (blkPl_357).base
      (withLsCodeLoaded lsmpl (withAllocCallPreserved (growOnePtFullSpec M A lim))) :=
  grow_one_pt_full_acp_placed_of_bs (grow_one_pt_bs_acp_placed_ok h_panic hshim halloc hrealloc)

theorem grow_one_pt_acp_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_357).rebase (blkPl_357).base H)
      (blkPl_357).base
      (withLsCodeLoaded lsmpl (withAllocCallPreserved (growOnePtSpec M A lim))) :=
  grow_one_pt_empty_acp_placed_of_bs (grow_one_pt_bs_acp_placed_ok h_panic hshim halloc hrealloc)

/-! ## 2. Callee Call Wrappers (`grow_one_pt` with `withLsCodeLoaded lsmpl` & `AllocCallPreserved`) -/

attribute [local arm64_norm ↓, local wp_norm ↓]
  CryptoVerification.SpqrV1.Poly.AddChunk.AddChunkNorm.sp_setPC_pre
  CryptoVerification.SpqrV1.Poly.AddChunk.AddChunkNorm.sp_setMem_setPC_pre
  CryptoVerification.SpqrV1.Poly.AddChunk.AddChunkNorm.readReg64_setPC_pre
  CryptoVerification.SpqrV1.Poly.AddChunk.AddChunkNorm.readReg64_setMem_setPC_pre
  CryptoVerification.SpqrV1.Poly.AddChunk.AddChunkNorm.readReg32_setPC_pre
  CryptoVerification.SpqrV1.Poly.AddChunk.AddChunkNorm.readReg32_setMem_setPC_pre
  CryptoVerification.SpqrV1.Poly.AddChunk.AddChunkNorm.readReg_setPC_pre
  CryptoVerification.SpqrV1.Poly.AddChunk.AddChunkNorm.readReg_setMem_setPC_pre
  CryptoVerification.SpqrV1.Poly.AddChunk.AddChunkNorm.calleeSavedVRegs_setPC_pre
  CryptoVerification.SpqrV1.Poly.AddChunk.AddChunkNorm.calleeSavedVRegs_setMem_setPC_pre

private theorem sepWPp_call_frozen_noPanic {α : Type} {Inv : Memory → Prop}
    (hpres : ∀ m m', Inv m → m.KeepsFrozen m' → Inv m')
    {prog : Program} {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {F : SepProp}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hinv : Inv s.mem) (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → Inv sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp oom)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intros; rfl)
    (hpan_eq : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intros; rfl)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  obtain ⟨sm, hsteps, hout, _⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R) s hpc hrun (hpre R hm) hsp hL
  rcases hout with
      ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hpost⟩
  · rw [← sepConj_assoc] at hpost; rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm (hpres s.mem sm.mem hinv hsteps.keepsFrozen) R hpost
        (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [hpan_eq sm] at hpost; exact (not_satisfies_false_sepConj hpost).elim
  · rw [hexit_eq code sm] at hpost; exact (not_satisfies_false_sepConj hpost).elim
  · rw [hoom_eq sm] at hpost; exact (not_satisfies_false_sepConj hpost).elim

private theorem growOneStrideEvents_pt_full {cap : BitVec 64} {vec : List Pt}
    (h1 : 1 ≤ vec.length) (hcap_eq : cap.toNat = vec.length) :
    growOneStrideEvents cap 4 2 = growOnePtEvents vec.length := by
  have hcap_ne0 : cap ≠ 0#64 := by
    intro hc0; subst hc0; change 0 = vec.length at hcap_eq; omega
  have hlen_ne0 : vec.length ≠ 0 := by omega
  simp only [growOneStrideEvents, growOnePtEvents, hcap_ne0, hlen_ne0, ↓reduceIte, hcap_eq]
  rw [Nat.mul_comm vec.length 4, Nat.mul_comm (max (2 * vec.length) 4) 4]

private theorem growOneStrideEvents_pt_zero :
    growOneStrideEvents 0#64 4 2 = growOnePtEvents 0 := rfl

theorem call_grow_one_pt_full_cl_acp_placed_wpp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hgrow_full : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (lsmpl.base 357) (withLsCodeLoaded lsmpl (withAllocCallPreserved (growOnePtFullSpec M A lim))))
    {ret_pc target_pc : BitVec 64} {s0 s : State}
    {Q Qp : State → SepProp → Prop} {F : SepProp}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (v cap ptr : BitVec 64) (vec : List Pt) (st : M.σ)
    (h1 : 1 ≤ vec.length) (hlen : vec.length ≤ 65536)
    (hcap_eq : cap.toNat = vec.length) (hptr : ptr ≠ 0#64)
    (hfits : FitsEvents M lim st (growOnePtEvents vec.length))
    (hpc : s.pc = lsmpl.base 357) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = v) (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hnext : ∀ sf : State, LibsignalCodeLoaded lsmpl sf.mem →
      sf.pc = ret_pc → sf.status = .Running → AllocCallPreserved s sf →
      sf.sp = s.sp → sf.trace = s0.trace → CalleeSavedPreserved s sf →
      SepWPp ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext)) target_pc sf
        (sortedSetPtGrownAt A.repAlloc v vec ∗
          A.pool lim (M.stepEvents (growOnePtEvents vec.length) st) sf ∗
          stackAt s.sp growOneStack ∗ F)
        Q Qp) :
    SepWPp ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext)) target_pc s
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 vec.length) ∗
        A.live ptr (cap.toNat * 4) 2 ∗ ptSliceAt ptr vec ∗
        A.pool lim st s ∗ stackAt s.sp growOneStack ∗ F)
      Q Qp := by
  have hcap_ne0 : cap ≠ 0#64 := by
    intro hc0; subst hc0
    change 0 = vec.length at hcap_eq; omega
  have hbs_len : (ptListBytes vec).length = cap.toNat * 4 := by
    rw [ptListBytes_length, hcap_eq, Nat.mul_comm]
  have hmax_bound : max (2 * cap.toNat) 4 * 4 + 2 ≤ 2 ^ 63 := by omega
  have hevs_eq := growOneStrideEvents_pt_full h1 hcap_eq
  refine sepWPp_call_frozen_noPanic (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl hgrow_full
    (x := ((v, cap, ptr, ptListBytes vec), st))
    (F := ((v + 16#64) ↦₆₄ BitVec.ofNat 64 vec.length) ∗ F)
    hpc hrun hsp hlr ?_ ?_
  · intro R' hm
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    simp only [withAllocCallPreserved, growOnePtFullSpec, growOneStrideFullSpec,
      growOneStrideFullSpecWithStack, hcap_ne0, ↓reduceIte, hbs_len,
      ← ptSliceAt_eq_pointsToBytes, fitsEnv_growOneStride_iff, hevs_eq,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, trivial, hptr, hmax_bound, hfits⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  · intro sf hpc_f hrun_f hsp_f hcs_f hcl_f
    simp only [withLsCodeLoaded, withAllocCallPreserved, growOnePtFullSpec,
      growOneStrideFullSpec, growOneStrideFullSpecWithStack, hevs_eq, sepConj_assoc]
    apply SepWPp.pure_elim; intro hacp_f
    apply SepWPp.pure_elim; intro htr_f
    have hgrown := growOnePtFull_post_entails_grown A.repAlloc v cap vec h1 hcap_eq hlen
    refine SepWPp.weaken_pre ?_
      (hnext sf hcl_f hpc_f hrun_f hacp_f hsp_f (htr_f.trans htr) hcs_f)
    rw [show (∃∗ p' : BitVec 64,
        ⌜p' ≠ 0#64 ∧ p'.toNat % 2 = 0⌝ ∗
        (v ↦₆₄ BitVec.ofNat 64 (max (2 * cap.toNat) 4)) ∗ ((v + 8#64) ↦₆₄ p') ∗
        A.live p' (max (2 * cap.toNat) 4 * 4) 2 ∗ (p' ↦ₛ ptListBytes vec) ∗
        memRegion (p' + BitVec.ofNat 64 (ptListBytes vec).length) ((max (2 * cap.toNat) 4 - cap.toNat) * 4)) ∗
        A.pool lim (M.stepEvents (growOnePtEvents vec.length) st) sf ∗
        stackAt s.sp growOneStack ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 vec.length) ∗ F =
      ((∃∗ p' : BitVec 64,
        ⌜p' ≠ 0#64 ∧ p'.toNat % 2 = 0⌝ ∗
        (v ↦₆₄ BitVec.ofNat 64 (max (2 * cap.toNat) 4)) ∗ ((v + 8#64) ↦₆₄ p') ∗
        (A.repAlloc).live p' (max (2 * cap.toNat) 4 * 4) 2 ∗ (p' ↦ₛ ptListBytes vec) ∗
        memRegion (p' + BitVec.ofNat 64 (ptListBytes vec).length) ((max (2 * cap.toNat) 4 - cap.toNat) * 4)) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 vec.length)) ∗
        (A.pool lim (M.stepEvents (growOnePtEvents vec.length) st) sf ∗
          stackAt s.sp growOneStack ∗ F) by sep_ac_rfl]
    exact sepConj_mono_left hgrown

theorem call_grow_one_pt_empty_cl_acp_placed_wpp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hgrow_empty : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (lsmpl.base 357) (withLsCodeLoaded lsmpl (withAllocCallPreserved (growOnePtSpec M A lim))))
    {ret_pc target_pc : BitVec 64} {s0 s : State}
    {Q Qp : State → SepProp → Prop} {F : SepProp}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (v ptr lenOld : BitVec 64) (st : M.σ) (hptr : ptr ≠ 0#64)
    (hfits : FitsEvents M lim st (growOnePtEvents 0))
    (hpc : s.pc = lsmpl.base 357) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = v) (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hnext : ∀ (sf : State) (p' : BitVec 64), LibsignalCodeLoaded lsmpl sf.mem → p' ≠ 0#64 →
      sf.pc = ret_pc → sf.status = .Running → AllocCallPreserved s sf → sf.sp = s.sp →
      sf.trace = s0.trace → CalleeSavedPreserved s sf →
      SepWPp ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext)) target_pc sf
        ((v ↦₆₄ 4#64) ∗ ((v + 8#64) ↦₆₄ p') ∗ ((v + 16#64) ↦₆₄ lenOld) ∗
          A.live p' 16 2 ∗ memRegion p' 16 ∗
          A.pool lim (M.stepEvents (growOnePtEvents 0) st) sf ∗ stackAt s.sp growOneStack ∗ F)
        Q Qp) :
    SepWPp ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext)) target_pc s
      ((v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ lenOld) ∗
        A.pool lim st s ∗ stackAt s.sp growOneStack ∗ F)
      Q Qp := by
  have hmax_bound : max (2 * (0#64 : BitVec 64).toNat) 4 * 4 + 2 ≤ 2 ^ 63 := by decide
  refine sepWPp_call_frozen_noPanic (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl hgrow_empty
    (x := ((v, 0#64, ptr), st))
    (F := ((v + 16#64) ↦₆₄ lenOld) ∗ F)
    hpc hrun hsp hlr ?_ ?_
  · intro R' hm
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    simp only [withAllocCallPreserved, growOnePtSpec, growOneStrideEmptySpec,
      growOneStrideEmptySpecWithStack, ↓reduceIte, emp_sepConj,
      fitsEnv_growOneStride_iff, growOneStrideEvents_pt_zero,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hptr, hmax_bound, hfits⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  · intro sf hpc_f hrun_f hsp_f hcs_f hcl_f
    have hmax0 : max (2 * (0#64 : BitVec 64).toNat) 4 = 4 := rfl
    simp only [withLsCodeLoaded, withAllocCallPreserved, growOnePtSpec, growOneStrideEmptySpec,
      growOneStrideEmptySpecWithStack, hmax0, growOneStrideEvents_pt_zero,
      sepExists_sepConj_left, sepConj_assoc]
    apply SepWPp.pure_elim; intro hacp_f
    apply SepWPp.pure_elim; intro htr_f
    apply SepWPp.exists_elim; intro p'
    apply SepWPp.pure_elim; rintro ⟨hp', _⟩
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext sf p' hcl_f hp' hpc_f hrun_f hacp_f hsp_f (htr_f.trans htr) hcs_f)

/-! ## 3. Placed `bsearchReplace` (`+236 -> +64`, `withLsCodeLoaded lsmpl`) -/

theorem bsearchReplace_cl_placed_wpp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveSpec growOneStack)))
    (hgrow_full : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (lsmpl.base 357) (withLsCodeLoaded lsmpl (withAllocCallPreserved (growOnePtFullSpec M A lim))))
    {target_pc : BitVec 64} {s0 st : State}
    {Q Qp : State → SepProp → Prop} {F : SepProp}
    (hcl : LibsignalCodeLoaded lsmpl st.mem)
    (v cap ptr : BitVec 64) (s : SortedSetPt) (pt : Pt) (curSt : M.σ)
    (h1 : 1 ≤ s.vec.length) (hlen : s.vec.length ≤ 65536)
    (hle_cap : s.vec.length ≤ cap.toNat) (hcap : cap.toNat * 4 < 2 ^ 63) (hptr : ptr ≠ 0#64)
    (hfits : FitsEnv M lim curSt (AddChunkSlotEnv s))
    (hpc : st.pc = (blkPl_419).base + 236#64) (hrun : st.status = .Running)
    (hsp_al : st.spAligned = true) (htr : st.trace = s0.trace)
    (hx8 : st.readReg64 .x8 = ptr) (hx14 : st.readReg64 .x14 = 1#64) (hx21 : st.readReg64 .x21 = v)
    (hx24 : st.readReg64 .x24 = pt.x.value.zeroExtend 64)
    (hx27 : st.readReg64 .x27 = pt.y.value.zeroExtend 64)
    (hx28 : st.readReg64 .x28 = BitVec.ofNat 64 s.vec.length)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      LibsignalCodeLoaded lsmpl sf.mem → AddChunkSlotEnv s evs →
      sf.pc = (blkPl_419).base + 64#64 → sf.status = .Running →
      AllocCallPreserved st sf → sf.sp = st.sp → sf.trace = s0.trace →
      sf.readReg64 .x14 = 1#64 → sf.readReg64 .x19 = st.readReg64 .x19 →
      sf.readReg64 .x20 = st.readReg64 .x20 → sf.readReg64 .x23 = st.readReg64 .x23 →
      sf.readReg64 .x24 = st.readReg64 .x24 → sf.readReg64 .x25 = st.readReg64 .x25 →
      sf.readReg64 .x29 = st.readReg64 .x29 → calleeSavedVRegs sf = calleeSavedVRegs st →
      SepWPp ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext)) target_pc sf
        (sortedSetPtOf A.repAlloc v (bsearchReplace s pt) ∗
          A.pool lim (M.stepEvents evs curSt) sf ∗ stackAt st.sp growOneStack ∗ F)
        Q Qp) :
    SepWPp ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext)) target_pc st
      (ptSliceAt ptr s.vec ∗
        (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 s.vec.length) ∗
        A.live ptr (cap.toNat * 4) 2 ∗
        memRegion (ptr + BitVec.ofNat 64 (s.vec.length * 4)) ((cap.toNat - s.vec.length) * 4) ∗
        A.pool lim curSt st ∗ stackAt st.sp growOneStack ∗ F)
      Q Qp := by
  apply of_sepWP_lscl hcl (mid := (blkPl_419).base + 296#64)
  refine bsearch_to_296_placed_sepWP h1 (by omega) st _ _ hpc hrun hx8 hx24 hx28
    (fun s1 hpc1 hrun1 hvm1 hacp1 hsp1 htr1 hx8_1 hx9_1 hx14_1 hx19_1 hx20_1 hx21_1 hx23_1 hx24_1 hx25_1 hx27_1 hx28_1 hx29_1 _ hvregs_1 => ?_)
  apply SepWP.done hpc1 hrun1
  intro hcl1
  rw [← A.pool_of_vmPreserved hvm1]
  have htr1' : s1.trace = s0.trace := htr1.trans htr
  have hsp1_al : s1.spAligned = true := by
    unfold State.spAligned at hsp_al ⊢; rwa [hsp1]
  let base := bsearchLoop s.vec pt.x.value 0 s.vec.length
  change s1.readReg64 .x9 = BitVec.ofNat 64 base at hx9_1
  have ⟨_, hb_lt0⟩ := bsearchLoop_bounds s.vec pt.x.value 0 s.vec.length h1 (by omega)
  have hb_lt : base < s.vec.length := by omega
  have hb_get : s.vec[base]?.getD default = s.vec[base]'hb_lt := by
    rw [List.getElem?_eq_getElem hb_lt, Option.getD_some]
  let baseX := (s.vec[base]'hb_lt).x.value
  have hlsl_base : (BitVec.ofNat 64 base) <<< 2 = BitVec.ofNat 64 (4 * base) :=
    bv64_lsl2_ofNat (by omega)
  unfold bsearchReplace at hnext
  dsimp only at hnext
  rw [hb_get] at hnext
  by_cases heq : ((s.vec[base]'hb_lt).x.value == pt.x.value) = true
  · simp only [heq, ↓reduceIte] at hnext
    have hbaseX_eq : (s.vec[base]'hb_lt).x.value = pt.x.value := beq_iff_eq.mp heq
    have hreasm := reassemble_sortedSetPtOf_set A.repAlloc v cap ptr s.vec base pt hb_lt hle_cap hcap hptr
    apply of_sepWP_lscl hcl1 (mid := (blkPl_419).base + 64#64)
    rw [ptSliceAt_focus s.vec base ptr hb_lt]
    unfold ptAt
    apply sepWP_with_vm
    by_vm_steps
      wp_steps 6
      refine SepWP.weaken_pre
        (show (((ptSliceAt ptr (List.take base s.vec) ∗
            ((ptr + BitVec.ofNat 64 (4 * base)) ↦₁₆ (s.vec[base]'hb_lt).x.value ∗
              (ptr + BitVec.ofNat 64 (4 * base) + 2#64) ↦₁₆ pt.y.value) ∗
            ptSliceAt (ptr + BitVec.ofNat 64 (4 * (base + 1))) (List.drop (base + 1) s.vec)) ∗
            (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 s.vec.length) ∗
            A.live ptr (cap.toNat * 4) 2 ∗
            memRegion (ptr + BitVec.ofNat 64 (s.vec.length * 4)) ((cap.toNat - s.vec.length) * 4) ∗
            A.pool lim curSt s1 ∗ stackAt st.sp growOneStack ∗ F)) ⊢
          sortedSetPtOf A.repAlloc v { vec := s.vec.set base pt } ∗
            A.pool lim curSt s1 ∗ stackAt st.sp growOneStack ∗ F by
          rw [hbaseX_eq]
          refine Entails.trans ?_ (sepConj_mono_left hreasm)
          exact Entails.of_eq (by sep_ac_rfl)) ?_
      refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
        ⟨by simp [wp_norm, arm64_norm], fun hvm2 hcl2 => ?_⟩
      rw [← A.pool_of_vmPreserved hvm2]
      refine hnext _ [] hcl2 (Or.inl rfl)
        (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
        (allocCallPreserved_trans hacp1 (by simp [AllocCallPreserved, wp_norm, arm64_norm]))
        (by simpa [wp_norm, arm64_norm] using hsp1) (by simpa [wp_norm, arm64_norm] using htr1')
        (by simpa [wp_norm, arm64_norm, hx14] using hx14_1)
        (by simpa [wp_norm, arm64_norm] using hx19_1) (by simpa [wp_norm, arm64_norm] using hx20_1)
        (by simpa [wp_norm, arm64_norm] using hx23_1) (by simpa [wp_norm, arm64_norm] using hx24_1)
        (by simpa [wp_norm, arm64_norm] using hx25_1) (by simpa [wp_norm, arm64_norm] using hx29_1)
        (by simpa [wp_norm, arm64_norm] using hvregs_1)
  · simp only [heq, Bool.false_eq_true, ↓reduceIte] at hnext
    let insertIdx := if baseX.toNat < pt.x.value.toNat then base + 1 else base
    have hins_le : insertIdx ≤ s.vec.length := by dsimp [insertIdx]; split_ifs <;> omega
    have hfold_slice : ∀ poolP : SepProp,
        ((ptSliceAt ptr (List.take base s.vec) ∗
          ((ptr + BitVec.ofNat 64 (4 * base)) ↦₁₆ (s.vec[base]'hb_lt).x.value ∗
            (ptr + BitVec.ofNat 64 (4 * base) + 2#64) ↦₁₆ (s.vec[base]'hb_lt).y.value) ∗
          ptSliceAt (ptr + BitVec.ofNat 64 (4 * (base + 1))) (List.drop (base + 1) s.vec)) ∗
          (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 s.vec.length) ∗
          A.live ptr (cap.toNat * 4) 2 ∗
          memRegion (ptr + BitVec.ofNat 64 (s.vec.length * 4)) ((cap.toNat - s.vec.length) * 4) ∗
          poolP ∗ stackAt st.sp growOneStack ∗ F) =
        (ptSliceAt ptr s.vec ∗
          (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 s.vec.length) ∗
          A.live ptr (cap.toNat * 4) 2 ∗
          memRegion (ptr + BitVec.ofNat 64 (s.vec.length * 4)) ((cap.toNat - s.vec.length) * 4) ∗
          poolP ∗ stackAt st.sp growOneStack ∗ F) := by
      intro poolP
      change ((ptSliceAt ptr (List.take base s.vec) ∗
        ptAt (s.vec[base]'hb_lt) (ptr + BitVec.ofNat 64 (4 * base)) ∗
        ptSliceAt (ptr + BitVec.ofNat 64 (4 * (base + 1))) (List.drop (base + 1) s.vec)) ∗ _) = _
      rw [← ptSliceAt_focus s.vec base ptr hb_lt]
    by_cases hlt_cap : s.vec.length < cap.toNat
    · have hcap_ne : ¬ s.vec.length = cap.toNat := by omega
      apply of_sepWP_lscl hcl1 (mid := (blkPl_419).base + 336#64)
      rw [ptSliceAt_focus s.vec base ptr hb_lt]
      unfold ptAt
      apply sepWP_with_vm
      by_vm_steps
        wp_steps 4
        rw [bv32_bne_zeroExtend16, show ((s.vec[base]'hb_lt).x.value == pt.x.value) = false from
          Bool.eq_false_iff.mpr heq]
        simp only [Bool.not_false, ↓reduceIte]
        wp_steps 4
        rw [bv64_beq_cap_ofNat (by omega),
          show decide (s.vec.length = cap.toNat) = false from decide_eq_false hcap_ne]
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine SepWP.done (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm, hrun1])
          ⟨by simp [wp_norm, arm64_norm], fun hvm_pre hcl_pre => ?_⟩
        rw [hfold_slice, ← A.pool_of_vmPreserved hvm_pre]
        have hins336 := @bsearch_insert_at_336_acp_placed_sepWP _ M A ext hmemmove_sat v cap ptr
          (BitVec.ofNat 64 s.vec.length) s.vec insertIdx pt hins_le hlt_cap hcap hptr
        apply of_sepWP_lscl hcl_pre (mid := (blkPl_419).base + 64#64)
        refine SepWP.weaken_pre (by rw [← hsp1]; exact Entails.of_eq (by sep_ac_rfl))
          (hins336 _ (A.pool lim curSt _ ∗ F) _
            (by simp [wp_norm, arm64_norm])
            (by simp [wp_norm, arm64_norm, hrun1])
            (by simpa [wp_norm, arm64_norm] using hsp1_al)
            (by simp [wp_norm, arm64_norm, hx8_1])
            (by simp [wp_norm, arm64_norm, hx14_1, hx14])
            (by simp [wp_norm, arm64_norm, hx21_1, hx21])
            (by simp [wp_norm, arm64_norm, hx24_1, hx24])
            (by simp only [wp_norm, arm64_norm]; exact cinc_insertIdx_eq baseX pt.x.value base)
            (by simp [wp_norm, arm64_norm, hx27_1, hx27])
            (by simp [wp_norm, arm64_norm, hx28_1, hx28])
            (fun sf hpc_f hrun_f hvm_f hacp_f hsp_f htr_f hx14_f hx19_f hx20_f hx23_f hx24_f hx25_f hx29_f hvregs_f => ?_))
        apply SepWP.done hpc_f hrun_f
        intro hcl_f
        rw [← A.pool_of_vmPreserved hvm_f]
        have hsp_f' : sf.sp = st.sp := by
          simpa [wp_norm, arm64_norm, hsp1] using hsp_f
        rw [← hsp_f, hsp_f']
        refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
          (hnext sf [] hcl_f (Or.inl rfl) hpc_f hrun_f
            (allocCallPreserved_trans hacp1
              (allocCallPreserved_trans (by simp [AllocCallPreserved, wp_norm, arm64_norm]) hacp_f))
            hsp_f'
            (by simpa [wp_norm, arm64_norm, htr1'] using htr_f)
            hx14_f
            (by simpa [wp_norm, arm64_norm, hx19_1] using hx19_f)
            (by simpa [wp_norm, arm64_norm, hx20_1] using hx20_f)
            (by simpa [wp_norm, arm64_norm, hx23_1] using hx23_f)
            (by simpa [wp_norm, arm64_norm, hx24_1] using hx24_f)
            (by simpa [wp_norm, arm64_norm, hx25_1] using hx25_f)
            (by simpa [wp_norm, arm64_norm, hx29_1] using hx29_f)
            (by simpa [wp_norm, arm64_norm, hvregs_1] using hvregs_f))
    · have hcap_eq : cap.toNat = s.vec.length := by omega
      have hfits_grow : FitsEvents M lim curSt (growOnePtEvents s.vec.length) :=
        hfits _ (Or.inr rfl)
      have hcall := @call_grow_one_pt_full_cl_acp_placed_wpp _ M A lim ext hgrow_full
        ((blkPl_419).base + 452#64) target_pc s0
      have hins452 := @bsearch_insert_at_452_acp_placed_sepWP _ M A ext hmemmove_sat v s.vec insertIdx pt hins_le
      apply of_sepWP_lscl hcl1 (mid := lsmpl.base 357)
      rw [ptSliceAt_focus s.vec base ptr hb_lt]
      unfold ptAt
      apply sepWP_with_vm
      by_vm_steps
        wp_steps 4
        rw [bv32_bne_zeroExtend16, show ((s.vec[base]'hb_lt).x.value == pt.x.value) = false from
          Bool.eq_false_iff.mpr heq]
        simp only [Bool.not_false, ↓reduceIte]
        wp_steps 4
        rw [hfold_slice, bv64_beq_cap_ofNat (by omega),
          show decide (s.vec.length = cap.toNat) = true from decide_eq_true (by omega)]
        simp only [↓reduceIte]
        wp_steps 2
        refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
          ⟨by simp [wp_norm, arm64_norm], fun hvm_pre hcl_pre => ?_⟩
        rw [← A.pool_of_vmPreserved hvm_pre]
        have hmem_zero :
            memRegion (ptr + BitVec.ofNat 64 (s.vec.length * 4)) ((cap.toNat - s.vec.length) * 4) = emp := by
          rw [hcap_eq, Nat.sub_self, Nat.zero_mul, memRegion_zero]
        rw [hmem_zero, ← hsp1]
        simp only [emp_sepConj]
        refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
          (hcall (F := F) hcl_pre v cap ptr s.vec curSt h1 hlen hcap_eq hptr hfits_grow
            (by simp [wp_norm, arm64_norm])
            (by simp [wp_norm, arm64_norm, hrun1])
            (by simpa [wp_norm, arm64_norm] using hsp1_al)
            (by simp [wp_norm, arm64_norm])
            (by simp [wp_norm, arm64_norm])
            (by simpa [wp_norm, arm64_norm] using htr1')
            (fun s2 hcl_s2 hpc2 hrun2 hacp2 hsp2 htr2 hcs2 => ?_))
        have hsp2' : s2.sp = st.sp := by
          rw [hsp2]; simpa [wp_norm, arm64_norm] using hsp1
        have hsp2_al : s2.spAligned = true := by
          unfold State.spAligned at hsp_al ⊢; rwa [hsp2']
        rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, _, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hvregs_2⟩
        have hx26_s2 : s2.readReg64 .x26 = BitVec.ofNat 64 insertIdx := by
          rw [hx26_2]
          simp only [wp_norm, arm64_norm]
          exact cinc_insertIdx_eq baseX pt.x.value base
        rw [← hsp2]
        apply of_sepWP_lscl hcl_s2 (mid := (blkPl_419).base + 64#64)
        refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
          (hins452 s2 (A.pool lim (M.stepEvents (growOnePtEvents s.vec.length) curSt) s2 ∗ F) _
            hpc2 hrun2 hsp2_al
            (by rw [hx21_2]; simpa [wp_norm, arm64_norm, hx21] using hx21_1)
            (by rw [hx24_2]; simpa [wp_norm, arm64_norm, hx24] using hx24_1)
            hx26_s2
            (by rw [hx27_2]; simpa [wp_norm, arm64_norm, hx27] using hx27_1)
            (by rw [hx28_2]; simpa [wp_norm, arm64_norm, hx28] using hx28_1)
            (fun sf hpc_f hrun_f hvm_f hacp_f hsp_f htr_f hx14_f hx19_f hx20_f hx23_f hx24_f hx25_f hx29_f hvregs_f => ?_))
        apply SepWP.done hpc_f hrun_f
        intro hcl_f
        rw [← A.pool_of_vmPreserved hvm_f, hsp2']
        refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
          (hnext sf (growOnePtEvents s.vec.length) hcl_f (Or.inr rfl) hpc_f hrun_f
            (allocCallPreserved_trans hacp1
              (allocCallPreserved_trans (by simp [AllocCallPreserved, wp_norm, arm64_norm])
                (allocCallPreserved_trans hacp2 hacp_f)))
            (hsp_f.trans hsp2') (htr_f.trans htr2) hx14_f
            (by rw [hx19_f, hx19_2]; simpa [wp_norm, arm64_norm] using hx19_1)
            (by rw [hx20_f, hx20_2]; simpa [wp_norm, arm64_norm] using hx20_1)
            (by rw [hx23_f, hx23_2]; simpa [wp_norm, arm64_norm] using hx23_1)
            (by rw [hx24_f, hx24_2]; simpa [wp_norm, arm64_norm] using hx24_1)
            (by rw [hx25_f, hx25_2]; simpa [wp_norm, arm64_norm] using hx25_1)
            (by rw [hx29_f, hx29_2]; simpa [wp_norm, arm64_norm] using hx29_1)
            (by rw [hvregs_f, hvregs_2]; simpa [wp_norm, arm64_norm] using hvregs_1))

/-! ## 4. Placed `bsearchPush` (`+128 -> +64`, `withLsCodeLoaded lsmpl`) -/

theorem bsearchPush_cl_placed_wpp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveSpec growOneStack)))
    (hgrow_full : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (lsmpl.base 357) (withLsCodeLoaded lsmpl (withAllocCallPreserved (growOnePtFullSpec M A lim))))
    (hgrow_empty : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (lsmpl.base 357) (withLsCodeLoaded lsmpl (withAllocCallPreserved (growOnePtSpec M A lim))))
    {target_pc : BitVec 64} {s0 st : State}
    {Q Qp : State → SepProp → Prop} {F : SepProp}
    (hcl : LibsignalCodeLoaded lsmpl st.mem)
    (v : BitVec 64) (s : SortedSetPt) (pt : Pt) (curSt : M.σ)
    (hlen : s.vec.length ≤ 65536)
    (hfits : FitsEnv M lim curSt (AddChunkSlotEnv s))
    (hpc : st.pc = (blkPl_419).base + 128#64) (hrun : st.status = .Running)
    (hsp_al : st.spAligned = true) (htr : st.trace = s0.trace)
    (hx14 : st.readReg64 .x14 = 1#64) (hx21 : st.readReg64 .x21 = v)
    (hx24 : st.readReg64 .x24 = pt.x.value.zeroExtend 64)
    (hx27 : st.readReg64 .x27 = pt.y.value.zeroExtend 64)
    (hx28 : st.readReg64 .x28 = BitVec.ofNat 64 s.vec.length)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      LibsignalCodeLoaded lsmpl sf.mem → AddChunkSlotEnv s evs →
      sf.pc = (blkPl_419).base + 64#64 → sf.status = .Running →
      AllocCallPreserved st sf → sf.sp = st.sp → sf.trace = s0.trace →
      sf.readReg64 .x14 = 1#64 → sf.readReg64 .x19 = st.readReg64 .x19 →
      sf.readReg64 .x20 = st.readReg64 .x20 → sf.readReg64 .x23 = st.readReg64 .x23 →
      sf.readReg64 .x24 = st.readReg64 .x24 → sf.readReg64 .x25 = st.readReg64 .x25 →
      sf.readReg64 .x29 = st.readReg64 .x29 → calleeSavedVRegs sf = calleeSavedVRegs st →
      SepWPp ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext)) target_pc sf
        (sortedSetPtOf A.repAlloc v (bsearchPush s pt) ∗
          A.pool lim (M.stepEvents evs curSt) sf ∗ stackAt st.sp growOneStack ∗ F)
        Q Qp) :
    SepWPp ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext)) target_pc st
      (sortedSetPtOf A.repAlloc v s ∗ A.pool lim curSt st ∗ stackAt st.sp growOneStack ∗ F)
      Q Qp := by
  refine SepWPp.weaken_pre (sepConj_mono_left (sortedSetPtOf_expose A.repAlloc v s)) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWPp.exists_elim; intro cap
  apply SepWPp.exists_elim; intro ptr
  apply SepWPp.pure_elim; rintro ⟨hle_cap, hcap, hptr⟩
  rcases Nat.eq_zero_or_pos s.vec.length with hlen0 | h1
  · have hvec_nil : s.vec = [] := List.eq_nil_of_length_eq_zero hlen0
    have hpush_nil : bsearchPush s pt = { vec := [pt] } := by
      unfold bsearchPush; rw [hvec_nil]; rfl
    rw [hpush_nil] at hnext
    rw [hlen0] at hx28
    have hslice_nil : ptSliceAt ptr [] = emp := rfl
    simp only [hvec_nil, List.length_nil, Nat.zero_mul, Nat.sub_zero,
      BitVec.add_zero, hslice_nil, emp_sepConj]
    by_cases hcap0 : cap = 0#64
    · subst hcap0
      simp only [↓reduceIte, emp_sepConj]
      have hfits_empty : FitsEvents M lim curSt (growOnePtEvents 0) := by
        rw [← hlen0]; exact hfits _ (Or.inr rfl)
      have hslot_empty : AddChunkSlotEnv s (growOnePtEvents 0) := by
        right; rw [hlen0]
      have hcall := @call_grow_one_pt_empty_cl_acp_placed_wpp _ M A lim ext hgrow_empty
        ((blkPl_419).base + 396#64) target_pc s0
      have hpush216 := @bsearch_push_empty_at_216_placed_sepWP _ M A ext v 4#64
      apply of_sepWP_lscl hcl (mid := lsmpl.base 357)
      apply sepWP_with_vm
      by_vm_steps
        wp_steps 5
        refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
          ⟨by simp [wp_norm, arm64_norm], fun hvm1 hcl1 => ?_⟩
        rw [← A.pool_of_vmPreserved hvm1]
        refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
          (hcall (F := F) hcl1 v ptr 0#64 curSt hptr hfits_empty
            (by simp [wp_norm, arm64_norm])
            (by simp [wp_norm, arm64_norm, hrun])
            (by simpa [wp_norm, arm64_norm] using hsp_al)
            (by simp [wp_norm, arm64_norm])
            (by simp [wp_norm, arm64_norm])
            (by simpa [wp_norm, arm64_norm] using htr)
            (fun s2 p' hcl_s2 hp' hpc2 hrun2 hacp2 hsp2 htr2 hcs2 => ?_))
        have hsp2' : s2.sp = st.sp := by simpa [wp_norm, arm64_norm] using hsp2
        rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, _, hx23_2, hx24_2, hx25_2, _, hx27_2, _, hx29_2, hvregs_2⟩
        rw [← hsp2]
        apply of_sepWP_lscl hcl_s2 (mid := (blkPl_419).base + 216#64)
        apply sepWP_with_vm
        by_vm_steps
          wp_steps 2
          refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun2])
            ⟨by simp [wp_norm, arm64_norm], fun hvm_mid hcl_mid => ?_⟩
          rw [← A.pool_of_vmPreserved hvm_mid]
          have h4_16 : (4#64 : BitVec 64).toNat * 4 = 16 := rfl
          apply of_sepWP_lscl hcl_mid (mid := (blkPl_419).base + 64#64)
          refine SepWP.weaken_pre (by rw [h4_16]; exact Entails.of_eq (by sep_ac_rfl))
            (hpush216 p' 0#64 pt (by decide) (by decide) hp' _
              (A.pool lim (M.stepEvents (growOnePtEvents 0) curSt) _ ∗ stackAt s2.sp growOneStack ∗ F) _
              (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun2])
              (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hx21_2, hx21])
              (by simp [wp_norm, arm64_norm, hx24_2, hx24]) (by simp [wp_norm, arm64_norm, hx27_2, hx27])
              (fun sf hpc_f hrun_f hvm_f hacp_f hsp_f htr_f hx14_f hx19_f hx20_f hx23_f hx24_f hx25_f hx29_f hvregs_f => ?_))
          apply SepWP.done hpc_f hrun_f; intro hcl_f
          rw [← A.pool_of_vmPreserved hvm_f]
          have hsp_f' : sf.sp = st.sp := by simpa [wp_norm, arm64_norm, hsp2'] using hsp_f
          rw [hsp2']
          refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
            (hnext sf (growOnePtEvents 0) hcl_f hslot_empty hpc_f hrun_f
              (allocCallPreserved_trans (by simp [AllocCallPreserved, wp_norm, arm64_norm])
                (allocCallPreserved_trans hacp2
                  (allocCallPreserved_trans (by simp [AllocCallPreserved, wp_norm, arm64_norm]) hacp_f)))
              hsp_f' (by simpa [wp_norm, arm64_norm, htr2] using htr_f) hx14_f
              (by simpa [wp_norm, arm64_norm, hx19_2] using hx19_f) (by simpa [wp_norm, arm64_norm, hx20_2] using hx20_f)
              (by simpa [wp_norm, arm64_norm, hx23_2] using hx23_f) (by simpa [wp_norm, arm64_norm, hx24_2] using hx24_f)
              (by simpa [wp_norm, arm64_norm, hx25_2] using hx25_f) (by simpa [wp_norm, arm64_norm, hx29_2] using hx29_f)
              (by simpa [wp_norm, arm64_norm, hvregs_2] using hvregs_f))
    · simp only [hcap0, ↓reduceIte]
      have hlt0 : 0 < cap.toNat := by
        by_contra hle0
        apply hcap0
        apply BitVec.eq_of_toNat_eq
        change cap.toNat = 0; omega
      have hbeq0 : (cap == 0#64) = false := beq_false_of_ne hcap0
      have hpush216 := @bsearch_push_empty_at_216_placed_sepWP _ M A ext v cap ptr 0#64 pt hlt0 hcap hptr
      apply of_sepWP_lscl hcl (mid := (blkPl_419).base + 216#64)
      apply sepWP_with_vm
      by_vm_steps
        wp_steps 3
        refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
          ⟨by simp [wp_norm, arm64_norm], fun hvm1 hcl1 => ?_⟩
        rw [← A.pool_of_vmPreserved hvm1]
        apply of_sepWP_lscl hcl1 (mid := (blkPl_419).base + 64#64)
        refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
          (hpush216 _ (A.pool lim curSt _ ∗ stackAt st.sp growOneStack ∗ F) _
            (by simp [wp_norm, arm64_norm])
            (by simp [wp_norm, arm64_norm, hrun])
            (by simp [wp_norm, arm64_norm, hx14])
            (by simp [wp_norm, arm64_norm, hx21])
            (by simp [wp_norm, arm64_norm, hx24])
            (by simp [wp_norm, arm64_norm, hx27])
            (fun sf hpc_f hrun_f hvm_f hacp_f hsp_f htr_f hx14_f hx19_f hx20_f hx23_f hx24_f hx25_f hx29_f hvregs_f => ?_))
        apply SepWP.done hpc_f hrun_f
        intro hcl_f
        rw [← A.pool_of_vmPreserved hvm_f]
        refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
          (hnext sf [] hcl_f (Or.inl rfl) hpc_f hrun_f
            (allocCallPreserved_trans (by simp [AllocCallPreserved, wp_norm, arm64_norm]) hacp_f)
            (by simpa [wp_norm, arm64_norm] using hsp_f)
            (by simpa [wp_norm, arm64_norm, htr] using htr_f)
            hx14_f
            (by simpa [wp_norm, arm64_norm] using hx19_f)
            (by simpa [wp_norm, arm64_norm] using hx20_f)
            (by simpa [wp_norm, arm64_norm] using hx23_f)
            (by simpa [wp_norm, arm64_norm] using hx24_f)
            (by simpa [wp_norm, arm64_norm] using hx25_f)
            (by simpa [wp_norm, arm64_norm] using hx29_f)
            (by simpa [wp_norm, arm64_norm] using hvregs_f))
  · have hcap0 : cap ≠ 0#64 := by
      intro hc; subst hc
      have h0 : (0#64 : BitVec 64).toNat = 0 := rfl
      omega
    simp only [hcap0, ↓reduceIte]
    let lastIdx := s.vec.length - 1
    have hlast_lt : lastIdx < s.vec.length := by omega
    let lastPt := s.vec[lastIdx]'hlast_lt
    have hlast_eq : s.vec.getLast? = some lastPt := by
      rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem hlast_lt]
    have hne0 : (BitVec.ofNat 64 s.vec.length == 0#64) = false := bv64_ne_zero_of_pos h1 hlen
    have hlsl_len : (BitVec.ofNat 64 s.vec.length) <<< 2 = BitVec.ofNat 64 (4 * s.vec.length) :=
      bv64_lsl2_ofNat (by omega)
    have hsub4 := ptr_add_len_sub4 ptr h1 hlen
    have hsub2 := ptr_add_len_sub2 ptr h1 hlen
    unfold bsearchPush at hnext
    rw [hlast_eq] at hnext
    dsimp only at hnext
    cases hcmp : Pt.cmp pt lastPt with
    | eq =>
      rw [hcmp] at hnext
      dsimp only at hnext
      have hset_eq : s.vec.dropLast ++ [pt] = s.vec.set lastIdx pt :=
        dropLast_append_singleton_eq_set s.vec pt h1
      rw [hset_eq] at hnext
      have hcmp' : pt.x.value.toNat = (s.vec[lastIdx]'hlast_lt).x.value.toNat :=
        compare_eq_iff_eq.mp hcmp
      have hule1 :
          (BitVec.zeroExtend 32 (s.vec[lastIdx]'hlast_lt).x.value).ule
            (BitVec.zeroExtend 32 pt.x.value) = true := by
        rw [bv32_ule_zeroExtend16, decide_eq_true_eq]; omega
      have hule2 :
          (BitVec.zeroExtend 32 pt.x.value).ule
            (BitVec.zeroExtend 32 (s.vec[lastIdx]'hlast_lt).x.value) = true := by
        rw [bv32_ule_zeroExtend16, decide_eq_true_eq]; omega
      apply of_sepWP_lscl hcl (mid := (blkPl_419).base + 64#64)
      rw [ptSliceAt_focus s.vec lastIdx ptr hlast_lt]
      unfold ptAt
      rw [← hsub2, ← hsub4]
      apply sepWP_with_vm
      by_vm_steps
        wp_steps 11
        refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
          ⟨by simp [wp_norm, arm64_norm], fun hvm hcl1 => ?_⟩
        rw [hsub4, hsub2, ← A.pool_of_vmPreserved hvm]
        have hreasm := reassemble_sortedSetPtOf_set A.repAlloc v cap ptr s.vec lastIdx pt hlast_lt hle_cap hcap hptr
        refine SepWPp.weaken_pre
          (P' := sortedSetPtOf A.repAlloc v { vec := s.vec.set lastIdx pt } ∗
            A.pool lim curSt _ ∗ stackAt st.sp growOneStack ∗ F)
          (by refine Entails.trans ?_ (sepConj_mono_left hreasm)
              exact Entails.of_eq (by sep_ac_rfl))
          (hnext _ [] hcl1 (Or.inl rfl)
            (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
            (by simp [AllocCallPreserved, wp_norm, arm64_norm])
            (by simp [wp_norm, arm64_norm]) (by simpa [wp_norm, arm64_norm] using htr)
            (by simp [wp_norm, arm64_norm, hx14]) (by simp [wp_norm, arm64_norm])
            (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
            (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
            (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]))
    | lt =>
      rw [hcmp] at hnext
      dsimp only at hnext
      have hcmp' : pt.x.value.toNat < (s.vec[lastIdx]'hlast_lt).x.value.toNat :=
        compare_lt_iff_lt.mp hcmp
      have hule1 :
          (BitVec.zeroExtend 32 (s.vec[lastIdx]'hlast_lt).x.value).ule
            (BitVec.zeroExtend 32 pt.x.value) = false := by
        rw [bv32_ule_zeroExtend16, decide_eq_false_iff_not]; omega
      have hrep := @bsearchReplace_cl_placed_wpp _ M A lim ext hmemmove_sat hgrow_full target_pc s0
      apply of_sepWP_lscl hcl (mid := (blkPl_419).base + 236#64)
      rw [ptSliceAt_focus s.vec lastIdx ptr hlast_lt]
      unfold ptAt
      rw [← hsub2, ← hsub4]
      apply sepWP_with_vm
      by_vm_steps
        wp_steps 11
        refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
          ⟨by simp [wp_norm, arm64_norm], fun hvm1 hcl1 => ?_⟩
        rw [hsub4, hsub2, ← A.pool_of_vmPreserved hvm1]
        have hfold_slice :
            ptSliceAt ptr (s.vec.take lastIdx) ∗
              (((ptr + BitVec.ofNat 64 (4 * lastIdx)) ↦₁₆ (s.vec[lastIdx]'hlast_lt).x.value) ∗
                ((ptr + BitVec.ofNat 64 (4 * lastIdx) + 2#64) ↦₁₆ (s.vec[lastIdx]'hlast_lt).y.value)) ∗
              ptSliceAt (ptr + BitVec.ofNat 64 (4 * (lastIdx + 1))) (s.vec.drop (lastIdx + 1)) =
            ptSliceAt ptr s.vec := by
          rw [ptSliceAt_focus s.vec lastIdx ptr hlast_lt]; rfl
        rw [hfold_slice]
        refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
          (hrep (F := F) hcl1 v cap ptr s pt curSt h1 hlen hle_cap hcap hptr hfits
            (by simp [wp_norm, arm64_norm])
            (by simp [wp_norm, arm64_norm, hrun])
            (by simpa [wp_norm, arm64_norm] using hsp_al)
            (by simpa [wp_norm, arm64_norm] using htr)
            (by simp [wp_norm, arm64_norm])
            (by simp [wp_norm, arm64_norm, hx14])
            (by simp [wp_norm, arm64_norm, hx21])
            (by simp [wp_norm, arm64_norm, hx24])
            (by simp [wp_norm, arm64_norm, hx27])
            (by simp [wp_norm, arm64_norm, hx28])
            (fun sf evs hcl_f hevs hpc_f hrun_f hacp_f hsp_f htr_f hx14_f hx19_f hx20_f hx23_f hx24_f hx25_f hx29_f hvregs_f => ?_))
        have hsp_f' : sf.sp = st.sp := by
          simpa [wp_norm, arm64_norm] using hsp_f
        simp only [wp_norm, arm64_norm]
        refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
          (hnext sf evs hcl_f hevs hpc_f hrun_f
            (allocCallPreserved_trans (by simp [AllocCallPreserved, wp_norm, arm64_norm]) hacp_f)
            hsp_f' htr_f hx14_f
            (by simpa [wp_norm, arm64_norm] using hx19_f)
            (by simpa [wp_norm, arm64_norm] using hx20_f)
            (by simpa [wp_norm, arm64_norm] using hx23_f)
            (by simpa [wp_norm, arm64_norm] using hx24_f)
            (by simpa [wp_norm, arm64_norm] using hx25_f)
            (by simpa [wp_norm, arm64_norm] using hx29_f)
            (by simpa [wp_norm, arm64_norm] using hvregs_f))
    | gt =>
      rw [hcmp] at hnext
      dsimp only at hnext
      have hcmp' : (s.vec[lastIdx]'hlast_lt).x.value.toNat < pt.x.value.toNat :=
        compare_gt_iff_gt.mp hcmp
      have hule1 :
          (BitVec.zeroExtend 32 (s.vec[lastIdx]'hlast_lt).x.value).ule
            (BitVec.zeroExtend 32 pt.x.value) = true := by
        rw [bv32_ule_zeroExtend16, decide_eq_true_eq]; omega
      have hule2 :
          (BitVec.zeroExtend 32 pt.x.value).ule
            (BitVec.zeroExtend 32 (s.vec[lastIdx]'hlast_lt).x.value) = false := by
        rw [bv32_ule_zeroExtend16, decide_eq_false_iff_not]; omega
      have hfold_slice :
          ptSliceAt ptr (s.vec.take lastIdx) ∗
            (((ptr + BitVec.ofNat 64 (4 * lastIdx)) ↦₁₆ (s.vec[lastIdx]'hlast_lt).x.value) ∗
              ((ptr + BitVec.ofNat 64 (4 * lastIdx) + 2#64) ↦₁₆ (s.vec[lastIdx]'hlast_lt).y.value)) ∗
            ptSliceAt (ptr + BitVec.ofNat 64 (4 * (lastIdx + 1))) (s.vec.drop (lastIdx + 1)) =
          ptSliceAt ptr s.vec := by
        rw [ptSliceAt_focus s.vec lastIdx ptr hlast_lt]; rfl
      by_cases hlt_cap : s.vec.length < cap.toNat
      · have hbeq_cap : (BitVec.ofNat 64 s.vec.length == cap) = false := by
          rw [bv64_beq_cap_ofNat (by omega), decide_eq_false_iff_not]; omega
        have hule_succ :
            (BitVec.ofNat 64 s.vec.length).ule (BitVec.ofNat 64 (s.vec.length + 1)) = true :=
          bv64_ule_succ (by omega)
        apply of_sepWP_lscl hcl (mid := (blkPl_419).base + 64#64)
        rw [ptSliceAt_focus s.vec lastIdx ptr hlast_lt]
        unfold ptAt
        rw [← hsub2, ← hsub4]
        rw [memRegion_spare_split_one ptr hlt_cap hcap]
        wp_pull_exists
        rename_i v1 v0
        apply sepWP_with_vm
        by_vm_steps
          wp_steps 19
          refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
            ⟨by simp [wp_norm, arm64_norm], fun hvm hcl1 => ?_⟩
          rw [hsub4, hsub2, ← A.pool_of_vmPreserved hvm]
          have hreasm := reassemble_sortedSetPtOf_snoc A.repAlloc v cap ptr s.vec pt hlt_cap hcap hptr
          rw [← hfold_slice] at hreasm
          refine SepWPp.weaken_pre
            (P' := sortedSetPtOf A.repAlloc v { vec := s.vec ++ [pt] } ∗
              A.pool lim curSt _ ∗ stackAt st.sp growOneStack ∗ F)
            (by refine Entails.trans ?_ (sepConj_mono_left hreasm)
                exact Entails.of_eq (by sep_ac_rfl))
            (hnext _ [] hcl1 (Or.inl rfl)
              (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
              (by simp [AllocCallPreserved, wp_norm, arm64_norm])
              (by simp [wp_norm, arm64_norm]) (by simpa [wp_norm, arm64_norm] using htr)
              (by simp [wp_norm, arm64_norm, hx14]) (by simp [wp_norm, arm64_norm])
              (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
              (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
              (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]))
      · have hbeq_cap : (BitVec.ofNat 64 s.vec.length == cap) = true := by
          rw [bv64_beq_cap_ofNat (by omega), decide_eq_true_eq]; omega
        have hcap_eq : cap.toNat = s.vec.length := by omega
        have hfits_grow : FitsEvents M lim curSt (growOnePtEvents s.vec.length) :=
          hfits _ (Or.inr rfl)
        have hcall := @call_grow_one_pt_full_cl_acp_placed_wpp _ M A lim ext hgrow_full
          ((blkPl_419).base + 412#64) target_pc s0
        have hgrown := @bsearch_push_grown_at_412_placed_sepWP _ M A ext v s.vec pt
        apply of_sepWP_lscl hcl (mid := lsmpl.base 357)
        rw [ptSliceAt_focus s.vec lastIdx ptr hlast_lt]
        unfold ptAt
        rw [← hsub2, ← hsub4]
        apply sepWP_with_vm
        by_vm_steps
          wp_steps 16
          refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
            ⟨by simp [wp_norm, arm64_norm], fun hvm1 hcl1 => ?_⟩
          rw [hsub4, hsub2, hfold_slice, ← A.pool_of_vmPreserved hvm1]
          have hmem_zero :
              memRegion (ptr + BitVec.ofNat 64 (s.vec.length * 4)) ((cap.toNat - s.vec.length) * 4) = emp := by
            rw [hcap_eq, Nat.sub_self, Nat.zero_mul, memRegion_zero]
          rw [hmem_zero]
          refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
            (hcall (F := F) hcl1 v cap ptr s.vec curSt h1 hlen hcap_eq hptr hfits_grow
              (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
              (by simpa [wp_norm, arm64_norm] using hsp_al) (by simp [wp_norm, arm64_norm])
              (by simp [wp_norm, arm64_norm]) (by simpa [wp_norm, arm64_norm] using htr)
              (fun s2 hcl_s2 hpc2 hrun2 hacp2 hsp2 htr2 hcs2 => ?_))
          have hsp2' : s2.sp = st.sp := by simpa [wp_norm, arm64_norm] using hsp2
          rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, _, hx23_2, hx24_2, hx25_2, _, hx27_2, hx28_2, hx29_2, hvregs_2⟩
          rw [← hsp2]
          apply of_sepWP_lscl hcl_s2 (mid := (blkPl_419).base + 64#64)
          refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
            (hgrown s2 (A.pool lim (M.stepEvents (growOnePtEvents s.vec.length) curSt) s2 ∗ stackAt s2.sp growOneStack ∗ F) _
              hpc2 hrun2
              (by rw [hx21_2]; simp [wp_norm, arm64_norm, hx21]) (by rw [hx24_2]; simp [wp_norm, arm64_norm, hx24])
              (by rw [hx27_2]; simp [wp_norm, arm64_norm, hx27]) (by rw [hx28_2]; simp [wp_norm, arm64_norm, hx28])
              (fun sf hpc_f hrun_f hvm_f hacp_f hsp_f htr_f hx14_f hx19_f hx20_f hx23_f hx24_f hx25_f hx29_f hvregs_f => ?_))
          apply SepWP.done hpc_f hrun_f; intro hcl_f
          rw [← A.pool_of_vmPreserved hvm_f]
          have hsp_f' : sf.sp = st.sp := by simpa [wp_norm, arm64_norm, hsp2'] using hsp_f
          rw [hsp2']
          refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
            (hnext sf (growOnePtEvents s.vec.length) hcl_f (Or.inr rfl) hpc_f hrun_f
              (allocCallPreserved_trans (by simp [AllocCallPreserved, wp_norm, arm64_norm])
                (allocCallPreserved_trans hacp2 hacp_f))
              hsp_f' (by simpa [wp_norm, arm64_norm, htr2] using htr_f) hx14_f
              (by rw [hx19_f, hx19_2]; simp [wp_norm, arm64_norm]) (by rw [hx20_f, hx20_2]; simp [wp_norm, arm64_norm])
              (by rw [hx23_f, hx23_2]; simp [wp_norm, arm64_norm]) (by rw [hx24_f, hx24_2]; simp [wp_norm, arm64_norm])
              (by rw [hx25_f, hx25_2]; simp [wp_norm, arm64_norm]) (by rw [hx29_f, hx29_2]; simp [wp_norm, arm64_norm])
              (by rw [hvregs_f, hvregs_2]; simp [wp_norm, arm64_norm]))

end LibsignalBinary.Proofs.SpqrV1.States.Leaves.AddChunkCl1PlacedBudgetAux

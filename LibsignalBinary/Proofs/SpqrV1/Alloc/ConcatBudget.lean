/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Alloc.Fetch
import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]` (Block 386)

Re-exports 2-slice budget concatenation from `ConcatBudgetAux` and proves relocatable
`RustCliAllocBudget M` / `AllocCallPreserved` 3-slice concatenation contracts for block 386.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement blkPC_386 blkPl_386 lsρ)
open CryptoVerification.RustHeap (allocHookStack vecU8At)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt)
open CryptoVerification.SpqrV1.Alloc (
  SliceConcat3Ghost
  spqrMemcpySym spqrRustAllocSym spqrRustNoAllocShimSym
  spqr_externAt?_of_mem spqr_hook_ok_of_mem
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents
  RustCliAllocBudget RustLayoutOk
  rustAllocEvents rustCliAllocBudgetSpec
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  rustCliAllocNoOomSpecWithStack
  subroutine_ok_allocNoOom_withStack_of_hookSat
)
open LibsignalBinary.Proofs.SpqrV1.Alloc.FinishGrowBudget (memRegion_24)
open LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux (
  acp_chain_acp ofNat_beq_zero_false ofNat_getElem_63_false ofNat_getLsbD_63_false
  ofNat_ult_of_le pointsToBytes_append3 session2MemcpyAcpWithStack_of_frameless
  session2ShimAcpWithStack_of_rustAllocShimVm sessionMemcpyRegionROWithStack_of_ro
  session_memcpy_bytesAt_ok_at stackAt_concat_gen stackAt_extHookStack_eq_concatStack
  vecU8At_of_append3_pos vecU8At_of_append_pos vecU8At_of_pos vecU8At_of_zero
)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Re-Exports from `ConcatBudgetAux` -/

abbrev vecU8_of_exists_vecU8At := @ConcatBudgetAux.vecU8_of_exists_vecU8At
abbrev hookNoop_rustAllocShimVm_ok := ConcatBudgetAux.hookNoop_rustAllocShimVm_ok
abbrev session2ShimAcpSpecWithStack := ConcatBudgetAux.session2ShimAcpSpecWithStack
abbrev framelessMemcpyAcpSpec := ConcatBudgetAux.framelessMemcpyAcpSpec
abbrev hookMemcpy_framelessMemcpyAcp_ok := ConcatBudgetAux.hookMemcpy_framelessMemcpyAcp_ok
abbrev framelessMemcpyAcp_of_allocMemcpyVm := @ConcatBudgetAux.framelessMemcpyAcp_of_allocMemcpyVm
abbrev session2MemcpyAcpSpecWithStack := ConcatBudgetAux.session2MemcpyAcpSpecWithStack
abbrev sessionMemcpyRegionROSpec := ConcatBudgetAux.sessionMemcpyRegionROSpec
abbrev hookMemcpy_region_ro_trace_ok := ConcatBudgetAux.hookMemcpy_region_ro_trace_ok
abbrev sessionMemcpyRegionROSpecWithStack := ConcatBudgetAux.sessionMemcpyRegionROSpecWithStack
abbrev sessionMemcpyRegionROSpecX := ConcatBudgetAux.sessionMemcpyRegionROSpecX
abbrev sessionMemcpyBytesAtSpec := ConcatBudgetAux.sessionMemcpyBytesAtSpec
abbrev sessionMemcpyBytesAtSpecWithStack := ConcatBudgetAux.sessionMemcpyBytesAtSpecWithStack
abbrev sliceConcat2Events := ConcatBudgetAux.sliceConcat2Events
abbrev SliceConcat2Env := ConcatBudgetAux.SliceConcat2Env
abbrev sliceConcat2Spec := @ConcatBudgetAux.sliceConcat2Spec
abbrev fitsEnv_sliceConcat2_iff := @ConcatBudgetAux.fitsEnv_sliceConcat2_iff
abbrev sliceConcat2SpecWithStack := ConcatBudgetAux.sliceConcat2SpecWithStack
abbrev sliceConcat2SpecXA := ConcatBudgetAux.sliceConcat2SpecXA
abbrev slice_concat_2_withStack_placed_ok_of_hooks :=
  @ConcatBudgetAux.slice_concat_2_withStack_placed_ok_of_hooks
abbrev slice_concat_2_withStack_placed_ok := @ConcatBudgetAux.slice_concat_2_withStack_placed_ok
abbrev slice_concat_2_placed_ok := @ConcatBudgetAux.slice_concat_2_placed_ok
abbrev slice_concat_2_placed_ok_xa := @ConcatBudgetAux.slice_concat_2_placed_ok_xa

/-! ## 3-Slice Concatenation (Block 386) -/

abbrev sliceConcat3Events := LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget.sliceConcat2Events

def SliceConcat3Env (x : SliceConcat3Ghost) (evs : List AllocEvent) : Prop :=
  evs = sliceConcat3Events (x.bs0.length + x.bs1.length + x.bs2.length)

theorem fitsEnv_sliceConcat3_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {x : SliceConcat3Ghost} :
    FitsEnv M lim st (SliceConcat3Env x) ↔
      FitsEvents M lim st (sliceConcat3Events (x.bs0.length + x.bs1.length + x.bs2.length)) :=
  FitsEnv.eq_iff

/-- Budget-threaded 3-slice concatenation specification parameterized by callee `hookStack`. -/
def sliceConcat3SpecWithStack (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (hookStack : Nat) : Spec (SliceConcat3Ghost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.outVec ∧ s.readReg64 .x1 = x.slicesA ∧ s.readReg64 .x2 = 3#64 ∧
      x.bs0.length + x.bs1.length + x.bs2.length < 2 ^ 63 ∧ FitsEnv M lim st (SliceConcat3Env x)⌝ ∗
      memRegion x.outVec 24 ∗
      (x.slicesA ↦₆₄ x.p0) ∗ ((x.slicesA + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs0.length) ∗
      ((x.slicesA + 16#64) ↦₆₄ x.p1) ∗ ((x.slicesA + 24#64) ↦₆₄ BitVec.ofNat 64 x.bs1.length) ∗
      ((x.slicesA + 32#64) ↦₆₄ x.p2) ∗ ((x.slicesA + 40#64) ↦₆₄ BitVec.ofNat 64 x.bs2.length) ∗
      bytesAt x.ro0 x.p0 x.bs0 ∗ bytesAt x.ro1 x.p1 x.bs1 ∗ bytesAt x.ro2 x.p2 x.bs2 ∗
      A.pool lim st s ∗ stackAt s.sp (hookStack + 96)
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ SliceConcat3Env x evs⌝ ∗
      (∃∗ ptr : BitVec 64, vecU8At A.repAlloc x.outVec
        (BitVec.ofNat 64 (x.bs0.length + x.bs1.length + x.bs2.length))
        ptr (x.bs0 ++ x.bs1 ++ x.bs2)) ∗
      (x.slicesA ↦₆₄ x.p0) ∗ ((x.slicesA + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs0.length) ∗
      ((x.slicesA + 16#64) ↦₆₄ x.p1) ∗ ((x.slicesA + 24#64) ↦₆₄ BitVec.ofNat 64 x.bs1.length) ∗
      ((x.slicesA + 32#64) ↦₆₄ x.p2) ∗ ((x.slicesA + 40#64) ↦₆₄ BitVec.ofNat 64 x.bs2.length) ∗
      bytesAt x.ro0 x.p0 x.bs0 ∗ bytesAt x.ro1 x.p1 x.bs1 ∗ bytesAt x.ro2 x.p2 x.bs2 ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp (hookStack + 96)

/-- Budget-threaded 3-slice concatenation specification at `extHookStack`. -/
def sliceConcat3Spec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (SliceConcat3Ghost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.outVec ∧ s.readReg64 .x1 = x.slicesA ∧ s.readReg64 .x2 = 3#64 ∧
      x.bs0.length + x.bs1.length + x.bs2.length < 2 ^ 63 ∧ FitsEnv M lim st (SliceConcat3Env x)⌝ ∗
      memRegion x.outVec 24 ∗
      (x.slicesA ↦₆₄ x.p0) ∗ ((x.slicesA + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs0.length) ∗
      ((x.slicesA + 16#64) ↦₆₄ x.p1) ∗ ((x.slicesA + 24#64) ↦₆₄ BitVec.ofNat 64 x.bs1.length) ∗
      ((x.slicesA + 32#64) ↦₆₄ x.p2) ∗ ((x.slicesA + 40#64) ↦₆₄ BitVec.ofNat 64 x.bs2.length) ∗
      bytesAt x.ro0 x.p0 x.bs0 ∗ bytesAt x.ro1 x.p1 x.bs1 ∗ bytesAt x.ro2 x.p2 x.bs2 ∗
      A.pool lim st s ∗ stackAt s.sp extHookStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ SliceConcat3Env x evs⌝ ∗
      (∃∗ ptr : BitVec 64, vecU8At A.repAlloc x.outVec
        (BitVec.ofNat 64 (x.bs0.length + x.bs1.length + x.bs2.length))
        ptr (x.bs0 ++ x.bs1 ++ x.bs2)) ∗
      (x.slicesA ↦₆₄ x.p0) ∗ ((x.slicesA + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs0.length) ∗
      ((x.slicesA + 16#64) ↦₆₄ x.p1) ∗ ((x.slicesA + 24#64) ↦₆₄ BitVec.ofNat 64 x.bs1.length) ∗
      ((x.slicesA + 32#64) ↦₆₄ x.p2) ∗ ((x.slicesA + 40#64) ↦₆₄ BitVec.ofNat 64 x.bs2.length) ∗
      bytesAt x.ro0 x.p0 x.bs0 ∗ bytesAt x.ro1 x.p1 x.bs1 ∗ bytesAt x.ro2 x.p2 x.bs2 ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp extHookStack

abbrev sliceConcat3SpecXA (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (SliceConcat3Ghost × M.σ) :=
  sliceConcat3SpecWithStack M A lim extHookStack

private theorem sliceConcat3Spec_of_withStack {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {addr : BitVec 64}
    (h : subroutine_ok P addr (sliceConcat3SpecWithStack M A lim allocHookStack)) :
    subroutine_ok P addr (sliceConcat3Spec M A lim) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  let btm := memRegion (s0.sp - 16384#64) 12192
  have hpre' : s0.mem ⊨
      (sliceConcat3SpecWithStack M A lim allocHookStack).pre (x, st) s0 ∗ (btm ∗ R) := by
    simpa only [sliceConcat3Spec, sliceConcat3SpecWithStack,
      stackAt_extHookStack_eq_concatStack, btm, sepConj_assoc] using hpre
  refine h.mono_outcome (x, st) (btm ∗ R) s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hmem⟩ | ⟨code, _, hmem⟩ | ⟨_, hmem⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simpa only [sliceConcat3SpecWithStack, sliceConcat3Spec,
      stackAt_extHookStack_eq_concatStack, btm, sepExists_sepConj_left, sepConj_assoc] using hq
  · rw [show (sliceConcat3SpecWithStack M A lim allocHookStack).onPanic (x, st) s0 sf = ⌜False⌝ from rfl,
      satisfies_pure_sepConj] at hmem; exact False.elim hmem.1
  · rw [show (sliceConcat3SpecWithStack M A lim allocHookStack).onExit (x, st) code s0 sf = ⌜False⌝ from rfl,
      satisfies_pure_sepConj] at hmem; exact False.elim hmem.1
  · rw [show (sliceConcat3SpecWithStack M A lim allocHookStack).onOom (x, st) s0 sf = ⌜False⌝ from rfl,
      satisfies_pure_sepConj] at hmem; exact False.elim hmem.1

set_option maxHeartbeats 3200000 in
/-- Block 386 meets `sliceConcat3SpecWithStack M A lim hookStack` given callee hook contracts. -/
theorem slice_concat_3_withStack_placed_ok_of_hooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : hookStack + 12 * 8 ≤ 2 ^ 64)
    (hshim : subroutine_ok ((blkPC_386).rebase (blkPl_386).base H)
      (lsρ spqrRustNoAllocShimSym) (session2ShimAcpSpecWithStack hookStack))
    (halloc : subroutine_ok ((blkPC_386).rebase (blkPl_386).base H)
      (lsρ spqrRustAllocSym) (rustCliAllocNoOomSpecWithStack M A lim false hookStack))
    (hmc_any : ∀ ro, subroutine_ok ((blkPC_386).rebase (blkPl_386).base H)
      (lsρ spqrMemcpySym) (sessionMemcpyBytesAtSpecWithStack hookStack ro)) :
    subroutine_ok ((blkPC_386).rebase (blkPl_386).base H)
      (blkPl_386).base (sliceConcat3SpecWithStack M A lim hookStack) := by
  unfold sliceConcat3SpecWithStack
  simp only [memRegion_24, stackAt_concat_gen _ hhook,
    sepExists_sepConj_left, sepExists_sepConj_right]
  wp_init x s0
  rcases x with ⟨⟨outVec, slicesA, ro0, p0, bs0, ro1, p1, bs1, ro2, p2, bs2⟩, st⟩
  dsimp only at *
  have hmax : bs0.length + bs1.length + bs2.length < 2 ^ 63 := ‹_›
  have hfits_env : FitsEnv M lim st
      (SliceConcat3Env ⟨outVec, slicesA, ro0, p0, bs0, ro1, p1, bs1, ro2, p2, bs2⟩) := ‹_›
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have h0_lt64 : bs0.length < 2 ^ 64 := by omega
  have h1_lt64 : bs1.length < 2 ^ 64 := by omega
  have h2_lt64 : bs2.length < 2 ^ 64 := by omega
  have h0_le64 : bs0.length ≤ 2 ^ 64 := by omega
  have h1_le64 : bs1.length ≤ 2 ^ 64 := by omega
  have h2_le64 : bs2.length ≤ 2 ^ 64 := by omega
  have hadd10_bv : BitVec.ofNat 64 bs1.length + BitVec.ofNat 64 bs0.length =
      BitVec.ofNat 64 (bs0.length + bs1.length) := by rw [← BitVec.ofNat_add, Nat.add_comm]
  have hadd201_bv : BitVec.ofNat 64 bs2.length + BitVec.ofNat 64 (bs0.length + bs1.length) =
      BitVec.ofNat 64 (bs0.length + bs1.length + bs2.length) := by rw [← BitVec.ofNat_add, Nat.add_comm]
  have hadd20_bv : BitVec.ofNat 64 bs2.length + BitVec.ofNat 64 bs0.length =
      BitVec.ofNat 64 (bs0.length + bs2.length) := by rw [← BitVec.ofNat_add, Nat.add_comm]
  have hadd21_bv : BitVec.ofNat 64 bs2.length + BitVec.ofNat 64 bs1.length =
      BitVec.ofNat 64 (bs1.length + bs2.length) := by rw [← BitVec.ofNat_add, Nat.add_comm]
  have hadd01_bv : BitVec.ofNat 64 bs0.length + BitVec.ofNat 64 bs1.length =
      BitVec.ofNat 64 (bs0.length + bs1.length) := by rw [← BitVec.ofNat_add]
  have hadd02_bv : BitVec.ofNat 64 bs0.length + BitVec.ofNat 64 bs2.length =
      BitVec.ofNat 64 (bs0.length + bs2.length) := by rw [← BitVec.ofNat_add]
  have hadd12_bv : BitVec.ofNat 64 bs1.length + BitVec.ofNat 64 bs2.length =
      BitVec.ofNat 64 (bs1.length + bs2.length) := by rw [← BitVec.ofNat_add]
  have hadd012_bv : BitVec.ofNat 64 (bs0.length + bs1.length) + BitVec.ofNat 64 bs2.length =
      BitVec.ofNat 64 (bs0.length + bs1.length + bs2.length) := by rw [← BitVec.ofNat_add]
  have hsub0_bv : BitVec.ofNat 64 (bs0.length + bs1.length + bs2.length) - BitVec.ofNat 64 bs0.length =
      BitVec.ofNat 64 (bs1.length + bs2.length) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub_of_le]
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt h0_lt64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
    · simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega
  have hsub01_bv : BitVec.ofNat 64 (bs0.length + bs1.length + bs2.length) -
      BitVec.ofNat 64 (bs0.length + bs1.length) = BitVec.ofNat 64 bs2.length := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub_of_le]
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2_lt64]; omega
    · simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega
  have hsub0_01_bv : BitVec.ofNat 64 (bs0.length + bs1.length) - BitVec.ofNat 64 bs0.length =
      BitVec.ofNat 64 bs1.length := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub_of_le]
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt h0_lt64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1_lt64]; omega
    · simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega
  have hsub0_02_bv : BitVec.ofNat 64 (bs0.length + bs2.length) - BitVec.ofNat 64 bs0.length =
      BitVec.ofNat 64 bs2.length := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub_of_le]
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt h0_lt64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2_lt64]; omega
    · simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega
  have hsub1_bv : BitVec.ofNat 64 (bs1.length + bs2.length) - BitVec.ofNat 64 bs1.length =
      BitVec.ofNat 64 bs2.length := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub_of_le]
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt h1_lt64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2_lt64]; omega
    · simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega
  have hcs1 : (BitVec.ofNat 64 (bs0.length + bs1.length)).ult (BitVec.ofNat 64 bs1.length) = false :=
    ofNat_ult_of_le (by omega) (by omega)
  have hcs2 : (BitVec.ofNat 64 (bs0.length + bs1.length + bs2.length)).ult (BitVec.ofNat 64 bs2.length) = false :=
    ofNat_ult_of_le (by omega) (by omega)
  have hcs02 : (BitVec.ofNat 64 (bs0.length + bs2.length)).ult (BitVec.ofNat 64 bs2.length) = false :=
    ofNat_ult_of_le (by omega) (by omega)
  have hcs12 : (BitVec.ofNat 64 (bs1.length + bs2.length)).ult (BitVec.ofNat 64 bs2.length) = false :=
    ofNat_ult_of_le (by omega) (by omega)
  have hbit63 : (BitVec.ofNat 64 (bs0.length + bs1.length + bs2.length)).getLsbD 63 = false :=
    ofNat_getLsbD_63_false (by omega)
  have helem63 : (BitVec.ofNat 64 (bs0.length + bs1.length + bs2.length))[63] = false :=
    ofNat_getElem_63_false (by omega)
  have htot_toNat : (BitVec.ofNat 64 (bs0.length + bs1.length + bs2.length)).toNat =
      bs0.length + bs1.length + bs2.length := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h01_toNat : (BitVec.ofNat 64 (bs0.length + bs1.length)).toNat = bs0.length + bs1.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h02_toNat : (BitVec.ofNat 64 (bs0.length + bs2.length)).toNat = bs0.length + bs2.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h12_toNat : (BitVec.ofNat 64 (bs1.length + bs2.length)).toNat = bs1.length + bs2.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h0_toNat : (BitVec.ofNat 64 bs0.length).toNat = bs0.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h0_lt64]
  have h1_toNat : (BitVec.ofNat 64 bs1.length).toNat = bs1.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1_lt64]
  have h2_toNat : (BitVec.ofNat 64 bs2.length).toNat = bs2.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2_lt64]
  have hhi0 : (BitVec.ofNat 64 (bs0.length + bs1.length + bs2.length)).ult (BitVec.ofNat 64 bs0.length) = false :=
    ofNat_ult_of_le (by omega) (by omega)
  have hhi0_01 : (BitVec.ofNat 64 (bs0.length + bs1.length)).ult (BitVec.ofNat 64 bs0.length) = false :=
    ofNat_ult_of_le (by omega) (by omega)
  have hhi0_02 : (BitVec.ofNat 64 (bs0.length + bs2.length)).ult (BitVec.ofNat 64 bs0.length) = false :=
    ofNat_ult_of_le (by omega) (by omega)
  have hhi0_self : (BitVec.ofNat 64 bs0.length).ult (BitVec.ofNat 64 bs0.length) = false :=
    ProofLib.bitvec_ult_self _
  have hhi1 : (BitVec.ofNat 64 (bs1.length + bs2.length)).ult (BitVec.ofNat 64 bs1.length) = false :=
    ofNat_ult_of_le (by omega) (by omega)
  have hhi1_self : (BitVec.ofNat 64 bs1.length).ult (BitVec.ofNat 64 bs1.length) = false :=
    ProofLib.bitvec_ult_self _
  have hhi2 : (BitVec.ofNat 64 bs2.length).ult (BitVec.ofNat 64 bs2.length) = false :=
    ProofLib.bitvec_ult_self _
  simp only [Bool.false_eq_true, ↓reduceIte] at halloc
  have h0_eq : bs0 = [] ∨ 0 < bs0.length := by cases bs0 <;> simp
  have h1_eq : bs1 = [] ∨ 0 < bs1.length := by cases bs1 <;> simp
  have h2_eq : bs2 = [] ∨ 0 < bs2.length := by cases bs2 <;> simp
  rcases h0_eq with rfl | hpos0 <;> rcases h1_eq with rfl | hpos1 <;> rcases h2_eq with rfl | hpos2
  ·
    simp only [List.length_nil, Nat.add_zero, List.append_nil] at *
    have henv : SliceConcat3Env ⟨outVec, slicesA, ro0, p0, [], ro1, p1, [], ro2, p2, []⟩ [] := rfl
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists ([] : List AllocEvent)
    simp only [M.stepEvents_nil]
    apply SepWP.fold (vecU8At_of_zero A.repAlloc outVec) (by sep_focus)
    wp_done
  ·
    simp only [List.length_nil, Nat.add_zero, Nat.zero_add, List.nil_append, List.append_nil] at *
    have h2_ne0 : (BitVec.ofNat 64 bs2.length == 0#64) = false := ofNat_beq_zero_false hpos2 h2_lt64
    have h2_len_ne : bs2.length ≠ 0 := Nat.ne_of_gt hpos2
    have henv : SliceConcat3Env ⟨outVec, slicesA, ro0, p0, [], ro1, p1, [], ro2, p2, bs2⟩
        (rustAllocEvents bs2.length 1) := by
      simp only [SliceConcat3Env, sliceConcat3Events,
        LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget.sliceConcat2Events,
        List.length_nil, Nat.add_zero, Nat.zero_add, h2_len_ne, ↓reduceIte]
    have hfits : FitsEvents M lim st (rustAllocEvents bs2.length 1) := hfits_env _ henv
    have hlay : RustLayoutOk bs2.length 1 := ⟨⟨hpos2, hpow1, by omega⟩, by decide⟩
    wp_steps_sync_pool (lsρ spqrRustNoAllocShimSym)
    simp only [State.setMem_setMem]
    wp_call hshim ()
    have hacp0 : AllocCallPreserved s0 sf :=
      acp_chain_acp ‹_› (by simp only [wp_norm, arm64_norm])
    rw [← A.pool_of_vmPreserved ‹_›]
    wp_steps_sync_pool (lsρ spqrRustAllocSym)
    simp only [State.setMem_setMem]
    wp_call halloc (bs2.length, 1, st)
    have hacp1 : AllocCallPreserved s0 sf_1 :=
      acp_chain_acp ‹_› (by simp only [wp_norm, arm64_norm, hacp0])
    have htr_sf1 : sf_1.trace = s0.trace := hacp1.2.1
    have hptr_ne : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := ‹_›
    have hoom_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_false_of_ne hptr_ne
    wp_steps_sync_pool (lsρ spqrMemcpySym)
    simp only [State.setMem_setMem]
    wp_call (hmc_any ro2) (sf_1.readReg64 (Reg.gpr 0#5), p2, bs2)
    have hacp2 : AllocCallPreserved s0 sf_2 :=
      acp_chain_acp ‹_› (by simp only [wp_norm, arm64_norm, hacp1])
    rcases hacp2 with ⟨_, _, _, _, _, _, _⟩
    rw [← A.pool_of_vmPreserved ‹_›]
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists
      (rustAllocEvents bs2.length 1)
    apply SepWP.fold (vecU8At_of_pos A outVec (sf_1.readReg64 (Reg.gpr 0#5)) bs2
      hpos2 hmax hptr_ne) (by sep_focus)
    wp_done
  ·
    simp only [List.length_nil, Nat.add_zero, Nat.zero_add, List.nil_append, List.append_nil] at *
    have h1_ne0 : (BitVec.ofNat 64 bs1.length == 0#64) = false := ofNat_beq_zero_false hpos1 h1_lt64
    have h1_len_ne : bs1.length ≠ 0 := Nat.ne_of_gt hpos1
    have henv : SliceConcat3Env ⟨outVec, slicesA, ro0, p0, [], ro1, p1, bs1, ro2, p2, []⟩
        (rustAllocEvents bs1.length 1) := by
      simp only [SliceConcat3Env, sliceConcat3Events,
        LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget.sliceConcat2Events,
        List.length_nil, Nat.add_zero, Nat.zero_add, h1_len_ne, ↓reduceIte]
    have hfits : FitsEvents M lim st (rustAllocEvents bs1.length 1) := hfits_env _ henv
    have hlay : RustLayoutOk bs1.length 1 := ⟨⟨hpos1, hpow1, by omega⟩, by decide⟩
    wp_steps_sync_pool (lsρ spqrRustNoAllocShimSym)
    simp only [State.setMem_setMem]
    wp_call hshim ()
    have hacp0 : AllocCallPreserved s0 sf :=
      acp_chain_acp ‹_› (by simp only [wp_norm, arm64_norm])
    rw [← A.pool_of_vmPreserved ‹_›]
    wp_steps_sync_pool (lsρ spqrRustAllocSym)
    simp only [State.setMem_setMem]
    wp_call halloc (bs1.length, 1, st)
    have hacp1 : AllocCallPreserved s0 sf_1 :=
      acp_chain_acp ‹_› (by simp only [wp_norm, arm64_norm, hacp0])
    have htr_sf1 : sf_1.trace = s0.trace := hacp1.2.1
    have hptr_ne : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := ‹_›
    have hoom_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_false_of_ne hptr_ne
    wp_steps_sync_pool (lsρ spqrMemcpySym)
    simp only [State.setMem_setMem]
    wp_call (hmc_any ro1) (sf_1.readReg64 (Reg.gpr 0#5), p1, bs1)
    have hacp2 : AllocCallPreserved s0 sf_2 :=
      acp_chain_acp ‹_› (by simp only [wp_norm, arm64_norm, hacp1])
    rcases hacp2 with ⟨_, _, _, _, _, _, _⟩
    rw [← A.pool_of_vmPreserved ‹_›]
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists
      (rustAllocEvents bs1.length 1)
    apply SepWP.fold (vecU8At_of_pos A outVec (sf_1.readReg64 (Reg.gpr 0#5)) bs1
      hpos1 hmax hptr_ne) (by sep_focus)
    wp_done
  ·
    simp only [List.length_nil, Nat.zero_add, List.nil_append] at *
    have htot_ne0 : (BitVec.ofNat 64 (bs1.length + bs2.length) == 0#64) = false :=
      ofNat_beq_zero_false (by omega) (by omega)
    have h1_ne0 : (BitVec.ofNat 64 bs1.length == 0#64) = false := ofNat_beq_zero_false hpos1 h1_lt64
    have h2_ne0 : (BitVec.ofNat 64 bs2.length == 0#64) = false := ofNat_beq_zero_false hpos2 h2_lt64
    have htot_pos : 0 < bs1.length + bs2.length := by omega
    have htot_len_ne : bs1.length + bs2.length ≠ 0 := Nat.ne_of_gt htot_pos
    have henv : SliceConcat3Env ⟨outVec, slicesA, ro0, p0, [], ro1, p1, bs1, ro2, p2, bs2⟩
        (rustAllocEvents (bs1.length + bs2.length) 1) := by
      simp only [SliceConcat3Env, sliceConcat3Events,
        LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget.sliceConcat2Events,
        List.length_nil, Nat.zero_add, htot_len_ne, ↓reduceIte]
    have hfits : FitsEvents M lim st (rustAllocEvents (bs1.length + bs2.length) 1) :=
      hfits_env _ henv
    have hlay : RustLayoutOk (bs1.length + bs2.length) 1 := ⟨⟨htot_pos, hpow1, by omega⟩, by decide⟩
    wp_steps_sync_pool (lsρ spqrRustNoAllocShimSym)
    simp only [State.setMem_setMem]
    wp_call hshim ()
    have hacp0 : AllocCallPreserved s0 sf :=
      acp_chain_acp ‹_› (by simp only [wp_norm, arm64_norm])
    rw [← A.pool_of_vmPreserved ‹_›]
    wp_steps_sync_pool (lsρ spqrRustAllocSym)
    simp only [State.setMem_setMem]
    wp_call halloc (bs1.length + bs2.length, 1, st)
    have hacp1 : AllocCallPreserved s0 sf_1 :=
      acp_chain_acp ‹_› (by simp only [wp_norm, arm64_norm, hacp0])
    have htr_sf1 : sf_1.trace = s0.trace := hacp1.2.1
    have hptr_ne : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := ‹_›
    have hoom_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_false_of_ne hptr_ne
    rw [ProofLib.memRegion_split (sf_1.readReg64 (Reg.gpr 0#5)) bs1.length bs2.length (by omega)]
    wp_steps_sync_pool (lsρ spqrMemcpySym)
    simp only [State.setMem_setMem]
    wp_call (hmc_any ro1) (sf_1.readReg64 (Reg.gpr 0#5), p1, bs1)
    have hacp2 : AllocCallPreserved s0 sf_2 :=
      acp_chain_acp ‹_› (by simp only [wp_norm, arm64_norm, hacp1])
    rw [← A.pool_of_vmPreserved ‹_›]
    wp_steps_sync_pool (lsρ spqrMemcpySym)
    simp only [State.setMem_setMem]
    wp_call (hmc_any ro2) (sf_1.readReg64 (Reg.gpr 0#5) + BitVec.ofNat 64 bs1.length, p2, bs2)
    have hacp3 : AllocCallPreserved s0 sf_3 :=
      acp_chain_acp ‹_› (by simp only [wp_norm, arm64_norm, hacp2])
    rcases hacp3 with ⟨_, _, _, _, _, _, _⟩
    rw [← A.pool_of_vmPreserved ‹_›]
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists
      (rustAllocEvents (bs1.length + bs2.length) 1)
    apply SepWP.fold (Entails.of_eq (pointsToBytes_append (sf_1.readReg64 (Reg.gpr 0#5)) bs1 bs2).symm)
      (by sep_focus)
    apply SepWP.fold (vecU8At_of_append_pos A outVec (sf_1.readReg64 (Reg.gpr 0#5)) bs1 bs2
      htot_pos hmax hptr_ne) (by sep_focus)
    wp_done
  ·
    simp only [List.length_nil, Nat.add_zero, List.append_nil] at *
    have h0_ne0 : (BitVec.ofNat 64 bs0.length == 0#64) = false := ofNat_beq_zero_false hpos0 h0_lt64
    have h0_len_ne : bs0.length ≠ 0 := Nat.ne_of_gt hpos0
    have henv : SliceConcat3Env ⟨outVec, slicesA, ro0, p0, bs0, ro1, p1, [], ro2, p2, []⟩
        (rustAllocEvents bs0.length 1) := by
      simp only [SliceConcat3Env, sliceConcat3Events,
        LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget.sliceConcat2Events,
        List.length_nil, Nat.add_zero, h0_len_ne, ↓reduceIte]
    have hfits : FitsEvents M lim st (rustAllocEvents bs0.length 1) := hfits_env _ henv
    have hlay : RustLayoutOk bs0.length 1 := ⟨⟨hpos0, hpow1, by omega⟩, by decide⟩
    wp_steps_sync_pool (lsρ spqrRustNoAllocShimSym)
    simp only [State.setMem_setMem]
    wp_call hshim ()
    have hacp0 : AllocCallPreserved s0 sf :=
      acp_chain_acp ‹_› (by simp only [wp_norm, arm64_norm])
    rw [← A.pool_of_vmPreserved ‹_›]
    wp_steps_sync_pool (lsρ spqrRustAllocSym)
    simp only [State.setMem_setMem]
    wp_call halloc (bs0.length, 1, st)
    have hacp1 : AllocCallPreserved s0 sf_1 :=
      acp_chain_acp ‹_› (by simp only [wp_norm, arm64_norm, hacp0])
    have htr_sf1 : sf_1.trace = s0.trace := hacp1.2.1
    have hptr_ne : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := ‹_›
    have hoom_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_false_of_ne hptr_ne
    wp_steps_sync_pool (lsρ spqrMemcpySym)
    simp only [State.setMem_setMem]
    wp_call (hmc_any ro0) (sf_1.readReg64 (Reg.gpr 0#5), p0, bs0)
    have hacp2 : AllocCallPreserved s0 sf_2 :=
      acp_chain_acp ‹_› (by simp only [wp_norm, arm64_norm, hacp1])
    rcases hacp2 with ⟨_, _, _, _, _, _, _⟩
    rw [← A.pool_of_vmPreserved ‹_›]
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists
      (rustAllocEvents bs0.length 1)
    apply SepWP.fold (vecU8At_of_pos A outVec (sf_1.readReg64 (Reg.gpr 0#5)) bs0
      hpos0 hmax hptr_ne) (by sep_focus)
    wp_done
  ·
    simp only [List.length_nil, Nat.add_zero, Nat.zero_add, List.append_nil] at *
    have htot_ne0 : (BitVec.ofNat 64 (bs0.length + bs2.length) == 0#64) = false :=
      ofNat_beq_zero_false (by omega) (by omega)
    have h0_ne0 : (BitVec.ofNat 64 bs0.length == 0#64) = false := ofNat_beq_zero_false hpos0 h0_lt64
    have h2_ne0 : (BitVec.ofNat 64 bs2.length == 0#64) = false := ofNat_beq_zero_false hpos2 h2_lt64
    have htot_pos : 0 < bs0.length + bs2.length := by omega
    have htot_len_ne : bs0.length + bs2.length ≠ 0 := Nat.ne_of_gt htot_pos
    have henv : SliceConcat3Env ⟨outVec, slicesA, ro0, p0, bs0, ro1, p1, [], ro2, p2, bs2⟩
        (rustAllocEvents (bs0.length + bs2.length) 1) := by
      simp only [SliceConcat3Env, sliceConcat3Events,
        LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget.sliceConcat2Events,
        List.length_nil, Nat.add_zero, htot_len_ne, ↓reduceIte]
    have hfits : FitsEvents M lim st (rustAllocEvents (bs0.length + bs2.length) 1) :=
      hfits_env _ henv
    have hlay : RustLayoutOk (bs0.length + bs2.length) 1 := ⟨⟨htot_pos, hpow1, by omega⟩, by decide⟩
    wp_steps_sync_pool (lsρ spqrRustNoAllocShimSym)
    simp only [State.setMem_setMem]
    wp_call hshim ()
    have hacp0 : AllocCallPreserved s0 sf :=
      acp_chain_acp ‹_› (by simp only [wp_norm, arm64_norm])
    rw [← A.pool_of_vmPreserved ‹_›]
    wp_steps_sync_pool (lsρ spqrRustAllocSym)
    simp only [State.setMem_setMem]
    wp_call halloc (bs0.length + bs2.length, 1, st)
    have hacp1 : AllocCallPreserved s0 sf_1 :=
      acp_chain_acp ‹_› (by simp only [wp_norm, arm64_norm, hacp0])
    have htr_sf1 : sf_1.trace = s0.trace := hacp1.2.1
    have hptr_ne : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := ‹_›
    have hoom_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_false_of_ne hptr_ne
    rw [ProofLib.memRegion_split (sf_1.readReg64 (Reg.gpr 0#5)) bs0.length bs2.length (by omega)]
    wp_steps_sync_pool (lsρ spqrMemcpySym)
    simp only [State.setMem_setMem]
    wp_call (hmc_any ro0) (sf_1.readReg64 (Reg.gpr 0#5), p0, bs0)
    have hacp2 : AllocCallPreserved s0 sf_2 :=
      acp_chain_acp ‹_› (by simp only [wp_norm, arm64_norm, hacp1])
    rw [← A.pool_of_vmPreserved ‹_›]
    wp_steps_sync_pool (lsρ spqrMemcpySym)
    simp only [State.setMem_setMem]
    wp_call (hmc_any ro2) (sf_1.readReg64 (Reg.gpr 0#5) + BitVec.ofNat 64 bs0.length, p2, bs2)
    have hacp3 : AllocCallPreserved s0 sf_3 :=
      acp_chain_acp ‹_› (by simp only [wp_norm, arm64_norm, hacp2])
    rcases hacp3 with ⟨_, _, _, _, _, _, _⟩
    rw [← A.pool_of_vmPreserved ‹_›]
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists
      (rustAllocEvents (bs0.length + bs2.length) 1)
    apply SepWP.fold (Entails.of_eq (pointsToBytes_append (sf_1.readReg64 (Reg.gpr 0#5)) bs0 bs2).symm)
      (by sep_focus)
    apply SepWP.fold (vecU8At_of_append_pos A outVec (sf_1.readReg64 (Reg.gpr 0#5)) bs0 bs2
      htot_pos hmax hptr_ne) (by sep_focus)
    wp_done
  ·
    simp only [List.length_nil, Nat.add_zero, List.append_nil] at *
    have htot_ne0 : (BitVec.ofNat 64 (bs0.length + bs1.length) == 0#64) = false :=
      ofNat_beq_zero_false (by omega) (by omega)
    have h0_ne0 : (BitVec.ofNat 64 bs0.length == 0#64) = false := ofNat_beq_zero_false hpos0 h0_lt64
    have h1_ne0 : (BitVec.ofNat 64 bs1.length == 0#64) = false := ofNat_beq_zero_false hpos1 h1_lt64
    have htot_pos : 0 < bs0.length + bs1.length := by omega
    have htot_len_ne : bs0.length + bs1.length ≠ 0 := Nat.ne_of_gt htot_pos
    have henv : SliceConcat3Env ⟨outVec, slicesA, ro0, p0, bs0, ro1, p1, bs1, ro2, p2, []⟩
        (rustAllocEvents (bs0.length + bs1.length) 1) := by
      simp only [SliceConcat3Env, sliceConcat3Events,
        LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget.sliceConcat2Events,
        List.length_nil, Nat.add_zero, htot_len_ne, ↓reduceIte]
    have hfits : FitsEvents M lim st (rustAllocEvents (bs0.length + bs1.length) 1) :=
      hfits_env _ henv
    have hlay : RustLayoutOk (bs0.length + bs1.length) 1 := ⟨⟨htot_pos, hpow1, by omega⟩, by decide⟩
    wp_steps_sync_pool (lsρ spqrRustNoAllocShimSym)
    simp only [State.setMem_setMem]
    wp_call hshim ()
    have hacp0 : AllocCallPreserved s0 sf :=
      acp_chain_acp ‹_› (by simp only [wp_norm, arm64_norm])
    rw [← A.pool_of_vmPreserved ‹_›]
    wp_steps_sync_pool (lsρ spqrRustAllocSym)
    simp only [State.setMem_setMem]
    wp_call halloc (bs0.length + bs1.length, 1, st)
    have hacp1 : AllocCallPreserved s0 sf_1 :=
      acp_chain_acp ‹_› (by simp only [wp_norm, arm64_norm, hacp0])
    have htr_sf1 : sf_1.trace = s0.trace := hacp1.2.1
    have hptr_ne : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := ‹_›
    have hoom_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_false_of_ne hptr_ne
    rw [ProofLib.memRegion_split (sf_1.readReg64 (Reg.gpr 0#5)) bs0.length bs1.length (by omega)]
    wp_steps_sync_pool (lsρ spqrMemcpySym)
    simp only [State.setMem_setMem]
    wp_call (hmc_any ro0) (sf_1.readReg64 (Reg.gpr 0#5), p0, bs0)
    have hacp2 : AllocCallPreserved s0 sf_2 :=
      acp_chain_acp ‹_› (by simp only [wp_norm, arm64_norm, hacp1])
    rw [← A.pool_of_vmPreserved ‹_›]
    wp_steps_sync_pool (lsρ spqrMemcpySym)
    simp only [State.setMem_setMem]
    wp_call (hmc_any ro1) (sf_1.readReg64 (Reg.gpr 0#5) + BitVec.ofNat 64 bs0.length, p1, bs1)
    have hacp3 : AllocCallPreserved s0 sf_3 :=
      acp_chain_acp ‹_› (by simp only [wp_norm, arm64_norm, hacp2])
    rcases hacp3 with ⟨_, _, _, _, _, _, _⟩
    rw [← A.pool_of_vmPreserved ‹_›]
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists
      (rustAllocEvents (bs0.length + bs1.length) 1)
    apply SepWP.fold (Entails.of_eq (pointsToBytes_append (sf_1.readReg64 (Reg.gpr 0#5)) bs0 bs1).symm)
      (by sep_focus)
    apply SepWP.fold (vecU8At_of_append_pos A outVec (sf_1.readReg64 (Reg.gpr 0#5)) bs0 bs1
      htot_pos hmax hptr_ne) (by sep_focus)
    wp_done
  ·
    have htot_ne0 : (BitVec.ofNat 64 (bs0.length + bs1.length + bs2.length) == 0#64) = false :=
      ofNat_beq_zero_false (by omega) (by omega)
    have h0_ne0 : (BitVec.ofNat 64 bs0.length == 0#64) = false := ofNat_beq_zero_false hpos0 h0_lt64
    have h1_ne0 : (BitVec.ofNat 64 bs1.length == 0#64) = false := ofNat_beq_zero_false hpos1 h1_lt64
    have h2_ne0 : (BitVec.ofNat 64 bs2.length == 0#64) = false := ofNat_beq_zero_false hpos2 h2_lt64
    have htot_pos : 0 < bs0.length + bs1.length + bs2.length := by omega
    have htot_len_ne : bs0.length + bs1.length + bs2.length ≠ 0 := Nat.ne_of_gt htot_pos
    have henv : SliceConcat3Env ⟨outVec, slicesA, ro0, p0, bs0, ro1, p1, bs1, ro2, p2, bs2⟩
        (rustAllocEvents (bs0.length + bs1.length + bs2.length) 1) := by
      simp only [SliceConcat3Env, sliceConcat3Events,
        LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget.sliceConcat2Events,
        htot_len_ne, ↓reduceIte]
    have hfits : FitsEvents M lim st (rustAllocEvents (bs0.length + bs1.length + bs2.length) 1) :=
      hfits_env _ henv
    have hlay : RustLayoutOk (bs0.length + bs1.length + bs2.length) 1 :=
      ⟨⟨htot_pos, hpow1, by omega⟩, by decide⟩
    wp_steps_sync_pool (lsρ spqrRustNoAllocShimSym)
    simp only [State.setMem_setMem]
    wp_call hshim ()
    have hacp0 : AllocCallPreserved s0 sf :=
      acp_chain_acp ‹_› (by simp only [wp_norm, arm64_norm])
    rw [← A.pool_of_vmPreserved ‹_›]
    wp_steps_sync_pool (lsρ spqrRustAllocSym)
    simp only [State.setMem_setMem]
    wp_call halloc (bs0.length + bs1.length + bs2.length, 1, st)
    have hacp1 : AllocCallPreserved s0 sf_1 :=
      acp_chain_acp ‹_› (by simp only [wp_norm, arm64_norm, hacp0])
    have htr_sf1 : sf_1.trace = s0.trace := hacp1.2.1
    have hptr_ne : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := ‹_›
    have hoom_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_false_of_ne hptr_ne
    rw [ProofLib.memRegion_split (sf_1.readReg64 (Reg.gpr 0#5)) (bs0.length + bs1.length) bs2.length (by omega),
      ProofLib.memRegion_split (sf_1.readReg64 (Reg.gpr 0#5)) bs0.length bs1.length (by omega)]
    wp_steps_sync_pool (lsρ spqrMemcpySym)
    simp only [State.setMem_setMem]
    wp_call (hmc_any ro0) (sf_1.readReg64 (Reg.gpr 0#5), p0, bs0)
    have hacp2 : AllocCallPreserved s0 sf_2 :=
      acp_chain_acp ‹_› (by simp only [wp_norm, arm64_norm, hacp1])
    rw [← A.pool_of_vmPreserved ‹_›]
    wp_steps_sync_pool (lsρ spqrMemcpySym)
    simp only [State.setMem_setMem]
    wp_call (hmc_any ro1) (sf_1.readReg64 (Reg.gpr 0#5) + BitVec.ofNat 64 bs0.length, p1, bs1)
    have hacp3 : AllocCallPreserved s0 sf_3 :=
      acp_chain_acp ‹_› (by simp only [wp_norm, arm64_norm, hacp2])
    rw [← A.pool_of_vmPreserved ‹_›]
    wp_steps_sync_pool (lsρ spqrMemcpySym)
    simp only [State.setMem_setMem]
    wp_call (hmc_any ro2) (sf_1.readReg64 (Reg.gpr 0#5) + BitVec.ofNat 64 (bs0.length + bs1.length), p2, bs2)
    have hacp4 : AllocCallPreserved s0 sf_4 :=
      acp_chain_acp ‹_› (by simp only [wp_norm, arm64_norm, hacp3])
    rcases hacp4 with ⟨_, _, _, _, _, _, _⟩
    rw [← A.pool_of_vmPreserved ‹_›]
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists
      (rustAllocEvents (bs0.length + bs1.length + bs2.length) 1)
    apply SepWP.fold (Entails.of_eq (pointsToBytes_append3 (sf_1.readReg64 (Reg.gpr 0#5)) bs0 bs1 bs2).symm)
      (by sep_focus)
    apply SepWP.fold (vecU8At_of_append3_pos A outVec (sf_1.readReg64 (Reg.gpr 0#5)) bs0 bs1 bs2
      htot_pos hmax hptr_ne) (by sep_focus)
    wp_done

theorem slice_concat_3_withStack_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hge : hookStack ≥ allocHookStack) (hhook : hookStack + 12 * 8 ≤ 2 ^ 64)
    (hshim : HookSat H spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : HookSat H spqrMemcpySym framelessMemcpyAcpSpec)
    (hRO : HookSat H spqrMemcpySym sessionMemcpyRegionROSpec) :
    subroutine_ok ((blkPC_386).rebase (blkPl_386).base H)
      (blkPl_386).base (sliceConcat3SpecWithStack M A lim hookStack) :=
  slice_concat_3_withStack_placed_ok_of_hooks hhook
    (session2ShimAcpWithStack_of_rustAllocShimVm hookStack (spqr_hook_ok_of_mem hshim))
    (subroutine_ok_allocNoOom_withStack_of_hookSat halloc spqr_externAt?_of_mem hge (by omega))
    (session_memcpy_bytesAt_ok_at
      (session2MemcpyAcpWithStack_of_frameless hookStack (spqr_hook_ok_of_mem hmemcpy))
      (sessionMemcpyRegionROWithStack_of_ro (spqr_hook_ok_of_mem hRO) hookStack))

/-- Block 386 meets `sliceConcat3Spec M A lim` under `HookSat`. -/
theorem slice_concat_3_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : HookSat H spqrMemcpySym framelessMemcpyAcpSpec)
    (hRO : HookSat H spqrMemcpySym sessionMemcpyRegionROSpec) :
    subroutine_ok ((blkPC_386).rebase (blkPl_386).base H)
      (blkPl_386).base (sliceConcat3Spec M A lim) :=
  sliceConcat3Spec_of_withStack (slice_concat_3_withStack_placed_ok (hookStack := allocHookStack)
    (by decide) (by decide) hshim halloc hmemcpy hRO)

/-- Block 386 meets `sliceConcat3SpecXA M A lim` under `HookSat`. -/
theorem slice_concat_3_placed_ok_xa [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : HookSat H spqrMemcpySym framelessMemcpyAcpSpec)
    (hRO : HookSat H spqrMemcpySym sessionMemcpyRegionROSpec) :
    subroutine_ok ((blkPC_386).rebase (blkPl_386).base H)
      (blkPl_386).base (sliceConcat3SpecXA M A lim) :=
  slice_concat_3_withStack_placed_ok (hookStack := extHookStack) (by decide) (by decide)
    hshim halloc hmemcpy hRO

end LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudget

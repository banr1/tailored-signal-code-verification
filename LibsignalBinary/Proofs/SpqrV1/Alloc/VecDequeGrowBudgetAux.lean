/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.VecDequeGrow
public import LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneBudget
public import LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Alloc.Fetch
import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `AllocCallPreserved` `memmove` and `RawVec<ChainEpoch>::grow_one` Helpers

Provides `AllocCallPreserved ∧ VmPreserved` `memmove` contracts and `AllocCallPreserved`
budget contracts for block 361 (`finish_grow [local#8]`) and block 356
(`RawVec<ChainEpoch>::grow_one`), used by `VecDequeGrowBudget`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Alloc.VecDequeGrowBudgetAux

open Arm64 ProofLib
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement
  blkPC_356 blkPC_361
  blkPl_356 blkPl_361
  lscall_blk lsmpl lsρ sepWP_seq_lscl withLsCodeLoaded
)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchet (sessionMemmoveSpec)
open CryptoVerification.SpqrV1.Alloc (
  GrowGhost
  spqrHandleErrorSym spqrRustAllocSym spqrRustNoAllocShimSym spqrRustReallocSym
  spqr_externAt?_of_mem spqr_hook_ok_of_mem
)
open CryptoVerification.SpqrV1.Alloc.GrowOneNorm (
  readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre
  readReg64_setPC_pre readReg_setMem_setPC_pre readReg_setPC_pre
  sp_setMem_setPC_pre sp_setPC_pre
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel BudgetLimits FitsEnv FitsEvents
  RustCliAllocBudget RustLayoutOk VmPreserved
  rustAllocEvents rustCliAllocBudgetSpec rustCliReallocBudgetSpec rustReallocEvents
)
open LibsignalBinary.Heap.IfaceSimp (
  allocCallPreserved_self
  allocCallPreserved_setMem allocCallPreserved_setMem_left
  allocCallPreserved_setPC allocCallPreserved_setPC_left
  allocCallPreserved_setPState allocCallPreserved_setPState_left
  allocCallPreserved_setStatus allocCallPreserved_setStatus_left
  allocCallPreserved_writeReg64 allocCallPreserved_writeReg64_left
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  rustCliAllocNoOomSpecWithStack rustCliReallocNoOomSpecWithStack
  subroutine_ok_allocNoOom_withStack_of_hookSat
  subroutine_ok_reallocNoOom_withStack_of_hookSat
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (sessionMemmoveBudget_hookOk)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemmoveBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneBudget (
  FG8CellsGhost GrowOneStrideEnv fitsEnv_growOneStride_iff growOneStrideEvents
)
open LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux (
  acp_chain_acp session2ShimAcpSpecWithStack session2ShimAcpWithStack_of_rustAllocShimVm
)
open LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget (
  VecDequeGrowEnv vecDequeGrowEvents
)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

private theorem pc_setMem_pre (s : State) (m : Memory) : (s.setMem m).pc = s.pc := rfl
private theorem status_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).status = s.status := rfl
private theorem pstate_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).pstate = s.pstate := rfl
private theorem trace_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).trace = s.trace := rfl
private theorem calleeSavedVRegs_setMem_pre (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := rfl

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff FitsEvents
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Envelope, Stack, and `AllocCallPreserved ∧ VmPreserved` `memmove` Helpers -/

theorem fitsEnv_vecDequeGrow_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {x : CryptoVerification.SpqrV1.ChainProofs.VecDequeGrowGhost} :
    FitsEnv M lim st (VecDequeGrowEnv x) ↔
      FitsEvents M lim st (vecDequeGrowEvents x.cap) := by
  constructor
  · intro h
    exact h _ rfl
  · rintro h evs rfl
    exact h

theorem growOneStrideEvents_112_8_eq (cap : BitVec 64) :
    growOneStrideEvents cap 112 8 = vecDequeGrowEvents cap :=
  rfl

private theorem stackAt_finishGrow_gen (sp : BitVec 64) {hookStack : Nat}
    (hhook : hookStack + 48 ≤ 2 ^ 64) :
    stackAt sp (hookStack + 48) =
      stackAt (sp - 48#64) hookStack ∗ cells (sp - 48#64) 6 :=
  ProofLib.stackAt_split_cells sp hookStack 6 hhook

private theorem stackAt_growOne_gen (sp : BitVec 64) {hookStack : Nat}
    (hhook : (hookStack + 48) + 8 * 8 ≤ 2 ^ 64) :
    stackAt sp ((hookStack + 48) + 64) =
      stackAt (sp - 64#64) (hookStack + 48) ∗ cells (sp - 64#64) 8 :=
  ProofLib.stackAt_split_cells sp (hookStack + 48) 8 hhook

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

private theorem listMove_append_to_end {bs1 bs2 : List (BitVec 8)} :
    listMove (bs1 ++ bs2) bs2.length 0 bs1.length =
      (bs1 ++ bs2).take bs2.length ++ bs1 := by
  unfold listMove
  have hdrop0 : (bs1 ++ bs2).drop 0 = bs1 ++ bs2 := rfl
  have htake1 : (bs1 ++ bs2).take bs1.length = bs1 := by
    rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length]
  have hdrop_end : (bs1 ++ bs2).drop (bs2.length + bs1.length) = [] := by
    rw [Nat.add_comm, ← List.length_append, List.drop_length]
  rw [hdrop0, htake1, hdrop_end, List.append_nil]

private theorem pointsToBytes_listMove_append_entails (base : BitVec 64)
    (bs1 bs2 : List (BitVec 8)) :
    (base ↦ₛ listMove (bs1 ++ bs2) bs2.length 0 bs1.length) ⊢
      memRegion base bs2.length ∗ ((base + BitVec.ofNat 64 bs2.length) ↦ₛ bs1) := by
  rw [listMove_append_to_end, pointsToBytes_append]
  have hlen : ((bs1 ++ bs2).take bs2.length).length = bs2.length :=
    List.length_take_of_le (by rw [List.length_append]; omega)
  rw [hlen]
  apply sepConj_mono_left
  have hreg := pointsToBytes_entails_memRegion base ((bs1 ++ bs2).take bs2.length)
  rwa [hlen] at hreg

/-- Stack-equipped `AllocCallPreserved ∧ VmPreserved` `memmove` contract. -/
def sessionMemmoveAcpSpec (hookStack : Nat := 4096) :
    Spec (BitVec 64 × List (BitVec 8) × Nat × Nat × Nat) where
  pre := (sessionMemmoveSpec hookStack).pre
  post := fun (base, buf, dst, src, len) s0 sf =>
    ⌜sf.readReg64 .x0 = base + BitVec.ofNat 64 dst ∧ AllocCallPreserved s0 sf ∧ VmPreserved s0 sf⌝ ∗
      (base ↦ₛ listMove buf dst src len) ∗ stackAt s0.sp hookStack

theorem hookMemmove_sessionMemmoveAcp_ok (hookStack : Nat := 4096) :
    HookOk hookMemmove (sessionMemmoveAcpSpec hookStack) := by
  have h := sessionMemmoveBudget_hookOk hookStack
  intro x R s0 hrun hpre hsp
  have hpre' : s0.mem ⊨ (sessionMemmoveBudgetSpec hookStack).pre x s0 ∗ R := hpre
  rcases h x R s0 hrun hpre' hsp with ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    rcases x with ⟨base, buf, dst, src, len⟩
    dsimp only [sessionMemmoveBudgetSpec, withVmPreserved, sessionMemmoveSpec,
      sessionMemmoveAcpSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, sepConj_assoc,
      satisfies_pure_sepConj] at hpost
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hpost.2.1.1, ?_, hpost.1⟩, hpost.2.2⟩
    dsimp only [hookMemmove, retHook]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact Or.inr hrest

def sessionMemmoveFrontToEndAcpSpec (hookStack : Nat) :
    Spec (BitVec 64 × List (BitVec 8) × Nat) where
  pre := fun (base, bs_front, uninitLen) s0 =>
    ⌜s0.readReg64 .x0 = base + BitVec.ofNat 64 uninitLen ∧
      s0.readReg64 .x1 = base ∧
      (s0.readReg64 .x2).toNat = bs_front.length ∧
      uninitLen ≤ 2 ^ 64⌝ ∗
      (base ↦ₛ bs_front) ∗
      memRegion (base + BitVec.ofNat 64 bs_front.length) uninitLen ∗
      stackAt s0.sp hookStack
  post := fun (base, bs_front, uninitLen) s0 sf =>
    ⌜sf.readReg64 .x0 = base + BitVec.ofNat 64 uninitLen ∧
      AllocCallPreserved s0 sf ∧ VmPreserved s0 sf⌝ ∗
      memRegion base uninitLen ∗
      ((base + BitVec.ofNat 64 uninitLen) ↦ₛ bs_front) ∗
      stackAt s0.sp hookStack

theorem session_memmove_front_to_end_acp_ok {prog : Program} {addr : BitVec 64}
    {hookStack : Nat} (hmm : subroutine_ok prog addr (sessionMemmoveAcpSpec hookStack)) :
    subroutine_ok prog addr (sessionMemmoveFrontToEndAcpSpec hookStack) := by
  refine subroutine_ok_outcome_intro fun ⟨base, bs_front, uninitLen⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [sessionMemmoveFrontToEndAcpSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, huninit_le⟩, hmem⟩
  rw [memRegion_eq_exists_bytes (base + BitVec.ofNat 64 bs_front.length) uninitLen huninit_le,
      sepExists_sepConj_left, sepExists_sepConj_right] at hmem
  rw [satisfies_sepExists] at hmem
  obtain ⟨bs_uninit, hmem⟩ := hmem
  have hmem1 : s0.mem ⊨
      ⌜bs_uninit.length = uninitLen⌝ ∗
        (((base + BitVec.ofNat 64 bs_front.length) ↦ₛ bs_uninit) ∗
          ((base ↦ₛ bs_front) ∗ (stackAt s0.sp hookStack ∗ R))) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  rw [satisfies_pure_sepConj] at hmem1
  rcases hmem1 with ⟨hbs_uninit, hmem1⟩
  have hpre' : s0.mem ⊨
      (sessionMemmoveAcpSpec hookStack).pre
        (base, bs_front ++ bs_uninit, uninitLen, 0, bs_front.length) s0 ∗ R := by
    dsimp only [sessionMemmoveAcpSpec, sessionMemmoveSpec, libcMemmoveSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, by rw [BitVec.add_zero]; exact hx1, hx2,
      by rw [List.length_append, hbs_uninit]; omega,
      by rw [List.length_append]; omega⟩, ?_⟩
    rw [pointsToBytes_append, sepConj_assoc]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem1
  refine hmm.mono_outcome (base, bs_front ++ bs_uninit, uninitLen, 0, bs_front.length) R s0
      hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hfail
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [sessionMemmoveAcpSpec, sessionMemmoveFrontToEndAcpSpec] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    refine ⟨hpost.1, ?_⟩
    have hent := pointsToBytes_listMove_append_entails base bs_front bs_uninit
    rw [hbs_uninit] at hent
    have hpost2 := Satisfies.mono (sepConj_mono_left hent) hpost.2
    simpa only [sepConj_assoc] using hpost2
  · exact Or.inr hfail

/-! ## `AllocCallPreserved` `finish_grow [local#8]` and `RawVec<ChainEpoch>::grow_one` -/

section SymbolicExec

attribute [local irreducible] AllocCallPreserved

private theorem memRegion_24_eq (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v2) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v0)) :=
  CryptoVerification.SpqrV1.Alloc.memRegion_24 a

def finishGrow8AllocAcpSpecG (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hookStack : Nat) :
    Spec (CryptoVerification.LibsignalTripleRatchet.FinishGrowCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
      s.readReg64 .x3 = x.new ∧ s.readReg64 .x4 = x.align ∧ s.readReg64 .x5 = x.stride ∧
      x.cap = 0#64 ∧ x.bs = [] ∧ x.cap.toNat ≤ x.new.toNat ∧
      0 < x.new.toNat ∧ 0 < x.stride.toNat ∧
      RustLayoutOk (x.new.toNat * x.stride.toNat) x.align.toNat ∧
      FitsEvents M lim st (rustAllocEvents (x.new.toNat * x.stride.toNat) x.align.toNat)⌝ ∗
    memRegion x.out 24 ∗
    A.pool lim st s ∗ stackAt s.sp (hookStack + 48)
  post := fun (x, st) s0 sf =>
    ∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ p'.toNat % x.align.toNat = 0 ∧ AllocCallPreserved s0 sf⌝ ∗
      (x.out ↦₆₄ 0#64) ∗ ((x.out + 8#64) ↦₆₄ p') ∗
      ((x.out + 16#64) ↦₆₄ BitVec.ofNat 64 (x.new.toNat * x.stride.toNat)) ∗
      A.live p' (x.new.toNat * x.stride.toNat) x.align.toNat ∗
      memRegion p' (x.new.toNat * x.stride.toNat) ∗
      A.pool lim (M.stepEvents (rustAllocEvents (x.new.toNat * x.stride.toNat) x.align.toNat) st) sf ∗
      stackAt s0.sp (hookStack + 48)

def finishGrow8ReallocAcpSpecG (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hookStack : Nat) :
    Spec (CryptoVerification.LibsignalTripleRatchet.FinishGrowCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
      s.readReg64 .x3 = x.new ∧ s.readReg64 .x4 = x.align ∧ s.readReg64 .x5 = x.stride ∧
      x.cap ≠ 0#64 ∧ x.bs.length ≤ x.cap.toNat * x.stride.toNat ∧ x.cap.toNat ≤ x.new.toNat ∧
      0 < x.new.toNat ∧ 0 < x.stride.toNat ∧
      RustLayoutOk (x.new.toNat * x.stride.toNat) x.align.toNat ∧
      FitsEvents M lim st
        (rustReallocEvents (x.cap.toNat * x.stride.toNat) (x.new.toNat * x.stride.toNat)
          x.align.toNat)⌝ ∗
    memRegion x.out 24 ∗
    A.live x.ptr (x.cap.toNat * x.stride.toNat) x.align.toNat ∗ (x.ptr ↦ₛ x.bs) ∗
    memRegion (x.ptr + BitVec.ofNat 64 x.bs.length)
      (x.cap.toNat * x.stride.toNat - x.bs.length) ∗
    A.pool lim st s ∗ stackAt s.sp (hookStack + 48)
  post := fun (x, st) s0 sf =>
    ∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ p'.toNat % x.align.toNat = 0 ∧ AllocCallPreserved s0 sf⌝ ∗
      (x.out ↦₆₄ 0#64) ∗ ((x.out + 8#64) ↦₆₄ p') ∗
      ((x.out + 16#64) ↦₆₄ BitVec.ofNat 64 (x.new.toNat * x.stride.toNat)) ∗
      A.live p' (x.new.toNat * x.stride.toNat) x.align.toNat ∗ (p' ↦ₛ x.bs) ∗
      memRegion (p' + BitVec.ofNat 64 x.bs.length)
        (x.new.toNat * x.stride.toNat - x.bs.length) ∗
      A.pool lim
        (M.stepEvents
          (rustReallocEvents (x.cap.toNat * x.stride.toNat) (x.new.toNat * x.stride.toNat)
            x.align.toNat) st)
        sf ∗
      stackAt s0.sp (hookStack + 48)

theorem finish_grow_8_zero_acp_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : hookStack + 48 ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (lsρ spqrRustNoAllocShimSym) (session2ShimAcpSpecWithStack hookStack))
    (halloc : subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (lsρ spqrRustAllocSym) (rustCliAllocNoOomSpecWithStack M A lim false hookStack)) :
    subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (blkPl_361).base
      (finishGrow8AllocAcpSpecG M A lim hookStack) := by
  unfold finishGrow8AllocAcpSpecG
  simp only [memRegion_24_eq, stackAt_finishGrow_gen _ hhook,
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  wp_init x s0
  rcases x with ⟨⟨out, cap, ptr, new, align, stride, bs⟩, st⟩
  dsimp only at *
  rcases ‹cap = 0#64› with rfl
  rcases ‹bs = []› with rfl
  have hrlay : RustLayoutOk (new.toNat * stride.toNat) align.toNat := by assumption
  rcases hrlay with ⟨⟨hsz_pos, hpow, hbound⟩, hal_le⟩
  have hfits : FitsEvents M lim st (rustAllocEvents (new.toNat * stride.toNat) align.toNat) := by
    assumption
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
  have hacp_sf : AllocCallPreserved s0 sf :=
    acp_chain_acp ‹AllocCallPreserved _ sf›
      (by simp only [arm64_norm, wp_norm, allocCallPreserved_self])
  rw [← A.pool_of_vmPreserved ‹VmPreserved _ sf›]
  wp_steps_sync_pool (lsρ spqrRustAllocSym)
  simp only [State.setMem_setMem]
  simp only [Bool.false_eq_true, ↓reduceIte] at halloc
  wp_call halloc (new.toNat * stride.toNat, align.toNat, st)
  have hacp_sf1 : AllocCallPreserved s0 sf_1 :=
    acp_chain_acp ‹AllocCallPreserved _ sf_1›
      (by simp only [arm64_norm, wp_norm, hacp_sf])
  have hmul_bv : stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) :=
    mul_stride_eq_ofNat hlt64
  wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
  simp only [State.setMem_setMem]
  apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists
    (sf_1.readReg64 Reg.x0)
  wp_done

theorem finish_grow_8_ne_acp_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : hookStack + 48 ≤ 2 ^ 64 := by decide)
    (hrealloc : subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (lsρ spqrRustReallocSym) (rustCliReallocNoOomSpecWithStack M A lim hookStack)) :
    subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (blkPl_361).base
      (finishGrow8ReallocAcpSpecG M A lim hookStack) := by
  unfold finishGrow8ReallocAcpSpecG
  simp only [memRegion_24_eq, stackAt_finishGrow_gen _ hhook,
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  wp_init x s0
  rcases x with ⟨⟨out, cap, ptr, new, align, stride, bs⟩, st⟩
  dsimp only at *
  have hrlay : RustLayoutOk (new.toNat * stride.toNat) align.toNat := by assumption
  rcases hrlay with ⟨⟨hsz_pos, hpow, hbound⟩, hal_le⟩
  have hcap_ne : cap ≠ 0#64 := by assumption
  have hcap_le_new : cap.toNat ≤ new.toNat := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat * stride.toNat := by assumption
  have hfits : FitsEvents M lim st
      (rustReallocEvents (cap.toNat * stride.toNat) (new.toNat * stride.toNat) align.toNat) := by
    assumption
  have hlt64 : new.toNat * stride.toNat < 2 ^ 64 := by omega
  have hcap_le : cap.toNat * stride.toNat ≤ new.toNat * stride.toNat :=
    Nat.mul_le_mul_right stride.toNat hcap_le_new
  have hcap_lt64 : cap.toNat * stride.toNat < 2 ^ 64 := by omega
  have humulh := umulh_stride_eq_zero hlt64
  have hhi := hi_stride_eq_false hbound
  have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap_ne
  have hmul : (stride * new).toNat = new.toNat * stride.toNat := mul_stride_toNat hlt64
  have hmul_cap : (stride * cap).toNat = cap.toNat * stride.toNat := mul_stride_toNat hcap_lt64
  have hle_new : bs.length ≤ new.toNat * stride.toNat := by omega
  have hlay : RustLayoutOk (new.toNat * stride.toNat) align.toNat :=
    ⟨⟨hsz_pos, hpow, hbound⟩, hal_le⟩
  wp_steps_sync_pool (lsρ spqrRustReallocSym)
  simp only [State.setMem_setMem]
  wp_call hrealloc (ptr, cap.toNat * stride.toNat, align.toNat, new.toNat * stride.toNat, bs, st)
  have hacp_sf : AllocCallPreserved s0 sf :=
    acp_chain_acp ‹AllocCallPreserved _ sf›
      (by simp only [arm64_norm, wp_norm, allocCallPreserved_self])
  have hmul_bv : stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) :=
    mul_stride_eq_ofNat hlt64
  wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
  simp only [State.setMem_setMem]
  apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists
    (sf.readReg64 Reg.x0)
  wp_done

def finishGrow8ZeroCellsAcpSpecG (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hookStack : Nat) : Spec (FG8CellsGhost M.σ) where
  pre := fun (out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp, st) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.readReg64 .x4 = align ∧ s.readReg64 .x5 = stride ∧
      s.sp = fsp ∧ cap = 0#64 ∧ bs = [] ∧ cap.toNat ≤ new.toNat ∧
      0 < new.toNat ∧ 0 < stride.toNat ∧
      RustLayoutOk (new.toNat * stride.toNat) align.toNat ∧
      FitsEvents M lim st (rustAllocEvents (new.toNat * stride.toNat) align.toNat)⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.pool lim st s ∗ stackAt fsp (hookStack + 48)
  post := fun (out, _cap, _ptr, new, align, stride, _bs, _o0, _o1, _o2, fsp, st) s0 sf =>
    ∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ p'.toNat % align.toNat = 0 ∧ AllocCallPreserved s0 sf⌝ ∗
      (out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ p') ∗
      ((out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * stride.toNat)) ∗
      A.live p' (new.toNat * stride.toNat) align.toNat ∗
      memRegion p' (new.toNat * stride.toNat) ∗
      A.pool lim (M.stepEvents (rustAllocEvents (new.toNat * stride.toNat) align.toNat) st) sf ∗
      stackAt fsp (hookStack + 48)

def finishGrow8NeCellsAcpSpecG (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hookStack : Nat) : Spec (FG8CellsGhost M.σ) where
  pre := fun (out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp, st) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.readReg64 .x4 = align ∧ s.readReg64 .x5 = stride ∧
      s.sp = fsp ∧ cap ≠ 0#64 ∧ bs.length ≤ cap.toNat * stride.toNat ∧ cap.toNat ≤ new.toNat ∧
      0 < new.toNat ∧ 0 < stride.toNat ∧
      RustLayoutOk (new.toNat * stride.toNat) align.toNat ∧
      FitsEvents M lim st
        (rustReallocEvents (cap.toNat * stride.toNat) (new.toNat * stride.toNat) align.toNat)⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.live ptr (cap.toNat * stride.toNat) align.toNat ∗ (ptr ↦ₛ bs) ∗
    memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat * stride.toNat - bs.length) ∗
    A.pool lim st s ∗ stackAt fsp (hookStack + 48)
  post := fun (out, cap, _ptr, new, align, stride, bs, _o0, _o1, _o2, fsp, st) s0 sf =>
    ∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ p'.toNat % align.toNat = 0 ∧ AllocCallPreserved s0 sf⌝ ∗
      (out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ p') ∗
      ((out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * stride.toNat)) ∗
      A.live p' (new.toNat * stride.toNat) align.toNat ∗ (p' ↦ₛ bs) ∗
      memRegion (p' + BitVec.ofNat 64 bs.length) (new.toNat * stride.toNat - bs.length) ∗
      A.pool lim
        (M.stepEvents
          (rustReallocEvents (cap.toNat * stride.toNat) (new.toNat * stride.toNat) align.toNat) st)
        sf ∗
      stackAt fsp (hookStack + 48)

theorem finish_grow_8_zero_cells_acp_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : hookStack + 48 ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (lsρ spqrRustNoAllocShimSym) (session2ShimAcpSpecWithStack hookStack))
    (halloc : subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (lsρ spqrRustAllocSym) (rustCliAllocNoOomSpecWithStack M A lim false hookStack)) :
    subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (blkPl_361).base
      (finishGrow8ZeroCellsAcpSpecG M A lim hookStack) := by
  have hfg := finish_grow_8_zero_acp_placed_ok_of_hooks hhook hshim halloc
  refine subroutine_ok_outcome_intro
    fun ⟨out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [finishGrow8ZeroCellsAcpSpecG, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap0, hbs, hle, hpos, hstr, hlay, hfits⟩,
    hmem⟩
  subst hfsp; subst hcap0; subst hbs
  let hcall : CryptoVerification.LibsignalTripleRatchet.FinishGrowCall :=
    ⟨out, 0#64, ptr, new, align, stride, []⟩
  have hpre' : s0.mem ⊨ (finishGrow8AllocAcpSpecG M A lim hookStack).pre (hcall, st) s0 ∗ R := by
    simp only [finishGrow8AllocAcpSpecG, hcall, memRegion_24_eq,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, trivial, trivial, hle, hpos, hstr, hlay, hfits⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  refine hfg.mono_outcome (hcall, st) R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | hfail
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [finishGrow8AllocAcpSpecG, finishGrow8ZeroCellsAcpSpecG, hcall,
      sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨p', hq⟩
    exact ⟨p', by simpa only [sepConj_assoc] using hq⟩
  · exact Or.inr hfail

theorem finish_grow_8_ne_cells_acp_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : hookStack + 48 ≤ 2 ^ 64 := by decide)
    (hrealloc : subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (lsρ spqrRustReallocSym) (rustCliReallocNoOomSpecWithStack M A lim hookStack)) :
    subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (blkPl_361).base
      (finishGrow8NeCellsAcpSpecG M A lim hookStack) := by
  have hfg := finish_grow_8_ne_acp_placed_ok_of_hooks hhook hrealloc
  refine subroutine_ok_outcome_intro
    fun ⟨out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [finishGrow8NeCellsAcpSpecG, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap, hbs, hle, hpos, hstr, hlay, hfits⟩,
    hmem⟩
  subst hfsp
  let hcall : CryptoVerification.LibsignalTripleRatchet.FinishGrowCall :=
    ⟨out, cap, ptr, new, align, stride, bs⟩
  have hpre' : s0.mem ⊨ (finishGrow8ReallocAcpSpecG M A lim hookStack).pre (hcall, st) s0 ∗ R := by
    simp only [finishGrow8ReallocAcpSpecG, hcall, memRegion_24_eq,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hcap, hbs, hle, hpos, hstr, hlay, hfits⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  refine hfg.mono_outcome (hcall, st) R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hfail
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [finishGrow8ReallocAcpSpecG, finishGrow8NeCellsAcpSpecG, hcall,
      sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨p', hpost⟩
    exact ⟨p', by simpa only [sepConj_assoc] using hpost⟩
  · exact Or.inr hfail

attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg_setPC_pre readReg_setMem_setPC_pre
  pc_setMem_pre status_setMem_pre pstate_setMem_pre trace_setMem_pre
  calleeSavedVRegs_setMem_pre

/-- `AllocCallPreserved` budget contract for `RawVec<ChainEpoch>::grow_one` (`stride = 112, align = 8`). -/
def growOneChainEpochBsAcpSpecWithStack (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hookStack : Nat) : Spec (GrowGhost × M.σ) where
  pre := fun ((v, cap, ptr, bs), st) s =>
    ⌜s.readReg64 .x0 = v ∧ bs.length ≤ cap.toNat * 112 ∧ ptr ≠ 0#64 ∧
      max (2 * cap.toNat) 4 * 112 + 8 ≤ 2 ^ 63 ∧
      FitsEnv M lim st (GrowOneStrideEnv cap 112 8)⌝ ∗
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
    (if cap = 0#64 then emp
     else A.live ptr (cap.toNat * 112) 8 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat * 112 - bs.length)) ∗
    A.pool lim st s ∗ stackAt s.sp ((hookStack + 48) + 64)
  post := fun ((v, cap, _, bs), st) s0 sf =>
    ⌜AllocCallPreserved s0 sf⌝ ∗
    (∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ p'.toNat % 8 = 0⌝ ∗
      (v ↦₆₄ BitVec.ofNat 64 (max (2 * cap.toNat) 4)) ∗ ((v + 8#64) ↦₆₄ p') ∗
      A.live p' (max (2 * cap.toNat) 4 * 112) 8 ∗ (p' ↦ₛ bs) ∗
      memRegion (p' + BitVec.ofNat 64 bs.length) (max (2 * cap.toNat) 4 * 112 - bs.length)) ∗
    A.pool lim (M.stepEvents (growOneStrideEvents cap 112 8) st) sf ∗
    stackAt s0.sp ((hookStack + 48) + 64)

abbrev growOneChainEpochBsAcpSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (GrowGhost × M.σ) :=
  growOneChainEpochBsAcpSpecWithStack M A lim allocHookStack

theorem grow_one_chain_epoch_bs_acp_placed_ok_of_fg [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : (hookStack + 48) + 8 * 8 ≤ 2 ^ 64)
    (_h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hfg0_blk : subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (blkPl_361).base (finishGrow8ZeroCellsAcpSpecG M A lim hookStack))
    (hfg1_blk : subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (blkPl_361).base (finishGrow8NeCellsAcpSpecG M A lim hookStack)) :
    subroutine_ok ((blkPC_356).rebase (blkPl_356).base H)
      (blkPl_356).base
      (withLsCodeLoaded lsmpl (growOneChainEpochBsAcpSpecWithStack M A lim hookStack)) := by
  unfold withLsCodeLoaded growOneChainEpochBsAcpSpecWithStack
  simp only [stackAt_growOne_gen _ hhook]
  cells_unfold
  wp_init x s0
  rcases x with ⟨⟨v, cap, ptr, bs⟩, st⟩
  dsimp only at *
  have hcl : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hbs_le : bs.length ≤ cap.toNat * 112 := by assumption
  have hbound : max (2 * cap.toNat) 4 * 112 + 8 ≤ 2 ^ 63 := by omega
  have hfits_env : FitsEnv M lim st (GrowOneStrideEnv cap 112 8) := by assumption
  have hnew_lt63 : max (2 * cap.toNat) 4 < 2 ^ 63 := by omega
  have hnew_eq := grow_new_cap_eq hnew_lt63
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
    have hfits : FitsEvents M lim st (rustAllocEvents (new.toNat * 112) 8) := by
      rw [fitsEnv_growOneStride_iff] at hfits_env
      simpa only [growOneStrideEvents, ↓reduceIte, hnew_toNat, hm4] using hfits_env
    have hnew_eq0 : (if (4#64).ult (0#64 <<< 1) = true then 0#64 <<< 1 else 4#64) = new := hnew_eq
    have hmul_eq : max (2 * 0) 4 * 112 = new.toNat * 112 := by rw [hnew_toNat]
    simp only [ite_true, emp_sepConj, pointsToBytes_nil, List.length_nil,
      BitVec.add_zero, BitVec.toNat_ofNat, Nat.zero_mod, Nat.sub_zero,
      growOneStrideEvents, hmul_eq]
    apply sepWP_seq_lscl hcl (mid := lsmpl.base 361)
    wp_steps_sync_pool (lsmpl.base 361)
    simp only [State.setMem_setMem]
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) ?_
    intro hcl_m
    have hfg0 := lscall_blk (callerProg := (blkPC_356).rebase (blkPl_356).base H) hfg0_blk hcl_m
    wp_call hfg0 (s0.sp - 56#64, 0#64, ptr, new, 8#64, 112#64, [],
      v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64, st)
    have hacp : AllocCallPreserved s0 sf :=
      acp_chain_acp ‹AllocCallPreserved _ sf›
        (by simp only [arm64_norm, wp_norm, allocCallPreserved_self])
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    wp_done
  · have hfits : FitsEvents M lim st (rustReallocEvents (cap.toNat * 112) (new.toNat * 112) 8) := by
      rw [fitsEnv_growOneStride_iff] at hfits_env
      simpa only [growOneStrideEvents, hcap0, ↓reduceIte, hnew_toNat] using hfits_env
    simp only [hcap0, ite_false, growOneStrideEvents, sepConj_assoc]
    rw [← hnew_toNat]
    apply sepWP_seq_lscl hcl (mid := lsmpl.base 361)
    wp_steps_sync_pool (lsmpl.base 361)
    simp only [State.setMem_setMem]
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) ?_
    intro hcl_m
    have hfg1 := lscall_blk (callerProg := (blkPC_356).rebase (blkPl_356).base H) hfg1_blk hcl_m
    wp_call hfg1 (s0.sp - 56#64, cap, ptr, new, 8#64, 112#64, bs,
      v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64, st)
    have hacp : AllocCallPreserved s0 sf :=
      acp_chain_acp ‹AllocCallPreserved _ sf›
        (by simp only [arm64_norm, wp_norm, allocCallPreserved_self])
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    wp_done

end SymbolicExec

theorem grow_one_chain_epoch_bs_acp_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_356).rebase (blkPl_356).base H)
      (blkPl_356).base
      (withLsCodeLoaded lsmpl (growOneChainEpochBsAcpSpec M A lim)) :=
  grow_one_chain_epoch_bs_acp_placed_ok_of_fg (hookStack := allocHookStack) (by decide) h_panic
    (finish_grow_8_zero_cells_acp_placed_ok_of_hooks (by decide)
      (session2ShimAcpWithStack_of_rustAllocShimVm allocHookStack (spqr_hook_ok_of_mem hshim))
      (subroutine_ok_allocNoOom_withStack_of_hookSat halloc spqr_externAt?_of_mem))
    (finish_grow_8_ne_cells_acp_placed_ok_of_hooks (by decide)
      (subroutine_ok_reallocNoOom_withStack_of_hookSat hrealloc spqr_externAt?_of_mem))

end LibsignalBinary.Proofs.SpqrV1.Alloc.VecDequeGrowBudgetAux

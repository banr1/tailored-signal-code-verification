/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.VecDequeGrow
public import LibsignalBinary.Proofs.SpqrV1.Alloc.VecDequeGrowBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneBudget
public import LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget
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
import LibsignalBinary.Proofs.SpqrV1.Alloc.VecDequeHeap
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable `<VecDeque<spqr::chain::ChainEpoch>>::grow` (Block 353)

Proves `RustCliAllocBudget M` `[LibsignalPlacement]` contracts for block 353 across
non-wrapping, wrapping-`memcpy`, and wrapping-`memmove` branches, assembling
`Chain.DefsBudget.vecDequeGrowSpec`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Alloc.VecDequeGrowBudget

open Arm64 ProofLib
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement
  blkPC_353 blkPC_356
  blkPl_353 blkPl_356
  extract_withLsCodeLoaded lscall_blk_cl lsmpl lsρ sepWP_seq_lscl
  withLsCodeLoaded
)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SpqrV1.ChainProofs (
  chainEpochAlign chainEpochAt chainEpochSize
  newCapChainEpoch vecDequeAt
)
open CryptoVerification.SpqrV1.Alloc (
  VecDequeGrowGhost VecDequeGrowWrapGhost
  chainEpochHeaps growOneStack spqrHandleErrorSym spqrMemcpySym spqrMemmoveSym
  spqrRustAllocSym spqrRustNoAllocShimSym spqrRustReallocSym
  spqr_hook_ok_of_mem
  vecDequeAt_head_zero_entails_bytes vecDequeAt_head_zero_of_post
  vecDequeAt_wrap_entails_bytes vecDequeAt_wrap_memcpy_of_post
  vecDequeAt_wrap_memmove_of_post
  vecDequeGrowStack
)
open CryptoVerification.SpqrV1.Alloc.GrowOneNorm (
  readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre
  readReg64_setPC_pre readReg_setMem_setPC_pre readReg_setPC_pre
  sp_setMem_setPC_pre sp_setPC_pre
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel BudgetLimits FitsEnv FitsEvents
  RustCliAllocBudget VmPreserved
  rustAllocEvents rustCliAllocBudgetSpec rustCliReallocBudgetSpec
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
open LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneBudget (
  GrowOneStrideEnv fitsEnv_growOneStride_iff
  growOneStrideEvents
)
open LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux (
  acp_chain_acp framelessMemcpyAcpSpec
)
open LibsignalBinary.Proofs.SpqrV1.Alloc.VecDequeGrowBudgetAux (
  session_memmove_front_to_end_acp_ok
)
open LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget (
  VecDequeGrowEnv vecDequeGrowEvents vecDequeGrowSpec
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
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg_setPC_pre readReg_setMem_setPC_pre
  pc_setMem_pre status_setMem_pre pstate_setMem_pre trace_setMem_pre
  calleeSavedVRegs_setMem_pre

/-! ## Re-Exports from `VecDequeGrowBudgetAux` and Branch Helpers -/

theorem fitsEnv_vecDequeGrow_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {x : CryptoVerification.SpqrV1.ChainProofs.VecDequeGrowGhost} :
    FitsEnv M lim st (VecDequeGrowEnv x) ↔
      FitsEvents M lim st (vecDequeGrowEvents x.cap) :=
  VecDequeGrowBudgetAux.fitsEnv_vecDequeGrow_iff

theorem growOneStrideEvents_112_8_eq (cap : BitVec 64) :
    growOneStrideEvents cap 112 8 = vecDequeGrowEvents cap :=
  VecDequeGrowBudgetAux.growOneStrideEvents_112_8_eq cap

abbrev sessionMemmoveAcpSpec (hookStack : Nat := 4096) :=
  VecDequeGrowBudgetAux.sessionMemmoveAcpSpec hookStack

theorem hookMemmove_sessionMemmoveAcp_ok (hookStack : Nat := 4096) :
    HookOk hookMemmove (sessionMemmoveAcpSpec hookStack) :=
  VecDequeGrowBudgetAux.hookMemmove_sessionMemmoveAcp_ok hookStack

abbrev finishGrow8ZeroCellsAcpSpecG := VecDequeGrowBudgetAux.finishGrow8ZeroCellsAcpSpecG
abbrev finishGrow8NeCellsAcpSpecG := VecDequeGrowBudgetAux.finishGrow8NeCellsAcpSpecG
abbrev growOneChainEpochBsAcpSpecWithStack :=
  VecDequeGrowBudgetAux.growOneChainEpochBsAcpSpecWithStack
abbrev growOneChainEpochBsAcpSpec := VecDequeGrowBudgetAux.growOneChainEpochBsAcpSpec

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
  VecDequeGrowBudgetAux.grow_one_chain_epoch_bs_acp_placed_ok h_panic hshim halloc hrealloc

private theorem stackAt_vecDequeGrow (sp : BitVec 64) :
    stackAt sp vecDequeGrowStack =
      stackAt (sp - 32#64) growOneStack ∗ cells (sp - 32#64) 4 :=
  ProofLib.stackAt_split_cells sp 4208 4 (by decide)

private theorem stackAt_extHookStack_vecDequeGrow (sp : BitVec 64) :
    stackAt sp extHookStack =
      stackAt sp vecDequeGrowStack ∗ memRegion (sp - 16384#64) 12144 := by
  have hsplit : stackAt sp extHookStack =
      memRegion (sp - 16384#64) 12144 ∗ stackAt sp vecDequeGrowStack := by
    change memRegion (sp - 16384#64) 16384 =
      memRegion (sp - 16384#64) 12144 ∗ memRegion (sp - 4240#64) 4240
    rw [ProofLib.memRegion_split (sp - 16384#64) 12144 4240 (by decide),
      bv_sub_add_lit sp 16384 12144 (by decide)]
  rw [hsplit, sepConj_comm]

private theorem vec_deque_nonwrap_ule {cap head len : BitVec 64}
    (h : head.toNat + len.toNat ≤ cap.toNat) :
    head.ule (cap - len) = true := by
  have hle : len.toNat ≤ cap.toNat := by omega
  rw [BitVec.ule_eq_decide, decide_eq_true_iff, BitVec.toNat_sub_of_le hle]
  omega

private theorem vec_deque_wrap_ule_false {cap head : BitVec 64}
    (h : 0 < head.toNat) :
    head.ule (cap - cap) = false := by
  rw [BitVec.sub_self, BitVec.ule_eq_decide, decide_eq_false_iff_not]
  change ¬ (head.toNat ≤ 0)
  omega

private theorem vec_deque_memcpy_branch {cap head : BitVec 64}
    (h1 : head.toNat < cap.toNat) (h2 : head.toNat < cap.toNat - head.toNat) :
    (cap - head).ule head = false := by
  have hsub1 : (cap - head).toNat = cap.toNat - head.toNat :=
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)
  rw [BitVec.ule_eq_decide, decide_eq_false_iff_not, hsub1]
  omega

private theorem vec_deque_memcpy_fit {cap head : BitVec 64}
    (h1 : head.toNat < cap.toNat)
    (hmax : max (2 * cap.toNat) 4 * 112 + 8 ≤ 2 ^ 63) :
    (BitVec.ofNat 64 (max (2 * cap.toNat) 4) - cap).ult head = false := by
  have hnc : (BitVec.ofNat 64 (max (2 * cap.toNat) 4)).toNat = max (2 * cap.toNat) 4 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hle : cap ≤ BitVec.ofNat 64 (max (2 * cap.toNat) 4) := by
    rw [BitVec.le_def, hnc]; omega
  have hsub1 : (BitVec.ofNat 64 (max (2 * cap.toNat) 4) - cap).toNat =
      max (2 * cap.toNat) 4 - cap.toNat := by
    rw [BitVec.toNat_sub_of_le hle, hnc]
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, hsub1]
  omega

private theorem vec_deque_memmove_branch {cap head : BitVec 64}
    (h1 : head.toNat < cap.toNat) (h2 : cap.toNat - head.toNat ≤ head.toNat) :
    (cap - head).ule head = true := by
  have hsub1 : (cap - head).toNat = cap.toNat - head.toNat :=
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)
  rw [BitVec.ule_eq_decide, decide_eq_true_iff, hsub1]
  omega

private theorem shift_128_sub_16_toNat {x : BitVec 64} (h : x.toNat * 128 < 2 ^ 64) :
    (x <<< 7 - x <<< 4).toNat = x.toNat * 112 := by
  have h7 : (x <<< 7).toNat = x.toNat * 128 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
  have h4 : (x <<< 4).toNat = x.toNat * 16 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
  have hle : x <<< 4 ≤ x <<< 7 := by
    rw [BitVec.le_def, h4, h7]; omega
  rw [BitVec.toNat_sub_of_le hle, h7, h4]
  omega

private theorem madd_112_eq (p x : BitVec 64) (_h : x.toNat * 112 < 2 ^ 64) :
    p + x * 112#64 = p + BitVec.ofNat 64 (x.toNat * 112) := by
  have hx : x * 112#64 = BitVec.ofNat 64 (x.toNat * 112) := by
    apply BitVec.eq_of_toNat_eq
    have h112 : (112#64 : BitVec 64).toNat = 112 := rfl
    rw [BitVec.toNat_mul, h112, BitVec.toNat_ofNat]
  rw [hx]

/-! ## Branch Budget Contracts -/

/-- Non-wrapping budget contract (`head + len ≤ cap`). -/
def vecDequeGrowNonwrapBsSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (VecDequeGrowGhost × M.σ) where
  pre := fun ((d, cap, ptr, head, len, bs), st) s =>
    let newCap := max (2 * cap.toNat) 4
    ⌜s.readReg64 .x0 = d ∧ bs.length ≤ cap.toNat * 112 ∧ ptr ≠ 0#64 ∧
      head.toNat + len.toNat ≤ cap.toNat ∧
      newCap * 112 + 8 ≤ 2 ^ 63 ∧
      FitsEnv M lim st (GrowOneStrideEnv cap 112 8)⌝ ∗
    (d ↦₆₄ cap) ∗ ((d + 8#64) ↦₆₄ ptr) ∗
    ((d + 16#64) ↦₆₄ head) ∗ ((d + 24#64) ↦₆₄ len) ∗
    (if cap = 0#64 then emp
     else A.live ptr (cap.toNat * 112) 8 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat * 112 - bs.length)) ∗
    A.pool lim st s ∗ stackAt s.sp vecDequeGrowStack
  post := fun ((d, cap, _ptr, head, len, bs), st) s0 sf =>
    let newCap := max (2 * cap.toNat) 4
    ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf⌝ ∗
    (∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ p'.toNat % 8 = 0⌝ ∗
      (d ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((d + 8#64) ↦₆₄ p') ∗
      ((d + 16#64) ↦₆₄ head) ∗ ((d + 24#64) ↦₆₄ len) ∗
      A.live p' (newCap * 112) 8 ∗ (p' ↦ₛ bs) ∗
      memRegion (p' + BitVec.ofNat 64 bs.length) (newCap * 112 - bs.length)) ∗
    A.pool lim (M.stepEvents (growOneStrideEvents cap 112 8) st) sf ∗
    stackAt s0.sp vecDequeGrowStack

/-- Empty-`VecDeque` budget contract (`cap = 0, head = 0, len = 0`). -/
def vecDequeGrowEmptySpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec ((BitVec 64 × BitVec 64) × M.σ) where
  pre := fun ((d, ptr), st) s =>
    ⌜s.readReg64 .x0 = d ∧ ptr ≠ 0#64 ∧
      FitsEnv M lim st (GrowOneStrideEnv 0#64 112 8)⌝ ∗
    (d ↦₆₄ 0#64) ∗ ((d + 8#64) ↦₆₄ ptr) ∗
    ((d + 16#64) ↦₆₄ 0#64) ∗ ((d + 24#64) ↦₆₄ 0#64) ∗
    A.pool lim st s ∗ stackAt s.sp vecDequeGrowStack
  post := fun ((d, _), st) s0 sf =>
    ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf⌝ ∗
    (∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ p'.toNat % 8 = 0⌝ ∗
      (d ↦₆₄ 4#64) ∗ ((d + 8#64) ↦₆₄ p') ∗
      ((d + 16#64) ↦₆₄ 0#64) ∗ ((d + 24#64) ↦₆₄ 0#64) ∗
      A.live p' 448 8 ∗ memRegion p' 448) ∗
    A.pool lim (M.stepEvents (rustAllocEvents 448 8) st) sf ∗
    stackAt s0.sp vecDequeGrowStack

/-- Wrapping `memcpy` budget contract (`head < cap - head`). -/
def vecDequeGrowWrapMemcpyBsSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (VecDequeGrowWrapGhost × M.σ) where
  pre := fun ((d, cap, ptr, head, bs_back, bs_front), st) s =>
    let newCap := max (2 * cap.toNat) 4
    ⌜s.readReg64 .x0 = d ∧ ptr ≠ 0#64 ∧
      0 < head.toNat ∧ head.toNat < cap.toNat ∧
      head.toNat < cap.toNat - head.toNat ∧
      bs_back.length = head.toNat * 112 ∧
      bs_front.length = (cap.toNat - head.toNat) * 112 ∧
      newCap * 112 + 8 ≤ 2 ^ 63 ∧
      FitsEnv M lim st (GrowOneStrideEnv cap 112 8)⌝ ∗
    (d ↦₆₄ cap) ∗ ((d + 8#64) ↦₆₄ ptr) ∗
    ((d + 16#64) ↦₆₄ head) ∗ ((d + 24#64) ↦₆₄ cap) ∗
    A.live ptr (cap.toNat * 112) 8 ∗
    (ptr ↦ₛ (bs_back ++ bs_front)) ∗
    A.pool lim st s ∗ stackAt s.sp vecDequeGrowStack
  post := fun ((d, cap, _ptr, head, bs_back, bs_front), st) s0 sf =>
    let newCap := max (2 * cap.toNat) 4
    ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf⌝ ∗
    (∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ p'.toNat % 8 = 0⌝ ∗
      (d ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((d + 8#64) ↦₆₄ p') ∗
      ((d + 16#64) ↦₆₄ head) ∗ ((d + 24#64) ↦₆₄ cap) ∗
      A.live p' (newCap * 112) 8 ∗
      memRegion p' (head.toNat * 112) ∗
      ((p' + BitVec.ofNat 64 (head.toNat * 112)) ↦ₛ (bs_front ++ bs_back)) ∗
      memRegion (p' + BitVec.ofNat 64 ((cap.toNat + head.toNat) * 112))
        ((newCap - (cap.toNat + head.toNat)) * 112)) ∗
    A.pool lim (M.stepEvents (growOneStrideEvents cap 112 8) st) sf ∗
    stackAt s0.sp vecDequeGrowStack

/-- Wrapping `memmove` budget contract (`cap - head ≤ head`). -/
def vecDequeGrowWrapMemmoveBsSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (VecDequeGrowWrapGhost × M.σ) where
  pre := fun ((d, cap, ptr, head, bs_back, bs_front), st) s =>
    let newCap := max (2 * cap.toNat) 4
    ⌜s.readReg64 .x0 = d ∧ ptr ≠ 0#64 ∧
      0 < head.toNat ∧ head.toNat < cap.toNat ∧
      cap.toNat - head.toNat ≤ head.toNat ∧
      bs_back.length = head.toNat * 112 ∧
      bs_front.length = (cap.toNat - head.toNat) * 112 ∧
      newCap * 112 + 8 ≤ 2 ^ 63 ∧
      FitsEnv M lim st (GrowOneStrideEnv cap 112 8)⌝ ∗
    (d ↦₆₄ cap) ∗ ((d + 8#64) ↦₆₄ ptr) ∗
    ((d + 16#64) ↦₆₄ head) ∗ ((d + 24#64) ↦₆₄ cap) ∗
    A.live ptr (cap.toNat * 112) 8 ∗
    (ptr ↦ₛ (bs_back ++ bs_front)) ∗
    A.pool lim st s ∗ stackAt s.sp vecDequeGrowStack
  post := fun ((d, cap, _ptr, head, bs_back, bs_front), st) s0 sf =>
    let newCap := max (2 * cap.toNat) 4
    let newHead := newCap - (cap.toNat - head.toNat)
    ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf⌝ ∗
    (∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ p'.toNat % 8 = 0⌝ ∗
      (d ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((d + 8#64) ↦₆₄ p') ∗
      ((d + 16#64) ↦₆₄ BitVec.ofNat 64 newHead) ∗ ((d + 24#64) ↦₆₄ cap) ∗
      A.live p' (newCap * 112) 8 ∗
      (p' ↦ₛ bs_back) ∗
      memRegion (p' + BitVec.ofNat 64 (head.toNat * 112)) ((newCap - cap.toNat) * 112) ∗
      ((p' + BitVec.ofNat 64 (newHead * 112)) ↦ₛ bs_front)) ∗
    A.pool lim (M.stepEvents (growOneStrideEvents cap 112 8) st) sf ∗
    stackAt s0.sp vecDequeGrowStack

/-! ## Relocatable Branch Proofs (Block 353) -/

private theorem intro_withLsCodeLoaded {α : Type} {pl : Obj.MultiPlacement}
    {spec : Spec α} {x : α} {s0 : State} {R : SepProp}
    (hcl : LibsignalCodeLoaded pl s0.mem)
    (hpre : s0.mem ⊨ spec.pre x s0 ∗ R) :
    s0.mem ⊨ (withLsCodeLoaded pl spec).pre x s0 ∗ R := by
  dsimp only [withLsCodeLoaded]
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  exact ⟨hcl, hpre⟩

private def growOneChainEpochCallAcpSpecG (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64 × M.σ) where
  pre := fun (v, cap, ptr, bs, gsp, st) s =>
    ⌜s.readReg64 .x0 = v ∧ s.sp = gsp ∧ bs.length ≤ cap.toNat * 112 ∧ ptr ≠ 0#64 ∧
      max (2 * cap.toNat) 4 * 112 + 8 ≤ 2 ^ 63 ∧
      FitsEnv M lim st (GrowOneStrideEnv cap 112 8)⌝ ∗
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
    (if cap = 0#64 then emp
     else A.live ptr (cap.toNat * 112) 8 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat * 112 - bs.length)) ∗
    A.pool lim st s ∗ stackAt gsp growOneStack
  post := fun (v, cap, _ptr, bs, gsp, st) s0 sf =>
    ∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ p'.toNat % 8 = 0 ∧ AllocCallPreserved s0 sf⌝ ∗
      (v ↦₆₄ BitVec.ofNat 64 (max (2 * cap.toNat) 4)) ∗ ((v + 8#64) ↦₆₄ p') ∗
      A.live p' (max (2 * cap.toNat) 4 * 112) 8 ∗ (p' ↦ₛ bs) ∗
      memRegion (p' + BitVec.ofNat 64 bs.length) (max (2 * cap.toNat) 4 * 112 - bs.length) ∗
      A.pool lim (M.stepEvents (growOneStrideEvents cap 112 8) st) sf ∗
      stackAt gsp growOneStack

private theorem grow_one_chain_epoch_call_acp_placed_ok_of_bs [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {addr : BitVec 64}
    (hbs : subroutine_ok P addr
      (withLsCodeLoaded lsmpl (growOneChainEpochBsAcpSpec M A lim))) :
    subroutine_ok P addr
      (withLsCodeLoaded lsmpl (growOneChainEpochCallAcpSpecG M A lim)) := by
  refine subroutine_ok_outcome_intro fun ⟨v, cap, ptr, bs, gsp, st⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl, hpre⟩
  simp only [growOneChainEpochCallAcpSpecG, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hgsp, hbs_le, hptr, hmax, hfits⟩, hmem⟩
  subst hgsp
  have hpre' : s0.mem ⊨
      (withLsCodeLoaded lsmpl (growOneChainEpochBsAcpSpec M A lim)).pre
        ((v, cap, ptr, bs), st) s0 ∗ R := by
    refine intro_withLsCodeLoaded hcl ?_
    simp only [growOneChainEpochBsAcpSpec, VecDequeGrowBudgetAux.growOneChainEpochBsAcpSpec,
      VecDequeGrowBudgetAux.growOneChainEpochBsAcpSpecWithStack,
      sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hbs_le, hptr, hmax, hfits⟩, hmem⟩
  refine hbs.mono_outcome ((v, cap, ptr, bs), st) R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | hfail
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [growOneChainEpochBsAcpSpec,
      VecDequeGrowBudgetAux.growOneChainEpochBsAcpSpec,
      VecDequeGrowBudgetAux.growOneChainEpochBsAcpSpecWithStack,
      growOneChainEpochCallAcpSpecG, growOneStack,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨p', hq⟩
    refine ⟨p', ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    exact ⟨⟨hq.2.1.1, hq.2.1.2, hq.1⟩, hq.2.2⟩
  · exact Or.inr hfail

private def sessionMemmoveFrontToEndCallAcpSpec (hookStack : Nat) :
    Spec (BitVec 64 × List (BitVec 8) × Nat × BitVec 64) where
  pre := fun (base, bs_front, uninitLen, gsp) s0 =>
    ⌜s0.readReg64 .x0 = base + BitVec.ofNat 64 uninitLen ∧
      s0.readReg64 .x1 = base ∧
      (s0.readReg64 .x2).toNat = bs_front.length ∧
      s0.sp = gsp ∧ uninitLen ≤ 2 ^ 64⌝ ∗
      (base ↦ₛ bs_front) ∗
      memRegion (base + BitVec.ofNat 64 bs_front.length) uninitLen ∗
      stackAt gsp hookStack
  post := fun (base, bs_front, uninitLen, gsp) s0 sf =>
    ⌜sf.readReg64 .x0 = base + BitVec.ofNat 64 uninitLen ∧
      AllocCallPreserved s0 sf ∧ VmPreserved s0 sf⌝ ∗
      memRegion base uninitLen ∗
      ((base + BitVec.ofNat 64 uninitLen) ↦ₛ bs_front) ∗
      stackAt gsp hookStack

private theorem session_memmove_front_to_end_call_acp_ok {prog : Program} {addr : BitVec 64}
    {hookStack : Nat} (hmm : subroutine_ok prog addr (sessionMemmoveAcpSpec hookStack)) :
    subroutine_ok prog addr (sessionMemmoveFrontToEndCallAcpSpec hookStack) := by
  have hfe := session_memmove_front_to_end_acp_ok hmm
  refine subroutine_ok_outcome_intro fun ⟨base, bs_front, uninitLen, gsp⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [sessionMemmoveFrontToEndCallAcpSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hgsp, huninit⟩, hmem⟩
  subst hgsp
  have hpre' : s0.mem ⊨
      (VecDequeGrowBudgetAux.sessionMemmoveFrontToEndAcpSpec hookStack).pre
        (base, bs_front, uninitLen) s0 ∗ R := by
    simp only [VecDequeGrowBudgetAux.sessionMemmoveFrontToEndAcpSpec,
      sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, huninit⟩, hmem⟩
  exact hfe.mono_outcome (base, bs_front, uninitLen) R s0 hpc hrun hpre' hsp fun _ hout => hout

private def growOneChainEpochFullCallAcpSpecG (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64 × M.σ) where
  pre := fun (v, cap, ptr, bs, gsp, st) s =>
    ⌜s.readReg64 .x0 = v ∧ s.sp = gsp ∧ cap ≠ 0#64 ∧ bs.length = cap.toNat * 112 ∧ ptr ≠ 0#64 ∧
      max (2 * cap.toNat) 4 * 112 + 8 ≤ 2 ^ 63 ∧
      FitsEnv M lim st (GrowOneStrideEnv cap 112 8)⌝ ∗
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
    A.live ptr (cap.toNat * 112) 8 ∗ (ptr ↦ₛ bs) ∗
    A.pool lim st s ∗ stackAt gsp growOneStack
  post := fun (v, cap, _ptr, bs, gsp, st) s0 sf =>
    ∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ p'.toNat % 8 = 0 ∧ AllocCallPreserved s0 sf⌝ ∗
      (v ↦₆₄ BitVec.ofNat 64 (max (2 * cap.toNat) 4)) ∗ ((v + 8#64) ↦₆₄ p') ∗
      A.live p' (max (2 * cap.toNat) 4 * 112) 8 ∗ (p' ↦ₛ bs) ∗
      memRegion (p' + BitVec.ofNat 64 bs.length) (max (2 * cap.toNat) 4 * 112 - bs.length) ∗
      A.pool lim (M.stepEvents (growOneStrideEvents cap 112 8) st) sf ∗
      stackAt gsp growOneStack

private theorem grow_one_chain_epoch_full_call_acp_placed_ok_of_bs [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {addr : BitVec 64}
    (hbs : subroutine_ok P addr
      (withLsCodeLoaded lsmpl (growOneChainEpochBsAcpSpec M A lim))) :
    subroutine_ok P addr
      (withLsCodeLoaded lsmpl (growOneChainEpochFullCallAcpSpecG M A lim)) := by
  have hg := grow_one_chain_epoch_call_acp_placed_ok_of_bs hbs
  refine subroutine_ok_outcome_intro fun ⟨v, cap, ptr, bs, gsp, st⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl, hpre⟩
  simp only [growOneChainEpochFullCallAcpSpecG, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hgsp, hcap_ne, hbs_eq, hptr, hmax, hfits⟩, hmem⟩
  have hpre' : s0.mem ⊨
      (withLsCodeLoaded lsmpl (growOneChainEpochCallAcpSpecG M A lim)).pre
        (v, cap, ptr, bs, gsp, st) s0 ∗ R := by
    refine intro_withLsCodeLoaded hcl ?_
    simp only [growOneChainEpochCallAcpSpecG, hcap_ne, ↓reduceIte, hbs_eq, Nat.sub_self,
      memRegion_zero, sepConj_emp, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hgsp, Nat.le_refl _, hptr, hmax, hfits⟩, hmem⟩
  exact hg.mono_outcome (v, cap, ptr, bs, gsp, st) R s0 hpc hrun hpre' hsp fun _ hout => hout

/-- Block 353 meets `withLsCodeLoaded lsmpl (vecDequeGrowNonwrapBsSpec M A lim)`. -/
theorem vec_deque_grow_nonwrap_bs_placed_ok_of_grow [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hgrow : subroutine_ok ((blkPC_356).rebase (blkPl_356).base H)
      (blkPl_356).base (withLsCodeLoaded lsmpl (growOneChainEpochBsAcpSpec M A lim))) :
    subroutine_ok ((blkPC_353).rebase (blkPl_353).base H)
      (blkPl_353).base
      (withLsCodeLoaded lsmpl (vecDequeGrowNonwrapBsSpec M A lim)) := by
  unfold withLsCodeLoaded vecDequeGrowNonwrapBsSpec
  simp only [stackAt_vecDequeGrow, sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  wp_init x s0
  rcases x with ⟨⟨d, cap, ptr, head, len, bs⟩, st⟩
  dsimp only at *
  have hcl : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hule := vec_deque_nonwrap_ule (cap := cap) (head := head) (len := len) (by omega)
  apply sepWP_seq_lscl hcl (mid := lsmpl.base 356)
  wp_steps_sync_pool (lsmpl.base 356)
  simp only [State.setMem_setMem]
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) ?_
  intro hcl_m
  have hgrow_call := lscall_blk_cl (callerProg := (blkPC_353).rebase (blkPl_353).base H)
    (grow_one_chain_epoch_call_acp_placed_ok_of_bs hgrow) hcl_m
  wp_call hgrow_call (d, cap, ptr, bs, s0.sp - 32#64, st)
  have hacp_sf : AllocCallPreserved s0 sf :=
    acp_chain_acp ‹AllocCallPreserved _ sf›
      (by simp only [arm64_norm, wp_norm, allocCallPreserved_self])
  have htr_sf : sf.trace = s0.trace := hacp_sf.2.1
  rcases hacp_sf with ⟨_, _, _, _, _, _, _⟩
  wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
  simp only [State.setMem_setMem]
  wp_done

theorem vec_deque_grow_nonwrap_bs_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_353).rebase (blkPl_353).base H)
      (blkPl_353).base
      (withLsCodeLoaded lsmpl (vecDequeGrowNonwrapBsSpec M A lim)) :=
  vec_deque_grow_nonwrap_bs_placed_ok_of_grow
    (grow_one_chain_epoch_bs_acp_placed_ok h_panic hshim halloc hrealloc)

theorem vec_deque_grow_empty_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_353).rebase (blkPl_353).base H)
      (blkPl_353).base
      (withLsCodeLoaded lsmpl (vecDequeGrowEmptySpec M A lim)) := by
  have h := vec_deque_grow_nonwrap_bs_placed_ok h_panic hshim halloc hrealloc
  refine subroutine_ok_outcome_intro fun ⟨⟨d, ptr⟩, st⟩ R s0 hpc hrun hpre hsp => ?_
  have hpre' : s0.mem ⊨
      (withLsCodeLoaded lsmpl (vecDequeGrowNonwrapBsSpec M A lim)).pre
        ((d, 0#64, ptr, 0#64, 0#64, []), st) s0 ∗ R := by
    simp only [vecDequeGrowEmptySpec, vecDequeGrowNonwrapBsSpec,
      BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero,
      List.length_nil, Nat.le_refl, ite_true, emp_sepConj, sepConj_assoc,
      satisfies_pure_sepConj] at hpre ⊢
    exact ⟨⟨hpre.1.1, trivial, hpre.1.2.1, trivial, by decide, hpre.1.2.2⟩, hpre.2⟩
  refine h.mono_outcome ((d, 0#64, ptr, 0#64, 0#64, []), st) R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | hfail)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    have h0 : max (2 * (0#64 : BitVec 64).toNat) 4 = 4 := rfl
    have hevs : growOneStrideEvents 0#64 112 8 = rustAllocEvents 448 8 := rfl
    simp only [vecDequeGrowEmptySpec, vecDequeGrowNonwrapBsSpec, h0, hevs,
      Nat.sub_zero, List.length_nil, BitVec.add_zero, pointsToBytes_nil, emp_sepConj,
      sepExists_sepConj_left, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact hpost
  · exact Or.inr hfail

/-- Block 353 meets `withLsCodeLoaded lsmpl (vecDequeGrowWrapMemcpyBsSpec M A lim)`. -/
theorem vec_deque_grow_wrap_memcpy_bs_placed_ok_of_grow [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hgrow : subroutine_ok ((blkPC_356).rebase (blkPl_356).base H)
      (blkPl_356).base (withLsCodeLoaded lsmpl (growOneChainEpochBsAcpSpec M A lim)))
    (hmc : subroutine_ok ((blkPC_353).rebase (blkPl_353).base H)
      (lsρ spqrMemcpySym) framelessMemcpyAcpSpec) :
    subroutine_ok ((blkPC_353).rebase (blkPl_353).base H)
      (blkPl_353).base
      (withLsCodeLoaded lsmpl (vecDequeGrowWrapMemcpyBsSpec M A lim)) := by
  unfold withLsCodeLoaded vecDequeGrowWrapMemcpyBsSpec
  simp only [stackAt_vecDequeGrow, sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  wp_init x s0
  rcases x with ⟨⟨d, cap, ptr, head, bs_back, bs_front⟩, st⟩
  dsimp only at *
  have hcl : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hhead_pos : 0 < head.toNat := ‹_›
  have hhead_lt : head.toNat < cap.toNat := ‹_›
  have hbranch : head.toNat < cap.toNat - head.toNat := ‹_›
  have hbs_back : bs_back.length = head.toNat * 112 := ‹_›
  have hbs_front : bs_front.length = (cap.toNat - head.toNat) * 112 := ‹_›
  have hmax : max (2 * cap.toNat) 4 * 112 + 8 ≤ 2 ^ 63 := by omega
  have hcap_ne : cap ≠ 0#64 := by
    intro h0; rw [h0] at hhead_lt; change head.toNat < 0 at hhead_lt; omega
  have hbs_len : (bs_back ++ bs_front).length = cap.toNat * 112 := by
    rw [List.length_append, hbs_back, hbs_front]; omega
  have hule1 := vec_deque_wrap_ule_false (cap := cap) hhead_pos
  have hule2 := vec_deque_memcpy_branch hhead_lt hbranch
  have hult3 := vec_deque_memcpy_fit hhead_lt hmax
  have hsub_head : cap - (cap - head) = head := by bv_arith
  have hshift_head : (head <<< 7 - head <<< 4).toNat = head.toNat * 112 :=
    shift_128_sub_16_toNat (by omega)
  apply sepWP_seq_lscl hcl (mid := lsmpl.base 356)
  wp_steps_sync_pool (lsmpl.base 356)
  simp only [State.setMem_setMem]
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) ?_
  intro hcl_m
  have hgrow_call := lscall_blk_cl (callerProg := (blkPC_353).rebase (blkPl_353).base H)
    (grow_one_chain_epoch_full_call_acp_placed_ok_of_bs hgrow) hcl_m
  wp_call hgrow_call (d, cap, ptr, bs_back ++ bs_front, s0.sp - 32#64, st)
  let v0 := w
  have hacp_sm : AllocCallPreserved s0 sf :=
    acp_chain_acp ‹AllocCallPreserved _ sf›
      (by simp only [arm64_norm, wp_norm, allocCallPreserved_self])
  have hmadd_cap : v0 + cap * 112#64 = v0 + BitVec.ofNat 64 (cap.toNat * 112) :=
    madd_112_eq v0 cap (by omega)
  have hsplit_bs : (v0 ↦ₛ (bs_back ++ bs_front)) =
      (v0 ↦ₛ bs_back) ∗ ((v0 + BitVec.ofNat 64 (head.toNat * 112)) ↦ₛ bs_front) := by
    rw [pointsToBytes_append, hbs_back]
  have hsplit_reg :
      memRegion (v0 + BitVec.ofNat 64 (bs_back ++ bs_front).length)
        (max (2 * cap.toNat) 4 * 112 - (bs_back ++ bs_front).length) =
      memRegion (v0 + BitVec.ofNat 64 (cap.toNat * 112)) bs_back.length ∗
        memRegion (v0 + BitVec.ofNat 64 ((cap.toNat + head.toNat) * 112))
          ((max (2 * cap.toNat) 4 - (cap.toNat + head.toNat)) * 112) := by
    rw [hbs_len, hbs_back]
    have hlen_eq : max (2 * cap.toNat) 4 * 112 - cap.toNat * 112 =
        head.toNat * 112 + (max (2 * cap.toNat) 4 - (cap.toNat + head.toNat)) * 112 := by
      have : max (2 * cap.toNat) 4 - cap.toNat =
          head.toNat + (max (2 * cap.toNat) 4 - (cap.toNat + head.toNat)) := by omega
      calc max (2 * cap.toNat) 4 * 112 - cap.toNat * 112
          = (max (2 * cap.toNat) 4 - cap.toNat) * 112 := (Nat.sub_mul _ _ 112).symm
        _ = (head.toNat + (max (2 * cap.toNat) 4 - (cap.toNat + head.toNat))) * 112 := by rw [this]
        _ = head.toNat * 112 + (max (2 * cap.toNat) 4 - (cap.toNat + head.toNat)) * 112 :=
          Nat.add_mul _ _ 112
    have hoff : v0 + BitVec.ofNat 64 (cap.toNat * 112) + BitVec.ofNat 64 (head.toNat * 112) =
        v0 + BitVec.ofNat 64 ((cap.toNat + head.toNat) * 112) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.add_mul]
    rw [hlen_eq,
      memRegion_split (v0 + BitVec.ofNat 64 (cap.toNat * 112)) (head.toNat * 112) _ (by omega),
      hoff]
  wp_conv_pre => rw [hsplit_bs, hsplit_reg]
  wp_steps_sync_pool (lsρ spqrMemcpySym)
  simp only [State.setMem_setMem]
  wp_call hmc (v0 + BitVec.ofNat 64 (cap.toNat * 112), v0, bs_back)
  have hacp_sf1 : AllocCallPreserved s0 sf_1 :=
    acp_chain_acp ‹AllocCallPreserved _ sf_1› (by simp only [arm64_norm, wp_norm, hacp_sm])
  have htr_sf1 : sf_1.trace = s0.trace := hacp_sf1.2.1
  rcases hacp_sf1 with ⟨_, _, _, _, _, _, _⟩
  rw [← A.pool_of_vmPreserved ‹VmPreserved _ sf_1›]
  have hreg_back : (v0 ↦ₛ bs_back) ⊢ memRegion v0 (head.toNat * 112) := by
    rw [← hbs_back]
    exact pointsToBytes_entails_memRegion v0 bs_back
  have hcomb_fb :
      ((v0 + BitVec.ofNat 64 (head.toNat * 112)) ↦ₛ bs_front) ∗
        ((v0 + BitVec.ofNat 64 (cap.toNat * 112)) ↦ₛ bs_back) =
      ((v0 + BitVec.ofNat 64 (head.toNat * 112)) ↦ₛ (bs_front ++ bs_back)) := by
    rw [pointsToBytes_append, hbs_front]
    have hoff : v0 + BitVec.ofNat 64 (head.toNat * 112) +
        BitVec.ofNat 64 ((cap.toNat - head.toNat) * 112) =
        v0 + BitVec.ofNat 64 (cap.toNat * 112) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.add_mul]
      congr 2; omega
    rw [hoff]
  apply SepWP.fold hreg_back (by sep_focus)
  apply SepWP.fold (Entails.of_eq hcomb_fb) (by sep_focus)
  wp_done

theorem vec_deque_grow_wrap_memcpy_bs_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H spqrMemcpySym framelessMemcpyAcpSpec) :
    subroutine_ok ((blkPC_353).rebase (blkPl_353).base H)
      (blkPl_353).base
      (withLsCodeLoaded lsmpl (vecDequeGrowWrapMemcpyBsSpec M A lim)) :=
  vec_deque_grow_wrap_memcpy_bs_placed_ok_of_grow
    (grow_one_chain_epoch_bs_acp_placed_ok h_panic hshim halloc hrealloc)
    (spqr_hook_ok_of_mem hmc)

/-- Block 353 meets `withLsCodeLoaded lsmpl (vecDequeGrowWrapMemmoveBsSpec M A lim)`. -/
theorem vec_deque_grow_wrap_memmove_bs_placed_ok_of_grow [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hgrow : subroutine_ok ((blkPC_356).rebase (blkPl_356).base H)
      (blkPl_356).base (withLsCodeLoaded lsmpl (growOneChainEpochBsAcpSpec M A lim)))
    (hmm : subroutine_ok ((blkPC_353).rebase (blkPl_353).base H)
      (lsρ spqrMemmoveSym) (sessionMemmoveAcpSpec growOneStack)) :
    subroutine_ok ((blkPC_353).rebase (blkPl_353).base H)
      (blkPl_353).base
      (withLsCodeLoaded lsmpl (vecDequeGrowWrapMemmoveBsSpec M A lim)) := by
  have hmm_fe := session_memmove_front_to_end_call_acp_ok hmm
  unfold withLsCodeLoaded vecDequeGrowWrapMemmoveBsSpec
  simp only [stackAt_vecDequeGrow, sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  wp_init x s0
  rcases x with ⟨⟨d, cap, ptr, head, bs_back, bs_front⟩, st⟩
  dsimp only at *
  have hcl : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hhead_pos : 0 < head.toNat := ‹_›
  have hhead_lt : head.toNat < cap.toNat := ‹_›
  have hbranch : cap.toNat - head.toNat ≤ head.toNat := ‹_›
  have hbs_back : bs_back.length = head.toNat * 112 := ‹_›
  have hbs_front : bs_front.length = (cap.toNat - head.toNat) * 112 := ‹_›
  have hmax : max (2 * cap.toNat) 4 * 112 + 8 ≤ 2 ^ 63 := by omega
  have hcap_ne : cap ≠ 0#64 := by
    intro h0; rw [h0] at hhead_lt; change head.toNat < 0 at hhead_lt; omega
  have hbs_len : (bs_back ++ bs_front).length = cap.toNat * 112 := by
    rw [List.length_append, hbs_back, hbs_front]; omega
  have hule1 := vec_deque_wrap_ule_false (cap := cap) hhead_pos
  have hule2 := vec_deque_memmove_branch hhead_lt hbranch
  have hsub_head : cap - (cap - head) = head := by bv_arith
  have hnc : (BitVec.ofNat 64 (max (2 * cap.toNat) 4)).toNat = max (2 * cap.toNat) 4 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hch : (cap - head).toNat = cap.toNat - head.toNat :=
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)
  have hle_nc : cap - head ≤ BitVec.ofNat 64 (max (2 * cap.toNat) 4) := by
    rw [BitVec.le_def, hch, hnc]; omega
  have hsub_newHead :
      BitVec.ofNat 64 (max (2 * cap.toNat) 4) - (cap - head) =
        BitVec.ofNat 64 (max (2 * cap.toNat) 4 - (cap.toNat - head.toNat)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le hle_nc, hnc, hch,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hshift_front : ((cap - head) <<< 7 - (cap - head) <<< 4).toNat =
      (cap.toNat - head.toNat) * 112 := by
    rw [← hch]
    exact shift_128_sub_16_toNat (by omega)
  apply sepWP_seq_lscl hcl (mid := lsmpl.base 356)
  wp_steps_sync_pool (lsmpl.base 356)
  simp only [State.setMem_setMem]
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) ?_
  intro hcl_m
  have hgrow_call := lscall_blk_cl (callerProg := (blkPC_353).rebase (blkPl_353).base H)
    (grow_one_chain_epoch_full_call_acp_placed_ok_of_bs hgrow) hcl_m
  wp_call hgrow_call (d, cap, ptr, bs_back ++ bs_front, s0.sp - 32#64, st)
  let v0 := w
  have hacp_sm : AllocCallPreserved s0 sf :=
    acp_chain_acp ‹AllocCallPreserved _ sf›
      (by simp only [arm64_norm, wp_norm, allocCallPreserved_self])
  have hmadd_head : v0 + head * 112#64 = v0 + BitVec.ofNat 64 (head.toNat * 112) :=
    madd_112_eq v0 head (by omega)
  have hmadd_newHead :
      v0 + BitVec.ofNat 64 (max (2 * cap.toNat) 4 - (cap.toNat - head.toNat)) * 112#64 =
        v0 + BitVec.ofNat 64 (head.toNat * 112) +
          BitVec.ofNat 64 ((max (2 * cap.toNat) 4 - cap.toNat) * 112) := by
    have h1 := madd_112_eq v0
      (BitVec.ofNat 64 (max (2 * cap.toNat) 4 - (cap.toNat - head.toNat))) (by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)
    rw [h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.add_mul]
    congr 2; omega
  have hsplit_bs : (v0 ↦ₛ (bs_back ++ bs_front)) =
      (v0 ↦ₛ bs_back) ∗ ((v0 + BitVec.ofNat 64 (head.toNat * 112)) ↦ₛ bs_front) := by
    rw [pointsToBytes_append, hbs_back]
  have hreg_eq :
      memRegion (v0 + BitVec.ofNat 64 (bs_back ++ bs_front).length)
        (max (2 * cap.toNat) 4 * 112 - (bs_back ++ bs_front).length) =
      memRegion (v0 + BitVec.ofNat 64 (head.toNat * 112) + BitVec.ofNat 64 bs_front.length)
        ((max (2 * cap.toNat) 4 - cap.toNat) * 112) := by
    rw [hbs_len, hbs_front, ← Nat.sub_mul, BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.add_mul]
    congr 3; omega
  wp_conv_pre => rw [hsplit_bs, hreg_eq]
  wp_steps_sync_pool (lsρ spqrMemmoveSym)
  simp only [State.setMem_setMem]
  wp_call hmm_fe (v0 + BitVec.ofNat 64 (head.toNat * 112), bs_front,
    (max (2 * cap.toNat) 4 - cap.toNat) * 112, s0.sp - 32#64)
  have hacp_sf1 : AllocCallPreserved s0 sf_1 :=
    acp_chain_acp ‹AllocCallPreserved _ sf_1› (by simp only [arm64_norm, wp_norm, hacp_sm])
  have htr_sf1 : sf_1.trace = s0.trace := hacp_sf1.2.1
  rcases hacp_sf1 with ⟨_, _, _, _, _, _, _⟩
  rw [← A.pool_of_vmPreserved ‹VmPreserved _ sf_1›]
  have hoff_nh :
      v0 + BitVec.ofNat 64 (head.toNat * 112) +
        BitVec.ofNat 64 ((max (2 * cap.toNat) 4 - cap.toNat) * 112) =
      v0 + BitVec.ofNat 64 ((max (2 * cap.toNat) 4 - (cap.toNat - head.toNat)) * 112) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.add_mul]
    congr 2; omega
  wp_conv_pre => rw [hoff_nh]
  wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
  simp only [State.setMem_setMem]
  wp_done

theorem vec_deque_grow_wrap_memmove_bs_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmm : HookSat H spqrMemmoveSym (sessionMemmoveAcpSpec growOneStack)) :
    subroutine_ok ((blkPC_353).rebase (blkPl_353).base H)
      (blkPl_353).base
      (withLsCodeLoaded lsmpl (vecDequeGrowWrapMemmoveBsSpec M A lim)) :=
  vec_deque_grow_wrap_memmove_bs_placed_ok_of_grow
    (grow_one_chain_epoch_bs_acp_placed_ok h_panic hshim halloc hrealloc)
    (spqr_hook_ok_of_mem hmm)

/-! ## High-Level `vecDequeGrowSpec` Placed Proof -/

private theorem false_outcomes_elim {sf : State} {Q : SepProp} {P_out : Prop}
    (hfail :
      (sf.status = .Panicked ∧ sf.mem ⊨ ⌜False⌝ ∗ Q) ∨
      (∃ code, sf.status = .Exited code ∧ sf.mem ⊨ ⌜False⌝ ∗ Q) ∨
      (sf.status = .OutOfMemory ∧ sf.mem ⊨ ⌜False⌝ ∗ Q)) : P_out := by
  rcases hfail with ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, h⟩ <;>
    exact (not_satisfies_false_sepConj h).elim

/-- Block 353 meets `withLsCodeLoaded lsmpl (Chain.DefsBudget.vecDequeGrowSpec M A lim)`. -/
theorem vec_deque_grow_spec_placed_ok_of_branches [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {addr : BitVec 64}
    (h_nonwrap : subroutine_ok P addr (withLsCodeLoaded lsmpl (vecDequeGrowNonwrapBsSpec M A lim)))
    (h_memcpy : subroutine_ok P addr
      (withLsCodeLoaded lsmpl (vecDequeGrowWrapMemcpyBsSpec M A lim)))
    (h_memmove : subroutine_ok P addr
      (withLsCodeLoaded lsmpl (vecDequeGrowWrapMemmoveBsSpec M A lim))) :
    subroutine_ok P addr (withLsCodeLoaded lsmpl (vecDequeGrowSpec M A lim)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre0 hsp => ?_
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre0
  dsimp only [withLsCodeLoaded, vecDequeGrowSpec, newCapChainEpoch] at hpre ⊢
  simp only [stackAt_extHookStack_vecDequeGrow, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hlen, hmax, hfits_vd⟩, hmem⟩
  have hmax8 : max (2 * x.cap.toNat) 4 * 112 + 8 ≤ 2 ^ 63 := by
    change max (2 * x.cap.toNat) 4 * 112 < 2 ^ 63 at hmax
    omega
  have hfits_stride : FitsEnv M lim st (GrowOneStrideEnv x.cap 112 8) := by
    rw [fitsEnv_growOneStride_iff, growOneStrideEvents_112_8_eq]
    exact fitsEnv_vecDequeGrow_iff.mp hfits_vd
  by_cases hhead0 : x.head = 0#64
  · rw [hhead0] at hmem
    have hmem1 := Satisfies.mono
      (sepConj_mono_left (vecDequeAt_head_zero_entails_bytes A.repAlloc x.v x.cap x.ptr x.xs hlen))
      hmem
    simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
      satisfies_pure_sepConj] at hmem1
    rcases hmem1 with ⟨bs, ⟨hbs, hbs_len, hptr⟩, hmem1⟩
    let F := chainEpochHeaps A.repAlloc x.xs ∗ memRegion (s0.sp - 16384#64) 12144
    have hpre' : s0.mem ⊨
        (withLsCodeLoaded lsmpl (vecDequeGrowNonwrapBsSpec M A lim)).pre
          ((x.v, x.cap, x.ptr, 0#64, x.cap, bs), st) s0 ∗ (F ∗ R) := by
      refine intro_withLsCodeLoaded hcl0 ?_
      dsimp only [vecDequeGrowNonwrapBsSpec, F]
      simp only [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx0, by omega, hptr, by change 0 + x.cap.toNat ≤ x.cap.toNat; omega,
        hmax8, hfits_stride⟩, ?_⟩
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem1
    refine h_nonwrap.mono_outcome ((x.v, x.cap, x.ptr, 0#64, x.cap, bs), st) (F ∗ R)
      s0 hpc hrun hpre' hsp ?_
    rintro sf (⟨hret, hcc, hpost⟩ | hfail)
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [withLsCodeLoaded, vecDequeGrowNonwrapBsSpec, F] at hpost
      simp only [stackAt_extHookStack_vecDequeGrow, growOneStrideEvents_112_8_eq,
        sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists, sepConj_assoc,
        satisfies_pure_sepConj] at hpost ⊢
      rcases hpost with ⟨p', ⟨htr, hacp⟩, ⟨hp', _⟩, hpost⟩
      refine ⟨vecDequeGrowEvents x.cap, p', 0#64, ⟨htr, hacp, rfl⟩, fun _ => rfl, ?_⟩
      have hpost1 : sf.mem ⊨
          ((x.v ↦₆₄ BitVec.ofNat 64 (max (2 * x.cap.toNat) 4)) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
            ((x.v + 16#64) ↦₆₄ 0#64) ∗ ((x.v + 24#64) ↦₆₄ x.cap) ∗
            A.live p' (max (2 * x.cap.toNat) 4 * 112) 8 ∗
            (p' ↦ₛ bs) ∗
            memRegion (p' + BitVec.ofNat 64 bs.length) (max (2 * x.cap.toNat) 4 * 112 - bs.length) ∗
            chainEpochHeaps A.repAlloc x.xs) ∗
          (A.pool lim (M.stepEvents (vecDequeGrowEvents x.cap) st) sf ∗
            stackAt s0.sp vecDequeGrowStack ∗
            memRegion (s0.sp - 16384#64) 12144 ∗ R) :=
        Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
      have hpost2 := Satisfies.mono
        (sepConj_mono_left
          (vecDequeAt_head_zero_of_post A.repAlloc x.v x.cap p' x.xs hlen hbs hmax hp'))
        hpost1
      simpa only [sepConj_assoc] using hpost2
    · exact false_outcomes_elim hfail
  · have hhead_pos : 0 < x.head.toNat := by
      refine Nat.pos_of_ne_zero fun h0 => hhead0 ?_
      exact BitVec.eq_of_toNat_eq h0
    have hmem1 := Satisfies.mono
      (sepConj_mono_left
        (vecDequeAt_wrap_entails_bytes A.repAlloc x.v x.cap x.ptr x.head x.xs hlen hhead_pos))
      hmem
    simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
      satisfies_pure_sepConj] at hmem1
    rcases hmem1 with ⟨bs_back, bs_front,
      ⟨hhead_lt, hptr, hbs_back, hbs_front, hlen_back, hlen_front⟩, hmem1⟩
    let F := chainEpochHeaps A.repAlloc (x.xs.drop (x.cap.toNat - x.head.toNat)) ∗
      chainEpochHeaps A.repAlloc (x.xs.take (x.cap.toNat - x.head.toNat)) ∗
      memRegion (s0.sp - 16384#64) 12144
    by_cases hcmp : x.head.toNat < x.cap.toNat - x.head.toNat
    · have hpre' : s0.mem ⊨
          (withLsCodeLoaded lsmpl (vecDequeGrowWrapMemcpyBsSpec M A lim)).pre
            ((x.v, x.cap, x.ptr, x.head, bs_back, bs_front), st) s0 ∗ (F ∗ R) := by
        refine intro_withLsCodeLoaded hcl0 ?_
        dsimp only [vecDequeGrowWrapMemcpyBsSpec, F]
        simp only [sepConj_assoc, satisfies_pure_sepConj]
        refine ⟨⟨hx0, hptr, hhead_pos, hhead_lt, hcmp, hlen_back, hlen_front,
          hmax8, hfits_stride⟩, ?_⟩
        exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem1
      refine h_memcpy.mono_outcome
        ((x.v, x.cap, x.ptr, x.head, bs_back, bs_front), st) (F ∗ R)
        s0 hpc hrun hpre' hsp ?_
      rintro sf (⟨hret, hcc, hpost⟩ | hfail)
      · refine Or.inl ⟨hret, hcc, ?_⟩
        dsimp only [withLsCodeLoaded, vecDequeGrowWrapMemcpyBsSpec, F] at hpost
        simp only [stackAt_extHookStack_vecDequeGrow, growOneStrideEvents_112_8_eq,
          sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists, sepConj_assoc,
          satisfies_pure_sepConj] at hpost ⊢
        rcases hpost with ⟨p', ⟨htr, hacp⟩, ⟨hp', _⟩, hpost⟩
        refine ⟨vecDequeGrowEvents x.cap, p', x.head,
          ⟨htr, hacp, rfl⟩, fun h0 => (hhead0 h0).elim, ?_⟩
        have hpost1 : sf.mem ⊨
            ((x.v ↦₆₄ BitVec.ofNat 64 (max (2 * x.cap.toNat) 4)) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
              ((x.v + 16#64) ↦₆₄ x.head) ∗ ((x.v + 24#64) ↦₆₄ x.cap) ∗
              A.live p' (max (2 * x.cap.toNat) 4 * 112) 8 ∗
              memRegion p' (x.head.toNat * 112) ∗
              ((p' + BitVec.ofNat 64 (x.head.toNat * 112)) ↦ₛ (bs_front ++ bs_back)) ∗
              memRegion (p' + BitVec.ofNat 64 ((x.cap.toNat + x.head.toNat) * 112))
                ((max (2 * x.cap.toNat) 4 - (x.cap.toNat + x.head.toNat)) * 112) ∗
              chainEpochHeaps A.repAlloc (x.xs.drop (x.cap.toNat - x.head.toNat)) ∗
              chainEpochHeaps A.repAlloc (x.xs.take (x.cap.toNat - x.head.toNat))) ∗
            (A.pool lim (M.stepEvents (vecDequeGrowEvents x.cap) st) sf ∗
              stackAt s0.sp vecDequeGrowStack ∗
              memRegion (s0.sp - 16384#64) 12144 ∗ R) :=
          Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
        have hpost2 := Satisfies.mono
          (sepConj_mono_left (vecDequeAt_wrap_memcpy_of_post A.repAlloc x.v x.cap p' x.head x.xs
            hlen hhead_pos hcmp hbs_back hbs_front hmax hp'))
          hpost1
        simpa only [sepConj_assoc] using hpost2
      · exact false_outcomes_elim hfail
    · have hge : x.cap.toNat - x.head.toNat ≤ x.head.toNat := by omega
      have hpre' : s0.mem ⊨
          (withLsCodeLoaded lsmpl (vecDequeGrowWrapMemmoveBsSpec M A lim)).pre
            ((x.v, x.cap, x.ptr, x.head, bs_back, bs_front), st) s0 ∗ (F ∗ R) := by
        refine intro_withLsCodeLoaded hcl0 ?_
        dsimp only [vecDequeGrowWrapMemmoveBsSpec, F]
        simp only [sepConj_assoc, satisfies_pure_sepConj]
        refine ⟨⟨hx0, hptr, hhead_pos, hhead_lt, hge, hlen_back, hlen_front,
          hmax8, hfits_stride⟩, ?_⟩
        exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem1
      refine h_memmove.mono_outcome
        ((x.v, x.cap, x.ptr, x.head, bs_back, bs_front), st) (F ∗ R)
        s0 hpc hrun hpre' hsp ?_
      rintro sf (⟨hret, hcc, hpost⟩ | hfail)
      · refine Or.inl ⟨hret, hcc, ?_⟩
        dsimp only [withLsCodeLoaded, vecDequeGrowWrapMemmoveBsSpec, F] at hpost
        simp only [stackAt_extHookStack_vecDequeGrow, growOneStrideEvents_112_8_eq,
          sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists, sepConj_assoc,
          satisfies_pure_sepConj] at hpost ⊢
        rcases hpost with ⟨p', ⟨htr, hacp⟩, ⟨hp', _⟩, hpost⟩
        refine ⟨vecDequeGrowEvents x.cap, p',
          BitVec.ofNat 64 (max (2 * x.cap.toNat) 4 - (x.cap.toNat - x.head.toNat)),
          ⟨htr, hacp, rfl⟩, fun h0 => (hhead0 h0).elim, ?_⟩
        have hpost1 : sf.mem ⊨
            ((x.v ↦₆₄ BitVec.ofNat 64 (max (2 * x.cap.toNat) 4)) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
              ((x.v + 16#64) ↦₆₄
                BitVec.ofNat 64 (max (2 * x.cap.toNat) 4 - (x.cap.toNat - x.head.toNat))) ∗
              ((x.v + 24#64) ↦₆₄ x.cap) ∗
              A.live p' (max (2 * x.cap.toNat) 4 * 112) 8 ∗
              (p' ↦ₛ bs_back) ∗
              memRegion (p' + BitVec.ofNat 64 (x.head.toNat * 112))
                ((max (2 * x.cap.toNat) 4 - x.cap.toNat) * 112) ∗
              ((p' + BitVec.ofNat 64
                ((max (2 * x.cap.toNat) 4 - (x.cap.toNat - x.head.toNat)) * 112)) ↦ₛ bs_front) ∗
              chainEpochHeaps A.repAlloc (x.xs.drop (x.cap.toNat - x.head.toNat)) ∗
              chainEpochHeaps A.repAlloc (x.xs.take (x.cap.toNat - x.head.toNat))) ∗
            (A.pool lim (M.stepEvents (vecDequeGrowEvents x.cap) st) sf ∗
              stackAt s0.sp vecDequeGrowStack ∗
              memRegion (s0.sp - 16384#64) 12144 ∗ R) :=
          Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
        have hpost2 := Satisfies.mono
          (sepConj_mono_left (vecDequeAt_wrap_memmove_of_post A.repAlloc x.v x.cap p' x.head x.xs
            hlen hhead_pos hhead_lt hge hbs_back hbs_front hmax hp'))
          hpost1
        simpa only [sepConj_assoc] using hpost2
      · exact false_outcomes_elim hfail

theorem vec_deque_grow_spec_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H spqrMemcpySym framelessMemcpyAcpSpec)
    (hmm : HookSat H spqrMemmoveSym (sessionMemmoveAcpSpec growOneStack)) :
    subroutine_ok ((blkPC_353).rebase (blkPl_353).base H)
      (blkPl_353).base
      (withLsCodeLoaded lsmpl (vecDequeGrowSpec M A lim)) :=
  vec_deque_grow_spec_placed_ok_of_branches
    (vec_deque_grow_nonwrap_bs_placed_ok h_panic hshim halloc hrealloc)
    (vec_deque_grow_wrap_memcpy_bs_placed_ok h_panic hshim halloc hrealloc hmc)
    (vec_deque_grow_wrap_memmove_bs_placed_ok h_panic hshim halloc hrealloc hmm)

end LibsignalBinary.Proofs.SpqrV1.Alloc.VecDequeGrowBudget

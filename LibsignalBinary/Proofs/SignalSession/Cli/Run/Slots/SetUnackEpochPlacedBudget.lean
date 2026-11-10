/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Common.SharedHelpers
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SessionStateCalleesBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.TopLevel.SessionInitiateACommon
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.SetUnackEpochPlaced
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import ProofLib.SepLogic.WP.Apply

/-!
# Budget-Threaded `SessionState::set_unacknowledged_pre_key_message` at `UNIX_EPOCH` (Placed)

Verifies Block `33` (`<SessionState>::set_unacknowledged_pre_key_message`) at `now = UNIX_EPOCH`
(`x5 = 0`, `w6 = 0`) against the budget-threaded `setUnackPreKeyMsgExactStackEpochSpecPlaced`
(with exact allocator event sequence `[.alloc 33, .alloc 33, .free 1 33]`) under
`[LibsignalPlacement]`, together with cross-block (`i < 619`) and `CliGhostAllocHooks`
specializations.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.SetUnackEpochPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoVerification (
  IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement
  lsMemcpySym lsRustAllocSym lsRustDeallocSym lsRustNoAllocShimSym
  ls_hook_ok_of_mem ls_subroutine_ok_cl_of_plain lsmpl lsρ sepWP_seq_lscl withLsCl withLsCodeLoaded
)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchet (sessionMemcpyRegionSpec sessionShimSpec)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  ls_subroutine_ok_rocl_of_block subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
  withLsCodeRoLoaded withLsRoCl
)
open CryptoVerification.E2E.Pqxdh.Initiator (
  Bytes blkPC_33 blkPl_33 bv_sub_add_lit' bytesToBv8 encodeEC instIsLsBlockProg_33
  readReg_setMem_setPC_pre readReg_setPC_pre
  readReg32_setMem_setPC_pre readReg32_setPC_pre
  readReg64_setMem_setPC_pre readReg64_setPC_pre
  sp_setMem_setPC_pre sp_setPC_pre stackAt_split_top vecU8
)
open CryptoVerification.E2E.Pqxdh.TopLevel (SetUnackExactGhost)
open CryptoVerification.SignalSession (
  CliHooks cliExternsPlaced durationSinceExactHook lsDurationSinceSym
)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliExternsPlaced_row cliGhostExterns)
open CryptoVerification.SignalSession.Cli.Slots (
  cliExternsPlaced_durationSinceEpochAlloc_sat cliGhostExterns_sat_of_cliExternsPlaced
  durationSinceEpochAllocSpec durationSinceEpochAtSpec durationSince_row_placed
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvent FitsEvents FitsStep RustCliAllocBudget
  VmPreserved coarseCostModel coarseStep coarseStepReserve rustAllocEvents rustCliAllocBudgetSpec
  rustCliAllocNoOomExternSpecWithStack rustCliDeallocBudgetSpec rustDeallocEvents
  subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  perm_write32_norm perm_write64_norm subroutine_ok_rustCliAllocNoOom_externWithStack
)
open LibsignalBinary.Heap.SpecBudget (hookSat_withVmPreserved withVmPreserved)
open LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SessionStateCalleesBudget (
  dealloc_bytes_placed_ok ecPubKeySerializeAllocEvents ecPubKeySerializeRawPlacedSpec
  ecPubKeySerializeRaw_placed_ok_of_session rustDeallocBytesSpec setUnackPreKeyMsgEvents
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (
  CliAllocHooks CliGhostAllocHooks cliExternsPlaced_alloc_budget_sat
  cliExternsPlaced_dealloc_budget_sat cliExternsPlaced_sessionMemcpyRegion_budget_sat
  cliExternsPlaced_shim_budget_sat
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec
)

/-! ## 1. Allocator event envelope and non-vacuity check -/

/-- Exact binary allocator event sequence of `<SessionState>::set_unacknowledged_pre_key_message`
(Block `33`): `[.alloc 33, .alloc 33, .free 1 33]`. -/
def setUnackPreKeyMsgEpochEvents : List AllocEvent :=
  setUnackPreKeyMsgEvents

def SetUnackPreKeyMsgEpochEnv (evs : List AllocEvent) : Prop :=
  evs = setUnackPreKeyMsgEpochEvents

theorem fitsEnv_setUnackPreKeyMsgEpochEnv_iff (M : AllocCostModel) (lim : BudgetLimits)
    (st : M.σ) :
    FitsEnv M lim st SetUnackPreKeyMsgEpochEnv ↔ FitsEvents M lim st setUnackPreKeyMsgEpochEvents :=
  FitsEnv.eq_iff

example :
    FitsEnv coarseCostModel ⟨64, 67108864, 536870912, true⟩ coarseCostModel.init
      SetUnackPreKeyMsgEpochEnv := by
  have hevs : setUnackPreKeyMsgEpochEvents = [.alloc 33, .alloc 33, .free 1 33] := by decide
  rw [fitsEnv_setUnackPreKeyMsgEpochEnv_iff, hevs]
  dsimp only [FitsEvents, FitsEvent, AllocEvent.withinMaxAlloc, FitsStep,
    AllocCostModel.step, coarseCostModel, coarseStep, coarseStepReserve]
  decide

/-! ## 2. `VmPreserved` `durationSinceEpochAllocBudgetSpec` -/

/-- `VmPreserved`-strengthened counterpart of `Slots.durationSinceEpochAllocSpec`
(`allocHookStack = 4096`). -/
def durationSinceEpochAllocBudgetSpec : Spec (BitVec 64 × BitVec 64) :=
  withVmPreserved durationSinceEpochAllocSpec

private theorem retHook_vm_local {f : State → State} {s : State} (h : VmPreserved s (f s)) :
    VmPreserved s (retHook f s) := h

private theorem setMem_vm_local (s : State) {m : Memory}
    (hp : ∀ a : BitVec 64, m.perm a = s.mem.perm a) :
    VmPreserved s (s.setMem m) :=
  ⟨⟨rfl, rfl, rfl⟩, rfl, hp, fun _ _ _ => rfl⟩

private theorem durationSinceExactHook_vm_local (s : State) :
    VmPreserved s (durationSinceExactHook s) := by
  unfold durationSinceExactHook; try dsimp only
  split
  · exact VmPreserved.refl s
  · try dsimp only
    split
    · refine retHook_vm_local (setMem_vm_local s fun a => ?_)
      simp only [perm_write32_norm, perm_write64_norm]
    · exact VmPreserved.refl s

theorem cliExternsPlaced_durationSinceEpochAlloc_budget_sat (mmpl : Obj.MultiPlacement)
    (W : CliHooks) :
    HookSat (cliExternsPlaced mmpl W) lsDurationSinceSym durationSinceEpochAllocBudgetSpec := by
  refine hookSat_withVmPreserved (cliExternsPlaced_durationSinceEpochAlloc_sat mmpl W) fun g hg s => ?_
  have hfeq : cliExternsPlaced mmpl W lsDurationSinceSym = some durationSinceExactHook :=
    cliExternsPlaced_row mmpl W (durationSince_row_placed mmpl W)
  rw [hfeq] at hg
  injection hg with hfg
  subst hfg
  exact durationSinceExactHook_vm_local s

/-! ## 3. Budget-threaded `[LibsignalPlacement]` specifications -/

/-- Budget-threaded image-free inner `Spec` of `<SessionState>::set_unacknowledged_pre_key_message`
(Block `33`) at `now = UNIX_EPOCH` (`x5 = 0`, `w6 = 0`), with `onPanic = ⌜False⌝` and
`onOom = ⌜False⌝` under `FitsEvents M lim st setUnackPreKeyMsgEpochEvents`. -/
def setUnackPreKeyMsgEpochInnerSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (SetUnackExactGhost × M.σ) where
  pre := fun (g, st) s =>
    ⌜s.readReg64 .x5 = 0#64 ∧ (s.readReg64 .x6).setWidth 32 = 0#32⌝ ∗
      ⌜s.readReg64 .x0 = g.statePtr ∧
        (s.readReg64 .x1).setWidth 32 = g.optOpkTag ∧
        (s.readReg64 .x2).setWidth 32 = g.optOpkVal ∧
        (s.readReg64 .x3).setWidth 32 = g.spkId ∧
        s.readReg64 .x4 = g.baseKeyPtr ∧
        g.baseKeyBytes.length = 32 ∧
        FitsEvents M lim st setUnackPreKeyMsgEpochEvents⌝ ∗
      (g.baseKeyPtr ↦ₛ bytesToBv8 g.baseKeyBytes) ∗
      ((g.statePtr + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64) ∗
      memRegion (g.statePtr + 0x100#64) 40 ∗
      stackAt (s.sp - 144#64) (allocHookStack + 32) ∗
      cells (s.sp - 144#64) 18 ∗
      A.pool lim st s
  post := fun (g, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (g.baseKeyPtr ↦ₛ bytesToBv8 g.baseKeyBytes) ∗
      vecU8 A.repAlloc (g.statePtr + 0xf8#64) (bytesToBv8 (encodeEC g.baseKeyBytes)) ∗
      ((g.statePtr + 0x110#64) ↦₃₂ g.optOpkTag) ∗
      ((g.statePtr + 0x114#64) ↦₃₂ g.optOpkVal) ∗
      ((g.statePtr + 0x118#64) ↦₆₄ 0#64) ∗
      ((g.statePtr + 0x120#64) ↦₃₂ g.spkId) ∗
      memRegion (g.statePtr + 0x124#64) 4 ∗
      stackAt (s0.sp - 144#64) (allocHookStack + 32) ∗
      cells (s0.sp - 144#64) 18 ∗
      A.pool lim (M.stepEvents setUnackPreKeyMsgEpochEvents st) sf

abbrev setUnackPreKeyMsgExactStackEpochSpecPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Spec (SetUnackExactGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl (setUnackPreKeyMsgEpochInnerSpec A lim)

/-! ## 4. Block-`33` proof and cross-block specializations -/

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff FitsEvent
attribute [local arm64_norm] bv_sub_add_lit bv_sub_add_lit' BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.read8_write64_264_271
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.read8_write64_408_415
  Memory.read8_write64_base_off_disjoint
  Memory.read64_write8_base_off_disjoint

@[local simp, local wp_norm, local arm64_norm]
private theorem cond_lt_subs_neg1_1_true_epoch_placed_budget :
    ConditionHolds CondCode.LT (subsPState64 0xffffffffffffffff#64 1#64) = true := by
  simp only [ConditionHolds, subsPState64]; decide

@[local simp, local wp_norm, local arm64_norm]
private theorem cond_ite_zero64_epoch_placed_budget (b : Bool) :
    (if b = true then 0#64 else 0#64) = 0#64 := by
  cases b <;> rfl

private theorem memRegion_16_split_64_epoch_placed_budget (a : BitVec 64) :
    memRegion a 16 =
      (∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64, (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1)) := by
  rw [ProofLib.memRegion_split a 8 8 (by decide), ProofLib.memRegion_eight a,
    ProofLib.memRegion_eight (a + 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

private theorem memRegion_24_split_64_epoch_placed_budget (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2)) := by
  rw [ProofLib.memRegion_split a 8 16 (by decide),
    ProofLib.memRegion_split (a + 8#64) 8 8 (by decide),
    ProofLib.memRegion_eight a, ProofLib.memRegion_eight (a + 8#64),
    ProofLib.memRegion_eight (a + 8#64 + 8#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right]

private theorem pointsTo64_triple_entails_memRegion24_epoch_placed_budget
    (a w0 w1 w2 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ⊢ memRegion a 24 := by
  rw [memRegion_24_split_64_epoch_placed_budget a]
  exact Entails.sepExists_right w2 (Entails.sepExists_right w1
    (Entails.sepExists_right w0 (Entails.refl _)))

private theorem memRegion_40_unack_split_epoch_placed_budget (statePtr : BitVec 64) :
    memRegion (statePtr + 0x100#64) 40 =
      (∃∗ w100 : BitVec 64, (statePtr + 0x100#64) ↦₆₄ w100) ∗
      (∃∗ w108 : BitVec 64, (statePtr + 0x108#64) ↦₆₄ w108) ∗
      (∃∗ w110 : BitVec 32, (statePtr + 0x110#64) ↦₃₂ w110) ∗
      (∃∗ w114 : BitVec 32, (statePtr + 0x114#64) ↦₃₂ w114) ∗
      (∃∗ w118 : BitVec 64, (statePtr + 0x118#64) ↦₆₄ w118) ∗
      (∃∗ w120 : BitVec 32, (statePtr + 0x120#64) ↦₃₂ w120) ∗
      memRegion (statePtr + 0x124#64) 4 := by
  rw [ProofLib.memRegion_split (statePtr + 0x100#64) 8 32 (by decide),
    ProofLib.memRegion_split (statePtr + 0x100#64 + 8#64) 8 24 (by decide),
    ProofLib.memRegion_split (statePtr + 0x100#64 + 8#64 + 8#64) 4 20 (by decide),
    ProofLib.memRegion_split (statePtr + 0x100#64 + 8#64 + 8#64 + 4#64) 4 16 (by decide),
    ProofLib.memRegion_split (statePtr + 0x100#64 + 8#64 + 8#64 + 4#64 + 4#64) 8 8 (by decide),
    ProofLib.memRegion_split (statePtr + 0x100#64 + 8#64 + 8#64 + 4#64 + 4#64 + 8#64) 4 4
      (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_four, ProofLib.memRegion_four,
    ProofLib.memRegion_eight, ProofLib.memRegion_four]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd]

private theorem stackAt_setUnack_call_epoch_placed_budget (sp : BitVec 64) :
    stackAt (sp - 144#64) (allocHookStack + 32) =
      stackAt (sp - 176#64) allocHookStack ∗ cells (sp - 176#64) 4 := by
  have h1 := ProofLib.stackAt_split_cells (sp - 144#64) allocHookStack 4 (by decide)
  have h2 : sp - 144#64 - BitVec.ofNat 64 (8 * 4) = sp - 176#64 := by bv_arith
  rw [h2] at h1
  exact h1

private theorem stackAt_setUnack_hooks_epoch_placed_budget (sp : BitVec 64) :
    stackAt (sp - 176#64) allocHookStack ∗ cells (sp - 176#64) 4 =
      memRegion (sp - 4272#64) 32 ∗ stackAt (sp - 144#64) allocHookStack := by
  rw [← stackAt_setUnack_call_epoch_placed_budget sp]
  have h1 := stackAt_split_top (sp - 144#64) 32 allocHookStack (by decide)
  have h2 : (32 + allocHookStack : Nat) = allocHookStack + 32 := by decide
  have h3 : BitVec.ofNat 64 (32 + allocHookStack) = 4128#64 := rfl
  have h4 : sp - 144#64 - 4128#64 = sp - 4272#64 := by bv_arith
  rw [h3, h4] at h1
  rw [← h2, h1]

set_option maxHeartbeats 4000000 in
/-- Block `33` satisfies `withLsCodeLoaded lsmpl (setUnackPreKeyMsgEpochInnerSpec A lim)` under `[LibsignalPlacement]`. -/
theorem setUnackPreKeyMsg_exact_stack_epoch_placed_cl_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hTime : HookSat H lsDurationSinceSym durationSinceEpochAllocBudgetSpec) :
    subroutine_ok ((blkPC_33).rebase (blkPl_33).base H) (blkPl_33).base
      (withLsCodeLoaded lsmpl (setUnackPreKeyMsgEpochInnerSpec A lim)) := by
  unfold withLsCodeLoaded setUnackPreKeyMsgEpochInnerSpec
    setUnackPreKeyMsgEpochEvents setUnackPreKeyMsgEvents
  have hser : subroutine_ok ((blkPC_33).rebase (blkPl_33).base H) (lsmpl.base 205)
      (withLsCl lsmpl (ecPubKeySerializeRawPlacedSpec M A lim)) :=
    ls_subroutine_ok_cl_of_plain (callerProg := (blkPC_33).rebase (blkPl_33).base H)
      (ecPubKeySerializeRaw_placed_ok_of_session hshim halloc)
  dsimp only [withLsCl, ecPubKeySerializeRawPlacedSpec, ecPubKeySerializeAllocEvents] at hser
  have hshim' : subroutine_ok ((blkPC_33).rebase (blkPl_33).base H)
      (lsρ lsRustNoAllocShimSym) sessionShimBudgetSpec := ls_hook_ok_of_mem hshim
  have halloc0 : subroutine_ok ((blkPC_33).rebase (blkPl_33).base H)
      (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false) := ls_hook_ok_of_mem halloc
  have halloc' : subroutine_ok ((blkPC_33).rebase (blkPl_33).base H)
      (lsρ lsRustAllocSym) (rustCliAllocNoOomExternSpecWithStack M A lim false allocHookStack) :=
    subroutine_ok_rustCliAllocNoOom_externWithStack (stk := allocHookStack)
      (by decide) (by decide) (subroutine_ok_allocNoOom_of_budget halloc0)
  have hdealloc' := dealloc_bytes_placed_ok (prog := (blkPC_33).rebase (blkPl_33).base H) hdealloc
  have hmemcpy' : subroutine_ok ((blkPC_33).rebase (blkPl_33).base H)
      (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec := ls_hook_ok_of_mem hmemcpy
  have htime' : subroutine_ok ((blkPC_33).rebase (blkPl_33).base H)
      (lsρ lsDurationSinceSym) durationSinceEpochAllocBudgetSpec :=
    ls_hook_ok_of_mem hTime
  dsimp only [sessionShimBudgetSpec, CryptoVerification.LibsignalTripleRatchet.sessionShimSpec] at hshim'
  dsimp only [rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomSpecWithStack,
    LibsignalBinary.Heap.RustLayoutOk, CryptoVerification.RustHeap.LayoutOk, ↓reduceIte] at halloc'
  dsimp only [rustDeallocBytesSpec] at hdealloc'
  dsimp only [sessionMemcpyRegionBudgetSpec,
    CryptoVerification.LibsignalTripleRatchet.sessionMemcpyRegionSpec, memcpyRegionSpec] at hmemcpy'
  dsimp only [durationSinceEpochAllocBudgetSpec, withVmPreserved,
    durationSinceEpochAllocSpec, durationSinceEpochAtSpec] at htime'
  wp_init x s0
  rcases x with ⟨⟨statePtr, optOpkTag, optOpkVal, spkId, baseKeyPtr, baseKeyBytes⟩, st⟩
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hx5 : s0.readReg64 (.gpr 5#5) = 0#64 := ‹_›
  have hx6 : (s0.readReg64 (.gpr 6#5)).setWidth 32 = 0#32 := ‹_›
  have hx6_ext : (s0.readReg64 (.gpr 6#5)).extractLsb' 0 32 = 0#32 := by
    ext i hi
    have := congrArg (fun v => v[i]) hx6
    simpa using this
  have hlen_base : baseKeyBytes.length = 32 := ‹_›
  subst statePtr optOpkTag optOpkVal spkId baseKeyPtr
  have hfe_all : FitsEvents M lim st [.alloc 33, .alloc 33, .free 1 33] := by
    simpa [rustAllocEvents, rustDeallocEvents] using
      ‹FitsEvents M lim st (rustAllocEvents 33 1 ++ rustAllocEvents 33 1 ++ rustDeallocEvents 33 1)›
  rcases hfe_all with ⟨hfe1, hfe2, -, -⟩
  let st1 := M.stepEvents (rustAllocEvents 33 1) st
  let st2 := M.stepEvents (rustAllocEvents 33 1) st1
  have henc33 : (encodeEC baseKeyBytes).length = 33 := by
    change (0x05 :: baseKeyBytes).length = 33; simp [hlen_base]
  have hlen_enc : (bytesToBv8 (encodeEC baseKeyBytes)).length = 33 := by
    simp [bytesToBv8, henc33]
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hpos33 : 0 < (33 : Nat) := by decide
  have hal1 : (1 : Nat) ≤ 2 ^ 31 := by decide
  have hsum33 : (33 : Nat) + 1 ≤ 2 ^ 63 := by decide
  rw [memRegion_40_unack_split_epoch_placed_budget (s0.readReg64 (.gpr 0#5))]
  cells_pre_unfold_fast
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun c0 => SepWP.exists_elim fun c1 => SepWP.exists_elim fun c2 => ?_
  repeat (refine SepWP.exists_elim fun _ => ?_)
  rw (occs := .pos [1]) [stackAt_setUnack_call_epoch_placed_budget s0.sp]
  rw [pointsTo64_split32' (s0.sp - 128#64)]
  simp only [bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  apply sepWP_seq_lscl hcl0 (mid := lsmpl.base 205)
  wp_steps_sync_pool (lsmpl.base 205)
  simp only [State.setMem_setMem]
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl1
  wp_call hser ((s0.readReg64 (.gpr 4#5), baseKeyBytes), st)
  apply SepWP.replace_pre (by sep_focus) (Entails.of_eq (stackAt_setUnack_hooks_epoch_placed_budget s0.sp))
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  simp only [State.setMem_setMem]
  wp_call hshim' ()
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_1› (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call halloc' (33, 1, st1)
  have hne : sf_2.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq : (sf_2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne
  wp_steps_sync_pool (lsρ lsMemcpySym)
  simp only [State.setMem_setMem]
  rw [← hlen_enc]
  wp_call hmemcpy' (sf_2.readReg64 (Reg.gpr 0#5), _, bytesToBv8 (encodeEC baseKeyBytes))
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_3› (hnext := ?_)
  simp only [hlen_enc]
  wp_steps_sync_pool (lsρ lsDurationSinceSym)
  simp only [State.setMem_setMem]
  have h136_eq : s0.sp - 136#64 + 8#64 = s0.sp - 128#64 := by bv_arith
  have h136_12 : s0.sp - 136#64 + 12#64 = s0.sp - 124#64 := by bv_arith
  have h120_8 : s0.sp - 120#64 + 8#64 = s0.sp - 112#64 := by bv_arith
  have h120_16 : s0.sp - 120#64 + 16#64 = s0.sp - 104#64 := by bv_arith
  have h124_ent : ∀ v, ((s0.sp - 124#64) ↦₃₂ v) ⊢ memRegion (s0.sp - 136#64 + 12#64) 4 := by
    intro v; rw [h136_12]; exact pointsTo32_entails_memRegion (s0.sp - 124#64) v
  rw [← h136_eq]
  apply SepWP.replace_pre (by sep_focus) (h124_ent _)
  apply SepWP.replace_pre (by sep_focus)
    (h120_8 ▸ h120_16 ▸ pointsTo64_triple_entails_memRegion24_epoch_placed_budget (s0.sp - 120#64) _ _ _)
  have hsp3 : sf_3.sp = s0.sp - 144#64 := by simp only [*, arm64_norm]
  wp_call htime' (s0.sp - 136#64, s0.sp - 120#64)
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_4› (hnext := ?_)
  rw [memRegion_16_split_64_epoch_placed_budget (s0.sp - 136#64), h136_eq]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  wp_pull_exists
  wp_steps_sync_pool (lsρ lsRustDeallocSym)
  rw [show sf_3.sp = sf_4.sp by simp only [*, arm64_norm]]
  simp only [State.setMem_setMem]
  wp_call hdealloc' ((_, bytesToBv8 (encodeEC baseKeyBytes), 33, 1), st2)
  wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
  simp only [State.setMem_setMem]
  simp only [*] at *
  apply SepWP.replace_pre (by sep_focus)
    (Entails.of_eq ((stackAt_setUnack_call_epoch_placed_budget s0.sp).trans
      (stackAt_setUnack_hooks_epoch_placed_budget s0.sp)).symm)
  dsimp only [st2, st1]
  simp only [vecU8, A.repAlloc_live, AllocCostModel.stepEvents_append]
  cells_unfold
  wp_done

theorem setUnackPreKeyMsg_exact_stack_epoch_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hTime : HookSat H lsDurationSinceSym durationSinceEpochAllocBudgetSpec) :
    subroutine_ok ((blkPC_33).rebase (blkPl_33).base H) (blkPl_33).base
      (setUnackPreKeyMsgExactStackEpochSpecPlaced A lim) :=
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (setUnackPreKeyMsg_exact_stack_epoch_placed_cl_ok hshim halloc hdealloc hmemcpy hTime)

/-- Transfers `setUnackPreKeyMsg_exact_stack_epoch_placed_ok` to any caller block `i < 619`. -/
theorem setUnackPreKeyMsg_exact_stack_epoch_placed_at_block [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H]
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hTime : HookSat H lsDurationSinceSym durationSinceEpochAllocBudgetSpec)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (blkPl_33).base
      (setUnackPreKeyMsgExactStackEpochSpecPlaced A lim) := by
  have hrocl := @ls_subroutine_ok_rocl_of_block _ _ callerProg
    ((blkPC_33).rebase (blkPl_33).base H) i 33 H
    hcaller (instIsLsBlockProg_33 H) (blkPl_33).base _
    (setUnackPreKeyMsg_exact_stack_epoch_placed_ok hshim halloc hdealloc hmemcpy hTime)
    _ _ _ _ hi (by decide) (by decide)
  refine subroutine_ok_mono hrocl (fun _ _ _ h => h) ?_
  intro x R s0 sf hpost
  dsimp only [withLsRoCl] at hpost
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
  exact hpost.2

theorem setUnackPreKeyMsg_exact_stack_epoch_placed_ok_cli [LibsignalPlacement]
    {callerProg : Program} {i : Nat} (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    [IsLsBlockProg callerProg i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hG : CliGhostAllocHooks M A lim g)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (blkPl_33).base
      (setUnackPreKeyMsgExactStackEpochSpecPlaced A lim) :=
  setUnackPreKeyMsg_exact_stack_epoch_placed_at_block
    (cliExternsPlaced_shim_budget_sat mmpl g W hG.shim_eq)
    (cliExternsPlaced_alloc_budget_sat mmpl g W hG)
    (cliExternsPlaced_dealloc_budget_sat mmpl g W hG)
    (cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl g W hG)
    (cliGhostExterns_sat_of_cliExternsPlaced mmpl g W
      (cliExternsPlaced_durationSinceEpochAlloc_budget_sat mmpl W))
    hi

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.SetUnackEpochPlacedBudget

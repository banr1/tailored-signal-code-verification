/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2cPlacedBudgetAux
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch2Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2c
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Budget-Threaded Variant 1 (`KeysSampled`) — Part C

Relocatable Block-`333` error-path deallocation at `+5916`, `+5860`, and `+4116` under
`RustCliAllocBudget M` and `FreeOnlyEvs`, re-exporting `+8756 -> +4016` from `Variant2cPlacedBudgetAux`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2cPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalPlacement blkLib_eq_333 blkPC_333 blkPl_333 lsProg_333 lsmpl lsρ)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.Drop (chunkedStatesSize vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved resultChunkedStatesAt sp_sub_2400_align spqrErrorByte
   stackAt_encoderFromPb_split_allocHook statesFromPbSavedCells statesFromPbStack
   v1c_bv_add_add_lit v1c_bv_sub_sub_lit)
open CryptoVerification.SpqrV1.Unchunked
  (extractLsb'_0_64_append extractLsb'_64_64_append)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget
   rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
  (FromPbAllocHooksPlacedBudget spqrRustDeallocSym)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
  (align_pre_st deallocFreeOnlySpec sepWP_evs_dealloc sepWP_evs_nil seq_clean_evs
   subroutine_ok_deallocFreeOnly)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux
  (FromPbAllocHooksBudget blk333_noSvc0 entails_pre_st
   v1_dealloc_ok_at_statesFromPb_placed v1_dealloc_ok_of_placedHooks)

export Variant2cPlacedBudgetAux
  (v1_auth_from_pb_step2_8756_9804_of_placedHooks
   v1_auth_from_pb_step2_8756_9804_placed
   v1_auth_from_pb_step2_8756_9804_placed_wpp
   v1_auth_from_pb_step2_8756_9804_placed_lscl_wpp)
export Variant2cPlacedBudgetAux
  (v1_auth_from_pb_step3_9804_4016_of_sub_placed
   v1_auth_from_pb_step3_9804_4016_of_placedHooks
   v1_auth_from_pb_step3_9804_4016_placed)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm, local wp_norm]
  v1c_bv_add_add_lit v1c_bv_sub_sub_lit

local macro "wp_steps_sync_333 " mid:term : tactic => `(tactic| (
  apply sepWP_seg_ls_vm
    (Q := (blkPC_333).rebase (blkPl_333).base (hooksException _))
    blkLib_eq_333 blk333_noSvc0 (mid := $mid)
  intro _m_strip
  wp_steps
  refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  refine ProofLib.SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))
    (hnext := ?_)
))

/-! ## Local Stack-Region Coalescing Helpers -/

private theorem merge_stack_216_8_2080 (fsp u40 : BitVec 64) :
    memRegion fsp 216 ∗ ((fsp + 216#64) ↦₆₄ u40) ∗ memRegion (fsp + 224#64) 2080 ⊢
      memRegion fsp 2304 := by
  rw [ProofLib.memRegion_split' (b := fsp) (n := 216) (k := 2088)
        (b' := fsp + 216#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := fsp + 216#64) (n := 8) (k := 2080)
        (b' := fsp + 224#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_right (sepConj_mono_left (pointsTo64_entails_memRegion _ _))

private theorem merge_stack_224_2080 (fsp u32 u96 : BitVec 64) :
    ((fsp + 224#64) ↦₆₄ u32) ∗ ((fsp + 232#64) ↦₆₄ u96) ∗ memRegion (fsp + 240#64) 2064 ⊢
      memRegion (fsp + 224#64) 2080 := by
  rw [ProofLib.memRegion_split' (b := fsp + 224#64) (n := 8) (k := 2072)
        (b' := fsp + 232#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 232#64) (n := 8) (k := 2064)
        (b' := fsp + 240#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono_left (pointsTo64_entails_memRegion _ _))

private theorem merge_stack_176_216_none (fsp u16 pa2 : BitVec 64) :
    memRegion fsp 176 ∗ ((fsp + 176#64) ↦₆₄ u16) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
      memRegion (fsp + 192#64) 24 ⊢
      memRegion fsp 216 := by
  rw [ProofLib.memRegion_split' (b := fsp) (n := 176) (k := 40)
        (b' := fsp + 176#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := fsp + 176#64) (n := 8) (k := 32)
        (b' := fsp + 184#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 184#64) (n := 8) (k := 24)
        (b' := fsp + 192#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono_left (pointsTo64_entails_memRegion _ _)))

private theorem merge_stack_176_216_err (fsp u16 pa2 pa1 : BitVec 64) :
    memRegion fsp 176 ∗ ((fsp + 176#64) ↦₆₄ u16) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
      memRegion (fsp + 192#64) 8 ∗ ((fsp + 200#64) ↦₆₄ pa1) ∗ memRegion (fsp + 208#64) 8 ⊢
      memRegion fsp 216 := by
  rw [ProofLib.memRegion_split' (b := fsp) (n := 176) (k := 40)
        (b' := fsp + 176#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := fsp + 176#64) (n := 8) (k := 32)
        (b' := fsp + 184#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 184#64) (n := 8) (k := 24)
        (b' := fsp + 192#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 192#64) (n := 8) (k := 16)
        (b' := fsp + 200#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 200#64) (n := 8) (k := 8)
        (b' := fsp + 208#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono_right (sepConj_mono_left (pointsTo64_entails_memRegion _ _)))))

/-! ## Cleanup Helpers for `sendingHdr = none` (`+5860`) and `from_pb` Error (`+4116`) -/

/-- Shared tail at `+5916`: deallocates `dk` (`x28 = u32`, `[fsp + 216] = u40`) under explicit
    Block-`333` `__rust_dealloc` contract and exits via `v1_err_5940_placed_budget` with
    `Err(StateDecode)` (`FreeOnlyEvs`). -/
theorem v1_cleanup_dk_5916_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (out u32 u40 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 5916#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx28_1 : s1.readReg64 .x28 = u32)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 216 ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
        memRegion (s0.sp - 2400#64 + 224#64) 2080 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecCapPtrDealloc A.repAlloc u32 u40 ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            Rest ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧
          CalleeSavedPreserved s0 sf ∧
          sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  have hdealloc_fo : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (deallocFreeOnlySpec M A lim) :=
    subroutine_ok_deallocFreeOnly hdealloc_ok
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  have hm2304 := merge_stack_216_8_2080 (s0.sp - 2400#64) u40
  rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
  refine seq_clean_evs
    (mid := lsmpl.base 333 + 5940#64)
    (P_evs := fun evs1 s2 =>
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      A.pool lim (M.stepEvents evs1 st) s2 ∗
      Rest)
    (Q := fun s2 =>
      s2.sp = s0.sp - 2400#64 ∧
      s2.readReg64 .x19 = out ∧
      (s2.readReg64 .x26).extractLsb' 0 8 = spqrErrorByte .stateDecode ∧
      TraceCalleeSaved s2 s0)
    ?_ ?_
  · dsimp only [vecCapPtrDealloc, spqrErrorByte, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
      BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc1 ⊢
    change s1.pc = (blkPl_333).base + 5916#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 5940#64) s1 _ _
    by_cases hc_dk : (u32 == 0#64) = true <;>
      simp only [hc_dk, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · apply sepWP_evs_nil
      simp only [M.stepEvents_nil]
      wp_steps_sync_333 ((blkPl_333).base + 5940#64)
      simp only [State.setMem_setMem]
      refine entails_pre_st ?_ ?_
      · intro sc hsc
        rw [← hsc, stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
        simp only [arm64_norm] at hm2304 ⊢
        refine Entails.trans (Entails.of_eq (show _ =
          (memRegion (s0.sp - 2400#64) 216 ∗
           ((s0.sp - 2184#64) ↦₆₄ u40) ∗
           memRegion (s0.sp - 2176#64) 2080) ∗
          (memRegion (s0.sp - 7552#64) 1056 ∗
           stackAt (s0.sp - 2400#64) allocHookStack ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
           A.pool lim st sc ∗ Rest) by sep_ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hm2304) (Entails.of_eq (by sep_ac_rfl))
      · wp_done
    · apply sepWP_evs_dealloc u32.toNat 1
      wp_steps_sync_333 (lsρ spqrRustDeallocSym)
      simp only [State.setMem_setMem]
      wp_call hdealloc_fo (u40, u32.toNat, 1, st)
      have hacp1 : AllocCallPreserved s1 sf := by
        simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
      have htr_sf : sf.trace = s0.trace := hacp1.2.1.trans htr1.1
      have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
        ‹calleeSavedVRegs sf = calleeSavedVRegs s1›.trans htr1.2
      wp_steps_sync_333 ((blkPl_333).base + 5940#64)
      simp only [State.setMem_setMem]
      refine entails_pre_st ?_ ?_
      · intro sc hsc
        rw [← hsc, stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64), hsp1]
        simp only [arm64_norm] at hm2304 ⊢
        refine Entails.trans (Entails.of_eq (show _ =
          (memRegion (s0.sp - 2400#64) 216 ∗
           ((s0.sp - 2184#64) ↦₆₄ u40) ∗
           memRegion (s0.sp - 2176#64) 2080) ∗
          (memRegion (s0.sp - 7552#64) 1056 ∗
           stackAt (s0.sp - 2400#64) allocHookStack ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
           A.pool lim (M.stepEvents (rustDeallocEvents u32.toNat 1) st) sc ∗
           Rest) by sep_ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hm2304) (Entails.of_eq (by sep_ac_rfl))
      · wp_done
  · intro evs1 s2 hevs1 hpc2 hrun2 ⟨hsp2, hx19_2, hx26_2, htr2⟩
    have herr := Variant2aPlacedBudgetAux.v1_err_5940_placed_budget A lim (M.stepEvents evs1 st)
      (F := F) (ext := ext) s0 s2 out Rest hsp0_align hpc2 hrun2 hsp2 hx19_2 hx26_2 htr2
    refine SepWP.mono herr fun sf Pf _ _ ⟨hPf, _hvm, hsp_f, hcc_f, htr_f⟩ =>
      ⟨evs1, hevs1, hPf, hsp_f, hcc_f, htr_f⟩

theorem v1_cleanup_dk_5916_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out u32 u40 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 5916#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx28_1 : s1.readReg64 .x28 = u32)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 216 ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
        memRegion (s0.sp - 2400#64 + 224#64) 2080 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecCapPtrDealloc A.repAlloc u32 u40 ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            Rest ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧
          CalleeSavedPreserved s0 sf ∧
          sf.trace = s0.trace) :=
  v1_cleanup_dk_5916_of_sub_placed (F := F) (v1_dealloc_ok_of_placedHooks hA) st s0 s1 out u32 u40
    Rest hsp0_align hpc1 hrun1 hsp1 hx19_1 hx28_1 htr1

theorem v1_cleanup_dk_5916_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out u32 u40 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 5916#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx28_1 : s1.readReg64 .x28 = u32)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 216 ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
        memRegion (s0.sp - 2400#64 + 224#64) 2080 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecCapPtrDealloc A.repAlloc u32 u40 ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            Rest ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧
          CalleeSavedPreserved s0 sf ∧
          sf.trace = s0.trace) :=
  v1_cleanup_dk_5916_of_sub_placed (F := F) (v1_dealloc_ok_at_statesFromPb_placed hA) st s0 s1 out
    u32 u40 Rest hsp0_align hpc1 hrun1 hsp1 hx19_1 hx28_1 htr1

/-- Cleanup at `+5860` when `s.sendingHdr = none`: deallocates cloned `auth.rootKey`, cloned
    `auth.macKey`, `ek`, and `dk` under explicit Block-`333` `__rust_dealloc` contract,
    returning `Err(StateDecode)` (`FreeOnlyEvs`). -/
theorem v1_cleanup_sendingHdr_none_5860_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (out pa1 pa2 u8 u16 u32 u40 u72 u96 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 5860#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx0_1 : s1.readReg64 .x0 = pa1)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = u8)
    (hx22_1 : s1.readReg64 .x22 = u72)
    (hx28_1 : s1.readReg64 .x28 = u32)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 176 ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
        ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
        memRegion (s0.sp - 2400#64 + 192#64) 24 ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
        ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 2064 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecCapPtrDealloc A.repAlloc u72 pa1 ∗
        vecCapPtrDealloc A.repAlloc u96 pa2 ∗
        vecCapPtrDealloc A.repAlloc u8 u16 ∗
        vecCapPtrDealloc A.repAlloc u32 u40 ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            Rest ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧
          CalleeSavedPreserved s0 sf ∧
          sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  have hdealloc_fo : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (deallocFreeOnlySpec M A lim) :=
    subroutine_ok_deallocFreeOnly hdealloc_ok
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  have hm216 := merge_stack_176_216_none (s0.sp - 2400#64) u16 pa2
  have hm2080 := merge_stack_224_2080 (s0.sp - 2400#64) u32 u96
  rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
  refine seq_clean_evs
    (mid := lsmpl.base 333 + 5876#64)
    (P_evs := fun evs1 s2 =>
      memRegion (s0.sp - 2400#64 - 5152#64) 1056 ∗
      stackAt (s0.sp - 2400#64) allocHookStack ∗
      memRegion (s0.sp - 2400#64) 176 ∗
      ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
      ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
      memRegion (s0.sp - 2400#64 + 192#64) 24 ∗
      ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
      ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
      ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗
      memRegion (s0.sp - 2400#64 + 240#64) 2064 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      vecCapPtrDealloc A.repAlloc u96 pa2 ∗
      vecCapPtrDealloc A.repAlloc u8 u16 ∗
      vecCapPtrDealloc A.repAlloc u32 u40 ∗
      A.pool lim (M.stepEvents evs1 st) s2 ∗
      Rest)
    (Q := fun s2 =>
      s2.sp = s0.sp - 2400#64 ∧
      s2.readReg64 .x19 = out ∧
      s2.readReg64 .x21 = u8 ∧
      s2.readReg64 .x28 = u32 ∧
      TraceCalleeSaved s2 s0)
    ?_ ?_
  · dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
      BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc1 ⊢
    change s1.pc = (blkPl_333).base + 5860#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 5876#64) s1 _ _
    by_cases hc1 : (u72 == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · apply sepWP_evs_nil
      simp only [M.stepEvents_nil]
      wp_steps_sync_333 ((blkPl_333).base + 5876#64)
      simp only [State.setMem_setMem]
      refine align_pre_st (by simp only [arm64_norm]; sep_ac_rfl) ?_
      wp_done
    · apply sepWP_evs_dealloc u72.toNat 1
      wp_steps_sync_333 (lsρ spqrRustDeallocSym)
      simp only [State.setMem_setMem]
      wp_call hdealloc_fo (pa1, u72.toNat, 1, st)
      have hacp1 : AllocCallPreserved s1 sf := by
        simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
      have hsp_sf : sf.sp = s0.sp - 2400#64 := ‹sf.sp = s1.sp›.trans hsp1
      have htr_sf : sf.trace = s0.trace := hacp1.2.1.trans htr1.1
      have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
        ‹calleeSavedVRegs sf = calleeSavedVRegs s1›.trans htr1.2
      refine align_pre_st (by rw [hsp1]; simp only [arm64_norm]; sep_ac_rfl) ?_
      wp_done
  · intro evs1 s2 hevs1 hpc2 hrun2 ⟨hsp2, hx19_2, hx21_2, hx28_2, htr2⟩
    let st1 := M.stepEvents evs1 st
    refine seq_clean_evs
      (mid := lsmpl.base 333 + 5896#64)
      (P_evs := fun evs2 s3 =>
        memRegion (s0.sp - 2400#64 - 5152#64) 1056 ∗
        stackAt (s0.sp - 2400#64) allocHookStack ∗
        memRegion (s0.sp - 2400#64) 176 ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
        ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
        memRegion (s0.sp - 2400#64 + 192#64) 24 ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
        ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 2064 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecCapPtrDealloc A.repAlloc u8 u16 ∗
        vecCapPtrDealloc A.repAlloc u32 u40 ∗
        A.pool lim (M.stepEvents evs2 st1) s3 ∗
        Rest)
      (Q := fun s3 =>
        s3.sp = s0.sp - 2400#64 ∧
        s3.readReg64 .x19 = out ∧
        s3.readReg64 .x21 = u8 ∧
        s3.readReg64 .x28 = u32 ∧
        TraceCalleeSaved s3 s0)
      ?_ ?_
    · dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
        BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc2 ⊢
      change s2.pc = (blkPl_333).base + 5876#64 at hpc2
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 5896#64) s2 _ _
      by_cases hc2 : (u96 == 0#64) = true <;>
        simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · apply sepWP_evs_nil
        simp only [M.stepEvents_nil]
        wp_steps_sync_333 ((blkPl_333).base + 5896#64)
        simp only [State.setMem_setMem]
        refine align_pre_st (by simp only [arm64_norm]; sep_ac_rfl) ?_
        wp_done
      · apply sepWP_evs_dealloc u96.toNat 1
        wp_steps_sync_333 (lsρ spqrRustDeallocSym)
        simp only [State.setMem_setMem]
        wp_call hdealloc_fo (pa2, u96.toNat, 1, st1)
        have hacp2 : AllocCallPreserved s2 sf := by
          simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
        have hsp_sf : sf.sp = s0.sp - 2400#64 := ‹sf.sp = s2.sp›.trans hsp2
        have htr_sf : sf.trace = s0.trace := hacp2.2.1.trans htr2.1
        have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
          ‹calleeSavedVRegs sf = calleeSavedVRegs s2›.trans htr2.2
        refine align_pre_st (by rw [hsp2]; simp only [arm64_norm]; sep_ac_rfl) ?_
        wp_done
    · intro evs2 s3 hevs2 hpc3 hrun3 ⟨hsp3, hx19_3, hx21_3, hx28_3, htr3⟩
      let st2 := M.stepEvents evs2 st1
      refine seq_clean_evs
        (mid := lsmpl.base 333 + 5916#64)
        (P_evs := fun evs3 s4 =>
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (s0.sp - 2400#64) 216 ∗
          ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
          memRegion (s0.sp - 2400#64 + 224#64) 2080 ∗
          statesFromPbSavedCells s0 ∗
          memRegion out chunkedStatesSize ∗
          vecCapPtrDealloc A.repAlloc u32 u40 ∗
          A.pool lim (M.stepEvents evs3 st2) s4 ∗
          Rest)
        (Q := fun s4 =>
          s4.sp = s0.sp - 2400#64 ∧
          s4.readReg64 .x19 = out ∧
          s4.readReg64 .x28 = u32 ∧
          TraceCalleeSaved s4 s0)
        ?_ ?_
      · dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
          BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc3 ⊢
        change s3.pc = (blkPl_333).base + 5896#64 at hpc3
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 5916#64) s3 _ _
        by_cases hc3 : (u8 == 0#64) = true <;>
          simp only [hc3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · apply sepWP_evs_nil
          simp only [M.stepEvents_nil]
          wp_steps_sync_333 ((blkPl_333).base + 5916#64)
          simp only [State.setMem_setMem]
          refine entails_pre_st ?_ ?_
          · intro sc hsc
            rw [← hsc, stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
            simp only [arm64_norm] at hm216 hm2080 ⊢
            refine Entails.trans (Entails.of_eq (show _ =
              (memRegion (s0.sp - 2400#64) 176 ∗
               ((s0.sp - 2224#64) ↦₆₄ u16) ∗
               ((s0.sp - 2216#64) ↦₆₄ pa2) ∗
               memRegion (s0.sp - 2208#64) 24) ∗
              (((s0.sp - 2176#64) ↦₆₄ u32) ∗
               ((s0.sp - 2168#64) ↦₆₄ u96) ∗
               memRegion (s0.sp - 2160#64) 2064) ∗
              (memRegion (s0.sp - 7552#64) 1056 ∗
               stackAt (s0.sp - 2400#64) allocHookStack ∗
               ((s0.sp - 2184#64) ↦₆₄ u40) ∗
               statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
               vecCapPtrDealloc A.repAlloc u32 u40 ∗
               A.pool lim st2 sc ∗ Rest) by
                 dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]
                 sep_ac_rfl)) ?_
            exact Entails.trans (sepConj_mono hm216 (sepConj_mono_left hm2080))
              (Entails.of_eq (by
                dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]
                sep_ac_rfl))
          · wp_done
        · apply sepWP_evs_dealloc u8.toNat 1
          wp_steps_sync_333 (lsρ spqrRustDeallocSym)
          simp only [State.setMem_setMem]
          wp_call hdealloc_fo (u16, u8.toNat, 1, st2)
          have hacp3 : AllocCallPreserved s3 sf := by
            simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
          have hsp_sf : sf.sp = s0.sp - 2400#64 := ‹sf.sp = s3.sp›.trans hsp3
          have htr_sf : sf.trace = s0.trace := hacp3.2.1.trans htr3.1
          have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
            ‹calleeSavedVRegs sf = calleeSavedVRegs s3›.trans htr3.2
          refine entails_pre_st ?_ ?_
          · intro sc hsc
            rw [← hsc, stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64), hsp3]
            simp only [arm64_norm] at hm216 hm2080 ⊢
            refine Entails.trans (Entails.of_eq (show _ =
              (memRegion (s0.sp - 2400#64) 176 ∗
               ((s0.sp - 2224#64) ↦₆₄ u16) ∗
               ((s0.sp - 2216#64) ↦₆₄ pa2) ∗
               memRegion (s0.sp - 2208#64) 24) ∗
              (((s0.sp - 2176#64) ↦₆₄ u32) ∗
               ((s0.sp - 2168#64) ↦₆₄ u96) ∗
               memRegion (s0.sp - 2160#64) 2064) ∗
              (memRegion (s0.sp - 7552#64) 1056 ∗
               stackAt (s0.sp - 2400#64) allocHookStack ∗
               ((s0.sp - 2184#64) ↦₆₄ u40) ∗
               statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
               vecCapPtrDealloc A.repAlloc u32 u40 ∗
               A.pool lim (M.stepEvents (rustDeallocEvents u8.toNat 1) st2) sc ∗
               Rest) by
                 dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]
                 sep_ac_rfl)) ?_
            exact Entails.trans (sepConj_mono hm216 (sepConj_mono_left hm2080))
              (Entails.of_eq (by
                dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]
                sep_ac_rfl))
          · wp_done
      · intro evs3 s4 hevs3 hpc4 hrun4 ⟨hsp4, hx19_4, hx28_4, htr4⟩
        let st3 := M.stepEvents evs3 st2
        have hdk := v1_cleanup_dk_5916_of_sub_placed (F := F) hdealloc_ok st3 s0 s4 out u32 u40 Rest
          hsp0_align hpc4 hrun4 hsp4 hx19_4 hx28_4 htr4
        refine SepWP.mono hdk fun sf Pf _ _ ⟨evs4, hevs4, hPf, hsp_f, hcc_f, htr_f⟩ => ?_
        refine ⟨evs1 ++ evs2 ++ evs3 ++ evs4,
          FreeOnlyEvs.append (FreeOnlyEvs.append (FreeOnlyEvs.append hevs1 hevs2) hevs3) hevs4,
          ?_, hsp_f, hcc_f, htr_f⟩
        have hst_eq : M.stepEvents evs4 st3 = M.stepEvents (evs1 ++ evs2 ++ evs3 ++ evs4) st := by
          dsimp only [st3, st2, st1]
          simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
        rwa [← hst_eq]

theorem v1_cleanup_sendingHdr_none_5860_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out pa1 pa2 u8 u16 u32 u40 u72 u96 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 5860#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx0_1 : s1.readReg64 .x0 = pa1)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = u8)
    (hx22_1 : s1.readReg64 .x22 = u72)
    (hx28_1 : s1.readReg64 .x28 = u32)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 176 ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
        ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
        memRegion (s0.sp - 2400#64 + 192#64) 24 ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
        ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 2064 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecCapPtrDealloc A.repAlloc u72 pa1 ∗
        vecCapPtrDealloc A.repAlloc u96 pa2 ∗
        vecCapPtrDealloc A.repAlloc u8 u16 ∗
        vecCapPtrDealloc A.repAlloc u32 u40 ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            Rest ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧
          CalleeSavedPreserved s0 sf ∧
          sf.trace = s0.trace) :=
  v1_cleanup_sendingHdr_none_5860_of_sub_placed (F := F) (v1_dealloc_ok_of_placedHooks hA) st s0 s1
    out pa1 pa2 u8 u16 u32 u40 u72 u96 Rest hsp0_align hpc1 hrun1 hsp1 hx0_1 hx19_1 hx21_1 hx22_1
    hx28_1 htr1

theorem v1_cleanup_sendingHdr_none_5860_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out pa1 pa2 u8 u16 u32 u40 u72 u96 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 5860#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx0_1 : s1.readReg64 .x0 = pa1)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = u8)
    (hx22_1 : s1.readReg64 .x22 = u72)
    (hx28_1 : s1.readReg64 .x28 = u32)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 176 ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
        ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
        memRegion (s0.sp - 2400#64 + 192#64) 24 ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
        ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 2064 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecCapPtrDealloc A.repAlloc u72 pa1 ∗
        vecCapPtrDealloc A.repAlloc u96 pa2 ∗
        vecCapPtrDealloc A.repAlloc u8 u16 ∗
        vecCapPtrDealloc A.repAlloc u32 u40 ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            Rest ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧
          CalleeSavedPreserved s0 sf ∧
          sf.trace = s0.trace) :=
  v1_cleanup_sendingHdr_none_5860_of_sub_placed (F := F) (v1_dealloc_ok_at_statesFromPb_placed hA)
    st s0 s1 out pa1 pa2 u8 u16 u32 u40 u72 u96 Rest hsp0_align hpc1 hrun1 hsp1 hx0_1 hx19_1 hx21_1
    hx22_1 hx28_1 htr1

/-- Cleanup at `+4116` when `<PolyEncoder>::from_pb` returns `.error`:
    deallocates cloned `auth.rootKey`, cloned `auth.macKey`, `ek`, and `dk` under explicit
    Block-`333` `__rust_dealloc` contract, returning `Err(StateDecode)` (`FreeOnlyEvs`). -/
theorem v1_cleanup_enc_err_4116_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (out pa1 pa2 u8 u16 u32 u40 u72 u96 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4116#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = u72)
    (hx26_1 : s1.readReg64 .x26 = u8)
    (hx28_1 : s1.readReg64 .x28 = u32)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 176 ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
        ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
        memRegion (s0.sp - 2400#64 + 192#64) 8 ∗
        ((s0.sp - 2400#64 + 200#64) ↦₆₄ pa1) ∗
        memRegion (s0.sp - 2400#64 + 208#64) 8 ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
        ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 2064 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecCapPtrDealloc A.repAlloc u72 pa1 ∗
        vecCapPtrDealloc A.repAlloc u96 pa2 ∗
        vecCapPtrDealloc A.repAlloc u8 u16 ∗
        vecCapPtrDealloc A.repAlloc u32 u40 ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            Rest ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧
          CalleeSavedPreserved s0 sf ∧
          sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  have hdealloc_fo : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (deallocFreeOnlySpec M A lim) :=
    subroutine_ok_deallocFreeOnly hdealloc_ok
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  have hm216 := merge_stack_176_216_err (s0.sp - 2400#64) u16 pa2 pa1
  have hm2080 := merge_stack_224_2080 (s0.sp - 2400#64) u32 u96
  rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
  refine seq_clean_evs
    (mid := lsmpl.base 333 + 4136#64)
    (P_evs := fun evs1 s2 =>
      memRegion (s0.sp - 2400#64 - 5152#64) 1056 ∗
      stackAt (s0.sp - 2400#64) allocHookStack ∗
      memRegion (s0.sp - 2400#64) 176 ∗
      ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
      ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
      memRegion (s0.sp - 2400#64 + 192#64) 8 ∗
      ((s0.sp - 2400#64 + 200#64) ↦₆₄ pa1) ∗
      memRegion (s0.sp - 2400#64 + 208#64) 8 ∗
      ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
      ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
      ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗
      memRegion (s0.sp - 2400#64 + 240#64) 2064 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      vecCapPtrDealloc A.repAlloc u96 pa2 ∗
      vecCapPtrDealloc A.repAlloc u8 u16 ∗
      vecCapPtrDealloc A.repAlloc u32 u40 ∗
      A.pool lim (M.stepEvents evs1 st) s2 ∗
      Rest)
    (Q := fun s2 =>
      s2.sp = s0.sp - 2400#64 ∧
      s2.readReg64 .x19 = out ∧
      s2.readReg64 .x26 = u8 ∧
      s2.readReg64 .x28 = u32 ∧
      TraceCalleeSaved s2 s0)
    ?_ ?_
  · dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
      BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc1 ⊢
    change s1.pc = (blkPl_333).base + 4116#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 4136#64) s1 _ _
    by_cases hc1 : (u72 == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · apply sepWP_evs_nil
      simp only [M.stepEvents_nil]
      wp_steps_sync_333 ((blkPl_333).base + 4136#64)
      simp only [State.setMem_setMem]
      refine align_pre_st (by simp only [arm64_norm]; sep_ac_rfl) ?_
      wp_done
    · apply sepWP_evs_dealloc u72.toNat 1
      wp_steps_sync_333 (lsρ spqrRustDeallocSym)
      simp only [State.setMem_setMem]
      wp_call hdealloc_fo (pa1, u72.toNat, 1, st)
      have hacp1 : AllocCallPreserved s1 sf := by
        simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
      have hsp_sf : sf.sp = s0.sp - 2400#64 := ‹sf.sp = s1.sp›.trans hsp1
      have htr_sf : sf.trace = s0.trace := hacp1.2.1.trans htr1.1
      have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
        ‹calleeSavedVRegs sf = calleeSavedVRegs s1›.trans htr1.2
      refine align_pre_st (by rw [hsp1]; simp only [arm64_norm]; sep_ac_rfl) ?_
      wp_done
  · intro evs1 s2 hevs1 hpc2 hrun2 ⟨hsp2, hx19_2, hx26_2, hx28_2, htr2⟩
    let st1 := M.stepEvents evs1 st
    refine seq_clean_evs
      (mid := lsmpl.base 333 + 4156#64)
      (P_evs := fun evs2 s3 =>
        memRegion (s0.sp - 2400#64 - 5152#64) 1056 ∗
        stackAt (s0.sp - 2400#64) allocHookStack ∗
        memRegion (s0.sp - 2400#64) 176 ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
        ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
        memRegion (s0.sp - 2400#64 + 192#64) 8 ∗
        ((s0.sp - 2400#64 + 200#64) ↦₆₄ pa1) ∗
        memRegion (s0.sp - 2400#64 + 208#64) 8 ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
        ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 2064 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecCapPtrDealloc A.repAlloc u8 u16 ∗
        vecCapPtrDealloc A.repAlloc u32 u40 ∗
        A.pool lim (M.stepEvents evs2 st1) s3 ∗
        Rest)
      (Q := fun s3 =>
        s3.sp = s0.sp - 2400#64 ∧
        s3.readReg64 .x19 = out ∧
        s3.readReg64 .x26 = u8 ∧
        s3.readReg64 .x28 = u32 ∧
        TraceCalleeSaved s3 s0)
      ?_ ?_
    · dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
        BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc2 ⊢
      change s2.pc = (blkPl_333).base + 4136#64 at hpc2
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 4156#64) s2 _ _
      by_cases hc2 : (u96 == 0#64) = true <;>
        simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · apply sepWP_evs_nil
        simp only [M.stepEvents_nil]
        wp_steps_sync_333 ((blkPl_333).base + 4156#64)
        simp only [State.setMem_setMem]
        refine align_pre_st (by simp only [arm64_norm]; sep_ac_rfl) ?_
        wp_done
      · apply sepWP_evs_dealloc u96.toNat 1
        wp_steps_sync_333 (lsρ spqrRustDeallocSym)
        simp only [State.setMem_setMem]
        wp_call hdealloc_fo (pa2, u96.toNat, 1, st1)
        have hacp2 : AllocCallPreserved s2 sf := by
          simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
        have hsp_sf : sf.sp = s0.sp - 2400#64 := ‹sf.sp = s2.sp›.trans hsp2
        have htr_sf : sf.trace = s0.trace := hacp2.2.1.trans htr2.1
        have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
          ‹calleeSavedVRegs sf = calleeSavedVRegs s2›.trans htr2.2
        refine align_pre_st (by rw [hsp2]; simp only [arm64_norm]; sep_ac_rfl) ?_
        wp_done
    · intro evs2 s3 hevs2 hpc3 hrun3 ⟨hsp3, hx19_3, hx26_3, hx28_3, htr3⟩
      let st2 := M.stepEvents evs2 st1
      refine seq_clean_evs
        (mid := lsmpl.base 333 + 5916#64)
        (P_evs := fun evs3 s4 =>
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (s0.sp - 2400#64) 216 ∗
          ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
          memRegion (s0.sp - 2400#64 + 224#64) 2080 ∗
          statesFromPbSavedCells s0 ∗
          memRegion out chunkedStatesSize ∗
          vecCapPtrDealloc A.repAlloc u32 u40 ∗
          A.pool lim (M.stepEvents evs3 st2) s4 ∗
          Rest)
        (Q := fun s4 =>
          s4.sp = s0.sp - 2400#64 ∧
          s4.readReg64 .x19 = out ∧
          s4.readReg64 .x28 = u32 ∧
          TraceCalleeSaved s4 s0)
        ?_ ?_
      · dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
          BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc3 ⊢
        change s3.pc = (blkPl_333).base + 4156#64 at hpc3
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 5916#64) s3 _ _
        by_cases hc3 : (u8 == 0#64) = true <;>
          simp only [hc3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · apply sepWP_evs_nil
          simp only [M.stepEvents_nil]
          wp_steps_sync_333 ((blkPl_333).base + 5916#64)
          simp only [State.setMem_setMem]
          refine entails_pre_st ?_ ?_
          · intro sc hsc
            rw [← hsc, stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
            simp only [arm64_norm] at hm216 hm2080 ⊢
            refine Entails.trans (Entails.of_eq (show _ =
              (memRegion (s0.sp - 2400#64) 176 ∗
               ((s0.sp - 2224#64) ↦₆₄ u16) ∗
               ((s0.sp - 2216#64) ↦₆₄ pa2) ∗
               memRegion (s0.sp - 2208#64) 8 ∗
               ((s0.sp - 2200#64) ↦₆₄ pa1) ∗
               memRegion (s0.sp - 2192#64) 8) ∗
              (((s0.sp - 2176#64) ↦₆₄ u32) ∗
               ((s0.sp - 2168#64) ↦₆₄ u96) ∗
               memRegion (s0.sp - 2160#64) 2064) ∗
              (memRegion (s0.sp - 7552#64) 1056 ∗
               stackAt (s0.sp - 2400#64) allocHookStack ∗
               ((s0.sp - 2184#64) ↦₆₄ u40) ∗
               statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
               vecCapPtrDealloc A.repAlloc u32 u40 ∗
               A.pool lim st2 sc ∗ Rest) by
                 dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]
                 sep_ac_rfl)) ?_
            exact Entails.trans (sepConj_mono hm216 (sepConj_mono_left hm2080))
              (Entails.of_eq (by
                dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]
                sep_ac_rfl))
          · wp_done
        · apply sepWP_evs_dealloc u8.toNat 1
          wp_steps_sync_333 (lsρ spqrRustDeallocSym)
          simp only [State.setMem_setMem]
          wp_call hdealloc_fo (u16, u8.toNat, 1, st2)
          have hacp3 : AllocCallPreserved s3 sf := by
            simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
          have hsp_sf : sf.sp = s0.sp - 2400#64 := ‹sf.sp = s3.sp›.trans hsp3
          have htr_sf : sf.trace = s0.trace := hacp3.2.1.trans htr3.1
          have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
            ‹calleeSavedVRegs sf = calleeSavedVRegs s3›.trans htr3.2
          refine entails_pre_st ?_ ?_
          · intro sc hsc
            rw [← hsc, stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64), hsp3]
            simp only [arm64_norm] at hm216 hm2080 ⊢
            refine Entails.trans (Entails.of_eq (show _ =
              (memRegion (s0.sp - 2400#64) 176 ∗
               ((s0.sp - 2224#64) ↦₆₄ u16) ∗
               ((s0.sp - 2216#64) ↦₆₄ pa2) ∗
               memRegion (s0.sp - 2208#64) 8 ∗
               ((s0.sp - 2200#64) ↦₆₄ pa1) ∗
               memRegion (s0.sp - 2192#64) 8) ∗
              (((s0.sp - 2176#64) ↦₆₄ u32) ∗
               ((s0.sp - 2168#64) ↦₆₄ u96) ∗
               memRegion (s0.sp - 2160#64) 2064) ∗
              (memRegion (s0.sp - 7552#64) 1056 ∗
               stackAt (s0.sp - 2400#64) allocHookStack ∗
               ((s0.sp - 2184#64) ↦₆₄ u40) ∗
               statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
               vecCapPtrDealloc A.repAlloc u32 u40 ∗
               A.pool lim (M.stepEvents (rustDeallocEvents u8.toNat 1) st2) sc ∗
               Rest) by
                 dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]
                 sep_ac_rfl)) ?_
            exact Entails.trans (sepConj_mono hm216 (sepConj_mono_left hm2080))
              (Entails.of_eq (by
                dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]
                sep_ac_rfl))
          · wp_done
      · intro evs3 s4 hevs3 hpc4 hrun4 ⟨hsp4, hx19_4, hx28_4, htr4⟩
        let st3 := M.stepEvents evs3 st2
        have hdk := v1_cleanup_dk_5916_of_sub_placed (F := F) hdealloc_ok st3 s0 s4 out u32 u40 Rest
          hsp0_align hpc4 hrun4 hsp4 hx19_4 hx28_4 htr4
        refine SepWP.mono hdk fun sf Pf _ _ ⟨evs4, hevs4, hPf, hsp_f, hcc_f, htr_f⟩ => ?_
        refine ⟨evs1 ++ evs2 ++ evs3 ++ evs4,
          FreeOnlyEvs.append (FreeOnlyEvs.append (FreeOnlyEvs.append hevs1 hevs2) hevs3) hevs4,
          ?_, hsp_f, hcc_f, htr_f⟩
        have hst_eq : M.stepEvents evs4 st3 = M.stepEvents (evs1 ++ evs2 ++ evs3 ++ evs4) st := by
          dsimp only [st3, st2, st1]
          simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
        rwa [← hst_eq]

theorem v1_cleanup_enc_err_4116_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out pa1 pa2 u8 u16 u32 u40 u72 u96 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4116#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = u72)
    (hx26_1 : s1.readReg64 .x26 = u8)
    (hx28_1 : s1.readReg64 .x28 = u32)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 176 ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
        ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
        memRegion (s0.sp - 2400#64 + 192#64) 8 ∗
        ((s0.sp - 2400#64 + 200#64) ↦₆₄ pa1) ∗
        memRegion (s0.sp - 2400#64 + 208#64) 8 ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
        ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 2064 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecCapPtrDealloc A.repAlloc u72 pa1 ∗
        vecCapPtrDealloc A.repAlloc u96 pa2 ∗
        vecCapPtrDealloc A.repAlloc u8 u16 ∗
        vecCapPtrDealloc A.repAlloc u32 u40 ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            Rest ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧
          CalleeSavedPreserved s0 sf ∧
          sf.trace = s0.trace) :=
  v1_cleanup_enc_err_4116_of_sub_placed (F := F) (v1_dealloc_ok_of_placedHooks hA) st s0 s1 out
    pa1 pa2 u8 u16 u32 u40 u72 u96 Rest hsp0_align hpc1 hrun1 hsp1 hx19_1 hx22_1 hx26_1 hx28_1 htr1

theorem v1_cleanup_enc_err_4116_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out pa1 pa2 u8 u16 u32 u40 u72 u96 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4116#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = u72)
    (hx26_1 : s1.readReg64 .x26 = u8)
    (hx28_1 : s1.readReg64 .x28 = u32)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 176 ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
        ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
        memRegion (s0.sp - 2400#64 + 192#64) 8 ∗
        ((s0.sp - 2400#64 + 200#64) ↦₆₄ pa1) ∗
        memRegion (s0.sp - 2400#64 + 208#64) 8 ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
        ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 2064 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecCapPtrDealloc A.repAlloc u72 pa1 ∗
        vecCapPtrDealloc A.repAlloc u96 pa2 ∗
        vecCapPtrDealloc A.repAlloc u8 u16 ∗
        vecCapPtrDealloc A.repAlloc u32 u40 ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            Rest ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧
          CalleeSavedPreserved s0 sf ∧
          sf.trace = s0.trace) :=
  v1_cleanup_enc_err_4116_of_sub_placed (F := F) (v1_dealloc_ok_at_statesFromPb_placed hA) st s0 s1
    out pa1 pa2 u8 u16 u32 u40 u72 u96 Rest hsp0_align hpc1 hrun1 hsp1 hx19_1 hx22_1 hx26_1 hx28_1
    htr1

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2cPlacedBudget

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9aPlacedBudgetAux
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch2Placed
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Placed Variant 9 (`Ct1Acknowledged`, `+444`, Block `333`) — Part A

Proves the Variant 9 `uc` error-cleanup paths (`+7024`, `+6904`, `+8588`, `+488`, `+2768`) under
`VmPreserved`, `RustCliAllocBudget M`, and `FreeOnlyEvs`, re-exporting `+7084` and `+5360..+5440`
helpers from `Variant9aPlacedBudgetAux`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9aPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkLib_eq_333 blkPC_333 blkPl_333
   lsProg_333 lsmpl lsρ withLsCodeLoaded withMemEq)
open CryptoVerification.LibsignalSpqrV1 (V1State)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.Drop
  (DropProtoUnchunkedCt1SentEkReceivedGhost cap_add_one_beq_zero_false dropStack32
   protoUnchunkedCt1SentAt protoUnchunkedCt1SentEkReceivedAt protoUnchunkedCt1SentEkReceivedSize
   vecCapPtrDealloc)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved v9_Saved5368Preserved v9_Saved7084Preserved)
open CryptoVerification.SpqrV1.Unchunked
  (extractLsb'_0_64_append extractLsb'_64_64_append)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget
   VmPreserved rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.Drop.UnchunkedBudget (dropProtoUnchunkedCt1SentEkReceivedSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (isTotalTrapHooks_withPanics_vmTrapHooks sepWP_lsBlock_vmPreserved
   stripS_calleeSavedVRegs stripS_pc stripS_readReg64 stripS_sp stripS_status stripS_trace
   vmTrapHooks)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget (spqrRustDeallocSym)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
  (align_pre_st deallocFreeOnlySpec sepWP_evs_dealloc sepWP_evs_nil seq_clean_evs
   subroutine_ok_deallocFreeOnly)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
  (FromPbAllocHooksBudget seq_clean_lscl_st withMemEq_of_withLsCodeLoaded)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux (blk333_noSvc0)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget (blk333_safeVm)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9aPlacedBudgetAux
  (v9_saved5368Preserved_stripS)

export Variant9aPlacedBudgetAux
  (v9_sub_ok_dealloc_of_dealloc_placed v9_sub_ok_dealloc_placed
   v9_sub_ok_deallocFreeOnly_placed v9_sub_ok_decoder_from_pb_placed
   v9_sub_ok_decoder_from_pb_mem_placed)
export Variant9aPlacedBudgetAux
  (drop_proto_unchunked_ct1_sent_ek_received_cl_placed_ok
   v9_sub_ok_drop_proto_unchunked_ct1_sent_of_dealloc_placed
   v9_sub_ok_drop_proto_unchunked_ct1_sent_placed
   v9_sub_ok_drop_proto_unchunked_ct1_sent_mem_of_dealloc_placed
   v9_sub_ok_drop_proto_unchunked_ct1_sent_mem_placed)
export Variant9aPlacedBudgetAux
  (v9_states_from_pb_err_7084_placed v9_states_from_pb_err_7084_placed_budget
   v9_proto_decoder_dealloc_body_5392_of_sub_placed
   v9_proto_decoder_dealloc_body_5392_of_dealloc_placed
   v9_proto_decoder_dealloc_body_5392_placed)
export Variant9aPlacedBudgetAux
  (v9_proto_decoder_dealloc_loop_5392_of_sub_placed
   v9_proto_decoder_dealloc_loop_5392_of_dealloc_placed
   v9_proto_decoder_dealloc_loop_5392_placed
   v9_states_from_pb_dealloc_proto_decoder_5368_of_sub_placed
   v9_states_from_pb_dealloc_proto_decoder_5368_of_dealloc_placed)
export Variant9aPlacedBudgetAux
  (v9_states_from_pb_dealloc_proto_decoder_5368_placed
   v9_states_from_pb_dealloc_none_proto_decoder_5360_placed
   v9_states_from_pb_dealloc_none_proto_decoder_5360_placed_budget
   v9_states_from_pb_dealloc_some_proto_decoder_5360_of_sub_placed
   v9_states_from_pb_dealloc_some_proto_decoder_5360_of_dealloc_placed
   v9_states_from_pb_dealloc_some_proto_decoder_5360_placed)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

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

/-! ## 3. Shared `uc` Cleanup Paths (`+7024`, `+6904`, `+8588`, `+488`, `+2768`) -/

/-- Cleanup at `+7024 -> +7084`: drops `ct1` (`cap = [fsp + 128]`, `ptr = [fsp + 72]`)
    and `k1` (`cap = x13`, `ptr = x14`), sets `x28 = 0#64`, and falls through to `+7084`. -/
theorem v9_states_from_pb_drop_uc_7024_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s : State) (fsp out ct1Ptr ct1Cap k1Ptr k1Cap : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 7024#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx13 : s.readReg64 .x13 = k1Cap)
    (hx14 : s.readReg64 .x14 = k1Ptr)
    (hx19 : s.readReg64 .x19 = out)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 7084#64) s
      (((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
        ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
        vecCapPtrDealloc A.repAlloc ct1Cap ct1Ptr ∗
        vecCapPtrDealloc A.repAlloc k1Cap k1Ptr ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢ ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
            ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
            A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v9_Saved7084Preserved s0 sm fsp out) := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc_ok
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  have hsp_align_s : (s.sp &&& 15#64 == 0#64) = true := hsp ▸ hfsp_align
  refine seq_clean_evs (mid := lsmpl.base 333 + 7060#64)
    (P_evs := fun evs1 sm =>
      ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
      ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
      vecCapPtrDealloc A.repAlloc k1Cap k1Ptr ∗
      A.pool lim (M.stepEvents evs1 st) sm ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x13 = k1Cap ∧
      sm.readReg64 .x14 = k1Ptr ∧ sm.readReg64 .x19 = out ∧ TraceCalleeSaved sm s0)
    ?_ ?_
  · change s.pc = (blkPl_333).base + 7024#64 at hpc
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 7060#64) s _ _
    dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
      BitVec.ofNat_eq_ofNat] at hdealloc_fo ⊢
    by_cases hct1 : (ct1Cap == 0#64) = true
    · simp only [hct1, ↓reduceIte, emp_sepConj, sepConj_emp]
      apply sepWP_evs_nil
      simp only [M.stepEvents_nil]
      wp_steps_sync_333 ((blkPl_333).base + 7060#64)
      try simp only [State.setMem_setMem]
      refine align_pre_st (by (try simp only [wp_norm, arm64_norm]); try sep_ac_rfl) ?_
      wp_done
    · have hct1_f : (ct1Cap == 0#64) = false := Bool.eq_false_iff.mpr hct1
      simp only [hct1_f, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      apply sepWP_evs_dealloc ct1Cap.toNat 1
      wp_steps_sync_333 (lsρ spqrRustDeallocSym)
      try simp only [State.setMem_setMem]
      wp_call hdealloc_fo (ct1Ptr, ct1Cap.toNat, 1, st)
      have hacp : AllocCallPreserved s sf := by
        simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
      have htr_sf : sf.trace = s0.trace := hacp.2.1.trans htrace.1
      have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
        ‹calleeSavedVRegs sf = calleeSavedVRegs s›.trans htrace.2
      wp_steps_sync_333 ((blkPl_333).base + 7060#64)
      try simp only [State.setMem_setMem]
      refine align_pre_st (by (try simp only [wp_norm, arm64_norm, hsp]); try sep_ac_rfl) ?_
      wp_done
  · intro evs1 s1 hevs1 hpc1 hrun1 ⟨hsp1, hx13_1, hx14_1, hx19_1, htrace1⟩
    let st1 := M.stepEvents evs1 st
    have hsp_align_s1 : (s1.sp &&& 15#64 == 0#64) = true := hsp1 ▸ hfsp_align
    change s1.pc = (blkPl_333).base + 7060#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 7084#64) s1 _ _
    dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
      BitVec.ofNat_eq_ofNat] at hdealloc_fo ⊢
    by_cases hk1 : (k1Cap == 0#64) = true
    · simp only [hk1, ↓reduceIte, emp_sepConj, sepConj_emp]
      have hfin : SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 7084#64) s1
          (((fsp + 72#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
            A.pool lim st1 s1 ∗ stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
              A.pool lim st1 sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
            v9_Saved7084Preserved s0 sm fsp out) := by
        wp_steps_sync_333 ((blkPl_333).base + 7084#64)
        try simp only [State.setMem_setMem]
        dsimp only [v9_Saved7084Preserved]
        refine align_pre_st (by (try simp only [wp_norm, arm64_norm]); try sep_ac_rfl) ?_
        wp_done
      exact SepWP.mono hfin fun _ _ _ _ ⟨hp, hq⟩ => ⟨evs1, hevs1, hp, hq⟩
    · have hk1_f : (k1Cap == 0#64) = false := Bool.eq_false_iff.mpr hk1
      simp only [hk1_f, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      have hfin : SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 7084#64) s1
          (((fsp + 72#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
            A.live k1Ptr k1Cap.toNat 1 ∗ memRegion k1Ptr k1Cap.toNat ∗
            A.pool lim st1 s1 ∗ stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
              A.pool lim (M.stepEvents (rustDeallocEvents k1Cap.toNat 1) st1) sm ∗
              stackAt fsp allocHookStack ∗ Frame) ∧
            v9_Saved7084Preserved s0 sm fsp out) := by
        wp_steps_sync_333 (lsρ spqrRustDeallocSym)
        try simp only [State.setMem_setMem]
        wp_call hdealloc_fo (k1Ptr, k1Cap.toNat, 1, st1)
        have hacp : AllocCallPreserved s1 sf := by
          simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
        have htr_sf : sf.trace = s0.trace := hacp.2.1.trans htrace1.1
        have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
          ‹calleeSavedVRegs sf = calleeSavedVRegs s1›.trans htrace1.2
        wp_steps_sync_333 ((blkPl_333).base + 7084#64)
        try simp only [State.setMem_setMem]
        dsimp only [v9_Saved7084Preserved]
        refine align_pre_st (by (try simp only [wp_norm, arm64_norm, hsp1]); try sep_ac_rfl) ?_
        wp_done
      refine SepWP.mono hfin fun sm Pm _ _ ⟨hPm, hq⟩ => ?_
      refine ⟨evs1 ++ rustDeallocEvents k1Cap.toNat 1,
        hevs1.append (FreeOnlyEvs.singleton 1 k1Cap.toNat), ?_, hq⟩
      have hst_eq : M.stepEvents (rustDeallocEvents k1Cap.toNat 1) st1 =
          M.stepEvents (evs1 ++ rustDeallocEvents k1Cap.toNat 1) st := by
        dsimp only [st1]; rw [M.stepEvents_append]
      rwa [← hst_eq]

theorem v9_states_from_pb_drop_uc_7024_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s : State) (fsp out ct1Ptr ct1Cap k1Ptr k1Cap : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 7024#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx13 : s.readReg64 .x13 = k1Cap)
    (hx14 : s.readReg64 .x14 = k1Ptr)
    (hx19 : s.readReg64 .x19 = out)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 7084#64) s
      (((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
        ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
        vecCapPtrDealloc A.repAlloc ct1Cap ct1Ptr ∗
        vecCapPtrDealloc A.repAlloc k1Cap k1Ptr ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢ ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
            ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
            A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v9_Saved7084Preserved s0 sm fsp out) :=
  v9_states_from_pb_drop_uc_7024_of_sub_placed
    (v9_sub_ok_dealloc_of_dealloc_placed hdealloc)
    st s0 s fsp out ct1Ptr ct1Cap k1Ptr k1Cap Frame
    hfsp_align hpc hrun hsp hx13 hx14 hx19 htrace

theorem v9_states_from_pb_drop_uc_7024_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s : State) (fsp out ct1Ptr ct1Cap k1Ptr k1Cap : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 7024#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx13 : s.readReg64 .x13 = k1Cap)
    (hx14 : s.readReg64 .x14 = k1Ptr)
    (hx19 : s.readReg64 .x19 = out)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 7084#64) s
      (((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
        ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
        vecCapPtrDealloc A.repAlloc ct1Cap ct1Ptr ∗
        vecCapPtrDealloc A.repAlloc k1Cap k1Ptr ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢ ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
            ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
            A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v9_Saved7084Preserved s0 sm fsp out) :=
  v9_states_from_pb_drop_uc_7024_of_dealloc_placed
    hA.dealloc st s0 s fsp out ct1Ptr ct1Cap k1Ptr k1Cap Frame
    hfsp_align hpc hrun hsp hx13 hx14 hx19 htrace

/-- Cleanup at `+6904 -> +7084`: drops `rootKey` (`cap = x10`, `ptr = x28`),
    `macKey` (`cap = x1`, `ptr = x0`), `ek` (`cap = [fsp + 152]`, `ptr = [fsp + 144]`),
    `ct1` (`cap = [fsp + 128]`, `ptr = [fsp + 72]`), and `k1` (`cap = x13`, `ptr = x14`),
    sets `x28 = 0#64`, and falls through to `+7084`. -/
theorem v9_states_from_pb_drop_uc_6904_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s : State)
    (fsp out rkPtr rkCap mkPtr mkCap ekPtr ekCap ct1Ptr ct1Cap k1Ptr k1Cap : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 6904#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = mkPtr)
    (hx1 : s.readReg64 .x1 = mkCap)
    (hx10 : s.readReg64 .x10 = rkCap)
    (hx13 : s.readReg64 .x13 = k1Cap)
    (hx14 : s.readReg64 .x14 = k1Ptr)
    (hx19 : s.readReg64 .x19 = out)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 7084#64) s
      (((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
        ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
        ((fsp + 144#64) ↦₆₄ ekPtr) ∗
        ((fsp + 152#64) ↦₆₄ ekCap) ∗
        vecCapPtrDealloc A.repAlloc rkCap rkPtr ∗
        vecCapPtrDealloc A.repAlloc mkCap mkPtr ∗
        vecCapPtrDealloc A.repAlloc ekCap ekPtr ∗
        vecCapPtrDealloc A.repAlloc ct1Cap ct1Ptr ∗
        vecCapPtrDealloc A.repAlloc k1Cap k1Ptr ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢ ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
            ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
            ((fsp + 144#64) ↦₆₄ ekPtr) ∗
            ((fsp + 152#64) ↦₆₄ ekCap) ∗
            A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v9_Saved7084Preserved s0 sm fsp out) := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc_ok
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  have hsp_align_s : (s.sp &&& 15#64 == 0#64) = true := hsp ▸ hfsp_align
  refine seq_clean_evs (mid := lsmpl.base 333 + 6960#64)
    (P_evs := fun evs1 sm =>
      ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
      ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
      ((fsp + 144#64) ↦₆₄ ekPtr) ∗
      ((fsp + 152#64) ↦₆₄ ekCap) ∗
      vecCapPtrDealloc A.repAlloc mkCap mkPtr ∗
      vecCapPtrDealloc A.repAlloc ekCap ekPtr ∗
      vecCapPtrDealloc A.repAlloc ct1Cap ct1Ptr ∗
      vecCapPtrDealloc A.repAlloc k1Cap k1Ptr ∗
      A.pool lim (M.stepEvents evs1 st) sm ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x0 = mkPtr ∧ sm.readReg64 .x1 = mkCap ∧
      sm.readReg64 .x13 = k1Cap ∧ sm.readReg64 .x14 = k1Ptr ∧
      sm.readReg64 .x19 = out ∧ sm.readReg64 .x20 = ekCap ∧ TraceCalleeSaved sm s0)
    ?_ ?_
  · change s.pc = (blkPl_333).base + 6904#64 at hpc
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 6960#64) s _ _
    dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
      BitVec.ofNat_eq_ofNat] at hdealloc_fo ⊢
    by_cases hrk : (rkCap == 0#64) = true
    · simp only [hrk, ↓reduceIte, emp_sepConj, sepConj_emp]
      apply sepWP_evs_nil
      simp only [M.stepEvents_nil]
      wp_steps_sync_333 ((blkPl_333).base + 6960#64)
      try simp only [State.setMem_setMem]
      refine align_pre_st (by (try simp only [wp_norm, arm64_norm]); try sep_ac_rfl) ?_
      wp_done
    · have hrk_f : (rkCap == 0#64) = false := Bool.eq_false_iff.mpr hrk
      simp only [hrk_f, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      apply sepWP_evs_dealloc rkCap.toNat 1
      wp_steps_sync_333 (lsρ spqrRustDeallocSym)
      try simp only [State.setMem_setMem]
      wp_call hdealloc_fo (rkPtr, rkCap.toNat, 1, st)
      have hacp : AllocCallPreserved s sf := by
        simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
      have htr_sf : sf.trace = s0.trace := hacp.2.1.trans htrace.1
      have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
        ‹calleeSavedVRegs sf = calleeSavedVRegs s›.trans htrace.2
      wp_steps_sync_333 ((blkPl_333).base + 6960#64)
      try simp only [State.setMem_setMem]
      refine align_pre_st (by (try simp only [wp_norm, arm64_norm, hsp]); try sep_ac_rfl) ?_
      wp_done
  · intro evs1 s1 hevs1 hpc1 hrun1 ⟨hsp1, hx0_1, hx1_1, hx13_1, hx14_1, hx19_1, hx20_1, htrace1⟩
    let st1 := M.stepEvents evs1 st
    have hsp_align_s1 : (s1.sp &&& 15#64 == 0#64) = true := hsp1 ▸ hfsp_align
    refine seq_clean_evs (mid := lsmpl.base 333 + 6988#64)
      (P_evs := fun evs2 sm =>
        ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
        ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
        ((fsp + 144#64) ↦₆₄ ekPtr) ∗
        ((fsp + 152#64) ↦₆₄ ekCap) ∗
        vecCapPtrDealloc A.repAlloc ekCap ekPtr ∗
        vecCapPtrDealloc A.repAlloc ct1Cap ct1Ptr ∗
        vecCapPtrDealloc A.repAlloc k1Cap k1Ptr ∗
        A.pool lim (M.stepEvents evs2 st1) sm ∗ stackAt fsp allocHookStack ∗ Frame)
      (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x13 = k1Cap ∧ sm.readReg64 .x14 = k1Ptr ∧
        sm.readReg64 .x19 = out ∧ sm.readReg64 .x20 = ekCap ∧ TraceCalleeSaved sm s0)
      ?_ ?_
    · change s1.pc = (blkPl_333).base + 6960#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 6988#64) s1 _ _
      dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
        BitVec.ofNat_eq_ofNat] at hdealloc_fo ⊢
      by_cases hmk : (mkCap == 0#64) = true
      · simp only [hmk, ↓reduceIte, emp_sepConj, sepConj_emp]
        apply sepWP_evs_nil
        simp only [M.stepEvents_nil]
        wp_steps_sync_333 ((blkPl_333).base + 6988#64)
        try simp only [State.setMem_setMem]
        refine align_pre_st (by (try simp only [wp_norm, arm64_norm]); try sep_ac_rfl) ?_
        wp_done
      · have hmk_f : (mkCap == 0#64) = false := Bool.eq_false_iff.mpr hmk
        simp only [hmk_f, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
        apply sepWP_evs_dealloc mkCap.toNat 1
        wp_steps_sync_333 (lsρ spqrRustDeallocSym)
        try simp only [State.setMem_setMem]
        wp_call hdealloc_fo (mkPtr, mkCap.toNat, 1, st1)
        have hacp : AllocCallPreserved s1 sf := by
          simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
        have htr_sf : sf.trace = s0.trace := hacp.2.1.trans htrace1.1
        have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
          ‹calleeSavedVRegs sf = calleeSavedVRegs s1›.trans htrace1.2
        wp_steps_sync_333 ((blkPl_333).base + 6988#64)
        try simp only [State.setMem_setMem]
        refine align_pre_st (by (try simp only [wp_norm, arm64_norm, hsp1]); try sep_ac_rfl) ?_
        wp_done
    · intro evs2 s2 hevs2 hpc2 hrun2 ⟨hsp2, hx13_2, hx14_2, hx19_2, hx20_2, htrace2⟩
      let st2 := M.stepEvents evs2 st1
      have hsp_align_s2 : (s2.sp &&& 15#64 == 0#64) = true := hsp2 ▸ hfsp_align
      refine seq_clean_evs (mid := lsmpl.base 333 + 7024#64)
        (P_evs := fun evs3 sm =>
          ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
          ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
          vecCapPtrDealloc A.repAlloc ct1Cap ct1Ptr ∗
          vecCapPtrDealloc A.repAlloc k1Cap k1Ptr ∗
          A.pool lim (M.stepEvents evs3 st2) sm ∗ stackAt fsp allocHookStack ∗
          (((fsp + 144#64) ↦₆₄ ekPtr) ∗ ((fsp + 152#64) ↦₆₄ ekCap) ∗ Frame))
        (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x13 = k1Cap ∧ sm.readReg64 .x14 = k1Ptr ∧
          sm.readReg64 .x19 = out ∧ TraceCalleeSaved sm s0)
        ?_ ?_
      · change s2.pc = (blkPl_333).base + 6988#64 at hpc2
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 7024#64) s2 _ _
        dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
          BitVec.ofNat_eq_ofNat] at hdealloc_fo ⊢
        by_cases hek : (ekCap == 0#64) = true
        · simp only [hek, ↓reduceIte, emp_sepConj, sepConj_emp]
          apply sepWP_evs_nil
          simp only [M.stepEvents_nil]
          wp_steps_sync_333 ((blkPl_333).base + 7024#64)
          try simp only [State.setMem_setMem]
          refine align_pre_st (by (try simp only [wp_norm, arm64_norm]); try sep_ac_rfl) ?_
          wp_done
        · have hek_f : (ekCap == 0#64) = false := Bool.eq_false_iff.mpr hek
          simp only [hek_f, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
          apply sepWP_evs_dealloc ekCap.toNat 1
          wp_steps_sync_333 (lsρ spqrRustDeallocSym)
          try simp only [State.setMem_setMem]
          wp_call hdealloc_fo (ekPtr, ekCap.toNat, 1, st2)
          have hacp : AllocCallPreserved s2 sf := by
            simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
          have htr_sf : sf.trace = s0.trace := hacp.2.1.trans htrace2.1
          have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
            ‹calleeSavedVRegs sf = calleeSavedVRegs s2›.trans htrace2.2
          wp_steps_sync_333 ((blkPl_333).base + 7024#64)
          try simp only [State.setMem_setMem]
          refine align_pre_st (by (try simp only [wp_norm, arm64_norm, hsp2]); try sep_ac_rfl) ?_
          wp_done
      · intro evs3 s3 hevs3 hpc3 hrun3 ⟨hsp3, hx13_3, hx14_3, hx19_3, htrace3⟩
        let st3 := M.stepEvents evs3 st2
        have hcall := v9_states_from_pb_drop_uc_7024_of_sub_placed hdealloc_ok
          st3 s0 s3 fsp out ct1Ptr ct1Cap k1Ptr k1Cap
          (((fsp + 144#64) ↦₆₄ ekPtr) ∗ ((fsp + 152#64) ↦₆₄ ekCap) ∗ Frame)
          hfsp_align hpc3 hrun3 hsp3 hx13_3 hx14_3 hx19_3 htrace3
        refine SepWP.mono hcall fun sm Pm _ _ ⟨evs4, hevs4, hPm, hpres⟩ => ?_
        refine ⟨evs1 ++ evs2 ++ evs3 ++ evs4,
          ((hevs1.append hevs2).append hevs3).append hevs4, ?_, hpres⟩
        have hst_eq : M.stepEvents evs4 st3 =
            M.stepEvents (evs1 ++ evs2 ++ evs3 ++ evs4) st := by
          dsimp only [st3, st2, st1]
          rw [M.stepEvents_append, M.stepEvents_append, M.stepEvents_append]
        rw [hst_eq] at hPm
        exact Entails.trans hPm (Entails.of_eq (by sep_ac_rfl))

theorem v9_states_from_pb_drop_uc_6904_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s : State)
    (fsp out rkPtr rkCap mkPtr mkCap ekPtr ekCap ct1Ptr ct1Cap k1Ptr k1Cap : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 6904#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = mkPtr)
    (hx1 : s.readReg64 .x1 = mkCap)
    (hx10 : s.readReg64 .x10 = rkCap)
    (hx13 : s.readReg64 .x13 = k1Cap)
    (hx14 : s.readReg64 .x14 = k1Ptr)
    (hx19 : s.readReg64 .x19 = out)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 7084#64) s
      (((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
        ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
        ((fsp + 144#64) ↦₆₄ ekPtr) ∗
        ((fsp + 152#64) ↦₆₄ ekCap) ∗
        vecCapPtrDealloc A.repAlloc rkCap rkPtr ∗
        vecCapPtrDealloc A.repAlloc mkCap mkPtr ∗
        vecCapPtrDealloc A.repAlloc ekCap ekPtr ∗
        vecCapPtrDealloc A.repAlloc ct1Cap ct1Ptr ∗
        vecCapPtrDealloc A.repAlloc k1Cap k1Ptr ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢ ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
            ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
            ((fsp + 144#64) ↦₆₄ ekPtr) ∗
            ((fsp + 152#64) ↦₆₄ ekCap) ∗
            A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v9_Saved7084Preserved s0 sm fsp out) :=
  v9_states_from_pb_drop_uc_6904_of_sub_placed
    (v9_sub_ok_dealloc_of_dealloc_placed hdealloc)
    st s0 s fsp out rkPtr rkCap mkPtr mkCap ekPtr ekCap ct1Ptr ct1Cap k1Ptr k1Cap Frame
    hfsp_align hpc hrun hsp hx0 hx1 hx10 hx13 hx14 hx19 hx28 htrace

theorem v9_states_from_pb_drop_uc_6904_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s : State)
    (fsp out rkPtr rkCap mkPtr mkCap ekPtr ekCap ct1Ptr ct1Cap k1Ptr k1Cap : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 6904#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = mkPtr)
    (hx1 : s.readReg64 .x1 = mkCap)
    (hx10 : s.readReg64 .x10 = rkCap)
    (hx13 : s.readReg64 .x13 = k1Cap)
    (hx14 : s.readReg64 .x14 = k1Ptr)
    (hx19 : s.readReg64 .x19 = out)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 7084#64) s
      (((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
        ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
        ((fsp + 144#64) ↦₆₄ ekPtr) ∗
        ((fsp + 152#64) ↦₆₄ ekCap) ∗
        vecCapPtrDealloc A.repAlloc rkCap rkPtr ∗
        vecCapPtrDealloc A.repAlloc mkCap mkPtr ∗
        vecCapPtrDealloc A.repAlloc ekCap ekPtr ∗
        vecCapPtrDealloc A.repAlloc ct1Cap ct1Ptr ∗
        vecCapPtrDealloc A.repAlloc k1Cap k1Ptr ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢ ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
            ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
            ((fsp + 144#64) ↦₆₄ ekPtr) ∗
            ((fsp + 152#64) ↦₆₄ ekCap) ∗
            A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v9_Saved7084Preserved s0 sm fsp out) :=
  v9_states_from_pb_drop_uc_6904_of_dealloc_placed
    hA.dealloc st s0 s fsp out rkPtr rkCap mkPtr mkCap ekPtr ekCap ct1Ptr ct1Cap k1Ptr k1Cap Frame
    hfsp_align hpc hrun hsp hx0 hx1 hx10 hx13 hx14 hx19 hx28 htrace

private theorem v9_drop_uc_8652_to_7084 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st3 : M.σ) (s0 s3 : State)
    (fsp out rkCap mkPtr mkCap ekPtr ekCap ct1Ptr ct1Cap k1Ptr k1Cap : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc3 : s3.pc = lsmpl.base 333 + 8652#64)
    (hrun3 : s3.status = .Running)
    (hsp3 : s3.sp = fsp)
    (hx19_3 : s3.readReg64 .x19 = out)
    (htrace3 : TraceCalleeSaved s3 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 7084#64) s3
      (((fsp + 48#64) ↦₆₄ k1Cap) ∗
        ((fsp + 56#64) ↦₆₄ rkCap) ∗
        ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
        ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
        ((fsp + 136#64) ↦₆₄ mkPtr) ∗
        ((fsp + 144#64) ↦₆₄ ekPtr) ∗
        ((fsp + 152#64) ↦₆₄ ekCap) ∗
        ((fsp + 200#64) ↦₆₄ k1Ptr) ∗
        ((fsp + 216#64) ↦₆₄ mkCap) ∗
        vecCapPtrDealloc A.repAlloc ct1Cap ct1Ptr ∗
        vecCapPtrDealloc A.repAlloc k1Cap k1Ptr ∗
        A.pool lim st3 s3 ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢ ((fsp + 48#64) ↦₆₄ k1Cap) ∗
            ((fsp + 56#64) ↦₆₄ rkCap) ∗
            ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
            ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
            ((fsp + 136#64) ↦₆₄ mkPtr) ∗
            ((fsp + 144#64) ↦₆₄ ekPtr) ∗
            ((fsp + 152#64) ↦₆₄ ekCap) ∗
            ((fsp + 200#64) ↦₆₄ k1Ptr) ∗
            ((fsp + 216#64) ↦₆₄ mkCap) ∗
            A.pool lim (M.stepEvents evs st3) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v9_Saved7084Preserved s0 sm fsp out) := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc_ok
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  have hsp_align_s3 : (s3.sp &&& 15#64 == 0#64) = true := hsp3 ▸ hfsp_align
  refine seq_clean_evs (mid := lsmpl.base 333 + 8672#64)
    (P_evs := fun evs4 sm =>
      ((fsp + 48#64) ↦₆₄ k1Cap) ∗
      ((fsp + 56#64) ↦₆₄ rkCap) ∗
      ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
      ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
      ((fsp + 136#64) ↦₆₄ mkPtr) ∗
      ((fsp + 144#64) ↦₆₄ ekPtr) ∗
      ((fsp + 152#64) ↦₆₄ ekCap) ∗
      ((fsp + 200#64) ↦₆₄ k1Ptr) ∗
      ((fsp + 216#64) ↦₆₄ mkCap) ∗
      vecCapPtrDealloc A.repAlloc k1Cap k1Ptr ∗
      A.pool lim (M.stepEvents evs4 st3) sm ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧ TraceCalleeSaved sm s0)
    ?_ ?_
  · change s3.pc = (blkPl_333).base + 8652#64 at hpc3
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 8672#64) s3 _ _
    dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
      BitVec.ofNat_eq_ofNat] at hdealloc_fo ⊢
    by_cases hct1 : (ct1Cap == 0#64) = true
    · simp only [hct1, ↓reduceIte, emp_sepConj, sepConj_emp]
      apply sepWP_evs_nil
      simp only [M.stepEvents_nil]
      wp_steps_sync_333 ((blkPl_333).base + 8672#64)
      try simp only [State.setMem_setMem]
      refine align_pre_st (by (try simp only [wp_norm, arm64_norm]); try sep_ac_rfl) ?_
      wp_done
    · have hct1_f : (ct1Cap == 0#64) = false := Bool.eq_false_iff.mpr hct1
      simp only [hct1_f, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      apply sepWP_evs_dealloc ct1Cap.toNat 1
      wp_steps_sync_333 (lsρ spqrRustDeallocSym)
      try simp only [State.setMem_setMem]
      wp_call hdealloc_fo (ct1Ptr, ct1Cap.toNat, 1, st3)
      have hacp : AllocCallPreserved s3 sf := by
        simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
      have hsp_sf : sf.sp = fsp := ‹sf.sp = s3.sp›.trans hsp3
      have htr_sf : sf.trace = s0.trace := hacp.2.1.trans htrace3.1
      have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
        ‹calleeSavedVRegs sf = calleeSavedVRegs s3›.trans htrace3.2
      refine align_pre_st (by rw [hsp3]; (try simp only [wp_norm, arm64_norm]); try sep_ac_rfl) ?_
      wp_done
  · intro evs4 s4 hevs4 hpc4 hrun4 ⟨hsp4, hx19_4, htrace4⟩
    let st4 := M.stepEvents evs4 st3
    have hsp_align_s4 : (s4.sp &&& 15#64 == 0#64) = true := hsp4 ▸ hfsp_align
    change s4.pc = (blkPl_333).base + 8672#64 at hpc4
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 7084#64) s4 _ _
    dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
      BitVec.ofNat_eq_ofNat] at hdealloc_fo ⊢
    by_cases hk1 : (k1Cap == 0#64) = true
    · simp only [hk1, ↓reduceIte, emp_sepConj, sepConj_emp]
      have hfin : SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 7084#64) s4
          (((fsp + 48#64) ↦₆₄ k1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗
            ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
            ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ ekPtr) ∗
            ((fsp + 152#64) ↦₆₄ ekCap) ∗ ((fsp + 200#64) ↦₆₄ k1Ptr) ∗
            ((fsp + 216#64) ↦₆₄ mkCap) ∗
            A.pool lim st4 s4 ∗ stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ ((fsp + 48#64) ↦₆₄ k1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗
              ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
              ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ ekPtr) ∗
              ((fsp + 152#64) ↦₆₄ ekCap) ∗ ((fsp + 200#64) ↦₆₄ k1Ptr) ∗
              ((fsp + 216#64) ↦₆₄ mkCap) ∗
              A.pool lim st4 sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
            v9_Saved7084Preserved s0 sm fsp out) := by
        wp_steps_sync_333 ((blkPl_333).base + 7084#64)
        try simp only [State.setMem_setMem]
        dsimp only [v9_Saved7084Preserved]
        refine align_pre_st (by (try simp only [wp_norm, arm64_norm]); try sep_ac_rfl) ?_
        wp_done
      exact SepWP.mono hfin fun _ _ _ _ ⟨hp, hq⟩ => ⟨evs4, hevs4, hp, hq⟩
    · have hk1_f : (k1Cap == 0#64) = false := Bool.eq_false_iff.mpr hk1
      simp only [hk1_f, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      have hfin : SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 7084#64) s4
          (((fsp + 48#64) ↦₆₄ k1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗
            ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
            ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ ekPtr) ∗
            ((fsp + 152#64) ↦₆₄ ekCap) ∗ ((fsp + 200#64) ↦₆₄ k1Ptr) ∗
            ((fsp + 216#64) ↦₆₄ mkCap) ∗
            A.live k1Ptr k1Cap.toNat 1 ∗ memRegion k1Ptr k1Cap.toNat ∗
            A.pool lim st4 s4 ∗ stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ ((fsp + 48#64) ↦₆₄ k1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗
              ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
              ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ ekPtr) ∗
              ((fsp + 152#64) ↦₆₄ ekCap) ∗ ((fsp + 200#64) ↦₆₄ k1Ptr) ∗
              ((fsp + 216#64) ↦₆₄ mkCap) ∗
              A.pool lim (M.stepEvents (rustDeallocEvents k1Cap.toNat 1) st4) sm ∗
              stackAt fsp allocHookStack ∗ Frame) ∧
            v9_Saved7084Preserved s0 sm fsp out) := by
        wp_steps_sync_333 (lsρ spqrRustDeallocSym)
        try simp only [State.setMem_setMem]
        wp_call hdealloc_fo (k1Ptr, k1Cap.toNat, 1, st4)
        have hacp : AllocCallPreserved s4 sf := by
          simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
        have htr_sf : sf.trace = s0.trace := hacp.2.1.trans htrace4.1
        have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
          ‹calleeSavedVRegs sf = calleeSavedVRegs s4›.trans htrace4.2
        wp_steps_sync_333 ((blkPl_333).base + 7084#64)
        try simp only [State.setMem_setMem]
        dsimp only [v9_Saved7084Preserved]
        refine align_pre_st (by (try simp only [wp_norm, arm64_norm, hsp4]); try sep_ac_rfl) ?_
        wp_done
      refine SepWP.mono hfin fun sm Pm _ _ ⟨hPm, hq⟩ => ?_
      refine ⟨evs4 ++ rustDeallocEvents k1Cap.toNat 1,
        hevs4.append (FreeOnlyEvs.singleton 1 k1Cap.toNat), ?_, hq⟩
      have hst_eq : M.stepEvents (rustDeallocEvents k1Cap.toNat 1) st4 =
          M.stepEvents (evs4 ++ rustDeallocEvents k1Cap.toNat 1) st3 := by
        dsimp only [st4]; rw [M.stepEvents_append]
      rwa [← hst_eq]

/-- Cleanup at `+8588 -> +7084`: drops `rootKey` (`cap = [fsp + 56]`, `ptr = x28`),
    `macKey` (`cap = [fsp + 216]`, `ptr = [fsp + 136]`), `ek` (`cap = [fsp + 152]`, `ptr = [fsp + 144]`),
    `ct1` (`cap = [fsp + 128]`, `ptr = [fsp + 72]`), and `k1` (`cap = [fsp + 48]`, `ptr = [fsp + 200]`),
    sets `x28 = 0#64`, and branches to `+7084`. -/
theorem v9_states_from_pb_drop_uc_8588_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s : State)
    (fsp out rkPtr rkCap mkPtr mkCap ekPtr ekCap ct1Ptr ct1Cap k1Ptr k1Cap : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 8588#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 7084#64) s
      (((fsp + 48#64) ↦₆₄ k1Cap) ∗
        ((fsp + 56#64) ↦₆₄ rkCap) ∗
        ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
        ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
        ((fsp + 136#64) ↦₆₄ mkPtr) ∗
        ((fsp + 144#64) ↦₆₄ ekPtr) ∗
        ((fsp + 152#64) ↦₆₄ ekCap) ∗
        ((fsp + 200#64) ↦₆₄ k1Ptr) ∗
        ((fsp + 216#64) ↦₆₄ mkCap) ∗
        vecCapPtrDealloc A.repAlloc rkCap rkPtr ∗
        vecCapPtrDealloc A.repAlloc mkCap mkPtr ∗
        vecCapPtrDealloc A.repAlloc ekCap ekPtr ∗
        vecCapPtrDealloc A.repAlloc ct1Cap ct1Ptr ∗
        vecCapPtrDealloc A.repAlloc k1Cap k1Ptr ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢ ((fsp + 48#64) ↦₆₄ k1Cap) ∗
            ((fsp + 56#64) ↦₆₄ rkCap) ∗
            ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
            ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
            ((fsp + 136#64) ↦₆₄ mkPtr) ∗
            ((fsp + 144#64) ↦₆₄ ekPtr) ∗
            ((fsp + 152#64) ↦₆₄ ekCap) ∗
            ((fsp + 200#64) ↦₆₄ k1Ptr) ∗
            ((fsp + 216#64) ↦₆₄ mkCap) ∗
            A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v9_Saved7084Preserved s0 sm fsp out) := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc_ok
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  have hsp_align_s : (s.sp &&& 15#64 == 0#64) = true := hsp ▸ hfsp_align
  refine seq_clean_evs (mid := lsmpl.base 333 + 8608#64)
    (P_evs := fun evs1 sm =>
      ((fsp + 48#64) ↦₆₄ k1Cap) ∗
      ((fsp + 56#64) ↦₆₄ rkCap) ∗
      ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
      ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
      ((fsp + 136#64) ↦₆₄ mkPtr) ∗
      ((fsp + 144#64) ↦₆₄ ekPtr) ∗
      ((fsp + 152#64) ↦₆₄ ekCap) ∗
      ((fsp + 200#64) ↦₆₄ k1Ptr) ∗
      ((fsp + 216#64) ↦₆₄ mkCap) ∗
      vecCapPtrDealloc A.repAlloc mkCap mkPtr ∗
      vecCapPtrDealloc A.repAlloc ekCap ekPtr ∗
      vecCapPtrDealloc A.repAlloc ct1Cap ct1Ptr ∗
      vecCapPtrDealloc A.repAlloc k1Cap k1Ptr ∗
      A.pool lim (M.stepEvents evs1 st) sm ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧ TraceCalleeSaved sm s0)
    ?_ ?_
  · change s.pc = (blkPl_333).base + 8588#64 at hpc
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 8608#64) s _ _
    dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
      BitVec.ofNat_eq_ofNat] at hdealloc_fo ⊢
    by_cases hrk : (rkCap == 0#64) = true
    · simp only [hrk, ↓reduceIte, emp_sepConj, sepConj_emp]
      apply sepWP_evs_nil
      simp only [M.stepEvents_nil]
      wp_steps_sync_333 ((blkPl_333).base + 8608#64)
      try simp only [State.setMem_setMem]
      refine align_pre_st (by (try simp only [wp_norm, arm64_norm]); try sep_ac_rfl) ?_
      wp_done
    · have hrk_f : (rkCap == 0#64) = false := Bool.eq_false_iff.mpr hrk
      simp only [hrk_f, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      apply sepWP_evs_dealloc rkCap.toNat 1
      wp_steps_sync_333 (lsρ spqrRustDeallocSym)
      try simp only [State.setMem_setMem]
      wp_call hdealloc_fo (rkPtr, rkCap.toNat, 1, st)
      have hacp : AllocCallPreserved s sf := by
        simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
      have hsp_sf : sf.sp = fsp := ‹sf.sp = s.sp›.trans hsp
      have htr_sf : sf.trace = s0.trace := hacp.2.1.trans htrace.1
      have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
        ‹calleeSavedVRegs sf = calleeSavedVRegs s›.trans htrace.2
      refine align_pre_st (by rw [hsp]; (try simp only [wp_norm, arm64_norm]); try sep_ac_rfl) ?_
      wp_done
  · intro evs1 s1 hevs1 hpc1 hrun1 ⟨hsp1, hx19_1, htrace1⟩
    let st1 := M.stepEvents evs1 st
    have hsp_align_s1 : (s1.sp &&& 15#64 == 0#64) = true := hsp1 ▸ hfsp_align
    refine seq_clean_evs (mid := lsmpl.base 333 + 8632#64)
      (P_evs := fun evs2 sm =>
        ((fsp + 48#64) ↦₆₄ k1Cap) ∗
        ((fsp + 56#64) ↦₆₄ rkCap) ∗
        ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
        ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
        ((fsp + 136#64) ↦₆₄ mkPtr) ∗
        ((fsp + 144#64) ↦₆₄ ekPtr) ∗
        ((fsp + 152#64) ↦₆₄ ekCap) ∗
        ((fsp + 200#64) ↦₆₄ k1Ptr) ∗
        ((fsp + 216#64) ↦₆₄ mkCap) ∗
        vecCapPtrDealloc A.repAlloc ekCap ekPtr ∗
        vecCapPtrDealloc A.repAlloc ct1Cap ct1Ptr ∗
        vecCapPtrDealloc A.repAlloc k1Cap k1Ptr ∗
        A.pool lim (M.stepEvents evs2 st1) sm ∗ stackAt fsp allocHookStack ∗ Frame)
      (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = ekCap ∧ TraceCalleeSaved sm s0)
      ?_ ?_
    · change s1.pc = (blkPl_333).base + 8608#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 8632#64) s1 _ _
      dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
        BitVec.ofNat_eq_ofNat] at hdealloc_fo ⊢
      by_cases hmk : (mkCap == 0#64) = true
      · simp only [hmk, ↓reduceIte, emp_sepConj, sepConj_emp]
        apply sepWP_evs_nil
        simp only [M.stepEvents_nil]
        wp_steps_sync_333 ((blkPl_333).base + 8632#64)
        try simp only [State.setMem_setMem]
        refine align_pre_st (by (try simp only [wp_norm, arm64_norm]); try sep_ac_rfl) ?_
        wp_done
      · have hmk_f : (mkCap == 0#64) = false := Bool.eq_false_iff.mpr hmk
        simp only [hmk_f, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
        apply sepWP_evs_dealloc mkCap.toNat 1
        wp_steps_sync_333 (lsρ spqrRustDeallocSym)
        try simp only [State.setMem_setMem]
        wp_call hdealloc_fo (mkPtr, mkCap.toNat, 1, st1)
        have hacp : AllocCallPreserved s1 sf := by
          simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
        have hsp_sf : sf.sp = fsp := ‹sf.sp = s1.sp›.trans hsp1
        have htr_sf : sf.trace = s0.trace := hacp.2.1.trans htrace1.1
        have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
          ‹calleeSavedVRegs sf = calleeSavedVRegs s1›.trans htrace1.2
        refine align_pre_st (by rw [hsp1]; (try simp only [wp_norm, arm64_norm]); try sep_ac_rfl) ?_
        wp_done
    · intro evs2 s2 hevs2 hpc2 hrun2 ⟨hsp2, hx19_2, hx20_2, htrace2⟩
      let st2 := M.stepEvents evs2 st1
      have hsp_align_s2 : (s2.sp &&& 15#64 == 0#64) = true := hsp2 ▸ hfsp_align
      refine seq_clean_evs (mid := lsmpl.base 333 + 8652#64)
        (P_evs := fun evs3 sm =>
          ((fsp + 48#64) ↦₆₄ k1Cap) ∗
          ((fsp + 56#64) ↦₆₄ rkCap) ∗
          ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
          ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
          ((fsp + 136#64) ↦₆₄ mkPtr) ∗
          ((fsp + 144#64) ↦₆₄ ekPtr) ∗
          ((fsp + 152#64) ↦₆₄ ekCap) ∗
          ((fsp + 200#64) ↦₆₄ k1Ptr) ∗
          ((fsp + 216#64) ↦₆₄ mkCap) ∗
          vecCapPtrDealloc A.repAlloc ct1Cap ct1Ptr ∗
          vecCapPtrDealloc A.repAlloc k1Cap k1Ptr ∗
          A.pool lim (M.stepEvents evs3 st2) sm ∗ stackAt fsp allocHookStack ∗ Frame)
        (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧ TraceCalleeSaved sm s0)
        ?_ ?_
      · change s2.pc = (blkPl_333).base + 8632#64 at hpc2
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 8652#64) s2 _ _
        dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
          BitVec.ofNat_eq_ofNat] at hdealloc_fo ⊢
        by_cases hek : (ekCap == 0#64) = true
        · simp only [hek, ↓reduceIte, emp_sepConj, sepConj_emp]
          apply sepWP_evs_nil
          simp only [M.stepEvents_nil]
          wp_steps_sync_333 ((blkPl_333).base + 8652#64)
          try simp only [State.setMem_setMem]
          refine align_pre_st (by (try simp only [wp_norm, arm64_norm]); try sep_ac_rfl) ?_
          wp_done
        · have hek_f : (ekCap == 0#64) = false := Bool.eq_false_iff.mpr hek
          simp only [hek_f, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
          apply sepWP_evs_dealloc ekCap.toNat 1
          wp_steps_sync_333 (lsρ spqrRustDeallocSym)
          try simp only [State.setMem_setMem]
          wp_call hdealloc_fo (ekPtr, ekCap.toNat, 1, st2)
          have hacp : AllocCallPreserved s2 sf := by
            simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
          have hsp_sf : sf.sp = fsp := ‹sf.sp = s2.sp›.trans hsp2
          have htr_sf : sf.trace = s0.trace := hacp.2.1.trans htrace2.1
          have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
            ‹calleeSavedVRegs sf = calleeSavedVRegs s2›.trans htrace2.2
          refine align_pre_st (by rw [hsp2]; (try simp only [wp_norm, arm64_norm]); try sep_ac_rfl) ?_
          wp_done
      · intro evs3 s3 hevs3 hpc3 hrun3 ⟨hsp3, hx19_3, htrace3⟩
        let st3 := M.stepEvents evs3 st2
        have htail := v9_drop_uc_8652_to_7084 hdealloc_ok st3 s0 s3
          fsp out rkCap mkPtr mkCap ekPtr ekCap ct1Ptr ct1Cap k1Ptr k1Cap Frame
          hfsp_align hpc3 hrun3 hsp3 hx19_3 htrace3
        refine SepWP.mono htail fun sm Pm _ _ ⟨evs4, hevs4, hPm, hq⟩ => ?_
        refine ⟨evs1 ++ evs2 ++ evs3 ++ evs4,
          ((hevs1.append hevs2).append hevs3).append hevs4, ?_, hq⟩
        have hst_eq : M.stepEvents evs4 st3 =
            M.stepEvents (evs1 ++ evs2 ++ evs3 ++ evs4) st := by
          dsimp only [st3, st2, st1]
          rw [M.stepEvents_append, M.stepEvents_append, M.stepEvents_append]
        rwa [← hst_eq]

theorem v9_states_from_pb_drop_uc_8588_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s : State)
    (fsp out rkPtr rkCap mkPtr mkCap ekPtr ekCap ct1Ptr ct1Cap k1Ptr k1Cap : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 8588#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 7084#64) s
      (((fsp + 48#64) ↦₆₄ k1Cap) ∗
        ((fsp + 56#64) ↦₆₄ rkCap) ∗
        ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
        ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
        ((fsp + 136#64) ↦₆₄ mkPtr) ∗
        ((fsp + 144#64) ↦₆₄ ekPtr) ∗
        ((fsp + 152#64) ↦₆₄ ekCap) ∗
        ((fsp + 200#64) ↦₆₄ k1Ptr) ∗
        ((fsp + 216#64) ↦₆₄ mkCap) ∗
        vecCapPtrDealloc A.repAlloc rkCap rkPtr ∗
        vecCapPtrDealloc A.repAlloc mkCap mkPtr ∗
        vecCapPtrDealloc A.repAlloc ekCap ekPtr ∗
        vecCapPtrDealloc A.repAlloc ct1Cap ct1Ptr ∗
        vecCapPtrDealloc A.repAlloc k1Cap k1Ptr ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢ ((fsp + 48#64) ↦₆₄ k1Cap) ∗
            ((fsp + 56#64) ↦₆₄ rkCap) ∗
            ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
            ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
            ((fsp + 136#64) ↦₆₄ mkPtr) ∗
            ((fsp + 144#64) ↦₆₄ ekPtr) ∗
            ((fsp + 152#64) ↦₆₄ ekCap) ∗
            ((fsp + 200#64) ↦₆₄ k1Ptr) ∗
            ((fsp + 216#64) ↦₆₄ mkCap) ∗
            A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v9_Saved7084Preserved s0 sm fsp out) :=
  v9_states_from_pb_drop_uc_8588_of_sub_placed
    (v9_sub_ok_dealloc_of_dealloc_placed hdealloc)
    st s0 s fsp out rkPtr rkCap mkPtr mkCap ekPtr ekCap ct1Ptr ct1Cap k1Ptr k1Cap Frame
    hfsp_align hpc hrun hsp hx19 hx28 htrace

theorem v9_states_from_pb_drop_uc_8588_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s : State)
    (fsp out rkPtr rkCap mkPtr mkCap ekPtr ekCap ct1Ptr ct1Cap k1Ptr k1Cap : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 8588#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 7084#64) s
      (((fsp + 48#64) ↦₆₄ k1Cap) ∗
        ((fsp + 56#64) ↦₆₄ rkCap) ∗
        ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
        ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
        ((fsp + 136#64) ↦₆₄ mkPtr) ∗
        ((fsp + 144#64) ↦₆₄ ekPtr) ∗
        ((fsp + 152#64) ↦₆₄ ekCap) ∗
        ((fsp + 200#64) ↦₆₄ k1Ptr) ∗
        ((fsp + 216#64) ↦₆₄ mkCap) ∗
        vecCapPtrDealloc A.repAlloc rkCap rkPtr ∗
        vecCapPtrDealloc A.repAlloc mkCap mkPtr ∗
        vecCapPtrDealloc A.repAlloc ekCap ekPtr ∗
        vecCapPtrDealloc A.repAlloc ct1Cap ct1Ptr ∗
        vecCapPtrDealloc A.repAlloc k1Cap k1Ptr ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢ ((fsp + 48#64) ↦₆₄ k1Cap) ∗
            ((fsp + 56#64) ↦₆₄ rkCap) ∗
            ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
            ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
            ((fsp + 136#64) ↦₆₄ mkPtr) ∗
            ((fsp + 144#64) ↦₆₄ ekPtr) ∗
            ((fsp + 152#64) ↦₆₄ ekCap) ∗
            ((fsp + 200#64) ↦₆₄ k1Ptr) ∗
            ((fsp + 216#64) ↦₆₄ mkCap) ∗
            A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v9_Saved7084Preserved s0 sm fsp out) :=
  v9_states_from_pb_drop_uc_8588_of_dealloc_placed
    hA.dealloc st s0 s fsp out rkPtr rkCap mkPtr mkCap ekPtr ekCap ct1Ptr ct1Cap k1Ptr k1Cap Frame
    hfsp_align hpc hrun hsp hx19 hx28 htrace

/-- `VmPreserved`-strengthened early error path `+488 -> +4516 -> +5368` when
    `receivingEk = some d` (`d.ptsNeeded ≠ 576#32`) and `uc = none` (`x8 = noneCap`).
    Sets `x28 = 2#64` (`spqrErrorByte .msgDecode`). -/
theorem v9_states_from_pb_drop_proto_uc_none_488_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out ptsPtr ptsCap x22_val : BitVec 64) (P : SepProp)
    (hpc : s.pc = lsmpl.base 333 + 488#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx8 : s.readReg64 .x8 = noneCap)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = ptsPtr)
    (hx21 : s.readReg64 .x21 = ptsCap)
    (hx22 : s.readReg64 .x22 = x22_val)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 5368#64) s P
      (fun sm Pm =>
        (Pm ⊢ P) ∧
        VmPreserved s sm ∧
        v9_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap 2#64 ∧
        sm.readReg64 .x22 = x22_val) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant9aPlaced.v9_states_from_pb_drop_proto_uc_none_488_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
      fsp out ptsPtr ptsCap x22_val P
      (by simpa using hpc) (by simpa using hrun) (by simpa using hsp)
      (by simpa using hx8) (by simpa using hx19) (by simpa using hx20)
      (by simpa using hx21) (by simpa using hx22)
      ⟨by simpa using htrace.1, by simpa using htrace.2⟩)
    fun sm Pm hvm ⟨hPm, hpres_m, hx22_m⟩ =>
      ⟨hPm, hvm, v9_saved5368Preserved_stripS.mp hpres_m, by simpa using hx22_m⟩

theorem v9_states_from_pb_drop_proto_uc_none_488_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out ptsPtr ptsCap x22_val : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = lsmpl.base 333 + 488#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx8 : s.readReg64 .x8 = noneCap)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = ptsPtr)
    (hx21 : s.readReg64 .x21 = ptsCap)
    (hx22 : s.readReg64 .x22 = x22_val)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 5368#64) s
      (A.pool lim st s ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ A.pool lim st sm ∗ Rest) ∧
        VmPreserved s sm ∧
        v9_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap 2#64 ∧
        sm.readReg64 .x22 = x22_val) := by
  have hwp := v9_states_from_pb_drop_proto_uc_none_488_placed (ext := ext)
    s0 s fsp out ptsPtr ptsCap x22_val (A.pool lim st s ∗ Rest)
    hpc hrun hsp hx8 hx19 hx20 hx21 hx22 htrace
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨hPm, hvm, hrest⟩

/-- `VmPreserved`-strengthened error path `+2768 -> +4372 -> +5360` when `uc = none`
    (`x8 = noneCap`). Sets `x28 = 0#64` (`spqrErrorByte .stateDecode`) and branches to `+5360`. -/
theorem v9_states_from_pb_uc_none_2768_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out ptsPtr ptsCap x22_val : BitVec 64) (P : SepProp)
    (hpc : s.pc = lsmpl.base 333 + 2768#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx8 : s.readReg64 .x8 = noneCap)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = ptsPtr)
    (hx21 : s.readReg64 .x21 = ptsCap)
    (hx22 : s.readReg64 .x22 = x22_val)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 5360#64) s P
      (fun sm Pm =>
        (Pm ⊢ P) ∧
        VmPreserved s sm ∧
        v9_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap 0#64 ∧
        sm.readReg64 .x22 = x22_val) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant9aPlaced.v9_states_from_pb_uc_none_2768_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
      fsp out ptsPtr ptsCap x22_val P
      (by simpa using hpc) (by simpa using hrun) (by simpa using hsp)
      (by simpa using hx8) (by simpa using hx19) (by simpa using hx20)
      (by simpa using hx21) (by simpa using hx22)
      ⟨by simpa using htrace.1, by simpa using htrace.2⟩)
    fun sm Pm hvm ⟨hPm, hpres_m, hx22_m⟩ =>
      ⟨hPm, hvm, v9_saved5368Preserved_stripS.mp hpres_m, by simpa using hx22_m⟩

theorem v9_states_from_pb_uc_none_2768_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out ptsPtr ptsCap x22_val : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = lsmpl.base 333 + 2768#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx8 : s.readReg64 .x8 = noneCap)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = ptsPtr)
    (hx21 : s.readReg64 .x21 = ptsCap)
    (hx22 : s.readReg64 .x22 = x22_val)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 5360#64) s
      (A.pool lim st s ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ A.pool lim st sm ∗ Rest) ∧
        VmPreserved s sm ∧
        v9_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap 0#64 ∧
        sm.readReg64 .x22 = x22_val) := by
  have hwp := v9_states_from_pb_uc_none_2768_placed (ext := ext)
    s0 s fsp out ptsPtr ptsCap x22_val (A.pool lim st s ∗ Rest)
    hpc hrun hsp hx8 hx19 hx20 hx21 hx22 htrace
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨hPm, hvm, hrest⟩

/-- Early error path `+488 -> +496 -> +500 -> +5368` when `receivingEk = some d`
    (`d.ptsNeeded ≠ 576#32`) and `uc = some u` (`hdrCap.toNat < 2^63`).
    Calls Block `286` (`drop_glue::<proto::unchunked::Ct1SentEkReceived>`, ICF-shared with `Ct1Sent`)
    with `x0 = ucA`, sets `x28 = 2#64`, and branches to `+5368`. -/
theorem v9_states_from_pb_drop_proto_uc_some_488_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdrop_cl : subroutine_ok (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 286)
      (withLsCodeLoaded lsmpl (dropProtoUnchunkedCt1SentEkReceivedSpec M A lim)))
    (st : M.σ) (s0 s : State) (fsp out ucA hdrCap ptsPtr ptsCap x22_val : BitVec 64)
    (u : V1State.Unchunked.Ct1Sent) (Frame : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hhdr_lt : hdrCap.toNat < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 488#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = ucA)
    (hx8 : s.readReg64 .x8 = hdrCap)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = ptsPtr)
    (hx21 : s.readReg64 .x21 = ptsCap)
    (hx22 : s.readReg64 .x22 = x22_val)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 5368#64) s
      (protoUnchunkedCt1SentAt A.repAlloc ucA u ∗
        A.pool lim st s ∗ stackAt fsp dropStack32 ∗ Frame)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢ memRegion ucA 128 ∗ A.pool lim (M.stepEvents evs st) sm ∗
            stackAt fsp dropStack32 ∗ Frame) ∧
          v9_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap 2#64 ∧
          sm.readReg64 .x22 = x22_val) := by
  have hhdr_ne := cap_add_one_beq_zero_false hhdr_lt
  refine seq_clean_lscl_st hcl
    (mid := lsmpl.base 286)
    (P_mid := fun sm =>
      protoUnchunkedCt1SentEkReceivedAt A.repAlloc ucA
        { es := u.hdr, ek := u.es, ct1 := u.ct1, auth := u.auth, epoch := u.epoch } ∗
        A.pool lim st sm ∗ stackAt fsp dropStack32 ∗ Frame)
    (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x0 = ucA ∧
      sm.readReg64 .lr = (blkPl_333).base + 500#64 ∧
      sm.readReg64 .x19 = out ∧ sm.readReg64 .x20 = ptsPtr ∧
      sm.readReg64 .x21 = ptsCap ∧ sm.readReg64 .x22 = x22_val ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · change s.pc = (blkPl_333).base + 488#64 at hpc
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsmpl.base 286) s
      (protoUnchunkedCt1SentEkReceivedAt A.repAlloc ucA
        { es := u.hdr, ek := u.es, ct1 := u.ct1, auth := u.auth, epoch := u.epoch } ∗
        A.pool lim st s ∗ stackAt fsp dropStack32 ∗ Frame) _
    wp_steps_sync_333 (lsmpl.base 286)
    try simp only [State.setMem_setMem]
    refine align_pre_st (by (try simp only [wp_norm, arm64_norm]); try sep_ac_rfl) ?_
    wp_done
  · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx0_2, hlr_2, hx19_2, hx20_2, hx21_2, hx22_2, htr2⟩
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := hsp2 ▸ hfsp_align
    have hdrop : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        (lsmpl.base 286) (withMemEq s2.mem (dropProtoUnchunkedCt1SentEkReceivedSpec M A lim)) :=
      withMemEq_of_withLsCodeLoaded hdrop_cl hcl2
    simp only [withMemEq, dropProtoUnchunkedCt1SentEkReceivedSpec,
      protoUnchunkedCt1SentEkReceivedSize] at hdrop
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 5368#64) s2 _ _
    rw [show stackAt fsp dropStack32 = stackAt s2.sp dropStack32 from hsp2 ▸ rfl]
    wp_call hdrop
      ((⟨ucA, { es := u.hdr, ek := u.es, ct1 := u.ct1, auth := u.auth, epoch := u.epoch }⟩ :
        DropProtoUnchunkedCt1SentEkReceivedGhost), st)
    rw [hsp2]
    rw [hlr_2] at *
    have hevs_w : FreeOnlyEvs w := ‹_›
    have hacp_w : AllocCallPreserved s2 sf := by
      simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
    have htr_sf : sf.trace = s0.trace := hacp_w.2.1.trans htr2.1
    have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
      ‹calleeSavedVRegs sf = calleeSavedVRegs s2›.trans htr2.2
    refine SepWP.mono
      (post := fun sm Pm =>
        (Pm ⊢ memRegion ucA 128 ∗ A.pool lim (M.stepEvents w st) sm ∗
          stackAt fsp dropStack32 ∗ Frame) ∧
        v9_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap 2#64 ∧
        sm.readReg64 .x22 = x22_val)
      ?_ (fun _ _ _ _ ⟨hp, hq⟩ => ⟨w, hevs_w, hp, hq⟩)
    wp_steps_sync_333 ((blkPl_333).base + 5368#64)
    try simp only [State.setMem_setMem]
    refine align_pre_st (by (try simp only [wp_norm, arm64_norm, hsp2]); try sep_ac_rfl) ?_
    wp_done

theorem v9_states_from_pb_drop_proto_uc_some_488_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s : State) (fsp out ucA hdrCap ptsPtr ptsCap x22_val : BitVec 64)
    (u : V1State.Unchunked.Ct1Sent) (Frame : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hhdr_lt : hdrCap.toNat < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 488#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = ucA)
    (hx8 : s.readReg64 .x8 = hdrCap)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = ptsPtr)
    (hx21 : s.readReg64 .x21 = ptsCap)
    (hx22 : s.readReg64 .x22 = x22_val)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 5368#64) s
      (protoUnchunkedCt1SentAt A.repAlloc ucA u ∗
        A.pool lim st s ∗ stackAt fsp dropStack32 ∗ Frame)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢ memRegion ucA 128 ∗ A.pool lim (M.stepEvents evs st) sm ∗
            stackAt fsp dropStack32 ∗ Frame) ∧
          v9_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap 2#64 ∧
          sm.readReg64 .x22 = x22_val) :=
  v9_states_from_pb_drop_proto_uc_some_488_of_sub_placed
    (v9_sub_ok_drop_proto_unchunked_ct1_sent_of_dealloc_placed hdealloc)
    st s0 s fsp out ucA hdrCap ptsPtr ptsCap x22_val u Frame
    hcl hfsp_align hhdr_lt hpc hrun hsp hx0 hx8 hx19 hx20 hx21 hx22 htrace

theorem v9_states_from_pb_drop_proto_uc_some_488_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s : State) (fsp out ucA hdrCap ptsPtr ptsCap x22_val : BitVec 64)
    (u : V1State.Unchunked.Ct1Sent) (Frame : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hhdr_lt : hdrCap.toNat < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 488#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = ucA)
    (hx8 : s.readReg64 .x8 = hdrCap)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = ptsPtr)
    (hx21 : s.readReg64 .x21 = ptsCap)
    (hx22 : s.readReg64 .x22 = x22_val)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 5368#64) s
      (protoUnchunkedCt1SentAt A.repAlloc ucA u ∗
        A.pool lim st s ∗ stackAt fsp dropStack32 ∗ Frame)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢ memRegion ucA 128 ∗ A.pool lim (M.stepEvents evs st) sm ∗
            stackAt fsp dropStack32 ∗ Frame) ∧
          v9_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap 2#64 ∧
          sm.readReg64 .x22 = x22_val) :=
  v9_states_from_pb_drop_proto_uc_some_488_of_dealloc_placed
    hA.dealloc st s0 s fsp out ucA hdrCap ptsPtr ptsCap x22_val u Frame
    hcl hfsp_align hhdr_lt hpc hrun hsp hx0 hx8 hx19 hx20 hx21 hx22 htrace

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9aPlacedBudget

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hscPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch1Placed
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Budget Error Exits and Decoder Deallocation (`Variant2hsc`)

Relocatable Block-`333` error exits (`+9224`, `+9228`) and `FreeOnlyEvs` inline
`ProtoPolynomialDecoder` deallocation (`+4428..+4512 -> +9228`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hscPlacedBudgetAux

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalPlacement blkLib_eq_333 blkPC_333 blkPl_333 lsProg_333 lsmpl lsρ)
open CryptoVerification.LibsignalSpqrV1 (Error)
open CryptoVerification.RustHeap (RustAlloc allocHookStack arrayAt vecU8)
open CryptoVerification.SpqrV1.Drop
  (add_24_add_8 cap_mul_24 chunkedStatesSize cons_len_mul header_cells_entails_memRegion_24
   ofNat_add_one_beq_one_false_24 ofNat_beq_zero_false_24 ofNat_succ_eq_add_one
   sep_pull_body sep_push_body sep_rejoin_loop tail_len_mul_lt vecCapPtrDealloc
   vecU8_entails_capPtr_dealloc)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved resultChunkedStatesAt spqrErrorByte statesFromPbSavedCells
   statesFromPbStack v2hsc_Saved4436Preserved v2hsc_bv_add_add_lit)
open CryptoVerification.SpqrV1.Unchunked
  (extractLsb'_0_64_append extractLsb'_64_64_append)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget
   VmPreserved rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (isTotalTrapHooks_withPanics_vmTrapHooks sepWP_lsBlock_vmPreserved
   stripS_calleeSavedVRegs stripS_pc stripS_readReg64 stripS_sp stripS_status stripS_trace
   vmTrapHooks)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
  (FromPbAllocHooksPlacedBudget spqrRustDeallocSym)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
  (align_pre_st deallocFreeOnlySpec sepWP_evs_dealloc sepWP_evs_nil seq_clean_evs seq_clean_st
   subroutine_ok_deallocFreeOnly)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux
  (FromPbAllocHooksBudget blk333_noSvc0 entails_pre_st v1_dealloc_ok_at_statesFromPb_placed
   v1_dealloc_ok_of_dealloc_placed v1_dealloc_ok_of_placedHooks)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget (blk333_safeVm)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm, local wp_norm] v2hsc_bv_add_add_lit

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

/-! ## Block-`333` `__rust_dealloc` Contract Projections -/

theorem v2hsc_sub_ok_dealloc_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim) :=
  v1_dealloc_ok_of_dealloc_placed hdealloc

theorem v2hsc_sub_ok_dealloc_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim) :=
  v1_dealloc_ok_of_placedHooks hA

theorem v2hsc_sub_ok_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim) :=
  v1_dealloc_ok_at_statesFromPb_placed hA

/-! ## Error Exit Tails (`+9228 -> s0.x30` and `+9224 -> s0.x30`) -/

/-- `VmPreserved`-strengthened relocatable error exit tail at `+9228 -> s0.x30` (Block `333`). -/
theorem v2hsc_err_exit_9228_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (err : Error) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9228#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : (s1.readReg64 .x23).extractLsb' 0 8 = spqrErrorByte err)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out (.error (.err err)) ∗
          Rest ∗
          stackAt s0.sp statesFromPbStack) ∧
        VmPreserved s1 sf ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant2hscPlaced.v2hsc_err_exit_9228_placed
      (A := A) (F := F) (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      out err Rest hsp0_align
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1) (by simpa using hx23_1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sf Pf hvm ⟨hPf, hsp_f, hcc_f, htr_f⟩ =>
      ⟨hPf, hvm, hsp_f, hcc_f, htr_f⟩

theorem v2hsc_err_exit_9228_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (err : Error) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9228#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : (s1.readReg64 .x23).extractLsb' 0 8 = spqrErrorByte err)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err err)) ∗
          A.pool lim st sf ∗
          Rest ∗
          stackAt s0.sp statesFromPbStack) ∧
        VmPreserved s1 sf ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hwp := v2hsc_err_exit_9228_placed (A := A.repAlloc) (F := F) (ext := ext)
    s0 s1 out err (A.pool lim st s1 ∗ Rest)
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx23_1 htr1
  refine SepWP.mono hwp fun sf Pf _ _ ⟨hPf, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPf
  exact ⟨Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hvm, hrest⟩

/-- `VmPreserved`-strengthened relocatable error exit tail at `+9224 -> s0.x30` (Block `333`). -/
theorem v2hsc_err_exit_9224_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (err : Error) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9224#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : (s1.readReg64 .x23).extractLsb' 0 8 = spqrErrorByte err)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out (.error (.err err)) ∗
          Rest ∗
          stackAt s0.sp statesFromPbStack) ∧
        VmPreserved s1 sf ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant2hscPlaced.v2hsc_err_exit_9224_placed
      (A := A) (F := F) (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      out err Rest hsp0_align
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1) (by simpa using hx23_1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sf Pf hvm ⟨hPf, hsp_f, hcc_f, htr_f⟩ =>
      ⟨hPf, hvm, hsp_f, hcc_f, htr_f⟩

theorem v2hsc_err_exit_9224_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (err : Error) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9224#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : (s1.readReg64 .x23).extractLsb' 0 8 = spqrErrorByte err)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err err)) ∗
          A.pool lim st sf ∗
          Rest ∗
          stackAt s0.sp statesFromPbStack) ∧
        VmPreserved s1 sf ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hwp := v2hsc_err_exit_9224_placed (A := A.repAlloc) (F := F) (ext := ext)
    s0 s1 out err (A.pool lim st s1 ∗ Rest)
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx23_1 htr1
  refine SepWP.mono hwp fun sf Pf _ _ ⟨hPf, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPf
  exact ⟨Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hvm, hrest⟩

/-! ## Shared `ProtoPolynomialDecoder` Deallocation (`+4428..+4512 -> +9228`) -/

theorem v2hsc_proto_decoder_dealloc_body_4460_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (fsp out ptsPtr ptsCap x23_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (st : M.σ) (s : State) (Frame : SepProp),
      s.pc = (blkPl_333).base + 4460#64 →
      s.status = .Running →
      v2hsc_Saved4436Preserved s0 s fsp out ptsPtr ptsCap x23_val →
      s.readReg64 .x21 = cnt →
      s.readReg64 .x24 = cur + 8#64 →
      SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 4448#64) s
        (vecU8 A.repAlloc cur bs ∗ A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evs, FreeOnlyEvs evs ∧
          (Pm ⊢ memRegion cur 24 ∗ A.pool lim (M.stepEvents evs st) sm ∗
            stackAt fsp allocHookStack ∗ Frame) ∧
          v2hsc_Saved4436Preserved s0 sm fsp out ptsPtr ptsCap x23_val ∧
          sm.readReg64 .x21 = cnt ∧
          sm.readReg64 .x24 = cur + 8#64) := by
  have hdealloc_fo : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (deallocFreeOnlySpec M A lim) :=
    subroutine_ok_deallocFreeOnly hdealloc_ok
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  intro cur cnt bs st s Frame hpc hrun hpres hx21 hx24
  rcases hpres with ⟨hsp, hx19, hx20, hx22, hx23, htr, hvregs⟩
  refine SepWP.weaken_pre (sepConj_mono_left (vecU8_entails_capPtr_dealloc A.repAlloc cur bs)) ?_
  apply CryptoVerification.SpqrV1.Drop.SepWP.exists_sepConj_left; intro cap
  apply CryptoVerification.SpqrV1.Drop.SepWP.exists_sepConj_left; intro vptr
  have hpost24 (Pool : SepProp) :
      ((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
        Pool ∗ stackAt fsp allocHookStack ∗ Frame ⊢
      memRegion cur 24 ∗ Pool ∗ stackAt fsp allocHookStack ∗ Frame :=
    sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)
  dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live,
    BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc ⊢
  by_cases hcap : (cap == 0#64) = true <;>
    simp only [hcap, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · apply sepWP_evs_nil
    simp only [M.stepEvents_nil]
    wp_steps_sync_333 ((blkPl_333).base + 4448#64)
    simp only [State.setMem_setMem]
    refine entails_pre_st ?_ ?_
    · intro sc hsc
      rw [← hsc]
      exact Entails.trans (Entails.of_eq (by sep_ac_rfl)) (hpost24 (A.pool lim st sc))
    · wp_done
  · apply sepWP_evs_dealloc cap.toNat 1
    wp_steps_sync_333 (lsρ spqrRustDeallocSym)
    simp only [State.setMem_setMem]
    wp_call hdealloc_fo (vptr, cap.toNat, 1, st)
    have hacp : AllocCallPreserved s sf := by
      simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
    have hsp_sf : sf.sp = fsp := ‹sf.sp = _›.trans (by simp [wp_norm, arm64_norm, hsp])
    have htr_sf : sf.trace = s0.trace := hacp.2.1.trans htr
    have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
      ‹calleeSavedVRegs sf = _›.trans hvregs
    wp_steps_sync_333 ((blkPl_333).base + 4448#64)
    simp only [State.setMem_setMem]
    refine entails_pre_st ?_ ?_
    · intro sc hsc
      rw [← hsc]
      simp only [wp_norm, arm64_norm, hsp]
      exact Entails.trans (Entails.of_eq (by sep_ac_rfl))
        (hpost24 (A.pool lim (M.stepEvents (rustDeallocEvents cap.toNat 1) st) sc))
    · wp_done

theorem v2hsc_proto_decoder_dealloc_body_4460_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 : State) (fsp out ptsPtr ptsCap x23_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (st : M.σ) (s : State) (Frame : SepProp),
      s.pc = (blkPl_333).base + 4460#64 →
      s.status = .Running →
      v2hsc_Saved4436Preserved s0 s fsp out ptsPtr ptsCap x23_val →
      s.readReg64 .x21 = cnt →
      s.readReg64 .x24 = cur + 8#64 →
      SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 4448#64) s
        (vecU8 A.repAlloc cur bs ∗ A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evs, FreeOnlyEvs evs ∧
          (Pm ⊢ memRegion cur 24 ∗ A.pool lim (M.stepEvents evs st) sm ∗
            stackAt fsp allocHookStack ∗ Frame) ∧
          v2hsc_Saved4436Preserved s0 sm fsp out ptsPtr ptsCap x23_val ∧
          sm.readReg64 .x21 = cnt ∧
          sm.readReg64 .x24 = cur + 8#64) :=
  v2hsc_proto_decoder_dealloc_body_4460_of_sub_placed
    (v2hsc_sub_ok_dealloc_placed hA) s0 fsp out ptsPtr ptsCap x23_val hfsp_align

theorem v2hsc_proto_decoder_dealloc_loop_4460_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (fsp out ptsPtr ptsCap x23_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (st : M.σ) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = (blkPl_333).base + 4460#64 →
      s.status = .Running →
      v2hsc_Saved4436Preserved s0 s fsp out ptsPtr ptsCap x23_val →
      s.readReg64 .x21 = BitVec.ofNat 64 rest.length →
      s.readReg64 .x24 = cur + 8#64 →
      SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 4484#64) s
        (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 cur rest ∗
          A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evs, FreeOnlyEvs evs ∧
          (Pm ⊢ memRegion cur (rest.length * 24) ∗
            A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v2hsc_Saved4436Preserved s0 sm fsp out ptsPtr ptsCap x23_val) := by
  have hbody := v2hsc_proto_decoder_dealloc_body_4460_of_sub_placed
    hdealloc_ok s0 fsp out ptsPtr ptsCap x23_val hfsp_align
  intro rest
  induction rest with
  | nil => intro _ _ _ _ hne; exact absurd rfl hne
  | cons bs tl ih =>
    intro cur st s Frame _ hlen hpc hrun hpres hx21 hx24
    simp only [arrayAt, BitVec.ofNat_eq_ofNat]; rw [sep_pull_body]
    refine seq_clean_evs
      (hbody cur (BitVec.ofNat 64 (bs :: tl).length) bs st s _ hpc hrun hpres hx21 hx24) ?_
    intro evs1 s1 hevs1 hpc1 hrun1 ⟨hpres1, hx21_1, hx24_1⟩
    rcases tl with _ | ⟨bs2, tl2⟩
    · simp only [List.length_singleton, arrayAt, sepConj_emp, emp_sepConj, Nat.one_mul] at hx21_1 ⊢
      rcases hpres1 with ⟨hsp_1, hx19_1, hx20_1, hx22_1, hx23_1, htr_1, hvregs_1⟩
      refine SepWP.mono
        (post := fun sm Pm =>
          (Pm ⊢ memRegion cur 24 ∗ A.pool lim (M.stepEvents evs1 st) sm ∗
            stackAt fsp allocHookStack ∗ Frame) ∧
          v2hsc_Saved4436Preserved s0 sm fsp out ptsPtr ptsCap x23_val)
        ?_ (fun _ _ _ _ ⟨hp, hq⟩ => ⟨evs1, hevs1, hp, hq⟩)
      wp_steps_sync_333 ((blkPl_333).base + 4484#64)
      simp only [State.setMem_setMem]
      refine align_pre_st (by sep_ac_rfl) ?_
      wp_done
    · have hlen_tl : (bs2 :: tl2).length * 24 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_add_one_beq_one_false_24 (n := (bs2 :: tl2).length) (by simp) hlen_tl
      rw [List.length_cons, ofNat_succ_eq_add_one] at hx21_1
      refine seq_clean_st (mid := (blkPl_333).base + 4460#64)
        (P_mid := fun sm =>
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (cur + 24#64) (bs2 :: tl2) ∗
          A.pool lim (M.stepEvents evs1 st) sm ∗ stackAt fsp allocHookStack ∗
          (memRegion cur 24 ∗ Frame))
        (Q := fun sm => v2hsc_Saved4436Preserved s0 sm fsp out ptsPtr ptsCap x23_val ∧
          sm.readReg64 .x21 = BitVec.ofNat 64 (bs2 :: tl2).length ∧
          sm.readReg64 .x24 = (cur + 24#64) + 8#64)
        ?_ ?_
      · rcases hpres1 with ⟨hsp_1, hx19_1, hx20_1, hx22_1, hx23_1, htr_1, hvregs_1⟩
        rw [sep_push_body]
        wp_steps_sync_333 ((blkPl_333).base + 4460#64)
        simp only [State.setMem_setMem]
        refine align_pre_st (by sep_ac_rfl) ?_
        rw [add_24_add_8]
        wp_done
      · intro s2 hpc2 hrun2 ⟨hpres2, hx21_2, hx24_2⟩
        have hrec := ih (cur + 24#64) (M.stepEvents evs1 st) s2 (memRegion cur 24 ∗ Frame)
          (List.cons_ne_nil _ _) hlen_tl hpc2 hrun2 hpres2 hx21_2 hx24_2
        refine SepWP.mono hrec fun sf _Pf _ _ ⟨evs2, hevs2, hp, hpres_f⟩ => ?_
        refine ⟨evs1 ++ evs2, hevs1.append hevs2, ?_, hpres_f⟩
        rw [M.stepEvents_append]
        have hsplit := cons_len_mul bs (bs2 :: tl2) 24
        have hbound : 24 + (bs2 :: tl2).length * 24 ≤ 2 ^ 64 := by
          rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
        refine Entails.trans hp ?_
        rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 24 ((bs2 :: tl2).length * 24) hbound]
        exact Entails.refl _

theorem v2hsc_proto_decoder_dealloc_loop_4460_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 : State) (fsp out ptsPtr ptsCap x23_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (st : M.σ) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = (blkPl_333).base + 4460#64 →
      s.status = .Running →
      v2hsc_Saved4436Preserved s0 s fsp out ptsPtr ptsCap x23_val →
      s.readReg64 .x21 = BitVec.ofNat 64 rest.length →
      s.readReg64 .x24 = cur + 8#64 →
      SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 4484#64) s
        (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 cur rest ∗
          A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evs, FreeOnlyEvs evs ∧
          (Pm ⊢ memRegion cur (rest.length * 24) ∗
            A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v2hsc_Saved4436Preserved s0 sm fsp out ptsPtr ptsCap x23_val) :=
  v2hsc_proto_decoder_dealloc_loop_4460_of_sub_placed
    (v2hsc_sub_ok_dealloc_placed hA) s0 fsp out ptsPtr ptsCap x23_val hfsp_align

/-- `ProtoPolynomialDecoder` inline deallocation (`+4436 -> +4484`) under an explicit
    Block-`333` `__rust_dealloc` contract. -/
theorem v2hsc_dealloc_proto_decoder_4436_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (s0 s : State) (fsp out ptsPtr ptsCap x23_val : BitVec 64)
    (pts : List (List (BitVec 8))) (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 4436#64)
    (hrun : s.status = .Running)
    (hpres : v2hsc_Saved4436Preserved s0 s fsp out ptsPtr ptsCap x23_val)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 pts.length) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4484#64) s
      ((if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ (if ptsCap = 0#64 then emp
          else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗ memRegion ptsPtr (ptsCap.toNat * 24)) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v2hsc_Saved4436Preserved s0 sm fsp out ptsPtr ptsCap x23_val) := by
  have hloop := v2hsc_proto_decoder_dealloc_loop_4460_of_sub_placed
    hdealloc_ok s0 fsp out ptsPtr ptsCap x23_val hfsp_align
  change s.pc = (blkPl_333).base + 4436#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 4484#64) s _ _
  cases pts with
  | nil =>
    rcases hpres with ⟨hsp, hx19, hx20, hx22, hx23, htr, hvregs⟩
    simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat,
      BitVec.add_zero, arrayAt, emp_sepConj] at hx21 ⊢
    apply sepWP_evs_nil
    simp only [M.stepEvents_nil]
    wp_steps_sync_333 ((blkPl_333).base + 4484#64)
    simp only [State.setMem_setMem]
    refine align_pre_st (by sep_ac_rfl) ?_
    wp_done
  | cons bs tl =>
    have hlen_pos : 0 < (bs :: tl).length := by simp
    have hlen_lt : (bs :: tl).length * 24 < 2 ^ 63 := by
      have : (bs :: tl).length * 24 ≤ ptsCap.toNat * 24 := Nat.mul_le_mul_right 24 hpts_le
      omega
    have hne0 := ofNat_beq_zero_false_24 hlen_pos hlen_lt
    have hcap_ne : ptsCap ≠ 0#64 := by intro hc0; rw [hc0] at hpts_le; simp at hpts_le
    simp only [BitVec.ofNat_eq_ofNat, hcap_ne, ↓reduceIte]
    refine seq_clean_st (mid := (blkPl_333).base + 4460#64)
      (P_mid := fun sm =>
        arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr (bs :: tl) ∗
        A.pool lim st sm ∗ stackAt fsp allocHookStack ∗
        (A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
         memRegion (ptsPtr + BitVec.ofNat 64 ((bs :: tl).length * 24))
           ((ptsCap.toNat - (bs :: tl).length) * 24) ∗
         Frame))
      (Q := fun sm => v2hsc_Saved4436Preserved s0 sm fsp out ptsPtr ptsCap x23_val ∧
        sm.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧
        sm.readReg64 .x24 = ptsPtr + 8#64)
      ?_ ?_
    · rcases hpres with ⟨hsp, hx19, hx20, hx22, hx23, htr, hvregs⟩
      wp_steps_sync_333 ((blkPl_333).base + 4460#64)
      simp only [State.setMem_setMem]
      refine align_pre_st (by sep_ac_rfl) ?_
      wp_done
    · intro s_loop hpc_loop hrun_loop ⟨hpres_loop, hx21_loop, hx24_loop⟩
      have hsplit : ptsCap.toNat * 24 =
          (bs :: tl).length * 24 + (ptsCap.toNat - (bs :: tl).length) * 24 := by
        rw [← Nat.add_mul]; congr 1; omega
      have hbound : (bs :: tl).length * 24 + (ptsCap.toNat - (bs :: tl).length) * 24 ≤ 2 ^ 64 := by
        rw [← hsplit]; omega
      have hjoin : A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          memRegion ptsPtr ((bs :: tl).length * 24) ∗
          memRegion (ptsPtr + BitVec.ofNat 64 ((bs :: tl).length * 24))
            ((ptsCap.toNat - (bs :: tl).length) * 24) ⊢
          A.live ptsPtr (ptsCap.toNat * 24) 8 ∗ memRegion ptsPtr (ptsCap.toNat * 24) := by
        rw [hsplit, ProofLib.memRegion_split ptsPtr ((bs :: tl).length * 24)
          ((ptsCap.toNat - (bs :: tl).length) * 24) hbound]
        exact Entails.of_eq (by sep_ac_rfl)
      refine SepWP.mono
        (hloop (bs :: tl) ptsPtr st s_loop _
          (List.cons_ne_nil _ _) hlen_lt hpc_loop hrun_loop hpres_loop
          hx21_loop hx24_loop)
        fun sm _Pm _ _ ⟨evs, hevs, hPm, hpres_m⟩ => ?_
      refine ⟨evs, hevs, Entails.trans hPm ?_, hpres_m⟩
      refine Entails.trans
        (Entails.of_eq (show _ =
          (A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
           memRegion ptsPtr ((bs :: tl).length * 24) ∗
           memRegion (ptsPtr + BitVec.ofNat 64 ((bs :: tl).length * 24))
             ((ptsCap.toNat - (bs :: tl).length) * 24)) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame by sep_ac_rfl))
        (sepConj_mono_left hjoin)

theorem v2hsc_dealloc_proto_decoder_4436_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 s : State) (fsp out ptsPtr ptsCap x23_val : BitVec 64)
    (pts : List (List (BitVec 8))) (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 4436#64)
    (hrun : s.status = .Running)
    (hpres : v2hsc_Saved4436Preserved s0 s fsp out ptsPtr ptsCap x23_val)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 pts.length) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4484#64) s
      ((if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ (if ptsCap = 0#64 then emp
          else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗ memRegion ptsPtr (ptsCap.toNat * 24)) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v2hsc_Saved4436Preserved s0 sm fsp out ptsPtr ptsCap x23_val) :=
  v2hsc_dealloc_proto_decoder_4436_of_sub_placed
    (v2hsc_sub_ok_dealloc_placed hA) s0 s fsp out ptsPtr ptsCap x23_val pts st Frame
    hfsp_align hpts_le hpts_cap_lt hpc hrun hpres hx21

/-- `ProtoPolynomialDecoder` inline deallocation (`+4484 -> +9228`) under an explicit
    Block-`333` `__rust_dealloc` contract. -/
theorem v2hsc_dealloc_proto_decoder_4484_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (s0 s : State) (fsp out ptsPtr ptsCap x23_val w232 : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 4484#64)
    (hrun : s.status = .Running)
    (hpres : v2hsc_Saved4436Preserved s0 s fsp out ptsPtr ptsCap x23_val) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9228#64) s
      ((if ptsCap = 0#64 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗ memRegion ptsPtr (ptsCap.toNat * 24)) ∗
        ((fsp + 232#64) ↦₆₄ w232) ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ ((fsp + 232#64) ↦₆₄ w232) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v2hsc_Saved4436Preserved s0 sm fsp out ptsPtr ptsCap x23_val) := by
  have hdealloc_fo : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (deallocFreeOnlySpec M A lim) :=
    subroutine_ok_deallocFreeOnly hdealloc_ok
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  change s.pc = (blkPl_333).base + 4484#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 9228#64) s _ _
  rcases hpres with ⟨hsp, hx19, hx20, hx22, hx23, htr, hvregs⟩
  by_cases hc : ptsCap = 0#64
  · have hc_beq : (ptsCap == 0#64) = true := by rw [beq_iff_eq]; exact hc
    simp only [hc, ↓reduceIte, emp_sepConj, sepConj_emp] at hx22 ⊢
    apply sepWP_evs_nil
    simp only [M.stepEvents_nil]
    wp_steps_sync_333 ((blkPl_333).base + 9228#64)
    simp only [State.setMem_setMem]
    refine align_pre_st (by sep_ac_rfl) ?_
    wp_done
  · have hc_beq : ¬((ptsCap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
    have hlsl := cap_mul_24 hpts_cap_lt
    simp only [hc, ↓reduceIte]
    apply sepWP_evs_dealloc (ptsCap.toNat * 24) 8
    wp_steps_sync_333 (lsρ spqrRustDeallocSym)
    simp only [State.setMem_setMem]
    wp_call hdealloc_fo (ptsPtr, ptsCap.toNat * 24, 8, st)
    have hacp : AllocCallPreserved s sf := by
      simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
    have hsp_sf : sf.sp = fsp := ‹sf.sp = _›.trans (by simp [wp_norm, arm64_norm, hsp])
    have htr_sf : sf.trace = s0.trace := hacp.2.1.trans htr
    have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
      ‹calleeSavedVRegs sf = _›.trans hvregs
    wp_steps_sync_333 ((blkPl_333).base + 9228#64)
    simp only [State.setMem_setMem]
    refine entails_pre_st ?_ ?_
    · intro sc hsc
      rw [← hsc]
      simp only [wp_norm, arm64_norm, hsp]
      exact Entails.of_eq (by sep_ac_rfl)
    · wp_done

theorem v2hsc_dealloc_proto_decoder_4484_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 s : State) (fsp out ptsPtr ptsCap x23_val w232 : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 4484#64)
    (hrun : s.status = .Running)
    (hpres : v2hsc_Saved4436Preserved s0 s fsp out ptsPtr ptsCap x23_val) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9228#64) s
      ((if ptsCap = 0#64 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗ memRegion ptsPtr (ptsCap.toNat * 24)) ∗
        ((fsp + 232#64) ↦₆₄ w232) ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ ((fsp + 232#64) ↦₆₄ w232) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v2hsc_Saved4436Preserved s0 sm fsp out ptsPtr ptsCap x23_val) :=
  v2hsc_dealloc_proto_decoder_4484_of_sub_placed
    (v2hsc_sub_ok_dealloc_placed hA) s0 s fsp out ptsPtr ptsCap x23_val w232 st Frame
    hfsp_align hpts_cap_lt hpc hrun hpres

/-- Shared `Option<ProtoPolynomialDecoder>::Some` inline deallocation at `+4428 -> +9228` under
    an explicit Block-`333` `__rust_dealloc` contract. -/
theorem v2hsc_dealloc_some_proto_decoder_4428_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (s0 s : State) (fsp out ptsPtr ptsCap x23_val w232 : BitVec 64)
    (pts : List (List (BitVec 8))) (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 4428#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx22 : s.readReg64 .x22 = ptsCap)
    (hx23 : s.readReg64 .x23 = x23_val)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9228#64) s
      (((fsp + 232#64) ↦₆₄ w232) ∗
        ((fsp + 1040#64) ↦₆₄ ptsPtr) ∗
        ((fsp + 1048#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
        (if ptsCap = 0 then emp
         else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pts ∗
           memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
             ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ ((fsp + 232#64) ↦₆₄ w232) ∗
          ((fsp + 1040#64) ↦₆₄ ptsPtr) ∗
          ((fsp + 1048#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x23 = x23_val ∧
        TraceCalleeSaved sm s0) := by
  have h4436 := v2hsc_dealloc_proto_decoder_4436_of_sub_placed hdealloc_ok s0
  have h4484 := v2hsc_dealloc_proto_decoder_4484_of_sub_placed hdealloc_ok s0
  refine seq_clean_st (mid := lsmpl.base 333 + 4436#64)
    (P_mid := fun sm =>
      (if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool lim st sm ∗ stackAt fsp allocHookStack ∗
        (((fsp + 232#64) ↦₆₄ w232) ∗
         ((fsp + 1040#64) ↦₆₄ ptsPtr) ∗
         ((fsp + 1048#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗ Frame))
    (Q := fun sm => v2hsc_Saved4436Preserved s0 sm fsp out ptsPtr ptsCap x23_val ∧
      sm.readReg64 .x21 = BitVec.ofNat 64 pts.length)
    ?_ ?_
  · rcases htrace with ⟨htr, hvregs⟩
    change s.pc = (blkPl_333).base + 4428#64 at hpc
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 4436#64) s _ _
    wp_steps_sync_333 ((blkPl_333).base + 4436#64)
    simp only [State.setMem_setMem]
    refine align_pre_st (by sep_ac_rfl) ?_
    wp_done
  · intro s1 hpc1 hrun1 ⟨hpres1, hx21_1⟩
    have h1 := h4436 s1 fsp out ptsPtr ptsCap x23_val pts st
      (((fsp + 232#64) ↦₆₄ w232) ∗
       ((fsp + 1040#64) ↦₆₄ ptsPtr) ∗
       ((fsp + 1048#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗ Frame)
      hfsp_align hpts_le hpts_cap_lt hpc1 hrun1 hpres1 hx21_1
    refine seq_clean_evs
      (P_evs := fun evs1 sm =>
        (if ptsCap = 0#64 then emp
          else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗ memRegion ptsPtr (ptsCap.toNat * 24)) ∗
          ((fsp + 232#64) ↦₆₄ w232) ∗
          A.pool lim (M.stepEvents evs1 st) sm ∗ stackAt fsp allocHookStack ∗
          (((fsp + 1040#64) ↦₆₄ ptsPtr) ∗
           ((fsp + 1048#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗ Frame))
      (Q := fun sm => v2hsc_Saved4436Preserved s0 sm fsp out ptsPtr ptsCap x23_val)
      (SepWP.mono h1 fun sm _Pm _ _ ⟨evs1, hevs1, hPm, hpres_m⟩ =>
        ⟨evs1, hevs1, Entails.trans hPm (Entails.of_eq (by sep_ac_rfl)), hpres_m⟩) ?_
    intro evs1 s2 hevs1 hpc2 hrun2 hpres2
    have h2 := h4484 s2 fsp out ptsPtr ptsCap x23_val w232 (M.stepEvents evs1 st)
      (((fsp + 1040#64) ↦₆₄ ptsPtr) ∗
       ((fsp + 1048#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗ Frame)
      hfsp_align hpts_cap_lt hpc2 hrun2 hpres2
    refine SepWP.mono h2 fun sm _Pm _ _ ⟨evs2, hevs2, hPm, hsp_m, hx19_m, _, _, hx23_m, htr_m⟩ => ?_
    refine ⟨evs1 ++ evs2, hevs1.append hevs2, ?_, hsp_m, hx19_m, hx23_m, htr_m⟩
    rw [M.stepEvents_append]
    exact Entails.trans hPm (Entails.of_eq (by sep_ac_rfl))

theorem v2hsc_dealloc_some_proto_decoder_4428_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (s0 s : State) (fsp out ptsPtr ptsCap x23_val w232 : BitVec 64)
    (pts : List (List (BitVec 8))) (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 4428#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx22 : s.readReg64 .x22 = ptsCap)
    (hx23 : s.readReg64 .x23 = x23_val)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9228#64) s
      (((fsp + 232#64) ↦₆₄ w232) ∗
        ((fsp + 1040#64) ↦₆₄ ptsPtr) ∗
        ((fsp + 1048#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
        (if ptsCap = 0 then emp
         else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pts ∗
           memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
             ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ ((fsp + 232#64) ↦₆₄ w232) ∗
          ((fsp + 1040#64) ↦₆₄ ptsPtr) ∗
          ((fsp + 1048#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x23 = x23_val ∧
        TraceCalleeSaved sm s0) :=
  v2hsc_dealloc_some_proto_decoder_4428_of_sub_placed
    (v2hsc_sub_ok_dealloc_of_dealloc_placed hdealloc) s0 s fsp out ptsPtr ptsCap x23_val w232
    pts st Frame hfsp_align hpts_le hpts_cap_lt hpc hrun hsp hx19 hx22 hx23 htrace

theorem v2hsc_dealloc_some_proto_decoder_4428_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 s : State) (fsp out ptsPtr ptsCap x23_val w232 : BitVec 64)
    (pts : List (List (BitVec 8))) (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 4428#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx22 : s.readReg64 .x22 = ptsCap)
    (hx23 : s.readReg64 .x23 = x23_val)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9228#64) s
      (((fsp + 232#64) ↦₆₄ w232) ∗
        ((fsp + 1040#64) ↦₆₄ ptsPtr) ∗
        ((fsp + 1048#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
        (if ptsCap = 0 then emp
         else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pts ∗
           memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
             ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ ((fsp + 232#64) ↦₆₄ w232) ∗
          ((fsp + 1040#64) ↦₆₄ ptsPtr) ∗
          ((fsp + 1048#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x23 = x23_val ∧
        TraceCalleeSaved sm s0) :=
  v2hsc_dealloc_some_proto_decoder_4428_of_sub_placed
    (v2hsc_sub_ok_dealloc_of_placedHooks hA) s0 s fsp out ptsPtr ptsCap x23_val w232
    pts st Frame hfsp_align hpts_le hpts_cap_lt hpc hrun hsp hx19 hx22 hx23 htrace

theorem v2hsc_dealloc_some_proto_decoder_4428_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 s : State) (fsp out ptsPtr ptsCap x23_val w232 : BitVec 64)
    (pts : List (List (BitVec 8))) (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 4428#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx22 : s.readReg64 .x22 = ptsCap)
    (hx23 : s.readReg64 .x23 = x23_val)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9228#64) s
      (((fsp + 232#64) ↦₆₄ w232) ∗
        ((fsp + 1040#64) ↦₆₄ ptsPtr) ∗
        ((fsp + 1048#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
        (if ptsCap = 0 then emp
         else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pts ∗
           memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
             ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ ((fsp + 232#64) ↦₆₄ w232) ∗
          ((fsp + 1040#64) ↦₆₄ ptsPtr) ∗
          ((fsp + 1048#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x23 = x23_val ∧
        TraceCalleeSaved sm s0) :=
  v2hsc_dealloc_some_proto_decoder_4428_of_sub_placed
    (v2hsc_sub_ok_dealloc_placed hA) s0 s fsp out ptsPtr ptsCap x23_val w232
    pts st Frame hfsp_align hpts_le hpts_cap_lt hpc hrun hsp hx19 hx22 hx23 htrace

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hscPlacedBudgetAux

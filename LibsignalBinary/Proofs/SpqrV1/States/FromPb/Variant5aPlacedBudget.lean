/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5aPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch2Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch3Placed
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Budget-Threaded Variant 5 (`NoHeaderReceived`) — Part A

Relocatable Block-`333` OOM cold path (`+11596`), `+6500` error exit, and `FreeOnlyEvs` inline
`ProtoPolynomialDecoder` deallocation (`+6420..+6500`) under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5aPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkLib_eq_333 blkPC_333 blkPl_333
   lsProg_333 lsmpl lsρ withLsCodeLoaded withMemEq)
open CryptoVerification.LibsignalSpqrV1 (Error)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap
  (RustAlloc allocFailedEvent allocFailedIn allocHookStack arrayAt vecU8)
open CryptoVerification.SpqrV1.Alloc (spqrHandleErrorSym spqr_externAt?_of_mem)
open CryptoVerification.SpqrV1.Drop
  (add_24_add_8 cap_mul_24 chunkedStatesSize cons_len_mul header_cells_entails_memRegion_24
   none2Cap_add_two_beq_zero noneCap_add_two_beq_zero ofNat_add_one_beq_one_false_24
   ofNat_beq_zero_false_24 ofNat_succ_eq_add_one sep_pull_body sep_push_body sep_rejoin_loop
   tail_len_mul_lt vecCapPtrDealloc vecU8_entails_capPtr_dealloc)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved resultChunkedStatesAt spqrErrorByte statesFromPbOnPanic
   statesFromPbSavedCells statesFromPbStack v5a_Saved6428Preserved v5a_ptsCap_add_one_ne_zero)
open CryptoVerification.SpqrV1.Unchunked (extractLsb'_0_64_append extractLsb'_64_64_append)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget
   VmPreserved rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (isTotalTrapHooks_withPanics_vmTrapHooks sepWP_lsBlock_vmPreserved
   stripS_calleeSavedVRegs stripS_pc stripS_readReg64 stripS_sp stripS_status stripS_trace
   vmTrapHooks)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
  (FromPbAllocHooksPlacedBudget spqrRustDeallocSym)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
  (align_pre_st deallocFreeOnlySpec sepWP_evs_dealloc sepWP_evs_nil
   seq_clean_evs seq_clean_st subroutine_ok_deallocFreeOnly)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
  (FromPbAllocHooksBudget v1_dealloc_ok_at_statesFromPb_placed v1_dealloc_ok_of_dealloc_placed
   v1_dealloc_ok_of_placedHooks withMemEq_of_withLsCodeLoaded)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget (blk333_safeVm)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

/-! ## Relocatable Budget Callee Contracts & OOM Cold Path (`v5a_*_placed`) -/

theorem v5a_sub_ok_dealloc_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim) :=
  v1_dealloc_ok_of_dealloc_placed hdealloc

theorem v5a_sub_ok_dealloc_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim) :=
  v1_dealloc_ok_of_placedHooks hA

theorem v5a_sub_ok_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim) :=
  v1_dealloc_ok_at_statesFromPb_placed hA

theorem v5a_sub_ok_deallocFreeOnly_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (deallocFreeOnlySpec M A lim) :=
  subroutine_ok_deallocFreeOnly (v5a_sub_ok_dealloc_placed hA)

theorem v5a_sub_ok_decoder_from_pb_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 376)
      (withLsCodeLoaded lsmpl (DefsBudget.decoderFromPbSpec M A lim)) :=
  hdec

theorem v5a_sub_ok_decoder_from_pb_mem_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {m : Memory}
    (hdec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (hcl : LibsignalCodeLoaded lsmpl m) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsmpl.base 376)
      (withMemEq m (DefsBudget.decoderFromPbSpec M A lim)) :=
  withMemEq_of_withLsCodeLoaded hdec hcl

private theorem allocFailedIn_and_prefix_of_eq {s0 sf : State}
    (h : sf.trace = s0.trace ++ [allocFailedEvent]) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  unfold allocFailedIn
  rw [h]
  exact ⟨by simp, List.prefix_append _ _⟩

/-- Shared OOM cold path at `+11596` (`mov w0, #1; mov x1, x27; bl handle_error`)
    under an explicit `handle_error` panic hook hypothesis. -/
theorem v5a_states_from_pb_oom_11596_of_panic_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hpanic_ok : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (s0 s : State) (target_pc : BitVec 64) (P R : SepProp)
    (Q : State → SepProp → Prop)
    (hpc : s.pc = lsmpl.base 333 + 11596#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) target_pc s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) := by
  have hpanic :
      ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)).externAt?
        (lsρ spqrHandleErrorSym) = some Rust.panicked :=
    Eq.trans spqr_externAt?_of_mem hpanic_ok
  change s.pc = (blkPl_333).base + 11596#64 at hpc
  change SepWPp ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)) target_pc s P Q _
  apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
  unfold statesFromPbOnPanic
  exact Satisfies.mono
    (sepConj_mono_left (Entails.pure_right
      (allocFailedIn_and_prefix_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *]))
      (entails_anyHeap _))) hm

theorem v5a_states_from_pb_oom_11596_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 s : State) (target_pc : BitVec 64) (P R : SepProp)
    (Q : State → SepProp → Prop)
    (hpc : s.pc = lsmpl.base 333 + 11596#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) target_pc s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) :=
  v5a_states_from_pb_oom_11596_of_panic_placed hA.panic_ok s0 s target_pc P R Q hpc hrun htr

theorem v5a_states_from_pb_oom_11596_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 s : State) (target_pc : BitVec 64) (P R : SepProp)
    (Q : State → SepProp → Prop)
    (hpc : s.pc = lsmpl.base 333 + 11596#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) target_pc s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) :=
  v5a_states_from_pb_oom_11596_of_panic_placed hA.panic_ok s0 s target_pc P R Q hpc hrun htr

/-! ## Shared Error Exit at `+6500` (`+6500 -> +60 -> s0.x30`) -/

/-- `VmPreserved`-strengthened shared `Err(err)` exit at `+6500` (`+6500 -> +60 -> s0.x30`). -/
theorem v5a_states_from_pb_err_6500_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (err : Error) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 6500#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : (s1.readReg64 .x27).extractLsb' 0 8 = spqrErrorByte err)
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
    (Variant5aPlaced.v5a_states_from_pb_err_6500_placed
      (A := A) (F := F) (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      out err Rest hsp0_align
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1) (by simpa using hx27_1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sf Pf hvm ⟨hPf, hsp_f, hcc_f, htr_f⟩ =>
      ⟨hPf, hvm, hsp_f, hcc_f, htr_f⟩

theorem v5a_states_from_pb_err_6500_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (err : Error) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 6500#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : (s1.readReg64 .x27).extractLsb' 0 8 = spqrErrorByte err)
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
  have hwp := v5a_states_from_pb_err_6500_placed (A := A.repAlloc) (F := F) (ext := ext)
    s0 s1 out err (A.pool lim st s1 ∗ Rest)
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1
  refine SepWP.mono hwp fun sf Pf _ _ ⟨hPf, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPf
  exact ⟨Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hvm, hrest⟩

/-! ## `ProtoPolynomialDecoder` Deallocation Loop (`+6420..+6500`) -/

theorem v5a_proto_decoder_dealloc_body_6452_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (fsp out ptsPtr ptsCap x27_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (st : M.σ) (s : State) (Frame : SepProp),
      s.pc = lsmpl.base 333 + 6452#64 →
      s.status = .Running →
      v5a_Saved6428Preserved s0 s fsp out ptsPtr ptsCap x27_val →
      s.readReg64 .x28 = cnt →
      s.readReg64 .x21 = cur + 8#64 →
      SepWP (lsProg_333 (Rust.withPanics ext))
        (lsmpl.base 333 + 6440#64) s
        (vecU8 A.repAlloc cur bs ∗ A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evs : List AllocEvent,
            FreeOnlyEvs evs ∧
            (Pm ⊢ memRegion cur 24 ∗ A.pool lim (M.stepEvents evs st) sm ∗
              stackAt fsp allocHookStack ∗ Frame) ∧
            v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap x27_val ∧
            AllocCallPreserved s sm ∧
            sm.readReg64 .x28 = cnt ∧
            sm.readReg64 .x21 = cur + 8#64) := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc_ok
  clear hdealloc_ok
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  intro cur cnt bs st s Frame hpc hrun hpres hx28 hx21
  rcases hpres with ⟨hsp, hx19, hx22, hx23, hx27, htrace⟩
  change s.pc = (blkPl_333).base + 6452#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 6440#64) s _ _
  refine SepWP.weaken_pre (sepConj_mono_left (vecU8_entails_capPtr_dealloc A.repAlloc cur bs)) ?_
  rw [sepExists_sepConj_left]; apply SepWP.exists_left; intro cap
  rw [sepExists_sepConj_left]; apply SepWP.exists_left; intro vptr
  dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
  by_cases hcap : (cap == 0#64) = true <;>
    simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
  · apply sepWP_evs_nil
    simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
    have hstep : SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 6440#64) s
        (((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
          A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ ((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
            A.pool lim st sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap x27_val ∧
          AllocCallPreserved s sm ∧
          sm.readReg64 .x28 = cnt ∧
          sm.readReg64 .x21 = cur + 8#64) := by
      wp_steps; wp_done
    exact SepWP.mono hstep fun sm _Pm _ _ ⟨hp, hq⟩ =>
      ⟨Entails.trans hp (sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)), hq⟩
  · apply sepWP_evs_dealloc cap.toNat 1
    have hstep : SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 6440#64) s
        (((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8 ∗
          (A.live vptr cap.toNat 1 ∗ memRegion vptr cap.toNat)) ∗
          A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ ((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
            A.pool lim (M.stepEvents (rustDeallocEvents cap.toNat 1) st) sm ∗
            stackAt fsp allocHookStack ∗ Frame) ∧
          v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap x27_val ∧
          AllocCallPreserved s sm ∧
          sm.readReg64 .x28 = cnt ∧
          sm.readReg64 .x21 = cur + 8#64) := by
      wp_steps
      wp_apply
      have hacp_sf : AllocCallPreserved s sf := by
        simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
      rcases hacp_sf with ⟨_, _, _, _, _, _, _⟩
      wp_steps
      refine align_pre_st (by rw [hsp]; simp only [wp_norm, arm64_norm]; sep_ac_rfl) ?_
      wp_done
    exact SepWP.mono hstep fun sm _Pm _ _ ⟨hp, hq⟩ =>
      ⟨Entails.trans hp (sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)), hq⟩

theorem v5a_proto_decoder_dealloc_body_6452_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 : State) (fsp out ptsPtr ptsCap x27_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (st : M.σ) (s : State) (Frame : SepProp),
      s.pc = lsmpl.base 333 + 6452#64 →
      s.status = .Running →
      v5a_Saved6428Preserved s0 s fsp out ptsPtr ptsCap x27_val →
      s.readReg64 .x28 = cnt →
      s.readReg64 .x21 = cur + 8#64 →
      SepWP (lsProg_333 (Rust.withPanics ext))
        (lsmpl.base 333 + 6440#64) s
        (vecU8 A.repAlloc cur bs ∗ A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evs : List AllocEvent,
            FreeOnlyEvs evs ∧
            (Pm ⊢ memRegion cur 24 ∗ A.pool lim (M.stepEvents evs st) sm ∗
              stackAt fsp allocHookStack ∗ Frame) ∧
            v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap x27_val ∧
            AllocCallPreserved s sm ∧
            sm.readReg64 .x28 = cnt ∧
            sm.readReg64 .x21 = cur + 8#64) :=
  v5a_proto_decoder_dealloc_body_6452_of_sub_placed hA.dealloc_ok
    s0 fsp out ptsPtr ptsCap x27_val hfsp_align

theorem v5a_proto_decoder_dealloc_body_6452_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 : State) (fsp out ptsPtr ptsCap x27_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (st : M.σ) (s : State) (Frame : SepProp),
      s.pc = lsmpl.base 333 + 6452#64 →
      s.status = .Running →
      v5a_Saved6428Preserved s0 s fsp out ptsPtr ptsCap x27_val →
      s.readReg64 .x28 = cnt →
      s.readReg64 .x21 = cur + 8#64 →
      SepWP (lsProg_333 (Rust.withPanics ext))
        (lsmpl.base 333 + 6440#64) s
        (vecU8 A.repAlloc cur bs ∗ A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evs : List AllocEvent,
            FreeOnlyEvs evs ∧
            (Pm ⊢ memRegion cur 24 ∗ A.pool lim (M.stepEvents evs st) sm ∗
              stackAt fsp allocHookStack ∗ Frame) ∧
            v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap x27_val ∧
            AllocCallPreserved s sm ∧
            sm.readReg64 .x28 = cnt ∧
            sm.readReg64 .x21 = cur + 8#64) :=
  v5a_proto_decoder_dealloc_body_6452_of_sub_placed (v5a_sub_ok_dealloc_placed hA)
    s0 fsp out ptsPtr ptsCap x27_val hfsp_align

theorem v5a_proto_decoder_dealloc_loop_6452_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (fsp out ptsPtr ptsCap x27_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (st : M.σ) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = lsmpl.base 333 + 6452#64 →
      s.status = .Running →
      v5a_Saved6428Preserved s0 s fsp out ptsPtr ptsCap x27_val →
      s.readReg64 .x28 = BitVec.ofNat 64 rest.length →
      s.readReg64 .x21 = cur + 8#64 →
      SepWP (lsProg_333 (Rust.withPanics ext))
        (lsmpl.base 333 + 6476#64) s
        (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 cur rest ∗
          A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evs : List AllocEvent,
            FreeOnlyEvs evs ∧
            (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool lim (M.stepEvents evs st) sm ∗
              stackAt fsp allocHookStack ∗ Frame) ∧
            v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap x27_val ∧
            AllocCallPreserved s sm) := by
  have hbody := v5a_proto_decoder_dealloc_body_6452_of_sub_placed hdealloc_ok
    s0 fsp out ptsPtr ptsCap x27_val hfsp_align
  intro rest
  induction rest with
  | nil => intro _ _ _ _ hne; exact absurd rfl hne
  | cons bs tl ih =>
    intro cur st s Frame _ hlen hpc hrun hpres hx28 hx21
    simp only [arrayAt, BitVec.ofNat_eq_ofNat]
    rw [sep_pull_body]
    refine seq_clean_evs (mid := lsmpl.base 333 + 6440#64)
      (P_evs := fun evs_hd sm =>
        memRegion cur 24 ∗ A.pool lim (M.stepEvents evs_hd st) sm ∗ stackAt fsp allocHookStack ∗
          (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (cur + 24#64) tl ∗ Frame))
      (Q := fun sm =>
        v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap x27_val ∧
        AllocCallPreserved s sm ∧
        sm.readReg64 .x28 = BitVec.ofNat 64 (bs :: tl).length ∧
        sm.readReg64 .x21 = cur + 8#64)
      (hbody cur (BitVec.ofNat 64 (bs :: tl).length) bs st s
        (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (cur + 24#64) tl ∗ Frame)
        hpc hrun hpres hx28 hx21) ?_
    intro evs_hd s1 hevs_hd hpc1 hrun1 ⟨hpres1, hacp1, hx28_1, hx21_1⟩
    rcases tl with _ | ⟨bs2, tl2⟩
    · simp only [List.length_singleton, arrayAt, sepConj_emp, emp_sepConj, Nat.one_mul] at hx28_1 ⊢
      rcases hpres1 with ⟨hsp_1, hx19_1, hx22_1, hx23_1, hx27_1, htrace_1⟩
      change s1.pc = (blkPl_333).base + 6440#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 6476#64) s1 _ _
      have hfin : SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 6476#64) s1
          (memRegion cur 24 ∗ A.pool lim (M.stepEvents evs_hd st) s1 ∗
            stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ memRegion cur 24 ∗ A.pool lim (M.stepEvents evs_hd st) sm ∗
              stackAt fsp allocHookStack ∗ Frame) ∧
            v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap x27_val ∧
            AllocCallPreserved s1 sm) := by
        wp_steps; wp_done
      exact SepWP.mono hfin fun _ _ _ _ ⟨hp, hpres_f, hacp_f⟩ =>
        ⟨evs_hd, hevs_hd, hp, hpres_f, hacp1.trans hacp_f⟩
    · have hlen_tl : (bs2 :: tl2).length * 24 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_add_one_beq_one_false_24 (n := (bs2 :: tl2).length) (by simp) hlen_tl
      rw [List.length_cons, ofNat_succ_eq_add_one] at hx28_1
      refine seq_clean_st (mid := lsmpl.base 333 + 6452#64)
        (P_mid := fun sm =>
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (cur + 24#64) (bs2 :: tl2) ∗
            A.pool lim (M.stepEvents evs_hd st) sm ∗ stackAt fsp allocHookStack ∗
            (memRegion cur 24 ∗ Frame))
        (Q := fun sm =>
          v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap x27_val ∧
          AllocCallPreserved s1 sm ∧
          sm.readReg64 .x28 = BitVec.ofNat 64 (bs2 :: tl2).length ∧
          sm.readReg64 .x21 = (cur + 24#64) + 8#64)
        ?_ ?_
      · rcases hpres1 with ⟨hsp_1, hx19_1, hx22_1, hx23_1, hx27_1, htrace_1⟩
        change s1.pc = (blkPl_333).base + 6440#64 at hpc1
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 6452#64) s1 _ _
        rw [sep_push_body]
        wp_steps
        rw [add_24_add_8]
        wp_done
      · intro s2 hpc2 hrun2 ⟨hpres2, hacp2, hx28_2, hx21_2⟩
        have hrec := ih (cur + 24#64) (M.stepEvents evs_hd st) s2 (memRegion cur 24 ∗ Frame)
          (List.cons_ne_nil _ _) hlen_tl hpc2 hrun2 hpres2 hx28_2 hx21_2
        refine SepWP.mono hrec fun sf _Pf _ _ ⟨evs_tl, hevs_tl, hp, hpres_f, hacp_tl⟩ => ?_
        refine ⟨evs_hd ++ evs_tl, hevs_hd.append hevs_tl, ?_, hpres_f,
          (hacp1.trans hacp2).trans hacp_tl⟩
        rw [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
        refine Entails.trans hp ?_
        have hsplit := cons_len_mul bs (bs2 :: tl2) 24
        have hbound : 24 + (bs2 :: tl2).length * 24 ≤ 2 ^ 64 := by
          rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
        rw [sep_rejoin_loop, hsplit,
          ProofLib.memRegion_split cur 24 ((bs2 :: tl2).length * 24) hbound]
        exact Entails.refl _

theorem v5a_proto_decoder_dealloc_loop_6452_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 : State) (fsp out ptsPtr ptsCap x27_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (st : M.σ) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = lsmpl.base 333 + 6452#64 →
      s.status = .Running →
      v5a_Saved6428Preserved s0 s fsp out ptsPtr ptsCap x27_val →
      s.readReg64 .x28 = BitVec.ofNat 64 rest.length →
      s.readReg64 .x21 = cur + 8#64 →
      SepWP (lsProg_333 (Rust.withPanics ext))
        (lsmpl.base 333 + 6476#64) s
        (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 cur rest ∗
          A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evs : List AllocEvent,
            FreeOnlyEvs evs ∧
            (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool lim (M.stepEvents evs st) sm ∗
              stackAt fsp allocHookStack ∗ Frame) ∧
            v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap x27_val ∧
            AllocCallPreserved s sm) :=
  v5a_proto_decoder_dealloc_loop_6452_of_sub_placed hA.dealloc_ok
    s0 fsp out ptsPtr ptsCap x27_val hfsp_align

theorem v5a_proto_decoder_dealloc_loop_6452_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 : State) (fsp out ptsPtr ptsCap x27_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (st : M.σ) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = lsmpl.base 333 + 6452#64 →
      s.status = .Running →
      v5a_Saved6428Preserved s0 s fsp out ptsPtr ptsCap x27_val →
      s.readReg64 .x28 = BitVec.ofNat 64 rest.length →
      s.readReg64 .x21 = cur + 8#64 →
      SepWP (lsProg_333 (Rust.withPanics ext))
        (lsmpl.base 333 + 6476#64) s
        (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 cur rest ∗
          A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evs : List AllocEvent,
            FreeOnlyEvs evs ∧
            (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool lim (M.stepEvents evs st) sm ∗
              stackAt fsp allocHookStack ∗ Frame) ∧
            v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap x27_val ∧
            AllocCallPreserved s sm) :=
  v5a_proto_decoder_dealloc_loop_6452_of_sub_placed (v5a_sub_ok_dealloc_placed hA)
    s0 fsp out ptsPtr ptsCap x27_val hfsp_align

/-- Shared `ProtoPolynomialDecoder` inline deallocation at `+6428 -> +6500` under an explicit
    Block-`333` `__rust_dealloc` contract: deallocates all `Vec<u8>` elements in `pts` and the
    `pts` buffer itself (`FreeOnlyEvs`), then reaches `+6500`. -/
theorem v5a_states_from_pb_dealloc_proto_decoder_6428_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s : State) (fsp out ptsPtr ptsCap x27_val : BitVec 64)
    (pts : List (List (BitVec 8))) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 6428#64)
    (hrun : s.status = .Running)
    (hpres : v5a_Saved6428Preserved s0 s fsp out ptsPtr ptsCap x27_val)
    (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 pts.length) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 6500#64) s
      ((if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢ A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap x27_val ∧
          AllocCallPreserved s sm) := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc_ok
  have hloop := v5a_proto_decoder_dealloc_loop_6452_of_sub_placed hdealloc_ok
    s0 fsp out ptsPtr ptsCap x27_val hfsp_align
  clear hdealloc_ok
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  refine seq_clean_evs (mid := lsmpl.base 333 + 6476#64)
    (P_evs := fun evs1 sm =>
      (if ptsCap = 0#64 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗ memRegion ptsPtr (ptsCap.toNat * 24)) ∗
      A.pool lim (M.stepEvents evs1 st) sm ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm =>
      v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap x27_val ∧
      AllocCallPreserved s sm)
    ?_ ?_
  · cases pts with
    | nil =>
      apply sepWP_evs_nil
      simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
      rcases hpres with ⟨hsp, hx19, hx22, hx23, hx27, htrace⟩
      simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, arrayAt, emp_sepConj] at hx28 ⊢
      change s.pc = (blkPl_333).base + 6428#64 at hpc
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 6476#64) s _ _
      wp_steps
      refine align_pre_st (by simp only [wp_norm, arm64_norm]) ?_
      wp_done
    | cons bs tl =>
      have hlen_pos : 0 < (bs :: tl).length := by simp
      have hlen_lt : (bs :: tl).length * 24 < 2 ^ 63 := by
        have : (bs :: tl).length * 24 ≤ ptsCap.toNat * 24 := Nat.mul_le_mul_right 24 hpts_le
        omega
      have hne0 := ofNat_beq_zero_false_24 hlen_pos hlen_lt
      have hcap_ne : ptsCap ≠ 0#64 := by intro hc0; rw [hc0] at hpts_le; simp at hpts_le
      simp only [BitVec.ofNat_eq_ofNat, hcap_ne, ↓reduceIte]
      refine seq_clean_st (mid := lsmpl.base 333 + 6452#64)
        (P_mid := fun sm =>
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr (bs :: tl) ∗
            A.pool lim st sm ∗ stackAt fsp allocHookStack ∗
            (A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
             memRegion (ptsPtr + BitVec.ofNat 64 ((bs :: tl).length * 24))
               ((ptsCap.toNat - (bs :: tl).length) * 24) ∗
             Frame))
        (Q := fun sm =>
          v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap x27_val ∧
          AllocCallPreserved s sm ∧
          sm.readReg64 .x28 = BitVec.ofNat 64 (bs :: tl).length ∧
          sm.readReg64 .x21 = ptsPtr + 8#64)
        ?_ ?_
      · rcases hpres with ⟨hsp, hx19, hx22, hx23, hx27, htrace⟩
        change s.pc = (blkPl_333).base + 6428#64 at hpc
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 6452#64) s _ _
        wp_steps
        refine align_pre_st (by simp only [wp_norm, arm64_norm]; sep_ac_rfl) ?_
        wp_done
      · intro s_loop hpc_loop hrun_loop ⟨hpres_loop, hacp_loop, hx28_loop, hx21_loop⟩
        have hl := hloop (bs :: tl) ptsPtr st s_loop
          (A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
            memRegion (ptsPtr + BitVec.ofNat 64 ((bs :: tl).length * 24))
              ((ptsCap.toNat - (bs :: tl).length) * 24) ∗
            Frame)
          (List.cons_ne_nil _ _) hlen_lt hpc_loop hrun_loop hpres_loop hx28_loop hx21_loop
        refine SepWP.mono hl fun sm _Pm _ _ ⟨evs1, hevs1, hp, hpres_m, hacp_m⟩ => ?_
        refine ⟨evs1, hevs1, ?_, hpres_m, hacp_loop.trans hacp_m⟩
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
        refine Entails.trans hp ?_
        refine Entails.trans
          (Entails.of_eq (show _ =
            (A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
             memRegion ptsPtr ((bs :: tl).length * 24) ∗
             memRegion (ptsPtr + BitVec.ofNat 64 ((bs :: tl).length * 24))
               ((ptsCap.toNat - (bs :: tl).length) * 24)) ∗
            A.pool lim (M.stepEvents evs1 st) sm ∗ stackAt fsp allocHookStack ∗ Frame by
              sep_ac_rfl))
          (sepConj_mono_left hjoin)
  · intro evs1 s3 hevs1 hpc3 hrun3 ⟨hpres3, hacp3⟩
    rcases hpres3 with ⟨hsp_3, hx19_3, hx22_3, hx23_3, hx27_3, htrace_3⟩
    change s3.pc = (blkPl_333).base + 6476#64 at hpc3
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 6500#64) s3 _ _
    by_cases hc : ptsCap = 0#64
    · have hc_beq : (ptsCap == 0#64) = true := by rw [beq_iff_eq]; exact hc
      simp only [hc, ↓reduceIte, emp_sepConj, sepConj_emp] at hx23_3 ⊢
      have hfin : SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 6500#64) s3
          (A.pool lim (M.stepEvents evs1 st) s3 ∗ stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ A.pool lim (M.stepEvents evs1 st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
            v5a_Saved6428Preserved s0 sm fsp out ptsPtr 0#64 x27_val ∧
            AllocCallPreserved s3 sm) := by
        wp_steps; wp_done
      exact SepWP.mono hfin fun _ _ _ _ ⟨hp, hpres_f, hacp_f⟩ =>
        ⟨evs1, hevs1, hp, hpres_f, hacp3.trans hacp_f⟩
    · have hc_beq : ¬((ptsCap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
      have hlsl := cap_mul_24 hpts_cap_lt
      simp only [hc, ↓reduceIte]
      have hfin : SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 6500#64) s3
          ((A.live ptsPtr (ptsCap.toNat * 24) 8 ∗ memRegion ptsPtr (ptsCap.toNat * 24)) ∗
            A.pool lim (M.stepEvents evs1 st) s3 ∗ stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ A.pool lim
                (M.stepEvents (rustDeallocEvents (ptsCap.toNat * 24) 8) (M.stepEvents evs1 st))
                sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
            v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap x27_val ∧
            AllocCallPreserved s3 sm) := by
        wp_steps
        wp_apply
        have hacp_sf : AllocCallPreserved s3 sf := by
          simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
        rcases hacp_sf with ⟨_, _, _, _, _, _, _⟩
        wp_steps
        refine align_pre_st (by rw [hsp_3]; sep_ac_rfl) ?_
        wp_done
      refine SepWP.mono hfin fun sm _Pm _ _ ⟨hp, hpres_f, hacp_f⟩ => ?_
      refine ⟨evs1 ++ rustDeallocEvents (ptsCap.toNat * 24) 8,
        hevs1.append (LibsignalBinary.Heap.FreeOnlyEvs.singleton 8 (ptsCap.toNat * 24)),
        ?_, hpres_f, hacp3.trans hacp_f⟩
      rw [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
      exact hp

theorem v5a_states_from_pb_dealloc_proto_decoder_6428_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s : State) (fsp out ptsPtr ptsCap x27_val : BitVec 64)
    (pts : List (List (BitVec 8))) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 6428#64)
    (hrun : s.status = .Running)
    (hpres : v5a_Saved6428Preserved s0 s fsp out ptsPtr ptsCap x27_val)
    (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 pts.length) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 6500#64) s
      ((if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢ A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap x27_val ∧
          AllocCallPreserved s sm) :=
  v5a_states_from_pb_dealloc_proto_decoder_6428_of_sub_placed hA.dealloc_ok
    st s0 s fsp out ptsPtr ptsCap x27_val pts Frame
    hfsp_align hpts_le hpts_cap_lt hpc hrun hpres hx28

theorem v5a_states_from_pb_dealloc_proto_decoder_6428_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s : State) (fsp out ptsPtr ptsCap x27_val : BitVec 64)
    (pts : List (List (BitVec 8))) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 6428#64)
    (hrun : s.status = .Running)
    (hpres : v5a_Saved6428Preserved s0 s fsp out ptsPtr ptsCap x27_val)
    (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 pts.length) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 6500#64) s
      ((if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢ A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap x27_val ∧
          AllocCallPreserved s sm) :=
  v5a_states_from_pb_dealloc_proto_decoder_6428_of_sub_placed (v5a_sub_ok_dealloc_placed hA)
    st s0 s fsp out ptsPtr ptsCap x27_val pts Frame
    hfsp_align hpts_le hpts_cap_lt hpc hrun hpres hx28

/-- `VmPreserved`-strengthened `+6420 -> +6500` branch when `receivingHdr = none` (`ptsCap = noneCap`). -/
theorem v5a_states_from_pb_dealloc_none_proto_decoder_6420_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out ptsPtr x27_val : BitVec 64) (P : SepProp)
    (hpc : s.pc = lsmpl.base 333 + 6420#64)
    (hrun : s.status = .Running)
    (hpres : v5a_Saved6428Preserved s0 s fsp out ptsPtr noneCap x27_val) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 6500#64) s P
      (fun sm Pm =>
        (Pm ⊢ P) ∧
        v5a_Saved6428Preserved s0 sm fsp out ptsPtr noneCap x27_val ∧
        VmPreserved s sm ∧
        AllocCallPreserved s sm) := by
  rcases hpres with ⟨hsp, hx19, hx22, hx23, hx27, htrace⟩
  dsimp only [noneCap] at hx23
  change s.pc = (blkPl_333).base + 6420#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 6500#64) s P _
  wp_steps
  wp_done

theorem v5a_states_from_pb_dealloc_none_proto_decoder_6420_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out ptsPtr x27_val : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = lsmpl.base 333 + 6420#64)
    (hrun : s.status = .Running)
    (hpres : v5a_Saved6428Preserved s0 s fsp out ptsPtr noneCap x27_val) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 6500#64) s
      (A.pool lim st s ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ A.pool lim st sm ∗ Frame) ∧
        v5a_Saved6428Preserved s0 sm fsp out ptsPtr noneCap x27_val ∧
        VmPreserved s sm ∧
        AllocCallPreserved s sm) := by
  have hwp := v5a_states_from_pb_dealloc_none_proto_decoder_6420_placed (ext := ext)
    s0 s fsp out ptsPtr x27_val (A.pool lim st s ∗ Frame) hpc hrun hpres
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hpres_m, hvm, hacp⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨hPm, hpres_m, hvm, hacp⟩

theorem v5a_states_from_pb_dealloc_some_proto_decoder_6420_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s : State) (fsp out ptsPtr ptsCap x27_val : BitVec 64)
    (pts : List (List (BitVec 8))) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 6420#64)
    (hrun : s.status = .Running)
    (hpres : v5a_Saved6428Preserved s0 s fsp out ptsPtr ptsCap x27_val)
    (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 pts.length) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 6500#64) s
      ((if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢ A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap x27_val ∧
          AllocCallPreserved s sm) := by
  refine seq_clean_st (mid := lsmpl.base 333 + 6428#64)
    (P_mid := fun sm =>
      (if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool lim st sm ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm =>
      v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap x27_val ∧
      AllocCallPreserved s sm ∧
      sm.readReg64 .x28 = BitVec.ofNat 64 pts.length)
    ?_ ?_
  · rcases hpres with ⟨hsp, hx19, hx22, hx23, hx27, htrace⟩
    have hne := v5a_ptsCap_add_one_ne_zero hpts_cap_lt
    change s.pc = (blkPl_333).base + 6420#64 at hpc
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 6428#64) s _ _
    wp_steps
    wp_done
  · intro s1 hpc1 hrun1 ⟨hpres1, hacp1, hx28_1⟩
    have h6428 := v5a_states_from_pb_dealloc_proto_decoder_6428_of_sub_placed hdealloc_ok
      st s0 s1 fsp out ptsPtr ptsCap x27_val pts Frame
      hfsp_align hpts_le hpts_cap_lt hpc1 hrun1 hpres1 hx28_1
    exact SepWP.mono h6428 fun _ _ _ _ ⟨evs, hevs, hp, hpres_f, hacp_f⟩ =>
      ⟨evs, hevs, hp, hpres_f, hacp1.trans hacp_f⟩

theorem v5a_states_from_pb_dealloc_some_proto_decoder_6420_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s : State) (fsp out ptsPtr ptsCap x27_val : BitVec 64)
    (pts : List (List (BitVec 8))) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 6420#64)
    (hrun : s.status = .Running)
    (hpres : v5a_Saved6428Preserved s0 s fsp out ptsPtr ptsCap x27_val)
    (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 pts.length) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 6500#64) s
      ((if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢ A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap x27_val ∧
          AllocCallPreserved s sm) :=
  v5a_states_from_pb_dealloc_some_proto_decoder_6420_of_sub_placed hA.dealloc_ok
    st s0 s fsp out ptsPtr ptsCap x27_val pts Frame
    hfsp_align hpts_le hpts_cap_lt hpc hrun hpres hx28

theorem v5a_states_from_pb_dealloc_some_proto_decoder_6420_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s : State) (fsp out ptsPtr ptsCap x27_val : BitVec 64)
    (pts : List (List (BitVec 8))) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 6420#64)
    (hrun : s.status = .Running)
    (hpres : v5a_Saved6428Preserved s0 s fsp out ptsPtr ptsCap x27_val)
    (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 pts.length) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 6500#64) s
      ((if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢ A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap x27_val ∧
          AllocCallPreserved s sm) :=
  v5a_states_from_pb_dealloc_some_proto_decoder_6420_of_sub_placed (v5a_sub_ok_dealloc_placed hA)
    st s0 s fsp out ptsPtr ptsCap x27_val pts Frame
    hfsp_align hpts_le hpts_cap_lt hpc hrun hpres hx28

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5aPlacedBudget

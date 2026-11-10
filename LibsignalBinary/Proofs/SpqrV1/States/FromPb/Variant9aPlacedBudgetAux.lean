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
public import LibsignalBinary.Proofs.SpqrV1.Drop.UnchunkedBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9aPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch2Placed
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Auxiliary Decoder-Cleanup and Exit Lemmas for `Variant9aPlacedBudget`

Relocatable callee contracts, `VmPreserved`-strengthened `+7084` `Err(err)` exit, and
`FreeOnlyEvs`-tracked inline `ProtoPolynomialDecoder` deallocation (`+5360..+5440 -> +7084`) for
Variant 9 (`Ct1Acknowledged`, Block `333`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9aPlacedBudgetAux

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkLib_eq_333 blkPC_333 blkPl_333
   lsProg_286 lsProg_333 ls_blockPlacement_base ls_subroutine_ok_of_block lscall_blk_cl
   lsmpl lsρ subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded withMemEq)
open CryptoVerification.LibsignalSpqrV1 (Error)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (RustAlloc allocHookStack arrayAt vecU8)
open CryptoVerification.SpqrV1.Alloc (spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.Drop
  (add_24_add_8 cap_mul_24 chunkedStatesSize cons_len_mul header_cells_entails_memRegion_24
   ofNat_add_one_beq_one_false_24 ofNat_beq_zero_false_24 ofNat_succ_eq_add_one
   sep_pull_body sep_push_body sep_rejoin_loop tail_len_mul_lt vecCapPtrDealloc
   vecU8_entails_capPtr_dealloc)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved resultChunkedStatesAt spqrErrorByte statesFromPbSavedCells statesFromPbStack
   v9_Saved5368Preserved v9_ptsCap_add_one_ne_zero)
open CryptoVerification.SpqrV1.Unchunked
  (extractLsb'_0_64_append extractLsb'_64_64_append)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget
   VmPreserved rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.Drop.UnchunkedBudget
  (dropProtoUnchunkedCt1SentEkReceivedSpec
   drop_proto_unchunked_ct1_sent_ek_received_placed_ok)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (calleeSavedPreserved_of_stripS_right isTotalTrapHooks_withPanics_vmTrapHooks
   sepWP_lsBlock_vmPreserved stripS_calleeSavedVRegs stripS_pc stripS_readReg64 stripS_sp
   stripS_status stripS_trace vmTrapHooks)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
  (DecoderFromPbPlacedOkExt decoderFromPbSpec spqrRustDeallocSym)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
  (align_pre_st deallocFreeOnlySpec sepWP_evs_dealloc sepWP_evs_nil seq_clean_evs
   seq_clean_st subroutine_ok_deallocFreeOnly)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
  (FromPbAllocHooksBudget v1_deallocFreeOnly_ok_at_statesFromPb_placed
   v1_dealloc_ok_at_statesFromPb_placed v1_dealloc_ok_of_dealloc_placed
   withMemEq_of_withLsCodeLoaded)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux
  (blk333_noSvc0)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget (blk333_safeVm)

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

/-! ## 1. Relocatable Callee Contracts & Shared `Err(err)` Exit at `+7084` -/

theorem v9_sub_ok_dealloc_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim) :=
  v1_dealloc_ok_of_dealloc_placed hdealloc

theorem v9_sub_ok_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim) :=
  v1_dealloc_ok_at_statesFromPb_placed hA

theorem v9_sub_ok_deallocFreeOnly_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (deallocFreeOnlySpec M A lim) :=
  v1_deallocFreeOnly_ok_at_statesFromPb_placed hA

theorem v9_sub_ok_decoder_from_pb_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 376)
      (withLsCodeLoaded lsmpl (DefsBudget.decoderFromPbSpec M A lim)) :=
  hdec

theorem v9_sub_ok_decoder_from_pb_mem_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {m : Memory}
    (hdec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext) (hcl : LibsignalCodeLoaded lsmpl m) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsmpl.base 376)
      (withMemEq m (DefsBudget.decoderFromPbSpec M A lim)) :=
  withMemEq_of_withLsCodeLoaded hdec hcl

theorem drop_proto_unchunked_ct1_sent_ek_received_cl_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_286 (Rust.withPanics ext)) (lsmpl.base 286)
      (withLsCodeLoaded lsmpl (dropProtoUnchunkedCt1SentEkReceivedSpec M A lim)) := by
  rw [← ls_blockPlacement_base (i := 286)]
  exact subroutine_ok_withLsCodeLoaded_of_plain
    (drop_proto_unchunked_ct1_sent_ek_received_placed_ok (spqr_hook_ok_of_mem hdealloc))

theorem v9_sub_ok_drop_proto_unchunked_ct1_sent_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 286)
      (withLsCodeLoaded lsmpl (dropProtoUnchunkedCt1SentEkReceivedSpec M A lim)) :=
  ls_subroutine_ok_of_block
    (drop_proto_unchunked_ct1_sent_ek_received_cl_placed_ok hdealloc) (by decide)

theorem v9_sub_ok_drop_proto_unchunked_ct1_sent_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 286)
      (withLsCodeLoaded lsmpl (dropProtoUnchunkedCt1SentEkReceivedSpec M A lim)) :=
  v9_sub_ok_drop_proto_unchunked_ct1_sent_of_dealloc_placed hA.dealloc

theorem v9_sub_ok_drop_proto_unchunked_ct1_sent_mem_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {m : Memory}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hcl : LibsignalCodeLoaded lsmpl m) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsmpl.base 286)
      (withMemEq m (dropProtoUnchunkedCt1SentEkReceivedSpec M A lim)) :=
  lscall_blk_cl (drop_proto_unchunked_ct1_sent_ek_received_cl_placed_ok hdealloc) hcl (by decide)

theorem v9_sub_ok_drop_proto_unchunked_ct1_sent_mem_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {m : Memory}
    (hA : FromPbAllocHooksBudget M A lim ext) (hcl : LibsignalCodeLoaded lsmpl m) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsmpl.base 286)
      (withMemEq m (dropProtoUnchunkedCt1SentEkReceivedSpec M A lim)) :=
  v9_sub_ok_drop_proto_unchunked_ct1_sent_mem_of_dealloc_placed hA.dealloc hcl

/-- `VmPreserved`-strengthened shared `Err(err)` exit at `+7084` (`+7084 -> +60 -> s0.x30`):
    when `x28` has low byte `spqrErrorByte err` and `x19 = out`, writes `x26, x24` to `[out + 16..32]`,
    sets `x8 = noneCap`, writes `x28` to `[out + 8]`, and branches to `+60`. -/
theorem v9_states_from_pb_err_7084_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (err : Error) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 7084#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx28_1 : (s1.readReg64 .x28).extractLsb' 0 8 = spqrErrorByte err)
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
    (Variant9aPlaced.v9_states_from_pb_err_7084_placed
      (A := A) (F := F) (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      out err Rest hsp0_align
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1) (by simpa using hx28_1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sf Pf hvm ⟨hPf, hsp_f, hcc_f, htr_f⟩ =>
      ⟨hPf, hvm, by simpa using hsp_f, calleeSavedPreserved_of_stripS_right hcc_f,
       by simpa using htr_f⟩

theorem v9_states_from_pb_err_7084_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (err : Error) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 7084#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx28_1 : (s1.readReg64 .x28).extractLsb' 0 8 = spqrErrorByte err)
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
  have hwp := v9_states_from_pb_err_7084_placed (A := A.repAlloc) (F := F) (ext := ext)
    s0 s1 out err (A.pool lim st s1 ∗ Rest)
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx28_1 htr1
  refine SepWP.mono hwp fun sf Pf _ _ ⟨hPf, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPf
  exact ⟨Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hvm, hrest⟩

/-! ## 2. Shared `ProtoPolynomialDecoder` Deallocation Loop (`+5360..+5440 -> +7084`) -/

theorem v9_proto_decoder_dealloc_body_5392_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (fsp out ptsPtr ptsCap x28_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (st : M.σ) (cur cnt : BitVec 64) (bs : List (BitVec 8)) (s : State) (Frame : SepProp),
      s.pc = lsmpl.base 333 + 5392#64 →
      s.status = .Running →
      v9_Saved5368Preserved s0 s fsp out ptsPtr ptsCap x28_val →
      s.readReg64 .x22 = cnt →
      s.readReg64 .x23 = cur + 8#64 →
      SepWP (lsProg_333 (Rust.withPanics ext))
        (lsmpl.base 333 + 5380#64) s
        (vecU8 A.repAlloc cur bs ∗ A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evs : List AllocEvent,
            FreeOnlyEvs evs ∧
            (Pm ⊢ memRegion cur 24 ∗ A.pool lim (M.stepEvents evs st) sm ∗
              stackAt fsp allocHookStack ∗ Frame) ∧
            v9_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap x28_val ∧
            sm.readReg64 .x22 = cnt ∧
            sm.readReg64 .x23 = cur + 8#64) := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc_ok
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  intro st cur cnt bs s Frame hpc hrun hpres hx22 hx23
  rcases hpres with ⟨hsp, hx19, hx20, hx21, hx28, htrace⟩
  have hsp_align_s : (s.sp &&& 15#64 == 0#64) = true := hsp ▸ hfsp_align
  refine SepWP.weaken_pre (sepConj_mono_left (vecU8_entails_capPtr_dealloc A.repAlloc cur bs)) ?_
  wp_simp_pre [sepExists_sepConj_left]
  apply ProofLib.SepWP.exists_left; intro cap
  apply ProofLib.SepWP.exists_left; intro vptr
  change s.pc = (blkPl_333).base + 5392#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 5380#64) s _ _
  have hstep : SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 5380#64) s
      ((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8 ∗
        vecCapPtrDealloc A.repAlloc cap vptr ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢ ((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
            A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v9_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap x28_val ∧
          sm.readReg64 .x22 = cnt ∧
          sm.readReg64 .x23 = cur + 8#64) := by
    dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
      BitVec.ofNat_eq_ofNat] at hdealloc_fo ⊢
    by_cases hcap : (cap == 0#64) = true <;>
      simp only [hcap, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · apply sepWP_evs_nil
      simp only [M.stepEvents_nil]
      wp_steps_sync_333 ((blkPl_333).base + 5380#64)
      try simp only [State.setMem_setMem]
      refine align_pre_st (by (try simp only [wp_norm, arm64_norm]); try sep_ac_rfl) ?_
      wp_done
    · apply sepWP_evs_dealloc cap.toNat 1
      wp_steps_sync_333 (lsρ spqrRustDeallocSym)
      try simp only [State.setMem_setMem]
      wp_call hdealloc_fo (vptr, cap.toNat, 1, st)
      have hacp : AllocCallPreserved s sf := by
        simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
      have htr_sf : sf.trace = s0.trace := hacp.2.1.trans htrace.1
      have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
        ‹calleeSavedVRegs sf = calleeSavedVRegs s›.trans htrace.2
      wp_steps_sync_333 ((blkPl_333).base + 5380#64)
      try simp only [State.setMem_setMem]
      refine align_pre_st (by (try simp only [wp_norm, arm64_norm, hsp]); try sep_ac_rfl) ?_
      wp_done
  refine SepWP.mono hstep fun sm _Pm _ _ ⟨evs, hevs, hPm, hq⟩ => ?_
  exact ⟨evs, hevs,
    Entails.trans hPm (sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)), hq⟩

theorem v9_proto_decoder_dealloc_body_5392_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (fsp out ptsPtr ptsCap x28_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (st : M.σ) (cur cnt : BitVec 64) (bs : List (BitVec 8)) (s : State) (Frame : SepProp),
      s.pc = lsmpl.base 333 + 5392#64 →
      s.status = .Running →
      v9_Saved5368Preserved s0 s fsp out ptsPtr ptsCap x28_val →
      s.readReg64 .x22 = cnt →
      s.readReg64 .x23 = cur + 8#64 →
      SepWP (lsProg_333 (Rust.withPanics ext))
        (lsmpl.base 333 + 5380#64) s
        (vecU8 A.repAlloc cur bs ∗ A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evs : List AllocEvent,
            FreeOnlyEvs evs ∧
            (Pm ⊢ memRegion cur 24 ∗ A.pool lim (M.stepEvents evs st) sm ∗
              stackAt fsp allocHookStack ∗ Frame) ∧
            v9_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap x28_val ∧
            sm.readReg64 .x22 = cnt ∧
            sm.readReg64 .x23 = cur + 8#64) :=
  v9_proto_decoder_dealloc_body_5392_of_sub_placed
    (v9_sub_ok_dealloc_of_dealloc_placed hdealloc) s0 fsp out ptsPtr ptsCap x28_val hfsp_align

theorem v9_proto_decoder_dealloc_body_5392_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 : State) (fsp out ptsPtr ptsCap x28_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (st : M.σ) (cur cnt : BitVec 64) (bs : List (BitVec 8)) (s : State) (Frame : SepProp),
      s.pc = lsmpl.base 333 + 5392#64 →
      s.status = .Running →
      v9_Saved5368Preserved s0 s fsp out ptsPtr ptsCap x28_val →
      s.readReg64 .x22 = cnt →
      s.readReg64 .x23 = cur + 8#64 →
      SepWP (lsProg_333 (Rust.withPanics ext))
        (lsmpl.base 333 + 5380#64) s
        (vecU8 A.repAlloc cur bs ∗ A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evs : List AllocEvent,
            FreeOnlyEvs evs ∧
            (Pm ⊢ memRegion cur 24 ∗ A.pool lim (M.stepEvents evs st) sm ∗
              stackAt fsp allocHookStack ∗ Frame) ∧
            v9_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap x28_val ∧
            sm.readReg64 .x22 = cnt ∧
            sm.readReg64 .x23 = cur + 8#64) :=
  v9_proto_decoder_dealloc_body_5392_of_dealloc_placed
    hA.dealloc s0 fsp out ptsPtr ptsCap x28_val hfsp_align

theorem v9_proto_decoder_dealloc_loop_5392_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (fsp out ptsPtr ptsCap x28_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (st : M.σ) (cur : BitVec 64) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = lsmpl.base 333 + 5392#64 →
      s.status = .Running →
      v9_Saved5368Preserved s0 s fsp out ptsPtr ptsCap x28_val →
      s.readReg64 .x22 = BitVec.ofNat 64 rest.length →
      s.readReg64 .x23 = cur + 8#64 →
      SepWP (lsProg_333 (Rust.withPanics ext))
        (lsmpl.base 333 + 5416#64) s
        (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 cur rest ∗
          A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evs : List AllocEvent,
            FreeOnlyEvs evs ∧
            (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool lim (M.stepEvents evs st) sm ∗
              stackAt fsp allocHookStack ∗ Frame) ∧
            v9_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap x28_val) := by
  have hbody := v9_proto_decoder_dealloc_body_5392_of_sub_placed
    hdealloc_ok s0 fsp out ptsPtr ptsCap x28_val hfsp_align
  intro rest
  induction rest with
  | nil => intro _ _ _ _ hne; exact absurd rfl hne
  | cons bs tl ih =>
    intro st cur s Frame _ hlen hpc hrun hpres hx22 hx23
    simp only [arrayAt, BitVec.ofNat_eq_ofNat]
    rw [sep_pull_body]
    refine seq_clean_evs (mid := lsmpl.base 333 + 5380#64)
      (P_evs := fun evs1 sm =>
        memRegion cur 24 ∗ A.pool lim (M.stepEvents evs1 st) sm ∗ stackAt fsp allocHookStack ∗
          (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (cur + 24#64) tl ∗ Frame))
      (Q := fun sm => v9_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap x28_val ∧
        sm.readReg64 .x22 = BitVec.ofNat 64 (bs :: tl).length ∧
        sm.readReg64 .x23 = cur + 8#64)
      (hbody st cur (BitVec.ofNat 64 (bs :: tl).length) bs s _ hpc hrun hpres hx22 hx23) ?_
    intro evs1 s1 hevs1 hpc1 hrun1 ⟨hpres1, hx22_1, hx23_1⟩
    let st1 := M.stepEvents evs1 st
    rcases tl with _ | ⟨bs2, tl2⟩
    · simp only [List.length_singleton, arrayAt, sepConj_emp, emp_sepConj, Nat.one_mul] at hx22_1 ⊢
      rcases hpres1 with ⟨hsp_1, hx19_1, hx20_1, hx21_1, hx28_1, htrace_1⟩
      have hfin : SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 5416#64) s1
          (memRegion cur 24 ∗ A.pool lim st1 s1 ∗ stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ memRegion cur 24 ∗ A.pool lim st1 sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
            v9_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap x28_val) := by
        change s1.pc = (blkPl_333).base + 5380#64 at hpc1
        wp_steps_sync_333 ((blkPl_333).base + 5416#64)
        try simp only [State.setMem_setMem]
        refine align_pre_st (by (try simp only [wp_norm, arm64_norm]); try sep_ac_rfl) ?_
        wp_done
      exact SepWP.mono hfin fun _ _ _ _ ⟨hp, hq⟩ => ⟨evs1, hevs1, hp, hq⟩
    · have hlen_tl : (bs2 :: tl2).length * 24 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_add_one_beq_one_false_24 (n := (bs2 :: tl2).length) (by simp) hlen_tl
      rw [List.length_cons, ofNat_succ_eq_add_one] at hx22_1
      refine seq_clean_st (mid := lsmpl.base 333 + 5392#64)
        (P_mid := fun s2 =>
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (cur + 24#64) (bs2 :: tl2) ∗
            A.pool lim st1 s2 ∗ stackAt fsp allocHookStack ∗ (memRegion cur 24 ∗ Frame))
        (Q := fun s2 => v9_Saved5368Preserved s0 s2 fsp out ptsPtr ptsCap x28_val ∧
          s2.readReg64 .x22 = BitVec.ofNat 64 (bs2 :: tl2).length ∧
          s2.readReg64 .x23 = (cur + 24#64) + 8#64)
        ?_ ?_
      · rcases hpres1 with ⟨hsp_1, hx19_1, hx20_1, hx21_1, hx28_1, htrace_1⟩
        change s1.pc = (blkPl_333).base + 5380#64 at hpc1
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 5392#64) s1 _ _
        rw [sep_push_body]
        wp_steps_sync_333 ((blkPl_333).base + 5392#64)
        try simp only [State.setMem_setMem]
        rw [add_24_add_8]
        refine align_pre_st (by (try simp only [wp_norm, arm64_norm]); try sep_ac_rfl) ?_
        wp_done
      · intro s2 hpc2 hrun2 ⟨hpres2, hx22_2, hx23_2⟩
        have hrec := ih st1 (cur + 24#64) s2 (memRegion cur 24 ∗ Frame)
          (List.cons_ne_nil _ _) hlen_tl hpc2 hrun2 hpres2 hx22_2 hx23_2
        refine SepWP.mono hrec fun sm _Pm _ _ ⟨evs2, hevs2, hPm, hpres_m⟩ => ?_
        refine ⟨evs1 ++ evs2, hevs1.append hevs2, ?_, hpres_m⟩
        have hst_eq : M.stepEvents evs2 st1 = M.stepEvents (evs1 ++ evs2) st := by
          dsimp only [st1]; rw [M.stepEvents_append]
        rw [hst_eq] at hPm
        refine Entails.trans hPm ?_
        have hsplit := cons_len_mul bs (bs2 :: tl2) 24
        have hbound : 24 + (bs2 :: tl2).length * 24 ≤ 2 ^ 64 := by
          rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
        rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 24 ((bs2 :: tl2).length * 24) hbound]
        exact Entails.refl _

theorem v9_proto_decoder_dealloc_loop_5392_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (fsp out ptsPtr ptsCap x28_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (st : M.σ) (cur : BitVec 64) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = lsmpl.base 333 + 5392#64 →
      s.status = .Running →
      v9_Saved5368Preserved s0 s fsp out ptsPtr ptsCap x28_val →
      s.readReg64 .x22 = BitVec.ofNat 64 rest.length →
      s.readReg64 .x23 = cur + 8#64 →
      SepWP (lsProg_333 (Rust.withPanics ext))
        (lsmpl.base 333 + 5416#64) s
        (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 cur rest ∗
          A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evs : List AllocEvent,
            FreeOnlyEvs evs ∧
            (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool lim (M.stepEvents evs st) sm ∗
              stackAt fsp allocHookStack ∗ Frame) ∧
            v9_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap x28_val) :=
  v9_proto_decoder_dealloc_loop_5392_of_sub_placed
    (v9_sub_ok_dealloc_of_dealloc_placed hdealloc) s0 fsp out ptsPtr ptsCap x28_val hfsp_align

theorem v9_proto_decoder_dealloc_loop_5392_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 : State) (fsp out ptsPtr ptsCap x28_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (st : M.σ) (cur : BitVec 64) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = lsmpl.base 333 + 5392#64 →
      s.status = .Running →
      v9_Saved5368Preserved s0 s fsp out ptsPtr ptsCap x28_val →
      s.readReg64 .x22 = BitVec.ofNat 64 rest.length →
      s.readReg64 .x23 = cur + 8#64 →
      SepWP (lsProg_333 (Rust.withPanics ext))
        (lsmpl.base 333 + 5416#64) s
        (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 cur rest ∗
          A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evs : List AllocEvent,
            FreeOnlyEvs evs ∧
            (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool lim (M.stepEvents evs st) sm ∗
              stackAt fsp allocHookStack ∗ Frame) ∧
            v9_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap x28_val) :=
  v9_proto_decoder_dealloc_loop_5392_of_dealloc_placed
    hA.dealloc s0 fsp out ptsPtr ptsCap x28_val hfsp_align

/-- Shared `ProtoPolynomialDecoder` inline deallocation at `+5368 -> +7084`:
    when `x21 = ptsCap`, `x20 = ptsPtr`, `x22 = BitVec.ofNat 64 pts.length`, deallocates all `Vec<u8>`
    elements in `pts` and the `pts` buffer itself, then jumps to `+7084`. -/
theorem v9_states_from_pb_dealloc_proto_decoder_5368_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s : State) (fsp out ptsPtr ptsCap x28_val : BitVec 64)
    (pts : List (List (BitVec 8))) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 5368#64)
    (hrun : s.status = .Running)
    (hpres : v9_Saved5368Preserved s0 s fsp out ptsPtr ptsCap x28_val)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 pts.length) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 7084#64) s
      ((if ptsCap = 0 then emp
        else A.repAlloc.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢ A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v9_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap x28_val) := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc_ok
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  have hloop := v9_proto_decoder_dealloc_loop_5392_of_sub_placed
    hdealloc_ok s0 fsp out ptsPtr ptsCap x28_val hfsp_align
  refine seq_clean_evs (mid := lsmpl.base 333 + 5416#64)
    (P_evs := fun evs1 sm =>
      (if ptsCap = 0#64 then emp
       else A.repAlloc.live ptsPtr (ptsCap.toNat * 24) 8 ∗ memRegion ptsPtr (ptsCap.toNat * 24)) ∗
      A.pool lim (M.stepEvents evs1 st) sm ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => v9_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap x28_val)
    ?_ ?_
  · cases pts with
    | nil =>
      rcases hpres with ⟨hsp, hx19, hx20, hx21, hx28, htrace⟩
      simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, arrayAt, emp_sepConj] at hx22 ⊢
      change s.pc = (blkPl_333).base + 5368#64 at hpc
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 5416#64) s _ _
      apply sepWP_evs_nil
      simp only [M.stepEvents_nil]
      wp_steps_sync_333 ((blkPl_333).base + 5416#64)
      try simp only [State.setMem_setMem]
      refine align_pre_st (by (try simp only [wp_norm, arm64_norm]); try sep_ac_rfl) ?_
      wp_done
    | cons bs tl =>
      have hlen_pos : 0 < (bs :: tl).length := by simp
      have hlen_lt : (bs :: tl).length * 24 < 2 ^ 63 := by
        have : (bs :: tl).length * 24 ≤ ptsCap.toNat * 24 := Nat.mul_le_mul_right 24 hpts_le
        omega
      have hne0 := ofNat_beq_zero_false_24 hlen_pos hlen_lt
      have hcap_ne : ptsCap ≠ 0#64 := by intro hc0; rw [hc0] at hpts_le; simp at hpts_le
      simp only [BitVec.ofNat_eq_ofNat, hcap_ne, ↓reduceIte]
      refine seq_clean_st (mid := lsmpl.base 333 + 5392#64)
        (P_mid := fun sm =>
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr (bs :: tl) ∗
            A.pool lim st sm ∗ stackAt fsp allocHookStack ∗
            (A.repAlloc.live ptsPtr (ptsCap.toNat * 24) 8 ∗
             memRegion (ptsPtr + BitVec.ofNat 64 ((bs :: tl).length * 24))
               ((ptsCap.toNat - (bs :: tl).length) * 24) ∗
             Frame))
        (Q := fun sm => v9_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap x28_val ∧
          sm.readReg64 .x22 = BitVec.ofNat 64 (bs :: tl).length ∧
          sm.readReg64 .x23 = ptsPtr + 8#64)
        ?_ ?_
      · rcases hpres with ⟨hsp, hx19, hx20, hx21, hx28, htrace⟩
        change s.pc = (blkPl_333).base + 5368#64 at hpc
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 5392#64) s _ _
        wp_steps_sync_333 ((blkPl_333).base + 5392#64)
        try simp only [State.setMem_setMem]
        refine align_pre_st (by (try simp only [wp_norm, arm64_norm]); try sep_ac_rfl) ?_
        wp_done
      · intro s_loop hpc_loop hrun_loop ⟨hpres_loop, hx22_loop, hx23_loop⟩
        have hlp := hloop (bs :: tl) st ptsPtr s_loop
          (A.repAlloc.live ptsPtr (ptsCap.toNat * 24) 8 ∗
           memRegion (ptsPtr + BitVec.ofNat 64 ((bs :: tl).length * 24))
             ((ptsCap.toNat - (bs :: tl).length) * 24) ∗
           Frame)
          (List.cons_ne_nil _ _) hlen_lt hpc_loop hrun_loop hpres_loop
          hx22_loop hx23_loop
        refine SepWP.mono hlp fun sm _Pm _ _ ⟨evs1, hevs1, hPm, hpres_m⟩ => ?_
        refine ⟨evs1, hevs1, Entails.trans hPm ?_, hpres_m⟩
        have hsplit : ptsCap.toNat * 24 =
            (bs :: tl).length * 24 + (ptsCap.toNat - (bs :: tl).length) * 24 := by
          rw [← Nat.add_mul]; congr 1; omega
        have hbound : (bs :: tl).length * 24 + (ptsCap.toNat - (bs :: tl).length) * 24 ≤ 2 ^ 64 := by
          rw [← hsplit]; omega
        have hjoin : A.repAlloc.live ptsPtr (ptsCap.toNat * 24) 8 ∗
            memRegion ptsPtr ((bs :: tl).length * 24) ∗
            memRegion (ptsPtr + BitVec.ofNat 64 ((bs :: tl).length * 24))
              ((ptsCap.toNat - (bs :: tl).length) * 24) ⊢
            A.repAlloc.live ptsPtr (ptsCap.toNat * 24) 8 ∗ memRegion ptsPtr (ptsCap.toNat * 24) := by
          rw [hsplit, ProofLib.memRegion_split ptsPtr ((bs :: tl).length * 24)
            ((ptsCap.toNat - (bs :: tl).length) * 24) hbound]
          exact Entails.of_eq (by sep_ac_rfl)
        refine Entails.trans
          (Entails.of_eq (show _ =
            (A.repAlloc.live ptsPtr (ptsCap.toNat * 24) 8 ∗
             memRegion ptsPtr ((bs :: tl).length * 24) ∗
             memRegion (ptsPtr + BitVec.ofNat 64 ((bs :: tl).length * 24))
               ((ptsCap.toNat - (bs :: tl).length) * 24)) ∗
            A.pool lim (M.stepEvents evs1 st) sm ∗ stackAt fsp allocHookStack ∗ Frame by sep_ac_rfl))
          (sepConj_mono_left hjoin)
  · intro evs1 s3 hevs1 hpc3 hrun3 ⟨hsp_3, hx19_3, hx20_3, hx21_3, hx28_3, htrace_3⟩
    let st1 := M.stepEvents evs1 st
    have hsp_align_s3 : (s3.sp &&& 15#64 == 0#64) = true := hsp_3 ▸ hfsp_align
    change s3.pc = (blkPl_333).base + 5416#64 at hpc3
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 7084#64) s3 _ _
    dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
      BitVec.ofNat_eq_ofNat] at hdealloc_fo ⊢
    by_cases hc : ptsCap = 0#64
    · have hc_beq : (ptsCap == 0#64) = true := by rw [beq_iff_eq]; exact hc
      simp only [hc, ↓reduceIte, emp_sepConj, sepConj_emp] at hx21_3 ⊢
      have hfin : SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 7084#64) s3
          (A.pool lim st1 s3 ∗ stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ A.pool lim st1 sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
            v9_Saved5368Preserved s0 sm fsp out ptsPtr 0#64 x28_val) := by
        wp_steps_sync_333 ((blkPl_333).base + 7084#64)
        try simp only [State.setMem_setMem]
        refine align_pre_st (by (try simp only [wp_norm, arm64_norm]); try sep_ac_rfl) ?_
        wp_done
      exact SepWP.mono hfin fun _ _ _ _ ⟨hp, hq⟩ => ⟨evs1, hevs1, hp, hq⟩
    · have hc_beq : ¬((ptsCap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
      have hlsl := cap_mul_24 hpts_cap_lt
      simp only [hc, ↓reduceIte]
      have hfin : SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 7084#64) s3
          ((A.live ptsPtr (ptsCap.toNat * 24) 8 ∗ memRegion ptsPtr (ptsCap.toNat * 24)) ∗
            A.pool lim st1 s3 ∗ stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ A.pool lim (M.stepEvents (rustDeallocEvents (ptsCap.toNat * 24) 8) st1) sm ∗
              stackAt fsp allocHookStack ∗ Frame) ∧
            v9_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap x28_val) := by
        wp_steps_sync_333 (lsρ spqrRustDeallocSym)
        try simp only [State.setMem_setMem]
        wp_call hdealloc_fo (ptsPtr, ptsCap.toNat * 24, 8, st1)
        have hacp : AllocCallPreserved s3 sf := by
          simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
        have htr_sf : sf.trace = s0.trace := hacp.2.1.trans htrace_3.1
        have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
          ‹calleeSavedVRegs sf = calleeSavedVRegs s3›.trans htrace_3.2
        wp_steps_sync_333 ((blkPl_333).base + 7084#64)
        try simp only [State.setMem_setMem]
        refine align_pre_st (by (try simp only [wp_norm, arm64_norm, hsp_3]); try sep_ac_rfl) ?_
        wp_done
      refine SepWP.mono hfin fun sm Pm _ _ ⟨hPm, hpres_m⟩ => ?_
      refine ⟨evs1 ++ rustDeallocEvents (ptsCap.toNat * 24) 8,
        hevs1.append (FreeOnlyEvs.singleton 8 (ptsCap.toNat * 24)), ?_, hpres_m⟩
      have hst_eq : M.stepEvents (rustDeallocEvents (ptsCap.toNat * 24) 8) st1 =
          M.stepEvents (evs1 ++ rustDeallocEvents (ptsCap.toNat * 24) 8) st := by
        dsimp only [st1]; rw [M.stepEvents_append]
      rwa [← hst_eq]

theorem v9_states_from_pb_dealloc_proto_decoder_5368_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s : State) (fsp out ptsPtr ptsCap x28_val : BitVec 64)
    (pts : List (List (BitVec 8))) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 5368#64)
    (hrun : s.status = .Running)
    (hpres : v9_Saved5368Preserved s0 s fsp out ptsPtr ptsCap x28_val)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 pts.length) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 7084#64) s
      ((if ptsCap = 0 then emp
        else A.repAlloc.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢ A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v9_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap x28_val) :=
  v9_states_from_pb_dealloc_proto_decoder_5368_of_sub_placed
    (v9_sub_ok_dealloc_of_dealloc_placed hdealloc)
    st s0 s fsp out ptsPtr ptsCap x28_val pts Frame
    hfsp_align hpts_le hpts_cap_lt hpc hrun hpres hx22

theorem v9_states_from_pb_dealloc_proto_decoder_5368_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s : State) (fsp out ptsPtr ptsCap x28_val : BitVec 64)
    (pts : List (List (BitVec 8))) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 5368#64)
    (hrun : s.status = .Running)
    (hpres : v9_Saved5368Preserved s0 s fsp out ptsPtr ptsCap x28_val)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 pts.length) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 7084#64) s
      ((if ptsCap = 0 then emp
        else A.repAlloc.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢ A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v9_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap x28_val) :=
  v9_states_from_pb_dealloc_proto_decoder_5368_of_dealloc_placed
    hA.dealloc st s0 s fsp out ptsPtr ptsCap x28_val pts Frame
    hfsp_align hpts_le hpts_cap_lt hpc hrun hpres hx22

theorem v9_saved5368Preserved_stripS {keep : BitVec 64 → Bool} {s0 s : State}
    {fsp out ptsPtr ptsCap x28_val : BitVec 64} :
    v9_Saved5368Preserved s0 (ProofLib.stripS keep s) fsp out ptsPtr ptsCap x28_val ↔
      v9_Saved5368Preserved s0 s fsp out ptsPtr ptsCap x28_val := by
  simp [v9_Saved5368Preserved, TraceCalleeSaved]

/-- `VmPreserved`-strengthened `Option<ProtoPolynomialDecoder>` inline deallocation at
    `+5360 -> +7084` when `x21 = noneCap`. -/
theorem v9_states_from_pb_dealloc_none_proto_decoder_5360_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out ptsPtr x28_val : BitVec 64) (P : SepProp)
    (hpc : s.pc = lsmpl.base 333 + 5360#64)
    (hrun : s.status = .Running)
    (hpres : v9_Saved5368Preserved s0 s fsp out ptsPtr noneCap x28_val) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 7084#64) s P
      (fun sm Pm =>
        (Pm ⊢ P) ∧
        VmPreserved s sm ∧
        v9_Saved5368Preserved s0 sm fsp out ptsPtr noneCap x28_val) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant9aPlaced.v9_states_from_pb_dealloc_none_proto_decoder_5360_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
      fsp out ptsPtr x28_val P
      (by simpa using hpc) (by simpa using hrun)
      (v9_saved5368Preserved_stripS.mpr hpres))
    fun sm Pm hvm ⟨hPm, hpres_m⟩ =>
      ⟨hPm, hvm, v9_saved5368Preserved_stripS.mp hpres_m⟩

theorem v9_states_from_pb_dealloc_none_proto_decoder_5360_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out ptsPtr x28_val : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = lsmpl.base 333 + 5360#64)
    (hrun : s.status = .Running)
    (hpres : v9_Saved5368Preserved s0 s fsp out ptsPtr noneCap x28_val) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 7084#64) s
      (A.pool lim st s ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ A.pool lim st sm ∗ Rest) ∧
        VmPreserved s sm ∧
        v9_Saved5368Preserved s0 sm fsp out ptsPtr noneCap x28_val) := by
  have hwp := v9_states_from_pb_dealloc_none_proto_decoder_5360_placed (ext := ext)
    s0 s fsp out ptsPtr x28_val (A.pool lim st s ∗ Rest) hpc hrun hpres
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hpres_m⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨hPm, hvm, hpres_m⟩

theorem v9_states_from_pb_dealloc_some_proto_decoder_5360_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s : State) (fsp out ptsPtr ptsCap x28_val : BitVec 64)
    (pts : List (List (BitVec 8))) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 5360#64)
    (hrun : s.status = .Running)
    (hpres : v9_Saved5368Preserved s0 s fsp out ptsPtr ptsCap x28_val)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 pts.length) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 7084#64) s
      ((if ptsCap = 0 then emp
        else A.repAlloc.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢ A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v9_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap x28_val) := by
  refine seq_clean_st (mid := lsmpl.base 333 + 5368#64)
    (P_mid := fun sm =>
      (if ptsCap = 0 then emp
       else A.repAlloc.live ptsPtr (ptsCap.toNat * 24) 8 ∗
         arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pts ∗
         memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
           ((ptsCap.toNat - pts.length) * 24)) ∗
      A.pool lim st sm ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => v9_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap x28_val ∧
      sm.readReg64 .x22 = BitVec.ofNat 64 pts.length)
    ?_ ?_
  · rcases hpres with ⟨hsp, hx19, hx20, hx21, hx28, htrace⟩
    have hne := v9_ptsCap_add_one_ne_zero hpts_cap_lt
    change s.pc = (blkPl_333).base + 5360#64 at hpc
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 5368#64) s _ _
    wp_steps_sync_333 ((blkPl_333).base + 5368#64)
    try simp only [State.setMem_setMem]
    refine align_pre_st (by (try simp only [wp_norm, arm64_norm]); try sep_ac_rfl) ?_
    wp_done
  · intro s1 hpc1 hrun1 ⟨hpres1, hx22_1⟩
    exact v9_states_from_pb_dealloc_proto_decoder_5368_of_sub_placed hdealloc_ok
      st s0 s1 fsp out ptsPtr ptsCap x28_val pts Frame
      hfsp_align hpts_le hpts_cap_lt hpc1 hrun1 hpres1 hx22_1

theorem v9_states_from_pb_dealloc_some_proto_decoder_5360_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s : State) (fsp out ptsPtr ptsCap x28_val : BitVec 64)
    (pts : List (List (BitVec 8))) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 5360#64)
    (hrun : s.status = .Running)
    (hpres : v9_Saved5368Preserved s0 s fsp out ptsPtr ptsCap x28_val)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 pts.length) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 7084#64) s
      ((if ptsCap = 0 then emp
        else A.repAlloc.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢ A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v9_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap x28_val) :=
  v9_states_from_pb_dealloc_some_proto_decoder_5360_of_sub_placed
    (v9_sub_ok_dealloc_of_dealloc_placed hdealloc)
    st s0 s fsp out ptsPtr ptsCap x28_val pts Frame
    hfsp_align hpts_le hpts_cap_lt hpc hrun hpres hx22

theorem v9_states_from_pb_dealloc_some_proto_decoder_5360_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s : State) (fsp out ptsPtr ptsCap x28_val : BitVec 64)
    (pts : List (List (BitVec 8))) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 5360#64)
    (hrun : s.status = .Running)
    (hpres : v9_Saved5368Preserved s0 s fsp out ptsPtr ptsCap x28_val)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 pts.length) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 7084#64) s
      ((if ptsCap = 0 then emp
        else A.repAlloc.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢ A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v9_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap x28_val) :=
  v9_states_from_pb_dealloc_some_proto_decoder_5360_of_dealloc_placed
    hA.dealloc st s0 s fsp out ptsPtr ptsCap x28_val pts Frame
    hfsp_align hpts_le hpts_cap_lt hpc hrun hpres hx22

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9aPlacedBudgetAux

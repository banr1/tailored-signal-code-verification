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
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10aPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch2Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10a
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Variant 10 (`Ct2Sampled`, `+1632`) — Error & Cleanup Paths

Proves `VmPreserved`-strengthened and `FreeOnlyEvs`-threading Block `333` drop/dealloc bridges, OOM
cold path (`+11572`), shared error epilogues (`+2084`, `+2064`), and `Authenticator` cleanup
deallocation paths (`+5844`, `+7236`, `+7212`, `+5820`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10aPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkLib_eq_333 blkPC_333 blkPl_333
   lsProg_333 lsmpl lsρ withLsCodeLoaded withMemEq)
open CryptoVerification.LibsignalSpqrV1 (Error ProtoPolynomialEncoder)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalTripleRatchet (allocFailedIn_of_eq)
open CryptoVerification.RustHeap (RustAlloc allocFailedEvent allocHookStack)
open CryptoVerification.SpqrV1.Alloc (spqrHandleErrorSym spqr_externAt?_of_mem)
open CryptoVerification.SpqrV1.Drop
  (DropProtoPolyEncoderGhost cap_add_one_beq_zero_false chunkedStatesSize dropStack48
   optProtoPolyEncoder_none_entails_memRegion_56 optProtoPolynomialEncoderAt_none'
   optProtoPolynomialEncoderAt_some' vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Poly
  (optProtoPolynomialEncoderAt protoPolynomialEncoderAt protoPolynomialEncoderSize)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved resultChunkedStatesAt sp_sub_2400_align spqrErrorByte
   stackAt_encoderFromPb_split_allocHook statesFromPbOnPanic statesFromPbSavedCells
   statesFromPbStack v1_bv_add_add_lit v1_bv_sub_sub_lit v1_shl8_extract_0_8
   v1_stackAt_encoder_split_dropStack48)
open CryptoVerification.SpqrV1.Unchunked
  (extractLsb'_0_64_append extractLsb'_64_64_append)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget
   VmPreserved rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget (dropProtoPolyEncoderSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (isTotalTrapHooks_withPanics_vmTrapHooks sepWP_lsBlock_vmPreserved
   stripS_calleeSavedVRegs stripS_pc stripS_readReg64 stripS_sp stripS_status stripS_trace
   vmTrapHooks)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
  (FromPbAllocHooksPlacedBudget spqrRustDeallocSym)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
  (align_pre_st deallocFreeOnlySpec sepWP_evs_dealloc sepWP_evs_nil seq_clean_evs seq_clean_st
   subroutine_ok_deallocFreeOnly)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
  (FromPbAllocHooksBudget seq_clean_evs_lscl seq_clean_lscl_st
   v1_deallocFreeOnly_ok_at_statesFromPb_placed v1_dealloc_ok_at_statesFromPb_placed
   v1_dealloc_ok_of_dealloc_placed v1_dealloc_ok_of_placedHooks
   v1_drop_glue_proto_poly_encoder_ok_at_statesFromPb_placed
   v1_drop_glue_proto_poly_encoder_ok_of_dealloc_placed withMemEq_of_withLsCodeLoaded)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux
  (blk333_noSvc0 entails_pre_st)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget (blk333_safeVm)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm, local wp_norm]
  v1_bv_sub_sub_lit v1_shl8_extract_0_8 v1_bv_add_add_lit

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

/-! ## 1. Subroutine Bridges and OOM Cold Path (`+11572`) -/

/-- Budget-threaded subroutine contract for `core::ptr::drop_in_place<ProtoPolynomialEncoder>`
    (Block `271`) on `lsProg_333` from a `__rust_dealloc` hook contract. -/
theorem v10_sub_ok_drop_proto_poly_encoder_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 271)
      (withLsCodeLoaded lsmpl (dropProtoPolyEncoderSpec M A lim)) :=
  v1_drop_glue_proto_poly_encoder_ok_of_dealloc_placed hdealloc

theorem v10_sub_ok_drop_proto_poly_encoder_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 271)
      (withLsCodeLoaded lsmpl (dropProtoPolyEncoderSpec M A lim)) :=
  v1_drop_glue_proto_poly_encoder_ok_at_statesFromPb_placed hA

/-- Budget-threaded subroutine contract for `alloc::__rust_dealloc` on Block `333` from `HookSat`. -/
theorem v10_sub_ok_dealloc_125316_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym)
      (rustCliDeallocBudgetSpec M A lim) :=
  v1_dealloc_ok_of_dealloc_placed hdealloc

theorem v10_sub_ok_dealloc_125316_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym)
      (rustCliDeallocBudgetSpec M A lim) :=
  v1_dealloc_ok_of_placedHooks hA

theorem v10_sub_ok_dealloc_125316_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym)
      (rustCliDeallocBudgetSpec M A lim) :=
  v1_dealloc_ok_at_statesFromPb_placed hA

/-- `FreeOnlyEvs`-specialized `__rust_dealloc` contract on Block `333` from `FromPbAllocHooksBudget`. -/
theorem v10_sub_ok_deallocFreeOnly_125316_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym)
      (deallocFreeOnlySpec M A lim) :=
  v1_deallocFreeOnly_ok_at_statesFromPb_placed hA

/-- Shared OOM cold path at `+11572` (`mov w0, #1; mov x1, x28; bl handle_error`) from an explicit
    `spqrHandleErrorSym` panic binding. -/
theorem v10_states_from_pb_oom_11572_of_panic_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hpanic_ok : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (s0 s : State) (target_pc : BitVec 64) (P R : SepProp)
    (Q : State → SepProp → Prop)
    (hpc : s.pc = lsmpl.base 333 + 11572#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) target_pc s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) := by
  have hpanic :
      ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)).externAt?
        (lsρ spqrHandleErrorSym) = some Rust.panicked :=
    (spqr_externAt?_of_mem (sym := spqrHandleErrorSym)).trans hpanic_ok
  change s.pc = (blkPl_333).base + _ at hpc
  change SepWPp ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)) target_pc s P Q _
  apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
  simpa only [statesFromPbOnPanic, sepConj_assoc] using
    allowPanic_panicked
      (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm

theorem v10_states_from_pb_oom_11572_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 s : State) (target_pc : BitVec 64) (P R : SepProp) (Q : State → SepProp → Prop)
    (hpc : s.pc = lsmpl.base 333 + 11572#64) (hrun : s.status = .Running)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) target_pc s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) :=
  v10_states_from_pb_oom_11572_of_panic_placed hA.panic_ok s0 s target_pc P R Q hpc hrun htr

theorem v10_states_from_pb_oom_11572_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 s : State) (target_pc : BitVec 64) (P R : SepProp) (Q : State → SepProp → Prop)
    (hpc : s.pc = lsmpl.base 333 + 11572#64) (hrun : s.status = .Running)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) target_pc s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) :=
  v10_states_from_pb_oom_11572_of_panic_placed hA.panic_ok s0 s target_pc P R Q hpc hrun htr

/-! ## 2. Shared Error Epilogues at `+2084` and `+2064` -/

/-- `VmPreserved`-strengthened shared `Err(err)` exit at `+2084` (`lsmpl.base 333 + 2084 -> s0.x30`). -/
theorem v10_states_from_pb_err_2084_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (err : Error) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 2084#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : (s1.readReg64 .x21).extractLsb' 0 8 = spqrErrorByte err)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out (.error (.err err)) ∗
          Rest ∗ stackAt s0.sp statesFromPbStack) ∧
        VmPreserved s1 sf ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (LibsignalBinary.Proofs.SpqrV1.States.FromPb.v10_states_from_pb_err_2084_placed
      (A := A) (F := F) (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      out err Rest hsp0_align
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1) (by simpa using hx21_1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sf Pf hvm ⟨hPf, hsp_f, hcc_f, htr_f⟩ => ⟨hPf, hvm, hsp_f, hcc_f, htr_f⟩

theorem v10_states_from_pb_err_2084_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (err : Error) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 2084#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : (s1.readReg64 .x21).extractLsb' 0 8 = spqrErrorByte err)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool lim st s1 ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err err)) ∗
          A.pool lim st sf ∗ Rest ∗ stackAt s0.sp statesFromPbStack) ∧
        VmPreserved s1 sf ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hwp := v10_states_from_pb_err_2084_placed (A := A.repAlloc) (F := F) (ext := ext)
    s0 s1 out err (A.pool lim st s1 ∗ Rest) hsp0_align hpc1 hrun1 hsp1 hx19_1 hx21_1 htr1
  refine SepWP.mono hwp fun sf Pf _ _ ⟨hPf, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPf
  exact ⟨Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hvm, hrest⟩

/-- Shared `+2064` error epilogue (`lsmpl.base 333 + 2064 -> s0.x30`) from an explicit Block-`271`
    `withLsCodeLoaded` drop-glue contract: drops `optEnc` at `encAddr` into `memRegion encAddr 56`
    emitting `FreeOnlyEvs` and returns `Err(.stateDecode)`. -/
theorem v10_states_from_pb_err_2064_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdrop_cl : subroutine_ok (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 271)
      (withLsCodeLoaded lsmpl (dropProtoPolyEncoderSpec M A lim)))
    (st : M.σ) (s0 s1 : State) (out encAddr : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (Rest : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 2064#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = encAddr)
    (hx22_1 : match optEnc with
      | none => s1.readReg64 .x22 = noneCap
      | some _ => (s1.readReg64 .x22).toNat < 2 ^ 63)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        optProtoPolynomialEncoderAt A.repAlloc encAddr optEnc ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            memRegion encAddr 56 ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            Rest ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧
          CalleeSavedPreserved s0 sf ∧
          sf.trace = s0.trace) := by
  cases optEnc with
  | none =>
    rw [optProtoPolynomialEncoderAt_none']
    refine seq_clean_st
      (mid := lsmpl.base 333 + 2084#64)
      (P_mid := fun sm =>
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        A.pool lim st sm ∗
        (memRegion encAddr 56 ∗ Rest))
      (Q := fun sm =>
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = 0#64 ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · dsimp only [noneCap, BitVec.ofNat_eq_ofNat] at hpc1 hx22_1 ⊢
      change s1.pc = (blkPl_333).base + 2064#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 2084#64) s1 _ _
      wp_steps_sync_333 ((blkPl_333).base + 2084#64)
      simp only [State.setMem_setMem]
      have hm := optProtoPolyEncoder_none_entails_memRegion_56 encAddr
      dsimp only [noneCap] at hm
      refine entails_pre_st ?_ ?_
      · intro sc hsc
        rw [← hsc]
        refine Entails.trans (Entails.of_eq (show _ =
          ((encAddr ↦₆₄ noneCap) ∗ memRegion (encAddr + 8#64) 48) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           memRegion (s0.sp - 2400#64) 2304 ∗
           statesFromPbSavedCells s0 ∗
           memRegion out chunkedStatesSize ∗
           A.pool lim st sc ∗ Rest) by
          dsimp only [noneCap]
          sep_ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hm) (Entails.of_eq (by sep_ac_rfl))
      · wp_done
    · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx21_2, htr2⟩
      have hx21_b : (s2.readReg64 .x21).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
        rw [hx21_2]; rfl
      have hep := v10_states_from_pb_err_2084_placed_budget A lim st (F := F) (ext := ext)
        s0 s2 out .stateDecode (memRegion encAddr 56 ∗ Rest)
        hsp0_align hpc2 hrun2 hsp2 hx19_2 hx21_b htr2
      refine SepWP.mono hep fun sf Pf _ _ ⟨hPf, _, hsp_f, hcc_f, htr_f⟩ => ?_
      refine ⟨[], FreeOnlyEvs.nil, ?_, hsp_f, hcc_f, htr_f⟩
      simpa only [M.stepEvents_nil] using Entails.trans hPf (Entails.of_eq (by sep_ac_rfl))
  | some enc =>
    rw [optProtoPolynomialEncoderAt_some']
    have hne_none := cap_add_one_beq_zero_false hx22_1
    have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
      sp_sub_2400_align s0.sp hsp0_align
    refine seq_clean_lscl_st hcl1
      (mid := lsmpl.base 271)
      (P_mid := fun sm =>
        protoPolynomialEncoderAt A.repAlloc encAddr enc ∗
        A.pool lim st sm ∗
        stackAt (s0.sp - 2400#64) dropStack48 ∗
        (memRegion (s0.sp - 2400#64 - 5152#64) 1008 ∗
         memRegion (s0.sp - 2400#64) 2304 ∗
         statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗
         Rest))
      (Q := fun sm =>
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x0 = encAddr ∧
        sm.readReg64 .lr = (blkPl_333).base + 2084#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = 0#64 ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · rw [v1_stackAt_encoder_split_dropStack48 (s0.sp - 2400#64)]
      change s1.pc = (blkPl_333).base + 2064#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        (lsmpl.base 271) s1 _ _
      wp_steps_sync_333 (lsmpl.base 271)
      simp only [State.setMem_setMem]
      refine align_pre_st (by sep_ac_rfl) ?_
      wp_done
    · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx0_2, hlr_2, hx19_2, hx21_2, htr2⟩
      have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := hsp2 ▸ hfsp_align
      have hdrop : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          (lsmpl.base 271) (withMemEq s2.mem (dropProtoPolyEncoderSpec M A lim)) :=
        withMemEq_of_withLsCodeLoaded hdrop_cl hcl2
      simp only [withMemEq, dropProtoPolyEncoderSpec] at hdrop
      refine seq_clean_evs
        (mid := lsmpl.base 333 + 2084#64)
        (P_evs := fun evs sm =>
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (s0.sp - 2400#64) 2304 ∗
          statesFromPbSavedCells s0 ∗
          memRegion out chunkedStatesSize ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          (memRegion encAddr 56 ∗ Rest))
        (Q := fun sm =>
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x21 = 0#64 ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 2084#64) s2 _ _
        rw [show stackAt (s0.sp - 2400#64) dropStack48 = stackAt s2.sp dropStack48 from hsp2 ▸ rfl]
        wp_call hdrop ((⟨encAddr, enc⟩ : DropProtoPolyEncoderGhost), st)
        rw [hsp2]
        have hevs_w : FreeOnlyEvs w := ‹_›
        have hacp_w : AllocCallPreserved s2 sf := by
          simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
        have hsp_sf : sf.sp = s0.sp - 2400#64 := ‹sf.sp = s2.sp›.trans hsp2
        have hx19_sf : sf.readReg64 .x19 = out :=
          ‹sf.readReg64 (Reg.gpr 19#5) = s2.readReg64 (Reg.gpr 19#5)›.trans hx19_2
        have hx21_sf : sf.readReg64 .x21 = 0#64 :=
          ‹sf.readReg64 (Reg.gpr 21#5) = s2.readReg64 (Reg.gpr 21#5)›.trans hx21_2
        have htr_sf : sf.trace = s0.trace := hacp_w.2.1.trans htr2.1
        have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
          ‹calleeSavedVRegs sf = calleeSavedVRegs s2›.trans htr2.2
        refine SepWP.mono
          (post := fun sm Pm =>
            (Pm ⊢
              stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
              memRegion (s0.sp - 2400#64) 2304 ∗
              statesFromPbSavedCells s0 ∗
              memRegion out chunkedStatesSize ∗
              A.pool lim (M.stepEvents w st) sm ∗
              (memRegion encAddr 56 ∗ Rest)) ∧
            sm.sp = s0.sp - 2400#64 ∧
            sm.readReg64 .x19 = out ∧
            sm.readReg64 .x21 = 0#64 ∧
            TraceCalleeSaved sm s0)
          ?_ (fun _ _ _ _ ⟨hp, hq⟩ => ⟨w, hevs_w, hp, hq⟩)
        refine entails_pre_st ?_ ?_
        · intro sc hsc
          have h7552 : s0.sp - 2400#64 - 5152#64 = s0.sp - 7552#64 := by bv_omega
          rw [← hsc, v1_stackAt_encoder_split_dropStack48 (s0.sp - 2400#64), h7552]
          dsimp only [protoPolynomialEncoderSize]
          exact Entails.of_eq (by sep_ac_rfl)
        · wp_done
      · intro evs s3 hevs hpc3 hrun3 ⟨hsp3, hx19_3, hx21_3, htr3⟩
        have hx21_b : (s3.readReg64 .x21).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
          rw [hx21_3]; rfl
        have hep := v10_states_from_pb_err_2084_placed_budget A lim (M.stepEvents evs st)
          (F := F) (ext := ext) s0 s3 out .stateDecode (memRegion encAddr 56 ∗ Rest)
          hsp0_align hpc3 hrun3 hsp3 hx19_3 hx21_b htr3
        refine SepWP.mono hep fun sf Pf _ _ ⟨hPf, _, hsp_f, hcc_f, htr_f⟩ =>
          ⟨evs, hevs, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hsp_f, hcc_f, htr_f⟩

theorem v10_states_from_pb_err_2064_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (out encAddr : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (Rest : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 2064#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = encAddr)
    (hx22_1 : match optEnc with
      | none => s1.readReg64 .x22 = noneCap
      | some _ => (s1.readReg64 .x22).toNat < 2 ^ 63)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        optProtoPolynomialEncoderAt A.repAlloc encAddr optEnc ∗ A.pool lim st s1 ∗ Rest)
      (fun sf Pf => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
          memRegion encAddr 56 ∗ A.pool lim (M.stepEvents evs st) sf ∗
          Rest ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v10_states_from_pb_err_2064_of_sub_placed
    (v10_sub_ok_drop_proto_poly_encoder_of_dealloc_placed hdealloc)
    st s0 s1 out encAddr optEnc Rest hcl1 hsp0_align hpc1 hrun1 hsp1 hx19_1 hx23_1 hx22_1 htr1

theorem v10_states_from_pb_err_2064_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out encAddr : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (Rest : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 2064#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = encAddr)
    (hx22_1 : match optEnc with
      | none => s1.readReg64 .x22 = noneCap
      | some _ => (s1.readReg64 .x22).toNat < 2 ^ 63)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        optProtoPolynomialEncoderAt A.repAlloc encAddr optEnc ∗ A.pool lim st s1 ∗ Rest)
      (fun sf Pf => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
          memRegion encAddr 56 ∗ A.pool lim (M.stepEvents evs st) sf ∗
          Rest ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v10_states_from_pb_err_2064_of_dealloc_placed hA.dealloc
    st s0 s1 out encAddr optEnc Rest hcl1 hsp0_align hpc1 hrun1 hsp1 hx19_1 hx23_1 hx22_1 htr1

/-! ## 3. Shared Error-Cleanup Deallocation Paths at `+5844`, `+7236`, `+7212`, and `+5820` -/

/-- `VmPreserved`-strengthened shared `+5844` transition (`+5844 -> +2084`): `mov x21, xzr; b +2084`. -/
theorem v10_states_from_pb_err_5844_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (P : SepProp)
    (hpc1 : s1.pc = lsmpl.base 333 + 5844#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 2084#64) s1 P
      (fun sm Pm =>
        (Pm ⊢ P) ∧
        VmPreserved s1 sm ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (LibsignalBinary.Proofs.SpqrV1.States.FromPb.v10_states_from_pb_err_5844_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      out P (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1) ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sm Pm hvm ⟨hPm, hsp_m, hx19_m, hx21_m, htr_m⟩ =>
      ⟨hPm, hvm, hsp_m, hx19_m, hx21_m, htr_m⟩

theorem v10_states_from_pb_err_5844_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (Rest : SepProp)
    (hpc1 : s1.pc = lsmpl.base 333 + 5844#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 2084#64) s1
      (A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ A.pool lim st sm ∗ Rest) ∧
        VmPreserved s1 sm ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  have hwp := v10_states_from_pb_err_5844_placed (ext := ext)
    s0 s1 out (A.pool lim st s1 ∗ Rest)
    hpc1 hrun1 hsp1 hx19_1 htr1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨hPm, hvm, hrest⟩

/-- Shared `+7236` transition (`+7236 -> +2084`) from a Block-`333` `__rust_dealloc` contract:
    when `(ca2 == 0#64) = false`, deallocates `vecCapPtrDealloc A.repAlloc ca2 pa2` emitting
    `FreeOnlyEvs`, sets `x21 = 0`, and jumps to `+2084`. -/
theorem v10_states_from_pb_err_7236_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (out ca2 pa2 : BitVec 64) (Rest : SepProp)
    (hca2_ne : (ca2 == 0#64) = false)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 7236#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx26_1 : s1.readReg64 .x26 = ca2)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 2084#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
            A.pool lim (M.stepEvents evs st) sm ∗
            Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x21 = 0#64 ∧
          TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    sp_sub_2400_align s0.sp hsp0_align
  have hdealloc_fo : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (deallocFreeOnlySpec M A lim) :=
    subroutine_ok_deallocFreeOnly hdealloc_ok
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
    BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc1 ⊢
  simp only [hca2_ne, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
  rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
  change s1.pc = (blkPl_333).base + 7236#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 2084#64) s1 _ _
  apply sepWP_evs_dealloc ca2.toNat 1
  wp_steps_sync_333 (lsρ spqrRustDeallocSym)
  simp only [State.setMem_setMem]
  wp_call hdealloc_fo (pa2, ca2.toNat, 1, st)
  have hacp1 : AllocCallPreserved s1 sf := by
    simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
  have htr_sf : sf.trace = s0.trace := hacp1.2.1.trans htr1.1
  have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
    ‹calleeSavedVRegs sf = calleeSavedVRegs s1›.trans htr1.2
  wp_steps_sync_333 ((blkPl_333).base + 2084#64)
  simp only [State.setMem_setMem]
  refine entails_pre_st ?_ ?_
  · intro sc hsc
    rw [← hsc, hsp1]
    simp only [arm64_norm]
    exact Entails.of_eq (by sep_ac_rfl)
  · wp_done

theorem v10_states_from_pb_err_7236_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (out ca2 pa2 : BitVec 64) (Rest : SepProp)
    (hca2_ne : (ca2 == 0#64) = false) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 7236#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx26_1 : s1.readReg64 .x26 = ca2) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 2084#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗ A.pool lim st s1 ∗ Rest)
      (fun sm Pm => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = 0#64 ∧ TraceCalleeSaved sm s0) :=
  v10_states_from_pb_err_7236_of_sub_placed
    (v10_sub_ok_dealloc_125316_of_dealloc_placed hdealloc)
    st s0 s1 out ca2 pa2 Rest hca2_ne hsp0_align hpc1 hrun1 hsp1 hx19_1 hx26_1 htr1

theorem v10_states_from_pb_err_7236_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out ca2 pa2 : BitVec 64) (Rest : SepProp)
    (hca2_ne : (ca2 == 0#64) = false) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 7236#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx26_1 : s1.readReg64 .x26 = ca2) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 2084#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗ A.pool lim st s1 ∗ Rest)
      (fun sm Pm => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = 0#64 ∧ TraceCalleeSaved sm s0) :=
  v10_states_from_pb_err_7236_of_sub_placed hA.dealloc_ok
    st s0 s1 out ca2 pa2 Rest hca2_ne hsp0_align hpc1 hrun1 hsp1 hx19_1 hx26_1 htr1

theorem v10_states_from_pb_err_7236_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out ca2 pa2 : BitVec 64) (Rest : SepProp)
    (hca2_ne : (ca2 == 0#64) = false) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 7236#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx26_1 : s1.readReg64 .x26 = ca2) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 2084#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗ A.pool lim st s1 ∗ Rest)
      (fun sm Pm => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = 0#64 ∧ TraceCalleeSaved sm s0) :=
  v10_states_from_pb_err_7236_of_dealloc_placed hA.dealloc
    st s0 s1 out ca2 pa2 Rest hca2_ne hsp0_align hpc1 hrun1 hsp1 hx19_1 hx26_1 htr1

/-- Shared `+7212` error-cleanup path (`+7212 -> +2084`) from a Block-`333` `__rust_dealloc`
    contract: deallocates `vecCapPtrDealloc A.repAlloc ca1 pa1` (`[sp + 200] = ca1`, `x21 = pa1`)
    and `vecCapPtrDealloc A.repAlloc ca2 pa2` (`x26 = ca2`, `[sp + 184] = pa2`) emitting
    `FreeOnlyEvs`, sets `x21 = 0`, and reaches `+2084`. -/
theorem v10_states_from_pb_err_7212_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (out ca1 pa1 ca2 pa2 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 7212#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = pa1)
    (hx26_1 : s1.readReg64 .x26 = ca2)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 2084#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
        vecCapPtrDealloc A.repAlloc ca1 pa1 ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
            (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
            A.pool lim (M.stepEvents evs st) sm ∗
            Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x21 = 0#64 ∧
          TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    sp_sub_2400_align s0.sp hsp0_align
  have hdealloc_fo : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (deallocFreeOnlySpec M A lim) :=
    subroutine_ok_deallocFreeOnly hdealloc_ok
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  refine seq_clean_evs
    (mid := lsmpl.base 333 + 7232#64)
    (P_evs := fun evs1 sm =>
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
      (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
      vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
      A.pool lim (M.stepEvents evs1 st) sm ∗
      Rest)
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x26 = ca2 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
    dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
      BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc1 ⊢
    change s1.pc = (blkPl_333).base + 7212#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 7232#64) s1 _ _
    by_cases hca1 : (ca1 == 0#64) = true
    · simp only [hca1, ↓reduceIte, sepConj_emp, emp_sepConj]
      apply sepWP_evs_nil
      simp only [M.stepEvents_nil]
      wp_steps_sync_333 ((blkPl_333).base + 7232#64)
      simp only [State.setMem_setMem]
      refine entails_pre_st ?_ ?_
      · intro sc hsc
        rw [← hsc]
        simp only [arm64_norm]
        exact Entails.of_eq (by sep_ac_rfl)
      · wp_done
    · have hbeq : (ca1 == 0#64) = false := Bool.eq_false_iff.mpr hca1
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      apply sepWP_evs_dealloc ca1.toNat 1
      wp_steps_sync_333 (lsρ spqrRustDeallocSym)
      simp only [State.setMem_setMem]
      wp_call hdealloc_fo (pa1, ca1.toNat, 1, st)
      have hacp1 : AllocCallPreserved s1 sf := by
        simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
      have hsp_sf : sf.sp = s0.sp - 2400#64 := ‹sf.sp = s1.sp›.trans hsp1
      have htr_sf : sf.trace = s0.trace := hacp1.2.1.trans htr1.1
      have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
        ‹calleeSavedVRegs sf = calleeSavedVRegs s1›.trans htr1.2
      refine entails_pre_st ?_ ?_
      · intro sc hsc
        rw [← hsc, hsp1]
        simp only [arm64_norm]
        exact Entails.of_eq (by sep_ac_rfl)
      · wp_done
  ·
    intro evs1 s2 hevs1 hpc2 hrun2 ⟨hsp2, hx19_2, hx26_2, htr2⟩
    let st1 := M.stepEvents evs1 st
    by_cases hca2 : (ca2 == 0#64) = true
    · dsimp only [vecCapPtrDealloc]
      simp only [hca2, ↓reduceIte, sepConj_emp, emp_sepConj]
      refine seq_clean_st
        (mid := lsmpl.base 333 + 5844#64)
        (P_mid := fun sm =>
          A.pool lim st1 sm ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
           (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
           Rest))
        (Q := fun sm =>
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · change s2.pc = (blkPl_333).base + 7232#64 at hpc2
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 5844#64) s2 _ _
        wp_steps_sync_333 ((blkPl_333).base + 5844#64)
        simp only [State.setMem_setMem]
        refine align_pre_st (by sep_ac_rfl) ?_
        wp_done
      · intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, htr3⟩
        have h5844 := v10_states_from_pb_err_5844_placed_budget A lim st1 (ext := ext)
          s0 s3 out
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
           (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
           Rest)
          hpc3 hrun3 hsp3 hx19_3 htr3
        refine SepWP.mono h5844 fun sf Pf _ _ ⟨hPf, _, hsp_f, hx19_f, hx21_f, htr_f⟩ => ?_
        exact ⟨evs1, hevs1, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)),
          hsp_f, hx19_f, hx21_f, htr_f⟩
    · have hbeq : (ca2 == 0#64) = false := Bool.eq_false_iff.mpr hca2
      refine seq_clean_st
        (mid := lsmpl.base 333 + 7236#64)
        (P_mid := fun sm =>
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
          vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
          A.pool lim st1 sm ∗
          ((((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗ Rest))
        (Q := fun sm =>
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x26 = ca2 ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · change s2.pc = (blkPl_333).base + 7232#64 at hpc2
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 7236#64) s2 _ _
        wp_steps_sync_333 ((blkPl_333).base + 7236#64)
        simp only [State.setMem_setMem]
        refine align_pre_st (by sep_ac_rfl) ?_
        wp_done
      · intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx26_3, htr3⟩
        have h7236 := v10_states_from_pb_err_7236_of_sub_placed hdealloc_ok st1 s0 s3 out ca2 pa2
          ((((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗ Rest)
          hbeq hsp0_align hpc3 hrun3 hsp3 hx19_3 hx26_3 htr3
        refine SepWP.mono h7236 fun sf Pf _ _ ⟨evs2, hevs2, hPf, hsp_f, hx19_f, hx21_f, htr_f⟩ => ?_
        refine ⟨evs1 ++ evs2, FreeOnlyEvs.append hevs1 hevs2, ?_, hsp_f, hx19_f, hx21_f, htr_f⟩
        have hst_eq : M.stepEvents evs2 st1 = M.stepEvents (evs1 ++ evs2) st := by
          dsimp only [st1]
          rw [M.stepEvents_append]
        rw [hst_eq] at hPf
        exact Entails.trans hPf (Entails.of_eq (by sep_ac_rfl))

theorem v10_states_from_pb_err_7212_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (out ca1 pa1 ca2 pa2 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 7212#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = pa1) (hx26_1 : s1.readReg64 .x26 = ca2)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 2084#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ vecCapPtrDealloc A.repAlloc ca1 pa1 ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗ A.pool lim st s1 ∗ Rest)
      (fun sm Pm => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = 0#64 ∧ TraceCalleeSaved sm s0) :=
  v10_states_from_pb_err_7212_of_sub_placed
    (v10_sub_ok_dealloc_125316_of_dealloc_placed hdealloc)
    st s0 s1 out ca1 pa1 ca2 pa2 Rest hsp0_align hpc1 hrun1 hsp1 hx19_1 hx21_1 hx26_1 htr1

theorem v10_states_from_pb_err_7212_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out ca1 pa1 ca2 pa2 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 7212#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = pa1) (hx26_1 : s1.readReg64 .x26 = ca2)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 2084#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ vecCapPtrDealloc A.repAlloc ca1 pa1 ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗ A.pool lim st s1 ∗ Rest)
      (fun sm Pm => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = 0#64 ∧ TraceCalleeSaved sm s0) :=
  v10_states_from_pb_err_7212_of_sub_placed hA.dealloc_ok
    st s0 s1 out ca1 pa1 ca2 pa2 Rest hsp0_align hpc1 hrun1 hsp1 hx19_1 hx21_1 hx26_1 htr1

theorem v10_states_from_pb_err_7212_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out ca1 pa1 ca2 pa2 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 7212#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = pa1) (hx26_1 : s1.readReg64 .x26 = ca2)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 2084#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ vecCapPtrDealloc A.repAlloc ca1 pa1 ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗ A.pool lim st s1 ∗ Rest)
      (fun sm Pm => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = 0#64 ∧ TraceCalleeSaved sm s0) :=
  v10_states_from_pb_err_7212_of_dealloc_placed hA.dealloc
    st s0 s1 out ca1 pa1 ca2 pa2 Rest hsp0_align hpc1 hrun1 hsp1 hx19_1 hx21_1 hx26_1 htr1

/-- Shared `+5820` error-cleanup path (`+5820 -> +2084`) from a Block-`333` `__rust_dealloc`
    contract: deallocates `vecCapPtrDealloc A.repAlloc ca1 pa1` (`[sp + 200] = ca1`, `x21 = pa1`)
    and `vecCapPtrDealloc A.repAlloc ca2 pa2` (`x26 = ca2`, `[sp + 184] = pa2`) emitting
    `FreeOnlyEvs`, sets `x21 = 0`, and reaches `+2084`. -/
theorem v10_states_from_pb_err_5820_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (out ca1 pa1 ca2 pa2 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 5820#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = pa1)
    (hx26_1 : s1.readReg64 .x26 = ca2)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 2084#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
        vecCapPtrDealloc A.repAlloc ca1 pa1 ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
            (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
            A.pool lim (M.stepEvents evs st) sm ∗
            Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x21 = 0#64 ∧
          TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    sp_sub_2400_align s0.sp hsp0_align
  have hdealloc_fo : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (deallocFreeOnlySpec M A lim) :=
    subroutine_ok_deallocFreeOnly hdealloc_ok
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  refine seq_clean_evs
    (mid := lsmpl.base 333 + 5840#64)
    (P_evs := fun evs1 sm =>
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
      (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
      vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
      A.pool lim (M.stepEvents evs1 st) sm ∗
      Rest)
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x26 = ca2 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
    dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
      BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc1 ⊢
    change s1.pc = (blkPl_333).base + 5820#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 5840#64) s1 _ _
    by_cases hca1 : (ca1 == 0#64) = true
    · simp only [hca1, ↓reduceIte, sepConj_emp, emp_sepConj]
      apply sepWP_evs_nil
      simp only [M.stepEvents_nil]
      wp_steps_sync_333 ((blkPl_333).base + 5840#64)
      simp only [State.setMem_setMem]
      refine entails_pre_st ?_ ?_
      · intro sc hsc
        rw [← hsc]
        simp only [arm64_norm]
        exact Entails.of_eq (by sep_ac_rfl)
      · wp_done
    · have hbeq : (ca1 == 0#64) = false := Bool.eq_false_iff.mpr hca1
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      apply sepWP_evs_dealloc ca1.toNat 1
      wp_steps_sync_333 (lsρ spqrRustDeallocSym)
      simp only [State.setMem_setMem]
      wp_call hdealloc_fo (pa1, ca1.toNat, 1, st)
      have hacp1 : AllocCallPreserved s1 sf := by
        simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
      have hsp_sf : sf.sp = s0.sp - 2400#64 := ‹sf.sp = s1.sp›.trans hsp1
      have htr_sf : sf.trace = s0.trace := hacp1.2.1.trans htr1.1
      have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
        ‹calleeSavedVRegs sf = calleeSavedVRegs s1›.trans htr1.2
      refine entails_pre_st ?_ ?_
      · intro sc hsc
        rw [← hsc, hsp1]
        simp only [arm64_norm]
        exact Entails.of_eq (by sep_ac_rfl)
      · wp_done
  ·
    intro evs1 s2 hevs1 hpc2 hrun2 ⟨hsp2, hx19_2, hx26_2, htr2⟩
    let st1 := M.stepEvents evs1 st
    by_cases hca2 : (ca2 == 0#64) = true
    · dsimp only [vecCapPtrDealloc]
      simp only [hca2, ↓reduceIte, sepConj_emp, emp_sepConj]
      refine seq_clean_st
        (mid := lsmpl.base 333 + 5844#64)
        (P_mid := fun sm =>
          A.pool lim st1 sm ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
           (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
           Rest))
        (Q := fun sm =>
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · change s2.pc = (blkPl_333).base + 5840#64 at hpc2
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 5844#64) s2 _ _
        wp_steps_sync_333 ((blkPl_333).base + 5844#64)
        simp only [State.setMem_setMem]
        refine align_pre_st (by sep_ac_rfl) ?_
        wp_done
      · intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, htr3⟩
        have h5844 := v10_states_from_pb_err_5844_placed_budget A lim st1 (ext := ext)
          s0 s3 out
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
           (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
           Rest)
          hpc3 hrun3 hsp3 hx19_3 htr3
        refine SepWP.mono h5844 fun sf Pf _ _ ⟨hPf, _, hsp_f, hx19_f, hx21_f, htr_f⟩ => ?_
        exact ⟨evs1, hevs1, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)),
          hsp_f, hx19_f, hx21_f, htr_f⟩
    · have hbeq : (ca2 == 0#64) = false := Bool.eq_false_iff.mpr hca2
      refine seq_clean_st
        (mid := lsmpl.base 333 + 7236#64)
        (P_mid := fun sm =>
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
          vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
          A.pool lim st1 sm ∗
          ((((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗ Rest))
        (Q := fun sm =>
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x26 = ca2 ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · change s2.pc = (blkPl_333).base + 5840#64 at hpc2
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 7236#64) s2 _ _
        wp_steps_sync_333 ((blkPl_333).base + 7236#64)
        simp only [State.setMem_setMem]
        refine align_pre_st (by sep_ac_rfl) ?_
        wp_done
      · intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx26_3, htr3⟩
        have h7236 := v10_states_from_pb_err_7236_of_sub_placed hdealloc_ok st1 s0 s3 out ca2 pa2
          ((((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗ Rest)
          hbeq hsp0_align hpc3 hrun3 hsp3 hx19_3 hx26_3 htr3
        refine SepWP.mono h7236 fun sf Pf _ _ ⟨evs2, hevs2, hPf, hsp_f, hx19_f, hx21_f, htr_f⟩ => ?_
        refine ⟨evs1 ++ evs2, FreeOnlyEvs.append hevs1 hevs2, ?_, hsp_f, hx19_f, hx21_f, htr_f⟩
        have hst_eq : M.stepEvents evs2 st1 = M.stepEvents (evs1 ++ evs2) st := by
          dsimp only [st1]
          rw [M.stepEvents_append]
        rw [hst_eq] at hPf
        exact Entails.trans hPf (Entails.of_eq (by sep_ac_rfl))

theorem v10_states_from_pb_err_5820_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (out ca1 pa1 ca2 pa2 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 5820#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = pa1) (hx26_1 : s1.readReg64 .x26 = ca2)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 2084#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ vecCapPtrDealloc A.repAlloc ca1 pa1 ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗ A.pool lim st s1 ∗ Rest)
      (fun sm Pm => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = 0#64 ∧ TraceCalleeSaved sm s0) :=
  v10_states_from_pb_err_5820_of_sub_placed
    (v10_sub_ok_dealloc_125316_of_dealloc_placed hdealloc)
    st s0 s1 out ca1 pa1 ca2 pa2 Rest hsp0_align hpc1 hrun1 hsp1 hx19_1 hx21_1 hx26_1 htr1

theorem v10_states_from_pb_err_5820_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out ca1 pa1 ca2 pa2 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 5820#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = pa1) (hx26_1 : s1.readReg64 .x26 = ca2)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 2084#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ vecCapPtrDealloc A.repAlloc ca1 pa1 ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗ A.pool lim st s1 ∗ Rest)
      (fun sm Pm => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = 0#64 ∧ TraceCalleeSaved sm s0) :=
  v10_states_from_pb_err_5820_of_sub_placed hA.dealloc_ok
    st s0 s1 out ca1 pa1 ca2 pa2 Rest hsp0_align hpc1 hrun1 hsp1 hx19_1 hx21_1 hx26_1 htr1

theorem v10_states_from_pb_err_5820_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out ca1 pa1 ca2 pa2 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 5820#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = pa1) (hx26_1 : s1.readReg64 .x26 = ca2)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 2084#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ vecCapPtrDealloc A.repAlloc ca1 pa1 ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗ A.pool lim st s1 ∗ Rest)
      (fun sm Pm => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = 0#64 ∧ TraceCalleeSaved sm s0) :=
  v10_states_from_pb_err_5820_of_dealloc_placed hA.dealloc
    st s0 s1 out ca1 pa1 ca2 pa2 Rest hsp0_align hpc1 hrun1 hsp1 hx19_1 hx21_1 hx26_1 htr1

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10aPlacedBudget

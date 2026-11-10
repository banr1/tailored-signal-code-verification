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
public import LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.PolyEncoderBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.UnchunkedBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.UnchunkedFromPbClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7a
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7aPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBaseBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch1Placed
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Placed Variant 7 (`Ct1Sampled`, Block `333`) — Part A

Relocatable budget-threaded subroutine call bridges, `+4632` error exit (`+4632 -> +7084 -> s0.x30`),
and `FreeOnlyEvs`-tracked inline `ProtoPolynomialDecoder` deallocation (`+4556..+4632`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7aPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkLib_333 blkLib_eq_333 blkPC_279 blkPC_333
   blkPl_279 blkPl_333 lsProg_279 lsProg_333 ls_blockPlacement_base
   ls_subroutine_ok_of_block lscall_blk_cl lsmpl lsρ
   subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded withMemEq)
open CryptoVerification.LibsignalSpqrV1 (Error)
open CryptoVerification.RustHeap (RustAlloc allocHookStack arrayAt vecU8)
open CryptoVerification.SpqrV1.Alloc (spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.Drop
  (add_24_add_8 cap_mul_24 chunkedStatesSize cons_len_mul header_cells_entails_memRegion_24
   ofNat_add_one_beq_one_false_24 ofNat_beq_zero_false_24 ofNat_succ_eq_add_one
   protoPolyDecoderHeaders_entails_memRegion_40 sep_pull_body sep_push_body sep_rejoin_loop
   tail_len_mul_lt vecCapPtrDealloc vecU8_entails_capPtr_dealloc)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved resultChunkedStatesAt spqrErrorByte statesFromPbSavedCells statesFromPbStack)
open CryptoVerification.SpqrV1.Unchunked (extractLsb'_0_64_append extractLsb'_64_64_append)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs
   RustCliAllocBudget VmPreserved rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget (dropGluePoly16Spec)
open LibsignalBinary.Proofs.SpqrV1.Drop.PolyEncoderBudget (dropGluePolyEncoderSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget (dropProtoPolyEncoderSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.UnchunkedBudget
  (dropProtoUnchunkedCt1SentEkReceivedSpec dropUnchunkedCt1SentSpec
   drop_unchunked_ct1_sent_local2_placed_ok)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (isTotalTrapHooks_withPanics_vmTrapHooks sepWP_lsBlock_vmPreserved
   stripS_calleeSavedVRegs stripS_pc stripS_readReg64 stripS_sp stripS_status stripS_trace
   vmTrapHooks)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.DefsBudget (encoderFromPbSpec)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
  (FromPbAllocHooksPlacedBudget spqrRustDeallocSym)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.UnchunkedFromPbClPlacedBudget
  (ct1_sent_from_pb_on_333_placed_ok
   drop_proto_unchunked_ct1_sent_ek_received_cl_on
   drop_proto_unchunked_ct1_sent_ek_received_mem_on)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
  (align_pre_st deallocFreeOnlySpec sepWP_evs_dealloc sepWP_evs_nil
   seq_clean_evs seq_clean_st)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
  (EncoderFromPbPlacedOkExt FromPbAllocHooksBudget withMemEq_of_withLsCodeLoaded)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget (blk333_safeVm)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4PlacedBudget
  (v4_stackAt_allocHook_to_encoderFromPbStack v4_stackAt_encoderFromPbStack_to_allocHook
   v4_sub_ok_dealloc_125316_fo_placed)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudget
  (drop_glue_poly16_cl_on drop_glue_poly16_mem_on
   drop_glue_poly_encoder_local2_cl_on drop_glue_poly_encoder_local2_mem_on
   drop_glue_proto_poly_encoder_cl_on drop_glue_proto_poly_encoder_mem_on)
open LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBaseBudget (ct1SentFromPbSpec)

/-! ## Re-exports from `Variant7a` -/

abbrev v7_Saved4560Preserved := CryptoVerification.SpqrV1.States.FromPb.v7_Saved4560Preserved

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

private theorem blk333_noSvc0 :
    VerifiedLibraries.RustStd.checkBlockNoSvc0 blkLib_333.text = true := by
  decide +kernel

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

private theorem entails_pre_st {prog : Program} {target : BitVec 64} {s : State}
    {P : SepProp} {P_mid : State → SepProp} {Q : State → Prop}
    (hent : ∀ sc : State, sc = s → P ⊢ P_mid sc)
    (h : SepWP prog target s (P_mid s) (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm) :=
  SepWP.weaken_pre (hent s rfl) h

private theorem sepWP_with_evs {prog : Program} {target : BitVec 64} {s : State}
    (evs : List AllocEvent) (hevs : FreeOnlyEvs evs)
    {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    (h : SepWP prog target s P (fun sm Pm => (Pm ⊢ P_evs evs sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm =>
      ∃ evs', FreeOnlyEvs evs' ∧ (Pm ⊢ P_evs evs' sm) ∧ Q sm) :=
  SepWP.mono h fun _ _ _ _ ⟨hp, hq⟩ => ⟨evs, hevs, hp, hq⟩

/-! ## 1. Budget-Threaded Subroutine Call Bridges for Variant 7 -/

theorem v7_sub_ok_drop_proto_unchunked_ct1_sent_ek_received_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : FromPbAllocHooksBudget M A lim ext) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 286)
      (withLsCodeLoaded lsmpl (dropProtoUnchunkedCt1SentEkReceivedSpec M A lim)) :=
  drop_proto_unchunked_ct1_sent_ek_received_cl_on
    (callerProg := lsProg_333 (Rust.withPanics ext)) hA.dealloc

theorem v7_sub_ok_drop_proto_unchunked_ct1_sent_ek_received_mem_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {m : Memory}
    (hA : FromPbAllocHooksBudget M A lim ext) (hcl : LibsignalCodeLoaded lsmpl m) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsmpl.base 286)
      (withMemEq m (dropProtoUnchunkedCt1SentEkReceivedSpec M A lim)) :=
  drop_proto_unchunked_ct1_sent_ek_received_mem_on
    (callerProg := (blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)) hA.dealloc hcl

theorem v7_sub_ok_drop_proto_poly_encoder_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : FromPbAllocHooksBudget M A lim ext) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 271)
      (withLsCodeLoaded lsmpl (dropProtoPolyEncoderSpec M A lim)) :=
  drop_glue_proto_poly_encoder_cl_on
    (callerProg := lsProg_333 (Rust.withPanics ext)) hA.dealloc

theorem v7_sub_ok_drop_proto_poly_encoder_mem_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {m : Memory}
    (hA : FromPbAllocHooksBudget M A lim ext) (hcl : LibsignalCodeLoaded lsmpl m) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsmpl.base 271)
      (withMemEq m (dropProtoPolyEncoderSpec M A lim)) :=
  drop_glue_proto_poly_encoder_mem_on
    (callerProg := (blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)) hA.dealloc hcl

theorem v7_sub_ok_drop_poly16_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : FromPbAllocHooksBudget M A lim ext) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 265)
      (withLsCodeLoaded lsmpl (dropGluePoly16Spec M A lim)) :=
  drop_glue_poly16_cl_on
    (callerProg := lsProg_333 (Rust.withPanics ext)) hA.dealloc

theorem v7_sub_ok_drop_poly16_mem_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {m : Memory}
    (hA : FromPbAllocHooksBudget M A lim ext) (hcl : LibsignalCodeLoaded lsmpl m) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsmpl.base 265)
      (withMemEq m (dropGluePoly16Spec M A lim)) :=
  drop_glue_poly16_mem_on
    (callerProg := (blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)) hA.dealloc hcl

theorem v7_sub_ok_drop_poly_encoder_local2_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : FromPbAllocHooksBudget M A lim ext) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 272)
      (withLsCodeLoaded lsmpl (dropGluePolyEncoderSpec M A lim)) :=
  drop_glue_poly_encoder_local2_cl_on
    (callerProg := lsProg_333 (Rust.withPanics ext)) hA.dealloc

theorem v7_sub_ok_drop_poly_encoder_local2_mem_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {m : Memory}
    (hA : FromPbAllocHooksBudget M A lim ext) (hcl : LibsignalCodeLoaded lsmpl m) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsmpl.base 272)
      (withMemEq m (dropGluePolyEncoderSpec M A lim)) :=
  drop_glue_poly_encoder_local2_mem_on
    (callerProg := (blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)) hA.dealloc hcl

theorem v7_drop_unchunked_ct1_sent_local2_cl_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {H : String → Option (State → State)}
    (hdealloc : HookSat H spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_279 H) (lsmpl.base 279)
      (withLsCodeLoaded lsmpl (dropUnchunkedCt1SentSpec M A lim F)) := by
  rw [← ls_blockPlacement_base (i := 279)]
  exact subroutine_ok_withLsCodeLoaded_of_plain
    (drop_unchunked_ct1_sent_local2_placed_ok (spqr_hook_ok_of_mem (prog := lsProg_279 H) hdealloc))

theorem v7_sub_ok_drop_unchunked_ct1_sent_local2_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 279)
      (withLsCodeLoaded lsmpl (dropUnchunkedCt1SentSpec M A lim F)) :=
  ls_subroutine_ok_of_block (v7_drop_unchunked_ct1_sent_local2_cl_placed_ok hA.dealloc) (by decide)

theorem v7_sub_ok_drop_unchunked_ct1_sent_local2_mem_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)} {m : Memory}
    (hA : FromPbAllocHooksBudget M A lim ext) (hcl : LibsignalCodeLoaded lsmpl m) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsmpl.base 279)
      (withMemEq m (dropUnchunkedCt1SentSpec M A lim F)) :=
  lscall_blk_cl (v7_drop_unchunked_ct1_sent_local2_cl_placed_ok hA.dealloc) hcl (by decide)

theorem v7_sub_ok_encoder_from_pb_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (henc : EncoderFromPbPlacedOkExt M A lim ext) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 374)
      (withLsCodeLoaded lsmpl (encoderFromPbSpec M A lim)) :=
  henc

theorem v7_sub_ok_encoder_from_pb_mem_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {m : Memory}
    (henc : EncoderFromPbPlacedOkExt M A lim ext) (hcl : LibsignalCodeLoaded lsmpl m) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsmpl.base 374)
      (withMemEq m (encoderFromPbSpec M A lim)) :=
  withMemEq_of_withLsCodeLoaded henc hcl

/-- Budget-threaded placed contract hypothesis for `<Ct1Sent>::from_pb` (Block `339`) on
    `lsProg_333`. -/
def Ct1SentFromPbPlacedOkExt [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 339)
    (withLsCodeLoaded lsmpl (ct1SentFromPbSpec M A lim F))

/-- Discharge `Ct1SentFromPbPlacedOkExt` unconditionally from `FromPbAllocHooksBudget`. -/
theorem ct1_sent_from_pb_ok_of_alloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext) :
    Ct1SentFromPbPlacedOkExt M A lim F ext :=
  ct1_sent_from_pb_on_333_placed_ok hA.shim hA.alloc hA.dealloc hA.memcpy

theorem v7_sub_ok_ct1_sent_from_pb_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hct1 : Ct1SentFromPbPlacedOkExt M A lim F ext) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 339)
      (withLsCodeLoaded lsmpl (ct1SentFromPbSpec M A lim F)) :=
  hct1

theorem v7_sub_ok_ct1_sent_from_pb_mem_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)} {m : Memory}
    (hct1 : Ct1SentFromPbPlacedOkExt M A lim F ext) (hcl : LibsignalCodeLoaded lsmpl m) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsmpl.base 339)
      (withMemEq m (ct1SentFromPbSpec M A lim F)) :=
  withMemEq_of_withLsCodeLoaded hct1 hcl

/-! ## 2. Error Exit at `+4632` (`bfi x28, x23, #8, #56; b +7084`) -/

/-- `VmPreserved`-strengthened placed error exit at `+4632` (`+4632 -> +7084 -> s0.x30`):
    given `(s1.readReg64 .x28).extractLsb' 0 8 = spqrErrorByte err`, executes
    `bfi x28, x23, #8, #56`, jumps to `+7084`, and returns `Err(err)`. -/
theorem v7_err_4632_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (err : Error) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4632#64)
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
    (CryptoVerification.SpqrV1.States.FromPb.v7_err_4632_placed
      (A := A) (F := F) (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      out err Rest hsp0_align
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1) (by simpa using hx28_1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sf Pf hvm ⟨hPf, hsp_f, hcc_f, htr_f⟩ =>
      ⟨hPf, hvm, hsp_f, hcc_f, htr_f⟩

theorem v7_err_4632_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (err : Error) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4632#64)
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
        Rest ∗ A.pool lim st s1)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err err)) ∗
          Rest ∗ A.pool lim st sf ∗
          stackAt s0.sp statesFromPbStack) ∧
        VmPreserved s1 sf ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hwp := v7_err_4632_placed (A := A.repAlloc) (F := F) (ext := ext)
    s0 s1 out err (Rest ∗ A.pool lim st s1)
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx28_1 htr1
  refine SepWP.mono hwp fun sf Pf _ _ ⟨hPf, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPf
  exact ⟨Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hvm, hrest⟩

/-! ## 3. Budget-Threaded `ProtoPolynomialDecoder` Inline Deallocation at `+4556..+4632` -/

theorem v7_proto_decoder_dealloc_body_4584_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 : State) (fsp out ptsPtr ptsCap x28_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (st : M.σ) (s : State) (Frame : SepProp),
      s.pc = lsmpl.base 333 + 4584#64 →
      s.status = .Running →
      v7_Saved4560Preserved s0 s fsp out ptsPtr ptsCap x28_val →
      s.readReg64 .x25 = cnt →
      s.readReg64 .x27 = cur + 8#64 →
      SepWP (lsProg_333 (Rust.withPanics ext))
        (lsmpl.base 333 + 4572#64) s
        (vecU8 A.repAlloc cur bs ∗ A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evs, FreeOnlyEvs evs ∧
          (Pm ⊢ memRegion cur 24 ∗ A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v7_Saved4560Preserved s0 sm fsp out ptsPtr ptsCap x28_val ∧
          sm.readReg64 .x25 = cnt ∧
          sm.readReg64 .x27 = cur + 8#64) := by
  have hdealloc_fo := v4_sub_ok_dealloc_125316_fo_placed hA
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  intro cur cnt bs st s Frame hpc hrun hpres hx25 hx27
  rw [← ls_blockPlacement_base (i := 333)] at hpc ⊢
  change s.pc = (blkPl_333).base + 4584#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 4572#64) s _ _
  rcases hpres with ⟨hsp, hx19, hx20, hx22, hx28, htrace⟩
  refine SepWP.weaken_pre (sepConj_mono_left (vecU8_entails_capPtr_dealloc A.repAlloc cur bs)) ?_
  conv => arg 4; simp only [sepExists_sepConj_left]
  apply ProofLib.SepWP.exists_left; intro cap
  apply ProofLib.SepWP.exists_left; intro vptr
  have hpost24 (Pool : SepProp) :
      ((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
        Pool ∗ stackAt fsp allocHookStack ∗ Frame ⊢
      memRegion cur 24 ∗ Pool ∗ stackAt fsp allocHookStack ∗ Frame :=
    sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)
  dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
    BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc ⊢
  by_cases hcap : (cap == 0#64) = true <;>
    simp only [hcap, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · apply sepWP_evs_nil
    simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
    wp_steps_sync_333 ((blkPl_333).base + 4572#64)
    simp only [State.setMem_setMem]
    refine entails_pre_st (fun _ hsc => ?_) ?_
    · subst hsc
      exact Entails.trans (Entails.of_eq (by sep_ac_rfl)) (hpost24 _)
    · wp_done
  · apply sepWP_evs_dealloc cap.toNat 1
    wp_steps_sync_333 (lsρ spqrRustDeallocSym)
    simp only [State.setMem_setMem]
    wp_call hdealloc_fo (vptr, cap.toNat, 1, st)
    have hacp : AllocCallPreserved s sf := by
      simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
    have htr_sf : sf.trace = s0.trace := hacp.2.1.trans htrace.1
    have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
      ‹calleeSavedVRegs sf = calleeSavedVRegs s›.trans htrace.2
    wp_steps_sync_333 ((blkPl_333).base + 4572#64)
    simp only [State.setMem_setMem]
    refine entails_pre_st (fun _ hsc => ?_) ?_
    · subst hsc
      rw [hsp]
      exact Entails.trans (Entails.of_eq (by sep_ac_rfl)) (hpost24 _)
    · wp_done

theorem v7_proto_decoder_dealloc_body_4584_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 : State) (fsp out ptsPtr ptsCap x28_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (st : M.σ) (s : State) (Frame : SepProp),
      s.pc = lsmpl.base 333 + 4584#64 →
      s.status = .Running →
      v7_Saved4560Preserved s0 s fsp out ptsPtr ptsCap x28_val →
      s.readReg64 .x25 = cnt →
      s.readReg64 .x27 = cur + 8#64 →
      SepWP (lsProg_333 (Rust.withPanics ext))
        (lsmpl.base 333 + 4572#64) s
        (vecU8 A.repAlloc cur bs ∗ A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evs, FreeOnlyEvs evs ∧
          (Pm ⊢ memRegion cur 24 ∗ A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v7_Saved4560Preserved s0 sm fsp out ptsPtr ptsCap x28_val ∧
          sm.readReg64 .x25 = cnt ∧
          sm.readReg64 .x27 = cur + 8#64) :=
  v7_proto_decoder_dealloc_body_4584_of_placedHooks hA.toPlacedBudget s0 fsp out ptsPtr ptsCap x28_val hfsp_align

theorem v7_proto_decoder_dealloc_loop_4584_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 : State) (fsp out ptsPtr ptsCap x28_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (st : M.σ) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = lsmpl.base 333 + 4584#64 →
      s.status = .Running →
      v7_Saved4560Preserved s0 s fsp out ptsPtr ptsCap x28_val →
      s.readReg64 .x25 = BitVec.ofNat 64 rest.length →
      s.readReg64 .x27 = cur + 8#64 →
      SepWP (lsProg_333 (Rust.withPanics ext))
        (lsmpl.base 333 + 4608#64) s
        (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 cur rest ∗
          A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evs, FreeOnlyEvs evs ∧
          (Pm ⊢ memRegion cur (rest.length * 24) ∗
            A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v7_Saved4560Preserved s0 sm fsp out ptsPtr ptsCap x28_val) := by
  have hbody := v7_proto_decoder_dealloc_body_4584_of_placedHooks
    hA s0 fsp out ptsPtr ptsCap x28_val hfsp_align
  intro rest
  induction rest with
  | nil => intro _ _ _ _ hne; exact absurd rfl hne
  | cons bs tl ih =>
    intro cur st s Frame _ hlen hpc hrun hpres hx25 hx27
    simp only [arrayAt, BitVec.ofNat_eq_ofNat]; rw [sep_pull_body]
    refine seq_clean_evs
      (mid := lsmpl.base 333 + 4572#64)
      (P_evs := fun evs1 sm =>
        memRegion cur 24 ∗ A.pool lim (M.stepEvents evs1 st) sm ∗ stackAt fsp allocHookStack ∗
          (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (cur + 24#64) tl ∗ Frame))
      (Q := fun sm => v7_Saved4560Preserved s0 sm fsp out ptsPtr ptsCap x28_val ∧
        sm.readReg64 .x25 = BitVec.ofNat 64 (bs :: tl).length ∧
        sm.readReg64 .x27 = cur + 8#64)
      (hbody cur (BitVec.ofNat 64 (bs :: tl).length) bs st s _ hpc hrun hpres hx25 hx27) ?_
    intro evs1 s1 hevs1 hpc1 hrun1 ⟨hpres1, hx25_1, hx27_1⟩
    rcases tl with _ | ⟨bs2, tl2⟩
    · simp only [List.length_singleton, arrayAt, sepConj_emp, emp_sepConj, Nat.one_mul] at hx25_1 ⊢
      rcases hpres1 with ⟨hsp_1, hx19_1, hx20_1, hx22_1, hx28_1, htrace_1⟩
      rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
      change s1.pc = (blkPl_333).base + 4572#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 4608#64) s1 _ _
      apply sepWP_with_evs evs1 hevs1
      wp_steps_sync_333 ((blkPl_333).base + 4608#64)
      simp only [State.setMem_setMem]
      refine align_pre_st (by sep_ac_rfl) ?_
      wp_done
    · have hlen_tl : (bs2 :: tl2).length * 24 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_add_one_beq_one_false_24 (n := (bs2 :: tl2).length) (by simp) hlen_tl
      rw [List.length_cons, ofNat_succ_eq_add_one] at hx25_1
      refine seq_clean_st (mid := lsmpl.base 333 + 4584#64)
        (P_mid := fun sm =>
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (cur + 24#64) (bs2 :: tl2) ∗
          A.pool lim (M.stepEvents evs1 st) sm ∗ stackAt fsp allocHookStack ∗
          (memRegion cur 24 ∗ Frame))
        (Q := fun sm => v7_Saved4560Preserved s0 sm fsp out ptsPtr ptsCap x28_val ∧
          sm.readReg64 .x25 = BitVec.ofNat 64 (bs2 :: tl2).length ∧
          sm.readReg64 .x27 = (cur + 24#64) + 8#64)
        ?_ ?_
      · rcases hpres1 with ⟨hsp_1, hx19_1, hx20_1, hx22_1, hx28_1, htrace_1⟩
        rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
        change s1.pc = (blkPl_333).base + 4572#64 at hpc1
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 4584#64) s1 _ _
        rw [sep_push_body]
        wp_steps_sync_333 ((blkPl_333).base + 4584#64)
        simp only [State.setMem_setMem]
        rw [add_24_add_8]
        refine align_pre_st (by sep_ac_rfl) ?_
        wp_done
      · intro s2 hpc2 hrun2 ⟨hpres2, hx25_2, hx27_2⟩
        have hrec := ih (cur + 24#64) (M.stepEvents evs1 st) s2 (memRegion cur 24 ∗ Frame)
          (List.cons_ne_nil _ _) hlen_tl hpc2 hrun2 hpres2 hx25_2 hx27_2
        refine SepWP.mono hrec fun sm _Pm _ _ ⟨evs2, hevs2, hp, hpres_f⟩ => ?_
        refine ⟨evs1 ++ evs2, hevs1.append hevs2, ?_, hpres_f⟩
        rw [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
        have hsplit := cons_len_mul bs (bs2 :: tl2) 24
        have hbound : 24 + (bs2 :: tl2).length * 24 ≤ 2 ^ 64 := by
          rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
        refine Entails.trans hp ?_
        rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 24 ((bs2 :: tl2).length * 24) hbound]
        exact Entails.refl _

theorem v7_proto_decoder_dealloc_loop_4584_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 : State) (fsp out ptsPtr ptsCap x28_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (st : M.σ) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = lsmpl.base 333 + 4584#64 →
      s.status = .Running →
      v7_Saved4560Preserved s0 s fsp out ptsPtr ptsCap x28_val →
      s.readReg64 .x25 = BitVec.ofNat 64 rest.length →
      s.readReg64 .x27 = cur + 8#64 →
      SepWP (lsProg_333 (Rust.withPanics ext))
        (lsmpl.base 333 + 4608#64) s
        (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 cur rest ∗
          A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evs, FreeOnlyEvs evs ∧
          (Pm ⊢ memRegion cur (rest.length * 24) ∗
            A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v7_Saved4560Preserved s0 sm fsp out ptsPtr ptsCap x28_val) :=
  v7_proto_decoder_dealloc_loop_4584_of_placedHooks hA.toPlacedBudget s0 fsp out ptsPtr ptsCap x28_val hfsp_align

theorem v7_proto_decoder_dealloc_4560_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 s : State) (fsp out ptsPtr ptsCap x28_val : BitVec 64)
    (pts : List (List (BitVec 8))) (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 4560#64)
    (hrun : s.status = .Running)
    (hpres : v7_Saved4560Preserved s0 s fsp out ptsPtr ptsCap x28_val)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 pts.length) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4632#64) s
      ((if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v7_Saved4560Preserved s0 sm fsp out ptsPtr ptsCap x28_val) := by
  have hdealloc_fo := v4_sub_ok_dealloc_125316_fo_placed hA
  have hloop := v7_proto_decoder_dealloc_loop_4584_of_placedHooks
    hA s0 fsp out ptsPtr ptsCap x28_val hfsp_align
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  dsimp only [BitVec.ofNat_eq_ofNat] at hdealloc_fo hloop hpc ⊢
  refine seq_clean_evs (mid := lsmpl.base 333 + 4608#64)
    (P_evs := fun evs1 sm =>
      (if ptsCap = 0#64 then emp
       else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗ memRegion ptsPtr (ptsCap.toNat * 24)) ∗
      A.pool lim (M.stepEvents evs1 st) sm ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => v7_Saved4560Preserved s0 sm fsp out ptsPtr ptsCap x28_val)
    ?_ ?_
  · cases pts with
    | nil =>
      rcases hpres with ⟨hsp, hx19, hx20, hx22, hx28, htrace⟩
      simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, arrayAt, emp_sepConj] at hx25 ⊢
      rw [← ls_blockPlacement_base (i := 333)] at hpc ⊢
      change s.pc = (blkPl_333).base + 4560#64 at hpc
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 4608#64) s _ _
      apply sepWP_evs_nil
      simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
      wp_steps_sync_333 ((blkPl_333).base + 4608#64)
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
      simp only [hcap_ne, ↓reduceIte]
      refine seq_clean_st (mid := lsmpl.base 333 + 4584#64)
        (P_mid := fun sm =>
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr (bs :: tl) ∗
          A.pool lim st sm ∗ stackAt fsp allocHookStack ∗
          (A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
           memRegion (ptsPtr + BitVec.ofNat 64 ((bs :: tl).length * 24))
             ((ptsCap.toNat - (bs :: tl).length) * 24) ∗
           Frame))
        (Q := fun sm => v7_Saved4560Preserved s0 sm fsp out ptsPtr ptsCap x28_val ∧
          sm.readReg64 .x25 = BitVec.ofNat 64 (bs :: tl).length ∧
          sm.readReg64 .x27 = ptsPtr + 8#64)
        ?_ ?_
      · rcases hpres with ⟨hsp, hx19, hx20, hx22, hx28, htrace⟩
        rw [← ls_blockPlacement_base (i := 333)] at hpc ⊢
        change s.pc = (blkPl_333).base + 4560#64 at hpc
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 4584#64) s _ _
        wp_steps_sync_333 ((blkPl_333).base + 4584#64)
        simp only [State.setMem_setMem]
        refine align_pre_st (by sep_ac_rfl) ?_
        wp_done
      · intro s_loop hpc_loop hrun_loop ⟨hpres_loop, hx25_loop, hx27_loop⟩
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
            hx25_loop hx27_loop)
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
  · intro evs1 s3 hevs1 hpc3 hrun3 ⟨hsp_3, hx19_3, hx20_3, hx22_3, hx28_3, htrace_3⟩
    let st1 := M.stepEvents evs1 st
    rw [← ls_blockPlacement_base (i := 333)] at hpc3 ⊢
    change s3.pc = (blkPl_333).base + 4608#64 at hpc3
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 4632#64) s3 _ _
    by_cases hc : ptsCap = 0#64
    · have hc_beq : (ptsCap == 0#64) = true := by rw [beq_iff_eq]; exact hc
      simp only [hc, ↓reduceIte, emp_sepConj, sepConj_emp] at hx22_3 ⊢
      apply sepWP_with_evs evs1 hevs1
      wp_steps_sync_333 ((blkPl_333).base + 4632#64)
      simp only [State.setMem_setMem]
      refine align_pre_st (by sep_ac_rfl) ?_
      wp_done
    · have hc_beq : ¬((ptsCap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
      have hlsl := cap_mul_24 hpts_cap_lt
      simp only [hc, ↓reduceIte]
      apply sepWP_with_evs (evs1 ++ rustDeallocEvents (ptsCap.toNat * 24) 8)
        (hevs1.append (FreeOnlyEvs.singleton 8 (ptsCap.toNat * 24)))
      simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
      wp_steps_sync_333 (lsρ spqrRustDeallocSym)
      simp only [State.setMem_setMem]
      wp_call hdealloc_fo (ptsPtr, ptsCap.toNat * 24, 8, st1)
      have hacp : AllocCallPreserved s3 sf := by
        simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
      have htr_sf : sf.trace = s0.trace := hacp.2.1.trans htrace_3.1
      have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
        ‹calleeSavedVRegs sf = calleeSavedVRegs s3›.trans htrace_3.2
      simp only [State.setMem_setMem, st1, wp_norm, arm64_norm] at *
      refine align_pre_st (by rw [hsp_3]) ?_
      wp_done

theorem v7_proto_decoder_dealloc_4560_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 s : State) (fsp out ptsPtr ptsCap x28_val : BitVec 64)
    (pts : List (List (BitVec 8))) (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 4560#64)
    (hrun : s.status = .Running)
    (hpres : v7_Saved4560Preserved s0 s fsp out ptsPtr ptsCap x28_val)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 pts.length) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4632#64) s
      ((if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v7_Saved4560Preserved s0 sm fsp out ptsPtr ptsCap x28_val) :=
  v7_proto_decoder_dealloc_4560_of_placedHooks hA.toPlacedBudget
    s0 s fsp out ptsPtr ptsCap x28_val pts st Frame
    hfsp_align hpts_le hpts_cap_lt hpc hrun hpres hx25

/-- Budget-threaded placed `ProtoPolynomialDecoder` deallocation at `pbA + 184#64` starting at
    `+4556`: given `x27 = pbA` and `x22 = ptsCap`, loads `ptsPtr, pts.length`, runs the loop
    `+4560..+4632` under `FreeOnlyEvs`, and collapses `pbA + 184..224` into
    `memRegion (pbA + 184#64) 40`, reaching `+4632`. -/
theorem v7_proto_decoder_dealloc_4556_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 s1 : State) (out pbA ptsCap ptsPtr x28_val : BitVec 64)
    (pts : List (List (BitVec 8))) (st : M.σ) (Frame : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 4556#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = ptsCap)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = x28_val)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((pbA + 184#64) ↦₆₄ ptsCap) ∗
         ((pbA + 192#64) ↦₆₄ ptsPtr) ∗
         ((pbA + 200#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
         (if ptsCap = 0 then emp
          else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
            arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pts ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
              ((ptsCap.toNat - pts.length) * 24)) ∗
         memRegion (pbA + 208#64) 16) ∗
        A.pool lim st s1 ∗
        Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (pbA + 184#64) 40 ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = x28_val ∧
        TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  refine SepWP.weaken_pre
    (sepConj_mono_left (v4_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
  refine seq_clean_st
    (mid := lsmpl.base 333 + 4560#64)
    (P_mid := fun sm =>
      (if ptsCap = 0 then emp
       else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
         arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pts ∗
         memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
           ((ptsCap.toNat - pts.length) * 24)) ∗
      A.pool lim st sm ∗
      stackAt (s0.sp - 2400#64) allocHookStack ∗
      (memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗
       ((pbA + 184#64) ↦₆₄ ptsCap) ∗
       ((pbA + 192#64) ↦₆₄ ptsPtr) ∗
       ((pbA + 200#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
       memRegion (pbA + 208#64) 16 ∗
       Frame))
    (Q := fun sm =>
      v7_Saved4560Preserved s0 sm (s0.sp - 2400#64) out ptsPtr ptsCap x28_val ∧
      sm.readReg64 .x25 = BitVec.ofNat 64 pts.length)
    ?_ ?_
  · rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
    change s1.pc = (blkPl_333).base + 4556#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 4560#64) s1 _ _
    wp_steps_sync_333 ((blkPl_333).base + 4560#64)
    simp only [State.setMem_setMem]
    refine align_pre_st (by sep_ac_rfl) ?_
    wp_done
  · intro s2 hpc2 hrun2 ⟨hpres2, hx25_2⟩
    have h4560 := v7_proto_decoder_dealloc_4560_of_placedHooks
      hA s0 s2 (s0.sp - 2400#64) out ptsPtr ptsCap x28_val pts st
      (memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗
       ((pbA + 184#64) ↦₆₄ ptsCap) ∗
       ((pbA + 192#64) ↦₆₄ ptsPtr) ∗
       ((pbA + 200#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
       memRegion (pbA + 208#64) 16 ∗
       Frame)
      hfsp_align hpts_le hpts_cap_lt hpc2 hrun2 hpres2 hx25_2
    refine SepWP.mono h4560 ?_
    intro sf Pf _ _ ⟨evs, hevs, hPf, hsp_f, hx19_f, _, _, hx28_f, htr_f⟩
    refine ⟨evs, hevs, Entails.trans hPf ?_, hsp_f, hx19_f, hx28_f, htr_f⟩
    have hst := v4_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
    have hhdr := protoPolyDecoderHeaders_entails_memRegion_40
      (pbA + 184#64) ptsCap ptsPtr (BitVec.ofNat 64 pts.length)
    have h192 : (pbA + 184#64) + 8#64 = pbA + 192#64 := by bv_omega
    have h200 : (pbA + 184#64) + 16#64 = pbA + 200#64 := by bv_omega
    have h208 : (pbA + 184#64) + 24#64 = pbA + 208#64 := by bv_omega
    rw [h192, h200, h208] at hhdr
    refine Entails.trans
      (Entails.of_eq (show _ =
        (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion ((s0.sp - 2400#64) - 5152#64) 1056) ∗
        (((pbA + 184#64) ↦₆₄ ptsCap) ∗
         ((pbA + 192#64) ↦₆₄ ptsPtr) ∗
         ((pbA + 200#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
         memRegion (pbA + 208#64) 16) ∗
        (A.pool lim (M.stepEvents evs st) sf ∗ Frame) by sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono hst (sepConj_mono_left hhdr)) (Entails.of_eq (by sep_ac_rfl))

theorem v7_proto_decoder_dealloc_4556_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 s1 : State) (out pbA ptsCap ptsPtr x28_val : BitVec 64)
    (pts : List (List (BitVec 8))) (st : M.σ) (Frame : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 4556#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = ptsCap)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = x28_val)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((pbA + 184#64) ↦₆₄ ptsCap) ∗
         ((pbA + 192#64) ↦₆₄ ptsPtr) ∗
         ((pbA + 200#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
         (if ptsCap = 0 then emp
          else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
            arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pts ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
              ((ptsCap.toNat - pts.length) * 24)) ∗
         memRegion (pbA + 208#64) 16) ∗
        A.pool lim st s1 ∗
        Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (pbA + 184#64) 40 ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = x28_val ∧
        TraceCalleeSaved sm s0) :=
  v7_proto_decoder_dealloc_4556_of_placedHooks hA.toPlacedBudget
    s0 s1 out pbA ptsCap ptsPtr x28_val pts st Frame
    hsp0_align hpts_le hpts_cap_lt hpc1 hrun1 hsp1 hx19_1 hx22_1 hx27_1 hx28_1 htr1

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7aPlacedBudget

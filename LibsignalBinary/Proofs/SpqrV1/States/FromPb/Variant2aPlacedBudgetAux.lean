/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.EncoderFromPbProofClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch2Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.EpiloguePlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Budget Hook Bundles and `sendingHdr` Drop Helpers

External hook bundles (`FromPbAllocHooksBudget`, `EncoderFromPbPlacedOkExt`), cross-block
sequencing helpers, shared `+5940` error exit, and `+4204` / `+4332` `sendingHdr` drop cleanup.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkLib_333 blkLib_eq_333 blkPC_333 blkPl_333
   extract_withMemEq lsProg_333 lsmpl lsρ sepWP_seq_lscl withLsCodeLoaded withMemEq)
open CryptoVerification.LibsignalSpqrV1 (ProtoPolynomialEncoder)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SpqrV1.Alloc
  (spqrHandleErrorSym spqrMemcpySym spqrRustAllocSym spqrRustNoAllocShimSym spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.Drop
  (DropProtoPolyEncoderGhost cap_add_one_beq_zero_false chunkedStatesSize dropStack48)
open CryptoVerification.SpqrV1.Poly (protoPolynomialEncoderAt protoPolynomialEncoderSize)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved resultChunkedStatesAt spqrErrorByte statesFromPbSavedCells statesFromPbStack
   v1_bv_add_add_lit v1_bv_sub_sub_lit v1_memRegion_1496_split_232
   v1_merge_stack_1496_56_752 v1_optProtoPolyEncoderAt_pack_some v1_optProtoPolyEncoderHeap
   v1_optProtoPolyEncoderHeap_extract_w0 v1_optProtoPolyEncoderWordsAt
   v1_optProtoPolyEncoderWordsAt_entails_56 v1_shl8_extract_0_8
   v1_stackAt_encoder_split_dropStack48)
open CryptoVerification.SpqrV1.Unchunked
  (extractLsb'_0_64_append extractLsb'_64_64_append)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget
   VmPreserved rustCliAllocBudgetSpec rustCliDeallocBudgetSpec)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (allocMemcpyVmSpec rustAllocShimVmSpec)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget (dropProtoPolyEncoderSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (isTotalTrapHooks_withPanics_vmTrapHooks sepWP_lsBlock_vmPreserved
   stripS_calleeSavedVRegs stripS_pc stripS_readReg64 stripS_sp stripS_status stripS_trace
   vmTrapHooks)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.DefsBudget (encoderFromPbSpec)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
  (FromPbAllocHooksPlacedBudget spqrRustDeallocSym)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.EncoderFromPbProofClPlacedBudget
  (encoder_from_pb_on_333_placed_ok_ext)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
  (align_pre_st deallocFreeOnlySpec subroutine_ok_deallocFreeOnly)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget (blk333_safeVm)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudget
  (drop_glue_proto_poly_encoder_cl_on drop_glue_proto_poly_encoder_mem_on)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm, local wp_norm]
  v1_bv_sub_sub_lit v1_shl8_extract_0_8 v1_bv_add_add_lit

theorem blk333_noSvc0 :
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

theorem entails_pre_st {prog : Program} {target : BitVec 64} {s : State}
    {P : SepProp} {P_mid : State → SepProp} {Q : State → Prop}
    (hent : ∀ sc : State, sc = s → P ⊢ P_mid sc)
    (h : SepWP prog target s (P_mid s) (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm) :=
  SepWP.weaken_pre (hent s rfl) h

/-! ## Hook Bundles, `withLsCodeLoaded` Sequencing Helpers, and Callee Relocation Lemmas -/

/-- External `HookSat` bundle for budget-threaded relocatable `States::from_pb` (Block `333` and
    its cross-block callees), mirroring `FromPbAllocHooks A ext`. -/
structure FromPbAllocHooksBudget [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop where
  panic_ok : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked
  shim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec
  alloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false)
  dealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim)
  memcpy : HookSat (Rust.withPanics ext) spqrMemcpySym allocMemcpyVmSpec

theorem FromPbAllocHooksBudget.toPlacedBudget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext) :
    FromPbAllocHooksPlacedBudget M A lim ext :=
  { shim_ok := spqr_hook_ok_of_mem hA.shim
    alloc_ok := spqr_hook_ok_of_mem hA.alloc
    dealloc_ok := spqr_hook_ok_of_mem hA.dealloc
    memcpy_ok := spqr_hook_ok_of_mem hA.memcpy
    panic_ok := hA.panic_ok }

/-- Budget-threaded relocatable `PolyEncoder::from_pb` (Block `374`) contract lifted to `lsProg_333`. -/
def EncoderFromPbPlacedOkExt [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 374)
    (withLsCodeLoaded lsmpl (encoderFromPbSpec M A lim))

theorem encoder_from_pb_ok_of_alloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext) :
    EncoderFromPbPlacedOkExt M A lim ext :=
  encoder_from_pb_on_333_placed_ok_ext hA.shim hA.alloc hA.dealloc hA.memcpy

alias seq_clean_lscl := Variant2aPlaced.seq_clean_lscl

/-- State-indexed `SepWP` sequence helper threading `LibsignalCodeLoaded lsmpl ·.mem`. -/
theorem seq_clean_lscl_st [LibsignalPlacement] {prog : Program} {mid target : BitVec 64}
    {s : State} {P : SepProp} {P_mid : State → SepProp} {Q : State → Prop}
    {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q sm → SepWP prog target sm (P_mid sm) post) :
    SepWP prog target s P post :=
  sepWP_seq_lscl hcl (SepWP.mono h1 fun sm _Pm hpc hrun ⟨hPm, hQ⟩ hcl' =>
    SepWP.weaken_pre hPm (h2 sm hpc hrun hcl' hQ))

/-- `FreeOnlyEvs`-threading `SepWP` sequence helper preserving `LibsignalCodeLoaded lsmpl ·.mem`. -/
theorem seq_clean_evs_lscl [LibsignalPlacement] {prog : Program} {mid target : BitVec 64}
    {s : State} {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm =>
      ∃ evs, FreeOnlyEvs evs ∧ (Pm ⊢ P_evs evs sm) ∧ Q sm))
    (h2 : ∀ (evs : List AllocEvent) (sm : State),
      FreeOnlyEvs evs → sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q sm →
      SepWP prog target sm (P_evs evs sm) post) :
    SepWP prog target s P post :=
  sepWP_seq_lscl hcl (SepWP.mono h1 fun sm _Pm hpc hrun ⟨evs, hevs, hPm, hQ⟩ hcl' =>
    SepWP.weaken_pre hPm (h2 evs sm hevs hpc hrun hcl' hQ))

/-- Specialize a `withLsCodeLoaded` contract to `withMemEq m` at a call site with `hcl`. -/
theorem withMemEq_of_withLsCodeLoaded [LibsignalPlacement] {α : Type}
    {prog : Program} {entry : BitVec 64} {spec : Spec α} {m : Memory}
    (h : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec))
    (hcl : LibsignalCodeLoaded lsmpl m) :
    subroutine_ok prog entry (withMemEq m spec) :=
  subroutine_ok_mono h
    (fun _ _ s0 hp => by
      have ⟨hm, hpre⟩ := extract_withMemEq hp
      have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := hm ▸ hcl
      dsimp only [withLsCodeLoaded]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨hcl0, hpre⟩)
    (fun _ _ _ _ hq => hq)

theorem v1_drop_glue_proto_poly_encoder_ok_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 271)
      (withLsCodeLoaded lsmpl (dropProtoPolyEncoderSpec M A lim)) :=
  drop_glue_proto_poly_encoder_cl_on (callerProg := lsProg_333 (Rust.withPanics ext)) hdealloc

theorem v1_drop_glue_proto_poly_encoder_ok_at_statesFromPb_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 271)
      (withLsCodeLoaded lsmpl (dropProtoPolyEncoderSpec M A lim)) :=
  v1_drop_glue_proto_poly_encoder_ok_of_dealloc_placed hA.dealloc

theorem v1_drop_glue_proto_poly_encoder_mem_ok_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {m : Memory}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hcl : LibsignalCodeLoaded lsmpl m) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)) (lsmpl.base 271)
      (withMemEq m (dropProtoPolyEncoderSpec M A lim)) :=
  drop_glue_proto_poly_encoder_mem_on
    (callerProg := (blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)) hdealloc hcl

theorem v1_drop_glue_proto_poly_encoder_mem_ok_at_statesFromPb_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {m : Memory}
    (hA : FromPbAllocHooksBudget M A lim ext) (hcl : LibsignalCodeLoaded lsmpl m) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)) (lsmpl.base 271)
      (withMemEq m (dropProtoPolyEncoderSpec M A lim)) :=
  v1_drop_glue_proto_poly_encoder_mem_ok_of_dealloc_placed hA.dealloc hcl

theorem v1_encoder_from_pb_ok_at_statesFromPb_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (henc : EncoderFromPbPlacedOkExt M A lim ext) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 374)
      (withLsCodeLoaded lsmpl (encoderFromPbSpec M A lim)) :=
  henc

theorem v1_encoder_from_pb_mem_ok_at_statesFromPb_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {m : Memory}
    (henc : EncoderFromPbPlacedOkExt M A lim ext) (hcl : LibsignalCodeLoaded lsmpl m) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)) (lsmpl.base 374)
      (withMemEq m (encoderFromPbSpec M A lim)) :=
  withMemEq_of_withLsCodeLoaded henc hcl

theorem v1_dealloc_ok_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim) :=
  spqr_hook_ok_of_mem hdealloc

theorem v1_dealloc_ok_at_statesFromPb_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim) :=
  v1_dealloc_ok_of_dealloc_placed hA.dealloc

theorem v1_dealloc_ok_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim) :=
  hA.dealloc_ok

theorem v1_deallocFreeOnly_ok_at_statesFromPb_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (deallocFreeOnlySpec M A lim) :=
  subroutine_ok_deallocFreeOnly (v1_dealloc_ok_at_statesFromPb_placed hA)

/-! ## Shared `+5940` `Err(StateDecode)` Exit and `+4332` / `+4204` `sendingHdr` Drop Cleanup -/

/-- `VmPreserved`-strengthened shared `Err(Error::StateDecode)` exit at `+5940`
    (`+5940 -> +60 -> s0.x30`). -/
theorem v1_err_5940_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 5940#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx26_1 : (s1.readReg64 .x26).extractLsb' 0 8 = spqrErrorByte .stateDecode)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          Rest ∗
          stackAt s0.sp statesFromPbStack) ∧
        VmPreserved s1 sf ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant2aPlaced.v1_err_5940_placed
      (A := A) (F := F) (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      out Rest hsp0_align
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1) (by simpa using hx26_1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sf Pf hvm ⟨hPf, hsp_f, hcc_f, htr_f⟩ =>
      ⟨hPf, hvm, hsp_f, hcc_f, htr_f⟩

theorem v1_err_5940_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 5940#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx26_1 : (s1.readReg64 .x26).extractLsb' 0 8 = spqrErrorByte .stateDecode)
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
          resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
          A.pool lim st sf ∗
          Rest ∗
          stackAt s0.sp statesFromPbStack) ∧
        VmPreserved s1 sf ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hwp := v1_err_5940_placed (A := A.repAlloc) (F := F) (ext := ext)
    s0 s1 out (A.pool lim st s1 ∗ Rest)
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx26_1 htr1
  refine SepWP.mono hwp fun sf Pf _ _ ⟨hPf, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPf
  exact ⟨Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hvm, hrest⟩

/-- Drop `Option<ProtoPolynomialEncoder>` at `fsp + 1496` and return `Err(StateDecode)`
    (`+4332 -> s0.x30`) from a Block-`271` `withLsCodeLoaded` contract. -/
theorem v1_drop_sendingHdr_4332_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdrop_cl : subroutine_ok (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 271)
      (withLsCodeLoaded lsmpl (dropProtoPolyEncoderSpec M A lim)))
    (st : M.σ) (s0 s1 : State) (out : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4332#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx26_1 : (s1.readReg64 .x26).extractLsb' 0 8 = spqrErrorByte .stateDecode)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 1496 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
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
  have hex := v1_optProtoPolyEncoderHeap_extract_w0 A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono (v1_memRegion_1496_split_232 (s0.sp - 2400#64))
      (sepConj_mono_right (sepConj_mono_left hex)))) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right,
    sepConj_assoc, sepConj_left_comm _ ⌜_⌝, sepConj_comm _ ⌜_⌝]
  apply ProofLib.SepWP.exists_left
  intro w232
  apply SepWP.pure_elim
  intro hw0_cond
  have hmerge := v1_merge_stack_1496_56_752 (s0.sp - 2400#64) w232
  cases optEnc with
  | none =>
    subst hw0_cond
    dsimp only [v1_optProtoPolyEncoderHeap]
    wp_simp_pre [sepConj_assoc, sepConj_left_comm _ ⌜_⌝, sepConj_comm _ ⌜_⌝]
    refine Variant1bPlacedBudgetAux2.seq_clean_st
      (mid := lsmpl.base 333 + 5940#64)
      (P_mid := fun sm =>
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        A.pool lim st sm ∗
        Rest)
      (Q := fun sm =>
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        (sm.readReg64 .x26).extractLsb' 0 8 = spqrErrorByte .stateDecode ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · dsimp only [v1_optProtoPolyEncoderWordsAt, noneCap, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      change s1.pc = (blkPl_333).base + 4332#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 5940#64) s1 _ _
      wp_steps_sync_333 ((blkPl_333).base + 5940#64)
      simp only [State.setMem_setMem]
      have hw_mem := v1_optProtoPolyEncoderWordsAt_entails_56
        (s0.sp - 2400#64 + 1496#64) noneCap w8 w16 w24 w32 w40 w48
      dsimp only [v1_optProtoPolyEncoderWordsAt, noneCap] at hw_mem
      refine entails_pre_st ?_ ?_
      · intro sc hsc
        rw [← hsc]
        refine Entails.trans (Entails.of_eq (show _ =
          (memRegion (s0.sp - 2400#64) 232 ∗
           ((s0.sp - 2400#64 + 232#64) ↦₆₄ w232) ∗
           memRegion (s0.sp - 2400#64 + 240#64) 1256 ∗
           (((s0.sp - 2400#64 + 1496#64) ↦₆₄ noneCap) ∗
            ((s0.sp - 2400#64 + 1496#64 + 8#64) ↦₆₄ w8) ∗
            ((s0.sp - 2400#64 + 1496#64 + 16#64) ↦₆₄ w16) ∗
            ((s0.sp - 2400#64 + 1496#64 + 24#64) ↦₆₄ w24) ∗
            ((s0.sp - 2400#64 + 1496#64 + 32#64) ↦₆₄ w32) ∗
            ((s0.sp - 2400#64 + 1496#64 + 40#64) ↦₆₄ w40) ∗
            ((s0.sp - 2400#64 + 1496#64 + 48#64) ↦₆₄ w48)) ∗
           memRegion (s0.sp - 2400#64 + 1552#64) 752) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
           A.pool lim st sc ∗ Rest) by
          dsimp only [noneCap]
          sep_ac_rfl)) ?_
        refine Entails.trans (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_left hw_mem))))) ?_
        exact Entails.trans (sepConj_mono_left hmerge) (Entails.of_eq (by sep_ac_rfl))
      · wp_done
    · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx26_2, htr2⟩
      have herr := v1_err_5940_placed_budget A lim st (F := F) (ext := ext) s0 s2 out Rest
        hsp0_align hpc2 hrun2 hsp2 hx19_2 hx26_2 htr2
      refine SepWP.mono herr fun sf Pf _ _ ⟨hPf, _, hsp_f, hcc_f, htr_f⟩ => ?_
      refine ⟨[], FreeOnlyEvs.nil, ?_, hsp_f, hcc_f, htr_f⟩
      simpa only [M.stepEvents_nil] using hPf
  | some pbEnc =>
    have hpack := v1_optProtoPolyEncoderAt_pack_some A.repAlloc (s0.sp - 2400#64 + 1496#64) pbEnc
      w0 w8 w16 w24 w32 w40 w48
    have hne := cap_add_one_beq_zero_false hw0_cond
    have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
      ProofLib.spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
    have h904 : s0.sp - 2400#64 + 1496#64 = s0.sp - 904#64 := by bv_omega
    refine seq_clean_lscl_st hcl1
      (mid := lsmpl.base 271)
      (P_mid := fun sm =>
        protoPolynomialEncoderAt A.repAlloc (s0.sp - 904#64) pbEnc ∗
        A.pool lim st sm ∗
        stackAt (s0.sp - 2400#64) dropStack48 ∗
        (memRegion (s0.sp - 2400#64 - 5152#64) 1008 ∗
         memRegion (s0.sp - 2400#64) 232 ∗
         ((s0.sp - 2400#64 + 232#64) ↦₆₄ w232) ∗
         memRegion (s0.sp - 2400#64 + 240#64) 1256 ∗
         memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
         statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗
         Rest))
      (Q := fun sm =>
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x0 = s0.sp - 904#64 ∧
        sm.readReg64 .lr = (blkPl_333).base + 4356#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x26 = s1.readReg64 .x26 ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · dsimp only [v1_optProtoPolyEncoderWordsAt, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      change s1.pc = (blkPl_333).base + 4332#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        (lsmpl.base 271) s1 _ _
      wp_steps_sync_333 (lsmpl.base 271)
      simp only [State.setMem_setMem]
      refine entails_pre_st ?_ ?_
      · intro sc hsc
        rw [← hsc, v1_stackAt_encoder_split_dropStack48 (s0.sp - 2400#64), ← h904]
        refine Entails.trans (Entails.of_eq (show _ =
          (v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
           v1_optProtoPolyEncoderHeap A.repAlloc (some pbEnc) w0 w8 w16 w24 w32 w40 w48) ∗
          (A.pool lim st sc ∗ stackAt (s0.sp - 2400#64) dropStack48 ∗
           (memRegion (s0.sp - 2400#64 - 5152#64) 1008 ∗
            memRegion (s0.sp - 2400#64) 232 ∗
            ((s0.sp - 2400#64 + 232#64) ↦₆₄ w232) ∗
            memRegion (s0.sp - 2400#64 + 240#64) 1256 ∗
            memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
            statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest)) by
            dsimp only [v1_optProtoPolyEncoderWordsAt]
            sep_ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hpack) (Entails.of_eq (by sep_ac_rfl))
      · wp_done
    · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx0_2, hlr_2, hx19_2, hx26_2, htr2⟩
      have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := hsp2 ▸ hfsp_align
      have hdrop : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          (lsmpl.base 271) (withMemEq s2.mem (dropProtoPolyEncoderSpec M A lim)) :=
        withMemEq_of_withLsCodeLoaded hdrop_cl hcl2
      simp only [withMemEq, dropProtoPolyEncoderSpec] at hdrop
      refine Variant1bPlacedBudgetAux2.seq_clean_evs
        (mid := lsmpl.base 333 + 5940#64)
        (P_evs := fun evs sm =>
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (s0.sp - 2400#64) 2304 ∗
          statesFromPbSavedCells s0 ∗
          memRegion out chunkedStatesSize ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          Rest)
        (Q := fun sm =>
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          (sm.readReg64 .x26).extractLsb' 0 8 = spqrErrorByte .stateDecode ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 5940#64) s2 _ _
        rw [show stackAt (s0.sp - 2400#64) dropStack48 = stackAt s2.sp dropStack48 from hsp2 ▸ rfl]
        wp_call hdrop ((⟨s0.sp - 904#64, pbEnc⟩ : DropProtoPolyEncoderGhost), st)
        rw [hsp2]
        rw [hlr_2] at *
        have hevs_w : FreeOnlyEvs w := ‹_›
        have hacp_w : AllocCallPreserved s2 sf := by
          simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
        have hsp_sf : sf.sp = s0.sp - 2400#64 := ‹sf.sp = s2.sp›.trans hsp2
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
              Rest) ∧
            sm.sp = s0.sp - 2400#64 ∧
            sm.readReg64 .x19 = out ∧
            (sm.readReg64 .x26).extractLsb' 0 8 = spqrErrorByte .stateDecode ∧
            TraceCalleeSaved sm s0)
          ?_ (fun _ _ _ _ ⟨hp, hq⟩ => ⟨w, hevs_w, hp, hq⟩)
        wp_steps_sync_333 ((blkPl_333).base + 5940#64)
        simp only [State.setMem_setMem]
        refine entails_pre_st ?_ ?_
        · intro sc hsc
          have h7552 : s0.sp - 2400#64 - 5152#64 = s0.sp - 7552#64 := by bv_omega
          rw [← hsc, v1_stackAt_encoder_split_dropStack48 (s0.sp - 2400#64), h7552, ← h904]
          dsimp only [protoPolynomialEncoderSize]
          simp only [arm64_norm] at hmerge ⊢
          refine Entails.trans (Entails.of_eq (show _ =
            (memRegion (s0.sp - 2400#64) 232 ∗
             ((s0.sp - 2168#64) ↦₆₄ w232) ∗
             memRegion (s0.sp - 2160#64) 1256 ∗
             memRegion (s0.sp - 904#64) 56 ∗
             memRegion (s0.sp - 848#64) 752) ∗
            (memRegion (s0.sp - 7552#64) 1008 ∗
             stackAt (s0.sp - 2400#64) dropStack48 ∗
             statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
             A.pool lim (M.stepEvents w st) sc ∗ Rest) by sep_ac_rfl)) ?_
          exact Entails.trans (sepConj_mono_left hmerge) (Entails.of_eq (by sep_ac_rfl))
        · wp_done
      · intro evs s3 hevs hpc3 hrun3 ⟨hsp3, hx19_3, hx26_3, htr3⟩
        have herr := v1_err_5940_placed_budget A lim (M.stepEvents evs st) (F := F) (ext := ext)
          s0 s3 out Rest hsp0_align hpc3 hrun3 hsp3 hx19_3 hx26_3 htr3
        refine SepWP.mono herr fun sf Pf _ _ ⟨hPf, _, hsp_f, hcc_f, htr_f⟩ =>
          ⟨evs, hevs, hPf, hsp_f, hcc_f, htr_f⟩

theorem v1_drop_sendingHdr_4332_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (out : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4332#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx26_1 : (s1.readReg64 .x26).extractLsb' 0 8 = spqrErrorByte .stateDecode)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 1496 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
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
  v1_drop_sendingHdr_4332_of_sub_placed
    (v1_drop_glue_proto_poly_encoder_ok_of_dealloc_placed hdealloc)
    st s0 s1 out optEnc w0 w8 w16 w24 w32 w40 w48 Rest
    hcl1 hsp0_align hpc1 hrun1 hsp1 hx19_1 hx26_1 htr1

/-- Drop `Option<ProtoPolynomialEncoder>` at `fsp + 1496` and return `Err(StateDecode)`
    (`+4332 -> s0.x30`). -/
theorem v1_drop_sendingHdr_4332_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4332#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx26_1 : (s1.readReg64 .x26).extractLsb' 0 8 = spqrErrorByte .stateDecode)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 1496 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
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
  v1_drop_sendingHdr_4332_of_dealloc_placed hA.dealloc
    st s0 s1 out optEnc w0 w8 w16 w24 w32 w40 w48 Rest
    hcl1 hsp0_align hpc1 hrun1 hsp1 hx19_1 hx26_1 htr1

theorem v1_drop_sendingHdr_4204_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdrop_cl : subroutine_ok (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 271)
      (withLsCodeLoaded lsmpl (dropProtoPolyEncoderSpec M A lim)))
    (st : M.σ) (s0 s1 : State) (out : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4204#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 1496 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
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
  refine seq_clean_lscl_st hcl1
    (mid := lsmpl.base 333 + 4332#64)
    (P_mid := fun sm =>
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 1496 ∗
      v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
      v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
      memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      A.pool lim st sm ∗
      Rest)
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      (sm.readReg64 .x26).extractLsb' 0 8 = spqrErrorByte .stateDecode ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · dsimp only [spqrErrorByte, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    change s1.pc = (blkPl_333).base + 4204#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 4332#64) s1 _ _
    wp_steps_sync_333 ((blkPl_333).base + 4332#64)
    simp only [State.setMem_setMem]
    refine align_pre_st (by sep_ac_rfl) ?_
    wp_done
  · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, hx26_2, htr2⟩
    exact v1_drop_sendingHdr_4332_of_sub_placed (F := F) hdrop_cl st s0 s2 out optEnc
      w0 w8 w16 w24 w32 w40 w48 Rest hcl2 hsp0_align hpc2 hrun2 hsp2 hx19_2 hx26_2 htr2

theorem v1_drop_sendingHdr_4204_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (out : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4204#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 1496 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
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
  v1_drop_sendingHdr_4204_of_sub_placed
    (v1_drop_glue_proto_poly_encoder_ok_of_dealloc_placed hdealloc)
    st s0 s1 out optEnc w0 w8 w16 w24 w32 w40 w48 Rest
    hcl1 hsp0_align hpc1 hrun1 hsp1 hx19_1 htr1

/-- Drop `Option<ProtoPolynomialEncoder>` from `+4204` (`w26 := 0 -> +4332 -> s0.x30`). -/
theorem v1_drop_sendingHdr_4204_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4204#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 1496 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
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
  v1_drop_sendingHdr_4204_of_dealloc_placed hA.dealloc
    st s0 s1 out optEnc w0 w8 w16 w24 w32 w40 w48 Rest
    hcl1 hsp0_align hpc1 hrun1 hsp1 hx19_1 htr1

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux

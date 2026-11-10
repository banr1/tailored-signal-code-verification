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
public import LibsignalBinary.Proofs.SpqrV1.Auth.FromPbBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2bPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2a
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2b
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Budget-Threaded Variant 1 (`KeysSampled`) — Part B

Relocatable Block-`333` stack copy, validation error/success paths, and `auth.rootKey` clone
(`+1104 -> +8756`) under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2bPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkLib_eq_333 blkPC_333 blkPl_333
   lsProg_333 lsmpl lsρ withLsCodeLoaded)
open CryptoVerification.LibsignalSpqrV1 (ProtoAuthenticator ProtoPolynomialEncoder)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.Alloc (spqrRustAllocSym spqrRustNoAllocShimSym)
open CryptoVerification.SpqrV1.Drop (chunkedStatesSize optProtoInnerStateSize vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved ofNat_beq_zero_false resultChunkedStatesAt
   stackAt_encoderFromPb_split_allocHook statesFromPbSavedCells statesFromPbStack
   v1_bv_add_add_lit v1_bv_sub_sub_lit v1_frame_entails_192_216_224_1496
   v1_memRegion_1392_split_frame v1_merge_1392_104_1496 v1_optProtoAuthHeap
   v1_optProtoPolyEncoderHeap v1_optProtoPolyEncoderWordsAt v1_pb128At
   v1_pb128_entails_full_224 v1_shl8_extract_0_8 v1_ucWordsAt v1_ucWordsAt_entails_104
   vecU8Payload_of_nil vecU8Payload_pos vecU8Payload_pos_dealloc vecU8Payload_pos_unpack)
open CryptoVerification.SpqrV1.Unchunked
  (extractLsb'_0_64_append extractLsb'_64_64_append vecU8Payload vecU8Payload_entails_dealloc)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEvents FreeOnlyEvs
   RustCliAllocBudget RustLayoutOk VmPreserved rustAllocEvents rustCliAllocNoOomSpec
   rustCliDeallocBudgetSpec subroutine_ok_allocNoOom_of_budget)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (allocMemcpyVmSpec rustAllocShimVmSpec)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.Auth.FromPbBudget (authKeyCloneEvents)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget (dropProtoPolyEncoderSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (isTotalTrapHooks_withPanics_vmTrapHooks sepWP_lsBlock_vmPreserved
   stripS_calleeSavedVRegs stripS_pc stripS_readReg64 stripS_sp stripS_status stripS_trace
   vmTrapHooks)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
  (FromPbAllocHooksPlacedBudget spqrRustDeallocSym)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
  (FromPbAllocHooksBudget seq_clean_lscl_st v1_dealloc_ok_of_dealloc_placed
   v1_drop_glue_proto_poly_encoder_ok_of_dealloc_placed v1_drop_sendingHdr_4204_of_sub_placed
   v1_drop_uc_and_sendingHdr_3872_of_sub_placed v1_drop_uc_and_sendingHdr_3936_of_sub_placed)
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

/-! ## Entry Copy (`+1104 -> +1196`) and `uc = None` Error Branch (`+1104 -> +4204 -> s0.x30`) -/

/-- `VmPreserved`-strengthened 160-byte copy of `s.uc` and `s.sendingHdr` to the stack frame
    (`+1104 -> +4204` if `u8 + 1 == 0`, else `+1196`). -/
theorem v1_copy_pb_to_stack_1104_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1104#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (if (u8 + 1#64 == 0#64) = true then lsmpl.base 333 + 4204#64 else lsmpl.base 333 + 1196#64)
      s1
      (memRegion (s0.sp - 2400#64) 2304 ∗
        v1_pb128At pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
          w0 w8 w16 w24 w32 w40 w48 ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢
          memRegion (s0.sp - 2400#64) 1392 ∗
          v1_ucWordsAt (s0.sp - 2400#64 + 1392#64)
            u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
          v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
          memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
          v1_pb128At pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
            w0 w8 w16 w24 w32 w40 w48 ∗ Rest) ∧
        VmPreserved s1 s2 ∧ s2.sp = s0.sp - 2400#64 ∧
        s2.readReg64 .x19 = out ∧ s2.readReg64 .x20 = u8 ∧
        s2.readReg64 .x27 = pbA ∧ TraceCalleeSaved s2 s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant2bPlaced.v1_copy_pb_to_stack_1104_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      out pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
      w0 w8 w16 w24 w32 w40 w48 Rest hsp0_align
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1) (by simpa using hx27_1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun s2 P2 hvm ⟨hP2, hsp2, hx19_2, hx20_2, hx27_2, htr2⟩ =>
      ⟨hP2, hvm, hsp2, hx19_2, hx20_2, hx27_2, htr2⟩

theorem v1_copy_pb_to_stack_1104_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1104#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (if (u8 + 1#64 == 0#64) = true then lsmpl.base 333 + 4204#64 else lsmpl.base 333 + 1196#64)
      s1
      (memRegion (s0.sp - 2400#64) 2304 ∗
        v1_pb128At pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
          w0 w8 w16 w24 w32 w40 w48 ∗ A.pool lim st s1 ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢
          memRegion (s0.sp - 2400#64) 1392 ∗
          v1_ucWordsAt (s0.sp - 2400#64 + 1392#64)
            u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
          v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
          memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
          v1_pb128At pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
            w0 w8 w16 w24 w32 w40 w48 ∗ A.pool lim st s2 ∗ Rest) ∧
        VmPreserved s1 s2 ∧ s2.sp = s0.sp - 2400#64 ∧
        s2.readReg64 .x19 = out ∧ s2.readReg64 .x20 = u8 ∧
        s2.readReg64 .x27 = pbA ∧ TraceCalleeSaved s2 s0) := by
  have hwp := v1_copy_pb_to_stack_1104_placed (ext := ext) s0 s1 out pbA
    u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
    w0 w8 w16 w24 w32 w40 w48 (A.pool lim st s1 ∗ Rest)
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1
  refine SepWP.mono hwp fun s2 P2 _ _ ⟨hP2, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hP2
  exact ⟨Entails.trans hP2 (Entails.of_eq (by sep_ac_rfl)), hvm, hrest⟩

/-- Variant 1 error path when `s.uc = none` (`+1104 -> +4204 -> s0.x30`) under an explicit
    Block-`271` drop-glue contract and arbitrary spatial frame `Rest`. -/
theorem v1_keysSampled_uc_none_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdrop_cl : subroutine_ok (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 271)
      (withLsCodeLoaded lsmpl (dropProtoPolyEncoderSpec M A lim)))
    (st : M.σ) (s0 s1 : State) (hcl1 : LibsignalCodeLoaded lsmpl s1.mem) (out pbA : BitVec 64)
    (u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1104#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗ statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗ (pbA ↦₆₄ 0x8000000000000001#64) ∗
        v1_pb128At pbA noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
          w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (pbA + 168#64) 56 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        A.pool lim st s1 ∗ Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            memRegion pbA optProtoInnerStateSize ∗
            A.pool lim (M.stepEvents evs st) sf ∗ Rest ∗ stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hcopy := v1_copy_pb_to_stack_1104_placed_budget A lim st (ext := ext) s0 s1 out pbA
    noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 w0 w8 w16 w24 w32 w40 w48
    (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize ∗ (pbA ↦₆₄ 0x8000000000000001#64) ∗
     memRegion (pbA + 168#64) 56 ∗
     v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗ Rest)
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1
  have hcmn : (noneCap + 1#64 == 0#64) = true := by decide
  simp only [hcmn, ↓reduceIte] at hcopy
  refine seq_clean_lscl_st hcl1
    (mid := lsmpl.base 333 + 4204#64)
    (P_mid := fun s2 =>
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 1496 ∗
      v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
      v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
      memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
      statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
      A.pool lim st s2 ∗ (memRegion pbA optProtoInnerStateSize ∗ Rest))
    (Q := fun s2 =>
      s2.sp = s0.sp - 2400#64 ∧ s2.readReg64 .x19 = out ∧ TraceCalleeSaved s2 s0)
    (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (SepWP.mono hcopy fun s2 P2 _ _ ⟨hP2, _, hsp2, hx19_2, _, _, htr2⟩ => ?_)) ?_
  · refine ⟨Entails.trans hP2 ?_, hsp2, hx19_2, htr2⟩
    have huc := v1_ucWordsAt_entails_104 (s0.sp - 2400#64 + 1392#64)
      noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
    have h1496 := v1_merge_1392_104_1496 (s0.sp - 2400#64)
    have hpb := v1_pb128_entails_full_224 pbA
      noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 w0 w8 w16 w24 w32 w40 w48
    refine Entails.trans (Entails.of_eq (show _ =
      (memRegion (s0.sp - 2400#64) 1392 ∗
       v1_ucWordsAt (s0.sp - 2400#64 + 1392#64)
         noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104) ∗
      ((pbA ↦₆₄ 0x8000000000000001#64) ∗
       v1_pb128At pbA noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
         w0 w8 w16 w24 w32 w40 w48 ∗
       memRegion (pbA + 168#64) 56) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
       v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
       memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
       A.pool lim st s2 ∗ Rest) by sep_ac_rfl)) ?_
    exact Entails.trans
      (sepConj_mono (Entails.trans (sepConj_mono_right huc) h1496) (sepConj_mono_left hpb))
      (Entails.of_eq (by sep_ac_rfl))
  · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, htr2⟩
    have hdrop := v1_drop_sendingHdr_4204_of_sub_placed (F := F) hdrop_cl st s0 s2 out optEnc
      w0 w8 w16 w24 w32 w40 w48 (memRegion pbA optProtoInnerStateSize ∗ Rest)
      hcl2 hsp0_align hpc2 hrun2 hsp2 hx19_2 htr2
    refine SepWP.mono hdrop fun sf Pf _ _ ⟨evs, hevs, hPf, hsp_f, hcc_f, htr_f⟩ =>
      ⟨evs, hevs, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hsp_f, hcc_f, htr_f⟩

/-- Variant 1 `s.uc = none` error path (`+1104 -> +4204 -> s0.x30`) from `HookSat ... dealloc`. -/
theorem v1_keysSampled_uc_none_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (hcl1 : LibsignalCodeLoaded lsmpl s1.mem) (out pbA : BitVec 64)
    (u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1104#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗ statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗ (pbA ↦₆₄ 0x8000000000000001#64) ∗
        v1_pb128At pbA noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
          w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (pbA + 168#64) 56 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        A.pool lim st s1 ∗ Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            memRegion pbA optProtoInnerStateSize ∗
            A.pool lim (M.stepEvents evs st) sf ∗ Rest ∗ stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v1_keysSampled_uc_none_of_sub_placed
    (v1_drop_glue_proto_poly_encoder_ok_of_dealloc_placed hdealloc)
    st s0 s1 hcl1 out pbA u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
    optEnc w0 w8 w16 w24 w32 w40 w48 Rest hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1

/-- Framed Variant 1 error path when `s.uc = none` (`+1104 -> +4204 -> s0.x30`) under
    `FromPbAllocHooksBudget` and arbitrary `Rest : SepProp`. -/
theorem v1_keysSampled_uc_none_rest_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (hcl1 : LibsignalCodeLoaded lsmpl s1.mem) (out pbA : BitVec 64)
    (u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1104#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗ statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗ (pbA ↦₆₄ 0x8000000000000001#64) ∗
        v1_pb128At pbA noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
          w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (pbA + 168#64) 56 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        A.pool lim st s1 ∗ Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            memRegion pbA optProtoInnerStateSize ∗
            A.pool lim (M.stepEvents evs st) sf ∗ Rest ∗ stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v1_keysSampled_uc_none_of_dealloc_placed hA.dealloc
    st s0 s1 hcl1 out pbA u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
    optEnc w0 w8 w16 w24 w32 w40 w48 Rest hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1

/-- Variant 1 error path when `s.uc = none` (`+1104 -> +4204 -> s0.x30`). -/
theorem v1_keysSampled_uc_none_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (hcl1 : LibsignalCodeLoaded lsmpl s1.mem) (out pbA : BitVec 64)
    (u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1104#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗ statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗ (pbA ↦₆₄ 0x8000000000000001#64) ∗
        v1_pb128At pbA noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
          w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (pbA + 168#64) 56 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        A.pool lim st s1)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            memRegion pbA optProtoInnerStateSize ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hwp := v1_keysSampled_uc_none_rest_placed (F := F) hA st s0 s1 hcl1 out pbA
    u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
    optEnc w0 w8 w16 w24 w32 w40 w48 emp hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1
  refine SepWP.weaken_pre (Entails.of_eq (by simp only [sepConj_emp]))
    (SepWP.mono hwp fun sf Pf _ _ ⟨evs, hevs, hPf, hrest⟩ =>
      ⟨evs, hevs, Entails.trans hPf (Entails.of_eq (by simp only [emp_sepConj, sepConj_emp])),
        hrest⟩)

/-! ## Validation (`+1196..+1292`) and `Authenticator::from_pb` Root-Key Clone (`+1292..+8756`) -/

/-- Validation error paths at `+1196` under explicit Block-`333` `__rust_dealloc` and Block-`271`
    drop-glue contracts: when `u48 != 2400#64`, `u24 != 1152#64`, or `optAuth = none`, cleans up
    `uc` and `sendingHdr` (`FreeOnlyEvs`) and returns `Err(StateDecode)`. -/
theorem v1_validate_err_1196_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hdrop_cl : subroutine_ok (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 271)
      (withLsCodeLoaded lsmpl (dropProtoPolyEncoderSpec M A lim)))
    (st : M.σ) (s0 s1 : State) (hcl1 : LibsignalCodeLoaded lsmpl s1.mem) (out pbA : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 : BitVec 64)
    (optAuth : Option ProtoAuthenticator)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp) (herr : (u48 == 2400#64) = false ∨ (u24 == 1152#64) = false ∨ optAuth = none)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1196#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = u8) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 1392 ∗
        v1_ucWordsAt (s0.sp - 2400#64 + 1392#64)
          u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        vecCapPtrDealloc A.repAlloc u8 u16 ∗ vecCapPtrDealloc A.repAlloc u32 u40 ∗
        v1_optProtoAuthHeap A.repAlloc optAuth u56 u64 u72 u80 u88 u96 ∗
        A.pool lim st s1 ∗ Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ Rest ∗ stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left
    (v1_memRegion_1392_split_frame (s0.sp - 2400#64)))) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro w232
  apply ProofLib.SepWP.exists_left; intro w224
  apply ProofLib.SepWP.exists_left; intro w216
  apply ProofLib.SepWP.exists_left; intro w200
  apply ProofLib.SepWP.exists_left; intro w192
  apply ProofLib.SepWP.exists_left; intro w184
  apply ProofLib.SepWP.exists_left; intro w176
  apply ProofLib.SepWP.exists_left; intro w64
  by_cases hdk_ek : (u48 == 2400#64) = true ∧ (u24 == 1152#64) = true
  · rcases hdk_ek with ⟨hdk, hek⟩
    have hauth : optAuth = none := by
      rcases herr with h | h | h
      · rw [hdk] at h; cases h
      · rw [hek] at h; cases h
      · exact h
    subst hauth
    dsimp only [v1_optProtoAuthHeap]
    wp_simp_pre [sepConj_assoc, sepConj_left_comm _ ⌜_⌝, sepConj_comm _ ⌜_⌝]
    apply SepWP.pure_elim
    intro hu56
    subst hu56
    refine seq_clean_lscl_st hcl1
      (mid := lsmpl.base 333 + 3936#64)
      (P_mid := fun s2 =>
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 192 ∗ ((s0.sp - 2400#64 + 192#64) ↦₆₄ w192) ∗
        memRegion (s0.sp - 2400#64 + 200#64) 16 ∗ ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗ memRegion (s0.sp - 2400#64 + 232#64) 1264 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗ statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗ vecCapPtrDealloc A.repAlloc u8 u16 ∗
        vecCapPtrDealloc A.repAlloc u32 u40 ∗ A.pool lim st s2 ∗ Rest)
      (Q := fun s2 =>
        s2.sp = s0.sp - 2400#64 ∧ s2.readReg64 .x19 = out ∧ s2.readReg64 .x20 = u8 ∧
        s2.readReg64 .x9 = u16 ∧ TraceCalleeSaved s2 s0)
      ?_ ?_
    · dsimp only [v1_ucWordsAt, noneCap, BitVec.ofNat_eq_ofNat] at hpc1 hdk hek ⊢
      change s1.pc = (blkPl_333).base + 1196#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 3936#64) s1 _ _
      wp_steps_sync_333 ((blkPl_333).base + 3936#64)
      simp only [State.setMem_setMem]
      refine entails_pre_st ?_ ?_
      · intro sc hsc
        rw [← hsc]
        have hf := v1_frame_entails_192_216_224_1496 (s0.sp - 2400#64)
          w64 w176 w184 w192 w200 u40 u32 w232
          u8 u16 u24 u32 u40 u48 18446744073709551615#64 u64 u72 u80 u88 u96 u104
        dsimp only [v1_ucWordsAt] at hf
        simp only [arm64_norm] at hf ⊢
        refine Entails.trans (Entails.of_eq (show _ =
          (memRegion (s0.sp - 2400#64) 64 ∗ ((s0.sp - 2336#64) ↦₆₄ w64) ∗
           memRegion (s0.sp - 2328#64) 104 ∗ ((s0.sp - 2224#64) ↦₆₄ w176) ∗
           ((s0.sp - 2216#64) ↦₆₄ w184) ∗ ((s0.sp - 2208#64) ↦₆₄ w192) ∗
           ((s0.sp - 2200#64) ↦₆₄ w200) ∗ memRegion (s0.sp - 2192#64) 8 ∗
           ((s0.sp - 2184#64) ↦₆₄ u40) ∗ ((s0.sp - 2176#64) ↦₆₄ u32) ∗
           ((s0.sp - 2168#64) ↦₆₄ w232) ∗ memRegion (s0.sp - 2160#64) 1152 ∗
           ((s0.sp - 1008#64) ↦₆₄ u8) ∗ ((s0.sp - 1000#64) ↦₆₄ u16) ∗
           ((s0.sp - 992#64) ↦₆₄ u24) ∗ ((s0.sp - 984#64) ↦₆₄ u32) ∗
           ((s0.sp - 976#64) ↦₆₄ u40) ∗ ((s0.sp - 968#64) ↦₆₄ u48) ∗
           ((s0.sp - 960#64) ↦₆₄ 18446744073709551615#64) ∗ ((s0.sp - 952#64) ↦₆₄ u64) ∗
           ((s0.sp - 944#64) ↦₆₄ u72) ∗ ((s0.sp - 936#64) ↦₆₄ u80) ∗
           ((s0.sp - 928#64) ↦₆₄ u88) ∗ ((s0.sp - 920#64) ↦₆₄ u96) ∗
           ((s0.sp - 912#64) ↦₆₄ u104)) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           v1_optProtoPolyEncoderWordsAt (s0.sp - 904#64) w0 w8 w16 w24 w32 w40 w48 ∗
           v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
           memRegion (s0.sp - 848#64) 752 ∗ statesFromPbSavedCells s0 ∗
           memRegion out chunkedStatesSize ∗ vecCapPtrDealloc A.repAlloc u8 u16 ∗
           vecCapPtrDealloc A.repAlloc u32 u40 ∗ A.pool lim st sc ∗ Rest) by sep_ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hf) (Entails.of_eq (by sep_ac_rfl))
      · wp_done
    · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, hx20_2, hx9_2, htr2⟩
      exact v1_drop_uc_and_sendingHdr_3936_of_sub_placed (F := F) hdealloc_ok hdrop_cl st s0 s2 out
        u8 u16 u32 u40 w192 optEnc w0 w8 w16 w24 w32 w40 w48 Rest
        hcl2 hsp0_align hpc2 hrun2 hsp2 hx19_2 hx20_2 hx9_2 htr2
  · refine seq_clean_lscl_st hcl1
      (mid := lsmpl.base 333 + 3872#64)
      (P_mid := fun s2 =>
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 192 ∗ ((s0.sp - 2400#64 + 192#64) ↦₆₄ w192) ∗
        memRegion (s0.sp - 2400#64 + 200#64) 16 ∗ ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗ memRegion (s0.sp - 2400#64 + 232#64) 1264 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗ statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗ vecCapPtrDealloc A.repAlloc u8 u16 ∗
        vecCapPtrDealloc A.repAlloc u32 u40 ∗
        v1_optProtoAuthHeap A.repAlloc optAuth u56 u64 u72 u80 u88 u96 ∗ A.pool lim st s2 ∗ Rest)
      (Q := fun s2 =>
        s2.sp = s0.sp - 2400#64 ∧ s2.readReg64 .x19 = out ∧ s2.readReg64 .x20 = u8 ∧
        s2.readReg64 .x9 = u16 ∧ s2.readReg64 .x25 = u56 ∧ s2.readReg64 .x28 = u64 ∧
        s2.readReg64 .x23 = u80 ∧ s2.readReg64 .x24 = u88 ∧ TraceCalleeSaved s2 s0)
      ?_ ?_
    · have hf := v1_frame_entails_192_216_224_1496 (s0.sp - 2400#64)
        w64 w176 w184 w192 w200 u40 u32 w232
        u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
      dsimp only [v1_ucWordsAt] at hf
      simp only [arm64_norm] at hf
      by_cases hdk : (u48 == 2400#64) = true
      · have hek_f : (u24 == 1152#64) = false :=
          Bool.eq_false_iff.mpr fun hek => hdk_ek ⟨hdk, hek⟩
        dsimp only [v1_ucWordsAt, BitVec.ofNat_eq_ofNat] at hpc1 hdk hek_f ⊢
        change s1.pc = (blkPl_333).base + 1196#64 at hpc1
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 3872#64) s1 _ _
        wp_steps_sync_333 ((blkPl_333).base + 3872#64)
        refine entails_pre_st ?_ ?_
        · intro sc hsc
          rw [← hsc]
          simp only [arm64_norm]
          refine Entails.trans (Entails.of_eq (show _ =
            (memRegion (s0.sp - 2400#64) 64 ∗ ((s0.sp - 2336#64) ↦₆₄ w64) ∗
             memRegion (s0.sp - 2328#64) 104 ∗ ((s0.sp - 2224#64) ↦₆₄ w176) ∗
             ((s0.sp - 2216#64) ↦₆₄ w184) ∗ ((s0.sp - 2208#64) ↦₆₄ w192) ∗
             ((s0.sp - 2200#64) ↦₆₄ w200) ∗ memRegion (s0.sp - 2192#64) 8 ∗
             ((s0.sp - 2184#64) ↦₆₄ u40) ∗ ((s0.sp - 2176#64) ↦₆₄ u32) ∗
             ((s0.sp - 2168#64) ↦₆₄ w232) ∗ memRegion (s0.sp - 2160#64) 1152 ∗
             ((s0.sp - 1008#64) ↦₆₄ u8) ∗ ((s0.sp - 1000#64) ↦₆₄ u16) ∗
             ((s0.sp - 992#64) ↦₆₄ u24) ∗ ((s0.sp - 984#64) ↦₆₄ u32) ∗
             ((s0.sp - 976#64) ↦₆₄ u40) ∗ ((s0.sp - 968#64) ↦₆₄ u48) ∗
             ((s0.sp - 960#64) ↦₆₄ u56) ∗ ((s0.sp - 952#64) ↦₆₄ u64) ∗
             ((s0.sp - 944#64) ↦₆₄ u72) ∗ ((s0.sp - 936#64) ↦₆₄ u80) ∗
             ((s0.sp - 928#64) ↦₆₄ u88) ∗ ((s0.sp - 920#64) ↦₆₄ u96) ∗
             ((s0.sp - 912#64) ↦₆₄ u104)) ∗
            (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
             v1_optProtoPolyEncoderWordsAt (s0.sp - 904#64) w0 w8 w16 w24 w32 w40 w48 ∗
             v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
             memRegion (s0.sp - 848#64) 752 ∗ statesFromPbSavedCells s0 ∗
             memRegion out chunkedStatesSize ∗ vecCapPtrDealloc A.repAlloc u8 u16 ∗
             vecCapPtrDealloc A.repAlloc u32 u40 ∗
             v1_optProtoAuthHeap A.repAlloc optAuth u56 u64 u72 u80 u88 u96 ∗
             A.pool lim st sc ∗ Rest) by sep_ac_rfl)) ?_
          exact Entails.trans (sepConj_mono_left hf) (Entails.of_eq (by sep_ac_rfl))
        · wp_done
      · have hdk_f : (u48 == 2400#64) = false := Bool.eq_false_iff.mpr hdk
        dsimp only [v1_ucWordsAt, BitVec.ofNat_eq_ofNat] at hpc1 hdk_f ⊢
        change s1.pc = (blkPl_333).base + 1196#64 at hpc1
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 3872#64) s1 _ _
        wp_steps_sync_333 ((blkPl_333).base + 3872#64)
        refine entails_pre_st ?_ ?_
        · intro sc hsc
          rw [← hsc]
          simp only [arm64_norm]
          refine Entails.trans (Entails.of_eq (show _ =
            (memRegion (s0.sp - 2400#64) 64 ∗ ((s0.sp - 2336#64) ↦₆₄ w64) ∗
             memRegion (s0.sp - 2328#64) 104 ∗ ((s0.sp - 2224#64) ↦₆₄ w176) ∗
             ((s0.sp - 2216#64) ↦₆₄ w184) ∗ ((s0.sp - 2208#64) ↦₆₄ w192) ∗
             ((s0.sp - 2200#64) ↦₆₄ w200) ∗ memRegion (s0.sp - 2192#64) 8 ∗
             ((s0.sp - 2184#64) ↦₆₄ u40) ∗ ((s0.sp - 2176#64) ↦₆₄ u32) ∗
             ((s0.sp - 2168#64) ↦₆₄ w232) ∗ memRegion (s0.sp - 2160#64) 1152 ∗
             ((s0.sp - 1008#64) ↦₆₄ u8) ∗ ((s0.sp - 1000#64) ↦₆₄ u16) ∗
             ((s0.sp - 992#64) ↦₆₄ u24) ∗ ((s0.sp - 984#64) ↦₆₄ u32) ∗
             ((s0.sp - 976#64) ↦₆₄ u40) ∗ ((s0.sp - 968#64) ↦₆₄ u48) ∗
             ((s0.sp - 960#64) ↦₆₄ u56) ∗ ((s0.sp - 952#64) ↦₆₄ u64) ∗
             ((s0.sp - 944#64) ↦₆₄ u72) ∗ ((s0.sp - 936#64) ↦₆₄ u80) ∗
             ((s0.sp - 928#64) ↦₆₄ u88) ∗ ((s0.sp - 920#64) ↦₆₄ u96) ∗
             ((s0.sp - 912#64) ↦₆₄ u104)) ∗
            (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
             v1_optProtoPolyEncoderWordsAt (s0.sp - 904#64) w0 w8 w16 w24 w32 w40 w48 ∗
             v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
             memRegion (s0.sp - 848#64) 752 ∗ statesFromPbSavedCells s0 ∗
             memRegion out chunkedStatesSize ∗ vecCapPtrDealloc A.repAlloc u8 u16 ∗
             vecCapPtrDealloc A.repAlloc u32 u40 ∗
             v1_optProtoAuthHeap A.repAlloc optAuth u56 u64 u72 u80 u88 u96 ∗
             A.pool lim st sc ∗ Rest) by sep_ac_rfl)) ?_
          exact Entails.trans (sepConj_mono_left hf) (Entails.of_eq (by sep_ac_rfl))
        · wp_done
    · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, hx20_2, hx9_2, hx25_2, hx28_2, hx23_2, hx24_2, htr2⟩
      exact v1_drop_uc_and_sendingHdr_3872_of_sub_placed (F := F) hdealloc_ok hdrop_cl st s0 s2 out
        u8 u16 u32 u40 w192 optAuth u56 u64 u72 u80 u88 u96
        optEnc w0 w8 w16 w24 w32 w40 w48 Rest
        hcl2 hsp0_align hpc2 hrun2 hsp2 hx19_2 hx20_2 hx9_2 hx25_2 hx28_2 hx23_2 hx24_2 htr2

/-- Validation error paths at `+1196` from `HookSat ... dealloc`. -/
theorem v1_validate_err_1196_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (hcl1 : LibsignalCodeLoaded lsmpl s1.mem) (out pbA : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 : BitVec 64)
    (optAuth : Option ProtoAuthenticator)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp) (herr : (u48 == 2400#64) = false ∨ (u24 == 1152#64) = false ∨ optAuth = none)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1196#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = u8) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 1392 ∗
        v1_ucWordsAt (s0.sp - 2400#64 + 1392#64)
          u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        vecCapPtrDealloc A.repAlloc u8 u16 ∗ vecCapPtrDealloc A.repAlloc u32 u40 ∗
        v1_optProtoAuthHeap A.repAlloc optAuth u56 u64 u72 u80 u88 u96 ∗
        A.pool lim st s1 ∗ Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ Rest ∗ stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v1_validate_err_1196_of_sub_placed
    (v1_dealloc_ok_of_dealloc_placed hdealloc)
    (v1_drop_glue_proto_poly_encoder_ok_of_dealloc_placed hdealloc)
    st s0 s1 hcl1 out pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
    optAuth optEnc w0 w8 w16 w24 w32 w40 w48 Rest herr hsp0_align hpc1 hrun1 hsp1 hx19_1 hx20_1 htr1

/-- Validation error paths at `+1196` under `FromPbAllocHooksBudget`: when `u48 != 2400#64`,
    `u24 != 1152#64`, or `optAuth = none`, cleans up `uc` and `sendingHdr` and returns
    `Err(StateDecode)`. -/
theorem v1_validate_err_1196_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (hcl1 : LibsignalCodeLoaded lsmpl s1.mem) (out pbA : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 : BitVec 64)
    (optAuth : Option ProtoAuthenticator)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp) (herr : (u48 == 2400#64) = false ∨ (u24 == 1152#64) = false ∨ optAuth = none)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1196#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = u8) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 1392 ∗
        v1_ucWordsAt (s0.sp - 2400#64 + 1392#64)
          u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        vecCapPtrDealloc A.repAlloc u8 u16 ∗ vecCapPtrDealloc A.repAlloc u32 u40 ∗
        v1_optProtoAuthHeap A.repAlloc optAuth u56 u64 u72 u80 u88 u96 ∗
        A.pool lim st s1 ∗ Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ Rest ∗ stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v1_validate_err_1196_of_dealloc_placed hA.dealloc
    st s0 s1 hcl1 out pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
    optAuth optEnc w0 w8 w16 w24 w32 w40 w48 Rest herr hsp0_align hpc1 hrun1 hsp1 hx19_1 hx20_1 htr1

/-- `VmPreserved`-strengthened validation success step (`+1196 -> +1292`). -/
theorem v1_validate_ok_1196_1292_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 : BitVec 64)
    (w64 w176 w192 w216 w224 w232 : BitVec 64) (Rest : SepProp)
    (hdk : (u48 == 2400#64) = true) (hek : (u24 == 1152#64) = true) (hu56 : u56.toNat < 2 ^ 63)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1196#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = u8) (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 1292#64) s1
      (((s0.sp - 2400#64 + 64#64) ↦₆₄ w64) ∗ ((s0.sp - 2400#64 + 176#64) ↦₆₄ w176) ∗
        ((s0.sp - 2400#64 + 192#64) ↦₆₄ w192) ∗ ((s0.sp - 2400#64 + 216#64) ↦₆₄ w216) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ w224) ∗ ((s0.sp - 2400#64 + 232#64) ↦₆₄ w232) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 1152 ∗
        v1_ucWordsAt (s0.sp - 2400#64 + 1392#64)
          u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢
          ((s0.sp - 2400#64 + 64#64) ↦₆₄ u104) ∗ ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
          ((s0.sp - 2400#64 + 192#64) ↦₆₄ u48) ∗ ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
          ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗ ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗
          memRegion (s0.sp - 2400#64 + 240#64) 1256 ∗ Rest) ∧
        VmPreserved s1 s2 ∧ s2.sp = s0.sp - 2400#64 ∧
        s2.readReg64 .x19 = out ∧ s2.readReg64 .x20 = u72 ∧
        s2.readReg64 .x21 = u8 ∧ s2.readReg64 .x22 = u48 ∧
        s2.readReg64 .x23 = u80 ∧ s2.readReg64 .x24 = u88 ∧
        s2.readReg64 .x25 = u56 ∧ s2.readReg64 .x27 = pbA ∧
        s2.readReg64 .x28 = u64 ∧ s2.readReg64 .x9 = u96 ∧ TraceCalleeSaved s2 s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant2bPlaced.v1_validate_ok_1196_1292_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      out pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
      w64 w176 w192 w216 w224 w232 Rest hdk hek hu56 hsp0_align
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1) (by simpa using hx20_1) (by simpa using hx27_1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun s2 P2 hvm ⟨hP2, hregs⟩ => ⟨hP2, hvm, hregs⟩

theorem v1_validate_ok_1196_1292_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 : BitVec 64)
    (w64 w176 w192 w216 w224 w232 : BitVec 64) (Rest : SepProp)
    (hdk : (u48 == 2400#64) = true) (hek : (u24 == 1152#64) = true) (hu56 : u56.toNat < 2 ^ 63)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1196#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = u8) (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 1292#64) s1
      (((s0.sp - 2400#64 + 64#64) ↦₆₄ w64) ∗ ((s0.sp - 2400#64 + 176#64) ↦₆₄ w176) ∗
        ((s0.sp - 2400#64 + 192#64) ↦₆₄ w192) ∗ ((s0.sp - 2400#64 + 216#64) ↦₆₄ w216) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ w224) ∗ ((s0.sp - 2400#64 + 232#64) ↦₆₄ w232) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 1152 ∗
        v1_ucWordsAt (s0.sp - 2400#64 + 1392#64)
          u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
        A.pool lim st s1 ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢
          ((s0.sp - 2400#64 + 64#64) ↦₆₄ u104) ∗ ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
          ((s0.sp - 2400#64 + 192#64) ↦₆₄ u48) ∗ ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
          ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗ ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗
          memRegion (s0.sp - 2400#64 + 240#64) 1256 ∗ A.pool lim st s2 ∗ Rest) ∧
        VmPreserved s1 s2 ∧ s2.sp = s0.sp - 2400#64 ∧
        s2.readReg64 .x19 = out ∧ s2.readReg64 .x20 = u72 ∧
        s2.readReg64 .x21 = u8 ∧ s2.readReg64 .x22 = u48 ∧
        s2.readReg64 .x23 = u80 ∧ s2.readReg64 .x24 = u88 ∧
        s2.readReg64 .x25 = u56 ∧ s2.readReg64 .x27 = pbA ∧
        s2.readReg64 .x28 = u64 ∧ s2.readReg64 .x9 = u96 ∧ TraceCalleeSaved s2 s0) := by
  have hwp := v1_validate_ok_1196_1292_placed (ext := ext) s0 s1 out pbA
    u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
    w64 w176 w192 w216 w224 w232 (A.pool lim st s1 ∗ Rest)
    hdk hek hu56 hsp0_align hpc1 hrun1 hsp1 hx19_1 hx20_1 hx27_1 htr1
  refine SepWP.mono hwp fun s2 P2 _ _ ⟨hP2, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hP2
  exact ⟨Entails.trans hP2 (Entails.of_eq (by sep_ac_rfl)), hvm, hrest⟩

set_option maxHeartbeats 800000 in
/-- Direct `SepWP` segment (`+1292 -> +8756`) of `Authenticator::from_pb` in Variant 1 under
    `FromPbAllocHooksPlacedBudget` and `FitsEvents M lim st (authKeyCloneEvents auth.rootKey)`,
    allocating and copying `auth.rootKey` into `pa1 = s1.readReg64 .x26` (or `1#64` if empty)
    with zero OOM/panic branches. -/
theorem v1_auth_from_pb_step1_1292_8756_placed_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s : State) (fsp out pbA u8 u56 u64 u80 u88 u96 : BitVec 64)
    (auth : ProtoAuthenticator) (Frame : SepProp)
    (hfits : FitsEvents M lim st (authKeyCloneEvents auth.rootKey))
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 1292#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 auth.rootKey.length)
    (hx21 : s.readReg64 .x21 = u8) (hx23 : s.readReg64 .x23 = u80) (hx24 : s.readReg64 .x24 = u88)
    (hx25 : s.readReg64 .x25 = u56) (hx27 : s.readReg64 .x27 = pbA) (hx28 : s.readReg64 .x28 = u64)
    (hx9 : s.readReg64 .x9 = u96) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 8756#64) s
      (stackAt fsp encoderFromPbStack ∗ ((fsp + 232#64) ↦₆₄ u96) ∗
       vecU8Payload A.repAlloc u56 u64 auth.rootKey ∗ A.pool lim st s ∗ Frame)
      (fun s1 P1 =>
        ∃ pa1 : BitVec 64,
          (P1 ⊢
            stackAt fsp encoderFromPbStack ∗ ((fsp + 232#64) ↦₆₄ u96) ∗
            vecCapPtrDealloc A.repAlloc u56 u64 ∗
            vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
            A.pool lim (M.stepEvents (authKeyCloneEvents auth.rootKey) st) s1 ∗ Frame) ∧
          s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧ s1.readReg64 .x21 = u8 ∧
          s1.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length ∧
          s1.readReg64 .x23 = u80 ∧ s1.readReg64 .x24 = u88 ∧
          s1.readReg64 .x25 = u56 ∧ s1.readReg64 .x26 = pa1 ∧
          s1.readReg64 .x27 = pbA ∧ s1.readReg64 .x28 = u64 ∧
          s1.readReg64 .x9 = u96 ∧ TraceCalleeSaved s1 s0) := by
  have hr_cases : auth.rootKey = [] ∨ 0 < auth.rootKey.length := by cases auth.rootKey <;> simp
  rcases hr_cases with hr_nil | hr_pos
  · have hevs : authKeyCloneEvents auth.rootKey = [] := by simp [authKeyCloneEvents, hr_nil]
    rw [hevs, M.stepEvents_nil]
    rw [hr_nil] at hx20 ⊢
    dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hpc hx20 ⊢
    change s.pc = (blkPl_333).base + 1292#64 at hpc
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 8756#64) s _ _
    refine SepWP.mono
      (P := stackAt fsp encoderFromPbStack ∗ ((fsp + 232#64) ↦₆₄ u96) ∗
        vecU8Payload A.repAlloc u56 u64 [] ∗ A.pool lim st s ∗ Frame)
      (post := fun s1 P1 =>
        (P1 ⊢
          stackAt fsp encoderFromPbStack ∗ ((fsp + 232#64) ↦₆₄ u96) ∗
          vecCapPtrDealloc A.repAlloc u56 u64 ∗ vecU8Payload A.repAlloc 0#64 1#64 [] ∗
          A.pool lim st s1 ∗ Frame) ∧
        s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧ s1.readReg64 .x21 = u8 ∧
        s1.readReg64 .x22 = 0#64 ∧ s1.readReg64 .x23 = u80 ∧ s1.readReg64 .x24 = u88 ∧
        s1.readReg64 .x25 = u56 ∧ s1.readReg64 .x26 = 1#64 ∧
        s1.readReg64 .x27 = pbA ∧ s1.readReg64 .x28 = u64 ∧
        s1.readReg64 .x9 = u96 ∧ TraceCalleeSaved s1 s0) ?_
      fun s1 P1 _ _ ⟨hP1, hregs⟩ => ⟨1#64, hP1, hregs⟩
    wp_steps_sync_333 ((blkPl_333).base + 8756#64)
    simp only [State.setMem_setMem]
    have hd := vecU8Payload_entails_dealloc A.repAlloc u56 u64 []
    have hn := vecU8Payload_of_nil A.repAlloc
    dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hn
    refine entails_pre_st ?_ ?_
    · intro sc hsc
      rw [← hsc]
      refine Entails.trans (Entails.of_eq (show _ =
        vecU8Payload A.repAlloc u56 u64 [] ∗ emp ∗
        stackAt fsp encoderFromPbStack ∗ ((fsp + 232#64) ↦₆₄ u96) ∗
        A.pool lim st sc ∗ Frame by sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono hd (sepConj_mono_left hn)) (Entails.of_eq (by sep_ac_rfl))
    · wp_done
  · have hne_nil : auth.rootKey.isEmpty = false := by
      cases h : auth.rootKey with | nil => simp [h] at hr_pos | cons => rfl
    have hevs : authKeyCloneEvents auth.rootKey = rustAllocEvents auth.rootKey.length 1 := by
      simp [authKeyCloneEvents, hne_nil]
    rw [hevs] at hfits ⊢
    refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (vecU8Payload_pos_unpack A.repAlloc u56 u64 auth.rootKey hr_pos)))) ?_
    refine SepWP.weaken_pre (Entails.of_eq (show
          stackAt fsp encoderFromPbStack ∗ ((fsp + 232#64) ↦₆₄ u96) ∗
          (⌜auth.rootKey.length ≤ u56.toNat ∧ u56.toNat < 2 ^ 63 ∧ u64 ≠ 0#64 ∧ u56 ≠ 0#64⌝ ∗
           (A.repAlloc.live u64 u56.toNat 1 ∗ (u64 ↦ₛ auth.rootKey) ∗
            memRegion (u64 + BitVec.ofNat 64 auth.rootKey.length)
              (u56.toNat - auth.rootKey.length))) ∗
          A.pool lim st s ∗ Frame =
        ⌜auth.rootKey.length ≤ u56.toNat ∧ u56.toNat < 2 ^ 63 ∧ u64 ≠ 0#64 ∧ u56 ≠ 0#64⌝ ∗
        (memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack ∗ ((fsp + 232#64) ↦₆₄ u96) ∗
         A.live u64 u56.toNat 1 ∗ (u64 ↦ₛ auth.rootKey) ∗
         memRegion (u64 + BitVec.ofNat 64 auth.rootKey.length) (u56.toNat - auth.rootKey.length) ∗
         A.pool lim st s ∗ Frame) by
      rw [stackAt_encoderFromPb_split_allocHook fsp]
      dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]
      sep_ac_rfl)) ?_
    apply SepWP.pure_elim
    rintro ⟨hr_le, hr_cap, hptr0, hcap0_ne⟩
    have hr_lt63 : auth.rootKey.length < 2 ^ 63 := Nat.lt_of_le_of_lt hr_le hr_cap
    have hr_lt64 : auth.rootKey.length < 2 ^ 64 := by omega
    have hr_toNat : (BitVec.ofNat 64 auth.rootKey.length).toNat = auth.rootKey.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr_lt64]
    have hr_ne0 : (BitVec.ofNat 64 auth.rootKey.length == 0#64) = false :=
      ofNat_beq_zero_false hr_pos hr_lt64
    have hpow1 : ∃ k : Nat, 1 = 2 ^ k := ⟨0, rfl⟩
    have hrlay : RustLayoutOk auth.rootKey.length 1 := ⟨⟨hr_pos, hpow1, hr_lt63⟩, by decide⟩
    have hshim := hA.shim_ok
    dsimp only [rustAllocShimVmSpec] at hshim
    have halloc := subroutine_ok_allocNoOom_of_budget hA.alloc_ok
    dsimp only [rustCliAllocNoOomSpec] at halloc
    have hmc := hA.memcpy_ok
    dsimp only [allocMemcpyVmSpec] at hmc
    clear hA
    change s.pc = (blkPl_333).base + 1292#64 at hpc
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 8756#64) s _ _
    wp_steps_sync_333 (lsρ spqrRustNoAllocShimSym)
    simp only [State.setMem_setMem]
    wp_call hshim ()
    have hacp_shim : AllocCallPreserved s sf := by
      simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
    refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
    wp_steps_sync_333 (lsρ spqrRustAllocSym)
    simp only [State.setMem_setMem]
    wp_call halloc (auth.rootKey.length, 1, st)
    have hoom0 : sf_1.readReg64 .x0 ≠ 0#64 := ‹_›
    have hoom0_beq : (sf_1.readReg64 .x0 == 0#64) = false := beq_false_of_ne hoom0
    have hacp_alloc : AllocCallPreserved s sf_1 :=
      hacp_shim.trans (by simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf_1›)
    wp_steps_sync_333 (lsρ "memcpy")
    simp only [State.setMem_setMem]
    wp_call hmc (sf_1.readReg64 .x0, u64, auth.rootKey)
    have hacp_mc : AllocCallPreserved s sf_2 :=
      hacp_alloc.trans (by simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf_2›)
    have hsp_sf : sf.sp = fsp := ‹sf.sp = s.sp›.trans hsp
    have hsp1_eq : sf_1.sp = sf.sp := by simpa only [wp_norm, arm64_norm] using ‹sf_1.sp = _›
    have hsp_sf1 : sf_1.sp = fsp := hsp1_eq.trans hsp_sf
    have hsp2_eq : sf_2.sp = sf_1.sp := by simpa only [wp_norm, arm64_norm] using ‹sf_2.sp = _›
    have hsp_sf2 : sf_2.sp = fsp := hsp2_eq.trans hsp_sf1
    have htr_sf2 : sf_2.trace = s0.trace := hacp_mc.2.1.trans htr.1
    have hvregs_sf2 : calleeSavedVRegs sf_2 = calleeSavedVRegs s0 :=
      ‹calleeSavedVRegs sf_2 = calleeSavedVRegs sf_1›.trans
        (‹calleeSavedVRegs sf_1 = calleeSavedVRegs sf›.trans
          (‹calleeSavedVRegs sf = calleeSavedVRegs s›.trans htr.2))
    refine SepWP.transport_budgetPool ‹VmPreserved _ sf_2› (hnext := ?_)
    refine SepWP.mono
      (post := fun s1 P1 =>
        (P1 ⊢
          stackAt fsp encoderFromPbStack ∗ ((fsp + 232#64) ↦₆₄ u96) ∗
          vecCapPtrDealloc A.repAlloc u56 u64 ∗
          vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.rootKey.length)
            (sf_1.readReg64 .x0) auth.rootKey ∗
          A.pool lim (M.stepEvents (rustAllocEvents auth.rootKey.length 1) st) s1 ∗ Frame) ∧
        s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧ s1.readReg64 .x21 = u8 ∧
        s1.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length ∧
        s1.readReg64 .x23 = u80 ∧ s1.readReg64 .x24 = u88 ∧
        s1.readReg64 .x25 = u56 ∧ s1.readReg64 .x26 = sf_1.readReg64 .x0 ∧
        s1.readReg64 .x27 = pbA ∧ s1.readReg64 .x28 = u64 ∧
        s1.readReg64 .x9 = u96 ∧ TraceCalleeSaved s1 s0) ?_
      fun s1 P1 _ _ ⟨hP1, hregs⟩ => ⟨sf_1.readReg64 .x0, hP1, hregs⟩
    wp_steps_sync_333 ((blkPl_333).base + 8756#64)
    simp only [State.setMem_setMem]
    have hd := vecU8Payload_pos_dealloc A.repAlloc u56 u64 auth.rootKey hr_le hr_cap hptr0 hcap0_ne
    have hp := vecU8Payload_pos A.repAlloc (sf_1.readReg64 .x0) auth.rootKey hr_pos hr_lt63 hoom0
    refine entails_pre_st ?_ ?_
    · intro sc hsc
      rw [← hsc, hsp_sf, stackAt_encoderFromPb_split_allocHook fsp]
      simp only [arm64_norm] at hd hp ⊢
      refine Entails.trans (Entails.of_eq (show _ =
        (A.repAlloc.live u64 u56.toNat 1 ∗ (u64 ↦ₛ auth.rootKey) ∗
         memRegion (u64 + BitVec.ofNat 64 auth.rootKey.length) (u56.toNat - auth.rootKey.length)) ∗
        (A.repAlloc.live (sf_1.readReg64 .x0) auth.rootKey.length 1 ∗
         (sf_1.readReg64 .x0 ↦ₛ auth.rootKey)) ∗
        memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack ∗ ((fsp + 232#64) ↦₆₄ u96) ∗
        A.pool lim (M.stepEvents (rustAllocEvents auth.rootKey.length 1) st) sc ∗ Frame by
          dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]
          sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono hd (sepConj_mono_left hp)) (Entails.of_eq (by sep_ac_rfl))
    · wp_done

/-- Direct `SepWP` segment (`+1292 -> +8756`) of `Authenticator::from_pb` in Variant 1 under
    `FromPbAllocHooksBudget` and `FitsEvents M lim st (authKeyCloneEvents auth.rootKey)`. -/
theorem v1_auth_from_pb_step1_1292_8756_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s : State) (fsp out pbA u8 u56 u64 u80 u88 u96 : BitVec 64)
    (auth : ProtoAuthenticator) (Frame : SepProp)
    (hfits : FitsEvents M lim st (authKeyCloneEvents auth.rootKey))
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 1292#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 auth.rootKey.length)
    (hx21 : s.readReg64 .x21 = u8) (hx23 : s.readReg64 .x23 = u80) (hx24 : s.readReg64 .x24 = u88)
    (hx25 : s.readReg64 .x25 = u56) (hx27 : s.readReg64 .x27 = pbA) (hx28 : s.readReg64 .x28 = u64)
    (hx9 : s.readReg64 .x9 = u96) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 8756#64) s
      (stackAt fsp encoderFromPbStack ∗ ((fsp + 232#64) ↦₆₄ u96) ∗
       vecU8Payload A.repAlloc u56 u64 auth.rootKey ∗ A.pool lim st s ∗ Frame)
      (fun s1 P1 =>
        ∃ pa1 : BitVec 64,
          (P1 ⊢
            stackAt fsp encoderFromPbStack ∗ ((fsp + 232#64) ↦₆₄ u96) ∗
            vecCapPtrDealloc A.repAlloc u56 u64 ∗
            vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
            A.pool lim (M.stepEvents (authKeyCloneEvents auth.rootKey) st) s1 ∗ Frame) ∧
          s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧ s1.readReg64 .x21 = u8 ∧
          s1.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length ∧
          s1.readReg64 .x23 = u80 ∧ s1.readReg64 .x24 = u88 ∧
          s1.readReg64 .x25 = u56 ∧ s1.readReg64 .x26 = pa1 ∧
          s1.readReg64 .x27 = pbA ∧ s1.readReg64 .x28 = u64 ∧
          s1.readReg64 .x9 = u96 ∧ TraceCalleeSaved s1 s0) :=
  v1_auth_from_pb_step1_1292_8756_placed_of_placedHooks hA.toPlacedBudget
    st s0 s fsp out pbA u8 u56 u64 u80 u88 u96 auth Frame hfits hfsp_align
    hpc hrun hsp hx19 hx20 hx21 hx23 hx24 hx25 hx27 hx28 hx9 htr

/-- CPS `SepWPp` segment (`+1292 -> +8756`) of `Authenticator::from_pb` in Variant 1 under
    `FromPbAllocHooksBudget` and `FitsEvents M lim st (authKeyCloneEvents auth.rootKey)`. -/
theorem v1_auth_from_pb_step1_1292_8756_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s : State) (target_pc fsp out pbA u8 u56 u64 u80 u88 u96 : BitVec 64)
    (auth : ProtoAuthenticator) (Frame : SepProp) (post onPanic : State → SepProp → Prop)
    (hfits : FitsEvents M lim st (authKeyCloneEvents auth.rootKey))
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 1292#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 auth.rootKey.length)
    (hx21 : s.readReg64 .x21 = u8) (hx23 : s.readReg64 .x23 = u80) (hx24 : s.readReg64 .x24 = u88)
    (hx25 : s.readReg64 .x25 = u56) (hx27 : s.readReg64 .x27 = pbA) (hx28 : s.readReg64 .x28 = u64)
    (hx9 : s.readReg64 .x9 = u96) (hu96 : u96 = BitVec.ofNat 64 auth.macKey.length)
    (htr : TraceCalleeSaved s s0)
    (hnext : ∀ (pa1 : BitVec 64) (s1 : State),
      s1.pc = lsmpl.base 333 + 8756#64 → s1.status = .Running →
      (s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧ s1.readReg64 .x21 = u8 ∧
       s1.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length ∧
       s1.readReg64 .x23 = u80 ∧ s1.readReg64 .x24 = u88 ∧
       s1.readReg64 .x25 = u56 ∧ s1.readReg64 .x26 = pa1 ∧
       s1.readReg64 .x27 = pbA ∧ s1.readReg64 .x28 = u64 ∧
       s1.readReg64 .x9 = u96 ∧ TraceCalleeSaved s1 s0) →
      SepWPp (lsProg_333 (Rust.withPanics ext)) target_pc s1
        (stackAt fsp encoderFromPbStack ∗ ((fsp + 232#64) ↦₆₄ u96) ∗
         vecCapPtrDealloc A.repAlloc u56 u64 ∗
         vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
         A.pool lim (M.stepEvents (authKeyCloneEvents auth.rootKey) st) s1 ∗ Frame)
        post onPanic) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) target_pc s
      (stackAt fsp encoderFromPbStack ∗ ((fsp + 232#64) ↦₆₄ u96) ∗
       vecU8Payload A.repAlloc u56 u64 auth.rootKey ∗ A.pool lim st s ∗ Frame)
      post onPanic := by
  have hwp := v1_auth_from_pb_step1_1292_8756_placed_sepWP hA st s0 s fsp out pbA
    u8 u56 u64 u80 u88 u96 auth Frame hfits hfsp_align
    hpc hrun hsp hx19 hx20 hx21 hx23 hx24 hx25 hx27 hx28 hx9 htr
  exact SepWPp.of_sepWP (SepWP.mono hwp fun s1 _P1 hpc1 hrun1 ⟨pa1, hP1, hregs⟩ =>
    SepWPp.weaken_pre hP1 (hnext pa1 s1 hpc1 hrun1 hregs))

theorem v1_auth_from_pb_step1_1292_8756_lscl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (target_pc fsp out pbA u8 u56 u64 u80 u88 u96 : BitVec 64)
    (auth : ProtoAuthenticator) (Frame : SepProp) (post onPanic : State → SepProp → Prop)
    (hfits : FitsEvents M lim st (authKeyCloneEvents auth.rootKey))
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 1292#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 auth.rootKey.length)
    (hx21 : s.readReg64 .x21 = u8) (hx23 : s.readReg64 .x23 = u80) (hx24 : s.readReg64 .x24 = u88)
    (hx25 : s.readReg64 .x25 = u56) (hx27 : s.readReg64 .x27 = pbA) (hx28 : s.readReg64 .x28 = u64)
    (hx9 : s.readReg64 .x9 = u96) (htr : TraceCalleeSaved s s0)
    (hnext : ∀ (pa1 : BitVec 64) (s1 : State),
      s1.pc = lsmpl.base 333 + 8756#64 → s1.status = .Running →
      LibsignalCodeLoaded lsmpl s1.mem →
      (s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧ s1.readReg64 .x21 = u8 ∧
       s1.readReg64 .x22 = BitVec.ofNat 64 auth.rootKey.length ∧
       s1.readReg64 .x23 = u80 ∧ s1.readReg64 .x24 = u88 ∧
       s1.readReg64 .x25 = u56 ∧ s1.readReg64 .x26 = pa1 ∧
       s1.readReg64 .x27 = pbA ∧ s1.readReg64 .x28 = u64 ∧
       s1.readReg64 .x9 = u96 ∧ TraceCalleeSaved s1 s0) →
      SepWPp (lsProg_333 (Rust.withPanics ext)) target_pc s1
        (stackAt fsp encoderFromPbStack ∗ ((fsp + 232#64) ↦₆₄ u96) ∗
         vecCapPtrDealloc A.repAlloc u56 u64 ∗
         vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
         A.pool lim (M.stepEvents (authKeyCloneEvents auth.rootKey) st) s1 ∗ Frame)
        post onPanic) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) target_pc s
      (stackAt fsp encoderFromPbStack ∗ ((fsp + 232#64) ↦₆₄ u96) ∗
       vecU8Payload A.repAlloc u56 u64 auth.rootKey ∗ A.pool lim st s ∗ Frame)
      post onPanic := by
  have hwp := v1_auth_from_pb_step1_1292_8756_placed_sepWP hA st s0 s fsp out pbA
    u8 u56 u64 u80 u88 u96 auth Frame hfits hfsp_align
    hpc hrun hsp hx19 hx20 hx21 hx23 hx24 hx25 hx27 hx28 hx9 htr
  refine SepWPp.seq_frozen
    (Φ := LibsignalCodeLoaded lsmpl)
    (fun _ _ h hf => LibsignalCodeLoaded.of_keepsFrozen h hf)
    hcl
    (SepWP.mono hwp fun s1 _P1 hpc1 hrun1 ⟨pa1, hP1, hregs⟩ hcl1 =>
      SepWPp.weaken_pre hP1 (hnext pa1 s1 hpc1 hrun1 hcl1 hregs))

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2bPlacedBudget

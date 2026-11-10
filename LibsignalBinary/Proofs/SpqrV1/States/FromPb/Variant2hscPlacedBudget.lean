/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hscPlacedBudgetAux
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch3Placed
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Budget-Threaded Variant 2 (`HeaderSent`) — Part C

Relocatable Block-`333` `FreeOnlyEvs` cleanup chain (`+9152 -> +9228`) under
`RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hscPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalPlacement blkLib_eq_333 blkPC_333 blkPl_333 lsProg_333 lsmpl lsρ)
open CryptoVerification.LibsignalSpqrV1 (ProtoPolynomialDecoder)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (RustAlloc allocHookStack arrayAt vecU8)
open CryptoVerification.SpqrV1.Drop (vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Poly (boolByte)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved v2hsc_Saved4436Preserved v2hsc_bv_add_add_lit
   v2hsc_optProtoPolyDecoderHeap v2hsc_optProtoPolyDecoderWordsAt
   v2hsc_ptsCap_add_one_ne_zero v2hsc_stackAt_allocHook_to_encoderFromPbStack
   v2hsc_stackAt_encoderFromPbStack_to_allocHook)
open CryptoVerification.SpqrV1.Unchunked
  (extractLsb'_0_64_append extractLsb'_64_64_append)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget
   rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
  (FromPbAllocHooksPlacedBudget spqrRustDeallocSym)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
  (align_pre_st deallocFreeOnlySpec sepWP_evs_dealloc sepWP_evs_nil seq_clean_evs seq_clean_st
   subroutine_ok_deallocFreeOnly)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux
  (FromPbAllocHooksBudget blk333_noSvc0 entails_pre_st)

export Variant2hscPlacedBudgetAux
  (v2hsc_sub_ok_dealloc_of_dealloc_placed v2hsc_sub_ok_dealloc_of_placedHooks
   v2hsc_sub_ok_dealloc_placed v2hsc_err_exit_9228_placed v2hsc_err_exit_9228_placed_budget)
export Variant2hscPlacedBudgetAux
  (v2hsc_err_exit_9224_placed v2hsc_err_exit_9224_placed_budget
   v2hsc_proto_decoder_dealloc_body_4460_of_sub_placed
   v2hsc_proto_decoder_dealloc_body_4460_placed
   v2hsc_proto_decoder_dealloc_loop_4460_of_sub_placed)
export Variant2hscPlacedBudgetAux
  (v2hsc_proto_decoder_dealloc_loop_4460_placed
   v2hsc_dealloc_proto_decoder_4436_of_sub_placed v2hsc_dealloc_proto_decoder_4436_placed
   v2hsc_dealloc_proto_decoder_4484_of_sub_placed v2hsc_dealloc_proto_decoder_4484_placed)
export Variant2hscPlacedBudgetAux
  (v2hsc_dealloc_some_proto_decoder_4428_of_sub_placed
   v2hsc_dealloc_some_proto_decoder_4428_of_dealloc_placed
   v2hsc_dealloc_some_proto_decoder_4428_of_placedHooks
   v2hsc_dealloc_some_proto_decoder_4428_placed)

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

/-! ## Cleanup Chain (`+9152 -> +9176 -> +9184 -> +9192 -> +9212 -> +9228`) -/

theorem v2hsc_optProtoDecoder_some_pre_pool (A : RustAlloc) (fsp : BitVec 64)
    (pb : ProtoPolynomialDecoder)
    (d0 d8 d16 : BitVec 64) (d24 d28 : BitVec 32) (d32 w232 : BitVec 64)
    (Pool Frame : SepProp) :
    v2hsc_optProtoPolyDecoderWordsAt (fsp + 1032#64) d0 d8 d16 d24 d28 d32 ∗
      v2hsc_optProtoPolyDecoderHeap A (some pb) d0 d8 d16 d24 d28 d32 ∗
      ((fsp + 232#64) ↦₆₄ w232) ∗
      Pool ∗ stackAt fsp allocHookStack ∗ Frame ⊢
    ⌜d16 = BitVec.ofNat 64 pb.pts.length ∧
      pb.pts.length ≤ d0.toNat ∧ d0.toNat * 24 < 2 ^ 63⌝ ∗
    (((fsp + 232#64) ↦₆₄ w232) ∗
     ((fsp + 1040#64) ↦₆₄ d8) ∗
     ((fsp + 1048#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
     (if d0 = 0#64 then emp
      else A.live d8 (d0.toNat * 24) 8 ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 d8 pb.pts ∗
        memRegion (d8 + BitVec.ofNat 64 (pb.pts.length * 24)) ((d0.toNat - pb.pts.length) * 24)) ∗
     Pool ∗ stackAt fsp allocHookStack ∗
     (((fsp + 1032#64) ↦₆₄ d0) ∗
      ((fsp + 1056#64) ↦₃₂ d24) ∗
      ((fsp + 1060#64) ↦₃₂ d28) ∗
      ((fsp + 1064#64) ↦₆₄ d32) ∗ Frame)) := by
  dsimp only [v2hsc_optProtoPolyDecoderWordsAt, v2hsc_optProtoPolyDecoderHeap]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜d16 = BitVec.ofNat 64 pb.pts.length ∧
      d24 = pb.ptsNeeded ∧ d28 = pb.polys ∧
      pb.pts.length ≤ d0.toNat ∧ d0.toNat * 24 < 2 ^ 63 ∧
      d8 ≠ 0#64 ∧
      (∃ bs : List (BitVec 8), bs.length = 7 ∧ boolByte pb.isComplete :: bs = unpack64 d32)⌝ ∗
    (((fsp + 232#64) ↦₆₄ w232) ∗
     ((fsp + 1040#64) ↦₆₄ d8) ∗
     ((fsp + 1048#64) ↦₆₄ d16) ∗
     (if d0 = 0#64 then emp
      else A.live d8 (d0.toNat * 24) 8 ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 d8 pb.pts ∗
        memRegion (d8 + BitVec.ofNat 64 (pb.pts.length * 24)) ((d0.toNat - pb.pts.length) * 24)) ∗
     Pool ∗ stackAt fsp allocHookStack ∗
     (((fsp + 1032#64) ↦₆₄ d0) ∗
      ((fsp + 1056#64) ↦₃₂ d24) ∗
      ((fsp + 1060#64) ↦₃₂ d28) ∗
      ((fsp + 1064#64) ↦₆₄ d32) ∗ Frame)) by sep_ac_rfl)) ?_
  apply Entails.pure_left
  rintro ⟨hd16, _, _, hle, hcap, _, _⟩
  subst hd16
  exact Entails.pure_right ⟨rfl, hle, hcap⟩ (Entails.refl _)

/-- Cleanup at `+9212 -> +9228`: sets `w23 = 0` (`spqrErrorByte .stateDecode = 0#8`),
    deallocates `optDec` at `fsp + 1032..1072` if `some`, and reaches `+9228`. -/
theorem v2hsc_cleanup_9212_to_9228_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (s0 s1 : State) (fsp out : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder)
    (d0 d8 d16 : BitVec 64) (d24 d28 : BitVec 32) (d32 w232 : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9212#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9228#64) s1
      (stackAt fsp encoderFromPbStack ∗
        v2hsc_optProtoPolyDecoderWordsAt (fsp + 1032#64) d0 d8 d16 d24 d28 d32 ∗
        v2hsc_optProtoPolyDecoderHeap A.repAlloc optDec d0 d8 d16 d24 d28 d32 ∗
        ((fsp + 232#64) ↦₆₄ w232) ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          v2hsc_optProtoPolyDecoderWordsAt (fsp + 1032#64) d0 d8 d16 d24 d28 d32 ∗
          ((fsp + 232#64) ↦₆₄ w232) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x23 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  cases optDec with
  | none =>
    rcases htr1 with ⟨htr_1, hvregs_1⟩
    dsimp only [v2hsc_optProtoPolyDecoderHeap]
    refine SepWP.weaken_pre (Entails.of_eq (show _ =
      ⌜d0 = noneCap⌝ ∗
      (stackAt fsp encoderFromPbStack ∗
       v2hsc_optProtoPolyDecoderWordsAt (fsp + 1032#64) d0 d8 d16 d24 d28 d32 ∗
       ((fsp + 232#64) ↦₆₄ w232) ∗ A.pool lim st s1 ∗ Frame) by sep_ac_rfl)) ?_
    apply ProofLib.SepWP.pure_elim; intro hd0
    subst hd0
    dsimp only [noneCap] at hpc1 hx22_1 ⊢
    change s1.pc = (blkPl_333).base + 9212#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 9228#64) s1 _ _
    apply sepWP_evs_nil
    simp only [M.stepEvents_nil]
    wp_steps_sync_333 ((blkPl_333).base + 9228#64)
    simp only [State.setMem_setMem]
    refine align_pre_st (by sep_ac_rfl) ?_
    wp_done
  | some pb =>
    refine SepWP.weaken_pre
      (sepConj_mono_left (v2hsc_stackAt_encoderFromPbStack_to_allocHook fsp)) ?_
    refine SepWP.weaken_pre
      (Entails.trans (Entails.of_eq (by sep_ac_rfl))
        (v2hsc_optProtoDecoder_some_pre_pool A.repAlloc fsp pb d0 d8 d16 d24 d28 d32 w232
          (A.pool lim st s1) (memRegion (fsp - 5152#64) 1056 ∗ Frame))) ?_
    apply ProofLib.SepWP.pure_elim; rintro ⟨rfl, hpts_le, hpts_cap_lt⟩
    dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
    have hd0_ne := v2hsc_ptsCap_add_one_ne_zero hpts_cap_lt
    refine seq_clean_st
      (mid := lsmpl.base 333 + 4428#64)
      (P_mid := fun sm =>
        ((fsp + 232#64) ↦₆₄ w232) ∗
        ((fsp + 1040#64) ↦₆₄ d8) ∗
        ((fsp + 1048#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
        (if d0 = 0#64 then emp
         else A.live d8 (d0.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 d8 pb.pts ∗
           memRegion (d8 + BitVec.ofNat 64 (pb.pts.length * 24)) ((d0.toNat - pb.pts.length) * 24)) ∗
        A.pool lim st sm ∗ stackAt fsp allocHookStack ∗
        (((fsp + 1032#64) ↦₆₄ d0) ∗
         ((fsp + 1056#64) ↦₃₂ d24) ∗
         ((fsp + 1060#64) ↦₃₂ d28) ∗
         ((fsp + 1064#64) ↦₆₄ d32) ∗
         (memRegion (fsp - 5152#64) 1056 ∗ Frame)))
      (Q := fun sm =>
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        sm.readReg64 .x23 = 0#64 ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · rcases htr1 with ⟨htr_1, hvregs_1⟩
      change s1.pc = (blkPl_333).base + 9212#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 4428#64) s1 _ _
      wp_steps_sync_333 ((blkPl_333).base + 4428#64)
      refine align_pre_st (by sep_ac_rfl) ?_
      wp_done
    · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, hx23_2, htr2⟩
      have h4428 := v2hsc_dealloc_some_proto_decoder_4428_of_sub_placed hdealloc_ok s0 s2 fsp
        out d8 d0 0#64 w232 pb.pts st
        (((fsp + 1032#64) ↦₆₄ d0) ∗
         ((fsp + 1056#64) ↦₃₂ d24) ∗
         ((fsp + 1060#64) ↦₃₂ d28) ∗
         ((fsp + 1064#64) ↦₆₄ d32) ∗
         (memRegion (fsp - 5152#64) 1056 ∗ Frame))
        hfsp_align hpts_le hpts_cap_lt hpc2 hrun2 hsp2 hx19_2 hx22_2 hx23_2 htr2
      refine SepWP.mono h4428 fun sm _Pm _ _ ⟨evs, hevs, hPm, hsp_m, hx19_m, hx23_m, htr_m⟩ => ?_
      refine ⟨evs, hevs, Entails.trans hPm ?_, hsp_m, hx19_m, hx23_m, htr_m⟩
      have hst := v2hsc_stackAt_allocHook_to_encoderFromPbStack fsp
      dsimp only [v2hsc_optProtoPolyDecoderWordsAt]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      refine Entails.trans
        (Entails.of_eq (show _ =
          (stackAt fsp allocHookStack ∗ memRegion (fsp - 5152#64) 1056) ∗
          (((fsp + 1032#64) ↦₆₄ d0) ∗
           ((fsp + 1040#64) ↦₆₄ d8) ∗
           ((fsp + 1048#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
           ((fsp + 1056#64) ↦₃₂ d24) ∗
           ((fsp + 1060#64) ↦₃₂ d28) ∗
           ((fsp + 1064#64) ↦₆₄ d32) ∗
           ((fsp + 232#64) ↦₆₄ w232) ∗
           A.pool lim (M.stepEvents evs st) sm ∗ Frame) by sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left hst) (Entails.of_eq (by sep_ac_rfl))

theorem v2hsc_cleanup_9212_to_9228_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (s0 s1 : State) (fsp out : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder)
    (d0 d8 d16 : BitVec 64) (d24 d28 : BitVec 32) (d32 w232 : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9212#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9228#64) s1
      (stackAt fsp encoderFromPbStack ∗
        v2hsc_optProtoPolyDecoderWordsAt (fsp + 1032#64) d0 d8 d16 d24 d28 d32 ∗
        v2hsc_optProtoPolyDecoderHeap A.repAlloc optDec d0 d8 d16 d24 d28 d32 ∗
        ((fsp + 232#64) ↦₆₄ w232) ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          v2hsc_optProtoPolyDecoderWordsAt (fsp + 1032#64) d0 d8 d16 d24 d28 d32 ∗
          ((fsp + 232#64) ↦₆₄ w232) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x23 = 0#64 ∧
        TraceCalleeSaved sm s0) :=
  v2hsc_cleanup_9212_to_9228_of_sub_placed
    (v2hsc_sub_ok_dealloc_of_dealloc_placed hdealloc) s0 s1 fsp out optDec
    d0 d8 d16 d24 d28 d32 w232 st Frame hfsp_align hpc1 hrun1 hsp1 hx19_1 hx22_1 htr1

theorem v2hsc_cleanup_9212_to_9228_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 s1 : State) (fsp out : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder)
    (d0 d8 d16 : BitVec 64) (d24 d28 : BitVec 32) (d32 w232 : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9212#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9228#64) s1
      (stackAt fsp encoderFromPbStack ∗
        v2hsc_optProtoPolyDecoderWordsAt (fsp + 1032#64) d0 d8 d16 d24 d28 d32 ∗
        v2hsc_optProtoPolyDecoderHeap A.repAlloc optDec d0 d8 d16 d24 d28 d32 ∗
        ((fsp + 232#64) ↦₆₄ w232) ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          v2hsc_optProtoPolyDecoderWordsAt (fsp + 1032#64) d0 d8 d16 d24 d28 d32 ∗
          ((fsp + 232#64) ↦₆₄ w232) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x23 = 0#64 ∧
        TraceCalleeSaved sm s0) :=
  v2hsc_cleanup_9212_to_9228_of_sub_placed
    (v2hsc_sub_ok_dealloc_of_placedHooks hA) s0 s1 fsp out optDec
    d0 d8 d16 d24 d28 d32 w232 st Frame hfsp_align hpc1 hrun1 hsp1 hx19_1 hx22_1 htr1

theorem v2hsc_cleanup_9212_to_9228_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 s1 : State) (fsp out : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder)
    (d0 d8 d16 : BitVec 64) (d24 d28 : BitVec 32) (d32 w232 : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9212#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9228#64) s1
      (stackAt fsp encoderFromPbStack ∗
        v2hsc_optProtoPolyDecoderWordsAt (fsp + 1032#64) d0 d8 d16 d24 d28 d32 ∗
        v2hsc_optProtoPolyDecoderHeap A.repAlloc optDec d0 d8 d16 d24 d28 d32 ∗
        ((fsp + 232#64) ↦₆₄ w232) ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          v2hsc_optProtoPolyDecoderWordsAt (fsp + 1032#64) d0 d8 d16 d24 d28 d32 ∗
          ((fsp + 232#64) ↦₆₄ w232) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x23 = 0#64 ∧
        TraceCalleeSaved sm s0) :=
  v2hsc_cleanup_9212_to_9228_of_sub_placed
    (v2hsc_sub_ok_dealloc_placed hA) s0 s1 fsp out optDec
    d0 d8 d16 d24 d28 d32 w232 st Frame hfsp_align hpc1 hrun1 hsp1 hx19_1 hx22_1 htr1

/-- Deallocate `(ca3, pa3)` at `+9192 -> +9212`
    (`cbz x26, +9212; ldr x0, [sp, #176]; mov x1, x26; mov w2, #1; bl __rust_dealloc`). -/
theorem v2hsc_cleanup_9192_to_9212_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (s0 s1 : State) (fsp out d0 ca3 pa3 : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9192#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9212#64) s1
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        TraceCalleeSaved sm s0) := by
  rcases htr1 with ⟨htr_1, hvregs_1⟩
  have hdealloc_fo : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (deallocFreeOnlySpec M A lim) :=
    subroutine_ok_deallocFreeOnly hdealloc_ok
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  refine SepWP.weaken_pre
    (sepConj_mono_left (v2hsc_stackAt_encoderFromPbStack_to_allocHook fsp)) ?_
  have hst := v2hsc_stackAt_allocHook_to_encoderFromPbStack fsp
  dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live,
    BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc1 ⊢
  change s1.pc = (blkPl_333).base + 9192#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 9212#64) s1 _ _
  by_cases hca3 : (ca3 == 0#64) = true <;>
    simp only [hca3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · apply sepWP_evs_nil
    simp only [M.stepEvents_nil]
    wp_steps_sync_333 ((blkPl_333).base + 9212#64)
    simp only [State.setMem_setMem]
    refine entails_pre_st ?_ ?_
    · intro sc hsc
      rw [← hsc]
      refine Entails.trans (Entails.of_eq (show _ =
        (stackAt fsp allocHookStack ∗ memRegion (fsp - 5152#64) 1056) ∗
        (((fsp + 176#64) ↦₆₄ pa3) ∗ A.pool lim st sc ∗ Frame) by sep_ac_rfl)) ?_
      exact sepConj_mono_left hst
    · wp_done
  · apply sepWP_evs_dealloc ca3.toNat 1
    wp_steps_sync_333 (lsρ spqrRustDeallocSym)
    simp only [State.setMem_setMem]
    wp_call hdealloc_fo (pa3, ca3.toNat, 1, st)
    have hacp : AllocCallPreserved s1 sf := by
      simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
    have hsp_sf : sf.sp = fsp := ‹sf.sp = _›.trans (by simp [wp_norm, arm64_norm, hsp1])
    have htr_sf : sf.trace = s0.trace := hacp.2.1.trans htr_1
    have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
      ‹calleeSavedVRegs sf = _›.trans hvregs_1
    refine entails_pre_st ?_ ?_
    · intro sc hsc
      rw [← hsc]
      simp only [wp_norm, arm64_norm, hsp1]
      refine Entails.trans (Entails.of_eq (show _ =
        (stackAt fsp allocHookStack ∗ memRegion (fsp - 5152#64) 1056) ∗
        (((fsp + 176#64) ↦₆₄ pa3) ∗
         A.pool lim (M.stepEvents (rustDeallocEvents ca3.toNat 1) st) sc ∗ Frame) by sep_ac_rfl)) ?_
      exact sepConj_mono_left hst
    · wp_done

theorem v2hsc_cleanup_9192_to_9212_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (s0 s1 : State) (fsp out d0 ca3 pa3 : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9192#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9212#64) s1
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        TraceCalleeSaved sm s0) :=
  v2hsc_cleanup_9192_to_9212_of_sub_placed
    (v2hsc_sub_ok_dealloc_of_dealloc_placed hdealloc) s0 s1 fsp out d0 ca3 pa3 st Frame
    hfsp_align hpc1 hrun1 hsp1 hx19_1 hx22_1 hx26_1 htr1

theorem v2hsc_cleanup_9192_to_9212_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 s1 : State) (fsp out d0 ca3 pa3 : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9192#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9212#64) s1
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        TraceCalleeSaved sm s0) :=
  v2hsc_cleanup_9192_to_9212_of_sub_placed
    (v2hsc_sub_ok_dealloc_of_placedHooks hA) s0 s1 fsp out d0 ca3 pa3 st Frame
    hfsp_align hpc1 hrun1 hsp1 hx19_1 hx22_1 hx26_1 htr1

theorem v2hsc_cleanup_9192_to_9212_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 s1 : State) (fsp out d0 ca3 pa3 : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9192#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9212#64) s1
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        TraceCalleeSaved sm s0) :=
  v2hsc_cleanup_9192_to_9212_of_sub_placed
    (v2hsc_sub_ok_dealloc_placed hA) s0 s1 fsp out d0 ca3 pa3 st Frame
    hfsp_align hpc1 hrun1 hsp1 hx19_1 hx22_1 hx26_1 htr1

/-- Deallocate non-empty `(ca2, pa2)` at `+9184 -> +9192` (`mov w2, #1; bl __rust_dealloc`). -/
theorem v2hsc_cleanup_9184_to_9192_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (s0 s1 : State) (fsp out d0 ca2 pa2 ca3 : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hca2 : (ca2 == 0#64) = false)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9184#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx0_1 : s1.readReg64 .x0 = pa2)
    (hx1_1 : s1.readReg64 .x1 = ca2)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9192#64) s1
      (stackAt fsp encoderFromPbStack ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        sm.readReg64 .x26 = ca3 ∧
        TraceCalleeSaved sm s0) := by
  rcases htr1 with ⟨htr_1, hvregs_1⟩
  have hdealloc_fo : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (deallocFreeOnlySpec M A lim) :=
    subroutine_ok_deallocFreeOnly hdealloc_ok
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  refine SepWP.weaken_pre
    (sepConj_mono_left (v2hsc_stackAt_encoderFromPbStack_to_allocHook fsp)) ?_
  have hst := v2hsc_stackAt_allocHook_to_encoderFromPbStack fsp
  dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live,
    BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc1 ⊢
  change s1.pc = (blkPl_333).base + 9184#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 9192#64) s1 _ _
  simp only [hca2, Bool.false_eq_true, ↓reduceIte]
  apply sepWP_evs_dealloc ca2.toNat 1
  wp_steps_sync_333 (lsρ spqrRustDeallocSym)
  simp only [State.setMem_setMem]
  wp_call hdealloc_fo (pa2, ca2.toNat, 1, st)
  have hacp : AllocCallPreserved s1 sf := by
    simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
  have hsp_sf : sf.sp = fsp := ‹sf.sp = _›.trans (by simp [wp_norm, arm64_norm, hsp1])
  have htr_sf : sf.trace = s0.trace := hacp.2.1.trans htr_1
  have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
    ‹calleeSavedVRegs sf = _›.trans hvregs_1
  refine entails_pre_st ?_ ?_
  · intro sc hsc
    rw [← hsc]
    simp only [wp_norm, arm64_norm, hsp1]
    refine Entails.trans
      (Entails.of_eq (show _ =
        (stackAt fsp allocHookStack ∗ memRegion (fsp - 5152#64) 1056) ∗
        (A.pool lim (M.stepEvents (rustDeallocEvents ca2.toNat 1) st) sc ∗ Frame) by sep_ac_rfl)) ?_
    exact sepConj_mono_left hst
  · wp_done

theorem v2hsc_cleanup_9184_to_9192_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (s0 s1 : State) (fsp out d0 ca2 pa2 ca3 : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hca2 : (ca2 == 0#64) = false)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9184#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx0_1 : s1.readReg64 .x0 = pa2)
    (hx1_1 : s1.readReg64 .x1 = ca2)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9192#64) s1
      (stackAt fsp encoderFromPbStack ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        sm.readReg64 .x26 = ca3 ∧
        TraceCalleeSaved sm s0) :=
  v2hsc_cleanup_9184_to_9192_of_sub_placed
    (v2hsc_sub_ok_dealloc_of_dealloc_placed hdealloc) s0 s1 fsp out d0 ca2 pa2 ca3 st Frame
    hca2 hfsp_align hpc1 hrun1 hsp1 hx0_1 hx1_1 hx19_1 hx22_1 hx26_1 htr1

theorem v2hsc_cleanup_9184_to_9192_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 s1 : State) (fsp out d0 ca2 pa2 ca3 : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hca2 : (ca2 == 0#64) = false)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9184#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx0_1 : s1.readReg64 .x0 = pa2)
    (hx1_1 : s1.readReg64 .x1 = ca2)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9192#64) s1
      (stackAt fsp encoderFromPbStack ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        sm.readReg64 .x26 = ca3 ∧
        TraceCalleeSaved sm s0) :=
  v2hsc_cleanup_9184_to_9192_of_sub_placed
    (v2hsc_sub_ok_dealloc_of_placedHooks hA) s0 s1 fsp out d0 ca2 pa2 ca3 st Frame
    hca2 hfsp_align hpc1 hrun1 hsp1 hx0_1 hx1_1 hx19_1 hx22_1 hx26_1 htr1

theorem v2hsc_cleanup_9184_to_9192_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 s1 : State) (fsp out d0 ca2 pa2 ca3 : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hca2 : (ca2 == 0#64) = false)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9184#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx0_1 : s1.readReg64 .x0 = pa2)
    (hx1_1 : s1.readReg64 .x1 = ca2)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9192#64) s1
      (stackAt fsp encoderFromPbStack ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        sm.readReg64 .x26 = ca3 ∧
        TraceCalleeSaved sm s0) :=
  v2hsc_cleanup_9184_to_9192_of_sub_placed
    (v2hsc_sub_ok_dealloc_placed hA) s0 s1 fsp out d0 ca2 pa2 ca3 st Frame
    hca2 hfsp_align hpc1 hrun1 hsp1 hx0_1 hx1_1 hx19_1 hx22_1 hx26_1 htr1

/-- Deallocate `(ca2, pa2)` and `(ca3, pa3)` at `+9176 -> +9212`. -/
theorem v2hsc_cleanup_9176_to_9212_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (s0 s1 : State) (fsp out d0 ca2 pa2 ca3 pa3 : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9176#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx0_1 : s1.readReg64 .x0 = pa2)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9212#64) s1
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        TraceCalleeSaved sm s0) := by
  refine seq_clean_evs
    (mid := lsmpl.base 333 + 9192#64)
    (P_evs := fun evs1 sm =>
      stackAt fsp encoderFromPbStack ∗
      ((fsp + 176#64) ↦₆₄ pa3) ∗
      vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
      A.pool lim (M.stepEvents evs1 st) sm ∗
      (((fsp + 232#64) ↦₆₄ ca2) ∗ Frame))
    (Q := fun sm =>
      sm.sp = fsp ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = d0 ∧
      sm.readReg64 .x26 = ca3 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · rcases htr1 with ⟨htr_1, hvregs_1⟩
    by_cases hca2 : (ca2 == 0#64) = true
    · dsimp only [vecCapPtrDealloc] at ⊢
      change s1.pc = (blkPl_333).base + 9176#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 9192#64) s1 _ _
      simp only [hca2, ↓reduceIte, emp_sepConj]
      apply sepWP_evs_nil
      simp only [M.stepEvents_nil]
      wp_steps_sync_333 ((blkPl_333).base + 9192#64)
      simp only [State.setMem_setMem]
      refine align_pre_st (by sep_ac_rfl) ?_
      wp_done
    · have hca2_f : (ca2 == 0#64) = false := Bool.eq_false_iff.mpr hca2
      refine seq_clean_st
        (mid := lsmpl.base 333 + 9184#64)
        (P_mid := fun sm =>
          stackAt fsp encoderFromPbStack ∗
          vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
          A.pool lim st sm ∗
          (((fsp + 176#64) ↦₆₄ pa3) ∗
           vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
           (((fsp + 232#64) ↦₆₄ ca2) ∗ Frame)))
        (Q := fun sm =>
          sm.sp = fsp ∧
          sm.readReg64 .x0 = pa2 ∧
          sm.readReg64 .x1 = ca2 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x22 = d0 ∧
          sm.readReg64 .x26 = ca3 ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · change s1.pc = (blkPl_333).base + 9176#64 at hpc1
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 9184#64) s1 _ _
        wp_steps_sync_333 ((blkPl_333).base + 9184#64)
        simp only [State.setMem_setMem]
        refine align_pre_st (by sep_ac_rfl) ?_
        wp_done
      · intro s2 hpc2 hrun2 ⟨hsp2, hx0_2, hx1_2, hx19_2, hx22_2, hx26_2, htr2⟩
        have h9184 := v2hsc_cleanup_9184_to_9192_of_sub_placed hdealloc_ok s0 s2 fsp out d0
          ca2 pa2 ca3 st
          (((fsp + 176#64) ↦₆₄ pa3) ∗
           vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
           (((fsp + 232#64) ↦₆₄ ca2) ∗ Frame))
          hca2_f hfsp_align hpc2 hrun2 hsp2 hx0_2 hx1_2 hx19_2 hx22_2 hx26_2 htr2
        exact SepWP.mono h9184 fun sm _Pm _ _ ⟨evs, hevs, hPm, hq⟩ =>
          ⟨evs, hevs, Entails.trans hPm (Entails.of_eq (by sep_ac_rfl)), hq⟩
  · intro evs1 s2 hevs1 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, hx26_2, htr2⟩
    have h9192 := v2hsc_cleanup_9192_to_9212_of_sub_placed hdealloc_ok s0 s2 fsp out d0
      ca3 pa3 (M.stepEvents evs1 st)
      (((fsp + 232#64) ↦₆₄ ca2) ∗ Frame)
      hfsp_align hpc2 hrun2 hsp2 hx19_2 hx22_2 hx26_2 htr2
    refine SepWP.mono h9192 fun sm _Pm _ _ ⟨evs2, hevs2, hPm, hq⟩ => ?_
    refine ⟨evs1 ++ evs2, hevs1.append hevs2, ?_, hq⟩
    rw [M.stepEvents_append]
    exact Entails.trans hPm (Entails.of_eq (by sep_ac_rfl))

theorem v2hsc_cleanup_9176_to_9212_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (s0 s1 : State) (fsp out d0 ca2 pa2 ca3 pa3 : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9176#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx0_1 : s1.readReg64 .x0 = pa2)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9212#64) s1
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        TraceCalleeSaved sm s0) :=
  v2hsc_cleanup_9176_to_9212_of_sub_placed
    (v2hsc_sub_ok_dealloc_of_dealloc_placed hdealloc) s0 s1 fsp out d0 ca2 pa2 ca3 pa3 st Frame
    hfsp_align hpc1 hrun1 hsp1 hx0_1 hx19_1 hx22_1 hx26_1 htr1

theorem v2hsc_cleanup_9176_to_9212_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 s1 : State) (fsp out d0 ca2 pa2 ca3 pa3 : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9176#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx0_1 : s1.readReg64 .x0 = pa2)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9212#64) s1
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        TraceCalleeSaved sm s0) :=
  v2hsc_cleanup_9176_to_9212_of_sub_placed
    (v2hsc_sub_ok_dealloc_of_placedHooks hA) s0 s1 fsp out d0 ca2 pa2 ca3 pa3 st Frame
    hfsp_align hpc1 hrun1 hsp1 hx0_1 hx19_1 hx22_1 hx26_1 htr1

theorem v2hsc_cleanup_9176_to_9212_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 s1 : State) (fsp out d0 ca2 pa2 ca3 pa3 : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9176#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx0_1 : s1.readReg64 .x0 = pa2)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9212#64) s1
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        TraceCalleeSaved sm s0) :=
  v2hsc_cleanup_9176_to_9212_of_sub_placed
    (v2hsc_sub_ok_dealloc_placed hA) s0 s1 fsp out d0 ca2 pa2 ca3 pa3 st Frame
    hfsp_align hpc1 hrun1 hsp1 hx0_1 hx19_1 hx22_1 hx26_1 htr1

/-- Cleanup at `+9152 -> +9212` (`sendingEk = none`): deallocates `(ca1, pa1)` (`x25 = ca1`,
    `[sp + 1272] = pa1`), `(ca2, pa2)` (`[sp + 232] = ca2`, `x0 / [sp + 184] = pa2`),
    and `(ca3, pa3)` (`x26 = ca3`, `[sp + 176] = pa3`). -/
theorem v2hsc_cleanup_9152_to_9212_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (s0 s1 : State) (fsp out d0 ca1 pa1 ca2 pa2 ca3 pa3 : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9152#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx0_1 : s1.readReg64 .x0 = pa2)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx25_1 : s1.readReg64 .x25 = ca1)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9212#64) s1
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 1272#64) ↦₆₄ pa1) ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        vecCapPtrDealloc A.repAlloc ca1 pa1 ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          ((fsp + 1272#64) ↦₆₄ pa1) ∗
          ((fsp + 184#64) ↦₆₄ pa2) ∗
          ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        TraceCalleeSaved sm s0) := by
  have hdealloc_fo : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (deallocFreeOnlySpec M A lim) :=
    subroutine_ok_deallocFreeOnly hdealloc_ok
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  refine seq_clean_evs
    (mid := lsmpl.base 333 + 9176#64)
    (P_evs := fun evs1 sm =>
      stackAt fsp encoderFromPbStack ∗
      ((fsp + 232#64) ↦₆₄ ca2) ∗
      ((fsp + 176#64) ↦₆₄ pa3) ∗
      vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
      vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
      A.pool lim (M.stepEvents evs1 st) sm ∗
      (((fsp + 1272#64) ↦₆₄ pa1) ∗
       ((fsp + 184#64) ↦₆₄ pa2) ∗ Frame))
    (Q := fun sm =>
      sm.sp = fsp ∧
      sm.readReg64 .x0 = pa2 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = d0 ∧
      sm.readReg64 .x26 = ca3 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · rcases htr1 with ⟨htr_1, hvregs_1⟩
    refine SepWP.weaken_pre
      (sepConj_mono_left (v2hsc_stackAt_encoderFromPbStack_to_allocHook fsp)) ?_
    have hst := v2hsc_stackAt_allocHook_to_encoderFromPbStack fsp
    rw [show vecCapPtrDealloc A.repAlloc ca1 pa1 =
      (if (ca1 == 0#64) = true then emp else A.live pa1 ca1.toNat 1 ∗ memRegion pa1 ca1.toNat) from rfl]
    change s1.pc = (blkPl_333).base + 9152#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 9176#64) s1 _ _
    by_cases hca1 : (ca1 == 0#64) = true <;>
      simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · apply sepWP_evs_nil
      simp only [M.stepEvents_nil]
      wp_steps_sync_333 ((blkPl_333).base + 9176#64)
      simp only [State.setMem_setMem]
      refine entails_pre_st ?_ ?_
      · intro sc hsc
        rw [← hsc]
        refine Entails.trans
          (Entails.of_eq (show _ =
            (stackAt fsp allocHookStack ∗ memRegion (fsp - 5152#64) 1056) ∗
            (((fsp + 232#64) ↦₆₄ ca2) ∗
             ((fsp + 176#64) ↦₆₄ pa3) ∗
             vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
             vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
             A.pool lim st sc ∗
             (((fsp + 1272#64) ↦₆₄ pa1) ∗
              ((fsp + 184#64) ↦₆₄ pa2) ∗ Frame)) by sep_ac_rfl)) ?_
        exact sepConj_mono_left hst
      · wp_done
    · apply sepWP_evs_dealloc ca1.toNat 1
      wp_steps_sync_333 (lsρ spqrRustDeallocSym)
      simp only [State.setMem_setMem]
      wp_call hdealloc_fo (pa1, ca1.toNat, 1, st)
      have hacp : AllocCallPreserved s1 sf := by
        simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
      have hsp_sf : sf.sp = fsp := ‹sf.sp = _›.trans (by simp [wp_norm, arm64_norm, hsp1])
      have htr_sf : sf.trace = s0.trace := hacp.2.1.trans htr_1
      have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
        ‹calleeSavedVRegs sf = _›.trans hvregs_1
      wp_steps_sync_333 ((blkPl_333).base + 9176#64)
      simp only [State.setMem_setMem]
      refine entails_pre_st ?_ ?_
      · intro sc hsc
        rw [← hsc]
        simp only [wp_norm, arm64_norm, hsp1]
        refine Entails.trans
          (Entails.of_eq (show _ =
            (stackAt fsp allocHookStack ∗ memRegion (fsp - 5152#64) 1056) ∗
            (((fsp + 232#64) ↦₆₄ ca2) ∗
             ((fsp + 176#64) ↦₆₄ pa3) ∗
             vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
             vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
             A.pool lim (M.stepEvents (rustDeallocEvents ca1.toNat 1) st) sc ∗
             (((fsp + 1272#64) ↦₆₄ pa1) ∗
              ((fsp + 184#64) ↦₆₄ pa2) ∗ Frame)) by sep_ac_rfl)) ?_
        exact sepConj_mono_left hst
      · wp_done
  · intro evs1 s2 hevs1 hpc2 hrun2 ⟨hsp2, hx0_2, hx19_2, hx22_2, hx26_2, htr2⟩
    have h9176 := v2hsc_cleanup_9176_to_9212_of_sub_placed hdealloc_ok s0 s2 fsp out d0
      ca2 pa2 ca3 pa3 (M.stepEvents evs1 st)
      (((fsp + 1272#64) ↦₆₄ pa1) ∗
       ((fsp + 184#64) ↦₆₄ pa2) ∗ Frame)
      hfsp_align hpc2 hrun2 hsp2 hx0_2 hx19_2 hx22_2 hx26_2 htr2
    refine SepWP.mono h9176 fun sm _Pm _ _ ⟨evs2, hevs2, hPm, hq⟩ => ?_
    refine ⟨evs1 ++ evs2, hevs1.append hevs2, ?_, hq⟩
    rw [M.stepEvents_append]
    exact Entails.trans hPm (Entails.of_eq (by sep_ac_rfl))

theorem v2hsc_cleanup_9152_to_9212_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (s0 s1 : State) (fsp out d0 ca1 pa1 ca2 pa2 ca3 pa3 : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9152#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx0_1 : s1.readReg64 .x0 = pa2)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx25_1 : s1.readReg64 .x25 = ca1)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9212#64) s1
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 1272#64) ↦₆₄ pa1) ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        vecCapPtrDealloc A.repAlloc ca1 pa1 ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          ((fsp + 1272#64) ↦₆₄ pa1) ∗
          ((fsp + 184#64) ↦₆₄ pa2) ∗
          ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        TraceCalleeSaved sm s0) :=
  v2hsc_cleanup_9152_to_9212_of_sub_placed
    (v2hsc_sub_ok_dealloc_of_dealloc_placed hdealloc) s0 s1 fsp out d0 ca1 pa1 ca2 pa2 ca3 pa3
    st Frame hfsp_align hpc1 hrun1 hsp1 hx0_1 hx19_1 hx22_1 hx25_1 hx26_1 htr1

theorem v2hsc_cleanup_9152_to_9212_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 s1 : State) (fsp out d0 ca1 pa1 ca2 pa2 ca3 pa3 : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9152#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx0_1 : s1.readReg64 .x0 = pa2)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx25_1 : s1.readReg64 .x25 = ca1)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9212#64) s1
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 1272#64) ↦₆₄ pa1) ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        vecCapPtrDealloc A.repAlloc ca1 pa1 ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          ((fsp + 1272#64) ↦₆₄ pa1) ∗
          ((fsp + 184#64) ↦₆₄ pa2) ∗
          ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        TraceCalleeSaved sm s0) :=
  v2hsc_cleanup_9152_to_9212_of_sub_placed
    (v2hsc_sub_ok_dealloc_of_placedHooks hA) s0 s1 fsp out d0 ca1 pa1 ca2 pa2 ca3 pa3
    st Frame hfsp_align hpc1 hrun1 hsp1 hx0_1 hx19_1 hx22_1 hx25_1 hx26_1 htr1

theorem v2hsc_cleanup_9152_to_9212_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 s1 : State) (fsp out d0 ca1 pa1 ca2 pa2 ca3 pa3 : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9152#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx0_1 : s1.readReg64 .x0 = pa2)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx25_1 : s1.readReg64 .x25 = ca1)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9212#64) s1
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 1272#64) ↦₆₄ pa1) ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        vecCapPtrDealloc A.repAlloc ca1 pa1 ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          ((fsp + 1272#64) ↦₆₄ pa1) ∗
          ((fsp + 184#64) ↦₆₄ pa2) ∗
          ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        TraceCalleeSaved sm s0) :=
  v2hsc_cleanup_9152_to_9212_of_sub_placed
    (v2hsc_sub_ok_dealloc_placed hA) s0 s1 fsp out d0 ca1 pa1 ca2 pa2 ca3 pa3
    st Frame hfsp_align hpc1 hrun1 hsp1 hx0_1 hx19_1 hx22_1 hx25_1 hx26_1 htr1

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hscPlacedBudget

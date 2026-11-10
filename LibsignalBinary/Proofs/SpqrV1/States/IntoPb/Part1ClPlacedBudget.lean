/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.GenLsBlock
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1ClPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1PlacedBudget
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `<States>::into_pb` (Block `334`) — Part 1 `withLsCodeLoaded`: Arm 0 & Call Helpers

Re-exports `withLsCodeLoaded` relocatable Arm 0 (`States.keysUnsampled`) budget proofs and `SepWPp`
call combinators from `Part1PlacedBudget`, and proves total-correctness (`SepWP`) `withLsCodeLoaded`
call helpers for `<PolyEncoder>::into_pb` (`lsmpl.base 375`) and `<PolyDecoder>::into_pb` (`lsmpl.base 377`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1ClPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement extract_withLsCodeLoaded lsmpl
   withLsCodeLoaded)
open CryptoVerification.LibsignalSpqrV1 (PolyDecoder PolyEncoder)
open CryptoVerification.SpqrV1.Poly
  (polyDecoderAt polyDecoderSize polyEncoderAt polyEncoderSize
   protoPolynomialDecoderAt protoPolynomialDecoderSize
   protoPolynomialEncoderAt protoPolynomialEncoderSize)
open CryptoVerification.SpqrV1.Poly.DecoderPb (decoderIntoPbStack)
open CryptoVerification.SpqrV1.Poly.EncoderIntoPb (encoderIntoPbStack)
open CryptoVerification.SpqrV1.States.IntoPb
  (TraceCalleeSaved protoPolynomialDecoderHeap protoPolynomialDecoder_expose
   protoPolynomialEncoderHeap protoPolynomialEncoder_expose
   sepWPp_call_keepLsCl_pub stackAt_encoderIntoPb_eq_decoderIntoPb
   statesIntoPb_seq_sepWP_cl)
open CryptoVerification.SpqrV1.States.IntoPb.Placed (blkPC_334 blkPl_334)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv
   RustCliAllocBudget)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbDefsBudget
  (DecoderIntoPbAllocEnv DecoderIntoPbEnv decoderIntoPbSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.DefsBudget
  (EncoderIntoPbAllocEnv EncoderIntoPbEnv encoderIntoPbSpec)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1PlacedBudget
  (StatesIntoPbNoPanic StatesIntoPbPlacedPost StatesIntoPbPlacedPostOfEnv
   call_decoderIntoPb_expose_cl_placed call_encoderIntoPb_expose_cl_placed
   sepWPp_of_states_into_pb_wpp_cl_placed
   sepWPp_of_states_into_pb_wpp_of_env_cl_placed
   states_into_pb_keysUnsampled_cl_placed
   states_into_pb_keysUnsampled_env_cl_placed
   states_into_pb_keysUnsampled_of_env_cl_placed)

/-! ## 1. Re-Exports from `Part1PlacedBudget` and `Part1ClPlaced` -/

export CryptoVerification.SpqrV1.States.IntoPb
  (statesIntoPb_seq_sepWP_cl sepWPp_call_keepLsCl_pub)

export LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1PlacedBudget
  (StatesIntoPbNoPanic StatesIntoPbPlacedPostOfEnv StatesIntoPbPlacedPost
   states_into_pb_keysUnsampled_of_env_cl_placed
   states_into_pb_keysUnsampled_env_cl_placed
   states_into_pb_keysUnsampled_cl_placed
   sepWPp_of_states_into_pb_wpp_of_env_cl_placed
   sepWPp_of_states_into_pb_wpp_cl_placed
   call_encoderIntoPb_expose_cl_placed
   call_decoderIntoPb_expose_cl_placed)

/-! ## 2. Total-Correctness (`SepWP`) `withLsCodeLoaded` Call Helpers -/

/-- Total-correctness (`SepWP`) call helper for `withLsCodeLoaded lsmpl (encoderIntoPbSpec M A lim)`
    at `lsmpl.base 375`, preserving `LibsignalCodeLoaded lsmpl` via `SepWP.call_subroutine_frame` +
    `KeepsFrozen` when needed or directly discharging `hcl` at entry. -/
theorem call_encoderIntoPb_expose_wp_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (henc_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375)
      (withLsCodeLoaded lsmpl (encoderIntoPbSpec M A lim)))
    (st : M.σ) (outEncA encA : BitVec 64) (enc : PolyEncoder)
    {s0 s : State} {ret_pc target_pc : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = lsmpl.base 375)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 .x30 = ret_pc)
    (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 .x0 = outEncA)
    (hx1 : s.readReg64 .x1 = encA)
    (hfit : FitsEnv M lim st (EncoderIntoPbAllocEnv enc))
    (hsplit : P = (memRegion outEncA protoPolynomialEncoderSize ∗
      polyEncoderAt A.repAlloc encA enc ∗
      A.pool lim st s ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent) (e0 e1 e2 e3 e4 e5 e6 : BitVec 64),
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s0.sp - 1520#64 →
      CalleeSavedPreserved s sf →
      AllocCallPreserved s sf →
      TraceCalleeSaved sf s0 →
      EncoderIntoPbEnv enc evs →
      SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) target_pc sf
        (((outEncA ↦₆₄ e0) ∗ ((outEncA + 8#64) ↦₆₄ e1) ∗ ((outEncA + 16#64) ↦₆₄ e2) ∗
          ((outEncA + 24#64) ↦₆₄ e3) ∗ ((outEncA + 32#64) ↦₆₄ e4) ∗ ((outEncA + 40#64) ↦₆₄ e5) ∗
          ((outEncA + 48#64) ↦₆₄ e6) ∗
          protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 enc.intoPb ∗
          memRegion encA polyEncoderSize ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗ Frame)
        post) :
    SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) target_pc s P post := by
  refine SepWP.call_subroutine_frame henc_cl (x := (⟨outEncA, encA, enc⟩, st)) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [withLsCodeLoaded, encoderIntoPbSpec]
    rw [hsp]
    refine Satisfies.mono
      (P := ⌜s.readReg64 .x0 = outEncA ∧ s.readReg64 .x1 = encA ∧
          FitsEnv M lim st (EncoderIntoPbAllocEnv enc)⌝ ∗
        (⌜LibsignalCodeLoaded lsmpl s.mem⌝ ∗
          (((memRegion outEncA protoPolynomialEncoderSize ∗
              polyEncoderAt A.repAlloc encA enc ∗
              A.pool lim st s ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗ Frame) ∗ R')))
      (Entails.of_eq (by sep_ac_rfl)) ?_
    rw [satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hfit⟩, ?_⟩
    rw [satisfies_pure_sepConj]
    exact ⟨hcl, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm⟩
  · intro _ _ _ hpan
    dsimp only [withLsCodeLoaded, encoderIntoPbSpec] at hpan
    exact not_satisfies_false_sepConj hpan
  · intro _ _ _ _ hex
    dsimp only [withLsCodeLoaded, encoderIntoPbSpec] at hex
    exact not_satisfies_false_sepConj hex
  · intro sm hpcm hrunm hspm hcsm
    dsimp only [withLsCodeLoaded, encoderIntoPbSpec]
    rw [hsp, sepExists_sepConj_left]
    refine SepWP.exists_elim fun evs => ?_
    refine SepWP.weaken_pre (Entails.of_eq (show _ =
      ⌜sm.trace = s.trace ∧ AllocCallPreserved s sm ∧ EncoderIntoPbEnv enc evs⌝ ∗
      ((protoPolynomialEncoderAt A.repAlloc outEncA enc.intoPb ∗
        memRegion encA polyEncoderSize ∗
        A.pool lim (M.stepEvents evs st) sm ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗
       Frame) by sep_ac_rfl)) ?_
    refine SepWP.pure_elim fun ⟨htrm, hacp, henv⟩ => ?_
    have hexp :
        (protoPolynomialEncoderAt A.repAlloc outEncA enc.intoPb ∗
          memRegion encA polyEncoderSize ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗
          Frame ⊢
        ∃∗ e0 : BitVec 64, ∃∗ e1 : BitVec 64, ∃∗ e2 : BitVec 64,
        ∃∗ e3 : BitVec 64, ∃∗ e4 : BitVec 64, ∃∗ e5 : BitVec 64, ∃∗ e6 : BitVec 64,
          (((outEncA ↦₆₄ e0) ∗ ((outEncA + 8#64) ↦₆₄ e1) ∗ ((outEncA + 16#64) ↦₆₄ e2) ∗
            ((outEncA + 24#64) ↦₆₄ e3) ∗ ((outEncA + 32#64) ↦₆₄ e4) ∗ ((outEncA + 40#64) ↦₆₄ e5) ∗
            ((outEncA + 48#64) ↦₆₄ e6) ∗
            protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 enc.intoPb ∗
            memRegion encA polyEncoderSize ∗
            A.pool lim (M.stepEvents evs st) sm ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗
           Frame) := by
      refine Entails.trans (sepConj_mono_left (sepConj_mono_left
        (protoPolynomialEncoder_expose A.repAlloc outEncA enc.intoPb))) ?_
      simp only [sepExists_sepConj_left]
      apply Entails.sepExists_elim; intro e0
      apply Entails.sepExists_elim; intro e1
      apply Entails.sepExists_elim; intro e2
      apply Entails.sepExists_elim; intro e3
      apply Entails.sepExists_elim; intro e4
      apply Entails.sepExists_elim; intro e5
      apply Entails.sepExists_elim; intro e6
      refine Entails.sepExists_right e0 (Entails.sepExists_right e1
        (Entails.sepExists_right e2 (Entails.sepExists_right e3
          (Entails.sepExists_right e4 (Entails.sepExists_right e5
            (Entails.sepExists_right e6 (Entails.of_eq (by sep_ac_rfl))))))))
    refine SepWP.weaken_pre hexp ?_
    refine SepWP.exists_elim fun e0 => SepWP.exists_elim fun e1 =>
      SepWP.exists_elim fun e2 => SepWP.exists_elim fun e3 =>
      SepWP.exists_elim fun e4 => SepWP.exists_elim fun e5 =>
      SepWP.exists_elim fun e6 => ?_
    exact hnext sm evs e0 e1 e2 e3 e4 e5 e6 hpcm hrunm (hspm.trans hsp) hcsm hacp
      ⟨htrm.trans htrace.1, hcsm.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩ henv
  · intro _ _ _ ho
    dsimp only [withLsCodeLoaded, encoderIntoPbSpec] at ho
    exact (not_satisfies_false_sepConj ho).elim

/-- Total-correctness (`SepWP`) call helper for `withLsCodeLoaded lsmpl (decoderIntoPbSpec M A lim)`
    at `lsmpl.base 377`, splitting/restoring `stackAt (s0.sp - 1520#64) encoderIntoPbStack`. -/
theorem call_decoderIntoPb_expose_wp_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdec_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377)
      (withLsCodeLoaded lsmpl (decoderIntoPbSpec M A lim)))
    (st : M.σ) (outDecA decA : BitVec 64) (dec : PolyDecoder)
    {s0 s : State} {ret_pc target_pc : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = lsmpl.base 377)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 .x30 = ret_pc)
    (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 .x0 = outDecA)
    (hx1 : s.readReg64 .x1 = decA)
    (hfit : FitsEnv M lim st (DecoderIntoPbAllocEnv dec))
    (hsplit : P = (memRegion outDecA protoPolynomialDecoderSize ∗
      polyDecoderAt A.repAlloc decA dec ∗
      A.pool lim st s ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent) (d0 d1 d2 d3 d4 : BitVec 64),
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s0.sp - 1520#64 →
      CalleeSavedPreserved s sf →
      AllocCallPreserved s sf →
      TraceCalleeSaved sf s0 →
      DecoderIntoPbEnv dec evs →
      SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) target_pc sf
        (((outDecA ↦₆₄ d0) ∗ ((outDecA + 8#64) ↦₆₄ d1) ∗ ((outDecA + 16#64) ↦₆₄ d2) ∗
          ((outDecA + 24#64) ↦₆₄ d3) ∗ ((outDecA + 32#64) ↦₆₄ d4) ∗
          protoPolynomialDecoderHeap A.repAlloc d0 d1 d2 d3 d4 dec.intoPb ∗
          memRegion decA polyDecoderSize ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗ Frame)
        post) :
    SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) target_pc s P post := by
  refine SepWP.call_subroutine_frame hdec_cl (x := (⟨outDecA, decA, dec⟩, st))
    (F := memRegion ((s0.sp - 1520#64) - 4352#64) 64 ∗ Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hsplit, stackAt_encoderIntoPb_eq_decoderIntoPb (s0.sp - 1520#64)] at hm
    dsimp only [withLsCodeLoaded, decoderIntoPbSpec]
    rw [hsp]
    refine Satisfies.mono
      (P := ⌜s.readReg64 .x0 = outDecA ∧ s.readReg64 .x1 = decA ∧
          FitsEnv M lim st (DecoderIntoPbAllocEnv dec)⌝ ∗
        (⌜LibsignalCodeLoaded lsmpl s.mem⌝ ∗
          (((memRegion outDecA protoPolynomialDecoderSize ∗
              polyDecoderAt A.repAlloc decA dec ∗
              A.pool lim st s ∗
              (memRegion ((s0.sp - 1520#64) - 4352#64) 64 ∗
                stackAt (s0.sp - 1520#64) decoderIntoPbStack)) ∗ Frame) ∗ R')))
      (Entails.of_eq (by sep_ac_rfl)) ?_
    rw [satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hfit⟩, ?_⟩
    rw [satisfies_pure_sepConj]
    exact ⟨hcl, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm⟩
  · intro _ _ _ hpan
    dsimp only [withLsCodeLoaded, decoderIntoPbSpec] at hpan
    exact not_satisfies_false_sepConj hpan
  · intro _ _ _ _ hex
    dsimp only [withLsCodeLoaded, decoderIntoPbSpec] at hex
    exact not_satisfies_false_sepConj hex
  · intro sm hpcm hrunm hspm hcsm
    dsimp only [withLsCodeLoaded, decoderIntoPbSpec]
    rw [hsp, sepExists_sepConj_left]
    refine SepWP.exists_elim fun evs => ?_
    refine SepWP.weaken_pre (Entails.of_eq (show _ =
      ⌜sm.trace = s.trace ∧ AllocCallPreserved s sm ∧ DecoderIntoPbEnv dec evs⌝ ∗
      ((protoPolynomialDecoderAt A.repAlloc outDecA dec.intoPb ∗
        memRegion decA polyDecoderSize ∗
        A.pool lim (M.stepEvents evs st) sm ∗ stackAt (s0.sp - 1520#64) decoderIntoPbStack) ∗
       (memRegion ((s0.sp - 1520#64) - 4352#64) 64 ∗ Frame)) by sep_ac_rfl)) ?_
    refine SepWP.pure_elim fun ⟨htrm, hacp, henv⟩ => ?_
    have hexp :
        (protoPolynomialDecoderAt A.repAlloc outDecA dec.intoPb ∗
          memRegion decA polyDecoderSize ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt (s0.sp - 1520#64) decoderIntoPbStack) ∗
          (memRegion ((s0.sp - 1520#64) - 4352#64) 64 ∗ Frame) ⊢
        ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64,
        ∃∗ d3 : BitVec 64, ∃∗ d4 : BitVec 64,
          (((outDecA ↦₆₄ d0) ∗ ((outDecA + 8#64) ↦₆₄ d1) ∗ ((outDecA + 16#64) ↦₆₄ d2) ∗
            ((outDecA + 24#64) ↦₆₄ d3) ∗ ((outDecA + 32#64) ↦₆₄ d4) ∗
            protoPolynomialDecoderHeap A.repAlloc d0 d1 d2 d3 d4 dec.intoPb ∗
            memRegion decA polyDecoderSize ∗
            A.pool lim (M.stepEvents evs st) sm ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗
           Frame) := by
      refine Entails.trans (sepConj_mono_left (sepConj_mono_left
        (protoPolynomialDecoder_expose A.repAlloc outDecA dec.intoPb))) ?_
      simp only [sepExists_sepConj_left]
      apply Entails.sepExists_elim; intro d0
      apply Entails.sepExists_elim; intro d1
      apply Entails.sepExists_elim; intro d2
      apply Entails.sepExists_elim; intro d3
      apply Entails.sepExists_elim; intro d4
      refine Entails.sepExists_right d0 (Entails.sepExists_right d1
        (Entails.sepExists_right d2 (Entails.sepExists_right d3
          (Entails.sepExists_right d4 ?_))))
      rw [stackAt_encoderIntoPb_eq_decoderIntoPb (s0.sp - 1520#64)]
      exact Entails.of_eq (by sep_ac_rfl)
    refine SepWP.weaken_pre hexp ?_
    refine SepWP.exists_elim fun d0 => SepWP.exists_elim fun d1 =>
      SepWP.exists_elim fun d2 => SepWP.exists_elim fun d3 =>
      SepWP.exists_elim fun d4 => ?_
    exact hnext sm evs d0 d1 d2 d3 d4 hpcm hrunm (hspm.trans hsp) hcsm hacp
      ⟨htrm.trans htrace.1, hcsm.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩ henv
  · intro _ _ _ ho
    dsimp only [withLsCodeLoaded, decoderIntoPbSpec] at ho
    exact (not_satisfies_false_sepConj ho).elim

end LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1ClPlacedBudget

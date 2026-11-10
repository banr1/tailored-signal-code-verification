/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetBase
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7bBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7c
meta import LibsignalBinary.Proofs.SpqrV1.States.FromPb.EpilogueBudget -- shake: keep
import GeneratedLean.LibsignalSessionCode -- shake: keep
meta import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
meta import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry -- shake: keep
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Variant 7 (`Ct1Sampled`, `+1056`) — Part C

Fixed-offset budget-threaded mid-stage cleanup paths (`+7196`, `+7100`, `+3732`, and
`+10556 -> +11112 -> +4632`) under `FreeOnlyEvs`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7cBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification (libsignalSessionCode)
open CryptoVerification.RustHeap (RustAlloc allocHookStack arrayAt vecU8)
open CryptoVerification.LibsignalSpqrV1 (GF16 NUM_POLYS PolyEncoder ProtoPolynomialDecoder)
open CryptoVerification.LibsignalTripleRatchet (tripleRatchetProgAtExt)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.SpqrV1.Drop (
  dropGluePoly16Stack dropStack32 optProtoPolyDecoder_none_entails_memRegion_40
  polyEncoderAt_entails_tag_vecs_tail vecCapPtrDealloc vecGF16ListOf
)
open CryptoVerification.SpqrV1.Poly (polyArrayBytes polyEncoderAt)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack)
open CryptoVerification.SpqrV1.Unchunked (extractLsb'_0_64_append extractLsb'_64_64_append)
open CryptoVerification.SpqrV1.Layout.Stubs (
  fnOff_drop_poly16 stubOff_handle_error stubOff_memcpy
  stubOff_rust_alloc stubOff_rust_dealloc stubOff_rust_no_alloc_shim
)
open CryptoVerification.SpqrV1.States.FromPb (TraceCalleeSaved statesFromPbName statesFromPb_fnOff)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs
  RustCliAllocBudget rustCliDeallocBudgetSpecBase rustDeallocEvents
)
open LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4KBudget (AllocContracts4K)
open LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget (dropGluePoly16SpecBase)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hscBudgetAux (
  allocCallPreserved_of_step deallocFreeOnlySpec sepWP_evs_dealloc sepWP_evs_nil
  seq_clean_evs seq_clean_st
)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4Budget (
  v4_ptsCap_add_one_ne_zero v4_stackAt_allocHook_to_encoderFromPbStack
  v4_stackAt_encoderFromPbStack_to_allocHook v4_sub_ok_dealloc_125316_fo
)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7aBudget (
  v7_proto_decoder_dealloc_4556 v7_sub_ok_drop_poly16
)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7bBudget (
  v7_cleanup_11112 v7_cleanup_opt_decoder_some_pre_pool v7_optDecoderCapProp
  v7_optProtoPolyDecoderTail v7_stackAt_dropStack32_to_encoderFromPbStack
  v7_stackAt_encoderFromPbStack_to_dropStack32
)
open scoped CryptoVerification.CodeLayout
open scoped LibsignalBinary.Proofs.SpqrV1.States.FromPb.EpilogueBudget

/-! ## Re-exports of Pure Predicates & Join Helpers from `Variant7c` -/

abbrev v7_ct1SentSpillCells := CryptoVerification.SpqrV1.States.FromPb.v7_ct1SentSpillCells

alias v7_polyEncoder_1392_join := CryptoVerification.SpqrV1.States.FromPb.v7_polyEncoder_1392_join
alias v7_drop_poly16_pre := CryptoVerification.SpqrV1.States.FromPb.v7_drop_poly16_pre

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  statesFromPb_fnOff fnOff_drop_poly16
  stubOff_rust_no_alloc_shim stubOff_rust_alloc stubOff_rust_dealloc
  stubOff_memcpy stubOff_handle_error TraceCalleeSaved
  RustCliAllocBudget.pool_setPC RustCliAllocBudget.pool_advancePC
  RustCliAllocBudget.pool_setPState RustCliAllocBudget.pool_writeReg64
  RustCliAllocBudget.pool_writeReg32 RustCliAllocBudget.pool_writeReg

/-! ## Local Sequential Event-Composition Helper -/

private theorem seq_acp_evs {M : AllocCostModel}
    {prog : Program} {mid target : BitVec 64} {s1 : State} (st : M.σ)
    {Pre : SepProp} (P_mid P_post : M.σ → State → SepProp)
    (Q_mid : State → Prop) {Q_post : State → Prop}
    (h1 : SepWP prog mid s1 Pre (fun sm Pm =>
      ∃ evs1, FreeOnlyEvs evs1 ∧ (Pm ⊢ P_mid (M.stepEvents evs1 st) sm) ∧
        AllocCallPreserved s1 sm ∧ Q_mid sm))
    (h2 : ∀ (st1 : M.σ) (s2 : State),
      s2.pc = mid → s2.status = .Running → Q_mid s2 →
      SepWP prog target s2 (P_mid st1 s2) (fun sf Pf =>
        ∃ evs2, FreeOnlyEvs evs2 ∧ (Pf ⊢ P_post (M.stepEvents evs2 st1) sf) ∧
          AllocCallPreserved s2 sf ∧ Q_post sf)) :
    SepWP prog target s1 Pre (fun sf Pf =>
      ∃ evs, FreeOnlyEvs evs ∧ (Pf ⊢ P_post (M.stepEvents evs st) sf) ∧
        AllocCallPreserved s1 sf ∧ Q_post sf) := by
  refine seq_clean_evs (P_evs := fun evs1 sm => P_mid (M.stepEvents evs1 st) sm)
    (Q := fun sm => AllocCallPreserved s1 sm ∧ Q_mid sm) h1 ?_
  intro evs1 s2 hevs1 hpc2 hrun2 ⟨hacp1, hq2⟩
  refine SepWP.mono (h2 (M.stepEvents evs1 st) s2 hpc2 hrun2 hq2) ?_
  intro sf _Pf _ _ ⟨evs2, hevs2, hPf, hacp2, hqf⟩
  refine ⟨evs1 ++ evs2, hevs1.append hevs2, ?_, hacp1.trans hacp2, hqf⟩
  rw [AllocCostModel.stepEvents_append]; exact hPf

/-! ## 1. Cleanup at `+7100..+7208 -> +4632` and `+3732..+3740 -> +7104/+7116` -/

/-- Step `+7196 -> +4632` (`mov w28, wzr; cmn x22, #1; b.ne +4556; b +4632`):
sets `x28 = 0#64` and deallocates `optDec` at `pbA + 184#64` if `some`, with `FreeOnlyEvs`. -/
theorem v7_cleanup_7196
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext)
    (s0 s1 : State) (out pbA cap_dec : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder) (st : M.σ) (Frame : SepProp)
    (hcap_dec : v7_optDecoderCapProp cap_dec optDec)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7196#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (pbA + 184#64) 40 ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        AllocCallPreserved s1 sm ∧ sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧ sm.readReg64 .x28 = 0#64 ∧ TraceCalleeSaved sm s0) := by
  rcases htr1 with ⟨htr_1, hvregs_1⟩
  cases optDec with
  | none =>
    unfold v7_optDecoderCapProp CryptoVerification.SpqrV1.States.FromPb.v7_optDecoderCapProp at hcap_dec
    subst hcap_dec
    unfold v7_optProtoPolyDecoderTail CryptoVerification.SpqrV1.States.FromPb.v7_optProtoPolyDecoderTail
    states_from_pb_fetches_range_b b (Rust.withPanics ext) 7196 16
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, noneCap, BitVec.ofNat_eq_ofNat] at hpc1 hx22_1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    apply sepWP_evs_nil; simp only [AllocCostModel.stepEvents_nil]; wp_steps
    apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
    refine ⟨?_, by simp [AllocCallPreserved, wp_norm, arm64_norm, *]⟩
    simp only [wp_norm, arm64_norm]
    have hm := optProtoPolyDecoder_none_entails_memRegion_40 (pbA + 184#64)
    dsimp only [noneCap] at hm
    refine Entails.trans (Entails.of_eq (show _ =
      (((pbA + 184#64) ↦₆₄ 18446744073709551615#64) ∗ memRegion ((pbA + 184#64) + 8#64) 32) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ A.pool lim st s1 ∗ Frame) by sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hm) (Entails.of_eq (by sep_ac_rfl))
  | some pb =>
    refine SepWP.weaken_pre
      (v7_cleanup_opt_decoder_some_pre_pool A.repAlloc (s0.sp - 2400#64) pbA cap_dec pb
        (A.pool lim st s1) Frame) ?_
    apply ProofLib.SepWP.exists_left; intro ptsPtr
    apply ProofLib.SepWP.pure_elim; rintro ⟨hpts_le, hpts_cap_lt, _⟩
    dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
    refine seq_clean_st
      (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4556#64)
      (P_mid := fun sm =>
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗ ((pbA + 192#64) ↦₆₄ ptsPtr) ∗
         ((pbA + 200#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
         (if cap_dec = 0 then emp
          else A.live ptsPtr (cap_dec.toNat * 24) 8 ∗
            arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pb.pts ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24))
              ((cap_dec.toNat - pb.pts.length) * 24)) ∗
         memRegion (pbA + 208#64) 16) ∗
        A.pool lim st sm ∗ Frame)
      (Q := fun sm => AllocCallPreserved s1 sm ∧ sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧ sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x27 = pbA ∧ sm.readReg64 .x28 = 0#64 ∧ TraceCalleeSaved sm s0) ?_ ?_
    · have hne := v4_ptsCap_add_one_ne_zero hpts_cap_lt
      states_from_pb_fetches_range_b b (Rust.withPanics ext) 7196 12
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches; wp_steps
      apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
      refine ⟨?_, by simp [AllocCallPreserved, wp_norm, arm64_norm, *]⟩
      simp only [wp_norm, arm64_norm]; exact Entails.of_eq (by sep_ac_rfl)
    · intro s2 hpc2 hrun2 ⟨hacp1, hsp2, hx19_2, hx22_2, hx27_2, hx28_2, htr2⟩
      have h4556 := v7_proto_decoder_dealloc_4556 hA s0 s2 out pbA cap_dec ptsPtr 0#64 pb.pts st Frame
        hsp0_align hpts_le hpts_cap_lt hpc2 hrun2 hsp2 hx19_2 hx22_2 hx27_2 hx28_2 htr2
      exact SepWP.mono h4556 fun sm _Pm _ _ ⟨evs, hevs, hPm, hacp2, hrest⟩ =>
        ⟨evs, hevs, hPm, hacp1.trans hacp2, hrest⟩

/-- Deallocate the 4 `Vec<u8>` buffers `c2/p2 .. c5/p5` at `+7116 -> +7196` (`0x5bc70 -> 0x5bcc0`). -/
theorem v7_dealloc_4vecs_7116_to_7196
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext)
    (s0 s1 : State) (out pbA cap_dec c2 p2 c3 p3 c4 p4 c5 p5 : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7116#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx24_1 : s1.readReg64 .x24 = c2) (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7196#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
        vecCapPtrDealloc A.repAlloc c2 p2 ∗ vecCapPtrDealloc A.repAlloc c3 p3 ∗
        vecCapPtrDealloc A.repAlloc c4 p4 ∗ vecCapPtrDealloc A.repAlloc c5 p5 ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        AllocCallPreserved s1 sm ∧ sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧ sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x27 = pbA ∧ TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hdealloc := v4_sub_ok_dealloc_125316_fo hA
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpecBase] at hdealloc
  refine SepWP.weaken_pre
    (sepConj_mono_left (v4_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
  unfold v7_ct1SentSpillCells CryptoVerification.SpqrV1.States.FromPb.v7_ct1SentSpillCells
  have h7552 : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
  have h1296 : (s0.sp - 2400#64) + 1296#64 = s0.sp - 1104#64 := by bv_omega
  have h1312 : (s0.sp - 2400#64) + 1312#64 = s0.sp - 1088#64 := by bv_omega
  have h1320 : (s0.sp - 2400#64) + 1320#64 = s0.sp - 1080#64 := by bv_omega
  have h1336 : (s0.sp - 2400#64) + 1336#64 = s0.sp - 1064#64 := by bv_omega
  have h1344 : (s0.sp - 2400#64) + 1344#64 = s0.sp - 1056#64 := by bv_omega
  have h1360 : (s0.sp - 2400#64) + 1360#64 = s0.sp - 1040#64 := by bv_omega
  have h1368 : (s0.sp - 2400#64) + 1368#64 = s0.sp - 1032#64 := by bv_omega
  have hst := v4_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
  rw [h7552] at hst; rw [h7552, h1296, h1312, h1320, h1336, h1344, h1360, h1368]
  states_from_pb_fetches_range_b b (Rust.withPanics ext) 7116 80
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, vecCapPtrDealloc,
    LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live,
    BitVec.ofNat_eq_ofNat] at hdealloc hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  let P_post : M.σ → State → SepProp := fun stf sm =>
    stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      (((s0.sp - 1104#64) ↦₆₄ p2) ∗ ((s0.sp - 1088#64) ↦₆₄ c3) ∗ ((s0.sp - 1080#64) ↦₆₄ p3) ∗
       ((s0.sp - 1064#64) ↦₆₄ c4) ∗ ((s0.sp - 1056#64) ↦₆₄ p4) ∗ ((s0.sp - 1040#64) ↦₆₄ c5) ∗
       ((s0.sp - 1032#64) ↦₆₄ p5)) ∗
      A.pool lim stf sm ∗ Frame
  refine seq_acp_evs st (mid := entry + 7136#64)
    (fun st1 sm =>
      (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
      (((s0.sp - 1104#64) ↦₆₄ p2) ∗ ((s0.sp - 1088#64) ↦₆₄ c3) ∗ ((s0.sp - 1080#64) ↦₆₄ p3) ∗
       ((s0.sp - 1064#64) ↦₆₄ c4) ∗ ((s0.sp - 1056#64) ↦₆₄ p4) ∗ ((s0.sp - 1040#64) ↦₆₄ c5) ∗
       ((s0.sp - 1032#64) ↦₆₄ p5)) ∗
      (if (c3 == 0#64) = true then emp else A.live p3 c3.toNat 1 ∗ memRegion p3 c3.toNat) ∗
      (if (c4 == 0#64) = true then emp else A.live p4 c4.toNat 1 ∗ memRegion p4 c4.toNat) ∗
      (if (c5 == 0#64) = true then emp else A.live p5 c5.toNat 1 ∗ memRegion p5 c5.toNat) ∗
      A.pool lim st1 sm ∗ Frame)
    P_post
    (fun sm => sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = cap_dec ∧ sm.readReg64 .x27 = pbA ∧ TraceCalleeSaved sm s0) ?_ ?_
  · rcases htr1 with ⟨htr_1, hvregs_1⟩
    by_cases hc2 : (c2 == 0#64) = true
    · simp only [hc2, ↓reduceIte, sepConj_emp, emp_sepConj]
      apply sepWP_evs_nil; simp only [AllocCostModel.stepEvents_nil]; wp_steps
      apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
      exact ⟨by simp only [wp_norm, arm64_norm]; exact Entails.of_eq (by sep_ac_rfl),
        by simp [AllocCallPreserved, wp_norm, arm64_norm, *]⟩
    · have hc2_f : (c2 == 0#64) = false := Bool.eq_false_iff.mpr hc2
      simp only [hc2_f, Bool.false_eq_true, ↓reduceIte]
      apply sepWP_evs_dealloc c2.toNat 1; wp_steps; wp_apply
      have hacp_s : AllocCallPreserved s1 sf :=
        allocCallPreserved_of_step (by assumption) (by simp [AllocCallPreserved, wp_norm, arm64_norm])
      have ⟨_, _, _, _, _, _, _⟩ := hacp_s
      have hsp_sf' : sf.sp = s0.sp - 2400#64 := hsp_sf.trans (by simp [wp_norm, arm64_norm, hsp1])
      apply SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
      refine ⟨?_, hacp_s, by simp [wp_norm, arm64_norm, hsp_sf', *]⟩
      rw [← hsp_sf, hsp_sf']; exact Entails.of_eq (by sep_ac_rfl)
  intro st2 s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, hx27_2, htr2⟩
  refine seq_acp_evs st2 (mid := entry + 7156#64)
    (fun st3 sm =>
      (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
      (((s0.sp - 1104#64) ↦₆₄ p2) ∗ ((s0.sp - 1088#64) ↦₆₄ c3) ∗ ((s0.sp - 1080#64) ↦₆₄ p3) ∗
       ((s0.sp - 1064#64) ↦₆₄ c4) ∗ ((s0.sp - 1056#64) ↦₆₄ p4) ∗ ((s0.sp - 1040#64) ↦₆₄ c5) ∗
       ((s0.sp - 1032#64) ↦₆₄ p5)) ∗
      (if (c4 == 0#64) = true then emp else A.live p4 c4.toNat 1 ∗ memRegion p4 c4.toNat) ∗
      (if (c5 == 0#64) = true then emp else A.live p5 c5.toNat 1 ∗ memRegion p5 c5.toNat) ∗
      A.pool lim st3 sm ∗ Frame)
    P_post
    (fun sm => sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = cap_dec ∧ sm.readReg64 .x27 = pbA ∧ TraceCalleeSaved sm s0) ?_ ?_
  · rcases htr2 with ⟨htr_2, hvregs_2⟩
    by_cases hc3 : (c3 == 0#64) = true
    · simp only [hc3, ↓reduceIte, sepConj_emp, emp_sepConj]
      apply sepWP_evs_nil; simp only [AllocCostModel.stepEvents_nil]; wp_steps
      apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun2])
      exact ⟨by simp only [wp_norm, arm64_norm]; exact Entails.of_eq (by sep_ac_rfl),
        by simp [AllocCallPreserved, wp_norm, arm64_norm, *]⟩
    · have hc3_f : (c3 == 0#64) = false := Bool.eq_false_iff.mpr hc3
      simp only [hc3_f, Bool.false_eq_true, ↓reduceIte]
      apply sepWP_evs_dealloc c3.toNat 1; wp_steps; wp_apply
      have hacp_s : AllocCallPreserved s2 sf :=
        allocCallPreserved_of_step (by assumption) (by simp [AllocCallPreserved, wp_norm, arm64_norm])
      have ⟨_, _, _, _, _, _, _⟩ := hacp_s
      have hsp_sf' : sf.sp = s0.sp - 2400#64 := hsp_sf.trans (by simp [wp_norm, arm64_norm, hsp2])
      apply SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
      refine ⟨?_, hacp_s, by simp [wp_norm, arm64_norm, hsp_sf', *]⟩
      rw [← hsp_sf, hsp_sf']; exact Entails.of_eq (by sep_ac_rfl)
  intro st3 s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx22_3, hx27_3, htr3⟩
  refine seq_acp_evs st3 (mid := entry + 7176#64)
    (fun st4 sm =>
      (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
      (((s0.sp - 1104#64) ↦₆₄ p2) ∗ ((s0.sp - 1088#64) ↦₆₄ c3) ∗ ((s0.sp - 1080#64) ↦₆₄ p3) ∗
       ((s0.sp - 1064#64) ↦₆₄ c4) ∗ ((s0.sp - 1056#64) ↦₆₄ p4) ∗ ((s0.sp - 1040#64) ↦₆₄ c5) ∗
       ((s0.sp - 1032#64) ↦₆₄ p5)) ∗
      (if (c5 == 0#64) = true then emp else A.live p5 c5.toNat 1 ∗ memRegion p5 c5.toNat) ∗
      A.pool lim st4 sm ∗ Frame)
    P_post
    (fun sm => sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = cap_dec ∧ sm.readReg64 .x27 = pbA ∧ TraceCalleeSaved sm s0) ?_ ?_
  · rcases htr3 with ⟨htr_3, hvregs_3⟩
    by_cases hc4 : (c4 == 0#64) = true
    · simp only [hc4, ↓reduceIte, sepConj_emp, emp_sepConj]
      apply sepWP_evs_nil; simp only [AllocCostModel.stepEvents_nil]; wp_steps
      apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun3])
      exact ⟨by simp only [wp_norm, arm64_norm]; exact Entails.of_eq (by sep_ac_rfl),
        by simp [AllocCallPreserved, wp_norm, arm64_norm, *]⟩
    · have hc4_f : (c4 == 0#64) = false := Bool.eq_false_iff.mpr hc4
      simp only [hc4_f, Bool.false_eq_true, ↓reduceIte]
      apply sepWP_evs_dealloc c4.toNat 1; wp_steps; wp_apply
      have hacp_s : AllocCallPreserved s3 sf :=
        allocCallPreserved_of_step (by assumption) (by simp [AllocCallPreserved, wp_norm, arm64_norm])
      have ⟨_, _, _, _, _, _, _⟩ := hacp_s
      have hsp_sf' : sf.sp = s0.sp - 2400#64 := hsp_sf.trans (by simp [wp_norm, arm64_norm, hsp3])
      apply SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
      refine ⟨?_, hacp_s, by simp [wp_norm, arm64_norm, hsp_sf', *]⟩
      rw [← hsp_sf, hsp_sf']; exact Entails.of_eq (by sep_ac_rfl)
  intro st4 s4 hpc4 hrun4 ⟨hsp4, hx19_4, hx22_4, hx27_4, htr4⟩
  rcases htr4 with ⟨htr_4, hvregs_4⟩
  by_cases hc5 : (c5 == 0#64) = true
  · simp only [hc5, ↓reduceIte, sepConj_emp, emp_sepConj]
    apply sepWP_evs_nil; simp only [AllocCostModel.stepEvents_nil]; wp_steps
    apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun4])
    exact ⟨by dsimp only [P_post]; simp only [wp_norm, arm64_norm]; exact Entails.trans (Entails.of_eq (by sep_ac_rfl)) (sepConj_mono_left hst),
      by simp [AllocCallPreserved, wp_norm, arm64_norm, *]⟩
  · have hc5_f : (c5 == 0#64) = false := Bool.eq_false_iff.mpr hc5
    simp only [hc5_f, Bool.false_eq_true, ↓reduceIte]
    apply sepWP_evs_dealloc c5.toNat 1; wp_steps; wp_apply
    have hacp_s : AllocCallPreserved s4 sf :=
      allocCallPreserved_of_step (by assumption) (by simp [AllocCallPreserved, wp_norm, arm64_norm])
    have ⟨_, _, _, _, _, _, _⟩ := hacp_s
    have hsp_sf' : sf.sp = s0.sp - 2400#64 := hsp_sf.trans (by simp [wp_norm, arm64_norm, hsp4])
    apply SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
    refine ⟨?_, hacp_s, by simp [wp_norm, arm64_norm, hsp_sf', *]⟩
    rw [← hsp_sf, hsp_sf']
    refine Entails.trans (Entails.of_eq (show _ =
      (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
      ((((s0.sp - 1104#64) ↦₆₄ p2) ∗ ((s0.sp - 1088#64) ↦₆₄ c3) ∗ ((s0.sp - 1080#64) ↦₆₄ p3) ∗
        ((s0.sp - 1064#64) ↦₆₄ c4) ∗ ((s0.sp - 1056#64) ↦₆₄ p4) ∗ ((s0.sp - 1040#64) ↦₆₄ c5) ∗
        ((s0.sp - 1032#64) ↦₆₄ p5)) ∗
       A.pool lim (M.stepEvents (rustDeallocEvents c5.toNat 1) st4) sf ∗ Frame) by sep_ac_rfl)) ?_
    exact sepConj_mono_left hst

/-- Deallocate `c1/p1` at `+7104 -> +7116` (`mov x0, x28; mov w2, #1; bl __rust_dealloc`)
when `¬((c1 == 0#64) = true)`. -/
theorem v7_dealloc_c1_7104_to_7116
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext)
    (s0 s1 : State) (out pbA cap_dec c1 p1 c2 : BitVec 64)
    (st : M.σ) (Frame : SepProp) (hc1 : ¬((c1 == 0#64) = true))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7104#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx1_1 : s1.readReg64 .x1 = c1) (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = cap_dec) (hx24_1 : s1.readReg64 .x24 = c2)
    (hx27_1 : s1.readReg64 .x27 = pbA) (hx28_1 : s1.readReg64 .x28 = p1)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7116#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        vecCapPtrDealloc A.repAlloc c1 p1 ∗ A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        AllocCallPreserved s1 sm ∧ sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧ sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x24 = c2 ∧ sm.readReg64 .x27 = pbA ∧ TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  rcases htr1 with ⟨htr_1, hvregs_1⟩
  have hdealloc := v4_sub_ok_dealloc_125316_fo hA
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpecBase] at hdealloc
  refine SepWP.weaken_pre
    (sepConj_mono_left (v4_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
  have h7552 : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
  rw [h7552]
  have hst := v4_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
  rw [h7552] at hst
  states_from_pb_fetches_range_b b (Rust.withPanics ext) 7104 12
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, vecCapPtrDealloc,
    LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live,
    BitVec.ofNat_eq_ofNat] at hdealloc hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  simp only [hc1, ↓reduceIte]
  apply sepWP_evs_dealloc c1.toNat 1; wp_steps; wp_apply
  have hacp_s : AllocCallPreserved s1 sf :=
    allocCallPreserved_of_step (by assumption) (by simp [AllocCallPreserved, wp_norm, arm64_norm])
  have ⟨_, _, _, _, _, _, _⟩ := hacp_s
  have hsp_sf' : sf.sp = s0.sp - 2400#64 := hsp_sf.trans (by simp [wp_norm, arm64_norm, hsp1])
  apply SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
  refine ⟨?_, hacp_s, by simp [wp_norm, arm64_norm, hsp_sf', *]⟩
  rw [← hsp_sf, hsp_sf']
  refine Entails.trans (Entails.of_eq (show _ =
    (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
    (A.pool lim (M.stepEvents (rustDeallocEvents c1.toNat 1) st) sf ∗ Frame) by sep_ac_rfl)) ?_
  exact sepConj_mono_left hst

/-- Cleanup at `+7100 -> +4632` (`0x5bc60`, when `s.sendingCt1 = none`):
deallocates `c1/p1 .. c5/p5` and `optDec` (if `some`), sets `x28 = 0#64`, and reaches `+4632`. -/
theorem v7_cleanup_7100
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext)
    (s0 s1 : State) (out pbA cap_dec c1 p1 c2 p2 c3 p3 c4 p4 c5 p5 : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder) (st : M.σ) (Frame : SepProp)
    (hcap_dec : v7_optDecoderCapProp cap_dec optDec)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7100#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx1_1 : s1.readReg64 .x1 = c1) (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = cap_dec) (hx24_1 : s1.readReg64 .x24 = c2)
    (hx27_1 : s1.readReg64 .x27 = pbA) (hx28_1 : s1.readReg64 .x28 = p1)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
        vecCapPtrDealloc A.repAlloc c1 p1 ∗ vecCapPtrDealloc A.repAlloc c2 p2 ∗
        vecCapPtrDealloc A.repAlloc c3 p3 ∗ vecCapPtrDealloc A.repAlloc c4 p4 ∗
        vecCapPtrDealloc A.repAlloc c5 p5 ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
          memRegion (pbA + 184#64) 40 ∗ A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        AllocCallPreserved s1 sm ∧ sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧ sm.readReg64 .x28 = 0#64 ∧ TraceCalleeSaved sm s0) := by
  let P_post : M.σ → State → SepProp := fun stf sm =>
    stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
      memRegion (pbA + 184#64) 40 ∗ A.pool lim stf sm ∗ Frame
  refine seq_acp_evs st
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7116#64)
    (fun st1 sm =>
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ A.pool lim st1 sm ∗
      (v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
       vecCapPtrDealloc A.repAlloc c2 p2 ∗ vecCapPtrDealloc A.repAlloc c3 p3 ∗
       vecCapPtrDealloc A.repAlloc c4 p4 ∗ vecCapPtrDealloc A.repAlloc c5 p5 ∗
       (((pbA + 184#64) ↦₆₄ cap_dec) ∗
        v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗ Frame))
    P_post
    (fun sm => sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = cap_dec ∧ sm.readReg64 .x24 = c2 ∧
      sm.readReg64 .x27 = pbA ∧ TraceCalleeSaved sm s0) ?_ ?_
  · by_cases hc1 : (c1 == 0#64) = true
    · rcases htr1 with ⟨htr_1, hvregs_1⟩
      states_from_pb_fetches_range_b b (Rust.withPanics ext) 7100 4
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, vecCapPtrDealloc,
        BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches; simp only [hc1, ↓reduceIte, emp_sepConj]
      apply sepWP_evs_nil; simp only [AllocCostModel.stepEvents_nil]; wp_steps
      apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
      exact ⟨by simp only [wp_norm, arm64_norm]; exact Entails.of_eq (by sep_ac_rfl),
        by simp [AllocCallPreserved, wp_norm, arm64_norm, *]⟩
    · rcases htr1 with ⟨htr_1, hvregs_1⟩
      refine seq_clean_st
        (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7104#64)
        (P_mid := fun sm =>
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ vecCapPtrDealloc A.repAlloc c1 p1 ∗
          A.pool lim st sm ∗
          (v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
           vecCapPtrDealloc A.repAlloc c2 p2 ∗ vecCapPtrDealloc A.repAlloc c3 p3 ∗
           vecCapPtrDealloc A.repAlloc c4 p4 ∗ vecCapPtrDealloc A.repAlloc c5 p5 ∗
           (((pbA + 184#64) ↦₆₄ cap_dec) ∗
            v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗ Frame))
        (Q := fun sm => AllocCallPreserved s1 sm ∧ sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x1 = c1 ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x22 = cap_dec ∧
          sm.readReg64 .x24 = c2 ∧ sm.readReg64 .x27 = pbA ∧ sm.readReg64 .x28 = p1 ∧
          TraceCalleeSaved sm s0) ?_ ?_
      · states_from_pb_fetches_range_b b (Rust.withPanics ext) 7100 4
        dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
        generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
          "<spqr::v1::chunked::states::States>::from_pb" = entry
        examples_hide_fetches; wp_steps
        apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
        exact ⟨by simp only [wp_norm, arm64_norm]; exact Entails.of_eq (by sep_ac_rfl),
          by simp [AllocCallPreserved, wp_norm, arm64_norm, *]⟩
      · intro s2 hpc2 hrun2 ⟨hacp1, hsp2, hx1_2, hx19_2, hx22_2, hx24_2, hx27_2, hx28_2, htr2⟩
        have h7104 := v7_dealloc_c1_7104_to_7116 hA s0 s2 out pbA cap_dec c1 p1 c2 st
          (v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
           vecCapPtrDealloc A.repAlloc c2 p2 ∗ vecCapPtrDealloc A.repAlloc c3 p3 ∗
           vecCapPtrDealloc A.repAlloc c4 p4 ∗ vecCapPtrDealloc A.repAlloc c5 p5 ∗
           (((pbA + 184#64) ↦₆₄ cap_dec) ∗
            v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗ Frame)
          hc1 hsp0_align hpc2 hrun2 hsp2 hx1_2 hx19_2 hx22_2 hx24_2 hx27_2 hx28_2 htr2
        exact SepWP.mono h7104 fun sm _Pm _ _ ⟨evs, hevs, hPm, hacp2, hrest⟩ =>
          ⟨evs, hevs, hPm, hacp1.trans hacp2, hrest⟩
  · intro st1 s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, hx24_2, hx27_2, htr2⟩
    refine seq_acp_evs st1
      (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7196#64)
      (fun st2 sm =>
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
        A.pool lim st2 sm ∗
        ((((pbA + 184#64) ↦₆₄ cap_dec) ∗
          v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗ Frame))
      P_post
      (fun sm => sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = cap_dec ∧ sm.readReg64 .x27 = pbA ∧ TraceCalleeSaved sm s0) ?_ ?_
    · exact SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (v7_dealloc_4vecs_7116_to_7196 hA s0 s2 out pbA cap_dec c2 p2 c3 p3 c4 p4 c5 p5 st1
          ((((pbA + 184#64) ↦₆₄ cap_dec) ∗
            v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗ Frame)
          hsp0_align hpc2 hrun2 hsp2 hx19_2 hx22_2 hx24_2 hx27_2 htr2)
    · intro st2 s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx22_3, hx27_3, htr3⟩
      have h7196 := v7_cleanup_7196 hA s0 s3 out pbA cap_dec optDec st2
        (v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗ Frame)
        hcap_dec hsp0_align hpc3 hrun3 hsp3 hx19_3 hx22_3 hx27_3 htr3
      refine SepWP.weaken_pre ?_
        (SepWP.mono h7196 fun _ _ _ _ ⟨evs, hevs, hPm, hacp, hq⟩ =>
          ⟨evs, hevs, Entails.trans hPm (by dsimp only [P_post]; exact Entails.of_eq (by sep_ac_rfl)), hacp, hq⟩)
      exact Entails.of_eq (by sep_ac_rfl)

/-- Cleanup at `+3732 -> +4632` (`0x5af38`, when `<PolyEncoder>::from_pb = Err`):
loads `c1` from `[sp, #0x18]`, deallocates `c1/p1 .. c5/p5` and `optDec` (if `some`),
sets `x28 = 0#64`, and reaches `+4632`. -/
theorem v7_cleanup_3732
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext)
    (s0 s1 : State) (out pbA cap_dec c1 p1 c2 p2 c3 p3 c4 p4 c5 p5 : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder) (st : M.σ) (Frame : SepProp)
    (hcap_dec : v7_optDecoderCapProp cap_dec optDec)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3732#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx24_1 : s1.readReg64 .x24 = c2) (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = p1) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
        v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
        vecCapPtrDealloc A.repAlloc c1 p1 ∗ vecCapPtrDealloc A.repAlloc c2 p2 ∗
        vecCapPtrDealloc A.repAlloc c3 p3 ∗ vecCapPtrDealloc A.repAlloc c4 p4 ∗
        vecCapPtrDealloc A.repAlloc c5 p5 ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
          v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
          memRegion (pbA + 184#64) 40 ∗ A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        AllocCallPreserved s1 sm ∧ sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧ sm.readReg64 .x28 = 0#64 ∧ TraceCalleeSaved sm s0) := by
  have h24 : (s0.sp - 2400#64) + 24#64 = s0.sp - 2376#64 := by bv_omega
  let P_post : M.σ → State → SepProp := fun stf sm =>
    stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
      v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
      memRegion (pbA + 184#64) 40 ∗ A.pool lim stf sm ∗ Frame
  refine seq_acp_evs st
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7116#64)
    (fun st1 sm =>
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ A.pool lim st1 sm ∗
      (v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
       vecCapPtrDealloc A.repAlloc c2 p2 ∗ vecCapPtrDealloc A.repAlloc c3 p3 ∗
       vecCapPtrDealloc A.repAlloc c4 p4 ∗ vecCapPtrDealloc A.repAlloc c5 p5 ∗
       (((pbA + 184#64) ↦₆₄ cap_dec) ∗
        v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗
       ((((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗ Frame)))
    P_post
    (fun sm => sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = cap_dec ∧ sm.readReg64 .x24 = c2 ∧
      sm.readReg64 .x27 = pbA ∧ TraceCalleeSaved sm s0) ?_ ?_
  · by_cases hc1 : (c1 == 0#64) = true
    · rcases htr1 with ⟨htr_1, hvregs_1⟩
      rw [h24]
      states_from_pb_fetches_range_b b (Rust.withPanics ext) 3732 12
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, vecCapPtrDealloc,
        BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches; simp only [hc1, Bool.true_eq_false, ↓reduceIte, emp_sepConj]
      apply sepWP_evs_nil; simp only [AllocCostModel.stepEvents_nil]; wp_steps
      apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
      exact ⟨by simp only [wp_norm, arm64_norm]; exact Entails.of_eq (by sep_ac_rfl),
        by simp [AllocCallPreserved, wp_norm, arm64_norm, *]⟩
    · rcases htr1 with ⟨htr_1, hvregs_1⟩
      refine seq_clean_st
        (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7104#64)
        (P_mid := fun sm =>
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ vecCapPtrDealloc A.repAlloc c1 p1 ∗
          A.pool lim st sm ∗
          (v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
           vecCapPtrDealloc A.repAlloc c2 p2 ∗ vecCapPtrDealloc A.repAlloc c3 p3 ∗
           vecCapPtrDealloc A.repAlloc c4 p4 ∗ vecCapPtrDealloc A.repAlloc c5 p5 ∗
           (((pbA + 184#64) ↦₆₄ cap_dec) ∗
            v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗
           ((((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗ Frame)))
        (Q := fun sm => AllocCallPreserved s1 sm ∧ sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x1 = c1 ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x22 = cap_dec ∧
          sm.readReg64 .x24 = c2 ∧ sm.readReg64 .x27 = pbA ∧ sm.readReg64 .x28 = p1 ∧
          TraceCalleeSaved sm s0) ?_ ?_
      · rw [h24]
        states_from_pb_fetches_range_b b (Rust.withPanics ext) 3732 8
        dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
        generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
          "<spqr::v1::chunked::states::States>::from_pb" = entry
        examples_hide_fetches; wp_steps
        apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
        exact ⟨by simp only [wp_norm, arm64_norm]; exact Entails.of_eq (by sep_ac_rfl),
          by simp [AllocCallPreserved, wp_norm, arm64_norm, *]⟩
      · intro s2 hpc2 hrun2 ⟨hacp1, hsp2, hx1_2, hx19_2, hx22_2, hx24_2, hx27_2, hx28_2, htr2⟩
        have h7104 := v7_dealloc_c1_7104_to_7116 hA s0 s2 out pbA cap_dec c1 p1 c2 st
          (v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
           vecCapPtrDealloc A.repAlloc c2 p2 ∗ vecCapPtrDealloc A.repAlloc c3 p3 ∗
           vecCapPtrDealloc A.repAlloc c4 p4 ∗ vecCapPtrDealloc A.repAlloc c5 p5 ∗
           (((pbA + 184#64) ↦₆₄ cap_dec) ∗
            v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗
           ((((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗ Frame))
          hc1 hsp0_align hpc2 hrun2 hsp2 hx1_2 hx19_2 hx22_2 hx24_2 hx27_2 hx28_2 htr2
        exact SepWP.mono h7104 fun sm _Pm _ _ ⟨evs, hevs, hPm, hacp2, hrest⟩ =>
          ⟨evs, hevs, hPm, hacp1.trans hacp2, hrest⟩
  · intro st1 s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, hx24_2, hx27_2, htr2⟩
    refine seq_acp_evs st1
      (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7196#64)
      (fun st2 sm =>
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
        A.pool lim st2 sm ∗
        ((((pbA + 184#64) ↦₆₄ cap_dec) ∗
          v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗
         ((((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗ Frame)))
      P_post
      (fun sm => sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = cap_dec ∧ sm.readReg64 .x27 = pbA ∧ TraceCalleeSaved sm s0) ?_ ?_
    · exact SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (v7_dealloc_4vecs_7116_to_7196 hA s0 s2 out pbA cap_dec c2 p2 c3 p3 c4 p4 c5 p5 st1
          ((((pbA + 184#64) ↦₆₄ cap_dec) ∗
            v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗
           ((((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗ Frame))
          hsp0_align hpc2 hrun2 hsp2 hx19_2 hx22_2 hx24_2 hx27_2 htr2)
    · intro st2 s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx22_3, hx27_3, htr3⟩
      have h7196 := v7_cleanup_7196 hA s0 s3 out pbA cap_dec optDec st2
        (v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
         ((((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗ Frame))
        hcap_dec hsp0_align hpc3 hrun3 hsp3 hx19_3 hx22_3 hx27_3 htr3
      refine SepWP.weaken_pre ?_
        (SepWP.mono h7196 fun _ _ _ _ ⟨evs, hevs, hPm, hacp, hq⟩ =>
          ⟨evs, hevs, Entails.trans hPm (by dsimp only [P_post]; exact Entails.of_eq (by sep_ac_rfl)), hacp, hq⟩)
      exact Entails.of_eq (by sep_ac_rfl)

/-! ## 2. Cleanup at `+10556..+10672 -> +11112 -> +4632` (`s.receivingEk = none`) -/

theorem v7_drop_poly16_pre_pool (A : RustAlloc) (fsp : BitVec 64) (enc : PolyEncoder)
    (Pool Frame : SepProp) :
    stackAt fsp encoderFromPbStack ∗ polyEncoderAt A (fsp + 1392#64) enc ∗ Pool ∗ Frame ⊢
    ∃∗ tag : BitVec 64, ∃∗ vecs : List (List GF16),
      ⌜vecs.length = NUM_POLYS⌝ ∗
      ((stackAt fsp dropStack32 ∗ memRegion (fsp - 5152#64) 1024) ∗
       ((fsp + 1392#64) ↦₆₄ tag) ∗ vecGF16ListOf A ((fsp + 1392#64) + 8#64) vecs ∗
       memRegion ((fsp + 1392#64) + 392#64) 8 ∗ Pool ∗ Frame) := by
  refine Entails.trans
    (sepConj_mono
      (v7_stackAt_encoderFromPbStack_to_dropStack32 fsp)
      (sepConj_mono_left (polyEncoderAt_entails_tag_vecs_tail A (fsp + 1392#64) enc))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro tag
  apply Entails.sepExists_elim; intro vecs
  exact Entails.sepExists_right tag (Entails.sepExists_right vecs (Entails.of_eq (by sep_ac_rfl)))

/-- Step `+10556 -> +10568`: drops `[Poly; 16]` at `(s0.sp - 2400#64) + 1400#64` via `v7_sub_ok_drop_poly16`
and combines with the tag and tail to leave `memRegion ((s0.sp - 2400#64) + 1392#64) 400`. -/
theorem v7_drop_poly16_10556_to_10568
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext)
    (s0 s1 : State) (out c2 : BitVec 64)
    (enc : PolyEncoder) (st : M.σ) (Frame : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10556#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx24_1 : s1.readReg64 .x24 = c2)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10568#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        polyEncoderAt A.repAlloc ((s0.sp - 2400#64) + 1392#64) enc ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        AllocCallPreserved s1 sm ∧ sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧ sm.readReg64 .x24 = c2 ∧ TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  rcases htr1 with ⟨htr_1, hvregs_1⟩
  have hdrop := v7_sub_ok_drop_poly16 hA
  simp only [dropGluePoly16SpecBase, dropGluePoly16Stack] at hdrop
  refine SepWP.weaken_pre
    (v7_drop_poly16_pre_pool A.repAlloc (s0.sp - 2400#64) enc (A.pool lim st s1) Frame) ?_
  apply ProofLib.SepWP.exists_left; intro tag
  apply ProofLib.SepWP.exists_left; intro vecs
  apply ProofLib.SepWP.pure_elim; intro hvecs_len
  have h1392 : (s0.sp - 2400#64) + 1392#64 = s0.sp - 1008#64 := by bv_omega
  have h1400 : (s0.sp - 1008#64) + 8#64 = s0.sp - 1000#64 := by bv_omega
  have h1784 : (s0.sp - 1008#64) + 392#64 = s0.sp - 616#64 := by bv_omega
  have h7552 : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
  rw [h1392, h1400, h1784, h7552]
  states_from_pb_fetches_range_b b (Rust.withPanics ext) 10556 12
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, polyArrayBytes,
    BitVec.ofNat_eq_ofNat] at hdrop hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hdrop
  wp_steps
  wp_call hdrop (⟨s0.sp - 1000#64, vecs⟩, st)
  have hacp : AllocCallPreserved s1 sf :=
    allocCallPreserved_of_step (by assumption) (by simp [AllocCallPreserved, wp_norm, arm64_norm])
  have hevs : FreeOnlyEvs w := by assumption
  have ⟨_, _, _, _, _, _, _⟩ := hacp
  have hsp_sf' : sf.sp = s0.sp - 2400#64 := hsp_sf.trans (by simp [wp_norm, arm64_norm, hsp1])
  apply SepWP.done hpc_sf hrun_sf
  refine ⟨w, hevs, ?_, hacp, by simp [wp_norm, arm64_norm, hsp_sf', *]⟩
  have hst := v7_stackAt_dropStack32_to_encoderFromPbStack (s0.sp - 2400#64)
  have hjoin := v7_polyEncoder_1392_join (s0.sp - 2400#64) tag
  have h1400' : (s0.sp - 2400#64) + 1400#64 = s0.sp - 1000#64 := by bv_omega
  have h1784' : (s0.sp - 2400#64) + 1784#64 = s0.sp - 616#64 := by bv_omega
  rw [h7552] at hst; rw [h1392, h1400', h1784'] at hjoin; rw [← hsp_sf, hsp_sf']
  refine Entails.trans (Entails.of_eq (show _ =
    (stackAt (s0.sp - 2400#64) dropStack32 ∗ memRegion (s0.sp - 7552#64) 1024) ∗
    ((((s0.sp - 1008#64) ↦₆₄ tag) ∗ memRegion (s0.sp - 1000#64) 384 ∗
      memRegion (s0.sp - 616#64) 8) ∗
     (A.pool lim (M.stepEvents w st) sf ∗ Frame)) by sep_ac_rfl)) ?_
  exact Entails.trans (sepConj_mono hst (sepConj_mono_left hjoin)) (Entails.of_eq (by sep_ac_rfl))

/-- Deallocate `c1/p1` at `+10568 -> +10588` (`ldr x0, [sp, #0xc8]; ldr x1, [sp, #0x18]; cbz x1, +10588; ...`). -/
theorem v7_dealloc_c1_10568_to_10588
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext)
    (s0 s1 : State) (out c1 p1 c2 : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10568#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx24_1 : s1.readReg64 .x24 = c2)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10588#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗ (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
        vecCapPtrDealloc A.repAlloc c1 p1 ∗ A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗ (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        AllocCallPreserved s1 sm ∧ sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧ sm.readReg64 .x24 = c2 ∧ TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  rcases htr1 with ⟨htr_1, hvregs_1⟩
  have hdealloc := v4_sub_ok_dealloc_125316_fo hA
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpecBase] at hdealloc
  refine SepWP.weaken_pre
    (sepConj_mono_left (v4_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
  have h7552 : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
  have h200 : (s0.sp - 2400#64) + 200#64 = s0.sp - 2200#64 := by bv_omega
  have h24 : (s0.sp - 2400#64) + 24#64 = s0.sp - 2376#64 := by bv_omega
  rw [h7552, h200, h24]
  have hst := v4_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
  rw [h7552] at hst
  states_from_pb_fetches_range_b b (Rust.withPanics ext) 10568 20
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, vecCapPtrDealloc,
    LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live,
    BitVec.ofNat_eq_ofNat] at hdealloc hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  by_cases hc1 : (c1 == 0#64) = true
  · simp only [hc1, ↓reduceIte, sepConj_emp, emp_sepConj]
    apply sepWP_evs_nil; simp only [AllocCostModel.stepEvents_nil]; wp_steps
    apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
    exact ⟨by simp only [wp_norm, arm64_norm]; exact Entails.trans (Entails.of_eq (by sep_ac_rfl)) (sepConj_mono_left hst),
      by simp [AllocCallPreserved, wp_norm, arm64_norm, *]⟩
  · have hc1_f : (c1 == 0#64) = false := Bool.eq_false_iff.mpr hc1
    simp only [hc1_f, Bool.false_eq_true, ↓reduceIte]
    apply sepWP_evs_dealloc c1.toNat 1; wp_steps; wp_apply
    have hacp_s : AllocCallPreserved s1 sf :=
      allocCallPreserved_of_step (by assumption) (by simp [AllocCallPreserved, wp_norm, arm64_norm])
    have ⟨_, _, _, _, _, _, _⟩ := hacp_s
    have hsp_sf' : sf.sp = s0.sp - 2400#64 := hsp_sf.trans (by simp [wp_norm, arm64_norm, hsp1])
    apply SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
    refine ⟨?_, hacp_s, by simp [wp_norm, arm64_norm, hsp_sf', *]⟩
    rw [← hsp_sf, hsp_sf']
    refine Entails.trans (Entails.of_eq (show _ =
      (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
      (((s0.sp - 2200#64) ↦₆₄ p1) ∗ ((s0.sp - 2376#64) ↦₆₄ c1) ∗
       A.pool lim (M.stepEvents (rustDeallocEvents c1.toNat 1) st) sf ∗ Frame) by sep_ac_rfl)) ?_
    exact sepConj_mono_left hst

/-- Deallocate the 4 `Vec<u8>` buffers `c2/p2 .. c5/p5` at `+10588 -> +11112` (`0x5ca00 -> 0x5cc0c`). -/
theorem v7_dealloc_4vecs_10588_to_11112
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext)
    (s0 s1 : State) (out c2 p2 c3 p3 c4 p4 c5 p5 : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10588#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx24_1 : s1.readReg64 .x24 = c2)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 11112#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
        vecCapPtrDealloc A.repAlloc c2 p2 ∗ vecCapPtrDealloc A.repAlloc c3 p3 ∗
        vecCapPtrDealloc A.repAlloc c4 p4 ∗ vecCapPtrDealloc A.repAlloc c5 p5 ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        AllocCallPreserved s1 sm ∧ sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧ TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hdealloc := v4_sub_ok_dealloc_125316_fo hA
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpecBase] at hdealloc
  refine SepWP.weaken_pre
    (sepConj_mono_left (v4_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
  unfold v7_ct1SentSpillCells CryptoVerification.SpqrV1.States.FromPb.v7_ct1SentSpillCells
  have h7552 : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
  have h1296 : (s0.sp - 2400#64) + 1296#64 = s0.sp - 1104#64 := by bv_omega
  have h1312 : (s0.sp - 2400#64) + 1312#64 = s0.sp - 1088#64 := by bv_omega
  have h1320 : (s0.sp - 2400#64) + 1320#64 = s0.sp - 1080#64 := by bv_omega
  have h1336 : (s0.sp - 2400#64) + 1336#64 = s0.sp - 1064#64 := by bv_omega
  have h1344 : (s0.sp - 2400#64) + 1344#64 = s0.sp - 1056#64 := by bv_omega
  have h1360 : (s0.sp - 2400#64) + 1360#64 = s0.sp - 1040#64 := by bv_omega
  have h1368 : (s0.sp - 2400#64) + 1368#64 = s0.sp - 1032#64 := by bv_omega
  have hst := v4_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
  rw [h7552] at hst; rw [h7552, h1296, h1312, h1320, h1336, h1344, h1360, h1368]
  states_from_pb_fetches_range_b b (Rust.withPanics ext) 10588 84
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, vecCapPtrDealloc,
    LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live,
    BitVec.ofNat_eq_ofNat] at hdealloc hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  let P_post : M.σ → State → SepProp := fun stf sm =>
    stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      (((s0.sp - 1104#64) ↦₆₄ p2) ∗ ((s0.sp - 1088#64) ↦₆₄ c3) ∗ ((s0.sp - 1080#64) ↦₆₄ p3) ∗
       ((s0.sp - 1064#64) ↦₆₄ c4) ∗ ((s0.sp - 1056#64) ↦₆₄ p4) ∗ ((s0.sp - 1040#64) ↦₆₄ c5) ∗
       ((s0.sp - 1032#64) ↦₆₄ p5)) ∗
      A.pool lim stf sm ∗ Frame
  refine seq_acp_evs st (mid := entry + 10608#64)
    (fun st1 sm =>
      (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
      (((s0.sp - 1104#64) ↦₆₄ p2) ∗ ((s0.sp - 1088#64) ↦₆₄ c3) ∗ ((s0.sp - 1080#64) ↦₆₄ p3) ∗
       ((s0.sp - 1064#64) ↦₆₄ c4) ∗ ((s0.sp - 1056#64) ↦₆₄ p4) ∗ ((s0.sp - 1040#64) ↦₆₄ c5) ∗
       ((s0.sp - 1032#64) ↦₆₄ p5)) ∗
      (if (c3 == 0#64) = true then emp else A.live p3 c3.toNat 1 ∗ memRegion p3 c3.toNat) ∗
      (if (c4 == 0#64) = true then emp else A.live p4 c4.toNat 1 ∗ memRegion p4 c4.toNat) ∗
      (if (c5 == 0#64) = true then emp else A.live p5 c5.toNat 1 ∗ memRegion p5 c5.toNat) ∗
      A.pool lim st1 sm ∗ Frame)
    P_post
    (fun sm => sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧ TraceCalleeSaved sm s0)
    ?_ ?_
  · rcases htr1 with ⟨htr_1, hvregs_1⟩
    by_cases hc2 : (c2 == 0#64) = true
    · simp only [hc2, ↓reduceIte, sepConj_emp, emp_sepConj]
      apply sepWP_evs_nil; simp only [AllocCostModel.stepEvents_nil]; wp_steps
      apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
      exact ⟨by simp only [wp_norm, arm64_norm]; exact Entails.of_eq (by sep_ac_rfl),
        by simp [AllocCallPreserved, wp_norm, arm64_norm, *]⟩
    · have hc2_f : (c2 == 0#64) = false := Bool.eq_false_iff.mpr hc2
      simp only [hc2_f, Bool.false_eq_true, ↓reduceIte]
      apply sepWP_evs_dealloc c2.toNat 1; wp_steps; wp_apply
      have hacp_s : AllocCallPreserved s1 sf :=
        allocCallPreserved_of_step (by assumption) (by simp [AllocCallPreserved, wp_norm, arm64_norm])
      have ⟨_, _, _, _, _, _, _⟩ := hacp_s
      have hsp_sf' : sf.sp = s0.sp - 2400#64 := hsp_sf.trans (by simp [wp_norm, arm64_norm, hsp1])
      apply SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
      refine ⟨?_, hacp_s, by simp [wp_norm, arm64_norm, hsp_sf', *]⟩
      rw [← hsp_sf, hsp_sf']; exact Entails.of_eq (by sep_ac_rfl)
  intro st2 s2 hpc2 hrun2 ⟨hsp2, hx19_2, htr2⟩
  refine seq_acp_evs st2 (mid := entry + 10628#64)
    (fun st3 sm =>
      (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
      (((s0.sp - 1104#64) ↦₆₄ p2) ∗ ((s0.sp - 1088#64) ↦₆₄ c3) ∗ ((s0.sp - 1080#64) ↦₆₄ p3) ∗
       ((s0.sp - 1064#64) ↦₆₄ c4) ∗ ((s0.sp - 1056#64) ↦₆₄ p4) ∗ ((s0.sp - 1040#64) ↦₆₄ c5) ∗
       ((s0.sp - 1032#64) ↦₆₄ p5)) ∗
      (if (c4 == 0#64) = true then emp else A.live p4 c4.toNat 1 ∗ memRegion p4 c4.toNat) ∗
      (if (c5 == 0#64) = true then emp else A.live p5 c5.toNat 1 ∗ memRegion p5 c5.toNat) ∗
      A.pool lim st3 sm ∗ Frame)
    P_post
    (fun sm => sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧ TraceCalleeSaved sm s0)
    ?_ ?_
  · rcases htr2 with ⟨htr_2, hvregs_2⟩
    by_cases hc3 : (c3 == 0#64) = true
    · simp only [hc3, ↓reduceIte, sepConj_emp, emp_sepConj]
      apply sepWP_evs_nil; simp only [AllocCostModel.stepEvents_nil]; wp_steps
      apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun2])
      exact ⟨by simp only [wp_norm, arm64_norm]; exact Entails.of_eq (by sep_ac_rfl),
        by simp [AllocCallPreserved, wp_norm, arm64_norm, *]⟩
    · have hc3_f : (c3 == 0#64) = false := Bool.eq_false_iff.mpr hc3
      simp only [hc3_f, Bool.false_eq_true, ↓reduceIte]
      apply sepWP_evs_dealloc c3.toNat 1; wp_steps; wp_apply
      have hacp_s : AllocCallPreserved s2 sf :=
        allocCallPreserved_of_step (by assumption) (by simp [AllocCallPreserved, wp_norm, arm64_norm])
      have ⟨_, _, _, _, _, _, _⟩ := hacp_s
      have hsp_sf' : sf.sp = s0.sp - 2400#64 := hsp_sf.trans (by simp [wp_norm, arm64_norm, hsp2])
      apply SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
      refine ⟨?_, hacp_s, by simp [wp_norm, arm64_norm, hsp_sf', *]⟩
      rw [← hsp_sf, hsp_sf']; exact Entails.of_eq (by sep_ac_rfl)
  intro st3 s3 hpc3 hrun3 ⟨hsp3, hx19_3, htr3⟩
  refine seq_acp_evs st3 (mid := entry + 10648#64)
    (fun st4 sm =>
      (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
      (((s0.sp - 1104#64) ↦₆₄ p2) ∗ ((s0.sp - 1088#64) ↦₆₄ c3) ∗ ((s0.sp - 1080#64) ↦₆₄ p3) ∗
       ((s0.sp - 1064#64) ↦₆₄ c4) ∗ ((s0.sp - 1056#64) ↦₆₄ p4) ∗ ((s0.sp - 1040#64) ↦₆₄ c5) ∗
       ((s0.sp - 1032#64) ↦₆₄ p5)) ∗
      (if (c5 == 0#64) = true then emp else A.live p5 c5.toNat 1 ∗ memRegion p5 c5.toNat) ∗
      A.pool lim st4 sm ∗ Frame)
    P_post
    (fun sm => sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧ TraceCalleeSaved sm s0)
    ?_ ?_
  · rcases htr3 with ⟨htr_3, hvregs_3⟩
    by_cases hc4 : (c4 == 0#64) = true
    · simp only [hc4, ↓reduceIte, sepConj_emp, emp_sepConj]
      apply sepWP_evs_nil; simp only [AllocCostModel.stepEvents_nil]; wp_steps
      apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun3])
      exact ⟨by simp only [wp_norm, arm64_norm]; exact Entails.of_eq (by sep_ac_rfl),
        by simp [AllocCallPreserved, wp_norm, arm64_norm, *]⟩
    · have hc4_f : (c4 == 0#64) = false := Bool.eq_false_iff.mpr hc4
      simp only [hc4_f, Bool.false_eq_true, ↓reduceIte]
      apply sepWP_evs_dealloc c4.toNat 1; wp_steps; wp_apply
      have hacp_s : AllocCallPreserved s3 sf :=
        allocCallPreserved_of_step (by assumption) (by simp [AllocCallPreserved, wp_norm, arm64_norm])
      have ⟨_, _, _, _, _, _, _⟩ := hacp_s
      have hsp_sf' : sf.sp = s0.sp - 2400#64 := hsp_sf.trans (by simp [wp_norm, arm64_norm, hsp3])
      apply SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
      refine ⟨?_, hacp_s, by simp [wp_norm, arm64_norm, hsp_sf', *]⟩
      rw [← hsp_sf, hsp_sf']; exact Entails.of_eq (by sep_ac_rfl)
  intro st4 s4 hpc4 hrun4 ⟨hsp4, hx19_4, htr4⟩
  rcases htr4 with ⟨htr_4, hvregs_4⟩
  by_cases hc5 : (c5 == 0#64) = true
  · simp only [hc5, ↓reduceIte, sepConj_emp, emp_sepConj]
    apply sepWP_evs_nil; simp only [AllocCostModel.stepEvents_nil]; wp_steps
    apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun4])
    exact ⟨by dsimp only [P_post]; simp only [wp_norm, arm64_norm]; exact Entails.trans (Entails.of_eq (by sep_ac_rfl)) (sepConj_mono_left hst),
      by simp [AllocCallPreserved, wp_norm, arm64_norm, *]⟩
  · have hc5_f : (c5 == 0#64) = false := Bool.eq_false_iff.mpr hc5
    simp only [hc5_f, Bool.false_eq_true, ↓reduceIte]
    apply sepWP_evs_dealloc c5.toNat 1; wp_steps; wp_apply
    have hacp_s : AllocCallPreserved s4 sf :=
      allocCallPreserved_of_step (by assumption) (by simp [AllocCallPreserved, wp_norm, arm64_norm])
    have ⟨_, _, _, _, _, _, _⟩ := hacp_s
    have hsp_sf' : sf.sp = s0.sp - 2400#64 := hsp_sf.trans (by simp [wp_norm, arm64_norm, hsp4])
    wp_steps
    apply SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, hrun_sf])
    refine ⟨?_, hacp_s.trans (by simp [AllocCallPreserved, wp_norm, arm64_norm]),
      by simp [wp_norm, arm64_norm, hsp_sf', *]⟩
    dsimp only [P_post]; simp only [wp_norm, arm64_norm]; rw [← hsp_sf, hsp_sf']
    refine Entails.trans (Entails.of_eq (show _ =
      (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
      ((((s0.sp - 1104#64) ↦₆₄ p2) ∗ ((s0.sp - 1088#64) ↦₆₄ c3) ∗ ((s0.sp - 1080#64) ↦₆₄ p3) ∗
        ((s0.sp - 1064#64) ↦₆₄ c4) ∗ ((s0.sp - 1056#64) ↦₆₄ p4) ∗ ((s0.sp - 1040#64) ↦₆₄ c5) ∗
        ((s0.sp - 1032#64) ↦₆₄ p5)) ∗
       A.pool lim (M.stepEvents (rustDeallocEvents c5.toNat 1) st4) sf ∗ Frame) by sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hst) (Entails.of_eq (by sep_ac_rfl))

/-- Cleanup at `+10556 -> +4632` (`0x5c9e0`, when `s.receivingEk = none`):
drops `enc` at `fsp + 1392..1792`, deallocates `c1/p1 .. c5/p5`, sets `x28 = 0#64` at `+11112`,
and branches to `+4632`. -/
theorem v7_cleanup_10556
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext)
    (s0 s1 : State) (out c1 p1 c2 p2 c3 p3 c4 p4 c5 p5 : BitVec 64)
    (enc : PolyEncoder) (st : M.σ) (Frame : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10556#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx24_1 : s1.readReg64 .x24 = c2)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        polyEncoderAt A.repAlloc ((s0.sp - 2400#64) + 1392#64) enc ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗ (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
        v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
        vecCapPtrDealloc A.repAlloc c1 p1 ∗ vecCapPtrDealloc A.repAlloc c2 p2 ∗
        vecCapPtrDealloc A.repAlloc c3 p3 ∗ vecCapPtrDealloc A.repAlloc c4 p4 ∗
        vecCapPtrDealloc A.repAlloc c5 p5 ∗ A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗
          (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗ (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
          v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        AllocCallPreserved s1 sm ∧ sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧ sm.readReg64 .x28 = 0#64 ∧ TraceCalleeSaved sm s0) := by
  let P_post : M.σ → State → SepProp := fun stf sm =>
    stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗
      (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗ (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
      v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
      A.pool lim stf sm ∗ Frame
  refine seq_acp_evs st
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10568#64)
    (fun st1 sm =>
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗ A.pool lim st1 sm ∗
      ((((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗ (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
       v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
       vecCapPtrDealloc A.repAlloc c1 p1 ∗ vecCapPtrDealloc A.repAlloc c2 p2 ∗
       vecCapPtrDealloc A.repAlloc c3 p3 ∗ vecCapPtrDealloc A.repAlloc c4 p4 ∗
       vecCapPtrDealloc A.repAlloc c5 p5 ∗ Frame))
    P_post
    (fun sm => sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
      sm.readReg64 .x24 = c2 ∧ TraceCalleeSaved sm s0) ?_ ?_
  · exact SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (v7_drop_poly16_10556_to_10568 hA s0 s1 out c2 enc st
        ((((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗ (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
         v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
         vecCapPtrDealloc A.repAlloc c1 p1 ∗ vecCapPtrDealloc A.repAlloc c2 p2 ∗
         vecCapPtrDealloc A.repAlloc c3 p3 ∗ vecCapPtrDealloc A.repAlloc c4 p4 ∗
         vecCapPtrDealloc A.repAlloc c5 p5 ∗ Frame)
        hsp0_align hpc1 hrun1 hsp1 hx19_1 hx24_1 htr1)
  · intro st1 s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx24_2, htr2⟩
    refine seq_acp_evs st1
      (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10588#64)
      (fun st2 sm =>
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗ (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
        A.pool lim st2 sm ∗
        (v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
         vecCapPtrDealloc A.repAlloc c2 p2 ∗ vecCapPtrDealloc A.repAlloc c3 p3 ∗
         vecCapPtrDealloc A.repAlloc c4 p4 ∗ vecCapPtrDealloc A.repAlloc c5 p5 ∗
         memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗ Frame))
      P_post
      (fun sm => sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x24 = c2 ∧ TraceCalleeSaved sm s0) ?_ ?_
    · exact SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (v7_dealloc_c1_10568_to_10588 hA s0 s2 out c1 p1 c2 st1
          (v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
           vecCapPtrDealloc A.repAlloc c2 p2 ∗ vecCapPtrDealloc A.repAlloc c3 p3 ∗
           vecCapPtrDealloc A.repAlloc c4 p4 ∗ vecCapPtrDealloc A.repAlloc c5 p5 ∗
           memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗ Frame)
          hsp0_align hpc2 hrun2 hsp2 hx19_2 hx24_2 htr2)
    · intro st2 s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx24_3, htr3⟩
      refine seq_clean_evs
        (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 11112#64)
        (P_evs := fun evs3 sm =>
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
          A.pool lim (M.stepEvents evs3 st2) sm ∗
          ((((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗ (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
           memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗ Frame))
        (Q := fun sm => AllocCallPreserved s3 sm ∧ sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧ TraceCalleeSaved sm s0) ?_ ?_
      · exact SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
          (v7_dealloc_4vecs_10588_to_11112 hA s0 s3 out c2 p2 c3 p3 c4 p4 c5 p5 st2
            ((((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗ (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
             memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗ Frame)
            hsp0_align hpc3 hrun3 hsp3 hx19_3 hx24_3 htr3)
      · intro evs3 s4 hevs3 hpc4 hrun4 ⟨hacp3, hsp4, hx19_4, htr4⟩
        have h11112 := v7_cleanup_11112 s0 s4 out
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗
           (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗ (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
           v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
           A.pool lim (M.stepEvents evs3 st2) s4 ∗ Frame)
          hpc4 hrun4 hsp4 hx19_4 htr4
        refine SepWP.weaken_pre ?_
          (SepWP.mono h11112 fun sm _Pm _ _ ⟨hPm, hvm4, hacp4, hsp_m, hx19_m, hx28_m, htr_m⟩ =>
            ⟨evs3, hevs3, by dsimp only [P_post]; rw [A.pool_of_vmPreserved hvm4]; exact hPm,
              hacp3.trans hacp4, hsp_m, hx19_m, hx28_m, htr_m⟩)
        exact Entails.of_eq (by sep_ac_rfl)

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7cBudget

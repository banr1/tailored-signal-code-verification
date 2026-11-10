/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7aBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7b
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
# Budget-Threaded Variant 7 (`Ct1Sampled`, `+1056`) — Part B

Fixed-offset budget-threaded `Option<ProtoPolynomialDecoder>` and `Option<ProtoPolynomialEncoder>`
cleanup blocks (`+4548`, `+4528`, `+5444`, `+11112`, `+11096 -> +4632`) under `FreeOnlyEvs`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7bBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (libsignalSessionCode)
open CryptoVerification.RustHeap (RustAlloc arrayAt vecU8)
open CryptoVerification.LibsignalSpqrV1 (
  PolyEncoder ProtoPolynomialDecoder ProtoPolynomialEncoder spqrAuthApi
)
open CryptoVerification.LibsignalTripleRatchet (tripleRatchetProgAtExt)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.SpqrV1.Drop (
  cap_add_one_beq_zero_false dropGluePoly16Stack dropStack32 dropStack48
  optProtoPolyDecoder_none_entails_memRegion_40 optProtoPolyEncoder_none_entails_memRegion_56
  optProtoPolynomialEncoderAt_none' optProtoPolynomialEncoderAt_some'
  protoPolyDecoderTail_entails_memRegion_16 protoPolynomialEncoderAt_expose_cap
  protoPolynomialEncoderAt_unexpose_cap protoPolynomialEncoderRestAt
  unchunkedCt1SentAt unchunkedCt1SentSize
)
open CryptoVerification.SpqrV1.Poly (
  boolByte optProtoPolynomialEncoderAt polyEncoderAt polyEncoderSize
  protoPolynomialDecoderIsCompleteOff protoPolynomialDecoderPadOff protoPolynomialDecoderPadSize
  protoPolynomialDecoderPolysOff protoPolynomialDecoderPtsNeededOff
  protoPolynomialEncoderAt protoPolynomialEncoderSize
)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack)
open CryptoVerification.SpqrV1.Unchunked (
  extractLsb'_0_64_append extractLsb'_64_64_append
)
open CryptoVerification.SpqrV1.Layout.Stubs (
  fnOff_drop_ct1_sent_local2 fnOff_drop_poly_encoder_local2 fnOff_drop_proto_poly_encoder
  stubOff_handle_error stubOff_memcpy stubOff_rust_alloc stubOff_rust_dealloc
  stubOff_rust_no_alloc_shim
)
open CryptoVerification.SpqrV1.States.FromPb (
  TraceCalleeSaved statesFromPbName statesFromPb_fnOff
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel BudgetLimits FreeOnlyEvs RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (trapHooks)
open LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4KBudget (AllocContracts4K)
open LibsignalBinary.Proofs.SpqrV1.Drop.PolyEncoderBudget (dropGluePolyEncoderSpec dropGluePolyEncoderSpecBase)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget (dropProtoPolyEncoderSpec dropProtoPolyEncoderSpecBase)
open LibsignalBinary.Proofs.SpqrV1.Drop.UnchunkedBudget (dropUnchunkedCt1SentSpecBase)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hscBudgetAux (
  allocCallPreserved_of_step fnAddr_rebase_hooks_eq sepWP_evs_nil seq_clean_evs seq_clean_st
)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4Budget (v4_ptsCap_add_one_ne_zero)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7aBudget (
  v7_proto_decoder_dealloc_4556 v7_sub_ok_drop_poly_encoder_local2
  v7_sub_ok_drop_proto_poly_encoder v7_sub_ok_drop_unchunked_ct1_sent_local2
)
open scoped CryptoVerification.CodeLayout
open scoped LibsignalBinary.Proofs.SpqrV1.States.FromPb.EpilogueBudget

/-! ## Re-exports of Pure Decomposition & Stack-Split Helpers from `Variant7b` -/

abbrev v7_optDecoderCapProp := CryptoVerification.SpqrV1.States.FromPb.v7_optDecoderCapProp
abbrev v7_optProtoPolyDecoderTail := CryptoVerification.SpqrV1.States.FromPb.v7_optProtoPolyDecoderTail

alias v7_optProtoPolyDecoder_expose_cap :=
  CryptoVerification.SpqrV1.States.FromPb.v7_optProtoPolyDecoder_expose_cap
alias v7_optProtoPolyDecoder_unexpose_some :=
  CryptoVerification.SpqrV1.States.FromPb.v7_optProtoPolyDecoder_unexpose_some
alias v7_cleanup_opt_decoder_some_pre :=
  CryptoVerification.SpqrV1.States.FromPb.v7_cleanup_opt_decoder_some_pre
alias v7_expose_some_protoPolyEncoder_pre :=
  CryptoVerification.SpqrV1.States.FromPb.v7_expose_some_protoPolyEncoder_pre
alias v7_stackAt_encoderFromPbStack_to_dropStack48 :=
  CryptoVerification.SpqrV1.States.FromPb.v7_stackAt_encoderFromPbStack_to_dropStack48
alias v7_stackAt_dropStack48_to_encoderFromPbStack :=
  CryptoVerification.SpqrV1.States.FromPb.v7_stackAt_dropStack48_to_encoderFromPbStack
alias v7_stackAt_encoderFromPbStack_to_dropStack32 :=
  CryptoVerification.SpqrV1.States.FromPb.v7_stackAt_encoderFromPbStack_to_dropStack32
alias v7_stackAt_dropStack32_to_encoderFromPbStack :=
  CryptoVerification.SpqrV1.States.FromPb.v7_stackAt_dropStack32_to_encoderFromPbStack

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  statesFromPb_fnOff
  fnOff_drop_proto_poly_encoder fnOff_drop_poly_encoder_local2 fnOff_drop_ct1_sent_local2
  stubOff_rust_no_alloc_shim stubOff_rust_alloc stubOff_rust_dealloc
  stubOff_memcpy stubOff_handle_error TraceCalleeSaved

/-! ## 1. `Option<ProtoPolynomialDecoder>` Decomposition & Cleanup at `+4548`, `+4528`, `+5444` -/

theorem v7_cleanup_opt_decoder_some_pre_pool (A : RustAlloc) (fsp pbA cap_dec : BitVec 64)
    (pb : ProtoPolynomialDecoder) (Pool Frame : SepProp) :
    stackAt fsp encoderFromPbStack ∗
      (((pbA + 184#64) ↦₆₄ cap_dec) ∗
       v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec (some pb)) ∗
      Pool ∗ Frame ⊢
    ∃∗ ptsPtr : BitVec 64,
      ⌜pb.pts.length ≤ cap_dec.toNat ∧ cap_dec.toNat * 24 < 2 ^ 63 ∧ ptsPtr ≠ 0⌝ ∗
      (stackAt fsp encoderFromPbStack ∗
       (((pbA + 184#64) ↦₆₄ cap_dec) ∗
        ((pbA + 192#64) ↦₆₄ ptsPtr) ∗
        ((pbA + 200#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
        (if cap_dec = 0 then emp
         else A.live ptsPtr (cap_dec.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
           memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24))
             ((cap_dec.toNat - pb.pts.length) * 24)) ∗
        memRegion (pbA + 208#64) 16) ∗
       Pool ∗ Frame) := by
  unfold v7_optProtoPolyDecoderTail CryptoVerification.SpqrV1.States.FromPb.v7_optProtoPolyDecoderTail
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro ptsPtr
  refine Entails.sepExists_right ptsPtr ?_
  have htl := protoPolyDecoderTail_entails_memRegion_16 (pbA + 184#64)
    pb.ptsNeeded pb.polys pb.isComplete
  have h192 : (pbA + 184#64) + 8#64 = pbA + 192#64 := by bv_omega
  have h200 : (pbA + 184#64) + 16#64 = pbA + 200#64 := by bv_omega
  have h208 : (pbA + 184#64) + 24#64 = pbA + 208#64 := by bv_omega
  rw [h208] at htl
  rw [h192, h200]
  refine Entails.trans
    (Entails.of_eq (show _ =
      ⌜pb.pts.length ≤ cap_dec.toNat ∧ cap_dec.toNat * 24 < 2 ^ 63 ∧ ptsPtr ≠ 0⌝ ∗
      (((((pbA + 184#64) + protoPolynomialDecoderPtsNeededOff) ↦₃₂ pb.ptsNeeded) ∗
        (((pbA + 184#64) + protoPolynomialDecoderPolysOff) ↦₃₂ pb.polys) ∗
        (((pbA + 184#64) + protoPolynomialDecoderIsCompleteOff) ↦₈ boolByte pb.isComplete) ∗
        memRegion ((pbA + 184#64) + protoPolynomialDecoderPadOff) protoPolynomialDecoderPadSize) ∗
       (stackAt fsp encoderFromPbStack ∗
        ((pbA + 184#64) ↦₆₄ cap_dec) ∗
        ((pbA + 192#64) ↦₆₄ ptsPtr) ∗
        ((pbA + 200#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
        (if cap_dec = 0 then emp
         else A.live ptsPtr (cap_dec.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
           memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24))
             ((cap_dec.toNat - pb.pts.length) * 24)) ∗
        Pool ∗ Frame)) by sep_ac_rfl)) ?_
  apply Entails.pure_left; intro hp
  refine Entails.pure_right hp ?_
  exact Entails.trans (sepConj_mono_left htl) (Entails.of_eq (by sep_ac_rfl))

/-- Budget-threaded cleanup of `Option<ProtoPolynomialDecoder>` at `+4548` (`0x5b268 -> +4632`):
given `x22 = cap_dec`, `x27 = pbA`, and `(pbA + 184#64 ↦₆₄ cap_dec) ∗ v7_optProtoPolyDecoderTail`,
deallocates `optDec` if `some` and reaches `+4632` with `memRegion (pbA + 184#64) 40` and `FreeOnlyEvs`. -/
theorem v7_cleanup_opt_decoder_4548
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext)
    (s0 s1 : State) (out pbA cap_dec x28_val : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder) (st : M.σ) (Frame : SepProp)
    (hcap_dec : v7_optDecoderCapProp cap_dec optDec)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4548#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = x28_val)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗
        A.pool lim st s1 ∗
        Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (pbA + 184#64) 40 ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          Frame) ∧
        AllocCallPreserved s1 sm ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = x28_val ∧
        TraceCalleeSaved sm s0) := by
  rcases htr1 with ⟨htr_1, hvregs_1⟩
  cases optDec with
  | none =>
    unfold v7_optDecoderCapProp CryptoVerification.SpqrV1.States.FromPb.v7_optDecoderCapProp at hcap_dec
    subst hcap_dec
    unfold v7_optProtoPolyDecoderTail CryptoVerification.SpqrV1.States.FromPb.v7_optProtoPolyDecoderTail
    states_from_pb_fetches_range_b b (Rust.withPanics ext) 4548 8
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, noneCap, BitVec.ofNat_eq_ofNat] at hpc1 hx22_1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    apply sepWP_evs_nil
    simp only [AllocCostModel.stepEvents_nil]
    wp_steps
    apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
    refine ⟨?_, by simp [AllocCallPreserved, wp_norm, arm64_norm, *]⟩
    simp only [wp_norm, arm64_norm]
    have hm := optProtoPolyDecoder_none_entails_memRegion_40 (pbA + 184#64)
    dsimp only [noneCap] at hm
    refine Entails.trans
      (Entails.of_eq (show _ =
        (((pbA + 184#64) ↦₆₄ 18446744073709551615#64) ∗
         memRegion ((pbA + 184#64) + 8#64) 32) ∗
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
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         ((pbA + 192#64) ↦₆₄ ptsPtr) ∗
         ((pbA + 200#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
         (if cap_dec = 0 then emp
          else A.live ptsPtr (cap_dec.toNat * 24) 8 ∗
            arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pb.pts ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24))
              ((cap_dec.toNat - pb.pts.length) * 24)) ∗
         memRegion (pbA + 208#64) 16) ∗
        A.pool lim st sm ∗
        Frame)
      (Q := fun sm =>
        AllocCallPreserved s1 sm ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = x28_val ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · have hne := v4_ptsCap_add_one_ne_zero hpts_cap_lt
      states_from_pb_fetches_range_b b (Rust.withPanics ext) 4548 8
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      wp_steps
      apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
      refine ⟨?_, by simp [AllocCallPreserved, wp_norm, arm64_norm, *]⟩
      simp only [wp_norm, arm64_norm]
      exact Entails.of_eq (by sep_ac_rfl)
    · intro s2 hpc2 hrun2 ⟨hacp1, hsp2, hx19_2, hx22_2, hx27_2, hx28_2, htr2⟩
      have h4556 := v7_proto_decoder_dealloc_4556 hA s0 s2 out pbA cap_dec ptsPtr x28_val pb.pts st Frame
        hsp0_align hpts_le hpts_cap_lt hpc2 hrun2 hsp2 hx19_2 hx22_2 hx27_2 hx28_2 htr2
      exact SepWP.mono h4556 fun sm _Pm _ _ ⟨evs, hevs, hPm, hacp2, hrest⟩ =>
        ⟨evs, hevs, hPm, hacp1.trans hacp2, hrest⟩

/-- Budget-threaded helper for `+4544 -> +4548` (`bl 0x4c500`): calls
`drop_glue::<ProtoPolynomialEncoder>` with `x0 = pbA + 128#64`. -/
theorem v7_call_drop_proto_poly_encoder_4544
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext)
    (s0 s1 : State) (out pbA cap_dec x28_val : BitVec 64)
    (enc : ProtoPolynomialEncoder) (st : M.σ) (Frame : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4544#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx0_1 : s1.readReg64 .x0 = pbA + 128#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = x28_val)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4548#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        protoPolynomialEncoderAt A.repAlloc (pbA + 128#64) enc ∗
        A.pool lim st s1 ∗
        Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (pbA + 128#64) 56 ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          Frame) ∧
        AllocCallPreserved s1 sm ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = x28_val ∧
        TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  rcases htr1 with ⟨htr_1, hvregs_1⟩
  have hdrop := v7_sub_ok_drop_proto_poly_encoder hA
  simp only [dropProtoPolyEncoderSpecBase] at hdrop
  refine SepWP.weaken_pre
    (sepConj_mono_left (v7_stackAt_encoderFromPbStack_to_dropStack48 (s0.sp - 2400#64))) ?_
  have h7552 : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
  rw [h7552]
  states_from_pb_fetches_range_b b (Rust.withPanics ext) 4544 4
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, protoPolynomialEncoderSize,
    BitVec.ofNat_eq_ofNat] at hdrop hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  wp_steps
  wp_call hdrop (⟨pbA + 128#64, enc⟩, st)
  have hacp : AllocCallPreserved s1 sf :=
    allocCallPreserved_of_step (by assumption) (by simp [AllocCallPreserved, wp_norm, arm64_norm])
  have hevs : FreeOnlyEvs w := by assumption
  have ⟨_, _, _, _, _, _, _⟩ := hacp
  have hsp_sf' : sf.sp = s0.sp - 2400#64 := hsp_sf.trans (by simp [wp_norm, arm64_norm, hsp1])
  apply SepWP.done hpc_sf hrun_sf
  refine ⟨w, hevs, ?_, hacp, by simp [wp_norm, arm64_norm, hsp_sf', *]⟩
  rw [← hsp_sf, hsp_sf']
  have hst := v7_stackAt_dropStack48_to_encoderFromPbStack (s0.sp - 2400#64)
  rw [h7552] at hst
  refine Entails.trans
    (Entails.of_eq (show _ =
      (stackAt (s0.sp - 2400#64) dropStack48 ∗ memRegion (s0.sp - 7552#64) 1008) ∗
      (memRegion (pbA + 128#64) 56 ∗ A.pool lim (M.stepEvents w st) sf ∗ Frame) by sep_ac_rfl)) ?_
  exact sepConj_mono_left hst

theorem v7_expose_some_protoPolyEncoder_pre_pool (A : RustAlloc) (fsp pbA : BitVec 64)
    (enc : ProtoPolynomialEncoder) (Mid Pool Frame : SepProp) :
    stackAt fsp encoderFromPbStack ∗
      protoPolynomialEncoderAt A (pbA + 128#64) enc ∗
      Mid ∗ Pool ∗ Frame ⊢
    ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
      ⌜cap.toNat < 2 ^ 63⌝ ∗
      (stackAt fsp encoderFromPbStack ∗
       ((pbA + 128#64) ↦₆₄ cap) ∗
       protoPolynomialEncoderRestAt A (pbA + 128#64) cap ptr enc ∗
       Mid ∗ Pool ∗ Frame) := by
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_left (protoPolynomialEncoderAt_expose_cap A (pbA + 128#64) enc))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro cap
  refine Entails.sepExists_right cap ?_
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right ptr ?_
  exact Entails.of_eq (by sep_ac_rfl)

/-- Budget-threaded cleanup at `+4528 -> +4632` (`0x5b254 -> 0x5b2bc`):
drops `optEnc` at `pbA + 128#64` and `optDec` at `pbA + 184#64`, preserving `x28`. -/
theorem v7_cleanup_4528
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext)
    (s0 s1 : State) (out pbA cap_dec x28_val : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder)
    (optDec : Option ProtoPolynomialDecoder)
    (st : M.σ) (Frame : SepProp)
    (hcap_dec : v7_optDecoderCapProp cap_dec optDec)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4528#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = x28_val)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        optProtoPolynomialEncoderAt A.repAlloc (pbA + 128#64) optEnc ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗
        A.pool lim st s1 ∗
        Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (pbA + 128#64) 56 ∗
          memRegion (pbA + 184#64) 40 ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          Frame) ∧
        AllocCallPreserved s1 sm ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = x28_val ∧
        TraceCalleeSaved sm s0) := by
  refine seq_clean_evs
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4548#64)
    (P_evs := fun evs1 sm =>
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      (((pbA + 184#64) ↦₆₄ cap_dec) ∗
       v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗
      A.pool lim (M.stepEvents evs1 st) sm ∗
      (memRegion (pbA + 128#64) 56 ∗ Frame))
    (Q := fun sm =>
      AllocCallPreserved s1 sm ∧
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = cap_dec ∧
      sm.readReg64 .x27 = pbA ∧
      sm.readReg64 .x28 = x28_val ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · rcases htr1 with ⟨htr_1, hvregs_1⟩
    cases optEnc with
    | none =>
      rw [optProtoPolynomialEncoderAt_none']
      states_from_pb_fetches_range_b b (Rust.withPanics ext) 4528 16
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, noneCap, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      apply sepWP_evs_nil
      simp only [AllocCostModel.stepEvents_nil]
      wp_steps
      apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
      refine ⟨?_, by simp [AllocCallPreserved, wp_norm, arm64_norm, *]⟩
      simp only [wp_norm, arm64_norm]
      have hm := optProtoPolyEncoder_none_entails_memRegion_56 (pbA + 128#64)
      dsimp only [noneCap] at hm
      refine Entails.trans
        (Entails.of_eq (show _ =
          (((pbA + 128#64) ↦₆₄ 18446744073709551615#64) ∗
           memRegion ((pbA + 128#64) + 8#64) 48) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           (((pbA + 184#64) ↦₆₄ cap_dec) ∗
            v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗
           A.pool lim st s1 ∗ Frame) by sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left hm) (Entails.of_eq (by sep_ac_rfl))
    | some enc =>
      rw [optProtoPolynomialEncoderAt_some']
      refine SepWP.weaken_pre
        (v7_expose_some_protoPolyEncoder_pre_pool A.repAlloc (s0.sp - 2400#64) pbA enc
          (((pbA + 184#64) ↦₆₄ cap_dec) ∗
           v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec)
          (A.pool lim st s1) Frame) ?_
      apply ProofLib.SepWP.exists_left; intro cap_enc
      apply ProofLib.SepWP.exists_left; intro ptr_enc
      apply ProofLib.SepWP.pure_elim; intro hcap_enc
      refine seq_clean_st
        (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4544#64)
        (P_mid := fun sm =>
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          protoPolynomialEncoderAt A.repAlloc (pbA + 128#64) enc ∗
          A.pool lim st sm ∗
          ((((pbA + 184#64) ↦₆₄ cap_dec) ∗
            v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗ Frame))
        (Q := fun sm =>
          AllocCallPreserved s1 sm ∧
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x0 = pbA + 128#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x22 = cap_dec ∧
          sm.readReg64 .x27 = pbA ∧
          sm.readReg64 .x28 = x28_val ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · have hne := cap_add_one_beq_zero_false hcap_enc
        states_from_pb_fetches_range_b b (Rust.withPanics ext) 4528 16
        dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
        generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
          "<spqr::v1::chunked::states::States>::from_pb" = entry
        examples_hide_fetches
        wp_steps
        apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
        refine ⟨?_, by simp [AllocCallPreserved, wp_norm, arm64_norm, *]⟩
        simp only [wp_norm, arm64_norm]
        have hunexp := protoPolynomialEncoderAt_unexpose_cap A.repAlloc (pbA + 128#64) cap_enc ptr_enc enc
        refine Entails.trans
          (Entails.of_eq (show _ =
            (((pbA + 128#64) ↦₆₄ cap_enc) ∗
             protoPolynomialEncoderRestAt A.repAlloc (pbA + 128#64) cap_enc ptr_enc enc) ∗
            (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
             A.pool lim st s1 ∗
             ((((pbA + 184#64) ↦₆₄ cap_dec) ∗
               v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗ Frame)) by sep_ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hunexp) (Entails.of_eq (by sep_ac_rfl))
      · intro s2 hpc2 hrun2 ⟨hacp1, hsp2, hx0_2, hx19_2, hx22_2, hx27_2, hx28_2, htr2⟩
        have hcall := v7_call_drop_proto_poly_encoder_4544 hA s0 s2 out pbA cap_dec x28_val enc st
          ((((pbA + 184#64) ↦₆₄ cap_dec) ∗
            v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗ Frame)
          hsp0_align hpc2 hrun2 hsp2 hx0_2 hx19_2 hx22_2 hx27_2 hx28_2 htr2
        refine SepWP.mono hcall fun sf _Pf _ _ ⟨evs1, hevs1, hPf, hacp2, hrest⟩ => ?_
        exact ⟨evs1, hevs1, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)),
          hacp1.trans hacp2, hrest⟩
  · intro evs1 s2 hevs1 hpc2 hrun2 ⟨hacp1, hsp2, hx19_2, hx22_2, hx27_2, hx28_2, htr2⟩
    have h4548 := v7_cleanup_opt_decoder_4548 hA s0 s2 out pbA cap_dec x28_val optDec
      (M.stepEvents evs1 st) (memRegion (pbA + 128#64) 56 ∗ Frame)
      hcap_dec hsp0_align hpc2 hrun2 hsp2 hx19_2 hx22_2 hx27_2 hx28_2 htr2
    refine SepWP.mono h4548 fun sf _Pf _ _ ⟨evs2, hevs2, hPf, hacp2, hrest⟩ => ?_
    refine ⟨evs1 ++ evs2, hevs1.append hevs2, ?_, hacp1.trans hacp2, hrest⟩
    rw [AllocCostModel.stepEvents_append]
    exact Entails.trans hPf (Entails.of_eq (by sep_ac_rfl))

/-- Budget-threaded cleanup at `+5444 -> +4632` (`0x5b5e8 -> 0x5b2bc`):
executes `lsr x23, x28, #8`, drops `optEnc` at `pbA + 128#64` and `optDec` at `pbA + 184#64`,
preserving `x28`. -/
theorem v7_cleanup_5444
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext)
    (s0 s1 : State) (out pbA cap_dec x28_val : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder)
    (optDec : Option ProtoPolynomialDecoder)
    (st : M.σ) (Frame : SepProp)
    (hcap_dec : v7_optDecoderCapProp cap_dec optDec)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5444#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = x28_val)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        optProtoPolynomialEncoderAt A.repAlloc (pbA + 128#64) optEnc ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗
        A.pool lim st s1 ∗
        Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (pbA + 128#64) 56 ∗
          memRegion (pbA + 184#64) 40 ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          Frame) ∧
        AllocCallPreserved s1 sm ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = x28_val ∧
        TraceCalleeSaved sm s0) := by
  refine seq_clean_evs
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4548#64)
    (P_evs := fun evs1 sm =>
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      (((pbA + 184#64) ↦₆₄ cap_dec) ∗
       v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗
      A.pool lim (M.stepEvents evs1 st) sm ∗
      (memRegion (pbA + 128#64) 56 ∗ Frame))
    (Q := fun sm =>
      AllocCallPreserved s1 sm ∧
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = cap_dec ∧
      sm.readReg64 .x27 = pbA ∧
      sm.readReg64 .x28 = x28_val ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · rcases htr1 with ⟨htr_1, hvregs_1⟩
    cases optEnc with
    | none =>
      rw [optProtoPolynomialEncoderAt_none']
      states_from_pb_fetches_range_b b (Rust.withPanics ext) 5444 24
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, noneCap, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      apply sepWP_evs_nil
      simp only [AllocCostModel.stepEvents_nil]
      wp_steps
      apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
      refine ⟨?_, by simp [AllocCallPreserved, wp_norm, arm64_norm, *]⟩
      simp only [wp_norm, arm64_norm]
      have hm := optProtoPolyEncoder_none_entails_memRegion_56 (pbA + 128#64)
      dsimp only [noneCap] at hm
      refine Entails.trans
        (Entails.of_eq (show _ =
          (((pbA + 128#64) ↦₆₄ 18446744073709551615#64) ∗
           memRegion ((pbA + 128#64) + 8#64) 48) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           (((pbA + 184#64) ↦₆₄ cap_dec) ∗
            v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗
           A.pool lim st s1 ∗ Frame) by sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left hm) (Entails.of_eq (by sep_ac_rfl))
    | some enc =>
      rw [optProtoPolynomialEncoderAt_some']
      refine SepWP.weaken_pre
        (v7_expose_some_protoPolyEncoder_pre_pool A.repAlloc (s0.sp - 2400#64) pbA enc
          (((pbA + 184#64) ↦₆₄ cap_dec) ∗
           v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec)
          (A.pool lim st s1) Frame) ?_
      apply ProofLib.SepWP.exists_left; intro cap_enc
      apply ProofLib.SepWP.exists_left; intro ptr_enc
      apply ProofLib.SepWP.pure_elim; intro hcap_enc
      refine seq_clean_st
        (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4544#64)
        (P_mid := fun sm =>
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          protoPolynomialEncoderAt A.repAlloc (pbA + 128#64) enc ∗
          A.pool lim st sm ∗
          ((((pbA + 184#64) ↦₆₄ cap_dec) ∗
            v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗ Frame))
        (Q := fun sm =>
          AllocCallPreserved s1 sm ∧
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x0 = pbA + 128#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x22 = cap_dec ∧
          sm.readReg64 .x27 = pbA ∧
          sm.readReg64 .x28 = x28_val ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · have hne := cap_add_one_beq_zero_false hcap_enc
        states_from_pb_fetches_range_b b (Rust.withPanics ext) 5444 20
        dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
        generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
          "<spqr::v1::chunked::states::States>::from_pb" = entry
        examples_hide_fetches
        wp_steps
        apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
        refine ⟨?_, by simp [AllocCallPreserved, wp_norm, arm64_norm, *]⟩
        simp only [wp_norm, arm64_norm]
        have hunexp := protoPolynomialEncoderAt_unexpose_cap A.repAlloc (pbA + 128#64) cap_enc ptr_enc enc
        refine Entails.trans
          (Entails.of_eq (show _ =
            (((pbA + 128#64) ↦₆₄ cap_enc) ∗
             protoPolynomialEncoderRestAt A.repAlloc (pbA + 128#64) cap_enc ptr_enc enc) ∗
            (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
             A.pool lim st s1 ∗
             ((((pbA + 184#64) ↦₆₄ cap_dec) ∗
               v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗ Frame)) by sep_ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hunexp) (Entails.of_eq (by sep_ac_rfl))
      · intro s2 hpc2 hrun2 ⟨hacp1, hsp2, hx0_2, hx19_2, hx22_2, hx27_2, hx28_2, htr2⟩
        have hcall := v7_call_drop_proto_poly_encoder_4544 hA s0 s2 out pbA cap_dec x28_val enc st
          ((((pbA + 184#64) ↦₆₄ cap_dec) ∗
            v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗ Frame)
          hsp0_align hpc2 hrun2 hsp2 hx0_2 hx19_2 hx22_2 hx27_2 hx28_2 htr2
        refine SepWP.mono hcall fun sf _Pf _ _ ⟨evs1, hevs1, hPf, hacp2, hrest⟩ => ?_
        exact ⟨evs1, hevs1, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)),
          hacp1.trans hacp2, hrest⟩
  · intro evs1 s2 hevs1 hpc2 hrun2 ⟨hacp1, hsp2, hx19_2, hx22_2, hx27_2, hx28_2, htr2⟩
    have h4548 := v7_cleanup_opt_decoder_4548 hA s0 s2 out pbA cap_dec x28_val optDec
      (M.stepEvents evs1 st) (memRegion (pbA + 128#64) 56 ∗ Frame)
      hcap_dec hsp0_align hpc2 hrun2 hsp2 hx19_2 hx22_2 hx27_2 hx28_2 htr2
    refine SepWP.mono h4548 fun sf _Pf _ _ ⟨evs2, hevs2, hPf, hacp2, hrest⟩ => ?_
    refine ⟨evs1 ++ evs2, hevs1.append hevs2, ?_, hacp1.trans hacp2, hrest⟩
    rw [AllocCostModel.stepEvents_append]
    exact Entails.trans hPf (Entails.of_eq (by sep_ac_rfl))

/-! ## 2. Cleanup at `+11112 -> +4632` and `+11096 -> +4632` (`<PolyDecoder>::from_pb = Err`) -/

/-- Step `+11112 -> +4632` (`mov w28, wzr; b +4632`): sets `x28 = 0#64` (`spqrErrorByte .stateDecode`
is `0#8`) and jumps to `+4632`, preserving `VmPreserved` and `AllocCallPreserved`. -/
theorem v7_cleanup_11112
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (Rest : SepProp)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 11112#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4632#64) s1
      Rest
      (fun sm Pm =>
        (Pm ⊢ Rest) ∧
        VmPreserved s1 sm ∧
        AllocCallPreserved s1 sm ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  rcases htr1 with ⟨htr_1, hvregs_1⟩
  have hwp : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext))
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4632#64) s1
      Rest
      (fun sm Pm =>
        VmPreserved s1 sm ∧
        (Pm ⊢ Rest) ∧
        (AllocCallPreserved s1 sm ∧
         sm.sp = s0.sp - 2400#64 ∧
         sm.readReg64 .x19 = out ∧
         sm.readReg64 .x28 = 0#64 ∧
         TraceCalleeSaved sm s0)) := by
    states_from_pb_fetches_range_b b trapHooks 11112 8
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    rw [fnAddr_rebase_hooks_eq libsignalSessionCode b trapHooks (Rust.withPanics ext)] at *
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    by_vm_steps {
      wp_steps
      apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
      refine ⟨by simp [wp_norm, arm64_norm], Entails.refl _,
        by simp [AllocCallPreserved, wp_norm, arm64_norm, *]⟩
    }
  exact SepWP.mono hwp fun _ _ _ _ ⟨hvm, hP, hacp, hsp, hx19, hx28, htr⟩ =>
    ⟨hP, hvm, hacp, hsp, hx19, hx28, htr⟩

/-- Budget-threaded cleanup at `+11096 -> +4632` (`0x5cbfc -> 0x5b2bc`):
drops `polyEncoderAt A.repAlloc (fsp + 1392) enc` (`bl 0x4c5d0`),
drops `unchunkedCt1SentAt A.repAlloc (fsp + 1264) uc` (`bl 0x4c99c`),
sets `x28 = 0#64`, and jumps to `+4632`. -/
theorem v7_cleanup_11096
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext)
    (s0 s1 : State) (out : BitVec 64)
    (enc : PolyEncoder) (uc : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (st : M.σ) (Frame : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 11096#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        polyEncoderAt A.repAlloc ((s0.sp - 2400#64) + 1392#64) enc ∗
        unchunkedCt1SentAt A.repAlloc ((s0.sp - 2400#64) + 1264#64) uc ∗
        A.pool lim st s1 ∗
        Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗
          memRegion ((s0.sp - 2400#64) + 1264#64) 128 ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          Frame) ∧
        AllocCallPreserved s1 sm ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hdrop_enc := v7_sub_ok_drop_poly_encoder_local2 hA
  have hdrop_uc := v7_sub_ok_drop_unchunked_ct1_sent_local2 (F := F) hA
  simp only [dropGluePolyEncoderSpecBase, dropGluePoly16Stack] at hdrop_enc
  simp only [dropUnchunkedCt1SentSpecBase] at hdrop_uc
  refine seq_clean_evs
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 11112#64)
    (P_evs := fun evs1 sm =>
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗
      memRegion ((s0.sp - 2400#64) + 1264#64) 128 ∗
      A.pool lim (M.stepEvents evs1 st) sm ∗
      Frame)
    (Q := fun sm =>
      AllocCallPreserved s1 sm ∧
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · rcases htr1 with ⟨htr_1, hvregs_1⟩
    refine SepWP.weaken_pre
      (sepConj_mono_left (v7_stackAt_encoderFromPbStack_to_dropStack32 (s0.sp - 2400#64))) ?_
    have h1392 : (s0.sp - 2400#64) + 1392#64 = s0.sp - 1008#64 := by bv_omega
    have h1264 : (s0.sp - 2400#64) + 1264#64 = s0.sp - 1136#64 := by bv_omega
    have h7552 : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
    rw [h1392, h1264, h7552]
    states_from_pb_fetches_range_b b (Rust.withPanics ext) 11096 16
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, polyEncoderSize, unchunkedCt1SentSize,
      BitVec.ofNat_eq_ofNat] at hdrop_enc hdrop_uc hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = fnEntry
    examples_hide_fetches
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hdrop_enc hdrop_uc
    refine seq_clean_evs (mid := fnEntry + 11104#64)
      (P_evs := fun evs_a sm =>
        (stackAt (s0.sp - 2400#64) dropStack32 ∗ memRegion (s0.sp - 7552#64) 1024) ∗
        memRegion (s0.sp - 1008#64) 400 ∗
        unchunkedCt1SentAt A.repAlloc (s0.sp - 1136#64) uc ∗
        A.pool lim (M.stepEvents evs_a st) sm ∗
        Frame)
      (Q := fun sm =>
        AllocCallPreserved s1 sm ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · wp_steps
      wp_call hdrop_enc (⟨s0.sp - 1008#64, enc⟩, st)
      have hacp_a : AllocCallPreserved s1 sf :=
        allocCallPreserved_of_step (by assumption) (by simp [AllocCallPreserved, wp_norm, arm64_norm])
      have hevs_a : FreeOnlyEvs w := by assumption
      have ⟨_, _, _, _, _, _, _⟩ := hacp_a
      have hsp_sf' : sf.sp = s0.sp - 2400#64 := hsp_sf.trans (by simp [wp_norm, arm64_norm, hsp1])
      apply SepWP.done hpc_sf hrun_sf
      refine ⟨w, hevs_a, ?_, hacp_a, by simp [wp_norm, arm64_norm, hsp_sf', *]⟩
      rw [← hsp_sf, hsp_sf']
      exact Entails.of_eq (by sep_ac_rfl)
    · intro evs_a s2 hevs_a hpc2 hrun2 ⟨hacp_a, hsp2, hx19_2, ⟨htr_2, hvregs_2⟩⟩
      clear hdrop_enc
      wp_steps
      wp_call hdrop_uc (⟨s0.sp - 1136#64, uc⟩, M.stepEvents evs_a st)
      have hacp_b : AllocCallPreserved s2 sf :=
        allocCallPreserved_of_step (by assumption) (by simp [AllocCallPreserved, wp_norm, arm64_norm])
      have hevs_b : FreeOnlyEvs w := by assumption
      have hacp_ab : AllocCallPreserved s1 sf := hacp_a.trans hacp_b
      have ⟨_, _, _, _, _, _, _⟩ := hacp_ab
      have hsp_sf' : sf.sp = s0.sp - 2400#64 := hsp_sf.trans (by simp [wp_norm, arm64_norm, hsp2])
      apply SepWP.done hpc_sf hrun_sf
      refine ⟨evs_a ++ w, hevs_a.append hevs_b, ?_, hacp_ab, by simp [wp_norm, arm64_norm, hsp_sf', *]⟩
      rw [AllocCostModel.stepEvents_append, ← hsp_sf, hsp_sf']
      have hst := v7_stackAt_dropStack32_to_encoderFromPbStack (s0.sp - 2400#64)
      rw [h7552] at hst
      refine Entails.trans
        (Entails.of_eq (show _ =
          (stackAt (s0.sp - 2400#64) dropStack32 ∗ memRegion (s0.sp - 7552#64) 1024) ∗
          (memRegion (s0.sp - 1008#64) 400 ∗
           memRegion (s0.sp - 1136#64) 128 ∗
           A.pool lim (M.stepEvents w (M.stepEvents evs_a st)) sf ∗ Frame) by sep_ac_rfl)) ?_
      exact sepConj_mono_left hst
  · intro evs1 s2 hevs1 hpc2 hrun2 ⟨hacp1, hsp2, hx19_2, htr2⟩
    have h11112 := v7_cleanup_11112 s0 s2 out
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗
       memRegion ((s0.sp - 2400#64) + 1264#64) 128 ∗
       A.pool lim (M.stepEvents evs1 st) s2 ∗
       Frame)
      hpc2 hrun2 hsp2 hx19_2 htr2
    refine SepWP.mono h11112 fun sm _Pm _ _ ⟨hPm, hvm2, hacp2, hsp_m, hx19_m, hx28_m, htr_m⟩ => ?_
    refine ⟨evs1, hevs1, ?_, hacp1.trans hacp2, hsp_m, hx19_m, hx28_m, htr_m⟩
    rw [A.pool_of_vmPreserved hvm2]
    exact hPm

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7bBudget

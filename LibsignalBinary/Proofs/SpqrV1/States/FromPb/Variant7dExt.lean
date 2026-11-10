/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4K
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7d
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7aExt
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7bExt
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: 4-KiB Hook Companion for `Variant7d`

Lifts `Variant7d.lean`'s `AllocContracts`-parameterized theorems to `AllocContracts4K`
inside `CryptoVerification.SpqrV1.States.FromPb.Ext4K`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.States.FromPb.Ext4K

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.States.FromPb

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  statesFromPb_fnOff
  stubOff_rust_no_alloc_shim
  stubOff_rust_alloc
  stubOff_rust_dealloc
  stubOff_memcpy
  stubOff_handle_error

theorem v7_call_drop_proto_unchunked_ct1_sent_1092
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (s0 s1 : State) (out pbA cap_dec : BitVec 64)
    (u : V1State.Unchunked.Ct1Sent) (Frame : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1092#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx0_1 : s1.readReg64 .x0 = pbA)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1096#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        protoUnchunkedCt1SentEkReceivedAt A pbA (v7_ct1SentToCt1SentEkReceived u) ∗
        A.pool ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion pbA 128 ∗
          A.pool ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x27 = pbA ∧
        TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hdrop := Ext4K.v7_sub_ok_drop_proto_unchunked_ct1_sent_ek_received hA
  simp only [dropProtoUnchunkedCt1SentEkReceivedSpec] at hdrop
  refine SepWP.weaken_pre
    (sepConj_mono_left (v7_stackAt_encoderFromPbStack_to_dropStack32 (s0.sp - 2400#64))) ?_
  states_from_pb_fetches_range b (Rust.withPanics ext) 1092 4
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, protoUnchunkedCt1SentEkReceivedSize,
    BitVec.ofNat_eq_ofNat] at hdrop hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  wp_steps
  wp_apply
  refine EncoderFromPb.align_pre ?_ ?_
  · have hst := v7_stackAt_dropStack32_to_encoderFromPbStack (s0.sp - 2400#64)
    have haddr : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
    rw [haddr] at hst
    nth_rw 1 [← hsp1] at hst
    refine Entails.trans
      (Entails.of_eq (show _ =
        (stackAt s1.sp dropStack32 ∗ memRegion (s0.sp - 7552#64) 1024) ∗
        (memRegion pbA 128 ∗ A.pool ∗ Frame) by ac_rfl)) ?_
    exact sepConj_mono_left hst
  · wp_done

theorem v7_entry_bad_pts_1056_to_4632
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (s0 s1 : State) (out pbA w0 cap_dec : BitVec 64)
    (optUcPb : Option V1State.Unchunked.Ct1Sent)
    (optEncPb : Option PolynomialEncoder)
    (d : PolynomialDecoder) (Frame : SepProp)
    (hcap_uc : v7_optUcCapProp w0 optUcPb)
    (hcap_dec : v7_optDecoderCapProp cap_dec (some (pbToProtoPolyDecoder d)))
    (hpts : (d.ptsNeeded == 576#32) = false)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1056#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx9_1 : s1.readReg64 .x9 = w0)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((pbA ↦₆₄ w0) ∗ v7_optProtoUnchunkedCt1SentTail A pbA w0 optUcPb) ∗
        optProtoPolynomialEncoderAt A (pbA + 128#64) (optEncPb.map pbToProtoPolyEncoder) ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec (some (pbToProtoPolyDecoder d))) ∗
        A.pool ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion pbA 224 ∗
          A.pool ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = 2#64 ∧
        TraceCalleeSaved sm s0) := by
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4528#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      optProtoPolynomialEncoderAt A (pbA + 128#64) (optEncPb.map pbToProtoPolyEncoder) ∗
      (((pbA + 184#64) ↦₆₄ cap_dec) ∗
       v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec (some (pbToProtoPolyDecoder d))) ∗
      A.pool ∗
      (memRegion pbA 128 ∗ Frame))
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = cap_dec ∧
      sm.readReg64 .x27 = pbA ∧
      sm.readReg64 .x28 = 2#64 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · have hne_dec := v4_ptsCap_add_one_ne_zero hcap_dec
    have hpts' : ((pbToProtoPolyDecoder d).ptsNeeded == 576#32) = false := hpts
    have hpts_sub := v7_ptsNeeded_sub_576_beq_zero hpts'
    refine SepWP.weaken_pre
      (Entails.trans
        (Entails.of_eq (show _ =
          v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec (some (pbToProtoPolyDecoder d)) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           ((pbA ↦₆₄ w0) ∗ v7_optProtoUnchunkedCt1SentTail A pbA w0 optUcPb) ∗
           optProtoPolynomialEncoderAt A (pbA + 128#64) (optEncPb.map pbToProtoPolyEncoder) ∗
           ((pbA + 184#64) ↦₆₄ cap_dec) ∗
           A.pool ∗ Frame) by ac_rfl))
        (sepConj_mono_left
          (v7_optProtoPolyDecoderTail_expose_pts A pbA cap_dec (pbToProtoPolyDecoder d)))) ?_
    cases optUcPb with
    | none =>
      unfold v7_optUcCapProp at hcap_uc
      subst hcap_uc
      dsimp only [v7_optProtoUnchunkedCt1SentTail]
      states_from_pb_fetches_range b (Rust.withPanics ext) 1056 48
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, noneCap,
        BitVec.ofNat_eq_ofNat] at hpc1 hx9_1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · have hun_dec := v7_optProtoPolyDecoderTail_unexpose_pts A pbA cap_dec (pbToProtoPolyDecoder d)
        have hun_uc := v7_optProtoUnchunkedCt1Sent_unexpose_none pbA
        dsimp only [noneCap] at hun_uc
        refine Entails.trans
          (Entails.of_eq (show _ =
            (((pbA + 208#64) ↦₃₂ (pbToProtoPolyDecoder d).ptsNeeded) ∗
             v7_optProtoPolyDecoderTailWithoutPts A (pbA + 184#64) cap_dec (pbToProtoPolyDecoder d)) ∗
            ((pbA ↦₆₄ (bv% (2 ^ 64 - 1))) ∗ memRegion (pbA + 8#64) 120) ∗
            (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
             optProtoPolynomialEncoderAt A (pbA + 128#64) (optEncPb.map pbToProtoPolyEncoder) ∗
             ((pbA + 184#64) ↦₆₄ cap_dec) ∗
             A.pool ∗ Frame) by ac_rfl)) ?_
        exact Entails.trans
          (sepConj_mono hun_dec (sepConj_mono_left hun_uc))
          (Entails.of_eq (by ac_rfl))
      · wp_done
    | some u =>
      unfold v7_optUcCapProp at hcap_uc
      have hne_uc := cap_add_one_beq_zero_false hcap_uc
      refine EncoderFromPb.seq_clean
        (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1092#64)
        (P_mid :=
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          protoUnchunkedCt1SentEkReceivedAt A pbA (v7_ct1SentToCt1SentEkReceived u) ∗
          A.pool ∗
          (optProtoPolynomialEncoderAt A (pbA + 128#64) (optEncPb.map pbToProtoPolyEncoder) ∗
           (((pbA + 184#64) ↦₆₄ cap_dec) ∗
            v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec (some (pbToProtoPolyDecoder d))) ∗
           Frame))
        (Q := fun sm =>
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x0 = pbA ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x22 = cap_dec ∧
          sm.readReg64 .x27 = pbA ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · states_from_pb_fetches_range b (Rust.withPanics ext) 1056 36
        dsimp only [tripleRatchetProgAtExt, statesFromPbName,
          BitVec.ofNat_eq_ofNat] at hpc1 ⊢
        generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
          "<spqr::v1::chunked::states::States>::from_pb" = entry
        examples_hide_fetches
        wp_steps
        refine EncoderFromPb.align_pre ?_ ?_
        · have hun_dec := v7_optProtoPolyDecoderTail_unexpose_pts A pbA cap_dec (pbToProtoPolyDecoder d)
          have hun_uc := v7_optProtoUnchunkedCt1Sent_unexpose_some A pbA w0 u
          rw [v7_protoUnchunkedCt1SentAt_eq] at hun_uc
          refine Entails.trans
            (Entails.of_eq (show _ =
              (((pbA + 208#64) ↦₃₂ (pbToProtoPolyDecoder d).ptsNeeded) ∗
               v7_optProtoPolyDecoderTailWithoutPts A (pbA + 184#64) cap_dec (pbToProtoPolyDecoder d)) ∗
              ((pbA ↦₆₄ w0) ∗ v7_optProtoUnchunkedCt1SentTail A pbA w0 (some u)) ∗
              (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
               A.pool ∗
               optProtoPolynomialEncoderAt A (pbA + 128#64) (optEncPb.map pbToProtoPolyEncoder) ∗
               ((pbA + 184#64) ↦₆₄ cap_dec) ∗
               Frame) by ac_rfl)) ?_
          exact Entails.trans
            (sepConj_mono hun_dec (sepConj_mono_left hun_uc))
            (Entails.of_eq (by ac_rfl))
        · wp_done
      · intro s2 hpc2 hrun2 ⟨hsp2, hx0_2, hx19_2, hx22_2, hx27_2, htr2⟩
        refine EncoderFromPb.seq_clean
          (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1096#64)
          (P_mid :=
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            memRegion pbA 128 ∗
            A.pool ∗
            (optProtoPolynomialEncoderAt A (pbA + 128#64) (optEncPb.map pbToProtoPolyEncoder) ∗
             (((pbA + 184#64) ↦₆₄ cap_dec) ∗
              v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec (some (pbToProtoPolyDecoder d))) ∗
             Frame))
          (Q := fun sm =>
            sm.sp = s0.sp - 2400#64 ∧
            sm.readReg64 .x19 = out ∧
            sm.readReg64 .x22 = cap_dec ∧
            sm.readReg64 .x27 = pbA ∧
            TraceCalleeSaved sm s0)
          (Ext4K.v7_call_drop_proto_unchunked_ct1_sent_1092 hA s0 s2 out pbA cap_dec u _
            hsp0_align hpc2 hrun2 hsp2 hx0_2 hx19_2 hx22_2 hx27_2 htr2)
          ?_
        intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx22_3, hx27_3, htr3⟩
        states_from_pb_fetches_range b (Rust.withPanics ext) 1096 8
        dsimp only [tripleRatchetProgAtExt, statesFromPbName,
          BitVec.ofNat_eq_ofNat] at hpc3 ⊢
        generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
          "<spqr::v1::chunked::states::States>::from_pb" = entry
        examples_hide_fetches
        wp_steps
        refine EncoderFromPb.align_pre (Entails.of_eq (by ac_rfl)) ?_
        wp_done
  · intro s4 hpc4 hrun4 ⟨hsp4, hx19_4, hx22_4, hx27_4, hx28_4, htr4⟩
    refine SepWP.mono
      (Ext4K.v7_cleanup_4528 hA s0 s4 out pbA cap_dec 2#64
        (optEncPb.map pbToProtoPolyEncoder) (some (pbToProtoPolyDecoder d))
        (memRegion pbA 128 ∗ Frame)
        hcap_dec hsp0_align hpc4 hrun4 hsp4 hx19_4 hx22_4 hx27_4 hx28_4 htr4)
      ?_
    intro sm Pm _ _ ⟨hPm, hq⟩
    refine ⟨Entails.trans hPm ?_, hq⟩
    have hm184 := ProofLib.memRegion_split pbA 128 56 (by decide)
    have hm224 := ProofLib.memRegion_split pbA 184 40 (by decide)
    rw [hm224, hm184]
    exact Entails.of_eq (by ac_rfl)

theorem v7_uc_none_3480_to_4632
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (s0 s1 : State) (out pbA cap_dec : BitVec 64)
    (optEncPb : Option PolynomialEncoder)
    (optDecPb : Option PolynomialDecoder) (Frame : SepProp)
    (hcap_dec : v7_optDecoderCapProp cap_dec (optDecPb.map pbToProtoPolyDecoder))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3480#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx9_1 : s1.readReg64 .x9 = noneCap)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((pbA ↦₆₄ noneCap) ∗ v7_optProtoUnchunkedCt1SentTail A pbA noneCap none) ∗
        optProtoPolynomialEncoderAt A (pbA + 128#64) (optEncPb.map pbToProtoPolyEncoder) ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec (optDecPb.map pbToProtoPolyDecoder)) ∗
        A.pool ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion pbA 224 ∗
          A.pool ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4528#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      optProtoPolynomialEncoderAt A (pbA + 128#64) (optEncPb.map pbToProtoPolyEncoder) ∗
      (((pbA + 184#64) ↦₆₄ cap_dec) ∗
       v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec (optDecPb.map pbToProtoPolyDecoder)) ∗
      A.pool ∗
      (memRegion pbA 128 ∗ Frame))
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = cap_dec ∧
      sm.readReg64 .x27 = pbA ∧
      sm.readReg64 .x28 = 0#64 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · dsimp only [v7_optProtoUnchunkedCt1SentTail]
    states_from_pb_fetches_range b (Rust.withPanics ext) 3480 8
    states_from_pb_fetches_range b (Rust.withPanics ext) 4524 4
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, noneCap,
      BitVec.ofNat_eq_ofNat] at hpc1 hx9_1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · have hun_uc := v7_optProtoUnchunkedCt1Sent_unexpose_none pbA
      dsimp only [noneCap] at hun_uc
      refine Entails.trans
        (Entails.of_eq (show _ =
          ((pbA ↦₆₄ (bv% (2 ^ 64 - 1))) ∗ memRegion (pbA + 8#64) 120) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           optProtoPolynomialEncoderAt A (pbA + 128#64) (optEncPb.map pbToProtoPolyEncoder) ∗
           (((pbA + 184#64) ↦₆₄ cap_dec) ∗
            v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec (optDecPb.map pbToProtoPolyDecoder)) ∗
           A.pool ∗ Frame) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left hun_uc) (Entails.of_eq (by ac_rfl))
    · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, hx27_2, hx28_2, htr2⟩
    refine SepWP.mono
      (Ext4K.v7_cleanup_4528 hA s0 s2 out pbA cap_dec 0#64
        (optEncPb.map pbToProtoPolyEncoder) (optDecPb.map pbToProtoPolyDecoder)
        (memRegion pbA 128 ∗ Frame)
        hcap_dec hsp0_align hpc2 hrun2 hsp2 hx19_2 hx22_2 hx27_2 hx28_2 htr2)
      ?_
    intro sm Pm _ _ ⟨hPm, hq⟩
    refine ⟨Entails.trans hPm ?_, hq⟩
    have hm184 := ProofLib.memRegion_split pbA 128 56 (by decide)
    have hm224 := ProofLib.memRegion_split pbA 184 40 (by decide)
    rw [hm224, hm184]
    exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SpqrV1.States.FromPb.Ext4K

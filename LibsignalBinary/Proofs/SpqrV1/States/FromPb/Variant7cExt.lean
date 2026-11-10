/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4K
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7c
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7aExt
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: 4-KiB Hook Companion for `Variant7c`

Lifts `Variant7c.lean`'s `AllocContracts`-parameterized theorems to `AllocContracts4K`
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

theorem v7_cleanup_7196
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (s0 s1 : State) (out pbA cap_dec : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder) (Frame : SepProp)
    (hcap_dec : v7_optDecoderCapProp cap_dec optDec)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7196#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗
        A.pool ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (pbA + 184#64) 40 ∗
          A.pool ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  cases optDec with
  | none =>
    unfold v7_optDecoderCapProp at hcap_dec
    subst hcap_dec
    unfold v7_optProtoPolyDecoderTail
    states_from_pb_fetches_range b (Rust.withPanics ext) 7196 16
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, noneCap, BitVec.ofNat_eq_ofNat] at hpc1 hx22_1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · have hm := optProtoPolyDecoder_none_entails_memRegion_40 (pbA + 184#64)
      dsimp only [noneCap] at hm
      refine Entails.trans
        (Entails.of_eq (show _ =
          (((pbA + 184#64) ↦₆₄ (bv% (2 ^ 64 - 1))) ∗
           memRegion ((pbA + 184#64) + 8#64) 32) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ A.pool ∗ Frame) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left hm) (Entails.of_eq (by ac_rfl))
    · wp_done
  | some pb =>
    refine SepWP.weaken_pre (v7_cleanup_opt_decoder_some_pre A (s0.sp - 2400#64) pbA cap_dec pb Frame) ?_
    apply ProofLib.SepWP.exists_left; intro ptsPtr
    apply ProofLib.SepWP.pure_elim; rintro ⟨hpts_le, hpts_cap_lt, _⟩
    refine EncoderFromPb.seq_clean
      (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4556#64)
      (P_mid :=
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         ((pbA + 192#64) ↦₆₄ ptsPtr) ∗
         ((pbA + 200#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
         (if cap_dec = 0 then emp
          else A.live ptsPtr (cap_dec.toNat * 24) 8 ∗
            arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24))
              ((cap_dec.toNat - pb.pts.length) * 24)) ∗
         memRegion (pbA + 208#64) 16) ∗
        A.pool ∗
        Frame)
      (Q := fun sm =>
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = 0#64 ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · have hne := v4_ptsCap_add_one_ne_zero hpts_cap_lt
      states_from_pb_fetches_range b (Rust.withPanics ext) 7196 12
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      wp_steps
      refine Drop.align_pre (by ac_rfl) ?_
      wp_done
    · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, hx27_2, hx28_2, htr2⟩
      exact Ext4K.v7_proto_decoder_dealloc_4556 hA s0 s2 out pbA cap_dec ptsPtr 0#64 pb.pts Frame
        hsp0_align hpts_le hpts_cap_lt hpc2 hrun2 hsp2 hx19_2 hx22_2 hx27_2 hx28_2 htr2

theorem v7_dealloc_4vecs_7116_to_7196
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (s0 s1 : State) (out pbA cap_dec c2 p2 c3 p3 c4 p4 c5 p5 : BitVec 64)
    (Frame : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7116#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx24_1 : s1.readReg64 .x24 = c2)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7196#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
        vecCapPtrDealloc A c2 p2 ∗
        vecCapPtrDealloc A c3 p3 ∗
        vecCapPtrDealloc A c4 p4 ∗
        vecCapPtrDealloc A c5 p5 ∗
        A.pool ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
          A.pool ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x27 = pbA ∧
        TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hdealloc := Ext4K.v7_sub_ok_dealloc_125316 (b := b) (A := A) (ext := ext) hA
  simp only [rustDeallocSpec] at hdealloc
  refine SepWP.weaken_pre
    (sepConj_mono_left (v4_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
  unfold v7_ct1SentSpillCells
  have h7552 : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
  have h1296 : (s0.sp - 2400#64) + 1296#64 = s0.sp - 1104#64 := by bv_omega
  have h1312 : (s0.sp - 2400#64) + 1312#64 = s0.sp - 1088#64 := by bv_omega
  have h1320 : (s0.sp - 2400#64) + 1320#64 = s0.sp - 1080#64 := by bv_omega
  have h1336 : (s0.sp - 2400#64) + 1336#64 = s0.sp - 1064#64 := by bv_omega
  have h1344 : (s0.sp - 2400#64) + 1344#64 = s0.sp - 1056#64 := by bv_omega
  have h1360 : (s0.sp - 2400#64) + 1360#64 = s0.sp - 1040#64 := by bv_omega
  have h1368 : (s0.sp - 2400#64) + 1368#64 = s0.sp - 1032#64 := by bv_omega
  rw [h7552, h1296, h1312, h1320, h1336, h1344, h1360, h1368]
  states_from_pb_fetches_range b (Rust.withPanics ext) 7116 80
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, vecCapPtrDealloc,
    BitVec.ofNat_eq_ofNat] at hdealloc hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  refine EncoderFromPb.seq_clean (mid := entry + 7136#64)
    (P_mid := (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
      (((s0.sp - 1104#64) ↦₆₄ p2) ∗ ((s0.sp - 1088#64) ↦₆₄ c3) ∗ ((s0.sp - 1080#64) ↦₆₄ p3) ∗
       ((s0.sp - 1064#64) ↦₆₄ c4) ∗ ((s0.sp - 1056#64) ↦₆₄ p4) ∗ ((s0.sp - 1040#64) ↦₆₄ c5) ∗
       ((s0.sp - 1032#64) ↦₆₄ p5)) ∗
      (if (c3 == 0#64) = true then emp else A.live p3 c3.toNat 1 ∗ memRegion p3 c3.toNat) ∗
      (if (c4 == 0#64) = true then emp else A.live p4 c4.toNat 1 ∗ memRegion p4 c4.toNat) ∗
      (if (c5 == 0#64) = true then emp else A.live p5 c5.toNat 1 ∗ memRegion p5 c5.toNat) ∗
      A.pool ∗ Frame)
    (Q := fun sm => sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = cap_dec ∧ sm.readReg64 .x27 = pbA ∧ TraceCalleeSaved sm s0)
    ?_ ?_
  · by_cases hc2 : (c2 == 0#64) = true <;>
      simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; refine Drop.align_pre (by ac_rfl) ?_; wp_done
    · wp_steps; wp_apply; refine Drop.align_pre (by rw [hsp1]; ac_rfl) ?_; wp_done
  intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, hx27_2, htr2⟩
  refine EncoderFromPb.seq_clean (mid := entry + 7156#64)
    (P_mid := (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
      (((s0.sp - 1104#64) ↦₆₄ p2) ∗ ((s0.sp - 1088#64) ↦₆₄ c3) ∗ ((s0.sp - 1080#64) ↦₆₄ p3) ∗
       ((s0.sp - 1064#64) ↦₆₄ c4) ∗ ((s0.sp - 1056#64) ↦₆₄ p4) ∗ ((s0.sp - 1040#64) ↦₆₄ c5) ∗
       ((s0.sp - 1032#64) ↦₆₄ p5)) ∗
      (if (c4 == 0#64) = true then emp else A.live p4 c4.toNat 1 ∗ memRegion p4 c4.toNat) ∗
      (if (c5 == 0#64) = true then emp else A.live p5 c5.toNat 1 ∗ memRegion p5 c5.toNat) ∗
      A.pool ∗ Frame)
    (Q := fun sm => sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = cap_dec ∧ sm.readReg64 .x27 = pbA ∧ TraceCalleeSaved sm s0)
    ?_ ?_
  · by_cases hc3 : (c3 == 0#64) = true <;>
      simp only [hc3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; refine Drop.align_pre (by ac_rfl) ?_; wp_done
    · wp_steps; wp_apply; refine Drop.align_pre (by rw [hsp2]; ac_rfl) ?_; wp_done
  intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx22_3, hx27_3, htr3⟩
  refine EncoderFromPb.seq_clean (mid := entry + 7176#64)
    (P_mid := (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
      (((s0.sp - 1104#64) ↦₆₄ p2) ∗ ((s0.sp - 1088#64) ↦₆₄ c3) ∗ ((s0.sp - 1080#64) ↦₆₄ p3) ∗
       ((s0.sp - 1064#64) ↦₆₄ c4) ∗ ((s0.sp - 1056#64) ↦₆₄ p4) ∗ ((s0.sp - 1040#64) ↦₆₄ c5) ∗
       ((s0.sp - 1032#64) ↦₆₄ p5)) ∗
      (if (c5 == 0#64) = true then emp else A.live p5 c5.toNat 1 ∗ memRegion p5 c5.toNat) ∗
      A.pool ∗ Frame)
    (Q := fun sm => sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = cap_dec ∧ sm.readReg64 .x27 = pbA ∧ TraceCalleeSaved sm s0)
    ?_ ?_
  · by_cases hc4 : (c4 == 0#64) = true <;>
      simp only [hc4, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; refine Drop.align_pre (by ac_rfl) ?_; wp_done
    · wp_steps; wp_apply; refine Drop.align_pre (by rw [hsp3]; ac_rfl) ?_; wp_done
  intro s4 hpc4 hrun4 ⟨hsp4, hx19_4, hx22_4, hx27_4, htr4⟩
  have hst := v4_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
  rw [h7552] at hst
  by_cases hc5 : (c5 == 0#64) = true <;>
    simp only [hc5, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · exact sepConj_mono_left hst
    · wp_done
  · wp_steps
    wp_apply
    refine EncoderFromPb.align_pre ?_ ?_
    · rw [hsp4]
      refine Entails.trans
        (Entails.of_eq (show _ =
          (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
          ((((s0.sp - 1104#64) ↦₆₄ p2) ∗ ((s0.sp - 1088#64) ↦₆₄ c3) ∗ ((s0.sp - 1080#64) ↦₆₄ p3) ∗
            ((s0.sp - 1064#64) ↦₆₄ c4) ∗ ((s0.sp - 1056#64) ↦₆₄ p4) ∗ ((s0.sp - 1040#64) ↦₆₄ c5) ∗
            ((s0.sp - 1032#64) ↦₆₄ p5)) ∗ A.pool ∗ Frame) by ac_rfl)) ?_
      exact sepConj_mono_left hst
    · wp_done

theorem v7_dealloc_c1_7104_to_7116
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (s0 s1 : State) (out pbA cap_dec c1 p1 c2 : BitVec 64)
    (Frame : SepProp)
    (hc1 : ¬((c1 == 0#64) = true))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7104#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx1_1 : s1.readReg64 .x1 = c1)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx24_1 : s1.readReg64 .x24 = c2)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = p1)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7116#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        vecCapPtrDealloc A c1 p1 ∗
        A.pool ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          A.pool ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x24 = c2 ∧
        sm.readReg64 .x27 = pbA ∧
        TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hdealloc := Ext4K.v7_sub_ok_dealloc_125316 (b := b) (A := A) (ext := ext) hA
  simp only [rustDeallocSpec] at hdealloc
  refine SepWP.weaken_pre
    (sepConj_mono_left (v4_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
  have h7552 : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
  rw [h7552]
  have hst := v4_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
  rw [h7552] at hst
  states_from_pb_fetches_range b (Rust.withPanics ext) 7104 12
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, vecCapPtrDealloc,
    BitVec.ofNat_eq_ofNat] at hdealloc hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  simp only [hc1, ↓reduceIte]
  wp_steps
  wp_apply
  refine EncoderFromPb.align_pre ?_ ?_
  · rw [hsp1]
    refine Entails.trans
      (Entails.of_eq (show _ =
        (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
        (A.pool ∗ Frame) by ac_rfl)) ?_
    exact sepConj_mono_left hst
  · wp_done

theorem v7_cleanup_7100
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (s0 s1 : State) (out pbA cap_dec c1 p1 c2 p2 c3 p3 c4 p4 c5 p5 : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder) (Frame : SepProp)
    (hcap_dec : v7_optDecoderCapProp cap_dec optDec)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7100#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx1_1 : s1.readReg64 .x1 = c1)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx24_1 : s1.readReg64 .x24 = c2)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = p1)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
        vecCapPtrDealloc A c1 p1 ∗
        vecCapPtrDealloc A c2 p2 ∗
        vecCapPtrDealloc A c3 p3 ∗
        vecCapPtrDealloc A c4 p4 ∗
        vecCapPtrDealloc A c5 p5 ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗
        A.pool ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
          memRegion (pbA + 184#64) 40 ∗
          A.pool ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7116#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      A.pool ∗
      (v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
       vecCapPtrDealloc A c2 p2 ∗
       vecCapPtrDealloc A c3 p3 ∗
       vecCapPtrDealloc A c4 p4 ∗
       vecCapPtrDealloc A c5 p5 ∗
       (((pbA + 184#64) ↦₆₄ cap_dec) ∗
        v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗
       Frame))
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = cap_dec ∧
      sm.readReg64 .x24 = c2 ∧
      sm.readReg64 .x27 = pbA ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · by_cases hc1 : (c1 == 0#64) = true
    · states_from_pb_fetches_range b (Rust.withPanics ext) 7100 4
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, vecCapPtrDealloc,
        BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      simp only [hc1, ↓reduceIte, emp_sepConj]
      wp_steps
      refine Drop.align_pre (by ac_rfl) ?_
      wp_done
    · refine EncoderFromPb.seq_clean
        (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7104#64)
        (P_mid :=
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          vecCapPtrDealloc A c1 p1 ∗
          A.pool ∗
          (v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
           vecCapPtrDealloc A c2 p2 ∗
           vecCapPtrDealloc A c3 p3 ∗
           vecCapPtrDealloc A c4 p4 ∗
           vecCapPtrDealloc A c5 p5 ∗
           (((pbA + 184#64) ↦₆₄ cap_dec) ∗
            v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗
           Frame))
        (Q := fun sm =>
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x1 = c1 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x22 = cap_dec ∧
          sm.readReg64 .x24 = c2 ∧
          sm.readReg64 .x27 = pbA ∧
          sm.readReg64 .x28 = p1 ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · states_from_pb_fetches_range b (Rust.withPanics ext) 7100 4
        dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
        generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
          "<spqr::v1::chunked::states::States>::from_pb" = entry
        examples_hide_fetches
        wp_steps
        refine Drop.align_pre (by ac_rfl) ?_
        wp_done
      · intro s2 hpc2 hrun2 ⟨hsp2, hx1_2, hx19_2, hx22_2, hx24_2, hx27_2, hx28_2, htr2⟩
        exact Ext4K.v7_dealloc_c1_7104_to_7116 hA s0 s2 out pbA cap_dec c1 p1 c2 _
          hc1 hsp0_align hpc2 hrun2 hsp2 hx1_2 hx19_2 hx22_2 hx24_2 hx27_2 hx28_2 htr2
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, hx24_2, hx27_2, htr2⟩
    refine EncoderFromPb.seq_clean
      (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7196#64)
      (P_mid :=
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
        A.pool ∗
        ((((pbA + 184#64) ↦₆₄ cap_dec) ∗
          v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗ Frame))
      (Q := fun sm =>
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x27 = pbA ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · exact SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
        (Ext4K.v7_dealloc_4vecs_7116_to_7196 hA s0 s2 out pbA cap_dec c2 p2 c3 p3 c4 p4 c5 p5
          ((((pbA + 184#64) ↦₆₄ cap_dec) ∗
            v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗ Frame)
          hsp0_align hpc2 hrun2 hsp2 hx19_2 hx22_2 hx24_2 hx27_2 htr2)
    · intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx22_3, hx27_3, htr3⟩
      refine SepWP.weaken_pre ?_
        (SepWP.mono
          (Ext4K.v7_cleanup_7196 hA s0 s3 out pbA cap_dec optDec
            (v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗ Frame)
            hcap_dec hsp0_align hpc3 hrun3 hsp3 hx19_3 hx22_3 hx27_3 htr3)
          (fun _ _ _ _ ⟨hPm, hq⟩ => ⟨Entails.trans hPm (Entails.of_eq (by ac_rfl)), hq⟩))
      exact Entails.of_eq (by ac_rfl)

theorem v7_cleanup_3732
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (s0 s1 : State) (out pbA cap_dec c1 p1 c2 p2 c3 p3 c4 p4 c5 p5 : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder) (Frame : SepProp)
    (hcap_dec : v7_optDecoderCapProp cap_dec optDec)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3732#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx24_1 : s1.readReg64 .x24 = c2)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = p1)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
        v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
        vecCapPtrDealloc A c1 p1 ∗
        vecCapPtrDealloc A c2 p2 ∗
        vecCapPtrDealloc A c3 p3 ∗
        vecCapPtrDealloc A c4 p4 ∗
        vecCapPtrDealloc A c5 p5 ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗
        A.pool ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
          v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
          memRegion (pbA + 184#64) 40 ∗
          A.pool ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  have h24 : (s0.sp - 2400#64) + 24#64 = s0.sp - 2376#64 := by bv_omega
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7116#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      A.pool ∗
      (v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
       vecCapPtrDealloc A c2 p2 ∗
       vecCapPtrDealloc A c3 p3 ∗
       vecCapPtrDealloc A c4 p4 ∗
       vecCapPtrDealloc A c5 p5 ∗
       (((pbA + 184#64) ↦₆₄ cap_dec) ∗
        v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗
       ((((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗ Frame)))
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = cap_dec ∧
      sm.readReg64 .x24 = c2 ∧
      sm.readReg64 .x27 = pbA ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · by_cases hc1 : (c1 == 0#64) = true
    · rw [h24]
      states_from_pb_fetches_range b (Rust.withPanics ext) 3732 12
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, vecCapPtrDealloc,
        BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      simp only [hc1, Bool.true_eq_false, ↓reduceIte, emp_sepConj]
      wp_steps
      refine Drop.align_pre (by ac_rfl) ?_
      wp_done
    · refine EncoderFromPb.seq_clean
        (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7104#64)
        (P_mid :=
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          vecCapPtrDealloc A c1 p1 ∗
          A.pool ∗
          (v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
           vecCapPtrDealloc A c2 p2 ∗
           vecCapPtrDealloc A c3 p3 ∗
           vecCapPtrDealloc A c4 p4 ∗
           vecCapPtrDealloc A c5 p5 ∗
           (((pbA + 184#64) ↦₆₄ cap_dec) ∗
            v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗
           ((((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗ Frame)))
        (Q := fun sm =>
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x1 = c1 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x22 = cap_dec ∧
          sm.readReg64 .x24 = c2 ∧
          sm.readReg64 .x27 = pbA ∧
          sm.readReg64 .x28 = p1 ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · rw [h24]
        states_from_pb_fetches_range b (Rust.withPanics ext) 3732 8
        dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
        generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
          "<spqr::v1::chunked::states::States>::from_pb" = entry
        examples_hide_fetches
        wp_steps
        refine Drop.align_pre (by ac_rfl) ?_
        wp_done
      · intro s2 hpc2 hrun2 ⟨hsp2, hx1_2, hx19_2, hx22_2, hx24_2, hx27_2, hx28_2, htr2⟩
        exact Ext4K.v7_dealloc_c1_7104_to_7116 hA s0 s2 out pbA cap_dec c1 p1 c2 _
          hc1 hsp0_align hpc2 hrun2 hsp2 hx1_2 hx19_2 hx22_2 hx24_2 hx27_2 hx28_2 htr2
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, hx24_2, hx27_2, htr2⟩
    refine EncoderFromPb.seq_clean
      (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7196#64)
      (P_mid :=
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
        A.pool ∗
        ((((pbA + 184#64) ↦₆₄ cap_dec) ∗
          v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗
         ((((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗ Frame)))
      (Q := fun sm =>
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x27 = pbA ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · exact SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
        (Ext4K.v7_dealloc_4vecs_7116_to_7196 hA s0 s2 out pbA cap_dec c2 p2 c3 p3 c4 p4 c5 p5
          ((((pbA + 184#64) ↦₆₄ cap_dec) ∗
            v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗
           ((((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗ Frame))
          hsp0_align hpc2 hrun2 hsp2 hx19_2 hx22_2 hx24_2 hx27_2 htr2)
    · intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx22_3, hx27_3, htr3⟩
      refine SepWP.weaken_pre ?_
        (SepWP.mono
          (Ext4K.v7_cleanup_7196 hA s0 s3 out pbA cap_dec optDec
            (v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
             ((((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗ Frame))
            hcap_dec hsp0_align hpc3 hrun3 hsp3 hx19_3 hx22_3 hx27_3 htr3)
          (fun _ _ _ _ ⟨hPm, hq⟩ => ⟨Entails.trans hPm (Entails.of_eq (by ac_rfl)), hq⟩))
      exact Entails.of_eq (by ac_rfl)

theorem v7_drop_poly16_10556_to_10568
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (s0 s1 : State) (out c2 : BitVec 64)
    (enc : PolyEncoder) (Frame : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10556#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx24_1 : s1.readReg64 .x24 = c2)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10568#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        polyEncoderAt A ((s0.sp - 2400#64) + 1392#64) enc ∗
        A.pool ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗
          A.pool ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x24 = c2 ∧
        TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hdrop := Ext4K.v7_sub_ok_drop_poly16 hA
  simp only [dropGluePoly16Spec, dropGluePoly16Stack] at hdrop
  refine SepWP.weaken_pre (v7_drop_poly16_pre A (s0.sp - 2400#64) enc Frame) ?_
  apply ProofLib.SepWP.exists_left; intro tag
  apply ProofLib.SepWP.exists_left; intro vecs
  apply ProofLib.SepWP.pure_elim; intro hvecs_len
  have h1392 : (s0.sp - 2400#64) + 1392#64 = s0.sp - 1008#64 := by bv_omega
  have h1400 : (s0.sp - 1008#64) + 8#64 = s0.sp - 1000#64 := by bv_omega
  have h1784 : (s0.sp - 1008#64) + 392#64 = s0.sp - 616#64 := by bv_omega
  have h7552 : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
  rw [h1392, h1400, h1784, h7552]
  states_from_pb_fetches_range b (Rust.withPanics ext) 10556 12
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, polyArrayBytes,
    BitVec.ofNat_eq_ofNat] at hdrop hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hdrop
  wp_steps
  wp_apply
  refine EncoderFromPb.align_pre ?_ ?_
  · have hst := v7_stackAt_dropStack32_to_encoderFromPbStack (s0.sp - 2400#64)
    have hjoin := v7_polyEncoder_1392_join (s0.sp - 2400#64) tag
    have h1400' : (s0.sp - 2400#64) + 1400#64 = s0.sp - 1000#64 := by bv_omega
    have h1784' : (s0.sp - 2400#64) + 1784#64 = s0.sp - 616#64 := by bv_omega
    rw [h7552] at hst
    rw [h1392, h1400', h1784'] at hjoin
    rw [hsp1]
    refine Entails.trans
      (Entails.of_eq (show _ =
        (stackAt (s0.sp - 2400#64) dropStack32 ∗ memRegion (s0.sp - 7552#64) 1024) ∗
        ((((s0.sp - 1008#64) ↦₆₄ tag) ∗
          memRegion (s0.sp - 1000#64) 384 ∗
          memRegion (s0.sp - 616#64) 8) ∗
         (A.pool ∗ Frame)) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono hst (sepConj_mono_left hjoin)) (Entails.of_eq (by ac_rfl))
  · wp_done

theorem v7_dealloc_c1_10568_to_10588
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (s0 s1 : State) (out c1 p1 c2 : BitVec 64)
    (Frame : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10568#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx24_1 : s1.readReg64 .x24 = c2)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10588#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
        (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
        vecCapPtrDealloc A c1 p1 ∗
        A.pool ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
          (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
          A.pool ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x24 = c2 ∧
        TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hdealloc := Ext4K.v7_sub_ok_dealloc_125316 (b := b) (A := A) (ext := ext) hA
  simp only [rustDeallocSpec] at hdealloc
  refine SepWP.weaken_pre
    (sepConj_mono_left (v4_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
  have h7552 : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
  have h200 : (s0.sp - 2400#64) + 200#64 = s0.sp - 2200#64 := by bv_omega
  have h24 : (s0.sp - 2400#64) + 24#64 = s0.sp - 2376#64 := by bv_omega
  rw [h7552, h200, h24]
  have hst := v4_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
  rw [h7552] at hst
  states_from_pb_fetches_range b (Rust.withPanics ext) 10568 20
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, vecCapPtrDealloc,
    BitVec.ofNat_eq_ofNat] at hdealloc hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  by_cases hc1 : (c1 == 0#64) = true <;>
    simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · exact sepConj_mono_left hst
    · wp_done
  · wp_steps
    wp_apply
    refine EncoderFromPb.align_pre ?_ ?_
    · rw [hsp1]
      refine Entails.trans
        (Entails.of_eq (show _ =
          (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
          (((s0.sp - 2200#64) ↦₆₄ p1) ∗ ((s0.sp - 2376#64) ↦₆₄ c1) ∗ A.pool ∗ Frame) by ac_rfl)) ?_
      exact sepConj_mono_left hst
    · wp_done

theorem v7_dealloc_4vecs_10588_to_11112
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (s0 s1 : State) (out c2 p2 c3 p3 c4 p4 c5 p5 : BitVec 64)
    (Frame : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10588#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx24_1 : s1.readReg64 .x24 = c2)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 11112#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
        vecCapPtrDealloc A c2 p2 ∗
        vecCapPtrDealloc A c3 p3 ∗
        vecCapPtrDealloc A c4 p4 ∗
        vecCapPtrDealloc A c5 p5 ∗
        A.pool ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
          A.pool ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hdealloc := Ext4K.v7_sub_ok_dealloc_125316 (b := b) (A := A) (ext := ext) hA
  simp only [rustDeallocSpec] at hdealloc
  refine SepWP.weaken_pre
    (sepConj_mono_left (v4_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
  unfold v7_ct1SentSpillCells
  have h7552 : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
  have h1296 : (s0.sp - 2400#64) + 1296#64 = s0.sp - 1104#64 := by bv_omega
  have h1312 : (s0.sp - 2400#64) + 1312#64 = s0.sp - 1088#64 := by bv_omega
  have h1320 : (s0.sp - 2400#64) + 1320#64 = s0.sp - 1080#64 := by bv_omega
  have h1336 : (s0.sp - 2400#64) + 1336#64 = s0.sp - 1064#64 := by bv_omega
  have h1344 : (s0.sp - 2400#64) + 1344#64 = s0.sp - 1056#64 := by bv_omega
  have h1360 : (s0.sp - 2400#64) + 1360#64 = s0.sp - 1040#64 := by bv_omega
  have h1368 : (s0.sp - 2400#64) + 1368#64 = s0.sp - 1032#64 := by bv_omega
  rw [h7552, h1296, h1312, h1320, h1336, h1344, h1360, h1368]
  states_from_pb_fetches_range b (Rust.withPanics ext) 10588 84
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, vecCapPtrDealloc,
    BitVec.ofNat_eq_ofNat] at hdealloc hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  refine EncoderFromPb.seq_clean (mid := entry + 10608#64)
    (P_mid := (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
      (((s0.sp - 1104#64) ↦₆₄ p2) ∗ ((s0.sp - 1088#64) ↦₆₄ c3) ∗ ((s0.sp - 1080#64) ↦₆₄ p3) ∗
       ((s0.sp - 1064#64) ↦₆₄ c4) ∗ ((s0.sp - 1056#64) ↦₆₄ p4) ∗ ((s0.sp - 1040#64) ↦₆₄ c5) ∗
       ((s0.sp - 1032#64) ↦₆₄ p5)) ∗
      (if (c3 == 0#64) = true then emp else A.live p3 c3.toNat 1 ∗ memRegion p3 c3.toNat) ∗
      (if (c4 == 0#64) = true then emp else A.live p4 c4.toNat 1 ∗ memRegion p4 c4.toNat) ∗
      (if (c5 == 0#64) = true then emp else A.live p5 c5.toNat 1 ∗ memRegion p5 c5.toNat) ∗
      A.pool ∗ Frame)
    (Q := fun sm => sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧ TraceCalleeSaved sm s0)
    ?_ ?_
  · by_cases hc2 : (c2 == 0#64) = true <;>
      simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; refine Drop.align_pre (by ac_rfl) ?_; wp_done
    · wp_steps; wp_apply; refine Drop.align_pre (by rw [hsp1]; ac_rfl) ?_; wp_done
  intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, htr2⟩
  refine EncoderFromPb.seq_clean (mid := entry + 10628#64)
    (P_mid := (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
      (((s0.sp - 1104#64) ↦₆₄ p2) ∗ ((s0.sp - 1088#64) ↦₆₄ c3) ∗ ((s0.sp - 1080#64) ↦₆₄ p3) ∗
       ((s0.sp - 1064#64) ↦₆₄ c4) ∗ ((s0.sp - 1056#64) ↦₆₄ p4) ∗ ((s0.sp - 1040#64) ↦₆₄ c5) ∗
       ((s0.sp - 1032#64) ↦₆₄ p5)) ∗
      (if (c4 == 0#64) = true then emp else A.live p4 c4.toNat 1 ∗ memRegion p4 c4.toNat) ∗
      (if (c5 == 0#64) = true then emp else A.live p5 c5.toNat 1 ∗ memRegion p5 c5.toNat) ∗
      A.pool ∗ Frame)
    (Q := fun sm => sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧ TraceCalleeSaved sm s0)
    ?_ ?_
  · by_cases hc3 : (c3 == 0#64) = true <;>
      simp only [hc3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; refine Drop.align_pre (by ac_rfl) ?_; wp_done
    · wp_steps; wp_apply; refine Drop.align_pre (by rw [hsp2]; ac_rfl) ?_; wp_done
  intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, htr3⟩
  refine EncoderFromPb.seq_clean (mid := entry + 10648#64)
    (P_mid := (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
      (((s0.sp - 1104#64) ↦₆₄ p2) ∗ ((s0.sp - 1088#64) ↦₆₄ c3) ∗ ((s0.sp - 1080#64) ↦₆₄ p3) ∗
       ((s0.sp - 1064#64) ↦₆₄ c4) ∗ ((s0.sp - 1056#64) ↦₆₄ p4) ∗ ((s0.sp - 1040#64) ↦₆₄ c5) ∗
       ((s0.sp - 1032#64) ↦₆₄ p5)) ∗
      (if (c5 == 0#64) = true then emp else A.live p5 c5.toNat 1 ∗ memRegion p5 c5.toNat) ∗
      A.pool ∗ Frame)
    (Q := fun sm => sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧ TraceCalleeSaved sm s0)
    ?_ ?_
  · by_cases hc4 : (c4 == 0#64) = true <;>
      simp only [hc4, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; refine Drop.align_pre (by ac_rfl) ?_; wp_done
    · wp_steps; wp_apply; refine Drop.align_pre (by rw [hsp3]; ac_rfl) ?_; wp_done
  intro s4 hpc4 hrun4 ⟨hsp4, hx19_4, htr4⟩
  have hst := v4_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
  rw [h7552] at hst
  by_cases hc5 : (c5 == 0#64) = true <;>
    simp only [hc5, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · exact sepConj_mono_left hst
    · wp_done
  · wp_steps
    wp_apply
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · rw [hsp4]
      refine Entails.trans
        (Entails.of_eq (show _ =
          (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
          ((((s0.sp - 1104#64) ↦₆₄ p2) ∗ ((s0.sp - 1088#64) ↦₆₄ c3) ∗ ((s0.sp - 1080#64) ↦₆₄ p3) ∗
            ((s0.sp - 1064#64) ↦₆₄ c4) ∗ ((s0.sp - 1056#64) ↦₆₄ p4) ∗ ((s0.sp - 1040#64) ↦₆₄ c5) ∗
            ((s0.sp - 1032#64) ↦₆₄ p5)) ∗ A.pool ∗ Frame) by ac_rfl)) ?_
      exact sepConj_mono_left hst
    · wp_done

theorem v7_cleanup_10556
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (s0 s1 : State) (out c1 p1 c2 p2 c3 p3 c4 p4 c5 p5 : BitVec 64)
    (enc : PolyEncoder) (Frame : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10556#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx24_1 : s1.readReg64 .x24 = c2)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        polyEncoderAt A ((s0.sp - 2400#64) + 1392#64) enc ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
        (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
        v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
        vecCapPtrDealloc A c1 p1 ∗
        vecCapPtrDealloc A c2 p2 ∗
        vecCapPtrDealloc A c3 p3 ∗
        vecCapPtrDealloc A c4 p4 ∗
        vecCapPtrDealloc A c5 p5 ∗
        A.pool ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗
          (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
          (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
          v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
          A.pool ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10568#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗
      A.pool ∗
      ((((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
       (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
       v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
       vecCapPtrDealloc A c1 p1 ∗
       vecCapPtrDealloc A c2 p2 ∗
       vecCapPtrDealloc A c3 p3 ∗
       vecCapPtrDealloc A c4 p4 ∗
       vecCapPtrDealloc A c5 p5 ∗ Frame))
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x24 = c2 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · exact SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (Ext4K.v7_drop_poly16_10556_to_10568 hA s0 s1 out c2 enc
        ((((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
         (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
         v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
         vecCapPtrDealloc A c1 p1 ∗
         vecCapPtrDealloc A c2 p2 ∗
         vecCapPtrDealloc A c3 p3 ∗
         vecCapPtrDealloc A c4 p4 ∗
         vecCapPtrDealloc A c5 p5 ∗ Frame)
        hsp0_align hpc1 hrun1 hsp1 hx19_1 hx24_1 htr1)
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx24_2, htr2⟩
    refine EncoderFromPb.seq_clean
      (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10588#64)
      (P_mid :=
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
        (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
        A.pool ∗
        (v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
         vecCapPtrDealloc A c2 p2 ∗
         vecCapPtrDealloc A c3 p3 ∗
         vecCapPtrDealloc A c4 p4 ∗
         vecCapPtrDealloc A c5 p5 ∗
         memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗ Frame))
      (Q := fun sm =>
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x24 = c2 ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · exact SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
        (Ext4K.v7_dealloc_c1_10568_to_10588 hA s0 s2 out c1 p1 c2
          (v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
           vecCapPtrDealloc A c2 p2 ∗
           vecCapPtrDealloc A c3 p3 ∗
           vecCapPtrDealloc A c4 p4 ∗
           vecCapPtrDealloc A c5 p5 ∗
           memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗ Frame)
          hsp0_align hpc2 hrun2 hsp2 hx19_2 hx24_2 htr2)
    · intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx24_3, htr3⟩
      refine EncoderFromPb.seq_clean
        (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 11112#64)
        (P_mid :=
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
          A.pool ∗
          ((((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
           (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
           memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗ Frame))
        (Q := fun sm =>
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · exact SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
          (Ext4K.v7_dealloc_4vecs_10588_to_11112 hA s0 s3 out c2 p2 c3 p3 c4 p4 c5 p5
            ((((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
             (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
             memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗ Frame)
            hsp0_align hpc3 hrun3 hsp3 hx19_3 hx24_3 htr3)
      · intro s4 hpc4 hrun4 ⟨hsp4, hx19_4, htr4⟩
        refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) ?_
        exact SepWP.mono
          (v7_cleanup_11112 s0 s4 out _ hpc4 hrun4 hsp4 hx19_4 htr4)
          (fun _ _ _ _ ⟨hPm, hq⟩ => ⟨Entails.trans hPm (Entails.of_eq (by ac_rfl)), hq⟩)

end CryptoVerification.SpqrV1.States.FromPb.Ext4K

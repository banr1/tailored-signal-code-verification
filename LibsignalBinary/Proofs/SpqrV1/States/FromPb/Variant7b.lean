/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7a
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# SPQR V1 `<States>::from_pb`: Variant 7 (`Ct1Sampled`, niche variant) — Part B

`Option<ProtoPolynomialDecoder>` decomposition and error/cleanup blocks
(`+4548`, `+4528`, `+5444`, `+7100`, `+10556`, `+11096`) for Variant 7.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.FromPb

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

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff libsignalSessionCode
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero
attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  statesFromPb_fnOff
  stubOff_rust_no_alloc_shim
  stubOff_rust_alloc
  stubOff_rust_dealloc
  stubOff_memcpy
  stubOff_handle_error

/-! ## 1. `Option<ProtoPolynomialDecoder>` Decomposition & Cleanup at `+4548`, `+4528`, `+5444` -/

/-- Pure condition on the exposed `cap` word at `d` of `optProtoPolynomialDecoderAt A d m`. -/
def v7_optDecoderCapProp (cap : BitVec 64) : Option ProtoPolynomialDecoder → Prop
  | none => cap = noneCap
  | some _ => cap.toNat * 24 < 2 ^ 63

/-- Remainder of `optProtoPolynomialDecoderAt A d m` after splitting out `d ↦₆₄ cap`,
    exposing `d + 24 ↦₃₂ pb.ptsNeeded` for the `+1068` check. -/
def v7_optProtoPolyDecoderTail (A : RustAlloc) (d cap : BitVec 64) :
    Option ProtoPolynomialDecoder → SepProp
  | none => memRegion (d + 8#64) 32
  | some pb =>
    ∃∗ ptr : BitVec 64,
      ⌜pb.pts.length ≤ cap.toNat ∧ cap.toNat * 24 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ((d + 8#64) ↦₆₄ ptr) ∗
      ((d + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
      (if cap = 0 then emp
       else A.live ptr (cap.toNat * 24) 8 ∗
         arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr pb.pts ∗
         memRegion (ptr + BitVec.ofNat 64 (pb.pts.length * 24))
           ((cap.toNat - pb.pts.length) * 24)) ∗
      ((d + protoPolynomialDecoderPtsNeededOff) ↦₃₂ pb.ptsNeeded) ∗
      ((d + protoPolynomialDecoderPolysOff) ↦₃₂ pb.polys) ∗
      ((d + protoPolynomialDecoderIsCompleteOff) ↦₈ boolByte pb.isComplete) ∗
      memRegion (d + protoPolynomialDecoderPadOff) protoPolynomialDecoderPadSize

theorem v7_optProtoPolyDecoder_expose_cap (A : RustAlloc) (d : BitVec 64)
    (m : Option ProtoPolynomialDecoder) :
    optProtoPolynomialDecoderAt A d m ⊢
      ∃∗ cap : BitVec 64,
        ⌜v7_optDecoderCapProp cap m⌝ ∗
        (d ↦₆₄ cap) ∗ v7_optProtoPolyDecoderTail A d cap m := by
  cases m with
  | none =>
    rw [optProtoPolynomialDecoderAt_none']
    refine Entails.sepExists_right noneCap ?_
    unfold v7_optDecoderCapProp v7_optProtoPolyDecoderTail
    exact Entails.pure_right rfl (Entails.refl _)
  | some pb =>
    rw [optProtoPolynomialDecoderAt_some']
    unfold protoPolynomialDecoderAt vecVecU8At vecOf Poly.vecHeaderBytes
    rw [sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro cap
    rw [sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro ptr
    refine Entails.sepExists_right cap ?_
    unfold vecAt vecBuf vecHeader v7_optDecoderCapProp v7_optProtoPolyDecoderTail
    refine Entails.trans
      (Entails.of_eq (show _ =
        ⌜pb.pts.length ≤ cap.toNat ∧ cap.toNat * 24 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        ((d ↦₆₄ cap) ∗
         (((d + 8#64) ↦₆₄ ptr) ∗
          ((d + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
          (if cap = 0 then emp
           else A.live ptr (cap.toNat * 24) 8 ∗
             arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr pb.pts ∗
             memRegion (ptr + BitVec.ofNat 64 (pb.pts.length * 24))
               ((cap.toNat - pb.pts.length) * 24)) ∗
          ((d + protoPolynomialDecoderPtsNeededOff) ↦₃₂ pb.ptsNeeded) ∗
          ((d + protoPolynomialDecoderPolysOff) ↦₃₂ pb.polys) ∗
          ((d + protoPolynomialDecoderIsCompleteOff) ↦₈ boolByte pb.isComplete) ∗
          memRegion (d + protoPolynomialDecoderPadOff) protoPolynomialDecoderPadSize)) by ac_rfl)) ?_
    apply Entails.pure_left; intro hp
    refine Entails.pure_right hp.2.1 ?_
    exact sepConj_mono_right (Entails.sepExists_right ptr (Entails.pure_right hp (Entails.refl _)))

theorem v7_optProtoPolyDecoder_unexpose_some (A : RustAlloc) (d cap : BitVec 64)
    (pb : ProtoPolynomialDecoder) :
    (d ↦₆₄ cap) ∗ v7_optProtoPolyDecoderTail A d cap (some pb) ⊢
      protoPolynomialDecoderAt A d pb := by
  unfold v7_optProtoPolyDecoderTail protoPolynomialDecoderAt vecVecU8At vecOf Poly.vecHeaderBytes
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro ptr
  rw [← sepConj_assoc, sepConj_comm (d ↦₆₄ cap), sepConj_assoc]
  apply Entails.pure_left; intro hp
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_right cap ?_
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_right ptr ?_
  unfold vecAt vecBuf vecHeader
  refine Entails.trans ?_
    (Entails.of_eq (show
      ⌜pb.pts.length ≤ cap.toNat ∧ cap.toNat * 24 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ((d ↦₆₄ cap) ∗
       (((d + 8#64) ↦₆₄ ptr) ∗
        ((d + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
        (if cap = 0 then emp
         else A.live ptr (cap.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr pb.pts ∗
           memRegion (ptr + BitVec.ofNat 64 (pb.pts.length * 24))
             ((cap.toNat - pb.pts.length) * 24)) ∗
        ((d + protoPolynomialDecoderPtsNeededOff) ↦₃₂ pb.ptsNeeded) ∗
        ((d + protoPolynomialDecoderPolysOff) ↦₃₂ pb.polys) ∗
        ((d + protoPolynomialDecoderIsCompleteOff) ↦₈ boolByte pb.isComplete) ∗
        memRegion (d + protoPolynomialDecoderPadOff) protoPolynomialDecoderPadSize)) = _ by ac_rfl))
  exact Entails.pure_right hp (Entails.refl _)

theorem v7_cleanup_opt_decoder_some_pre (A : RustAlloc) (fsp pbA cap_dec : BitVec 64)
    (pb : ProtoPolynomialDecoder) (Frame : SepProp) :
    stackAt fsp encoderFromPbStack ∗
      (((pbA + 184#64) ↦₆₄ cap_dec) ∗
       v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec (some pb)) ∗
      A.pool ∗ Frame ⊢
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
       A.pool ∗ Frame) := by
  unfold v7_optProtoPolyDecoderTail
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
        A.pool ∗ Frame)) by ac_rfl)) ?_
  apply Entails.pure_left; intro hp
  refine Entails.pure_right hp ?_
  exact Entails.trans (sepConj_mono_left htl) (Entails.of_eq (by ac_rfl))

/-- Cleanup of `Option<ProtoPolynomialDecoder>` at `+4548` (`0x5b268 -> +4632`):
given `x22 = cap_dec`, `x27 = pbA`, and `(pbA + 184#64 ↦₆₄ cap_dec) ∗ v7_optProtoPolyDecoderTail`,
deallocates `optDec` if `some` and reaches `+4632` with `memRegion (pbA + 184#64) 40`. -/
theorem v7_cleanup_opt_decoder_4548
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s1 : State) (out pbA cap_dec x28_val : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder) (Frame : SepProp)
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
        sm.readReg64 .x28 = x28_val ∧
        TraceCalleeSaved sm s0) := by
  cases optDec with
  | none =>
    unfold v7_optDecoderCapProp at hcap_dec
    subst hcap_dec
    unfold v7_optProtoPolyDecoderTail
    states_from_pb_fetches_range b (Rust.withPanics ext) 4548 8
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
          (((pbA + 184#64) ↦₆₄ 18446744073709551615#64) ∗
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
        sm.readReg64 .x28 = x28_val ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · have hne := v4_ptsCap_add_one_ne_zero hpts_cap_lt
      states_from_pb_fetches_range b (Rust.withPanics ext) 4548 8
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      wp_steps
      refine Drop.align_pre (by ac_rfl) ?_
      wp_done
    · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, hx27_2, hx28_2, htr2⟩
      exact v7_proto_decoder_dealloc_4556 hA s0 s2 out pbA cap_dec ptsPtr x28_val pb.pts Frame
        hsp0_align hpts_le hpts_cap_lt hpc2 hrun2 hsp2 hx19_2 hx22_2 hx27_2 hx28_2 htr2

theorem v7_stackAt_encoderFromPbStack_to_dropStack48 (fsp : BitVec 64) :
    stackAt fsp encoderFromPbStack ⊢
      stackAt fsp dropStack48 ∗ memRegion (fsp - 5152#64) 1008 := by
  have h := ProofLib.stackAt_split_bottom fsp dropStack48 1008 (by decide)
  change stackAt fsp encoderFromPbStack =
    memRegion (fsp - 5152#64) 1008 ∗ stackAt fsp dropStack48 at h
  rw [h]
  exact Entails.of_eq (by ac_rfl)

theorem v7_stackAt_dropStack48_to_encoderFromPbStack (fsp : BitVec 64) :
    stackAt fsp dropStack48 ∗ memRegion (fsp - 5152#64) 1008 ⊢
      stackAt fsp encoderFromPbStack := by
  have h := ProofLib.stackAt_split_bottom fsp dropStack48 1008 (by decide)
  change stackAt fsp encoderFromPbStack =
    memRegion (fsp - 5152#64) 1008 ∗ stackAt fsp dropStack48 at h
  rw [h]
  exact Entails.of_eq (by ac_rfl)

/-- Helper for `+4544 -> +4548` (`bl 0x4c500`): calls `drop_glue::<ProtoPolynomialEncoder>`
    with `x0 = pbA + 128#64`. -/
theorem v7_call_drop_proto_poly_encoder_4544
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s1 : State) (out pbA cap_dec x28_val : BitVec 64)
    (enc : ProtoPolynomialEncoder) (Frame : SepProp)
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
        protoPolynomialEncoderAt A (pbA + 128#64) enc ∗
        A.pool ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (pbA + 128#64) 56 ∗
          A.pool ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = x28_val ∧
        TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hdrop := v7_sub_ok_drop_proto_poly_encoder hA
  simp only [dropProtoPolyEncoderSpec] at hdrop
  refine SepWP.weaken_pre
    (sepConj_mono_left (v7_stackAt_encoderFromPbStack_to_dropStack48 (s0.sp - 2400#64))) ?_
  states_from_pb_fetches_range b (Rust.withPanics ext) 4544 4
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, protoPolynomialEncoderSize,
    BitVec.ofNat_eq_ofNat] at hdrop hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  wp_steps
  wp_apply
  refine EncoderFromPb.align_pre ?_ ?_
  · have hst := v7_stackAt_dropStack48_to_encoderFromPbStack (s0.sp - 2400#64)
    have haddr : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
    rw [haddr] at hst
    nth_rw 1 [← hsp1] at hst
    refine Entails.trans
      (Entails.of_eq (show _ =
        (stackAt s1.sp dropStack48 ∗ memRegion (s0.sp - 7552#64) 1008) ∗
        (memRegion (pbA + 128#64) 56 ∗ A.pool ∗ Frame) by ac_rfl)) ?_
    exact sepConj_mono_left hst
  · wp_done

theorem v7_expose_some_protoPolyEncoder_pre (A : RustAlloc) (fsp pbA : BitVec 64)
    (enc : ProtoPolynomialEncoder) (Mid Frame : SepProp) :
    stackAt fsp encoderFromPbStack ∗
      protoPolynomialEncoderAt A (pbA + 128#64) enc ∗
      Mid ∗ A.pool ∗ Frame ⊢
    ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
      ⌜cap.toNat < 2 ^ 63⌝ ∗
      (stackAt fsp encoderFromPbStack ∗
       ((pbA + 128#64) ↦₆₄ cap) ∗
       protoPolynomialEncoderRestAt A (pbA + 128#64) cap ptr enc ∗
       Mid ∗ A.pool ∗ Frame) := by
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_left (protoPolynomialEncoderAt_expose_cap A (pbA + 128#64) enc))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro cap
  refine Entails.sepExists_right cap ?_
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right ptr ?_
  exact Entails.of_eq (by ac_rfl)

/-- Cleanup at `+4528 -> +4632` (`0x5b254 -> 0x5b2bc`):
drops `optEnc` at `pbA + 128#64` and `optDec` at `pbA + 184#64`, preserving `x28`. -/
theorem v7_cleanup_4528
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s1 : State) (out pbA cap_dec x28_val : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder)
    (optDec : Option ProtoPolynomialDecoder)
    (Frame : SepProp)
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
        optProtoPolynomialEncoderAt A (pbA + 128#64) optEnc ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗
        A.pool ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (pbA + 128#64) 56 ∗
          memRegion (pbA + 184#64) 40 ∗
          A.pool ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = x28_val ∧
        TraceCalleeSaved sm s0) := by
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4548#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      (((pbA + 184#64) ↦₆₄ cap_dec) ∗
       v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗
      A.pool ∗
      (memRegion (pbA + 128#64) 56 ∗ Frame))
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = cap_dec ∧
      sm.readReg64 .x27 = pbA ∧
      sm.readReg64 .x28 = x28_val ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · cases optEnc with
    | none =>
      rw [optProtoPolynomialEncoderAt_none']
      states_from_pb_fetches_range b (Rust.withPanics ext) 4528 16
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, noneCap, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · have hm := optProtoPolyEncoder_none_entails_memRegion_56 (pbA + 128#64)
        dsimp only [noneCap] at hm
        refine Entails.trans
          (Entails.of_eq (show _ =
            (((pbA + 128#64) ↦₆₄ 18446744073709551615#64) ∗
             memRegion ((pbA + 128#64) + 8#64) 48) ∗
            (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
             (((pbA + 184#64) ↦₆₄ cap_dec) ∗
              v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗
             A.pool ∗ Frame) by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hm) (Entails.of_eq (by ac_rfl))
      · wp_done
    | some enc =>
      rw [optProtoPolynomialEncoderAt_some']
      refine SepWP.weaken_pre
        (v7_expose_some_protoPolyEncoder_pre A (s0.sp - 2400#64) pbA enc
          (((pbA + 184#64) ↦₆₄ cap_dec) ∗
           v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) Frame) ?_
      apply ProofLib.SepWP.exists_left; intro cap_enc
      apply ProofLib.SepWP.exists_left; intro ptr_enc
      apply ProofLib.SepWP.pure_elim; intro hcap_enc
      refine EncoderFromPb.seq_clean
        (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4544#64)
        (P_mid :=
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          protoPolynomialEncoderAt A (pbA + 128#64) enc ∗
          A.pool ∗
          ((((pbA + 184#64) ↦₆₄ cap_dec) ∗
            v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗ Frame))
        (Q := fun sm =>
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x0 = pbA + 128#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x22 = cap_dec ∧
          sm.readReg64 .x27 = pbA ∧
          sm.readReg64 .x28 = x28_val ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · have hne := cap_add_one_beq_zero_false hcap_enc
        states_from_pb_fetches_range b (Rust.withPanics ext) 4528 16
        dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
        generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
          "<spqr::v1::chunked::states::States>::from_pb" = entry
        examples_hide_fetches
        wp_steps
        refine EncoderFromPb.align_pre ?_ ?_
        · have hunexp := protoPolynomialEncoderAt_unexpose_cap A (pbA + 128#64) cap_enc ptr_enc enc
          refine Entails.trans
            (Entails.of_eq (show _ =
              (((pbA + 128#64) ↦₆₄ cap_enc) ∗
               protoPolynomialEncoderRestAt A (pbA + 128#64) cap_enc ptr_enc enc) ∗
              (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
               A.pool ∗
               ((((pbA + 184#64) ↦₆₄ cap_dec) ∗
                 v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗ Frame)) by ac_rfl)) ?_
          exact Entails.trans (sepConj_mono_left hunexp) (Entails.of_eq (by ac_rfl))
        · wp_done
      · intro s2 hpc2 hrun2 ⟨hsp2, hx0_2, hx19_2, hx22_2, hx27_2, hx28_2, htr2⟩
        have hcall := v7_call_drop_proto_poly_encoder_4544 hA s0 s2 out pbA cap_dec x28_val enc
          ((((pbA + 184#64) ↦₆₄ cap_dec) ∗
            v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗ Frame)
          hsp0_align hpc2 hrun2 hsp2 hx0_2 hx19_2 hx22_2 hx27_2 hx28_2 htr2
        refine SepWP.mono hcall ?_
        intro sf Pf _ _ ⟨hPf, hrest⟩
        exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hrest⟩
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, hx27_2, hx28_2, htr2⟩
    have h4548 := v7_cleanup_opt_decoder_4548 hA s0 s2 out pbA cap_dec x28_val optDec
      (memRegion (pbA + 128#64) 56 ∗ Frame)
      hcap_dec hsp0_align hpc2 hrun2 hsp2 hx19_2 hx22_2 hx27_2 hx28_2 htr2
    refine SepWP.mono h4548 ?_
    intro sf Pf _ _ ⟨hPf, hrest⟩
    exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hrest⟩

/-- Cleanup at `+5444 -> +4632` (`0x5b5e8 -> 0x5b2bc`):
executes `lsr x23, x28, #8`, drops `optEnc` at `pbA + 128#64` and `optDec` at `pbA + 184#64`,
preserving `x28`. -/
theorem v7_cleanup_5444
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s1 : State) (out pbA cap_dec x28_val : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder)
    (optDec : Option ProtoPolynomialDecoder)
    (Frame : SepProp)
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
        optProtoPolynomialEncoderAt A (pbA + 128#64) optEnc ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗
        A.pool ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (pbA + 128#64) 56 ∗
          memRegion (pbA + 184#64) 40 ∗
          A.pool ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = x28_val ∧
        TraceCalleeSaved sm s0) := by
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4548#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      (((pbA + 184#64) ↦₆₄ cap_dec) ∗
       v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗
      A.pool ∗
      (memRegion (pbA + 128#64) 56 ∗ Frame))
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = cap_dec ∧
      sm.readReg64 .x27 = pbA ∧
      sm.readReg64 .x28 = x28_val ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · cases optEnc with
    | none =>
      rw [optProtoPolynomialEncoderAt_none']
      states_from_pb_fetches_range b (Rust.withPanics ext) 5444 24
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, noneCap, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · have hm := optProtoPolyEncoder_none_entails_memRegion_56 (pbA + 128#64)
        dsimp only [noneCap] at hm
        refine Entails.trans
          (Entails.of_eq (show _ =
            (((pbA + 128#64) ↦₆₄ 18446744073709551615#64) ∗
             memRegion ((pbA + 128#64) + 8#64) 48) ∗
            (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
             (((pbA + 184#64) ↦₆₄ cap_dec) ∗
              v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗
             A.pool ∗ Frame) by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hm) (Entails.of_eq (by ac_rfl))
      · wp_done
    | some enc =>
      rw [optProtoPolynomialEncoderAt_some']
      refine SepWP.weaken_pre
        (v7_expose_some_protoPolyEncoder_pre A (s0.sp - 2400#64) pbA enc
          (((pbA + 184#64) ↦₆₄ cap_dec) ∗
           v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) Frame) ?_
      apply ProofLib.SepWP.exists_left; intro cap_enc
      apply ProofLib.SepWP.exists_left; intro ptr_enc
      apply ProofLib.SepWP.pure_elim; intro hcap_enc
      refine EncoderFromPb.seq_clean
        (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4544#64)
        (P_mid :=
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          protoPolynomialEncoderAt A (pbA + 128#64) enc ∗
          A.pool ∗
          ((((pbA + 184#64) ↦₆₄ cap_dec) ∗
            v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗ Frame))
        (Q := fun sm =>
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x0 = pbA + 128#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x22 = cap_dec ∧
          sm.readReg64 .x27 = pbA ∧
          sm.readReg64 .x28 = x28_val ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · have hne := cap_add_one_beq_zero_false hcap_enc
        states_from_pb_fetches_range b (Rust.withPanics ext) 5444 20
        dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
        generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
          "<spqr::v1::chunked::states::States>::from_pb" = entry
        examples_hide_fetches
        wp_steps
        refine EncoderFromPb.align_pre ?_ ?_
        · have hunexp := protoPolynomialEncoderAt_unexpose_cap A (pbA + 128#64) cap_enc ptr_enc enc
          refine Entails.trans
            (Entails.of_eq (show _ =
              (((pbA + 128#64) ↦₆₄ cap_enc) ∗
               protoPolynomialEncoderRestAt A (pbA + 128#64) cap_enc ptr_enc enc) ∗
              (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
               A.pool ∗
               ((((pbA + 184#64) ↦₆₄ cap_dec) ∗
                 v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗ Frame)) by ac_rfl)) ?_
          exact Entails.trans (sepConj_mono_left hunexp) (Entails.of_eq (by ac_rfl))
        · wp_done
      · intro s2 hpc2 hrun2 ⟨hsp2, hx0_2, hx19_2, hx22_2, hx27_2, hx28_2, htr2⟩
        have hcall := v7_call_drop_proto_poly_encoder_4544 hA s0 s2 out pbA cap_dec x28_val enc
          ((((pbA + 184#64) ↦₆₄ cap_dec) ∗
            v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗ Frame)
          hsp0_align hpc2 hrun2 hsp2 hx0_2 hx19_2 hx22_2 hx27_2 hx28_2 htr2
        refine SepWP.mono hcall ?_
        intro sf Pf _ _ ⟨hPf, hrest⟩
        exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hrest⟩
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, hx27_2, hx28_2, htr2⟩
    have h4548 := v7_cleanup_opt_decoder_4548 hA s0 s2 out pbA cap_dec x28_val optDec
      (memRegion (pbA + 128#64) 56 ∗ Frame)
      hcap_dec hsp0_align hpc2 hrun2 hsp2 hx19_2 hx22_2 hx27_2 hx28_2 htr2
    refine SepWP.mono h4548 ?_
    intro sf Pf _ _ ⟨hPf, hrest⟩
    exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hrest⟩

/-! ## 2. Cleanup at `+11112 -> +4632` and `+11096 -> +4632` (`<PolyDecoder>::from_pb = Err`) -/

/-- Step `+11112 -> +4632` (`mov w28, wzr; b +4632`): sets `x28 = 0#64` (`spqrErrorByte .encoding`
is `0#8`) and jumps to `+4632`. -/
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
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  states_from_pb_fetches_range b (Rust.withPanics ext) 11112 8
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  wp_steps
  wp_done

theorem v7_stackAt_encoderFromPbStack_to_dropStack32 (fsp : BitVec 64) :
    stackAt fsp encoderFromPbStack ⊢
      stackAt fsp dropStack32 ∗ memRegion (fsp - 5152#64) 1024 := by
  have h := ProofLib.stackAt_split_bottom fsp dropStack32 1024 (by decide)
  change stackAt fsp encoderFromPbStack =
    memRegion (fsp - 5152#64) 1024 ∗ stackAt fsp dropStack32 at h
  rw [h]
  exact Entails.of_eq (by ac_rfl)

theorem v7_stackAt_dropStack32_to_encoderFromPbStack (fsp : BitVec 64) :
    stackAt fsp dropStack32 ∗ memRegion (fsp - 5152#64) 1024 ⊢
      stackAt fsp encoderFromPbStack := by
  have h := ProofLib.stackAt_split_bottom fsp dropStack32 1024 (by decide)
  change stackAt fsp encoderFromPbStack =
    memRegion (fsp - 5152#64) 1024 ∗ stackAt fsp dropStack32 at h
  rw [h]
  exact Entails.of_eq (by ac_rfl)

/-- Cleanup at `+11096 -> +4632` (`0x5cbfc -> 0x5b2bc`):
drops `polyEncoderAt A (fsp + 1392) enc` (`bl 0x4c5d0`), drops `unchunkedCt1SentAt A (fsp + 1264) uc`
(`bl 0x4c99c`), sets `x28 = 0#64`, and jumps to `+4632`. -/
theorem v7_cleanup_11096
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s1 : State) (out : BitVec 64)
    (enc : PolyEncoder) (uc : LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (Frame : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 11096#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        polyEncoderAt A ((s0.sp - 2400#64) + 1392#64) enc ∗
        unchunkedCt1SentAt A ((s0.sp - 2400#64) + 1264#64) uc ∗
        A.pool ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗
          memRegion ((s0.sp - 2400#64) + 1264#64) 128 ∗
          A.pool ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hdrop_enc := v7_sub_ok_drop_poly_encoder_local2 hA
  have hdrop_uc := v7_sub_ok_drop_unchunked_ct1_sent_local2 (F := F) hA
  simp only [dropGluePolyEncoderSpec, dropGluePoly16Stack] at hdrop_enc
  simp only [dropUnchunkedCt1SentSpec] at hdrop_uc
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 11112#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗
      memRegion ((s0.sp - 2400#64) + 1264#64) 128 ∗
      A.pool ∗
      Frame)
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · refine SepWP.weaken_pre
      (sepConj_mono_left (v7_stackAt_encoderFromPbStack_to_dropStack32 (s0.sp - 2400#64))) ?_
    have h1392 : (s0.sp - 2400#64) + 1392#64 = s0.sp - 1008#64 := by bv_omega
    have h1264 : (s0.sp - 2400#64) + 1264#64 = s0.sp - 1136#64 := by bv_omega
    have h7552 : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
    rw [h1392, h1264, h7552]
    states_from_pb_fetches_range b (Rust.withPanics ext) 11096 16
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, polyEncoderSize, unchunkedCt1SentSize,
      BitVec.ofNat_eq_ofNat] at hdrop_enc hdrop_uc hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hdrop_enc hdrop_uc
    refine EncoderFromPb.seq_clean (mid := entry + 11104#64)
      (P_mid :=
        (stackAt (s0.sp - 2400#64) dropStack32 ∗ memRegion (s0.sp - 7552#64) 1024) ∗
        memRegion (s0.sp - 1008#64) 400 ∗
        unchunkedCt1SentAt A (s0.sp - 1136#64) uc ∗
        A.pool ∗
        Frame)
      (Q := fun sm =>
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · wp_steps
      wp_apply
      refine Drop.align_pre (by rw [hsp1]; ac_rfl) ?_
      wp_done
    · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, htr2⟩
      clear hdrop_enc
      rcases uc with ⟨epoch, ⟨rootKey, macKey⟩, hdr, es, ct1⟩
      wp_steps
      wp_apply
      refine EncoderFromPb.align_pre ?_ ?_
      · have hst := v7_stackAt_dropStack32_to_encoderFromPbStack (s0.sp - 2400#64)
        rw [h7552] at hst
        rw [hsp2]
        refine Entails.trans
          (Entails.of_eq (show _ =
            (stackAt (s0.sp - 2400#64) dropStack32 ∗ memRegion (s0.sp - 7552#64) 1024) ∗
            (memRegion (s0.sp - 1008#64) 400 ∗
             memRegion (s0.sp - 1136#64) 128 ∗
             A.pool ∗ Frame) by ac_rfl)) ?_
        exact sepConj_mono_left hst
      · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, htr2⟩
    exact v7_cleanup_11112 s0 s2 out _ hpc2 hrun2 hsp2 hx19_2 htr2

end CryptoVerification.SpqrV1.States.FromPb

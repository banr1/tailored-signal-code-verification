/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsa
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 2 (`HeaderSent`, `+508`) — Part B0

Shared error epilogues (`+4392`, `+4396`), bad-`ptsNeeded` cleanup (`+604..+688`), and
`Unchunked::EkSent` validation error cleanup (`+4660..+4748`).
-/

@[expose] public section

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open V1State.Chunked
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff libsignalSessionCode
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  statesFromPb_fnOff
  stubOff_rust_no_alloc_shim
  stubOff_rust_alloc
  stubOff_rust_dealloc
  stubOff_memcpy
  stubOff_handle_error

/-! ## `+4396 -> s0.x30` and `+4392 -> s0.x30` Shared Epilogues -/

theorem v2hs_memRegion_976_56_to_1032 (fsp : BitVec 64) :
    memRegion fsp 976 ∗ memRegion (fsp + 976#64) 56 ⊢ memRegion fsp 1032 :=
  collapse_top <| collapse_step0 (Entails.refl _) <| Entails.refl _

theorem v2hs_epilogue_4396_ret
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (s0 s : State) (out : BitVec 64) (err : LibsignalSpqrV1.Error)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder) (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4396#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64)
    (hx19 : s.readReg64 .x19 = out) (hx22 : s.readReg64 .x22 = d_w0)
    (hx23 : s.readReg64 .x23 = (spqrErrorByte err).zeroExtend 64) (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 976 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (s0.sp - 2400#64 + 1072#64) 1232 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out (.error (.err err)) ∗
          A.pool ∗ Rest ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  cases optEnc with
  | none =>
    dsimp only [v1_optProtoPolyEncoderHeap]
    wp_simp_pre [sepConj_assoc, sepConj_left_comm _ ⌜_⌝, sepConj_comm _ ⌜_⌝]
    apply SepWP.pure_elim; intro hw0; subst hw0
    have hstep :
        SepWP (tripleRatchetProgAtExt b ext)
          ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4420#64) s
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            memRegion (s0.sp - 2400#64) 976 ∗
            v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) noneCap w8 w16 w24 w32 w40 w48 ∗
            v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
            v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
            memRegion (s0.sp - 2400#64 + 1072#64) 1232 ∗
            statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest)
          (fun sm Pm =>
            (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
              memRegion (s0.sp - 2400#64) 1032 ∗
              v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
              v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
              memRegion (s0.sp - 2400#64 + 1072#64) 1232 ∗
              statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest) ∧
            sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
            sm.readReg64 .x22 = d_w0 ∧
            sm.readReg64 .x23 = (spqrErrorByte err).zeroExtend 64 ∧ TraceCalleeSaved sm s0) := by
      have h56 := v1_optProtoPolyEncoderWordsAt_entails_56 (s0.sp - 2400#64 + 976#64) noneCap w8 w16 w24 w32 w40 w48
      have h1032 := Entails.trans (sepConj_mono_right h56) (v2hs_memRegion_976_56_to_1032 (s0.sp - 2400#64))
      dsimp only [v1_optProtoPolyEncoderWordsAt] at h1032 ⊢
      states_from_pb_fetches_range b (Rust.withPanics ext) 4396 12
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · simp only [arm64_norm] at h1032 ⊢
        refine Entails.trans (Entails.of_eq (show _ =
          (memRegion (s0.sp - 2400#64) 976 ∗
           (((s0.sp - 1424#64) ↦₆₄ noneCap) ∗ ((s0.sp - 1416#64) ↦₆₄ w8) ∗
            ((s0.sp - 1408#64) ↦₆₄ w16) ∗ ((s0.sp - 1400#64) ↦₆₄ w24) ∗
            ((s0.sp - 1392#64) ↦₆₄ w32) ∗ ((s0.sp - 1384#64) ↦₆₄ w40) ∗
            ((s0.sp - 1376#64) ↦₆₄ w48))) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           v2hs_optProtoDecoderWordsAt (s0.sp - 1368#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
           v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
           memRegion (s0.sp - 1328#64) 1232 ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest) by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left h1032) (Entails.of_eq (by ac_rfl))
      · wp_done
    refine Drop.seq_clean (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4420#64)
      (P_mid := stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 1032 ∗
        v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (s0.sp - 2400#64 + 1072#64) 1232 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest)
      (Q := fun sm => sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d_w0 ∧
        sm.readReg64 .x23 = (spqrErrorByte err).zeroExtend 64 ∧ TraceCalleeSaved sm s0)
      hstep ?_
    intro sm hpcm hrunm ⟨hspm, hx19m, hx22m, hx23m, htrm⟩
    exact v2hs_epilogue_4420_ret (A := A) (F := F) hA s0 sm out err optDec d_w0 d_w8 d_w16 d_w24 d_w32 Rest
      hsp0_align hpcm hrunm hspm hx19m hx22m hx23m htrm
  | some pbEnc =>
    refine SepWP.weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
        (v1_optProtoPolyEncoderHeap_extract_w0 A pbEnc w0 w8 w16 w24 w32 w40 w48))))) ?_
    wp_simp_pre [sepConj_assoc, sepConj_left_comm _ ⌜_⌝, sepConj_comm _ ⌜_⌝]
    apply SepWP.pure_elim; intro hw0_ne
    have hcmn_f := cap_add_one_beq_zero_false hw0_ne
    have hpack := v1_optProtoPolyEncoderAt_pack_some A (s0.sp - 2400#64 + 976#64) pbEnc w0 w8 w16 w24 w32 w40 w48
    have hdrop := v1_drop_glue_proto_poly_encoder_ok_at_statesFromPb (b := b) (A := A) (ext := ext) hA
    simp only [dropProtoPolyEncoderSpec] at hdrop
    rw [v1_stackAt_encoder_split_dropStack48 (s0.sp - 2400#64)]
    have hstep :
        SepWP (tripleRatchetProgAtExt b ext)
          ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4420#64) s
          ((memRegion (s0.sp - 2400#64 - 5152#64) 1008 ∗ stackAt (s0.sp - 2400#64) dropStack48) ∗
            memRegion (s0.sp - 2400#64) 976 ∗
            v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
            v1_optProtoPolyEncoderHeap A (some pbEnc) w0 w8 w16 w24 w32 w40 w48 ∗
            v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
            v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
            memRegion (s0.sp - 2400#64 + 1072#64) 1232 ∗
            statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest)
          (fun sm Pm =>
            (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
              memRegion (s0.sp - 2400#64) 1032 ∗
              v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
              v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
              memRegion (s0.sp - 2400#64 + 1072#64) 1232 ∗
              statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest) ∧
            sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
            sm.readReg64 .x22 = d_w0 ∧
            sm.readReg64 .x23 = (spqrErrorByte err).zeroExtend 64 ∧ TraceCalleeSaved sm s0) := by
      have h1032 := v2hs_memRegion_976_56_to_1032 (s0.sp - 2400#64)
      have hstack := v1_stackAt_encoder_split_dropStack48 (s0.sp - 2400#64)
      dsimp only [v1_optProtoPolyEncoderWordsAt]
      states_from_pb_fetches_range b (Rust.withPanics ext) 4396 24
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc hdrop ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      wp_steps
      have hpre_pack :
          ((memRegion (s0.sp - 2400#64 - 5152#64) 1008 ∗ stackAt (s0.sp - 2400#64) dropStack48) ∗
           memRegion (s0.sp - 2400#64) 976 ∗
           (((s0.sp - 2400#64 + 976#64) ↦₆₄ w0) ∗ ((s0.sp - 2400#64 + 976#64 + 8#64) ↦₆₄ w8) ∗
            ((s0.sp - 2400#64 + 976#64 + 16#64) ↦₆₄ w16) ∗ ((s0.sp - 2400#64 + 976#64 + 24#64) ↦₆₄ w24) ∗
            ((s0.sp - 2400#64 + 976#64 + 32#64) ↦₆₄ w32) ∗ ((s0.sp - 2400#64 + 976#64 + 40#64) ↦₆₄ w40) ∗
            ((s0.sp - 2400#64 + 976#64 + 48#64) ↦₆₄ w48)) ∗
           (v1_optProtoPolyEncoderHeap A (some pbEnc) w0 w8 w16 w24 w32 w40 w48 ∗
            (v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
             (v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
              (memRegion (s0.sp - 2400#64 + 1072#64) 1232 ∗
               (statesFromPbSavedCells s0 ∗ (memRegion out chunkedStatesSize ∗ (A.pool ∗ Rest)))))))) ⊢
          protoPolynomialEncoderAt A (s0.sp - 2400#64 + 976#64) pbEnc ∗ A.pool ∗
          stackAt (s0.sp - 2400#64) dropStack48 ∗
          (memRegion (s0.sp - 2400#64 - 5152#64) 1008 ∗ memRegion (s0.sp - 2400#64) 976 ∗
           v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
           v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
           memRegion (s0.sp - 2400#64 + 1072#64) 1232 ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest) := by
        refine Entails.trans (Entails.of_eq (show _ =
          (v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
           v1_optProtoPolyEncoderHeap A (some pbEnc) w0 w8 w16 w24 w32 w40 w48) ∗
          (A.pool ∗ stackAt (s0.sp - 2400#64) dropStack48 ∗
           (memRegion (s0.sp - 2400#64 - 5152#64) 1008 ∗ memRegion (s0.sp - 2400#64) 976 ∗
            v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
            v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
            memRegion (s0.sp - 2400#64 + 1072#64) 1232 ∗
            statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest)) by
          dsimp only [v1_optProtoPolyEncoderWordsAt]; ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hpack) (Entails.of_eq (by ac_rfl))
      refine SepWP.weaken_pre hpre_pack ?_
      wp_apply
      refine EncoderFromPb.align_pre ?_ ?_
      · dsimp only [protoPolynomialEncoderSize]
        have h7552 : s0.sp - 2400#64 - 5152#64 = s0.sp - 7552#64 := by bv_omega
        rw [hsp, hstack, h7552]
        simp only [arm64_norm] at h1032 ⊢
        refine Entails.trans (Entails.of_eq (show _ =
          (memRegion (s0.sp - 7552#64) 1008 ∗ stackAt (s0.sp - 2400#64) dropStack48) ∗
          (memRegion (s0.sp - 2400#64) 976 ∗ memRegion (s0.sp - 1424#64) 56) ∗
          (v2hs_optProtoDecoderWordsAt (s0.sp - 1368#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
           v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
           memRegion (s0.sp - 1328#64) 1232 ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest) by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_right (sepConj_mono_left h1032)) (Entails.of_eq (by ac_rfl))
      · wp_done
    refine Drop.seq_clean (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4420#64)
      (P_mid := stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 1032 ∗
        v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (s0.sp - 2400#64 + 1072#64) 1232 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest)
      (Q := fun sm => sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d_w0 ∧
        sm.readReg64 .x23 = (spqrErrorByte err).zeroExtend 64 ∧ TraceCalleeSaved sm s0)
      hstep ?_
    intro sm hpcm hrunm ⟨hspm, hx19m, hx22m, hx23m, htrm⟩
    exact v2hs_epilogue_4420_ret (A := A) (F := F) hA s0 sm out err optDec d_w0 d_w8 d_w16 d_w24 d_w32 Rest
      hsp0_align hpcm hrunm hspm hx19m hx22m hx23m htrm

theorem v2hs_epilogue_4392_ret
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (s0 s : State) (out : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder) (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4392#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64)
    (hx19 : s.readReg64 .x19 = out) (hx22 : s.readReg64 .x22 = d_w0) (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 976 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (s0.sp - 2400#64 + 1072#64) 1232 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          A.pool ∗ Rest ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hstep :
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4396#64) s
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (s0.sp - 2400#64) 976 ∗
          v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
          v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
          v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
          v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
          memRegion (s0.sp - 2400#64 + 1072#64) 1232 ∗
          statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest)
        (fun sm Pm =>
          (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            memRegion (s0.sp - 2400#64) 976 ∗
            v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
            v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
            v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
            v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
            memRegion (s0.sp - 2400#64 + 1072#64) 1232 ∗
            statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
          sm.readReg64 .x22 = d_w0 ∧
          sm.readReg64 .x23 = (spqrErrorByte .stateDecode).zeroExtend 64 ∧ TraceCalleeSaved sm s0) := by
    states_from_pb_fetches_range b (Rust.withPanics ext) 4392 4
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    wp_steps
    wp_done
  refine Drop.seq_clean (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4396#64)
    (P_mid := stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 976 ∗
      v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
      v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
      v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
      v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
      memRegion (s0.sp - 2400#64 + 1072#64) 1232 ∗
      statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest)
    (Q := fun sm => sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = d_w0 ∧
      sm.readReg64 .x23 = (spqrErrorByte .stateDecode).zeroExtend 64 ∧ TraceCalleeSaved sm s0)
    hstep ?_
  intro sm hpcm hrunm ⟨hspm, hx19m, hx22m, hx23m, htrm⟩
  exact v2hs_epilogue_4396_ret (A := A) (F := F) hA s0 sm out .stateDecode
    optEnc w0 w8 w16 w24 w32 w40 w48 optDec d_w0 d_w8 d_w16 d_w24 d_w32 Rest
    hsp0_align hpcm hrunm hspm hx19m hx22m hx23m htrm

/-! ## Bad `ptsNeeded` Cleanup (`+604..+688 -> +4396 -> s0.x30`) -/

theorem v2hs_memRegion_896_ucWords_to_976
    (fsp u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 : BitVec 64) :
    memRegion fsp 896 ∗ v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ⊢
      memRegion fsp 976 := by
  have h80 := v2hs_ucWordsAt_entails_80 (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
  have h976 : memRegion fsp 896 ∗ memRegion (fsp + 896#64) 80 ⊢ memRegion fsp 976 :=
    collapse_top <| collapse_step0 (Entails.refl _) <| Entails.refl _
  exact Entails.trans (sepConj_mono_right h80) h976

theorem v2hs_vecU8Payload_entails_dealloc (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8Payload A cap ptr bs ⊢ ⌜cap.toNat < 2 ^ 63⌝ ∗ vecCapPtrDealloc A cap ptr := by
  dsimp only [vecU8Payload, vecCapPtrDealloc]
  apply Entails.pure_left
  rintro ⟨hle, hcap_lt, _⟩
  refine Entails.pure_right hcap_lt ?_
  by_cases hcap : cap = 0#64
  · have hbeq : (cap == 0#64) = true := by simp [hcap]
    simp only [hcap, hbeq, ↓reduceIte]
    exact Entails.refl emp
  · have hbeq : (cap == 0#64) = false := by simp [hcap]
    simp only [hcap, hbeq, Bool.false_eq_true, ↓reduceIte]
    have hsplit : cap.toNat = bs.length + (cap.toNat - bs.length) := by omega
    have hbound : bs.length + (cap.toNat - bs.length) ≤ 2 ^ 64 := by omega
    have hmr : memRegion ptr cap.toNat =
        memRegion ptr bs.length ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) := by
      conv_lhs => rw [hsplit]
      exact memRegion_split ptr bs.length (cap.toNat - bs.length) hbound
    refine Entails.trans (sepConj_mono_right (sepConj_mono_left (pointsToBytes_entails_memRegion ptr bs))) ?_
    rw [hmr]
    exact Entails.of_eq (by ac_rfl)

theorem v2hs_optProtoUcHeap_some_none_dealloc (A : RustAlloc) (dk : List (BitVec 8))
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 epoch : BitVec 64) :
    v4b_vecU8Heap A dk u8 u16 u24 ∗
    v1_optProtoAuthHeap A none u32 u40 u48 u56 u64 u72 ∗ ⌜u80 = epoch⌝ ⊢
      ⌜u8.toNat < 2 ^ 63 ∧ u32 = noneCap⌝ ∗ vecCapPtrDealloc A u8 u16 := by
  dsimp only [v4b_vecU8Heap, v1_optProtoAuthHeap]
  refine Entails.trans (sepConj_mono_left (sepConj_mono_right (v2hs_vecU8Payload_entails_dealloc A u8 u16 dk))) ?_
  simp only [sepConj_assoc]
  apply Entails.pure_left; rintro ⟨_, hu8_lt⟩
  apply Entails.pure_left; intro _
  rw [sepConj_left_comm (vecCapPtrDealloc A u8 u16) ⌜u32 = noneCap⌝]
  apply Entails.pure_left; intro hu32
  rw [sepConj_comm (vecCapPtrDealloc A u8 u16) ⌜u80 = epoch⌝]
  apply Entails.pure_left; intro _
  exact Entails.pure_right ⟨hu8_lt, hu32⟩ (Entails.refl _)

theorem v2hs_optProtoUcHeap_some_some_dealloc (A : RustAlloc) (dk : List (BitVec 8))
    (auth : ProtoAuthenticator)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 epoch : BitVec 64) :
    v4b_vecU8Heap A dk u8 u16 u24 ∗
    v1_optProtoAuthHeap A (some auth) u32 u40 u48 u56 u64 u72 ∗ ⌜u80 = epoch⌝ ⊢
      ⌜u8.toNat < 2 ^ 63 ∧ u32.toNat < 2 ^ 63⌝ ∗
      vecCapPtrDealloc A u8 u16 ∗ vecCapPtrDealloc A u32 u40 ∗ vecCapPtrDealloc A u56 u64 := by
  dsimp only [v4b_vecU8Heap, v1_optProtoAuthHeap]
  refine Entails.trans (sepConj_mono
    (sepConj_mono_right (v2hs_vecU8Payload_entails_dealloc A u8 u16 dk))
    (sepConj_mono_left (sepConj_mono_right (sepConj_mono
      (v2hs_vecU8Payload_entails_dealloc A u32 u40 auth.rootKey)
      (v2hs_vecU8Payload_entails_dealloc A u56 u64 auth.macKey))))) ?_
  simp only [sepConj_assoc]
  apply Entails.pure_left; rintro ⟨_, hu8_lt⟩
  apply Entails.pure_left; intro _
  rw [sepConj_left_comm (vecCapPtrDealloc A u8 u16) ⌜_⌝]
  apply Entails.pure_left; rintro ⟨hu32_lt, _, _⟩
  rw [sepConj_left_comm (vecCapPtrDealloc A u8 u16) ⌜_⌝]
  apply Entails.pure_left; intro _
  have hcomm :
      vecCapPtrDealloc A u8 u16 ∗ (vecCapPtrDealloc A u32 u40 ∗
        (⌜u56.toNat < 2 ^ 63⌝ ∗ (vecCapPtrDealloc A u56 u64 ∗ ⌜u80 = epoch⌝))) =
      ⌜u56.toNat < 2 ^ 63⌝ ∗ (⌜u80 = epoch⌝ ∗
        (vecCapPtrDealloc A u8 u16 ∗ vecCapPtrDealloc A u32 u40 ∗ vecCapPtrDealloc A u56 u64)) := by
    ac_rfl
  rw [hcomm]
  apply Entails.pure_left; intro _
  apply Entails.pure_left; intro _
  exact Entails.pure_right ⟨hu8_lt, hu32_lt⟩ (Entails.refl _)

theorem v2hs_err_uc_628_to_644
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (s0 s : State) (fsp out u8 u40 u32 d_w0 : BitVec 64) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 628#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx1 : s.readReg64 .x1 = u32) (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = u8) (hx22 : s.readReg64 .x22 = d_w0) (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 644#64) s
      (((fsp + 928#64) ↦₆₄ u40) ∗ vecCapPtrDealloc A u32 u40 ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ ((fsp + 928#64) ↦₆₄ u40) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x20 = u8 ∧
        sm.readReg64 .x22 = d_w0 ∧ TraceCalleeSaved sm s0) := by
  have hdealloc := v4_sub_ok_dealloc_125316 (b := b) (A := A) (ext := ext) hA
  simp only [rustDeallocSpec] at hdealloc
  states_from_pb_fetches_range b (Rust.withPanics ext) 628 16
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hdealloc hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  dsimp only [vecCapPtrDealloc]
  by_cases hcap : (u32 == 0#64) = true <;>
    simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
  · wp_steps; wp_done
  · wp_steps; wp_apply; refine Drop.align_pre (by rw [hsp]; ac_rfl) ?_; wp_done

theorem v2hs_err_uc_644_to_664
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (s0 s : State) (fsp out u8 u56 u64 d_w0 : BitVec 64) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 644#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = u8) (hx22 : s.readReg64 .x22 = d_w0) (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 664#64) s
      (((fsp + 944#64) ↦₆₄ u56) ∗ ((fsp + 952#64) ↦₆₄ u64) ∗ vecCapPtrDealloc A u56 u64 ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ ((fsp + 944#64) ↦₆₄ u56) ∗ ((fsp + 952#64) ↦₆₄ u64) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x20 = u8 ∧
        sm.readReg64 .x22 = d_w0 ∧ TraceCalleeSaved sm s0) := by
  have hdealloc := v4_sub_ok_dealloc_125316 (b := b) (A := A) (ext := ext) hA
  simp only [rustDeallocSpec] at hdealloc
  states_from_pb_fetches_range b (Rust.withPanics ext) 644 20
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hdealloc hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  dsimp only [vecCapPtrDealloc]
  by_cases hcap : (u56 == 0#64) = true <;>
    simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
  · wp_steps; wp_done
  · wp_steps; wp_apply; refine Drop.align_pre (by rw [hsp]; ac_rfl) ?_; wp_done

theorem v2hs_err_uc_664_to_4396
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (s0 s : State) (fsp out u8 u16 d_w0 : BitVec 64) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 664#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = u8) (hx22 : s.readReg64 .x22 = d_w0) (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4396#64) s
      (((fsp + 904#64) ↦₆₄ u16) ∗ vecCapPtrDealloc A u8 u16 ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ ((fsp + 904#64) ↦₆₄ u16) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x22 = d_w0 ∧
        sm.readReg64 .x23 = (spqrErrorByte .msgDecode).zeroExtend 64 ∧ TraceCalleeSaved sm s0) := by
  have hdealloc := v4_sub_ok_dealloc_125316 (b := b) (A := A) (ext := ext) hA
  simp only [rustDeallocSpec] at hdealloc
  states_from_pb_fetches_range b (Rust.withPanics ext) 664 28
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hdealloc hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  dsimp only [vecCapPtrDealloc]
  by_cases hcap : (u8 == 0#64) = true <;>
    simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
  · wp_steps; wp_done
  · wp_steps; wp_apply; wp_steps; refine Drop.align_pre (by rw [hsp]; ac_rfl) ?_; wp_done

theorem v2hs_err_uc_604_to_4396
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (s0 s : State) (fsp out d_w0 : BitVec 64)
    (optUc : Option V1State.Unchunked.EkSent)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 : BitVec 64) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 604#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx22 : s.readReg64 .x22 = d_w0) (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4396#64) s
      (v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
        v2hs_optProtoUcHeap A optUc u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 896#64) 80 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x22 = d_w0 ∧
        sm.readReg64 .x23 = (spqrErrorByte .msgDecode).zeroExtend 64 ∧ TraceCalleeSaved sm s0) := by
  cases optUc with
  | none =>
    dsimp only [v2hs_optProtoUcHeap]
    wp_simp_pre [sepConj_assoc, sepConj_left_comm _ ⌜_⌝, sepConj_comm _ ⌜_⌝]
    apply SepWP.pure_elim; intro hu8; subst hu8
    have h80 := v2hs_ucWordsAt_entails_80 (fsp + 896#64) noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80
    dsimp only [v2hs_ucWordsAt] at h80 ⊢
    states_from_pb_fetches_range b (Rust.withPanics ext) 604 12
    states_from_pb_fetches_range b (Rust.withPanics ext) 684 8
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · simp only [arm64_norm] at h80 ⊢
      refine Entails.trans (Entails.of_eq (show _ =
        (((fsp + 896#64) ↦₆₄ noneCap) ∗ ((fsp + 904#64) ↦₆₄ u16) ∗ ((fsp + 912#64) ↦₆₄ u24) ∗
         ((fsp + 920#64) ↦₆₄ u32) ∗ ((fsp + 928#64) ↦₆₄ u40) ∗ ((fsp + 936#64) ↦₆₄ u48) ∗
         ((fsp + 944#64) ↦₆₄ u56) ∗ ((fsp + 952#64) ↦₆₄ u64) ∗ ((fsp + 960#64) ↦₆₄ u72) ∗
         ((fsp + 968#64) ↦₆₄ u80)) ∗
        (A.pool ∗ stackAt fsp allocHookStack ∗ Frame) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left h80) (Entails.of_eq (by ac_rfl))
    · wp_done
  | some st =>
    dsimp only [v2hs_optProtoUcHeap]
    have h80 := v2hs_ucWordsAt_entails_80 (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
    cases hauth : st.auth with
    | none =>
      refine SepWP.weaken_pre
        (sepConj_mono_right (sepConj_mono_left
          (v2hs_optProtoUcHeap_some_none_dealloc A st.dk u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 st.epoch))) ?_
      wp_simp_pre [sepConj_assoc, sepConj_left_comm _ ⌜_⌝, sepConj_comm _ ⌜_⌝]
      apply SepWP.pure_elim; rintro ⟨hu8_lt, hu32⟩; subst hu32
      have hu8_ne := cap_add_one_beq_zero_false hu8_lt
      have h80' := v2hs_ucWordsAt_entails_80 (fsp + 896#64) u8 u16 u24 noneCap u40 u48 u56 u64 u72 u80
      let RestWords664 : SepProp :=
        ((fsp + 896#64) ↦₆₄ u8) ∗ ((fsp + 912#64) ↦₆₄ u24) ∗
        ((fsp + 920#64) ↦₆₄ noneCap) ∗ ((fsp + 928#64) ↦₆₄ u40) ∗ ((fsp + 936#64) ↦₆₄ u48) ∗
        ((fsp + 944#64) ↦₆₄ u56) ∗ ((fsp + 952#64) ↦₆₄ u64) ∗ ((fsp + 960#64) ↦₆₄ u72) ∗
        ((fsp + 968#64) ↦₆₄ u80) ∗ Frame
      have hstep604 :
          SepWP (tripleRatchetProgAtExt b ext)
            ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 664#64) s
            (v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 noneCap u40 u48 u56 u64 u72 u80 ∗
              (vecCapPtrDealloc A u8 u16 ∗ (A.pool ∗ (stackAt fsp allocHookStack ∗ Frame))))
            (fun sm Pm =>
              (Pm ⊢ ((fsp + 904#64) ↦₆₄ u16) ∗ vecCapPtrDealloc A u8 u16 ∗
                A.pool ∗ stackAt fsp allocHookStack ∗ RestWords664) ∧
              sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x20 = u8 ∧
              sm.readReg64 .x22 = d_w0 ∧ TraceCalleeSaved sm s0) := by
        dsimp only [v2hs_ucWordsAt, RestWords664]
        states_from_pb_fetches_range b (Rust.withPanics ext) 604 24
        dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
        generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
          "<spqr::v1::chunked::states::States>::from_pb" = entry
        examples_hide_fetches
        wp_steps
        refine Drop.align_pre (by simp only [arm64_norm]; ac_rfl) ?_
        wp_done
      refine Drop.seq_clean (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 664#64)
        (P_mid := ((fsp + 904#64) ↦₆₄ u16) ∗ vecCapPtrDealloc A u8 u16 ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ RestWords664)
        (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x20 = u8 ∧
          sm.readReg64 .x22 = d_w0 ∧ TraceCalleeSaved sm s0)
        hstep604 ?_
      intro s1 hpc1 hrun1 ⟨hsp1, hx19_1, hx20_1, hx22_1, htr1⟩
      have h664 := v2hs_err_uc_664_to_4396 hA s0 s1 fsp out u8 u16 d_w0 RestWords664
        hfsp_align hpc1 hrun1 hsp1 hx19_1 hx20_1 hx22_1 htr1
      refine SepWP.mono h664 fun sm Pm _ _ ⟨hPm, hspm, hx19m, hx22m, hx23m, htrm⟩ => ?_
      refine ⟨Entails.trans hPm ?_, hspm, hx19m, hx22m, hx23m, htrm⟩
      dsimp only [v2hs_ucWordsAt, RestWords664] at h80' ⊢
      simp only [arm64_norm] at h80' ⊢
      refine Entails.trans (Entails.of_eq (show _ =
        (((fsp + 896#64) ↦₆₄ u8) ∗ ((fsp + 904#64) ↦₆₄ u16) ∗ ((fsp + 912#64) ↦₆₄ u24) ∗
         ((fsp + 920#64) ↦₆₄ noneCap) ∗ ((fsp + 928#64) ↦₆₄ u40) ∗ ((fsp + 936#64) ↦₆₄ u48) ∗
         ((fsp + 944#64) ↦₆₄ u56) ∗ ((fsp + 952#64) ↦₆₄ u64) ∗ ((fsp + 960#64) ↦₆₄ u72) ∗
         ((fsp + 968#64) ↦₆₄ u80)) ∗
        (A.pool ∗ stackAt fsp allocHookStack ∗ Frame) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left h80') (Entails.of_eq (by ac_rfl))
    | some auth =>
      refine SepWP.weaken_pre
        (sepConj_mono_right (sepConj_mono_left
          (v2hs_optProtoUcHeap_some_some_dealloc A st.dk auth u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 st.epoch))) ?_
      wp_simp_pre [sepConj_assoc, sepConj_left_comm _ ⌜_⌝, sepConj_comm _ ⌜_⌝]
      apply SepWP.pure_elim; rintro ⟨hu8_lt, hu32_lt⟩
      have hu8_ne := cap_add_one_beq_zero_false hu8_lt
      have hu32_ne := cap_add_one_beq_zero_false hu32_lt
      let RestWords628 : SepProp :=
        ((fsp + 896#64) ↦₆₄ u8) ∗ ((fsp + 904#64) ↦₆₄ u16) ∗ ((fsp + 912#64) ↦₆₄ u24) ∗
        ((fsp + 920#64) ↦₆₄ u32) ∗ ((fsp + 936#64) ↦₆₄ u48) ∗
        ((fsp + 944#64) ↦₆₄ u56) ∗ ((fsp + 952#64) ↦₆₄ u64) ∗ ((fsp + 960#64) ↦₆₄ u72) ∗
        ((fsp + 968#64) ↦₆₄ u80) ∗
        vecCapPtrDealloc A u56 u64 ∗ vecCapPtrDealloc A u8 u16 ∗ Frame
      have hstep604 :
          SepWP (tripleRatchetProgAtExt b ext)
            ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 628#64) s
            (v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
              (vecCapPtrDealloc A u8 u16 ∗ (vecCapPtrDealloc A u32 u40 ∗
               (vecCapPtrDealloc A u56 u64 ∗ (A.pool ∗ (stackAt fsp allocHookStack ∗ Frame))))))
            (fun sm Pm =>
              (Pm ⊢ ((fsp + 928#64) ↦₆₄ u40) ∗ vecCapPtrDealloc A u32 u40 ∗
                A.pool ∗ stackAt fsp allocHookStack ∗ RestWords628) ∧
              sm.sp = fsp ∧ sm.readReg64 .x1 = u32 ∧ sm.readReg64 .x19 = out ∧
              sm.readReg64 .x20 = u8 ∧ sm.readReg64 .x22 = d_w0 ∧ TraceCalleeSaved sm s0) := by
        dsimp only [v2hs_ucWordsAt, RestWords628]
        states_from_pb_fetches_range b (Rust.withPanics ext) 604 24
        dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
        generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
          "<spqr::v1::chunked::states::States>::from_pb" = entry
        examples_hide_fetches
        wp_steps
        refine Drop.align_pre (by simp only [arm64_norm]; ac_rfl) ?_
        wp_done
      refine Drop.seq_clean (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 628#64)
        (P_mid := ((fsp + 928#64) ↦₆₄ u40) ∗ vecCapPtrDealloc A u32 u40 ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ RestWords628)
        (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x1 = u32 ∧ sm.readReg64 .x19 = out ∧
          sm.readReg64 .x20 = u8 ∧ sm.readReg64 .x22 = d_w0 ∧ TraceCalleeSaved sm s0)
        hstep604 ?_
      intro s1 hpc1 hrun1 ⟨hsp1, hx1_1, hx19_1, hx20_1, hx22_1, htr1⟩
      refine Drop.seq_clean (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 644#64)
        (P_mid := ((fsp + 928#64) ↦₆₄ u40) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ RestWords628)
        (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧
          sm.readReg64 .x20 = u8 ∧ sm.readReg64 .x22 = d_w0 ∧ TraceCalleeSaved sm s0)
        (v2hs_err_uc_628_to_644 hA s0 s1 fsp out u8 u40 u32 d_w0 RestWords628
          hfsp_align hpc1 hrun1 hsp1 hx1_1 hx19_1 hx20_1 hx22_1 htr1) ?_
      intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx20_2, hx22_2, htr2⟩
      let RestWords644 : SepProp :=
        ((fsp + 896#64) ↦₆₄ u8) ∗ ((fsp + 904#64) ↦₆₄ u16) ∗ ((fsp + 912#64) ↦₆₄ u24) ∗
        ((fsp + 920#64) ↦₆₄ u32) ∗ ((fsp + 928#64) ↦₆₄ u40) ∗ ((fsp + 936#64) ↦₆₄ u48) ∗
        ((fsp + 960#64) ↦₆₄ u72) ∗ ((fsp + 968#64) ↦₆₄ u80) ∗
        vecCapPtrDealloc A u8 u16 ∗ Frame
      have hre644 :
          (((fsp + 928#64) ↦₆₄ u40) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ RestWords628) =
          (((fsp + 944#64) ↦₆₄ u56) ∗ ((fsp + 952#64) ↦₆₄ u64) ∗ vecCapPtrDealloc A u56 u64 ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ RestWords644) := by
        dsimp only [RestWords628, RestWords644]; ac_rfl
      refine SepWP.weaken_pre (Entails.of_eq hre644) ?_
      refine Drop.seq_clean (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 664#64)
        (P_mid := ((fsp + 944#64) ↦₆₄ u56) ∗ ((fsp + 952#64) ↦₆₄ u64) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ RestWords644)
        (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧
          sm.readReg64 .x20 = u8 ∧ sm.readReg64 .x22 = d_w0 ∧ TraceCalleeSaved sm s0)
        (v2hs_err_uc_644_to_664 hA s0 s2 fsp out u8 u56 u64 d_w0 RestWords644
          hfsp_align hpc2 hrun2 hsp2 hx19_2 hx20_2 hx22_2 htr2) ?_
      intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx20_3, hx22_3, htr3⟩
      let RestWords664 : SepProp :=
        ((fsp + 896#64) ↦₆₄ u8) ∗ ((fsp + 912#64) ↦₆₄ u24) ∗
        ((fsp + 920#64) ↦₆₄ u32) ∗ ((fsp + 928#64) ↦₆₄ u40) ∗ ((fsp + 936#64) ↦₆₄ u48) ∗
        ((fsp + 944#64) ↦₆₄ u56) ∗ ((fsp + 952#64) ↦₆₄ u64) ∗ ((fsp + 960#64) ↦₆₄ u72) ∗
        ((fsp + 968#64) ↦₆₄ u80) ∗ Frame
      have hre664 :
          (((fsp + 944#64) ↦₆₄ u56) ∗ ((fsp + 952#64) ↦₆₄ u64) ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ RestWords644) =
          (((fsp + 904#64) ↦₆₄ u16) ∗ vecCapPtrDealloc A u8 u16 ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ RestWords664) := by
        dsimp only [RestWords644, RestWords664]; ac_rfl
      refine SepWP.weaken_pre (Entails.of_eq hre664) ?_
      have h664 := v2hs_err_uc_664_to_4396 hA s0 s3 fsp out u8 u16 d_w0 RestWords664
        hfsp_align hpc3 hrun3 hsp3 hx19_3 hx20_3 hx22_3 htr3
      refine SepWP.mono h664 fun sm Pm _ _ ⟨hPm, hspm, hx19m, hx22m, hx23m, htrm⟩ => ?_
      refine ⟨Entails.trans hPm ?_, hspm, hx19m, hx22m, hx23m, htrm⟩
      dsimp only [v2hs_ucWordsAt, RestWords664] at h80 ⊢
      simp only [arm64_norm] at h80 ⊢
      refine Entails.trans (Entails.of_eq (show _ =
        (((fsp + 896#64) ↦₆₄ u8) ∗ ((fsp + 904#64) ↦₆₄ u16) ∗ ((fsp + 912#64) ↦₆₄ u24) ∗
         ((fsp + 920#64) ↦₆₄ u32) ∗ ((fsp + 928#64) ↦₆₄ u40) ∗ ((fsp + 936#64) ↦₆₄ u48) ∗
         ((fsp + 944#64) ↦₆₄ u56) ∗ ((fsp + 952#64) ↦₆₄ u64) ∗ ((fsp + 960#64) ↦₆₄ u72) ∗
         ((fsp + 968#64) ↦₆₄ u80)) ∗
        (A.pool ∗ stackAt fsp allocHookStack ∗ Frame) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left h80) (Entails.of_eq (by ac_rfl))

theorem v2hs_err_uc_604_to_ret
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (s0 s : State) (out : BitVec 64)
    (optUc : Option V1State.Unchunked.EkSent)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder) (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 604#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64)
    (hx19 : s.readReg64 .x19 = out) (hx22 : s.readReg64 .x22 = d_w0) (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 896 ∗
        v2hs_ucWordsAt (s0.sp - 2400#64 + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
        v2hs_optProtoUcHeap A optUc u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (s0.sp - 2400#64 + 1072#64) 1232 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out (.error (.err .msgDecode)) ∗
          A.pool ∗ Rest ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  let fsp := s0.sp - 2400#64
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  rw [stackAt_encoderFromPb_split_allocHook fsp]
  let Frame604 : SepProp :=
    memRegion (fsp - 5152#64) 1056 ∗ memRegion fsp 896 ∗
    v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
    v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
    v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    memRegion (fsp + 1072#64) 1232 ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest
  have hpre604 :
      ((memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack) ∗
        memRegion fsp 896 ∗
        v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
        v2hs_optProtoUcHeap A optUc u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (fsp + 1072#64) 1232 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest) =
      (v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
        v2hs_optProtoUcHeap A optUc u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame604) := by
    dsimp only [Frame604]; ac_rfl
  refine SepWP.weaken_pre (Entails.of_eq hpre604) ?_
  refine Drop.seq_clean (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4396#64)
    (P_mid := memRegion (fsp + 896#64) 80 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame604)
    (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x22 = d_w0 ∧
      sm.readReg64 .x23 = (spqrErrorByte .msgDecode).zeroExtend 64 ∧ TraceCalleeSaved sm s0)
    (v2hs_err_uc_604_to_4396 hA s0 s fsp out d_w0 optUc u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 Frame604
      hfsp_align hpc hrun hsp hx19 hx22 htr) ?_
  intro sm hpcm hrunm ⟨hspm, hx19m, hx22m, hx23m, htrm⟩
  have h976 : memRegion fsp 896 ∗ memRegion (fsp + 896#64) 80 ⊢ memRegion fsp 976 :=
    collapse_top <| collapse_step0 (Entails.refl _) <| Entails.refl _
  have hpost604 :
      (memRegion (fsp + 896#64) 80 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame604) ⊢
      stackAt fsp encoderFromPbStack ∗
        memRegion fsp 976 ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (fsp + 1072#64) 1232 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest := by
    have hre :
        (memRegion (fsp + 896#64) 80 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame604) =
        (memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack) ∗
        (memRegion fsp 896 ∗ memRegion (fsp + 896#64) 80) ∗
        (v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
         v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ∗
         v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
         v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
         memRegion (fsp + 1072#64) 1232 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest) := by
      dsimp only [Frame604]; ac_rfl
    rw [← stackAt_encoderFromPb_split_allocHook fsp] at hre
    refine Entails.trans (Entails.of_eq hre) ?_
    exact Entails.trans (sepConj_mono_right (sepConj_mono_left h976)) (Entails.of_eq (by ac_rfl))
  refine SepWP.weaken_pre hpost604 ?_
  exact v2hs_epilogue_4396_ret (A := A) (F := F) hA s0 sm out .msgDecode
    optEnc w0 w8 w16 w24 w32 w40 w48 optDec d_w0 d_w8 d_w16 d_w24 d_w32 Rest
    hsp0_align hpcm hrunm hspm hx19m hx22m hx23m htrm

/-! ## `Unchunked::EkSent` Validation Error Cleanup (`+4660..+4748 -> +6852/+8916 -> +4396`) -/

theorem v2hs_optProtoAuthHeap_some_dealloc (A : RustAlloc) (auth : ProtoAuthenticator)
    (u32 u40 u48 u56 u64 u72 : BitVec 64) :
    v1_optProtoAuthHeap A (some auth) u32 u40 u48 u56 u64 u72 ⊢
      ⌜u32.toNat < 2 ^ 63⌝ ∗ vecCapPtrDealloc A u32 u40 ∗ vecCapPtrDealloc A u56 u64 := by
  dsimp only [v1_optProtoAuthHeap]
  refine Entails.trans (sepConj_mono_right (sepConj_mono
    (v2hs_vecU8Payload_entails_dealloc A u32 u40 auth.rootKey)
    (v2hs_vecU8Payload_entails_dealloc A u56 u64 auth.macKey))) ?_
  simp only [sepConj_assoc]
  apply Entails.pure_left; rintro ⟨hu32_lt, _, _⟩
  apply Entails.pure_left; intro _
  rw [sepConj_left_comm (vecCapPtrDealloc A u32 u40) ⌜_⌝]
  apply Entails.pure_left; intro _
  exact Entails.pure_right hu32_lt (Entails.refl _)

theorem v2hs_err_dk_8916_to_4396
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (s0 s : State) (fsp out u8 u16 d_w0 : BitVec 64) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hu8_ne : (u8 == 0#64) = false)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8916#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx22 : s.readReg64 .x22 = d_w0)
    (hx23 : s.readReg64 .x23 = (spqrErrorByte .stateDecode).zeroExtend 64)
    (hx24 : s.readReg64 .x24 = u8) (hx25 : s.readReg64 .x25 = u16) (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4396#64) s
      (((fsp + 200#64) ↦₆₄ noneCap) ∗ vecCapPtrDealloc A u8 u16 ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ ((fsp + 200#64) ↦₆₄ noneCap) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x22 = d_w0 ∧
        sm.readReg64 .x23 = (spqrErrorByte .stateDecode).zeroExtend 64 ∧ TraceCalleeSaved sm s0) := by
  have hdealloc := v4_sub_ok_dealloc_125316 (b := b) (A := A) (ext := ext) hA
  simp only [rustDeallocSpec] at hdealloc
  states_from_pb_fetches_range b (Rust.withPanics ext) 8916 28
  states_from_pb_fetches_range b (Rust.withPanics ext) 9148 4
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hdealloc hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  dsimp only [vecCapPtrDealloc, noneCap]
  simp only [hu8_ne, Bool.false_eq_true, ↓reduceIte]
  wp_steps
  wp_apply
  wp_steps
  refine Drop.align_pre (by rw [hsp]; ac_rfl) ?_
  wp_done

theorem v2hs_err_uc_4720_to_4396
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (s0 s : State) (fsp out u8 u16 w176 w200 d_w0 : BitVec 64) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4720#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx9 : s.readReg64 .x9 = u16) (hx19 : s.readReg64 .x19 = out)
    (hx22 : s.readReg64 .x22 = d_w0) (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4396#64) s
      (((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 176#64) ↦₆₄ w176) ∗ ((fsp + 200#64) ↦₆₄ w200) ∗
        vecCapPtrDealloc A u8 u16 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ ((fsp + 152#64) ↦₆₄ u8) ∗ memRegion (fsp + 176#64) 8 ∗ memRegion (fsp + 200#64) 8 ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x22 = d_w0 ∧
        sm.readReg64 .x23 = (spqrErrorByte .stateDecode).zeroExtend 64 ∧ TraceCalleeSaved sm s0) := by
  by_cases hcap : (u8 == 0#64) = true
  · dsimp only [vecCapPtrDealloc]
    simp only [hcap, ↓reduceIte, emp_sepConj]
    states_from_pb_fetches_range b (Rust.withPanics ext) 4720 12
    states_from_pb_fetches_range b (Rust.withPanics ext) 6852 4
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · have h176 := Drop.pointsTo64_entails_memRegion (fsp + 176#64) w176
      have h200 := Drop.pointsTo64_entails_memRegion (fsp + 200#64) w200
      refine Entails.trans (Entails.of_eq (show _ =
        ((fsp + 176#64) ↦₆₄ w176) ∗ ((fsp + 200#64) ↦₆₄ w200) ∗
        (((fsp + 152#64) ↦₆₄ u8) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono h176 (sepConj_mono_left h200)) (Entails.of_eq (by ac_rfl))
    · wp_done
  · have hcap_f : (u8 == 0#64) = false := Bool.eq_false_iff.mpr hcap
    have hstep4720 :
        SepWP (tripleRatchetProgAtExt b ext)
          ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8916#64) s
          (((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 176#64) ↦₆₄ w176) ∗ ((fsp + 200#64) ↦₆₄ w200) ∗
            vecCapPtrDealloc A u8 u16 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ ((fsp + 200#64) ↦₆₄ noneCap) ∗ vecCapPtrDealloc A u8 u16 ∗
              A.pool ∗ stackAt fsp allocHookStack ∗
              (((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗ Frame)) ∧
            sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x22 = d_w0 ∧
            sm.readReg64 .x23 = (spqrErrorByte .stateDecode).zeroExtend 64 ∧
            sm.readReg64 .x24 = u8 ∧ sm.readReg64 .x25 = u16 ∧ TraceCalleeSaved sm s0) := by
      states_from_pb_fetches_range b (Rust.withPanics ext) 4720 32
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, noneCap, BitVec.ofNat_eq_ofNat] at hpc ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      wp_steps
      refine Drop.align_pre (by ac_rfl) ?_
      wp_done
    refine Drop.seq_clean (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8916#64)
      (P_mid := ((fsp + 200#64) ↦₆₄ noneCap) ∗ vecCapPtrDealloc A u8 u16 ∗
        A.pool ∗ stackAt fsp allocHookStack ∗
        (((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗ Frame))
      (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x22 = d_w0 ∧
        sm.readReg64 .x23 = (spqrErrorByte .stateDecode).zeroExtend 64 ∧
        sm.readReg64 .x24 = u8 ∧ sm.readReg64 .x25 = u16 ∧ TraceCalleeSaved sm s0)
      hstep4720 ?_
    intro s1 hpc1 hrun1 ⟨hsp1, hx19_1, hx22_1, hx23_1, hx24_1, hx25_1, htr1⟩
    have h8916 := v2hs_err_dk_8916_to_4396 hA s0 s1 fsp out u8 u16 d_w0
      (((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗ Frame)
      hfsp_align hcap_f hpc1 hrun1 hsp1 hx19_1 hx22_1 hx23_1 hx24_1 hx25_1 htr1
    refine SepWP.mono h8916 fun sm Pm _ _ ⟨hPm, hspm, hx19m, hx22m, hx23m, htrm⟩ => ?_
    refine ⟨Entails.trans hPm ?_, hspm, hx19m, hx22m, hx23m, htrm⟩
    have h176 := Drop.pointsTo64_entails_memRegion (fsp + 176#64) u16
    have h200 := Drop.pointsTo64_entails_memRegion (fsp + 200#64) noneCap
    refine Entails.trans (Entails.of_eq (show _ =
      ((fsp + 176#64) ↦₆₄ u16) ∗ ((fsp + 200#64) ↦₆₄ noneCap) ∗
      (((fsp + 152#64) ↦₆₄ u8) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono h176 (sepConj_mono_left h200)) (Entails.of_eq (by ac_rfl))

theorem v2hs_err_uc_4668_to_4692
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (s0 s : State) (fsp out u16 u32 u40 u56 u64 d_w0 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4668#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = u40) (hx9 : s.readReg64 .x9 = u16)
    (hx19 : s.readReg64 .x19 = out) (hx22 : s.readReg64 .x22 = d_w0)
    (hx24 : s.readReg64 .x24 = u56) (hx25 : s.readReg64 .x25 = u64)
    (hx26 : s.readReg64 .x26 = u32) (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4692#64) s
      (vecCapPtrDealloc A u32 u40 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = fsp ∧ sm.readReg64 .x9 = u16 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d_w0 ∧ sm.readReg64 .x24 = u56 ∧
        sm.readReg64 .x25 = u64 ∧ TraceCalleeSaved sm s0) := by
  have hdealloc := v4_sub_ok_dealloc_125316 (b := b) (A := A) (ext := ext) hA
  simp only [rustDeallocSpec] at hdealloc
  states_from_pb_fetches_range b (Rust.withPanics ext) 4668 24
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hdealloc hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  dsimp only [vecCapPtrDealloc]
  by_cases hcap : (u32 == 0#64) = true <;>
    simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
  · wp_steps; wp_done
  · wp_steps; wp_apply; wp_steps; refine Drop.align_pre (by rw [hsp]) ?_; wp_done

theorem v2hs_err_uc_4692_to_4720
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (s0 s : State) (fsp out u16 u56 u64 d_w0 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4692#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx9 : s.readReg64 .x9 = u16) (hx19 : s.readReg64 .x19 = out)
    (hx22 : s.readReg64 .x22 = d_w0) (hx24 : s.readReg64 .x24 = u56)
    (hx25 : s.readReg64 .x25 = u64) (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4720#64) s
      (vecCapPtrDealloc A u56 u64 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = fsp ∧ sm.readReg64 .x9 = u16 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d_w0 ∧ TraceCalleeSaved sm s0) := by
  have hdealloc := v4_sub_ok_dealloc_125316 (b := b) (A := A) (ext := ext) hA
  simp only [rustDeallocSpec] at hdealloc
  states_from_pb_fetches_range b (Rust.withPanics ext) 4692 28
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hdealloc hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  dsimp only [vecCapPtrDealloc]
  by_cases hcap : (u56 == 0#64) = true <;>
    simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
  · wp_steps; wp_done
  · wp_steps; wp_apply; wp_steps; refine Drop.align_pre (by rw [hsp]) ?_; wp_done

theorem v2hs_err_uc_4660_to_4720
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (s0 s : State) (fsp out u16 u32 u40 u48 u56 u64 u72 d_w0 : BitVec 64)
    (optAuth : Option ProtoAuthenticator) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4660#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = u40) (hx9 : s.readReg64 .x9 = u16)
    (hx19 : s.readReg64 .x19 = out) (hx22 : s.readReg64 .x22 = d_w0)
    (hx24 : s.readReg64 .x24 = u56) (hx25 : s.readReg64 .x25 = u64)
    (hx26 : s.readReg64 .x26 = u32) (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4720#64) s
      (v1_optProtoAuthHeap A optAuth u32 u40 u48 u56 u64 u72 ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = fsp ∧ sm.readReg64 .x9 = u16 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d_w0 ∧ TraceCalleeSaved sm s0) := by
  cases optAuth with
  | none =>
    dsimp only [v1_optProtoAuthHeap]
    apply SepWP.pure_elim; intro hu32; subst hu32
    states_from_pb_fetches_range b (Rust.withPanics ext) 4660 8
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, noneCap, BitVec.ofNat_eq_ofNat] at hpc hx26 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    wp_steps
    wp_done
  | some auth =>
    refine SepWP.weaken_pre
      (sepConj_mono_left (v2hs_optProtoAuthHeap_some_dealloc A auth u32 u40 u48 u56 u64 u72)) ?_
    wp_simp_pre [sepConj_assoc]
    apply SepWP.pure_elim; intro hu32_lt
    have hu32_ne := cap_add_one_beq_zero_false hu32_lt
    have hstep4660 :
        SepWP (tripleRatchetProgAtExt b ext)
          ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4668#64) s
          (vecCapPtrDealloc A u32 u40 ∗ (vecCapPtrDealloc A u56 u64 ∗
            (A.pool ∗ (stackAt fsp allocHookStack ∗ Frame))))
          (fun sm Pm =>
            (Pm ⊢ vecCapPtrDealloc A u32 u40 ∗ A.pool ∗ stackAt fsp allocHookStack ∗
              (vecCapPtrDealloc A u56 u64 ∗ Frame)) ∧
            sm.sp = fsp ∧ sm.readReg64 .x0 = u40 ∧ sm.readReg64 .x9 = u16 ∧
            sm.readReg64 .x19 = out ∧ sm.readReg64 .x22 = d_w0 ∧
            sm.readReg64 .x24 = u56 ∧ sm.readReg64 .x25 = u64 ∧
            sm.readReg64 .x26 = u32 ∧ TraceCalleeSaved sm s0) := by
      states_from_pb_fetches_range b (Rust.withPanics ext) 4660 8
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      wp_steps
      refine Drop.align_pre (by ac_rfl) ?_
      wp_done
    refine Drop.seq_clean (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4668#64)
      (P_mid := vecCapPtrDealloc A u32 u40 ∗ A.pool ∗ stackAt fsp allocHookStack ∗
        (vecCapPtrDealloc A u56 u64 ∗ Frame))
      (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x0 = u40 ∧ sm.readReg64 .x9 = u16 ∧
        sm.readReg64 .x19 = out ∧ sm.readReg64 .x22 = d_w0 ∧
        sm.readReg64 .x24 = u56 ∧ sm.readReg64 .x25 = u64 ∧
        sm.readReg64 .x26 = u32 ∧ TraceCalleeSaved sm s0)
      hstep4660 ?_
    intro s1 hpc1 hrun1 ⟨hsp1, hx0_1, hx9_1, hx19_1, hx22_1, hx24_1, hx25_1, hx26_1, htr1⟩
    refine Drop.seq_clean (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4692#64)
      (P_mid := A.pool ∗ stackAt fsp allocHookStack ∗ (vecCapPtrDealloc A u56 u64 ∗ Frame))
      (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x9 = u16 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d_w0 ∧ sm.readReg64 .x24 = u56 ∧
        sm.readReg64 .x25 = u64 ∧ TraceCalleeSaved sm s0)
      (v2hs_err_uc_4668_to_4692 hA s0 s1 fsp out u16 u32 u40 u56 u64 d_w0
        (vecCapPtrDealloc A u56 u64 ∗ Frame)
        hfsp_align hpc1 hrun1 hsp1 hx0_1 hx9_1 hx19_1 hx22_1 hx24_1 hx25_1 hx26_1 htr1) ?_
    intro s2 hpc2 hrun2 ⟨hsp2, hx9_2, hx19_2, hx22_2, hx24_2, hx25_2, htr2⟩
    refine SepWP.weaken_pre (Entails.of_eq (show
      (A.pool ∗ stackAt fsp allocHookStack ∗ (vecCapPtrDealloc A u56 u64 ∗ Frame)) =
      (vecCapPtrDealloc A u56 u64 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) by ac_rfl)) ?_
    exact v2hs_err_uc_4692_to_4720 hA s0 s2 fsp out u16 u56 u64 d_w0 Frame
      hfsp_align hpc2 hrun2 hsp2 hx9_2 hx19_2 hx22_2 hx24_2 hx25_2 htr2

theorem v2hs_err_uc_4660_to_4396
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (s0 s : State)
    (fsp out u8 u16 u32 u40 u48 u56 u64 u72 w176 w200 d_w0 : BitVec 64)
    (optAuth : Option ProtoAuthenticator) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4660#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = u40) (hx9 : s.readReg64 .x9 = u16)
    (hx19 : s.readReg64 .x19 = out) (hx22 : s.readReg64 .x22 = d_w0)
    (hx24 : s.readReg64 .x24 = u56) (hx25 : s.readReg64 .x25 = u64)
    (hx26 : s.readReg64 .x26 = u32) (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4396#64) s
      (((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 176#64) ↦₆₄ w176) ∗ ((fsp + 200#64) ↦₆₄ w200) ∗
        vecCapPtrDealloc A u8 u16 ∗ v1_optProtoAuthHeap A optAuth u32 u40 u48 u56 u64 u72 ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ ((fsp + 152#64) ↦₆₄ u8) ∗ memRegion (fsp + 176#64) 8 ∗ memRegion (fsp + 200#64) 8 ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x22 = d_w0 ∧
        sm.readReg64 .x23 = (spqrErrorByte .stateDecode).zeroExtend 64 ∧ TraceCalleeSaved sm s0) := by
  let Frame4660 : SepProp :=
    ((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 176#64) ↦₆₄ w176) ∗ ((fsp + 200#64) ↦₆₄ w200) ∗
    vecCapPtrDealloc A u8 u16 ∗ Frame
  refine SepWP.weaken_pre (Entails.of_eq (show
    (((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 176#64) ↦₆₄ w176) ∗ ((fsp + 200#64) ↦₆₄ w200) ∗
      vecCapPtrDealloc A u8 u16 ∗ v1_optProtoAuthHeap A optAuth u32 u40 u48 u56 u64 u72 ∗
      A.pool ∗ stackAt fsp allocHookStack ∗ Frame) =
    (v1_optProtoAuthHeap A optAuth u32 u40 u48 u56 u64 u72 ∗
      A.pool ∗ stackAt fsp allocHookStack ∗ Frame4660) by dsimp only [Frame4660]; ac_rfl)) ?_
  refine Drop.seq_clean (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4720#64)
    (P_mid := A.pool ∗ stackAt fsp allocHookStack ∗ Frame4660)
    (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x9 = u16 ∧ sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = d_w0 ∧ TraceCalleeSaved sm s0)
    (v2hs_err_uc_4660_to_4720 hA s0 s fsp out u16 u32 u40 u48 u56 u64 u72 d_w0 optAuth Frame4660
      hfsp_align hpc hrun hsp hx0 hx9 hx19 hx22 hx24 hx25 hx26 htr) ?_
  intro s1 hpc1 hrun1 ⟨hsp1, hx9_1, hx19_1, hx22_1, htr1⟩
  refine SepWP.weaken_pre (Entails.of_eq (show
    (A.pool ∗ stackAt fsp allocHookStack ∗ Frame4660) =
    (((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 176#64) ↦₆₄ w176) ∗ ((fsp + 200#64) ↦₆₄ w200) ∗
      vecCapPtrDealloc A u8 u16 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) by
      dsimp only [Frame4660]; ac_rfl)) ?_
  exact v2hs_err_uc_4720_to_4396 hA s0 s1 fsp out u8 u16 w176 w200 d_w0 Frame
    hfsp_align hpc1 hrun1 hsp1 hx9_1 hx19_1 hx22_1 htr1

end CryptoVerification.SpqrV1.States.FromPb

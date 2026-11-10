/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4K
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10a
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4Ext
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-! # `<spqr::v1::chunked::states::States>::from_pb`: 4-KiB Hook Wrapper for `Variant3b` -/

namespace CryptoVerification.SpqrV1.States.FromPb.Ext4K

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoVerification.SpqrV1.Alloc

open CryptoVerification.SpqrV1.States.FromPb

open CryptoGames.LibsignalSession (ShaCompress Crypto)

open CryptoVerification.RustHeap

open CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalSpqrV1

open CryptoVerification.SpqrV1.Poly

open CryptoVerification.SpqrV1.Poly.EncoderFromPb

open CryptoVerification.SpqrV1.Drop

open CryptoVerification.SpqrV1.Auth

open CryptoVerification.SpqrV1.Unchunked

open CryptoVerification.SpqrV1.ProtoRepr

open CryptoVerification.CodeLayout

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff libsignalSessionCode

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  statesFromPb_fnOff
  fnOff_drop_proto_poly_encoder
  fnOff_ek_sent_ct1_received_from_pb
  fnOff_poly_encoder_from_pb
  stubOff_rust_no_alloc_shim
  stubOff_rust_alloc
  stubOff_rust_dealloc
  stubOff_memcpy
  stubOff_handle_error

theorem v3cr_sub_ok_drop_proto_poly_encoder_4192
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 18446744073709495388#64)
      (dropProtoPolyEncoderSpec A) :=
  sub_ok_of_addr_eq
    (by
      have hsub := v10_fnAddr_eq_sub_of_rel (Program.fnAddr_rel (k := 56228) (b := b) (X := Rust.withPanics ext)
        fnOff_drop_proto_poly_encoder statesFromPb_fnOff (by decide))
      change (tripleRatchetProgAtExt b ext).fnAddr dropProtoPolyEncoderName =
        (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName - 56228#64 at hsub
      rw [hsub]
      generalize_entry (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName = x
      rw [BitVec.sub_eq_add_neg]; rfl)
    (drop_glue_proto_poly_encoder_ok_ext (b := b) (A := A) (ext := ext) hA.dealloc)

/-- Error-cleanup path at `+4176` (`0x5b0f4 -> +4968 -> s0.x30`):
drops `optProtoPolynomialEncoderAt A (fsp + 1496) (sendingEk.map pbToProtoPolyEncoder)`
and exits via `+4968` with `err` in low byte of `x22`. -/
theorem v3cr_states_from_pb_err_4176
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (s0 s1 : State) (out : BitVec 64) (err : LibsignalSpqrV1.Error)
    (sendingEk : Option PolynomialEncoder) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4176#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : (s1.readReg64 .x22).extractLsb' 0 8 = spqrErrorByte err)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 1496 ∗
        optProtoPolynomialEncoderAt A ((s0.sp - 2400#64) + 1496#64)
          (sendingEk.map pbToProtoPolyEncoder) ∗
        memRegion ((s0.sp - 2400#64) + 1552#64) 752 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        A.pool ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out (.error (.err err)) ∗
          (A.pool ∗ Rest) ∗
          stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  cases sendingEk with
  | none =>
    simp only [Option.map_none]
    rw [optProtoPolynomialEncoderAt_none']
    have h1504 : ((s0.sp - 2400#64) + 1496#64) + 8#64 = (s0.sp - 2400#64) + 1504#64 := by bv_omega
    rw [h1504]
    refine EncoderFromPb.seq_clean
      (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4968#64)
      (P_mid :=
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        (A.pool ∗ Rest))
      (Q := fun sm =>
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        (sm.readReg64 .x22).extractLsb' 0 8 = spqrErrorByte err ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · states_from_pb_fetches_range b (Rust.withPanics ext) 4176 12
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, noneCap, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · have hfsp := v3cr_fsp_1496_none_entails_2304 (s0.sp - 2400#64)
        dsimp only [noneCap] at hfsp
        refine Entails.trans
          (Entails.of_eq (show _ =
            (memRegion (s0.sp - 2400#64) 1496 ∗
             (((s0.sp - 2400#64) + 1496#64) ↦₆₄ 18446744073709551615#64) ∗
             memRegion ((s0.sp - 2400#64) + 1504#64) 48 ∗
             memRegion ((s0.sp - 2400#64) + 1552#64) 752) ∗
            (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
             statesFromPbSavedCells s0 ∗
             memRegion out chunkedStatesSize ∗
             A.pool ∗ Rest) by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hfsp) (Entails.of_eq (by ac_rfl))
      · wp_done
    · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, htr2⟩
      exact v3cr_states_from_pb_err_4968 s0 s2 out err (A.pool ∗ Rest)
        hsp0_align hpc2 hrun2 hsp2 hx19_2 hx22_2 htr2
  | some pbEnc =>
    simp only [Option.map_some]
    refine SepWP.weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
        (v10_optProtoPolyEncoder_expose_cap A ((s0.sp - 2400#64) + 1496#64)
          (some (pbToProtoPolyEncoder pbEnc)))))) ?_
    wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply ProofLib.SepWP.exists_left; intro cap
    rw [show
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 1496 ∗
        ⌜v10_optEncoderCapProp cap (some (pbToProtoPolyEncoder pbEnc))⌝ ∗
        (((s0.sp - 2400#64) + 1496#64) ↦₆₄ cap) ∗
        v10_optProtoPolyEncoderTail A ((s0.sp - 2400#64) + 1496#64) cap
          (some (pbToProtoPolyEncoder pbEnc)) ∗
        memRegion ((s0.sp - 2400#64) + 1552#64) 752 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        A.pool ∗ Rest =
      ⌜v10_optEncoderCapProp cap (some (pbToProtoPolyEncoder pbEnc))⌝ ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 1496 ∗
        (((s0.sp - 2400#64) + 1496#64) ↦₆₄ cap) ∗
        v10_optProtoPolyEncoderTail A ((s0.sp - 2400#64) + 1496#64) cap
          (some (pbToProtoPolyEncoder pbEnc)) ∗
        memRegion ((s0.sp - 2400#64) + 1552#64) 752 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        A.pool ∗ Rest) by ac_rfl]
    apply ProofLib.SepWP.pure_elim; intro hcap_lt
    dsimp only [v10_optEncoderCapProp] at hcap_lt
    have hne_none := cap_add_one_beq_zero_false hcap_lt
    have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
      spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
    have hdrop := v3cr_sub_ok_drop_proto_poly_encoder_4192 hA
    simp only [dropProtoPolyEncoderSpec] at hdrop
    refine EncoderFromPb.seq_clean
      (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4968#64)
      (P_mid :=
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        (A.pool ∗ Rest))
      (Q := fun sm =>
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        (sm.readReg64 .x22).extractLsb' 0 8 = spqrErrorByte err ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · refine EncoderFromPb.seq_clean
        (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4196#64)
        (P_mid :=
          stackAt (s0.sp - 2400#64) dropStack48 ∗
          protoPolynomialEncoderAt A ((s0.sp - 2400#64) + 1496#64) (pbToProtoPolyEncoder pbEnc) ∗
          A.pool ∗
          (memRegion ((s0.sp - 2400#64) - 5152#64) 1008 ∗
           memRegion (s0.sp - 2400#64) 1496 ∗
           memRegion ((s0.sp - 2400#64) + 1552#64) 752 ∗
           statesFromPbSavedCells s0 ∗
           memRegion out chunkedStatesSize ∗ Rest))
        (Q := fun s2 =>
          s2.sp = s0.sp - 2400#64 ∧
          s2.readReg64 .x0 = (s0.sp - 2400#64) + 1496#64 ∧
          s2.readReg64 .x19 = out ∧
          (s2.readReg64 .x22).extractLsb' 0 8 = spqrErrorByte err ∧
          TraceCalleeSaved s2 s0)
        ?_ ?_
      · states_from_pb_fetches_range b (Rust.withPanics ext) 4176 20
        dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
        generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
          "<spqr::v1::chunked::states::States>::from_pb" = entry
        examples_hide_fetches
        wp_steps
        refine EncoderFromPb.align_pre ?_ ?_
        · have hunexp := v10_optProtoPolyEncoder_unexpose_cap A
            ((s0.sp - 2400#64) + 1496#64) cap (some (pbToProtoPolyEncoder pbEnc))
          rw [optProtoPolynomialEncoderAt_some'] at hunexp
          have hst := v10_stackAt_encoderFromPbStack_to_dropStack48 (s0.sp - 2400#64)
          refine Entails.trans
            (Entails.of_eq (show _ =
              ((((s0.sp - 2400#64) + 1496#64) ↦₆₄ cap) ∗
               v10_optProtoPolyEncoderTail A ((s0.sp - 2400#64) + 1496#64) cap
                 (some (pbToProtoPolyEncoder pbEnc))) ∗
              stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
              (memRegion (s0.sp - 2400#64) 1496 ∗
               memRegion ((s0.sp - 2400#64) + 1552#64) 752 ∗
               statesFromPbSavedCells s0 ∗
               memRegion out chunkedStatesSize ∗
               A.pool ∗ Rest) by ac_rfl)) ?_
          exact Entails.trans (sepConj_mono hunexp (sepConj_mono_left hst))
            (Entails.of_eq (by ac_rfl))
        · wp_done
      · intro s2 hpc2 hrun2 ⟨hsp2, hx0_2, hx19_2, hx22_2, htr2⟩
        states_from_pb_fetches_range b (Rust.withPanics ext) 4196 8
        dsimp only [tripleRatchetProgAtExt, statesFromPbName, protoPolynomialEncoderSize,
          BitVec.ofNat_eq_ofNat] at hdrop hpc2 hx0_2 ⊢
        generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
          "<spqr::v1::chunked::states::States>::from_pb" = entry
        examples_hide_fetches
        wp_steps
        wp_apply
        wp_steps
        refine EncoderFromPb.align_pre ?_ ?_
        · have hst := v10_stackAt_dropStack48_to_encoderFromPbStack (s0.sp - 2400#64)
          have haddr : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
          rw [haddr] at hst
          nth_rw 1 [← hsp2] at hst
          have hfsp := v3cr_fsp_1496_56_entails_2304 (s0.sp - 2400#64)
          have h1496 : (s0.sp - 2400#64) + 1496#64 = s0.sp - 904#64 := by bv_omega
          have h1552 : (s0.sp - 2400#64) + 1552#64 = s0.sp - 848#64 := by bv_omega
          rw [h1496, h1552] at hfsp
          refine Entails.trans
            (Entails.of_eq (show _ =
              (stackAt s2.sp dropStack48 ∗ memRegion (s0.sp - 7552#64) 1008) ∗
              (memRegion (s0.sp - 2400#64) 1496 ∗
               memRegion (s0.sp - 904#64) 56 ∗
               memRegion (s0.sp - 848#64) 752) ∗
              (statesFromPbSavedCells s0 ∗
               memRegion out chunkedStatesSize ∗
               A.pool ∗ Rest) by ac_rfl)) ?_
          exact Entails.trans (sepConj_mono hst (sepConj_mono_left hfsp))
            (Entails.of_eq (by ac_rfl))
        · have hx22_sf : sf.readReg64 .x22 = s2.readReg64 .x22 := by assumption
          wp_done
    · intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx22_3, htr3⟩
      exact v3cr_states_from_pb_err_4968 s0 s3 out err (A.pool ∗ Rest)
        hsp0_align hpc3 hrun3 hsp3 hx19_3 hx22_3 htr3

private theorem v3cr_vecCapPtrDealloc_zero (A : RustAlloc) {ca pa : BitVec 64}
    (h : (ca == 0#64) = true) :
    vecCapPtrDealloc A ca pa = emp := by
  simp only [vecCapPtrDealloc, h, ↓reduceIte]

private theorem v3cr_vecCapPtrDealloc_ne_zero (A : RustAlloc) {ca pa : BitVec 64}
    (h : ¬(ca == 0#64) = true) :
    vecCapPtrDealloc A ca pa = (A.live pa ca.toNat 1 ∗ memRegion pa ca.toNat) := by
  have hbeq : (ca == 0#64) = false := Bool.eq_false_iff.mpr h
  simp only [vecCapPtrDealloc, hbeq, Bool.false_eq_true, ↓reduceIte]

/-- Shared `+4924` error-cleanup path (`0x5b3e0 -> +4968`):
deallocates `vecCapPtrDealloc A ca3 pa3` (`x26 = ca3`, `[sp + 176] = pa3`) and
`vecCapPtrDealloc A ca4 pa4` (`[sp + 224] = ca4`, `x21 = pa4`), sets `x22 = 0`, and reaches `+4968`. -/
theorem v3cr_states_from_pb_err_4924
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (s0 s1 : State) (out ca3 pa3 ca4 pa4 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4924#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (hx21_1 : s1.readReg64 .x21 = pa4)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4968#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
        vecCapPtrDealloc A ca3 pa3 ∗
        vecCapPtrDealloc A ca4 pa4 ∗
        A.pool ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
          (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
          A.pool ∗
          Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hdealloc := v4_sub_ok_dealloc_125316 hA
  simp only [rustDeallocSpec] at hdealloc
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4944#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
      (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
      vecCapPtrDealloc A ca4 pa4 ∗
      A.pool ∗
      Rest)
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x21 = pa4 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · by_cases hca3 : (ca3 == 0#64) = true
    · rw [v3cr_vecCapPtrDealloc_zero A hca3]
      simp only [sepConj_emp, emp_sepConj]
      states_from_pb_fetches_range b (Rust.withPanics ext) 4924 4
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      wp_steps
      wp_done
    · rw [v3cr_vecCapPtrDealloc_ne_zero A hca3]
      simp only [sepConj_assoc]
      refine SepWP.weaken_pre
        (sepConj_mono_left (v10_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
      states_from_pb_fetches_range b (Rust.withPanics ext) 4924 20
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hdealloc hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      wp_steps
      wp_apply
      refine EncoderFromPb.align_pre ?_ ?_
      · have hst := v10_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
        have haddr : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
        have h176 : (s0.sp - 2400#64) + 176#64 = s0.sp - 2224#64 := by bv_omega
        have h224 : (s0.sp - 2400#64) + 224#64 = s0.sp - 2176#64 := by bv_omega
        rw [haddr] at hst
        nth_rw 1 [← hsp1] at hst
        rw [h176, h224]
        refine Entails.trans
          (Entails.of_eq (show _ =
            (stackAt s1.sp allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
            (((s0.sp - 2224#64) ↦₆₄ pa3) ∗
             ((s0.sp - 2176#64) ↦₆₄ ca4) ∗
             vecCapPtrDealloc A ca4 pa4 ∗
             A.pool ∗ Rest) by ac_rfl)) ?_
        exact sepConj_mono_left hst
      · wp_done
  ·
    intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx21_2, htr2⟩
    by_cases hca4 : (ca4 == 0#64) = true
    · rw [v3cr_vecCapPtrDealloc_zero A hca4]
      simp only [sepConj_emp, emp_sepConj]
      states_from_pb_fetches_range b (Rust.withPanics ext) 4944 24
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc2 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      wp_steps
      wp_done
    · rw [v3cr_vecCapPtrDealloc_ne_zero A hca4]
      simp only [sepConj_assoc]
      refine SepWP.weaken_pre
        (sepConj_mono_left (v10_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
      states_from_pb_fetches_range b (Rust.withPanics ext) 4944 24
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hdealloc hpc2 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      wp_steps
      wp_apply
      wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · have hst := v10_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
        have haddr : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
        have h176 : (s0.sp - 2400#64) + 176#64 = s0.sp - 2224#64 := by bv_omega
        have h224 : (s0.sp - 2400#64) + 224#64 = s0.sp - 2176#64 := by bv_omega
        rw [haddr] at hst
        nth_rw 1 [← hsp2] at hst
        rw [h176, h224]
        refine Entails.trans
          (Entails.of_eq (show _ =
            (stackAt s2.sp allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
            (((s0.sp - 2224#64) ↦₆₄ pa3) ∗
             ((s0.sp - 2176#64) ↦₆₄ ca4) ∗
             A.pool ∗ Rest) by ac_rfl)) ?_
        exact sepConj_mono_left hst
      · wp_done

/-- Shared `+4908` error-cleanup path (`0x5b3d0 -> +4968`):
deallocates `vecCapPtrDealloc A ca2 pa2` (`x28 = ca2`, `x0 = pa2`) and then chains to `+4924`. -/
theorem v3cr_states_from_pb_err_4908
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (s0 s1 : State) (out ca2 pa2 ca3 pa3 ca4 pa4 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4908#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx0_1 : s1.readReg64 .x0 = pa2)
    (hx28_1 : s1.readReg64 .x28 = ca2)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (hx21_1 : s1.readReg64 .x21 = pa4)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4968#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
        vecCapPtrDealloc A ca2 pa2 ∗
        vecCapPtrDealloc A ca3 pa3 ∗
        vecCapPtrDealloc A ca4 pa4 ∗
        A.pool ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
          (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
          A.pool ∗
          Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hdealloc := v4_sub_ok_dealloc_125316 hA
  simp only [rustDeallocSpec] at hdealloc
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4924#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
      (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
      vecCapPtrDealloc A ca3 pa3 ∗
      vecCapPtrDealloc A ca4 pa4 ∗
      A.pool ∗
      Rest)
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x26 = ca3 ∧
      sm.readReg64 .x21 = pa4 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · by_cases hca2 : (ca2 == 0#64) = true
    · rw [v3cr_vecCapPtrDealloc_zero A hca2]
      simp only [sepConj_emp, emp_sepConj]
      states_from_pb_fetches_range b (Rust.withPanics ext) 4908 4
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      wp_steps
      wp_done
    · rw [v3cr_vecCapPtrDealloc_ne_zero A hca2]
      simp only [sepConj_assoc]
      refine SepWP.weaken_pre
        (sepConj_mono_left (v10_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
      states_from_pb_fetches_range b (Rust.withPanics ext) 4908 16
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hdealloc hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      wp_steps
      wp_apply
      refine EncoderFromPb.align_pre ?_ ?_
      · have hst := v10_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
        have haddr : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
        have h176 : (s0.sp - 2400#64) + 176#64 = s0.sp - 2224#64 := by bv_omega
        have h224 : (s0.sp - 2400#64) + 224#64 = s0.sp - 2176#64 := by bv_omega
        rw [haddr] at hst
        nth_rw 1 [← hsp1] at hst
        rw [h176, h224]
        refine Entails.trans
          (Entails.of_eq (show _ =
            (stackAt s1.sp allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
            (((s0.sp - 2224#64) ↦₆₄ pa3) ∗
             ((s0.sp - 2176#64) ↦₆₄ ca4) ∗
             vecCapPtrDealloc A ca3 pa3 ∗
             vecCapPtrDealloc A ca4 pa4 ∗
             A.pool ∗ Rest) by ac_rfl)) ?_
        exact sepConj_mono_left hst
      · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx26_2, hx21_2, htr2⟩
    exact v3cr_states_from_pb_err_4924 hA s0 s2 out ca3 pa3 ca4 pa4 Rest
      hsp0_align hpc2 hrun2 hsp2 hx19_2 hx26_2 hx21_2 htr2

/-- Shared `+4884` error-cleanup path (`0x5b3b8 -> +4968`):
deallocates all 4 `EkSentCt1Received` vectors (`rootKey`, `macKey`, `dk`, `ct1`) when
`sendingEk = none`, sets `x22 = 0`, and reaches `+4968`. -/
theorem v3cr_states_from_pb_err_4884
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (s0 s1 : State) (out ca1 pa1 ca2 pa2 ca3 pa3 ca4 pa4 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4884#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx1_1 : s1.readReg64 .x1 = ca1)
    (hx22_1 : s1.readReg64 .x22 = pa1)
    (hx0_1 : s1.readReg64 .x0 = pa2)
    (hx28_1 : s1.readReg64 .x28 = ca2)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (hx21_1 : s1.readReg64 .x21 = pa4)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4968#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
        vecCapPtrDealloc A ca1 pa1 ∗
        vecCapPtrDealloc A ca2 pa2 ∗
        vecCapPtrDealloc A ca3 pa3 ∗
        vecCapPtrDealloc A ca4 pa4 ∗
        A.pool ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
          (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
          A.pool ∗
          Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hdealloc := v4_sub_ok_dealloc_125316 hA
  simp only [rustDeallocSpec] at hdealloc
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4908#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
      (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
      vecCapPtrDealloc A ca2 pa2 ∗
      vecCapPtrDealloc A ca3 pa3 ∗
      vecCapPtrDealloc A ca4 pa4 ∗
      A.pool ∗
      Rest)
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x0 = pa2 ∧
      sm.readReg64 .x28 = ca2 ∧
      sm.readReg64 .x26 = ca3 ∧
      sm.readReg64 .x21 = pa4 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · by_cases hca1 : (ca1 == 0#64) = true
    · rw [v3cr_vecCapPtrDealloc_zero A hca1]
      simp only [sepConj_emp, emp_sepConj]
      states_from_pb_fetches_range b (Rust.withPanics ext) 4884 4
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      wp_steps
      wp_done
    · rw [v3cr_vecCapPtrDealloc_ne_zero A hca1]
      simp only [sepConj_assoc]
      refine SepWP.weaken_pre
        (sepConj_mono_left (v10_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
      states_from_pb_fetches_range b (Rust.withPanics ext) 4884 24
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hdealloc hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      wp_steps
      wp_apply
      wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · have hst := v10_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
        have haddr : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
        have h176 : (s0.sp - 2400#64) + 176#64 = s0.sp - 2224#64 := by bv_omega
        have h224 : (s0.sp - 2400#64) + 224#64 = s0.sp - 2176#64 := by bv_omega
        rw [haddr] at hst
        nth_rw 1 [← hsp1] at hst
        rw [h176, h224]
        refine Entails.trans
          (Entails.of_eq (show _ =
            (stackAt s1.sp allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
            (((s0.sp - 2224#64) ↦₆₄ pa3) ∗
             ((s0.sp - 2176#64) ↦₆₄ ca4) ∗
             vecCapPtrDealloc A ca2 pa2 ∗
             vecCapPtrDealloc A ca3 pa3 ∗
             vecCapPtrDealloc A ca4 pa4 ∗
             A.pool ∗ Rest) by ac_rfl)) ?_
        exact sepConj_mono_left hst
      · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx0_2, hx28_2, hx26_2, hx21_2, htr2⟩
    exact v3cr_states_from_pb_err_4908 hA s0 s2 out ca2 pa2 ca3 pa3 ca4 pa4 Rest
      hsp0_align hpc2 hrun2 hsp2 hx19_2 hx0_2 hx28_2 hx26_2 hx21_2 htr2

/-- Shared `+1024` error-cleanup path (`0x5a4a4 -> +4968`):
deallocates all 4 `EkSentCt1Received` vectors when `<PolyEncoder>::from_pb` returns `Err`,
sets `x22 = 0`, and reaches `+4968`. -/
theorem v3cr_states_from_pb_err_1024
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (s0 s1 : State) (out ca1 pa1 ca2 pa2 ca3 pa3 ca4 pa4 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1024#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = pa1)
    (hx28_1 : s1.readReg64 .x28 = ca2)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (hx21_1 : s1.readReg64 .x21 = pa4)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4968#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
        (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
        vecCapPtrDealloc A ca1 pa1 ∗
        vecCapPtrDealloc A ca2 pa2 ∗
        vecCapPtrDealloc A ca3 pa3 ∗
        vecCapPtrDealloc A ca4 pa4 ∗
        A.pool ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
          (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
          (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
          (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
          A.pool ∗
          Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hdealloc := v4_sub_ok_dealloc_125316 hA
  simp only [rustDeallocSpec] at hdealloc
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1044#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
      (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
      (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
      (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
      vecCapPtrDealloc A ca2 pa2 ∗
      vecCapPtrDealloc A ca3 pa3 ∗
      vecCapPtrDealloc A ca4 pa4 ∗
      A.pool ∗
      Rest)
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x28 = ca2 ∧
      sm.readReg64 .x26 = ca3 ∧
      sm.readReg64 .x21 = pa4 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · by_cases hca1 : (ca1 == 0#64) = true
    · rw [v3cr_vecCapPtrDealloc_zero A hca1]
      simp only [sepConj_emp, emp_sepConj]
      states_from_pb_fetches_range b (Rust.withPanics ext) 1024 8
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      wp_steps
      wp_done
    · rw [v3cr_vecCapPtrDealloc_ne_zero A hca1]
      simp only [sepConj_assoc]
      refine SepWP.weaken_pre
        (sepConj_mono_left (v10_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
      states_from_pb_fetches_range b (Rust.withPanics ext) 1024 20
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hdealloc hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      wp_steps
      wp_apply
      refine EncoderFromPb.align_pre ?_ ?_
      · have hst := v10_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
        have haddr : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
        have h176 : (s0.sp - 2400#64) + 176#64 = s0.sp - 2224#64 := by bv_omega
        have h184 : (s0.sp - 2400#64) + 184#64 = s0.sp - 2216#64 := by bv_omega
        have h200 : (s0.sp - 2400#64) + 200#64 = s0.sp - 2200#64 := by bv_omega
        have h224 : (s0.sp - 2400#64) + 224#64 = s0.sp - 2176#64 := by bv_omega
        rw [haddr] at hst
        nth_rw 1 [← hsp1] at hst
        rw [h176, h184, h200, h224]
        refine Entails.trans
          (Entails.of_eq (show _ =
            (stackAt s1.sp allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
            (((s0.sp - 2200#64) ↦₆₄ ca1) ∗
             ((s0.sp - 2216#64) ↦₆₄ pa2) ∗
             ((s0.sp - 2224#64) ↦₆₄ pa3) ∗
             ((s0.sp - 2176#64) ↦₆₄ ca4) ∗
             vecCapPtrDealloc A ca2 pa2 ∗
             vecCapPtrDealloc A ca3 pa3 ∗
             vecCapPtrDealloc A ca4 pa4 ∗
             A.pool ∗ Rest) by ac_rfl)) ?_
        exact sepConj_mono_left hst
      · wp_done
  ·
    intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx28_2, hx26_2, hx21_2, htr2⟩
    by_cases hca2 : (ca2 == 0#64) = true
    · rw [v3cr_vecCapPtrDealloc_zero A hca2]
      simp only [sepConj_emp, emp_sepConj]
      refine EncoderFromPb.seq_clean
        (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4924#64)
        (P_mid :=
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
          (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
          vecCapPtrDealloc A ca3 pa3 ∗
          vecCapPtrDealloc A ca4 pa4 ∗
          A.pool ∗
          ((((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
           (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ Rest))
        (Q := fun sm =>
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x26 = ca3 ∧
          sm.readReg64 .x21 = pa4 ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · states_from_pb_fetches_range b (Rust.withPanics ext) 1044 4
        dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc2 ⊢
        generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
          "<spqr::v1::chunked::states::States>::from_pb" = entry
        examples_hide_fetches
        wp_steps
        refine EncoderFromPb.align_pre (Entails.of_eq (by ac_rfl)) ?_
        wp_done
      · intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx26_3, hx21_3, htr3⟩
        have h4924 := v3cr_states_from_pb_err_4924 hA s0 s3 out ca3 pa3 ca4 pa4
          ((((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
           (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ Rest)
          hsp0_align hpc3 hrun3 hsp3 hx19_3 hx26_3 hx21_3 htr3
        refine SepWP.mono h4924 ?_
        intro sf Pf _ _ ⟨hPf, hsp_f, hx19_f, hx22_f, htr_f⟩
        exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hx19_f, hx22_f, htr_f⟩
    · refine EncoderFromPb.seq_clean
        (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4912#64)
        (P_mid :=
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
          (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
          (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
          vecCapPtrDealloc A ca2 pa2 ∗
          vecCapPtrDealloc A ca3 pa3 ∗
          vecCapPtrDealloc A ca4 pa4 ∗
          A.pool ∗
          ((((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗ Rest))
        (Q := fun sm =>
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x0 = pa2 ∧
          sm.readReg64 .x28 = ca2 ∧
          sm.readReg64 .x26 = ca3 ∧
          sm.readReg64 .x21 = pa4 ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · states_from_pb_fetches_range b (Rust.withPanics ext) 1044 12
        dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc2 ⊢
        generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
          "<spqr::v1::chunked::states::States>::from_pb" = entry
        examples_hide_fetches
        wp_steps
        refine EncoderFromPb.align_pre ?_ ?_
        · have h184 : (s0.sp - 2400#64) + 184#64 = s0.sp - 2216#64 := by bv_omega
          rw [h184]
          exact Entails.of_eq (by ac_rfl)
        · wp_done
      · intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx0_3, hx28_3, hx26_3, hx21_3, htr3⟩
        refine EncoderFromPb.seq_clean
          (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4924#64)
          (P_mid :=
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
            (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
            vecCapPtrDealloc A ca3 pa3 ∗
            vecCapPtrDealloc A ca4 pa4 ∗
            A.pool ∗
            ((((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
             (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ Rest))
          (Q := fun sm =>
            sm.sp = s0.sp - 2400#64 ∧
            sm.readReg64 .x19 = out ∧
            sm.readReg64 .x26 = ca3 ∧
            sm.readReg64 .x21 = pa4 ∧
            TraceCalleeSaved sm s0)
          ?_ ?_
        · rw [v3cr_vecCapPtrDealloc_ne_zero A hca2]
          simp only [sepConj_assoc]
          refine SepWP.weaken_pre
            (sepConj_mono_left (v10_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
          states_from_pb_fetches_range b (Rust.withPanics ext) 4912 12
          dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hdealloc hpc3 ⊢
          generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
            "<spqr::v1::chunked::states::States>::from_pb" = entry
          examples_hide_fetches
          wp_steps
          wp_apply
          refine EncoderFromPb.align_pre ?_ ?_
          · have hst := v10_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
            have haddr : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
            have h176 : (s0.sp - 2400#64) + 176#64 = s0.sp - 2224#64 := by bv_omega
            have h184 : (s0.sp - 2400#64) + 184#64 = s0.sp - 2216#64 := by bv_omega
            have h200 : (s0.sp - 2400#64) + 200#64 = s0.sp - 2200#64 := by bv_omega
            have h224 : (s0.sp - 2400#64) + 224#64 = s0.sp - 2176#64 := by bv_omega
            rw [haddr] at hst
            nth_rw 1 [← hsp3] at hst
            rw [h176, h184, h200, h224]
            refine Entails.trans
              (Entails.of_eq (show _ =
                (stackAt s3.sp allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
                (((s0.sp - 2224#64) ↦₆₄ pa3) ∗
                 ((s0.sp - 2176#64) ↦₆₄ ca4) ∗
                 vecCapPtrDealloc A ca3 pa3 ∗
                 vecCapPtrDealloc A ca4 pa4 ∗
                 A.pool ∗
                 (((s0.sp - 2200#64) ↦₆₄ ca1) ∗
                  ((s0.sp - 2216#64) ↦₆₄ pa2) ∗ Rest)) by ac_rfl)) ?_
            exact sepConj_mono_left hst
          · wp_done
        · intro s4 hpc4 hrun4 ⟨hsp4, hx19_4, hx26_4, hx21_4, htr4⟩
          have h4924 := v3cr_states_from_pb_err_4924 hA s0 s4 out ca3 pa3 ca4 pa4
            ((((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
             (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ Rest)
            hsp0_align hpc4 hrun4 hsp4 hx19_4 hx26_4 hx21_4 htr4
          refine SepWP.mono h4924 ?_
          intro sf Pf _ _ ⟨hPf, hsp_f, hx19_f, hx22_f, htr_f⟩
          exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hx19_f, hx22_f, htr_f⟩

end CryptoVerification.SpqrV1.States.FromPb.Ext4K

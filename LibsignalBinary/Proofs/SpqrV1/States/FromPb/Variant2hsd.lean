/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Drop.PolyEncoder
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsc
import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBase
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 2 (`HeaderSent`, `+508`) — Part D

Cleanup blocks (`+9132`, `+9112`, `+11024`, `+11240 -> +9212/+9228`) for `InnerState.headerSent`.
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
set_option linter.unusedVariables false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff libsignalSessionCode
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  statesFromPb_fnOff
  fnOff_drop_poly16
  fnOff_drop_proto_poly_encoder
  fnOff_drop_poly_encoder_local2
  fnOff_drop_ek_sent
  fnOff_poly_encoder_from_pb
  fnOff_poly_decoder_from_pb
  stubOff_rust_no_alloc_shim
  stubOff_rust_alloc
  stubOff_rust_dealloc
  stubOff_memcpy
  stubOff_handle_error

@[local simp, local arm64_norm, local wp_norm]
theorem v2hsd_bv_add_add_lit (x : BitVec 64) (a b : Nat) :
    x + BitVec.ofNat 64 a + BitVec.ofNat 64 b = x + BitVec.ofNat 64 (a + b) := by
  bv_omega

/-! ## Subroutine Call Bridges -/

private theorem v2hsd_add_11028_sub_68860_eq (x : BitVec 64) :
    x + 11028#64 + 18446744073709482756#64 = x - 57832#64 := by bv_omega

theorem v2hsd_sub_ok_drop_poly16_11028 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 11028#64 + 18446744073709482756#64)
      (dropGluePoly16Spec A) :=
  sub_ok_of_addr_eq
    (by
      rw [v2hsd_add_11028_sub_68860_eq]
      exact v2hsc_fnAddr_eq_sub_of_rel (Program.fnAddr_rel (k := 57832) (b := b) (X := Rust.withPanics ext)
        fnOff_drop_poly16 statesFromPb_fnOff (by decide)))
    (drop_glue_poly16_ok_ext (b := b) (A := A) (ext := ext) hA.dealloc)

private theorem v2hsd_add_11244_sub_67264_eq (x : BitVec 64) :
    x + 11244#64 + 18446744073709484352#64 = x - 56020#64 := by bv_omega

theorem v2hsd_sub_ok_drop_poly_encoder_11244 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 11244#64 + 18446744073709484352#64)
      (dropGluePolyEncoderSpec A) :=
  sub_ok_of_addr_eq
    (by
      rw [v2hsd_add_11244_sub_67264_eq]
      exact v2hsc_fnAddr_eq_sub_of_rel (Program.fnAddr_rel (k := 56020) (b := b) (X := Rust.withPanics ext)
        fnOff_drop_poly_encoder_local2 statesFromPb_fnOff (by decide)))
    (drop_glue_poly_encoder_local2_ok_ext (b := b) (A := A) (ext := ext) hA.dealloc)

private theorem v2hsd_add_11252_sub_66164_eq (x : BitVec 64) :
    x + 11252#64 + 18446744073709485452#64 = x - 54912#64 := by bv_omega

theorem v2hsd_sub_ok_drop_unchunked_ek_sent_11252 {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 11252#64 + 18446744073709485452#64)
      (dropUnchunkedEkSentSpec A F) :=
  sub_ok_of_addr_eq
    (by
      rw [v2hsd_add_11252_sub_66164_eq]
      exact v2hsc_fnAddr_eq_sub_of_rel (Program.fnAddr_rel (k := 54912) (b := b) (X := Rust.withPanics ext)
        fnOff_drop_ek_sent statesFromPb_fnOff (by decide)))
    (drop_unchunked_ek_sent_ok_ext (b := b) (A := A) (F := F) (ext := ext) hA.dealloc)

theorem v2hsd_sub_ok_decoder_from_pb {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdec : DecoderFromPbOkExt b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 35448#64)
      (decoderFromPbSpec A) :=
  sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := 35448) (b := b) (X := Rust.withPanics ext)
      statesFromPb_fnOff fnOff_poly_decoder_from_pb (by decide))
    hdec

/-! ## Cleanup Paths (`+9132`, `+9112`, `+11256`, `+11240`, `+11024`) -/

/-- Cleanup at `+9132 -> +9212`: loads `ca2` from `[sp + 232]` and `pa2` from `[sp + 184]`,
deallocates `(ca2, pa2)` and `(ca3, pa3)`, and reaches `+9212`. -/
theorem v2hsd_cleanup_9132_to_9212
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s1 : State) (fsp out d0 ca2 pa2 ca3 pa3 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9132#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9212#64) s1
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        vecCapPtrDealloc A ca2 pa2 ∗
        vecCapPtrDealloc A ca3 pa3 ∗
        A.pool ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          ((fsp + 184#64) ↦₆₄ pa2) ∗
          ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          A.pool ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        TraceCalleeSaved sm s0) := by
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9192#64)
    (P_mid :=
      stackAt fsp encoderFromPbStack ∗
      ((fsp + 176#64) ↦₆₄ pa3) ∗
      vecCapPtrDealloc A ca3 pa3 ∗
      A.pool ∗
      (((fsp + 184#64) ↦₆₄ pa2) ∗
       ((fsp + 232#64) ↦₆₄ ca2) ∗ Frame))
    (Q := fun sm =>
      sm.sp = fsp ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = d0 ∧
      sm.readReg64 .x26 = ca3 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · by_cases hca2 : (ca2 == 0#64) = true
    · states_from_pb_fetches_range b (Rust.withPanics ext) 9132 16
      dsimp only [tripleRatchetProgAtExt, statesFromPbName, vecCapPtrDealloc,
        BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::v1::chunked::states::States>::from_pb" = entry
      examples_hide_fetches
      simp only [hca2, ↓reduceIte, emp_sepConj]
      wp_steps
      refine Drop.align_pre (by ac_rfl) ?_
      wp_done
    · have hca2_f : (ca2 == 0#64) = false := Bool.eq_false_iff.mpr hca2
      refine EncoderFromPb.seq_clean
        (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9184#64)
        (P_mid :=
          stackAt fsp encoderFromPbStack ∗
          vecCapPtrDealloc A ca2 pa2 ∗
          A.pool ∗
          (((fsp + 176#64) ↦₆₄ pa3) ∗
           vecCapPtrDealloc A ca3 pa3 ∗
           (((fsp + 184#64) ↦₆₄ pa2) ∗
            ((fsp + 232#64) ↦₆₄ ca2) ∗ Frame)))
        (Q := fun sm =>
          sm.sp = fsp ∧
          sm.readReg64 .x0 = pa2 ∧
          sm.readReg64 .x1 = ca2 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x22 = d0 ∧
          sm.readReg64 .x26 = ca3 ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · states_from_pb_fetches_range b (Rust.withPanics ext) 9132 16
        dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
        generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
          "<spqr::v1::chunked::states::States>::from_pb" = entry
        examples_hide_fetches
        wp_steps
        refine Drop.align_pre (by ac_rfl) ?_
        wp_done
      · intro s2 hpc2 hrun2 ⟨hsp2, hx0_2, hx1_2, hx19_2, hx22_2, hx26_2, htr2⟩
        have h9184 := v2hsc_cleanup_9184_to_9192 hA s0 s2 fsp out d0 ca2 pa2 ca3
          (((fsp + 176#64) ↦₆₄ pa3) ∗
           vecCapPtrDealloc A ca3 pa3 ∗
           (((fsp + 184#64) ↦₆₄ pa2) ∗
            ((fsp + 232#64) ↦₆₄ ca2) ∗ Frame))
          hca2_f hfsp_align hpc2 hrun2 hsp2 hx0_2 hx1_2 hx19_2 hx22_2 hx26_2 htr2
        exact SepWP.mono h9184 fun sm Pm _ _ ⟨hPm, hq⟩ =>
          ⟨Entails.trans hPm (Entails.of_eq (by ac_rfl)), hq⟩
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, hx26_2, htr2⟩
    have h9192 := v2hsc_cleanup_9192_to_9212 hA s0 s2 fsp out d0 ca3 pa3
      (((fsp + 184#64) ↦₆₄ pa2) ∗
       ((fsp + 232#64) ↦₆₄ ca2) ∗ Frame)
      hfsp_align hpc2 hrun2 hsp2 hx19_2 hx22_2 hx26_2 htr2
    exact SepWP.mono h9192 fun sm Pm _ _ ⟨hPm, hq⟩ =>
      ⟨Entails.trans hPm (Entails.of_eq (by ac_rfl)), hq⟩

/-- Cleanup at `+9112 -> +9212` (`<PolyEncoder>::from_pb = Err`): deallocates `(ca1, pa1)`
(`[sp + 200] = ca1`, `[sp + 1272] = pa1`), `(ca2, pa2)` (`[sp + 232] = ca2`, `[sp + 184] = pa2`),
and `(ca3, pa3)` (`x26 = ca3`, `[sp + 176] = pa3`). -/
theorem v2hsd_cleanup_9112_to_9212
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s1 : State) (fsp out d0 ca1 pa1 ca2 pa2 ca3 pa3 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9112#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9212#64) s1
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 200#64) ↦₆₄ ca1) ∗
        ((fsp + 1272#64) ↦₆₄ pa1) ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        vecCapPtrDealloc A ca1 pa1 ∗
        vecCapPtrDealloc A ca2 pa2 ∗
        vecCapPtrDealloc A ca3 pa3 ∗
        A.pool ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          ((fsp + 200#64) ↦₆₄ ca1) ∗
          ((fsp + 1272#64) ↦₆₄ pa1) ∗
          ((fsp + 184#64) ↦₆₄ pa2) ∗
          ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          A.pool ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        TraceCalleeSaved sm s0) := by
  have hdealloc := v2hsc_sub_ok_dealloc_125316 (b := b) (A := A) (ext := ext) hA
  simp only [rustDeallocSpec] at hdealloc
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9132#64)
    (P_mid :=
      stackAt fsp encoderFromPbStack ∗
      ((fsp + 184#64) ↦₆₄ pa2) ∗
      ((fsp + 232#64) ↦₆₄ ca2) ∗
      ((fsp + 176#64) ↦₆₄ pa3) ∗
      vecCapPtrDealloc A ca2 pa2 ∗
      vecCapPtrDealloc A ca3 pa3 ∗
      A.pool ∗
      (((fsp + 200#64) ↦₆₄ ca1) ∗
       ((fsp + 1272#64) ↦₆₄ pa1) ∗ Frame))
    (Q := fun sm =>
      sm.sp = fsp ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = d0 ∧
      sm.readReg64 .x26 = ca3 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · refine SepWP.weaken_pre
      (sepConj_mono_left (v2hsc_stackAt_encoderFromPbStack_to_allocHook fsp)) ?_
    have hst := v2hsc_stackAt_allocHook_to_encoderFromPbStack fsp
    states_from_pb_fetches_range b (Rust.withPanics ext) 9112 20
    rw [show vecCapPtrDealloc A ca1 pa1 =
      (if (ca1 == 0#64) = true then emp else A.live pa1 ca1.toNat 1 ∗ memRegion pa1 ca1.toNat) from rfl]
    dsimp only [tripleRatchetProgAtExt, statesFromPbName,
      BitVec.ofNat_eq_ofNat] at hdealloc hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    by_cases hca1 : (ca1 == 0#64) = true <;>
      simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · refine Entails.trans
          (Entails.of_eq (show _ =
            (stackAt fsp allocHookStack ∗ memRegion (fsp - 5152#64) 1056) ∗
            (((fsp + 184#64) ↦₆₄ pa2) ∗
             ((fsp + 232#64) ↦₆₄ ca2) ∗
             ((fsp + 176#64) ↦₆₄ pa3) ∗
             vecCapPtrDealloc A ca2 pa2 ∗
             vecCapPtrDealloc A ca3 pa3 ∗
             A.pool ∗
             (((fsp + 200#64) ↦₆₄ ca1) ∗
              ((fsp + 1272#64) ↦₆₄ pa1) ∗ Frame)) by ac_rfl)) ?_
        exact sepConj_mono_left hst
      · wp_done
    · wp_steps
      wp_apply
      refine EncoderFromPb.align_pre ?_ ?_
      · rw [hsp1]
        refine Entails.trans
          (Entails.of_eq (show _ =
            (stackAt fsp allocHookStack ∗ memRegion (fsp - 5152#64) 1056) ∗
            (((fsp + 184#64) ↦₆₄ pa2) ∗
             ((fsp + 232#64) ↦₆₄ ca2) ∗
             ((fsp + 176#64) ↦₆₄ pa3) ∗
             vecCapPtrDealloc A ca2 pa2 ∗
             vecCapPtrDealloc A ca3 pa3 ∗
             A.pool ∗
             (((fsp + 200#64) ↦₆₄ ca1) ∗
              ((fsp + 1272#64) ↦₆₄ pa1) ∗ Frame)) by ac_rfl)) ?_
        exact sepConj_mono_left hst
      · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, hx26_2, htr2⟩
    have h9132 := v2hsd_cleanup_9132_to_9212 hA s0 s2 fsp out d0 ca2 pa2 ca3 pa3
      (((fsp + 200#64) ↦₆₄ ca1) ∗
       ((fsp + 1272#64) ↦₆₄ pa1) ∗ Frame)
      hfsp_align hpc2 hrun2 hsp2 hx19_2 hx22_2 hx26_2 htr2
    exact SepWP.mono h9132 fun sm Pm _ _ ⟨hPm, hq⟩ =>
      ⟨Entails.trans hPm (Entails.of_eq (by ac_rfl)), hq⟩

theorem v2hsd_stackAt_encoderFromPbStack_to_dropStack32 (fsp : BitVec 64) :
    stackAt fsp encoderFromPbStack ⊢
      stackAt fsp dropStack32 ∗ memRegion (fsp - 5152#64) 1024 := by
  have h := ProofLib.stackAt_split_bottom fsp dropStack32 1024 (by decide)
  change stackAt fsp encoderFromPbStack =
    memRegion (fsp - 5152#64) 1024 ∗ stackAt fsp dropStack32 at h
  rw [h]
  exact Entails.of_eq (by ac_rfl)

theorem v2hsd_stackAt_dropStack32_to_encoderFromPbStack (fsp : BitVec 64) :
    stackAt fsp dropStack32 ∗ memRegion (fsp - 5152#64) 1024 ⊢
      stackAt fsp encoderFromPbStack := by
  have h := ProofLib.stackAt_split_bottom fsp dropStack32 1024 (by decide)
  change stackAt fsp encoderFromPbStack =
    memRegion (fsp - 5152#64) 1024 ∗ stackAt fsp dropStack32 at h
  rw [h]
  exact Entails.of_eq (by ac_rfl)

/-- Execution segment `+11256 -> +9228` (`mov w23, wzr; b +9228`): sets `x23 = 0#64` and jumps to `+9228`. -/
theorem v2hsd_cleanup_11256_to_9228
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (fsp out : BitVec 64) (Rest : SepProp)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 11256#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9228#64) s1
      Rest
      (fun sm Pm =>
        (Pm ⊢ Rest) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x23 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  states_from_pb_fetches_range b (Rust.withPanics ext) 11256 8
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  wp_steps
  wp_done

/-- Cleanup at `+11240 -> +9228` (`0x5cc8c -> 0x5c4b0`, when `<PolyDecoder>::from_pb = Err`):
drops `polyEncoderAt A (fsp + 1392) enc` (`bl 0x4c5d0`), drops `unchunkedEkSentAt A (fsp + 1264) uc`
(`bl 0x4ca24`), sets `x23 = 0#64`, and jumps to `+9228`. -/
theorem v2hsd_cleanup_11240_to_9228
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s1 : State) (fsp out : BitVec 64)
    (enc : PolyEncoder) (uc : LibsignalSpqrV1.Unchunked.SendEk.EkSent (spqrAuthApi F))
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 11240#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9228#64) s1
      (stackAt fsp encoderFromPbStack ∗
        polyEncoderAt A (fsp + 1392#64) enc ∗
        unchunkedEkSentAt A (fsp + 1264#64) uc ∗
        A.pool ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          memRegion (fsp + 1392#64) 400 ∗
          memRegion (fsp + 1264#64) 80 ∗
          A.pool ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x23 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  have hdrop_enc := v2hsd_sub_ok_drop_poly_encoder_11244 hA
  have hdrop_uc := v2hsd_sub_ok_drop_unchunked_ek_sent_11252 (F := F) hA
  simp only [dropGluePolyEncoderSpec, dropGluePoly16Stack] at hdrop_enc
  simp only [dropUnchunkedEkSentSpec] at hdrop_uc
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 11256#64)
    (P_mid :=
      stackAt fsp encoderFromPbStack ∗
      memRegion (fsp + 1392#64) 400 ∗
      memRegion (fsp + 1264#64) 80 ∗
      A.pool ∗
      Frame)
    (Q := fun sm =>
      sm.sp = fsp ∧
      sm.readReg64 .x19 = out ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · refine SepWP.weaken_pre
      (sepConj_mono_left (v2hsd_stackAt_encoderFromPbStack_to_dropStack32 fsp)) ?_
    states_from_pb_fetches_range b (Rust.withPanics ext) 11240 16
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, polyEncoderSize, unchunkedEkSentSize,
      BitVec.ofNat_eq_ofNat] at hdrop_enc hdrop_uc hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hdrop_enc hdrop_uc
    refine EncoderFromPb.seq_clean (mid := entry + 11248#64)
      (P_mid :=
        (stackAt fsp dropStack32 ∗ memRegion (fsp - 5152#64) 1024) ∗
        memRegion (fsp + 1392#64) 400 ∗
        unchunkedEkSentAt A (fsp + 1264#64) uc ∗
        A.pool ∗
        Frame)
      (Q := fun sm =>
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · wp_steps
      wp_apply
      refine Drop.align_pre (by rw [hsp1]; ac_rfl) ?_
      wp_done
    · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, htr2⟩
      clear hdrop_enc
      rcases uc with ⟨epoch, ⟨rootKey, macKey⟩, hdr⟩
      wp_steps
      wp_apply
      refine EncoderFromPb.align_pre ?_ ?_
      · have hst := v2hsd_stackAt_dropStack32_to_encoderFromPbStack fsp
        rw [hsp2]
        refine Entails.trans
          (Entails.of_eq (show _ =
            (stackAt fsp dropStack32 ∗ memRegion (fsp - 5152#64) 1024) ∗
            (memRegion (fsp + 1392#64) 400 ∗
             memRegion (fsp + 1264#64) 80 ∗
             A.pool ∗ Frame) by ac_rfl)) ?_
        exact sepConj_mono_left hst
      · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, htr2⟩
    exact v2hsd_cleanup_11256_to_9228 s0 s2 fsp out _ hpc2 hrun2 hsp2 hx19_2 htr2

theorem v2hsd_polyEncoder_1392_join (fsp tag : BitVec 64) :
    ((fsp + 1392#64) ↦₆₄ tag) ∗
      memRegion (fsp + 1400#64) 384 ∗
      memRegion (fsp + 1784#64) 8 ⊢
    memRegion (fsp + 1392#64) 400 := by
  have h1 : fsp + 1400#64 = (fsp + 1392#64) + 8#64 := by bv_omega
  have h2 : fsp + 1784#64 = (fsp + 1400#64) + 384#64 := by bv_omega
  rw [ProofLib.memRegion_split' (b := fsp + 1392#64) (n := 8) (k := 392)
        (b' := fsp + 1400#64) rfl h1 (by decide),
      ProofLib.memRegion_split' (b := fsp + 1400#64) (n := 384) (k := 8)
        (b' := fsp + 1784#64) rfl h2 (by decide)]
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _)

theorem v2hsd_drop_poly16_pre (A : RustAlloc) (fsp : BitVec 64) (enc : PolyEncoder) (Frame : SepProp) :
    stackAt fsp encoderFromPbStack ∗
      polyEncoderAt A (fsp + 1392#64) enc ∗
      A.pool ∗
      Frame ⊢
    ∃∗ tag : BitVec 64, ∃∗ vecs : List (List GF16),
      ⌜vecs.length = NUM_POLYS⌝ ∗
      ((stackAt fsp dropStack32 ∗ memRegion (fsp - 5152#64) 1024) ∗
       ((fsp + 1392#64) ↦₆₄ tag) ∗
       vecGF16ListOf A ((fsp + 1392#64) + 8#64) vecs ∗
       memRegion ((fsp + 1392#64) + 392#64) 8 ∗
       A.pool ∗
       Frame) := by
  refine Entails.trans
    (sepConj_mono
      (v2hsd_stackAt_encoderFromPbStack_to_dropStack32 fsp)
      (sepConj_mono_left (polyEncoderAt_entails_tag_vecs_tail A (fsp + 1392#64) enc))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro tag
  apply Entails.sepExists_elim; intro vecs
  refine Entails.sepExists_right tag ?_
  refine Entails.sepExists_right vecs ?_
  exact Entails.of_eq (by ac_rfl)

/-- Execution segment `+11024 -> +11032`: drops `[Poly; 16]` at `fsp + 1400#64` (`x23 + 8#64`) via `v2hsd_sub_ok_drop_poly16_11028`
and combines with the tag and tail to leave `memRegion (fsp + 1392#64) 400`. -/
theorem v2hsd_drop_poly16_11024_to_11032
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s1 : State) (fsp out ca3 : BitVec 64)
    (enc : PolyEncoder) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 11024#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = fsp + 1392#64)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 11032#64) s1
      (stackAt fsp encoderFromPbStack ∗
        polyEncoderAt A (fsp + 1392#64) enc ∗
        A.pool ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          memRegion (fsp + 1392#64) 400 ∗
          A.pool ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x26 = ca3 ∧
        TraceCalleeSaved sm s0) := by
  have hdrop := v2hsd_sub_ok_drop_poly16_11028 hA
  simp only [dropGluePoly16Spec, dropGluePoly16Stack] at hdrop
  refine SepWP.weaken_pre (v2hsd_drop_poly16_pre A fsp enc Frame) ?_
  apply ProofLib.SepWP.exists_left; intro tag
  apply ProofLib.SepWP.exists_left; intro vecs
  apply ProofLib.SepWP.pure_elim; intro hvecs_len
  states_from_pb_fetches_range b (Rust.withPanics ext) 11024 8
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, polyArrayBytes,
    BitVec.ofNat_eq_ofNat] at hdrop hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hdrop ⊢
  wp_steps
  wp_apply
  refine EncoderFromPb.align_pre ?_ ?_
  · have hst := v2hsd_stackAt_dropStack32_to_encoderFromPbStack fsp
    have hjoin := v2hsd_polyEncoder_1392_join fsp tag
    rw [hsp1]
    refine Entails.trans
      (Entails.of_eq (show _ =
        (stackAt fsp dropStack32 ∗ memRegion (fsp - 5152#64) 1024) ∗
        (((fsp + 1392#64) ↦₆₄ tag) ∗
          memRegion (fsp + 1400#64) 384 ∗
          memRegion (fsp + 1784#64) 8) ∗
        (A.pool ∗ Frame) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono hst (sepConj_mono_left hjoin)) (Entails.of_eq (by ac_rfl))
  · wp_done

/-- Execution segment `+11072 -> +11256`: deallocates `(ca3, pa3)` (`x26 = ca3`, `[sp + 176] = pa3`). -/
theorem v2hsd_cleanup_11072_to_11256
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s1 : State) (fsp out ca3 pa3 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 11072#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 11256#64) s1
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        vecCapPtrDealloc A ca3 pa3 ∗
        A.pool ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          A.pool ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        TraceCalleeSaved sm s0) := by
  have hdealloc := v2hsc_sub_ok_dealloc_125316 (b := b) (A := A) (ext := ext) hA
  simp only [rustDeallocSpec] at hdealloc
  refine SepWP.weaken_pre
    (sepConj_mono_left (v2hsc_stackAt_encoderFromPbStack_to_allocHook fsp)) ?_
  have hst := v2hsc_stackAt_allocHook_to_encoderFromPbStack fsp
  states_from_pb_fetches_range b (Rust.withPanics ext) 11072 24
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, vecCapPtrDealloc,
    BitVec.ofNat_eq_ofNat] at hdealloc hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  by_cases hca3 : (ca3 == 0#64) = true <;>
    simp only [hca3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · wp_steps
    refine EncoderFromPb.align_pre (sepConj_mono_left hst) ?_
    wp_done
  · wp_steps
    wp_apply
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · rw [hsp1]
      refine Entails.trans
        (Entails.of_eq (show _ =
          (stackAt fsp allocHookStack ∗ memRegion (fsp - 5152#64) 1056) ∗
          (((fsp + 176#64) ↦₆₄ pa3) ∗ A.pool ∗ Frame) by ac_rfl)) ?_
      exact sepConj_mono_left hst
    · wp_done

/-- Execution segment `+11052 -> +11072`: deallocates `(ca2, pa2)` (`[sp + 232] = ca2`, `[sp + 184] = pa2`). -/
theorem v2hsd_cleanup_11052_to_11072
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s1 : State) (fsp out ca2 pa2 ca3 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 11052#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 11072#64) s1
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗
        vecCapPtrDealloc A ca2 pa2 ∗
        A.pool ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 184#64) ↦₆₄ pa2) ∗
          A.pool ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x26 = ca3 ∧
        TraceCalleeSaved sm s0) := by
  have hdealloc := v2hsc_sub_ok_dealloc_125316 (b := b) (A := A) (ext := ext) hA
  simp only [rustDeallocSpec] at hdealloc
  refine SepWP.weaken_pre
    (sepConj_mono_left (v2hsc_stackAt_encoderFromPbStack_to_allocHook fsp)) ?_
  have hst := v2hsc_stackAt_allocHook_to_encoderFromPbStack fsp
  states_from_pb_fetches_range b (Rust.withPanics ext) 11052 20
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, vecCapPtrDealloc,
    BitVec.ofNat_eq_ofNat] at hdealloc hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  by_cases hca2 : (ca2 == 0#64) = true <;>
    simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · wp_steps
    refine EncoderFromPb.align_pre (sepConj_mono_left hst) ?_
    wp_done
  · wp_steps
    wp_apply
    refine EncoderFromPb.align_pre ?_ ?_
    · rw [hsp1]
      refine Entails.trans
        (Entails.of_eq (show _ =
          (stackAt fsp allocHookStack ∗ memRegion (fsp - 5152#64) 1056) ∗
          (((fsp + 232#64) ↦₆₄ ca2) ∗
           ((fsp + 184#64) ↦₆₄ pa2) ∗ A.pool ∗ Frame) by ac_rfl)) ?_
      exact sepConj_mono_left hst
    · wp_done

/-- Execution segment `+11032 -> +11052`: deallocates `(ca1, pa1)` (`[sp + 200] = ca1`, `[sp + 1272] = pa1`). -/
theorem v2hsd_cleanup_11032_to_11052
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s1 : State) (fsp out ca1 pa1 ca3 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 11032#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 11052#64) s1
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 200#64) ↦₆₄ ca1) ∗
        ((fsp + 1272#64) ↦₆₄ pa1) ∗
        vecCapPtrDealloc A ca1 pa1 ∗
        A.pool ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          ((fsp + 200#64) ↦₆₄ ca1) ∗
          ((fsp + 1272#64) ↦₆₄ pa1) ∗
          A.pool ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x26 = ca3 ∧
        TraceCalleeSaved sm s0) := by
  have hdealloc := v2hsc_sub_ok_dealloc_125316 (b := b) (A := A) (ext := ext) hA
  simp only [rustDeallocSpec] at hdealloc
  refine SepWP.weaken_pre
    (sepConj_mono_left (v2hsc_stackAt_encoderFromPbStack_to_allocHook fsp)) ?_
  have hst := v2hsc_stackAt_allocHook_to_encoderFromPbStack fsp
  states_from_pb_fetches_range b (Rust.withPanics ext) 11032 20
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, vecCapPtrDealloc,
    BitVec.ofNat_eq_ofNat] at hdealloc hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  by_cases hca1 : (ca1 == 0#64) = true <;>
    simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · wp_steps
    refine EncoderFromPb.align_pre (sepConj_mono_left hst) ?_
    wp_done
  · wp_steps
    wp_apply
    refine EncoderFromPb.align_pre ?_ ?_
    · rw [hsp1]
      refine Entails.trans
        (Entails.of_eq (show _ =
          (stackAt fsp allocHookStack ∗ memRegion (fsp - 5152#64) 1056) ∗
          (((fsp + 200#64) ↦₆₄ ca1) ∗
           ((fsp + 1272#64) ↦₆₄ pa1) ∗ A.pool ∗ Frame) by ac_rfl)) ?_
      exact sepConj_mono_left hst
    · wp_done

/-- Full cleanup at `+11024 -> +9228` (`receivingCt1 = none`): drops `[Poly; 16]` at `fsp + 1400`,
deallocates `(ca1, pa1)`, `(ca2, pa2)`, `(ca3, pa3)`, sets `x23 = 0#64`, and reaches `+9228`. -/
theorem v2hsd_cleanup_11024_to_9228
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s1 : State) (fsp out ca1 pa1 ca2 pa2 ca3 pa3 : BitVec 64)
    (enc : PolyEncoder) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 11024#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = fsp + 1392#64)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9228#64) s1
      (stackAt fsp encoderFromPbStack ∗
        polyEncoderAt A (fsp + 1392#64) enc ∗
        ((fsp + 200#64) ↦₆₄ ca1) ∗
        ((fsp + 1272#64) ↦₆₄ pa1) ∗
        ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        vecCapPtrDealloc A ca1 pa1 ∗
        vecCapPtrDealloc A ca2 pa2 ∗
        vecCapPtrDealloc A ca3 pa3 ∗
        A.pool ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          memRegion (fsp + 1392#64) 400 ∗
          ((fsp + 200#64) ↦₆₄ ca1) ∗
          ((fsp + 1272#64) ↦₆₄ pa1) ∗
          ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 184#64) ↦₆₄ pa2) ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          A.pool ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x23 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 11032#64)
    (P_mid :=
      stackAt fsp encoderFromPbStack ∗
      ((fsp + 200#64) ↦₆₄ ca1) ∗
      ((fsp + 1272#64) ↦₆₄ pa1) ∗
      vecCapPtrDealloc A ca1 pa1 ∗
      A.pool ∗
      (memRegion (fsp + 1392#64) 400 ∗
       ((fsp + 232#64) ↦₆₄ ca2) ∗
       ((fsp + 184#64) ↦₆₄ pa2) ∗
       ((fsp + 176#64) ↦₆₄ pa3) ∗
       vecCapPtrDealloc A ca2 pa2 ∗
       vecCapPtrDealloc A ca3 pa3 ∗
       Frame))
    (Q := fun sm =>
      sm.sp = fsp ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x26 = ca3 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · have h11024 := v2hsd_drop_poly16_11024_to_11032 hA s0 s1 fsp out ca3 enc
      (((fsp + 200#64) ↦₆₄ ca1) ∗
       ((fsp + 1272#64) ↦₆₄ pa1) ∗
       ((fsp + 232#64) ↦₆₄ ca2) ∗
       ((fsp + 184#64) ↦₆₄ pa2) ∗
       ((fsp + 176#64) ↦₆₄ pa3) ∗
       vecCapPtrDealloc A ca1 pa1 ∗
       vecCapPtrDealloc A ca2 pa2 ∗
       vecCapPtrDealloc A ca3 pa3 ∗
       Frame)
      hfsp_align hpc1 hrun1 hsp1 hx19_1 hx23_1 hx26_1 htr1
    exact SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (SepWP.mono h11024 fun sm Pm _ _ ⟨hPm, hq⟩ =>
        ⟨Entails.trans hPm (Entails.of_eq (by ac_rfl)), hq⟩)
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx26_2, htr2⟩
    refine EncoderFromPb.seq_clean
      (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 11052#64)
      (P_mid :=
        stackAt fsp encoderFromPbStack ∗
        ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗
        vecCapPtrDealloc A ca2 pa2 ∗
        A.pool ∗
        (memRegion (fsp + 1392#64) 400 ∗
         ((fsp + 200#64) ↦₆₄ ca1) ∗
         ((fsp + 1272#64) ↦₆₄ pa1) ∗
         ((fsp + 176#64) ↦₆₄ pa3) ∗
         vecCapPtrDealloc A ca3 pa3 ∗
         Frame))
      (Q := fun sm =>
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x26 = ca3 ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · have h11032 := v2hsd_cleanup_11032_to_11052 hA s0 s2 fsp out ca1 pa1 ca3
        (memRegion (fsp + 1392#64) 400 ∗
         ((fsp + 232#64) ↦₆₄ ca2) ∗
         ((fsp + 184#64) ↦₆₄ pa2) ∗
         ((fsp + 176#64) ↦₆₄ pa3) ∗
         vecCapPtrDealloc A ca2 pa2 ∗
         vecCapPtrDealloc A ca3 pa3 ∗
         Frame)
        hfsp_align hpc2 hrun2 hsp2 hx19_2 hx26_2 htr2
      exact SepWP.mono h11032 fun sm Pm _ _ ⟨hPm, hq⟩ =>
        ⟨Entails.trans hPm (Entails.of_eq (by ac_rfl)), hq⟩
    · intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx26_3, htr3⟩
      refine EncoderFromPb.seq_clean
        (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 11072#64)
        (P_mid :=
          stackAt fsp encoderFromPbStack ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          vecCapPtrDealloc A ca3 pa3 ∗
          A.pool ∗
          (memRegion (fsp + 1392#64) 400 ∗
           ((fsp + 200#64) ↦₆₄ ca1) ∗
           ((fsp + 1272#64) ↦₆₄ pa1) ∗
           ((fsp + 232#64) ↦₆₄ ca2) ∗
           ((fsp + 184#64) ↦₆₄ pa2) ∗
           Frame))
        (Q := fun sm =>
          sm.sp = fsp ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x26 = ca3 ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · have h11052 := v2hsd_cleanup_11052_to_11072 hA s0 s3 fsp out ca2 pa2 ca3
          (memRegion (fsp + 1392#64) 400 ∗
           ((fsp + 200#64) ↦₆₄ ca1) ∗
           ((fsp + 1272#64) ↦₆₄ pa1) ∗
           ((fsp + 176#64) ↦₆₄ pa3) ∗
           vecCapPtrDealloc A ca3 pa3 ∗
           Frame)
          hfsp_align hpc3 hrun3 hsp3 hx19_3 hx26_3 htr3
        exact SepWP.mono h11052 fun sm Pm _ _ ⟨hPm, hq⟩ =>
          ⟨Entails.trans hPm (Entails.of_eq (by ac_rfl)), hq⟩
      · intro s4 hpc4 hrun4 ⟨hsp4, hx19_4, hx26_4, htr4⟩
        refine EncoderFromPb.seq_clean
          (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 11256#64)
          (P_mid :=
            stackAt fsp encoderFromPbStack ∗
            memRegion (fsp + 1392#64) 400 ∗
            ((fsp + 200#64) ↦₆₄ ca1) ∗
            ((fsp + 1272#64) ↦₆₄ pa1) ∗
            ((fsp + 232#64) ↦₆₄ ca2) ∗
            ((fsp + 184#64) ↦₆₄ pa2) ∗
            ((fsp + 176#64) ↦₆₄ pa3) ∗
            A.pool ∗ Frame)
          (Q := fun sm =>
            sm.sp = fsp ∧
            sm.readReg64 .x19 = out ∧
            TraceCalleeSaved sm s0)
          ?_ ?_
        · have h11072 := v2hsd_cleanup_11072_to_11256 hA s0 s4 fsp out ca3 pa3
            (memRegion (fsp + 1392#64) 400 ∗
             ((fsp + 200#64) ↦₆₄ ca1) ∗
             ((fsp + 1272#64) ↦₆₄ pa1) ∗
             ((fsp + 232#64) ↦₆₄ ca2) ∗
             ((fsp + 184#64) ↦₆₄ pa2) ∗
             Frame)
            hfsp_align hpc4 hrun4 hsp4 hx19_4 hx26_4 htr4
          exact SepWP.mono h11072 fun sm Pm _ _ ⟨hPm, hq⟩ =>
            ⟨Entails.trans hPm (Entails.of_eq (by ac_rfl)), hq⟩
        · intro s5 hpc5 hrun5 ⟨hsp5, hx19_5, htr5⟩
          exact v2hsd_cleanup_11256_to_9228 s0 s5 fsp out _ hpc5 hrun5 hsp5 hx19_5 htr5

end CryptoVerification.SpqrV1.States.FromPb
